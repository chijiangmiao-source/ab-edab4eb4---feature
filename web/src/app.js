/* 安全规程 TMS 页面逻辑: 通过真实 HTTP 接口读写, 不做任何本地推断。 */
"use strict";

const $ = (sel) => document.querySelector(sel);

async function api(path, options = {}) {
  const resp = await fetch(path, {
    headers: { "Content-Type": "application/json" },
    ...options,
  });
  const data = await resp.json().catch(() => ({}));
  if (!resp.ok) {
    const err = new Error(data.message || `请求失败 (${resp.status})`);
    err.code = data.error;
    throw err;
  }
  return data;
}

function esc(s) {
  return String(s).replace(/[&<>"']/g, (c) => (
    { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
}

function setHealth(kind, text) {
  const box = $("#health");
  box.className = `health health-${kind}`;
  $("#health-text").textContent = text;
}

async function checkHealth() {
  try {
    const h = await api("/api/health");
    if (h.status === "ok") setHealth("ok", `接口可用 · 事实 ${h.facts} · 规则 ${h.rules}`);
    else setHealth("degraded", `接口降级: ${h.database}`);
  } catch (e) {
    setHealth("unavailable", "接口不可用");
  }
}

function renderState(state) {
  // 事实表
  const fb = $("#facts-table tbody");
  fb.innerHTML = "";
  for (const f of state.facts) {
    const tr = document.createElement("tr");
    const status = f.active
      ? '<span class="badge badge-valid">有效</span>'
      : '<span class="badge badge-retracted">已撤回</span>';
    tr.innerHTML = `
      <td><code>${esc(f.id)}</code></td>
      <td>${status}</td>
      <td><button class="retract" data-fact="${esc(f.id)}" ${f.active ? "" : "disabled"}>
        ${f.active ? "撤回" : "—"}</button></td>`;
    fb.appendChild(tr);
  }
  fb.querySelectorAll("button[data-fact]").forEach((btn) => {
    btn.addEventListener("click", () => retract(btn.dataset.fact));
  });

  // 规则表
  const rb = $("#rules-table tbody");
  rb.innerHTML = "";
  for (const r of state.rules) {
    const tr = document.createElement("tr");
    tr.innerHTML = `
      <td><code>${esc(r.id)}</code></td>
      <td><code>${esc(r.conclusion)} :- ${r.antecedents.map(esc).join(", ")}</code></td>`;
    rb.appendChild(tr);
  }

  // 结论 + 每项结论的完整依据
  const box = $("#conclusions");
  box.innerHTML = "";
  if (state.conclusions.length === 0) {
    box.innerHTML = '<p class="muted">尚无规则结论。添加规则后在此展示。</p>';
    return;
  }
  for (const c of state.conclusions) {
    const div = document.createElement("div");
    div.className = `conclusion ${c.status === "active" ? "" : "inactive"}`;
    const badge = c.status === "active"
      ? '<span class="badge badge-valid">有效</span>'
      : '<span class="badge badge-invalid">已失效</span>';
    const auditBtn = c.status === "active"
      ? `<button class="audit-btn" data-conclusion="${esc(c.id)}">依据容量审计</button>`
      : "";
    let html = `
      <div class="conclusion-head">
        <strong><code>${esc(c.id)}</code></strong>${badge}${auditBtn}
      </div>
      <div class="basis">
        <details ${c.supports.length ? "open" : ""}>
          <summary>当前完整支持（${c.supports.length}）— 每条含完整可复算依据</summary>`;
    if (c.supports.length === 0) {
      html += `<p class="muted">${esc(c.reason || "无完整支持")}</p>`;
    }
    for (const s of c.supports) {
      html += `
        <ul class="basis-route">
          <li>规则 <code>${esc(s.rule_id)}</code>：前提
            ${s.antecedents.map((a) => `<code>${esc(a)}</code>`).join(" ∧ ")}
          </li>
          <li>完整依据（事实层，可复算）：
            ${s.basis.length
              ? s.basis.map((b) => `<code>${esc(b)}</code>`).join(" ∪ ")
              : '<span class="muted">（无）</span>'}
          </li>
        </ul>`;
    }
    html += `</details>`;
    if (c.retired_supports.length) {
      html += `
        <details class="depleted">
          <summary>已耗尽的历史依据（${c.retired_supports.length}）</summary>`;
      for (const s of c.retired_supports) {
        html += `
          <ul class="basis-route">
            <li>规则 <code>${esc(s.rule_id)}</code>：前提
              ${s.antecedents.map((a) => `<code>${esc(a)}</code>`).join(" ∧ ")}</li>
            <li>当时完整依据：${s.basis.map((b) => `<code>${esc(b)}</code>`).join(" ∪ ")}</li>
          </ul>`;
      }
      html += `</details>`;
    }
    html += `</div>`;
    div.innerHTML = html;
    div.querySelectorAll("button[data-conclusion]").forEach((btn) => {
      btn.addEventListener("click", () => auditConclusion(btn.dataset.conclusion));
    });
    box.appendChild(div);
  }
}

function renderVerdict(v) {
  const box = $("#verdict");
  if (!v) return;
  if (v.already_retracted) {
    box.className = "verdict";
    box.innerHTML = `<p>事实 <code>${esc(v.fact_id)}</code> 此前已撤回 —— 稳定返回既有裁决
      （幂等，不产生新传播）。</p>`;
    return;
  }

  const affectedHtml = v.affected.map((a) => {
    const who = a.rule_id
      ? `结论 <code>${esc(a.node_id)}</code>（规则 <code>${esc(a.rule_id)}</code>）`
      : `事实 <code>${esc(a.node_id)}</code>`;
    const basis = a.complete_basis.length
      ? a.complete_basis.map((b) => `<code>${esc(b)}</code>`).join(" ∪ ")
      : '<span class="muted">（事实自身）</span>';
    return `<li>${who}<br/>失效前完整依据：${basis}</li>`;
  }).join("");

  const chainHtml = v.propagation_chain.length
    ? v.propagation_chain.map((c) => `
        <li>
          <code>${esc(c.triggered_by)}</code>
          <span class="arrow">── 失效后 ──▶</span>
          <code>${esc(c.node_id)}</code>
          的规则 <code>${esc(c.rule_id)}</code> 支持耗尽<br/>
          耗尽前提：${c.exhausted_antecedents.map((a) => `<code>${esc(a)}</code>`).join(" ∧ ")}<br/>
          该支持的完整依据：${c.exhausted_basis.map((b) => `<code>${esc(b)}</code>`).join(" ∪ ")}
        </li>`).join("")
    : '<li class="muted">本次撤回未导致任何结论失效（替代依据仍成立）。</li>';

  const survivedHtml = v.survived.length
    ? v.survived.map((n) => `<li>结论 <code>${esc(n)}</code> 仍有其它完整支持，保持有效</li>`).join("")
    : '<li class="muted">无。</li>';

  box.className = "verdict";
  box.innerHTML = `
    <p>撤回事实 <code>${esc(v.fact_id)}</code> 的裁决：</p>
    <div class="vgrid">
      <div class="vbox">
        <h4>被撤回事实与受影响结论（含每项完整依据）</h4>
        <ul class="chain affected">${affectedHtml}</ul>
      </div>
      <div class="vbox">
        <h4>支持耗尽形成的传播链</h4>
        <ul class="chain">${chainHtml}</ul>
      </div>
      <div class="vbox">
        <h4>靠替代依据保留的结论</h4>
        <ul class="chain survived-list">${survivedHtml}</ul>
      </div>
    </div>`;
}

function showError(msg) {
  const box = $("#error-box");
  box.textContent = msg;
  box.hidden = false;
  clearTimeout(showError._t);
  showError._t = setTimeout(() => { box.hidden = true; }, 6000);
}

function renderAudit(a) {
  const box = $("#audit");
  const basesHtml = a.bases.map((b) => `
    <div class="vbox">
      <h4>依据 <code>${esc(b.id)}</code></h4>
      <ul class="chain audit-basis">
        <li>原始事实：${b.facts.map((f) => `<code>${esc(f)}</code>`).join(" ∪ ")}</li>
        <li>规则链：${b.rule_chain.map((s) =>
          `<code>${esc(s.rule_id)}</code>（<code>${esc(s.conclusion)}</code> :- ${s.antecedents.map(esc).join(", ")}）`
        ).join(" → ")}</li>
      </ul>
    </div>`).join("");
  box.className = "verdict";
  box.innerHTML = `
    <p>结论 <code>${esc(a.conclusion)}</code> 的独立依据容量审计（同一读取快照，只读）：</p>
    <p>当前完整复算依据共 <strong>${a.total_bases}</strong> 套；
      彼此不共享原始事实的最大依据套数（容量）为 <strong>${a.capacity}</strong>。<br/>
      按稳定规则裁决的一组依据：
      <strong>${a.basis_ids.map((id) => `<code>${esc(id)}</code>`).join(" ")}</strong></p>
    <div class="vgrid">${basesHtml}</div>`;
}

function renderAuditError(id, err) {
  const box = $("#audit");
  box.className = "verdict";
  box.innerHTML = `
    <p>无法对结论 <code>${esc(id)}</code> 发起依据容量审计：${esc(err.message)}
      <span class="muted">（${esc(err.code || "error")}）</span><br/>
      规程与页面已有结论保持不变。</p>`;
}

function clearAudit() {
  const box = $("#audit");
  if (box.classList.contains("muted")) return;
  box.className = "verdict muted";
  box.textContent = "规程已变更：之前的审计结果已失效，请重新发起审计（结果只反映最新读取快照）。";
}

async function auditConclusion(id) {
  try {
    const data = await api("/api/audit", {
      method: "POST",
      body: JSON.stringify({ conclusion: id }),
    });
    renderAudit(data.audit);
  } catch (e) {
    renderAuditError(id, e);
  }
}

async function refresh() {
  try {
    const state = await api("/api/state");
    renderState(state);
    if (state.last_verdict) renderVerdict(state.last_verdict);
  } catch (e) {
    showError(`加载状态失败: ${e.message}`);
  }
}

async function retract(factId) {
  try {
    const data = await api("/api/retract", {
      method: "POST",
      body: JSON.stringify({ fact_id: factId }),
    });
    renderVerdict(data.verdict);
    renderState(data.state);
    clearAudit();
  } catch (e) {
    showError(`撤回失败: ${e.message}`);
  }
}

$("#form-fact").addEventListener("submit", async (e) => {
  e.preventDefault();
  const input = e.target.elements.id;
  try {
    await api("/api/facts", { method: "POST", body: JSON.stringify({ id: input.value }) });
    input.value = "";
    await refresh();
    clearAudit();
  } catch (err) { showError(`添加事实被拒绝: ${err.message}`); }
});

$("#form-rule").addEventListener("submit", async (e) => {
  e.preventDefault();
  const f = e.target.elements;
  const antecedents = f.antecedents.value.split(",").map((s) => s.trim()).filter(Boolean);
  try {
    await api("/api/rules", {
      method: "POST",
      body: JSON.stringify({
        id: f.id.value, conclusion: f.conclusion.value, antecedents,
      }),
    });
    f.id.value = f.conclusion.value = f.antecedents.value = "";
    await refresh();
    clearAudit();
  } catch (err) { showError(`添加规则被拒绝: ${err.message}`); }
});

checkHealth();
setInterval(checkHealth, 5000);
refresh();
