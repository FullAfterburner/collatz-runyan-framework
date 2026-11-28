import numpy as np


def compute_charged_lepton_masses(
    m_e_MeV=0.51099895,
    collatz_steps=114,
):
    """
    Computes the charged lepton mass ladder (e, mu, tau) using the
    Collatz-Runyan Framework invariants from Sections 2.1 and 3.3:
      - Prime Matrix M_p = [[3, 37], [5, 17]]
      - Persistent quantum floor: 49 / 234
      - Diagonal trace divergence: factored from Tr(M_p) = 20 and diag gap = 14
    """
    # 1. Define Prime Matrix M_p (Section 2.1)
    M_p = np.array([[3, 37], [5, 17]], dtype=float)
    p_gen = M_p[1, 1]  # Prime generator: 17

    # 2. Factor the Diagonal Trace Divergence
    # Trace Tr(M_p) = 3 + 17 = 20 (equals modal beat gap delta_omega)
    # Diagonal gap = 17 - 3 = 14 (pre-exit anchor seed E_0)
    diag_trace = np.trace(M_p)  # 20.0
    diag_gap = M_p[1, 1] - M_p[0, 0]  # 14.0

    # Factored divergence: (Tr(M_p) / S_total) + (diag_gap / (S_total * 17))
    trace_horizon_term = diag_trace / collatz_steps  # 20 / 114 = 0.175439
    diag_skew_residue = diag_gap / (
        collatz_steps * p_gen
    )  # 14 / 1938 = 0.007224
    trace_divergence = trace_horizon_term + diag_skew_residue  # 0.182663

    # 3. Spinor Quantum Floor & Charged Lepton Ladder (Section 3.3)
    quantum_floor = 49.0 / 234.0  # Persistent left-handed floor

    # Muon mass
    mu_to_e_ratio = 207.0 - quantum_floor  # ~206.790598
    m_mu_MeV = m_e_MeV * mu_to_e_ratio

    # Tau mass (decouples along prime generator 17 minus diagonal trace divergence)
    tau_to_mu_ratio = p_gen - trace_divergence  # ~16.817337
    m_tau_MeV = m_mu_MeV * tau_to_mu_ratio

    return {
        "M_p": M_p,
        "diag_trace": diag_trace,
        "diag_gap": diag_gap,
        "trace_divergence": trace_divergence,
        "m_e_MeV": m_e_MeV,
        "m_mu_MeV": m_mu_MeV,
        "m_tau_MeV": m_tau_MeV,
        "mu_to_e_ratio": mu_to_e_ratio,
        "tau_to_mu_ratio": tau_to_mu_ratio,
        "tau_to_e_ratio": m_tau_MeV / m_e_MeV,
    }


if __name__ == "__main__":
    res = compute_charged_lepton_masses()
    print(f"Diagonal Trace Tr(M_p) : {res['diag_trace']:.1f}")
    print(f"Diagonal Gap (17 - 3)  : {res['diag_gap']:.1f}")
    print(f"Factored Divergence    : {res['trace_divergence']:.6f}")
    print("-" * 52)
    print(f"Electron (e)           : {res['m_e_MeV']:.6f} MeV/c^2")
    print(
        f"Muon     (mu)          : {res['m_mu_MeV']:.6f} MeV/c^2  (m_mu/m_e  = {res['mu_to_e_ratio']:.6f})"
    )
    print(
        f"Tau     (tau)          : {res['m_tau_MeV']:.6f} MeV/c^2  (m_tau/m_mu = {res['tau_to_mu_ratio']:.6f})"
    )
