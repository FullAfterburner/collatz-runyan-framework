import numpy as np
import matplotlib.pyplot as plt

# --- 1. Spinor Wave Function Evolution ---
Omega = 3 * np.sqrt(26)  # ~15.297 rad/s
t = np.linspace(0, 0.45, 1000)

P_L = 1 - (185 / 234) * (np.sin(Omega * t))**2
P_R = (185 / 234) * (np.sin(Omega * t))**2

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 5.5))

# Plot Probabilities
ax1.plot(t, P_L, color='#0284C7', linewidth=2.5, label=r'$P_L(t)$ (Left-Handed Survival)')
ax1.plot(t, P_R, color='#EF4444', linewidth=2.5, label=r'$P_R(t)$ (Right-Handed Transition)')
ax1.axhline(185 / 234, color='#EF4444', linestyle=':', alpha=0.7, label=r'Peak $P_R = 185/234$ (~79.1%)')
ax1.axhline(49 / 234, color='#0284C7', linestyle=':', alpha=0.7, label=r'Floor $P_L = 49/234$ (~20.9%)')
ax1.set_title(r"Spinor Flavor Wave Function ($\Omega = 3\sqrt{26}$)", fontsize=13)
ax1.set_xlabel("Proper Time $t$", fontsize=11)
ax1.set_ylabel("Probability", fontsize=11)
ax1.set_ylim(-0.05, 1.05)
ax1.grid(True, linestyle='--', alpha=0.4)
ax1.legend(loc='center right', frameon=True)

# --- 2. Rotational Phase Steps (7 -> 22 -> 11 -> 17 -> 13 -> 5 -> 1) ---
cascade_stages = [
    {"label": "7 (Ground)",  "n": 7,  "angle": 0},
    {"label": "11 (via 22)", "n": 11, "angle": -np.pi / 2},
    {"label": "17 (Matrix)", "n": 17, "angle": -np.pi},
    {"label": "13",          "n": 13, "angle": -np.pi * 2},
    {"label": "5 (Matrix)",  "n": 5,  "angle": -np.pi * 3.5},
    {"label": "1 (Sink)",    "n": 1,  "angle": -np.pi * 5.5}
]

angles = [s["angle"] for s in cascade_stages]
radii = [np.log2(s["n"]) for s in cascade_stages]

ax2 = plt.subplot(121, projection='polar') if False else ax2
x_coords = [r * np.cos(a) for r, a in zip(radii, angles)]
y_coords = [r * np.sin(a) for r, a in zip(radii, angles)]

ax2.plot(x_coords, y_coords, color='#8B5CF6', linestyle='--', marker='o', linewidth=2, markersize=8)
for i, s in enumerate(cascade_stages):
    ax2.text(x_coords[i] * 1.15, y_coords[i] * 1.15, s["label"], fontsize=10, weight='bold', ha='center')

ax2.set_title(r"Phase Spiral of Post-22 Odd Milestones ($\log_2(n)$ vs $\theta$)", fontsize=13)
ax2.set_xlabel(r"$\text{Re} \sim \log_2(n)\cos(\theta)$", fontsize=11)
ax2.set_ylabel(r"$\text{Im} \sim \log_2(n)\sin(\theta)$", fontsize=11)
ax2.grid(True, linestyle='--', alpha=0.4)

plt.tight_layout()
plt.show()