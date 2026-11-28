import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# --- 1. Base Sphere Mesh (S^2) ---
u = np.linspace(0, 2 * np.pi, 80)
v = np.linspace(0, np.pi, 80)
Xs = np.outer(np.cos(u), np.sin(v))
Ys = np.outer(np.sin(u), np.sin(v))
Zs = np.outer(np.ones(np.size(u)), np.cos(v))

# --- 2. Continuous Trajectory via Hopf Projection ---
# Modal frequencies from the skew-symmetric matrix T
w1 = 10 + 3 * np.sqrt(26)   # ~25.297 rad/s
w2 = 3 * np.sqrt(26) - 10   # ~5.297 rad/s

# Eigenvector amplitude components
v1 = (7 + 3 * np.sqrt(26)) / 5
v2 = (7 - 3 * np.sqrt(26)) / 5

# Time parameter for the continuous flow
t = np.linspace(0, 2 * np.pi / w2, 3000)
C1, C2 = 0.6, 0.4

# Complex coordinates z1(t), z2(t)
z1 = C1 * v1 * np.exp(1j * w1 * t) + C2 * v2 * np.exp(-1j * w2 * t)
z2 = C1 * np.exp(1j * w1 * t) + C2 * np.exp(-1j * w2 * t)

# Normalize onto the unit 3-sphere (S^3)
norm_S3 = np.sqrt(np.abs(z1)**2 + np.abs(z2)**2)
z1_u = z1 / norm_S3
z2_u = z2 / norm_S3

# Hopf map to S^2
X_hopf = 2 * np.real(z1_u * np.conj(z2_u))
Y_hopf = 2 * np.imag(z1_u * np.conj(z2_u))
Z_hopf = np.abs(z1_u)**2 - np.abs(z2_u)**2

# --- 3. Discrete Cascade Projection (112 -> 56 -> 28 -> 14 -> 7) ---
# Map discrete complex steps (r * exp(i*theta)) to Hopf coordinates
steps = [
    {"label": "112 (0°)",       "z1": 112 + 0j,  "z2": 37 + 0j,  "color": "#FF4500"},
    {"label": "56 (-90° / -i)", "z1": 0 - 56j,   "z2": 17 + 0j,  "color": "#FF8C00"},
    {"label": "28 (-180° / -1)","z1": -28 + 0j,  "z2": 7 + 0j,   "color": "#FFD700"},
    {"label": "14 (-270° / i)", "z1": 0 + 14j,   "z2": 3 + 0j,   "color": "#32CD32"},
    {"label": "7 (Ground)",     "z1": 7 + 0j,    "z2": 1 + 0j,   "color": "#00CED1"}
]

pts_x, pts_y, pts_z = [], [], []
for pt in steps:
    z1_val = pt["z1"]
    z2_val = pt["z2"]
    norm_val = np.sqrt(abs(z1_val)**2 + abs(z2_val)**2)
    z1_n = z1_val / norm_val
    z2_n = z2_val / norm_val
    
    # Scale slightly outward for clean 3D visibility
    scale = 1.03
    pts_x.append(scale * 2 * np.real(z1_n * np.conj(z2_n)))
    pts_y.append(scale * 2 * np.imag(z1_n * np.conj(z2_n)))
    pts_z.append(scale * (abs(z1_n)**2 - abs(z2_n)**2))

# --- 4. Plotting ---
fig = plt.figure(figsize=(11, 9))
ax = fig.add_subplot(111, projection='3d')

# Render base sphere
ax.plot_surface(Xs, Ys, Zs, color='#0F172A', alpha=0.15, edgecolor='#334155', linewidth=0.3)

# Render continuous Hopf trajectory
ax.plot(X_hopf, Y_hopf, Z_hopf, color='#38BDF8', linewidth=1.4, alpha=0.8,
        label=r'Precessing Flow ($\omega_{\rm sum} = 6\sqrt{26}$)')

# Render discrete cascade track
ax.plot(pts_x, pts_y, pts_z, color='#F97316', linestyle='--', linewidth=2.2, label='Cascade Descent')

# Plot labeled nodes
for i, pt in enumerate(steps):
    ax.scatter(pts_x[i], pts_y[i], pts_z[i], color=pt["color"], s=85, edgecolors='white', depthshade=False)
    ax.text(pts_x[i] * 1.12, pts_y[i] * 1.12, pts_z[i] * 1.12, pt["label"], color='black', fontsize=9, weight='bold')

ax.set_title("Hopf Projection of the Cascade Engine ($S^3 \\to S^2$)", fontsize=13, pad=15)
ax.set_axis_off()
ax.legend(loc='lower left', frameon=True)
ax.view_init(elev=24, azim=55)

plt.tight_layout()
plt.show()