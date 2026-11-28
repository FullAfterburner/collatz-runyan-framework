import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# --- 1. Torus Parameters ---
R_major = 6.0   # Distance from tube center to donut center
r_minor = 2.2   # Radius of the tube itself

# Create the 3D surface mesh
phi_grid = np.linspace(0, 2 * np.pi, 60)
theta_grid = np.linspace(0, 2 * np.pi, 60)
Phi, Theta = np.meshgrid(phi_grid, theta_grid)

X_torus = (R_major + r_minor * np.cos(Theta)) * np.cos(Phi)
Y_torus = (R_major + r_minor * np.cos(Theta)) * np.sin(Phi)
Z_torus = r_minor * np.sin(Theta)

# --- 2. Continuous Hamiltonian Trajectory (T Matrix Flow) ---
w1 = 10 + 3 * np.sqrt(26)  # ~25.297 rad/s (Poloidal fast mode)
w2 = 3 * np.sqrt(26) - 10  # ~5.297 rad/s  (Toroidal slow mode)

t_flow = np.linspace(0, 2 * np.pi / w2, 2500)
theta_flow = w1 * t_flow
phi_flow = w2 * t_flow

X_flow = (R_major + r_minor * np.cos(theta_flow)) * np.cos(phi_flow)
Y_flow = (R_major + r_minor * np.cos(theta_flow)) * np.sin(phi_flow)
Z_flow = r_minor * np.sin(theta_flow)

# --- 3. Discrete Collatz Cascade Nodes (112 -> 56 -> 28 -> 14 -> 7 -> 37) ---
cascade_nodes = [
    {"label": "112 (0°)",       "theta": 0.0,            "phi": 2 * np.pi * (112 % 30) / 30, "color": "#FF4500"},
    {"label": "56 (-90° / -i)", "theta": -np.pi / 2,     "phi": 2 * np.pi * (56 % 30) / 30,  "color": "#FF8C00"},
    {"label": "28 (-180° / -1)","theta": -np.pi,         "phi": 2 * np.pi * (28 % 30) / 30,  "color": "#FFD700"},
    {"label": "14 (-270° / i)", "theta": -3 * np.pi / 2, "phi": 2 * np.pi * (14 % 30) / 30,  "color": "#32CD32"},
    {"label": "7 (Ground)",     "theta": -2 * np.pi,     "phi": 2 * np.pi * (7 % 30) / 30,   "color": "#00CED1"},
    {"label": "37 (Seed)",      "theta": 0.0,            "phi": 2 * np.pi * (37 % 30) / 30,  "color": "#9400D3"}
]

# Compute 3D coords for discrete points
pts_x, pts_y, pts_z = [], [], []
for pt in cascade_nodes:
    x = (R_major + (r_minor + 0.15) * np.cos(pt["theta"])) * np.cos(pt["phi"])
    y = (R_major + (r_minor + 0.15) * np.cos(pt["theta"])) * np.sin(pt["phi"])
    z = (r_minor + 0.15) * np.sin(pt["theta"])
    pts_x.append(x)
    pts_y.append(y)
    pts_z.append(z)

# --- 4. Plotting ---
fig = plt.figure(figsize=(13, 10))
ax = fig.add_subplot(111, projection='3d')

# Render semi-transparent Torus skin
ax.plot_surface(X_torus, Y_torus, Z_torus, color='#1E293B', alpha=0.18, edgecolor='none')

# Render the continuous winding trajectory
ax.plot(X_flow, Y_flow, Z_flow, color='#38BDF8', alpha=0.45, linewidth=1.2, label=r'Continuous Flow ($\Delta\omega = 20$)')

# Connect discrete cascade steps with an orange vector track
ax.plot(pts_x[:5], pts_y[:5], pts_z[:5], color='#F97316', linestyle='--', linewidth=2.5, label='4-Step Inward Cascade')

# Draw 2-adic topological bridge between 7 and 37
ax.plot([pts_x[4], pts_x[5]], [pts_y[4], pts_y[5]], [pts_z[4], pts_z[5]], 
        color='#A855F7', linestyle=':', linewidth=3, label=r'2-Adic Bridge ($|37-7|_2 = 0.5$)')

# Render the labeled nodes
for i, pt in enumerate(cascade_nodes):
    ax.scatter(pts_x[i], pts_y[i], pts_z[i], color=pt["color"], s=90, edgecolors='white', depthshade=False)
    ax.text(pts_x[i] * 1.08, pts_y[i] * 1.08, pts_z[i] * 1.08, pt["label"], color='black', fontsize=9, weight='bold')

ax.set_title("2-Adic Toroidal Embedding of the 37 $\\to$ 7 Cascade Engine", fontsize=14, pad=20)
ax.set_axis_off()
ax.legend(loc='upper right', frameon=True)
ax.view_init(elev=32, azim=48)

plt.tight_layout()
plt.show()