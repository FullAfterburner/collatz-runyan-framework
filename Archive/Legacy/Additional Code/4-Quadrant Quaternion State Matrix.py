import numpy as np

def trace_collatz_down(n):
    path = [n]
    parity_string = ""
    while n > 1:
        if n % 2 == 0:
            n = n // 2
            parity_string += "E"
        else:
            n = 3 * n + 1
            parity_string += "O"
        path.append(n)
    return path, parity_string

def generate_quaternion_matrix(radius=0.0625, theta=np.pi/4, phi=np.pi/3):
    # Mapping coordinates onto an S^3 sphere surface using the 2-adic radius
    w = radius * np.cos(theta)
    x = radius * np.sin(theta) * np.cos(phi)
    y = radius * np.sin(theta) * np.sin(phi)
    z = radius * np.sin(theta) # 4th dimension complement
    
    # Constructing a unitary quaternion rotation operator matrix
    q_matrix = np.array([
        [w, -x, -y, -z],
        [x,  w, -z,  y],
        [y,  z,  w, -x],
        [z, -y,  x,  w]
    ])
    return q_matrix

# Execute the tracker
full_path, parities = trace_collatz_down(305065927)
q_matrix = generate_quaternion_matrix()

print(f"Collatz Convergence Steps: {len(full_path) - 1}")
print(f"Terminal Drainage Sequence (Last 10 steps): {full_path[-10:]}")
print(f"First 30 Operations Parity String: {parities[:30]}")
print("\nGenerated Unified 4-Quadrant Quaternion Matrix Key:")
print(np.round(q_matrix, 6))
