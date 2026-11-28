import os

def fabricate_optimized_collatz_interface():
    html_content = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Runyan Collatz & Triangular Hub - 3D Dashboard</title>
    <style>
        * { box-sizing: border-box; margin: 0; padding: 0; }
        body, html { width: 100%; height: 100%; overflow: hidden; background-color: #050505; font-family: 'Consolas', monospace; color: #ffffff; }
        #canvas-container { width: 100%; height: 100%; position: absolute; top: 0; left: 0; z-index: 1; }
        
        .hud-panel {
            position: absolute;
            z-index: 10;
            background: rgba(15, 15, 15, 0.88);
            backdrop-filter: blur(12px);
            -webkit-backdrop-filter: blur(12px);
            border: 1px solid rgba(0, 255, 150, 0.3);
            border-radius: 8px;
            padding: 20px;
            box-shadow: 0 4px 24px rgba(0, 0, 0, 0.6);
        }
        #left-panel { top: 20px; left: 20px; width: 360px; }
        #right-panel { top: 20px; right: 20px; width: 320px; }
        
        h1, h2 { color: #00FF96; font-size: 13px; text-transform: uppercase; margin-bottom: 12px; letter-spacing: 1px; border-bottom: 1px solid rgba(0, 255, 150, 0.3); padding-bottom: 4px; }
        .metric-row { display: flex; justify-content: space-between; margin: 6px 0; font-size: 11px; }
        .metric-label { color: #888888; }
        .metric-value { color: #ffffff; font-weight: bold; }
        .highlight { color: #00FF96; }
        
        .control-group { margin: 14px 0; }
        label { display: block; font-size: 11px; color: #aaa; margin-bottom: 4px; }
        input[type="range"] { width: 100%; -webkit-appearance: none; background: #222; height: 4px; border-radius: 2px; outline: none; }
        input[type="range"]::-webkit-slider-thumb { -webkit-appearance: none; width: 12px; height: 12px; background: #00FF96; border-radius: 50%; cursor: pointer; box-shadow: 0 0 8px #00FF96; }
        
        .trajectory-box {
            margin-top: 12px;
            background: rgba(0, 0, 0, 0.5);
            border: 1px dashed rgba(0, 255, 150, 0.3);
            padding: 8px;
            border-radius: 4px;
            font-size: 10px;
            color: #00FF96;
            max-height: 80px;
            overflow-y: auto;
            word-break: break-all;
        }
        .status-pill { display: inline-block; padding: 2px 8px; background: rgba(0, 255, 150, 0.15); border: 1px solid #00FF96; color: #00FF96; border-radius: 12px; font-size: 10px; font-weight: bold; }
    </style>

    <script src="https://cdn.jsdelivr.net/npm/three@0.132.2/build/three.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/three@0.132.2/examples/js/controls/OrbitControls.js"></script>
</head>
<body>

    <div id="canvas-container"></div>

    <div id="left-panel" class="hud-panel">
        <h1>Diophantine / Pell Engine</h1>
        <div class="metric-row"><span class="metric-label">Equation:</span><span class="metric-value highlight">(2m+1)² - 3(2n+1)² = 6</span></div>
        <div class="metric-row"><span class="metric-label">Target Discovery n:</span><span class="metric-value" id="val-n">9 (T_9 = 45)</span></div>
        <div class="metric-row"><span class="metric-label">Mapped Result m:</span><span class="metric-value highlight" id="val-m">16 (T_16 = 136)</span></div>
        <div class="metric-row"><span class="metric-label">Identity Match:</span><span class="metric-value">3(45) + 1 = 136</span></div>
        
        <div class="control-group" style="margin-top: 15px;">
            <label id="solution-label">Pell Solution Index: Pair 3 of 6</label>
            <input type="range" id="solution-index" min="0" max="5" step="1" value="2">
        </div>
        <div class="control-group">
            <label id="speed-label">Orbital Rotation Velocity: 1.0x</label>
            <input type="range" id="rotation-speed" min="0" max="4" step="0.1" value="1">
        </div>
        <div style="margin-top: 10px; text-align: right;"><span class="status-pill">PELL SOLVER: OPTIMIZED</span></div>
    </div>

    <div id="right-panel" class="hud-panel">
        <h2>Collatz Trajectory Mapping</h2>
        <div class="metric-row"><span class="metric-label">Starting Triangular Value:</span><span class="metric-value highlight" id="collatz-start">T_16 = 136</span></div>
        <div class="metric-row"><span class="metric-label">Max Steps to Unity:</span><span class="metric-value">17 Steps</span></div>
        <label style="margin-top: 10px;">Active Step Sequence (3x+1 / 2):</label>
        <div class="trajectory-box" id="collatz-path-display">
            136 -> 68 -> 34 -> 17 -> 52 -> 26 -> 13 -> 40 -> 20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1
        </div>
    </div>

    <script>
        // Pre-computed exact Diophantine solution pairs: [n, m, T_n, T_m]
        const diophantinePairs = [
            { n: 0, m: 1, tn: 0, tm: 1 },
            { n: 2, m: 4, tn: 3, tm: 10 },
            { n: 9, m: 16, tn: 45, tm: 136 },
            { n: 35, m: 61, tn: 630, tm: 1891 },
            { n: 132, m: 229, tn: 8778, tm: 26335 },
            { n: 494, m: 856, tn: 122265, tm: 366796 }
        ];

        // Pre-calculated Collatz sequences for each pair's T_m value
        const collatzSequences = {
            1: [1],
            10: [10, 5, 16, 8, 4, 2, 1],
            136: [136, 68, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1],
            1891: [1891, 5674, 2837, 8512, 4256, 2128, 1064, 532, 266, 133, 400, 200, 100, 50, 25, 76, 38, 19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1],
            26335: [26335, 79006, 39503, 118510, 59255, 177766, 88883, 266650, 133325, 399976, 199988, 99994, 49997, 149992, 74996, 37498, 18749, 56248, 28124, 14062, 7031, 21094, 10547, 31642, 15821, 47464, 23732, 11866, 5933, 17800, 8900, 4450, 2225, 6676, 3338, 1669, 5008, 2504, 1252, 626, 313, 940, 470, 235, 706, 353, 1060, 530, 265, 796, 398, 199, 598, 299, 898, 449, 1348, 674, 337, 1012, 506, 253, 760, 380, 190, 95, 286, 143, 430, 215, 646, 323, 970, 485, 1456, 728, 364, 182, 91, 274, 137, 412, 206, 103, 310, 155, 466, 233, 700, 350, 175, 526, 263, 790, 395, 1186, 593, 1780, 890, 445, 1336, 668, 334, 167, 502, 251, 754, 377, 1132, 566, 283, 850, 425, 1276, 638, 319, 958, 479, 1438, 719, 2158, 1079, 3238, 1619, 4858, 2429, 7288, 3644, 1822, 911, 2734, 1367, 4102, 2051, 6154, 3077, 9232, 4616, 2308, 1154, 577, 1732, 866, 433, 1300, 650, 325, 976, 488, 244, 122, 61, 184, 92, 46, 23, 70, 35, 106, 53, 160, 80, 40, 20, 10, 5, 16, 8, 4, 2, 1],
            366796: [366796, 183398, 91699, 275098, 137549, 412648, 206324, 103162, 51581, 154744, 77372, 38686, 19343, 58030, 29015, 87046, 43523, 130570, 65285, 195856, 97928, 48964, 24482, 12241, 36724, 18362, 9181, 27544, 13772, 6886, 3443, 10330, 5165, 15496, 7748, 3874, 1937, 5812, 2906, 1453, 4360, 2180, 1090, 545, 1636, 818, 409, 1228, 614, 307, 922, 461, 1384, 692, 346, 173, 520, 260, 130, 65, 196, 98, 49, 148, 74, 37, 112, 56, 28, 14, 7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1]
        };

        const container = document.getElementById('canvas-container');
        const scene = new THREE.Scene();
        scene.fog = new THREE.FogExp2(0x050505, 0.012);

        const camera = new THREE.PerspectiveCamera(60, window.innerWidth / window.innerHeight, 0.1, 1000);
        camera.position.set(0, 15, 35);

        const renderer = new THREE.WebGLRenderer({ antialias: true });
        renderer.setSize(window.innerWidth, window.innerHeight);
        renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
        renderer.setClearColor(scene.fog.color);
        container.appendChild(renderer.domElement);

        const controls = new THREE.OrbitControls(camera, renderer.domElement);
        controls.enableDamping = true;
        controls.dampingFactor = 0.05;

        // Lighting
        scene.add(new THREE.AmbientLight(0x222222));
        const pLight = new THREE.PointLight(0x00FF96, 2.0, 80);
        pLight.position.set(10, 20, 15);
        scene.add(pLight);

        // Build 3D Spiral Geometry representing the Collatz trajectory points
        const trajectoryGroup = new THREE.Group();
        scene.add(trajectoryGroup);

        const sphereGeo = new THREE.SphereGeometry(0.3, 16, 16);
        const sphereMat = new THREE.MeshPhongMaterial({ color: 0x00FF96, emissive: 0x003322 });
        const lineMat = new THREE.LineBasicMaterial({ color: 0x00FF96, transparent: true, opacity: 0.5 });

        function updateSceneForPair(index) {
            const pair = diophantinePairs[index];
            document.getElementById('val-n').innerText = `${pair.n} (T_${pair.n} = ${pair.tn})`;
            document.getElementById('val-m').innerText = `${pair.m} (T_${pair.m} = ${pair.tm})`;
            document.getElementById('solution-label').innerText = `Pell Solution Index: Pair ${index + 1} of ${diophantinePairs.length}`;
            document.getElementById('collatz-start').innerText = `T_${pair.m} = ${pair.tm}`;
            
            const seq = collatzSequences[pair.tm] || [pair.tm, 1];
            document.getElementById('collatz-path-display').innerText = seq.join(" -> ");

            // Clear old meshes cleanly
            while(trajectoryGroup.children.length > 0) {
                trajectoryGroup.remove(trajectoryGroup.children[0]);
            }

            // Build new 3D spiral path from the sequence
            const points = [];
            const count = seq.length;
            const maxVal = Math.max(...seq, 10);

            for(let i = 0; i < count; i++) {
                let val = seq[i];
                let angle = (i / count) * Math.PI * 4;
                let radius = 3.0 + (Math.log(val + 1) / Math.log(maxVal + 1)) * 10.0;
                let x = Math.cos(angle) * radius;
                let z = Math.sin(angle) * radius;
                let y = (i - count / 2) * 0.8;

                points.push(new THREE.Vector3(x, y, z));

                const node = new THREE.Mesh(sphereGeo, sphereMat);
                node.position.set(x, y, z);
                trajectoryGroup.add(node);
            }

            const lineGeo = new THREE.BufferGeometry().setFromPoints(points);
            const line = new THREE.Line(lineGeo, lineMat);
            trajectoryGroup.add(line);
        }

        const slider = document.getElementById('solution-index');
        const speedSlider = document.getElementById('rotation-speed');

        slider.addEventListener('input', (e) => {
            updateSceneForPair(parseInt(e.target.value));
        });

        speedSlider.addEventListener('input', (e) => {
            document.getElementById('speed-label').innerText = `Orbital Rotation Velocity: ${parseFloat(e.target.value).toFixed(1)}x`;
        });

        // Initialize with index 2 (n=9, m=16, tm=136)
        updateSceneForPair(2);

        const clock = new THREE.Clock();
        function loop() {
            requestAnimationFrame(loop);
            let speed = parseFloat(speedSlider.value);
            trajectoryGroup.rotation.y += clock.getDelta() * 0.2 * speed;
            controls.update();
            renderer.render(scene, camera);
        }
        
        window.addEventListener('resize', () => {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });
        loop();
    </script>
</body>
</html>
"""

    with open("runyan_collatz_3d.html", "w", encoding="utf-8") as f:
        f.write(html_content)

    print("\n>> SUCCESS: Standalone Collatz 3D Interface fabricated successfully.")
    print(">> Double-click 'runyan_collatz_3d.html' to open it directly in your browser.\n")

if __name__ == "__main__":
    fabricate_optimized_collatz_interface()