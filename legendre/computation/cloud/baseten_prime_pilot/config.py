"""CPU-only, single-node Baseten Training Job template."""
import os
from truss_train import definitions as d

vcpu = int(os.environ.get("PILOT_VCPUS", "8"))
if not 1 <= vcpu <= 256:
    raise ValueError("Choose a vCPU count in [1, 256] within the workspace quota")
memory_gib = int(os.environ.get("PILOT_MEMORY_GIB", "16"))
if memory_gib < 1:
    raise ValueError("Choose a positive memory request in GiB")
rows = int(os.environ.get("PILOT_ROWS", "1000000"))
repeats = int(os.environ.get("PILOT_REPEATS", "3"))
if rows <= 0 or repeats <= 0:
    raise ValueError("Choose positive sample size and repeat count")
environment = {
    "PILOT_ROWS": str(rows),
    "PILOT_REPEATS": str(repeats),
    "PILOT_MEMORY_GIB": str(memory_gib),
}
if os.environ.get("PILOT_STORAGE_PROBE") == "1":
    environment.update({
        "PILOT_STORAGE_PROBE":"1",
        "PILOT_PUT_URL":d.SecretReference(name="prime_pilot_put_url"),
        "PILOT_GET_URL":d.SecretReference(name="prime_pilot_get_url"),
    })
project = d.TrainingProject(
    name="prime-witness-calibration",
    job=d.TrainingJob(
        image=d.Image(base_image="python:3.12-slim-bookworm"),
        compute=d.Compute(node_count=1, cpu_count=vcpu, memory=f"{memory_gib}Gi"),
        workspace=d.Workspace(exclude_dirs=["dist", "__pycache__", ".venv", "prime-pilot"]),
        runtime=d.Runtime(
            start_commands=[f"bash run.sh {vcpu}"],
            environment_variables=environment,
            checkpointing_config=d.CheckpointingConfig(enabled=True),
        ),
    ),
)
