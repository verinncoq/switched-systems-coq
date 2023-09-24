New-Item -ItemType Directory -Force -Path target

#Compile dependencies
coqc -w none -R target CoqE2EAI dependencies\coquelicot_extensions\matrix_extensions.v -o target\matrix_extensions.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\piecewise_affine.v -o target\piecewise_affine.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\pwaf_operations.v -o target\pwaf_operations.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\neuron_functions.v -o target\neuron_functions.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\neural_networks.v -o target\neural_networks.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\string_to_number.v -o target\string_to_number.vo
coqc -w none -R target CoqE2EAI dependencies\neural_networks\pendnet.v -o target\pendnet.vo

#Compile project
coqc -w none -R target CoqE2EAI switched_systems.v -o target\switched_systems.vo
coqc -w none -R target CoqE2EAI inverted_pendulum.v -o target\inverted_pendulum.vo