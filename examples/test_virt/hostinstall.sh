export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y docker.io
apt-get install -y openvswitch-switch
docker pull ubuntu
docker build -t testvm /vagrant
