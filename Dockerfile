FROM ubuntu:24.10

RUN apt update && apt install -y \
python3 \
pipx \
build-essential \
python-is-python3 \
curl \
git 

RUN apt install -y \
dpkg-dev \
python3-dev \
freeglut3-dev \
libgl1-mesa-dev \
libglu1-mesa-dev \
libgstreamer-plugins-base1.0-dev \
libgtk-3-dev \
libjpeg-dev \
libnotify-dev \
libpng-dev \
libsdl2-dev \
libsm-dev \
libtiff-dev \
libwebkit2gtk-4.1-dev \
libxtst-dev \
libgtk2.0-dev

RUN apt install -y \
python-dev-is-python3 \
gcc \
python3-pip

RUN pipx install poetry 

ENV PATH="$PATH:~/.local/bin"

WORKDIR /home/workspace
