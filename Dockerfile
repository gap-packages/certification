FROM gapsystem/gap-docker

RUN sudo pip3 install ipywidgets RISE

RUN jupyter-nbextension install rise --user --py

RUN jupyter-nbextension enable rise --user --py

# Update version number each time after gap-docker container is updated
ENV GAP_VERSION 4.11.1

USER gap

# install this package
WORKDIR /home/gap/inst/gap-${GAP_VERSION}/pkg

RUN wget https://github.com/gap-packages/certification/archive/refs/heads/main.zip \
    && unzip main.zip \
    && rm main.zip \
    && mv certification-main certification

WORKDIR /home/gap/inst/gap-${GAP_VERSION}/pkg/certification
