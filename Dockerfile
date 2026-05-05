# Hugging Face Spaces (Docker SDK) builds this image automatically on every
# git push to the Space's `main` branch. Microsoft's Playwright base image
# already has Chromium, ffmpeg, and every system library Chromium needs at
# runtime — saves ~50 lines of `apt-get install` and avoids version drift.
FROM mcr.microsoft.com/playwright/python:v1.47.0-jammy

WORKDIR /app

# App-level Python deps. python-multipart is loaded for the upload endpoints
# even though banner_app.py uses stdlib email parser today — it's pinned in
# case we want to swap to a faster parser later. Pillow / pypdf / python-docx
# / imageio-ffmpeg are required by the existing capture / storyboard /
# CPFP code paths.
RUN pip install --no-cache-dir \
        playwright \
        imageio-ffmpeg \
        pillow \
        pypdf \
        python-docx \
        python-multipart

COPY banner_app.py /app/banner_app.py

# Hugging Face Spaces sets PORT=7860 in the runtime environment — match it.
ENV PORT=7860
ENV PYTHONUNBUFFERED=1

EXPOSE 7860

CMD ["python", "/app/banner_app.py"]
