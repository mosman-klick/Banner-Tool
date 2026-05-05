---
title: Banner Frame Capture
emoji: 🎬
colorFrom: blue
colorTo: indigo
sdk: docker
app_port: 7860
pinned: false
---

# Banner Frame Capture

Internal Klick tool for capturing frames, ISI images, MP4 videos, and
storyboards from HTML banner ads.

## Features

- **Frame Capture** — load a banner from a Ziflow proof URL, DoubleClick
  Studio external-preview URL, Klick AdPiler staging URL, or by uploading a
  banner folder; pick frame timings; export PNGs + MP4 + ISI image/HTML.
- **ISI Compare** — diff the banner's ISI text against an uploaded PDF/Word
  reference document, word-by-word.
- **Banner Compare** — load two banners side-by-side, scrub them in
  lockstep, see visual + text diffs.
- **Multi-Banner Viewer** — load every size from a Klick staging or
  DoubleClick Studio URL at once and capture them all in one bundle.
- **Storyboard** — generate a PDF of captured frames + animation notes;
  also drop captured frames into an existing storyboard PDF.
- **CPFP** — change-proof full-proof: diff two storyboard PDFs page-by-page
  with optional Claude-powered analysis.

## Hosting

This Space runs on Hugging Face's free CPU basic tier (16 GB RAM, 2 vCPU).
The `Dockerfile` uses Microsoft's Playwright base image so Chromium and
all its system deps are baked in. No login is required; share the URL
internally only.

## Updates

`git push origin main` to the source GitHub repo → a GitHub Action mirrors
to this Space → the image rebuilds in ~2 minutes.

## Local development

```bash
docker build -t banner-capture .
docker run -p 7860:7860 banner-capture
# open http://localhost:7860
```

Or, on macOS without Docker, the original local-app workflow still works
(see `_run.sh`).
