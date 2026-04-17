.PHONY: web web-install web-test web-build web-dev

WEB_DIR := web

web-install:
	cd $(WEB_DIR) && npm install

web-test:
	cd $(WEB_DIR) && npx vitest run

web-build:
	cd $(WEB_DIR) && npm run build

web-dev:
	cd $(WEB_DIR) && npm run dev

# Default web target: install + test + build a distributable bundle
web: web-install web-test web-build
	@echo
	@echo "Built $(WEB_DIR)/dist/. Copy into ai4fm with:"
	@echo "  rsync -a $(WEB_DIR)/dist/ /path/to/ai4fm/src/_static/demos/microwave/"
