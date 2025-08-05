#!/bin/bash

# Terry Ecom Link Checker - Quick Deployment Script
# This script helps you deploy the application quickly

echo "🚀 Terry Ecom Link Checker - Deployment Script"
echo "================================================"

# Check if we're in the right directory
if [ ! -f "app.py" ]; then
    echo "❌ Error: app.py not found. Please run this script from the project root directory."
    exit 1
fi

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Check required tools
echo "🔍 Checking required tools..."

if ! command_exists python3; then
    echo "❌ Python 3 is required but not installed."
    exit 1
fi

if ! command_exists git; then
    echo "❌ Git is required but not installed."
    exit 1
fi

echo "✅ Required tools found"

# Create virtual environment if it doesn't exist
if [ ! -d "venv" ]; then
    echo "📦 Creating virtual environment..."
    python3 -m venv venv
fi

# Activate virtual environment
echo "🔧 Activating virtual environment..."
source venv/bin/activate

# Install dependencies
echo "📚 Installing dependencies..."
pip install -r requirements.txt

# Create .env file if it doesn't exist
if [ ! -f ".env" ]; then
    echo "⚙️ Creating .env file..."
    cp .env.example .env
    echo "📝 Please edit .env file with your configuration"
fi

# Run tests (basic functionality check)
echo "🧪 Running basic functionality test..."
python3 -c "
import app
print('✅ Flask app imports successfully')
"

# Git operations
echo "📡 Git repository setup..."

if [ ! -d ".git" ]; then
    echo "🔄 Initializing Git repository..."
    git init
    git add .
    git commit -m "Initial commit - Terry Ecom Link Checker"
else
    echo "✅ Git repository already exists"
fi

# Create .gitignore if it doesn't exist
if [ ! -f ".gitignore" ]; then
    echo "📝 Creating .gitignore..."
    cat > .gitignore << 'EOF'
__pycache__/
*.pyc
.env
venv/
.DS_Store
*.log
crawl_results_*
EOF
fi

echo ""
echo "🎉 Setup Complete!"
echo "=================="
echo ""
echo "Next steps:"
echo "1. Edit .env file with your configuration"
echo "2. For local development:"
echo "   source venv/bin/activate"
echo "   flask run --host=0.0.0.0 --port=5000"
echo ""
echo "3. For production deployment:"
echo "   - Push to GitHub: git remote add origin YOUR_REPO_URL && git push -u origin main"
echo "   - Deploy on Render.com using the repository"
echo ""
echo "4. Optional: Configure email settings in .env for feedback functionality"
echo ""
echo "🌐 Local URL: http://localhost:5000"
echo "📧 Support: terry@terryecom.com"
echo ""
echo "Happy link checking! 🔗✨"