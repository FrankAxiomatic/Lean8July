#!/usr/bin/env python3
"""
Secure API Key Setup and Testing Script
Helps configure and test Anthropic API key for automated consultation system
"""

import os
import getpass
from pathlib import Path
import anthropic

def setup_api_key():
    """Securely set up the Anthropic API key"""
    print("🔑 Anthropic API Key Setup")
    print("=" * 40)
    
    # Check if already set
    current_key = os.getenv('ANTHROPIC_API_KEY')
    if current_key:
        print(f"✅ API key already set ({len(current_key)} characters)")
        choice = input("Do you want to use the existing key? (y/n): ").lower()
        if choice == 'y':
            return current_key
    
    # Get API key securely
    print("\n📝 Please enter your Anthropic API key:")
    print("   (Get one at: https://console.anthropic.com/)")
    print("   (Input will be hidden for security)")
    
    api_key = getpass.getpass("API Key: ").strip()
    
    if not api_key:
        print("❌ No API key entered. Exiting.")
        return None
    
    # Validate format
    if not api_key.startswith('sk-ant-'):
        print("⚠️  Warning: API key doesn't start with 'sk-ant-'")
        choice = input("Continue anyway? (y/n): ").lower()
        if choice != 'y':
            return None
    
    return api_key

def test_api_connection(api_key):
    """Test the API key with a simple call"""
    print("\n🧪 Testing API connection...")
    
    try:
        client = anthropic.Anthropic(api_key=api_key)
        
        # Simple test call
        response = client.messages.create(
            model="claude-3-haiku-20240307",  # Use cheaper model for testing
            max_tokens=50,
            messages=[{
                "role": "user", 
                "content": "Say 'API connection successful!'"
            }]
        )
        
        result = response.content[0].text
        print(f"✅ API test successful!")
        print(f"📝 Response: {result}")
        return True
        
    except anthropic.AuthenticationError:
        print("❌ Authentication failed - invalid API key")
        return False
    except anthropic.APIError as e:
        print(f"❌ API error: {e}")
        return False
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        return False

def save_api_key_to_env(api_key):
    """Save API key to local .env file"""
    env_file = Path(".env")
    
    # Read existing .env or create new
    env_content = ""
    if env_file.exists():
        env_content = env_file.read_text()
    
    # Remove existing ANTHROPIC_API_KEY line
    lines = env_content.split('\n')
    lines = [line for line in lines if not line.startswith('ANTHROPIC_API_KEY=')]
    
    # Add new API key
    lines.append(f"ANTHROPIC_API_KEY={api_key}")
    
    # Write back
    env_file.write_text('\n'.join(lines))
    print(f"💾 API key saved to {env_file.absolute()}")

def set_session_env(api_key):
    """Set API key for current session"""
    os.environ['ANTHROPIC_API_KEY'] = api_key
    print("🔧 API key set for current session")

def main():
    """Main setup flow"""
    print("🚀 Automated Claude Consultation Setup")
    print("=" * 50)
    
    # Step 1: Get API key
    api_key = setup_api_key()
    if not api_key:
        return
    
    # Step 2: Test connection
    if not test_api_connection(api_key):
        print("\n❌ API test failed. Please check your key and try again.")
        return
    
    # Step 3: Save and set environment
    choice = input("\n💾 Save API key to .env file? (y/n): ").lower()
    if choice == 'y':
        save_api_key_to_env(api_key)
    
    set_session_env(api_key)
    
    # Step 4: Ready to use
    print("\n🎉 Setup complete! Ready to use automated consultation.")
    print("\n🚀 Next steps:")
    print("   1. Run: python3 test_automated_consultation.py")
    print("   2. Or: python3 automated_claude_consultation.py 'your_consultation_id'")
    
    # Step 5: Offer immediate test
    choice = input("\n🧪 Run automated consultation test now? (y/n): ").lower()
    if choice == 'y':
        print("\n" + "="*50)
        print("🤖 Running Automated Consultation Test...")
        try:
            import asyncio
            from automated_claude_consultation import AutomatedClaudeConsultation
            
            async def run_test():
                consultant = AutomatedClaudeConsultation(api_key=api_key)
                result = await consultant.run_consultation(
                    consultation_id="setup_test",
                    request_file="opus_advice.md"
                )
                
                if result["status"] == "completed":
                    print(f"\n✅ Consultation successful!")
                    print(f"📁 Response: {result['response_file']}")
                else:
                    print(f"\n❌ Consultation failed: {result.get('error')}")
            
            asyncio.run(run_test())
            
        except Exception as e:
            print(f"\n❌ Test failed: {e}")
            print("You can run tests manually later.")

if __name__ == "__main__":
    main() 