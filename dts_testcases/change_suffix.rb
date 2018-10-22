# src_dir = File.join("D:", "workspace", "_DTSEmbed", "dts_testcases", "**", "*.c")
src_dir = File.join(".", "**", "*.c")
Dir.glob(src_dir).each do |file|
  puts file
  # puts file[0..-3]
  # File.rename(file, file[0..-3])
  content = File.read file
  File.delete file if content.include? "class"
end