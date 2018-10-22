# src_dir = File.join("D:", "workspace-juno", "dts_testcases", "**", "*.cpp")
# report_dir = File.join("D:", "workspace-juno", "dts_testcases", "report")
src_dir = File.join(".", "**", "*.c")
report_dir = File.join(".", "report")
layout = File.read "layout.txt"
glob_type = ""
Dir.glob(src_dir).each do |file|
  puts file
  report = File.join(report_dir, file.split("/")[1] + "_report.txt")
  type = file.split("/")[3]
  #puts type
  if glob_type == type
    layout = File.read report
  else
    glob_type = type
    layout = File.read "layout.txt"
  end
  name = file.split("/")[2].split(".")[0..1].join(".")
  idx = layout.index "\n", layout.index(name)
  pre = layout[0..idx]
  suf = layout[idx + 1, layout.length - 1]
  #puts suf
  #puts File.join(report_dir, file.split("/")[3] + "_report.txt")
  input = File.read file
  content = pre + input + suf
  f = File.open(report, 'w')
  f.puts content
  f.close
end

puts "finish"