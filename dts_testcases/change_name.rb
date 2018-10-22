src_dir = File.join("D:", "workspace-juno", "dts_testcases", "**", "*.cpp")
# src_dir = File.join("D:", "Dropbox", "dev", "**", "*.cpp")
Dir.glob(src_dir).each do |file|
  puts file
  fun_name_suffix = "_" << file.split("/")[4].split(".")[0..1].join("_")
  # puts fun_name_suffix
  content = File.read(file)
  content.gsub!(/([a-zA-Z_0-9]+\()/) do |match|
    # m = match[0..-2]
    m = match.split("_")[0]
    print match + " ----- "
    print m + " " + "+" * 5 + " "
    if m == "main"
      print "ff#{fun_name_suffix}(\n"
      "ff#{fun_name_suffix}("
    elsif m == "free(" || m == "malloc(" || m == "sizeof(" || m == "if(" || m == "time(" || m == "srand(" || m == "rand("
      print "#{m}\n"
      "#{m}"
    else
      print "#{m}#{fun_name_suffix}(\n"
      "#{m}#{fun_name_suffix}("
    end
  end

  content.gsub!(/[A-Z]+[_0-9]+/) do |match| 
    puts match + " ---> "
    n = match.split("_")[0] + fun_name_suffix
    print n + "\n"
    n
  end

  f = File.open file, 'w'
  f.puts content
  f.close
end