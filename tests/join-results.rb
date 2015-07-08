
while true
  file = $stdin.readline()
  file.strip!
  break if file == "q"

  p file

  content = File.read(file)
  
  i = 0
  lines = content.lines
  output_lines = []
  while i < lines.length do
    if (i+1 < lines.length) && (lines[i+1].split.first == "===") then
      i+=1
      next
    end
    p i
    output = ""
    words = lines[i].split # name
    output += File.dirname(file) + "/" + words[1] + " "
    i+=1
    words = lines[i].split # vars cls
    output += words[5] + " " + words[7] + " "
    i+=1
    words = lines[i].split # sat?
    output += words[1] + " " 
    i+=1
    words = lines[i].split # time
    output += words[1]
    i+=1
    if i < lines.length && lines[i].split.first == "c" then
      i+=1
    end
    output_lines << output
  end
  
  File.open("ll-results", "a") do |f|
    output_lines.each { |l| f.puts l }
  end
end
