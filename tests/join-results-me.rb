while true
  file = $stdin.readline()
  file.strip!
  break if file == "q" 

  p file

  content = File.read(file)

  begin
    i = 0
    lines = content.lines
    output_lines = []
    while i < lines.length do
      if (i+1 < lines.length) && (lines[i+1].split.first == "===") then
        i+=1
        next
      end
      # p i
      output = ""
      words = lines[i].split # name + encoding
      output += File.dirname(file) + "/" + words[1] + " " + words[2].split("=").last + " "
      i+=1
      words = lines[i].split # vars
      output += words[4] + " "
      i+=1
      words = lines[i].split # cls
      output += words[4] + " "
      i+=1
      words = lines[i].split # time
      output += words[3] + " " 
      i+=1
      words = lines[i].split # sat?
      output += words[0]
      i+=1
      output_lines << output
    end
    
    File.open("me-results", "a") do |f|
      output_lines.each { |l| f.puts l }
    end

  rescue TypeError => e
    File.open("me-results-errors", "a") do |f|
      f.puts file
    end
  rescue NoMethodError => e
    File.open("me-results-errors", "a") do |f|
      f.puts file
    end
  end
end
