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
      words = lines[i].split # name 
      output += File.dirname(file) + "/" + words[1] + " "
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
     
      if ( (i >= lines.length) || (lines[i].split.first == "==="))
        output +="INDETERMINED"
        output_lines << output
        next
      end
     
      words = lines[i].split # sat?
      output += words[0]
      i+=1
      output_lines << output
    end
    
    File.open("mc-results", "a") do |f|
      output_lines.each { |l| f.puts l }
    end

  rescue TypeError => e
#    raise Exception
    File.open("mc-results-errors", "a") do |f|
      f.puts file
    end
  rescue NoMethodError => e
#    raise Exception
    File.open("mc-results-errors", "a") do |f|
      f.puts file
    end
  end
end
