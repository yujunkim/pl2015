file = File.open("checker.log","w")
40.times do |i|
  next if i == 0
  number = '%02d' % i
  file.write("\n\n\n\n\nNumber #{number} Homework Start\n======================================\n\n\n\n\n\n")
  filename = "Assignment05_#{number}.v"
  need_check = "~/Dropbox/study/2015/programming_language/pl2015/sf/#{filename}"
  checker_folder = "~/Dropbox/study/2015/programming_language/basic_pl2015/sf"
  `cp #{need_check} #{checker_folder}`
  puts "[#{filename}] copy to basic"
  out = `cd #{checker_folder}; make clean ; make`
  puts "[#{filename}] end compile"
  `cd #{checker_folder}; git reset --hard HEAD`
  puts "[#{filename}] git clean"

  file.write(out)
  file.write("\n\n\n\n\nNumber #{number} Homework End\n======================================\n\n\n\n\n\n")
end
