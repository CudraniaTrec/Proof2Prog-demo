import matplotlib.pyplot as plt
import numpy as np

file=open('log.txt', 'r')
lines=file.readlines()

total=50
line0=lines[0].split()
success_proof,fail_proof=int(line0[0]),int(line0[1])
line1=lines[1].split()
success_classic,fail_classic=int(line1[0]),int(line1[1])

succ_time_proof=list(map(float,lines[2].split()))[-10:]
succ_time_classic=list(map(float,lines[3].split()))[-10:]

def autolabel(rects):
    for rect in rects:
        height = rect.get_height()
        plt.text(rect.get_x()+rect.get_width()/2.-0.08, 1.03*height,
                  '%s' % int(height), size=10)

pic1=plt.bar(['Search Proof','Search Program'],
             [success_proof/total,success_classic/total],color=['green','red'],width=0.5)
plt.bar_label(pic1,fmt='%.2f')
plt.title('Success Rate')
plt.savefig('output/success_rate.png')
plt.close()

pic2=plt.bar(['Search Proof','Search Program'],
             [fail_proof/total,fail_classic/total],color=['green','red'],width=0.5)
plt.bar_label(pic2,fmt='%d')
plt.title('Fail Times Average')
plt.savefig('output/fail_times.png')
plt.close()

x=np.arange(len(succ_time_proof))
w=0.35
fig,ax=plt.subplots()
rects1=ax.bar(x-w/2,succ_time_proof,width=w,label='Search Proof')
rects2=ax.bar(x+w/2,succ_time_classic,width=w,label='Search Program')
ax.set_ylabel('Time (ms)')
ax.set_xlabel('Test Case Number')
ax.set_xticks(x)
ax.set_title('Time Cost')
ax.legend()
# plt.bar_label(rects1,fmt='%.2f')
# plt.bar_label(rects2,fmt='%.2f')
plt.savefig('output/time.png')
plt.close()