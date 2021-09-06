#!/usr/bin/env python3
from math import inf as infinity, trunc
import math
from random import choice
import platform
import time
from os import system
from typing import Coroutine

# 3 biến ngay dưới đây có thể thay đổi
# Độ sâu tối đa của cây tìm kiếm, nôm na là tính trước bao nhiêu bước, nếu đến độ sâu này mà chưa biết được kết quả(thắng thua hòa) thì phải dùng heuristic. Độ sâu càng lớn thì tính càng lâu. maxmoves phải > 0, với maxmoves > số ô của bàn cờ thì sẽ ko dùng đến heuristic và máy tính ko bao giờ thua.
maxmoves = 1
# Số ô liên tiếp để thắng
wincount= 4
#số hàng hoặc cột của bàn cờ. tốc độ chạy không phụ thuộc vào gridsize, nó phụ thuộc vào hình chữ nhật bé nhất chứa tất cả nước đi.
gridsize = 6  

#Độ sâu của state root (độ sâu giảm dần)
rootdepth = gridsize*gridsize

#vị trí trái trên và phải dưới. 2 vị trí này tạo thành 1 hình chữ nhật bé nhất mà chứa toàn bộ nước đi. Khi cần xét thắng thua thì chỉ cần xem xét bên trong hcn này chứ ko cần phải xét toàn bộ bàn cờ.
topleft=[-1,-1]
botright=[-1,-1]

#nước đánh cuối cùng mà máy hoặc người vừa đi. Nếu có chiến thắng thì chỉ cần xem xét hàng ngang cột dọc đường chéo chứa nước đi này.
lastmove =[-1,-1]

HUMAN = -1
COMP = +1
board = []
moves = {}

#khởi tạo bàn cờ
def initboard(grids):
    count = grids
    for i in range(count):
        board.append([])
        for _ in range(count):
            board[i].append(0)

#Tạo danh sách tọa độ của nước đi
def initmoves(grids):
    limit = grids*grids
    count = grids
    for i in range(limit):
        moves[i+1]=[int(i//count), int(i%count)]

#xác định chiến thắng dựa trên nước đi cuối cùng
def wins(state, player,cor):
    #hàng ngang
    sum= wincount * player
    i= min(botright[1]-wincount+1, cor[1])
    while i>= topleft[1] :
        for j in range(wincount):
            sum-= state[cor[0]][i+j]
        if sum==0: 
            return True 
        sum= wincount * player
        i= i-1

    #hàng dọc
    i= min(botright[0] - wincount+1, cor[0])
    while i >= topleft[0]:
        for j in range(wincount):
            sum-= state[i+j][cor[1]]
        if sum==0: 
            return True 
        sum= wincount * player
        i= i-1

    #2 đường chéo
    i = min(botright[0] - wincount+1, cor[0])
    j = cor[1] - cor[0]+i
    temp = j
    j= min(botright[1]-wincount+1, j)
    i= i - temp+j
    while i>=topleft[0] and j>= topleft[1]:
        for k in range(wincount):
            sum-= state[i+k][j+k]
        if sum==0: 
            return True 
        sum= wincount * player
        i= i-1
        j= j-1
     
    j= max(topleft[1]+wincount-1, cor[1])
    i= cor[0] - j+cor[1]
    temp= i
    i= min(botright[0]-wincount+1, i)
    j = j + temp - i
    if i>= botright[0] or j<= topleft[1]: 
        return False

    while i>= topleft[0] and j <= botright[1]:
        for k in range(wincount):
            sum-= state[i+k][j-k]
        if sum==0: 
            return True 
        sum= wincount * player
        i= i-1
        j= j+1
    return False

#game kết thúc thì return người chiến thắng, chưa kết thúc thì return 0
def game_over(state,player,cor):
    if wins(state, player, cor ):
        return player
    return 0   

#toàn bộ ô trống
def emptycells(state):
    cells = []
    for x, row in enumerate(state):
        for y, cell in enumerate(row):
            if cell == 0:
                cells.append([x, y])
    return cells

#lấy ra những ô trống xung quanh hình chữ nhật chứa toàn bộ nước cờ.
def smartemptycells(state):
    cells = []
    i= max(topleft[0] - wincount +1,0)
    x= min(botright[0]+wincount -1,gridsize-1)
    while i<= x:
        j= max(topleft[1]- wincount +1,0)
        y= min(botright[1]+wincount -1,gridsize-1)
        while j<=y:
            if state[i][j]==0:
                cells.append([i,j])
            j+=1
        i+=1
    return cells

#heuristic function. Đánh giá số điểm của trạng thái, với wincount =4 thì xem xét 4 ô liên tiếp nhau 
def evaluate(state, player):
    score =0
    a =2
    #tạo hình chữ nhật chứa toàn bộ nước đi những phải đủ lớn để mỗi ô của máy hoặc người có thể là ô đầu và ô cuối của chuỗi 4 ô liên tiếp
    tl= [max(topleft[0] - wincount +1 ,0), max(topleft[1] - wincount+1, 0)]
    br= [min(botright[0] + wincount -1, gridsize-1), min(botright[1] + wincount-1, gridsize-1)]
    
    count = wincount
    # hàng ngang
    for r in range(tl[0], br[0]+1):
        for c in range(tl[1], br[1] - count+2):
            sum=0
            checkposone = 0
            checknegone = 0                  
            for k in range(count):
                sum += state[r][c+ k]
                #Kiểm tra xem 1 và -1 có xuất hiện trong 4 ô không, -1 or bất kỳ số nào luôn =-1 nên nếu kết quả là -1 nghĩa là -1 đã xuất hiện
                checkposone |= -state[r][c+ k]
                checknegone |= state[r][c+k] 
            score += getscore(sum, -checkposone, checknegone, count, a, player)       
    #hàng dọc       
    for c in range(tl[1], br[1]+1):
        for r in range(tl[0], br[0] - count+2):
                sum=0
                checkposone = 0
                checknegone = 0          
                for k in range(count):                  
                    sum += state[r+ k][c]
                    checkposone |= -state[r+ k][c]
                    checknegone |= state[r+ k][c]
                score += getscore(sum, -checkposone, checknegone, count, a, player)                       
    #2 đường chéo
    for i in range(tl[0], br[0]-count+2):
        for j in range(tl[0], br[1] - count+2):
            bsum =0
            bcheckposone = 0
            bchecknegone = 0       
            fcheckposone = 0
            fchecknegone = 0
            fsum =0          
            for k in range(count):
                bsum += state[i+k][j+k] 
                bcheckposone |= -state[i+k][j+k] 
                bchecknegone |= state[i+k][j+k] 
                fsum += state[i+k][j+ count-1- k]
                fcheckposone |=  -state[i+k][j+ count-1- k]
                fchecknegone |=  state[i+k][j+ count-1- k]
            score += getscore(bsum, -bcheckposone, bchecknegone, count, a, player)       
            score += getscore(fsum, -fcheckposone, fchecknegone, count, a, player)                           
    return score


#đánh giá điểm. 
#VD 4 ô liên tiếp giống nhau là thắng thì xem xét 4 ô liên tiếp bất kỳ nếu đã có 3 ô giống nhau và 1 ô trống thì được điểm số lớn, 2 ô giống nhau và 2 ô trống thì điểm trung bình, 3 ô trống thì được 1 chênh lệch điểm của máy và người là điểm số cuối cùng  
def getscore(sum, checkposone, checknegone, count,a, player):
    #điểm có chỉnh tùy thích nhưng phải làm sao để điểm của hàm này luôn < điểm được xác định khi tìm ra người chơi chiến thắng trong hàm minimax
    #điểm có chỉnh tùy thích nhưng phải làm sao để điểm khi có số ô giống nhau = wincount -1 phải luôn >  điểm khi số ô giống nhau = wincount-2
    #khi điểm của đối thủ cao hơn thì player mới có xu hướng chặn đối thủ
    scores = {
        (wincount-1)*player:10000 *player,  #điểm của player: khi có số ô giống nhau = wincount -1.
        (wincount-2)*player:100 *player,  #điểm của player: khi có số ô giống nhau = wincount -2.
        (wincount-1)*-player:40000 *-player,  #điểm của đối thủ: khi có số ô giống nhau = wincount -1.
        (wincount-2)*-player:400*-player}  #điểm của đối thủ: khi có số ô giống nhau = wincount -2.
    #tổng điểm của người
    hscore=0
    #tổng điểm của máy
    cscore = 0

    #wincount =4, TH: 2 ô giống nhau và 2 ô trống.
    if sum >= COMP* (count- a) and (checknegone!= -1):
        cscore += scores[sum]
    #wincount =4, TH: 3 ô trống
    if sum > 0 and sum < COMP* (count- a) and (checknegone!= -1) :
        cscore+= sum

    if sum <= HUMAN * (count -a) and (checkposone!= 1):
        hscore += scores[sum]
    if sum < 0 and sum > HUMAN* (count- a) and (checkposone!= 1):
        hscore += sum
    return hscore + cscore

#nước đi hợp lệ
def validmove(x, y):
    if [x, y] in emptycells(board):
        return True
    else:
        return False

#ghi nhận nước đi
def set_move(x, y, player):
    if validmove(x, y):
        board[x][y] = player
        return True
    else:
        return False


#với maxmoves =1 thì tỉa nhánh chả có tác dụng gì :((
def minimax(state, depth, player, lastmove, al, be):
    if player == COMP:
        best = [-1, -1, al]
    else:
        best = [-1, -1, be]

    #set lại tọa độ 2 điểm của hình chữ nhật
    setarea(lastmove)
    #có người chiến thắng hay ko
    winner = game_over(state, -player, lastmove)
    if depth == 0 or winner!=0:
        if winner == 0 : 
            return [-1,-1,0]
        #điểm số của state càng gần root thì càng có lợi
        score = -player* depth + -player * 1000000
        return [-1, -1, score]
    #đến độ sâu tối đa cho phép thì dùng heuristic
    if rootdepth - depth >= maxmoves:               
        score = evaluate(state, -player)
        return [-1,-1,score]     

    cells = smartemptycells(state)
    for cell in cells:
        #lưu trữ lại tọa độ của hcn và state  
        temptl0 = topleft[0]
        temptl1 = topleft[1]
        tempbr0 = botright[0]
        tembr1 = botright[1]
        x, y = cell[0], cell[1]
        state[x][y] = player               
        score = minimax(state, depth - 1, -player, [x,y], al, be)   
        #hồi phục trạng thái cũ
        state[x][y] = 0
        topleft[0]= temptl0
        topleft[1] = temptl1
        botright[0] = tempbr0
        botright[1] = tembr1
      
        score[0], score[1] = x, y     
        if player == COMP:          
            if score[2] > best[2]:
                best = score  
                al= score[2]          
        else:           
            if score[2] < best[2]:
                best = score  
                be = score[2]          
        if al>be:           
            break

    return best

#xóa màn hình
def clean():
    os_name = platform.system().lower()
    if 'windows' in os_name:
        system('cls')
    else:
        system('clear')
#set độ sâu của root state
def setrootdepth():
    global rootdepth
    rootdepth-=1
#hiển thị
def render(state, c_choice, h_choice):
    chars = {
        -1: h_choice,
        +1: c_choice,
        0: ' '
    }
    str_line = '---------------------------------------------------------------------'

    print('\n' + str_line)
    for row in state:
        for cell in row:
            symbol = chars[cell]
            print(f'| {symbol} |', end='')
        print('\n' + str_line)

#set lại tọa độ hcn
def setarea(cor):
    if cor[0] < topleft[0]:
        topleft[0]= max(cor[0],0)
    if cor[1] < topleft[1]:
        topleft[1] = max(cor[1],0)
    if cor[0] > botright[0]:
        botright[0]= min(cor[0],gridsize-1)
    if cor[1]> botright[1]:
        botright[1] = min(cor[1], gridsize-1)
#lượt đi của máy
def ai_turn(c_choice, h_choice):
    depth = len(emptycells(board))
    if depth == 0 or game_over(board,board[lastmove[0]][lastmove[1]], lastmove):
        return

    clean()
    print(f'Computer turn [{c_choice}]')
    render(board, c_choice, h_choice)
   
    if depth == gridsize* gridsize:
        x = choice([0, 1, 2])
        y = choice([0, 1, 2])
        topleft[0]= x
        topleft[1]= y
        botright[0]= x
        botright[1]=y
        #thực hiện 1 nước đi thì độ sâu của root sẽ giảm
        setrootdepth()
    else:
        move = minimax(board, depth, COMP,lastmove,-infinity, +infinity)
        x, y = move[0], move[1]     
        setarea([x,y])
        setrootdepth()
        lastmove[0] =x
        lastmove[1] = y
    set_move(x, y, COMP)
#lượt đi của người     
def human_turn(c_choice, h_choice):
    depth = len(emptycells(board))
    if depth == 0 or game_over(board,board[lastmove[0]][lastmove[1]], lastmove):
        return
    move = -1  
    clean()
    print(f'Human turn [{h_choice}]')
    render(board, c_choice, h_choice)

    while move < 1 or move > gridsize*gridsize:
        try:
            move = int(input('Enter number:'))
            coord = moves[move]
            can_move = set_move(coord[0], coord[1], HUMAN)
            
            if not can_move:
                print('Bad move')
                move = -1
            else:                
                lastmove[0] = coord[0]
                lastmove[1] = coord[1]
                setrootdepth()
                if depth == gridsize*gridsize:
                    topleft[0]= coord[0]
                    topleft[1]= coord[1]
                    botright[0]= coord[0]
                    botright[1]= coord[1]
                else:
                    setarea([coord[0],coord[1]])   
                               
        except (EOFError, KeyboardInterrupt):
            print('Bye')
            exit()
        except (KeyError, ValueError):
            print('Bad choice')


def main():
    initmoves(gridsize)
    initboard(gridsize)
    clean()
    h_choice = ''  # chọn X hoặc O
    c_choice = ''  # chọn X hoặc O
    first = ''  # người chơi có đi trước không

    # Người chơi chọn X hoặc O
    while h_choice != 'O' and h_choice != 'X':
        try:
            print('')
            h_choice = input('Choose X or O\nChosen: ').upper()
        except (EOFError, KeyboardInterrupt):
            print('Bye')
            exit()
        except (KeyError, ValueError):
            print('Bad choice')

    # Thiết lập lựa chọn của máy
    if h_choice == 'X':
        c_choice = 'O'
    else:
        c_choice = 'X'

    # Hỏi người chơi có chơi trước không
    clean()
    while first != 'Y' and first != 'N':
        try:
            first = input('First to start?[y/n]: ').upper()
        except (EOFError, KeyboardInterrupt):
            print('Bye')
            exit()
        except (KeyError, ValueError):
            print('Bad choice')
    
    #Trò chơi bắt đầu.
    while len(smartemptycells(board)) > 0 and not game_over(board,board[lastmove[0]][lastmove[1]], lastmove):
        if first == 'N':
            ai_turn(c_choice, h_choice)
            first = ''

        human_turn(c_choice, h_choice)
        ai_turn(c_choice, h_choice)

    # Game over 
    if wins(board, HUMAN,lastmove):
        clean()
        print(f'Human turn [{h_choice}]')
        render(board, c_choice, h_choice)
        print('YOU WIN!')
    elif wins(board, COMP,lastmove):
        clean()
        print(f'Computer turn [{c_choice}]')
        render(board, c_choice, h_choice)
        print('YOU LOSE!')
    else:
        clean()
        render(board, c_choice, h_choice)
        print('DRAW!')
    exit()
if __name__ == '__main__':
    main()
