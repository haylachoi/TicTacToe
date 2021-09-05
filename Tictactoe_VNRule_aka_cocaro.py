#!/usr/bin/env python3
from math import inf as infinity, trunc
import math
from random import choice
import platform
import time
from os import system
from typing import Coroutine


#luật chơi việt nam 4 ăn , 5 chặn
# Độ sâu tối đa của cây tìm kiếm, nôm na là tính trước bao nhiêu bước, nếu đến độ sâu này mà chưa biết được kết quả(thắng thua hòa) thì phải dùng heuristic. Độ sâu càng lớn thì tính càng lâu. maxmoves phải > 0, với maxmoves > số ô của bàn cờ thì sẽ ko dùng đến heuristic và máy tính ko bao giờ thua.
maxmoves = 1
# Số ô liên tiếp để thắng
wincount= 4
#số hàng hoặc cột của bàn cờ. tốc độ chạy không phụ thuộc vào gridsize, nó phụ thuộc vào hình chữ nhật bé nhất chứa tất cả nước đi.
gridsize = 10 

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
    start= cor[1]
    end= cor[1]
    while(start-1 >= topleft[1] and state[cor[0]][start-1]==player):
        start-=1
    while(end+1 <= botright[1] and state[cor[0]][ end+1] == player):
        end+=1
    if end-start>= wincount+1:
        return True
    right = True
    left = True
    if start-1 >= topleft[1] and state[cor[0]][start-1]== -player:
        left=False
    if end+1 <= botright[1] and state[cor[0]][ end+1] == -player:
        right= False
    if end-start == wincount  and (left or right):
        return True
    if end- start == wincount-1 and left and right:
        return True

    #hàng dọc
    start= cor[0]
    end= cor[0]
    while(start-1 >= topleft[0] and state[start-1][cor[1]]==player):
        start-=1
    while(end+1 <= botright[0] and state[end+1][cor[1]] == player):
        end+=1
    if end-start>= wincount+1:
        return True
    right = True
    left = True
    if start-1 >= topleft[0] and state[start-1][cor[1]]== -player:
        left=False
    if end+1 <= botright[0] and state[end+1][cor[1]] == -player:
        right= False
    if end-start == wincount  and (left or right):
        return True
    if end- start == wincount-1 and left and right:
        return True

    #2 đường chéo
    tl = [cor[0],cor[1]]
    br = [cor[0], cor[1]]
    length =1
    while br[0]+1 <= botright[0] and br[1] +1 <= botright[1] and state[br[0]+1][br[1]+1] == player:
        br= [br[0]+1,br[1]+1]
        length+=1
    while tl[0]-1 >= topleft[0] and tl[1]-1 >=topleft[1] and state[tl[0]-1][tl[1]-1] == player:
        tl= [tl[0]-1, tl[1]-1]
        length+=1
    if length> wincount+1:
        return True
    left=True
    right= True
    if br[0]+1 <= botright[0] and br[1] +1 <= botright[1] and state[br[0]+1][br[1]+1] == -player:
        right= False
    if tl[0]-1 >= topleft[0] and tl[1]-1 >=topleft[1] and state[tl[0]-1][tl[1]-1] == -player:
        left= False
    if length == wincount+1 and (left or right):
        return True
    if length == wincount  and left and right:
        return True
    
    tr=[cor[0],cor[1]]
    bl = [cor[0],cor[1]]
    length=1
    while tr[0]-1 >= topleft[0] and tr[1]+1 <= botright[1] and state[tr[0]-1][tr[1]+1] == player:
        tr= [tr[0]-1, tr[1]+1]
        length+=1
    while bl[0]+1 <= botright[0] and bl[1]-1 > topleft[1] and state[bl[0]+1][bl[1]-1] == player:
        bl= [bl[0]+1, bl[1]-1]
        length+=1
    if length> wincount+1:
        return True
    left=True
    right= True
    if tr[0]-1 >= topleft[0] and tr[1]+1 <= botright[1] and state[tr[0]-1][tr[1]+1] == -player:
        right = False
    if bl[0]+1 <= botright[0] and bl[1]-1 > topleft[1] and state[bl[0]+1][bl[1]-1] == -player:
        left = False
    
    if length == wincount+1 and (left or right):
        return True
    if length == wincount  and left and right:
        return True

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
def evaluate(state):
    score =0
    a =2
    #tạo hình chữ nhật chứa toàn bộ nước đi những phải đủ lớn để mỗi ô của máy hoặc người có thể là ô đầu và ô cuối của chuỗi 4 ô liên tiếp
    tl= [max(topleft[0] - wincount ,0), max(topleft[1] - wincount, 0)]
    br= [min(botright[0] + wincount , gridsize-1), min(botright[1] + wincount, gridsize-1)]
    
    count = wincount
    scores = {wincount-1:1000, wincount-2:100, -wincount+1:-4000, -wincount+2: -400}

    #hàng
    for r in range(tl[0], br[0]+1):
        #máy   
        start = tl[1]   
        while start <= br[1]-wincount+1:
                sum=0
                end = start+ wincount-1
                if start - 1 >= tl[1] and state[r][start-1]== HUMAN:
                    end+=1
                if end > br[1]:
                    start+=1
                    continue
                if end+1 <= br[1] and state[r][end+1] == HUMAN:
                    start= end+2                 
                    continue
                ci = -1    
                for c in range(end, start-1, -1):
                    if state[r][c] == HUMAN:
                        ci= c
                        break
                    sum+= state[r][c]
                if ci!=-1:
                    start= ci+1
                    end = start + wincount
                    continue               
                if end - start == wincount:
                    sum+= HUMAN
                if sum>= wincount-2:
                    score+= scores[sum]
                elif sum>0: score+= sum
                start+=1
        #người
        start = tl[1]   
        while start <= br[1]-wincount+1:
                sum=0
                end = start+ wincount-1
                if start - 1 >= tl[1] and state[r][start-1]== COMP:
                    end+=1
                if end > br[1]:
                    start+=1
                    continue
                if end+1 <= br[1] and state[r][end+1] == COMP:
                    start= end+2                
                    continue
                ci = -1    
                for c in range(end, start-1, -1):
                    if state[r][c] == COMP:
                        ci= c
                        break
                    sum+= state[r][c]
                if ci!=-1:
                    start= ci+1
                    end = start + wincount
                    continue               
                if end - start == wincount:
                    sum+=COMP
                if sum<= (wincount-2)*HUMAN:
                    score+= scores[sum]
                elif sum<0: score+= sum
                start+=1

    #cột
    for c in range(tl[1], br[1]+1):
        #máy   
        start = tl[0]   
        while start <= br[0]-wincount+1:
                sum=0
                end = start+ wincount-1
                if start - 1 >= tl[0] and state[start-1][c]== HUMAN:
                    end+=1
                if end > br[0]:
                    start+=1
                    continue
                if end+1 <= br[0] and state[end+1][c] == HUMAN:
                    start= end+2
                    end = start + wincount
                    continue
                ci = -1    
                for r in range(end, start-1, -1):
                    if state[r][c] == HUMAN:
                        ci= r
                        break
                    sum+= state[r][c]
                if ci!=-1:
                    start= ci+1
                    end = start + wincount
                    continue               
                if end - start == wincount:
                    sum+= HUMAN
                if sum>= wincount-2:
                    score+= scores[sum] 
                elif sum>0: score+= sum
                start+=1
        #người
        start = tl[0]   
        while start <= br[0]-wincount+1:
                sum=0
                end = start+ wincount-1
                if start - 1 >= tl[0] and state[r][start-1]== COMP:
                    end+=1
                if end > br[0]:
                    start+=1
                    continue
                if end+1 <= br[0] and state[r][end+1] == COMP:
                    start= end+2
                    end = start + wincount
                    continue
                ci = -1    
                for r in range(end, start-1, -1):
                    if state[r][c] == COMP:
                        ci= r
                        break
                    sum+= state[r][c]
                if ci!=-1:
                    start= ci+1
                    end = start + wincount
                    continue               
                if end - start == wincount:
                    sum+=COMP
                if sum<= (wincount-2)*HUMAN:
                    score+= scores[sum]
                elif sum<0: score+= sum
                start+=1

    #2 đường chéo
    for i in range(tl[0], br[0]-count+2):
        for j in range(tl[0], br[1] - count+2):
            #chéo chính, máy
            sum=0
            length = wincount
            if i -1>= tl[0] and j -1 >= tl[1] and state[i-1][j-1] == HUMAN:
                length+=1
            if ((i+ length <= br[0] and j+ length <= br[1]) and state[i+length][j+length]==HUMAN)==False and i+ length-1 <= br[0] and j+ length-1 <= br[1]:                
                ci =0
                for k in range(0, length):                
                    if state[i+k][j+k] == HUMAN:
                        ci=k
                        break
                    sum+= state[i+k][j+k]
                if ci==0:                 
                    if length == wincount+1:
                        sum+= HUMAN
                    if sum>= wincount-2:
                        score+= scores[sum]
                    elif sum>0: score+= sum
            #chéo chính, người
            sum=0
            length = wincount
            if i -1>= tl[0] and j -1 >= tl[1] and state[i-1][j-1] == COMP:
                length+=1
            if ((i+ length <= br[0] and j+ length <= br[1]) and state[i+length][j+length]==COMP)==False and i+ length-1 <= br[0] and j+ length-1 <= br[1]:                
                ci =0
                for k in range(0, length):                
                    if state[i+k][j+k] == COMP:
                        ci=k
                        break
                    sum+= state[i+k][j+k]
                if ci==0:                 
                    if length == wincount+1:
                        sum+= COMP
                    if sum<= (wincount-2)*HUMAN:
                        score+= scores[sum]
                    elif sum<0: score+= sum
            
            #chéo phụ, máy
            sum=0
            length = wincount
            if i -1>= tl[0] and j + wincount <= br[1] and state[i-1][j+wincount] == HUMAN:
                length+=1
            if ((i+ length <= br[0] and j- length +wincount >= tl[1]) and state[i+length][j- length +wincount]==HUMAN)==False and i+ length -1<= br[0] and j- length+1 +wincount >= tl[1]:                
                ci =0
                for k in range(0, length):                
                    if state[i+k][j+wincount-k-1] == HUMAN:
                        ci=k
                        break
                    sum+= state[i+k][j+wincount-k-1]
                if ci==0:                 
                    if length == wincount+1:
                        sum+= HUMAN
                    if sum>= wincount-2:
                        score+= scores[sum]
                    elif sum>0: score+= sum
            #chéo phụ, người
            sum=0
            length = wincount
            if i -1>= tl[0] and j + wincount <= br[1] and state[i-1][j+wincount] == COMP:
                length+=1
            if ((i+ length  <= br[0] and j- length +wincount >= tl[1]) and state[i+length][j- length +wincount]==COMP)==False and i+ length -1<= br[0] and j- length+1 +wincount >= tl[1]:                
                ci =0
                for k in range(0, length):                
                    if state[i+k][j+wincount-k-1] == COMP:
                        ci=k
                        break
                    sum+= state[i+k][j+wincount-k-1]
                if ci==0:                 
                    if length == wincount+1:
                        sum+= COMP
                    if sum<= (wincount-2)*HUMAN:
                        score+= scores[sum]
                    elif sum<0: score+= sum
    return score



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
        score = -player* depth + -player * gridsize *gridsize * 10000
        return [-1, -1, score]
    #đến độ sâu tối đa cho phép thì dùng heuristic
    if rootdepth - depth >= maxmoves:               
        score = evaluate(state)
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
