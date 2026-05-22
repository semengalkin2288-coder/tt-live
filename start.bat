@echo off
title TT Live Analyzer
color 0A
echo.
echo  =========================================
echo   TT Live Analyzer - Запуск сервера
echo  =========================================
echo.
echo  Источник: Леон (лайв котировки + счёт)
echo  Адрес:     http://localhost:8080
echo.
echo  Браузер откроется автоматически...
echo  Для остановки нажми Ctrl+C
echo.
python server.py
if errorlevel 1 (
    echo.
    echo  [ОШИБКА] Python не найден или ошибка сервера.
    echo  Убедись что Python установлен: https://python.org
    pause
)