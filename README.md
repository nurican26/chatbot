[ATİLA.py](https://github.com/user-attachments/files/32559724/ATILA.py)
import os
import re
import html
import hashlib
import json
import time
import threading
import uuid
import xml.etree.ElementTree as ET
import concurrent.futures
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
import urllib.parse
import unicodedata

import pandas as pd
import requests
import streamlit as st
import streamlit.components.v1 as components
import yfinance as yf
from streamlit_autorefresh import st_autorefresh
from PIL import Image, ImageOps

try:
    import plotly.graph_objects as go
    _PLOTLY_VAR = True
except Exception:
    go = None
    _PLOTLY_VAR = False

try:
    from zoneinfo import ZoneInfo
    TURKIYE_TZ = ZoneInfo("Europe/Istanbul")
except Exception:
    # Sunucuda tzdata veritabanı yoksa (bazı minimal Linux
    # kurulumlarında olabilir), sabit UTC+3 ofsetine düşülür.
    # Türkiye 2016'dan beri yaz saati uygulamadığı için bu
    # sabit ofset her zaman doğrudur.
    TURKIYE_TZ = timezone(timedelta(hours=3))


def turkiye_saati():
    """
    Sunucunun çalıştığı saat dilimi ne olursa olsun
    (çoğu bulut sunucusu UTC kullanır), her zaman doğru
    Türkiye saatini (UTC+3) döndürür.
    """
    return datetime.now(TURKIYE_TZ)


# ==================================================
# SAYFA AYARLARI
# ==================================================
st.set_page_config(
    page_title="BTA Algoritmik İşlem",
    page_icon="📈",
    layout="wide",
    initial_sidebar_state="collapsed"
)


# ==================================================
# DOSYA AYARLARI
# ==================================================
ISTATISTIK_DOSYASI = "bta_oda_istatistik.csv"
MESAJ_DOSYASI = "bta_canli_mesajlar.csv"
NOT_DOSYASI = "bta_analiz_notlari.csv"

ISTATISTIK_SUTUNLARI = [
    "takip_sayisi"
]
TAKIP_DOSYASI = "bta_takipci.csv"
ENGEL_DOSYASI = "bta_engelli_kullanicilar.csv"
YONETICI_MESAJ_DOSYASI = "bta_yonetici_mesajlari.csv"

TAKIP_SUTUNLARI = ["oturum", "kullanici", "tarih"]
ENGEL_SUTUNLARI = ["oturum", "kullanici", "bitis", "tur"]
YONETICI_MESAJ_SUTUNLARI = [
    "mesaj_id",
    "tarih",
    "kullanici",
    "mesaj"
]

MESAJ_SUTUNLARI = [
    "mesaj_id",
    "tarih",
    "kullanici",
    "mesaj",
    "resim",
    "oturum"
]

NOT_SUTUNLARI = [
    "not_id",
    "tarih",
    "kullanici",
    "sembol",
    "not_metni",
    "resim"
]


def dosya_olustur(dosya, sutunlar):
    if not os.path.exists(dosya):
        pd.DataFrame(
            columns=sutunlar
        ).to_csv(
            dosya,
            index=False,
            encoding="utf-8-sig"
        )


dosya_olustur(ISTATISTIK_DOSYASI, ISTATISTIK_SUTUNLARI)
dosya_olustur(TAKIP_DOSYASI, ["oturum", "kullanici", "tarih"])
dosya_olustur(ENGEL_DOSYASI, [
    "oturum", "kullanici", "bitis", "tur"
])
dosya_olustur(YONETICI_MESAJ_DOSYASI, YONETICI_MESAJ_SUTUNLARI)
dosya_olustur(MESAJ_DOSYASI, MESAJ_SUTUNLARI)
dosya_olustur(NOT_DOSYASI, NOT_SUTUNLARI)


# ==================================================
# FORMATLAMA
# ==================================================
def tl_format(deger):
    try:
        return (
            f"{float(deger):,.2f}"
            .replace(",", "X")
            .replace(".", ",")
            .replace("X", ".")
            + " TL"
        )
    except Exception:
        return "-"


def fiyat_coz(metin):
    """
    Kullanıcının yazdığı fiyatı sayıya çevirir. Türkçe ve
    İngilizce biçimleri destekler:
      '2.955,00' -> 2955.0
      '2955,00'  -> 2955.0
      '2.955'    -> 2955.0
      '2955.00'  -> 2955.0
      '2955'     -> 2955.0
    """
    _m = str(metin).strip()
    _m = _m.replace("TL", "").replace("tl", "").replace("₺", "")
    _m = _m.replace(" ", "").replace("\u00a0", "").replace("_", "")

    if not _m:
        raise ValueError("Boş fiyat")

    if "," in _m and "." in _m:
        if _m.rfind(",") > _m.rfind("."):
            _m = _m.replace(".", "").replace(",", ".")
        else:
            _m = _m.replace(",", "")
    elif "," in _m:
        _m = _m.replace(",", ".")
    elif "." in _m:
        _parca = _m.split(".")

        if len(_parca) > 2:
            _m = _m.replace(".", "")
        elif len(_parca[1]) == 3 and _parca[0].isdigit():
            _m = _m.replace(".", "")

    return float(_m)


def sayi_format(deger):
    try:
        return (
            f"{float(deger):,.2f}"
            .replace(",", "X")
            .replace(".", ",")
            .replace("X", ".")
        )
    except Exception:
        return "-"


def turkce_sayi_cevir(deger):
    if pd.isna(deger):
        return None

    if isinstance(deger, (int, float)):
        return float(deger)

    metin = str(deger).strip()
    metin = metin.replace("TL", "")
    metin = metin.replace("tl", "")
    metin = metin.replace(" ", "")

    if not metin:
        return None

    try:
        if "." in metin and "," in metin:
            metin = metin.replace(".", "")
            metin = metin.replace(",", ".")

        elif "," in metin:
            son_parca = metin.split(",")[-1]

            if len(son_parca) == 3:
                metin = metin.replace(",", "")
            else:
                metin = metin.replace(",", ".")

        elif "." in metin:
            son_parca = metin.split(".")[-1]

            if len(son_parca) == 3:
                metin = metin.replace(".", "")

        return float(metin)

    except Exception:
        return None


# ==================================================
# KAR YÜZDESI HESAPLA
# ==================================================
def kar_yuzdesi_hesapla(bta_fiyat, anlık_fiyat):
    if bta_fiyat <= 0 or pd.isna(bta_fiyat) or pd.isna(anlık_fiyat):
        return None
    
    kar = ((anlık_fiyat - bta_fiyat) / bta_fiyat) * 100
    return kar


# ==================================================
# KAR YÜZDESI FORMATLAMA
# ==================================================
def kar_yuzdesi_format(kar_yuzde):
    if kar_yuzde is None:
        return "-"
    
    durum = "📈" if kar_yuzde >= 0 else "📉"
    renk = "#00f5c8" if kar_yuzde >= 0 else "#ff5264"
    
    return f"""
    <div style="
        background: rgba(0, 0, 0, 0.3);
        border-left: 4px solid {renk};
        border-radius: 5px;
        padding: 12px;
        margin: 10px 0;
        text-align: center;
    ">
        <div style="font-size: 24px; font-weight: bold; color: {renk};">
            {durum} {kar_yuzde:+.2f}%
        </div>
        <div style="font-size: 12px; color: #999;">
            {'💰 Kar' if kar_yuzde >= 0 else '📊 Zarar'}
        </div>
    </div>
    """


# ==================================================
# BEDELLİ / BEDELSİZ HESAPLAMA
# ==================================================
def bedelli_bedelsiz_hesapla(
    eski_fiyat,
    sahip_lot,
    bedelli_orani,
    bedelli_fiyat,
    bedelsiz_orani
):
    """
    BIST sermaye artırımı (bedelli/bedelsiz) hesaplama makinesi.
    Oranlar yüzde (%) cinsinden girilir (örn. %50 bedelsiz için 50).
    Teorik (düzeltilmiş) fiyat, BIST'in resmi sermaye artırımı
    fiyat düzeltme formülüne göre hesaplanır:

        Teorik Fiyat =
            (Eski Fiyat + (Bedelli Oranı x Bedelli Fiyatı))
            / (1 + Bedelli Oranı + Bedelsiz Oranı)
    """
    try:
        eski_fiyat = float(eski_fiyat)
        sahip_lot = float(sahip_lot)
        bedelli_orani_yuzde = float(bedelli_orani)
        bedelli_fiyat = float(bedelli_fiyat)
        bedelsiz_orani_yuzde = float(bedelsiz_orani)
    except Exception:
        return None

    if eski_fiyat <= 0 or sahip_lot < 0:
        return None

    if bedelli_orani_yuzde < 0 or bedelsiz_orani_yuzde < 0:
        return None

    bedelli_orani = bedelli_orani_yuzde / 100
    bedelsiz_orani = bedelsiz_orani_yuzde / 100

    payda = 1 + bedelli_orani + bedelsiz_orani

    if payda <= 0:
        return None

    # Yeni pay (lot) sayıları - mevcut sahiplik üzerinden
    bedelli_yeni_lot = sahip_lot * bedelli_orani
    bedelsiz_yeni_lot = sahip_lot * bedelsiz_orani
    toplam_yeni_lot = bedelli_yeni_lot + bedelsiz_yeni_lot
    toplam_lot_sonrasi = sahip_lot + toplam_yeni_lot

    # Bedelli hakkının kullanılması için ödenecek tutar
    odenecek_tutar = bedelli_yeni_lot * bedelli_fiyat

    # Teorik (düzeltilmiş) fiyat
    teorik_fiyat = (
        eski_fiyat + (bedelli_orani * bedelli_fiyat)
    ) / payda

    # Portföy değerleri (bedelli tutarı yatırılmış varsayımıyla)
    eski_portfoy_degeri = sahip_lot * eski_fiyat
    yeni_portfoy_degeri = toplam_lot_sonrasi * teorik_fiyat

    fiyat_degisim_yuzde = (
        ((teorik_fiyat - eski_fiyat) / eski_fiyat) * 100
    )

    return {
        "eski_fiyat": eski_fiyat,
        "sahip_lot": sahip_lot,
        "bedelli_yeni_lot": bedelli_yeni_lot,
        "bedelsiz_yeni_lot": bedelsiz_yeni_lot,
        "toplam_yeni_lot": toplam_yeni_lot,
        "toplam_lot_sonrasi": toplam_lot_sonrasi,
        "odenecek_tutar": odenecek_tutar,
        "teorik_fiyat": teorik_fiyat,
        "eski_portfoy_degeri": eski_portfoy_degeri,
        "yeni_portfoy_degeri": yeni_portfoy_degeri,
        "fiyat_degisim_yuzde": fiyat_degisim_yuzde
    }


def bedelli_bedelsiz_kart_format(sonuc):
    if sonuc is None:
        return "-"

    durum = "📉" if sonuc["fiyat_degisim_yuzde"] < 0 else "📈"
    renk = (
        "#ff5264"
        if sonuc["fiyat_degisim_yuzde"] < 0
        else "#00f5c8"
    )

    return f"""
    <div style="
        background: rgba(0, 0, 0, 0.3);
        border-left: 4px solid {renk};
        border-radius: 5px;
        padding: 12px;
        margin: 10px 0;
        text-align: center;
    ">
        <div style="font-size: 13px; color: #999;">
            Teorik (Düzeltilmiş) Fiyat
        </div>
        <div style="font-size: 26px; font-weight: bold; color: {renk};">
            {tl_format(sonuc["teorik_fiyat"])}
        </div>
        <div style="font-size: 13px; color: {renk};">
            {durum} {sonuc["fiyat_degisim_yuzde"]:+.2f}%
        </div>
    </div>
    """


# ==================================================
# TEK SEMBOL İÇİN FİYAT + DEĞİŞİM
# ==================================================
@st.cache_data(ttl=30, show_spinner=False)
def fiyat_degisim_getir(sembol, marj_kontrolu=True):
    """
    Tek bir sembol için son fiyatı ve önceki kapanışa göre değişim
    yüzdesini döndürür.

    Öncelik sırası:
      1) fast_info -> last_price / previous_close
         (borsanın resmi "önceki kapanış" değeri; sermaye artırımı ve
          temettü düzeltmelerini doğru yansıtır)
      2) history() -> son iki kapanış (yedek yöntem)

    marj_kontrolu=True iken BIST'in günlük ±%10 fiyat marjı gözetilir;
    bunun dışında kalan değerler (ör. bedelsiz/temettü kaynaklı veri
    kopukluğu) hatalı kabul edilip elenir. Endeks, döviz ve emtia için
    bu kontrol kapatılmalıdır.

    Hata durumunda (None, None, hata_metni) döner.
    """
    # BIST günlük fiyat marjı %10'dur; veri gürültüsüne
    # küçük bir tolerans bırakılır.
    MARJ_SINIRI = 11.0

    son = None
    onceki = None

    try:
        # ----- 0. YÖNTEM: BIST resmî gecikmeli veri (İş Yatırım) -----
        _temiz = _bist_sembol_mu(sembol)
        if _temiz:
            try:
                _k = _bist_kot(_temiz)
                _s2 = float(_k["fiyat"])
                _p2 = float(_k["onceki_kapanis"])
                if _s2 and _p2 and _p2 > 0:
                    _d2 = ((_s2 - _p2) / _p2) * 100
                    if not (marj_kontrolu and abs(_d2) > MARJ_SINIRI):
                        return _s2, _d2, None
            except Exception:
                pass

        hisse = yf.Ticker(sembol)

        # ----- 1. YÖNTEM: fast_info -----
        try:
            hizli = hisse.fast_info

            aday_son = getattr(hizli, "last_price", None)
            aday_onceki = getattr(hizli, "previous_close", None)

            if aday_son is None and hasattr(hizli, "get"):
                aday_son = hizli.get("last_price")
            if aday_onceki is None and hasattr(hizli, "get"):
                aday_onceki = hizli.get("previous_close")

            if aday_son and aday_onceki:
                son = float(aday_son)
                onceki = float(aday_onceki)

        except Exception:
            son = None
            onceki = None

        # ----- 2. YÖNTEM (YEDEK): history -----
        if son is None or onceki is None or onceki <= 0:
            gecmis = hisse.history(
                period="5d",
                interval="1d",
                auto_adjust=False
            )

            if (
                gecmis is None
                or gecmis.empty
                or "Close" not in gecmis.columns
            ):
                return None, None, "veri boş döndü"

            kapanislar = gecmis["Close"]

            if pd.isna(kapanislar.iloc[-1]):
                return (
                    None,
                    None,
                    "bugünkü kapanış kaydı henüz yok (anlık veri için fast_info gerekli)"
                )

            kapanislar = kapanislar.dropna()

            if len(kapanislar) < 2:
                return None, None, "yetersiz geçmiş veri"

            onceki = float(kapanislar.iloc[-2])
            son = float(kapanislar.iloc[-1])

        if (
            onceki is None
            or son is None
            or onceki <= 0
            or pd.isna(onceki)
            or pd.isna(son)
        ):
            return None, None, "geçersiz fiyat"

        degisim = ((son - onceki) / onceki) * 100

        if marj_kontrolu and abs(degisim) > MARJ_SINIRI:
            return (
                None,
                None,
                f"marj dışı değişim (%{degisim:.2f}) - "
                "muhtemelen bedelsiz/temettü kaynaklı veri kopukluğu"
            )

        return son, degisim, None

    except Exception as hata:
        return None, None, str(hata)


# ==================================================
# ==================================================
# BIST RESMÎ GECİKMELİ VERİ (İŞ YATIRIM KAMU API)
# ~15 dk gecikmeli. Uçlar: OneEndeks (anlık) / HisseTekil (günlük)
# ==================================================
_BIST_UA = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                   "AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/120.0 Safari/537.36")
}

_BIST_PERIYOT_GUN = {
    "1d": 3, "5d": 10, "1mo": 40, "3mo": 95, "6mo": 185, "ytd": 220,
    "1y": 370, "2y": 740, "5y": 1850, "10y": 3700, "max": 7300,
}


@st.cache_data(ttl=120, show_spinner=False)
def _bist_kot(sembol):
    temiz = str(sembol).strip().upper()
    url = ("https://www.isyatirim.com.tr/_Layouts/15/"
           "IsYatirim.Website/Common/Data.aspx/OneEndeks?endeks=" + temiz)
    r = requests.get(url, headers=_BIST_UA, timeout=10)
    r.raise_for_status()
    satir = r.json()[0]
    return {
        "fiyat": float(satir["last"]),
        "onceki_kapanis": float(satir["dayClose"]),
        "zaman": satir.get("updateDate", ""),
    }


@st.cache_data(ttl=300, show_spinner=False)
def _bist_gecmis(sembol, gun=400):
    temiz = str(sembol).strip().upper()
    bitis = datetime.now()
    basla = bitis - timedelta(days=gun)
    url = ("https://www.isyatirim.com.tr/_Layouts/15/"
           "IsYatirim.Website/Common/Data.aspx/HisseTekil?hisse=" +
           temiz + "&startdate=" + basla.strftime("%d-%m-%Y") +
           "&enddate=" + bitis.strftime("%d-%m-%Y"))
    r = requests.get(url, headers=_BIST_UA, timeout=15)
    r.raise_for_status()
    kayit = r.json().get("value")
    if not kayit:
        raise ValueError("BIST gecmis veri bos: " + temiz)
    veri = pd.DataFrame(kayit)[
        ["HGDG_TARIH", "HGDG_AOF", "HGDG_MAX", "HGDG_MIN",
         "HGDG_KAPANIS", "HGDG_HACIM"]
    ]
    veri["HGDG_TARIH"] = pd.to_datetime(
        veri["HGDG_TARIH"], format="%d-%m-%Y"
    )
    veri = veri.rename(columns={
        "HGDG_TARIH": "Date", "HGDG_AOF": "Open", "HGDG_MAX": "High",
        "HGDG_MIN": "Low", "HGDG_KAPANIS": "Close", "HGDG_HACIM": "Volume"
    })
    for kol in ["Open", "High", "Low", "Close", "Volume"]:
        veri[kol] = pd.to_numeric(veri[kol], errors="coerce")
    veri = (
        veri.set_index("Date").sort_index()
        .dropna(subset=["Open", "High", "Low", "Close"])
    )
    if veri.empty:
        raise ValueError("BIST gecmis veri bos: " + temiz)
    return veri


def _bist_sembol_mu(sembol):
    temiz = str(sembol or "").strip().upper().replace(".IS", "")
    if not temiz:
        return None
    if (":" in temiz or "=" in temiz or "/" in temiz
            or temiz.endswith("-USD") or temiz.endswith("-TRY")):
        return None
    if not re.fullmatch(r"[A-Z0-9]{2,5}", temiz):
        return None
    return temiz


# ==================================================
# TAVAN KUTLAMA KARTI
# ==================================================
# ==================================================
# HİSSE FİYAT KARTI (GENEL AMAÇLI)
# ==================================================
def hisse_karti_format(
    hisse_kodu, fiyat, degisim, renk, sira=0, rozet_html=""
):
    durum = "▲" if degisim >= 0 else "▼"

    # Sade ve düzenli görünüm: arka plan yok, sadece alt çizgi.
    # Sabit sütun genişlikleri sayesinde fiyat ve yüzde her satırda
    # aynı hizada durur (sağa sola kaymaz); sütunlar arası boşluk
    # sabit ve ferah tutulur.

    return f"""
    <div class="bta-alsat-kart" style="
        border-bottom: 1px solid rgba(255, 255, 255, 0.28);
        padding: 12px 2px;
        margin: 0;
        display: grid;
        grid-template-columns: 116px 150px 112px auto;
        column-gap: 18px;
        align-items: center;
        justify-content: start;
    ">
        <span class="bta-kart-isim" style="
            font-size: 19px;
            font-weight: 700;
            letter-spacing: 0.5px;
            color: {renk};
            white-space: nowrap;
            overflow: hidden;
        ">{hisse_kodu}</span>
        <span class="bta-kart-fiyat" style="
            font-size: 24px;
            font-weight: 600;
            color: #ffffff;
            white-space: nowrap;
            text-align: right;
        ">{tl_format(fiyat)}</span>
        <span class="bta-kart-deg" style="
            font-size: 19px;
            font-weight: 700;
            color: {renk};
            white-space: nowrap;
            text-align: right;
        ">{durum} {degisim:+.2f}%</span>
        <span class="bta-kart-rozet" style="margin-left: 8px;">{rozet_html}</span>
    </div>
    """


def sekme_baslik_format(logo, baslik, renk):
    return f"""
    <div class="sekme-baslik" style="border-left-color: {renk};">
        <span style="color: {renk};">{baslik}</span>
    </div>
    """


def tavan_kutlama_format(hisse_kodu, fiyat, degisim):
    return f"""
    <div style="
        background: linear-gradient(
            120deg,
            rgba(0, 245, 200, 0.22),
            rgba(22, 140, 255, 0.22)
        );
        border: 2px solid #00f5c8;
        border-radius: 12px;
        padding: 16px 20px;
        margin: 10px 0;
        text-align: center;
        box-shadow: 0 0 22px rgba(0, 245, 200, 0.45);
        animation: tavan_parlama 1.6s ease-in-out infinite alternate;
    ">
        <div style="font-size: 26px;">
            🎉 🚀 🥳
        </div>
        <div style="
            font-size: 21px;
            font-weight: 800;
            color: #00f5c8;
            margin-top: 4px;
        ">
            Tebrikler! {hisse_kodu} bugün TAVAN yaptı!
        </div>
        <div style="font-size: 15px; color: #d8fff5; margin-top: 4px;">
            {tl_format(fiyat)} &nbsp;•&nbsp; {degisim:+.2f}%
        </div>
    </div>
    <style>
        @keyframes tavan_parlama {{
            from {{
                box-shadow: 0 0 14px rgba(0, 245, 200, 0.35);
            }}
            to {{
                box-shadow: 0 0 30px rgba(0, 245, 200, 0.75);
            }}
        }}
    </style>
    """


# ==================================================
# PİYASA ÖZETİ (BIST100 / USDTRY / EURTRY / GRAM ALTIN)
# ==================================================
@st.cache_data(ttl=30, show_spinner=False)
def piyasa_ozeti_getir():
    """
    Ana endeks, döviz ve altın kartları için veri toplar.
    Gram Altın (TL), ons altın (USD) fiyatının USDTRY ile çarpılıp
    31.1035 gramlık ons ağırlığına bölünmesiyle yaklaşık hesaplanır.
    """
    sonuclar = []

    bist_son, bist_degisim, bist_hata = fiyat_degisim_getir(
        "XU100.IS",
        marj_kontrolu=False
    )
    sonuclar.append(
        {
            "isim": "BIST100",
            "fiyat": bist_son,
            "degisim": bist_degisim,
            "tur": "sayi",
            "hata": bist_hata
        }
    )

    usd_son, usd_degisim, usd_hata = fiyat_degisim_getir(
        "USDTRY=X",
        marj_kontrolu=False
    )
    sonuclar.append(
        {
            "isim": "USDTRY",
            "fiyat": usd_son,
            "degisim": usd_degisim,
            "tur": "sayi",
            "hata": usd_hata
        }
    )

    eur_son, eur_degisim, eur_hata = fiyat_degisim_getir(
        "EURTRY=X",
        marj_kontrolu=False
    )
    sonuclar.append(
        {
            "isim": "EURTRY",
            "fiyat": eur_son,
            "degisim": eur_degisim,
            "tur": "sayi",
            "hata": eur_hata
        }
    )

    ons_son, ons_degisim, ons_hata = fiyat_degisim_getir(
        "GC=F",
        marj_kontrolu=False
    )

    if ons_son is not None and usd_son is not None:
        gram_fiyat = (ons_son / 31.1035) * usd_son
        gram_degisim = ons_degisim
        gram_hata = None
    else:
        gram_fiyat = None
        gram_degisim = None
        gram_hata = ons_hata or usd_hata or "veri alınamadı"

    sonuclar.append(
        {
            "isim": "GRAM ALTIN (yakl.)",
            "fiyat": gram_fiyat,
            "degisim": gram_degisim,
            "tur": "tl",
            "hata": gram_hata
        }
    )

    # 22 ayar madeni altınlar: gram altının 1.754 / 3.508 / 7.016
    # gramlık ağırlıkları ile yaklaşık hesaplanır. Gerçek kuyumcu
    # fiyatı işçilik ve alış-satış makası nedeniyle farklı olabilir;
    # bu nedenle kartta "yakl." etiketi gösterilir.
    madeni_altinlar = [
        ("ÇEYREK ALTIN (yakl.)", 1.754),
        ("YARIM ALTIN (yakl.)", 3.508),
        ("TAM ALTIN (yakl.)", 7.016),
    ]

    for _isim, _carpan in madeni_altinlar:
        if gram_fiyat is not None:
            _madeni_fiyat = gram_fiyat * _carpan
            _madeni_hata = None
        else:
            _madeni_fiyat = None
            _madeni_hata = gram_hata

        sonuclar.append(
            {
                "isim": _isim,
                "fiyat": _madeni_fiyat,
                "degisim": gram_degisim,
                "tur": "tl",
                "hata": _madeni_hata
            }
        )

    # Veri gerçekten bu an çekildiği için zaman damgası da
    # burada, önbelleklenen sonucun içinde üretilir. Böylece
    # ekranda gösterilen saat, sayfanın yenilenme anını değil,
    # verinin GERÇEKTEN çekildiği anı yansıtır.
    cekim_zamani = turkiye_saati().strftime("%d.%m.%Y %H:%M:%S")

    return sonuclar, cekim_zamani


# ==================================================
# SON DAKİKA HABERLERİ (GOOGLE NEWS RSS)
# ==================================================
@st.cache_data(ttl=600, show_spinner=False)
def son_dakika_haberleri_getir():
    """
    Google News'ten SADECE genel/ekonomi ağırlıklı akış değil,
    birden fazla kategoriden (yurt, dünya, spor, magazin, sağlık)
    haber çekip karıştırır. Böylece bir TV ana haber bülteni gibi
    çeşitli konular yer alır, tek bir konu (ör. ekonomi) baskın
    olmaz. Yalnızca son 48 saatte yayınlananlar listelenir.
    """
    _kategori_url_listesi = [
        "https://news.google.com/rss?hl=tr&gl=TR&ceid=TR:tr",
        "https://news.google.com/rss/headlines/section/topic/"
        "NATION?hl=tr&gl=TR&ceid=TR:tr",
        "https://news.google.com/rss/headlines/section/topic/"
        "WORLD?hl=tr&gl=TR&ceid=TR:tr",
        "https://news.google.com/rss/headlines/section/topic/"
        "SPORTS?hl=tr&gl=TR&ceid=TR:tr",
        "https://news.google.com/rss/headlines/section/topic/"
        "ENTERTAINMENT?hl=tr&gl=TR&ceid=TR:tr",
        "https://news.google.com/rss/headlines/section/topic/"
        "HEALTH?hl=tr&gl=TR&ceid=TR:tr",
    ]

    def _tek_kategori_getir(_url):
        try:
            _yanit = requests.get(
                _url,
                timeout=12,
                headers={
                    "User-Agent": (
                        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                        "AppleWebKit/537.36"
                    )
                }
            )
            _kok = ET.fromstring(_yanit.content)
            return _kok.findall(".//item")
        except Exception:
            return []

    try:
        _tum_ogeler = []

        with concurrent.futures.ThreadPoolExecutor(
            max_workers=len(_kategori_url_listesi)
        ) as _havuz:
            for _ogeler in _havuz.map(
                _tek_kategori_getir, _kategori_url_listesi
            ):
                _tum_ogeler.extend(_ogeler)

        simdi = turkiye_saati()
        sinir_zaman = simdi - timedelta(hours=48)

        _gecici = []
        _gorulen_basliklar = set()

        for oge in _tum_ogeler:
            baslik = (oge.findtext("title") or "").strip()
            link = (oge.findtext("link") or "").strip()
            yayin = (oge.findtext("pubDate") or "").strip()

            if not baslik:
                continue

            _anahtar = baslik.strip().lower()
            if _anahtar in _gorulen_basliklar:
                continue

            try:
                yayin_zamani = parsedate_to_datetime(
                    yayin
                ).astimezone(TURKIYE_TZ)
            except Exception:
                continue

            # Sadece son 48 saatte yayınlanan haberler
            if yayin_zamani < sinir_zaman:
                continue

            _gorulen_basliklar.add(_anahtar)
            _gecici.append((baslik, link, yayin_zamani))

        # En yeniden en eskiye doğru karışık (kategoriler arası) sırala
        _gecici.sort(key=lambda _oge: _oge[2], reverse=True)

        haberler = [
            (
                html.escape(_b),
                html.escape(_l),
                html.escape(_z.strftime("%H:%M"))
            )
            for _b, _l, _z in _gecici[:20]
        ]

        return haberler

    except Exception:
        return []


# ==================================================
# GÜNCEL ARZ (HALKA ARZ) HABERLERİ - GOOGLE NEWS ARAMA
# ==================================================
@st.cache_data(ttl=600, show_spinner=False)
def arz_haberleri_getir():
    """
    Google News'te 'halka arz' konulu son haberleri getirir.
    Yalnızca son 48 saatte yayınlananlar listelenir; eski haberler atlanır.
    """
    try:
        # Google News Türkiye "halka arz" arama akışı
        sorgu = urllib.parse.quote_plus(
            '"halka arz" OR "halka arzda" OR "halka arza"'
        )

        url = (
            "https://news.google.com/rss/search?q="
            f"{sorgu}&hl=tr&gl=TR&ceid=TR:tr"
        )

        yanit = requests.get(
            url,
            timeout=12,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36"
                )
            }
        )

        kok = ET.fromstring(yanit.content)
        ogeler = kok.findall(".//item")

        simdi = turkiye_saati()
        sinir_zaman = simdi - timedelta(hours=48)

        haberler = []

        for oge in ogeler:
            baslik = (oge.findtext("title") or "").strip()
            link = (oge.findtext("link") or "").strip()
            yayin = (oge.findtext("pubDate") or "").strip()
            kaynak = (oge.findtext("source") or "").strip()

            if not baslik:
                continue

            try:
                yayin_zamani = parsedate_to_datetime(
                    yayin
                ).astimezone(TURKIYE_TZ)
            except Exception:
                continue

            # Sadece son 48 saatte yayınlanan haberler
            if yayin_zamani < sinir_zaman:
                continue

            zaman = yayin_zamani.strftime("%H:%M")

            haberler.append(
                (
                    html.escape(baslik),
                    html.escape(link),
                    html.escape(zaman),
                    html.escape(kaynak)
                )
            )

            if len(haberler) >= 20:
                break

        return haberler

    except Exception:
        return []


# ==================================================
# BEDELLİ / BEDELSİZ SERMAYE ARTIRIMI HABERLERİ
# ==================================================
@st.cache_data(ttl=600, show_spinner=False)
def bedelli_bedelsiz_haberleri_getir():
    """
    Google News'te 'bedelli' ve 'bedelsiz' sermaye artırımı
    konulu haberleri AYRI AYRI arayıp tek listede birleştirir.
    Böylece her iki tür haber de garantili olarak gelir.
    """
    sorgular = [
        '"bedelli sermaye artırımı" OR "bedelli artırım" '
        'OR "rüçhan hakkı" OR "bedelli hisse"',
        '"bedelsiz sermaye artırımı" OR "bedelsiz hisse" '
        'OR "bedelsiz artırım"'
    ]

    haberler = []
    gorulen = set()

    for sorgu_ham in sorgular:
        sorgu = urllib.parse.quote_plus(sorgu_ham)

        try:
            url = (
                "https://news.google.com/rss/search?q="
                f"{sorgu}&hl=tr&gl=TR&ceid=TR:tr"
            )

            yanit = requests.get(
                url,
                timeout=12,
                headers={
                    "User-Agent": (
                        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                        "AppleWebKit/537.36"
                    )
                }
            )

            kok = ET.fromstring(yanit.content)
            ogeler = kok.findall(".//item")

            simdi = turkiye_saati()
            sinir_zaman = simdi - timedelta(hours=48)

            for oge in ogeler:
                baslik = (oge.findtext("title") or "").strip()
                link = (oge.findtext("link") or "").strip()
                yayin = (oge.findtext("pubDate") or "").strip()
                kaynak = (oge.findtext("source") or "").strip()

                if not baslik:
                    continue

                try:
                    yayin_zamani = parsedate_to_datetime(
                        yayin
                    ).astimezone(TURKIYE_TZ)
                except Exception:
                    continue

                if yayin_zamani < sinir_zaman:
                    continue

                zaman = yayin_zamani.strftime("%H:%M")

                if link in gorulen:
                    continue

                gorulen.add(link)

                haberler.append(
                    (
                        html.escape(baslik),
                        html.escape(link),
                        html.escape(zaman),
                        html.escape(kaynak)
                    )
                )

                if len(haberler) >= 30:
                    break

        except Exception:
            continue

    return haberler[:30]


# ==================================================
# KAP HABERLERİ - GOOGLE NEWS ARAMA
# ==================================================
@st.cache_data(ttl=600, show_spinner=False)
def kap_haberleri_getir(hisse_kodu=""):
    """
    Google News'te 'KAP (Kamuyu Aydınlatma Platformu)' konulu son
    haberleri getirir. Yalnızca son 48 saatte yayınlananlar listelenir.
    hisse_kodu verilirse yalnızca o hisseyle ilgili KAP haberleri döner.
    """
    hisse_kodu = hisse_kodu.strip().upper()

    if hisse_kodu:
        sorgu = urllib.parse.quote_plus(
            f'"{hisse_kodu}" ("KAP" OR "Kamuyu Aydınlatma" '
            'OR "özel durum açıklaması")'
        )
    else:
        sorgu = urllib.parse.quote_plus(
            '"KAP" OR "Kamuyu Aydınlatma Platformu" '
            'OR "KAP bildirim" OR "özel durum açıklaması"'
        )

    try:
        url = (
            "https://news.google.com/rss/search?q="
            f"{sorgu}&hl=tr&gl=TR&ceid=TR:tr"
        )

        yanit = requests.get(
            url,
            timeout=12,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36"
                )
            }
        )

        kok = ET.fromstring(yanit.content)
        ogeler = kok.findall(".//item")

        simdi = turkiye_saati()
        sinir_zaman = simdi - timedelta(hours=48)

        haberler = []

        for oge in ogeler:
            baslik = (oge.findtext("title") or "").strip()
            link = (oge.findtext("link") or "").strip()
            yayin = (oge.findtext("pubDate") or "").strip()
            kaynak = (oge.findtext("source") or "").strip()

            if not baslik:
                continue

            try:
                yayin_zamani = parsedate_to_datetime(
                    yayin
                ).astimezone(TURKIYE_TZ)
            except Exception:
                continue

            if yayin_zamani < sinir_zaman:
                continue

            zaman = yayin_zamani.strftime("%H:%M")

            haberler.append(
                (
                    html.escape(baslik),
                    html.escape(link),
                    html.escape(zaman),
                    html.escape(kaynak)
                )
            )

            if len(haberler) >= 20:
                break

        return haberler

    except Exception:
        return []


# ==================================================
# SPK HABERLERİ - GOOGLE NEWS ARAMA
# ==================================================
@st.cache_data(ttl=600, show_spinner=False)
def spk_haberleri_getir(hisse_kodu=""):
    """
    Google News'te 'SPK (Sermaye Piyasası Kurulu)' konulu son
    haberleri getirir. Yalnızca son 48 saatte yayınlananlar listelenir.
    hisse_kodu verilirse yalnızca o hisseyle ilgili SPK haberleri döner.
    """
    hisse_kodu = hisse_kodu.strip().upper()

    if hisse_kodu:
        sorgu = urllib.parse.quote_plus(
            f'"{hisse_kodu}" ("SPK" OR "Sermaye Piyasası Kurulu")'
        )
    else:
        sorgu = urllib.parse.quote_plus(
            '"SPK" OR "Sermaye Piyasası Kurulu" OR "SPK açıklama"'
        )

    try:
        url = (
            "https://news.google.com/rss/search?q="
            f"{sorgu}&hl=tr&gl=TR&ceid=TR:tr"
        )

        yanit = requests.get(
            url,
            timeout=12,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36"
                )
            }
        )

        kok = ET.fromstring(yanit.content)
        ogeler = kok.findall(".//item")

        simdi = turkiye_saati()
        sinir_zaman = simdi - timedelta(hours=48)

        haberler = []

        for oge in ogeler:
            baslik = (oge.findtext("title") or "").strip()
            link = (oge.findtext("link") or "").strip()
            yayin = (oge.findtext("pubDate") or "").strip()
            kaynak = (oge.findtext("source") or "").strip()

            if not baslik:
                continue

            try:
                yayin_zamani = parsedate_to_datetime(
                    yayin
                ).astimezone(TURKIYE_TZ)
            except Exception:
                continue

            if yayin_zamani < sinir_zaman:
                continue

            zaman = yayin_zamani.strftime("%H:%M")

            haberler.append(
                (
                    html.escape(baslik),
                    html.escape(link),
                    html.escape(zaman),
                    html.escape(kaynak)
                )
            )

            if len(haberler) >= 20:
                break

        return haberler

    except Exception:
        return []


# ==================================================
# ALGORİTMA LİSTESİ - KAP / SPK HABER ROZETİ
# ==================================================
# Algoritma listesindeki her hissenin yanında, son 48 saatte o hisseyle
# ilgili KAP/SPK haberi varsa küçük bir "📰 KAP 14:32" rozeti gösterilir
# (dokununca haber açılır).
#
# Haberler ARKA PLAN iş parçacığında çekilir; böylece 5 sn'de bir yenilenen
# canlı fiyat listesi haber beklerken donmaz. Sonuçlar tüm ziyaretçiler
# için ortak tutulur (10 dk), yani Google News'e tek seferde az istek gider.
# ==================================================
_HABER_ROZET_SURESI_SN = 600
_HABER_ROZET_SAAT = 48


def _haber_turu(baslik):
    """Başlığa bakarak KAP / SPK / Haber etiketi üretir."""
    b = baslik.upper()

    _kap = (
        re.search(r"\bKAP\b", b) is not None
        or "KAMUYU AYDINLATMA" in b
        or "ÖZEL DURUM" in b
    )
    _spk = (
        re.search(r"\bSPK\b", b) is not None
        or "SERMAYE PIYASASI" in b
        or "SERMAYE PİYASASI" in b
    )

    if _kap:
        return "KAP"
    if _spk:
        return "SPK"
    return "Haber"


def _hisse_haber_cek(hisse_kodu):
    """
    Tek bir hisse için son 48 saatteki KAP/SPK haberlerini döndürür
    (en yeni başta). Hata olursa None döner (önceki veri korunsun diye).
    Başlığında hisse kodu tam kelime olarak geçmeyen sonuçlar elenir;
    böylece kodla ilgisiz haberler yanlış rozet üretmez.
    """
    kod = str(hisse_kodu).strip().upper().replace(".IS", "")

    if not kod:
        return []

    sorgu = urllib.parse.quote_plus(
        f'"{kod}" ("KAP" OR "Kamuyu Aydınlatma" '
        'OR "özel durum açıklaması" OR "SPK" '
        'OR "Sermaye Piyasası Kurulu")'
    )

    try:
        yanit = requests.get(
            "https://news.google.com/rss/search?q="
            f"{sorgu}&hl=tr&gl=TR&ceid=TR:tr",
            timeout=12,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36"
                )
            }
        )
        kok = ET.fromstring(yanit.content)
    except Exception:
        return None

    kod_deseni = re.compile(
        r"(?<![A-Z0-9ÇĞİÖŞÜ])" + re.escape(kod) + r"(?![A-Z0-9ÇĞİÖŞÜ])"
    )
    sinir = turkiye_saati() - timedelta(hours=_HABER_ROZET_SAAT)

    haberler = []
    gorulen = set()

    for oge in kok.findall(".//item"):
        baslik = (oge.findtext("title") or "").strip()
        link = (oge.findtext("link") or "").strip()

        if not baslik or baslik in gorulen:
            continue

        if not kod_deseni.search(baslik):
            continue

        try:
            zaman = parsedate_to_datetime(
                (oge.findtext("pubDate") or "").strip()
            ).astimezone(TURKIYE_TZ)
        except Exception:
            continue

        if zaman < sinir:
            continue

        gorulen.add(baslik)
        haberler.append(
            {
                "baslik": baslik,
                "link": link,
                "tur": _haber_turu(baslik),
                "zaman": zaman,
            }
        )

    haberler.sort(key=lambda _h: _h["zaman"], reverse=True)
    return haberler[:5]


@st.cache_resource(show_spinner=False)
def _haber_rozet_deposu():
    # Tüm oturumlar bu tek sözlüğü paylaşır.
    return {
        "veri": {},
        "kodlar": set(),
        "zaman": 0.0,
        "calisiyor": False,
        "kilit": threading.Lock(),
    }


def haber_rozetlerini_getir(hisse_kodlari):
    """
    {hisse_kodu: [haber, ...]} sözlüğünü ANINDA döndürür (bekletmez).
    Veri eskiyse ya da listeye yeni hisse geldiyse arka planda
    yenileme başlatır; sonuç bir sonraki 5 sn'lik yenilemede görünür.
    """
    kodlar = {
        str(_k).strip().upper().replace(".IS", "")
        for _k in hisse_kodlari
        if str(_k).strip()
    }
    depo = _haber_rozet_deposu()

    with depo["kilit"]:
        taze = (
            time.time() - depo["zaman"] < _HABER_ROZET_SURESI_SN
            and kodlar <= depo["kodlar"]
        )

        if depo["calisiyor"] or taze or not kodlar:
            return dict(depo["veri"])

        depo["calisiyor"] = True
        onceki = dict(depo["veri"])

    def _isle():
        try:
            yeni = {}
            sirali = sorted(kodlar)

            with concurrent.futures.ThreadPoolExecutor(
                max_workers=6
            ) as havuz:
                for _kod, _haber in zip(
                    sirali, havuz.map(_hisse_haber_cek, sirali)
                ):
                    # Hata (None) olduysa eski veri korunur.
                    yeni[_kod] = (
                        _haber if _haber is not None
                        else onceki.get(_kod, [])
                    )

            with depo["kilit"]:
                depo["veri"] = yeni
                depo["kodlar"] = kodlar
                depo["zaman"] = time.time()
        except Exception:
            pass
        finally:
            with depo["kilit"]:
                depo["calisiyor"] = False

    threading.Thread(target=_isle, daemon=True).start()
    return onceki


def haber_rozeti_html(haberler):
    """Hisse kartının altına konacak rozet; haber yoksa boş metin."""
    if not haberler:
        return ""

    son = haberler[0]
    link = str(son.get("link") or "")

    if not link.lower().startswith(("http://", "https://")):
        return ""

    bugun = turkiye_saati().date()
    saat = son["zaman"].strftime("%H:%M")
    zaman_metni = saat if son["zaman"].date() == bugun else f"dün {saat}"

    etiket = f"📰 {son['tur']} {zaman_metni}"
    if len(haberler) > 1:
        etiket += f" · {len(haberler)}"

    ipucu = f"{son['baslik']} (son 48 saatte {len(haberler)} haber)"

    return (
        '<div style="margin-top:4px;">'
        f'<a href="{html.escape(link)}" target="_blank" '
        'rel="noopener noreferrer" '
        f'title="{html.escape(ipucu)}" '
        'style="display:inline-block;padding:2px 9px;border-radius:12px;'
        'font-size:11.5px;font-weight:600;letter-spacing:0;'
        'text-decoration:none;white-space:nowrap;color:#ffd166;'
        'background:rgba(255,209,102,0.14);'
        'border:1px solid rgba(255,209,102,0.5);">'
        f'{html.escape(etiket)}</a></div>'
    )


# ==================================================
# FİNANSAL TAKVİM - TEMETTÜ VE EARNINGS TARİHLERİ
# ==================================================
@st.cache_data(ttl=3600, show_spinner=False)
def finansal_takvim_getir(hisse_kodu):
    """
    Belirtilen hisse için yahoo finance üzerinden finansal
    takvim bilgilerini getirir: temettü, kazanç (earnings)
    ve bölünme (split) tarihleri.
    """
    hisse_kodu = hisse_kodu.strip().upper()

    if not hisse_kodu:
        return None

    sembol = f"{hisse_kodu}.IS"

    try:
        hisse = yf.Ticker(sembol)
        takvim = hisse.get_calendar()

        sonuclar = {}

        if takvim is not None:
            if isinstance(takvim, dict):
                takvim = {str(_k): _v for _k, _v in takvim.items()}
            else:
                takvim = {}

        if takvim:
            try:
                _kazanc = takvim.get("Earnings Date", None)
                if _kazanc is not None:
                    if hasattr(_kazanc, "__iter__") and not isinstance(
                        _kazanc, str
                    ):
                        _kazanc = list(_kazanc)
                        sonuclar["earnings"] = [
                            _t.strftime("%d.%m.%Y")
                            if hasattr(_t, "strftime") else str(_t)
                            for _t in _kazanc if _t is not None
                        ]
                    else:
                        sonuclar["earnings"] = (
                            _kazanc.strftime("%d.%m.%Y")
                            if hasattr(_kazanc, "strftime")
                            else str(_kazanc)
                        )
            except Exception:
                pass

            for _anahtar, _etiket in [
                ("Ex-Dividend Date", "temettu_eski"),
                ("Dividend Pay Date", "temettu_odeme"),
                ("Stock Split Date", "bolunme")
            ]:
                try:
                    _tarih = takvim.get(_anahtar, None)
                    if _tarih is not None and not isinstance(_tarih, list):
                        sonuclar[_etiket] = (
                            _tarih.strftime("%d.%m.%Y")
                            if hasattr(_tarih, "strftime")
                            else str(_tarih)
                        )
                except Exception:
                    pass

        try:
            temettu_gd = hisse.dividends
            if temettu_gd is not None and len(temettu_gd) > 0:
                son_temettuler = temettu_gd.tail(
                    8
                ).reset_index()

                son_temettuler.columns = [
                    "tarih", "temettu"
                ]

                son_temettuler["tarih"] = (
                    son_temettuler["tarih"]
                    .dt.strftime("%d.%m.%Y")
                )

                sonuclar["temettu_gecmis"] = (
                    son_temettuler.to_dict("records")
                )
        except Exception:
            pass

        if not sonuclar:
            return None

        return sonuclar

    except Exception:
        return None


# ==================================================
# TEMEL ANALİZ ÖZETİ - DEĞERLEME, KÂRLILIK, BİLANÇO
# ==================================================
_SEKTOR_TR = {
    "Financial Services": "Finans",
    "Industrials": "Sanayi",
    "Basic Materials": "Temel Malzemeler",
    "Consumer Cyclical": "Döngüsel Tüketim",
    "Consumer Defensive": "Defansif Tüketim",
    "Technology": "Teknoloji",
    "Energy": "Enerji",
    "Utilities": "Kamu Hizmetleri",
    "Real Estate": "Gayrimenkul",
    "Healthcare": "Sağlık",
    "Communication Services": "İletişim",
}


@st.cache_data(ttl=3600, show_spinner=False)
def temel_analiz_getir(hisse_kodu):
    """
    Belirtilen BIST hissesi için Yahoo Finance üzerinden temel
    analiz özetini (değerleme, kârlılık, bilanço, piyasa) getirir.

    Veri alınamazsa hata fırlatır; böylece başarısız sonuç 1 saatlik
    önbelleğe yazılmaz ve bir sonraki denemede yeniden sorgulanır.
    """
    kod = hisse_kodu.strip().upper()

    if not kod:
        raise ValueError("Hisse kodu boş.")

    sembol = kod if "." in kod else kod + ".IS"

    bilgi = yf.Ticker(sembol).info or {}

    if not any(
        bilgi.get(_k) is not None
        for _k in (
            "marketCap", "trailingPE", "priceToBook",
            "longName", "shortName"
        )
    ):
        raise ValueError("Temel veri bulunamadı.")

    def _al(anahtar):
        _d = bilgi.get(anahtar)

        if (
            isinstance(_d, (int, float))
            and not isinstance(_d, bool)
            and not pd.isna(_d)
        ):
            return float(_d)

        return None

    def _yuzde(anahtar):
        _d = _al(anahtar)
        return _d * 100 if _d is not None else None

    fiyat = (
        _al("currentPrice")
        or _al("regularMarketPrice")
        or _al("previousClose")
    )

    # Temettü verimi: Yahoo'nun dividendYield alanı sürüme göre
    # oran ya da yüzde döndürebildiği için, belirsizlik olmasın diye
    # yıllık temettü tutarı / fiyat olarak hesaplanır.
    _temettu_tutari = _al("dividendRate")

    if _temettu_tutari and fiyat:
        temettu_verimi = _temettu_tutari / fiyat * 100
    else:
        temettu_verimi = _yuzde("trailingAnnualDividendYield")

    _sektor = bilgi.get("sector") or ""

    # Ödenmiş sermaye (BIST payları varsayılan olarak 1 TL nominaldir;
    # yaklaşık değerdir) ve öz sermaye (piyasa değeri / PD/DD)
    _pay_adedi = _al("sharesOutstanding")
    _pd = _al("marketCap")
    _pddd2 = _al("priceToBook")
    _oz = None

    if _pd and _pddd2 and _pddd2 > 0:
        _oz = _pd / _pddd2
    elif _pay_adedi:
        _dk = _al("bookValue")
        if _dk:
            _oz = _pay_adedi * _dk

    return {
        "ad": (
            bilgi.get("longName")
            or bilgi.get("shortName")
            or kod
        ),
        "sektor": _SEKTOR_TR.get(_sektor, _sektor),
        "fiyat": fiyat,
        "piyasa_degeri": _al("marketCap"),
        "fk": _al("trailingPE"),
        "ileri_fk": _al("forwardPE"),
        "pddd": _al("priceToBook"),
        "fd_favok": _al("enterpriseToEbitda"),
        "fiyat_satis": _al("priceToSalesTrailing12Months"),
        "hbk": _al("trailingEps"),
        "defter_degeri": _al("bookValue"),
        "roe": _yuzde("returnOnEquity"),
        "roa": _yuzde("returnOnAssets"),
        "brut_marj": _yuzde("grossMargins"),
        "faaliyet_marj": _yuzde("operatingMargins"),
        "net_marj": _yuzde("profitMargins"),
        "gelir_buyume": _yuzde("revenueGrowth"),
        "kar_buyume": _yuzde("earningsGrowth"),
        # Yahoo, borç/özsermayeyi zaten yüzde olarak verir
        "borc_ozsermaye": _al("debtToEquity"),
        "cari_oran": _al("currentRatio"),
        "nakit": _al("totalCash"),
        "borc": _al("totalDebt"),
        "temettu_verimi": temettu_verimi,
        "beta": _al("beta"),
        "hafta52_dusuk": _al("fiftyTwoWeekLow"),
        "hafta52_yuksek": _al("fiftyTwoWeekHigh"),
        "pay_adedi": _pay_adedi,
        "sermaye": _pay_adedi,
        "oz_sermaye": _oz,
    }


def temel_yuzde_format(deger):
    """% işaretli Türk formatı: 12,34 -> %12,34 ; -5 -> -%5,00"""
    if deger is None:
        return "-"

    _isaret = "-" if deger < 0 else ""
    return f"{_isaret}%{sayi_format(abs(deger))}"


def temel_buyuk_sayi_format(deger):
    """Büyük TL tutarlarını Milyon/Milyar/Trilyon olarak yazar."""
    if deger is None:
        return "-"

    _mutlak = abs(deger)

    if _mutlak >= 1e12:
        return f"{sayi_format(deger / 1e12)} Trilyon TL"
    if _mutlak >= 1e9:
        return f"{sayi_format(deger / 1e9)} Milyar TL"
    if _mutlak >= 1e6:
        return f"{sayi_format(deger / 1e6)} Milyon TL"

    return tl_format(deger)


def temel_adet_format(deger):
    """Büyük hacim/adet değerlerini Milyon/Milyar adet yazar."""
    if deger is None:
        return "-"

    _mutlak = abs(float(deger))

    if _mutlak >= 1e9:
        return f"{sayi_format(float(deger) / 1e9)} Milyar adet"
    if _mutlak >= 1e6:
        return f"{sayi_format(float(deger) / 1e6)} Milyon adet"

    return f"{sayi_format(float(deger))} adet"


@st.cache_data(ttl=1800, show_spinner=False)
def _hisse_macd_likidite(sembol):
    """Hisse için günlük/aylık/yıllık MACD (12,26,9) ile likidite
    (hacim ve işlem hacmi) değerlerini Yahoo günlük verisi üzerinden
    üretir. Tek bir indirme ile: günlük MACD, aylık ve yıllık
    kapanışa yeniden örneklenmiş MACD, son 20 gün ortalamaları ve
    son günün hacmi döndürülür."""
    import yfinance as _yf

    _v = _yf.Ticker(str(sembol).strip().upper()).history(
        period="10y",
        interval="1d",
        auto_adjust=False,
    )

    if _v.empty or "Close" not in _v:
        raise ValueError("Fiyat verisi bulunamadı.")

    _son = _v.iloc[-1]
    _ks = _v["Close"].dropna()

    if "Volume" in _v:
        _para = (_v["Close"] * _v["Volume"]).astype(float)
    else:
        _para = pd.Series(float("nan"), index=_v.index)

    if len(_ks) < 30 or len(_ks) < 3:
        raise ValueError("MACD için yeterli veri yok.")

    def _macd_son(_kap):
        _em12 = _kap.ewm(span=12, adjust=False).mean()
        _em26 = _kap.ewm(span=26, adjust=False).mean()
        _macd = _em12 - _em26
        _sinyal = _macd.ewm(span=9, adjust=False).mean()
        _hist = _macd - _sinyal
        _bod = _macd.dropna()

        if _bod.empty:
            return None, None, None

        _hk = _hist.dropna()

        return (
            float(_bod.iloc[-1]),
            float(_sinyal.dropna().iloc[-1])
            if not _sinyal.dropna().empty else None,
            float(_hk.iloc[-1]) if not _hk.empty else None,
        )

    _macd_g, _sin_g, _hist_g = _macd_son(_ks)

    def _aylik_yillik(_freq_yeni, _freq_eski):
        try:
            return _ks.resample(_freq_yeni).last().dropna()
        except ValueError:
            return _ks.resample(_freq_eski).last().dropna()

    try:
        _macd_a, _sin_a, _hist_a = _macd_son(
            _aylik_yillik("1ME", "1M")
        )
    except Exception:
        _macd_a, _sin_a, _hist_a = None, None, None

    try:
        _macd_y, _sin_y, _hist_y = _macd_son(
            _aylik_yillik("1YE", "1Y")
        )
    except Exception:
        _macd_y, _sin_y, _hist_y = None, None, None

    _ort20_para = (
        float(_para.tail(20).mean())
        if _para.notna().any() else None
    )
    _ort20_hacim = (
        float(_v["Volume"].tail(20).mean())
        if "Volume" in _v else None
    )
    _para_g = _para.dropna()
    _hacim_g = _v["Volume"].dropna()

    return {
        "macd_gunluk": _macd_g,
        "macd_gunluk_sinyal": _sin_g,
        "macd_gunluk_hist": _hist_g,
        "macd_aylik": _macd_a,
        "macd_aylik_hist": _hist_a,
        "macd_yillik": _macd_y,
        "macd_yillik_hist": _hist_y,
        "hacim_son": (
            float(_hacim_g.iloc[-1]) if not _hacim_g.empty else None
        ),
        "hacim_ort20": _ort20_hacim,
        "para_son": (
            float(_para_g.iloc[-1]) if not _para_g.empty else None
        ),
        "para_ort20": _ort20_para,
        "fiyat": float(_ks.iloc[-1]),
    }


def _macd_ozet(_hist):
    """MACD histogram işaretine göre kısa yorum."""
    if _hist is None:
        return "-"
    if _hist > 0:
        return f"{_hist:+.4f} (pozitif)"
    if _hist < 0:
        return f"{_hist:+.4f} (negatif)"
    return "0.0000 (nötr)"


st.markdown(
    """
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@700;800;900&display=swap');

    /* ===== NEON ADA: SEKMELER + "BTA ALGORİTMA VE PİYASA" BAŞLIĞI ===== */
    .bta-baslik-neon {
        font-family: 'Plus Jakarta Sans', 'Segoe UI', sans-serif;
        font-weight: 900;
        font-size: clamp(26px, 4.6vw, 44px);
        letter-spacing: 1.5px;
        text-align: center;
        margin: 6px auto 16px auto;
        padding: 12px 20px;
        color: #eafffb;
        background: linear-gradient(90deg, #00f5c8, #4da6ff, #00f5c8);
        background-size: 200% auto;
        -webkit-background-clip: text;
        background-clip: text;
        -webkit-text-fill-color: transparent;
        animation: btaUgla 6s linear infinite, btaBaslikNeon 2.4s ease-in-out infinite;
        filter: drop-shadow(0 0 16px rgba(0, 245, 200, 0.55));
    }
    @keyframes btaUgla {
        0% { background-position: 0% center; }
        100% { background-position: 200% center; }
    }
    @keyframes btaBaslikNeon {
        0%, 100% { filter: drop-shadow(0 0 8px rgba(0, 245, 200, 0.35)); }
        50% { filter: drop-shadow(0 0 24px rgba(0, 245, 200, 0.95)); }
    }
    /* ===== HABERLER / ARAÇLAR / DİĞER panel başlıkları:
       en üstteki "BTA ALGORİTMA VE PİYASA" ile aynı neon yazı karakteri (büyük başlık).
       NOT: summary'nin kendi ok/ikon span'ına DOKUNMUYORUZ, sadece metin (p) hedefleniyor. */
    .st-key-bta_ai_expander summary p,
    .st-key-bta_haberler_expander summary p,
    .st-key-bta_araclar_expander summary p,
    .st-key-bta_diger_expander summary p,
    .st-key-bta_derin_expander summary p,
    .st-key-bta_teknik_expander summary p,
    .st-key-bta_takvim_expander summary p,
    .st-key-bta_ozel_expander summary p {
        font-family: 'Plus Jakarta Sans', 'Segoe UI', sans-serif !important;
        font-weight: 900 !important;
        font-size: clamp(16px, 2.6vw, 24px) !important;
        letter-spacing: 1.5px !important;
        white-space: nowrap !important;
        background: linear-gradient(90deg, #00f5c8, #4da6ff, #00f5c8) !important;
        background-size: 200% auto !important;
        -webkit-background-clip: text !important;
        background-clip: text !important;
        -webkit-text-fill-color: transparent !important;
        animation: none !important;
        filter: none;
    }
    /* ===== Bu 3 panelin İÇİNDEKİ sekme butonları: aynı neon karakter, normal (taşmayan) boyutta ===== */
    .st-key-bta_haberler_expander [data-testid="stTabs"] [role="tab"] p,
    .st-key-bta_araclar_expander [data-testid="stTabs"] [role="tab"] p,
    .st-key-bta_diger_expander [data-testid="stTabs"] [role="tab"] p,
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tab"] p,
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tab"] p {
        font-family: 'Plus Jakarta Sans', 'Segoe UI', sans-serif !important;
        font-weight: 900 !important;
        font-size: 18px !important;
        letter-spacing: 0.5px !important;
        white-space: nowrap !important;
        color: #ffffff !important;
        background: none !important;
        -webkit-background-clip: initial !important;
        background-clip: initial !important;
        -webkit-text-fill-color: #ffffff !important;
        animation: none !important;
        filter: none !important;
        text-shadow:
            0 0 8px rgba(0, 245, 200, 0.95),
            0 0 18px rgba(0, 245, 200, 0.5),
            0 1px 2px rgba(0, 0, 0, 0.9) !important;
    }
    .st-key-bta_haberler_expander [data-testid="stTabs"] [role="tab"][data-selected] p,
    .st-key-bta_araclar_expander [data-testid="stTabs"] [role="tab"][data-selected] p,
    .st-key-bta_diger_expander [data-testid="stTabs"] [role="tab"][data-selected] p,
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tab"][data-selected] p,
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tab"][data-selected] p {
        color: #ffd34d !important;
        -webkit-text-fill-color: #ffd34d !important;
        text-shadow:
            0 0 10px rgba(255, 211, 77, 0.95),
            0 0 22px rgba(255, 211, 77, 0.6),
            0 1px 2px rgba(0, 0, 0, 0.9) !important;
    }
    .st-key-bta_haberler_expander [data-testid="stTabs"] [role="tab"],
    .st-key-bta_araclar_expander [data-testid="stTabs"] [role="tab"],
    .st-key-bta_diger_expander [data-testid="stTabs"] [role="tab"],
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tab"],
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tab"] {
        flex: 0 0 auto !important;
    }
    /* ÖZEL + DERİN panelin sekmeleri eşit genişlikte, düzgün sıralı;
       uzun başlıklar ("Yabancı Takas Oranları" vb.) mobilde alt satıra geçer */
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tablist"],
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tablist"] {
        display: flex !important;
        justify-content: center !important;
        align-items: center !important;
        width: 100% !important;
        gap: 4px !important;
    }
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tab"],
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tab"] {
        flex: 1 1 0 !important;
        min-width: 0 !important;
        padding: 8px 6px !important;
    }
    .st-key-bta_ozel_expander [data-testid="stTabs"] [role="tab"] p,
    .st-key-bta_derin_expander [data-testid="stTabs"] [role="tab"] p {
        font-size: clamp(13px, 3.3vw, 17px) !important;
        white-space: normal !important;
        text-align: center !important;
    }
    [data-testid="stTabs"] [role="tab"][data-selected],
    [data-testid="stTabs"] [data-testid="stTab"][data-selected],
    .stTabs [role="tab"][data-selected] {
        box-shadow:
            0 0 12px rgba(0, 245, 200, 0.55),
            0 0 30px rgba(0, 245, 200, 0.3) !important;
        animation: none !important;
    }
    .stTabs [role="tab"]:hover:not([data-selected]) {
        box-shadow: 0 0 10px rgba(255, 75, 75, 0.55) !important;
    }
    @keyframes btaTabNeon {
        0%, 100% {
            box-shadow:
                0 0 10px rgba(0, 245, 200, 0.4),
                0 0 26px rgba(0, 245, 200, 0.2);
        }
        50% {
            box-shadow:
                0 0 20px rgba(0, 245, 200, 0.9),
                0 0 48px rgba(0, 245, 200, 0.5);
        }
    }

    .stApp {
        background-color: #0c1730 !important;
        background-image:
            linear-gradient(
                rgba(13, 27, 51, 0.94),
                rgba(8, 17, 34, 0.98)
            ),
            url("https://images.unsplash.com/photo-1611974789855-9c2a0a7236a3?auto=format&fit=crop&w=2400&q=85") !important;
        background-size: cover !important;
        background-position: center !important;
        background-attachment: fixed !important;
    }

    [data-testid="stHeader"] {
        background: transparent !important;
    }

    [data-testid="stSidebar"] > div:first-child {
        background: rgba(13, 27, 51, 0.98) !important;
    }

    .main .block-container {
        max-width: 1450px !important;
        padding-top: 1rem !important;
        padding-bottom: 2rem !important;
    }

    h1, h2, h3, h4, p, label, span, div {
        text-shadow: 0 1px 2px rgba(0, 0, 0, 0.7);
    }

    .bta-logo-alani {
        width: 100%;
        margin-bottom: 12px;
        text-align: center;
    }

    .bta-logo {
        display: inline-flex;
        flex-wrap: wrap;
        align-items: center;
        justify-content: center;
        gap: 12px;
        color: #00f5c8;
    }

    .bta-logo-ikon {
        width: 46px;
        height: 46px;
        flex-shrink: 0;
        filter: drop-shadow(0 0 6px #00f5c8)
                drop-shadow(0 0 14px #168cff);
    }

    .bta-logo-metin {
        display: inline-block;
        font-family: "Consolas", "SFMono-Regular", "Menlo",
                     "Courier New", monospace;
        font-size: 42px;
        font-weight: 900;
        letter-spacing: 2px;
        color: #eafffb;
        text-shadow:
            -1px -1px 0 rgba(0, 0, 0, 0.9),
            1px 1px 0 rgba(255, 255, 255, 0.35),
            0 3px 0 rgba(0, 90, 120, 0.55),
            0 0 10px #00f5c8,
            0 0 26px #00f5c8,
            0 0 48px #168cff;
    }

    /* ============================================
       PİYASA ÖZETİ - EKRAN KÖŞESİNDE KOMPAKT KART
       ============================================ */
    .piyasa-ozet-badge {
        background: rgba(5, 18, 32, 0.94);
        border: 1px solid rgba(0, 245, 200, 0.45);
        border-left: 4px solid #00f5c8;
        border-radius: 8px;
        padding: 8px 12px;
        margin: 0 0 14px auto;
        max-width: 460px;
        box-shadow: 0 4px 18px rgba(0, 0, 0, 0.55);
    }

    .piyasa-ozet-badge-header {
        font-size: 12px;
        font-weight: 800;
        letter-spacing: 1.5px;
        color: #00f5c8;
        margin-bottom: 6px;
        text-align: right;
    }

    .piyasa-ozet-satir {
        display: grid;
        grid-template-columns: 1fr 105px 72px;
        align-items: center;
        column-gap: 8px;
        padding: 7px 2px;
        border-bottom: 1px solid rgba(255, 255, 255, 0.14);
        font-size: 15px;
        font-weight: 600;
        white-space: nowrap;
    }

    .piyasa-ozet-satir:last-child {
        border-bottom: none;
    }

    .piyasa-ozet-isim {
        color: #eaf4fa;
        font-weight: 700;
        text-align: left;
        overflow: hidden;
        text-overflow: ellipsis;
    }

    .piyasa-ozet-fiyat {
        color: #ffffff;
        font-weight: 800;
        font-size: 18px;
        font-variant-numeric: tabular-nums;
        text-align: right;
        letter-spacing: 0.3px;
    }

    .piyasa-ozet-degisim {
        font-weight: 800;
        font-size: 17px;
        font-variant-numeric: tabular-nums;
        text-align: right;
    }

    .piyasa-ozet-not {
        font-size: 10.5px;
        color: #8aa7bb;
        margin-top: 6px;
        text-align: center;
        line-height: 1.4;
    }

    /* ============================================
       HIZLI ARAÇLAR (HİSSE ARAMA + DÖVİZ ÇEVİRİCİ)
       ============================================ */
    .hizli-arac-baslik {
        background: linear-gradient(
            90deg,
            rgba(0, 245, 200, 0.18),
            rgba(22, 140, 255, 0.12)
        );
        border: 1px solid rgba(0, 245, 200, 0.4);
        border-left: 4px solid #00f5c8;
        border-radius: 8px;
        padding: 8px 12px;
        margin: 6px 0 12px 0;
        font-size: 15px;
        font-weight: 800;
        letter-spacing: 1.2px;
        color: #00f5c8;
        text-align: center;
    }

    .hisse-arama-kart {
        background: rgba(5, 18, 32, 0.94);
        border: 1px solid rgba(0, 245, 200, 0.4);
        border-radius: 8px;
        padding: 10px 14px;
        margin: 6px 0;
    }

    .hisse-arama-ust {
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        gap: 10px;
        flex-wrap: wrap;
    }

    .hisse-arama-kod {
        font-size: 20px;
        font-weight: 800;
        color: #eaf4fa;
        letter-spacing: 1px;
    }

    .hisse-arama-fiyat {
        font-size: 22px;
        font-weight: 800;
        font-variant-numeric: tabular-nums;
    }

    .hisse-arama-degisim {
        font-size: 15px;
        font-weight: 800;
        margin: 2px 0 8px 0;
    }

    .hisse-arama-alt {
        display: flex;
        flex-wrap: wrap;
        gap: 6px 18px;
        font-size: 13px;
        color: #eaf4fa;
        border-top: 1px solid rgba(255, 255, 255, 0.14);
        padding-top: 8px;
    }

    .hareket-kart {
        background: rgba(5, 18, 32, 0.9);
        border: 1px solid rgba(0, 245, 200, 0.3);
        border-radius: 8px;
        padding: 6px 10px;
        height: 100%;
    }

    .hareket-baslik {
        font-size: 14px;
        font-weight: 800;
        text-align: center;
        padding: 2px 0 6px 0;
        border-bottom: 1px solid rgba(255, 255, 255, 0.14);
        margin-bottom: 4px;
    }

    .hareket-satir {
        display: grid;
        grid-template-columns: 1fr auto auto;
        align-items: center;
        column-gap: 10px;
        padding: 5px 2px;
        border-bottom: 1px solid
            rgba(255, 255, 255, 0.08);
        font-size: 14px;
        font-weight: 700;
    }

    .hareket-satir:last-child {
        border-bottom: none;
    }

    .hareket-satir-kod {
        color: #eaf4fa;
        font-weight: 800;
    }

    .hareket-satir-fiyat {
        color: #ffffff;
        font-variant-numeric: tabular-nums;
    }

    .hareket-satir-deg {
        font-weight: 800;
        font-variant-numeric: tabular-nums;
        text-align: right;
    }

    @media screen and (max-width: 768px) {
        .hareket-satir {
            font-size: 12.5px;
            column-gap: 6px;
        }
    }

    @media screen and (max-width: 768px) {
        .piyasa-ozet-badge {
            max-width: 100%;
            padding: 6px 10px;
        }

        .piyasa-ozet-satir {
            grid-template-columns: 1fr 92px 66px;
            font-size: 13px;
            padding: 6px 2px;
        }

        .piyasa-ozet-fiyat {
            font-size: 14px;
        }
    }

    /* ============================================
       SON DAKİKA HABERLERİ PANELİ
       ============================================ */
    .son-dakika-baslik {
        display: flex;
        align-items: center;
        gap: 10px;
        background: linear-gradient(
            90deg,
            rgba(255, 82, 100, 0.18),
            rgba(255, 82, 100, 0.04)
        );
        border: 1px solid rgba(255, 82, 100, 0.55);
        border-radius: 8px;
        padding: 8px 14px;
        margin: 6px 0 0 0;
        font-size: 17px;
        font-weight: 800;
        color: #ffffff;
        letter-spacing: 1px;
        text-shadow: 0 0 10px rgba(255, 82, 100, 0.8);
    }

    .son-dakika-nokta {
        width: 11px;
        height: 11px;
        border-radius: 50%;
        background: #ff3b4e;
        box-shadow: 0 0 12px #ff3b4e;
        animation: son_dakika_yanip_son 1s ease-in-out infinite;
        flex-shrink: 0;
    }

    @keyframes son_dakika_yanip_son {
        0%, 100% {
            opacity: 1;
        }
        50% {
            opacity: 0.25;
        }
    }

    .son-dakika-tarih {
        margin-left: auto;
        font-size: 12px;
        font-weight: 600;
        color: #ff9da8;
    }

    .son-dakika-cerceve {
        background: rgba(6, 20, 33, 0.6);
        border: 1px solid rgba(255, 82, 100, 0.35);
        border-radius: 10px;
        padding: 10px 12px;
        max-height: 380px;
        overflow-y: auto;
        scroll-behavior: smooth;
        margin: 0 0 6px 0;
    }

    .son-dakika-cerceve::-webkit-scrollbar {
        width: 6px;
    }

    .son-dakika-cerceve::-webkit-scrollbar-thumb {
        background: rgba(255, 82, 100, 0.4);
        border-radius: 4px;
    }

    .son-dakika-cerceve::-webkit-scrollbar-track {
        background: rgba(255, 255, 255, 0.05);
    }

    .son-dakika-haber-kart {
        display: flex;
        align-items: flex-start;
        gap: 10px;
        background: #000000;
        border-left: 3px solid #3a3a3a;
        border-radius: 6px;
        padding: 8px 12px;
        margin: 6px 0;
        font-size: 13.5px;
        line-height: 1.45;
        word-break: break-word;
    }

    .son-dakika-haber-saat {
        flex-shrink: 0;
        color: #b0b0b0;
        font-size: 11.5px;
        font-weight: 600;
        padding-top: 2px;
        min-width: 46px;
    }

    .son-dakika-haber-link {
        color: #f2f2f2 !important;
        text-decoration: none;
        font-weight: 600;
        text-shadow: none !important;
    }

    .son-dakika-haber-link:hover {
        color: #ffffff !important;
        text-decoration: underline;
    }

    @media screen and (max-width: 768px) {
        .son-dakika-baslik {
            font-size: 14px;
            padding: 7px 10px;
            gap: 8px;
        }

        .son-dakika-cerceve {
            max-height: 320px;
            padding: 8px 8px;
        }

        .son-dakika-haber-kart {
            font-size: 12.5px;
            padding: 7px 9px;
            gap: 8px;
        }

        .son-dakika-haber-saat {
            font-size: 11px;
            min-width: 42px;
        }
    }

    .mesaj-karti {
        background: rgba(8, 29, 45, 0.95);
        border-left: 3px solid #00f5c8;
        border-radius: 7px;
        padding: 10px;
        margin: 7px 0;
    }

    /* ============================================
       SOHBET - ÇERÇEVE İÇİNDE KAYAN MESAJLAR
       ============================================ */
    .sohbet-cerceve {
        background: rgba(6, 20, 33, 0.6);
        border: 1px solid rgba(0, 245, 200, 0.35);
        border-radius: 10px;
        padding: 10px 12px;
        max-height: 460px;
        overflow-y: auto;
        scroll-behavior: smooth;
        margin-bottom: 10px;
    }

    .sohbet-cerceve::-webkit-scrollbar {
        width: 6px;
    }

    .sohbet-cerceve::-webkit-scrollbar-thumb {
        background: rgba(0, 245, 200, 0.35);
        border-radius: 4px;
    }

    .sohbet-cerceve::-webkit-scrollbar-track {
        background: rgba(255, 255, 255, 0.05);
    }

    .sohbet-kart {
        background: rgba(8, 29, 45, 0.97);
        border-left: 3px solid #00f5c8;
        border-radius: 7px;
        padding: 8px 12px;
        margin: 6px 0;
        font-size: 14px;
        word-break: break-word;
    }

    .sohbet-kart-baslik {
        font-size: 13px;
        font-weight: 700;
        color: #ffd166;
        margin-bottom: 2px;
    }

    .sohbet-kart-saat {
        font-size: 11px;
        color: #8aa7bb;
    }

    .sohbet-mesaj-metni {
        color: #f0f0f0;
        line-height: 1.5;
    }

    .sohbet-silme {
        display: flex;
        justify-content: flex-end;
        gap: 8px;
        margin-top: 4px;
    }

    .sohbet-sil-buton {
        background: rgba(255, 82, 100, 0.18);
        border: 1px solid rgba(255, 82, 100, 0.5);
        color: #ff8d99;
        border-radius: 6px;
        padding: 2px 10px;
        font-size: 11px;
        cursor: pointer;
        text-decoration: none;
        display: inline-block;
    }

    .sohbet-sil-buton:hover {
        background: rgba(255, 82, 100, 0.35);
        color: white;
    }

    .sohbet-uyari {
        background: rgba(60, 45, 8, 0.85);
        border: 1px solid rgba(255, 209, 102, 0.7);
        border-left: 4px solid #ffd166;
        border-radius: 8px;
        padding: 11px 14px;
        margin: 6px 0 12px 0;
        color: #ffe9b0;
        font-size: 12.5px;
        line-height: 1.6;
    }

    /* ============================================
       BEĞENİ - ŞEFFAF PARMAK İŞARETİ + (SAYI)
       ============================================ */
    .st-key-bta_begeni_buton {
        background: transparent !important;
        border: 1px solid transparent !important;
        box-shadow: none !important;
        font-size: 26px !important;
        padding: 4px 10px !important;
        color: #00f5c8 !important;
    }

    .st-key-bta_begeni_buton:hover {
        background: rgba(0, 245, 200, 0.12) !important;
        border: 1px solid rgba(0, 245, 200, 0.4) !important;
    }

    .sohbet-begeni-sayi {
        display: flex;
        align-items: center;
        height: 100%;
        font-size: 20px;
        font-weight: 800;
        color: #00f5c8;
        text-shadow: 0 0 8px rgba(0, 245, 200, 0.6);
        padding: 0 4px;
    }

    .sohbet-haber-cerceve .sohbet-kart {
        border-left-color: #ff9f43;
    }

    /* ============================================
       SON HABER BÜLTENİ (büyük ve okunaklı)
       ============================================ */
    .haber-bulteni-baslik {
        display: flex;
        align-items: center;
        justify-content: space-between;
        flex-wrap: wrap;
        gap: 8px;
        background: linear-gradient(
            90deg,
            rgba(255, 82, 100, 0.22),
            rgba(255, 82, 100, 0.06)
        );
        border: 1px solid rgba(255, 82, 100, 0.6);
        border-radius: 9px;
        padding: 12px 18px;
        margin: 4px 0 12px 0;
        font-size: 17px;
        font-weight: 800;
        color: #ffffff;
        letter-spacing: 1px;
        text-shadow: 0 0 12px rgba(255, 82, 100, 0.8);
    }

    .haber-bulteni-baslik span {
        font-size: 13px;
        font-weight: 600;
        color: #ff9da8;
    }

    .haber-bulteni-kart {
        background: transparent;
        border-left: 5px solid #3a3a3a;
        border-radius: 10px;
        padding: 20px 22px;
        margin: 12px 0;
        transition: background 0.3s ease;
    }

    .haber-bulteni-kart:hover {
        background: rgba(255, 255, 255, 0.04);
    }

    .haber-bulteni-saat {
        font-size: 17px;
        font-weight: 700;
        color: #cfcfcf;
        margin-bottom: 10px;
    }

    /* GÜNCEL ARZ HABERLERİ - sade */
    .arz-kart {
        border-left-color: #3a3a3a;
    }

    .arz-kaynak {
        color: #cfcfcf;
        font-weight: 700;
    }

    .haber-bulteni-link,
    .haber-bulteni-cerceve .haber-bulteni-link {
        display: block;
        color: #ffffff !important;
        text-decoration: none !important;
        font-size: 24px;
        font-weight: 700;
        line-height: 1.55;
        word-break: break-word;
        text-shadow: none !important;
    }

    .haber-bulteni-link:hover {
        color: #ffffff !important;
        text-decoration: underline !important;
    }

    @media screen and (max-width: 768px) {
        .haber-bulteni-baslik {
            font-size: 16px;
            padding: 10px 14px;
        }

        .haber-bulteni-saat {
            font-size: 16px;
        }

        .haber-bulteni-link {
            font-size: 21px;
            line-height: 1.5;
        }

        .haber-bulteni-kart {
            padding: 16px 15px;
        }
    }

    @media screen and (max-width: 768px) {
        .sohbet-cerceve {
            max-height: 420px;
            padding: 8px 8px;
        }

        .sohbet-kart {
            padding: 7px 10px;
            font-size: 13px;
        }

        .st-key-bta_begeni_buton {
            font-size: 22px !important;
            padding: 4px 8px !important;
        }

        .sohbet-begeni-sayi {
            font-size: 17px;
        }
    }

    .bilgi-karti {
        background: rgba(9, 31, 48, 0.95);
        border: 1px solid rgba(0, 245, 200, 0.35);
        border-radius: 9px;
        padding: 14px;
        margin: 10px 0;
        line-height: 1.8;
    }

    .paylas-container {
        display: flex;
        flex-wrap: wrap;
        gap: 12px;
        justify-content: center;
        margin: 20px 0;
    }

    .paylas-buton {
        display: inline-flex;
        align-items: center;
        justify-content: center;
        padding: 14px 20px;
        border-radius: 10px;
        text-decoration: none;
        font-weight: bold;
        transition: all 0.3s ease;
        border: none;
        cursor: pointer;
        text-align: center;
        min-width: 140px;
        font-size: 14px;
        box-shadow: 0 2px 8px rgba(0, 0, 0, 0.3);
    }

    .paylas-twitter {
        background-color: #1DA1F2;
        color: white;
    }

    .paylas-twitter:hover {
        background-color: #1a8cd8;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(29, 161, 242, 0.6);
    }

    .paylas-facebook {
        background-color: #1877F2;
        color: white;
    }

    .paylas-facebook:hover {
        background-color: #0a66c2;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(24, 119, 242, 0.6);
    }

    .paylas-linkedin {
        background-color: #0A66C2;
        color: white;
    }

    .paylas-linkedin:hover {
        background-color: #084998;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(10, 102, 194, 0.6);
    }

    .paylas-whatsapp {
        background-color: #25D366;
        color: white;
    }

    .paylas-whatsapp:hover {
        background-color: #1eaa54;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(37, 211, 102, 0.6);
    }

    .paylas-telegram {
        background-color: #0088cc;
        color: white;
    }

    .paylas-telegram:hover {
        background-color: #006ba3;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(0, 136, 204, 0.6);
    }

    .paylas-email {
        background-color: #EA4335;
        color: white;
    }

    .paylas-email:hover {
        background-color: #c5221f;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(234, 67, 53, 0.6);
    }

    .paylas-kopya {
        background-color: #00f5c8;
        color: #07131f;
        font-weight: bold;
    }

    .paylas-kopya:hover {
        background-color: #00d4a8;
        transform: translateY(-3px);
        box-shadow: 0 4px 12px rgba(0, 245, 200, 0.6);
    }

    .spk-uyari {
        background: rgba(70, 18, 27, 0.96);
        border: 1px solid #ff5264;
        border-radius: 8px;
        padding: 13px;
        margin-top: 30px;
        color: white;
        font-size: 12px;
        line-height: 1.6;
        text-align: justify;
    }

[data-testid="stHeader"] [data-testid="stStatusWidget"],
[data-testid="stStatusWidget"],
#stStatusWidget,
.stStatusWidget {
    display: none !important;
}

@media screen and (max-width: 768px) {
    .main .block-container {
        padding: 0 0.6rem 1.5rem 0.6rem !important;
    }
        [data-testid="stHeader"] {
            position: fixed !important;
            background: transparent !important;
        }

        .bta-logo {
            gap: 6px;
        }

        .bta-logo-ikon {
            width: clamp(22px, 8vw, 34px);
            height: clamp(22px, 8vw, 34px);
        }

        .bta-logo-metin {
            font-size: clamp(14px, 5vw, 28px);
        }

        [data-testid="stTabs"] button {
            font-size: 17px !important;
            padding: 10px 6px !important;
            flex: 0 0 auto !important;
            line-height: 1.3;
        }

        .stTabs [data-baseweb="tab-list"] {
            -webkit-overflow-scrolling: touch;
        }

        .spk-uyari {
            font-size: 11px;
            text-align: left;
        }

        .paylas-buton {
            min-width: 120px;
            padding: 12px 16px;
            font-size: 12px;
        }

        .paylas-container {
            gap: 8px;
        }
    }

    /* ================================================
       SEKME (TAB) ÇUBUĞU - DAHA BELİRGİN
       ================================================ */
    .stTabs [data-baseweb="tab-list"] {
        background: rgba(0, 245, 200, 0.10);
        border: 2px solid rgba(0, 245, 200, 0.55);
        border-radius: 12px;
        padding: 10px 8px 14px 8px;
        gap: 6px;
        overflow-x: auto;
        scrollbar-width: auto;
        scrollbar-color: rgba(0, 245, 200, 0.85) rgba(0, 245, 200, 0.12);
        box-shadow: 0 0 24px rgba(0, 245, 200, 0.25);
    }

    .stTabs [data-baseweb="tab-list"]::-webkit-scrollbar {
        height: 14px;
    }

    .stTabs [data-baseweb="tab-list"]::-webkit-scrollbar-track {
        background: rgba(0, 245, 200, 0.12);
        border-radius: 10px;
    }

    .stTabs [data-baseweb="tab-list"]::-webkit-scrollbar-thumb {
        background: linear-gradient(
            90deg,
            #00f5c8,
            #168cff
        );
        border-radius: 10px;
        border: 2px solid rgba(0, 0, 0, 0.6);
    }

    .stTabs [data-baseweb="tab-list"]::-webkit-scrollbar-thumb:hover {
        background: linear-gradient(
            90deg,
            #5cffe0,
            #4da6ff
        );
    }

    .stTabs [data-baseweb="tab"] {
        font-size: 22px !important;
        font-weight: 900 !important;
        letter-spacing: 0.4px;
        padding: 14px 20px !important;
        white-space: nowrap;
        border-radius: 10px !important;
        margin: 3px 2px !important;
        border: 2px solid rgba(255, 255, 255, 0.22) !important;
        flex: 0 0 auto !important;
        -webkit-text-stroke: 1px rgba(0, 0, 0, 0.55);
        paint-order: stroke fill;
        box-shadow:
            0 4px 10px rgba(0, 0, 0, 0.55),
            0 1px 0 rgba(255, 255, 255, 0.35) inset,
            0 -1px 0 rgba(0, 0, 0, 0.45) inset;
    }

    .stTabs [data-baseweb="tab"] > div {
        font-size: 22px !important;
        font-weight: 900 !important;
        line-height: 1.25;
    }

    .stTabs [data-baseweb="tab"] img {
        width: 18px;
        height: 18px;
        vertical-align: middle;
        margin-right: 4px;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(1),
    .stTabs [data-baseweb="tab"]:first-of-type {
        color: #00f5c8 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(0, 245, 200, 0.22),
            rgba(0, 245, 200, 0.07)
        ) !important;
        border-color: rgba(0, 245, 200, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(0, 245, 200, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(2),
    .stTabs [data-baseweb="tab"]:nth-of-type(2) {
        color: #4da6ff !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(77, 166, 255, 0.22),
            rgba(77, 166, 255, 0.07)
        ) !important;
        border-color: rgba(77, 166, 255, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(77, 166, 255, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(3),
    .stTabs [data-baseweb="tab"]:nth-of-type(3) {
        color: #b48bff !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(180, 139, 255, 0.22),
            rgba(180, 139, 255, 0.07)
        ) !important;
        border-color: rgba(180, 139, 255, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(180, 139, 255, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(4),
    .stTabs [data-baseweb="tab"]:nth-of-type(4) {
        color: #ff6ec7 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(255, 110, 199, 0.22),
            rgba(255, 110, 199, 0.07)
        ) !important;
        border-color: rgba(255, 110, 199, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(255, 110, 199, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(5),
    .stTabs [data-baseweb="tab"]:nth-of-type(5) {
        color: #ff5264 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(255, 82, 100, 0.22),
            rgba(255, 82, 100, 0.07)
        ) !important;
        border-color: rgba(255, 82, 100, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(255, 82, 100, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(6),
    .stTabs [data-baseweb="tab"]:nth-of-type(6) {
        color: #ffd166 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(255, 209, 102, 0.22),
            rgba(255, 209, 102, 0.07)
        ) !important;
        border-color: rgba(255, 209, 102, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(255, 209, 102, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(7),
    .stTabs [data-baseweb="tab"]:nth-of-type(7) {
        color: #7ddb6e !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(125, 219, 110, 0.22),
            rgba(125, 219, 110, 0.07)
        ) !important;
        border-color: rgba(125, 219, 110, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(125, 219, 110, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(8),
    .stTabs [data-baseweb="tab"]:nth-of-type(8) {
        color: #ff9f43 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(255, 159, 67, 0.22),
            rgba(255, 159, 67, 0.07)
        ) !important;
        border-color: rgba(255, 159, 67, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(255, 159, 67, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(9),
    .stTabs [data-baseweb="tab"]:nth-of-type(9) {
        color: #66d9ff !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(102, 217, 255, 0.22),
            rgba(102, 217, 255, 0.07)
        ) !important;
        border-color: rgba(102, 217, 255, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(102, 217, 255, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(10),
    .stTabs [data-baseweb="tab"]:nth-of-type(10) {
        color: #c77dff !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(199, 125, 255, 0.22),
            rgba(199, 125, 255, 0.07)
        ) !important;
        border-color: rgba(199, 125, 255, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(199, 125, 255, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(11),
    .stTabs [data-baseweb="tab"]:nth-of-type(11) {
        color: #66d9ff !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(102, 217, 255, 0.22),
            rgba(102, 217, 255, 0.07)
        ) !important;
        border-color: rgba(102, 217, 255, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(102, 217, 255, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(12),
    .stTabs [data-baseweb="tab"]:nth-of-type(12) {
        color: #ff9f43 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(255, 159, 67, 0.22),
            rgba(255, 159, 67, 0.07)
        ) !important;
        border-color: rgba(255, 159, 67, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(255, 159, 67, 0.7);;
    }

    .stTabs [data-baseweb="tab-list"] button:nth-of-type(13),
    .stTabs [data-baseweb="tab"]:nth-of-type(13) {
        color: #2ecc71 !important;
        background: radial-gradient(
            circle at 30% 30%,
            rgba(46, 204, 113, 0.22),
            rgba(46, 204, 113, 0.07)
        ) !important;
        border-color: rgba(46, 204, 113, 0.55) !important;
        text-shadow: 2px 2px 0 rgba(0, 0, 0, 0.6), -1px -1px 0 rgba(255, 255, 255, 0.18), 0 0 14px rgba(46, 204, 113, 0.7);
    }

    .stTabs button[role="tab"][aria-selected="true"] {
        color: #ffffff !important;
        font-weight: 900 !important;
        font-size: 36px !important;
        border-radius: 10px !important;
        border-width: 2.5px !important;
        text-shadow:
            -1px -1px 0 rgba(255, 255, 255, 0.6),
            -2px -2px 0 rgba(255, 255, 255, 0.25),
            3px 3px 0 rgba(0, 0, 0, 0.95),
            2px 2px 0 rgba(0, 0, 0, 0.85),
            0 0 25px rgba(0, 245, 200, 0.9) !important;
        box-shadow:
            0 0 20px rgba(0, 245, 200, 0.5),
            0 6px 14px rgba(0, 0, 0, 0.55),
            0 2px 0 rgba(255, 255, 255, 0.4) inset,
            0 -2px 0 rgba(0, 0, 0, 0.5) inset;
        transform: scale(1.05);
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(1) {
        background: rgba(0, 245, 200, 0.45) !important;
        border-color: #00f5c8 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(2) {
        background: rgba(77, 166, 255, 0.45) !important;
        border-color: #4da6ff !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(3) {
        background: rgba(180, 139, 255, 0.45) !important;
        border-color: #b48bff !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(4) {
        background: rgba(255, 110, 199, 0.45) !important;
        border-color: #ff6ec7 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(5) {
        background: rgba(255, 82, 100, 0.45) !important;
        border-color: #ff5264 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(6) {
        background: rgba(255, 209, 102, 0.45) !important;
        border-color: #ffd166 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(7) {
        background: rgba(125, 219, 110, 0.45) !important;
        border-color: #7ddb6e !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(8) {
        background: rgba(255, 159, 67, 0.45) !important;
        border-color: #ff9f43 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(9) {
        background: rgba(102, 217, 255, 0.45) !important;
        border-color: #66d9ff !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(10) {
        background: rgba(199, 125, 255, 0.45) !important;
        border-color: #c77dff !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(11) {
        background: rgba(102, 217, 255, 0.45) !important;
        border-color: #66d9ff !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(12) {
        background: rgba(255, 159, 67, 0.45) !important;
        border-color: #ff9f43 !important;
    }

    .stTabs button[role="tab"][aria-selected="true"]:nth-of-type(13) {
        background: rgba(46, 204, 113, 0.45) !important;
        border-color: #2ecc71 !important;
    }

    .stTabs [role="tablist"] [aria-selected="true"] + *::before,
    .stTabs [data-baseweb="tab-highlight"],
    .stTabs [data-baseweb="tab-border"] {
        display: none !important;
    }

    /* SEKMELERİN İÇİNDEKİ BAŞLIK PANKARTLARI - her biri
       kendi logosu ve rengiyle ayırt edilir */
    .sekme-baslik {
        display: flex;
        align-items: center;
        gap: 10px;
        font-size: 24px;
        font-weight: 800;
        letter-spacing: 0.5px;
        padding: 14px 18px;
        border-radius: 10px;
        margin: 6px 0 14px 0;
        border: 1px solid rgba(255, 255, 255, 0.12);
        border-left-width: 6px;
        background: rgba(0, 0, 0, 0.35);
    }

.sekme-baslik .sb-logo {
        font-size: 34px;
    }

    .sekme-baslik .sekme-baslik-tarih {
        font-size: 13px;
        font-weight: 700;
        color: rgba(255, 255, 255, 0.75);
        background: rgba(0, 0, 0, 0.35);
        border-radius: 12px;
        padding: 4px 12px;
    }

    /* QR paylaşım kartı - beyaz QR'ın çevresine platform
       kimliği eklenir; telefonla okunabilir durumda kalır */
    .qr-kart {
        background: rgba(5, 18, 32, 0.96);
        border: 1px solid rgba(0, 245, 200, 0.45);
        border-top: 4px solid #00f5c8;
        border-radius: 14px;
        padding: 16px;
        max-width: 360px;
        margin: 0 auto;
        text-align: center;
        box-shadow: 0 6px 22px rgba(0, 0, 0, 0.55);
    }

    .qr-kart-ust {
        font-size: 15px;
        font-weight: 800;
        letter-spacing: 0.5px;
        color: #00f5c8;
        margin-bottom: 12px;
    }

    .qr-kart-gorsel {
        background: #ffffff;
        border-radius: 10px;
        padding: 10px;
        display: inline-block;
        box-shadow: 0 2px 10px rgba(0, 0, 0, 0.35);
        max-width: 100%;
    }

    .qr-kart-gorsel img {
        display: block;
        width: 100%;
        max-width: 240px;
        height: auto;
        border-radius: 4px;
    }

    .qr-kart-link {
        font-size: 13px;
        color: #9bd6ff;
        word-break: break-all;
        margin-top: 12px;
        font-weight: 600;
    }

    .qr-kart-alt {
        font-size: 12px;
        color: #c8d6e2;
        margin-top: 8px;
        line-height: 1.5;
    }

    /* =====================================================
       PROFESYONEL MASAÜSTÜ GÖRÜNÜM (>=1024px)
       Telefonda mevcut tasarım korunur; bilgisayarda site
       tarzı, sade ve düzenli bir görünüm uygulanır.
       ===================================================== */
    @media (min-width: 1024px) {
        .main .block-container {
            max-width: 1240px !important;
            padding-top: 1rem !important;
        }

        /* Üst bar: logo solda, kompakt; dev pankart kaldırıldı */
        .bta-logo-alani {
            display: flex;
            align-items: center;
            margin-bottom: 14px;
        }

        .bta-logo {
            justify-content: flex-start;
            gap: 10px;
        }

        .bta-logo-ikon {
            width: 38px;
            height: 38px;
        }

        .bta-logo-metin {
            font-size: 36px;
        }

        /* Sekme çubuğu: profesyonel menü görünümü */
        .stTabs [data-baseweb="tab-list"] {
            background: rgba(6, 20, 33, 0.8) !important;
            border: 1px solid rgba(255, 255, 255, 0.14) !important;
            border-radius: 11px !important;
            padding: 8px 10px !important;
            gap: 3px !important;
            box-shadow: 0 4px 16px rgba(0, 0, 0, 0.35) !important;
            flex-wrap: wrap;
        }

        .stTabs [data-baseweb="tab"] {
            font-size: 20px !important;
            font-weight: 900 !important;
            line-height: 1.3 !important;
            letter-spacing: 0.4px !important;
            padding: 11px 18px !important;
            margin: 3px !important;
            border-radius: 10px !important;
            border: 2px solid rgba(255, 255, 255, 0.3) !important;
            -webkit-text-stroke: 1px rgba(0, 0, 0, 0.5);
            paint-order: stroke fill;
            box-shadow:
                0 4px 10px rgba(0, 0, 0, 0.6),
                0 1px 0 rgba(255, 255, 255, 0.35) inset,
                0 -2px 0 rgba(0, 0, 0, 0.5) inset,
                0 0 14px rgba(0, 245, 200, 0.12) !important;
            white-space: nowrap;
        }

        .stTabs [data-baseweb="tab"] > div {
            font-size: 20px !important;
            font-weight: 900 !important;
            line-height: 1.3 !important;
        }

        .stTabs [data-baseweb="tab"] img {
            width: 15px;
            height: 15px;
            margin-right: 3px;
        }

        .stTabs [data-baseweb="tab"]:hover {
            filter: brightness(1.3) !important;
            transform: translateY(-1px) !important;
        }

        .stTabs button[role="tab"][aria-selected="true"] {
            transform: translateY(-1px) !important;
            filter: brightness(1.18) !important;
            box-shadow:
                0 4px 16px rgba(0, 0, 0, 0.65),
                0 0 18px rgba(0, 245, 200, 0.35),
                0 1px 0 rgba(255, 255, 255, 0.35) inset,
                0 -2px 0 rgba(0, 0, 0, 0.5) inset !important;
        }

        /* İçerik panelleri hafif kart görünümü */
        .stTabs [data-baseweb="tab-panel"] {
            background: rgba(5, 18, 32, 0.45) !important;
            border: 1px solid rgba(255, 255, 255, 0.08) !important;
            border-radius: 12px !important;
            padding: 1.6rem 1.8rem !important;
            margin-top: 8px;
        }

        .sekme-baslik {
            font-size: 19px !important;
            padding: 10px 14px !important;
        }

        .sekme-baslik .sb-logo {
            font-size: 26px !important;
        }
    }
    </style>
    """,
    unsafe_allow_html=True
)


# ==================================================
# ZİYARETÇİ OTURUM KODU
# ==================================================
def ziyaretci_oturum_kodu():
    """Her ziyaretçi için benzersiz ve kalıcı bir oturum kodu.

    Kod URL'ye (?bta_ziyaretci=...) yazılır ve tarayıcı / cihaz
    bazlı olarak session_state'ta saklanır. Böylece:
      - Aynı ziyaretçi sayfayı her açtığında AYNI kodu alır (kesin takip).
      - Her ziyaretçi kendini BENZERSİZ takip edebilir (çoklu hesap çökmez).
      - Engel / susturma da bu koda göre işlenir.
    """
    PARAM_ADI = "bta_ziyaretci"

    try:
        qp = st.query_params
        if PARAM_ADI not in qp:
            qp[PARAM_ADI] = ...
        _url_kodu = str(qp.get(PARAM_ADI, "") or "").strip()
    except Exception:
        _url_kodu = ""

    if _url_kodu:
        st.session_state["ziyaretci_oturum"] = _url_kodu
        return _url_kodu

    if st.session_state.get("ziyaretci_oturum"):
        try:
            st.query_params[PARAM_ADI] = (
                st.session_state["ziyaretci_oturum"]
            )
        except Exception:
            pass
        return st.session_state["ziyaretci_oturum"]

    _yeni = uuid.uuid4().hex[:12]
    st.session_state["ziyaretci_oturum"] = _yeni
    try:
        st.query_params[PARAM_ADI] = _yeni
    except Exception:
        pass
    return _yeni


def _oturum_istasyonu_olustur():
    """Sohbet sayfası dışında da oturum kodunun hazır olması için
    ilk çalıştırmada üretilip session_state'e yazılır; böylece
    ziyaretci_oturum_kodu() her çağrıldığında aynı kodu döndürür."""
    if "ziyaretci_oturum" not in st.session_state:
        _kod = uuid.uuid4().hex[:12]
        st.session_state["ziyaretci_oturum"] = _kod
        try:
            st.query_params["bta_z"] = _kod
        except Exception:
            pass


def ziyaretci_oturum_kodu():
    """Bu ziyaretçiye özel, kalıcı ve benzersiz oturum kodunu
    döndürür. Kod URL (?bta_z=...) içinde saklanır; tarayıcı
    sekmesinden ayrılıp geri gelinse bile aynı kullanıcı aynı
    kodu alır. Böylece takip etme ve engelleme işlemleri
    'kesin' olur: aynı ziyaretçi kendi oturumuyla tanınır."""
    _oturum_istasyonu_olustur()

    try:
        _url_kodu = st.query_params.get("bta_z", "").strip()
    except Exception:
        _url_kodu = ""

    if _url_kodu:
        st.session_state["ziyaretci_oturum"] = _url_kodu
        return _url_kodu

    _olusan = st.session_state["ziyaretci_oturum"]
    try:
        st.query_params["bta_z"] = _olusan
    except Exception:
        pass
    return _olusan


# ==================================================
# TAKİPÇİ VE ENGELLEME FONKSİYONLARI
# ==================================================
def takipci_oku():
    """Takip eden benzersiz ziyaretçi oturum kodlarını döndürür."""
    try:
        df = pd.read_csv(
            TAKIP_DOSYASI,
            encoding="utf-8-sig"
        )
        if df.empty or "oturum" not in df.columns:
            # Eski tek sütunlu dosyalarda "kullanici" oturum,
            # "kullanici" görünümlüyse geriye dönük uyum.
            if "kullanici" in df.columns:
                return set(
                    str(x).strip()
                    for x in df["kullanici"].dropna()
                    if str(x).strip()
                )
            return set()
        return set(
            str(x).strip()
            for x in df["oturum"].dropna()
            if str(x).strip()
        )
    except Exception:
        return set()


def takipci_sayisi():
    return len(takipci_oku())


def takiptesin_mi(oturum):
    return str(oturum).strip() in takipci_oku()


def takip_birak(oturum):
    oturum = str(oturum).strip()
    if not oturum:
        return False

    try:
        df = pd.read_csv(
            TAKIP_DOSYASI,
            encoding="utf-8-sig"
        )
        if df.empty:
            return False

        kalan = df[
            df["oturum"].astype(str).str.strip()
            != oturum
        ]
        kalan.to_csv(
            TAKIP_DOSYASI,
            index=False,
            encoding="utf-8-sig"
        )
        return True
    except Exception:
        return False


def takip_ekle(oturum=""):
    """Ziyaretçi oturum koduna göre takip işlemini kaydeder.
    Aynı oturum (aynı kişi) defalarca takip edemez; her ziyaretçi
    kendi oturum koduyla yalnızca BİR kez takip eder (kesin takip)."""
    oturum = str(oturum).strip()
    if not oturum:
        return False

    mevcut = takipci_oku()
    if oturum in mevcut:
        return False

    mevcut.add(oturum)
    pd.DataFrame(
        {
            "oturum": sorted(mevcut),
            "kullanici": "",
            "tarih": ""
        }
    ).to_csv(
        TAKIP_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )
    return True


def takip_birak(oturum):
    """Ziyaretçi oturum koduna göre takibi bırakır."""
    oturum = str(oturum).strip()
    if not oturum:
        return False

    mevcut = takipci_oku()
    if oturum not in mevcut:
        return False

    mevcut.discard(oturum)
    pd.DataFrame(
        {
            "oturum": sorted(mevcut),
            "kullanici": "",
            "tarih": ""
        }
    ).to_csv(
        TAKIP_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )
    return True


# ==================================================
# YÖNETİCİYE ÖZEL MESAJ (DM) FONKSİYONLARI
# ==================================================
def yonetici_mesajlarini_oku():
    """Yöneticiye gönderilen özel mesajları (DM) tarih sırasına
    göre döndürür. Bu mesajlar sohbet akışında GÖRÜNMEZ; yalnızca
    yönetici bu dosyadan okuyabilir."""
    try:
        df = pd.read_csv(
            YONETICI_MESAJ_DOSYASI,
            encoding="utf-8-sig"
        )
        if df.empty:
            return pd.DataFrame(
                columns=YONETICI_MESAJ_SUTUNLARI
            )
        return df.sort_values(
            "tarih",
            ascending=False
        )
    except Exception:
        return pd.DataFrame(
            columns=YONETICI_MESAJ_SUTUNLARI
        )


def yonetici_mesaji_sil(mesaj_id):
    """Yönetici okuduktan sonra özel mesajı kalıcı olarak siler."""
    try:
        df = pd.read_csv(
            YONETICI_MESAJ_DOSYASI,
            encoding="utf-8-sig"
        )
        if df.empty:
            return True

        mesaj_id = str(mesaj_id).strip()
        kalan = df[
            df["mesaj_id"].astype(str).str.strip()
            != mesaj_id
        ]
        kalan.to_csv(
            YONETICI_MESAJ_DOSYASI,
            index=False,
            encoding="utf-8-sig"
        )
        return True
    except Exception:
        return False


def yonetici_mesaji_ekle(kullanici, oturum, mesaj):
    """Ziyaretçiden yöneticiye özel mesaj kaydeder. Bu mesaj genel
    sohbet akışına GİRMEZ; yalnızca yönetici okuyabilir."""
    ad = str(kullanici).strip()
    metin = str(mesaj).strip()
    if not ad or not metin:
        return False

    veriler = yonetici_mesajlarini_oku()
    yeni = pd.DataFrame(
        [{
            "mesaj_id": str(
                turkiye_saati().timestamp() * 1000
            ),
            "tarih": turkiye_saati().strftime(
                "%d.%m.%Y %H:%M:%S"
            ),
            "kullanici": ad,
            "oturum": str(oturum).strip(),
            "mesaj": metin
        }]
    )
    veriler = pd.concat(
        [veriler, yeni],
        ignore_index=True
    )
    veriler.to_csv(
        YONETICI_MESAJ_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )
    return True


def istatistik_oku():
    """Geriye dönük uyumluluk: takip sayısını döndürür."""
    return takipci_sayisi()


def engelli_oku():
    """Anahtar (oturum kodu varsa oturum, yoksa kullanıcı adı) ile
    {anahtar: (bitis, tur, ad, oturum)} sözlüğü döndürür.
    bitis None ise kalıcı engel; bitis varsa o an'a kadar susturma.
    Süresi geçenler otomatik temizlenir.
    """
    try:
        df = pd.read_csv(
            ENGEL_DOSYASI,
            encoding="utf-8-sig"
        )

        if df.empty:
            return {}

        sonuc = {}
        simdi = turkiye_saati()
        degisiklik = False

        for _, satir in df.iterrows():
            ad = str(satir.get("kullanici", "") or "").strip()
            os = str(satir.get("oturum", "") or "").strip()
            anahtar = (os or ad).lower()
            if not anahtar:
                continue

            bitis_metin = str(
                satir.get("bitis", "") or ""
            ).strip()
            bitis = None

            if bitis_metin and bitis_metin.lower() != "kalici":
                try:
                    bitis = datetime.strptime(
                        bitis_metin, "%Y-%m-%d %H:%M:%S"
                    )
                except Exception:
                    bitis = None

            tur = str(
                satir.get("tur", "") or ""
            ).strip() or "susturma"

            if bitis is not None and bitis < simdi:
                degisiklik = True
                continue

            sonuc[anahtar] = (bitis, tur, ad or os, os)

        if degisiklik:
            _engelli_kaydet_raw(sonuc)

        return sonuc

    except Exception:
        return {}


def _engelli_kaydet(sonuc):
    """Engelli sözlüğünü dosyaya yazar (temizlikli)."""
    df = pd.DataFrame(
        [
            {
                "oturum": bilgi[3],
                "kullanici": bilgi[2],
                "bitis": (
                    "kalici" if bilgi[0] is None
                    else bilgi[0].strftime("%Y-%m-%d %H:%M:%S")
                ),
                "tur": bilgi[1]
            }
            for bilgi in sonuc.values()
        ]
    )
    df.to_csv(
        ENGEL_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )


def _engelli_kaydet_raw(sonuc):
    """engelli_oku içinden erişilen yardımcı (süresi dolanları
    ayıklar ve dosyayı yeniden yazar)."""
    _engelli_kaydet(sonuc)


def kullanici_engelle(kullanici, gun=0, oturum=""):
    """gun=0 ise kalıcı engel, gun>0 ise o kadar gün susturma.
    Kimlik olarak oturum kodu varsa oturum, yoksa kullanıcı adı
    anahtar olur. kullanici alanı görünen etikettir."""
    ad = str(kullanici).strip()
    os = str(oturum).strip()
    anahtar = (os or ad).lower()

    if not anahtar:
        return False

    sonuc = engelli_oku()

    if gun and gun > 0:
        bitis = turkiye_saati() + timedelta(days=gun)
        sonuc[anahtar] = (bitis, "susturma", ad or os, os)
    else:
        sonuc[anahtar] = (None, "engel", ad or os, os)

    _engelli_kaydet(sonuc)
    return True


def engeli_kaldir(anahtar):
    key = str(anahtar).strip()
    if not key:
        return False

    sonuc = engelli_oku()
    if key.lower() in sonuc:
        del sonuc[key.lower()]

    _engelli_kaydet(sonuc)
    return True


def kullanici_engelli_mi(kullanici):
    """(engelli_mi, aciklama) döndürür."""
    ad = str(kullanici).strip()
    if not ad:
        return False, None

    engelliler = engelli_oku()
    bilgi = engelliler.get(ad.lower())
    if not bilgi:
        return False, None

    bitis, tur, _ = bilgi

    if tur == "engel" or bitis is None:
        return (
            True,
            "🚫 Bu kullanıcı adı kalıcı olarak engellendi. "
            "Yöneticiyle iletişime geçin."
        )

    sure = bitis - turkiye_saati()
    saat = int(sure.total_seconds() // 3600)
    dakika = int((sure.total_seconds() % 3600) // 60)

    return (
        True,
        f"🔇 Bu kullanıcı adı {saat} saat {dakika} dakika "
        "susturulmuş durumda. Lütfen daha sonra tekrar deneyin."
    )


# ==================================================
# MESAJ FONKSİYONLARI
# ==================================================
def mesajlari_oku():
    try:
        df = pd.read_csv(
            MESAJ_DOSYASI,
            encoding="utf-8-sig"
        )

        for sutun in MESAJ_SUTUNLARI:
            if sutun not in df.columns:
                df[sutun] = ""

        return df[MESAJ_SUTUNLARI]

    except Exception:
        return pd.DataFrame(columns=MESAJ_SUTUNLARI)


def _b64_veri_ayikla(data_uri):
    """
    'data:image/...;base64,XXXX' biçimindeki veriyi çözüp
    bytes olarak döndürür. Geçersizse boş bytes döner.
    """
    if not data_uri or "," not in data_uri:
        return b""

    import base64 as _b64

    try:
        return _b64.b64decode(
            data_uri.split(",", 1)[1]
        )
    except Exception:
        return b""


def _resim_thumb(data_bytes, genislik=180):
    """
    Resmi küçük bir önizleme (thumbnail) olarak küçültüp base64
    verisine çevirir. Sohbette resim küçük gösterilir; tıklanınca
    orijinal boyutu yeni sekmede açılır. Bozuk veride orijinali döner.
    """
    try:
        import io
        import base64 as _b64

        with Image.open(io.BytesIO(data_bytes)) as img:
            img = ImageOps.exif_transpose(img)
            img = img.convert("RGB")
            img.thumbnail((genislik, genislik))

            tampon = io.BytesIO()
            img.save(tampon, format="JPEG", quality=70)

            return (
                "data:image/jpeg;base64,"
                + _b64.b64encode(tampon.getvalue()).decode("ascii")
            )
    except Exception:
        return None


def resim_mesaj_verisi(yuklenen_dosya):
    """
    Yüklenen resmi Pillow ile yeniden boyutlandırıp (en fazla 720px,
    JPEG kalite ~82) base64 verisine çevirir. Mesaj CSV'sinde bir
    alan olarak saklanır ve HTML <img> olarak gösterilir.
    Bozuk/aşılamayan dosyalarda (yığın izi) yükseltir.
    """
    with Image.open(yuklenen_dosya) as img:
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGB")

        img.thumbnail((720, 720))

        import io
        import base64 as _b64

        tampon = io.BytesIO()
        img.save(tampon, format="JPEG", quality=82)

        return (
            "data:image/jpeg;base64,"
            + _b64.b64encode(tampon.getvalue()).decode("ascii")
        )


def grafik_resmi_verisi(yuklenen_dosya):
    """
    Analiz notuna eklenecek grafik resmini büyütür (en fazla 1600px)
    ve base64 verisine çevirir; böylece not CSV'sinde saklanıp nota
    tıklanınca açılabilir. Bozuk dosyada yükseltir.
    """
    with Image.open(yuklenen_dosya) as img:
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGB")

        img.thumbnail((1600, 1600))

        import io
        import base64 as _b64

        tampon = io.BytesIO()
        img.save(tampon, format="JPEG", quality=88)

        return (
            "data:image/jpeg;base64,"
            + _b64.b64encode(tampon.getvalue()).decode("ascii")
        )


def _veri_url_bytes(veri_url):
    """data:image/...;base64,XXXX -> ham baytları döndürür."""
    try:
        import base64 as _b64

        return _b64.b64decode(
            str(veri_url).split(",", 1)[1]
        )
    except Exception:
        return None


def mesaj_ekle(kullanici, metin, resim="", oturum=""):
    mesajlar = mesajlari_oku()
    _oturum_son = str(oturum).strip()

    yeni_mesaj = pd.DataFrame(
        [{
            "mesaj_id": int(
                turkiye_saati().timestamp() * 1000
            ),
            "tarih": turkiye_saati().strftime(
                "%d.%m.%Y %H:%M:%S"
            ),
            "kullanici": kullanici,
            "mesaj": metin,
            "resim": resim,
            "oturum": _oturum_son
        }]
    )

    mesajlar = pd.concat(
        [
            mesajlar,
            yeni_mesaj
        ],
        ignore_index=True
    )

    mesajlar.to_csv(
        MESAJ_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )


def analiz_notlari_oku():
    try:
        df = pd.read_csv(
            NOT_DOSYASI,
            encoding="utf-8-sig"
        )

        for sutun in NOT_SUTUNLARI:
            if sutun not in df.columns:
                df[sutun] = ""

        return df[NOT_SUTUNLARI]
    except Exception:
        return pd.DataFrame(columns=NOT_SUTUNLARI)


def analiz_notu_ekle(kullanici, sembol, not_metni, resim=""):
    notlar = analiz_notlari_oku()

    yeni_not = pd.DataFrame(
        [{
            "not_id": int(
                turkiye_saati().timestamp() * 1000
            ),
            "tarih": turkiye_saati().strftime(
                "%d.%m.%Y %H:%M:%S"
            ),
            "kullanici": kullanici,
            "sembol": sembol,
            "not_metni": not_metni,
            "resim": resim
        }]
    )

    for _sutun in NOT_SUTUNLARI:
        if _sutun not in notlar.columns:
            notlar[_sutun] = ""

    notlar = pd.concat(
        [
            notlar[NOT_SUTUNLARI],
            yeni_not[NOT_SUTUNLARI]
        ],
        ignore_index=True
    )

    notlar.to_csv(
        NOT_DOSYASI,
        index=False,
        encoding="utf-8-sig"
    )


def analiz_notu_sil(not_id):
    """Yönetici bir analiz notunu kalıcı olarak siler."""
    try:
        df = analiz_notlari_oku()

        if df.empty:
            return True

        not_id = str(not_id).strip()

        kalan = df[
            df["not_id"].astype(str).str.strip() != not_id
        ]

        kalan.to_csv(
            NOT_DOSYASI,
            index=False,
            encoding="utf-8-sig"
        )

        return True
    except Exception:
        return False


def analiz_notlari_tumunu_sil():
    """Yönetici tüm analiz notlarını kalıcı olarak siler."""
    try:
        pd.DataFrame(
            columns=NOT_SUTUNLARI
        ).to_csv(
            NOT_DOSYASI,
            index=False,
            encoding="utf-8-sig"
        )

        return True
    except Exception:
        return False


# ==================================================
# PAYLAŞIM FONKSİYONLARI
# ==================================================
def paylas_linki_olustur(platform, url, baslik):
    """
    Farklı platformlar için paylaşım linki oluşturur
    """
    encoded_url = urllib.parse.quote(url)
    encoded_baslik = urllib.parse.quote(baslik)
    
    linkler = {
        "twitter": f"https://twitter.com/intent/tweet?url={encoded_url}&text={encoded_baslik}",
        "facebook": f"https://www.facebook.com/sharer/sharer.php?u={encoded_url}",
        "linkedin": f"https://www.linkedin.com/sharing/share-offsite/?url={encoded_url}",
        "whatsapp": f"https://wa.me/?text={encoded_baslik}%0A{encoded_url}",
        "telegram": f"https://t.me/share/url?url={encoded_url}&text={encoded_baslik}",
        "email": f"mailto:?subject={encoded_baslik}&body={encoded_url}"
    }
    
    return linkler.get(platform, "#")


# ==================================================
# MESAJ DENETİMİ (KÜFÜR / HAKARET / YATIRIM TELKİNİ)
# ==================================================
# Küfür, hakaret ve argo kelimeler ile yatırım yönlendirmesi
# (AL / SAT / TUT) içeren kelimeler engellenir.
KUFUR_KOKLERI = [
    "amk", "aq", "oç", "orospu", "siktir", "sikeyim", "sikik",
    "pezevenk", "piç", "yavşak", "şerefsiz", "göt", "bok",
    "salak", "aptal", "gerizekalı", "hain", "kahpe", "sürtük",
    "amına", "ananı", "avradı"
]

# İçinde küfür kökü geçen ama masum olan kelimeler (ör. "götür"
# kelimesi "göt" köküyle başlar). Bunlar engellenmez.
KUFUR_ISTISNALARI = [
    "götür", "götüre", "götürü", "boks", "bokser", "boksu"
]

YATIRIM_TELKIN_KELIMELERI = [
    "al", "sat", "tut",
    "alın", "satın", "tutun",
    "alınız", "satınız", "tutunuz"
]


def _tam_kelime_geciyor(metin_kucuk, kelime):
    """
    Kelimeyi yalnızca bağımsız bir sözcük olarak arar. Böylece 'al'
    kelimesi 'aldım', 'sat' kelimesi 'satış' gibi kelimelerin içinde
    yanlışlıkla yakalanmaz (Türkçe harfler de sözcük parçası sayılır).
    """
    desen = (
        r"(?<![a-zçğıöşü0-9])"
        + re.escape(kelime)
        + r"(?![a-zçğıöşü0-9])"
    )
    return re.search(desen, metin_kucuk) is not None


def _kufur_var_mi(metin_kucuk):
    """
    Metni kelimelere ayırıp her kelimede küfür kökü arar; böylece
    'boktan' gibi ek almış küfürler de yakalanır. Masum kelimeler
    (ör. 'götür') istisna listesiyle korunur.
    """
    kelimeler = re.findall(r"[a-zçğıöşü0-9]+", metin_kucuk)

    for kelime in kelimeler:
        if any(
            kelime.startswith(istisna)
            for istisna in KUFUR_ISTISNALARI
        ):
            continue

        for kok in KUFUR_KOKLERI:
            if kok in kelime:
                return True

    return False


def mesaj_yasakli_mi(metin):
    """
    Mesajda küfür/hakaret veya yatırım telkini (AL/SAT/TUT) varsa
    (True, kullanıcıya_gösterilecek_uyari) döndürür; yoksa
    (False, None) döndürür.
    """
    metin_kucuk = str(metin).lower()

    if _kufur_var_mi(metin_kucuk):
        return (
            True,
            "Mesajınız gönderilemedi: Küfür, hakaret veya argo "
            "içeren ifadeler kullanılamaz."
        )

    for kelime in YATIRIM_TELKIN_KELIMELERI:
        if _tam_kelime_geciyor(metin_kucuk, kelime):
            return (
                True,
                "Mesajınız gönderilemedi: AL / SAT / TUT gibi "
                "yatırım yönlendirmesi (al-sat tavsiyesi) içeren "
                "ifadeler kullanılamaz."
            )

    return False, None


# ==================================================
# MESAJ SESİ
# ==================================================
def mesaj_sesi_cal():
    # Her çağrıda benzersiz bir damga üretilir. Streamlit, birebir
    # aynı içerikli bir components.html'i yeniden ÇALIŞTIRMADIĞI için
    # (özellikle st.fragment içinde tekrar tekrar render edilirken),
    # içerik değişmezse iframe yeniden yüklenmez ve bildirim sesi bir
    # daha çalmaz. Damga sayesinde içerik her seferinde değişir,
    # iframe yenilenir ve ses her yeni mesajda çalar.
    _damga = int(turkiye_saati().timestamp() * 1000)

    components.html(
        f"""
        <script>
        // ses-damga: {_damga}
        try {{
            const audioContext = new (
                window.AudioContext ||
                window.webkitAudioContext
            )();

            if (audioContext.state === "suspended") {{
                audioContext.resume();
            }}

            const oscillator = audioContext.createOscillator();
            const gainNode = audioContext.createGain();

            oscillator.type = "sine";
            oscillator.frequency.setValueAtTime(
                880,
                audioContext.currentTime
            );

            gainNode.gain.setValueAtTime(
                0.0001,
                audioContext.currentTime
            );

            gainNode.gain.exponentialRampToValueAtTime(
                0.18,
                audioContext.currentTime + 0.02
            );

            gainNode.gain.exponentialRampToValueAtTime(
                0.0001,
                audioContext.currentTime + 0.35
            );

            oscillator.connect(gainNode);
            gainNode.connect(audioContext.destination);

            oscillator.start();
            oscillator.stop(audioContext.currentTime + 0.35);
        }} catch (error) {{
            console.log("Bildirim sesi oynatılamadı:", error);
        }}
        </script>
        """,
        height=0,
        width=0
    )


# ==================================================
# CANLI YENİLEME
# ==================================================
# Not: Sayfa geneli otomatik yenileme (eski st_autorefresh) KALDIRILDI.
# Artık yalnızca canlı bölümler (piyasa kartı, günlük liste, sohbet)
# st.fragment(run_every=...) ile ARKA PLANDA tazelenir; böylece
# sayfanın baştan çizilmesinden (ekranın sönüp yenilenmesinden)
# kaçınılır. Statik içerik (logo, sekmeler, formlar) yerinde kalır.


# ==================================================
# LOGO
# ==================================================
_bta_logo_svg = (
    '<svg class="bta-logo-ikon" viewBox="0 0 64 64" '
    'xmlns="http://www.w3.org/2000/svg" fill="none" '
    'stroke="currentColor" stroke-width="2.4" stroke-linecap="round">'
    '<line x1="12" y1="48" x2="24" y2="30" />'
    '<line x1="24" y1="30" x2="36" y2="38" />'
    '<line x1="36" y1="38" x2="52" y2="14" />'
    '<line x1="12" y1="48" x2="52" y2="48" />'
    '<circle cx="12" cy="48" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="24" cy="30" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="36" cy="38" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="52" cy="14" r="4.6" fill="currentColor" stroke="none" />'
    '</svg>'
)

_bta_logo_kucuk_svg = (
    '<svg style="width:20px;height:20px;vertical-align:middle;" '
    'viewBox="0 0 64 64" xmlns="http://www.w3.org/2000/svg" '
    'fill="none" stroke="currentColor" stroke-width="3" '
    'stroke-linecap="round">'
    '<line x1="12" y1="48" x2="24" y2="30" />'
    '<line x1="24" y1="30" x2="36" y2="38" />'
    '<line x1="36" y1="38" x2="52" y2="14" />'
    '<line x1="12" y1="48" x2="52" y2="48" />'
    '<circle cx="12" cy="48" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="24" cy="30" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="36" cy="38" r="4.6" fill="currentColor" stroke="none" />'
    '<circle cx="52" cy="14" r="4.6" fill="currentColor" stroke="none" />'
    '</svg>'
)

# Tab etiketlerinde güvenle kullanılabilecek sabit renkli,
# base64 gömülü BTA logosu (özel karakter içermez).
_bta_logo_b64 = (
    "PHN2ZyB2aWV3Qm94PSIwIDAgNjQgNjQiIHhtbG5zPSJodHRwOi8vd3d3Lncz"
    "Lm9yZy8yMDAwL3N2ZyIgZmlsbD0ibm9uZSIgc3Ryb2tlPSIjMDBmNWM4IiBz"
    "dHJva2Utd2lkdGg9IjQiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCI+PGxpbmUg"
    "eDE9IjEyIiB5MT0iNDgiIHgyPSIyNCIgeTI9IjMwIi8+PGxpbmUgeDE9IjI0"
    "IiB5MT0iMzAiIHgyPSIzNiIgeTI9IjM4Ii8+PGxpbmUgeDE9IjM2IiB5MT0i"
    "MzgiIHgyPSI1MiIgeTI9IjE0Ii8+PGxpbmUgeDE9IjEyIiB5MT0iNDgiIHgy"
    "PSI1MiIgeTI9IjQ4Ii8+PGNpcmNsZSBjeD0iMTIiIGN5PSI0OCIgcj0iNC42"
    "IiBmaWxsPSIjMDBmNWM4IiBzdHJva2U9Im5vbmUiLz48Y2lyY2xlIGN4PSIy"
    "NCIgY3k9IjMwIiByPSI0LjYiIGZpbGw9IiMwMGY1YzgiIHN0cm9rZT0ibm9u"
    "ZSIvPjxjaXJjbGUgY3g9IjM2IiBjeT0iMzgiIHI9IjQuNiIgZmlsbD0iIzAw"
    "ZjVjOCIgc3Ryb2tlPSJub25lIi8+PGNpcmNsZSBjeD0iNTIiIGN5PSIxNCIg"
    "cj0iNC42IiBmaWxsPSIjMDBmNWM4IiBzdHJva2U9Im5vbmUiLz48L3N2Zz4="
)

# ==================================================
# CANLI PİYASA KULİSİ (ÜST ŞERİT) + EKONOMİ/SEKME CSS
# ==================================================
_BTA_EKSTRA_CSS = """
/* ==================================================
   HAREKETLİ ARKA PLAN (yavaş akan koyu lacivert ışık)
   ================================================== */
.stApp,
[data-testid="stAppViewContainer"] {
    background-color: #0c1730;
    background-image:
        radial-gradient(circle at 18% 22%, rgba(64, 108, 180, 0.16), transparent 45%),
        radial-gradient(circle at 82% 12%, rgba(38, 74, 140, 0.14), transparent 45%),
        radial-gradient(circle at 60% 88%, rgba(70, 118, 200, 0.12), transparent 50%),
        repeating-linear-gradient(0deg, rgba(255, 255, 255, 0.022) 0 1px, transparent 1px 44px),
        repeating-linear-gradient(90deg, rgba(255, 255, 255, 0.022) 0 1px, transparent 1px 44px);
    background-size: 180% 180%, 200% 200%, 220% 220%, auto, auto;
    background-repeat: no-repeat;
    background-attachment: fixed;
    animation: btaArkaPlan 30s ease-in-out infinite alternate;
}
@keyframes btaArkaPlan {
    0% {
        background-position: 0% 0%, 100% 0%, 50% 100%, 0 0, 0 0;
    }
    50% {
        background-position: 45% 35%, 55% 25%, 40% 70%, 0 0, 0 0;
    }
    100% {
        background-position: 85% 20%, 20% 45%, 65% 30%, 0 0, 0 0;
    }
}
@media (prefers-reduced-motion: reduce) {
    .stApp,
    [data-testid="stAppViewContainer"] {
        animation: none;
    }
}

/* Parçacık ağı + radar dalgaları: içerik canvas'ın üstünde kalsın */
#bta-arka-canvas {
    position: fixed;
    left: 0;
    top: 0;
    width: 100%;
    height: 100%;
    z-index: 0;
    pointer-events: none;
    opacity: 0.6;
}
[data-testid="stMain"],
section.main,
[data-testid="stAppViewContainer"] > section {
    position: relative;
    z-index: 1;
}

.piyasa-kulisi {
    background: linear-gradient(90deg, rgba(3, 22, 38, 0.98), rgba(4, 44, 66, 0.98));
    border: 1px solid rgba(0, 245, 200, 0.55);
    border-radius: 10px;
    overflow: hidden;
    margin: 4px 0 2px 0;
    box-shadow: 0 4px 18px rgba(0, 0, 0, 0.5), 0 0 16px rgba(0, 245, 200, 0.16);
}
.piyasa-kulisi-iz {
    display: inline-flex;
    align-items: center;
    white-space: nowrap;
    animation: pk-kaydir 88s linear infinite;
    will-change: transform;
}
.piyasa-kulisi:hover .piyasa-kulisi-iz {
    animation-play-state: paused;
}
.pk-item {
    display: inline-flex;
    align-items: center;
    gap: 10px;
    padding: 12px 22px;
    font-family: "Consolas", "SFMono-Regular", monospace;
    font-size: 23px;
}
.pk-isim {
    font-weight: 900;
    color: #00f5c8;
    letter-spacing: 0.5px;
    text-shadow:
        -1px -1px 0 rgba(0, 0, 0, 0.9),
        1px 1px 0 rgba(255, 255, 255, 0.3),
        0 0 12px rgba(0, 245, 200, 0.55);
}
.pk-fiyat {
    font-weight: 900;
    color: #eafffb;
    text-shadow:
        -1px -1px 0 rgba(0, 0, 0, 0.9),
        1px 1px 0 rgba(255, 255, 255, 0.3),
        0 0 10px rgba(22, 140, 255, 0.4);
}
.pk-deg {
    font-weight: 900;
    text-shadow:
        -1px -1px 0 rgba(0, 0, 0, 0.9),
        1px 1px 0 rgba(255, 255, 255, 0.25);
}
.pk-ayrac {
    color: rgba(255, 255, 255, 0.35);
    font-size: 15px;
    margin-left: -6px;
}
@keyframes pk-kaydir {
    0% { transform: translateX(0); }
    100% { transform: translateX(-50%); }
}

/* ==================================================
   BTA TABELA: NEON BAŞLIK + CANLI ŞERİT + IŞIK SÜZÜLMESİ
   ================================================== */
.bta-logo-alani {
    position: relative;
    display: flex;
    justify-content: center;
    align-items: center;
    margin: 10px 0 24px 0;
    padding: 14px 18px;
    border-radius: 16px;
    background:
        radial-gradient(circle at 50% 0%, rgba(0, 245, 200, 0.16), transparent 62%),
        linear-gradient(120deg, rgba(3, 20, 34, 0.96), rgba(4, 40, 60, 0.96));
    border: 1px solid rgba(0, 245, 200, 0.5);
    box-shadow:
        0 0 0 1px rgba(0, 245, 200, 0.12) inset,
        0 8px 30px rgba(0, 0, 0, 0.55),
        0 0 26px rgba(0, 245, 200, 0.25);
    overflow: hidden;
}
.bta-logo-alani::after {
    content: "";
    position: absolute;
    left: 12%;
    right: 12%;
    bottom: 0;
    height: 2px;
    background: linear-gradient(90deg, transparent, #00f5c8, transparent);
    box-shadow: 0 0 12px rgba(0, 245, 200, 0.9);
    pointer-events: none;
}
.bta-logo {
    position: relative;
    z-index: 1;
}
.bta-logo-metin {
    font-family: 'Plus Jakarta Sans', 'Segoe UI', sans-serif;
    font-weight: 900;
    font-size: clamp(22px, 4vw, 38px);
    letter-spacing: 1.5px;
    background: linear-gradient(90deg, #00f5c8, #4da6ff, #00f5c8);
    background-size: 200% auto;
    -webkit-background-clip: text;
    background-clip: text;
    -webkit-text-fill-color: transparent;
    animation: none;
    filter: drop-shadow(0 0 12px rgba(0, 245, 200, 0.5));
    text-shadow: none !important;
}
@keyframes btaUgla {
    0% { background-position: 0% center; }
    100% { background-position: 200% center; }
}
@keyframes btaBaslikNeon {
    0%, 100% { filter: drop-shadow(0 0 8px rgba(0, 245, 200, 0.35)); }
    50% { filter: drop-shadow(0 0 24px rgba(0, 245, 200, 0.95)); }
}

/* CANLI ROZET + ŞERİT DÜZENİ */
.bta-serif-wrap {
    display: flex;
    align-items: stretch;
    gap: 8px;
    margin: 6px 0 2px 0;
}
.bta-serif-wrap .piyasa-kulisi {
    flex: 1;
    min-width: 0;
    margin: 0;
}
.piyasa-kulisi {
    position: relative;
    -webkit-mask-image: linear-gradient(90deg, transparent 0,
        #000 42px, #000 calc(100% - 42px), transparent 100%);
    mask-image: linear-gradient(90deg, transparent 0,
        #000 42px, #000 calc(100% - 42px), transparent 100%);
}

/* SEKME ÇUBUĞU: İKİ YANA, ALTA DOĞRU + BÜYÜK KABARTMALI YAZI */
[data-testid="stTabs"] [data-baseweb="tab-list"],
div[role="tablist"],
[data-baseweb="tab-list"] {
    display: grid !important;
    grid-template-columns: repeat(2, minmax(0, 1fr)) !important;
    align-items: stretch !important;
    gap: 8px !important;
    overflow-x: hidden !important;
    overflow-y: auto !important;
}
[data-testid="stTabs"] [role="tab"],
[data-testid="stTabs"] [data-baseweb="tab"],
.stTabs [role="tab"],
[role="tab"],
[data-baseweb="tab"] {
    width: 100% !important;
    justify-content: center !important;
    text-align: center !important;
    font-size: 34px !important;
    font-weight: 900 !important;
    letter-spacing: 0.4px !important;
    padding: 13px 16px !important;
    border-radius: 10px !important;
    white-space: normal !important;
    color: #ffffff !important;
    text-shadow:
        -1px -1px 0 rgba(255, 255, 255, 0.7),
        -2px -2px 0 rgba(255, 255, 255, 0.3),
        3px 3px 0 rgba(0, 0, 0, 0.95),
        2px 2px 0 rgba(0, 0, 0, 0.85),
        0 0 30px rgba(0, 245, 200, 1.0) !important;
}
[data-testid="stTabs"] [role="tab"] > div,
[data-testid="stTabs"] [role="tab"] > span,
[data-testid="stTabs"] [role="tab"] div,
[data-testid="stTabs"] [role="tab"] span,
[data-testid="stTabs"] [role="tab"] *,
[data-testid="stTabs"] [data-baseweb="tab"] > div,
[data-testid="stTabs"] [data-baseweb="tab"] div,
[data-testid="stTabs"] [data-baseweb="tab"] span,
[role="tab"] > div,
[role="tab"] div,
[role="tab"] span,
[role="tab"] *,
[data-baseweb="tab"] > div,
[data-baseweb="tab"] div,
[data-baseweb="tab"] span {
    font-size: 34px !important;
    font-weight: 900 !important;
    line-height: 1.25 !important;
    text-align: center !important;
    color: #ffffff !important;
    text-shadow:
        -1px -1px 0 rgba(255, 255, 255, 0.7),
        -2px -2px 0 rgba(255, 255, 255, 0.3),
        3px 3px 0 rgba(0, 0, 0, 0.95),
        2px 2px 0 rgba(0, 0, 0, 0.85),
        0 0 30px rgba(0, 245, 200, 1.0) !important;
}
[data-testid="stTabs"] [role="tab"] img,
[data-testid="stTabs"] [data-baseweb="tab"] img,
[role="tab"] img {
    width: 18px;
    height: 18px;
    margin-right: 5px;
}
[data-testid="stTabs"] [role="tab"]:hover,
.stTabs [role="tab"]:hover,
[role="tab"]:hover,
[data-testid="stTabs"] [role="tab"]:active,
[data-testid="stTabs"] [role="tab"]:focus {
    color: #ff4b4b !important;
    transform: translateY(-2px) scale(1.05) !important;
    filter: brightness(1.25) !important;
    transition: transform 0.15s ease !important;
}
/* ANA SAYFA (BTA) SEKMESİ SABİT: tıklama/hover kırmızı yakmaz */
[data-testid="stTabs"] [role="tab"]:first-child,
[data-testid="stTabs"] [role="tab"]:first-child *,
[data-testid="stTabs"] [role="tab"]:first-child:hover,
[data-testid="stTabs"] [role="tab"]:first-child:hover *,
[data-testid="stTabs"] [role="tab"]:first-child:active,
[data-testid="stTabs"] [role="tab"]:first-child:active *,
[data-testid="stTabs"] [role="tab"]:first-child:focus,
[data-testid="stTabs"] [role="tab"]:first-child:focus *,
[data-testid="stTabs"] [data-testid="stTab"]:first-child,
[data-testid="stTabs"] [data-testid="stTab"]:first-child * {
    color: #ffffff !important;
    transform: none !important;
    filter: none !important;
    transition: none !important;
}
[data-testid="stTabs"] [role="tab"][aria-selected="true"],
[data-testid="stTabs"] [data-baseweb="tab"][aria-selected="true"],
.stTabs [role="tab"][aria-selected="true"],
[role="tab"][aria-selected="true"],
[data-baseweb="tab"][aria-selected="true"] {
    border-bottom: none !important;
    border-bottom-color: transparent !important;
}
[data-testid="stTabs"] [role="tab"][aria-selected="true"]::after,
[data-testid="stTabs"] [role="tab"][aria-selected="true"]::before,
[role="tab"][aria-selected="true"]::after,
[role="tab"][aria-selected="true"]::before {
    display: none !important;
}
.stTabs [role="tab"] .react-aria-SelectionIndicator,
[data-testid="stTabs"] [role="tab"] .react-aria-SelectionIndicator,
[data-testid="stTabs"] [data-testid="stTab"] .react-aria-SelectionIndicator,
[role="tab"] .react-aria-SelectionIndicator,
.react-aria-SelectionIndicator {
    display: none !important;
    height: 0 !important;
    background-color: transparent !important;
}
.stTabs [role="tablist"]::after,
[data-testid="stTabs"] [role="tablist"]::after,
[role="tablist"]::after {
    display: none !important;
}
.stTabs [role="tab"][data-selected],
[data-testid="stTabs"] [role="tab"][data-selected],
.stTabs [data-testid="stTab"][data-selected],
[data-testid="stTabs"] [data-testid="stTab"][data-selected] {
    color: #ffffff !important;
}
.stTabs [role="tab"][data-hovered],
[data-testid="stTabs"] [role="tab"][data-hovered],
.stTabs [data-testid="stTab"][data-hovered],
[data-testid="stTabs"] [role="tab"]:hover,
[data-testid="stTabs"] [data-testid="stTab"]:hover {
    color: #ff4b4b !important;
}

@media screen and (max-width: 700px) {
    .pk-item { font-size: 16px; padding: 6px 14px; }
    [data-testid="stCustomComponentV1"] iframe,
    [data-testid="stCustomComponentV1"],
    [data-testid="stCustomComponent"] iframe,
    [data-testid="stCustomComponent"] {
        height: 44px !important;
    }

    .bta-logo-alani {
        padding: 4px 10px !important;
        border-radius: 12px !important;
        margin: 6px 0 28px 0 !important;
    }
    .bta-serif-wrap { gap: 6px; margin: 0; }
    .sekme-baslik {
        font-size: 17px !important;
        padding: 10px 12px !important;
        gap: 8px !important;
    }
    .sekme-baslik .sb-logo {
        font-size: 22px !important;
    }
    .sekme-baslik .sb-logo svg {
        width: 20px !important;
        height: 20px !important;
        vertical-align: middle !important;
    }
    .sekme-baslik .sekme-baslik-tarih {
        font-size: 11px !important;
    }
    [data-testid="stTabs"] [class*="react-aria-Tabs"] {
        display: flex !important;
        flex-direction: column-reverse !important;
    }
    [data-testid="stTabs"] [data-baseweb="tab-list"],
    [data-testid="stTabs"] [role="tablist"],
    div[role="tablist"],
    [data-baseweb="tab-list"] {
        display: grid !important;
        grid-template-columns: 1fr !important;
        align-items: stretch !important;
        gap: clamp(10px, 3vw, 18px) !important;
        padding: 8px !important;
        overflow: visible !important;
    }
    [data-testid="stTabs"] [role="tab"],
    [data-testid="stTabs"] [data-baseweb="tab"],
    [role="tab"],
    [data-baseweb="tab"],
    [role="tab"] > div,
    [role="tab"] div,
    [role="tab"] span,
    [data-testid="stTabs"] [role="tab"] div,
    [data-testid="stTabs"] [role="tab"] span {
        font-size: clamp(15px, 4.8vw, 24px) !important;
        font-weight: 900 !important;
        line-height: 1.45 !important;
        letter-spacing: 0.4px !important;
        padding: 8px 6px 10px !important;
        margin: 0 !important;
        width: 100% !important;
        white-space: normal !important;
        text-align: left !important;
        justify-content: flex-start !important;
        text-shadow:
            -1px -1px 0 rgba(255, 255, 255, 0.35),
            1px 1px 0 rgba(0, 0, 0, 0.95),
            0 0 12px rgba(0, 245, 200, 0.45) !important;
    }
    [data-testid="stTabs"] [role="tab"] *,
    [data-testid="stTabs"] [data-baseweb="tab"] *,
    [role="tab"] *,
    [data-baseweb="tab"] * {
        font-size: clamp(15px, 4.8vw, 24px) !important;
        font-weight: 900 !important;
        line-height: 1.45 !important;
        letter-spacing: 0.4px !important;
        white-space: normal !important;
        text-align: left !important;
        text-shadow:
            -1px -1px 0 rgba(255, 255, 255, 0.35),
            1px 1px 0 rgba(0, 0, 0, 0.95),
            0 0 12px rgba(0, 245, 200, 0.45) !important;
    }
    [data-testid="stTabs"] [role="tab"],
    [data-testid="stTabs"] [role="tab"] *,
    [role="tab"],
    [role="tab"] *,
    [data-testid="stTabs"] [data-testid="stTab"],
    [data-testid="stTabs"] [data-baseweb="tab"] {
        color: #cfe3ee !important;
    }
    [data-testid="stTabs"] [role="tab"][data-selected],
    [data-testid="stTabs"] [role="tab"][data-selected] *,
    [data-testid="stTabs"] [data-testid="stTab"][data-selected],
    [data-testid="stTabs"] [data-testid="stTab"][data-selected] *,
    .stTabs [role="tab"][data-selected],
    .stTabs [role="tab"][data-selected] * {
        color: #ffffff !important;
        text-shadow:
            -1px -1px 0 rgba(255, 255, 255, 0.5),
            -2px -2px 0 rgba(255, 255, 255, 0.18),
            2px 2px 0 rgba(0, 0, 0, 0.95),
            0 0 18px rgba(0, 245, 200, 0.85) !important;
    }
    [data-testid="stTabs"] [role="tab"]:hover,
    [data-testid="stTabs"] [role="tab"]:hover *,
    [data-testid="stTabs"] [data-testid="stTab"]:hover,
    [data-testid="stTabs"] [data-testid="stTab"]:hover * {
        color: #ff4b4b !important;
    }
    [data-testid="stTabs"] [role="tab"]:first-child,
    [data-testid="stTabs"] [role="tab"]:first-child *,
    [data-testid="stTabs"] [role="tab"]:nth-of-type(1),
    [data-testid="stTabs"] [role="tab"]:nth-of-type(1) *,
    [data-testid="stTabs"] [data-testid="stTab"]:first-child,
    [data-testid="stTabs"] [data-testid="stTab"]:first-child * {
        justify-content: center !important;
        text-align: center !important;
    }
    /* BTA AL SAT kartları: dar ekranda sütunlar sıkışır,
       yüzde "+10,00%" satır dışında kalmaz, hiza korunur. */
    .bta-alsat-kart {
        grid-template-columns:
            minmax(42px, 0.7fr)
            minmax(58px, 1fr)
            minmax(64px, 0.95fr)
            auto !important;
        column-gap: 5px !important;
        padding: 9px 2px !important;
    }
    .bta-kart-isim {
        font-size: 15px !important;
        letter-spacing: 0.3px !important;
    }
    .bta-kart-fiyat {
        font-size: 17px !important;
    }
    .bta-kart-deg {
        font-size: 15px !important;
    }
    .bta-kart-rozet {
        margin-left: 4px !important;
    }
    .bta-kart-rozet * {
        font-size: 10px !important;
    }
}

/* ==================================================
   PANELLER: KOYU LACİVERT
   ================================================== */
[data-testid="stVerticalBlockBorderWrapper"],
div[data-testid="stVerticalBlockBorderWrapper"] {
    background: linear-gradient(140deg, #0c1930 0%, #16233f 100%);
    border: 1px solid #2a3f66 !important;
    border-radius: 12px;
    box-shadow: 0 6px 22px rgba(0, 0, 0, 0.5);
}
#bta-alarm-bilgi {
    background: linear-gradient(140deg, #0c1930 0%, #16233f 100%);
    border: 1px solid #2a3f66;
    border-radius: 12px;
    padding: 14px 18px;
    margin: 6px 0 14px 0;
    color: #dbe7f5;
    box-shadow: 0 6px 20px rgba(0, 0, 0, 0.45);
}
#bta-alarm-bilgi b { color: #7ec3ff; }

/* ===== BİLDİRİM SİSTEMİ ===== */
.bta-notif-kutu {
    background: linear-gradient(140deg, #0c1930 0%, #16233f 100%);
    border: 1px solid #2a3f66;
    border-radius: 10px;
    padding: 8px 12px;
    margin: 6px 0;
    color: #dbe7f5;
    font-size: 13px;
}
.bta-yeni-rozet {
    display: inline-block;
    margin-right: 6px;
    padding: 1px 8px;
    border-radius: 10px;
    font-size: 11px;
    font-weight: 700;
    color: #0c1730;
    background: linear-gradient(90deg, #ffd166, #ff9f43);
    box-shadow: 0 0 10px rgba(255, 209, 102, 0.6);
    animation: btaPuls 1.6s infinite;
}
@keyframes btaPuls {
    0%, 100% { opacity: 1; transform: scale(1); }
    50% { opacity: 0.75; transform: scale(1.05); }
}
.bta-veri-bar {
    width: 100%;
    height: 14px;
    background: rgba(255, 255, 255, 0.08);
    border-radius: 7px;
    overflow: hidden;
    margin: 3px 0 8px 0;
}
.bta-veri-bar-dolgu {
    height: 100%;
    border-radius: 7px;
    background: linear-gradient(90deg, #4da6ff, #00f5c8);
}
.bta-veri-bar-kirmizi {
    height: 100%;
    border-radius: 7px;
    background: linear-gradient(90deg, #ff9f43, #ff5264);
}

/* ===== EKRANDA "YENİ HABER" SİNYALİ ===== */
.bta-yeni-sinyal {
    position: fixed;
    top: 76px;
    left: 50%;
    transform: translateX(-50%);
    z-index: 100003;
    display: inline-flex;
    align-items: center;
    gap: 10px;
    padding: 10px 18px;
    border-radius: 30px;
    font-size: 18px;
    font-weight: 800;
    color: #0a1122;
    background: linear-gradient(90deg, #ffd166, #ff9f43);
    box-shadow: 0 4px 18px rgba(255, 159, 67, 0.55);
    cursor: pointer;
    text-decoration: none;
    border: 1px solid rgba(255, 255, 255, 0.65);
    animation: btaPuls 1.5s infinite;
    max-width: 460px;
    line-height: 1.25;
}
.bta-yeni-sinyal:hover {
    transform: translateX(-50%) scale(1.05);
    color: #0a1122;
    text-decoration: none;
    border-color: #ffffff;
}
.bta-yeni-sinyal .nokta {
    width: 12px;
    height: 12px;
    border-radius: 50%;
    background: #ff2d3b;
    box-shadow: 0 0 10px rgba(255, 45, 59, 0.9);
    animation: btaPuls 0.9s infinite;
    flex: 0 0 auto;
}
.bta-yeni-sinyal .bta-sinyal-metin {
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
}
@media screen and (max-width: 700px) {
    .bta-yeni-sinyal {
        top: 70px;
        left: 50%;
        transform: translateX(-50%);
        font-size: 16px;
        padding: 8px 14px;
        max-width: 300px;
        z-index: 100003;
    }
}

/* ===== TIKLA-AÇILIR PANELER (HABERLER / ARAÇLAR / DİĞER) ===== */
[data-testid="stExpander"] details { border: none; }
[data-testid="stExpander"] {
    margin: -1rem 0 0 0 !important;
}
[data-testid="stExpander"] summary {
    background: linear-gradient(140deg, #0c1930 0%, #16233f 100%);
    border: 1px solid #2a3f66;
    border-radius: 10px;
    padding: 6px 12px;
    font-weight: 700 !important;
    color: #dbe7f5 !important;
    box-shadow: 0 4px 14px rgba(0, 0, 0, 0.45);
}
[data-testid="stExpander"] summary:hover {
    border-color: #4da6ff;
    box-shadow: 0 0 14px rgba(77, 166, 255, 0.35);
}
"""

st.markdown(
    f"<style>{_BTA_EKSTRA_CSS}</style>",
    unsafe_allow_html=True
)


def _canli_satir_hazirla(_fiyat, _degisim, _tur):
    if _fiyat is None:
        return "-", "--%", "#8aa7bb"
    _deger = (
        tl_format(_fiyat) if _tur == "tl" else sayi_format(_fiyat)
    )
    if _degisim is None:
        return _deger, "• --%", "#f2f2f2"
    _ok = "▲" if _degisim >= 0 else "▼"
    _metin = f"{_ok} {_degisim:+.2f}%"
    _renk = "#00f5c8" if _degisim >= 0 else "#ff5264"
    return _deger, _metin, _renk


@st.fragment(run_every=30)
def piyasa_kulisi_fragment():
    _ku_veriler, _ku_zaman = piyasa_ozeti_getir()
    _piyasa_item = ""
    _doviz_item = ""
    _sinyaller = []

    for _v in _ku_veriler:
        _f, _d, _r = _canli_satir_hazirla(
            _v["fiyat"], _v["degisim"], _v.get("tur", "sayi")
        )
        _satir = (
            '<span class="pk-item">'
            f'<span class="pk-isim">{_v["isim"]}</span>'
            f'<span class="pk-fiyat">{_f}</span>'
            f'<span class="pk-deg" style="color:{_r};">{_d}</span>'
            '</span><span class="pk-ayrac">│</span>'
        )
        _sinyaller.append(f'{_v["isim"]}|{_f}|{_d}')
        if str(_v.get("isim", "")).upper().endswith("TRY"):
            _doviz_item += _satir
        else:
            _piyasa_item += _satir

    _icerik = _piyasa_item + _doviz_item

    # Değişen hücrelerin yeşil/kırmızı parladığı kendi kendine
    # çalışan kayan şerit (iframe). Önceki değerler window.name'de
    # saklanır; iframe her 10 sn'de yenilenince değerler karşılaştırılıp
    # yalnızca değişen hücre parlattırılır, kaydırma konumu korunur.
    import json as _json

    _stil = """
    body { margin: 0; padding: 0; background: transparent; overflow: hidden; }
    .bta-serif-wrap {
        display: flex;
        align-items: stretch;
        gap: 8px;
        margin: 0;
    }
    .bta-serif-wrap .piyasa-kulisi { flex: 1; min-width: 0; margin: 0; }
    .piyasa-kulisi {
        position: relative;
        background: linear-gradient(90deg, rgba(3, 22, 38, 0.98), rgba(4, 44, 66, 0.98));
        border: 1px solid rgba(0, 245, 200, 0.55);
        border-radius: 10px;
        overflow: hidden;
        box-shadow: 0 4px 18px rgba(0, 0, 0, 0.5), 0 0 16px rgba(0, 245, 200, 0.16);
    }
    .piyasa-kulisi-iz {
        display: inline-flex;
        align-items: center;
        white-space: nowrap;
        overflow: hidden;
        max-width: 100%;
    }
    .pk-item {
        display: inline-flex;
        align-items: center;
        gap: 10px;
        padding: 12px 22px;
        font-family: "Consolas", "SFMono-Regular", monospace;
        font-size: 23px;
        border-radius: 8px;
        -webkit-background-clip: padding-box;
        background-clip: padding-box;
        transition: background-color 0.2s ease;
    }
    .pk-isim { font-weight: 900; color: #00f5c8; letter-spacing: 0.5px; }
    .pk-fiyat { font-weight: 900; color: #eafffb; }
    .pk-deg { font-weight: 900; }
    .pk-ayrac { color: rgba(255, 255, 255, 0.35); font-size: 15px; margin-left: -6px; }
    .pk-item.flash-up {
        animation: btaFlashUp 0.9s ease-out;
    }
    .pk-item.flash-down {
        animation: btaFlashDown 0.9s ease-out;
    }
    @keyframes btaFlashUp {
        0% { background-color: rgba(0, 245, 200, 0.4); box-shadow: 0 0 20px rgba(0, 245, 200, 0.55) inset; }
        100% { background-color: transparent; box-shadow: none; }
    }
    @keyframes btaFlashDown {
        0% { background-color: rgba(255, 82, 100, 0.4); box-shadow: 0 0 20px rgba(255, 82, 100, 0.55) inset; }
        100% { background-color: transparent; box-shadow: none; }
    }
    @media screen and (max-width: 700px) {
        .pk-item { font-size: 16px; padding: 6px 14px; }
    }
    """

    _ilcuk = r"""
    <script>
    (function () {
        var iz = document.getElementById('iz');
        if (!iz) return;
        var sig = document.getElementById('sign').getAttribute('data-sigs');
        var simdi;
        try { simdi = JSON.parse(sig); } catch (e) { simdi = []; }
        var depo = null;
        try { depo = JSON.parse(window.name || 'null'); } catch (e) { depo = null; }
        if (depo && depo.s && Array.isArray(depo.s)) {
            var items = iz.querySelectorAll('.pk-item');
            for (var i = 0; i < simdi.length; i++) {
                if (depo.s[i] !== simdi[i]) {
                    var yon = ('' + simdi[i]).split('|')[2] || '';
                    var sinif = (yon.indexOf('+') === 0) ? 'flash-up' : 'flash-down';
                    if (items[i]) items[i].className += ' ' + sinif;
                }
            }
        }
        var x0 = (depo && typeof depo.x === 'number') ? depo.x : 0;
        iz.scrollLeft = x0;
        var sayac = 0;
        var hiz = (window.innerWidth < 700) ? 0.22 : 0.5;
        (function step() {
            iz.scrollLeft += hiz;
            if (iz.scrollLeft >= iz.scrollWidth / 2) iz.scrollLeft = 0;
            sayac++;
            if (sayac % 40 === 0) {
                window.name = JSON.stringify({ s: simdi, x: iz.scrollLeft });
            }
            requestAnimationFrame(step);
        })();
    })();
    </script>
    """

    _html = (
        '<!DOCTYPE html><html><head><meta charset="utf-8">'
        '<style>' + _stil + '</style></head><body>'
        '<div class="bta-serif-wrap">'
        '<div class="piyasa-kulisi">'
        f'<div class="piyasa-kulisi-iz" id="iz">{_icerik}{_icerik}</div>'
        '</div></div>'
        f'<div id="sign" data-sigs="{_json.dumps(_sinyaller, ensure_ascii=False)}" '
        'style="display:none;"></div>'
        + _ilcuk
        + '</body></html>'
    )

    components.html(_html, height=64, scrolling=False)


piyasa_kulisi_fragment()


_bta_logo_html = (
    '<div class="bta-logo-alani"><div class="bta-logo">'
    + _bta_logo_svg
    + '<span class="bta-logo-metin">BTA ALGORİTMA VE PİYASA</span>'
    + '</div></div>'
)

st.markdown(_bta_logo_html, unsafe_allow_html=True)


# ==================================================
# BTA GÜNLÜK ALGORİTMA - SABİT GÜNCELLEME SAATİ
# ==================================================





# ==================================================
# BTA GÜNLÜK ALGORİTMA - SABİT GÜNCELLEME SAATİ
# ==================================================
BTA_DURUM_DOSYASI = "bta_gunluk_durum.csv"


def _aktif_excel_kimligi():
    """
    Klasördeki güncel BTA excel dosyasının "kimliğini"
    (dosya adı + son değiştirilme zamanı) döndürür. Yeni bir
    excel yüklendiğinde bu kimlik değişir; böylece aşağıdaki
    bta_gunluk_zaman_yukle() fonksiyonu YENİ bir excel geldiğini
    anlayıp güncelleme saatini yeniler.
    """
    try:
        _dosyalar = [
            _d for _d in os.listdir(".")
            if _d.lower().endswith((".xlsx", ".xlsm"))
        ]
        _dosyalar.sort(
            key=lambda _ad: (
                not _ad.lower().startswith("bta"),
                _ad.lower()
            )
        )
        if not _dosyalar:
            return ""
        _secilen = _dosyalar[0]
        return f"{_secilen}:{os.path.getmtime(_secilen)}"
    except Exception:
        return ""


def bta_gunluk_zaman_yukle():
    """
    "BTA Günlük Algoritma" bölümünün güncelleme saati ve tarihi,
    o an yüklü olan Excel dosyasının SON DEĞİŞTİRİLME zamanından
    (dosyanın üzerine yazıldığı/yüklendiği andan) Türkiye saatine
    göre hesaplanır. Yeni bir excel yüklediğinizde dosyanın
    değişiklik zamanı güncellendiği için ekrandaki saat de yeni
    yükleme saatini gösterir; dosya aynı kaldığı sürece saat sabit
    kalır.
    """
    try:
        _dosyalar = [
            _d for _d in os.listdir(".")
            if _d.lower().endswith((".xlsx", ".xlsm"))
        ]
        _dosyalar.sort(
            key=lambda _ad: (
                not _ad.lower().startswith("bta"),
                _ad.lower()
            )
        )
        if _dosyalar:
            _secilen = _dosyalar[0]
            _mt = os.path.getmtime(_secilen)
            return datetime.fromtimestamp(
                _mt, TURKIYE_TZ
            ).strftime("%d.%m.%Y %H:%M:%S")
    except Exception:
        pass

    return turkiye_saati().strftime("%d.%m.%Y %H:%M:%S")


# Güncelleme saati her çizimde Excel'in gerçek değişiklik zamanından okunur;
# böylece yeni yüklenen dosyanın saati hiçbir zaman eski/yanlış kalmaz.
_bta_gunluk_sabit_zaman = bta_gunluk_zaman_yukle()


# ==================================================
# PİYASA ÖZETİ KARTLARI (BIST100 / USDTRY / EURTRY / GRAM ALTIN)
# EKRANIN SAĞ KÖŞESİNDE KOMPAKT KART
# ==================================================

@st.fragment(run_every=15)
def piyasa_ozeti_fragment():
    """
    Canlı piyasa kartı. Sayfa baştan çizilmeden yalnızca bu kart
    arka planda 15 saniyede bir yenilenir (st.fragment).
    """
    _ozet_veriler, _ozet_zamani = piyasa_ozeti_getir()

    _ozet_satirlar = ""

    for _i, _veri in enumerate(_ozet_veriler):
        _fiyat_metni, _degisim_metni, _renk = _piyasa_ozet_hazirla(_veri)

        _ozet_satirlar += (
            f'<div class="piyasa-ozet-satir">'
            f'<span class="piyasa-ozet-isim">{_veri["isim"]}</span>'
            f'<span class="piyasa-ozet-fiyat">{_fiyat_metni}</span>'
            f'<span class="piyasa-ozet-degisim" style="color:{_renk};">'
            f'{_degisim_metni}</span>'
            f'</div>'
        )

    st.markdown(
        f'<div class="piyasa-ozet-badge">'
        f'<div class="piyasa-ozet-badge-header">'
        f'📈 CANLI PİYASA · {_ozet_zamani}</div>'
        f'{_ozet_satirlar}'
        f'<div class="piyasa-ozet-not">'
        f'Altın fiyatları ons spot verisinden yaklaşık hesaplanır; '
        f'güncel alım-satım için kuyumcudan teyit alınız.</div>'
        f'</div>',
        unsafe_allow_html=True
    )


def _piyasa_ozet_hazirla(_veri):
    if _veri["fiyat"] is None:
        return "-", "--%", "#8aa7bb"

    if _veri["tur"] == "tl":
        _deger = tl_format(_veri["fiyat"])
    else:
        _deger = sayi_format(_veri["fiyat"])

    if _veri["degisim"] is None:
        return _deger, "--%", "#f2f2f2"

    _degisim = f"{_veri['degisim']:+.2f}%"
    _renk = "#00f5c8" if _veri["degisim"] >= 0 else "#ff5264"

    return _deger, _degisim, _renk


# ==================================================
# CANLI HABER BİLDİRİM SİSTEMİ
# ==================================================
_HABER_TAKIP_DOSYA = "bta_haber_takip.json"


def _haber_kimlik(_baslik):
    """
    Haber başlığını normale indirip kararlı bir kimlik (hash)
    üretir; aynı başlık her seferinde aynı kimliği verir.
    """
    try:
        _temiz = re.sub(r"\s+", " ", str(_baslik).strip().lower())
        return hashlib.md5(
            _temiz.encode("utf-8", "ignore")
        ).hexdigest()
    except Exception:
        return ""


def _haber_takip_oku():
    try:
        if not os.path.exists(_HABER_TAKIP_DOSYA):
            return {}
        with open(_HABER_TAKIP_DOSYA, "r", encoding="utf-8") as _d:
            return json.load(_d)
    except Exception:
        return {}


def _haber_takip_yaz(_kayit):
    try:
        with open(_HABER_TAKIP_DOSYA, "w", encoding="utf-8") as _d:
            json.dump(_kayit, _d, ensure_ascii=False)
    except Exception:
        pass


def _haber_bildirim_durumu():
    """
    5 haber akışını tarar; daha önce görülmemiş (yeni) başlıkları
    tespit eder ve durumu döndürür. Sonuç hem st.session_state'e
    yazılır hem de fonksiyondan döner.

    Dönen sözlük yapısı:
        {
          "bulten": {"etiket": str, "yeni_say": int,
                     "yeni_kimlikler": set, "son_baslik": str,
                     "son_link": str},
          "kap": {...}, "spk": {...}, "bedelli": {...}, "arz": {...}
        }
    """
    _kaynaklar = [
        ("bulten", "Haber Bülteni", son_dakika_haberleri_getir, ()),
        ("kap", "KAP Haberleri", kap_haberleri_getir, ("",)),
        ("spk", "SPK Haberleri", spk_haberleri_getir, ("",)),
        ("bedelli", "Bedelli/Bedelsiz", bedelli_bedelsiz_haberleri_getir, ()),
        ("arz", "Güncel Arz", arz_haberleri_getir, ()),
    ]

    _takip = _haber_takip_oku()
    _sonuc = {}
    _veri = {}

    for _kat, _etiket, _getirici, _arg in _kaynaklar:
        try:
            _ogeler = _getirici(*_arg) or []
        except Exception:
            _ogeler = []

        _veri[_kat] = _ogeler

        _simdi_kimlikler = [
            _haber_kimlik(_o[0]) for _o in _ogeler[:12]
        ]
        _onceki_kimlik = set(_takip.get(_kat, {}).get("kimlikler", []))

        # İlk açılışta (daha önce hiç kayıt yokken) her şeyi
        # "yeni" diye kırmızıya boyamayalım; temel alınarak geçilir.
        _baslangic = not _onceki_kimlik

        if _baslangic:
            _yeni_kimlik = set()
        else:
            _yeni_kimlik = set(_simdi_kimlikler) - _onceki_kimlik

        _takip[_kat] = {"kimlikler": _simdi_kimlikler}

        _sonuc[_kat] = {
            "etiket": _etiket,
            "yeni_say": len(_yeni_kimlik),
            "yeni_kimlikler": _yeni_kimlik,
            "son_baslik": _ogeler[0][0] if _ogeler else None,
            "son_link": _ogeler[0][1] if _ogeler else None,
        }

    _haber_takip_yaz(_takip)

    st.session_state["bta_haber_veri"] = _veri

    return _sonuc


# ==================================================
# CANLI HABER BİLDİRİM PANELİ (KENAR ÇUBUĞU)
# ==================================================

def _haber_bildirim_panel():
    """Kenar çubuğu bildirim paneli; sayfayı yeniden açmadan
    arka planda (fragment) sessizce tazelenir. Durum, ekrandaki
    sinyal parçasından (bta_haber_durum) okunur; tek hesaplama."""
    with st.sidebar.expander("📢 Canlı Haber Bildirimi", expanded=True):
        try:
            _haber_durum = st.session_state.get("bta_haber_durum")
            if not _haber_durum:
                _haber_durum = _haber_bildirim_durumu()
                st.session_state["bta_haber_durum"] = _haber_durum

            _toplam_yeni = sum(
                _d["yeni_say"] for _d in _haber_durum.values()
            )

            if _toplam_yeni == 0:
                st.caption("✔ Tüm haber akışları güncel")
            else:
                st.markdown(
                    f'<div class="bta-notif-kutu">🔴 <b>{_toplam_yeni} '
                    "yeni içerik</b> seni bekliyor</div>",
                    unsafe_allow_html=True,
                )

            for _kat, _d in _haber_durum.items():
                _etiket = _d["etiket"]
                _yeni = _d["yeni_say"]
                _son = _d["son_baslik"]

                if _yeni:
                    st.markdown(f"**{_etiket}** → 🔴 {_yeni} yeni")
                else:
                    st.caption(f"{_etiket}: güncel")

                if _son:
                    _link = _d["son_link"] or "#"
                    st.markdown(
                        f'<a href="{_link}" target="_blank" '
                        f'style="color:#8fb8ff;font-size:12px;'
                        f'text-decoration:none;">'
                        f"{_son[:90]}{'…' if len(_son) > 90 else ''}"
                        "</a>",
                        unsafe_allow_html=True,
                    )

        except Exception:
            st.caption("Haber bildirimi şu anda alınamadı.")


def _haber_ekran_sinyal():
    """ANA EKRANDA "YENİ HABER" SİNYALİ: haber akışlarını tarar,
    yeni içerik düştüğünde sağ üstte küçük, yanıp sönen bir rozet
    gösterir. Sayfa yeniden açılmaz; fragment arka planda çalışır.
    Önce ÇALIŞIR: yeni haberi önce o tüketir, kenar çubuğu yalnızca
    görüntüler."""
    try:
        _haber_durum = _haber_bildirim_durumu()
        st.session_state["bta_haber_durum"] = _haber_durum

        _toplam_yeni = sum(
            _d["yeni_say"] for _d in _haber_durum.values()
        )
        if _toplam_yeni == 0:
            return

        _ilk = None
        for _d in _haber_durum.values():
            if _d["yeni_say"]:
                _ilk = _d
                break

        if _ilk is None:
            return

        _baslik = (_ilk.get("son_baslik") or "Yeni içerik")
        _link = _ilk.get("son_link") or ""
        if not str(_link).strip() or str(_link).strip() == "#":
            _sorgu = urllib.parse.quote_plus(str(_baslik)[:80])
            _link = (
                "https://news.google.com/rss/search?q="
                f"{_sorgu}&hl=tr&gl=TR&ceid=TR:tr"
            )
        _metin = f"🔴 {_baslik}  →"

        st.markdown(
            f'<a class="bta-yeni-sinyal" href="{_link}" '
            f'target="_blank" title="{_baslik} · {_toplam_yeni} yeni haber">'
            f'<span class="nokta"></span>'
            f'<span class="bta-sinyal-metin">{_metin}</span>'
            f"</a>",
            unsafe_allow_html=True,
        )
    except Exception:
        pass


def _haber_ekran_sinyal_otomatik():
    _haber_ekran_sinyal()


_haber_ekran_sinyal_otomatik = st.fragment(run_every=60)(
    _haber_ekran_sinyal_otomatik
)
# Kapatıldı: telefondaki kırmızı sinyal çubuğu metni kapatıyor.
# _haber_ekran_sinyal_otomatik()


def _haber_bildirim_otomatik():
    """Fragment: panel yalnızca kendisi tazelenir, sayfa açılıp
    kapanmaz. Arka planda 5 dakikada bir sessizce güncellenir."""
    _haber_bildirim_panel()


_haber_bildirim_otomatik = st.fragment(run_every=300)(
    _haber_bildirim_otomatik
)
_haber_bildirim_otomatik()


# ==================================================
# YÖNETİCİ SİSTEMİ
# ==================================================
st.sidebar.header("⚙️ Sistem Kontrolleri")

admin_sifre = st.sidebar.text_input(
    "Yönetici Şifresi",
    type="password",
    help="Yönetici paneline erişmek için şifre girin"
)

is_admin = admin_sifre == "3015"

if is_admin:
    st.sidebar.success("✅ Yönetici yetkileri aktif")
    
    with st.sidebar.expander("🔧 Yönetici Paneli"):
        st.subheader("İstatistikleri Yönet")

        col1, col2 = st.columns(2)

        with col1:
            st.metric("👥 Takipçi", takipci_sayisi())

        with col2:
            st.metric("💬 Mesajlar", len(mesajlari_oku()))

        st.divider()

        st.subheader("📩 Yöneticinin Özel Mesaj Kutusu (DM)")

        _dmlar = yonetici_mesajlarini_oku()

        if _dmlar is None or _dmlar.empty:
            st.caption(
                "Kullanıcılardan gelen özel mesaj yok. "
                "Mesajlar yalnızca burada görünür ve sohbete "
                "karışmaz."
            )
        else:
            _dm_sayac = 0
            for _dm_id, _dm_vr in _dmlar.iterrows():
                _dm_sayac += 1

                _dm_kart = st.container(border=True)
                with _dm_kart:
                    _bd1, _bs2 = st.columns([3, 1])
                    with _bd1:
                        st.markdown(
                            f"**🧑‍💼 {_dm_vr['kullanici']}** "
                            f"· *{_dm_vr['tarih']}*"
                        )
                    with _bs2:
                        _dm_sil_bas = st.button(
                            "🗑️ Sil",
                            key=f"dm_sil_{_dm_vr['mesaj_id']}",
                            use_container_width=True
                        )
                        if _dm_sil_bas:
                            yonetici_mesaji_sil(_dm_vr["mesaj_id"])
                            st.rerun()

                    st.write(_dm_vr["mesaj"])
                    if str(_dm_vr.get("oturum", "")).strip():
                        oturum_go = str(_dm_vr["oturum"]).strip()
                        if oturum_go in takipci_oku():
                            st.caption(
                                "👥 Bu kullanıcı sizi takip ediyor."
                            )
                        else:
                            st.caption(
                                "🚫 Takip edilmiyor."
                            )
                        if kullanici_engelli_mi(oturum_go):
                            st.caption("⛔ Şu an engelli/susturulu.")

            st.caption(f"Toplam {_dm_sayac} özel mesaj.")

        st.divider()

        st.subheader("🚫 Engellenen Kullanıcılar")

        engelliler = engelli_oku()

        if not engelliler:
            st.caption("Şu anda engelli kullanıcı yok.")
        else:
            for anahtar, bilgi in sorted(
                engelliler.items()
            ):
                bitis, tur, ad, _os = bilgi
                gorunen = ad or anahtar
                if tur == "engel" or bitis is None:
                    etiket = "🚫 Kalıcı engel"
                else:
                    etiket = (
                        "🔇 Susturma · "
                        + bitis.strftime("%d.%m %H:%M")
                    )

                k1, k2 = st.columns([4, 1])
                with k1:
                    st.markdown(
                        f"**{html.escape(gorunen)}** — {etiket}"
                    )
                with k2:
                    if st.button(
                        "X",
                        key=f"bta_engel_kaldir_{anahtar}",
                        help="Engeli kaldır",
                        use_container_width=True
                    ):
                        engeli_kaldir(anahtar)
                        st.rerun()

        st.divider()

        st.caption(
            "Sohbette her mesajın yanında 🔇 (1 gün sustur) ve "
            "🚫 (kalıcı engel) butonlarını kullanarak kullanıcıları "
            "engelleyebilirsiniz."
        )


# ==================================================
# HİSSE KODU TEMİZLEME + GÜNLÜK LİSTE OKUMA + TANI ARACI
# ==================================================
# Excel'e elle yazılan kodlar her zaman temiz gelmez: "LİDFA" (noktalı İ),
# "unlu", "UNLU.IS", "UNLU LIDFA" (tek hücrede iki kod), "THYAO," gibi.
# Yahoo Finance yalnızca düz ASCII kodları bulur; bu yüzden kodlar önce
# normalize edilir. Aksi halde hisse listede sessizce görünmez.
_TR_ASCII = str.maketrans("İıŞşĞğÜüÖöÇç", "IiSsGgUuOoCc")

_GUNLUK_YASAK_KODLAR = {
    "", "NAN", "NONE", "NULL", "NA",
    "BTA", "AL", "SAT", "TUT", "ALSAT", "BTAALSAT",
    "HISSE", "HISSEKODU", "HISSELER", "HISSELERI", "KOD",
    "GUNLUK", "ALGORITMA",
}


def hisse_kodu_temizle(deger):
    """'LİDFA', ' unlu ', 'UNLU.IS' -> 'LIDFA', 'UNLU', 'UNLU'."""
    if deger is None:
        return ""
    metin = str(deger).strip().translate(_TR_ASCII).upper()
    if metin.endswith(".IS"):
        metin = metin[:-3]
    metin = re.sub(r"[^A-Z0-9]", "", metin)
    return "" if metin in ("NAN", "NONE", "NULL", "NA") else metin


def _hucre_parcala(deger):
    """Bir hücreyi (birden çok kod içerebilir) kod adaylarına böler."""
    return [
        _p for _p in re.split(r"[\s,;/|]+", str(deger)) if _p.strip()
    ]


def gunluk_kodlari_ayikla(degerler):
    """
    B sütunu hücrelerinden temiz, tekrarsız hisse kodu listesi üretir
    (sıra korunur). Başlık satırları ve sayısal/boş hücreler atlanır.
    """
    sonuc = []

    for _d in degerler:
        if _d is None or (isinstance(_d, float) and pd.isna(_d)):
            continue

        for _parca in _hucre_parcala(_d):
            _kod = hisse_kodu_temizle(_parca)

            if (
                _kod in _GUNLUK_YASAK_KODLAR
                or not re.search(r"[A-Z]", _kod)
                or len(_kod) > 7
            ):
                continue

            if _kod not in sonuc:
                sonuc.append(_kod)

    return sonuc


def hisse_liste_teshisi(kod_ham):
    """
    Bir hisse günlük algoritma listesinde neden görünmüyor?
    Excel dosyalarını/sayfalarını tarar, kodun nerede geçtiğini ve
    hangi aşamada elendiğini (Excel'de yok / B sütununda değil /
    fiyat alınamadı) (ikon, metin) satırları olarak döndürür.
    """
    from openpyxl.utils import get_column_letter

    kod = hisse_kodu_temizle(kod_ham)
    if not kod:
        return [("⚠️", "Geçerli bir hisse kodu girin.")]

    satirlar = []

    dosyalar = [
        _d for _d in os.listdir(".")
        if _d.lower().endswith((".xlsx", ".xlsm"))
    ]
    dosyalar.sort(
        key=lambda _ad: (not _ad.lower().startswith("bta"), _ad.lower())
    )

    if not dosyalar:
        return [("❌", "Klasörde Excel dosyası yok.")]

    okunan = dosyalar[0]
    satirlar.append((
        "📄",
        f"Uygulamanın okuduğu Excel: {okunan} (yalnızca 1. sayfa)"
        + (
            f" · klasörde ayrıca: {', '.join(dosyalar[1:])}"
            if len(dosyalar) > 1 else ""
        )
    ))

    isabetler = []  # (dosya, sayfa, adres, sutun_no, hucre_metni)

    for _dosya in dosyalar:
        try:
            _xl = pd.ExcelFile(_dosya, engine="openpyxl")
        except Exception as _h:
            satirlar.append(("⚠️", f"{_dosya} açılamadı: {_h}"))
            continue

        for _i, _sayfa in enumerate(_xl.sheet_names):
            try:
                _df = _xl.parse(_sayfa, header=None)
            except Exception:
                continue

            for _c in range(_df.shape[1]):
                for _r, _v in enumerate(_df.iloc[:, _c].tolist()):
                    if _v is None or (
                        isinstance(_v, float) and pd.isna(_v)
                    ):
                        continue

                    if any(
                        hisse_kodu_temizle(_p) == kod
                        for _p in _hucre_parcala(_v)
                    ):
                        isabetler.append((
                            _dosya,
                            _sayfa,
                            f"{get_column_letter(_c + 1)}{_r + 1}",
                            _c,
                            str(_v),
                            _i == 0 and _dosya == okunan,
                        ))

    if not isabetler:
        satirlar.append((
            "❌",
            f"{kod}, hiçbir Excel dosyasının hiçbir sayfasında yok. "
            "Yani günlük listeye Excel'den gelmemiş; kodu Excel'in "
            "1. sayfasındaki B sütununa ekleyin."
        ))
    else:
        for _dosya, _sayfa, _adres, _c, _hucre, _okunan_yer in isabetler:
            satirlar.append((
                "🔎",
                f"{_dosya} › {_sayfa} › {_adres} hücresinde geçiyor: "
                f"“{_hucre}”"
            ))

        b_de = [_i for _i in isabetler if _i[5] and _i[3] == 1]

        if b_de:
            _listede = kod in gunluk_algoritma_df["Hisse Kodu"].tolist()
            if _listede:
                satirlar.append((
                    "✅", "Günlük listeye alınmış (B sütunu okundu)."
                ))
            else:
                satirlar.append((
                    "❌",
                    "B sütununda var ama liste okuyucu almadı; "
                    "bu bir hata, bana hücre içeriğini gönderin."
                ))
        else:
            _okunanda = [_i for _i in isabetler if _i[5]]
            _baska_dosya = [_i for _i in isabetler if _i[0] != okunan]

            if _okunanda:
                satirlar.append((
                    "⚠️",
                    "Kod okunan sayfada var ama B sütununda değil "
                    f"({', '.join(_i[2] for _i in _okunanda)}). Günlük "
                    "listeye yalnızca 1. sayfanın B sütunu alınır."
                ))
            elif _baska_dosya:
                satirlar.append((
                    "⚠️",
                    f"Kod yalnızca başka dosyada ({_baska_dosya[0][0]}). "
                    f"Uygulama {okunan} dosyasını okuyor; yeni Excel'in "
                    "adı 'bta' ile başlamıyorsa ya da eski bir 'bta' "
                    "dosyası varsa eski dosya öncelik alır."
                ))
            else:
                satirlar.append((
                    "⚠️",
                    "Kod Excel'de yalnızca 1. sayfa dışındaki sayfalarda; "
                    "uygulama yalnızca 1. sayfayı okur."
                ))

    # Fiyat aşaması
    try:
        _s, _d, _hata = fiyat_degisim_getir(kod + ".IS")
        if _hata is None and _s is not None:
            satirlar.append((
                "✅", f"Fiyat alındı: {tl_format(_s)} ({_d:+.2f}%)."
            ))
        else:
            satirlar.append((
                "❌", f"Fiyat alınamadı ({kod}.IS): {_hata}"
            ))
    except Exception as _h:
        satirlar.append(("❌", f"Fiyat sorgusunda hata: {_h}"))

    return satirlar


# ==================================================
# EXCEL'İ OTOMATİK OKU
# A = BTA HİSSE (BTA Algoritma)
# B = BTA AL SAT Hisseleri (ayrı listes)
# C = BTA Alım Fiyatı
# D = BTA Puanı
# ==================================================
excel_dosyalari = [
    dosya
    for dosya in os.listdir(".")
    if dosya.lower().endswith(
        (".xlsx", ".xlsm")
    )
]

# BTA klasöründe bazen ESKİ yedek dosyalar da durabilir
# (ör. nurican.xls.xlsm). os.listdir sırası garanti olmadığından
# "bta" ile başlayan dosya ÖNCELİKLİ seçilir; yoksa ilk bulunan alınır.
excel_dosyalari.sort(
    key=lambda _ad: (
        not _ad.lower().startswith("bta"),
        _ad.lower()
    )
)

excel_df = pd.DataFrame(
    columns=[
        "Hisse Kodu",
        "BTA Alım Fiyatı",
        "BTA Puanı"
    ]
)

gunluk_algoritma_df = pd.DataFrame(columns=["Hisse Kodu"])

if excel_dosyalari:
    secilen_excel = excel_dosyalari[0]

    try:
        ham_df = pd.read_excel(
            secilen_excel,
            sheet_name=0,
            engine="openpyxl",
            header=None
        )

        if ham_df.shape[1] >= 4:
            excel_df = ham_df.iloc[:, [0, 2, 3]].copy()

            excel_df.columns = [
                "Hisse Kodu",
                "BTA Alım Fiyatı",
                "BTA Puanı"
            ]

            excel_df["Hisse Kodu"] = (
                excel_df["Hisse Kodu"]
                .astype(str)
                .str.strip()
                .str.upper()
            )

            excel_df["BTA Alım Fiyatı"] = (
                excel_df["BTA Alım Fiyatı"]
                .apply(turkce_sayi_cevir)
            )

            excel_df["BTA Puanı"] = (
                excel_df["BTA Puanı"]
                .apply(turkce_sayi_cevir)
            )

            excel_df = excel_df[
                ~excel_df["Hisse Kodu"].isin(
                    [
                        "",
                        "NONE",
                        "NAN",
                        "NULL",
                        "NA",
                        "HİSSE",
                        "HISSE",
                        "HİSSE KODU",
                        "HISSE KODU"
                    ]
                )
            ]

            excel_df = excel_df[
                excel_df["BTA Alım Fiyatı"].notna()
            ]

            excel_df = excel_df[
                excel_df["BTA Alım Fiyatı"] > 0
            ]

            excel_df["BTA Puanı"] = (
                excel_df["BTA Puanı"].fillna(0)
            )

            excel_df = excel_df.drop_duplicates(
                subset=["Hisse Kodu"],
                keep="last"
            )

            # ----- B SÜTUNU: BTA AL SAT hisseleri (ayrı listes) -----
            if ham_df.shape[1] >= 2:
                gunluk_algoritma_df = pd.DataFrame(
                    {
                        "Hisse Kodu": gunluk_kodlari_ayikla(
                            ham_df.iloc[:, 1].tolist()
                        )
                    }
                )

    except Exception as hata:
        st.error(
            f"Excel okunamadı: {hata}"
        )


# ==================================================
# EXCEL HİSSE SİNYALİ (ana ekranda)
# ==================================================

def _bta_excel_hisse_adet():
    """BTA klasöründeki güncel Excel'deki hisse sayısını döndürür.
    Hem A/C (BTA hisse) hem B (BTA AL SAT) sütunlarını sayar."""
    _dosyalar = sorted(
        [
            _d
            for _d in os.listdir(".")
            if _d.lower().endswith((".xlsx", ".xlsm"))
        ],
        key=lambda _ad: (
            not _ad.lower().startswith("bta"),
            _ad.lower()
        ),
    )

    if not _dosyalar:
        return 0

    try:
        _ham = pd.read_excel(
            _dosyalar[0],
            sheet_name=0,
            engine="openpyxl",
            header=None
        )
    except Exception:
        return 0

    if _ham.shape[1] < 4:
        return 0

    _kodlar = set()
    _filtre = {
        "", "NONE", "NAN", "NULL", "NA",
        "HİSSE", "HISSE", "HİSSE KODU", "HISSE KODU"
    }

    for _i in range(len(_ham)):
        try:
            _kod = str(_ham.iloc[_i, 0]).strip().upper()
        except Exception:
            _kod = ""

        if not _kod or _kod in _filtre:
            continue

        _fyt = turkce_sayi_cevir(_ham.iloc[_i, 2])

        if _fyt is not None and _fyt > 0:
            _kodlar.add(_kod)

    if _ham.shape[1] >= 2:
        _kodlar.update(
            set(gunluk_kodlari_ayikla(_ham.iloc[:, 1].tolist()))
        )

    return len(_kodlar)


def _bta_sekme_sinyal_stili():
    """Sinyal aktifken başlıktaki "📥 N HİSSE · TIKLA" kısmını
    kırmızı, hafif parıldayan yazıyla gösterir; çerçeve oynamaz,
    başlığın "🧭 BTA" kısmı normal kalır."""
    try:
        _adet = _bta_excel_hisse_adet()
    except Exception:
        _adet = 0

    if not _adet:
        return

    st.markdown(
        f"""
        <style>
        @keyframes btaKizilMetin {{
            0%, 100% {{ text-shadow: 0 0 4px rgba(255, 59, 77, 0.5); }}
            50% {{ text-shadow: 0 0 12px rgba(255, 59, 77, 0.95); }}
        }}
        .st-key-bta_diger_expander summary p::after {{
            content: "  📥 {_adet} HİSSE · TIKLA";
            color: #ff3b4d;
            font-weight: 800;
            animation: btaKizilMetin 2s ease-in-out infinite;
        }}
        </style>
        """,
        unsafe_allow_html=True,
    )


# ==================================================
# TAVAN KUTLAMA (BTA TAKİP LİSTESİ)
# ==================================================
_tavan_listesi = []
_taban_listesi = []
if not excel_df.empty:

    def _tek_hisse_tavan_kontrol(_hisse_kodu):
        try:
            _kod = str(_hisse_kodu).strip().upper()

            if not _kod:
                return _hisse_kodu, None, None, "boş hisse kodu"

            _sembol = _kod

            if not _sembol.endswith(".IS"):
                _sembol += ".IS"

            _son, _degisim, _hata = fiyat_degisim_getir(_sembol)
            return _kod, _son, _degisim, _hata

        except Exception as _ic_hata:
            return _hisse_kodu, None, None, str(_ic_hata)

    try:
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=10
        ) as _havuz:
            for _hisse_kodu, _son, _degisim, _hata in _havuz.map(
                _tek_hisse_tavan_kontrol,
                excel_df["Hisse Kodu"].tolist()
            ):
                if _hata is None and _son is not None and _degisim is not None:
                    if _degisim >= 9.85:
                        _tavan_listesi.append(
                            (_hisse_kodu, _son, _degisim)
                        )
                    elif _degisim <= -9.85:
                        _taban_listesi.append(
                            (_hisse_kodu, _son, _degisim)
                        )
    except Exception:
        _tavan_listesi = []
        _taban_listesi = []





def _sayi_dondur(_metin):
    """Virgüllü ya da noktalı ondalık metni float'a çevirir."""
    try:
        return float(str(_metin).replace(",", ".").replace(" ", ""))
    except Exception:
        return None


# ==================================================
# YABANCI TAKAS ORANLARI - İŞ YATIRIM (BIST)
# ==================================================
def yabanci_takas_oranlari():
    # Günde bir kez (her yeni Türkiye gününün ilk açılışında) yenilenir;
    # gece tazelenir, gün içinde tekrar çekilmez.
    return _yabanci_takas_gun(turkiye_saati().strftime("%Y-%m-%d"))


@st.cache_data(ttl=86400, show_spinner=False)
def _yabanci_takas_gun(gun):
    """
    Borsa İstanbul hisselerinin yabancı (yabancı yatırımcı)
    takas oranlarını İş Yatırım gelişmiş hisse arama ekranından
    çeker. Veri günde bir kez güncellenir; ufak gecikmeli olabilir.

    Alan karşılıkları: 7=Kapanış, 8=Piyasa Değeri (mn TL),
    11=Halka Açıklık %, 40=Yabancı Oranı %, 44=Yabancı 1H Değişim,
    45=Yabancı 1A Değişim.
    """
    _baz_ua = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/125.0.0.0 Safari/537.36"
        ),
        "Accept": "application/json, text/javascript, */*; q=0.01",
        "Accept-Language": "tr-TR,tr;q=0.9,en;q=0.8",
        "X-Requested-With": "XMLHttpRequest",
        "Origin": "https://www.isyatirim.com.tr",
        "Referer": ("https://www.isyatirim.com.tr/tr-tr/analiz/hisse/"
                    "Sayfalar/gelismis-hisse-arama.aspx"),
    }

    try:
        with requests.Session() as _oturum:
            _oturum.get(
                "https://www.isyatirim.com.tr/tr-tr/analiz/hisse/"
                "Sayfalar/gelismis-hisse-arama.aspx",
                headers=_baz_ua,
                timeout=20,
            )
            _govde = {
                "sektor": "",
                "endeks": "",
                "takip": "",
                "oneri": "",
                "criterias": [
                    ["40", "0", "100", "False"],
                    ["44", "-9999999", "9999999", "False"],
                    ["45", "-9999999", "9999999", "False"],
                    ["7", "0", "9999999", "False"],
                    ["8", "0", "9999999", "False"],
                    ["11", "0", "100", "False"],
                ],
                "lang": "1055",
            }
            _yanit = _oturum.post(
                "https://www.isyatirim.com.tr/tr-tr/analiz/_Layouts/"
                "15/IsYatirim.Website/StockInfo/CompanyInfoAjax.aspx/"
                "getScreenerDataNEW",
                json=_govde,
                headers={
                    **_baz_ua,
                    "Content-Type": "application/json; charset=UTF-8",
                },
                timeout=30,
            )
            _d = json.loads(_yanit.json()["d"])
    except Exception:
        return None

    _satirlar = []
    for _r in _d:
        try:
            _hisse = _r.get("Hisse", "") or ""
            if " - " in _hisse:
                _kod = _hisse.split(" - ", 1)[0].strip()
            else:
                _kod = _hisse.strip()

            _satirlar.append({
                "Hisse Kodu": _kod,
                "Yabancı Oranı %": _sayi_dondur(_r.get("40")),
                "1H Değişim": _sayi_dondur(_r.get("44")),
                "1A Değişim": _sayi_dondur(_r.get("45")),
                "Kapanış TL": _sayi_dondur(_r.get("7")),
                "Piyasa Değeri (mn TL)": _sayi_dondur(_r.get("8")),
                "Halka Açıklık %": _sayi_dondur(_r.get("11")),
            })
        except Exception:
            continue

    if not _satirlar:
        return None

    return pd.DataFrame(_satirlar)


# ==================================================
# ARACI KURUM DAĞILIMI - BORSANIN ARACI KURUMLARI
# ==================================================
def araci_kurum_dagilimi():
    # Günde bir kez (her yeni Türkiye gününün ilk açılışında) yenilenir;
    # gece tazelenir, gün içinde tekrar çekilmez.
    return _araci_kurum_dagilimi_gun(turkiye_saati().strftime("%Y-%m-%d"))


@st.cache_data(ttl=86400, show_spinner=False)
def _araci_kurum_dagilimi_gun(gun):
    """
    Gün içi pazar AKD (aracı kurum dağılımı) verisini
    borsakaynak.com'dan çeker. Veri; borsa tarafından sembol
    bazlı ilk 10 kademe AKD verilerinden hesaplanan bir tahmindir,
    resmî pazar geneli AKD değildir.
    """
    try:
        _yanit = requests.get(
            "https://borsakaynak.com/api/bopt/market-akd",
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 Chrome/125 Safari/537.36"
                )
            },
            timeout=20,
        )
        return _yanit.json()
    except Exception:
        return None


# ==================================================
# YAPAY ZEKA ASİSTANI (YEREL AKILLI ARAMA + SOHBET)
# ==================================================
_AI_YARDIM = (
    "Bir hisse kodu yaz (Örn: THYAO, GARAN, ASELS). "
    "O hisseyle ilgili sayfadaki her şeyi bulurum: "
    "fiyat, yabancı takas, haber, algoritma durumu."
)


_AI_HISSE_ISIMLERI = {
    "garanti": "GARAN",
    "akbank": "AKBNK",
    "aselsan": "ASELS",
    "turkcell": "TCELL",
    "sise": "SISE",
    "sisecam": "SISE",
    "şişe": "SISE",
    "şişecam": "SISE",
    "erdemir": "EREGL",
    "tupras": "TUPRS",
    "koc": "KCHOL",
    "sabanci": "SAHOL",
    "turk hava yollari": "THYAO",
    "thyao": "THYAO",
    "thy": "THYAO",
    "yapi kredi": "YKBNK",
    "vakifbank": "VAKBN",
    "halkbank": "HALKB",
    "is bankasi": "ISCTR",
    "sahol": "SAHOL",
    "kchol": "KCHOL",
}


def _ai_hisse_ara(_soru):
    _buyuk = str(_soru).upper()
    for _isim, _kod in _AI_HISSE_ISIMLERI.items():
        if _isim.upper() in _buyuk:
            return _kod
    _eslesme = re.findall(r"\b[A-Z][A-Z0-9]{2,5}\b", _buyuk)
    _skipped = {
        "BIST", "SPK", "KAP", "TL", "USD", "EUR", "TRY", "ALTIN",
        "GRAM", "BTC", "XU100",
        "AL", "SAT", "ALSAT", "BTA", "TUT", "ILE", "VE", "VAR",
        "MI", "MU", "NE", "FARK", "LISTE", "LISTESI", "HANGI",
        "NEDIR", "NED\u0130R", "NELER", "HISSELERI", "HISSELER",
    }
    for _o in _eslesme:
        if _o not in _skipped:
            return _o
    return None


def _piyasa_ozet_pan(_filtre):
    _satirlar = []
    try:
        _kartlar, _ = piyasa_ozeti_getir()
    except Exception:
        return "Piyasa verisi şu anda alınamadı. Lütfen birazdan tekrar dene.\n"
    for _kart in _kartlar:
        _isim = str(_kart.get("isim", "?"))
        if _filtre and _filtre.lower() not in _isim.lower():
            continue
        _fi = _kart.get("fiyat")
        _de = _kart.get("degisim")
        try:
            if _fi is None:
                _satirlar.append(f"- **{_isim}:** veri yok")
            elif _de is None:
                _satirlar.append(f"- **{_isim}:** {float(_fi):,.2f}")
            else:
                _satirlar.append(
                    f"- **{_isim}:** {float(_fi):,.2f} ({float(_de):+.2f}%)"
                )
        except Exception:
            _satirlar.append(f"- **{_isim}:** değer işlenemedi")
    if not _satirlar:
        return "Bu konuda veri bulunamadı.\n"
    return "📊 **Piyasa Özeti**\n\n" + "\n".join(_satirlar) + "\n"


def _fiyat_kart_yanit(_sembol, _etiket, _birim):
    """
    Döviz/altın için doğrudan canlı fiyat kartı döndürür.
    _birim: "tl" veya "gram"
    """
    _son, _deg, _hata = fiyat_degisim_getir(_sembol, marj_kontrolu=False)

    if _birim == "gram":
        _usd, _deg_usd, _hu = fiyat_degisim_getir("USDTRY=X", marj_kontrolu=False)
        if _son is not None and _usd is not None:
            try:
                _gram = float(_son) * float(_usd) / 31.1035
            except Exception:
                return "🥇 **Gram Altın:** değer şu anda işlenemedi.\n"
            _ozet = f"🥇 **Gram Altın:** {_gram:,.2f} TL\n"
            if _deg is not None and _deg_usd is not None:
                _ozet += (
                    f"_(Ons {float(_son):,.2f} USD {float(_deg):+.2f}% · "
                    f"USDTRY {float(_usd):,.2f} {float(_deg_usd):+.2f}%)_\n"
                )
            return _ozet
        return "🥇 **Gram Altın** fiyatı şu anda alınamadı.\n"

    if _son is None:
        return f"**{_etiket}** fiyatı şu anda alınamadı. Lütfen birazdan tekrar dene.\n"
    try:
        if _birim == "sayi":
            _satir = f"📊 **{_etiket}:** {float(_son):,.2f}"
        else:
            _satir = f"💱 **{_etiket}:** {float(_son):,.2f} {_birim.upper()}"
        if _deg is not None:
            _satir += f" ({float(_deg):+.2f}%)"
    except Exception:
        _satir = f"💱 **{_etiket}:** {_son}"
    return _satir + "\n\n_Kaynak: Borsa İstanbul / Yahoo (gecikmeli)_"


def _ai_genel_ara(_soru):
    _bulgular = []
    _anahtar = str(_soru).lower()
    _veri = st.session_state.get("bta_haber_veri", {}) or {}

    for _kat, _etiket in [
        ("bulten", "Haber Bülteni"),
        ("kap", "KAP Haberleri"),
        ("spk", "SPK Haberleri"),
        ("bedelli", "Bedelli/Bedelsiz"),
        ("arz", "Güncel Arz"),
    ]:
        for _o in (_veri.get(_kat) or [])[:60]:
            if _anahtar in str(_o[0]).lower():
                _bulgular.append((_etiket, _o[0], _o[1]))

    try:
        _ys = yabanci_takas_oranlari()
        if _ys is not None:
            for _kod in _ys["Hisse Kodu"].astype(str):
                if _anahtar in _kod.lower():
                    _bulgular.append(
                        ("Yabancı Takas", _kod, "#")
                    )
    except Exception:
        pass

    _gorulen = set()
    _temiz = []
    for _b in _bulgular:
        _t = (_b[0], _b[1])
        if _t in _gorulen:
            continue
        _gorulen.add(_t)
        _temiz.append(_b)

    return _temiz[:15]


def _ai_asistan_yanit(_soru):
    """
    Soruyu akıllıca yorumlar; (özet_markdown, [bulgular]) döndürür.
    Canlı API anahtarı kullanmaz; uygulamanın kendi verisiyle çalışır.
    """
    _soru2 = str(_soru).strip().lower()
    _bulgular = []

    # 1) Yabancı takas
    if ("yabancı" in _soru2) or ("yabanci" in _soru2) or ("takas" in _soru2):
        _ys = yabanci_takas_oranlari()
        if _ys is not None and not _ys.empty:
            _kod = _ai_hisse_ara(_soru)
            if _kod and len(_ys[_ys["Hisse Kodu"] == _kod]):
                _sat = _ys[_ys["Hisse Kodu"] == _kod].iloc[0]
                return (
                    f"**{_kod}** yabancı takas: "
                    f"**%{_sat['Yabancı Oranı %']:.2f}**\n\n"
                    f"- 1H değişim: {_sat['1H Değişim']:+.2f}\n"
                    f"- 1A değişim: {_sat['1A Değişim']:+.2f}\n"
                    f"- Kapanış: {_sat['Kapanış TL']:,.2f} TL · "
                    f"Halka açıklık: %{_sat['Halka Açıklık %']:.2f}\n\n"
                    "_Kaynak: İş Yatırım / BIST (günlük güncellenir)_"
                ), _bulgular
            _top = _ys.sort_values(
                "Yabancı Oranı %", ascending=False, na_position="last"
            ).head(5)
            _ozet = "🏆 **En yüksek yabancı oranlı 5 hisse:**\n\n"
            for _, _r in _top.iterrows():
                _ozet += (
                    f"- {_r['Hisse Kodu']}: **%{_r['Yabancı Oranı %']:.2f}** "
                    f"(1H {_r['1H Değişim']:+.2f})\n"
                )
            return _ozet + "\n_Kaynak: İş Yatırım / BIST_", _bulgular

    # 1.5) BTA ALGORİTMA (A sütunu) ve BTA AL SAT (B sütunu)
    _kod = _ai_hisse_ara(_soru)
    _sor_alsat = ("al sat" in _soru2) or ("alsat" in _soru2)
    _sor_algo = (
        ("algoritma" in _soru2)
        or ("g\u00fcnl\u00fck" in _soru2 and "algoritma" in _soru2)
        or (_kod is not None and "puan" in _soru2)
    )

    _algo_liste = []
    if not excel_df.empty:
        _algo_liste = [
            str(_x).strip().upper()
            for _x in excel_df["Hisse Kodu"].tolist()
            if str(_x).strip()
        ]
    _alsat_liste = []
    if not gunluk_algoritma_df.empty:
        _alsat_liste = [
            str(_h).strip().upper()
            for _h in gunluk_algoritma_df["Hisse Kodu"].tolist()
            if str(_h).strip()
            and str(_h).strip().upper()
            not in (
                "NAN", "NONE", "NULL", "NA", "NAN.0",
                "BTA AL SAT", "AL SAT", "H\u0130SSE", "HISSE",
            )
        ]

    if _sor_alsat or _sor_algo:
        if (
            _sor_alsat and _sor_algo and (
                "fark" in _soru2 or "kar\u0131\u015f" in _soru2
                or "ayr\u0131" in _soru2 or "nedir" in _soru2
            )
        ):
            return (
                "Bunlar iki ayr\u0131 liste:\n\n"
                "- **BTA ALGOR\u0130TMA** (Excel A/C/D s\u00fctunlar\u0131): "
                "BTA hissesi, al\u0131m fiyat\u0131 ve puan\u0131.\n"
                "- **BTA AL SAT** (Excel B s\u00fctunu): g\u00fcnl\u00fck "
                "al-sat hisseleri.\n\n"
                "Aralar\u0131nda kar\u0131\u015ft\u0131rma yok; ikisini "
                "ayr\u0131 listeler halinde takip ediyoruz."
            ), _bulgular

        if _sor_alsat and not _sor_algo:
            if _kod is not None:
                _k_ust = str(_kod).upper()
                if _k_ust in _alsat_liste:
                    _cevap = [
                        f"**{_k_ust}** BTA AL SAT listesinde: "
                        "**EVET** (Excel B s\u00fctunu)."
                    ]
                    _son, _deg, _hata = fiyat_degisim_getir(_k_ust + ".IS")
                    if _son is not None:
                        _cevap.append(
                            f"- Anl\u0131k fiyat: {tl_format(_son)} "
                            f"({_deg:+.2f}%)"
                        )
                    _cevap.append(
                        "- BTA ALGOR\u0130TMA (A s\u00fctunu): "
                        + ("**EVET**" if _k_ust in _algo_liste else "**YOK**")
                    )
                    return "\n".join(_cevap), _bulgular
                return (
                    f"**{_k_ust}** BTA AL SAT listesinde **YOK** "
                    "(Excel B s\u00fctununda yok)."
                ), _bulgular

            if _alsat_liste:
                _ozet = "\U0001F4C5 **BTA AL SAT Hisseleri** "
                _ozet += "(Excel B s\u00fctunu):\n\n"
                for _h in _alsat_liste[:12]:
                    _son, _deg, _hata = fiyat_degisim_getir(_h + ".IS")
                    if _son is not None:
                        _ozet += (
                            f"- {_h}: **{tl_format(_son)}** "
                            f"({_deg:+.2f}%)\n"
                        )
                    else:
                        _ozet += f"- {_h}: fiyat al\u0131namad\u0131\n"
                return (
                    _ozet
                    + "\n_Kaynak: Excel B s\u00fctunu (AL SAT)_"
                ), _bulgular
            return (
                "BTA AL SAT listesi bug\u00fcn bo\u015f."
            ), _bulgular

        if _sor_algo:
            if _kod is not None:
                _k_ust = str(_kod).upper()
                if _k_ust in _algo_liste:
                    _cevap = [
                        f"**{_k_ust}** BTA ALGOR\u0130TMASINDA: "
                        "**EVET** (Excel A s\u00fctunu)."
                    ]
                    try:
                        _kayit = excel_df[
                            excel_df["Hisse Kodu"].astype(str).str.upper()
                            == _k_ust
                        ].iloc[0]
                        _cevap.append(
                            f"- BTA Al\u0131m Fiyat\u0131: "
                            f"{tl_format(_kayit['BTA Al\u0131m Fiyat\u0131'])}"
                        )
                        _cevap.append(
                            f"- BTA Puan\u0131: "
                            f"{sayi_format(_kayit['BTA Puan\u0131'])}"
                        )
                    except Exception:
                        pass
                    _son, _deg, _hata = fiyat_degisim_getir(_k_ust + ".IS")
                    if _son is not None:
                        _cevap.append(
                            f"- Anl\u0131k fiyat: {tl_format(_son)} "
                            f"({_deg:+.2f}%)"
                        )
                    _cevap.append(
                        "- BTA AL SAT (B s\u00fctunu): "
                        + (
                            "**EVET**" if _k_ust in _alsat_liste else "**YOK**"
                        )
                    )
                    return "\n".join(_cevap), _bulgular

                return (
                    f"**{_k_ust}** \u015fu anda BTA ALGOR\u0130TMASINDA "
                    "**yok** (Excel A s\u00fctununda yok).\n"
                    + (
                        f"AL SAT listesinde (B s\u00fctunu) ise "
                        f"**EVET** var.\n\n"
                        f"AL SAT listedekiler: "
                        + (", ".join(_alsat_liste[:12]) if _alsat_liste else "(bo\u015f)")
                        if _k_ust in _alsat_liste else
                        f"AL SAT listesinde de **YOK**.\n\n"
                        f"BTA ALGOR\u0130TMA listen: "
                        + (", ".join(_algo_liste[:12]) if _algo_liste else "(bo\u015f)")
                    )
                ), _bulgular

            if _algo_liste:
                _ozet = "\U0001F4C5 **BTA ALGOR\u0130TMA** "
                _ozet += "(Excel A/C/D s\u00fctunlar\u0131):\n\n"
                for _h in _algo_liste[:12]:
                    _satir = f"- {_h}"
                    try:
                        _kayit = excel_df[
                            excel_df["Hisse Kodu"].astype(str).str.upper()
                            == _h
                        ].iloc[0]
                        _satir += (
                            f": al\u0131m {tl_format(_kayit['BTA Al\u0131m Fiyat\u0131'])}"
                            f", puan {sayi_format(_kayit['BTA Puan\u0131'])}"
                        )
                    except Exception:
                        pass
                    _ozet += _satir + "\n"
                return (
                    _ozet
                    + "\n_Kaynak: Excel A/C/D s\u00fctunlar\u0131 "
                    "(BTA ALGOR\u0130TMA)_"
                ), _bulgular
            return (
                "BTA ALGOR\u0130TMA bug\u00fcn bo\u015f "
                "(Excel A s\u00fctunu okunamad\u0131 m\u0131?)."
            ), _bulgular

    # 2) Hisse fiyatı + ilgili her şey (haber, yabancı takas)
    _kod = _ai_hisse_ara(_soru)
    if _kod:
        _bolumler = []
        _bulgular2 = []
        _kod_pat = re.compile(
            r"(?<![A-Z0-9])" + re.escape(_kod.upper()) + r"(?![A-Z0-9])"
        )

        _son, _deg, _hata = fiyat_degisim_getir(_kod + ".IS")
        _fiyat_var = (_son is not None and _deg is not None)
        if _fiyat_var:
            _bolumler.append(
                f"📈 **{_kod}** güncel fiyat: **{_son:,.2f} TL** "
                f"({_deg:+.2f}%)"
                "\n_(Kaynak: Borsa İstanbul resmî gecikmeli ~15 dk)_"
            )

        # Yabancı takas bilgisi
        _yabanci_var = False
        try:
            _ys = yabanci_takas_oranlari()
            if (
                _ys is not None and not _ys.empty
                and len(_ys[_ys["Hisse Kodu"] == _kod])
            ):
                _sat = _ys[_ys["Hisse Kodu"] == _kod].iloc[0]
                _yabanci_var = True
                _bolumler.append(
                    f"💹 **{_kod} yabancı takas:** "
                    f"**%{_sat['Yabancı Oranı %']:.2f}**\n"
                    f"- 1H: {_sat['1H Değişim']:+.2f} · "
                    f"1A: {_sat['1A Değişim']:+.2f}\n"
                    f"- Kapanış: {_sat['Kapanış TL']:,.2f} TL · "
                    f"Halka açıklık: %{_sat['Halka Açıklık %']:.2f}"
                    "\n_(Kaynak: İş Yatırım / BIST, günlük güncellenir)_"
                )
        except Exception:
            pass

        # Haberler: KAP / SPK / bedelli / arz / bültende kodu geçenler
        _veri = st.session_state.get("bta_haber_veri", {}) or {}
        _haberler = []
        _kayi_kaynak = [
            ("kap", "KAP Haberleri", kap_haberleri_getir),
            ("spk", "SPK Haberleri", spk_haberleri_getir),
            ("bedelli", "Bedelli/Bedelsiz", bedelli_bedelsiz_haberleri_getir),
            ("arz", "Güncel Arz", arz_haberleri_getir),
        ]
        for _kat, _etiket, _ft in _kayi_kaynak:
            _gelenler = _veri.get(_kat) or []
            if not _gelenler:
                try:
                    _gelenler = (_ft() or [])[:40]
                except Exception:
                    _gelenler = []
            for _o in _gelenler:
                if _kod_pat.search(str(_o[0]).upper()):
                    _haberler.append((_etiket, _o[0], _o[1]))
                    _bulgular2.append((_etiket, _o[0], _o[1]))
                    if len(_haberler) >= 8:
                        break
            if len(_haberler) >= 8:
                break

        if _haberler:
            _bolumler.append("📰 **Hakkındaki haberler:**")
            for _etiket, _bas, _link in _haberler[:6]:
                _bolumler.append(f"- *{_etiket}:* [{_bas}]({_link})")

        # Yalnızca gerçek hisse olduğu doğrulanınca kapsamlı rapor dön
        if _fiyat_var or _yabanci_var or _haberler:
            return "\n\n".join(_bolumler), _bulgular2

        # Kod tanındı ama veri alınamadı: "sonuç yok" yerine net bilgi ver
        return (
            f"**{_kod}** kodunu buldum; fiyat, takas veya haber "
            "verisi şu anda alınamadı. Birazdan tekrar dene. "
            "(Kod yanlışsa örn. THYAO, GARAN, ASELS gibi yaz.)"
        ), _bulgular2

    # 3) Haber kategorileri
    _veri = st.session_state.get("bta_haber_veri", {}) or {}
    _akislar = [
        ("kap", "kap", "KAP haberleri"),
        ("spk", "spk", "SPK haberleri"),
        ("bedelli", "bedelli", "Bedelli/Bedelsiz Sermaye"),
        ("bedelli", "bedelsiz", "Bedelli/Bedelsiz Sermaye"),
        ("arz", "halka arz", "Güncel Arz"),
        ("arz", "arz", "Güncel Arz"),
    ]
    for _kat, _anahtar, _etiket in _akislar:
        if _anahtar in _soru2:
            _gelenler = _veri.get(_kat) or []
            if not _gelenler:
                _get_ft = {
                    "kap": kap_haberleri_getir,
                    "spk": spk_haberleri_getir,
                    "bedelli": bedelli_bedelsiz_haberleri_getir,
                    "arz": arz_haberleri_getir,
                }[_kat]
                _gelenler = _get_ft() or []
            _ozet = f"📰 **{_etiket} — son 5:**\n\n"
            for _o in _gelenler[:5]:
                _bas, _link = _o[0], _o[1]
                _bulgular.append((_etiket, _bas, _link))
                _ozet += f"- [{_bas}]({_link})\n"
            return _ozet, _bulgular

    # 4) Haber bülteni (genel)
    if any(_k in _soru2 for _k in ("haber", "gündem", "gundem", "bülten")):
        _gelenler = _veri.get("bulten") or son_dakika_haberleri_getir()
        _ozet = "📰 **Haber Bülteni — son 5:**\n\n"
        for _o in (_gelenler or [])[:5]:
            _bas, _link = _o[0], _o[1]
            _bulgular.append(("Haber Bülteni", _bas, _link))
            _ozet += f"- [{_bas}]({_link})\n"
        return _ozet, _bulgular

    # 5) Piyasa / döviz / altın
    if ("gram altın" in _soru2) or ("gram" in _soru2) or (
        "altın" in _soru2
    ) or ("altin" in _soru2):
        return _fiyat_kart_yanit("GC=F", "Gram Altın", "gram"), _bulgular
    if "döviz" in _soru2 or "doviz" in _soru2:
        return (
            _fiyat_kart_yanit("USDTRY=X", "DOLAR", "tl")
            + _fiyat_kart_yanit("EURTRY=X", "EURO", "tl"),
            _bulgular,
        )
    if ("dolar" in _soru2) or ("usd" in _soru2):
        return _fiyat_kart_yanit("USDTRY=X", "DOLAR", "tl"), _bulgular
    if ("euro" in _soru2) or ("eur" in _soru2) or ("avro" in _soru2):
        return _fiyat_kart_yanit("EURTRY=X", "EURO", "tl"), _bulgular
    if any(_k in _soru2 for _k in ("piyasa", "endeks", "bist")):
        return _piyasa_ozet_pan(""), _bulgular

    # 6) Yardım
    if any(
        _k in _soru2
        for _k in ("yardım", "yardim", "ne yaparsın", "neler yapabilirsin",
                   "merhaba", "selam")
    ):
        return _AI_YARDIM, _bulgular

    # 7) Genel akıllı arama (her yerde ara)
    _bulgular = _ai_genel_ara(_soru)
    if _bulgular:
        _ozet = "🔎 **Şu sonuçları buldum:**\n\n"
        for _etiket, _bas, _link in _bulgular:
            if _link and _link != "#":
                _ozet += f"- *{_etiket}:* [{_bas}]({_link})\n"
            else:
                _ozet += f"- *{_etiket}:* {_bas}\n"
        return _ozet, _bulgular

    # 8) Anlaşılamadı
    return (
        "Bunu anlayamadım. Şöyle sorabilirsin: _" + _AI_YARDIM + "_"
    ), _bulgular


# ==================================================
# PANELLER - TIKLA-AÇILIR GRUPLAR
# ==================================================
# ----- 0) YAPAY ZEKA ASİSTANI -----

# TAVAN KUTLAMA (ana sayfada, yapay zekâ panelinin üstünde görünür)
if not excel_df.empty and _tavan_listesi:
    for _hisse_kodu, _son, _degisim in _tavan_listesi:
        st.markdown(
            tavan_kutlama_format(_hisse_kodu, _son, _degisim),
            unsafe_allow_html=True
        )
    st.divider()

with st.expander(
    "🤖 HİSSE SOR", expanded=False, key="bta_ai_expander"
):
    st.markdown("##### 🔍 Hisse Fiyat Getir")

    with st.form("hisse_arama_form"):
        _arama_kodu = st.text_input(
            "BIST Hisse Kodu",
            placeholder="Örn: THYAO, GARAN, ASELS",
            help="Hisse kodunu yazıp Fiyat Getir'e basın."
        ).strip().upper()
        _arama_bas = st.form_submit_button(
            "💰 Fiyat Getir",
            use_container_width=True
        )

    if _arama_bas and _arama_kodu:
        _arama_sembol = (
            _arama_kodu
            if _arama_kodu.endswith(".IS")
            else _arama_kodu + ".IS"
        )

        _arama_son, _arama_degisim, _arama_hata = fiyat_degisim_getir(
            _arama_sembol,
            marj_kontrolu=False
        )

        if _arama_hata or _arama_son is None:
            st.error(
                f"'{_arama_kodu}' için fiyat alınamadı. "
                f"({_arama_hata or 'bilinmeyen hata'})"
            )
        else:
            _arama_renk = (
                "#00f5c8"
                if (_arama_degisim or 0) >= 0
                else "#ff5264"
            )

            st.markdown(
                f"""
                <div class="hisse-arama-kart">
                    <div class="hisse-arama-ust">
                        <span class="hisse-arama-kod">
                            {_arama_kodu}
                        </span>
                        <span class="hisse-arama-fiyat"
                              style="color:{_arama_renk};">
                            ₺ {tl_format(_arama_son)}
                        </span>
                    </div>
                    <div class="hisse-arama-degisim"
                         style="color:{_arama_renk};">
                        {(_arama_degisim if _arama_degisim is not None else 0):+.2f}%
                    </div>
                </div>
                """,
                unsafe_allow_html=True
            )

            _arama_haberler = _hisse_haber_cek(_arama_kodu)
            if _arama_haberler:
                st.markdown("##### 📰 Haber Akışı")
                for _arah in _arama_haberler[:5]:
                    st.markdown(
                        f"- [{_arah['baslik']}]({_arah['link']})"
                    )
            else:
                st.caption(
                    f"'{_arama_kodu}' için son 48 saatte haber bulunamadı."
                )

# ----- 1A) TEKNİK ANALİZ ÖZETİ (ayrı panel) -----
with st.expander(
    "📊 TEKNİK ANALİZ ÖZETİ", expanded=False,
    key="bta_teknik_expander"
):
    tab_hizli = st.container()

# ----- 1B) FİNANSAL TAKVİM (ayrı panel) -----
with st.expander(
    "📅 FİNANSAL TAKVİM", expanded=False,
    key="bta_takvim_expander"
):
    tab_takvim = st.container()

# ----- 1) HABERLER -----
with st.expander("📰 HABERLER", expanded=False, key="bta_haberler_expander"):
    tab_haber, tab_kap, tab_sermaye, tab_spk, tab_arz = st.tabs(
        [
            "Haber Bülteni",
            "KAP Haberleri",
            "Bedelli/Bedelsiz Sermaye",
            "SPK Haberleri",
            "Güncel Arz",
        ]
    )

# ----- 2) ARAÇLAR -----
with st.expander("🛠️ ARAÇLAR", expanded=False, key="bta_araclar_expander"):
    tab_doviz, tab_grafik, tab_bedelli, tab_alarm, tab_paylas = st.tabs(
        [
            "Döviz Çevirici",
            "Grafik Çiz",
            "Bedelli/Bedelsiz HESAP",
            "Fiyat Alarmı",
            "Paylaş",
        ]
    )

# ----- 3) DİĞER (BTA algoritması) -----
with st.expander(
    "🧭 BTA",
    expanded=False,
    key="bta_diger_expander",
):
    tab_gunluk = st.tabs(["BTA ALGORİTMA"])[0]

    _bta_sekme_sinyal_stili()

# ----- 4) DERİNLEMESİNE ANALİZ (Yabancı Takas + Aracı Kurum + Temel) -----
with st.expander(
    "📊 DERİNLEMESİNE ANALİZ", expanded=False, key="bta_derin_expander"
):
    tab_yabanci, tab_kurum, tab_temel = st.tabs(
        [
            "Yabancı Takas Oranları",
            "Aracı Kurum Dağılımı",
            "Temel Analiz Özeti",
        ]
    )


UYE_DOSYASI = "bta_uyeler.csv"
UYE_SUTUNLARI = ["kullanici", "sifre_hash", "tarih"]
TAKIP_LISTE_DOSYASI = "bta_takip_listesi.csv"
TAKIP_LISTE_SUTUNLARI = ["kullanici", "sembol", "eklenme"]
YONETICI_ADI = "ATİLA"
YONETICI_SIFRESI = "3015"
dosya_olustur(UYE_DOSYASI, UYE_SUTUNLARI)
dosya_olustur(TAKIP_LISTE_DOSYASI, TAKIP_LISTE_SUTUNLARI)


def _uye_sifre_hash(sifre):
    return hashlib.sha256((sifre or "").encode("utf-8")).hexdigest()


def uye_listesi_oku():
    try:
        _df = pd.read_csv(UYE_DOSYASI, dtype=str).fillna("")
    except Exception:
        return pd.DataFrame(columns=UYE_SUTUNLARI)
    for _c in UYE_SUTUNLARI:
        if _c not in _df.columns:
            _df[_c] = ""
    return _df


def _uye_kisi_anahtar(k):
    _x = unicodedata.normalize("NFKC", str(k or ""))
    for _a, _b in (
        ("ı", "i"),
        ("İ", "i"),
        ("i\u0307", "i"),
        ("I", "i"),
        ("i\u0307", "i"),
    ):
        _x = _x.replace(_a, _b)
    return _x.strip().lower()


def _uye_eslestir(k):
    _df = uye_listesi_oku()
    if _df.empty:
        return None
    _ak = _uye_kisi_anahtar(k)
    for _, _r in _df.iterrows():
        if _uye_kisi_anahtar(_r["kullanici"]) == _ak:
            return str(_r["kullanici"]), str(_r["sifre_hash"])
    return None


def _uye_dedup():
    _df = uye_listesi_oku()
    if _df.empty or len(_df) < 2:
        return
    _df = _df.copy()
    _df["_ak"] = [_uye_kisi_anahtar(x) for x in _df["kullanici"]]
    _df = _df.sort_values("tarih")
    _gorulen = set()
    _sec = []
    for _, _r in _df.iterrows():
        if _r["_ak"] in _gorulen:
            continue
        _gorulen.add(_r["_ak"])
        _sec.append([_r["kullanici"], _r["sifre_hash"], _r["tarih"]])
    _df2 = pd.DataFrame(_sec, columns=UYE_SUTUNLARI)
    _df2 = _df2.drop_duplicates(subset=["kullanici"])
    _df2.to_csv(UYE_DOSYASI, index=False, encoding="utf-8-sig")
    _tk = takip_listesi_oku()
    if not _tk.empty:
        _esi = {}
        for _, _r in _df2.iterrows():
            _esi[_uye_kisi_anahtar(_r["kullanici"])] = str(_r["kullanici"])
        _tk = _tk.copy()
        _tk["_ak"] = [_uye_kisi_anahtar(x) for x in _tk["kullanici"]]
        _tk["kullanici"] = [
            _esi.get(_a, _e)
            for _a, _e in zip(_tk["_ak"], _tk["kullanici"])
        ]
        _tk = _tk[["kullanici", "sembol", "eklenme"]]
        _tk = _tk.drop_duplicates(subset=["kullanici", "sembol"])
        _tk.to_csv(TAKIP_LISTE_DOSYASI, index=False, encoding="utf-8-sig")


def uye_kayit(kullanici, sifre):
    _k = str(kullanici or "").strip()
    _sif = str(sifre or "").strip()
    if not _k or not _sif:
        return "Kullanıcı adı ve şifre gerekli."
    if len(_sif) < 3:
        return "Şifre en az 3 karakter olmalı."
    if _uye_eslestir(_k) is not None:
        return "Bu kullanıcı adı zaten alınmış."
    if _uye_kisi_anahtar(_k) == _uye_kisi_anahtar(YONETICI_ADI):
        return "Bu kullanıcı adı yöneticiye ayrılmış."
    _df = uye_listesi_oku()
    _yeni = pd.DataFrame([{
        "kullanici": _k,
        "sifre_hash": _uye_sifre_hash(_sif),
        "tarih": turkiye_saati().strftime("%Y-%m-%d %H:%M"),
    }])
    pd.concat([_df, _yeni], ignore_index=True).to_csv(
        UYE_DOSYASI, index=False, encoding="utf-8-sig"
    )
    return "OK"


def uye_giris(kullanici, sifre):
    _k = str(kullanici or "").strip()
    _sif = str(sifre or "").strip()
    if not _k or not _sif:
        return None
    _es = _uye_eslestir(_k)
    if _es is None:
        return None
    _kayit_hash = _es[1]
    if _kayit_hash == _uye_sifre_hash(_sif) or _kayit_hash == _uye_sifre_hash(
        sifre
    ):
        return _es[0]
    return False


def uye_listesi_nickler():
    _df = uye_listesi_oku()
    if _df.empty:
        return []
    _uniq = {}
    for _k in _df["kullanici"]:
        _n = str(_k).strip()
        if not _n:
            continue
        _uniq.setdefault(_uye_kisi_anahtar(_n), _n)
    return list(_uniq.values())


def uye_iptal(kullanici):
    _k = str(kullanici or "").strip()
    if not _k:
        return False
    _ak = _uye_kisi_anahtar(_k)
    _df = uye_listesi_oku()
    _df = _df[_df["kullanici"].map(_uye_kisi_anahtar) != _ak]
    _df.to_csv(UYE_DOSYASI, index=False, encoding="utf-8-sig")
    _tk = takip_listesi_oku()
    _tk = _tk[_tk["kullanici"].map(_uye_kisi_anahtar) != _ak]
    _tk.to_csv(TAKIP_LISTE_DOSYASI, index=False, encoding="utf-8-sig")
    return True


def takip_listesi_oku():
    try:
        _df = pd.read_csv(TAKIP_LISTE_DOSYASI, dtype=str).fillna("")
    except Exception:
        return pd.DataFrame(columns=TAKIP_LISTE_SUTUNLARI)
    for _c in TAKIP_LISTE_SUTUNLARI:
        if _c not in _df.columns:
            _df[_c] = ""
    return _df


_uye_dedup()


def takip_listesi_ekle(kullanici, sembol):
    _k = str(kullanici or "").strip()
    _s = str(sembol or "").strip().upper().replace(".IS", "")
    if not _k or not _s:
        return False
    _df = takip_listesi_oku()
    if ((_df["kullanici"] == _k) & (_df["sembol"] == _s)).any():
        return False
    _yeni = pd.DataFrame([{
        "kullanici": _k,
        "sembol": _s,
        "eklenme": turkiye_saati().strftime("%Y-%m-%d %H:%M"),
    }])
    pd.concat([_df, _yeni], ignore_index=True).to_csv(
        TAKIP_LISTE_DOSYASI, index=False, encoding="utf-8-sig"
    )
    return True


def takip_listesi_sil(kullanici, sembol):
    _k = str(kullanici or "").strip()
    _s = str(sembol or "").strip().upper().replace(".IS", "")
    _df = takip_listesi_oku()
    _df = _df[~((_df["kullanici"] == _k) & (_df["sembol"] == _s))]
    _df.to_csv(TAKIP_LISTE_DOSYASI, index=False, encoding="utf-8-sig")


def takip_listesi_getir(kullanici):
    _df = takip_listesi_oku()
    _k = str(kullanici or "").strip()
    if _df.empty or not _k:
        return []
    return _df[_df["kullanici"] == _k]["sembol"].tolist()


def _takip_sembol_ayristir(girdi):
    _g = str(girdi or "").strip().upper().replace(".IS", "")
    if not _g:
        return None
    if _g in ("XU100", "BIST", "BIST100"):
        return {"tur": "endeks", "isim": "BIST100", "yf": "XU100.IS", "kod": None}
    if _g in ("GRAM", "ALTIN", "GOLD"):
        return {"tur": "emtia", "isim": "GRAM", "yf": "GC=F", "kod": None}
    if _g.endswith("TRY") and len(_g) == 6:
        return {"tur": "doviz", "isim": _g, "yf": _g + "=X", "kod": None}
    _temiz = _bist_sembol_mu(_g)
    if _temiz:
        return {"tur": "hisse", "isim": _temiz, "yf": _temiz + ".IS", "kod": _temiz}
    return None


def _takip_fiyat(_c):
    _c = dict(_c)
    try:
        if _c["tur"] in ("doviz", "emtia", "endeks"):
            _son, _deg, _hata = fiyat_degisim_getir(_c["yf"], marj_kontrolu=False)
        else:
            _son, _deg, _hata = fiyat_degisim_getir(_c["kod"])
        if _son is None:
            return _c["isim"], None, None, _hata or "veri alınamadı"
        return _c["isim"], _son, _deg, None
    except Exception:
        return _c["isim"], None, None, "hata"


@st.cache_data(ttl=60, show_spinner=False)
def _takip_durum_kayit(sembol):
    _c = _takip_sembol_ayristir(sembol)
    if _c is None:
        return sembol, None, None, "geçersiz sembol"
    return _takip_fiyat(_c)


def _yabanci_oran_kayit(kod):
    try:
        _g = yabanci_takas_oranlari()
        _hisse = str(kod or "").strip().upper().replace(".IS", "")
        _m = _g[
            _g["Hisse Kodu"].astype(str).str.strip().str.upper()
            .str.replace(".IS", "", regex=False) == _hisse
        ]
        if _m.empty:
            return None
        _r = _m.iloc[0]

        def _al(_c):
            try:
                _v = float(_r[_c])
                if pd.isna(_v):
                    return None
                return _v
            except Exception:
                return None

        return {
            "oran": _al("Yabancı Oranı %"),
            "1s": _al("1H Değişim"),
            "1a": _al("1A Değişim"),
            "halka": _al("Halka Açıklık %"),
        }
    except Exception:
        return None


def _rsi14_hesapla(kapanislar):
    try:
        _d = kapanislar.diff()
        _artis = _d.clip(lower=0)
        _dusus = -_d.clip(upper=0)
        _oa = _artis.ewm(alpha=1 / 14, adjust=False, min_periods=14).mean()
        _od = _dusus.ewm(alpha=1 / 14, adjust=False, min_periods=14).mean()
        _rs = _oa / _od.replace(0, 1e-9)
        _son = float((100 - 100 / (1 + _rs)).iloc[-1])
        if pd.isna(_son):
            return None
        return _son
    except Exception:
        return None


def _rsi_yorum(_r):
    if _r is None:
        return "-"
    if _r <= 30:
        return "Aşırı satım"
    if _r >= 70:
        return "Aşırı alım"
    if _r >= 55:
        return "Güçlü"
    if _r <= 45:
        return "Zayıf"
    return "Nötr"


# ==================================================
# AI HİSSE DOSYASI (TEK TIKLA BİRLEŞİK KARAR RAPORU)
# ==================================================


def _ai_hisse_dosyasi(_kod):
    """Tek hisse için teknik + temel + yabancı takas + haber
    verilerini birleştirir; avantaj/risk listesi ve 1-5 yıldız
    skor üretir. Herhangi bir kaynağın hatası tek tek atlanır."""
    _kod = str(_kod or "").strip().upper().replace(".IS", "")
    _r = {
        "kod": _kod,
        "fiyat": None,
        "guncel_degisim": None,
        "rsi": None,
        "sma20": None,
        "sma50": None,
        "trend": "-",
        "temel": None,
        "yabanci": None,
        "likidite": None,
        "haberler": [],
        "avantajlar": [],
        "riskler": [],
        "notlar": [],
        "yildiz": 3,
        "yorum": "Yeterli veri alınamadı; sonra tekrar deneyin.",
    }

    try:
        _son, _deg, _ht = fiyat_degisim_getir(
            _kod + ".IS", marj_kontrolu=False
        )
        _r["fiyat"] = _son
        _r["guncel_degisim"] = _deg
    except Exception:
        pass

    try:
        _g = _bist_gecmis(_kod, 100)
        _kap = _g["Close"].dropna()
        _r["rsi"] = _rsi14_hesapla(_kap)
        _s20 = _kap.rolling(20).mean().iloc[-1]
        _s50 = _kap.rolling(50).mean().iloc[-1]
        _r["sma20"] = None if pd.isna(_s20) else _s20
        _r["sma50"] = None if pd.isna(_s50) else _s50
        _sonk = float(_kap.iloc[-1])
        _puan_yon = 0
        if _r["sma20"] is not None:
            _puan_yon += 1 if _sonk > _r["sma20"] else -1
        if _r["sma50"] is not None:
            _puan_yon += 1 if _sonk > _r["sma50"] else -1
        _r["trend"] = "Yükseliş" if _puan_yon > 0 else (
            "Düşüş" if _puan_yon < 0 else "Yatay"
        )
    except Exception:
        pass

    try:
        _r["temel"] = temel_analiz_getir(_kod)
    except Exception:
        _r["temel"] = None

    try:
        _r["likidite"] = _hisse_macd_likidite(_kod + ".IS")
    except Exception:
        _r["likidite"] = None

    try:
        _r["yabanci"] = _yabanci_oran_kayit(_kod)
    except Exception:
        _r["yabanci"] = None

    try:
        _r["haberler"] = (_hisse_haber_cek(_kod) or [])[:5]
    except Exception:
        _r["haberler"] = []

    _p = 3.0

    if _r["yabanci"]:
        _y2 = _r["yabanci"]
        if _y2.get("1a") is not None:
            if _y2["1a"] > 0.5:
                _p += 0.5
                _r["avantajlar"].append("Yabancı payı son 1 ayda artıyor (alım var)")
            elif _y2["1a"] < -0.5:
                _p -= 0.5
                _r["riskler"].append("Yabancı payı son 1 ayda azalıyor (satış var)")
        if _y2.get("1s") is not None and _y2["1s"] > 0.1:
            _p += 0.25
            _r["avantajlar"].append("Bu hafta yabancılar net alım yapıyor")
        if _y2.get("oran") is not None and _y2["oran"] < 10:
            _r["notlar"].append(
                f"Düşük yabancı oranı (%{_y2['oran']:.1f}) — kurumsal ilgi az"
            )

    if _r["rsi"] is not None:
        if 30 <= _r["rsi"] <= 55:
            _p += 0.5
            _r["avantajlar"].append("RSI uygun aralıkta, aşırı alım/satım yok")
        elif _r["rsi"] > 75:
            _p -= 0.5
            _r["riskler"].append("RSI aşırı alımda — düzeltme riski yüksek")
        elif _r["rsi"] < 25:
            _p += 0.25
            _r["notlar"].append("RSI çok düşük — dip arayışında olabilir")

    if _r["trend"] == "Yükseliş":
        _p += 0.5
        _r["avantajlar"].append("Fiyat SMA20/50 üzerinde (yükseliş eğilimi)")
    elif _r["trend"] == "Düşüş":
        _p -= 0.5
        _r["riskler"].append("Fiyat SMA20/50 altında (düşüş eğilimi)")

    if _r["temel"]:
        _t2 = _r["temel"]
        if _t2.get("pddd") and 0 < float(_t2["pddd"]) < 3:
            _p += 0.25
            _r["avantajlar"].append("PD/DD değerlemesi görece makul")
        elif _t2.get("pddd") and float(_t2["pddd"]) >= 6:
            _p -= 0.25
            _r["riskler"].append("PD/DD yüksek — primli fiyatlama")
        if _t2.get("temettu_verimi"):
            _p += 0.25
            _r["avantajlar"].append(
                f"Temettü veriyor (%{_t2['temettu_verimi']:.2f})"
            )
        if _t2.get("fk") and 0 < float(_t2["fk"]) < 20:
            _p += 0.25
            _r["avantajlar"].append("F/K değeri görece düşük")
        elif _t2.get("fk"):
            try:
                if float(_t2["fk"]) < 0:
                    _p -= 0.5
                    _r["riskler"].append("Şirket zararda (F/K negatif)")
            except Exception:
                pass

    if _r["likidite"]:
        _ml3 = _r["likidite"]

        if _ml3.get("macd_gunluk_hist") is not None:
            if float(_ml3["macd_gunluk_hist"]) > 0:
                _p += 0.25
                _r["avantajlar"].append(
                    "Günlük MACD momentumu pozitif (histogram > 0)"
                )
            else:
                _p -= 0.25
                _r["riskler"].append(
                    "Günlük MACD momentumu negatif (histogram < 0)"
                )

        if _ml3.get("para_ort20"):
            try:
                if float(_ml3["para_ort20"]) >= 1e7:
                    _r["notlar"].append(
                        "Likidite yüksek: ort. günlük işlem hacmi "
                        + temel_buyuk_sayi_format(_ml3["para_ort20"])
                    )
            except Exception:
                pass

    _negatif_kelime = [
        "zarar", "soruşturma", "kayıp", "kriz", "ertelendi", "iptal",
        "yeni sınırlamalar", "dava", "uyarı",
    ]
    for _h in _r["haberler"]:
        _bas = str(_h.get("baslik", ""))
        if any(_nk in _bas.lower() for _nk in _negatif_kelime):
            _p -= 0.25
            _r["riskler"].append("Haber başlıkları olumsuz sinyal içeriyor")
            break

    if _r["guncel_degisim"] is not None and _r["guncel_degisim"] > 4:
        _p -= 0.25
        _r["notlar"].append("Bugün sert yükseliş var — kovalamaca riski")

    _p = max(1.0, min(5.0, _p))
    _r["yildiz"] = round(_p)

    _durum = "Olumlu" if _p >= 3.5 else ("Olumsuz" if _p <= 2.4 else "Nötr")
    _r["yorum"] = (
        f"{_kod} için karışık veri değerlendirmesi: teknik+kurumsal+temel "
        f"bileşkesinde görünüm {_durum.lower()}. Skor {_p:.1f}/5 "
        "(1=riskli, 5=avantajlı). Bu bir yatırım tavsiyesi değildir; "
        "kendi araştırmanızla birlikte kullanın."
    )
    return _r


# ==================================================
# FİYAT VE HABER ALARMI - ORTAK ALTYAPI
# (Hem Fiyat Alarmı sekmesi hem Kişisel Takip kullanır)
# ==================================================

ALARM_DOSYASI = "bta_alarmlar.csv"
_ALARM_SUTUNLARI = [
    "alarm_id", "sembol", "yon", "fiyat", "durum", "tarih", "sahip"
]


def _alarmlar_oku():
    if not os.path.exists(ALARM_DOSYASI):
        return pd.DataFrame(columns=_ALARM_SUTUNLARI)
    try:
        _df = pd.read_csv(ALARM_DOSYASI, dtype=str).fillna("")
    except Exception:
        return pd.DataFrame(columns=_ALARM_SUTUNLARI)
    for _c in _ALARM_SUTUNLARI:
        if _c not in _df.columns:
            _df[_c] = ""
    return _df


def _alarmlar_yaz(_df):
    try:
        _df.to_csv(ALARM_DOSYASI, index=False)
    except Exception:
        pass


def _alarm_ekle(_sembol, _yon, _fiyat, _sahip):
    _df = _alarmlar_oku()
    _yeni = pd.DataFrame([{
        "alarm_id": uuid.uuid4().hex[:8],
        "sembol": str(_sembol).strip().upper(),
        "yon": _yon,
        "fiyat": f"{_fiyat:.4f}",
        "durum": "aktif",
        "tarih": turkiye_saati().strftime("%d.%m.%Y %H:%M"),
        "sahip": _sahip,
    }])
    _alarmlar_yaz(pd.concat([_df, _yeni], ignore_index=True))


def _alarm_sil(_aid, _sahip):
    _df = _alarmlar_oku()
    if not _df.empty:
        _df = _df[
            (_df["alarm_id"] != _aid) | (_df["sahip"] != _sahip)
        ]
        _alarmlar_yaz(_df)


def _alarm_sembol_kontrol(_sembol, _son_fiyat, _sahip):
    """Verilen güncel fiyata göre o sembolün aktif alarmlarını
    denetler; hedefe ulaşanları 'tetiklendi' yapar. Değişiklik
    yapıldıysa dosyaya yazar."""
    try:
        _df = _alarmlar_oku()
        if _df.empty or _son_fiyat is None:
            return _df
        _degisti = False
        for _idx, _row in _df.iterrows():
            if str(_row["durum"]) != "aktif":
                continue
            if str(_row["sahip"]) != str(_sahip):
                continue
            if str(_row["sembol"]).strip().upper() != str(_sembol).strip().upper():
                continue
            try:
                _hedef = float(_row["fiyat"])
            except Exception:
                continue
            _tetik = (
                (str(_row["yon"]) == "Üstüne çıkınca" and _son_fiyat >= _hedef)
                or (str(_row["yon"]) == "Altına inince" and _son_fiyat <= _hedef)
            )
            if _tetik:
                _df.at[_idx, "durum"] = "tetiklendi"
                _degisti = True
        if _degisti:
            _alarmlar_yaz(_df)
        return _df
    except Exception:
        return _alarmlar_oku()


dosya_olustur(ALARM_DOSYASI, _ALARM_SUTUNLARI)


# ==================================================
# PORTFÖY DOKTORU - VERİ KATMANI
# ==================================================

PORTFOY_DOSYASI = "bta_portfoy.csv"
_PORTFOY_SUTUNLARI = [
    "id", "kullanici", "sembol", "adet", "alis", "tarih"
]


def _portfoy_oku():
    if not os.path.exists(PORTFOY_DOSYASI):
        return pd.DataFrame(columns=_PORTFOY_SUTUNLARI)
    try:
        _df = pd.read_csv(PORTFOY_DOSYASI, dtype=str).fillna("")
    except Exception:
        return pd.DataFrame(columns=_PORTFOY_SUTUNLARI)
    for _c in _PORTFOY_SUTUNLARI:
        if _c not in _df.columns:
            _df[_c] = ""
    return _df


def _portfoy_yaz(_df):
    try:
        _df.to_csv(PORTFOY_DOSYASI, index=False)
    except Exception:
        pass


def _portfoy_getir(kullanici):
    _df = _portfoy_oku()
    if _df.empty:
        return _df
    return _df[_df["kullanici"] == kullanici].copy()


def _portfoy_ekle(kullanici, sembol, adet, alis):
    _df = _portfoy_oku()
    _yeni = pd.DataFrame([{
        "id": uuid.uuid4().hex[:8],
        "kullanici": kullanici,
        "sembol": str(sembol).strip().upper(),
        "adet": f"{float(adet):.6f}",
        "alis": f"{float(alis):.4f}",
        "tarih": turkiye_saati().strftime("%d.%m.%Y %H:%M"),
    }])
    _portfoy_yaz(pd.concat([_df, _yeni], ignore_index=True))


def _portfoy_sil(kullanici, pid):
    _df = _portfoy_oku()
    if not _df.empty:
        _df = _df[
            (_df["id"] != pid) | (_df["kullanici"] != kullanici)
        ]
        _portfoy_yaz(_df)


def _portfoy_raporu(kullanici):
    """Üyenin portföyünü güncel fiyatlarla karşılaştırır; her satır
    için kar/zarar, toplamları ve en çok sürükleyen hisseleri
    döndürür. Herhangi bir veri çekme hatasında atlanır."""
    _pf = _portfoy_getir(kullanici)
    _satirlar = []
    _toplam_alis = 0.0
    _toplam_simdi = 0.0
    for _idx, _row in _pf.iterrows():
        try:
            _sembol = str(_row["sembol"]).strip().upper()
            _adet = float(_row["adet"])
            _alis = float(_row["alis"])
            _c = _takip_sembol_ayristir(_sembol)
            if _c is None:
                _c = {"isim": _sembol, "kod": _sembol, "tur": "hisse"}
            _ad2, _son2, _deg2, _ht2 = _takip_fiyat(_c)
            if _son2 is None:
                raise ValueError("fiyat yok")
            _maliyet = _adet * _alis
            _deger = _adet * float(_son2)
            _kar = _deger - _maliyet
            _kar_y = (_kar / _maliyet * 100.0) if _maliyet else 0.0
            _gunluk = (float(_deg2) / 100.0 * _maliyet) if _deg2 else 0.0
            _toplam_alis += _maliyet
            _toplam_simdi += _deger
            _satirlar.append({
                "id": _row["id"],
                "sembol": _sembol,
                "isim": _c.get("isim", _sembol),
                "adet": _adet,
                "alis": _alis,
                "son": float(_son2),
                "maliyet": _maliyet,
                "deger": _deger,
                "kar": _kar,
                "kar_y": _kar_y,
                "gunluk": _gunluk,
                "tarih": _row.get("tarih", ""),
            })
        except Exception:
            continue
    _satirlar.sort(key=lambda _x: _x["kar"], reverse=True)
    return {
        "satirlar": _satirlar,
        "toplam_alis": _toplam_alis,
        "toplam_simdi": _toplam_simdi,
        "toplam_kar": _toplam_simdi - _toplam_alis,
        "toplam_kar_y": (
            (_toplam_simdi - _toplam_alis) / _toplam_alis * 100.0
            if _toplam_alis
            else 0.0
        ),
        "gunluk_kar": sum(_x["gunluk"] for _x in _satirlar),
        "kar_edenler": [x for x in _satirlar if x["kar"] >= 0],
        "kaybedenler": [
            x for x in _satirlar if x["kar"] < 0
        ],
    }


with st.expander("🔒 ÖZEL", expanded=False, key="bta_ozel_expander"):
    tab_takip, tab_sohbet, tab_dm = st.tabs(["Kişisel Takip", "💬 Sohbet", "✉️ Yöneticiye Mesaj"])

with tab_takip:
    _uye = st.session_state.get("bta_uyelik_user")

    if not _uye:
        st.markdown("### 🔐 Giriş / Üyelik")
        _kullanici = st.text_input("Kullanıcı adı", key="uye_kul")
        _sifre = st.text_input("Şifre", type="password", key="uye_sif")
        _bt1, _bt2 = st.columns(2)
        with _bt1:
            if st.button(
                "✅ Giriş Yap", key="uye_giris_btn", use_container_width=True
            ):
                _gl = uye_giris(_kullanici, _sifre)
                if _gl:
                    st.session_state["bta_uyelik_user"] = _gl
                    st.rerun()
                elif _gl is None:
                    st.error("Bu kullanıcı adıyla kayıt yok. 'Kayıt Ol' ile hesap aç.")
                else:
                    st.error("Şifre hatalı.")
        with _bt2:
            if st.button(
                "🔓 Kayıt Ol", key="uye_kayit_btn", use_container_width=True
            ):
                if not _kullanici.strip() or not _sifre:
                    st.warning("Kullanıcı adı ve şifre gir.")
                elif len(str(_sifre).strip()) < 3:
                    st.warning("Şifre en az 3 karakter olsun.")
                else:
                    _snc = uye_kayit(_kullanici, _sifre)
                    if _snc == "OK":
                        st.session_state["bta_uyelik_user"] = _kullanici.strip()
                        st.rerun()
                    else:
                        st.warning(_snc)
        st.caption(
            "Üyelikle kendi hisse/döviz listeni oluştur; hepsi tek ekranda. "
            "Şifreler yalnızca özet (hash) olarak saklanır."
        )
        with st.expander("⚙️ Yönetici Girişi", expanded=False):
            _a_kul = st.text_input("Yönetici adı", key="yon_kul")
            _a_sif = st.text_input(
                "Yönetici şifresi", type="password", key="yon_sif"
            )
            if st.button(
                "Yönetici Girişi", key="yon_btn", use_container_width=True
            ):
                if _a_kul.strip() == YONETICI_ADI and _a_sif == YONETICI_SIFRESI:
                    st.session_state["bta_uyelik_user"] = YONETICI_ADI
                    st.rerun()
                else:
                    st.error("Yönetici bilgileri hatalı.")
    else:
        _s1, _s2 = st.columns([5, 1])
        with _s1:
            st.success(f"Hoş geldin {_uye}")
        with _s2:
            if st.button("Çıkış", key="uye_cikis_btn", use_container_width=True):
                st.session_state["bta_uyelik_user"] = None
                st.rerun()

        _glist = takip_listesi_getir(_uye)
        if _glist:
            with st.container(border=True):
                st.markdown(
                    "📋 **Bugünün Özeti** · "
                    f"{turkiye_saati().strftime('%d.%m.%Y')}"
                )
                _gros = [_takip_durum_kayit(_s) for _s in _glist]
                _gor = [_r for _r in _gros if _r is not None and _r[3] is None]
                _up_n = sum(
                    1 for _r in _gor if _r[2] is not None and _r[2] >= 0
                )
                _dn_n = sum(
                    1 for _r in _gor if _r[2] is not None and _r[2] < 0
                )
                _ort_d = (
                    sum(_r[2] for _r in _gor if _r[2] is not None)
                    / max(1, sum(1 for _r in _gor if _r[2] is not None))
                    if any(_r[2] is not None for _r in _gor)
                    else 0.0
                )
                _gm1, _gm2, _gm3, _gm4 = st.columns(4)
                _gm1.metric("Takip Edilen", len(_glist))
                _gm2.metric("Yükselen", _up_n)
                _gm3.metric("Düşen", _dn_n)
                _gm4.metric("Ort. Değişim", f"%{_ort_d:+.2f}")
                _tatmp = _alarmlar_oku()
                if not _tatmp.empty:
                    _ted = _tatmp[
                        (_tatmp["sahip"] == _uye)
                        & (_tatmp["durum"] == "tetiklendi")
                    ]
                    if not _ted.empty:
                        st.markdown(
                            "🔔 **Tetiklenen alarmlar:** "
                            + ", ".join(_ted["sembol"].tolist())
                        )
                _bugun_tavan = {
                    str(_tk_).strip().upper()
                    for _tk_, _, _ in _tavan_listesi
                }
                _kesisim = [
                    _s
                    for _s in _glist
                    if str(_s).strip().upper() in _bugun_tavan
                ]
                if _kesisim:
                    st.markdown(
                        "🟢 **Takip listenizde tavanda:** "
                        + ", ".join(_kesisim)
                    )
                _vw = st.session_state.get("bta_haber_veri", {})
                _mmol = []
                _mem = set()
                for _ogeler in _vw.values():
                    for _o in _ogeler[:12]:
                        _bU = str(_o[0]).upper()
                        for _sm in _glist:
                            if len(str(_sm).strip()) < 3:
                                continue
                            if str(_sm).strip().upper() in _bU:
                                if str(_o[0]) in _mem:
                                    break
                                _mem.add(str(_o[0]))
                                _mmol.append((_sm, _o[0], _o[1]))
                                break
                if _mmol:
                    st.markdown("📰 **Takip listenizle ilgili yeni haberler**")
                    for _sm, _bb, _ll in _mmol[:3]:
                        _ll = _ll or "#"
                        st.markdown(
                            f"- 🔹 <b>{_sm}</b> — "
                            f"[{str(_bb)[:60]}]({_ll})",
                            unsafe_allow_html=True,
                        )
                    if len(_mmol) > 3:
                        st.caption(f"+{len(_mmol) - 3} haber daha")

        _yeni_sembol = st.text_input(
            "Sembol ekle (Örn: THYAO, USDTRY, GRAM, XU100)",
            key="takip_yeni_sembol",
            placeholder="THYAO, USDTRY, GRAM...",
        )
        if st.button(
            "Listeye Ekle",
            key="takip_ekle_btn",
            use_container_width=True,
        ):
            _a = _takip_sembol_ayristir(_yeni_sembol)
            if _a is None:
                st.warning("Geçerli bir sembol yaz (örn: THYAO).")
            else:
                if takip_listesi_ekle(_uye, _a["isim"]):
                    st.success("Eklendi ✓")
                else:
                    st.info("Zaten listede ya da tekrar deneyin.")

        _liste = takip_listesi_getir(_uye)
        if not _liste:
            st.info("Takip listen boş. Yukarıdan sembol ekleyebilirsin.")
        else:
            _ros = [_takip_durum_kayit(_s) for _s in _liste]
            st.markdown("### 📊 Takip Listem")
            _sil_iste = None
            _al_aktif = set()
            _atmps = _alarmlar_oku()
            if not _atmps.empty:
                _al_aktif = set(
                    _atmps.loc[
                        (_atmps["sahip"] == _uye)
                        & (_atmps["durum"] == "aktif"),
                        "sembol",
                    ].str.upper()
                )
            for _s, _r in zip(_liste, _ros):
                if _r is None:
                    _ad, _son, _deg, _hata = _s, None, None, "geçersiz"
                else:
                    _ad, _son, _deg, _hata = _r
                with st.container(border=True):
                    _ca, _cb, _cc, _cd = st.columns([3, 2, 2, 2])
                    with _ca:
                        _cal = "🔔 " if str(_ad).upper() in _al_aktif else ""
                        st.markdown(f"**{_cal}{_ad}**")
                    with _cb:
                        if _son is not None:
                            st.markdown(f"**{sayi_format(_son)}**")
                        else:
                            st.markdown("-")
                    with _cc:
                        if _deg is not None:
                            _rc = "#00f5c8" if _deg >= 0 else "#ff5264"
                            _ok = "▲" if _deg >= 0 else "▼"
                            st.markdown(
                                f"<span style='color:{_rc};font-weight:900'>"
                                f"{_ok} %{_deg:.2f}</span>",
                                unsafe_allow_html=True,
                            )
                        else:
                            st.markdown("-")
                    with _cd:
                        _sek_a = st.session_state.get("bta_takip_secilen")
                        _acik2 = _sek_a == _s
                        if st.button(
                            "Kapat" if _acik2 else "Ayrıntı",
                            key=f"takip_ayrinti_{_s}",
                            use_container_width=True,
                        ):
                            st.session_state["bta_takip_secilen"] = (
                                None if _acik2 else _s
                            )
                        if st.button(
                            "Sil",
                            key=f"takip_sil_{_s}",
                            use_container_width=True,
                        ):
                            _sil_iste = _s
            if _sil_iste:
                takip_listesi_sil(_uye, _sil_iste)
                st.rerun()

            _sec = st.session_state.get("bta_takip_secilen")
            if _sec in _liste:
                _c = _takip_sembol_ayristir(_sec)
                if _c:
                    _isi, _so, _dg, _ht = _takip_fiyat(_c)
                    _renk = "#ff5264" if (_dg is not None and _dg < 0) else "#00f5c8"
                    _deg_metin = ""
                    if _dg is not None:
                        _ok = "▲" if _dg >= 0 else "▼"
                        _deg_metin = (
                            f"<span style='color:{_renk}'> {_ok} %{_dg:.2f}</span>"
                        )
                    _fiyat_metin = (
                        sayi_format(_so) if _so is not None else "veri alınamadı"
                    )
                    st.markdown(
                        f"<h3 style='text-align:center'>{_isi} &nbsp; "
                        f"<span style='color:#eafffb'>{_fiyat_metin}</span>"
                        f"{_deg_metin}</h3>",
                        unsafe_allow_html=True,
                    )
                    if st.button(
                        "❌ Ayrıntıyı Kapat",
                        key=f"takip_kapat_{_sec}",
                        use_container_width=True,
                    ):
                        st.session_state["bta_takip_secilen"] = None
                        st.rerun()
                    if _c["tur"] == "hisse":
                        try:
                            _g = _bist_gecmis(_c["kod"], 100)
                            _kapanis = _g["Close"].dropna()
                            _rsi = _rsi14_hesapla(_kapanis)
                            _sma20 = _kapanis.rolling(20).mean().iloc[-1]
                            _sma50 = _kapanis.rolling(50).mean().iloc[-1]
                            if pd.isna(_sma20):
                                _sma20 = None
                            if pd.isna(_sma50):
                                _sma50 = None
                            with st.container(border=True):
                                st.markdown("📈 **Teknik Göstergeler**")
                                _a1, _a2, _a3 = st.columns(3)
                                _a1.metric(
                                    "RSI (14)",
                                    f"{_rsi:.1f}" if _rsi is not None else "-",
                                    _rsi_yorum(_rsi),
                                )
                                _a2.metric(
                                    "SMA20",
                                    sayi_format(_sma20) if _sma20 is not None else "-",
                                )
                                _a3.metric(
                                    "SMA50",
                                    sayi_format(_sma50) if _sma50 is not None else "-",
                                )
                        except Exception:
                            st.caption("Teknik veri alınamadı.")
                        _yo = _yabanci_oran_kayit(_c["kod"])
                        if _yo:
                            with st.container(border=True):
                                st.markdown("💹 **Yabancı Oranı**")
                                _o1, _o2, _o3 = st.columns(3)
                                _o1.metric(
                                    "Yabancı Oranı",
                                    f"%{_yo['oran']:.2f}"
                                    if _yo["oran"] is not None
                                    else "-",
                                    f"1S {_yo['1s']:+.2f}%"
                                    if _yo["1s"] is not None
                                    else None,
                                )
                                _o2.metric(
                                    "1 Aylık Değişim",
                                    f"%{_yo['1a']:+.2f}"
                                    if _yo["1a"] is not None
                                    else "-",
                                )
                                _o3.metric(
                                    "Halka Açıklık",
                                    f"%{_yo['halka']:.2f}"
                                    if _yo["halka"] is not None
                                    else "-",
                                )
                        try:
                            _t = temel_analiz_getir(_c["kod"])
                            with st.container(border=True):
                                st.markdown("🏢 **Temel Değerler**")
                                _b1, _b2, _b3, _b4 = st.columns(4)
                                _b1.metric(
                                    "F/K", sayi_format(_t["fk"]) if _t["fk"] else "-"
                                )
                                _b2.metric(
                                    "PD/DD",
                                    sayi_format(_t["pddd"]) if _t["pddd"] else "-",
                                )
                                _b3.metric(
                                    "Temettü",
                                    f"%{_t['temettu_verimi']:.2f}"
                                    if _t["temettu_verimi"]
                                    else "-",
                                )
                                _bd = _t["piyasa_degeri"]
                                _b4.metric(
                                    "Piyasa Değeri", sayi_format(_bd) if _bd else "-"
                                )
                                st.caption(
                                    f"Sektör: {_t['sektor'] or '-'} "
                                    f"&nbsp;•&nbsp; {_t['ad'] or ''}"
                                )
                        except Exception:
                            st.caption("Temel veri alınamadı.")
                    if st.button(
                        "🤖 AI Hisse Dosyası (Karar Raporu)",
                        key=f"ai_dosya_buton_{_sec}",
                        use_container_width=True,
                    ):
                        with st.spinner("AI raporu hazırlanıyor..."):
                            st.session_state[f"bta_ai_dosya_{_sec}"] = (
                                _ai_hisse_dosyasi(_c["kod"])
                            )
                        st.rerun()
                    _rapo = st.session_state.get(f"bta_ai_dosya_{_sec}")
                    if _rapo:
                        with st.container(border=True):
                            _ys = "★" * _rapo["yildiz"] + "☆" * (
                                5 - _rapo["yildiz"]
                            )
                            st.markdown(
                                f"🤖 **AI Hisse Dosyası — {_rapo['kod']}** "
                                f"· {_ys} ({_rapo['yildiz']}/5)"
                            )
                            if _rapo["fiyat"] is not None:
                                _dg_txt = (
                                    f"▲ {_rapo['guncel_degisim']:+.2f}%"
                                    if _rapo["guncel_degisim"] is not None
                                    and _rapo["guncel_degisim"] >= 0
                                    else f"▼ {_rapo['guncel_degisim']:+.2f}%"
                                )
                            else:
                                _dg_txt = "-"
                            _rs_txt = ""
                            if _rapo["rsi"] is not None:
                                _rs_txt = (
                                    f"RSI: {_rapo['rsi']:.1f} "
                                    f"({_rsi_yorum(_rapo['rsi'])})"
                                )
                            _tekn_parca = " · ".join(
                                _p for _p in [
                                    f"Fiyat: {sayi_format(_rapo['fiyat']) if _rapo['fiyat'] is not None else '-'} ({_dg_txt})",
                                    _rs_txt or "",
                                    f"SMA20 {sayi_format(_rapo['sma20']) if _rapo['sma20'] is not None else '-'}",
                                    f"SMA50 {sayi_format(_rapo['sma50']) if _rapo['sma50'] is not None else '-'}",
                                    f"Trend: {_rapo['trend']}",
                                ] if _p
                            )
                            st.caption(_tekn_parca)
                            if _rapo["yabanci"]:
                                _y3 = _rapo["yabanci"]
                                st.caption(
                                    "Yabancı: "
                                    f"{f'%{_y3['oran']:.2f}' if _y3.get('oran') is not None else '-'}"
                                    f"  ·  1H {f'{_y3['1s']:+.2f}' if _y3.get('1s') is not None else '-'}"
                                    f"  ·  1A {f'{_y3['1a']:+.2f}' if _y3.get('1a') is not None else '-'}"
                                )
                            if _rapo["temel"]:
                                _t5 = _rapo["temel"]
                                st.caption(
                                    "Sermaye: "
                                    f"{temel_buyuk_sayi_format(_t5.get('sermaye'))}"
                                    " (ödenmiş, yakl.)"
                                    f"  ·  Özsermaye: "
                                    f"{temel_buyuk_sayi_format(_t5.get('oz_sermaye'))}"
                                    f"  ·  Defter Değeri: "
                                    f"{tl_format(_t5.get('defter_degeri'))}"
                                )
                            if _rapo["likidite"]:
                                _m3 = _rapo["likidite"]
                                _macd_txt = (
                                    f"MACD G: {_m3['macd_gunluk']:+.3f}"
                                    if _m3.get("macd_gunluk") is not None
                                    else "MACD G: -"
                                )
                                _macd_txt += (
                                    f"  ·  A: {_m3['macd_aylik']:+.3f}"
                                    if _m3.get("macd_aylik") is not None
                                    else "  ·  A: -"
                                )
                                _macd_txt += (
                                    f"  ·  Y: {_m3['macd_yillik']:+.3f}"
                                    if _m3.get("macd_yillik") is not None
                                    else "  ·  Y: -"
                                )
                                st.caption(_macd_txt)
                                st.caption(
                                    "💧 Likidite: "
                                    f"Ort.20g hacim "
                                    f"{temel_adet_format(_m3.get('hacim_ort20'))}"
                                    f"  ·  işlem hacmi "
                                    f"{temel_buyuk_sayi_format(_m3.get('para_ort20'))}"
                                )
                            if _rapo["avantajlar"]:
                                st.markdown(
                                    "**✔ Avantajlar**\n\n"
                                    + "\n".join(
                                        f"- {_a}" for _a in _rapo["avantajlar"]
                                    )
                                )
                            if _rapo["riskler"]:
                                st.markdown(
                                    "**⚠ Riskler**\n\n"
                                    + "\n".join(
                                        f"- {_a}" for _a in _rapo["riskler"]
                                    )
                                )
                            if _rapo["notlar"]:
                                st.caption(
                                    "ℹ Notlar: " + " · ".join(_rapo["notlar"])
                                )
                            st.markdown(_rapo["yorum"])
                            if _rapo["haberler"]:
                                st.markdown("**📰 Son Haberler**")
                                for _hh in _rapo["haberler"]:
                                    st.markdown(
                                        f"- [🔗 {_hh['baslik']}]({_hh['link']})"
                                    )
                            st.caption(
                                "Skor otomatik bir değerlendirmedir; "
                                "yatırım tavsiyesi değildir."
                            )
                    with st.container(border=True):
                        st.markdown("🔔 **Fiyat Alarmı**")
                        _tum_al = _alarm_sembol_kontrol(
                            _c["kod"], _so, _uye
                        )
                        _kedi = pd.DataFrame(columns=_ALARM_SUTUNLARI)
                        if not _tum_al.empty:
                            _kedi = _tum_al[
                                (_tum_al["sahip"] == _uye)
                                & (
                                    _tum_al["sembol"].str.upper()
                                    == _c["kod"].upper()
                                )
                            ]
                        _aktif_say = 0
                        if not _kedi.empty:
                            for _aidx, _arow in _kedi.iterrows():
                                if str(_arow["durum"]) == "tetiklendi":
                                    st.error(
                                        f"🔔 ALARM TETİKLENDİ: {_arow['sembol']} "
                                        f"{_arow['yon']} {tl_format(_arow['fiyat'])} "
                                        f"(kuruluş: {_arow['tarih']})"
                                    )
                                elif str(_arow["durum"]) == "aktif":
                                    _aktif_say += 1
                                    _x1, _x2 = st.columns([5, 1])
                                    with _x1:
                                        st.write(
                                            f"🔔 {_arow['sembol']} • {_arow['yon']} • "
                                            f"{tl_format(_arow['fiyat'])} • "
                                            f"{_arow['tarih']}"
                                        )
                                    with _x2:
                                        if st.button(
                                            "Sil",
                                            key=f"takeh_al_sil_{_arow['alarm_id']}",
                                            use_container_width=True,
                                        ):
                                            _alarm_sil(_arow["alarm_id"], _uye)
                                            st.rerun()
                        if _aktif_say == 0:
                            st.caption("Bu sembol için aktif alarmın yok.")
                        _yy1, _yy2, _yy3 = st.columns([2, 2, 1])
                        with _yy1:
                            _tayon = st.selectbox(
                                "Yön",
                                ["Üstüne çıkınca", "Altına inince"],
                                key=f"takeh_al_yon_{_c['kod']}_{_uye}",
                            )
                        with _yy2:
                            _tafiyat = st.text_input(
                                "Hedef fiyat (örn: 2955,00)",
                                key=f"takeh_al_fiyat_{_c['kod']}_{_uye}",
                            )
                        with _yy3:
                            st.write("")
                            if st.button(
                                "Kur",
                                key=f"takeh_al_kur_{_c['kod']}_{_uye}",
                                use_container_width=True,
                            ):
                                try:
                                    _th = fiyat_coz(_tafiyat)
                                except Exception:
                                    _th = 0.0
                                if _th <= 0:
                                    st.error("Geçerli bir hedef fiyat gir (örn: 2955,00).")
                                else:
                                    _alarm_ekle(_c["kod"], _tayon, _th, _uye)
                                    st.success(
                                        f"Alarm kuruldu: {_c['kod']} {_tayon} "
                                        f"{tl_format(_th)}"
                                    )
                                    st.rerun()
                    _hb = _hisse_haber_cek(_c["isim"])
                    st.markdown(f"#### 📰 {_isi} Haberleri")
                    if _hb:
                        for _h in _hb:
                            st.markdown(f"- [🔗 {_h['baslik']}]({_h['link']})")
                    else:
                        st.write("Son 48 saatte ilgili haber bulunamadı.")

        if _uye == YONETICI_ADI:
            st.markdown("### ⚙️ Yönetici Paneli")
            _nickler = uye_listesi_nickler()
            st.metric("Üye Sayısı", len(_nickler))
            if not _nickler:
                st.info("Henüz üye yok.")
            else:
                st.markdown("**Üyeler:** " + ", ".join(_nickler))
                _ip = st.selectbox(
                    "İptal edilecek üye:", _nickler, key="yon_iptal_sec"
                )
                if st.button(
                    "🚫 Üyeliği İptal Et",
                    key="yon_iptal_btn",
                    use_container_width=True,
                ):
                    if uye_iptal(_ip):
                        st.success(f"{_ip} üyeliği iptal edildi ✓")
                        st.rerun()
                    else:
                        st.error("İptal sırasında sorun oluştu.")

    with st.expander(
        f"👥 Üyeler ({len(uye_listesi_nickler())})", expanded=False
    ):
        _nick2 = uye_listesi_nickler()
        if not _nick2:
            st.caption("Henüz üye yok.")
        else:
            st.caption("Kayıtlı kullanıcılar: " + ", ".join(_nick2))

    if _uye and _uye != YONETICI_ADI:
        st.divider()
        with st.expander("💼 Portföy Doktorum", expanded=False):
            st.markdown("**Hisse Ekle**")
            _pfk, _pfa, _pfz, _pfb = st.columns([2, 1, 1, 1])
            _pfsym = _pfk.text_input(
                "Sembol", key="pf_sembol", placeholder="THYAO"
            )
            _pfadet = _pfa.text_input("Adet", key="pf_adet", value="1000")
            _pfalis = _pfz.text_input(
                "Alış Fiyatı", key="pf_alis", placeholder="150.00"
            )
            with _pfb:
                st.write("")
                if st.button(
                    "Ekle", key="pf_ekle", use_container_width=True
                ):
                    _a9 = _takip_sembol_ayristir(_pfsym)
                    if _a9 is None:
                        st.error("Sembol tanınmadı.")
                    else:
                        try:
                            _ad9 = float(_pfadet)
                            _al9 = fiyat_coz(_pfalis)
                            if _ad9 <= 0 or _al9 is None or _al9 <= 0:
                                st.error(
                                    "Adet ve alış fiyatı geçerli olmalı."
                                )
                            else:
                                _portfoy_ekle(
                                    _uye, _a9.get("kod", _pfsym), _ad9, _al9
                                )
                                st.success("Eklendi ✓")
                                st.rerun()
                        except Exception:
                            st.error("Geçerli bir sayı girin.")

            _pr2 = _portfoy_raporu(_uye)
            _sat = _pr2["satirlar"]
            if not _sat:
                st.info(
                    "Portföyünüz boş ya da güncel fiyatlar alınamadı. "
                    "Yukarıdan hisse ekleyerek başlayın."
                )
            else:
                _pz1, _pz2, _pz3, _pz4 = st.columns(4)
                _pz1.metric("Maliyet", tl_format(_pr2["toplam_alis"]))
                _pz2.metric(
                    "Güncel Değer", tl_format(_pr2["toplam_simdi"])
                )
                _pz3.metric(
                    "Kar/Zarar",
                    tl_format(_pr2["toplam_kar"]),
                    f"%{_pr2['toplam_kar_y']:+.2f}",
                )
                _pz4.metric(
                    "Bugünkü Değişim", f"₺{_pr2['gunluk_kar']:+,.0f}"
                )

                st.markdown("**Dağılım (güncel değere göre)**")
                for _sA in _sat:
                    _pay = (
                        _sA["deger"]
                        / max(_pr2["toplam_simdi"], 0.0001)
                        * 100.0
                    )
                    st.progress(
                        min(1.0, _pay / 100.0),
                        text=f"{_sA['sembol']} · %{_pay:.1f}",
                    )

                st.markdown("**Kayıtlar**")
                for _sA in _sat:
                    _a1, _a2, _a3, _a4, _a5, _a6, _a7 = st.columns(
                        [2, 1, 1, 1, 2, 2, 1]
                    )
                    _renk_z = "🟢" if _sA["kar"] >= 0 else "🔴"
                    _a1.markdown(f"{_renk_z} **{_sA['sembol']}**")
                    _a2.markdown(f"{_sA['isim'][:12]}")
                    _a3.markdown(f"{_sA['adet']:g} adet")
                    _a4.markdown(f"Alış {_sA['alis']:.2f}")
                    _a5.markdown(f"Güncel {_sA['son']:.2f}")
                    _a6.markdown(
                        f"**₺{_sA['kar']:+,.0f}** (%{_sA['kar_y']:+.2f})"
                    )
                    if _a7.button(
                        "Sil", key=f"pf_sil_{_sA['id']}"
                    ):
                        _portfoy_sil(_uye, _sA["id"])
                        st.rerun()

                _kar2 = _pr2["kar_edenler"]
                _kayb2 = _pr2["kaybedenler"]
                if _kar2:
                    _env1 = _kar2[0]
                    st.success(
                        f"En çok kazandıran: **{_env1['sembol']}** "
                        f"(₺{_env1['kar']:+,.0f}, %{_env1['kar_y']:+.2f})"
                    )
                if _kayb2:
                    _env2 = _kayb2[0]
                    st.warning(
                        f"En çok kaybettiren: **{_env2['sembol']}** "
                        f"(₺{_env2['kar']:+,.0f}, %{_env2['kar_y']:+.2f})"
                    )
                if len(_sat) >= 2:
                    _gsl = sorted(_sat, key=lambda _x: _x["gunluk"])
                    st.caption(
                        "Bugün sürükleyen: "
                        f"{_gsl[-1]['sembol']} (+₺{_gsl[-1]['gunluk']:,.0f})"
                        " · bugün zayıf: "
                        f"{_gsl[0]['sembol']} ({_gsl[0]['gunluk']:+,.0f})"
                    )


# ==================================================
# TAKİP HİSSELERİ HABER ALARMI (KENAR ÇUBUĞU)
# ==================================================


def _takip_haber_paneli():
    """Kenar çubuğunda: giriş yapan üyenin takip listesindeki
    hisselerin adı geçen en yeni haberleri listeler. 120 saniyede
    bir sessizce tazelenir."""
    try:
        _uk_ = st.session_state.get("bta_uyelik_user")
        if not _uk_:
            return
        with st.sidebar:
            _takk = takip_listesi_getir(_uk_)
            if not _takk:
                return
            _vrm2 = st.session_state.get("bta_haber_veri", {})
            _esless = []
            _goruldu = set()
            for _kat2, _ogeler2 in _vrm2.items():
                for _o2 in _ogeler2[:12]:
                    _ust2 = str(_o2[0]).upper()
                    for _sm_ in _takk:
                        if len(str(_sm_).strip()) < 3:
                            continue
                        if str(_sm_).strip().upper() in _ust2:
                            if str(_o2[0]) in _goruldu:
                                break
                            _goruldu.add(str(_o2[0]))
                            _esless.append((_sm_, _o2[0], _o2[1]))
                            break
            if not _esless:
                return
            with st.expander(
                f"🔔 Takip Hisseleri Haberleri ({len(_esless)})",
                expanded=False,
            ):
                for _sm_, _bas2, _lnk2 in _esless[:8]:
                    _lnk2 = _lnk2 or "#"
                    st.markdown(
                        f'<a href="{_lnk2}" target="_blank" '
                        f'style="color:#ffd166;font-size:12px;'
                        f'text-decoration:none;">'
                        f"🔹 <b>{_sm_}</b> · "
                        f"{str(_bas2)[:70]}"
                        f"{'…' if len(str(_bas2)) > 70 else ''}"
                        "</a>",
                        unsafe_allow_html=True,
                    )
                if len(_esless) > 8:
                    st.caption(f"+{len(_esless) - 8} haber daha")
    except Exception:
        pass


_takip_haber_otomatik = st.fragment(run_every=120)(_takip_haber_paneli)
_takip_haber_otomatik()


# ==================================================
# SAYFA ALT PANELİ: CANLI HABER ŞERİDİ
# ==================================================

st.divider()

with st.container(border=True):
    st.markdown("📰 **Canlı Haber Şeridi** · tıklayınca haber açılır")
    try:
        _akim = son_dakika_haberleri_getir()
    except Exception:
        _akim = []
    if _akim:
        _parcalar = []
        for _b, _l2, _z2 in _akim[:14]:
            _hl = _l2 if _l2 and _l2 != "#" else "#"
            _parcalar.append(
                f'<a class="bta-serit-hb" href="{_hl}" target="_blank">'
                f'<span class="bta-serit-saat">{_z2}</span> {_b}</a>'
            )
        _ileri = "&nbsp;&nbsp;<span style='color:#ffd166'>●</span>&nbsp;&nbsp;"
        _satir = _ileri.join(_parcalar)
        st.markdown(
            "<style>"
            ".bta-serit-kutu{overflow:hidden;border:2px solid rgba(255,209,102,.55);"
            "border-radius:14px;background:linear-gradient(90deg,"
            "#041523,#06263a);padding:18px 0;}"
            ".bta-serit-ic{display:inline-flex;white-space:nowrap;align-items:center;"
            "gap:38px;animation:btaSerit 320s linear infinite;} "
            "@keyframes btaSerit{from{transform:translateX(100%);}"
            "to{transform:translateX(-100%);}} "
            ".bta-serit-hb{color:#ffffff;text-decoration:none;font-size:25px;"
            "font-weight:800;transition:color .2s;} "
            ".bta-serit-hb:hover{color:#ffd166;} "
            ".bta-serit-saat{color:#ffd166;font-size:17px;font-weight:700;}"
            "</style>"
            '<div class="bta-serit-kutu">'
            f'<div class="bta-serit-ic">{_satir}</div>'
            "</div>",
            unsafe_allow_html=True,
        )
    else:
        st.caption("Haber akışı şu an alınamadı.")


# ==================================================
# HİSSE SOR BİLEŞENLERİ: TEKNİK ANALİZ + ÖZET
# ==================================================

with tab_hizli:
    st.markdown(
        sekme_baslik_format(
            "📊", "Teknik Analiz", "#00f5c8"
        ),
        unsafe_allow_html=True
    )

    st.markdown("##### 📊 RSI & Teknik Özet")

    st.caption(
        "Hisse için saatlik, günlük, haftalık ve aylık RSI14 "
        "değerleri ile güncel teknik özet gösterilir. "
        "Yatırım tavsiyesi değildir, bilgilendirme amaçlıdır."
    )

    def _rsi_hesapla(_kapanislar):
        _delta = _kapanislar.diff()
        _kazanc = _delta.clip(lower=0)
        _kayip = -_delta.clip(upper=0)
        _ok = _kazanc.ewm(alpha=1 / 14).mean()
        _ak = _kayip.ewm(alpha=1 / 14).mean().replace(0, float("nan"))
        _rsi = 100 - (100 / (1 + _ok / _ak))

        _temiz = _rsi.dropna()

        return float(_temiz.iloc[-1]) if not _temiz.empty else None

    def _zaman_cek(_sembol, _period, _interval, _guncel_fiyat=None):
        import yfinance as _yf

        _v = _yf.Ticker(_sembol).history(
            period=_period,
            interval=_interval,
            auto_adjust=False
        )

        if _v.empty:
            raise ValueError("Veri bulunamadı.")

        if (
            _guncel_fiyat is not None
            and "Close" in _v
            and pd.isna(_v["Close"].iloc[-1])
        ):
            _v.loc[_v.index[-1], "Close"] = _guncel_fiyat

        return _v

    def _rsi_yorumu(_deger):
        if _deger is None:
            return "veri yok", "#8aa7bb"
        if _deger >= 70:
            return "Yüksek (aşırı alım)", "#ffd166"
        if _deger >= 55:
            return "Güçlü pozitif", "#00f5c8"
        if _deger >= 45:
            return "Nötr", "#eaf4fa"
        if _deger >= 30:
            return "Zayıf", "#4da6ff"
        return "Düşük (aşırı satım)", "#ff5264"

    _sin_kod = st.text_input(
        "BIST Hisse Kodu (RSI Özeti)",
        placeholder="Örn: TRHOL, THYAO, GARAN",
        key="hisse_rsi_kod"
    ).strip().upper()

    _sin_bas = st.button(
        "📊 Analiz",
        use_container_width=True,
        key="hisse_rsi_buton"
    )

    if _sin_bas and not _sin_kod:
        st.error("Lütfen bir hisse kodu girin.")

    if _sin_bas and _sin_kod:
        _sin_sembol = (
            _sin_kod
            if _sin_kod.endswith(".IS")
            else _sin_kod + ".IS"
        )

        try:
            with st.spinner("Teknik özet hazırlanıyor..."):
                _guncel_fiyat = None
                _onceki_kapanis = None

                try:
                    _info = yf.Ticker(_sin_sembol).info

                    for _k in (
                        "currentPrice",
                        "regularMarketPrice",
                        "postMarketPrice"
                    ):
                        _deger = _info.get(_k)

                        if _deger:
                            _guncel_fiyat = float(_deger)
                            break

                    _ok = _info.get("previousClose")

                    if _ok:
                        _onceki_kapanis = float(_ok)

                except Exception:
                    pass

                _rsi_sonuclari = []
                _gunluk_veri = None

                for _ad, _period, _interval in [
                    ("🕐 Saatlik", "1mo", "1h"),
                    ("📅 Günlük", "6mo", "1d"),
                    ("🗓 Haftalık", "2y", "1wk"),
                    ("📆 Aylık", "5y", "1mo")
                ]:
                    _v = _zaman_cek(
                        _sin_sembol,
                        _period,
                        _interval,
                        _guncel_fiyat
                    )

                    if _interval == "1d" and _gunluk_veri is None:
                        _gunluk_veri = _v

                    _rsi_sonuclari.append(
                        (_ad, _rsi_hesapla(_v["Close"]))
                    )

            _kapanis_seri = _gunluk_veri["Close"].copy()
            _kapanislar = _kapanis_seri.dropna()

            if _guncel_fiyat:
                _son_fiyat = _guncel_fiyat
                _onceki_fiyat = (
                    _onceki_kapanis
                    if _onceki_kapanis
                    else float(_kapanislar.iloc[-1])
                )
                _gun_degisim = (
                    (_son_fiyat - _onceki_fiyat) / _onceki_fiyat * 100
                )
            else:
                _son_fiyat = float(_kapanislar.iloc[-1])
                _onceki_fiyat = float(_kapanislar.iloc[-2])
                _gun_degisim = (
                    (_son_fiyat - _onceki_fiyat) / _onceki_fiyat * 100
                )

            _bes = _kapanislar.tail(5)

            if _guncel_fiyat and pd.isna(_kapanis_seri.iloc[-1]):
                _bes = _kapanis_seri.dropna().tail(4).to_list() + [
                    _guncel_fiyat
                ]

            _bes_degisim = (
                (_bes.iloc[-1] - _bes.iloc[0]) / _bes.iloc[0] * 100
                if hasattr(_bes, "iloc")
                else (_bes[-1] - _bes[0]) / _bes[0] * 100
            )

            _deg_renk = (
                "#00f5c8"
                if _gun_degisim >= 0
                else "#ff5264"
            )

            _rsi_satirlar = ""

            for _ad, _rsi in _rsi_sonuclari:
                _yorum, _rel_renk = _rsi_yorumu(_rsi)
                _rsi_metin = f"{_rsi:.1f}" if _rsi is not None else "-"

                _rsi_satirlar += (
                    f'<div class="hisse-arama-alt" style="'
                    f'justify-content:space-between;">'
                    f'<span>{_ad}</span>'
                    f'<span style="color:{_rel_renk};font-weight:800;">'
                    f'RSI {_rsi_metin} · {_yorum}</span>'
                    f'</div>'
                )

            st.markdown(
                f"""
                <div class="hisse-arama-kart">
                    <div class="hisse-arama-ust">
                        <span class="hisse-arama-kod">
                            {_sin_kod}
                        </span>
                        <span class="hisse-arama-fiyat"
                              style="color:{_deg_renk};">
                            ₺ {tl_format(_son_fiyat)}
                        </span>
                    </div>
                    <div class="hisse-arama-degisim"
                         style="color:{_deg_renk};">
                        Günlük: {_gun_degisim:+.2f}% · Son 5 gün: {_bes_degisim:+.2f}%
                    </div>
                    {_rsi_satirlar}
                </div>
                """,
                unsafe_allow_html=True
            )

            st.caption(
                "Güncel fiyat canlı veriden alınır; son işlem günü "
                "henüz kapanmamışsa günlük/haftalık/aylık veriler "
                "buna göre tamamlanır. RSI son bara göre hesaplanır. "
                "Yatırım tavsiyesi değildir."
            )

            st.markdown("#### 💎 Sermaye · Öz Sermaye · Defter Değeri")

            try:
                _t3 = temel_analiz_getir(_sin_kod)

                _k3 = st.columns(4)
                _k3[0].metric(
                    "Ödenmiş Sermaye*",
                    temel_buyuk_sayi_format(_t3["sermaye"])
                )
                _k3[1].metric(
                    "Özsermaye",
                    temel_buyuk_sayi_format(_t3["oz_sermaye"])
                )
                _k3[2].metric(
                    "Defter Değeri",
                    tl_format(_t3["defter_degeri"])
                )
                _k3[3].metric(
                    "Pay Adedi",
                    temel_buyuk_sayi_format(_t3["pay_adedi"])
                )
                st.caption(
                    "*Ödenmiş sermaye, Yahoo pay adedi üzerinden "
                    "(1 TL nominal) yaklaşık değerdir."
                )
            except Exception:
                st.caption("Sermaye/öz sermaye verisi alınamadı.")

            st.markdown("#### 📆 MACD (Günlük/Aylık/Yıllık) & 💧 Likidite")

            try:
                _ml = _hisse_macd_likidite(_sin_sembol)

                _k4 = st.columns(4)
                _k4[0].metric(
                    "MACD Günlük",
                    f"{_ml['macd_gunluk']:+.3f}"
                    if _ml["macd_gunluk"] is not None else "-"
                )
                _k4[1].metric(
                    "MACD Aylık",
                    f"{_ml['macd_aylik']:+.3f}"
                    if _ml["macd_aylik"] is not None else "-"
                )
                _k4[2].metric(
                    "MACD Yıllık",
                    f"{_ml['macd_yillik']:+.3f}"
                    if _ml["macd_yillik"] is not None else "-"
                )
                _k4[3].metric(
                    "MACD Histogram",
                    _macd_ozet(_ml["macd_gunluk_hist"])
                )

                _k5 = st.columns(4)
                _k5[0].metric(
                    "Son Gün Hacim",
                    temel_adet_format(_ml["hacim_son"])
                )
                _k5[1].metric(
                    "Ort. Hacim (20g)",
                    temel_adet_format(_ml["hacim_ort20"])
                )
                _k5[2].metric(
                    "Son Gün İşlem Hacmi",
                    temel_buyuk_sayi_format(_ml["para_son"])
                )
                _k5[3].metric(
                    "Ort. İşlem Hacmi (20g)",
                    temel_buyuk_sayi_format(_ml["para_ort20"])
                )
                st.caption(
                    "MACD(12,26,9) 10 yıllık günlük kapanıştan; aylık/ "
                    "yıllık, kapanışın yeniden örneklenmesiyle hesaplanır. "
                    "Likidite, Yahoo'nun günlük hacim/para verisidir."
                )
            except Exception as _ml_hata:
                st.caption(
                    f"MACD/likidite alınamadı: {_ml_hata}"
                )

        except Exception as _sin_hata:
            st.error(
                f"'{_sin_kod}' için teknik özet üretilemedi: "
                f"{_sin_hata}"
            )


# ==================================================
# TEKNİK ANALİZ
# ==================================================

_KLC_SABLON = r"""
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8" />
<style>
  html, body { margin: 0; padding: 0; background: #0b1a24;
    font-family: system-ui, -apple-system, Segoe UI, sans-serif; }
  #bta-bar { display: flex; flex-wrap: wrap; gap: 5px; align-items: center;
    padding: 8px; background: #0f2430; border-bottom: 1px solid #1c3a4a; }
  #bta-bar button, #bta-bar select { background: #12303f; color: #eaf4fa;
    border: 1px solid #1f4a5f; border-radius: 6px;
    padding: 4px 8px; font-size: 12px; cursor: pointer; }
  #bta-bar button:hover { background: #1a4256; }
  #bta-bar button.aktif { background: #00f5c8; color: #04222b;
    font-weight: 700; }
  #bta-bar .bta-ayrac { width: 1px; align-self: stretch;
    background: #1f4a5f; margin: 0 4px; }
  #bta-klc { width: 100%; height: 560px; }
</style>
</head>
<body>
  <div id="bta-bar">
    <select id="bta-tur" title="Grafik turu">
      <option value="candle_solid">Mum</option>
      <option value="candle_stroke">Bos mum</option>
      <option value="ohlc">Bar</option>
      <option value="area">Alan</option>
    </select>
    <span class="bta-ayrac"></span>
    <button data-o="__IMLEC__">&#10021; Imlec</button>
    <button data-o="segment">&#8599; Trend</button>
    <button data-o="rayLine">&#8599; Isin</button>
    <button data-o="horizontalStraightLine">&#8212; Yatay</button>
    <button data-o="verticalStraightLine">| Dikey</button>
    <button data-o="priceLine">&#8378; Fiyat</button>
    <button data-o="parallelStraightLine">&#8741; Kanal</button>
    <button data-o="fibonacciLine">&#402; Fibo</button>
    <button data-o="rect">&#9645; Dikdortgen</button>
    <button data-o="circle">&#9675; Daire</button>
    <button data-o="arc">&#9697; Yay</button>
    <button data-o="polygon">&#11045; Poligon</button>
    <button data-o="simpleAnnotation">T Metin</button>
    <span class="bta-ayrac"></span>
    <button data-ind="MA">MA</button>
    <button data-ind="EMA">EMA</button>
    <button data-ind="BOLL">BOLL</button>
    <button data-ind="VOL">Hacim</button>
    <button data-ind="RSI">RSI</button>
    <button data-ind="MACD">MACD</button>
    <button data-ind="KDJ">KDJ</button>
    <span class="bta-ayrac"></span>
    <button id="bta-geri">&#8630; Geri Al</button>
    <button id="bta-temizle">&#128465; Temizle</button>
    <button id="bta-disari">&#128190; Disa Aktar</button>
    <button id="bta-ice-buton">&#128193; Ice Aktar</button>
    <input type="file" id="bta-ice" accept=".json,application/json"
           style="display:none" />
    <button id="bta-kaydet">&#128248; Kaydet (PNG)</button>
  </div>
  <div id="bta-klc"></div>
  <script src="https://cdn.jsdelivr.net/npm/klinecharts@9/dist/klinecharts.min.js"></script>
  <script>
  (function(){
    var VERI = __VERI__;
    var OTO = __OTOMATIK__;
    var ANAHTAR = 'bta_cizim___ANAHTAR__';
    var chart = klinecharts.init('bta-klc');

    try {
      chart.setStyles({
        grid: { horizontal: { color: '#122a36' },
                vertical: { color: '#122a36' } },
        candle: { bar: { upColor: '#00f5c8', downColor: '#ff5264',
                         noChangeColor: '#8aa0ad' } },
        xAxis: { axisLine: { color: '#1c3a4a' },
                 tickText: { color: '#9fb3c0' } },
        yAxis: { axisLine: { color: '#1c3a4a' },
                 tickText: { color: '#9fb3c0' } }
      });
    } catch (e) {}

    chart.applyNewData(VERI);

    var ids = [];
    var otoIds = [];

    function overlayOzet(o) {
      return {
        name: o.name,
        points: JSON.parse(JSON.stringify(o.points || [])),
        lock: o.lock,
        visible: o.visible
      };
    }

    function yaz() {
      var liste = [];
      for (var i = 0; i < ids.length; i++) {
        var o = chart.getOverlayById(ids[i]);
        if (o && o.name) { liste.push(overlayOzet(o)); }
      }
      try { localStorage.setItem(ANAHTAR, JSON.stringify(liste)); } catch (e) {}
    }

    function oku() {
      var ham = null;
      try { ham = localStorage.getItem(ANAHTAR); } catch (e) {}
      if (!ham) { return; }
      var liste = [];
      try { liste = JSON.parse(ham); } catch (e) { return; }
      for (var i = 0; i < liste.length; i++) {
        try {
          var id = chart.createOverlay(liste[i]);
          if (id) { ids.push(id); }
        } catch (e) {}
      }
    }

    function otoCiz() {
      for (var i = 0; i < OTO.length; i++) {
        try {
          var id = chart.createOverlay(OTO[i]);
          if (id) { otoIds.push(id); }
        } catch (e) {}
      }
    }

    otoCiz();
    oku();
    setInterval(yaz, 900);

    var butonlar = document.querySelectorAll('#bta-bar button[data-o]');
    butonlar.forEach(function(btn){
      btn.addEventListener('click', function(){
        butonlar.forEach(function(b){ b.classList.remove('aktif'); });
        btn.classList.add('aktif');
        var ad = btn.getAttribute('data-o');
        if (ad === '__IMLEC__') { return; }
        try {
          var id = chart.createOverlay({ name: ad });
          if (id) { ids.push(id); }
        } catch (e) { console.warn(e); }
      });
    });

    var turSec = document.getElementById('bta-tur');
    var tur = 'candle_solid';
    try { tur = localStorage.getItem('bta_tur') || 'candle_solid'; } catch (e) {}
    turSec.value = tur;
    function turUygula(t) {
      try { chart.setStyles({ candle: { type: t } }); } catch (e) {}
      try { localStorage.setItem('bta_tur', t); } catch (e) {}
    }
    turUygula(tur);
    turSec.addEventListener('change', function(){ turUygula(turSec.value); });

    var gost = {};
    try {
      gost = JSON.parse(localStorage.getItem('bta_gost') || '{}');
    } catch (e) { gost = {}; }
    function gostKaydet() {
      try { localStorage.setItem('bta_gost', JSON.stringify(gost)); } catch (e) {}
    }
    function indAc(kap) {
      var paneId = null;
      try {
        if (kap === 'MA' || kap === 'EMA' || kap === 'BOLL') {
          paneId = chart.createIndicator(kap, true, { id: 'candle_pane' });
        } else {
          paneId = chart.createIndicator(
            kap, false, { id: 'bta_' + kap.toLowerCase() }
          );
        }
      } catch (e) { paneId = null; }
      if (paneId) { gost[kap] = paneId; gostKaydet(); }
    }
    function indKapa(kap) {
      try {
        if (typeof gost[kap] === 'string') {
          chart.removeIndicator(gost[kap], kap);
        }
      } catch (e) {}
      delete gost[kap];
      gostKaydet();
    }
    function indButonlari() {
      var ib = document.querySelectorAll('#bta-bar button[data-ind]');
      ib.forEach(function(b){
        var ad = b.getAttribute('data-ind');
        if (gost[ad]) { b.classList.add('aktif'); }
        b.addEventListener('click', function(){
          if (gost[ad]) { indKapa(ad); b.classList.remove('aktif'); }
          else { indAc(ad); b.classList.add('aktif'); }
        });
      });
    }
    indButonlari();
    for (var gk in gost) {
      if (gost.hasOwnProperty(gk)) { indAc(gk); }
    }

    document.getElementById('bta-geri').addEventListener('click', function(){
      while (ids.length) {
        var id = ids.pop();
        if (chart.getOverlayById(id)) { chart.removeOverlay(id); yaz(); return; }
      }
      while (otoIds.length) {
        var id2 = otoIds.pop();
        if (chart.getOverlayById(id2)) { chart.removeOverlay(id2); return; }
      }
    });

    document.getElementById('bta-temizle').addEventListener('click', function(){
      var i;
      for (i = 0; i < ids.length; i++) {
        if (chart.getOverlayById(ids[i])) { chart.removeOverlay(ids[i]); }
      }
      for (i = 0; i < otoIds.length; i++) {
        if (chart.getOverlayById(otoIds[i])) { chart.removeOverlay(otoIds[i]); }
      }
      ids = []; otoIds = []; yaz();
    });

    document.getElementById('bta-disari').addEventListener('click', function(){
      var liste = [];
      for (var i = 0; i < ids.length; i++) {
        var o = chart.getOverlayById(ids[i]);
        if (o && o.name) { liste.push(overlayOzet(o)); }
      }
      var blob = new Blob(
        [JSON.stringify(liste)], { type: 'application/json' }
      );
      var a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'bta-cizimler-__DOSYA__.json';
      document.body.appendChild(a); a.click(); a.remove();
    });

    document.getElementById('bta-ice-buton').addEventListener('click', function(){
      document.getElementById('bta-ice').click();
    });
    document.getElementById('bta-ice').addEventListener('change', function(ev){
      var f = ev.target.files && ev.target.files[0];
      if (!f) { return; }
      var rd = new FileReader();
      rd.onload = function(){
        var liste = [];
        try { liste = JSON.parse(rd.result); } catch (e) { return; }
        for (var i = 0; i < liste.length; i++) {
          try {
            var id = chart.createOverlay(liste[i]);
            if (id) { ids.push(id); }
          } catch (e) {}
        }
        yaz();
      };
      rd.readAsText(f);
    });

    document.getElementById('bta-kaydet').addEventListener('click', function(){
      var resim = chart.getConvertPictureUrl(true, 'png', '#0b1a24');
      var a = document.createElement('a');
      a.href = resim;
      a.download = 'bta-__DOSYA__.png';
      document.body.appendChild(a); a.click(); a.remove();
    });
  })();
  </script>
</body>
</html>
"""


with tab_grafik:
    st.markdown(
        sekme_baslik_format(
            "\U0001F4C8", "Grafik \u00c7izimi ve Analiz Ara\u00e7lar\u0131", "#ffd166"
        ),
        unsafe_allow_html=True
    )

    st.caption(
        "Hisse kodunu yaz (\u00f6r. THYAO, GARAN, ASELS). BIST hisseleri "
        "i\u00e7in Borsa \u0130stanbul kaynakl\u0131 resm\u00ee gecikmeli "
        "(\u2248 15 dk) veri, di\u011ferleri i\u00e7in yFinance kullan\u0131l\u0131r. "
        "Grafik t\u00fcr\u00fcn\u00fc, g\u00f6stergeleri ve \u00e7izim "
        "ara\u00e7lar\u0131n\u0131 \u00fcstteki \u00e7ubuktan se\u00e7."
    )

    @st.cache_data(ttl=3600, show_spinner=False)
    def _yf_sembol_bul(_s):
        _s = str(_s).strip().upper()

        if ":" in _s:
            _s = _s.split(":")[-1]

        _s = _s.replace(".IS", "")

        if _s.endswith("=X") or _s.endswith("-USD"):
            _adaylar = [_s]
        else:
            _adaylar = [_s + ".IS", _s, _s + "=X", _s + "-USD"]

        for _aday in _adaylar:
            try:
                _v = yf.Ticker(_aday).history(
                    period="5d", interval="1d", auto_adjust=False
                )
                if not _v.empty:
                    return _aday
            except Exception:
                continue

        raise ValueError("Sembol bulunamad\u0131: " + _s)

    @st.cache_data(ttl=300, show_spinner=False)
    def _grafik_veri_cek(_yf_sembol, _periyot, _aralik):
        if _aralik == "1d":
            _temiz = _bist_sembol_mu(_yf_sembol)
            if _temiz:
                try:
                    return _bist_gecmis(
                        _temiz, _BIST_PERIYOT_GUN.get(_periyot, 400)
                    )
                except Exception:
                    pass
        veri = yf.Ticker(_yf_sembol).history(
            period=_periyot, interval=_aralik, auto_adjust=False
        )
        if veri.empty:
            raise ValueError("Veri bulunamad\u0131.")
        return veri

    @st.cache_data(ttl=120, show_spinner=False)
    def _son_fiyat(_yf_sembol):
        _temiz = _bist_sembol_mu(_yf_sembol)
        if _temiz:
            try:
                return float(_bist_kot(_temiz)["fiyat"])
            except Exception:
                pass
        _v = yf.Ticker(_yf_sembol).history(
            period="5d", interval="1d", auto_adjust=False
        )
        if _v.empty:
            raise ValueError("Veri yok")
        return float(_v["Close"].iloc[-1])

    def _otomatik_cizimler(_veri):
        _v = _veri.tail(90)
        if _v.empty:
            return []
        _ts_ilk = int(_v.index[0].timestamp() * 1000)
        _ts_son = int(_v.index[-1].timestamp() * 1000)
        _yuksek = float(_v["High"].max())
        _dusuk = float(_v["Low"].min())
        _son20 = _v.tail(20)
        _direnc = float(_son20["High"].max())
        _destek = float(_son20["Low"].min())
        return [
            {"name": "horizontalStraightLine",
             "points": [{"timestamp": _ts_son, "value": _direnc}],
             "lock": True, "visible": True},
            {"name": "horizontalStraightLine",
             "points": [{"timestamp": _ts_son, "value": _destek}],
             "lock": True, "visible": True},
            {"name": "fibonacciLine",
             "points": [{"timestamp": _ts_ilk, "value": _dusuk},
                        {"timestamp": _ts_son, "value": _yuksek}],
             "lock": True, "visible": True}
        ]

    _periyot_secenek = {
        "1 Ay (g\u00fcnl\u00fck)": ("1mo", "1d"),
        "3 Ay (g\u00fcnl\u00fck)": ("3mo", "1d"),
        "6 Ay (g\u00fcnl\u00fck)": ("6mo", "1d"),
        "1 Y\u0131l (g\u00fcnl\u00fck)": ("1y", "1d"),
        "2 Y\u0131l (g\u00fcnl\u00fck)": ("2y", "1d"),
        "5 Y\u0131l (haftal\u0131k)": ("5y", "1wk"),
        "1 Ay (saatlik)": ("1mo", "1h"),
        "5 G\u00fcn (15 dk)": ("5d", "15m")
    }

    _gk1, _gk2 = st.columns([2, 1])

    with _gk1:
        sembol = st.text_input(
            "Sembol",
            value="THYAO",
            placeholder="\u00d6rn: THYAO, GARAN, ASELS, AAPL",
            key="teknik_sembol"
        ).strip().upper()

    with _gk2:
        _periyot_etiket = st.selectbox(
            "Periyot",
            list(_periyot_secenek.keys()),
            index=3,
            key="teknik_periyot_sec"
        )

    _oto_seviye = st.checkbox(
        "Otomatik destek/diren\u00e7 ve Fibonacci \u00e7iz",
        value=True,
        key="teknik_oto_seviye"
    )

    _g_buton = st.button(
        "\U0001F4C8 Grafi\u011fi \u00c7iz",
        use_container_width=True,
        key="teknik_analiz_buton"
    )

    if _g_buton and not sembol:
        st.error("L\u00fctfen bir sembol girin.")

    if _g_buton and sembol:
        st.session_state["teknik_aktif"] = sembol

    _teknik_sembol = st.session_state.get("teknik_aktif", "THYAO")

    if isinstance(_teknik_sembol, (tuple, list)):
        _teknik_sembol = _teknik_sembol[0]

    _teknik_sembol = str(_teknik_sembol).strip().upper()
    _teknik_periyot, _teknik_aralik = _periyot_secenek[_periyot_etiket]

    if _teknik_sembol:
        try:
            with st.spinner("Veri \u00e7ekiliyor, grafik haz\u0131rlan\u0131yor..."):
                _yf_sembol = _yf_sembol_bul(_teknik_sembol)
                _g_veri = _grafik_veri_cek(
                    _yf_sembol, _teknik_periyot, _teknik_aralik
                )

            _kayitlar = []

            for _g_ts, _g_satir in _g_veri.iterrows():
                _hacim = _g_satir.get("Volume")

                _kayitlar.append({
                    "timestamp": int(_g_ts.timestamp() * 1000),
                    "open": float(_g_satir["Open"]),
                    "high": float(_g_satir["High"]),
                    "low": float(_g_satir["Low"]),
                    "close": float(_g_satir["Close"]),
                    "volume": (
                        float(_hacim) if pd.notna(_hacim) else 0.0
                    )
                })

            _oto_cizimler = []

            if _oto_seviye:
                try:
                    _oto_cizimler = _otomatik_cizimler(_g_veri)
                except Exception:
                    _oto_cizimler = []

            _klc_html = _KLC_SABLON.replace(
                "__VERI__", json.dumps(_kayitlar)
            ).replace(
                "__OTOMATIK__", json.dumps(_oto_cizimler)
            ).replace(
                "__ANAHTAR__", _yf_sembol.replace(".", "_")
            ).replace(
                "__DOSYA__", _teknik_sembol.replace(".", "_")
            )

            components.html(_klc_html, height=660, scrolling=False)

            st.caption(
                f"{_yf_sembol} \u2022 {_periyot_etiket} \u2022 Veriler "
                "yFinance'ten al\u0131n\u0131r. \u00dcstteki \u00e7ubuktan grafik "
                "t\u00fcr\u00fcn\u00fc (Mum/Bar/Alan), g\u00f6stergeleri (MA, EMA, "
                "BOLL, Hacim, RSI, MACD, KDJ) ve \u00e7izim ara\u00e7lar\u0131n\u0131 se\u00e7. "
                "\u21b6 Geri Al, \U0001F5D1 Temizle, \U0001F4BE D\u0131\u015fa Aktar / "
                "\U0001F4C2 \u0130\u00e7e Aktar ile \u00e7izimleri dosya olarak ta\u015f\u0131, "
                "\U0001F4F8 Kaydet (PNG) ile resmi indir. \u00c7izimler ve g\u00f6stergeler "
                "otomatik kaydedilir. Veriler yakla\u015f\u0131k 15 dakika gecikmelidir. Yat\u0131r\u0131m tavsiyesi de\u011fildir."
            )
        except Exception as _g_hata:
            st.error(f"Grafik olu\u015fturulamad\u0131: {_g_hata}")

    st.divider()

    st.markdown(
        sekme_baslik_format(
            "\U0001F500", "\u0130ki Sembol Kar\u015f\u0131la\u015ft\u0131r", "#7ec8ff"
        ),
        unsafe_allow_html=True
    )

    st.caption(
        "\u0130ki hisseyi ayn\u0131 grafikte y\u00fczde de\u011fi\u015fim olarak k\u0131yaslar "
        "(ikisi de ba\u015flang\u0131\u00e7ta 100 kabul edilir)."
    )

    _kk1, _kk2, _kk3 = st.columns([2, 2, 1])

    with _kk1:
        _kars_sembol = st.text_input(
            "2. Sembol", value="", placeholder="\u00d6rn: GARAN",
            key="kars_sembol"
        ).strip().upper()

    with _kk2:
        _kars_periyot = st.selectbox(
            "Kar\u015f\u0131la\u015ft\u0131rma periyodu",
            ["1mo", "3mo", "6mo", "1y", "2y", "5y"],
            index=3, key="kars_periyot",
            format_func=lambda _x: {
                "1mo": "1 Ay", "3mo": "3 Ay", "6mo": "6 Ay",
                "1y": "1 Y\u0131l", "2y": "2 Y\u0131l", "5y": "5 Y\u0131l"
            }.get(_x, _x)
        )

    with _kk3:
        st.write("")
        _kars_buton = st.button(
            "Kar\u015f\u0131la\u015ft\u0131r", key="kars_buton", use_container_width=True
        )

    if _kars_buton:
        if not _kars_sembol:
            st.error("2. sembol\u00fc gir.")
        else:
            st.session_state["kars_aktif"] = (
                _teknik_sembol, _kars_sembol, _kars_periyot
            )

    _kars_aktif = st.session_state.get("kars_aktif")

    if _kars_aktif:
        try:
            _ks1, _ks2, _ksp = _kars_aktif

            with st.spinner("Kar\u015f\u0131la\u015ft\u0131rma haz\u0131rlan\u0131yor..."):
                _ys1 = _yf_sembol_bul(_ks1)
                _ys2 = _yf_sembol_bul(_ks2)
                _vd1 = _grafik_veri_cek(_ys1, _ksp, "1d")
                _vd2 = _grafik_veri_cek(_ys2, _ksp, "1d")

            if _PLOTLY_VAR:
                _s1 = (_vd1["Close"] / _vd1["Close"].iloc[0]) * 100.0
                _s2 = (_vd2["Close"] / _vd2["Close"].iloc[0]) * 100.0
                _fig = go.Figure()
                _fig.add_trace(go.Scatter(
                    x=_s1.index, y=_s1.values, name=_ks1,
                    line=dict(color="#00f5c8")
                ))
                _fig.add_trace(go.Scatter(
                    x=_s2.index, y=_s2.values, name=_ks2,
                    line=dict(color="#ffb454")
                ))
                _fig.update_layout(
                    height=360, margin=dict(l=10, r=10, t=30, b=10),
                    paper_bgcolor="#0b1a24", plot_bgcolor="#0b1a24",
                    font=dict(color="#d8e6ef"),
                    legend=dict(orientation="h", y=1.1),
                    xaxis=dict(gridcolor="#122a36"),
                    yaxis=dict(gridcolor="#122a36",
                               title="100 = ba\u015flang\u0131\u00e7")
                )
                st.plotly_chart(_fig, use_container_width=True)

                _d1 = float(
                    _vd1["Close"].iloc[-1] / _vd1["Close"].iloc[0] - 1
                ) * 100
                _d2 = float(
                    _vd2["Close"].iloc[-1] / _vd2["Close"].iloc[0] - 1
                ) * 100
                st.info(
                    f"{_ks1}: {_d1:+.2f}%  \u2022  {_ks2}: {_d2:+.2f}%  "
                    f"\u2022  Fark: {(_d1 - _d2):+.2f} puan"
                )
            else:
                st.warning("Kar\u015f\u0131la\u015ft\u0131rma grafi\u011fi i\u00e7in plotly gerekli.")
        except Exception as _kh:
            st.error(f"Kar\u015f\u0131la\u015ft\u0131rma yap\u0131lamad\u0131: {_kh}")


    st.divider()

    st.markdown(
        sekme_baslik_format(
            "📝", "Analiz Notu Kaydet", "#00f5c8"
        ),
        unsafe_allow_html=True
    )

    st.caption(
        "Sembol ve analiz notunu kaydet; kayıtlar aşağıda listelenir "
        "ve sayfa yenilense de kalır. Çizdiğin grafiği de eklemek "
        "için önce grafikteki 📸 Kaydet (PNG) ile indir, sonra "
        "aşağıdaki 'Çizdiğin grafik resmi' kutusuna yükle. Kayıtta "
        "📈 Çizilen Grafiği Göster'e basınca grafik açılır."
    )

    with st.form("analiz_not_form", clear_on_submit=True):
        _not_c1, _not_c2 = st.columns([2, 1])

        with _not_c1:
            _not_kullanici = st.text_input(
                "Kullanıcı adı",
                value="Hissedar"
            )

        with _not_c2:
            _not_sembol = st.text_input(
                "Sembol",
                value=_teknik_sembol
            )

        _not_metni = st.text_area(
            "Analiz notu",
            height=90,
            placeholder="Örn: 42.50 desteği üzerinde, hedef 45.00..."
        )

        yuklenen_grafik = st.file_uploader(
            "Çizdiğin grafik resmi (opsiyonel)",
            type=["png", "jpg", "jpeg"],
            key="analiz_not_grafik"
        )

        if yuklenen_grafik is not None:
            st.caption(
                "Önizleme: bu resim notla birlikte kaydedilir."
            )
            st.image(yuklenen_grafik, use_container_width=True)

        _not_kaydet = st.form_submit_button(
            "💾 Notu Kaydet",
            use_container_width=True
        )

    if _not_kaydet:
        if not _not_metni.strip():
            st.error("Analiz notu boş bırakılamaz.")
        else:
            _grafik_veri_url = ""

            if yuklenen_grafik is not None:
                try:
                    _grafik_veri_url = grafik_resmi_verisi(
                        yuklenen_grafik
                    )
                except Exception:
                    _grafik_veri_url = ""

            analiz_notu_ekle(
                _not_kullanici.strip() or "Hissedar",
                _not_sembol.strip().upper(),
                _not_metni.strip(),
                _grafik_veri_url
            )
            st.success("Analiz notu kaydedildi.")
            st.rerun()

    _kayitli_notlar = analiz_notlari_oku()

    if not _kayitli_notlar.empty:
        st.markdown("#### 🗂 Kayıtlı Analiz Notları")

        if is_admin:
            _na1, _na2 = st.columns([3, 1])

            with _na2:
                if st.button(
                    "🗑️ Tümünü Sil",
                    use_container_width=True,
                    key="analiz_notu_tumunu_sil"
                ):
                    analiz_notlari_tumunu_sil()
                    st.success("Tüm analiz notları silindi.")
                    st.rerun()

        for _n_idx, _not in _kayitli_notlar.tail(20).iloc[::-1].iterrows():
            with st.container(border=True):
                _nk1, _nk2 = st.columns([6, 1])

                with _nk1:
                    st.markdown(
                        f"**{_not['sembol']}** · {_not['kullanici']} · "
                        f"{_not['tarih']}"
                    )
                    st.write(_not["not_metni"])

                    _not_resim = (
                        _not["resim"]
                        if "resim" in _not.index else ""
                    )

                    if pd.isna(_not_resim):
                        _not_resim = ""

                    _not_resim = str(_not_resim).strip()

                    if _not_resim.startswith("data:image"):
                        _resim_bayt = _veri_url_bytes(_not_resim)

                        with st.expander(
                            "📈 Çizilen Grafiği Göster"
                        ):
                            if _resim_bayt:
                                st.image(
                                    _resim_bayt,
                                    use_container_width=True
                                )

                                st.download_button(
                                    "⬇️ Grafiği İndir",
                                    data=_resim_bayt,
                                    file_name=(
                                        f"grafik_{_not['not_id']}"
                                        ".jpg"
                                    ),
                                    mime="image/jpeg",
                                    key=(
                                        f"not_resim_indir_{_n_idx}"
                                    )
                                )

                with _nk2:
                    if is_admin and st.button(
                        "🗑️ Sil",
                        key=f"analiz_notu_sil_{_n_idx}",
                        use_container_width=True
                    ):
                        analiz_notu_sil(_not["not_id"])
                        st.success("Not silindi.")
                        st.rerun()
    else:
        st.info("Henüz kayıtlı analiz notu yok.")


# ==================================================
# TEMEL ANALİZ ÖZETİ
# ==================================================

with tab_temel:
    st.caption(
        "Hisse kodu yazın; değerleme (F/K, PD/DD), kârlılık, "
        "bilanço ve piyasa göstergeleri Yahoo Finance verisiyle "
        "özetlenir. Yatırım tavsiyesi değildir."
    )

    col_temel_hisse, col_temel_buton = st.columns([3, 1])

    with col_temel_hisse:
        _temel_hisse = st.text_input(
            "Hisse Kodu",
            placeholder="Örn: THYAO, ASELS, EREGL",
            key="temel_hisse"
        ).strip().upper()

    with col_temel_buton:
        _temel_baslat = st.button(
            "🧾 Özeti Getir",
            use_container_width=True,
            key="temel_getir_buton"
        )

    if _temel_baslat and not _temel_hisse:
        st.error("Lütfen bir hisse kodu girin.")

    if _temel_baslat and _temel_hisse:
        _temel = None

        try:
            with st.spinner("Temel analiz özeti hazırlanıyor..."):
                _temel = temel_analiz_getir(_temel_hisse)
        except Exception as _temel_hata:
            st.warning(
                f"{_temel_hisse} için temel analiz verisi alınamadı "
                f"({_temel_hata}). Kod doğru mu kontrol edin, BIST "
                "hisseleri için sadece kodu yazın (Örn: THYAO)."
            )

        if _temel:
            def _temel_satir(_liste):
                _kolonlar = st.columns(len(_liste))

                for _kol, (_etiket, _deger) in zip(_kolonlar, _liste):
                    _kol.metric(_etiket, _deger)

            st.subheader(f"🧾 {_temel['ad']}")

            if _temel["sektor"]:
                st.caption(f"Sektör: {_temel['sektor']}")

            st.markdown("**📐 Değerleme**")
            _temel_satir([
                ("F/K", sayi_format(_temel["fk"])),
                ("İleri F/K", sayi_format(_temel["ileri_fk"])),
                ("PD/DD", sayi_format(_temel["pddd"])),
                ("FD/FAVÖK", sayi_format(_temel["fd_favok"])),
            ])
            _temel_satir([
                ("Fiyat/Satış", sayi_format(_temel["fiyat_satis"])),
                ("Hisse Başı Kâr", tl_format(_temel["hbk"])),
                ("Defter Değeri", tl_format(_temel["defter_degeri"])),
                (
                    "Piyasa Değeri",
                    temel_buyuk_sayi_format(_temel["piyasa_degeri"])
                ),
            ])

            st.markdown("**💹 Kârlılık ve Büyüme**")
            _temel_satir([
                ("Özsermaye Kârlılığı", temel_yuzde_format(_temel["roe"])),
                ("Aktif Kârlılığı", temel_yuzde_format(_temel["roa"])),
                ("Net Kâr Marjı", temel_yuzde_format(_temel["net_marj"])),
                (
                    "Faaliyet Marjı",
                    temel_yuzde_format(_temel["faaliyet_marj"])
                ),
            ])
            _temel_satir([
                ("Brüt Marj", temel_yuzde_format(_temel["brut_marj"])),
                (
                    "Gelir Büyümesi",
                    temel_yuzde_format(_temel["gelir_buyume"])
                ),
                (
                    "Kâr Büyümesi",
                    temel_yuzde_format(_temel["kar_buyume"])
                ),
                (
                    "Temettü Verimi",
                    temel_yuzde_format(_temel["temettu_verimi"])
                ),
            ])

            st.markdown("**🏦 Bilanço**")
            _temel_satir([
                (
                    "Borç/Özsermaye",
                    temel_yuzde_format(_temel["borc_ozsermaye"])
                ),
                ("Cari Oran", sayi_format(_temel["cari_oran"])),
                (
                    "Toplam Nakit",
                    temel_buyuk_sayi_format(_temel["nakit"])
                ),
                (
                    "Toplam Borç",
                    temel_buyuk_sayi_format(_temel["borc"])
                ),
            ])

            st.markdown("**🧭 Sermaye & Öz Sermaye**")
            _temel_satir([
                (
                    "Ödenmiş Sermaye*",
                    temel_buyuk_sayi_format(_temel["sermaye"])
                ),
                (
                    "Özsermaye",
                    temel_buyuk_sayi_format(_temel["oz_sermaye"])
                ),
                (
                    "Defter Değeri",
                    tl_format(_temel["defter_degeri"])
                ),
                (
                    "Pay Adedi",
                    temel_buyuk_sayi_format(_temel["pay_adedi"])
                ),
            ])
            st.caption(
                "*Ödenmiş sermaye, Yahoo pay adedi üzerinden "
                "(1 TL nominal) yaklaşık değerdir."
            )

            st.markdown("**📆 MACD (Günlük/Aylık/Yıllık)**")
            try:
                _ml = _hisse_macd_likidite(_temel_hisse + ".IS")

                _temel_satir([
                    (
                        "MACD Günlük",
                        f"{_ml['macd_gunluk']:+.3f}"
                        if _ml["macd_gunluk"] is not None else "-"
                    ),
                    (
                        "MACD Aylık",
                        f"{_ml['macd_aylik']:+.3f}"
                        if _ml["macd_aylik"] is not None else "-"
                    ),
                    (
                        "MACD Yıllık",
                        f"{_ml['macd_yillik']:+.3f}"
                        if _ml["macd_yillik"] is not None else "-"
                    ),
                    (
                        "Histogram",
                        _macd_ozet(_ml["macd_gunluk_hist"])
                    ),
                ])
            except Exception as _ml_hata:
                st.caption(
                    f"MACD alınamadı: {_ml_hata}"
                )

            st.markdown("**💧 Likidite (Hacim / İşlem Hacmi)**")
            try:
                _ml2 = _hisse_macd_likidite(_temel_hisse + ".IS")

                _temel_satir([
                    (
                        "Son Gün Hacim",
                        temel_adet_format(_ml2["hacim_son"])
                    ),
                    (
                        "Ort. Hacim (20g)",
                        temel_adet_format(_ml2["hacim_ort20"])
                    ),
                    (
                        "Son Gün İşlem Hacmi",
                        temel_buyuk_sayi_format(_ml2["para_son"])
                    ),
                    (
                        "Ort. İşlem Hacmi (20g)",
                        temel_buyuk_sayi_format(_ml2["para_ort20"])
                    ),
                ])
                st.caption(
                    "MACD(12,26,9) ve likidite 10 yıllık günlük "
                    "veriden hesaplanır."
                )
            except Exception as _ml_hata2:
                st.caption(
                    f"Likidite alınamadı: {_ml_hata2}"
                )

            _dusuk = _temel["hafta52_dusuk"]
            _yuksek = _temel["hafta52_yuksek"]
            _fiyat = _temel["fiyat"]

            if _dusuk and _yuksek and _fiyat and _yuksek > _dusuk:
                _konum = min(
                    max((_fiyat - _dusuk) / (_yuksek - _dusuk), 0.0),
                    1.0
                )

                st.markdown("**📏 52 Hafta Aralığı**")
                st.progress(_konum)
                st.caption(
                    f"{tl_format(_dusuk)} – {tl_format(_yuksek)} · "
                    f"güncel fiyat aralığın %{_konum * 100:.0f} "
                    "seviyesinde"
                    + (
                        f" · Beta: {sayi_format(_temel['beta'])}"
                        if _temel["beta"] is not None
                        else ""
                    )
                )

            st.caption(
                "Veriler Yahoo Finance'ten alınır ve eksik/gecikmeli "
                "olabilir; boş alanlar '-' ile gösterilir. BIST "
                "şirketlerinde enflasyon muhasebesi nedeniyle oranlar "
                "dönemsel olarak sapabilir; kesin değerler için KAP'taki "
                "finansal tabloları kontrol edin. Yatırım tavsiyesi "
                "değildir."
            )


# ==================================================
# FİNANSAL TAKVİM
# ==================================================

with tab_takvim:
    st.caption(
        "Hisse kodu yazın; temettü ödeme/eski tarihleri, "
        "kazanç (earnings) tarihleri ve geçmiş temettü ödemeleri "
        "Yahoo Finance verisiyle listelenir."
    )

    col_takvim_hisse, col_takvim_buton = st.columns([3, 1])

    with col_takvim_hisse:
        _takvim_hisse = st.text_input(
            "Hisse Kodu",
            placeholder="Örn: THYAO, ASELS, EREGL",
            key="takvim_hisse"
        ).strip().upper()

    with col_takvim_buton:
        _takvim_baslat = st.button(
            "📆 Takvimi Getir",
            use_container_width=True,
            key="takvim_getir_buton"
        )

    if _takvim_hisse and _takvim_baslat:
        with st.spinner("Finansal takvim yükleniyor..."):
            _takvim = finansal_takvim_getir(_takvim_hisse)

        if not _takvim:
            st.warning(
                f"{_takvim_hisse} için takvim verisi alınamadı. "
                "Kod doğru mu kontrol edin, BIST hisseleri için "
                "sadece kodu yazın (Örn: THYAO)."
            )
        else:
            st.subheader(
                f"📆 {_takvim_hisse} Finansal Takvimi"
            )

            if _takvim.get("earnings"):
                st.markdown("**💰 Kazanç (Earnings) Tarihleri**")
                _earnings = _takvim["earnings"]
                if isinstance(_earnings, list):
                    for _t in _earnings:
                        st.markdown(f"- {_t}")
                else:
                    st.markdown(f"- {_earnings}")

            if _takvim.get("temettu_eski"):
                st.markdown(
                    f"**🏦 Son Temettü Eski (Ex-Dividend) Tarihi:** "
                    f"{_takvim['temettu_eski']}"
                )

            if _takvim.get("temettu_odeme"):
                st.markdown(
                    f"**💵 Temettü Ödeme Tarihi:** "
                    f"{_takvim['temettu_odeme']}"
                )

            if _takvim.get("bolunme"):
                st.markdown(
                    f"**🔀 Son Bölünme (Split) Tarihi:** "
                    f"{_takvim['bolunme']}"
                )

            if _takvim.get("temettu_gecmis"):
                st.markdown("**Temettü Geçmişi (Son 8)**")
                _gd = pd.DataFrame(_takvim["temettu_gecmis"])
                _gd["temettu"] = _gd["temettu"].apply(
                    lambda _x: f"{_x:.4f}".replace(".", ",")
                )
                _gd.columns = ["Tarih", "Temettü (TL)"]
                st.dataframe(
                    _gd,
                    use_container_width=True,
                    hide_index=True
                )

            st.caption(
                "Veriler Yahoo Finance'ten alınır ve en az 15 dakika "
                "gecikmeli olabilir; kesin bilgi için KAP'ı kontrol edin."
            )


# ==================================================
# ANA SAYFA (LOGO + CANLI KAYAN ŞERİT + SEKMELER)
# ==================================================

# ==================================================
# DÖVİZ ÇEVİRİCİ
# ==================================================

with tab_alarm:
    st.markdown(
        sekme_baslik_format(
            "\U0001F514", "Fiyat Alarm\u0131", "#ff6b6b"
        ),
        unsafe_allow_html=True
    )

    st.markdown(
        '<div id="bta-alarm-bilgi">'
        "<b>\u23f1 15 dakika gecikmeli canl\u0131 veri:</b> "
        "Fiyatlar ve alarm kontrol\u00fc yFinance/BIST verisiyle "
        "yap\u0131l\u0131r; bu veri yakla\u015f\u0131k 15 dakika "
        "gecikmelidir. Alarmlar sayfa a\u00e7\u0131kken en fazla "
        "90 saniyede bir kontrol edilir ve hedefe ula\u015f\u0131nca "
        "uyar\u0131 verilir."
        "</div>",
        unsafe_allow_html=True
    )

    ALARM_DOSYASI = "bta_alarmlar.csv"
    _ALARM_SUTUNLARI = [
        "alarm_id", "sembol", "yon", "fiyat", "durum", "tarih", "sahip"
    ]

    def _alarmlar_oku():
        if not os.path.exists(ALARM_DOSYASI):
            return pd.DataFrame(columns=_ALARM_SUTUNLARI)
        try:
            _df = pd.read_csv(ALARM_DOSYASI, dtype=str).fillna("")
        except Exception:
            return pd.DataFrame(columns=_ALARM_SUTUNLARI)
        for _c in _ALARM_SUTUNLARI:
            if _c not in _df.columns:
                _df[_c] = ""
        return _df

    def _alarm_yaz(_df):
        try:
            _df.to_csv(ALARM_DOSYASI, index=False)
        except Exception:
            pass

    # --- Kişiye özel alarm: takma ad ---
    _al_sahip_input = st.text_input(
        "Takma ad\u0131n (alarmlar\u0131n sadece sana g\u00f6r\u00fcn\u00fcr)",
        key="al_sahip_input",
        placeholder="\u00d6rn: nurican",
    ).strip()

    if _al_sahip_input:
        _sahip = _al_sahip_input
    else:
        if "al_sahip_misafir" not in st.session_state:
            st.session_state["al_sahip_misafir"] = (
                "Misafir-" + uuid.uuid4().hex[:5].upper()
            )
        _sahip = st.session_state["al_sahip_misafir"]

    st.caption(
        "Kendine bir takma ad ver (\u00f6rn: nurican); her ziyarette "
        "ayn\u0131 ad\u0131 yaz\u0131nca sadece senin alarmlar\u0131n "
        f"g\u00f6r\u00fcn\u00fcr. \u015eu anki kimlik: **{_sahip}**"
    )

    def _alarm_ekle(_sembol, _yon, _fiyat, _sahip):
        _df = _alarmlar_oku()
        _yeni = pd.DataFrame([{
            "alarm_id": uuid.uuid4().hex[:8],
            "sembol": _sembol,
            "yon": _yon,
            "fiyat": f"{_fiyat:.4f}",
            "durum": "aktif",
            "tarih": turkiye_saati().strftime("%d.%m.%Y %H:%M"),
            "sahip": _sahip,
        }])
        _df = pd.concat([_df, _yeni], ignore_index=True)
        _alarm_yaz(_df)

    def _alarm_sil(_aid, _sahip):
        _df = _alarmlar_oku()
        if not _df.empty:
            _df = _df[
                (_df["alarm_id"] != _aid) | (_df["sahip"] != _sahip)
            ]
            _alarm_yaz(_df)

    def _alarm_paneli_govde():
        _tum = _alarmlar_oku()
        _df = _tum[_tum["sahip"] == _sahip].copy()

        _miras = (
            int(len(_tum[_tum["sahip"] == ""]))
            if "sahip" in _tum.columns else 0
        )
        if _miras:
            st.caption(
                f"\u2139\ufe0f {_miras} eski alarm, takma ad\u0131 "
                "olmad\u0131\u011f\u0131 i\u00e7in kimsenin listesinde "
                "g\u00f6r\u00fcnm\u00fcyor."
            )

        if _df.empty:
            st.caption("Sana ait alarm yok. A\u015fa\u011f\u0131daki "
                       "formdan kurabilirsin.")
            return

        _degisti = False
        _simdi = turkiye_saati().timestamp()
        _son_kontrol = st.session_state.get("bta_alarm_son_kontrol", 0.0)
        _zamani_geldi = (_simdi - _son_kontrol) >= 90
        if _zamani_geldi:
            st.session_state["bta_alarm_son_kontrol"] = _simdi

        for _aid, _row in _df.iterrows():
            if not _zamani_geldi:
                break
            if str(_row["durum"]) != "aktif":
                continue
            try:
                _ys = _yf_sembol_bul(_row["sembol"])
                _sf = _son_fiyat(_ys)
            except Exception:
                continue

            _hedef = float(_row["fiyat"])
            _tetik = (
                (str(_row["yon"]) == "\u00dcst\u00fcne \u00e7\u0131k\u0131nca"
                 and _sf >= _hedef) or
                (str(_row["yon"]) == "Alt\u0131na inince" and _sf <= _hedef)
            )

            if _tetik:
                _df.at[_aid, "durum"] = "tetiklendi"
                _degisti = True
                st.error(
                    f"\U0001F514 ALARM: {_row['sembol']} {tl_format(_sf)} "
                    f"(hedef {tl_format(_hedef)})"
                )

        if _degisti:
            _alarm_yaz(_df)

        _aktifler = _df[_df["durum"] == "aktif"]

        if not _aktifler.empty:
            with st.container(border=True):
                st.markdown(f"**Aktif alarmlar\u0131n ({_sahip})**")

                for _aid, _row in _aktifler.iterrows():
                    _rid = str(_row["alarm_id"])
                    _ac1, _ac2 = st.columns([5, 1])
                    with _ac1:
                        st.write(
                            f"\U0001F514 {_row['sembol']} \u2022 "
                            f"{_row['yon']} \u2022 "
                            f"{tl_format(_row['fiyat'])} \u2022 "
                            f"{_row['tarih']}"
                        )
                    with _ac2:
                        if st.button(
                            "Sil", key=f"alarm_sil_{_rid}",
                            use_container_width=True
                        ):
                            _alarm_sil(_rid, _sahip)
                            st.rerun()
        else:
            st.caption(
                "Aktif alarm\u0131n yok. A\u015fa\u011f\u0131daki "
                "formdan yenisini kur."
            )

    @st.cache_data(ttl=60)
    def _alarm_guncel_fiyat_cek(_sembol):
        try:
            _sembol = str(_sembol).strip().upper()
            _son, _deg, _hata = fiyat_degisim_getir(
                _sembol + ".IS", marj_kontrolu=False
            )
            if _son is not None:
                return float(_son)
            return float(_son_fiyat(_yf_sembol_bul(_sembol)))
        except Exception:
            return None

    # Aktif alarmların listesi ÖNCE gösterilir; yeni alarm kurunca
    # hemen üstte görünür (aşağı kaymaya gerek kalmaz).
    # Fragment kullanılmaz: "Sil" butonu tüm sayfayı yeniler ->
    # %100 çalışır. Fiyat kontrolü 90 sn'de bir yapılır (yukarıda).
    _alarm_paneli_govde()

    with st.container(border=True):
        st.markdown("**\u2795 Yeni alarm kur**")
        _al1, _al2, _al3, _al4 = st.columns([2, 2, 2, 1])

        with _al1:
            _al_sembol = st.text_input(
                "Alarm sembol\u00fc", placeholder="\u00d6rn: TRHOL, THYAO",
                key="al_sembol"
            ).strip().upper()
            if _al_sembol:
                _gf = _alarm_guncel_fiyat_cek(_al_sembol)
                if _gf:
                    st.caption(
                        f"G\u00fcncel fiyat: {tl_format(_gf)} "
                        "(yakla\u015f\u0131k 15 dk gecikmeli)"
                    )
                else:
                    st.caption("G\u00fcncel fiyat al\u0131namad\u0131")

        with _al2:
            _al_yon = st.selectbox(
                "Y\u00f6n",
                ["\u00dcst\u00fcne \u00e7\u0131k\u0131nca", "Alt\u0131na inince"],
                key="al_yon"
            )

        with _al3:
            _al_fiyat_metin = st.text_input(
                "Hedef fiyat",
                value="",
                placeholder="\u00d6rn: 2955,00 veya 2.955",
                key="al_fiyat"
            )

        with _al4:
            st.write("")
            _al_kur = st.button(
                "Alarm Kur", key="al_kur", use_container_width=True
            )

        if _al_kur:
            try:
                _al_fiyat = fiyat_coz(_al_fiyat_metin)
            except Exception:
                _al_fiyat = 0.0

            if not _al_sembol:
                st.error("Sembol gir.")
            elif _al_fiyat <= 0:
                st.error(
                    "Ge\u00e7erli bir hedef fiyat gir "
                    "(\u00f6r. 2955,00 veya 2.955)."
                )
            else:
                _alarm_ekle(_al_sembol, _al_yon, _al_fiyat, _sahip)
                st.success(
                    f"Alarm kuruldu: {_al_sembol} {_al_yon} "
                    f"{tl_format(_al_fiyat)} (kimlik: {_sahip})"
                )
                st.rerun()

with tab_doviz:
    _kur_veriler, _ = piyasa_ozeti_getir()

    _kur_tl = {"TL": 1.0}

    for _kur_v in _kur_veriler:
        if _kur_v["isim"] == "USDTRY":
            _kur_tl["USD"] = _kur_v["fiyat"]
        elif _kur_v["isim"] == "EURTRY":
            _kur_tl["EUR"] = _kur_v["fiyat"]
        elif _kur_v["isim"] == "GRAM ALTIN (yakl.)":
            _kur_tl["Gram Altın"] = _kur_v["fiyat"]
        elif _kur_v["isim"] == "ÇEYREK ALTIN (yakl.)":
            _kur_tl["Çeyrek Altın"] = _kur_v["fiyat"]
        elif _kur_v["isim"] == "YARIM ALTIN (yakl.)":
            _kur_tl["Yarım Altın"] = _kur_v["fiyat"]
        elif _kur_v["isim"] == "TAM ALTIN (yakl.)":
            _kur_tl["Tam Altın"] = _kur_v["fiyat"]

    _kur_mevcut = [
        _birim
        for _birim, _deger in _kur_tl.items()
        if _deger is not None
    ]

    def _cevir_goster(_deger):
        """Tam sayıya yakın değerler '10.000' gibi ondalıksız,
        diğerleri '12,34' gibi iki ondalık; Türkçe biçimde döner."""
        try:
            _yuv = round(_deger)
            if abs(_deger - _yuv) < 1e-9:
                return (
                    f"{_yuv:,.0f}"
                    .replace(",", "X")
                    .replace(".", ",")
                    .replace("X", ".")
                )
            return (
                f"{_deger:,.2f}"
                .replace(",", "X")
                .replace(".", ",")
                .replace("X", ".")
            )
        except Exception:
            return "-"

    if len(_kur_mevcut) < 2:
        st.info("Kur verisi alınamadı, birazdan tekrar deneniyor.")
    else:
        with st.container(border=True):
            st.markdown("#### 💱 DÖVİZ ÇEVİRİCİ")

            _cevir_miktar_metin = st.text_input(
                "Miktar",
                value="10.000",
                key="cevir_miktar",
                help="Örn: 10.000 veya 10000 yazabilirsiniz."
            )

            _cevir_miktar = turkce_sayi_cevir(_cevir_miktar_metin)

            if _cevir_miktar is None:
                _cevir_miktar = 0.0

            _cc1, _cc2 = st.columns(2)

            with _cc1:
                _cevir_kaynak = st.selectbox(
                    "Çevirilecek Birim",
                    _kur_mevcut,
                    key="cevir_kaynak"
                )

            with _cc2:
                _cevir_hedef = st.selectbox(
                    "Hedef Birim",
                    _kur_mevcut,
                    key="cevir_hedef"
                )

            _cevir_hesapla = st.button(
                "💱 Hesapla",
                use_container_width=True,
                key="cevir_hesapla_buton"
            )

            _cevir_sonuc = (
                _cevir_miktar
                * _kur_tl[_cevir_kaynak]
                / _kur_tl[_cevir_hedef]
            )

            st.success(
                f"{_cevir_goster(_cevir_miktar)} {_cevir_kaynak} = "
                f"{_cevir_goster(_cevir_sonuc)} {_cevir_hedef}"
            )

            st.caption(
                "Kurlar canlı piyasa kartından alınır; "
                "altın fiyatları yaklaşık hesaplanır, "
                "alım-satım için kuyumcudan teyit alınız."
            )


# ==================================================
# ALGORİTMA HİSSELER (CANLI FİYATLAR)
# ==================================================
with tab_gunluk:
    st.markdown(
        sekme_baslik_format(
            _bta_logo_kucuk_svg, "BTA ALGOR\u0130TMA", "#00f5c8"
        ),
        unsafe_allow_html=True
    )

    if excel_df.empty:
        st.warning(
            "Tarama da herhangi bir hisse bulunamadı."
        )
    else:
        secilen_hisse = st.selectbox(
            f"🔍 BTA Algoritma Hissesi Seç ({len(excel_df)} hisse):",
            excel_df["Hisse Kodu"].tolist()
        )

        sembol = secilen_hisse

        if not sembol.endswith(".IS"):
            sembol += ".IS"

        try:
            hisse = yf.Ticker(sembol)
            bilgi = hisse.info

            fiyat, degisim_yuzde, hata = fiyat_degisim_getir(
                sembol, marj_kontrolu=False
            )

            onceki_kapanis = bilgi.get(
                "regularMarketPreviousClose"
            )
            if onceki_kapanis is None:
                onceki_kapanis = getattr(
                    hisse.fast_info, "previous_close", None
                )

            en_yuksek = bilgi.get(
                "dayHigh"
            )

            en_dusuk = bilgi.get(
                "dayLow"
            )

            hacim = bilgi.get(
                "volume"
            )

            piyasa_degeri = bilgi.get(
                "marketCap"
            )

            kayit = excel_df[
                excel_df["Hisse Kodu"] == secilen_hisse
            ].iloc[0]

            bta_alim_fiyati = kayit["BTA Alım Fiyatı"]
            kar_yuzde = kar_yuzdesi_hesapla(bta_alim_fiyati, fiyat)

            col1, col2, col3 = st.columns(3)

            col1.metric(
                "BTA Algoritma Fiyatı",
                tl_format(bta_alim_fiyati)
            )

            col2.metric(
                "BTA Puanı",
                sayi_format(
                    kayit["BTA Puanı"]
                )
            )

            col3.metric(
                "Anlık Fiyat",
                tl_format(fiyat)
            )

            # Kar Yüzdesi Göster
            st.markdown(
                kar_yuzdesi_format(kar_yuzde),
                unsafe_allow_html=True
            )

            st.markdown(
                f"""
                <div class="bilgi-karti">
                    <strong>Hisse Kodu:</strong> {secilen_hisse}<br>
                    <strong>Önceki Kapanış:</strong>
                    {tl_format(onceki_kapanis)}<br>
                    <strong>Günlük En Yüksek:</strong>
                    {tl_format(en_yuksek)}<br>
                    <strong>Günlük En Düşük:</strong>
                    {tl_format(en_dusuk)}<br>
                    <strong>İşlem Hacmi:</strong>
                    {sayi_format(hacim)}<br>
                    <strong>Piyasa Değeri:</strong>
                    {sayi_format(piyasa_degeri)}<br>
                    <strong>Veri Durumu:</strong>
                    En az 15 dakika gecikmeli olabilir.
                </div>
                """,
                unsafe_allow_html=True
            )

        except Exception as hata:
            st.warning(
                f"Algoritmik bilgiler alınamadı: {hata}"
            )


# ==================================================
# BTA AL SAT (B SÜTUNU LİSTESİ - CANLI FİYATLAR)
# ==================================================

    @st.fragment(run_every=30)
    def _gunluk_liste_fragment():
        """BTA AL SAT listesi (Excel B sütunu); sayfa titretilmeden
        30 sn'de bir arka planda güncellenir (st.fragment)."""
        st.markdown("**BTA AL SAT Hisseleri**")
        if gunluk_algoritma_df.empty:
            st.info(
                "Tarama da herhangi bir hisse bulunamadı."
            )
        else:
            _gunluk_hisseler = [
                str(_h).strip().upper()
                for _h in gunluk_algoritma_df["Hisse Kodu"].tolist()
                if str(_h).strip()
                and str(_h).strip().upper()
                not in (
                    "NAN", "NONE", "NULL", "NA", "NAN.0",
                    "BTA AL SAT", "AL SAT", "HİSSE", "HISSE"
                )
            ]

            # KAP/SPK haber rozetleri (arka planda çekilir, bekletmez;
            # hazır olunca sonraki 5 sn'lik yenilemede görünür).
            try:
                _haber_rozetleri = haber_rozetlerini_getir(
                    _gunluk_hisseler
                )
            except Exception:
                _haber_rozetleri = {}

            def _gunluk_tek_hisse(_hisse_kodu):
                # Ne gelirse gelsin (float, None, NaN vb.) önce
                # güvenli biçimde metne çevrilir; tek bir bozuk
                # satır yüzünden tüm tarama durmasın diye fonksiyon
                # hiçbir zaman hata fırlatmaz, hatayı veri olarak
                # döndürür.
                try:
                    _kod = str(_hisse_kodu).strip().upper()

                    if not _kod:
                        return _hisse_kodu, None, None, "boş hisse kodu"

                    _sembol = _kod

                    if not _sembol.endswith(".IS"):
                        _sembol += ".IS"

                    _son, _degisim, _hata = fiyat_degisim_getir(_sembol)
                    return _kod, _son, _degisim, _hata

                except Exception as _ic_hata:
                    return _hisse_kodu, None, None, str(_ic_hata)

            _gunluk_sonuclar = []
            _gunluk_hatalar = []

            try:
                with concurrent.futures.ThreadPoolExecutor(
                    max_workers=15
                ) as _gunluk_havuz:
                    for _h, _s, _d, _e in _gunluk_havuz.map(
                        _gunluk_tek_hisse,
                        _gunluk_hisseler
                    ):
                        if _e is not None or _s is None or _d is None:
                            _gunluk_hatalar.append(f"{_h}: {_e}")
                            continue

                        _gunluk_sonuclar.append((_h, _s, _d))
            except Exception as _hata:
                st.error(f"Veri çekilirken hata oluştu: {_hata}")

            # Güncelleme saati, Excel dosyasının gerçek değişiklik
            # zamanından her çizimde okunur; aynı dosya durdukça sabit
            # kalır, yeni bir Excel yüklenince otomatik güncellenir.
            _gunluk_zamani = bta_gunluk_zaman_yukle()

            st.markdown(
                f"""
                <div style="
                    display: inline-block;
                    background: rgba(0, 245, 200, 0.12);
                    border: 1px solid rgba(0, 245, 200, 0.4);
                    border-radius: 20px;
                    padding: 5px 14px;
                    margin-bottom: 8px;
                    font-size: 14px;
                    font-weight: 600;
                    color: #00f5c8;
                ">
                    🕒 BTA AL SAT g\u00fcncelleme saati: {_gunluk_zamani}
                </div>
                """,
                unsafe_allow_html=True
            )

            if not _gunluk_sonuclar:
                st.info(
                    "Şu anda canlı fiyat alınamadı, birazdan "
                    "tekrar denenecek."
                )
            else:
                # Değişim yüzdesine göre büyükten küçüğe sıralanır
                # (her yenilemede tutarlı şekilde aynı sıralama).
                _gunluk_sonuclar = sorted(
                    _gunluk_sonuclar,
                    key=lambda _oge: _oge[2],
                    reverse=True
                )

                # Liste ekran genişliğine yayılır; dar ekranda kartlar
                # sıkışıp yüzde sütunu satır dışında kalmaz.
                for _sira, (_h, _s, _d) in enumerate(
                    _gunluk_sonuclar
                ):
                    _renk = "#00f5c8" if _d >= 0 else "#ff5264"

                    st.markdown(
                        hisse_karti_format(
                            _h, _s, _d, _renk, sira=_sira,
                            rozet_html=haber_rozeti_html(
                                _haber_rozetleri.get(_h)
                            )
                        ),
                        unsafe_allow_html=True
                    )

            if _gunluk_hatalar:
                with st.expander(
                    f"⚠️ Listede olan {len(_gunluk_hatalar)} hissenin "
                    "fiyatı alınamadı",
                    expanded=True
                ):
                    for _satir in _gunluk_hatalar[:20]:
                        st.code(_satir, language=None)

# Kapatıldı: B sütunundaki uzun "BTA AL SAT Hisseleri" listesi
    # (Excel'de çok hisse olduğunda sayfa uzayıp sönüp açılıyordu).
    # En iyisi BTA ALGORİTMA hisse analizi olduğundan liste kaldırıldı.
    # _gunluk_liste_fragment()

    # ==============================================
    # SPK / YASAL UYARI (ALGORİTMA HİSSELER)
    # ==============================================
    st.markdown(
        '<div class="spk-uyari">'
        '⚠️ <strong>SPK / Yasal Uyarı:</strong> '
        'Bu sayfada yer alan bilgiler, yorumlar ve algoritma çıktıları '
        'yatırım danışmanlığı kapsamında değildir. Yatırım danışmanlığı '
        'hizmeti; yetkili kuruluşlar tarafından, kişilerin risk ve getiri '
        'tercihleri dikkate alınarak kişiye özel sunulmaktadır. Burada '
        'yer alan bilgiler genel niteliktedir ve mali durumunuz ile risk '
        've getiri tercihlerinize uygun sonuçlar doğurmayabilir. Bu '
        'nedenle yalnızca burada yer alan bilgilere dayanarak yatırım '
        'kararı verilmesi beklentilerinize uygun sonuçlar '
        'doğurmayabilir. Gösterilen fiyatlar '
        '<strong>en az 15 dakika gecikmeli</strong> olabilir.'
        '</div>',
        unsafe_allow_html=True
    )


# ==================================================
# BEDELLİ / BEDELSİZ HESAPLAMA MAKİNESİ
# ==================================================
with tab_bedelli:
    st.markdown(
        sekme_baslik_format(
            "🧮",
            "Bedelli / Bedelsiz Hesaplama Makinesi",
            "#b48bff"
        ),
        unsafe_allow_html=True
    )

    st.markdown(
        """
        <div class="bilgi-karti">
            Sermaye artırımı (bedelli/bedelsiz) sonrası portföyünüzde
            oluşacak <strong>yeni pay sayısını</strong> ve
            <strong>teorik (düzeltilmiş) fiyatı</strong> hesaplayın.
            Oranları hisse için açıklanan sermaye artırımı
            duyurusundaki yüzdelerle girin.
        </div>
        """,
        unsafe_allow_html=True
    )

    # ==================================================
    # FİYAT KAYNAĞI SEÇİMİ
    # ==================================================
    hisse_listesi = (
        excel_df["Hisse Kodu"].tolist()
        if not excel_df.empty
        else []
    )

    kaynak_secenekleri = ["✍️ Manuel Fiyat Gir"]

    if hisse_listesi:
        kaynak_secenekleri = [
            "📈 Listeden Hisse Seç (Anlık Fiyat)"
        ] + kaynak_secenekleri

    kaynak = st.radio(
        "Fiyat Kaynağı",
        kaynak_secenekleri,
        horizontal=True
    )

    varsayilan_fiyat = 0.0
    secilen_hisse_bedelli = None

    if kaynak == "📈 Listeden Hisse Seç (Anlık Fiyat)":
        secilen_hisse_bedelli = st.selectbox(
            "🔍 Hisse Seç:",
            hisse_listesi,
            key="bedelli_hisse_secim"
        )

        sembol_bedelli = secilen_hisse_bedelli

        if not sembol_bedelli.endswith(".IS"):
            sembol_bedelli += ".IS"

        try:
            hisse_bedelli = yf.Ticker(sembol_bedelli)
            bilgi_bedelli = hisse_bedelli.info

            varsayilan_fiyat = bilgi_bedelli.get(
                "regularMarketPrice"
            ) or 0.0

            st.caption(
                f"Anlık fiyat otomatik dolduruldu: "
                f"{tl_format(varsayilan_fiyat)} "
                f"(en az 15 dakika gecikmeli olabilir)"
            )

        except Exception as hata:
            st.warning(
                f"Anlık fiyat alınamadı, manuel girebilirsiniz: {hata}"
            )

    st.divider()

    # ==================================================
    # GİRDİ FORMU
    # ==================================================
    col1, col2 = st.columns(2)

    with col1:
        eski_fiyat_girdi = st.number_input(
            "Mevcut / Önceki Kapanış Fiyatı (TL)",
            min_value=0.0,
            value=float(varsayilan_fiyat or 0.0),
            step=0.01,
            format="%.4f"
        )

        sahip_lot_girdi = st.number_input(
            "Sahip Olduğunuz Pay (Lot) Adedi",
            min_value=0.0,
            value=100.0,
            step=1.0
        )

    with col2:
        bedelli_orani_girdi = st.number_input(
            "Bedelli Sermaye Artırım Oranı (%)",
            min_value=0.0,
            value=0.0,
            step=1.0,
            help="Örn. %50 bedelli için 50 girin. Bedelli yoksa 0 bırakın."
        )

        bedelli_fiyat_girdi = st.number_input(
            "Bedelli Pay Alım Fiyatı (TL)",
            min_value=0.0,
            value=1.00,
            step=0.01,
            format="%.4f",
            help="Genellikle nominal değer (1 TL) üzerinden yapılır."
        )

        bedelsiz_orani_girdi = st.number_input(
            "Bedelsiz Sermaye Artırım Oranı (%)",
            min_value=0.0,
            value=0.0,
            step=1.0,
            help="Örn. %20 bedelsiz için 20 girin. Bedelsiz yoksa 0 bırakın."
        )

    st.divider()

    hesapla_buton = st.button(
        "🧮 Hesapla",
        use_container_width=True,
        type="primary"
    )

    # ==================================================
    # NOT: Sayfa 5 saniyede bir otomatik yenilendiği için
    # (st_autorefresh) sonuç "if hesapla_buton:" içinde
    # tutulursa bir sonraki otomatik yenilemede kaybolur.
    # Bu yüzden sonuç, session_state'e yazılıp aşağıda
    # butondan bağımsız olarak her zaman gösterilir.
    # ==================================================
    if hesapla_buton:
        if eski_fiyat_girdi <= 0:
            st.session_state["bedelli_sonuc"] = None
            st.session_state["bedelli_hata"] = (
                "Lütfen geçerli bir mevcut fiyat girin."
            )
        elif bedelli_orani_girdi == 0 and bedelsiz_orani_girdi == 0:
            st.session_state["bedelli_sonuc"] = None
            st.session_state["bedelli_hata"] = (
                "Lütfen bedelli veya bedelsiz oranından "
                "en az birini girin."
            )
        else:
            sonuc = bedelli_bedelsiz_hesapla(
                eski_fiyat_girdi,
                sahip_lot_girdi,
                bedelli_orani_girdi,
                bedelli_fiyat_girdi,
                bedelsiz_orani_girdi
            )

            if sonuc is None:
                st.session_state["bedelli_sonuc"] = None
                st.session_state["bedelli_hata"] = (
                    "Hesaplama yapılamadı, "
                    "girdiğiniz değerleri kontrol edin."
                )
            else:
                st.session_state["bedelli_sonuc"] = sonuc
                st.session_state["bedelli_hata"] = None

    if st.session_state.get("bedelli_hata"):
        st.error(st.session_state["bedelli_hata"])

    sonuc_kalici = st.session_state.get("bedelli_sonuc")

    if sonuc_kalici:
        st.markdown(
            bedelli_bedelsiz_kart_format(sonuc_kalici),
            unsafe_allow_html=True
        )

        col1, col2, col3 = st.columns(3)

        col1.metric(
            "Bedelli Yeni Pay",
            sayi_format(sonuc_kalici["bedelli_yeni_lot"])
        )

        col2.metric(
            "Bedelsiz Yeni Pay",
            sayi_format(sonuc_kalici["bedelsiz_yeni_lot"])
        )

        col3.metric(
            "Toplam Yeni Pay",
            sayi_format(sonuc_kalici["toplam_yeni_lot"])
        )

        col1, col2, col3 = st.columns(3)

        col1.metric(
            "Artırım Sonrası Toplam Pay",
            sayi_format(sonuc_kalici["toplam_lot_sonrasi"])
        )

        col2.metric(
            "Bedelli İçin Ödenecek Tutar",
            tl_format(sonuc_kalici["odenecek_tutar"])
        )

        col3.metric(
            "Fiyat Değişimi",
            f"{sonuc_kalici['fiyat_degisim_yuzde']:+.2f}%"
        )

        st.markdown(
            f"""
            <div class="bilgi-karti">
                <strong>Sermaye Artırımı Öncesi Portföy Değeri:</strong>
                {tl_format(sonuc_kalici["eski_portfoy_degeri"])}<br>
                <strong>Sermaye Artırımı Sonrası Portföy Değeri:</strong>
                {tl_format(sonuc_kalici["yeni_portfoy_degeri"])}<br>
                <strong>Not:</strong> Sonrası değer, bedelli tutarının
                nakit olarak yatırıldığı varsayımıyla hesaplanmıştır.
                Teorik fiyat, borsanın ilan ettiği kesin referans
                fiyattan farklılık gösterebilir.
            </div>
            """,
            unsafe_allow_html=True
        )

        if st.button(
            "✖️ Sonucu Temizle",
            use_container_width=True,
            key="bedelli_sonuc_temizle"
        ):
            st.session_state["bedelli_sonuc"] = None
            st.session_state["bedelli_hata"] = None
            st.rerun()


# ==================================================
# BEDELLİ / BEDELSİZ SERMAYE ARTIRIMI HABERLERİ
# ==================================================
with tab_sermaye:
    _sermaye_durum = st.session_state.get(
        "bta_haber_durum", {}
    ).get("bedelli", {})
    _sermaye_yeni_kimlik = (
        _sermaye_durum.get("yeni_kimlikler") or set()
    )
    _sermaye_yeni = _sermaye_durum.get("yeni_say", 0)

    _sermaye_haberler = (
        st.session_state.get("bta_haber_veri", {}).get("bedelli")
        or bedelli_bedelsiz_haberleri_getir()
    )

    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #c77dff;
            border-color: #c77dff;
            background: linear-gradient(
                90deg,
                rgba(199, 125, 255, 0.22),
                rgba(199, 125, 255, 0.06)
            );
            box-shadow: 0 0 18px rgba(199, 125, 255, 0.3);
        ">
            <span style="color: #c77dff;
                         text-shadow: 0 0 14px rgba(199, 125, 255, 0.8);">
                BEDELLİ / BEDELSİZ SERMAYE ARTIRIMI HABERLERİ
            </span>
            <span class="sekme-baslik-tarih">Son 48 Saat</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    st.caption(
        "Sermaye artırımı yapan şirketlerin güncel haberleri "
        "otomatik olarak listelenir; her 10 dakikada bir tazelenir."
    )

    if _sermaye_yeni:
        st.success(f"🔴 {_sermaye_yeni} yeni sermaye artırımı haberi var!")

    _sermaye_filtre = st.text_input(
        "🔎 Haberlerde ara",
        placeholder="Örn: bedelli, bedelsiz, rüçhan",
        key="sermaye_haber_filtre"
    ).strip().lower()

    if _sermaye_filtre:
        _sermaye_haberler = [
            _h for _h in _sermaye_haberler
            if _sermaye_filtre in _h[0].lower()
        ]

    if not _sermaye_haberler:
        st.info(
            "Şu anda bedelli/bedelsiz sermaye artırımı haberi "
            "bulunamadı, birazdan tekrar deneniyor."
        )
    else:
        for (
            _baslik, _link, _zaman, _kaynak
        ) in _sermaye_haberler:
            _sermaye_yeni_rozet = (
                '<span class="bta-yeni-rozet">🆕 YENİ</span>'
                if _haber_kimlik(_baslik) in _sermaye_yeni_kimlik
                else ""
            )
            st.markdown(
                f"""
                <div class="haber-bulteni-kart arz-kart">
                    <div class="haber-bulteni-saat">
                        {_sermaye_yeni_rozet}🕒 {_zaman}
                        <span class="arz-kaynak">
                            · {_kaynak or "Haber"}
                        </span>
                    </div>
                    <a href="{_link}" target="_blank"
                       class="haber-bulteni-link">
                        {_baslik}
                    </a>
                </div>
                """,
                unsafe_allow_html=True
            )

    st.caption(
        "Kaynak: Google News. Yatırım tavsiyesi değildir; "
        "kesin oran ve tarihler için şirket KAP duyurularını "
        "kontrol edin."
    )


# ==================================================
# YABANCI TAKAS ORANLARI
# ==================================================
with tab_yabanci:
    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #4da6ff;
            border-color: #4da6ff;
            background: linear-gradient(
                90deg,
                rgba(77, 166, 255, 0.22),
                rgba(77, 166, 255, 0.06)
            );
            box-shadow: 0 0 18px rgba(77, 166, 255, 0.3);
        ">
            <span style="color: #4da6ff;
                         text-shadow: 0 0 14px rgba(77, 166, 255, 0.8);">
                YABANCI TAKAS ORANLARI
            </span>
            <span class="sekme-baslik-tarih">BIST · Günlük</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    st.caption(
        "Borsa İstanbul hisselerinin yabancı yatırımcı takas "
        "oranları (Kaynak: İş Yatırım). Veri genellikle günde "
        "bir kez güncellenir; ufak gecikme olabilir. "
        "Yatırım tavsiyesi değildir."
    )

    _yster = yabanci_takas_oranlari()

    if _yster is None or _yster.empty:
        st.info(
            "Yabancı takas verisi şu anda alınamadı; "
            "birazdan tekrar deneniyor."
        )
    else:
        _yfiltre = st.text_input(
            "🔎 Hisse ara",
            placeholder="Örn: THYAO",
            key="yabanci_takas_filtre",
        ).strip().upper()

        _ydf = _yster
        if _yfiltre:
            _ydf = _ydf[
                _ydf["Hisse Kodu"].astype(str).str.contains(_yfiltre)
            ]

        _ysurut = st.selectbox(
            "Sıralama",
            [
                "Yabancı Oranı % (yüksekten)",
                "1H Değişim",
                "1A Değişim",
                "Piyasa Değeri (mn TL)",
                "Halka Açıklık %",
            ],
            key="yabanci_takas_sirala",
        )

        if _ysurut == "Yabancı Oranı % (yüksekten)":
            _ydf = _ydf.sort_values(
                "Yabancı Oranı %", ascending=False, na_position="last"
            )
        else:
            _ydf = _ydf.sort_values(
                _ysurut, ascending=False, na_position="last"
            )

        st.caption(
            f"Toplam {len(_yster)} hisse · {len(_ydf)} gösteriliyor"
        )

        st.dataframe(
            _ydf,
            use_container_width=True,
            hide_index=True,
            height=430,
            column_config={
                "Hisse Kodu": st.column_config.TextColumn("Hisse Kodu"),
                "Yabancı Oranı %": st.column_config.NumberColumn(
                    "Yabancı Oranı %", format="%.2f %%"),
                "1H Değişim": st.column_config.NumberColumn(
                    "1H Değişim", format="%+.2f"),
                "1A Değişim": st.column_config.NumberColumn(
                    "1A Değişim", format="%+.2f"),
                "Kapanış TL": st.column_config.NumberColumn(
                    "Kapanış TL", format="%.2f TL"),
                "Piyasa Değeri (mn TL)": st.column_config.NumberColumn(
                    "Piyasa Değeri (mn TL)", format="%.0f"),
                "Halka Açıklık %": st.column_config.NumberColumn(
                    "Halka Açıklık %", format="%.2f %%"),
            },
        )

        _ilkler = _yster.sort_values(
            "Yabancı Oranı %", ascending=False, na_position="last"
        ).head(10)

        st.markdown("🏆 **En Yüksek Yabancı Oranlı Hisseler (İlk 10)**")

        _max_oran = max(
            [_r["Yabancı Oranı %"] or 0 for _, _r in _ilkler.iterrows()] or [1]
        )
        _htm = ""
        for _, _r in _ilkler.iterrows():
            _oran = _r["Yabancı Oranı %"] or 0
            _genislik = (
                max(2.0, (_oran / _max_oran) * 100) if _max_oran else 2.0
            )
            _htm += (
                f'<div style="margin:4px 0;"><b>{_r["Hisse Kodu"]}</b> '
                f'<span style="float:right;color:#00f5c8;">'
                f'{_oran:.2f}%</span></div>'
                f'<div class="bta-veri-bar">'
                f'<div class="bta-veri-bar-dolgu" '
                f'style="width:{_genislik:.1f}%"></div></div>'
            )
        st.markdown(_htm, unsafe_allow_html=True)


# ==================================================
# ARACI KURUM DAĞILIMI
# ==================================================
with tab_kurum:
    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #b48bff;
            border-color: #b48bff;
            background: linear-gradient(
                90deg,
                rgba(180, 139, 255, 0.22),
                rgba(180, 139, 255, 0.06)
            );
            box-shadow: 0 0 18px rgba(180, 139, 255, 0.3);
        ">
            <span style="color: #b48bff;
                         text-shadow: 0 0 14px rgba(180, 139, 255, 0.8);">
                ARACI KURUM DAĞILIMI
            </span>
            <span class="sekme-baslik-tarih">Gün İçi Pazar AKD</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    st.caption(
        "Gün içi Pazar AKD (Aracı Kurum Dağılımı) — Kaynak: BOPT / "
        "@borsakaynak. Veri; borsa tarafından yayımlanan sembol bazlı "
        "ilk 10 kademe AKD verilerinden hesaplanan bir tahmindir, "
        "resmî pazar geneli AKD değildir."
    )

    _akveri = araci_kurum_dagilimi()

    if not _akveri or not _akveri.get("success"):
        st.info(
            "Aracı kurum dağılımı verisi şu anda alınamadı; "
            "birazdan tekrar deneniyor."
        )
    else:
        _asof = _akveri.get("sourceAsOf", "") or ""
        _totals = _akveri.get("totals") or {}

        col_m1, col_m2 = st.columns(2)
        with col_m1:
            st.metric(
                "Toplam Alış",
                f"{(_totals.get('totalBuyValue') or 0) / 1e6:,.0f} mn TL",
            )
        with col_m2:
            st.metric(
                "Toplam Satış",
                f"{(_totals.get('totalSellValue') or 0) / 1e6:,.0f} mn TL",
            )

        st.caption(f"Son güncelleme: {_asof}")

        _alicilar = _akveri.get("buyers") or []
        _saticilar = _akveri.get("sellers") or []

        if _alicilar and _saticilar:
            st.markdown("📊 **Net Alım / Net Satış (Aracı Kurumlar)**")
            _akd_sekme_al, _akd_sekme_sat = st.tabs(
                ["🔵 Net Alımda", "🔴 Net Satışta"]
            )

            with _akd_sekme_al:
                st.markdown("Bu kurlar bugün **net alımda**:")
                _adf = pd.DataFrame([
                    {
                        "Kurum": (
                            _l.get("institutionShortName")
                            or _l.get("institutionName", "")
                        ),
                        "Net (mn TL)": (_l.get("netValue") or 0) / 1e6,
                        "Alış Tarafı Payı %": _l.get("sharePct") or 0,
                    }
                    for _l in _alicilar
                ])
                st.dataframe(
                    _adf, use_container_width=True, hide_index=True,
                    height=300,
                )

            with _akd_sekme_sat:
                st.markdown("Bu kurumlar bugün **net satışta**:")
                _sdf = pd.DataFrame([
                    {
                        "Kurum": (
                            _l.get("institutionShortName")
                            or _l.get("institutionName", "")
                        ),
                        "Net (mn TL)": (_l.get("netValue") or 0) / 1e6,
                        "Satış Tarafı Payı %": _l.get("sharePct") or 0,
                    }
                    for _l in _saticilar
                ])
                st.dataframe(
                    _sdf, use_container_width=True, hide_index=True,
                    height=300,
                )

        _liderler = _akveri.get("leaders") or []
        if _liderler:
            _ldf = pd.DataFrame([
                {
                    "Kurum": (
                        _l.get("institutionShortName")
                        or _l.get("institutionName", "")
                    ),
                    "Net (mn TL)": (_l.get("netValue") or 0) / 1e6,
                    "Pazar Payı %": _l.get("sharePct") or 0,
                }
                for _l in _liderler
            ])

            st.markdown("📊 **Kurumların Net Dağılımı (Pazar Geneli)**")
            st.dataframe(
                _ldf,
                use_container_width=True,
                hide_index=True,
                column_config={
                    "Net (mn TL)": st.column_config.NumberColumn(
                        "Net (mn TL)", format="%.0f"),
                    "Pazar Payı %": st.column_config.NumberColumn(
                        "Pazar Payı %", format="%.2f %%"),
                },
            )

        _detay = _akveri.get("institutionDetails") or {}
        if _detay:
            _kurum_sec = st.selectbox(
                "🔍 Kurum Detayları",
                list(_detay.keys()),
                format_func=lambda _k: (
                    _detay[_k].get("institutionName") or _k
                ),
                key="araci_kurum_detay",
            )

            _kd = _detay.get(_kurum_sec) or {}

            _alimlar = _kd.get("topBought") or []
            _satalar = _kd.get("topSold") or []

            col_ky, col_ks = st.columns(2)
            with col_ky:
                st.markdown("##### En Çok Aldığı Hisseler")
                if _alimlar:
                    for _h in _alimlar:
                        st.markdown(
                            f"• **{_h.get('symbol', '')}** — "
                            f"{_h.get('value', '')}"
                        )
                else:
                    st.caption("Veri yok")

            with col_ks:
                st.markdown("##### En Çok Sattığı Hisseler")
                if _satalar:
                    for _h in _satalar:
                        st.markdown(
                            f"• **{_h.get('symbol', '')}** — "
                            f"{_h.get('value', '')}"
                        )
                else:
                    st.caption("Veri yok")

        st.caption(
            "Veri @borsakaynak hesaplamasıdır; yalnızca bilgilendirme "
            "amaçlıdır, yatırım tavsiyesi değildir."
        )


# ==================================================
# CANLI SOHBET
# ==================================================
with tab_sohbet:
    st.markdown(
        sekme_baslik_format(
            "💬", "Sohbet", "#ff6ec7"
        ),
        unsafe_allow_html=True
    )

    st.markdown(
        """
        <div class="sohbet-uyari">
            ⚠️ <strong>Uyarı:</strong> Bu bölümde paylaşılan yorum ve
            mesajlar tamamen kullanıcıların
            <strong>kişisel görüşleridir</strong>; platformun veya
            yöneticilerin görüşünü yansıtmaz. Yatırım danışmanlığı,
            yatırım tavsiyesi ya da <strong>AL – SAT – TUT önerisi
            değildir</strong>. Küfür, hakaret ve yatırım yönlendirmesi
            içeren mesajlar otomatik olarak engellenir. Yatırım
            kararlarınızı kendi araştırmanıza dayanarak veriniz.
        </div>
        """,
        unsafe_allow_html=True
    )

    @st.fragment(run_every=15)
    def _sohbet_fragment():
        """Takip butonu, DM formu, mesaj formu ve mesaj listesi.
        Tıklama veya yeni mesaj geldiğinde yalnızca bu bölüm arka
        planda yenilenir; sayfa baştan çizilip ekran sönmez."""
        _oturum_kodu = ziyaretci_oturum_kodu()

        _sohbet_uye = st.session_state.get("bta_uyelik_user")
        _sohbet_uyemi = bool(_sohbet_uye)
        _sohbet_kullanici = str(_sohbet_uye or "").strip()

        _kalan_uyari = st.session_state.get("sohbet_uyari")
        if _kalan_uyari:
            _uk1, _uk2 = st.columns([6, 1])
            with _uk1:
                st.error(_kalan_uyari)
            with _uk2:
                if st.button(
                    "Kapat ✕",
                    key="sohbet_uyari_kapat",
                    use_container_width=True
                ):
                    st.session_state["sohbet_uyari"] = ""
                    st.rerun(scope="fragment")

        takip_sayisi_deger = takipci_sayisi()

        # ============================================
        # TAKİP BÖLÜMÜ (KESİN TAKİP - OTTURUM KODUYLA)
        # ============================================
        if takiptesin_mi(_oturum_kodu):
            if st.button(
                "👥 Takiptesin",
                type="secondary",
                use_container_width=True,
                key="takip_birak_btn"
            ):
                takip_birak(_oturum_kodu)
                st.rerun(scope="fragment")
        else:
            if st.button(
                "➕ Takip Et",
                type="primary",
                use_container_width=True,
                key="takip_ekle_btn"
            ):
                takip_ekle(oturum=_oturum_kodu)
                st.rerun(scope="fragment")

        st.caption(
            f"👥 {takip_sayisi_deger} takipçi"
        )

        st.divider()

        # ============================================
        # MESAJ FORMU (MESAJ GÖNDERME ALANI ÜSTTE DURUR)
        # ÖZEL SOHBET: SADECE KAYITLI ÜYELER YAZABİLİR;
        # DIŞARIDAKİLER YALNIZCA OKUYABİLİR.
        # ============================================
        st.subheader("💬 Mesaj Gönder")

        kullanici = _sohbet_kullanici

        if not _sohbet_uyemi:
            st.warning(
                "🔒 **Sohbete mesaj yazmak sadece üyelere açıktır.** "
                "Mesajları okuyabilirsiniz; aşağıdan hemen üye "
                "olabilir ya da giriş yapabilirsiniz."
            )
            with st.container(border=True):
                st.markdown("### 🔐 Üyelik (Giriş / Kayıt)")
                _sk = st.text_input("Kullanıcı adı", key="sohbet_uye_kul")
                _ss = st.text_input(
                    "Şifre", type="password", key="sohbet_uye_sif"
                )
                _bt1, _bt2 = st.columns(2)
                with _bt1:
                    if st.button(
                        "✅ Giriş Yap",
                        key="sohbet_uye_giris_btn",
                        use_container_width=True,
                    ):
                        _gl2 = uye_giris(_sk, _ss)
                        if _gl2:
                            st.session_state["bta_uyelik_user"] = _gl2
                            st.rerun(scope="fragment")
                        elif _gl2 is None:
                            st.error(
                                "Bu kullanıcı adıyla kayıt yok. "
                                "'Kayıt Ol' ile hesap açın."
                            )
                        else:
                            st.error("Şifre hatalı.")
                with _bt2:
                    if st.button(
                        "🔓 Kayıt Ol",
                        key="sohbet_uye_kayit_btn",
                        use_container_width=True,
                    ):
                        if not str(_sk or "").strip() or not _ss:
                            st.warning("Kullanıcı adı ve şifre girin.")
                        elif len(str(_ss).strip()) < 3:
                            st.warning("Şifre en az 3 karakter olsun.")
                        else:
                            _sn2 = uye_kayit(_sk, _ss)
                            if _sn2 == "OK":
                                st.session_state["bta_uyelik_user"] = (
                                    str(_sk).strip()
                                )
                                st.rerun(scope="fragment")
                            else:
                                st.warning(_sn2)
                st.caption(
                    "Üyelikle sohbetten yazışır, kendi hisse listenizi "
                    "oluşturursunuz. Şifreler yalnızca özet (hash) "
                    "olarak saklanır."
                )
        else:
            st.caption(
                f"👤 Adınız: **{_sohbet_kullanici}** "
                "(üyelik adınızla gönderilir)"
            )

        _form_no = st.session_state.get("sohbet_form_no", 0)

        if _sohbet_uyemi:
            st.markdown(
                "😀 Hızlı Emoji (bir ya da birkaçını seçin)"
            )

            _emoji_liste = [
                "🔥", "📈", "💎", "🚀", "💪", "💰",
                "😀", "😂", "😍", "🤔", "👍", "🙏",
                "🎉", "😎", "🤝", "👏", "💯", "📉"
            ]

            _secili_emoji = st.pills(
                "Emoji",
                options=_emoji_liste,
                selection_mode="multi",
                key=f"mesaj_hizli_{_form_no}",
                label_visibility="collapsed",
                help="Mesaja eklemek için bir ya da birkaç "
                     "emoji seçin."
            )

            _emoji_listesi = list(
                _secili_emoji
            ) if _secili_emoji else []

            if _emoji_listesi:
                st.markdown(
                    "Seçilen emojiler: "
                    + " ".join(_emoji_listesi)
                )

            mesaj = st.text_area(
                "Mesajınız",
                height=90,
                placeholder="Mesajınızı yazın...",
                key=f"mesaj_metni_{_form_no}"
            )

            yuklenen_resim = st.file_uploader(
                "📷 Fotoğraf ekle (en fazla 25 MB)",
                type=["png", "jpg", "jpeg", "webp"],
                key=f"mesaj_resim_{_form_no}",
                help="JPG, PNG veya WEBP; büyük dosyalar otomatik "
                     "küçültülür, en fazla 25 MB yüklenebilir."
            )

            _resim_onizleme = ""

            if yuklenen_resim is not None:
                if yuklenen_resim.size > 25 * 1024 * 1024:
                    st.error(
                        "Dosya 25 MB'tan büyük. Lütfen daha küçük "
                        "bir fotoğraf seçin."
                    )
                else:
                    try:
                        _resim_onizleme = resim_mesaj_verisi(
                            yuklenen_resim
                        )

                        st.image(
                            yuklenen_resim,
                            width=220,
                            caption="Yüklenecek fotoğraf"
                        )
                    except Exception as _khata:
                        _resim_onizleme = None
                        st.error(
                            "Fotoğraf okunamadı. JPG, PNG veya WEBP "
                            "bir dosya seçin. "
                            f"({type(_khata).__name__})"
                        )

            gonder = st.button(
                "Mesaj Gönder 🚀",
                use_container_width=True,
                type="primary",
                key="mesaj_gonder_buton"
            )

            if gonder:
                if not _sohbet_uyemi:
                    st.error(
                        "Yazmak için üye girişi yapmalısınız."
                    )
                else:
                    _resim_verisi = _resim_onizleme
                    _resim_hata = False

                    if yuklenen_resim is not None and not _resim_hata:
                        if _resim_onizleme is None or isinstance(
                            _resim_onizleme, str
                        ) and not _resim_onizleme:
                            _resim_hata = True
                            st.error(
                                "Fotoğraf okunamadı. Başka bir dosya deneyin."
                            )

                    if not _resim_hata:
                        _ek_emoji = "".join(
                            _emoji_listesi
                        )

                        _mesaj_son = (
                            mesaj.strip() + " " + _ek_emoji
                        ).strip()

                        if not kullanici.strip():
                            st.error(
                                "Kullanıcı adı boş bırakılamaz."
                            )
                        elif not _mesaj_son and not _resim_verisi:
                            st.error(
                                "Mesaj ve fotoğraf boş bırakılamaz."
                            )
                        else:
                            _engelli_mi, _engel_uyarisi = (
                                kullanici_engelli_mi(_oturum_kodu)
                            )

                            if _engelli_mi:
                                st.session_state["sohbet_uyari"] = _engel_uyarisi
                                st.rerun(scope="fragment")
                            else:
                                _yasakli, _uyari = mesaj_yasakli_mi(
                                    _mesaj_son
                                )

                                if _yasakli:
                                    st.session_state["sohbet_uyari"] = _uyari
                                    st.rerun(scope="fragment")
                                else:
                                    mesaj_ekle(
                                        kullanici.strip(),
                                        _mesaj_son,
                                        resim=_resim_verisi,
                                        oturum=_oturum_kodu
                                    )

                                    st.session_state["sohbet_form_no"] = (
                                        _form_no + 1
                                    )
                                    st.session_state["sohbet_uyari"] = ""

                                    st.success(
                                        "Mesajınız gönderildi."
                                    )

                                    st.rerun(scope="fragment")

        st.divider()

        # ============================================
        # MESAJ LİSTESİ
        # ============================================
        st.subheader("📨 Mesajlar")

        mesajlar = mesajlari_oku()

        if not mesajlar.empty:
            son_mesaj_id = str(
                mesajlar.iloc[-1]["mesaj_id"]
            )

            if "son_ses_mesaj_id" not in st.session_state:
                st.session_state["son_ses_mesaj_id"] = (
                    son_mesaj_id
                )
            elif (
                st.session_state["son_ses_mesaj_id"]
                != son_mesaj_id
            ):
                mesaj_sesi_cal()

                st.session_state["son_ses_mesaj_id"] = (
                    son_mesaj_id
                )

        if mesajlar.empty:
            st.info(
                "Henüz mesaj bulunmuyor."
            )
        else:
            # Aynı kullanıcı hep aynı rengi alır; farklı
            # kullanıcılar birbirinden ayrılır. (Sonlu ve sabit
            # karma için std hash değil, karakter toplamı kullanılır.)
            _kullanici_palet = [
                "#00f5c8", "#4da6ff", "#b48bff",
                "#ff6ec7", "#ffd166", "#ff9f43", "#7ddb6e"
            ]

            # En yeni mesaj en üstte olacak şekilde sıralanır.
            # Silme, tarayıcı "kopyala" menüsü açan ?bta_sil linki
            # yerine gerçek bir Streamlit butonu ile yapılır; böylece
            # mobilde dokununca sayfa kaybolmaz, mesaj doğrudan silinir.
            for index, satir in mesajlar.iloc[::-1].iterrows():
                _mesaj_id = str(satir["mesaj_id"])
                _kullanici = html.escape(str(satir["kullanici"]))
                _mesaj_metni = html.escape(
                    str(satir["mesaj"])
                ).replace("\n", "<br>")

                _resim_ham = str(satir.get("resim", "") or "")

                _kc = (
                    sum(_kullanici.encode("utf-8"))
                    % len(_kullanici_palet)
                )
                _kenar_renk = _kullanici_palet[_kc]

                _kart_html = f"""
                <div class="sohbet-kart"
                     style="border-left-color: {_kenar_renk};">
                    <div class="sohbet-kart-baslik"
                         style="color: {_kenar_renk};">
                        👤 {_kullanici}
                        <span class="sohbet-kart-saat">
                            · {html.escape(str(satir["tarih"]))}
                        </span>
                    </div>
                    <div class="sohbet-mesaj-metni">
                        {_mesaj_metni}
                    </div>
                </div>
                """

                # Mesaj sahibi silme, admin ayrıca susturma/engelleme
                # butonları görür.
                _mesaj_sahibi = str(satir["kullanici"]).strip()
                _mesaj_oturum = str(
                    satir.get("oturum", "") or ""
                ).strip()
                _silebilir = bool(_mesaj_sahibi) and (
                    is_admin or _mesaj_sahibi == kullanici.strip()
                )
                _admin_ileti = is_admin and bool(
                    _mesaj_oturum or _mesaj_sahibi
                )

                if _admin_ileti:
                    _kart_kol, _sust_kol, _eng_kol, _sil_kol = \
                        st.columns([4, 1, 1, 1])
                elif _silebilir:
                    _kart_kol, _sil_kol = st.columns([5, 1])
                else:
                    _kart_kol = st.container()
                    _sil_kol = None

                with _kart_kol:
                    st.markdown(
                        _kart_html,
                        unsafe_allow_html=True
                    )

                    if _resim_ham.startswith("data:image"):
                        try:
                            _gorsel_bytes = _b64_veri_ayikla(
                                _resim_ham
                            )
                            if _gorsel_bytes:
                                _thumb_veri = _resim_thumb(
                                    _gorsel_bytes,
                                    genislik=180
                                )
                                _thumb_src = (
                                    _thumb_veri or _resim_ham
                                )

                                st.markdown(
                                    f"""
                                    <details style="margin:4px 0;">
                                        <summary style="cursor:zoom-in;
                                               list-style:none;
                                               display:inline-block;
                                               text-decoration:none;">
                                            <img src="{_thumb_src}"
                                                 alt="Tıklayıp büyütün"
                                                 style="max-width:180px;
                                                        height:auto;
                                                        border-radius:8px;
                                                        border:1px solid
                                                        rgba(255,255,255,0.3);
                                                        box-shadow:0 2px 8px
                                                        rgba(0,0,0,0.4);" />
                                            <div style="font-size:11px;
                                                        color:#8aa7bb;
                                                        margin-top:2px;">
                                                🔍 Tıklayıp büyütün
                                            </div>
                                        </summary>
                                        <img src="{_resim_ham}"
                                             alt="Büyük görsel"
                                             style="max-width:100%;
                                                    height:auto;
                                                    border-radius:8px;
                                                    border:1px solid
                                                    rgba(255,255,255,0.25);
                                                    margin-top:6px;" />
                                    </details>
                                    """,
                                    unsafe_allow_html=True
                                )
                        except Exception:
                            pass

                if _admin_ileti:
                    with _sust_kol:
                        st.write("")
                        if st.button(
                            "🔇",
                            key=f"bta_mesaj_sustur_{_mesaj_id}",
                            help=(
                                f"{_mesaj_sahibi} kullanıcısını "
                                "1 gün sustur"
                            ),
                            use_container_width=True
                        ):
                            kullanici_engelle(
                                _mesaj_sahibi or _mesaj_oturum,
                                gun=1,
                                oturum=_mesaj_oturum
                            )
                            st.rerun(scope="fragment")

                    with _eng_kol:
                        st.write("")
                        if st.button(
                            "🚫",
                            key=f"bta_mesaj_engel_{_mesaj_id}",
                            help=(
                                f"{_mesaj_sahibi} kullanıcısını "
                                "kalıcı engelle"
                            ),
                            use_container_width=True
                        ):
                            kullanici_engelle(
                                _mesaj_sahibi or _mesaj_oturum,
                                gun=0,
                                oturum=_mesaj_oturum
                            )
                            st.rerun(scope="fragment")

                if _sil_kol is not None:
                    with _sil_kol:
                        st.write("")
                        if st.button(
                            "🗑️",
                            key=f"bta_mesaj_sil_{_mesaj_id}",
                            help="Bu mesajı sil",
                            use_container_width=True
                        ):
                            _kalan = mesajlari_oku()
                            _kalan = _kalan[
                                _kalan["mesaj_id"].astype(str)
                                != _mesaj_id
                            ]
                            _kalan.to_csv(
                                MESAJ_DOSYASI,
                                index=False,
                                encoding="utf-8-sig"
                            )
                            st.rerun()

    _sohbet_fragment()


# ==================================================
# YÖNETİCİYE ÖZEL MESAJ (DM) - ÖZEL SEKME
# ==================================================
with tab_dm:
    st.markdown(
        sekme_baslik_format(
            "✉️", "Yöneticiye Mesaj", "#ffd166"
        ),
        unsafe_allow_html=True
    )

    st.markdown(
        "Bu mesajlar **sohbette GÖRÜNMEZ**; yalnızca yönetici "
        "okuyabilir. Gönderilmeden önce mesajınızın hakaret, "
        "yatırım yönlendirmesi ya da reklam içermediğinden emin olun."
    )

    _tabdm_oturum = ziyaretci_oturum_kodu()
    _tabdm_uye = st.session_state.get("bta_uyelik_user")
    _tabdm_uyemi = bool(_tabdm_uye)
    _tabdm_kullanici = str(_tabdm_uye or "").strip()

    if not _tabdm_uyemi:
        st.caption(
            "🔒 DM göndermek üyelik ister; üye olmayanlar "
            "yalnızca okuyabilir."
        )

    with st.form(key="dm_formu", clear_on_submit=True):
        _dm_konu = st.text_input(
            "Konu (isteğe bağlı)",
            key="dm_konu",
            placeholder="Örn: Bölüm önerisi, sorun bildirimi"
        )
        _dm_kullanici_ad = st.text_input(
            "Kullanıcı adınız (DM için)",
            key="dm_kullanici_ad",
            placeholder=("Üyelik adınız" if _tabdm_uyemi else "Sohbetteki adınızı yazın")
        ).strip()

        _dm_metin = st.text_area(
            "Mesajınız",
            height=70,
            key="dm_metin",
            placeholder="Yöneticiye iletmek istediğiniz "
                        "mesajı yazın..."
        )
        _dm_gonder = st.form_submit_button(
            "✉️ Gönder",
            use_container_width=True
        )

        if _dm_gonder:
            if not _tabdm_uyemi:
                st.error(
                    "DM göndermek için önce üye girişi "
                    "yapmalısınız."
                )
            elif not _dm_metin.strip():
                st.error(
                    "Yöneticiye göndermek için mesaj "
                    "yazmalısınız."
                )
            else:
                yonetici_mesaji_ekle(
                    kullanici=(
                        _tabdm_kullanici
                        or _dm_kullanici_ad
                    ),
                    oturum=_tabdm_oturum,
                    mesaj=_dm_metin.strip()
                )
                st.success(
                    "Mesajınız yöneticiye iletildi. "
                    "Sohbette görünmez."
                )


# ==================================================
# SON HABER BÜLTENİ (bugünün gündemi, büyük ve okunaklı)
# ==================================================
with tab_haber:
    _haber_durum = st.session_state.get("bta_haber_durum", {})
    _haber_yeni_kimlik = (
        _haber_durum.get("bulten", {}).get("yeni_kimlikler") or set()
    )
    _bulten_yeni = _haber_durum.get("bulten", {}).get("yeni_say", 0)

    _haberler = (
        st.session_state.get("bta_haber_veri", {}).get("bulten")
        or son_dakika_haberleri_getir()
    )

    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #ff5264;
            border-color: #ff5264;
            background: linear-gradient(
                90deg,
                rgba(255, 82, 100, 0.22),
                rgba(255, 82, 100, 0.06)
            );
            box-shadow: 0 0 18px rgba(255, 82, 100, 0.3);
        ">
            <span style="color: #ff5264;
                         text-shadow: 0 0 14px rgba(255, 82, 100, 0.8);">
                SON HABER BÜLTENİ
            </span>
            <span class="sekme-baslik-tarih">Son 48 Saat</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    if _bulten_yeni:
        st.success(f"🔴 {_bulten_yeni} yeni haber var!")

    _haber_filtre = st.text_input(
        "🔎 Haberlerde ara",
        placeholder="Örn: ekonomi, borsa, enflasyon",
        key="son_dakika_haber_filtre"
    ).strip().lower()

    if _haber_filtre:
        _haberler = [
            _h for _h in _haberler
            if _haber_filtre in _h[0].lower()
        ]

    if not _haberler:
        st.info(
            "Şu anda habere ulaşılamadı, birazdan "
            "tekrar deneniyor."
        )
    else:
        _haber_renkleri = [
            "#00f5c8", "#4da6ff", "#b48bff",
            "#ff6ec7", "#ffd166", "#ff9f43", "#7ddb6e"
        ]

        for _baslik, _link, _zaman in _haberler:
            _yeni_rozet = (
                '<span class="bta-yeni-rozet">🆕 YENİ</span>'
                if _haber_kimlik(_baslik) in _haber_yeni_kimlik
                else ""
            )
            st.markdown(
                f"""
                <div class="haber-bulteni-kart">
                    <div class="haber-bulteni-saat">
                        {_yeni_rozet}🕒 {_zaman}
                    </div>
                    <a href="{_link}" target="_blank"
                       class="haber-bulteni-link">
                        {_baslik}
                    </a>
                </div>
                """,
                unsafe_allow_html=True
            )

    st.caption(
        "Haberler Google News gündem akışından alınır; "
        "yalnızca bugün yayınlananlar listelenir. "
        "Başlığa dokunarak haber kaynağına gidebilirsiniz."
    )


# ==================================================
# KAP HABERLERİ (Kamuyu Aydınlatma Platformu)
# ==================================================
with tab_kap:
    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #ffd166;
            border-color: #ffd166;
            background: linear-gradient(
                90deg,
                rgba(255, 209, 102, 0.22),
                rgba(255, 209, 102, 0.06)
            );
            box-shadow: 0 0 18px rgba(255, 209, 102, 0.3);
        ">
            <span style="color: #ffd166;
                         text-shadow: 0 0 14px rgba(255, 209, 102, 0.8);">
                KAP HABERLERİ
            </span>
            <span class="sekme-baslik-tarih">Son 48 Saat</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    _kap_durum = st.session_state.get("bta_haber_durum", {}).get("kap", {})
    _kap_yeni_kimlik = _kap_durum.get("yeni_kimlikler") or set()
    _kap_yeni = _kap_durum.get("yeni_say", 0)

    if _kap_yeni:
        st.success(f"🔴 {_kap_yeni} yeni KAP haberi var!")

    _kap_hisse_filtre = st.text_input(
        "🏷 Hisse Kodu",
        placeholder="Örn: THYAO (boş bırakılırsa tüm KAP haberleri)",
        key="kap_hisse_filtre"
    ).strip().upper()

    if _kap_hisse_filtre:
        _kap_haberler = kap_haberleri_getir(_kap_hisse_filtre)
    else:
        _kap_haberler = (
            st.session_state.get("bta_haber_veri", {}).get("kap")
            or kap_haberleri_getir("")
        )

    _kap_filtre = st.text_input(
        "🔎 Haberlerde ara",
        placeholder="Örn: şirket adı, kar, temettü",
        key="kap_haber_filtre"
    ).strip().lower()

    if _kap_filtre:
        _kap_haberler = [
            _h for _h in _kap_haberler
            if _kap_filtre in _h[0].lower()
        ]

    if not _kap_haberler:
        st.info(
            "Şu anda KAP haberi bulunamadı, birazdan "
            "tekrar deneniyor."
        )
    else:
        for (
            _baslik, _link, _zaman, _kaynak
        ) in _kap_haberler:
            _kap_yeni_rozet = (
                '<span class="bta-yeni-rozet">🆕 YENİ</span>'
                if _haber_kimlik(_baslik) in _kap_yeni_kimlik
                else ""
            )
            st.markdown(
                f"""
                <div class="haber-bulteni-kart arz-kart">
                    <div class="haber-bulteni-saat">
                        {_kap_yeni_rozet}🕒 {_zaman}
                        <span class="arz-kaynak">
                            · {_kaynak or "Haber"}
                        </span>
                    </div>
                    <a href="{_link}" target="_blank"
                       class="haber-bulteni-link">
                        {_baslik}
                    </a>
                </div>
                """,
                unsafe_allow_html=True
            )

    st.caption(
        "KAP haberleri Google News arama akışından alınır; "
        "her 10 dakikada bir tazelenir. Kesin bilgi için "
        "Kamuyu Aydınlatma Platformu (KAP) sitesini kontrol edin."
    )


# ==================================================
# SPK HABERLERİ (Sermaye Piyasası Kurulu)
# ==================================================
with tab_spk:
    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #7ddb6e;
            border-color: #7ddb6e;
            background: linear-gradient(
                90deg,
                rgba(125, 219, 110, 0.22),
                rgba(125, 219, 110, 0.06)
            );
            box-shadow: 0 0 18px rgba(125, 219, 110, 0.3);
        ">
            <span style="color: #7ddb6e;
                         text-shadow: 0 0 14px rgba(125, 219, 110, 0.8);">
                SPK HABERLERİ
            </span>
            <span class="sekme-baslik-tarih">Son 48 Saat</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    _spk_durum = st.session_state.get("bta_haber_durum", {}).get("spk", {})
    _spk_yeni_kimlik = _spk_durum.get("yeni_kimlikler") or set()
    _spk_yeni = _spk_durum.get("yeni_say", 0)

    if _spk_yeni:
        st.success(f"🔴 {_spk_yeni} yeni SPK haberi var!")

    _spk_hisse_filtre = st.text_input(
        "🏷 Hisse Kodu",
        placeholder="Örn: THYAO (boş bırakılırsa tüm SPK haberleri)",
        key="spk_hisse_filtre"
    ).strip().upper()

    if _spk_hisse_filtre:
        _spk_haberler = spk_haberleri_getir(_spk_hisse_filtre)
    else:
        _spk_haberler = (
            st.session_state.get("bta_haber_veri", {}).get("spk")
            or spk_haberleri_getir("")
        )

    _spk_filtre = st.text_input(
        "🔎 Haberlerde ara",
        placeholder="Örn: ceza, onay, izahname",
        key="spk_haber_filtre"
    ).strip().lower()

    if _spk_filtre:
        _spk_haberler = [
            _h for _h in _spk_haberler
            if _spk_filtre in _h[0].lower()
        ]

    if not _spk_haberler:
        st.info(
            "Şu anda SPK haberi bulunamadı, birazdan "
            "tekrar deneniyor."
        )
    else:
        for (
            _baslik, _link, _zaman, _kaynak
        ) in _spk_haberler:
            _spk_yeni_rozet = (
                '<span class="bta-yeni-rozet">🆕 YENİ</span>'
                if _haber_kimlik(_baslik) in _spk_yeni_kimlik
                else ""
            )
            st.markdown(
                f"""
                <div class="haber-bulteni-kart arz-kart">
                    <div class="haber-bulteni-saat">
                        {_spk_yeni_rozet}🕒 {_zaman}
                        <span class="arz-kaynak">
                            · {_kaynak or "Haber"}
                        </span>
                    </div>
                    <a href="{_link}" target="_blank"
                       class="haber-bulteni-link">
                        {_baslik}
                    </a>
                </div>
                """,
                unsafe_allow_html=True
            )

    st.caption(
        "SPK haberleri Google News arama akışından alınır; "
        "her 10 dakikada bir tazelenir. Yatırım tavsiyesi değildir."
    )


# ==================================================
# GÜNCEL ARZ (HALKA ARZ) HABERLERİ
# ==================================================
with tab_arz:
    _arz_durum = st.session_state.get("bta_haber_durum", {}).get("arz", {})
    _arz_yeni_kimlik = _arz_durum.get("yeni_kimlikler") or set()
    _arz_yeni = _arz_durum.get("yeni_say", 0)

    _arz_haberler = (
        st.session_state.get("bta_haber_veri", {}).get("arz")
        or arz_haberleri_getir()
    )

    st.markdown(
        f"""
        <div class="sekme-baslik" style="
            border-left-color: #7ddb6e;
            border-color: #7ddb6e;
            background: linear-gradient(
                90deg,
                rgba(125, 219, 110, 0.22),
                rgba(125, 219, 110, 0.06)
            );
            box-shadow: 0 0 18px rgba(125, 219, 110, 0.3);
        ">
            <span style="color: #7ddb6e;
                         text-shadow: 0 0 14px rgba(125, 219, 110, 0.8);">
                GÜNCEL ARZ HABERLERİ
            </span>
            <span class="sekme-baslik-tarih">Son 48 Saat</span>
        </div>
        """,
        unsafe_allow_html=True
    )

    if _arz_yeni:
        st.success(f"🔴 {_arz_yeni} yeni halka arz haberi var!")

    _arz_filtre = st.text_input(
        "🔎 Haberlerde ara",
        placeholder="Örn: halka arz, talep toplama",
        key="arz_haber_filtre"
    ).strip().lower()

    if _arz_filtre:
        _arz_haberler = [
            _h for _h in _arz_haberler
            if _arz_filtre in _h[0].lower()
        ]

    if not _arz_haberler:
        st.info(
            "Şu anda halka arz haberi bulunamadı, birazdan "
            "tekrar deneniyor."
        )
    else:
        for (
            _baslik, _link, _zaman, _kaynak
        ) in _arz_haberler:
            _arz_yeni_rozet = (
                '<span class="bta-yeni-rozet">🆕 YENİ</span>'
                if _haber_kimlik(_baslik) in _arz_yeni_kimlik
                else ""
            )
            st.markdown(
                f"""
                <div class="haber-bulteni-kart arz-kart">
                    <div class="haber-bulteni-saat">
                        {_arz_yeni_rozet}🕒 {_zaman}
                        <span class="arz-kaynak">
                            · {_kaynak or "Haber"}
                        </span>
                    </div>
                    <a href="{_link}" target="_blank"
                       class="haber-bulteni-link">
                        {_baslik}
                    </a>
                </div>
                """,
                unsafe_allow_html=True
            )

    st.caption(
        "Halka arz haberleri Google News arama akışından alınır; "
        "yatırım tavsiyesi değildir. Başlığa dokunarak kaynağa gidebilirsiniz."
    )


# ==================================================
# PAYLAŞ TAB'I
# ==================================================
with tab_paylas:
    st.markdown(
        sekme_baslik_format(
            "🔗", "Sayfayı Sosyal Medyada Paylaş", "#ff9f43"
        ),
        unsafe_allow_html=True
    )

    st.divider()

    # ==================================================
    # PAYLAŞ URL'Sİ
    # ==================================================
    st.subheader("📍 Paylaş Linki")

    sayfa_url = st.text_input(
        "Platform URL:",
        value="https://btasinyal.streamlit.app",
        help="Paylaşmak istediğiniz sayfanın tam URL'sini girin"
    )

    baslik = st.text_input(
        "Paylaşım Başlığı:",
        value="BTA Algoritmik İşlem Platformu - Borsa Sinyalleri"
    )

    st.divider()

    # ==================================================
    # PAYLAŞ BUTONLARI
    # ==================================================
    st.subheader("📱 Sosyal Medya Kanalları")

    # Paylaşım linklerini oluştur
    twitter_link = paylas_linki_olustur("twitter", sayfa_url, baslik)
    facebook_link = paylas_linki_olustur("facebook", sayfa_url, baslik)
    linkedin_link = paylas_linki_olustur("linkedin", sayfa_url, baslik)
    whatsapp_link = paylas_linki_olustur("whatsapp", sayfa_url, baslik)
    telegram_link = paylas_linki_olustur("telegram", sayfa_url, baslik)
    email_link = paylas_linki_olustur("email", sayfa_url, baslik)

    # Butonları göster
    st.markdown(
        f"""
        <div class="paylas-container">
            <a href="{twitter_link}" target="_blank" class="paylas-buton paylas-twitter">🐦 Twitter</a>
            <a href="{facebook_link}" target="_blank" class="paylas-buton paylas-facebook">👍 Facebook</a>
            <a href="{linkedin_link}" target="_blank" class="paylas-buton paylas-linkedin">💼 LinkedIn</a>
            <a href="{whatsapp_link}" target="_blank" class="paylas-buton paylas-whatsapp">💬 WhatsApp</a>
            <a href="{telegram_link}" target="_blank" class="paylas-buton paylas-telegram">✈️ Telegram</a>
            <a href="{email_link}" class="paylas-buton paylas-email">✉️ E-Posta</a>
            <button class="paylas-buton paylas-kopya" onclick="
                navigator.clipboard.writeText('{sayfa_url}');
                alert('Link kopyalandı! 📋');
            ">📋 Linki Kopyala</button>
        </div>
        """,
        unsafe_allow_html=True
    )

    st.divider()

    # ==================================================
    # QR KOD - NORMAL (SİYAH-BEYAZ), KART GÖRÜNÜMLÜ
    # ==================================================
    st.subheader("📱 QR Kod ile Hızlı Erişim")

    try:
        import io
        import base64
        import qrcode

        # Telefon kamerasının okuyabilmesi için QR her zaman
        # SİYAH kareler + BEYAZ zemin olmalıdır. Önceki renkli
        # (turkuaz/koyu lacivert) sürüm telefonlarda okunmuyordu.
        qr = qrcode.QRCode(
            version=1,
            error_correction=qrcode.constants.ERROR_CORRECT_L,
            box_size=10,
            border=4,
        )

        qr.add_data(sayfa_url)
        qr.make(fit=True)

        qr_img = qr.make_image(
            fill_color="black",
            back_color="white"
        )

        _qr_buf = io.BytesIO()
        qr_img.save(_qr_buf, format="PNG")
        _qr_b64 = (
            base64.b64encode(
                _qr_buf.getvalue()
            ).decode("utf-8")
        )

        st.markdown(
            f"""
            <div class="qr-kart">
                <div class="qr-kart-ust">
                    📱 BTA Platform · Hızlı Erişim
                </div>
                <div class="qr-kart-gorsel">
                    <img src="data:image/png;base64,{_qr_b64}"
                         alt="BTA QR kodu" />
                </div>
                <div class="qr-kart-link">
                    🔗 {sayfa_url}
                </div>
                <div class="qr-kart-alt">
                    Kameranızla okutup paylaşın · Basıp
                    arkadaşınıza gösterebilirsiniz
                </div>
            </div>
            """,
            unsafe_allow_html=True
        )

    except ImportError:
        st.info("QR kod göstermek için: pip install qrcode[pil]")

    st.divider()

    # ==================================================
    # İSTATİSTİKLER
    # ==================================================
    st.subheader("📊 Platform İstatistikleri")

    col1, col2 = st.columns(2)

    with col1:
        st.metric("🤝 Takipçi", takipci_sayisi())

    with col2:
        st.metric("💬 Mesajlar", len(mesajlari_oku()))


# ==================================================
# PWA DESTEĞİ - ANA EKRANA EKLE
# ==================================================
# Telefonda "Ana ekrana ekle" ile uygulama gibi (adres çubuğu
# olmadan, tam ekran) açılmasını sağlar.
#
# Streamlit kök dizine dosya (manifest.json, service worker)
# sunamadığı için her şey tarayıcıda, JavaScript ile eklenir:
#   - Web App Manifest  (Android / Chrome)
#   - apple-touch-icon + apple-mobile-web-app-* etiketleri (iPhone)
#   - Küçük bir "Ana ekrana ekle" kartı (kapatılabilir)
# Simgeler Pillow ile çalışma anında üretilir; ek dosya gerekmez.
# ==================================================
@st.cache_resource(show_spinner=False)
def _pwa_ikon_verileri():
    import base64
    import io
    from PIL import ImageDraw

    arka = (7, 19, 31, 255)      # #07131f (uygulama arka planı)
    renk = (0, 245, 200, 255)    # #00f5c8 (BTA turkuazı)
    yeniden = getattr(Image, "Resampling", Image).LANCZOS

    def ciz(boyut, glif_orani, yuvarlak):
        ust = 4  # daha yumuşak kenarlar için büyük çizip küçült
        b = boyut * ust
        img = Image.new("RGBA", (b, b), (0, 0, 0, 0))
        d = ImageDraw.Draw(img)

        if yuvarlak:
            d.rounded_rectangle(
                [0, 0, b - 1, b - 1], radius=int(b * 0.22), fill=arka
            )
        else:
            d.rectangle([0, 0, b, b], fill=arka)

        # Logo 64x64 koordinatında; ortalanıp ölçeklenir.
        k = b * glif_orani / 40.0

        def nokta(x, y):
            return (b / 2 + (x - 32) * k, b / 2 + (y - 31) * k)

        kalinlik = max(2, int(3.2 * k))
        r = 4.6 * k
        noktalar = [(12, 48), (24, 30), (36, 38), (52, 14)]

        d.line([nokta(*n) for n in noktalar], fill=renk, width=kalinlik)
        d.line([nokta(12, 48), nokta(52, 48)], fill=renk, width=kalinlik)

        for n in noktalar:
            cx, cy = nokta(*n)
            d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=renk)

        # Taban çizgisinin sağ ucu (yuvarlak uç)
        cx, cy = nokta(52, 48)
        yr = kalinlik / 2
        d.ellipse([cx - yr, cy - yr, cx + yr, cy + yr], fill=renk)

        return img.resize((boyut, boyut), yeniden)

    def uri(img):
        buf = io.BytesIO()
        img.save(buf, format="PNG", optimize=True)
        return (
            "data:image/png;base64,"
            + base64.b64encode(buf.getvalue()).decode("ascii")
        )

    return {
        "i192": uri(ciz(192, 0.62, True)),
        "i512": uri(ciz(512, 0.62, True)),
        # maskable: Android'in yuvarlatma/kırpma alanına sığsın diye
        # logo daha küçük ve arka plan tam dolu
        "maskable": uri(ciz(512, 0.50, False)),
        # iOS köşeleri kendisi yuvarlar; saydamlık siyah görünür
        "apple": uri(ciz(180, 0.62, False).convert("RGB")),
    }


_PWA_JS = r"""
<script>
(function () {
  var CFG = __CFG__;

  function guvenli(fn) { try { return fn(); } catch (e) { return null; } }

  // Streamlit bileşeni bir iframe içinde çalışır. Streamlit Cloud'da
  // uygulama ayrıca bir kabuk sayfasının içindedir; manifest'in geçerli
  // olması için EN ÜSTTEKİ sayfaya (erişilebiliyorsa) eklenir.
  var P = guvenli(function () {
    return window.parent.document ? window.parent : null;
  });
  var T = guvenli(function () {
    var t = window.top;
    return t.document ? t : null;
  });
  if (!P && !T) { return; }
  var UST = T || P;   // manifest + iOS etiketleri
  var UI = P || T;    // kartın gösterileceği belge

  var hedefler = (UST === UI) ? [UST] : [UST, UI];

  function meta(win, ad, icerik) {
    var d = win.document;
    var m = d.querySelector('meta[name="' + ad + '"]');
    if (!m) {
      m = d.createElement('meta');
      m.setAttribute('name', ad);
      d.head.appendChild(m);
    }
    m.setAttribute('content', icerik);
  }

  function pwaEtiketleriEkle(win) {
    var d = win.document;
    if (d.head.querySelector('link[data-bta-pwa]')) { return; }

    var yol = win.location.origin + win.location.pathname;
    var manifest = {
      id: yol,
      name: CFG.ad,
      short_name: CFG.kisaAd,
      description: CFG.aciklama,
      lang: 'tr',
      dir: 'ltr',
      start_url: yol,
      scope: win.location.origin + '/',
      display: 'standalone',
      orientation: 'any',
      background_color: CFG.arka,
      theme_color: CFG.arka,
      categories: ['finance'],
      icons: [
        { src: CFG.i192, sizes: '192x192', type: 'image/png', purpose: 'any' },
        { src: CFG.i512, sizes: '512x512', type: 'image/png', purpose: 'any' },
        { src: CFG.maskable, sizes: '512x512', type: 'image/png', purpose: 'maskable' }
      ]
    };

    // Blob, sayfanın kendi penceresinde üretilir; böylece bu iframe
    // yenilense bile manifest adresi geçerli kalır.
    var blob = new win.Blob([JSON.stringify(manifest)],
                            { type: 'application/manifest+json' });
    var mUrl = win.URL.createObjectURL(blob);

    Array.prototype.forEach.call(
      d.querySelectorAll('link[rel="manifest"], link[rel="apple-touch-icon"]'),
      function (el) { el.parentNode.removeChild(el); }
    );

    var lm = d.createElement('link');
    lm.setAttribute('rel', 'manifest');
    lm.setAttribute('href', mUrl);
    lm.setAttribute('data-bta-pwa', '1');
    d.head.appendChild(lm);

    var la = d.createElement('link');
    la.setAttribute('rel', 'apple-touch-icon');
    la.setAttribute('sizes', '180x180');
    la.setAttribute('href', CFG.apple);
    d.head.appendChild(la);

    meta(win, 'theme-color', CFG.arka);
    meta(win, 'application-name', CFG.kisaAd);
    meta(win, 'apple-mobile-web-app-capable', 'yes');
    meta(win, 'mobile-web-app-capable', 'yes');
    meta(win, 'apple-mobile-web-app-title', CFG.kisaAd);
    meta(win, 'apple-mobile-web-app-status-bar-style', 'black');
  }

  // 1) Önce dinleyiciler, sonra manifest: Chrome manifest'i görünce
  //    'beforeinstallprompt' olayını gönderir; kaçırılmamalı.
  var durum = UST.__btaPwa || (UST.__btaPwa = { hazir: null, kuruldu: false });
  if (!durum.dinliyor) {
    durum.dinliyor = true;
    UST.addEventListener('beforeinstallprompt', function (e) {
      e.preventDefault();
      durum.hazir = e;
    });
    UST.addEventListener('appinstalled', function () {
      durum.kuruldu = true;
      durum.hazir = null;
      var b = UI.document.getElementById('bta-pwa-banner');
      if (b) { b.parentNode.removeChild(b); }
    });
  }

  hedefler.forEach(function (w) { guvenli(function () { pwaEtiketleriEkle(w); }); });

  // 2) "Ana ekrana ekle" kartı
  var ud = UI.document;

  function uygulamaModunda() {
    return !!(guvenli(function () {
      return UST.matchMedia('(display-mode: standalone)').matches ||
             UST.navigator.standalone === true;
    }));
  }
  var ua = UST.navigator.userAgent || '';
  var ios = /iphone|ipad|ipod/i.test(ua) ||
            (UST.navigator.platform === 'MacIntel' && UST.navigator.maxTouchPoints > 1);
  var dokunmatik = !!guvenli(function () {
    return UST.matchMedia('(pointer: coarse)').matches;
  });

  var ANAHTAR = 'bta_pwa_gizle';
  var GIZLEME_MS = 7 * 24 * 60 * 60 * 1000;
  function gizlendi() {
    var t = guvenli(function () { return parseInt(UI.localStorage.getItem(ANAHTAR) || '0', 10); });
    return !!t && (Date.now() - t) < GIZLEME_MS;
  }
  function gizle() {
    guvenli(function () { UI.localStorage.setItem(ANAHTAR, String(Date.now())); });
    var b = ud.getElementById('bta-pwa-banner');
    if (b) { b.parentNode.removeChild(b); }
  }

  function stilEkle() {
    if (ud.getElementById('bta-pwa-stil')) { return; }
    var s = ud.createElement('style');
    s.id = 'bta-pwa-stil';
    s.textContent =
      '#bta-pwa-banner{position:fixed;left:12px;right:12px;' +
      'bottom:calc(env(safe-area-inset-bottom,0px) + 14px);' +
      'z-index:2147483000;max-width:460px;margin:0 auto;display:flex;' +
      'align-items:center;gap:12px;padding:10px 12px;border-radius:16px;' +
      'background:rgba(4,13,24,.97);border:1px solid rgba(0,245,200,.45);' +
      'box-shadow:0 10px 30px rgba(0,0,0,.55),0 0 18px rgba(0,245,200,.15);' +
      'color:#e8f4f8;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;' +
      'animation:btaPwaGir .35s ease-out}' +
      '#bta-pwa-banner *{text-shadow:none!important;box-sizing:border-box}' +
      '@keyframes btaPwaGir{from{transform:translateY(24px);opacity:0}to{transform:none;opacity:1}}' +
      '#bta-pwa-banner img{width:44px;height:44px;border-radius:10px;flex:none}' +
      '#bta-pwa-banner .bp-metin{flex:1;min-width:0;display:flex;flex-direction:column;gap:2px;' +
      'font-size:12.5px;line-height:1.35;color:#c9dbe4}' +
      '#bta-pwa-banner .bp-metin b{font-size:14px;color:#00f5c8}' +
      '#bta-pwa-ekle{flex:none;border:0;border-radius:10px;padding:9px 14px;font-weight:700;' +
      'font-size:13px;background:linear-gradient(135deg,#00f5c8,#00c2a0);color:#04121c;cursor:pointer}' +
      '#bta-pwa-kapat{flex:none;border:0;background:transparent;color:#8aa4b3;font-size:18px;' +
      'padding:4px 6px;cursor:pointer}';
    ud.head.appendChild(s);
  }

  var METINLER = {
    kur:  'Uygulama gibi, tam ekran açılır.',
    ios:  'Safari’de alttaki Paylaş (⬆︎) simgesine dokun, ardından “Ana Ekrana Ekle”yi seç.',
    menu: 'Tarayıcı menüsünden (⋮) “Ana ekrana ekle” veya “Uygulamayı yükle”yi seç.'
  };

  function bannerGoster(mod) {
    if (ud.getElementById('bta-pwa-banner')) { return; }
    stilEkle();

    var b = ud.createElement('div');
    b.id = 'bta-pwa-banner';
    b.setAttribute('role', 'dialog');
    b.setAttribute('aria-label', 'Ana ekrana ekle');

    var img = ud.createElement('img');
    img.alt = '';
    img.src = CFG.apple;
    b.appendChild(img);

    var m = ud.createElement('div');
    m.className = 'bp-metin';
    var baslik = ud.createElement('b');
    baslik.textContent = 'BTA’yı ana ekrana ekle';
    var alt = ud.createElement('span');
    alt.textContent = METINLER[mod];
    m.appendChild(baslik);
    m.appendChild(alt);
    b.appendChild(m);

    if (mod === 'kur') {
      var ekle = ud.createElement('button');
      ekle.id = 'bta-pwa-ekle';
      ekle.type = 'button';
      ekle.textContent = 'Ekle';
      ekle.addEventListener('click', function () {
        var olay = durum.hazir;
        if (!olay) { alt.textContent = METINLER.menu; ekle.style.display = 'none'; return; }
        olay.prompt();
        olay.userChoice.then(function (s) {
          durum.hazir = null;
          if (s && s.outcome === 'accepted') { durum.kuruldu = true; }
          gizle();
        });
      });
      b.appendChild(ekle);
    }

    var kapat = ud.createElement('button');
    kapat.id = 'bta-pwa-kapat';
    kapat.type = 'button';
    kapat.setAttribute('aria-label', 'Kapat');
    kapat.textContent = '✕';
    kapat.addEventListener('click', gizle);
    b.appendChild(kapat);

    ud.body.appendChild(b);
  }

  function planla() {
    if (uygulamaModunda() || durum.kuruldu || gizlendi() || !dokunmatik) { return; }
    if (ios) {
      setTimeout(function () { bannerGoster('ios'); }, 2500);
      return;
    }
    (function bekle(n) {
      if (durum.kuruldu) { return; }
      if (durum.hazir) { bannerGoster('kur'); return; }
      if (n >= 12) { bannerGoster('menu'); return; }   // ~6 sn sonra
      setTimeout(function () { bekle(n + 1); }, 500);
    })(0);
  }

  planla();
})();
</script>
"""


def pwa_destegi_ekle():
    _ikon = _pwa_ikon_verileri()
    _cfg = {
        "ad": "BTA Algoritmik İşlem",
        "kisaAd": "BTA",
        "aciklama": "BIST hisse sinyalleri ve algoritmik işlem takibi",
        "arka": "#07131f",
        "i192": _ikon["i192"],
        "i512": _ikon["i512"],
        "maskable": _ikon["maskable"],
        "apple": _ikon["apple"],
    }
    components.html(
        _PWA_JS.replace("__CFG__", json.dumps(_cfg)),
        height=0,
        width=0
    )


# Sayfanın en sonunda, ana akışın DIŞINDA çağrılır (boşluk bırakmaz).
pwa_destegi_ekle()


_BTA_ARKA_JS = r"""
<script>
(function () {
  function guvenli(fn) { try { return fn(); } catch (e) { return null; } }

  var W = guvenli(function () {
    return (window.parent && window.parent.document) ? window.parent : null;
  });
  if (!W) { return; }
  if (W.__btaArkaPlan) { return; }
  W.__btaArkaPlan = true;

  var D = W.document;

  function kur(deneme) {
    if (D.getElementById('bta-arka-canvas')) { return; }
    var kap = D.querySelector('.stApp') || D.body;
    if (!kap || !D.body) {
      if ((deneme || 0) < 40) {
        W.setTimeout(function () { kur((deneme || 0) + 1); }, 150);
      }
      return;
    }

    var c = D.createElement('canvas');
    c.id = 'bta-arka-canvas';
    kap.appendChild(c);

    var ctx = c.getContext('2d');
    var dpr = Math.min(W.devicePixelRatio || 1, 2);
    var gen = 0, yuk = 0;
    var noktalar = [];
    var calisiyor = true;

    function olcekle() {
      gen = W.innerWidth;
      yuk = W.innerHeight;
      c.width = gen * dpr;
      c.height = yuk * dpr;
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      var sayi = Math.round(gen * yuk / 26000);
      if (sayi < 16) { sayi = 16; }
      if (sayi > 64) { sayi = 64; }
      noktalar = [];
      for (var i = 0; i < sayi; i++) {
        noktalar.push({
          x: Math.random() * gen,
          y: Math.random() * yuk,
          vx: (Math.random() - 0.5) * 0.35,
          vy: (Math.random() - 0.5) * 0.35,
          r: Math.random() * 1.6 + 0.8
        });
      }
    }
    olcekle();
    W.addEventListener('resize', olcekle);

    D.addEventListener('visibilitychange', function () {
      calisiyor = !D.hidden;
    });

    var ESIK = 16000;

    function ciz(t) {
      ctx.clearRect(0, 0, gen, yuk);

      var j, p, a, b, dx, dy, d2, al;
      for (j = 0; j < noktalar.length; j++) {
        p = noktalar[j];
        p.x += p.vx;
        p.y += p.vy;
        if (p.x < 0 || p.x > gen) { p.vx *= -1; }
        if (p.y < 0 || p.y > yuk) { p.vy *= -1; }
        ctx.beginPath();
        ctx.fillStyle = 'rgba(120,165,235,0.70)';
        ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
        ctx.fill();
      }

      for (j = 0; j < noktalar.length; j++) {
        a = noktalar[j];
        for (var k = j + 1; k < noktalar.length; k++) {
          b = noktalar[k];
          dx = a.x - b.x;
          dy = a.y - b.y;
          d2 = dx * dx + dy * dy;
          if (d2 < ESIK) {
            al = (1 - d2 / ESIK) * 0.35;
            ctx.beginPath();
            ctx.strokeStyle = 'rgba(90,140,220,' + al.toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.moveTo(a.x, a.y);
            ctx.lineTo(b.x, b.y);
            ctx.stroke();
          }
        }
      }
    }

    var son = 0;
    function dongu(t) {
      W.requestAnimationFrame(dongu);
      if (!calisiyor) { return; }
      if (t - son < 33) { return; }
      son = t;
      ciz(t);
    }
    W.requestAnimationFrame(dongu);
  }

  kur(0);
})();
</script>
"""


def arka_plan_efekti_ekle():
    components.html(_BTA_ARKA_JS, height=0, width=0)


arka_plan_efekti_ekle()


def _bta_excel_dosya_imza():
    """BTA Excel dosyasının (ad + değişiklik zamanı + boyut)
    imzasını döndürür; dosya yoksa None."""
    try:
        _dosyalar = sorted(
            [
                _d
                for _d in os.listdir(".")
                if _d.lower().endswith((".xlsx", ".xlsm"))
            ],
            key=lambda _ad: (
                not _ad.lower().startswith("bta"),
                _ad.lower()
            ),
        )
        if not _dosyalar:
            return None
        _p = _dosyalar[0]
        return (_p, os.path.getmtime(_p), os.path.getsize(_p))
    except Exception:
        return None


# Sayfa açıldığında mevcut dosyanın imzasını kaydeder
st.session_state["_bta_excel_imza"] = _bta_excel_dosya_imza()


@st.fragment(run_every=5)
def _bta_excel_arka_izle():
    """Arka planda sessizce Excel'i izler. Dosya değişirse/yenilenirse
    sayfayı kendisi yeniler; böylece BTA sinyali ve tablo güncellenir,
    sayfayı el ile yenilemeye gerek kalmaz."""
    st.markdown(
        '<span class="bta-arka-izle" style="display:none"></span>',
        unsafe_allow_html=True,
    )
    _simdi = _bta_excel_dosya_imza()
    if _simdi != st.session_state.get("_bta_excel_imza"):
        st.session_state["_bta_excel_imza"] = _simdi
        st.rerun()


_bta_excel_arka_izle()
