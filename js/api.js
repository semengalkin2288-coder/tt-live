const API = (() => {
  async function getLive(sport = 'tt') {
    const res = await fetch(`/api/live?sport=${sport}`, { cache: 'no-store' });
    if (!res.ok) {
      const err = await res.json().catch(() => ({}));
      throw new Error(err.error || `Ошибка сервера ${res.status}`);
    }
    const data = await res.json();
    if (data.error) throw new Error(data.error);
    return data;
  }
  return { getLive };
})();