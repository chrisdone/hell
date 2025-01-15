// parse the json in the index
const indexEl = document.getElementById("searchIndex");
const index = JSON.parse(indexEl.textContent);

function hideItem(item) {
  item.style.display = "none";
  item.classList.add("hidden");
}

function showItem(item) {
  item.style.display = "block";
  item.classList.remove("hidden");
}

function hideSearchable() {
  const allItems = document.querySelectorAll(".searchable");
  // hide all items
  allItems.forEach((item) => {
    hideItem(item);
  });
}

function showSearchable() {
  const allItems = document.querySelectorAll(".searchable");
  // show all items
  allItems.forEach((item) => {
    showItem(item);
  });
}

function showUsedHeadings() {
  // fancy query which selects any headings which have
  // non hidden children
  const els = document.querySelectorAll(
    ".searchableHeading:has(+ul li:not(.hidden))",
  );
  els.forEach((el) => {
    el.style.display = "block";
  });
}

function hideAllHeadings() {
  const els = document.querySelectorAll(".searchableHeading");
  els.forEach((el) => {
    el.style.display = "none";
  });
}

function showAllHeadings() {
  const els = document.querySelectorAll(".searchableHeading");
  els.forEach((el) => {
    el.style.display = "block";
  });
}

function search(query) {
  if (query === "" || query === null) {
    showAllHeadings();
    showSearchable();
    return;
  }

  //
  const results = index.filter((item) => {
    return item.text.toLowerCase().includes(query.toLowerCase());
  });
  const resultIds = results.map((item) => item.elementId);

  // hide everything (we will show relevant things next)
  hideSearchable();
  hideAllHeadings();
  // show the items that match the search
  resultIds.forEach((id) => {
    const item = document.getElementById(id);
    showItem(item);
  });
  showUsedHeadings();
}

// when the search changes, hide non-matching elements
const searchInput = document.getElementById("search");
searchInput.addEventListener("input", function (event) {
  const value = event.target.value;
  search(value);
});
