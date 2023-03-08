class TreapNode {
  const key: int
  const priority: int
  var left: TreapNode?
  var right: TreapNode?

  constructor TreapNode(key:int, priority:int) {
    this.key := key;
    this.priority:= priority;
    this.left := null;
    this.right:= null;
  }
}
