
名前空間は、`UecInLean.CategoryTheory.Category` 内で記述する。

圏の対象はそのまま書く。
圏の射は、`.Hom` とする。
e.g. 対象は `Comma : Type*`, 射は `Comma.Hom : Comma -> Comma -> Type*`

インスタンス化したときに、`...Category.instComma` みたいになっているのが理想。
