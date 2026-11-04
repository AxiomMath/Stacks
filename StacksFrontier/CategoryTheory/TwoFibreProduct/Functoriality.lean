module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the 2-fibre product of categories

Suppose given two cospans of categories together with functors between them,
```
𝒳 --H--> 𝒵 <--I-- 𝒴
|        |         |
L        M         K
v        v         v
𝒜 --F--> 𝒞 <--G-- ℬ
```
which 2-commute: the left-hand square is filled by `β : H ⋙ M ≅ L ⋙ F` and the right-hand one by
`α : K ⋙ G ≅ I ⋙ M`. Then there is an induced functor on 2-fibre products `𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ`,
sending an object `(x, y, φ : H x ≅ I y)` to `(L x, K y, α_y⁻¹ ∘ M(φ) ∘ β_x⁻¹)` and a morphism
`(f, g)` to `(L f, K g)`. Both 2-fibre products are `CategoryTheory.Limits.CategoricalPullback`.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.map`: the functor `𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` induced by
  a 2-commutative diagram between two cospans.

## References

* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {𝒳 𝒴 𝒵 𝒜 ℬ 𝒞 : Type*}
  [Category 𝒳] [Category 𝒴] [Category 𝒵] [Category 𝒜] [Category ℬ] [Category 𝒞]

/-- The functor `𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` induced by a 2-commutative diagram between the two cospans: on
objects it sends `(x, y, φ)` to `(L x, K y, α_y⁻¹ ∘ M(φ) ∘ β_x⁻¹)`, and on morphisms it applies `L`
and `K` componentwise. -/
@[stacks 02XA]
def CategoricalPullback.map (H : 𝒳 ⥤ 𝒵) (I : 𝒴 ⥤ 𝒵)
    (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞) (G : ℬ ⥤ 𝒞)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CategoricalPullback H I ⥤ CategoricalPullback F G :=
  (CatCommSqOver.toFunctorToCategoricalPullback F G (CategoricalPullback H I)).obj
    { fst := CategoricalPullback.π₁ H I ⋙ L
      snd := CategoricalPullback.π₂ H I ⋙ K
      iso :=
        Functor.isoWhiskerLeft (CategoricalPullback.π₁ H I) β.symm ≪≫
          Functor.isoWhiskerRight
            (CatCommSq.iso (CategoricalPullback.π₁ H I) (CategoricalPullback.π₂ H I) H I) M ≪≫
          (Functor.isoWhiskerLeft (CategoricalPullback.π₂ H I) α).symm }

namespace CategoricalPullback

variable (H : 𝒳 ⥤ 𝒵) (I : 𝒴 ⥤ 𝒵)
  (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞) (G : ℬ ⥤ 𝒞)
  (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/-- The `𝒜`-component of `CategoricalPullback.map … |>.obj P` is `L.obj P.fst`. -/
@[simp]
lemma map_obj_fst (P : CategoricalPullback H I) :
    ((map H I L K M F G α β).obj P).fst = L.obj P.fst := rfl

/-- The `ℬ`-component of `CategoricalPullback.map … |>.obj P` is `K.obj P.snd`. -/
@[simp]
lemma map_obj_snd (P : CategoricalPullback H I) :
    ((map H I L K M F G α β).obj P).snd = K.obj P.snd := rfl

/-- The filling isomorphism of `CategoricalPullback.map … |>.obj P` is `M.map P.iso.hom`
conjugated by the two 2-cells of the functoriality square: `β.inv` at `P.fst` on the left and
`α.inv` at `P.snd` on the right. -/
@[simp]
lemma map_obj_iso_hom (P : CategoricalPullback H I) :
    ((map H I L K M F G α β).obj P).iso.hom =
      β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd := rfl

/-- On morphisms, `CategoricalPullback.map` applies `L` to the `𝒳`-component. -/
@[simp]
lemma map_map_fst {P Q : CategoricalPullback H I} (f : P ⟶ Q) :
    ((map H I L K M F G α β).map f).fst = L.map f.fst := rfl

/-- On morphisms, `CategoricalPullback.map` applies `K` to the `𝒴`-component. -/
@[simp]
lemma map_map_snd {P Q : CategoricalPullback H I} (f : P ⟶ Q) :
    ((map H I L K M F G α β).map f).snd = K.map f.snd := rfl

end CategoricalPullback

end CategoryTheory.Limits
