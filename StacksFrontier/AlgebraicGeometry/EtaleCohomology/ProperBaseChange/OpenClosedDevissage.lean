module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage

/-!
# The open-closed dévissage step for the restriction map on étale cohomology

Let `i : Z ⟶ Y` be a closed immersion and `j : U ⟶ Y` an open immersion onto the complement, and
consider the short exact sequence

`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`

of abelian sheaves on the small étale site of `Y`. For an arbitrary morphism of schemes `f`,
bijectivity of the restriction map on étale cohomology for `F` follows from bijectivity for the
extension by zero of `F|_U` and for the direct image of `F|_Z`. An additive functor carries an
object killed by `n` to an object killed by `n`, so if `F` is killed by `n` then so are
`j_! j^{-1} F` and `i_* i^{-1} F`.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_map_eq_zero`: an additive functor carries an object killed by
  `n` to an object killed by `n`.
* `Stacks.EtaleCohomology.isBijectiveOnExt_of_openClosed`: the open-closed dévissage step for an
  arbitrary exact functor between abelian categories, in the site-independent form
  `Stacks.EtaleCohomology.IsBijectiveOnExt`.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_openClosed`: the same step
  for the restriction map on étale cohomology along an arbitrary morphism of schemes.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_openClosed_of_nsmul_id`:
  the open-closed step with the annihilation condition carried along, so that its two hypotheses
  are restricted to sheaves killed by the same integer as `F`.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u v w v₁ v₂ u₁ u₂

section Annihilation

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **An additive functor preserves annihilation by an integer.** If `n • 𝟙 A = 0` then
`n • 𝟙 (G.obj A) = 0`. -/
lemma nsmul_id_map_eq_zero (G : C ⥤ D) [G.Additive] {A : C} {n : ℕ} (h : n • 𝟙 A = 0) :
    n • 𝟙 (G.obj A) = 0 := by
  rw [← G.map_id, ← G.map_nsmul, h, G.map_zero]

end Annihilation

section OpenClosedDevissage

attribute [local instance] HasDerivedCategory.standard

variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (j : U ⟶ Y) [IsOpenImmersion j]

/-- **The open-closed dévissage step, for an arbitrary exact functor.** Let `i : Z ⟶ Y` be a
closed immersion and `j : U ⟶ Y` an open immersion onto the complement, and let `G` be an exact
functor out of the abelian sheaves on the small étale site of `Y`. If `G` is bijective on `Ext`
from `A` into the extension by zero of `F|_U` and into the direct image of `F|_Z`, in every
degree, then it is bijective on `Ext` from `A` into `F` in every degree. -/
theorem isBijectiveOnExt_of_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (A F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hopen : ∀ q, IsBijectiveOnExt G A
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) q)
    (hclosed : ∀ q, IsBijectiveOnExt G A
      ((etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F)) q)
    (q : ℕ) :
    IsBijectiveOnExt G A F q := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F
  exact isBijectiveOnExt_of_shortExact G A hS hopen hclosed q

variable {X : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The open-closed dévissage step for the restriction map on étale cohomology.** Let
`i : Z ⟶ Y` be a closed immersion, `j : U ⟶ Y` an open immersion onto the complement, and
`f : X ⟶ Y` an arbitrary morphism of schemes. If restriction along `f` is bijective on étale
cohomology, in every degree, for the extension by zero `j_! (F|_U)` and for the direct image
`i_* (F|_Z)`, then it is bijective for `F` in every degree. -/
theorem etaleCohomologyRestrictionMap_bijective_of_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hopen : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) q))
    (hclosed : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f
      ((etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F)) q))
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F
  exact etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} f hS hopen hclosed q

/-- **The open-closed dévissage step inside a class of annihilated sheaves.** The same reduction
as `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_openClosed`, with the two
hypotheses required only for sheaves killed by the integer `n` that kills `F`. -/
theorem etaleCohomologyRestrictionMap_bijective_of_openClosed_of_nsmul_id
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {n : ℕ}
    (hF : n • 𝟙 F = 0)
    (hopen : ∀ (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      n • 𝟙 G = 0 → ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f
        ((extensionByZero.{u, v} j).obj G) q))
    (hclosed : ∀ (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      n • 𝟙 H = 0 → ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f
        ((etaleAbelianDirectImage.{u, v} i).obj H) q))
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) :=
  etaleCohomologyRestrictionMap_bijective_of_openClosed.{u, v, w} i j f hij F
    (hopen _ (nsmul_id_map_eq_zero (etaleRestriction.{u, v} j) hF))
    (hclosed _ (nsmul_id_map_eq_zero (etaleAbelianInverseImage.{u, v} i) hF)) q

end OpenClosedDevissage

end Stacks.EtaleCohomology

end
