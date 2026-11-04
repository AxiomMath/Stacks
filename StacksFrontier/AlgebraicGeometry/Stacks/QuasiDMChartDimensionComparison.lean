module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SmoothDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite

/-!
# Comparing a smooth chart with a flat locally quasi-finite chart at a point

Let `P` be a locally Noetherian algebraic space carrying two morphisms,

* `πT : P ⟶ T`, flat, locally of finite type and locally quasi-finite, and
* `πW : P ⟶ W`, smooth of relative dimension `d` at a point `p` of `P`.

Then `d ≤ dim_{πT(p)}(T)`. Over the spectrum of a field, a locally quasi-finite morphism of
algebraic spaces does not raise the dimension at a point, with no flatness hypothesis.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `le_dimensionAtPoint_of_isLocallyQuasiFinite_isSmooth`: the comparison, with the relative
  dimension read in `WithBot ℕ∞`.
* `le_dimensionAtPoint_natCast_of_isLocallyQuasiFinite_isSmooth`: the same inequality between
  natural numbers, given the dimension of `T` at the image point as a natural number.
* `dimensionAtPoint_le_dimensionAtPoint_of_isLocallyQuasiFinite_fieldTarget`: a locally
  quasi-finite morphism of algebraic spaces over the spectrum of a field does not raise the
  dimension at a point.

## References

* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0AFH](https://stacks.math.columbia.edu/tag/0AFH)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A locally quasi-finite morphism locally of finite type has relative dimension zero. -/
private theorem hasRelativeDimension_zero_of_isLocallyQuasiFinite
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hlft : IsLocallyOfFiniteType B S hS f) (hqf : IsLocallyQuasiFinite B S hS f) :
    HasRelativeDimension 0 B S hS f := fun x => by
  simpa using (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS f hlft).mp
    hqf x

/-- **The relative dimension of a smooth chart is bounded by the dimension of the base of a flat
locally quasi-finite chart through the same point.** Let `T`, `W` and `P` be locally Noetherian
algebraic spaces over `S`, let `πT : P ⟶ T` be flat, locally of finite type and locally
quasi-finite, and let `πW : P ⟶ W` be smooth of relative dimension `d` at a point `p` of `P`.
Then `d ≤ dim_{πT(p)}(T)`. -/
theorem le_dimensionAtPoint_of_isLocallyQuasiFinite_isSmooth
    {T W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hW : IsAlgebraicSpace B S hS W)
    (hP : IsAlgebraicSpace B S hS P)
    (hNT : HasEtaleLocalProperty B S hS T (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNW : HasEtaleLocalProperty B S hS W (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNP : HasEtaleLocalProperty B S hS P (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (πT : P ⟶ T) (πW : P ⟶ W)
    (hflat : IsFlat B S hS πT) (hlft : IsLocallyOfFiniteType B S hS πT)
    (hqf : IsLocallyQuasiFinite B S hS πT) (hsm : IsSmooth B S hS πW)
    {d : ℕ} (p : points B S hS P)
    (hd : HasRelativeDimensionAt (d : ℕ∞) B S hS πW p) :
    (d : WithBot ℕ∞) ≤ dimensionAtPoint B S hS T hT (pointsMap B S hS P πT p) := by
  have hzero := hasRelativeDimension_zero_of_isLocallyQuasiFinite B S hS πT hlft hqf
  have hflatFormula := dimensionAtPoint_eq_add_of_hasRelativeDimension B S hS hP hT hNP hNT πT
    hflat hlft hzero p
  have hsmoothFormula := dimensionAtPoint_eq_add_of_isSmooth B S hS hP hW hNP hNW πW hsm p hd
  rw [hsmoothFormula, show ((0 : ℕ) : WithBot ℕ∞) = 0 from rfl, add_zero] at hflatFormula
  rw [← hflatFormula]
  exact le_add_of_nonneg_left (zero_le_dimensionAtPoint B S hS hW _)

/-- **The comparison of
`AlgebraicGeometry.Space.le_dimensionAtPoint_of_isLocallyQuasiFinite_isSmooth` between natural
numbers.** With the dimension of `T` at the image of `p` given as a natural number `m`, the
relative dimension `d` of the smooth chart at `p` satisfies `d ≤ m`. -/
theorem le_dimensionAtPoint_natCast_of_isLocallyQuasiFinite_isSmooth
    {T W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hW : IsAlgebraicSpace B S hS W)
    (hP : IsAlgebraicSpace B S hS P)
    (hNT : HasEtaleLocalProperty B S hS T (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNW : HasEtaleLocalProperty B S hS W (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNP : HasEtaleLocalProperty B S hS P (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (πT : P ⟶ T) (πW : P ⟶ W)
    (hflat : IsFlat B S hS πT) (hlft : IsLocallyOfFiniteType B S hS πT)
    (hqf : IsLocallyQuasiFinite B S hS πT) (hsm : IsSmooth B S hS πW)
    {d : ℕ} (p : points B S hS P)
    (hd : HasRelativeDimensionAt (d : ℕ∞) B S hS πW p)
    (t : points B S hS T) (ht : pointsMap B S hS P πT p = t)
    (m : ℕ) (hm : dimensionAtPoint B S hS T hT t = (m : WithBot ℕ∞)) :
    d ≤ m := by
  have hle := le_dimensionAtPoint_of_isLocallyQuasiFinite_isSmooth B S hS hT hW hP hNT hNW hNP
    πT πW hflat hlft hqf hsm p hd
  rw [ht, hm] at hle
  exact_mod_cast hle

/-- **A locally quasi-finite morphism of algebraic spaces over the spectrum of a field does not
raise the dimension at a point.** Let `Q` and `Y` be algebraic spaces over `S`, let
`g : Y ⟶ Spec k` be locally of finite type with `Spec k` the spectrum of a field of the site, and
let `c : Q ⟶ Y` be locally of finite type and locally quasi-finite. Then
`dim_x(Q) ≤ dim_{c(x)}(Y)` at every point `x` of `Q`. -/
theorem dimensionAtPoint_le_dimensionAtPoint_of_isLocallyQuasiFinite_fieldTarget
    {Q Y G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : IsAlgebraicSpace B S hS Q) (hY : IsAlgebraicSpace B S hS Y)
    (k : FieldValuedPoint B S hS G) (c : Q ⟶ Y)
    (g : Y ⟶ yoneda.obj (k.siteObject B S hS G))
    (hclft : IsLocallyOfFiniteType B S hS c) (hqf : IsLocallyQuasiFinite B S hS c)
    (hg : IsLocallyOfFiniteType B S hS g) (x : points B S hS Q) :
    dimensionAtPoint B S hS Q hQ x ≤
      dimensionAtPoint B S hS Y hY (pointsMap B S hS Q c x) := by
  have hk : IsAlgebraicSpace B S hS (yoneda.obj (k.siteObject B S hS G)) :=
    isAlgebraicSpace_yoneda B S hS _
  obtain ⟨n, hn⟩ := exists_hasRelativeDimensionAt B S hS hQ hk (c ≫ g) x
  obtain ⟨e, he⟩ := exists_hasRelativeDimensionAt B S hS hY hk g (pointsMap B S hS Q c x)
  have hzero : HasRelativeDimensionAt 0 B S hS c x :=
    hasRelativeDimension_zero_of_isLocallyQuasiFinite B S hS c hclft hqf x
  have hle :=
    hasRelativeDimensionAt_comp_le_add B S hS hQ hY hk c g x hclft hg 0 e n hzero he hn
  rw [zero_add] at hle
  rw [(relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hQ k (c ≫ g) x n).mp hn,
    (relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hY k g
      (pointsMap B S hS Q c x) e).mp he]
  exact_mod_cast hle

end AlgebraicGeometry.Space

end
