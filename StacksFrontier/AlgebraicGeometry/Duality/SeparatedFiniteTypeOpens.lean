module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian

/-!
# Affine opens of objects of `FTS S`

An affine open `U` of an object `X` of `AlgebraicGeometry.FTS S`, the category of [Stacks,
Tag 0F42], over a quasi-separated base, is again an object of `FTS S`, its inclusion is a
morphism of `FTS S`, and a morphism `f : X ⟶ Y` restricts to `U ⟶ V` whenever `U ⊆ f⁻¹(V)`.

## Main definitions

* `AlgebraicGeometry.FTS.ofAffineOpen`: the affine open `U` of `X` as an object of `FTS S`.
* `AlgebraicGeometry.FTS.ofAffineOpenι`: its inclusion into `X`.
* `AlgebraicGeometry.FTS.homOfAffineOpens`: the restriction `U ⟶ V` of `f : X ⟶ Y`.

## Main results

* `AlgebraicGeometry.FTS.ofAffineOpenι_comp`: the inclusions intertwine `f` and its restriction
  `U ⟶ V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FTS

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]

/-- The inclusion of an affine open of an object of `FTS S` is quasi-compact. -/
theorem quasiCompact_ι_of_isAffineOpen (X : FTS S) {U : X.left.Opens} (hU : IsAffineOpen U) :
    QuasiCompact U.ι :=
  have : IsAffine U.toScheme := hU
  quasiCompact_of_compactSpace _

/-- **An affine open of an object of `FTS S` is an object of `FTS S`.** -/
abbrev ofAffineOpen (X : FTS S) (U : X.left.Opens) (hU : IsAffineOpen U) : FTS S :=
  haveI := quasiCompact_ι_of_isAffineOpen X hU
  FTS.mk (U.ι ≫ X.hom)

/-- The inclusion of an affine open, as a morphism of `FTS S`. -/
abbrev ofAffineOpenι (X : FTS S) (U : X.left.Opens) (hU : IsAffineOpen U) :
    ofAffineOpen X U hU ⟶ X :=
  MorphismProperty.Over.homMk U.ι rfl

/-- The inclusion of an affine open of an object of `FTS S` is an open immersion. -/
instance (X : FTS S) (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsOpenImmersion (ofAffineOpenι X U hU).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- **The restriction of `f : X ⟶ Y` to affine opens `U ⊆ f⁻¹(V)`**, as a morphism of `FTS S`. -/
abbrev homOfAffineOpens {X Y : FTS S} (f : X ⟶ Y) {U : X.left.Opens} (hU : IsAffineOpen U)
    {V : Y.left.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    ofAffineOpen X U hU ⟶ ofAffineOpen Y V hV :=
  MorphismProperty.Over.homMk (f.left.resLE V U hUV) (by
    change f.left.resLE V U hUV ≫ V.ι ≫ Y.hom = U.ι ≫ X.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    congr 1
    exact Over.w f.toCommaMorphism)

/-- The inclusion of `U` followed by `f` equals the restriction `U ⟶ V` of `f` followed by the
inclusion of `V`. -/
theorem ofAffineOpenι_comp {X Y : FTS S} (f : X ⟶ Y) {U : X.left.Opens} (hU : IsAffineOpen U)
    {V : Y.left.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    ofAffineOpenι X U hU ≫ f = homOfAffineOpens f hU hV hUV ≫ ofAffineOpenι Y V hV := by
  ext1
  exact (Scheme.Hom.resLE_comp_ι f.left (e := hUV)).symm

end AlgebraicGeometry.FTS
