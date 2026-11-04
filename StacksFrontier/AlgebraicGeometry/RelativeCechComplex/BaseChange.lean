module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray

/-!
# The inverse-image cover of a base change, and `Rf'_*ℱ'` ([Stacks, Tag 01XM])

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be the cartesian square of [Stacks, Tag 02KF], let `ℱ` be a quasi-coherent `𝒪_X`-module and let
`ℱ' = (g')^*ℱ`.  For a finite affine open covering `𝒰 : X = ⋃ Uᵢ`, [Stacks, Tag 01XM] forms the
covering `𝒰' : X' = ⋃ U'ᵢ` with `U'ᵢ = (g')^{-1}(Uᵢ)`, observes that `U'ᵢ` is again affine when
`g` is affine, and asserts that the relative Čech complex of `𝒰'` computes `Rf'_*ℱ'`.

This file supplies the inverse-image covering for an affine `g`, and the isomorphism
`Č ⁼(𝒰', f', ℱ') ≅ Rf'_*ℱ'` of [Stacks, Tag 01XL] for it.  An affine `g` makes `g'` affine, hence
makes each `U'ᵢ = Uᵢ ×_X X'` affine and makes `X'` and `S'` of affine diagonal, which is exactly
the hypothesis list under which [Stacks, Tag 01XL] applies to the base-changed data `(f', 𝒰')`.
The two assertions of [Stacks, Tag 01XM] themselves are
`Stacks.AlgebraicGeometry.RelativeCechBaseChange.baseChangeRelativeCechIsoDerivedPushforward` and
`Stacks.AlgebraicGeometry.RelativeCechBaseChange.baseChangeRelativeCechComplexIsoOfIsAffineHom`.

## Main definitions

* `inverseImageAffineOpenCover`: the covering `𝒰' : X' = ⋃ U'ᵢ` of [Stacks, Tag 01XM], as a
  finite affine open covering of `X'` indexed by the same set as `𝒰`.

## Main results

* `opensRange_inverseImageAffineOpenCover_f`: the `i`-th member of `𝒰'` is the open subscheme
  `(g')^{-1}(Uᵢ)`.
* `isAffineHom_diagonal_of_isAffineHom`: the source of an affine morphism whose target has
  affine diagonal has affine diagonal.
* `inverseImageRelativeCechIsoDerivedPushforward`: **`Č ⁼(𝒰', f', ℱ') ≅ Rf'_*ℱ'`** in `D⁺(S')`,
  naturally in the quasi-coherent `𝒪_{X'}`-module.

## Implementation notes

`Scheme.AffineOpenCover` records its members as `Spec` of a ring, while the fibre product
`Uᵢ ×_X X'` is an abstract pullback, so the members of `𝒰'` are spelled as the composite of
`Scheme.isoSpec` with `pullback.snd`.  This changes neither the range nor the open-immersion
property, and `opensRange_inverseImageAffineOpenCover_f` records that the range is the one
[Stacks, Tag 01XM] prescribes.

Affineness of the diagonal of the source of an affine morphism is the factorisation
`f ≫ terminal.from Y = terminal.from X` together with `pullback.diagonal_comp`:  the first
factor of the resulting composite is a base change of the diagonal of `f`, which is an
isomorphism because an affine morphism is separated.

The binder list is [Stacks, Tag 01XL]'s — the morphism, the finite affine open covering, and
affine diagonal for the two schemes — together with the cartesian square of [Stacks, Tag 02KF]
and the affineness of `g`, which is the hypothesis [Stacks, Tag 01XM] itself adds for its second
assertion.  Nothing else is assumed:  no affineness of `f` or `f'`, no Noetherian hypothesis, no
separatedness beyond affine diagonal.  Affineness of `g` is what this file needs and all it
needs, because `U'ᵢ` is affine, and `X'` and `S'` are of affine diagonal, exactly through it.

## References

* [Stacks Project, Tag 01XM](https://stacks.math.columbia.edu/tag/01XM)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechComplex

attribute [local instance] HasDerivedCategory.standard

variable {X X' : Scheme.{u}}

/-! ### The inverse-image covering -/

/-- **The inverse-image covering of [Stacks, Tag 01XM].**  For a finite affine open covering
`𝒰 : X = ⋃ Uᵢ` and an affine morphism `g' : X' ⟶ X`, the opens `U'ᵢ = (g')^{-1}(Uᵢ)` form an
affine open covering of `X'` indexed by the same set:  `U'ᵢ = Uᵢ ×_X X'` is affine because it is
a base change of the affine `g'` along a morphism with affine source. -/
public noncomputable def inverseImageAffineOpenCover (g' : X' ⟶ X) [IsAffineHom g']
    (T : X.AffineOpenCover.{u, u}) : X'.AffineOpenCover.{u, u} where
  I₀ := T.I₀
  X i := Γ(pullback (T.f i) g', ⊤)
  f i := (pullback (T.f i) g').isoSpec.inv ≫ pullback.snd (T.f i) g'
  idx x := T.idx (g'.base x)
  covers x := by
    have hsurj : Function.Surjective
        ((pullback (T.f (T.idx (g'.base x))) g').isoSpec.inv.base) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
        (pullback (T.f (T.idx (g'.base x))) g').isoSpec.symm)).surjective
    have h := AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd
      (T.f (T.idx (g'.base x))) g'
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ, h]
    exact T.covers (g'.base x)
  map_prop i := by infer_instance

/-- The inverse-image covering is indexed by the same set as the original covering. -/
public theorem inverseImageAffineOpenCover_I₀ (g' : X' ⟶ X) [IsAffineHom g']
    (T : X.AffineOpenCover.{u, u}) :
    (inverseImageAffineOpenCover g' T).I₀ = T.I₀ := rfl

/-- The members of the inverse-image covering are open immersions. -/
public instance isOpenImmersion_inverseImageAffineOpenCover_f (g' : X' ⟶ X) [IsAffineHom g']
    (T : X.AffineOpenCover.{u, u}) (i : T.I₀) :
    IsOpenImmersion ((inverseImageAffineOpenCover g' T).f i) :=
  (inverseImageAffineOpenCover g' T).map_prop i

/-- The inverse-image covering of a finite covering is finite. -/
public noncomputable instance fintype_inverseImageAffineOpenCover_I₀ (g' : X' ⟶ X)
    [IsAffineHom g'] (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    Fintype (inverseImageAffineOpenCover g' T).I₀ :=
  inferInstanceAs (Fintype T.I₀)

/-- **The members of the inverse-image covering are the inverse images of the members of the
original covering**:  `U'ᵢ = (g')^{-1}(Uᵢ)` as opens of `X'`. -/
public theorem opensRange_inverseImageAffineOpenCover_f (g' : X' ⟶ X) [IsAffineHom g']
    (T : X.AffineOpenCover.{u, u}) (i : T.I₀) :
    ((inverseImageAffineOpenCover g' T).f i).opensRange = g' ⁻¹ᵁ (T.f i).opensRange := by
  have hsurj : Function.Surjective ((pullback (T.f i) g').isoSpec.inv.base) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
      (pullback (T.f i) g').isoSpec.symm)).surjective
  refine TopologicalSpace.Opens.ext ?_
  have h := AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd (T.f i) g'
  show Set.range ((pullback (T.f i) g').isoSpec.inv ≫ pullback.snd (T.f i) g').base = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact h

/-! ### Transfer of the affine-diagonal hypothesis -/

/-- **The source of an affine morphism whose target has affine diagonal has affine diagonal.**
An affine morphism is separated, so its diagonal is a closed immersion; the diagonal of the
source over the terminal object factors as a base change of that diagonal followed by a base
change of the diagonal of the target. -/
public theorem isAffineHom_diagonal_of_isAffineHom {Y Z : Scheme.{u}} (p : Y ⟶ Z)
    [IsAffineHom p] [IsAffineHom (pullback.diagonal (terminal.from Z))] :
    IsAffineHom (pullback.diagonal (terminal.from Y)) := by
  have := IsSeparated.of_isAffineHom p
  have affPb : ∀ {A B C : Scheme.{u}} (a : A ⟶ C) (b : B ⟶ C) [IsAffineHom a],
      IsAffineHom (pullback.snd a b) := fun a b ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback a b) inferInstance
  rw [← terminal.comp_from p, pullback.diagonal_comp]
  infer_instance

/-! ### The relative Čech complex of the inverse-image covering computes `Rf'_*ℱ'` -/

variable {S S' : Scheme.{u}}

/-- **The relative Čech complex of the inverse-image covering computes `Rf'_*ℱ'`.**  In
`D⁺(S')`,

`Č ⁼(𝒰', f', ℱ') ≅ Rf'_*ℱ'`,

naturally in the quasi-coherent `𝒪_{X'}`-module, where `𝒰'` is the covering of `X'` by the
inverse images `U'ᵢ = (g')^{-1}(Uᵢ)`.  This is [Stacks, Tag 01XL] applied to the base-changed
data:  an affine `g` makes `g'` affine, so `𝒰'` is a finite affine open covering of `X'` and both
`X'` and `S'` are of affine diagonal, which is [Stacks, Tag 01XL]'s hypothesis list for
`(f', 𝒰')`. -/
public noncomputable def inverseImageRelativeCechIsoDerivedPushforward {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hw : IsPullback g' f' f g)
    (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] [IsAffineHom g]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))] :
    letI : IsAffineHom g' := MorphismProperty.of_isPullback hw.flip inferInstance
    relativeCechComplex f' (inverseImageAffineOpenCover g' T) ⋙
        HomotopyCategory.Plus.quotient S'.Modules ⋙ DerivedCategory.Plus.Qh ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X'.ringCatSheaf) ⋙
        DerivedCategory.Plus.singleFunctor X'.Modules 0 ⋙
          (Scheme.Modules.pushforward f').rightDerivedFunctorPlus := by
  letI : IsAffineHom g' := MorphismProperty.of_isPullback hw.flip inferInstance
  letI := isAffineHom_diagonal_of_isAffineHom g'
  letI := isAffineHom_diagonal_of_isAffineHom g
  exact Tag01XLDerivedIso.relativeCechIsoDerivedPushforward f'
    (inverseImageAffineOpenCover g' T)

end Stacks.AlgebraicGeometry.RelativeCechComplex

end
