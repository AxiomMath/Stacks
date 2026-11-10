module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSheafifyModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionsChartPullback

/-!
# Meromorphic sections of a quasi-coherent module over an affine chart

Let `X` be an algebraic space over a scheme `S` satisfying the two hypotheses of Stacks 0EN6 —
every weakly associated point has codimension `0`, and every quasi-compact open of every étale
scheme chart has finitely many irreducible components — and let `L` be a quasi-coherent
`𝒪_X`-module.  Over an affine object `U` of the small étale site the sections of the sheaf
`𝒦_X(L)` of meromorphic sections of Stacks 0EN5 are exactly `𝒦_X(U) ⊗_{𝒪_X(U)} L(U)`: the
module analogue of Stacks 0EN6, part (2).

The proof is the cartesianness argument of
`AlgebraicGeometry.Space.isIso_restrictionBaseChange_meromorphic` carried out for the presheaf
of modules `𝒦_X ⊗_{𝒪_X} L` in place of the presheaf of rings `𝒦_X`.  Over a morphism of affine
charts the presheaf of meromorphic functions is cartesian, by Stacks 0EN6 part (2), and `L` is
cartesian, by Stacks 03DX (2); an extension of scalars along a cartesian presheaf of algebras of
a cartesian presheaf of modules is cartesian, which is the algebra of this file.  A cartesian
presheaf of modules over the chart rings is a sheaf for the affine étale topology, and
sheafification therefore does not change its sections over an affine chart.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicSectionStructureModule` is `𝒦_X ⊗_{𝒪_X} L` read as a
  presheaf of `𝒪_X`-modules.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_changeOfRings`: **an extension of scalars
  of a cartesian presheaf of modules along a cartesian presheaf of algebras is cartesian.**
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_structurePresheaf_of_isQuasicoherentOnSite`:
  Stacks 03DX (2) for the chart rings, in the shape of the base-change comparison.
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_meromorphicSectionStructureModule` and
  `AlgebraicGeometry.Space.isSheaf_affineEtale_meromorphicSectionModuleUp`: the presheaf of
  meromorphic sections is cartesian on the affine charts, hence a sheaf there.
* `AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite`:
  **the module analogue of Stacks 0EN6, part (2).**

## Implementation notes

The algebra is the chain of isomorphisms

`B ⊗_A (K ⊗_A M) ≅ (B ⊗_A K) ⊗_A M ≅ K' ⊗_A M ≅ K' ⊗_B (B ⊗_A M) ≅ K' ⊗_B N`,

whose middle two steps are the two cartesianness hypotheses and whose outer two are
`TensorProduct.assoc` and `TensorProduct.AlgebraTensorModule.cancelBaseChange`.  The first two
are linear over `A = 𝒪_X(U)` and the last two over `B = 𝒪_X(V)`, so the composite is assembled
on the underlying bijections rather than as a linear equivalence; the comparison of the two
spellings of the ring `𝒦_X(V)` as an `A`-module — through `B` and through the composite ring map
— is the scalar tower `IsScalarTower.of_algebraMap_eq`, and the comparison with the
`ModuleCat.extendScalars` module structure is definitional, as it already is in
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_algModule`.

The restriction of the presheaf of modules to the affine charts is
`PresheafOfModules.pushforward₀`, whose underlying presheaf of abelian groups is the
precomposition with the inclusion on the nose, so the base-change comparison over a morphism of
affine charts is the one over its image in the small étale site with no transport.

A chart carrying a free generator of `L` computes the same sections with no affineness and no
hypothesis on `X`, by
`AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_tmul`; the two statements are
incomparable, that one asking for a trivialization over every chart below and this one for
affineness and quasi-coherence.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v r

namespace Stacks.PresheafOfModules

open _root_.Stacks.PresheafOfModules.ChangeOfRings

/-- Two additive maps out of a tensor product that agree on pure tensors agree everywhere. -/
private theorem tensor_funext {R M N P F G : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [FunLike F (M ⊗[R] N) P]
    [FunLike G (M ⊗[R] N) P] [AddMonoidHomClass F (M ⊗[R] N) P] [AddMonoidHomClass G (M ⊗[R] N) P]
    (f : F) (g : G) (h : ∀ m n, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) (z : M ⊗[R] N) : f z = g z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m n => exact h m n

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **An extension of scalars of a cartesian presheaf of modules along a cartesian presheaf of
algebras is cartesian.**  If the presheaf of `O₁`-algebras `O₂` is cartesian over `f` when read
as a presheaf of `O₁`-modules, and `G` is cartesian over `f`, then so is `O₂ ⊗_{O₁} G`. -/
theorem isIso_restrictionBaseChange_changeOfRings (θ : O₁ ⟶ O₂) (G : PMod O₁)
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (halg : IsIso (restrictionBaseChange (algModule O₁ O₂ θ) f))
    (hG : IsIso (restrictionBaseChange G f)) :
    IsIso (restrictionBaseChange
      ((ChangeOfRings.restrictScalars θ).obj ((changeOfRings θ).obj G)) f) := by
  let algB : Algebra (O₁.obj X) (O₁.obj Y) := (O₁.map f).hom.toAlgebra
  let algK : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let algK' : Algebra (O₁.obj Y) (O₂.obj Y) := (θ.app Y).hom.toAlgebra
  let algAK' : Algebra (O₁.obj X) (O₂.obj Y) :=
    ((θ.app Y).hom.comp (O₁.map f).hom).toAlgebra
  let towAK' : IsScalarTower (O₁.obj X) (O₁.obj Y) (O₂.obj Y) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the two given comparisons, as maps
  let γ : (O₁.obj Y) ⊗[O₁.obj X] (O₂.obj X) →ₗ[O₁.obj Y] (O₂.obj Y) :=
    (restrictionBaseChange (algModule O₁ O₂ θ) f).hom
  let β : (O₁.obj Y) ⊗[O₁.obj X] (G.obj X) →ₗ[O₁.obj Y] (G.obj Y) :=
    (restrictionBaseChange G f).hom
  have hγ : Function.Bijective γ :=
    ConcreteCategory.bijective_of_isIso (restrictionBaseChange (algModule O₁ O₂ θ) f)
  have hβ : Function.Bijective β :=
    ConcreteCategory.bijective_of_isIso (restrictionBaseChange G f)
  -- the comparison of the algebras, read as a map of `O₁ X`-modules
  let γA := γ.restrictScalars (O₁.obj X)
  let E₁ := (TensorProduct.assoc (O₁.obj X) (O₁.obj Y) (O₂.obj X) (G.obj X)).symm
  let E₂ := TensorProduct.congr (LinearEquiv.ofBijective γA hγ)
    (LinearEquiv.refl (O₁.obj X) (G.obj X))
  let E₃ := (TensorProduct.AlgebraTensorModule.cancelBaseChange (O₁.obj X) (O₁.obj Y)
    (O₁.obj Y) (O₂.obj Y) (G.obj X)).symm
  let E₄ := TensorProduct.congr (LinearEquiv.refl (O₁.obj Y) (O₂.obj Y))
    (LinearEquiv.ofBijective β hβ)
  let Θ := (restrictionBaseChange
    ((ChangeOfRings.restrictScalars θ).obj ((changeOfRings θ).obj G)) f).hom
  let E := E₁.toAddEquiv.trans (E₂.toAddEquiv.trans (E₃.toAddEquiv.trans E₄.toAddEquiv))
  have keyT : ∀ (b : O₁.obj Y) (a : O₂.obj X) (x : G.obj X),
      Θ (b ⊗ₜ[O₁.obj X] (a ⊗ₜ[O₁.obj X] x)) =
        E (b ⊗ₜ[O₁.obj X] (a ⊗ₜ[O₁.obj X] x)) := by
    intro b a x
    have h1 := restrictionBaseChange_tmul
      ((ChangeOfRings.restrictScalars θ).obj ((changeOfRings θ).obj G)) f b
      (a ⊗ₜ[O₁.obj X] x)
    have h2 : (((ChangeOfRings.restrictScalars θ).obj ((changeOfRings θ).obj G)).map f)
          (a ⊗ₜ[O₁.obj X] x) =
        ((O₂.map f).hom a) ⊗ₜ[O₁.obj Y] ((G.map f).hom x) := cofMap_tmul θ G f a x
    rw [h2] at h1
    refine h1.trans ?_
    have h5 : E (b ⊗ₜ[O₁.obj X] (a ⊗ₜ[O₁.obj X] x)) =
        (γ (b ⊗ₜ[O₁.obj X] a)) ⊗ₜ[O₁.obj Y]
          (β ((1 : O₁.obj Y) ⊗ₜ[O₁.obj X] x)) := rfl
    refine Eq.trans ?_ h5.symm
    have h3 : γ (b ⊗ₜ[O₁.obj X] a) = b • ((O₂.map f).hom a) :=
      restrictionBaseChange_tmul (algModule O₁ O₂ θ) f b a
    have h4 : β ((1 : O₁.obj Y) ⊗ₜ[O₁.obj X] x) = (G.map f).hom x :=
      restrictionBaseChange_one_tmul G f x
    rw [h3, h4]
    rfl
  have key : ∀ z, Θ z = E z := tensor_funext Θ E fun b =>
    tensor_funext (Θ.toAddMonoidHom.comp (TensorProduct.mk _ _ _ b).toAddMonoidHom)
      (E.toAddMonoidHom.comp (TensorProduct.mk _ _ _ b).toAddMonoidHom) (keyT b)
  have hbij : Function.Bijective Θ := by
    rw [show (Θ : _ → _) = E from funext key]
    exact E.bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Descent, Proposition 03DX (2) read on the chart rings of the small étale site**: a
quasi-coherent `𝒪_X`-module is cartesian over a morphism of affine étale charts, in the shape of
the base-change comparison of `Stacks.PresheafOfModules.restrictionBaseChange`. -/
theorem isIso_restrictionBaseChange_structurePresheaf_of_isQuasicoherentOnSite
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (hV : IsAffine (smallEtaleScheme B S hS X.1 V)) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS X.1) G.val f.op) := by
  have hb := bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG hU hV f
  let _ := chartAlgebra (hF := X.2) f
  let _ := chartSectionsModule G f
  have key : ∀ z, sectionsBaseChange G f z =
      restrictionBaseChange.{u + 1, u, u, u}
        (R := structurePresheaf B S hS X.1) G.val f.op z :=
    tensor_funext _ _ fun b x =>
      (chartBaseChange_tmul G f b x).trans (restrictionBaseChange_tmul G.val f.op b x).symm
  rw [show (sectionsBaseChange G f : _ → _) = _ from funext key] at hb
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- The presheaf `𝒦_X ⊗_{𝒪_X} L` of meromorphic sections of a sheaf of `𝒪_X`-modules, read as a
presheaf of `𝒪_X`-modules by restriction of scalars along `𝒪_X ⟶ 𝒦_X`. -/
noncomputable abbrev meromorphicSectionStructureModule (L : Modules.{u, u} B S hS X.1 X.2) :
    PresheafOfModules.{u}
      (structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (ChangeOfRings.restrictScalars (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj
    (meromorphicSectionModule B S hS X.1 X.2 L)

/-- **The presheaf of meromorphic sections of a quasi-coherent module is cartesian over a
morphism of affine étale charts.**  Over an affine chart the meromorphic functions are the total
ring of fractions (Stacks 0EN6, part (2)) and the module is cartesian by Stacks 03DX (2), so the
extension of scalars of the module along `𝒪_X ⟶ 𝒦_X` is cartesian too. -/
theorem isIso_restrictionBaseChange_meromorphicSectionStructureModule
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : L.IsQuasicoherentOnSite)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (hV : IsAffine (smallEtaleScheme B S hS X.1 V)) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS X.1)
      (meromorphicSectionStructureModule B S hS X L) f.op) :=
  isIso_restrictionBaseChange_changeOfRings _ L.val f.op
    (isIso_restrictionBaseChange_meromorphic B S hS X hwa hfin f hU hV)
    (isIso_restrictionBaseChange_structurePresheaf_of_isQuasicoherentOnSite B S hS X L hL f hU hV)

/-- **The presheaf of meromorphic sections of a quasi-coherent module is a sheaf on the affine
étale charts.** -/
theorem isSheaf_affineEtale_meromorphicSectionModuleUp
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : L.IsQuasicoherentOnSite)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS X.1)
      ((AffineEtale.inclusion B S hS X.1).op ⋙
        meromorphicSectionModuleUp B S hS X.1 X.2 L) := by
  set PAff : PresheafOfModules.{u}
      (affineEtaleChartRings B S hS X.1 ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    (PresheafOfModules.pushforward₀ (AffineEtale.inclusion B S hS X.1)
      (structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat.{u} RingCat.{u})).obj
        (meromorphicSectionStructureModule B S hS X L) with hPAff
  have hcart : ∀ {Z W : (AffineEtale B S hS X.1)ᵒᵖ} (g : Z ⟶ W),
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1}
        (R := affineEtaleChartRings B S hS X.1) (PAff.uliftSections.{u + 1}) g) := by
    intro Z W g
    refine isIso_restrictionBaseChange_uliftSections.{u + 1, u + 1, u, u, u}
      (R := affineEtaleChartRings B S hS X.1) _ g ?_
    exact isIso_restrictionBaseChange_meromorphicSectionStructureModule B S hS X L hL hwa hfin
      ((AffineEtale.inclusion B S hS X.1).map g.unop) Z.unop.property W.unop.property
  have hsheaf := isSheaf_of_cartesian_affineEtaleChart.{u, u} B S hS X.1
    (PAff.uliftSections.{u + 1}) hcart
  refine (Presheaf.isSheaf_of_iso_iff
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))).mp hsheaf

/-- **The module analogue of Stacks 0EN6, part (2).**  For an affine object `U` of the small
étale site of an algebraic space `X` satisfying hypotheses (a) and (b) of Stacks 0EN6, and a
quasi-coherent `𝒪_X`-module `L`, the sections of the sheaf `𝒦_X(L)` of meromorphic sections of
Stacks 0EN5 over `U` are exactly the meromorphic sections `𝒦_X(U) ⊗_{𝒪_X(U)} L(U)`. -/
theorem bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : L.IsQuasicoherentOnSite)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    Function.Bijective (toMeromorphicSectionSheaf B S hS X.1 X.2 L U) :=
  bijective_toMeromorphicSectionSheaf_of_isAffine B S hS X.1 X.2 L
    (isSheaf_affineEtale_meromorphicSectionModuleUp B S hS X L hL hwa hfin) U hU

end AlgebraicGeometry.Space

end
