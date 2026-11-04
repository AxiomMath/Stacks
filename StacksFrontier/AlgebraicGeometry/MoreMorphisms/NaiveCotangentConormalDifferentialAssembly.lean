module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalDifferentialComplex
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentTowerScheme
public import StacksFrontier.Homology.DoubleMappingCone

/-!
# Assembling `NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` from the tower complex

Let `i : X ⟶ P` be an immersion of schemes and `g : P ⟶ Y` formally smooth.
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentTowerScheme` identifies `NL_{X/Y}` in
`D(𝒪_X)` with the two-term complex

`(I/I² ⟶ 𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y])`

of the presentation `i⁻¹𝒪_P ⟶ 𝒪_X`, whose two terms are the sites-level conormal sheaf and
tensor-differentials sheaf of [Stacks Project, Tag 08TS].  The right-hand side of
[Stacks Project, Tag 0FV4] is instead the geometric two-term complex
`Stacks.ConormalSequenceRight.conormalDifferentialComplex i g`, built from the geometric conormal
sheaf of [Stacks Project, Tag 01R2] and the first arrow of the conormal sequence of
[Stacks Project, Tag 01UZ].  This file does the categorical work of passing from one to the other,
given the two identifications of the terms.

In degree `-1`, the sites-level conormal sheaf is the geometric one by
`Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf` (the degree `-1` input of
[Stacks Project, Tag 0FV2]), read at the spelling of the conormal sheaf that
[Stacks Project, Tag 01UZ] uses through `Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge`.

The degree `0` identification `𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y] ≅ i^*Ω_{P/Y}` and the
commutation of the resulting square with the two differentials are hypotheses of the statements.

## Main results

* `Stacks.NaiveCotangentConormalAssembly.hsq_of_transpose`: the commuting square needed in degree
  `-1`/`0` follows from the identity of the two *transposes* on the ideal sheaf of the canonical
  closed factor — which is the form in which [Stacks Project, Tag 01UZ]'s first arrow is pinned
  down (`Stacks.ConormalSequenceRight.conormalDifferential_unique`).
* `Stacks.NaiveCotangentConormalAssembly.towerComplexIso`: the resulting isomorphism of complexes
  `(I/I² ⟶ 𝒪_X ⊗ Ω) ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})`.
* `Stacks.NaiveCotangentConormalAssembly.derivedIso`: the isomorphism
  `NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in `D(𝒪_X)` that it produces.

## Implementation notes

The two spellings of the category of sheaves of `𝒪_X`-modules — `AlgebraicGeometry.Scheme.Modules`
and `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_X)` — are definitionally equal but
carry distinct `CategoryTheory.Category` instances, and a goal that mixes them is not type-correct
at reducible transparency, so `rw` and `simp` do not act on it.  The categorical steps are
therefore isolated into the abstract lemmas
`Stacks.NaiveCotangentConormalAssembly.iso_comm_of_comm`,
`...comp_eq_zero_of_eq_zero`, `...cancel_inv_inv`, `...comp_functor_map_comp` and
`...functor_map_comp_of_eq`, each stated in a bare category where the tactics do work, and applied
with `exact`, which uses default transparency.

For the same reason the type of `Stacks.NaiveCotangentConormalAssembly.derivedIso` ascribes
`AlgebraicGeometry.Scheme.naiveCotangentComplex` to `CochainComplex X.Modules ℤ`: with the two
spellings left as they come, the two occurrences of `DerivedCategory.Q` trigger two independent
searches for `HasDerivedCategory` and the universe constraint between them cannot be solved.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow is the differential of the target complex.
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the sites-level conormal
  sequence, whose two terms the source complex is built from.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.Sites.FreeAlgebra
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.ConormalSequenceRight
open HomologicalComplex (doubleIsoOfIsZero)
open RingedSpaceModuleAdjunction

universe u

noncomputable section

namespace Stacks.NaiveCotangentConormalAssembly

/-- If `σ ≫ br ≫ ψ = f ≫ t`, then `(σ ≫ br ≫ e₁.inv) ≫ e₁.hom ≫ ψ ≫ e₀.inv = f ≫ t ≫ e₀.inv`
for isomorphisms `e₁ : K₁ ≅ M` and `e₀ : K₀ ≅ T`. -/
theorem iso_comm_of_comm {C : Type*} [Category C] {S M₀ M K₁ T K₀ N : C}
    (σ : S ⟶ M₀) (br : M₀ ⟶ M) (e₁ : K₁ ≅ M) (ψ : M ⟶ T) (e₀ : K₀ ≅ T) (f : S ⟶ N) (t : N ⟶ T)
    (h : σ ≫ br ≫ ψ = f ≫ t) :
    (σ ≫ br ≫ e₁.inv) ≫ e₁.hom ≫ ψ ≫ e₀.inv = f ≫ t ≫ e₀.inv := by
  have h2 : (σ ≫ br ≫ ψ) ≫ e₀.inv = (f ≫ t) ≫ e₀.inv := congrArg (fun m ↦ m ≫ e₀.inv) h
  simp only [Category.assoc] at h2
  simpa using h2

/-- Composing with a vanishing morphism gives zero. -/
theorem comp_eq_zero_of_eq_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {A B D : C}
    (f : A ⟶ B) {g : B ⟶ D} (hg : g = 0) : f ≫ g = 0 := by
  rw [hg, Limits.comp_zero]

/-- If `b.hom ≫ e.hom ≫ k = ψ` for isomorphisms `e` and `b`, then `e.inv ≫ b.inv ≫ ψ = k`. -/
theorem cancel_inv_inv {C : Type*} [Category C] {S M₁ M₂ T : C} (e : M₁ ≅ S) (b : M₂ ≅ M₁)
    (ψ : M₂ ⟶ T) (k : S ⟶ T) (h : b.hom ≫ e.hom ≫ k = ψ) :
    e.inv ≫ b.inv ≫ ψ = k := by
  rw [← h, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

/-- For a functor `F`, if `cc ≫ F.map b = ib ≫ u`, then
`cc ≫ F.map (b ≫ r) = ib ≫ u ≫ F.map r`. -/
theorem comp_functor_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B₁ : D} {M₁ M₂ M₃ : C} (cc : A ⟶ F.obj M₁) (b : M₁ ⟶ M₂) (r : M₂ ⟶ M₃)
    (ib : A ⟶ B₁) (u : B₁ ⟶ F.obj M₂) (h : cc ≫ F.map b = ib ≫ u) :
    cc ≫ F.map (b ≫ r) = ib ≫ u ≫ F.map r := by
  rw [F.map_comp, ← Category.assoc, h, Category.assoc]

/-- For a functor `F`, if `u ≫ F.map e = t`, then `ib ≫ u ≫ F.map (e ≫ k) = ib ≫ t ≫ F.map k`. -/
theorem functor_map_comp_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B₁ : D}
    {M₁ M₂ M₃ : C} (ib : A ⟶ B₁) (u : B₁ ⟶ F.obj M₁) (e : M₁ ⟶ M₂) (k : M₂ ⟶ M₃)
    {t : B₁ ⟶ F.obj M₂} (h : u ≫ F.map e = t) :
    ib ≫ u ≫ F.map (e ≫ k) = ib ≫ t ≫ F.map k := by
  rw [F.map_comp, ← h]
  simp

/-! ### The square and the isomorphism of complexes -/

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y) [IsImmersion i]

/-- The square comparing the two differentials in degrees `-1` and `0` commutes, given the identity
of the two transposes on the ideal sheaf of the canonical closed factor. -/
theorem hsq_of_transpose
    (τ : (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).X₂ ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g))
    (hτ : (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom ≫
          Stacks.Conormal.Sites.conormalTranspose i ≫
          (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
            ((Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
                (Opens.grothendieckTopology X.toRingedSpace.carrier)
                (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
                (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
                (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
                (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫ τ.hom) =
        Stacks.ConormalSequenceRight.conormalDifferentialTranspose i g) :
    (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i).hom ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          conormalDifferential i g =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫ τ.hom := by
  refine cancel_inv_inv (Stacks.Conormal.Sites.conormalComparisonIso i)
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i) (conormalDifferential i g) _ ?_
  refine Stacks.ConormalSequenceRight.conormalDifferential_unique i g _ ?_
  refine Eq.trans ?_ hτ
  refine Eq.trans (comp_functor_map_comp
    (modulePushforward i.liftCoborder.toLRSHom.toShHom)
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison i)
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom
    (Stacks.Conormal.Sites.conormalComparison i ≫
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫ τ.hom)
    (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom
    ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
      (Stacks.Conormal.Sites.idealSheafLift i))
    (Stacks.Conormal.DefiningIdealBridge.conormalComparison_comp_conormalSheafBridge i)) ?_
  exact functor_map_comp_of_eq (modulePushforward i.liftCoborder.toLRSHom.toShHom) _ _
    (Stacks.Conormal.Sites.conormalComparison i) _
    (Stacks.Conormal.Sites.unit_comp_conormalComparison i)

/-- **The isomorphism of complexes `(I/I² ⟶ 𝒪_X ⊗ Ω) ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})`**, given the
degree `0` identification of the terms and the commuting square. -/
def towerComplexIso
    (τ : (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).X₂ ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g))
    (hsq : (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i).hom ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          conormalDifferential i g =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫ τ.hom) :
    towerNaiveCotangentComplex
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i)) ≅
      conormalDifferentialComplex i g :=
  doubleIsoOfIsZero _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (conormalDifferentialComplex i g)
    (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i ≪≫
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).symm ≪≫
      (conormalDifferentialComplexXIsoNegOne i g).symm)
    (τ ≪≫ (conormalDifferentialComplexXIsoZero i g).symm)
    (by
      rw [conormalDifferentialComplex_d_negOne_zero]
      exact iso_comm_of_comm (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i).hom
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv
        (conormalDifferentialComplexXIsoNegOne i g) (conormalDifferential i g)
        (conormalDifferentialComplexXIsoZero i g) _ τ.hom hsq)
    (fun j _ ↦ by
      have hz : (conormalDifferentialComplex i g).d 0 j = 0 :=
        HomologicalComplex.double_d_eq_zero₀ (conormalDifferential i g)
          ComplexShape.upIntRelNegOneZero 0 j (by decide)
      exact comp_eq_zero_of_eq_zero _ hz)
    (fun j h0 h1 ↦ conormalDifferentialComplex_isZero_X i g j h0 h1)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in `D(𝒪_X)`**, given the degree `0` identification
of the terms and the commuting square. -/
def derivedIso (hg : Stacks.Smooth.FormallySmoothScheme g)
    (τ : (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).X₂ ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g))
    (hsq : (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i).hom ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          conormalDifferential i g =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫ τ.hom) :
    DerivedCategory.Q.obj
        (Scheme.naiveCotangentComplex (i ≫ g) : CochainComplex X.Modules ℤ) ≅
      DerivedCategory.Q.obj (conormalDifferentialComplex i g) :=
  Stacks.NaiveCotangentTower.schemeTowerIso i g hg ≪≫
    DerivedCategory.Q.mapIso (towerComplexIso i g τ hsq)

end Derived

end Stacks.NaiveCotangentConormalAssembly

end

end
