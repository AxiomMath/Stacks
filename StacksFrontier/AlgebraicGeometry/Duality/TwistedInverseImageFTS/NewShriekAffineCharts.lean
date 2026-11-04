module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekRelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleDataOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Local
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModuleIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `H⁰(f_new^! 𝒪_Y)` on the affine opens of a locally quasi-finite morphism

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes of
finite type over `S`, not necessarily separated. On an affine open `V ⊆ X` the restriction
`V → Y` is separated, so `H⁰(f_new^! 𝒪_Y)|_V = H⁰((V → Y)_new^! 𝒪_Y)` is identified, through the
closing remark of [Stacks, Tag 0AUE] and the first assertion of [Stacks, Tag 0BUL], with the
module `M|_V` of a factorization `V → T → Y` into an open immersion and a finite morphism. This
file builds these identifications and the chart data they carry.

## Main definitions

* `Stacks.Duality.homologyPullIso`: `H⁰` commutes with restriction to an open.
* `Stacks.Duality.NormalizedOnOpens.newShriekStructureSheafZerothRestrictIso`:
  `H⁰(f_new^! 𝒪_Y)|_V ≅ H⁰((V → Y)_new^! 𝒪_Y)`.
* `Stacks.Duality.NormalizedOnOpens.affineIso`, `Stacks.Duality.NormalizedOnOpens.affineData`:
  the identification with `M|_V` and the chart data of `ω_{V/Y}` on `H⁰(f_new^! 𝒪_Y)|_V`.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)
open CategoryTheory.MonoidalClosed

/-- `H⁰` at the standard model commutes with restriction to an open. -/
def homologyPullIso {X : Scheme.{u}} (V : X.Opens) (K : Std X) :
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) 0).obj ((pull V.ι).obj K) ≅
      ((@DerivedCategory.homologyFunctor X.Modules _ _
        (PerfectApproximation.standardModel X) 0).obj K).restrict V.ι :=
  letI := PerfectApproximation.standardModel X
  letI := PerfectApproximation.standardModel V.toScheme
  (DerivedCategory.homologyFunctor V.toScheme.Modules 0).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback V.ι).app K).symm ≪≫
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryHomologyIso 0).app K

section Independence

variable {S : Scheme.{u}} [IsNoetherian S] {A B : FTS S} {g : A ⟶ B} [LocallyQuasiFinite g.left]

/-- The affine identifications of the chart data of a factorization, read through an
isomorphism onto `H⁰(g^!𝒪)`, do not depend on the factorization. -/
theorem OpenFiniteFactorization.localEquiv_ofFiniteTrace_trans_eq
    (F₁ F₂ : OpenFiniteFactorization g)
    (j : CompactificationOf (Over.mk g.left)) {N' : A.left.Modules}
    (α : N' ≅ upperShriekStructureSheafZeroth g j) (U : B.left.affineOpens)
    (V : A.left.affineOpens) (hVU : V.1 ≤ g.left ⁻¹ᵁ U.1) :
    letI : Algebra Γ(B.left, U.1) Γ(A.left, V.1) := (g.left.appLE U V hVU).hom.toAlgebra
    ∀ (G : Stacks.Discriminant.FiniteOpenFactorization.{u, u, u} Γ(B.left, U.1) Γ(A.left, V.1))
      (s : Γ(N', V.1)),
      (Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace F₁.fac
          (finiteZeroTwisted F₁) (finiteTrace F₁) (bijective_traceDual_finiteTrace F₁)
          (α ≪≫ upperShriekStructureSheafZerothIso F₁ j)).localEquiv U V hVU G s =
        (Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace F₂.fac
          (finiteZeroTwisted F₂) (finiteTrace F₂) (bijective_traceDual_finiteTrace F₂)
          (α ≪≫ upperShriekStructureSheafZerothIso F₂ j)).localEquiv U V hVU G s := by
  let : Algebra Γ(B.left, U.1) Γ(A.left, V.1) := (g.left.appLE U V hVU).hom.toAlgebra
  intro G s
  exact (Stacks.Discriminant.ofFiniteTraceLocalEquiv_trans _ _ _ _ _ _ U V hVU G s).trans
    ((congrArg (fun φ : Γ(upperShriekStructureSheafZeroth g j, V.1) ≃ₗ[Γ(A.left, V.1)]
        Stacks.Discriminant.dualizingModule G => φ (α.hom.app V.1 s))
      (OpenFiniteFactorization.localEquiv_relativeDualizingModuleData_eq F₁ F₂ j U V hVU G)).trans
      (Stacks.Discriminant.ofFiniteTraceLocalEquiv_trans _ _ _ _ _ _ U V hVU G s).symm)

end Independence

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} (f : X ⟶ Y) {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed in
/-- `H⁰(f_new^! 𝒪_Y)|_V ≅ H⁰((V → Y)_new^! 𝒪_Y)`, with `ω_V^• = ω_X^•|_V`. -/
def newShriekStructureSheafZerothRestrictIso (V : X.Opens) :
    (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y).restrict V.ι ≅
      newShriekStructureSheafZeroth c (V.ι ≫ f) (𝒦X.restrict V) 𝒦Y :=
  (homologyPullIso V _).symm ≪≫
    (@DerivedCategory.homologyFunctor V.toScheme.Modules _ _
      (PerfectApproximation.standardModel V.toScheme) 0).mapIso
      ((fNewShriekRestrictIso V.ι f (V.ι ≫ f) rfl (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).app
          (structureStd Y) ≪≫
        (Functor.isoWhiskerLeft ((dualInto (stdComplex c 𝒦Y)).rightOp ⋙ (pull (V.ι ≫ f)).op)
          (dualIntoMapIso (stdComplexRestrictIso c 𝒦X V).symm)).app (structureStd Y))

/-- An affine open of a scheme of finite type over a Noetherian base is separated and of finite
type over the base ([Stacks, Tag 01KV]). -/
theorem _root_.Stacks.Duality.IsFiniteTypeOverNoetherian.isShriekable_of_isAffineOpen
    {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p) {V : X.Opens}
    (hV : IsAffineOpen V) : IsShriekable (V.ι ≫ p) := by
  have := hp.base_noetherian
  have := hp.source_noetherian
  have := hp.locallyOfFiniteType
  have : IsAffine V.toScheme := hV
  have := hp.opens_noetherian V
  exact { target_noetherian := hp.base_noetherian
          separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩,
            quasiCompact_of_noetherianSpace_source _⟩ }

variable {f} (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

/-- The restriction of `f` to an affine open of the source is shriekable. -/
theorem _root_.Stacks.Duality.IsFiniteTypeOverNoetherian.isShriekable_ι_comp_of_isAffineOpen
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) (hpe : f ≫ q = p) {V : X.Opens} (hV : IsAffineOpen V) :
    IsShriekable (V.ι ≫ f) :=
  hp.isShriekable_ι_comp hq hpe (V := ⊤) (fun _ _ => trivial)
    (hp.isShriekable_of_isAffineOpen hV)

include hpe in
/-- The structure morphism of an open `V ⊆ X` factors through `V → Y`. -/
theorem comp_structure_ι (V : X.Opens) : (V.ι ≫ f) ≫ q = V.ι ≫ p := by
  rw [Category.assoc, hpe]

variable [LocallyQuasiFinite f]

/-- The chosen open-finite factorization of `V → Y` for an affine open `V ⊆ X`. -/
def affineFactorization (V : X.affineOpens) :
    haveI := hq.source_noetherian
    OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)) :=
  haveI := hq.source_noetherian
  haveI : LocallyQuasiFinite
      (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).left :=
    inferInstanceAs (LocallyQuasiFinite (V.1.ι ≫ f))
  chosenOpenFiniteFactorization _

/-- The identification of `H⁰(f_new^! 𝒪_Y)|_V` with the module `M|_V` of a factorization
`V → T → Y`. -/
def affineIso (V : X.affineOpens) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)),
    (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y).restrict V.1.ι ≅
      @Scheme.Modules.restrict _ _ (finiteZeroTwisted F) F.immersion
        F.isOpenImmersion_immersion :=
  haveI := hq.source_noetherian
  fun F => (newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y V.1 ≪≫
    newShriekStructureSheafZerothIso c (comp_structure_ι hpe V.1) hωS
      (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2) (𝒦X.restrict V.1) 𝒦Y) ≪≫
    upperShriekStructureSheafZerothIso F (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2))

/-- The chart data of `ω_{V/Y}` on `H⁰(f_new^! 𝒪_Y)|_V` for an affine open `V ⊆ X`, through the
chosen factorization of `V → Y`. -/
def affineData (V : X.affineOpens) :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    Stacks.Discriminant.RelativeDualizingModuleData (V.1.ι ≫ f) :=
  haveI := hp.source_noetherian
  haveI := hq.source_noetherian
  haveI : LocallyQuasiFinite
      (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).left :=
    inferInstanceAs (LocallyQuasiFinite (V.1.ι ≫ f))
  Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace
    (affineFactorization (hp := hp) (hq := hq) hpe V).fac
    (finiteZeroTwisted (affineFactorization (hp := hp) (hq := hq) hpe V))
    (finiteTrace (affineFactorization (hp := hp) (hq := hq) hpe V))
    (bijective_traceDual_finiteTrace (affineFactorization (hp := hp) (hq := hq) hpe V))
    (affineIso c 𝒦X 𝒦Y hpe hωS V (affineFactorization (hp := hp) (hq := hq) hpe V))

/-- The restriction of a factorization of `V → Y` to an open `W ⊆ V`. -/
def restrictFactorization {V W : X.affineOpens} (hWV : W.1 ≤ V.1) :
    haveI := hq.source_noetherian
    OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)) →
      OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2)) :=
  haveI := hq.source_noetherian
  fun F =>
  { space := F.space
    immersion := X.homOfLE hWV ≫ F.immersion
    toBase := F.toBase
    isOpenImmersion_immersion :=
      @IsOpenImmersion.comp _ _ _ (X.homOfLE hWV) F.immersion inferInstance
        F.isOpenImmersion_immersion
    fac := (Category.assoc _ _ _).trans ((congrArg (fun φ => X.homOfLE hWV ≫ φ) F.fac).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (Scheme.homOfLE_ι X hWV)))) }

end NormalizedOnOpens

end Stacks.Duality
