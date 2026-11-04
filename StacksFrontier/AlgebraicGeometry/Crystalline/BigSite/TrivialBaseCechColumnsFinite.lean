module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamTrivialBaseRows
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseCechColumns

/-!
# Finiteness and vanishing of the columns of the Čech–de Rham double complex

Continuation of `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/TrivialBaseCechColumns.lean`.

## Main results

* `Crystalline.GlobalCrystallineSituation.isLocalizing_trivialColumnModule` — the column module
  localizes on the basic opens of the affine opens.
* `Crystalline.GlobalCrystallineSituation.moduleFinite_homology_trivialColumnPresheaf`,
  `Crystalline.GlobalCrystallineSituation.isZero_homology_trivialColumnPresheaf` — the Čech
  cohomology of a column along a finite affine cover is finite, and vanishes in degrees at least
  the size of the cover.
* `Crystalline.GlobalCrystallineSituation.exists_isZero_trivialColumnPresheaf` — the columns
  vanish in high degree.
* `Crystalline.GlobalCrystallineSituation.trivialColumnPresheaf_eq` — the column presheaf is the
  degree-`a` part of `...bigCrystalDeRhamPresheaf` along the trivial thickenings, by `rfl`.
* `Crystalline.GlobalCrystallineSituation.moduleFinite_homology_trivialCechDeRhamDoubleComplex_X`,
  `Crystalline.GlobalCrystallineSituation.exists_isZero_trivialCechDeRhamDoubleComplex_X` — the
  same two statements for the Čech–de Rham double complex
  `...CechEnvelope.trivialCechDeRhamDoubleComplex` of the trivial thickenings of a cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe w u

namespace Crystalline.GlobalCrystallineSituation

open SmallSite

variable {T : GlobalCrystallineSituation.{u}}

namespace TrivialColumn

variable (N : SheafOfModules.{u} (crystallineStructureSheaf T)) (a : ℕ)

/-! ### The crystal localizes -/

section Crystal

variable {W V : T.X.Opens} (h : W ≤ V)

/-- The base change `Γ(W) ⊗_{Γ(V)} N(V, V, 0)` of the sections of `N`, read in the spelling of
`...SmallSite.crysBaseChange`: the identity on pure tensors. -/
def baseChangeCross :
    letI := DeRhamPair.algebraOf (ringMap h)
    (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u) ⊗[
        sectionsDPRing T ((openTrivialThickening T).obj V).obj]
        (restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)) →+
      ringAlong ((openTrivialThickening T).map (homOfLE h)).hom ⊗[
        crysSheafRing T ((openTrivialThickening T).obj V).obj]
        (restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)) :=
  letI := DeRhamPair.algebraOf (ringMap h)
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun q ↦ (TensorProduct.mk (crysSheafRing T
        ((openTrivialThickening T).obj V).obj)
        (ringAlong ((openTrivialThickening T).map (homOfLE h)).hom)
        ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)))
        (ringAlongSection ((openTrivialThickening T).map (homOfLE h)).hom q)).toAddMonoidHom)
      (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _))
    (fun b q m ↦ TensorProduct.smul_tmul
      (R := crysSheafRing T ((openTrivialThickening T).obj V).obj)
      (R' := crysSheafRing T ((openTrivialThickening T).obj V).obj) b
      (ringAlongSection ((openTrivialThickening T).map (homOfLE h)).hom q) m)

/-- The inverse of `baseChangeCross`. -/
def baseChangeCrossInv :
    letI := DeRhamPair.algebraOf (ringMap h)
    ringAlong ((openTrivialThickening T).map (homOfLE h)).hom ⊗[
        crysSheafRing T ((openTrivialThickening T).obj V).obj]
        (restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)) →+
      (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u) ⊗[
        sectionsDPRing T ((openTrivialThickening T).obj V).obj]
        (restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)) :=
  letI := DeRhamPair.algebraOf (ringMap h)
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun t ↦ (TensorProduct.mk (sectionsDPRing T
        ((openTrivialThickening T).obj V).obj)
        (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)
        ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V)))
        (siteRingAlong ((openTrivialThickening T).map (homOfLE h)).hom t)).toAddMonoidHom)
      (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _))
    (fun b t m ↦ TensorProduct.smul_tmul
      (R := sectionsDPRing T ((openTrivialThickening T).obj V).obj)
      (R' := sectionsDPRing T ((openTrivialThickening T).obj V).obj)
      (M := (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)) b
      (siteRingAlong ((openTrivialThickening T).map (homOfLE h)).hom t) m)

/-- `baseChangeCross` is bijective. -/
theorem bijective_baseChangeCross : Function.Bijective (baseChangeCross N h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨baseChangeCrossInv N h, fun z ↦ ?_, fun z ↦ ?_⟩ <;>
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul q m => rfl

/-- The restriction of sections of `N` to a smaller trivial thickening is a scalar tower over the
sections of the thickening of the larger open. -/
private theorem isScalarTower_restrict :
    letI := DeRhamPair.algebraOf (ringMap h)
    letI := DeRhamPair.compHomModule (ringMap h)
      ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W)))
    IsScalarTower (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
        (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)
        ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W))) := by
  let := DeRhamPair.algebraOf (ringMap h)
  let := DeRhamPair.compHomModule (ringMap h)
    ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W)))
  exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable (hN : (restrictSheafOfModules N).IsQuasicoherentOnSite)

include hN in
/-- **The sections of a crystal in quasi-coherent modules over the trivial thickening of an affine
open `W ⊆ V` of an affine open are the base change of its sections over that of `V`**
(`...SmallSite.bijective_crysBaseChange_of_isQuasicoherentOnSite`). -/
theorem isBaseChange_restrict (hW : IsAffineOpen W) (hV : IsAffineOpen V) :
    letI := DeRhamPair.algebraOf (ringMap h)
    letI := DeRhamPair.compHomModule (ringMap h)
      ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W)))
    haveI : IsScalarTower (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
        (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)
        ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)
      (DeRhamPair.toLinear (ringMap h)
        (restrict N ((openTrivialThickening T).map (homOfLE h))).toAddMonoidHom
        (restrict N ((openTrivialThickening T).map (homOfLE h))).map_smulₛₗ) := by
  let := DeRhamPair.algebraOf (ringMap h)
  let := DeRhamPair.compHomModule (ringMap h)
    ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj W)))
  have := isScalarTower_restrict N h
  have hWa : IsAffine (W : Scheme.{u}) := hW
  have hVa : IsAffine (V : Scheme.{u}) := hV
  let L := (DeRhamPair.toLinear (ringMap h)
    (restrict N ((openTrivialThickening T).map (homOfLE h))).toAddMonoidHom
    (restrict N ((openTrivialThickening T).map (homOfLE h))).map_smulₛₗ).liftBaseChange
      (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u)
  have hL : ∀ z, L z = crysBaseChange (restrictSheafOfModules N)
      ((openTrivialThickening T).map (homOfLE h)) (baseChangeCross N h z) := fun z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul q m => rfl
  have hLb : Function.Bijective L := by
    rw [show (L : _ → _) = _ from funext hL]
    exact (bijective_crysBaseChange_of_isQuasicoherentOnSite (restrictSheafOfModules N) hN
      ((openTrivialThickening T).map (homOfLE h)) ⟨hWa, hWa⟩ ⟨hVa, hVa⟩).comp
      (bijective_baseChangeCross N h)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hLb) fun x ↦ one_smul _ _

end Crystal

end TrivialColumn

open TrivialColumn

/-! ### The column localizes on the basic opens of the affine opens -/

variable (N : SheafOfModules.{u} (crystallineStructureSheaf T)) (a : ℕ)

/-- **The column module localizes on the basic opens of the affine opens**, for a crystal in
quasi-coherent modules: for `D(g) ⊆ V` with `V` affine, `N(D(g)) = N(V)_g` by the crystal property,
`Ω_{Γ(D(g))/R} = (Ω_{Γ(V)/R})_g` since the divided power ideals of trivial thickenings are zero,
and exterior powers and tensor products of localizations are localizations
(`Crystalline.DeRhamPair.isLocalizedModule_tensorMap`). -/
theorem isLocalizing_trivialColumnModule
    (hN : (restrictSheafOfModules N).IsQuasicoherentOnSite) :
    AffineOpens.IsLocalizing (trivialColumnModule N a) := by
  rintro V hV g _ rfl hWV
  let := DeRhamPair.algebraOf (ringMap hWV)
  have hloc := isLocalization_ringMap hV g
  let := DeRhamPair.compHomModule (ringMap hWV)
    ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj (T.X.basicOpen g))))
  have := isScalarTower_restrict N hWV
  have hμ := (isLocalizedModule_iff_isBaseChange (Submonoid.powers (sectionsHom T V g)) _ _).2
    (isBaseChange_restrict N hWV hN (hV.basicOpen g) hV)
  have ht := DeRhamPair.isLocalizedModule_tensorMap (ringMap hWV)
    (isDPMorphism_sectionsDPRingMap _) (ideal_eq_bot V) (ideal_eq_bot (T.X.basicOpen g))
    (sectionsHom T V g) hloc
    (TrivialColumn.restrict N ((openTrivialThickening T).map (homOfLE hWV)))
    hμ a
  let : Algebra Γ(T.X, V) (sectionsDPRing T ((openTrivialThickening T).obj V).obj) :=
    (sectionsHom T V).toAlgebra
  let : Module Γ(T.X, V) (term N a ((openTrivialThickening T).obj V)) := termModule N a V
  let : Module Γ(T.X, V) (term N a ((openTrivialThickening T).obj (T.X.basicOpen g))) :=
    Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
      (trivialColumnModule N a) hWV
  let := DeRhamPair.compHomModule (ringMap hWV)
    (term N a ((openTrivialThickening T).obj (T.X.basicOpen g)))
  have hT1 : IsScalarTower Γ(T.X, V)
      (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
      (term N a ((openTrivialThickening T).obj V)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hT2 : IsScalarTower Γ(T.X, V)
      (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
      (term N a ((openTrivialThickening T).obj (T.X.basicOpen g))) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      show ringMap hWV (sectionsHom T V r) • x =
        sectionsHom T (T.X.basicOpen g) (T.X.presheaf.map (homOfLE hWV).op r) • x
      exact congrArg (fun c : (sectionsDPRing T ((openTrivialThickening T).obj
        (T.X.basicOpen g)).obj : Type u) ↦ c • x) (sectionsDPRingMap_sectionsHom hWV r)
  exact @IsLocalizedModule.restrictScalars_powers _ _ _ _ _ _ _ _ _ _ _ _ _ hT1 hT2 g _ ht

/-! ### The column is finite over the affine opens -/

/-- **The ring of sections of the trivial thickening of an affine open of `X` is of finite type
over `R`**, when `X` is locally of finite type over the affine base. -/
theorem finiteType_sectionsDPRing [IsAffine T.S.scheme] [LocallyOfFiniteType (sourceToBase T)]
    {V : T.X.Opens} (hV : IsAffineOpen V) :
    Algebra.FiniteType Γ(T.S.scheme, ⊤)
      (sectionsDPRing T ((openTrivialThickening T).obj V).obj) :=
  have : IsAffine (V : Scheme.{u}) := hV
  HasRingHomProperty.appLE @LocallyOfFiniteType (V.ι ≫ sourceToBase T) inferInstance
    ⟨⊤, isAffineOpen_top T.S.scheme⟩ ⟨⊤, isAffineOpen_top (V : Scheme.{u})⟩ _

/-- **The divided power differentials of the trivial thickening of an affine open are finite.** -/
theorem finite_dividedPowerDifferentials [IsAffine T.S.scheme]
    [LocallyOfFiniteType (sourceToBase T)] {V : T.X.Opens} (hV : IsAffineOpen V) :
    Module.Finite (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
      (dividedPowerDifferentials (A := Γ(T.S.scheme, ⊤))
        (sectionsDPRing T ((openTrivialThickening T).obj V).obj).dividedPowers) :=
  have := finiteType_sectionsDPRing hV
  inferInstance

/-- **The sections of the column over an affine open are a finite module**, for a crystal in
finite locally free modules on a scheme locally of finite type over the affine base. -/
theorem isFiniteOnAffines_trivialColumnModule [IsAffine T.S.scheme]
    [LocallyOfFiniteType (sourceToBase T)] (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) :
    AffineOpens.IsFiniteOnAffines (trivialColumnModule N a) := by
  intro V hV
  have : IsAffine ((openTrivialThickening T).obj V).obj.thickening.target.scheme := hV
  have : Module.Finite (sectionsDPRing T ((openTrivialThickening T).obj V).obj : Type u)
      ((restrictSheafOfModules N).val.obj (op ((openTrivialThickening T).obj V))) :=
    hN.finite_val_obj ((openTrivialThickening T).obj V).obj
  have := finite_dividedPowerDifferentials hV
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (R := Γ(T.X, V)) (sectionsHom T V) (sectionsEquiv V).surjective
    (term N a ((openTrivialThickening T).obj V))

/-! ### The Čech cohomology of the columns -/

section Cech

variable [T.X.IsSeparated] {ι : Type w} [Finite ι]
  [HasProducts.{w} (ModuleCat.{u} Γ(T.S.scheme, ⊤))] (U : ι → AffineOpens T.X)
  (hU : ⨆ i, (U i).obj = ⊤)

include hU in
/-- **The Čech cohomology of the degree-`a` column along a finite affine cover is finite**: for
`X` proper over the affine base `S` with `R = Γ(S, 𝒪_S)` Noetherian and `N` a crystal in finite
locally free modules on `CRIS(X/S)`, every cohomology module of the Čech complex of
`V ↦ N(V, V, 0) ⊗_{Γ(V)} Ω^a_{Γ(V)/R, 0}` along a finite cover of `X` by affine opens is a finite
`R`-module. -/
theorem moduleFinite_homology_trivialColumnPresheaf [IsAffine T.S.scheme]
    [IsNoetherianRing Γ(T.S.scheme, ⊤)] [IsProper (sourceToBase T)]
    (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) (r : ℕ) :
    Module.Finite Γ(T.S.scheme, ⊤)
      (((Stacks.CechSite.FinalCover.complexFunctor U (ModuleCat.{u} Γ(T.S.scheme, ⊤))).obj
        (trivialColumnPresheaf N a)).homology r) := by
  have : IsLocallyNoetherian T.S.scheme :=
    isLocallyNoetherian_of_affine_cover (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top _⟩)
      (iSup_const.trans rfl) fun _ ↦ inferInstanceAs (IsNoetherianRing Γ(T.S.scheme, ⊤))
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _
    (AffineOpens.moduleFinite_homology_presheafSections (sourceToBase T) U hU
      (isLocalizing_trivialColumnModule N a
        (isQuasicoherentOnSite_restrictSheafOfModules hN.isQuasicoherentOnSite))
      (isFiniteOnAffines_trivialColumnModule N a hN) r)
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) r).mapIso
      ((Stacks.CechSite.FinalCover.complexFunctor U (ModuleCat.{u} Γ(T.S.scheme, ⊤))).mapIso
        (trivialColumnPresheafIso N a))).symm.toLinearEquiv

include hU in
/-- **The Čech cohomology of the degree-`a` column along a finite affine cover vanishes in degrees
at least the size of the cover**, for a crystal in quasi-coherent modules on a separated `X` over
an affine base. -/
theorem isZero_homology_trivialColumnPresheaf [IsAffine T.S.scheme]
    (hN : (restrictSheafOfModules N).IsQuasicoherentOnSite) (r : ℕ) (hr : Nat.card ι ≤ r) :
    IsZero (((Stacks.CechSite.FinalCover.complexFunctor U (ModuleCat.{u} Γ(T.S.scheme, ⊤))).obj
      (trivialColumnPresheaf N a)).homology r) :=
  IsZero.of_iso (AffineOpens.isZero_homology_presheafSections (sourceToBase T) U hU
      (isLocalizing_trivialColumnModule N a hN) r hr)
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) r).mapIso
      ((Stacks.CechSite.FinalCover.complexFunctor U (ModuleCat.{u} Γ(T.S.scheme, ⊤))).mapIso
        (trivialColumnPresheafIso N a)))

end Cech

/-! ### The columns vanish in high degree -/

section Vanishing

open Stacks.AlgebraicGeometry.AffineChartLocalization

attribute [local instance] sectionsModule

/-- **Over an affine open the column vanishes in high degree**: the divided power differentials
of a finite type algebra are generated by finitely many elements, and exterior powers above that
number vanish. -/
theorem exists_subsingleton_term [IsAffine T.S.scheme] [LocallyOfFiniteType (sourceToBase T)]
    {W : T.X.Opens} (hW : IsAffineOpen W) :
    ∃ d : ℕ, ∀ a, d < a → Subsingleton (term N a ((openTrivialThickening T).obj W)) := by
  have := finite_dividedPowerDifferentials hW
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin
    (R := (sectionsDPRing T ((openTrivialThickening T).obj W).obj : Type u))
    (M := dividedPowerDifferentials (A := Γ(T.S.scheme, ⊤))
      (sectionsDPRing T ((openTrivialThickening T).obj W).obj).dividedPowers)
  refine ⟨n, fun a ha ↦ ?_⟩
  have := exteriorPower.subsingleton_of_span_eq_top_of_card_lt v hv a (by simpa using ha)
  infer_instance

variable (hN : (restrictSheafOfModules N).IsQuasicoherentOnSite)

include hN in
/-- If the column vanishes on an affine open, it vanishes on its basic opens, being a
localization there. -/
theorem subsingleton_term_basicOpen {W : T.X.Opens} (hW : IsAffineOpen W) (g : Γ(T.X, W))
    (h : Subsingleton (term N a ((openTrivialThickening T).obj W))) :
    Subsingleton (term N a ((openTrivialThickening T).obj (T.X.basicOpen g))) := by
  let := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
    (trivialColumnModule N a) (T.X.basicOpen_le g)
  have hloc := isLocalizing_trivialColumnModule N a hN W hW g rfl (T.X.basicOpen_le g)
  refine ⟨fun y y' ↦ ?_⟩
  suffices hz : ∀ y : (trivialColumnModule N a).obj (op (T.X.basicOpen g)), y = 0 from
    (hz y).trans (hz y').symm
  intro y
  obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (Stacks.AlgebraicGeometry.AffineChartLocalization.presheafRestrictₗ (trivialColumnModule N a)
      (T.X.basicOpen_le g)) y
  have : Subsingleton ((trivialColumnModule N a).obj (op W)) := h
  have hu := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units
    (Stacks.AlgebraicGeometry.AffineChartLocalization.presheafRestrictₗ (trivialColumnModule N a)
      (T.X.basicOpen_le g)) c)
  refine hu.1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_zero]
  exact hc.trans (by rw [Subsingleton.elim x 0, map_zero])

include hN in
/-- **The column vanishes on an affine open as soon as it vanishes on the members of a cover of
it by basic opens**: a section killed on every `D(f)` is killed by a power of every `f`, and the
`f` generate the unit ideal. -/
theorem subsingleton_term_of_basicOpen {V : T.X.Opens} (hV : IsAffineOpen V)
    (h : ∀ x ∈ V, ∃ f : Γ(T.X, V), x ∈ T.X.basicOpen f ∧
      Subsingleton (term N a ((openTrivialThickening T).obj (T.X.basicOpen f)))) :
    Subsingleton (term N a ((openTrivialThickening T).obj V)) := by
  refine ⟨fun z z' ↦ ?_⟩
  suffices hz : ∀ z : (trivialColumnModule N a).obj (op V), z = 0 from
    (hz z).trans (hz z').symm
  intro z
  choose f hxf hf using h
  have hpow : ∀ x : V, ∃ n : ℕ, f x x.2 ^ n • z = 0 := by
    intro x
    let := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafModuleOfLE
      (trivialColumnModule N a) (T.X.basicOpen_le (f x x.2))
    have hloc := isLocalizing_trivialColumnModule N a hN V hV (f x x.2) rfl
      (T.X.basicOpen_le (f x x.2))
    have : Subsingleton ((trivialColumnModule N a).obj (op (T.X.basicOpen (f x x.2)))) :=
      hf x x.2
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f x x.2))
      (f := Stacks.AlgebraicGeometry.AffineChartLocalization.presheafRestrictₗ
        (trivialColumnModule N a) (T.X.basicOpen_le (f x x.2)))
      (x₁ := z) (x₂ := 0) (Subsingleton.elim _ _)
    exact ⟨n, hc.trans (smul_zero _)⟩
  choose n hn using hpow
  let I : Ideal Γ(T.X, V) := LinearMap.ker (LinearMap.toSpanSingleton Γ(T.X, V) _ z)
  have hspan : Ideal.span (Set.range fun x : V ↦ f x x.2 ^ (n x + 1)) = ⊤ := by
    refine (hV.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, ⟨⟨x, hx⟩, rfl⟩⟩, ?_⟩
    rw [Scheme.basicOpen_pow _ _ (n ⟨x, hx⟩).succ_pos]
    exact hxf x hx
  have hI : I = ⊤ := by
    refine eq_top_iff.2 (hspan ▸ Ideal.span_le.2 ?_)
    rintro _ ⟨x, rfl⟩
    show f x x.2 ^ (n x + 1) • z = 0
    rw [pow_succ', mul_smul, hn x, smul_zero]
  exact (one_smul _ z).symm.trans (hI ▸ Submodule.mem_top : (1 : Γ(T.X, V)) ∈ I)

end Vanishing

/-- **The columns vanish in high degree**: for `X` quasi-compact and locally of finite type over
the affine base and `N` a crystal in quasi-coherent modules, there is `D` such that
`N(V, V, 0) ⊗_{Γ(V)} Ω^a_{Γ(V)/R, 0} = 0` for every affine open `V` and every `a > D`.

A finite cover of `X` by affine opens `W_j` has `Ω_{Γ(W_j)/R}` generated by `d_j` elements, so the
column vanishes on `W_j` above `d_j`, and then on the basic opens of the `W_j`; every affine open
is covered by opens which are basic both in it and in some `W_j`, and the column localizes. -/
theorem exists_isZero_trivialColumnPresheaf [IsAffine T.S.scheme] [CompactSpace T.X]
    [LocallyOfFiniteType (sourceToBase T)]
    (hN : (restrictSheafOfModules N).IsQuasicoherentOnSite) :
    ∃ D : ℕ, ∀ a, D < a → ∀ V : AffineOpens T.X,
      IsZero ((trivialColumnPresheaf N a).obj (op V)) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun W : T.X.affineOpens ↦ ((W : T.X.Opens) : Set T.X)) (fun W ↦ W.1.isOpen)
    fun x _ ↦ by
      obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.X.isBasis_affineOpens)
        (show x ∈ (⊤ : T.X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
  choose d hd using fun W : T.X.affineOpens ↦ exists_subsingleton_term N W.2
  refine ⟨t.sup d, fun a ha V ↦ ?_⟩
  have : Subsingleton (term N a ((openTrivialThickening T).obj V.obj)) := by
    refine subsingleton_term_of_basicOpen N a hN V.property fun x hxV ↦ ?_
    obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.property W.2 x ⟨hxV, hxW⟩
    refine ⟨f, hxf, ?_⟩
    rw [hfg]
    exact subsingleton_term_basicOpen N a hN W.2 g (hd W a ((Finset.le_sup hWt).trans_lt ha))
  have : Subsingleton ((trivialColumnPresheaf N a).obj (op V)) :=
    inferInstanceAs (Subsingleton (term N a ((openTrivialThickening T).obj V.obj)))
  exact ModuleCat.isZero_of_subsingleton _

/-- **The column presheaf is the degree-`a` part of the presheaf of de Rham complexes of `N`**
along the trivial thickenings of the affine opens, on the nose. -/
theorem trivialColumnPresheaf_eq [IsAffine T.S.scheme] (hN : N.IsQuasicoherentOnSite) (a : ℕ) :
    (trivialThickeningFunctor T).op ⋙ bigCrystalDeRhamPresheaf hN ⋙
        HomologicalComplex.eval _ _ a = trivialColumnPresheaf N a :=
  rfl

/-! ### The columns of the Čech–de Rham double complex of the trivial thickenings -/

section DoubleComplex

open AlgebraicTopology

variable {ι : Type} [Finite ι] {U : ι → T.X.Opens} [∀ i, IsAffine (U i)]

/-- **The columns of the Čech–de Rham double complex `C` of the trivial thickenings
`(U_x, U_x, 0)` of a finite affine cover have finite cohomology**, for `X` separated and proper
over the affine base with `R` Noetherian and `N` a crystal in finite locally free modules: the
degree-`a` column is the Čech complex of `trivialColumnPresheaf N a`
(`moduleFinite_homology_trivialColumnPresheaf`). -/
theorem moduleFinite_homology_trivialCechDeRhamDoubleComplex_X [IsAffine T.S.scheme]
    [IsNoetherianRing Γ(T.S.scheme, ⊤)] [IsProper (sourceToBase T)] [T.X.IsSeparated]
    (hU : ∀ x, ∃ i, x ∈ U i) (hN : IsFiniteLocallyFreeQuasicoherentCrystal N)
    (hN' : N.IsQuasicoherentOnSite) (a j : ℕ) :
    Module.Finite Γ(T.S.scheme, ⊤)
      (((alternatingCofaceMapComplex _).obj
        ((CechEnvelope.trivialCechDeRhamDoubleComplex U N hN').X a)).homology j) :=
  moduleFinite_homology_trivialColumnPresheaf N a (CechEnvelope.chartOpen U)
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hU x)) hN j

omit [Finite ι] in
/-- **The Čech–de Rham double complex `C` of the trivial thickenings `(U_x, U_x, 0)` vanishes in
de Rham degrees above some `D`**, for `X` quasi-compact and locally of finite type over the affine
base and `N` quasi-coherent (`exists_isZero_trivialColumnPresheaf`). -/
theorem exists_isZero_trivialCechDeRhamDoubleComplex_X [IsAffine T.S.scheme] [CompactSpace T.X]
    [LocallyOfFiniteType (sourceToBase T)] [T.X.IsSeparated] (U : ι → T.X.Opens)
    [∀ i, IsAffine (U i)] (hN : N.IsQuasicoherentOnSite) :
    ∃ D : ℕ, ∀ a, D < a → IsZero ((CechEnvelope.trivialCechDeRhamDoubleComplex U N hN).X a) := by
  obtain ⟨D, hD⟩ := exists_isZero_trivialColumnPresheaf N
    (isQuasicoherentOnSite_restrictSheafOfModules hN)
  exact ⟨D, fun a ha ↦ Functor.isZero _ fun _ ↦ (IsZero.iff_id_eq_zero _).2
    (Stacks.CechSite.FinalCover.cosimplicialObject_hom_ext _ _ fun _ ↦ (hD a ha _).eq_of_tgt _ _)⟩

end DoubleComplex

end Crystalline.GlobalCrystallineSituation
