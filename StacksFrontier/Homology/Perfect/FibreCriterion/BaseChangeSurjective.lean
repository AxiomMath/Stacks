module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Perfect.FibreCriterion.FibreCohomologyVanishing
import Mathlib
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Splitting from surjectivity of the base-change map

Surjectivity of the base-change map `H^i(K) ⊗_R κ(p) → H^i(K ⊗_R^L κ(p))` makes the degree-`i + 1`
opcycles free near `p`, which gives the splitting criterion [stacks 0A1U]
(`StacksDraft.Perfect.exists_localization_perfect_truncGE_and_iso_biprod`); then the combination of
two principal neighbourhoods into bounded finite projective representatives of two adjacent
upper truncations.

Part of `StacksFrontier.Homology.Perfect.FibreCriterion`; see that module for the overview.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

-- The truncation and base-change identifications below read instances through iterated
-- `mapHomologicalComplex` and `opcycles` isomorphisms; this needs the pre-4.x defeq transparency.
set_option backward.isDefEq.respectTransparency false

namespace StacksDraft.Perfect

universe u v

/-! ### Surjectivity of the base-change map on cohomology

If every degree-`i` cohomology class of the fibre lifts to the base change of the cocycles, then
the inclusion of the image of the degree-`i` differential stays injective after base change, so
the degree-`i + 1` opcycles are free near `p`. -/

/-- A map into the cycles of a short complex is surjective as soon as it hits every boundary and
every homology class. -/
private lemma surjective_cycles_of_homology_lifts
    {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}
    (S : ShortComplex (ModuleCat.{max u v} R))
    (f : M ⟶ S.cycles)
    (hbound : ∀ z : S.X₁, ∃ y : M, f y = S.toCycles z)
    (hlift : ∀ x : S.cycles, ∃ y : M, S.homologyπ (f y) = S.homologyπ x) :
    Function.Surjective f := by
  intro x
  obtain ⟨y, hy⟩ := hlift x
  have hq : S.moduleCatLeftHomologyData.π
      (S.moduleCatCyclesIso.hom (f y)) =
      S.moduleCatLeftHomologyData.π (S.moduleCatCyclesIso.hom x) := by
    have heq := congrArg (fun z => S.moduleCatHomologyIso.hom z) hy
    change (S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π) (f y) =
      (S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π) x
    rwa [← S.π_moduleCatCyclesIso_hom]
  have hrange : S.moduleCatCyclesIso.hom (x - f y) ∈
      LinearMap.range S.moduleCatToCycles := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change S.moduleCatLeftHomologyData.π
      (S.moduleCatCyclesIso.hom (x - f y)) = 0
    simp only [map_sub, sub_eq_zero]
    exact hq.symm
  obtain ⟨z, hz⟩ := hrange
  have hdiff : x - f y = S.toCycles z := by
    apply (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).mp inferInstance
    rw [map_sub]
    change S.moduleCatCyclesIso.hom x - S.moduleCatCyclesIso.hom (f y) =
      (S.toCycles ≫ S.moduleCatCyclesIso.hom) z
    rw [S.toCycles_moduleCatCyclesIso_hom]
    change S.moduleCatCyclesIso.hom.hom x - S.moduleCatCyclesIso.hom.hom (f y) =
      S.moduleCatToCycles z
    change S.moduleCatToCycles z = S.moduleCatCyclesIso.hom.hom (x - f y) at hz
    rw [map_sub] at hz
    simpa [ShortComplex.moduleCatLeftHomologyData] using hz.symm
  obtain ⟨y', hy'⟩ := hbound z
  refine ⟨y + y', ?_⟩
  rw [map_add, hy', ← hdiff]
  abel

/-- The lifting condition of `CohomologyBaseChangeSurjective` produces a surjection from the base
change of the cocycles onto the cocycles of the base change. -/
private lemma surjective_baseChange_cycles_of_homology_lifts
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    (hbase :
      let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
      let Pκ := residueFieldComplex.{u, v} p P
      ∀ x : Pκ.cycles i, ∃ y : F.obj (P.cycles i),
        ∃ hy : Pκ.d i (i + 1) (F.map (P.iCycles i) y) = 0,
          Pκ.homologyπ i
              (Pκ.cyclesMk (F.map (P.iCycles i) y) (i + 1) (by simp) hy) =
            Pκ.homologyπ i x) :
    let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
    let Pκ := residueFieldComplex.{u, v} p P
    ∃ m : F.obj (P.cycles i) ⟶ Pκ.cycles i,
      Function.Surjective m ∧ m ≫ Pκ.iCycles i = F.map (P.iCycles i) := by
  dsimp at hbase ⊢
  let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let Pκ : CochainComplex (ModuleCat.{max u v} p.ResidueField) ℤ :=
    residueFieldComplex.{u, v} p P
  have hk : F.map (P.iCycles i) ≫ Pκ.d i (i + 1) = 0 := by
    change F.map (P.iCycles i) ≫ F.map (P.d i (i + 1)) = 0
    rw [← F.map_comp, P.iCycles_d]
    simp
  let m : F.obj (P.cycles i) ⟶ Pκ.cycles i :=
    Pκ.liftCycles (F.map (P.iCycles i)) (i + 1) (by simp) hk
  refine ⟨m, ?_, ?_⟩
  · apply surjective_cycles_of_homology_lifts (Pκ.sc i) m
    · intro z
      let j := (ComplexShape.up ℤ).prev i
      refine ⟨F.map (P.toCycles j i) z, ?_⟩
      have hmap : F.map (P.toCycles j i) ≫ m = Pκ.toCycles j i := by
        apply (cancel_mono (Pκ.iCycles i)).mp
        rw [Category.assoc, Pκ.liftCycles_i, Pκ.toCycles_i]
        change F.map (P.toCycles j i) ≫ F.map (P.iCycles i) = F.map (P.d j i)
        rw [← F.map_comp, P.toCycles_i]
      have hto : Pκ.toCycles j i = (Pκ.sc i).toCycles := by
        apply (cancel_mono (Pκ.iCycles i)).mp
        rw [Pκ.toCycles_i]
        exact (Pκ.sc i).toCycles_i.symm
      rw [hto] at hmap
      change (F.map (P.toCycles j i) ≫ m).hom z = ((Pκ.sc i).toCycles).hom z
      exact congrArg (fun q : F.obj (P.X j) ⟶ Pκ.cycles i => q.hom z) hmap
    · intro x
      change ∃ y, Pκ.homologyπ i (m y) = Pκ.homologyπ i x
      obtain ⟨y, hy, hclass⟩ := hbase x
      refine ⟨y, ?_⟩
      have hm : m y = Pκ.cyclesMk (F.map (P.iCycles i) y) (i + 1) (by simp) hy := by
        apply (ModuleCat.mono_iff_injective (Pκ.iCycles i)).mp inferInstance
        have hmk : Pκ.iCycles i
            (Pκ.cyclesMk (F.map (P.iCycles i) y) (i + 1) (by simp) hy) =
            F.map (P.iCycles i) y := Pκ.i_cyclesMk _ _ _ _
        rw [hmk]
        exact congrArg (fun q : F.obj (P.cycles i) ⟶ Pκ.X i => q.hom y)
          (Pκ.liftCycles_i (F.map (P.iCycles i)) (i + 1) (by simp) hk)
      rwa [hm]
  · exact Pκ.liftCycles_i (F.map (P.iCycles i)) (i + 1) (by simp) hk

/-- The inclusion of the image of `d` stays injective after base change when the tensored complex
stays exact. -/
private lemma baseChange_range_subtype_injective
    {R : Type u} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    {L M N : Type*} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (k : L →ₗ[R] M) (d : M →ₗ[R] N) (hex : Function.Exact k d)
    (hbase : Function.Exact (k.lTensor S) (d.lTensor S)) :
    Function.Injective (LinearMap.baseChange S d.range.subtype) := by
  have hex' : Function.Exact k d.rangeRestrict := by
    intro m
    simpa only [LinearMap.codRestrict_apply, Subtype.ext_iff, ZeroMemClass.coe_zero]
      using hex m
  have hsurj := LinearMap.lTensor_surjective S d.surjective_rangeRestrict
  have ht := lTensor_exact S hex' d.surjective_rangeRestrict
  rw [LinearMap.baseChange_eq_lTensor, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : d.lTensor S y = 0 := by
    change (d.range.subtype.lTensor S ∘ₗ d.rangeRestrict.lTensor S) y = 0 at hx
    rwa [← LinearMap.lTensor_comp] at hx
  exact (ht y).mpr ((hbase y).mp hy)

/-- A finitely presented cokernel whose presenting map stays injective over `κ(p)` becomes free
after localizing away from a suitable element outside `p`. -/
private lemma exists_free_baseChange_of_fiber_injective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {M N W : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup W] [Module R W]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    [Module.FinitePresentation R W]
    (d : M →ₗ[R] N) (q : N →ₗ[R] W) (hq : Function.Surjective q) (hex : Function.Exact d q)
    (hfib : Function.Injective (LinearMap.baseChange p.ResidueField d)) :
    ∃ f : R, f ∉ p ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[R] W) := by
  let A := Localization.AtPrime p
  have hqA : Function.Surjective (LinearMap.baseChange A q) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective A hq
  have hexA : Function.Exact (LinearMap.baseChange A d) (LinearMap.baseChange A q) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact A hex hq
  have : Module.Free A (A ⊗[R] W) :=
    Module.free_of_lTensor_residueField_injective
      (LinearMap.baseChange A d) (LinearMap.baseChange A q) hqA hexA
      (lTensor_residueField_localization_injective p d
        (by simpa only [LinearMap.baseChange_eq_lTensor] using hfib))
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl ((TensorProduct.mk R A W) 1) A
  refine ⟨f, hf, ?_⟩
  let := hfree
  exact Module.Free.of_equiv
    ((IsLocalizedModule.iso (Submonoid.powers f)
      ((TensorProduct.mk R (Localization.Away f) W) 1)).extendScalarsOfIsLocalization
        (Submonoid.powers f) (Localization.Away f))

/-- If the base change to `κ(p)` of the degree-`i` cycles of `P` surjects onto the degree-`i`
cycles of `residueFieldComplex p P`, compatibly with the inclusions into the degree-`i` terms, then
the degree-`i + 1` opcycles of `P` become free after localizing away from some `f ∉ p`. -/
private lemma exists_free_localized_opcycles
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    [Module.Finite R (P.X i)] [Module.Finite R (P.X (i + 1))]
    [Module.Free R (P.X (i + 1))]
    (m : (ModuleCat.extendScalars (algebraMap R p.ResidueField)).obj (P.cycles i) ⟶
      (residueFieldComplex.{u, v} p P).cycles i)
    (hm : Function.Surjective m)
    (hcomm : m ≫ (residueFieldComplex.{u, v} p P).iCycles i =
      (ModuleCat.extendScalars (algebraMap R p.ResidueField)).map (P.iCycles i)) :
    ∃ f : R, f ∉ p ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[R] (P.opcycles (i + 1))) := by
  let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
  let Pκ : CochainComplex (ModuleCat.{max u v} p.ResidueField) ℤ :=
    residueFieldComplex.{u, v} p P
  let d := (P.d i (i + 1)).hom
  let q := (P.pOpcycles (i + 1)).hom
  have hex : Function.Exact (P.iCycles i).hom d := by
    intro x
    constructor
    · intro hx
      exact ⟨P.cyclesMk x (i + 1) (by simp) hx, P.i_cyclesMk _ _ _ _⟩
    · rintro ⟨y, rfl⟩
      exact congrArg (fun a : P.cycles i ⟶ P.X (i + 1) => a.hom y)
        (P.iCycles_d i (i + 1))
  have hexκ : Function.Exact (F.map (P.iCycles i)).hom (F.map (P.d i (i + 1))).hom := by
    intro x
    constructor
    · intro hx
      let z := Pκ.cyclesMk x (i + 1) (by simp) hx
      obtain ⟨y, hy⟩ := hm z
      refine ⟨y, ?_⟩
      have he : (F.map (P.iCycles i)).hom y = (Pκ.iCycles i).hom z := by
        rw [← hcomm]
        change (Pκ.iCycles i).hom (m y) = _
        rw [hy]
      exact he.trans (Pκ.i_cyclesMk _ _ _ _)
    · rintro ⟨y, rfl⟩
      have hz : F.map (P.iCycles i) ≫ F.map (P.d i (i + 1)) = 0 := by
        rw [← F.map_comp, P.iCycles_d, F.map_zero]
      exact congrArg (fun a : F.obj (P.cycles i) ⟶ F.obj (P.X (i + 1)) => a.hom y) hz
  have hxt : Function.Exact ((P.iCycles i).hom.lTensor p.ResidueField)
      (d.lTensor p.ResidueField) := by
    change (let := (algebraMap R p.ResidueField).toAlgebra;
      Function.Exact (LinearMap.baseChange p.ResidueField (P.iCycles i).hom)
        (LinearMap.baseChange p.ResidueField d)) at hexκ
    rw [toAlgebra_algebraMap] at hexκ
    simpa only [LinearMap.baseChange_eq_lTensor] using hexκ
  have hq : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (P.pOpcycles (i + 1))).mp inferInstance
  have hdq : Function.Exact d q := exact_d_pOpcycles P i (i + 1) rfl
  have : Module.Finite R d.range := Module.Finite.range d
  have : Module.FinitePresentation R (P.opcycles (i + 1)) :=
    Module.finitePresentation_of_free_of_surjective q hq
      (by
        rw [hdq.linearMap_ker_eq, LinearMap.range_eq_map]
        exact Module.Finite.fg_top.map d)
  have hincq : Function.Exact d.range.subtype q := fun x =>
    (hdq x).trans ⟨fun ⟨y, hy⟩ => ⟨⟨x, y, hy⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩
  exact exists_free_baseChange_of_fiber_injective p d.range.subtype q hq hincq
    (baseChange_range_subtype_injective p.ResidueField (P.iCycles i).hom d hex hxt)

/-- If `τ_{≥ i+1}(K ⊗_R R_f)` is represented by a bounded complex of finite projective modules in
degrees `≥ i + 1`, then it is perfect with Tor amplitude in `[i + 1, ∞]`, and `K ⊗_R R_f` is
uniquely the direct sum of `τ_{≤ i}` and `τ_{≥ i+1}` compatibly with the truncation maps. -/
private lemma conclusion_of_upper_projective_representative
    {R : Type u} [CommRing R] (f : R) (K : DerivedCategory (ModuleCat.{max u v} R))
    (i b : ℤ)
    (P : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ)
    (hGE : P.IsStrictlyGE (i + 1)) (hLE : P.IsStrictlyLE b)
    (hFinite : ∀ j : ℤ, Module.Finite (Localization.Away f) (P.X j))
    (hProjective : ∀ j : ℤ, Module.Projective (Localization.Away f) (P.X j))
    (e : (DerivedCategory.TStructure.t.truncGE (i + 1)).obj
          ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K) ≅
        DerivedCategory.Q.obj P) :
    let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
    let upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
    let lower := (DerivedCategory.TStructure.t.truncLE i).obj Kf
    IsPerfect upper ∧
      (∃ (P' : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ) (b' : ℤ),
        P'.IsStrictlyGE (i + 1) ∧ P'.IsStrictlyLE b' ∧
          (∀ j : ℤ, Module.Finite (Localization.Away f) (P'.X j)) ∧
          (∀ j : ℤ, Module.Projective (Localization.Away f) (P'.X j)) ∧
          Nonempty (upper ≅ DerivedCategory.Q.obj P') ∧
          ∀ (M : ModuleCat.{max u v} (Localization.Away f)) (j : ℤ), j < i + 1 →
            IsZero ((TorAmplitude.tensorComplex P' M).homology j)) ∧
      ∃! e' : Kf ≅ lower ⊞ upper,
        (DerivedCategory.TStructure.t.truncLEι i).app Kf ≫ e'.hom = biprod.inl ∧
          (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app Kf = e'.hom ≫ biprod.snd := by
  dsimp
  let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
  let upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
  let lower := (DerivedCategory.TStructure.t.truncLE i).obj Kf
  have hAmp : HasProjectiveAmplitude.{u, v} upper (i + 1) b :=
    ⟨P, ⟨e.symm⟩, hProjective, hGE, hLE⟩
  have hLower : ∀ j : ℤ, i + 1 ≤ j →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (Localization.Away f)) j).obj lower) := fun j hj =>
    DerivedCategory.isZero_of_isLE lower i j (by omega)
  exact ⟨⟨P, i + 1, b, hGE, hLE, hFinite, hProjective, ⟨e⟩⟩,
    ⟨P, b, hGE, hLE, hFinite, hProjective, ⟨e⟩,
      isZero_tensorComplex_homology_of_isStrictlyGE P (i + 1) hGE⟩,
    (hom_eq_zero_and_existsUnique_iso_biprod lower upper (i + 1) b hAmp).2.2 hLower Kf
      ((DerivedCategory.TStructure.t.truncLEι i).app Kf)
      ((DerivedCategory.TStructure.t.truncGEπ (i + 1)).app Kf)
      ((DerivedCategory.TStructure.t.truncGEδLE i (i + 1) rfl).app Kf)
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished i (i + 1) rfl Kf)⟩

/-! ### Splitting from surjectivity of the base-change map -/

/-- Let `R` be a ring, `p ⊂ R` a prime and `K` a pseudo-coherent object of
`D(R)`. If for some `i ∈ ℤ` the map `H^i(K) ⊗_R κ(p) → H^i(K ⊗_R^L κ(p))` is surjective, then
there is `f ∈ R`, `f ∉ p`, such that `τ_{≥ i+1}(K ⊗_R R_f)` is a perfect object of `D(R_f)` with
Tor amplitude in `[i + 1, ∞]`, together with a canonical isomorphism
`K ⊗_R R_f ≅ τ_{≤ i}(K ⊗_R R_f) ⊕ τ_{≥ i+1}(K ⊗_R R_f)` in `D(R_f)`. -/
@[stacks 0A1U]
theorem exists_localization_perfect_truncGE_and_iso_biprod
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (_hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hbase : CohomologyBaseChangeSurjective.{u, v} p K i) :
    ∃ f : R, f ∉ p ∧
      let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
      let upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
      let lower := (DerivedCategory.TStructure.t.truncLE i).obj Kf
      IsPerfect upper ∧
        (∃ (P : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ) (b : ℤ),
          P.IsStrictlyGE (i + 1) ∧ P.IsStrictlyLE b ∧
            (∀ j : ℤ, Module.Finite (Localization.Away f) (P.X j)) ∧
            (∀ j : ℤ, Module.Projective (Localization.Away f) (P.X j)) ∧
            Nonempty (upper ≅ DerivedCategory.Q.obj P) ∧
            ∀ (M : ModuleCat.{max u v} (Localization.Away f)) (j : ℤ), j < i + 1 →
              IsZero ((TorAmplitude.tensorComplex P M).homology j)) ∧
        ∃! e : Kf ≅ lower ⊞ upper,
          (DerivedCategory.TStructure.t.truncLEι i).app Kf ≫ e.hom = biprod.inl ∧
            (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app Kf = e.hom ≫ biprod.snd := by
  obtain ⟨P, hP, ⟨eP⟩, hbase⟩ := hbase
  obtain ⟨b, hb⟩ := hP.upperBound
  have hFinite (j : ℤ) : Module.Finite R (P.X j) := (hP.finiteFree j).1
  have hFree (j : ℤ) : Module.Free R (P.X j) := (hP.finiteFree j).2
  obtain ⟨m, hm, hcomm⟩ := surjective_baseChange_cycles_of_homology_lifts p P i hbase
  obtain ⟨f, hf, hOp⟩ := exists_free_localized_opcycles p P i m hm hcomm
  have hOpProj : Module.Projective (Localization.Away f)
      (Localization.Away f ⊗[R] (P.opcycles (i + 1))) := by
    have := hOp
    exact Module.Projective.of_free
  obtain ⟨Q, hGE, hLE, hFin, hProj, ⟨eQ⟩⟩ :=
    localized_upper_representative f P (i + 1) b hb hFinite hFree hOpProj
  exact ⟨f, hf, conclusion_of_upper_projective_representative f K i (max (i + 1) b)
    Q hGE hLE hFin hProj <| (DerivedCategory.TStructure.t.truncGE (i + 1)).mapIso
    ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).mapIso eP.symm) ≪≫ eQ⟩

/-! ### Combining two principal neighbourhoods -/

/-- The product of two elements outside a prime is outside it, and both become units after
localizing away from the product. -/
lemma common_principal_refinement
    {R : Type u} [CommRing R] (prime : Ideal R) [prime.IsPrime]
    (first second : R) (hfirst : first ∉ prime) (hsecond : second ∉ prime) :
    first * second ∉ prime ∧
      IsUnit (algebraMap R (Localization.Away (first * second)) first) ∧
      IsUnit (algebraMap R (Localization.Away (first * second)) second) := by
  refine ⟨fun h => (Ideal.IsPrime.mem_or_mem (I := prime) inferInstance h).elim hfirst hsecond,
    ?_⟩
  have hprod : IsUnit (algebraMap R (Localization.Away (first * second)) (first * second)) :=
    IsLocalization.map_units (Localization.Away (first * second))
      ⟨first * second, Submonoid.mem_powers _⟩
  rw [map_mul] at hprod
  exact IsUnit.mul_iff.mp hprod

/-- `K` is represented by a bounded complex of finite projective modules concentrated in degrees
`≥ a`. -/
abbrev HasFiniteProjectiveRepresentative
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ j, Module.Finite R (P.X j)) ∧
      (∀ j, Module.Projective R (P.X j)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj P)

/-- If the degree-`(n - 1)` base-change map of `K` is surjective, then for some `f ∉ p` the
truncation `τ_{≥ n}(K ⊗_R R_f)` has a bounded finite projective representative in degrees `≥ n`.
-/
private lemma exists_upper_representative
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (n : ℤ)
    (hbase : CohomologyBaseChangeSurjective.{u, v} p K (n - 1)) :
    ∃ f : R, f ∉ p ∧ HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE n).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K)) n := by
  obtain ⟨f, hf, _, ⟨P, b, hGE, hLE, hFin, hProj, e, _⟩, _⟩ :=
    exists_localization_perfect_truncGE_and_iso_biprod p K hK (n - 1) hbase
  refine ⟨f, hf, P, b, ?_, hLE, hFin, hProj, ?_⟩
  · simpa only [sub_add_cancel] using hGE
  · simpa only [sub_add_cancel] using e

/-- Transport of `HasFiniteProjectiveRepresentative` along an isomorphism. -/
lemma hasFiniteProjectiveRepresentative_of_iso
    {R : Type u} [CommRing R] {K L : DerivedCategory (ModuleCat.{max u v} R)}
    {a : ℤ} (e : K ≅ L) (hL : HasFiniteProjectiveRepresentative.{u, v} L a) :
    HasFiniteProjectiveRepresentative.{u, v} K a := by
  obtain ⟨P, b, hGE, hLE, hFin, hProj, ⟨eP⟩⟩ := hL
  exact ⟨P, b, hGE, hLE, hFin, hProj, ⟨e ≪≫ eP⟩⟩

/-- An exact functor sends a derived-category object represented by `P` to the one represented by
`F P`. -/
private lemma nonempty_mapDerivedCategory_iso_Q_obj
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : DerivedCategory C} {P : CochainComplex C ℤ} (e : K ≅ DerivedCategory.Q.obj P) :
    Nonempty (F.mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P⟩

section ExactFunctor

variable {C D E : Type*} [Category C] [Abelian C]
  [Category D] [Abelian D] [Category E] [Abelian E]

/-- An exact functor preserves upper cohomological cutoffs. -/
private lemma mapDerivedCategory_isLE (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n := by
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K n
  let := hP
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj P) n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact F.map_isZero ((P.isStrictlyLE_iff n).mp hP j hj)
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).IsLE n :=
    inferInstance
  obtain ⟨e'⟩ := nonempty_mapDerivedCategory_iso_Q_obj F e
  exact DerivedCategory.TStructure.t.isLE_of_iso e'.symm n

/-- An exact functor preserves lower cohomological cutoffs. -/
private lemma mapDerivedCategory_isGE (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n := by
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K n
  let := hP
  have : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj P) n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact F.map_isZero ((P.isStrictlyGE_iff n).mp hP j hj)
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).IsGE n :=
    inferInstance
  obtain ⟨e'⟩ := nonempty_mapDerivedCategory_iso_Q_obj F e
  exact DerivedCategory.TStructure.t.isGE_of_iso e'.symm n

/-- An exact functor commutes with the canonical lower truncation. -/
private lemma mapDerivedCategory_truncGE_iso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) :
    Nonempty ((DerivedCategory.TStructure.t.truncGE n).obj (F.mapDerivedCategory.obj K) ≅
      F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE n).obj K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let t' := DerivedCategory.TStructure.t (C := D)
  have hLE := mapDerivedCategory_isLE F ((t.truncLE (n - 1)).obj K) (n - 1)
  have hGE := mapDerivedCategory_isGE F ((t.truncGE n).obj K) n
  obtain ⟨e, _⟩ := t'.triangle_iso_exists
    (t'.triangleLEGE_distinguished (n - 1) n (by omega) (F.mapDerivedCategory.obj K))
    (F.mapDerivedCategory.map_distinguished _
      (t.triangleLEGE_distinguished (n - 1) n (by omega) K))
    (Iso.refl _) (n - 1) n
    (by
      change ((t'.truncLE (n - 1)).obj (F.mapDerivedCategory.obj K)).IsLE (n - 1)
      infer_instance)
    (by
      change ((t'.truncGE n).obj (F.mapDerivedCategory.obj K)).IsGE n
      infer_instance) hLE hGE
  exact ⟨CategoryTheory.Pretriangulated.Triangle.π₃.mapIso e⟩

/-- For exact functors with `F ⋙ G ≅ H`, the induced functors on derived categories satisfy
`G(F(K)) ≅ H(K)`. -/
private lemma mapDerivedCategory_comp_obj_iso
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (K : DerivedCategory C) :
    Nonempty (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
      H.mapDerivedCategory.obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact ⟨(F.mapDerivedCategory ⋙ G.mapDerivedCategory).mapIso eK.symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).app P) ≪≫
    (H.mapDerivedCategoryFactors.app P).symm ≪≫ H.mapDerivedCategory.mapIso eK⟩

end ExactFunctor

/-- A flat extension of scalars preserves bounded finite projective representatives. -/
private lemma map_hasFiniteProjectiveRepresentative
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ)
    (hK : HasFiniteProjectiveRepresentative.{u, v} K a) :
    let F := ModuleCat.extendScalars (algebraMap R S)
    letI : F.Additive := extendScalars_additive.{u, u, max v u} _
    letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
    letI : PreservesFiniteColimits F := inferInstance
    HasFiniteProjectiveRepresentative.{u, v} (F.mapDerivedCategory.obj K) a := by
  dsimp only
  let F := ModuleCat.extendScalars (algebraMap R S)
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : PreservesFiniteColimits F := inferInstance
  obtain ⟨P, b, hGE, hLE, hFin, hProj, ⟨e⟩⟩ := hK
  let := hGE
  let := hLE
  let (j : ℤ) := hFin j
  let (j : ℤ) := hProj j
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj P, b, inferInstance, inferInstance,
    ?_, ?_, nonempty_mapDerivedCategory_iso_Q_obj F e⟩
  · intro j
    exact Module.Finite.equiv
      (PseudoCoherence.extendScalarsTensorIso (S := S) (P.X j)).toLinearEquiv.symm
  · intro j
    exact Module.Projective.of_equiv
      (PseudoCoherence.extendScalarsTensorIso (S := S) (P.X j)).toLinearEquiv.symm

/-- A bounded finite projective representative of the upper truncation over `R_f` transports to
`R_g` whenever `f` becomes a unit in `R_g`. -/
lemma upper_representative_after_localization
    {R : Type u} [CommRing R] (f g : R)
    (hunit : IsUnit (algebraMap R (Localization.Away g) f))
    (K : DerivedCategory (ModuleCat.{max u v} R)) (n : ℤ)
    (hK : HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE n).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K)) n) :
    HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE n).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K)) n := by
  let S := Localization.Away f
  let T := Localization.Away g
  let φ : S →+* T := IsLocalization.Away.lift f hunit
  let : Algebra S T := φ.toAlgebra
  have hcomp : (algebraMap S T).comp (algebraMap R S) = algebraMap R T :=
    IsLocalization.Away.lift_comp f hunit
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun x =>
    (RingHom.congr_fun hcomp x).symm)
  let : Module.Flat R T := IsLocalization.flat T (Submonoid.powers g)
  let : Module.Flat S T :=
    (Module.flat_iff_of_isLocalization S (Submonoid.powers f) T).mpr inferInstance
  let F := ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)
  let G := ModuleCat.extendScalars.{u, u, max u v} (algebraMap S T)
  let H := ModuleCat.extendScalars.{u, u, max u v} (algebraMap R T)
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let : G.Additive := extendScalars_additive.{u, u, max v u} _
  let : H.Additive := extendScalars_additive.{u, u, max v u} _
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers f)))
  let : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : PreservesFiniteLimits H := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : PreservesFiniteColimits F := inferInstance
  let : PreservesFiniteColimits G := inferInstance
  let : PreservesFiniteColimits H := inferInstance
  have eFG : F ⋙ G ≅ H := (ModuleCat.extendScalarsComp _ _).symm ≪≫
    eqToIso (congrArg (fun ψ : R →+* T => ModuleCat.extendScalars.{u, u, max u v} ψ) hcomp)
  obtain ⟨e⟩ := mapDerivedCategory_comp_obj_iso F G H eFG K
  obtain ⟨et⟩ := mapDerivedCategory_truncGE_iso G (F.mapDerivedCategory.obj K) n
  have hm := map_hasFiniteProjectiveRepresentative (S := T)
    ((DerivedCategory.TStructure.t.truncGE n).obj (F.mapDerivedCategory.obj K)) n hK
  exact hasFiniteProjectiveRepresentative_of_iso
    ((DerivedCategory.TStructure.t.truncGE n).mapIso e.symm ≪≫ et) hm

/-- If the base-change maps of `K` in degrees `i - 1` and `i` are surjective, then for a single
`f ∉ p` both `τ_{≥ i}(K ⊗_R R_f)` and `τ_{≥ i+1}(K ⊗_R R_f)` have bounded finite projective
representatives, in degrees `≥ i` and `≥ i + 1` respectively. -/
lemma exists_adjacent_upper_representatives
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hbase_i : CohomologyBaseChangeSurjective.{u, v} p K i)
    (hbase_prev : CohomologyBaseChangeSurjective.{u, v} p K (i - 1)) :
    ∃ f : R, f ∉ p ∧
      HasFiniteProjectiveRepresentative.{u, v} ((DerivedCategory.TStructure.t.truncGE i).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K)) i ∧
      HasFiniteProjectiveRepresentative.{u, v} ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K)) (i + 1) := by
  obtain ⟨f, hf, hfi⟩ := exists_upper_representative p K hK i hbase_prev
  obtain ⟨g, hg, hgi⟩ := exists_upper_representative p K hK (i + 1)
    (by simpa only [add_sub_cancel_right] using hbase_i)
  obtain ⟨hfg, huf, hug⟩ := common_principal_refinement p f g hf hg
  exact ⟨f * g, hfg,
    upper_representative_after_localization f (f * g) huf K i hfi,
    upper_representative_after_localization g (f * g) hug K (i + 1) hgi⟩

end StacksDraft.Perfect

end
