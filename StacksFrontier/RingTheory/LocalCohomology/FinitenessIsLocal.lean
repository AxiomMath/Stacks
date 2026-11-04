module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of local cohomology is a local property

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module. The local
cohomology modules `H^i_{V(I)}(M)` are finite for all `i ≤ n` if and only if every
localization `H^i_{V(I)}(M)_𝔭` at a prime `𝔭` is a finite `A_𝔭`-module for all `i ≤ n`.

The nontrivial direction is an induction on `n`. In degree zero the module `H^0_{V(I)}(M)`
is the `I`-power torsion submodule of `M`, hence finite. For the inductive step one may
replace `M` by `M / Γ_I(M)`, which changes no local cohomology module in positive degree and
on which some `f ∈ I` acts injectively; the short exact sequence `0 → M' → M' → M'/fM' → 0`
then reduces degree `n + 1` to degree `n` after one observes that the kernel of `f` on
`H^i_{V(I)}(M')` is finitely generated and that `f` lies in every associated prime of an
`I`-power torsion module.

## Main results

* `Stacks.LocalCohomology.localCohomology_finite_iff_localizations_finite` — finiteness of
  local cohomology through a fixed degree may be checked after localizing at every prime.

## Implementation notes

Local cohomology with support in `V(I)` is the right adjoint
`Dualizing.localCohomologyFunctor` of the inclusion of the `I`-power-torsion objects of the
derived category; `H^i_{V(I)}(M)` is the `i`-th homology of its value on `M` placed in degree
zero. Localization at a prime `𝔭` is `LocalizedModule 𝔭.primeCompl` over
`Localization.AtPrime 𝔭`.

## References

* [Stacks Project, Tag 0AW9](https://stacks.math.columbia.edu/tag/0AW9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- A module that is finite over some ring of scalars acting compatibly and is `I`-power
torsion over `A` is annihilated by a single power of `I`: take the supremum of the exponents
killing a finite generating family. -/
private theorem exists_pow_annihilator_of_finite_isIPowerTorsion {A S M : Type*}
    [CommRing A] [Semiring S] [AddCommGroup M] [Module S M] [Module A M]
    [SMulCommClass A S M] [Module.Finite S M] (I : Ideal A)
    (hT : IsIPowerTorsion A M I) :
    ∃ e : ℕ, I ^ e ≤ Module.annihilator A M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  choose en _ hkill using (fun j : Fin n => hT (g j))
  obtain ⟨e, hen⟩ := Finite.exists_le en
  refine ⟨e, fun a ha => Module.mem_annihilator.mpr fun x => ?_⟩
  have hx : x ∈ Submodule.span S (Set.range g) := by
    rw [hg]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hkill j a (Ideal.pow_le_pow_right (hen j) ha)
  | zero => simp
  | add y z _ _ hy hz => simp [smul_add, hy, hz]
  | smul c y _ hy =>
      rw [smul_comm a c y, hy, smul_zero]

/-- Localizing an `I`-power torsion module at a multiplicative set leaves it `I`-power
torsion. -/
private theorem isIPowerTorsion_localized {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (S : Submonoid A) (I : Ideal A) (hT : IsIPowerTorsion A M I) :
    IsIPowerTorsion A (LocalizedModule S M) I := by
  intro x
  obtain ⟨⟨m, s⟩, hx⟩ :=
    IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  obtain ⟨e, he, hkill⟩ := hT m
  refine ⟨e, he, fun a ha => ?_⟩
  rw [← hx]
  show a • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m s = 0
  rw [← IsLocalizedModule.mk'_smul, hkill a ha]
  simp

/-- Every associated prime of an `I`-power torsion module contains `I`. -/
private theorem ideal_le_associatedPrime_of_isIPowerTorsion {A M : Type*}
    [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A)
    (hT : IsIPowerTorsion A M I) (p : associatedPrimes A M) : I ≤ p.val := by
  intro a ha
  obtain ⟨hp, x, hx⟩ := p.property
  obtain ⟨e, _, hkill⟩ := hT x
  apply hp.mem_of_pow_mem e
  rw [hx]
  apply Ideal.le_radical
  rw [Submodule.mem_colon]
  rintro _ rfl
  rw [Submodule.mem_bot]
  exact hkill (a ^ e) (Ideal.pow_mem_pow ha e)

/-- A finite module over a Noetherian ring whose `I`-power torsion submodule vanishes admits
an element of `I` acting injectively: no associated prime of the module contains `I`. -/
private theorem exists_regular_element_of_primaryComponent_eq_bot {A M : Type*}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hT : Ideal.primaryComponent M I = ⊥) :
    ∃ f ∈ I, ∀ x : M, f • x = 0 → x = 0 := by
  classical
  have hI_not_le (p : Ideal A) (hp : p ∈ associatedPrimes A M) : ¬ I ≤ p := by
    intro hIp
    obtain ⟨hp, x, hx⟩ := (isAssociatedPrime_iff (I := p) (M := M)).mp hp
    have hxT : x ∈ Ideal.primaryComponent M I := by
      rw [Ideal.primaryComponent_mem]
      refine ⟨1, ?_⟩
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have hpa : (a : A) ∈ p := hIp (by simpa using a.property)
      rw [hx, Submodule.mem_colon] at hpa
      simpa using hpa x (by simp)
    have hx0 : x = 0 := by simpa [hT] using hxT
    have hxBot : (⊥ : Submodule A M).colon {x} = ⊤ := by
      simp [hx0]
    exact hp.ne_top (hx.trans hxBot)
  obtain ⟨f, hf, hreg⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le I M
      (associatedPrimes.finite A M)).mpr
      hI_not_le
  exact ⟨f, hf, fun x hx => hreg.right_eq_zero_of_smul hx⟩

/-- Having `I`-power torsion cohomology is invariant under isomorphism in the derived
category. -/
public theorem derivedPowerTorsionProperty_closedUnderIso (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, v} A I hI).IsClosedUnderIsomorphisms where
  of_iso e h i := (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e) (h i)

/-- The objects of `D(A)` with `I`-power torsion cohomology form a triangulated
subcategory. -/
public theorem derivedPowerTorsionProperty_triangulated (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, v} A I hI).IsTriangulated := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let S := Dualizing.powerTorsionModuleProperty.{u, v} A I hI
  let : P.IsClosedUnderIsomorphisms := derivedPowerTorsionProperty_closedUnderIso A I hI
  let : P.ContainsZero := ⟨⟨0, isZero_zero _, fun i =>
    S.prop_of_isZero ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))⟩⟩
  let : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun X hX i =>
    S.prop_of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).shiftIso
      n i (n + i) rfl).app X).symm (hX (n + i))⟩⟩
  let : P.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ i =>
    S.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i))
  exact {}

/-- The `i`-th local cohomology module with support in `V(I)` of a module placed in degree
zero, as a functor `ModuleCat A ⥤ ModuleCat A`. -/
private noncomputable abbrev derivedSupportCohomology (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (i : ℤ) : ModuleCat.{v} A ⥤ ModuleCat.{v} A :=
  DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
    Dualizing.localCohomologyFunctor A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι ⋙ DerivedCategory.homologyFunctor _ i

/-- A short exact sequence of `A`-modules induces the usual long exact sequence of local
cohomology modules with support in `V(I)`; this records the three exactness statements
around a fixed degree `i` together with the connecting maps. -/
private theorem localCohomology_homology_exact_sequences (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (S : ShortComplex (ModuleCat.{v} A))
    (hS : S.ShortExact) (i : ℤ) :
    let Eprev := derivedSupportCohomology A I hI (i - 1)
    let Ecurr := derivedSupportCohomology A I hI i
    let Enext := derivedSupportCohomology A I hI (i + 1)
    ∃ δprev : Eprev.obj S.X₃ ⟶ Ecurr.obj S.X₁,
      ∃ hprev : δprev ≫ Ecurr.map S.f = 0,
        (ShortComplex.mk δprev (Ecurr.map S.f) hprev).Exact ∧
      ∃ hcurr : Ecurr.map S.f ≫ Ecurr.map S.g = 0,
        (ShortComplex.mk (Ecurr.map S.f) (Ecurr.map S.g) hcurr).Exact ∧
      ∃ δnext : Ecurr.obj S.X₃ ⟶ Enext.obj S.X₁,
        ∃ hnext : Ecurr.map S.g ≫ δnext = 0,
          (ShortComplex.mk (Ecurr.map S.g) δnext hnext).Exact := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let : P.IsClosedUnderIsomorphisms := derivedPowerTorsionProperty_closedUnderIso A I hI
  let : P.IsTriangulated := derivedPowerTorsionProperty_triangulated A I hI
  let adj := Dualizing.localCohomologyAdjunction.{u, v} A I hI
  let G := Dualizing.localCohomologyRightAdjoint.{u, v} A I hI |>.1
  let : P.ι.IsTriangulated := inferInstance
  let : P.ι.Additive := inferInstance
  let : P.ι.CommShift ℤ := inferInstance
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let : G.Additive := adj.right_adjoint_additive
  let F := G ⋙ P.ι
  let : F.CommShift ℤ := Functor.CommShift.comp _ _
  let : F.IsTriangulated := inferInstance
  let Sng := CochainComplex.singleFunctor (ModuleCat.{v} A) 0
  let : PreservesFiniteLimits Sng :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single _ (.up ℤ) 0))
  let : PreservesFiniteColimits Sng :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single _ (.up ℤ) 0))
  let : Mono S.f := ModuleCat.mono_iff_injective S.f |>.mpr hS.moduleCat_injective_f
  let : Epi S.g := ModuleCat.epi_iff_surjective S.g |>.mpr hS.moduleCat_surjective_g
  let S' := S.map Sng
  have hS' : S'.ShortExact := hS.map Sng
  let T := DerivedCategory.triangleOfSES hS'
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished T (DerivedCategory.triangleOfSES_distinguished hS')
  let T' := F.mapTriangle.obj T
  let Ecurr := derivedSupportCohomology.{u, v} A I hI i
  let Hcurr := DerivedCategory.homologyFunctor (ModuleCat.{v} A) i
  let : Hcurr.Additive := inferInstance
  let : Ecurr.Additive := by
    show (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙ F ⋙ Hcurr).Additive
    infer_instance
  let δprev := DerivedCategory.HomologySequence.δ T' (i - 1) i (by omega)
  let δnext := DerivedCategory.HomologySequence.δ T' i (i + 1) (by omega)
  have hcurr : Ecurr.map S.f ≫ Ecurr.map S.g = 0 := by
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  refine ⟨δprev, ?_, ?_, hcurr, ?_, δnext, ?_, ?_⟩
  · show δprev ≫ Hcurr.map T'.mor₁ = 0
    exact DerivedCategory.HomologySequence.δ_comp T' hT (i - 1) i (by omega)
  · convert DerivedCategory.HomologySequence.exact₁ T' hT (i - 1) i (by omega) using 1
    rfl
  · convert DerivedCategory.HomologySequence.exact₂ T' hT i using 1
    rfl
  · show Hcurr.map T'.mor₂ ≫ δnext = 0
    exact DerivedCategory.HomologySequence.comp_δ T' hT i (i + 1) (by omega)
  · convert DerivedCategory.HomologySequence.exact₃ T' hT i (i + 1) (by omega) using 1
    rfl

/-- An `I`-power torsion module over a Noetherian ring with finitely many associated primes
all of whose localizations at associated primes are finite is annihilated by a power of
`I`. -/
private theorem exists_pow_le_annihilator_of_finite_associatedPrimes_localizations
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (hAss : (associatedPrimes A M).Finite) (hT : IsIPowerTorsion A M I)
    (hfin : ∀ p : associatedPrimes A M, Module.Finite (Localization.AtPrime p.val)
      (LocalizedModule p.val.primeCompl M)) :
    ∃ e : ℕ, I ^ e ≤ Module.annihilator A M := by
  classical
  have := hAss.to_subtype
  choose ep hp using fun p : associatedPrimes A M => by
    let : p.val.IsPrime := p.property.isPrime
    let : Module.Finite (Localization.AtPrime p.val)
        (LocalizedModule p.val.primeCompl M) := hfin p
    exact exists_pow_annihilator_of_finite_isIPowerTorsion
      (S := Localization.AtPrime p.val) (M := LocalizedModule p.val.primeCompl M) I
      (isIPowerTorsion_localized p.val.primeCompl I hT)
  obtain ⟨e, he⟩ := Finite.exists_le ep
  have hkill (a : A) (ha : a ∈ I ^ e) (x : M) : a • x = 0 := by
    apply _root_.zero_at_ass_zero A M
    ext p
    let : p.val.IsPrime := p.property.isPrime
    show LocalizedModule.mkLinearMap p.val.primeCompl M (a • x) =
      LocalizedModule.mkLinearMap p.val.primeCompl M (0 : M)
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp (hp p (Ideal.pow_le_pow_right (he p) ha)) _
  exact ⟨e, fun a ha => Module.mem_annihilator.mpr (hkill a ha)⟩

/-- A zero module is `I`-power torsion. -/
private lemma torsion_of_isZero {A : Type u} [CommRing A] (I : Ideal A)
    (M : ModuleCat.{v} A) (h : IsZero M) : IsIPowerTorsion A M I :=
  fun x => ⟨1, by omega, fun a _ =>
    (ModuleCat.isZero_iff_subsingleton.mp h).elim _ _⟩

/-- An `I`-power torsion module placed in degree zero has `I`-power torsion cohomology. -/
private lemma torsion_single {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (hM : IsIPowerTorsion A M I) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro i
  by_cases hi : i = 0
  · subst i
    exact (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · exact torsion_of_isZero I _ (IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M i hi)
      ((DerivedCategory.homologyFunctorFactors _ i).app _))

/-- The `I`-power torsion submodule of `M / Γ_I(M)` vanishes. -/
public lemma primaryComponent_quotient_eq_bot (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (M : Type v) [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent (M ⧸ Ideal.primaryComponent M I) I = ⊥ := by
  let Q := M ⧸ Ideal.primaryComponent M I
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem Q I x).mp hx
  by_cases h : n = 0
  · subst n
    simpa using ((Submodule.mem_torsionBySet_iff _ _).mp hn) (1 : (I ^ 0 : Ideal A))
  · have hz := torsionBySet_pow_eq_bot I
      (torsionBySet_quotient_primaryComponent_eq_bot I hI M) n (Nat.one_le_iff_ne_zero.mpr h)
    rw [hz] at hn
    simpa using hn

/-- Truncation at level `n` does not change the homology in degrees `≤ n`. -/
public lemma isIso_homology_map_truncLEι {C : Type*} [Category C] [Abelian C]
    (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGT n).obj X
  have hT := t.triangleLEGT_distinguished n X
  have : T.obj₃.IsGE (n + 1) := t.isGE_truncGT_obj X n (n + 1)
  have hz (j : ℤ) (hj : j ≤ n) : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) j (by omega)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      ((hz (i - 1) (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
      ((hz i hi).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₁)

/-- An object of `D(C)` concentrated in degrees `≥ 0` receives a map from an object of `C`
placed in degree zero which is an isomorphism on `H^0` and corepresents maps out of objects
of `C`. -/
public lemma exists_single_approximation
    {C : Type*} [Category C] [Abelian C] (X : DerivedCategory C) [X.IsGE 0] :
    ∃ (B : C) (b : (DerivedCategory.singleFunctor C 0).obj B ⟶ X),
      IsIso ((DerivedCategory.homologyFunctor C 0).map b) ∧
      ∀ T : C, Function.Bijective
        (fun f : T ⟶ B => (DerivedCategory.singleFunctor C 0).map f ≫ b) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let L := (t.truncLE 0).obj X
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0
  let b := e.inv ≫ (t.truncLEι 0).app X
  refine ⟨B, b, ?_, ?_⟩
  · have := isIso_homology_map_truncLEι X 0 0 le_rfl
    dsimp [b]
    rw [Functor.map_comp]
    infer_instance
  · refine fun T => ⟨fun f g h => ?_, fun f => ?_⟩
    · apply (DerivedCategory.singleFunctor C 0).map_injective
      apply (cancel_mono e.inv).1
      apply t.to_truncLE_obj_ext
      simpa [b, Category.assoc] using h
    · obtain ⟨g, hg⟩ := (DerivedCategory.singleFunctor C 0).map_surjective
        (t.liftTruncLE f 0 ≫ e.hom)
      exact ⟨g, by simp [hg, b]⟩

/-- Truncation preserves the property of having `I`-power torsion cohomology. -/
private lemma torsion_truncLE
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A))
    (hX : Dualizing.derivedPowerTorsionProperty A I hI X) (n : ℤ) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : i ≤ n
  · have := isIso_homology_map_truncLEι X n i hi
    exact (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)
  · exact torsion_of_isZero I _ (DerivedCategory.isZero_of_isLE _ n i (by omega))

/-- For a right adjoint `R` of the inclusion of a full subcategory `P`, composing with the
counit identifies maps from an object of `P` into `R.obj Y` with maps into `Y`. -/
private lemma inclusion_counit_bijective
    {C : Type*} [Category C] {P : ObjectProperty C} {R : C ⥤ P.FullSubcategory}
    (adj : P.ι ⊣ R) (X : P.FullSubcategory) (Y : C) :
    Function.Bijective (fun f : X.obj ⟶ (R.obj Y).obj => f ≫ adj.counit.app Y) := by
  constructor
  · intro f g h
    have hh : (adj.homEquiv X Y).symm (ObjectProperty.homMk f) =
        (adj.homEquiv X Y).symm (ObjectProperty.homMk g) := h
    exact congrArg (fun k => k.hom) ((adj.homEquiv X Y).symm.injective hh)
  · intro f
    exact ⟨((adj.homEquiv X Y) f).hom, (adj.homEquiv X Y).symm_apply_apply f⟩

/-- The adjunction between the inclusion of the `I`-power-torsion objects of `D(A)` and local
cohomology with support in `V(I)`, with the right adjoint named as
`Dualizing.localCohomologyFunctor`. -/
private def supportAdjunction (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, v} A I hI).ι ⊣
      Dualizing.localCohomologyFunctor.{u, v} A I hI :=
  Dualizing.localCohomologyAdjunction A I hI

/-- Local cohomology with support in `V(I)` does not lower the connectivity of its
argument. -/
private lemma localCohomology_isGE
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) [X.IsGE n] :
    ((Dualizing.localCohomologyFunctor A I hI).obj X).obj.IsGE n := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let Z := (Dualizing.localCohomologyFunctor A I hI).obj X
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  let L : P.FullSubcategory := ⟨(t.truncLE (n - 1)).obj Z.obj,
    torsion_truncLE I hI Z.obj Z.property (n - 1)⟩
  have he : (t.truncLEι (n - 1)).app Z.obj = 0 := by
    apply (inclusion_counit_bijective adj L X).1
    have hz := t.zero_of_isLE_of_isGE
      ((t.truncLEι (n - 1)).app Z.obj ≫ adj.counit.app X) (n - 1) n (by omega)
      (t.isLE_truncLE_obj Z.obj (n - 1) (n - 1)) (by exact ‹X.IsGE n›)
    exact hz.trans zero_comp.symm
  apply (t.isGE_iff_isZero_truncLE_obj (n - 1) n (by omega) Z.obj).2
  apply (IsZero.iff_id_eq_zero _).2
  apply t.to_truncLE_obj_ext
  simp [he]

/-- `H^0_{V(I)}(M)` is a finite module when `M` is: it is a submodule of `M`. -/
private theorem localCohomology_zero_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) [Module.Finite A M] :
    Module.Finite A ((derivedSupportCohomology A I hI 0).obj M) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{v} A) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0
  let s := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0
  let adj := supportAdjunction A I hI
  let Z := (Dualizing.localCohomologyFunctor A I hI).obj (S.obj M)
  have : Z.obj.IsGE 0 := localCohomology_isGE I hI (S.obj M) 0
  obtain ⟨B, b, hb, hb'⟩ := exists_single_approximation Z.obj
  have hB : IsIPowerTorsion A B I :=
    (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
      ((asIso (H.map b)).symm ≪≫ s.app B) (Z.property 0)
  let f : B ⟶ M := S.preimage (b ≫ adj.counit.app (S.obj M))
  have hf : S.map f = b ≫ adj.counit.app (S.obj M) := S.map_preimage _
  let K := LinearMap.ker f.hom
  let k : ModuleCat.of A K ⟶ B := ModuleCat.ofHom K.subtype
  have hK : IsIPowerTorsion A K I := by
    intro x
    obtain ⟨n, hn, hx⟩ := hB x.val
    exact ⟨n, hn, fun a ha => Subtype.ext (hx a ha)⟩
  let T : Dualizing.PowerTorsionDerivedCategory A I hI :=
    ⟨S.obj (ModuleCat.of A K), torsion_single I hI _ hK⟩
  have hkf : k ≫ f = 0 := by ext x; exact x.property
  have hkb : S.map k ≫ b = 0 := by
    apply (inclusion_counit_bijective adj T (S.obj M)).1
    dsimp only
    rw [Category.assoc, ← hf, ← S.map_comp, hkf, S.map_zero, zero_comp]
  have hk : k = 0 := (hb' (ModuleCat.of A K)).1 (by simpa using hkb)
  have hinj : Function.Injective f.hom := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    exact congrArg (fun q : ModuleCat.of A K ⟶ B => q ⟨x, hx⟩) hk
  have : Module.Finite A B := Module.Finite.of_injective f.hom hinj
  let e : H.obj Z.obj ≃ₗ[A] B :=
    ((asIso (H.map b)).symm ≪≫ s.app B).toLinearEquiv
  exact Module.Finite.equiv e.symm

/-- The higher local cohomology of an `I`-power torsion module vanishes. -/
private theorem localCohomology_torsion_higher
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (hM : IsIPowerTorsion A M I) (i : ℤ) (hi : 0 < i) :
    IsZero ((derivedSupportCohomology A I hI i).obj M) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{v} A) 0
  let P := Dualizing.derivedPowerTorsionProperty.{u, v} A I hI
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let X : P.FullSubcategory := ⟨S.obj M, torsion_single I hI M hM⟩
  have : IsIso (adj.counit.app X.obj) :=
    adj.isIso_counit_app_of_iso (Y := X) (Iso.refl X.obj)
  let e := asIso (adj.counit.app X.obj)
  exact (DerivedCategory.isZero_of_isLE (S.obj M) 0 i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e)

/-- Passing to `M / Γ_I(M)` does not change local cohomology in positive degrees. -/
private theorem localCohomology_quotient_torsion_map_isIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ) (hi : 0 < i) :
    IsIso ((derivedSupportCohomology A I hI i).map
      (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ)) := by
  let N := Ideal.primaryComponent M I
  let S : ShortComplex (ModuleCat.{v} A) :=
    ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by ext; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
  have hN : IsIPowerTorsion A N I := by
    intro x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp x.property
    exact ⟨n + 1, by omega, fun a ha => Subtype.ext ((Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a, Ideal.pow_le_pow_right n.le_succ ha⟩)⟩
  obtain ⟨δp, hp, ep, hc, ec, δn, hn, en⟩ :=
    localCohomology_homology_exact_sequences A I hI S hS i
  let E := derivedSupportCohomology A I hI i
  have hz := localCohomology_torsion_higher A I hI (ModuleCat.of A N) hN i hi
  have hz' := localCohomology_torsion_higher A I hI (ModuleCat.of A N) hN (i + 1) (by omega)
  have hinj : Function.Injective (E.map S.g).hom := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ :=
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp ec x).mp hx
    rw [← hy]
    exact congrArg (fun q => q y) (hz.eq_of_src (E.map S.f) 0)
  have hsurj : Function.Surjective (E.map S.g).hom := fun x =>
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp en x).mp
      (congrArg (fun q => q x) (hz'.eq_of_tgt δn 0))
  have : Mono (E.map S.g) := (ModuleCat.mono_iff_injective _).mpr hinj
  have : Epi (E.map S.g) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi (E.map S.g)

/-- Finiteness after localization is inherited by the middle term of an exact sequence. -/
private theorem finite_localized_of_exact
    {R X Y Z : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : Function.Exact f g)
    (S : Submonoid R)
    [Module.Finite (Localization S) (LocalizedModule S X)]
    [Module.Finite (Localization S) (LocalizedModule S Z)] :
    Module.Finite (Localization S) (LocalizedModule S Y) := by
  let f' := IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S X)
    (LocalizedModule.mkLinearMap S Y) (Localization S) f
  let g' := IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S Y)
    (LocalizedModule.mkLinearMap S Z) (Localization S) g
  have hexact : Function.Exact f' g' := LocalizedModule.map_exact S f g h
  have : IsNoetherian (Localization S) (LocalizedModule S Y) :=
    isNoetherian_of_range_eq_ker f' g' (LinearMap.exact_iff.mp hexact).symm
  exact ⟨IsNoetherian.noetherian _⟩

/-- If multiplication by `f` has finitely generated kernel on `M` and `f ^ n` annihilates
`M`, then `M` is a finite module. -/
private theorem finite_of_ker_smul_of_pow_smul_zero
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (f : R)
    (hker : (LinearMap.ker (f • (LinearMap.id : M →ₗ[R] M))).FG)
    (n : ℕ) (hn : ∀ x : M, f ^ n • x = 0) : Module.Finite R M := by
  have hfg (e : ℕ) : (LinearMap.ker (f ^ e • (LinearMap.id : M →ₗ[R] M))).FG := by
    induction e with
    | zero => simpa using (Submodule.fg_bot : (⊥ : Submodule R M).FG)
    | succ e ih =>
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (f • (LinearMap.id : M →ₗ[R] M))
      · apply ih.of_le
        rintro _ ⟨x, hx, rfl⟩
        show f ^ e • (f • x) = 0
        simpa [pow_succ, mul_smul] using hx
      · exact hker.of_le inf_le_right
  have heq : LinearMap.ker (f ^ n • (LinearMap.id : M →ₗ[R] M)) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_top, iff_true]
    exact hn x
  exact ⟨heq ▸ hfg n⟩

/-- An `I`-power torsion module over a Noetherian ring is finite as soon as some `f ∈ I` has
finitely generated kernel on it and all its localizations at primes are finite. -/
private theorem finite_of_ker_smul_of_localizations_finite
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hT : IsIPowerTorsion R M I) (f : R) (hf : f ∈ I)
    (hker : (LinearMap.ker (f • (LinearMap.id : M →ₗ[R] M))).FG)
    (hloc : ∀ p : PrimeSpectrum R,
      Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    Module.Finite R M := by
  let K := LinearMap.ker (f • (LinearMap.id : M →ₗ[R] M))
  have : Module.Finite R K := Module.Finite.of_fg hker
  have hass : associatedPrimes R M ⊆ associatedPrimes R K := by
    intro p hp
    obtain ⟨hpp, x, hx⟩ := (isAssociatedPrime_iff (I := p) (M := M)).mp hp
    have hf' : f ∈ p := ideal_le_associatedPrime_of_isIPowerTorsion I hT ⟨p, hp⟩ hf
    have hfx : f • x = 0 := by
      rw [hx, Submodule.mem_colon] at hf'
      exact hf' x (by simp)
    apply isAssociatedPrime_iff.mpr
    refine ⟨hpp, ⟨x, hfx⟩, ?_⟩
    rw [hx]
    ext a
    simp only [Submodule.mem_colon, Set.mem_singleton_iff, forall_eq,
      Submodule.mem_bot, Subtype.ext_iff]
    exact ⟨fun h s hs => by simpa [hs] using h, fun h => h ⟨x, hfx⟩ rfl⟩
  obtain ⟨e, he⟩ := exists_pow_le_annihilator_of_finite_associatedPrimes_localizations I
    ((associatedPrimes.finite R K).subset hass) hT
    (fun p => hloc ⟨p.val, p.property.isPrime⟩)
  exact finite_of_ker_smul_of_pow_smul_zero f hker e
    (Module.mem_annihilator.mp (he (Ideal.pow_mem_pow hf e)))

/-- Each local cohomology functor with support in `V(I)` is `A`-linear. -/
private theorem derivedSupportCohomology_linear
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (i : ℤ) :
    (derivedSupportCohomology.{u, v} A I hI i).Linear A := by
  have hF : (Dualizing.localCohomologyFunctor.{u, v} A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty.{u, v} A I hI).ι).Linear A := ⟨by
    intro X Y f a
    apply (inclusion_counit_bijective (supportAdjunction A I hI)
      ((Dualizing.localCohomologyFunctor A I hI).obj X) Y).1
    dsimp only
    rw [(supportAdjunction A I hI).counit.naturality, Linear.smul_comp,
      (supportAdjunction A I hI).counit.naturality, Functor.id_map, Functor.id_map,
      Linear.comp_smul]⟩
  have hH : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).Linear A := by
    let : Localization.Lifting DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ))
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (.up ℤ) i)
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i) :=
      ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i⟩
    apply (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ)) A
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (.up ℤ) i)
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i)).mp
    have : (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} A) (.up ℤ) i).Linear A :=
      ⟨fun f a => by ext <;> rfl⟩
    show ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} A) (.up ℤ) i) ⋙
      ShortComplex.homologyFunctor (ModuleCat.{v} A)).Linear A
    infer_instance
  show (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
    (Dualizing.localCohomologyFunctor.{u, v} A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty.{u, v} A I hI).ι) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).Linear A
  infer_instance

/-- The nontrivial implication of
`Stacks.LocalCohomology.localCohomology_finite_iff_localizations_finite`, by induction on the
degree `n` through which finiteness is asserted. -/
private theorem localCohomology_finite_of_localizations_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (n : ℕ) (M : ModuleCat.{v} A) [Module.Finite A M]
    (h : ∀ p : PrimeSpectrum A, ∀ i : ℕ, i ≤ n →
      Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl ((derivedSupportCohomology A I hI i).obj M))) :
    ∀ i : ℕ, i ≤ n → Module.Finite A ((derivedSupportCohomology A I hI i).obj M) := by
  induction n generalizing M with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
    exact localCohomology_zero_finite A I hI M
  | succ n ih =>
    let N := ModuleCat.of A (M ⧸ Ideal.primaryComponent M I)
    let E := fun i : ℤ => derivedSupportCohomology.{u, v} A I hI i
    have eQ (i : ℕ) (hi : 0 < i) : (E i).obj M ≅ (E i).obj N := by
      have := localCohomology_quotient_torsion_map_isIso A I hI M (i : ℤ) (by omega)
      exact asIso ((E i).map (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))
    have hN (p : PrimeSpectrum A) (i : ℕ) (hi : i ≤ n + 1) :
        Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl ((E i).obj N)) := by
      by_cases hi0 : i = 0
      · subst i
        have := localCohomology_zero_finite A I hI N
        exact Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl ((E 0).obj N))
      · have := h p i hi
        exact Module.Finite.equiv (IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl ((E i).obj M))
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl ((E i).obj N))
          (Localization.AtPrime p.asIdeal) (eQ i (by omega)).toLinearEquiv)
    have hNT : Ideal.primaryComponent N I = ⊥ :=
      primaryComponent_quotient_eq_bot A I hI M
    obtain ⟨f, hf, hreg⟩ := exists_regular_element_of_primaryComponent_eq_bot I hNT
    let μ : N ⟶ N := f • 𝟙 N
    let Q := ModuleCat.of A (N ⧸ LinearMap.range μ.hom)
    let q : N ⟶ Q := ModuleCat.ofHom (LinearMap.range μ.hom).mkQ
    let S : ShortComplex (ModuleCat.{v} A) := ShortComplex.mk μ q (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩)
    have hS : S.ShortExact := by
      apply ModuleCat.shortComplex_shortExact S
      · exact LinearMap.exact_map_mkQ_range μ.hom
      · apply (LinearMap.ker_eq_bot).mp
        rw [Submodule.eq_bot_iff]
        intro x hx
        exact hreg x hx
      · exact (LinearMap.range μ.hom).mkQ_surjective
    have hQ (p : PrimeSpectrum A) (j : ℕ) (hj : j ≤ n) :
        Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl ((E j).obj Q)) := by
      obtain ⟨δp, hp, ep, hc, ec, δn, hn, en⟩ :=
        localCohomology_homology_exact_sequences A I hI S hS j
      have := hN p j (by omega)
      have : Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl ((E ((j : ℤ) + 1)).obj N)) := by
        have heq : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
        rw [heq]
        exact hN p (j + 1) (by omega)
      exact finite_localized_of_exact ((E j).map q).hom δn.hom
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp en)
        p.asIdeal.primeCompl
    have hQfin := ih Q hQ
    have hNfin (i : ℕ) (hi : i ≤ n + 1) : Module.Finite A ((E i).obj N) := by
      by_cases hi0 : i = 0
      · subst i
        exact localCohomology_zero_finite A I hI N
      · obtain ⟨δp, hp, ep, hc, ec, δn, hn, en⟩ :=
          localCohomology_homology_exact_sequences A I hI S hS i
        have : Module.Finite A ((E ((i : ℤ) - 1)).obj Q) := by
          have heq : (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) := by omega
          rw [heq]
          exact hQfin (i - 1) (by omega)
        have hlin : (E i).Linear A := derivedSupportCohomology_linear A I hI (i : ℤ)
        have hμ : (E i).map μ = f • 𝟙 ((E i).obj N) :=
          ((E i).map_smul f (𝟙 N)).trans
            (congrArg (fun g => f • g) ((E i).map_id N))
        have hker : (LinearMap.ker (f • (LinearMap.id :
            (E i).obj N →ₗ[A] (E i).obj N))).FG := by
          have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp ep
          change Function.Exact δp.hom ((E i).map μ).hom at he
          rw [hμ] at he
          change Function.Exact δp.hom (f • (LinearMap.id :
            (E i).obj N →ₗ[A] (E i).obj N)) at he
          rw [LinearMap.exact_iff.mp he]
          simpa only [Submodule.map_top] using
            (Module.Finite.fg_top (R := A) (M := (E ((i : ℤ) - 1)).obj Q)).map δp.hom
        exact finite_of_ker_smul_of_localizations_finite I
          (by exact ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor _ 0).obj N)).property (i : ℤ))
          f hf hker (fun p => hN p i hi)
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      exact localCohomology_zero_finite A I hI M
    · have := hNfin i hi
      exact Module.Finite.equiv (eQ i (by omega)).toLinearEquiv.symm

/-- **Stacks 0AW9.** For a finite module over a Noetherian ring, finiteness of
local cohomology through degree `n` can be checked after localization at every
prime ideal. -/
@[stacks 0AW9]
public theorem localCohomology_finite_iff_localizations_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (n : ℕ) :
    let hI : I.FG := Ideal.fg_of_isNoetherianRing I
    let RΓ := Dualizing.localCohomologyFunctor A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty A I hI).ι
    let H := fun i : ℕ ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (i : ℤ)).obj
        (RΓ.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A M)))
    (∀ i : ℕ, i ≤ n → Module.Finite A (H i)) ↔
      ∀ p : PrimeSpectrum A, ∀ i : ℕ, i ≤ n →
        Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl (H i)) := by
  classical
  dsimp only
  refine ⟨fun h p i hi => ?_, localCohomology_finite_of_localizations_finite A I
    (Ideal.fg_of_isNoetherianRing I) n (ModuleCat.of A M)⟩
  have := h i hi
  exact Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)

end Stacks.LocalCohomology
