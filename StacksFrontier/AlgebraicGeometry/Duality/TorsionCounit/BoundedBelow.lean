module

public import StacksFrontier.AlgebraicGeometry.Duality.TorsionCounit.TorsionModule
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.DerivedTorsion

/-!
# Part (1) of Stacks 0955 for a bounded-below object

Let `A` be a Noetherian ring and `I ⊆ A` a finitely generated ideal. Derived `I`-power torsion
`RΓ_I` is right adjoint to the derived inclusion of the `I`-power-torsion modules into `D(A)`
([Stacks, Tag 0A6L]), and part (1) of [Stacks, Tag 0955] asserts that the counit `RΓ_I(K) ⟶ K`
of that adjunction is invertible at every object `K` of `D(A)` whose cohomology modules are
`I`-power torsion. This file proves that assertion for every such `K` which is **bounded below**.

The source proves the bounded-below case with the hypercohomology spectral sequence of
[Stacks, Tag 015J]; the proof here replaces it with an induction up the degrees, and is therefore
elementary. Represent `K` by a bounded-below complex `J` of injective `A`-modules. It is
K-injective, so by `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso`
the assertion is that the degreewise inclusion `Γ_I(J) ⟶ J` of the termwise torsion subcomplex is
a quasi-isomorphism, i.e. that the quotient complex `J/Γ_I(J)` is acyclic. Here the Noetherian
hypothesis enters: each `Γ_I(J^n)` is an injective `A`-module ([Stacks, Tag 08XW]), so the
termwise short exact sequence splits, and the quotient is again a bounded-below complex of
injectives — hence K-injective — with no `I`-power torsion in any degree. Those two properties say
exactly that no nonzero morphism of `D(A)` reaches the quotient from a torsion module placed in a
single degree, while the long exact sequence of the short exact sequence says that the quotient's
cohomology is `I`-power torsion. A bounded-below object with those two properties has no
cohomology at all, by an induction on the degree which at each step identifies the canonical
truncation `τ^{≤j}` with a single torsion module and kills the truncation map.

## Main results

* `Dualizing.TorsionCounit.isZero_homology_of_isGE_of_hom_eq_zero` — the vanishing criterion: a
  bounded-below object of a derived category whose cohomology satisfies a property `P` and which
  receives no nonzero morphism from an object of `P` in a single degree has no cohomology.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isGE` — **part (1) of
  [Stacks, Tag 0955] for a bounded-below object**, for the normalized counit.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isGE'` — the same for the
  counit of `Dualizing.derivedPowerTorsionAdjunction`, the adjunction of [Stacks, Tag 0A6L] named
  as a value.
* `Dualizing.TorsionCounit.isIso_compareTorsionFunctors_app_of_isGE` — part (3) of
  [Stacks, Tag 0955] at a bounded-below object: the comparison `RΓ_I ⟶ RΓ_Z` of
  [Stacks, Tag 0A6U] is invertible there.
* `Dualizing.TorsionCounit.isIso_compareSectionsWithSupportLocalCohomology_app_of_isGE` — the
  bridge `RΓ_{V(I)} ⟶ RΓ_Z` between the set-indexed model of local cohomology and the
  ideal-indexed coreflection model is invertible at a bounded-below object with torsion
  cohomology. This is what the implementation notes of
  `StacksFrontier/RingTheory/LocalCohomology/ModelComparison/DerivedTorsion.lean` record as missing.

## Implementation notes

No `@[stacks 0955]` attribute appears here. Part (1) of the source is the assertion for *every*
object of `D_{I^∞-torsion}(A)`, and the unbounded case is not proved: it needs the third paragraph
of the source's proof, which replaces the powers `A/I^n` by the Koszul complexes on
`f₁^n, …, f_r^n` ([Stacks, Tag 0921], in the library as
`NoetherianKoszulProIso.koszulPowerSystem_proIso_quotientPowerSystem`) in the colimit description
of `R^qΓ_I` ([Stacks, Tag 0954], in the library as
`Stacks.LocalCohomology.localCohomologyHomologyIsoColimitExt`) in order to see that `R^qΓ_I(K)`
depends only on a bounded-below truncation of `K`.

The universe convention is the one forced by `Dualizing.derivedPowerTorsion`: the ring lives in
`Type u` and the modules in `Type (max u v)`.

## References

* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 08XW](https://stacks.math.columbia.edu/tag/08XW)
* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v u₁ v₁

namespace Dualizing.TorsionCounit

attribute [local instance] HasDerivedCategory.standard

/-! ### A vanishing criterion in the derived category -/

section Vanishing

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle whose third vertex has no homology in degrees `≤ a`, the first
map induces an isomorphism on homology in every degree `≤ a`. -/
lemma isIso_homologyMap_mor₁_of_isZero {T : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang (DerivedCategory C)) (a i : ℤ) (hi : i ≤ a)
    (hV : ∀ j : ℤ, j ≤ a → IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i]
    exact (hV (i - 1) (by omega)).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (hV i hi).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- The inductive step: if `Y` has no homology below `j`, if its homology satisfies `P`, and if
no nonzero morphism reaches `Y` from an object of `P` in a single degree, then `Y` has no
homology in degree `j` either. -/
private lemma isGE_succ_of_hom_eq_zero (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (Y : DerivedCategory C)
    (hP : ∀ j : ℤ, P ((DerivedCategory.homologyFunctor C j).obj Y))
    (hhom : ∀ (j : ℤ) (M : C), P M →
      ∀ f : (DerivedCategory.singleFunctor C j).obj M ⟶ Y, f = 0)
    (j : ℤ) (hY : Y.IsGE j) : Y.IsGE (j + 1) := by
  set t := DerivedCategory.TStructure.t (C := C)
  set A0 := (t.truncLE j).obj Y
  have hle : t.IsLE A0 j := inferInstance
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A0 j
  set T : Triangle (DerivedCategory C) :=
    Triangle.mk ((t.truncLEι j).app Y) ((t.truncGTπ j).app Y) ((t.truncGTδLE j).app Y)
  have hTd : T ∈ distTriang (DerivedCategory C) := t.triangleLEGT_distinguished j Y
  have hiso : IsIso ((DerivedCategory.homologyFunctor C j).map T.mor₁) :=
    isIso_homologyMap_mor₁_of_isZero hTd j j le_rfl (fun i hi =>
      DerivedCategory.isZero_of_isGE ((t.truncGT j).obj Y) (j + 1) i (by omega))
  have eM : M ≅ (DerivedCategory.homologyFunctor C j).obj Y :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C j).app M).symm ≪≫
      (DerivedCategory.homologyFunctor C j).mapIso e.symm ≪≫
      asIso ((DerivedCategory.homologyFunctor C j).map T.mor₁)
  have hu : T.mor₁ = 0 := by
    simpa using e.hom ≫= hhom j M (P.prop_of_iso eM.symm (hP j)) (e.inv ≫ T.mor₁)
  have hobj₃ : t.IsGE T.obj₃ (j + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGT j).obj Y) (j + 1))
  have hzero : IsZero A0 := by
    rw [IsZero.iff_id_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hTd)
      (𝟙 A0) ((Category.id_comp _).trans hu)
    have hg0 : g = 0 := t.zero_of_isLE_of_isGE g j (j + 2) (by omega) hle
      (t.isGE_shift T.obj₃ (j + 1) (-1) (j + 2) (by omega))
    rw [hg, hg0]
    exact zero_comp
  exact (t.isGE_iff_isZero_truncLE_obj j (j + 1) rfl Y).mpr hzero

/-- **The vanishing criterion.** Let `Y` be a bounded-below object of `D(C)` all of whose
homology objects satisfy `P`, and suppose no nonzero morphism reaches `Y` from an object of `P`
placed in a single degree. Then `Y` has no homology at all. -/
lemma isZero_homology_of_isGE_of_hom_eq_zero (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (Y : DerivedCategory C) (a : ℤ) (hYa : Y.IsGE a)
    (hP : ∀ j : ℤ, P ((DerivedCategory.homologyFunctor C j).obj Y))
    (hhom : ∀ (j : ℤ) (M : C), P M →
      ∀ f : (DerivedCategory.singleFunctor C j).obj M ⟶ Y, f = 0)
    (j : ℤ) : IsZero ((DerivedCategory.homologyFunctor C j).obj Y) := by
  have key : ∀ k : ℕ, Y.IsGE (a + k) := by
    intro k
    induction k with
    | zero => simpa using hYa
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact isGE_succ_of_hom_eq_zero P Y hP hhom (a + k) ih
  have := key (j - a + 1).toNat
  exact DerivedCategory.isZero_of_isGE Y (a + ((j - a + 1).toNat : ℤ)) j (by omega)

end Vanishing

/-! ### Transporting the torsion property -/

section Transport

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The `I`-power-torsion property transports along an isomorphism of modules. -/
lemma isIPowerTorsion_of_iso {M N : ModuleCat.{max u v} A} (e : M ≅ N)
    (h : IsIPowerTorsion A M I) : IsIPowerTorsion A N I := by
  intro y
  obtain ⟨n, hn, hkill⟩ := h (e.inv.hom y)
  refine ⟨n, hn, fun a ha => ?_⟩
  calc a • y = e.hom.hom (a • e.inv.hom y) := by simp
    _ = 0 := by rw [hkill a ha, map_zero]

/-- A zero module is `I`-power torsion. -/
lemma isIPowerTorsion_of_isZero {M : ModuleCat.{max u v} A} (h : IsZero M) :
    IsIPowerTorsion A M I := by
  intro m
  have hm : m = 0 := by
    simpa using congrArg (fun (φ : M ⟶ M) => φ.hom m) (h.eq_of_src (𝟙 M) 0)
  exact ⟨1, Nat.zero_lt_one, fun a _ => by rw [hm, smul_zero]⟩

/-- Every term of the complex concentrated in one degree on an `I`-power-torsion module is
`I`-power torsion. -/
lemma isIPowerTorsion_singleFunctor_X (j : ℤ) (M : ModuleCat.{max u v} A)
    (hM : IsIPowerTorsion A M I) (n : ℤ) :
    IsIPowerTorsion A
      (((CochainComplex.singleFunctor (ModuleCat.{max u v} A) j).obj M).X n) I := by
  by_cases hn : n = j
  · subst hn
    exact isIPowerTorsion_of_iso.{u, v} A I
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M).symm hM
  · exact isIPowerTorsion_of_isZero.{u, v} A I
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j M n hn)

end Transport

/-! ### The torsion-free quotient of a complex of injectives -/

section Quotient

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The termwise torsion inclusion is a monomorphism of complexes. -/
lemma mono_powerTorsionSubcomplexι (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    Mono ((powerTorsionSubcomplexι.{u, v} A I).app J) := by
  refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
  rw [ModuleCat.mono_iff_injective]
  exact fun _ _ => Subtype.ext

/-- The quotient of a complex by its termwise `I`-power-torsion subcomplex. -/
def torsionFreeQuotient (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    CochainComplex (ModuleCat.{max u v} A) ℤ :=
  cokernel ((powerTorsionSubcomplexι.{u, v} A I).app J)

/-- The projection onto the quotient by the termwise `I`-power-torsion subcomplex. -/
def torsionFreeProjection (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    J ⟶ torsionFreeQuotient.{u, v} A I J :=
  cokernel.π _

/-- The short complex `Γ_I(J) ⟶ J ⟶ J/Γ_I(J)`. -/
def torsionShortComplex (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max u v} A) ℤ) :=
  ShortComplex.mk ((powerTorsionSubcomplexι.{u, v} A I).app J)
    (cokernel.π _) (cokernel.condition _)

/-- The short complex `Γ_I(J) ⟶ J ⟶ J/Γ_I(J)` is short exact. -/
lemma torsionShortComplex_shortExact (J : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (torsionShortComplex.{u, v} A I J).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := mono_powerTorsionSubcomplexι.{u, v} A I J
  epi_g := inferInstanceAs (Epi (cokernel.π
    ((powerTorsionSubcomplexι.{u, v} A I).app J)))

/-- In each degree `n`, the short complex `Γ_I(J)ⁿ ⟶ Jⁿ ⟶ (J/Γ_I(J))ⁿ` is short exact. -/
lemma torsionShortComplex_shortExact_eval (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (n : ℤ) :
    ((torsionShortComplex.{u, v} A I J).map
      (HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n)).ShortExact :=
  (torsionShortComplex_shortExact.{u, v} A I J).map_of_exact _

section Noetherian
variable [IsNoetherianRing A]

/-- Over a Noetherian ring, the termwise torsion subcomplex of a complex of injectives has
injective terms. This is Stacks 08XW. -/
lemma injective_torsionShortComplex_X₁ (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hJ : ∀ n, Injective (J.X n)) (n : ℤ) :
    Injective (((torsionShortComplex.{u, v} A I J).map
      (HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n)).X₁) := by
  have : Module.Injective A (J.X n) :=
    (Module.injective_iff_injective_object A (J.X n)).mpr (hJ n)
  exact (Module.injective_iff_injective_object A (Ideal.primaryComponent (J.X n) I)).mp
    (Module.injective_primaryComponent (R := A) (I := (J.X n : Type (max u v))) I)

/-- **The termwise splitting.** Since the torsion subcomplex has injective terms, the termwise
short exact sequence `0 ⟶ Γ_I(J) ⟶ J ⟶ J/Γ_I(J) ⟶ 0` splits in every degree. -/
lemma exists_section_torsionFreeProjection (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hJ : ∀ n, Injective (J.X n)) (n : ℤ) :
    ∃ s : (torsionFreeQuotient.{u, v} A I J).X n ⟶ J.X n,
      s ≫ (torsionFreeProjection.{u, v} A I J).f n = 𝟙 _ := by
  have := injective_torsionShortComplex_X₁.{u, v} A I J hJ n
  exact ⟨_, (torsionShortComplex_shortExact_eval.{u, v} A I J n).splittingOfInjective.s_g⟩

/-- The terms of the torsion-free quotient are injective: each is a retract of a term of `J`. -/
lemma injective_torsionFreeQuotient_X (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hJ : ∀ n, Injective (J.X n)) (n : ℤ) :
    Injective ((torsionFreeQuotient.{u, v} A I J).X n) := by
  obtain ⟨s, hs⟩ := exists_section_torsionFreeProjection.{u, v} A I J hJ n
  have := hJ n
  exact (⟨s, _, hs⟩ : Retract ((torsionFreeQuotient.{u, v} A I J).X n) (J.X n)).injective

/-- The torsion-free quotient has no `I`-power torsion in any degree: a map into it from a
torsion module lifts along the splitting into `J`, where it factors through the torsion
subcomplex, hence dies in the quotient. -/
lemma hom_eq_zero_of_isIPowerTorsion (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hJ : ∀ n, Injective (J.X n)) (n : ℤ) (N : ModuleCat.{max u v} A)
    (hN : IsIPowerTorsion A N I) (f : N ⟶ (torsionFreeQuotient.{u, v} A I J).X n) :
    f = 0 := by
  obtain ⟨s, hs⟩ := exists_section_torsionFreeProjection.{u, v} A I J hJ n
  let adj := powerTorsionAdjunction.{u, v} A I
  let Nt : (ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I)) := ⟨N, hN⟩
  let g := (adj.homEquiv Nt (J.X n)) (f ≫ s)
  have hfac : (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I)).map g ≫
      adj.counit.app (J.X n) = f ≫ s :=
    (adj.homEquiv_counit Nt (J.X n) g).symm.trans
      ((adj.homEquiv Nt (J.X n)).symm_apply_apply (f ≫ s))
  have hcounit : adj.counit.app (J.X n) =
      ((powerTorsionSubcomplexι.{u, v} A I).app J).f n := by
    rw [powerTorsionAdjunction_counit.{u, v} A I]
    rfl
  have hzero : ((powerTorsionSubcomplexι.{u, v} A I).app J).f n ≫
      (torsionFreeProjection.{u, v} A I J).f n = 0 := by
    rw [← HomologicalComplex.comp_f,
      show (powerTorsionSubcomplexι.{u, v} A I).app J ≫ torsionFreeProjection.{u, v} A I J = 0
        from cokernel.condition _, HomologicalComplex.zero_f]
  have hf : f = f ≫ s ≫ (torsionFreeProjection.{u, v} A I J).f n := by
    rw [hs, Category.comp_id]
  rw [hf, ← Category.assoc, ← hfac, hcounit, Category.assoc, hzero, comp_zero]

omit [IsNoetherianRing A] in
/-- The torsion-free quotient vanishes wherever `J` does. -/
lemma isZero_torsionFreeQuotient_X (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (n : ℤ) (h : IsZero (J.X n)) : IsZero ((torsionFreeQuotient.{u, v} A I J).X n) := by
  have hepi : Epi (((torsionShortComplex.{u, v} A I J).map
      (HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n)).g) :=
    (torsionShortComplex_shortExact_eval.{u, v} A I J n).epi_g
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi ((torsionShortComplex.{u, v} A I J).map
    (HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n)).g).mp ?_
  exact (Category.comp_id _).trans ((h.eq_of_src _ _).trans comp_zero.symm)

end Noetherian

/-- The torsion-free quotient of a strictly bounded-below complex is strictly bounded below. -/
lemma isStrictlyGE_torsionFreeQuotient (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : ℤ)
    [J.IsStrictlyGE a] : (torsionFreeQuotient.{u, v} A I J).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact isZero_torsionFreeQuotient_X.{u, v} A I J i
    ((CochainComplex.isStrictlyGE_iff J a).mp ‹_› i hi)

end Quotient

/-! ### Morphisms into a K-injective complex -/

section KInjectiveHom

variable (A : Type u) [CommRing A]

/-- No nonzero morphism of the derived category reaches a K-injective complex from a complex
admitting no nonzero chain map into it. -/
lemma hom_eq_zero_of_isKInjective
    (Qc L : CochainComplex (ModuleCat.{max u v} A) ℤ) (hQc : Qc.IsKInjective)
    (hzero : ∀ φ : L ⟶ Qc, φ = 0)
    (f : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj Qc) : f = 0 := by
  set eL := (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L
  set eQ := (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app Qc
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L)
    Qc).surjective (eL.hom ≫ f ≫ eQ.inv)
  obtain ⟨φ, hφ⟩ := (HomotopyCategory.quotient (ModuleCat.{max u v} A)
    (ComplexShape.up ℤ)).map_surjective g
  have h0 : eL.hom ≫ f ≫ eQ.inv = 0 := by
    rw [← hg, ← hφ, hzero φ, Functor.map_zero, Functor.map_zero]
  simpa using eL.inv ≫= h0 =≫ eQ.hom

end KInjectiveHom

/-! ### Part (1) of Stacks 0955 for a bounded-below object -/

section Main

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)

omit [IsNoetherianRing A] in
include hI in
/-- The cohomology of the termwise torsion subcomplex is `I`-power torsion: it is a subquotient
of a term, and the `I`-power-torsion modules are a Serre subcategory. -/
lemma isIPowerTorsion_homology_torsionSubcomplex
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ) :
    IsIPowerTorsion A (((torsionShortComplex.{u, v} A I J).X₁).homology i) I := by
  have hterm : powerTorsionModuleProperty.{u, max u v} A I hI
      (((torsionShortComplex.{u, v} A I J).X₁).X i) :=
    ((powerTorsionFunctor.{u, v} A I).obj (J.X i)).property
  have h1 : powerTorsionModuleProperty.{u, max u v} A I hI
      (((torsionShortComplex.{u, v} A I J).X₁).opcycles i) :=
    (powerTorsionModuleProperty.{u, max u v} A I hI).prop_of_epi
      (HomologicalComplex.pOpcycles _ i) hterm
  exact (powerTorsionModuleProperty.{u, max u v} A I hI).prop_of_mono
    (HomologicalComplex.homologyι _ i) h1

/-- **Stacks 0955, part (1), for a bounded-below object.** Let `A` be a Noetherian ring and
`I ⊆ A` a finitely generated ideal. For every object `K` of `D(A)` which is bounded below and
whose cohomology modules are `I`-power torsion, the counit `RΓ_I(K) ⟶ K` is an isomorphism.

This is the second paragraph of the proof of [Stacks, Tag 0955], by an argument which replaces
the source's spectral sequence with an induction on the degree. Choose a bounded-below complex
`J` of injective `A`-modules representing `K`; it is K-injective, so by
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso` the assertion is
that the degreewise torsion inclusion `Γ_I(J) ⟶ J` is a quasi-isomorphism, i.e. that the
quotient `Q = J/Γ_I(J)` is acyclic. Over a Noetherian ring each `Γ_I(J^n)` is injective
([Stacks, Tag 08XW]), so the termwise short exact sequence splits: `Q` is again a bounded-below
complex of injectives, hence K-injective, and it has no `I`-power torsion in any degree. The
first property makes every morphism into `Q` from a torsion module in a single degree vanish;
the second makes the cohomology of `Q` torsion, by the long exact sequence. An object of `D(A)`
bounded below, with torsion cohomology, which receives no nonzero map from a torsion module in
a single degree is zero — that is
`Dualizing.TorsionCounit.isZero_homology_of_isGE_of_hom_eq_zero`, proved by induction up the
degrees using the canonical truncation. -/
theorem isIso_derivedPowerTorsionCounit_app_of_isGE
    (K : DerivedCategory (ModuleCat.{max u v} A)) (a : ℤ) (hKa : K.IsGE a)
    (hK : derivedPowerTorsionProperty A I hI K) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app K) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  obtain ⟨L, hLGE, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨R, -, hRGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a L
  have hinj : ∀ n, Injective (R.cocomplex.X n) := R.injective
  have hqi : IsIso (DerivedCategory.Q.map R.ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr R.quasiIso
  let eJ : DerivedCategory.Q.obj R.cocomplex ≅ K :=
    (asIso (DerivedCategory.Q.map R.ι)).symm ≪≫ eL.symm
  refine isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI eJ ?_
  rw [isIso_derivedPowerTorsionCounit_app_Q_iff_quasiIso.{u, v} A I hI R.cocomplex
    (CochainComplex.isKInjective_of_injective R.cocomplex a),
    ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  -- the short exact sequence of complexes and its distinguished triangle
  have hTr := DerivedCategory.triangleOfSES_distinguished
    (torsionShortComplex_shortExact.{u, v} A I R.cocomplex)
  -- the quotient is a bounded-below complex of injectives, hence K-injective
  have := isStrictlyGE_torsionFreeQuotient.{u, v} A I R.cocomplex a
  have hQcinj : ∀ n, Injective ((torsionFreeQuotient.{u, v} A I R.cocomplex).X n) :=
    injective_torsionFreeQuotient_X.{u, v} A I R.cocomplex hinj
  -- the quotient has no homology
  have hvanish : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      (DerivedCategory.Q.obj (torsionFreeQuotient.{u, v} A I R.cocomplex))) := by
    refine isZero_homology_of_isGE_of_hom_eq_zero
      (powerTorsionModuleProperty.{u, max u v} A I hI) _ a inferInstance ?_ ?_
    · -- the homology of the quotient is torsion
      intro j
      refine (powerTorsionModuleProperty.{u, max u v} A I hI).prop_X₂_of_exact
        (DerivedCategory.HomologySequence.exact₃ _ hTr j (j + 1) rfl) ?_ ?_
      · exact isIPowerTorsion_of_iso.{u, v} A I
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) j).mapIso eJ).symm (hK j)
      · exact isIPowerTorsion_of_iso.{u, v} A I
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) (j + 1)).app
            (torsionShortComplex.{u, v} A I R.cocomplex).X₁).symm
          (isIPowerTorsion_homology_torsionSubcomplex.{u, v} A I hI R.cocomplex (j + 1))
    · -- no nonzero map from a torsion module in a single degree
      intro j M hM f
      refine hom_eq_zero_of_isKInjective.{u, v} A _
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) j).obj M)
        (CochainComplex.isKInjective_of_injective _ a) (fun φ => ?_) f
      refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
      exact hom_eq_zero_of_isIPowerTorsion.{u, v} A I R.cocomplex hinj n _
        (isIPowerTorsion_singleFunctor_X.{u, v} A I j M hM n) (φ.f n)
  rw [DerivedCategory.isIso_iff]
  intro i
  exact isIso_homologyMap_mor₁_of_isZero hTr i i le_rfl (fun j _ => hvanish j)

/-- **Part (1) of Stacks 0955 for a bounded-below object, for the counit of the Tag 0A6L
adjunction as a value.** Invertibility of the counit at an object does not depend on which
adjunction between the two functors is chosen, so the statement for the normalized counit
transfers to `Dualizing.derivedPowerTorsionCounit`. -/
alias isIso_derivedPowerTorsionCounit_app_of_isGE' :=
    Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isGE

/-- **Part (3) of Stacks 0955 at a bounded-below object.** The comparison `RΓ_I ⟶ RΓ_Z` of
[Stacks, Tag 0A6U] is invertible at every bounded-below object of `D(A)` whose cohomology modules
are `I`-power torsion. -/
theorem isIso_compareTorsionFunctors_app_of_isGE
    (K : PowerTorsionDerivedCategory.{u, max u v} A I hI) (a : ℤ) (hKa : K.obj.IsGE a) :
    IsIso ((compareTorsionFunctors.{u, v} A I hI).app K.obj) :=
  (isIso_derivedPowerTorsionCounit_app_iff_isIso_compareTorsionFunctors.{u, v} A I hI K).mp
    (isIso_derivedPowerTorsionCounit_app_of_isGE.{u, v} A I hI K.obj a hKa K.property)

/-- **The two models of local cohomology agree on bounded-below torsion objects.** The canonical
map from the total right derived functor of sections supported in the closed subset `V(I)` to
local cohomology `RΓ_Z` in the sense of [Stacks, Tag 0A6Q] — the bridge
`Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology` between the set-indexed model
and the ideal-indexed coreflection model — is invertible at every bounded-below object of `D(A)`
whose cohomology modules are `I`-power torsion. -/
theorem isIso_compareSectionsWithSupportLocalCohomology_app_of_isGE
    (K : DerivedCategory (ModuleCat.{max u v} A)) (a : ℤ) (hKa : K.IsGE a)
    (hK : derivedPowerTorsionProperty A I hI K) :
    IsIso ((Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology.{u, v}
      A I hI).app K) := by
  have h1 : IsIso ((compareTorsionFunctors.{u, v} A I hI).app K) :=
    isIso_compareTorsionFunctors_app_of_isGE.{u, v} A I hI ⟨K, hK⟩ a hKa
  change IsIso
    ((Stacks.LocalCohomology.derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v}
        A I hI).hom.app K ≫
      (Functor.isoWhiskerLeft (derivedPowerTorsion.{u, v} A I hI)
        (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv.app K ≫
      (derivedPowerTorsionProperty A I hI).ι.map
        ((compareTorsionFunctors.{u, v} A I hI).app K))
  exact (((Stacks.LocalCohomology.derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v}
      A I hI).app K) ≪≫
    ((Functor.isoWhiskerLeft (derivedPowerTorsion.{u, v} A I hI)
      (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).symm.app K) ≪≫
    (derivedPowerTorsionProperty A I hI).ι.mapIso
      (@asIso _ _ _ _ ((compareTorsionFunctors.{u, v} A I hI).app K) h1)).isIso_hom

end Main

end Dualizing.TorsionCounit

end
