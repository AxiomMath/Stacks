module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Detecting injective amplitude and finite injective dimension

For an object of the derived category of modules over a commutative ring, having injective
amplitude in an interval is equivalent to the vanishing of all Ext groups outside that interval,
and it is enough to test this vanishing on quotient modules by ideals. A bounded object has
finite injective dimension as soon as each of its cohomology modules does, and likewise as soon
as some bounded representative has terms of finite injective dimension.

The Stacks Project convention that rings are commutative accounts for the `CommRing` assumption.

## Main definitions

This file introduces no new definitions.

## Main results

* `StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing`:
  the equivalent characterizations of injective amplitude by Ext vanishing against all modules
  and against cyclic quotient modules.
* `StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_of_bounded`: the cohomology and
  representative criteria for finite injective dimension.

## Implementation notes

An Ext group vanishes when its underlying type is a subsingleton. Quotient modules are shrunk
into the universe containing the target module. The three-way equivalence of Stacks 0A5T is
expressed by the equivalence of the first and second conditions together with that of the second
and third conditions.

Baer's criterion in the form "injectivity is the vanishing of first Ext from quotients by ideals"
is taken from Mathlib as `ModuleCat.injective_iff_subsingleton_ext_quotient_one`. That statement
is the content of Stacks 0AVF, which belongs to another cluster; whichever module ends up
registering that tag should cite the same Mathlib lemma rather than reprove it.

Membership in the bounded derived category is expressed by simultaneous cohomological lower and
upper bounds. A complex represents a derived object through an isomorphism from its image under
the localization functor. Finite injective dimension of an individual module is expressed by the
existence of a natural-number upper bound on its injective dimension.

## References

* [Stacks Project, Tag 0A5T](https://stacks.math.columbia.edu/tag/0A5T)
* [Stacks Project, Tag 0A5V](https://stacks.math.columbia.edu/tag/0A5V)
-/

open CategoryTheory

namespace StacksDraft.InjectiveDimension

universe w u v

section ExtCriterion

open Limits HomologicalComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private lemma single_hom_eq_zero_iff (N : C) (K : DerivedCategory C) (i : ℤ) :
    (∀ f : (DerivedCategory.singleFunctor C i).obj N ⟶ K, f = 0) ↔
      (∀ f : DerivedCategory.Ext ((DerivedCategory.singleFunctor C 0).obj N) K i,
        f = 0) := by
  let e := ((DerivedCategory.singleFunctors C).shiftIso i 0 i (by omega)).app N
  constructor
  · intro h f
    have hf : e.hom ≫ f = 0 := by
      obtain ⟨g, hg⟩ := (shiftFunctor (DerivedCategory C) i).map_surjective (e.hom ≫ f)
      rw [← hg, h g, Functor.map_zero]
    simpa using congrArg (fun g => e.inv ≫ g) hf
  · intro h f
    apply (shiftFunctor (DerivedCategory C) i).map_injective
    rw [Functor.map_zero]
    simpa using congrArg (fun g => e.hom ≫ g) (h (e.inv ≫ f⟦i⟧'))

private lemma Q_map_surjective_of_isKInjective (A B : CochainComplex C ℤ)
    [B.IsKInjective] : Function.Surjective (DerivedCategory.Q.map : (A ⟶ B) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj A) B).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app A ≫ f ≫
        (DerivedCategory.quotientCompQhIso C).inv.app B)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app A)]
  simp only [← DerivedCategory.quotientCompQhIso_hom_naturality,
    hg, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private lemma homotopy_zero_of_Q_map_eq_zero {A B : CochainComplex C ℤ}
    [B.IsKInjective] (f : A ⟶ B) (hf : DerivedCategory.Q.map f = 0) :
    Nonempty (Homotopy f 0) := by
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).1
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ B).injective
  rw [Functor.map_zero, ← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app B)]
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality,
    hf, comp_zero, zero_comp]

private lemma exists_eq_comp_d_of_single_hom_eq_zero (I : CochainComplex C ℤ)
    [I.IsKInjective] (N : C) (n : ℤ)
    (h : ∀ f : (DerivedCategory.singleFunctor C n).obj N ⟶ DerivedCategory.Q.obj I,
      f = 0) (f : N ⟶ I.X n) (hf : f ≫ I.d n (n + 1) = 0) :
    ∃ g : N ⟶ I.X (n - 1), g ≫ I.d (n - 1) n = f := by
  let φ := mkHomFromSingle f (fun j hj => by
    obtain rfl : j = n + 1 := by simpa only [ComplexShape.up_Rel] using hj.symm
    exact hf)
  obtain ⟨H⟩ := homotopy_zero_of_Q_map_eq_zero φ (h (DerivedCategory.Q.map φ))
  refine ⟨(singleObjXSelf (.up ℤ) n N).inv ≫ H.hom n (n - 1), ?_⟩
  have hh := H.comm n
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at hh
  dsimp [φ] at hh
  simpa only [mkHomFromSingle_f, single_obj_d, zero_comp, zero_f, zero_add, add_zero,
    Iso.inv_hom_id_assoc, Category.assoc] using
      congrArg (fun g => (singleObjXSelf (.up ℤ) n N).inv ≫ g) hh.symm

set_option backward.isDefEq.respectTransparency false in
private lemma hom_homology_eq_zero_of_single_hom_eq_zero (I : CochainComplex C ℤ)
    (P : C) [Projective P] (n : ℤ)
    (h : ∀ f : (DerivedCategory.singleFunctor C n).obj P ⟶ DerivedCategory.Q.obj I,
      f = 0) (f : P ⟶ I.homology n) : f = 0 := by
  let g := Projective.factorThru f (I.homologyπ n)
  let φ := mkHomFromSingle (g ≫ I.iCycles n) (fun j _ => by simp)
  have hφ : homologyMap φ n = 0 := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors C n).hom.app
      ((CochainComplex.singleFunctor C n).obj P)),
      ← DerivedCategory.homologyFunctorFactors_hom_naturality,
      h (DerivedCategory.Q.map φ), Functor.map_zero, zero_comp, comp_zero]
  have hc : (singleObjCyclesSelfIso (.up ℤ) n P).inv ≫ cyclesMap φ n = g := by
    rw [← cancel_mono (I.iCycles n), Category.assoc, cyclesMap_i]
    dsimp [φ]
    simp only [mkHomFromSingle_f, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles,
      Iso.inv_hom_id, Category.id_comp]
  rw [← Projective.factorThru_comp f (I.homologyπ n)]
  show g ≫ I.homologyπ n = 0
  rw [← hc, Category.assoc, ← homologyπ_naturality, hφ, comp_zero, comp_zero]

/-- A map between objects isomorphic to `Q A` and `Q I`, with `I` K-injective, vanishes when
every map of complexes `A ⟶ I` does. -/
private lemma eq_zero_of_forall_hom_eq_zero_of_isKInjective {X K : DerivedCategory C}
    {A I : CochainComplex C ℤ} [I.IsKInjective] (eA : X ≅ DerivedCategory.Q.obj A)
    (e : K ≅ DerivedCategory.Q.obj I) (h : ∀ g : A ⟶ I, g = 0) (f : X ⟶ K) : f = 0 := by
  obtain ⟨g, hg⟩ := Q_map_surjective_of_isKInjective A I (eA.inv ≫ f ≫ e.hom)
  rw [h g, Functor.map_zero] at hg
  simpa using congrArg (fun u => eA.hom ≫ u ≫ e.inv) hg.symm

/-- An object of the derived category with injective amplitude in `[a, b]` has no cohomology
below the degree `a`. -/
public lemma isGE_of_hasInjectiveAmplitude (K : DerivedCategory C) (a b : ℤ)
    (hK : HasInjectiveAmplitude K a b) : K.IsGE a := by
  obtain ⟨I, _, _, _, ⟨e⟩⟩ := hK
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

/-- An object of the derived category with injective amplitude in `[a, b]` has no cohomology
above the degree `b`. -/
public lemma isLE_of_hasInjectiveAmplitude (K : DerivedCategory C) (a b : ℤ)
    (hK : HasInjectiveAmplitude K a b) : K.IsLE b := by
  obtain ⟨I, _, _, _, ⟨e⟩⟩ := hK
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm b

/-- Shifting by `n` translates injective amplitude: if `K` has injective amplitude in `[a, b]`,
then `K⟦n⟧` has injective amplitude in `[a', b']` whenever `a' + n = a` and `b' + n = b`. -/
public lemma hasInjectiveAmplitude_shift (K : DerivedCategory C) (a b n a' b' : ℤ)
    (hK : HasInjectiveAmplitude K a b) (ha : a' + n = a) (hb : b' + n = b) :
    HasInjectiveAmplitude (K⟦n⟧) a' b' := by
  obtain ⟨I, _, _, hI, ⟨e⟩⟩ := hK
  refine ⟨I⟦n⟧, I.isStrictlyGE_shift a n a' (by omega),
    I.isStrictlyLE_shift b n b' (by omega), fun i => ?_,
    ⟨(shiftFunctor (DerivedCategory C) n).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app I⟩⟩
  exact Injective.of_iso (I.shiftFunctorObjXIso n i (i + n) rfl).symm (hI (i + n))

/-- There is no nonzero map from an object of the derived category with no cohomology below the
degree `p` to an object with injective amplitude in `[a, b]` when `b < p`. -/
public lemma eq_zero_of_isGE_of_hasInjectiveAmplitude (X Y : DerivedCategory C) (p a b : ℤ)
    (hX : X.IsGE p) (hY : HasInjectiveAmplitude Y a b) (hb : b < p) (f : X ⟶ Y) : f = 0 := by
  obtain ⟨I, _, _, hI, ⟨e⟩⟩ := hY
  let := hI
  let := hX
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  obtain ⟨P, _, ⟨eP⟩⟩ := X.exists_iso_Q_obj_of_isGE p
  refine eq_zero_of_forall_hom_eq_zero_of_isKInjective eP e (fun g => ?_) f
  ext i
  by_cases hi : i < p
  · exact (P.isZero_of_isStrictlyGE p i hi).eq_of_src _ _
  · exact (I.isZero_of_isStrictlyLE b i (by omega)).eq_of_tgt _ _

/-- There is no nonzero map from an object of the derived category with no cohomology below the
degree `p` to the shift by `n` of an object with injective amplitude in `[a, b]` when
`b - n < p`. -/
public lemma eq_zero_of_isGE_of_hasInjectiveAmplitude_shift (X Y : DerivedCategory C)
    (p a b n : ℤ) (hX : X.IsGE p) (hY : HasInjectiveAmplitude Y a b) (hb : b - n < p)
    (f : X ⟶ (Y⟦n⟧)) : f = 0 :=
  eq_zero_of_isGE_of_hasInjectiveAmplitude X (Y⟦n⟧) p (a - n) (b - n) hX
    (hasInjectiveAmplitude_shift Y a b n (a - n) (b - n) hY (by omega) (by omega)) hb f

private lemma ext_eq_zero_of_injective_amplitude (K : DerivedCategory C) (a b : ℤ)
    (hK : HasInjectiveAmplitude K a b) (N : C) (i : ℤ)
    (hi : i < a ∨ b < i) :
    ∀ f : DerivedCategory.Ext ((DerivedCategory.singleFunctor C 0).obj N) K i,
      f = 0 := by
  obtain ⟨I, ha, hb, hI, ⟨e⟩⟩ := hK
  let := hI
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  apply (single_hom_eq_zero_iff N K i).1
  intro f
  refine eq_zero_of_forall_hom_eq_zero_of_isKInjective (Iso.refl _) e (fun g => ?_) f
  apply from_single_hom_ext
  apply (show IsZero (I.X i) from hi.elim
    (fun h => I.isZero_of_isStrictlyGE a i h)
    (fun h => I.isZero_of_isStrictlyLE b i h)).eq_of_tgt

omit [HasDerivedCategory C] in
private lemma ext_one_eq_zero_of_surjective (S : ShortComplex C) (hS : S.ShortExact)
    [HasExt C] [Injective S.X₂] (N : C)
    (h : ∀ f : N ⟶ S.X₃, ∃ g : N ⟶ S.X₂, g ≫ S.g = f)
    (x : Abelian.Ext N S.X₁ 1) : x = 0 := by
  obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ N hS x
    (Abelian.Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨g, hg⟩ := h (Abelian.Ext.addEquiv₀ y)
  rw [← Abelian.Ext.mk₀_addEquiv₀_apply y, ← hg, ← Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Abelian.Ext.comp_zero]

private lemma exists_lift_cokernel_cycles (I : CochainComplex C ℤ) [I.IsKInjective]
    (N : C) (b : ℤ)
    (h : ∀ f : (DerivedCategory.singleFunctor C (b + 1)).obj N ⟶ DerivedCategory.Q.obj I,
      f = 0) (f : N ⟶ cokernel (I.iCycles b)) :
    ∃ g : N ⟶ I.X b, g ≫ cokernel.π (I.iCycles b) = f := by
  let c := cokernel.desc (I.iCycles b) (I.d b (b + 1)) (I.iCycles_d b (b + 1))
  have hc : cokernel.π (I.iCycles b) ≫ c = I.d b (b + 1) := cokernel.π_desc ..
  have : Mono c :=
    (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (I.iCycles b) (I.d b (b + 1)) (I.iCycles_d ..))
      (I.cyclesIsKernel b (b + 1) (by simp))).mono_cokernelDesc
  have hd : c ≫ I.d (b + 1) (b + 1 + 1) = 0 := by
    rw [← cancel_epi (cokernel.π (I.iCycles b)), ← Category.assoc, hc,
      I.d_comp_d, comp_zero]
  obtain ⟨g, hg⟩ := exists_eq_comp_d_of_single_hom_eq_zero I N (b + 1) h
    (f ≫ c) (by rw [Category.assoc, hd, comp_zero])
  have hbb : b + 1 - 1 = b := by omega
  refine ⟨g ≫ (I.XIsoOfEq hbb).hom, ?_⟩
  rw [← cancel_mono c, Category.assoc, Category.assoc, hc]
  simpa using hg

set_option backward.isDefEq.respectTransparency false in
private lemma exists_injective_representative [EnoughInjectives C]
    (K : DerivedCategory C) (a : ℤ) [K.IsGE a] :
    ∃ (I : CochainComplex C ℤ) (_ : I.IsStrictlyGE a),
      (∀ n, Injective (I.X n)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨I, hI, f, hf⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ⟨L, a, hL⟩ a
  have : QuasiIso f.hom := hf
  refine ⟨((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj,
    inferInstance, ?_, ⟨e ≪≫ asIso (DerivedCategory.Q.map f.hom)⟩⟩
  intro n
  exact inferInstanceAs (Injective ((InjectiveObject.ι C).obj (I.obj.X n)))

private lemma hasInjectiveAmplitude_of_injective_cycles (I : CochainComplex C ℤ)
    (a b : ℤ) [I.IsStrictlyGE a] [I.IsLE b] [∀ n, Injective (I.X n)]
    [Injective (I.cycles b)] :
    HasInjectiveAmplitude (DerivedCategory.Q.obj I) a b := by
  refine ⟨I.truncLE b, inferInstance, inferInstance, ?_,
    ⟨(asIso (DerivedCategory.Q.map (I.ιTruncLE b))).symm⟩⟩
  intro n
  rcases lt_trichotomy n b with hn | rfl | hn
  · exact Injective.of_iso (I.truncLEXIso b n hn).symm inferInstance
  · exact Injective.of_iso (I.truncLEXIsoCycles n).symm inferInstance
  · exact ((I.truncLE b).isZero_of_isStrictlyLE b n hn).injective

end

section Modules

variable {R : Type u} [CommRing R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]

private lemma isZero_homology_of_quotient_hom_eq_zero
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (h : ∀ f : (DerivedCategory.singleFunctor (ModuleCat.{v} R) n).obj
      (ModuleCat.of R (Shrink.{v} (R ⧸ (⊥ : Ideal R)))) ⟶ DerivedCategory.Q.obj I,
      f = 0) : IsZero (I.homology n) := by
  let e := (Shrink.linearEquiv R (R ⧸ (⊥ : Ideal R))).trans
    (Submodule.quotEquivOfEqBot _ rfl)
  have : Module.Projective R (Shrink.{v} (R ⧸ (⊥ : Ideal R))) :=
    Module.Projective.of_equiv e.symm
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx := hom_homology_eq_zero_of_single_hom_eq_zero I _ n h
    (ModuleCat.ofHom ((LinearMap.toSpanSingleton R (I.homology n) x).comp e.toLinearMap))
  have hx' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hx) (e.symm 1)
  change e (e.symm 1) • x = 0 at hx'
  simpa using hx'

private lemma injective_cycles_of_quotient_hom_eq_zero
    (I : CochainComplex (ModuleCat.{v} R) ℤ) [I.IsKInjective] (b : ℤ)
    [Injective (I.X b)]
    (h : ∀ (J : Ideal R)
      (f : (DerivedCategory.singleFunctor (ModuleCat.{v} R) (b + 1)).obj
        (ModuleCat.of R (Shrink.{v} (R ⧸ J))) ⟶ DerivedCategory.Q.obj I), f = 0) :
    Injective (I.cycles b) := by
  let S := ShortComplex.mk (I.iCycles b) (cokernel.π (I.iCycles b)) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel _) }
  exact (ModuleCat.injective_iff_subsingleton_ext_quotient_one _).2 fun J =>
    subsingleton_of_forall_eq 0
      (ext_one_eq_zero_of_surjective S hS _ (exists_lift_cokernel_cycles I _ b (h J)))

private lemma hasInjectiveAmplitude_of_quotient_ext_vanishing
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : ∀ (J : Ideal R) (n : ℤ), n < a ∨ b < n →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
          (ModuleCat.of R (Shrink.{v} (R ⧸ J)))) K n)) :
    HasInjectiveAmplitude K a b := by
  have hs (J : Ideal R) (n : ℤ) (hn : n < a ∨ b < n) :
      ∀ f : (DerivedCategory.singleFunctor (ModuleCat.{v} R) n).obj
        (ModuleCat.of R (Shrink.{v} (R ⧸ J))) ⟶ K, f = 0 :=
    (single_hom_eq_zero_iff _ K n).2 (fun f => @Subsingleton.elim _ (h J n hn) f 0)
  have hz (n : ℤ) (hn : n < a ∨ b < n) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K) := by
    let L := DerivedCategory.Q.objPreimage K
    let e := DerivedCategory.Q.objObjPreimageIso K
    have hL : IsZero (L.homology n) :=
      isZero_homology_of_quotient_hom_eq_zero L n (fun f => by
        rw [← cancel_mono e.hom, zero_comp]
        exact hs ⊥ n hn (f ≫ e.hom))
    exact hL.of_iso (((DerivedCategory.homologyFunctor _ n).mapIso e).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app L)
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2 (fun n hn => hz n (Or.inl hn))
  have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 (fun n hn => hz n (Or.inr hn))
  obtain ⟨I, ha, hI, ⟨e⟩⟩ := exists_injective_representative K a
  let := hI
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have : I.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e b
  have : Injective (I.cycles b) := injective_cycles_of_quotient_hom_eq_zero I b
    (fun J f => by
      rw [← cancel_mono e.inv, zero_comp]
      exact hs J (b + 1) (Or.inr (by omega)) (f ≫ e.inv))
  obtain ⟨T, hTa, hTb, hT, ⟨eT⟩⟩ := hasInjectiveAmplitude_of_injective_cycles I a b
  exact ⟨T, hTa, hTb, hT, ⟨e ≪≫ eT⟩⟩

end Modules

/-- **Stacks 0A5T.** An object of the derived category of modules has injective amplitude in
`[a, b]` if and only if its Ext groups from all modules vanish in degrees outside `[a, b]`; this
is in turn equivalent to testing the same vanishing only on quotients by ideals. -/
@[stacks 0A5T, ega "0 17.2.1" "partial"]
public lemma hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
    {R : Type u} [CommRing R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    (HasInjectiveAmplitude K a b ↔
      ∀ (N : ModuleCat.{v} R) (i : ℤ), i < a ∨ b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) K i)) ∧
    ((∀ (N : ModuleCat.{v} R) (i : ℤ), i < a ∨ b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) K i)) ↔
      ∀ (I : Ideal R) (i : ℤ), i < a ∨ b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
              (ModuleCat.of R (Shrink.{v} (R ⧸ I)))) K i)) := by
  have forward := ext_eq_zero_of_injective_amplitude K a b
  have backward := hasInjectiveAmplitude_of_quotient_ext_vanishing K a b
  have restrict :
      (∀ (N : ModuleCat.{v} R) (i : ℤ), i < a ∨ b < i →
        Subsingleton (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) K i)) →
      (∀ (I : Ideal R) (i : ℤ), i < a ∨ b < i →
        Subsingleton (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
            (ModuleCat.of R (Shrink.{v} (R ⧸ I)))) K i)) :=
    fun h I => h (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
  exact ⟨⟨fun h N i hi => subsingleton_of_forall_eq 0 (forward h N i hi),
    fun h => backward (restrict h)⟩,
    ⟨restrict, fun h N i hi => subsingleton_of_forall_eq 0 (forward (backward h) N i hi)⟩⟩

end ExtCriterion

section BoundedCriterion

private lemma exists_uniform_injective_dimension_bound
    {R : Type u} [CommRing R] [Small.{v} R]
    (X : ℤ → ModuleCat.{v} R) (a b : ℤ)
    (hX : ∀ i : ℤ, ∃ n : ℕ, HasInjectiveDimensionLE (X i) n) :
    ∃ d : ℕ, ∀ i ∈ Set.Icc a b,
      (CategoryTheory.ObjectProperty.binaryProductsClosure
        fun M : ModuleCat.{v} R => HasInjectiveDimensionLE M d).retractClosure (X i) := by
  choose n hn using hX
  let d := (Finset.Icc a b).sup n
  refine ⟨d, fun i hi => ?_⟩
  have hid : n i ≤ d := Finset.le_sup (by simpa using hi)
  have := hn i
  apply CategoryTheory.ObjectProperty.le_retractClosure _
  apply CategoryTheory.ObjectProperty.le_limitsClosure _ _
  exact hasInjectiveDimensionLT_of_ge (X i) (n i + 1) (d + 1) (by omega)

private lemma iSup_map_singleFunctor_le_iSup_shift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (E : CategoryTheory.ObjectProperty C) (a b : ℤ) :
    (⨆ i ∈ Set.Icc a b, E.map (DerivedCategory.singleFunctor C i)) ≤
      ⨆ i ∈ Set.Icc a b, (E.map (DerivedCategory.singleFunctor C 0)).isoClosure.shift i := by
  intro X hX
  obtain ⟨i, hXi⟩ := (CategoryTheory.ObjectProperty.prop_iSup_iff _ _).1 hX
  obtain ⟨hi, M, hM, ⟨e⟩⟩ := (CategoryTheory.ObjectProperty.prop_iSup_iff _ _).1 hXi
  refine (CategoryTheory.ObjectProperty.prop_iSup_iff _ _).2
    ⟨i, (CategoryTheory.ObjectProperty.prop_iSup_iff _ _).2 ⟨hi, ?_⟩⟩
  exact ⟨(DerivedCategory.singleFunctor C 0).obj M, ⟨M, hM, ⟨Iso.refl _⟩⟩,
    ⟨((shiftFunctor (DerivedCategory C) i).mapIso e.symm) ≪≫
      ((DerivedCategory.singleFunctors C).shiftIso i 0 i (by omega)).app M⟩⟩

private lemma subsingleton_single_hom_shift_of_hasInjectiveDimensionLE
    {R : Type u} [CommRing R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]
    (N M : ModuleCat.{v} R) (d : ℕ)
    (hM : HasInjectiveDimensionLE M d) (j : ℤ) (hj : j < 0 ∨ (d : ℤ) < j) :
    Subsingleton ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)⟦j⟧) := by
  refine subsingleton_of_forall_eq 0 fun f => ?_
  rcases hj with hj | hj
  · apply DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f 0 (-j) (by omega)
    · infer_instance
    · exact (DerivedCategory.TStructure.t.isGE_shift_iff _ 0 j (-j) (by omega)).2
        inferInstance
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
    have := HasInjectiveDimensionLT.subsingleton M (d + 1) n (by omega) N
    exact @Subsingleton.elim _ Abelian.Ext.homEquiv.symm.subsingleton f 0

-- closures by instance search exceeds the default synthesis budget.
private lemma hasInjectiveAmplitude_of_filtration
    {R : Type u} [CommRing R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) (d : ℕ) (_hab : a ≤ b)
    (hK : let E : CategoryTheory.ObjectProperty (ModuleCat.{v} R) :=
          fun M => HasInjectiveDimensionLE M d
        (CategoryTheory.ObjectProperty.extensionProductIter
          ((⨆ i ∈ Set.Icc a b,
            E.map (DerivedCategory.singleFunctor (ModuleCat.{v} R) i)).binaryProductsClosure)
          (b - a).toNat).retractClosure K) :
    HasInjectiveAmplitude K a (b + d) := by
  let C := ModuleCat.{v} R
  let E : CategoryTheory.ObjectProperty C := fun M => HasInjectiveDimensionLE M d
  let G : CategoryTheory.ObjectProperty (DerivedCategory C) :=
    E.map (DerivedCategory.singleFunctor C 0)
  have hbase :
      (⨆ i ∈ Set.Icc a b, E.map (DerivedCategory.singleFunctor C i)) ≤
        ⨆ i ∈ Set.Icc a b, G.isoClosure.shift i :=
    iSup_map_singleFunctor_le_iSup_shift E a b
  have hK' :
      (CategoryTheory.ObjectProperty.extensionProductIter
        ((⨆ i ∈ Set.Icc a b, G.isoClosure.shift i).binaryProductsClosure)
        (b - a).toNat).retractClosure K := by
    apply CategoryTheory.ObjectProperty.monotone_retractClosure
      (CategoryTheory.ObjectProperty.monotone_extensionProductIter
        (CategoryTheory.ObjectProperty.limitsClosure_monotone _ hbase) _)
    exact hK
  have hvanish (N : C) (i : ℤ) (hi : i ∉ Set.Icc (a + 0) (d + b)) :
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor C 0).obj N) K i) := by
    let H := preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.singleFunctor C 0).obj N))
    have hE : ∀ ⦃Y : DerivedCategory C⦄, G Y →
        ∀ j ∉ Set.Icc (0 : ℤ) d, Limits.IsZero (H.obj (Y⟦j⟧)) := by
      rintro Y ⟨M, hM, ⟨eM⟩⟩ j hj
      have hs := subsingleton_single_hom_shift_of_hasInjectiveDimensionLE N M d hM j
        (by simpa only [Set.mem_Icc, not_and_or, not_le] using hj)
      have hzero : Limits.IsZero
          (H.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦j⟧)) := by
        rw [Limits.IsZero.iff_id_eq_zero]
        apply AddCommGrpCat.hom_ext
        ext x
        exact hs.elim x 0
      exact hzero.of_iso (H.mapIso ((shiftFunctor (DerivedCategory C) j).mapIso eM.symm))
    have hz := CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter
      H G hE a b (b - a).toNat hK' (by simpa [add_comm] using hi)
    exact ⟨fun x y => by
      have hzid := hz.eq_of_src (𝟙 _) 0
      have hxy := congrArg (fun f => f.hom (x - y)) hzid
      change x - y = 0 at hxy
      exact sub_eq_zero.mp hxy⟩
  refine (hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
    K a (b + d)).1.mpr fun N i hi => hvanish N i ?_
  simp only [Set.mem_Icc]
  omega

/-- **Stacks 0A5V.** A bounded object of the derived category of modules has finite injective
dimension if all its cohomology modules have finite injective dimension. Likewise, a derived
object represented by a bounded complex whose terms all have finite injective dimension has
finite injective dimension. -/
@[stacks 0A5V]
public theorem hasFiniteInjectiveDimension_of_bounded
    {R : Type u} [CommRing R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) :
    ((∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) →
      (∀ i : ℤ, ∃ n : ℕ,
        HasInjectiveDimensionLE
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) n) →
      HasFiniteInjectiveDimension K) ∧
    (∀ (L : CochainComplex (ModuleCat.{v} R) ℤ),
      Nonempty (DerivedCategory.Q.obj L ≅ K) →
      (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) →
      (∀ i : ℤ, ∃ n : ℕ, HasInjectiveDimensionLE (L.X i) n) →
      HasFiniteInjectiveDimension K) := by
  constructor
  · rintro ⟨a, b, hge, hle⟩ hH
    let b' := max a b
    have hab' : a ≤ b' := le_max_left _ _
    obtain ⟨d, hd⟩ := exists_uniform_injective_dimension_bound
      (fun i => (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) a b' hH
    let : K.IsGE a := hge
    let : K.IsLE b := hle
    let : K.IsLE b' := DerivedCategory.TStructure.t.isLE_of_le K b b' (le_max_right _ _)
    refine ⟨a, b' + d, hasInjectiveAmplitude_of_filtration K a b' d hab' ?_⟩
    exact (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
      (fun M : ModuleCat.{v} R => HasInjectiveDimensionLE M d) hab').1 K hd
  · intro L ⟨e⟩
    rintro ⟨a, b, hge, hle⟩ hL
    let b' := max a b
    have hab' : a ≤ b' := le_max_left _ _
    obtain ⟨d, hd⟩ := exists_uniform_injective_dimension_bound L.X a b' hL
    let : L.IsStrictlyGE a := hge
    let : L.IsStrictlyLE b := hle
    let : L.IsStrictlyLE b' := L.isStrictlyLE_of_le b b' (le_max_right _ _)
    have hamp : HasInjectiveAmplitude (DerivedCategory.Q.obj L) a (b' + d) := by
      apply hasInjectiveAmplitude_of_filtration _ a b' d hab'
      exact (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
        (fun M : ModuleCat.{v} R => HasInjectiveDimensionLE M d) hab').2 L hd
    obtain ⟨I, hIa, hIb, hI, ⟨eI⟩⟩ := hamp
    exact ⟨a, b' + d, I, hIa, hIb, hI, ⟨e.symm ≪≫ eI⟩⟩

end BoundedCriterion

end StacksDraft.InjectiveDimension
