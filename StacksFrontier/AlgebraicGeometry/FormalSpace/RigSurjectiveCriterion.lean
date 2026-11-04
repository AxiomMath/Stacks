module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# A flatness criterion for rig-surjectivity

Let `A` be a Noetherian ring complete with respect to an ideal `I`, and let `C` be an
`I`-adically complete `A`-algebra. If `A/Iⁿ → C/IⁿC` is of finite type and flat for every `n`
and faithfully flat for `n = 1`, then `Spf C → Spf A` is rig-surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem`: a complete adic ring carrying
  a quotient system over `S` is smaller than the cutoff of the site.
* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_continuousHom`: a quotient system
  transports along a continuous ring map.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap`: the flatness criterion for
  rig-surjectivity of `Spf C → Spf A`.
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Cardinality

/-- The spectrum of a ring is smaller than the cutoff of the site iff the ring is. -/
private theorem size_spec_lt_cutoff_iff {R : Type u} [CommRing R] :
    (Spec (CommRingCat.of R)).size < B.cutoff ↔ #R < B.cutoff := by
  rw [Scheme.size_Spec, max_lt_iff, and_iff_right B.aleph0_lt_cutoff]

/-- A complete adic ring carrying a quotient system over `S` is smaller than the cutoff of the
site: it embeds into the product of its quotients by the powers of the defining ideal, each of
which is the ring of functions on a scheme the site contains, and the cutoff is a strong
prelimit cardinal of uncountable cofinality. -/
theorem mk_lt_cutoff_of_quotientSystem {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {I : Ideal A} (h : IsAdic I) (hc : IsAdicComplete I A)
    (D : QuotientSystem B S hS A) : #A < B.cutoff := by
  have hQ : ∀ n : ℕ, #(A ⧸ I ^ (n + 1)) < B.cutoff := by
    intro n
    exact size_spec_lt_cutoff_iff.mp
      (D.inSite ⟨I ^ (n + 1), TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic h n⟩)
  have hsup : (⨆ n : ℕ, #(A ⧸ I ^ (n + 1))) < B.cutoff :=
    lift_iSup_lt_of_lt_cof_ord
      (by rw [mk_nat, lift_aleph0, lift_id']; exact B.aleph0_lt_cutoff_cof) hQ
  have hinj : Function.Injective
      (fun a : A => fun n : ℕ => Ideal.Quotient.mk (I ^ (n + 1)) a) := by
    intro x y he
    refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n => ?_
    have hn := Ideal.Quotient.eq.mp (congrFun he n)
    simpa [SModEq.sub_mem] using Ideal.pow_le_pow_right (Nat.le_succ n) hn
  calc
    #A ≤ #(∀ n : ℕ, A ⧸ I ^ (n + 1)) := mk_le_of_injective hinj
    _ = Cardinal.prod (fun n : ℕ => #(A ⧸ I ^ (n + 1))) := mk_pi _
    _ ≤ Cardinal.prod (fun _ : ℕ => ⨆ n : ℕ, #(A ⧸ I ^ (n + 1))) :=
      prod_le_prod _ _ (fun n => le_ciSup bddAbove_of_small n)
    _ = (⨆ n : ℕ, #(A ⧸ I ^ (n + 1))) ^ ℵ₀ := by simp
    _ < B.cutoff := Cardinal.power_aleph0_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit hsup

end Cardinality

section Plumbing

variable {A C : Type u} [CommRing A] [CommRing C]

/-- A continuous ring map pulls every open ideal of its target back to an ideal containing a
weak ideal of definition of its source. -/
private theorem exists_weakIdeal_le_comap_ideal
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (φ : A →+* C) (hφ : Continuous φ)
    (K : Ideal C) (hK : IsOpen (K : Set C)) :
    ∃ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }, J.1 ≤ K.comap φ :=
  ⟨⟨hA.1.choose ⊓ K.comap φ,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hA.1.choose_spec
      (hK.preimage hφ)⟩, inf_le_right⟩

/-- Composing two quotient maps is the quotient map of the composition. -/
private theorem quotientMap_comp {R : Type u} [CommRing R] (φ : A →+* C) (ψ : C →+* R)
    (I : Ideal A) (J : Ideal C) (K : Ideal R) (hφ : I ≤ J.comap φ) (hψ : J ≤ K.comap ψ) :
    (Ideal.quotientMap K ψ hψ).comp (Ideal.quotientMap J φ hφ) =
      Ideal.quotientMap K (ψ.comp φ) (hφ.trans (Ideal.comap_mono hψ)) := by
  ext x
  rfl

/-- The structure map over `S` attached to a quotient of `C` does not depend on which weak
ideal of definition of `A` is used to factor it: any two are compared through their
intersection. -/
private theorem overS_quotientMap_eq [TopologicalSpace A] (D : QuotientSystem B S hS A)
    (φ : A →+* C)
    (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : Ideal C) (hJ : J.1 ≤ K.comap φ) (hL : L.1 ≤ K.comap φ) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ hJ)) ≫ D.overS J =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ hL)) ≫ D.overS L := by
  let M : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1 ⊓ L.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 L.2.1⟩
  rw [← D.compatible M J inf_le_left, ← D.compatible M L inf_le_right,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  rfl

/-- Transport a quotient system along a continuous ring map: the quotients of the target are
placed over `S` through a weak ideal of definition of the source which maps into them. -/
theorem exists_quotientSystem_continuousHom
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (φ : A →+* C) (hφ : Continuous φ) (hC : #C < B.cutoff) :
    ∃ (E : QuotientSystem B S hS C) (f : ContinuousHom D E), f.toRingHom = φ := by
  classical
  have hJ : ∀ K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I },
      (exists_weakIdeal_le_comap_ideal hA φ hφ K.1 K.2.1).choose.1 ≤ Ideal.comap φ K.1 :=
    fun K => (exists_weakIdeal_le_comap_ideal hA φ hφ K.1 K.2.1).choose_spec
  set J := fun K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I } =>
    (exists_weakIdeal_le_comap_ideal hA φ hφ K.1 K.2.1).choose
  refine ⟨{ inSite := ?_, overS := ?_, compatible := ?_ }, ⟨φ, hφ, ?_⟩, rfl⟩
  · intro K
    exact size_spec_lt_cutoff_iff.mpr
      ((mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := K.1))).trans_lt hC)
  · exact fun K => Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ (hJ K))) ≫
      D.overS (J K)
  · intro K L hKL
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have he : (Ideal.Quotient.factor hKL).comp (Ideal.quotientMap K.1 φ (hJ K)) =
        Ideal.quotientMap L.1 φ ((hJ K).trans (Ideal.comap_mono hKL)) := by
      ext x
      rfl
    rw [he]
    exact overS_quotientMap_eq D φ (J K) (J L) L.1 _ _
  · exact fun L K h => overS_quotientMap_eq D φ L (J K) K.1 h (hJ K)

/-- A continuous ring map out of the target of a continuous map over `S` is itself over `S`,
provided the composition is. -/
theorem exists_continuousHom_of_comp {R : Type u} [CommRing R]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C]
    [TopologicalSpace R]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} {F : QuotientSystem B S hS R}
    (f : ContinuousHom D E) (h : ContinuousHom D F) (g : C →+* R) (hg : Continuous g)
    (hcomp : g.comp f.toRingHom = h.toRingHom) :
    ∃ g' : ContinuousHom E F, g'.toRingHom = g := by
  refine ⟨⟨g, hg, fun J K hJK => ?_⟩, rfl⟩
  obtain ⟨I, hI⟩ := exists_weakIdeal_le_comap_ideal hA f.toRingHom f.continuous J.1 J.2.1
  rw [← f.overS I J hI, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotientMap_comp]
  have hIK : I.1 ≤ K.1.comap h.toRingHom := by
    rw [← hcomp]
    exact hI.trans (Ideal.comap_mono hJK)
  have he : Ideal.quotientMap K.1 (g.comp f.toRingHom)
      (hI.trans (Ideal.comap_mono hJK)) = Ideal.quotientMap K.1 h.toRingHom hIK := by
    ext x
    exact congrArg (Ideal.Quotient.mk K.1) (RingHom.congr_fun hcomp x)
  rw [he]
  exact h.overS I K hIK

/-- Continuous maps over `S` compose. -/
theorem exists_continuousHom_comp {R : Type u} [CommRing R]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [TopologicalSpace R]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} {F : QuotientSystem B S hS R}
    (f : ContinuousHom D E) (g : ContinuousHom E F)
    (hC : TopologicalRing.IsWeaklyAdmissible C) :
    ∃ gf : ContinuousHom D F, gf.toRingHom = g.toRingHom.comp f.toRingHom := by
  refine ⟨⟨g.toRingHom.comp f.toRingHom, g.continuous.comp f.continuous, fun I K hIK => ?_⟩, rfl⟩
  obtain ⟨J, hJK⟩ := exists_weakIdeal_le_comap_ideal hC g.toRingHom g.continuous K.1 K.2.1
  obtain ⟨L, hL⟩ := exists_weakIdeal_le_comap_ideal hA f.toRingHom f.continuous J.1 J.2.1
  rw [overS_quotientMap_eq D _ I L K.1 hIK (hL.trans (Ideal.comap_mono hJK)),
    ← quotientMap_comp f.toRingHom g.toRingHom L.1 J.1 K.1 hL hJK,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, f.overS L J hL]
  exact g.overS J K hJK

end Plumbing

/-- Let `A` be a Noetherian ring complete with respect to an ideal `I`, and let `C` be an
`I`-adically complete `A`-algebra. If `A/Iⁿ → C/IⁿC` is of finite type and flat for every `n`,
and faithfully flat for `n = 1`, then `Spf C → Spf A` is rig-surjective. -/
@[stacks 0AQX]
theorem isRigSurjective_formalSpectrumMap
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing A] (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    (hfinite : ∀ n : ℕ,
      Algebra.FiniteType (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (hfaithful : Module.FaithfullyFlat (A ⧸ I) (C ⧸ I.map (algebraMap A C)))
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C) :
    IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f) := by
  set hAweak := TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete
  have hCweak : TopologicalRing.IsWeaklyAdmissible C :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hCadic hCcomplete
  have hCft : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := by
    convert hfinite 1 using 2 <;> rw [pow_one]
  have hCnoeth : IsNoetherianRing C :=
    Rig.isNoetherianRing (Rig.AdicFiniteTypeAlgebra.of C hCcomplete)
  have hflatAC : Module.Flat A C := Module.Flat.of_flat_adic_reductions I hflat
  have hffAC : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_faithfullyFlat_reduction I (IsAdicComplete.le_jacobson_bot I)
  have hCcard : #C < B.cutoff := mk_lt_cutoff_of_quotientSystem hCadic hCcomplete E
  intro R _ _ _ _ _ _ hRtop hRcomplete hRweak DR p _
  obtain ⟨pR, hpR, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hAweak hRweak p
  let : Algebra A R := pR.toRingHom.toAlgebra
  have hIR : I.map (algebraMap A R) ≤ IsLocalRing.maximalIdeal R :=
    Ideal.map_le_maximalIdeal_of_continuous hAadic hRtop pR.toRingHom pR.continuous
  obtain ⟨W, hWring, hWdomain, hWdvr, hRW, hWext, hWcomplete, g, hg, hWcard⟩ :=
    exists_isAdicComplete_isDiscreteValuationRing_ringHom (C := C) (R := R) I hIR B.cutoff
      B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hCcard
      (mk_lt_cutoff_of_quotientSystem hRtop hRcomplete DR)
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWtop : IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R W) ≤ IsLocalRing.maximalIdeal W :=
    Ideal.map_le_iff_le_comap.mpr (by rw [IsLocalRing.maximalIdeal_comap])
  have hecont : Continuous (algebraMap R W) :=
    continuous_of_isAdic_of_map_le hRtop hWtop _ hmax
  obtain ⟨DW, e, he⟩ :=
    exists_quotientSystem_continuousHom hRweak DR (algebraMap R W) hecont hWcard
  obtain ⟨ep, hep⟩ := exists_continuousHom_comp hAweak pR e hRweak
  have hgcomp : g.comp f.toRingHom = ep.toRingHom := by
    rw [hep, he, hf]
    exact hg
  have hgI : (I.map (algebraMap A C)).map g ≤ IsLocalRing.maximalIdeal W := by
    rw [Ideal.map_map, hg, ← Ideal.map_map]
    exact (Ideal.map_mono hIR).trans hmax
  have hgcont : Continuous g := continuous_of_isAdic_of_map_le hCadic hWtop g hgI
  obtain ⟨g', hg'⟩ := exists_continuousHom_of_comp hAweak f ep g hgcont hgcomp
  refine ⟨W, hWring, hWdomain, hWdvr, hRW, hWext, inferInstance, hWtopring, hWlin, hWtop,
    hWcomplete, DW, e, formalSpectrumMap hCweak g', he, ?_⟩
  rw [formalSpectrumMap_comp hAweak hCweak f g' ep (by rw [hg']; exact hgcomp.symm), ← hpR,
    formalSpectrumMap_comp hAweak hRweak pR e ep hep]

end AlgebraicGeometry.FormalSpace

end
