module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocalRefined
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import all StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Tautness of a homomorphism whose formal spectrum map is representable

Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S`. **Stacks 0AN5** says that `Spf φ : Spf C ⟶ Spf A` is representable by algebraic
spaces exactly when it is representable by objects of the site, and exactly when `φ` is taut.
This file proves the implication from representability by objects of the site — condition (2)
of that lemma — to tautness.

## Main results

* `AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_closure_map_of_isPullback_stage`: the
  closure of the extended ideal is a weak ideal of definition, from the cartesian square
  presenting the stage base change by an object of the site.
* `AlgebraicGeometry.FormalSpace.isTaut_of_isWeakIdealOfDefinition_closure_map`: a continuous
  homomorphism is taut once the closure of the extension of every weak ideal of definition is a
  weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap`: a
  continuous homomorphism whose formal spectrum map is representable by objects of the site is
  taut.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AMS](https://stacks.math.columbia.edu/tag/0AMS)
* [Stacks Project, Tag 0AMW](https://stacks.math.columbia.edu/tag/0AMW)
* [Stacks Project, Tag 0AMY](https://stacks.math.columbia.edu/tag/0AMY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- The weak ideal of definition of `C` classifying the base change of `Spf φ` along a stage
`Spec (A ⧸ I)` of `Spf A`, together with the two inclusions characterising it: it contains the
extension of `I` and is contained in every weak ideal of definition of `C` that does. -/
private theorem exists_weakIdeal_classifying_stage_baseChange
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (V : BigFppfOver B S hS)
    (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
    (q : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (hpb : IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      (formalSpectrumMap hA f) (formalSpectrumInclusion D I)) :
    ∃ J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J },
      I.1.map f.toRingHom ≤ J.1 ∧
        ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
          I.1.map f.toRingHom ≤ K.1 → J.1 ≤ K.1 := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)
  let _ : (MorphismProperty.relative F
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hp : (MorphismProperty.relative F
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
      (formalSpectrumInclusion_isThickening B S hS hA D I)
  obtain ⟨J, e, he⟩ := (existsUnique_weakIdeal_quotient B S hS C (formalSpectrum E)
    E.weakIdealColimitPresentation hC V p hp.rep hp).exists
  change F.map e.hom ≫ formalSpectrumInclusion E J = p at he
  refine ⟨OrderDual.ofDual J, ?_, ?_⟩
  · exact map_ideal_le_of_formalSpectrum_square B S hS hA D E f I (OrderDual.ofDual J)
      (e.inv ≫ q) (comp_eq_of_map_iso F e _ p _ q _ he hpb.w)
  · intro K hIK
    have hIK' : I.1 ≤ Ideal.comap f.toRingHom K.1 := Ideal.map_le_iff_le_comap.mp hIK
    have hcomm : formalSpectrumInclusion E (OrderDual.toDual K) ≫ formalSpectrumMap hA f =
        F.map (T.map (f.stageMap I K hIK')) ≫ formalSpectrumInclusion D I :=
      formalSpectrumMap_spec hA f I K hIK'
    set t := hpb.lift (formalSpectrumInclusion E (OrderDual.toDual K))
      (F.map (T.map (f.stageMap I K hIK'))) hcomm with ht
    have htp : t ≫ p = formalSpectrumInclusion E (OrderDual.toDual K) := hpb.lift_fst _ _ _
    obtain ⟨s, hs⟩ := F.map_surjective t
    refine ideal_le_of_stage_factorization B S hS hC.1 E K (OrderDual.ofDual J)
      (s ≫ e.hom) ?_
    change F.map (s ≫ e.hom) ≫ formalSpectrumInclusion E J =
      formalSpectrumInclusion E (OrderDual.toDual K)
    refine Eq.trans (F.map_comp_assoc s e.hom (formalSpectrumInclusion E J)) ?_
    refine Eq.trans (congrArg (fun z ↦ F.map s ≫ z) he) ?_
    exact Eq.trans (congrArg (fun z ↦ z ≫ p) hs) htp

/-- The closure of the extended ideal is a weak ideal of definition of `C`, from the cartesian
square presenting the base change of `Spf φ` along the stage `Spec (A ⧸ I)` by an object of the
site. -/
theorem isWeakIdealOfDefinition_closure_map_of_isPullback_stage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (V : BigFppfOver B S hS)
    (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
    (q : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (hpb : IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      (formalSpectrumMap hA f) (formalSpectrumInclusion D I)) :
    TopologicalRing.IsWeakIdealOfDefinition (Ideal.closure (I.1.map f.toRingHom)) := by
  obtain ⟨J, hIJ, hmin⟩ :=
    exists_weakIdeal_classifying_stage_baseChange B S hS hA hC D E f I V p q hpb
  have hnil : Ideal.closure (I.1.map f.toRingHom) ≤ topologicalNilradical C :=
    TopologicalRing.closure_map_le_topologicalNilradical f.toRingHom f.continuous I.1
      (fun x hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (I.2.2 x hx))
  have hle : Ideal.closure (I.1.map f.toRingHom) ≤ J.1 :=
    closure_minimal hIJ (J.1.toAddSubgroup.isClosed_of_isOpen J.2.1)
  have hge : J.1 ≤ Ideal.closure (I.1.map f.toRingHom) := by
    intro x hx
    rw [TopologicalRing.mem_closure_iff_forall_sup_open]
    intro L hL
    obtain ⟨K₀, hK₀, hK₀L⟩ :=
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).mem_iff.mp
        (hL.mem_nhds L.zero_mem)
    have hKwid : TopologicalRing.IsWeakIdealOfDefinition
        (Ideal.closure (I.1.map f.toRingHom) ⊔ K₀) := by
      refine ⟨Ideal.isOpen_of_isOpen_subideal le_sup_right hK₀.1, fun y hy ↦ ?_⟩
      refine IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ?_
      exact sup_le hnil
        (fun z hz ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hK₀.2 z hz)) hy
    have hsup : Ideal.closure (I.1.map f.toRingHom) ⊔ K₀ ≤ I.1.map f.toRingHom ⊔ L := by
      refine sup_le (fun y hy ↦ ?_) (le_trans (fun y hy ↦ hK₀L hy) le_sup_right)
      exact (TopologicalRing.mem_closure_iff_forall_sup_open _ y).mp hy L hL
    exact hsup (hmin ⟨_, hKwid⟩ (le_trans (fun y hy ↦ subset_closure hy) le_sup_left) hx)
  rw [le_antisymm hle hge]
  exact J.2

/-- A continuous homomorphism of weakly admissible topological rings is taut as soon as the
closure of the extension of every weak ideal of definition of the source is a weak ideal of
definition of the target. -/
theorem isTaut_of_isWeakIdealOfDefinition_closure_map
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (φ : A →+* C) (hφ : Continuous φ)
    (hwid : ∀ I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      TopologicalRing.IsWeakIdealOfDefinition (Ideal.closure (I.1.map φ))) :
    RingHom.IsTaut φ := by
  rw [RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition φ hφ hA]
  refine ⟨fun I hI ↦ hwid ⟨I, hI⟩, ?_⟩
  refine (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).to_hasBasis
    (fun K hK ↦ ?_) (fun I hI ↦ ⟨Ideal.closure (I.map φ), hwid ⟨I, hI⟩, subset_rfl⟩)
  obtain ⟨I, hIK⟩ := exists_weakIdeal_below_comap hA φ hφ ⟨K, hK⟩
  exact ⟨I.1, I.2, closure_minimal (Ideal.map_le_iff_le_comap.mpr hIK)
    (K.toAddSubgroup.isClosed_of_isOpen hK.1)⟩

/-- A continuous homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S` whose
formal spectrum map is representable by objects of the site is taut. -/
theorem isTaut_of_relativelyRepresentable_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hrep : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap hA f)) :
    RingHom.IsTaut f.toRingHom :=
  isTaut_of_isWeakIdealOfDefinition_closure_map hA hC f.toRingHom f.continuous fun I ↦
    isWeakIdealOfDefinition_closure_map_of_isPullback_stage B S hS hA hC D E f I
      (hrep.pullback (formalSpectrumInclusion D I)) (hrep.fst _) (hrep.snd _)
      (hrep.isPullback _)

end AlgebraicGeometry.FormalSpace

end
