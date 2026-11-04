module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable

/-!
# Tautness of a representable morphism of formal spectra

Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S`. If `Spf φ : Spf C ⟶ Spf A` is representable — every base change of it along a point
of `Spf A` coming from an object of the site is again such an object — then `φ` is taut. This is
the implication (2) ⟹ (3) of **Stacks 0AN5**. Only the base changes along the quotient stages
of `Spf A` are used, and those stages are affine, so the same argument runs from condition (1)
of Stacks 0AN5 through Stacks 0AKN over the affine test objects of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap`:
  **Stacks 0AN5**, the implication from its condition (2) to its condition (3).
* `AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`:
  **Stacks 0AN5**, the implication from its condition (1) to its condition (3).
* `AlgebraicGeometry.FormalSpace.isTaut_of_isClosedImmersionInto_formalSpectrumMap`: the
  consequence for a closed immersion of formal spectra, a closed immersion being representable
  by definition.

## Implementation notes

The argument is the one of Stacks 0AN5. Fix a weak ideal of definition `I ⊆ A`. The stage
inclusion `Spec (A ⧸ I) ⟶ Spf A` is a representable thickening, so its base change along
`Spf φ` is one too; representability of `Spf φ` makes the source of that base change an object
of the site, and Stacks 0AIC then identifies it with a quotient stage `Spec (C ⧸ J)` over
`Spf C` for a unique weak ideal of definition `J ⊆ C`. Two comparisons pin `J` down. Reading
the resulting commuting square on quotient rings gives `IC ⊆ J`. Conversely, for any weak ideal
of definition `K ⊆ C` with `IC ⊆ K` the stage `Spec (C ⧸ K)` maps into the base change, so `J`
is contained in `K`. Hence `J` is the smallest weak ideal of definition containing `IC`, which
forces `J` to be the closure of `IC`; in particular that closure is open, and openness of the
closures of the extended weak ideals of definition is tautness.

The hypothesis is therefore isolated as the existence, for every weak ideal of definition `I`
of `A`, of a cartesian square exhibiting the base change of `Spf φ` along the stage inclusion
of `I` as an object of the site. Condition (2) supplies it directly; condition (1) supplies it
through Stacks 0AKN, which is available in this library over exactly the test objects with
affine underlying scheme, and `Spec (A ⧸ I)` is one. Stacks 0AKN consumes of the two formal
spectra only their presentations as directed colimits of affine objects of the site along
thickenings, which for a formal spectrum are its construction, so neither implication assumes
anything about the size of the site.

The last step — that the smallest weak ideal of definition above an ideal of topologically
nilpotent elements is its closure — uses that the weak ideals of definition of a weakly
admissible ring are a neighbourhood basis of zero, so that the closure of an ideal is the
intersection of its translates by them.

Only openness of the extended closures has to be checked: for a continuous homomorphism of
weakly admissible rings it already implies the basis condition in the definition of tautness,
because the weak ideals of definition of the source are cofinal among the preimages of the open
ideals of the target.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AMY](https://stacks.math.columbia.edu/tag/0AMY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### Tautness from openness of the extended closures -/

section Rings

variable {A C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- An open ideal contained in the topological nilradical is a weak ideal of definition. -/
private theorem isWeakIdealOfDefinition_of_isOpen_of_le_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R] {I : Ideal R}
    (hopen : IsOpen (I : Set R)) (hle : I ≤ topologicalNilradical R) :
    TopologicalRing.IsWeakIdealOfDefinition I :=
  ⟨hopen, fun _ hy ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp (hle hy)⟩

/-- A continuous homomorphism of weakly admissible topological rings is taut as soon as the
closure of the extension of every weak ideal of definition of the source is open: the weak
ideals of definition of the source are cofinal among the preimages of the open ideals of the
target, so the basis condition is automatic. -/
private theorem isTaut_iff_isOpen_closure_map_weakIdeal (φ : A →+* C) (hφ : Continuous φ)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C) :
    RingHom.IsTaut φ ↔ ∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      IsOpen (Ideal.closure (I.map φ) : Set C) := by
  refine ⟨fun h I hI ↦ h.1 I hI.1, fun h ↦ ?_⟩
  refine (RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition φ hφ hA hC).2 ⟨fun I hI ↦
    isWeakIdealOfDefinition_of_isOpen_of_le_topologicalNilradical (h I hI)
      (TopologicalRing.closure_map_le_topologicalNilradical φ hφ I
        (TopologicalRing.le_topologicalNilradical_of_isWeakIdealOfDefinition hI)), ?_⟩
  refine IsLinearTopology.hasBasis_open_ideal.to_hasBasis (fun K hK ↦ ?_)
    (fun I hI ↦ ⟨Ideal.closure (I.map φ), h I hI, Set.Subset.rfl⟩)
  obtain ⟨I, hI, hIK⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).mem_iff.mp
      ((hK.preimage hφ).mem_nhds (by simp))
  exact ⟨I, hI, closure_minimal (Ideal.map_le_iff_le_comap.mpr hIK)
    (K.toAddSubgroup.isClosed_of_isOpen hK)⟩

/-- The smallest weak ideal of definition above an ideal of topologically nilpotent elements of
a weakly admissible ring is the closure of that ideal. -/
private theorem closure_eq_of_isWeakIdealOfDefinition_least
    (hC : TopologicalRing.IsWeaklyAdmissible C) (I J : Ideal C)
    (hI : I ≤ topologicalNilradical C) (hJ : TopologicalRing.IsWeakIdealOfDefinition J)
    (hIJ : I ≤ J)
    (hmin : ∀ K : Ideal C, TopologicalRing.IsWeakIdealOfDefinition K → I ≤ K → J ≤ K) :
    Ideal.closure I = J := by
  refine le_antisymm (closure_minimal hIJ (J.toAddSubgroup.isClosed_of_isOpen hJ.1))
    fun x hx ↦ ?_
  change x ∈ closure (I : Set C)
  rw [← (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition
    hC).iInter_add_right_eq_closure]
  refine Set.mem_iInter.mpr fun K ↦ Set.mem_iInter.mpr fun hK ↦ ?_
  have hIK : TopologicalRing.IsWeakIdealOfDefinition (I ⊔ K) :=
    isWeakIdealOfDefinition_of_isOpen_of_le_topologicalNilradical
      (Ideal.isOpen_of_isOpen_subideal le_sup_right hK.1)
      (sup_le hI (TopologicalRing.le_topologicalNilradical_of_isWeakIdealOfDefinition hK))
  exact Submodule.mem_sup.mp (hmin (I ⊔ K) hIK le_sup_left hx)

end Rings

/-! ### The weak ideal classifying the base change of a stage -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The canonical quotient stage of Stacks 0AIC attached to the canonical weak-ideal colimit
presentation of a formal spectrum is the stage inclusion of that formal spectrum. -/
private theorem quotientMap_weakIdealColimitPresentation (D : QuotientSystem B S hS A)
    (I : WeakIdeals A) :
    quotientMap B S hS A (formalSpectrum D) D.weakIdealColimitPresentation I =
      formalSpectrumInclusion D I :=
  Category.comp_id _

/-- The base change of a stage inclusion of the target along a morphism of formal spectra is a
stage inclusion of the source. Stacks 0AIC classifies representable thickenings into `Spf C` by
the weak ideals of definition of `C`, and the base change of the representable thickening
`Spec (A ⧸ I) ⟶ Spf A` is such a thickening as soon as it is represented by an object of the
site. -/
private theorem exists_weakIdeal_of_isPullback_formalSpectrumInclusion
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (V : BigFppfOver B S hS)
    (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
    (q : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (hpb : IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      (formalSpectrumMap hA f) (formalSpectrumInclusion D I)) :
    ∃ (J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J })
      (e : V ≅ (BigAffineFppf.inclusion B S hS).obj (E.stage J)),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map e.hom ≫
        formalSpectrumInclusion E J = p := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : Nonempty { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have hp : Q.relative F p := Q.relative_isStableUnderBaseChange.of_isPullback hpb.flip
    (formalSpectrumInclusion_isThickening' B S hS D I)
  obtain ⟨J, e, he⟩ := (existsUnique_weakIdeal_quotient B S hS C (formalSpectrum E)
    E.weakIdealColimitPresentation hC V p hp.rep hp).exists
  exact ⟨J, e, by rwa [quotientMap_weakIdealColimitPresentation B S hS E J] at he⟩

/-! ### Stacks 0AN5, towards condition (3) -/

/-- **The core of the implication to condition (3) of Stacks 0AN5.** A continuous homomorphism
`φ : A ⟶ C` of weakly admissible topological rings over `S` is taut as soon as the base change
of `Spf φ` along every quotient stage `Spec (A ⧸ I) ⟶ Spf A` is represented by an object of the
site.

Only the quotient stages are tested, and they are affine; both conditions (1) and (2) of Stacks
0AN5 supply that much. -/
private theorem isTaut_of_isPullback_formalSpectrumInclusion
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hstage : ∀ I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ (V : BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
        (q : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)),
        IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
          (formalSpectrumMap hA f) (formalSpectrumInclusion D I)) :
    RingHom.IsTaut f.toRingHom := by
  refine (isTaut_iff_isOpen_closure_map_weakIdeal f.toRingHom f.continuous hA hC).2 fun I hI ↦ ?_
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let i : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } := ⟨I, hI⟩
  let ξ := formalSpectrumInclusion D i
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : F.Full := inferInstanceAs
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full)
  have _ : F.Faithful := inferInstanceAs
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful)
  obtain ⟨V, p, q, hpb⟩ := hstage i
  obtain ⟨J, e, he⟩ :=
    exists_weakIdeal_of_isPullback_formalSpectrumInclusion B S hS hA hC D E f i V p q hpb
  have hIJ : I.map f.toRingHom ≤ J.1 :=
    map_ideal_le_of_formalSpectrum_square B S hS hA D E f i J (e.inv ≫ q)
      (comp_eq_of_map_iso F e _ _ _ _ ξ he hpb.w)
  have hmin (K : Ideal C) (hK : TopologicalRing.IsWeakIdealOfDefinition K)
      (hIK : I.map f.toRingHom ≤ K) : J.1 ≤ K := by
    let k : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K } := ⟨K, hK⟩
    have hIK' := Ideal.map_le_iff_le_comap.mp hIK
    have hk : formalSpectrumInclusion E k ≫ formalSpectrumMap hA f =
        F.map (T.map (f.stageMap i k hIK')) ≫ ξ :=
      formalSpectrumMap_spec hA f i k hIK'
    let l := hpb.lift (formalSpectrumInclusion E k) (F.map (T.map (f.stageMap i k hIK'))) hk
    refine ideal_le_of_stage_factorization B S hS hC.1 E k J
      (F.preimage (l ≫ F.map e.hom)) ?_
    rw [F.map_preimage, Category.assoc, he]
    exact hpb.lift_fst _ _ hk
  rw [closure_eq_of_isWeakIdealOfDefinition_least hC (I.map f.toRingHom) J.1
    (TopologicalRing.closure_map_le_topologicalNilradical f.toRingHom f.continuous I
      (TopologicalRing.le_topologicalNilradical_of_isWeakIdealOfDefinition hI)
      |>.trans' (fun _ hx ↦ subset_closure hx))
    J.2 hIJ hmin]
  exact J.2.1

/-- **Stacks 0AN5**, the implication from its condition (1) to its condition (3): if the formal
spectrum of a continuous homomorphism `φ : A ⟶ C` of weakly admissible topological rings over
`S` is representable by algebraic spaces, then `φ` is taut.

Only the base changes along the quotient stages of `Spf A` are needed, and those stages are
affine, so what carries the step from condition (1) to condition (2) is Stacks 0AKN over the
test objects of the site with affine underlying scheme,
`AlgebraicGeometry.FormalSpace.exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces`.
That statement consumes of each of the two formal spectra only its presentation as a directed
colimit of affine objects of the site along thickenings, and for a formal spectrum that
presentation is its construction
(`AlgebraicGeometry.FormalSpace.hasThickeningPresentation_formalSpectrum`). So nothing is
assumed here beyond condition (1) — in particular no bound on the size of the site, which is
what asking the two formal spectra to be affine formal algebraic spaces would amount to. -/
@[stacks 0AN5 "(1) implies (3)"]
theorem isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hA f).hom) :
    RingHom.IsTaut f.toRingHom := by
  refine isTaut_of_isPullback_formalSpectrumInclusion B S hS hA hC D E f fun I ↦ ?_
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.stage I))) :=
    inferInstanceAs (IsAffine (Spec (.of (A ⧸ I.1))))
  obtain ⟨V, p, q, hpb, -, -⟩ :=
    exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces' B S hS
      (formalSpectrumMap hA f) (hasThickeningPresentation_formalSpectrum hC E)
      (hasThickeningPresentation_formalSpectrum hA D) hrep
      ((BigAffineFppf.inclusion B S hS).obj (D.stage I)) inferInstance
      (formalSpectrumInclusion D I)
  exact ⟨V, p, q, hpb⟩

/-- A closed immersion of formal spectra of weakly admissible topological rings over `S` comes
from a taut homomorphism: a closed immersion is representable, so **Stacks 0AN5** applies. -/
@[stacks 0AN5 "(2) implies (3), for a closed immersion"]
theorem isTaut_of_isClosedImmersionInto_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : IsClosedImmersionInto B S hS (formalSpectrumMap hA f)) :
    RingHom.IsTaut f.toRingHom :=
  isTaut_of_relativelyRepresentable_formalSpectrumMap B S hS hA hC D E f hf.rep

end AlgebraicGeometry.FormalSpace

end
