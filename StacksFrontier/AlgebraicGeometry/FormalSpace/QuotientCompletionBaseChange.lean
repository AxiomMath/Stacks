module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Base change of the formal spectrum of a completed quotient

Let `S` be a scheme contained in a big fppf site `B`, let `A` be a weakly admissible
topological ring over `S` and let `K ⊆ A` be an ideal. **Stacks 0ANR** considers

`C = (A/K)^∧ = lim_{I ⊆ A w.i.d.} A/(I + K)`

and the morphism `Spf C ⟶ Spf A` it induces, and identifies the base change of that morphism
along a morphism `T ⟶ Spf A` out of a quasi-compact scheme: such a morphism factors through
`Spec (A/I)` for some weak ideal of definition `I ⊆ A` by Stacks 0AIA, and then

`T ×_{Spf A} Spf C = T ×_{Spec (A/I)} Spec (A/(K + I))`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.quotientCompletionStageIdeal`: the weak ideal of definition
  `ker (C → A/(I + K))` of `C` attached to a weak ideal of definition `I` of `A`.
* `AlgebraicGeometry.FormalSpace.quotientCompletionStageEquiv`: the identification
  `C ⧸ ker (C → A/(I + K)) ≃+* A ⧸ (K + I)`, which is the displayed description of the
  quotient stages of `C`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_quotientCompletion_stage`:
  the square formed by the two stage inclusions and `Spf C ⟶ Spf A` is cartesian, so that
  `Spec (A/(K + I)) = Spf C ×_{Spf A} Spec (A/I)`.
* `AlgebraicGeometry.FormalSpace.isPullback_baseChange_quotientCompletion`: **Stacks 0ANR**,
  the base-change identification, for a morphism into `Spf A` which factors through the stage
  `Spec (A/I)`.
* `AlgebraicGeometry.FormalSpace.surjective_quotientMap_quotientCompletionStageIdeal` and
  `AlgebraicGeometry.FormalSpace.isClosedImmersion_quotientCompletion_stageMap`: the stage
  morphism `Spec (A/(K + I)) ⟶ Spec (A/I)` is `Spec` of a surjection, hence a closed
  immersion of schemes.
* `FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_quotientCompletion`:
  `Spf ((A/K)^∧) ⟶ Spf A` is representable by algebraic spaces over `S`, which is what
  Example 0AN6 contributes to the source's argument.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_formalSpectrumMap_quotientCompletion`:
  **Stacks 0ANR**, the conclusion. `Spf ((A/K)^∧) ⟶ Spf A` is a closed immersion of formal
  algebraic spaces over `S`, in the sense of Stacks 0ANP.

## Implementation notes

The ring `C` is `TopologicalRing.CompletionOver (Ideal.Quotient.mk K)`: the completion of
`A/K` along the extensions of the weak ideals of definition of `A`, whose quotient by the
kernel of its projection at `I` is `(A/K) ⧸ I(A/K) = A/(K + I)`. The identification of that
quotient with `A/(K + I)` is `quotientCompletionStageEquiv`; the projection is surjective by
`TopologicalRing.CompletionOver.projection_surjective`, so no completeness input is needed for
it.

A quotient-system presentation `E` of `C` over `S` is a hypothesis rather than a construction,
exactly as in `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum`:
`AlgebraicGeometry.FormalSpace.QuotientSystem` asks that every quotient spectrum
`Spec (C ⧸ J)` lie in the chosen big fppf site and carry a structure morphism to `S`, which is
site-smallness data about the base rather than mathematical input. For the same reason the
continuous homomorphism `A ⟶ C` over `S` is a hypothesis whose underlying ring map is required
to be the canonical one.

The cartesian stage square is the one of Stacks 0AN5,
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage`, applied to the canonical
map `A → C`: its hypothesis that the weak ideal of definition of `C` cutting out the stage be
the closure of the extended ideal is
`TopologicalRing.CompletionOver.ker_projection_eq_closure`, so the stage of `Spf C` over the
stage `Spec (A/I)` of `Spf A` is exactly `Spec (A/(K + I))`. Tautness of `A → C`
(`TopologicalRing.isTaut_canonicalMap`) is therefore not needed as a separate
input here, being subsumed by that identification of the kernel.

Closedness of `K` is not used below. It is what makes `K` the kernel of `A → C`
(`TopologicalRing.ker_canonicalMap_eq`), which is the last assertion of the source's example
and is proved in `StacksFrontier.Topology.Algebra.AdicTopology.ClosedImmersion`; the base-change
assertion holds for an arbitrary ideal `K`.

The source states its base change for a morphism `T ⟶ Spf A` out of a *quasi-compact scheme*
and produces the factorisation through `Spec (A/I)` from Stacks 0AIA
(`AlgebraicGeometry.exists_factor_through_thickening`, and
`AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage` for an affine source). The
factorisation is therefore taken as the hypothesis of
`AlgebraicGeometry.FormalSpace.isPullback_baseChange_quotientCompletion` rather than
re-derived, and the statement is made for an arbitrary fppf sheaf `T` over `S`, which is the
generality the pasting argument has.

*Representability.* The source reads representability off Example 0AN6, which refers in turn to
Stacks 0AN5 and so asks for a fibre product over an arbitrary scheme-valued point. What is used
here instead is Zariski locality of representability on the target,
`AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover`: a point
`T ⟶ Spf A` is covered, surjectively and étale, by the coproduct `V` of the affine opens of `T`
(`AlgebraicGeometry.BigFppfOver.exists_affineOpens_surjective_etale_sigma`). Each affine open is
quasi-compact, so its point of `Spf A` factors through a stage `Spec (A/I)` by Stacks 0AIA
(`AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage`), and the cartesian stage square
above identifies the fibre product over it with the object
`X_i ×_{Spec (A/I)} Spec (A/(K + I))` of the site, a closed subscheme of `X_i`. Coproducts in
the topos of fppf sheaves are universal
(`CategoryTheory.Sheaf.nonempty_isColimit_cofanMk_of_isPullback`), so the fibre product over `V`
is the coproduct of those over the affine opens; that coproduct is again an object of the site
because a closed immersion does not raise the size of a scheme
(`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`), so the single cardinal `T.size`
bounds both the index of the family and each of its members, which is exactly what
`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le` asks for.

*The closed-immersion conclusion.* With representability available this is the descent step of
Stacks 0GHY, `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_locallySurjectiveFamily`,
applied to the family of stage inclusions `{Spec (A/I) ⟶ Spf A}` indexed by the universe lift of
the weak ideals of definition of `A`. That family is jointly surjective because `Spf A` is the
colimit of its stages, and the base change of `Spf ((A/K)^∧) ⟶ Spf A` along each member is the
stage morphism `Spec (A/(K + I)) ⟶ Spec (A/I)`, a closed immersion of schemes by
`AlgebraicGeometry.FormalSpace.isClosedImmersion_quotientCompletion_stageMap`. Passing from a
closed immersion of the site to one of formal algebraic spaces is
`AlgebraicGeometry.FormalSpace.isClosedImmersion_of_isClosedImmersionInto`.

Tautness of `A → C` — `TopologicalRing.isTaut_canonicalMap`, which is condition (3) of Stacks
0AN5 for this map — is therefore not used: the stage identification of
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_quotientCompletion_stage` already
supplies everything the representability argument needs.

## References

* [Stacks Project, Tag 0ANR](https://stacks.math.columbia.edu/tag/0ANR)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Ring

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The completed quotient `(A/K)^∧ = lim_{I w.i.d.} A/(I + K)` of a topological ring by an
ideal: the completion of `A/K` along the extensions of the weak ideals of definition of `A`. -/
abbrev quotientCompletion (K : Ideal A) : Type u :=
  TopologicalRing.CompletionOver (Ideal.Quotient.mk K)

variable [IsTopologicalRing A] [IsLinearTopology A A]

/-- The weak ideal of definition `ker (C → A/(I + K))` of the completed quotient
`C = (A/K)^∧` attached to a weak ideal of definition `I` of `A`. -/
def quotientCompletionStageIdeal (K : Ideal A)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    TopologicalRing.WeakIdealOfDefinitionIndex (quotientCompletion K) :=
  ⟨RingHom.ker (TopologicalRing.CompletionOver.projection (Ideal.Quotient.mk K) I),
    TopologicalRing.projection_ker_isWeakIdealOfDefinition
      (Ideal.Quotient.mk K) I⟩

/-- **The quotient stages of `C = (A/K)^∧`.** The quotient of the completed quotient by the
weak ideal of definition `ker (C → A/(I + K))` is `A/(K + I)`: the projection
`C → (A/K) ⧸ I(A/K)` is surjective, and `(A/K) ⧸ I(A/K) = A/(K + I)`. -/
def quotientCompletionStageEquiv (K : Ideal A)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    (quotientCompletion K ⧸ (quotientCompletionStageIdeal K I).1) ≃+* A ⧸ (K ⊔ I.1) :=
  (RingHom.quotientKerEquivOfSurjective
      (TopologicalRing.CompletionOver.projection_surjective (Ideal.Quotient.mk K) I)).trans
    (DoubleQuot.quotQuotEquivQuotSup K I.1)

/-- A weak ideal of definition of `A` is carried into the stage ideal of the completed
quotient by the canonical map. -/
theorem le_comap_quotientCompletionStageIdeal (K : Ideal A)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    I.1 ≤ Ideal.comap
      (TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K))
      (quotientCompletionStageIdeal K I).1 := by
  intro x hx
  change TopologicalRing.CompletionOver.projection (Ideal.Quotient.mk K) I
    (TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K) x) = 0
  rw [TopologicalRing.CompletionOver.projection_canonicalMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_map_of_mem (Ideal.Quotient.mk K) hx)

/-- The stage ideal of the completed quotient is the closure of the ideal extended along the
canonical map, which is the form in which the base change of Stacks 0AN5 asks for it. -/
theorem quotientCompletionStageIdeal_eq_closure (K : Ideal A)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    (quotientCompletionStageIdeal K I).1 =
      (I.1.map
        (TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K))).closure :=
  TopologicalRing.CompletionOver.ker_projection_eq_closure (Ideal.Quotient.mk K) I

end Ring

section Geometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  {K : Ideal A}

variable (hA : TopologicalRing.IsWeaklyAdmissible A)
  (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS (quotientCompletion K))
  (φ : ContinuousHom D E)
  (hφ : φ.toRingHom =
    TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K))

include hφ in
/-- The canonical map carries a weak ideal of definition of `A` into the stage ideal of the
completed quotient. -/
theorem continuousHom_le_comap_quotientCompletionStageIdeal
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    I.1 ≤ Ideal.comap φ.toRingHom (quotientCompletionStageIdeal K I).1 := by
  rw [hφ]
  exact le_comap_quotientCompletionStageIdeal K I

include hφ in
/-- **The quotient stage of `Spf ((A/K)^∧)` over a quotient stage of `Spf A`.** The square
```
Spec (A/(K + I)) ⟶ Spec (A/I)
      ↓                ↓
  Spf ((A/K)^∧)  ⟶   Spf A
```
is cartesian: the stage of `Spf ((A/K)^∧)` cut out by `ker (C → A/(I + K))` is the fibre
product `Spf ((A/K)^∧) ×_{Spf A} Spec (A/I)`. This is the base change of Stacks 0AN5 for the
canonical map `A → (A/K)^∧`, whose stage ideals are the closures of the extended ideals. -/
theorem isPullback_formalSpectrumMap_quotientCompletion_stage
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    IsPullback
      (formalSpectrumInclusion E (OrderDual.toDual (quotientCompletionStageIdeal K I)))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map
          (φ.stageMap I (quotientCompletionStageIdeal K I)
            (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I))))
      (formalSpectrumMap hA φ) (formalSpectrumInclusion D (OrderDual.toDual I)) := by
  refine isPullback_formalSpectrumMap_stage B S hS hA
    (TopologicalRing.completionOver_isWeaklyAdmissible
      (Ideal.Quotient.mk K) hA) D E φ I (quotientCompletionStageIdeal K I) ?_ _
  rw [hφ]
  exact quotientCompletionStageIdeal_eq_closure K I

include hφ in
/-- **Stacks 0ANR, the base-change identification.** Let `T` be an fppf sheaf over `S` and let
`t : T ⟶ Spec (A/I)` be a morphism to a quotient stage of `Spf A`. Then the fibre product of
`Spf ((A/K)^∧) ⟶ Spf A` with the induced morphism `T ⟶ Spf A` is
`T ×_{Spec (A/I)} Spec (A/(K + I))`:
```
T ×_{Spec (A/I)} Spec (A/(K + I)) ⟶ Spf ((A/K)^∧)
               ↓                           ↓
               T                   ⟶     Spf A
```
is cartesian. A morphism to `Spf A` out of a quasi-compact scheme admits such a factorisation
by Stacks 0AIA, which is the shape in which the source states this. -/
@[stacks 0ANR "base change"]
theorem isPullback_baseChange_quotientCompletion
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) (T : FppfSheaf B S hS)
    (t : T ⟶ (formalSpectrumDiagram D).obj (OrderDual.toDual I)) :
    IsPullback
      (pullback.fst
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (φ.stageMap I (quotientCompletionStageIdeal K I)
              (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I)))) t ≫
        formalSpectrumInclusion E (OrderDual.toDual (quotientCompletionStageIdeal K I)))
      (pullback.snd
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (φ.stageMap I (quotientCompletionStageIdeal K I)
              (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I)))) t)
      (formalSpectrumMap hA φ)
      (t ≫ formalSpectrumInclusion D (OrderDual.toDual I)) :=
  (IsPullback.of_hasPullback _ t).paste_horiz
    (isPullback_formalSpectrumMap_quotientCompletion_stage B S hS hA D E φ hφ I)

include hφ in
/-- The ring map `A/I ⟶ C ⧸ ker (C → A/(I + K))` presenting a stage of `Spf ((A/K)^∧)` over
the corresponding stage of `Spf A` is surjective: through
`AlgebraicGeometry.FormalSpace.quotientCompletionStageEquiv` it is the projection
`A/I ⟶ A/(K + I)`. -/
theorem surjective_quotientMap_quotientCompletionStageIdeal
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    Function.Surjective
      (Ideal.quotientMap (quotientCompletionStageIdeal K I).1 φ.toRingHom
        (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I)) := by
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
    (TopologicalRing.CompletionOver.projection (Ideal.Quotient.mk K) I c)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨Ideal.Quotient.mk I.1 a, ?_⟩
  rw [Ideal.quotientMap_mk, hφ]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  change TopologicalRing.CompletionOver.projection (Ideal.Quotient.mk K) I
    (TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K) a - c) = 0
  rw [map_sub, TopologicalRing.CompletionOver.projection_canonicalMap, hz, sub_self]

include hφ in
/-- **The stage morphism of `Spf ((A/K)^∧)` over a stage of `Spf A` is a closed immersion of
schemes.** It is `Spec` of the surjection `A/I ⟶ A/(K + I)`. Together with
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_quotientCompletion_stage`, which
exhibits it as the base change of `Spf ((A/K)^∧) ⟶ Spf A` along the stage inclusion
`Spec (A/I) ⟶ Spf A`, this is the step from which the source reads off that
`Spf ((A/K)^∧) ⟶ Spf A` is a closed immersion. -/
theorem isClosedImmersion_quotientCompletion_stageMap
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map
        (φ.stageMap I (quotientCompletionStageIdeal K I)
          (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I))) := by
  change _root_.AlgebraicGeometry.IsClosedImmersion
    (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (quotientCompletionStageIdeal K I).1 φ.toRingHom
        (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I))))
  exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (surjective_quotientMap_quotientCompletionStageIdeal B S hS D E φ hφ I)

/-- The big fppf topology over `S` is subcanonical, as a local instance for the proofs below. -/
private instance : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS

include hφ in
/-- The stage morphism `Spec (A/(K + I)) ⟶ Spec (A/I)` of `Spf ((A/K)^∧)` over `Spf A` stays a
closed immersion of schemes after every represented base change, being one already and closed
immersions of schemes being stable under base change. -/
private theorem relative_isClosedImmersion_quotientCompletion_stageMap
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map
          (φ.stageMap I (quotientCompletionStageIdeal K I)
            (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ I)))) := by
  have _ := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  exact MorphismProperty.relative_map
    (isClosedImmersion_quotientCompletion_stageMap B S hS D E φ hφ I)

include hφ in
/-- **The fibre product over a point factoring through a stage is an object of the site.** If a
point `a : U ⟶ Spf A` of an object of the site factors through the stage `Spec (A/I)`, then
`U ×_{Spf A} Spf ((A/K)^∧)` is represented by an object `W` of the site, and `W ⟶ U` is a closed
immersion of schemes, being a base change of `Spec (A/(K + I)) ⟶ Spec (A/I)`. -/
private theorem exists_isPullback_quotientCompletion_of_factorsThroughStage
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A) (U : BigFppfOver B S hS)
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D)
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
      formalSpectrumInclusion D (OrderDual.toDual I) = a) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ formalSpectrum E),
      IsPullback q ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA φ) a ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  subst ha
  obtain ⟨hrep, hprop⟩ := relative_isClosedImmersion_quotientCompletion_stageMap B S hS D E φ hφ I
  obtain ⟨W, p, q, hpb⟩ := hrep ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g)
  exact ⟨W, p,
    q ≫ formalSpectrumInclusion E (OrderDual.toDual (quotientCompletionStageIdeal K I)),
    hpb.paste_horiz
      (isPullback_formalSpectrumMap_quotientCompletion_stage B S hS hA D E φ hφ I),
    hprop _ q p hpb⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Stacks 0AIA for the formal spectrum.** A point of `Spf A` out of an affine object of the
site factors through one of the quotient stages `Spec (A/I)`: the stages present `Spf A` as a
directed colimit along thickenings, and an affine scheme is quasi-compact. -/
private theorem exists_factor_through_stage_of_affine
    (hA : TopologicalRing.IsWeaklyPreAdmissible A) (X : BigAffineFppf B S hS)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj X) ⟶ formalSpectrum D) :
    ∃ (I : TopologicalRing.WeakIdealOfDefinitionIndex A) (g : X ⟶ D.stage I),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        formalSpectrumInclusion D (OrderDual.toDual I) = a := by
  have _ : Nonempty (WeakIdeals A) :=
    ⟨OrderDual.toDual ⟨Classical.choose hA, Classical.choose_spec hA⟩⟩
  have _ : IsDirected (WeakIdeals A) (· ≤ ·) :=
    ⟨fun I₁ I₂ => ⟨OrderDual.toDual ⟨I₁.1 ⊓ I₂.1,
      ⟨I₁.2.1.inter I₂.2.1, fun x hx => I₁.2.2 x hx.1⟩⟩,
      show I₁.1 ⊓ I₂.1 ≤ I₁.1 from inf_le_left,
      show I₁.1 ⊓ I₂.1 ≤ I₂.1 from inf_le_right⟩⟩
  have hD : ∀ ⦃i j : WeakIdeals A⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map ((QuotientSystem.diagram D).map f)) :=
    fun i j f => quotientPresentation_transition_isThickening B S hS A (formalSpectrum D)
      D.weakIdealColimitPresentation i j f
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS (formalSpectrum D)
    (WeakIdeals A) (QuotientSystem.diagram D) hD (Iso.refl _) X a
  refine ⟨OrderDual.ofDual j, g, ?_⟩
  rw [← Category.comp_id
    (formalSpectrumInclusion D (OrderDual.toDual (OrderDual.ofDual j)))]
  exact hg

include hA hφ in
/-- **The fibre product over an affine point is an object of the site.** Combining Stacks 0AIA
with the cartesian stage square: a point of `Spf A` out of an affine object `X` of the site
factors through some `Spec (A/I)`, and then `X ×_{Spf A} Spf ((A/K)^∧)` is the object
`X ×_{Spec (A/I)} Spec (A/(K + I))` of the site, closed in `X`. -/
private theorem exists_isPullback_quotientCompletion_of_affine (X : BigAffineFppf B S hS)
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
        ((BigAffineFppf.inclusion B S hS).obj X) ⟶ formalSpectrum D) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ (BigAffineFppf.inclusion B S hS).obj X)
      (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ formalSpectrum E),
      IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p)
        (formalSpectrumMap hA φ) ξ ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  let ε := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨I, g, hg⟩ := exists_factor_through_stage_of_affine B S hS D hA.1 X
    (ε.inv.app ((BigAffineFppf.inclusion B S hS).obj X) ≫ ξ)
  obtain ⟨W, p, c, hpb, hci⟩ :=
    exists_isPullback_quotientCompletion_of_factorsThroughStage B S hS hA D E φ hφ I
      ((BigAffineFppf.inclusion B S hS).obj X) ((BigAffineFppf.inclusion B S hS).map g) _ hg
  refine ⟨W, p, ε.hom.app W ≫ c, hpb.of_iso' (ε.app W) (Iso.refl _)
    (ε.app ((BigAffineFppf.inclusion B S hS).obj X)) (Iso.refl _) (by simp)
    (ε.hom.naturality p).symm (by simp) ?_, hci⟩
  rw [← Iso.app_inv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

include hA hφ in
/-- **`Spf ((A/K)^∧) ⟶ Spf A` is representable by algebraic spaces over `S`.** This is what the
source's reference to Example 0AN6 contributes to Stacks 0ANR.

Representability is checked after a surjective étale covering of each scheme-valued point of
`Spf A` by one object of the site, namely the coproduct of the affine opens of that point. Over
each affine open the point factors through a quotient stage by Stacks 0AIA and the fibre product
is an object of the site; coproducts of fppf sheaves are universal, so the fibre product over
the covering object is the coproduct of those, which lies in the site because the members are
closed subschemes of affine opens of a single object. -/
theorem isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_quotientCompletion :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA φ).hom := by
  refine isRepresentable_of_forall_surjective_etale_cover B S hS (formalSpectrumMap hA φ) ?_
  intro T ξ
  obtain ⟨ι, X, V, j, q, hXaff, hιsize, hXsize, hqsurj, hqetale, -, ⟨hsheaf⟩⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma B S hS T
  refine ⟨V, q, hqsurj, hqetale, ?_⟩
  let ξV : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ formalSpectrum D :=
    ⟨uliftYoneda.{u + 1}.map q ≫ ξ⟩
  have hex : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ X i)
      (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ formalSpectrum E),
      IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p)
        (formalSpectrumMap hA φ)
        ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i) ≫ ξV) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) :=
    fun i => exists_isPullback_quotientCompletion_of_affine B S hS hA D E φ hφ
      ⟨X i, hXaff i⟩ _
  choose W p c hpb hci using hex
  have hWsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj T).size := by
    intro i
    have _ := hci i
    exact le_trans
      (Scheme.size_le_of_mono_quasiCompact ((BigFppfOver.toScheme B S hS).map (p i)))
      (hXsize i)
  obtain ⟨Wt, jw, -, -, -, -, ⟨hWsheaf⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS W T.left.property hιsize hWsize
  have hP := IsPullback.of_hasPullback ξV (formalSpectrumMap hA φ)
  have hleft := fun i => IsPullback.of_right' (hpb i) hP.flip
  obtain ⟨hPcol⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback
    (BigFppfOver.topology B S hS)
    (fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i)) hsheaf
    (pullback.fst ξV (formalSpectrumMap hA φ)) _
    (fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (p i)) hleft
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (pullback ξV (formalSpectrumMap hA φ))) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
        (IsColimit.coconePointUniqueUpToIso hWsheaf hPcol))
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Wt)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    (hP.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).isoPullback hPalg

include hA hφ in
/-- **Stacks 0ANR.** The morphism `Spf ((A/K)^∧) ⟶ Spf A` induced by the canonical map
`A → (A/K)^∧` is a closed immersion of formal algebraic spaces over `S`, in the sense of
Stacks 0ANP.

The stage inclusions `Spec (A/I) ⟶ Spf A` are jointly surjective with each base change of it
along them the closed immersion `Spec (A/(K + I)) ⟶ Spec (A/I)`; the descent step of
Stacks 0GHY concludes, representability by algebraic spaces being part of what that step
returns rather than a hypothesis of it. -/
@[stacks 0ANR "closed immersion"]
theorem isClosedImmersion_formalSpectrumMap_quotientCompletion :
    AlgebraicGeometry.FormalSpace.IsClosedImmersion B S hS (formalSpectrumMap hA φ) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  set Idx := ULift.{u + 1, u} (TopologicalRing.WeakIdealOfDefinitionIndex A)
  set Yi : Idx → FppfSheaf B S hS :=
    fun i => (formalSpectrumDiagram D).obj (OrderDual.toDual i.down)
  set cc : ∀ i, Yi i ⟶ formalSpectrum D :=
    fun i => formalSpectrumInclusion D (OrderDual.toDual i.down)
  have hls : Sheaf.IsLocallySurjective (Limits.Sigma.desc cc) := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨fun {Q} f₁ f₂ h => Limits.colimit.hom_ext fun Kk => ?_⟩
    have hK : cc (ULift.up (OrderDual.ofDual Kk)) ≫ f₁ =
        cc (ULift.up (OrderDual.ofDual Kk)) ≫ f₂ := by
      rw [← Limits.Sigma.ι_comp_desc cc (ULift.up (OrderDual.ofDual Kk)),
        Category.assoc, Category.assoc, h]
    exact hK
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS Idx Yi cc hls fun i => ?_
  have hsq := isPullback_formalSpectrumMap_quotientCompletion_stage B S hS hA D E φ hφ i.down
  have hm := isClosedImmersion_of_isClosedImmersionInto B S hS _
    (relative_isClosedImmersion_quotientCompletion_stageMap B S hS D E φ hφ i.down)
  have hpb2 := IsPullback.of_hasPullback (formalSpectrumMap hA φ) (cc i)
  have hw : (hsq.isoIsPullback _ _ hpb2).inv ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map
          (φ.stageMap i.down (quotientCompletionStageIdeal K i.down)
            (continuousHom_le_comap_quotientCompletionStageIdeal B S hS D E φ hφ i.down))) =
      pullback.snd (formalSpectrumMap hA φ) (cc i) ≫ 𝟙 (Yi i) := by
    rw [Category.comp_id]
    exact hsq.isoIsPullback_inv_snd _ _ hpb2
  exact isClosedImmersion_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := (hsq.isoIsPullback _ _ hpb2).inv) (g := 𝟙 (Yi i))
      (CommSq.mk hw)) hm

end Geometry

end AlgebraicGeometry.FormalSpace

end
