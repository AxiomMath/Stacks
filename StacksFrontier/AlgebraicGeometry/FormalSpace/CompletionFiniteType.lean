module

public import Mathlib.Algebra.FreeAlgebra.Cardinality
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Completion along a finite type ring map (Stacks 0ANM)

Let `S` be a scheme in a big fppf site, let `B` be a weakly admissible topological ring over
`S` and let `f : B →+* A` be a finite type ring map. **Stacks 0ANM** studies the relative
completion `A^ = lim_J A / JA`, the limit over the weak ideals of definition `J ⊆ B`.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_quotientCompletionEquiv`: the quotient of `A^`
  by the kernel of its projection to `A / JA` is canonically `A / JA`.
* `AlgebraicGeometry.FormalSpace.completionOverQuotientSystem` and
  `AlgebraicGeometry.FormalSpace.completionOverContinuousHomWithCanonicalMap`: that quotient
  system named, and the canonical map `B → A^` as a continuous homomorphism over `S` into it,
  carried together with the identification of its underlying ring map.
* `AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem`: `A^` is a topological
  ring over `S`, by a quotient system receiving a continuous map from `B` whose underlying
  ring map is the canonical one, hence a morphism `Spf A^ ⟶ Spf B` of formal spectra.
* `AlgebraicGeometry.FormalSpace.hasLargeSite_completionOver_of_finiteType`: a site large
  enough for the stage spectra of `B` is large enough for those of `A^`.
* `AlgebraicGeometry.FormalSpace.ker_projection_eq_sup`: the kernel of `A^ → A / JA` is the sum
  of `J·A^` and any open ideal of `A^` contained in it.
* `AlgebraicGeometry.FormalSpace.isPullback_specMap_kerProjection`: the affine base change of
  the relative completion along a quotient stage, `Spec (A / JA) = Spec (B / J)
  ×_{Spec (B / M)} Spec (A^ / L)`.
* `AlgebraicGeometry.FormalSpace.kerProjectionIdeal`: the kernel of `A^ → A / JA` as a weak
  ideal of definition of `A^`.
* `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_kerProjection`: the base change
  of the relative completion along a quotient stage, as fppf sheaves over `S`:
  `Spec (A / JA) = Spec (B / J) ×_{Spf B} Spf A^`.

## Implementation notes

The quotient system of `A^` sends a weak ideal of definition `K` of `A^` to the spectrum of
`A^ / K`, over `S` through the stage of a weak ideal of definition `J` of `B` with
`ker (A^ → A / JA) ⊆ K`; such a `J` exists because the canonical map `B → A^` is taut. The
large-site statement is a cardinality estimate: `A^` is a subring of the product of the
`A / JA` over the weak ideals of definition `J` of `B`, and both the index and each factor
are bounded by the size of the coproduct of the stage spectra of `B`.

The affine base-change square is deduced from a pushout square of rings: the quotient map
`B / M → B / J` is surjective, so the pushout of `B / J` and `A^ / L` over `B / M` is
`A^ / (L + J·A^)`, and that ideal is `ker (A^ → A / JA)` because the kernel is the closure of
`J·A^` while `L` is an open subgroup.

The sheaf-level base-change square is the affine one made global by the universality of the
colimit presenting `Spf A^`. The canonical map from `Spec (A / JA)` to the fibre product is a
monomorphism because a quotient stage includes into a formal spectrum by a monomorphism, and
it is an epimorphism because the base changes of the fibre product along the stages of
`Spf A^` cover it and each of them factors through `Spec (A / JA)`: for a weak ideal of
definition `L` of `A^` the affine square applies to `L ⊓ ker (A^ → A / JA)` together with
`J ⊓ (A^ → A / JA)⁻¹ L`. The sheaves of sets over `S` form a balanced category, so a
monomorphic epimorphism is an isomorphism.

## References

* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₁ v₂ w₁ w₂ u

namespace AlgebraicGeometry.FormalSpace

/-- The quotient of the relative completion `A^` by the kernel of its projection to `A / JA`
is canonically `A / JA`, by the unique isomorphism compatible with that projection. -/
@[stacks 0ANM "the quotient of the relative completion at a weak ideal of definition"]
theorem existsUnique_quotientCompletionEquiv
    {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    ∃! e : (TopologicalRing.CompletionOver f ⧸
        RingHom.ker (TopologicalRing.CompletionOver.projection f J)) ≃+*
          (A ⧸ TopologicalRing.extendedIdeal f J),
      ∀ x : TopologicalRing.CompletionOver f,
        e (Ideal.Quotient.mk _ x) = TopologicalRing.CompletionOver.projection f J x := by
  refine ⟨RingHom.quotientKerEquivOfSurjective
    (TopologicalRing.CompletionOver.projection_surjective f J), fun _ ↦ rfl, ?_⟩
  intro e he
  refine RingEquiv.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (he y).trans rfl

section QuotientSystem

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A]

/-- The intersection of two weak ideals of definition is a weak ideal of definition. -/
private def weakInf (J K : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    TopologicalRing.WeakIdealOfDefinitionIndex B :=
  ⟨J.1 ⊓ K.1, ⟨J.2.1.inter K.2.1, fun x hx ↦ J.2.2 x hx.1⟩⟩

/-- An ideal of the relative completion containing the kernel of the projection at `J`
pulls back along `ofTarget` to an ideal containing `JA`. -/
private theorem extendedIdeal_le_comap_ofTarget (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (K : Ideal (TopologicalRing.CompletionOver f))
    (hK : RingHom.ker (TopologicalRing.CompletionOver.projection f J) ≤ K) :
    TopologicalRing.extendedIdeal f J ≤
      Ideal.comap (TopologicalRing.CompletionOver.ofTarget f) K := by
  rw [TopologicalRing.extendedIdeal, Ideal.map_le_iff_le_comap]
  intro b hb
  refine hK ?_
  change TopologicalRing.CompletionOver.projection f J
    (TopologicalRing.CompletionOver.ofTarget f (f b)) = 0
  rw [TopologicalRing.CompletionOver.projection_ofTarget]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hb)

/-- The surjection from `A / JA` onto a quotient of the relative completion by an ideal
containing the kernel of the projection at `J`. -/
private noncomputable def quotientStageMap (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (K : Ideal (TopologicalRing.CompletionOver f))
    (hK : RingHom.ker (TopologicalRing.CompletionOver.projection f J) ≤ K) :
    A ⧸ TopologicalRing.extendedIdeal f J →+* TopologicalRing.CompletionOver f ⧸ K :=
  Ideal.quotientMap K (TopologicalRing.CompletionOver.ofTarget f)
    (extendedIdeal_le_comap_ofTarget f J K hK)

private theorem quotientStageMap_surjective (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (K : Ideal (TopologicalRing.CompletionOver f))
    (hK : RingHom.ker (TopologicalRing.CompletionOver.projection f J) ≤ K) :
    Function.Surjective (quotientStageMap f J K hK) := by
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (TopologicalRing.CompletionOver.projection f J c)
  have hdiff : c - TopologicalRing.CompletionOver.ofTarget f a ∈
      RingHom.ker (TopologicalRing.CompletionOver.projection f J) := by
    change TopologicalRing.CompletionOver.projection f J
      (c - TopologicalRing.CompletionOver.ofTarget f a) = 0
    rw [map_sub, TopologicalRing.CompletionOver.projection_ofTarget, ← ha, sub_self]
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  change Ideal.Quotient.mk K (TopologicalRing.CompletionOver.ofTarget f a) =
    Ideal.Quotient.mk K c
  refine Ideal.Quotient.eq.mpr ?_
  simpa [sub_eq_add_neg] using K.neg_mem (hK hdiff)

/-- Every open ideal of the relative completion contains the kernel of one of the
projections: tautness of the canonical map. -/
private theorem exists_ker_projection_le [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (L : Ideal (TopologicalRing.CompletionOver f))
    (hL : IsOpen (L : Set (TopologicalRing.CompletionOver f))) :
    ∃ J : TopologicalRing.WeakIdealOfDefinitionIndex B,
      RingHom.ker (TopologicalRing.CompletionOver.projection f J) ≤ L := by
  obtain ⟨I, hIopen, hIL⟩ := (TopologicalRing.isTaut_canonicalMap f hB.1).2.mem_iff.mp
    (hL.mem_nhds (Ideal.zero_mem L))
  obtain ⟨I₀, hI₀⟩ := hB.1
  refine ⟨⟨I₀ ⊓ I, ⟨hI₀.1.inter hIopen, fun x hx ↦ hI₀.2 x hx.1⟩⟩, ?_⟩
  rw [TopologicalRing.CompletionOver.ker_projection_eq_closure]
  have hmono : (Ideal.closure ((I₀ ⊓ I).map
        (TopologicalRing.CompletionOver.canonicalMap f)) :
        Set (TopologicalRing.CompletionOver f)) ⊆
      (Ideal.closure (I.map (TopologicalRing.CompletionOver.canonicalMap f)) :
        Set (TopologicalRing.CompletionOver f)) := by
    simpa only [Ideal.coe_closure] using
      closure_mono (Ideal.map_mono (inf_le_right : I₀ ⊓ I ≤ I))
  exact fun x hx ↦ hIL (hmono hx)

/-- A weak ideal of definition of the base whose projection kernel lies in a given weak
ideal of definition of the relative completion. -/
private noncomputable def sourceWeakIdeal [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (K : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f)) :
    TopologicalRing.WeakIdealOfDefinitionIndex B :=
  (exists_ker_projection_le f hB K.1 K.2.1).choose

private theorem ker_projection_sourceWeakIdeal_le
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (K : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f)) :
    RingHom.ker (TopologicalRing.CompletionOver.projection f
      (sourceWeakIdeal f hB K)) ≤ K.1 :=
  (exists_ker_projection_le f hB K.1 K.2.1).choose_spec

/-- The map `B / J → A / JA` induced by `f`. -/
private noncomputable def baseStageMap (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    B ⧸ J.1 →+* A ⧸ TopologicalRing.extendedIdeal f J :=
  Ideal.quotientMap (TopologicalRing.extendedIdeal f J) f Ideal.le_comap_map

private theorem baseStageMap_comp (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (baseStageMap f J).comp (Ideal.Quotient.mk J.1) =
      (Ideal.Quotient.mk (TopologicalRing.extendedIdeal f J)).comp f :=
  RingHom.ext fun _ ↦ rfl

private theorem baseStageMap_finiteType (f : B →+* A)
    (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (baseStageMap f J).FiniteType := by
  let : Algebra B A := f.toAlgebra
  have hfRing : f.FiniteType := RingHom.finiteType_algebraMap.mpr hf
  have hq : ((Ideal.Quotient.mk (TopologicalRing.extendedIdeal f J)).comp f).FiniteType :=
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hfRing
  refine RingHom.FiniteType.of_comp_finiteType
    (f := Ideal.Quotient.mk J.1) (g := baseStageMap f J) ?_
  rw [baseStageMap_comp]
  exact hq

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

/-- The spectra of the quotients `A / JA` lie in the site as soon as the stage spectra of
the base do and `f` is of finite type. -/
private theorem baseStage_site (f : B →+* A)
    (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    {D : QuotientSystem 𝔅 S hS B} (hD : D.HasLargeSite)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    𝔅.Contains (Spec (.of (A ⧸ TopologicalRing.extendedIdeal f J))) := by
  have hBJ : 𝔅.Contains (Spec (.of (B ⧸ J.1))) := by
    refine Scheme.size_lt_of_isOpenImmersion
      (Sigma.ι (fun I : TopologicalRing.WeakIdealOfDefinitionIndex B ↦
        Spec (.of (B ⧸ I.1))) J) ?_
    exact hD
  let : Algebra (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
    (baseStageMap f J).toAlgebra
  let : Algebra.FiniteType (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
    RingHom.finiteType_algebraMap.mp (baseStageMap_finiteType f hf J)
  exact Scheme.size_Spec_lt_of_finiteType 𝔅.aleph0_lt_cutoff 𝔅.cutoff_isStrongPrelimit
    (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) hBJ

/-- The quotient system of the relative completion: its stage at a weak ideal of definition
`K` is `Spec` of the quotient, mapping to the base through the stage of a weak ideal of
definition `J` of `B` with `ker (A^ → A/JA) ⊆ K`.

This is *the* quotient system of `A^` over `S` attached to `D`, not merely one: a quotient
system on `A^` receiving a continuous homomorphism from `D` whose underlying ring map is the
canonical map `B → A^` has its structure morphisms determined by that data, so any two such
agree (`AlgebraicGeometry.FormalSpace.QuotientSystem.eq_of_continuousHom`), and that is how it
is used: its body is `@[no_expose]`, being built from the private stage maps of this file. -/
@[no_expose]
noncomputable def completionOverQuotientSystem'
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (D : QuotientSystem 𝔅 S hS B) (hD : D.HasLargeSite) :
    QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f) where
  inSite K := by
    let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (quotientStageMap f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K)))) :=
      IsClosedImmersion.spec_of_surjective _
        (quotientStageMap_surjective f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K))
    exact Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (quotientStageMap f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K))))
      (baseStage_site 𝔅 S hS f hf hD (sourceWeakIdeal f hB K))
  overS K :=
    Spec.map (CommRingCat.ofHom
      ((quotientStageMap f (sourceWeakIdeal f hB K) K.1
        (ker_projection_sourceWeakIdeal_le f hB K)).comp
          (baseStageMap f (sourceWeakIdeal f hB K)))) ≫
      D.overS (sourceWeakIdeal f hB K)
  compatible := by
    intro K L hKL
    set I := sourceWeakIdeal f hB K with hI
    set I' := sourceWeakIdeal f hB L with hI'
    have hMI : (weakInf I I').1 ≤ I.1 := inf_le_left
    have hMI' : (weakInf I I').1 ≤ I'.1 := inf_le_right
    have hMK : RingHom.ker (TopologicalRing.CompletionOver.projection f (weakInf I I')) ≤
        K.1 := (TopologicalRing.ker_projection_mono f hMI).trans
          (ker_projection_sourceWeakIdeal_le f hB K)
    have hML : RingHom.ker (TopologicalRing.CompletionOver.projection f (weakInf I I')) ≤
        L.1 := (TopologicalRing.ker_projection_mono f hMI').trans
          (ker_projection_sourceWeakIdeal_le f hB L)
    set qIK := (quotientStageMap f I K.1
      (ker_projection_sourceWeakIdeal_le f hB K)).comp (baseStageMap f I) with hqIK
    set qI'L := (quotientStageMap f I' L.1
      (ker_projection_sourceWeakIdeal_le f hB L)).comp (baseStageMap f I') with hqI'L
    set qML := (quotientStageMap f (weakInf I I') L.1 hML).comp
      (baseStageMap f (weakInf I I')) with hqML
    have hcompK : (Ideal.Quotient.factor hKL).comp
        (qIK.comp (Ideal.Quotient.factor hMI)) = qML := by ext b; rfl
    have hcompL : qI'L.comp (Ideal.Quotient.factor hMI') = qML := by ext b; rfl
    have hcompKScheme :
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKL)) ≫
            Spec.map (CommRingCat.ofHom qIK) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMI)) ≫
              D.overS (weakInf I I') =
          Spec.map (CommRingCat.ofHom qML) ≫ D.overS (weakInf I I') := by
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
        congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q) ≫ D.overS (weakInf I I')) hcompK
    have hcompLScheme :
        Spec.map (CommRingCat.ofHom qI'L) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMI')) ≫
              D.overS (weakInf I I') =
          Spec.map (CommRingCat.ofHom qML) ≫ D.overS (weakInf I I') := by
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
        congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q) ≫ D.overS (weakInf I I')) hcompL
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKL)) ≫
        Spec.map (CommRingCat.ofHom qIK) ≫ D.overS I =
      Spec.map (CommRingCat.ofHom qI'L) ≫ D.overS I'
    rw [← D.compatible (weakInf I I') I hMI, ← D.compatible (weakInf I I') I' hMI']
    exact hcompKScheme.trans hcompLScheme.symm

/-- The canonical map `B → A^` to the relative completion, as a continuous homomorphism of
topological rings over `S` into the quotient system
`AlgebraicGeometry.FormalSpace.completionOverQuotientSystem`, **together with** the
identification of its underlying ring map with
`TopologicalRing.CompletionOver.canonicalMap f`.

The identification is carried as the second component of a subtype rather than as a separate
equation because the quotient system is `@[no_expose]`: a theorem stating the equation would
have to unfold that definition, and the definition is built from the private stage maps of
this file. -/
@[no_expose]
noncomputable def completionOverContinuousHomWithCanonicalMap
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (D : QuotientSystem 𝔅 S hS B) (hD : D.HasLargeSite) :
    { g : ContinuousHom D (completionOverQuotientSystem' 𝔅 S hS f hf hB D hD) //
        g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f } :=
  ⟨{ toRingHom := TopologicalRing.CompletionOver.canonicalMap f
     continuous := TopologicalRing.continuous_canonicalMap f
     overS := by
       intro J K hJK
       set I := sourceWeakIdeal f hB K with hI
       have hMJ : (weakInf J I).1 ≤ J.1 := inf_le_left
       have hMI : (weakInf J I).1 ≤ I.1 := inf_le_right
       have hMK : RingHom.ker (TopologicalRing.CompletionOver.projection f (weakInf J I)) ≤ K.1 :=
         (TopologicalRing.ker_projection_mono f hMI).trans
           (ker_projection_sourceWeakIdeal_le f hB K)
       set qJK := Ideal.quotientMap K.1 (TopologicalRing.CompletionOver.canonicalMap f) hJK
         with hqJK
       set qIK := (quotientStageMap f I K.1
         (ker_projection_sourceWeakIdeal_le f hB K)).comp (baseStageMap f I) with hqIK
       set qMK := (quotientStageMap f (weakInf J I) K.1 hMK).comp
         (baseStageMap f (weakInf J I)) with hqMK
       have hcompJ : qJK.comp (Ideal.Quotient.factor hMJ) = qMK := by ext b; rfl
       have hcompI : qIK.comp (Ideal.Quotient.factor hMI) = qMK := by ext b; rfl
       have hcompJScheme :
           Spec.map (CommRingCat.ofHom qJK) ≫
               Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMJ)) ≫
                 D.overS (weakInf J I) =
             Spec.map (CommRingCat.ofHom qMK) ≫ D.overS (weakInf J I) := by
         simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
           congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q) ≫ D.overS (weakInf J I)) hcompJ
       have hcompIScheme :
           Spec.map (CommRingCat.ofHom qIK) ≫
               Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMI)) ≫
                 D.overS (weakInf J I) =
             Spec.map (CommRingCat.ofHom qMK) ≫ D.overS (weakInf J I) := by
         simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
           congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q) ≫ D.overS (weakInf J I)) hcompI
       change Spec.map (CommRingCat.ofHom qJK) ≫ D.overS J =
         Spec.map (CommRingCat.ofHom qIK) ≫ D.overS I
       rw [← D.compatible (weakInf J I) J hMJ, ← D.compatible (weakInf J I) I hMI]
       exact hcompJScheme.trans hcompIScheme.symm }, rfl⟩

/-- **Stacks 0ANM.** A finite type ring map out of a weakly admissible topological ring
over `S` gives the relative completion a quotient system over `S` and a continuous map from
the base whose underlying ring map is the canonical one. -/
@[stacks 0ANM "the induced quotient system and continuous map of the relative completion"]
theorem exists_completionOver_quotientSystem
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (D : QuotientSystem 𝔅 S hS B) (hD : D.HasLargeSite) :
    ∃ (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
      (g : ContinuousHom D E),
      g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f :=
  ⟨completionOverQuotientSystem' 𝔅 S hS f hf hB D hD,
    (completionOverContinuousHomWithCanonicalMap 𝔅 S hS f hf hB D hD).1,
    (completionOverContinuousHomWithCanonicalMap 𝔅 S hS f hf hB D hD).2⟩

end QuotientSystem

section LargeSite

/-- A strong prelimit cardinal above `ℵ₀` is closed under exponentiation. -/
private theorem power_lt_of_isStrongPrelimit {κ a b : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    (ha : a < κ) (hb : b < κ) : a ^ b < κ :=
  calc
    a ^ b ≤ (2 ^ a) ^ b := Cardinal.power_le_power_right (Cardinal.cantor a).le
    _ = 2 ^ (a * b) := Cardinal.power_mul.symm
    _ < κ := hsl (Cardinal.mul_lt_of_lt hκ.le ha hb)

/-- A finite type algebra has at most `max #B ℵ₀` elements. -/
private theorem finiteType_cardinal_le_max {B A : Type u} [CommRing B] [CommRing A]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A) :
    Cardinal.mk A ≤ max (Cardinal.mk B) Cardinal.aleph0 := by
  let : Algebra B A := f.toAlgebra
  obtain ⟨s, g, hg⟩ := (Algebra.FiniteType.iff_quotient_freeAlgebra).mp hf
  have hs : Cardinal.mk (↥s) ≤ Cardinal.aleph0 :=
    ((Cardinal.mk_lt_aleph0_iff).mpr (Finite.of_fintype (α := {x // x ∈ s}))).le
  calc
    Cardinal.mk A ≤ Cardinal.mk (FreeAlgebra B s) := Cardinal.mk_le_of_surjective hg
    _ ≤ max (max (Cardinal.mk B) (Cardinal.mk s)) Cardinal.aleph0 :=
      FreeAlgebra.cardinalMk_le_max B s
    _ ≤ max (Cardinal.mk B) Cardinal.aleph0 := by
      refine (max_le_max (max_le_max le_rfl hs) (le_refl Cardinal.aleph0)).trans ?_
      simp

/-- A site containing the coproduct of the stage spectra has fewer weak ideals of
definition than its cutoff: distinct proper weak ideals give distinct affine opens of the
coproduct. -/
private theorem weakIdealIndex_lt_cutoff_of_largeSite (𝔅 : BigFppfSite.{u})
    {B : Type u} [CommRing B] [TopologicalSpace B]
    (hD : 𝔅.Contains (∐ fun J : TopologicalRing.WeakIdealOfDefinitionIndex B ↦
      Spec (.of (B ⧸ J.1)))) :
    Cardinal.mk (TopologicalRing.WeakIdealOfDefinitionIndex B) < 𝔅.cutoff := by
  classical
  let Y : TopologicalRing.WeakIdealOfDefinitionIndex B → Scheme.{u} :=
    fun J ↦ Spec (.of (B ⧸ J.1))
  let X := ∐ Y
  have hX : X.size < 𝔅.cutoff := hD
  let U (J : TopologicalRing.WeakIdealOfDefinitionIndex B) : X.affineOpens :=
    ⟨(Sigma.ι Y J).opensRange, isAffineOpen_opensRange (Sigma.ι Y J)⟩
  have hUinj {J K : TopologicalRing.WeakIdealOfDefinitionIndex B}
      (hJ : J.1 ≠ ⊤) (hK : K.1 ≠ ⊤) (hJK : U J = U K) : J = K := by
    by_contra hne
    have hbot : (U J).1 ⊓ (U K).1 = (⊥ : X.Opens) :=
      disjoint_iff.mp (disjoint_opensRange_sigmaι Y J K hne)
    let : Nontrivial (B ⧸ J.1) := Ideal.Quotient.nontrivial_iff.mpr hJ
    obtain ⟨x⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr
      (inferInstance : Nontrivial (B ⧸ J.1))
    have hx : (Sigma.ι Y J) x ∈ (U J).1 := (Scheme.Hom.mem_opensRange).2 ⟨x, rfl⟩
    have hboth : (Sigma.ι Y J) x ∈ (U J).1 ⊓ (U K).1 := ⟨hx, by rwa [← hJK]⟩
    rw [hbot] at hboth
    simp at hboth
  let code (J : TopologicalRing.WeakIdealOfDefinitionIndex B) : Option X.affineOpens :=
    if J.1 = ⊤ then none else some (U J)
  have hcode : Function.Injective code := by
    intro J K h
    by_cases hJ : J.1 = ⊤ <;> by_cases hK : K.1 = ⊤
    · exact Subtype.ext (hJ.trans hK.symm)
    · simp [code, hJ, hK] at h
    · simp [code, hJ, hK] at h
    · exact hUinj hJ hK (Option.some.inj (by simpa [code, hJ, hK] using h))
  have hidx : Cardinal.mk (TopologicalRing.WeakIdealOfDefinitionIndex B) ≤
      Cardinal.mk X.affineOpens + 1 :=
    (Cardinal.mk_le_of_injective hcode).trans Cardinal.mk_option.le
  refine hidx.trans_lt (lt_of_le_of_lt ?_ hX)
  calc
    Cardinal.mk X.affineOpens + 1 ≤
        max (max (Cardinal.mk X.affineOpens) 1) Cardinal.aleph0 := Cardinal.add_le_max _ _
    _ ≤ X.size := max_le (max_le X.mk_affineOpens_le_size
      (Cardinal.one_le_aleph0.trans X.aleph0_le_size)) X.aleph0_le_size

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)
  {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A]

/-- A site large enough for the stage spectra of `B` is large enough for those of the
relative completion of a finite type `B`-algebra: the completion is a subring of a product
of `#I` quotients of `A`, each bounded by the size of the coproduct of the stages of `B`. -/
private theorem hasLargeSite_completionOver (f : B →+* A)
    (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    {D : QuotientSystem 𝔅 S hS B} (hD : D.HasLargeSite) :
    𝔅.Contains (∐ fun K : TopologicalRing.WeakIdealOfDefinitionIndex
      (TopologicalRing.CompletionOver f) ↦
      Spec (.of (TopologicalRing.CompletionOver f ⧸ K.1))) := by
  classical
  let C := TopologicalRing.CompletionOver f
  let I := TopologicalRing.WeakIdealOfDefinitionIndex B
  let Y : I → Scheme.{u} := fun J ↦ Spec (.of (B ⧸ J.1))
  let X := ∐ Y
  have hX : X.size < 𝔅.cutoff := hD
  have hIcard : Cardinal.mk I < 𝔅.cutoff := weakIdealIndex_lt_cutoff_of_largeSite 𝔅 hD
  have hCstage (J : I) :
      Cardinal.mk (A ⧸ TopologicalRing.extendedIdeal f J) ≤ X.size := by
    have hbase : Cardinal.mk (B ⧸ J.1) ≤ X.size := by
      let V : X.affineOpens :=
        ⟨(Sigma.ι Y J).opensRange, isAffineOpen_opensRange (Sigma.ι Y J)⟩
      have hRange : Set.range (Sigma.ι Y J) = Set.range V.1.ι := by ext x; simp [V]
      have hYsize : (Y J).size ≤ X.size := by
        rw [Scheme.size_congr (IsOpenImmersion.isoOfRangeEq (Sigma.ι Y J) V.1.ι hRange)]
        exact Scheme.size_coe_opens_le X V.1
      refine le_trans ?_ hYsize
      rw [show (Y J) = Spec (.of (B ⧸ J.1)) from rfl, Scheme.size_Spec]
      exact le_max_right _ _
    let : Algebra (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
      (baseStageMap f J).toAlgebra
    let : Algebra.FiniteType (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
      RingHom.finiteType_algebraMap.mp (baseStageMap_finiteType f hf J)
    exact (finiteType_cardinal_le_max (baseStageMap f J) inferInstance).trans
      (max_le hbase X.aleph0_le_size)
  have hC : Cardinal.mk C < 𝔅.cutoff := by
    refine lt_of_le_of_lt ?_ (power_lt_of_isStrongPrelimit 𝔅.aleph0_lt_cutoff
      𝔅.cutoff_isStrongPrelimit hX hIcard)
    calc
      Cardinal.mk C ≤ Cardinal.mk (∀ J : I, A ⧸ TopologicalRing.extendedIdeal f J) :=
        Cardinal.mk_le_of_injective Subtype.val_injective
      _ = Cardinal.prod (fun J : I ↦
          Cardinal.mk (A ⧸ TopologicalRing.extendedIdeal f J)) := by rw [Cardinal.mk_pi]
      _ ≤ Cardinal.prod (fun _ : I ↦ X.size) := Cardinal.prod_le_prod _ _ hCstage
      _ = X.size ^ Cardinal.mk I := by rw [Cardinal.prod_const']
  have hν : max Cardinal.aleph0 (2 ^ Cardinal.mk C) < 𝔅.cutoff :=
    max_lt 𝔅.aleph0_lt_cutoff (𝔅.cutoff_isStrongPrelimit hC)
  have hCpow : Cardinal.mk C ≤ 2 ^ Cardinal.mk C := by
    calc
      Cardinal.mk C ≤ Cardinal.mk (Set C) := Cardinal.mk_le_of_injective
        (f := fun x : C ↦ ({x} : Set C)) (fun x y h ↦ by
          simpa using congrArg (fun V : Set C ↦ x ∈ V) h)
      _ = 2 ^ Cardinal.mk C := Cardinal.mk_set
  have hidx : Cardinal.mk (TopologicalRing.WeakIdealOfDefinitionIndex C) ≤
      2 ^ Cardinal.mk C := by
    calc
      _ ≤ Cardinal.mk (Ideal C) := Cardinal.mk_subtype_le _
      _ ≤ Cardinal.mk (Set C) := Cardinal.mk_le_of_injective
        (f := fun J : Ideal C ↦ (J : Set C)) (fun J K h ↦ Ideal.ext fun x ↦
          Iff.of_eq (congrArg (fun V : Set C ↦ x ∈ V) h))
      _ = 2 ^ Cardinal.mk C := Cardinal.mk_set
  refine lt_of_le_of_lt (AlgebraicGeometry.schemeSize_coproduct_le
    (fun K : TopologicalRing.WeakIdealOfDefinitionIndex C ↦ Spec (.of (C ⧸ K.1)))
    (max Cardinal.aleph0 (2 ^ Cardinal.mk C)) (le_max_left _ _)
    (hidx.trans (le_max_right _ _)) ?_) hν
  intro K
  rw [Scheme.size_Spec]
  refine max_le (le_max_left _ _) ?_
  exact ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hCpow).trans
    (le_max_right _ _)

/-- **Stacks 0ANM.** If the site is large enough to carry the formal spectrum of `B`, it is
large enough to carry the formal spectrum of the relative completion of a finite type
`B`-algebra. -/
theorem hasLargeSite_completionOver_of_finiteType (f : B →+* A)
    (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    {D : QuotientSystem 𝔅 S hS B} (hD : D.HasLargeSite)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) :
    E.HasLargeSite :=
  hasLargeSite_completionOver 𝔅 S hS f hf hD

end LargeSite

section BaseChange

/-- The closure of an ideal is contained in its sum with any open ideal: a point of the
closure differs from a point of the ideal by an element of the open ideal. -/
private theorem closure_le_sup_of_isOpen {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] (H L : Ideal C) (hL : IsOpen (L : Set C)) :
    Ideal.closure H ≤ H ⊔ L := by
  intro x hx
  have hxc : x ∈ closure (H : Set C) := by
    rw [← Ideal.coe_closure]
    exact hx
  have hopen : IsOpen {y : C | x - y ∈ L} :=
    hL.preimage (continuous_const.sub continuous_id)
  obtain ⟨y, hyO, hyH⟩ :=
    mem_closure_iff.mp hxc {y : C | x - y ∈ L} hopen (by simp)
  have hxy : x = y + (x - y) := by ring
  have h₁ : H ≤ H ⊔ L := le_sup_left
  have h₂ : L ≤ H ⊔ L := le_sup_right
  exact hxy ▸ add_mem (h₁ hyH) (h₂ hyO)

/-- For an open ideal `L` of the relative completion inside the kernel of the projection at
`J`, that kernel is the sum of `L` and the ideal generated by the image of `J`. This is the
identity `ker (A^ → A / JA) = J·A^ + L`, which holds because the kernel is the closure of
`J·A^` and `L` is open. -/
@[stacks 0ANM "the affine base change of the completion along a quotient stage"]
theorem ker_projection_eq_sup {B A : Type u} [CommRing B] [TopologicalSpace B]
    [CommRing A] (f : B →+* A) (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (L : Ideal (TopologicalRing.CompletionOver f))
    (hLopen : IsOpen (L : Set (TopologicalRing.CompletionOver f)))
    (hL : L ≤ RingHom.ker (TopologicalRing.CompletionOver.projection f J)) :
    RingHom.ker (TopologicalRing.CompletionOver.projection f J) =
      J.1.map (TopologicalRing.CompletionOver.canonicalMap f) ⊔ L := by
  refine le_antisymm ?_ (sup_le ?_ hL)
  · rw [TopologicalRing.CompletionOver.ker_projection_eq_closure]
    exact closure_le_sup_of_isOpen _ _ hLopen
  · rw [TopologicalRing.CompletionOver.ker_projection_eq_closure]
    intro x hx
    have : (J.1.map (TopologicalRing.CompletionOver.canonicalMap f) :
        Set (TopologicalRing.CompletionOver f)) ⊆
        (Ideal.closure (J.1.map (TopologicalRing.CompletionOver.canonicalMap f)) :
          Set (TopologicalRing.CompletionOver f)) := by
      simpa only [Ideal.coe_closure] using
        subset_closure (s := (J.1.map (TopologicalRing.CompletionOver.canonicalMap f) :
          Set (TopologicalRing.CompletionOver f)))
    exact this hx

/-- A square of quotient rings is a pushout: for `M ≤ J` in `S`, `L ≤ K` in `T` and a ring map
`φ : S →+* T` carrying `M` into `L` and `J` into `K`, with `K` contained in the sum of `L` and
the image of `J`, the ring `T ⧸ K` is the pushout of `S ⧸ J` and `T ⧸ L` over `S ⧸ M`. -/
private theorem isPushout_quotientMap {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)
    {M J : Ideal S} {L K : Ideal T} (hMJ : M ≤ J) (hLK : L ≤ K)
    (hML : M ≤ Ideal.comap φ L) (hJK : J ≤ Ideal.comap φ K)
    (hK : K ≤ J.map φ ⊔ L) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.factor hMJ))
      (CommRingCat.ofHom (Ideal.quotientMap L φ hML))
      (CommRingCat.ofHom (Ideal.quotientMap K φ hJK))
      (CommRingCat.ofHom (Ideal.Quotient.factor hLK)) := by
  have hcomm : CommRingCat.ofHom (Ideal.Quotient.factor hMJ) ≫
      CommRingCat.ofHom (Ideal.quotientMap K φ hJK) =
      CommRingCat.ofHom (Ideal.quotientMap L φ hML) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor hLK) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  -- Elementwise form of the cocone condition.
  have key : ∀ (W : CommRingCat.{u}) (u : CommRingCat.of (S ⧸ J) ⟶ W)
      (v : CommRingCat.of (T ⧸ L) ⟶ W),
      CommRingCat.ofHom (Ideal.Quotient.factor hMJ) ≫ u =
        CommRingCat.ofHom (Ideal.quotientMap L φ hML) ≫ v →
      ∀ x : S, u.hom (Ideal.Quotient.mk J x) = v.hom (Ideal.Quotient.mk L (φ x)) := by
    intro W u v hw x
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom hw) (Ideal.Quotient.mk M x)
  -- The kernel condition making the descent along `T ↠ T ⧸ K` well defined.
  have hker (s : Limits.PushoutCocone (CommRingCat.ofHom (Ideal.Quotient.factor hMJ))
      (CommRingCat.ofHom (Ideal.quotientMap L φ hML))) :
      ∀ a ∈ K, (s.inr.hom.comp (Ideal.Quotient.mk L)) a = 0 := by
    have hJ : J.map φ ≤ RingHom.ker (s.inr.hom.comp (Ideal.Quotient.mk L)) := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj ↦ ?_
      change s.inr.hom (Ideal.Quotient.mk L (φ j)) = 0
      rw [← key _ s.inl s.inr s.condition j,
        Ideal.Quotient.eq_zero_iff_mem.mpr hj, map_zero]
    have hLker : L ≤ RingHom.ker (s.inr.hom.comp (Ideal.Quotient.mk L)) := fun z hz ↦ by
      change s.inr.hom (Ideal.Quotient.mk L z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
    exact fun a ha ↦ hK.trans (sup_le hJ hLker) ha
  refine IsPushout.of_isColimit (Limits.PushoutCocone.IsColimit.mk hcomm
    (fun s ↦ CommRingCat.ofHom
      (Ideal.Quotient.lift K (s.inr.hom.comp (Ideal.Quotient.mk L)) (hker s)))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m _ h₂ ↦ ?_))
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (key _ s.inl s.inr s.condition a).symm
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom h₂) (Ideal.Quotient.mk L a)

/-- The spectra of a pushout square of quotient rings form a pullback square of schemes. -/
private theorem isPullback_specMap_quotientMap {S T : Type u} [CommRing S] [CommRing T]
    (φ : S →+* T) {M J : Ideal S} {L K : Ideal T} (hMJ : M ≤ J) (hLK : L ≤ K)
    (hML : M ≤ Ideal.comap φ L) (hJK : J ≤ Ideal.comap φ K)
    (hK : K ≤ J.map φ ⊔ L) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLK)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ hJK)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap L φ hML)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMJ))) :=
  (isPushout_quotientMap φ hMJ hLK hML hJK hK).op.map Scheme.Spec

/-- The canonical map carries a weak ideal of definition `J` of the base into the kernel of
the projection of the relative completion at `J`. -/
theorem le_comap_ker_projection {B A : Type u} [CommRing B] [TopologicalSpace B]
    [CommRing A] (f : B →+* A) (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    J.1 ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f)
      (RingHom.ker (TopologicalRing.CompletionOver.projection f J)) := by
  intro b hb
  change TopologicalRing.CompletionOver.projection f J
    (TopologicalRing.CompletionOver.canonicalMap f b) = 0
  rw [TopologicalRing.CompletionOver.projection_canonicalMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hb)

/-- **Stacks 0ANM.** The affine base change of the relative completion along a quotient stage:
`Spec (A / JA) = Spec (B / J) ×_{Spec (B / M)} Spec (A^ / L)`, for an open ideal `L` of `A^`
inside `ker (A^ → A / JA)` and an ideal `M ⊆ J` of `B` whose image lies in `L`. -/
@[stacks 0ANM "the affine base change of the completion along a quotient stage"]
theorem isPullback_specMap_kerProjection {B A : Type u} [CommRing B]
    [TopologicalSpace B] [CommRing A] (f : B →+* A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    {M : Ideal B} {L : Ideal (TopologicalRing.CompletionOver f)}
    (hMJ : M ≤ J.1) (hLopen : IsOpen (L : Set (TopologicalRing.CompletionOver f)))
    (hLK : L ≤ RingHom.ker (TopologicalRing.CompletionOver.projection f J))
    (hML : M ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) L) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLK)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (RingHom.ker (TopologicalRing.CompletionOver.projection f J))
        (TopologicalRing.CompletionOver.canonicalMap f) (le_comap_ker_projection f J))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap L
        (TopologicalRing.CompletionOver.canonicalMap f) hML)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMJ))) :=
  isPullback_specMap_quotientMap _ hMJ hLK hML (le_comap_ker_projection f J)
    (le_of_eq (ker_projection_eq_sup f J L hLopen hLK))

end BaseChange

section SheafBaseChange

attribute [local instance] sheaf_hasColimits

/-- The base changes of a morphism along the legs of a universal colimit cocone are jointly
epimorphic, since they assemble into a colimit cocone over the source of the morphism. -/
private theorem hom_ext_of_pullback_colimit_ι {Q : Type w₁} [Category.{w₂} Q]
    [HasPullbacks Q] {I : Type v₁} [Category.{v₂} I] {G : I ⥤ Q} {c : Cocone G}
    (hU : IsUniversalColimit c) {P T : Q} (ψ : P ⟶ c.pt) {α β : P ⟶ T}
    (h : ∀ i : I, pullback.fst ψ (c.ι.app i) ≫ α = pullback.fst ψ (c.ι.app i) ≫ β) :
    α = β := by
  have hlift (i j : I) (v : i ⟶ j) :
      pullback.fst ψ (c.ι.app i) ≫ ψ =
        (pullback.snd ψ (c.ι.app i) ≫ G.map v) ≫ c.ι.app j := by
    rw [Category.assoc, c.w v]
    exact pullback.condition
  let m (i j : I) (v : i ⟶ j) : pullback ψ (c.ι.app i) ⟶ pullback ψ (c.ι.app j) :=
    pullback.lift (pullback.fst ψ (c.ι.app i)) (pullback.snd ψ (c.ι.app i) ≫ G.map v)
      (hlift i j v)
  have hmfst (i j : I) (v : i ⟶ j) :
      m i j v ≫ pullback.fst ψ (c.ι.app j) = pullback.fst ψ (c.ι.app i) :=
    pullback.lift_fst _ _ _
  have hmsnd (i j : I) (v : i ⟶ j) :
      m i j v ≫ pullback.snd ψ (c.ι.app j) = pullback.snd ψ (c.ι.app i) ≫ G.map v :=
    pullback.lift_snd _ _ _
  let F : I ⥤ Q :=
    { obj i := pullback ψ (c.ι.app i)
      map {i j} v := m i j v
      map_id i := by
        refine pullback.hom_ext ?_ ?_
        · rw [hmfst, Category.id_comp]
        · rw [hmsnd, G.map_id, Category.comp_id, Category.id_comp]
      map_comp {i j k} v w := by
        refine pullback.hom_ext ?_ ?_
        · calc m i k (v ≫ w) ≫ pullback.fst ψ (c.ι.app k)
              = pullback.fst ψ (c.ι.app i) := hmfst i k (v ≫ w)
            _ = m i j v ≫ pullback.fst ψ (c.ι.app j) := (hmfst i j v).symm
            _ = m i j v ≫ m j k w ≫ pullback.fst ψ (c.ι.app k) := by rw [hmfst j k w]
            _ = (m i j v ≫ m j k w) ≫ pullback.fst ψ (c.ι.app k) :=
                (Category.assoc _ _ _).symm
        · calc m i k (v ≫ w) ≫ pullback.snd ψ (c.ι.app k)
              = pullback.snd ψ (c.ι.app i) ≫ G.map (v ≫ w) := hmsnd i k (v ≫ w)
            _ = pullback.snd ψ (c.ι.app i) ≫ G.map v ≫ G.map w := by rw [G.map_comp]
            _ = (pullback.snd ψ (c.ι.app i) ≫ G.map v) ≫ G.map w :=
                (Category.assoc _ _ _).symm
            _ = (m i j v ≫ pullback.snd ψ (c.ι.app j)) ≫ G.map w := by rw [hmsnd i j v]
            _ = m i j v ≫ pullback.snd ψ (c.ι.app j) ≫ G.map w := Category.assoc _ _ _
            _ = m i j v ≫ m j k w ≫ pullback.snd ψ (c.ι.app k) := by rw [hmsnd j k w]
            _ = (m i j v ≫ m j k w) ≫ pullback.snd ψ (c.ι.app k) :=
                (Category.assoc _ _ _).symm }
  have hFfst (i j : I) (v : i ⟶ j) :
      F.map v ≫ pullback.fst ψ (c.ι.app j) = pullback.fst ψ (c.ι.app i) := hmfst i j v
  have hFsnd (i j : I) (v : i ⟶ j) :
      F.map v ≫ pullback.snd ψ (c.ι.app j) = pullback.snd ψ (c.ι.app i) ≫ G.map v :=
    hmsnd i j v
  let cP : Cocone F :=
    { pt := P
      ι :=
        { app i := pullback.fst ψ (c.ι.app i)
          naturality := fun i j v ↦ (hFfst i j v).trans (Category.comp_id _).symm } }
  let α' : F ⟶ G :=
    { app i := pullback.snd ψ (c.ι.app i)
      naturality := fun i j v ↦ hFsnd i j v }
  have hcomm : α' ≫ c.ι = cP.ι ≫ (Functor.const I).map ψ :=
    NatTrans.ext (funext fun i ↦ pullback.condition.symm)
  have hα : NatTrans.Equifibered α' := by
    intro i j v
    refine IsPullback.of_right ?_ (hFsnd i j v) (IsPullback.of_hasPullback ψ (c.ι.app j))
    rw [hFfst i j v, c.w v]
    exact IsPullback.of_hasPullback ψ (c.ι.app i)
  exact (hU cP α' ψ hcomm hα fun i ↦ IsPullback.of_hasPullback ψ (c.ι.app i)).some.hom_ext h

/-- The embedding of the affine objects of the big fppf site over `S` into the fppf sheaves,
the functor the canonical diagram of a formal spectrum is assembled from. -/
private noncomputable abbrev siteSheaf (T : BigFppfSite.{u}) (X : Scheme.{u}) (hX : T.Contains X) :
    BigAffineFppf T X hX ⥤ Sheaf (BigFppfOver.topology T X hX) (Type (u + 1)) :=
  BigAffineFppf.inclusion T X hX ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology T X hX)

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

section Monos

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The weak ideals of definition of a topological ring are directed under reverse
inclusion, the intersection of two of them being one. -/
private theorem isDirected_weakIdeals :
    IsDirected (OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) (· ≤ ·) := by
  refine ⟨fun J K ↦ ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 K.2.1⟩, ?_, ?_⟩⟩
  · exact (inf_le_left : (J.1 : Ideal A) ⊓ K.1 ≤ J.1)
  · exact (inf_le_right : (J.1 : Ideal A) ⊓ K.1 ≤ K.1)

/-- The transition morphisms of the canonical diagram of a formal spectrum are
monomorphisms: the transition ring maps are surjective. -/
private theorem mono_formalSpectrumDiagram_map (D : QuotientSystem 𝔅 S hS A)
    {J K : OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)} (v : J ⟶ K) :
    Mono ((formalSpectrumDiagram D).map v) := by
  have hclosed : IsClosedImmersion ((BigFppfOver.toScheme 𝔅 S hS).map
      ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map v))) := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show (K.1 : Ideal A) ≤ J.1 from leOfHom v))))
    exact IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (show (K.1 : Ideal A) ≤ J.1 from leOfHom v))
  have hm : Mono ((BigFppfOver.toScheme 𝔅 S hS).map
      ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map v))) := by
    let _ := hclosed
    infer_instance
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying (BigFppfOver.topology 𝔅 S hS)
    (BigFppfOver.toScheme 𝔅 S hS) ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map v)) hm

/-- Every quotient stage of a formal spectrum includes into it as a monomorphism: the
canonical diagram is filtered with monomorphic transitions. -/
private theorem mono_formalSpectrumInclusion [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem 𝔅 S hS A)
    (J : OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) :
    Mono (formalSpectrumInclusion D J) := by
  let _ : Nonempty (OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) :=
    ⟨OrderDual.toDual ⟨hA.1.choose, hA.1.choose_spec⟩⟩
  let _ : IsDirected (OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) (· ≤ ·) :=
    isDirected_weakIdeals
  exact Sheaf.mono_colimit_ι_of_mono_transition (formalSpectrumDiagram D)
    (fun _ _ v ↦ mono_formalSpectrumDiagram_map D v) J

/-- The canonical diagram of a formal spectrum has a universal colimit cocone, being a
filtered diagram of sheaves of types. -/
private theorem isUniversalColimit_formalSpectrum [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem 𝔅 S hS A) :
    IsUniversalColimit (colimit.cocone (formalSpectrumDiagram D)) := by
  let _ : Nonempty (OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) :=
    TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  let _ : IsDirected (OrderDual (TopologicalRing.WeakIdealOfDefinitionIndex A)) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  exact sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology 𝔅 S hS)
    (formalSpectrumDiagram D)

end Monos

section CompletionBaseChange

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] (f : B →+* A)

/-- The kernel of the projection of the relative completion onto `A / JA`, as a weak ideal of
definition of the relative completion. -/
def kerProjectionIdeal (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f) :=
  ⟨RingHom.ker (TopologicalRing.CompletionOver.projection f J),
    TopologicalRing.projection_ker_isWeakIdealOfDefinition f J⟩

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {D : QuotientSystem 𝔅 S hS B}
  {E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)}

/-- A weak ideal of definition of the base maps into the kernel of the projection of the
relative completion at that same ideal. -/
theorem le_comap_kerProjectionIdeal (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1 := by
  rw [hg]
  exact le_comap_ker_projection f J

omit [IsTopologicalRing B] [IsLinearTopology B B] in
/-- The induced map of quotients attached to a continuous map whose ring map is the canonical
one is the one attached to the canonical map itself. -/
private theorem quotientMap_toRingHom_eq (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    {J : TopologicalRing.WeakIdealOfDefinitionIndex B}
    {L : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f)}
    (h : J.1 ≤ Ideal.comap g.toRingHom L.1)
    (h' : J.1 ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) L.1) :
    Ideal.quotientMap L.1 g.toRingHom h =
      Ideal.quotientMap L.1 (TopologicalRing.CompletionOver.canonicalMap f) h' := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [Ideal.quotientMap_mk, hg]

/-- The affine base-change square of the relative completion, written for a continuous map
whose underlying ring map is the canonical one. -/
private theorem isPullback_specMap_stage (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J M : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (L : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f))
    (hMJ : M.1 ≤ J.1) (hLK : L.1 ≤ (kerProjectionIdeal f J).1)
    (hML : M.1 ≤ Ideal.comap g.toRingHom L.1)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLK)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (kerProjectionIdeal f J).1 g.toRingHom hJK)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 g.toRingHom hML)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hMJ))) := by
  have hMLc : M.1 ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) L.1 := by
    rw [← hg]; exact hML
  rw [quotientMap_toRingHom_eq f g hg hJK (le_comap_ker_projection f J),
    quotientMap_toRingHom_eq f g hg hML hMLc]
  exact isPullback_specMap_kerProjection f J hMJ L.2.1 hLK hMLc

/-- The affine base-change square of the relative completion, transported into the fppf
sheaves: for `L` inside `ker (A^ → A / JA)` and `M ⊆ J` mapping into `L`, the stage of
`ker (A^ → A / JA)` is the fibre product of the stage of `J` and the stage of `L`. -/
private theorem isPullback_sheaf_stage (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J M : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (L : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f))
    (hMJ : M.1 ≤ J.1) (hLK : L.1 ≤ (kerProjectionIdeal f J).1)
    (hML : M.1 ≤ Ideal.comap g.toRingHom L.1)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1) :
    IsPullback ((siteSheaf 𝔅 S hS).map (E.transition hLK))
      ((siteSheaf 𝔅 S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK))
      ((siteSheaf 𝔅 S hS).map (g.stageMap M L hML))
      ((siteSheaf 𝔅 S hS).map (D.transition hMJ)) := by
  have hsite : IsPullback ((BigAffineFppf.inclusion 𝔅 S hS).map (E.transition hLK))
      ((BigAffineFppf.inclusion 𝔅 S hS).map
        (g.stageMap J (kerProjectionIdeal f J) hJK))
      ((BigAffineFppf.inclusion 𝔅 S hS).map (g.stageMap M L hML))
      ((BigAffineFppf.inclusion 𝔅 S hS).map (D.transition hMJ)) := by
    refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme 𝔅 S hS) ?_
    exact isPullback_specMap_stage f g hg J M L hMJ hLK hML hJK
  let _ : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)) := by
    dsimp only [Sheaf.sheafifiedYoneda]
    infer_instance
  exact hsite.map (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS))

/-- Every base change of `Spf A^ ⟶ Spf B` along a quotient stage of the base, restricted to
a quotient stage of `A^`, factors through the stage of the kernel of the projection. -/
private theorem exists_factor_stage_pullback
    (hB : TopologicalRing.IsWeaklyAdmissible B) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1)
    (θ : (siteSheaf 𝔅 S hS).obj (E.stage (kerProjectionIdeal f J)) ⟶
      pullback (formalSpectrumInclusion D (OrderDual.toDual J)) (formalSpectrumMap hB g))
    (hθfst : θ ≫ pullback.fst (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g) =
      (siteSheaf 𝔅 S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK))
    (hθsnd : θ ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g) =
      formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)))
    (L : OrderDual
      (TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f))) :
    ∃ c, c ≫ θ = pullback.fst (pullback.snd
        (formalSpectrumInclusion D (OrderDual.toDual J)) (formalSpectrumMap hB g))
      (formalSpectrumInclusion E L) := by
  classical
  let L' : TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f) :=
    ⟨(L.1 : Ideal (TopologicalRing.CompletionOver f)) ⊓ (kerProjectionIdeal f J).1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right L.2
        (kerProjectionIdeal f J).2.1⟩
  have hL'L : L'.1 ≤ (L.1 : Ideal (TopologicalRing.CompletionOver f)) := inf_le_left
  have hL'K : L'.1 ≤ (kerProjectionIdeal f J).1 := inf_le_right
  have hMopen : IsOpen ((Ideal.comap
      (TopologicalRing.CompletionOver.canonicalMap f) L'.1 : Ideal B) : Set B) := by
    change IsOpen (TopologicalRing.CompletionOver.canonicalMap f ⁻¹'
      (L'.1 : Set (TopologicalRing.CompletionOver f)))
    exact L'.2.1.preimage (TopologicalRing.continuous_canonicalMap f)
  let M : TopologicalRing.WeakIdealOfDefinitionIndex B :=
    ⟨J.1 ⊓ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap f) L'.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 hMopen⟩
  have hMJ : M.1 ≤ J.1 := inf_le_left
  have hML : M.1 ≤ Ideal.comap g.toRingHom L'.1 := by
    rw [hg]
    exact inf_le_right
  have HQ := isPullback_sheaf_stage f g hg J M L' hMJ hL'K hML hJK
  let sm := (siteSheaf 𝔅 S hS).map (E.transition hL'L)
  let sk := (siteSheaf 𝔅 S hS).map (E.transition hL'K)
  let gm := (siteSheaf 𝔅 S hS).map (g.stageMap M L' hML)
  let dm := (siteSheaf 𝔅 S hS).map (D.transition hMJ)
  let Φ := formalSpectrumMap hB g
  let ιJ := formalSpectrumInclusion D (OrderDual.toDual J)
  let ιM := formalSpectrumInclusion D (OrderDual.toDual M)
  let ιK := formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J))
  let ιL := formalSpectrumInclusion E L
  let ιL' := formalSpectrumInclusion E (OrderDual.toDual L')
  let ψ := pullback.snd ιJ Φ
  let qJ := pullback.fst ιJ Φ
  let p := pullback.fst ψ ιL
  let uu := pullback.snd ψ ιL
  have hcond1 : p ≫ ψ = uu ≫ ιL := pullback.condition
  have hcond2 : qJ ≫ ιJ = ψ ≫ Φ := pullback.condition
  have hwE : sm ≫ ιL' = ιL :=
    colimit.w (formalSpectrumDiagram E) (homOfLE (show L ≤ OrderDual.toDual L' from hL'L))
  have hwK : sk ≫ ιL' = ιK :=
    colimit.w (formalSpectrumDiagram E)
      (homOfLE (show OrderDual.toDual (kerProjectionIdeal f J) ≤
        OrderDual.toDual L' from hL'K))
  have hwD : dm ≫ ιM = ιJ :=
    colimit.w (formalSpectrumDiagram D)
      (homOfLE (show OrderDual.toDual J ≤ OrderDual.toDual M from hMJ))
  have hspecM : ιL' ≫ Φ = gm ≫ ιM := formalSpectrumMap_spec hB g M L' hML
  have hmonoM : Mono ιM := formalSpectrumInclusion_mono 𝔅 S hS hB.1 D _
  have hcompat : (uu ≫ sm) ≫ gm = (p ≫ qJ) ≫ dm := by
    refine hmonoM.right_cancellation _ _ ?_
    have e1 : ((uu ≫ sm) ≫ gm) ≫ ιM = (uu ≫ sm) ≫ gm ≫ ιM := Category.assoc _ _ _
    have e2 : (uu ≫ sm) ≫ gm ≫ ιM = (uu ≫ sm) ≫ ιL' ≫ Φ :=
      congrArg (fun z ↦ (uu ≫ sm) ≫ z) hspecM.symm
    have e3 : (uu ≫ sm) ≫ ιL' ≫ Φ = ((uu ≫ sm) ≫ ιL') ≫ Φ := (Category.assoc _ _ _).symm
    have e4 : ((uu ≫ sm) ≫ ιL') ≫ Φ = (uu ≫ sm ≫ ιL') ≫ Φ :=
      congrArg (fun z ↦ z ≫ Φ) (Category.assoc uu sm ιL')
    have e5 : (uu ≫ sm ≫ ιL') ≫ Φ = (uu ≫ ιL) ≫ Φ :=
      congrArg (fun z ↦ (uu ≫ z) ≫ Φ) hwE
    have e6 : (uu ≫ ιL) ≫ Φ = (p ≫ ψ) ≫ Φ := congrArg (fun z ↦ z ≫ Φ) hcond1.symm
    have e7 : (p ≫ ψ) ≫ Φ = p ≫ ψ ≫ Φ := Category.assoc _ _ _
    have e8 : p ≫ ψ ≫ Φ = p ≫ qJ ≫ ιJ := congrArg (fun z ↦ p ≫ z) hcond2.symm
    have e9 : p ≫ qJ ≫ ιJ = (p ≫ qJ) ≫ ιJ := (Category.assoc _ _ _).symm
    have e10 : (p ≫ qJ) ≫ ιJ = (p ≫ qJ) ≫ dm ≫ ιM :=
      congrArg (fun z ↦ (p ≫ qJ) ≫ z) hwD.symm
    have e11 : (p ≫ qJ) ≫ dm ≫ ιM = ((p ≫ qJ) ≫ dm) ≫ ιM := (Category.assoc _ _ _).symm
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans
      (e7.trans (e8.trans (e9.trans (e10.trans e11)))))))))
  refine ⟨HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hθfst]
    exact HQ.lift_snd _ _ _
  · have f1 : (HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ θ) ≫ ψ =
        HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ θ ≫ ψ := Category.assoc _ _ _
    have f2 : HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ θ ≫ ψ =
        HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ ιK :=
      congrArg (fun z ↦ HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ z) hθsnd
    have f3 : HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ ιK =
        HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ sk ≫ ιL' :=
      congrArg (fun z ↦ HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ z) hwK.symm
    have f4 : HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ sk ≫ ιL' =
        (HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ sk) ≫ ιL' := (Category.assoc _ _ _).symm
    have f5 : (HQ.lift (uu ≫ sm) (p ≫ qJ) hcompat ≫ sk) ≫ ιL' = (uu ≫ sm) ≫ ιL' :=
      congrArg (fun z ↦ z ≫ ιL') (HQ.lift_fst _ _ _)
    have f6 : (uu ≫ sm) ≫ ιL' = uu ≫ sm ≫ ιL' := Category.assoc _ _ _
    have f7 : uu ≫ sm ≫ ιL' = uu ≫ ιL := congrArg (fun z ↦ uu ≫ z) hwE
    have f8 : uu ≫ ιL = p ≫ ψ := hcond1.symm
    exact f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans (f7.trans f8))))))

/-- **Stacks 0ANM.** The base change of the formal spectrum of the relative completion along
a quotient stage of the base is the spectrum of the corresponding quotient of `A`, that is
`Spec (A / JA) = Spec (B / J) ×_{Spf B} Spf A^`. -/
@[stacks 0ANM "the base change of the completion along a quotient stage"]
theorem isPullback_formalSpectrumMap_kerProjection
    (hB : TopologicalRing.IsWeaklyAdmissible B) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (hJK : J.1 ≤ Ideal.comap g.toRingHom (kerProjectionIdeal f J).1) :
    IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map
          (g.stageMap J (kerProjectionIdeal f J) hJK)))
      (formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)))
      (formalSpectrumInclusion D (OrderDual.toDual J))
      (formalSpectrumMap hB g) := by
  classical
  have hC : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletionOver f) :=
    TopologicalRing.completionOver_isWeaklyAdmissible f hB
  have hsq : (siteSheaf 𝔅 S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK) ≫
        formalSpectrumInclusion D (OrderDual.toDual J) =
      formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)) ≫
        formalSpectrumMap hB g :=
    (formalSpectrumMap_spec hB g J (kerProjectionIdeal f J) hJK).symm
  let Θ := pullback.lift
    (f := formalSpectrumInclusion D (OrderDual.toDual J)) (g := formalSpectrumMap hB g)
    ((siteSheaf 𝔅 S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK))
    (formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J))) hsq
  have hθfst : Θ ≫ pullback.fst (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g) =
      (siteSheaf 𝔅 S hS).map (g.stageMap J (kerProjectionIdeal f J) hJK) :=
    pullback.lift_fst _ _ _
  have hθsnd : Θ ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g) =
      formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)) :=
    pullback.lift_snd _ _ _
  have hmonoK : Mono (formalSpectrumInclusion E
      (OrderDual.toDual (kerProjectionIdeal f J))) :=
    formalSpectrumInclusion_mono 𝔅 S hS hC.1 E _
  have hmono : Mono Θ := by
    refine ⟨fun a b hab ↦ hmonoK.right_cancellation a b ?_⟩
    have k1 : a ≫ formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)) =
        (a ≫ Θ) ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
          (formalSpectrumMap hB g) :=
      (congrArg (fun z ↦ a ≫ z) hθsnd.symm).trans (Category.assoc _ _ _).symm
    have k2 : (a ≫ Θ) ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
          (formalSpectrumMap hB g) =
        (b ≫ Θ) ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
          (formalSpectrumMap hB g) :=
      congrArg (fun z ↦ z ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g)) hab
    have k3 : (b ≫ Θ) ≫ pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
          (formalSpectrumMap hB g) =
        b ≫ formalSpectrumInclusion E (OrderDual.toDual (kerProjectionIdeal f J)) :=
      (Category.assoc _ _ _).trans (congrArg (fun z ↦ b ≫ z) hθsnd)
    exact k1.trans (k2.trans k3)
  have hepi : Epi Θ := by
    refine ⟨fun a b hab ↦ ?_⟩
    refine hom_ext_of_pullback_colimit_ι (isUniversalColimit_formalSpectrum hC E)
      (pullback.snd (formalSpectrumInclusion D (OrderDual.toDual J))
        (formalSpectrumMap hB g)) ?_
    intro L
    obtain ⟨c, hc⟩ := exists_factor_stage_pullback f hB g hg J hJK Θ hθfst hθsnd L
    refine ((congrArg (fun z ↦ z ≫ a) hc).symm.trans ?_).trans
      (congrArg (fun z ↦ z ≫ b) hc)
    exact (Category.assoc c Θ a).trans
      ((congrArg (fun z ↦ c ≫ z) hab).trans (Category.assoc c Θ b).symm)
  have hiso : IsIso Θ := @isIso_of_mono_of_epi _ _ _ _ _ Θ hmono hepi
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (@asIso _ _ _ _ Θ hiso) hθfst hθsnd

end CompletionBaseChange

end SheafBaseChange

end AlgebraicGeometry.FormalSpace

end
