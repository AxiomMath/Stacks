module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# The formal spectrum of a taut homomorphism is representable by affine morphisms

Let `S` be a scheme and let `φ : A → C` be a continuous homomorphism of weakly admissible
topological rings over `S`. Stacks 0AN5 says that "`Spf φ` is representable by algebraic
spaces" (1), "`Spf φ` is representable by schemes" (2) and "`φ` is taut" (3) are equivalent.
This file proves the implication (3) ⟹ (2), in the sharp form that `Spf φ` is representable by
objects of the site and affine.

(3) implies (2) runs through the identification of `C ⊗̂_A A/I` with `C/J(I)` for `J(I)` the
closure of `IC`, which is Stacks 0AMZ; in the form used here that identification has already
been turned into the cartesian square
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`, so what this file
adds is the passage from the base change over a quotient stage to the base change over an
arbitrary scheme-valued point — the source's unexplained "we conclude".

That passage is a size question, and it is answered by a smallness argument rather than by a
finite type condition. `AlgebraicGeometry.FormalSpace.CompactPullbackRepresentable`, the other
route to representability in this library, asks the represented base changes to be locally of
finite type and quasi-compact, which is what
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact` needs to keep the
glued object inside the site; for a general taut `φ` the base changes are affine, hence
quasi-compact, but not of finite type, so that route is unavailable. Instead the sections of
`Spf C` are shown to be a `u`-small family — every section over an affine object factors
through a quotient stage by Stacks 0AIA, and there are only `#(Ideal C)`-many of those — which
is the hypothesis of
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges`. The uniform
size bound that gluing also wants comes from `QuotientSystem.HasLargeSite` for the target
ring: the coproduct of all the quotient stages of `C` lies in the site, so each stage does,
uniformly. Nothing is assumed about `A`.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_isAffineHom_formalSpectrumMap_of_isTaut`:
  **Stacks 0AN5**, the implication from its condition (3) to its condition (2).

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter

namespace AlgebraicGeometry.FormalSpace

universe w₁ w₂ v₁ v₂ u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point of a formal spectrum out of an *affine* object of the site factors through one of
the quotient stages, by a morphism of the site. This is **Stacks 0AIA** read at the canonical
presentation of `Spf A` by the spectra of the quotients by the weak ideals of definition. No
lifting of the index is needed: `AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage`
accepts an index in any universe, and `WeakIdeals A` lives in `Type u`. -/
private theorem exists_weakIdealFactorization_of_isAffine
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (I : WeakIdeals A) (p : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I)),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p ≫
        formalSpectrumInclusion D I = ξ := by
  classical
  have _ : Nonempty (WeakIdeals A) := nonempty_weakIdeals hA
  have _ : IsDirected (WeakIdeals A) (· ≤ ·) := isDirected_weakIdeals
  obtain ⟨I, g, hg⟩ := exists_factor_to_affine_stage B S hS (formalSpectrum D)
    (WeakIdeals A) D.diagram (fun _ _ f ↦ D.isThickening_map_diagram f) (Iso.refl _)
    ⟨U, hU⟩ ξ
  refine ⟨I, (BigAffineFppf.inclusion B S hS).map g, ?_⟩
  refine Eq.trans ?_ hg
  exact congrArg (fun z ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    ((BigAffineFppf.inclusion B S hS).map g) ≫ z)
    (Category.comp_id (formalSpectrumInclusion D I)).symm

/-- **The sections of a formal spectrum form a `u`-small family.** This is the smallness
argument that replaces a finite type bound in the proof of Stacks 0AN5, (3) ⟹ (2): over an
affine object `U` of the site every section of `Spf A` factors through a quotient stage
`Spec (A ⧸ I)` by Stacks 0AIA, so the sections over `U` are a quotient of
`Σ I : WeakIdeals A, (U ⟶ Spec (A ⧸ I))`, a type in `Type u` because the weak ideals of
definition of `A : Type u` are indexed by a subtype of `Ideal A` and the site is locally
`u`-small. An arbitrary object of the site is covered by its affine opens, and a sheaf is
separated for that covering, so smallness spreads from the affine objects to all of them.

Note that no set-theoretic hypothesis is used: in particular `Spf A` is *not* required to be
an affine formal algebraic space, which is what
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` would be needed for. -/
private theorem small_sections_formalSpectrum
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) :
    FunctorToTypes.Small.{u} (formalSpectrum D).obj := by
  classical
  refine CartesianColimit.small_sections_of_affine B S hS (formalSpectrum D) fun U hU ↦ ?_
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigAffineFppf.inclusion B S hS
  refine small_of_surjective (f := fun z : Σ I : WeakIdeals A, (U ⟶ T.obj (D.stage I)) ↦
    Sheaf.sectionEquiv J (F.map z.2 ≫ formalSpectrumInclusion D z.1)) ?_
  intro x
  obtain ⟨I, p, hp⟩ :=
    exists_weakIdealFactorization_of_isAffine hA D U hU ((Sheaf.sectionEquiv J).symm x)
  refine ⟨⟨I, p⟩, ?_⟩
  change Sheaf.sectionEquiv J (F.map p ≫ formalSpectrumInclusion D I) = x
  rw [hp]
  exact (Sheaf.sectionEquiv J).apply_symm_apply x

/-- **The affine base change of Stacks 0AN5, (3) ⟹ (2).** For a taut `φ : A ⟶ C` and a point
of `Spf A` out of an affine object `U` of the site, the base change of `Spf φ` along it is
represented by the object `U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)` of the site, whose projection to
`U` is an affine morphism and whose size is bounded by `max κ (size U)` for any bound `κ` on
the sizes of the quotient stages of `C`.

The point factors through a stage `Spec (A ⧸ I) ⟶ Spf A` by Stacks 0AIA, and over that stage
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut` identifies the
base change with `Spec (C ⧸ K)` for `K` the closure of `φ(I)C` — which is where tautness is
used, and the only place. Taking the fibre product inside the site keeps the projection affine
(it is a base change of the affine morphism `Spec (C ⧸ K) ⟶ Spec (A ⧸ I)`) and bounds its size
by that of the two factors. -/
private theorem exists_isPullback_isAffineHom_formalSpectrumMap_of_isTaut
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (φ : ContinuousHom D E)
    (hφ : RingHom.IsTaut φ.toRingHom) {κ : Cardinal.{u}}
    (hκ : ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      ((BigAffineFppf.toScheme B S hS).obj (E.stage K)).size ≤ κ)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E)
      (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
          (formalSpectrumMap hA φ) ξ ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
        ((BigFppfOver.toScheme B S hS).obj V).size ≤
          max κ ((BigFppfOver.toScheme B S hS).obj U).size := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp only [F, Sheaf.sheafifiedYoneda]
    infer_instance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  obtain ⟨I, p, hp⟩ := exists_weakIdealFactorization_of_isAffine hA D U hU ξ
  obtain ⟨K, -, hIK, hsq⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E φ hφ I
  have ha : IsAffineHom ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (φ.stageMap I K hIK))) := by
    have _ (X) : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj X)) := BigAffineFppf.isAffine_toScheme_obj B S hS X
    infer_instance
  set w := T.map (φ.stageMap I K hIK)
  have hinner : IsPullback (pullback.fst w p) (pullback.snd w p) w p :=
    IsPullback.of_hasPullback w p
  refine ⟨pullback w p, F.map (pullback.fst w p) ≫ formalSpectrumInclusion E K,
    pullback.snd w p, ?_, MorphismProperty.of_isPullback
      (hinner.map (BigFppfOver.toScheme B S hS)) ha,
    (Space.size_pullback_le B S hS w p).trans (max_le_max (hκ K) le_rfl)⟩
  rw [← hp]
  exact ((hinner.map F).flip.paste_vert hsq.flip).flip

/-- **Stacks 0AN5**, the implication from its condition (3) to its condition (2): if a
continuous homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S` is taut,
then `Spf φ` is representable by objects of the site, and every represented base change of it
is an affine morphism of schemes.

This is the source's own argument. A point of `Spf A` out of an affine object `U` of the site
factors through a quotient stage `Spec (A ⧸ I)` by Stacks 0AIA, and tautness makes the closure
`K` of `φ(I)C` a weak ideal of definition, so that `Spec (C ⧸ K) = Spf C ×_{Spf A}
Spec (A ⧸ I)`; the base change over `U` is then the affine `U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)`.
Passing from the affine points of `Spf A` to arbitrary ones is the gluing of
`AlgebraicGeometry.FormalSpace.CartesianColimit.relative_of_affineBaseChanges` — the step the
source leaves at "we conclude" — and it needs the charts over the affine opens of a test object
to obey a uniform size bound.

Where the source has a convention on the size of the site, this carries the single
set-theoretic hypothesis `hE : E.HasLargeSite`, and only for that uniform bound: it says the
coproduct `∐_K Spec (C ⧸ K)` of all the quotient stages of `C` lies in the site, hence each
stage has size at most that of the coproduct, which is one cardinal below the cutoff. Nothing
is assumed about `A` — in particular not that `Spf A` is an affine formal algebraic space,
which is what the implication (1) ⟹ (3) above needs — because the smallness of the sections of
`Spf C` comes from Stacks 0AIA (`small_sections_formalSpectrum`) rather than from the
set-theoretic condition of Stacks 0AIS. That substitution is what removes the finite type
condition which bounds the size of the coproduct in
`AlgebraicGeometry.FormalSpace.CompactPullbackRepresentable`. -/
theorem relative_isAffineHom_formalSpectrumMap_of_isTaut
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (hE : E.HasLargeSite)
    (φ : ContinuousHom D E) (hφ : RingHom.IsTaut φ.toRingHom) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (formalSpectrumMap hA φ) := by
  classical
  have _ : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : FunctorToTypes.Small.{u} (formalSpectrum E).obj := small_sections_formalSpectrum hC E
  set Y : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K } → Scheme.{u} :=
    fun K ↦ Spec (.of (C ⧸ K.1))
  have hκ : (∐ Y).size < B.cutoff := hE
  have hstage : ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      ((BigAffineFppf.toScheme B S hS).obj (E.stage K)).size ≤ (∐ Y).size := fun K ↦
    @Scheme.size_le_of_isOpenImmersion _ _ (Sigma.ι Y K)
      ((AlgebraicGeometry.sigmaOpenCover Y).map_prop K)
  exact CartesianColimit.relative_of_affineBaseChanges B S hS (@IsAffineHom.{u})
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyIsAffineHomIsAffine)
    (formalSpectrumMap hA φ) hκ
    fun U hU ξ ↦ exists_isPullback_isAffineHom_formalSpectrumMap_of_isTaut
      hA hC D E φ hφ hstage U hU ξ

end AlgebraicGeometry.FormalSpace

end
