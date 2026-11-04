module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
import StacksCore.Tactic.StacksAttribute

/-!
# A taut homomorphism has representable formal spectrum (Stacks 0AN5, (3) implies (1))

Let `S` be a scheme contained in a big fppf site `B` and let `φ : A ⟶ C` be a continuous
homomorphism of weakly admissible topological rings over `S`. **Stacks 0AN5** says that
`Spf φ : Spf C ⟶ Spf A` is representable by algebraic spaces if and only if it is representable
by schemes if and only if `φ` is taut. This file proves the implication from tautness, condition
(3), to representability by algebraic spaces, condition (1).

`StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful` carries the implication
(2) ⟹ (1) of the same lemma, which is the formal one: a base change which is an object of the
site is in particular an algebraic space. That implication cannot be used to reach condition (1)
from condition (3), its hypothesis being representability itself. The two together give
(3) ⟹ (1) only once the base change of `Spf φ` along an *arbitrary* scheme-valued point of
`Spf A` is known to be representable, and that passage — from the quasi-compact points, where
the source computes the base change, to all of them — is what is proved here.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`
  — **Stacks 0AN5**, the implication from its condition (3) to its condition (1).

## Implementation notes

The source's argument computes the base change over a weak ideal of definition `I ⊆ A`: the
closure `K` of `φ(I)C` is open by tautness, `C ⊗̂_A A/I = C/K`, and so
`Spf C ×_{Spf A} Spec (A/I) = Spec (C/K)`. That cartesian square is
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`. A point of `Spf A`
out of a quasi-compact object of the site factors through a stage `Spec (A/I)` by Stacks 0AIA
(`AlgebraicGeometry.FormalSpace.exists_factorsThroughStage_of_compactSpace`), and the base
change along the factorisation is the fibre product of the factorisation with the stage
morphism, an object of the site. The source then writes "we conclude", which is the step taken
here: representability by algebraic spaces is Zariski local on the target
(`AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover`), so a point
out of an arbitrary object `T` of the site may be covered by the coproduct `V` of the affine
opens of `T`, each of which is quasi-compact. Coproducts of fppf sheaves are universal, so the
base change over `V` is the coproduct of the base changes over the affine opens.

That coproduct has to be an object of the site again, which is where a bound on the representing
objects is needed and is the one thing the two halves already in the library do not supply.
`AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_factorsThroughStage`
produces the representing object through `CategoryTheory.Functor.relativelyRepresentable`, whose
underlying object is a `Classical.choose` and therefore carries no size information, and
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_affine_pullback` asks
for its projection to be of finite type, which `Spec (C/K) ⟶ Spec (A/I)` is not. So the fibre
product is taken explicitly in the site here, and bounded by
`AlgebraicGeometry.FormalSpace.size_pullback_le`: the base change over an affine open `X` of `T`
has size at most the larger of `size X ≤ size T` and `size (Spec (C/K))`.

The uniform bound on the stages of `Spf C` is the hypothesis `E.HasLargeSite` of Stacks 0AIF:
each `Spec (C/K)` is an open subscheme of `∐_K Spec (C/K)`, so its size is at most the size of
that coproduct, which lies below the cutoff exactly when the site contains the coproduct. This
is the condition under which `Spf C` is an affine formal algebraic space at all, and it is a
smallness condition on the chosen site rather than mathematical input, of the same kind as the
`AlgebraicGeometry.FormalSpace.QuotientSystem` data itself. No bound of any kind is placed on
the stages of `Spf A`: the index type of the covering is bounded by `size T` and so are its
members, which is what `AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`
asks for.

Weak admissibility of `C` is used only through
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`; `Spf φ` itself
needs it only on `A`.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

omit [IsTopologicalRing C] [IsLinearTopology C C] in
/-- Under the hypothesis of Stacks 0AIF that the site contain the coproduct of all the quotient
spectra of `C`, that coproduct's size bounds every single quotient spectrum: each of them is an
open subscheme of it. -/
theorem size_stage_le_of_hasLargeSite (E : QuotientSystem B S hS C)
    (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K }) :
    ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.stage K))).size ≤
      (∐ fun J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J } =>
        Spec (.of (C ⧸ J.1))).size := by
  show (Spec (.of (C ⧸ K.1))).size ≤ _
  exact Scheme.size_le_of_mono_locallyOfFinitePresentation
    (Sigma.ι (fun J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J } =>
      Spec (.of (C ⧸ J.1))) K)

/-- **The base change over a point factoring through a stage, with its size.** Let `φ : A ⟶ C`
be a taut continuous homomorphism of weakly admissible topological rings over `S`, let `I` be a
weak ideal of definition of `A` and let `U ⟶ Spf A` be a point of the formal spectrum which
factors through the stage `Spec (A ⧸ I)`. Then the base change of `Spf φ` along that point is
represented by an object `V` of the site whose size is bounded by the larger of `size U` and any
uniform bound `μ` on the stages of `Spf C`.

This is `AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_factorsThroughStage`
with the size of the representing object recorded. The representing object is taken to be the
fibre product `U ×_{Spec (A ⧸ I)} Spec (C ⧸ K)` in the site itself, rather than the one
`CategoryTheory.Functor.relativelyRepresentable` chooses, precisely so that
`AlgebraicGeometry.FormalSpace.size_pullback_le` applies to it. -/
theorem exists_isPullback_size_le_formalSpectrumMap_of_factorsThroughStage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) {μ : Cardinal.{u}}
    (hμ : ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.stage K))).size ≤ μ)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS)
    (g : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D)
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
      formalSpectrumInclusion D I = a) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum E),
      IsPullback q
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA f) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        max μ ((BigFppfOver.toScheme B S hS).obj U).size := by
  classical
  subst ha
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let _ : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  obtain ⟨K, -, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf I
  exact ⟨pullback (T.map (f.stageMap I K hIK)) g,
    pullback.snd (T.map (f.stageMap I K hIK)) g,
    F.map (pullback.fst (T.map (f.stageMap I K hIK)) g) ≫ formalSpectrumInclusion E K,
    ((IsPullback.of_hasPullback (T.map (f.stageMap I K hIK)) g).map F).paste_horiz hsq,
    (Space.size_pullback_le B S hS (T.map (f.stageMap I K hIK)) g).trans
      (max_le_max (hμ K) le_rfl)⟩

/-- **The base change over a point out of a quasi-compact object of the site, with its size.**
A point of `Spf A` out of a quasi-compact object `U` of the site factors through a quotient
stage `Spec (A ⧸ I)` by Stacks 0AIA, so the previous lemma applies to it.

The statement is in terms of the universe-lifted Yoneda embedding into sheaves, which is the
shape the locality criterion and the universality of coproducts consume; the factorisation
through a stage is available for the sheafification of that embedding, and the two are
identified by `CategoryTheory.Sheaf.uliftYonedaIsoSheafifiedYoneda`. -/
theorem exists_isPullback_size_le_formalSpectrumMap_of_compactSpace
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) {μ : Cardinal.{u}}
    (hμ : ∀ K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K },
      ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (E.stage K))).size ≤ μ)
    (U : BigFppfOver B S hS) (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ formalSpectrum E),
      IsPullback q ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p)
        (formalSpectrumMap hA f) ξ ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        max μ ((BigFppfOver.toScheme B S hS).obj U).size := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ε := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨I, g, hg⟩ :=
    exists_factorsThroughStage_of_compactSpace hA.1 D U hU (ε.inv.app U ≫ ξ)
  obtain ⟨V, p, c, hpb, hsize⟩ :=
    exists_isPullback_size_le_formalSpectrumMap_of_factorsThroughStage B S hS hA hC D E f hf
      hμ I U g _ hg
  refine ⟨V, p, ε.hom.app V ≫ c, ?_, hsize⟩
  refine hpb.of_iso' (ε.app V) (Iso.refl _) (ε.app U) (Iso.refl _) (by simp)
    (ε.hom.naturality p).symm (by simp) ?_
  rw [← Iso.app_inv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

/-- **Stacks 0AN5, the implication from its condition (3) to its condition (1).** Let `φ : A ⟶ C`
be a continuous homomorphism of weakly admissible topological rings over `S` whose underlying
ring map is taut, which is condition (3) of Stacks 0AN5. Then `Spf φ : Spf C ⟶ Spf A` is
representable by algebraic spaces over `S`, which is its condition (1).

The hypothesis `hE` is the condition of Stacks 0AIF that the site contain the coproduct of the
quotient spectra of `C`, under which `Spf C` is an affine formal algebraic space; it enters only
as the uniform size bound on those quotient spectra which puts the base change over a
non-quasi-compact point of `Spf A` back in the site. Nothing is assumed about the stages of
`Spf A`. -/
@[stacks 0AN5 "(3) implies (1)"]
theorem isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (hE : E.HasLargeSite)
    (f : ContinuousHom D E) (hf : RingHom.IsTaut f.toRingHom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA f).hom := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  set μ : Cardinal.{u} :=
    (∐ fun J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J } =>
      Spec (.of (C ⧸ J.1))).size
  have hμ := size_stage_le_of_hasLargeSite B S hS E
  refine isRepresentable_of_forall_surjective_etale_cover B S hS _ fun T ξ => ?_
  obtain ⟨ι, X, V, j, q, hXaff, hιsize, hXsize, hqsurj, hqetale, -, ⟨hsheaf⟩⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma B S hS T
  refine ⟨V, q, hqsurj, hqetale, ?_⟩
  let ξV : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ formalSpectrum D :=
    ⟨uliftYoneda.{u + 1}.map q ≫ ξ⟩
  choose W p c hpb hWbound using fun i =>
    exists_isPullback_size_le_formalSpectrumMap_of_compactSpace B S hS hA hC D E f hf hμ (X i)
      (by have := hXaff i; infer_instance)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i) ≫ ξV)
  let ν : Cardinal.{u} := max μ ((BigFppfOver.toScheme B S hS).obj T).size
  have hWsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ ν :=
    fun i => (hWbound i).trans (max_le_max le_rfl (hXsize i))
  obtain ⟨Wt, jw, -, -, -, -, ⟨hWsheaf⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS W (max_lt hE T.left.property)
      (hιsize.trans (le_max_right _ _)) hWsize
  have ht : IsPullback (pullback.snd ξV (formalSpectrumMap hA f))
      (pullback.fst ξV (formalSpectrumMap hA f)) (formalSpectrumMap hA f) ξV :=
    (IsPullback.of_hasPullback ξV (formalSpectrumMap hA f)).flip
  obtain ⟨hPcol⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback
    (BigFppfOver.topology B S hS)
    (fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i)) hsheaf
    (pullback.fst ξV (formalSpectrumMap hA f)) _
    (fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (p i))
    fun i => IsPullback.of_right' (hpb i) ht
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (pullback ξV (formalSpectrumMap hA f))) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
        (IsColimit.coconePointUniqueUpToIso hWsheaf hPcol))
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Wt)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    ((IsPullback.of_hasPullback ξV (formalSpectrumMap hA f)).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).isoPullback hPalg

end AlgebraicGeometry.FormalSpace

end
