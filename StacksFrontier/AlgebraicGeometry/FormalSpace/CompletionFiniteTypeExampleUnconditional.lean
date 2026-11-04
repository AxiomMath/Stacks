module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChangeStages

/-!
# Finite type of the formal spectrum of a relative completion

For a finite type ring map `f : B →+* A` over a weakly admissible topological ring `B`, the
morphism of formal spectra induced by the relative completion `B → A^` is of finite type, with
no restriction on the scheme-valued points along which base changes are taken.

## Main results

* `compactPullbackRepresentable_formalSpectrumMap`: for a taut continuous homomorphism `φ : B ⟶ C`
  of weakly admissible topological rings which is of finite type modulo every weak ideal of
  definition, every base change of `Spf (φ)` along a point out of a quasi-compact object is
  represented by an object whose projection is locally of finite type and quasi-compact.
* `isFiniteType_formalSpectrumMap_completionOver'`: the morphism `Spf A^ ⟶ Spf B` induced by the
  relative completion along a finite type ring map is of finite type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u v

section Quotients

variable {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B] [CommRing A]

end Quotients

add_to_stacks 0ANM "the relative completion of a ring map over a weakly admissible \
topological ring is weakly admissible; no finite type hypothesis is needed"
  completionOver_isWeaklyAdmissible

add_to_stacks 0ANM "the relative completion along a finite type ring map is topologically of \
finite type over the base, which is the ring-theoretic form of the finite type assertion"
  isTopologicallyOfFiniteType_canonicalMap

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A]

section StageBaseChange

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

end StageBaseChange

section CompactPullback

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Let `φ : B ⟶ C` be a continuous homomorphism of weakly admissible topological rings over `S`
which is taut and of finite type modulo every weak ideal of definition. Then the base change of
`Spf (φ)` along a point of `Spf B` out of a quasi-compact object of the site is represented by an
object of the site whose projection is locally of finite type and quasi-compact. This is the
quasi-compact half of the implication (2) ⟹ (1) of Stacks 0ANT. -/
theorem compactPullbackRepresentable_formalSpectrumMap
    (hB : TopologicalRing.IsWeaklyAdmissible B) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem 𝔅 S hS B) (E : QuotientSystem 𝔅 S hS C) (φ : ContinuousHom D E)
    (h : TopologicalRing.FiniteTypeModuloEveryWeakIdeal φ.toRingHom) :
    CompactPullbackRepresentable 𝔅 S hS (formalSpectrumMap hB φ) := by
  classical
  intro U hU ξ
  let _ : (BigFppfOver.topology 𝔅 S hS).Subcanonical := bigFppfOver_subcanonical 𝔅 S hS
  let η := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)
  obtain ⟨I, p₀, hp₀⟩ :=
    exists_factorsThroughStage_of_compactSpace hB.1 D U hU ((η.app U).inv ≫ ξ)
  obtain ⟨W, q, r, hsq, hlft, hqc⟩ :=
    exists_isPullback_isFiniteTypeULift_formalSpectrumMap_of_factorsThroughStage hB hC D E φ h
      I U p₀
  have hsq' : IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q)
      (formalSpectrumMap hB φ) ((η.app U).inv ≫ ξ) :=
    hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (hp₀.trans (Category.id_comp _).symm))
  have hleft : IsPullback ((η.app W).hom)
      ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map q)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q) ((η.app U).hom) :=
    IsPullback.of_horiz_isIso ⟨(η.hom.naturality q).symm⟩
  refine ⟨W, q, (η.app W).hom ≫ r, ?_, hlft, hqc⟩
  have hpaste := hleft.paste_horiz hsq'
  rwa [Iso.hom_inv_id_assoc] at hpaste

end CompactPullback

/-- Let `f : B →+* A` be a finite type ring map over a weakly admissible topological ring `B`,
and `g` a continuous homomorphism whose underlying ring map is the canonical map `B → A^` to the
relative completion. Then `Spf A^ ⟶ Spf B` is of finite type in the sense of Definition 0AM4,
part (2): locally of finite type — representable by algebraic spaces, with every base change of
it along a scheme-valued point of `Spf B` a morphism of algebraic spaces which is locally of
finite type — and quasi-compact in the sense of Definition 0AJC. -/
@[stacks 0ANM "finite type of `Spf ((A')^) → Spf A`: the morphism is of finite type as \
Definition 0AM4, part (2), verbatim. What the argument produces is condition (2) of \
Stacks 0AJJ — representable by algebraic spaces plus of finite type in the Bootstrap sense \
of Stacks 03XZ — and Stacks 0AJJ, \
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, carries it to \
Definition 0AM4, part (2), unconditionally. With no restriction on the scheme-valued point \
of `Spf A` along which the base \
change is taken; the base change along a point out of a quasi-compact scheme `T` is the \
source's `T ×_{Spec (A / I)} Spec (A' / IA')`"]
theorem isFiniteType_formalSpectrumMap_completionOver'
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B) (hf : f.FiniteType)
    (D : QuotientSystem 𝔅 S hS B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    IsFiniteType' 𝔅 S hS (formalSpectrumMap hB g) := by
  refine (isFiniteType_iff_isBootstrapFiniteType 𝔅 S hS (formalSpectrumMap hB g)).mpr ?_
  have hcpr := compactPullbackRepresentable_formalSpectrumMap_completionOver f hB hf D E g hg
  refine ⟨isRepresentableByAlgebraicSpacesULift_of_affine_pullback 𝔅 S hS
    (formalSpectrumMap hB g) hcpr, ?_⟩
  intro U ξ
  show Space.IsFiniteTypeULift.{u + 1} 𝔅 S hS
    (pullback.fst ξ (formalSpectrumMap hB g).hom)
  refine ⟨isLocallyOfFiniteTypeULift_pullback_of_compact_pullback 𝔅 S hS
    (formalSpectrumMap hB g) hcpr U ξ, ?_⟩
  intro Z hZ hZqc γ
  exact Space.isQuasiCompactSpaceULift_of_iso 𝔅 S hS
    (pullbackRightPullbackFstIso ξ (formalSpectrumMap hB g).hom γ).symm
    (isQuasiCompactULift_of_compact_pullback 𝔅 S hS (formalSpectrumMap hB g) hcpr Z hZ hZqc
      (γ ≫ ξ))

end AlgebraicGeometry.FormalSpace

end
