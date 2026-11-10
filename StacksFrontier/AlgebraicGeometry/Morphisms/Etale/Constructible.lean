module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.Topology.Constructible.Homeomorph

/-!
# Local constructibility descends along a surjective étale morphism

If `g : T ⟶ V` is surjective and étale and the inverse image of `s ⊆ V` is locally
constructible, then `s` itself is locally constructible.

Over an affine target the argument is direct: the restriction of `g` to an affine open of the
source is an affine morphism of finite presentation, so it carries locally constructible sets
to locally constructible sets, and the images of the affine opens of the source cover `V`
because an étale morphism is open and `g` is surjective. The general case follows by covering
the target with affine opens and base changing.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_of_etale_surjective_of_isAffine`
* `AlgebraicGeometry.isLocallyConstructible_of_etale_surjective`
-/

@[expose] public section

open CategoryTheory Topology
open scoped Set.Notation

universe u

namespace AlgebraicGeometry

/-- Local constructibility descends along a surjective étale morphism with affine target:
the restriction of the morphism to an affine open of the source is an affine morphism of
finite presentation, whose image of the inverse image of `s` is the intersection of `s` with
an open subset of the target, and those open subsets cover the target. -/
theorem isLocallyConstructible_of_etale_surjective_of_isAffine {T V : Scheme.{u}}
    (hV : IsAffine V) (g : T ⟶ V) (hg : Etale g) (hgs : Function.Surjective g) {s : Set V}
    (hs : IsLocallyConstructible (g ⁻¹' s)) : IsLocallyConstructible s := by
  set C := T.affineCover
  set O : C.I₀ → V.Opens := fun i ↦ ⟨Set.range (C.f i ≫ g), (C.f i ≫ g).isOpenMap.isOpen_range⟩
  have hcover : TopologicalSpace.IsOpenCover O := by
    refine TopologicalSpace.IsOpenCover.of_sets (v := fun i ↦ (O i : Set V))
      (fun i ↦ (O i).2) ?_
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hgs y
    obtain ⟨i, hi⟩ := C.isOpenCover_opensRange.exists_mem x
    obtain ⟨z, hz⟩ := Set.mem_range.mp hi
    exact ⟨i, z, by change g (C.f i z) = y; rw [hz]; exact hx⟩
  refine IsLocallyConstructible.of_isOpenCover hcover fun i ↦ ?_
  have hpre : IsLocallyConstructible ((C.f i ≫ g) ⁻¹' s) :=
    isLocallyConstructible_preimage (C.f i) hs
  have himage := (C.f i ≫ g).isLocallyConstructible_image hpre
  have hset : (C.f i ≫ g) '' ((C.f i ≫ g) ⁻¹' s) = (O i : Set V) ∩ s :=
    Set.image_preimage_eq_range_inter
  have hsub := himage.preimage_of_isOpenEmbedding (O i).2.isOpenEmbedding_subtypeVal
  rw [hset] at hsub
  change IsLocallyConstructible ((Subtype.val : O i → V) ⁻¹' ((O i : Set V) ∩ s)) at hsub
  have heq : (Subtype.val : O i → V) ⁻¹' ((O i : Set V) ∩ s) =
      (Subtype.val : O i → V) ⁻¹' s := Set.ext fun x ↦ by simp
  rwa [heq] at hsub

/-- **Local constructibility descends along a surjective étale morphism of schemes.** The
target is covered by affine opens, over each of which the base change of the morphism is
again surjective and étale, so the affine case applies. -/
theorem isLocallyConstructible_of_etale_surjective {T V : Scheme.{u}} (g : T ⟶ V)
    (hg : Etale g) (hgs : Function.Surjective g) {s : Set V}
    (hs : IsLocallyConstructible (g ⁻¹' s)) : IsLocallyConstructible s := by
  refine IsLocallyConstructible.of_isOpenCover V.affineCover.isOpenCover_opensRange fun i ↦ ?_
  set v := V.affineCover.f i
  have hgsurj : Surjective g := ⟨hgs⟩
  have hpre : IsLocallyConstructible (Limits.pullback.snd g v ⁻¹' (v ⁻¹' s)) := by
    have hset : Limits.pullback.snd g v ⁻¹' (v ⁻¹' s) =
        Limits.pullback.fst g v ⁻¹' (g ⁻¹' s) := by
      ext x
      change v (Limits.pullback.snd g v x) ∈ s ↔ g (Limits.pullback.fst g v x) ∈ s
      exact Iff.of_eq (congrArg (fun y ↦ y ∈ s) (congrArg (fun f ↦ f x)
        (Limits.pullback.condition (f := g) (g := v)))).symm
    rw [hset]
    exact isLocallyConstructible_preimage _ hs
  have hlocV := isLocallyConstructible_of_etale_surjective_of_isAffine
    (Scheme.isAffine_affineCover V i) (Limits.pullback.snd g v) inferInstance
    (Limits.pullback.snd g v).surjective hpre
  -- Transport along the homeomorphism of the affine chart with its open range.
  set e : V.affineCover.X i ≃ₜ (v.opensRange : Set V) :=
    ((Homeomorph.Set.univ (V.affineCover.X i)).symm.trans
      (v.isOpenEmbedding.isEmbedding.homeomorphImage Set.univ)).trans
      (Homeomorph.setCongr (show ((v : V.affineCover.X i → V) '' Set.univ) =
        (v.opensRange : Set V) by ext y; simp))
  change IsLocallyConstructible ((v.opensRange : Set V) ↓∩ s)
  exact (e.isLocallyConstructible_preimage_iff _).mp hlocV

end AlgebraicGeometry

end
