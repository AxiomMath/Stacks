module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Descent of properties of representable transformations

Let `a : F ⟶ G` be a representable transformation of presheaves on the big fppf site over a
scheme `S`. A property of scheme morphisms which is local on the target for the fppf topology
descends from the base change of `a` along a transformation `b : H ⟶ G` whose sheafification
is surjective.

## Main results

* `AlgebraicGeometry.Space.presheaf_of_isLocallySurjective_pullback` descends the relative
  morphism property from `H ×_G F ⟶ H` to `F ⟶ G`.

## Implementation notes

The scheme morphism property is pulled back to the full slice category of schemes in the
chosen big fppf site over `S`. Its base-change stability and fppf locality are imposed on
schemes, as in the source, rather than on the slice category. Mathlib's
`CategoryTheory.Presheaf.IsLocallySurjective` is equivalent to local surjectivity of the
induced map of sheafifications, the condition in the source.

## References

* [Stacks Project, Tag 03KD](https://stacks.math.columbia.edu/tag/03KD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism property of a representable transformation descends along a transformation
which becomes surjective after fppf sheafification. -/
@[stacks 03KD]
theorem presheaf_of_isLocallySurjective_pullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : H ⟶ G)
    (ha : yoneda.relativelyRepresentable a)
    (hb : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) b)
    (hbase : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd a b)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  apply (MorphismProperty.relative.of_exists (P := Q) (F := yoneda))
  intro U g
  let ξ : G.obj (Opposite.op U) := yonedaEquiv g
  have hcover : Presheaf.imageSieve b ξ ∈ J U := hb.imageSieve_mem ξ
  have hcoverB : (Sieve.overEquiv U) (Presheaf.imageSieve b ξ) ∈ B.topology U.left :=
    B.topology.mem_over_iff _ |>.mp hcover
  obtain ⟨E, hE, hsub⟩ := exists_covering_refining_sieve B hcoverB
  refine ⟨ha.pullback g, ha.fst g, ha.snd g, ha.isPullback g, ?_⟩
  let v := ha.snd g
  have hfppf : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    have hF : E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion U.left :=
      B.isFppfCovering_of_isCovering hE
    rw [Precoverage.mem_comap_iff] at hF
    simpa [PreZeroHypercover.presieve₀_map] using hF
  change P ((BigFppfOver.toScheme B S hS).map v)
  apply (inferInstance : P.IsLocalAtTarget Scheme.fppfPrecoverage).of_forall_pullbackSnd hfppf
  intro Z k _ hk
  obtain ⟨i⟩ := hk
  let Ui : C := Over.mk (E.f i ≫ U.hom)
  let ui : Ui ⟶ U := Over.homMk (E.f i)
  obtain ⟨η, hηsec⟩ : Presheaf.imageSieve b ξ ui :=
    (Sieve.overEquiv_iff (Presheaf.imageSieve b ξ) (E.f i)).mp (hsub _ _ ⟨i⟩)
  let ηmap : yoneda.obj Ui ⟶ H := yonedaEquiv.symm η
  have hn : G.map ui.op ξ = g.app (Opposite.op Ui) ui := by
    change G.map ui.op (g.app (Opposite.op U) (𝟙 U)) = g.app (Opposite.op Ui) ui
    exact (NatTrans.naturality_apply g ui.op (𝟙 U)).symm
  have hη : ηmap ≫ b = yoneda.map ui ≫ g := by
    apply (yonedaEquiv (X := Ui) (F := G)).injective
    simpa [ηmap, CategoryTheory.yonedaEquiv] using hηsec.trans hn
  let W := pullback v ui
  let wv := pullback.fst v ui
  let wu := pullback.snd v ui
  let k' : yoneda.obj W ⟶ pullback a b :=
    pullback.lift (yoneda.map wv ≫ ha.fst g) (yoneda.map wu ≫ ηmap) (by
      rw [Category.assoc, (ha.isPullback g).w, Category.assoc, hη, ← Functor.map_comp_assoc,
        pullback.condition, Functor.map_comp_assoc])
  have hinner : IsPullback k' (yoneda.map wu) (pullback.snd a b) ηmap := by
    have houter : IsPullback (k' ≫ pullback.fst a b) (yoneda.map wu) a (ηmap ≫ b) := by
      convert ((IsPullback.of_hasPullback v ui).map yoneda).paste_horiz (ha.isPullback g) using 1
      simp [k', wv]
    apply IsPullback.of_right houter ?_ (IsPullback.of_hasPullback a b)
    simp [k', wu]
  have hloc : P ((BigFppfOver.toScheme B S hS).map wu) := hbase.property ηmap k' wu hinner
  have hui : (BigFppfOver.toScheme B S hS).map ui = (E.map B.inclusion).f i := rfl
  have : HasPullback ((BigFppfOver.toScheme B S hS).map v)
      ((BigFppfOver.toScheme B S hS).map ui) := by
    rw [hui]; infer_instance
  have hschemePB := (IsPullback.of_hasPullback v ui).map (BigFppfOver.toScheme B S hS)
  have he : hschemePB.isoPullback.hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map v)
      ((E.map B.inclusion).f i) = (BigFppfOver.toScheme B S hS).map wu := by
    cases hui; exact hschemePB.isoPullback_hom_snd
  exact (P.cancel_left_of_respectsIso hschemePB.isoPullback.hom _).mp (by rwa [he])

end AlgebraicGeometry.Space

end
