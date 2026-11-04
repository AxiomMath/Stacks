/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Graphs of legs and base change of graph line bundles

Let `k` be a field, `X` and `S` schemes over `k`, and `x : S ⟶ X` a morphism over `k`. Its
graph `Γ_x : S ⟶ X ×_k S` is a section of the second projection.

* When `X` is separated over `k`, `Γ_x` is a closed immersion.
* For `g : S' ⟶ S` over `k`, the square
  ```
  S'  --Γ_{x ∘ g}-->  X ×_k S'
  |g                  |id × g
  S   --Γ_x------->   X ×_k S
  ```
  is cartesian, and so is the square formed by `id × g` and the two second projections. For a
  quasi-coherent `𝒪_S`-module `L` the base-change morphism
  `(id × g)^* Γ_{x,*} L ⟶ Γ_{x ∘ g, *} g^* L` is an isomorphism.
* The direct image `Γ_{x,*} L` of a finite locally free `𝒪_S`-module is flat over `S` through the
  second projection.

## Main results

* `Stacks.Drinfeld.Shtuka.isClosedImmersion_graph`: `Γ_x` is a closed immersion when `X` is
  separated over `k`.
* `Stacks.Drinfeld.Shtuka.isPullback_productMap`, `Stacks.Drinfeld.Shtuka.isPullback_graph`: the
  two base-change squares along `id × g` are cartesian.
* `Stacks.Drinfeld.Shtuka.graphBaseChangeIso`: `(id × g)^* Γ_{x,*} L ≅ Γ_{x ∘ g, *} g^* L`.
* `Stacks.Drinfeld.Shtuka.isFlatOver_pushforward_graph`: `Γ_{x,*} L` is flat over `S`.
* `Stacks.Drinfeld.Shtuka.IsGraphLineBundle.isQuasicoherent`,
  `Stacks.Drinfeld.Shtuka.IsGraphLineBundle.isFlatOver`,
  `Stacks.Drinfeld.Shtuka.IsGraphLineBundle.pullback_productMap`: a graph line bundle is
  quasi-coherent and flat over `S`, and its pullback along `id × g` is a graph line bundle for
  the leg `x ∘ g`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Drinfeld.Shtuka

variable {k : Type u} [Field k] [Fintype k] {X S S' : Over (Spec (.of k))}

/-- **The graph of a leg is a closed immersion when `X` is separated.** -/
theorem isClosedImmersion_graph [IsSeparated X.hom] (x : S ⟶ X) : IsClosedImmersion (graph x) := by
  have : IsClosedImmersion (graph x ≫ pullback.snd X.hom S.hom) := by
    rw [graph_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (graph x) (pullback.snd X.hom S.hom)

/-- **`id_X × g` is a base change of `g`.** The square formed by `id_X × g`, the two second
projections and `g` is cartesian. -/
theorem isPullback_productMap (g : S' ⟶ S) :
    IsPullback (productMap (X := X) g) (pullback.snd X.hom S'.hom) (pullback.snd X.hom S.hom)
      g.left := by
  refine IsPullback.of_right ?_ (productMap_snd g)
    (IsPullback.of_hasPullback X.hom S.hom)
  rw [productMap_fst, Over.w g]
  exact IsPullback.of_hasPullback X.hom S'.hom

/-- **The graph of `x ∘ g` is the base change of the graph of `x`.** The square
`Γ_{x ∘ g} ≫ (id × g) = g ≫ Γ_x` is cartesian. -/
theorem isPullback_graph (g : S' ⟶ S) (x : S ⟶ X) :
    IsPullback g.left (graph (g ≫ x)) (graph x) (productMap g) := by
  refine IsPullback.of_bot ?_ (graph_comp_productMap g x).symm (isPullback_productMap g)
  rw [graph_snd, graph_snd]
  exact IsPullback.id_vert g.left

/-- **Base change of the direct image along a graph.** For a quasi-coherent `𝒪_S`-module `L`,
the canonical base-change morphism `(id × g)^* Γ_{x,*} L ⟶ Γ_{x ∘ g, *} g^* L` is an
isomorphism. -/
theorem isIso_graphBaseChange [IsSeparated X.hom] (g : S' ⟶ S) (x : S ⟶ X) (L : S.left.Modules)
    [L.IsQuasicoherent] :
    IsIso ((AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (isPullback_graph g x).w).app L) := by
  have := isClosedImmersion_graph x
  exact AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_graph g x) L

/-- **Base change of the direct image along a graph**, as an isomorphism
`(id × g)^* Γ_{x,*} L ≅ Γ_{x ∘ g, *} g^* L`. -/
def graphBaseChangeIso [IsSeparated X.hom] (g : S' ⟶ S) (x : S ⟶ X) (L : S.left.Modules)
    [L.IsQuasicoherent] :
    (Scheme.Modules.pullback (productMap g)).obj ((Scheme.Modules.pushforward (graph x)).obj L) ≅
      (Scheme.Modules.pushforward (graph (g ≫ x))).obj ((Scheme.Modules.pullback g.left).obj L) :=
  have := isIso_graphBaseChange g x L
  asIso ((AlgebraicGeometry.AffinePushforward.baseChangeNatTrans (isPullback_graph g x).w).app L)

/-- **The direct image of a finite locally free module along a graph is flat over the base**
through the second projection. -/
theorem isFlatOver_pushforward_graph [IsSeparated X.hom] (x : S ⟶ X) (L : S.left.Modules)
    [L.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFree.{u, u, u} L] :
    IsFlatOver (pullback.snd X.hom S.hom).toLRSHom.toShHom
      ((Scheme.Modules.pushforward (graph x)).obj L) := by
  have := isClosedImmersion_graph x
  have h : IsFlatOver (Scheme.Hom.toLRSHom (𝟙 S.left)).toShHom L :=
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree (𝟙 _) L
  rw [← graph_snd x] at h
  exact (isFlatOver_pushforward_iff (graph x) (pullback.snd X.hom S.hom) L).1 h

namespace IsGraphLineBundle

/-- An invertible module is finite locally free and quasi-coherent. -/
private theorem isFiniteLocallyFree_and_isQuasicoherent_of_rank_one {Y : Scheme.{u}}
    (L : Y.Modules)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} L ∧ L.IsQuasicoherent := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact ⟨this, Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree L⟩

/-- A graph line bundle is quasi-coherent. -/
theorem isQuasicoherent [IsSeparated X.hom] {Q : (product X S).Modules} {x : S ⟶ X}
    (h : IsGraphLineBundle Q x) : Q.IsQuasicoherent := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  have := isClosedImmersion_graph x
  obtain ⟨_, _⟩ := isFiniteLocallyFree_and_isQuasicoherent_of_rank_one L hL
  exact (SheafOfModules.isQuasicoherent (product X S).ringCatSheaf).prop_of_iso e.symm
    inferInstance

/-- **A graph line bundle is flat over the base** through the second projection. -/
theorem isFlatOver [IsSeparated X.hom] {Q : (product X S).Modules} {x : S ⟶ X}
    (h : IsGraphLineBundle Q x) :
    IsFlatOver (pullback.snd X.hom S.hom).toLRSHom.toShHom Q := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  obtain ⟨_, _⟩ := isFiniteLocallyFree_and_isQuasicoherent_of_rank_one L hL
  exact (isFlatOver_iff_of_moduleIso _ e).2 (isFlatOver_pushforward_graph x L)

/-- **Graph line bundles are stable under base change.** If `Q` is the direct image of an
invertible `𝒪_S`-module along the graph of `x`, then `(id × g)^* Q` is the direct image of an
invertible `𝒪_{S'}`-module along the graph of `x ∘ g`. -/
theorem pullback_productMap [IsSeparated X.hom] {Q : (product X S).Modules} {x : S ⟶ X}
    (h : IsGraphLineBundle Q x) (g : S' ⟶ S) :
    IsGraphLineBundle ((Scheme.Modules.pullback (productMap g)).obj Q) (g ≫ x) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  obtain ⟨_, _⟩ := isFiniteLocallyFree_and_isQuasicoherent_of_rank_one L hL
  exact ⟨(Scheme.Modules.pullback g.left).obj L,
    SheafOfModules.IsFiniteLocallyFreeOfRank.pullback_scheme g.left L 1 hL,
    ⟨(Scheme.Modules.pullback (productMap g)).mapIso e ≪≫ graphBaseChangeIso g x L⟩⟩

end IsGraphLineBundle

end Stacks.Drinfeld.Shtuka
