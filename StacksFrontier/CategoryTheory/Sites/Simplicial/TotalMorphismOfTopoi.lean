module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# The morphism of total topoi of a morphism between simplicial sites

Let `h` be a morphism between simplicial sites, in either of the two cases of Stacks 0D95: a
family of morphisms of sites `h_n : C_n → C'_n` commuting with the transition morphisms (case
(A)), or a family of cocontinuous functors `v_n : C_n ⥤ C'_n` commuting with the transition
functors (case (B)). Write `g_n : Sh(C_n) → Sh(C_total)` and `g'_n : Sh(C'_n) → Sh(C'_total)`
for the morphisms of topoi of the component inclusions. This file assembles the morphism of
topoi `h_total : Sh(C_total) → Sh(C'_total)`, the commutative squares
`h_total ∘ g_n = g'_n ∘ h_n`, and the identity `(g'_n)^{-1} ∘ h_{total,*} = h_{n,*} ∘ g_n^{-1}`.

In case (A) the morphism of total topoi is the one of the morphism of sites given by the functor
`v_total : C'_total ⥤ C_total` obtained by applying the functors representing the `h_n`
degreewise; in case (B) it is the one of the cocontinuous functor `v_total : C_total ⥤ C'_total`
obtained from the `v_n`. The equalities of the source are stated as natural isomorphisms: the
commutative square both on direct images and on inverse images, and the last identity on the
functors it names.

## Main definitions

* `CategoryTheory.SimplicialSiteMorphism.totalMorphism`: the morphism of total topoi.
* `CategoryTheory.SimplicialSiteMorphism.TotalMorphismSquares`: the comparisons asserted by
  Stacks 0D96 for the morphism of total topoi.
* `CategoryTheory.SimplicialSiteMorphism.totalMorphismSquares`: those comparisons.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

namespace SimplicialSiteMorphism

variable {S S' : SimplicialSiteSituation.{u}}

/-- The morphism of topoi `h_total : Sh(C_total) → Sh(C'_total)` induced by a morphism between
simplicial sites: in case (A) the morphism of topoi of the morphism of sites given by applying
the functors representing the `h_n` degreewise, in case (B) the morphism of topoi of the
cocontinuous functor obtained by applying the `v_n` degreewise. -/
def totalMorphism : SimplicialSiteMorphism S S' →
    MorphismOfTopoi (Sheaf S.totalTopology (Type u)) (Sheaf S'.totalTopology (Type u))
  | .ofMorphismOfSites h => h.totalMorphism
  | .ofCocontinuous h => h.totalMorphism

/-- The comparisons of Stacks 0D96 for the morphism of total topoi `h_total` of a morphism `h`
between simplicial sites, with `h_n` its morphism of topoi in degree `n` and `g_n`, `g'_n` the
morphisms of topoi of the component inclusions of degree `n`: the square
`h_total ∘ g_n = g'_n ∘ h_n` commutes, on direct images and on inverse images, and
`(g'_n)^{-1} ∘ h_{total,*} = h_{n,*} ∘ g_n^{-1}`. -/
structure TotalMorphismSquares (h : SimplicialSiteMorphism S S') where
  /-- The square commutes on direct images: `g'_{n,*} ∘ h_{n,*} ≅ h_{total,*} ∘ g_{n,*}`. -/
  pushforwardIso (n : SimplexCategory) :
    (h.componentMorphism n).pushforward ⋙ (S'.componentMorphism n).pushforward ≅
      (S.componentMorphism n).pushforward ⋙ h.totalMorphism.pushforward
  /-- The square commutes on inverse images: `g_n^{-1} ∘ h_total^{-1} ≅ h_n^{-1} ∘ (g'_n)^{-1}`.
  -/
  inverseImageIso (n : SimplexCategory) :
    h.totalMorphism.inverseImage ⋙ (S.componentMorphism n).inverseImage ≅
      (S'.componentMorphism n).inverseImage ⋙ (h.componentMorphism n).inverseImage
  /-- `(g'_n)^{-1} ∘ h_{total,*} ≅ h_{n,*} ∘ g_n^{-1}`. -/
  pushforwardRestrictIso (n : SimplexCategory) :
    h.totalMorphism.pushforward ⋙ (S'.componentMorphism n).inverseImage ≅
      (S.componentMorphism n).inverseImage ⋙ (h.componentMorphism n).pushforward

/-- **Stacks 0D96.** A morphism `h` between simplicial sites, in either case of Stacks 0D95,
induces a morphism of topoi `h_total : Sh(C_total) → Sh(C'_total)` (`h.totalMorphism`) such that
for every `n` the square formed by `h_total`, the morphism of topoi `h_n` of degree `n` and the
morphisms of topoi `g_n`, `g'_n` of the component inclusions commutes, and
`(g'_n)^{-1} ∘ h_{total,*} = h_{n,*} ∘ g_n^{-1}`. -/
@[stacks 0D96 "the morphism of total topoi, its commutative squares with the component \
  morphisms, and the restriction of its direct image, in both cases"]
def totalMorphismSquares : (h : SimplicialSiteMorphism S S') → h.TotalMorphismSquares
  | .ofMorphismOfSites h =>
      { pushforwardIso := h.totalComponentPushforwardIso
        inverseImageIso := h.totalComponentInverseImageIso
        pushforwardRestrictIso := h.totalPushforwardRestrictIso }
  | @ofCocontinuous C C' h =>
      { pushforwardIso := h.totalComponentPushforwardIso
        inverseImageIso := fun n =>
          (h.totalMorphism.adj.comp (SimplicialSiteSituation.componentMorphism
              (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).adj).leftAdjointUniq
            (((SimplicialSiteSituation.componentMorphism
                (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).adj.comp
              ((ofCocontinuous h).componentMorphism n).adj).ofNatIsoRight
              (h.totalComponentPushforwardIso n))
        pushforwardRestrictIso := h.totalPushforwardRestrictIso }

end SimplicialSiteMorphism

end CategoryTheory

end
