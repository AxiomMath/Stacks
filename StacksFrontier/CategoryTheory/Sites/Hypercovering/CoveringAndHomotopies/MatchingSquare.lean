module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.HomObjects

/-!
# The matching square of a Hom object out of the interval

Let `C` be a site with fibre products, let `X : C` and let `L` be a simplicial semi-representable
object over `X`. Write `H` for a `Hom(Δ[1], L)`. This file identifies the square

```
Hom(Δ[1] ⊗ Δ[n + 1], L)₀ ⟶ Hom(Δ[1] ⊗ ∂Δ[n + 1], L)₀
         ↓                              ↓
Hom(∂Δ[1] ⊗ Δ[n + 1], L)₀ ⟶ Hom(∂Δ[1] ⊗ ∂Δ[n + 1], L)₀
```

of restriction morphisms with the square

```
H_{n + 1} ⟶ (cosk_n H)_{n + 1}
    ↓                ↓
(L × L)_{n + 1} ⟶ (cosk_n (L × L))_{n + 1}
```

whose left vertical arrow is the endpoint evaluation `H ⟶ L × L` and whose horizontal arrows are
the canonical morphisms to the matching objects, and exhibits the `Hom` object of the
pushout-product `∂Δ[1] ⊡ ∂Δ[n + 1]` of the two boundary inclusions as the fibre product of the
other three corners. This is the computation out of which Tag 01GS builds a homotopy.

## Main definitions

* `intervalEndpointMap`: the endpoint-evaluation morphism `Hom(Δ[1], L) ⟶ L × L`, fixed by its
  two ordered components, before any simplicial degree is chosen.

## Main results

* `boundaryIntervalRepresentable`: `L × L` is a `Hom(∂Δ[1], L)`.
* `homotopyMatchingSquare`: the four corners of the square are identified by their representing
  properties, every arrow is induced by an inclusion of simplicial sets, and the `Hom` object of
  the union `∂Δ[1] ⊡ ∂Δ[n + 1]` is the fibre product of the other three.

## Implementation notes

The two copies of a simplex are written as `∂Δ[1] ⊗ Δ[n + 1]`, and the union in the
pushout-product is `SSet.Subcomplex.unionProd`; its defining pushout square
(`SSet.Subcomplex.unionProd.isPushout`) is turned into a fibre product of `Hom` objects by
`SimplicialObject.isPullback_hom_of_isPushout` (Tag 017N).

`intervalEndpointMap` is specified by its ordered vertex components in every simplicial degree,
and it is fixed before the degree is chosen, which is what lets `homotopyMatchingSquare` and
Tag 01GS speak about the same morphism.

Representability is recorded by canonical and natural identifications
(`Functor.RepresentableBy`) rather than by noncanonical equalities of chosen representing
objects; the `Hom` objects of Tag 017L are only determined up to isomorphism. The fifth
representing object `Q` is the source's `Hom(U, L)₀` for the union `U`.

The index universe `w` of the formal coproducts is independent of the object and morphism
universes of `C`, and the hom-universe of `SR(C, X)` is `max v w`, so the simplicial sets
occurring here are `SSet.{max v w}`.

## References

* [Stacks Project, Tag 01GP](https://stacks.math.columbia.edu/tag/01GP)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite Simplicial
open scoped MonoidalCategory

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (X : C)

/-- Restriction to the two vertices of the interval is represented by the product of two copies
of a simplicial semi-representable object. -/
@[stacks 01GP "the two endpoint copies"]
theorem boundaryIntervalRepresentable
    (L : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Nonempty (SimplicialObject.IsHomFromSSet (SSet.boundary.{max v w} 1) L (L ⨯ L)) :=
  ⟨boundaryIntervalHomFromSSet L⟩

/-- The fixed endpoint-evaluation morphism `Hom(Δ[1], L) ⟶ L × L`. Its two components are, in
order, the restrictions of the universal interval map to the vertices zero and one. -/
@[stacks 01GP "the ordered endpoint map"]
noncomputable def intervalEndpointMap
    (L H : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hH : SimplicialObject.IsHomFromSSet Δ[1] L H) :
    { e : H ⟶ L ⨯ L //
      (∀ m : SimplexCategoryᵒᵖ,
        (e ≫ prod.fst).app m =
          (Functor.functorHomEquiv H L Δ[1] (hH.homEquiv (𝟙 H))).app m
            (SSet.stdSimplex.const 1 0 m)) ∧
      (∀ m : SimplexCategoryᵒᵖ,
        (e ≫ prod.snd).app m =
          (Functor.functorHomEquiv H L Δ[1] (hH.homEquiv (𝟙 H))).app m
            (SSet.stdSimplex.const 1 1 m)) } := by
  let components := Functor.functorHomEquiv H L Δ[1] (hH.homEquiv (𝟙 H))
  let f : Fin 2 → (H ⟶ L) := fun i ↦
    { app m := components.app m (SSet.stdSimplex.const 1 i m)
      naturality := by
        intro m m' g
        simpa only [stdSimplex_map_const] using
          components.naturality g (SSet.stdSimplex.const 1 i m) }
  exact ⟨prod.lift (f 0) (f 1), NatTrans.congr_app (prod.lift_fst _ _),
    NatTrans.congr_app (prod.lift_snd _ _)⟩

/-- **Stacks Project, Tag 01GP.** The four matching objects are represented by the corresponding
simplicial sets, and the `Hom` object of the union is their fibre product. All arrows in the
fibre product square are those induced by inclusions of simplicial sets. -/
@[stacks 01GP]
theorem homotopyMatchingSquare
    (L : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (H : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hH : SimplicialObject.IsHomFromSSet Δ[1] L H) :
    ∀ n : ℕ, ∃ Q : FormalCoproduct.{w} (Over X),
      let e := (intervalEndpointMap X L H hH).1;
      let m := n + 1;
      let S := SSet.boundary.{max v w} 1;
      let T := SSet.boundary.{max v w} m;
      let U := S.unionProd T;
      let F := coyoneda ⋙
        (Functor.whiskeringLeft SimplexCategoryᵒᵖ
          (FormalCoproduct.{w} (Over X)) (Type (max v w))).obj L;
      ∃ (hFull : (F ⋙ coyoneda.obj (op (Δ[1] ⊗ Δ[m]))).RepresentableBy (H _⦋m⦌))
        (hTop : (F ⋙ coyoneda.obj (op (Δ[1] ⊗ (T : SSet)))).RepresentableBy
          (((SimplicialObject.cosk n).obj H) _⦋m⦌))
        (hBottom : (F ⋙ coyoneda.obj (op ((S : SSet) ⊗ Δ[m]))).RepresentableBy
          ((L ⨯ L) _⦋m⦌))
        (hRight : (F ⋙ coyoneda.obj (op ((S : SSet) ⊗ (T : SSet)))).RepresentableBy
          (((SimplicialObject.cosk n).obj (L ⨯ L)) _⦋m⦌))
        (hUnion : (F ⋙ coyoneda.obj (op (U : SSet))).RepresentableBy Q),
        let comparison := hUnion.homEquiv.symm (U.ι ≫ hFull.homEquiv (𝟙 _));
        (e.app (op ⦋m⦌) =
          hBottom.homEquiv.symm ((S.ι ▷ Δ[m]) ≫ hFull.homEquiv (𝟙 _))) ∧
        ((((SimplicialObject.coskAdj n).unit.app H).app (op ⦋m⦌)) =
          hTop.homEquiv.symm ((Δ[1] ◁ T.ι) ≫ hFull.homEquiv (𝟙 _))) ∧
        ((((SimplicialObject.coskAdj n).unit.app (L ⨯ L)).app (op ⦋m⦌)) =
          hRight.homEquiv.symm (((S : SSet) ◁ T.ι) ≫ hBottom.homEquiv (𝟙 _))) ∧
        ((((SimplicialObject.cosk n).map e).app (op ⦋m⦌)) =
          hRight.homEquiv.symm ((S.ι ▷ (T : SSet)) ≫ hTop.homEquiv (𝟙 _))) ∧
        (comparison ≫ hTop.homEquiv.symm
          (SSet.Subcomplex.unionProd.ι₁ S T ≫ hUnion.homEquiv (𝟙 Q)) =
          ((SimplicialObject.coskAdj n).unit.app H).app (op ⦋m⦌)) ∧
        (comparison ≫ hBottom.homEquiv.symm
          (SSet.Subcomplex.unionProd.ι₂ S T ≫ hUnion.homEquiv (𝟙 Q)) =
          e.app (op ⦋m⦌)) ∧
        IsPullback
          (hTop.homEquiv.symm (SSet.Subcomplex.unionProd.ι₁ S T ≫
            hUnion.homEquiv (𝟙 Q)))
          (hBottom.homEquiv.symm (SSet.Subcomplex.unionProd.ι₂ S T ≫
            hUnion.homEquiv (𝟙 Q)))
          (hRight.homEquiv.symm ((S.ι ▷ (T : SSet)) ≫ hTop.homEquiv (𝟙 _)))
          (hRight.homEquiv.symm (((S : SSet) ◁ T.ι) ≫ hBottom.homEquiv (𝟙 _))) := by
  classical
  intro n
  let m := n + 1
  let S : (Δ[1] : SSet.{max v w}).Subcomplex := SSet.boundary.{max v w} 1
  let T : (Δ[m] : SSet.{max v w}).Subcomplex := SSet.boundary.{max v w} m
  let U : SSet.{max v w} := SSet.Subcomplex.unionProd S T
  let hBoundary : SimplicialObject.IsHomFromSSet S L (L ⨯ L) :=
    boundaryIntervalHomFromSSet L
  let hFull := representableBy_homFromSSetPoints hH (representableByStdSimplex H m)
  let hTop := representableBy_homFromSSetPoints hH (representableByBoundarySucc H n)
  let hBottom := representableBy_homFromSSetPoints hBoundary
    (representableByStdSimplex (L ⨯ L) m)
  let hRight := representableBy_homFromSSetPoints hBoundary
    (representableByBoundarySucc (L ⨯ L) n)
  obtain ⟨Qobj, hQ, _⟩ := CategoryTheory.SimplicialObject.exists_representableBy_sHom U L
  let Q := Qobj _⦋0⦌
  let hUnion := representableByAppZero U L Qobj (Classical.choice hQ)
  have hPullback := CategoryTheory.SimplicialObject.isPullback_hom_of_isPushout L
    (SSet.Subcomplex.unionProd.isPushout S T) hRight hTop hBottom hUnion
  let endpoint := intervalEndpointMap X L H hH
  have hendpoint := intervalEndpointMap_boundary_restriction L H hH
    endpoint.1 endpoint.2.1 endpoint.2.2
  have h₁ : endpoint.1.app (op ⦋m⦌) =
      hBottom.homEquiv.symm ((S.ι ▷ Δ[m]) ≫ hFull.homEquiv (𝟙 _)) := by
    rw [Equiv.eq_symm_apply]
    change homFromSSetPointsEquiv S Δ[m] L (L ⨯ L) hBoundary _
      ((representableByStdSimplex (L ⨯ L) m).homEquiv _) = _
    rw [← Category.id_comp (endpoint.1.app _), representableByStdSimplex_postcomp]
    exact homFromSSetPointsEquiv_restriction hH hBoundary S.ι endpoint.1 hendpoint _ _
  have unit_eq : ∀ (A : SSet.{max v w}) (G : SimplicialObject (FormalCoproduct.{w} (Over X)))
      (hG : SimplicialObject.IsHomFromSSet A L G),
      ((SimplicialObject.coskAdj n).unit.app G).app (op ⦋m⦌) =
        (representableBy_homFromSSetPoints hG (representableByBoundarySucc G n)).homEquiv.symm
          ((A ◁ T.ι) ≫ (representableBy_homFromSSetPoints hG
            (representableByStdSimplex G m)).homEquiv (𝟙 _)) := by
    intro A G hG
    rw [Equiv.eq_symm_apply]
    change homFromSSetPointsEquiv A T L G hG _
      ((representableByBoundarySucc G n).homEquiv _) = _
    rw [← boundarySucc_induced_eq_coskAdj_unit G n, Equiv.apply_symm_apply]
    exact homFromSSetPointsEquiv_precomp hG _ T.ι _
  have h₂ := unit_eq Δ[1] H hH
  have h₃ := unit_eq S (L ⨯ L) hBoundary
  have h₄ : ((SimplicialObject.cosk n).map endpoint.1).app (op ⦋m⦌) =
      hRight.homEquiv.symm ((S.ι ▷ (T : SSet)) ≫ hTop.homEquiv (𝟙 _)) := by
    rw [Equiv.eq_symm_apply]
    change homFromSSetPointsEquiv S T L (L ⨯ L) hBoundary _
      ((representableByBoundarySucc (L ⨯ L) n).homEquiv _) = _
    have he := representableByBoundarySucc_postcomp n endpoint.1 _ (𝟙 _)
    rw [Category.id_comp] at he
    rw [he]
    exact homFromSSetPointsEquiv_restriction hH hBoundary S.ι endpoint.1 hendpoint _ _
  refine ⟨Q, hFull, hTop, hBottom, hRight, hUnion, h₁, h₂, h₃, h₄, ?_, ?_, hPullback⟩
  · refine (representedRestriction_comp (pointwisePresheaf L) hFull hUnion hTop
      (S.unionProd T).ι (SSet.Subcomplex.unionProd.ι₁ S T)).trans ?_
    simpa only [SSet.Subcomplex.unionProd.ι₁_ι] using h₂.symm
  · refine (representedRestriction_comp (pointwisePresheaf L) hFull hUnion hBottom
      (S.unionProd T).ι (SSet.Subcomplex.unionProd.ι₂ S T)).trans ?_
    simpa only [SSet.Subcomplex.unionProd.ι₂_ι] using h₁.symm

end Stacks.CategoryTheory.Hypercovering

end
