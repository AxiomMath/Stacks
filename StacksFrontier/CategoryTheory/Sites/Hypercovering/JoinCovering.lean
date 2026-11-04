module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.JoinFaces
public import StacksFrontier.CategoryTheory.Sites.HypercoverDescent

/-!
# Two complementary faces of a hypercovering form a covering

Let `(C, J)` be a site with fibre products, let `X : C` and let `K` be a hypercovering of `X`,
that is, a simplicial object of `SR(C, X) = FormalCoproduct (Over X)` whose degree-zero term
covers `X` and whose canonical morphism to each successive coskeleton is covering. Write
`N = m + n + 1` and let `⦋m⦌ ⟶ ⦋N⦌` and `⦋n⦌ ⟶ ⦋N⦌` be the two complementary face inclusions.
This file proves that the induced morphism

`K_N ⟶ K_m ⨯ K_n`

is a covering morphism of `SR(C, X)`: a pair consisting of an `m`-simplex and an `n`-simplex of
`K` is, locally, the pair of complementary faces of a single `N`-simplex.

This is Tag 01GN applied to the inclusion `Δ[m] ⊔ Δ[n] ⊆ Δ[N]` of the two ends of the join
`Δ[m] ⋆ Δ[n] = Δ[N]`, using the identification `Hom(Δ[k], K)₀ = K_k` of Tag 017L on the right of
the inclusion and the identification `Hom(Δ[m] ⊔ Δ[n], K)₀ = K_m ⨯ K_n` on its left.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.representableByJoinEnds`: the product `K_m ⨯ K_n`
  represents the `Hom` presheaf of the union of the two complementary faces.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isCoveringOver_joinProdLift`: the morphism
  `K_N ⟶ K_m ⨯ K_n` of the two complementary faces is covering.

## Implementation notes

The proof is the one of `Stacks.CategoryTheory.Hypercovering.isCoveringOver_delta` (Tag 0DEQ
(2)), which is Tag 01GN applied to a single face inclusion: four representing data for the two
`Hom` presheaves involved, Tag 01GN for the chosen `Hom` objects, and
`representableByHom_comp_induced` to transport the covering morphism it produces along the
comparison isomorphisms. The only difference is the subcomplex, and hence the representing
object on the left: `SSet.stdSimplex.joinEnds` instead of a single face, and `K_m ⨯ K_n` instead
of `K_m`.

`SSet.stdSimplex.joinEndsHomEquiv` is what makes the left-hand representing datum: a morphism
out of the union of the two complementary faces is a pair of morphisms out of `Δ[m]` and
`Δ[n]`, because the union is their coproduct.

## References

* [Stacks Project, Tag 01GN](https://stacks.math.columbia.edu/tag/01GN)
* [Stacks Project, Tag 017L](https://stacks.math.columbia.edu/tag/017L)
* [Stacks Project, Tag 0DEQ](https://stacks.math.columbia.edu/tag/0DEQ)
-/

@[expose] public noncomputable section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SSet.stdSimplex

namespace Stacks.CategoryTheory.Hypercovering

section Representable

variable {D : Type u'} [Category.{v'} D]

/-- Morphisms into a binary product are pairs of morphisms. -/
def prodHomEquiv (Y A B : D) [HasBinaryProduct A B] :
    (Y ⟶ A ⨯ B) ≃ ((Y ⟶ A) × (Y ⟶ B)) where
  toFun f := (f ≫ prod.fst, f ≫ prod.snd)
  invFun p := prod.lift p.1 p.2
  left_inv f := by
    refine prod.hom_ext ?_ ?_ <;> simp
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> simp

/-- **`K_m ⨯ K_n` represents the `Hom` presheaf of the two complementary faces.** A morphism
from `Y` to `K_m ⨯ K_n` is a pair of morphisms, hence by Tag 017L a pair of morphisms out of
`Δ[m]` and `Δ[n]`, hence by `SSet.stdSimplex.joinEndsHomEquiv` a morphism out of the union of
the two complementary faces of `Δ[m + n + 1]`. -/
def representableByJoinEnds (K : SimplicialObject D) (m n : ℕ)
    [HasBinaryProduct (K.obj (op ⦋m⦌)) (K.obj (op ⦋n⦌))] :
    (homPresheaf K (joinEnds.{v'} m n : SSet.{v'})).RepresentableBy
      (K.obj (op ⦋m⦌) ⨯ K.obj (op ⦋n⦌)) where
  homEquiv {Y} :=
    (prodHomEquiv Y _ _).trans
      (((representableByStdSimplex K m).homEquiv.prodCongr
        (representableByStdSimplex K n).homEquiv).trans
          (joinEndsHomEquiv m n (K ⋙ coyoneda.obj (op Y))).symm)
  homEquiv_comp {Y Y'} f g := by
    change joinEndsDesc m n ((representableByStdSimplex K m).homEquiv ((f ≫ g) ≫ prod.fst))
        ((representableByStdSimplex K n).homEquiv ((f ≫ g) ≫ prod.snd)) =
      joinEndsDesc m n ((representableByStdSimplex K m).homEquiv (g ≫ prod.fst))
          ((representableByStdSimplex K n).homEquiv (g ≫ prod.snd)) ≫
        Functor.whiskerLeft K (coyoneda.map f.op)
    rw [joinEndsDesc_comp, Category.assoc, Category.assoc,
      (representableByStdSimplex K m).homEquiv_comp f (g ≫ prod.fst),
      (representableByStdSimplex K n).homEquiv_comp f (g ≫ prod.snd)]
    rfl

/-- The representing equivalence of `representableByJoinEnds`, unfolded. -/
theorem homEquiv_representableByJoinEnds (K : SimplicialObject D) (m n : ℕ)
    [HasBinaryProduct (K.obj (op ⦋m⦌)) (K.obj (op ⦋n⦌))] {Y : D}
    (f : Y ⟶ K.obj (op ⦋m⦌) ⨯ K.obj (op ⦋n⦌)) :
    (representableByJoinEnds K m n).homEquiv f =
      joinEndsDesc m n ((representableByStdSimplex K m).homEquiv (f ≫ prod.fst))
        ((representableByStdSimplex K n).homEquiv (f ≫ prod.snd)) :=
  rfl

/-- The representing equivalence of `representableByStdSimplex` is the Yoneda bijection. -/
theorem homEquiv_representableByStdSimplex (K : SimplicialObject D) (k : ℕ) {Y : D}
    (f : Y ⟶ K.obj (op ⦋k⦌)) :
    (representableByStdSimplex K k).homEquiv f =
      (SSet.yonedaEquiv (X := K ⋙ coyoneda.obj (op Y)) (n := ⦋k⦌)).symm f :=
  rfl

/-- Restricting the universal `N`-simplex of `K` along a face map `a` gives the Yoneda element of
any morphism `f` equal to `K.map a.op`. -/
private theorem map_comp_homEquiv_representableByStdSimplex (K : SimplicialObject D) {k N : ℕ}
    (a : ⦋k⦌ ⟶ ⦋N⦌) {f : K.obj (op ⦋N⦌) ⟶ K.obj (op ⦋k⦌)} (hf : f = K.map a.op) :
    SSet.stdSimplex.map a ≫ (representableByStdSimplex K N).homEquiv (𝟙 (K.obj (op ⦋N⦌))) =
      (representableByStdSimplex K k).homEquiv f := by
  rw [homEquiv_representableByStdSimplex, SSet.yonedaEquiv_symm_naturality_left,
    homEquiv_representableByStdSimplex]
  congr 1
  exact (Category.id_comp _).trans hf.symm

end Representable

/-! ### The covering morphism of two complementary faces -/

section Join

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C)
  [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
  (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (m n : ℕ)

/-- **Restriction of an `N`-simplex to a subcomplex of `Δ[N]` is a covering morphism.** For a
hypercovering `K` of `X`, a finite nonempty subcomplex `U ⊆ Δ[N]` and any object of `SR(C, X)`
representing the `Hom` presheaf of `U`, the morphism out of `K_N` which restricts the universal
`N`-simplex to `U` is covering: a `U`-shaped configuration of simplices of `K` is, locally, the
restriction of a single `N`-simplex.

This is Tag 01GN for the inclusion `U ⊆ Δ[N]`, transported along the comparison isomorphisms of
the representing objects exactly as in `isCoveringOver_delta`. -/
theorem isCoveringOver_subcomplexRestriction (hK : IsHypercovering J K) (N : ℕ)
    (U : (Δ[N] : SSet.{max w v}).Subcomplex) [SSet.Finite (U : SSet.{max w v})]
    [SSet.Nonempty (U : SSet.{max w v})] {M : FormalCoproduct.{w} (Over X)}
    (hA : (homPresheaf K (U : SSet.{max w v})).RepresentableBy M) :
    IsCoveringOver J (hA.homEquiv.symm
      (U.ι ≫ (representableByStdSimplex K N).homEquiv (𝟙 (K.obj (op ⦋N⦌))))) := by
  classical
  let hA' : (homPresheaf K (U : SSet.{max w v})).RepresentableBy
      ((homFromSSet (U : SSet.{max w v}) K).obj (op ⦋0⦌)) :=
    representableByAppZero _ K _ (homFromSSetIsHom (U : SSet.{max w v}) K)
  let hB : (homPresheaf K (Δ[N] : SSet.{max w v})).RepresentableBy (K.obj (op ⦋N⦌)) :=
    representableByStdSimplex K N
  let hB' : (homPresheaf K (Δ[N] : SSet.{max w v})).RepresentableBy
      ((homFromSSet (Δ[N] : SSet.{max w v}) K).obj (op ⦋0⦌)) :=
    representableByAppZero _ K _ (homFromSSetIsHom (Δ[N] : SSet.{max w v}) K)
  have hcov : IsCoveringOver J ((homFromSSetRestriction U.ι K).app (op ⦋0⦌)) :=
    isCoveringOver_homFromSSetRestriction_app_zero J X K hK (Δ[N] : SSet.{max w v}) U
  rw [homFromSSetRestriction_eq_homFromSSetMap, homFromSSetMap_app_zero] at hcov
  rw [← Category.comp_id (hA.homEquiv.symm _), ← IsIso.hom_inv_id (representableByHom hA hA'),
    ← Category.assoc, ← representableByHom_comp_induced U.ι hA hA' hB hB', Category.assoc]
  exact IsCoveringOver.comp J (IsCoveringOver.of_isIso J _) (hcov.comp_isIso J _)

/-- The morphism of `SR(C, X)` taking an `N`-simplex of `K`, `N = m + n + 1`, to the pair of its
two complementary faces. -/
abbrev joinProdLift [HasBinaryProduct (K.obj (op ⦋m⦌)) (K.obj (op ⦋n⦌))] :
    K.obj (op ⦋m + n + 1⦌) ⟶ K.obj (op ⦋m⦌) ⨯ K.obj (op ⦋n⦌) :=
  prod.lift (K.map (joinFst m n).op) (K.map (joinSnd m n).op)

omit [HasPullbacks C] in
/-- The universal element of the Yoneda representation of `K_{m + n + 1}`, restricted along the
inclusion of the two complementary faces, is the pair of the universal elements of `K_m` and
`K_n` twisted by the two face maps of `K`. -/
theorem homEquiv_joinProdLift [HasBinaryProduct (K.obj (op ⦋m⦌)) (K.obj (op ⦋n⦌))] :
    (representableByJoinEnds K m n).homEquiv (joinProdLift K m n) =
      (joinEnds.{max w v} m n).ι ≫
        (representableByStdSimplex K (m + n + 1)).homEquiv
          (𝟙 (K.obj (op ⦋m + n + 1⦌))) := by
  rw [homEquiv_representableByJoinEnds]
  refine (joinEnds_hom_ext m n ?_ ?_).symm
  · rw [joinFstInclusion_comp_ι_assoc, joinFstInclusion_comp_joinEndsDesc]
    exact map_comp_homEquiv_representableByStdSimplex K _ (prod.lift_fst _ _)
  · rw [joinSndInclusion_comp_ι_assoc, joinSndInclusion_comp_joinEndsDesc]
    exact map_comp_homEquiv_representableByStdSimplex K _ (prod.lift_snd _ _)

/-- **The two complementary faces of a hypercovering form a covering morphism.** For a
hypercovering `K` of `X` and `m n : ℕ`, the morphism `K_{m + n + 1} ⟶ K_m ⨯ K_n` given by the two
complementary face inclusions `⦋m⦌ ⟶ ⦋m + n + 1⦌ ⟵ ⦋n⦌` is covering in `SR(C, X)`.

This is Tag 01GN for the inclusion of the union of the two complementary faces of
`Δ[m + n + 1]`, transported along the comparison isomorphisms of the representing objects
exactly as in `isCoveringOver_delta`. -/
theorem isCoveringOver_joinProdLift (hK : IsHypercovering J K)
    [HasBinaryProduct (K.obj (op ⦋m⦌)) (K.obj (op ⦋n⦌))] :
    IsCoveringOver J (joinProdLift K m n) := by
  have hface : (representableByJoinEnds K m n).homEquiv.symm ((joinEnds m n).ι ≫
      (representableByStdSimplex K (m + n + 1)).homEquiv (𝟙 (K.obj (op ⦋m + n + 1⦌)))) =
      joinProdLift K m n :=
    (representableByJoinEnds K m n).homEquiv.injective (by
      rw [Equiv.apply_symm_apply]
      exact (homEquiv_joinProdLift K m n).symm)
  rw [← hface]
  exact isCoveringOver_subcomplexRestriction J K hK (m + n + 1) (joinEnds m n)
    (representableByJoinEnds K m n)

end Join

end Stacks.CategoryTheory.Hypercovering

end
