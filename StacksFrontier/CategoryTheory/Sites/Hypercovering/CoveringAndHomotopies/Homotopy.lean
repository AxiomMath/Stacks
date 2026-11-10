module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.CategoryTheory.Sites.HypercoverDescent
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.FibreProduct
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.MatchingSquare

/-!
# Homotopy after refining a hypercovering

Let `C` be a site given by a pretopology `J`, let `C` have fibre products and let `X : C`. Given
two morphisms `a, b : K ⟶ L` between hypercoverings of `X`, there is a hypercovering `K'` of `X`
and a morphism `c : K' ⟶ K` such that `c ≫ a` and `c ≫ b` are joined by a simplicial homotopy.

The proof is the one of the source. Let `H` be a `Hom(Δ[1], L)` and let `e : H ⟶ L × L` be the
endpoint-evaluation morphism. Then `K' = K ×_{L × L} H` works, with `c` the first projection and
the homotopy read off from the second: it is a hypercovering by Tag 01GH, because `e` is covering
in degree zero (Tag 01GN applied to `∂Δ[1] ⊆ Δ[1]`) and covering on every relative matching
object (Tag 01GN applied to the pushout-product `∂Δ[1] ⊡ ∂Δ[n + 1] ⊆ Δ[1] ⊗ Δ[n + 1]`, through
the identification of the matching square of Tag 01GP).

## Main results

* `homFromSSetRestriction_app_zero`: the degree-zero part of a restriction of chosen `Hom`
  objects is the morphism the degree-zero representing data induce.
* `exists_homotopy_after_hypercovering_refinement` is Tag 01GS.

## Implementation notes

The homotopy is exhibited explicitly as a morphism out of the copower by the standard
`1`-simplex, using `CategoryTheory.SimplicialObject.IsHomotopy`.

The statement of Tag 01GS leaves the universe of `Δ[1]` free, while the construction produces a
homotopy out of the copower by `Δ[1] : SSet.{max v w}`, that being the hom-universe of
`SR(C, X)`. `intervalUniverseLift` transports a homotopy from the latter to any universe: the
simplices of `Δ[1]` in degree `m` are a `ULift` of the finite set of order-preserving maps, so
the comparison is a bijection in every degree, compatible with the simplicial structure and
with the two vertices.

The stability of the pretopology under composition carries the indexed-family composition axiom
of the source's site (Tag 00VH (2)).

## References

* [Stacks Project, Tag 01GS](https://stacks.math.columbia.edu/tag/01GS)
-/

@[expose] public section

universe z z' w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite Simplicial
open scoped MonoidalCategory

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Universe transport for the interval -/

section UniverseLift

/-- An `m`-simplex of the standard `1`-simplex, read in another universe. -/
def intervalUniverseLift {m : SimplexCategoryᵒᵖ} (x : (SSet.stdSimplex.{z}.obj ⦋1⦌).obj m) :
    (SSet.stdSimplex.{z'}.obj ⦋1⦌).obj m :=
  ULift.up x.down

/-- Universe transport for the interval is compatible with the simplicial structure. -/
lemma intervalUniverseLift_map {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m')
    (x : (SSet.stdSimplex.{z}.obj ⦋1⦌).obj m) :
    intervalUniverseLift.{z, z'} ((SSet.stdSimplex.{z}.obj ⦋1⦌).map f x) =
      (SSet.stdSimplex.{z'}.obj ⦋1⦌).map f (intervalUniverseLift.{z, z'} x) := by
  apply SSet.stdSimplex.ext.{z'}
  intro j
  rfl

/-- Universe transport for the interval fixes the two constant simplices. -/
lemma intervalUniverseLift_const (m : SimplexCategoryᵒᵖ) (i : Fin 2) :
    intervalUniverseLift.{z, z'}
        (SSet.stdSimplex.const 1 i m : (SSet.stdSimplex.{z}.obj ⦋1⦌).obj m) =
      (SSet.stdSimplex.const 1 i m : (SSet.stdSimplex.{z'}.obj ⦋1⦌).obj m) := by
  apply SSet.stdSimplex.ext.{z'}
  intro j
  rfl

end UniverseLift

/-! ### The degree-zero part of a restriction of Hom objects -/

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The degree-zero part of the restriction morphism between the chosen `Hom` objects is the
morphism that the degree-zero representing data induce. -/
lemma homFromSSetRestriction_app_zero {X : C} {A B : SSet.{max w v}} [A.Finite] [B.Finite]
    (i : A ⟶ B) (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    (homFromSSetRestriction i K).app (op ⦋0⦌) =
      (representableByAppZero A K (homFromSSet A K) (homFromSSetIsHom A K)).homEquiv.symm
        (i ≫ (representableByAppZero B K (homFromSSet B K)
          (homFromSSetIsHom B K)).homEquiv (𝟙 ((homFromSSet B K).obj (op ⦋0⦌)))) := by
  rw [homFromSSetRestriction_eq_homFromSSetMap, homFromSSetMap_app_zero]

/-! ### Tag 01GS -/

/-- The isomorphism between two objects representing the same presheaf carries the universal
element of the source to that of the target.

`representableByIso` itself is already in `StacksFrontier.CategoryTheory.Sites.HypercoverDescent`,
in this namespace; this file reuses it rather than restating it. -/
lemma representableByIso_hom_homEquiv {D : Type u} [Category.{v} D] {F : Dᵒᵖ ⥤ Type v}
    {R R' : D} (h : F.RepresentableBy R) (h' : F.RepresentableBy R') :
    h'.homEquiv (representableByIso h h').hom = h.homEquiv (𝟙 R) :=
  homEquiv_representableByHom h h'

/-- The endpoint-evaluation morphism `Hom(Δ[1], L) ⟶ L × L` is covering in degree zero. -/
private theorem isCoveringOver_intervalEndpointMap_app_zero (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {L : SimplicialObject (FormalCoproduct.{w} (Over X))} (hL : IsHypercovering J L) :
    let H := homFromSSet (X := X) (Δ[1] : SSet.{max v w}) L
    let hH := homFromSSetIsHom (X := X) (Δ[1] : SSet.{max v w}) L
    let e := (intervalEndpointMap X L H hH).1
    IsCoveringOver J (e.app (op ⦋0⦌)) := by
  intro H hH e
  let S : (Δ[1] : SSet.{max v w}).Subcomplex := SSet.boundary 1
  let hB : SimplicialObject.IsHomFromSSet (S : SSet) L (L ⨯ L) :=
    boundaryIntervalHomFromSSet L
  let hChosen := homFromSSetIsHom (S : SSet) L
  let r := homFromSSetRestriction S.ι L
  let iso : homFromSSet (S : SSet) L ≅ L ⨯ L := representableByIso hChosen hB
  have hIso (g : H ⟶ homFromSSet (S : SSet) L) :
      hB.homEquiv (g ≫ iso.hom) = hChosen.homEquiv g := by
    rw [hB.homEquiv_comp, representableByIso_hom_homEquiv]
    exact (hChosen.homEquiv_eq g).symm
  have hr : hChosen.homEquiv r = S.ι ≫ hH.homEquiv (𝟙 H) := by
    dsimp only [r, homFromSSetRestriction]
    exact Equiv.apply_symm_apply _ _
  have he : r ≫ iso.hom = e := by
    apply hB.homEquiv.injective
    rw [hIso, hr, intervalEndpointMap_boundary_restriction L H hH e
      (intervalEndpointMap X L H hH).2.1 (intervalEndpointMap X L H hH).2.2]
  have : SSet.Nonempty (S : SSet) := ⟨boundaryOneVertex (m := op ⦋0⦌) 0⟩
  have hc := isCoveringOver_homFromSSetRestriction_app_zero J X L hL
    (Δ[1] : SSet.{max v w}) S
  rw [← he]
  exact hc.comp_isIso J (iso.hom.app (op ⦋0⦌))

/-- For a nonempty subcomplex `U` of a nonempty finite simplicial set `V`, the comparison
between any two objects representing `Hom(V, L)₀` and `Hom(U, L)₀` is covering. -/
private theorem isCoveringOver_representableBy_comparison (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {L : SimplicialObject (FormalCoproduct.{w} (Over X))} (hL : IsHypercovering J L)
    (V : SSet.{max v w}) [V.Finite] [V.Nonempty] (U : V.Subcomplex) [SSet.Finite (U : SSet)]
    [SSet.Nonempty (U : SSet)] {P Q : FormalCoproduct.{w} (Over X)}
    (hFull : ((coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (FormalCoproduct.{w} (Over X)) (Type (max v w))).obj L) ⋙
        coyoneda.obj (op V)).RepresentableBy P)
    (hUnion : ((coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (FormalCoproduct.{w} (Over X)) (Type (max v w))).obj L) ⋙
        coyoneda.obj (op (U : SSet))).RepresentableBy Q) :
    IsCoveringOver J (hUnion.homEquiv.symm (U.ι ≫ hFull.homEquiv (𝟙 P))) := by
  let r := homFromSSetRestriction U.ι L
  let repV := representableByAppZero V L (homFromSSet V L) (homFromSSetIsHom V L)
  let repU := representableByAppZero (U : SSet) L (homFromSSet (U : SSet) L)
    (homFromSSetIsHom (U : SSet) L)
  have hChosenCover : IsCoveringOver J (r.app (op ⦋0⦌)) :=
    isCoveringOver_homFromSSetRestriction_app_zero J X L hL V U
  let isoV := representableByIso repV hFull
  let isoU := representableByIso repU hUnion
  let comparison := hUnion.homEquiv.symm (U.ι ≫ hFull.homEquiv (𝟙 P))
  have hRestrictionRep : repU.homEquiv (r.app (op ⦋0⦌)) =
      U.ι ≫ repV.homEquiv (𝟙 ((homFromSSet V L).obj (op ⦋0⦌))) := by
    rw [homFromSSetRestriction_app_zero]
    simp [repU, repV]
  have hComparison : r.app (op ⦋0⦌) ≫ isoU.hom = isoV.hom ≫ comparison := by
    apply hUnion.homEquiv.injective
    rw [hUnion.homEquiv_comp, hUnion.homEquiv_comp, show hUnion.homEquiv isoU.hom =
      repU.homEquiv (𝟙 ((homFromSSet (U : SSet) L).obj (op ⦋0⦌))) from
        representableByIso_hom_homEquiv repU hUnion,
      show hUnion.homEquiv comparison = U.ι ≫ hFull.homEquiv (𝟙 P) by simp [comparison]]
    have hCompU := repU.homEquiv_comp (r.app (op ⦋0⦌))
      (𝟙 ((homFromSSet (U : SSet) L).obj (op ⦋0⦌)))
    let F := coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (FormalCoproduct.{w} (Over X)) (Type (max v w))).obj L
    let FU' := F ⋙ coyoneda.obj (op (U : SSet))
    have hNatural : FU'.map isoV.hom.op (U.ι ≫ hFull.homEquiv (𝟙 P)) =
        U.ι ≫ hFull.homEquiv isoV.hom := by
      have hFullNat := hFull.homEquiv_comp isoV.hom (𝟙 P)
      rw [Category.comp_id] at hFullNat
      change hFull.homEquiv isoV.hom =
        hFull.homEquiv (𝟙 P) ≫ Functor.whiskerLeft L (coyoneda.map isoV.hom.op) at hFullNat
      have h := congrArg (fun z ↦ U.ι ≫ z) hFullNat.symm
      simpa [Category.assoc, FU', F] using h
    calc
      _ = repU.homEquiv (r.app (op ⦋0⦌)) := by simpa using hCompU.symm
      _ = U.ι ≫ repV.homEquiv (𝟙 ((homFromSSet V L).obj (op ⦋0⦌))) := hRestrictionRep
      _ = U.ι ≫ hFull.homEquiv isoV.hom := by
            rw [representableByIso_hom_homEquiv repV hFull]
      _ = FU'.map isoV.hom.op (U.ι ≫ hFull.homEquiv (𝟙 P)) := hNatural.symm
  change IsCoveringOver J comparison
  refine IsCoveringOver.of_isIso_comp J isoV.hom ?_
  rw [← hComparison]
  exact hChosenCover.comp_isIso J isoU.hom

/-- The endpoint-evaluation morphism `Hom(Δ[1], L) ⟶ L × L` is covering on every relative
matching object. -/
private theorem isCoveringOver_intervalEndpointMap_matching (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {L : SimplicialObject (FormalCoproduct.{w} (Over X))} (hL : IsHypercovering J L) (n : ℕ) :
    let H := homFromSSet (X := X) (Δ[1] : SSet.{max v w}) L
    let hH := homFromSSetIsHom (X := X) (Δ[1] : SSet.{max v w}) L
    let e := (intervalEndpointMap X L H hH).1
    IsCoveringOver J
      (Limits.pullback.lift
        (f := (((SimplicialObject.coskAdj n).unit.app (L ⨯ L)).app (op ⦋n + 1⦌)))
        (g := (((SimplicialObject.Truncated.cosk n).map
          ((SimplicialObject.truncation n).map e)).app (op ⦋n + 1⦌)))
        (e.app (op ⦋n + 1⦌))
        (((SimplicialObject.coskAdj n).unit.app H).app (op ⦋n + 1⦌))
        (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality e)
          (op ⦋n + 1⦌))) := by
  intro H hH e
  let m := n + 1
  let i := op (⦋m⦌ : SimplexCategory)
  let S : (Δ[1] : SSet.{max v w}).Subcomplex := SSet.boundary 1
  let T : (Δ[m] : SSet.{max v w}).Subcomplex := SSet.boundary m
  let U := SSet.Subcomplex.unionProd S T
  let V : SSet.{max v w} := (Δ[1] : SSet.{max v w}) ⊗ Δ[m]
  have : SSet.Nonempty V := ⟨(SSet.stdSimplex.const 1 0 (op ⦋0⦌),
    SSet.stdSimplex.const m 0 (op ⦋0⦌))⟩
  let p : V.obj (op ⦋0⦌) :=
    ((boundaryOneVertex (m := op ⦋0⦌) 0).1, SSet.stdSimplex.const m 0 (op ⦋0⦌))
  have : SSet.Nonempty (U : SSet) := ⟨⟨p, (SSet.Subcomplex.mem_unionProd_iff S T p).2
    (Or.inr (boundaryOneVertex (m := op ⦋0⦌) 0).2)⟩⟩
  obtain ⟨Q, hFull, hTop, hBottom, hRight, hUnion,
    hEndpoint, hUnitH, hUnitPair, hCoskE, hCompareTop, hCompareBottom, hPullback⟩ :=
    homotopyMatchingSquare X L H hH n
  let comparison := hUnion.homEquiv.symm (U.ι ≫ hFull.homEquiv (𝟙 (H _⦋m⦌)))
  have hComparisonCover : IsCoveringOver J comparison :=
    isCoveringOver_representableBy_comparison J hL V U hFull hUnion
  let fRight := (((SimplicialObject.coskAdj n).unit.app (L ⨯ L)).app i)
  let gRight := (((SimplicialObject.Truncated.cosk n).map
    ((SimplicialObject.truncation n).map e)).app i)
  let mLift : H _⦋m⦌ ⟶ Limits.pullback fRight gRight :=
    Limits.pullback.lift (e.app i) (((SimplicialObject.coskAdj n).unit.app H).app i)
      (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality e) i)
  let hCanonical := IsPullback.of_hasPullback gRight fRight
  rw [← hCoskE, ← hUnitPair] at hPullback
  let isoUnionPullback :=
    hPullback.isoIsPullback _ _ hCanonical ≪≫ pullbackSymmetry gRight fRight
  have hIsoBottom := hPullback.isoIsPullback_hom_snd _ _ hCanonical
  have hIsoTop := hPullback.isoIsPullback_hom_fst _ _ hCanonical
  have hMfst : mLift ≫ Limits.pullback.fst fRight gRight = e.app i :=
    Limits.pullback.lift_fst _ _ _
  have hMsnd : mLift ≫ Limits.pullback.snd fRight gRight =
      ((SimplicialObject.coskAdj n).unit.app H).app i :=
    Limits.pullback.lift_snd _ _ _
  have hFactor : comparison ≫ isoUnionPullback.hom = mLift := by
    dsimp only [isoUnionPullback]
    apply Limits.pullback.hom_ext
    · simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
      rw [hIsoBottom, hMfst]
      simpa [comparison, e] using hCompareBottom
    · simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
      rw [hIsoTop, hMsnd]
      simpa [comparison] using hCompareTop
  change IsCoveringOver J mLift
  rw [← hFactor]
  exact hComparisonCover.comp_isIso J isoUnionPullback.hom

/-- **Stacks Project, Tag 01GS**, for the interval in the hom-universe of `SR(C, X)`. Two
morphisms between hypercoverings become simplicially homotopic after precomposition with a
morphism from a further hypercovering. -/
theorem exists_homotopy_after_hypercovering_refinement_max (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) (a b : K ⟶ L) :
    ∃ (K' : SimplicialObject (FormalCoproduct.{w} (Over X))) (c : K' ⟶ K),
      IsHypercovering J K' ∧
        ∃ h : K'.copower (Δ[1] : SSet.{max v w}) ⟶ L,
          SimplicialObject.IsHomotopy h (c ≫ a) (c ≫ b) := by
  classical
  let H := homFromSSet (X := X) (Δ[1] : SSet.{max v w}) L
  let hH := homFromSSetIsHom (X := X) (Δ[1] : SSet.{max v w}) L
  let e := (intervalEndpointMap X L H hH).1
  let f : K ⟶ L ⨯ L := prod.lift a b
  let K' := SimplicialObject.fibreProduct f e
  let c : K' ⟶ K := pointwisePullback.fst f e
  let q : K' ⟶ H := pointwisePullback.snd f e
  refine ⟨K', c, isHypercovering_fibreProduct J f e hK
    (isCoveringOver_intervalEndpointMap_app_zero J hL)
    (isCoveringOver_intervalEndpointMap_matching J hL), ?_⟩
  let hData := Functor.functorHomEquiv K' L (Δ[1] : SSet.{max v w}) (hH.homEquiv q)
  let h : K'.copower (Δ[1] : SSet.{max v w}) ⟶ L :=
    { app := fun m ↦ Sigma.desc (fun x ↦ hData.app m x)
      naturality m m' φ := Sigma.hom_ext _ _ fun x ↦ by
        simp only [Functor.copower_map, Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc,
          Sigma.ι_comp_desc_assoc]
        exact hData.naturality φ x }
  have hqe : q ≫ e = c ≫ f :=
    NatTrans.ext <| funext fun d ↦ (Limits.pullback.condition (f := f.app d) (g := e.app d)).symm
  have heval (m : SimplexCategoryᵒᵖ) (x : (Δ[1] : SSet.{max v w}).obj m) : hData.app m x =
      q.app m ≫ (Functor.functorHomEquiv H L (Δ[1] : SSet.{max v w})
        (hH.homEquiv (𝟙 H))).app m x := by
    have hcomp := hH.homEquiv_comp q (𝟙 H)
    rw [Category.comp_id] at hcomp
    have hcomp' := congrArg (Functor.functorHomEquiv K' L (Δ[1] : SSet.{max v w})) hcomp
    rw [functorHomEquiv_sHomFunctorMap] at hcomp'
    exact congrArg (fun t ↦ t.app m x) hcomp'
  have key (i : Fin 2) (p : L ⨯ L ⟶ L) (g : K ⟶ L) (hg : f ≫ p = g)
      (hp : ∀ m, (e ≫ p).app m = (Functor.functorHomEquiv H L (Δ[1] : SSet.{max v w})
        (hH.homEquiv (𝟙 H))).app m (SSet.stdSimplex.const 1 i m)) (m : SimplexCategoryᵒᵖ) :
      Sigma.ι (fun _ : (Δ[1] : SSet.{max v w}).obj m ↦ K'.obj m)
        (SSet.stdSimplex.const 1 i m) ≫ h.app m = (c ≫ g).app m := by
    dsimp only [h]
    rw [Sigma.ι_comp_desc, heval, ← hp m, ← hg]
    simpa using congrArg (fun z ↦ (z ≫ p).app m) hqe
  exact ⟨h, key 0 prod.fst a (prod.lift_fst _ _) (intervalEndpointMap X L H hH).2.1,
    key 1 prod.snd b (prod.lift_snd _ _) (intervalEndpointMap X L H hH).2.2⟩

/-- **Stacks Project, Tag 01GS**, for the interval in an arbitrary universe. -/
theorem exists_homotopy_after_hypercovering_refinement_universe (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) (a b : K ⟶ L) :
    ∃ (K' : SimplicialObject (FormalCoproduct.{w} (Over X))) (c : K' ⟶ K),
      IsHypercovering J K' ∧
        ∃ h : K'.copower (SSet.stdSimplex.{z}.obj ⦋1⦌) ⟶ L,
          SimplicialObject.IsHomotopy h (c ≫ a) (c ≫ b) := by
  classical
  obtain ⟨K', c, hK', hMax, hHomotopy⟩ :=
    exists_homotopy_after_hypercovering_refinement_max J hK hL a b
  let h : K'.copower (SSet.stdSimplex.{z}.obj ⦋1⦌) ⟶ L :=
    { app := fun m ↦ Sigma.desc (fun x ↦
        Sigma.ι (fun _ : (SSet.stdSimplex.{max v w}.obj ⦋1⦌).obj m ↦ K'.obj m)
          (intervalUniverseLift.{z, max v w} x) ≫ hMax.app m)
      naturality := by
        intro m m' f
        apply Sigma.hom_ext
        intro x
        simp only [Functor.copower_map, Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc]
        calc
          K'.map f ≫
              Sigma.ι (fun _ : (SSet.stdSimplex.{max v w}.obj ⦋1⦌).obj m' ↦ K'.obj m')
                (intervalUniverseLift.{z, max v w}
                  ((SSet.stdSimplex.{z}.obj ⦋1⦌).map f x)) ≫ hMax.app m' =
            (Sigma.ι (fun _ : (SSet.stdSimplex.{max v w}.obj ⦋1⦌).obj m ↦ K'.obj m)
              (intervalUniverseLift.{z, max v w} x) ≫
                (K'.copower (SSet.stdSimplex.{max v w}.obj ⦋1⦌)).map f) ≫ hMax.app m' := by
            rw [intervalUniverseLift_map.{z, max v w} f x]
            simp [Category.assoc]
          _ = Sigma.ι (fun _ : (SSet.stdSimplex.{max v w}.obj ⦋1⦌).obj m ↦ K'.obj m)
              (intervalUniverseLift.{z, max v w} x) ≫ hMax.app m ≫ L.map f := by
            rw [← hMax.naturality]
            simp [Category.assoc]
          _ = Sigma.ι (fun _ : (SSet.stdSimplex.{z}.obj ⦋1⦌).obj m ↦ K'.obj m) x ≫
              (Sigma.desc (fun y ↦ Sigma.ι
                (fun _ : (SSet.stdSimplex.{max v w}.obj ⦋1⦌).obj m ↦ K'.obj m)
                  (intervalUniverseLift.{z, max v w} y) ≫ hMax.app m)) ≫ L.map f := by
            simp }
  refine ⟨K', c, hK', h, ?_, ?_⟩ <;> intro m <;> dsimp only [h] <;>
    rw [Sigma.ι_comp_desc, intervalUniverseLift_const]
  exacts [hHomotopy.1 m, hHomotopy.2 m]

/-- **Stacks Project, Tag 01GS.** Two morphisms between hypercoverings become simplicially
homotopic after precomposition with a morphism from a further hypercovering. -/
@[stacks 01GS]
theorem exists_homotopy_after_hypercovering_refinement (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {K L : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hK : IsHypercovering J K) (hL : IsHypercovering J L) (a b : K ⟶ L) :
    ∃ (K' : SimplicialObject (FormalCoproduct.{w} (Over X))) (c : K' ⟶ K),
      IsHypercovering J K' ∧
        ∃ h : K'.copower Δ[1] ⟶ L, SimplicialObject.IsHomotopy h (c ≫ a) (c ≫ b) :=
  exists_homotopy_after_hypercovering_refinement_universe J hK hL a b

end Stacks.CategoryTheory.Hypercovering

end
