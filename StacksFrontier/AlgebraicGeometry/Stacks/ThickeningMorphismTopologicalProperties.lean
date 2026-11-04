module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversallyInjective

/-!
# Topological properties in a morphism of thickenings of algebraic stacks (Stacks 0CJ9)

Stacks 0CJ9 reads, at the three items treated here:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (3) `f` is quasi-compact if and only if `f'` quasi-compact,
> (4) `f` is universally closed if and only if `f'` is universally closed,
> (7) `f` is universally open if and only if `f'` is universally open.

The source's proof: the thickenings `𝒳 → 𝒳'` and `𝒴 → 𝒴'` are universal homeomorphisms
(**Stacks 0CJ7**), so any condition on `|f|` is equivalent to the corresponding condition on
`|f'|`, and the same is true after an arbitrary base change by a morphism `𝒵' → 𝒴'`.

Each of the three notions quantifies over test 1-morphisms into the *target*, and the targets
`𝒴`, `𝒴'` of `f`, `f'` differ, so the source's sentence is made precise here by two comparison
lemmas between the base changes of `f` and of `f'`.

* `AlgebraicGeometry.Stack.exists_isThickening_baseChange_comp`: for a test `d : 𝒵 ⟶ 𝒴`, there is
  a thickening `𝒵 ×_𝒴 𝒳 ⟶ 𝒵 ×_{𝒴'} 𝒳'` (the second base change along `d ≫ j`) over `𝒵`. It is
  the composite of enlarging the target of the cospan along `j` (an equivalence, `j` being fully
  faithful, **Stacks 04ZZ**), the comparison of two 2-fibre products of the cospan
  `(d ≫ j, f ≫ j) ≅ (d ≫ j, i ≫ f')`, and the base change of the thickening `i` along
  `𝒵 ×_{𝒴'} 𝒳' ⟶ 𝒳'` (**Stacks 0BPR**).
* `AlgebraicGeometry.Stack.exists_isThickening_baseChange_of_twoIso`: more generally, for tests
  `d : 𝒵 ⟶ 𝒴` and `t : 𝒵' ⟶ 𝒴'` related by a thickening `q : 𝒵 ⟶ 𝒵'` and a 2-isomorphism
  `q ≫ t ≅ d ≫ j`, there is a thickening `𝒵 ×_𝒴 𝒳 ⟶ 𝒵' ×_{𝒴'} 𝒳'` lying over `q` on points. It
  is the previous comparison followed by the base change of `q` along `𝒵' ×_{𝒴'} 𝒳' ⟶ 𝒵'`. The
  instance used for an arbitrary test `t` is `𝒵 = 𝒵' ×_{𝒴'} 𝒴`, with `q` the base change of `j`.

A thickening is a homeomorphism on points
(`AlgebraicGeometry.Stack.isHomeomorphOnPoints_of_isThickening`), so both comparisons identify the
map on points of a base change of `f` with that of a base change
of `f'` up to homeomorphisms; closedness and openness of a map of topological spaces, and
compactness of a space (quasi-compactness of an algebraic stack is compactness of its space of
points, **Stacks 04YB**), are invariant under such identifications.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_inner_iff_outer`: **Stacks 0CJ9**, part (3).
* `AlgebraicGeometry.Stack.universallyClosed_inner_iff_outer`: **Stacks 0CJ9**, part (4).
* `AlgebraicGeometry.Stack.universallyOpen_inner_iff_outer`: **Stacks 0CJ9**, part (7).

## References

* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CJ7](https://stacks.math.columbia.edu/tag/0CJ7)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- **A base change of the restricted 1-morphism of a morphism of thickenings is a thickening of
the corresponding base change of the ambient one.** For a test `d : 𝒵 ⟶ 𝒴` there is a thickening
`c : 𝒵 ×_{d, 𝒴} 𝒳 ⟶ 𝒵 ×_{d ≫ j, 𝒴'} 𝒳'` of the canonical 2-fibre products of Stacks 04T2 under
which the first projection of the source is the first projection of the target, on points.

The 1-morphism is enlarging the target of the cospan along `j` (an equivalence because `j` is
fully faithful, **Stacks 04ZZ**), followed by the comparison with the 2-fibre product of
`(d ≫ j, f ≫ j)` obtained by pasting `𝒵 ×_{𝒴'} 𝒳'` with its base change along `i` and
reindexing along the restriction 2-isomorphism, followed by that base change of `i`, which is a
thickening by **Stacks 0BPR**. -/
theorem exists_isThickening_baseChange_comp (m : ThickeningMorphism i j hi hj)
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (d : 𝒵 ⟶ 𝒴) :
    ∃ c : (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).pt ⟶
        (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).pt,
      IsThickening c ∧
        AlgebraicStacks.pointsMap B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).fst ∘
          AlgebraicStacks.pointsMap B S hS c =
        AlgebraicStacks.pointsMap B S hS
          (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).fst := by
  have hjff := AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  set E := AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer
  have hE := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (d ≫ j) m.outer
  set T := AlgebraicStacks.twoFibreProductSquare B S hS E.snd i
  have hT := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS E.snd i
  have hTfst : IsThickening T.fst := isThickening_fst_of_isTwoFibreProduct B S hS hi T hT
  have hA := Bicategory.isTwoFibreProduct_reindexSnd (P := E.pasteSnd T) m.comm.symm
    (Bicategory.isTwoFibreProduct_pasteSnd E hE T hT)
  set C := AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (m.inner ≫ j)
  have hC := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (d ≫ j)
    (m.inner ≫ j)
  let a := Bicategory.twoFibreProductPreHom hA C
  have := isEquivalence_homFunctor_preHom B S hS hC hA a
  have := isEquivalence_enlargeTargetComparison B S hS d m.inner hjff
  refine ⟨enlargeTargetComparison B S hS d m.inner j ≫ a.hom ≫ T.fst,
    isThickening_comp_of_isEquivalence B S hS _ _
      (isThickening_comp_of_isEquivalence B S hS a.hom T.fst hTfst), ?_⟩
  have ha : AlgebraicStacks.pointsMap B S hS C.fst =
      AlgebraicStacks.pointsMap B S hS ((E.pasteSnd T).reindexSnd m.comm.symm).fst ∘
        AlgebraicStacks.pointsMap B S hS a.hom :=
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS a.isoFst.hom).trans
      (AlgebraicStacks.pointsMap_comp B S hS a.hom _)
  have hAfst : AlgebraicStacks.pointsMap B S hS ((E.pasteSnd T).reindexSnd m.comm.symm).fst =
      AlgebraicStacks.pointsMap B S hS E.fst ∘ AlgebraicStacks.pointsMap B S hS T.fst :=
    AlgebraicStacks.pointsMap_comp B S hS T.fst E.fst
  have hen : AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).fst =
        AlgebraicStacks.pointsMap B S hS C.fst ∘
          AlgebraicStacks.pointsMap B S hS (enlargeTargetComparison B S hS d m.inner j) := by
    rw [← AlgebraicStacks.pointsMap_comp, enlargeTargetComparison_comp_fst]
  have hc : AlgebraicStacks.pointsMap B S hS (a.hom ≫ T.fst) =
      AlgebraicStacks.pointsMap B S hS T.fst ∘ AlgebraicStacks.pointsMap B S hS a.hom :=
    AlgebraicStacks.pointsMap_comp B S hS _ _
  funext x
  rw [hen, AlgebraicStacks.pointsMap_comp, hc]
  exact (congrFun (ha.trans (congrArg (· ∘ AlgebraicStacks.pointsMap B S hS a.hom) hAfst))
    (AlgebraicStacks.pointsMap B S hS (enlargeTargetComparison B S hS d m.inner j) x)).symm

/-- **Base changes of the two 1-morphisms of a morphism of thickenings along related tests.** Let
`d : 𝒵 ⟶ 𝒴` and `t : 𝒵' ⟶ 𝒴'` be test 1-morphisms, `q : 𝒵 ⟶ 𝒵'` a thickening and
`θ : q ≫ t ≅ d ≫ j` a 2-isomorphism. Then there is a thickening
`c : 𝒵 ×_{d, 𝒴} 𝒳 ⟶ 𝒵' ×_{t, 𝒴'} 𝒳'` of the canonical 2-fibre products of Stacks 04T2 lying
over `q` on points.

It is `AlgebraicGeometry.Stack.exists_isThickening_baseChange_comp` followed by the comparison of
two 2-fibre products of `(d ≫ j, f')` — the canonical one and the rectangle obtained by pasting
`𝒵' ×_{𝒴'} 𝒳'` with its base change along `q`, reindexed along `θ` — and by that base change of
`q`, a thickening by **Stacks 0BPR**. -/
theorem exists_isThickening_baseChange_of_twoIso (m : ThickeningMorphism i j hi hj)
    {𝒵 𝒵' : AlgebraicStacks.{u, w} B S hS} (d : 𝒵 ⟶ 𝒴) (t : 𝒵' ⟶ 𝒴') (q : 𝒵 ⟶ 𝒵')
    (hq : IsThickening q) (θ : q ≫ t ≅ d ≫ j) :
    ∃ c : (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).pt ⟶
        (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).pt,
      IsThickening c ∧
        AlgebraicStacks.pointsMap B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).fst ∘
          AlgebraicStacks.pointsMap B S hS c =
        AlgebraicStacks.pointsMap B S hS q ∘ AlgebraicStacks.pointsMap B S hS
          (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).fst := by
  set Q := AlgebraicStacks.twoFibreProductSquare B S hS t m.outer
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS t m.outer
  set V := AlgebraicStacks.twoFibreProductSquare B S hS q Q.fst
  have hV := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS q Q.fst
  have hVsnd : IsThickening V.snd := isThickening_snd_of_isTwoFibreProduct B S hS hq V hV
  have hR := Bicategory.isTwoFibreProduct_reindexFst θ
    (Bicategory.isTwoFibreProduct_pasteFst Q hQ V hV)
  set E := AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer
  have hE := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (d ≫ j) m.outer
  let e := Bicategory.twoFibreProductPreHom hR E
  have := isEquivalence_homFunctor_preHom B S hS hE hR e
  obtain ⟨c₁, hc₁, hpm₁⟩ := exists_isThickening_baseChange_comp B S hS m d
  refine ⟨c₁ ≫ e.hom ≫ V.snd, isThickening_comp c₁ _ hc₁
    (isThickening_comp_of_isEquivalence B S hS e.hom V.snd hVsnd), ?_⟩
  have hVsq : AlgebraicStacks.pointsMap B S hS Q.fst ∘ AlgebraicStacks.pointsMap B S hS V.snd =
      AlgebraicStacks.pointsMap B S hS q ∘ AlgebraicStacks.pointsMap B S hS V.fst := by
    rw [← AlgebraicStacks.pointsMap_comp, ← AlgebraicStacks.pointsMap_comp]
    exact (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS V.iso.hom).symm
  have he : AlgebraicStacks.pointsMap B S hS E.fst =
      AlgebraicStacks.pointsMap B S hS V.fst ∘ AlgebraicStacks.pointsMap B S hS e.hom :=
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS e.isoFst.hom).trans
      (AlgebraicStacks.pointsMap_comp B S hS e.hom ((Q.pasteFst V).reindexFst θ).fst)
  have hc : AlgebraicStacks.pointsMap B S hS (e.hom ≫ V.snd) =
      AlgebraicStacks.pointsMap B S hS V.snd ∘ AlgebraicStacks.pointsMap B S hS e.hom :=
    AlgebraicStacks.pointsMap_comp B S hS _ _
  funext x
  rw [AlgebraicStacks.pointsMap_comp, hc]
  exact (congrFun hVsq (AlgebraicStacks.pointsMap B S hS e.hom
    (AlgebraicStacks.pointsMap B S hS c₁ x))).trans
    ((congrArg (AlgebraicStacks.pointsMap B S hS q)
      (congrFun he (AlgebraicStacks.pointsMap B S hS c₁ x)).symm).trans
      (congrArg (AlgebraicStacks.pointsMap B S hS q) (congrFun hpm₁ x)))

end Comparison

section Items

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}

/-- The test of `exists_isThickening_baseChange_of_twoIso` attached to a test `t : 𝒵' ⟶ 𝒴'` of
the ambient 1-morphism: the base change `W = 𝒵' ×_{t, 𝒴', j} 𝒴`, whose first projection to `𝒵'`
is a thickening by **Stacks 0BPR**, with the comparison 2-isomorphism of that square. -/
theorem exists_isThickening_baseChange_outer (m : ThickeningMorphism i j hi hj)
    {𝒵' : AlgebraicStacks.{u, w} B S hS} (t : 𝒵' ⟶ 𝒴') :
    ∃ c : (AlgebraicStacks.twoFibreProductSquare B S hS
          (AlgebraicStacks.twoFibreProductSquare B S hS t j).snd m.inner).pt ⟶
        (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).pt,
      IsThickening c ∧
        AlgebraicStacks.pointsMap B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).fst ∘
          AlgebraicStacks.pointsMap B S hS c =
        AlgebraicStacks.pointsMap B S hS (AlgebraicStacks.twoFibreProductSquare B S hS t j).fst ∘
          AlgebraicStacks.pointsMap B S hS (AlgebraicStacks.twoFibreProductSquare B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS t j).snd m.inner).fst :=
  exists_isThickening_baseChange_of_twoIso B S hS m _ t _
    (isThickening_fst_of_isTwoFibreProduct B S hS hj _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS t j))
    (AlgebraicStacks.twoFibreProductSquare B S hS t j).iso

/-- If `g ∘ c = q ∘ f` with `c` and `q` homeomorphisms, then `g` is a closed map as soon as `f`
is. -/
theorem _root_.IsClosedMap.of_comp_eq_comp_isHomeomorph {X Y X' Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] {f : X → Y} {g : X' → Y'}
    {c : X → X'} {q : Y → Y'} (hf : IsClosedMap f) (hc : IsHomeomorph c) (hq : IsHomeomorph q)
    (h : g ∘ c = q ∘ f) : IsClosedMap g := by
  intro F hF
  rw [← Set.image_preimage_eq F hc.surjective, ← Set.image_comp, h, Set.image_comp]
  exact hq.isClosedMap _ (hf _ (hF.preimage hc.continuous))

/-- If `g ∘ c = q ∘ f` with `c` and `q` homeomorphisms, then `g` is an open map as soon as `f`
is. -/
theorem _root_.IsOpenMap.of_comp_eq_comp_isHomeomorph {X Y X' Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] {f : X → Y} {g : X' → Y'}
    {c : X → X'} {q : Y → Y'} (hf : IsOpenMap f) (hc : IsHomeomorph c) (hq : IsHomeomorph q)
    (h : g ∘ c = q ∘ f) : IsOpenMap g := by
  intro F hF
  rw [← Set.image_preimage_eq F hc.surjective, ← Set.image_comp, h, Set.image_comp]
  exact hq.isOpenMap _ (hf _ (hF.preimage hc.continuous))

/-- The first projection of the base change of a thickening `j` along `t` is a homeomorphism on
points. -/
private theorem isHomeomorphOnPoints_fst_twoFibreProductSquare
    {𝒴 𝒴' 𝒵' : AlgebraicStacks.{u, w} B S hS} {j : 𝒴 ⟶ 𝒴'} (hj : IsThickening j) (t : 𝒵' ⟶ 𝒴') :
    AlgebraicStacks.IsHomeomorphOnPoints B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS t j).fst :=
  isHomeomorphOnPoints_of_isThickening B S hS
    (isThickening_fst_of_isTwoFibreProduct B S hS hj _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS t j))

/-- **Stacks 0CJ9, part (4), from the ambient 1-morphism to the restricted one.** -/
theorem universallyClosed_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (h : AlgebraicStacks.UniversallyClosed B S hS m.outer) :
    AlgebraicStacks.UniversallyClosed B S hS m.inner := by
  intro 𝒵 d
  obtain ⟨c, hc, hpm⟩ := exists_isThickening_baseChange_comp B S hS m d
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).pt.val
  let _ := pointTopology B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).pt.val
  let _ := pointTopology B S hS 𝒵.val
  show IsClosedMap (AlgebraicStacks.pointsMap B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).fst)
  rw [← hpm]
  exact IsClosedMap.comp (h 𝒵 (d ≫ j)) (isHomeomorphOnPoints_of_isThickening B S hS hc).isClosedMap

/-- **Stacks 0CJ9, part (4), from the restricted 1-morphism to the ambient one.** -/
theorem universallyClosed_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (h : AlgebraicStacks.UniversallyClosed B S hS m.inner) :
    AlgebraicStacks.UniversallyClosed B S hS m.outer := by
  intro 𝒵' t
  set W := AlgebraicStacks.twoFibreProductSquare B S hS t j
  obtain ⟨c, hc, hpm⟩ := exists_isThickening_baseChange_outer B S hS m t
  have hqh := isHomeomorphOnPoints_fst_twoFibreProductSquare B S hS hj t
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS W.snd m.inner).pt.val
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).pt.val
  let _ := pointTopology B S hS 𝒵'.val
  let _ := pointTopology B S hS W.pt.val
  have hP : IsClosedMap (AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS W.snd m.inner).fst) := h W.pt W.snd
  show IsClosedMap (AlgebraicStacks.pointsMap B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).fst)
  exact IsClosedMap.of_comp_eq_comp_isHomeomorph hP
    (isHomeomorphOnPoints_of_isThickening B S hS hc) hqh hpm

/-- **Stacks 0CJ9, part (4).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is universally closed (**Stacks 0513**)
if and only if the ambient 1-morphism `f'` is.

The base changes of `f` and of `f'` are compared by the thickenings of
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_comp` and
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_outer`, which are homeomorphisms on points
(**Stacks 0CJ7**). -/
@[stacks 0CJ9 "part (4): universally closed"]
theorem universallyClosed_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.UniversallyClosed B S hS m.inner ↔
      AlgebraicStacks.UniversallyClosed B S hS m.outer :=
  ⟨universallyClosed_outer_of_inner B S hS m, universallyClosed_inner_of_outer B S hS m⟩

/-- **Stacks 0CJ9, part (7), from the ambient 1-morphism to the restricted one.** -/
theorem universallyOpen_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (h : AlgebraicStacks.UniversallyOpen B S hS m.outer) :
    AlgebraicStacks.UniversallyOpen B S hS m.inner := by
  intro 𝒵 d
  obtain ⟨c, hc, hpm⟩ := exists_isThickening_baseChange_comp B S hS m d
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).pt.val
  let _ := pointTopology B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).pt.val
  let _ := pointTopology B S hS 𝒵.val
  show IsOpenMap (AlgebraicStacks.pointsMap B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).fst)
  rw [← hpm]
  exact IsOpenMap.comp (h 𝒵 (d ≫ j)) (isHomeomorphOnPoints_of_isThickening B S hS hc).isOpenMap

/-- **Stacks 0CJ9, part (7), from the restricted 1-morphism to the ambient one.** -/
theorem universallyOpen_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (h : AlgebraicStacks.UniversallyOpen B S hS m.inner) :
    AlgebraicStacks.UniversallyOpen B S hS m.outer := by
  intro 𝒵' t
  set W := AlgebraicStacks.twoFibreProductSquare B S hS t j
  obtain ⟨c, hc, hpm⟩ := exists_isThickening_baseChange_outer B S hS m t
  have hqh := isHomeomorphOnPoints_fst_twoFibreProductSquare B S hS hj t
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS W.snd m.inner).pt.val
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).pt.val
  let _ := pointTopology B S hS 𝒵'.val
  let _ := pointTopology B S hS W.pt.val
  have hP : IsOpenMap (AlgebraicStacks.pointsMap B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS W.snd m.inner).fst) := h W.pt W.snd
  show IsOpenMap (AlgebraicStacks.pointsMap B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS t m.outer).fst)
  exact IsOpenMap.of_comp_eq_comp_isHomeomorph hP
    (isHomeomorphOnPoints_of_isThickening B S hS hc) hqh hpm

/-- **Stacks 0CJ9, part (7).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is universally open (**Stacks 06U2**)
if and only if the ambient 1-morphism `f'` is. The argument is that of part (4). -/
@[stacks 0CJ9 "part (7): universally open"]
theorem universallyOpen_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    AlgebraicStacks.UniversallyOpen B S hS m.inner ↔
      AlgebraicStacks.UniversallyOpen B S hS m.outer :=
  ⟨universallyOpen_outer_of_inner B S hS m, universallyOpen_inner_of_outer B S hS m⟩

/-- **Stacks 0CJ9, part (3), from the ambient 1-morphism to the restricted one.** A base change
of `f` along a test out of a quasi-compact stack is homeomorphic on points to a base change of
`f'` along a test out of the same stack. -/
theorem isQuasiCompactMorphism_inner_of_outer (m : ThickeningMorphism i j hi hj)
    (h : IsQuasiCompactMorphism B S hS m.outer) : IsQuasiCompactMorphism B S hS m.inner := by
  intro 𝒵 d h𝒵
  obtain ⟨c, hc, -⟩ := exists_isThickening_baseChange_comp B S hS m d
  let _ := pointTopology B S hS (AlgebraicStacks.twoFibreProductSquare B S hS d m.inner).pt.val
  let _ := pointTopology B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).pt.val
  have : CompactSpace (AlgebraicStacks.points B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) m.outer).pt) := h 𝒵 (d ≫ j) h𝒵
  exact (isHomeomorphOnPoints_of_isThickening B S hS hc).isClosedEmbedding.compactSpace

/-- **Stacks 0CJ9, part (3), from the restricted 1-morphism to the ambient one.** For a test
`t : 𝒵' ⟶ 𝒴'` out of a quasi-compact stack, `𝒵' ×_{𝒴'} 𝒴` is quasi-compact (it is homeomorphic
to `𝒵'` on points), the base change of `f` along it is quasi-compact by hypothesis, and it
surjects onto the base change of `f'` along `t`. -/
theorem isQuasiCompactMorphism_outer_of_inner (m : ThickeningMorphism i j hi hj)
    (h : IsQuasiCompactMorphism B S hS m.inner) : IsQuasiCompactMorphism B S hS m.outer := by
  intro 𝒵' t h𝒵'
  set W := AlgebraicStacks.twoFibreProductSquare B S hS t j
  obtain ⟨c, hc, -⟩ := exists_isThickening_baseChange_outer B S hS m t
  have hqh := isHomeomorphOnPoints_fst_twoFibreProductSquare B S hS hj t
  have hW : IsQuasiCompactStack.{u, w} B S hS W.pt.val W.pt.property := by
    let _ := pointTopology B S hS 𝒵'.val
    let _ := pointTopology B S hS W.pt.val
    have : CompactSpace (AlgebraicStacks.points B S hS 𝒵') := h𝒵'
    exact hqh.isClosedEmbedding.compactSpace
  exact isQuasiCompactStack_of_isSurjective B S hS c (h W.pt W.snd hW) hc.2

/-- **Stacks 0CJ9, part (3).** In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of
algebraic stacks over `S`, the restricted 1-morphism `f` is quasi-compact (**Stacks 050U**) if
and only if the ambient 1-morphism `f'` is.

Quasi-compactness of an algebraic stack is compactness of its space of points (**Stacks 04YB**),
and the base changes of `f` and of `f'` are compared by the thickenings of
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_comp` and
`AlgebraicGeometry.Stack.exists_isThickening_baseChange_outer`. -/
@[stacks 0CJ9 "part (3): quasi-compact"]
theorem isQuasiCompactMorphism_inner_iff_outer (m : ThickeningMorphism i j hi hj) :
    IsQuasiCompactMorphism B S hS m.inner ↔ IsQuasiCompactMorphism B S hS m.outer :=
  ⟨isQuasiCompactMorphism_outer_of_inner B S hS m, isQuasiCompactMorphism_inner_of_outer B S hS m⟩

end Items

end AlgebraicGeometry.Stack

end
