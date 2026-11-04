module

public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The standard simplex is `1`-coskeletal

Let `Δ` be the simplex category, the finite nonempty ordinals `⦋m⦌ = {0 < 1 < ⋯ < m}` with the
order-preserving maps, and for `n : ℕ` let `Δ[n]` be the standard `n`-simplex, the simplicial set
represented by `⦋n⦌`. The skeleton functor `sk_1 : SSet ⥤ SSet.Truncated 1` restricts a simplicial
set to the full subcategory `Δ_{≤ 1} ⊆ Δ`, and its right adjoint is the coskeleton functor
`cosk_1`, so that `Mor(U, cosk_1 V) = Mor(sk_1 U, V)`. The canonical map
`c_X : X ⟶ cosk_1 sk_1 X` is the unit of that adjunction at `X`, and `c_{Δ[n]}` is an isomorphism
of simplicial sets for every `n`.

Equivalently, `Δ[n]` is `1`-coskeletal: it is the right Kan extension of its `1`-truncation along
`(Δ_{≤ 1})ᵒᵖ ⥤ Δᵒᵖ`. This holds pointwise at each `⦋m⦌`, because an `m`-simplex of `Δ[n]` is an
order-preserving map `⦋m⦌ → ⦋n⦌`, hence is determined by its values on the vertices `⦋0⦌ ⟶ ⦋m⦌`,
and conversely every family of vertex and edge values compatible with the maps between `⦋0⦌` and
`⦋1⦌` comes from such a map: monotonicity is exactly the constraint imposed by the edge
`⦋1⦌ ⟶ ⦋m⦌` joining a pair `j ≤ j'`, and such an edge is available for every pair, so no
`2`-simplex is involved.

## Main definitions

* `SSet.cosk1Unit`: the canonical map `c_X : X ⟶ cosk_1 sk_1 X`.
* `SSet.stdSimplex.isPointwiseRightKanExtensionAt.liftSimplex`: the `m`-simplex
  `⦋m⦌ ⟶ ⦋n⦌` of `Δ[n]` reconstructed from the vertex values of a cone.
* `SSet.stdSimplex.isPointwiseRightKanExtensionAt.canonCone`: the cone with apex
  `Δ[n] _⦋m⦌` over the `1`-truncated structured-arrow diagram of `Δ[n]` at `⦋m⦌`.

## Main results

* `SSet.stdSimplex.isPointwiseRightKanExtensionAt`: the canonical cone exhibiting `Δ[n]` at
  level `m` as a limit over the `1`-truncated structured-arrow diagram is a limit cone.
* `SSet.stdSimplex.isCoskeletal`: `Δ[n]` is `1`-coskeletal.
* `SSet.canonicalMap_stdSimplex_isIso`: `cosk1Unit Δ[n]` is an isomorphism.

## References

* [Stacks, Tag 018E](https://stacks.math.columbia.edu/tag/018E)
-/

open CategoryTheory Simplicial SimplexCategory Functor Limits

namespace SSet

/-- The canonical map `c_X : X ⟶ cosk_1 sk_1 X`, the unit of the adjunction `sk_1 ⊣ cosk_1`
at `X`. -/
noncomputable def cosk1Unit (X : SSet) :
    X ⟶ (SSet.truncation 1 ⋙ SSet.Truncated.cosk 1).obj X :=
  (SSet.coskAdj 1).unit.app X

namespace stdSimplex

namespace isPointwiseRightKanExtensionAt

open SimplexCategory.Truncated Opposite

universe u

/-- The object of the comma category `StructuredArrow (op ⦋m⦌) (Truncated.inclusion 1).op`
defined by a morphism `φ : ⦋i⦌ ⟶ ⦋m⦌` of `SimplexCategory` with `i ≤ 1`. -/
abbrev strArrowMk₁ {i : ℕ} {m : ℕ} (φ : ⦋i⦌ ⟶ ⦋m⦌) (hi : i ≤ 1 := by omega) :
    StructuredArrow (op ⦋m⦌) (Truncated.inclusion 1).op :=
  StructuredArrow.mk (Y := op ⦋i⦌₁) φ.op

/-- The type of cones over the `1`-truncated structured-arrow diagram of `Δ[n]` at `⦋m⦌`. -/
abbrev Cn (n m : ℕ) : Type _ :=
  Cone (StructuredArrow.proj (op ⦋m⦌) (Truncated.inclusion 1).op ⋙
    (Truncated.inclusion 1).op ⋙ (Δ[n] : SSet.{u}))

variable {n m : ℕ}

/-- `objEquiv` intertwines the simplicial-set action of `Δ[n]` with precomposition. -/
lemma objEquiv_map {k l : SimplexCategory} (ψ : k ⟶ l) (y : (Δ[n] : SSet.{u}).obj (op l)) :
    SSet.stdSimplex.objEquiv ((Δ[n] : SSet.{u}).map ψ.op y)
      = ψ ≫ SSet.stdSimplex.objEquiv y := by
  conv_lhs => rw [← Equiv.symm_apply_apply SSet.stdSimplex.objEquiv y,
    SSet.stdSimplex.map_objEquiv_symm, Equiv.apply_symm_apply]
  rfl

/-- The morphism `strArrowMk₁ ψ ⟶ strArrowMk₁ φ` of structured arrows given by a factorization
`φ = θ ≫ ψ`. -/
def saHom {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1)
    (ψ : ⦋j⦌ ⟶ ⦋m⦌) (θ : (⦋i⦌ : SimplexCategory) ⟶ ⦋j⦌) (φ : ⦋i⦌ ⟶ ⦋m⦌) (hφ : φ = θ ≫ ψ) :
    strArrowMk₁ ψ hj ⟶ strArrowMk₁ φ hi :=
  StructuredArrow.homMk (Hom.tr θ (by omega) (by omega)).op
    (Quiver.Hom.unop_inj (by subst hφ; rfl))

/-- Naturality of a cone `s` along `saHom`: the leg at `strArrowMk₁ ψ` composed with
`Δ[n].map θ.op` is the leg at `strArrowMk₁ φ`, when `φ = θ ≫ ψ`. -/
lemma saHom_w (s : Cn.{u} n m) (x : s.pt) {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1)
    (ψ : ⦋j⦌ ⟶ ⦋m⦌) (θ : (⦋i⦌ : SimplexCategory) ⟶ ⦋j⦌) (φ : ⦋i⦌ ⟶ ⦋m⦌) (hφ : φ = θ ≫ ψ) :
    (Δ[n] : SSet.{u}).map θ.op (s.π.app (strArrowMk₁ ψ hj) x)
      = s.π.app (strArrowMk₁ φ hi) x :=
  ConcreteCategory.congr_hom (s.w (saHom hi hj ψ θ φ hφ)) x

/-- The element of `⦋n⦌` assigned to the `j`-th vertex of `⦋m⦌` by a cone `s` at `x : s.pt`. -/
noncomputable def vval (s : Cn.{u} n m) (x : s.pt) (j : Fin (m + 1)) : Fin (n+1) :=
  (SSet.stdSimplex.objEquiv
    (s.π.app (strArrowMk₁ (SimplexCategory.const ⦋0⦌ ⦋m⦌ j)) x)).toOrderHom 0

/-- The two endpoints of the edge `mkOfLe i j h` agree with the vertex values at `i` and `j`. -/
lemma edge_endpoint (s : Cn.{u} n m) (x : s.pt) (i j : Fin (m + 1)) (h : i ≤ j) (k : Fin 2) :
    (SSet.stdSimplex.objEquiv (s.π.app (strArrowMk₁ (mkOfLe i j h)) x)).toOrderHom k
      = vval s x ((mkOfLe i j h).toOrderHom k) := by
  have hfac : SimplexCategory.const ⦋0⦌ ⦋m⦌ ((mkOfLe i j h).toOrderHom k)
      = SimplexCategory.const ⦋0⦌ ⦋1⦌ k ≫ mkOfLe i j h :=
    (SimplexCategory.const_comp _ _ _).symm
  have hw := saHom_w s x (i := 0) (j := 1) (by omega) (by omega)
    (mkOfLe i j h) (SimplexCategory.const ⦋0⦌ ⦋1⦌ k)
    (SimplexCategory.const ⦋0⦌ ⦋m⦌ ((mkOfLe i j h).toOrderHom k)) hfac
  apply_fun SSet.stdSimplex.objEquiv at hw
  rw [objEquiv_map] at hw
  exact congrArg (·.toOrderHom 0) hw

/-- The edge `mkOfLe i j h : ⦋1⦌ ⟶ ⦋m⦌` sends the vertex `0` to `i`. -/
lemma mkOfLe_apply_zero (i j : Fin (m + 1)) (h : i ≤ j) : (mkOfLe i j h).toOrderHom 0 = i := by
  rw [mkOfLe, mkHom, Hom.toOrderHom_mk]
  rfl

/-- The edge `mkOfLe i j h : ⦋1⦌ ⟶ ⦋m⦌` sends the vertex `1` to `j`. -/
lemma mkOfLe_apply_one (i j : Fin (m + 1)) (h : i ≤ j) : (mkOfLe i j h).toOrderHom 1 = j := by
  rw [mkOfLe, mkHom, Hom.toOrderHom_mk]
  rfl

/-- The monotone map `⦋m⦌ → ⦋n⦌` given by the vertex values of a cone; it is monotone because the
edge value at a pair `i ≤ j` is an ordered pair with those two vertex values as endpoints. -/
noncomputable def liftHom (s : Cn.{u} n m) (x : s.pt) : Fin (m+1) →o Fin (n+1) where
  toFun := vval s x
  monotone' := by
    intro i j h
    have hmono :=
      (SSet.stdSimplex.objEquiv (s.π.app (strArrowMk₁ (mkOfLe i j h)) x)).toOrderHom.monotone
        (show (0:Fin 2) ≤ 1 by decide)
    rw [edge_endpoint s x i j h 0, edge_endpoint s x i j h 1, mkOfLe_apply_zero,
      mkOfLe_apply_one] at hmono
    exact hmono

/-- The `m`-simplex of `Δ[n]` reconstructed from the vertex values of a cone, as a morphism
`⦋m⦌ ⟶ ⦋n⦌` of `SimplexCategory`. -/
noncomputable def liftSimplex (s : Cn.{u} n m) (x : s.pt) : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (liftHom s x)

/-- The value of the reconstructed simplex at a vertex `j` of `⦋m⦌` is the vertex value
`vval s x j`. -/
@[simp] lemma liftSimplex_apply (s : Cn.{u} n m) (x : s.pt) (j : Fin (m + 1)) :
    (liftSimplex s x).toOrderHom j = vval s x j := rfl

/-- The reconstructed simplex restricts along an edge `φ : ⦋1⦌ ⟶ ⦋m⦌` to the cone's leg
at `φ`. -/
lemma fac_edge (s : Cn.{u} n m) (x : s.pt) (φ : (⦋1⦌ : SimplexCategory) ⟶ ⦋m⦌) :
    SSet.stdSimplex.objEquiv (s.π.app (strArrowMk₁ φ) x) = φ ≫ liftSimplex s x := by
  obtain ⟨i, j, hij, rfl⟩ : ∃ i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by decide),
      Hom.ext_one_left _ _ rfl rfl⟩
  refine Hom.ext_one_left _ _ ?_ ?_
  · exact (edge_endpoint s x i j hij 0).trans rfl
  · exact (edge_endpoint s x i j hij 1).trans rfl

/-- The reconstructed simplex restricts along a vertex `φ : ⦋0⦌ ⟶ ⦋m⦌` to the cone's leg
at `φ`. -/
lemma fac_vertex (s : Cn.{u} n m) (x : s.pt) (φ : (⦋0⦌ : SimplexCategory) ⟶ ⦋m⦌) :
    SSet.stdSimplex.objEquiv (s.π.app (strArrowMk₁ φ) x) = φ ≫ liftSimplex s x := by
  obtain ⟨a, rfl⟩ := exists_eq_const_of_zero φ
  exact Hom.ext_zero_left _ _

/-- The cone over the `1`-truncated structured-arrow diagram of `Δ[n]` at `⦋m⦌` with apex the
`m`-simplices of `Δ[n]` and leg `Δ[n].map j.hom` at `j`. -/
@[implicit_reducible, simps]
def canonCone (n m : ℕ) : Cn.{u} n m where
  pt := (Δ[n] : SSet.{u}) _⦋m⦌
  π :=
    { app j := (Δ[n] : SSet.{u}).map j.hom
      naturality j j' φ := by simp [← StructuredArrow.w φ] }

/-- The cone `canonCone n m` is a limit cone. -/
noncomputable def canonConeIsLimit (n m : ℕ) : IsLimit (canonCone.{u} n m) := by
  refine IsLimit.mk (fun s => ↾fun x => SSet.stdSimplex.objEquiv.symm (liftSimplex s x)) ?_ ?_
  · intro s j
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨k, rfl⟩ : ∃ k, ⦋k⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    rw [SSet.stdSimplex.map_objEquiv_symm]
    apply SSet.stdSimplex.objEquiv.symm_apply_eq.mpr
    interval_cases k
    · exact (fac_vertex s x f).symm
    · exact (fac_edge s x f).symm
  · intro s f hf
    ext x
    refine SSet.stdSimplex.objEquiv.eq_symm_apply.mpr ?_
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    rw [liftSimplex_apply]
    have hfi := ConcreteCategory.congr_hom (hf (strArrowMk₁ (SimplexCategory.const ⦋0⦌ ⦋m⦌ i))) x
    apply_fun SSet.stdSimplex.objEquiv at hfi
    rw [canonCone_π_app, ConcreteCategory.comp_apply, StructuredArrow.mk_hom_eq_self,
      objEquiv_map] at hfi
    rw [TypeCat.Fun.toFun_apply, vval, ← hfi]
    simp

end isPointwiseRightKanExtensionAt

open isPointwiseRightKanExtensionAt in
/-- The canonical cone exhibiting `Δ[n]` at level `m` as a limit over the `1`-truncated
structured-arrow diagram is a limit cone: an `m`-simplex of `Δ[n]` is uniquely determined by, and
reconstructible from, its restrictions to the vertices `⦋0⦌` and the edges `⦋1⦌` of `⦋m⦌`,
compatibly along the structured-arrow maps. -/
noncomputable def isPointwiseRightKanExtensionAt.{u} (n : ℕ) (m : ℕ) :
    (SSet.Truncated.rightExtensionInclusion (Δ[n] : SSet.{u}) 1).IsPointwiseRightKanExtensionAt
      ⟨⦋m⦌⟩ := by
  rw [RightExtension.IsPointwiseRightKanExtensionAt, SSet.Truncated.rightExtensionInclusion]
  exact (canonConeIsLimit n m).ofIsoLimit (Cone.ext (Iso.refl _) fun _ => by simp)

/-- The right extension `rightExtensionInclusion Δ[n] 1` is a pointwise right Kan extension. -/
noncomputable def isPointwiseRightKanExtension.{u} (n : ℕ) :
    (SSet.Truncated.rightExtensionInclusion (Δ[n] : SSet.{u}) 1).IsPointwiseRightKanExtension :=
  fun Δ => isPointwiseRightKanExtensionAt n Δ.unop.len

/-- `Δ[n]` is the right Kan extension of its `1`-truncation along `(inclusion 1).op`, via the
identity transformation. -/
theorem isRightKanExtension.{u} (n : ℕ) :
    (Δ[n] : SSet.{u}).IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ Δ[n])) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension n)

/-- `Δ[n]` is `1`-coskeletal. -/
theorem isCoskeletal.{u} (n : ℕ) : SimplicialObject.IsCoskeletal (Δ[n] : SSet.{u}) 1 where
  isRightKanExtension := isRightKanExtension n

end stdSimplex

/-- **Stacks 018E**.
For every `n`, the canonical map `c_{Δ[n]} : Δ[n] ⟶ cosk_1 sk_1 Δ[n]`, the unit of the adjunction
`sk_1 ⊣ cosk_1` at the standard `n`-simplex, is an isomorphism of simplicial sets. -/
@[stacks 018E]
theorem canonicalMap_stdSimplex_isIso (n : ℕ) :
    IsIso (cosk1Unit (Δ[n])) :=
  (SimplicialObject.isCoskeletal_iff_isIso _ 1).mp (stdSimplex.isCoskeletal n)

end SSet
