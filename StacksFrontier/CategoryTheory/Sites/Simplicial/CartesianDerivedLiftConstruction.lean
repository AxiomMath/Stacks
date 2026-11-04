module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLiftFace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedMapVanishing
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionAugmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionFaceRecognition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionAugmentationTower
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionTermDiff

/-!
# The degree-zero lift of Stacks 0D9K

Let `S` be a simplicial-site situation (Stacks 09WE), let `K` and `K'` be objects of the
unbounded derived category of abelian sheaves on its total site with `K` cartesian, and let `f`
be a morphism of the associated simplicial systems of Stacks 0D9H. The proof of Stacks 0D9K has
two halves; the second, that such a morphism is determined by its degree-zero component, is
`CategoryTheory.SimplicialSiteSituation.exists_hom_iff_exists_hom_zero`. **This file proves the
first**: hypothesis (2) of Stacks 0D9K produces a morphism `K ⟶ K'` whose derived restriction to
simplicial degree zero is the given component.

The source's argument runs through the Postnikov system of Stacks 0D9I for `- ⊗^L_ℤ K`. Its terms
are `Xₙ = g_{n!}ℤ ⊗^L_ℤ K`, which cartesianness and Stacks 0D9E (1) identify with `g_{n!}Kₙ`
(`integerResolutionTensorTermIso`), and `K` is the derived colimit of the system `Yₙ[n]`
(Stacks 0D9I (2)). The degree-zero component `f₀ : K₀ ⟶ K'₀` has a transpose
`X₀ = g_{0!}K₀ ⟶ K'` along `g_{0!} ⊣ g_0^{-1}` — that is `degreeZeroAdjunct` — and the induction
up the tower, `StacksDraft.BrutalPostnikov.exists_hom_of_termDiff_comp_eq_zero`, extends it over
the colimit as soon as two things are known: that it is annihilated by the differential
`X₁ ⟶ X₀` of the system, and that `Hom(Xᵢ₊₁[i], K') = 0` for `i > 0`. The second is hypothesis
(2) of Stacks 0D9K, through `hom_integerResolutionTensorTerm_eq_zero`.

The first is the source's first "computation (omitted)". The differential of the system in degree
zero is the difference of the two faces `⦋0⦌ ⟶ ⦋1⦌`
(`integerResolutionTermIso_inv_comp_termDiff_zero`), the face identity
`integerProjection_comp_derivedTensorFace_eq_realizationTermMap` turns each face into the
corresponding transition of the realization of Stacks 0D9L, and
`realizationTermMap_comp_homEquiv_symm` says that the transposes of the components of `f` are
compatible with those transitions — so the composite through either face is the same transpose in
degree one and the difference vanishes.

What is left is to read the conclusion of the tower argument, which is an identity against the
degree-zero coprojection of the derived colimit, as a statement about the counit. That is the
source's second "computation (omitted)", and it is where two previously separate identities meet:
`ιStupidTrunc_comp_integerResolutionDerivedIso` computes the coprojection, before tensoring with
`K`, as the bottom of the Postnikov tower followed by the augmentation `g_{0!}ℤ ⟶ ℤ`, and
`integerProjection_comp_derivedTensorAugmentation` says that the comparison of Stacks 0D9E in
degree zero followed by the derived tensor product with that augmentation is the counit at `K`.
Together they give `coprojectionZero_eq`, and since the bottom of the tower is invertible — the
integral resolution is concentrated in degrees `≤ 0`, so the projection `Y₀ ⟶ X₀` is an
isomorphism — the identity may be cancelled down to `ε_K ≫ γ = f₀`-transposed, which is exactly
`g_0^{-1}γ = f₀` by the triangle identity.

## Main results

* `CategoryTheory.SimplicialSiteSituation.integerResolutionTensorTermIso_inv_comp_termDiff`: the
  differential `X₁ ⟶ X₀` of the Postnikov system, read through the identifications
  `Xᵢ = g_{i!}Kᵢ`, is the difference of the two transitions of the realization at the two faces
  `⦋0⦌ ⟶ ⦋1⦌`.
* `CategoryTheory.SimplicialSiteSituation.termDiff_comp_degreeZeroAdjunct_eq_zero`: **the first
  of the two computations the source omits** — the composite `X₁ ⟶ X₀ ⟶ K'` vanishes.
* `CategoryTheory.SimplicialSiteSituation.coprojectionZero_eq`: **the second** — the degree-zero
  coprojection of the derived colimit of Stacks 0D9I is the bottom of the Postnikov tower
  followed by the counit of `g_{0!} ⊣ g_0^{-1}` at `K`.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponent_zero_eq`: **the first half
  of Stacks 0D9K** — hypothesis (2) produces a morphism `K ⟶ K'` agreeing with the given one in
  simplicial degree zero.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.DerivedTensor.AbelianSheaves
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.SimplicialSiteSituation.realizationTerm

/-! ### Rearrangements over abstract morphisms

Every step below that would otherwise be a rewrite inside a composite of the derived category of
abelian sheaves is extracted here, over abstract morphisms, and applied as a term. The reason is
the one recorded in `IntegerResolutionAugmentationTower`: `integerResolutionComplex` and the
terms of the Postnikov tower are plain definitions, so a goal naming two of their spellings is
not type-correct at `implicit` transparency and a rewrite in it stops without saying so. -/

/-- A difference of two morphisms, each of which composes with a common prefix to a factorisation
through one map, composed on the right. -/
private theorem sub_chain_of_comp {D : Type*} [Category* D] [Preadditive D] {V W X Y Z : D}
    (p : V ⟶ W) (a b : W ⟶ X) (c : X ⟶ Y) (r s : V ⟶ Z) (t : Z ⟶ X)
    (ha : p ≫ a = r ≫ t) (hb : p ≫ b = s ≫ t) :
    p ≫ (a - b) ≫ c = (r - s) ≫ t ≫ c := by
  have ha' : p ≫ a ≫ c = r ≫ t ≫ c := by rw [← Category.assoc, ha, Category.assoc]
  have hb' : p ≫ b ≫ c = s ≫ t ≫ c := by rw [← Category.assoc, hb, Category.assoc]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, ha', hb']

/-- A composite that factors as a difference followed by the inverse of an isomorphism vanishes
against that isomorphism followed by a map which the two terms of the difference equalise. -/
private theorem sub_cancel_eq_zero {D : Type*} [Category* D] [Preadditive D]
    {Z₁ X₁ X₀ Z₀ Y : D} (u : Z₁ ⟶ X₁) (d : X₁ ⟶ X₀) (r s : Z₁ ⟶ Z₀) (e : X₀ ≅ Z₀)
    (t : Z₀ ⟶ Y) (w : Z₁ ⟶ Y) (hkey : u ≫ d = (r - s) ≫ e.inv)
    (hr : r ≫ t = w) (hs : s ≫ t = w) : u ≫ d ≫ e.hom ≫ t = 0 := by
  rw [← Category.assoc, hkey, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sub_comp,
    hr, hs, sub_self]

/-- Two composites identified at their head and at their tail are identified. -/
private theorem chain_four {D : Type*} [Category* D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : D}
    (x : A₀ ⟶ A₁) (y : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (a : A₀ ⟶ A₄) (b : A₄ ⟶ A₅) (c : A₅ ⟶ A₆)
    (d : A₆ ⟶ A₂) (m : A₅ ⟶ A₇) (n : A₇ ⟶ A₃)
    (h₁ : x ≫ y = a ≫ b ≫ c ≫ d) (h₂ : c ≫ d ≫ g = m ≫ n) :
    (x ≫ y) ≫ g = a ≫ b ≫ m ≫ n := by
  rw [h₁]
  simp only [Category.assoc]
  rw [h₂]

/-- An invertible three-fold prefix is cancelled. The invertibility is taken after the equation
so that the three morphisms are known by the time the instances are needed. -/
private theorem cancel_three_prefix {D : Type*} [Category* D] {A₀ A₁ A₂ A₃ A₄ A₅ : D}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {u : A₃ ⟶ A₄} {w : A₄ ⟶ A₅} {v : A₃ ⟶ A₅}
    (h : (a ≫ b ≫ c ≫ u) ≫ w = a ≫ b ≫ c ≫ v)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) : u ≫ w = v := by
  have := ha; have := hb; have := hc
  simp only [Category.assoc] at h
  exact (cancel_epi c).1 ((cancel_epi b).1 ((cancel_epi a).1 h))

/-- A functor applied to a four-fold composite. -/
private theorem map_comp_four {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B X Y Z : C} (a : A ⟶ B) (b : B ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) :
    F.map (a ≫ b ≫ c ≫ d) = F.map a ≫ F.map b ≫ F.map c ≫ F.map d := by
  simp only [F.map_comp]

/-- An isomorphism cancelled against its inverse in the middle of a composite. -/
private theorem cancel_middle {D : Type*} [Category* D] {A B C E : D} (p : A ⟶ B)
    (q : B ⟶ C) (q' : C ⟶ B) (x : B ⟶ E) (hq : q ≫ q' = 𝟙 B) :
    (p ≫ q) ≫ q' ≫ x = p ≫ x := by
  rw [Category.assoc, ← Category.assoc q, hq, Category.id_comp]

/-- **The transpose of the counit followed by a morphism is the right adjoint of that
morphism**: the triangle identity. -/
private theorem homEquiv_counit_comp {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {X Y : D} (γ : X ⟶ Y) :
    adj.homEquiv (G.obj X) Y (adj.counit.app X ≫ γ) = G.map γ := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    adj.right_triangle_components, Category.id_comp]

/-- The vanishing of the maps out of a shifted object transported along an equality of
shifts. -/
private theorem eq_zero_of_shift_eq {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
    {X Y : D} {a a' : ℤ} (haa' : a = a') (h : ∀ u : X⟦a⟧ ⟶ Y, u = 0) (u : X⟦a'⟧ ⟶ Y) :
    u = 0 := by
  subst haa'; exact h u

/-! ### The transpose of the degree-zero component, and the vanishing it satisfies -/

variable (S : SimplicialSiteSituation.{u})
  (K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u}))

/-- **The map `X₀ ⟶ K'` the source of Stacks 0D9K builds out of the degree-zero component of the
given morphism of simplicial systems**: the transpose of that component along
`g_{0!} ⊣ g_0^{-1}`, read on the term `X₀` of the Postnikov system of Stacks 0D9I through the
identification `X₀ = g_{0!}K₀` of Stacks 0D9E (1). -/
abbrev degreeZeroAdjunct (hK : S.IsCartesianDerived K)
    (f : (S.associatedDerivedSystem K).Hom (S.associatedDerivedSystem K')) :
    integerResolutionTensorTerm S K 0 ⟶ K' :=
  (integerResolutionTensorTermIso S K hK 0).hom ≫
    ((S.componentLowerShriekDerivedAdjunction ⦋0⦌).homEquiv
      ((derivedComponent S ⦋0⦌).obj K) K').symm (f.app ⦋0⦌)

/-- **The differential `X₁ ⟶ X₀` of the Postnikov system of Stacks 0D9I, read through the
identifications `Xᵢ = g_{i!}Kᵢ` of Stacks 0D9E (1), is the difference of the two transitions of
the realization of Stacks 0D9L at the two faces `⦋0⦌ ⟶ ⦋1⦌`.** The differential is the
alternating difference of the two faces
(`integerResolutionTermIso_inv_comp_termDiff_zero`), and the face identity of Stacks 0D9K
(`integerProjection_comp_derivedTensorFace_eq_realizationTermMap`) turns the derived tensor
product with each face into the corresponding transition. -/
theorem integerResolutionTensorTermIso_inv_comp_termDiff (hK : S.IsCartesianDerived K) :
    (integerResolutionTensorTermIso S K hK 1).inv ≫
        (integerDerivedTensorRight S K).map (termDiff (integerResolutionComplex S) 0) =
      (realizationTermMap (S.associatedDerivedSystem K)
            (S.associatedDerivedSystem_cartesian K hK) (SimplexCategory.δ (0 : Fin 2)) -
          realizationTermMap (S.associatedDerivedSystem K)
            (S.associatedDerivedSystem_cartesian K hK) (SimplexCategory.δ (1 : Fin 2))) ≫
        (integerResolutionTensorTermIso S K hK 0).inv := by
  have hd : (integerResolutionTermIso S 1).inv ≫ termDiff (integerResolutionComplex S) 0 =
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
          (integerFace S (SimplexCategory.δ (0 : Fin 2)) -
            integerFace S (SimplexCategory.δ (1 : Fin 2))) ≫
        (integerResolutionTermIso S 0).inv :=
    (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
      (integerResolutionTermIso_inv_comp_termDiff_zero S))
  have h₁ : (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 1).inv) ≫
        (integerDerivedTensorRight S K).map (termDiff (integerResolutionComplex S) 0) =
      ((integerDerivedTensorRight S K).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S (SimplexCategory.δ (0 : Fin 2)))) -
          (integerDerivedTensorRight S K).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S (SimplexCategory.δ (1 : Fin 2))))) ≫
        (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 0).inv) := by
    rw [← Functor.map_comp, hd, Functor.map_comp]
    simp only [Functor.map_sub]
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans
    (congrArg (fun k => S.integerProjection K ⦋1⦌ ≫ k) h₁) ?_)
  exact sub_chain_of_comp _ _ _ _ _ _ _
    (integerProjection_comp_derivedTensorFace_eq_realizationTermMap S K hK
      (SimplexCategory.δ (0 : Fin 2)))
    (integerProjection_comp_derivedTensorFace_eq_realizationTermMap S K hK
      (SimplexCategory.δ (1 : Fin 2)))

/-- **The first of the two computations the proof of Stacks 0D9K omits**: the composite
`X₁ ⟶ X₀ ⟶ K'` through the differential of the Postnikov system of Stacks 0D9I vanishes, for the
map `X₀ ⟶ K'` built from the degree-zero component of the given morphism of simplicial systems.

The differential is the difference of the two faces `⦋0⦌ ⟶ ⦋1⦌`, so after the identifications
`Xᵢ = g_{i!}Kᵢ` the composite is the difference of the two composites through the transitions of
the realization; and the transposes of the components of a morphism of simplicial systems are
compatible with those transitions (`realizationTermMap_comp_homEquiv_symm`), so both are the
transpose in degree one and the difference is zero. -/
theorem termDiff_comp_degreeZeroAdjunct_eq_zero (hK : S.IsCartesianDerived K)
    (f : (S.associatedDerivedSystem K).Hom (S.associatedDerivedSystem K')) :
    (integerDerivedTensorRight S K).map (termDiff (integerResolutionComplex S) 0) ≫
      degreeZeroAdjunct S K K' hK f = 0 := by
  refine zero_of_epi_comp (integerResolutionTensorTermIso S K hK 1).inv ?_
  exact sub_cancel_eq_zero _ _ _ _ _ _ _
    (integerResolutionTensorTermIso_inv_comp_termDiff S K hK)
    (realizationTermMap_comp_homEquiv_symm (S.associatedDerivedSystem_cartesian K hK) f
      (SimplexCategory.δ (0 : Fin 2)))
    (realizationTermMap_comp_homEquiv_symm (S.associatedDerivedSystem_cartesian K hK) f
      (SimplexCategory.δ (1 : Fin 2)))

/-! ### The degree-zero coprojection of the derived colimit -/

/-- **The identification of `X₀` with `g_{0!}K₀`, followed by the counit, is the derived tensor
product of `K` with the augmentation `g_{0!}ℤ ⟶ ℤ` read through `ℤ ⊗^L_ℤ K ≅ K`.** Cancelling
the identification against its inverse leaves exactly
`integerProjection_comp_derivedTensorAugmentation`, the second of the two computations the source
omits. -/
theorem derivedTensorAugmentation_eq_counit (hK : S.IsCartesianDerived K) :
    (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 0).hom) ≫
        (integerDerivedTensorRight S K).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerAugmentation S)) ≫
          (constantSheafLeftUnitIso S.totalTopology K).hom =
      (integerResolutionTensorTermIso S K hK 0).hom ≫
        (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit.app K := by
  have hq : (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 0).inv) ≫
      (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 0).hom) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  refine (Iso.inv_comp_eq _).1 (Eq.trans
    (cancel_middle (S.integerProjection K ⦋0⦌) _ _ _ hq) ?_)
  exact integerProjection_comp_derivedTensorAugmentation S K

/-- **The degree-zero coprojection of the derived colimit of Stacks 0D9I is the bottom of the
Postnikov tower followed by the counit of `g_{0!} ⊣ g_0^{-1}` at `K`.** The coprojection is the
image under `- ⊗^L_ℤ K` of the inclusion `σ^{≥0}L ⟶ L` of the bottom brutal truncation of the
integral resolution, followed by `ℤ ⊗^L_ℤ K ≅ K`;
`ιStupidTrunc_comp_integerResolutionDerivedIso` computes that, before tensoring with `K`, as the
bottom of the tower followed by the augmentation, and `derivedTensorAugmentation_eq_counit` reads
the augmentation as the counit. -/
theorem coprojectionZero_eq (hK : S.IsCartesianDerived K) :
    (integerDerivedTensorRight S K).map (DerivedCategory.Q.map
          (HomologicalComplex.ιStupidTrunc (integerResolutionComplex S)
            (ComplexShape.embeddingUpIntGE (-((0 : ℕ) : ℤ))))) ≫
        (derivedTensorIntegerResolutionIso S K).hom =
      (integerDerivedTensorRight S K).map
          (totAtTowerIso (integerResolutionComplex S) (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        (integerDerivedTensorRight S K).map (totProj (integerResolutionComplex S) 0) ≫
          (integerResolutionTensorTermIso S K hK 0).hom ≫
            (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit.app K := by
  have h₁ : (integerDerivedTensorRight S K).map (DerivedCategory.Q.map
            (HomologicalComplex.ιStupidTrunc (integerResolutionComplex S)
              (ComplexShape.embeddingUpIntGE (-((0 : ℕ) : ℤ))))) ≫
        (integerDerivedTensorRight S K).map ((integerResolutionDerivedIso S).hom) =
      (integerDerivedTensorRight S K).map
          (totAtTowerIso (integerResolutionComplex S) (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        (integerDerivedTensorRight S K).map (totProj (integerResolutionComplex S) 0) ≫
          (integerDerivedTensorRight S K).map ((integerResolutionTermIso S 0).hom) ≫
            (integerDerivedTensorRight S K).map
              ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                (integerAugmentation S)) :=
    (((integerDerivedTensorRight S K).map_comp _ _).symm.trans
      (congrArg (integerDerivedTensorRight S K).map
        (ιStupidTrunc_comp_integerResolutionDerivedIso S))).trans
      (map_comp_four (integerDerivedTensorRight S K) _ _ _ _)
  exact (Category.assoc _ _ _).symm.trans
    (chain_four _ _ _ _ _ _ _ _ _ h₁ (derivedTensorAugmentation_eq_counit S K hK))

/-! ### The first half of Stacks 0D9K -/

/-- **The first half of the proof of Stacks 0D9K: hypothesis (2) produces a morphism `K ⟶ K'`
agreeing with the given one in simplicial degree zero.** For a cartesian `K` and a morphism `f`
of the associated simplicial systems of Stacks 0D9H, if `Hom(Kᵢ[i - 1], K'ᵢ) = 0` for every
`i > 1` then there is a `γ : K ⟶ K'` whose derived restriction to simplicial degree zero is
`f₀`.

The proof is the source's. The Postnikov system of Stacks 0D9I presents `K` as the derived
colimit of the system `Yₙ[n]`, with terms `Xₙ = g_{n!}Kₙ` by Stacks 0D9E (1); the transpose
`X₀ ⟶ K'` of `f₀` is annihilated by the differential `X₁ ⟶ X₀`
(`termDiff_comp_degreeZeroAdjunct_eq_zero`), hypothesis (2) kills the obstruction to extending it
up the tower (`hom_integerResolutionTensorTerm_eq_zero`), and
`StacksDraft.BrutalPostnikov.exists_hom_of_termDiff_comp_eq_zero` produces the extension `γ`
over the colimit. Reading its defining identity through `coprojectionZero_eq` and cancelling the
invertible bottom of the tower leaves `ε_K ≫ γ` equal to the transpose of `f₀`, hence
`g_0^{-1}γ = f₀` by the triangle identity. -/
theorem exists_hom_derivedComponent_zero_eq (hK : S.IsCartesianDerived K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology ⦋i⦌) Ab.{u}))
            ((i : ℤ) - 1)).obj ((derivedComponent S ⦋i⦌).obj K) ⟶
          (derivedComponent S ⦋i⦌).obj K', g = 0)
    (f : (S.associatedDerivedSystem K).Hom (S.associatedDerivedSystem K')) :
    ∃ γ : K ⟶ K', (derivedComponent S ⦋0⦌).map γ = f.app ⦋0⦌ := by
  have hvanish : ∀ i : ℕ, 0 < i →
      ∀ g : ((integerDerivedTensorRight S K).obj
          (term (integerResolutionComplex S) (i + 1)))⟦(i : ℤ)⟧ ⟶ K', g = 0 := by
    intro i _
    refine hom_integerResolutionTensorTerm_eq_zero S K K' hK (i + 1) (i : ℤ) (fun g => ?_)
    exact eq_zero_of_shift_eq (show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by push_cast; ring)
      (hHom (i + 1) (by omega)) g
  obtain ⟨γ, hγ⟩ := exists_hom_of_termDiff_comp_eq_zero (integerResolutionComplex S)
    (integerDerivedTensorRight S K)
    (isHomotopyColimitWith_derivedTensorIntegerResolutionSystem S K)
    (degreeZeroAdjunct S K K' hK f)
    (termDiff_comp_degreeZeroAdjunct_eq_zero S K K' hK f) hvanish
  refine ⟨γ, ?_⟩
  have hcounit : (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit.app K ≫ γ =
      ((S.componentLowerShriekDerivedAdjunction ⦋0⦌).homEquiv
        ((derivedComponent S ⦋0⦌).obj K) K').symm (f.app ⦋0⦌) :=
    cancel_three_prefix
      ((congrArg (fun k => k ≫ γ) (coprojectionZero_eq S K hK)).symm.trans hγ) inferInstance
      (Functor.map_isIso (integerDerivedTensorRight S K)
        (totProj (integerResolutionComplex S) 0)) inferInstance
  exact (homEquiv_counit_comp (S.componentLowerShriekDerivedAdjunction ⦋0⦌) γ).symm.trans
    ((congrArg ((S.componentLowerShriekDerivedAdjunction ⦋0⦌).homEquiv
        ((derivedComponent S ⦋0⦌).obj K) K') hcounit).trans
      (Equiv.apply_symm_apply _ _))

end CategoryTheory.SimplicialSiteSituation

end
