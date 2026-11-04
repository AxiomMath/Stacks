module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.FiniteLevelCofinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FiniteLevelMatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechSystem07Q9

/-!
# [Stacks, Tag 07L4] on the finite levels

Fix an affine crystalline situation `(A, I, γ) → C` and a surjective polynomial presentation
`P → C`.  [Stacks, Tag 07L4] says that the completed divided power envelope `D(n)` of the
`(n + 1)`-fold tensor power of the presentation is the coproduct of `n + 1` copies of `D = D(0)` in
`Cris^∧(C/A)`, the coprojections being induced by the vertices `⦋0⦌ ⟶ ⦋n⦌`.

This file reads that statement on the finite levels `D(n)/(p)^{N + e}` of
`Crystalline.affineLevelSystem`, which are objects of the little affine crystalline category
`Cris(C/A)`: a family of `n + 1` morphisms out of the level `e` of `D(0)` into an object `Y` of
`Cris(C/A)` is induced, after passing to a deeper level `e'`, by a morphism out of the level `e'`
of `D(n)`; and a morphism out of a level of `D(n)` is determined by its composites with the vertex
maps.

Across the equivalence `wholeSiteEquivLittleAffine` the same two statements hold for the system
`wholeSpaceSystemOf` of a global situation with `X` and `S` affine, on the thickenings of the
whole of `X`.

## Main results

* `exists_affineLevelSystem_desc` and `affineLevelSystem_hom_ext` — the two halves on the little
  affine crystalline category.
* `exists_wholeSpaceSystemOf_desc` and `wholeSpaceSystemOf_hom_ext` — the two halves on the
  chaotic subsite of `Cris(X/S)`, for `X` and `S` affine.

## References

* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

/-! ### The little affine crystalline category -/

section Affine

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- The projection of the completed envelope `D(n)` onto its finite level `D(n)/(p)^{N + e}`,
read as a morphism of `Cris^∧(C/A)`. -/
abbrev envelopeLevelProjection (n e : ℕ) :
    (tensorPowerEnvelopeThickening s g hg n).thickening ⟶
      (crystallineToCompleted s).obj (((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e)) :=
  finiteLevelProjection (uniformLevelSystem _) e

/-- The projections onto the finite levels are natural in the cosimplicial direction. -/
@[reassoc]
theorem envelopeCosimplicial_map_comp_envelopeLevelProjection {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌)
    (e : ℕ) :
    (envelopeCosimplicial s g hg).map φ ≫ envelopeLevelProjection s g hg m e =
      envelopeLevelProjection s g hg n e ≫
        (crystallineToCompleted s).map (((affineLevelSystem s g hg).map φ).app (op e)) := by
  apply CompletedCrystallineThickening.Hom.ext
  rfl

/-- The projections onto the finite levels are compatible with the level drops. -/
@[reassoc]
theorem envelopeLevelProjection_comp_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    envelopeLevelProjection s g hg n e' ≫
        (crystallineToCompleted s).map (((affineLevelSystem s g hg).obj ⦋n⦌).map (homOfLE h).op) =
      envelopeLevelProjection s g hg n e := by
  apply CompletedCrystallineThickening.Hom.ext
  rfl

/-- The `j`-th coprojection `D ⟶ D(n)` is the coprojection `D ⟶ D(0)` followed by the map of the
`j`-th vertex. -/
theorem coprojection_eq_coprojection_comp_vertex (n : ℕ) (j : Fin (n + 1)) :
    completedEnvelopeCoprojection s g hg n j =
      completedEnvelopeCoprojection s g hg 0 0 ≫
        (envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) :=
  (envelopeCosimplicial_coprojection_comp_map s g hg (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) 0).symm

/-- The `j`-th coprojection `D ⟶ D(n)` followed by a morphism out of `D(n)`, rewritten through
the coprojection `D ⟶ D(0)` and the map of the `j`-th vertex. -/
theorem coprojection_comp_eq (n : ℕ) (j : Fin (n + 1))
    {B : CompletedCrystallineThickening.{u, u, u} s}
    (x : (tensorPowerEnvelopeThickening s g hg n).thickening ⟶ B) :
    completedEnvelopeCoprojection s g hg n j ≫ x =
      completedEnvelopeCoprojection s g hg 0 0 ≫
        (envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫ x :=
  (congrArg (· ≫ x) (coprojection_eq_coprojection_comp_vertex s g hg n j)).trans
    (Category.assoc _ _ _)

/-- A morphism out of the completed envelope `D(0)` is determined by its composite with the
coprojection `D ⟶ D(0)`. -/
theorem envelopeZero_hom_ext {B : CompletedCrystallineThickening.{u, u, u} s}
    (a b : (tensorPowerEnvelopeThickening s g hg 0).thickening ⟶ B)
    (hab : completedEnvelopeCoprojection s g hg 0 0 ≫ a =
      completedEnvelopeCoprojection s g hg 0 0 ≫ b) : a = b :=
  envelopeCoproduct_hom_ext s g hg a b fun j ↦ by rwa [Fin.fin_one_eq_zero j]

/-- The `j`-th coprojection into `D(n)`, followed by the projection onto a finite level and a
morphism out of it, is the coprojection into `D(0)` followed by the projection onto the same level
and the composite of the `j`-th vertex map with the morphism. -/
theorem coprojection_comp_envelopeLevelProjection_comp {Y :
      _root_.Crystalline.CrystallineThickening.{u, u, u} s} (n e : ℕ) (j : Fin (n + 1))
    (χ : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) ⟶ Y) :
    completedEnvelopeCoprojection s g hg n j ≫ envelopeLevelProjection s g hg n e ≫
        (crystallineToCompleted s).map χ =
      completedEnvelopeCoprojection s g hg 0 0 ≫ envelopeLevelProjection s g hg 0 e ≫
        (crystallineToCompleted s).map
          (((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)).app (op e) ≫ χ) :=
  calc _ = completedEnvelopeCoprojection s g hg 0 0 ≫
        (envelopeCosimplicial s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫
          envelopeLevelProjection s g hg n e ≫ (crystallineToCompleted s).map χ :=
        coprojection_comp_eq s g hg n j _
    _ = completedEnvelopeCoprojection s g hg 0 0 ≫ envelopeLevelProjection s g hg 0 e ≫
        (crystallineToCompleted s).map
          (((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)).app (op e)) ≫
        (crystallineToCompleted s).map χ :=
        congrArg (completedEnvelopeCoprojection s g hg 0 0 ≫ ·)
          (envelopeCosimplicial_map_comp_envelopeLevelProjection_assoc s g hg _ e _)
    _ = _ := by rw [Functor.map_comp]

/-- Two morphisms out of a finite level of `D(n)` are equal if their composites with the projection
and every coprojection agree. -/
private theorem eq_of_coprojection_comp_envelopeLevelProjection_comp_eq
    {Y : _root_.Crystalline.CrystallineThickening.{u, u, u} s} {n e : ℕ}
    (χ χ' : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) ⟶ Y)
    (h : ∀ j : Fin (n + 1),
      completedEnvelopeCoprojection s g hg n j ≫ envelopeLevelProjection s g hg n e ≫
          (crystallineToCompleted s).map χ =
        completedEnvelopeCoprojection s g hg n j ≫ envelopeLevelProjection s g hg n e ≫
          (crystallineToCompleted s).map χ') : χ = χ' := by
  have := crystallineToCompleted_faithful.{u, u, u} s
  have : Epi (envelopeLevelProjection s g hg n e) := finiteLevelProjection_epi _ e
  exact (crystallineToCompleted s).map_injective
    ((cancel_epi (envelopeLevelProjection s g hg n e)).mp (envelopeCoproduct_hom_ext s g hg _ _ h))

/-- The projection onto a deeper level, followed by a morphism that factors through the level
drop, is the projection onto the shallower level followed by the remaining factor. -/
private theorem envelopeLevelProjection_comp_map_comp {Y :
      _root_.Crystalline.CrystallineThickening.{u, u, u} s} (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (χ : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) ⟶ Y) :
    envelopeLevelProjection s g hg n e' ≫ (crystallineToCompleted s).map
        (((affineLevelSystem s g hg).obj ⦋n⦌).map (homOfLE h).op ≫ χ) =
      envelopeLevelProjection s g hg n e ≫ (crystallineToCompleted s).map χ := by
  rw [Functor.map_comp, envelopeLevelProjection_comp_map_assoc]

/-- **A morphism out of a finite level of `D(n)` is determined by its composites with the vertex
maps**, for a target in `Cris(C/A)`.  This is the uniqueness half of [Stacks, Tag 07L4], read on
the finite levels. -/
theorem affineLevelSystem_hom_ext {Y : _root_.Crystalline.CrystallineThickening.{u, u, u} s}
    {n e : ℕ} (χ χ' : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) ⟶ Y)
    (h : ∀ i : Fin (n + 1),
      ((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e) ≫ χ =
        ((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e) ≫ χ') :
    χ = χ' := by
  refine eq_of_coprojection_comp_envelopeLevelProjection_comp_eq s g hg χ χ' fun j ↦ ?_
  refine (coprojection_comp_envelopeLevelProjection_comp s g hg n e j χ).trans ?_
  refine Eq.trans ?_ (coprojection_comp_envelopeLevelProjection_comp s g hg n e j χ').symm
  rw [h j]

/-- **A family of morphisms out of a finite level of `D(0)` is induced, at a deeper level, by a
morphism out of the corresponding level of `D(n)`**, for a target in `Cris(C/A)`. This is the
existence half of [Stacks, Tag 07L4], read on the finite levels. -/
theorem exists_affineLevelSystem_desc (Y : _root_.Crystalline.CrystallineThickening.{u, u, u} s)
    (n e : ℕ) (ψ : Fin (n + 1) → (((affineLevelSystem s g hg).obj ⦋0⦌).obj (op e) ⟶ Y)) :
    ∃ (e' : ℕ) (hee' : e ≤ e') (χ : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e') ⟶ Y),
      ∀ i : Fin (n + 1),
        ((affineLevelSystem s g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e') ≫ χ =
          ((affineLevelSystem s g hg).obj ⦋0⦌).map (homOfLE hee').op ≫ ψ i := by
  have := crystallineToCompleted_faithful.{u, u, u} s
  let k : Fin (n + 1) → ((completedEnvelopeThickening s g hg).thickening ⟶
      (crystallineToCompleted s).obj Y) := fun j ↦
    completedEnvelopeCoprojection s g hg 0 0 ≫ envelopeLevelProjection s g hg 0 e ≫
      (crystallineToCompleted s).map (ψ j)
  let m := Cofan.IsColimit.desc (envelopeCoproductIsColimit s g hg n) k
  obtain ⟨e₁, χ₀, hχ₀⟩ := finiteLevel_factor_morphism
    (uniformLevelSystem (tensorPowerEnvelopeThickening s g hg n).thickening) m
  have h₁ : e₁ ≤ max e e₁ := le_max_right _ _
  let χ : ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op (max e e₁)) ⟶ Y :=
    ((affineLevelSystem s g hg).obj ⦋n⦌).map (homOfLE h₁).op ≫ χ₀
  have hχ : envelopeLevelProjection s g hg n (max e e₁) ≫ (crystallineToCompleted s).map χ = m :=
    (envelopeLevelProjection_comp_map_comp s g hg n h₁ χ₀).trans hχ₀
  refine ⟨max e e₁, le_max_left _ _, χ, fun i ↦ ?_⟩
  refine eq_of_coprojection_comp_envelopeLevelProjection_comp_eq s g hg _ _ fun j ↦ ?_
  rw [Fin.fin_one_eq_zero j]
  refine (coprojection_comp_envelopeLevelProjection_comp s g hg n (max e e₁) i χ).symm.trans ?_
  calc completedEnvelopeCoprojection s g hg n i ≫
        envelopeLevelProjection s g hg n (max e e₁) ≫ (crystallineToCompleted s).map χ
      = completedEnvelopeCoprojection s g hg n i ≫ m := congrArg _ hχ
    _ = k i := coprojection_comp_desc s g hg k i
    _ = _ := congrArg (completedEnvelopeCoprojection s g hg 0 0 ≫ ·)
        (envelopeLevelProjection_comp_map_comp s g hg 0 (le_max_left e e₁) (ψ i)).symm

end Affine

/-! ### The chaotic subsite of a global situation with `X` and `S` affine -/

section Whole

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **Morphisms of `𝒞` into the object attached to `L` by the inverse equivalence are morphisms
of `Cris(Γ(X, ⊤)/Γ(S, ⊤))` out of `L`.**  The bijection is the hom-set bijection of the
adjunction underlying the inverse of `wholeSiteEquivLittleAffine`. -/
def wholeHomEquiv (C : WholeSpaceThickening S)
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)) :
    ((wholeι S).obj C ⟶ (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop) ≃
      (L ⟶ (wholeSiteEquivLittleAffine hp).functor.obj (op C)) :=
  (fullyFaithfulWholeι S).homEquiv.symm.trans <|
    (opEquiv _ _).symm.trans <| (wholeSiteEquivLittleAffine hp).symm.toAdjunction.homEquiv L (op C)

/-- `wholeHomEquiv` turns postcomposition with a transported morphism into precomposition with the
morphism itself. -/
theorem wholeHomEquiv_comp (C : WholeSpaceThickening S)
    {L L' : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)}
    (k : (wholeι S).obj C ⟶ (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop)
    (φ : L' ⟶ L) :
    wholeHomEquiv hp C L'
        (k ≫ (wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map φ).unop) =
      φ ≫ wholeHomEquiv hp C L k := by
  show (wholeSiteEquivLittleAffine hp).symm.toAdjunction.homEquiv L' (op C)
      (((wholeSiteEquivLittleAffine hp).inverse.map φ) ≫ ((fullyFaithfulWholeι S).preimage k).op) =
    φ ≫ (wholeSiteEquivLittleAffine hp).symm.toAdjunction.homEquiv L (op C)
      ((fullyFaithfulWholeι S).preimage k).op
  exact Adjunction.homEquiv_naturality_left _ _ _

variable {ι : Type u}
  (g : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
    (affineSituation S hp).C) (hg : Function.Surjective g)

/-- **The uniqueness half of [Stacks, Tag 07L4] on the chaotic subsite**: two morphisms from a
thickening of the whole of `X` into a level of `wholeSpaceSystemOf` in degree `n` which agree
after every vertex map are equal. -/
theorem wholeSpaceSystemOf_hom_ext (C : WholeSpaceThickening S) {n e : ℕ}
    (k k' : (wholeι S).obj C ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).obj e)
    (h : ∀ i : Fin (n + 1),
      k ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e =
        k' ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e) :
    k = k' := by
  refine (wholeHomEquiv hp C _).injective (affineLevelSystem_hom_ext _ g hg _ _ fun i ↦ ?_)
  exact (wholeHomEquiv_comp hp C k
      (((affineLevelSystem _ g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e))).symm.trans
    ((congrArg (wholeHomEquiv hp C _) (h i)).trans (wholeHomEquiv_comp hp C k'
      (((affineLevelSystem _ g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e))))

/-- **The existence half of [Stacks, Tag 07L4] on the chaotic subsite**: a family of `n + 1`
morphisms from a thickening of the whole of `X` into a level of `wholeSpaceSystemOf` in degree
`0` is induced, after a tower map, by a morphism into a deeper level in degree `n`. -/
theorem exists_wholeSpaceSystemOf_desc (C : WholeSpaceThickening S) (n e : ℕ)
    (q : Fin (n + 1) → ((wholeι S).obj C ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋0⦌)).obj e)) :
    ∃ (e' : ℕ) (hee' : e ≤ e')
      (k : (wholeι S).obj C ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).obj e'),
      ∀ i : Fin (n + 1),
        k ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e' =
          q i ≫ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋0⦌)).map (homOfLE hee') := by
  obtain ⟨e', hee', χ, hχ⟩ := exists_affineLevelSystem_desc _ g hg _ n e
    fun i ↦ wholeHomEquiv hp C _ (q i)
  refine ⟨e', hee', (wholeHomEquiv hp C _).symm χ, fun i ↦ (wholeHomEquiv hp C _).injective ?_⟩
  refine (wholeHomEquiv_comp hp C ((wholeHomEquiv hp C _).symm χ)
      (((affineLevelSystem _ g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e'))).trans ?_
  refine Eq.trans ?_ (wholeHomEquiv_comp hp C (q i)
      (((affineLevelSystem _ g hg).obj ⦋0⦌).map (homOfLE hee').op)).symm
  rw [Equiv.apply_symm_apply, hχ]

end Whole

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
