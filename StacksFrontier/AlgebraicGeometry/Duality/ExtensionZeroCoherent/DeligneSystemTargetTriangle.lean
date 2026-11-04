module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles

/-!
# Dévissage in the target of a Hom-colimit along an inverse system

Let `R : 𝒟 ⥤ 𝒞` be a triangulated functor and let `F` be an inverse sequence in `𝒟`. The
predicate `CategoryTheory.RestrictionLifting F R N` says that `R` identifies
`colim_n Mor(F_n, N)` with `colim_n Mor(R F_n, R N)`, elementwise: every morphism
`R F_n ⟶ R N` is, past some index, the restriction of a morphism `F_m ⟶ N`, and two morphisms
`F_n ⟶ N` with the same restriction already agree past some index. For an open immersion
`j : U → X` of Noetherian schemes, a Deligne system `(K_n)` with value `K` and `R = j^*`, this
is the identification

`colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)`

of [Stacks, Tag 0G2H] at the object `L`.

This file proves that the collection of objects at which that identification holds is closed
under extensions in the *target* variable: for a distinguished triangle `L ⟶ M ⟶ N ⟶ L⟦1⟧` of
`𝒟`, if the identification holds at `N⟦-1⟧`, `L`, `N` and `L⟦1⟧` then it holds at `M`. This is
the first reduction in the proof of [Stacks, Tag 0G2H], where it is applied to the distinguished
triangles of the canonical truncations of the target in order to reduce that tag to a target
with a single nonzero cohomology sheaf. The companion reduction in the *source* variable — an
inverse system of distinguished triangles whose outer systems satisfy the predicate has middle
system satisfying it — is `CategoryTheory.restrictionLifting_triangle` of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles`.

## The shape of the statement

The four objects of the source's reduction are `N⟦-1⟧`, `L`, `N` and `L⟦1⟧`, and a shift by `-1`
is awkward to carry: `N⟦-1⟧⟦1⟧` is only isomorphic to `N`, not equal to it. The reduction is
therefore stated for a distinguished triangle

`T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧`

concluding at `T.obj₃` from hypotheses at `T.obj₁`, `T.obj₂`, `T.obj₁⟦1⟧` and `T.obj₂⟦1⟧`. The
source's triangle is the rotation of this one, with `L = T.obj₂`, `M = T.obj₃` and
`N = T.obj₁⟦1⟧`; the source's four objects are then exactly `T.obj₁`, `T.obj₂`, `T.obj₁⟦1⟧` and
`T.obj₂⟦1⟧`, with `N⟦-1⟧` realized as `T.obj₁` on the nose. In this shape no shift by `-1`
occurs and no rotated triangle is ever formed: the three instances of exactness of
`Mor(F_m, -)` that the five-lemma step needs are exactness of the original triangle at its
first and third objects, and exactness of its image at the second object.

## Main results

* `CategoryTheory.restrictionLifting_target_triangle_lift`: the surjectivity half — a morphism
  out of a restricted term into `T.obj₃` is, past some index, a restriction.
* `CategoryTheory.restrictionLifting_target_triangle_eq`: the injectivity half — two morphisms
  into `T.obj₃` with equal restrictions agree past some index.
* `CategoryTheory.restrictionLifting_target_triangle`: the two halves together, the first
  reduction in the proof of [Stacks, Tag 0G2H].

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v u u'

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- Exactness of `Mor(X, -)` at the second object of the image of a distinguished triangle under
a triangulated functor: a morphism into `R T.obj₂` killed by `R T.mor₂` factors through
`R T.mor₁`.

This is `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂` for the distinguished triangle
`R.mapTriangle.obj T`, restated with the first two morphisms of that triangle spelled as
`R.map T.mor₁` and `R.map T.mor₂`, which is what they are. -/
public lemma coyoneda_exact₂_map_of_distTriang (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟) {X : 𝒞}
    (f : X ⟶ R.obj T.obj₂) (hf : f ≫ R.map T.mor₂ = 0) :
    ∃ g : X ⟶ R.obj T.obj₁, f = g ≫ R.map T.mor₁ :=
  Triangle.coyoneda_exact₂ (R.mapTriangle.obj T) (R.map_distinguished T hT) f hf

/-- Exactness of `Mor(X, -)` at the third object of the image of a distinguished triangle under a
triangulated functor: a morphism into `R T.obj₃` killed by `R T.mor₃` factors through
`R T.mor₂`.

This is `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃` for the distinguished triangle
`R.mapTriangle.obj T`. The third morphism of that triangle is `R T.mor₃` followed by the
comparison isomorphism of the commutation of `R` with the shift, so being killed by `R T.mor₃`
is enough to be killed by it. -/
public lemma coyoneda_exact₃_map_of_distTriang (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟) {X : 𝒞}
    (f : X ⟶ R.obj T.obj₃) (hf : f ≫ R.map T.mor₃ = 0) :
    ∃ g : X ⟶ R.obj T.obj₂, f = g ≫ R.map T.mor₂ := by
  refine Triangle.coyoneda_exact₃ (R.mapTriangle.obj T) (R.map_distinguished T hT) f ?_
  show f ≫ R.map T.mor₃ ≫ (R.commShiftIso (1 : ℤ)).hom.app T.obj₁ = 0
  rw [← Category.assoc, hf, zero_comp]

/-- **The surjectivity half of the dévissage in the target.** Let `T` be a distinguished triangle
of `𝒟`. Suppose every morphism out of a restricted term of `F` into `T.obj₁⟦1⟧` lifts past some
index, morphisms into `T.obj₂⟦1⟧` are detected by their restrictions, and morphisms into
`T.obj₂` lift. Then every morphism `R F_n ⟶ R T.obj₃` is, past some index, the restriction of a
morphism `F_m ⟶ T.obj₃`.

The argument is the one of the source. Pushing `g` forward along `T.mor₃` and lifting it gives a
morphism `u : F_{m₁} ⟶ T.obj₁⟦1⟧` whose composite with `T.mor₁⟦1⟧` restricts to zero, hence
vanishes past some index; exactness of `Mor(F_{m₂}, -)` at the first object of `T` then factors
`u` through `T.obj₃` as some `v`. The difference between `R v` and the restriction of `g` dies
against `R T.mor₃`, so exactness at the second object of the image triangle factors it through
`R T.obj₂`; lifting that factorization and correcting `v` by it produces the required
morphism. -/
public lemma restrictionLifting_target_triangle_lift (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) [R.Additive]
    [R.CommShift ℤ] [R.IsTriangulated] {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟)
    (h₂ : RestrictionLifting F R T.obj₂)
    (h₁' : RestrictionLifting F R (T.obj₁⟦(1 : ℤ)⟧))
    (h₂' : RestrictionLifting F R (T.obj₂⟦(1 : ℤ)⟧))
    (n : ℕ) (g : R.obj (F.obj (op n)) ⟶ R.obj T.obj₃) :
    ∃ (m : ℕ) (h : n ≤ m) (f : F.obj (op m) ⟶ T.obj₃),
      R.map f = R.map (InverseSequence.tr F h) ≫ g := by
  -- Push `g` forward along `T.mor₃` and lift it to the term `T.obj₁⟦1⟧`.
  obtain ⟨m₁, hm₁, u, hu⟩ := h₁'.lift n (g ≫ R.map T.mor₃)
  -- The composite of `u` with `T.mor₁⟦1⟧` restricts to zero, hence dies past some index.
  have hzero : R.map (u ≫ T.mor₁⟦(1 : ℤ)⟧') =
      R.map (0 : F.obj (op m₁) ⟶ T.obj₂⟦(1 : ℤ)⟧) := by
    rw [R.map_comp, hu, R.map_zero, Category.assoc, Category.assoc, ← R.map_comp,
      comp_distTriang_mor_zero₃₁ T hT, R.map_zero, comp_zero, comp_zero]
  obtain ⟨m₂, hm₂, he⟩ := h₂'.eq m₁ (u ≫ T.mor₁⟦(1 : ℤ)⟧') 0 hzero
  rw [comp_zero] at he
  -- Hence `tr ≫ u` factors through `T.obj₃`, by exactness at the first object of `T`.
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₁ T hT (InverseSequence.tr F hm₂ ≫ u) (by
    rw [Category.assoc, he])
  have hn₂ : n ≤ m₂ := hm₁.trans hm₂
  -- The discrepancy between `R v` and the restriction of `g` dies against `R T.mor₃`.
  have hvg : R.map v ≫ R.map T.mor₃ = R.map (InverseSequence.tr F hn₂) ≫ g ≫ R.map T.mor₃ := by
    rw [← R.map_comp, ← hv, R.map_comp, hu, ← Category.assoc, ← R.map_comp, tr_comp]
  obtain ⟨w, hw⟩ := coyoneda_exact₃_map_of_distTriang R hT
    (R.map v - R.map (InverseSequence.tr F hn₂) ≫ g) (by
      rw [Preadditive.sub_comp, hvg, Category.assoc, sub_self])
  -- Lift that factorization and correct `v` by it.
  obtain ⟨m₃, hm₃, w', hw'⟩ := h₂.lift m₂ w
  refine ⟨m₃, hn₂.trans hm₃, InverseSequence.tr F hm₃ ≫ v - w' ≫ T.mor₂, ?_⟩
  have hfin : R.map (InverseSequence.tr F hm₃ ≫ v - w' ≫ T.mor₂) =
      R.map (InverseSequence.tr F hm₃) ≫ (R.map v - w ≫ R.map T.mor₂) := by
    rw [R.map_sub, R.map_comp, R.map_comp, hw', Category.assoc, Preadditive.comp_sub]
  have hcancel : R.map v - w ≫ R.map T.mor₂ = R.map (InverseSequence.tr F hn₂) ≫ g := by
    rw [← hw, sub_sub_cancel]
  rw [hfin, hcancel, ← Category.assoc, ← R.map_comp, tr_comp]

/-- **The injectivity half of the dévissage in the target.** Let `T` be a distinguished triangle
of `𝒟`. Suppose morphisms into `T.obj₁⟦1⟧` and into `T.obj₂` are detected by their restrictions,
and morphisms into `T.obj₁` lift. Then two morphisms `F_n ⟶ T.obj₃` with equal restrictions
agree past some index.

The argument is the one of the source. The two morphisms agree against `T.mor₃` past some index,
so their difference factors through `T.obj₂` as some `e`, by exactness of `Mor(F_{m₁}, -)` at
the third object of `T`. Since that difference restricts to zero, `R e` dies against
`R T.mor₂`, so exactness at the second object of the image triangle factors `R e` through
`R T.obj₁`; lifting that factorization and correcting `e` by it gives a morphism into `T.obj₂`
restricting to zero, which therefore vanishes past some index. The difference is then a
composite through `T.mor₁ ≫ T.mor₂ = 0`. -/
public lemma restrictionLifting_target_triangle_eq (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) [R.Additive]
    [R.CommShift ℤ] [R.IsTriangulated] {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟)
    (h₁ : RestrictionLifting F R T.obj₁) (h₂ : RestrictionLifting F R T.obj₂)
    (h₁' : RestrictionLifting F R (T.obj₁⟦(1 : ℤ)⟧))
    (n : ℕ) (f g : F.obj (op n) ⟶ T.obj₃) (hfg : R.map f = R.map g) :
    ∃ (m : ℕ) (h : n ≤ m), InverseSequence.tr F h ≫ f = InverseSequence.tr F h ≫ g := by
  -- The two morphisms agree against `T.mor₃` past some index.
  obtain ⟨m₁, hm₁, he₁⟩ := h₁'.eq n (f ≫ T.mor₃) (g ≫ T.mor₃) (by
    rw [R.map_comp, R.map_comp, hfg])
  -- Their difference factors through `T.obj₂`, by exactness at the third object of `T`.
  obtain ⟨e, hee⟩ := Triangle.coyoneda_exact₃ T hT
    (InverseSequence.tr F hm₁ ≫ f - InverseSequence.tr F hm₁ ≫ g) (by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, he₁, sub_self])
  -- Since the difference restricts to zero, `R e` dies against `R T.mor₂`.
  have hRe : R.map e ≫ R.map T.mor₂ = 0 := by
    rw [← R.map_comp, ← hee, R.map_sub, R.map_comp, R.map_comp, hfg, sub_self]
  obtain ⟨k, hk⟩ := coyoneda_exact₂_map_of_distTriang R hT (R.map e) hRe
  -- Lift that factorization and correct `e` by it; the correction restricts to zero.
  obtain ⟨m₂, hm₂, κ, hκ⟩ := h₁.lift m₁ k
  have hcorr : R.map (InverseSequence.tr F hm₂ ≫ e - κ ≫ T.mor₁) =
      R.map (0 : F.obj (op m₂) ⟶ T.obj₂) := by
    rw [R.map_sub, R.map_comp, R.map_comp, hκ, hk, R.map_zero, Category.assoc, sub_self]
  obtain ⟨m₃, hm₃, hvanish⟩ := h₂.eq m₂ (InverseSequence.tr F hm₂ ≫ e - κ ≫ T.mor₁) 0 hcorr
  rw [comp_zero, Preadditive.comp_sub, sub_eq_zero] at hvanish
  -- The difference is now a composite through `T.mor₁ ≫ T.mor₂ = 0`.
  refine ⟨m₃, hm₁.trans (hm₂.trans hm₃), ?_⟩
  have htr : InverseSequence.tr F (hm₁.trans (hm₂.trans hm₃)) =
      (InverseSequence.tr F hm₃ ≫ InverseSequence.tr F hm₂) ≫ InverseSequence.tr F hm₁ := by
    rw [tr_comp, tr_comp]
  rw [← sub_eq_zero, htr]
  simp only [Category.assoc]
  rw [← Preadditive.comp_sub, ← Preadditive.comp_sub, hee,
    show InverseSequence.tr F hm₃ ≫ InverseSequence.tr F hm₂ ≫ e ≫ T.mor₂ =
        (InverseSequence.tr F hm₃ ≫ InverseSequence.tr F hm₂ ≫ e) ≫ T.mor₂ from by
      simp only [Category.assoc],
    hvanish]
  simp only [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

/-- **The dévissage in the target of the identification of [Stacks, Tag 0G2H]**, the first
reduction in the proof of that tag. Let `R : 𝒟 ⥤ 𝒞` be a triangulated functor, let `F` be an
inverse sequence in `𝒟`, and let

`T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧`

be a distinguished triangle of `𝒟`. If `R` identifies `colim_n Mor(F_n, -)` with
`colim_n Mor(R F_n, R -)` at the four objects `T.obj₁`, `T.obj₂`, `T.obj₁⟦1⟧` and `T.obj₂⟦1⟧`,
then it does so at `T.obj₃`.

Read through the rotation `L = T.obj₂`, `M = T.obj₃`, `N = T.obj₁⟦1⟧`, this is the step of the
source reading: for a distinguished triangle `L ⟶ M ⟶ N ⟶ L⟦1⟧`, if the identification holds
for `N⟦-1⟧`, `L`, `N` and `L⟦1⟧` then it holds for `M`. The source deduces it from the two long
exact sequences of the triangle by the five lemma; here the two halves of that five lemma are
`CategoryTheory.restrictionLifting_target_triangle_lift` and
`CategoryTheory.restrictionLifting_target_triangle_eq`, each proved by the elementwise exactness
of `Mor(F_m, -)` on a distinguished triangle.

Applied to the distinguished triangles of the canonical truncations of a target, this is what
reduces [Stacks, Tag 0G2H] to a target with a single nonzero cohomology sheaf. -/
public lemma restrictionLifting_target_triangle (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) [R.Additive]
    [R.CommShift ℤ] [R.IsTriangulated] {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟)
    (h₁ : RestrictionLifting F R T.obj₁) (h₂ : RestrictionLifting F R T.obj₂)
    (h₁' : RestrictionLifting F R (T.obj₁⟦(1 : ℤ)⟧))
    (h₂' : RestrictionLifting F R (T.obj₂⟦(1 : ℤ)⟧)) :
    RestrictionLifting F R T.obj₃ where
  lift := restrictionLifting_target_triangle_lift F R hT h₂ h₁' h₂'
  eq := restrictionLifting_target_triangle_eq F R hT h₁ h₂ h₁'

end CategoryTheory

end
