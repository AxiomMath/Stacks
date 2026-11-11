module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.Precoverage
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence

/-!
# Coverings of semi-representable objects over an arbitrary site

A site in the sense of the Stacks Project (Tag 00VH) is a category `C` with a set of covering
families containing the isomorphisms, closed under composition, and closed under base change,
the fibre products along a member of a covering family existing. Here such a site is a
precoverage `J : Precoverage C` with `J.HasIsos`, `J.IsStableUnderComposition`,
`J.IsStableUnderBaseChange` and `J.HasPullbacks`; the category `C` itself is not assumed to have
fibre products.

The category `SR(C)` of semi-representable objects is `FormalCoproduct C`, and `SR(C, X)` is
`FormalCoproduct (Over X)`. This file defines covering morphisms of `SR(C)` and of `SR(C, X)`
for such a site (Tag 01G3) and proves their three permanence properties (Tag 01G4): stability
under composition, existence of the base change of a covering along any morphism together with
its covering property, and stability under products of pairs, the last when `C` has products
of pairs (for `SR(C)`), respectively fibre products (for `SR(C, X)`).

## Main definitions

* `IsSiteCovering`: a morphism of `SR(C)` is covering when, over each index of the target, its
  family of components is a covering family of the site (Tag 01G3).
* `IsSiteCoveringOver`: a morphism of `SR(C, X)` is covering when its image in `SR(C)` is
  (Tag 01G3).

## Main results

* `IsSiteCovering.comp` and `IsSiteCoveringOver.comp`: Tag 01G4, part (1).
* `IsSiteCovering.exists_hasPullback_pullback_snd` and
  `IsSiteCoveringOver.exists_hasPullback_pullback_snd`: Tag 01G4, part (2) — the fibre product
  exists and its projection to the base-change target is covering.
  `IsSiteCovering.of_isPullback` and `IsSiteCoveringOver.of_isPullback` give the covering
  property for an arbitrary fibre product square.
* `IsSiteCovering.prod_map` and `IsSiteCoveringOver.prod_map`: Tag 01G4, part (3).
* `isSiteCovering_toPrecoverage_iff` and `isSiteCoveringOver_toPrecoverage_iff`: for a site
  given by a pretopology on a category with fibre products, these notions are `IsCovering` and
  `IsCoveringOver`.

## Implementation notes

The fibre product in part (2) is the componentwise fibre product
`pullbackFormalCoproduct`, whose components are the fibre products in `C` (respectively in
`Over X`) that the site's base-change axiom provides along members of covering families. Over
`X` these are created by the forgetful functor `Over X ⥤ C`, which creates connected limits.

## References

* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
* [Stacks Project, Tag 01G4](https://stacks.math.columbia.edu/tag/01G4)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-! ### Covering morphisms -/

/-- Covering morphisms of `SR(C)` (Stacks Project, Tag 01G3). A morphism `f = (α, f_i)` of
semi-representable objects is a covering if, for every index `j` of the target, the family
`{U_i → V_j}_{α(i) = j}` is a covering family of the site. -/
def IsSiteCovering (J : Precoverage C) {U V : FormalCoproduct.{w} C} (f : U ⟶ V) : Prop :=
  ∀ j : V.I,
    Presieve.ofArrows
      (fun i : { i : U.I // f.f i = j } ↦ U.obj i.1)
      (fun i ↦ f.φ i.1 ≫ eqToHom (congrArg V.obj i.2)) ∈ J (V.obj j)

/-- Covering morphisms of `SR(C, X)` (Stacks Project, Tag 01G3). A morphism of
semi-representable objects over `X` is a covering if its image in `SR(C)` is a covering. -/
def IsSiteCoveringOver (J : Precoverage C) {X : C} {U V : FormalCoproduct.{w} (Over X)}
    (f : U ⟶ V) : Prop :=
  IsSiteCovering J ((mapFormalCoproduct (Over.forget X)).map f)

/-- For a site given by a pretopology, a morphism of `SR(C)` is covering for the underlying
precoverage exactly when it is covering in the sense of `IsCovering`. -/
theorem isSiteCovering_toPrecoverage_iff [HasPullbacks C] (J : Pretopology C)
    {U V : FormalCoproduct.{w} C} (f : U ⟶ V) :
    IsSiteCovering J.toPrecoverage f ↔ IsCovering J f :=
  Iff.rfl

/-- For a site given by a pretopology, a morphism of `SR(C, X)` is covering for the underlying
precoverage exactly when it is covering in the sense of `IsCoveringOver`. -/
theorem isSiteCoveringOver_toPrecoverage_iff [HasPullbacks C] (J : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) :
    IsSiteCoveringOver J.toPrecoverage f ↔ IsCoveringOver J f :=
  Iff.rfl

/-- An isomorphism of semi-representable objects is a covering. -/
theorem IsSiteCovering.of_isIso (J : Precoverage C) [J.HasIsos] {U V : FormalCoproduct.{w} C}
    (e : U ⟶ V) [IsIso e] : IsSiteCovering J e := by
  intro j
  let _ : Unique { i : U.I // e.f i = j } :=
    { default := ⟨(inv e).f j, f_inv_f e j⟩
      uniq := by
        rintro ⟨i, hi⟩
        exact Subtype.ext ((inv_f_f e i).symm.trans (congrArg (inv e).f hi)) }
  rw [Presieve.ofArrows_of_unique]
  exact J.mem_coverings_of_isIso _

/-- An isomorphism of semi-representable objects over `X` is a covering. -/
theorem IsSiteCoveringOver.of_isIso (J : Precoverage C) [J.HasIsos] {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (e : U ⟶ V) [IsIso e] : IsSiteCoveringOver J e :=
  IsSiteCovering.of_isIso J _

/-! ### Tag 01G4, part (1): composition -/

/-- **Stacks Project, Tag 01G4, part (1).** A composition of coverings in `SR(C)` is a
covering. -/
@[stacks 01G4 "part (1), for `SR(C)`, over an arbitrary site"]
theorem IsSiteCovering.comp (J : Precoverage C) [J.IsStableUnderComposition]
    {U V W : FormalCoproduct.{w} C} {f : U ⟶ V} {g : V ⟶ W}
    (hf : IsSiteCovering J f) (hg : IsSiteCovering J g) : IsSiteCovering J (f ≫ g) := by
  intro k
  have h := Precoverage.comp_mem_coverings (J := J)
    (fun j : { j : V.I // g.f j = k } ↦ g.φ j.1 ≫ eqToHom (congrArg W.obj j.2)) (hg k)
    (fun j (i : { i : U.I // f.f i = j.1 }) ↦ f.φ i.1 ≫ eqToHom (congrArg V.obj i.2))
    (fun j ↦ hf j.1)
  convert h using 1
  refine le_antisymm ?_ ?_
  · rintro Y a ⟨i⟩
    exact .mk' ⟨⟨f.f i.1, i.2⟩, ⟨i.1, rfl⟩⟩ rfl (by simp)
  · rintro Y a ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩⟩
    dsimp at hi
    subst j
    exact .mk' ⟨i, hj⟩ rfl (by simp)

/-- **Stacks Project, Tag 01G4, part (1)**, for `SR(C, X)`. A composition of coverings in
`SR(C, X)` is a covering. -/
@[stacks 01G4 "part (1), for `SR(C, X)`, over an arbitrary site"]
theorem IsSiteCoveringOver.comp (J : Precoverage C) [J.IsStableUnderComposition] {X : C}
    {U V W : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} {g : V ⟶ W}
    (hf : IsSiteCoveringOver J f) (hg : IsSiteCoveringOver J g) :
    IsSiteCoveringOver J (f ≫ g) := by
  unfold IsSiteCoveringOver at hf hg ⊢
  rw [Functor.map_comp]
  exact hf.comp J hg

/-! ### Tag 01G4, part (2): base change -/

/-- Along a component of a covering morphism of `SR(C)`, the fibre products with the
components of any other morphism to the same target exist: this is the existence clause of the
base-change axiom of the site. -/
theorem IsSiteCovering.hasPullback_φ (J : Precoverage C) [J.HasPullbacks]
    {U V W : FormalCoproduct.{w} C} {f : U ⟶ V} (hf : IsSiteCovering J f) (g : W ⟶ V)
    (i : Function.Pullback f.f g.f) :
    HasPullback (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2) := by
  have := J.hasPullbacks_of_mem (g.φ i.1.2) (hf (g.f i.1.2))
  exact Presieve.hasPullback (R := Presieve.ofArrows
      (fun a : { a : U.I // f.f a = g.f i.1.2 } ↦ U.obj a.1)
      (fun a ↦ f.φ a.1 ≫ eqToHom (congrArg V.obj a.2)))
    (g.φ i.1.2) (Presieve.ofArrows.mk (⟨i.1.1, i.2⟩ : { a : U.I // f.f a = g.f i.1.2 }))

/-- The componentwise fibre product of a covering morphism of `SR(C)` with any morphism to its
target, built from fibre product squares of the components, projects by a covering onto the
second factor. -/
theorem IsSiteCovering.pullbackFormalCoproduct_snd (J : Precoverage C)
    [J.IsStableUnderBaseChange] {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : W ⟶ V)
    (P : ∀ i : Function.Pullback f.f g.f,
      PullbackCone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2))
    (hP : ∀ i, IsLimit (P i)) (hf : IsSiteCovering J f) :
    IsSiteCovering J (pullbackFormalCoproduct.snd f g P) := by
  intro k
  change Presieve.ofArrows
    (fun i : { i : Function.Pullback f.f g.f // i.1.2 = k } ↦ (P i.1).pt)
    (fun i ↦ (P i.1).snd ≫ eqToHom (congrArg W.obj i.2)) ∈ _
  have h := Precoverage.mem_coverings_of_isPullback (J := J)
    (fun a : { a : U.I // f.f a = g.f k } ↦ f.φ a.1 ≫ eqToHom (congrArg V.obj a.2))
    (hf (g.f k)) (g.φ k) (P := fun a ↦ (P ⟨(a.1, k), a.2⟩).pt)
    (fun a ↦ (P ⟨(a.1, k), a.2⟩).snd) (fun a ↦ (P ⟨(a.1, k), a.2⟩).fst)
    (fun a ↦ (IsPullback.of_isLimit (hP ⟨(a.1, k), a.2⟩)).flip)
  convert h using 1
  refine le_antisymm ?_ ?_
  · rintro Y a ⟨⟨⟨⟨i, k'⟩, hi⟩, hk⟩⟩
    change k' = k at hk
    subst k'
    exact .mk' ⟨i, hi⟩ rfl (by simp)
  · rintro Y a ⟨⟨i, hi⟩⟩
    exact .mk' ⟨⟨⟨i, k⟩, hi⟩, rfl⟩ rfl (by simp)

/-- The fibre product of a covering morphism of `SR(C)` with any morphism to its target
exists. -/
theorem IsSiteCovering.hasPullback (J : Precoverage C) [J.HasPullbacks]
    {U V W : FormalCoproduct.{w} C} {f : U ⟶ V} (hf : IsSiteCovering J f) (g : W ⟶ V) :
    HasPullback f g := by
  have := hf.hasPullback_φ J g
  exact HasLimit.mk ⟨_, pullbackFormalCoproduct.isLimit f g (fun _ ↦ pullback.cone _ _)
    (fun _ ↦ pullback.isLimit _ _)⟩

/-- In any fibre product square of `SR(C)` whose bottom arrow is a covering, the opposite
arrow is a covering. -/
theorem IsSiteCovering.of_isPullback (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {P U V W : FormalCoproduct.{w} C} {p : P ⟶ U} {q : P ⟶ W} {f : U ⟶ V} {g : W ⟶ V}
    (h : IsPullback p q f g) (hf : IsSiteCovering J f) : IsSiteCovering J q := by
  have := hf.hasPullback_φ J g
  have hc := IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f g
    (fun _ ↦ pullback.cone _ _) (fun _ ↦ pullback.isLimit _ _))
  rw [← h.isoIsPullback_hom_snd _ _ hc]
  exact (IsSiteCovering.of_isIso J _).comp J
    (IsSiteCovering.pullbackFormalCoproduct_snd J f g _ (fun _ ↦ pullback.isLimit _ _) hf)

/-- **Stacks Project, Tag 01G4, part (2).** If `K ⟶ L` is a covering in `SR(C)` and `L' ⟶ L`
is a morphism, then the fibre product `K ×_L L'` exists and its projection to `L'` is a
covering. -/
@[stacks 01G4 "part (2), for `SR(C)`, over an arbitrary site"]
theorem IsSiteCovering.exists_hasPullback_pullback_snd (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {K L L' : FormalCoproduct.{w} C} {f : K ⟶ L} (hf : IsSiteCovering J f) (g : L' ⟶ L) :
    ∃ _ : HasPullback f g, IsSiteCovering J (pullback.snd f g) := by
  have := hf.hasPullback J g
  exact ⟨this, IsSiteCovering.of_isPullback J (IsPullback.of_hasPullback f g) hf⟩

/-- A morphism of objects over `X` whose underlying morphism in `C` has a fibre product with a
second morphism has a fibre product with it in `Over X`. -/
theorem hasPullback_over_of_hasPullback_left {X : C} {A B D : Over X} (a : A ⟶ D) (b : B ⟶ D)
    [HasPullback a.left b.left] : HasPullback a b := by
  have : HasLimit (cospan ((Over.forget X).map a) ((Over.forget X).map b)) :=
    ‹HasPullback a.left b.left›
  have : HasLimit (cospan a b ⋙ Over.forget X) :=
    hasLimit_of_iso (cospanCompIso (Over.forget X) a b).symm
  exact hasLimit_of_created (cospan a b) (Over.forget X)

/-- Along a component of a covering morphism of `SR(C, X)`, the fibre products in `Over X`
with the components of any other morphism to the same target exist. -/
theorem IsSiteCoveringOver.hasPullback_φ (J : Precoverage C) [J.HasPullbacks] {X : C}
    {U V W : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} (hf : IsSiteCoveringOver J f)
    (g : W ⟶ V) (i : Function.Pullback f.f g.f) :
    HasPullback (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2) := by
  have h := IsSiteCovering.hasPullback_φ J hf ((mapFormalCoproduct (Over.forget X)).map g) i
  have : HasPullback (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)).left (g.φ i.1.2).left := by
    rw [Over.comp_left, Over.eqToHom_left]
    exact h
  exact hasPullback_over_of_hasPullback_left _ _

/-- The fibre product of a covering morphism of `SR(C, X)` with any morphism to its target
exists. -/
theorem IsSiteCoveringOver.hasPullback (J : Precoverage C) [J.HasPullbacks] {X : C}
    {U V W : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} (hf : IsSiteCoveringOver J f)
    (g : W ⟶ V) : HasPullback f g := by
  have := hf.hasPullback_φ J g
  exact HasLimit.mk ⟨_, pullbackFormalCoproduct.isLimit f g (fun _ ↦ pullback.cone _ _)
    (fun _ ↦ pullback.isLimit _ _)⟩

/-- In any fibre product square of `SR(C, X)` whose bottom arrow is a covering, the opposite
arrow is a covering. -/
theorem IsSiteCoveringOver.of_isPullback (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks] {X : C}
    {P U V W : FormalCoproduct.{w} (Over X)} {p : P ⟶ U} {q : P ⟶ W} {f : U ⟶ V} {g : W ⟶ V}
    (h : IsPullback p q f g) (hf : IsSiteCoveringOver J f) : IsSiteCoveringOver J q := by
  have := hf.hasPullback_φ J g
  have hc := IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f g
    (fun _ ↦ pullback.cone _ _) (fun _ ↦ pullback.isLimit _ _))
  rw [← h.isoIsPullback_hom_snd _ _ hc]
  refine (IsSiteCoveringOver.of_isIso J _).comp J ?_
  have hsq : ∀ i : Function.Pullback f.f g.f,
      IsPullback (pullback.fst (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2)).left
        (pullback.snd (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2)).left
        ((f.φ i.1.1).left ≫ eqToHom (congrArg (fun j ↦ (V.obj j).left) i.2))
        (g.φ i.1.2).left := fun i ↦ by
    have := (IsPullback.of_hasPullback (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2))
      (g.φ i.1.2)).map (Over.forget X)
    simpa only [Over.forget_map, Over.comp_left, Over.eqToHom_left] using this
  exact IsSiteCovering.pullbackFormalCoproduct_snd J
    ((mapFormalCoproduct (Over.forget X)).map f) ((mapFormalCoproduct (Over.forget X)).map g)
    (fun i ↦ (hsq i).cone) (fun i ↦ (hsq i).isLimit) hf

/-- **Stacks Project, Tag 01G4, part (2)**, for `SR(C, X)`. If `K ⟶ L` is a covering in
`SR(C, X)` and `L' ⟶ L` is a morphism, then the fibre product `K ×_L L'` exists and its
projection to `L'` is a covering. -/
@[stacks 01G4 "part (2), for `SR(C, X)`, over an arbitrary site"]
theorem IsSiteCoveringOver.exists_hasPullback_pullback_snd (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks] {X : C}
    {K L L' : FormalCoproduct.{w} (Over X)} {f : K ⟶ L} (hf : IsSiteCoveringOver J f)
    (g : L' ⟶ L) :
    ∃ _ : HasPullback f g, IsSiteCoveringOver J (pullback.snd f g) := by
  have := hf.hasPullback J g
  exact ⟨this, IsSiteCoveringOver.of_isPullback J (IsPullback.of_hasPullback f g) hf⟩

/-! ### Tag 01G4, part (3): products -/

/-- **Stacks Project, Tag 01G4, part (3).** If `C` has products of pairs and `A ⟶ B`,
`K ⟶ L` are coverings in `SR(C)`, then `A × K ⟶ B × L` is a covering. The products in `SR(C)`
are those of `FormalCoproduct.instHasBinaryProducts` (Tag 01G2). -/
@[stacks 01G4 "part (3), for `SR(C)`, over an arbitrary site with products of pairs"]
theorem IsSiteCovering.prod_map (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [HasBinaryProducts C]
    {A B K L : FormalCoproduct.{w} C} {f : A ⟶ B} {g : K ⟶ L}
    (hf : IsSiteCovering J f) (hg : IsSiteCovering J g) : IsSiteCovering J (prod.map f g) := by
  rw [show prod.map f g = prod.map f (𝟙 K) ≫ prod.map (𝟙 B) g by
    refine prod.hom_ext ?_ ?_ <;> simp]
  exact (IsSiteCovering.of_isPullback J (IsPullback.of_prod_fst_with_id f K) hf).comp J
    (IsSiteCovering.of_isPullback J (isPullback_prod_snd (B := B) g) hg)

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback in
/-- **Stacks Project, Tag 01G4, part (3)**, for `SR(C, X)`. If `C` has fibre products and
`A ⟶ B`, `K ⟶ L` are coverings in `SR(C, X)`, then `A × K ⟶ B × L` is a covering. The products
in `SR(C, X)` are those of `FormalCoproduct.instHasBinaryProducts` (Tag 01G2) over the products
of `Over X`, which are fibre products over `X`. -/
@[stacks 01G4 "part (3), for `SR(C, X)`, over an arbitrary site with fibre products"]
theorem IsSiteCoveringOver.prod_map (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [HasPullbacks C] {X : C}
    {A B K L : FormalCoproduct.{w} (Over X)} {f : A ⟶ B} {g : K ⟶ L}
    (hf : IsSiteCoveringOver J f) (hg : IsSiteCoveringOver J g) :
    IsSiteCoveringOver J (prod.map f g) := by
  rw [show prod.map f g = prod.map f (𝟙 K) ≫ prod.map (𝟙 B) g by
    refine prod.hom_ext ?_ ?_ <;> simp]
  exact (IsSiteCoveringOver.of_isPullback J (IsPullback.of_prod_fst_with_id f K) hf).comp J
    (IsSiteCoveringOver.of_isPullback J (isPullback_prod_snd (B := B) g) hg)

end Stacks.CategoryTheory.Hypercovering

end
