module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BottomHomologyEdgeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CounitGysinEdge

/-!
# An exact functor carries the Gysin edge morphism to the Gysin edge morphism

`Stacks.CounitGysinEdge.edge` is the Gysin edge morphism `P(H ᶜ(RH K))[-c] ⟶ K` of [Stacks, Tag
0G8A] with every geometric input replaced by a variable.  This file identifies the image of that
morphism under an exact functor with the edge morphism built from the corresponding data on the
other side, which is what the square of [Stacks, Tag 0G8B] needs: there the exact functor is the
one forgetting the module structure of a sheaf of modules, and the two sets of data are the
module-side and the abelian-side derived supported sections, direct images and counits.

Two squares of exact functors are given, one over the ambient category and one over the closed
subset,

`Φ : C₁ ⥤ C₂`,  `Ψ : D₁ ⥤ D₂`,  `P₁ : D₁ ⥤ C₁`,  `P₂ : D₂ ⥤ C₂`,  `ν : P₁ ⋙ Φ ≅ Ψ ⋙ P₂`,

together with functors `RH₁`, `RH₂` on the derived categories, a comparison
`θ : RH₁ ⋙ Ψᴰ ≅ Φᴰ ⋙ RH₂` — in the application [Stacks, Tag 0G74] part (2) — and the two
transformations `ε₁`, `ε₂` the edge morphisms are built from.  The one hypothesis is that `Φᴰ`
carries `ε₁` to `ε₂` across `θ` and `ν`; in the application that is the compatibility of the
counit of [Stacks, Tag 0A3B] with forgetting the module structure.

## Main definitions

* `Stacks.CounitGysinEdge.pushCompare`: the derived comparison `P₁ᴰ ⋙ Φᴰ ≅ Ψᴰ ⋙ P₂ᴰ` descended
  from `ν`, which is
  `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` with the
  geometry replaced by variables.
* `Stacks.CounitGysinEdge.CounitCompatible`: the hypothesis above, named.
* `Stacks.CounitGysinEdge.edgeSourceCompare`: the identification of `Φᴰ` of the source of the
  first edge morphism with the source of the second.

## Main results

* `Stacks.CounitGysinEdge.pushCompare_single`: **the four single-functor comparisons of the square
  intertwine**, the generic form of
  `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_single`.
* `Stacks.CounitGysinEdge.mapDerivedCategory_edge`: **an exact functor carries the Gysin edge
  morphism to the Gysin edge morphism**, read across `edgeSourceCompare`.

## Implementation notes

The three factors of the edge morphism are treated one at a time, and each is already available:

* the **first** factor, the single-functor comparison of the direct image, moves across the square
  by `pushCompare_single`, which is
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_app` at the two instances of
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` that `pushCompare` is built from
  together with `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app` at the
  instance of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` between them;
* the **second** factor, the edge morphism out of the bottom cohomology object, moves by
  `Stacks.BottomHomologyEdge.mapDerivedCategory_edge` for `Ψ`, followed by
  `Stacks.BottomHomologyEdge.naturality` at `θ` to pass from `Ψᴰ(RH₁ K)` to `RH₂(Φᴰ K)`;
* the **third** factor is the hypothesis `CounitCompatible`.

What glues them is the naturality of `pushCompare` at the bottom edge morphism and that of the
single-functor comparison of `P₂`.  Both rearrangements are `private` lemmas stated at a variable
category and applied with `exact`, as in
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_single` and
`Stacks.BottomHomologyEdge.mapDerivedCategory_edge`: the objects along the composites are
definitionally equal in the two spellings "push forward then apply the exact functor" and "apply
the exact functor then push forward", which `rw` refuses to identify.

That `RH₂(Φᴰ K)` again has no cohomology below `c` is read off `θ`, by
`Stacks.BottomHomologyEdge.isGE_mapDerivedCategory_obj` for `Ψ` and
`CategoryTheory.Triangulated.TStructure.isGE_of_iso`.

**No declaration here carries a `@[stacks ...]` attribute.**  The edge morphism is a construction
of this library and this is a compatibility of it with an exact functor; nothing of the source is
proved.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G8B](https://stacks.math.columbia.edu/tag/0G8B)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.4 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits

namespace Stacks.CounitGysinEdge

open DerivedCategory

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {D₁ : Type u₂} [Category.{v₂} D₁] [Abelian D₁] [HasDerivedCategory.{w₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] [Abelian C₂] [HasDerivedCategory.{w₃} C₂]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂] [HasDerivedCategory.{w₄} D₂]
  (P₁ : D₁ ⥤ C₁) [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  (Φ : C₁ ⥤ C₂) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (Ψ : D₁ ⥤ D₂) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
  (P₂ : D₂ ⥤ C₂) [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  (ν : P₁ ⋙ Φ ≅ Ψ ⋙ P₂)

/-- **The derived comparison `P₁ᴰ ⋙ Φᴰ ≅ Ψᴰ ⋙ P₂ᴰ`** descended from an isomorphism
`ν : P₁ ⋙ Φ ≅ Ψ ⋙ P₂` of exact functors: the two comparisons of a composite of exact functors
with the composite of the descents, with the descent of `ν` between them.

This is
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` with the
geometry replaced by variables. -/
def pushCompare : P₁.mapDerivedCategory ⋙ Φ.mapDerivedCategory ≅
    Ψ.mapDerivedCategory ⋙ P₂.mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso P₁ Φ).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ ν ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso Ψ P₂

/-- The three factors of `pushCompare` at an object, as an equation; `pushCompare` is an
`Iso.trans` chain, whose component is the composite of the components only after
`CategoryTheory.Iso.trans_hom` and `CategoryTheory.NatTrans.comp_app`. -/
theorem pushCompare_hom_app (L : DerivedCategory D₁) :
    (pushCompare P₁ Φ Ψ P₂ ν).hom.app L =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso P₁ Φ).inv.app L ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
            (P₁ ⋙ Φ) (Ψ ⋙ P₂) ν).hom.app L ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso Ψ P₂).hom.app L := by
  simp [pushCompare]

/-- The formal rearrangement of `pushCompare_single`, at a variable category: `h1` splits the
left-hand side into the comparison for the composite, `h3` and `hp` recognise the two right-hand
factors as the comparison for the other composite, `h2` exchanges the two and `hw` cancels the
isomorphism placed in degree `c` against its inverse.  Stated abstractly and applied with `exact`
because the objects along the composites are definitionally equal in the two spellings "push
forward then apply the functor" and "apply the functor then push forward", which `rw` refuses to
identify. -/
lemma paste {V : Type*} [Category* V] {a b d g m m' : V}
    (P : a ⟶ g) (p₁ : a ⟶ b) (p₂ : b ⟶ d) (p₃ : d ⟶ g) (p₃' : g ⟶ d)
    (t : b ⟶ m) (u : d ⟶ m') (v : g ⟶ m') (w : m ⟶ m') (w' : m' ⟶ m) (L : a ⟶ m)
    (h1 : p₁ ≫ t = L) (h2 : p₂ ≫ u = t ≫ w) (h3 : p₃' ≫ u = v)
    (hp : p₃ ≫ p₃' = 𝟙 d) (hw : w ≫ w' = 𝟙 m) (hP : P = p₁ ≫ p₂ ≫ p₃) :
    L = P ≫ v ≫ w' := by
  have h : p₃ ≫ v = u := by rw [← h3, ← Category.assoc, hp, Category.id_comp]
  rw [hP, Category.assoc, Category.assoc, ← Category.assoc p₃ v w', h,
    ← Category.assoc p₂ u w', h2, Category.assoc t w w', hw, Category.comp_id, h1]

/-- A functor carries a composite equal to an identity to a composite equal to an identity. -/
private lemma map_comp_eq_id {V W : Type*} [Category* V] [Category* W] (F : V ⥤ W) {x y : V}
    {f : x ⟶ y} {g : y ⟶ x} (h : f ≫ g = 𝟙 x) : F.map f ≫ F.map g = 𝟙 (F.obj x) := by
  rw [← F.map_comp, h, F.map_id]

/-- **The four single-functor comparisons of the square intertwine.**  Applying `Φ` to the
comparison for `P₁` and then the comparison for `Φ` is, through `pushCompare`, applying `P₂` to
the comparison for `Ψ` and then the comparison for `P₂`, up to `ν` placed in degree `c`.

This is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comp_app` at each of the two
instances of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` that `pushCompare` is
built from, together with
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app` at the instance of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` between them.  It is the generic
form of
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_single`. -/
theorem pushCompare_single (c : ℤ) (A : D₁) :
    Φ.mapDerivedCategory.map ((P₁.mapDerivedCategorySingleFunctor c).hom.app A) ≫
        (Φ.mapDerivedCategorySingleFunctor c).hom.app (P₁.obj A) =
      (pushCompare P₁ Φ Ψ P₂ ν).hom.app ((singleFunctor D₁ c).obj A) ≫
        (P₂.mapDerivedCategory.map ((Ψ.mapDerivedCategorySingleFunctor c).hom.app A) ≫
            (P₂.mapDerivedCategorySingleFunctor c).hom.app (Ψ.obj A)) ≫
          (singleFunctor C₂ c).map (ν.inv.app A) :=
  paste _ _ _ _ _ _ _ _ _ _ _
    (Functor.mapDerivedCategorySingleFunctor_comp_app P₁ Φ c A)
    (Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app (P₁ ⋙ Φ) (Ψ ⋙ P₂) ν c A)
    (Functor.mapDerivedCategorySingleFunctor_comp_app Ψ P₂ c A)
    (Iso.hom_inv_id_app _ _)
    (map_comp_eq_id _ (Iso.hom_inv_id_app ν A))
    (pushCompare_hom_app P₁ Φ Ψ P₂ ν _)

variable (RH₁ : DerivedCategory C₁ ⥤ DerivedCategory D₁)
  (RH₂ : DerivedCategory C₂ ⥤ DerivedCategory D₂)
  (θ : RH₁ ⋙ Ψ.mapDerivedCategory ≅ Φ.mapDerivedCategory ⋙ RH₂)
  (ε₁ : RH₁ ⋙ P₁.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C₁))
  (ε₂ : RH₂ ⋙ P₂.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C₂))

/-- **`Φᴰ` carries `ε₁` to `ε₂`.**  The image under `Φᴰ` of `ε₁` at `K` is, across `pushCompare`
and `θ`, the transformation `ε₂` at `Φᴰ K`.

In the application `ε₁` and `ε₂` are the counits of the adjunctions of [Stacks, Tag 0A3B] on
modules and on abelian sheaves, and this is their compatibility with forgetting the module
structure: `Stacks.Cohomology.AbelianSupportedCounitForget`
`.whiskerRight_derivedSupportedSectionsToId` bridged to the counit by `Stacks.Perfect`
`.SupportCounitComparison.derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`. -/
def CounitCompatible : Prop :=
  ∀ K : DerivedCategory C₁,
    Φ.mapDerivedCategory.map (ε₁.app K) =
      (pushCompare P₁ Φ Ψ P₂ ν).hom.app (RH₁.obj K) ≫
        P₂.mapDerivedCategory.map (θ.hom.app K) ≫ ε₂.app (Φ.mapDerivedCategory.obj K)

/-- **The image under `Φᴰ` of `RH₁ K` has no cohomology below `c`** when `RH₁ K` has none, and so
neither has `RH₂(Φᴰ K)`, the two being identified by `θ`.  This is
`Stacks.BottomHomologyEdge.isGE_mapDerivedCategory_obj` for `Ψ` carried across `θ`. -/
lemma isGE_obj_mapDerivedCategory (c : ℤ) (K : DerivedCategory C₁) [(RH₁.obj K).IsGE c]
    (e : (RH₁ ⋙ Ψ.mapDerivedCategory).obj K ≅ (Φ.mapDerivedCategory ⋙ RH₂).obj K) :
    (RH₂.obj (Φ.mapDerivedCategory.obj K)).IsGE c :=
  have : ((RH₁ ⋙ Ψ.mapDerivedCategory).obj K).IsGE c :=
    Stacks.BottomHomologyEdge.isGE_mapDerivedCategory_obj Ψ c (RH₁.obj K)
  TStructure.t.isGE_of_iso e c

/-- **The identification of `Φᴰ` of the source of the first edge morphism with the source of the
second.**  The single complex `P₁(H ᶜ(RH₁ K))[-c]` is carried by `Φᴰ` to
`P₂(H ᶜ(RH₂(Φᴰ K)))[-c]` in three steps: the single functor is moved across `Φ` by Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, the square of direct images by `ν`, and
the cohomology object by `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for `Ψ` followed
by `θ`, the last two placed in degree `c`.  The first two factors are bracketed together because
that is the shape in which `pushCompare_single` delivers them. -/
def edgeSourceCompare (c : ℤ) (K : DerivedCategory C₁) :
    Φ.mapDerivedCategory.obj
        ((singleFunctor C₁ c).obj (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K)))) ⟶
      (singleFunctor C₂ c).obj
        (P₂.obj ((homologyFunctor D₂ c).obj (RH₂.obj (Φ.mapDerivedCategory.obj K)))) :=
  ((Φ.mapDerivedCategorySingleFunctor c).hom.app
          (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
        (singleFunctor C₂ c).map
          (ν.hom.app ((homologyFunctor D₁ c).obj (RH₁.obj K)))) ≫
    (singleFunctor C₂ c).map
      (P₂.map ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
        (homologyFunctor D₂ c).map (θ.hom.app K)))

omit [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁] [P₂.Additive]
    [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂] in
/-- The three factors of `edgeSourceCompare`, as an equation holding by `rfl`; the chase below
uses them separately. -/
theorem edgeSourceCompare_eq (c : ℤ) (K : DerivedCategory C₁) :
    edgeSourceCompare P₁ Φ Ψ P₂ ν RH₁ RH₂ θ c K =
      ((Φ.mapDerivedCategorySingleFunctor c).hom.app
            (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
          (singleFunctor C₂ c).map
            (ν.hom.app ((homologyFunctor D₁ c).obj (RH₁.obj K)))) ≫
        (singleFunctor C₂ c).map
          (P₂.map ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
            (homologyFunctor D₂ c).map (θ.hom.app K))) :=
  rfl

/-- The first factor of the chase below, at a variable category: the inverse of the single-functor
comparison of `P₁` is moved to the other side of `pushCompare_single`, which `hstar` is, and `ν`
placed in degree `c` is inverted.  Stated abstractly and applied with `exact` for the reason
recorded on `paste`. -/
private lemma first_formal {V : Type*} [Category* V] {x y r z : V}
    (hm : y ⟶ x) (hi : x ⟶ y) (u : x ⟶ z) (q : y ⟶ r) (νi : r ⟶ z) (νh : z ⟶ r)
    (hstar : hm ≫ u = q ≫ νi) (hν : νi ≫ νh = 𝟙 r) (hinv : hi ≫ hm = 𝟙 x) :
    hi ≫ q = u ≫ νh := by
  have hq : hm ≫ u ≫ νh = q := by
    rw [← Category.assoc, hstar, Category.assoc, hν, Category.comp_id]
  rw [← hq, ← Category.assoc, hinv, Category.id_comp]

/-- The rearrangement that moves the bottom edge morphism across `Ψ` and then along `θ`, at a
variable category: `hΨ` is `Stacks.BottomHomologyEdge.mapDerivedCategory_edge`, `hθ` its
naturality at `θ`, `hsplit` splits the composite placed in degree `c`, and `hsh` and `hm` cancel
the two comparisons against their inverses.  Stated abstractly and applied with `exact` for the
reason recorded on `paste`. -/
private lemma mid_formal {V : Type*} [Category* V] {x y z w u v : V}
    (m : x ⟶ y) (mi : y ⟶ x) (sh : y ⟶ z) (shh : z ⟶ y) (ed : x ⟶ w) (t : w ⟶ v)
    (bp : z ⟶ w) (sHt : z ⟶ u) (bq : u ⟶ v) (shsH : y ⟶ u)
    (hΨ : shh ≫ mi ≫ ed = bp) (hθ : sHt ≫ bq = bp ≫ t)
    (hsplit : shsH = sh ≫ sHt) (hsh : sh ≫ shh = 𝟙 y) (hm : m ≫ mi = 𝟙 x) :
    ed ≫ t = m ≫ shsH ≫ bq := by
  rw [hsplit]
  simp only [Category.assoc]
  rw [hθ, ← hΨ]
  simp only [Category.assoc]
  rw [← Category.assoc sh shh (mi ≫ ed ≫ t), hsh, Category.id_comp,
    ← Category.assoc m mi (ed ≫ t), hm, Category.id_comp]

/-- Cancelling an isomorphism off the right of an equation, at a variable category: used where the
two sides spell one object as `F.obj (G.obj x)` and as `(G ⋙ F).obj x`, which `rw` refuses to
identify while `exact` reduces them. -/
private lemma cancel_formal {V : Type*} [Category* V] {x y z : V}
    (f : x ⟶ y) (hv : y ⟶ z) (iv : z ⟶ y) (g : x ⟶ z)
    (h : f ≫ hv = g) (hvi : hv ≫ iv = 𝟙 y) : f = g ≫ iv := by
  rw [← h, Category.assoc, hvi, Category.comp_id]

/-- The formal rearrangement of the chase below, at a variable category.  Reading the edge
morphism's three factors left to right: `hfirst` moves the first across the square, `hnat` — the
naturality of `pushCompare` — carries the second to the other side, `hmid` identifies it there
with the second factor of the other edge morphism, and `hε` replaces the third by the hypothesis
`CounitCompatible`.  Stated abstractly and applied with `exact` for the reason recorded on
`paste`. -/
private lemma chase {V : Type*} [Category* V] {x y z k l n p q r s t : V}
    (e₁ : x ⟶ y) (e₂ : y ⟶ z) (e₃ : z ⟶ k) (pc : z ⟶ l) (pt : l ⟶ n) (g₃ : n ⟶ k)
    (pcs : y ⟶ p) (pm : p ⟶ l) (b₁ : p ⟶ q) (b₂ : q ⟶ r) (b₃ : r ⟶ s) (g₁ : s ⟶ t)
    (g₂ : t ⟶ n) (u : x ⟶ r)
    (hε : e₃ = pc ≫ pt ≫ g₃) (hnat : e₂ ≫ pc = pcs ≫ pm)
    (hmid : pm ≫ pt = b₁ ≫ b₂ ≫ b₃ ≫ g₁ ≫ g₂) (hfirst : e₁ ≫ pcs ≫ b₁ ≫ b₂ = u) :
    e₁ ≫ e₂ ≫ e₃ = (u ≫ b₃) ≫ g₁ ≫ g₂ ≫ g₃ := by
  have hstep : e₁ ≫ e₂ ≫ pc ≫ pt ≫ g₃ = e₁ ≫ pcs ≫ pm ≫ pt ≫ g₃ := by
    rw [← Category.assoc e₂ pc (pt ≫ g₃), hnat, Category.assoc]
  rw [hε, hstep, ← Category.assoc pm pt g₃, hmid, ← hfirst]
  simp only [Category.assoc]

/-- **An exact functor carries the Gysin edge morphism to the Gysin edge morphism.**  Granted that
`Φᴰ` carries `ε₁` to `ε₂`, the image under `Φᴰ` of the edge morphism
`P₁(H ᶜ(RH₁ K))[-c] ⟶ K` is the edge morphism `P₂(H ᶜ(RH₂(Φᴰ K)))[-c] ⟶ Φᴰ K`, read across
`edgeSourceCompare`.

The three factors move one at a time: the first by `pushCompare_single`, the second by
`Stacks.BottomHomologyEdge.mapDerivedCategory_edge` for `Ψ` followed by
`Stacks.BottomHomologyEdge.naturality` at `θ`, and the third by the hypothesis. -/
theorem mapDerivedCategory_edge (hε : CounitCompatible P₁ Φ Ψ P₂ ν RH₁ RH₂ θ ε₁ ε₂) (c : ℤ)
    (K : DerivedCategory C₁) [(RH₁.obj K).IsGE c] :
    haveI : (RH₂.obj (Φ.mapDerivedCategory.obj K)).IsGE c :=
      isGE_obj_mapDerivedCategory Φ Ψ RH₁ RH₂ c K (θ.app K)
    Φ.mapDerivedCategory.map (edge RH₁ P₁ ε₁ c K) =
      edgeSourceCompare P₁ Φ Ψ P₂ ν RH₁ RH₂ θ c K ≫
        edge RH₂ P₂ ε₂ c (Φ.mapDerivedCategory.obj K) := by
  have hGEcomp : ((RH₁ ⋙ Ψ.mapDerivedCategory).obj K).IsGE c :=
    Stacks.BottomHomologyEdge.isGE_mapDerivedCategory_obj Ψ c (RH₁.obj K)
  have hGE₂ : (RH₂.obj (Φ.mapDerivedCategory.obj K)).IsGE c :=
    isGE_obj_mapDerivedCategory Φ Ψ RH₁ RH₂ c K (θ.app K)
  have hGE₂' : ((Φ.mapDerivedCategory ⋙ RH₂).obj K).IsGE c := hGE₂
  -- the naturality of `pushCompare` at the bottom edge morphism of `RH₁ K`
  have hnat := (pushCompare P₁ Φ Ψ P₂ ν).hom.naturality
    ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (RH₁.obj K) ≫
      (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app (RH₁.obj K)) ≫
        inv ((TStructure.t.truncGEπ c).app (RH₁.obj K)))
  simp only [Functor.comp_map] at hnat
  -- the bottom edge morphism moved across `Ψ` and then along `θ`
  have hΨ := Stacks.BottomHomologyEdge.mapDerivedCategory_edge Ψ c (RH₁.obj K)
  have hθ : (singleFunctor D₂ c).map ((homologyFunctor D₂ c).map (θ.hom.app K)) ≫
        ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app
              (RH₂.obj (Φ.mapDerivedCategory.obj K)) ≫
            (TStructure.t.truncGE c).map
                ((TStructure.t.truncLTι (c + 1)).app
                  (RH₂.obj (Φ.mapDerivedCategory.obj K))) ≫
              inv ((TStructure.t.truncGEπ c).app
                (RH₂.obj (Φ.mapDerivedCategory.obj K)))) =
      ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app
              (Ψ.mapDerivedCategory.obj (RH₁.obj K)) ≫
            (TStructure.t.truncGE c).map
                ((TStructure.t.truncLTι (c + 1)).app
                  (Ψ.mapDerivedCategory.obj (RH₁.obj K))) ≫
              inv ((TStructure.t.truncGEπ c).app
                (Ψ.mapDerivedCategory.obj (RH₁.obj K)))) ≫
        θ.hom.app K :=
    Stacks.BottomHomologyEdge.naturality c (θ.hom.app K)
  have hΨθ : Ψ.mapDerivedCategory.map
          ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (RH₁.obj K) ≫
            (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app (RH₁.obj K)) ≫
              inv ((TStructure.t.truncGEπ c).app (RH₁.obj K))) ≫ θ.hom.app K =
      (Ψ.mapDerivedCategorySingleFunctor c).hom.app
          ((homologyFunctor D₁ c).obj (RH₁.obj K)) ≫
        (singleFunctor D₂ c).map
            ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
              (homologyFunctor D₂ c).map (θ.hom.app K)) ≫
          ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app
                (RH₂.obj (Φ.mapDerivedCategory.obj K)) ≫
              (TStructure.t.truncGE c).map
                  ((TStructure.t.truncLTι (c + 1)).app
                    (RH₂.obj (Φ.mapDerivedCategory.obj K))) ≫
                inv ((TStructure.t.truncGEπ c).app
                  (RH₂.obj (Φ.mapDerivedCategory.obj K)))) :=
    mid_formal _ _ _ _ _ _ _ _ _ _ hΨ hθ ((singleFunctor D₂ c).map_comp _ _)
      (map_comp_eq_id _ (Iso.inv_hom_id_app (Ψ.mapDerivedCategoryHomologyIso c) (RH₁.obj K)))
      (Iso.hom_inv_id_app _ _)
  -- the single functor of `P₂` moved past the comparison of the cohomology objects
  have hsingle : P₂.mapDerivedCategory.map
        ((singleFunctor D₂ c).map
          ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
            (homologyFunctor D₂ c).map (θ.hom.app K))) =
      (P₂.mapDerivedCategorySingleFunctor c).hom.app
          (Ψ.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
        (singleFunctor C₂ c).map
            (P₂.map ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
              (homologyFunctor D₂ c).map (θ.hom.app K))) ≫
          (P₂.mapDerivedCategorySingleFunctor c).inv.app
            ((homologyFunctor D₂ c).obj (RH₂.obj (Φ.mapDerivedCategory.obj K))) := by
    have h := (P₂.mapDerivedCategorySingleFunctor c).hom.naturality
      ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
        (homologyFunctor D₂ c).map (θ.hom.app K))
    simp only [Functor.comp_map] at h
    exact Eq.trans (cancel_formal _ _ _ _ h (Iso.hom_inv_id_app _ _))
      (Category.assoc _ _ _)
  have hmid : P₂.mapDerivedCategory.map
          (Ψ.mapDerivedCategory.map
            ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app (RH₁.obj K) ≫
              (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app (RH₁.obj K)) ≫
                inv ((TStructure.t.truncGEπ c).app (RH₁.obj K)))) ≫
        P₂.mapDerivedCategory.map (θ.hom.app K) =
      P₂.mapDerivedCategory.map
          ((Ψ.mapDerivedCategorySingleFunctor c).hom.app
            ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
        (P₂.mapDerivedCategorySingleFunctor c).hom.app
            (Ψ.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
          (singleFunctor C₂ c).map
              (P₂.map ((Ψ.mapDerivedCategoryHomologyIso c).inv.app (RH₁.obj K) ≫
                (homologyFunctor D₂ c).map (θ.hom.app K))) ≫
            (P₂.mapDerivedCategorySingleFunctor c).inv.app
                ((homologyFunctor D₂ c).obj (RH₂.obj (Φ.mapDerivedCategory.obj K))) ≫
              P₂.mapDerivedCategory.map
                ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app
                    (RH₂.obj (Φ.mapDerivedCategory.obj K)) ≫
                  (TStructure.t.truncGE c).map
                      ((TStructure.t.truncLTι (c + 1)).app
                        (RH₂.obj (Φ.mapDerivedCategory.obj K))) ≫
                    inv ((TStructure.t.truncGEπ c).app
                      (RH₂.obj (Φ.mapDerivedCategory.obj K)))) := by
    rw [← P₂.mapDerivedCategory.map_comp, hΨθ, P₂.mapDerivedCategory.map_comp,
      P₂.mapDerivedCategory.map_comp, hsingle]
    simp only [Category.assoc]
  -- the first factor, by `pushCompare_single`
  have hfirst := first_formal
    (Φ.mapDerivedCategory.map
      ((P₁.mapDerivedCategorySingleFunctor c).hom.app
        ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    (Φ.mapDerivedCategory.map
      ((P₁.mapDerivedCategorySingleFunctor c).inv.app
        ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    ((Φ.mapDerivedCategorySingleFunctor c).hom.app
      (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    ((pushCompare P₁ Φ Ψ P₂ ν).hom.app
        ((singleFunctor D₁ c).obj ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
      P₂.mapDerivedCategory.map
          ((Ψ.mapDerivedCategorySingleFunctor c).hom.app
            ((homologyFunctor D₁ c).obj (RH₁.obj K))) ≫
        (P₂.mapDerivedCategorySingleFunctor c).hom.app
          (Ψ.obj ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    ((singleFunctor C₂ c).map (ν.inv.app ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    ((singleFunctor C₂ c).map (ν.hom.app ((homologyFunctor D₁ c).obj (RH₁.obj K))))
    (Eq.trans (pushCompare_single P₁ Φ Ψ P₂ ν c _) (by simp only [Category.assoc]))
    (map_comp_eq_id _ (Iso.inv_hom_id_app ν _))
    (map_comp_eq_id _ (Iso.inv_hom_id_app (P₁.mapDerivedCategorySingleFunctor c) _))
  rw [edge_eq RH₁ P₁ ε₁ c K, edge_eq RH₂ P₂ ε₂ c (Φ.mapDerivedCategory.obj K),
    edgeSourceCompare_eq, Functor.map_comp, Functor.map_comp]
  exact chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hε K) hnat hmid hfirst

/-- The formal rearrangement of `mapDerivedCategory_edge_square`, at a variable category: `hnat`
is the naturality of the second edge morphism and `ht` the square on the sources.  Stated
abstractly and applied with `exact` for the reason recorded on `paste`. -/
private lemma chase_square {V : Type*} [Category* V] {a b k d a' b' : V}
    (e : a ⟶ b) (ed : b ⟶ k) (g : k ⟶ d) (t : a ⟶ a') (e' : a' ⟶ b') (ed' : b' ⟶ d)
    (m : b ⟶ b') (hnat : m ≫ ed' = ed ≫ g) (ht : t ≫ e' = e ≫ m) :
    (e ≫ ed) ≫ g = t ≫ e' ≫ ed' := by
  rw [Category.assoc, ← hnat, ← Category.assoc, ← ht, Category.assoc]

/-- **The square of [Stacks, Tag 0G8B] for the image of the edge morphism, reduced to a square
between the two single complexes in degree `c`.**  Granted `CounitCompatible`, the image under
`Φᴰ` of the edge morphism is natural along an *arbitrary* morphism `g` of the target category —
not only along the image of a morphism of `DerivedCategory C₁` — as soon as the corresponding
arrow `t` on the sources makes the square `ht` commute against `edgeSourceCompare`.

`mapDerivedCategory_edge` replaces both images of the edge morphism by `edgeSourceCompare`
followed by the edge morphism of the other side, `edge_naturality` carries `g` across the second
edge morphism, and `ht` is then exactly what is left.  The point of the statement is that
everything about derived categories has been discharged: `ht` mentions only morphisms between
objects placed in a single degree. -/
theorem mapDerivedCategory_edge_square
    (hε : CounitCompatible P₁ Φ Ψ P₂ ν RH₁ RH₂ θ ε₁ ε₂) (c : ℤ) (K K' : DerivedCategory C₁)
    [(RH₁.obj K).IsGE c] [(RH₁.obj K').IsGE c]
    (g : Φ.mapDerivedCategory.obj K ⟶ Φ.mapDerivedCategory.obj K')
    (t : Φ.mapDerivedCategory.obj
          ((singleFunctor C₁ c).obj (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K)))) ⟶
        Φ.mapDerivedCategory.obj
          ((singleFunctor C₁ c).obj (P₁.obj ((homologyFunctor D₁ c).obj (RH₁.obj K')))))
    (ht : t ≫ edgeSourceCompare P₁ Φ Ψ P₂ ν RH₁ RH₂ θ c K' =
      edgeSourceCompare P₁ Φ Ψ P₂ ν RH₁ RH₂ θ c K ≫
        (singleFunctor C₂ c).map
          (P₂.map ((homologyFunctor D₂ c).map (RH₂.map g)))) :
    Φ.mapDerivedCategory.map (edge RH₁ P₁ ε₁ c K) ≫ g =
      t ≫ Φ.mapDerivedCategory.map (edge RH₁ P₁ ε₁ c K') := by
  have hGE : (RH₂.obj (Φ.mapDerivedCategory.obj K)).IsGE c :=
    isGE_obj_mapDerivedCategory Φ Ψ RH₁ RH₂ c K (θ.app K)
  have hGE' : (RH₂.obj (Φ.mapDerivedCategory.obj K')).IsGE c :=
    isGE_obj_mapDerivedCategory Φ Ψ RH₁ RH₂ c K' (θ.app K')
  have hnat := edge_naturality RH₂ P₂ ε₂ c (K := Φ.mapDerivedCategory.obj K)
    (K' := Φ.mapDerivedCategory.obj K') g
  rw [mapDerivedCategory_edge P₁ Φ Ψ P₂ ν RH₁ RH₂ θ ε₁ ε₂ hε c K,
    mapDerivedCategory_edge P₁ Φ Ψ P₂ ν RH₁ RH₂ θ ε₁ ε₂ hε c K']
  exact chase_square _ _ _ _ _ _ _ hnat ht

end Stacks.CounitGysinEdge

end
