module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# The Rim–Schlessinger condition for the schemes over a fixed object

A slice category `𝒞/T` is fibred in groupoids over `𝒞`, and its fibre over an object `Z`
is the set of morphisms `Z ⟶ T`, carrying only identity morphisms. So for a commutative
square

```
U ---f---> V
|          |
g          i
|          |
v          v
W ---j---> Z
```

in `𝒞`, the comparison functor from the fibre of `𝒞/T` over `Z` to the two-fibre product of
the fibres over `V` and `W` over the fibre over `U` is an equivalence exactly when `Z` is a
pushout of the square *as tested on `T`*: morphisms out of `Z` into `T` are pairs of
compatible morphisms out of `V` and out of `W`. That is the content of this file, and it is
the special case of **Stacks 07WN** — algebraic stacks satisfy (RS) — for a *representable*
stack, where the pushouts of algebraic spaces the general case needs (Stacks 07VX, 07W3,
07SY) are replaced by the universal property of the pushout in the ambient category itself.

The two consequences recorded are that the category of schemes over an object of the big
fppf site satisfies condition (RS) of Tag 07WP, in both of the shapes this development
states that condition in: over the big fppf site itself
(`Deformation.Artin.SatisfiesRS`) and over the category of all schemes over the base
(`Deformation.Artin.SatisfiesRSOver`). This is the instance of Stacks 07WQ — every
algebraic stack satisfies (RS) — that the proof of Stacks 07XG opens with.

## Main definitions

* `Deformation.Artin.sliceBase` — the structure morphism `Z ⟶ T` of an object of the fibre
  of `𝒞/T` over `Z`, and `Deformation.Artin.sliceFiberMk` the object of that fibre attached
  to a morphism `Z ⟶ T`. These two identify the fibre with the morphisms `Z ⟶ T`.
* `Deformation.Artin.sliceFiberHom` — the morphism of the fibre between two objects with the
  same structure morphism.

## Main results

* `Deformation.Artin.isEquivalence_fiberSquareComparison_over_forget` — the comparison
  functor of a square is an equivalence for a slice category, given that morphisms into `T`
  see the square as a pushout.
* `Deformation.Artin.isEquivalence_fiberSquareComparison_over_forget_of_isPushout` — the same
  for a square which is a pushout in the ambient category.
* `Deformation.Artin.satisfiesRS_over_forget` — the category of schemes over an object of the
  big fppf site satisfies (RS) in the site shape of Tag 07WP.
* `Deformation.Artin.satisfiesRSOver_over_forget` — the same in the shape over the category of
  all schemes over the base.

## Implementation notes

The two hypotheses `huniq` and `hdesc` of the main theorem are the universal property of the
pushout tested on the single object `T`, rather than `CategoryTheory.IsPushout` in `𝒞`. They
have to be in that shape to be usable: in both applications the square is given as a pushout
of the underlying *schemes*, while the fibred category is a slice of the big fppf site, or of
the schemes over the base, whose morphisms are morphisms of schemes *over the base*. Testing
on `T` is what lets the descended morphism be lifted back: a morphism of schemes out of the
pushout is a morphism of the ambient category as soon as it commutes with the structure
morphisms, and that commutation is itself an instance of the uniqueness half.

No choice of pullbacks is preferred: the statement is for an arbitrary
`CategoryTheory.Functor.ChoiceOfPullbacks`, which is what the two conditions (RS) quantify
over — the site shape at the canonical choice, and the shape over all schemes at a given one.

Both the fibre of the slice and the categorical pullback of two of its pullback functors have
at most one morphism between any two objects (`Deformation.Artin.slice_fiber_hom_ext`), so
every compatibility square of morphisms demanded by `CategoryTheory.Limits.CategoricalPullback`
holds for free, and the whole proof is the bijection between objects.

### What this does not give, and what Stacks 0CXM is blocked on

`Deformation.Artin.satisfiesRSOver_over_forget` discharges the hypothesis `hRS` of
`Deformation.Artin.changeOfFieldFunctor_isEquivalence` (Stacks 07WX) for the slice side of
the comparison that Stacks 07XG is about, namely for `(Sch/T)`. It does *not* unblock
Stacks 07XG, and the obstruction is not this instance of (RS).

Stacks 07XG — versality at `u₀` and (RS) imply that
`𝓕_{(Sch/U),l,u_{l,0}} ⟶ 𝓕_{𝒳,l,x_{l,0}}` is smooth for `l/κ(u₀)` finite — is carried, for a
site-presented `𝒳`, by
`Deformation.Artin.isSmoothOnPredeformationCategories_sliceFunctor_of_isVersalAt`'s neighbour
`Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt` in
`StacksFrontier/Deformation/Artin/Versality/FiniteResidueFieldExtension.lean`, and Stacks 0CXM by
`Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt` in
`StacksFrontier/Deformation/ArtinCriteria/VersalBaseChange.lean`. Both are unconditional.

Its route here is Stacks 07WX for `𝒳` itself, followed by Stacks 07WD
(`Deformation.isSmooth_changeOfFields`). Stacks 07WX in the form
`Deformation.Artin.changeOfFieldFunctor_isEquivalence` is unusable for this, since its
hypotheses `q.IsFiberedInGroupoids` and `q.ChoiceOfPullbacks` are for `q : 𝒳 ⥤ Over S`, i.e.
fibredness over the category of *all* schemes over `S`, and for a `𝒳` fibred in groupoids over
the big fppf site — the shape in which Stacks 0G2J and 0G2S are carried, in
`StacksFrontier/Deformation/Artin/Versality/NonversalThickening.lean` and
`StacksFrontier/Deformation/Artin/Versality/NonversalThickeningSequence.lean` — neither datum is
inhabited, by `Deformation.Artin.not_isFiberedInGroupoids_comp_post` and
`Deformation.Artin.not_nonempty_choiceOfPullbacks_comp_post`. What settled it was re-deriving
Stacks 07WX over the site, with (RS) as `Deformation.Artin.SatisfiesRS`:
`Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence` in
`StacksFrontier/Deformation/Artin/ChangeOfField/SiteRestriction.lean`. The slice is not where that
difficulty sat, which is what the two theorems below settle, and the `hRS` they discharge is the
hypothesis that site form takes.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
* [Stacks Project, Tag 07XG](https://stacks.math.columbia.edu/tag/07XG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u u₁ v₁

/-! ### The fibres of a slice category -/

section Slice

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {T : 𝒞}

/-- The structure morphism `Z ⟶ T` of an object of the fibre of the slice `𝒞/T` over `Z`. -/
public def sliceBase {Z : 𝒞} (a : (Over.forget T).Fiber Z) : Z ⟶ T :=
  eqToHom a.2.symm ≫ a.1.hom

/-- The object of the fibre of the slice `𝒞/T` over `Z` attached to a morphism `Z ⟶ T`. -/
public def sliceFiberMk {Z : 𝒞} (z : Z ⟶ T) : (Over.forget T).Fiber Z :=
  ⟨Over.mk z, rfl⟩

/-- The structure morphism of the fibre object attached to `z : Z ⟶ T` is `z`. -/
@[simp]
public theorem sliceBase_sliceFiberMk {Z : 𝒞} (z : Z ⟶ T) :
    sliceBase (sliceFiberMk z) = z := by
  simp only [sliceBase, sliceFiberMk]
  exact Category.id_comp z

/-- The fibre of a slice category has at most one morphism between any two objects: a
morphism of `𝒞/T` lying over an identity is the identity on underlying objects. -/
public theorem slice_fiber_hom_ext {Z : 𝒞} {a b : (Over.forget T).Fiber Z} (φ ψ : a ⟶ b) :
    φ = ψ := by
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have hφ := CategoryTheory.IsHomLift.fac' (Over.forget T) (𝟙 Z)
    (Functor.Fiber.fiberInclusion.map φ)
  have hψ := CategoryTheory.IsHomLift.fac' (Over.forget T) (𝟙 Z)
    (Functor.Fiber.fiberInclusion.map ψ)
  exact hφ.trans hψ.symm

/-- A morphism of the fibre of a slice, read on structure morphisms. -/
public theorem sliceBase_of_hom {Z : 𝒞} {a b : (Over.forget T).Fiber Z} (φ : a ⟶ b) :
    sliceBase a = sliceBase b := by
  have hφ := CategoryTheory.IsHomLift.fac' (Over.forget T) (𝟙 Z)
    (Functor.Fiber.fiberInclusion.map φ)
  have hw : φ.1.left ≫ b.1.hom = a.1.hom := Over.w φ.1
  have hleft : φ.1.left = eqToHom a.2 ≫ 𝟙 Z ≫ eqToHom b.2.symm := hφ
  rw [hleft, Category.id_comp, eqToHom_trans] at hw
  simp only [sliceBase, ← hw, ← Category.assoc, eqToHom_trans]

/-- The morphism of the fibre of a slice between two objects carrying the same structure
morphism. -/
public def sliceFiberHom {Z : 𝒞} {a b : (Over.forget T).Fiber Z}
    (hab : sliceBase a = sliceBase b) : a ⟶ b :=
  ⟨Over.homMk (eqToHom (a.2.trans b.2.symm)) (by
      simp only [sliceBase] at hab
      calc eqToHom (a.2.trans b.2.symm) ≫ b.1.hom
          = eqToHom a.2 ≫ eqToHom b.2.symm ≫ b.1.hom := by
            rw [← Category.assoc, eqToHom_trans]
        _ = eqToHom a.2 ≫ eqToHom a.2.symm ≫ a.1.hom := by rw [← hab]
        _ = a.1.hom := by
            rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]),
    CategoryTheory.IsHomLift.of_fac' (Over.forget T) (𝟙 Z) _ a.2 b.2 (by simp)⟩

/-- Two objects of the fibre of a slice with the same structure morphism are isomorphic in
the fibre. -/
public def sliceFiberIso {Z : 𝒞} {a b : (Over.forget T).Fiber Z}
    (hab : sliceBase a = sliceBase b) : a ≅ b where
  hom := sliceFiberHom hab
  inv := sliceFiberHom hab.symm
  hom_inv_id := slice_fiber_hom_ext _ _
  inv_hom_id := slice_fiber_hom_ext _ _

/-- The structure morphism of a chosen pullback in a slice category is the composite with the
morphism pulled back along. -/
public theorem sliceBase_choiceOfPullbacks_obj (c : (Over.forget T).ChoiceOfPullbacks)
    {V Z : 𝒞} (i : V ⟶ Z) (a : (Over.forget T).Fiber Z) :
    sliceBase (c.obj i a) = i ≫ sliceBase a := by
  have : (Over.forget T).IsStronglyCartesian i (c.map i a) := c.isStronglyCartesian i a
  have hφ := CategoryTheory.IsHomLift.fac' (Over.forget T) i (c.map i a)
  have hw : (c.map i a).left ≫ a.1.hom = (c.obj i a).1.hom := Over.w (c.map i a)
  have hleft : (c.map i a).left = eqToHom (c.obj i a).2 ≫ i ≫ eqToHom a.2.symm := hφ
  rw [hleft] at hw
  simp only [sliceBase, ← hw, Category.assoc, ← Category.assoc (eqToHom (c.obj i a).2.symm),
    eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A morphism in the fibre between two chosen pullbacks identifies the composites of the
structure morphisms of the objects pulled back. -/
private theorem comp_sliceBase_eq_of_hom (c : (Over.forget T).ChoiceOfPullbacks)
    {X A B : 𝒞} (i : X ⟶ A) (i' : X ⟶ B) {a : (Over.forget T).Fiber A}
    {b : (Over.forget T).Fiber B} (φ : c.obj i a ⟶ c.obj i' b) :
    i ≫ sliceBase a = i' ≫ sliceBase b := by
  have := sliceBase_of_hom φ
  rwa [sliceBase_choiceOfPullbacks_obj, sliceBase_choiceOfPullbacks_obj] at this

/-! ### The comparison functor of a square -/

variable {U V W Z : 𝒞}

/-- **(RS) for a representable stack.** For a slice category `𝒞/T`, the comparison functor
from the fibre over `Z` to the two-fibre product of the fibres over `V` and `W` over the
fibre over `U` is an equivalence as soon as the morphisms of `𝒞` into `T` see `Z` as the
pushout of the square: they are determined by their restrictions along `i` and `j`, and every
compatible pair of morphisms out of `V` and `W` arises that way.

This is the special case of Stacks 07WN for a representable stack; the general case needs
pushouts of algebraic spaces. -/
public theorem isEquivalence_fiberSquareComparison_over_forget
    (c : (Over.forget T).ChoiceOfPullbacks)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (huniq : ∀ z z' : Z ⟶ T, i ≫ z = i ≫ z' → j ≫ z = j ≫ z' → z = z')
    (hdesc : ∀ (v : V ⟶ T) (w : W ⟶ T), f ≫ v = g ≫ w →
      ∃ z : Z ⟶ T, i ≫ z = v ∧ j ≫ z = w) :
    (fiberSquareComparison (Over.forget T) c f g i j h).IsEquivalence := by
  set F := fiberSquareComparison (Over.forget T) c f g i j h with hF
  have hobjfst : ∀ z : (Over.forget T).Fiber Z, (F.obj z).fst = c.obj i z := fun _ => rfl
  have hobjsnd : ∀ z : (Over.forget T).Fiber Z, (F.obj z).snd = c.obj j z := fun _ => rfl
  -- The fibre over `Z` is thin, so `F` is faithful outright.
  have hfaithful : F.Faithful := ⟨fun _ => slice_fiber_hom_ext _ _⟩
  have hfull : F.Full := by
    refine ⟨fun {a b} ψ => ?_⟩
    exact ⟨sliceFiberHom (huniq _ _ (comp_sliceBase_eq_of_hom c i i ψ.fst)
        (comp_sliceBase_eq_of_hom c j j ψ.snd)),
      CategoricalPullback.hom_ext (slice_fiber_hom_ext _ _) (slice_fiber_hom_ext _ _)⟩
  have hessSurj : F.EssSurj := by
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz₁, hz₂⟩ := hdesc _ _ (comp_sliceBase_eq_of_hom c f g x.iso.hom)
    refine ⟨sliceFiberMk z, ⟨CategoricalPullback.mkIso ?_ ?_ ?_⟩⟩
    · exact sliceFiberIso (by
        rw [hobjfst, sliceBase_choiceOfPullbacks_obj, sliceBase_sliceFiberMk, hz₁])
    · exact sliceFiberIso (by
        rw [hobjsnd, sliceBase_choiceOfPullbacks_obj, sliceBase_sliceFiberMk, hz₂])
    · exact slice_fiber_hom_ext _ _
  exact ⟨hfaithful, hfull, hessSurj⟩

/-- The comparison functor of a square for a slice category is an equivalence when the square
is a pushout in the ambient category. -/
public theorem isEquivalence_fiberSquareComparison_over_forget_of_isPushout
    (c : (Over.forget T).ChoiceOfPullbacks)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hpo : IsPushout f g i j) :
    (fiberSquareComparison (Over.forget T) c f g i j h).IsEquivalence :=
  isEquivalence_fiberSquareComparison_over_forget c f g i j h
    (fun _ _ h₁ h₂ => hpo.hom_ext h₁ h₂)
    (fun v w hvw => ⟨hpo.desc v w hvw, hpo.inl_desc v w hvw, hpo.inr_desc v w hvw⟩)

end Slice

/-! ### Transporting the pushout test to a slice of the ambient category -/

section Transport

universe u₂ u₃ v₂ v₃

/-- A pushout square of the underlying objects, read through a fully faithful functor, tests
as a pushout for the morphisms of a slice category into a fixed object of that slice.

Uniqueness is faithfulness together with uniqueness downstairs. For the descent, the morphism
supplied downstairs is a morphism of the ambient category by fullness, and it commutes with
the two structure morphisms by the uniqueness half applied to the structure morphism of the
target, which is what makes it a morphism of the slice. -/
public theorem pushout_test_over {𝒟 : Type u₂} [Category.{v₂} 𝒟] {ℰ : Type u₃}
    [Category.{v₃} ℰ] (G : 𝒟 ⥤ ℰ) [G.Full] [G.Faithful] {A : 𝒟}
    {X X' Y Y' : Over A} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y')
    (hpo : IsPushout (G.map i.left) (G.map j.left) (G.map i'.left) (G.map j'.left))
    (T : Over A) :
    (∀ z z' : Y' ⟶ T, j' ≫ z = j' ≫ z' → i' ≫ z = i' ≫ z' → z = z') ∧
      ∀ (v : Y ⟶ T) (u : X' ⟶ T), j ≫ v = i ≫ u →
        ∃ z : Y' ⟶ T, j' ≫ z = v ∧ i' ≫ z = u := by
  refine ⟨fun z z' h₁ h₂ => ?_, fun v u huv => ?_⟩
  · refine Over.OverMorphism.ext (G.map_injective (hpo.hom_ext ?_ ?_))
    · rw [← G.map_comp, ← G.map_comp]
      exact congrArg (fun t : X' ⟶ T => G.map t.left) h₂
    · rw [← G.map_comp, ← G.map_comp]
      exact congrArg (fun t : Y ⟶ T => G.map t.left) h₁
  · have hcond : G.map i.left ≫ G.map u.left = G.map j.left ≫ G.map v.left := by
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg (fun t : X ⟶ T => G.map t.left) huv.symm
    set d := hpo.desc (G.map u.left) (G.map v.left) hcond with hd
    have hdi : G.map i'.left ≫ d = G.map u.left := hpo.inl_desc _ _ hcond
    have hdj : G.map j'.left ≫ d = G.map v.left := hpo.inr_desc _ _ hcond
    have hpre : G.map (G.preimage d) = d := G.map_preimage d
    have hstruct : G.preimage d ≫ T.hom = Y'.hom := by
      refine G.map_injective (hpo.hom_ext ?_ ?_)
      · rw [G.map_comp, hpre, ← Category.assoc, hdi, ← G.map_comp, ← G.map_comp,
          Over.w u, Over.w i']
      · rw [G.map_comp, hpre, ← Category.assoc, hdj, ← G.map_comp, ← G.map_comp,
          Over.w v, Over.w j']
    refine ⟨Over.homMk (G.preimage d) hstruct, ?_, ?_⟩
    · refine Over.OverMorphism.ext (G.map_injective ?_)
      change G.map (j'.left ≫ G.preimage d) = G.map v.left
      rw [G.map_comp, hpre, hdj]
    · refine Over.OverMorphism.ext (G.map_injective ?_)
      change G.map (i'.left ≫ G.preimage d) = G.map u.left
      rw [G.map_comp, hpre, hdi]

end Transport

/-! ### Condition (RS) for the schemes over a fixed object -/

section RS

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The schemes over an object of the big fppf site satisfy (RS).** This is the instance of
Stacks 07WQ — every algebraic stack satisfies (RS) — for the representable stack `(Sch/T)`,
and it is the instance that the proof of Stacks 07XG opens with. Condition (RS) of Tag 07WP
hands over a square of local Artinian schemes of finite type whose underlying square of
schemes is a pushout, and for a representable stack the fibre over a corner is the set of
morphisms into `T`, so the comparison functor is an equivalence by the universal property of
that pushout alone; none of the finite-type, local Artinian or closed-immersion hypotheses is
used. -/
public theorem satisfiesRS_over_forget (T : BigFppfOver B S hS) :
    SatisfiesRS B S hS (Over.forget T) (Functor.IsFiberedInGroupoids.over_forget T) := by
  intro X X' Y Y' i j i' j' w _ _ _ _ _ _ _ _ _ hpo
  obtain ⟨huniq, hdesc⟩ := pushout_test_over B.inclusion i j i' j' hpo T
  exact isEquivalence_fiberSquareComparison_over_forget _ j i j' i' w.symm huniq hdesc

/-- **The schemes over a scheme over `S` satisfy (RS)**, in the shape of condition (RS) over
the category of *all* schemes over `S` — the shape in which Stacks 07WX is available in this
development. The proof is the one of `Deformation.Artin.satisfiesRS_over_forget`: the fibre of
a slice over a corner is the set of morphisms into `T`, so the comparison functor is an
equivalence by the universal property of the given pushout of schemes. -/
public theorem satisfiesRSOver_over_forget (T : Over S)
    (c : (Over.forget T).ChoiceOfPullbacks) : SatisfiesRSOver (Over.forget T) c := by
  intro U U' V V' i j i' j' hw _ _ _ _ _ _ _ _ _ hpo
  obtain ⟨huniq, hdesc⟩ := pushout_test_over (𝟭 Scheme.{u}) i j i' j' hpo T
  exact isEquivalence_fiberSquareComparison_over_forget c j i j' i' hw.symm huniq hdesc

end RS

end Deformation.Artin
