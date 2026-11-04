module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationSheafCondition
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-!
# The sheaf condition across the localization of Stacks 06W0, read through fibre products

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over a
scheme `U`, and `{φ i : z i ⟶ x}` a family of arrows of `𝒳`.
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost` moves the sheaf condition for a
presheaf `P` on `𝒳` and that family to the big fppf site of `U`, where the images `{U_i → U}` of
the family live.  The sheaf condition it lands in is still
`CategoryTheory.Presieve.IsSheafFor`, whose compatibility condition
`CategoryTheory.Presieve.Arrows.Compatible` quantifies over an *arbitrary* test object of the
site and an arbitrary pair of arrows from it into the `U_i`.

This file cuts that quantifier down.  Fibre products exist on the big fppf site of `U`
(`AlgebraicGeometry.hasPullbacks_bigFppfOver`), and they do not exist on `𝒳`; so once the sheaf
condition is downstairs, Mathlib's `CategoryTheory.Presieve.Arrows.pullbackCompatible_iff`
replaces compatibility against every test object by compatibility against the *pairwise fibre
products* `U_i ×_U U_j` alone, and
`CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition` reads the resulting condition as the
fork diagram of **Stacks 00VM** being an equalizer.

Why that matters for **Stacks 076T**: the objects which survive the cut are the `U_i / U` and the
`(U_i ×_U U_j) / U`, and all of them lie over a morphism to `U` which is flat and locally of
finite presentation as soon as the `U_i → U` are — a fibre product projection is a base change,
and flatness and local finite presentation are stable under base change and under composition.
That is exactly the class of arrows hypothesis (b) of Stacks 076T
(`AlgebraicGeometry.Stack.HasFlatLfpBaseChangeProperty`) speaks about, whereas the uncut
condition reaches outside it.  The flatness and local finite presentation of those objects are
proved here as well, so the reduction is certified to stay inside hypothesis (b)'s class.

## Main definitions

* `AlgebraicGeometry.Stack.overPostEquivalence`: the localization functor of Stacks 06W0 packaged
  as an equivalence of categories.
* `AlgebraicGeometry.Stack.overPostTransport`: the presheaf on the big fppf site of `U` obtained
  from a presheaf on `𝒳` by transport along that equivalence, together with
  `AlgebraicGeometry.Stack.overPostTransportIso`, the identification its restriction to `𝒳/x`
  satisfies.  These supply, at no cost, the data the hypothesis `e` of
  `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost` asks for.

## Main results

* `AlgebraicGeometry.prop_hom_pullback`: an object of the big fppf site of `V` obtained as a
  fibre product lies over a morphism in any class of morphisms of schemes stable under base
  change and composition, as soon as the two objects it is formed from do.
* `AlgebraicGeometry.flat_hom_pullback_toMkId`,
  `AlgebraicGeometry.locallyOfFinitePresentation_hom_pullback_toMkId`: the pairwise fibre
  products of a family `{U_i / U}` lie over flat morphisms locally of finite presentation when
  the `U_i → U` do.
* `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost`: **the equalizer
  reduction.**  The sheaf condition for `P` and `{φ i}` on `𝒳` is the condition, downstairs on
  the big fppf site of `U`, that every family of elements compatible on the pairwise fibre
  products has a unique amalgamation.
* `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPostTransport`: the
  same with no hypothesis at all, the presheaf downstairs being the transported one.
* `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_isLimit_fork_overPost`: the same condition
  written as the fork diagram of Stacks 00VM being an equalizer.
* `AlgebraicGeometry.Stack.flat_hom_pullback_overPost`,
  `AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost`: the objects the
  reduced condition quantifies over lie over flat morphisms locally of finite presentation.

## Implementation notes

The transported presheaf is the inverse image along the inverse of the localization equivalence,
and the identification `e` it satisfies is Mathlib's
`CategoryTheory.Equivalence.funInvIdAssoc` for the opposite equivalence; both are free, which is
what makes
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPostTransport`
hypothesis-free.  The `e`-carrying form is kept because a consumer which has another presheaf
downstairs — the `G^a` of the proof of Stacks 076T, say — wants the statement for that presheaf
and not for the transport.

The fork form carries a `Small` hypothesis on the indexing type, which the compatibility form
does not: Mathlib's fork diagram is a product indexed by `I`, so it only exists once `I` is small
relative to the universe of the presheaf's values.  Nothing else distinguishes the two.

Fibre products of the slice are computed by the forgetful functor, which preserves them because
`WalkingCospan` is connected; composing it with the inclusion of the big fppf site into schemes
turns a fibre product of the site into a fibre product of schemes, which is where base-change
stability of a morphism property is applied.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 00VM](https://stacks.math.columbia.edu/tag/00VM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u v w

namespace AlgebraicGeometry

/-! ### Fibre products in the big fppf site of a scheme -/

section FibreProducts

variable (B : BigFppfSite.{u})

/-- **A fibre product of the big fppf site of `V` lies over a fibre product of schemes.**  The
forgetful functor of the slice preserves fibre products, `WalkingCospan` being connected, and so
does the inclusion of the big fppf site into schemes; so the underlying square of schemes of a
fibre product square of `Sch/V` is a fibre product square. -/
theorem isPullback_inclusion_left {V : B.Schemes} {W₁ W₂ T : Over V} (a : W₁ ⟶ T) (b : W₂ ⟶ T) :
    IsPullback (B.inclusion.map (pullback.fst a b).left)
        (B.inclusion.map (pullback.snd a b).left)
      (B.inclusion.map a.left) (B.inclusion.map b.left) :=
  (IsPullback.of_hasPullback a b).map (Over.forget V ⋙ B.inclusion)

/-- **A fibre product of the big fppf site of `V` lies over `V` by a morphism in any class stable
under base change and composition.**  The structure morphism of `W₁ ×_T W₂` to `V` factors as the
first projection followed by the structure morphism of `W₁`, and the first projection lies over a
base change of the morphism below `b`. -/
theorem prop_hom_pullback (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {V : B.Schemes} {W₁ W₂ T : Over V} (a : W₁ ⟶ T) (b : W₂ ⟶ T)
    (h₁ : P (B.inclusion.map W₁.hom)) (h₂ : P (B.inclusion.map b.left)) :
    P (B.inclusion.map (pullback a b).hom) := by
  rw [← Over.w (pullback.fst a b), B.inclusion.map_comp]
  exact P.comp_mem _ _
    (MorphismProperty.of_isPullback (isPullback_inclusion_left B a b).flip h₂) h₁

/-- **The pairwise fibre products of a family of objects of the big fppf site of `V` lie over `V`
flatly.**  This is the first half of the certification that the reduced sheaf condition of
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost` only looks at
objects lying over a flat morphism locally of finite presentation. -/
theorem flat_hom_pullback_toMkId {V X₁ X₂ : B.Schemes} (f₁ : X₁ ⟶ V) (f₂ : X₂ ⟶ V)
    (h₁ : Flat (B.inclusion.map f₁)) (h₂ : Flat (B.inclusion.map f₂)) :
    Flat (B.inclusion.map (pullback
      (Over.homMk f₁ (by simp) : Over.mk f₁ ⟶ Over.mk (𝟙 V))
      (Over.homMk f₂ (by simp) : Over.mk f₂ ⟶ Over.mk (𝟙 V))).hom) :=
  prop_hom_pullback B _ _ _ h₁ h₂

/-- **The pairwise fibre products of a family of objects of the big fppf site of `V` lie over `V`
by a morphism locally of finite presentation.**  This is the second half of the certification
that the reduced sheaf condition of
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost` only looks at
objects lying over a flat morphism locally of finite presentation. -/
theorem locallyOfFinitePresentation_hom_pullback_toMkId {V X₁ X₂ : B.Schemes} (f₁ : X₁ ⟶ V)
    (f₂ : X₂ ⟶ V) (h₁ : LocallyOfFinitePresentation (B.inclusion.map f₁))
    (h₂ : LocallyOfFinitePresentation (B.inclusion.map f₂)) :
    LocallyOfFinitePresentation (B.inclusion.map (pullback
      (Over.homMk f₁ (by simp) : Over.mk f₁ ⟶ Over.mk (𝟙 V))
      (Over.homMk f₂ (by simp) : Over.mk f₂ ⟶ Over.mk (𝟙 V))).hom) :=
  prop_hom_pullback B _ _ _ h₁ h₂

end FibreProducts

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x : 𝒳) (P : 𝒳ᵒᵖ ⥤ Type t)
  (Q : (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ Type t)

/-! ### The equalizer reduction -/

include hp in
/-- **The equalizer reduction of the sheaf condition across the localization of Stacks 06W0.**
Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over
a scheme `U`, and `{φ i : z i ⟶ x}` a family of arrows of `𝒳` lying over `{f i : U_i → U}`.  Let
`P` be a presheaf on `𝒳` and `Q` a presheaf on the big fppf site of `U` whose restriction along
the localization functor is the restriction of `P` to `𝒳/x`.  Then `P` satisfies the sheaf
condition for `{φ i}` if and only if every family of elements of `Q` over the `U_i / U` which
agrees on the pairwise fibre products `U_i ×_U U_j` has a unique amalgamation.

This is `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost` followed by Mathlib's
`CategoryTheory.Presieve.Arrows.pullbackCompatible_iff`.  The point of the composite is which
objects the condition still mentions: the uncut compatibility condition
`CategoryTheory.Presieve.Arrows.Compatible` quantifies over an arbitrary object of the site, and
after the cut only the `U_i / U` and the `(U_i ×_U U_j) / U` remain — all of which lie over a
flat morphism locally of finite presentation whenever the `f i` do, by
`AlgebraicGeometry.Stack.flat_hom_pullback_overPost` and
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost`.  The cut is
available here and not on `𝒳`, because the big fppf site of `U` has fibre products
(`AlgebraicGeometry.hasPullbacks_bigFppfOver`) and `𝒳` need not. -/
theorem isSheafFor_ofArrows_iff_pullbackCompatible_overPost {I : Type*} {z : I → 𝒳}
    (φ : ∀ i, z i ⟶ x)
    (e : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙ Q ≅ (Over.forget x).op ⋙ P) :
    Presieve.IsSheafFor P (Presieve.ofArrows z φ) ↔
      ∀ y : (i : I) → Q.obj (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)))),
        Presieve.Arrows.PullbackCompatible Q
            (fun i ↦ (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
                Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))) y →
          ∃! s, ∀ i, Q.map (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
                Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))).op s = y i := by
  rw [isSheafFor_ofArrows_iff_overPost B S hS p hp x P Q φ e,
    Presieve.isSheafFor_arrows_iff_pullbacks]

include hp in
/-- **The equalizer reduction, as the fork diagram of Stacks 00VM.**  The reduced sheaf condition
of `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost` says exactly
that the fork

`Q(U/U) ⟶ ∏ᵢ Q(Uᵢ/U) ⇉ ∏ᵢⱼ Q((Uᵢ ×_U Uⱼ)/U)`

is an equalizer.  The indexing type has to be small relative to the universe of the presheaf's
values for the two products to exist; no other hypothesis is added to
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost`. -/
theorem isSheafFor_ofArrows_iff_isLimit_fork_overPost {I : Type*} [Small.{t} I] {z : I → 𝒳}
    (φ : ∀ i, z i ⟶ x)
    (e : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙ Q ≅ (Over.forget x).op ⋙ P) :
    Presieve.IsSheafFor P (Presieve.ofArrows z φ) ↔
      Nonempty (IsLimit (Fork.ofι
        (Equalizer.Presieve.Arrows.forkMap Q
          (fun i ↦ Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)))
          (fun i ↦ (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
            Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
              Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))))
        (Equalizer.Presieve.Arrows.w Q _ _))) := by
  rw [isSheafFor_ofArrows_iff_overPost B S hS p hp x P Q φ e,
    Equalizer.Presieve.Arrows.sheaf_condition]

/-! ### The transported presheaf, which supplies the identification for free -/

/-- The localization functor of **Stacks 06W0** packaged as an equivalence of categories, by
`AlgebraicGeometry.Stack.isEquivalence_overPost`. -/
noncomputable def overPostEquivalence : Over x ≌ Over ((p ⋙ Over.forget (B.obj hS)).obj x) :=
  haveI := isEquivalence_overPost B S hS p hp x
  (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence

/-- The functor of `AlgebraicGeometry.Stack.overPostEquivalence` is the localization functor
`Over.post (p ⋙ Over.forget (B.obj hS))`. -/
@[simp]
theorem overPostEquivalence_functor :
    (overPostEquivalence B S hS p hp x).functor =
      Over.post (X := x) (p ⋙ Over.forget (B.obj hS)) :=
  rfl

/-- The presheaf on the big fppf site of `U` transported from a presheaf `P` on `𝒳` along the
localization equivalence of **Stacks 06W0**: the inverse image, along the inverse of that
equivalence, of the restriction of `P` to the slice `𝒳/x`. -/
noncomputable def overPostTransport : (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ Type t :=
  (overPostEquivalence B S hS p hp x).inverse.op ⋙ (Over.forget x).op ⋙ P

/-- **The identification the transported presheaf satisfies for free.**  Restricting
`AlgebraicGeometry.Stack.overPostTransport` back along the localization functor returns the
restriction of `P` to `𝒳/x`.  This is the hypothesis `e` of
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost` and of
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost`, supplied at no
cost; it is the unit of the localization equivalence, in the form
`CategoryTheory.Equivalence.funInvIdAssoc`. -/
noncomputable def overPostTransportIso :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙ overPostTransport B S hS p hp x P ≅
      (Over.forget x).op ⋙ P :=
  (overPostEquivalence B S hS p hp x).op.funInvIdAssoc ((Over.forget x).op ⋙ P)

include hp in
/-- **The equalizer reduction, with nothing assumed.**  For a presheaf `P` on `𝒳` and a family of
arrows `{φ i : z i ⟶ x}` of `𝒳`, the sheaf condition for `P` and `{φ i}` is the condition, on the
big fppf site of the scheme `U` below `x`, that every family of elements of the transported
presheaf over the `U_i / U` which agrees on the pairwise fibre products `U_i ×_U U_j` has a
unique amalgamation.

This is
`AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPost` for the presheaf
`AlgebraicGeometry.Stack.overPostTransport`, whose identification
`AlgebraicGeometry.Stack.overPostTransportIso` is free.  It is the form in which the sheaf
condition on `𝒳` lands on the big fppf site of `U` without any hypothesis being incurred. -/
theorem isSheafFor_ofArrows_iff_pullbackCompatible_overPostTransport {I : Type*} {z : I → 𝒳}
    (φ : ∀ i, z i ⟶ x) :
    Presieve.IsSheafFor P (Presieve.ofArrows z φ) ↔
      ∀ y : (i : I) → (overPostTransport B S hS p hp x P).obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)))),
        Presieve.Arrows.PullbackCompatible (overPostTransport B S hS p hp x P)
            (fun i ↦ (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
                Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))) y →
          ∃! s, ∀ i, (overPostTransport B S hS p hp x P).map
              (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
                Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
                  Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))).op s = y i :=
  isSheafFor_ofArrows_iff_pullbackCompatible_overPost B S hS p hp x P _ φ
    (overPostTransportIso B S hS p hp x P)

/-! ### The reduced condition stays inside the class of hypothesis (b) of Stacks 076T -/

/-- **The pairwise fibre products the reduced sheaf condition mentions lie over flat
morphisms.**  Together with
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost` this is what makes
the cut from `CategoryTheory.Presieve.Arrows.Compatible` to
`CategoryTheory.Presieve.Arrows.PullbackCompatible` worth making for Stacks 076T: hypothesis (b)
of that lemma speaks only about arrows lying over a morphism which is flat and locally of finite
presentation, and these are the objects the reduced condition quantifies over. -/
theorem flat_hom_pullback_overPost {I : Type*} {z : I → 𝒳} (φ : ∀ i, z i ⟶ x)
    (hflat : ∀ i, Flat (B.inclusion.map (p.map (φ i)).left)) (i j : I) :
    Flat (B.inclusion.map (pullback
      (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
        Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
          Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
      (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ j)) (by simp) :
        Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ j)) ⟶
          Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))).hom) :=
  flat_hom_pullback_toMkId B _ _ (hflat i) (hflat j)

/-- **The pairwise fibre products the reduced sheaf condition mentions lie over morphisms locally
of finite presentation.**  The companion of
`AlgebraicGeometry.Stack.flat_hom_pullback_overPost`. -/
theorem locallyOfFinitePresentation_hom_pullback_overPost {I : Type*} {z : I → 𝒳}
    (φ : ∀ i, z i ⟶ x)
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (p.map (φ i)).left)) (i j : I) :
    LocallyOfFinitePresentation (B.inclusion.map (pullback
      (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
        Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
          Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
      (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ j)) (by simp) :
        Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ j)) ⟶
          Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))).hom) :=
  locallyOfFinitePresentation_hom_pullback_toMkId B _ _ (hlfp i) (hlfp j)

end Stack

end AlgebraicGeometry

end
