module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting across a thickening of finite order

Stacks 0611 gives a formally étale morphism of algebraic spaces exactly one lift in a solid
square whose right-hand side is a **first-order** thickening, and
`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening` is that
statement. This file removes the bound on the order: the same conclusion holds over an
`n`th-order thickening, for every `n`.

Formal étaleness is defined by lifting across square-zero closed immersions of affine objects
of the site (Stacks 049S, part (2)), so the extra order has to be bought somewhere. It is
bought by the tower of infinitesimal neighbourhoods: a closed immersion `i : P ⟶ Q` of objects
of the site whose defining ideal sheaf `K` satisfies `K ^ (n + 2) = 0` factors as

`P ⟶ V(K ^ (n + 1)) ⟶ Q`

where the second map is square-zero — its defining ideal sheaf is `K ^ (n + 1)`, whose square
`K ^ (2n + 2)` lies in `K ^ (n + 2) = 0` — and the first has `(n + 1)`st power of its defining
ideal sheaf vanishing. Induction on `n` then reduces lifting across `i` to `n + 1` applications
of the square-zero statements of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/FormallyEtale.lean`.

## Main results

* `Stacks.Thickenings.exists_factorization_of_ker_pow_eq_bot`: the factorization, on schemes.
* `AlgebraicGeometry.Space.exists_factorization_of_ker_pow_eq_bot`: the same factorization
  through an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_ker_pow_eq_bot` and
  `AlgebraicGeometry.Space.FormallySmooth.exists_lift_of_ker_pow_eq_bot`: uniqueness and
  existence of a lift across a closed immersion of objects of the site with nilpotent defining
  ideal sheaf, generalising the square-zero statements of Stacks 049S, parts (3) and (1).
* `AlgebraicGeometry.Space.FormallyUnramified.lifts_unique_of_isNthOrderThickening`: Stacks
  05ZY for a thickening of order `n`.
* `AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_isNthOrderThickening`: **Stacks
  0611 for a thickening of order `n`.**

## Implementation notes

The intermediate closed subscheme is produced as an object of the big fppf site over `S` by
`AlgebraicGeometry.BigFppfOver.mk`: a closed subscheme of a scheme in the site is again in the
site, by `AlgebraicGeometry.Scheme.size_lt_of_isClosedImmersion` (Stacks 000R, part (4)), and
its structure morphism is the closed immersion followed by that of the ambient object. The two
legs of the factorization are then morphisms of the site by
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`.

The scheme-level factorization is stated with the intermediate scheme existentially quantified
rather than as the subscheme of `K ^ (n + 1)` on the nose. That is not cosmetic: the site object
built from it has `AlgebraicGeometry.BigFppfOver.toScheme`-image only *reducibly* equal to that
subscheme, and rewriting across that equality produces type-incorrect motives.

Only the **order** of the thickening is bounded here, and it is bounded by nothing: every finite
order is covered. What is *not* covered is an arbitrary thickening in the sense of
`AlgebraicGeometry.Space.IsThickeningHom`, whose defining ideal is nil but need not be
nilpotent, so that no single `n` works; see the section "What is not proved" below.

## What is not proved

A thickening of algebraic spaces of unbounded order, *for a formally étale morphism*. If the
morphism being lifted against is **étale**, the unbounded case is available: it is
`AlgebraicGeometry.Space.existsUnique_lift_of_isThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleSectionExtension.lean`, which buys the
order from the open-subspace correspondence of Stacks 05ZP rather than from a tower of
infinitesimal neighbourhoods. What follows is about formal étaleness alone.

The defining ideal of a thickening has every section nilpotent, but the ideal itself need not
be nilpotent, and the tower above needs one exponent valid globally — which is exactly
`AlgebraicGeometry.Space.IsFiniteOrderThickening`, Stacks 05ZK part (3), and not Stacks 05ZK
part (1). Passing from nilpotent to nil needs a finiteness property of the morphism being lifted
against, so that a given lifting problem involves only finitely many sections and hence factors
through a finite-order sub-thickening; formal étaleness alone does not supply one. The
ring-level form of that reduction is
`Stacks.RingTheory.Smooth.exists_lift_through_fg_subideal` of
`StacksFrontier/RingTheory/Smooth/Lifting.lean`; it has no counterpart here. Étaleness bypasses the
reduction entirely rather than supplying it.

## References

* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 05ZY](https://stacks.math.columbia.edu/tag/05ZY)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Thickenings

open _root_.AlgebraicGeometry

variable {P Q : Scheme.{u}}

/-- **A closed immersion whose defining ideal sheaf has vanishing `(n + 2)`nd power factors as a
closed immersion with vanishing `(n + 1)`st power followed by a square-zero closed immersion.**
The intermediate closed subscheme is the one cut out by `K ^ (n + 1)`, for `K` the defining
ideal sheaf: the second leg is its closed immersion, whose defining ideal sheaf is `K ^ (n + 1)`
with square `K ^ (2n + 2) ≤ K ^ (n + 2) = 0`, and the first leg is the factorization of the
given closed immersion through it, whose defining ideal sheaf is `K / K ^ (n + 1)` with
`(n + 1)`st power the image of `K ^ (n + 1)`, hence zero.

This is one stage of the tower of infinitesimal neighbourhoods of
`StacksFrontier/AlgebraicGeometry/Thickenings/InfinitesimalTower.lean`, isolated in the form the
induction on the order consumes. -/
theorem exists_factorization_of_ker_pow_eq_bot (f : P ⟶ Q) [IsClosedImmersion f] {n : ℕ}
    (hker : f.ker ^ (n + 2) = ⊥) :
    ∃ (M : Scheme.{u}) (u : P ⟶ M) (v : M ⟶ Q), u ≫ v = f ∧
      IsClosedImmersion v ∧ v.ker ^ 2 = ⊥ ∧ IsClosedImmersion u ∧ u.ker ^ (n + 1) = ⊥ := by
  have hIK : f.ker ^ (n + 1) ≤ f.ker := Stacks.IdealSheaf.pow_succ_le_self f.ker n
  have hlift : (f.ker ^ (n + 1)).subschemeι.ker ≤ f.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨(f.ker ^ (n + 1)).subscheme, IsClosedImmersion.lift _ f hlift,
    (f.ker ^ (n + 1)).subschemeι, IsClosedImmersion.lift_fac _ _ _, inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.ker_subschemeι, ← pow_mul]
    exact le_bot_iff.1 (hker ▸ idealSheaf_pow_le_pow_right (by omega))
  · have h1 : IsClosedImmersion
        (IsClosedImmersion.lift (f.ker ^ (n + 1)).subschemeι f hlift ≫
          (f.ker ^ (n + 1)).subschemeι) := by
      rw [IsClosedImmersion.lift_fac]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ (f.ker ^ (n + 1)).subschemeι
  · have hc : IsClosedImmersion.lift (f.ker ^ (n + 1)).subschemeι f hlift
        = f.toImage ≫ Scheme.IdealSheafData.inclusion hIK := by
      refine (cancel_mono (f.ker ^ (n + 1)).subschemeι).1 ?_
      rw [IsClosedImmersion.lift_fac, Category.assoc,
        Scheme.IdealSheafData.inclusion_subschemeι]
      exact (Scheme.Hom.toImage_imageι f).symm
    rw [hc, Scheme.Hom.ker_comp_of_isIso, ker_inclusion_pow_eq_bot hIK le_rfl]

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

open Stacks.Thickenings

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf category over `S` commutes with the structure morphisms of its
source and target, read as morphisms of schemes. -/
theorem comp_inclusion_map_hom {P Q : BigFppfOver B S hS} (i : P ⟶ Q) :
    (BigFppfOver.toScheme B S hS).map i ≫ B.inclusion.map Q.hom = B.inclusion.map P.hom := by
  rw [show (BigFppfOver.toScheme B S hS).map i = B.inclusion.map i.left from rfl,
    ← Functor.map_comp, Over.w]

/-- **A closed immersion of objects of the big fppf site over `S` whose defining ideal sheaf has
vanishing `(n + 2)`nd power factors through an object of the site, as a closed immersion with
vanishing `(n + 1)`st power followed by a square-zero closed immersion.**

The intermediate scheme of `Stacks.Thickenings.exists_factorization_of_ker_pow_eq_bot` is a
closed subscheme of an object of the site, hence an object of the site by Stacks 000R part (4),
and both legs of the factorization are morphisms over `S`. -/
theorem exists_factorization_of_ker_pow_eq_bot {P Q : BigFppfOver B S hS} {i : P ⟶ Q}
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map i))
    {n : ℕ} (hker : ((BigFppfOver.toScheme B S hS).map i).ker ^ (n + 2) = ⊥) :
    ∃ (W : BigFppfOver B S hS) (u : P ⟶ W) (v : W ⟶ Q), u ≫ v = i ∧
      IsSquareZeroClosedImmersion B S hS v ∧
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map u) ∧
      ((BigFppfOver.toScheme B S hS).map u).ker ^ (n + 1) = ⊥ := by
  have := hci
  obtain ⟨M, u', v', hfac, hciv, hsqv, hciu, hkeru⟩ :=
    Stacks.Thickenings.exists_factorization_of_ker_pow_eq_bot
      ((BigFppfOver.toScheme B S hS).map i) hker
  have := hciv
  have hWsize : B.Contains M := Scheme.size_lt_of_isClosedImmersion v' Q.left.property
  obtain ⟨v, hv⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hWsize (v' ≫ B.inclusion.map Q.hom)) (Y := Q) v' rfl
  have htri : u' ≫ (v' ≫ B.inclusion.map Q.hom) = B.inclusion.map P.hom := by
    rw [← Category.assoc, hfac]
    exact comp_inclusion_map_hom B S hS i
  obtain ⟨u, hu⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := P) (Y := BigFppfOver.mk B S hS hWsize (v' ≫ B.inclusion.map Q.hom)) u' htri
  refine ⟨_, u, v, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · apply BigFppfOver.map_toScheme_injective B S hS
    show (BigFppfOver.toScheme B S hS).map (u ≫ v) = (BigFppfOver.toScheme B S hS).map i
    rw [Functor.map_comp, hu, hv]
    exact hfac
  · rwa [hv]
  · rwa [hv]
  · rwa [hu]
  · rwa [hu]

/-- A closed immersion of objects of the site whose defining ideal sheaf itself vanishes is in
particular square-zero. This is the base case `n = 0` of the induction on the order. -/
theorem isSquareZeroClosedImmersion_of_ker_eq_bot {P Q : BigFppfOver B S hS} {i : P ⟶ Q}
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map i))
    (hker : ((BigFppfOver.toScheme B S hS).map i).ker ^ 1 = ⊥) :
    IsSquareZeroClosedImmersion B S hS i :=
  ⟨hci, le_bot_iff.1 (hker ▸ idealSheaf_pow_le_pow_right (by omega))⟩

/-- **The square-zero hypothesis of Stacks 049S, part (3), may be relaxed to a nilpotent
defining ideal sheaf.** A formally unramified transformation of sheaves has at most one dotted
arrow in a commutative square over a closed immersion `i : P ⟶ Q` of objects of the big fppf
site over `S` whose defining ideal sheaf has vanishing `(n + 1)`st power.

Induction on `n`. For `n = 0` the immersion is square-zero and this is
`AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion`. For
`n + 1`, factor `i = u ≫ v` with `v` square-zero and `u` of one order less: the two restrictions
`v ≫ z₁` and `v ≫ z₂` solve the same lifting problem over `u`, hence agree by induction, and
`z₁`, `z₂` then solve the same lifting problem over the square-zero `v`. -/
theorem FormallyUnramified.lift_unique_of_ker_pow_eq_bot
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (ha : FormallyUnramified a) :
    ∀ (n : ℕ) {P Q : BigFppfOver B S hS} (i : P ⟶ Q),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      ((BigFppfOver.toScheme B S hS).map i).ker ^ (n + 1) = ⊥ →
      ∀ (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G) (z₁ z₂ : yoneda.obj Q ⟶ F),
        yoneda.map i ≫ z₁ = x → z₁ ≫ a = y →
        yoneda.map i ≫ z₂ = x → z₂ ≫ a = y → z₁ = z₂ := by
  intro n
  induction n with
  | zero =>
    intro P Q i hci hker x y z₁ z₂ hz₁ hz₁' hz₂ hz₂'
    exact FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion B S hS hF ha
      (isSquareZeroClosedImmersion_of_ker_eq_bot B S hS hci hker) x y z₁ z₂ hz₁ hz₁' hz₂ hz₂'
  | succ n ih =>
    intro P Q i hci hker x y z₁ z₂ hz₁ hz₁' hz₂ hz₂'
    obtain ⟨W, u, v, huv, hsqv, hciu, hkeru⟩ :=
      exists_factorization_of_ker_pow_eq_bot B S hS hci hker
    have hrest (z : yoneda.obj Q ⟶ F) (hz : yoneda.map i ≫ z = x) :
        yoneda.map u ≫ yoneda.map v ≫ z = x := by
      rw [← Category.assoc, ← Functor.map_comp, huv, hz]
    have hw : yoneda.map v ≫ z₁ = yoneda.map v ≫ z₂ :=
      ih u hciu hkeru x (yoneda.map v ≫ y) _ _ (hrest z₁ hz₁)
        (by rw [Category.assoc, hz₁']) (hrest z₂ hz₂) (by rw [Category.assoc, hz₂'])
    exact FormallyUnramified.lift_unique_of_isSquareZeroClosedImmersion B S hS hF ha hsqv
      (yoneda.map v ≫ z₁) y z₁ z₂ rfl hz₁' hw.symm hz₂'

/-- **The square-zero hypothesis of Stacks 049S, part (1), may be relaxed to a nilpotent
defining ideal sheaf**, granted uniqueness. A formally smooth and formally unramified
transformation of sheaves admits a dotted arrow in every commutative square over a closed
immersion `i : P ⟶ Q` of objects of the big fppf site over `S` whose defining ideal sheaf has
vanishing `(n + 1)`st power.

Induction on `n`, as for
`AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_ker_pow_eq_bot`: lift first across
the leg `u` of one order less, then across the square-zero leg `v`. -/
theorem FormallySmooth.exists_lift_of_ker_pow_eq_bot
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (ha : FormallySmooth a) (hau : FormallyUnramified a) :
    ∀ (n : ℕ) {P Q : BigFppfOver B S hS} (i : P ⟶ Q),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      ((BigFppfOver.toScheme B S hS).map i).ker ^ (n + 1) = ⊥ →
      ∀ (x : yoneda.obj P ⟶ F) (y : yoneda.obj Q ⟶ G), x ≫ a = yoneda.map i ≫ y →
        ∃ z : yoneda.obj Q ⟶ F, yoneda.map i ≫ z = x ∧ z ≫ a = y := by
  intro n
  induction n with
  | zero =>
    intro P Q i hci hker x y hsq
    exact FormallySmooth.exists_lift_of_isSquareZeroClosedImmersion B S hS hF hG ha hau
      (isSquareZeroClosedImmersion_of_ker_eq_bot B S hS hci hker) x y hsq
  | succ n ih =>
    intro P Q i hci hker x y hsq
    obtain ⟨W, u, v, huv, hsqv, hciu, hkeru⟩ :=
      exists_factorization_of_ker_pow_eq_bot B S hS hci hker
    obtain ⟨zW, hzW, hzW'⟩ := ih u hciu hkeru x (yoneda.map v ≫ y) (by
      rw [hsq, ← huv, Functor.map_comp, Category.assoc])
    obtain ⟨z, hz, hz'⟩ := FormallySmooth.exists_lift_of_isSquareZeroClosedImmersion B S hS
      hF hG ha hau hsqv zW y hzW'
    refine ⟨z, ?_, hz'⟩
    rw [← huv, Functor.map_comp, Category.assoc, hz, hzW]

/-! ### Lifting across a thickening of algebraic spaces of order `n` -/

/-- Two arrows out of the target of an epimorphism of sheaves agree if they agree after
precomposition. -/
private theorem eq_of_comp_eq_of_epi_sheaf
    {A A' C : Sheaf (BigFppfOver.topology B S hS) (Type u)} (φ : A ⟶ A') [Epi φ]
    {g₁ g₂ : A'.obj ⟶ C.obj} (h : φ.hom ≫ g₁ = φ.hom ≫ g₂) : g₁ = g₂ :=
  Sheaf.hom_ext_iff.1 ((cancel_epi φ).1
    (Sheaf.hom_ext h : φ ≫ ObjectProperty.homMk g₁ = φ ≫ ObjectProperty.homMk g₂))

/-- **Stacks 05ZY for a thickening of order `n`.** A formally unramified morphism `f : X ⟶ Y` of
algebraic spaces over `S` admits at most one dotted arrow in a solid square over an `n`th-order
thickening `T ⊂ T'` of algebraic spaces over `S`.

The thickening pulls back along a surjective étale atlas of `T'` to a closed immersion of
objects of the site with nilpotent defining ideal sheaf
(`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`), where
`AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_ker_pow_eq_bot` applies; the atlas is
an epimorphism of fppf sheaves, so the two arrows agree. -/
theorem FormallyUnramified.lifts_unique_of_isNthOrderThickening {n : ℕ}
    {X Y T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : FormallyUnramified f.hom)
    (T : Subfunctor T'.obj) (hT : IsNthOrderThickening B S hS n T' T)
    (a : T.toFunctor ⟶ X.obj) (b : T'.obj ⟶ Y.obj) (_hsq : a ≫ f.hom = T.ι ≫ b)
    (z₁ z₂ : T'.obj ⟶ X.obj)
    (hz₁a : T.ι ≫ z₁ = a) (hz₁b : z₁ ≫ f.hom = b)
    (hz₂a : T.ι ≫ z₂ = a) (hz₂b : z₂ ≫ f.hom = b) :
    z₁ = z₂ := by
  obtain ⟨U, q, hqS, hqE⟩ := T'.property.exists_atlas
  obtain ⟨U₀, i, p, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT U q hqE
  have hrest (z : T'.obj ⟶ X.obj) (hz : T.ι ≫ z = a) :
      yoneda.map i ≫ q ≫ z = p ≫ a := by
    rw [← Category.assoc, ← hpb.w, Category.assoc, hz]
  have hU : q ≫ z₁ = q ≫ z₂ :=
    FormallyUnramified.lift_unique_of_ker_pow_eq_bot B S hS X.property.isSheaf hf n i hci hker
      (p ≫ a) (q ≫ b) _ _ (hrest z₁ hz₁a) (by rw [Category.assoc, hz₁b])
      (hrest z₂ hz₂a) (by rw [Category.assoc, hz₂b])
  -- The atlas is an epimorphism of fppf sheaves.
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q :=
    isLocallySurjective_of_surjective_etale B S hS q hqS hqE
  let Usheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj U, BigFppfOver.isSheaf_yoneda_obj B S hS U⟩
  let T'sheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨T'.obj, T'.property.isSheaf⟩
  let Xsheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let φ : Usheaf ⟶ T'sheaf := ObjectProperty.homMk q
  have hφls : Sheaf.IsLocallySurjective φ := hls
  have : Epi φ := inferInstance
  exact eq_of_comp_eq_of_epi_sheaf B S hS (C := Xsheaf) φ hU

/-- **Stacks 0611 for a thickening of order `n`.** A formally étale morphism `f : X ⟶ Y` of
algebraic spaces over `S` admits exactly one dotted arrow in a solid square over an `n`th-order
thickening `T ⊂ T'` of algebraic spaces over `S`, for every `n`. No affineness is assumed of
either space of the thickening.

The source states the tag for a first-order thickening, which is
`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening`, the case
`n = 1`. The proof here is the same descent along a surjective étale atlas, with the square-zero
statements of Stacks 049S replaced by their nilpotent forms
`AlgebraicGeometry.Space.FormallySmooth.exists_lift_of_ker_pow_eq_bot` and
`AlgebraicGeometry.Space.FormallyUnramified.lift_unique_of_ker_pow_eq_bot`, and uniqueness
supplied by `AlgebraicGeometry.Space.FormallyUnramified.lifts_unique_of_isNthOrderThickening`.
Every other input was already order-free: the chart pullback
`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback` is stated at order `n`, and
so is the presentation of an algebraic space as the coequalizer of the kernel pair of an atlas,
Stacks 0262 part (3). -/
@[ega "IV 17.1.2" "(ii), partial"]
theorem FormallyEtale.existsUnique_lift_of_isNthOrderThickening {n : ℕ}
    {X Y T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : FormallyEtale f.hom)
    (T : Subfunctor T'.obj) (hT : IsNthOrderThickening B S hS n T' T)
    (a : T.toFunctor ⟶ X.obj) (b : T'.obj ⟶ Y.obj) (hsq : a ≫ f.hom = T.ι ≫ b) :
    ∃! c : T'.obj ⟶ X.obj, T.ι ≫ c = a ∧ c ≫ f.hom = b := by
  have hsm : FormallySmooth f.hom := fun P Q hP hQ i hi v y hvy ↦
    (hf P Q hP hQ i hi v y hvy).exists
  have hur : FormallyUnramified f.hom := fun P Q hP hQ i hi v y hvy z₁ z₂ h₁ h₂ ↦
    (hf P Q hP hQ i hi v y hvy).unique h₁ h₂
  -- A surjective étale atlas of the ambient space, and the thickening of site objects that the
  -- given thickening pulls back to over it.
  obtain ⟨U, q, hqS, hqE⟩ := T'.property.exists_atlas
  obtain ⟨U₀, i, p, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT U q hqE
  obtain ⟨c, hc₁, hc₂⟩ := FormallySmooth.exists_lift_of_ker_pow_eq_bot B S hS
    X.property.isSheaf Y.property.isSheaf hsm hur n i hci hker (p ≫ a) (q ≫ b)
    (by rw [Category.assoc, hsq, ← Category.assoc, hpb.w, Category.assoc])
  -- The kernel pair of the atlas, and the invariance of the lift under it.
  let rep := T'.property.diagonal_representable.of_diag q
  let R := rep.pullback q
  let s : R ⟶ U := rep.fst' q
  let t : R ⟶ U := rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := rep.isPullback' q
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hqE.property q (yoneda.map t) s hR.flip
  have hinv : yoneda.map s ≫ c = yoneda.map t ≫ c := by
    have hmul := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
    have hρE : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map s ≫ q) :=
      MorphismProperty.comp_mem _ _ _
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s).2 hEs) hqE
    obtain ⟨R₀, j, pR, hpbR, hciR, hkerR⟩ :=
      exists_nthOrderThickening_chart_pullback B S hS hT R (yoneda.map s ≫ q) hρE
    have key (v : R ⟶ U) (hv : yoneda.map v ≫ q = yoneda.map s ≫ q) :
        yoneda.map j ≫ yoneda.map v ≫ c = pR ≫ a ∧
          (yoneda.map v ≫ c) ≫ f.hom = (yoneda.map s ≫ q) ≫ b := by
      have hw : pR ≫ T.ι = yoneda.map (j ≫ v) ≫ q := by
        rw [hpbR.w, Functor.map_comp, Category.assoc, hv]
      refine ⟨?_, ?_⟩
      · calc yoneda.map j ≫ yoneda.map v ≫ c = yoneda.map (j ≫ v) ≫ c := by
              rw [Functor.map_comp, Category.assoc]
          _ = (hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ yoneda.map i) ≫ c := by
              rw [hpb.lift_snd]
          _ = hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ p ≫ a := by rw [Category.assoc, hc₁]
          _ = pR ≫ a := by rw [← Category.assoc, hpb.lift_fst]
      · calc (yoneda.map v ≫ c) ≫ f.hom = yoneda.map v ≫ q ≫ b := by
              rw [Category.assoc, hc₂]
          _ = (yoneda.map v ≫ q) ≫ b := by rw [Category.assoc]
          _ = (yoneda.map s ≫ q) ≫ b := by rw [hv]
    exact FormallyUnramified.lift_unique_of_ker_pow_eq_bot B S hS
      X.property.isSheaf hur n j hciR hkerR (pR ≫ a) ((yoneda.map s ≫ q) ≫ b) _ _
      (key s rfl).1 (key s rfl).2 (key t hR.w.symm).1 (key t hR.w.symm).2
  -- The atlas presents `T'` as the coequalizer of its kernel pair, so the lift descends.
  let J := BigFppfOver.topology B S hS
  let hcolimit := isCoequalizer_of_surjectiveEtale B S hS q s t hR T'.property hqS hqE
  let hRsh := Classical.choose hcolimit
  have hcolimitU := Classical.choose_spec hcolimit
  let hUsh := Classical.choose hcolimitU
  have hcolimitC := Classical.choose_spec hcolimitU
  let hc := Classical.choice hcolimitC
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let T'F : Sheaf J (Type u) := ⟨T'.obj, T'.property.isSheaf⟩
  let XF : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let YF : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let qf : UF ⟶ T'F := ⟨q⟩
  have hwc : sf ≫ (⟨c⟩ : UF ⟶ XF) = tf ≫ (⟨c⟩ : UF ⟶ XF) := Sheaf.hom_ext hinv
  let cofork : Cofork sf tf := Cofork.ofπ (⟨c⟩ : UF ⟶ XF) hwc
  let dsh := hc.desc cofork
  have hfac : qf ≫ dsh = (⟨c⟩ : UF ⟶ XF) := by
    simpa [dsh, cofork] using hc.fac cofork WalkingParallelPair.one
  have hqd : q ≫ dsh.hom = c := congrArg (fun φ ↦ φ.hom) hfac
  -- The descended arrow solves the original lifting problem.
  have hd₂ : dsh.hom ≫ f.hom = b := by
    have _ : Epi qf := Cofork.IsColimit.epi hc
    refine eq_of_comp_eq_of_epi_sheaf B S hS (C := YF) qf ?_
    rw [← Category.assoc, hqd, hc₂]
  have hd₁ : T.ι ≫ dsh.hom = a := by
    have hstabS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hstabE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hpS := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqS
    have hpE := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqE
    let U₀F : Sheaf J (Type u) := ⟨yoneda.obj U₀, BigFppfOver.isSheaf_yoneda_obj B S hS U₀⟩
    let TF : Sheaf J (Type u) := ⟨T.toFunctor, hT.choose.1.1.isSheaf⟩
    let pf : U₀F ⟶ TF := ⟨p⟩
    have _ : Sheaf.IsLocallySurjective pf :=
      isLocallySurjective_of_surjective_etale B S hS p hpS hpE
    have _ : Epi pf := inferInstance
    refine eq_of_comp_eq_of_epi_sheaf B S hS (C := XF) pf ?_
    calc p ≫ T.ι ≫ dsh.hom = (p ≫ T.ι) ≫ dsh.hom := by rw [Category.assoc]
      _ = (yoneda.map i ≫ q) ≫ dsh.hom := by rw [hpb.w]
      _ = yoneda.map i ≫ c := by rw [Category.assoc, hqd]
      _ = p ≫ a := hc₁
  exact ⟨dsh.hom, ⟨hd₁, hd₂⟩, fun c' hc' ↦
    FormallyUnramified.lifts_unique_of_isNthOrderThickening B S hS f hur T hT a b hsq
      c' dsh.hom hc'.1 hc'.2 hd₁ hd₂⟩

end AlgebraicGeometry.Space

end
