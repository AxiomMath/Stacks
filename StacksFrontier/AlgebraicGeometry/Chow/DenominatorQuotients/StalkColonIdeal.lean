module

public import StacksFrontier.AlgebraicGeometry.Chow.CartierDivisorsK.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk

/-!
# The stalk of the ideal of denominators is the denominator ideal of a local ratio

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules and `s` a meromorphic section of
`L`. The ideal of denominators of `s` is the subsheaf `I ⊆ 𝒪_X` whose sections over an open set
are the `f` with `f s` a section of `L`, and [Stacks, Tag 02P0] presents it affine-locally: over
an affine open `V` on which `L` is trivial and on which `s` is the ratio `a / b` of two sections
of `𝒪_X`, the sections of `I` are the `g` with `g a` a multiple of `b`.

This file passes that presentation to the stalk at a point `x` of `V`: the germs at `x` of the
sections of `I` are exactly the elements of `Ideal.denominatorIdeal` of the germs of `a` and of
`b` in the local ring `𝒪_{X, x}`. That is the shape in which the length computation of
[Stacks, Tag 02QH] consumes the ideal of denominators, being stated about
`Ideal.denominatorIdeal`.

## Main definitions

* `Stacks.Chow.DenominatorStalk.germs`: the germs at a point of the sections of the ideal of
  denominators, that is the image of the stalk of that ideal in the local ring.

## Main results

* `Stacks.Chow.DenominatorStalk.germs_eq_coe_denominatorIdeal`: those germs are exactly the
  denominator ideal of the germs of the local ratio.
* `Stacks.Chow.DenominatorStalk.span_germs_eq_denominatorIdeal`: the same statement as an
  equality of ideals of the local ring.
* `Stacks.Chow.DenominatorStalk.exists_affineOpen_span_germs_eq_denominatorIdeal`: around every
  point of a scheme there is an affine open carrying a ratio for which that equality holds. This
  is the entry point, and it assumes only that `L` is invertible.
* `Stacks.Chow.DenominatorStalk.mem_germs_iff_unitStalkLinearEquiv_mem_range`: the germs are the
  range of the stalk map of the inclusion of the ideal of denominators in the structure sheaf,
  read across the identification `Stacks.UnitStalk.unitStalkLinearEquiv`.
* `Stacks.Chow.DenominatorStalk.comap_range_stalkLinearMap_eq_denominatorIdeal` and
  `Stacks.Chow.DenominatorStalk.exists_affineOpen_comap_range_stalkLinearMap_eq`: the same
  equality stated about that range, which is the spelling the stalk computations of
  [Stacks, Tag 02SW] are written in.

## Implementation notes

No localization statement about colon ideals is used, and in particular
`Stacks.ColonLocalization` is not: the presentation
`Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen` is already available on
*every* basic open of the trivializing affine, and those form a neighbourhood basis of each of
its points by `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`. So both inclusions are
proved by choosing representatives of germs on a basic open and reading the presentation there,
and the stalk is the colimit of the sections over such a basis with no further input.

The set of germs is defined over *all* neighbourhoods of the point rather than over the
neighbourhoods inside the trivializing affine, so that the definition does not mention the
affine open; the two agree, and the proof shrinks a neighbourhood to the affine open before
shrinking it to a basic open.

Restrictions along inclusions of opens are composed by `res_res`, which needs
`CategoryTheory.Functor.map_comp_apply` and then `rfl` on the two inclusions: morphisms in the
poset category of opens are proofs, so any two with the same source and target are
definitionally equal. The scalars `a` and `b` are kept at the `Γ(X, V)` spelling, where
`Ideal.denominatorIdeal` is formed, and never at
`Stacks.DenominatorLocalRatio.oScalar`; the two carriers are the same type but instance search
does not cross between them, and the presentation lemmas consumed here are already stated at
`Γ(X, V)`.

The germ description and the `AlgebraicGeometry.stalkLinearMap` description of the stalk of the
ideal of denominators are joined, not identified: the range of that stalk map is a submodule of
the stalk of the unit module, which is taken in `AddCommGrpCat` and carries no ring structure, so
`Ideal.denominatorIdeal` cannot be *written* against it. `Stacks.UnitStalk.unitStalkLinearEquiv`
identifies that stalk with the local ring, and the bridge is stated by pulling the range back
along it, which keeps the ideal on the side where it is meaningful. The three objects of
[Stacks, Tag 02P2] are re-ascribed at the declared type `AlgebraicGeometry.Scheme.Modules` by
the `Decl` abbreviations below, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Stalks`: that type is a `def` whose
categorical instances are copies, and instance search re-infers the type from the term, so a
type ascription does not suffice.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι
open CategoryTheory TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio
open Stacks.UnitStalk (unitModule unitStalkLinearEquiv unitStalkLinearEquiv_germ)

universe u

namespace Stacks.Chow.DenominatorStalk

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L)

/-- Restrictions of sections of the structure sheaf compose: restricting along `V ≤ U` and then
along `W ≤ V` restricts along `W ≤ U`. Morphisms in the poset category of opens are proofs, so
the two inclusions are definitionally equal. -/
lemma res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (t : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op t) =
      X.presheaf.map (homOfLE h₃).op t := by
  rw [← X.presheaf.map_comp_apply]
  rfl

/-- The germ of a section restricted to a basic open, read through the algebra structure map that
`Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen` is stated with. -/
lemma germ_algebraMap_basicOpen {V : Opens X} (f : Γ(X, V)) {x : X} (hx : x ∈ V)
    (hxf : x ∈ X.basicOpen f) (a : Γ(X, V)) :
    X.presheaf.germ (X.basicOpen f) x hxf (algebraMap Γ(X, V) Γ(X, X.basicOpen f) a) =
      X.presheaf.germ V x hx a :=
  X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxf a

/-- The image of the ideal of denominators on sections is stable under restriction: a denominator
over `W` restricts to a denominator over any smaller open set. -/
lemma mem_range_denominatorIdealι_app_res {W W' : Opens X} (h : W' ≤ W) {g : Γ(X, W)}
    (hg : g ∈ Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op W)))) :
    X.presheaf.map (homOfLE h).op g ∈
      Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op W'))) := by
  obtain ⟨d, rfl⟩ := hg
  exact ⟨(denominatorIdeal X L s).val.map (homOfLE h).op d,
    PresheafOfModules.naturality_apply (denominatorIdealι X L s).val (homOfLE h).op d⟩

/-- **The germs at `x` of the sections of the ideal of denominators of `s`**, that is the image
of the stalk of that ideal in the local ring `𝒪_{X, x}`. -/
def germs (x : X) : Set (X.presheaf.stalk x) :=
  {z | ∃ (W : Opens X) (hxW : x ∈ W) (g : Γ(X, W)),
    g ∈ Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op W))) ∧
      X.presheaf.germ W x hxW g = z}

/-- **The germs of the ideal of denominators are the denominator ideal of the germs of the local
ratio.** The hypothesis is the colon-ideal presentation of the ideal of denominators on every
basic open of an affine open `V`, which is what
`Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen` provides for a trivializing
affine open carrying a ratio `a / b` of `s`.

Both inclusions shrink a neighbourhood of `x` to a basic open of `V`, where the presentation is
available: a denominator restricts to one there, and conversely an equation between germs holds
on some neighbourhood, hence on a basic open inside it. -/
theorem germs_eq_coe_denominatorIdeal {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
        {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
          g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
            algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v})
    {x : X} (hx : x ∈ V) :
    germs X L s x =
      (Ideal.denominatorIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) :
        Set (X.presheaf.stalk x)) := by
  ext z
  constructor
  · rintro ⟨W, hxW, g, hg, rfl⟩
    obtain ⟨f, hfle, hxf⟩ :=
      hV.exists_basicOpen_le (⟨x, ⟨hxW, hx⟩⟩ : (W ⊓ V : Opens X)) hx
    have hleW : X.basicOpen f ≤ W := hfle.trans inf_le_left
    obtain ⟨v, hv⟩ := (Set.ext_iff.mp (hbas f) _).mp
      (mem_range_denominatorIdealι_app_res X L s hleW hg)
    refine SetLike.mem_coe.mpr (Ideal.mem_denominatorIdeal_iff.mpr
      ⟨X.presheaf.germ (X.basicOpen f) x hxf v, ?_⟩)
    have hgerm := congrArg (ConcreteCategory.hom (X.presheaf.germ (X.basicOpen f) x hxf)) hv
    rw [map_mul, map_mul, germ_algebraMap_basicOpen X f hx hxf a,
      germ_algebraMap_basicOpen X f hx hxf b,
      X.presheaf.germ_res_apply (homOfLE hleW) x hxf g] at hgerm
    exact hgerm.trans (mul_comm _ _)
  · intro hz
    obtain ⟨y, hy⟩ := Ideal.mem_denominatorIdeal_iff.mp (SetLike.mem_coe.mp hz)
    obtain ⟨W₁, hW₁V, hxW₁, g₁, hg₁⟩ := X.presheaf.exists_le_germ_eq z hx
    obtain ⟨W₂, hW₂V, hxW₂, y₂, hy₂⟩ := X.presheaf.exists_le_germ_eq y hx
    have hxW₃ : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
    have hW₃V : W₁ ⊓ W₂ ≤ V := inf_le_left.trans hW₁V
    set g₃ := X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op g₁
    set y₃ := X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op y₂
    set a₃ := X.presheaf.map (homOfLE hW₃V).op a
    set b₃ := X.presheaf.map (homOfLE hW₃V).op b
    have heq : X.presheaf.germ (W₁ ⊓ W₂) x hxW₃ (g₃ * a₃) =
        X.presheaf.germ (W₁ ⊓ W₂) x hxW₃ (y₃ * b₃) := by
      simp only [map_mul, g₃, y₃, a₃, b₃, X.presheaf.germ_res_apply, hg₁, hy₂]
      exact hy
    obtain ⟨W₄, hxW₄, i₁, i₂, hmap⟩ :=
      X.presheaf.germ_eq x hxW₃ hxW₃ (g₃ * a₃) (y₃ * b₃) heq
    obtain ⟨f, hfle, hxf⟩ := hV.exists_basicOpen_le (⟨x, hxW₄⟩ : W₄) hx
    have hD : X.basicOpen f ≤ W₁ ⊓ W₂ := hfle.trans i₁.le
    have hmapD : X.presheaf.map (homOfLE hD).op (g₃ * a₃) =
        X.presheaf.map (homOfLE hD).op (y₃ * b₃) :=
      (res_res X i₁.le hfle hD _).symm.trans
        ((congrArg (ConcreteCategory.hom (X.presheaf.map (homOfLE hfle).op)) hmap).trans
          (res_res X i₂.le hfle hD _))
    rw [map_mul, map_mul, res_res X hW₃V hD (X.basicOpen_le f) a,
      res_res X hW₃V hD (X.basicOpen_le f) b] at hmapD
    exact ⟨X.basicOpen f, hxf, X.presheaf.map (homOfLE hD).op g₃,
      (Set.ext_iff.mp (hbas f) _).mpr
        ⟨X.presheaf.map (homOfLE hD).op y₃, hmapD.trans (mul_comm _ _)⟩,
      by simp only [g₃, X.presheaf.germ_res_apply, hg₁]⟩

/-- **The stalk of the ideal of denominators is the denominator ideal of the germs of the local
ratio**, as an equality of ideals of the local ring. This is
`Stacks.Chow.DenominatorStalk.germs_eq_coe_denominatorIdeal` together with
`Ideal.span_eq`: the germs already form an ideal, being the underlying set of one. -/
theorem span_germs_eq_denominatorIdeal {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
        {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
          g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
            algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v})
    {x : X} (hx : x ∈ V) :
    Ideal.span (germs X L s x) =
      Ideal.denominatorIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) := by
  rw [germs_eq_coe_denominatorIdeal X L s hV hbas hx, Ideal.span_eq]

/-- **Around every point of a scheme there is an affine open on which the meromorphic section is
a ratio `a / b` whose denominator ideal is the stalk of the ideal of denominators.** The affine
open and the ratio come from
`Stacks.DenominatorIdealQcoh.exists_affineOpen_colon_presentations`, which uses no Noetherian
hypothesis; the only hypothesis here is that `L` is invertible. -/
theorem exists_affineOpen_span_germs_eq_denominatorIdeal
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      Ideal.span (germs X L s x) =
        Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) := by
  obtain ⟨V, hxV, hVaff, a, b, -, hbas⟩ :=
    Stacks.DenominatorIdealQcoh.exists_affineOpen_colon_presentations X L s hL x
  exact ⟨V, hxV, hVaff, a, b, span_germs_eq_denominatorIdeal X L s hVaff hbas hxV⟩

/-! ### The same stalk through `AlgebraicGeometry.stalkLinearMap` -/

/-- The ideal of denominators, at the declared type `AlgebraicGeometry.Scheme.Modules`. -/
abbrev denominatorIdealDecl : X.Modules := denominatorIdeal X L s

/-- The inclusion of the ideal of denominators in the structure sheaf, at the declared type
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev denominatorIdealιDecl : denominatorIdealDecl X L s ⟶ unitModule X :=
  denominatorIdealι X L s

/-- **The germs of the ideal of denominators are the range of the stalk map of its inclusion in
the structure sheaf**, read across the identification of the stalk of the unit module with the
local ring. Both directions are the same computation: the stalk map carries the germ of a
section of the ideal to the germ of its image, and the identification carries the germ of a
section of `𝒪_X` to the germ of that section in the unit module. -/
theorem mem_germs_iff_unitStalkLinearEquiv_mem_range (x : X) (z : X.presheaf.stalk x) :
    z ∈ germs X L s x ↔
      unitStalkLinearEquiv X x z ∈
        LinearMap.range (AlgebraicGeometry.stalkLinearMap (denominatorIdealDecl X L s)
          (unitModule X) (denominatorIdealιDecl X L s) x) := by
  constructor
  · rintro ⟨W, hxW, g, ⟨d, rfl⟩, rfl⟩
    refine ⟨(denominatorIdealDecl X L s).presheaf.germ W x hxW d, ?_⟩
    exact (AlgebraicGeometry.stalkLinearMap_germ (denominatorIdealDecl X L s) (unitModule X)
        (denominatorIdealιDecl X L s) W x hxW d).trans
      (unitStalkLinearEquiv_germ X x W hxW _).symm
  · rintro ⟨c, hc⟩
    obtain ⟨W, hxW, d, rfl⟩ := (denominatorIdealDecl X L s).presheaf.exists_germ_eq c
    refine ⟨W, hxW, (denominatorIdealι X L s).val.app (op W) d, ⟨d, rfl⟩,
      (unitStalkLinearEquiv X x).injective ?_⟩
    refine (unitStalkLinearEquiv_germ X x W hxW _).trans (Eq.trans ?_ hc)
    exact (AlgebraicGeometry.stalkLinearMap_germ (denominatorIdealDecl X L s) (unitModule X)
      (denominatorIdealιDecl X L s) W x hxW d).symm

/-- **The stalk of the ideal of denominators, read through
`AlgebraicGeometry.stalkLinearMap`, is the denominator ideal of the germs of the local ratio.**
The range of the stalk map lives in the stalk of the unit module, which is taken in
`AddCommGrpCat` and so carries no ring structure; pulling it back along
`Stacks.UnitStalk.unitStalkLinearEquiv` puts it in the local ring, where
`Ideal.denominatorIdeal` is formed. -/
theorem comap_range_stalkLinearMap_eq_denominatorIdeal {V : Opens X} (hV : IsAffineOpen V)
    {a b : Γ(X, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
        {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
          g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
            algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v})
    {x : X} (hx : x ∈ V) :
    Submodule.comap (unitStalkLinearEquiv X x).toLinearMap
        (LinearMap.range (AlgebraicGeometry.stalkLinearMap (denominatorIdealDecl X L s)
          (unitModule X) (denominatorIdealιDecl X L s) x)) =
      Ideal.denominatorIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) :=
  SetLike.ext fun z =>
    Submodule.mem_comap.trans
      (((mem_germs_iff_unitStalkLinearEquiv_mem_range X L s x z).symm.trans
        (Set.ext_iff.mp (germs_eq_coe_denominatorIdeal X L s hV hbas hx) z)).trans
          SetLike.mem_coe)

/-- **Around every point of a scheme there is an affine open on which the meromorphic section is
a ratio `a / b` whose denominator ideal is the stalk of the ideal of denominators**, in the
`AlgebraicGeometry.stalkLinearMap` spelling. The only hypothesis is that `L` is invertible. -/
theorem exists_affineOpen_comap_range_stalkLinearMap_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      Submodule.comap (unitStalkLinearEquiv X x).toLinearMap
          (LinearMap.range (AlgebraicGeometry.stalkLinearMap (denominatorIdealDecl X L s)
            (unitModule X) (denominatorIdealιDecl X L s) x)) =
        Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) := by
  obtain ⟨V, hxV, hVaff, a, b, -, hbas⟩ :=
    Stacks.DenominatorIdealQcoh.exists_affineOpen_colon_presentations X L s hL x
  exact ⟨V, hxV, hVaff, a, b,
    comap_range_stalkLinearMap_eq_denominatorIdeal X L s hVaff hbas hxV⟩

end Stacks.Chow.DenominatorStalk

end
