module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.RelativeProj

/-!
# What the nested cocycle reduces to

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A n` is the single hypothesis
that the glued twist `gluedTwist` — and hence the twist `𝒪_{𝐏(E)}(1)` that Stacks Tag 01VM
quantifies over — is conditional on. As stated it is a statement about the sections of three
pushed-forward twists over an arbitrary open of the relative Proj, quantified over three affine
opens of the base, three containments between them, an open of the relative Proj, two
containments of that open, and a section.

**This file removes all of that but the three affine opens.** The cocycle follows from the single
equation

`pushNested A W' U ≫ pushNested A W W' = pushNested A W U`

between morphisms of sheaves of modules on the relative Proj, in which no open of the relative
Proj, no section, and no containment of such opens occurs.

## Main results

* `…ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp`: **the reduction**, in every
  integer degree.

## What this leaves owed, and what it is

The remaining equation is the **third assertion of Stacks Tag 01MZ** — that the maps induced on
every twist `𝒪(n)` compose — and that assertion is absent from this repository. Two module
docstrings record it independently:

* `StacksFrontier/AlgebraicGeometry/TwistBaseChange/General.lean`, "Not done here":
  functoriality of `θ` in the graded ring homomorphism, the twist clause of Tag 01MZ, is not
  proved and is not used.
* `StacksFrontier/AlgebraicGeometry/ProjMapComposition/Basic.lean`, "What is not done": the third
  assertion of Tag 01MZ, that the maps on every twist `𝒪(n)` compose, is not proved there.

So the nested cocycle is not a budget problem but missing mathematics, and the reduction above
locates it exactly. `Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` together with
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom_comp` is its pointwise
*content* — `twistSection` is literally `fibreMap` pointwise, by
`Stacks.AlgebraicGeometry.TwistBaseChange.twistSection_val'`, which is `rfl` — but nothing in the
repository transports that content up through the six factors of `projInclusionTwistIso`, where
`mapDomain` for a composite behaves non-trivially. That transport is what
`StacksFrontier/AlgebraicGeometry/ProjMapComposition/Basic.lean` carried out at the level of
*schemes* and explicitly declined at the level of twists.

The alternative route, which the module documentation of
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean` blesses, is rigidity:
the owed section computation for `cmpNested` on `degreeSection` over `⊤`, then
`StacksFrontier/AlgebraicGeometry/TwistExistence/Overlap.lean` followed verbatim as the template —
it is the same argument already carried out there for the twist-data comparisons — closing with
`Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.eq_id_res` in degree one, which needs no
multiplicativity. That route additionally needs a counit identification
`restrict (pushforward (chart W) M) (chart W) ≅ M` for the open immersion `chart W`, which
`StacksFrontier/AlgebraicGeometry/TwistExistence/Overlap.lean` got free from a `TwistData`'s own
`chartIso` field and which does not exist here.

## Implementation notes

Both helper lemmas are at the level of variables. The only facts about the concrete instance used
are `cmpNested_app`, which is `rfl`, and the reading of a composite on a section; no `rw` is used
on a goal mentioning a pushforward of a twist, and no type mentioning
`AlgebraicGeometry.Scheme.Modules.pullback` at a concrete morphism is ever written — the kernel
reduces that while checking a statement, as the sibling `TwistSectionOn.lean` records.

The hypothesis is stated at a triple of *variable* opens, so nothing concrete appears in it.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)

## Not done here

**No tag is claimed.** Tag 01MZ's third assertion is named above as what is owed, not asserted.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

@[expose] public noncomputable section

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

universe u

/-- One factor of a composite of morphisms of sheaves of modules, read on a section. At the level
of variables, where the conversion is free. -/
public theorem comp_app_apply_of_eq {X : Scheme.{u}} {M₀ M₁ M₂ : X.Modules} (a : M₀ ⟶ M₁)
    (b : M₁ ⟶ M₂) (V : X.Opens) {x : M₀.val.obj (op V)} {y : M₁.val.obj (op V)}
    (he : a.val.app (op V) x = y) :
    (a ≫ b).val.app (op V) x = b.val.app (op V) y :=
  congrArg (b.val.app (op V)) he

/-- Equal morphisms of sheaves of modules act equally on a section. -/
public theorem app_apply_of_morphism_eq {X : Scheme.{u}} {M N : X.Modules} {a b : M ⟶ N}
    (hab : a = b) (V : X.Opens) (s : M.val.obj (op V)) :
    a.val.app (op V) s = b.val.app (op V) s := by
  subst hab; rfl

/-- **The nested cocycle follows from the composition law for `pushNested` as a morphism of
sheaves of modules on the relative Proj**, in every integer degree. -/
public theorem isNestedCocycle_of_pushNested_comp {S : Scheme.{u}} (A : SheafGradedAlgebra S)
    (n : ℤ)
    (hyp : ∀ (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
      (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U),
      pushNested A W' U hW'U hW' hU n ≫ pushNested A W W' hWW' hW hW' n
        = pushNested A W U hWU hW hU n) :
    IsNestedCocycle A n := by
  intro W W' U hWW' hW'U hWU hW hW' hU V hV hV' s
  refine Eq.trans (app_congr_arg (cmpNested A W W' hWW' hW hW' n) hV
    (cmpNested_app A W' U hW'U hW' hU n V hV' s)) ?_
  refine Eq.trans (cmpNested_app A W W' hWW' hW hW' n V hV _) ?_
  refine Eq.trans (comp_app_apply_of_eq (pushNested A W' U hW'U hW' hU n)
    (pushNested A W W' hWW' hW hW' n) V rfl).symm ?_
  refine Eq.trans (app_apply_of_morphism_eq (hyp W W' U hWW' hW'U hWU hW hW' hU) V s) ?_
  exact (cmpNested_app A W U hWU hW hU n V hV s).symm

end Stacks.AlgebraicGeometry.ChartTransRelativeProj

end
