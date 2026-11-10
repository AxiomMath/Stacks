module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# The pullback along an isomorphism of schemes, on global sections

`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso` builds the comparison

`Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv : α.hom^* ≅ α.inv _*`

for an isomorphism of schemes `α : A' ≅ A`, and characterizes it through the units
(`unit_comp_map_pullbackIsoPushforwardInv`). Its "What is not done" section then records an
**obstruction**: the right-hand side of that characterization is the unit of the
adjunction underlying `pullbackEquivalence`, and `CategoryTheory.Equivalence.mk` replaces the
unit it is handed by `CategoryTheory.Equivalence.adjointifyη` of it, so

> Unfolding `adjointifyη` and reducing it on sections leaves a goal that **is not type-correct at
> implicit transparency** […] so the reduction has to be redone without unfolding, and is not done
> here.

**That obstruction is false, and `adjointifyη` never has to be unfolded.** The half-adjoint
identity `CategoryTheory.Equivalence.functor_unit_comp` already says that the equivalence's unit,
pushed forward along `α.inv` and followed by its counit, is the identity; and the counit of
`Stacks.Conormal.AffineShape.pushforwardEquivalence` is `pushforwardHomInvIso`, which *is* the
composite of `AlgebraicGeometry.Scheme.Modules.pushforwardComp`, `pushforwardCongr` and
`pushforwardId` that `adjointifyη` was feared to destroy. Over the top open those three are the
identity and two presheaf restriction maps along equalities of opens whose two sides are the same
open, so the composite is the identity on sections — and the equivalence's unit is therefore the
identity on sections over the top open, with no unfolding anywhere.

This file is consequently the **missing elementwise factor** of the part (2) chain of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): the module docstrings of
`StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections`,
`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso` and
`StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` between them name five factors of
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` as characterized through the units and
this one as unmeasured. It is now the only one of the six with an *elementwise* description, which
is the form the generator formula of [Stacks, Tag 01R3] part (2) has to travel in.

## Main results

* `Stacks.Conormal.AffineShape.pushforwardHomInvIso_hom_app_top`: `pushforwardHomInvIso` is the
  identity on sections over the top open.
* `Stacks.Conormal.AffineShape.pushforwardEquivalence_unit_app_top`: hence so is the unit of the
  adjunction underlying `pushforwardEquivalence` — the statement the "What is not done" section
  of `ConormalAffineShape.PullbackIso` records as blocked.
* `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv_hom_app_top`: **the elementwise formula
  for the comparison.** Over the top open, `pullbackIsoPushforwardInv` carries the unit generator
  of `α.hom^* Q` attached to a global section `t` of `Q` back to `t` itself. So the comparison
  inverts the unit on global sections, which is exactly what the affine model's generator formula
  needs of this factor.
* `Stacks.Conormal.AffineShape.isIso_unit_app_of_iso`: for an isomorphism of schemes the unit of
  `α.hom^* ⊣ α.hom _*` is itself an isomorphism. Not needed for the formula above, but it is the
  sheaf-level reason the formula can exist, and it is three lines from the characterization.
* `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_app` and
  `..._inv_app`: the pseudofunctoriality factor of the same chain, read on sections — the
  comparison carries the unit generator of `(f' ≫ f)^* M` attached to a section `t` to the
  iterated unit generator of `f'^* f^* M`, and conversely. These are stated at the *scheme*
  spelling of the morphisms, which is what the chain uses, rather than at the ringed-space
  spelling the general statement is proved at.

## Route

Three ingredients, all cited:

* `CategoryTheory.Equivalence.functor_unit_comp`, the half-adjoint identity carried by every
  `CategoryTheory.Equivalence`;
* Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app`,
  `pushforwardCongr_hom_app_app` and `pushforwardId_hom_app_app`, all three `rfl`;
* `Stacks.Conormal.AffineShape.unit_comp_map_pullbackIsoPushforwardInv`.

`f ⁻¹ᵁ ⊤ = ⊤` holds by `rfl` for every morphism of schemes, which is what makes the top open the
one place where no transport of opens is needed; `map_eqToHom_self` disposes of the single
`eqToHom` that `pushforwardCongr` contributes.

## Universe situation

A single universe `u` (`Scheme.{u}` with `SheafOfModules.{u}`), as everywhere in this cluster.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no `stacks` attribute is attached.**
  Nothing here mentions immersions, ideal sheaves, the conormal sheaf or `Ideal.Cotangent`:
  every statement is about an arbitrary sheaf of modules and an arbitrary isomorphism of schemes.
* **Nothing over a non-top open.** `pullbackIsoPushforwardInv_hom_app_top` is stated over `⊤`
  only, and deliberately: over a general open `O` of `A` the two sides live over
  `(α.inv ≫ α.hom) ⁻¹ᵁ O` and `O`, which are equal but not definitionally so, and the statement
  would have to carry a transport. The affine model is stated at `⊤`, so the restriction costs
  the chain nothing.
* **No assembly of the chain.** The engine
  `Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` still takes its locality comparison as
  an uncharacterized hypothesis, so a generator formula for it needs one further argument; that
  is a separate statement and is not made here.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.AffineShape

/-- A presheaf restriction map along an equality of an open with *itself* is the identity on
sections. The equality is an argument rather than `rfl` because the two sides of the equalities
produced by `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` are definitionally but not
syntactically the same open, so `CategoryTheory.eqToHom_refl` does not fire on them directly;
passing the proof lets unification identify the two opens first. -/
theorem map_eqToHom_self {Y : Scheme.{u}} (P : Y.Modules) {W : Y.Opens} (h : W = W)
    (x : Γ(P, W)) : (P.presheaf.map (eqToHom h).op) x = x := by
  rw [eqToHom_refl, op_id, P.presheaf.map_id]
  rfl

variable {A A' : Scheme.{u}} (α : A' ≅ A)

/-! ### The two pushforward comparisons over the top open -/

/-- **`pushforwardHomInvIso` is the identity on global sections.** Pushing forward along `α.hom`
and then along `α.inv` changes nothing over the top open: the `pushforwardComp` and
`pushforwardId` factors are the identity on sections by Mathlib's own `rfl` lemmas, and the
`pushforwardCongr` factor is a presheaf restriction map along `(α.hom ≫ α.inv) ⁻¹ᵁ ⊤ = 𝟙 ⁻¹ᵁ ⊤`,
whose two sides are both `⊤`. -/
theorem pushforwardHomInvIso_hom_app_top (P : A'.Modules)
    (s : Γ((Scheme.Modules.pushforward α.hom ⋙ Scheme.Modules.pushforward α.inv).obj P, ⊤)) :
    ((pushforwardHomInvIso α).hom.app P).app ⊤ s = s := by
  simp only [pushforwardHomInvIso, Iso.trans_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardId_hom_app_app]
  exact map_eqToHom_self P _ s

/-- **The unit of the adjunction underlying `pushforwardEquivalence` is the identity on global
sections.** This is the statement the "What is not done" section of
`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso` records as blocked by
`CategoryTheory.Equivalence.adjointifyη`, and `adjointifyη` is never unfolded: the half-adjoint
identity `CategoryTheory.Equivalence.functor_unit_comp` says the unit followed by the counit of
the equivalence is the identity, and the counit is `pushforwardHomInvIso`, which the previous
lemma computes. -/
theorem pushforwardEquivalence_unit_app_top (Q : A.Modules)
    (t : Γ((Scheme.Modules.pushforward α.inv).obj Q, (⊤ : A'.Opens))) :
    ((pushforwardEquivalence α).toAdjunction.unit.app Q).app ⊤ t = t := by
  have h := congr($((pushforwardEquivalence α).functor_unit_comp Q).app (⊤ : A'.Opens))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
  have key : ((pushforwardHomInvIso α).hom.app
        ((Scheme.Modules.pushforward α.inv).obj Q)).app ⊤
      (((pushforwardEquivalence α).toAdjunction.unit.app Q).app ⊤ t) = t :=
    ConcreteCategory.congr_hom h t
  exact (pushforwardHomInvIso_hom_app_top α _ _).symm.trans key

/-! ### The comparison on global sections -/

/-- **The elementwise formula for `pullbackIsoPushforwardInv`.** For an isomorphism of schemes
`α : A' ≅ A`, a module `Q` on `A` and a global section `t` of `Q`, the comparison carries the
unit generator of `α.hom^* Q` attached to `t` back to `t`.

So on global sections the comparison *inverts* the unit of `α.hom^* ⊣ α.hom _*`. This is the
description that
`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso` records as absent — no
description of it on a named section is given there — and it is
`unit_comp_map_pullbackIsoPushforwardInv` read over `⊤` with the
right-hand side computed by `pushforwardEquivalence_unit_app_top`. -/
theorem pullbackIsoPushforwardInv_hom_app_top (Q : A.Modules) (t : Γ(Q, (⊤ : A.Opens))) :
    ((pullbackIsoPushforwardInv α).hom.app Q).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app Q).app ⊤ t) = t := by
  have h := congr($(unit_comp_map_pullbackIsoPushforwardInv α Q).app (⊤ : A.Opens))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h
  exact (ConcreteCategory.congr_hom h t).trans (pushforwardEquivalence_unit_app_top α Q t)

/-- `pullbackIsoPushforwardInv_hom_app_top` in the `val.app` spelling, which is the one the
part (2) chain of [Stacks, Tag 01R3] is written in: the two differ only by the forgetful functor
`ModuleCat Γ(A, ⊤) ⥤ Ab` and agree by `rfl`. -/
theorem pullbackIsoPushforwardInv_hom_val_app_top (Q : A.Modules) (t : Γ(Q, (⊤ : A.Opens))) :
    (((pullbackIsoPushforwardInv α).hom.app Q).val.app (.op ⊤)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app Q).val.app
          (.op ⊤)).hom t) = t :=
  pullbackIsoPushforwardInv_hom_app_top α Q t

/-- **For an isomorphism of schemes the unit of `α.hom^* ⊣ α.hom _*` is an isomorphism.** The
characterization `unit_comp_map_pullbackIsoPushforwardInv` exhibits the unit followed by an
isomorphism as the unit of the equivalence, which is a component of an isomorphism of functors;
so the unit is an isomorphism by cancellation. This is the sheaf-level reason
`pullbackIsoPushforwardInv_hom_app_top` can hold, and it is not used in proving it. -/
theorem isIso_unit_app_of_iso (Q : A.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app Q) := by
  have h2 : IsIso ((pushforwardEquivalence α).toAdjunction.unit.app Q) := by
    rw [Equivalence.toAdjunction_unit]
    infer_instance
  rw [← unit_comp_map_pullbackIsoPushforwardInv α Q] at h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (inferInstanceAs (IsIso ((Scheme.Modules.pushforward α.hom).map
      ((pullbackIsoPushforwardInv α).hom.app Q)))) h2

end Stacks.Conormal.AffineShape

namespace Stacks.PullbackPseudofunctor

/-- **The pseudofunctoriality comparison on sections**, at the scheme spelling of the two
morphisms. For `f : X' ⟶ X`, `f' : X'' ⟶ X'`, a module `M` on `X` and a section `t` of `M` over
an open `W`, the comparison `modulePullbackCompIso` carries the unit generator of
`(f' ≫ f)^* M` attached to `t` to the unit generator of `f'^* (f^* M)` attached to the unit
generator of `f^* M` attached to `t`.

This is `unit_comp_map_modulePullbackCompIso_hom_app` read on sections over `W`. The statement is
made at the scheme spelling because that is the one
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` composes in; the collapse
`(f' ≫ f).toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom` and the two spellings of
the module pullback are both discharged by unification against the stated type, never by a
rewrite — `StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` records that rewriting
under them produces a term that is not type-correct. -/
theorem unit_comp_map_modulePullbackCompIso_app {X X' X'' : Scheme.{u}} (f : X' ⟶ X)
    (f' : X'' ⟶ X') (M : X.Modules) (W : X.Opens) (t : Γ(M, W)) :
    (((modulePullbackCompIso f.toLRSHom.toShHom
          f'.toLRSHom.toShHom).hom.app M).val.app (.op (f' ⁻¹ᵁ (f ⁻¹ᵁ W)))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)).unit.app M).val.app
          (.op W)).hom t) =
      ((((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback f).obj M)).val.app (.op (f ⁻¹ᵁ W))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (.op W)).hom t)) :=
  congrArg (fun g => ModuleCat.Hom.hom g t)
    (congr($(unit_comp_map_modulePullbackCompIso_hom_app
      f.toLRSHom.toShHom f'.toLRSHom.toShHom M).val.app (.op W)))

/-- `unit_comp_map_modulePullbackCompIso_app` inverted: the comparison's inverse carries the
iterated unit generator of `f'^* (f^* M)` to the unit generator of `(f' ≫ f)^* M`. This is the
direction `Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` uses first, the comparison
appearing there as `.symm`. -/
theorem unit_comp_map_modulePullbackCompIso_inv_app {X X' X'' : Scheme.{u}} (f : X' ⟶ X)
    (f' : X'' ⟶ X') (M : X.Modules) (W : X.Opens) (t : Γ(M, W)) :
    (((modulePullbackCompIso f.toLRSHom.toShHom
          f'.toLRSHom.toShHom).inv.app M).val.app (.op (f' ⁻¹ᵁ (f ⁻¹ᵁ W)))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
            ((Scheme.Modules.pullback f).obj M)).val.app (.op (f ⁻¹ᵁ W))).hom
          ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op W)).hom t)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)).unit.app M).val.app
        (.op W)).hom t := by
  refine Eq.trans (congrArg (fun z => (((modulePullbackCompIso f.toLRSHom.toShHom
      f'.toLRSHom.toShHom).inv.app M).val.app (.op (f' ⁻¹ᵁ (f ⁻¹ᵁ W)))).hom z)
    (unit_comp_map_modulePullbackCompIso_app f f' M W t).symm) ?_
  exact congrArg (fun g => ModuleCat.Hom.hom g _)
    (congr($((modulePullbackCompIso f.toLRSHom.toShHom
      f'.toLRSHom.toShHom).hom_inv_id_app M).val.app (.op (f' ⁻¹ᵁ (f ⁻¹ᵁ W)))))

end Stacks.PullbackPseudofunctor

end
