module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic

/-!
# The two stalk spellings of a module on a ringed space, identified

The `𝒪_{X,x}`-module structure on the stalk of an `𝒪_X`-module at a point has two names in this
repository, both Mathlib's instance:

* `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, the ringed-space spelling used for
  Stacks Tag 01CB, which is the structure the identification of the stalk of a pullback
  (`Stacks.PullbackTensorIso.pullbackStalkEquiv`, Stacks Tag 0098) is stated over;
* `Stacks.ModuleStalk.stalkModule`, Mathlib's `PresheafOfModules` instance, which is the
  structure ampleness is stated over, through
  `Stacks.ModuleStalk.maximalSmul` and `Stacks.Ample.nonvanishingLocus`.

`rfl` fails between them. Since both are characterised on germs, they are nevertheless
*equal*, and that is what this file proves; it also identifies the stalk map of a morphism with
the ring homomorphism the pullback identification is taken along, which is how locality of that
homomorphism becomes available.

Both halves are proved for an arbitrary morphism of ringed spaces and then read off for a scheme
and for a locally ringed space, because Stacks Tag 0098 is itself stated for ringed spaces and
Stacks Tag 0H78 for locally ringed spaces.

Together these are exactly the two bridges needed to apply Stacks Tag 0098 to a question about
nonvanishing loci, and neither existed.

## Main results

* `Stacks.NonvanishingPullback.stalkModule_eq`: **the two module structures are equal**, and
  `stalkModule_eq_scheme` is the same statement at the name ampleness uses.
* `Stacks.NonvanishingPullback.mem_maximalSmul_iff`: consequently, membership in
  `Stacks.ModuleStalk.maximalSmul` is membership in `𝔪_x · M_x` formed in the Tag 01CB structure.
* `Stacks.NonvanishingPullback.commStalkRingMap_germ`: the comparison ring homomorphism on germs,
  for an arbitrary morphism of ringed spaces.
* `Stacks.NonvanishingPullback.commStalkRingMap_eq_stalkMap` and
  `commStalkRingMap_eq_stalkMap_lrs`: it **is** the stalk map, of a morphism of schemes and of a
  morphism of locally ringed spaces respectively.
* `Stacks.NonvanishingPullback.isLocalHom_commStalkRingMap` and
  `isLocalHom_commStalkRingMap_lrs`: hence it is a local homomorphism.

## Implementation notes

**Every step out of the Tag 01CB spelling is term-mode.** `rw` and `simp` elaborate congruence
motives at implicit transparency, and the two spellings of a `RingCat`-valued stalk —
`Stacks.PullbackTensorIso.ringCatStalk` and `Stacks.ModuleSkyscraper.Stalk (structureSheafRing _)` —
are one unfolding apart, so a rewrite whose motive mentions both reports that it cannot find its
pattern. For instance, `rw [RingEquiv.apply_symm_apply]` fails on the goal of
`commStalkRingMap_germ` for this reason. The cure is `congrArg` at an explicitly typed binder,
which elaborates at default transparency.

**The instance equality is `Module.ext`, whose hypothesis is an equality of the two `SMul.smul`
functions**, not a pointwise statement, so it is supplied as a double `funext` rather than by
`intro`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingPullback

/-! ### The two module structures on a stalk -/

/-- **The module structure of Stacks Tag 01CB on the stalk of an `𝒪_X`-module is Mathlib's**, by
definition. -/
theorem stalkModule_eq {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Z)) (y
      : Z.carrier) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Z M.val y =
      Stacks.NonvanishingTrivialize.stalkModule Z M y :=
  rfl

/-- `Stacks.NonvanishingPullback.stalkModule_eq` at the scheme spelling of the module structure
ampleness is stated over. The two right-hand sides are the same term; only the name differs. -/
theorem stalkModule_eq_scheme {X : Scheme.{u}} (M : X.Modules) (y : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val y =
      Stacks.ModuleStalk.stalkModule M y :=
  stalkModule_eq (Z := X.toRingedSpace) M y

/-- **`𝔪_x · M_x` means the same thing in the two spellings.** The left-hand side is
`Stacks.ModuleStalk.maximalSmul`, which ampleness is stated over; the right-hand side is the same
submodule formed in the module structure of Stacks Tag 01CB, which the identification of the
stalk of a pullback is stated over. -/
theorem mem_maximalSmul_iff {X : Scheme.{u}} (M : X.Modules) (y : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y) :
    m ∈ Stacks.ModuleStalk.maximalSmul M y ↔
      letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val y
      m ∈ IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
        X.toRingedSpace y) •
        (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace y)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace M.val y)) := by
  change m ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
    (⊤ : Submodule (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y)) ↔ _
  rw [← stalkModule_eq_scheme M y]
  exact Iff.rfl

/-! ### The comparison ring homomorphism is the stalk map -/

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (x' : X')

/-- **The ring homomorphism of Stacks Tag 0098 on germs**: it carries the germ of `r` at `i x'`
to the germ of `i^♯ r` at `x'`, which is the defining formula of the stalk map. -/
theorem commStalkRingMap_germ {Z' Z : RingedSpace.{u, u}} (g : Z' ⟶ Z) (z' : Z'.carrier)
    (V : Opens Z.carrier) (hV : g.hom.base z' ∈ V) (r : Z.presheaf.obj (op V)) :
    Stacks.PullbackTensorIso.commStalkRingMap g z'
        ((Z.presheaf.germ V (g.hom.base z') hV).hom r) =
      (Z'.presheaf.germ ((Opens.map g.hom.base).obj V) z' hV).hom
        ((structureSheafHom g).hom.app (op V) r) := by
  have h1 : (Stacks.PullbackTensorIso.stalkRingEquiv Z (g.hom.base z'))
      ((Z.presheaf.germ V (g.hom.base z') hV).hom r) =
      Stacks.ModuleSkyscraper.germ (structureSheafRing Z) (g.hom.base z') V hV r :=
    Stacks.PullbackTensorIso.stalkRingEquiv_germ Z (g.hom.base z') V hV r
  have h2 := Stacks.ModuleSkyscraper.stalkRingMap_germ g.hom.base
      (structureSheafRing Z') (structureSheafRing Z) (structureSheafHom g) z' V hV r
  have h3 : (Stacks.PullbackTensorIso.stalkRingEquiv Z' z')
      ((Z'.presheaf.germ ((Opens.map g.hom.base).obj V) z' hV).hom
        ((structureSheafHom g).hom.app (op V) r)) =
      Stacks.ModuleSkyscraper.germ (structureSheafRing Z') z' ((Opens.map g.hom.base).obj V) hV
        ((structureSheafHom g).hom.app (op V) r) :=
    Stacks.PullbackTensorIso.stalkRingEquiv_germ Z' z' ((Opens.map g.hom.base).obj V) hV _
  refine (Stacks.PullbackTensorIso.stalkRingEquiv Z' z').injective ?_
  refine Eq.trans ?_ h3.symm
  change (Stacks.PullbackTensorIso.stalkRingEquiv Z' z')
      ((Stacks.PullbackTensorIso.stalkRingEquiv Z' z').symm
        ((Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap g z').hom
          ((Stacks.PullbackTensorIso.stalkRingEquiv Z (g.hom.base z'))
            ((Z.presheaf.germ V (g.hom.base z') hV).hom r)))) = _
  refine (RingEquiv.apply_symm_apply _ _).trans ?_
  exact Eq.trans (congrArg (fun z =>
    (Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap g z').hom z) h1) h2

/-- **The ring homomorphism the pullback identification of Stacks Tag 0098 is taken along is the
stalk map of the morphism of schemes.** Both are ring homomorphisms out of a stalk, so they agree
as soon as they agree on germs. -/
theorem commStalkRingMap_eq_stalkMap :
    Stacks.PullbackTensorIso.commStalkRingMap i.toLRSHom.toShHom x' = (i.stalkMap x').hom := by
  refine RingHom.ext fun t => ?_
  obtain ⟨V, hV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine Eq.trans (congrArg _ hr.symm)
    (Eq.trans (commStalkRingMap_germ i.toLRSHom.toShHom x' V hV r) ?_)
  exact Eq.trans (AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply i V x' hV r).symm
    (congrArg _ hr)

/-- **The comparison ring homomorphism of a morphism of locally ringed spaces is its stalk
map.** The form Stacks Tag 0H78 is stated in. -/
theorem commStalkRingMap_eq_stalkMap_lrs {Y W : LocallyRingedSpace.{u}} (g : Y ⟶ W) (y : Y) :
    Stacks.PullbackTensorIso.commStalkRingMap g.toShHom y = (g.stalkMap y).hom := by
  refine RingHom.ext fun t => ?_
  obtain ⟨V, hV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq W.presheaf t
  refine Eq.trans (congrArg _ hr.symm)
    (Eq.trans (commStalkRingMap_germ g.toShHom y V hV r) ?_)
  exact Eq.trans (AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply g V y hV r).symm
    (congrArg _ hr)

/-- **The comparison ring homomorphism of a morphism of locally ringed spaces is local.** -/
theorem isLocalHom_commStalkRingMap_lrs {Y W : LocallyRingedSpace.{u}} (g : Y ⟶ W) (y : Y) :
    IsLocalHom (Stacks.PullbackTensorIso.commStalkRingMap g.toShHom y) :=
  (commStalkRingMap_eq_stalkMap_lrs g y) ▸ g.2 y

/-- **The comparison ring homomorphism is local.** Immediate from
`Stacks.NonvanishingPullback.commStalkRingMap_eq_stalkMap` and Mathlib's instance for the stalk
map of a morphism of schemes, and it is the one hypothesis the algebraic half of Stacks Tag 0H78
needs. -/
theorem isLocalHom_commStalkRingMap :
    IsLocalHom (Stacks.PullbackTensorIso.commStalkRingMap i.toLRSHom.toShHom x') :=
  (commStalkRingMap_eq_stalkMap i x') ▸ (inferInstance : IsLocalHom (i.stalkMap x').hom)

end Stacks.NonvanishingPullback

end
