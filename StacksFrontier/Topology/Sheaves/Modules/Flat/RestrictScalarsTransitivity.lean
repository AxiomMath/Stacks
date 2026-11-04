module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transitivity of flatness along a restriction of scalars

Let `f : 𝒪 ⟶ 𝒪'` be a morphism of sheaves of commutative rings on a topological space and let
`H` be a sheaf of `𝒪'`-modules.  If `H` is flat over `𝒪'` and `f` is a flat morphism — that is,
`𝒪'` read as an `𝒪`-module is flat — then `H` read as an `𝒪`-module is flat.

This is the sheaf-of-modules counterpart of `Module.Flat.trans`, and it is the statement that
the library's two flatness transports did not cover: extension of scalars (Stacks 05V4,
`Stacks.FlatChangeOfRings.isFlat_extendScalars`) goes the other way, and
`Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso` restricts along
an *isomorphism* of structure sheaves only.

## Main results

* `Stacks.SheafOfModules.FlatRestrictScalars.isFlat_restrictScalars_of_isFlat`: **transitivity of
  flatness along a restriction of scalars.**
* `Stacks.SheafOfModules.FlatRestrictScalars.flat_commStalk_of_flat_unit`: the stalk of `𝒪'` is
  flat over the stalk of `𝒪` as soon as the unit `𝒪'`-module read as an `𝒪`-module is flat.
* `Stacks.SheafOfModules.FlatRestrictScalars.restrictScalars_stalk_smul`: the scalar action that
  restriction of scalars puts on a module stalk is the action of the stalk of `𝒪'` read through
  the stalk of `f`.

## Implementation notes

The proof is the stalkwise one.  Flatness of a sheaf of modules on a space is a condition on
stalks, Stacks 05NE (`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`, a biconditional),
and restriction of scalars does not change the underlying presheaf of abelian groups, hence does
not change the stalk; it only reads the scalars through the stalk of `f`
(`restrictScalars_stalk_smul`).  So the three ingredients of `Module.Flat.trans` are available
pointwise: the stalk of `H` is flat over the stalk of `𝒪'`, the stalk of `𝒪'` is flat over the
stalk of `𝒪`, and the actions are compatible by construction.  No comparison of tensor products
of sheaves intervenes, and in particular the base-change isomorphism
`Stacks.FlatChangeOfRings.baseChangeNatIso` — which is natural in the `𝒪'`-variable and would have
to be made natural in the `𝒪`-variable to serve here — is not needed.

Flatness of `𝒪'` over `𝒪` enters as the hypothesis `hf`, which is
`AlgebraicGeometry.SheafOfModules.IsFlatMap f` written out; it is written out rather than named so
that the universe arguments are the ones `isFlat_iff_stalk_flat` is stated at.

`unitStalkAddEquiv` identifies the stalk of the unit module of `𝒪'` with the stalk of `𝒪'`: the
first is the filtered colimit of the sections computed in `AddCommGrpCat`, the second the same
colimit computed in `CommRingCat`, and `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat
AddCommGrpCat` preserves it.  The library already has this identification five times over, each
time for the structure sheaf of a ringed space and over the germ-representative module structure
of Tag 01CB (`Stacks.IdealTorsion.unitStalkAddEquiv` and its copies); the form below is for an
arbitrary presheaf of commutative rings and over Mathlib's module structure on the stalk, which is
the one `isFlat_iff_stalk_flat` is stated at, so no `stalkModule_eq` crossing is needed.

Every rewrite that would have to cross the two spellings of the restricted module — the one where
the scalars are `𝒪` and the one where they are `𝒪'`, which have the same underlying presheaf of
abelian groups — is carried as an explicit `Eq.trans`/`congrArg` instead: `rw` re-checks the goal
at `implicit` transparency and does not find its pattern across that gap, while `Eq.trans` unifies
once at `default` transparency.

## References

* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public section
noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules.FlatRestrictScalars

/-! ### Transitivity of flatness of modules along a ring homomorphism -/

/-- **Transitivity of flatness along a ring homomorphism**, in the shape a stalkwise criterion
delivers it: the `R`-module structure on `M` is given in advance, and the hypothesis `hsmul` says
that it is the `S`-action read through `f`.  Mathlib's `Module.Flat.trans` asks instead for an
`Algebra R S` instance and a scalar tower, which `f` supplies once `hsmul` is known. -/
@[ega "0 6.2.1"]
public theorem flat_of_ringHom {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module S M] [Module R M] (f : R →+* S) (hSM : Module.Flat S M)
    (hRS : letI : Algebra R S := f.toAlgebra; Module.Flat R S)
    (hsmul : ∀ (r : R) (m : M), r • m = f r • m) :
    Module.Flat R M := by
  let : Algebra R S := f.toAlgebra
  have : IsScalarTower R S M := .of_algebraMap_smul fun r m => (hsmul r m).symm
  exact Module.Flat.trans R S M

/-! ### The stalk of a restriction of scalars -/

section Germs

variable {Y : TopCat.{u}} {R R' : TopCat.Presheaf CommRingCat.{u} Y} (φ : R ⟶ R')
  (N : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : Y)

/-- The map on `CommRingCat`-valued stalks induced by a morphism of presheaves of commutative
rings, with its source and target pinned at the `TopCat.Presheaf.stalk` spelling that the
module structures on stalks are stated over. -/
public def commStalkMap :
    TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x ⟶
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ

/-- `commStalkMap` carries the germ of a section to the germ of its image. -/
public theorem commStalkMap_germ (U : Opens Y) (hx : x ∈ U) (a : R.obj (op U)) :
    (commStalkMap φ x).hom (TopCat.Presheaf.germ (C := CommRingCat.{u}) R U x hx a) =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) R' U x hx (φ.app (op U) a) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ a

/-- A germ of a ring and a germ of an abelian group at `x` are germs of sections over one common
neighbourhood of `x`. -/
private theorem exists_germ_pair_eq {Y : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} Y)
    (A : TopCat.Presheaf AddCommGrpCat.{u} Y) (x : Y)
    (r : TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) A x) :
    ∃ (W : Opens Y) (hxW : x ∈ W) (a : R.obj (op W)) (b : A.obj (op W)),
      TopCat.Presheaf.germ (C := CommRingCat.{u}) R W x hxW a = r ∧
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) A W x hxW b = m := by
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) R r
  obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) A m
  exact ⟨U ⊓ V, ⟨hU, hV⟩, R.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a,
    A.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b,
    TopCat.Presheaf.germ_res_apply (C := CommRingCat.{u}) R _ x _ a,
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) A _ x _ b⟩

/-- **Restriction of scalars along `φ` does not change the stalk**: the action of the stalk of
`R` on it is the action of the stalk of `R'` read through `commStalkMap φ x`.  Both sides are
checked on germs, where the restricted action is the image section acting. -/
public theorem restrictScalars_stalk_smul
    (r : TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :
    letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
      inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((PresheafOfModules.restrictScalars
            (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))).obj N).presheaf x))
    r • m = (commStalkMap φ x).hom r • m := by
  let : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))).obj N).presheaf x))
  obtain ⟨W, hxW, a, b, rfl, rfl⟩ := exists_germ_pair_eq R N.presheaf x r m
  let N' := (PresheafOfModules.restrictScalars
    (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))).obj N
  rw [commStalkMap_germ]
  refine Eq.trans (PresheafOfModules.germ_smul N' x W hxW _ _).symm ?_
  exact PresheafOfModules.germ_smul N x W hxW _ _

/-- **The stalk of the unit module of `R'` is the stalk of `R'`**, as abelian groups: both are
the filtered colimit of the sections over the neighbourhoods of `x`, taken in `AddCommGrpCat`
and in `CommRingCat` respectively, and the forgetful functor preserves that colimit. -/
public def unitStalkAddEquiv :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x ≃+
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x :=
  (preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R')).symm.addCommGroupIsoToAddEquiv

/-- `unitStalkAddEquiv` carries the germ of a section of the unit module to the germ of the same
section of `R'`. -/
public theorem unitStalkAddEquiv_germ (U : Opens Y) (hx : x ∈ U) (r : R'.obj (op U)) :
    unitStalkAddEquiv (R' := R') x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf U x hx r) =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) R' U x hx r :=
  congrArg (fun f : AddCommGrpCat.of (R'.obj (op U)) ⟶
      AddCommGrpCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x) => f r)
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R') (.op ⟨U, hx⟩))

/-- `unitStalkAddEquiv` is linear over the stalk of `R'`: the action of that stalk on the stalk
of the unit module is multiplication in the stalk of `R'`. -/
public theorem unitStalkAddEquiv_smul
    (s : TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x) :
    unitStalkAddEquiv (R' := R') x (s • m) =
      s * unitStalkAddEquiv (R' := R') x m := by
  let PU := PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})
  obtain ⟨W, hxW, a, b, rfl, rfl⟩ := exists_germ_pair_eq R' PU.presheaf x s m
  refine Eq.trans (congrArg (unitStalkAddEquiv (R' := R') x)
    (PresheafOfModules.germ_smul PU x W hxW _ _).symm) ?_
  refine Eq.trans (unitStalkAddEquiv_germ (R' := R') x W hxW _) ?_
  refine Eq.trans ((TopCat.Presheaf.germ (C := CommRingCat.{u}) R' W x hxW).hom.map_mul _ _) ?_
  exact congrArg (fun t => (TopCat.Presheaf.germ (C := CommRingCat.{u}) R' W x hxW).hom _ * t)
    (unitStalkAddEquiv_germ (R' := R') x W hxW _).symm

/-- **Each stalk of `R'` is flat over the corresponding stalk of `R`**, as an algebra through
the stalk of `φ`, as soon as the unit `R'`-module read as an `R`-module has flat stalks.  This is
the middle term of the scalar tower that `isFlat_restrictScalars_of_isFlat` feeds to
`Module.Flat.trans`. -/
public theorem flat_commStalk_of_flat_unit
    (hf : Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))).obj
            (PresheafOfModules.unit
              (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u}))).presheaf x)) :
    letI : Algebra (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x) :=
      (commStalkMap φ x).hom.toAlgebra
    Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x) := by
  let : Algebra (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x) :=
    (commStalkMap φ x).hom.toAlgebra
  let : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))).obj
            (PresheafOfModules.unit
              (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u}))).presheaf x))
  have : Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x) := hf
  refine Module.Flat.of_linearEquiv
    (e := LinearEquiv.symm
      { unitStalkAddEquiv (R' := R') x with
        map_smul' := fun r m => ?_ })
  show unitStalkAddEquiv (R' := R') x (r • m) =
    (commStalkMap φ x).hom r * unitStalkAddEquiv (R' := R') x m
  refine Eq.trans (congrArg (unitStalkAddEquiv (R' := R') x)
    (restrictScalars_stalk_smul φ
      (PresheafOfModules.unit (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})) x r m)) ?_
  exact unitStalkAddEquiv_smul x _ m

end Germs

/-! ### Transitivity of flatness of sheaves of modules -/

/-- **Transitivity of flatness along a restriction of scalars.**  Let `f : O ⟶ O'` be a morphism
of sheaves of commutative rings on a topological space.  If `H` is a flat sheaf of `O'`-modules
and `O'` read as a sheaf of `O`-modules is flat — that is, `f` is a flat morphism, Stacks 03ER
part (4) — then `H` read as a sheaf of `O`-modules is flat.

Stacks 05NE reads flatness on stalks, restriction of scalars does not change a stalk, and
`Module.Flat.trans` then applies pointwise.  This is a step available to any proof, not a clause
of a tag, so it carries no `@[stacks]` attribute. -/
public theorem isFlat_restrictScalars_of_isFlat {Y : TopCat.{u}}
    {O O' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} (f : O ⟶ O')
    (H : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O'))
    (hH : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O') H)
    (hf : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O)
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat.{u} RingCat.{u})).map f)).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O')))) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O)
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat.{u} RingCat.{u})).map f)).obj H) := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat O _).2 fun x => ?_
  let targetModule : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) O'.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).map f)).obj H).val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := O'.obj) H.val x
  let sourceModule : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) O.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).map f)).obj H).val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := O.obj) ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat.{u} RingCat.{u})).map f)).obj H).val x
  exact @flat_of_ringHom _ _ _ _ _ _ targetModule sourceModule (commStalkMap f.hom x).hom
    ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat O' H).1 hH x)
    (flat_commStalk_of_flat_unit f.hom x
      ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat O _).1 hf x))
    (restrictScalars_stalk_smul f.hom H.val x)

end Stacks.SheafOfModules.FlatRestrictScalars

end

end
