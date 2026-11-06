module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.FiniteLocallyConstantClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafDictionary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The value of the fundamental group dictionary on a constant sheaf of modules

Let `X` be a connected scheme belonging to a big étale site, let `x` be a geometric point of it
and let `Λ` be a finite ring. This file computes the value of the dictionary of Stacks 0DV5 (3)
on the constant sheaf of `Λ`-modules with value a finite `Λ`-module `M`: the action of
`π₁(X, x)` on it is trivial, and its underlying finite set is that of `M`.

The sets case is `AlgebraicGeometry.rho_eq_one_finiteLocallyConstantSetsEquivalence_constantSheaf`
and `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceConstantSheafEquiv`; this file first
restates it for an arbitrary sheaf of sets *isomorphic* to a constant sheaf on a finite set,
which is the form in which it can be applied to the sheaf of sets underlying a constant sheaf of
modules, and then applies it.

## Main definitions

* `AlgebraicGeometry.constantSheafModuleForgetIso`: **the underlying sheaf of sets of a constant
  sheaf of `Λ`-modules is the constant sheaf on its underlying set.**
* `AlgebraicGeometry.constantSheafFiniteTypeLocallyConstantModule`: the constant sheaf of
  `Λ`-modules on a finite module, as an object of the finite type locally constant sheaves of
  `Λ`-modules.

## Main results

* `AlgebraicGeometry.rho_eq_one_finiteLocallyConstantSetsEquivalence_of_constant` and
  `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceEquivOfConstant`: Stacks 0DV5 (1) on a
  sheaf of sets isomorphic to a constant sheaf with finite value.
* `AlgebraicGeometry.rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf`:
  **Stacks 0DV5 (3) on a constant sheaf of modules: the action is trivial.**
* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceConstantSheafEquiv`:
  **Stacks 0DV5 (3) on a constant sheaf of modules: the underlying finite set.**

## Implementation notes

*The forgetful functors out of `ModuleCat`.* The dictionary of Stacks 0DV5 (3) is the dictionary
of part (2) read on additive functors out of `CategoryTheory.SingleObj Λ`, and that of part (2)
is the dictionary of part (1) read on commutative group objects. Both readings are strict on
underlying data — the units of
`Stacks.GroupCohomology.finiteTypeContinuousModuleScalarActionEquivalence` and of
`Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence` are identities, and
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_forgetAction` holds
by `rfl` — so the finite set underlying the value of part (3) on a sheaf of `Λ`-modules is, on the
nose, the value of part (1) on the sheaf of sets underlying it. What has to be supplied is the
identification of that sheaf of sets for a constant sheaf of modules, and it needs only one
instance of `CategoryTheory.constantCommuteCompose`, for `CategoryTheory.forget (ModuleCat Λ)`:
the two forgetful functors out of `ModuleCat Λ` that the dictionary passes through compose to it
by `Stacks.ConstantSheaf.sheafCompose_forget₂_forget`, so no separate statement for
`forget₂ (ModuleCat Λ) AddCommGrpCat` is needed. The hypothesis that sheafification commutes with
the forgetful functor is a theorem at this module universe,
`Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat`.

*Why the sets case is restated for an arbitrary trivializable sheaf.* The sheaf of sets
underlying the constant sheaf of `Λ`-modules on `M` is not the constant sheaf on `ULift ι` for an
index type `ι` in the universe of the schemes; it is the constant sheaf on `ToType M`, which lives
one universe up. The two statements below take the value in the sheaf universe together with an
isomorphism, and reduce to the `ULift ι` form by choosing a bijection of `E` with a `Fin n`.

*What is not proved here: the `Λ`-linear refinement.* The underlying object of the value of part
(3) is a `Λ`-module and `M` is a `Λ`-module, but what is produced below is a bijection of their
underlying sets, not an isomorphism of `Λ`-modules — nor even of abelian groups. This is not a
gap in the plumbing but a missing piece of mathematics. By
`CategoryTheory.scalarActionModule` the scalar action on the value is `a • v = U(µ a) v`, where
`U` is the underlying-set functor of the composite of the constant-sheaf functor with the
dictionary of part (1) and `µ a` is multiplication by `a` on `M`; so a bijection is `Λ`-linear
exactly when it is natural in the value of the constant sheaf, and the same holds one level down
for additivity. No naturality is available: the sets-case computation goes through Stacks 03RV in
the form `Stacks.EtaleCohomology.constantSheafIsoSheafifiedYonedaSplitObj`, which identifies the
constant sheaf on `ι` with the sheaf represented by the split cover `∐_{i : ι} X`, and through
`Stacks.FundamentalGroup.splitCoverFiberEquiv`, and neither is accompanied by a naturality
statement in `ι` — indeed the library contains no functor out of `FintypeCat` at all, so there is
nothing for such a statement to be about. Supplying it means producing, for a single map
`h : ι ⟶ κ` of finite index types, the comparison of `Stacks.FundamentalGroup.splitCoverMap h`
with the induced map of split objects of the site and the two naturality squares; the fibre half
is already available as
`Stacks.FundamentalGroup.splitCoverInj_comp_splitCoverMap`.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf Stacks.GroupCohomology
open scoped FintypeCatDiscrete

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-! ### Sheaves of sets isomorphic to a constant sheaf with finite value -/

/-- **The constant sheaf of sets with finite value is finite locally constant.** It is
represented by a finite disjoint union of copies of `X`, which is Stacks 03RV for a finite
constant sheaf, and a sheaf represented by a finite object of the small étale site is finite
locally constant. -/
public theorem isFiniteLocallyConstant_constantSheafType (E : Type (u + 1)) [Finite E] :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2)
      ((constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj E) :=
  Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable B X _
    (Stacks.EtaleCohomology.exists_finiteEtaleRepresentable_constantSheaf B X.2 E)

section SetsOfConstant

variable [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **Stacks Project, Tag 0DV5 (1) on a trivializable sheaf of sets: the action.** The finite
continuous `π₁(X, x)`-set attached to a finite locally constant sheaf of sets which is isomorphic
to a constant sheaf with finite value carries the trivial action.

This is `AlgebraicGeometry.rho_eq_one_finiteLocallyConstantSetsEquivalence_constantSheaf`, whose
value is taken in the universe of the schemes, transported along the isomorphism; the value `E`
is matched with a `ULift` of a `Fin n` in that universe. -/
public theorem rho_eq_one_finiteLocallyConstantSetsEquivalence_of_constant
    (F : FiniteLocallyConstantSheaf B X) (E : Type (u + 1)) [Finite E]
    (e : (constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj E ≅ F.obj)
    (σ : EtaleFundamentalGroup X.1 x) :
    ((finiteLocallyConstantSetsEquivalence B X x).functor.obj F).obj.ρ σ = 1 := by
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin E
  refine contAction_rho_eq_one_of_iso
    ((finiteLocallyConstantSetsEquivalence B X x).functor.mapIso
      (ObjectProperty.isoMk
        (P := fun G : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
          IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) G)
        (X := constantSheafFiniteLocallyConstant B X (ULift.{u} (Fin n))) (Y := F)
        ((constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).mapIso
            (Equiv.toIso ((Equiv.ulift.trans Equiv.ulift).trans e₀.symm)) ≪≫ e)))
    (fun τ ↦ rho_eq_one_finiteLocallyConstantSetsEquivalence_constantSheaf B X _ x τ) σ

/-- **Stacks Project, Tag 0DV5 (1) on a trivializable sheaf of sets: the underlying set.** The
finite continuous `π₁(X, x)`-set attached to a finite locally constant sheaf of sets which is
isomorphic to the constant sheaf on a finite set `E` has `E` as its underlying set. -/
public def finiteLocallyConstantSetsEquivalenceEquivOfConstant
    (F : FiniteLocallyConstantSheaf B X) (E : Type (u + 1)) [Finite E]
    (e : (constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj E ≅ F.obj) :
    ToType ((finiteLocallyConstantSetsEquivalence B X x).functor.obj F).obj.V ≃ E :=
  (FintypeCat.equivEquivIso.symm (contActionIsoV
      ((finiteLocallyConstantSetsEquivalence B X x).functor.mapIso
        (ObjectProperty.isoMk
          (P := fun G : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
            IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) G)
          (X := constantSheafFiniteLocallyConstant B X (ULift.{u} (Fin (Nat.card E))))
          (Y := F)
          ((constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).mapIso
              (Equiv.toIso ((Equiv.ulift.trans Equiv.ulift).trans
                (Finite.equivFin E).symm)) ≪≫ e))))).symm.trans
    ((finiteLocallyConstantSetsEquivalenceConstantSheafEquiv B X
        (ULift.{u} (Fin (Nat.card E))) x).trans
      (Equiv.ulift.trans (Finite.equivFin E).symm))

end SetsOfConstant

/-! ### The constant sheaf of modules -/

section Modules

variable (Λ : Type r) [Ring Λ]

/-- **The sheaf of sets underlying a constant sheaf of `Λ`-modules is the constant sheaf of sets
on its underlying set.** This is `CategoryTheory.constantCommuteCompose` for
`CategoryTheory.forget (ModuleCat Λ)`, whose hypothesis that sheafification commutes with the
forgetful functor is `Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat` at this
module universe. -/
@[sga "4 II 6.4" "special case"]
public def constantSheafModuleForgetIso (M : ModuleCat.{u + 1} Λ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2) (forget (ModuleCat.{u + 1} Λ))).obj
        ((constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M) ≅
      (constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj (ToType M) :=
  letI : (SmallEtale.topology B X.1 X.2).PreservesSheafification
      (forget (ModuleCat.{u + 1} Λ)) :=
    preservesSheafification_forget_moduleCat.{u, u + 1, u + 1} _ Λ
  (constantCommuteCompose (SmallEtale.topology B X.1 X.2)
    (forget (ModuleCat.{u + 1} Λ))).app M

/-- **The same identification, read through the two forgetful functors the dictionary passes
through.** The dictionary of Stacks 0DV5 (3) forgets the module structure in two steps, to abelian
groups and then to sets; the two steps compose to the forgetful functor to sets by
`Stacks.ConstantSheaf.sheafCompose_forget₂_forget`, so
`AlgebraicGeometry.constantSheafModuleForgetIso` is the identification in that spelling too. -/
public def constantSheafModuleForget₂ForgetIso (M : ModuleCat.{u + 1} Λ) :
    (constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj (ToType M) ≅
      (sheafCompose (SmallEtale.topology B X.1 X.2) (forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose (SmallEtale.topology B X.1 X.2)
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M)) :=
  (constantSheafModuleForgetIso B X Λ M).symm ≪≫
    eqToIso (sheafCompose_forget₂_forget (SmallEtale.topology B X.1 X.2) Λ _).symm

variable [Finite Λ]

/-- **The constant sheaf of `Λ`-modules on a finite module is finite locally constant.** Over a
finite ring finite local constancy of a sheaf of `Λ`-modules is a property of the sheaf of sets
underlying it, `Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_of_forget`, and for a
constant sheaf that is the constant sheaf on a finite set. -/
public theorem isFiniteLocallyConstant_constantSheafModule (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2)
      ((constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M) :=
  isFiniteLocallyConstant_moduleSheaf_of_forget _ Λ _
    (ObjectProperty.prop_of_iso
      (P := fun F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
        IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F)
      (constantSheafModuleForgetIso B X Λ M).symm
      (isFiniteLocallyConstant_constantSheafType B X (ToType M)))

section Dictionary

variable [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- The constant sheaf of `Λ`-modules on a finite `Λ`-module, as an object of the left-hand side
of Stacks 0DV5 (3). Over a finite ring Tag 03RW's condition is finite local constancy,
`AlgebraicGeometry.isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant`. -/
public def constantSheafFiniteTypeLocallyConstantModule (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] :
    ObjectProperty.FullSubcategory
      (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) :=
  ⟨(constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M, by
    rw [congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B X Λ)]
    exact isFiniteLocallyConstant_constantSheafModule B X Λ M⟩

/-- The sheaf of sets the dictionary of Stacks 0DV5 (3) reads a constant sheaf of `Λ`-modules
through, as a finite locally constant sheaf of sets. -/
public def constantSheafModuleUnderlyingFiniteLocallyConstant (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] : FiniteLocallyConstantSheaf B X :=
  ⟨(sheafCompose (SmallEtale.topology B X.1 X.2) (forget AddCommGrpCat.{u + 1})).obj
      ((sheafCompose (SmallEtale.topology B X.1 X.2)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((constantSheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)).obj M)),
    ObjectProperty.prop_of_iso
      (P := fun F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
        IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F)
      (constantSheafModuleForget₂ForgetIso B X Λ M)
      (isFiniteLocallyConstant_constantSheafType B X (ToType M))⟩

/-- **Stacks Project, Tag 0DV5 (3) on a constant sheaf of modules: the action.** The finite
`Λ`-module with a commuting continuous `π₁(X, x)`-action attached to the constant sheaf of
`Λ`-modules with value a finite `Λ`-module carries the trivial action.

The action of the value of part (3) is, on the nose, the action of the value of part (1) on the
sheaf of sets underlying the sheaf of modules: both readings the dictionary performs are strict on
underlying data. So this is
`AlgebraicGeometry.rho_eq_one_finiteLocallyConstantSetsEquivalence_of_constant` applied to that
sheaf of sets, which `AlgebraicGeometry.constantSheafModuleForget₂ForgetIso` identifies with the
constant sheaf on the underlying set of the module. -/
public theorem rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf
    (M : ModuleCat.{u + 1} Λ) [Finite (ToType M)] (σ : EtaleFundamentalGroup X.1 x) :
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
      (constantSheafFiniteTypeLocallyConstantModule B X Λ M)).obj.obj.obj.ρ σ = 1 := by
  refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_))
  exact ConcreteCategory.congr_hom (congrArg End.asHom
    (rho_eq_one_finiteLocallyConstantSetsEquivalence_of_constant B X x
      (constantSheafModuleUnderlyingFiniteLocallyConstant B X Λ M) (ToType M)
      (constantSheafModuleForget₂ForgetIso B X Λ M) σ)) v

/-- **Stacks Project, Tag 0DV5 (3) on a constant sheaf of modules: the underlying set.** The
finite `Λ`-module with a commuting continuous `π₁(X, x)`-action attached to the constant sheaf of
`Λ`-modules with value a finite `Λ`-module `M` has the underlying set of `M` as the underlying
set of its module.

This is a bijection and not an isomorphism of `Λ`-modules; see the implementation notes for what
would have to be proved to upgrade it. -/
public def finiteTypeLocallyConstantModuleSheafEquivalenceConstantSheafEquiv
    (M : ModuleCat.{u + 1} Λ) [Finite (ToType M)] :
    ToType ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
      (constantSheafFiniteTypeLocallyConstantModule B X Λ M)).obj.obj.obj.V ≃ ToType M :=
  finiteLocallyConstantSetsEquivalenceEquivOfConstant B X x
    (constantSheafModuleUnderlyingFiniteLocallyConstant B X Λ M) (ToType M)
    (constantSheafModuleForget₂ForgetIso B X Λ M)

end Dictionary

end Modules

end AlgebraicGeometry

end
