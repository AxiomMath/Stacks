module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk

/-!
# A strict section of the forgetful functor to abelian groups

An abelian group carries exactly one module structure over a copy of the integers, so the
functor forgetting the module structure of a `ULift ℤ`-module has a *section*: the functor
sending an abelian group to itself, equipped with that unique module structure. Unlike the
quasi-inverse of the equivalence
`AddCommGrpCat.uliftIntForgetEquivalence` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence`, whose counit is only an
isomorphism, this section composes with the forgetful functor to the identity functor *on the
nose*, both on abelian groups and on abelian sheaves of the small étale site. That is what makes
a statement about `AddCommGrpCat`-valued étale sheaves — the trace map of Stacks 0GKG — readable
off a statement about étale sheaves of `ULift ℤ`-modules, where the projection formula of
Stacks 0GKF is available, with no transport to perform.

## Main definitions

* `AddCommGrpCat.uliftIntModuleCat` — the section of the forgetful functor: an abelian group is
  a `ULift ℤ`-module, on the same underlying type.
* `AddCommGrpCat.uliftIntModuleCatIsoInverse` — it is the quasi-inverse of the forgetful
  functor, up to isomorphism; this is what makes it preserve limits.
* `AlgebraicGeometry.SmallEtale.intModuleSheaf` — the induced section on étale sheaves: an
  abelian étale sheaf is an étale sheaf of `ULift ℤ`-modules.

## Main results

* `AddCommGrpCat.uliftIntModuleCat_comp_forget₂` — the section composed with the forgetful
  functor is the identity functor, by `rfl`.
* `AlgebraicGeometry.SmallEtale.intModuleSheaf_comp_forgetModuleSheaf` — the same on étale
  sheaves, again by `rfl`.
* `AlgebraicGeometry.SmallEtale.forgetModuleSheaf_obj_intModuleSheaf_obj` — in particular an
  abelian étale sheaf is the underlying abelian sheaf of the sheaf of modules it becomes.

## Implementation notes

The unique `ULift ℤ`-module structure on an abelian group is already in the library as
`AddCommGrpCat.uliftIntModule`, a `local instance` of
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor`; it is restored as a local instance
here rather than duplicated, and `AddCommGrpCat.uliftInt_smul_eq_zsmul` from the same place is
what makes an additive map automatically linear over `ULift ℤ`.

Both identities with the forgetful functor hold by `rfl`: a bundled `AddCommGrpCat` is
reconstructed from its carrier and its instance by structure eta, a bundled `Sheaf` from its
presheaf, and a functor from its action on objects and morphisms, so no `eqToHom` and no
isomorphism intervenes anywhere. The existence of
`CategoryTheory.GrothendieckTopology.HasSheafCompose` for the section is obtained from
preservation of limits of every size, which holds because the section is isomorphic to the
quasi-inverse of an equivalence; it is *not* obtained from the sheaf condition directly.

Nothing here carries a `stacks` attribute: this is a dictionary entry between two
formalisations of the same coefficients, not a statement of the source.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AddCommGrpCat

section ModuleStructure

attribute [local instance] uliftIntModule

/-- **The section of the forgetful functor.** An abelian group is a module over a copy of the
integers in its own universe, on the same underlying type and with the same addition, and an
additive map between abelian groups is linear for those module structures. -/
public def uliftIntModuleCat : AddCommGrpCat.{w} ⥤ ModuleCat.{w} ULiftInt.{w} where
  obj A := ModuleCat.of ULiftInt.{w} (A : Type w)
  map {A B} φ := ModuleCat.ofHom
    { toFun := φ.hom
      map_add' := φ.hom.map_add
      map_smul' := fun r a => by
        rw [uliftInt_smul_eq_zsmul, uliftInt_smul_eq_zsmul]
        exact map_zsmul φ.hom _ _ }

end ModuleStructure

/-- **The section is a strict section.** Forgetting the module structure of the `ULift ℤ`-module
attached to an abelian group gives the abelian group back, on the nose: the two functors are
equal, not merely isomorphic. -/
public theorem uliftIntModuleCat_comp_forget₂ :
    uliftIntModuleCat.{w} ⋙ forget₂ (ModuleCat.{w} ULiftInt.{w}) AddCommGrpCat.{w} = 𝟭 _ :=
  rfl

/-- The section is the quasi-inverse of the forgetful functor up to isomorphism: both become the
inverse of `AddCommGrpCat.uliftIntForgetEquivalence` after composing with its fully faithful
functor. -/
public def uliftIntModuleCatIsoInverse :
    uliftIntModuleCat.{w} ≅ uliftIntForgetEquivalence.{w}.inverse :=
  Functor.fullyFaithfulCancelRight uliftIntForgetEquivalence.{w}.functor
    (eqToIso uliftIntModuleCat_comp_forget₂.{w} ≪≫
      uliftIntForgetEquivalence.{w}.counitIso.symm)

/-- The section preserves limits of every size, being isomorphic to the inverse of an
equivalence. -/
public instance preservesLimitsOfSize_uliftIntModuleCat :
    PreservesLimitsOfSize.{v, u} uliftIntModuleCat.{w} :=
  preservesLimits_of_natIso uliftIntModuleCatIsoInverse.{w}.symm

end AddCommGrpCat

namespace AlgebraicGeometry.SmallEtale

section Section

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-- Postcomposing a presheaf on the small étale site with the section of the forgetful functor
preserves the sheaf condition, the section preserving all limits. -/
public instance hasSheafCompose_uliftIntModuleCat :
    (SmallEtale.topology B S.obj S.property).HasSheafCompose
      AddCommGrpCat.uliftIntModuleCat.{max (u + 1) v} :=
  inferInstance

/-- **An abelian étale sheaf is an étale sheaf of `ULift ℤ`-modules.** The section of the
forgetful functor of `AddCommGrpCat.uliftIntModuleCat`, applied to the sections of a sheaf. -/
public def intModuleSheaf :
    Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v} ⥤
      ModuleSheaf.{u, v, max (u + 1) v} B S (AddCommGrpCat.ULiftInt.{max (u + 1) v}) :=
  sheafCompose _ AddCommGrpCat.uliftIntModuleCat.{max (u + 1) v}

/-- **The section on sheaves is a strict section.** Forgetting the module structure of the étale
sheaf of `ULift ℤ`-modules attached to an abelian étale sheaf gives the abelian sheaf back, on
the nose: the two functors are equal, not merely isomorphic. -/
public theorem intModuleSheaf_comp_forgetModuleSheaf :
    intModuleSheaf.{u, v} B S ⋙ forgetModuleSheaf.{u, v, max (u + 1) v} B S
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) = 𝟭 _ :=
  rfl

/-- An abelian étale sheaf is the underlying abelian sheaf of the étale sheaf of
`ULift ℤ`-modules attached to it. -/
public theorem forgetModuleSheaf_obj_intModuleSheaf_obj
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}) :
    (forgetModuleSheaf.{u, v, max (u + 1) v} B S (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
        ((intModuleSheaf.{u, v} B S).obj F) = F :=
  rfl

end Section

end AlgebraicGeometry.SmallEtale

end
