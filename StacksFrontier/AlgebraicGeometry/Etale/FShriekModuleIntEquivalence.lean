module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian étale sheaves are étale sheaves of modules over the lifted integers

Two worlds of coefficients coexist on a small étale site: abelian sheaves, in which the direct
image with compact support `f_!` of Stacks 0F6R and its base change are constructed, and
sheaves of `Λ`-modules, in which the projection formula of Stacks 0GKF is proved. At
`Λ = ULift ℤ` the two are the same world, and this file is the dictionary: the equivalence
itself, and the statement that each piece of vocabulary needed for the trace map of
Stacks 0GKG — `f_!`, the inverse image `f^{-1}`, the constant sheaf and the monoidal unit —
is carried across it.

The one thing that makes the dictionary usable is that its functor is *on the nose* the
functor forgetting the module structure, `AlgebraicGeometry.SmallEtale.forgetModuleSheaf`.
That is why the equivalence is assembled from `forget₂ (ModuleCat (ULift ℤ)) AddCommGrpCat`
rather than from `AddCommGrpCat.uliftIntEquivalence`, whose functor is a composite of a
restriction of scalars with the forgetful functor from `ℤ`-modules: the two functors are
definitionally equal, so the unit, counit and triangle identity of the latter serve as the
data of the former, and the resulting equivalence has the forgetful functor as its functor
syntactically. Each comparison below is then a lemma that is already available about
`forgetModuleSheaf` or about a change of coefficients along an equivalence.

## Main definitions

* `AddCommGrpCat.uliftIntForgetEquivalence` — abelian groups are the modules over `ULift ℤ`,
  the equivalence being the forgetful functor itself.
* `AlgebraicGeometry.SmallEtale.abelianSheafUliftIntEquivalence` — the induced equivalence
  between étale sheaves of `ULift ℤ`-modules and abelian étale sheaves.
* `AlgebraicGeometry.SmallEtale.fShriekModForget_natIso` — `f_!` commutes with it.
* `AlgebraicGeometry.SmallEtale.modPullbackForget_natIso` — `f^{-1}` commutes with it.
* `AlgebraicGeometry.SmallEtale.constantSheafForget_natIso` — the constant sheaf commutes
  with it.

## Main results

* `AlgebraicGeometry.SmallEtale.abelianSheafUliftIntEquivalence_functor` — the functor of the
  equivalence is the functor forgetting the module structure, on the nose.
* `AlgebraicGeometry.SmallEtale.moduleSheaf_tensorUnit_eq` — the unit of the tensor product of
  étale sheaves of `Λ`-modules is the constant sheaf with value the unit of `ModuleCat Λ`.

## Implementation notes

The coefficient universe is the cutoff `max (u + 1) v` at which `f_!` and the projection
formula live, so the coefficient ring is `ULift.{max (u + 1) v} ℤ` and the coefficient
universe argument `r` of `AlgebraicGeometry.SmallEtale.ModuleSheaf` is instantiated to
`max (u + 1) v`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift` on why that argument is supplied
explicitly.

The isomorphisms for the inverse image and the constant sheaf are the general ones for a
change of coefficients along an equivalence,
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` and
`CategoryTheory.Sheaf.constantSheafCoefficientIso`: both sides of each are left adjoint to the
same functor. The isomorphism for `f_!` is not of that kind — `f_!` is not defined on sheaves
of modules by transport but as a lift, so its comparison is the identity,
`AlgebraicGeometry.SmallEtale.fShriekModForgetIso`.

Nothing here carries a `stacks` attribute: every declaration is a dictionary entry between
two formalisations of the same coefficients, not a statement of the source.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.MonoidalCategory

universe u v w

namespace AddCommGrpCat

/-- **Abelian groups are the modules over a copy of the integers in their own universe, and
the equivalence is the forgetful functor.** This is `AddCommGrpCat.uliftIntEquivalence` with
its functor replaced by the definitionally equal `forget₂`, so that postcomposing sheaves with
it is literally the functor forgetting the module structure. -/
@[sga "3 I 3.1.3" "special case", sga "4 IV 11.1.5" "punctual topos"]
public def uliftIntForgetEquivalence : ModuleCat.{w} ULiftInt.{w} ≌ AddCommGrpCat.{w} where
  functor := forget₂ (ModuleCat.{w} ULiftInt.{w}) AddCommGrpCat.{w}
  inverse := uliftIntEquivalence.{w}.inverse
  unitIso := uliftIntEquivalence.{w}.unitIso
  counitIso := uliftIntEquivalence.{w}.counitIso
  functor_unitIso_comp := uliftIntEquivalence.{w}.functor_unitIso_comp

/-- The functor of `AddCommGrpCat.uliftIntForgetEquivalence` is the forgetful functor from
`ULift ℤ`-modules to abelian groups. -/
@[simp]
public theorem uliftIntForgetEquivalence_functor :
    uliftIntForgetEquivalence.{w}.functor =
      forget₂ (ModuleCat.{w} ULiftInt.{w}) AddCommGrpCat.{w} :=
  rfl

end AddCommGrpCat

namespace AlgebraicGeometry.SmallEtale

section Dictionary

attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-- **Abelian étale sheaves are étale sheaves of modules over the lifted integers.** The
change of coefficients along `AddCommGrpCat.uliftIntForgetEquivalence`, whose functor is the
functor forgetting the module structure; see
`AlgebraicGeometry.SmallEtale.abelianSheafUliftIntEquivalence_functor`. -/
@[sga "4 IV 11.1.5" "small étale topos"]
public def abelianSheafUliftIntEquivalence :
    ModuleSheaf.{u, v, max (u + 1) v} B S (AddCommGrpCat.ULiftInt.{max (u + 1) v}) ≌
      Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v} :=
  Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property)
    AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}

/-- **The dictionary is the forgetful functor.** The functor of
`AlgebraicGeometry.SmallEtale.abelianSheafUliftIntEquivalence` is
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf` at `Λ = ULift ℤ`, on the nose, so every
statement already proved about the underlying abelian sheaf of a sheaf of modules is a
statement about this equivalence. -/
public theorem abelianSheafUliftIntEquivalence_functor :
    (abelianSheafUliftIntEquivalence.{u, v} B S).functor =
      forgetModuleSheaf.{u, v, max (u + 1) v} B S (AddCommGrpCat.ULiftInt.{max (u + 1) v}) :=
  rfl

variable {X Y : B.Scheme} (f : X ⟶ Y)

section Shriek

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The direct image with compact support commutes with the dictionary.** The `ULift ℤ`-linear
`f_!` of `AlgebraicGeometry.SmallEtale.fShriekMod` becomes the `f_!` of Stacks 0F6R on abelian
sheaves. The two composites are the same functor, the module-linear `f_!` being a lift of the
abelian one rather than a transport of it. -/
public def fShriekModForget_natIso :
    fShriekMod.{u, v, max (u + 1) v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f ⋙
        (abelianSheafUliftIntEquivalence.{u, v} B Y).functor ≅
      (abelianSheafUliftIntEquivalence.{u, v} B X).functor ⋙ fShriekFunctor.{u, v} B f :=
  fShriekModForgetIso.{u, v, max (u + 1) v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f

end Shriek

/-- **The inverse image commutes with the dictionary.** The `ULift ℤ`-linear `f^{-1}` of
`AlgebraicGeometry.SmallEtale.modPullback` becomes the `f^{-1}` of
`AlgebraicGeometry.SmallEtale.abPullback` on abelian sheaves. Both composites are left adjoint
to the direct image followed by the inverse change of coefficients. -/
public def modPullbackForget_natIso :
    modPullback.{u, v, max (u + 1) v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f ⋙
        (abelianSheafUliftIntEquivalence.{u, v} B X).functor ≅
      (abelianSheafUliftIntEquivalence.{u, v} B Y).functor ⋙ abPullback.{u, v} B f :=
  Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}

/-- **The constant sheaf commutes with the dictionary.** The constant sheaf of étale sheaves of
`ULift ℤ`-modules becomes the constant abelian étale sheaf on the underlying abelian group.
Both composites are left adjoint to evaluation at the final object of the small étale site
followed by the inverse change of coefficients. -/
public def constantSheafForget_natIso :
    constantSheaf (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} AddCommGrpCat.ULiftInt.{max (u + 1) v}) ⋙
        (abelianSheafUliftIntEquivalence.{u, v} B S).functor ≅
      AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}.functor ⋙
        constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v} :=
  Sheaf.constantSheafCoefficientIso (SmallEtale.topology B S.obj S.property)
    AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}

end Dictionary

section MonoidalUnit

attribute [local instance] moduleSheafMonoidal

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] (S : B.Scheme)

/-- **The unit of the tensor product of étale sheaves of `Λ`-modules is a constant sheaf.** The
monoidal structure of `AlgebraicGeometry.SmallEtale.moduleSheafMonoidal` is the one obtained by
localizing the objectwise tensor product of presheaves, whose unit is the constant presheaf with
value `Λ`; sheafifying it is by definition the constant sheaf with value `Λ`. -/
public theorem moduleSheaf_tensorUnit_eq :
    (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)) =
      (constantSheaf (SmallEtale.topology B S.obj S.property)
        (ModuleCat.{max (u + 1) v} Λ)).obj (𝟙_ (ModuleCat.{max (u + 1) v} Λ)) :=
  rfl

end MonoidalUnit

end AlgebraicGeometry.SmallEtale

end
