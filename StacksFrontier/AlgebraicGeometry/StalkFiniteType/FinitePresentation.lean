module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.RingTheory.Flat.FlatStalkFinitePresentation

/-!
# The stalk of a finitely presented sheaf of modules is finitely presented

`Stacks.StalkFiniteType.finite_stalk` says that the stalk of a *finite type* sheaf of modules on
a scheme is a finite module over the local ring at the point. This file proves the finite
presentation counterpart: for `M : X.Modules` with `M.IsFinitePresentation`, the stalk `M_x` is a
finitely presented `𝒪_{X,x}`-module. Both
`StacksFrontier/AlgebraicGeometry/StalkFiniteType/FlatFinitePresentation.lean` and
`StacksFrontier/AlgebraicGeometry/StalkFreeBridge/StalkFree.lean` record that statement as missing
from this repository; it is no longer missing.

The route is affine-local and goes through the tilde construction rather than through generating
sections. Over `Spec R` a finitely presented sheaf of modules is quasi-coherent, hence is
`N^~` for `N = Γ(M, ⊤)` (Mathlib's `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`), and `N`
is finitely presented over `R` by Stacks 01PC (`AlgebraicGeometry.tilde_isFinitePresentation_iff`).
The stalk of `N^~` at a point is the localization of `N` there, so it is finitely presented over
the localization of `R`. A general point of a general scheme is reached from this case by
descending along two flat morphisms — the inclusion of an affine open neighbourhood and the
isomorphism of that open with the spectrum of its functions — which is what
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat` does.

That descent lemma is the geometric form of the algebraic descent in
`StacksFrontier/RingTheory/Flat/FlatStalkFinitePresentation.lean`: along a flat morphism of schemes
the stalk map is a flat local homomorphism of local rings, and Stacks 0098 identifies the stalk
of the pullback with the base change of the stalk, so finite presentation descends.

## Main results

* `Stacks.StalkFiniteType.finitePresentation_stalk_of_flat`: **finite presentation of a stalk
  descends along a flat morphism of schemes.** If `g : X ⟶ Y` is flat and the stalk of `g^*F` at
  `x` is a finitely presented `𝒪_{X,x}`-module, then the stalk of `F` at `g x` is a finitely
  presented `𝒪_{Y,g x}`-module.
* `Stacks.StalkFiniteType.finite_stalk_of_flat`: the same for finite generation.
* `Stacks.StalkFiniteType.finitePresentation_stalk`: **the stalk of a finitely presented sheaf of
  modules on a scheme is finitely presented** over the local ring at the point.
* `Stacks.StalkFiniteType.isFinitePresentation_pullback`: the pullback of a finitely presented
  sheaf of modules along a morphism of schemes is finitely presented, which is Stacks 01BQ read
  at `AlgebraicGeometry.Scheme.Modules.pullback`.

## Implementation notes

The module structure on a stalk is the global instance `Stacks.StalkFreeBridge.instModuleStalk`,
which is `rfl`-equal to the one `Stacks.ModuleSkyscraper.stalkObj` carries; that is what lets the
linear equivalence of Stacks 0098 be read directly against statements phrased with
`TopCat.Presheaf.stalk M.val.presheaf x`. The affine case is instead phrased with the stalk
spelled `(tilde N).presheaf.stalk x` at a point of `PrimeSpectrum.Top R`, because that is the
spelling at which Mathlib's `Module R ((tilde N).presheaf.stalk x)` and the localization instance
for `AlgebraicGeometry.tilde.toStalk` are found by instance resolution; the two spellings are
definitionally equal and the bridge is left to unification.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.ModuleSkyscraper

universe u

namespace Stacks.StalkFiniteType

/-- **Stacks 01BQ for Mathlib's pullback of sheaves of modules on schemes.** The pullback of a
finitely presented sheaf of modules along a morphism of schemes is finitely presented.

`Stacks.SheafOfModules.modulePullback_isFinitePresentation` states this for the pullback functor
of the ringed-space module adjunction; `AlgebraicGeometry.Scheme.Modules.pullback` is that
functor at the underlying morphism of ringed spaces. -/
theorem isFinitePresentation_pullback {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)
    [F.IsFinitePresentation] : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation.{u} X.toRingedSpace Y.toRingedSpace
    g.toLRSHom.toShHom F ‹F.IsFinitePresentation›

section Descent

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g] (F : Y.Modules) (x : X)

/-- Along a flat morphism of schemes the stalk map at a point is a flat local homomorphism of
local rings, and Stacks 0098 identifies the stalk of the pullback `g^*F` at `x` with the base
change of the stalk of `F` at `g x`. This packages what the descent statements below need. -/
private theorem flat_isLocalHom_nonempty_equiv_stalkMap :
    letI : Algebra (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x)) :=
      (g.stalkMap x).hom.toAlgebra
    Module.Flat (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x)) ∧
    IsLocalHom (algebraMap (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x))) ∧
    Nonempty (TensorProduct (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf (g x)))
      ≃ₗ[ToType (X.presheaf.stalk x)]
        ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj F).val.presheaf x)) :=
  let _ : Algebra (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x)) :=
    (g.stalkMap x).hom.toAlgebra
  ⟨RingHom.flat_algebraMap_iff.mp (Flat.stalkMap g x), g.toLRSHom.prop x,
    ⟨pullbackStalkLinearEquiv g x F⟩⟩

/-- **Finite presentation of a stalk descends along a flat morphism of schemes.** If `g : X ⟶ Y`
is flat and the stalk of the pullback `g^*F` at `x` is a finitely presented module over
`𝒪_{X,x}`, then the stalk of `F` at `g x` is a finitely presented module over `𝒪_{Y,g x}`.

The stalk map `𝒪_{Y,g x} → 𝒪_{X,x}` is flat (`AlgebraicGeometry.Flat.stalkMap`) and local, and
Stacks 0098 (`Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv`) identifies the stalk of `g^*F`
at `x` with `𝒪_{X,x} ⊗_{𝒪_{Y,g x}} F_{g x}`, so this is
`Module.FinitePresentation.of_tensorProduct_of_flat_of_isLocalHom`, i.e. Stacks 03C4 (2) together
with Stacks 00HR. -/
theorem finitePresentation_stalk_of_flat
    (h : Module.FinitePresentation (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj F).val.presheaf x))) :
    Module.FinitePresentation (ToType (Y.presheaf.stalk (g x)))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf (g x))) := by
  let _ : Algebra (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x)) :=
    (g.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, ⟨e⟩⟩ := flat_isLocalHom_nonempty_equiv_stalkMap g F x
  have := Module.FinitePresentation.of_equiv e.symm
  exact Module.FinitePresentation.of_tensorProduct_of_flat_of_isLocalHom
    (T := ToType (X.presheaf.stalk x))

/-- **Finite generation of a stalk descends along a flat morphism of schemes**, the companion of
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat` for `Module.Finite`. This is Stacks
03C4 (1) together with Stacks 00HR. -/
theorem finite_stalk_of_flat
    (h : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj F).val.presheaf x))) :
    Module.Finite (ToType (Y.presheaf.stalk (g x)))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf (g x))) := by
  let _ : Algebra (ToType (Y.presheaf.stalk (g x))) (ToType (X.presheaf.stalk x)) :=
    (g.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, ⟨e⟩⟩ := flat_isLocalHom_nonempty_equiv_stalkMap g F x
  have := Module.Finite.equiv e.symm
  exact Module.Finite.of_tensorProduct_of_flat_of_isLocalHom
    (T := ToType (X.presheaf.stalk x))

end Descent

/-- The stalk of `N^~` at a point of `Spec R` is a finitely presented module over the local ring
there, when `N` is a finitely presented `R`-module: the stalk is the localization of `N` at the
point, and finite presentation is preserved by base change. -/
private theorem finitePresentation_stalk_tilde {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    [Module.FinitePresentation R N] (x : PrimeSpectrum.Top R) :
    letI : Module (ToType ((Spec R).presheaf.stalk x)) (ToType ((tilde N).presheaf.stalk x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec R).presheaf) (tilde N).val x
    Module.FinitePresentation (ToType ((Spec R).presheaf.stalk x))
      (ToType ((tilde N).presheaf.stalk x)) := by
  let _ : Module (ToType ((Spec R).presheaf.stalk x)) (ToType ((tilde N).presheaf.stalk x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec R).presheaf) (tilde N).val x
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra R (ToType ((Spec R).presheaf.stalk x)) := StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime (ToType ((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have : IsScalarTower R (ToType ((Spec R).presheaf.stalk x))
      (ToType ((tilde N).presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact FinitePresentation.of_isBaseChange (tilde.toStalk N x).hom
    ((isLocalizedModule_iff_isBaseChange x.asIdeal.primeCompl _ _).mp inferInstance)

/-- The affine case of `Stacks.StalkFiniteType.finitePresentation_stalk`: on the spectrum of a
ring a finitely presented sheaf of modules has finitely presented stalks.

A finitely presented sheaf of modules is quasi-coherent, so Mathlib's
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` writes it as `N^~` for `N = Γ(M, ⊤)`; Stacks
01PC makes `N` a finitely presented `R`-module, and
`Stacks.StalkFiniteType.finitePresentation_stalk_tilde` computes the stalk. -/
private theorem finitePresentation_stalk_spec {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [hM : M.IsFinitePresentation] (z : Spec R) :
    Module.FinitePresentation (ToType ((Spec R).presheaf.stalk z))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf z)) := by
  have : M.IsQuasicoherent := by
    obtain ⟨q, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
    exact q.isQuasicoherent
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let N : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  have : Module.FinitePresentation R N := (tilde_isFinitePresentation_iff N).mp
    ((SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      (asIso M.fromTildeΓ).symm hM)
  have h : Module.FinitePresentation (ToType ((Spec R).presheaf.stalk z))
      (ToType (TopCat.Presheaf.stalk (tilde N).val.presheaf z)) :=
    finitePresentation_stalk_tilde N z
  have e : ToType (TopCat.Presheaf.stalk (tilde N).val.presheaf z)
      ≃ₗ[ToType ((Spec R).presheaf.stalk z)]
        ToType (TopCat.Presheaf.stalk M.val.presheaf z) :=
    ((modulesStalkFunctor (Spec R) z).mapIso (asIso M.fromTildeΓ)).toLinearEquiv
  exact Module.FinitePresentation.of_equiv e

/-- **The stalk of a finitely presented sheaf of modules on a scheme is a finitely presented
module** over the local ring at that point.

This is the statement that `StalkFiniteType/FlatFinitePresentation.lean` and
`StalkFreeBridge/StalkFree.lean` record as missing from this repository. The proof
restricts to an affine open neighbourhood of the point, identifies it with the spectrum of its
ring of functions, applies `Stacks.StalkFiniteType.finitePresentation_stalk_spec` there, and
descends back along those two flat morphisms with
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat`. -/
theorem finitePresentation_stalk {X : Scheme.{u}} (M : X.Modules) [M.IsFinitePresentation]
    (x : X) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  let x' : U.toScheme := ⟨x, X.affineCover.covers x⟩
  let e : U.toScheme ≅ Spec Γ(X, U) := hU.isoSpec
  let M' : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj M
  have : M'.IsFinitePresentation := isFinitePresentation_pullback U.ι M
  let M'' : (Spec Γ(X, U)).Modules := (Scheme.Modules.pullback e.inv).obj M'
  have : M''.IsFinitePresentation := isFinitePresentation_pullback e.inv M'
  have hmid : Module.FinitePresentation (ToType (U.toScheme.presheaf.stalk (e.inv (e.hom x'))))
      (ToType (TopCat.Presheaf.stalk M'.val.presheaf (e.inv (e.hom x')))) :=
    finitePresentation_stalk_of_flat e.inv M' (e.hom x')
      (finitePresentation_stalk_spec M'' (e.hom x'))
  have hx' : Module.FinitePresentation (ToType (U.toScheme.presheaf.stalk x'))
      (ToType (TopCat.Presheaf.stalk M'.val.presheaf x')) :=
    Eq.mp (congrArg (fun p : U.toScheme => Module.FinitePresentation
      (ToType (U.toScheme.presheaf.stalk p))
      (ToType (TopCat.Presheaf.stalk M'.val.presheaf p))) (Scheme.hom_inv_apply e x')) hmid
  exact finitePresentation_stalk_of_flat U.ι M x' hx'

end Stacks.StalkFiniteType

end
