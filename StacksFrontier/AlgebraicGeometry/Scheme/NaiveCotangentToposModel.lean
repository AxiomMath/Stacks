module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentUniverseLift
public import StacksFrontier.Cotangent.SchemeCotangentComplex

/-!
# `NL_{X/Y}` of a morphism of schemes, from the morphism of Zariski ringed topoi

Let `f : X ⟶ Y` be a morphism of schemes.  The naive cotangent complex `NL_{X/Y}` of Stacks 0D0H
(`AlgebraicGeometry.Scheme.naiveCotangentComplex`) is `NL_{𝒪_X/f^{-1}𝒪_Y}` for the inverse image
`f^{-1}𝒪_Y` of sheaves of commutative rings on topological spaces.  The same morphism, read as a
morphism of Zariski ringed topoi (`AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom`), has its
own inverse image `f^{-1}𝒪_Y` — the topos inverse image of sheaves of commutative rings — and its
own structure map in inverse-image form.  This file identifies the two.

Both inverse images are left adjoint to restriction along the inverse image of opens, which the
topos presents as `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor` and the theory of
sheaves on spaces as `TopCat.Sheaf.pushforward`; the two right adjoints agree by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, so the left adjoints agree, and the two
structure maps, being the adjuncts of the one map `f^♯`, correspond.  The two naive cotangent
complexes are then isomorphic by `Stacks.SheafOfModules.isIso_naiveCotangentComplexMapOfSquare`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.zariskiPushforwardCommRingIso`: the two right adjoints agree.
* `AlgebraicGeometry.Scheme.Hom.inverseImageSheafIso`: the two inverse images of `𝒪_Y` agree.
* `AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplex`: `NL_{𝒪_X/f^{-1}𝒪_Y}` for the topos
  model, at a free module universe.
* `AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplexIso`: it is `NL_{X/Y}`, at any module
  universe; at module sections in `Type (u + 1)`, composing with
  `Stacks.SheafOfModules.naiveCotangentComplexULiftIso` relates it to the universe lift of
  `NL_{X/Y}`.
* `AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplexULiftIso`: the topos model with module
  sections in `Type (u + 1)` is the universe lift of `NL_{X/Y}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageSheafIso_hom_fSharpInverseImage`: the identification
  carries one structure map to the other.

## References

* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H)
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

universe z u

namespace Stacks.SheafOfModules

variable {C : Type*} [Category C] (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **Change of base ring along an isomorphism**: for `e : A ≅ A'` and `a = e.hom ≫ a'`, the
change of base ring `NL_{B/A} ⟶ NL_{B/A'}` of Stacks 08TX is an isomorphism of complexes of
sheaves of `B`-modules. -/
noncomputable def naiveCotangentComplexIsoOfBase (A A' B : Sheaf J CommRingCat.{u}) (a : A ⟶ B)
    (a' : A' ⟶ B) (e : A ≅ A') (hf : a = e.hom ≫ a') :
    naiveCotangentComplex.{_, _, u, z} J A B a ≅ naiveCotangentComplex.{_, _, u, z} J A' B a' :=
  @asIso _ _ _ _ (naiveCotangentComplexMapOfBase.{_, _, u, z} J A B a A' a' e.hom hf)
    (isIso_naiveCotangentComplexMapOfSquare.{_, _, u, z} J A B a A' B a' e (Iso.refl B)
      (comp_id_eq_comp_of_fac J A B a A' a' e.hom hf))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The topos pushforward of sheaves of commutative rings along `f` is restriction along the
inverse image of opens**, componentwise `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`. -/
def zariskiPushforwardCommRingIso :
    pushforwardCommRingFunctor.{u, u, u, u, u, u} f.zariskiRingedToposHom.toToposHom ≅
      TopCat.Sheaf.pushforward CommRingCat.{u} f.base :=
  NatIso.ofComponents
    (fun O ↦ restrictionCommRingIso (Opens.grothendieckTopology ↥Y)
      (Opens.grothendieckTopology ↥X) (Opens.map f.base) O)
    (fun a ↦ restrictionCommRingIso_naturality (Opens.grothendieckTopology ↥Y)
      (Opens.grothendieckTopology ↥X) (Opens.map f.base) a)

/-- The inverse image of sheaves of commutative rings on spaces is left adjoint to the topos
pushforward along `f`. -/
def inverseImageSheafAdjunction :
    TopCat.Sheaf.pullback CommRingCat.{u} f.base ⊣
      pushforwardCommRingFunctor.{u, u, u, u, u, u} f.zariskiRingedToposHom.toToposHom :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).ofNatIsoRight
    (zariskiPushforwardCommRingIso f).symm

/-- **The two inverse images of `𝒪_Y` agree**: the topos inverse image of sheaves of commutative
rings along `f` and the inverse image of sheaves on spaces, both left adjoint to restriction
along the inverse image of opens. -/
def inverseImageSheafIso :
    (inverseImageCommRingFunctor.{u, u, u, u, u, u} f.zariskiRingedToposHom.toToposHom).obj
        Y.zariskiRingedTopos.O ≅
      inverseImageSheaf f.toLRSHom.toShHom :=
  ((commRingImageAdjunction f.zariskiRingedToposHom.toToposHom).leftAdjointUniq
    (inverseImageSheafAdjunction f)).app Y.sheaf

/-- **The identification of the two inverse images carries the structure map of the morphism of
Zariski ringed topoi to the structure map `f^{-1}𝒪_Y ⟶ 𝒪_X` of the morphism of ringed spaces.**
Both are adjuncts of `f^♯`. -/
theorem inverseImageSheafIso_hom_fSharpInverseImage :
    (inverseImageSheafIso f).hom ≫ inverseImageStructureMap f.toLRSHom.toShHom =
      f.zariskiRingedToposHom.fSharpInverseImage := by
  have h := Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm
    (commRingImageAdjunction f.zariskiRingedToposHom.toToposHom) (inverseImageSheafAdjunction f)
    f.zariskiRingedToposHom.fSharp
  have h2 : (inverseImageSheafAdjunction f).homEquiv _ _
      (inverseImageStructureMap f.toLRSHom.toShHom) = f.zariskiRingedToposHom.fSharp := by
    refine (Adjunction.homEquiv_ofNatIsoRight_apply
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base)
      (zariskiPushforwardCommRingIso f).symm
      (inverseImageStructureMap f.toLRSHom.toShHom)).trans ?_
    refine (congrArg (fun t ↦ t ≫ (zariskiPushforwardCommRingIso f).symm.hom.app X.sheaf)
      (Stacks.Sheaves.RingedSpaceDifferentials.homEquiv_inverseImageStructureMap
        f.toLRSHom.toShHom)).trans ?_
    rfl
  have h3 : ((inverseImageSheafAdjunction f).homEquiv _ _).symm f.zariskiRingedToposHom.fSharp =
      inverseImageStructureMap f.toLRSHom.toShHom := by
    rw [← h2]
    exact Equiv.symm_apply_apply _ _
  rw [← h3]
  exact h

/-- **`NL_{𝒪_X/f^{-1}𝒪_Y}` for the morphism of Zariski ringed topoi of `f`**, with module sections
in `Type z` joined with `Type u`: the naive cotangent complex of the structure map of
`AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom f` in inverse-image form. -/
def toposNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{max u z} (Stacks.SheafOfModules.Tensor.ringSheaf
      X.zariskiRingedTopos.O)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, z} X.zariskiRingedTopos.J
    ((inverseImageCommRingFunctor.{u, u, u, u, u, u} f.zariskiRingedToposHom.toToposHom).obj
      Y.zariskiRingedTopos.O)
    X.zariskiRingedTopos.O f.zariskiRingedToposHom.fSharpInverseImage

/-- **The topos model of `NL_{X/Y}` is `NL_{X/Y}`**, at any module universe: the chain map of
Stacks 08TX attached to the identification
`AlgebraicGeometry.Scheme.Hom.inverseImageSheafIso` of the two inverse images of `𝒪_Y` and the
identity of `𝒪_X`, which is an isomorphism. -/
def toposNaiveCotangentComplexIso :
    toposNaiveCotangentComplex.{z} f ≅
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, z}
        X.zariskiRingedTopos.J (inverseImageSheaf f.toLRSHom.toShHom) X.zariskiRingedTopos.O
        (inverseImageStructureMap f.toLRSHom.toShHom) :=
  Stacks.SheafOfModules.naiveCotangentComplexIsoOfBase.{z, u} X.zariskiRingedTopos.J _ _
    X.zariskiRingedTopos.O f.zariskiRingedToposHom.fSharpInverseImage
    (inverseImageStructureMap f.toLRSHom.toShHom) (inverseImageSheafIso f)
    (inverseImageSheafIso_hom_fSharpInverseImage f).symm

/-- `NL_{X/Y}` of Stacks 0D0H (`AlgebraicGeometry.Scheme.naiveCotangentComplex`), written on
the Zariski ringed topos of `X`. -/
theorem naiveCotangentComplex_eq_zariski :
    Scheme.naiveCotangentComplex f =
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        X.zariskiRingedTopos.J (inverseImageSheaf f.toLRSHom.toShHom) X.zariskiRingedTopos.O
        (inverseImageStructureMap f.toLRSHom.toShHom) :=
  rfl

/-- `Stacks.SheafOfModules.naiveCotangentComplexULiftIso` for `NL_{X/Y}`, from module sections in
`Type u` to module sections in `Type (u + 1)`.  It is stated without a type ascription: elaborating
the general isomorphism against the spelled-out type exhausts the elaborator's budget, while
checking the two types defeq afterwards does not. -/
def zariskiNaiveCotangentComplexULiftIso :=
  Stacks.SheafOfModules.naiveCotangentComplexULiftIso.{u, u, u, u, u + 1}
    X.zariskiRingedTopos.J (inverseImageSheaf f.toLRSHom.toShHom) X.zariskiRingedTopos.O
    (inverseImageStructureMap f.toLRSHom.toShHom)

/-- **The topos model of `NL_{X/Y}` with module sections in `Type (u + 1)` is the universe lift
of `NL_{X/Y}`**: `AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplexIso` at `Type (u + 1)`
followed by `AlgebraicGeometry.Scheme.Hom.zariskiNaiveCotangentComplexULiftIso`, which identifies
the naive cotangent complex with module sections in `Type (u + 1)` with the universe lift of the
one with module sections in `Type u`. -/
def toposNaiveCotangentComplexULiftIso :
    toposNaiveCotangentComplex.{u + 1} f ≅
      ((_root_.SheafOfModules.uliftFunctor.{u, u, u, u, u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Scheme.naiveCotangentComplex f) :=
  toposNaiveCotangentComplexIso.{u + 1} f ≪≫ zariskiNaiveCotangentComplexULiftIso f

end AlgebraicGeometry.Scheme.Hom

end
