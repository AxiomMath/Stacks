module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Cohomology along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module.
[Stacks, Tag 089W] asserts

`H^i(X, F) = H^i(S, f_* F)` for every `i ≥ 0`,

and the two sides are compared here as modules, over `Γ(S, ⊤)` after restriction of scalars
along `f^♯ : Γ(S, ⊤) ⟶ Γ(X, ⊤)`, exactly as [Stacks, Tag 01XK] is stated in
`StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBase.lean`.

## Main definitions

* `rightDerivedFunctorPlusObjSingleIso`: for an `F`-acyclic object `X`, the right derived
  functor of `F` on the bounded below derived category takes `X[0]` to `F(X)[0]`.
* `rightDerivedPlusCollapseIso` and `rightDerivedCollapseIso`: **the collapse of the derived
  functor of a composite at an acyclic object**, `R^n (G ∘ F)(X) ≅ R^n G (F X)` for `X` right
  acyclic for `F`, under the hypothesis that `F` carries injective objects to `G`-acyclic
  objects.
* `restrictScalarsRightDerivedIso`: restriction of scalars pulled inside the right derived
  functor, turning `H^n(X, −)` with scalars restricted into `R^n(Γ(S, ⊤) ∘ f_*)`.
* `cohomologyIsoPushforward`: **[Stacks, Tag 089W]**.

## Main results

* `rightAcyclic_pushforward_of_isAffineHom`: a quasi-coherent module is right acyclic for the
  direct image along an affine morphism. This is [Stacks, Tag 01XC] read as acyclicity.
* `rightAcyclic_moduleGlobalSections_pushforward_obj`: the direct image of an injective module
  has acyclic global sections, which is [Stacks, Tag 01EX] part (2) at the scheme-level
  spelling.

## Implementation notes

The acyclicity input is **not** `Functor.PreservesInjectiveObjects` for the direct image, and
cannot be. Direct image on modules is right adjoint to pullback, and with enough injectives
upstairs `CategoryTheory.Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`
turns preservation of injectives by `f_*` into preservation of monomorphisms by `f^*`, that is
into flatness of `f`; an affine morphism is not flat. What the source's proof of
[Stacks, Tag 01EZ] uses instead is that `f_*` carries injective modules to objects with
*acyclic sections*, which holds for every morphism of ringed spaces and is
[Stacks, Tag 01EX] part (2). So the composite collapses through
`Stacks.Cohomology.DerivedPushforwardSections.compIso`, the formalization of
[Stacks, Tag 015M], rather than through an injective resolution downstairs.

`rightDerivedPlusCollapseIso` is the complement of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`: that one collapses the *outer* functor,
`R^n(G ∘ F) ≅ G ∘ R^n F`, when `G` preserves the relevant homology, and is what
[Stacks, Tag 01XK] needs; this one collapses the *inner* functor at an `F`-acyclic object, and
is what [Stacks, Tag 089W] needs. Neither implies the other.

Both halves of the comparison are stated with Mathlib's `ℕ`-indexed `Functor.rightDerived`,
the two indexings being compared by `Stacks.DerivedIndexing.rightDerivedIso`, so that the
statement is in the shape its consumers use.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.AffineComparison

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The collapse of a composite at an acyclic object -/

section Collapse

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- **The right derived functor of `F` at an `F`-acyclic object.** Right acyclicity of `X` says
precisely that the unit of `RF` is invertible at `X[0]`, and the source of that unit is
`F(X)[0]`. -/
public def rightDerivedFunctorPlusObjSingleIso (X : A) (hX : F.rightAcyclic X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X) :=
  haveI : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := by
    have hX' : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
    have hd := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith).1 inferInstance
    rw [← Functor.rightDerived_fac_app _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith]
    infer_instance
  F.rightDerivedFunctorPlus.mapIso ((Functor.singleFunctorPlusIsoCompQh 0).app X) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X))).symm ≪≫
    F.mapSingleFunctorCompQhIso.app X

/-- **The collapse of the right derived functor of a composite at an acyclic object**, in the
`ℤ`-indexed form. If `F` carries injective objects to `G`-acyclic objects — the hypothesis of
[Stacks, Tag 015M] — and if `X` is right acyclic for `F`, then
`R^n (G ∘ F)(X) ≅ R^n G (F X)`. -/
public def rightDerivedPlusCollapseIso
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (X : A) (hX : F.rightAcyclic X) (n : ℤ) :
    ((F ⋙ G).rightDerivedPlus n).obj X ≅ (G.rightDerivedPlus n).obj (F.obj X) :=
  (DerivedCategory.Plus.homologyFunctor C n).mapIso
    ((Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≪≫
      G.rightDerivedFunctorPlus.mapIso (rightDerivedFunctorPlusObjSingleIso F X hX))

/-- **The collapse of the right derived functor of a composite at an acyclic object**, for
Mathlib's `ℕ`-indexed right derived functors. -/
public def rightDerivedCollapseIso
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (X : A) (hX : F.rightAcyclic X) (n : ℕ) :
    ((F ⋙ G).rightDerived n).obj X ≅ (G.rightDerived n).obj (F.obj X) :=
  (Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n).app X ≪≫
    rightDerivedPlusCollapseIso F G hFG X hX n ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso G n).app (F.obj X)).symm

end Collapse

/-! ### The two acyclicity inputs for an affine morphism of schemes -/

section Acyclicity

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 01XC] read as acyclicity.** A quasi-coherent module is right acyclic for the
direct image along an affine morphism: the higher direct images vanish, and the direct image
preserves finite limits, being a right adjoint. -/
public theorem rightAcyclic_pushforward_of_isAffineHom
    [AlgebraicGeometry.IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.pushforward f).rightAcyclic F := by
  refine (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
    (AlgebraicGeometry.Scheme.Modules.pushforward f) F).2 fun n hn => ?_
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n F).2
    (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f F (n : ℤ)
      (by exact_mod_cast hn))

/-- **[Stacks, Tag 01EX] part (2) at the scheme-level spelling.** The direct image of an
injective module has right acyclic global sections. No hypothesis on `f` is used. -/
public theorem rightAcyclic_moduleGlobalSections_pushforward_obj
    (I : X.Modules) (hI : Injective I) :
    (moduleGlobalSections S).rightAcyclic
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj I) :=
  @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
    (asRingedSpaceHom f) I hI ⊤

end Acyclicity

/-! ### The comparison -/

section Comparison

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- **Restriction of scalars pulled inside the right derived functor.** Cohomology upstairs,
read as a module over `Γ(S, ⊤)`, is the `n`-th right derived functor of the composite of the
direct image with global sections downstairs. Restriction of scalars is exact, and the square
of underived functors commutes by [Stacks, Tag 01EZ] over the whole space. -/
public def restrictScalarsRightDerivedIso (F : X.Modules) (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F) ≅
      ((AlgebraicGeometry.Scheme.Modules.pushforward f ⋙
        moduleGlobalSections S).rightDerived n).obj F :=
  let R := ModuleCat.restrictScalars.{u} f.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X) R
    (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
    (sectionsRestrictionIsoTop f) n).app F

/-- **[Stacks, Tag 089W].** For an affine morphism of schemes `f : X ⟶ S` and a quasi-coherent
`𝒪_X`-module `F`, the cohomology of `F` on `X` is the cohomology of its direct image on `S`, in
every degree `i ≥ 0`, as modules over `Γ(S, ⊤)` after restriction of scalars along `f^♯`.

The higher direct images vanish ([Stacks, Tag 01XC]), so `F` is acyclic for `f_*`, and the
direct image of an injective module has acyclic sections ([Stacks, Tag 01EX] part (2)), so the
right derived functor of `Γ(S, ⊤) ∘ f_*` collapses onto `H^i(S, f_* −)`; the other factor is
`Γ(X, ⊤)` with its scalars restricted, by [Stacks, Tag 01EZ]. -/
@[stacks 089W]
public def cohomologyIsoPushforward [AlgebraicGeometry.IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F) ≅
      ((moduleGlobalSections S).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F) :=
  restrictScalarsRightDerivedIso f F n ≪≫
    rightDerivedCollapseIso (AlgebraicGeometry.Scheme.Modules.pushforward f)
      (moduleGlobalSections S)
      (rightAcyclic_moduleGlobalSections_pushforward_obj f) F
      (rightAcyclic_pushforward_of_isAffineHom f F) n

end Comparison

end Stacks.Cohomology.AffineComparison

end
