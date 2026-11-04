module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineLeray
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# The affine cohomology comparison is natural in the module

[Stacks, Tag 089W] — `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` — compares
`H^n(X, F)`, read through restriction of scalars along `f^♯`, with `H^n(S, f_* F)` for an affine
morphism `f : X ⟶ S` and a quasi-coherent `F`. The multiplication identity of conclusion (c) of
[Stacks, Tag 0EX3] needs to cross that comparison with an endomorphism of the coefficient
module, and this file supplies the square.

Nothing geometric is involved: the comparison is a composite of six factors, every one of which
is a component of a natural transformation of functors — or the inverse of one — so each square
is `CategoryTheory.NatTrans.naturality`, and the squares are pasted with
`…TopDegreeBaseChange.comp_two_squares` and `…TopDegreeBaseChange.map_comp_square`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `rightDerivedFunctorPlusObjSingleIso_naturality`: an endomorphism crosses the collapse of
  `RF` at an `F`-acyclic object placed in degree zero.
* `rightDerivedPlusCollapseIso_naturality` and `rightDerivedCollapseIso_naturality`: an
  endomorphism crosses the collapse `R^n(G ∘ F)(X) ≅ R^n G(F X)` of the derived functor of a
  composite at an `F`-acyclic object, in the `ℤ`-indexed and the `ℕ`-indexed form.
* `restrictScalarsRightDerivedIso_naturality`: an endomorphism crosses the pulling of
  restriction of scalars inside the right derived functor.
* `cohomologyIsoPushforward_naturality`: **[Stacks, Tag 089W] is natural in the module.**
* `cohomologyPullbackIsoPushforward_naturality`: **the Leray comparison along an affine
  morphism, at a pullback, is natural in the module.**

## Implementation notes

*Why the proofs are terms and not rewrites.* The objects involved are values of right derived
functors at module sheaves, and a goal mentioning them is large enough that `rw` and
`simp only` fail to locate even `CategoryTheory.Category.assoc`; this is the reason
`HmulProjectionPaste.lean` exists. Accordingly every proof here is a term built out of
`comp_two_squares`, `map_comp_square` and `inv_square`, and the identifications
`(α ≪≫ β).hom = α.hom ≫ β.hom`, `(F.mapIso α).hom = F.map α.hom`,
`(α.app X).symm.hom = α.inv.app X` and
`(F.rightDerivedPlus n).map u = (homologyFunctor n).map (RF.map (X ↦ X[0]).map u)` are left to
the kernel, each holding by `rfl`.

*The one square that is not literal naturality.* The middle factor of
`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso` is the *inverse* of a
component of `CategoryTheory.Functor.rightDerivedFunctorPlusUnit`, which is invertible only at
the acyclic object and therefore is not a natural isomorphism. `inv_square` turns the naturality
square of the unit into the square across its inverse, which is all that is needed.

*Only endomorphisms.* Every statement below transports an endomorphism `u : M ⟶ M`, which is
what the multiplication identity needs; the two-object version would read the same way with
`map_comp_square` and `comp_two_squares` restated for a pair of objects.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.AffineComparison

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A square across an isomorphism crosses its inverse.** If `n` transports `m` across
`e.hom`, then `m` transports `n` across `e.inv`.

This is the only step of the comparison below that is not literal naturality: the unit of a
right derived functor is invertible at an acyclic object without being a natural isomorphism,
so the square across its inverse has to be deduced from the square across the unit. -/
theorem inv_square {D : Type*} [Category D] {P Q : D} {m : P ⟶ P} (e : P ≅ Q) {n : Q ⟶ Q}
    (hsq : m ≫ e.hom = e.hom ≫ n) : n ≫ e.inv = e.inv ≫ m := by
  rw [Iso.comp_inv_eq, Category.assoc, hsq, Iso.inv_hom_id_assoc]

/-! ### The collapse of a composite at an acyclic object is natural in the object -/

section Collapse

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

omit [EnoughInjectives B] in
/-- **An endomorphism crosses the collapse of `RF` at an acyclic object.** For `X` right acyclic
for `F` and `u : X ⟶ X`, the isomorphism
`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso` carries
`RF(u[0])` to `(F u)[0]`.

All three factors of that isomorphism are components of natural transformations: the
factorization of the single functor through the bounded below homotopy category, the unit of
`RF` — inverted, hence `inv_square` — and the commutation of `F` with placing an object in
degree zero. -/
theorem rightDerivedFunctorPlusObjSingleIso_naturality (X : A) (hX : F.rightAcyclic X)
    (u : X ⟶ X) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map u) ≫
        (rightDerivedFunctorPlusObjSingleIso F X hX).hom =
      (rightDerivedFunctorPlusObjSingleIso F X hX).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (F.map u) :=
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
  comp_two_squares
    (map_comp_square F.rightDerivedFunctorPlus
      ((Functor.singleFunctorPlusIsoCompQh 0).hom.naturality u))
    (comp_two_squares
      (inv_square
        (asIso (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))
        (F.rightDerivedFunctorPlusUnit.naturality
          ((HomotopyCategory.Plus.singleFunctor A 0).map u)))
      (F.mapSingleFunctorCompQhIso.hom.naturality u))

/-- **An endomorphism crosses the `ℤ`-indexed collapse of the derived functor of a composite.**
For `X` right acyclic for `F` and `u : X ⟶ X`,
`Stacks.Cohomology.AffineComparison.rightDerivedPlusCollapseIso` carries
`R^n(G ∘ F)(u)` to `R^n G(F u)`.

The isomorphism is the degree-`n` homology of a composite of two factors: the canonical
comparison `R(G ∘ F) ≅ RG ∘ RF` of [Stacks, Tag 015M], which is a natural isomorphism, and `RG`
applied to `rightDerivedFunctorPlusObjSingleIso`. Reading
`CategoryTheory.Functor.rightDerivedPlus` as the homology of `RF` at an object placed in degree
zero needs no unfolding lemma: it is its definition. -/
theorem rightDerivedPlusCollapseIso_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (X : A) (hX : F.rightAcyclic X) (n : ℤ) (u : X ⟶ X) :
    ((F ⋙ G).rightDerivedPlus n).map u ≫
        (rightDerivedPlusCollapseIso F G hFG X hX n).hom =
      (rightDerivedPlusCollapseIso F G hFG X hX n).hom ≫
        (G.rightDerivedPlus n).map (F.map u) :=
  map_comp_square (DerivedCategory.Plus.homologyFunctor C n)
    (comp_two_squares
      ((Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG).hom.naturality
        ((DerivedCategory.Plus.singleFunctor A 0).map u))
      (map_comp_square G.rightDerivedFunctorPlus
        (rightDerivedFunctorPlusObjSingleIso_naturality F X hX u)))

/-- **An endomorphism crosses the `ℕ`-indexed collapse of the derived functor of a composite.**
For `X` right acyclic for `F` and `u : X ⟶ X`,
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso` carries `R^n(G ∘ F)(u)` to
`R^n G(F u)`.

The two changes of indexing are crossed by the naturality of
`Stacks.DerivedIndexing.rightDerivedIso` — on its `hom` for the first factor and on its `inv`
for the last, the last factor of the definition being an inverted component — and the middle
factor is `rightDerivedPlusCollapseIso_naturality`. -/
theorem rightDerivedCollapseIso_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (X : A) (hX : F.rightAcyclic X) (n : ℕ) (u : X ⟶ X) :
    ((F ⋙ G).rightDerived n).map u ≫ (rightDerivedCollapseIso F G hFG X hX n).hom =
      (rightDerivedCollapseIso F G hFG X hX n).hom ≫
        (G.rightDerived n).map (F.map u) :=
  comp_two_squares
    ((Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n).hom.naturality u)
    (comp_two_squares
      (rightDerivedPlusCollapseIso_naturality F G hFG X hX n u)
      ((Stacks.DerivedIndexing.rightDerivedIso G n).inv.naturality (F.map u)))

end Collapse

/-! ### [Stacks, Tag 089W] is natural in the module -/

section Comparison

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **An endomorphism crosses the pulling of restriction of scalars inside the right derived
functor.** For `u : F ⟶ F`,
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` carries `H^n(X, u)` with its
scalars restricted to `R^n(Γ(S, ⊤) ∘ f_*)(u)`.

That isomorphism is a component of the natural isomorphism
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, so the square is its naturality; the
exactness inputs for restriction of scalars are the ones the definition itself uses. -/
theorem restrictScalarsRightDerivedIso_naturality (F : X.Modules) (n : ℕ) (u : F ⟶ F) :
    (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerived n).map u) ≫
        (restrictScalarsRightDerivedIso f F n).hom =
      (restrictScalarsRightDerivedIso f F n).hom ≫
        ((Scheme.Modules.pushforward f ⋙ moduleGlobalSections S).rightDerived n).map u := by
  let R := ModuleCat.restrictScalars.{u} f.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  exact (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X) R
    (Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
    (sectionsRestrictionIsoTop f) n).hom.naturality u

/-- **[Stacks, Tag 089W] is natural in the module.** For an affine morphism `f : X ⟶ S`, a
quasi-coherent `F` and an endomorphism `u : F ⟶ F`, the comparison
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` carries `H^n(X, u)`, read through
restriction of scalars along `f^♯`, to `H^n(S, f_* u)`.

The comparison is `restrictScalarsRightDerivedIso` followed by `rightDerivedCollapseIso` at the
two acyclicity inputs of [Stacks, Tag 089W], and the two squares just proved are pasted. -/
theorem cohomologyIsoPushforward_naturality [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (u : F ⟶ F) :
    (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerived n).map u) ≫
        (cohomologyIsoPushforward f F n).hom =
      (cohomologyIsoPushforward f F n).hom ≫
        ((moduleGlobalSections S).rightDerived n).map ((Scheme.Modules.pushforward f).map u) :=
  comp_two_squares
    (restrictScalarsRightDerivedIso_naturality f F n u)
    (rightDerivedCollapseIso_naturality (Scheme.Modules.pushforward f) (moduleGlobalSections S)
      (rightAcyclic_moduleGlobalSections_pushforward_obj f) F
      (rightAcyclic_pushforward_of_isAffineHom f F) n u)

end Comparison

/-- **The Leray comparison along an affine morphism, at a pullback, is natural in the module.**
For `h' : X'' ⟶ X'` affine, `F'` a quasi-coherent `𝒪_{X'}`-module and `u` an endomorphism of
`(h')^* F'`, the comparison
`…TopDegreeBaseChange.cohomologyPullbackIsoPushforward` carries `H^n(X'', u)`, read through
restriction of scalars along `(h')^♯`, to `H^n(X', h'_* u)`.

This is `cohomologyIsoPushforward_naturality` at `(h')^* F'`, whose quasi-coherence is
[Stacks, Tag 01BG], exactly as the comparison itself is [Stacks, Tag 089W] there. -/
theorem cohomologyPullbackIsoPushforward_naturality
    {X' X'' : Scheme.{u}} (h' : X'' ⟶ X') [IsAffineHom h'] (F' : X'.Modules)
    (hF' : F'.IsQuasicoherent) (n : ℕ)
    (u : (Scheme.Modules.pullback h').obj F' ⟶ (Scheme.Modules.pullback h').obj F') :
    (ModuleCat.restrictScalars h'.appTop.hom).map
          (((moduleGlobalSections X'').rightDerived n).map u) ≫
        (cohomologyPullbackIsoPushforward h' F' hF' n).hom =
      (cohomologyPullbackIsoPushforward h' F' hF' n).hom ≫
        ((moduleGlobalSections X').rightDerived n).map ((Scheme.Modules.pushforward h').map u) :=
  have : F'.IsQuasicoherent := hF'
  have : ((Scheme.Modules.pullback h').obj F').IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback h' F'
  cohomologyIsoPushforward_naturality h' ((Scheme.Modules.pullback h').obj F') n u

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
