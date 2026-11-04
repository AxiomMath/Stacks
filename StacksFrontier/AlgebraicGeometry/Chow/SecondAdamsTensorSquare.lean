module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorSquareTensorShortExact
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# The tensor square splits into the two squares in `K₀(Vect(X))`

Let `X` be a scheme and `ℰ` a finite locally free `𝒪_X`-module. The sequence
`0 ⟶ ⋀²ℰ ⟶ ℰ ⊗ ℰ ⟶ Sym²ℰ ⟶ 0` is short exact, so `[ℰ ⊗ ℰ] = [⋀²ℰ] + [Sym²ℰ]` in
`K₀(Vect(X))`. Consequently the filtration relation and the product relation for `⋀²` follow from
the corresponding relations for `Sym²`. Here `Sym²` and `⋀²` are the degree-two pieces of the
chosen package `SheafOfModules.algebras`, and the finite local freeness of the two squares of a
finite locally free module is taken as the hypotheses `hsq` and `halt`.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.tensorPieceTwoIsoTensorSquare`: the degree-two piece of the
  tensor algebra of the chosen package is the tensor square `ℰ ⊗ ℰ`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.shortExact_extSymSheafShortComplex_of_isFiniteLocallyFree`:
  the sequence `0 → ⋀²ℰ → T²ℰ → Sym²ℰ → 0` is short exact for a finite locally free module.
* `AlgebraicGeometry.VectorBundleKZero.classOf_tensorSquare`: `[ℰ ⊗ ℰ] = [⋀²ℰ] + [Sym²ℰ]` in
  `K₀(Vect(X))`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_secondExteriorPower_eq`,
  `AlgebraicGeometry.VectorBundleKZero.classOf_secondSymmetricPower_eq`: `[⋀²ℰ] = [ℰ]² - [Sym²ℰ]`
  and `[Sym²ℰ] = [ℰ]² - [⋀²ℰ]`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_alt_shortExact_of_sym`: the filtration relation
  for `⋀²` follows from the one for `Sym²`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_alt_tensor_of_sym`: the product relation for `⋀²`
  follows from the one for `Sym²`.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.FiniteLocallyFree TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace VectorBundleKZero

variable {X : Scheme.{u}}

/-! ### The degree-two piece of the tensor algebra -/

variable (X) in
/-- The degree-two piece of the tensor algebra of the chosen package of a sheaf of modules on a
scheme is its tensor square. -/
noncomputable def tensorPieceTwoIsoTensorSquare (E : X.Modules) :
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E).tensor.piece (2 : ℤ) ≅
      Scheme.Modules.tensorObjRingedSpace X E E :=
  (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E).tensorPieceIso 2

/-- The sequence `0 → ⋀²ℰ → T²ℰ → Sym²ℰ → 0` is short exact for a finite locally free module
on a scheme. -/
theorem shortExact_extSymSheafShortComplex_of_isFiniteLocallyFree (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    (SheafOfModules.extSymSheafShortComplex
      (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E)).ShortExact :=
  SheafOfModules.shortExact_extSymSheafShortComplex _ fun x =>
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree
      (hM := Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree (hM := hE) E) E x).1

/-- The degree-two piece of the tensor algebra of a finite locally free module is finite locally
free. -/
theorem isFiniteLocallyFree_tensorPieceTwo (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      ((SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E).tensor.piece
        (2 : ℤ)) :=
  @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ (tensorPieceTwoIsoTensorSquare X E).symm
    (@isFiniteLocallyFree_tensorObj X E E hE hE)

/-! ### The tensor square splits -/

/-- The class of the tensor square is the sum of the classes of the two squares:
`[ℰ ⊗ ℰ] = [⋀² ℰ] + [Sym² ℰ]` in `K₀(Vect(X))` for a finite locally free module `ℰ`. -/
theorem classOf_tensorSquare
    (hsq : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E))
    (halt : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E))
    (E : X.Modules) (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOf X (Scheme.Modules.tensorObjRingedSpace X E E) =
      classOf X (secondExteriorPower X E) + classOf X (secondSymmetricPower X E) := by
  have hSE := shortExact_extSymSheafShortComplex_of_isFiniteLocallyFree E hE
  exact (classOf_eq_of_iso (tensorPieceTwoIsoTensorSquare X E)
    (isFiniteLocallyFree_tensorPieceTwo E hE)).symm.trans
    (@classOf_shortExact X _ _ _ _ _ hSE.mono_f hSE.epi_g
      (SheafOfModules.extSymSheafShortComplex _).zero (halt E hE)
      (isFiniteLocallyFree_tensorPieceTwo E hE) (hsq E hE) hSE.exact)

/-- `[⋀² ℰ] = [ℰ]² - [Sym² ℰ]` in `K₀(Vect(X))` for a finite locally free module `ℰ`. -/
theorem classOf_secondExteriorPower_eq
    (hsq : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E))
    (halt : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E))
    (E : X.Modules) (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOf X (secondExteriorPower X E) =
      classOf X E * classOf X E - classOf X (secondSymmetricPower X E) := by
  rw [classOf_mul E E hE hE, classOf_tensorSquare hsq halt E hE]
  abel

/-- `[Sym² ℰ] = [ℰ]² - [⋀² ℰ]` in `K₀(Vect(X))` for a finite locally free module `ℰ`. -/
theorem classOf_secondSymmetricPower_eq
    (hsq : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E))
    (halt : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E))
    (E : X.Modules) (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOf X (secondSymmetricPower X E) =
      classOf X E * classOf X E - classOf X (secondExteriorPower X E) := by
  rw [classOf_secondExteriorPower_eq hsq halt E hE]
  abel

/-! ### The `⋀²` relations from the `Sym²` relations -/

/-- The filtration relation for `⋀²` follows from the one for `Sym²`: along a short exact
sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules, the relation
`[Sym²ℱ] = [Sym²ℰ] + [ℰ ⊗ 𝒢] + [Sym²𝒢]` implies `[⋀²ℱ] = [⋀²ℰ] + [ℰ ⊗ 𝒢] + [⋀²𝒢]`. -/
theorem classOf_alt_shortExact_of_sym
    (hsq : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E))
    (halt : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E))
    {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact)
    (hsym : classOf X (secondSymmetricPower X F) =
      classOf X (secondSymmetricPower X E) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
          classOf X (secondSymmetricPower X G)) :
    classOf X (secondExteriorPower X F) =
      classOf X (secondExteriorPower X E) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
          classOf X (secondExteriorPower X G) := by
  have := hmono
  have := hepi
  rw [classOf_secondExteriorPower_eq hsq halt F hF,
    classOf_secondExteriorPower_eq hsq halt E hE,
    classOf_secondExteriorPower_eq hsq halt G hG, hsym, classOf_shortExact f g w hE hF hG hex,
    ← classOf_mul E G hE hG]
  ring

/-- The product relation for `⋀²` follows from the one for `Sym²`: for finite locally free
modules `ℰ` and `ℱ`, the relation `[Sym²(ℰ ⊗ ℱ)] = [⋀²ℰ ⊗ ⋀²ℱ] + [Sym²ℰ ⊗ Sym²ℱ]` implies
`[⋀²(ℰ ⊗ ℱ)] = [Sym²ℰ ⊗ ⋀²ℱ] + [⋀²ℰ ⊗ Sym²ℱ]`. -/
theorem classOf_alt_tensor_of_sym
    (hsq : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E))
    (halt : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E))
    (E F : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hsym : classOf X (secondSymmetricPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
      classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondExteriorPower X E) (secondExteriorPower X F)) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondSymmetricPower X E) (secondSymmetricPower X F))) :
    classOf X (secondExteriorPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
      classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondSymmetricPower X E) (secondExteriorPower X F)) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondExteriorPower X E) (secondSymmetricPower X F)) := by
  have hEF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.tensorObjRingedSpace X E F) := @isFiniteLocallyFree_tensorObj X E F hE hF
  rw [classOf_secondExteriorPower_eq hsq halt _ hEF, hsym,
    ← classOf_mul _ _ (halt E hE) (halt F hF),
    ← classOf_mul _ _ (hsq E hE) (hsq F hF),
    ← classOf_mul _ _ (hsq E hE) (halt F hF),
    ← classOf_mul _ _ (halt E hE) (hsq F hF),
    ← classOf_mul E F hE hF, classOf_secondExteriorPower_eq hsq halt E hE,
    classOf_secondExteriorPower_eq hsq halt F hF]
  ring

end VectorBundleKZero

end AlgebraicGeometry

end
