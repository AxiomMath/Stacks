module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Completion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
import StacksCore.Tactic.StacksAttribute

/-! # Derived internal Hom into a Čech completion

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and write
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` for the candidate completion functor of [Stacks, Tag 099B]
constructed in `Completion.lean`. The first step of the source's proof that `K^∧` is derived
complete is the computation

`R𝑆heafHom_𝒪(M, K^∧) = R𝑆heafHom_𝒪(M ⊗^𝐋_𝒪 Č(f), K)`,

which is the derived currying isomorphism of [Stacks, Tag 08J9] read at the middle object
`Č(f)`. This file records that instance and the consequence the source uses it for: when the
derived tensor product `M ⊗^𝐋_𝒪 Č(f)` vanishes, so does `R𝑆heafHom_𝒪(M, K^∧)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomCompletionIso`: the computation above.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_completionFunctor_of_isZero_tensor`: if
  `M ⊗^𝐋_𝒪 Č(f)` is zero then `R𝑆heafHom_𝒪(M, K^∧)` is zero, for every `K`.

## Implementation notes

Nothing is constructed here. The derived currying isomorphism
`AlgebraicGeometry.RingedSite.derivedCurryIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCurrying.lean` is already
stated in full generality for three arbitrary objects of `D(𝒪)` on a `RingedSite.{u, u, u}`,
which is the universe spelling of this directory; the completion functor is derived internal
Hom out of one fixed object, so the instance needed is a substitution and not a special case.
The one thing that has to be checked is that the two spellings of the middle slot agree:
`completionFunctor` is `(derivedSheafHomBifunctor X).obj (op (Q (Č f)))`, so the middle object
is literally `DerivedCategory.Q.obj (extendedAlternatingCech X f)` and the substitution is by
`rfl`.

The source of the internal Hom is left arbitrary rather than specialized to the localization
`𝒪_g` of a global section, which is what [Stacks, Tag 0997] feeds it: the vanishing hypothesis
is the only thing the argument uses about it, and it is the hypothesis that is still owed.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] HasDerivedCategory.standard

/-- **Derived internal Hom into a Čech completion.** For objects `M`, `K` of `D(𝒪)`,

`R𝑆heafHom_𝒪(M, K^∧) ≅ R𝑆heafHom_𝒪(M ⊗^𝐋_𝒪 Č(f), K)`,

the derived currying isomorphism of [Stacks, Tag 08J9] read at the middle object `Č(f)`. This
is the first step of the source's proof that `K^∧` is derived complete. -/
def derivedSheafHomCompletionIso
    (M K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op M)).obj ((completionFunctor X f).obj K) ≅
      ((derivedSheafHomBifunctor X).obj
        (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj
          (DerivedCategory.Q.obj (extendedAlternatingCech X f))))).obj K :=
  derivedCurryIso X M (DerivedCategory.Q.obj (extendedAlternatingCech X f)) K

/-- **If `M ⊗^𝐋_𝒪 Č(f)` vanishes then so does `R𝑆heafHom_𝒪(M, K^∧)`, for every `K`.** This is
how the source uses the computation `R𝑆heafHom_𝒪(M, K^∧) = R𝑆heafHom_𝒪(M ⊗^𝐋_𝒪 Č(f), K)`: the
contractibility of the extended alternating Čech complex after inverting one of the `f_i`
([Stacks, Tag 099B], `homotopyIdZero_extendedAlternatingCech`) makes the hypothesis hold at
`M = 𝒪_{f_i}`. -/
theorem isZero_derivedSheafHom_completionFunctor_of_isZero_tensor
    (M K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : IsZero (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj
      (DerivedCategory.Q.obj (extendedAlternatingCech X f)))) :
    IsZero (((derivedSheafHomBifunctor X).obj (op M)).obj ((completionFunctor X f).obj K)) := by
  refine IsZero.of_iso ?_ (derivedSheafHomCompletionIso X f M K)
  exact Functor.map_isZero ((derivedSheafHomBifunctor X).flip.obj K) hM.op

end AlgebraicGeometry.RingedSite

end
