module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Completion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingForComplexesOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying

/-!
# Derived internal Hom into a Čech completion

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and write
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` for the candidate completion functor of [Stacks, Tag 099B]
built in `Completion.lean`. For every `A ∈ D(𝒪)`

`R𝑆heafHom_𝒪(A, K^∧) = R𝑆heafHom_𝒪(A ⊗^𝐋_𝒪 Č(f), K)`.

This is the **first step of the `hΦ` hypothesis** of
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion`: the source of
[Stacks, Tag 099B] computes `R𝑆heafHom_𝒪(𝒪_g, K^∧)` as derived internal Hom out of
`Č(f) ⊗_𝒪 𝒪_g`, and then observes that for `g = f_i` the latter complex is contractible.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHom_completionFunctor_iso`: the displayed
  identification, for an arbitrary `A ∈ D(𝒪)`.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_completionFunctor_of_isZero_derivedTensor`:
  consequently the completion `K^∧` is right-orthogonal to every `A` which the Čech complex
  annihilates, which is the form in which
  `IsDerivedCompleteAt` consumes the identification.

## Implementation notes

Nothing here is new mathematics and nothing is assumed: the identification is the derived
tensor–internal-Hom adjunction of [Stacks, Tag 08J9],
`AlgebraicGeometry.RingedSite.derivedCurryIso`, read at `L = Č(f)`, together with the
definition `completionFunctor X f = (derivedSheafHomBifunctor X).obj (op Q(Č(f)))`. Tag 08J9
holds for arbitrary objects of `D(𝒪)` — it chooses a K-flat model of its middle variable
internally — so no K-flatness of the Čech complex is needed, and in particular the route
through parts (2) and (3) of [Stacks, Tag 0996]
(`AlgebraicGeometry.RingedSite.derivedSheafHom_coextendScalarsIso` and
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulCurryIso`, both proved) is not the only
one: those two give the identification when *both* arguments are localizations `𝒪_f`, `𝒪_g` of
the structure sheaf, whereas the first step of `hΦ` needs it with the *complex* `Č(f)` in the
inner slot, which is what Tag 08J9 supplies.

`AlgebraicGeometry.RingedSite.hasMapBifunctor` is enabled as a local instance, as it is in
`AwayInternalHomMul.lean` and in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/CurryingForComplexesOfModules.lean`: it
is not an assumption
but the existing instance of `Stacks.Cohomology.SheafHomComplexCurrying`, named because
instance search solves its `∀`-quantified form only in applied form.

### What this does not close

`hΦ` asks that every `K^∧` be derived complete along the ideal sheaf, and three of its four
inputs remain open; see the module note of `Completion.lean`. The identification above removes
the first. What the second needs is the **base change of the Čech complex**: to apply
`AlgebraicGeometry.RingedSite.isZero_Q_extendedAlternatingCech_of_isUnit` — which asks that one
of the sections be a unit on `𝒪` itself — to `𝒪_{f_i} ⊗^𝐋_𝒪 Č(f)`, one needs that complex
identified with the extended alternating Čech complex of `f_1, …, f_r` over `𝒪_{f_i}`, where
`f_i` is a unit. The ring-level input is
`AlgebraicGeometry.RingedSite.awaySheafMulIso`, `𝒪_{h₁h₂} ≅ (𝒪_{h₂})_{h₁}` of
`AwayBaseChange.lean`; the complex-level identification is nowhere. The remaining two inputs —
the slice-site form of `AlgebraicGeometry.RingedSite.IsDerivedComplete` and the local
generation of the ideal sheaf by `f_1, …, f_r` ([Stacks, Tag 0998]) — are unaffected by this
file.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] hasMapBifunctor

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Derived internal Hom into a Čech completion**, which is the first step of the `hΦ`
hypothesis of `isRightAdjoint_ι_isDerivedComplete_of_completion`: for every `A` and `K` in
`D(𝒪)`

`R𝑆heafHom_𝒪(A, K^∧) = R𝑆heafHom_𝒪(A ⊗^𝐋_𝒪 Č(f), K)`,

where `K^∧ = R𝑆heafHom_𝒪(Č(f), K)` is `completionFunctor X f` applied to `K`.

It is the derived tensor–internal-Hom adjunction of [Stacks, Tag 08J9], `derivedCurryIso`, at
the middle variable `Q(Č(f))`. Nothing is assumed of `A`, of `K` or of the sections
`f_1, …, f_r`; in particular the Čech complex is not required to be K-flat, Tag 08J9 choosing a
K-flat model of its middle variable itself. The tensor factors appear in the order
`A ⊗^𝐋_𝒪 Č(f)`, the source writing `Č(f) ⊗_𝒪 𝒪_g`. -/
def derivedSheafHom_completionFunctor_iso
    (A K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op A)).obj ((completionFunctor X f).obj K) ≅
      ((derivedSheafHomBifunctor X).obj (op
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj
          (DerivedCategory.Q.obj (extendedAlternatingCech X f))))).obj K :=
  derivedCurryIso X A (DerivedCategory.Q.obj (extendedAlternatingCech X f)) K

/-- **A Čech completion is right-orthogonal to everything the Čech complex annihilates.** If
`A ⊗^𝐋_𝒪 Č(f)` is a zero object of `D(𝒪)` then `R𝑆heafHom_𝒪(A, K^∧) = 0`.

This is the form in which the derived-completeness criterion consumes the identification above:
`IsDerivedCompleteAt` asks exactly for the vanishing of derived
internal Hom out of a localization of the structure sheaf. Applied at `A = 𝒪_{f_i}` it is the
step of [Stacks, Tag 099B] which says that the completion is complete along each generator,
together with the contractibility of `𝒪_{f_i} ⊗^𝐋_𝒪 Č(f)`, which is the base change of the
Čech complex and is
`RingedSite.isZero_derivedTensor_awayComplex_extendedAlternatingCech_prodGlobalSection`
of `CechBaseChange.lean`; the composite is
`AlgebraicGeometry.RingedSite.memVanishingIdeal_completionFunctor_obj` of
`GeneratedIdealComplete.lean`. -/
theorem isZero_derivedSheafHom_completionFunctor_of_isZero_derivedTensor
    (A K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsZero (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj
      (DerivedCategory.Q.obj (extendedAlternatingCech X f)))) :
    IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj
      ((completionFunctor X f).obj K)) :=
  IsZero.of_iso
    ((isZero_derivedSheafHom_iff_of_iso X K (h.iso (isZero_zero _))).mpr
      (isZero_derivedSheafHom_zero X K))
    (derivedSheafHom_completionFunctor_iso X f A K)

end Derived

end AlgebraicGeometry.RingedSite

end
