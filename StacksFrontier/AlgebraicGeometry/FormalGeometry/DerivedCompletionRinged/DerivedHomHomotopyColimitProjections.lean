module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# Derived internal Hom out of a homotopy colimit, with the projections of the derived limit named

Let `(𝒞, 𝒪)` be a ringed site, let `(Kₙ, fₙ)` be a system of objects of `D(𝒪)` whose direct sum
exists, let `E` be an object of `D(𝒪)` and let `(K, iₙ, c)` be a derived colimit datum for the
system — [Stacks, Tag 0CRH], `CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections`.
Then

`R𝑆heafHom_𝒪(K, E) = R lim R𝑆heafHom_𝒪(Kₙ, E)`

*through the projections* `R𝑆heafHom_𝒪(iₙ, E)`, and — granted clause 3 of [Stacks, Tag 08JJ] —
likewise `R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Kₙ^∨)` through those projections followed by the
inverse of the canonical map of [Stacks, Tag 08JD].

`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit` and
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` prove the
same two identities with `CategoryTheory.Pretriangulated.IsDerivedLimit`, which quantifies the
structural map of its Milnor triangle away and so says nothing about which cone the presentation
carries. That is what every argument comparing two derived-limit presentations of one tower
needs, and it is why [Stacks, Tag 0CRH] — the refinement of Definition 090Z that names the
coprojections — exists.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_derivedSheafHom_of_coprojections`
  — the formal half of [Stacks, Tag 0A0A], with the projections named.
* `AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_tensorDerivedDual_of_coprojections`
  — the same for the tower of derived tensor products with the duals.

## Implementation notes

The first statement is
`CategoryTheory.Pretriangulated.exists_distTriang_pi_lift_map_coprojections` at
`H = R𝑆heafHom_𝒪(-, E)`, whose conclusion is
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` on the nose; that predicate is not
mentioned there because its defining module has a far larger import closure, so the crossing is
the `exact` below.

The second is the first transported along `AlgebraicGeometry.RingedSite.tensorDerivedDualSystemIso`
by `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`. An
isomorphism of towers has eventual inverses at the same level, with the inverse component as the
section: the two composites are the identity, which is the transition map along `n ≤ n` because
`homOfLE (le_refl n) = 𝟙 n`. No reindexing enters, so the projections are transported one by one.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0CRH](https://stacks.math.columbia.edu/tag/0CRH)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The formal half of [Stacks, Tag 0A0A] with the projections of the derived limit named.**
Let `(K, iₙ, c)` be a derived colimit datum ([Stacks, Tag 0CRH]) for a system
`F : ℕ ⥤ D(𝒪)` whose direct sum exists, and let the canonical comparison
`R𝑆heafHom_𝒪(⊕ Kₙ, E) ⟶ ∏ R𝑆heafHom_𝒪(Kₙ, E)` be invertible. Then the maps
`R𝑆heafHom_𝒪(iₙ, E)` are the projections of a derived-limit presentation of
`n ↦ R𝑆heafHom_𝒪(Kₙ, E)` at `R𝑆heafHom_𝒪(K, E)`: their product is the first map of a
distinguished Milnor triangle.

No perfectness is involved, exactly as in
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`, of which this
is the refinement that pins the cone. -/
theorem isDerivedLimitWithProjections_derivedSheafHom_of_coprojections
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct F.obj]
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)]
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι F.obj n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ F.obj)) ⟶
        ∏ᶜ fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (hK : IsHomotopyColimitWithCoprojections F K i c) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (derivedSheafHomSystem X F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K))
      (fun n : ℕ ↦ ((derivedSheafHomBifunctor X).flip.obj E).map (i n).op) :=
  exists_distTriang_pi_lift_map_coprojections ((derivedSheafHomBifunctor X).flip.obj E) F
    (fun T hT ↦ exists_distinguished_derivedSheafHom X E T hT) hcomp hK

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **[Stacks, Tag 0A0A] with the projections of the derived limit named.** Under the two inputs
of `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` — the
direct-sum comparison `hcomp` and clause 3 of [Stacks, Tag 08JJ] at every term — a derived
colimit datum `(K, iₙ, c)` for the system makes the maps

`R𝑆heafHom_𝒪(K, E) ⟶ E ⊗^𝐋_𝒪 Kₙ^∨`,

the images `R𝑆heafHom_𝒪(iₙ, E)` of the coprojections followed by the inverse of the canonical map
of [Stacks, Tag 08JD], the projections of a derived-limit presentation of `n ↦ E ⊗^𝐋_𝒪 Kₙ^∨` at
`R𝑆heafHom_𝒪(K, E)`. -/
theorem isDerivedLimitWithProjections_tensorDerivedDual_of_coprojections
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct F.obj]
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X T F E).obj (op n)]
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι F.obj n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ F.obj)) ⟶
        ∏ᶜ fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T (F.obj n) E))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (hK : IsHomotopyColimitWithCoprojections F K i c) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (tensorDerivedDualSystem X T F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K))
      (fun n : ℕ ↦ ((derivedSheafHomBifunctor X).flip.obj E).map (i n).op ≫
        (tensorDerivedDualSystemIso X T F E hdual).inv.app (op n)) :=
  NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    (tensorDerivedDualSystemIso X T F E hdual).inv
    (fun n ↦ ⟨n, le_rfl, (tensorDerivedDualSystemIso X T F E hdual).hom.app (op n), by simp,
      by simp⟩)
    (isDerivedLimitWithProjections_derivedSheafHom_of_coprojections X F E hcomp hK)

end AlgebraicGeometry.RingedSite

end
