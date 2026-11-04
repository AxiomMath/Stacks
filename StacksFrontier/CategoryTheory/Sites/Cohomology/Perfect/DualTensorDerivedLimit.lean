module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a homotopy colimit of perfect objects

Let `(𝒞, 𝒪)` be a ringed site, let `(Kₙ)` be a system of **perfect** objects of `D(𝒪)` whose
direct sum exists, let `K = hocolim Kₙ` and let `E` be an object of `D(𝒪)`. **Stacks 0A0A**
says that

`R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Kₙ^∨)`.

`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` proves this
from two inputs, of which the direct-sum comparison is discharged by
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`, while the other — clause 3
of [Stacks, Tag 08JJ] in the shape "the canonical map of [Stacks, Tag 08JD] is invertible" — is
not available in the library for anything beyond a retract of a finite direct sum of copies of
`𝒪`.

This file supplies that second input from **perfectness alone**. What the proof of Stacks 0A0A
uses clause 3 of Stacks 08JJ for is a single thing: an isomorphism of the inverse system
`n ↦ E ⊗^𝐋_𝒪 Kₙ^∨` with the inverse system `n ↦ R𝑆heafHom_𝒪(Kₙ, E)`. The library has clause 3
itself, for a perfect object and with both of its naturalities — as
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` together with
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso_naturality_dual` — by the route of
[Stacks, Tag 0ATN] rather than through the canonical map of Stacks 08JD. Those two assemble the
isomorphism of systems directly, so the canonical map of Stacks 08JD never enters and nothing
has to be said about it.

## Main results

* `AlgebraicGeometry.RingedSite.tensorDerivedDualSystemIsoOfPerfect`: for a system of perfect
  objects, the inverse system `n ↦ E ⊗^𝐋_𝒪 Kₙ^∨` is isomorphic to `n ↦ R𝑆heafHom_𝒪(Kₙ, E)`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isPerfect`: **Stacks 0A0A
  for a system of perfect objects, with no hypothesis beyond perfectness and the existence of
  the direct sum.**

## Implementation notes

The derived tensor product is the canonical one of [Stacks, Tag 06YU],
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, and not a parameter: the isomorphism of
[Stacks, Tag 08JJ] used here is stated for it, its bifunctor being
`Stacks.SheafOfModules.derivedTensorProductFunctor`, which is that datum's `tensor` field on
the nose. A statement for an arbitrary derived tensor product datum would need a comparison of
two such data, which is a different matter from the content here.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, which
is the pin of [Stacks, Tag 0ATN] and so of
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **For a system of perfect objects the tensor-dual system is isomorphic to the system of
derived internal Homs.** Its component at `n` is the isomorphism
`E ⊗^𝐋_𝒪 Kₙ^∨ ≅ R𝑆heafHom_𝒪(Kₙ, E)` of [Stacks, Tag 08JJ] and its naturality is the
contravariant naturality of that isomorphism in the dualized object.

This is the only use the proof of [Stacks, Tag 0A0A] makes of clause 3 of [Stacks, Tag 08JJ],
and it is supplied here without the canonical map of [Stacks, Tag 08JD]. -/
def tensorDerivedDualSystemIsoOfPerfect
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hF : ∀ n : ℕ, X.IsPerfect (F.obj n)) :
    tensorDerivedDualSystem X (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X) F E ≅
      derivedSheafHomSystem X F E :=
  NatIso.ofComponents
    (fun n ↦ derivedDualTensorSheafHomIso X (F.obj n.unop) E (hF n.unop))
    (fun g ↦ derivedDualTensorSheafHomIso_naturality_dual X (hF _) (hF _) E (F.map g.unop))

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0A0A for a system of perfect objects.** Let `(Kₙ)` be a system of perfect objects
of `D(𝒪)` whose direct sum exists and let `K = hocolim Kₙ`. For every object `E` of `D(𝒪)`,

`R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Kₙ^∨)`,

the derived tensor product being the canonical one of [Stacks, Tag 06YU].

Both inputs of the source's proof are discharged: the direct-sum comparison
`R𝑆heafHom_𝒪(⊕ Kₙ, E) ⟶ ∏ R𝑆heafHom_𝒪(Kₙ, E)` by
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`, and clause 3 of
[Stacks, Tag 08JJ] by `AlgebraicGeometry.RingedSite.tensorDerivedDualSystemIsoOfPerfect`, which
is where perfectness is used — exactly as in the source. -/
@[stacks 0A0A "the stated identity `RSheafHom(K, E) = R lim (E ⊗^L_O Kₙ^∨)` for \
`K = hocolim Kₙ` with the `Kₙ` perfect, for the canonical derived tensor product, with both \
inputs of the source's proof proved rather than assumed"]
theorem isDerivedLimit_tensorDerivedDual_of_isPerfect
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct F.obj]
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X) F E).obj (op n)]
    (hF : ∀ n : ℕ, X.IsPerfect (F.obj n))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (tensorDerivedDualSystem X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X) F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K)) :=
  IsDerivedLimit.of_natIso (tensorDerivedDualSystemIsoOfPerfect X F E hF).symm
    (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit' X F E hK)

end AlgebraicGeometry.RingedSite

end
