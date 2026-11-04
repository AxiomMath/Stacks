module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareCube
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization

/-!
# The source identification of the localization square, on cohomology

`RingTheory.TorIndependence.localizedSquareDomainIso` identifies the two readings over `R'` of a
complex `P` of `A₂`-modules, where `R₂` is a localization of `R` and `A₂` an `A`-algebra sitting
over it:

`((P|_A)|_R) ⊗ᴸ_R R'  ≅  (P|_{R₂}) ⊗ᴸ_{R₂} R'`.

On cohomology the left-hand side is the base-change cohomology of `P|_A` over `R`, an
`A ⊗_R R'`-module, and the right-hand side is the base-change cohomology of `P` over `R₂`, an
`A₂ ⊗_{R₂} R'`-module. The affine reduction of [stacks 0DJ8] uses the identification as one of
modules over the *target* ring `A₂ ⊗_{R₂} R'` — that is the ring over which the source of the
pointwise map of [stacks 0DJ7] at a point of `X'` lives — so it needs the two equivariances
recorded here: for the left tensor factor `A₂` and for the right tensor factor `R'`.

Neither is more than naturality. The action of `x : A₂` on the right-hand side is, by
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, the derived base change over
`R₂` of scalar multiplication `x • 𝟙` on `P`, and the identification is natural in `P`; the two
actions of `R'` are both the `R'`-module structure the derived extension of scalars supplies, by
`RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul`, and the identification is a
morphism of `R'`-modules.

## Main definitions

* `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq`: the identification with the ring map
  `R → R'` given in an arbitrary spelling equal to the composite `R → R₂ → R'`.

## Main results

* `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_smul`: the identification
  carries scalar multiplication by `x : A₂` on the complex to the action of the left tensor
  factor `A₂` of `A₂ ⊗_{R₂} R'`.
* `RingTheory.TorIndependence.localizedSquareDomainIsoOfEq_homology_includeRight_smul`: it
  carries the action of the right tensor factor `R'` of `A ⊗_R R'` to that of the right tensor
  factor `R'` of `A₂ ⊗_{R₂} R'`.

## Implementation notes

The four algebra structures are the four ring maps of the square taken as data, written as
`letI` in the statements: `a` for `R → A`, `a₂` for `R₂ → A₂`, `b₂` for `R₂ → R'` and a given
`brr` for `R → R'`. That `brr` is a free variable rather than the composite
`b₂ ∘ (R → R₂)` is what lets a chart use the statements at all: at a chart the composite reads
`baseStalkMap ∘ (𝒪_S(V) → 𝒪_{S, f(g' x')})` while the two corner moves on cohomology are stated
over `(𝒪_{S'}(V') → 𝒪_{S', f' x'}) ∘ ch.b`, and those are equal ring maps with different
spellings — `AlgebraicGeometry.BaseChangeChart.toStalkR'_b` — so the algebra structures, and
hence the rings `A ⊗_R R'` the two sides are modules over, are not the same term.
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr` absorbs the difference into the
identification itself, which is the only place it can go: a comparison's type mentions its edges.

On the source there is no action of `A₂` to write as a scalar multiplication: the source is the
base-change cohomology of `P|_A`, whose module structure is over `A ⊗_R R'`, and `A₂` acts on it
only through the functor. So the first statement has the source side written as the image of
`x • 𝟙 P` under the source functor followed by `H^n`, exactly as
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul` writes the action it
characterizes.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

section LocalizedDomainHomology

variable {R A R₂ A₂ R' : Type u}
  [CommRing R] [CommRing A] [CommRing R₂] [CommRing A₂] [CommRing R']
  [Algebra R R₂] [Algebra A A₂]
  (SR : Submonoid R) [IsLocalization SR R₂]
  (a : R →+* A) (a₂ : R₂ →+* A₂) (b₂ : R₂ →+* R') {brr : R →+* R'}
  (hloc : (algebraMap A A₂).comp a = a₂.comp (algebraMap R R₂))
  (hbrr : b₂.comp (algebraMap R R₂) = brr)
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R₂)] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R')]

/-- **The source identification, with `R → R'` in a given spelling.**
`RingTheory.TorIndependence.localizedSquareDomainIso` states the identification at the composite
`R → R₂ → R'`; this is the same identification with that composite replaced by any ring map
equal to it, the difference absorbed by
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr`. -/
public def localizedSquareDomainIsoOfEq :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u} brr).functor) ≅
      (ModuleCat.restrictScalars.{u} a₂).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} b₂).functor :=
  Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory)
      (Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory)
        (totalDerivedExtensionScalarsCongr.{u, u} hbrr).symm) ≪≫
    localizedSquareDomainIso.{u, u} SR a a₂ b₂ hloc

/-- **The source identification is equivariant for `A₂`.** On cohomology,
`RingTheory.TorIndependence.localizedSquareDomainIsoOfEq` carries scalar multiplication by
`x : A₂` on the complex `P` to the action of the left tensor factor `A₂` of `A₂ ⊗_{R₂} R'` on the
base-change cohomology of `P` over `R₂`.

The action of `x` on the target is that derived base change of `x • 𝟙` by
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, so this is the naturality of
the identification at `x • 𝟙 P`. -/
public theorem localizedSquareDomainIsoOfEq_homology_smul (n : ℤ)
    (P : DerivedCategory (ModuleCat.{u} A₂)) (x : A₂) :
    letI := a.toAlgebra
    letI := brr.toAlgebra
    letI := a₂.toAlgebra
    letI := b₂.toAlgebra
    ∀ m : baseChangeCohomology (R := R) (R' := R')
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj P) n,
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.app P)).hom
          (((((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
                derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (x • 𝟙 P)).hom m) =
        (Algebra.TensorProduct.includeLeft (R := R₂) (S := R₂) x : A₂ ⊗[R₂] R') •
          (show baseChangeCohomology (R := R₂) (R' := R') P n from
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
                ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.app P)).hom m) := by
  let := a.toAlgebra
  let := brr.toAlgebra
  let := a₂.toAlgebra
  let := b₂.toAlgebra
  intro m
  have hnat := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.naturality (x • 𝟙 P))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hnat
  rw [baseChangeCohomology_includeLeft_smul]
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat) m

/-- **The source identification is equivariant for the right tensor factor.** On cohomology,
`RingTheory.TorIndependence.localizedSquareDomainIsoOfEq` carries the action of the right tensor
factor `R'` of `A ⊗_R R'` to the action of the right tensor factor `R'` of `A₂ ⊗_{R₂} R'`.

Both are the `R'`-module structure of the derived extension of scalars, by
`RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul`, and the identification is a
morphism of `R'`-modules. -/
public theorem localizedSquareDomainIsoOfEq_homology_includeRight_smul (n : ℤ)
    (P : DerivedCategory (ModuleCat.{u} A₂)) (r : R') :
    letI := a.toAlgebra
    letI := brr.toAlgebra
    letI := a₂.toAlgebra
    letI := b₂.toAlgebra
    ∀ m : baseChangeCohomology (R := R) (R' := R')
        ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj P) n,
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.app P)).hom
          ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
        (Algebra.TensorProduct.includeRight r : A₂ ⊗[R₂] R') •
          (show baseChangeCohomology (R := R₂) (R' := R') P n from
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
                ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.app P)).hom m) := by
  let := a.toAlgebra
  let := brr.toAlgebra
  let := a₂.toAlgebra
  let := b₂.toAlgebra
  intro m
  rw [baseChangeCohomology_includeRight_smul, baseChangeCohomology_includeRight_smul]
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    ((localizedSquareDomainIsoOfEq.{u} SR a a₂ b₂ hloc hbrr).hom.app P)).hom.map_smul r m

end LocalizedDomainHomology

end RingTheory.TorIndependence

end
