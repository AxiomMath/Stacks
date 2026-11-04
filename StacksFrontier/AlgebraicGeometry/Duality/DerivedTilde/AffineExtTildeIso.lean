module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorCompare
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison

/-!
# The cohomology sheaves of `R𝓗om(K̃, L̃)` are the sheafified `Ext` modules

Let `R` be a commutative ring, `X = Spec R`, and let `K`, `L` be objects of `D(R)` with `K`
pseudo-coherent and `L` bounded below. Part (3)(a) of [Stacks, Tag 0A6H] identifies the derived
internal Hom of the sheafifications with the sheafification of the derived Hom,

`R𝓗om_{𝒪_X}(K̃, L̃) ≅ (RHom_R(K, L))~`,

and sheafification `M ↦ M̃` is exact, so it commutes with taking cohomology. Combining the two
identifies the `n`-th cohomology sheaf of `R𝓗om_{𝒪_X}(K̃, L̃)` with the sheafification of the
`R`-module `Hⁿ(RHom_R(K, L))`:

`Hⁿ(R𝓗om_{𝒪_X}(K̃, L̃)) ≅ (Hⁿ(RHom_R(K, L)))~`.

That `R`-module is in turn `Ext^n_R(K, L) = Hom_{D(R)}(K, L⟦n⟧)`, which is proved here for the
fixed-universe spelling `StacksDraft.DerivedHom.derivedHomAdjunction` of derived Hom that
[Stacks, Tag 0A6H] (3)(a) is stated with.

## Main results

* `AlgebraicGeometry.AffineExt.cohomologySheafIsoTilde` and
  `AlgebraicGeometry.AffineExt.nonempty_cohomologySheaf_iso_tilde`: the comparison isomorphism
  and its existence.
* `StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare`: the two library spellings of
  derived internal Hom at the ring's own module universe agree at every object.
* `AlgebraicGeometry.AffineExt.extLinearEquivHomologyDerivedHom`: the degree-`n` cohomology of
  `RHom_R(K, L)` is `Ext^n_R(K, L)`, `R`-linearly.

## Implementation notes

The two inputs to the cohomology-sheaf comparison are
`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso`, which is part (3)(a) of the tag, and
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`, which commutes an exact
functor past the cohomology functors of the derived categories. The latter needs exactness of
`AlgebraicGeometry.tilde.functor R`, which is `AlgebraicGeometry.tilde.preservesFiniteLimits`
together with `Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor`; both are theorems rather
than instances in this development, so they are supplied as local instances, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineExt/Basic.lean`.

The `Ext` reading needs a bridge between the two spellings of derived internal Hom. The
Ext--cohomology comparison `StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` is
stated for `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the tensor--Hom bundle of
[Stacks, Tag 0A63] built over `ULift R` and transported back, whereas part (3)(a) is stated for
`StacksDraft.DerivedHom.derivedHomAdjunction`, the fixed-universe construction over `R` itself.
The two were reconciled only for the *tensor* halves, by
`Dualizing.derivedHomAdjunctionTensorNatIsoCompare`. Since each internal Hom is right adjoint, in
its covariant variable, to its own tensor product, that one reconciliation determines the Hom
halves as well: transposing, transporting along the tensor comparison and transposing back is a
bijection `Hom(Z, RHom₁(K, L)) ≃ Hom(Z, RHom₂(K, L))` compatible with precomposition in `Z`, so
`CategoryTheory.Yoneda.ext` produces the comparison of objects. No naturality of that comparison
in `K` or `L` is claimed; only the object-level statement is needed, since an isomorphism of
objects of `D(R)` already induces an `R`-linear isomorphism on cohomology.

The derived model is pinned by a local instance of priority `10000`: the import closure reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory` instances
are global, and `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`
requires that priority of its importers.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace StacksDraft.DerivedHom

-- Standard model only: `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The two library spellings of derived internal Hom agree at every object.**
`StacksDraft.DerivedHom.derivedHomAdjunction`, the fixed-universe construction over `A` itself,
and `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` at the ring's own module universe,
which is built over `ULift A` and transported back, have isomorphic internal-Hom objects.

Both are right adjoint in the covariant variable to their own derived tensor product, and those
tensor products are isomorphic as bifunctors by
`Dualizing.derivedHomAdjunctionTensorNatIsoCompare`; so the two representing objects are
isomorphic by `CategoryTheory.Yoneda.ext`. -/
def derivedHomAdjunctionHomObjCompare (A : Type u) [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, L) ≅
      (derivedHomAdjunctionOverRing.{u, u, u + 1} A).hom.obj (Opposite.op K, L) :=
  Yoneda.ext _ _
    (fun {Z} f => ((derivedHomAdjunctionOverRing.{u, u, u + 1} A).homEquiv Z K L).symm
      (((Dualizing.derivedHomAdjunctionTensorNatIsoCompare.{u} A).app (Z, K)).inv ≫
        (derivedHomAdjunction (R := A)).homEquiv Z K L f))
    (fun {Z} g => ((derivedHomAdjunction (R := A)).homEquiv Z K L).symm
      (((Dualizing.derivedHomAdjunctionTensorNatIsoCompare.{u} A).app (Z, K)).hom ≫
        (derivedHomAdjunctionOverRing.{u, u, u + 1} A).homEquiv Z K L g))
    (fun {_} f => by
      rw [AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply])
    (fun {_} g => by
      rw [AddEquiv.apply_symm_apply, Iso.inv_hom_id_assoc, AddEquiv.symm_apply_apply])
    (fun {Z Z'} f g => by
      refine ((derivedHomAdjunctionOverRing.{u, u, u + 1} A).homEquiv Z' K L).injective ?_
      rw [AddEquiv.apply_symm_apply,
        (derivedHomAdjunctionOverRing.{u, u, u + 1} A).homEquiv_naturality_left f,
        AddEquiv.apply_symm_apply, (derivedHomAdjunction (R := A)).homEquiv_naturality_left f,
        Iso.app_inv, Iso.app_inv, ← Category.assoc, ← Category.assoc,
        (Dualizing.derivedHomAdjunctionTensorNatIsoCompare.{u} A).inv.naturality])

end StacksDraft.DerivedHom

namespace AlgebraicGeometry.AffineExt

-- Standard model only: `StacksDraft.DerivedHom.derivedHomAdjunction`,
--   `AlgebraicGeometry.AffineExt.cohomologySheaf`.
attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

/-- **The cohomology sheaves of `R𝓗om(K̃, L̃)` on `Spec R` are the sheafified `Ext` modules.**
For `K` a pseudo-coherent and `L` a bounded-below object of `D(R)`, the `n`-th cohomology sheaf
of `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` is the `𝒪_{Spec R}`-module associated to the `R`-module
`Hⁿ(RHom_R(K, L))`.

This is part (3)(a) of [Stacks, Tag 0A6H], namely
`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso`, read in cohomological degree `n` and
then commuted past the exact functor `M ↦ M̃`. -/
def cohomologySheafIsoTilde (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) (n : ℤ) :
    cohomologySheaf R K L n ≅
      (tilde.functor R).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (Opposite.op K, L))) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      (affinePseudoCoherentDerivedSheafHomIso R K L hK hL) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (tilde.functor R) n).app
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (Opposite.op K, L))

/-- **The cohomology sheaves of `R𝓗om(K̃, L̃)` on `Spec R` are the sheafified `Ext` modules**, as
an existence statement. The comparison itself is
`AlgebraicGeometry.AffineExt.cohomologySheafIsoTilde`. -/
theorem nonempty_cohomologySheaf_iso_tilde (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) (n : ℤ) :
    Nonempty (AlgebraicGeometry.AffineExt.cohomologySheaf R K L n ≅
      (tilde.functor R).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (Opposite.op K, L)))) :=
  ⟨cohomologySheafIsoTilde R K L hK hL n⟩

/-- **The degree-`n` cohomology of `RHom_R(K, L)` is `Ext^n_R(K, L)`**, as an isomorphism of
`R`-modules. Together with `AlgebraicGeometry.AffineExt.cohomologySheafIsoTilde` this reads the
`n`-th cohomology sheaf of `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` as the sheafification of `Ext^n_R(K, L)`.

The derived Hom is the fixed-universe spelling `StacksDraft.DerivedHom.derivedHomAdjunction` that
[Stacks, Tag 0A6H] (3)(a) is stated with; it is carried to the spelling of [Stacks, Tag 0A63] by
`StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare`, where
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` identifies the cohomology with
`Ext`. -/
def extLinearEquivHomologyDerivedHom (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (Opposite.op K, L)) :
          Type u) ≃ₗ[R] CategoryTheory.DerivedCategory.Ext K L n :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
        (StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare R K L)).toLinearEquiv.trans
    ((((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} R L n).app
      (Opposite.op K)).toLinearEquiv.trans ULift.moduleEquiv).symm)

end AlgebraicGeometry.AffineExt

end
