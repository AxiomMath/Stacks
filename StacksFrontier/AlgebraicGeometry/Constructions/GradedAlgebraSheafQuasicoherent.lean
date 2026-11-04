module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent

/-!
# Quasi-coherence of the algebra sheaf of a graded algebra, and of `Sym(ℰ)`

`Stacks.RelativeSpec.gradedAlgebraSheaf X A hc` is a sheaf of graded `𝒪_X`-algebras with
commuting homogeneous multiplication, read as a sheaf of commutative `𝒪_X`-algebras. This file
identifies its underlying module with the coproduct of the homogeneous pieces, when those are
concentrated in nonnegative degrees, and so proves it quasi-coherent as soon as that coproduct
is.

The consequence is **[Stacks, Tag 01CK] in the form the relative spectrum consumes**: the
symmetric algebra of a quasi-coherent module sheaf on a scheme is a quasi-coherent sheaf of
commutative algebras. It is an instance, and
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule` imports this file, so the
vector bundle `𝐕(ℰ)` and its projection are constructed there for any quasi-coherent `ℰ` with no
hypothesis beyond quasi-coherence of `ℰ` itself.

## Main definitions

* `Stacks.RelativeSpec.gradedDirectSumIsoUnderlyingModule`: the module underlying
  `gradedAlgebraSheaf` is the sheafification of the direct sum of the homogeneous components.
* `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule`: it is the coproduct of the pieces
  over *all* of `ℤ`, with no hypothesis on the grading.
* `Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule`: for pieces concentrated in nonnegative
  degrees, it is the coproduct of the nonnegative pieces.

## Main results

* `Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf`: **`gradedAlgebraSheaf` is
  quasi-coherent as soon as the coproduct of its homogeneous pieces is.**
* `Stacks.RelativeSpec.isQuasicoherent_intCoprod`: a `ℤ`-indexed coproduct of quasi-coherent
  modules on a scheme is quasi-coherent.
* `Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf_of_piece` (in
  `GradedAlgebraSheafQuasicoherentInt`): **`gradedAlgebraSheaf` is quasi-coherent as soon as
  every homogeneous piece is**, with no hypothesis on which degrees are occupied.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`: **the symmetric
  algebra of a quasi-coherent module sheaf, as an algebra sheaf, is quasi-coherent.** This is
  [Stacks, Tag 01CK] in the vocabulary `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent`, and it
  is an instance, so the declarations of `VectorBundleOfModule` need no such hypothesis.

## Implementation notes

**Why there is a `ℤ`-indexed form as well as an `ℕ`-indexed one.** [Stacks, Tag 0FQW] grades a
sheaf of algebras by `n ∈ ℤ`, and `SheafOfModules.GradedAlgebra` follows it, so a consumer with a
genuinely `ℤ`-graded algebra cannot supply `isQuasicoherent_gradedAlgebraSheaf`'s `hzero`.
`Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule` and
`isQuasicoherent_gradedAlgebraSheaf_of_piece` are the same statements with the `ℕ`-indexed
coproduct and `hzero` removed; they cost nothing, because
`Stacks.gradedDirectSumIsoUnderlyingModule` is already stated on the `ℤ`-indexed direct sum and
`Stacks.sheafifyDirectSumIso` is indifferent to the index type. The `ℕ`-indexed pair is kept:
it is the form `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf` and the
`Sym`/cone consumers are written against, and `hzero` is free for them.

There are two ungraded realizations of a sheaf of graded algebras in this library, and the
distinction is the whole reason this file is needed.

`Stacks.RelativeSpec.ungradedAlgebraSheaf` sheafifies the `CommRingCat`-valued presheaf of direct
sums, and `Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf` proves *it* quasi-coherent.
`Stacks.RelativeSpec.gradedAlgebraSheaf` instead takes the `RingCat`-sheafification
`SheafOfModules.GradedAlgebra.ungradedSheaf` and upgrades it to `CommRingCat` without
re-sheafifying, which is why `Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf` holds by `rfl`.
The two are isomorphic — that is
`Stacks.RelativeSpec.ringSheafIsoUngradedSheaf` — but only as sheaves of *rings*, so transporting
quasi-coherence along it would need that iso upgraded to `CommRingCat` and shown to commute with
the two structure morphisms. It is cheaper, and gives a cleaner statement, to instantiate the
generic comparison `Stacks.GradedAlgebra.directSumIsoUnderlyingModule` at the second realization
directly, which is what the four declarations below do: they mirror
`Stacks.RelativeSpec.{ungradedDirectSumHom, directSumIsoUnderlyingModule, coprodDirectSumHom,
coprodIsoUnderlyingModule}` with the sheafification unit `Stacks.RelativeSpec.ungradedRingUnit`
replaced by `SheafOfModules.GradedAlgebra.toTotalSheaf`.

Local injectivity and local surjectivity of that unit are proved here rather than taken from the
instances of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization`: those sit under
`[J.WEqualsLocallyBijective RingCat]`, which does not synthesize for the Zariski site, so
`inferInstance` fails on them. They are instead read off `toSheafify` directly, by
`Presheaf.equalizerSieve_mem` and `Presheaf.imageSieve_mem`, exactly as
`Stacks.RelativeSpec.isLocallyInjective_ungradedRingUnit` does for the other realization.

The factorisation hypothesis holds by `rfl`, because
`SheafOfModules.GradedAlgebra.ungradedStructureMap` is
`structureHom ≫ toTotalSheaf` by definition and
`Stacks.CommRingSheaf.homMk` does not change the underlying morphism of sheaves of rings.

The record at `StacksFrontier/AlgebraicGeometry/Constructions/ConeOfGradedAlgebra.lean:52-63`
asserts that the modules declaring the two realizations cannot be imported together, both
declaring `Stacks.GradedAlgebra.mul_comm_total`. That is stale: the second is now
`Stacks.GradedAlgebra.mul_comm_total_of_addCommMonoid`
(`DeRham/LineBundle/TotalSpace.lean:95`), the names no longer collide, and this file imports both.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- The sheafification unit of the ungraded realization is compatible with the structure map of
the graded algebra and the structure morphism of `Stacks.RelativeSpec.gradedAlgebraSheaf`. -/
theorem structureHom_comp_toTotalSheaf :
    A.toPresheafGradedAlgebra.structureHom ≫
        A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat)) =
      (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc)).hom :=
  rfl

/-- The sheafification unit of the ungraded realization is locally injective. -/
theorem isLocallyInjective_toTotalSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (X : TopCat))
      (A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat))) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (X : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat))
      A.toPresheafGradedAlgebra.totalPresheaf) x y h⟩

/-- The sheafification unit of the ungraded realization is locally surjective. -/
theorem isLocallySurjective_toTotalSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (A.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (X : TopCat))) :=
  ⟨fun s => Presheaf.imageSieve_mem (Opens.grothendieckTopology (X : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat))
      A.toPresheafGradedAlgebra.totalPresheaf) s⟩

/-- The comparison morphism from the direct sum of the homogeneous components to the module
underlying `Stacks.RelativeSpec.gradedAlgebraSheaf`. -/
def gradedDirectSumHom :
    Stacks.directSum (fun n : ℤ => (A.piece n).val) ⟶
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc)).val :=
  Stacks.GradedAlgebra.directSumHom A.toPresheafGradedAlgebra
    (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))
    (A.toPresheafGradedAlgebra.toTotalSheaf _) (structureHom_comp_toTotalSheaf X A hc)

/-- **The module underlying `Stacks.RelativeSpec.gradedAlgebraSheaf` is the sheafification of the
direct sum of the homogeneous components.** -/
def gradedDirectSumIsoUnderlyingModule :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (Stacks.directSum fun n : ℤ => (A.piece n).val) ≅
      AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc) :=
  Stacks.GradedAlgebra.directSumIsoUnderlyingModule A.toPresheafGradedAlgebra
    (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))
    (A.toPresheafGradedAlgebra.toTotalSheaf _) (structureHom_comp_toTotalSheaf X A hc)
    (isLocallyInjective_toTotalSheaf X A) (isLocallySurjective_toTotalSheaf X A)

/-- **A `ℤ`-indexed coproduct of quasi-coherent modules on a scheme is quasi-coherent.**
Quasi-coherence on a scheme is stable under colimits of any shape, so this needs nothing of the
grading; it is what discharges the coproduct hypothesis in the `ℤ`-indexed statements below. -/
theorem isQuasicoherent_intCoprod (P : ℤ → SheafOfModules.{u} X.ringCatSheaf)
    (hP : ∀ n : ℤ, (P n).IsQuasicoherent) : (∐ P).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor P) fun n => hP n.as

/-- `Stacks.RelativeSpec.gradedDirectSumHom`, restricted to the nonnegative degrees. -/
def gradedCoprodDirectSumHom :
    Stacks.directSum (fun n : ℕ => (A.piece (n : ℤ)).val) ⟶
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc)).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (A.piece n).val) ≫ gradedDirectSumHom X A hc

/-- **The module underlying `Stacks.RelativeSpec.gradedAlgebraSheaf` of a graded algebra
concentrated in nonnegative degrees is the coproduct of its homogeneous pieces.** -/
def gradedCoprodIsoUnderlyingModule (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (∐ fun n : ℕ => A.piece (n : ℤ)) ≅
      AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc) :=
  (Stacks.sheafifyDirectSumIso (fun n : ℕ => A.piece (n : ℤ))).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective (gradedCoprodDirectSumHom X A hc)
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
          (isLocallyInjective_toTotalSheaf X A)))
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
          (isLocallySurjective_toTotalSheaf X A)))

/-- **`Stacks.RelativeSpec.gradedAlgebraSheaf` of a graded algebra concentrated in nonnegative
degrees is quasi-coherent as soon as the coproduct of its homogeneous pieces is.** This is the
datum a relative spectrum requires. -/
theorem isQuasicoherent_gradedAlgebraSheaf (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
    (hqc : (∐ fun n : ℕ => A.piece (n : ℤ)).IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (gradedCoprodIsoUnderlyingModule X A hc hzero) hqc

end Stacks.RelativeSpec

namespace AlgebraicGeometry.Scheme.Modules

/-- **[Stacks, Tag 01CK] in the form the relative spectrum consumes: the symmetric algebra of a
quasi-coherent module sheaf on a scheme is a quasi-coherent sheaf of commutative algebras.**

The negative-degree pieces of `Sym(ℰ)` are zero and the coproduct of the nonnegative ones is
quasi-coherent by [Stacks, Tag 01CL], so
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` applies.

This is what `StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule` imports this file
for: the vector bundle `𝐕(ℰ) = Spec_S(Sym(ℰ))` and its projection exist for every quasi-coherent
`ℰ`, with no finiteness and no local freeness. -/
instance isQuasicoherent_symmetricAlgebraSheaf (S : Scheme.{u})
    (E : SheafOfModules.{u} S.ringCatSheaf) [E.IsQuasicoherent] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (symmetricAlgebraSheaf S E) :=
  Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf S (symmetricAlgebra S E)
    (symmetricAlgebra_mul_comm S E) (fun n hn => isZero_symmetricAlgebra_piece S E n hn)
    (isQuasicoherent_coprod_symmetricAlgebra S E)

end AlgebraicGeometry.Scheme.Modules

end
