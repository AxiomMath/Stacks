module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityUnconditional
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjectsSupplement

/-!
# Brown representability on the derived category of the small affine site of a scheme

Let `S` be a scheme and write `(S_affine, 𝒪)` for its small affine Zariski site read with the
chaotic topology, carrying the sheaf of global functions as structure sheaf. Stacks 0GZ0 part (3)
says that an exact functor out of the category `QC(𝒪)` of cartesian objects of Stacks 0GYV which
transforms direct sums into direct sums has an exact right adjoint, with no hypothesis beyond
commutativity of the section rings; and on the chaotic site `QC(S_affine, 𝒪)` *is*
`D_QCoh(S_affine, 𝒪)`, the complexes with quasi-coherent cohomology, which is the comparison
(4) ≃ (5) of Stacks 0GZZ.

Combining the two gives Brown representability on `D_QCoh(S_affine, 𝒪)` for an arbitrary scheme:
every exact, direct-sum-preserving functor out of it has an exact right adjoint. This is the
abstract input that the Stacks proof of [Stacks, Tag 0A9E] takes from compact generation
([Stacks, Tag 09IS]) — here with no compact generation and no quasi-compactness or
quasi-separatedness hypothesis — but stated on the *affine site* rather than on `D_QCoh(𝒪_S)`;
see the coverage note below.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_isTriangulated_rightAdjoint_of_eq`:
  [Stacks, Tag 0GZ0] part (3) for the full subcategory cut out by any object property which is
  equal to the cartesian one.
* `AlgebraicGeometry.exists_isTriangulated_rightAdjoint_smallAffineChaoticDerivedQuasiCoherent`:
  **[Stacks, Tag 0GZ0] part (3) on `D_QCoh(S_affine, 𝒪)`**, for an arbitrary scheme `S`.

## Implementation notes

`exists_isTriangulated_rightAdjoint_of_eq` is a transport along an *equality* of object
properties rather than along an equivalence, and that is why it is stated with the property as a
variable: the hypotheses `[F.CommShift ℤ]` and `[F.IsTriangulated]` only elaborate once the full
subcategory is known to be pretriangulated, so the equality cannot be rewritten in the goal of a
statement already mentioning them. With the property a variable and its triangulatedness an
instance argument, `subst` is available and the two sides become the same statement. The
alternative — composing with `AlgebraicGeometry.smallAffineChaoticDerivedQuasiCoherentEquivQC` —
would need that equivalence's functor, which is `CategoryTheory.ObjectProperty.ιOfLE`, to carry a
`Functor.CommShift ℤ` and a `Functor.IsTriangulated`, and neither is available.

The index universe is `max (u + 1) w` for a scheme in `Scheme.{u}` and module universe `w`,
because the objects of the small affine Zariski site are objects of the big Zariski site and so
live in `Type (u + 1)`; this is also the morphism universe of `D(S_affine, 𝒪)`, which is what
Brown representability asks the direct sums to be indexed by.

## Coverage limits

Nothing here is a statement about `D_QCoh(𝒪_S)`, and in particular [Stacks, Tag 0A9E] does not
follow. Reaching `D_QCoh(𝒪_S)` needs the three comparisons (1) ≃ (2) ≃ (3) ≃ (4) of
Stacks 0GZZ, none of which is proved; and, before them, a presentation of the small affine
Zariski site whose objects and morphisms both live in `Type u`, since the morphisms of
`D_QCoh(𝒪_S)` live in `Type u` while those of `QC(S_affine, 𝒪)` live in `Type (max (u + 1) w)`
and `D_QCoh(𝒪_S)` does not have `Type (u + 1)`-indexed direct sums. The coverage note of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineSiteQuasiCoherentObjects.lean` records both in
detail.

## References

* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentCohomology

universe w u v r u'

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- **[Stacks, Tag 0GZ0] part (3), for a subcategory presented by an equal object property.**
Let `C` be a category with the chaotic topology, let `O` be a presheaf of commutative rings on
`C` and let `bc` be derived base-change data for `O`. If an object property `P` of `D(O)` cuts
out the same subcategory as the cartesian one of [Stacks, Tag 0GYV], then an exact functor
`F : P.FullSubcategory ⥤ D'` of triangulated categories which transforms direct sums into direct
sums has a right adjoint `G`, which is again exact.

This is
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_isTriangulated_rightAdjoint`
with the property substituted. -/
theorem exists_isTriangulated_rightAdjoint_of_eq (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    {P : ObjectProperty (DMod.{w} O)} [ObjectProperty.IsTriangulated P]
    (hP : (fun K ↦ IsQC.{w} bc K) = P)
    {D' : Type u'} [Category.{max u v r w} D'] [HasZeroObject D'] [Preadditive D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (F : P.FullSubcategory ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max u v r w), PreservesColimitsOfShape (Discrete α) F] :
    ∃ (G : D' ⥤ P.FullSubcategory) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated := by
  subst hP
  exact exists_isTriangulated_rightAdjoint.{w} bc hO F

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

namespace AlgebraicGeometry

open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

attribute [local instance] smallAffineChaotic_qcohCohomologyProperty_isTriangulated_univ

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **[Stacks, Tag 0GZ0] part (3) on `D_QCoh(S_affine, 𝒪)`.** Let `S` be a scheme and let
`(S_affine, 𝒪)` be its small affine Zariski site read with the chaotic topology. An exact functor
`F : D_QCoh(S_affine, 𝒪) ⥤ D'` of triangulated categories which transforms direct sums into
direct sums has a right adjoint `G`, which is again exact: the adjunction `F ⊣ G` is a
triangulated adjunction for a `Functor.CommShift ℤ` structure on `G`.

No hypothesis is carried: no compact generation, and no quasi-compactness or
quasi-separatedness. The two inputs are [Stacks, Tag 0GZ0] part (3) for the cartesian objects,
which is Brown representability without compact generation, and the identification of
`D_QCoh(S_affine, 𝒪)` with `QC(S_affine, 𝒪)`, which is the comparison (4) ≃ (5) of
[Stacks, Tag 0GZZ] in the sharp form
`AlgebraicGeometry.smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology`: on the chaotic site
the two subcategories of `D(S_affine, 𝒪)` are equal, not merely equivalent.

This is the abstract input of the Stacks proof of [Stacks, Tag 0A9E], but on the affine site;
nothing here is a statement about `D_QCoh(𝒪_S)`, and Tag 0A9E does not follow. See the coverage
note of this file. -/
@[stacks 0GZ0 "part (3) on D_QCoh(S_affine, 𝒪) of an arbitrary scheme, through the equality of \
that subcategory with QC(S_affine, 𝒪) which is the comparison (4) ≃ (5) of Stacks 0GZZ"]
theorem exists_isTriangulated_rightAdjoint_smallAffineChaoticDerivedQuasiCoherent
    {D' : Type u'} [Category.{max (u + 1) w} D'] [HasZeroObject D'] [Preadditive D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (F : (qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS)).FullSubcategory ⥤ D')
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max (u + 1) w), PreservesColimitsOfShape (Discrete α) F] :
    ∃ (G : D' ⥤
        (qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS)).FullSubcategory)
      (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_of_eq.{w} (smallAffineChaoticBaseChangeDataUniv.{w} B S hS)
    (mul_comm_smallAffineChaoticRingedSite_ringSheaf B S hS)
    (smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology.{w} B S hS
      (smallAffineChaoticBaseChangeDataUniv.{w} B S hS)) F

end AlgebraicGeometry

end
