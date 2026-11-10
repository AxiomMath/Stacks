module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityFromSizeBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianBrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementExists
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Brown representability for cartesian objects

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
commutative rings on `C` and let `bc` be derived base-change data for `O`. Stacks 0GZ0 asserts
four things about the subcategory `QC(O) ⊆ D(O)` of cartesian objects of Stacks 0GYV:

1. it is a strictly full, saturated, triangulated subcategory closed under arbitrary direct sums;
2. a contravariant cohomological functor on `QC(O)` which transforms direct sums into products is
   representable;
3. an exact functor out of `QC(O)` which transforms direct sums into direct sums has an exact
   right adjoint;
4. in particular the inclusion `QC(O) ⥤ D(O)` has an exact right adjoint.

Part (1) is Stacks 0GYW, the four instances
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms`,
`isQC_isSaturated`, `isQC_isTriangulated` and `isQC_isClosedUnderColimitsOfShape`. This file proves
parts (2), (3) and (4), for `O` with commutative sections.

The proof combines two results. Stacks 0GYZ, the theorem
`exists_cardinal_small_nonzero_map_and_factorization` of this namespace, produces a cardinal `κ`
such that nonzero morphisms and factorizations of maps into countable direct sums can be found
through cartesian objects of size at most `κ`; weak Brown representability, Stacks 0GYG, and its
adjoint form, Stacks 0GYH, apply to a *family* of objects with those two properties. The passage
from the cardinal to the family is
`QuasiCoherentEquivalence.exists_small_qc_family_of_derivedObjectSize_le`.

## Main results

All in the namespace `Stacks.ModulesOnACategory.QuasiCoherentEquivalence`:

* `exists_small_generating_family` — the generating family of Stacks 0GYG for `QC(O)`.
* `exists_iso_preadditiveYoneda_of_isHomological_unconditional` — **Stacks 0GZ0 part (2)**.
* `exists_isTriangulated_rightAdjoint` — **Stacks 0GZ0 part (3)**.
* `exists_isTriangulated_rightAdjoint_QCι` — **Stacks 0GZ0 part (4)**.

## Implementation notes

The two results speak about different direct sums. Stacks 0GYZ states its factorization
conclusion with the direct sums of the *ambient* `D(O)`, because that is where the size function
`derivedObjectSize` lives, while Stacks 0GYG asks for a factorization of a morphism into a direct
sum formed *inside* `QC(O)`. The inclusion preserves direct sums — `QC(O)` is closed under them
by Stacks 0GYW — so the comparison morphism `CategoryTheory.Limits.sigmaComparison (QCι bc)` is
invertible, and `CategoryTheory.Limits.sigmaComparison_naturality` carries the factorization
across.

The hypothesis `hO` that the sections of `O` commute is that of
`exists_cardinal_small_nonzero_map_and_factorization` (Stacks 0GYZ). The cardinal `κ` appears in
no statement.

## References

* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r u'

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}} (bc : BaseChangeData.{w} O)

/-! ### Direct sums of cartesian objects, inside and outside `QC(O)` -/

/-- The inclusion `QC(O) ⥤ D(O)` preserves direct sums, `QC(O)` being closed under them
(Stacks 0GYW). Supplied explicitly: instance search times out finding it. -/
private lemma qcι_preservesColimitsOfShape_discrete' (J : Type*)
    [HasColimitsOfShape (Discrete J) (DMod.{w} O)] :
    PreservesColimitsOfShape (Discrete J) (QCι.{w} bc) :=
  preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _

attribute [local instance] qcι_preservesColimitsOfShape_discrete'

set_option synthInstance.maxHeartbeats 400000 in
-- synthesizing `IsIso (sigmaComparison _ K)` goes through the colimit instances of `QCι`
/-- **The direct sum of cartesian objects is their direct sum in `D(O)`.** `QC(O)` is closed under
direct sums ([Stacks, Tag 0GYW]), so the inclusion preserves them and the comparison morphism from
the direct sum of the underlying objects to the underlying object of the direct sum is
invertible. -/
instance isIso_sigmaQCComparison (K : ℕ → QC.{w} bc) :
    IsIso (sigmaComparison (QCι.{w} bc) K) :=
  isIso_sigmaComparison_of_preservesColimit _ K inferInstance

/-! ### The generating family of Stacks 0GYG -/

/-- **`QC(O)` has a generating family in the sense of [Stacks, Tag 0GYG].** There is a family
`E : ι → QC(O)`, indexed by a type of the module universe, such that every nonzero cartesian
object receives a nonzero morphism from some `E i`, and such that every morphism from some `E i`
into a countable direct sum `∐ X` of cartesian objects factors as a direct sum of morphisms
`E (j n) ⟶ X n` preceded by a morphism `E i ⟶ ∐ₙ E (j n)`.

This is [Stacks, Tag 0GYZ] converted from a bound on a *cardinal* to an indexed *family*: the
cartesian objects of size at most `κ` are, up to isomorphism, the members of a small family
(`exists_small_qc_family_of_derivedObjectSize_le` of this namespace),
and the two conclusions of 0GYZ transport along those isomorphisms. The factorization conclusion
of 0GYZ is stated for the direct sums of `D(O)`; it is carried to the direct sums of `QC(O)` by
the invertibility of `CategoryTheory.Limits.sigmaComparison (QCι bc)` and its naturality. -/
alias exists_small_generating_family := exists_qc_generating_family

/-! ### Stacks 0GZ0 -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for the triangulated structure on `QC(O)` and `D(O)` is deep
/-- **[Stacks, Tag 0GZ0] part (2).** Let `C` be a category with the chaotic topology, let `O` be a
presheaf of commutative rings on `C` and let `bc` be derived base-change data for `O`. Every
contravariant cohomological functor on `QC(O)` which transforms direct sums into products is
representable.

This is weak Brown representability [Stacks, Tag 0GYG] applied to the generating family
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_small_generating_family`, which is
[Stacks, Tag 0GYZ]. -/
@[stacks 0GZ0 "part (2), for a presheaf of commutative rings"]
theorem exists_iso_preadditiveYoneda_of_isHomological_unconditional
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    (H : (QC.{w} bc)ᵒᵖ ⥤ AddCommGrpCat.{max u v r w}) [H.IsHomological]
    [∀ J : Type (max u v r w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{w} bc, Nonempty (preadditiveYoneda.obj K ≅ H) := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_small_generating_family.{w} bc hO
  exact exists_iso_preadditiveYoneda_of_isHomological_of_generating.{w} bc E hE hE' H

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for the triangulated structure on `QC(O)` and `D(O)` is deep
/-- **[Stacks, Tag 0GZ0] part (3).** Let `C` be a category with the chaotic topology, let `O` be a
presheaf of commutative rings on `C` and let `bc` be derived base-change data for `O`. An exact
functor `F : QC(O) ⥤ D'` of triangulated categories which transforms direct sums into direct sums
has a right adjoint `G`, which is again exact: the adjunction `F ⊣ G` is a triangulated adjunction
for a `Functor.CommShift ℤ` structure on `G`.

This is Brown representability in the form [Stacks, Tag 0GYH] applied to the generating family
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_small_generating_family`, which is
[Stacks, Tag 0GYZ]. -/
@[stacks 0GZ0 "part (3), for a presheaf of commutative rings"]
theorem exists_isTriangulated_rightAdjoint
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    {D' : Type u'} [Category.{max u v r w} D'] [HasZeroObject D'] [Preadditive D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (F : QC.{w} bc ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max u v r w), PreservesColimitsOfShape (Discrete α) F] :
    ∃ (G : D' ⥤ QC.{w} bc) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_small_generating_family.{w} bc hO
  exact Pretriangulated.exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma
    F E hE hE'

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for the triangulated structure on `QC(O)` and `D(O)` is deep
/-- **[Stacks, Tag 0GZ0] part (4).** The inclusion `QC(O) ⥤ D(O)` of the cartesian objects has an
exact right adjoint. The inclusion is exact and transforms direct sums into direct sums, because
`QC(O)` is a triangulated subcategory closed under direct sums ([Stacks, Tag 0GYW]), so this is the
special case `F = QCι` of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_isTriangulated_rightAdjoint`. -/
@[stacks 0GZ0 "part (4), for a presheaf of commutative rings"]
theorem exists_isTriangulated_rightAdjoint_QCι
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ (G : DMod.{w} O ⥤ QC.{w} bc) (adj : QCι.{w} bc ⊣ G) (_ : G.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint.{w} bc hO (QCι.{w} bc)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
