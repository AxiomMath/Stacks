module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.CoreflectionTransfer

/-!
# The adequator on the big site of an affine scheme

Let `U = Spec A` be affine. [Stacks, Tag 06ZS] asserts that the inclusion functor
`Adeq(𝒪) → Mod((Sch/U)_τ, 𝒪)` has a right adjoint `A`, the *adequator*, and moreover that the
adjunction mapping `A(𝓕) → 𝓕` is an isomorphism for every adequate module `𝓕`.

The source's proof is formal once three inputs are in place. Writing `𝒫` for the module-valued
functors on `Alg_A`, `𝒜` for the adequate ones, `i : 𝒜 → 𝒫` for the inclusion and `Q : 𝒫 → 𝒜`
for its right adjoint, the commutative diagram of [Stacks, Tag 06ZT]

`Adeq(𝒪) --k--> Mod((Aff/U)_τ, 𝒪) --j--> PMod((Aff/U)_τ, 𝒪)` over `𝒜 --i--> 𝒫`

identifies `k ⋙ j` with `i`, and then `A(𝓕) = Q(j(𝓕))` is right adjoint to `k` because `j` is
fully faithful. The final assertion follows from full faithfulness of `k`, which here is
automatic: `k` is the inclusion of a strictly full subcategory.

All three inputs are theorems of the library, `Alg_A` being read throughout as the
`A`-algebras of the site:

* the coreflection `i ⊣ Q` is [Stacks, Tag 06Z6] over the algebras of the site,
  `AdequateFunctor.adequateCoreflectionSiteAdjunction`;
* the identification of `Adeq(𝒪)` with `𝒜` is [Stacks, Tag 06ZJ],
  `Stacks.Adequate.isEquivalence_adequateComparison`, with the commuting square
  `Stacks.Adequate.adequateComparisonSquare`;
* full faithfulness of `j`, the affine-section functor, is
  `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`, which is where the passage from
  `(Sch/U)_τ` to `(Aff/U)_τ` of [Stacks, Tag 021V] enters.

## Main definitions

* `Stacks.Adequate.adequator` — the adequator `A = Q ∘ j` followed by the identification of `𝒜`
  with `Adeq(𝒪)`, for an arbitrary right adjoint `Q` and identification `E`, as a functor
  `Mod((Sch/U)_τ, 𝒪) ⥤ Adeq(𝒪)`, with `j` the affine-section functor.
* `Stacks.Adequate.affineAdequator` — the adequator of [Stacks, Tag 06ZS] itself, with `Q` and
  `E` the ones the library constructs.

## Main results

* `Stacks.Adequate.exists_adequator` — **[Stacks, Tag 06ZS]**, both assertions, with no
  hypothesis.
* `Stacks.Adequate.affineAdequatorAdjunction` and
  `Stacks.Adequate.isIso_affineAdequatorAdjunction_counit` — the two assertions for the named
  adequator `Stacks.Adequate.affineAdequator`.
* `Stacks.Adequate.adequatorAdjunction` and `Stacks.Adequate.isIso_adequatorAdjunction_counit` —
  the same two assertions for `Stacks.Adequate.adequator`, from any realization of the source's
  square; this is the generality in which [Stacks, Tag 06ZU] uses the adequator.
* `Stacks.Adequate.adequateComparisonSquare` — [Stacks, Tag 06ZT]: the square of the source's
  proof commutes, the comparison functor of [Stacks, Tag 06ZJ] being its left vertical arrow.
* `Stacks.Adequate.adequateAffineDiagram`, in
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AdequatorDiagram.lean` —
  **[Stacks, Tag 06ZT]** as a whole, with the middle category `Mod((Aff/U)_τ, 𝒪)`, the arrows
  `k` and `j` and the right vertical identification written out.

## Implementation notes

The statement of [Stacks, Tag 06ZS] is at the value universe `u` of the site, which is where
the identification [Stacks, Tag 06ZJ] is available: its quasi-inverse builds an adequate
`𝒪`-module as a kernel `Ker(M^a → N^a)` through `AlgebraicGeometry.tilde`, which takes a
`ModuleCat.{u} A`. The coreflection of [Stacks, Tag 06Z6] over the algebras of the site is
available at that universe too, because the algebras of the site form an essentially small
category (`AdequateFunctor.essentiallySmall_algebraInSite`), so that the special adjoint
functor theorem applies with values in `u`.

`Stacks.Adequate.adequator` and its adjunction keep `Q`, `E` and the square as parameters and an
independent value universe: the statement of [Stacks, Tag 06ZU] in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AdequatorVanishing.lean` is phrased in
that generality. `Stacks.Adequate.affineAdequator` is its instance at the library's `Q` and `E`.

## References

* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06ZT](https://stacks.math.columbia.edu/tag/06ZT)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06Z6](https://stacks.math.columbia.edu/tag/06Z6)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 07AH](https://stacks.math.columbia.edu/tag/07AH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m v₃ u₃ v₄ u₄

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-! ### The adequator of the affine-section functor -/

section

variable (Q : AdequateFunctor.ModuleValuedFunctorOn.{m}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ⥤
    (adequateOn.{u, m} A (schemeSizeBelow B.cutoff)).FullSubcategory)
  (E : (adequate.{u, m} B).FullSubcategory ≌
    (adequateOn.{u, m} A (schemeSizeBelow B.cutoff)).FullSubcategory)

/-- The adequator of [Stacks, Tag 06ZS] built from given data: the affine-section functor `j`
into the module-valued functors on the `A`-algebras of the site, followed by a functor `Q` from
those to the adequate ones, followed by an identification `E` of the adequate ones with
`Adeq(𝒪)`. With the library's `Q` and `E` this is `Stacks.Adequate.affineAdequator`. -/
public noncomputable def adequator :
    SheafOfModules.{m} B.structureSheaf ⥤ (adequate.{u, m} B).FullSubcategory :=
  affineSectionsFunctor.{u, m} B A (𝟙 (Spec A)) ⋙ Q ⋙ E.inverse

variable (adj : (adequateOn.{u, m} A (schemeSizeBelow B.cutoff)).ι ⊣ Q)
  (hj : (affineSectionsFunctor.{u, m} B A (𝟙 (Spec A))).FullyFaithful)
  (comm : E.functor ⋙ (adequateOn.{u, m} A (schemeSizeBelow B.cutoff)).ι ≅
    (adequate.{u, m} B).ι ⋙ affineSectionsFunctor.{u, m} B A (𝟙 (Spec A)))

/-- The argument of [Stacks, Tag 06ZS] for given data: if `Q` is right adjoint to the inclusion
of the adequate module-valued functors, the affine-section functor is fully faithful and the
square through `E` commutes, then `Stacks.Adequate.adequator` is a right adjoint of the inclusion
`Adeq(𝒪) → Mod((Sch/U)_τ, 𝒪)`: the adjunction `i ⊣ Q` transfers across the square. -/
public noncomputable def adequatorAdjunction :
    (adequate.{u, m} B).ι ⊣ adequator B Q E :=
  Adjunction.transferAlongEquivalence _ (affineSectionsFunctor.{u, m} B A (𝟙 (Spec A))) E
    adj hj comm

/-- The "moreover" clause of [Stacks, Tag 06ZS] for given data: the counit of
`Stacks.Adequate.adequatorAdjunction` at an adequate `𝓕` is an isomorphism. An adequate `𝓕` is
the image of an object of `Adeq(𝒪)` under a fully faithful left adjoint, where the counit is
always invertible. -/
public theorem isIso_adequatorAdjunction_counit (F : SheafOfModules.{m} B.structureSheaf)
    (hF : IsAdequate B F) :
    IsIso ((adequatorAdjunction B Q E adj hj comm).counit.app F) :=
  inferInstanceAs (IsIso ((adequatorAdjunction B Q E adj hj comm).counit.app
    ((adequate.{u, m} B).ι.obj ⟨F, hF⟩)))

end

/-! ### The commutative square of the source's proof -/

/-- **[Stacks, Tag 06ZT]**, the commutative square in the proof of [Stacks, Tag 06ZS]: the
inclusion of `Adeq(𝒪)` followed by the affine-section functor into the module-valued functors on
the `A`-algebras of the site equals the comparison functor of [Stacks, Tag 06ZJ] followed by the
inclusion of the adequate module-valued functors. It commutes by definitional unfolding, which
is `Stacks.Adequate.adequateComparison_ι`. -/
@[stacks 06ZT "the commutativity of the square, with the comparison functor of Tag 06ZJ
as its left vertical arrow; that it is an identification is
`Stacks.Adequate.isEquivalence_adequateComparison`"]
public noncomputable def adequateComparisonSquare :
    adequateComparison.{u, m} B ⋙ (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, max u m} B).ι ⋙ affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A)) :=
  eqToIso (adequateComparison_ι.{u, m} B)

add_to_stacks 06ZT "the left vertical arrow of the square is an identification; the source reads
it off Tag 06ZJ, and this is that tag" isEquivalence_adequateComparison

/-! ### The adequator of Tag 06ZS -/

section Unconditional

/-- The cutoff of a chosen big site over an affine scheme is uncountable: it exceeds the size
of the base, which is infinite. -/
public theorem BigSite.aleph0_lt_cutoff_of_affine : Cardinal.aleph0 < B.cutoff :=
  lt_of_le_of_lt (Scheme.aleph0_le_size (Spec A)) B.base_mem

/-- The right adjoint `Q` of the inclusion of the adequate module-valued functors on the
`A`-algebras of the site, [Stacks, Tag 06Z6] over those algebras. -/
public noncomputable def siteAdequateCoreflection :
    AdequateFunctor.ModuleValuedFunctorOn.{u}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ⥤
      (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
  AdequateFunctor.adequateCoreflectionSite (BigSite.aleph0_lt_cutoff_of_affine B)
    B.cutoff_isStrongPrelimit B.base_mem

/-- The adjunction `i ⊣ Q` of [Stacks, Tag 06Z6] over the `A`-algebras of the site. -/
public noncomputable def siteAdequateCoreflectionAdjunction :
    (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι ⊣ siteAdequateCoreflection B :=
  AdequateFunctor.adequateCoreflectionSiteAdjunction (BigSite.aleph0_lt_cutoff_of_affine B)
    B.cutoff_isStrongPrelimit B.base_mem

/-- The identification `E` of `Adeq(𝒪)` with the adequate module-valued functors on the
`A`-algebras of the site: the comparison functor of [Stacks, Tag 06ZJ], which is an
equivalence by `Stacks.Adequate.isEquivalence_adequateComparison`. -/
public noncomputable def adequateComparisonEquivalence :
    (adequate.{u, u} B).FullSubcategory ≌
      (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
  @Functor.asEquivalence _ _ _ _ (adequateComparison.{u, u} B)
    (isEquivalence_adequateComparison B)

/-- **The adequator of [Stacks, Tag 06ZS].** For `U = Spec A` affine, the functor
`A = Q ∘ j : Mod((Sch/U)_τ, 𝒪) ⥤ Adeq(𝒪)`, with `j` the affine-section functor, `Q` the right
adjoint of [Stacks, Tag 06Z6] over the algebras of the site and `Adeq(𝒪)` identified with the
adequate module-valued functors by [Stacks, Tag 06ZJ]. -/
public noncomputable def affineAdequator :
    SheafOfModules.{u} B.structureSheaf ⥤ (adequate.{u, u} B).FullSubcategory :=
  adequator.{u, u} B (siteAdequateCoreflection B) (adequateComparisonEquivalence B)

/-- **[Stacks, Tag 06ZS], the right adjoint.** For `U = Spec A` affine, the adequator is a right
adjoint of the inclusion `Adeq(𝒪) → Mod((Sch/U)_τ, 𝒪)`. -/
public noncomputable def affineAdequatorAdjunction :
    (adequate.{u, u} B).ι ⊣ affineAdequator B :=
  adequatorAdjunction.{u, u} B (siteAdequateCoreflection B) (adequateComparisonEquivalence B)
    (siteAdequateCoreflectionAdjunction B) (fullyFaithfulAffineSectionsFunctor B)
    (adequateComparisonSquare.{u, u} B)

/-- **[Stacks, Tag 06ZS], the "moreover" clause.** The adjunction mapping `A(𝓕) → 𝓕` of the
adequator is an isomorphism for every adequate `𝓕`. -/
public theorem isIso_affineAdequatorAdjunction_counit (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) : IsIso ((affineAdequatorAdjunction B).counit.app F) :=
  isIso_adequatorAdjunction_counit.{u, u} B _ _ _ _ _ F hF

/-- **[Stacks, Tag 06ZS].** Let `U = Spec A` be an affine scheme. The inclusion functor
`Adeq(𝒪) → Mod((Sch/U)_τ, 𝒪)` has a right adjoint, and the adjunction mapping `A(𝓕) → 𝓕` is
an isomorphism for every adequate module `𝓕`.

The right adjoint is `Stacks.Adequate.affineAdequator`, with adjunction
`Stacks.Adequate.affineAdequatorAdjunction`. -/
@[stacks 06ZS]
public theorem exists_adequator :
    ∃ (R : SheafOfModules.{u} B.structureSheaf ⥤ (adequate.{u, u} B).FullSubcategory)
      (adjR : (adequate.{u, u} B).ι ⊣ R),
      ∀ F : SheafOfModules.{u} B.structureSheaf, IsAdequate B F → IsIso (adjR.counit.app F) :=
  ⟨affineAdequator B, affineAdequatorAdjunction B, isIso_affineAdequatorAdjunction_counit B⟩

end Unconditional

end Stacks.Adequate

end
