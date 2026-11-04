module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSheafTopology

/-!
# The abelian category of adequate modules, with no hypothesis

Let `S` be a scheme and `(Sch/S)_τ` a chosen big site over `S`, for `τ` any of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. This module states [Stacks, Tag 06VQ]:

1. the category `Adeq(𝒪)` of adequate `𝒪`-modules is abelian;
2. the inclusion `Adeq(𝒪) → Mod((Sch/S)_τ, 𝒪)` is exact;
3. the middle term of a short exact sequence of `𝒪`-modules with adequate outer terms is
   adequate (this clause is `Stacks.Adequate.isAdequate_of_shortExact`, in
   `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean`);
4. `Adeq(𝒪)` has colimits and the inclusion into all `𝒪`-modules commutes with them.

## Main results

* `Stacks.Adequate.abelian_adequate` — [Stacks, Tag 06VQ] (1).
* `Stacks.Adequate.exact_ι_adequate` — [Stacks, Tag 06VQ] (2).
* `Stacks.Adequate.hasColimits_adequate` — [Stacks, Tag 06VQ] (4).

## Implementation notes

The closure of adequacy under cokernels and under colimits, proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean`, takes as input the
hypothesis `Stacks.Adequate.AffineAdequateSheafTopology` of [Stacks, Tag 06VP]; here it is
discharged by `Stacks.Adequate.affineAdequateSheafTopology`, which lies above `Abelian.lean` in
the import order. Closure under cokernels is stated at every value universe `max u m`; the four
clauses are stated for `𝒪`-modules with values in the universe of the site, which is the
universe of the source's sets.

`Stacks.Adequate.abelian_adequate` produces the abelian structure itself rather than its
`Nonempty`, so that it can be installed with `letI`. It is the structure that
`CategoryTheory.ObjectProperty.abelian` builds from the closure properties, so its additive
structure is the `CategoryTheory.Preadditive.fullSubcategory` inherited from the sheaves of
modules on the site; it is not an `instance`, to keep a single path to that additive structure.

## References

* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### Cokernels and colimits of adequate modules -/

/-- A sheaf of modules isomorphic to the sheafification of a presheaf of modules with adequate
affine-section functors is adequate. -/
private theorem isAdequate_of_iso_sheafification
    (P : PresheafOfModules.{max u m} B.structureSheaf.obj)
    (G : SheafOfModules.{max u m} B.structureSheaf)
    (e : (sheafification.{u, m} B).obj P ≅ G)
    (hP : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S),
      schemeSizeBelow B.cutoff (Spec A) →
        AdequateFunctor.IsAdequate
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
          (presheafAffineSectionFunctor B P A f)) :
    IsAdequate B G :=
  (adequate.{u, max u m} B).prop_of_iso e
    (isAdequate_sheafification B (affineAdequateSheafTopology.{u, m} B) P _
      (toSheafification.{u, m} B _) inferInstance inferInstance hP)

/-- The cokernel of a map of adequate modules is adequate: the cokernel formed in the
presheaves of modules has adequate affine-section functors ([Stacks, Tag 06V2] on the algebras
of the site), and the sheaf cokernel is its sheafification, adequate by [Stacks, Tag 06VP]. -/
public theorem isAdequate_cokernel
    {F G : SheafOfModules.{max u m} B.structureSheaf} (φ : F ⟶ G)
    (hF : IsAdequate B F) (hG : IsAdequate B G) :
    IsAdequate B (cokernel φ) := by
  obtain ⟨e⟩ := cokernelIsSheafified.{u, m} B φ
  refine isAdequate_of_iso_sheafification.{u, m} B _ _ e fun A f hA => ?_
  refine (affineAdequateCokernels.{u, m} B A hA
    ((affineSectionsFunctor.{u, max u m} B A f).map φ)
    (affineLocalAdequacy.{u, m} B F hF A f hA)
    (affineLocalAdequacy.{u, m} B G hG A f hA)).of_iso ?_
  exact PreservesCokernel.iso (PresheafOfModules.pushforward (affineRingMap B A f))
    ((SheafOfModules.forget B.structureSheaf).map φ)

/-- Adequacy of sheaves of modules is closed under cokernels. -/
public theorem adequate_isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (adequate.{u, max u m} B) where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequate.{u, max u m} B).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (parallelPair φ 0)) hk)
      (isAdequate_cokernel B φ hF hG)

/-- A colimit of adequate `𝒪`-modules formed in all `𝒪`-modules on the site is adequate: the
colimit is
the sheafification of the colimit formed in presheaves of modules, whose affine-section functors
are colimits of adequate functors, adequate by [Stacks, Tag 06V4] on the algebras of the site
(`Stacks.Adequate.affineAdequateColimits`). -/
public theorem adequate_isClosedUnderColimitsOfShape
    (J : Type u)
    [Category.{u} J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (adequate.{u, u} B) J := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨K, hK⟩
  obtain ⟨e⟩ := colimitIsSheafified.{u, u} B J K
  refine isAdequate_of_iso_sheafification.{u, u} B _ _ e fun A f hA => ?_
  refine affineAdequateColimits.{u, u} B J A hA ((K ⋙ SheafOfModules.forget B.structureSheaf) ⋙
      PresheafOfModules.pushforward (affineRingMap B A f))
    ((PresheafOfModules.pushforward (affineRingMap B A f)).mapCocone (colimit.cocone _))
    (isColimitOfPreserves (PresheafOfModules.pushforward (affineRingMap B A f))
      (colimit.isColimit _))
    fun j => affineLocalAdequacy.{u, u} B (K.obj j) (hK j) A f hA

/-- **[Stacks, Tag 06VQ] (1).** The adequate `𝒪`-modules on the chosen big `τ`-site over `S`
form an abelian category: they contain the zero sheaf and are closed under kernels, cokernels
and finite products inside the abelian category of all sheaves of modules on the site. -/
@[stacks 06VQ "(1)", instance_reducible]
public noncomputable def abelian_adequate : Abelian (adequate.{u, u} B).FullSubcategory :=
  letI := adequate_isClosedUnderKernels.{u, u} B
  letI := adequate_isClosedUnderCokernels.{u, u} B
  letI := adequate_isClosedUnderFiniteProducts.{u, u} B
  letI : HasFiniteProducts (SheafOfModules.{u} B.structureSheaf) := inferInstance
  letI : HasFiniteCoproducts (SheafOfModules.{u} B.structureSheaf) := inferInstance
  letI : HasKernels (adequate.{u, u} B).FullSubcategory := inferInstance
  letI : HasCokernels (adequate.{u, u} B).FullSubcategory := inferInstance
  letI : HasFiniteProducts (adequate.{u, u} B).FullSubcategory := inferInstance
  inferInstance

/-- **[Stacks, Tag 06VQ] (2).** The inclusion of the adequate `𝒪`-modules into all `𝒪`-modules
on the chosen big `τ`-site over `S` is exact: it preserves finite limits and finite colimits,
kernels and cokernels of adequate modules being adequate. -/
@[stacks 06VQ "(2)"]
public theorem exact_ι_adequate :
    PreservesFiniteLimits (adequate.{u, u} B).ι ∧ PreservesFiniteColimits (adequate.{u, u} B).ι :=
  let := abelian_adequate B
  let := adequate_isClosedUnderKernels.{u, u} B
  let := adequate_isClosedUnderCokernels.{u, u} B
  have := (adequate.{u, u} B).preservesKernels_ι
  have := (adequate.{u, u} B).preservesCokernels_ι
  ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
    Functor.preservesFiniteColimits_of_preservesCokernels _⟩

/-- **[Stacks, Tag 06VQ] (4).** The category of adequate `𝒪`-modules on the chosen big
`τ`-site over `S` has all small colimits, and the inclusion into all `𝒪`-modules preserves them:
a colimit of adequate modules formed in all `𝒪`-modules is adequate. -/
@[stacks 06VQ "(4)"]
public theorem hasColimits_adequate :
    HasColimitsOfSize.{u, u} (adequate.{u, u} B).FullSubcategory ∧
      PreservesColimitsOfSize.{u, u} (adequate.{u, u} B).ι := by
  have h (J : Type u) [Category.{u} J] :
      (adequate.{u, u} B).IsClosedUnderColimitsOfShape J :=
    adequate_isClosedUnderColimitsOfShape B J
  exact ⟨⟨fun J _ => have := h J; inferInstance⟩,
    ⟨fun {J} _ => have := h J; inferInstance⟩⟩

end Stacks.Adequate

end
