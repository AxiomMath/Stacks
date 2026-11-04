module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Adequator
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSubsiteInjectives

/-!
# The diagram of Tag 06ZT

Let `U = Spec A` be affine. The proof of [Stacks, Tag 06ZS] displays the commutative diagram
[Stacks, Tag 06ZT]

`Adeq(𝒪) --k--> Mod((Aff/U)_τ, 𝒪) --j--> PMod((Aff/U)_τ, 𝒪)`, over `𝒜 --i--> 𝒫`,

with both vertical arrows identifications: the left one is [Stacks, Tag 06ZJ] and the right one
is the rule `F(B) = 𝓕(Spec B)` of [Stacks, Section 06US]. Here `𝒫` is the category of
module-valued functors on `Alg_A`, `𝒜` the adequate ones and `i` the inclusion; `k` is the
inclusion of adequate modules followed by the passage from `(Sch/U)_τ` to `(Aff/U)_τ` of
[Stacks, Tag 021V], and `j` is the inclusion of sheaves into presheaves. `Alg_A` is read, as
everywhere in this part of the library, as the `A`-algebras of the site, and `(Aff/U)_τ` as their
spectra with the topology restricted from the big site.

This file states every arrow of that diagram and its commutativity.

## Main definitions

* `Stacks.Adequate.adequateToAffineModules` — the functor `k`: an adequate module on the big site,
  restricted to `(Aff/U)_τ`, over the restriction of the structure sheaf.
* `Stacks.Adequate.affinePresheafModulesToModuleValued` — the right vertical arrow
  `PMod((Aff/U)_τ, 𝒪) → 𝒫`: restriction of scalars along the identification `B ≅ 𝒪(Spec B)`.
* `Stacks.Adequate.adequateDiagramSquare` — the commutativity of the diagram, at an arbitrary
  module universe.

## Main results

* `Stacks.Adequate.adequateAffineDiagram` — **[Stacks, Tag 06ZT], the whole diagram**: both
  vertical arrows are equivalences, the diagram commutes, `k` and `j` are fully faithful, the
  restriction `Mod((Sch/U)_τ, 𝒪) → Mod((Aff/U)_τ, 𝒪)` through which `k` factors is an
  equivalence, and the affine-spectrum functor is fully faithful with essential image the affine
  objects of the site.

## Implementation notes

The commutativity holds by definitional unfolding at every module universe. The two vertical
equivalences and the restriction equivalence are stated at the universe `u` of the site: the
identification of [Stacks, Tag 06ZJ] builds its quasi-inverse through `AlgebraicGeometry.tilde`,
which takes a `ModuleCat.{u} A`, and the restriction-of-scalars and comparison equivalences of the
library are stated with modules in the universe of the ring.

## References

* [Stacks Project, Tag 06ZT](https://stacks.math.columbia.edu/tag/06ZT)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06US](https://stacks.math.columbia.edu/tag/06US)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-! ### The arrows of the diagram -/

/-- The functor `k : Adeq(𝒪) → Mod((Aff/U)_τ, 𝒪)` of [Stacks, Tag 06ZT]: the inclusion of the
adequate modules followed by restriction to the spectra of the `A`-algebras of the site, over the
restriction of the structure sheaf. -/
public noncomputable def adequateToAffineModules :
    (adequate.{u, max u m} B).FullSubcategory ⥤
      SheafOfModules.{max u m} (DenseSubsiteModules.ringRestriction (affineSubsiteTopology B)
        B.topology (affineSpecOver B A (𝟙 (Spec A))) B.structureSheaf) :=
  (adequate.{u, max u m} B).ι ⋙ SheafOfModules.pushforward.{max u m} (𝟙 _)

/-- The right vertical arrow `PMod((Aff/U)_τ, 𝒪) → 𝒫` of [Stacks, Tag 06ZT], the rule
`F(B) = 𝓕(Spec B)` of [Stacks, Section 06US]: a presheaf of modules on the spectra of the
`A`-algebras of the site, read as a module-valued functor on those algebras through the
identification `B ≅ 𝒪(Spec B)` (`Stacks.Adequate.affineRingMap`). -/
public noncomputable def affinePresheafModulesToModuleValued :
    PresheafOfModules.{max u m} (DenseSubsiteModules.ringRestriction (affineSubsiteTopology B)
        B.topology (affineSpecOver B A (𝟙 (Spec A))) B.structureSheaf).obj ⥤
      AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) :=
  PresheafOfModules.restrictScalars (affineRingMap B A (𝟙 (Spec A)))

/-- **[Stacks, Tag 06ZT], the commutativity of the diagram**, at an arbitrary module universe:
`k`, then the inclusion `j` of sheaves into presheaves, then the right vertical arrow, is the left
vertical arrow (the comparison functor of [Stacks, Tag 06ZJ]) followed by the inclusion
`i : 𝒜 → 𝒫`. Both sides restrict sections to spectra and scalars along `B ≅ 𝒪(Spec B)`. -/
@[stacks 06ZT "the commutativity of the diagram, with k, j and the right vertical arrow
written out, at an arbitrary module universe"]
public noncomputable def adequateDiagramSquare :
    adequateToAffineModules.{u, m} B ⋙ SheafOfModules.forget _ ⋙
        affinePresheafModulesToModuleValued.{u, m} B ≅
      adequateComparison.{u, m} B ⋙ (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι :=
  Iso.refl _

/-- The functor `k` of [Stacks, Tag 06ZT] is fully faithful, at an arbitrary module universe:
the inclusion of adequate modules is, and so is restriction of sheaves of modules to the dense
subsite of spectra. -/
public noncomputable def fullyFaithfulAdequateToAffineModules :
    (adequateToAffineModules.{u, m} B).FullyFaithful :=
  (adequate.{u, max u m} B).fullyFaithfulι.comp
    (DenseSubsiteModules.fullyFaithfulPushforward.{u, max u m} (affineSubsiteTopology B)
      B.topology (affineSpecOver B A (𝟙 (Spec A))) (𝟙 _))

/-- **[Stacks, Tag 06ZT], the whole diagram.** For `U = Spec A` affine, in the diagram
`Adeq(𝒪) --k--> Mod((Aff/U)_τ, 𝒪) --j--> PMod((Aff/U)_τ, 𝒪)` over `𝒜 --i--> 𝒫`:

* the left vertical arrow `Adeq(𝒪) → 𝒜` is an equivalence ([Stacks, Tag 06ZJ]);
* the right vertical arrow `PMod((Aff/U)_τ, 𝒪) → 𝒫` is an equivalence ([Stacks, Section 06US]);
* the diagram commutes;
* `k` and `j` are fully faithful;
* the restriction `Mod((Sch/U)_τ, 𝒪) → Mod((Aff/U)_τ, 𝒪)` through which `k` factors is an
  equivalence ([Stacks, Tag 021V]);
* the affine-spectrum functor from the `A`-algebras of the site is fully faithful, with essential
  image exactly the affine objects of the site, so that its source is `(Aff/U)_τ`.

The commutativity and full-faithfulness conjuncts are wrapped in `Nonempty` because an
isomorphism of functors and a full-faithfulness witness are data while a conjunction needs a
proposition; asserting the diagram commutes is asserting such an isomorphism exists. -/
@[stacks 06ZT "the whole diagram: both vertical arrows are equivalences, it commutes, k and j
are fully faithful, and its middle category is modules on the affine objects of the site"]
public theorem adequateAffineDiagram :
    (adequateComparison.{u, u} B).IsEquivalence ∧
      (affinePresheafModulesToModuleValued.{u, u} B).IsEquivalence ∧
      Nonempty (adequateToAffineModules.{u, u} B ⋙ SheafOfModules.forget _ ⋙
          affinePresheafModulesToModuleValued.{u, u} B ≅
        adequateComparison.{u, u} B ⋙ (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι) ∧
      Nonempty (adequateToAffineModules.{u, u} B).FullyFaithful ∧
      Nonempty (SheafOfModules.forget.{u} (DenseSubsiteModules.ringRestriction
        (affineSubsiteTopology B) B.topology (affineSpecOver B A (𝟙 (Spec A)))
        B.structureSheaf)).FullyFaithful ∧
      (SheafOfModules.pushforward.{u} (𝟙 (DenseSubsiteModules.ringRestriction
        (affineSubsiteTopology B) B.topology (affineSpecOver B A (𝟙 (Spec A)))
        B.structureSheaf))).IsEquivalence ∧
      (affineSpecOver B A (𝟙 (Spec A))).Full ∧ (affineSpecOver B A (𝟙 (Spec A))).Faithful ∧
      ∀ X : B.category, IsAffine X.left.obj ↔ (affineSpecOver B A (𝟙 (Spec A))).essImage X :=
  ⟨isEquivalence_adequateComparison B,
    @Sheaves.RingedPoint.presheafRestrictScalars_isEquivalence _ _ _ _
      (affineRingMap B A (𝟙 (Spec A))) (affineRingMap_isIso B A _),
    ⟨adequateDiagramSquare.{u, u} B⟩, ⟨fullyFaithfulAdequateToAffineModules.{u, u} B⟩,
    ⟨SheafOfModules.fullyFaithfulForget _⟩,
    have := isEquivalence_affineSheafPushforwardContinuous.{u, u} B; inferInstance,
    inferInstance, inferInstance, isAffine_iff_mem_essImage_affineSpecOver B⟩

end Stacks.Adequate

end
