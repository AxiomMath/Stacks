module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening

/-!
# Surjectivity of the unit of `i^* ⊣ i_*` for a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `G` be an `𝒪_X`-module.  The unit

`η_G : G ⟶ i_*i^*G`

of the adjunction of Stacks 03LU is, over a scheme, the projection of `G` onto `G/𝓘G` for
`𝓘 = ker(i^♯)` the ideal cutting out the closed subspace, hence an epimorphism.  The counit of
the same adjunction is an isomorphism for algebraic spaces — that is Stacks 04CJ, part (2),
proved as `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit` — but epimorphy of the
unit is a genuinely different assertion, and it is **not** proved here.

What is proved here is that it follows from a single named statement: the unproved half of the
essential-image clause of Stacks 04CJ, part (3), namely that an `𝒪_X`-module annihilated by `𝓘`
is a direct image along `i`.  Granted that, the unit is an epimorphism at every `𝒪_X`-module.

## Main results

* `CategoryTheory.Adjunction.epi_unit_app_of_isIso_unit_app_image`: a purely categorical
  criterion in an abelian category — if the unit of `L ⊣ R` is an isomorphism at the image of
  `η_A`, then `η_A` is an epimorphism.  No hypothesis on `R` is needed.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_mono`: annihilation by the ideal cutting out
  the closed subspace passes to submodules.
* `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_image`: the unit is an
  epimorphism at `G` as soon as the image of `η_G` is a direct image along `i`.
* `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated`:
  **the reduction.**  If every `𝒪_X`-module annihilated by `𝓘` is a direct image along `i`, then
  the unit of Stacks 03LU is an epimorphism at every `𝒪_X`-module.

## Implementation notes

**Why the image, and why that is the whole content.**  The image of `η_G` is a submodule of
`i_*i^*G`, which the ideal `𝓘` annihilates
(`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`); annihilation passes to
submodules, so the image is annihilated.  The categorical criterion then asks only that the unit
be invertible at the image, and for a fully faithful right adjoint invertibility of the unit at
an object is membership of the essential image
(`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`, available because
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` is proved).  So the hypothesis of the
reduction is exactly the missing implication.

**The categorical criterion.**  Write `η_A = p ≫ e` with `p` the factorization through the image
and `e` the image inclusion.  Naturality of `η` at `e` together with the two triangle identities
exhibits `R(L p) ≫ η_{im}⁻¹` as a section of `e`, so `e` is a split epimorphism; as `p` is an
epimorphism, so is `η_A`.  Only `Abelian` is used, and in particular the criterion says nothing
about which adjunction it is applied to.

**The obstruction this does not remove.**  The implication `𝓘M = 0 → M ∈ essImage i_*` is open
for algebraic spaces.  The two routes to it recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` are the
essential-image clause of Stacks 04E5 for sheaves of sets — equivalently the closed-subtopos
clause of `MorphismOfTopoi.IsClosedImmersion` (Stacks 08M0) for
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, whose embedding half is proved and whose
closed-subtopos half is not — and testing on stalks at geometric points.  Neither is pursued
below.

**The module universe** is `u`, the universe of the schemes: that is where
`AlgebraicGeometry.Space.modulePullbackAdjunction` and the abelian structure of
`AlgebraicGeometry.Space.Modules` live.

No `@[stacks]` attribute is carried.  Epimorphy of the unit is not a numbered assertion of the
Stacks Project — the source's part (1) of Stacks 04CJ is the stronger statement that
`G/𝓘G ≅ i_*i^*G`, which cannot even be stated in this library, the product `𝓘G` of an ideal
subsheaf with a module not being available — and the hypothesis of the reduction is a clause of
Stacks 04CJ, part (3) that is *not* proved, so tagging anything here would claim it.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

/-- **A categorical criterion for the unit of an adjunction to be an epimorphism.**  In an
abelian category, if the unit of `L ⊣ R` is an isomorphism at the image of `η_A`, then `η_A` is
an epimorphism.

Write `η_A = p ≫ e` with `p : A ⟶ im η_A` the factorization through the image and `e` the image
inclusion.  Naturality of `η` at `e`, together with the left triangle identity at `A` and the
right triangle identity at `L A`, shows that `R(L p) ≫ η_{im}⁻¹` is a section of `e`; so `e` is
a split epimorphism, and `η_A = p ≫ e` is a composite of two epimorphisms. -/
alias epi_unit_app_of_isIso_unit_app_image :=
  AlgebraicGeometry.RingedSpaceThickening.epi_unit_app_of_isIso_unit_app_image

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **Annihilation by the ideal cutting out a closed subspace passes to submodules**, and more
generally along any monomorphism of `𝒪_X`-modules: a monomorphism of sheaves of modules is
injective on the sections over every étale chart, so a section scaled to zero in the target was
scaled to zero already. -/
theorem annihilatedByKerIdeal_of_mono (i : Z ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) [Mono φ]
    (hN : AnnihilatedByKerIdeal B S hS i N) : AnnihilatedByKerIdeal B S hS i M := by
  intro U a ha m
  have hinj : Function.Injective (φ.val.app U) :=
    PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map φ) U
  exact hinj (((φ.val.app U).hom.map_smul a m).trans
    ((hN U a ha (φ.val.app U m)).trans (map_zero _).symm))

/-- **The unit of Stacks 03LU is an epimorphism at `G` as soon as the image of the unit is a
direct image along the closed immersion.**

This is `CategoryTheory.Adjunction.epi_unit_app_of_isIso_unit_app_image` for the adjunction of
Stacks 03LU, the invertibility of the unit at the image being membership of the essential image
of the fully faithful right adjoint
(`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`, Stacks 04CJ, part (2)). -/
theorem epi_modulePullbackAdjunction_unit_of_essImage_image (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (h : (modulePushforward B S hS i).essImage
      (Abelian.image ((modulePullbackAdjunction B S hS i).unit.app G))) :
    Epi ((modulePullbackAdjunction B S hS i).unit.app G) :=
  have := (fullyFaithfulModulePushforward B S hS i hi).full
  have := (fullyFaithfulModulePushforward B S hS i hi).faithful
  Adjunction.epi_unit_app_of_isIso_unit_app_image (modulePullbackAdjunction B S hS i) G
    ((modulePullbackAdjunction B S hS i).isIso_unit_app_iff_mem_essImage.2 h)

/-- **The reduction.**  If every `𝒪_X`-module annihilated by the ideal `𝓘 = ker(i^♯)` cutting out
the closed subspace is a direct image along `i` — the unproved half of the essential-image clause
of Stacks 04CJ, part (3) — then the unit `G ⟶ i_*i^*G` of Stacks 03LU is an epimorphism for
every `𝒪_X`-module `G`.

The image of the unit is a submodule of `i_*i^*G`, which `𝓘` annihilates by
`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`; annihilation passes to
submodules by `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_mono`, so the hypothesis applies
to it, and `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_image`
concludes. -/
theorem epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (hess : ∀ M : Modules.{u, u} B S hS X.1 X.2, AnnihilatedByKerIdeal B S hS i M →
      (modulePushforward B S hS i).essImage M)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    Epi ((modulePullbackAdjunction B S hS i).unit.app G) :=
  epi_modulePullbackAdjunction_unit_of_essImage_image B S hS i hi G
    (hess _ (annihilatedByKerIdeal_of_mono B S hS i
      (Abelian.image.ι ((modulePullbackAdjunction B S hS i).unit.app G))
      (annihilatedByKerIdeal_modulePushforward B S hS i
        ((modulePullback B S hS i).obj G))))

end AlgebraicGeometry.Space

end
