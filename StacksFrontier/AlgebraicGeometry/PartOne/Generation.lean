module

public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic

/-!
# The conclusion of [Stacks, Tag 01PW] generates, over the open it is stated on

The conclusion of [Stacks, Tag 01PW] is an equation `τ|_V = m ⊗ σ|_V` between a global section
`τ` of `F ⊗ P` and the product of a section `m` of `F` over `V` with the restriction of a global
section `σ` of `P`. If `m` and `σ|_V` generate sectionwise over `V`, then `τ` alone generates
`F ⊗ P` over `V`. Two inputs enter:

* `Stacks.TensorSectionProduct.exists_smul_germ_tensorSection`: if `m` generates `F` and `n`
  generates `G` sectionwise over an open, the germ of
  `Stacks.SectionTensorFormula.tensorSection F G m n` generates the stalk of `F ⊗ G` at every
  point of it;
* `Stacks.FinGenFromCover.exists_ringStalk_smul_eq`, which converts a scalar of the stalk acting
  through `Stacks.ModuleStalk.stalkModule` into one of the `RingCat`-valued stalk over which the
  span of `Stacks.AmpleLocalGeneration.IsFinGenOn` is taken.

## Main results

* `Stacks.Tag01PWPartOne.isFinGenOn_of_resTop_eq_tensorSection`: **a single global section whose
  restriction is a product of two sectionwise generators generates over that open.** This is the
  conclusion of [Stacks, Tag 01PW] — an equation `τ|_V = m ⊗ σ|_V` — turned into
  `Stacks.AmpleLocalGeneration.IsFinGenOn (F ⊗ P) V`, with a one-element family.
* `Stacks.Tag01PWPartOne.isFinGenOn_of_resTop_eq_tensorSection_of_le_nonvanishingOpen`: the same
  with the hypothesis on the twisting factor discharged from invertibility, by
  `Stacks.NonvanishingSpelling.bijective_smul`: inside `X_σ` a nonvanishing global section of an
  invertible module *is* a sectionwise generator.

## Implementation notes

For a quasi-coherent `𝓕` of finite type the generators of `𝓕` over an affine `X_s` are finitely
many sections `mⱼ`, and the lemmas below apply once per `j`, each with its own twist `pⱼ`; for an
invertible `𝓕` — the coefficient of part (1) of [Stacks, Tag 0892] and of part (2) of
[Stacks, Tag 087S] — there is a single generator.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.Ample
open Stacks.SectionExtension (resTop)
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe u

namespace Stacks.Tag01PWPartOne

section Generation

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-- **The conclusion of [Stacks, Tag 01PW] generates over the open it is stated on.** Let `τ` be a
global section of `F ⊗ P` whose restriction to `V` is the product of a section `m` of `F` over `V`
with the restriction of a global section `σ` of `P`, and suppose `m` and `σ|_V` are *sectionwise
generators* over `V` — every section of `F`, resp. of `P`, over an open inside `V` is a multiple of
the restriction of `m`, resp. of `σ|_V`. Then `τ` alone generates `F ⊗ P` over `V`.

The germ of the product generates the stalk by
`Stacks.TensorSectionProduct.exists_smul_germ_tensorSection`, and the resulting
`𝒪_{X,x}`-scalar is converted into a scalar over the `RingCat`-valued stalk — the ring the span of
`Stacks.AmpleLocalGeneration.IsFinGenOn` is taken over — by
`Stacks.FinGenFromCover.exists_ringStalk_smul_eq`. The proof is the one of
`Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus` with the rank-one Nakayama step
replaced by the product. -/
theorem isFinGenOn_of_resTop_eq_tensorSection (F P : X.Modules) {V : X.Opens} (m : Γ(F, V))
    (σ : Γ(P, ⊤)) (τ : Γ((F ⊗ P : X.Modules), ⊤))
    (hF : ∀ (U : X.Opens) (i : U ⟶ V) (u : Γ(F, U)),
      ∃ r : Γ(X, U), u = r • F.presheaf.map i.op m)
    (hP : ∀ (U : X.Opens) (i : U ⟶ V) (u : Γ(P, U)),
      ∃ r : Γ(X, U), u = r • P.presheaf.map i.op (resTop V σ))
    (heq : resTop V τ = Stacks.SectionTensorFormula.tensorSection F P m (resTop V σ)) :
    Stacks.AmpleLocalGeneration.IsFinGenOn (F ⊗ P) V := by
  refine ⟨PUnit.{u + 1}, fun _ => τ, inferInstance, fun x hx => eq_top_iff.mpr fun w _ => ?_⟩
  obtain ⟨r, hr⟩ := Stacks.TensorSectionProduct.exists_smul_germ_tensorSection
    (F := F) (G := P) m (resTop V σ) hF hP hx w
  rw [← heq, resTop, TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u})] at hr
  obtain ⟨r', hr'⟩ := Stacks.FinGenFromCover.exists_ringStalk_smul_eq (F ⊗ P : X.Modules) x r
    (((F ⊗ P : X.Modules).presheaf.Γgerm x).hom τ)
  rw [hr, hr']
  exact Submodule.smul_mem _ r' (Submodule.subset_span ⟨PUnit.unit, rfl⟩)

/-- **The same, with the twisting factor's generation hypothesis discharged.** For `P` invertible
and `V` inside the nonvanishing open of `σ`, the restriction `σ|_V` is a sectionwise generator of
`P` over `V`: that is the trivialization clause of [Stacks, Tag 01CY],
`Stacks.NonvanishingSpelling.bijective_smul`. So the conclusion of [Stacks, Tag 01PW] — which
always comes with `V = X_σ` — needs only the generation hypothesis on the *coefficient*. -/
theorem isFinGenOn_of_resTop_eq_tensorSection_of_le_nonvanishingOpen (F P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] {V : X.Opens} (m : Γ(F, V)) (σ : Γ(P, ⊤))
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X P σ)
    (τ : Γ((F ⊗ P : X.Modules), ⊤))
    (hF : ∀ (U : X.Opens) (i : U ⟶ V) (u : Γ(F, U)),
      ∃ r : Γ(X, U), u = r • F.presheaf.map i.op m)
    (heq : resTop V τ = Stacks.SectionTensorFormula.tensorSection F P m (resTop V σ)) :
    Stacks.AmpleLocalGeneration.IsFinGenOn (F ⊗ P) V := by
  refine isFinGenOn_of_resTop_eq_tensorSection F P m σ τ hF (fun U i u => ?_) heq
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul X P σ
    ((leOfHom i).trans hV)).surjective u
  refine ⟨a, ?_⟩
  rw [← ha, Stacks.TensorSectionProduct.map_map]
  rfl

end Generation

end Stacks.Tag01PWPartOne

end
