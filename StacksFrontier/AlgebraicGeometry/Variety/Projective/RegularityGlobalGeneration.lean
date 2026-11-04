module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionFiniteFamily
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistAsTensorPower
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Projective
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplication

/-!
# A regular sheaf is globally generated after its own twist: the descent step

Let `k` be a field, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_k`. [Stacks, Tag 08A8] says that if
`ℱ` is `m`-regular then `ℱ(m)` is globally generated, and its proof is a descent: the twists of
`ℱ` are globally generated far out, and one steps down from `ℱ(d + 1)` to `ℱ(d)` for every
`d ≥ m`. This file proves the single step of that descent, from the conclusion of
[Stacks, Tag 08A7] at `d`; the tag itself is
`AlgebraicGeometry.isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_field` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/RegularityGlobalGenerationUnconditional.lean`,
which iterates the step downwards and supplies [Stacks, Tag 08A7] from `m`-regularity alone.

## Main definitions

* `AlgebraicGeometry.sectionOfTop` reads a section over `⊤` as a compatible family of sections.
* `AlgebraicGeometry.mulSectionOne` is multiplication by a global section of `𝒪(1)` as a map
  `ℳ ⟶ ℳ ⊗ 𝒪(1)`, the half of
  `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul` that is
  natural in `ℳ`.
* `AlgebraicGeometry.twistGeneratingHom` is the map to `ℱ(m)` from the free module on all of its
  global sections; global generation of `ℱ(m)` is exactly that this map is an epimorphism.

## Main results

* `AlgebraicGeometry.epi_of_isGeneratedByGlobalSections_of_surjective`: a map onto a globally
  generated module which is onto global sections is an epimorphism.
* `AlgebraicGeometry.twistSectionMul_eq_mulSectionOne_comp` and
  `AlgebraicGeometry.mulSectionOne_naturality`: the two halves of `twistSectionMul`, and the
  naturality of the first.
* `AlgebraicGeometry.tensorRightOfUnitHom_eq_whiskerLeft` and
  `AlgebraicGeometry.mulSectionOne_eq_rightUnitor_inv_comp`: `AlgebraicGeometry.mulSectionOne`
  read as the inverse of the right unit constraint followed by the whiskering of
  `…ProjectiveSpaceSectionFiniteFamily.tensorMonoidal`, which is the shape its consumers argue
  with.
* `AlgebraicGeometry.mulSectionOne_eq_mulRight_comp`: `AlgebraicGeometry.mulSectionOne` is
  `Stacks.TensorSectionNonvanishing.mulRight` followed by the comparison of the two tensor
  products.
* `AlgebraicGeometry.isGeneratedByGlobalSections_projectiveTwist_of_span_mulSections`: the
  descent step — if the products of global sections of `ℱ(m)` with degree-one forms span
  `H⁰(ℙⁿ_k, ℱ(m + 1))` and `ℱ(m + 1)` is globally generated, then `ℱ(m)` is globally generated.

## The mathematics of the descent step

Write `π : ⨁_{Γ(ℱ(m))} 𝒪 ⟶ ℱ(m)` for `twistGeneratingHom`, the map from the free module on all
global sections of `ℱ(m)`; global generation is `Epi π`. Twisting by one and composing with the
comparison `(ℱ(m)) ⊗ 𝒪(1) ≅ ℱ(m + 1)` gives `ψ`, and `Epi ψ` is equivalent to `Epi π` because
the twist is an equivalence of categories.

On `H⁰`, multiplication by a linear form commutes with `π`, so every product `s · a` of a global
section `a` of `ℱ(m)` with a linear form `s` lies in the image of `H⁰(ψ)`. By
[Stacks, Tag 08A7] those products span `H⁰(ℙⁿ_k, ℱ(m + 1))` — this is the one place
`m`-regularity is used in the step — so `H⁰(ψ)` is surjective. Since `ℱ(m + 1)` is globally
generated and `ψ` is onto global sections, `ψ` is an epimorphism, hence so is `π`.

Stepping down from a twist that is known to be globally generated to `ℱ(m)` then needs
`ℱ` to be `d`-regular at every `d` passed through, which is [Stacks, Tag 08A6]; that iteration
belongs to the file that assembles the tag, not to the step proved here.

## Why the span is a parameter of the step

`m`-regularity enters the step of the descent in exactly one place: it is what makes the
products of global sections of `ℱ(m)` with degree-one forms span `H⁰(ℙⁿ_k, ℱ(m + 1))`. That span
statement is [Stacks, Tag 08A7], and the form of it that needs nothing beyond `m`-regularity,
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_field`, is proved downstream of this
file, since its reduction to an infinite base field goes through the multiplication maps of
`StacksFrontier/AlgebraicGeometry/Variety/Projective/RegularitySectionMultiplicationFieldDescent.lean`
(built from `AlgebraicGeometry.mulSectionOne` below). So the step takes the span as a
parameter and the file that assembles [Stacks, Tag 08A8] discharges it from `m`-regularity.

## Implementation notes

**Global sections, twice over.** Two spellings of "global section" meet here.
`SheafOfModules.GeneratingSections`, and hence
`SheafOfModules.IsGeneratedByGlobalSections`, is stated with `SheafOfModules.sections`, a
compatible family over all opens; [Stacks, Tag 08A7] is stated with
`AlgebraicGeometry.cohomologyOverField` in degree zero, which
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` identifies with `Γ(ℱ, ⊤)`.
`AlgebraicGeometry.sectionOfTop` bridges the two: a section over `⊤` restricts to every open,
and that is inverse to evaluation at `⊤` because the opens form a poset, so no two restriction
arrows out of `⊤` differ. Because the identification with `H⁰` is only an `Equiv` and not
`k`-linear, the span statement of Tag 08A7 is used on the `H⁰` side and only surjectivity is
transported across.

**Why multiplication is split in two.** `twistSectionMul` is `ℱ(d) ⟶ ℱ(d + 1)`, and it is
natural in `ℱ`, not in `ℱ(d)`; the naturality needed here is in the whole of `ℱ(d)`, since the
free module takes the place of `ℱ(d)`. `mulSectionOne` is the first half, which is natural in
the module it starts from and needs only the right unitor and the interchange law, while
`twistAssocIso` is the second half, which reassociates. No coherence for `twistOverMulIso`
beyond its being an isomorphism is needed.

**Why `twistAssocIso` is not `projectiveTwistAddIso`.** The general degree additivity
`(ℱ(a))(b) ≅ ℱ(a + b)` is `Stacks.ProjectiveSpace.projectiveTwistAddIso`, and at `b = 1` it has
the same type as `twistAssocIso`. The two are not the same term: `projectiveTwistAddIso`
regroups with the associator of `Stacks.SheafInternalHom.schemeMonoidalCategory`, which is the
*localized* monoidal structure `Stacks.SheafOfModules.monoidalCategory` and whose tensor product
reaches `tensorModules` only across `Stacks.AmplePullbackPart1.tensorIsoTensorModules`, whereas
`twistAssocIso` is literally the last two factors of `twistSectionMul`, built from
`Stacks.SheafOfModules.Invertible.tensorProductAssociator`, the associator of
`Stacks.SheafOfModules.sheafTensorStruct`. That is what makes
`twistSectionMul_eq_mulSectionOne_comp` hold by `rfl`; with `projectiveTwistAddIso` in its place
the factorization is not definitional, and establishing it would mean proving the two
associators agree under `tensorIsoTensorModules` — a coherence comparison of the two monoidal
structures on `X.Modules`, which this file does not need.

**Why `mulSectionOne` needs a lemma to be read as a whiskering.** `mulSectionOne` tensors with
the section through
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom`, which is
the *uncurried* tensor bifunctor at the pair `(𝟙 ℳ, f)`. By the definition of
`CategoryTheory.Functor.uncurry` that is the bifunctor's value at `𝟙 ℳ` followed by the
whiskering, and the leading factor is an identity only by `CategoryTheory.Functor.map_id` — a
propositional equation, not a definitional one. So `mulSectionOne` is *not* definitionally
`(ρ_ ℳ).inv ≫ ℳ ◁ s`, and `change` cannot produce that form; the identification is
`AlgebraicGeometry.mulSectionOne_eq_rightUnitor_inv_comp`, which every consumer rewrites with.
Its proof writes the sheaf of rings out explicitly, `⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp …⟩` as
`Stacks.SheafOfModules.sheafTensorStruct` does, and goes through `congrArg`/`Eq.trans` rather
than `rw`: the goal mentions the ring sheaf at two spellings at once and so is not type-correct
below default transparency, which is exactly what `rw`'s motive check works at.

**Why `tensorModules` is spelled out.** `Stacks.RelativeVeryAmple.tensorModules` is written in
full in the two definitions below because `AlgebraicGeometry.tensorModules`, a second name for
the same construction in `StacksFrontier/AlgebraicGeometry/TwistedSheaf/ZeroDimensionalTensor.lean`,
is in scope here and, being in the enclosing namespace, takes precedence over the `open`.

**The localized spelling of `mulSectionOne`.** `mulSectionOne_eq_mulRight_comp` below identifies
it with `Stacks.TensorSectionNonvanishing.mulRight`, the spelling the monicity criterion of
[Stacks, Tag 01CY] is stated at. The comparison of the two right unit constraints that this
rests on is general in the scheme and in the module, and is in
`StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalRightUnitorCompare.lean`, which is where
[Stacks, Tag 08A0] takes it from — that file is upstream of this one.

## References

* [Stacks Project, Tag 08A8](https://stacks.math.columbia.edu/tag/08A8)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry

/-! ### A global section is determined by its value on `⊤` -/

section Sections

variable {Y : Scheme.{u}}

/-- The restriction arrow from `⊤` to an open, as an arrow of the opposite category. -/
abbrev homFromTop (U : (Opens Y)ᵒᵖ) : Opposite.op (⊤ : Y.Opens) ⟶ U :=
  Quiver.Hom.op (homOfLE le_top)

/-- The compatible family of sections obtained from a section over `⊤` by restriction. Every
open is contained in `⊤`, and the restriction arrows out of `⊤` compose correctly because the
opens of a space form a poset, so there is at most one arrow between two of them. -/
def sectionOfTop (M : Y.Modules) (x : Γ(M, ⊤)) : M.sections :=
  M.val.sectionsMk (fun U => M.val.map (homFromTop U) x) (fun {U V} g =>
    (M.val.map_comp_apply (homFromTop U) g x).symm.trans
      (M.val.congr_map_apply (Subsingleton.elim ((homFromTop U) ≫ g) (homFromTop V)) x))

/-- The value of `sectionOfTop M x` on an open `U` is the restriction of `x` to `U`. -/
theorem sectionOfTop_val (M : Y.Modules) (x : Γ(M, ⊤)) (U : (Opens Y)ᵒᵖ) :
    (sectionOfTop M x).val U = M.val.map (homFromTop U) x := rfl

/-- The value of `sectionOfTop M x` on `⊤` is `x`. -/
@[simp]
theorem sectionOfTop_val_top (M : Y.Modules) (x : Γ(M, ⊤)) :
    (sectionOfTop M x).val (op ⊤) = x := by
  refine (M.val.congr_map_apply
    (Subsingleton.elim (homFromTop (op (⊤ : Y.Opens))) (𝟙 (op (⊤ : Y.Opens)))) x).trans ?_
  rw [M.val.map_id]
  rfl

/-- A compatible family of sections is recovered by `sectionOfTop` from its value on `⊤`. -/
theorem sectionOfTop_val_top_self (M : Y.Modules) (s : M.sections) :
    sectionOfTop M (s.val (op ⊤)) = s :=
  PresheafOfModules.sections_ext _ _ fun U => PresheafOfModules.sections_property s (homFromTop U)

/-- The map induced by `φ` on global sections sends `sectionOfTop M x` to
`sectionOfTop N (φ.app ⊤ x)`. -/
theorem sectionsMap_sectionOfTop {M N : Y.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    SheafOfModules.sectionsMap φ (sectionOfTop M x)
      = sectionOfTop N (Scheme.Modules.Hom.app φ ⊤ x) :=
  PresheafOfModules.sections_ext _ _ fun U =>
    PresheafOfModules.naturality_apply φ.val (homFromTop U) x

end Sections

/-- Surjectivity on sections over `⊤` gives surjectivity on global sections. -/
theorem surjective_sectionsMap_of_surjective_app_top {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (h : Function.Surjective (Scheme.Modules.Hom.app φ ⊤)) :
    Function.Surjective (SheafOfModules.sectionsMap φ) := by
  intro t
  obtain ⟨y, hy⟩ := h (t.val (op ⊤))
  exact ⟨sectionOfTop M y, by rw [sectionsMap_sectionOfTop, hy, sectionOfTop_val_top_self]⟩

/-- Surjectivity on global sections gives surjectivity on sections over `⊤`. -/
theorem surjective_app_top_of_surjective_sectionsMap {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (h : Function.Surjective (SheafOfModules.sectionsMap φ)) :
    Function.Surjective (Scheme.Modules.Hom.app φ ⊤) := by
  intro x
  obtain ⟨u, hu⟩ := h (sectionOfTop N x)
  exact ⟨u.val (op ⊤),
    (congrArg (fun t : N.sections => t.val (op ⊤)) hu).trans (sectionOfTop_val_top N x)⟩

/-! ### Global generation from surjectivity on global sections -/

/-- **A map onto a globally generated module that is onto global sections is an
epimorphism.** If `ℬ` is generated by a family of global sections and every global section of
`ℬ` is the image of one of `𝒜`, then the chosen generators lift, so the epimorphism out of the
free module on them factors through `ψ`. -/
theorem epi_of_isGeneratedByGlobalSections_of_surjective {Y : Scheme.{u}} {A B : Y.Modules}
    (ψ : A ⟶ B) (hB : SheafOfModules.IsGeneratedByGlobalSections B)
    (hψ : Function.Surjective (SheafOfModules.sectionsMap ψ)) : Epi ψ := by
  obtain ⟨σ⟩ := hB
  choose u hu using hψ
  have hfac : A.freeHomEquiv.symm (fun i => u (σ.s i)) ≫ ψ = σ.π :=
    (SheafOfModules.freeHomEquiv_symm_comp (fun i => u (σ.s i)) ψ).trans
      (congrArg B.freeHomEquiv.symm (funext fun i => hu (σ.s i)))
  have hcomp : Epi (A.freeHomEquiv.symm (fun i => u (σ.s i)) ≫ ψ) := hfac ▸ σ.epi
  exact epi_of_epi (A.freeHomEquiv.symm (fun i => u (σ.s i))) ψ

/-- A morphism of `k`-modules whose image contains a spanning set is surjective. -/
theorem surjective_of_span_le_range {k : Type u} [Field k] {V W : ModuleCat.{u} k} (f : V ⟶ W)
    (S : Set W) (hS : Submodule.span k S = ⊤)
    (hmem : ∀ x ∈ S, ∃ y, ConcreteCategory.hom f y = x) :
    Function.Surjective (ConcreteCategory.hom f) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hS, Submodule.span_le]
  exact hmem

/-! ### Degree-zero cohomology and sections over `⊤` -/

/-- Surjectivity of `H⁰(X, φ)` is surjectivity of `φ` on sections over `⊤`, the two being
identified by `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`. -/
theorem surjective_cohomologyOverFieldMap_zero_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {M N : X.Modules} (φ : M ⟶ N) :
    Function.Surjective (ConcreteCategory.hom (cohomologyOverFieldMap k f φ 0)) ↔
      Function.Surjective (Scheme.Modules.Hom.app φ ⊤) := by
  constructor
  · intro h x
    obtain ⟨a, ha⟩ := h ((cohomologyOverFieldZeroEquivSections k f N).symm x)
    refine ⟨cohomologyOverFieldZeroEquivSections k f M a, ?_⟩
    rw [← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, ha,
      Equiv.apply_symm_apply]
  · intro h a
    obtain ⟨y, hy⟩ := h (cohomologyOverFieldZeroEquivSections k f N a)
    refine ⟨(cohomologyOverFieldZeroEquivSections k f M).symm y, ?_⟩
    refine (cohomologyOverFieldZeroEquivSections k f N).injective ?_
    rw [cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, Equiv.apply_symm_apply, hy]

/-! ### Multiplication by a linear form, before the twists are reassociated -/

section Monoidal

open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

variable (n : ℕ) (S : Scheme.{u})

/-! The monoidal structure is `ProjectiveSpaceSectionFiniteFamily.tensorMonoidal`, whose sheaf
condition is `Stacks.SheafInternalHom.isSheaf_structureRingPresheaf`, the spelling
`Stacks.RelativeVeryAmple.tensorModules` uses, so the two tensor products are one expression. -/
attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.tensorMonoidal

/-- **Multiplication by a global section `s` of `𝒪(1)`, as a map `ℳ ⟶ ℳ ⊗ 𝒪(1)`.** This is the
first half of `twistSectionMul`: the half that does not reassociate the twists, and the half
that is natural in `ℳ`. -/
def mulSectionOne (M : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) :
    M ⟶ Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) M (twistOver n S 1) :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property M).inv ≫
    tensorRightOfUnitHom n S M (sectionHom (twistOver n S 1) s)

/-- **The comparison `(ℱ(d)) ⊗ 𝒪(1) ≅ ℱ(d + 1)`**: reassociate the three factors, then multiply
the two twists of the structure sheaf by `twistOverMulIso`. This is the second half of
`twistSectionMul`. -/
def twistAssocIso (F : (projectiveSpaceOver n S).Modules) (d : ℤ) :
    Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S)
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
        (twistOver n S 1) ≅
      Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
        (twistOver n S (d + 1)) :=
  Stacks.SheafOfModules.Invertible.tensorProductAssociator
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      F (twistOver n S d) (twistOver n S 1) ≪≫
    tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl F) (twistOverMulIso n S d 1)

/-- **`twistSectionMul` is multiplication by the section followed by the comparison of the
twists.** Both sides are the same four-fold composite; only the bracketing differs. -/
theorem twistSectionMul_eq_mulSectionOne_comp (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    twistSectionMul n S F s d =
      mulSectionOne n S
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
            (twistOver n S d)) s ≫
        (twistAssocIso n S F d).hom :=
  rfl

/-- **Tensoring on the right by a morphism out of the structure sheaf is whiskering it into the
second factor.** `…ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom` is the uncurried
tensor bifunctor read at the pair `(𝟙 ℳ, f)`, which by the definition of
`CategoryTheory.Functor.uncurry` is the bifunctor at the identity of `ℳ` followed by the
whiskering; the first factor is an identity because a functor preserves identities, and that is
the whole content here.

The sheaf of rings is written out as `Stacks.SheafOfModules.sheafTensorStruct` writes it —
`⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp …⟩` — rather than left to a definition, because that is
the spelling the whiskering of the monoidal structure carries. -/
theorem tensorRightOfUnitHom_eq_whiskerLeft (M : (projectiveSpaceOver n S).Modules)
    {B : (projectiveSpaceOver n S).Modules}
    (f : SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf ⟶ B) :
    tensorRightOfUnitHom n S M f = M ◁ f :=
  have hid := CategoryTheory.NatTrans.congr_app
    (CategoryTheory.Functor.map_id (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n S).presheaf,
        CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ (projectiveSpaceOver n S).presheaf
          (forget₂ CommRingCat RingCat)
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
            (projectiveSpaceOver n S))⟩) M)
    (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)
  (congrArg (fun k => k ≫ M ◁ f) hid).trans (Category.id_comp (M ◁ f))

/-- **`AlgebraicGeometry.mulSectionOne` is the inverse of the right unit constraint followed by
whiskering the section into the second factor.** This is the form every consumer of it needs:
the definition tensors with the section through
`…ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom`, whose extra identity factor
`AlgebraicGeometry.tensorRightOfUnitHom_eq_whiskerLeft` removes. -/
theorem mulSectionOne_eq_rightUnitor_inv_comp (M : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    mulSectionOne n S M s = (ρ_ M).inv ≫ M ◁ unitSectionHom n S s :=
  congrArg (fun k => (ρ_ M).inv ≫ k)
    (tensorRightOfUnitHom_eq_whiskerLeft n S M (sectionHom (twistOver n S 1) s))

/-- **Multiplication by a global section of `𝒪(1)` is natural in the module.** The right unitor
is natural and the two whiskerings commute, which is all the monoidal coherence this needs. -/
@[reassoc]
theorem mulSectionOne_naturality {M N : (projectiveSpaceOver n S).Modules} (f : M ⟶ N)
    (s : (twistOver n S 1).sections) :
    f ≫ mulSectionOne n S N s = mulSectionOne n S M s ≫ f ▷ twistOver n S 1 := by
  rw [mulSectionOne_eq_rightUnitor_inv_comp, mulSectionOne_eq_rightUnitor_inv_comp,
    rightUnitor_inv_naturality_assoc, ← whisker_exchange, Category.assoc]

end Monoidal

/-! ### Multiplication by a linear form, in the localized monoidal spelling -/

section MonoidalCompare

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.schemeMonoidalCategory

/-- **`AlgebraicGeometry.mulSectionOne` is `Stacks.TensorSectionNonvanishing.mulRight`.**
Multiplication by a global section `s` of `𝒪(1)` on `ℙⁿ_S`, written with the fixed unit
constraint of the tensor product sheaf, is multiplication by the same section in the localized
monoidal structure, followed by the comparison of the two tensor products. This is what lets the
monicity criterion of [Stacks, Tag 01CY] be applied to the first arrow of
[Stacks, Tag 08A0]. -/
theorem mulSectionOne_eq_mulRight_comp (n : ℕ) (S : Scheme.{u})
    (M : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) :
    mulSectionOne n S M s =
      Stacks.TensorSectionNonvanishing.mulRight M
          (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) ≫
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n S) M
          (twistOver n S 1)).hom :=
  (mulSectionOne_eq_rightUnitor_inv_comp n S M s).trans
    (tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft (projectiveSpaceOver n S) M
      (sectionHom (twistOver n S 1) s))

end MonoidalCompare

/-! ### The twist reflects epimorphisms -/

/-- **The degree-`d` twist reflects epimorphisms**, being an equivalence. -/
theorem epi_of_epi_projectiveTwistFunctor_map {R : Type u} [CommRing R] (n : ℕ) (d : ℤ)
    {M N : (projectiveSpaceOverRing n (.of R)).Modules} (f : M ⟶ N)
    (h : Epi ((Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n d).map f)) :
    Epi f :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n d).epi_of_epi_map h

/-! ### The free module on all global sections of a twist -/

/-- The map to `ℱ(m)` from the free module on *all* of its global sections. Global generation of
`ℱ(m)` is exactly the statement that this map is an epimorphism. -/
def twistGeneratingHom (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ) :
    SheafOfModules.free (projectiveTwist n F m).sections ⟶ projectiveTwist n F m :=
  (projectiveTwist n F m).freeHomEquiv.symm id

/-- The map `twistGeneratingHom k n F m` is surjective on global sections. -/
theorem surjective_sectionsMap_twistGeneratingHom (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ) :
    Function.Surjective (SheafOfModules.sectionsMap (twistGeneratingHom k n F m)) := fun t =>
  ⟨SheafOfModules.freeSection t,
    SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := projectiveTwist n F m) id t⟩

/-- If `twistGeneratingHom k n F m` is an epimorphism, then `ℱ(m)` is generated by its global
sections. -/
theorem isGeneratedByGlobalSections_of_epi_twistGeneratingHom (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ)
    (h : Epi (twistGeneratingHom k n F m)) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) :=
  ⟨{ I := (projectiveTwist n F m).sections, s := id, epi := h }⟩

/-! ### One step down: from `ℱ(m + 1)` to `ℱ(m)` -/

/-- The degree-one twist of `AlgebraicGeometry.twistGeneratingHom`, followed by the comparison
`(ℱ(m)) ⊗ 𝒪(1) ≅ ℱ(m + 1)`: a map onto `ℱ(m + 1)` from the twist of a free module. -/
def twistGeneratingHomSucc (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ) :
    projectiveTwist n (SheafOfModules.free (projectiveTwist n F m).sections) 1 ⟶
      projectiveTwist n F (m + 1) :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
      (twistGeneratingHom k n F m) ≫
    (twistAssocIso n (Spec (.of k)) F m).hom

/-- **Multiplication by a linear form on `ℱ(m)` factors through the twisted generating map.**
This is where naturality of multiplication by a section is used: multiplying a section of `ℱ(m)`
coming from the free module is the same as multiplying inside the free module and then mapping
down. -/
theorem twistGeneratingHom_comp_twistSectionMul (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ)
    (s : (twistOver n (Spec (.of k)) 1).sections) :
    twistGeneratingHom k n F m ≫ twistSectionMul n (Spec (.of k)) F s m
      = mulSectionOne n (Spec (.of k))
            (SheafOfModules.free (projectiveTwist n F m).sections) s ≫
        twistGeneratingHomSucc k n F m :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (twistAssocIso n (Spec (.of k)) F m).hom)
        (mulSectionOne_naturality n (Spec (.of k)) (twistGeneratingHom k n F m) s)).trans
      (Category.assoc _ _ _))

/-- **`H⁰` of the twisted generating map is onto, given [Stacks, Tag 08A7].** Every product of a
global section of `ℱ(m)` with a linear form lies in the image of
`H⁰(AlgebraicGeometry.twistGeneratingHomSucc k n F m)`, and those products span. -/
private theorem surjective_cohomologyOverFieldMap_twistGeneratingHomSucc (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) (m : ℤ)
    (hspan : mulSectionsSpan k n F m = ⊤) :
    Function.Surjective (ConcreteCategory.hom (cohomologyOverFieldMap k
      (projectiveSpaceToBase k n) (twistGeneratingHomSucc k n F m) 0)) := by
  have hpi : Function.Surjective (ConcreteCategory.hom
      (cohomologyOverFieldMap k (projectiveSpaceToBase k n) (twistGeneratingHom k n F m) 0)) :=
    (surjective_cohomologyOverFieldMap_zero_iff k (projectiveSpaceToBase k n)
        (twistGeneratingHom k n F m)).mpr
      (surjective_app_top_of_surjective_sectionsMap _
        (surjective_sectionsMap_twistGeneratingHom k n F m))
  refine surjective_of_span_le_range _
    {t | ∃ (s : (twistOver n (Spec (.of k)) 1).sections)
        (a : ↑(projectiveH k n (projectiveTwist n F m) 0)),
      t = ConcreteCategory.hom (mulSection k n F s m) a}
    hspan ?_
  rintro x ⟨s, a, rfl⟩
  obtain ⟨b, hb⟩ := hpi a
  refine ⟨ConcreteCategory.hom (cohomologyOverFieldMap k (projectiveSpaceToBase k n)
    (mulSectionOne n (Spec (.of k))
      (SheafOfModules.free (projectiveTwist n F m).sections) s) 0) b, ?_⟩
  have hcomp := ((cohomologyOverFieldMap_comp k (projectiveSpaceToBase k n)
      (twistGeneratingHom k n F m) (twistSectionMul n (Spec (.of k)) F s m) 0).symm.trans
    ((congrArg (fun φ => cohomologyOverFieldMap k (projectiveSpaceToBase k n) φ 0)
      (twistGeneratingHom_comp_twistSectionMul k n F m s)).trans
      (cohomologyOverFieldMap_comp k (projectiveSpaceToBase k n)
        (mulSectionOne n (Spec (.of k))
          (SheafOfModules.free (projectiveTwist n F m).sections) s)
        (twistGeneratingHomSucc k n F m) 0)))
  have happ := congrFun (congrArg (fun g => (ConcreteCategory.hom g : _ → _)) hcomp) b
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hb] at happ
  exact happ.symm

/-- **The descent step behind [Stacks, Tag 08A8], from the conclusion of [Stacks, Tag 08A7].**
Let `ℱ` be coherent on `ℙⁿ_k`, and suppose the products of global sections of `ℱ(m)` with
degree-one forms span `H⁰(ℙⁿ_k, ℱ(m + 1))`. If `ℱ(m + 1)` is globally generated, then so is
`ℱ(m)`.

Write `π : ⨁ 𝒪 ⟶ ℱ(m)` for the map from the free module on *all* global sections of `ℱ(m)`;
global generation of `ℱ(m)` is exactly that `π` is an epimorphism. Twisting `π` by one and
composing with `(ℱ(m)) ⊗ 𝒪(1) ≅ ℱ(m+1)` gives `ψ`. On `H⁰`, every product of a global section
of `ℱ(m)` with a linear form lies in the image of `ψ`, by naturality of that multiplication;
those products span `H⁰(ℙⁿ_k, ℱ(m+1))` by `hspan`, so `ψ` is onto global sections. A map onto a
globally generated module which is onto global sections is an epimorphism, so `ψ` is epi, hence
so is the twist of `π`, and the twist is an equivalence, so `π` itself is epi.

`m`-regularity of `ℱ` enters the descent step only through `hspan`, which is why it is not a
hypothesis here. `AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_field` proves `hspan`
from `m`-regularity alone, over an arbitrary field. -/
@[sga "6 XIII 1.3" "partial"]
theorem isGeneratedByGlobalSections_projectiveTwist_of_span_mulSections (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) (hFc : F.IsCoherent) (m : ℤ)
    (hgg : SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F (m + 1)))
    (hspan : mulSectionsSpan k n F m = ⊤) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) := by
  let _ := hFc
  have hepi : Epi (twistGeneratingHomSucc k n F m) :=
    epi_of_isGeneratedByGlobalSections_of_surjective _ hgg
      (surjective_sectionsMap_of_surjective_app_top _
        ((surjective_cohomologyOverFieldMap_zero_iff k (projectiveSpaceToBase k n) _).mp
          (surjective_cohomologyOverFieldMap_twistGeneratingHomSucc k n F m hspan)))
  have htwist : Epi ((Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
      (twistGeneratingHom k n F m)) := by
    have hfac : (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n 1).map
        (twistGeneratingHom k n F m)
        = twistGeneratingHomSucc k n F m ≫ (twistAssocIso n (Spec (.of k)) F m).inv :=
      (Iso.eq_comp_inv _).mpr rfl
    rw [hfac]
    exact @epi_comp _ _ _ _ _ _ hepi (twistAssocIso n (Spec (.of k)) F m).inv inferInstance
  exact isGeneratedByGlobalSections_of_epi_twistGeneratingHom k n F m
    (epi_of_epi_projectiveTwistFunctor_map n 1 _ htwist)

end AlgebraicGeometry

end
