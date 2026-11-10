module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorRingedSpace
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseFive
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ComplementIdeal
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.IdealSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendIdealSheaf
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Consumers
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.TensorFiniteness.RingedSpace

/-!
# The converses of clauses (5) to (9) of Stacks Tag 01Q3

`./ClauseFive.lean` proves clauses (5) and (6) of [Stacks, Tag 01Q3] from ampleness. This file
proves the converse the source's first cycle runs through, `(6) ⇒ (1)`, and with it the converse
of clause (5); then the source's second cycle `(7) ⇒ (8) ⇒ (9) ⇒ (1)`, which closes the
**nine-clause equivalence**: every clause of the tag is now proved equivalent to ampleness.

## Main definitions

* `Stacks.AmpleCharacterization.twistUnitHom`: the morphism `L ^⊗ (-n) ⟶ 𝒪_X` attached to a
  global section of `L ^⊗ n` — the inverse dictionary to
  `Stacks.AmpleCharacterization.twistHom` with `F = 𝒪_X`.

## Main results

* `Stacks.AmpleCharacterization.exists_twistUnitHom_eq`: **every morphism `L ^⊗ (-n) ⟶ 𝒪_X`
  comes from a global section of `L ^⊗ n`.**
* `Stacks.AmpleCharacterization.germ_tensorSection_mem_maximalSmul`: **a product of sections
  vanishes wherever its right factor does.**
* `Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom_ideal`: **clause (6) implies
  clause (1)**.
* `Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom`: **clause (5) implies clause
  (1)**, since clause (5) is clause (6) with its quantifier widened.
* `Stacks.AmpleCharacterization.isAmple_iff_iSup_range_twistHom` and
  `Stacks.AmpleCharacterization.isAmple_iff_iSup_range_twistHom_ideal`: the two resulting
  equivalences.
* `Stacks.AmpleCharacterization.isFiniteType_tensor`: **the tensor product of two modules of
  finite type is of finite type** ([Stacks, Tag 01CE] (2)), in the monoidal spelling the clauses
  of this tag are stated over.
* `quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections` and
  `quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_exists_epi_biproduct`: **clause (7)
  implies (8) implies (9)**, the source's own links, with clause (7) read as the tag states it —
  the twists merely globally generated.
* `quasiSeparatedSpace_and_exists_epi_biproduct_of_isEventuallyGloballyGenerated`: the same
  implication from the strengthened hypothesis of a *finite* generating family, which needs no
  quasi-compactness.
* `isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`: **clause (9) implies clause
  (1)**, the last link of the cycle, and
  `iSup_range_twistHom_ideal_eq_top_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`:
  **clause (9) implies clause (6)**, the implication the source states.
* `isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections`,
  `isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct` and
  `isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`: **clauses (7), (8) and (9)
  are each equivalent to clause (1)**, for a quasi-compact scheme.
* `isAmple_iff_quasiSeparatedSpace_and_isEventuallyGloballyGenerated`: clause (7) with a finite
  generating family is equivalent to clause (1) too, so the two readings of the clause agree.

All of these live in the namespace `Stacks.AmpleCharacterization`.

## The source's argument

Fix `x ∈ X` and an affine open `U ∋ x`, and let `Z = X ∖ U` with its reduced closed subscheme
structure (Schemes, Section 01IZ). Its quasi-coherent sheaf of ideals `ℐ_Z ⊆ 𝒪_X` is
`Stacks.ComplementIdeal.sheaf`, built in `./ComplementIdeal.lean`. Clause (6) applied to `ℐ_Z` at
`x` writes the whole stalk `(ℐ_Z)_x` as the sum of the images of the maps
`Stacks.AmpleCharacterization.twistHom`, and `(ℐ_Z)_x` contains the germ of `1`, which is not in
`𝔪_x · (𝒪_X)_x`. A sum of submodules is contained in `𝔪_x · (𝒪_X)_x` as soon as each summand is,
so some single map `t : L ^⊗ (-n) ⟶ ℐ_Z` has `t ≫ ι` with image at `x` outside `𝔪_x`.

That composite is a morphism `L ^⊗ (-n) ⟶ 𝒪_X`, hence
(`Stacks.AmpleCharacterization.exists_twistUnitHom_eq`) is multiplication by a global section
`s` of `L ^⊗ n`. Multiplication by `s` is bijective on the stalk at every point of `X_s`
(clause 2 of [Stacks, Tag 01CY]) and lands in `𝔪_y · (𝒪_X)_y` at every point `y` where `s`
vanishes, so `X_s` is exactly where that composite is onto. At `x` it is not inside `𝔪_x`, so
`x ∈ X_s`; at a point of `Z` the composite factors through `ℐ_Z`, whose sections all vanish
there, so `X_s ⊆ U`. Then `X_s` is affine by [Stacks, Tag 01PV]
(`Stacks.NonvanishingAffineIntersection.isAffineOpen_of_le_affineOpen`), which is clause (1) of
[Stacks, Tag 01PS] at `x`.

## Implementation notes

**The dictionary runs from sections to morphisms, not the other way.** A global section `s` of
`L ^⊗ n` gives `Stacks.AmpleCharacterization.twistUnitHom L n s`, multiplication by `s` followed
by the evaluation isomorphism `L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X`; written in that direction the stalk
behaviour is `Stacks.TensorSectionNonvanishing.mulRight`'s, for which
`Stacks.AmpleCharacterization.bijective_mapFun_mulRight_unitHom` and the germ computation below
are available. That it is *onto* the morphisms `L ^⊗ (-n) ⟶ 𝒪_X` — which is what lets the
morphism clause (6) produces be fed to those lemmas — is `exists_twistUnitHom_eq`, and it is
exactly the fully-faithfulness of `tensorLeft (L ^⊗ (-n))`, an equivalence because `L ^⊗ (-n)` is
invertible.

**The vanishing half is a germ computation, not a stalk-tensor identification.** What is needed
is that the germ of `t ⊗ₛ b` lies in `𝔪_x · (A ⊗ G)_x` as soon as the germ of `b` lies in
`𝔪_x · G_x`. This is proved by induction over `𝔪_x · G_x` with
`Submodule.smul_induction_on`: on a generator `r • n` the section `b` agrees near `x` with a
product `c • d`, and `t ⊗ₛ (c • d) = c • (t ⊗ₛ d)`. No identification of `(A ⊗ G)_x` with
`A_x ⊗ G_x` is used, and none is available.

**The second cycle re-enters ampleness at clause (1), not at clause (6).** The source closes it by
`(7) ⇒ (8) ⇒ (9) ⇒ (6)`, using [Stacks, Tag 01PG] for the last step: it writes a quasi-coherent
sheaf of ideals as the filtered colimit of its finite-type quasi-coherent sub-ideals, applies
clause (9) to each of them, and concludes the generation statement. What is proved below is
`(9) ⇒ (1)` with Tag 01PG used at the same place and for the same purpose, but applied to the
*one* sheaf of ideals the argument for clause (1) needs — the ideal `ℐ_Z` of the complement of an
affine open — rather than to an arbitrary one. The reason is the shape Tag 01PG is available in:
`Stacks.IdealSheaf.exists_fg_le_of_mem` is stated for
`AlgebraicGeometry.Scheme.IdealSheafData`, and applying it to a sheaf of ideals presented as a
module with a monomorphism into `𝒪_X` needs the inverse translation, from a quasi-coherent
submodule of `𝒪_X` to affine-local ideal data. That translation DOES exist --
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section`
(`ResolutionsAndBounds/FiniteTypeSubobjectColimit.lean:104`, Tag 01PG in subobject form), with the
factorisation supplied by `CategoryTheory.Subobject.arrow` -- so the DIRECT `(9) ⇒ (6)` is proved
by the source's own argument in `AmpleCharacterization/ClauseNineDirect.lean`. The route below
goes through ampleness instead and is kept as a second registration; the ideal
sheaf of a closed subscheme comes with its ideal data already. `(9) ⇒ (6)` is then `(9) ⇒ (1)`
followed by clause (6) from ampleness, which is what makes the nine clauses equivalent.

**Clause (7) says only that the twists are globally generated.** The clause of the source asks
for no bound on the generating family, and the implication into clause (8) is stated from that
hypothesis: `quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections`. Clause
(8) does ask for a finite direct sum, and the finiteness comes from the tag's standing
quasi-compactness hypothesis rather than from the clause — `F ⊗ L ^⊗ n` is of finite type by
[Stacks, Tag 01CE] (2) (`isFiniteType_tensor`, `L ^⊗ n` being invertible and hence of finite
type), and Modules, Lemma 17.9.7 ([Stacks, Tag 01BB]) cuts a generating family of a finite-type
module on a quasi-compact scheme down to a finite one
(`Stacks.AmpleEventualGeneration.isFinGen_of_generatingSections`). The implication from the
strengthened hypothesis of a finite generating family is kept as
`quasiSeparatedSpace_and_exists_epi_biproduct_of_isEventuallyGloballyGenerated`, which is the
form `Stacks.AmpleGlobalGeneration.IsEventuallyGloballyGenerated` is phrased in and needs no
quasi-compactness; nothing below rests on it.

The three inputs that step needs are in `./IdealSheafFiniteType.lean`: affine-local finite
generation of an `IdealSheafData` gives `SheafOfModules.IsFiniteType` of the corresponding
module (`Stacks.IdealSheafModules.isFiniteType_sheaf`), an epimorphism of `X.Modules` is
surjective on stalks (`Stacks.ModuleStalk.surjective_mapFun_of_epi`), and a germ in the target of
an epimorphism from a finite direct sum is a sum of germs coming from the summands
(`Stacks.ModuleBicone.exists_germ_sum_of_epi`).

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample
open Stacks.TensorSectionNonvanishing (mulRight)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.AmpleCharacterization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### A product of sections vanishes wherever its right factor does -/

section Vanishing

variable {X : Scheme.{u}}

/-- The germ of a product of sections depends on its right factor only through that factor's
germ. -/
theorem germ_tensorSection_congr (A G : X.Modules) {x : X} {W : X.Opens} (hxW : x ∈ W)
    (t : Γ(A, W)) (b b' : Γ(G, W))
    (h : (G.presheaf.germ W x hxW).hom b = (G.presheaf.germ W x hxW).hom b') :
    ((A ⊗ G).presheaf.germ W x hxW).hom (tensorSection A G t b) =
      ((A ⊗ G).presheaf.germ W x hxW).hom (tensorSection A G t b') := by
  obtain ⟨W₄, hx₄, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq G.presheaf x hxW hxW b b' h
  rw [Subsingleton.elim i₂ i₁] at heq
  rw [← Stacks.SectionTensorFormula.germ_tensorSection A G i₁ x hx₄ t b,
    ← Stacks.SectionTensorFormula.germ_tensorSection A G i₁ x hx₄ t b', heq]

/-- **A product of sections vanishes wherever its right factor does.** If the germ of `b` at `x`
lies in `𝔪_x · G_x` then the germ of `t ⊗ₛ b` lies in `𝔪_x · (A ⊗ G)_x`, for every section `t`
of `A` over the same open set. -/
theorem germ_tensorSection_mem_maximalSmul (A G : X.Modules) {x : X}
    {u : TopCat.Presheaf.stalk (C := Ab.{u}) G.presheaf x}
    (hu : u ∈ Stacks.ModuleStalk.maximalSmul G x)
    (W : X.Opens) (hxW : x ∈ W) (t : Γ(A, W)) (b : Γ(G, W))
    (hb : (G.presheaf.germ W x hxW).hom b = u) :
    ((A ⊗ G).presheaf.germ W x hxW).hom (tensorSection A G t b) ∈
      Stacks.ModuleStalk.maximalSmul (A ⊗ G) x := by
  have hu' : u ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.presheaf x)) := hu
  revert W
  refine Submodule.smul_induction_on hu' ?_ ?_
  · -- a generator `r • n` with `r ∈ 𝔪_x`
    intro r hr n _ W hxW t b hb
    obtain ⟨W₁, hx₁, c, hc⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    obtain ⟨W₂, hx₂, d, hd⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf n
    have hx₃ : x ∈ W ⊓ (W₁ ⊓ W₂) := ⟨hxW, hx₁, hx₂⟩
    set i : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W := homOfLE inf_le_left with hi
    set i₁ : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W₁ := homOfLE (inf_le_right.trans inf_le_left) with hi₁
    set i₂ : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W₂ := homOfLE (inf_le_right.trans inf_le_right) with hi₂
    set c₃ : Γ(X, W ⊓ (W₁ ⊓ W₂)) := X.presheaf.map i₁.op c with hc₃
    set d₃ : Γ(G, W ⊓ (W₁ ⊓ W₂)) := G.presheaf.map i₂.op d with hd₃
    have hgc : (X.presheaf.germ _ x hx₃).hom c₃ = r := by
      rw [hc₃, TopCat.Presheaf.germ_res_apply, hc]
    have hgd : (G.presheaf.germ _ x hx₃).hom d₃ = n := by
      rw [hd₃, TopCat.Presheaf.germ_res_apply, hd]
    have hstep : (G.presheaf.germ _ x hx₃).hom (G.presheaf.map i.op b) =
        (G.presheaf.germ _ x hx₃).hom (c₃ • d₃) := by
      rw [TopCat.Presheaf.germ_res_apply, hb, Stacks.ModuleStalk.germ_smul, hgc, hgd]
    rw [← Stacks.SectionTensorFormula.germ_tensorSection A G i x hx₃ t b,
      germ_tensorSection_congr A G hx₃ _ _ _ hstep,
      Stacks.SectionTensorFormula.tensorSection_smul_right, Stacks.ModuleStalk.germ_smul, hgc]
    exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hr _
  · -- additivity
    intro v w hv hw W hxW t b hb
    obtain ⟨W₁, hx₁, b₁, hb₁⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf v
    obtain ⟨W₂, hx₂, b₂, hb₂⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf w
    have hx₃ : x ∈ W ⊓ (W₁ ⊓ W₂) := ⟨hxW, hx₁, hx₂⟩
    set i : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W := homOfLE inf_le_left with hi
    set i₁ : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W₁ := homOfLE (inf_le_right.trans inf_le_left) with hi₁
    set i₂ : (W ⊓ (W₁ ⊓ W₂) : X.Opens) ⟶ W₂ := homOfLE (inf_le_right.trans inf_le_right) with hi₂
    set e₁ : Γ(G, W ⊓ (W₁ ⊓ W₂)) := G.presheaf.map i₁.op b₁ with he₁
    set e₂ : Γ(G, W ⊓ (W₁ ⊓ W₂)) := G.presheaf.map i₂.op b₂ with he₂
    have hge₁ : (G.presheaf.germ _ x hx₃).hom e₁ = v := by
      rw [he₁, TopCat.Presheaf.germ_res_apply, hb₁]
    have hge₂ : (G.presheaf.germ _ x hx₃).hom e₂ = w := by
      rw [he₂, TopCat.Presheaf.germ_res_apply, hb₂]
    have hstep : (G.presheaf.germ _ x hx₃).hom (G.presheaf.map i.op b) =
        (G.presheaf.germ _ x hx₃).hom (e₁ + e₂) := by
      rw [TopCat.Presheaf.germ_res_apply, hb, map_add, hge₁, hge₂]
    rw [← Stacks.SectionTensorFormula.germ_tensorSection A G i x hx₃ t b,
      germ_tensorSection_congr A G hx₃ _ _ _ hstep,
      Stacks.SectionTensorFormula.tensorSection_add_right, map_add]
    exact Submodule.add_mem _
      (hv _ hx₃ (A.presheaf.map i.op t) e₁ hge₁) (hw _ hx₃ (A.presheaf.map i.op t) e₂ hge₂)

end Vanishing

/-! ### The tensor product of two modules of finite type -/

section TensorFiniteType

variable {X : Scheme.{u}}

/-- **The monoidal tensor product of two `𝒪_X`-modules is the tensor product sheaf of
[Stacks, Tag 01CA].** `Stacks.SheafOfModules.tensorObjIso` identifies the localized monoidal
product with the sheafification of the objectwise tensor product, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_eq'` retypes that sheafification over
the ring sheaf of the underlying ringed space, which is the spelling the finiteness results of
[Stacks, Tag 01CE] are stated for. -/
def tensorIsoTensorSheaf (F G : X.Modules) :
    F ⊗ G ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)) :=
  Stacks.SheafOfModules.tensorObjIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F G ≪≫
    eqToIso (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_eq'
      X.toRingedSpace F G).symm

/-- **[Stacks, Tag 01CE] (2) in the monoidal spelling**: the tensor product of two `𝒪_X`-modules
of finite type is of finite type.

`AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType` proves this for the tensor product
sheaf of [Stacks, Tag 01CA]; `tensorIsoTensorSheaf` carries it to the monoidal product, finite
type being invariant under isomorphism
(`AlgebraicGeometry.isFiniteType_of_iso_modules`). The two hypotheses are restated over
`AlgebraicGeometry.structureSheafRing X.toRingedSpace`, which is `X.ringCatSheaf` by `rfl` but is
not reached by instance search. -/
theorem isFiniteType_tensor (F G : X.Modules)
    (hF : SheafOfModules.IsFiniteType.{u, u, u} F)
    (hG : SheafOfModules.IsFiniteType.{u, u, u} G) :
    SheafOfModules.IsFiniteType.{u, u, u} ((F ⊗ G : X.Modules)) := by
  have hF' : SheafOfModules.IsFiniteType.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) F := hF
  have hG' : SheafOfModules.IsFiniteType.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) G := hG
  exact AlgebraicGeometry.isFiniteType_of_iso_modules (tensorIsoTensorSheaf F G)
    (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType X.toRingedSpace F G hF' hG')

end TensorFiniteType

/-! ### Global sections of a positive twist as morphisms out of the negative twist -/

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- `L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X`, with the target in the `Stacks.Ample.unitModule` spelling that
clause (6) states its sheaves of ideals over. -/
def negTensorCancelUnitIso (n : ℤ) :
    tensorPowModule X L (-n) ⊗ tensorPowModule X L n ≅ unitModule X :=
  negTensorCancelIso L n ≪≫ (Stacks.AmpleGlobalGeneration.unitModuleIsoUnit X).symm

/-- **The morphism `L ^⊗ (-n) ⟶ 𝒪_X` attached to a global section of `L ^⊗ n`**: multiplication
by that section, followed by the evaluation isomorphism of [Stacks, Tag 01CU]. -/
def twistUnitHom (n : ℤ) (σ : Γ(tensorPowModule X L n, ⊤)) :
    tensorPowModule X L (-n) ⟶ unitModule X :=
  mulRight (tensorPowModule X L (-n)) (unitHom (tensorPowModule X L n) σ) ≫
    (negTensorCancelUnitIso L n).hom

/-- **Every morphism `L ^⊗ (-n) ⟶ 𝒪_X` is multiplication by a global section of `L ^⊗ n`.**
Tensoring on the left by the invertible module `L ^⊗ (-n)` is an equivalence, hence full, and
a morphism out of the monoidal unit is a global section. -/
theorem exists_twistUnitHom_eq (n : ℤ) (ψ : tensorPowModule X L (-n) ⟶ unitModule X) :
    ∃ σ : Γ(tensorPowModule X L n, ⊤), twistUnitHom L n σ = ψ := by
  have : (tensorLeft (tensorPowModule X L (-n))).IsEquivalence :=
    (AlgebraicGeometry.SheafOfModules.isInvertible_iff_isEquivalence_tensorLeft X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _).mp inferInstance
  set f : 𝟙_ X.Modules ⟶ tensorPowModule X L n :=
    (tensorLeft (tensorPowModule X L (-n))).preimage
      ((ρ_ (tensorPowModule X L (-n))).hom ≫ ψ ≫ (negTensorCancelUnitIso L n).inv) with hf
  have hmap : tensorPowModule X L (-n) ◁ f =
      (ρ_ (tensorPowModule X L (-n))).hom ≫ ψ ≫ (negTensorCancelUnitIso L n).inv :=
    (tensorLeft (tensorPowModule X L (-n))).map_preimage _
  refine ⟨Stacks.NonvanishingSpelling.sectionsEquiv X (tensorPowModule X L n)
    (Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n) f), ?_⟩
  have hcomp : ∀ m : Γ(tensorPowModule X L n, ⊤),
      unitHom (tensorPowModule X L n) m =
        (Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n)).symm
          ((Stacks.NonvanishingSpelling.sectionsEquiv X (tensorPowModule X L n)).symm m) :=
    fun _ => rfl
  have hunit : unitHom (tensorPowModule X L n)
      (Stacks.NonvanishingSpelling.sectionsEquiv X (tensorPowModule X L n)
        (Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n) f)) = f :=
    -- purpose: forward reasoning, not `rw`. The two equivalences meet at the sections of
    -- `tensorPowModule X L n`, whose ring sheaf `X.ringCatSheaf` is a `TopCat.Sheaf`; the
    -- `SheafOfModules.sections` index wants a `Sheaf (Opens.grothendieckTopology ↥X)`. The two
    -- agree by `rfl` but not at `implicit` transparency, so `rw`'s pattern match is run against a
    -- target it considers ill-typed and `Equiv.symm_apply_apply` finds no occurrence. `Eq.trans`
    -- and `congrArg` check the junction at default transparency, where the spellings do agree.
    (hcomp _).trans
      ((congrArg (Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n)).symm
          ((Stacks.NonvanishingSpelling.sectionsEquiv X (tensorPowModule X L n)).symm_apply_apply
            (Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n) f))).trans
        ((Stacks.SectionProduct.monoidalUnitHomEquiv (tensorPowModule X L n)).symm_apply_apply f))
  rw [twistUnitHom, hunit, Stacks.TensorSectionNonvanishing.mulRight, Category.assoc, hmap]
  simp

/-- **Multiplication by a global section of `L ^⊗ n` is bijective on the stalk at every point
where that section does not vanish.** -/
theorem bijective_mapFun_twistUnitHom (n : ℤ) (σ : Γ(tensorPowModule X L n, ⊤)) {x : X}
    (hx : x ∈ nonvanishingLocus (tensorPowModule X L n) σ) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (twistUnitHom L n σ) x) := by
  have hbij := bijective_mapFun_mulRight_unitHom (tensorPowModule X L (-n))
    (tensorPowModule X L n) σ
    (W := Stacks.NonvanishingOpen.nonvanishingOpen X (tensorPowModule X L n) σ)
    ((Stacks.NonvanishingOpen.mem_nonvanishingOpen X _ σ x).mpr hx)
    fun y hy => (Stacks.NonvanishingOpen.mem_nonvanishingOpen X _ σ y).mp hy
  have hfun : Stacks.ModuleStalk.mapFun (twistUnitHom L n σ) x =
      Stacks.ModuleStalk.mapFun (negTensorCancelUnitIso L n).hom x ∘
        Stacks.ModuleStalk.mapFun
          (mulRight (tensorPowModule X L (-n)) (unitHom (tensorPowModule X L n) σ)) x :=
    funext fun w => Stacks.ModuleStalk.mapFun_comp _ _ x w
  rw [hfun]
  exact (bijective_mapFun_of_iso (negTensorCancelUnitIso L n) x).comp hbij

/-- **Multiplication by a global section of `L ^⊗ n` lands in `𝔪_y · (𝒪_X)_y` at every point
where that section vanishes.** -/
theorem mapFun_twistUnitHom_mem_maximalSmul (n : ℤ) (σ : Γ(tensorPowModule X L n, ⊤)) {y : X}
    (hy : y ∉ nonvanishingLocus (tensorPowModule X L n) σ)
    (v : TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPowModule X L (-n)).presheaf y) :
    Stacks.ModuleStalk.mapFun (twistUnitHom L n σ) y v ∈
      Stacks.ModuleStalk.maximalSmul (unitModule X) y := by
  obtain ⟨W, hyW, t, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (tensorPowModule X L (-n)).presheaf v
  have hgerm : ((tensorPowModule X L n).presheaf.germ W y hyW).hom
        (Stacks.SectionExtension.resTop W σ) =
      ((tensorPowModule X L n).presheaf.Γgerm y).hom σ :=
    Stacks.SectionTensorFormula.germ_resTop _ σ W y hyW
  have hmem : ((tensorPowModule X L n).presheaf.Γgerm y).hom σ ∈
      Stacks.ModuleStalk.maximalSmul (tensorPowModule X L n) y := by
    rw [Stacks.Ample.mem_nonvanishingLocus_iff] at hy
    exact not_not.mp hy
  have hvan := germ_tensorSection_mem_maximalSmul (tensorPowModule X L (-n))
    (tensorPowModule X L n) hmem W hyW t (Stacks.SectionExtension.resTop W σ) hgerm
  have hcomp : Stacks.ModuleStalk.mapFun (twistUnitHom L n σ) y
      (((tensorPowModule X L (-n)).presheaf.germ W y hyW).hom t) =
      Stacks.ModuleStalk.mapFun (negTensorCancelUnitIso L n).hom y
        (Stacks.ModuleStalk.mapFun
          (mulRight (tensorPowModule X L (-n)) (unitHom (tensorPowModule X L n) σ)) y
          (((tensorPowModule X L (-n)).presheaf.germ W y hyW).hom t)) :=
    Stacks.ModuleStalk.mapFun_comp _ _ y _
  rw [hcomp, Stacks.ModuleStalk.mapFun_germ, mulSec_unitHom]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul _ y hvan
/-- A morphism `L ^⊗ (-n) ⟶ 𝒪_X` that is multiplication by `σ`, is onto at `x` and lies in
`𝔪_y · (𝒪_X)_y` at every point `y` outside the affine open `U`, makes `X_σ` an affine
neighbourhood of `x`. -/
private theorem mem_and_isAffineOpen_nonvanishingOpen (n : ℕ)
    (σ : Γ(tensorPowModule X L (n : ℤ), ⊤)) (U : X.affineOpens) {x : X}
    (v : TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPowModule X L (-(n : ℤ))).presheaf x)
    (hvalue : Stacks.ModuleStalk.mapFun (twistUnitHom L (n : ℤ) σ) x v ∉
      Stacks.ModuleStalk.maximalSmul (unitModule X) x)
    (hvan : ∀ y : X, y ∉ (U : X.Opens) → ∀ w, Stacks.ModuleStalk.mapFun
      (twistUnitHom L (n : ℤ) σ) y w ∈ Stacks.ModuleStalk.maximalSmul (unitModule X) y) :
    x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (tensorPowModule X L (n : ℤ)) σ ∧
      IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen X
        (tensorPowModule X L (n : ℤ)) σ) := by
  refine ⟨(Stacks.NonvanishingOpen.mem_nonvanishingOpen X _ σ x).mpr ?_, ?_⟩
  · by_contra hc
    exact hvalue (mapFun_twistUnitHom_mem_maximalSmul L (n : ℤ) σ hc v)
  · refine Stacks.NonvanishingAffineIntersection.isAffineOpen_of_le_affineOpen
      (tensorPowModule X L (n : ℤ)) σ U.2 fun y hy => ?_
    by_contra hyU
    obtain ⟨z, hz⟩ := Stacks.SectionProduct.exists_notMem_maximalSmul (unitModule X) y
    obtain ⟨c, hc⟩ := (bijective_mapFun_twistUnitHom L (n : ℤ) σ
      ((Stacks.NonvanishingOpen.mem_nonvanishingOpen X _ σ y).mp hy)).2 z
    exact hz (hc ▸ hvan y hyU c)


/-! ### Clause (6) implies clause (1) -/

/-- **Clause (6) of [Stacks, Tag 01Q3] implies clause (1)** — the implication the source's cycle
re-enters ampleness through. If for every quasi-coherent sheaf of ideals of the quasi-compact
scheme `X` the sum of the images of the canonical maps
`Γ(X, ℐ ⊗ L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ ℐ`, `n ≥ 1`, is all of `ℐ`, then `L` is ample.

This is the source's argument verbatim. Given `x`, choose an affine open `U ∋ x` and apply the
hypothesis to the quasi-coherent sheaf of ideals `Stacks.ComplementIdeal.sheaf` of the reduced
closed subscheme on `X ∖ U` (Schemes, Section 01IZ, i.e. [Stacks, Tag 01J3]). Its stalk at `x`
contains the germ of `1`, so some single map `L ^⊗ (-n) ⟶ ℐ` composed with the inclusion
`ℐ ⟶ 𝒪_X` has image at `x` outside `𝔪_x`. That composite is multiplication by a global section
`s` of `L ^⊗ n` (`Stacks.AmpleCharacterization.exists_twistUnitHom_eq`); `s` does not vanish at
`x`, and it vanishes along `X ∖ U` because the composite factors through `ℐ`, so `X_s ⊆ U` and
`X_s` is affine by [Stacks, Tag 01PV]. -/
@[stacks 01Q3 "clause (6) implies (1)", ega "II 4.5.5" "(b) ⇒ (a), ideals"]
theorem isAmple_of_iSup_range_twistHom_ideal [CompactSpace X]
    (h : ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j → J.IsQuasicoherent →
      ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤) :
    IsAmple X L := by
  refine ⟨‹CompactSpace X›, fun x => ?_⟩
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  set Z : Closeds X := ⟨((U : X.Opens) : Set X)ᶜ, (U : X.Opens).2.isClosed_compl⟩ with hZdef
  have hxZ : x ∉ Z := fun hc => hc hxU
  obtain ⟨g, hg⟩ := Stacks.ComplementIdeal.exists_mapFun_ι_notMem_maximalSmul X Z hxZ
  set J : X.Modules := Stacks.ComplementIdeal.sheaf X Z with hJdef
  set jj : J ⟶ unitModule X := Stacks.ComplementIdeal.ι X Z with hjdef
  have hsup := h J jj inferInstance inferInstance x
  set P : Submodule (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) J.presheaf x) :=
    Submodule.comap (Stacks.ModuleStalk.map jj x)
      (Stacks.ModuleStalk.maximalSmul (unitModule X) x) with hPdef
  have hex : ∃ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
      ¬ LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x) ≤ P := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) ≤ P :=
      iSup_le fun n => iSup_le fun hn => iSup_le fun m => hcon n hn m
    rw [hsup] at hle
    exact hg (hle Submodule.mem_top)
  obtain ⟨n, hn, m, hnot⟩ := hex
  obtain ⟨w, hwmem, hwP⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨v, rfl⟩ := hwmem
  obtain ⟨σ, hσ⟩ := exists_twistUnitHom_eq L (n : ℤ) (twistHom L J (n : ℤ) m ≫ jj)
  have hvalue : Stacks.ModuleStalk.mapFun (twistUnitHom L (n : ℤ) σ) x v ∉
      Stacks.ModuleStalk.maximalSmul (unitModule X) x := by
    rw [hσ, Stacks.ModuleStalk.mapFun_comp]
    exact hwP
  obtain ⟨hxσ, haff⟩ := mem_and_isAffineOpen_nonvanishingOpen L n σ U v hvalue fun y hyU w => by
    rw [hσ, Stacks.ModuleStalk.mapFun_comp]
    exact Stacks.ComplementIdeal.mapFun_ι_mem_maximalSmul X Z hyU _
  exact ⟨n, hn, σ, _, Stacks.NonvanishingOpen.coe_nonvanishingOpen X _ σ, hxσ, haff⟩

/-- **Clause (5) of [Stacks, Tag 01Q3] implies clause (1)**: clause (5) is clause (6) with its
quantifier widened from the quasi-coherent sheaves of ideals to all quasi-coherent sheaves, so
this is `Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom_ideal` with the hypothesis
restricted. -/
@[stacks 01Q3 "clause (5) implies (1)", ega "II 4.5.5" "(b) ⇒ (a)"]
theorem isAmple_of_iSup_range_twistHom [CompactSpace X]
    (h : ∀ F : X.Modules, F.IsQuasicoherent → ∀ x : X,
      (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(F ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L F (n : ℤ) m) x)) = ⊤) :
    IsAmple X L :=
  isAmple_of_iSup_range_twistHom_ideal L fun J _ _ hJ => h J hJ

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (5)**, for a quasi-compact
scheme. -/
theorem isAmple_iff_iSup_range_twistHom [CompactSpace X] :
    IsAmple X L ↔ ∀ F : X.Modules, F.IsQuasicoherent → ∀ x : X,
      (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(F ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L F (n : ℤ) m) x)) = ⊤ :=
  ⟨iSup_range_twistHom_eq_top_of_isAmple L, isAmple_of_iSup_range_twistHom L⟩

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (6)**, for a quasi-compact
scheme. -/
theorem isAmple_iff_iSup_range_twistHom_ideal [CompactSpace X] :
    IsAmple X L ↔ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j → J.IsQuasicoherent →
      ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤ :=
  ⟨iSup_range_twistHom_ideal_eq_top_of_isAmple L, isAmple_of_iSup_range_twistHom_ideal L⟩


/-! ### The source's remaining links, `(7) ⇒ (8) ⇒ (9)` -/

/-- **Clause (7) of [Stacks, Tag 01Q3] implies clause (8), at clause (7)'s own strength.** The
clause asks only that `F ⊗ L ^⊗ n` be *globally generated* for every `n ≥ n₀` — generated by
*some* family of global sections, [Stacks, Tag 03DE] (3), with no finiteness demanded of that
family — and that is the hypothesis carried here. The quasi-compactness of `X` is the standing
hypothesis of the tag and nothing else is added.

The finiteness clause (8) asks for is supplied by that quasi-compactness, which is where the
source puts it too. `F ⊗ L ^⊗ n` is of finite type (`isFiniteType_tensor`: `F` is of finite type
by the clause's own hypothesis and `L ^⊗ n` is of finite type, being invertible), and on a
quasi-compact scheme a module of finite type generated by global sections is generated by
finitely many of them — Modules, Lemma 17.9.7 ([Stacks, Tag 01BB]), available as
`Stacks.AmpleEventualGeneration.isFinGen_of_generatingSections`. From there the step is the one
`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple` runs: a
finite family of global sections generating `F ⊗ L ^⊗ n` for one `n ≥ 1` is exactly an
epimorphism onto `F` from a finite direct sum of copies of `L ^⊗ (-n)`, by
`Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free`. -/
@[stacks 01Q3 "clause (7) implies (8)", ega "II 2.7.10" "(d) ⇒ (d')"]
theorem quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections
    [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          _root_.SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
            ((F ⊗ tensorPowModule X L n : X.Modules))) :
    QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p := by
  refine ⟨h.1, fun F hFqc hFft => ?_⟩
  obtain ⟨n₀, hgen⟩ := h.2 F hFqc hFft
  obtain ⟨σ₀⟩ := hgen (max n₀ 1) (le_max_left _ _)
  obtain ⟨σ, hfin⟩ := Stacks.AmpleEventualGeneration.isFinGen_of_generatingSections
    (isFiniteType_tensor F (tensorPowModule X L (max n₀ 1)) hFft
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)) σ₀
  have : Finite σ.I := hfin
  obtain ⟨b, hb, p, hp, -⟩ := Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L
    (max n₀ 1) F ((F ⊗ tensorPowModule X L (max n₀ 1)).freeHomEquiv.symm σ.s) σ.epi
  exact ⟨max n₀ 1, σ.I, hfin, lt_of_lt_of_le zero_lt_one (le_max_right _ _), b, hb, p, hp⟩

/-- **Clause (7) of [Stacks, Tag 01Q3] implies clause (8)**, from the *strengthened* hypothesis
that the twists are generated by **finitely many** global sections — which is more than clause
(7) says, and so is not the tag's implication; that one is
`quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections` above, and it is
what the equivalences below rest on. This variant is kept because it needs no quasi-compactness:
it is the proof
`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple` runs with
ampleness replaced by the strengthened clause, a finite family of global sections generating
`F ⊗ L ^⊗ n` for one `n ≥ 1` being exactly an epimorphism onto `F` from a finite direct sum of
copies of `L ^⊗ (-n)`, by
`Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free`. -/
@[stacks 01Q3 "clause (7) implies (8), under the strengthened hypothesis that the twists are \
generated by finitely many global sections; the tag's own implication is \
`quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections` above",
  ega "II 2.7.10" "(d) ⇒ (d')"]
theorem quasiSeparatedSpace_and_exists_epi_biproduct_of_isEventuallyGloballyGenerated
    (h : QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          ∃ σ : (F ⊗ tensorPowModule X L n).GeneratingSections, Finite σ.I) :
    QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p := by
  refine ⟨h.1, fun F hFqc hFft => ?_⟩
  obtain ⟨n₀, hgen⟩ := h.2 F hFqc hFft
  obtain ⟨σ, hfin⟩ := hgen (max n₀ 1) (le_max_left _ _)
  have : Finite σ.I := hfin
  obtain ⟨b, hb, p, hp, -⟩ := Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L
    (max n₀ 1) F ((F ⊗ tensorPowModule X L (max n₀ 1)).freeHomEquiv.symm σ.s) σ.epi
  exact ⟨max n₀ 1, σ.I, hfin, lt_of_lt_of_le zero_lt_one (le_max_right _ _), b, hb, p, hp⟩

/-- **Clause (8) of [Stacks, Tag 01Q3] implies clause (9)**, the source's "trivial" step: clause
(9) is clause (8) with its quantifier restricted to the sheaves of ideals. -/
@[stacks 01Q3 "clause (8) implies (9)", ega "II 2.7.10" "(d'), ideals"]
theorem quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_exists_epi_biproduct
    (h : QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p) :
    QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ J), Epi p :=
  ⟨h.1, fun J _ _ hJqc hJft => h.2 J hJqc hJft⟩


/-! ### Clause (9) implies clause (1), closing the cycle -/

/-- **Clause (9) of [Stacks, Tag 01Q3] implies clause (1)** — the step the source's second cycle
re-enters ampleness through, and with the two implications above the last link of the
nine-clause equivalence.

The argument is the source's, with [Stacks, Tag 01PG] where the source puts it. Fix `x`, choose
an affine open `U ∋ x` and let `Z = X ∖ U` with its reduced closed subscheme structure. Its
sheaf of ideals `ℐ_Z` is the unit ideal on some affine open `V ∋ x`, so Tag 01PG — in its
ideal-sheaf form `Stacks.IdealSheaf.exists_fg_le_of_mem`, which is what quasi-separatedness is
used for — produces a quasi-coherent sheaf of ideals `ℐ ⊆ ℐ_Z`, finitely generated on every
affine open and still containing the unit section over `V`. Being finitely generated affine-
locally it is of finite type (`Stacks.IdealSheafModules.isFiniteType_sheaf`), so clause (9)
applies to it: `ℐ` is a quotient of a finite direct sum of copies of `L ^⊗ (-n)` with `n > 0`.

The germ at `x` of that unit section is not in `𝔪_x · (𝒪_X)_x`, and
`Stacks.ModuleBicone.exists_germ_sum_of_epi` writes it as a finite sum of germs coming from the
summands; since `𝔪_x · (𝒪_X)_x` is a submodule, one summand `i` already escapes it. Its
composite `L ^⊗ (-n) ⟶ ℐ ⟶ 𝒪_X` is multiplication by a global section `σ` of `L ^⊗ n`
(`Stacks.AmpleCharacterization.exists_twistUnitHom_eq`), and from here the argument is the one
`Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom_ideal` runs: `σ` does not vanish at
`x`, and it vanishes at every point of `Z` — which is in the support of `ℐ` because `ℐ ⊆ ℐ_Z` —
so `X_σ ⊆ U` and `X_σ` is affine by [Stacks, Tag 01PV]. -/
@[stacks 01Q3 "clause (9) implies (1)", ega "II 2.7.10" "(d') ⇒ (a), ideals",
  ega "II 4.5.5" "(d') ⇒ (a), ideals"]
theorem isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ J), Epi p) :
    IsAmple X L := by
  obtain ⟨hqs, h9⟩ := h
  have := hqs
  refine ⟨‹CompactSpace X›, fun x => ?_⟩
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  set Z : Closeds X := ⟨((U : X.Opens) : Set X)ᶜ, (U : X.Opens).2.isClosed_compl⟩ with hZdef
  have hxZ : x ∉ Z := fun hc => hc hxU
  -- [Stacks, Tag 01PG]: a finite-type subideal of `ℐ_Z` still containing the unit near `x`
  obtain ⟨V, hxV, hV⟩ := Stacks.Divisors.exists_affineOpens_ideal_eq_top
    (Stacks.ComplementIdeal.data X Z) (Stacks.ComplementIdeal.notMem_support_data X Z hxZ)
  obtain ⟨J, hJZ, hJfg, hJ1⟩ := Stacks.IdealSheaf.exists_fg_le_of_mem
    (Stacks.ComplementIdeal.data X Z) V.2 (a := 1) (hV ▸ Submodule.mem_top)
  obtain ⟨n, ι, hιfin, hn, b, hb, p, hp⟩ := h9 (Stacks.IdealSheafModules.sheaf J)
    (Stacks.IdealSheafModules.ι J) inferInstance inferInstance
    (Stacks.IdealSheafModules.isFiniteType_sheaf J hJfg)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
  have hk : 1 ≤ k := by exact_mod_cast hn
  have : Fintype ι := Fintype.ofFinite ι
  -- the unit section of `ℐ` over `V`, whose germ at `x` is outside `𝔪_x · (𝒪_X)_x`
  obtain ⟨e, he⟩ := Stacks.IdealSheafModules.exists_app_ι_eq_one J V hJ1
  have hnot : Stacks.ModuleStalk.mapFun (Stacks.IdealSheafModules.ι J) x
      (((Stacks.IdealSheafModules.sheaf J).presheaf.germ (V : X.Opens) x hxV).hom e) ∉
      Stacks.ModuleStalk.maximalSmul (unitModule X) x := by
    rw [Stacks.ModuleStalk.mapFun_germ, he]
    exact Stacks.ComplementIdeal.germ_one_notMem_maximalSmul X x (V : X.Opens) hxV
  -- one summand of the direct sum already escapes `𝔪_x · (𝒪_X)_x`
  obtain ⟨v, hv⟩ := Stacks.ModuleBicone.exists_germ_sum_of_epi hb p hp x
    (((Stacks.IdealSheafModules.sheaf J).presheaf.germ (V : X.Opens) x hxV).hom e)
  have hescape : ∃ i : ι, Stacks.ModuleStalk.mapFun
      (b.ι i ≫ p ≫ Stacks.IdealSheafModules.ι J) x (v i) ∉
      Stacks.ModuleStalk.maximalSmul (unitModule X) x := by
    by_contra hcon
    push Not at hcon
    refine hnot ?_
    have hsum : Stacks.ModuleStalk.mapFun (Stacks.IdealSheafModules.ι J) x
        (∑ i : ι, Stacks.ModuleStalk.mapFun (b.ι i ≫ p) x (v i)) =
        ∑ i : ι, Stacks.ModuleStalk.mapFun
          (b.ι i ≫ p ≫ Stacks.IdealSheafModules.ι J) x (v i) := by
      refine Eq.trans
        (map_sum (Stacks.ModuleStalk.map (Stacks.IdealSheafModules.ι J) x) _ Finset.univ) ?_
      exact Finset.sum_congr rfl fun i _ => by
        rw [Stacks.ModuleStalk.map_apply, ← Stacks.ModuleStalk.mapFun_comp, Category.assoc]
    rw [hv, hsum]
    exact Submodule.sum_mem _ fun i _ => hcon i
  obtain ⟨i, hi⟩ := hescape
  -- that summand is multiplication by a global section of `L ^⊗ k`
  obtain ⟨σ, hσ⟩ := exists_twistUnitHom_eq L (k : ℤ)
    (b.ι i ≫ p ≫ Stacks.IdealSheafModules.ι J)
  have hvalue : Stacks.ModuleStalk.mapFun (twistUnitHom L (k : ℤ) σ) x (v i) ∉
      Stacks.ModuleStalk.maximalSmul (unitModule X) x := by
    rw [hσ]
    exact hi
  obtain ⟨hxσ, haff⟩ := mem_and_isAffineOpen_nonvanishingOpen L k σ U (v i) hvalue
    fun y hyU w => by
      rw [hσ, ← Category.assoc, Stacks.ModuleStalk.mapFun_comp]
      exact Stacks.IdealSheafModules.mapFun_ι_mem_maximalSmul J
        (Scheme.IdealSheafData.support_antitone hJZ
          (Stacks.ComplementIdeal.mem_support_data X Z hyU)) _
  exact ⟨k, hk, σ, _, Stacks.NonvanishingOpen.coe_nonvanishingOpen X _ σ, hxσ, haff⟩

/-- **Clause (9) of [Stacks, Tag 01Q3] implies clause (6)**, the implication the source's cycle
runs through. It is clause (9) implies clause (1)
(`Stacks.AmpleCharacterization.isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`)
followed by clause (6) from ampleness, rather than the source's direct argument; the ingredient
the source uses for the direct route, [Stacks, Tag 01PG], is the ingredient used there. -/
@[stacks 01Q3 "clause (9) implies (6)", ega "II 4.5.5" "(d') ⇒ (b), ideals"]
theorem iSup_range_twistHom_ideal_eq_top_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal
    [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ J), Epi p) :
    ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j → J.IsQuasicoherent →
      ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤ :=
  iSup_range_twistHom_ideal_eq_top_of_isAmple L
    (isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal L h)

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (9)**, for a quasi-compact
scheme. -/
theorem isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct_ideal [CompactSpace X] :
    IsAmple X L ↔ QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ J), Epi p :=
  ⟨quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_isAmple L,
    isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal L⟩

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (8)**, for a quasi-compact
scheme: clause (8) implies clause (9), which implies clause (1). -/
theorem isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct [CompactSpace X] :
    IsAmple X L ↔ QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p :=
  ⟨Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple L,
    fun h => isAmple_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal L
      (quasiSeparatedSpace_and_exists_epi_biproduct_ideal_of_exists_epi_biproduct L h)⟩

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (7)**, for a quasi-compact scheme,
with clause (7) read exactly as the tag states it: `X` is quasi-separated and for every
quasi-coherent module `F` of finite type there is an `n₀` with `F ⊗ L ^⊗ n` *globally generated*
for all `n ≥ n₀`, nothing asked of the size of the generating family.

Ampleness delivers the clause in the stronger form with a finite generating family
(`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple`),
and that extra information is forgotten here. The converse is the tag's own cycle at this
strength: clause (7) implies clause (8)
(`quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections`), which implies
clause (9), which implies clause (1). -/
theorem isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections [CompactSpace X] :
    IsAmple X L ↔ QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          _root_.SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
            ((F ⊗ tensorPowModule X L n : X.Modules)) := by
  refine ⟨fun hL => ?_, fun h =>
    (isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct L).2
      (quasiSeparatedSpace_and_exists_epi_biproduct_of_isGeneratedByGlobalSections L h)⟩
  obtain ⟨hqs, hgen⟩ :=
    Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      L hL
  refine ⟨hqs, fun F hFqc hFft => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hgen F hFqc hFft
  exact ⟨n₀, fun n hn => ⟨(hn₀ n hn).choose⟩⟩

/-- **Clause (1) of [Stacks, Tag 01Q3] is equivalent to clause (7) in its strengthened form**,
for a quasi-compact scheme: the generating family may be taken finite, which is more than the
clause asks. The clause as the tag states it is
`isAmple_iff_quasiSeparatedSpace_and_isGeneratedByGlobalSections`; this records that the two
readings agree, the finite form being what ampleness produces and the plain form being enough to
recover it. -/
theorem isAmple_iff_quasiSeparatedSpace_and_isEventuallyGloballyGenerated [CompactSpace X] :
    IsAmple X L ↔ QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          ∃ σ : (F ⊗ tensorPowModule X L n).GeneratingSections, Finite σ.I :=
  ⟨Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple L,
    fun h => (isAmple_iff_quasiSeparatedSpace_and_exists_epi_biproduct L).2
      (quasiSeparatedSpace_and_exists_epi_biproduct_of_isEventuallyGloballyGenerated L h)⟩

end Stacks.AmpleCharacterization

end
