module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedSectionRingMap
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjUniversal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.LinearAlgebra.SymmetricPower.DegreeOneGeneration

/-!
# The morphism to projective space defined by generating sections

Let `k` be a commutative ring, `V` a `k`-module, `X` a scheme over `k`, `ℒ` an invertible
`𝒪_X`-module and `ψ : V → Γ(X, ℒ)` a `k`-linear map whose image generates `ℒ`. [Stacks, Tag 0FCY]
attaches to this datum a morphism `φ_{ℒ,ψ} : X → 𝐏(V) = Proj(Sym_k V)` together with an
isomorphism `θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ` such that `ψ` is recovered as the composite

`V → Γ(𝐏(V), 𝒪(1)) → Γ(X, φ^*𝒪(1)) → Γ(X, ℒ)`

of the universal degree-one sections, the canonical pullback of sections, and `θ`. This file
produces all three.

**On the numbering.** Tag 0FCY is an unnumbered example and has no numbered clauses; "clause (5)"
below is this library's own label for the assertions about `φ_{ℒ,ψ}`. The convention is set out in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBundle`; the numbers do not
occur in the source.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom`: the ring map
  `k → Γ(X, 𝒪_X)` of the structure morphism, and `globalSectionsModule` the resulting `k`-module
  structure on the global sections of an `𝒪_X`-module.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra`: the `k`-algebra
  structure on the section ring `Γ_*(X, ℒ)`, through its degree-zero part.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.psiAlg`: **the graded ring map
  `Sym_k V → Γ_*(X, ℒ)` extending `ψ`**, and `veroneseOfLinearMap` the same read as the datum of
  [Stacks, Tag 01N8].
* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`:
  **`φ_{ℒ,ψ} : X ⟶ 𝐏(V)`**, and
  `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.twistIsoOfGeneratingSections`
  **the isomorphism `θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ`**.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.twistIso_pullbackSectionOne`:
  **`ψ` is recovered**: `θ` carries the pullback of the universal degree-one section of `v` to
  `ψ v`, for every `v : V`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.existsUnique_classifies`: the pair
  `(φ_{ℒ,ψ}, θ)` is the unique one classifying `(ℒ, ψ)`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.GradedSections (powSections sectionRing)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)

open scoped DirectSum

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-! ### The base ring and the `k`-module structure on sections -/

section Base

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- **The ring map `k → Γ(X, 𝒪_X)` of the structure morphism** of a scheme over `k`. -/
def baseRingHom : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop).hom

/-- **The `k`-module structure on the global sections of an `𝒪_X`-module**, for `X` a scheme over
`k`: restriction of scalars along `baseRingHom`. -/
@[instance_reducible]
def globalSectionsModule (F : X.Modules) : Module k Γ(F, ⊤) :=
  Module.compHom _ (baseRingHom k X)

end Base

attribute [local instance] globalSectionsModule

variable (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

/-! ### The `k`-algebra structure on the section ring -/

/-- **The `k`-algebra structure on the section ring `Γ_*(X, ℒ)`**: scalars act through the
degree-zero part `Γ(X, 𝒪_X)` and the structure morphism. -/
@[instance_reducible]
def sectionAlgebra : Algebra k (sectionRing L) :=
  RingHom.toAlgebra ((GradedSectionRingMap.degreeZeroHom L).comp (baseRingHom k X))

attribute [local instance] sectionAlgebra

/-- The algebra map of `sectionAlgebra`, unfolded. -/
theorem algebraMap_eq (r : k) :
    algebraMap k (sectionRing L) r
      = DirectSum.of (powSections L) 0
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X r)) :=
  rfl

/-! ### The graded ring map extending `ψ` -/

/-- **The symmetric-power grading of `Sym_k V`**, `n ↦ Symⁿ_k V`. -/
abbrev grading : ℕ → Submodule k (SymmetricAlgebra k V) :=
  fun n => SymPow.symmetricPower n k V

/-- **A vector of `V` as a degree-one element of `Sym_k V`.** -/
def degreeOneElement (v : V) : grading k V 1 :=
  ⟨SymmetricAlgebra.ι k V v, by
    simpa only [SymPow.symmetricPower, pow_one] using
      LinearMap.mem_range_self (SymmetricAlgebra.ι k V) v⟩

/-- **A global section of `ℒ`, read as a global section of `ℒ ^⊗ 1`** through the left unitor. -/
def twistOneSection (x : Γ(L, ⊤)) : Γ(natTensorPow L 1, ⊤) :=
  (MorphismToProjUniversal.unitorPow L).inv.app ⊤ x

omit [Ample.IsInvertibleModule X L] in
/-- Reading `twistOneSection L x` back in `ℒ` through the left unitor gives `x`. -/
@[simp] theorem unitorPow_app_twistOneSection (x : Γ(L, ⊤)) :
    (MorphismToProjUniversal.unitorPow L).hom.app ⊤ (twistOneSection L x) = x := by
  change (MorphismToProjUniversal.unitorPow L).hom.app ⊤
      ((MorphismToProjUniversal.unitorPow L).inv.app ⊤ x) = x
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
  rfl

/-- **The nonvanishing open of a section does not depend on whether it is read in `ℒ` or in
`ℒ ^⊗ 1`.** -/
theorem nonvanishingOpen_twistOneSection (x : Γ(L, ⊤)) :
    nonvanishingOpen X (natTensorPow L 1) (twistOneSection L x)
      = nonvanishingOpen X L x :=
  Opens.ext (Stacks.Ample.nonvanishingLocus_congr (MorphismToProjUniversal.unitorPow L).symm x)

/-- **`ψ` read as a `k`-linear map into the section ring**, landing in degree one. -/
def psiLinear (ψ : V →ₗ[k] Γ(L, ⊤)) : V →ₗ[k] sectionRing L where
  toFun v := DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (ψ v)))
  map_add' v w := by
    have h1 : twistOneSection L (ψ (v + w))
        = twistOneSection L (ψ v) + twistOneSection L (ψ w) := by
      rw [map_add]
      exact map_add _ _ _
    have h2 : secOf L (twistOneSection L (ψ v) + twistOneSection L (ψ w))
        = secOf L (twistOneSection L (ψ v)) + secOf L (twistOneSection L (ψ w)) :=
      map_add (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
        (natTensorPow L 1)).symm _ _
    rw [h1, h2, map_add]
  map_smul' r v := by
    have h1 : twistOneSection L (ψ (r • v))
        = baseRingHom k X r • twistOneSection L (ψ v) := by
      rw [map_smul]
      exact Scheme.Modules.Hom.app_smul _ _ _
    change DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (ψ (r • v))))
      = GradedSectionRingMap.degreeZeroHom L (baseRingHom k X r)
        * DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (ψ v)))
    rw [h1, GradedSectionRingMap.degreeZeroHom_mul_of]

/-- **The graded ring map `Sym_k V → Γ_*(X, ℒ)` extending `ψ`.** -/
def psiAlg (ψ : V →ₗ[k] Γ(L, ⊤)) : SymmetricAlgebra k V →ₐ[k] sectionRing L :=
  SymmetricAlgebra.lift (psiLinear k V L ψ)

/-- The extension of `ψ` sends a vector `v` to `ψ v`, in degree one. -/
@[simp] theorem psiAlg_ι (ψ : V →ₗ[k] Γ(L, ⊤)) (v : V) :
    psiAlg k V L ψ (SymmetricAlgebra.ι k V v)
      = DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (ψ v))) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- **The extension of `ψ` carries `Symⁿ_k V` into degree `n`**, in the vanishing form: the value
on a degree-`n` element has no component in any other degree. -/
theorem psiAlg_component_eq_zero (ψ : V →ₗ[k] Γ(L, ⊤)) :
    ∀ (n : ℕ) (x : SymmetricAlgebra k V), x ∈ grading k V n →
      ∀ m : ℕ, m ≠ n → (psiAlg k V L ψ x) m = 0 := by
  intro n x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      intro m hm
      rw [AlgHom.commutes, algebraMap_eq]
      exact DirectSum.of_eq_of_ne _ _ _ hm
  | add x y i _ _ ihx ihy =>
      intro m hm
      rw [map_add, DirectSum.add_apply, ihx m hm, ihy m hm, add_zero]
  | mem_mul a ha i y _ ih =>
      intro m hm
      obtain ⟨v, rfl⟩ := ha
      have hy : DirectSum.of (powSections L) i ((psiAlg k V L ψ y) i) = psiAlg k V L ψ y :=
        GradedSectionRingMap.of_component_eq_self L _ ih
      have h : psiAlg k V L ψ (SymmetricAlgebra.ι k V v * y)
          = DirectSum.of (powSections L) (1 + i)
            (Stacks.GradedSections.mul (secOf L (twistOneSection L (ψ v)))
              ((psiAlg k V L ψ y) i)) :=
        calc psiAlg k V L ψ (SymmetricAlgebra.ι k V v * y)
            = psiAlg k V L ψ (SymmetricAlgebra.ι k V v) * psiAlg k V L ψ y := map_mul _ _ _
          _ = DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (ψ v)))
                * DirectSum.of (powSections L) i ((psiAlg k V L ψ y) i) := by
                rw [psiAlg_ι, hy]
          _ = DirectSum.of (powSections L) (1 + i)
                (Stacks.GradedSections.mul (secOf L (twistOneSection L (ψ v)))
                  ((psiAlg k V L ψ y) i)) :=
                Stacks.SectionProduct.of_mul_of L 1 i _ _
      rw [h]
      exact DirectSum.of_eq_of_ne _ _ _ (by omega)

/-- **The datum of [Stacks, Tag 01N8] at weight one attached to `ψ`.** -/
def veroneseOfLinearMap (ψ : V →ₗ[k] Γ(L, ⊤)) : VeroneseSections (grading k V) 1 L :=
  GradedSectionRingMap.veroneseOfRingHom L (grading k V) (psiAlg k V L ψ).toRingHom
    fun n x hx =>
      GradedSectionRingMap.of_component_eq_self L _ (psiAlg_component_eq_zero k V L ψ n x hx)

/-- **The degree-one value of that datum on a vector is `ψ` of that vector**, read in `ℒ ^⊗ 1`. -/
theorem pow_degreeOneElement (ψ : V →ₗ[k] Γ(L, ⊤)) (v : V) :
    (veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1
      = twistOneSection L (ψ v) := by
  have h := ((veroneseOfLinearMap k V L ψ).toFun_eq_pow (degreeOneElement k V v).2 1
    ⟨SymmetricAlgebra.ι k V v, by simp⟩ (pow_one _).symm).symm
  rw [h]
  change globalSection X (natTensorPow L 1) ((psiAlg k V L ψ (SymmetricAlgebra.ι k V v)) 1) = _
  rw [psiAlg_ι, DirectSum.of_eq_same]
  exact globalSection_secOf L _

/-! ### Clause (5) of [Stacks, Tag 0FCY] -/

/-- **The generating sections cover `X`**: the nonvanishing opens of the degree-one sections of
the graded map attached to `ψ` cover `X` as soon as the nonvanishing opens of the sections `ψ(v)`,
`v ∈ V`, do. -/
theorem iSup_nvOpen_eq_top (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    ⨆ f : grading k V 1, nvOpen (grading k V) (veroneseOfLinearMap k V L ψ) f = ⊤ := by
  refine eq_top_iff.mpr (hψ.ge.trans (iSup_le fun v => le_iSup_of_le (degreeOneElement k V v) ?_))
  change nonvanishingOpen X L (ψ v)
    ≤ nonvanishingOpen X (natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1)
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

/-- **The pair `(φ_{ℒ,ψ}, α)` classifying `(ℒ, ψ)` exists and is unique**, when the nonvanishing
opens of the sections `ψ(v)`, `v ∈ V`, cover `X`. -/
theorem existsUnique_classifies (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    ∃! p : Pair (grading k V) L, Classifies (grading k V) (veroneseOfLinearMap k V L ψ) p :=
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.existsUnique_classifies (grading k V)
    (SymmetricAlgebra.adjoin_symmetricPower_one_eq_top k V) (veroneseOfLinearMap k V L ψ)
    (iSup_nvOpen_eq_top k V L ψ hψ)

/-- The classifying pair, chosen from its existence and uniqueness. -/
def classifyingPair (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) : Pair (grading k V) L :=
  (existsUnique_classifies k V L ψ hψ).exists.choose

/-- The chosen pair does classify `(ℒ, ψ)`. -/
theorem classifies_classifyingPair (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    Classifies (grading k V) (veroneseOfLinearMap k V L ψ)
      (classifyingPair k V L ψ hψ) :=
  (existsUnique_classifies k V L ψ hψ).exists.choose_spec

/-- **Stacks Project, Tag 0FCY, clause (5): the morphism `φ_{ℒ,ψ} : X → 𝐏(V)` defined by a
`k`-linear map `ψ : V → Γ(X, ℒ)` whose image generates the invertible module `ℒ`.** It is the
morphism of [Stacks, Tag 01NA] attached to the graded ring map `Sym_k V → Γ_*(X, ℒ)` extending
`ψ`. -/
def morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) : X ⟶ projectiveSpaceOfModule k V :=
  (classifyingPair k V L ψ hψ).1

/-- **Stacks Project, Tag 0FCY, clause (5): the isomorphism
`θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ`.** It is the isomorphism `α` of [Stacks, Tag 01N8] at `d = 1`
followed by the left unitor `ℒ ^⊗ 1 ≅ ℒ`. -/
def twistIsoOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    pullbackTwistOne (grading k V) (morphismOfGeneratingSections k V L ψ hψ) ≅ L :=
  (classifyingPair k V L ψ hψ).2 ≪≫ MorphismToProjUniversal.unitorPow L

/-- **Stacks Project, Tag 0FCY, clause (5): `ψ` is recovered from `(φ_{ℒ,ψ}, θ)`.** For every
`v : V` the composite of the universal degree-one section of `v`, the canonical map
`Γ(𝐏(V), 𝒪(1)) → Γ(X, φ^*𝒪(1))` and `θ` is `ψ v`. -/
theorem twistIso_pullbackSectionOne (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v : V) :
    (twistIsoOfGeneratingSections k V L ψ hψ).hom.app ⊤
        (pullbackSectionOne (grading k V) (morphismOfGeneratingSections k V L ψ hψ)
          (degreeOneElement k V v))
      = ψ v := by
  change (MorphismToProjUniversal.unitorPow L).hom.app ⊤
      ((classifyingPair k V L ψ hψ).2.hom.app ⊤
        (pullbackSectionOne (grading k V) (classifyingPair k V L ψ hψ).1
          (degreeOneElement k V v)))
    = ψ v
  rw [(classifies_classifyingPair k V L ψ hψ).2.1 (degreeOneElement k V v),
    pow_degreeOneElement, unitorPow_app_twistOneSection]

end Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

end
