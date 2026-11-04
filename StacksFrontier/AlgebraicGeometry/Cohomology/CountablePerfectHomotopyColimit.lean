module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CountableSectionsOfPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.CountableCellTower
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Derived colimits of perfect complexes on a scheme with countable rings of sections

Let `X` be a quasi-compact and quasi-separated scheme whose rings of sections `Γ(V, 𝒪_X)` over
affine opens are countable, and let `K` be an object of `D_QCoh(𝒪_X)`. Then
[Stacks, Tag 0CRQ] asserts that the following are equivalent:

1. `K = hocolim Eₙ` with `Eₙ` a perfect object of `D(𝒪_X)`, and
2. the cohomology sheaves `H^i(K)` have countable sets of sections over affine opens.

## Main results

* `Stacks.Cohomology.CountableSections.countable_hom_shift_of_isPerfect`: for `F` perfect and
  `K` in `D_QCoh(𝒪_X)` with countable sections of cohomology over affines, every
  `Hom(F⟦m⟧, K)` is countable — the `Ext` half of [Stacks, Tag 0CRP] on all of `X`, at every
  model of the derived category.
* `Stacks.Cohomology.CountableSections.countable_sections_colimit_of_isQuasicoherent`: a
  sequential colimit of quasi-coherent modules with countable sections over an affine open has
  countable sections there.
* `Stacks.Cohomology.CountableSections.countable_sections_homology_of_isHomotopyColimit`: the
  implication (1) ⇒ (2).
* `Stacks.Cohomology.CountableSections.exists_isHomotopyColimit_isPerfect_of_countable`: the
  implication (2) ⇒ (1).
* `Stacks.Cohomology.CountableSections.exists_isHomotopyColimit_isPerfect_iff_countable`:
  **[Stacks, Tag 0CRQ]**.

## Implementation notes

All statements are at an arbitrary model `[HasDerivedCategory X.Modules]` of the derived
category. Compactness, direct sums and the generator live at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; the countability of `Ext` groups is
computed at `HasDerivedCategory.standard`, the model of [Stacks, Tag 0CRP]. Both are reached by
the comparison equivalence `StacksDraft.DerivedModel.modelEquiv`, which is triangulated, commutes
with the shift, cohomology and perfectness.

## References

* [Stacks Project, Tag 0CRQ](https://stacks.math.columbia.edu/tag/0CRQ)
* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
* [Stacks Project, Tag 0CRM](https://stacks.math.columbia.edu/tag/0CRM)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe w z u

namespace Stacks.Cohomology.CountableSections

/-! ### Countable direct sums in `D(𝒪_X)` -/

section DirectSums

variable (X : Scheme.{u})

/-- Sequential colimits of `𝒪_X`-modules are exact. -/
instance hasExactColimitsOfShape_nat_modules : HasExactColimitsOfShape ℕ X.Modules :=
  have := AB5OfSize_of_univLE.{0, 0, u, u} X.Modules
  inferInstance

/-- `𝒪_X`-modules have exact countable direct sums. -/
theorem hasExactCountableDirectSums_modules : HasExactCountableDirectSums X.Modules :=
  have := AB5OfSize_of_univLE.{0, 0, u, u} X.Modules
  ⟨⟨fun _ _ => inferInstance⟩, fun _ _ => ⟨inferInstance, inferInstance⟩⟩

/-- **`D(𝒪_X)` has countable direct sums, at every model** ([Stacks, Tag 0A5L]). -/
instance hasCountableCoproducts_derivedCategory_modules [HasDerivedCategory.{w} X.Modules] :
    HasCountableCoproducts (DerivedCategory X.Modules) :=
  derivedCategory_hasCountableCoproducts X.Modules (hasExactCountableDirectSums_modules X)

/-- The cohomology sheaf functors of `D(𝒪_X)` commute with countable direct sums, at every
model. -/
instance preservesColimitsOfShape_discrete_nat_homologyFunctor_modules
    [HasDerivedCategory.{w} X.Modules] (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor X.Modules i) :=
  have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
    X.Modules (J := ULift.{u} ℕ) i
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

end DirectSums

/-! ### Countability of `Ext` groups at every model -/

section Ext

/-- Countability of `Hom(A⟦m⟧, B)` descends along a fully faithful functor commuting with shifts. -/
private theorem countable_hom_shift_of_fullyFaithful {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (hF : F.FullyFaithful)
    (A B : C) (m : ℤ) (hc : Countable ((F.obj A)⟦m⟧ ⟶ F.obj B)) : Countable (A⟦m⟧ ⟶ B) :=
  @Countable.of_equiv _ _ hc (hF.homEquiv.trans
    (Iso.homCongr ((F.commShiftIso m).app A) (Iso.refl _))).symm

/-- Countability of `Hom(A⟦m⟧, B)` passes from one model of the derived category to another. -/
theorem countable_hom_shift_of_modelEquiv {C : Type*} [Category C] [Abelian C]
    (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (A B : @DerivedCategory C _ _ h₁) (m : ℤ)
    (hc : Countable (((StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj A)⟦m⟧ ⟶
      (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj B)) :
    Countable (A⟦m⟧ ⟶ B) := by
  let e := StacksDraft.DerivedModel.modelEquiv h₁ h₂
  let : e.functor.CommShift ℤ := StacksDraft.Perfect.derivedEquivalenceCommShift h₁ h₂
  exact countable_hom_shift_of_fullyFaithful e.functor e.fullyFaithfulFunctor A B m hc

/-- Restriction along the open immersion `⊤ ⟶ X` is an equivalence of abelian categories, hence
induces a fully faithful functor on derived categories. -/
def topRestrictDerivedFullyFaithful (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{z} (⊤ : X.Opens).toScheme.Modules] :
    (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).mapDerivedCategory.FullyFaithful :=
  haveI : IsIso (⊤ : X.Opens).ι := (Scheme.topIso X).isIso_hom
  (Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι)
    (Scheme.Modules.restrictFunctor (inv (⊤ : X.Opens).ι))
    ((Scheme.Modules.restrictFunctorComp (inv (⊤ : X.Opens).ι) (⊤ : X.Opens).ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id _) ≪≫
        Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp (⊤ : X.Opens).ι (inv (⊤ : X.Opens).ι)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id _) ≪≫
        Scheme.Modules.restrictFunctorId)).fullyFaithfulFunctor

/-- The `Ext` half of [Stacks, Tag 0CRP] on all of `X`, at the standard model. -/
theorem countable_shiftedHom_of_isPerfect_standard {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] :
    letI := HasDerivedCategory.standard X.Modules
    ∀ (F K : DerivedCategory X.Modules),
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace
        (HasDerivedCategory.standard X.Modules) F →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
      (∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
        Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V)) →
      ∀ n : ℤ, Countable (ShiftedHom F K n) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (⊤ : X.Opens).toScheme.Modules
  intro F K hF hK hKc n
  have := countable_shiftedHom_restrict_of_isCompact F K hF hK hKc ⊤
    (by simpa using isCompact_univ) n
  exact Countable.of_equiv _
    (shiftedHomEquivOfFullyFaithful (topRestrictDerivedFullyFaithful X) F K n).symm

/-- **`Hom(F⟦m⟧, K)` is countable** for `F` perfect and `K` in `D_QCoh(𝒪_X)` whose cohomology
sheaves have countable sections over affine opens, on a quasi-compact quasi-separated scheme, at
every model of the derived category. This is the `Ext` half of [Stacks, Tag 0CRP] for `U = X`. -/
theorem countable_hom_shift_of_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (F K : DerivedCategory X.Modules)
    (hF : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h F)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V)) (m : ℤ) :
    Countable (F⟦m⟧ ⟶ K) := by
  refine countable_hom_shift_of_modelEquiv h (HasDerivedCategory.standard X.Modules) F K m ?_
  have hF' :=
    (isPerfect_modelEquiv_functor_obj_iff h (HasDerivedCategory.standard X.Modules) F).2 hF
  have hK' : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) i).obj
      ((StacksDraft.DerivedModel.modelEquiv h (HasDerivedCategory.standard X.Modules)).functor.obj
        K)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((StacksDraft.DerivedModel.modelHomologyFunctorIso h
        (HasDerivedCategory.standard X.Modules) i).app K).symm (hK i)
  have hKc' := fun V hV i => countable_sections_of_iso
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso h
      (HasDerivedCategory.standard X.Modules) i).app K).symm V (hKc V hV i)
  have hc := countable_shiftedHom_of_isPerfect_standard _ _ hF' hK' hKc' (-m)
  exact @Countable.of_equiv _ _ hc ((shiftEquiv (@DerivedCategory X.Modules _ _
    (HasDerivedCategory.standard X.Modules)) m).toAdjunction.homEquiv _ _).symm

end Ext

/-! ### Sections of a sequential colimit of quasi-coherent modules -/

section Colimit

/-- On a spectrum, a sequential colimit of quasi-coherent modules with countable global sections
has countable global sections. -/
theorem countable_sections_top_of_isColimit_spec (R : CommRingCat.{u})
    {D : ℕ ⥤ (Spec R).Modules} (hD : ∀ n, (D.obj n).IsQuasicoherent)
    (hDc : ∀ n, Countable Γ(D.obj n, ⊤)) {c : Cocone D} (hc : IsColimit c) :
    Countable Γ(c.pt, ⊤) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let D' : ℕ ⥤ P.FullSubcategory := P.lift D hD
  let G : ℕ ⥤ ModuleCat.{u} R := D' ⋙ (tildeEquiv (R := R)).inverse
  have iso : D ≅ G ⋙ tilde.functor R :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D' (tildeEquiv (R := R)).counitIso.symm) P.ι
  have h1 : IsColimit ((tilde.functor R).mapCocone (colimit.cocone G)) :=
    isColimitOfPreserves _ (colimit.isColimit G)
  have h2 := (IsColimit.precomposeHomEquiv iso _).symm h1
  let ept : c.pt ≅ (tilde.functor R).obj (colimit G) := hc.coconePointUniqueUpToIso h2
  have hG : ∀ n, Countable (G.obj n) := fun n => by
    have h₁ : Countable Γ((G ⋙ tilde.functor R).obj n, ⊤) :=
      countable_sections_of_iso (iso.app n) ⊤ (hDc n)
    have h₂ : Countable ((modulesSpecToSheaf.obj (tilde (G.obj n))).presheaf.obj (op ⊤)) := h₁
    exact Function.Injective.countable (f := (tilde.isoTop (G.obj n)).hom)
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hcolim : Countable (colimit G : ModuleCat.{u} R) := by
    have : ∀ n, Countable (ToType (G.obj n)) := hG
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
      preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
    exact Function.Surjective.countable
      (Concrete.from_union_surjective_of_isColimit G (colimit.isColimit G))
  have h₃ : Countable ((modulesSpecToSheaf.obj (tilde (colimit G))).presheaf.obj (op ⊤)) :=
    Function.Injective.countable (f := (tilde.isoTop (colimit G)).inv)
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact countable_sections_of_iso ept.symm ⊤ h₃

/-- **Sections over an affine open of a sequential colimit of quasi-coherent modules are
countable** when the sections of each term are. -/
theorem countable_sections_colimit_of_isQuasicoherent {X : Scheme.{u}} (M : ℕ ⥤ X.Modules)
    (hM : ∀ n, (M.obj n).IsQuasicoherent) {V : X.Opens} (hV : IsAffineOpen V)
    (hMc : ∀ n, Countable Γ(M.obj n, V)) : Countable Γ(colimit M, V) := by
  let r₁ := Scheme.Modules.restrictFunctor V.ι
  let r₂ := Scheme.Modules.restrictFunctor hV.isoSpec.inv
  let D := M ⋙ r₁ ⋙ r₂
  have hD : ∀ n, (D.obj n).IsQuasicoherent := fun n =>
    have := hM n
    have := Scheme.Modules.isQuasicoherent_restrictFunctor V.ι (M.obj n)
    Scheme.Modules.isQuasicoherent_restrictFunctor hV.isoSpec.inv (r₁.obj (M.obj n))
  have hsec : ∀ N : X.Modules, Countable Γ(N, V) ↔ Countable Γ((r₁ ⋙ r₂).obj N, ⊤) := fun N => by
    have h₀ : Countable Γ(N, V) ↔ Countable Γ(N, V.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]
    have h₂ : Countable Γ(r₁.obj N, ⊤) ↔ Countable Γ(r₁.obj N, hV.isoSpec.inv ''ᵁ ⊤) := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact h₀.trans h₂
  exact (hsec _).2 (countable_sections_top_of_isColimit_spec Γ(X, V) hD
    (fun n => (hsec _).1 (hMc n))
    (isColimitOfPreserves (r₁ ⋙ r₂) (colimit.isColimit M)))

end Colimit

/-! ### The implication (1) ⇒ (2) -/

/-- **[Stacks, Tag 0CRQ], (1) ⇒ (2).** Let `X` be a scheme whose rings of sections over affine
opens are countable, and let `K = hocolim Eₙ` with each `Eₙ` perfect. Then the cohomology sheaves
of `K` have countable sets of sections over affine opens. -/
theorem countable_sections_homology_of_isHomotopyColimit {X : Scheme.{u}}
    [h : HasDerivedCategory.{w} X.Modules]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (F : ℕ ⥤ DerivedCategory X.Modules) [HasCoproduct F.obj]
    (hF : ∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n))
    {K : DerivedCategory X.Modules} (hK : IsHomotopyColimit F K)
    (V : X.Opens) (hV : IsAffineOpen V) (i : ℤ) :
    Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V) := by
  obtain ⟨p, q, hT⟩ := hK
  obtain ⟨e, -⟩ := exists_iso_colimit_of_isHomotopyColimit F
    (DerivedCategory.homologyFunctor X.Modules i) p q hT
  refine countable_sections_of_iso e V
    (countable_sections_colimit_of_isQuasicoherent _ (fun n => ?_) hV
      (fun n => countable_sections_homology_of_isPerfect hO _ (hF n) V hV i))
  have hp := (isPerfect_modelEquiv_functor_obj_iff h (HasDerivedCategory.standard X.Modules)
    (F.obj n)).2 (hF n)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso h
      (HasDerivedCategory.standard X.Modules) i).app (F.obj n))
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _ hp i)

/-! ### The implication (2) ⇒ (1) -/

/-- The implication (2) ⇒ (1) at the locally small model, from countable morphism groups: if `K` is
in `D_QCoh(𝒪_X)` and every `Hom(G⟦m⟧, K)` with `G` perfect is countable, then `K` is a derived
colimit of perfect objects. -/
theorem exists_isHomotopyColimit_isPerfect_of_countable_hom_locallySmall {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKG : ∀ G : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G →
        ∀ m : ℤ, Countable (G⟦m⟧ ⟶ K)) :
    ∃ F : ℕ ⥤ DerivedCategory X.Modules,
      (∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (F.obj n)) ∧
        IsHomotopyColimit F K := by
  obtain ⟨ι, hι, E, hEc, hEgen⟩ := Stacks.Duality.QcqsGeneration.exists_finite_compact_generators X
  have : Countable ι := Finite.to_countable
  have := Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory X
  have : ∀ i, IsCompactObject.{u} (E i) := hEc
  let ιQ := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  have hEp : ∀ i, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (E i).obj :=
    fun i => Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs X (E i) (hEc i)
  have hcount : ∀ (A B : Stacks.Duality.quasiCoherentDerivedCategory X) (m : ℤ),
      Countable (A.obj⟦m⟧ ⟶ B.obj) → Countable (A⟦m⟧ ⟶ B) := fun A B m hc =>
    countable_hom_shift_of_fullyFaithful ιQ (ObjectProperty.fullyFaithfulι _) A B m hc
  have hEE : ∀ (i j : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ E j) := fun i j m =>
    hcount _ _ m (countable_hom_shift_of_isPerfect (E i).obj (E j).obj (hEp i)
      (fun k => (E j).property k)
      (fun V hV k => countable_sections_homology_of_isPerfect hO _ (hEp j) V hV k) m)
  let K' : Stacks.Duality.quasiCoherentDerivedCategory X := ⟨K, hK⟩
  have hK' : HasCountableCells E K' := fun i m => hcount _ K' m (hKG _ (hEp i) m)
  obtain ⟨F, hFc, hF⟩ :=
    exists_isHomotopyColimit_isCompactObject_of_hasCountableCells hEgen hEE K' hK'
  refine ⟨F ⋙ ιQ, fun n => Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs X
    (F.obj n) (hFc n), ?_⟩
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) ιQ :=
    have := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X
      (ULift.{u} ℕ)
    inferInstance
  have : PreservesColimitsOfShape (Discrete ℕ) ιQ :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  exact hF.map ιQ

/-- **A derived colimit of perfect objects, from countable morphism groups.** Let `X` be a
quasi-compact and quasi-separated scheme whose rings of sections over affine opens are countable,
and let `K` be an object of `D_QCoh(𝒪_X)` such that `Hom(G⟦m⟧, K)` is countable for every perfect
`G` and every `m`. Then `K = hocolim Eₙ` for a system of perfect objects `Eₙ` of `D(𝒪_X)`, at every
model. -/
theorem exists_isHomotopyColimit_isPerfect_of_countable_hom {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKG : ∀ G : DerivedCategory X.Modules,
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h G →
        ∀ m : ℤ, Countable (G⟦m⟧ ⟶ K)) :
    ∃ F : ℕ ⥤ DerivedCategory X.Modules,
      (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
        IsHomotopyColimit F K := by
  let e := StacksDraft.DerivedModel.modelEquiv (Scheme.Modules.hasDerivedCategory X) h
  let : e.functor.CommShift ℤ :=
    StacksDraft.Perfect.derivedEquivalenceCommShift (Scheme.Modules.hasDerivedCategory X) h
  let : ∀ n : ℤ, (shiftFunctor (@DerivedCategory X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X)) n).Additive := by
    let := Scheme.Modules.hasDerivedCategory X; infer_instance
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory X.Modules) n).Additive := inferInstance
  have : e.functor.IsTriangulated := StacksDraft.Perfect.derivedEquivalence_isTriangulated
    (Scheme.Modules.hasDerivedCategory X) h
  let K₀ := e.inverse.obj K
  let φ : ∀ i : ℤ, (@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) i).obj K₀ ≅
      (DerivedCategory.homologyFunctor X.Modules i).obj K := fun i =>
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso (Scheme.Modules.hasDerivedCategory X) h
      i).app K₀).symm ≪≫ (DerivedCategory.homologyFunctor X.Modules i).mapIso (e.counitIso.app K)
  obtain ⟨F, hFp, hF⟩ := exists_isHomotopyColimit_isPerfect_of_countable_hom_locallySmall hO K₀
    (fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (φ i).symm (hK i))
    (fun G hG m => by
      have hc := hKG (e.functor.obj G)
        ((isPerfect_modelEquiv_functor_obj_iff (Scheme.Modules.hasDerivedCategory X) h G).2 hG) m
      exact @Countable.of_equiv _ _ hc ((Iso.homCongr ((e.functor.commShiftIso m).app G).symm
        (Iso.refl _)).trans (e.toAdjunction.homEquiv _ _)))
  refine ⟨F ⋙ e.functor, fun n => (isPerfect_modelEquiv_functor_obj_iff
    (Scheme.Modules.hasDerivedCategory X) h _).2 (hFp n), ?_⟩
  obtain ⟨c, hc⟩ := (hF.map e.functor).exists_isHomotopyColimitWith
  exact (hc.of_iso (e.counitIso.app K)).isHomotopyColimit

/-- **[Stacks, Tag 0CRQ], (2) ⇒ (1).** Let `X` be a quasi-compact and quasi-separated scheme
whose rings of sections over affine opens are countable, and let `K` be an object of
`D_QCoh(𝒪_X)` whose cohomology sheaves have countable sets of sections over affine opens. Then
`K = hocolim Eₙ` for a system of perfect objects `Eₙ` of `D(𝒪_X)`. -/
theorem exists_isHomotopyColimit_isPerfect_of_countable {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V)) :
    ∃ F : ℕ ⥤ DerivedCategory X.Modules,
      (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
        IsHomotopyColimit F K :=
  exists_isHomotopyColimit_isPerfect_of_countable_hom hO K hK
    fun G hG m => countable_hom_shift_of_isPerfect G K hG hK hKc m

/-! ### The tag -/

/-- **[Stacks, Tag 0CRQ].** Let `X` be a quasi-compact and quasi-separated scheme such that the
sets of sections of `𝒪_X` over affine opens are countable. Let `K` be an object of
`D_QCoh(𝒪_X)`. The following are equivalent:

1. `K = hocolim Eₙ` with `Eₙ` a perfect object of `D(𝒪_X)`, and
2. the cohomology sheaves `H^i(K)` have countable sets of sections over affine opens.

`hocolim` is the derived colimit of [Stacks, Tag 090Z], perfectness is that of
[Stacks, Tag 08CM], and the derived category is an arbitrary model of `D(𝒪_X)`. -/
@[stacks 0CRQ]
theorem exists_isHomotopyColimit_isPerfect_iff_countable {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    (∃ F : ℕ ⥤ DerivedCategory X.Modules,
      (∀ n, @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h (F.obj n)) ∧
        IsHomotopyColimit F K) ↔
      ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
        Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V) :=
  ⟨fun ⟨F, hFp, hF⟩ V hV i => countable_sections_homology_of_isHomotopyColimit hO F hFp hF V hV i,
    exists_isHomotopyColimit_isPerfect_of_countable hO K hK⟩

end Stacks.Cohomology.CountableSections

end
