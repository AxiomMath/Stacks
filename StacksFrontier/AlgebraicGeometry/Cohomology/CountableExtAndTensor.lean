module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CountableOverQuasiCompactOpens
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts
public import StacksFrontier.AlgebraicGeometry.Scheme.ModulesOverOpenSlice
public import StacksFrontier.Homology.Perfect.CountableHomFromPerfect
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Countability of `H^i(U, K ⊗^L E)` and `Ext^i(E|_U, K|_U)` on a quasi-separated scheme

Let `X` be a quasi-separated scheme, let `K` be an object of `D_QCoh(𝒪_X)` whose cohomology
sheaves have countable sets of sections over affine opens, and let `E` be a perfect object of
`D(𝒪_X)`. [Stacks, Tag 0CRP] asserts that for every quasi-compact open `U` the sets
`H^i(U, K ⊗^L E)` and `Ext^i(E|_U, K|_U)` are countable. Both are proved here, with no hypothesis
beyond the source's (quasi-compactness of `X` is not even needed).

## Main results

* `Stacks.Cohomology.CountableSections.countable_shiftedHom_restrict_of_isAffineOpen`: the affine
  case of the `Ext` assertion.
* `Stacks.Cohomology.CountableSections.countable_homology_sectionComplex_homSheafComplex`: the
  cohomology over a quasi-compact open of the sections of the K-injective internal Hom complex
  `SheafHom^•(F, K)` is countable.
* `Stacks.Cohomology.CountableSections.countable_shiftedHom_restrict_of_isCompact`: the `Ext`
  assertion.
* `Stacks.Cohomology.CountableSections.countable_cohomology_derivedTensor_of_isPerfect`: the
  cohomology assertion.
* `Stacks.Cohomology.CountableSections.countable_cohomology_derivedTensor_and_ext_of_isCompact`:
  **[Stacks, Tag 0CRP]**, both assertions.

## Implementation notes

The restriction `E|_U` of the statement is restriction along the open immersion `U ⟶ X`
(`AlgebraicGeometry.Scheme.Modules.restrictFunctor`). The `Ext` groups of [Stacks, Tag 08DK] are
stated on the slice site over `U`; `shiftedHomSliceEquivRestrict` identifies the two, through
Mathlib's `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. Instance search does not cross
the `SheafOfModules X.ringCatSheaf` and `X.Modules` spellings of the category of modules, which
is why the exactness instances of `restrictFunctor U.ι` are transported along that isomorphism in
`sliceRestrictDerivedIso`. All derived categories are at `HasDerivedCategory.standard`, the model
of the Mayer--Vietoris triangle and of [Stacks, Tag 08DQ].

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Cohomology.CountableSections

section ShiftedHomTransport

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]

/-- A fully faithful functor commuting with the shifts identifies the groups of shifted
morphisms between two objects with those between their images. -/
def shiftedHomEquivOfFullyFaithful {G : C ⥤ D} [G.CommShift ℤ] (hG : G.FullyFaithful)
    (a b : C) (n : ℤ) : ShiftedHom a b n ≃ ShiftedHom (G.obj a) (G.obj b) n :=
  hG.homEquiv.trans (Iso.homCongr (Iso.refl _) ((G.commShiftIso n).app b))

/-- Isomorphic objects have the same groups of shifted morphisms. -/
def shiftedHomCongr {a a' b b' : C} (ea : a ≅ a') (eb : b ≅ b') (n : ℤ) :
    ShiftedHom a b n ≃ ShiftedHom a' b' n :=
  Iso.homCongr ea ((shiftFunctor C n).mapIso eb)

end ShiftedHomTransport

section Affine

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- Restriction along `V ≅ Spec Γ(X, V)` is an equivalence of the unbounded derived categories;
its forward functor is restriction along `hV.isoSpec.hom`. -/
def restrictIsoSpecHomDerivedEquivalence :
    DerivedCategory (Spec Γ(X, V)).Modules ≌ DerivedCategory V.toScheme.Modules :=
  Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom) (Scheme.Modules.restrictFunctor hV.isoSpec.inv)
    hV.restrictIsoSpecCompIso.symm
    ((Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.isoSpec.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hV.isoSpec.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId)

/-- The derived functor of `M ↦ (M^~)|_V` (sheafify, then transport along `V ≅ Spec Γ(X, V)`)
is fully faithful. -/
def tildeRestrictFullyFaithful :
    (tilde.functor Γ(X, V) ⋙
      Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.FullyFaithful :=
  ((StandardModel.mapDerivedCategoryFullyFaithful Γ(X, V)).comp
      (restrictIsoSpecHomDerivedEquivalence hV).fullyFaithfulFunctor).ofIso
    (Functor.mapDerivedCategoryCompIso (Iso.refl _))

/-- Sections over the whole affine scheme `V` of `(M^~)|_V` are `M`. -/
theorem countable_of_countable_sections_tildeRestrict (M : ModuleCat.{u} Γ(X, V))
    (h : Countable Γ((tilde.functor Γ(X, V) ⋙
      Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj M, ⊤)) : Countable M := by
  have h' : Countable Γ((tilde.functor Γ(X, V)).obj M, hV.isoSpec.hom ''ᵁ ⊤) := h
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso] at h'
  have : Countable ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)) := h'
  exact Function.Injective.countable (f := (tilde.isoTop M).hom)
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- **The cohomology of the presenting complex of `K|_V` is countable** when the cohomology
sheaves of `K` have countable sections over `V`. -/
theorem countable_homology_of_iso_tildeRestrict (K : DerivedCategory X.Modules)
    (hKc : ∀ i : ℤ, Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, V)))
    (e : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω)
    (i : ℤ) : Countable ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V)) i).obj ω) := by
  apply countable_of_countable_sections_tildeRestrict hV
  let φ : (Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj K) ≅
      (tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V)) i).obj ω) :=
    derivedHomologyMapIso (Scheme.Modules.restrictFunctor V.ι) K i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
        (derivedHomologyMapIso _ ω i).symm
  have h₀ : Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]; exact hKc i
  have h₁ : Countable Γ((Scheme.Modules.restrictFunctor V.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K), ⊤) := h₀
  exact Function.Injective.countable (f := (Scheme.Modules.Hom.app φ.inv ⊤).hom)
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)

include hV in
/-- **[Stacks, Tag 0CRP], the affine case.** Let `V` be an affine open of a scheme `X`, let `F` be
a perfect object of `D(𝒪_X)` and let `K` be an object of `D_QCoh(𝒪_X)` whose cohomology sheaves
have countable sections over `V`. Then every `Ext^n(F|_V, K|_V)` is countable. -/
theorem countable_shiftedHom_restrict_of_isAffineOpen
    (F K : DerivedCategory X.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ i : ℤ, Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (n : ℤ) :
    Countable (ShiftedHom ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj F)
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K) n) := by
  obtain ⟨ωF, hωF, ⟨eF⟩⟩ :=
    ComplexAndDivisorSituation.exists_isPerfect_presentation hF ⟨V, hV⟩
  obtain ⟨ωK, ⟨eK⟩⟩ := Stacks.Duality.exists_nonempty_iso_tilde_of_isQuasicoherent hV hK
  have hω := StacksDraft.Perfect.countable_hom_shift_of_isPerfect ωK
    (countable_homology_of_iso_tildeRestrict hV K hKc ωK eK) ωF hωF n
  exact Function.Injective.countable
    (f := ((shiftedHomCongr eF eK n).trans
      (shiftedHomEquivOfFullyFaithful (tildeRestrictFullyFaithful hV) ωF ωK n).symm))
    (Equiv.injective _)

end Affine

section Slice


variable {X : Scheme.{u}} (U : X.Opens)

/-- Passing from modules on the slice site over `U` to modules on the open subscheme `U` is
fully faithful on derived categories, being induced by an equivalence. -/
def overEquivDerivedFullyFaithful :
    (Scheme.Modules.overEquiv U).functor.mapDerivedCategory.FullyFaithful :=
  have := Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence
    (Scheme.Modules.overEquiv U)
  Functor.FullyFaithful.ofFullyFaithful _

/-- Restriction to the slice site over `U`, read on the open subscheme `U`, is restriction along
`U.ι`, on derived categories. -/
def sliceRestrictDerivedIso :
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapDerivedCategory ⋙
        (Scheme.Modules.overEquiv U).functor.mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  letI := Functor.additive_of_iso (Scheme.Modules.overFunctorEquiv U)
  letI := preservesFiniteLimits_of_natIso (Scheme.Modules.overFunctorEquiv U)
  letI := preservesFiniteColimits_of_natIso (Scheme.Modules.overFunctorEquiv U)
  Functor.mapDerivedCategoryCompIso (Scheme.Modules.overFunctorEquiv U)

/-- **`Ext^n(F|_U, K|_U)` does not depend on the model of the restriction to `U`**: the slice
site over `U` and the open subscheme `U` give the same groups. -/
def shiftedHomSliceEquivRestrict (F K : DerivedCategory X.Modules) (n : ℤ) :
    ShiftedHom ((SheafOfModules.overFunctor X.ringCatSheaf U).mapDerivedCategory.obj F)
        ((SheafOfModules.overFunctor X.ringCatSheaf U).mapDerivedCategory.obj K) n ≃
      ShiftedHom ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj F)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) n :=
  (shiftedHomEquivOfFullyFaithful (overEquivDerivedFullyFaithful U) _ _ n).trans
    (shiftedHomCongr ((sliceRestrictDerivedIso U).app F) ((sliceRestrictDerivedIso U).app K) n)

end Slice

section MayerVietoris

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

open Stacks.Cohomology.SpaceMayerVietoris (ModuleSheaves)

variable {X : Scheme.{u}}

/-- On a K-injective complex `I`, the cohomology of `RΓ(U, I)` is the cohomology of the
complex of sections of `I` over `U`. -/
def homologyDerivedSectionsOpenIsoOfIsKInjective (U : X.Opens)
    (I : CochainComplex (ModuleSheaves X.toRingedSpace) ℤ) [I.IsKInjective] (n : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedSectionsOpen X.toRingedSpace U).obj (DerivedCategory.Q.obj I)) ≅
      (Stacks.SheafOfModules.sectionComplex X.sheaf I U).homology n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      (asIso (((sectionsData X.toRingedSpace).unit U).app I)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app _

/-- Countability of an abelian group passes along an isomorphism. -/
theorem _root_.AddCommGrpCat.countable_of_iso {A B : AddCommGrpCat.{u}} (e : A ≅ B)
    (h : Countable A) : Countable B :=
  Function.Injective.countable ((AddCommGrpCat.mono_iff_injective e.inv).1 inferInstance)

/-- The section cohomology of the internal Hom complex over `U` is countable iff the
corresponding `Ext` group of the restrictions to `U` is. -/
private theorem countable_homology_sectionComplex_homSheafComplex_iff
    (F K : DerivedCategory X.Modules) (U : X.Opens) (n : ℤ) :
    Countable ((Stacks.SheafOfModules.sectionComplex X.sheaf
      (Stacks.SheafOfModules.homSheafComplex X.sheaf F K) U).homology n) ↔
    Countable (ShiftedHom ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj F)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) n) :=
  Equiv.countable_iff
    ((Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv X.sheaf F K U n).toEquiv.trans
      (shiftedHomSliceEquivRestrict U F K n))

/-- **`Ext^n(F|_U, K|_U)` is countable over every quasi-compact open, in its section form.** Let
`X` be a quasi-separated scheme, let `F` be perfect and let `K` be in `D_QCoh(𝒪_X)` with cohomology
sheaves having countable sections over affine opens. Then the cohomology of the sections over a
quasi-compact open `U` of the internal Hom complex `SheafHom^•(F, K)` of chosen representatives
is countable in every degree. That complex is K-injective, so its section cohomology over `U` is
both `H^n(U, RSheafHom(F, K))` and `Ext^n(F|_U, K|_U)` ([Stacks, Tag 08DK]). -/
theorem countable_homology_sectionComplex_homSheafComplex [QuasiSeparatedSpace X]
    (F K : DerivedCategory X.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (n : ℤ) :
    Countable ((Stacks.SheafOfModules.sectionComplex X.sheaf
      (Stacks.SheafOfModules.homSheafComplex X.sheaf F K) U).homology n) := by
  let I := Stacks.SheafOfModules.homSheafComplex X.sheaf F K
  have : I.IsKInjective := Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf F K
  have haffine : ∀ V : X.Opens, IsAffineOpen V →
      AddCommGrpCat.HasCountableCohomology
        ((derivedSectionsOpen X.toRingedSpace V).obj (DerivedCategory.Q.obj I)) := by
    intro V hV i
    have h₁ := countable_shiftedHom_restrict_of_isAffineOpen hV F K hF hK (hKc V hV) i
    have h₂ := (countable_homology_sectionComplex_homSheafComplex_iff F K V i).2 h₁
    exact AddCommGrpCat.countable_of_iso
      (homologyDerivedSectionsOpenIsoOfIsKInjective V I i).symm h₂
  exact AddCommGrpCat.countable_of_iso (homologyDerivedSectionsOpenIsoOfIsKInjective U I n)
    (countable_cohomology_of_isCompact X (DerivedCategory.Q.obj I) haffine U hU n)

/-- **The `Ext` half of [Stacks, Tag 0CRP].** For a quasi-separated scheme `X`, a perfect `F`, and
`K` in `D_QCoh(𝒪_X)` whose cohomology sheaves have countable sections over affine opens, every
`Ext^n(F|_U, K|_U)` over a quasi-compact open `U` is countable. -/
theorem countable_shiftedHom_restrict_of_isCompact [QuasiSeparatedSpace X]
    (F K : DerivedCategory X.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (n : ℤ) :
    Countable (ShiftedHom ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj F)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) n) := by
  exact (countable_homology_sectionComplex_homSheafComplex_iff F K U n).1
    (countable_homology_sectionComplex_homSheafComplex F K hF hK hKc U hU n)

/-- `K ⊗^L F ≅ RSheafHom(F^∨, K)` as the class of the K-injective internal Hom complex, for `F`
perfect: the bidual isomorphism `F ≅ (F^∨)^∨` followed by the third assertion of
[Stacks, Tag 08DQ] at the perfect object `F^∨`. -/
def derivedTensorIsoHomSheafObjectDual (F K : DerivedCategory X.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) :
    ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).obj F ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.homSheafComplex X.sheaf
        (Stacks.SheafOfModules.derivedDual X.sheaf F) K) :=
  ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).mapIso
      (Stacks.SheafOfModules.derivedBidualIsoOfIsPerfectSpace X.toRingedSpace F hF) ≪≫
    (Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace X.toRingedSpace
        (Stacks.SheafOfModules.derivedDual X.sheaf F)
        (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace
          F hF)).app K ≪≫
    Stacks.SheafOfModules.homSheafObjectIso X.sheaf _ K

/-- **The cohomology half of [Stacks, Tag 0CRP].** Under the same hypotheses every
`H^n(U, K ⊗^L F)` over a quasi-compact open `U` is countable. -/
theorem countable_cohomology_derivedTensor_of_isPerfect [QuasiSeparatedSpace X]
    (F K : DerivedCategory X.Modules)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (n : ℤ) :
    Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedSectionsOpen X.toRingedSpace U).obj
        (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).obj F))) := by
  let Fd := Stacks.SheafOfModules.derivedDual X.sheaf F
  have hFd : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) Fd :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace F hF
  have := Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf Fd K
  exact AddCommGrpCat.countable_of_iso
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((derivedSectionsOpen X.toRingedSpace U).mapIso
        (derivedTensorIsoHomSheafObjectDual F K hF))).symm
    (AddCommGrpCat.countable_of_iso
      (homologyDerivedSectionsOpenIsoOfIsKInjective U
        (Stacks.SheafOfModules.homSheafComplex X.sheaf Fd K) n).symm
      (countable_homology_sectionComplex_homSheafComplex Fd K hFd hK hKc U hU n))

/-- **[Stacks, Tag 0CRP].** Let `X` be a quasi-compact and quasi-separated scheme. Let `K` be an
object of `D_QCoh(𝒪_X)` such that the cohomology sheaves `H^i(K)` have countable sets of
sections over affine opens. Then for any quasi-compact open `U ⊆ X` and any perfect object `E`
of `D(𝒪_X)` the sets `H^i(U, K ⊗^L E)` and `Ext^i(E|_U, K|_U)` are countable.

Quasi-compactness of `X` is not used, so it is not assumed: the statement holds on every
quasi-separated scheme. `H^i(U, -)` is the cohomology of the right derived functor of sections
over `U` (`derivedSectionsOpen`), `⊗^L` is the derived tensor product of `D(𝒪_X)`, perfectness
is that of [Stacks, Tag 08CM], `E|_U` and `K|_U` are the restrictions along the open immersion
`U ⟶ X`, and `Ext^i` is the group of degree-`i` morphisms in `D(𝒪_U)`. -/
@[stacks 0CRP]
theorem countable_cohomology_derivedTensor_and_ext_of_isCompact [QuasiSeparatedSpace X]
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKc : ∀ V : X.Opens, IsAffineOpen V → ∀ i : ℤ,
      Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj K, V))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedSectionsOpen X.toRingedSpace U).obj
          (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).obj E))) ∧
      Countable (ShiftedHom ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) i) :=
  ⟨countable_cohomology_derivedTensor_of_isPerfect E K hE hK hKc U hU i,
    countable_shiftedHom_restrict_of_isCompact E K hE hK hKc U hU i⟩

end MayerVietoris

end Stacks.Cohomology.CountableSections

end
