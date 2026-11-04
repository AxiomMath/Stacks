module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedAdjunctionUnitFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.InverseImageInjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.EtaleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyAlongAnAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyAlongAnAdjunctionSupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Comparison of étale and pro-étale cohomology

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale site into the small pro-étale site, with inverse image `ε⁻¹` and
direct image `ε_*` on abelian sheaves. This file proves that `ε⁻¹` is fully faithful on bounded
below derived categories, and that it does not change cohomology:

* for an abelian sheaf `ℱ` on `X_étale`, `Rε_*(ε⁻¹ℱ) = ℱ` (Stacks 099V (1));
* for `K ∈ D⁺(X_étale)` the map `K ⟶ Rε_* ε⁻¹ K` is an isomorphism (Stacks 099V (2));
* `H^i(X_étale, ℱ) = H^i(X_proétale, ε⁻¹ℱ)` for all `i` (Stacks 099W (1));
* `RΓ(X_étale, K) = RΓ(X_proétale, ε⁻¹K)` for `K ∈ D⁺(X_étale)` (Stacks 099W (2)).

## Main definitions

* `AlgebraicGeometry.ProEtale.constantSheafCompEpsilonInverseImageIso`: `ε⁻¹ℤ = ℤ`.
* `AlgebraicGeometry.ProEtale.epsilonDirectImageCompΓIso`: `Γ(X_étale, ε_* -) = Γ(X_proétale, -)`.
* `AlgebraicGeometry.ProEtale.epsilonInverseImageCompFunctorHIso`: **Stacks 099W (1)**.
* `AlgebraicGeometry.ProEtale.rightDerivedFunctorPlusΓIso`: **Stacks 099W (2)**.

## Main results

* `AlgebraicGeometry.Scheme.preservesFiniteLimits_of_etaleToProetale_adjunction`: every left
  adjoint of `ε_*` on abelian sheaves is left exact, so `ε⁻¹` is exact.
* `AlgebraicGeometry.ProEtale.isZero_rightDerived_epsilonDirectImage_of_injective`: the higher
  direct images `R^q ε_*(ε⁻¹ℐ)` vanish for an injective abelian sheaf `ℐ` on `X_étale`.
* `AlgebraicGeometry.ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage`:
  **Stacks 099V (1)**.
* `AlgebraicGeometry.ProEtale.isIso_epsilonAdjunction_rightDerivedFunctorPlus_unit`:
  **Stacks 099V (2)**.

## Implementation notes

`ε⁻¹` and `ε_*` are `AlgebraicGeometry.ProEtale.epsilonInverseImage` and
`AlgebraicGeometry.ProEtale.epsilonDirectImage`, with the adjunction
`AlgebraicGeometry.ProEtale.epsilonAdjunction`. On bounded below derived categories `ε⁻¹` is the
right derived functor `Functor.rightDerivedFunctorPlus` of the exact functor `ε⁻¹`, that is,
`ε⁻¹` applied termwise; `Rε_*` is `Functor.rightDerivedFunctorPlus` of `ε_*`, and the map
`K ⟶ Rε_* ε⁻¹ K` is the unit of the derived adjunction
`CategoryTheory.Adjunction.rightDerivedFunctorPlus`.

The higher direct image `R^q ε_*(ε⁻¹ℐ)` is the sheafification of `U ↦ H^q(U_proétale, ε⁻¹ℐ)`
(Stacks 072W), so it vanishes because the latter vanishes on the affine objects of `X_étale`
(Stacks 099U), which cover every object. The rest of the proof of 099V is
`CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlus_unit`: represent `K` by a bounded below
complex of injectives `ℐ^•`; `Rε_* ε⁻¹ ℐ^•` is computed by `ε_* ε⁻¹ ℐ^• = ℐ^•` by Leray's
acyclicity lemma and Stacks 099T.

Cohomology of an abelian sheaf is `CategoryTheory.Sheaf.functorH`, `Ext` out of the constant
sheaf `ℤ`. Part (1) of 099W is read off from full faithfulness of `ε⁻¹` on bounded below derived
categories, which makes `ε⁻¹` bijective on `Ext` groups, together with `ε⁻¹ℤ = ℤ`; part (2) is the
Leray identification `RΓ(X_proétale, -) = RΓ(X_étale, Rε_* -)` — `ε_*` preserves injectives, its
left adjoint being exact — composed with 099V (2). Global sections are Mathlib's
`CategoryTheory.Sheaf.Γ`.

## References

* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
* [Stacks Project, Tag 099W](https://stacks.math.columbia.edu/tag/099W)
* [Stacks Project, Tag 099U](https://stacks.math.columbia.edu/tag/099U)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Exactness of the inverse image -/

namespace Scheme

variable (X : Scheme.{u})

/-- The left Kan extension along the inclusion of the small étale category into the small
pro-étale category is left exact on abelian presheaves: the inclusion preserves finite limits, so
the comma categories computing the extension pointwise are filtered, and filtered colimits of
abelian groups commute with finite limits. -/
theorem preservesFiniteLimits_lan_etaleToProetale :
    PreservesFiniteLimits (X.etaleToProetale.op.lan :
      (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have (Y : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      AddCommGrpCat.{max (u + 1) v} :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) v} _ _
  exact Stacks.Topology.lan_preservesFiniteLimits_of_flat _ (fun Y ↦ inferInstance)

/-- **The inverse image `ε⁻¹` of abelian sheaves is left exact.** Every left adjoint of the
restriction `ε_*` of abelian pro-étale sheaves to the small étale site preserves finite limits:
it is the sheafification of a left exact left Kan extension. -/
theorem preservesFiniteLimits_of_etaleToProetale_adjunction
    {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
    (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X)) :
    PreservesFiniteLimits L := by
  have := preservesFiniteLimits_lan_etaleToProetale.{v} X
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have := Functor.sheafPullbackConstruction.preservesFiniteLimits X.etaleToProetale
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology (Scheme.ProEt.topology X)
  exact preservesFiniteLimits_of_natIso
    ((X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X)).leftAdjointUniq adj)

end Scheme

namespace ProEtale

attribute [local instance] isGrothendieckAbelian_sheaf_proetale enoughInjectives_sheaf_proetale

variable (X : Scheme.{u})

/- The instances below are stated at the coefficient universe of this file: instance search
otherwise commits to instances for the small étale site at other universes before the
coefficient universe is known. -/

/-- Abelian presheaves on the small étale site of `X` admit sheafification. -/
local instance : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Scheme.hasSheafify_smallEtaleTopology X

/-- Abelian sheaves on the small étale site of `X` form an abelian category. -/
local instance : Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  sheafIsAbelian

/-- Abelian sheaves on the small étale site of `X` have enough injectives. -/
local instance : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale.{u, v} X

/-- The inverse image `ε⁻¹` of abelian sheaves is additive. -/
instance : (epsilonInverseImage.{u, v} X).Additive :=
  (epsilonAdjunction.{u, v} X).left_adjoint_additive

/-- The inverse image `ε⁻¹` of abelian sheaves preserves finite limits. -/
instance : PreservesFiniteLimits (epsilonInverseImage.{u, v} X) :=
  Scheme.preservesFiniteLimits_of_etaleToProetale_adjunction X (epsilonAdjunction.{u, v} X)

/-- The inverse image `ε⁻¹` of abelian sheaves preserves finite colimits. -/
instance : PreservesFiniteColimits (epsilonInverseImage.{u, v} X) :=
  have := (epsilonAdjunction.{u, v} X).isLeftAdjoint
  inferInstance

/-- The inverse image `ε⁻¹` of abelian sheaves preserves homology. -/
instance : (epsilonInverseImage.{u, v} X).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The direct image `ε_*` of abelian sheaves is additive. -/
instance : (epsilonDirectImage.{u, v} X).Additive :=
  (epsilonAdjunction.{u, v} X).right_adjoint_additive

/-- **Stacks 099T** for the inverse image `ε⁻¹` of abelian sheaves: the unit `ℱ ⟶ ε_* ε⁻¹ ℱ` is
an isomorphism. -/
instance isIso_epsilonAdjunction_unit : IsIso (epsilonAdjunction.{u, v} X).unit :=
  Scheme.isIso_unit_of_etaleToProetale_addCommGrp X _

/-- The direct image `ε_*` has a right derived functor on bounded below homotopy categories,
with unit `Functor.rightDerivedFunctorPlusUnit`. -/
local instance : ((epsilonDirectImage.{u, v} X).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v})) :=
  Functor.HasRightDerivedFunctor.mk' (RF := (epsilonDirectImage.{u, v} X).rightDerivedFunctorPlus)
    (α := (epsilonDirectImage.{u, v} X).rightDerivedFunctorPlusUnit)

/-! ### Higher direct images of the inverse image of an injective sheaf -/

/-- Every object of the small étale site is covered by objects whose underlying scheme is
affine: the members of an affine open cover of its underlying scheme. -/
theorem exists_affine_presieve_mem_smallEtaleTopology (V : X.Etale) :
    ∃ P : Presieve V, Sieve.generate P ∈ X.smallEtaleTopology V ∧
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), P g → IsAffine W.left := by
  let W (i : V.left.affineCover.I₀) : X.Etale := Scheme.Etale.mk (V.left.affineCover.f i ≫ V.hom)
  let f (i : V.left.affineCover.I₀) : W i ⟶ V :=
    MorphismProperty.Over.homMk (V.left.affineCover.f i) rfl
  refine ⟨Presieve.ofArrows W f, ?_, ?_⟩
  · show Sieve.ofArrows W f ∈ _
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := V.left.affineCover.exists_eq x
    exact ⟨i, y, hy⟩
  · rintro _ _ ⟨i⟩
    exact inferInstanceAs (IsAffine (V.left.affineCover.X i))

open Stacks.Cohomology Stacks.Cohomology.FreeYonedaUnivLE in
/-- **The higher direct images of `ε⁻¹ℐ` vanish** for an injective abelian sheaf `ℐ` on the small
étale site: `R^q ε_*(ε⁻¹ℐ) = 0` for `q > 0`. It is the sheafification of
`U ↦ H^q(U_proétale, ε⁻¹ℐ)`, which vanishes on the affine objects of `X_étale` by Stacks 099U,
and those cover every object. -/
theorem isZero_rightDerived_epsilonDirectImage_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I]
    (q : ℕ) (hq : 0 < q) :
    IsZero (((epsilonDirectImage.{u, v} X).rightDerived q).obj
      ((epsilonInverseImage.{u, v} X).obj I)) := by
  refine HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{max (u + 1) v}
    X.etaleToProetale q _ (fun V ↦ ?_)
  obtain ⟨P, hP, hPaff⟩ := exists_affine_presieve_mem_smallEtaleTopology X V
  refine ⟨P, hP, fun W g hg ↦ ?_⟩
  have : IsAffine W.left := hPaff g hg
  have hsub := subsingleton_ext_proetaleInverseImage_of_injective.{max (u + 1) v}
    (epsilonAdjunction.{u, v} X) I (isAffineIndEtaleOverEtale_etaleToProetale_obj W) q hq
  obtain ⟨e⟩ :=
    nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{max (u + 1) v}
      (Scheme.ProEt.topology X) (X.etaleToProetale.obj W) q
  exact (@AddCommGrpCat.isZero_of_subsingleton _ hsub).of_iso (e.app _).symm

/-- `ε⁻¹ℐ` is right acyclic for `ε_*` for an injective abelian sheaf `ℐ` on the small étale
site. -/
theorem rightAcyclic_epsilonInverseImage_obj_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I] :
    (epsilonDirectImage.{u, v} X).rightAcyclic ((epsilonInverseImage.{u, v} X).obj I) := by
  have := (epsilonAdjunction.{u, v} X).isRightAdjoint
  rw [((epsilonDirectImage.{u, v} X).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    _).2 inferInstance]
  intro i hi
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact (isZero_rightDerived_epsilonDirectImage_of_injective X I q (by exact_mod_cast hi)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).symm

/-! ### Stacks 099V -/

/-- **Stacks 099V (2).** For `K ∈ D⁺(X_étale)` the map `K ⟶ Rε_* ε⁻¹ K` is an isomorphism: the
unit of the derived adjunction `ε⁻¹ ⊣ Rε_*` on bounded below derived categories is invertible.
Here `ε⁻¹` on `D⁺` is the right derived functor of the exact functor `ε⁻¹`, that is, `ε⁻¹`
applied termwise. -/
theorem isIso_epsilonAdjunction_rightDerivedFunctorPlus_unit :
    IsIso (epsilonAdjunction.{u, v} X).rightDerivedFunctorPlus.unit :=
  (epsilonAdjunction.{u, v} X).isIso_rightDerivedFunctorPlus_unit
    (fun I _ ↦ rightAcyclic_epsilonInverseImage_obj_of_injective X I)

/-- **Stacks 099V (1).** For an abelian sheaf `ℱ` on `X_étale`, `Rε_*(ε⁻¹ℱ) = ℱ`: the adjunction
map `ℱ ⟶ ε_* ε⁻¹ ℱ` is an isomorphism and the higher direct images `R^q ε_*(ε⁻¹ℱ)`, `q > 0`,
vanish. -/
theorem isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((epsilonAdjunction.{u, v} X).unit.app F) ∧
      ∀ q : ℕ, 0 < q → IsZero (((epsilonDirectImage.{u, v} X).rightDerived q).obj
        ((epsilonInverseImage.{u, v} X).obj F)) := by
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  have := (epsilonAdjunction.{u, v} X).isRightAdjoint
  have hF := (epsilonAdjunction.{u, v} X).rightAcyclic_obj_of_isIso_unit
    (fun I _ ↦ rightAcyclic_epsilonInverseImage_obj_of_injective X I) F
  rw [((epsilonDirectImage.{u, v} X).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    _).2 inferInstance] at hF
  exact (hF q (by exact_mod_cast hq)).of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _)

/-! ### Stacks 099W -/

section Cohomology

/-- Identity morphisms of schemes are étale. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ inferInstance⟩

/-- Identity morphisms of schemes are weakly étale. -/
local instance : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ inferInstance⟩

/-- The final object `X ⟶ X` of the small étale site of `X`. -/
abbrev etaleFinal : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- `X ⟶ X` is final in the small étale site of `X`. -/
def isTerminalEtaleFinal : IsTerminal (etaleFinal X) :=
  MorphismProperty.Over.mkIdTerminal _ X

/-- The final object of the small étale site is final in the small pro-étale site. -/
def isTerminalEtaleToProetaleObjEtaleFinal :
    IsTerminal (X.etaleToProetale.obj (etaleFinal X)) :=
  MorphismProperty.Over.mkIdTerminal _ X

/-- The direct image `ε_*` of abelian sheaves preserves injective objects. -/
instance : (epsilonDirectImage.{u, v} X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (epsilonAdjunction.{u, v} X)

/-- The unit of the derived adjunction `ε⁻¹ ⊣ Rε_*` on `D⁺(X_étale)` is an isomorphism. -/
instance : IsIso (epsilonAdjunction.{u, v} X).rightDerivedFunctorPlus.unit :=
  isIso_epsilonAdjunction_rightDerivedFunctorPlus_unit X

/-- The functor `ε⁻¹ : D⁺(X_étale) ⥤ D⁺(X_proétale)` is full. -/
instance : (epsilonInverseImage.{u, v} X).mapDerivedCategoryPlus.Full :=
  have := (epsilonAdjunction.{u, v} X).rightDerivedFunctorPlus.fullyFaithfulLOfIsIsoUnit.full
  Functor.Full.of_iso
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (epsilonInverseImage.{u, v} X)).symm

/-- The functor `ε⁻¹ : D⁺(X_étale) ⥤ D⁺(X_proétale)` is faithful. -/
instance : (epsilonInverseImage.{u, v} X).mapDerivedCategoryPlus.Faithful :=
  have := (epsilonAdjunction.{u, v} X).rightDerivedFunctorPlus.fullyFaithfulLOfIsIsoUnit.faithful
  Functor.Faithful.of_iso
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (epsilonInverseImage.{u, v} X)).symm

/-- The inverse image `ε⁻¹` carries the constant sheaf `ℤ` on the small étale site to the
constant sheaf `ℤ` on the small pro-étale site. -/
def constantSheafCompEpsilonInverseImageIso :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        epsilonInverseImage.{u, v} X ≅
      constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  Stacks.ExtAdjunction.constantSheafPullbackIso (epsilonAdjunction.{u, v} X)
    (isTerminalEtaleFinal X) (isTerminalEtaleToProetaleObjEtaleFinal X)
    (Stacks.ExtAdjunction.restrictSections _ _ _)

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 099W (1).** For an abelian sheaf `ℱ` on `X_étale`,
`H^i(X_étale, ℱ) = H^i(X_proétale, ε⁻¹ℱ)` for all `i`, naturally in `ℱ`. Cohomology is
`CategoryTheory.Sheaf.functorH`, `Ext` out of the constant sheaf `ℤ`; the comparison is induced by
the exact functor `ε⁻¹`, which is fully faithful on bounded below derived categories by
Stacks 099V. -/
def epsilonInverseImageCompFunctorHIso (n : ℕ) :
    epsilonInverseImage.{u, v} X ⋙
        Sheaf.functorH.{w, max (u + 1) v, u, u + 1} (Scheme.ProEt.topology X) n ≅
      Sheaf.functorH.{w, max (u + 1) v, u, u + 1} X.smallEtaleTopology n :=
  Stacks.ExtAdjunction.functorHComparisonIsoOfBijective (constantSheafCompEpsilonInverseImageIso X)
    n (fun F ↦ by
      have h₁ := (epsilonInverseImage.{u, v} X).mapExt_bijective_of_mapDerivedCategoryPlus.{w, w}
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ))) F n
      have h₂ := Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso.{w}
        (Z := (epsilonInverseImage.{u, v} X).obj F)
        ((constantSheafCompEpsilonInverseImageIso X).app (AddCommGrpCat.of (ULift ℤ))).inv n
      exact h₂.comp h₁)

end Cohomology

section DerivedGlobalSections

/-- The global sections functor on abelian sheaves on `X_étale` is additive. -/
local instance : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).Additive :=
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ _ _

/-- The global sections functor on abelian sheaves on `X_proétale` is additive. -/
local instance : (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).Additive :=
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ _ _

/-- Restriction to the small étale site followed by global sections is global sections on the
small pro-étale site: `Γ(X_étale, ε_* -) = Γ(X_proétale, -)`. -/
def epsilonDirectImageCompΓIso :
    epsilonDirectImage.{u, v} X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso _ _ X.etaleToProetale _
    (isTerminalEtaleFinal X) (isTerminalEtaleToProetaleObjEtaleFinal X) rfl

/-- **Stacks 099W (2).** For `K ∈ D⁺(X_étale)`,
`RΓ(X_étale, K) = RΓ(X_proétale, ε⁻¹ K)`, naturally in `K`. It is the composite of the Leray
identification `RΓ(X_proétale, -) = RΓ(X_étale, Rε_* -)` (`ε_*` preserves injectives, its left
adjoint being exact) with `K = Rε_* ε⁻¹ K` (Stacks 099V (2)). -/
def rightDerivedFunctorPlusΓIso :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ≅
      (epsilonInverseImage.{u, v} X).rightDerivedFunctorPlus ⋙
        (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (epsilonAdjunction.{u, v} X).rightDerivedFunctorPlus.unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso _ _ _
        (epsilonDirectImageCompΓIso X)).symm

end DerivedGlobalSections

end ProEtale

end AlgebraicGeometry

end
