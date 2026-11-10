module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.GabrielPopescu
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.FlatPushforwardOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsKInjective
import StacksCore.Tactic.StacksAttribute

/-!
# The derived functor of sections supported on a closed subset

Let `Z` be a closed subset of a ringed space `X`, let `𝒪_X|_Z` be the restricted structure
sheaf and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. The functor
`H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on `Z` is right adjoint to the exact
functor `i_*`, so it has a total right derived functor `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)`, and
`RH_Z` is again right adjoint to `i_*`. The adjunction recovers a complex pushed forward from
`Z`: its unit is an isomorphism, so `RH_Z(i_* K) = K`, and consequently the higher derived
sheaves `H^p_Z` of a sheaf pushed forward from `Z` vanish for `p > 0`.

## Main definitions

* `derivedSupportedSectionsOnClosed`: the total right derived functor `RH_Z`, together with its
  derivation unit `derivedSupportedSectionsOnClosedUnit`.

## Main results

* `derivedPushforward_adj_derivedSupportedSectionsOnClosed`: **Stacks 0A3B (1)**, `RH_Z` is
  right adjoint to `i_*`.
* `exists_isIso_unit_derivedPushforward_adj_derivedSupportedSectionsOnClosed`: **Stacks 0A3B
  (2)**, the unit `K ⟶ RH_Z(i_* K)` of that adjunction is an isomorphism.
* `isZero_rightDerivedPlus_supportedSectionsOnClosed_modulePushforward`: **Stacks 0A3B (3)**,
  `H^p_Z(i_* 𝒢) = 0` for `p > 0`.

## Implementation notes

Because `i_*` is exact it inverts quasi-isomorphisms, so it needs no deriving and descends to
`CategoryTheory.Functor.mapDerivedCategory`; `H_Z` is derived by K-injective resolutions, which
exist because `Mod(𝒪_X)` is Grothendieck abelian. The adjunction is then Stacks 09T5, whose
pointwise hypotheses are a terminal K-injective resolution on the right and the constant system
on the left. The existential form of Stacks 09T5 also yields the compatibility of the derived
unit with the underived one, which is what identifies the derived unit as the canonical map
`K ⟶ RH_Z(i_* K)` and is therefore recorded alongside the adjunction.

That the unit is invertible is checked on a K-injective complex `J` of `𝒪_X|_Z`-modules and then
transported, every object of `D(𝒪_X|_Z)` being isomorphic to the image of such a complex. On
`J` the three factors of the compatibility are invertible: the underived unit because `i_*` is
fully faithful (Stacks 08KS), the comparison for `i_*` because `i_*` is exact, and the
derivation unit of `RH_Z` because `i_* J` is again K-injective — the stalk maps of `i` are
isomorphisms, so `i` is flat and Stacks 0D5Z applies.

The vanishing in positive degrees then follows: `RH_Z(i_* 𝒢)` is the single complex `𝒢` in
degree `0`, and the bounded-below right derived functor computing `H^p_Z` agrees with the
unbounded one on bounded-below objects.

## References

* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Lemma 13.30.3 (Tag 09T5)](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Lemma 20.32.9 (Tag 0D5Z)](https://stacks.math.columbia.edu/tag/0D5Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### Deriving an adjunction whose left adjoint is exact and fully faithful -/

section Derived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {G₀ : B ⥤ A} {H₀ : A ⥤ B} [G₀.Additive] [H₀.Additive]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]

/-- If every complex has a K-injective resolution, so does every object of the homotopy category:
there is a quasi-isomorphism in `K(C)` to the class of a K-injective complex. -/
private lemma exists_quasiIso_quotient_obj_isKInjective {C : Type*} [Category* C] [Abelian C]
    (hres : ∀ K : CochainComplex C ℤ, ∃ (J : CochainComplex C ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    ∃ (J : CochainComplex C ℤ)
      (q : M ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J),
      J.IsKInjective ∧ HomotopyCategory.quasiIso C (ComplexShape.up ℤ) q := by
  obtain ⟨Mc, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨J, q, hJ, hq⟩ := hres Mc
  exact ⟨J, (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q, hJ,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq⟩

/-- **Stacks 09T5 for an exact left adjoint.** Let `G₀ ⊣ H₀` be an adjunction of additive
functors between abelian categories with `G₀` exact, and let `RF` be a right derived functor of
`H₀` with derivation unit `β`. If every complex in the source of `H₀` admits a K-injective
resolution, then the functor induced by `G₀` on unbounded derived categories is left adjoint to
`RF`, by an adjunction whose unit is compatible with the unit of `G₀ ⊣ H₀` and with the two
derivation units. The compatibility identifies the derived unit as the canonical comparison. -/
theorem exists_derivedAdjunction_unit_compat_of_exact (adj : G₀ ⊣ H₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q) :
    ∃ Ad : G₀.mapDerivedCategory ⊣ RF,
      ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
        Ad.unit.app (DerivedCategory.Qh.obj M) ≫
            RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M) =
          DerivedCategory.Qh.map
              ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
            β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let W' := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let Q' := DerivedCategory.Qh (C := B)
  let F := H₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let G := G₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let LG := G₀.mapDerivedCategory
  let α := G₀.mapDerivedCategoryFactorsh.hom
  have hRF : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ K ⋙
        Under.forget K ⋙ F ⋙ Q')),
        ∃ (_ : (F ⋙ Q').IsRightDerivedValueAt W K c),
        ∃ (e : c.pt ≅ RF.obj (Q.obj K)),
          ∀ s : W.Under ⊤ K,
            c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right := by
    intro K
    obtain ⟨I, qh, hI, hqh⟩ := exists_quasiIso_quotient_obj_isKInjective hres K
    have : I.IsKInjective := hI
    let t₀ : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ qh hqh
    let ht := Stacks.Injectives.isTerminalUnderKInjective I qh hqh
    let c := Limits.coconeOfDiagramTerminal ht
      (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ F ⋙ Q')
    have hc := Stacks.Injectives.coconeOfTerminalUnder_isRightDerivedValueAt
      (F ⋙ Q') W K t₀ ht
    have hβ : IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
      Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective H₀ RF β hres I hI
    let eβ : _ ≅ _ := by
      have : IsIso (β.app t₀.right) := by simpa [t₀] using hβ
      exact asIso (β.app t₀.right)
    have : IsIso (Q.map t₀.hom) := (Localization.inverts Q W) t₀.hom t₀.prop
    have : IsIso (RF.map (Q.map t₀.hom)) := by infer_instance
    let eRF : _ ≅ _ := asIso (RF.map (Q.map t₀.hom))
    let e : c.pt ≅ RF.obj (Q.obj K) := eβ ≪≫ eRF.symm
    refine ⟨c, hc, e, ?_⟩
    intro s
    have hcomp : s.hom ≫ (ht.from s).right = t₀.hom :=
      MorphismProperty.Under.w (ht.from s)
    have hqr : Q.map t₀.hom = Q.map s.hom ≫ Q.map ((ht.from s).right) := by
      rw [← Functor.map_comp]
      exact congrArg Q.map hcomp.symm
    have hmap : RF.map (Q.map t₀.hom) =
        RF.map (Q.map s.hom) ≫ RF.map (Q.map ((ht.from s).right)) := by
      rw [← Functor.map_comp, hqr]
    have hnat : (F ⋙ Q').map ((ht.from s).right) ≫ β.app t₀.right =
        β.app s.right ≫ RF.map (Q.map ((ht.from s).right)) := by
      simpa only [Functor.comp_map] using β.naturality ((ht.from s).right)
    have : IsIso (Q.map s.hom) := (Localization.inverts Q W) s.hom s.prop
    have : IsIso (RF.map (Q.map s.hom)) := by infer_instance
    have he' : e.hom = β.app t₀.right ≫ eRF.inv := by
      change (eβ ≪≫ eRF.symm).hom = β.app t₀.right ≫ eRF.inv
      simp only [Iso.trans_hom, Iso.symm_hom, eβ, asIso_hom]
    have hComp : RF.map (Q.map s.hom) ≫
        RF.map (Q.map ((ht.from s).right)) = eRF.hom := by
      simpa only [eRF, asIso_hom] using hmap.symm
    have hcancel : RF.map (Q.map ((ht.from s).right)) ≫ eRF.inv ≫
        RF.map (Q.map s.hom) = 𝟙 _ := by
      have hEq : RF.map (Q.map s.hom) ≫
          (RF.map (Q.map ((ht.from s).right)) ≫ eRF.inv ≫
            RF.map (Q.map s.hom)) = RF.map (Q.map s.hom) := by
        simp only [← Category.assoc, hComp]
        exact (Category.assoc eRF.hom eRF.inv (RF.map (Q.map s.hom))).trans
          (eRF.hom_inv_id_assoc _)
      exact (cancel_epi (RF.map (Q.map s.hom))).mp
        (hEq.trans (Category.comp_id _).symm)
    dsimp [c, Limits.coconeOfDiagramTerminal]
    rw [he']
    calc
      _ = ((F ⋙ Q').map ((ht.from s).right) ≫
            (β.app t₀.right ≫ eRF.inv)) ≫ RF.map (Q.map s.hom) :=
        (Category.assoc ((F ⋙ Q').map ((ht.from s).right))
          (β.app t₀.right ≫ eRF.inv) (RF.map (Q.map s.hom))).symm
      _ = (((F ⋙ Q').map ((ht.from s).right) ≫ β.app t₀.right) ≫
            eRF.inv) ≫ RF.map (Q.map s.hom) :=
        congrArg (fun k => k ≫ RF.map (Q.map s.hom))
          (Category.assoc ((F ⋙ Q').map ((ht.from s).right))
            (β.app t₀.right) eRF.inv).symm
      _ = ((β.app s.right ≫ RF.map (Q.map ((ht.from s).right))) ≫
            eRF.inv) ≫ RF.map (Q.map s.hom) :=
        congrArg (fun k => (k ≫ eRF.inv) ≫ RF.map (Q.map s.hom)) hnat
      _ = β.app s.right ≫
            (RF.map (Q.map ((ht.from s).right)) ≫ eRF.inv ≫
              RF.map (Q.map s.hom)) :=
        (Category.assoc
          (β.app s.right ≫ RF.map (Q.map ((ht.from s).right)))
          eRF.inv (RF.map (Q.map s.hom))).trans
          (Category.assoc (β.app s.right)
            (RF.map (Q.map ((ht.from s).right)))
            (eRF.inv ≫ RF.map (Q.map s.hom)))
      _ = β.app s.right := by rw [hcancel]; exact Category.comp_id _
  have hInv : W'.IsInvertedBy (G ⋙ Q) :=
    Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso G₀
  have hLG : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      ∃ (d : Limits.Cone (MorphismProperty.Over.forget W' ⊤ M ⋙
        Over.forget M ⋙ G ⋙ Q)),
        ∃ (_ : (G ⋙ Q).IsLeftDerivedValueAt W' M d),
        ∃ (e : LG.obj (Q'.obj M) ≅ d.pt),
          ∀ t : W'.Over ⊤ M,
            LG.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left := by
    intro M
    let d := Stacks.Injectives.coneOfInvertedMorphisms (G ⋙ Q) W' hInv M
    have hd := Stacks.Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt
      (G ⋙ Q) W' hInv M
    let e : LG.obj (Q'.obj M) ≅ d.pt := G₀.mapDerivedCategoryFactorsh.app M
    refine ⟨d, hd, e, ?_⟩
    intro t
    have : IsIso ((G ⋙ Q).map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Q'.map t.hom) ≫ α.app M =
        α.app t.left ≫ (G ⋙ Q).map t.hom := by
      simpa [LG, Q', α, G, Q, Functor.comp_map] using
        G₀.mapDerivedCategoryFactorsh.hom.naturality t.hom
    dsimp [d, Stacks.Injectives.coneOfInvertedMorphisms]
    change LG.map (Q'.map t.hom) ≫ α.app M ≫ inv ((G ⋙ Q).map t.hom) = α.app t.left
    calc
      LG.map (Q'.map t.hom) ≫ α.app M ≫ inv ((G ⋙ Q).map t.hom) =
          (α.app t.left ≫ (G ⋙ Q).map t.hom) ≫ inv ((G ⋙ Q).map t.hom) := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ inv ((G ⋙ Q).map t.hom)) hn
      _ = α.app t.left := by simp
  obtain ⟨Ad, hAd, -⟩ :=
    CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      (CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ))
      W W' Q Q' RF β LG α hRF hLG
  exact ⟨Ad, hAd⟩

omit [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀] [HasDerivedCategory A] in
/-- The unit of the adjunction induced on homotopy categories is, at the homotopy class of a
complex, the class of the degreewise unit; localizing, it is the image of the degreewise unit
under `K(B) ⥤ D(B)` precomposed with the homotopy quotient. -/
private lemma qh_map_mapHomotopyCategoryAdjunction_unit_app_quotient (adj : G₀ ⊣ H₀)
    (J : CochainComplex B ℤ) :
    DerivedCategory.Qh.map
        ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app J) :=
  rfl

/-- The unit of a derived adjunction as in
`exists_derivedAdjunction_unit_compat_of_exact` is invertible at the image of a K-injective
complex, provided the underived unit is invertible and `G₀` preserves K-injectivity: the three
factors of the compatibility are then invertible. -/
private lemma isIso_unit_app_qh_quotient_of_isKInjective (adj : G₀ ⊣ H₀) [IsIso adj.unit]
    (hKinj : ∀ J : CochainComplex B ℤ, J.IsKInjective →
      CochainComplex.IsKInjective
        ((G₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
    {RF : DerivedCategory A ⥤ DerivedCategory B}
    {β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF}
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (Ad : G₀.mapDerivedCategory ⊣ RF)
    (hAd : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      Ad.unit.app (DerivedCategory.Qh.obj M) ≫
          RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M) =
        DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
          β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    (J : CochainComplex B ℤ) (hJ : J.IsKInjective) :
    IsIso (Ad.unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J))) := by
  have hM : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      IsIso (RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M)) := fun M => inferInstance
  have h₂ : IsIso (DerivedCategory.Qh.map
      ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J))) := by
    have hdeg : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction adj
        (ComplexShape.up ℤ)).unit.app J).f n) := fun n => by
      change IsIso (adj.unit.app (J.X n))
      infer_instance
    have hu : IsIso ((Adjunction.mapHomologicalComplexAdjunction adj
        (ComplexShape.up ℤ)).unit.app J) := HomologicalComplex.Hom.isIso_of_components _
    rw [qh_map_mapHomotopyCategoryAdjunction_unit_app_quotient]
    exact Functor.map_isIso _ _
  have h₃ : IsIso (β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J))) :=
    Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective H₀ RF β hres
      ((G₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) (hKinj J hJ)
  have h₁ := hM ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)
  have hiso : IsIso (Ad.unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)) ≫
      RF.map (G₀.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J))) := by
    rw [hAd ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (RF.map (G₀.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)))

/-- **The unit of the derived adjunction is invertible.** If the left adjoint `G₀` is exact,
fully faithful and preserves K-injectivity, and both categories admit K-injective resolutions,
then the unit of the derived adjunction of
`exists_derivedAdjunction_unit_compat_of_exact` is an isomorphism, so `RF(G₀ K) = K` for every
`K` in the derived category of the source of `G₀`. -/
theorem isIso_unit_of_fullyFaithful_of_isKInjective_map (adj : G₀ ⊣ H₀) [IsIso adj.unit]
    (hKinj : ∀ J : CochainComplex B ℤ, J.IsKInjective →
      CochainComplex.IsKInjective
        ((G₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
    {RF : DerivedCategory A ⥤ DerivedCategory B}
    {β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF}
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (hres' : ∀ K : CochainComplex B ℤ, ∃ (J : CochainComplex B ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (Ad : G₀.mapDerivedCategory ⊣ RF)
    (hAd : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      Ad.unit.app (DerivedCategory.Qh.obj M) ≫
          RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M) =
        DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
          β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) :
    IsIso Ad.unit := by
  have hpt : ∀ D : DerivedCategory B, IsIso (Ad.unit.app D) := by
    intro D
    set M := (DerivedCategory.Qh (C := B)).objPreimage D with hM
    let eD := (DerivedCategory.Qh (C := B)).objObjPreimageIso D
    obtain ⟨J, qh, hJ, hqh⟩ := exists_quasiIso_quotient_obj_isKInjective hres' M
    have hQq : IsIso ((DerivedCategory.Qh (C := B)).map qh) :=
      Localization.inverts (DerivedCategory.Qh (C := B))
        (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _ hqh
    let e : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J) ≅ D :=
      (asIso ((DerivedCategory.Qh (C := B)).map qh)).symm ≪≫ eD
    have hJiso : IsIso (Ad.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J))) :=
      isIso_unit_app_qh_quotient_of_isKInjective adj hKinj hres Ad hAd J hJ
    have hnat : e.hom ≫ Ad.unit.app D =
        Ad.unit.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J)) ≫
          (G₀.mapDerivedCategory ⋙ RF).map e.hom := by
      simp
    have hcomp : IsIso (e.hom ≫ Ad.unit.app D) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom (Ad.unit.app D)
  exact NatIso.isIso_of_isIso_app Ad.unit

end Derived

/-! ### The derived functor of sections supported on a closed subset -/

/-- The inclusion of a closed subset, with the restricted structure sheaf on the subset, is a
flat morphism of ringed spaces: its stalk maps are isomorphisms. -/
theorem isFlat_closedSubsetInclusion (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    AlgebraicGeometry.IsFlat (closedSubsetInclusion X Z) := by
  intro z
  have : IsIso ((closedSubsetInclusion X Z).hom.stalkMap z) :=
    AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z) z
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- Pushforward along the inclusion of a closed subset carries K-injective complexes of
`𝒪_X|_Z`-modules to K-injective complexes of `𝒪_X`-modules, the inclusion being flat. -/
theorem isKInjective_modulePushforward_closedSubsetInclusion (X : RingedSpace.{u, u})
    (Z : Set X.carrier)
    (J : CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) ℤ) (hJ : J.IsKInjective) :
    CochainComplex.IsKInjective
      (((modulePushforward (closedSubsetInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
  RingedSpaceModuleAdjunction.isKInjective_modulePushforward_of_isFlat
    (closedSubsetInclusion X Z) (isFlat_closedSubsetInclusion X Z) J hJ

/-- Every complex of `𝒪_X`-modules admits a K-injective resolution, `Mod(𝒪_X)` being
Grothendieck abelian. -/
theorem exists_isKInjective_quasiIso_moduleSheaves (X : RingedSpace.{u, u})
    (K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ∃ (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q :=
  have : IsGrothendieckAbelian.{u} (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    inferInstance
  Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso K

/-- The right derived functor of sections supported on a closed subset exists pointwise, being
computed by K-injective resolutions. -/
instance hasPointwiseRightDerivedFunctor_supportedSectionsOnClosed (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    Functor.HasPointwiseRightDerivedFunctor
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  letI : IsGrothendieckAbelian.{u} (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    inferInstance
  letI : EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    IsGrothendieckAbelian.enoughInjectives
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} _
    (fun K => by
      obtain ⟨J, q, hJ, hq⟩ := exists_isKInjective_quasiIso_moduleSheaves X K
      exact ⟨J, q, hJ, hq⟩)).1

/-- The total right derived functor `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` of the functor of sections
supported on a closed subset `Z`. -/
noncomputable def derivedSupportedSectionsOnClosed (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) :=
  Functor.totalRightDerived
    ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))

/-- The canonical comparison from the sections supported on `Z` of a complex to the value of
`RH_Z` on it. -/
noncomputable abbrev derivedSupportedSectionsOnClosedUnit (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSectionsOnClosed X Z hZ :=
  Functor.totalRightDerivedUnit
    ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))

/-- The comparison exhibits `RH_Z` as the right derived functor of sections supported on `Z`. -/
instance derivedSupportedSectionsOnClosed_isRightDerivedFunctor (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (derivedSupportedSectionsOnClosed X Z hZ).IsRightDerivedFunctor
      (derivedSupportedSectionsOnClosedUnit X Z hZ)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedSupportedSectionsOnClosed, derivedSupportedSectionsOnClosedUnit]
  infer_instance

/-- Every complex of `𝒪_X|_Z`-modules admits a K-injective resolution, `Mod(𝒪_X|_Z)` being
Grothendieck abelian. -/
theorem exists_isKInjective_quasiIso_moduleSheaves_closedSubset (X : RingedSpace.{u, u})
    (Z : Set X.carrier)
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) ℤ) :
    ∃ (J : CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q :=
  exists_isKInjective_quasiIso_moduleSheaves (closedSubsetRingedSpace X Z) K

/-- The unit of the adjunction `i_* ⊣ H_Z` is an isomorphism: `i_*` is fully faithful by
Stacks 08KS, so the sections supported on `Z` of a module pushed forward from `Z` recover that
module. -/
instance isIso_unit_modulePushforward_supportedSectionsOnClosed_adjunction
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    IsIso (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).unit :=
  have := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).full
  have := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  inferInstance

/-- **Stacks 0A3B (1), with the compatibility of the unit.** Derived pushforward from a closed
subset is left adjoint to `RH_Z`, by an adjunction whose unit at a complex `M` of
`𝒪_X|_Z`-modules is computed from the unit `M ⟶ H_Z(i_* M)` of the underived adjunction and the
derivation units of the two derived functors. The compatibility is what identifies the derived
unit as the canonical comparison `K ⟶ RH_Z(i_* K)`. -/
theorem exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ∃ Ad : (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
        derivedSupportedSectionsOnClosed X Z hZ,
      ∀ M : HomotopyCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ),
        Ad.unit.app (DerivedCategory.Qh.obj M) ≫
            (derivedSupportedSectionsOnClosed X Z hZ).map
              ((modulePushforward
                (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app M) =
          DerivedCategory.Qh.map
              ((Adjunction.mapHomotopyCategoryAdjunction
                (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
                (ComplexShape.up ℤ)).unit.app M) ≫
            (derivedSupportedSectionsOnClosedUnit X Z hZ).app
              (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj M) :=
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  exists_derivedAdjunction_unit_compat_of_exact
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (exists_isKInjective_quasiIso_moduleSheaves X)

/-- **Stacks 0A3B (1).** Let `Z` be a closed subset of a ringed space `X` and let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. The right derived functor
`RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` of sections supported on `Z` is right adjoint to the functor
`D(𝒪_X|_Z) ⥤ D(𝒪_X)` induced by `i_*`. -/
@[stacks 0A3B "adjunction"]
theorem derivedPushforward_adj_derivedSupportedSectionsOnClosed (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    Nonempty
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
        derivedSupportedSectionsOnClosed X Z hZ) :=
  ⟨(exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit X Z hZ).choose⟩

/-- **Stacks 0A3B (2).** Let `Z` be a closed subset of a ringed space `X` and let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. For `K` in `D(𝒪_X|_Z)` one has
`RH_Z(i_* K) = K`: the unit of the derived adjunction of Stacks 0A3B (1) is an isomorphism. The
adjunction is pinned down by the compatibility of its unit with the unit `M ⟶ H_Z(i_* M)` of the
underived adjunction, which identifies the invertible map as the canonical comparison. -/
@[stacks 0A3B "pushforward identity"]
theorem exists_isIso_unit_derivedPushforward_adj_derivedSupportedSectionsOnClosed
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ∃ Ad : (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
        derivedSupportedSectionsOnClosed X Z hZ,
      (∀ M : HomotopyCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ),
        Ad.unit.app (DerivedCategory.Qh.obj M) ≫
            (derivedSupportedSectionsOnClosed X Z hZ).map
              ((modulePushforward
                (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app M) =
          DerivedCategory.Qh.map
              ((Adjunction.mapHomotopyCategoryAdjunction
                (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
                (ComplexShape.up ℤ)).unit.app M) ≫
            (derivedSupportedSectionsOnClosedUnit X Z hZ).app
              (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj M)) ∧ IsIso Ad.unit := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  obtain ⟨Ad, hAd⟩ :=
    exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit X Z hZ
  exact ⟨Ad, hAd, isIso_unit_of_fullyFaithful_of_isKInjective_map
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (isKInjective_modulePushforward_closedSubsetInclusion X Z)
    (exists_isKInjective_quasiIso_moduleSheaves X)
    (exists_isKInjective_quasiIso_moduleSheaves_closedSubset X Z) Ad hAd⟩

/-- Composing `RH_Z` with derived pushforward from the closed subset is the identity on
`D(𝒪_X|_Z)`, the natural isomorphism being the inverse of the unit of Stacks 0A3B (1). -/
theorem nonempty_derivedPushforward_comp_derivedSupportedSectionsOnClosed_iso_id
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    Nonempty ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
      derivedSupportedSectionsOnClosed X Z hZ ≅
        𝟭 (DerivedCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (closedSubsetRingedSpace X Z))))) := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  obtain ⟨Ad, -, hiso⟩ :=
    exists_isIso_unit_derivedPushforward_adj_derivedSupportedSectionsOnClosed X Z hZ
  exact ⟨(asIso Ad.unit).symm⟩

/-- **Stacks 0A3B (3).** Let `Z` be a closed subset of a ringed space `X`, let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion and let `𝒢` be a sheaf of `𝒪_X|_Z`-modules on
`Z`. Then the higher derived sheaves of sections supported on `Z` of the pushforward of `𝒢`
vanish: `H^p_Z(i_* 𝒢) = 0` for `p > 0`. -/
@[stacks 0A3B "higher vanishing"]
theorem isZero_rightDerivedPlus_supportedSectionsOnClosed_modulePushforward
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (G : _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))
    (p : ℤ) (hp : 0 < p) :
    letI : EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
      IsGrothendieckAbelian.enoughInjectives
    IsZero (((supportedSectionsOnClosedFunctor X Z hZ).rightDerivedPlus p).obj
      ((modulePushforward (closedSubsetInclusion X Z)).obj G)) := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  let _ : IsGrothendieckAbelian.{u} (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    inferInstance
  let _ : EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    IsGrothendieckAbelian.enoughInjectives
  obtain ⟨ePR⟩ := nonempty_derivedPushforward_comp_derivedSupportedSectionsOnClosed_iso_id X Z hZ
  have hcomp : ∀ I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ,
      I.IsKInjective →
      IsIso ((derivedSupportedSectionsOnClosedUnit X Z hZ).app
        ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I)) := fun I hI =>
    Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
      (supportedSectionsOnClosedFunctor X Z hZ) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ)
      (exists_isKInjective_quasiIso_moduleSheaves X) I hI
  obtain ⟨eplus⟩ :=
    Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
      (supportedSectionsOnClosedFunctor X Z hZ) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ) hcomp
      ((DerivedCategory.Plus.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePushforward (closedSubsetInclusion X Z)).obj G)) 0
      (by
        change ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
          ((modulePushforward (closedSubsetInclusion X Z)).obj G)).IsGE 0
        infer_instance)
  have efull : (derivedSupportedSectionsOnClosed X Z hZ).obj
      ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePushforward (closedSubsetInclusion X Z)).obj G)) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z))) 0).obj G :=
    (derivedSupportedSectionsOnClosed X Z hZ).mapIso
        (((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategorySingleFunctor
          0).app G).symm ≪≫
      ePR.app ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z))) 0).obj G)
  exact IsZero.of_iso
    (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) 0).obj G) 0 p hp)
    ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z))) p).mapIso
      (((derivedSupportedSectionsOnClosed X Z hZ).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso (_root_.SheafOfModules.{u}
          (structureSheafRing X)) 0).app
          ((modulePushforward (closedSubsetInclusion X Z)).obj G)).symm ≪≫
        eplus).symm ≪≫ efull))

end Stacks.Cohomology.SupportedComplexes

end
