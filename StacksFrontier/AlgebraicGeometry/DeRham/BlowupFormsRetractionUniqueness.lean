module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartRegular
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreForms
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.RegularSequence.HomVanishingFromComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage

/-!
# Uniqueness of the retraction of `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`

For a morphism `b : X' ⟶ X` of schemes over `S`, [Stacks, Tag 0G5J] proves that the canonical
map `u : Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` has at most one retraction by showing that the third term
`C` of a distinguished triangle on `u` admits no nonzero morphism to `Ω^a_{X/S}`.  This file
collects the steps of that argument which do not see the geometry of the blowup.

## Main results

* `Stacks.DeRham.isIso_homology_zero_pushforwardSingleToDerived`: `H^0` of the comparison
  `g_*N ⟶ Rg_*N` is invertible.
* `Stacks.DeRham.isZero_homology_cone_of_le_zero` and
  `Stacks.DeRham.isIso_homology_cone_of_pos`: if `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is invertible,
  the cone `C` of `u` has no cohomology in degrees `≤ 0`, and in degrees `≥ 1` its cohomology is
  that of `Rb_*Ω^a_{X'/S}`.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SchemeCohomology (hom ringedSpace)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit boundedDerivedPushforwardIso
    boundedDerivedPushforwardIso_hom_app)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- A functor carries `a ≫ b = c`, with `F.map a` and `b` invertible, to an invertible
`F.map c`.  Stated for generic morphisms, so that it applies across the two spellings of the
modules on a scheme, where `rw` does not. -/
private theorem isIso_map_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {a : x ⟶ y} {b : y ⟶ z} {c : x ⟶ z} (h : a ≫ b = c) (ha : IsIso (F.map a))
    (hb : IsIso b) : IsIso (F.map c) := by
  subst h
  rw [F.map_comp]
  infer_instance

/-- **`H^0` of the comparison `g_*N ⟶ Rg_*N` is an isomorphism**: the direct image is left
exact, so `R^0g_* = g_*`. -/
theorem isIso_homology_zero_pushforwardSingleToDerived {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : X.Modules) :
    IsIso ((DerivedCategory.homologyFunctor Y.Modules 0).map (pushforwardSingleToDerived g N)) := by
  let _ : Abelian (SheafOfModules.{u} (structureSheafRing (ringedSpace X))) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.abelianModules _
  let _ : Abelian (SheafOfModules.{u} (structureSheafRing (ringedSpace Y))) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.abelianModules _
  have _ := Stacks.AlgebraicGeometry.FlatBaseChangeDerived.enoughInjectivesModules (ringedSpace X)
  have _ : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePushforward (hom g)) :=
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      (hom g)).rightAdjoint_preservesLimits.preservesFiniteLimits.{0, 0}
  have _ : (RingedSpaceModuleAdjunction.modulePushforward (hom g)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let K := (HomotopyCategory.Plus.singleFunctor (SheafOfModules.{u}
    (structureSheafRing (ringedSpace X))) 0).obj N
  have hu := boundedDerivedPushforwardIso_hom_app (hom g) K
  have h₀ : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((RingedSpaceModuleAdjunction.modulePushforward (hom g)).rightDerivedFunctorPlusUnith.app
        K)) :=
    (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      (A := SheafOfModules.{u} (structureSheafRing (ringedSpace X)))
      (B := SheafOfModules.{u} (structureSheafRing (ringedSpace Y)))
      (RingedSpaceModuleAdjunction.modulePushforward (hom g)) _
      (RingedSpaceModuleAdjunction.modulePushforward (hom g)).rightDerivedFunctorPlusUnith).2.2.mpr
      inferInstance N
  have h₁ : IsIso ((DerivedCategory.homologyFunctor Y.Modules 0).map
      ((schemeDerivedPushforwardUnit g).app
        ((HomotopyCategory.singleFunctor X.Modules 0).obj N))) :=
    isIso_map_of_comp_eq (DerivedCategory.homologyFunctor Y.Modules 0) hu h₀
      (Iso.isIso_hom ((boundedDerivedPushforwardIso (hom g)).app _))
  dsimp only [pushforwardSingleToDerived]
  simp only [Functor.map_comp]
  infer_instance

/-! ### Vanishing on a chart, from the coordinate model -/

section Chart

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X} (c : BlowupEtaleChart f i)

/-- **Vanishing of `R^q b_*Ω^a` on a chart, from the coordinate model.**  If the degree-`q`
cohomology of `Rb_*Ω^a_{L/R}` vanishes for the coordinate blowup `b : L ⟶ 𝐀^{m+n}_R`, then the
degree-`q` cohomology of `Rb_*Ω^a_{X'/S}` vanishes on the chart: over `U` the blowup is the base
change of the coordinate blowup along the étale chart map, `Ω^a_{X'/S}` is the pullback of
`Ω^a_{L/R}` there, and the cohomology of the derived direct image commutes with flat base change
([Stacks, Tag 02KH]). -/
theorem isZero_restrict_homology_blowUpFormsObj (a : ℕ) (q : ℤ)
    (hcoord : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((schemeDerivedPushforward (coordinateBlowupToAmbient c.R c.m c.n)).obj
        (formsSingle (coordinateBlowupToBase c.R c.m c.n) (a : ℤ))))) :
    IsZero (((DerivedCategory.homologyFunctor X.Modules q).obj
      (blowUpFormsObj f i.ker (a : ℤ))).restrict c.U.ι) := by
  let b := blowUpToBase i.ker
  let V := b ⁻¹ᵁ c.U
  let ΩL := Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase c.R c.m c.n) (a : ℤ)
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (coordinateBlowupToBase c.R c.m c.n) a
  -- the coordinate side, pulled back along the chart
  have h₁ : IsZero ((Scheme.Modules.pullback c.g).obj ((DerivedCategory.homologyFunctor _ q).obj
      ((schemeDerivedPushforward (coordinateBlowupToAmbient c.R c.m c.n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ΩL)))) :=
    Functor.map_isZero _ hcoord
  have h₂ := h₁.of_iso
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.homologyDerivedPushforwardBaseChangeIso
      c.isPullback_blowupMap.flip ΩL q).symm
  -- the chart side
  let e₁ : (Scheme.Modules.restrictFunctor c.U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules q).obj
        (blowUpFormsObj f i.ker (a : ℤ))) ≅ (DerivedCategory.homologyFunctor _ q).obj
      ((Scheme.Modules.restrictFunctor c.U.ι).mapDerivedCategory.obj
        (blowUpFormsObj f i.ker (a : ℤ))) :=
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor c.U.ι) q).app _).symm
  let e₂ := (DerivedCategory.homologyFunctor _ q).mapIso
    (schemeDerivedPushforwardRestrictOpensIso b c.U
      (formsSingle (b ≫ f) (a : ℤ)))
  let e₃ : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
      (formsSingle (b ≫ f) (a : ℤ)) ≅ (DerivedCategory.singleFunctor _ 0).obj
        ((Scheme.Modules.pullback c.blowupMap).obj ΩL) :=
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫ c.blowupFormsIso (a : ℤ))
  let e₄ := (DerivedCategory.homologyFunctor _ q).mapIso
    ((schemeDerivedPushforward (b ∣_ c.U)).mapIso e₃)
  exact h₂.of_iso (e₁ ≪≫ e₂ ≪≫ e₄)

/-- **Vanishing of `R^q b_*Ω^a` on a chart above its codimension.** -/
theorem isZero_restrict_homology_blowUpFormsObj_of_le (a : ℕ) (q : ℤ) (hq : (c.n : ℤ) ≤ q) :
    IsZero (((DerivedCategory.homologyFunctor X.Modules q).obj
      (blowUpFormsObj f i.ker (a : ℤ))).restrict c.U.ι) :=
  isZero_restrict_homology_blowUpFormsObj c a q
    (isZero_homology_coordinateBlowupFormsDerivedDirectImage c.R c.m c.n a q hq)

end Chart

/-! ### Uniqueness -/

section Uniqueness

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- A module whose restriction to an open is zero restricts to zero on every smaller open. -/
theorem isZero_restrict_of_le {F : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (h : IsZero (F.restrict U.ι)) : IsZero (F.restrict V.ι) :=
  (Functor.map_isZero (Scheme.Modules.restrictFunctor (X.homOfLE hVU)) h).of_iso
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVU).symm).app F ≪≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE hVU) U.ι).app F)

attribute [local instance] HasExt.standard

/-- **The cone of `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` admits no nonzero morphism to `Ω^a_{X/S}`**, given
the description of the higher direct images as modules pushed forward from the centre
([Stacks, Tag 0FUU] clause (3)).  This is the uniqueness half of [Stacks, Tag 0G5J]: locally
on `X` the cone has cohomology in degrees `[1, n]` with `n` the codimension of the centre, its
cohomology in degree `n` vanishes, and below that it is pushed forward from the centre, which is
cut out by a regular sequence of length `n`; so [Stacks, Tag 0G5I] applies. -/
theorem subsingleton_hom_cone_blowUpForms_of_homology [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (h3 : ∀ q : ℤ, 1 ≤ q → ∃ G : Z.Modules,
      Nonempty ((DerivedCategory.homologyFunctor X.Modules q).obj
        (blowUpFormsObj f i.ker (a : ℤ)) ≅ (Scheme.Modules.pushforward i).obj G))
    {C : DerivedCategory X.Modules} {p : blowUpFormsObj f i.ker (a : ℤ) ⟶ C}
    {w : C ⟶ (formsSingle f (a : ℤ))⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (blowUpFormsDerivedDirectImage f i.ker (a : ℤ)) p w ∈ distTriang _) :
    Subsingleton (C ⟶ formsSingle f (a : ℤ)) := by
  let b := blowUpToBase i.ker
  let Ω := Scheme.Hom.relativeDifferentialForms f (a : ℤ)
  -- `H^0` of the canonical map is invertible, by [Stacks, Tag 0FUU] clause (1)
  have hH0 : IsIso ((DerivedCategory.homologyFunctor X.Modules 0).map
      (blowUpFormsDerivedDirectImage f i.ker (a : ℤ))) := by
    have := isIso_formsDirectImageComparison_blowUpToBase (f := f) (i := i) hint a
    have := isIso_homology_zero_pushforwardSingleToDerived b
      (Scheme.Hom.relativeDifferentialForms (b ≫ f) (a : ℤ))
    rw [blowUpFormsDerivedDirectImage, formsDerivedDirectImage_eq, Functor.map_comp]
    infer_instance
  have hBGE : (blowUpFormsObj f i.ker (a : ℤ)).IsGE 0 :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward b _ 0 inferInstance
  have hC1 : C.IsGE 1 := Stacks.DerivedCategoryHomVanishing.isGE_one_of_distTriang hT hH0
  have hCq : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor X.Modules q).map p) :=
    Stacks.DerivedCategoryHomVanishing.isIso_homology_mor₂_of_distTriang hT
  let H : ℤ → X.Modules := fun q => (DerivedCategory.homologyFunctor X.Modules q).obj C
  have hlow : ∀ q : ℤ, q < 1 → ∀ V : X.Opens, IsZero ((H q).restrict V.ι) := fun q hq V =>
    Functor.map_isZero _ (DerivedCategory.isZero_of_isGE C 1 q hq)
  let hCiso (q : ℤ) (hq : 1 ≤ q) :=
    @asIso _ _ _ _ ((DerivedCategory.homologyFunctor X.Modules q).map p) (hCq q hq)
  have hpush : ∀ q : ℤ, 1 ≤ q → ∃ G : Z.Modules,
      Nonempty (H q ≅ (Scheme.Modules.pushforward i).obj G) := fun q hq =>
    (h3 q hq).imp fun _ ⟨e⟩ => ⟨(hCiso q hq).symm ≪≫ e⟩
  -- local freeness of `Ω^a_{X/S}`
  have hΩ : Ω.IsLocallyFree := by
    have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f a
    exact (Stacks.Modules.isLocallyFree_iff_localGenerators Ω).mpr
      (this.exists_isFiniteLocallyFreeData.elim fun q hq => ⟨q, hq.1⟩)
  let P : X.Opens → Prop := fun V => IsAffineOpen V ∧
    (∃ ι : Type u, Nonempty (Ω.restrict V.ι ≅ SheafOfModules.free.{u} ι)) ∧
    ((∃ c : BlowupEtaleChart f i, V ≤ c.U) ∨ i ⁻¹ᵁ V = ⊥)
  refine Stacks.SheafOfModules.subsingleton_hom_singleFunctor_of_locally_homology X C Ω P ?_ ?_
  · intro x U hxU
    obtain ⟨W, hxW, ι, ⟨e⟩⟩ := hΩ x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨c, hzc, hcN⟩ := exists_blowupEtaleChart f i z (U ⊓ W) ⟨hxU, hxW⟩
      obtain ⟨V, hV, hxV, hVc⟩ := exists_isAffineOpen_mem_and_subset hzc
      exact ⟨V, hxV, fun y hy => (hcN (hVc hy)).1, hV,
        ⟨ι, ⟨Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictIsoFreeOfLe Ω
          (fun y hy => (hcN (hVc hy)).2) ι e⟩⟩, Or.inl ⟨c, hVc⟩⟩
    · let N : X.Opens :=
        U ⊓ W ⊓ ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨V, hV, hxV, hVN⟩ := exists_isAffineOpen_mem_and_subset (U := N) ⟨⟨hxU, hxW⟩, hx⟩
      refine ⟨V, hxV, fun y hy => (hVN hy).1.1, hV,
        ⟨ι, ⟨Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictIsoFreeOfLe Ω
          (fun y hy => (hVN hy).1.2) ι e⟩⟩, Or.inr ?_⟩
      exact le_antisymm (fun z hz => ((hVN hz).2 ⟨z, rfl⟩).elim) bot_le
  · rintro V ⟨hV, ⟨ι, ⟨e⟩⟩, hc | hoff⟩
    · obtain ⟨c, hVc⟩ := hc
      have hhigh : ∀ q : ℤ, (c.n : ℤ) ≤ q → IsZero ((H q).restrict V.ι) := fun q hq =>
        (le_or_gt 1 q).elim (fun hq1 => isZero_restrict_of_le hVc
          ((isZero_restrict_homology_blowUpFormsObj_of_le c a q hq).of_iso
            ((Scheme.Modules.restrictFunctor c.U.ι).mapIso (hCiso q hq1).symm))) fun hq1 =>
          hlow q hq1 V
      refine ⟨1, c.n - 1, fun q hq => hq.elim (fun hq => hlow q hq V) fun hq => hhigh q (by omega),
        fun q hq₁ hq₂ k hk => ?_⟩
      rcases lt_or_ge q c.n with hqn | hqn
      · obtain ⟨G, ⟨eG⟩⟩ := hpush q hq₁
        refine (Equiv.subsingleton_congr (Iso.homCongr
          ((DerivedCategory.singleFunctor _ 0).mapIso
            ((Scheme.Modules.restrictFunctor V.ι).mapIso eG)) (Iso.refl _))).mpr ?_
        exact (Equiv.subsingleton_congr Abelian.Ext.homEquiv).mp
          (c.subsingleton_ext_restrict_pushforward hV hVc G Ω ι e k (by omega))
      · exact ⟨((DerivedCategory.singleFunctor _ 0).map_isZero (hhigh q hqn)).eq_of_src⟩
    · have hz : ∀ q : ℤ, 1 ≤ q → IsZero ((H q).restrict V.ι) := fun q hq => by
        obtain ⟨G, ⟨eG⟩⟩ := hpush q hq
        exact (AlgebraicGeometry.RegularIdealSheaf.isZero_restrict_pushforward_of_preimage_eq_bot
          i G V hoff).of_iso ((Scheme.Modules.restrictFunctor V.ι).mapIso eG)
      exact ⟨1, 0, fun q hq => hq.elim (fun hq => hlow q hq V) fun hq => hz q (by omega),
        fun q hq₁ _ _ _ => ⟨((DerivedCategory.singleFunctor _ 0).map_isZero (hz q hq₁)).eq_of_src⟩⟩

end Uniqueness

end Stacks.DeRham

end
