module

public import StacksFrontier.RingTheory.Dualizing.TorsionQuotient
public import StacksFrontier.RingTheory.Dualizing.TorsionExtCounterexample

/-!
# Part (1) of Stacks 0AW0 fails over a non-Noetherian ring

Let `A` be a ring, `I ⊆ A` a finitely generated ideal and `N` an `I`-power-torsion `A`-module.
Part (1) of [Stacks, Tag 0AW0] asserts, for every such `A`, that `H^p_I(N) = 0` for all
`p > 0`, where `H^p_I` is the cohomology of the derived `I`-power-torsion functor
`RΓ_I : D(A) ⥤ D(I^∞-torsion)` of [Stacks, Tag 0A6L]. This file proves that this vanishing
forces the comparison maps `Extⁿ_{I^∞-torsion}(M, N) ⟶ Extⁿ_A(M, N)` to be bijective for every
`I`-power-torsion `M` and every `n`, and deduces from part (3) of [Stacks, Tag 0A6P] that the
higher-degree assertions of part (1) of Tag 0AW0 are false for a suitable principal ideal of a
non-Noetherian ring. Over a Noetherian ring they hold: that is the corrected form,
`Stacks.Duality.localCohomology_divide_by_torsion`.

## Main results

* `Stacks.Duality.bijective_mapExt_of_isZero_idealLocalCohomology` — if `H^p_I(N) = 0` for all
  `p > 0`, the inclusion of `I`-power-torsion modules is bijective on `Extⁿ(M, N)` for all
  torsion `M` and all `n`.
* `Stacks.Duality.exists_not_isZero_idealLocalCohomology_primaryComponent` — the clause
  `H^p_I(N) = 0` (`p > 0`, `N = M[I^∞]`) of part (1) of Tag 0AW0 fails for some ring.
* `Stacks.Duality.exists_not_isIso_idealLocalCohomology_map_mkQ` — the clause
  `H^p_I(M) = H^p_I(M/M[I^∞])` (`p > 0`) of part (1) of Tag 0AW0 fails for some ring.
* `Stacks.Duality.localCohomology_divide_by_torsion_corrected_and_counterexample` — the whole
  of Tag 0AW0 as corrected, together with the two counterexamples to the printed form.

## Implementation notes

The argument: the vanishing and the degree-zero identification `H^0_I(N) = N[I^∞] = N` make the
counit `ι(RΓ_I(N)) ⟶ N` of the adjunction `ι ⊣ RΓ_I` an isomorphism, since it is one on every
cohomology module. The triangle identity then makes the unit `N ⟶ RΓ_I(ι N)` an isomorphism,
the derived inclusion `ι` reflecting isomorphisms, and so `ι` is bijective on morphisms into
`N`, hence, after shifting, on `Hom(M, N[n]) = Extⁿ(M, N)`. Part (3) of Tag 0A6P,
`Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule`, gives torsion modules `M`, `N`
over the square-zero extension `ℤ ⋉ (ℚ/ℤ)` with the ideal `(2)` for which this fails in degree
two.

## References

* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard CategoryTheory.HasExt.standard

universe u v w w' t t'

namespace Stacks.Duality

/-! ### Generalities -/

/-- A morphism between zero objects is an isomorphism. -/
private lemma isIso_of_isZero_of_isZero {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)
    (hX : IsZero X) (hY : IsZero Y) : IsIso f :=
  ⟨⟨hY.to_ X, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

/-- If the counit of an adjunction `L ⊣ R` is invertible at `L W` and `L` reflects
isomorphisms, then `L` is bijective on morphisms into `W`. -/
private lemma bijective_map_of_isIso_counit_app {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [hL : L.ReflectsIsomorphisms] (W : C)
    [hW : IsIso (adj.counit.app (L.obj W))] (Z : C) :
    Function.Bijective (fun g : Z ⟶ W ↦ L.map g) := by
  have h := adj.left_triangle_components W
  have : IsIso (L.map (adj.unit.app W)) := by
    rw [IsIso.eq_inv_of_inv_hom_id h]
    infer_instance
  have : IsIso (adj.unit.app W) := isIso_of_reflects_iso _ L
  have heq : (fun g : Z ⟶ W ↦ L.map g) =
      (adj.homEquiv Z (L.obj W)).symm ∘ (fun g : Z ⟶ W ↦ g ≫ adj.unit.app W) := by
    funext g
    simp only [Function.comp_apply, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, h, Category.comp_id]
  rw [heq]
  refine (adj.homEquiv Z (L.obj W)).symm.bijective.comp
    ⟨fun a b hab ↦ (cancel_mono _).1 hab, fun f ↦ ⟨f ≫ inv (adj.unit.app W), by simp⟩⟩

/-- A natural transformation invertible at an object is invertible at every isomorphic
object. -/
private lemma isIso_app_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (e : X ≅ Y) [hα : IsIso (α.app X)] : IsIso (α.app Y) := by
  have : α.app Y = F.map e.inv ≫ α.app X ≫ G.map e.hom := by
    rw [← α.naturality, ← F.map_comp_assoc]
    simp
  rw [this]
  infer_instance

/-- An exact functor that reflects isomorphisms induces a functor on derived categories that
reflects isomorphisms. -/
private lemma reflectsIsomorphisms_mapDerivedCategory
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    rw [DerivedCategory.isIso_iff]
    intro i
    have h : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i).map f) := by
      dsimp
      infer_instance
    have : IsIso (F.map ((DerivedCategory.homologyFunctor C i).map f)) :=
      (NatIso.isIso_map_iff (Dualizing.mapDerivedCategoryHomologyIso F i) f).mp h
    exact isIso_of_reflects_iso _ F

/-- An exact functor does not lower the connectivity of an object of the derived category. -/
private lemma exactFunctor_isGE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero (X.isZero_of_isGE n i hi)).of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso F i).app X)

/-- An exact functor `F` induces a bijection `Extⁿ(X, Y) ⟶ Extⁿ(F X, F Y)` as soon as its
derived functor is bijective on morphisms `X ⟶ Y[n]` of the derived category. -/
private lemma bijective_mapExtAddHom_of_bijective_map_shift
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X Y : C) (n : ℕ)
    (hff : Function.Bijective (fun α : ((DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ↦ F.mapDerivedCategory.map α)) :
    Function.Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  let Φ := F.mapDerivedCategory
  let e := F.mapDerivedCategorySingleFunctor (0 : ℤ)
  let sX := (DerivedCategory.singleFunctor C 0).obj X
  let sY := (DerivedCategory.singleFunctor C 0).obj Y
  let iso₂ : Φ.obj (sY⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦(n : ℤ)⟧ :=
    (Φ.commShiftIso (n : ℤ)).app sY ≪≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).mapIso (asIso (e.hom.app Y))
  let Ψ : ShiftedHom sX sY (n : ℤ) → ShiftedHom ((DerivedCategory.singleFunctor D 0).obj (F.obj X))
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y)) (n : ℤ) := fun α ↦
    e.inv.app X ≫ ShiftedHom.map α Φ ≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map (e.hom.app Y)
  have hΨ : Function.Bijective Ψ := by
    have heq : Ψ =
        ((asIso (e.hom.app X)).homCongr iso₂) ∘ (fun α : (sX ⟶ sY⟦(n : ℤ)⟧) ↦ Φ.map α) := by
      funext α
      simp [Ψ, ShiftedHom.map, Iso.homCongr, iso₂, Category.assoc]
    rw [heq]
    exact (Iso.homCongr (asIso (e.hom.app X)) iso₂).bijective.comp hff
  have hcomp : (Abelian.Ext.homEquiv (C := D) (X := F.obj X) (Y := F.obj Y) (n := n)) ∘
      (F.mapExtAddHom.{w, w'} X Y n) =
      Ψ ∘ (Abelian.Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)) := by
    funext a
    exact Abelian.Ext.mapExactFunctor_hom F a
  refine ((Abelian.Ext.homEquiv (C := D) (X := F.obj X) (Y := F.obj Y)
    (n := n)).bijective.of_comp_iff' ⇑(F.mapExtAddHom.{w, w'} X Y n)).mp ?_
  rw [hcomp]
  exact hΨ.comp (Abelian.Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)).bijective

/-- If a functor commuting with shifts is bijective on morphisms into `W⟦n⟧⟦-n⟧`, it is
bijective on morphisms into `W⟦n⟧` out of `Z`. -/
private lemma bijective_map_shift_of_bijective_map_shift_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) [L.CommShift ℤ] (Z W : C) (n : ℤ)
    (h : Function.Bijective (fun g : Z⟦-n⟧ ⟶ W⟦n⟧⟦-n⟧ ↦ L.map g)) :
    Function.Bijective (fun g : Z ⟶ W⟦n⟧ ↦ L.map g) := by
  have hC : Function.Bijective (fun g : Z ⟶ W⟦n⟧ ↦ g⟦-n⟧') :=
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C (-n))).map_bijective _ _
  have hD : Function.Injective (fun g : L.obj Z ⟶ L.obj (W⟦n⟧) ↦ g⟦-n⟧') :=
    (shiftFunctor D (-n)).map_injective
  have h₁ : Function.Bijective (fun g : Z ⟶ W⟦n⟧ ↦ L.map (g⟦-n⟧')) := h.comp hC
  let e := L.commShiftIso (-n)
  have h₂ : Function.Bijective (fun g : Z ⟶ W⟦n⟧ ↦ (L.map g)⟦-n⟧') := by
    have heq : (fun g : Z ⟶ W⟦n⟧ ↦ (L.map g)⟦-n⟧') =
        (fun k ↦ e.inv.app Z ≫ k ≫ e.hom.app (W⟦n⟧)) ∘
          (fun g : Z ⟶ W⟦n⟧ ↦ L.map (g⟦-n⟧')) := by
      funext g
      simp [e]
    rw [heq]
    exact (Iso.homCongr (e.app Z) (e.app (W⟦n⟧))).bijective.comp h₁
  refine ⟨fun a b hab ↦ h₂.1 (by simp only at hab ⊢; rw [hab]), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := h₂.2 (y⟦-n⟧')
  exact ⟨x, hD hx⟩

/-! ### Higher vanishing makes the torsion `Ext` comparison bijective -/

section Comparison

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- The torsion submodule of an `I`-power-torsion module is the whole module, so its
inclusion is an isomorphism. -/
private lemma isIso_ofHom_primaryComponent_subtype (N : ModuleCat.{v} A)
    (hN : IsIPowerTorsion A N I) :
    IsIso (ModuleCat.ofHom (Ideal.primaryComponent N I).subtype) := by
  have hsurj : Function.Surjective (Ideal.primaryComponent N I).subtype := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [Ideal.primaryComponent_mem]
    obtain ⟨n, -, hkill⟩ := hN x
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact hkill a a.property
  let eq : Ideal.primaryComponent N I ≃ₗ[A] N :=
    LinearEquiv.ofBijective (Ideal.primaryComponent N I).subtype
      ⟨Subtype.val_injective, hsurj⟩
  exact (eq.toModuleIso).isIso_hom

/-- If the higher ideal local cohomology of an `I`-power-torsion module `N` vanishes, the
counit `ι(RΓ_I(N)) ⟶ N` of the adjunction of [Stacks, Tag 0A6L] is invertible at `N`. -/
theorem isIso_derivedPowerTorsionCounit_app_of_isZero_idealLocalCohomology
    (N : ModuleCat.{max u v} A) (hN : IsIPowerTorsion A N I)
    (hH : ∀ p : ℤ, 0 < p → IsZero ((idealLocalCohomology.{u, v} A I hI p).obj N)) :
    IsIso ((Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N)) := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := Dualizing.powerTorsionModuleProperty_isSerreClass A I hI
  let : PreservesFiniteLimits P.ι := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N
  let RX := (Dualizing.derivedPowerTorsion.{u, v} A I hI).obj X
  let c := (Dualizing.powerTorsionComparisonCompInclusionIso A I hI).app RX
  rw [DerivedCategory.isIso_iff]
  intro p
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · have : RX.IsGE 0 :=
      derived_rightAdjoint_isGE P.ι (Dualizing.derivedPowerTorsionAdjunction.{u, v} A I hI) X 0
    have := exactFunctor_isGE P.ι RX 0
    exact isIso_of_isZero_of_isZero _ ((P.ι.mapDerivedCategory.obj RX).isZero_of_isGE 0 p hp)
      (X.isZero_of_isGE 0 p hp)
  · obtain ⟨e, he⟩ := idealLocalCohomology_zero_iso_torsion.{u, v} A I hI N
    have := isIso_ofHom_primaryComponent_subtype A I N hN
    have h₁ : IsIso (idealLocalCohomologyToModule.{u, v} A I hI N) := by
      rw [← he]
      infer_instance
    let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0
    let ε := (Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app X
    have h₃ : IsIso (H.map (c.hom ≫ ε) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0).hom.app
          N) := h₁
    have h₂ : IsIso (H.map (c.hom ≫ ε)) := IsIso.of_isIso_comp_right _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0).hom.app N)
    have h₄ : IsIso (H.map c.hom ≫ H.map ε) := by
      convert h₂ using 1
      exact (H.map_comp c.hom ε).symm
    exact IsIso.of_isIso_comp_left (H.map c.hom) (H.map ε)
  · exact isIso_of_isZero_of_isZero _
      ((hH p hp).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).mapIso c.symm))
      (X.isZero_of_isLE 0 p hp)

/-- If the higher ideal local cohomology `H^p_I(N)`, `p > 0`, of an `I`-power-torsion module `N`
vanishes, then the inclusion of `I`-power-torsion modules induces a bijection
`Extⁿ_{I^∞-torsion}(M, N) ⟶ Extⁿ_A(M, N)` for every `I`-power-torsion module `M` and every
`n`. -/
theorem bijective_mapExt_of_isZero_idealLocalCohomology
    (M N : Dualizing.PowerTorsionModule.{u, max u v} A I hI)
    (hH : ∀ p : ℤ, 0 < p → IsZero ((idealLocalCohomology.{u, v} A I hI p).obj N.obj))
    (n : ℕ) :
    Function.Bijective
      ((Dualizing.powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N n) := by
  let P := Dualizing.powerTorsionModuleProperty.{u, max u v} A I hI
  let L := P.ι.mapDerivedCategory
  let adj := Dualizing.derivedPowerTorsionAdjunction.{u, v} A I hI
  have : P.ι.ReflectsIsomorphisms := inferInstance
  have hL : L.ReflectsIsomorphisms := reflectsIsomorphisms_mapDerivedCategory P.ι
  let sM := (DerivedCategory.singleFunctor P.FullSubcategory 0).obj M
  let sN := (DerivedCategory.singleFunctor P.FullSubcategory 0).obj N
  have h₀ : IsIso (adj.counit.app ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
      N.obj)) :=
    isIso_derivedPowerTorsionCounit_app_of_isZero_idealLocalCohomology.{u, v} A I hI N.obj
      N.property hH
  have h₁ : IsIso (adj.counit.app (L.obj sN)) :=
    isIso_app_of_iso (hα := h₀) adj.counit
      ((P.ι.mapDerivedCategorySingleFunctor 0).app N).symm
  let e : sN ≅ (sN⟦(n : ℤ)⟧)⟦-(n : ℤ)⟧ :=
    ((shiftFunctorCompIsoId _ (n : ℤ) (-(n : ℤ)) (by omega)).app sN).symm
  have h₂ : IsIso (adj.counit.app (L.obj ((sN⟦(n : ℤ)⟧)⟦-(n : ℤ)⟧))) :=
    isIso_app_of_iso (hα := h₁) adj.counit (L.mapIso e)
  apply bijective_mapExtAddHom_of_bijective_map_shift
  exact bijective_map_shift_of_bijective_map_shift_neg L sM sN (n : ℤ)
    (bijective_map_of_isIso_counit_app (hL := hL) (hW := h₂) adj _ _)

end Comparison

/-! ### The counterexamples -/

/-- Ideal local cohomology of a zero module vanishes in every degree. -/
private lemma isZero_idealLocalCohomology_of_isZero (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (p : ℤ) (Q : ModuleCat.{max u v} A) (hQ : IsZero Q) :
    IsZero ((idealLocalCohomology.{u, v} A I hI p).obj Q) := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := Dualizing.powerTorsionModuleProperty_isSerreClass A I hI
  let : PreservesFiniteLimits P.ι := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  let adj := Dualizing.derivedPowerTorsionAdjunction.{u, v} A I hI
  let : (Dualizing.derivedPowerTorsion.{u, v} A I hI).Additive := adj.right_adjoint_additive
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj Q
  let RX := (Dualizing.derivedPowerTorsion.{u, v} A I hI).obj X
  have hX : IsZero X := Functor.map_isZero _ hQ
  have hRX : IsZero RX := Functor.map_isZero _ hX
  have hL : IsZero (P.ι.mapDerivedCategory.obj RX) := Functor.map_isZero _ hRX
  exact (Functor.map_isZero (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p) hL).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) p).mapIso
      ((Dualizing.powerTorsionComparisonCompInclusionIso A I hI).app RX))

/-- The `I`-primary component of an `I`-power-torsion module, as a module, is isomorphic to the
module. -/
private noncomputable def primaryComponentIsoOfIsIPowerTorsion (A : Type u) [CommRing A]
    (I : Ideal A) (N : ModuleCat.{v} A) (hN : IsIPowerTorsion A N I) :
    ModuleCat.of A (Ideal.primaryComponent N I) ≅ N :=
  have := isIso_ofHom_primaryComponent_subtype A I N hN
  asIso (ModuleCat.ofHom (Ideal.primaryComponent N I).subtype)

/-- **Stacks 0AW0, part (1), the printed clause `H^p_I(N) = 0` is false.** There are a ring `A`,
a finitely generated (indeed principal) ideal `I`, a module `M` and a degree `p > 0` with
`H^p_I(M[I^∞]) ≠ 0`. The ring is necessarily not Noetherian, by
`Stacks.Duality.idealLocalCohomology_torsion_higher`. -/
@[stacks 0AW0 "counterexample to part (1), higher cohomology of the torsion submodule, over a \
non-Noetherian ring"]
theorem exists_not_isZero_idealLocalCohomology_primaryComponent :
    ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{0} A) (p : ℤ),
      0 < p ∧ ¬ IsZero ((idealLocalCohomology.{0, 0} A I hI p).obj
        (ModuleCat.of A (Ideal.primaryComponent M I))) := by
  obtain ⟨A, _, I, hI, M, N, hns⟩ := Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule
  by_contra hcon
  push Not at hcon
  have hH : ∀ p : ℤ, 0 < p → IsZero ((idealLocalCohomology.{0, 0} A I hI p).obj N.obj) :=
    fun p hp ↦ (hcon A inferInstance I hI N.obj p hp).of_iso
      ((idealLocalCohomology.{0, 0} A I hI p).mapIso
        (primaryComponentIsoOfIsIPowerTorsion A I N.obj N.property)).symm
  exact hns (bijective_mapExt_of_isZero_idealLocalCohomology.{0, 0} A I hI M N hH 2).2

/-- **Stacks 0AW0, part (1), the printed clause `H^p_I(M) = H^p_I(M/M[I^∞])` is false.** There
are a ring `A`, a finitely generated (indeed principal) ideal `I`, a module `M` and a degree
`p > 0` for which the quotient map `M ⟶ M/M[I^∞]` does not induce an isomorphism on `H^p_I`.
The ring is necessarily not Noetherian, by
`Stacks.Duality.idealLocalCohomology_quotient_map_higher`. -/
@[stacks 0AW0 "counterexample to part (1), higher cohomology of the quotient, over a \
non-Noetherian ring"]
theorem exists_not_isIso_idealLocalCohomology_map_mkQ :
    ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{0} A) (p : ℤ),
      0 < p ∧ ¬ IsIso ((idealLocalCohomology.{0, 0} A I hI p).map
        (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ)) := by
  obtain ⟨A, _, I, hI, M, p, hp, hne⟩ := exists_not_isZero_idealLocalCohomology_primaryComponent
  -- For the torsion module `N = M[I^∞]` the quotient `N/N[I^∞]` is zero.
  let N := ModuleCat.of A (Ideal.primaryComponent M I)
  have hN : IsIPowerTorsion A N I :=
    ((Dualizing.powerTorsionFunctor.{0, 0} A I).obj M).property
  refine ⟨A, inferInstance, I, hI, N, p, hp, fun hiso ↦ hne ?_⟩
  have hQ : IsZero (ModuleCat.of A (N ⧸ Ideal.primaryComponent N I)) := by
    have htop : Ideal.primaryComponent N I = ⊤ := by
      have := isIso_ofHom_primaryComponent_subtype A I N hN
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, rfl⟩ := ((ModuleCat.epi_iff_surjective _).mp inferInstance :
        Function.Surjective (ModuleCat.ofHom (Ideal.primaryComponent N I).subtype)) x
      exact y.property
    rw [ModuleCat.isZero_iff_subsingleton]
    rw [htop]
    infer_instance
  have hZ := isZero_idealLocalCohomology_of_isZero.{0, 0} A I hI p _ hQ
  exact hZ.of_iso (asIso ((idealLocalCohomology.{0, 0} A I hI p).map
      (ModuleCat.ofHom (Ideal.primaryComponent N I).mkQ)))

/-! ### The whole of Stacks 0AW0, corrected -/

/-- **Stacks 0AW0, corrected, with the counterexample to the printed form.** Let `A` be a ring,
`I ⊆ A` a finitely generated ideal, `M` an `A`-module and `Z = V(I)`. Then
`H^0_I(M) = H^0_Z(M)`, the common value `N` being the `I`-power-torsion submodule `M[I^∞]`
(both identifications compatible with the canonical maps down to `M`), and, writing
`M' = M/N`,

1. `H^0_I(M') = 0`, and, when `A` is Noetherian, `H^p_I(M) = H^p_I(M')` and `H^p_I(N) = 0`
   for all `p > 0`;
2. `H^0_Z(M') = 0`, `H^p_Z(M) = H^p_Z(M')` and `H^p_Z(N) = 0` for all `p > 0`.

The source states the two positive-degree assertions of part (1) for every ring. They fail in
that generality: the last two conjuncts exhibit a ring, a principal ideal, a module and a
positive degree for which `H^p_I(M[I^∞]) ≠ 0`, and likewise one for which the quotient map
`M ⟶ M/M[I^∞]` is not an isomorphism on `H^p_I`. Everything else is stated, and holds, over an
arbitrary ring. -/
@[stacks 0AW0 "the statement with part (1) in positive degrees over a Noetherian ring, and \
counterexamples to part (1) in positive degrees over a non-Noetherian ring"]
theorem localCohomology_divide_by_torsion_corrected_and_counterexample :
    (∀ (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A),
      (∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
          (supportLocalCohomology.{u, v} A I hI 0).obj M,
        e.hom ≫ supportLocalCohomologyToModule.{u, v} A I hI M =
          idealLocalCohomologyToModule.{u, v} A I hI M) ∧
      (∃ e : (idealLocalCohomology.{u, v} A I hI 0).obj M ≅
          ModuleCat.of A (Ideal.primaryComponent M I),
        e.hom ≫ ModuleCat.ofHom (Submodule.subtype (Ideal.primaryComponent M I)) =
          idealLocalCohomologyToModule.{u, v} A I hI M) ∧
      (IsZero ((idealLocalCohomology.{u, v} A I hI 0).obj
            (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) ∧
        (IsNoetherianRing A →
          (∀ p : ℤ, 0 < p → IsIso ((idealLocalCohomology.{u, v} A I hI p).map
            (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))) ∧
          ∀ p : ℤ, 0 < p → IsZero ((idealLocalCohomology.{u, v} A I hI p).obj
            (ModuleCat.of A (Ideal.primaryComponent M I))))) ∧
      (IsZero ((supportLocalCohomology.{u, v} A I hI 0).obj
            (ModuleCat.of A (M ⧸ Ideal.primaryComponent M I))) ∧
        (∀ p : ℤ, 0 < p → IsIso ((supportLocalCohomology.{u, v} A I hI p).map
          (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))) ∧
        ∀ p : ℤ, 0 < p → IsZero ((supportLocalCohomology.{u, v} A I hI p).obj
          (ModuleCat.of A (Ideal.primaryComponent M I))))) ∧
    (∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{0} A) (p : ℤ),
      0 < p ∧ ¬ IsZero ((idealLocalCohomology.{0, 0} A I hI p).obj
        (ModuleCat.of A (Ideal.primaryComponent M I)))) ∧
    (∃ (A : Type) (_ : CommRing A) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{0} A) (p : ℤ),
      0 < p ∧ ¬ IsIso ((idealLocalCohomology.{0, 0} A I hI p).map
        (ModuleCat.ofHom (Ideal.primaryComponent M I).mkQ))) :=
  ⟨fun A _ I hI M ↦
    ⟨idealLocalCohomology_zero_iso_supportLocalCohomology_zero.{u, v} A I hI M,
      idealLocalCohomology_zero_iso_torsion.{u, v} A I hI M,
      ⟨idealLocalCohomology_quotient_zero.{u, v} A I hI M, fun h ↦ haveI := h
        ⟨fun p hp ↦ idealLocalCohomology_quotient_map_higher.{u, v} A I hI M p hp,
          fun p hp ↦ idealLocalCohomology_torsion_higher.{u, v} A I hI M p hp⟩⟩,
      supportLocalCohomology_quotient_zero.{u, v} A I hI M,
      fun p hp ↦ supportLocalCohomology_quotient_map_higher.{u, v} A I hI M p hp,
      fun p hp ↦ isZero_supportLocalCohomology_primaryComponent.{u, v} A I hI M p hp⟩,
    exists_not_isZero_idealLocalCohomology_primaryComponent,
    exists_not_isIso_idealLocalCohomology_map_mkQ⟩

end Stacks.Duality

end
