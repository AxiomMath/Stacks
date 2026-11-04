module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.BoundedBelowCompositionToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.DegreeZeroIsoUnit

/-!
# `Rj_! ⟶ Rj_*` and the open immersion case of [Stacks, Tag 0F7B], on `D⁺`

For a cartesian square `b ≫ f̄ = f' ≫ i` with `b`, `i` open immersions and `f̄` proper, the open
immersion case of [Stacks, Tag 0F7B] is the map `φ : i_! Rf'_* ⟶ Rf̄_* Rb_!` adjoint under
`Ri_! ⊣ i^{-1}` to `Rf'_* ≅ i^{-1} Rf̄_* Rb_!`
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageMap`). This file proves that
it is compatible with the maps `Rj_! ⟶ Rj_*` of [Stacks, Tag 0H6X]:
`φ` followed by `Rf̄_*` of `Rb_! ⟶ Rb_*` and the composition isomorphism
`Rf̄_* Rb_* ≅ R(b ≫ f̄)_*` is `Ri_! ⟶ Ri_*` at `Rf'_*` followed by
`Ri_* Rf'_* ≅ R(f' ≫ i)_*`. It is checked on the open `Y`, where every map in sight is the
identity, read through base change along the open immersion `i`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageComp_id_left_hom_app`: the left unit law
  `Rg_* ≅ R(𝟙)_* ⋙ Rg_*` of the composition of derived direct images.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange_self`:
  `Rb_! ⟶ Rb_*` restricted along `b`, followed by base change along `b`, is the unit of `R(𝟙)_*`.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage`:
  **the compatibility of the open immersion case of [Stacks, Tag 0F7B] with `Rj_! ⟶ Rj_*`.**

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Abstract rearrangements -/

section Algebra

/-- A map out of a left adjoint, written as the transpose of `α` followed by `X`, is `e` as soon
as `α ≫ R X` is the transpose of `e`. -/
theorem Adjunction.homEquiv_symm_comp_eq_of {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M : C} {N Z : D} (α : M ⟶ R.obj N) (X : N ⟶ Z)
    (e : L.obj M ⟶ Z) (h : α ≫ R.map X = adj.unit.app M ≫ R.map e) :
    (L.map α ≫ adj.counit.app N) ≫ X = e := by
  have h₁ : (L.map α ≫ adj.counit.app N) ≫ X = (adj.homEquiv M Z).symm (α ≫ R.map X) := by
    rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit]
  rw [h₁, h]
  exact ((adj.homEquiv M Z).symm_apply_eq).2 (Adjunction.homEquiv_unit adj M Z e).symm

/-- The cancellation behind `etaleModuleDerivedDirectImageComp_id_left_hom_app`, stated on
variables. -/
private theorem left_unit_chain {C : Type*} [Category* C] {a b c : C} (x y : a ⟶ b) (z : b ⟶ c)
    [IsIso z] (w : a ⟶ c) (h₁ : x ≫ z = w) (h₂ : y ≫ z = w) : x = y :=
  (cancel_mono z).1 (h₁.trans h₂.symm)

/-- The chase behind `etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange_self`,
stated on variables. -/
private theorem self_chain {C : Type*} [Category* C] {K K' A₁ A₂ B₁ B₂ T : C}
    (ω : K ⟶ K') (ζ : K ⟶ A₁) (ζ' : K' ⟶ A₂) (rω : A₁ ⟶ A₂) (ε : A₁ ⟶ B₁) (ε' : A₂ ⟶ B₂)
    (sω : B₁ ⟶ B₂) (l : B₂ ⟶ B₁) (bc : B₁ ⟶ T) (r : K' ⟶ T)
    (hζ : ω ≫ ζ' = ζ ≫ rω) (hε : rω ≫ ε' = ε ≫ sω) (hl : sω ≫ l = 𝟙 _)
    (hO : ζ' ≫ ε' ≫ l ≫ bc = r) : ζ ≫ ε ≫ bc = ω ≫ r := by
  rw [← hO, reassoc_of% hζ, reassoc_of% hε, reassoc_of% hl]

/-- The chase behind `etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage`, on the
side of `Rb_! ⟶ Rb_*`, stated on variables. -/
private theorem left_chain {C : Type*} [Category* C]
    {M R N₂ I₁ I₂ I₃ T₀ S₀ S₁ S₂ T₁ : C} (α : M ⟶ R) (rX : R ⟶ N₂) (ρh : N₂ ⟶ I₃)
    (bch : I₃ ⟶ T₀) (ρN : R ⟶ I₁) (iX : I₁ ⟶ I₃) (iε : I₁ ⟶ I₂) (il : I₂ ⟶ I₃)
    (bcfb : I₁ ⟶ S₀) (bcfb' : I₂ ⟶ S₁) (fε : S₀ ⟶ S₁) (fbc : S₁ ⟶ S₂) (lf : S₂ ⟶ T₀)
    (fζ : M ⟶ S₀) (fω : M ⟶ T₁) (fR : T₁ ⟶ S₂) (lf₀ : T₁ ⟶ M) (fid : M ⟶ T₀)
    (hρ : rX ≫ ρh = ρN ≫ iX) (hiX : iX = iε ≫ il) (hbc : iε ≫ bcfb' = bcfb ≫ fε)
    (hcomp : il ≫ bch = bcfb' ≫ fbc ≫ lf) (hα : α ≫ ρN ≫ bcfb = fζ)
    (hT : fζ ≫ fε ≫ fbc = fω ≫ fR) (hn : fR ≫ lf = lf₀ ≫ fid) (hlid : fω ≫ lf₀ = 𝟙 M) :
    α ≫ rX ≫ ρh ≫ bch = fid := by
  rw [reassoc_of% hρ, hiX, Category.assoc, hcomp, reassoc_of% hbc, reassoc_of% hα,
    reassoc_of% hT, hn, reassoc_of% hlid]

/-- The chase behind `etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage`, on the
side of `Ri_! ⟶ Ri_*`, stated on variables. -/
private theorem right_chain {C : Type*} [Category* C] {M R N₂ I₁ I₂ I₃ T₀ : C}
    (un : M ⟶ R) (rY : R ⟶ N₂) (ρh : N₂ ⟶ I₃) (bch : I₃ ⟶ T₀) (ρM : R ⟶ I₁) (iY : I₁ ⟶ I₃)
    (iε : I₁ ⟶ I₂) (il : I₂ ⟶ I₃) (ζ : M ⟶ I₁) (fid : M ⟶ T₀)
    (hρ : rY ≫ ρh = ρM ≫ iY) (hiY : iY = iε ≫ il) (hu : un ≫ ρM = ζ)
    (hO : ζ ≫ iε ≫ il ≫ bch = fid) :
    un ≫ rY ≫ ρh ≫ bch = fid := by
  rw [reassoc_of% hρ, hiY, Category.assoc, reassoc_of% hu, hO]

/-- Cancelling an inverse pair across a composite, stated on variables. -/
private theorem comp_eq_of_hom_inv {C : Type*} [Category* C] {a b c d : C} (x : a ⟶ b)
    (y : b ⟶ c) (z : c ⟶ d) (w : d ⟶ a) (v : a ⟶ d) [Mono w] (h₁ : x ≫ y ≫ z ≫ w = 𝟙 a)
    (h₂ : v ≫ w = 𝟙 a) : x ≫ y ≫ z = v :=
  (cancel_mono w).1 (by rw [Category.assoc, Category.assoc, h₁, h₂])

end Algebra

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-! ### The left unit law of the composition of derived direct images -/

section LeftUnit

/-- **The left unit law of the composition of derived direct images**: `Rg_* ≅ R(𝟙)_* ⋙ Rg_*`
is `Rg_*` of the unit `𝟭 ⟶ R(𝟙)_*`. -/
theorem etaleModuleDerivedDirectImageComp_id_left_hom_app {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hg : g = 𝟙 X ≫ g) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 X) g g hg).hom.app K =
      (etaleModuleDerivedDirectImage.{u, 0} Λ g).map
        ((etaleModuleDerivedDirectImageIdUnit Λ X).app K) := by
  have A := congrArg (fun t => NatTrans.app t K) (etaleModuleDerivedDirectImageComp_assoc Λ
    (𝟙 X) (𝟙 X) g (𝟙 X) (Category.comp_id _).symm g hg g hg hg)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  rw [← map_etaleModuleDerivedDirectImageIdUnit_app] at A
  have n := (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 X) g g hg).hom.naturality
    ((etaleModuleDerivedDirectImageIdUnit Λ X).app K)
  simp only [Functor.comp_map] at n
  exact left_unit_chain _ _
    ((etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 X) g g hg).hom.app
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 X)).obj K)) _ A.symm n

end LeftUnit

/-! ### `Rj_! ⟶ Rj_*` restricted along `j` -/

section Self

/-- `etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange` for an arbitrary spelling
of the composite. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange'
    {X Y Ub : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ Ub) [IsOpenImmersion i] (fi : X ⟶ Ub)
    (hfi : fi = f ≫ i) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K)) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ f i fi hfi).inv.app K) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ fi f i (𝟙 X)
        (by rw [hfi, Category.id_comp])).app K =
    (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
      ((etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app K) := by
  subst hfi
  exact etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange Λ f i K

/-- **`Rb_! ⟶ Rb_*` restricted along the open immersion `b`, followed by base change along `b`,
is the unit `𝟭 ⟶ R(𝟙)_*`**, read through `b^{-1} Rb_! ≅ 𝟭` and `(𝟙)^{-1} ≅ 𝟭`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange_self {P T : Scheme.{u}}
    (b : P ⟶ T) [IsOpenImmersion b] (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).inv.app K ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
        ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app K) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ b (𝟙 P) b (𝟙 P) rfl).app K =
    (etaleModuleDerivedDirectImageIdUnit Λ P).app K ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 P)).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ P).inv.app K) := by
  let ω := (etaleModuleDerivedDirectImageIdUnit Λ P).app K
  let lb := etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 P) b b (Category.id_comp _).symm
  have hO := etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange' Λ (𝟙 P) b b
    (Category.id_comp _).symm K
  have hζ := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).inv.naturality ω
  have hε : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).map ω) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
        ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 P)).obj K)) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app K) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ b).map ω) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).naturality ω)
  have hl : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ b).map ω) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map (lb.inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, ← etaleModuleDerivedDirectImageComp_id_left_hom_app Λ b
      (Category.id_comp _).symm, Iso.hom_inv_id_app]
    exact CategoryTheory.Functor.map_id _ _
  simp only [Functor.id_map, Functor.comp_map] at hζ
  exact self_chain _ _ _ _ _ _ _ _ _ _ hζ hε hl hO

end Self

/-! ### The open immersion case of [Stacks, Tag 0F7B] against `Rj_! ⟶ Rj_*` -/

section OpenBaseChange

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

/-- The inverse of `Rf'_* ≅ i^{-1} Rf̄_* Rb_!` at an object: the comparison of derived restriction
with inverse image, the base change map along `i` and `Rf'_*` of `b^{-1} Rb_! ≅ 𝟭`. -/
lemma etaleModuleDerivedDirectImageIsoRestriction_inv_app
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedDirectImageIsoRestriction.{u, 0} Λ fb i b f' sq).inv.app K =
      (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
            ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K)) ≫
        (etaleModuleDerivedBaseChange.{u, 0} Λ fb f' i b sq.w.symm).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
          ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.app K) := by
  simp only [Functor.comp_obj, etaleModuleDerivedDirectImageIsoRestriction, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, asIso_hom, Functor.isoWhiskerRight_inv,
    Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.id_obj,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.comp_id]
  rfl

/-- **The open immersion case of [Stacks, Tag 0F7B] is compatible with `Rj_! ⟶ Rj_*`.** For a
cartesian square `b ≫ f̄ = f' ≫ i` with `b`, `i` open immersions, the map
`φ : i_! Rf'_* K ⟶ Rf̄_* Rb_! K` followed by `Rf̄_*` of `Rb_! K ⟶ Rb_* K` and by
`Rf̄_* Rb_* ≅ R(f' ≫ i)_*` is `Ri_! ⟶ Ri_*` at `Rf'_* K` followed by
`Ri_* Rf'_* ≅ R(f' ≫ i)_*`. -/
theorem etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedExtensionByZeroDirectImageMap.{u, 0} Λ fb i b f' sq).app K ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ fb).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app K) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm).inv.app K =
      (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj K) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl).inv.app K := by
  let adj := etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i
  let E := etaleModuleDerivedDirectImageIsoRestriction.{u, 0} Λ fb i b f' sq
  let ρ := etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i
  let BC := etaleModuleDerivedBaseChange.{u, 0} Λ fb f' i b sq.w.symm
  have hsq : IsPullback (𝟙 P) f' (f' ≫ i) i := by
    have h1 : IsPullback (𝟙 P) f' f' (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h2 : IsPullback (𝟙 Y) (𝟙 Y) i i := (mono_iff_isPullback i).1 inferInstance
    simpa using h1.paste_vert h2
  let BCh := etaleModuleDerivedBaseChange.{u, 0} Λ (f' ≫ i) f' i (𝟙 P) (Category.id_comp _).symm
  have : IsIso (BCh.app K) := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ (f' ≫ i)
    hsq K
  let M := (etaleModuleDerivedDirectImage.{u, 0} Λ f').obj K
  let N := (etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K)
  let X := (etaleModuleDerivedDirectImage.{u, 0} Λ fb).map
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app K) ≫
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm).inv.app K
  let Y := (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).app M ≫
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl).inv.app K
  have hφ : (etaleModuleDerivedExtensionByZeroDirectImageMap.{u, 0} Λ fb i b f' sq).app K =
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).map (E.hom.app K) ≫ adj.counit.app N := rfl
  -- the side of `Rb_! ⟶ Rb_*`
  have hα : E.hom.app K ≫ ρ.hom.app N ≫
      BC.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K) =
      (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).inv.app K) :=
    comp_eq_of_hom_inv _ _ _ ((etaleModuleDerivedDirectImage.{u, 0} Λ f').map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.app K)) _
      ((congrArg (fun t => E.hom.app K ≫ t)
        (etaleModuleDerivedDirectImageIsoRestriction_inv_app Λ fb i b f' sq K)).symm.trans
          (E.hom_inv_id_app K))
      ((Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ K)).trans
        (CategoryTheory.Functor.map_id _ _)))
  have hbc := BC.naturality ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ b).app K)
  have hcomp := NatTrans.congr_app (etaleModuleDerivedBaseChange_comp Λ b fb (f' ≫ i) sq.w.symm
    (𝟙 P) f' f' (Category.id_comp _).symm (𝟙 P) b i rfl sq.w.symm (Category.id_comp _).symm) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hcomp
  have hcomp' := conj_inv_chain _ _ _ _ _ _ _ hcomp
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        (Iso.inv_hom_id_app _ K)).trans (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app _ _)
  have hT := congrArg (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
    (etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange_self Λ b K)
  simp only [Functor.map_comp] at hT
  have hn := (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 P) f' f'
    (Category.id_comp _).symm).inv.naturality
      ((etaleModuleDerivedInverseImagePlusIdIso Λ P).inv.app K)
  simp only [Functor.comp_map] at hn
  have hlid : (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
        ((etaleModuleDerivedDirectImageIdUnit Λ P).app K) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 P) f' f'
        (Category.id_comp _).symm).inv.app K = 𝟙 _ := by
    rw [← etaleModuleDerivedDirectImageComp_id_left_hom_app Λ f' (Category.id_comp _).symm]
    exact Iso.hom_inv_id_app _ _
  have L := left_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ρ.hom.naturality X)
    (Functor.map_comp _ _ _) hbc hcomp' hα hT hn hlid
  -- the side of `Ri_! ⟶ Ri_*`
  have hu : adj.unit.app M ≫ ρ.hom.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj M) =
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv.app M := by
    rw [show adj.unit.app M = (etaleModuleDerivedExtensionByZeroCompRestrictionIso Λ i).inv.app M
      from NatTrans.congr_app (etaleModuleDerivedExtensionByZeroAdj_unit_eq Λ i) M]
    rfl
  have R := right_chain _ _ _ _ _ _ _ _ _ _ (ρ.hom.naturality Y) (Functor.map_comp _ _ _) hu
    (etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange Λ f' i K)
  -- both transposes agree after restriction against inverse image and base change along `i`
  have H : E.hom.app K ≫ (etaleModuleDerivedRestriction.{u, 0} Λ i).map X =
      adj.unit.app M ≫ (etaleModuleDerivedRestriction.{u, 0} Λ i).map Y :=
    (cancel_mono (ρ.hom.app _ ≫ BCh.app K)).1
      ((Category.assoc _ _ _).trans (L.trans (R.symm.trans (Category.assoc _ _ _).symm)))
  rw [hφ]
  exact Adjunction.homEquiv_symm_comp_eq_of adj (E.hom.app K) X Y H

include sq in
/-- The open immersion case of [Stacks, Tag 0F7B] on the whole of `D⁺`, over a torsion ring, is
the map `φ` backwards. -/
lemma etaleModuleDerivedExtensionByZeroDirectImagePlusIso_inv_app
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedExtensionByZeroDirectImagePlusIso Λ hΛ fb i b f' sq).inv.app K =
      (etaleModuleDerivedExtensionByZeroDirectImageMap.{u, 0} Λ fb i b f' sq).app K := by
  simp [etaleModuleDerivedExtensionByZeroDirectImagePlusIso,
    etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv, ObjectProperty.liftCompιIso]

/-- **The underived open immersion case of [Stacks, Tag 0F7B] is compatible with `j_! ⟶ j_*`**,
over a torsion ring: `i_! f'_* F ≅ f̄_* b_! F` followed by `f̄_*` of `b_! F ⟶ b_* F` and by
`f̄_* b_* ≅ (f' ≫ i)_*` is `i_! ⟶ i_*` at `f'_* F` followed by `i_* f'_* ≅ (f' ≫ i)_*`. It is the
cohomology in degree zero of `etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage`
on `F` placed in degree zero. -/
theorem etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq).hom.app F ≫
        (etaleModuleDirectImage.{u, 0} Λ fb).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b).app F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm).hom.app F =
      (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i).app
          ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl).hom.app F := by
  have hC := etaleModuleDerivedExtensionByZeroDirectImageMap_comp_toDirectImage Λ fb i b f' sq
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  rw [← etaleModuleDerivedExtensionByZeroDirectImagePlusIso_inv_app Λ fb i b f' sq hΛ] at hC
  exact degreeZero_comp_natTrans_of_derived (etaleModuleDirectImage.{u, 0} Λ f')
    (etaleModuleExtensionByZero.{u, 0} Λ i) (etaleModuleDirectImage.{u, 0} Λ i)
    (etaleModuleExtensionByZero.{u, 0} Λ b) (etaleModuleDirectImage.{u, 0} Λ b)
    (etaleModuleDirectImage.{u, 0} Λ fb) (etaleModuleDirectImage.{u, 0} Λ (f' ≫ i))
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b)
    (etaleModuleDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm)
    (etaleModuleDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl)
    (etaleModuleDerivedExtensionByZeroDirectImagePlusIso Λ hΛ fb i b f' sq) F hC

end OpenBaseChange

end Stacks.EtaleCohomology

end
