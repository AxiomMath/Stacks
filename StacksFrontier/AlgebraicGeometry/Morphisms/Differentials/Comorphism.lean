module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials

/-!
# Relative derivations tested on sections pulled back along a morphism of schemes

A derivation of the structure sheaf of `X` relative to `f⁻¹ 𝒪_S` is required to annihilate the
image of `f⁻¹ 𝒪_S ⟶ 𝒪_X`, whose sections over an open of `X` need not come from a single
section of `𝒪_S`. This file records that it suffices to annihilate the sections that do: a
derivation annihilating `f^♯ b` for every local section `b` of `𝒪_S` is a derivation relative
to `f⁻¹ 𝒪_S`, and conversely every derivation relative to `f⁻¹ 𝒪_S` annihilates those
sections.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.constIntPresheaf` is the constant presheaf of commutative
  rings `ℤ`, and `AlgebraicGeometry.SheafOfModules.constIntMap` its unique morphism to a
  presheaf of commutative rings.
* `AlgebraicGeometry.SheafOfModules.ofComorphism` upgrades a relative derivation along an
  arbitrary morphism of presheaves of commutative rings to a relative derivation along the
  structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.SheafOfModules.constIntMap_app_eq_zero`: an additive map annihilating `1`
  annihilates every section of the constant presheaf `ℤ`.
* `AlgebraicGeometry.SheafOfModules.d_comorphism_eq_zero`: a relative derivation along
  `f⁻¹ 𝒪_S ⟶ 𝒪_X` annihilates every section pulled back along the comorphism of `f`.

## Implementation notes

`ofComorphism` takes a relative derivation along an unspecified morphism of presheaves of
commutative rings rather than bare data, because the fields of
`PresheafOfModules.Derivation` carry the scalar action of the structure sheaf and are easiest
to supply in the form the structure itself expects. `constIntMap` is the morphism to use when
there is no other candidate: a derivation relative to the constant presheaf `ℤ` is a
derivation with no vanishing condition beyond the Leibniz rule.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The constant presheaf of commutative rings `ℤ` on a topological space. -/
noncomputable def constIntPresheaf (T : TopCat.{u}) : (Opens T)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The unique morphism from the constant presheaf of commutative rings `ℤ` to a presheaf of
commutative rings. -/
noncomputable def constIntMap {T : TopCat.{u}} (P : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) :
    constIntPresheaf T ⟶ P where
  app W := CommRingCat.ofHom
    ((Int.castRingHom (P.obj W)).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
  naturality W W' i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro n
    change ((n.down : ℤ) : P.obj W') = (P.map i).hom ((n.down : ℤ) : P.obj W)
    exact (map_intCast (P.map i).hom _).symm

/-- An additive map annihilating `1` annihilates the image of every section of the constant
presheaf of commutative rings `ℤ`. -/
theorem constIntMap_app_eq_zero {T : TopCat.{u}} {P : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}}
    {W : (Opens T)ᵒᵖ} {A : Type*} [AddCommGroup A] (d : (P.obj W) →+ A)
    (hone : d 1 = 0) (a : (constIntPresheaf T).obj W) :
    d ((constIntMap P).app W a) = 0 := by
  show d (((a.down : ℤ) : P.obj W)) = 0
  rw [show ((a.down : ℤ) : P.obj W) = a.down • (1 : P.obj W) by simp [zsmul_eq_mul],
    AddMonoidHom.map_zsmul, hone, smul_zero]

/-- A relative derivation of `𝒪_X` which annihilates every section pulled back along the
comorphism of `f : X ⟶ S` is a relative derivation along the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`.
-/
noncomputable def ofComorphism {X S : Scheme.{u}} (f : X ⟶ S) {M : X.Modules}
    {R : (Opens ↥X)ᵒᵖ ⥤ CommRingCat.{u}} {ψ : R ⟶ X.presheaf} (D : M.val.Derivation' ψ)
    (hc : ∀ (W : S.Opens) (b : Γ(S, W)), D.d ((f.app W).hom b) = 0) :
    SheafDerivation (inverseImageStructureMap f) M where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {W} a :=
    Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero
      f.toLRSHom.toShHom M.isSheaf D (fun W b => hc W b) W a

/-- A relative derivation of `𝒪_X` along the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X` annihilates every
section pulled back along the comorphism of `f`. -/
theorem d_comorphism_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) {M : X.Modules}
    (D : SheafDerivation (inverseImageStructureMap f) M) (W : S.Opens) (b : Γ(S, W)) :
    D.d ((f.app W).hom b) = 0 := by
  have e : (⟨f.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map (inverseImageStructureMap f) :=
    (Equiv.apply_symm_apply
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
        S.sheaf X.sheaf) ⟨f.c⟩).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  exact (congrArg D.d (congrArg (fun t : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf =>
      (t.hom.app (op W)).hom b) e)).trans (PresheafOfModules.Derivation'.d_app D _)

end AlgebraicGeometry.SheafOfModules
