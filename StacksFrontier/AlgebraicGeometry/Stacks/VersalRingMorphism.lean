module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Formal.VersalObject.PowerSeriesComparisonHom

/-!
# The morphism `Spec A ⟶ 𝒳` of a versal ring, and the comparison of versal rings (Stacks 0DR1)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over `S`
and let `A` be a versal ring to `𝒳` at `x₀` (**Stacks 0DQV**), with its versal formal object `ξ`.
**Stacks 0DR1** observes that `ξ` comes from a morphism `Spec A ⟶ 𝒳` over `S` (by Artin's Axioms,
**Stacks 07X8**), and that the results of the section upgrade to statements compatible with these
morphisms.

The morphism of the remark is recorded as a *realization*
(`Deformation.Artin.FormalObject.Realization`): an object `y` of `𝒳` over `Spec A ⟶ S`, the
1-morphism `Spec A ⟶ 𝒳` it names, with arrows from the levels of `ξ` lying over the inclusions of
the infinitesimal thickenings of the closed point, which exhibit `ξ` as the system of restrictions
of `y`.

This file proves part (1) of the remark: in **Stacks 0DQX** the isomorphism
`A ≅ A'[[t₁, …, t_r]]` or `A' ≅ A[[t₁, …, t_r]]` may be chosen compatible with the morphisms
`Spec A ⟶ 𝒳` and `Spec A' ⟶ 𝒳`, i.e. so that there is a morphism of `𝒳` from the realizing object
over `Spec A` to the one over `Spec A'` lying over `Spec A ≅ Spec A'[[t]] ⟶ Spec A'`. As the remark
notes, this is a 2-commutative triangle: a morphism of a category fibred in groupoids lying over a
morphism of schemes is a 2-isomorphism between the 1-morphism of its source and the composite.

## Main results

* `AlgebraicGeometry.Stack.exists_powerSeries_comparison_realization_of_full`: **Stacks 0DR1**,
  part (1), from fullness of the approximation functor (the fullness half of Stacks 07X8).

## Implementation notes

The comparison of the two versal formal objects is made over a principal open `Spec Λ_f` of the
first chart over which `k` is a finite module, where the minimal versal theory applies
(`Deformation.exists_powerSeries_comparison_hom`); the formal objects are moved there by
`AlgebraicGeometry.Stack.exists_isVersal_ofPredeformation_eq_of_affineOpenPresentation`, which
keeps their formal objects over the site, hence their realizations. The isomorphism obtained there
is read back on the original rings through `Deformation.Artin.FormalBase.ringEquivOfEq`.

## References

* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQV](https://stacks.math.columbia.edu/tag/0DQV)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

section Comparison

variable (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})

/-- The spectrum of a composite of three ring maps is the composite of their spectra. -/
private theorem specMap_comp₃ {A₁ A₂ A₃ A₄ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
    [CommRing A₄] (f : A₃ →+* A₄) (g : A₂ →+* A₃) (h : A₁ →+* A₂) :
    Spec.map (CommRingCat.ofHom (f.comp (g.comp h))) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom h) := by
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]

/-- The constants of a power series ring followed by the structure map of the coefficients is the
structure map of the power series ring. -/
private theorem specMap_C_algebraMap {Λ₀ A₀ : Type u} [CommRing Λ₀] [CommRing A₀] [Algebra Λ₀ A₀]
    (σ : Type) {T : Scheme.{u}} (t : Spec (.of Λ₀) ⟶ T) :
    Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := σ) (R := A₀))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ₀ A₀)) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap Λ₀ (MvPowerSeries σ A₀))) ≫ t := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun a =>
    (MvPowerSeries.algebraMap_apply (σ := σ) (R := Λ₀) (A := A₀) (r := a)).symm

/-- The structure-morphism compatibility of a ring isomorphism `e` with the composite
`e⁻¹ ∘ c`. -/
private theorem specMap_ringEquiv_comp_symm {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂]
    [CommRing A₃] {T : Scheme.{u}} (e : A₁ ≃+* A₂) (c : A₃ →+* A₂)
    (t : Spec (.of A₃) ⟶ T) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp c)) ≫ t =
      Spec.map (CommRingCat.ofHom c) ≫ t := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext a
  simp

/-- Transporting `f : A' → A` along ring isomorphisms `A ≃ B`, `A' ≃ B'` gives the constants of
the power series isomorphism `B ≃ B'[[σ]]` induced by an isomorphism `A ≃ A'[[σ]]` that sends `f`
to the constants. -/
private theorem ringEquiv_comp_eq_symm_comp_C {R A A' B B' : Type*} [CommRing R] [CommRing A]
    [CommRing A'] [CommRing B] [CommRing B'] [Algebra R A] [Algebra R A'] {σ : Type*}
    (eA : A ≃+* B) (eA' : A' ≃+* B') (E : A ≃ₐ[R] MvPowerSeries σ A') (f : A' →+* A)
    (hE : ∀ b, E (f b) = MvPowerSeries.C b) :
    eA.toRingHom.comp (f.comp eA'.symm.toRingHom) =
      (eA.symm.trans (E.toRingEquiv.trans
        (Deformation.mvPowerSeriesRingEquivOfRingEquiv σ eA'))).symm.toRingHom.comp
        MvPowerSeries.C := by
  ext b
  change eA (f (eA'.symm b)) = eA (E.symm
    ((Deformation.mvPowerSeriesRingEquivOfRingEquiv σ eA').symm (MvPowerSeries.C b)))
  congr 1
  rw [show (Deformation.mvPowerSeriesRingEquivOfRingEquiv σ eA').symm (MvPowerSeries.C b) =
      MvPowerSeries.C (eA'.symm b) by
    rw [RingEquiv.symm_apply_eq, Deformation.mvPowerSeriesRingEquivOfRingEquiv_C,
      RingEquiv.apply_symm_apply]]
  exact ((E.symm_apply_eq).mpr (hE _).symm).symm

/-- A morphism of formal objects over the common chart `Spec R ⟶ S` comes from a morphism
`y ⟶ y'` of the realizing objects, whose image in the site is the map of complete local bases
read back on the original rings. -/
private theorem exists_hom_toScheme_map_eq
    {Λ Λ' R k : Type u} [CommRing Λ] [CommRing Λ'] [CommRing R] [Field k]
    [Algebra Λ k] [Algebra Λ' k] [Algebra R k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (iΛ' : Spec (.of Λ') ⟶ D.S) (iR : Spec (.of R) ⟶ D.S)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hxR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfiniteR : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (η η' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iR
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hxR).projection)
    (hEq : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
        hfiniteR η =
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ)
    (hEq' : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
        hfiniteR η' =
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀ hx₀'
        hfinite' ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ξ').Realization hA' y' hy')
    (hfull : (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).Full)
    (φ : η' ⟶ η) :
    ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
        (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
      Spec.map (CommRingCat.ofHom
        ((Deformation.Artin.FormalBase.ringEquivOfEq
            (congrArg Deformation.Artin.FormalObject.base hEq) :
            (η.base : Type u) ≃+* (ξ.base : Type u)).toRingHom.comp
          (φ.base.hom.toRingHom.comp (Deformation.Artin.FormalBase.ringEquivOfEq
            (congrArg Deformation.Artin.FormalObject.base hEq') :
            (η'.base : Type u) ≃+* (ξ'.base : Type u)).symm.toRingHom))) := by
  set ζ := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
    hfinite ξ
  set ζ' := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
    hx₀' hfinite' ξ'
  set θ := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
    hfiniteR η
  set θ' := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
    hfiniteR η'
  have hB : θ.base = ζ.base := congrArg Deformation.Artin.FormalObject.base hEq
  have hB' : θ'.base = ζ'.base := congrArg Deformation.Artin.FormalObject.base hEq'
  have hAθ : D.B.Contains (Spec (.of θ.base.R)) := by rwa [hB]
  have hAθ' : D.B.Contains (Spec (.of θ'.base.R)) := by rwa [hB']
  have hBO := Deformation.Artin.baseOver_congr D.B D.S D.hS hB.symm hA hAθ
  have hBO' := Deformation.Artin.baseOver_congr D.B D.S D.hS hB'.symm hA' hAθ'
  have hyθ := hy.trans hBO
  have hyθ' := hy'.trans hBO'
  obtain ⟨m, -, hm⟩ := Deformation.Artin.FormalObject.Realization.exists_hom
    D.𝒳.val.property hfull
    (Deformation.Artin.FormalObject.Realization.ofEq hEq.symm hyθ Ry)
    (Deformation.Artin.FormalObject.Realization.ofEq hEq'.symm hyθ' Ry')
    (Deformation.Artin.FormalObject.ofPredeformationMap D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
      hfiniteR φ)
  refine ⟨m, ?_⟩
  have hmb := hm _ (Deformation.Artin.FormalObject.ofPredeformationMap_isBaseMap D.B D.S D.hS iR
    D.𝒳.val.val.p x₀ hxR hfiniteR φ)
  let eA : (η.base : Type u) ≃+* (ξ.base : Type u) := Deformation.Artin.FormalBase.ringEquivOfEq hB
  let eA' : (η'.base : Type u) ≃+* (ξ'.base : Type u) :=
    Deformation.Artin.FormalBase.ringEquivOfEq hB'
  have hsplit : eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy' =
      eqToHom hBO ≫ (eqToHom hyθ.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hyθ') ≫
        eqToHom hBO'.symm := by
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  have hEA : (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hBO) =
      Spec.map (CommRingCat.ofHom eA.toRingHom) :=
    (eqToHom_map _ _).trans (Deformation.Artin.FormalBase.specMap_ringEquivOfEq hB).symm
  have hEA' : (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hBO'.symm) =
      Spec.map (CommRingCat.ofHom eA'.symm.toRingHom) :=
    (eqToHom_map _ _).trans (Deformation.Artin.FormalBase.specMap_ringEquivOfEq_symm hB').symm
  rw [hsplit]
  generalize (eqToHom hyθ.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hyθ') = X at hmb ⊢
  refine ((BigFppfOver.toScheme D.B D.S D.hS).map_comp _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((BigFppfOver.toScheme D.B D.S D.hS).map_comp _ _)).trans ?_
  refine (congrArg (· ≫ _) hEA).trans ?_
  refine (congrArg (fun g => _ ≫ g ≫ _) hmb).trans ?_
  exact (congrArg (fun g => _ ≫ _ ≫ g) hEA').trans (specMap_comp₃ _ _ _).symm

/-- The one-sided core of `exists_powerSeries_comparison_realization_of_full`: the formal objects
have been moved to a common chart `Spec R ⟶ S`, where a morphism `η' ⟶ η` over
`η'.base ⟶ η'.base[[t]] ≅ η.base` is given. -/
private theorem comparison_core
    {Λ Λ' R k : Type u} [CommRing Λ] [CommRing Λ'] [CommRing R] [Field k]
    [Algebra Λ k] [Algebra Λ' k] [Algebra R k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (iΛ' : Spec (.of Λ') ⟶ D.S) (iR : Spec (.of R) ⟶ D.S)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hxR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfiniteR : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (η η' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iR
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hxR).projection)
    (hEq : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
        hfiniteR η =
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ)
    (hEq' : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iR D.𝒳.val.val.p x₀ hxR
        hfiniteR η' =
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀ hx₀'
        hfinite' ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ξ').Realization hA' y' hy')
    (hfull : (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).Full)
    (r : ℕ) (E : η.base ≃ₐ[R] MvPowerSeries (Fin r) η'.base) (φ : η' ⟶ η)
    (hE : ∀ b, E (φ.base.hom b) = MvPowerSeries.C b) :
    ∃ e : (ξ.base : Type u) ≃+* MvPowerSeries (Fin r) ξ'.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' (MvPowerSeries (Fin r) ξ'.base))) ≫ iΛ' ∧
      ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C)) := by
  obtain ⟨m, hm⟩ := exists_hom_toScheme_map_eq D iΛ iΛ' iR x₀ hx₀ hx₀' hxR hfinite hfinite'
    hfiniteR ξ ξ' η η' hEq hEq' Ry Ry' hfull φ
  let eA : (η.base : Type u) ≃+* (ξ.base : Type u) :=
    Deformation.Artin.FormalBase.ringEquivOfEq (congrArg Deformation.Artin.FormalObject.base hEq)
  let eA' : (η'.base : Type u) ≃+* (ξ'.base : Type u) :=
    Deformation.Artin.FormalBase.ringEquivOfEq (congrArg Deformation.Artin.FormalObject.base hEq')
  let e : (ξ.base : Type u) ≃+* MvPowerSeries (Fin r) ξ'.base :=
    eA.symm.trans (E.toRingEquiv.trans (Deformation.mvPowerSeriesRingEquivOfRingEquiv (Fin r) eA'))
  have hmap : (BigFppfOver.toScheme D.B D.S D.hS).map
      (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
      Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C)) :=
    hm.trans (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (ringEquiv_comp_eq_symm_comp_C eA eA' E φ.base.hom.toRingHom hE))
  refine ⟨e, ?_, m, hmap⟩
  generalize (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') = X at hmap ⊢
  clear_value e
  have hw := congrArg D.B.inclusion.map (Over.w X)
  simp only [Functor.map_comp] at hw
  change (BigFppfOver.toScheme D.B D.S D.hS).map X ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ'.base)) ≫ iΛ') =
    Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ at hw
  rw [hmap] at hw
  refine (congrArg (fun g => Spec.map (CommRingCat.ofHom e.toRingHom) ≫ g) hw.symm).trans ?_
  refine (specMap_ringEquiv_comp_symm e MvPowerSeries.C _).trans ?_
  exact specMap_C_algebraMap (Fin r) iΛ'

/-- **Stacks 0DR1, part (1), from the fullness half of Stacks 07X8.** In the versal situation, let
`x₀` be a point of `𝒳` over `Spec k` for a field `k` of finite type over `S`, and let `A`, `A'` be
versal rings to `𝒳` at `x₀` (presented over affine opens `Spec Λ`, `Spec Λ'` of `S`), with versal
formal objects `ξ`, `ξ'` coming from morphisms `Spec A ⟶ 𝒳` and `Spec A' ⟶ 𝒳` over `S`: objects
`y`, `y'` of `𝒳` over `Spec A`, `Spec A'` realizing `ξ`, `ξ'`. If the approximation functor of `𝒳`
is full, then the isomorphism of **Stacks 0DQX** may be chosen compatible with these morphisms:
either there are `r` and an isomorphism `e : A ≅ A'[[t₁, …, t_r]]` over `S` together with a
morphism `y ⟶ y'` of `𝒳` lying over `Spec A ≅ Spec A'[[t₁, …, t_r]] ⟶ Spec A'`, or the same with
`A` and `A'` exchanged. The morphism `y ⟶ y'` is the 2-arrow making the triangle of 1-morphisms
`Spec A ⟶ Spec A' ⟶ 𝒳` 2-commute. -/
theorem exists_powerSeries_comparison_realization_of_full
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ξ').Realization hA' y' hy')
    (hfull : (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).Full) :
    (∃ r : ℕ, ∃ e : (ξ.base : Type u) ≃+* MvPowerSeries (Fin r) ξ'.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' (MvPowerSeries (Fin r) ξ'.base))) ≫ iΛ' ∧
      ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) ∨
    (∃ r : ℕ, ∃ e : (ξ'.base : Type u) ≃+* MvPowerSeries (Fin r) ξ.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ'.base)) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPowerSeries (Fin r) ξ.base))) ≫ iΛ ∧
      ∃ m : y' ⟶ y, (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  have : IsOpenImmersion iΛ := hiΛ
  obtain ⟨r₀, -, ψ₀, hψ₀, hψ₀finite⟩ := exists_finite_localized_affineChart iΛ hfinite.1
  let R := Localization.Away r₀
  let : IsLocalization.Away r₀ R := Localization.isLocalization
  let : Algebra R k := ψ₀.toAlgebra
  let iR : Spec (.of R) ⟶ D.S := Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  have hiR : IsOpenImmersion iR := by
    dsimp [iR]
    infer_instance
  have hpointR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    hx₀.trans (congrArg Over.mk (awayChart_point_map_eq iΛ r₀ ψ₀ hψ₀).symm)
  have hfiniteR : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    finiteTypeAfterAwayLocalization iΛ r₀ ψ₀ hψ₀finite
  have : Module.Finite R k := RingHom.finite_algebraMap.mp hψ₀finite
  obtain ⟨η, hη, hEq⟩ := exists_isVersal_ofPredeformation_eq_of_affineOpenPresentation D iΛ hiΛ
    iR hiR x₀ hx₀ hpointR hfinite hfiniteR ξ hξ
  obtain ⟨η', hη', hEq'⟩ := exists_isVersal_ofPredeformation_eq_of_affineOpenPresentation D iΛ'
    hiΛ' iR hiR x₀ hx₀' hpointR hfinite' hfiniteR ξ' hξ'
  rcases Deformation.exists_powerSeries_comparison_hom
      (Deformation.Artin.predeformationCategory_isPredeformationCategory D.B D.hS iR
        D.𝒳.val.val.p x₀ hpointR D.𝒳.val.property) η η' hη hη' with
    ⟨r, E, φ, hE⟩ | ⟨r, E, φ, hE⟩
  · exact Or.inl ⟨r, comparison_core D iΛ iΛ' iR x₀ hx₀ hx₀' hpointR hfinite hfinite'
      hfiniteR ξ ξ' η η' hEq hEq' Ry Ry' hfull r E φ hE⟩
  · exact Or.inr ⟨r, comparison_core D iΛ' iΛ iR x₀ hx₀' hx₀ hpointR hfinite' hfinite
      hfiniteR ξ' ξ η' η hEq' hEq Ry' Ry hfull r E φ hE⟩

/-- **Stacks 0DR1, part (1).** In the versal situation, let `x₀` be a point of `𝒳` over `Spec k`
for a field `k` of finite type over `S`, and let `A`, `A'` be versal rings to `𝒳` at `x₀`
(presented over affine opens `Spec Λ`, `Spec Λ'` of `S`), with versal formal objects `ξ`, `ξ'`
coming from morphisms `Spec A ⟶ 𝒳` and `Spec A' ⟶ 𝒳` over `S`: objects `y`, `y'` of `𝒳` over
`Spec A`, `Spec A'` realizing `ξ`, `ξ'`. Then the isomorphism of **Stacks 0DQX** may be chosen
compatible with these morphisms: either there are `r` and an isomorphism
`e : A ≅ A'[[t₁, …, t_r]]` over `S` together with a morphism `y ⟶ y'` of `𝒳` lying over
`Spec A ≅ Spec A'[[t₁, …, t_r]] ⟶ Spec A'`, or the same with `A` and `A'` exchanged. The
morphism `y ⟶ y'` is the 2-arrow making the triangle `Spec A ⟶ Spec A' ⟶ 𝒳` 2-commute, which
is how the source's "compatible" is to be read (the remark notes that the diagrams commute only
up to a noncanonical 2-arrow).

Fullness of the approximation functor, the input from **Stacks 07X8**, is
`Deformation.Artin.full_approximationFunctor_algebraicStacks`. -/
@[stacks 0DR1 "part (1): in Lemma 0DQX the isomorphism A ≅ A'[[t₁,…,t_r]] or \
A' ≅ A[[t₁,…,t_r]] may be chosen compatible with the morphisms Spec A → 𝒳, Spec A' → 𝒳"]
theorem exists_powerSeries_comparison_realization
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered ξ')
    {hA : D.B.Contains (Spec (.of ξ.base))} {hA' : D.B.Contains (Spec (.of ξ'.base))}
    {y y' : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ξ').Realization hA' y' hy') :
    (∃ r : ℕ, ∃ e : (ξ.base : Type u) ≃+* MvPowerSeries (Fin r) ξ'.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' (MvPowerSeries (Fin r) ξ'.base))) ≫ iΛ' ∧
      ∃ m : y ⟶ y', (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy') =
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) ∨
    (∃ r : ℕ, ∃ e : (ξ'.base : Type u) ≃+* MvPowerSeries (Fin r) ξ.base,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ'.base)) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPowerSeries (Fin r) ξ.base))) ≫ iΛ ∧
      ∃ m : y' ⟶ y, (BigFppfOver.toScheme D.B D.S D.hS).map
          (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
        Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) :=
  exists_powerSeries_comparison_realization_of_full D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite
    hfinite' ξ hξ ξ' hξ' Ry Ry'
    (Deformation.Artin.full_approximationFunctor_algebraicStacks D.𝒳)

end Comparison

end AlgebraicGeometry.Stack

end
