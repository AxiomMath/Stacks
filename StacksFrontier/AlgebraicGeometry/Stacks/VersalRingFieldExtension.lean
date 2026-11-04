module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
public import StacksFrontier.Deformation.FormalObject.VersalEquivalence
public import StacksFrontier.Deformation.VersalObject.ChangeOfFields

/-!
# Versal rings after a finite extension of the residue field (Stacks 0DQY)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over `S`,
let `l/k` be a finite extension and let `x_{l,0} : Spec l ⟶ 𝒳` be the induced point. Given a
versal ring `A` to `𝒳` at `x₀`, **Stacks 0DQY** produces a versal ring `A'` at `x_{l,0}` together
with an `S`-algebra map `A → A'` inducing `l/k` on residue fields and formally smooth for the
`𝔪_{A'}`-adic topology.

The proof is the source's. By **Stacks 0DQF** the versal formal object over `A` of
`𝓕_{𝒳,k,x₀}` gives a complete local algebra `A'` with residue field `l`, a formally smooth map
`A → A'` inducing `l/k`, and a versal formal object over `A'` of the change-of-fields category
`(𝓕_{𝒳,k,x₀})_{l/k}`. Since `𝒳` satisfies (RS) (**Stacks 07WQ**), the canonical functor
`(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` is an equivalence over `𝒞_{Λ,l}` (**Stacks 07WX**), and
versality is transported along it (`Deformation.isVersal_formalObjectMapOfCompEq`).

## Main results

* `AlgebraicGeometry.Stack.locallyOfFiniteType_and_quasiCompact_fieldExtension`: a finite
  extension of a field of finite type over `S` is of finite type over `S`, so the statement makes
  sense at `x_{l,0}`.
* `AlgebraicGeometry.Stack.exists_isVersalRingAt_fieldExtension`: **Stacks 0DQY**.

## Implementation notes

As in `AlgebraicGeometry.Stack.IsVersalRingAt`, the base `S` is replaced by an affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors; an `S`-algebra map between complete local rings
whose closed points map into `Spec Λ` is the same as a `Λ`-algebra map. The induced point
`x_{l,0}` is any object `xₗ` of `𝒳` over `Spec l ⟶ Spec Λ ⟶ S` together with a morphism
`η : xₗ ⟶ x₀` lying over `Spec l ⟶ Spec k`; in a category fibred in groupoids such an `η` is
cartesian, so `xₗ` is a restriction of `x₀` along `Spec l ⟶ Spec k`, and every such restriction
arises this way.

The equivalence of Stacks 07WX is stated over a chart `Spec Λ` over which `k` is a finite
`Λ`-module. For an arbitrary chart the statement is first moved, by **Stacks 0DQV**
(`AlgebraicGeometry.Stack.isVersalRingAt_iff_of_affineOpenPresentation`), to a principal open
`Spec Λ_r ⊆ Spec Λ` over which `k` is finite (**Stacks 00FY**, as in the proof of Stacks 0DQX),
and the resulting `Λ_r`-algebras are read back over `Λ`.

## References

* [Stacks Project, Tag 0DQF](https://stacks.math.columbia.edu/tag/0DQF)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQY](https://stacks.math.columbia.edu/tag/0DQY)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

/-- Composing `Spec` of two ring maps with a morphism out of `Spec` of the source is `Spec` of the
composite ring map followed by that morphism. -/
private theorem specMap_ofHom_comp_specMap_ofHom_comp {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] {S : Scheme.{u}} (f : A →+* B) (g : B →+* C) (i : Spec (.of A) ⟶ S) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) ≫ i =
      Spec.map (CommRingCat.ofHom (g.comp f)) ≫ i := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The ring of an affine open immersion into a locally Noetherian scheme is Noetherian. -/
private theorem isNoetherianRing_of_isOpenImmersion_spec {Λ : Type u} [CommRing Λ] {S : Scheme.{u}}
    [IsLocallyNoetherian S] (iΛ : Spec (.of Λ) ⟶ S)
    [_root_.AlgebraicGeometry.IsOpenImmersion iΛ] : IsNoetherianRing Λ := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  exact (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance

/-- **A finite extension of a field of finite type over `S` is of finite type over `S`.** If
`Spec k ⟶ Spec Λ ⟶ S` is locally of finite type and quasi-compact and `l/k` is finite, so is
`Spec l ⟶ Spec Λ ⟶ S`: it factors through the finite morphism `Spec l ⟶ Spec k`. -/
theorem locallyOfFiniteType_and_quasiCompact_fieldExtension
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite k l]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) := by
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
    rw [specMap_ofHom_comp_specMap_ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hfin : RingHom.Finite (algebraMap k l) := RingHom.finite_algebraMap.mpr inferInstance
  have hloc : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k l))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_finite hfin
  have hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k l))) := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k l))) :=
      (IsFinite.SpecMap_iff _).mpr hfin
    infer_instance
  obtain ⟨h1, h2⟩ := hfinite
  rw [hfac]
  exact ⟨locallyOfFiniteType_comp _ _, AlgebraicGeometry.quasiCompact_comp _ _⟩

/-- **Stacks 0DQY over a chart on which the residue field is finite.** This is the source's
proof: Stacks 0DQF at the versal formal object over `A`, followed by the equivalence of Stacks
07WX, available because `𝒳` satisfies (RS) by Stacks 07WQ. -/
theorem exists_isVersalRingAt_fieldExtension_of_finite
    (D : VersalSituation.{u, w})
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite Λ k] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    ∃ (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ l) (f : A →ₐ[Λ] A'),
      IsVersalRingAt D iΛ hiΛ xₗ hxₗ
          (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) A' ∧
        IsLocalHom f.toRingHom ∧
        (∀ a : A, A'.residueEquiv (residue A' (f a)) =
          algebraMap k l (A.residueEquiv (residue A a))) ∧
        RingHom.FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal A') := by
  have : IsNoetherianRing Λ := isNoetherianRing_of_isOpenImmersion_spec iΛ
  let T : Deformation.ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := l }
  obtain ⟨ξ, rfl, hξ⟩ := hA
  let q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let : Category C₀.carrier := C₀.category
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  let : Category Cₗ.carrier := Cₗ.category
  have hp₀ := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered
  have hpₗ := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered
  obtain ⟨A', f, hloc, hres, hsmooth, ξ', hξ'A, hξ'⟩ :=
    Deformation.exists_versal_formalObject_changeOfFields.{u, u, u, u} T C₀.projection hp₀ ξ hξ
  have hp : D.𝒳.val.val.p.IsFiberedInGroupoids := D.𝒳.val.property
  have hη : D.𝒳.val.val.p.IsCartesian (D.𝒳.val.val.p.map η) η :=
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
  let Fn := Deformation.Artin.Site.changeOfFieldFunctor T iΛ D.B D.hS D.𝒳.val.val.p
    x₀ xₗ hx₀ hxₗ η hp hη hηbase
  have : Fn.toFunctor.IsEquivalence :=
    Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence T iΛ D.B D.hS D.𝒳.val.val.p
      x₀ xₗ hx₀ hxₗ η hp hη hηbase hfinite
      (Deformation.Artin.satisfiesRS_of_isAlgebraicStack D.B D.S D.hS D.𝒳)
  obtain ⟨ξₗ, hξₗ, hξₗv⟩ := Deformation.exists_isVersal_base_eq_of_comp_eq Fn.toFunctor
    Fn.projection_comm
    (Deformation.changeOfFieldsProjection_isCofiberedInGroupoids T C₀.projection hp₀) hpₗ ξ' hξ'
  exact ⟨A', f, ⟨ξₗ, hξₗ.trans hξ'A, hξₗv⟩, hloc, hres, hsmooth⟩

/-- A complete local `R`-algebra with residue field `l`, read as a `Λ`-algebra through a ring map
`Λ → R` compatible with `l`. The carrier, the ring and the residue-field identification are those
of the input. -/
abbrev completeLocalAlgRestrictScalars {Λ R l : Type u} [CommRing Λ] [CommRing R] [Field l]
    [Algebra Λ R] [Algebra R l] [Algebra Λ l] [IsScalarTower Λ R l]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} R l) :
    Deformation.CompleteLocalAlgCat.{u, u, u} Λ l :=
  letI : Algebra Λ A := ((algebraMap R A).comp (algebraMap Λ R)).toAlgebra
  letI : IsScalarTower Λ R A := IsScalarTower.of_algebraMap_eq' rfl
  { carrier := A
    commRing := inferInstance
    algebra := inferInstance
    completeLocal := A.completeLocal
    residueEquiv := A.residueEquiv.restrictScalars Λ }

/-- **Stacks 0DQY.** In Situation 0DQU, let `x₀` be an object of `𝒳` over `Spec k` for a field
`k` of finite type over `S`, presented over an affine open `Spec Λ ⊆ S`, let `l/k` be a finite
extension of fields, and let `x_{l,0}` be the induced point: an object `xₗ` over
`Spec l ⟶ Spec Λ ⟶ S` with a morphism `η : xₗ ⟶ x₀` over `Spec l ⟶ Spec k`. Given a versal ring
`A` to `𝒳` at `x₀` there are a versal ring `A'` to `𝒳` at `x_{l,0}` and an `S`-algebra map
`f : A → A'` which is local, induces the given extension `l/k` on residue fields, and is formally
smooth for the `𝔪_{A'}`-adic topology. -/
@[stacks 0DQY]
theorem exists_isVersalRingAt_fieldExtension
    (D : VersalSituation.{u, w})
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A) :
    ∃ (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ l) (f : A →ₐ[Λ] A'),
      IsVersalRingAt D iΛ hiΛ xₗ hxₗ
          (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) A' ∧
        IsLocalHom f.toRingHom ∧
        (∀ a : A, A'.residueEquiv (residue A' (f a)) =
          algebraMap k l (A.residueEquiv (residue A a))) ∧
        RingHom.FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal A') := by
  have : IsNoetherianRing Λ := isNoetherianRing_of_isOpenImmersion_spec iΛ
  have : _root_.AlgebraicGeometry.IsOpenImmersion iΛ := hiΛ
  obtain ⟨r₀, hr₀, ψ₀, hψ₀, hψ₀finite⟩ := exists_finite_localized_affineChart iΛ hfinite.1
  let R := Localization.Away r₀
  have : IsLocalization.Away r₀ R := Localization.isLocalization
  let : Algebra R k := ψ₀.toAlgebra
  let : Algebra R l := ((algebraMap k l).comp ψ₀).toAlgebra
  have : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite R k := RingHom.finite_algebraMap.mp hψ₀finite
  have hΛRl : (algebraMap R l).comp (algebraMap Λ R) = algebraMap Λ l := by
    rw [IsScalarTower.algebraMap_eq Λ k l]
    show ((algebraMap k l).comp ψ₀).comp (algebraMap Λ R) = _
    rw [RingHom.comp_assoc, hψ₀]
  have : IsScalarTower Λ R l := IsScalarTower.of_algebraMap_eq' hΛRl.symm
  let iR : Spec (.of R) ⟶ D.S := Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  have hiR : _root_.AlgebraicGeometry.IsOpenImmersion iR := by
    dsimp [iR]
    infer_instance
  have hpointR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    hx₀.trans (congrArg Over.mk (awayChart_point_map_eq iΛ r₀ ψ₀ hψ₀).symm)
  have hlR : Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
    dsimp only [iR]
    rw [specMap_ofHom_comp_specMap_ofHom_comp, hΛRl]
  have hxₗR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR) :=
    hxₗ.trans (congrArg Over.mk hlR.symm)
  have hfiniteR : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    finiteTypeAfterAwayLocalization iΛ r₀ ψ₀ hψ₀finite
  have hAunit := coefficientElement_isUnit_in_completeLocal A r₀ hr₀
  have hkunit : IsUnit (algebraMap Λ k r₀) := isUnit_iff_ne_zero.mpr hr₀
  have hψ₀lift : ψ₀ = IsLocalization.Away.lift r₀ hkunit :=
    IsLocalization.ringHom_ext (Submonoid.powers r₀) <| RingHom.ext fun x =>
      (RingHom.congr_fun hψ₀ x).trans (IsLocalization.Away.lift_eq r₀ hkunit x).symm
  let AR := localizeCompleteLocalAlgCat r₀ A hAunit hkunit
    (fun x => DFunLike.congr_fun hψ₀lift x)
  have hAlg (x : Λ) : algebraMap Λ A x = algebraMap R AR (algebraMap Λ R x) :=
    (IsLocalization.Away.lift_eq r₀ hAunit x).symm
  let eA : (A : Type u) ≃+* (AR : Type u) := RingEquiv.refl _
  have heSA : Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap R AR)) ≫ iR := by
    dsimp only [iR]
    rw [specMap_ofHom_comp_specMap_ofHom_comp, specMap_ofHom_comp_specMap_ofHom_comp]
    congr 3
    ext x
    exact hAlg x
  have hAR : IsVersalRingAt D iR hiR x₀ hpointR hfiniteR AR :=
    (isVersalRingAt_iff_of_affineOpenPresentation D iΛ hiΛ iR hiR x₀ hx₀ hpointR hfinite
      hfiniteR A AR eA heSA (fun _ => rfl)).mp hA
  obtain ⟨A'R, fR, hvR, hloc, hres, hsm⟩ :=
    exists_isVersalRingAt_fieldExtension_of_finite D iR hiR x₀ hpointR hfiniteR xₗ hxₗR η
      hηbase AR hAR
  let A' := completeLocalAlgRestrictScalars (Λ := Λ) A'R
  let eA' : (A'R : Type u) ≃+* (A' : Type u) := RingEquiv.refl _
  have heSA' : Spec.map (CommRingCat.ofHom eA'.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A'R)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ := by
    dsimp only [iR]
    rw [specMap_ofHom_comp_specMap_ofHom_comp, specMap_ofHom_comp_specMap_ofHom_comp]
    rfl
  have hA' : IsVersalRingAt D iΛ hiΛ xₗ hxₗ
      (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) A' :=
    (isVersalRingAt_iff_of_affineOpenPresentation D iR hiR iΛ hiΛ xₗ hxₗR hxₗ
      (locallyOfFiniteType_and_quasiCompact_fieldExtension iR hfiniteR)
      (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) A'R A' eA' heSA'
      (fun _ => rfl)).mp hvR
  let f : A →ₐ[Λ] A' :=
    { toRingHom := fR.toRingHom
      commutes' := fun x => by
        show fR (algebraMap Λ A x) = algebraMap R A'R (algebraMap Λ R x)
        rw [hAlg x]
        exact fR.commutes _ }
  exact ⟨A', f, hA', hloc, hres, hsm⟩

end AlgebraicGeometry.Stack

end
