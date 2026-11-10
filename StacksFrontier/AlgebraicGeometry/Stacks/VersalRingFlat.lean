module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingMorphism
public import StacksFrontier.Algebra.MittagLeffler.MvPowerSeries
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of the morphism `Spec A ⟶ 𝒳` of a versal ring (Stacks 0DR2)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` a field of finite type
over `S`, and let `A` be a versal ring to `𝒳` at `x₀` (**Stacks 0DQV**). By **Stacks 0DR1** the
versal formal object over `A` comes from a morphism `Spec A ⟶ 𝒳`, recorded in this library as a
*realization* (`Deformation.Artin.FormalObject.Realization`): an object `y` of `𝒳` over `Spec A`
whose restrictions to the infinitesimal thickenings of the closed point are the levels of the
versal formal object. **Stacks 0DR2** says that this morphism is flat
(`AlgebraicGeometry.Stack.flatObject`, **Stacks 0H14**).

The proof is the source's, in three steps.

* **Step I.** If `A` and `A'` are versal rings at `x₀`, the lemma holds for `A` if and only if it
  holds for `A'`: by **Stacks 0DQX** and part (1) of **Stacks 0DR1**
  (`AlgebraicGeometry.Stack.exists_powerSeries_comparison_realization`), after possibly swapping
  them `A ≅ A'[[t₁, …, t_r]]` compatibly with the two morphisms to `𝒳`, and `A' → A'[[t]]` is
  faithfully flat, so flatness descends (**Stacks 06Q0**) and ascends (**Stacks 06PX**) along it.

## Main definitions

* `AlgebraicGeometry.Stack.RealizationsFlatAt`: the conclusion of Stacks 0DR2 at a point, for all
  presentations of the point, all versal formal objects and all their realizations.

## Main results

* `AlgebraicGeometry.Stack.realizationsFlatAt_of_flatObject`: Step I.

## References

* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DQX](https://stacks.math.columbia.edu/tag/0DQX)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Faithful flatness of a power series extension -/

/-- The morphism of spectra induced by a flat local homomorphism of local rings is flat and
surjective, since the homomorphism is faithfully flat. -/
private theorem flat_and_surjective_specMap_of_flat_of_isLocalHom {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hφ
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hφ, (surjective_iff _).mpr
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstance : Module.FaithfullyFlat A B))).2⟩

/-- The morphism of spectra induced by `A' → A'[[t₁, …, t_r]] ≅ A` is flat and surjective, for a
Noetherian local ring `A'`: power series over a Noetherian ring are flat, and a flat local
homomorphism of local rings is faithfully flat. -/
theorem flat_and_surjective_specMap_symm_comp_C {A A' : Type u} [CommRing A] [CommRing A']
    [IsNoetherianRing A'] [IsLocalRing A'] (r : ℕ) (e : A ≃+* MvPowerSeries (Fin r) A') :
    Flat (Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp MvPowerSeries.C))) := by
  have : IsLocalRing A := e.symm.isLocalRing
  let φ : A' →+* A := e.symm.toRingHom.comp MvPowerSeries.C
  have hC : (MvPowerSeries.C (σ := Fin r) (R := A')).Flat :=
    RingHom.flat_algebraMap_iff.mpr (Module.flat_and_mittagLeffler_mvPowerSeries A' r).1
  have hφ : φ.Flat := RingHom.Flat.comp hC (RingHom.Flat.of_bijective e.symm.bijective)
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have h₁ : IsUnit (MvPowerSeries.C (σ := Fin r) a) := by
      simpa [φ] using ha.map e.toRingHom
    simpa using (MvPowerSeries.isUnit_iff_constantCoeff.mp h₁)
  exact flat_and_surjective_specMap_of_flat_of_isLocalHom φ hφ

/-- The morphism of spectra induced by a local homomorphism of Noetherian complete local rings
which is formally smooth for the adic topology of the target is flat and surjective: it is flat
by **Stacks 07PM**, and a flat local homomorphism of local rings is faithfully flat. -/
@[sga "1 III 1.3" "special case"]
theorem flat_and_surjective_specMap_of_formallySmoothNAdic {A A' : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A'] [IsAdicComplete (maximalIdeal A') A']
    (f : A →+* A') [IsLocalHom f] (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal A')) :
    Flat (Spec.map (CommRingCat.ofHom f)) ∧ Surjective (Spec.map (CommRingCat.ofHom f)) := by
  let : Algebra A A' := f.toAlgebra
  have htfae := isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae f
  have h42 : f.FormallySmoothNAdic (maximalIdeal A') →
      Module.Flat A A' ∧ Algebra.IsGeometricallyRegular (ResidueField A)
        (TensorProduct A (ResidueField A) A') := (htfae.out 4 2).mp
  exact flat_and_surjective_specMap_of_flat_of_isLocalHom f (h42 hf).1

variable (D : VersalSituation.{u, w})

/-- A morphism of the site which, conjugated by transports, is flat and surjective on schemes is
flat and surjective. -/
lemma flat_and_surjective_of_toScheme_map_eq {X Y U V : BigFppfOver D.B D.S D.hS}
    (hX : X = U) (hY : Y = V) (g : X ⟶ Y)
    {ψ : (BigFppfOver.toScheme D.B D.S D.hS).obj U ⟶ (BigFppfOver.toScheme D.B D.S D.hS).obj V}
    (h : (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hX.symm ≫ g ≫ eqToHom hY) = ψ)
    (hψ : Flat ψ ∧ Surjective ψ) :
    Flat (D.B.inclusion.map g.left) ∧ Surjective (D.B.inclusion.map g.left) := by
  subst hX hY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  change Flat ((BigFppfOver.toScheme D.B D.S D.hS).map g) ∧
    Surjective ((BigFppfOver.toScheme D.B D.S D.hS).map g)
  rw [h]
  exact hψ

/-- **The conclusion of Stacks 0DR2 at a point.** Every realization `Spec A ⟶ 𝒳` of every versal
formal object at the point `x₀ : Spec k ⟶ 𝒳`, for every presentation of `x₀` over an affine open
`Spec Λ` of `S`, is a flat object of `𝒳`. -/
def RealizationsFlatAt (x₀ : D.𝒳.val.val.obj) (k : Type u) [Field k] : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (_hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection),
    Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
    ∀ (hA : D.B.Contains (Spec (.of ξ.base))) (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA),
      (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ).Realization hA y hy →
      flatObject D.B D.S D.hS D.𝒳.val y

/-- **Step I of the proof of Stacks 0DR2.** If one realization of one versal formal object at
`x₀` is flat, then every realization of every versal formal object at `x₀`, for every
presentation of `x₀`, is flat. By part (1) of Stacks 0DR1 the two versal rings are comparable,
after possibly swapping them, as `A ≅ A'[[t₁, …, t_r]]` compatibly with the morphisms to `𝒳`;
the comparison map of spectra is flat and surjective, so flatness transfers along it in both
directions (Stacks 06Q0 and Stacks 06PX). -/
theorem realizationsFlatAt_of_flatObject {k : Type u} [Field k] (x₀ : D.𝒳.val.val.obj)
    {Λ : Type u} [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (hflat : flatObject D.B D.S D.hS D.𝒳.val y) :
    RealizationsFlatAt D x₀ k := by
  intro Λ' _ _ iΛ' hiΛ' hx₀' hfinite' ξ' hξ' hA' y' hy' Ry'
  rcases exists_powerSeries_comparison_realization D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite
      hfinite' ξ hξ ξ' hξ' Ry Ry' with ⟨r, e, -, m, hm⟩ | ⟨r, e, -, m, hm⟩
  · obtain ⟨hfl, hsu⟩ := flat_and_surjective_of_toScheme_map_eq D hy hy'
      (D.𝒳.val.val.p.map m) hm (flat_and_surjective_specMap_symm_comp_C r e)
    exact flatObject_of_flat_of_surjective D.B D.S D.hS D.𝒳 m hfl hsu hflat
  · obtain ⟨hfl, -⟩ := flat_and_surjective_of_toScheme_map_eq D hy' hy
      (D.𝒳.val.val.p.map m) hm (flat_and_surjective_specMap_symm_comp_C r e)
    exact flatObject_of_flat D.B D.S D.hS D.𝒳 m hfl hflat

/-- **Transfer of the conclusion of Stacks 0DR2 between two points along a faithfully flat
comparison** (the shape of Step II of the source's proof). Let `y` realize a versal formal object
at `x₀` and `y'` one at `x₁`, and let `m : y' ⟶ y` lie over a flat surjective morphism of
schemes. Then the conclusion of Stacks 0DR2 holds at `x₀` if and only if it holds at `x₁`:
flatness ascends along `m` (Stacks 06PX) and descends along it (Stacks 06Q0), and Step I spreads
it to all versal formal objects, all realizations and all presentations. -/
theorem realizationsFlatAt_iff_of_hom {k l : Type u} [Field k] [Field l]
    (x₀ x₁ : D.𝒳.val.val.obj)
    {Λ : Type u} [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    {Λ' : Type u} [CommRing Λ'] [Algebra Λ' l] (iΛ' : Spec (.of Λ') ⟶ D.S)
    (hiΛ' : _root_.AlgebraicGeometry.IsOpenImmersion iΛ')
    (hx₁ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₁ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ'))
    (hfinite' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ'))
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₁ hx₁).projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₁ hx₁ D.𝒳.val.property).cofibered ξ')
    {hA' : D.B.Contains (Spec (.of ξ'.base))} {y' : D.𝒳.val.val.obj}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₁ hx₁
      hfinite' ξ').Realization hA' y' hy')
    (m : y' ⟶ y) (hmflat : Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left))
    (hmsurj : Surjective (D.B.inclusion.map (D.𝒳.val.val.p.map m).left)) :
    RealizationsFlatAt D x₀ k ↔ RealizationsFlatAt D x₁ l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact realizationsFlatAt_of_flatObject D x₁ iΛ' hiΛ' hx₁ hfinite' ξ' hξ' Ry'
      (flatObject_of_flat D.B D.S D.hS D.𝒳 m hmflat (h Λ iΛ hiΛ hx₀ hfinite ξ hξ hA y hy Ry))
  · exact realizationsFlatAt_of_flatObject D x₀ iΛ hiΛ hx₀ hfinite ξ hξ Ry
      (flatObject_of_flat_of_surjective D.B D.S D.hS D.𝒳 m hmflat hmsurj
        (h Λ' iΛ' hiΛ' hx₁ hfinite' ξ' hξ' hA' y' hy' Ry'))

end AlgebraicGeometry.Stack

end
