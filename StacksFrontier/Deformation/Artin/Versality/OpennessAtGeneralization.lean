module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMonicExtensionLift
public import StacksFrontier.Deformation.Artin.LimitPreserving.FiniteTypeDescent
public import StacksFrontier.Deformation.Artin.RimSchlessinger.MonicExtensionDescent
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening
public import StacksFrontier.Deformation.Artin.Versality.SmallExtensionReduction
public import StacksFrontier.Deformation.ArtinCriteria.VersalSmoothLocus
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction

/-!
# Versality at a finite type point persists at its generizations

This is Stacks 0G2K: for a category fibred in groupoids `𝒳` over the big fppf site of a locally
Noetherian scheme `S`, with representable diagonal, satisfying (RS*) and limit preserving, an
object `x` over a scheme `U` of finite type over `S` which is versal at a finite type point `u₀`
is versal at every finite type point `u` specializing to `u₀`.

## Main results

* `Deformation.Artin.isVersalAt_of_specializes`: **Stacks 0G2K**.

## Implementation notes

The source argues by contradiction with the thickening of Stacks 0G2J and needs to section the
smooth morphism `Z ⟶ U'` of algebraic spaces over a first-order thickening of affine schemes
(Stacks 04AM). Here the lifting problems defining versality at `u` are solved directly, and only
over Artinian local rings, so that no global section is needed.

Let `B' ⟶ A` be a small extension and `(y ⟶ z, y ⟶ x)` a lifting problem at `u`. Glue `x` and
`z` along `y` by (RS*) to an object over the thickening `T = U ⨿_{Spec A} Spec B'`, and descend
it by limit preservation to an object `x'` over a finite type thickening `U ⊆ U'`
(`Deformation.Artin.exists_finiteTypeCover_thickening_descent`). The algebraic space `Z`
representing `(Sch/U') ×_{x', 𝒳, x} (Sch/U)` is smooth over `U'` at the canonical point over
`u₀` by Stacks 0CXM, hence on an open subspace containing the canonical point over `u`. An étale
chart only provides a point over `Spec A` after a finite separable extension of the residue field;
`AlgebraicGeometry.Space.exists_monic_lift_of_isSmooth` provides the lift after the monogenic
extension `B' ⟶ B'[X]/(g)`, which is read back as a solution of the base-changed lifting problem
in `𝒳`. Gluing that solution with the original one over `A` by (RS*) and pulling back along the
retraction `Stacks.MonicExtension.retraction` solves the original problem
(`Deformation.Artin.exists_lift_of_lift_after_retract`).

## References

* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0G2J](https://stacks.math.columbia.edu/tag/0G2J)
* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
  Polynomial

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the site over `S` whose image in `Over S` is a prescribed object is that
object of the site, as soon as the prescribed object is read off a morphism of the site. -/
theorem eq_siteObject_of_post {T : Scheme.{u}} (hT : B.Contains T) (b : T ⟶ S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (hX : (Over.post B.inclusion).obj X = Over.mk b) :
    X = AlgebraicGeometry.siteObject B S hS hT b := by
  have hl : X.left = B.obj hT := ObjectProperty.FullSubcategory.ext (congrArg Over.left hX)
  apply CostructuredArrow.obj_ext X _ hl
  apply B.inclusion.map_injective
  simp only [Functor.id_map, Functor.map_comp, eqToHom_map]
  have hh := Over.w (eqToHom hX)
  rw [Over.eqToHom_left] at hh
  dsimp only [Over.post, Functor.id_obj] at hh
  exact hh

/-- The spectrum of a subring of a product of two rings whose spectra lie in the site lies in
the site. -/
theorem contains_spec_subring_prod {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    (h₁ : B.Contains (Spec (.of R₁))) (h₂ : B.Contains (Spec (.of R₂)))
    (R : Subring (R₁ × R₂)) : B.Contains (Spec (.of R)) := by
  have hmk : Cardinal.mk R ≤ Cardinal.mk (R₁ × R₂) := Cardinal.mk_subtype_le _
  rw [BigFppfSite.Contains, Scheme.size_Spec] at h₁ h₂ ⊢
  refine lt_of_le_of_lt (max_le_max le_rfl hmk) ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  refine lt_of_le_of_lt (max_le_max le_rfl (Cardinal.mul_le_max _ _)) ?_
  refine lt_of_le_of_lt ?_ (max_lt h₁ h₂)
  exact max_le (le_max_of_le_left (le_max_left _ _)) (max_le (max_le
    (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right (le_max_right _ _)))
    (le_max_of_le_left (le_max_left _ _)))

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))

/-- **The finite type thickening of the proof of Stacks 0G2K.** Let `B' ⟶ A` be a surjection of
`Λ`-algebras with square-zero kernel, let `i : y ⟶ z` lie over `Spec A ⟶ Spec B'` and
`a : y ⟶ x` over `Spec φ` for `φ : R₀ ⟶ A`, with `R₀` of finite type over `Λ`. Then there are a
finite type `Λ`-algebra `R'` with maps `R' ⟶ R₀` (surjective) and `R' ⟶ B'` agreeing in `A`, an
object `x'` over `Spec R'`, and arrows `x ⟶ x'`, `z ⟶ x'` over their spectra, compatible with
`a` and `i`. -/
theorem exists_finiteType_thickening (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ A A' : Type u} [CommRing R₀] [CommRing A] [CommRing A'] [Algebra Λ R₀] [Algebra Λ A]
    [Algebra Λ A'] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀))) (hA : B.Contains (Spec (.of A)))
    (hA' : B.Contains (Spec (.of A')))
    (φ : R₀ →ₐ[Λ] A) (f : A' →ₐ[Λ] A) (hf : Function.Surjective f)
    (hker : RingHom.ker f.toRingHom ^ 2 = ⊥)
    {x y z : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (hy : 𝒳.val.p.obj y = siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hz : 𝒳.val.p.obj z =
      siteObject B S hS hA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ))
    (i : y ⟶ z) (a : y ⟶ x)
    (hi : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f) i)
    (ha : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA hR₀ φ) a) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra Λ R') (_ : Algebra.FiniteType Λ R')
      (hR' : B.Contains (Spec (.of R'))) (gU : R' →ₐ[Λ] R₀) (gZ : R' →ₐ[Λ] A')
      (_ : Function.Surjective gU) (_ : φ.comp gU = f.comp gZ)
      (x' : 𝒳.val.obj)
      (_ : 𝒳.val.p.obj x' =
        siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ))
      (κ : x ⟶ x') (ζ : z ⟶ x'),
      𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ hR' gU) κ ∧
      𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA' hR' gZ) ζ ∧
      a ≫ κ = i ≫ ζ := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let : p.IsFibered := hp.isFibered
  -- the fibre product ring `R₀ ×_A A'`
  let RP : Subring (R₀ × A') := φ.toRingHom.pullback f.toRingHom
  let algRP : Λ →+* RP := RingHom.codRestrict
    ((algebraMap Λ R₀).prod (algebraMap Λ A')) RP (fun l => by
      change φ (algebraMap Λ R₀ l) = f (algebraMap Λ A' l)
      rw [φ.commutes, f.commutes])
  let : Algebra Λ RP := algRP.toAlgebra
  let fstA : RP →ₐ[Λ] R₀ :=
    { φ.toRingHom.pullbackFst f.toRingHom with commutes' := fun _ => rfl }
  let sndA : RP →ₐ[Λ] A' :=
    { φ.toRingHom.pullbackSnd f.toRingHom with commutes' := fun _ => rfl }
  have hfst : Function.Surjective fstA :=
    RingHom.surjective_pullbackFst_of_surjective _ _ hf
  have hcomm : φ.comp fstA = f.comp sndA := by
    ext r
    exact r.2
  let I : Ideal RP := RingHom.ker fstA.toRingHom
  have hI : I ^ 2 = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha1 : a.1.1 = 0 := ha
    have hb1 : b.1.1 = 0 := hb
    have ha2 : a.1.2 ∈ RingHom.ker f.toRingHom := by
      change f a.1.2 = 0
      rw [← (show φ a.1.1 = f a.1.2 from a.2), ha1, map_zero]
    have hb2 : b.1.2 ∈ RingHom.ker f.toRingHom := by
      change f b.1.2 = 0
      rw [← (show φ b.1.1 = f b.1.2 from b.2), hb1, map_zero]
    have hab : a.1.2 * b.1.2 ∈ RingHom.ker f.toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha2 hb2
    rw [hker] at hab
    refine Ideal.mem_bot.2 (Subtype.ext (Prod.ext ?_ (Ideal.mem_bot.1 hab)))
    change a.1.1 * b.1.1 = 0
    rw [ha1, zero_mul]
  have : Algebra.FiniteType Λ (RP ⧸ I) :=
    Algebra.FiniteType.equiv inferInstance
      (Ideal.quotientKerAlgEquivOfSurjective (f := fstA) hfst).symm
  have hRP : B.Contains (Spec (.of RP)) := contains_spec_subring_prod B hR₀ hA' RP
  -- the four objects of the site and the square
  let UaS := siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  let AS := siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
  let A'S := siteObject B S hS hA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ)
  let TS := siteObject B S hS hRP (Spec.map (CommRingCat.ofHom (algebraMap Λ RP)) ≫ iΛ)
  let fT := specAlgSiteHom B S hS iΛ hA hR₀ φ
  let gT := specAlgSiteHom B S hS iΛ hA hA' f
  let iT := specAlgSiteHom B S hS iΛ hR₀ hRP fstA
  let jT := specAlgSiteHom B S hS iΛ hA' hRP sndA
  have hsq : fT ≫ iT = gT ≫ jT := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (congrArg AlgHom.toRingHom hcomm)
  let AA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨AS, inferInstanceAs (IsAffine (Spec _))⟩
  let UU : AlgebraicGeometry.BigAffineFppf B S hS := ⟨UaS, inferInstanceAs (IsAffine (Spec _))⟩
  let BB : AlgebraicGeometry.BigAffineFppf B S hS := ⟨A'S, inferInstanceAs (IsAffine (Spec _))⟩
  let TT : AlgebraicGeometry.BigAffineFppf B S hS := ⟨TS, inferInstanceAs (IsAffine (Spec _))⟩
  have hpb : IsPullback
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk iT : UU ⟶ TT)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk jT : BB ⟶ TT)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk fT : AA ⟶ UU)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk gT : AA ⟶ BB)).appTop :=
    specMap_appTop_isPullback (Stacks.Pushout.isPullback_ofHom_pullback φ.toRingHom f.toRingHom)
  have hsurj : Function.Surjective ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (ObjectProperty.homMk gT : AA ⟶ BB)).appTop.hom :=
    specMap_appTop_surjective (CommRingCat.ofHom f.toRingHom) hf
  have hker' : RingHom.ker ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (ObjectProperty.homMk gT : AA ⟶ BB)).appTop.hom ^ 2 = ⊥ :=
    specMap_appTop_ker_sq (CommRingCat.ofHom f.toRingHom) hker
  have hE := hRS AA UU BB TT (ObjectProperty.homMk fT) (ObjectProperty.homMk gT)
    (ObjectProperty.homMk iT) (ObjectProperty.homMk jT)
    (ObjectProperty.hom_ext _ hsq) hpb hsurj hker'
  have : (fiberSquareComparison p (Functor.chosenPullbacks p) fT gT iT jT hsq).IsEquivalence :=
    hE
  have : (fiberSquareComparison p (Functor.chosenPullbacks p) fT gT iT jT hsq).EssSurj :=
    inferInstance
  have : p.IsHomLift fT a := ha
  have : p.IsHomLift gT i := hi
  obtain ⟨yT, hyT, r, s, hr, hs, hrs⟩ := exists_glued_object_of_fiberSquareComparison_essSurj
    p hp (Functor.chosenPullbacks p) fT gT iT jT hsq hx hz a i
  -- descent to a finite type stage
  obtain ⟨Asub, x'f, δ, hδ, -⟩ := exists_finiteTypeCover_thickening_descent B S hS 𝒳 hlim iΛ hΛ
    hRP I hI ⟨yT, hyT⟩
  let : Algebra.FiniteType Λ Asub.1 := (Subalgebra.fg_iff_finiteType Asub.1).1 Asub.2.1
  let gU : Asub.1 →ₐ[Λ] R₀ := fstA.comp Asub.1.val
  let gZ : Asub.1 →ₐ[Λ] A' := sndA.comp Asub.1.val
  have hgU : Function.Surjective gU := by
    intro r₀
    obtain ⟨t, ht⟩ := hfst r₀
    obtain ⟨b, hb⟩ := Asub.2.2 (Ideal.Quotient.mk I t)
    refine ⟨b, ?_⟩
    have : (b : RP) - t ∈ I := Ideal.Quotient.eq.1 hb
    have h0 : fstA ((b : RP) - t) = 0 := this
    rw [_root_.map_sub, sub_eq_zero] at h0
    change fstA (b : RP) = r₀
    rw [h0, ht]
  -- composing a lift over `Spec RP` with the descent arrow `δ`
  have comp_lift : ∀ {T : Type u} [CommRing T] [Algebra Λ T] (hT : B.Contains (Spec (.of T)))
      (c : RP →ₐ[Λ] T) {w : 𝒳.val.obj} (m : w ⟶ yT)
      (hm : p.IsHomLift (specAlgSiteHom B S hS iΛ hT hRP c) m),
      p.IsHomLift (specAlgSiteHom B S hS iΛ hT (contains_stage B hΛ Asub.1 Asub.2.1)
        (c.comp Asub.1.val)) (m ≫ δ) := by
    intro T _ _ hT c w m hm
    have h := @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hm hδ
    convert h using 1
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hR' : B.Contains (Spec (.of Asub.1)) := contains_stage B hΛ Asub.1 Asub.2.1
  refine ⟨Asub.1, inferInstance, inferInstance, inferInstance, hR', gU, gZ, hgU, ?_, x'f.1,
    x'f.2, r ≫ δ, s ≫ δ, ?_, ?_, ?_⟩
  · rw [← AlgHom.comp_assoc, hcomm, AlgHom.comp_assoc]
  · exact comp_lift hR₀ fstA r hr
  · exact comp_lift hA' sndA s hs
  · rw [← Category.assoc, hrs, Category.assoc]

/-- Transport of the lifting relation along equalities of the source and target objects, read
on underlying schemes. -/
theorem isHomLift_of_toScheme_eq {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {R R' T T' : AlgebraicGeometry.BigFppfOver B S hS} (m : R ⟶ T) (m' : R' ⟶ T')
    (hR : R = R') (hT : T = T')
    (h : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m ≫
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hT) =
      eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hR) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m')
    {a b : F} (φ : a ⟶ b) [p.IsHomLift m φ] : p.IsHomLift m' φ := by
  subst hR hT
  have hm : m = m' := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective (by
    simpa using h)
  subst hm
  infer_instance

/-- Composition of the morphisms of the site induced by algebra maps. -/
theorem specAlgSiteHom_comp {Λ T T' T'' : Type u} [CommRing Λ] [CommRing T] [CommRing T']
    [CommRing T''] [Algebra Λ T] [Algebra Λ T'] [Algebra Λ T''] (iΛ : Spec (.of Λ) ⟶ S)
    (hT : B.Contains (Spec (.of T))) (hT' : B.Contains (Spec (.of T')))
    (hT'' : B.Contains (Spec (.of T''))) (g : T' →ₐ[Λ] T) (g' : T'' →ₐ[Λ] T') :
    specAlgSiteHom B S hS iΛ hT hT' g ≫ specAlgSiteHom B S hS iΛ hT' hT'' g' =
      specAlgSiteHom B S hS iΛ hT hT'' (g.comp g') := by
  apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A morphism of the site whose underlying morphism of schemes is a monomorphism is a
monomorphism. -/
theorem mono_of_mono_inclusion_map {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U')
    (hg : Mono (B.inclusion.map g.left)) : Mono g :=
  ⟨fun {_} a b hab => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
    ((cancel_mono (B.inclusion.map g.left)).mp (by
      have h := congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map hab
      rwa [Functor.map_comp, Functor.map_comp] at h))⟩

/-- An equality of morphisms of the site, up to `eqToHom`s, read on underlying schemes: both
morphisms are a given morphism of schemes `n` under identifications of their sources and targets
with given schemes. -/
theorem eq_eqToHom_comp_comp_eqToHom {X X' Y Y' : AlgebraicGeometry.BigFppfOver B S hS}
    (hX : X = X') (hY : Y' = Y) (m : X ⟶ Y) (m' : X' ⟶ Y') {TX TY : Scheme.{u}}
    (eX : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X = TX)
    (eX' : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X' = TX)
    (eY : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Y = TY)
    (eY' : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Y' = TY) (n : TX ⟶ TY)
    (hm : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m = eqToHom eX ≫ n ≫ eqToHom eY.symm)
    (hm' : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m' =
      eqToHom eX' ≫ n ≫ eqToHom eY'.symm) :
    m = eqToHom hX ≫ m' ≫ eqToHom hY := by
  subst hX hY eX eY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm hm' ⊢
  exact (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective (hm.trans hm'.symm)

/-- The structure morphism to `U'` of an object over `U'` that is a spectrum of an algebra over
`T₀`, with structure map factoring through `m` as `Spec T ⟶ Spec T₀ ⟶ U'`, read in the site. -/
private theorem iteratedSliceBackward_hom_eq {Λ T₀ T : Type u} [CommRing Λ] [CommRing T₀]
    [CommRing T] [Algebra Λ T₀] [Algebra Λ T] [Algebra T₀ T] [IsScalarTower Λ T₀ T]
    (iΛ : Spec (.of Λ) ⟶ S) (hT₀ : B.Contains (Spec (.of T₀))) (hT : B.Contains (Spec (.of T)))
    {U' : AlgebraicGeometry.BigFppfOver B S hS}
    (m : siteObject B S hS hT₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ T₀)) ≫ iΛ) ⟶ U')
    {V : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2}
    (hV : (Over.map U'.hom).obj V =
      siteObject B S hS hT (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ))
    (eV : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj ((Over.map U'.hom).obj V) =
      Spec (.of T))
    (hs : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        ((Over.iteratedSliceBackward U').obj V).hom =
      eqToHom eV ≫ Spec.map (CommRingCat.ofHom (algebraMap T₀ T)) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) :
    ((Over.iteratedSliceBackward U').obj V).hom =
      (eqToHom hV ≫ specAlgSiteHom B S hS iΛ hT hT₀ (IsScalarTower.toAlgHom Λ T₀ T)) ≫ m := by
  rw [Category.assoc]
  refine (eq_eqToHom_comp_comp_eqToHom B S hS hV rfl _
    (specAlgSiteHom B S hS iΛ hT hT₀ (IsScalarTower.toAlgHom Λ T₀ T) ≫ m) eV rfl rfl rfl
    (Spec.map (CommRingCat.ofHom (algebraMap T₀ T)) ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) ?_ ?_).trans ?_
  · rw [eqToHom_refl, Category.comp_id]
    exact hs
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.map_comp]
    rfl
  · rw [eqToHom_refl, Category.comp_id]

open BaseChange in
/-- **The descent step of the proof of Stacks 0G2K.** In the situation of the finite type
thickening (`x ⟶ x'` over a monomorphism `g`, `z ⟶ x'` compatible with `a` and `i`), suppose a
section `c''` of the space `F` representing the base change over `Spec B''`, `B'' = A'[X]/(G)`,
restricts over `Spec A''`, `A'' = A[X]/(f G)`, to the canonical section. Then the lifting problem
`(i, a)` has a solution. -/
theorem exists_lift_of_chartSection
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {R₀ A A' : Type u} [CommRing R₀] [CommRing A] [CommRing A'] [Algebra Λ R₀] [Algebra Λ A]
    [Algebra Λ A']
    (hR₀ : B.Contains (Spec (.of R₀))) (hA : B.Contains (Spec (.of A)))
    (hA' : B.Contains (Spec (.of A')))
    (f : A' →ₐ[Λ] A) (hf : Function.Surjective f) (hker : RingHom.ker f.toRingHom ^ 2 = ⊥)
    {G : A'[X]} (hG : G.Monic) (hdeg : 0 < G.natDegree)
    (hA'' : B.Contains (Spec (.of (AdjoinRoot (G.map f.toRingHom)))))
    (hB'' : B.Contains (Spec (.of (AdjoinRoot G))))
    {U' : AlgebraicGeometry.BigFppfOver B S hS}
    (g : siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ) ⟶ U')
    (hgmono : Mono g)
    {x x' y z : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (hx' : 𝒳.val.p.obj x' = U')
    (hy : 𝒳.val.p.obj y = siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hz : 𝒳.val.p.obj z =
      siteObject B S hS hA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ))
    (i : y ⟶ z) (hi : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f) i)
    (mA : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) ⟶
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (a : y ⟶ x) (ha : 𝒳.val.p.IsHomLift mA a)
    (κ : x ⟶ x') (hκ : 𝒳.val.p.IsHomLift g κ)
    (mZ : siteObject B S hS hA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ) ⟶ U')
    (ζ : z ⟶ x') (hζ : 𝒳.val.p.IsHomLift mZ ζ) (hcompat : a ≫ κ = i ≫ ζ)
    (F : (AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 _ U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F)
    (s₀ : F.obj (op (overObj B S hS g)))
    (hsec : sectionArrow B S hS 𝒳 _ U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F e
          ⟨overObj B S hS g, Discrete.mk s₀⟩ ≫ κ =
        cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)))
    {AV A''V B''V : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2}
    (hAV : AV ⟶ overObj B S hS g) (pA : A''V ⟶ AV) (i'' : A''V ⟶ B''V)
    (c'' : F.obj (op B''V)) (hc'' : F.map i''.op c'' = F.map (pA ≫ hAV).op s₀)
    (hA''eq : (Over.map U'.hom).obj A''V = siteObject B S hS hA''
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot (G.map f.toRingHom)))) ≫ iΛ))
    (hB''eq : (Over.map U'.hom).obj B''V = siteObject B S hS hB''
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot G))) ≫ iΛ))
    (eA : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj ((Over.map U'.hom).obj A''V) =
      Spec (.of (AdjoinRoot (G.map f.toRingHom))))
    (eB : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj ((Over.map U'.hom).obj B''V) =
      Spec (.of (AdjoinRoot G)))
    (hi''s : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ((Over.map U'.hom).map i'') =
      eqToHom eA ≫
        Spec.map (CommRingCat.ofHom (Stacks.MonicExtension.extMap f.toRingHom (G := G))) ≫
        eqToHom eB.symm)
    (hA''s : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        ((Over.iteratedSliceBackward U').obj A''V).hom =
      eqToHom eA ≫ Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot (G.map f.toRingHom)))) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (mA ≫ g))
    (hB''s : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        ((Over.iteratedSliceBackward U').obj B''V).hom =
      eqToHom eB ≫ Spec.map (CommRingCat.ofHom (algebraMap A' (AdjoinRoot G))) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map mZ) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let gA := G.map f.toRingHom
  let tA := IsScalarTower.toAlgHom Λ A (AdjoinRoot gA)
  let tA' := IsScalarTower.toAlgHom Λ A' (AdjoinRoot G)
  have hi''eq : (Over.map U'.hom).map i'' = eqToHom hA''eq ≫
      specAlgSiteHom B S hS iΛ hA'' hB'' (extAlgHom f G) ≫ eqToHom hB''eq.symm :=
    eq_eqToHom_comp_comp_eqToHom B S hS hA''eq hB''eq.symm _ _ eA rfl eB rfl _ hi''s
      (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
  have hA''hom := iteratedSliceBackward_hom_eq B S hS iΛ hA hA'' (mA ≫ g) hA''eq eA hA''s
  have hB''hom := iteratedSliceBackward_hom_eq B S hS iΛ hA' hB'' mZ hB''eq eB hB''s
  let mpy := eqToHom hA''eq ≫ specAlgSiteHom B S hS iΛ hA'' hA tA
  let mpz := eqToHom hB''eq ≫ specAlgSiteHom B S hS iΛ hB'' hA' tA'
  obtain ⟨y'', py, hpy⟩ := hp.exists_lift mpy y hy
  obtain ⟨z'', pz, hpz⟩ := hp.exists_lift mpz z hz
  have hy''p := IsHomLift.domain_eq p mpy py
  have hz''p := IsHomLift.domain_eq p mpz pz
  have := hp.isStronglyCartesian_homLift mpz pz
  have hpyi : p.IsHomLift (mpy ≫ specAlgSiteHom B S hS iΛ hA hA' f) (py ≫ i) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hpy hi
  have hf' : mpy ≫ specAlgSiteHom B S hS iΛ hA hA' f = (Over.map U'.hom).map i'' ≫ mpz := by
    rw [hi''eq]
    simp only [mpy, mpz, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [specAlgSiteHom_comp, specAlgSiteHom_comp]
    congr 2
    ext a'
    exact (Stacks.MonicExtension.extMap_of f.toRingHom a').symm
  let i''X : y'' ⟶ z'' := IsStronglyCartesian.map p mpz pz hf' (py ≫ i)
  have hi''X : p.IsHomLift ((Over.map U'.hom).map i'') i''X :=
    IsStronglyCartesian.map_isHomLift p _ pz hf' (py ≫ i)
  have hcommX : i''X ≫ pz = py ≫ i := IsStronglyCartesian.fac p _ pz hf' (py ≫ i)
  have hpzζ : p.IsHomLift ((Over.iteratedSliceBackward U').obj B''V).hom (pz ≫ ζ) := by
    rw [hB''hom]
    exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hpz hζ
  have hpya : p.IsHomLift ((Over.iteratedSliceBackward U').obj A''V).hom (py ≫ a ≫ κ) := by
    rw [hA''hom]
    exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hpy
      (@IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ ha hκ)
  obtain ⟨b'', hb''⟩ := exists_lift_of_section B S hS 𝒳 g hgmono hx hx' κ hκ F e s₀ hsec hAV pA
    i'' c'' hc'' hy''p hz''p a i ζ hcompat py pz i''X hcommX hpzζ hpya hi''X
  have hi''X' : p.IsHomLift (eqToHom hA''eq ≫ specAlgSiteHom B S hS iΛ hA'' hB''
      (extAlgHom f G) ≫ eqToHom hB''eq.symm) i''X := by
    rw [← hi''eq]
    exact hi''X
  exact exists_lift_of_monicExtension' B S hS p hp hRS iΛ hA hA' hR₀ f hf hker hG hdeg hA'' hB''
    hx i hi a hA''eq hB''eq py hpy pz hpz i''X hi''X' hcommX b'' hb''

open BaseChange in
/-- **The chart step of the proof of Stacks 0G2K.** In the situation of the finite type
thickening, let `Z₀` be an open subspace, smooth over `Spec R'`, of the space `F` representing the
base change, through which every point over `u` of the canonical section factors, and suppose
`Spec A ⟶ Spec R₀` maps to `u`. Then the lifting problem `(i, a)` has a solution. -/
theorem exists_lift_of_smoothChart
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {R₀ R' : Type u} [CommRing R₀] [CommRing R'] [Algebra Λ R₀] [Algebra Λ R']
    (hR₀ : B.Contains (Spec (.of R₀))) (hR' : B.Contains (Spec (.of R')))
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A'] [IsLocalRing A]
    [IsArtinianRing A] (f : A' →ₐ[Λ] A)
    (hfs : Function.Surjective f) (hker : RingHom.ker f.toRingHom ^ 2 = ⊥)
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (φ : R₀ →ₐ[Λ] A) (gU : R' →ₐ[Λ] R₀) (gZ : R' →ₐ[Λ] A') (hcomm : φ.comp gU = f.comp gZ)
    (hgmono : Mono (specAlgSiteHom B S hS iΛ hR₀ hR' gU))
    {x x' y z : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (hx' : 𝒳.val.p.obj x' =
      siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ))
    (hyS : 𝒳.val.p.obj y =
      siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (hzS : 𝒳.val.p.obj z =
      siteObject B S hS hA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ))
    (i : y ⟶ z) (hi' : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f) i)
    (a : y ⟶ x) (ha' : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA hR₀ φ) a)
    (κ' : x ⟶ x') (hκ' : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ hR' gU) κ')
    (ζ : z ⟶ x') (hζ : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hA' hR' gZ) ζ)
    (hcompat : a ≫ κ' = i ≫ ζ)
    (F : (AlgebraicGeometry.BigFppfOver B
      (siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ)).left.1
      (siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ)).left.2)ᵒᵖ ⥤
        Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 _ _ x hx (twoYoneda B S hS 𝒳 _ x' hx') F)
    (s₀ : F.obj (op (overObj B S hS (specAlgSiteHom B S hS iΛ hR₀ hR' gU))))
    (Z₀ : Subfunctor F)
    (hZ₀ : AlgebraicGeometry.Space.IsOpenSubspace B _ _ Z₀)
    (hsmZ : AlgebraicGeometry.Space.IsSmooth B _ _ (Z₀.ι ≫ terminal.from F))
    (hsec : sectionArrow B S hS 𝒳 _ _ x hx (twoYoneda B S hS 𝒳 _ x' hx') F e
          ⟨overObj B S hS (specAlgSiteHom B S hS iΛ hR₀ hR' gU), Discrete.mk s₀⟩ ≫ κ' =
        cartArrow B S hS 𝒳 _ x' hx' ((Over.iteratedSliceBackward _).obj
          (overObj B S hS (specAlgSiteHom B S hS iΛ hR₀ hR' gU))))
    (u : (siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)).left.1)
    (hfac : ∀ (Y : AlgebraicGeometry.BigFppfOver B _ _)
        (h : Y ⟶ overObj B S hS (specAlgSiteHom B S hS iΛ hR₀ hR' gU)),
        (∀ y, (AlgebraicGeometry.BigFppfOver.toScheme B _ _).map h y = u) →
        ∃ α : yoneda.obj Y ⟶ Z₀.toFunctor, α ≫ Z₀.ι = yoneda.map h ≫ yonedaEquiv.symm s₀)
    (hφu : ∀ yy, Spec.map (CommRingCat.ofHom φ.toRingHom) yy = u) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let UaS := siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  let U'S := siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ)
  let gS : UaS ⟶ U'S := specAlgSiteHom B S hS iΛ hR₀ hR' gU
  -- `Spec A` as an object over `U'`, and the point of `Z₀` over it
  let fT := specAlgSiteHom B S hS iΛ hA hR₀ φ
  let AV := overObj B S hS (fT ≫ gS)
  let hAV : AV ⟶ overObj B S hS gS := Over.homMk fT.left rfl
  have hpts : ∀ yy, (AlgebraicGeometry.BigFppfOver.toScheme B U'S.left.1 U'S.left.2).map hAV yy =
      u := by
    intro yy
    change (Spec.map (CommRingCat.ofHom φ.toRingHom)) yy = _
    exact hφu yy
  obtain ⟨α₀, hα₀⟩ := hfac AV hAV hpts
  -- the monogenic extension and the lift through the chart
  have hsm : AlgebraicGeometry.Space.IsSmooth B U'S.left.1 U'S.left.2
      (terminal.from Z₀.toFunctor) := by
    rwa [show terminal.from Z₀.toFunctor = Z₀.ι ≫ terminal.from F from terminal.hom_ext _ _]
  have hmA : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨gbar, hgm, hgd, hlift⟩ := AlgebraicGeometry.Space.exists_monic_lift_of_isSmooth
    B U'S.left.1 U'S.left.2 hZ₀.1 hsm (RA := CommRingCat.of A) hmA AV (Iso.refl _) α₀
  have hres : Function.Surjective ((IsLocalRing.residue A).comp f.toRingHom) :=
    IsLocalRing.residue_surjective.comp hfs
  obtain ⟨G, hGmap, hGdeg, hG⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hres gbar) hgm
  have hGA : (G.map f.toRingHom).map (IsLocalRing.residue A) = gbar := by
    rw [Polynomial.map_map, hGmap]
  have hgA : (G.map f.toRingHom).Monic := hG.map _
  have hdeg : 0 < G.natDegree := hGdeg ▸ hgd
  -- the spectra of the monogenic extensions, over `U'`
  let gA := G.map f.toRingHom
  let ext := Stacks.MonicExtension.extMap f.toRingHom (G := G)
  have hA'' : B.Contains (Spec (.of (AdjoinRoot gA))) := contains_spec_adjoinRoot B hA hgA
  have hB'' : B.Contains (Spec (.of (AdjoinRoot G))) := contains_spec_adjoinRoot B hA' hG
  let gZS := specAlgSiteHom B S hS iΛ hA' hR' gZ
  let A'V := overObj B S hS gZS
  let A''V : AlgebraicGeometry.BigFppfOver B U'S.left.1 U'S.left.2 :=
    Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot gA))) ≫
      B.inclusion.map AV.hom⟩ : B.obj hA'' ⟶ B.obj U'S.left.2)
  let B''V : AlgebraicGeometry.BigFppfOver B U'S.left.1 U'S.left.2 :=
    Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap A' (AdjoinRoot G))) ≫
      B.inclusion.map A'V.hom⟩ : B.obj hB'' ⟶ B.obj U'S.left.2)
  let pA : A''V ⟶ AV := Over.homMk ⟨Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot gA)))⟩
    (by apply ObjectProperty.hom_ext; rfl)
  have hext : ∀ a' : A', ext (AdjoinRoot.of G a') = AdjoinRoot.of gA (f a') :=
    fun a' => Stacks.MonicExtension.extMap_of f.toRingHom a'
  let i'' : A''V ⟶ B''V := Over.homMk ⟨Spec.map (CommRingCat.ofHom ext)⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    change ext (AdjoinRoot.of G (gZ r)) = AdjoinRoot.of gA (φ (gU r))
    rw [hext]
    exact congrArg (AdjoinRoot.of gA) (AlgHom.congr_fun hcomm r).symm)
  have hpA : (AlgebraicGeometry.BigFppfOver.toScheme B U'S.left.1 U'S.left.2).map pA =
      (Iso.refl _).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot gA))) ≫
        (Iso.refl _).inv := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    rfl
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B U'S.left.1 U'S.left.2).map i'') :=
    Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom ext)
      (Stacks.MonicExtension.extMap_surjective f.toRingHom hfs)
      (Stacks.MonicExtension.ker_extMap_sq f.toRingHom hG hker)
  obtain ⟨γ, hγ⟩ := hlift gA hgA hGA A''V B''V (Iso.refl _) pA hpA i'' hthick
    (inferInstanceAs (IsAffine (Spec _)))
  -- the objects of `𝒳` over the two spectra, and the arrows of the descent
  let yV := twoYoneda B S hS 𝒳 U'S x' hx'
  have hyV : yV ⋙ p = Over.map U'S.hom := twoYoneda_comp B S hS 𝒳 U'S x' hx'
  have hAVhom : B.inclusion.map AV.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom gU.toRingHom) := Functor.map_comp _ _ _
  have hA''eq : (Over.map U'S.hom).obj A''V =
      siteObject B S hS hA''
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot gA))) ≫ iΛ) := by
    refine congrArg Over.mk (ObjectProperty.hom_ext _ ?_)
    change Spec.map _ ≫ B.inclusion.map AV.hom ≫ Spec.map _ ≫ iΛ = _
    rw [hAVhom, Category.assoc, specMap_algHom_comp_assoc gU, specMap_algHom_comp_assoc φ]
    exact specMap_algHom_comp_assoc (IsScalarTower.toAlgHom Λ A (AdjoinRoot gA)) iΛ
  have hB''eq : (Over.map U'S.hom).obj B''V =
      siteObject B S hS hB'' (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot G))) ≫ iΛ) := by
    refine congrArg Over.mk (ObjectProperty.hom_ext _ ?_)
    change (Spec.map _ ≫ B.inclusion.map A'V.hom) ≫ Spec.map _ ≫ iΛ = _
    rw [show B.inclusion.map A'V.hom = Spec.map (CommRingCat.ofHom gZ.toRingHom) from rfl,
      Category.assoc, specMap_algHom_comp_assoc gZ]
    exact specMap_algHom_comp_assoc (IsScalarTower.toAlgHom Λ A' (AdjoinRoot G)) iΛ
  -- the section of `F` over `B''`
  let c'' := yonedaEquiv (γ ≫ Z₀.ι)
  have hc'' : F.map i''.op c'' = F.map (pA ≫ hAV).op s₀ := by
    simp only [c'', yonedaEquiv_naturality]
    rw [← Category.assoc, hγ, Category.assoc, hα₀, ← Category.assoc, ← Functor.map_comp,
      ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact exists_lift_of_chartSection B S hS 𝒳 hRS iΛ hR₀ hA hA' f hfs hker hG hdeg hA'' hB''
    gS hgmono hx hx' hyS hzS i hi' fT a ha' κ' hκ' gZS ζ hζ
    hcompat F e s₀ hsec hAV pA i'' c'' hc'' hA''eq hB''eq rfl rfl
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [eqToHom_refl, Category.id_comp, Functor.map_comp]; rfl)
    (by simp only [eqToHom_refl, Category.id_comp]; rfl)

open BaseChange in
/-- **The core of Stacks 0G2K.** Let `x` be an object over `Spec R₀`, with `R₀` of finite type
over `Λ` and `Spec Λ ⊆ S` an affine open, versal at a finite type point `u₀`. Then `x` has the
lifting property at every residue point `κ` specializing to `u₀` against every small extension.
-/
theorem liftsAlong_of_isVersalAt_of_specializes [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (u₀ : Spec (.of R₀)) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x (congrArg (Over.post B.inclusion).obj hx))
    {k : Type u} [Field k] [Algebra Λ k] (κ : Spec (.of k) ⟶ Spec (.of R₀))
    (hspec : κ (IsLocalRing.closedPoint k) ⤳ u₀)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A' ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    LiftsAlong B S hS 𝒳.val.p iΛ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      x (congrArg (Over.post B.inclusion).obj hx) κ f := by
  classical
  intro y z hy hz i hi a ha
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let : p.IsFibered := hp.isFibered
  let q := p ⋙ Over.post B.inclusion
  have hcont : ∀ (w : 𝒳.val.obj) (T : Scheme.{u}), B.inclusion.obj (p.obj w).left = T →
      B.Contains T := by
    rintro w T rfl
    exact (p.obj w).left.2
  have hA : B.Contains (Spec (.of A)) := hcont y _ (congrArg Over.left hy)
  have hA' : B.Contains (Spec (.of A')) := hcont z _ (congrArg Over.left hz)
  have hyS := eq_siteObject_of_post B S hS hA _ (p.obj y) hy
  have hzS := eq_siteObject_of_post B S hS hA' _ (p.obj z) hz
  have hfs : Function.Surjective f.hom := hf.2.2.2.2.1
  have hker : RingHom.ker f.hom.toRingHom ^ 2 = ⊥ := smallExtension_kernel_sq_zero f hf
  -- the ring map `R₀ ⟶ A` under `a`
  obtain ⟨φ, hφ⟩ := exists_algHom_of_specMap S iΛ
    (schemeMap q hy (congrArg (Over.post B.inclusion).obj hx) a)
    (schemeMap_over q hy _ a)
  have ha' : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hR₀ φ) a :=
    isHomLift_of_schemeMap B S hS p hyS hx _ a (by rw [toScheme_specSiteHom, hφ])
  have hi' : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f.hom) i :=
    isHomLift_of_schemeMap B S hS p hyS hzS _ i (by rw [toScheme_specSiteHom]; exact hi)
  -- the finite type thickening
  obtain ⟨R', _, _, _, hR', gU, gZ, hgU, hcomm, x', hx', κ', ζ, hκ', hζ, hcompat⟩ :=
    exists_finiteType_thickening B S hS 𝒳 hRS hlim iΛ hΛ hR₀ hA hA' φ f.hom hfs hker hx hyS hzS
      i a hi' ha'
  -- the smooth locus of the base change
  let UaS := siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  let U'S := siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ)
  have hlftAlg : ∀ (T : Type u) [CommRing T] [Algebra Λ T] [Algebra.FiniteType Λ T],
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ) := by
    intro T _ _ _
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ T))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    infer_instance
  have : LocallyOfFiniteType (B.inclusion.map UaS.hom) := hlftAlg R₀
  have : LocallyOfFiniteType (B.inclusion.map U'S.hom) := hlftAlg R'
  let gS : UaS ⟶ U'S := specAlgSiteHom B S hS iΛ hR₀ hR' gU
  have hgmono : Mono (B.inclusion.map gS.left) := by
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom gU.toRingHom) hgU
    change Mono (Spec.map (CommRingCat.ofHom gU.toRingHom))
    infer_instance
  obtain ⟨F, hF, e, s₀, Z₀, hZ₀, hsmZ, hsec, hfac⟩ := exists_smooth_openSubspace_of_isVersalAt
    B S hS 𝒳 hΔ hRS hlim gS hgmono hx hx' κ' hκ' u₀ (κ (IsLocalRing.closedPoint k)) hu₀ hspec
    hversal
  have hsubA : ∀ c d : Spec (.of A), c = d := subsingleton_spec_of_isArtinianRing A
  have hφu : ∀ yy, Spec.map (CommRingCat.ofHom φ.toRingHom) yy = κ (IsLocalRing.closedPoint k) := by
    intro yy
    rw [hsubA yy ((Spec.map (CommRingCat.ofHom (residueMap A))) (IsLocalRing.closedPoint k)),
      ← ha, hφ]
    rfl
  exact exists_lift_of_smoothChart B S hS 𝒳 hRS iΛ hR₀ hR' f.hom hfs hker hA hA' φ gU gZ hcomm
    (mono_of_mono_inclusion_map B S hS gS hgmono) hx hx' hyS hzS i hi' a ha' κ' hκ' ζ hζ hcompat
    F e s₀ Z₀ hZ₀ hsmZ hsec _ hfac hφu

/-- **Stacks 0G2K over an affine chart.** Let `x` over `Spec R₀`, with `R₀` of finite type over
`Λ` and `Spec Λ ⊆ S` an affine open, be versal at a finite type point `u₀`. Then `x` is versal at
every generization of `u₀`. -/
theorem isVersalAt_of_specializes_chart [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (u₀ : Spec (.of R₀)) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x (congrArg (Over.post B.inclusion).obj hx))
    (t : Spec (.of R₀)) (htw : t ⤳ u₀) :
    IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) t x (congrArg (Over.post B.inclusion).obj hx) := by
  let U' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  have hx' : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U' :=
    congrArg (Over.post B.inclusion).obj hx
  have hH' : Set.range (U'.left.fromSpecResidueField t ≫ U'.hom).base ⊆ Set.range iΛ.base :=
    range_residuePoint_subset S U'.hom t iΛ ⟨_, rfl⟩
  let : Algebra Λ (U'.left.residueField t) := chartResidueAlgebra iΛ U' t hH'
  rw [isVersalAt_iff_liftsAtResiduePoint_chart iΛ U' t (𝒳.val.p ⋙ Over.post B.inclusion) x hx'
    (algebraMap_chartResidueAlgebra iΛ U' t hH')]
  refine liftsAtResiduePoint_of_isSmallExtension (k := U'.left.residueField t) B S hS 𝒳.val.p
    𝒳.isFiberedInGroupoids iΛ U' x hx' _ (fun {A A'} f hf => ?_)
  exact liftsAlong_of_isVersalAt_of_specializes (k := U'.left.residueField t) B S hS 𝒳 hΔ hRS hlim
    iΛ hΛ hR₀ x hx u₀ hu₀ hversal (U'.left.fromSpecResidueField t)
    (by convert htw; exact Scheme.fromSpecResidueField_apply _ _) f hf

/-- **Stacks 0G2K.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in
groupoids over the big fppf site of `S` whose diagonal is representable by algebraic spaces,
which satisfies (RS*) and which is limit preserving. Let `x` be an object of `𝒳` over a scheme
`U` locally of finite type over `S`, and let `u ⤳ u₀` be a specialization of points of `U` with
`u₀` of finite type. If `x` is versal at `u₀`, then `x` is versal at `u`.

The source asks `U` to be of finite type over `S` and `u` to be a finite type point; neither is
used. -/
@[stacks 0G2K]
public theorem isVersalAt_of_specializes [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (x : 𝒳.val.obj) [LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom]
    (u u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) (hspec : u ⤳ u₀)
    (hversal : IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl) :
    IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u x rfl := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) :=
    inferInstanceAs (LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
  -- shrink to an affine open `Spec R₀ ⊆ U` over an affine open `Spec Λ ⊆ S`
  obtain ⟨D, w₀, hw₀, -⟩ := exists_chartedData B S hS p x (p.obj x).left.2 u₀ hu₀
  obtain ⟨obj, ρ, hρ⟩ := exists_restrictedLift B S hS p x D.mem D.immersion hp
  let iΛ := D.chart.immersion
  have hΛ : B.Contains (Spec (.of D.chart.ring)) :=
    contains_of_isOpenImmersion B iΛ inferInstance hS
  have hxa : p.obj obj.1 = siteObject B S hS D.mem
      (Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring)) ≫ iΛ) := by
    refine obj.2.trans (eq_siteObject_of_post B S hS D.mem _ _ ?_)
    change Over.mk (restrictedSiteAlgebra B S hS p x D.mem D.immersion).toScheme = _
    rw [toScheme_restrictedSiteAlgebra, ← D.factorization]
    rfl
  let U' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring)) ≫ iΛ)
  have hx' : (p ⋙ Over.post B.inclusion).obj obj.1 = U' := congrArg (Over.post B.inclusion).obj hxa
  have hρ' : schemeMap (p ⋙ Over.post B.inclusion) hx' rfl ρ = D.immersion := hρ
  have hrange : ∀ t : Spec (CommRingCat.of D.ring),
      (B.inclusion.map (p.obj x).hom).base (D.immersion.base t) ∈ Set.range iΛ.base := fun t =>
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring))).base t,
      congrArg (fun m : Spec (CommRingCat.of D.ring) ⟶ S => m.base t) D.factorization⟩
  have hH : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField
          (D.immersion.base t) ≫ ((p ⋙ Over.post B.inclusion).obj x).hom).base ⊆
        Set.range iΛ.base := fun t =>
    range_residuePoint_subset S _ _ iΛ (hrange t)
  have hH' : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range (U'.left.fromSpecResidueField t ≫ U'.hom).base ⊆ Set.range iΛ.base := fun t =>
    range_residuePoint_subset S U'.hom t iΛ ⟨_, rfl⟩
  have hiff : ∀ t : Spec (CommRingCat.of D.ring),
      IsVersalAt U' (p ⋙ Over.post B.inclusion) t obj.1 hx' ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion)
          (D.immersion.base t) x rfl := fun t =>
    isVersalAt_iff_restrict B S hS p hp iΛ rfl hx' ρ D.immersion D.isOpenImmersion hρ' t
      (hH t) (hH' t)
  -- the point `u` lies in the affine open, and specializes to `w₀` there
  obtain ⟨t, rfl⟩ : u ∈ Set.range D.immersion.base :=
    hspec.mem_open D.immersion.isOpenEmbedding.isOpen_range ⟨w₀, hw₀⟩
  have htw : t ⤳ w₀ := by
    rwa [← D.immersion.isOpenEmbedding.isInducing.specializes_iff, hw₀]
  have hw₀ft : AlgebraicGeometry.IsFiniteTypePoint w₀ :=
    isFiniteTypePoint_of_isOpenImmersion D.immersion w₀ (by rwa [hw₀])
  have hversal' : IsVersalAt U' (p ⋙ Over.post B.inclusion) w₀ obj.1 hx' := by
    rwa [hiff w₀, hw₀]
  rw [← hiff t]
  exact isVersalAt_of_specializes_chart B S hS 𝒳 hΔ hRS hlim iΛ hΛ D.mem obj.1 hxa w₀ hw₀ft
    hversal' t htw

end Deformation.Artin
