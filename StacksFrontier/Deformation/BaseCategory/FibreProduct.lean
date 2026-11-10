module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic

/-!
# Fibre products in the category of Artinian local algebras

The ring-theoretic fibre product `A₁ ×_A A₂` of two morphisms of `𝒞_Λ` is always local, and it
carries a canonical map to the fixed residue field `k`. Three things are needed to make it an
object of `𝒞_Λ`: that it is Artinian, that its maximal ideal is the kernel of that canonical map,
and that the canonical map is surjective. This file establishes the first two unconditionally in
the two cases of interest, identifies the maximal ideal, and shows that the remaining datum — a
`Λ`-algebra identification of the residue field with `k` compatible with the canonical map — exists
exactly when the canonical map is surjective.

When one of the two morphisms is surjective the canonical map is surjective and the fibre product
is Artinian, so the fibre product exists in `𝒞_Λ` and its underlying ring is the ring of compatible
pairs.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.pullbackToResidueField`: the canonical map from the fibre
  product to `k`.
* `Deformation.ArtinianLocalAlgCat.IsConcretePullback`: the assertion that the ring of compatible
  pairs, with its canonical residue map and the two ordinary projections, is a pullback in `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.pullbackObj_of_surjective`,
  `Deformation.ArtinianLocalAlgCat.pullbackFst_of_surjective`,
  `Deformation.ArtinianLocalAlgCat.pullbackSnd_of_surjective`: the object and projections obtained
  when one of the two morphisms is surjective.

## Main results

* `Deformation.ArtinianLocalAlgCat.pullback_isArtinianRing_of_surjective` and
  `Deformation.ArtinianLocalAlgCat.pullback_isArtinianRing_of_isClassical`: the fibre product is
  Artinian when one morphism is surjective, and in the classical case.
* `Deformation.ArtinianLocalAlgCat.maximalIdeal_pullback`: its maximal ideal is the set of pairs
  lying in the two maximal ideals.
* `Deformation.ArtinianLocalAlgCat.ker_pullbackToResidueField`: that ideal is the kernel of the
  canonical map to `k`.
* `Deformation.ArtinianLocalAlgCat.residueField_embeds_pullback`: the residue field of the fibre
  product embeds in `k` compatibly with the canonical map.
* `Deformation.ArtinianLocalAlgCat.pullback_has_fixed_residueField_iff`: the identification with
  `k` exists exactly when the canonical map is surjective.
* `Deformation.ArtinianLocalAlgCat.isConcretePullback_of_pullbackToResidueField_surjective`:
  Artinianness together with surjectivity of the canonical map makes the ring of compatible pairs a
  pullback in `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.hasPullback_of_surjective`: if one of the two morphisms is
  surjective, the ring of compatible pairs is a pullback in `𝒞_Λ`, so the pullback exists.

## References

* [Stacks Project, Tag 06GH](https://stacks.math.columbia.edu/tag/06GH)
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The canonical map from the ring-theoretic fibre product to the common residue field. -/
noncomputable def pullbackToResidueField (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    AlgHom.pullback f₁.hom f₂.hom →+* k :=
  A.residueEquiv.toRingEquiv.toRingHom.comp
    ((residue A).comp
      (f₁.hom.toRingHom.comp (AlgHom.pullbackFst f₁.hom f₂.hom).toRingHom))

/-- The canonical map to `k` is computed through the residue field of the first factor. -/
private theorem pullbackToResidueField_apply_fst (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (x : AlgHom.pullback f₁.hom f₂.hom) :
    pullbackToResidueField f₁ f₂ x = A₁.residueEquiv (residue A₁ x.1.1) :=
  f₁.residue_comm x.1.1

/-- The canonical map to `k` is computed through the residue field of the second factor. -/
private theorem pullbackToResidueField_apply_snd (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (x : AlgHom.pullback f₁.hom f₂.hom) :
    pullbackToResidueField f₁ f₂ x = A₂.residueEquiv (residue A₂ x.1.2) := by
  rw [← f₂.residue_comm, ← show f₁.hom x.1.1 = f₂.hom x.1.2 from x.property]
  rfl

private theorem isArtinian_of_surjective_residue {R B : Type*}
    [CommRing R] [IsLocalRing R] [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    (h : Function.Surjective ((residue B).comp (algebraMap R B))) : IsArtinian R B := by
  have hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField B)) := by
    intro y
    obtain ⟨x, hx⟩ := h y
    exact ⟨residue R x, (ResidueField.algebraMap_residue x).trans hx⟩
  have hlen : Module.length (ResidueField R) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres, Module.length_eq_one]
  have hfinite : IsFiniteLength R B := by
    rw [← Module.length_ne_top_iff, IsLocalRing.length_restrictScalars R B B, hlen, mul_one]
    exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength B).mp inferInstance)
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2

/-- If one of the two morphisms is surjective then the canonical map from the fibre product
to `k` is surjective. -/
theorem pullbackToResidueField_surjective_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    Function.Surjective (pullbackToResidueField f₁ f₂) := by
  intro y
  rcases h with h₁ | h₂
  · obtain ⟨a₂, ha₂⟩ := residue_surjective (A₂.residueEquiv.symm y)
    obtain ⟨a₁, ha₁⟩ := h₁ (f₂.hom a₂)
    refine ⟨⟨(a₁, a₂), ha₁⟩, ?_⟩
    rw [pullbackToResidueField_apply_snd]
    change A₂.residueEquiv (residue A₂ a₂) = y
    rw [ha₂, A₂.residueEquiv.apply_symm_apply]
  · obtain ⟨a₁, ha₁⟩ := residue_surjective (A₁.residueEquiv.symm y)
    obtain ⟨a₂, ha₂⟩ := h₂ (f₁.hom a₁)
    refine ⟨⟨(a₁, a₂), ha₂.symm⟩, ?_⟩
    rw [pullbackToResidueField_apply_fst]
    change A₁.residueEquiv (residue A₁ a₁) = y
    rw [ha₁, A₁.residueEquiv.apply_symm_apply]

/-- If either morphism in `𝒞_Λ` is surjective, its ring-theoretic fibre product is Artinian. -/
theorem pullback_isArtinianRing_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    IsArtinianRing (AlgHom.pullback f₁.hom f₂.hom) := by
  let R := AlgHom.pullback f₁.hom f₂.hom
  let : IsLocalRing R := AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  have hp : Function.Surjective (pullbackToResidueField f₁ f₂) :=
    pullbackToResidueField_surjective_of_surjective f₁ f₂ h
  let : Algebra R A₁ := (AlgHom.pullbackFst f₁.hom f₂.hom).toRingHom.toAlgebra
  let : Algebra R A₂ := (AlgHom.pullbackSnd f₁.hom f₂.hom).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R A₁) :=
    RingHom.isLocalHom_pullbackFst f₁.hom.toRingHom f₂.hom.toRingHom
  let : IsLocalHom (algebraMap R A₂) :=
    RingHom.isLocalHom_pullbackSnd f₁.hom.toRingHom f₂.hom.toRingHom
  have : IsArtinian R A₁ := isArtinian_of_surjective_residue (by
    intro y
    obtain ⟨x, hx⟩ := hp (A₁.residueEquiv y)
    exact ⟨x, A₁.residueEquiv.injective
      ((pullbackToResidueField_apply_fst f₁ f₂ x).symm.trans hx)⟩)
  have : IsArtinian R A₂ := isArtinian_of_surjective_residue (by
    intro y
    obtain ⟨x, hx⟩ := hp (A₂.residueEquiv y)
    exact ⟨x, A₂.residueEquiv.injective
      ((pullbackToResidueField_apply_snd f₁ f₂ x).symm.trans hx)⟩)
  have : IsArtinian R (A₁ × A₂) := isArtinian_prod
  let i : R →ₗ[R] A₁ × A₂ :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact isArtinian_of_injective i Subtype.val_injective

/-- An object of `𝒞_Λ` has finite length over a Noetherian base over which `k` is module-finite. -/
@[sga "3 VIIB 1.2.6" "special case"]
private theorem isFiniteLength_of_moduleFinite (Λ : Type u) (k : Type w) [CommRing Λ]
    [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (B : ArtinianLocalAlgCat.{u, v, w} Λ k) : IsFiniteLength Λ B := by
  let old : Module Λ B := inferInstance
  let comp : Module Λ B := Module.compHom B (algebraMap Λ B)
  have hcomp : @IsFiniteLength Λ _ B _ comp := by
    rw [← Module.length_ne_top_iff,
      ← finrank_residueImageField_mul_length_eq_length Λ k B B B.residueEquiv]
    have hlen : Module.length B B ≠ ⊤ :=
      (@Module.length_ne_top_iff B B _ _ _).mpr
        ((isArtinianRing_iff_isFiniteLength B).mp inferInstance)
    rw [← ENat.natCast_toNat hlen, ← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  let f : @LinearMap Λ Λ _ _ (RingHom.id Λ) B B _ _ old comp :=
    @LinearMap.mk Λ Λ _ _ (RingHom.id Λ) B B _ _ old comp (AddHom.id B) (by
      intro r x
      change old.toSMul.smul r x = comp.toSMul.smul r x
      exact Algebra.smul_def r x)
  exact @IsFiniteLength.of_injective Λ _ B B _ old _ comp f hcomp fun _ _ h ↦ by
    simpa [f] using h

/-- Over a Noetherian base with `k` module-finite over it, the fibre product of two morphisms of
`𝒞_Λ` is Artinian. -/
theorem pullback_isArtinianRing_of_moduleFinite [IsNoetherianRing Λ] [Module.Finite Λ k]
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    IsArtinianRing (AlgHom.pullback f₁.hom f₂.hom) := by
  have hprod : IsFiniteLength Λ (A₁ × A₂) := by
    rw [← Module.length_ne_top_iff, Module.length_prod, ne_eq, ENat.add_eq_top, not_or]
    exact ⟨Module.length_ne_top_iff.mpr (isFiniteLength_of_moduleFinite Λ k A₁),
      Module.length_ne_top_iff.mpr (isFiniteLength_of_moduleFinite Λ k A₂)⟩
  have hpull : IsFiniteLength Λ (AlgHom.pullback f₁.hom f₂.hom) :=
    hprod.of_injective (f := (AlgHom.pullback f₁.hom f₂.hom).val.toLinearMap)
      fun _ _ h ↦ Subtype.ext h
  exact isArtinian_of_tower Λ (isFiniteLength_iff_isNoetherian_isArtinian.mp hpull).2

/-- In the classical case, the ring-theoretic fibre product of two morphisms in `𝒞_Λ` is
Artinian. -/
theorem pullback_isArtinianRing_of_isClassical (hΛ : IsClassical Λ k)
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    IsArtinianRing (AlgHom.pullback f₁.hom f₂.hom) := by
  let _ : IsNoetherianRing Λ := hΛ.choose.isNoetherian
  let _ : IsLocalRing Λ := hΛ.choose.isLocal
  let _ : Module.Finite Λ k := Module.Finite.equiv hΛ.choose_spec.some.toLinearEquiv
  exact pullback_isArtinianRing_of_moduleFinite f₁ f₂

/-- The maximal ideal of the fibre product consists exactly of pairs belonging to the two maximal
ideals. -/
theorem maximalIdeal_pullback (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    letI : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
      AlgHom.isLocalRing_pullback f₁.hom f₂.hom
    maximalIdeal (AlgHom.pullback f₁.hom f₂.hom) =
      (Ideal.prod (maximalIdeal A₁) (maximalIdeal A₂)).comap
        (AlgHom.pullback f₁.hom f₂.hom).val.toRingHom := by
  let _ : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
    AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  ext x
  rw [mem_maximalIdeal]
  change (¬ IsUnit x) ↔ x.1.1 ∈ maximalIdeal A₁ ∧ x.1.2 ∈ maximalIdeal A₂
  rw [AlgHom.isUnit_pullback_mk_iff f₁.hom f₂.hom x.property]
  simp only [not_and_or, mem_maximalIdeal]
  have hx : f₁.hom x.1.1 = f₂.hom x.1.2 := x.property
  constructor
  · rintro (h | h)
    · refine ⟨h, fun h₂ ↦ h (isUnit_of_map_unit f₁.hom _ ?_)⟩
      rw [hx]
      exact h₂.map f₂.hom
    · refine ⟨fun h₁ ↦ h (isUnit_of_map_unit f₂.hom _ ?_), h⟩
      rw [← hx]
      exact h₁.map f₁.hom
  · exact fun h ↦ Or.inl h.1

/-- The componentwise maximal ideal of the fibre product is the kernel of its canonical map
to the common residue field. -/
theorem ker_pullbackToResidueField (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    (Ideal.prod (maximalIdeal A₁) (maximalIdeal A₂)).comap
        (AlgHom.pullback f₁.hom f₂.hom).val.toRingHom =
      RingHom.ker (pullbackToResidueField f₁ f₂) := by
  ext x
  change (x.1.1 ∈ maximalIdeal A₁ ∧ x.1.2 ∈ maximalIdeal A₂) ↔
    pullbackToResidueField f₁ f₂ x = 0
  rw [← residue_eq_zero_iff (R := A₁), ← residue_eq_zero_iff (R := A₂),
    pullbackToResidueField_apply_fst, map_eq_zero_iff _ A₁.residueEquiv.injective]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, (map_eq_zero_iff _ A₂.residueEquiv.injective).1 ?_⟩⟩
  rw [← pullbackToResidueField_apply_snd f₁ f₂ x, pullbackToResidueField_apply_fst, h, map_zero]

/-- The residue field of the fibre product embeds canonically in the common residue field. -/
theorem residueField_embeds_pullback (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    letI : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
      AlgHom.isLocalRing_pullback f₁.hom f₂.hom
    ∃ e : ResidueField (AlgHom.pullback f₁.hom f₂.hom) →+* k,
      Function.Injective e ∧
        e.comp (residue (AlgHom.pullback f₁.hom f₂.hom)) =
          pullbackToResidueField f₁ f₂ := by
  let _ : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
    AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  let p := pullbackToResidueField f₁ f₂
  have hpker : RingHom.ker p = maximalIdeal (AlgHom.pullback f₁.hom f₂.hom) := by
    rw [← ker_pullbackToResidueField f₁ f₂, ← maximalIdeal_pullback f₁ f₂]
  let _ : IsLocalHom p := ⟨by
    intro x hx
    by_contra hxu
    have hz : p x = 0 := by
      rw [← RingHom.mem_ker, hpker, mem_maximalIdeal]
      exact hxu
    rw [hz] at hx
    exact not_isUnit_zero hx⟩
  exact ⟨ResidueField.lift p, RingHom.injective _, ResidueField.lift_comp_residue p⟩

/-- The fibre product has residue field `k`, compatibly with its canonical map, exactly when that
map is surjective. -/
theorem pullback_has_fixed_residueField_iff (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) :
    letI : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
      AlgHom.isLocalRing_pullback f₁.hom f₂.hom
    (∃ e : ResidueField (AlgHom.pullback f₁.hom f₂.hom) ≃ₐ[Λ] k,
      e.toRingEquiv.toRingHom.comp (residue (AlgHom.pullback f₁.hom f₂.hom)) =
        pullbackToResidueField f₁ f₂) ↔
      Function.Surjective (pullbackToResidueField f₁ f₂) := by
  let _ : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
    AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  constructor
  · rintro ⟨e, he⟩ y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := residue_surjective z
    exact ⟨x, (DFunLike.congr_fun he x).symm⟩
  · intro hp
    obtain ⟨q, hqinj, hq⟩ := residueField_embeds_pullback f₁ f₂
    have hqsurj : Function.Surjective q := by
      intro y
      obtain ⟨x, hx⟩ := hp y
      exact ⟨residue (AlgHom.pullback f₁.hom f₂.hom) x,
        (DFunLike.congr_fun hq x).trans hx⟩
    let er : ResidueField (AlgHom.pullback f₁.hom f₂.hom) ≃+* k :=
      RingEquiv.ofBijective q ⟨hqinj, hqsurj⟩
    let e : ResidueField (AlgHom.pullback f₁.hom f₂.hom) ≃ₐ[Λ] k :=
      { er with
        commutes' := by
          intro r
          change q (algebraMap Λ (ResidueField (AlgHom.pullback f₁.hom f₂.hom)) r) = _
          rw [show algebraMap Λ (ResidueField (AlgHom.pullback f₁.hom f₂.hom)) r =
              residue (AlgHom.pullback f₁.hom f₂.hom)
                (algebraMap Λ (AlgHom.pullback f₁.hom f₂.hom) r) from rfl,
            show q (residue (AlgHom.pullback f₁.hom f₂.hom)
              (algebraMap Λ (AlgHom.pullback f₁.hom f₂.hom) r)) =
                pullbackToResidueField f₁ f₂
                  (algebraMap Λ (AlgHom.pullback f₁.hom f₂.hom) r) from
              DFunLike.congr_fun hq _]
          simp only [pullbackToResidueField, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
            AlgHom.coe_toRingHom, AlgHom.commutes]
          exact A.residueEquiv.commutes r }
    exact ⟨e, hq⟩

/-- The ring of compatible pairs, with its canonical residue map and the two ordinary
projections, is a pullback in `𝒞_Λ`. -/
def IsConcretePullback (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) : Prop :=
  let R := AlgHom.pullback f₁.hom f₂.hom
  letI : IsLocalRing R := AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  ∃ hArt : IsArtinianRing R,
    letI : IsArtinianRing R := hArt
    ∃ e : ResidueField R ≃ₐ[Λ] k,
      (∀ x : R, e (residue R x) = pullbackToResidueField f₁ f₂ x) ∧
      let P : ArtinianLocalAlgCat.{u, v, w} Λ k := { carrier := R, residueEquiv := e }
      ∃ (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂),
        p₁.hom = AlgHom.pullbackFst f₁.hom f₂.hom ∧
        p₂.hom = AlgHom.pullbackSnd f₁.hom f₂.hom ∧
        IsPullback p₁ p₂ f₁ f₂

namespace IsConcretePullback

variable {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}

/-- The object on the ring of compatible pairs. -/
noncomputable def obj (h : IsConcretePullback f₁ f₂) : ArtinianLocalAlgCat.{u, v, w} Λ k :=
  letI : IsLocalRing (AlgHom.pullback f₁.hom f₂.hom) :=
    AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  letI : IsArtinianRing (AlgHom.pullback f₁.hom f₂.hom) := h.choose
  { carrier := AlgHom.pullback f₁.hom f₂.hom, residueEquiv := h.choose_spec.choose }

/-- The underlying type is the algebraic pullback. -/
theorem obj_carrier (h : IsConcretePullback f₁ f₂) :
    h.obj.carrier = AlgHom.pullback f₁.hom f₂.hom := rfl

/-- The chosen residue-field identification induces the canonical map to `k`. -/
theorem residueEquiv_residue (h : IsConcretePullback f₁ f₂) (x : h.obj) :
    h.obj.residueEquiv (IsLocalRing.residue h.obj x) =
      pullbackToResidueField f₁ f₂ x :=
  h.choose_spec.choose_spec.1 x

/-- The first projection of the concrete pullback object. -/
noncomputable def fst (h : IsConcretePullback f₁ f₂) : h.obj ⟶ A₁ :=
  h.choose_spec.choose_spec.2.choose

/-- The second projection of the concrete pullback object. -/
noncomputable def snd (h : IsConcretePullback f₁ f₂) : h.obj ⟶ A₂ :=
  h.choose_spec.choose_spec.2.choose_spec.choose

/-- The first projection is the ordinary algebra projection. -/
@[simp]
theorem fst_hom (h : IsConcretePullback f₁ f₂) :
    h.fst.hom = AlgHom.pullbackFst f₁.hom f₂.hom :=
  h.choose_spec.choose_spec.2.choose_spec.choose_spec.1

/-- The second projection is the ordinary algebra projection. -/
@[simp]
theorem snd_hom (h : IsConcretePullback f₁ f₂) :
    h.snd.hom = AlgHom.pullbackSnd f₁.hom f₂.hom :=
  h.choose_spec.choose_spec.2.choose_spec.choose_spec.2.1

/-- The concrete object and its projections satisfy the pullback universal property. -/
theorem isPullback (h : IsConcretePullback f₁ f₂) : IsPullback h.fst h.snd f₁ f₂ :=
  h.choose_spec.choose_spec.2.choose_spec.choose_spec.2.2

end IsConcretePullback

/-- If the ring of compatible pairs is Artinian and its canonical map to `k` is surjective, then it
is, with the ordinary projections, a pullback in `𝒞_Λ`. -/
theorem isConcretePullback_of_pullbackToResidueField_surjective
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hArt : IsArtinianRing (AlgHom.pullback f₁.hom f₂.hom))
    (hp : Function.Surjective (pullbackToResidueField f₁ f₂)) :
    IsConcretePullback f₁ f₂ := by
  classical
  dsimp [IsConcretePullback]
  let R := AlgHom.pullback f₁.hom f₂.hom
  let _ : IsLocalRing R := AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  refine ⟨hArt, ?_⟩
  let _ : IsArtinianRing R := hArt
  obtain ⟨e, he⟩ := (pullback_has_fixed_residueField_iff f₁ f₂).2 hp
  refine ⟨e, fun x ↦ DFunLike.congr_fun he x, ?_⟩
  let P : ArtinianLocalAlgCat.{u, v, w} Λ k := { carrier := R, residueEquiv := e }
  let _ : IsLocalHom f₂.hom.toRingHom := f₂.isLocal
  let p₁ : P ⟶ A₁ :=
    { hom := AlgHom.pullbackFst f₁.hom f₂.hom
      isLocal := by
        change IsLocalHom (RingHom.pullbackFst f₁.hom.toRingHom f₂.hom.toRingHom)
        infer_instance
      residue_comm x :=
        (pullbackToResidueField_apply_fst f₁ f₂ x).symm.trans (DFunLike.congr_fun he x).symm }
  let _ : IsLocalHom f₁.hom.toRingHom := f₁.isLocal
  let p₂ : P ⟶ A₂ :=
    { hom := AlgHom.pullbackSnd f₁.hom f₂.hom
      isLocal := by
        change IsLocalHom (RingHom.pullbackSnd f₁.hom.toRingHom f₂.hom.toRingHom)
        infer_instance
      residue_comm x :=
        (pullbackToResidueField_apply_snd f₁ f₂ x).symm.trans (DFunLike.congr_fun he x).symm }
  have hcomm : p₁ ≫ f₁ = p₂ ≫ f₂ := by ext x; exact x.2
  let cone : PullbackCone f₁ f₂ := PullbackCone.mk p₁ p₂ hcomm
  have hlimit : IsLimit cone := by
    refine PullbackCone.IsLimit.mk hcomm ?_ ?_ ?_ ?_
    · intro s
      let g : s.pt →ₐ[Λ] R :=
        AlgHom.codRestrict (AlgHom.prod s.fst.hom s.snd.hom) R (by
          intro x
          change f₁.hom (s.fst.hom x) = f₂.hom (s.snd.hom x)
          exact congrArg (fun q : s.pt ⟶ A ↦ q.hom x) s.condition)
      exact
        { hom := g
          isLocal := ⟨fun x hunit ↦ s.fst.isLocal.map_nonunit x
            (hunit.map (AlgHom.pullbackFst f₁.hom f₂.hom))⟩
          residue_comm x := (p₁.residue_comm (g x)).symm.trans (s.fst.residue_comm x) }
    · intro s; ext x; rfl
    · intro s; ext x; rfl
    · intro s m hm₁ hm₂
      exact hom_ext (AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
        (congrArg (fun q : s.pt ⟶ A₁ ↦ q.hom x) hm₁) (congrArg (fun q : s.pt ⟶ A₂ ↦ q.hom x) hm₂)))
  exact ⟨p₁, p₂, rfl, rfl, IsPullback.of_isLimit hlimit⟩

/-- If either morphism is surjective, the ring of compatible pairs is a pullback in `𝒞_Λ`; in
particular the pullback exists. -/
@[stacks 06GH "surjective_fiber_product_in_clambda"]
theorem hasPullback_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    IsConcretePullback f₁ f₂ ∧ HasPullback f₁ f₂ :=
  have hConcrete : IsConcretePullback f₁ f₂ :=
    isConcretePullback_of_pullbackToResidueField_surjective f₁ f₂
      (pullback_isArtinianRing_of_surjective f₁ f₂ h)
      (pullbackToResidueField_surjective_of_surjective f₁ f₂ h)
  ⟨hConcrete, hConcrete.isPullback.hasPullback⟩

/-- The ring of compatible pairs, equipped as an object of `𝒞_Λ` when either map is
surjective. Its carrier is definitionally `AlgHom.pullback f₁.hom f₂.hom`. -/
noncomputable def pullbackObj_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    ArtinianLocalAlgCat.{u, v, w} Λ k :=
  ((hasPullback_of_surjective f₁ f₂ h).1).obj

/-- The canonical first projection of the object constructed under surjectivity. -/
noncomputable def pullbackFst_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    pullbackObj_of_surjective f₁ f₂ h ⟶ A₁ :=
  ((hasPullback_of_surjective f₁ f₂ h).1).fst

/-- The canonical second projection of the object constructed under surjectivity. -/
noncomputable def pullbackSnd_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom) :
    pullbackObj_of_surjective f₁ f₂ h ⟶ A₂ :=
  ((hasPullback_of_surjective f₁ f₂ h).1).snd

variable (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
  (h : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)

/-- The carrier of `pullbackObj_of_surjective` is the ring of compatible pairs. -/
theorem pullbackObj_of_surjective_carrier :
    (pullbackObj_of_surjective f₁ f₂ h).carrier = AlgHom.pullback f₁.hom f₂.hom := rfl

/-- The constructed residue-field identification agrees with the canonical map to `k`. -/
theorem pullbackObj_of_surjective_residueEquiv_residue
    (x : pullbackObj_of_surjective f₁ f₂ h) :
    (pullbackObj_of_surjective f₁ f₂ h).residueEquiv
        (IsLocalRing.residue (pullbackObj_of_surjective f₁ f₂ h) x) =
      pullbackToResidueField f₁ f₂ x :=
  ((hasPullback_of_surjective f₁ f₂ h).1).residueEquiv_residue x

/-- The constructed first projection is the usual projection on compatible pairs. -/
@[simp]
theorem pullbackFst_of_surjective_hom :
    (pullbackFst_of_surjective f₁ f₂ h).hom = AlgHom.pullbackFst f₁.hom f₂.hom :=
  ((hasPullback_of_surjective f₁ f₂ h).1).fst_hom

/-- The constructed second projection is the usual projection on compatible pairs. -/
@[simp]
theorem pullbackSnd_of_surjective_hom :
    (pullbackSnd_of_surjective f₁ f₂ h).hom = AlgHom.pullbackSnd f₁.hom f₂.hom :=
  ((hasPullback_of_surjective f₁ f₂ h).1).snd_hom

/-- The constructed object and projections form a categorical pullback. -/
theorem isPullback_of_surjective :
    IsPullback (pullbackFst_of_surjective f₁ f₂ h) (pullbackSnd_of_surjective f₁ f₂ h)
      f₁ f₂ :=
  ((hasPullback_of_surjective f₁ f₂ h).1).isPullback

end

end ArtinianLocalAlgCat

end Deformation

end
