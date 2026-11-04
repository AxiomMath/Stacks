module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Examples.Geometric.Schemes
public import StacksFrontier.Deformation.RimSchlessinger.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Rim-Schlessinger condition for flat families of schemes

A morphism of `𝒞_Λ` whose underlying algebra map is surjective has nilpotent kernel, because
the kernel is a proper ideal of an Artinian local ring. So the induced map of spectra is a
thickening of finite order, the other leg of a cospan is an affine morphism, and the spectrum
of the fibre product of the cospan is the pushout of the two spectra along that thickening,
which is simultaneously cartesian.

These are the ingredients of condition (RS) for the category of flat families of schemes over
`𝒞_Λ`, which is proved as `Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection` in
`StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessingerSquares`: the glued scheme over
the spectrum of the fibre product, with its two cartesian restrictions, is a fibre product of
flat families lying over the fibre product of the bases.

## Main definitions

* `Deformation.Examples.IsFlatGluing`: the two unformalized clauses about gluing flat schemes
  across a pushout along a finite-order thickening and an affine morphism.

## Main results

* `Deformation.Examples.isFiniteOrderThickening_baseSpecMap`: a surjection in `𝒞_Λ` induces a
  finite-order thickening of spectra.
* `Deformation.Examples.isPushout_baseSpecMap_of_surjective`: the spectrum of the fibre product
  of a cospan whose second leg is surjective is the pushout of the two spectra.
* `Deformation.Examples.isPullback_baseSpecMap_of_surjective`: that pushout square is
  simultaneously cartesian.
* `Deformation.Examples.isAffineHom_pushout_inl_of_isFiniteOrderThickening`: the map into the
  pushout from the ambient scheme of a finite-order thickening is affine.
* `Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening`: clause (2) of
  [Stacks Project, Tag 07RX] for a finite-order thickening.

## Implementation notes

The fibre product is the concrete one of `Deformation.ArtinianLocalAlgCat`, the algebra of
compatible pairs; its two projections are the ordinary projections, so the square of
commutative rings is the standard pullback cone and the pushout of spectra is
[Stacks Project, Tag 0ET0].  Cartesianness is the third assertion of
[Stacks Project, Tag 07RT] for a thickening of finite order, transported from Mathlib's
canonical pushout along the comparison isomorphism.

`Deformation.Examples.IsFlatGluing` states two clauses of [Stacks Project, Tag 07RV] and
[Stacks Project, Tag 07RX] for arbitrary schemes and with no reference to the base category:
that the two restrictions of a glued flat scheme are the schemes it was glued from, and that a
flat scheme over the pushout is the pushout of its own two restrictions.  Nothing here assumes
it: `Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection` uses the gluing clauses
`Stacks.Pushout.isPullback_of_isPushout_glued` and
`Stacks.Pushout.isPushout_restrictions_of_flat` instead.  The existence of the glued family is
the first assertion of Tag 07RT for a thickening of finite order, and its flatness over the
spectrum of the fibre product is clause (2) of Tag 07RX, through the situation of
`AlgebraicGeometry.ThickeningAffinePushoutSituation`.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Examples

open Deformation.ArtinianLocalAlgCat Stacks.Thickenings
open Stacks.Thickenings

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The kernel of a morphism of `𝒞_Λ` is nilpotent: it is a proper ideal of an Artinian local
ring, hence contained in the maximal ideal, which is nilpotent. -/
theorem exists_ker_pow_eq_bot {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) :
    ∃ n : ℕ, RingHom.ker f.hom.toRingHom ^ (n + 1) = ⊥ := by
  have : IsNoetherianRing A.carrier := inferInstance
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A.carrier).mp
    A.isArtinianRing
  have hne : RingHom.ker f.hom.toRingHom ≠ ⊤ := by
    intro h
    have h1 : (1 : A.carrier) ∈ RingHom.ker f.hom.toRingHom := by rw [h]; trivial
    have h2 : (1 : B.carrier) = 0 := by
      simpa using RingHom.mem_ker.mp h1
    exact one_ne_zero h2
  refine ⟨n, le_bot_iff.mp (le_trans
    (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hne) (n + 1)) ?_)⟩
  rw [pow_succ, hn]
  simp

/-- A surjection in `𝒞_Λ` induces a thickening of finite order on spectra. -/
theorem isFiniteOrderThickening_baseSpecMap {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    IsFiniteOrderThickening (baseSpecMap f) := by
  obtain ⟨n, hn⟩ := exists_ker_pow_eq_bot f
  have hci : IsClosedImmersion (baseSpecMap f) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.hom.toRingHom) hf
  refine ⟨hci, n, ?_⟩
  have := hci
  exact (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine (baseSpecMap f) (n + 1)).mpr
    (Stacks.Smooth.ker_specMap_appTop_pow_eq_bot (CommRingCat.ofHom f.hom.toRingHom) hn)

variable {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The concrete fibre product of a cospan of `𝒞_Λ` whose second leg is surjective is a fibre
product of the underlying commutative rings. -/
theorem isPullback_commRingCat_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h₂ : Function.Surjective f₂.hom) :
    IsPullback
      (CommRingCat.ofHom (pullbackFst_of_surjective f₁ f₂ (Or.inr h₂)).hom.toRingHom)
      (CommRingCat.ofHom (pullbackSnd_of_surjective f₁ f₂ (Or.inr h₂)).hom.toRingHom)
      (CommRingCat.ofHom f₁.hom.toRingHom)
      (CommRingCat.ofHom f₂.hom.toRingHom) := by
  simp only [pullbackFst_of_surjective_hom, pullbackSnd_of_surjective_hom]
  exact IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom f₁.hom.toRingHom) (CommRingCat.ofHom f₂.hom.toRingHom))

/-- **The geometric reduction step in the proof of [Stacks Project, Tag 0DY8].**  For a cospan
of `𝒞_Λ` whose second leg is surjective, the spectrum of the fibre product is the pushout of
the two spectra along the finite-order thickening cut out by that surjection. -/
theorem isPushout_baseSpecMap_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h₂ : Function.Surjective f₂.hom) :
    IsPushout (baseSpecMap f₂) (baseSpecMap f₁)
      (baseSpecMap (pullbackSnd_of_surjective f₁ f₂ (Or.inr h₂)))
      (baseSpecMap (pullbackFst_of_surjective f₁ f₂ (Or.inr h₂))) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (isPullback_commRingCat_of_surjective f₁ f₂ h₂) h₂

/-- The pushout square of spectra of a cospan of `𝒞_Λ` whose second leg is surjective is
simultaneously cartesian; this is the third assertion of [Stacks Project, Tag 07RT] for the
finite-order thickening cut out by the surjection. -/
theorem isPullback_baseSpecMap_of_surjective (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h₂ : Function.Surjective f₂.hom) :
    IsPullback (baseSpecMap f₂) (baseSpecMap f₁)
      (baseSpecMap (pullbackSnd_of_surjective f₁ f₂ (Or.inr h₂)))
      (baseSpecMap (pullbackFst_of_surjective f₁ f₂ (Or.inr h₂))) := by
  have hi : IsFiniteOrderThickening (baseSpecMap f₂) :=
    isFiniteOrderThickening_baseSpecMap f₂ h₂
  have hpo := isPushout_baseSpecMap_of_surjective f₁ f₂ h₂
  have : HasPushout (baseSpecMap f₂) (baseSpecMap f₁) := hpo.hasPushout
  have hpb := Stacks.Pushout.isPullback_pushout_of_isFiniteOrderThickening_of_isAffineHom
    (baseSpecMap f₂) (baseSpecMap f₁) hi
  exact hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hpo.isoPushout.symm
    (by simp) (by simp) (by simp [hpo.inl_isoPushout_inv])
    (by simp [hpo.inr_isoPushout_inv])

/-! ### Flatness of a scheme glued across a pushout -/

/-- **The map into the pushout from the ambient scheme of a finite-order thickening is affine.**
Over an affine open of the pushout, the preimage in the ambient scheme is a finite-order
thickening of the preimage in the source, and the latter is affine because it is also the
preimage of an affine open along the affine leg. -/
theorem isAffineHom_pushout_inl_of_isFiniteOrderThickening {X X' Y : Scheme.{v}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsFiniteOrderThickening i) [IsAffineHom f]
    [HasPushout i f] : IsAffineHom (pushout.inl i f) := by
  have : IsClosedImmersion (pushout.inr i f) :=
    (Stacks.Pushout.pushout_inr_isThickening_of_isFiniteOrderThickening i f hi).1
  refine ⟨fun U hU => ?_⟩
  have hUY : IsAffineOpen (pushout.inr i f ⁻¹ᵁ U) :=
    IsAffineHom.isAffine_preimage U hU
  have hpre : i ⁻¹ᵁ (pushout.inl i f ⁻¹ᵁ U) = f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      pushout.condition (f := i) (g := f)]
  have : IsAffine (i ⁻¹ᵁ (pushout.inl i f ⁻¹ᵁ U)).toScheme := by
    rw [hpre]
    exact hUY.preimage f
  exact isAffine_of_isFiniteOrderThickening (hi.morphismRestrict _)

/-- The canonical pushout along a finite-order thickening and an affine morphism, as a situation
of `AlgebraicGeometry.ThickeningAffinePushoutSituation`: the sections hypothesis is the fourth
assertion of [Stacks Project, Tag 07RT] for a thickening of finite order. -/
def thickeningAffinePushoutSituation {X X' Y : Scheme.{v}} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsFiniteOrderThickening i) [IsAffineHom f] [HasPushout i f] :
    AlgebraicGeometry.ThickeningAffinePushoutSituation.{v} where
  X := X
  X' := X'
  Y := Y
  Y' := pushout i f
  i := i
  f := f
  inX' := pushout.inl i f
  inY := pushout.inr i f
  isClosedImmersion_i := hi.1
  isAffineHom_inX' := isAffineHom_pushout_inl_of_isFiniteOrderThickening i f hi
  isAffineHom_inY :=
    have : IsClosedImmersion (pushout.inr i f) :=
      (Stacks.Pushout.pushout_inr_isThickening_of_isFiniteOrderThickening i f hi).1
    inferInstance
  isPushout := IsPushout.of_hasPushout _ _
  sections_isPullback :=
    Stacks.Pushout.pushout_structureSheaf_isPullback_of_isFiniteOrderThickening i f hi

/-- **Clause (2) of [Stacks Project, Tag 07RX] for a finite-order thickening.**  The scheme
glued from a compatible pair of flat schemes over the two pieces of a pushout along a
finite-order thickening and an affine morphism is flat over that pushout. -/
@[sga "7 VI 4.3" "more general"]
theorem flat_pushoutDesc_of_isFiniteOrderThickening {S S₁ S₂ Y Y₁ Y₂ : Scheme.{v}}
    {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} (hj₂ : IsFiniteOrderThickening j₂) [IsAffineHom j₁]
    (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂)
    (hy₁ : Flat y₁) (hy₂ : Flat y₂) [HasPushout j₂ j₁] [HasPushout g₂ g₁]
    (w : g₂ ≫ y₂ ≫ pushout.inl j₂ j₁ = g₁ ≫ y₁ ≫ pushout.inr j₂ j₁) :
    Flat ((IsPushout.of_hasPushout g₂ g₁).desc (y₂ ≫ pushout.inl j₂ j₁)
      (y₁ ≫ pushout.inr j₂ j₁) w) := by
  have hg₂ : IsFiniteOrderThickening g₂ := isFiniteOrderThickening_of_isPullback h₂ hj₂
  have hg₁ : IsAffineHom g₁ := MorphismProperty.of_isPullback h₁.flip inferInstance
  have := hg₁
  let T := thickeningAffinePushoutSituation g₂ g₁ hg₂
  let Tr : (thickeningAffinePushoutSituation j₂ j₁ hj₂).Triple :=
    { T := T
      toX' := y₂
      toY := y₁
      toX := y
      isPullback_i := h₂
      isPullback_f := h₁ }
  exact Tr.flat_induced_iff.mpr ⟨hy₁, hy₂⟩

/-! ### Condition (RS) for flat families of schemes -/

/-- **The two clauses of [Stacks Project, Tag 07RV] and [Stacks Project, Tag 07RX] that this
development does not have.**  Let `T` be the pushout of a finite-order thickening `j₂` and an
affine morphism `j₁`, let a compatible pair of flat schemes over the two pieces be given, and
let `Z` be the pushout of their common restriction, with `z : Z ⟶ T` the induced morphism.  The
first clause is that the two restrictions of `z` are the given pair, which is the clause
`F ∘ G ≅ 𝟭` of Tag 07RV; the second is that a flat scheme over `T` is the pushout of its own
two restrictions, which is the equivalence clause of Tag 07RX.  Flatness of `z`, which is
clause (2) of Tag 07RX, is *not* assumed: it is
`Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening`. -/
structure IsFlatGluing : Prop where
  /-- The two restrictions of the glued scheme are the schemes it was glued from. -/
  restrict : ∀ {S S₁ S₂ T : Scheme.{v}} {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {b₂ : S₂ ⟶ T}
    {b₁ : S₁ ⟶ T}, IsFiniteOrderThickening j₂ → IsAffineHom j₁ → IsPushout j₂ j₁ b₂ b₁ →
    ∀ {Y Y₁ Y₂ Z : Scheme.{v}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
      {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z}, Flat y₁ → Flat y₂ →
      IsPullback g₁ y y₁ j₁ → IsPullback g₂ y y₂ j₂ → IsPushout g₂ g₁ c₂ c₁ →
      c₁ ≫ z = y₁ ≫ b₁ → c₂ ≫ z = y₂ ≫ b₂ →
      IsPullback c₁ y₁ z b₁ ∧ IsPullback c₂ y₂ z b₂
  /-- A flat scheme over the pushout is the pushout of its two restrictions. -/
  descend : ∀ {S S₁ S₂ T : Scheme.{v}} {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {b₂ : S₂ ⟶ T} {b₁ : S₁ ⟶ T},
    IsFiniteOrderThickening j₂ → IsAffineHom j₁ → IsPushout j₂ j₁ b₂ b₁ →
    ∀ {W W₀ W₁ W₂ : Scheme.{v}} {w : W ⟶ T} {w₀ : W₀ ⟶ S} {w₁ : W₁ ⟶ S₁} {w₂ : W₂ ⟶ S₂}
      {e₁ : W₁ ⟶ W} {e₂ : W₂ ⟶ W} {d₁ : W₀ ⟶ W₁} {d₂ : W₀ ⟶ W₂}, Flat w →
      IsPullback e₁ w₁ w b₁ → IsPullback e₂ w₂ w b₂ →
      IsPullback d₁ w₀ w₁ j₁ → IsPullback d₂ w₀ w₂ j₂ → IsPushout d₂ d₁ e₂ e₁

end Deformation.Examples

end
