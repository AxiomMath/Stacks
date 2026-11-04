module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Pushout.Affine
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushouts along a thickening and an affine morphism: the affine local model

Let `i : X ⟶ X'` be a thickening of schemes and `f : X ⟶ Y` an affine morphism.
[Stacks Project, Tag 07RT] asserts that the pushout `Y' = Y ⨿_X X'` exists in the category of
schemes, that `Y ⟶ Y'` is again a thickening, that the pushout square is simultaneously
cartesian, and that `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`.

This file proves these assertions when `X'` and `Y` are affine, the last one on global sections,
with pushout `Spec (Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤))`; all but the second need only that `i` is a
closed immersion.

## Main definitions

* `Stacks.Thickenings.IsThickening.homeomorph` is the homeomorphism of underlying spaces induced
  by a thickening, and `Stacks.Thickenings.IsThickening.opensCongr` the resulting order
  isomorphism of lattices of opens.
* `Stacks.Pushout.affinePushoutRing` is the fibre product of rings
  `Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤)`, with projections
  `Stacks.Pushout.affinePushoutRingToTarget` and `Stacks.Pushout.affinePushoutRingToAmbient`.

## Main results

* `Stacks.Thickenings.IsThickening.isHomeomorph`: a thickening is a homeomorphism on points.
* `Stacks.Thickenings.IsThickening.morphismRestrict` and
  `Stacks.Thickenings.IsThickening.iff_of_iSup_eq_top`: being a thickening is Zariski-local at the
  ambient scheme, packaged as the instance
  `Stacks.Thickenings.isThickening_isZariskiLocalAtTarget`.
* `Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop`: for a thickening of affine
  schemes, every global section cutting out the closed subscheme is nilpotent.
* `Stacks.Pushout.isPushout_of_isClosedImmersion_of_isAffine` and
  `Stacks.Pushout.isPullback_of_isClosedImmersion_of_isAffine`: for `i` a closed immersion and
  `X'`, `Y` affine, the square `X → X'`, `X → Y`, `X' → Spec (Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤))`,
  `Y → Spec (Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤))` is both cocartesian and cartesian.
* `Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine` and
  `Stacks.Pushout.isAffine_pushout_of_isClosedImmersion_of_isAffine`: the pushout therefore
  exists and is affine.
* `Stacks.Pushout.isThickening_pushout_inr_of_isAffine`: if moreover `i` is a thickening, the map
  `Y ⟶ Y ⨿_X X'` is a thickening.
* `Stacks.Pushout.isPullback_pushout_of_isAffine`: Mathlib's pushout square is also cartesian.
* `Stacks.Pushout.isPullback_appTop_pushout_of_isAffine`: on global sections the pushout square
  is cartesian, that is, `Γ(Y ⨿_X X', ⊤) = Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤)`.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-! ### The topology of a thickening -/

/-- A thickening is a homeomorphism on underlying spaces. -/
theorem IsThickening.isHomeomorph {i : X ⟶ X'} (hi : IsThickening i) : IsHomeomorph i.base :=
  have := hi.1
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, hi.2⟩

/-- The homeomorphism between the underlying spaces of the two schemes of a thickening. -/
noncomputable def IsThickening.homeomorph {i : X ⟶ X'} (hi : IsThickening i) :
    (X : Type u) ≃ₜ (X' : Type u) :=
  IsHomeomorph.homeomorph _ hi.isHomeomorph

/-- The order isomorphism between the opens of `X` and the opens of `X'` induced by a thickening
`i : X ⟶ X'`. Its inverse is taking preimages along `i`. -/
noncomputable def IsThickening.opensCongr {i : X ⟶ X'} (hi : IsThickening i) :
    X.Opens ≃o X'.Opens :=
  hi.homeomorph.opensCongr

/-- The open of `X'` matching an open `U` of `X` has preimage `U`. -/
theorem IsThickening.preimage_opensCongr {i : X ⟶ X'} (hi : IsThickening i) (U : X.Opens) :
    i ⁻¹ᵁ hi.opensCongr U = U :=
  hi.opensCongr.symm_apply_apply U

/-- The open of `X'` matching the preimage of an open `U` of `X'` is `U` itself. -/
theorem IsThickening.opensCongr_preimage {i : X ⟶ X'} (hi : IsThickening i) (U : X'.Opens) :
    hi.opensCongr (i ⁻¹ᵁ U) = U :=
  hi.opensCongr.apply_symm_apply U

/-- A thickening restricts to a thickening over any open of the ambient scheme. -/
theorem IsThickening.morphismRestrict {i : X ⟶ X'} (hi : IsThickening i) (V' : X'.Opens) :
    IsThickening (i ∣_ V') :=
  have : IsClosedImmersion i := hi.1
  have : Surjective i := ⟨hi.2⟩
  ⟨IsZariskiLocalAtTarget.restrict ‹IsClosedImmersion i› V',
    (IsZariskiLocalAtTarget.restrict ‹Surjective i› V').surj⟩

/-- If `i` restricts to a thickening over each member of a family of opens covering the ambient
scheme, then `i` is a thickening. -/
theorem IsThickening.of_iSup_eq_top {i : X ⟶ X'} {ι : Type*} (V' : ι → X'.Opens)
    (hV' : iSup V' = ⊤) (H : ∀ j, IsThickening (i ∣_ V' j)) : IsThickening i :=
  ⟨IsZariskiLocalAtTarget.of_iSup_eq_top V' hV' fun j ↦ (H j).1,
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Surjective) V' hV' fun j ↦ ⟨(H j).2⟩).surj⟩

/-- Being a thickening may be tested on any family of opens covering the ambient scheme. -/
theorem IsThickening.iff_of_iSup_eq_top {i : X ⟶ X'} {ι : Type*} (V' : ι → X'.Opens)
    (hV' : iSup V' = ⊤) : IsThickening i ↔ ∀ j, IsThickening (i ∣_ V' j) :=
  ⟨fun hi _j ↦ hi.morphismRestrict _, IsThickening.of_iSup_eq_top V' hV'⟩

/-- Being a thickening is a Zariski-local-at-target morphism property. -/
instance isThickening_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsThickening : MorphismProperty Scheme.{u}) :=
  IsZariskiLocalAtTarget.mk' (fun _i V' hi ↦ hi.morphismRestrict V')
    (fun _i _ι V' hV' H ↦ IsThickening.of_iSup_eq_top V' hV' H)

/-- For a thickening `i : X ⟶ X'` with `X'` affine, every global section of `X'` that dies in `X`
is nilpotent. -/
@[sga "1 IX 1.7" "special case"]
theorem IsThickening.isNilpotent_of_mem_ker_appTop [IsAffine X'] {i : X ⟶ X'}
    (hi : IsThickening i) {a : Γ(X', (⊤ : X'.Opens))} (ha : a ∈ RingHom.ker i.appTop.hom) :
    IsNilpotent a := by
  have := hi.1
  obtain ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have hs : Function.Surjective (Spec.map i.appTop).base := by
    have h : Function.Surjective (X.isoSpec.hom ≫ Spec.map i.appTop).base := by
      rw [Scheme.isoSpec_hom_naturality i]
      exact X'.isoSpec.hom.homeomorph.surjective.comp hi.2
    exact Function.Surjective.of_comp (g := X.isoSpec.hom.base) h
  have hrange : Set.range (PrimeSpectrum.comap i.appTop.hom) = Set.univ :=
    Set.range_eq_univ.mpr hs
  rw [range_comap_of_surjective _ _ hsurj, PrimeSpectrum.zeroLocus_eq_univ_iff] at hrange
  exact mem_nilradical.mp (hrange ha)

end Stacks.Thickenings

namespace Stacks.Pushout

variable {X X' Y : Scheme.{u}}

/-! ### The fibre product of rings of global sections -/

/-- The fibre product of rings `Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤)` attached to a pair of morphisms
`i : X ⟶ X'` and `f : X ⟶ Y`. -/
noncomputable abbrev affinePushoutRing (i : X ⟶ X') (f : X ⟶ Y) : CommRingCat.{u} :=
  CommRingCat.of (RingHom.pullback f.appTop.hom i.appTop.hom)

/-- The projection of `Stacks.Pushout.affinePushoutRing` to the global sections of the target `Y`
of the affine morphism. -/
noncomputable abbrev affinePushoutRingToTarget (i : X ⟶ X') (f : X ⟶ Y) :
    affinePushoutRing i f ⟶ Γ(Y, (⊤ : Y.Opens)) :=
  CommRingCat.ofHom (RingHom.pullbackFst f.appTop.hom i.appTop.hom)

/-- The projection of `Stacks.Pushout.affinePushoutRing` to the global sections of the ambient
scheme `X'` of the closed immersion. -/
noncomputable abbrev affinePushoutRingToAmbient (i : X ⟶ X') (f : X ⟶ Y) :
    affinePushoutRing i f ⟶ Γ(X', (⊤ : X'.Opens)) :=
  CommRingCat.ofHom (RingHom.pullbackSnd f.appTop.hom i.appTop.hom)

/-- The defining cartesian square of `Stacks.Pushout.affinePushoutRing`. -/
theorem isPullback_affinePushoutRing (i : X ⟶ X') (f : X ⟶ Y) :
    IsPullback (affinePushoutRingToTarget i f) (affinePushoutRingToAmbient i f) f.appTop
      i.appTop := by
  simpa using isPullback_ofHom_pullback f.appTop.hom i.appTop.hom

/-- If every element of the kernel of `p : A' →+* A` is nilpotent, so is every element of the
kernel of the projection `B ×_A A' ⟶ B`. -/
theorem isNilpotent_of_mem_ker_pullbackFst {A A' B : Type u} [CommRing A] [CommRing A']
    [CommRing B] (q : B →+* A) (p : A' →+* A) (hp : ∀ a ∈ RingHom.ker p, IsNilpotent a)
    {x : q.pullback p} (hx : x ∈ RingHom.ker (q.pullbackFst p)) : IsNilpotent x := by
  have hx1 : (x : B × A').1 = 0 := hx
  have hmem := x.2
  simp only [RingHom.mem_eqLocus, RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst,
    RingHom.coe_snd] at hmem
  have hx2 : (x : B × A').2 ∈ RingHom.ker p := by
    rw [RingHom.mem_ker, ← hmem, hx1, map_zero]
  obtain ⟨n, hn⟩ := hp _ hx2
  refine ⟨n + 1, Subtype.ext ?_⟩
  rw [Subring.coe_pow]
  exact Prod.ext (by simp [hx1]) (by simp [pow_succ, hn])

/-! ### The affine local model -/

/-- Let `i : X ⟶ X'` be a closed immersion and `f : X ⟶ Y` any morphism, with `X'` and `Y` affine.
Then `Spec (Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤))` is the pushout of `Y ← X → X'`. -/
theorem isPushout_of_isClosedImmersion_of_isAffine (i : X ⟶ X') (f : X ⟶ Y)
    [IsClosedImmersion i] [IsAffine X'] [IsAffine Y] :
    IsPushout i f (X'.isoSpec.hom ≫ Spec.map (affinePushoutRingToAmbient i f))
      (Y.isoSpec.hom ≫ Spec.map (affinePushoutRingToTarget i f)) :=
  have ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  (isPushout_spec_map_of_isPullback_of_surjective i.appTop f.appTop
      (affinePushoutRingToTarget i f) (affinePushoutRingToAmbient i f)
      (isPullback_affinePushoutRing i f) hsurj).of_iso'
    X.isoSpec X'.isoSpec Y.isoSpec (Iso.refl _) (Scheme.isoSpec_hom_naturality i)
    (Scheme.isoSpec_hom_naturality f) (by simp) (by simp)

/-- The square of `Stacks.Pushout.isPushout_of_isClosedImmersion_of_isAffine` is also cartesian. -/
theorem isPullback_of_isClosedImmersion_of_isAffine (i : X ⟶ X') (f : X ⟶ Y)
    [IsClosedImmersion i] [IsAffine X'] [IsAffine Y] :
    IsPullback i f (X'.isoSpec.hom ≫ Spec.map (affinePushoutRingToAmbient i f))
      (Y.isoSpec.hom ≫ Spec.map (affinePushoutRingToTarget i f)) := by
  obtain ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have H := isPullback_specMap_pullback f.appTop.hom i.appTop.hom hsurj
  simp only [CommRingCat.ofHom_hom] at H
  exact H.of_iso' X.isoSpec X'.isoSpec Y.isoSpec (Iso.refl _) (Scheme.isoSpec_hom_naturality i)
    (Scheme.isoSpec_hom_naturality f) (by simp) (by simp)

/-- The pushout of a closed immersion `i : X ⟶ X'` and a morphism `f : X ⟶ Y` exists when `X'` and
`Y` are affine. -/
theorem hasPushout_of_isClosedImmersion_of_isAffine (i : X ⟶ X') (f : X ⟶ Y)
    [IsClosedImmersion i] [IsAffine X'] [IsAffine Y] : HasPushout i f :=
  (isPushout_of_isClosedImmersion_of_isAffine i f).hasPushout

/-- In the affine local model the pushout is again affine. -/
theorem isAffine_pushout_of_isClosedImmersion_of_isAffine (i : X ⟶ X') (f : X ⟶ Y)
    [IsClosedImmersion i] [IsAffine X'] [IsAffine Y] [HasPushout i f] :
    IsAffine (pushout i f) :=
  IsAffine.of_isIso (isPushout_of_isClosedImmersion_of_isAffine i f).isoPushout.inv

/-- For a thickening `i : X ⟶ X'` and a morphism `f : X ⟶ Y` with `X'` and `Y` affine, the map
`Y ⟶ Y ⨿_X X'` is a thickening. -/
theorem isThickening_pushout_inr_of_isAffine (i : X ⟶ X') (f : X ⟶ Y)
    (hi : Thickenings.IsThickening i) [IsAffine X'] [IsAffine Y] [HasPushout i f] :
    Thickenings.IsThickening (pushout.inr i f) := by
  have := hi.1
  obtain ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have H := isPushout_of_isClosedImmersion_of_isAffine i f
  have hfst : Function.Surjective (affinePushoutRingToTarget i f).hom :=
    RingHom.surjective_pullbackFst_of_surjective _ _ hsurj
  have : IsClosedImmersion (Spec.map (affinePushoutRingToTarget i f)) :=
    IsClosedImmersion.spec_of_surjective _ hfst
  have : Surjective (Spec.map (affinePushoutRingToTarget i f)) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ]
    show Set.range (PrimeSpectrum.comap (affinePushoutRingToTarget i f).hom) = Set.univ
    rw [range_comap_of_surjective _ _ hfst, PrimeSpectrum.zeroLocus_eq_univ_iff]
    exact fun a ha ↦ mem_nilradical.mpr (isNilpotent_of_mem_ker_pullbackFst _ _
      (fun _ hb ↦ hi.isNilpotent_of_mem_ker_appTop hb) ha)
  rw [← H.inr_isoPushout_hom]
  exact ⟨inferInstance,
    ((Y.isoSpec.hom ≫ Spec.map (affinePushoutRingToTarget i f)) ≫ H.isoPushout.hom).surjective⟩

/-- For a closed immersion `i : X ⟶ X'` and a morphism `f : X ⟶ Y` with `X'` and `Y` affine, the
pushout square is cartesian. -/
theorem isPullback_pushout_of_isAffine (i : X ⟶ X') (f : X ⟶ Y) [IsClosedImmersion i]
    [IsAffine X'] [IsAffine Y] [HasPushout i f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) := by
  have H := isPushout_of_isClosedImmersion_of_isAffine i f
  rw [← H.inl_isoPushout_hom, ← H.inr_isoPushout_hom]
  exact (isPullback_of_isClosedImmersion_of_isAffine i f).of_iso' (Iso.refl X) (Iso.refl X')
    (Iso.refl Y) H.isoPushout.symm (by simp) (by simp) (by simp) (by simp)

/-- For a closed immersion `i : X ⟶ X'` and a morphism `f : X ⟶ Y` with `X'` and `Y` affine, the
global sections of the pushout are the fibre product `Γ(Y, ⊤) ×_{Γ(X, ⊤)} Γ(X', ⊤)`. -/
theorem isPullback_appTop_pushout_of_isAffine (i : X ⟶ X') (f : X ⟶ Y) [IsClosedImmersion i]
    [IsAffine X'] [IsAffine Y] [HasPushout i f] :
    IsPullback (pushout.inr i f).appTop (pushout.inl i f).appTop f.appTop i.appTop := by
  have H := isPushout_of_isClosedImmersion_of_isAffine i f
  refine (isPullback_affinePushoutRing i f).of_iso
    ((Scheme.ΓSpecIso (affinePushoutRing i f)).symm ≪≫
      (Scheme.Γ.mapIso H.isoPushout.op).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  all_goals
    change _ ≫ 𝟙 _ = ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop H.isoPushout.inv) ≫ _
    rw [Category.comp_id, Category.assoc, ← Scheme.Hom.comp_appTop]
    first | rw [H.inr_isoPushout_inv] | rw [H.inl_isoPushout_inv]
    rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.isoSpec, asIso_hom,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end Stacks.Pushout

end
