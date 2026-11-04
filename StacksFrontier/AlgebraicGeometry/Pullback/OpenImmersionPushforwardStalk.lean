module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Fiber
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# The stalk of the direct image along an open immersion

For an open subscheme `j : U ⟶ X` of a scheme `X` and a point `x` of `X` this file identifies

`(j_* 𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})`,

where `U_x` is the inverse image of `U` under the canonical morphism
`f_x : Spec 𝒪_{X, x} ⟶ X`, as an isomorphism of `𝒪_{X, x}`-algebras.  The point `x` is *not*
assumed to lie in `U`; the interesting case is `x ∉ U`.

The hypothesis is that `U ⊓ W` be quasi-compact for an affine open `W ∋ x` — that is, that `j` be
quasi-compact near `x`.  It cannot be dropped: both sides are built from the sections of `𝒪_X`
over the opens `U ⊓ V` for `V` a neighbourhood of `x`, the left side as a filtered colimit and
the right side as a limit over a cover, and a filtered colimit commutes with the limits of the
sheaf condition only when those are finite.

## The two halves

Both sides are the *same* localization of `Γ(X, U ⊓ W)`, at the prime of `x` in the affine
`W = Spec Γ(X, W)`:

* `AlgebraicGeometry.Scheme.Hom.isLocalization_pushforwardStalk_of_isCompact` of
  `Morphisms/Affine/Fiber.lean` does the left side.  It is the statement that the stalk of a
  direct image is the localization of the sections over the preimage, proved there for a
  quasi-compact quasi-separated preimage through the Qcqs lemma; an open immersion is not an
  affine morphism, which is why the affine form of that statement does not apply.
* `AlgebraicGeometry.isLocalization_sections_preimage_fromSpecStalk` below does the right side.
  It is degree-zero flat base change along `f_x`, which is flat by
  `AlgebraicGeometry.flat_fromSpecStalk`: Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` makes the sections
  square a pushout of rings, and a pushout along a localization is a localization.  The same
  computation is performed inside the proof of `AlgebraicGeometry.span_eq_top_of_isCompact` of
  `OneDimensionalLocal/QuasiCompactOpen.lean` and is exposed here.

The two localizations are of `Γ(U.toScheme, j ⁻¹ᵁ W)` and of `Γ(X, U ⊓ W)` respectively, which
are the same ring presented through the two descriptions of that open, so the comparison
isomorphism is `IsLocalization.ringEquivOfRingEquiv` along the restriction isomorphism between
them.

## Main results

* `AlgebraicGeometry.isLocalization_sections_preimage_fromSpecStalk`: the sections of `𝒪` over
  the inverse image of a quasi-compact quasi-separated open `V ⊆ W` under
  `Spec 𝒪_{X, x} ⟶ X`, for `W` an affine open containing `x`, are the localization of
  `Γ(X, V)` at the prime of `x`.
* `AlgebraicGeometry.exists_ringEquiv_pushforwardStalk_ι`: the identification
  `(j_* 𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})`, as a ring isomorphism carrying the canonical map from
  `𝒪_{X, x}` on the left to the one on the right.
* `AlgebraicGeometry.exists_ringEquiv_pushforwardStalk_ι_of_quasiCompact`: the same with the
  affine open and the quasi-compactness hypothesis replaced by quasi-compactness of `j`, which
  is how the hypothesis is usually met.

This module carries no Stacks tag: the identification is not the content of a numbered result of
the Stacks Project, which uses it inside the proofs of [Stacks, Tag 0EBN] and
[Stacks, Tag 0EBR], and no tag was invented for it.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH), flat base change.
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW), the Qcqs lemma.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- Mapping a submonoid along `φ` and then along a ring isomorphism `j` is mapping it along `ψ`,
when `j ∘ φ = ψ`. -/
private theorem Submonoid.map_ringEquiv_map_eq_map {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] (M : Submonoid R) (j : A ≃+* B) {φ : R →+* A} {ψ : R →+* B}
    (h : ∀ r, j (φ r) = ψ r) : (M.map φ).map j.toMonoidHom = M.map ψ := by
  ext z
  simp only [Submonoid.mem_map]
  constructor
  · rintro ⟨-, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, (h b).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, h b⟩

/-- Two maps out of a localization `S` of `R`, into localizations `P` of `A` and `Q` of `B`,
are intertwined by `IsLocalization.ringEquivOfRingEquiv` along a ring isomorphism `j : A ≃+* B`
as soon as they are compatible with maps `φ : R →+* A` and `ψ : R →+* B` with `j ∘ φ = ψ`. -/
private theorem IsLocalization.ringEquivOfRingEquiv_comp_eq {R A B S P Q : Type*} [CommRing R]
    [CommRing A] [CommRing B] [CommRing S] [CommRing P] [CommRing Q] [Algebra R S] [Algebra A P]
    [Algebra B Q] (M : Submonoid R) [IsLocalization M S] {MA : Submonoid A} {MB : Submonoid B}
    [IsLocalization MA P] [IsLocalization MB Q] (j : A ≃+* B) (hj : MA.map j.toMonoidHom = MB)
    {φ : R →+* A} {ψ : R →+* B} (h : ∀ r, j (φ r) = ψ r) {f : S →+* P} {g : S →+* Q}
    (hf : f.comp (algebraMap R S) = (algebraMap A P).comp φ)
    (hg : g.comp (algebraMap R S) = (algebraMap B Q).comp ψ) :
    (ringEquivOfRingEquiv P Q j hj : P →+* Q).comp f = g := by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun a ↦ ?_)
  have hfa := RingHom.congr_fun hf a
  have hga := RingHom.congr_fun hg a
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at hfa hga ⊢
  rw [hfa, hga, ringEquivOfRingEquiv_eq, h]

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Opens pulled back along `Spec 𝒪_{X, x} ⟶ X` -/

/-- **An open neighbourhood of `x` pulls back to the whole of `Spec 𝒪_{X, x}`.** Every point in
the image of `Spec 𝒪_{X, x} ⟶ X` specializes to `x` ([Stacks, Tag 01J7], Mathlib's
`AlgebraicGeometry.Scheme.range_fromSpecStalk`), and an open set containing a specialization
contains the point it specializes from. -/
lemma preimage_fromSpecStalk_eq_top (x : X) {W : X.Opens} (hx : x ∈ W) :
    X.fromSpecStalk x ⁻¹ᵁ W = ⊤ := by
  refine eq_top_iff.mpr fun p _ ↦ ?_
  have h : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  show X.fromSpecStalk x p ∈ W
  exact Specializes.mem_open h W.2 hx

/-- An open of `X` meeting an open neighbourhood of `x` has the same inverse image under
`Spec 𝒪_{X, x} ⟶ X` as the intersection does. -/
lemma preimage_fromSpecStalk_inf (x : X) (U : X.Opens) {W : X.Opens} (hx : x ∈ W) :
    X.fromSpecStalk x ⁻¹ᵁ U = X.fromSpecStalk x ⁻¹ᵁ (U ⊓ W) := by
  rw [Scheme.Hom.preimage_inf, preimage_fromSpecStalk_eq_top x hx, inf_top_eq]

/-- **On sections, `Spec 𝒪_{X, x} ⟶ X` is the germ map read through `Γ(Spec -, ⊤) ≅ -`.**
This is Mathlib's `AlgebraicGeometry.Scheme.fromSpecStalk_app` packaged as a statement about
`AlgebraicGeometry.Scheme.Hom.appLE`, with the two restrictions that appear in the two
statements composed into one. -/
lemma appLE_fromSpecStalk (x : X) {W : X.Opens} (hx : x ∈ W)
    (T : (Spec (X.presheaf.stalk x)).Opens) (h : T ≤ X.fromSpecStalk x ⁻¹ᵁ W) :
    (X.fromSpecStalk x).appLE W T h =
      X.presheaf.germ W x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE (le_top (a := T))).op := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx, Category.assoc, Category.assoc,
    ← Functor.map_comp, Scheme.presheaf_map_eq_homOfLE
      (Z := Spec (X.presheaf.stalk x)) _ (le_top (a := T))]

/-- The same at `T = ⊤`, where the restriction map is the identity. -/
lemma appLE_fromSpecStalk_top (x : X) {W : X.Opens} (hx : x ∈ W)
    (h : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ X.fromSpecStalk x ⁻¹ᵁ W) :
    (X.fromSpecStalk x).appLE W ⊤ h =
      X.presheaf.germ W x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [appLE_fromSpecStalk x hx ⊤ h, show (homOfLE
      (le_top (a := (⊤ : (Spec (X.presheaf.stalk x)).Opens)))).op = 𝟙 _ from
    Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]

/-- `AlgebraicGeometry.Scheme.Hom.appLE` along an identity morphism is a restriction map. -/
lemma appLE_id {Z : Scheme.{u}} {A B : Z.Opens} (h : B ≤ (𝟙 Z) ⁻¹ᵁ A) (h' : B ≤ A) :
    Scheme.Hom.appLE (𝟙 Z) A B h = Z.presheaf.map (homOfLE h').op := by
  have h1 : Scheme.Hom.appLE (𝟙 Z) A B h = Z.presheaf.map (homOfLE h).op :=
    Category.id_comp _
  rw [h1]
  exact Scheme.presheaf_map_eq_homOfLE (Z := Z) _ h'

/-! ### Flat base change for sections along `Spec 𝒪_{X, x} ⟶ X` -/

/-- **The global sections of `Spec 𝒪_{X, x}` are the local ring**, as a `Γ(X, W)`-algebra for an
affine open `W` containing `x`: the germ map is the localization at the prime of `x`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`) and
`AlgebraicGeometry.Scheme.ΓSpecIso` transports it. -/
theorem isLocalization_sections_top_fromSpecStalk (x : X) {W : X.Opens} (hW : IsAffineOpen W)
    (hx : x ∈ W) (h : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ X.fromSpecStalk x ⁻¹ᵁ W) :
    letI : Algebra Γ(X, W) Γ(Spec (X.presheaf.stalk x), ⊤) :=
      ((X.fromSpecStalk x).appLE W ⊤ h).hom.toAlgebra
    IsLocalization (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      Γ(Spec (X.presheaf.stalk x), ⊤) := by
  let : Algebra Γ(X, W) Γ(Spec (X.presheaf.stalk x), ⊤) :=
    ((X.fromSpecStalk x).appLE W ⊤ h).hom.toAlgebra
  let : Algebra Γ(X, W) (X.presheaf.stalk x) := (X.presheaf.germ W x hx).hom.toAlgebra
  have : IsLocalization (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hW.isLocalization_stalk ⟨x, hx⟩
  refine IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso (X.presheaf.stalk x)).symm.commRingCatIsoToRingEquiv) ?_)
  intro r
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    appLE_fromSpecStalk_top x hx h]
  rfl

/-- **Degree-zero flat base change along `Spec 𝒪_{X, x} ⟶ X`.**

Let `W` be an affine open of `X` containing `x` and let `V ⊆ W` be quasi-compact and
quasi-separated.  Then the sections of `𝒪` over the inverse image of `V` under
`f_x : Spec 𝒪_{X, x} ⟶ X` are the localization of `Γ(X, V)` at the prime of `x`.

The morphism `f_x` is flat (`AlgebraicGeometry.flat_fromSpecStalk`), so Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` — [Stacks, Tag 02KH]
part (2) in degree zero — makes

```
  Γ(X, W) ⟶ Γ(X, V)
     ↓          ↓
  𝒪_{X,x} ⟶ Γ(Spec 𝒪_{X,x}, f_x⁻¹ V)
```

a pushout of commutative rings.  Its left column is the localization at the prime of `x` by
`isLocalization_sections_top_fromSpecStalk`, and a pushout along a localization is a
localization (`Algebra.isLocalization_iff_isPushout`).

The open `T` of `Spec 𝒪_{X, x}` is kept abstract, constrained only to equal `f_x⁻¹ V`, so that
this applies to it presented in another way. -/
theorem isLocalization_sections_preimage_fromSpecStalk (x : X) {W : X.Opens}
    (hW : IsAffineOpen W) (hx : x ∈ W) {V : X.Opens} (hVW : V ≤ W)
    (hc : IsCompact (V : Set X)) (hq : IsQuasiSeparated (V : Set X))
    {T : (Spec (X.presheaf.stalk x)).Opens} (hT : T = X.fromSpecStalk x ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Spec (X.presheaf.stalk x), T) :=
      ((X.fromSpecStalk x).appLE V T hT.le).hom.toAlgebra
    IsLocalization (Submonoid.map (X.presheaf.map (homOfLE hVW).op).hom
        (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      Γ(Spec (X.presheaf.stalk x), T) := by
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have hWtop : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ X.fromSpecStalk x ⁻¹ᵁ W :=
    (preimage_fromSpecStalk_eq_top x hx).ge
  have H : IsPullback (X.fromSpecStalk x) (𝟙 (Spec (X.presheaf.stalk x))) (𝟙 X)
      (X.fromSpecStalk x) := IsPullback.of_vert_isIso ⟨by simp⟩
  have hUSX : V ≤ (𝟙 X) ⁻¹ᵁ W := by simpa using hVW
  have hUY : T = X.fromSpecStalk x ⁻¹ᵁ V ⊓ (𝟙 (Spec (X.presheaf.stalk x))) ⁻¹ᵁ ⊤ := by
    simpa using hT
  have hiso : IsIso (pushoutSection H hWtop hUSX hUY) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hWtop hUSX hUY hW
      (isAffineOpen_top _) hc hq
  let algWS : Algebra Γ(X, W) Γ(Spec (X.presheaf.stalk x), ⊤) :=
    ((X.fromSpecStalk x).appLE W ⊤ hWtop).hom.toAlgebra
  let algWV : Algebra Γ(X, W) Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom.toAlgebra
  let algVT : Algebra Γ(X, V) Γ(Spec (X.presheaf.stalk x), T) :=
    ((X.fromSpecStalk x).appLE V T hT.le).hom.toAlgebra
  let algST : Algebra Γ(Spec (X.presheaf.stalk x), ⊤) Γ(Spec (X.presheaf.stalk x), T) :=
    (Scheme.Hom.appLE (𝟙 (Spec (X.presheaf.stalk x))) ⊤ T (by simp)).hom.toAlgebra
  let algWT : Algebra Γ(X, W) Γ(Spec (X.presheaf.stalk x), T) :=
    ((X.fromSpecStalk x).appLE W ⊤ hWtop ≫
      Scheme.Hom.appLE (𝟙 (Spec (X.presheaf.stalk x))) ⊤ T (by simp)).hom.toAlgebra
  have esq : (X.fromSpecStalk x).appLE W ⊤ hWtop ≫
      Scheme.Hom.appLE (𝟙 (Spec (X.presheaf.stalk x))) ⊤ T (by simp) =
      X.presheaf.map (homOfLE hVW).op ≫ (X.fromSpecStalk x).appLE V T hT.le := by
    rw [appLE_id _ (le_top (a := T)), Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have tow1 : IsScalarTower Γ(X, W) Γ(Spec (X.presheaf.stalk x), ⊤)
      Γ(Spec (X.presheaf.stalk x), T) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp]
  have tow2 : IsScalarTower Γ(X, W) Γ(X, V) Γ(Spec (X.presheaf.stalk x), T) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    rw [esq, CommRingCat.hom_comp]
  have := isLocalization_sections_top_fromSpecStalk x hW hx hWtop
  have key : Algebra.IsPushout Γ(X, W) Γ(Spec (X.presheaf.stalk x), ⊤) Γ(X, V)
      Γ(Spec (X.presheaf.stalk x), T) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact ((isIso_pushoutSection_iff H hWtop hUSX hUY).mp hiso).flip
  exact (Algebra.isLocalization_iff_isPushout (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    Γ(Spec (X.presheaf.stalk x), ⊤)).mpr key.symm

/-- Restricting sections from `W` to `U ⊓ W` factors through `U.ι.app W`, transported along
`U ⊓ W = U.ι ''ᵁ (U.ι ⁻¹ᵁ W)`. -/
private theorem Scheme.Opens.map_eqToHom_ι_app_apply (U W : X.Opens)
    (h : U ⊓ W = U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) (b : Γ(X, W)) :
    (X.presheaf.map (eqToHom h).op).hom ((U.ι.app W).hom b) =
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom b := by
  have hbridge : U.ι.app W ≫ X.presheaf.map (eqToHom h).op =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op := by
    rw [Scheme.Opens.ι_app]
    show X.presheaf.map _ ≫ X.presheaf.map _ = _
    rw [← Functor.map_comp]
    exact Scheme.presheaf_map_eq_homOfLE _ inf_le_right
  rw [← hbridge]
  rfl

/-! ### The identification -/

/-- **`(j_* 𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` for an open subscheme `j : U ⟶ X`.**

Here `U_x` is the inverse image of `U` under the canonical `f_x : Spec 𝒪_{X, x} ⟶ X`; the point
`x` need not lie in `U`.  The isomorphism is one of `𝒪_{X, x}`-algebras: the second clause says
that it carries the stalk at `x` of the comorphism of `j`, which is the canonical map
`𝒪_{X, x} ⟶ (j_* 𝒪_U)_x`, to the canonical map `𝒪_{X, x} ⟶ Γ(U_x, 𝒪_{U_x})`, namely
`Γ(Spec -, ⊤) ≅ -` followed by restriction.

The hypothesis is that `U ⊓ W` be quasi-compact for some affine open `W ∋ x`.  Both sides are
then the same localization of `Γ(X, U ⊓ W)` at the prime of `x` in `W`; see the module
docstring. -/
theorem exists_ringEquiv_pushforwardStalk_ι (U : X.Opens) (x : X) {W : X.Opens}
    (hW : IsAffineOpen W) (hx : x ∈ W)
    (hc : IsCompact ((U.ι ⁻¹ᵁ W : (U.toScheme).Opens) : Set U.toScheme)) :
    ∃ e : U.ι.pushforwardStalk x ≃+* Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U),
      ∀ r : X.presheaf.stalk x, e (U.ι.pushforwardStalkMap x r) =
        ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map
            (homOfLE (le_top (a := X.fromSpecStalk x ⁻¹ᵁ U))).op).hom r := by
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = U ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hset : (U.ι.base '' ((U.ι ⁻¹ᵁ W : (U.toScheme).Opens) : Set U.toScheme)) =
      ((U ⊓ W : X.Opens) : Set X) := by rw [← himg]; rfl
  -- the two quasi-compactness and quasi-separatedness statements
  have hcX : IsCompact ((U ⊓ W : X.Opens) : Set X) := by
    rw [← hset]; exact hc.image U.ι.continuous
  have hqX : IsQuasiSeparated ((U ⊓ W : X.Opens) : Set X) :=
    hW.isQuasiSeparated.of_subset fun _ hz ↦ hz.2
  have hq : IsQuasiSeparated ((U.ι ⁻¹ᵁ W : (U.toScheme).Opens) : Set U.toScheme) :=
    U.ι.isOpenEmbedding.isQuasiSeparated_iff.mpr (by rwa [hset])
  -- the left side: the stalk of the direct image
  let alg₁ : Algebra Γ(U.toScheme, U.ι ⁻¹ᵁ W) (U.ι.pushforwardStalk x) :=
    (U.ι.pushforwardGerm W x hx).hom.toAlgebra
  have hloc₁ : IsLocalization (Submonoid.map (U.ι.app W).hom
      (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (U.ι.pushforwardStalk x) :=
    U.ι.isLocalization_pushforwardStalk_of_isCompact hW hx hc hq
  -- the right side: the sections over the inverse image
  have hT : X.fromSpecStalk x ⁻¹ᵁ U = X.fromSpecStalk x ⁻¹ᵁ (U ⊓ W) :=
    preimage_fromSpecStalk_inf x U hx
  let alg₂ : Algebra Γ(X, U ⊓ W) Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) :=
    ((X.fromSpecStalk x).appLE (U ⊓ W) (X.fromSpecStalk x ⁻¹ᵁ U) hT.le).hom.toAlgebra
  have hloc₂ : IsLocalization (Submonoid.map
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom
      (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) :=
    isLocalization_sections_preimage_fromSpecStalk x hW hx inf_le_right hcX hqX hT
  -- the restriction isomorphism between the two presentations of `Γ(X, U ⊓ W)`
  let jiso : Γ(U.toScheme, U.ι ⁻¹ᵁ W) ≅ Γ(X, U ⊓ W) :=
    X.presheaf.mapIso (eqToIso himg.symm).op
  have hhom : ∀ b : Γ(X, W), jiso.hom.hom ((U.ι.app W).hom b) =
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom b :=
    Scheme.Opens.map_eqToHom_ι_app_apply U W himg.symm
  have hmap := Submonoid.map_ringEquiv_map_eq_map
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl jiso.commRingCatIsoToRingEquiv hhom
  let : Algebra Γ(X, W) (X.presheaf.stalk x) := (X.presheaf.germ W x hx).hom.toAlgebra
  have : IsLocalization (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hW.isLocalization_stalk ⟨x, hx⟩
  have key := IsLocalization.ringEquivOfRingEquiv_comp_eq
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl jiso.commRingCatIsoToRingEquiv hmap hhom
    (f := (U.ι.pushforwardStalkMap x).hom)
    (g := ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫ (Spec (X.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top (a := X.fromSpecStalk x ⁻¹ᵁ U))).op).hom)
    (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        ← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkFunctor_map_germ W x hx U.ι.c))
    (by rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE,
      appLE_fromSpecStalk x hx (X.fromSpecStalk x ⁻¹ᵁ U)])
  exact ⟨IsLocalization.ringEquivOfRingEquiv (U.ι.pushforwardStalk x)
    Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U)
    jiso.commRingCatIsoToRingEquiv hmap, fun r ↦ RingHom.congr_fun key r⟩

/-- **`(j_* 𝒪_U)_x ≅ Γ(U_x, 𝒪_{U_x})` for a quasi-compact open subscheme.** This is
`exists_ringEquiv_pushforwardStalk_ι` with the affine open neighbourhood of `x` chosen from the
basis of affine opens, its quasi-compactness hypothesis being exactly quasi-compactness of `j`
there. -/
theorem exists_ringEquiv_pushforwardStalk_ι_of_quasiCompact (U : X.Opens) [QuasiCompact U.ι]
    (x : X) :
    ∃ e : U.ι.pushforwardStalk x ≃+* Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U),
      ∀ r : X.presheaf.stalk x, e (U.ι.pushforwardStalkMap x r) =
        ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map
            (homOfLE (le_top (a := X.fromSpecStalk x ⁻¹ᵁ U))).op).hom r := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact exists_ringEquiv_pushforwardStalk_ι U x hW hx
    (U.ι.isCompact_preimage hW.isCompact)

end AlgebraicGeometry

end
