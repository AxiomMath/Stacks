module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Pieces
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine chart of an immersion, and the conormal sheaf on it

Let `i : Z ⟶ X` be an immersion and `U ⊆ X` an affine open, and suppose the intersection
`Z ∩ U` is presented as `Spec (Γ(X, U) ⧸ I)` over `U ≅ Spec Γ(X, U)`, by an isomorphism
`e : Z ×_X U ≅ Spec (Γ(X, U) ⧸ I)` compatible with the two projections to `U`.  That is the
hypothesis of [Stacks, Tag 01R3] (2).  This file extracts from it everything the affine
computation of the conormal sheaf needs.

The content is that the hypothesis is much stronger than it looks.  It says that `i` restricted
over `U` is a *closed* immersion, and therefore — and this is what makes Tag 01R3 (2) reachable
without Tag 01R3 (1) — that `U` is contained in the canonical open `i.coborderRange` through
which Tag 01R2 factors `i` as a closed immersion.  So the conormal sheaf, which is defined as
the pullback of the ideal sheaf of `i.liftCoborder`, may be computed over `U` by the affine
base-change description of the pullback of sections, with no comparison of two different
closed-immersion factorizations.

## Main definitions

* `Stacks.Conormal.idealSheafKerObjIso` and `Stacks.Conormal.idealSheafSectionsIso`: the ideal
  sheaf of a closed immersion, as the sectionwise kernel of the map on functions; over any open
  its sections are `RingHom.ker (a.app W)`.
* `Stacks.Conormal.affineIdealPullbackIsoCotangent`: on an affine chart with affine preimage and
  surjective map on functions, the sections of the pullback of the ideal sheaf are `I/I²`.
* `Stacks.Conormal.cotangentComapIso`: `Ideal.Cotangent` transports along a ring isomorphism.
* `Stacks.Conormal.pushforwardCompSectionsIso`: the sections of a module pushforward along a
  composite through an open subscheme.
* `Stacks.Conormal.isQuasicoherent_idealSheaf`: the ideal sheaf of a closed immersion of schemes
  is quasi-coherent.

## Main results

* `Stacks.Conormal.le_coborderRange_of_isClosedImmersion_morphismRestrict`: an open over which
  an immersion restricts to a closed immersion is contained in the coborder of its range.  This
  is the geometric heart of the file.
* `Stacks.Conormal.isClosedImmersion_morphismRestrict_of_affineModel`,
  `Stacks.Conormal.isAffineOpen_preimage_of_affineModel` and
  `Stacks.Conormal.le_coborderRange_of_affineModel`: the three consequences of the affine model
  `(e, he)` — the restriction `i ∣_ U` is a closed immersion, `i ⁻¹ᵁ U` is affine, and
  `U ≤ i.coborderRange`.
* `Stacks.Conormal.exists_affineModel_of_isClosedImmersion_restrict`: conversely, an affine open
  over which the immersion restricts to a closed immersion carries an affine model.
  `Stacks.Conormal.exists_affineModel` is the case of a closed immersion, where every affine open
  qualifies.
* `Stacks.Conormal.exists_iso_appLE_quotientMk`: the map on sections
  `i.appLE U (i ⁻¹ᵁ U) : Γ(X, U) ⟶ Γ(Z, i ⁻¹ᵁ U)` is the quotient map
  `Γ(X, U) ⟶ Γ(X, U) ⧸ I` followed by an isomorphism.  This is the ring-level content of the
  affine model, and `Stacks.Conormal.ker_appLE_eq_of_affineModel` and
  `Stacks.Conormal.surjective_appLE_of_affineModel` are its two corollaries: the map is
  surjective with kernel exactly `I`.
* `Stacks.Conormal.ker_eq_comap_of_commSq` and `Stacks.Conormal.surjective_of_commSq`: kernels
  and surjectivity transport across a commuting square of rings whose vertical maps are
  isomorphisms.
* `Stacks.Conormal.affineConormalIsoCotangent`: the affine computation of the conormal sheaf
  asserted by [Stacks, Tag 01R3] (2).  `Stacks.Conormal.factoredAffineConormalIsoCotangent` is
  the same statement for an immersion presented with an arbitrary closed-immersion factorization
  through an open subscheme containing the chart.

## Implementation notes

`Stacks.Conormal.le_coborderRange_of_isClosedImmersion_morphismRestrict` is the only place where
anything topological happens.  `i.coborderRange` is the coborder `(closure (range i) \ range i)ᶜ`
of the range, and membership in it is, by `mem_coborder_iff_imp`, the implication
`x ∈ closure (range i) → x ∈ range i`.  For `x` in an open `U` over which `i` restricts to a
closed immersion, the range of `i ∣_ U` is closed in `U`, which by `isClosed_preimage_val` says
`U ∩ closure (U ∩ range i) ⊆ range i`; and `U` being open, `U ∩ closure (range i)` is contained
in `closure (U ∩ range i)` by `IsOpen.inter_closure`.  Those two together are the implication.

The ring-level statement is obtained by transporting the scheme-level square `(he)` from the
fibre product `Z ×_X U` to the open subscheme `i ⁻¹ᵁ U` along
`AlgebraicGeometry.pullbackRestrictIsoRestrict`, taking `Scheme.Hom.appTop` of it, and then
moving from `(i ∣_ U).appTop` to `i.appLE U (i ⁻¹ᵁ U)` along Mathlib's
`AlgebraicGeometry.arrowResLEAppIso`.  The two identifications of `Γ(Spec Γ(X, U), ⊤)` that
appear are `IsAffineOpen.isoSpec_hom_appTop` and `Scheme.ΓSpecIso_inv_naturality`, and nothing
else is needed: the comparison of the source rings is the *identity*, because the target of the
square `(he)` is identified with `Spec Γ(X, U)` by `hU.isoSpec` itself, which is the same
identification that `isoSpec_hom_appTop` unwinds.

The affine computation itself is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
(`Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U) ≅ Γ(f^*F, V)`) applied to the ideal sheaf, followed by
`Stacks.Conormal.surjectiveTensorEquivQuotSMul`, which turns the base change along a
surjection into a quotient: for `M = I` that quotient `I ⧸ I • ⊤` *is* `Ideal.Cotangent I`, by
definition, so the ring-theoretic step `I ⊗_R R/I = I/I²` costs nothing beyond that lemma.  The
base-change isomorphism is stated for `AlgebraicGeometry.Scheme.Modules.pullback`, which is
`RingedSpaceModuleAdjunction.modulePullback` of the same morphism of sheaves of rings **by
`rfl`**, so no comparison of the two pullbacks is needed.

Two propositional identifications of opens would otherwise have to be transported: `i ⁻¹ᵁ U`
against `i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U)`, and `i.coborderRange.ι ''ᵁ (…)` against
`U`.  Both are avoided by taking the factorization as a *hypothesis* `a ≫ C.ι = i` in
`factoredAffineConormalIsoCotangent` and substituting it: after the substitution the preimage
of `U` along the composite is the iterated preimage by `rfl`, and the map on functions factors
through `C.ι.app U` — an isomorphism, since `U ≤ C` — by `rfl` as well.  The remaining
comparison of the two ideals is then `RingHom.comap_ker`, and `Stacks.Conormal.cotangentComapIso`
carries the cotangent module across it.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction Opposite
open scoped Set.Notation TensorProduct ChangeOfRings

universe u

namespace Stacks.Conormal

/-! ### Kernels and surjectivity across a commuting square of rings -/

section CommSq

variable {A B A' B' : CommRingCat.{u}}

/-- **The kernel of a ring map is determined by a commuting square with invertible sides.**  If
`φ ≫ β = α ≫ ψ` with `α` and `β` isomorphisms, then the kernel of `φ` is the preimage along `α`
of the kernel of `ψ`. -/
theorem ker_eq_comap_of_commSq (φ : A ⟶ B) (ψ : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (h : φ ≫ β.hom = α.hom ≫ ψ) :
    RingHom.ker φ.hom = (RingHom.ker ψ.hom).comap α.hom.hom := by
  have hβ : Function.Injective β.hom.hom := β.commRingCatIsoToRingEquiv.injective
  ext x
  have hx := congrArg (fun f : A ⟶ B' => f.hom x) h
  simp only [CommRingCat.comp_apply] at hx
  simp only [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
  refine ⟨fun hk => by rw [← hx, hk, map_zero], fun hk => hβ ?_⟩
  rw [hx, hk, map_zero]

/-- **Surjectivity transports across a commuting square of rings with invertible sides.** -/
theorem surjective_of_commSq (φ : A ⟶ B) (ψ : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (h : φ ≫ β.hom = α.hom ≫ ψ)
    (hψ : Function.Surjective ψ.hom) : Function.Surjective φ.hom := by
  have hβ : Function.Injective β.hom.hom := β.commRingCatIsoToRingEquiv.injective
  intro b
  obtain ⟨a, ha⟩ := hψ (β.hom.hom b)
  refine ⟨α.inv.hom a, hβ ?_⟩
  have hx := congrArg (fun f : A ⟶ B' => f.hom (α.inv.hom a)) h
  simp only [CommRingCat.comp_apply] at hx
  rw [← CommRingCat.comp_apply α.inv α.hom, α.inv_hom_id] at hx
  rw [hx]
  simpa using ha

end CommSq

/-! ### An open over which an immersion is closed lies in the coborder -/

/-- **An open over which an immersion restricts to a closed immersion is contained in the
coborder of its range.**  Since `AlgebraicGeometry.Scheme.Hom.coborderRange` is the canonical
open through which [Stacks, Tag 01R2] factors an immersion as a closed immersion, this says that
such an open is already one of the opens over which the conormal sheaf may be computed. -/
theorem le_coborderRange_of_isClosedImmersion_morphismRestrict {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) [IsClosedImmersion (i ∣_ U)] : U ≤ i.coborderRange := by
  have hcl : IsClosed ((U : Set X) ↓∩ Set.range i.base) := by
    have h := (i ∣_ U).isClosedEmbedding.isClosed_range
    rw [morphismRestrict_base] at h
    rwa [← Set.range_restrictPreimage (U : Set X) i.base]
  rw [isClosed_preimage_val] at hcl
  intro x hx
  exact mem_coborder_iff_imp.2 fun hxc => hcl ⟨hx, U.2.inter_closure ⟨hx, hxc⟩⟩

/-! ### The affine model of an immersion over an affine open -/

section AffineModel

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
  (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
  (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
    e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include he

/-- The affine model, transported from the fibre product `Z ×_X U` to the open subscheme
`i ⁻¹ᵁ U` of `Z`. -/
theorem morphismRestrict_isoSpec_hom_eq :
    (i ∣_ U) ≫ hU.isoSpec.hom =
      ((pullbackRestrictIsoRestrict i U).symm ≪≫ e).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [morphismRestrict, Category.assoc, he]
  simp

/-- **The restriction of `i` over `U` is a closed immersion.**  This is the first consequence of
the affine model: the map on the fibre product is `Spec` of a surjection, up to isomorphism. -/
theorem isClosedImmersion_morphismRestrict_of_affineModel : IsClosedImmersion (i ∣_ U) := by
  have hsnd : IsClosedImmersion (pullback.snd i U.ι) := by
    have h : pullback.snd i U.ι =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hU.isoSpec.inv := by
      rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h]; infer_instance
  delta morphismRestrict; infer_instance

omit he in
/-- **`i ⁻¹ᵁ U` is an affine open of `Z`**, being isomorphic to `Spec (Γ(X, U) ⧸ I)`. -/
theorem isAffineOpen_preimage_of_affineModel
    (e' : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I))) : IsAffineOpen (i ⁻¹ᵁ U) :=
  .of_isIso ((pullbackRestrictIsoRestrict i U).symm ≪≫ e').hom

/-- **`U` is contained in the coborder of the range of `i`.**  Together with Tag 01R2's
definition of the conormal sheaf as a pullback along `i.liftCoborder`, this is what lets the
conormal sheaf be computed over `U` directly. -/
theorem le_coborderRange_of_affineModel [IsImmersion i] : U ≤ i.coborderRange :=
  let := isClosedImmersion_morphismRestrict_of_affineModel i U hU I e he
  le_coborderRange_of_isClosedImmersion_morphismRestrict i U

/-- **The ring-level content of the affine model**: the map on sections
`Γ(X, U) ⟶ Γ(Z, i ⁻¹ᵁ U)` is the quotient map by `I` followed by an isomorphism. -/
theorem exists_iso_appLE_quotientMk :
    ∃ γ : CommRingCat.of (Γ(X, U) ⧸ I) ≅ Γ(Z, i ⁻¹ᵁ U),
      i.appLE U (i ⁻¹ᵁ U) le_rfl = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ γ.hom := by
  set q : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I) with hq
  set ρ : (i ⁻¹ᵁ U).toScheme ≅ Spec (.of (Γ(X, U) ⧸ I)) :=
    (pullbackRestrictIsoRestrict i U).symm ≪≫ e with hρdef
  have hρ : (i ∣_ U) ≫ hU.isoSpec.hom = ρ.hom ≫ Spec.map q :=
    morphismRestrict_isoSpec_hom_eq i U hU I e he
  set σ : Γ(Spec Γ(X, U), ⊤) ≅ Γ((U : Scheme), ⊤) :=
    Scheme.ΓSpecIso Γ(X, U) ≪≫ U.topIso.symm with hσ
  have h2 : σ.hom ≫ (i ∣_ U).appTop = (Spec.map q).appTop ≫ ρ.hom.appTop := by
    rw [hσ, Iso.trans_hom, Iso.symm_hom, ← hU.isoSpec_hom_appTop,
      ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hρ]
  have h3 : (i ∣_ U).appTop =
      U.topIso.hom ≫ q ≫ (Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I))).inv ≫ ρ.hom.appTop := by
    rw [(Iso.eq_inv_comp σ).2 h2, hσ]
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  have hiso : IsIso (ρ.hom.appTop) :=
    ⟨ρ.inv.appTop, by rw [← Scheme.Hom.comp_appTop, ρ.inv_hom_id]; rfl,
      by rw [← Scheme.Hom.comp_appTop, ρ.hom_inv_id]; rfl⟩
  have hsq : (i ∣_ U).appTop ≫ (i ⁻¹ᵁ U).topIso.hom =
      U.topIso.hom ≫ i.appLE U (i ⁻¹ᵁ U) le_rfl := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact ((AlgebraicGeometry.arrowResLEAppIso i U (i ⁻¹ᵁ U) le_rfl).hom.w).symm
  refine ⟨(Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I))).symm ≪≫ asIso (ρ.hom.appTop) ≪≫
    (i ⁻¹ᵁ U).topIso, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
  refine (cancel_epi U.topIso.hom).mp ?_
  rw [← hsq, h3]
  simp only [Category.assoc]

/-- **The kernel of the map on sections of the affine chart is `I`.** -/
theorem ker_appLE_eq_of_affineModel :
    RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = I := by
  obtain ⟨γ, hγ⟩ := exists_iso_appLE_quotientMk i U hU I e he
  rw [ker_eq_comap_of_commSq (i.appLE U (i ⁻¹ᵁ U) le_rfl)
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (Iso.refl _) γ.symm
    (by rw [hγ]; simp)]
  simp

/-- **The map on sections of the affine chart is surjective.** -/
theorem surjective_appLE_of_affineModel :
    Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom := by
  obtain ⟨γ, hγ⟩ := exists_iso_appLE_quotientMk i U hU I e he
  exact surjective_of_commSq (i.appLE U (i ⁻¹ᵁ U) le_rfl)
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (Iso.refl _) γ.symm
    (by rw [hγ]; simp) Ideal.Quotient.mk_surjective

end AffineModel

/-! ### Existence of the affine model -/

section AffineModelExists

variable {Z X : Scheme.{u}}

/-- **An affine open over which an immersion restricts to a closed immersion carries an affine
model.**  The scheme-theoretic intersection `Z ×_X U` is the spectrum of a quotient
`Γ(X, U) ⧸ I`, compatibly with the projections to `U ≅ Spec Γ(X, U)`.  This is the hypothesis
that the affine computation of [Stacks, Tag 01R3] part (2) consumes.

The restriction `i ∣_ U` composed with `AlgebraicGeometry.IsAffineOpen.isoSpec` is a closed
immersion with affine target, so `AlgebraicGeometry.IsClosedImmersion.Spec_iff` presents it as
`Spec` of a quotient map; `AlgebraicGeometry.pullbackRestrictIsoRestrict` transports that
presentation from the open subscheme `i ⁻¹ᵁ U` to the fibre product. -/
theorem exists_affineModel_of_isClosedImmersion_restrict (i : Z ⟶ X) (U : X.Opens)
    (hU : IsAffineOpen U) (hcl : IsClosedImmersion (i ∣_ U)) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I))),
      pullback.snd i U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  let _ : IsClosedImmersion (i ∣_ U) := hcl
  have : IsClosedImmersion ((i ∣_ U) ≫ hU.isoSpec.hom) := inferInstance
  obtain ⟨I, e₀, he₀⟩ :=
    (IsClosedImmersion.Spec_iff (f := (i ∣_ U) ≫ hU.isoSpec.hom)).mp inferInstance
  refine ⟨I, pullbackRestrictIsoRestrict i U ≪≫ e₀, ?_⟩
  calc
    pullback.snd i U.ι ≫ hU.isoSpec.hom =
        ((pullbackRestrictIsoRestrict i U).hom ≫ (i ∣_ U)) ≫ hU.isoSpec.hom := by
          rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    _ = (pullbackRestrictIsoRestrict i U).hom ≫ ((i ∣_ U) ≫ hU.isoSpec.hom) := by
          rw [Category.assoc]
    _ = (pullbackRestrictIsoRestrict i U).hom ≫ e₀.hom ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
          rw [he₀]
    _ = (pullbackRestrictIsoRestrict i U ≪≫ e₀).hom ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
          rw [Iso.trans_hom, Category.assoc]

/-- The same statement with the restriction spelled as
`AlgebraicGeometry.Scheme.Hom.resLE`, which `Scheme.Hom.resLE_eq_morphismRestrict` identifies
with `AlgebraicGeometry.morphismRestrict`. -/
theorem exists_affineModel_of_resLE (i : Z ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hcl : IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl)) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I))),
      pullback.snd i U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  exists_affineModel_of_isClosedImmersion_restrict i U hU
    (by rwa [Scheme.Hom.resLE_eq_morphismRestrict] at hcl)

/-- **Every affine open of the ambient scheme of a closed immersion carries an affine model.**
A closed immersion is stable under base change, so it restricts to a closed immersion over every
open. -/
theorem exists_affineModel (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens)
    (hU : IsAffineOpen U) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I))),
      pullback.snd i U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  exists_affineModel_of_isClosedImmersion_restrict i U hU
    (MorphismProperty.of_isPullback (isPullback_morphismRestrict i U).flip inferInstance)

end AffineModelExists

/-! ### The sectionwise ideal sheaf, and the affine computation -/

section IdealSheaf

variable {Z C : Scheme.{u}} (a : Z ⟶ C) (W : C.Opens)

/-- The ideal sheaf of a closed immersion of schemes is quasi-coherent. -/
instance isQuasicoherent_idealSheaf [IsClosedImmersion a] :
    SheafOfModules.IsQuasicoherent (R := C.ringCatSheaf)
      (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom) :=
  inferInstanceAs
    ((kernel (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)).IsQuasicoherent)

/-- **The ideal sheaf is the sectionwise kernel.**  `Stacks.ClosedImmersion.idealSheaf` is the
categorical kernel of `𝒪_C ⟶ a_* 𝒪_Z`; this identifies it with the subsheaf of the structure
sheaf cut out by the map on functions. -/
def idealSheafKerObjIso : Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom ≅
    SheafOfModules.kerObj (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) :=
  IsLimit.conePointUniqueUpToIso
    (kernelIsKernel (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom))
    (SheafOfModules.kerIsLimit _)

/-- **Over any open, the sections of the ideal sheaf are the kernel of the map on functions.** -/
def idealSheafSectionsIso :
    (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op W) ≅
      ModuleCat.of Γ(C, W) (RingHom.ker (a.app W).hom) where
  hom := (idealSheafKerObjIso a).hom.val.app (op W)
  inv := (idealSheafKerObjIso a).inv.val.app (op W)
  hom_inv_id := by
    change ((idealSheafKerObjIso a).hom ≫ (idealSheafKerObjIso a).inv).val.app (op W) = _
    rw [(idealSheafKerObjIso a).hom_inv_id]; rfl
  inv_hom_id := by
    change ((idealSheafKerObjIso a).inv ≫ (idealSheafKerObjIso a).hom).val.app (op W) = _
    rw [(idealSheafKerObjIso a).inv_hom_id]; rfl

/-- **The affine computation for a closed immersion.**  Over an affine open `W` with affine
preimage and surjective map on functions, the sections over `a ⁻¹ᵁ W` of the pullback along `a`
of the ideal sheaf of `a` are `I/I²`, for `I = ker (Γ(C, W) ⟶ Γ(Z, a ⁻¹ᵁ W))`.

This is the ring-theoretic content `I ⊗_R R/I = I/I²` that [Stacks, Tag 01R3] records, read
through the affine base-change description of the sections of a pullback. -/
def affineIdealPullbackIsoCotangent [IsClosedImmersion a]
    (hW : IsAffineOpen W) (hV : IsAffineOpen (a ⁻¹ᵁ W))
    (hsurj : Function.Surjective (a.app W).hom) :
    ((modulePushforward a.toLRSHom.toShHom).obj
        ((modulePullback a.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom))).val.obj (op W)
      ≅ ModuleCat.of Γ(C, W) (RingHom.ker (a.app W).hom).Cotangent := by
  have bc := AlgebraicGeometry.affinePullbackSectionsBaseChangeIso a
    (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom) hW hV (le_refl (a ⁻¹ᵁ W))
  rw [Scheme.Hom.appLE_preimage_self] at bc
  letI : Algebra Γ(C, W) Γ(Z, a ⁻¹ᵁ W) := (a.app W).hom.toAlgebra
  have lin := surjectiveTensorEquivQuotSMul (R := Γ(C, W)) (S := Γ(Z, a ⁻¹ᵁ W))
    hsurj (RingHom.ker (a.app W).hom)
  exact (ModuleCat.restrictScalars (a.app W).hom).mapIso
      (bc.symm ≪≫ (ModuleCat.extendScalars (a.app W).hom).mapIso (idealSheafSectionsIso a W))
    ≪≫ lin.toModuleIso

end IdealSheaf

/-! ### Two transports -/

/-- **`Ideal.Cotangent` transports along a ring isomorphism.**  For an ideal `K` of `R'` and an
isomorphism `α : R ≅ R'`, the cotangent module of the preimage of `K` is, as an `R`-module, the
cotangent module of `K`. -/
def cotangentComapIso {R R' : CommRingCat.{u}} (α : R ≅ R') (K : Ideal R') :
    ModuleCat.of R (K.comap α.hom.hom).Cotangent ≅
      (ModuleCat.restrictScalars α.hom.hom).obj (ModuleCat.of R' K.Cotangent) := by
  letI : Algebra R R' := α.hom.hom.toAlgebra
  have hinj : Function.Injective (algebraMap R R') := α.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective (algebraMap R R') := α.commRingCatIsoToRingEquiv.surjective
  have hker : RingHom.ker (algebraMap R R') = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have heq : K.comap (algebraMap R R') =
      RingHom.ker (algebraMap R R') ⊔ K.comap (algebraMap R R') := by
    rw [hker, bot_sup_eq]
  have hs := Ideal.mapCotangent_surjective_of_comap_eq hsurj heq
  have hk := Ideal.mapCotangent_ker_of_surjective hsurj heq
  have hzero : (Submodule.comap (Submodule.subtype (K.comap (algebraMap R R')))
      (RingHom.ker (algebraMap R R') ⊓ K.comap (algebraMap R R'))).map
        (K.comap (algebraMap R R')).toCotangent = ⊥ := by
    rw [hker, bot_inf_eq, Submodule.comap_bot, LinearMap.ker_eq_bot.2
      (Submodule.injective_subtype _), Submodule.map_bot]
  exact (LinearEquiv.ofBijective _
    ⟨LinearMap.ker_eq_bot.1 (hk.trans hzero), hs⟩).toModuleIso

/-- **Sections of a pushforward along a composite through an open subscheme.**  Because the
module pushforward is functorial on the nose, this is the identity isomorphism once the
factorization has been substituted. -/
def pushforwardCompSectionsIso {Z X : Scheme.{u}} (C : X.Opens) (a : Z ⟶ C.toScheme)
    (i : Z ⟶ X) (hfac : a ≫ C.ι = i) (U : X.Opens)
    (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) :
    ((modulePushforward i.toLRSHom.toShHom).obj M).val.obj (op U) ≅
      (ModuleCat.restrictScalars (C.ι.app U).hom).obj
        (((modulePushforward a.toLRSHom.toShHom).obj M).val.obj (op (C.ι ⁻¹ᵁ U))) := by
  subst hfac
  exact Iso.refl _

/-! ### Tag 01R3, part (2) -/

/-- **The affine computation for a factored immersion.**  Given a closed-immersion factorization
`a ≫ C.ι = i` through an open subscheme `C` that contains the affine chart `U`, and the two
ring-level facts that the map on sections over `U` is surjective with kernel `I`, the sections of
the conormal sheaf over `Z ∩ U` are `I/I²`.

Substituting the factorization is what makes the two descriptions of `Z ∩ U` — as `i ⁻¹ᵁ U` and
as `a ⁻¹ᵁ (C.ι ⁻¹ᵁ U)` — literally the same open, so nothing has to be transported. -/
def factoredAffineConormalIsoCotangent {Z X : Scheme.{u}} (C : X.Opens)
    (a : Z ⟶ C.toScheme) [IsClosedImmersion a] (i : Z ⟶ X) (hfac : a ≫ C.ι = i)
    (U : X.Opens) (hUC : U ≤ C) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (hV : IsAffineOpen (i ⁻¹ᵁ U))
    (hker : RingHom.ker (i.app U).hom = I)
    (hsurj : Function.Surjective (i.app U).hom) :
    ((modulePushforward i.toLRSHom.toShHom).obj
        ((modulePullback a.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom))).val.obj (op U)
      ≅ ModuleCat.of Γ(X, U) I.Cotangent := by
  subst hfac
  haveI hιiso : IsIso (C.ι.app U) := C.ι.isIso_app U (by simpa using hUC)
  have hW : IsAffineOpen (C.ι ⁻¹ᵁ U) := hU.preimage_of_isOpenImmersion _ (by simpa using hUC)
  have hsurj' : Function.Surjective (a.app (C.ι ⁻¹ᵁ U)).hom :=
    Function.Surjective.of_comp (g := (C.ι.app U).hom) hsurj
  have hkerI : I = (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom).comap (C.ι.app U).hom := by
    rw [RingHom.comap_ker, ← hker]
    rfl
  exact pushforwardCompSectionsIso C a (a ≫ C.ι) rfl U _
    ≪≫ (ModuleCat.restrictScalars (C.ι.app U).hom).mapIso
      (affineIdealPullbackIsoCotangent a (C.ι ⁻¹ᵁ U) hW hV hsurj')
    ≪≫ (cotangentComapIso (asIso (C.ι.app U)) _).symm
    ≪≫ (Ideal.Cotangent.equivOfEq _ _ hkerI.symm).toModuleIso

/-- **The affine computation of the conormal sheaf.**  Let `i : Z ⟶ X` be an immersion and
`U ⊆ X` an affine open with `Z ∩ U = Spec (Γ(X, U) ⧸ I)` over `U`.  Then the sections of the
conormal sheaf of `i` over `Z ∩ U` are canonically `I/I²`, which is the assertion of
[Stacks, Tag 01R3] (2).

The conormal sheaf is [Stacks, Tag 01R2]'s, written out: the pullback along
`i.liftCoborder : Z ⟶ i.coborderRange` of the ideal sheaf of that closed immersion.  Its
sections over `Z ∩ U` are presented as the sections over `U` of its pushforward along `i`, so
that the module is one of `Γ(X, U)`-modules, as `I.Cotangent` is. -/
@[stacks 01R3 "part (2): affine conormal sections"]
def affineConormalIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (e : pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((modulePushforward i.toLRSHom.toShHom).obj
        ((modulePullback i.liftCoborder.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom))).val.obj (op U)
      ≅ ModuleCat.of Γ(X, U) I.Cotangent :=
  factoredAffineConormalIsoCotangent i.coborderRange i.liftCoborder i
    (Scheme.Hom.liftCoborder_ι i) U
    (le_coborderRange_of_affineModel i U hU I e he) hU I
    (isAffineOpen_preimage_of_affineModel i U I e)
    (by rw [← Scheme.Hom.appLE_preimage_self i U]
        exact ker_appLE_eq_of_affineModel i U hU I e he)
    (by rw [← Scheme.Hom.appLE_preimage_self i U]
        exact surjective_appLE_of_affineModel i U hU I e he)

end Stacks.Conormal

end
