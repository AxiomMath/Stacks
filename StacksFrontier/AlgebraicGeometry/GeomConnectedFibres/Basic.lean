module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic

/-!
# The fibres of `X ⟶ Spec Γ(X, ⊤)` are geometrically connected

Let `k` be a field and `X` a scheme proper over `k`.  This file proves Stacks Tag 0FD1:  the
canonical morphism `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` is geometrically connected.

The *connectedness* of the fibres is
`Stacks.AlgebraicGeometry.ProperGeomConnected.connectedSpace_fiber_toSpecΓ`;  what is added here
is the base change that upgrades it to geometric connectedness.

## Main results

* `Stacks.AlgebraicGeometry.ProperGeomConnected.isPushout_appTop_fieldBaseChange`:
  for `f : X ⟶ Spec k` proper and `k ⟶ K` a field extension, global sections of the base change
  `X ×_{Spec k} Spec K` are the pushout `Γ(X, ⊤) ⊗_k K`;  this is degree-zero flat base change
  (Stacks Tag 02KH for `i = 0`), obtained from Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`.
* `Stacks.AlgebraicGeometry.ProperGeomConnected.isPullback_toSpecΓ_fieldBaseChange`:
  consequently `X.toSpecΓ` base changes to `(X ×_{Spec k} Spec K).toSpecΓ`.
* `ProperGeomConnected.geometricallyConnected_toSpecΓ_of_isProper_over_field`:
  **Stacks Tag 0FD1**, `GeometricallyConnected X.toSpecΓ`.

## Implementation notes

The Stacks proof deduces from finiteness of coherent cohomology (Tag 02O5) that `Γ(X, ⊤)` is a
finite `k`-algebra, hence Artinian, and reads off the fibres of `X.toSpecΓ` from the resulting
product decomposition.  Here the connectedness of the fibres is instead taken from
`ProperGeomConnected.connectedSpace_fiber_toSpecΓ`, which needs only that `X` is a Noetherian
space and `Γ(X, ⊤)` is integral over `k` (Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`).

Given a field `K` with a `Γ(X, ⊤)`-algebra structure, write `Y := X ×_{Spec k} Spec K`, which is
again proper over the field `K`.  Degree-zero flat base change identifies `Γ(Y, ⊤)` with
`Γ(X, ⊤) ⊗_k K`, so the `Γ(X, ⊤)`-algebra structure on `K` supplies a *surjection*
`Γ(Y, ⊤) → K`, i.e. a closed point `t : Spec K ⟶ Spec Γ(Y, ⊤)`, and it makes
`Y.toSpecΓ` the base change of `X.toSpecΓ` along `Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤)`.  Pasting the two
cartesian squares exhibits `X ×_{Spec Γ(X, ⊤)} Spec K` as `Y ×_{Spec Γ(Y, ⊤)} Spec K`, whose
space is homeomorphic to the fibre of `Y.toSpecΓ` over the image of the closed point of
`Spec K` — connected by the result for `Y`.

## References

* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperGeomConnected

/-- **Degree-zero flat base change along a field extension** (Stacks Tag 02KH for `i = 0`).
If `f : X ⟶ Spec k` is proper and `k ⟶ K` is an extension of fields, then the square of global
sections of the base-change square is a pushout;  that is, the canonical map
`Γ(X, ⊤) ⊗_k K ⟶ Γ(X ×_{Spec k} Spec K, ⊤)` is an isomorphism.

Properness enters only through quasi-compactness and quasi-separatedness of `X`, and flatness of
`Spec K ⟶ Spec k` is automatic for a field extension. -/
theorem isPushout_appTop_fieldBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] :
    letI g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    IsPushout f.appTop g.appTop (pullback.fst f g).appTop (pullback.snd f g).appTop := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : UniversallyClosed f := IsProper.toUniversallyClosed
  have : IsSeparated f := IsProper.toIsSeparated
  have hcompact : IsCompact (X := X) (⊤ : X.Opens) := by
    simpa using f.isCompact_preimage (U := ⊤) isCompact_univ
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hqs : IsQuasiSeparated (α := X) (⊤ : X.Opens) := isQuasiSeparated_univ
  have : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hiso : IsIso (pushoutSection (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) H
      (by simp) (by simp) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H) (hUST := by simp)
      (hUSX := by simp) (hUY := by simp) (isAffineOpen_top _) (isAffineOpen_top _) hcompact hqs
  simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
    (isIso_pushoutSection_iff H (by simp) (by simp) (by simp)).mp hiso

/-- The canonical morphism to the spectrum of the global sections commutes with base change along
an extension of the base field:  for `f : X ⟶ Spec k` proper and `k ⟶ K` an extension of fields,
`(X ×_{Spec k} Spec K).toSpecΓ` is the base change of `X.toSpecΓ`. -/
theorem isPullback_toSpecΓ_fieldBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] :
    letI g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    IsPullback (pullback.fst f g) (pullback f g).toSpecΓ X.toSpecΓ
      (Spec.map (pullback.fst f g).appTop) := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback f g
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of K) := pullback.snd f g
  have hspec : IsPullback (Spec.map q.appTop) (Spec.map p.appTop) (Spec.map g.appTop)
      (Spec.map f.appTop) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appTop_fieldBaseChange k K f)).flip
  have houter : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) p (Spec.map g.appTop)
      (X.toSpecΓ ≫ Spec.map f.appTop) := by
    refine (IsPullback.of_hasPullback f g).flip.of_iso (Iso.refl Y) (asIso (Spec (.of K)).toSpecΓ)
      (Iso.refl X) (asIso (Spec (.of k)).toSpecΓ) ?_ (Category.id_comp p).symm
      (Scheme.toSpecΓ_naturality g) (Scheme.toSpecΓ_naturality f)
    simp only [Iso.refl_hom, asIso_hom]
    exact Scheme.toSpecΓ_naturality q
  exact (IsPullback.of_right houter (Scheme.toSpecΓ_naturality p).symm hspec).flip

/-- A base change of `g : T ⟶ S` along a closed immersion `Spec K ⟶ S` out of the spectrum of a
field is connected as soon as the set-theoretic fibre of `g` over the image point is. -/
theorem connectedSpace_pullback_of_isClosedImmersion {T S : Scheme.{u}} (g : T ⟶ S) (K : Type u)
    [Field K] (t : Spec (.of K) ⟶ S) [IsClosedImmersion t]
    (h : _root_.IsConnected (g ⁻¹' {t (IsLocalRing.closedPoint K)})) :
    ConnectedSpace ↥(pullback g t : Scheme.{u}) := by
  have hrange : Set.range t = ({t (IsLocalRing.closedPoint K)} : Set S) := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, rfl⟩, ?_⟩
    rintro s ⟨x, rfl⟩
    exact congrArg t (Subsingleton.elim x _)
  have hpre : Set.range (pullback.fst g t) = g ⁻¹' {t (IsLocalRing.closedPoint K)} := by
    rw [Scheme.Pullback.range_fst, hrange]
  exact (pullback.fst g t).isEmbedding.toHomeomorph.connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp (hpre ▸ h))

/-- **Stacks Project, Tag 0FD1.** If `X` is proper over a field, then the canonical morphism
from `X` to the spectrum of its ring of global sections has geometrically connected fibres. -/
@[stacks 0FD1, ega "III 4.3.4" "special case"]
theorem geometricallyConnected_toSpecΓ_of_isProper_over_field (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f] :
    GeometricallyConnected X.toSpecΓ := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let φ : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let _ : Algebra k Γ(X, ⊤) := φ.hom.toAlgebra
  let _ : Algebra k K := ((algebraMap Γ(X, ⊤) K).comp (algebraMap k Γ(X, ⊤))).toAlgebra
  let ψ : Γ(X, ⊤) ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap Γ(X, ⊤) K)
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback f g
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of K) := pullback.snd f g
  -- `Γ(X, ⊤) ⊗_k K ≅ Γ(Y, ⊤)`, so `ψ` and the identity of `K` descend to a surjection
  -- `d : Γ(Y, ⊤) ⟶ K`.
  have hcompat : f.appTop ≫ (ψ ≫ (Scheme.ΓSpecIso (.of K)).inv) = g.appTop := by
    have hφ : (Scheme.ΓSpecIso (.of k)).hom ≫ φ = f.appTop := by simp [φ]
    have hψ : φ ≫ ψ = CommRingCat.ofHom (algebraMap k K) := rfl
    rw [← hφ, Category.assoc, ← Category.assoc φ, hψ, Scheme.ΓSpecIso_inv_naturality]
    exact Iso.hom_inv_id_assoc _ _
  have hpush : IsPushout f.appTop g.appTop p.appTop q.appTop :=
    isPushout_appTop_fieldBaseChange k K f
  let d : Γ(Y, ⊤) ⟶ Γ(Spec (.of K), ⊤) :=
    hpush.desc (ψ ≫ (Scheme.ΓSpecIso (.of K)).inv) (𝟙 _) hcompat
  have hpd : p.appTop ≫ d = ψ ≫ (Scheme.ΓSpecIso (.of K)).inv := hpush.inl_desc _ _ _
  have hqd : q.appTop ≫ d = 𝟙 _ := hpush.inr_desc _ _ _
  have hd_surj : Function.Surjective d.hom := fun a =>
    ⟨q.appTop.hom a, by
      simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
        congrArg (fun h : Γ(Spec (.of K), ⊤) ⟶ Γ(Spec (.of K), ⊤) => h.hom a) hqd⟩
  let t : Spec (.of K) ⟶ Spec Γ(Y, ⊤) := (Spec (.of K)).toSpecΓ ≫ Spec.map d
  have : IsClosedImmersion t := by
    have : IsClosedImmersion (Spec.map d) := IsClosedImmersion.spec_of_surjective d hd_surj
    dsimp only [t]
    infer_instance
  -- Pasting `Y.toSpecΓ` over `X.toSpecΓ` with `t` exhibits `X ×_{Spec Γ(X, ⊤)} Spec K` as
  -- `Y ×_{Spec Γ(Y, ⊤)} Spec K`.
  have ht : t ≫ Spec.map p.appTop = Spec.map ψ := by
    dsimp only [t]
    rw [Category.assoc, ← Spec.map_comp, hpd, Spec.map_comp]
    simp
  have houter : IsPullback (pullback.fst Y.toSpecΓ t ≫ p) (pullback.snd Y.toSpecΓ t) X.toSpecΓ
      (Spec.map ψ) := by
    convert (IsPullback.of_hasPullback Y.toSpecΓ t).paste_horiz
      (isPullback_toSpecΓ_fieldBaseChange k K f) using 1
    exact ht.symm
  have : IsProper q := inferInstance
  exact houter.isoPullback.hom.homeomorph.connectedSpace_iff.mp
    (connectedSpace_pullback_of_isClosedImmersion Y.toSpecΓ K t
      (isConnected_preimage_singleton_toSpecΓ q _))

end Stacks.AlgebraicGeometry.ProperGeomConnected
