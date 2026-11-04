module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible modules and global sections under a faithfully flat base change

Let `A → B` be a faithfully flat ring map and `X` a quasi-compact, quasi-separated scheme over
`A`. Tag 0CDX says that an invertible `𝒪_X`-module whose pullback to `X_B` is trivial has
invertible global sections over `R = Γ(X, 𝒪_X)`, and that the multiplication map pairing them
against the sections of the inverse sheaf is an isomorphism. Its proof has exactly three
ingredients: that `R → R' = Γ(X_B, 𝒪_{X_B})` is again faithfully flat, that `Γ` of a
quasi-coherent module base changes along `A → B`, and that invertibility of a module descends
along a faithfully flat ring map. This file carries the first and the third; the second is
degree-zero flat base change for modules and is not available in the development (see the
implementation notes).

## Main results

* `Module.Invertible.of_isBaseChange_of_faithfullyFlat`: invertibility of a module descends
  along a faithfully flat ring map. This is the module-theoretic input of Tag 0CDX, cited there
  as Algebra, Proposition 058S.
* `Module.Invertible.of_trivial_baseChange_of_faithfullyFlat`: the shape in which Tag 0CDX uses
  it — a module whose faithfully flat base change is free of rank one is invertible.
* `Module.Invertible.exists_mulEquiv_of_lTensor_surjective`: a linear map to the base ring that
  becomes surjective after a faithfully flat base change is an isomorphism. This is the
  multiplication clause of Tag 0CDX, once the multiplication is known to be surjective over
  `R'`.
* `Stacks.AlgebraicGeometry.PicardBaseChange.isPushout_appTop_baseChange`: for `X` a
  quasi-compact, quasi-separated scheme over `A` and `A → B` flat, global sections of the base
  change `X_B` are the pushout `Γ(X, 𝒪_X) ⊗_A B`. This is Tag 02KH in degree zero for the
  structure sheaf.
* `Stacks.AlgebraicGeometry.PicardBaseChange.faithfullyFlat_appTop_pullback_fst`: consequently
  `Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})` is faithfully flat when `A → B` is.

## Implementation notes

Descent of invertibility is read off the characterization of an invertible module as a finite
projective module of rank one at every prime (Tag 0B8I, in the development as
`Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse`). Finiteness
and projectivity descend by Tag 058S, and the rank descends pointwise because a faithfully flat
ring map has surjective comap on prime spectra and `Module.rankAtStalk` is insensitive to base
change. Base changes are taken abstractly, as an `IsBaseChange` witness rather than through the
model `S ⊗[R] M`, matching `StacksFrontier/RingTheory/Flat/FaithfullyFlat/Descent.lean`.

The degree-zero base change for the structure sheaf is Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` read on the four
total opens. It generalizes
`Stacks.AlgebraicGeometry.ProperGeomConnected.isPushout_appTop_fieldBaseChange`, which is the
case of a proper morphism to the spectrum of a field; properness and the field there enter only
through quasi-compactness, quasi-separatedness and flatness, which are the hypotheses made here.

**What Tag 0CDX still needs is the same statement for a module**: for an invertible — hence
quasi-coherent — `𝒪_X`-module `L` on a quasi-compact, quasi-separated `X` over `A`, the
canonical map `Γ(X, L) ⊗_A B → Γ(X_B, L_B)` is an isomorphism. Mathlib's `pushoutSection`
family covers only the structure sheaf, so the statement is not an instance of what is here.
What *is* available, and is the affine input a Čech argument for it would run on, is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`:
`Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U) ≅ Γ(f^*F, V)` for a quasi-coherent `F` and a compatible pair of
affine opens, normalised on `1 ⊗ a` by `affinePullbackSectionsBaseChangeIso_one_tmul`, together
with `AlgebraicGeometry.isBaseChange_restrict_of_isAffineOpen`
(`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean`). Quasi-coherence of the two
sides is `AlgebraicGeometry.isQuasicoherent_of_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeData.lean`) and
`Stacks.Modules.isQuasicoherent_pullback`
(`StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentPullbackScheme.lean`, Tag 01BG), and the
ringed-space pullback `RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` that the
Chapter 33 decomposition states its triviality hypothesis with is *definitionally*
`Scheme.Modules.pullback f`, so no comparison is needed between the two. The one piece with no
module counterpart is the quasi-compact-quasi-separated induction that Mathlib performs for the
structure sheaf (`isIso_pushoutSection_of_iSup_eq` and
`mono_pushoutSection_of_isCompact_of_flat_right`): iso over each member of a finite affine cover
plus mono over the pairwise intersections gives iso over the union.

With the module statement in hand, Tag 0CDX is
`Module.Invertible.of_trivial_baseChange_of_faithfullyFlat` and
`Module.Invertible.exists_mulEquiv_of_lTensor_surjective` applied to
`faithfullyFlat_appTop_pullback_fst`.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
* [Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct TopologicalSpace

universe u v w t

/-! ### Descent of invertibility along a faithfully flat ring map -/

/-- **Stacks Project, Tag 058S** for invertible modules. Let `R → S` be a faithfully flat ring
map, let `M` be an `R`-module and let `f : M →ₗ[R] N` exhibit the `S`-module `N` as the base
change of `M`. If `N` is an invertible `S`-module then `M` is an invertible `R`-module.

This is the algebraic input of Tag 0CDX. -/
theorem Module.Invertible.of_isBaseChange_of_faithfullyFlat
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type t} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f) [Module.Invertible S N] :
    Module.Invertible R M := by
  have : Module.Finite S (S ⊗[R] M) := Module.Finite.equiv hf.equiv.symm
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have : Module.Projective R M :=
    Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat f hf
  have : Module.Flat R M := Module.Flat.of_projective
  have hN := ((Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{v,
    t, 0} S N).1.out 2 1).mp ‹Module.Invertible S N›
  have key : Module.Finite R M ∧ Module.Projective R M ∧
      Module.rankAtStalk (R := R) M = Function.const (PrimeSpectrum R) 1 := by
    refine ⟨‹_›, ‹_›, funext fun p ↦ ?_⟩
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
    rw [← Module.rankAtStalk_isBaseChange hf q, hN.2.2]
    rfl
  exact ((Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u, w, 0}
    R M).1.out 1 2).mp key

/-- A module whose base change along a faithfully flat ring map is free of rank one is
invertible. This is the form in which Tag 0CDX uses descent of invertibility: the base change of
`Γ(X, L)` to `Γ(X_B, 𝒪_{X_B})` is trivial because the pullback of `L` to `X_B` is. -/
@[sga "4½ Arcata 1.4.2" "special case"]
theorem Module.Invertible.of_trivial_baseChange_of_faithfullyFlat
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type t} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f) (hN : Nonempty (N ≃ₗ[S] S)) :
    Module.Invertible R M :=
  let : Module.Invertible S N := Module.Invertible.congr hN.some.symm
  Module.Invertible.of_isBaseChange_of_faithfullyFlat f hf

/-- A pairing of two invertible modules with values in the base ring that becomes surjective
after a faithfully flat base change is an isomorphism, with the given pairing as its underlying
function.

This is the multiplication clause of Tag 0CDX: the map
`Γ(X, L) ⊗ Γ(X, L^{⊗ -1}) → Γ(X, 𝒪_X)` is surjective over `X_B`, because `L` becomes trivial
there, and the two factors are invertible by the first two clauses. Surjectivity suffices to
conclude because a surjection between invertible modules is bijective. -/
theorem Module.Invertible.exists_mulEquiv_of_lTensor_surjective
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] {N : Type t} [AddCommGroup N] [Module R N] [Module.Invertible R N]
    (μ : M ⊗[R] N →ₗ[R] R) (hμ : Function.Surjective (μ.lTensor S)) :
    ∃ e : M ⊗[R] N ≃ₗ[R] R, ∀ s t, e (s ⊗ₜ[R] t) = μ (s ⊗ₜ[R] t) :=
  ⟨LinearEquiv.ofBijective μ (Module.Invertible.bijective_of_surjective
    ((Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S μ).mp hμ)), fun _ _ ↦ rfl⟩

namespace Stacks.AlgebraicGeometry.PicardBaseChange

/-! ### Degree-zero flat base change for the structure sheaf -/

/-- **Degree-zero flat base change** (Stacks Tag 02KH for `i = 0`). If `X` is a quasi-compact,
quasi-separated scheme over a ring `A` and `φ : A → B` is flat, then the square of global
sections of the base-change square is a pushout; that is, the canonical map
`Γ(X, 𝒪_X) ⊗_A B ⟶ Γ(X_B, 𝒪_{X_B})` is an isomorphism. -/
theorem isPushout_appTop_baseChange {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : φ.Flat) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPushout f.appTop (Spec.map (CommRingCat.ofHom φ)).appTop
      (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appTop
      (pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop := by
  let g : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
  let H : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hcompact : IsCompact (X := X) (⊤ : X.Opens) := by simpa using isCompact_univ (X := X)
  have hqs : IsQuasiSeparated (α := X) (⊤ : X.Opens) := isQuasiSeparated_univ
  have : Flat g := Flat.SpecMap_iff.mpr hφ
  have hiso : IsIso (pushoutSection (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) H
      (by simp) (by simp) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H) (hUST := by simp)
      (hUSX := by simp) (hUY := by simp) (isAffineOpen_top _) (isAffineOpen_top _) hcompact hqs
  simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
    (isIso_pushoutSection_iff H (by simp) (by simp) (by simp)).mp hiso

/-- Global sections of a quasi-compact, quasi-separated scheme over `A` stay faithfully flat
under a faithfully flat base change `A → B`: the ring map
`Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})` is faithfully flat, being the cobase change of `A → B` along
`A → Γ(X, 𝒪_X)`.

This is the step of Tag 0CDX reading "`R → R ⊗_A B` is faithfully flat, as the base change of
the faithfully flat map `A → B`". -/
theorem faithfullyFlat_appTop_pullback_fst {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : φ.FaithfullyFlat) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    RingHom.FaithfullyFlat
      (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appTop.hom := by
  have hiso : (RingHom.toMorphismProperty RingHom.FaithfullyFlat).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FaithfullyFlat.respectsIso
  have hcobase :
      (RingHom.toMorphismProperty RingHom.FaithfullyFlat).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.FaithfullyFlat.isStableUnderBaseChange
  have hg : RingHom.FaithfullyFlat (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
    have heq : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (.of A)).hom ≫
        CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of B)).inv := by
      simp
    have key : RingHom.FaithfullyFlat
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom :=
      MorphismProperty.RespectsIso.precomp (RingHom.toMorphismProperty RingHom.FaithfullyFlat)
        _ _ (MorphismProperty.RespectsIso.postcomp _ _ _ hφ)
    rw [heq]
    exact key
  exact hcobase.of_isPushout (isPushout_appTop_baseChange hφ.flat f) hg

end Stacks.AlgebraicGeometry.PicardBaseChange

end
