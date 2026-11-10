module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Algebra.MvPolynomial.Equiv
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine-space base changes and universally closed affine morphisms

For a quasi-compact morphism `f : X ⟶ Y`, the following are equivalent: `f` is universally closed;
every base change of `f` along a morphism locally of finite presentation is closed; and
`𝔸(n; X) ⟶ 𝔸(n; Y)` is closed for every `n : ℕ`. This file proves that an affine morphism `f` for
which `𝔸(1; X) ⟶ 𝔸(1; Y)` is closed is universally closed and integral, together with the
functoriality of `𝔸(n; -)` in the base and the stability of the affine-space condition under
restriction to opens of the target and base change along closed immersions into affine space.

## Main results

* `affineSpaceMap_isPullback_of_isPullback`: `𝔸(n; -)` carries a pullback square of schemes to a
  pullback square.
* `isClosedMap_affineSpaceMap_morphismRestrict`: the affine-space condition restricts to any open
  of the target.
* `isClosedMap_of_isPullback_of_isClosedImmersion_affineSpace`: a base change of `f` along a
  closed immersion into `𝔸(n; Y)` is closed as soon as `𝔸(n; X) ⟶ 𝔸(n; Y)` is.
* `universallyClosed_of_isClosedMap_affineSpaceMap_of_isAffineHom`: an affine morphism whose base
  change to the affine line is closed is universally closed.
* `isIntegralHom_of_isClosedMap_affineSpaceMap`: an affine morphism whose base change to the
  affine line is closed is integral.
* `isClosedMap_pullbackSnd_specMap_of_finiteType`: if every affine-space base change of
  `f : X ⟶ Spec R` is closed, then so is the base change of `f` along the spectrum of any
  finite-type ring map out of `R`.

## References

* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Stacks.AlgebraicGeometry.Tag05JXReduction

/-! ### Functoriality of affine space in the base -/

/-- `𝔸(n; -)` carries a pullback square of schemes to a pullback square. -/
theorem affineSpaceMap_isPullback_of_isPullback (n : Type u) {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {iX : X' ⟶ X} {iY : Y' ⟶ Y}
    (h : IsPullback iX f' f iY) :
    IsPullback (AffineSpace.map n iX) (AffineSpace.map n f') (AffineSpace.map n f)
      (AffineSpace.map n iY) := by
  refine IsPullback.of_bot ?_ ?_ (AffineSpace.isPullback_map (n := n) iY)
  · rw [AffineSpace.map_over, AffineSpace.map_over]
    exact (AffineSpace.isPullback_map (n := n) iX).paste_vert h
  · rw [← AffineSpace.map_comp, ← AffineSpace.map_comp, h.w]

/-- `𝔸(n; -)` carries an open immersion to an open immersion. -/
instance isOpenImmersion_affineSpaceMap (n : Type u) {Y' Y : Scheme.{u}} (iY : Y' ⟶ Y)
    [IsOpenImmersion iY] : IsOpenImmersion (AffineSpace.map n iY) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (AffineSpace.isPullback_map (n := n) iY).flip inferInstance

/-- `𝔸(n; -)` carries a closed immersion to a closed immersion. -/
instance isClosedImmersion_affineSpaceMap (n : Type u) {Y' Y : Scheme.{u}} (iY : Y' ⟶ Y)
    [IsClosedImmersion iY] : IsClosedImmersion (AffineSpace.map n iY) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (AffineSpace.isPullback_map (n := n) iY).flip inferInstance

/-! ### The affine-space condition is local on the target -/

/-- If `𝔸(n; X) ⟶ 𝔸(n; Y)` is closed, then so is `𝔸(n; X') ⟶ 𝔸(n; Y')` for the base change
`f' : X' ⟶ Y'` of `f : X ⟶ Y` along an open immersion `Y' ⟶ Y`. -/
theorem isClosedMap_affineSpaceMap_of_isPullback (n : Type u) {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {iX : X' ⟶ X} {iY : Y' ⟶ Y} [IsOpenImmersion iY]
    (h : IsPullback iX f' f iY) (hf : IsClosedMap (AffineSpace.map n f).base) :
    IsClosedMap (AffineSpace.map n f').base :=
  IsZariskiLocalAtTarget.of_isPullback (P := topologically @IsClosedMap)
    (affineSpaceMap_isPullback_of_isPullback n h) hf

/-- The affine-space closedness condition restricts to an open of the target. -/
theorem isClosedMap_affineSpaceMap_morphismRestrict (n : Type u) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hf : IsClosedMap (AffineSpace.map n f).base) :
    IsClosedMap (AffineSpace.map n (f ∣_ V)).base :=
  isClosedMap_affineSpaceMap_of_isPullback n (isPullback_morphismRestrict f V).flip hf

/-! ### Base change along a closed immersion into affine space -/

/-- A map is closed if it is conjugate, along closed embeddings on both sides, to a closed map. -/
private theorem isClosedMap_of_isClosedEmbedding_comm {α β γ δ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {u : β → α} {v : δ → γ} (hu : IsClosedEmbedding u) (hv : IsClosedEmbedding v)
    {g : α → γ} {g' : β → δ} (hcomm : ∀ b, v (g' b) = g (u b)) (hg : IsClosedMap g) :
    IsClosedMap g' := by
  intro C hC
  have himg : v '' (g' '' C) = g '' (u '' C) := by
    simp only [Set.image_image]
    exact Set.image_congr' hcomm
  rw [hv.isClosed_iff_image_isClosed, himg]
  exact hg _ (hu.isClosedMap _ hC)

/-- The base change of a closed morphism of schemes along a closed immersion is closed. -/
theorem isClosedMap_of_isPullback_of_isClosedImmersion
    {X Y T W : Scheme.{u}} {f : X ⟶ Y} {j : T ⟶ Y} [IsClosedImmersion j]
    {g : W ⟶ T} {k : W ⟶ X} (h : IsPullback k g f j) (hf : IsClosedMap f.base) :
    IsClosedMap g.base := by
  have hk : IsClosedImmersion k :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  have hw : ∀ w : W, j (g w) = f (k w) := fun w => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
  exact isClosedMap_of_isClosedEmbedding_comm k.isClosedEmbedding j.isClosedEmbedding hw hf

/-- A base change of `f` along a morphism that factors as a closed immersion into `𝔸(n; Y)`
followed by the projection is closed, as soon as `𝔸(n; X) ⟶ 𝔸(n; Y)` is. -/
theorem isClosedMap_of_isPullback_of_isClosedImmersion_affineSpace (n : Type u)
    {X Y T W : Scheme.{u}} {f : X ⟶ Y} {j : T ⟶ 𝔸(n; Y)} [IsClosedImmersion j]
    {g : W ⟶ T} {k : W ⟶ X} (h : IsPullback k g f (j ≫ 𝔸(n; Y) ↘ Y))
    (hf : IsClosedMap (AffineSpace.map n f).base) :
    IsClosedMap g.base :=
  isClosedMap_of_isPullback_of_isClosedImmersion
    (IsPullback.of_right' h (AffineSpace.isPullback_map f).flip) hf

/-! ### The affine case

A morphism of affine schemes is universally closed exactly when it is integral, and integrality
is detected by the affine line. -/

/-- `𝔸(n; -)` carries an isomorphism to an isomorphism. -/
instance isIso_affineSpaceMap (n : Type u) {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i] :
    IsIso (AffineSpace.map n i) :=
  ⟨AffineSpace.map n (inv i),
    by rw [← AffineSpace.map_comp, IsIso.hom_inv_id, AffineSpace.map_id],
    by rw [← AffineSpace.map_comp, IsIso.inv_hom_id, AffineSpace.map_id]⟩

/-- The affine-space condition only depends on a morphism up to composition with isomorphisms on
either side. -/
theorem isClosedMap_affineSpaceMap_of_eq (n : Type u) {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (i : X' ⟶ X) [IsIso i] (j : Y ⟶ Y') [IsIso j]
    (hf : f' = i ≫ f ≫ j) (h : IsClosedMap (AffineSpace.map n f).base) :
    IsClosedMap (AffineSpace.map n f').base := by
  subst hf
  rw [AffineSpace.map_comp, AffineSpace.map_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsClosedMap)
      (AffineSpace.map n i) (AffineSpace.map n f ≫ AffineSpace.map n j)).mpr
    ((MorphismProperty.cancel_right_of_respectsIso (P := topologically @IsClosedMap)
      (AffineSpace.map n f) (AffineSpace.map n j)).mpr h)

/-- The identification of `MvPolynomial σ R` with `R[X]` for a one-element index type `σ` is
natural in `R`. -/
theorem uniqueAlgEquiv_map {σ : Type u} [Unique σ] {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : MvPolynomial σ R) :
    MvPolynomial.uniqueAlgEquiv S σ (MvPolynomial.map φ p)
      = Polynomial.map φ (MvPolynomial.uniqueAlgEquiv R σ p) := by
  ext k
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.coeff_map, Polynomial.coeff_map,
    MvPolynomial.coeff_uniqueAlgEquiv]

/-- If, for a one-element index type `σ`, the comap of
`MvPolynomial.map φ : MvPolynomial σ R →+* MvPolynomial σ S` is a closed map, then `φ` is
integral. -/
theorem isIntegral_of_isClosedMap_comap_mvPolynomialMap {σ : Type u} [Unique σ]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (h : IsClosedMap (PrimeSpectrum.comap (MvPolynomial.map (σ := σ) φ))) :
    φ.IsIntegral := by
  refine PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom φ ?_
  set eR : MvPolynomial σ R ≃+* Polynomial R := (MvPolynomial.uniqueAlgEquiv R σ).toRingEquiv
  set eS : MvPolynomial σ S ≃+* Polynomial S := (MvPolynomial.uniqueAlgEquiv S σ).toRingEquiv
  refine isClosedMap_of_isClosedEmbedding_comm
    (PrimeSpectrum.homeomorphOfRingEquiv eS).symm.isClosedEmbedding
    (PrimeSpectrum.homeomorphOfRingEquiv eR).symm.isClosedEmbedding (fun b => ?_) h
  change PrimeSpectrum.comap (eR : MvPolynomial σ R →+* Polynomial R)
      (PrimeSpectrum.comap (Polynomial.mapRingHom φ) b)
    = PrimeSpectrum.comap (MvPolynomial.map (σ := σ) φ)
      (PrimeSpectrum.comap (eS : MvPolynomial σ S →+* Polynomial S) b)
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  exact RingHom.ext fun p => (uniqueAlgEquiv_map φ p).symm

/-- If the base change of `Spec φ` to the affine line is closed, then `Spec φ` is integral. -/
theorem isIntegralHom_specMap_of_isClosedMap_affineSpaceMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (h : IsClosedMap (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map φ)).base) :
    IsIntegralHom (Spec.map φ) := by
  rw [IsIntegralHom.SpecMap_iff]
  exact isIntegral_of_isClosedMap_comap_mvPolynomialMap (σ := ULift.{u} (Fin 1)) φ.hom
    ((MorphismProperty.arrow_mk_iso_iff (P := topologically @IsClosedMap)
      (AffineSpace.mapSpecMap (n := ULift.{u} (Fin 1)) φ)).mp h)

/-- A morphism of affine schemes whose base change to the affine line is closed is integral. -/
theorem isIntegralHom_of_isClosedMap_affineSpaceMap_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : IsClosedMap (AffineSpace.map (ULift.{u} (Fin 1)) f).base) : IsIntegralHom f := by
  have hfac : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [Scheme.isoSpec_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hspec : IsClosedMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map f.appTop)).base :=
    isClosedMap_affineSpaceMap_of_eq _ X.isoSpec.inv Y.isoSpec.hom
      (by rw [← Scheme.isoSpec_hom_naturality, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]) h
  have := isIntegralHom_specMap_of_isClosedMap_affineSpaceMap f.appTop hspec
  rw [hfac]
  infer_instance

/-- An affine morphism of schemes whose base change to the affine line is closed is universally
closed. -/
@[ega "II 5.4.9" "5.4.8, special case"]
theorem universallyClosed_of_isClosedMap_affineSpaceMap_of_isAffineHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    (h : IsClosedMap (AffineSpace.map (ULift.{u} (Fin 1)) f).base) :
    UniversallyClosed f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @UniversallyClosed)
    (fun V : Y.affineOpens => V.1) (iSup_affineOpens_eq_top Y)]
  intro V
  have : IsAffine V.1.toScheme := V.2
  have : IsAffineHom (f ∣_ V.1) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict f V.1).flip inferInstance
  have : IsAffine (f ⁻¹ᵁ V.1).toScheme := isAffine_of_isAffineHom (f ∣_ V.1)
  have := isIntegralHom_of_isClosedMap_affineSpaceMap_of_isAffine (f ∣_ V.1)
    (isClosedMap_affineSpaceMap_morphismRestrict _ f V.1 h)
  infer_instance

/-- An affine morphism of schemes whose base change to the affine line is closed is integral. -/
@[ega "IV 18.12.8" "more general"]
theorem isIntegralHom_of_isClosedMap_affineSpaceMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (h : IsClosedMap (AffineSpace.map (ULift.{u} (Fin 1)) f).base) :
    IsIntegralHom f :=
  IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨universallyClosed_of_isClosedMap_affineSpaceMap_of_isAffineHom f h, inferInstance⟩

/-- An affine morphism of schemes all of whose base changes to finite-dimensional affine spaces
are closed is universally closed. -/
theorem universallyClosed_of_forall_isClosedMap_affineSpaceMap_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (h : ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f).base) :
    UniversallyClosed f :=
  universallyClosed_of_isClosedMap_affineSpaceMap_of_isAffineHom f (h 1)

/-! ### Base change along a finite-type affine morphism

A finite-type ring map presents its target as a quotient of a polynomial ring in finitely many
variables, so its spectrum is a closed subscheme of a finite-dimensional affine space over the
base. -/

/-- A finite-type ring map `ψ : R →+* B` is the composite of `MvPolynomial.C` with a surjection
onto `B` from a polynomial ring over `R` in finitely many variables. -/
theorem exists_surjective_mvPolynomial_of_finiteType {R B : Type u} [CommRing R] [CommRing B]
    (ψ : R →+* B) (hψ : ψ.FiniteType) :
    ∃ (n : ℕ) (π : MvPolynomial (ULift.{u} (Fin n)) R →+* B),
      Function.Surjective π ∧ π.comp MvPolynomial.C = ψ := by
  let := ψ.toAlgebra
  obtain ⟨n, F, hF⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hψ
  refine ⟨n, (F.comp (MvPolynomial.renameEquiv R (Equiv.ulift (α := Fin n))).toAlgHom).toRingHom,
    hF.comp (MvPolynomial.renameEquiv R (Equiv.ulift (α := Fin n))).surjective, ?_⟩
  have hG := (F.comp
    (MvPolynomial.renameEquiv R (Equiv.ulift (α := Fin n))).toAlgHom).comp_algebraMap
  rwa [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra] at hG

/-- If every finite-dimensional affine-space base change of `f : X ⟶ Spec R` is closed, then the
base change of `f` along the spectrum of any finite-type ring map out of `R` is closed. -/
theorem isClosedMap_pullbackSnd_specMap_of_finiteType {X : Scheme.{u}} {R B : CommRingCat.{u}}
    (f : X ⟶ Spec R) (ψ : R ⟶ B) (hψ : ψ.hom.FiniteType)
    (h : ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f).base) :
    IsClosedMap (pullback.snd f (Spec.map ψ)).base := by
  obtain ⟨n, π, hπ, hπC⟩ := exists_surjective_mvPolynomial_of_finiteType ψ.hom hψ
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hfac : (Spec.map (CommRingCat.ofHom π) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv) ≫
      𝔸(ULift.{u} (Fin n); Spec R) ↘ Spec R = Spec.map ψ := by
    rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hπC, CommRingCat.ofHom_hom]
  have hpb : IsPullback (pullback.fst f (Spec.map ψ)) (pullback.snd f (Spec.map ψ)) f
      ((Spec.map (CommRingCat.ofHom π) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv) ≫
        𝔸(ULift.{u} (Fin n); Spec R) ↘ Spec R) := by
    rw [hfac]
    exact IsPullback.of_hasPullback f (Spec.map ψ)
  exact isClosedMap_of_isPullback_of_isClosedImmersion_affineSpace (ULift.{u} (Fin n)) hpb (h n)

end Stacks.AlgebraicGeometry.Tag05JXReduction
