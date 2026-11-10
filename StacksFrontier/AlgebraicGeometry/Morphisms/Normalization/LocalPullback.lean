module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk
import all StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk

/-!
# Local presentation of the normalization

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components and let
`x` be a point of `X`. The base change of the normalization of `X` along `Spec 𝒪_{X,x} ⟶ X` is the
spectrum of the integral closure of `𝒪_{X,x}` in the product of the residue fields of its minimal
primes, as a scheme over `Spec 𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.Scheme.exists_iso_pullback_fromSpecStalk`: for an affine quasi-separated
  morphism `f : Y ⟶ X`, the base change of `f` along `Spec 𝒪_{X,x} ⟶ X` is the spectrum of the
  stalk at `x` of `f_* 𝒪_Y`, compatibly with the projection to `Spec 𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme.exists_iso_pullback_normalization_fromSpecStalk`: the base change of
  the normalization along `Spec 𝒪_{X,x} ⟶ X` is the spectrum of the integral closure of `𝒪_{X,x}`
  in the product of the residue fields of its minimal primes, by the identification of Tag 0C3B.

## Implementation notes

The last step of `exists_iso_pullback_normalization_fromSpecStalk` is written in term mode rather
than with `rw`: the isomorphism crosses `CommRingCat.of ↑R = R`, which is definitional but not
type-correct at `implicit` transparency, so a rewrite whose motive mentions it fails.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An affine quasi-separated morphism pulled back to the spectrum of a local ring of the
target is the spectrum of the stalk of the pushed-forward structure sheaf. -/
public theorem exists_iso_pullback_fromSpecStalk {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] [QuasiSeparated f] (x : X) :
    ∃ e : pullback f (X.fromSpecStalk x) ≅ Spec ((f.base _* Y.presheaf).stalk x),
      e.hom ≫ Spec.map ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c) =
        pullback.snd f (X.fromSpecStalk x) := by
  classical
  obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hV
  have : IsAffine U.toScheme := hU
  set φ : Spec (X.presheaf.stalk x) ⟶ U.toScheme := U.fromSpecStalkOfMem x hxU with hφ
  have hfs : φ ≫ U.ι = X.fromSpecStalk x := U.fromSpecStalkOfMem_ι x hxU
  have ht : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  have hs : IsPullback (pullback.fst f (X.fromSpecStalk x))
      (pullback.snd f (X.fromSpecStalk x)) f (φ ≫ U.ι) := by
    rw [hfs]; exact IsPullback.of_hasPullback _ _
  have h₁ := IsPullback.of_right' hs ht
  have hgeo : IsPullback
      (ht.lift (pullback.fst f (X.fromSpecStalk x))
        (pullback.snd f (X.fromSpecStalk x) ≫ φ)
        (by rw [hs.w, Category.assoc]) ≫ hV.isoSpec.hom)
      (pullback.snd f (X.fromSpecStalk x))
      (Spec.map (f.app U)) (Spec.map (X.presheaf.germ U x hxU)) :=
    h₁.of_iso (Iso.refl _) hV.isoSpec (Iso.refl _) hU.isoSpec (by simp) (by simp)
      (by rw [hU.isoSpec_hom, hV.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality])
      (by rw [hU.isoSpec_hom, hφ, Iso.refl_hom, Category.id_comp,
        U.fromSpecStalkOfMem_toSpecΓ])
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let _ : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).stalk x) :=
    (f.base _* Y.presheaf).algebra_section_stalk (U := U) ⟨x, hxU⟩
  let _ : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let _ : Algebra (X.presheaf.stalk x) ((f.base _* Y.presheaf).stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom.toAlgebra
  let _ : Algebra Γ(X, U) ((f.base _* Y.presheaf).stalk x) :=
    (X.presheaf.germ U x hxU ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x)
      ((f.base _* Y.presheaf).stalk x) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).stalk x) :=
    .of_algebraMap_eq fun r ↦ congr($(TopCat.Presheaf.stalkFunctor_map_germ U x hxU f.c).hom r)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) ((f.base _* Y.presheaf).stalk x) :=
    pushforwardStalk_isLocalization f U hU x hxU
  have : Algebra.IsPushout Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (X.presheaf.stalk x)
      ((f.base _* Y.presheaf).stalk x) :=
    Algebra.isPushout_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _ _ _
  have halg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (X.presheaf.stalk x)
      ((f.base _* Y.presheaf).stalk x))
  exact ⟨hgeo.isoIsPullback _ _ halg, hgeo.isoIsPullback_hom_snd _ _ halg⟩

/-- The normalization over the spectrum of a local ring is the spectrum of the integral
closure in the product of its minimal-prime residue fields. -/
public lemma exists_iso_pullback_normalization_fromSpecStalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    let A := X.presheaf.stalk x
    letI : Algebra A (minimalPrimes.residueFieldProduct A) :=
      (minimalPrimes.residueFieldProductHom A).toAlgebra
    let B := integralClosure A (minimalPrimes.residueFieldProduct A)
    let ν := normalization X hX
    ∃ e : pullback ν (X.fromSpecStalk x) ≅ Spec (.of B),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
        pullback.snd ν (X.fromSpecStalk x) := by
  dsimp only
  let _ : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let _ : Algebra (X.presheaf.stalk x)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimes.residueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  obtain ⟨e₀, he₀⟩ := exists_iso_pullback_fromSpecStalk (normalization X hX) x
  have eAlg : normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) :=
    normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields X hX x
  let g : CommRingCat.of
        ↥(integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) ⟶
      normalizationPushforwardStalk X hX x :=
    CommRingCat.ofHom eAlg.symm.toRingEquiv.toRingHom
  let g' : normalizationPushforwardStalk X hX x ⟶ CommRingCat.of
      ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) :=
    CommRingCat.ofHom eAlg.toRingEquiv.toRingHom
  have h₁ : g ≫ g' = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ eAlg.apply_symm_apply a)
  have h₂ : g' ≫ g = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ eAlg.symm_apply_apply a)
  refine ⟨e₀ ≪≫
    { hom := Spec.map g
      inv := Spec.map g'
      hom_inv_id := Eq.trans (Spec.map_comp g' g).symm
        (Eq.trans (congrArg Spec.map h₂) (Spec.map_id _))
      inv_hom_id := Eq.trans (Spec.map_comp g g').symm
        (Eq.trans (congrArg Spec.map h₁) (Spec.map_id _)) }, ?_⟩
  change e₀.hom ≫ Spec.map g ≫
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) _)) = _
  refine Eq.trans (congrArg (fun k ↦ e₀.hom ≫ k) ?_) he₀
  refine Eq.trans (Spec.map_comp _ _).symm (congrArg Spec.map ?_)
  exact CommRingCat.hom_ext (RingHom.ext fun a ↦ eAlg.symm.commutes a)

end AlgebraicGeometry.Scheme

end
