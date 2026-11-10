module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting an étale morphism across a closed immersion

Let `i : Z ⟶ X` be a closed immersion of affine schemes and let `p : Z' ⟶ Z` be an étale
morphism with affine source. Then `p` is the base change along `i` of an étale morphism
`f : X' ⟶ X` with affine source. This is Stacks tag 057R, the geometric form of the
ring-theoretic lifting statement Stacks 04D1.

Dropping the affineness hypotheses costs a Zariski localization: for a closed immersion
`i : Z ⟶ X` of arbitrary schemes and an arbitrary étale `p : V ⟶ Z`, the scheme `V` has a
Zariski open cover each of whose members is, over `Z`, the base change along `i` of an étale
scheme over `X`.

## Main results

* `Stacks.Etale.exists_etale_lift_of_isClosedImmersion` produces the affine étale scheme over
  the ambient scheme together with an isomorphism identifying its base change with the given
  étale scheme over the closed subscheme.
* `Stacks.Etale.exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion` is the
  Zariski-local statement for arbitrary schemes.

## Implementation notes

The proof is a transcription of the affine algebra. Writing `R = Γ(X, ⊤)`, `S = Γ(Z, ⊤)` and
`T = Γ(Z', ⊤)`, the closed immersion makes `R → S` surjective with some kernel `I` and the
étale morphism makes `S → T` an étale ring map, so Stacks 04D1
(`etale_lift_along_surjection`) supplies an étale `R`-algebra `C` and a surjection `C → T`
with kernel `I C`. Mathlib's `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` identifies
`C ⧸ I C` with `(R ⧸ I) ⊗[R] C`, hence `T` with `S ⊗[R] C`, and
`AlgebraicGeometry.pullbackSpecIso` turns that ring isomorphism into the required isomorphism
of schemes. The three `isoSpec` isomorphisms transport the conclusion from the spectra of the
global sections back to the given schemes.

The assertion that the given scheme is the base change is expressed by an isomorphism to
Mathlib's chosen pullback whose composite with the first projection is the original structure
morphism. This is precisely an isomorphism of schemes over the closed subscheme.

The Zariski covering in the general statement is a `AlgebraicGeometry.Scheme.OpenCover` whose
index type lives in `max u v`: the covering is built from affine covers indexed in the scheme
universe `u`, and those indices are lifted so that the index universe is free. For each member
of the cover an isomorphism with the relevant fibre product is produced, and its compatibility
equation says that the isomorphism is one of schemes over the closed subscheme.

## References

* [Stacks Project, Tag 057R](https://stacks.math.columbia.edu/tag/057R)
* [Stacks Project, Tag 04FW](https://stacks.math.columbia.edu/tag/04FW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped AlgebraicGeometry TensorProduct

universe u v

namespace Stacks.Etale

/-- If `R → S` is surjective with kernel `I` and `ψ : C → T` is a surjective `R`-algebra map with
kernel `I C`, then `S ⊗[R] C ≃+* T`, compatibly with the structure map `S → T`. -/
theorem exists_ringEquiv_tensorProduct_of_ker_eq_map {R S C T : Type*} [CommRing R]
    [CommRing S] [CommRing C] [CommRing T] [Algebra R S] [Algebra R C] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (hRS : Function.Surjective (algebraMap R S))
    (ψ : C →ₐ[R] T) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : C →+* T) = (RingHom.ker (algebraMap R S)).map (algebraMap R C)) :
    ∃ e : S ⊗[R] C ≃+* T,
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap S T := by
  classical
  let I : Ideal R := RingHom.ker (algebraMap R S)
  let eRS : (R ⧸ I) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hRS) fun _ => rfl
  let eTen := Algebra.TensorProduct.congr eRS.symm (AlgEquiv.refl (R := R) (A₁ := C))
  let eQuot := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  have hker' : RingHom.ker ψ.toRingHom = I.map (algebraMap R C) := by simpa using hker
  let ePsi : C ⧸ I.map (algebraMap R C) ≃+* T :=
    (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have hePsi_mk (c : C) : ePsi (Ideal.Quotient.mk (I.map (algebraMap R C)) c) = ψ c := by
    change (RingHom.quotientKerEquivOfSurjective hψ)
        ((Ideal.quotEquivOfEq hker'.symm) (Ideal.Quotient.mk (I.map (algebraMap R C)) c)) = ψ c
    rw [Ideal.quotEquivOfEq_mk hker'.symm, RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  refine ⟨eTen.toRingEquiv.trans (eQuot.toRingEquiv.symm.trans ePsi), ?_⟩
  ext s
  obtain ⟨r, rfl⟩ := hRS s
  have ht : eTen.toRingEquiv
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] C) (algebraMap R S r)) =
      Ideal.Quotient.mk I r ⊗ₜ[R] (1 : C) := by
    simp [eTen]
  have hquot : eQuot.toRingEquiv.symm (Ideal.Quotient.mk I r ⊗ₜ[R] (1 : C)) =
      Ideal.Quotient.mk (I.map (algebraMap R C)) (algebraMap R C r) := by
    apply eQuot.toRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    change (Ideal.Quotient.mk I r ⊗ₜ[R] (1 : C)) =
      eQuot (Ideal.Quotient.mk (I.map (algebraMap R C)) (algebraMap R C r))
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    simpa only [Ideal.Quotient.algebraMap_eq] using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := R ⧸ I) (B := C) r)
  change (eTen.toRingEquiv.trans (eQuot.toRingEquiv.symm.trans ePsi))
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] C) (algebraMap R S r)) =
    algebraMap S T (algebraMap R S r)
  rw [RingEquiv.trans_apply, ht, RingEquiv.trans_apply, hquot, hePsi_mk, AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply R S T r

/-- A ring isomorphism `S ⊗[R] C ≃+* T` over `S` identifies `Spec T` with the fibre product
`Spec S ×_{Spec R} Spec C`, over `Spec S`. -/
theorem exists_iso_pullback_spec_of_ringEquiv {R S C T : Type u} [CommRing R] [CommRing S]
    [CommRing C] [CommRing T] [Algebra R S] [Algebra R C] [Algebra S T]
    (e : S ⊗[R] C ≃+* T)
    (he : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap S T) :
    ∃ e' : AlgebraicGeometry.Spec (.of T) ≅ pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))),
      e'.hom ≫ pullback.fst _ _ =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  refine ⟨AlgebraicGeometry.Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫
    (AlgebraicGeometry.pullbackSpecIso R S C).symm, ?_⟩
  dsimp
  rw [Category.assoc, AlgebraicGeometry.pullbackSpecIso_inv_fst,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext he

/-- Let `Z → X` be a closed immersion of affine schemes and let `Z' → Z` be an
étale morphism with affine source. Then it is the pullback of an étale morphism
`X' → X` with affine source. -/
@[stacks 057R]
theorem exists_etale_lift_of_isClosedImmersion
    {Z X Z' : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (p : Z' ⟶ Z)
    [AlgebraicGeometry.IsAffine Z] [AlgebraicGeometry.IsAffine X]
    [AlgebraicGeometry.IsAffine Z'] [AlgebraicGeometry.IsClosedImmersion i]
    [AlgebraicGeometry.Etale p] :
    ∃ (X' : AlgebraicGeometry.Scheme.{u}) (f : X' ⟶ X),
      AlgebraicGeometry.IsAffine X' ∧ AlgebraicGeometry.Etale f ∧
        ∃ e : Z' ≅ pullback i f, e.hom ≫ pullback.fst i f = p := by
  classical
  let R := Γ(X, ⊤)
  let S := Γ(Z, ⊤)
  let T := Γ(Z', ⊤)
  let φ : R →+* S := i.appTop.hom
  let ψ₀ : S →+* T := p.appTop.hom
  have hφ : Function.Surjective φ :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hψ₀ : ψ₀.Etale :=
    (AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine
      (P := @AlgebraicGeometry.Etale)).mp ‹AlgebraicGeometry.Etale p›
  let : Algebra R S := φ.toAlgebra
  let : Algebra S T := ψ₀.toAlgebra
  have : Algebra.Etale S T := hψ₀
  let : Algebra R T := (ψ₀.comp φ).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨C, hC, hRC, hCE, ψ, hψ, hker⟩ := etale_lift_along_surjection R S T hφ
  let : CommRing C := hC
  let : Algebra R C := hRC
  obtain ⟨eRing, hleft⟩ := exists_ringEquiv_tensorProduct_of_ker_eq_map hφ ψ hψ hker
  let fC : AlgebraicGeometry.Scheme := AlgebraicGeometry.Spec (.of C)
  let f : fC ⟶ X :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ X.isoSpec.inv
  let i₀ : AlgebraicGeometry.Spec (.of S) ⟶ AlgebraicGeometry.Spec (.of R) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)
  let q₀ : fC ⟶ AlgebraicGeometry.Spec (.of R) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C))
  let p₀ : AlgebraicGeometry.Spec (.of T) ⟶ AlgebraicGeometry.Spec (.of S) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ₀)
  obtain ⟨eCoord, hcoord⟩ : ∃ e : AlgebraicGeometry.Spec (.of T) ≅ pullback i₀ q₀,
      e.hom ≫ pullback.fst i₀ q₀ = p₀ :=
    exists_iso_pullback_spec_of_ringEquiv eRing hleft
  let zIso := Z.isoSpec
  let xIso := X.isoSpec
  let z'Iso := Z'.isoSpec
  let m := pullback.map i f i₀ q₀ zIso.hom (𝟙 _) xIso.hom
    (AlgebraicGeometry.Scheme.isoSpec_hom_naturality i).symm (by simp [f, q₀, xIso])
  have : IsIso m := pullback.map_isIso i f i₀ q₀ zIso.hom (𝟙 _) xIso.hom _ _
  have hm : inv m ≫ pullback.fst i f = pullback.fst i₀ q₀ ≫ zIso.inv := by
    rw [IsIso.inv_comp_eq, ← Category.assoc]
    dsimp only [m, pullback.map]
    rw [pullback.lift_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpCoord : z'Iso.hom ≫ p₀ = p ≫ zIso.hom :=
    AlgebraicGeometry.Scheme.isoSpec_hom_naturality p
  refine ⟨fC, f, inferInstance, ?_, z'Iso ≪≫ eCoord ≪≫ (asIso m).symm, ?_⟩
  · have : AlgebraicGeometry.Etale q₀ :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
        ((RingHom.etale_algebraMap (R := ↑R) (S := C)).2 hCE)
    infer_instance
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hm,
      reassoc_of% hcoord, reassoc_of% hpCoord, Iso.hom_inv_id, Category.comp_id]

open AlgebraicGeometry in
/-- Let `i : Z ⟶ X` be a closed immersion and `o : U ⟶ X` an open immersion with affine source.
An étale `q : W ⟶ U ×_X Z` with affine source is, over `Z`, the base change along `i` of an
étale scheme over `X`. -/
theorem exists_etale_iso_pullback_of_isOpenImmersion {X Z U W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (o : U ⟶ X) [IsOpenImmersion o] [IsAffine U] [IsAffine W]
    (q : W ⟶ pullback o i) [Etale q] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), Etale g ∧
      ∃ e : W ≅ pullback g i, e.hom ≫ pullback.snd g i = q ≫ pullback.snd o i := by
  obtain ⟨Y, g, -, hg, e₀, he₀⟩ := exists_etale_lift_of_isClosedImmersion (pullback.fst o i) q
  refine ⟨Y, g ≫ o, inferInstance,
    e₀ ≪≫ pullbackSymmetry _ g ≪≫ pullbackRightPullbackFstIso o i g, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd]
  rw [← Category.assoc (pullbackSymmetry _ g).hom, pullbackSymmetry_hom_comp_snd,
    ← Category.assoc, he₀]

open AlgebraicGeometry in
/-- **Stacks Project, Tag 04FW.** If `i : Z ⟶ X` is a closed immersion and `p : V ⟶ Z` is
étale, then `V` has a Zariski open cover whose members are, over `Z`, base changes along `i`
of étale schemes over `X`. -/
@[stacks 04FW]
theorem exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion
    {X Z V : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] :
    ∃ (W : Scheme.OpenCover.{max u v, u} V)
      (U : W.I₀ → AlgebraicGeometry.Scheme.{u}) (f : ∀ j, U j ⟶ X),
      (∀ j, Etale (f j)) ∧
        ∀ j, ∃ e : W.X j ≅ pullback (f j) i,
          e.hom ≫ pullback.snd (f j) i = W.f j ≫ p := by
  classical
  let 𝒳 := X.affineOpenCover
  let C : V.OpenCover := {
    toPreZeroHypercover := {
      I₀ := 𝒳.I₀
      X := fun j => pullback (p ≫ i) (𝒳.openCover.f j)
      f := fun j => pullback.fst (p ≫ i) (𝒳.openCover.f j)
    }
    mem₀ :=
      Precoverage.mem_coverings_of_isPullback 𝒳.openCover.f 𝒳.openCover.mem₀
        (p ≫ i) (fun j => pullback.fst (p ≫ i) (𝒳.openCover.f j))
        (fun j => pullback.snd (p ≫ i) (𝒳.openCover.f j))
        (fun j => IsPullback.of_hasPullback (p ≫ i) (𝒳.openCover.f j))
  }
  let W₀ := C.affineRefinement.openCover
  let W : Scheme.OpenCover.{max u v, u} V := {
    toPreZeroHypercover := {
      I₀ := ULift.{v} W₀.I₀
      X := fun j => W₀.X j.down
      f := fun j => W₀.f j.down
    }
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun j => W₀.map_prop j.down⟩
      obtain ⟨i, y, hy⟩ := W₀.exists_eq x
      exact ⟨ULift.up i, y, hy⟩
  }
  let q (j : W.I₀) := (C.fromAffineRefinement).s₀ j.down
  let x (j : W.I₀) : AlgebraicGeometry.Scheme.{u} := 𝒳.openCover.X (q j)
  let xToX (j : W.I₀) : x j ⟶ X := 𝒳.openCover.f (q j)
  let zToZ (j : W.I₀) : pullback (xToX j) i ⟶ Z := pullback.snd (xToX j) i
  let nestedIso (j : W.I₀) : C.X (q j) ≅ pullback (zToZ j) p :=
    pullbackSymmetry (p ≫ i) (xToX j) ≪≫ (pullbackLeftPullbackSndIso (xToX j) i p).symm
  let pLocal (j : W.I₀) : W.X j ⟶ pullback (xToX j) i :=
    (C.fromAffineRefinement).h₀ j.down ≫ (nestedIso j).hom ≫ pullback.fst (zToZ j) p
  have hNested (j : W.I₀) :
      (nestedIso j).hom ≫ pullback.fst (zToZ j) p ≫ zToZ j =
        pullback.fst (p ≫ i) (xToX j) ≫ p := by
    simp [nestedIso, zToZ]
  have hpLocal (j : W.I₀) : pLocal j ≫ zToZ j = W.f j ≫ p := by
    dsimp [pLocal]
    simp only [Category.assoc, hNested]
    rw [← Category.assoc, (C.fromAffineRefinement).w₀ j.down]
  have hExist (j : W.I₀) : ∃ (Y : Scheme.{u}) (g : Y ⟶ X), Etale g ∧
      ∃ e : W.X j ≅ pullback g i, e.hom ≫ pullback.snd g i = W.f j ≫ p := by
    have : IsAffine (W.X j) := Scheme.isAffine_affineOpenCover V C.affineRefinement j.down
    have : IsAffine (x j) := Scheme.isAffine_affineOpenCover X 𝒳 (q j)
    have : IsOpenImmersion (xToX j) := 𝒳.map_prop (q j)
    obtain ⟨Y, g, hg, e, he⟩ := exists_etale_iso_pullback_of_isOpenImmersion i (xToX j) (pLocal j)
    exact ⟨Y, g, hg, e, he.trans (hpLocal j)⟩
  choose U f hf e he using hExist
  exact ⟨W, U, f, hf, fun j => ⟨e j, he j⟩⟩

end Stacks.Etale

end
