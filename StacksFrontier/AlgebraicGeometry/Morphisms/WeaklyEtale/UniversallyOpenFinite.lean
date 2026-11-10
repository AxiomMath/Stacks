module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal openness of a finite algebra from one polynomial test

For a finite algebra generated as a module by `b i`, universal openness of its spectrum map is
equivalent to openness of the image of the principal open cut out by the universal linear
combination of the generators.

## Main results

* `AlgebraicGeometry.universallyOpen_iff_isOpen_image_basicOpen_linearCombination` gives the
  characterization.

## Implementation notes

The polynomial rings have variables indexed by `Fin d`. The image of the principal open is
expressed on prime spectra via the map on polynomial rings; this is the underlying topological
map of the corresponding affine-scheme morphism.

## References

* [Stacks Project, Tag 0F33](https://stacks.math.columbia.edu/tag/0F33)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry

private lemma isPullback_image_preimage_eq
    {X Y X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} {i₁ : X' ⟶ X} {i₂ : Y' ⟶ Y} {f : X ⟶ Y}
    (hp : IsPullback f' i₁ i₂ f) (V : Set X) :
    f' '' (i₁ ⁻¹' V) = i₂ ⁻¹' (f '' V) := by
  ext y
  constructor
  · rintro ⟨x', hx, rfl⟩
    refine ⟨i₁ x', hx, ?_⟩
    simpa only [← Scheme.Hom.comp_apply] using (congr($(hp.w) x')).symm
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hzy, hzx⟩ := Scheme.Pullback.exists_preimage_pullback y x hxy.symm
    refine ⟨hp.isoPullback.inv z, ?_, ?_⟩
    · change i₁ (hp.isoPullback.inv z) ∈ V
      rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_snd]
      simpa only [hzx] using hx
    · rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst]
      exact hzy

private lemma tensor_eq_sum_of_span_generators
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (d : ℕ) (b : Fin d → B)
    (hb : Submodule.span A (Set.range b) = ⊤)
    (z : C ⊗[A] B) :
    ∃ a : Fin d → C, z = ∑ i, a i ⊗ₜ[A] b i := by
  classical
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hy
      refine ⟨a + a', ?_⟩
      simp [Finset.sum_add_distrib, TensorProduct.add_tmul]
  | tmul c y =>
      have hy : y ∈ Submodule.span A (Set.range b) := hb ▸ Submodule.mem_top
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hy
      refine ⟨fun i => c * algebraMap A C (a i), ?_⟩
      rw [← ha]
      simp only [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [TensorProduct.tmul_smul]
      simp [Algebra.smul_def, mul_comm]

private lemma eval_polynomial_square_isPushout
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (d : ℕ)
    (a : Fin d → C) :
    IsPushout
      (CommRingCat.ofHom (MvPolynomial.aeval a).toRingHom)
      (CommRingCat.ofHom (MvPolynomial.map (algebraMap A B)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        C →ₐ[A] C ⊗[A] B).toRingHom)
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        (Algebra.TensorProduct.includeRight.toRingHom)
        (fun i => (Algebra.TensorProduct.includeLeft :
          C →ₐ[A] C ⊗[A] B) (a i)))) := by
  let R := MvPolynomial (Fin d) A
  let S := MvPolynomial (Fin d) B
  let D := C ⊗[A] B
  let φ : R →ₐ[A] C := MvPolynomial.aeval a
  let q : S →+* D := MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight.toRingHom)
    (fun i => (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] B) (a i))
  let : Algebra R C := φ.toRingHom.toAlgebra
  let : IsScalarTower A R C :=
    IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun x ↦ (φ.commutes x).symm
  let : Algebra R S := MvPolynomial.algebraMvPolynomial
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra C D := Algebra.TensorProduct.leftAlgebra
  let : Algebra S D := q.toAlgebra
  let : IsScalarTower A C D :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := C) (A := D) fun x =>
      (Algebra.TensorProduct.includeLeft.commutes x).symm
  let ρ : R →ₐ[A] D := (Algebra.TensorProduct.includeLeft : C →ₐ[A] D).comp φ
  let : Algebra R D := Algebra.compHom D φ.toRingHom
  let : IsScalarTower R C D := IsScalarTower.of_compHom R C D
  let : IsScalarTower B S D :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := S) (A := D) <| RingHom.ext fun x ↦ by
      change (Algebra.TensorProduct.includeRight : B →ₐ[A] D) x = q (MvPolynomial.C x)
      rw [MvPolynomial.eval₂Hom_C]
      rfl
  let : IsScalarTower A S D :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := D) fun x => by
      rw [IsScalarTower.algebraMap_apply A B S x]
      change (algebraMap A D) x = q (MvPolynomial.C (algebraMap A B x))
      rw [MvPolynomial.eval₂Hom_C]
      exact (Algebra.TensorProduct.includeRight.commutes x).symm
  let : IsScalarTower R S D :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := D) <| by
      change ((Algebra.TensorProduct.includeLeft : C →ₐ[A] D).toRingHom.comp
        φ.toRingHom) = q.comp (MvPolynomial.map (algebraMap A B))
      apply MvPolynomial.ringHom_ext
      · intro r
        dsimp [φ, q]
        rw [MvPolynomial.aeval_C, MvPolynomial.map_C,
          MvPolynomial.eval₂Hom_C]
        change (Algebra.TensorProduct.includeLeft : C →ₐ[A] D)
            (algebraMap A C r) =
          (Algebra.TensorProduct.includeRight : B →ₐ[A] D) (algebraMap A B r)
        rw [Algebra.TensorProduct.includeLeft.commutes,
          Algebra.TensorProduct.includeRight.commutes]
      · intro i
        dsimp [φ, q]
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X,
          MvPolynomial.eval₂Hom_X']
  let : Algebra.IsPushout A B R S := by infer_instance
  let : Algebra.IsPushout A R B S :=
    Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A B R S)
  have hRS : IsScalarTower R S D := inferInstance
  have hRC : IsScalarTower R C D := inferInstance
  have hbig : Algebra.IsPushout A C B D := by
    dsimp [D]
    infer_instance
  have hpush :=
    (@Algebra.IsPushout.comp_iff A R _ _ _ C _ _ _ _ B S _ _ _ _ _ _ _ _ D
      _ _ _ _ _ _ _ hRC hRS _ _ _ _).mp hbig
  exact @CommRingCat.isPushout_of_isPushout R C S D _ _ _ _ _ _ _ _ _ hRS hRC hpush

/-- Universal openness of a finite algebra is detected by the image of the
principal open defined by a universal linear combination of module generators. -/
@[stacks 0F33]
theorem universallyOpen_iff_isOpen_image_basicOpen_linearCombination
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (d : ℕ) (b : Fin d → B) (hb : Submodule.span A (Set.range b) = ⊤) :
    UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      IsOpen (PrimeSpectrum.comap (MvPolynomial.map (σ := Fin d) (algebraMap A B)) ''
        (PrimeSpectrum.basicOpen
          (∑ i : Fin d, MvPolynomial.C (b i) * MvPolynomial.X i) :
            Set (PrimeSpectrum (MvPolynomial (Fin d) B)))) := by
  constructor
  · intro h
    let R := MvPolynomial (Fin d) A
    let S := MvPolynomial (Fin d) B
    let : Algebra R S := MvPolynomial.algebraMvPolynomial
    let f₁ : CommRingCat.of A ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (algebraMap A R)
    let g₁ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (algebraMap A B)
    let i₁ : CommRingCat.of R ⟶ CommRingCat.of S :=
      CommRingCat.ofHom (algebraMap R S)
    let j₁ : CommRingCat.of B ⟶ CommRingCat.of S :=
      CommRingCat.ofHom (algebraMap B S)
    have hpush : IsPushout f₁ g₁ i₁ j₁ :=
      CommRingCat.isPushout_of_isPushout A R B S
    have hp : IsPullback (Spec.map i₁) (Spec.map j₁) (Spec.map f₁) (Spec.map g₁) :=
      isPullback_SpecMap_of_isPushout f₁ g₁ i₁ j₁ hpush
    have hopen : IsOpenMap (Spec.map i₁) :=
      h.universally_isOpenMap (Spec.map j₁) (Spec.map f₁) (Spec.map i₁) hp
    change IsOpen (PrimeSpectrum.comap (MvPolynomial.map (algebraMap A B)) ''
        (PrimeSpectrum.basicOpen
          (∑ i : Fin d, MvPolynomial.C (b i) * MvPolynomial.X i) :
            Set (PrimeSpectrum (MvPolynomial (Fin d) B))))
    exact hopen _ PrimeSpectrum.isOpen_basicOpen
  · intro hU
    refine ⟨MorphismProperty.universally_mk' _ _ fun {T} f _ ↦ ?_⟩
    wlog hT : ∃ C, T = Spec C generalizing T
    · refine (IsZariskiLocalAtTarget.iff_of_openCover T.affineCover).mpr fun i ↦ ?_
      refine (MorphismProperty.cancel_left_of_respectsIso _
        ((CategoryTheory.Limits.pullbackRightPullbackFstIso ..).inv ≫
          (CategoryTheory.Limits.pullbackSymmetry ..).hom) _).mp ?_
      simpa [Scheme.Cover.pullbackHom] using! this _ _ ⟨_, rfl⟩
    obtain ⟨C, rfl⟩ := hT
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective f
    algebraize [ψ.hom]
    refine (MorphismProperty.cancel_left_of_respectsIso _ (pullbackSpecIso A C B).inv _).mp ?_
    convert_to! topologically _ (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] B).toRingHom))
    · exact pullbackSpecIso_inv_fst ..
    change IsOpenMap (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] B).toRingHom)
    rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro _ ⟨g, rfl⟩
    classical
    obtain ⟨a, ha⟩ := tensor_eq_sum_of_span_generators
      (A := A) (B := B) (C := C) d b hb g
    let R := MvPolynomial (Fin d) A
    let S := MvPolynomial (Fin d) B
    let D := C ⊗[A] B
    let p : S := ∑ i : Fin d, MvPolynomial.C (b i) * MvPolynomial.X i
    let φ : R →ₐ[A] C := MvPolynomial.aeval a
    let q : S →+* D := MvPolynomial.eval₂Hom
      Algebra.TensorProduct.includeRight.toRingHom
      (fun i : Fin d =>
        (Algebra.TensorProduct.includeLeft : C →ₐ[A] D) (a i))
    have hq : q p = g := by
      rw [ha]
      simp only [p, q, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      change ((Algebra.TensorProduct.includeRight : B →ₐ[A] D) (b i)) *
        ((Algebra.TensorProduct.includeLeft : C →ₐ[A] D) (a i)) = a i ⊗ₜ[A] b i
      rw [Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
    have hp : IsPullback
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : C →ₐ[A] D).toRingHom))
        (Spec.map (CommRingCat.ofHom q))
        (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap A B)))) :=
      isPullback_SpecMap_of_isPushout _ _ _ _ (eval_polynomial_square_isPushout d a)
    let hV : Set (Spec (CommRingCat.of S)) := by
      rw [Spec_carrier]
      exact ↑(PrimeSpectrum.basicOpen (show ↑(CommRingCat.of S) from p))
    have himage := isPullback_image_preimage_eq hp hV
    have hpre : PrimeSpectrum.comap q ⁻¹' ↑(PrimeSpectrum.basicOpen p) =
        ↑(PrimeSpectrum.basicOpen g) := by
      calc
        PrimeSpectrum.comap q ⁻¹' ↑(PrimeSpectrum.basicOpen p) =
            ↑(TopologicalSpace.Opens.comap
              ⟨PrimeSpectrum.comap q, PrimeSpectrum.continuous_comap q⟩
              (PrimeSpectrum.basicOpen p)) := rfl
        _ = ↑(PrimeSpectrum.basicOpen (q p)) :=
          congrArg SetLike.coe (PrimeSpectrum.comap_basicOpen q p)
        _ = ↑(PrimeSpectrum.basicOpen g) := by rw [hq]
    have hmap (R S : CommRingCat) (f : R ⟶ S) :
        ⇑(Spec.map f) = PrimeSpectrum.comap f.hom := funext (Spec.map_apply f)
    have hset :
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeft : C →ₐ[A] D).toRingHom ''
          PrimeSpectrum.basicOpen g =
      PrimeSpectrum.comap φ.toRingHom ⁻¹'
          (PrimeSpectrum.comap (MvPolynomial.map (algebraMap A B)) ''
            PrimeSpectrum.basicOpen p) := by
      dsimp [hV] at himage
      rw [hmap, hmap, hmap, hmap] at himage
      change PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeft : C →ₐ[A] D).toRingHom ''
          (PrimeSpectrum.comap q ⁻¹' ↑(PrimeSpectrum.basicOpen p)) =
        PrimeSpectrum.comap φ.toRingHom ⁻¹'
          (PrimeSpectrum.comap (MvPolynomial.map (σ := Fin d) (algebraMap A B)) ''
            ↑(PrimeSpectrum.basicOpen p)) at himage
      simpa only [hpre] using himage
    rw [hset]
    exact (PrimeSpectrum.continuous_comap φ.toRingHom).isOpen_preimage _ hU

end AlgebraicGeometry
