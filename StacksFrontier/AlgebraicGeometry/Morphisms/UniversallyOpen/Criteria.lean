module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for universal openness

A morphism of schemes is universally open as soon as its base change along every morphism which
is locally of finite presentation is open. In fact it suffices to test openness after adjoining
finitely many affine coordinates.

## Main results

* `AlgebraicGeometry.universallyOpen_iff_forall_isOpenMap_pullback_snd` tests universal openness
  on base changes along morphisms locally of finite presentation.
* `AlgebraicGeometry.universallyOpen_iff_forall_isOpenMap_affineSpaceMap` tests universal
  openness on the maps of affine spaces over the source and the target.

## Implementation notes

The first equivalence identifies parts (1) and (2) of the source, and the second identifies
parts (1) and (3). Affine space of dimension `n` over a scheme in `Scheme.{u}` is indexed by
`ULift.{u} (Fin n)`.

## References

* [Stacks Project, Tag 0F31](https://stacks.math.columbia.edu/tag/0F31)
-/

public section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

universe u

/-- For an `A`-algebra `A'` and an `A`-algebra `B`, if every polynomial extension
`A[x_1, …, x_n] → B[x_1, …, x_n]` has open spectral map, then so has `A' → A' ⊗[A] B`. -/
private lemma affine_isOpenMap_tensorProduct_includeLeft_of_forall_isOpenMap_mvPolynomialMap
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (h : ∀ n : ℕ,
      IsOpenMap (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (σ := ULift.{u} (Fin n)) (algebraMap A B))))) :
    IsOpenMap (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := B)))) := by
  classical
  change IsOpenMap (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom
    (R := A) (A := A') (B := B)))
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨g, rfl⟩
  obtain ⟨k, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq (R := A) g
  let p : MvPolynomial (ULift.{u} (Fin k)) B :=
    ∑ i : Fin k, MvPolynomial.C (b i) * MvPolynomial.X (ULift.up i)
  let evA : MvPolynomial (ULift.{u} (Fin k)) A →+* A' :=
    MvPolynomial.eval₂Hom (algebraMap A A') (fun i : ULift.{u} (Fin k) => a i.down)
  let evB : MvPolynomial (ULift.{u} (Fin k)) B →+* A' ⊗[A] B :=
    MvPolynomial.eval₂Hom Algebra.TensorProduct.includeRight.toRingHom
      (fun i : ULift.{u} (Fin k) => a i.down ⊗ₜ[A] (1 : B))
  have hp : evB p = g := by
    simp only [p, map_sum, evB, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rw [hab]
    simp [Algebra.TensorProduct.includeRight, mul_comm]
  let : Algebra (MvPolynomial (ULift.{u} (Fin k)) A) (MvPolynomial (ULift.{u} (Fin k)) B) :=
    MvPolynomial.algebraMvPolynomial (R := A) (S := B)
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.includeRight.toAlgebra
  let : Algebra (MvPolynomial (ULift.{u} (Fin k)) A) A' := evA.toAlgebra
  let : Algebra (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B) := evB.toAlgebra
  let : Algebra (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B) :=
    (Algebra.TensorProduct.includeLeftRingHom.comp evA).toAlgebra
  let : SMul A (A' ⊗[A] B) := (inferInstance : Algebra A (A' ⊗[A] B)).toSMul
  let : SMul (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B) :=
    (inferInstance : Algebra (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B)).toSMul
  let : IsScalarTower A (MvPolynomial (ULift.{u} (Fin k)) A) A' := by
    refine .of_algebraMap_eq fun x => ?_
    change algebraMap A A' x = evA (MvPolynomial.C x)
    simp [evA]
  let : IsScalarTower A (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B) := by
    refine .of_algebraMap_eq fun x => ?_
    change algebraMap A (A' ⊗[A] B) x = evB (MvPolynomial.C ((algebraMap A B) x))
    simp [evB]
  let : IsScalarTower A (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B) := by
    refine IsScalarTower.of_algebraMap_eq (R := A) (S := MvPolynomial (ULift.{u} (Fin k)) A)
      (A := A' ⊗[A] B) fun x => ?_
    change algebraMap A (A' ⊗[A] B) x =
      Algebra.TensorProduct.includeLeftRingHom (evA (MvPolynomial.C x))
    simp [evA]
  let : IsScalarTower A (MvPolynomial (ULift.{u} (Fin k)) A)
      (MvPolynomial (ULift.{u} (Fin k)) B) := by
    refine .of_algebraMap_eq fun x => ?_
    change algebraMap A (MvPolynomial (ULift.{u} (Fin k)) B) x =
      MvPolynomial.map (algebraMap A B) (MvPolynomial.C x)
    simp
  let : IsScalarTower (MvPolynomial (ULift.{u} (Fin k)) A) (MvPolynomial (ULift.{u} (Fin k)) B)
      (A' ⊗[A] B) := by
    refine IsScalarTower.of_algebraMap_eq (R := MvPolynomial (ULift.{u} (Fin k)) A)
      (S := MvPolynomial (ULift.{u} (Fin k)) B) (A := A' ⊗[A] B) fun x => ?_
    have hmaps : (algebraMap (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B)).comp
        (algebraMap (MvPolynomial (ULift.{u} (Fin k)) A) (MvPolynomial (ULift.{u} (Fin k)) B)) =
        algebraMap (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B) := by
      apply MvPolynomial.ringHom_ext'
      · ext a
        change (algebraMap (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B))
            (MvPolynomial.map (algebraMap A B) (MvPolynomial.C a)) =
          (algebraMap (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B)) (MvPolynomial.C a)
        rw [MvPolynomial.map_C, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        change evB (MvPolynomial.C ((algebraMap A B) a)) =
          Algebra.TensorProduct.includeLeftRingHom (evA (MvPolynomial.C a))
        simp [evA, evB]
      · intro i
        change (algebraMap (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B))
            (MvPolynomial.map (algebraMap A B) (MvPolynomial.X i)) =
          (algebraMap (MvPolynomial (ULift.{u} (Fin k)) A) (A' ⊗[A] B)) (MvPolynomial.X i)
        rw [MvPolynomial.map_X, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        change evB (MvPolynomial.X i) =
          Algebra.TensorProduct.includeLeftRingHom (evA (MvPolynomial.X i))
        simp [evA, evB]
    exact (DFunLike.congr_fun hmaps x).symm
  let : IsScalarTower (MvPolynomial (ULift.{u} (Fin k)) A) A' (A' ⊗[A] B) :=
    IsScalarTower.of_algebraMap_eq (R := MvPolynomial (ULift.{u} (Fin k)) A) (S := A')
      (A := A' ⊗[A] B) fun _ => rfl
  let : IsScalarTower B (MvPolynomial (ULift.{u} (Fin k)) B) (A' ⊗[A] B) := by
    refine IsScalarTower.of_algebraMap_eq (R := B) (S := MvPolynomial (ULift.{u} (Fin k)) B)
      (A := A' ⊗[A] B) fun x => ?_
    simp [evB, RingHom.algebraMap_toAlgebra]
  let : Algebra.IsPushout (MvPolynomial (ULift.{u} (Fin k)) A)
      (MvPolynomial (ULift.{u} (Fin k)) B) A' (A' ⊗[A] B) :=
    Algebra.IsPushout.symm
      ((Algebra.IsPushout.comp_iff (R := A) (S := MvPolynomial (ULift.{u} (Fin k)) A)
        (R' := B) (S' := MvPolynomial (ULift.{u} (Fin k)) B) (T := A')
        (T' := A' ⊗[A] B)).mp inferInstance)
  have hpull := isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B)))
    (CommRingCat.ofHom evA) (CommRingCat.ofHom evB)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := B)))
    (CommRingCat.isPushout_of_isPushout (MvPolynomial (ULift.{u} (Fin k)) A)
      (MvPolynomial (ULift.{u} (Fin k)) B) A' (A' ⊗[A] B))
  let W : Set (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin k)) B))) := by
    rw [Spec_carrier]
    exact ↑(PrimeSpectrum.basicOpen
      (show ↑(CommRingCat.of (MvPolynomial (ULift.{u} (Fin k)) B)) from p))
  have himage := Scheme.image_preimage_eq_of_isPullback hpull W
  have hpre : PrimeSpectrum.comap evB ⁻¹' ↑(PrimeSpectrum.basicOpen p) =
      ↑(PrimeSpectrum.basicOpen g) := by
    calc
      PrimeSpectrum.comap evB ⁻¹' ↑(PrimeSpectrum.basicOpen p) =
          ↑(TopologicalSpace.Opens.comap
            ⟨PrimeSpectrum.comap evB, PrimeSpectrum.continuous_comap evB⟩
            (PrimeSpectrum.basicOpen p)) := rfl
      _ = ↑(PrimeSpectrum.basicOpen (evB p)) :=
        congrArg SetLike.coe (PrimeSpectrum.comap_basicOpen evB p)
      _ = ↑(PrimeSpectrum.basicOpen g) := by rw [hp]
  have hmap (R S : CommRingCat) (f : R ⟶ S) :
      ⇑(Spec.map f) = PrimeSpectrum.comap f.hom := funext (Spec.map_apply f)
  have hset :
      PrimeSpectrum.comap (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := B))).hom ''
          PrimeSpectrum.basicOpen g =
        PrimeSpectrum.comap (CommRingCat.ofHom evA).hom ⁻¹'
          (PrimeSpectrum.comap (CommRingCat.ofHom
          (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B))).hom ''
            PrimeSpectrum.basicOpen p) := by
    dsimp [W] at himage
    rw [hmap, hmap, hmap, hmap] at himage
    change PrimeSpectrum.comap (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := B))).hom ''
          (PrimeSpectrum.comap evB ⁻¹' ↑(PrimeSpectrum.basicOpen p)) =
        PrimeSpectrum.comap (CommRingCat.ofHom evA).hom ⁻¹'
          (PrimeSpectrum.comap (CommRingCat.ofHom
            (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B))).hom ''
            ↑(PrimeSpectrum.basicOpen p)) at himage
    simpa only [hpre] using himage
  change IsOpen (PrimeSpectrum.comap (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := B))).hom ''
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (A' ⊗[A] B))))
  rw [hset]
  have hpoly : IsOpen
      (PrimeSpectrum.comap (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B)) ''
        PrimeSpectrum.basicOpen p) := by
    have hh := h k W (by
      dsimp [W]
      exact (PrimeSpectrum.basicOpen p).2)
    change IsOpen (⇑(Spec.map (CommRingCat.ofHom
      (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B)))) '' W) at hh
    rw [hmap] at hh
    dsimp [W] at hh
    change IsOpen (PrimeSpectrum.comap (CommRingCat.ofHom
      (MvPolynomial.map (σ := ULift.{u} (Fin k)) (algebraMap A B))).hom ''
        PrimeSpectrum.basicOpen p) at hh
    exact hh
  exact (PrimeSpectrum.continuous_comap evA).isOpen_preimage _ hpoly

/-- If every base change of `f` along a morphism locally of finite presentation is open, then
every map of affine spaces induced by `f` is open. -/
private lemma forall_isOpenMap_affineSpaceMap_of_forall_isOpenMap_pullback_snd
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      LocallyOfFinitePresentation g → IsOpenMap (pullback.snd f g)) (n : ℕ) :
    IsOpenMap (AffineSpace.map (ULift.{u} (Fin n)) f) := by
  have hp := AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) f
  rw [← hp.isoPullback_hom_fst]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    hp.isoPullback.hom _).mpr ?_
  refine (MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    (pullbackSymmetry f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).hom _).mp ?_
  change IsOpenMap _
  simpa only [pullbackSymmetry_hom_comp_fst] using
    h _ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) inferInstance

/-- The morphism of affine schemes given by a ring map is universally open if every induced map
of affine `n`-spaces is open. -/
@[ega "IV 8.10.2" "special case"]
private lemma universallyOpen_specMap_of_forall_isOpenMap_affineSpaceMap
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (h : ∀ n : ℕ, IsOpenMap (AffineSpace.map (ULift.{u} (Fin n))
      (Spec.map (CommRingCat.ofHom φ)))) :
    UniversallyOpen (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra A B := φ.toAlgebra
  let φ' : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom φ
  have hpoly : ∀ n : ℕ, IsOpenMap (Spec.map (CommRingCat.ofHom
      (MvPolynomial.map (σ := ULift.{u} (Fin n)) φ))) := fun n =>
    (MorphismProperty.arrow_mk_iso_iff (topologically @IsOpenMap)
      (AffineSpace.mapSpecMap (n := ULift.{u} (Fin n)) φ')).mp (h n)
  rw [UniversallyOpen.eq]
  refine MorphismProperty.universally_mk' (topologically @IsOpenMap) (Spec.map φ') ?_
  intro T g
  wlog hT : ∃ A', T = Spec A' generalizing T
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
        (P := topologically @IsOpenMap) T.affineCover).mpr fun i ↦ ?_
    refine (MorphismProperty.cancel_left_of_respectsIso (topologically @IsOpenMap)
      ((pullbackRightPullbackFstIso ..).inv ≫ (pullbackSymmetry ..).hom) _).mp ?_
    simpa [Scheme.Cover.pullbackHom] using! this _ ⟨_, rfl⟩
  obtain ⟨A', rfl⟩ := hT
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ, ψ.hom]
  refine (MorphismProperty.cancel_left_of_respectsIso (topologically @IsOpenMap)
    (pullbackSpecIso A A' B).inv _).mp ?_
  convert_to! topologically _
    (Spec.map <| CommRingCat.ofHom (algebraMap A' (TensorProduct A A' B)))
  · exact pullbackSpecIso_inv_fst ..
  exact affine_isOpenMap_tensorProduct_includeLeft_of_forall_isOpenMap_mvPolynomialMap
    (by simpa using hpoly)

/-- A morphism of affine schemes is universally open if every induced map of affine `n`-spaces
is open. -/
@[ega "IV 8.10.2" "affine source and target"]
private lemma universallyOpen_of_forall_isOpenMap_affineSpaceMap_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (h : ∀ n : ℕ, IsOpenMap (AffineSpace.map (ULift.{u} (Fin n)) f)) :
    UniversallyOpen f := by
  let φ : Γ(S, ⊤) →+* Γ(X, ⊤) := f.appTop.hom
  have eSpec : Arrow.mk f ≅ Arrow.mk (Spec.map (CommRingCat.ofHom φ)) :=
    Arrow.isoMk X.isoSpec S.isoSpec (Scheme.isoSpec_hom_naturality f)
  refine (MorphismProperty.arrow_mk_iso_iff (P := @UniversallyOpen) eSpec).mpr
    (universallyOpen_specMap_of_forall_isOpenMap_affineSpaceMap φ fun n => ?_)
  have hcomm :
      AffineSpace.map (ULift.{u} (Fin n)) X.isoSpec.hom ≫
          AffineSpace.map (ULift.{u} (Fin n)) (Spec.map (CommRingCat.ofHom φ)) =
        AffineSpace.map (ULift.{u} (Fin n)) f ≫
          AffineSpace.map (ULift.{u} (Fin n)) S.isoSpec.hom := by
    rw [← AffineSpace.map_comp, ← AffineSpace.map_comp]
    exact congrArg (AffineSpace.map (ULift.{u} (Fin n))) (Scheme.isoSpec_hom_naturality f)
  exact (MorphismProperty.arrow_mk_iso_iff (topologically @IsOpenMap)
    (Arrow.isoMk ((AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin n)))).mapIso X.isoSpec)
      ((AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin n)))).mapIso S.isoSpec)
      hcomm)).mp (h n)

/-- A morphism of schemes is universally open if every induced map of affine `n`-spaces is
open. -/
@[ega "IV 8.10.2"]
private lemma universallyOpen_of_forall_isOpenMap_affineSpaceMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ n : ℕ, IsOpenMap (AffineSpace.map (ULift.{u} (Fin n)) f)) :
    UniversallyOpen f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyOpen) S.affineCover]
  intro j
  let p := (S.affineCover.pullback₁ f).X j
  let i₁ : p ⟶ X := (S.affineCover.pullback₁ f).f j
  let i₂ : p ⟶ S.affineCover.X j := S.affineCover.pullbackHom f j
  have hp : IsOpenImmersion i₁ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (S.affineCover.f j)).flip
      (S.affineCover.map_prop j)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @UniversallyOpen) p.affineCover]
  intro k
  let : IsAffine (S.affineCover.X j) := by dsimp [Scheme.affineCover]; infer_instance
  let iW : p.affineCover.X k ⟶ p := p.affineCover.f k
  let gV : p.affineCover.X k ⟶ S.affineCover.X j := iW ≫ i₂
  let iX : p.affineCover.X k ⟶ X := iW ≫ i₁
  have hfactor : iX ≫ f = gV ≫ S.affineCover.f j := by
    simp [iX, gV, i₁, i₂, Category.assoc]
  change UniversallyOpen gV
  refine universallyOpen_of_forall_isOpenMap_affineSpaceMap_of_isAffine gV fun n => ?_
  have hopenImm {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g] :
      IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin n)) g) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map g).flip ‹_›
  have := hopenImm iX
  have := hopenImm (S.affineCover.f j)
  have hopen : IsOpenMap (AffineSpace.map (ULift.{u} (Fin n)) (iX ≫ f)) := by
    rw [AffineSpace.map_comp]
    exact (h n).comp (AffineSpace.map (ULift.{u} (Fin n)) iX).isOpenEmbedding.isOpenMap
  rw [hfactor, AffineSpace.map_comp] at hopen
  refine (Topology.IsOpenEmbedding.isOpenMap_iff
    (f := ⇑(AffineSpace.map (ULift.{u} (Fin n)) gV))
    (g := ⇑(AffineSpace.map (ULift.{u} (Fin n)) (S.affineCover.f j)))
    (AffineSpace.map (ULift.{u} (Fin n)) (S.affineCover.f j)).isOpenEmbedding).mpr hopen

/-- A morphism of schemes is universally open if and only if its base change along every
morphism locally of finite presentation is an open map. -/
@[stacks 0F31 "parts (1) and (2)"]
theorem universallyOpen_iff_forall_isOpenMap_pullback_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    UniversallyOpen f ↔
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        LocallyOfFinitePresentation g → IsOpenMap (pullback.snd f g) :=
  ⟨fun hf _ g _ => hf.universally_isOpenMap _ _ _ (IsPullback.of_hasPullback f g).flip,
    fun h => universallyOpen_of_forall_isOpenMap_affineSpaceMap f
      (forall_isOpenMap_affineSpaceMap_of_forall_isOpenMap_pullback_snd f h)⟩

/-- A morphism of schemes is universally open if and only if the induced morphism of affine
`n`-spaces is an open map for every `n`. -/
@[stacks 0F31 "parts (1) and (3)"]
theorem universallyOpen_iff_forall_isOpenMap_affineSpaceMap {X S : Scheme.{u}} (f : X ⟶ S) :
    UniversallyOpen f ↔
      ∀ n : ℕ, IsOpenMap (AffineSpace.map (ULift.{u} (Fin n)) f) :=
  ⟨fun hf _ => hf.universally_isOpenMap _ _ _ (AffineSpace.isPullback_map f),
    universallyOpen_of_forall_isOpenMap_affineSpaceMap f⟩

end AlgebraicGeometry

end
