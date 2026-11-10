module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.NilpotentKernel
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.PolynomialDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantPointsHelpers
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral

/-!
# Points of the affine quotient of a finite locally free groupoid

Let `G` be a groupoid scheme with affine object and arrow schemes whose source and target maps
are finite locally free. The spectrum of its ring of invariant functions is then the quotient
of the object scheme by the groupoid, both on underlying topological points and on points
valued in an algebraically closed field: the canonical morphism
`AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum` is surjective, and two points
have the same image exactly when an arrow of the groupoid joins them.

## Main results

* `AlgebraicGeometry.GroupoidScheme.surjective_objectsToInvariantSpectrum` and
  `AlgebraicGeometry.GroupoidScheme.base_objectsToInvariantSpectrum_eq_iff` describe the
  quotient on underlying topological points.
* `AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum_base` computes the morphism on
  underlying points as a contraction of prime ideals.
* `AlgebraicGeometry.GroupoidScheme.surjective_comp_objectsToInvariantSpectrum` and
  `AlgebraicGeometry.GroupoidScheme.comp_objectsToInvariantSpectrum_eq_iff` describe it on
  points valued in an algebraically closed field.

## Implementation notes

Surjectivity on topological points is lying over for the integral extension of the invariant
ring; surjectivity on field-valued points is the corresponding lifting of ring homomorphisms
into an algebraically closed field. The description of the fibres over a field is where the
polynomial descent of
`AlgebraicGeometry.GroupoidScheme.exists_polynomial_map_eq_pow_X_sub_C` enters: base changing
the groupoid to the residue field of a point of the quotient makes its invariant functions a
field extension in which the norm of a suitable function is simultaneously a unit and
nilpotent unless the two points are joined by an arrow. The description of the fibres on
topological points is deduced from the field-valued one by passing to an algebraic closure of
the residue field of the image point.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- On underlying points, the morphism to the invariant spectrum is the contraction of prime
ideals along the inclusion of the invariant ring. -/
theorem objectsToInvariantSpectrum_base {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (x : G.objects.left) :
    (objectsToInvariantSpectrum G).base x =
      PrimeSpectrum.comap (Subring.subtype (invariantRing G))
        (G.objects.left.isoSpec.hom.base x) := rfl

/-! ### Arrows between two field-valued points -/

/-- The key step of the description of the fibres over a field. Let `B` be a finite projective
`A`-algebra through `s`, with a second map `t` and a common retraction `e`, let `C` be a
subring of `A` containing all the norms of the `t`-pullbacks and over which every element of
`A` satisfies a descended linear polynomial, and let `a₀` and `a₁` be two `k`-points of `A`
sharing the section `i`. Then `a₀` and `a₁` are the `t`- and the `s`-pullback of a common
`k`-point of `B`. -/
private theorem exists_ringHom_comp_eq_of_polynomial_descent {A B k : Type u} [CommRing A]
    [CommRing B] [Field k] [IsAlgClosed k] [Algebra A B] [Module.Finite A B]
    [Module.Projective A B] (s t : A →+* B) (e : B →+* A) (C : Subring A) (a₀ a₁ : A →+* k)
    (i : k →+* A) (φ : k →+* C) (hs : algebraMap A B = s)
    (hscalar : ∀ x, t (i x) = s (i x)) (hidentity₀ : e.comp s = RingHom.id A)
    (hidentity₁ : e.comp t = RingHom.id A) (ha₀ : a₀.comp i = RingHom.id k)
    (ha₁ : a₁.comp i = RingHom.id k) (hφ : Function.Injective φ)
    (hnorm : ∀ f, ProjectiveDeterminant.det (Algebra.lmul A B (t f)) ∈ C)
    (hpoly : ∀ x : C, ∃ (n : ℕ) (_ : 0 < n) (P : Polynomial k),
      Polynomial.map φ P = (Polynomial.X - Polynomial.C x) ^ n) :
    ∃ b : B →+* k, b.comp t = a₀ ∧ b.comp s = a₁ := by
  classical
  by_contra hno
  let _ : Algebra A k := a₁.toAlgebra
  let _ : IsArtinianRing (k ⊗[A] B) := IsArtinianRing.of_finite k (k ⊗[A] B)
  let _ : Fintype (MaximalSpectrum (k ⊗[A] B)) := Fintype.ofFinite _
  choose β hβ hβ_mem using fun m : MaximalSpectrum (k ⊗[A] B) ↦
    exists_ringHom_to_algClosed_of_maximal (k := k) m
  let b : MaximalSpectrum (k ⊗[A] B) → B →+* k := fun m ↦
    (β m).comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom
  have hbsource (m : MaximalSpectrum (k ⊗[A] B)) : (b m).comp s = a₁ := by
    refine RingHom.ext fun x ↦ ?_
    have htensor : (algebraMap A k) x ⊗ₜ[A] (1 : B) = (1 : k) ⊗ₜ[A] s x := by
      rw [← hs]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) x
    change (β m) (1 ⊗ₜ[A] s x) = a₁ x
    rw [← htensor]
    exact congrFun (congrArg DFunLike.coe (hβ m)) (a₁ x)
  let a : MaximalSpectrum (k ⊗[A] B) → A →+* k := fun m ↦ (b m).comp t
  have ha_section (m : MaximalSpectrum (k ⊗[A] B)) : (a m).comp i = RingHom.id k := by
    refine RingHom.ext fun x ↦ ?_
    change (b m) (t (i x)) = x
    rw [hscalar]
    simpa [RingHom.comp_apply] using
      (congrFun (congrArg DFunLike.coe (hbsource m)) (i x)).trans
        (congrFun (congrArg DFunLike.coe ha₁) x)
  have hamax (m : MaximalSpectrum (k ⊗[A] B)) : (RingHom.ker (a m)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (a m)
      fun x ↦ ⟨i x, congrFun (congrArg DFunLike.coe (ha_section m)) x⟩
  have hne (m : MaximalSpectrum (k ⊗[A] B)) : RingHom.ker (a m) ≠ RingHom.ker a₀ := fun heq ↦
    hno ⟨b m, ringHom_eq_of_ker_eq_of_comp_eq i (a m) a₀ (ha_section m) ha₀ heq, hbsource m⟩
  have hq : (RingHom.ker a₀).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective a₀ fun x ↦
      ⟨i x, by simpa using congrFun (congrArg DFunLike.coe ha₀) x⟩
  let qs : Finset (MaximalSpectrum A) :=
    Finset.univ.image fun m ↦ (⟨RingHom.ker (a m), hamax m⟩ : MaximalSpectrum A)
  obtain ⟨f, hfmem, hfavoid⟩ := exists_mem_notMem_of_ne (RingHom.ker a₀) hq qs (by
    intro p hp
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hp
    exact hne m)
  have hx_not_mem (m : MaximalSpectrum (k ⊗[A] B)) :
      (Algebra.TensorProduct.includeRight (t f) : k ⊗[A] B) ∉ m.asIdeal := fun hxm ↦
    hfavoid _ (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩) (RingHom.mem_ker.mpr (by
      simpa [a, b, Algebra.TensorProduct.includeRight_apply] using hβ_mem m _ hxm))
  have hxunit : IsUnit (Algebra.TensorProduct.includeRight (t f) : k ⊗[A] B) := by
    by_contra hnu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ fun htop ↦
      hnu (Ideal.span_singleton_eq_top.mp htop)
    exact hx_not_mem ⟨m, hm⟩ (hle (Ideal.subset_span (by simp)))
  have ha₁g : a₁ (ProjectiveDeterminant.det (Algebra.lmul A B (t f))) ≠ 0 := by
    change (algebraMap A k) (ProjectiveDeterminant.det (Algebra.lmul A B (t f))) ≠ 0
    rw [algebraMap_det_lmul (k := k) (t f)]
    exact (det_lmul_ne_zero_iff_isUnit (k := k) (F := k ⊗[A] B) _).2 hxunit
  have ha₀g : a₀ (ProjectiveDeterminant.det (Algebra.lmul A B (t f))) = 0 := by
    let _ : Algebra A k := a₀.toAlgebra
    have hb₀source : (a₀.comp e).comp s = a₀ := by
      simp [RingHom.comp_assoc, hidentity₀]
    let b₀Alg : B →ₐ[A] k :=
      { toRingHom := a₀.comp e
        commutes' := fun x ↦ by
          change (a₀.comp e) (algebraMap A B x) = algebraMap A k x
          rw [hs, ← RingHom.comp_apply, hb₀source]
          rfl }
    let β₀ : k ⊗[A] B →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) b₀Alg fun _ _ ↦ Commute.all _ _
    have hβ₀ : β₀ (Algebra.TensorProduct.includeRight (t f) : k ⊗[A] B) = 0 := by
      change Algebra.TensorProduct.lift (AlgHom.id k k) b₀Alg _ (1 ⊗ₜ[A] t f) = 0
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact (congrArg a₀ (RingHom.congr_fun hidentity₁ f)).trans (RingHom.mem_ker.mp hfmem)
    change (algebraMap A k) (ProjectiveDeterminant.det (Algebra.lmul A B (t f))) = 0
    rw [algebraMap_det_lmul (k := k) (t f)]
    by_contra hcon
    exact not_isUnit_zero
      (hβ₀ ▸ ((det_lmul_ne_zero_iff_isUnit (k := k) (F := k ⊗[A] B) _).mp hcon).map β₀.toRingHom)
  obtain ⟨n, hn, P, hP⟩ := hpoly ⟨_, hnorm f⟩
  rcases isUnit_or_isNilpotent_of_map_eq_pow_X_sub_C φ hφ ⟨_, hnorm f⟩ n hn P hP with hu | hnil
  · exact not_isUnit_zero (ha₀g ▸ IsUnit.map (a₀.comp C.subtype) hu)
  · exact ha₁g (hnil.map (a₁.comp C.subtype)).eq_zero

/-! ### The quotient on points -/

/-- **Stacks Project, Tag 03BL.** The morphism from the object scheme to the spectrum of the
invariant functions is surjective on underlying topological points. -/
@[stacks 03BL "part (1), surjectivity", sga "1 V 1.1" "more general"]
theorem surjective_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] :
    Function.Surjective (objectsToInvariantSpectrum G).base := by
  have hsurj : Function.Surjective
      (PrimeSpectrum.comap (Subring.subtype (invariantRing G))) :=
    integral_overring_surjective _ (isIntegral_invariantRing G) fun _ _ h ↦ Subtype.ext h
  have hΓ : Function.Surjective (G.objects.left.toSpecΓ).base := by
    let _ : IsIso G.objects.left.toSpecΓ := IsAffine.affine
    exact (TopCat.epi_iff_surjective _).mp inferInstance
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  obtain ⟨u, hu⟩ := hΓ x
  exact ⟨u, by
    change (Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G)))).base
      ((G.objects.left.toSpecΓ).base u) = y
    rwa [hu]⟩

/-- **Stacks Project, Tag 03BL.** Over an algebraically closed field, every point of the
spectrum of the invariant functions lifts to the object scheme. -/
@[stacks 03BL "part (2), surjectivity", sga "1 V 1.1" "more general"]
theorem surjective_comp_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Surjective
      fun x : Spec (.of k) ⟶ G.objects.left ↦ x ≫ objectsToInvariantSpectrum G := by
  intro x
  obtain ⟨h, hh⟩ := exists_ringHom_comp_eq_of_isIntegral (Subring.subtype (invariantRing G))
    (isIntegral_invariantRing G) Subtype.val_injective
    ((Scheme.ΓSpecIso (.of (invariantRing G))).inv ≫ x.appTop ≫
      (Scheme.ΓSpecIso (.of k)).hom).hom
  refine ⟨Spec.map (CommRingCat.ofHom h) ≫ G.objects.left.isoSpec.inv, ?_⟩
  change (Spec.map (CommRingCat.ofHom h) ≫ G.objects.left.isoSpec.inv) ≫
    G.objects.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G))) = x
  calc
    _ = Spec.map (CommRingCat.ofHom (h.comp (Subring.subtype (invariantRing G)))) := by
      rw [Category.assoc, Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
    _ = x := by rw [hh, ← eq_specMap_appTop]

/-- **Stacks Project, Tag 03BL.** Over an algebraically closed field, two points of the object
scheme have the same image in the spectrum of the invariant functions exactly when they are
the target and the source of a common arrow. -/
@[stacks 03BL "part (2), fibres"]
theorem comp_objectsToInvariantSpectrum_eq_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (k : Type u) [Field k] [IsAlgClosed k] (u₀ u₁ : Spec (.of k) ⟶ G.objects.left) :
    u₀ ≫ objectsToInvariantSpectrum G = u₁ ≫ objectsToInvariantSpectrum G ↔
      ∃ r : Spec (.of k) ⟶ G.arrows.left,
        r ≫ G.target.left = u₀ ∧ r ≫ G.source.left = u₁ := by
  classical
  refine ⟨fun h ↦ ?_, ?_⟩
  · let _ : Algebra (invariantRing G) k :=
      (((Scheme.ΓSpecIso (.of (invariantRing G))).inv ≫
        (u₀ ≫ objectsToInvariantSpectrum G).appTop ≫
          (Scheme.ΓSpecIso (.of k)).hom).hom).toAlgebra
    obtain ⟨G'⟩ := exists_affineInvariantBaseChange G k
    have w₀ : u₀ ≫ objectsToInvariantSpectrum G =
        𝟙 (Spec (.of k)) ≫ invariantSpectrumMap G k := by
      rw [Category.id_comp]
      exact eq_specMap_appTop (u₀ ≫ objectsToInvariantSpectrum G)
    have w₁ : u₁ ≫ objectsToInvariantSpectrum G =
        𝟙 (Spec (.of k)) ≫ invariantSpectrumMap G k := h.symm.trans w₀
    let v₀ := G'.objects_isPullback.lift u₀ (𝟙 (Spec (.of k))) w₀
    let v₁ := G'.objects_isPullback.lift u₁ (𝟙 (Spec (.of k))) w₁
    have hv₀proj : v₀ ≫ G'.objectsProjection = u₀ := by simp [v₀]
    have hv₁proj : v₁ ≫ G'.objectsProjection = u₁ := by simp [v₁]
    have hv₀base : v₀ ≫ G'.groupoid.objects.hom = 𝟙 (Spec (.of k)) := by simp [v₀]
    have hv₁base : v₁ ≫ G'.groupoid.objects.hom = 𝟙 (Spec (.of k)) := by simp [v₁]
    let _ : IsAffine G'.groupoid.objects.left := IsAffine.of_isIso G'.objectsIso.hom
    let _ : IsAffine G'.groupoid.arrows.left := IsAffine.of_isIso G'.arrowsIso.hom
    let _ : IsFiniteLocallyFree G'.groupoid.source.left := G'.source_isFiniteLocallyFree
    let _ : IsFiniteLocallyFree G'.groupoid.target.left := G'.target_isFiniteLocallyFree
    let i : k →+* Γ(G'.groupoid.objects.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G'.groupoid.objects.hom.appTop).hom
    let a₀ : Γ(G'.groupoid.objects.left, ⊤) →+* k :=
      (v₀.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    let a₁ : Γ(G'.groupoid.objects.left, ⊤) →+* k :=
      (v₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    have hsect (v : Spec (.of k) ⟶ G'.groupoid.objects.left)
        (hv : v ≫ G'.groupoid.objects.hom = 𝟙 (Spec (.of k))) :
        ((v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom).comp i = RingHom.id k := by
      have hcomp : G'.groupoid.objects.hom.appTop ≫ v.appTop =
          Scheme.Hom.appTop (𝟙 (Spec (.of k))) := by
        simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hv
      change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G'.groupoid.objects.hom.appTop ≫
        v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom = RingHom.id k
      simpa [Category.assoc] using congrArg CommRingCat.Hom.hom
        (congrArg (fun f ↦ (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          f ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) hcomp)
    have hφ : Function.Injective G'.canonicalMapToInvariantFunctions := fun x y hxy ↦
      sub_eq_zero.mp (isNilpotent_of_mem_ker_canonicalMapToInvariantFunctions G G' (x - y)
        (RingHom.mem_ker.mpr (by rw [map_sub, hxy]; simp))).eq_zero
    let _ : Algebra Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
      (sourceMap G'.groupoid).toAlgebra
    obtain ⟨hfinite, hprojective, -⟩ :=
      det_lmul_targetMap_mem_invariantRing G'.groupoid (0 : Γ(G'.groupoid.objects.left, ⊤))
    let _ : Module.Finite Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
      hfinite
    let _ : Module.Projective Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
      hprojective
    have hidentity (m : G'.groupoid.arrows ⟶ G'.groupoid.objects)
        (hm : G'.groupoid.identity ≫ m = 𝟙 G'.groupoid.objects) :
        ((Scheme.Γ.map G'.groupoid.identity.left.op).hom).comp
          ((Scheme.Γ.map m.left.op).hom) = RingHom.id Γ(G'.groupoid.objects.left, ⊤) := by
      refine RingHom.ext fun x ↦ ?_
      have hm' : G'.groupoid.identity.left ≫ m.left = 𝟙 G'.groupoid.objects.left := by
        simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left hm
      have hx := congrArg (fun f : G'.groupoid.objects.left ⟶ G'.groupoid.objects.left ↦
        f.appTop.hom x) hm'
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp] at hx
      exact hx.trans (RingHom.id_apply x)
    obtain ⟨r', hrt, hrs⟩ := exists_ringHom_comp_eq_of_polynomial_descent
      (sourceMap G'.groupoid) (targetMap G'.groupoid)
      (Scheme.Γ.map G'.groupoid.identity.left.op).hom (invariantRing G'.groupoid) a₀ a₁ i
      G'.canonicalMapToInvariantFunctions rfl
      (fun x ↦ (G'.baseRingMap_invariant x).symm)
      (hidentity G'.groupoid.source G'.groupoid.source_identity)
      (hidentity G'.groupoid.target G'.groupoid.target_identity)
      (hsect v₀ hv₀base) (hsect v₁ hv₁base) hφ
      (fun f ↦ (det_lmul_targetMap_mem_invariantRing G'.groupoid f).2.2)
      (fun x ↦ exists_polynomial_map_eq_pow_X_sub_C (G := G) (G' := G') x)
    let r : Spec (.of k) ⟶ G'.groupoid.arrows.left :=
      Spec.map (CommRingCat.ofHom r') ≫ G'.groupoid.arrows.left.isoSpec.inv
    have hrcoord : (r.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom = r' := by
      have hspec : r ≫ G'.groupoid.arrows.left.toSpecΓ = Spec.map (CommRingCat.ofHom r') := by
        change (Spec.map (CommRingCat.ofHom r') ≫ G'.groupoid.arrows.left.isoSpec.inv) ≫
          G'.groupoid.arrows.left.toSpecΓ = _
        rw [Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
        rfl
      have htop := congrArg Scheme.Hom.appTop hspec
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at htop
      refine congrArg CommRingCat.Hom.hom ?_
      refine (cancel_epi (Scheme.ΓSpecIso (.of Γ(G'.groupoid.arrows.left, ⊤))).hom).1 ?_
      simpa only [Category.assoc, CommRingCat.of_carrier] using
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom r') ▸
          congrArg (fun f ↦ f ≫ (Scheme.ΓSpecIso (.of k)).hom) htop)
    have hcomp (m : G'.groupoid.arrows.left ⟶ G'.groupoid.objects.left)
        (v : Spec (.of k) ⟶ G'.groupoid.objects.left)
        (hm : r'.comp (Scheme.Γ.map m.op).hom =
          (v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) :
        r ≫ m = v := by
      refine ext_of_appTop_eq _ _ ?_
      calc
        (Scheme.Hom.appTop (r ≫ m) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom =
            ((r.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom).comp
              (m.appTop).hom := RingHom.ext fun _ ↦ rfl
        _ = _ := by rwa [hrcoord]
    refine ⟨r ≫ G'.arrowsProjection, ?_, ?_⟩
    · calc
        (r ≫ G'.arrowsProjection) ≫ G.target.left =
            r ≫ (G'.groupoid.target.left ≫ G'.objectsProjection) := by
          rw [Category.assoc, G'.projection_target]
        _ = u₀ := by
          rw [← Category.assoc, hcomp G'.groupoid.target.left v₀ hrt, hv₀proj]
    · calc
        (r ≫ G'.arrowsProjection) ≫ G.source.left =
            r ≫ (G'.groupoid.source.left ≫ G'.objectsProjection) := by
          rw [Category.assoc, G'.projection_source]
        _ = u₁ := by
          rw [← Category.assoc, hcomp G'.groupoid.source.left v₁ hrs, hv₁proj]
  · rintro ⟨r, htarget, hsource⟩
    calc
      u₀ ≫ objectsToInvariantSpectrum G =
          r ≫ (G.target.left ≫ objectsToInvariantSpectrum G) := by
        rw [← htarget, Category.assoc]
      _ = r ≫ (G.source.left ≫ objectsToInvariantSpectrum G) := by
        rw [source_comp_objectsToInvariantSpectrum]
      _ = u₁ ≫ objectsToInvariantSpectrum G := by rw [← Category.assoc, hsource]

/-- **Stacks Project, Tag 03BL.** Two topological points of the object scheme have the same
image in the spectrum of the invariant functions exactly when they are the target and the
source of a common arrow. -/
@[stacks 03BL "part (1), fibres"]
theorem base_objectsToInvariantSpectrum_eq_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (u₀ u₁ : G.objects.left) :
    (objectsToInvariantSpectrum G).base u₀ = (objectsToInvariantSpectrum G).base u₁ ↔
      ∃ r : G.arrows.left,
        G.target.left.base r = u₀ ∧ G.source.left.base r = u₁ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let f : invariantRing G →+* Γ(G.objects.left, ⊤) := Subring.subtype (invariantRing G)
    obtain ⟨p₀, hp₀⟩ : ∃ p, G.objects.left.isoSpec.hom.base u₀ = p := ⟨_, rfl⟩
    obtain ⟨p₁, hp₁⟩ : ∃ p, G.objects.left.isoSpec.hom.base u₁ = p := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, (objectsToInvariantSpectrum G).base u₀ = q := ⟨_, rfl⟩
    let _ : q.asIdeal.IsPrime := q.isPrime
    let _ : p₀.asIdeal.IsPrime := p₀.isPrime
    let _ : p₁.asIdeal.IsPrime := p₁.isPrime
    have hcomap₀ : q.asIdeal = Ideal.comap f p₀.asIdeal := by
      rw [← hq, ← hp₀, objectsToInvariantSpectrum_base G u₀]
      rfl
    have hcomap₁ : q.asIdeal = Ideal.comap f p₁.asIdeal := by
      rw [← hq, h, ← hp₁, objectsToInvariantSpectrum_base G u₁]
      rfl
    let _ : Algebra (invariantRing G) Γ(G.objects.left, ⊤) := f.toAlgebra
    let _ : Algebra.IsIntegral (invariantRing G) Γ(G.objects.left, ⊤) :=
      ⟨isIntegral_invariantRing G⟩
    obtain ⟨K, hKfield, hKalgClosed, hKalgebra, hKinj⟩ :
        ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
          (_ : Algebra q.asIdeal.ResidueField K),
            Function.Injective (algebraMap q.asIdeal.ResidueField K) :=
      ⟨AlgebraicClosure q.asIdeal.ResidueField, inferInstance, inferInstance, inferInstance,
        RingHom.injective _⟩
    let _ : Field K := hKfield
    let _ : IsAlgClosed K := hKalgClosed
    let _ : Algebra q.asIdeal.ResidueField K := hKalgebra
    let _ : Module.IsTorsionFree q.asIdeal.ResidueField K :=
      Module.isTorsionFree_iff_algebraMap_injective.2 hKinj
    have hlift (p : PrimeSpectrum Γ(G.objects.left, ⊤))
        (hp : q.asIdeal = Ideal.comap f p.asIdeal) :
        ∃ α : Γ(G.objects.left, ⊤) →+* K,
          α.comp f = (algebraMap q.asIdeal.ResidueField K).comp
            (algebraMap (invariantRing G) q.asIdeal.ResidueField) ∧
          RingHom.ker α = p.asIdeal := by
      let _ : p.asIdeal.LiesOver q.asIdeal := ⟨hp⟩
      let _ : Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) :=
        Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
      let _ : Algebra.IsAlgebraic q.asIdeal.ResidueField p.asIdeal.ResidueField := inferInstance
      let _ : Module.IsTorsionFree q.asIdeal.ResidueField p.asIdeal.ResidueField :=
        Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.injective
          (algebraMap q.asIdeal.ResidueField p.asIdeal.ResidueField))
      let α : p.asIdeal.ResidueField →ₐ[q.asIdeal.ResidueField] K := IsAlgClosed.lift
      refine ⟨α.toRingHom.comp (algebraMap Γ(G.objects.left, ⊤) p.asIdeal.ResidueField), ?_, ?_⟩
      · refine RingHom.ext fun x ↦ ?_
        change α (algebraMap Γ(G.objects.left, ⊤) p.asIdeal.ResidueField (f x)) =
          algebraMap q.asIdeal.ResidueField K
            (algebraMap (invariantRing G) q.asIdeal.ResidueField x)
        rw [← Ideal.ResidueField.map_algebraMap q.asIdeal p.asIdeal f hp x]
        exact α.commutes _
      · ext x
        change α (algebraMap Γ(G.objects.left, ⊤) p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
        refine ⟨fun hx ↦ Ideal.algebraMap_residueField_eq_zero.mp (α.injective (by simpa using hx)),
          fun hx ↦ by simp [Ideal.algebraMap_residueField_eq_zero.mpr hx]⟩
    obtain ⟨a₀, hcompat₀, hker₀⟩ := hlift p₀ hcomap₀
    obtain ⟨a₁, hcompat₁, hker₁⟩ := hlift p₁ hcomap₁
    have hspec (α : Γ(G.objects.left, ⊤) →+* K)
        (hcompat : α.comp f = (algebraMap q.asIdeal.ResidueField K).comp
          (algebraMap (invariantRing G) q.asIdeal.ResidueField)) :
        (Spec.map (CommRingCat.ofHom α) ≫ G.objects.left.isoSpec.inv) ≫
            objectsToInvariantSpectrum G =
          Spec.map (CommRingCat.ofHom ((algebraMap q.asIdeal.ResidueField K).comp
            (algebraMap (invariantRing G) q.asIdeal.ResidueField))) := by
      change (Spec.map (CommRingCat.ofHom α) ≫ G.objects.left.isoSpec.inv) ≫
        G.objects.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) = _
      rw [Category.assoc, Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hcompat]
    obtain ⟨r, htarget, hsource⟩ := (comp_objectsToInvariantSpectrum_eq_iff G K
      (Spec.map (CommRingCat.ofHom a₀) ≫ G.objects.left.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom a₁) ≫ G.objects.left.isoSpec.inv)).mp
      ((hspec a₀ hcompat₀).trans (hspec a₁ hcompat₁).symm)
    have hpt (α : Γ(G.objects.left, ⊤) →+* K) (p : PrimeSpectrum Γ(G.objects.left, ⊤))
        (hker : RingHom.ker α = p.asIdeal) (u : G.objects.left)
        (hu : G.objects.left.isoSpec.hom.base u = p) :
        (Spec.map (CommRingCat.ofHom α) ≫ G.objects.left.isoSpec.inv).base
          (IsLocalRing.closedPoint K) = u := by
      have hp : (Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint K) = p := by
        refine PrimeSpectrum.ext ?_
        change Ideal.comap α (IsLocalRing.maximalIdeal K) = p.asIdeal
        rwa [IsLocalRing.maximalIdeal_eq_bot]
      change G.objects.left.isoSpec.inv.base
        ((Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint K)) = u
      rw [hp, ← hu]
      simp
    refine ⟨r.base (IsLocalRing.closedPoint K), ?_, ?_⟩
    · exact (congrArg (fun m : Spec (.of K) ⟶ G.objects.left ↦
        m.base (IsLocalRing.closedPoint K)) htarget).trans (hpt a₀ p₀ hker₀ u₀ hp₀)
    · exact (congrArg (fun m : Spec (.of K) ⟶ G.objects.left ↦
        m.base (IsLocalRing.closedPoint K)) hsource).trans (hpt a₁ p₁ hker₁ u₁ hp₁)
  · rintro ⟨r, htarget, hsource⟩
    have hv : (objectsToInvariantSpectrum G).base (G.target.left.base r) =
        (objectsToInvariantSpectrum G).base (G.source.left.base r) := by
      simpa [Scheme.Hom.comp_base] using congrArg (fun m ↦ TopCat.Hom.hom m r)
        (congrArg (fun m : G.arrows.left ⟶ Spec (.of (invariantRing G)) ↦ m.base)
          (source_comp_objectsToInvariantSpectrum G).symm)
    rwa [← htarget, ← hsource]

end AlgebraicGeometry.GroupoidScheme

end

end
