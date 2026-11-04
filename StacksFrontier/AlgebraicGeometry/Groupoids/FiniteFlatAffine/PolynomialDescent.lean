module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FlatInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.IdempotentRank
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantNorm
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.PolynomialBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.TensorPushout
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantPolynomialHelpers
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# Polynomial descent for invariant functions of a finite locally free affine groupoid

Let `G` be a groupoid scheme with affine object and arrow schemes and with finite locally free
source and target, let `C` be its ring of invariant functions and let `C'` be any `C`-algebra.
An invariant function `f` of the base-changed groupoid then satisfies a monic polynomial with
coefficients in `C'`: a positive power of its linear polynomial `X - f` is the image of a
polynomial over `C'`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.objectRingEquiv` and
  `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.arrowRingEquiv`: the coordinates
  of a base-changed groupoid, its identifications of the rings of global functions with the
  tensor products.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_polynomial_map_eq_pow_X_sub_C`: a positive power of
  the linear polynomial of an invariant function after base change comes from the new base
  ring.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Coordinates of a base-changed groupoid -/

namespace AffineInvariantBaseChange

variable {S : Scheme.{u}} {G : GroupoidScheme S} {C' : Type u} [CommRing C']
  [Algebra (invariantRing G) C']

/-- The identification of the global functions on the object scheme of a base-changed groupoid
with the tensor product `A ⊗[C] C'`. -/
def objectRingEquiv (G' : AffineInvariantBaseChange G C') :
    Γ(G'.groupoid.objects.left, ⊤) ≃+* objectRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.objectsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- The identification of the global functions on the arrow scheme of a base-changed groupoid
with the tensor product `B ⊗[C] C'`. -/
def arrowRingEquiv (G' : AffineInvariantBaseChange G C') :
    Γ(G'.groupoid.arrows.left, ⊤) ≃+* arrowRingBaseChange G C' :=
  (asIso (Scheme.Γ.map G'.arrowsIso.inv.op)).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv

/-- Transporting a global function along an isomorphism with an affine scheme and back, and then
passing to the ring, is the same as passing to the ring directly. -/
private theorem ΓSpecIso_apply_appTop_inv_appTop_hom {X : Scheme.{u}} {R : CommRingCat.{u}}
    (e : X ≅ Spec R) (y : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
      ((Scheme.Hom.appTop e.inv).hom ((Scheme.Hom.appTop e.hom).hom y)) =
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv y := by
  have hi : Scheme.Hom.appTop e.hom ≫ Scheme.Hom.appTop e.inv = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]; simp
  refine congrArg (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv ?_
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    congrArg (fun f ↦ f y) hi

private theorem objectRingEquiv_apply_objectsIso_hom (G' : AffineInvariantBaseChange G C')
    (y : Γ(Spec (.of (objectRingBaseChange G C')), ⊤)) :
    G'.objectRingEquiv ((Scheme.Hom.appTop G'.objectsIso.hom).hom y) =
      (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv y :=
  ΓSpecIso_apply_appTop_inv_appTop_hom G'.objectsIso y

/-- If the source or target map of a base-changed groupoid is the scalar extension of a map `s`
of `G`, then in coordinates it is the scalar extension of `s`. -/
private theorem arrowRingEquiv_appTop_eq_map (G' : AffineInvariantBaseChange G C') :
    letI := invariantRingAlgebraArrow G
    ∀ (s : Γ(G.objects.left, ⊤) →ₐ[invariantRing G] Γ(G.arrows.left, ⊤))
      (m : G'.groupoid.arrows.left ⟶ G'.groupoid.objects.left),
      m = G'.arrowsIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C')).toRingHom) ≫
          G'.objectsIso.inv →
      ∀ x : Γ(G'.groupoid.objects.left, ⊤),
        G'.arrowRingEquiv ((Scheme.Hom.appTop m).hom x) =
          Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C') (G'.objectRingEquiv x) := by
  let _ := invariantRingAlgebraArrow G
  intro s m hm x
  have hnat (y : Γ(Spec (.of (objectRingBaseChange G C')), ⊤)) :
      (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv
        ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C')).toRingHom))).hom y) =
        Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C')
          ((Scheme.ΓSpecIso
            (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv y) :=
    congrArg (fun k ↦ k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C')).toRingHom))
  subst hm
  show (Scheme.ΓSpecIso (.of (arrowRingBaseChange G C'))).commRingCatIsoToRingEquiv
    ((Scheme.Hom.appTop G'.arrowsIso.inv).hom ((Scheme.Hom.appTop G'.arrowsIso.hom).hom
      ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map s (AlgHom.id (invariantRing G) C')).toRingHom))).hom
        ((Scheme.Hom.appTop G'.objectsIso.inv).hom x)))) = _
  rw [ΓSpecIso_apply_appTop_inv_appTop_hom, hnat]
  rfl

/-- In coordinates, the source map of a base-changed groupoid is the scalar extension of the
source map of `G`. -/
theorem arrowRingEquiv_sourceMap (G' : AffineInvariantBaseChange G C')
    (x : Γ(G'.groupoid.objects.left, ⊤)) :
    letI := invariantRingAlgebraArrow G
    G'.arrowRingEquiv (sourceMap G'.groupoid x) =
      Algebra.TensorProduct.map (sourceAlgHom G) (AlgHom.id (invariantRing G) C')
        (G'.objectRingEquiv x) :=
  let _ := invariantRingAlgebraArrow G
  arrowRingEquiv_appTop_eq_map G' _ _ G'.source_eq x

/-- In coordinates, the target map of a base-changed groupoid is the scalar extension of the
target map of `G`. -/
theorem arrowRingEquiv_targetMap (G' : AffineInvariantBaseChange G C')
    (x : Γ(G'.groupoid.objects.left, ⊤)) :
    letI := invariantRingAlgebraArrow G
    G'.arrowRingEquiv (targetMap G'.groupoid x) =
      Algebra.TensorProduct.map (targetAlgHom G) (AlgHom.id (invariantRing G) C')
        (G'.objectRingEquiv x) :=
  let _ := invariantRingAlgebraArrow G
  arrowRingEquiv_appTop_eq_map G' _ _ G'.target_eq x

/-- In coordinates, the canonical map from the new base ring to the invariant functions is the
inclusion of the right tensor factor. -/
theorem objectRingEquiv_canonicalMapToInvariantFunctions (G' : AffineInvariantBaseChange G C')
    (d : C') :
    G'.objectRingEquiv (G'.canonicalMapToInvariantFunctions d).val =
      Algebra.TensorProduct.includeRight d := by
  show G'.objectRingEquiv
    ((G'.groupoid.objects.hom.appTop).hom ((Scheme.ΓSpecIso (.of C')).inv.hom d)) = _
  rw [← G'.objectsIso_over, Scheme.Hom.comp_appTop]
  show G'.objectRingEquiv ((G'.objectsIso.hom.appTop).hom
    ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom)).appTop.hom
      ((Scheme.ΓSpecIso (.of C')).inv.hom d))) = _
  rw [objectRingEquiv_apply_objectsIso_hom]
  have hn := congrArg (fun k ↦ k.hom ((Scheme.ΓSpecIso (.of C')).inv.hom d))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom))
  change (Scheme.ΓSpecIso (.of (objectRingBaseChange G C'))).commRingCatIsoToRingEquiv
      ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        C' →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom)).appTop.hom
          ((Scheme.ΓSpecIso (.of C')).inv.hom d)) =
    Algebra.TensorProduct.includeRight
      ((Scheme.ΓSpecIso (.of C')).commRingCatIsoToRingEquiv
        ((Scheme.ΓSpecIso (.of C')).inv.hom d)) at hn
  rw [hn]
  exact congrArg (Algebra.TensorProduct.includeRight :
    C' →ₐ[invariantRing G] objectRingBaseChange G C')
    (congrArg (fun k ↦ k.hom d) (Scheme.ΓSpecIso (.of C')).inv_hom_id)

/-- The square of coordinate rings over the source map of a base-changed groupoid is
cocartesian. -/
theorem isPushout_sourceMap (G' : AffineInvariantBaseChange G C') :
    letI := invariantRingAlgebraArrow G
    IsPushout (CommRingCat.ofHom (sourceMap G'.groupoid))
      (CommRingCat.ofHom G'.objectRingEquiv.toRingHom)
      (CommRingCat.ofHom G'.arrowRingEquiv.toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (sourceAlgHom G)
        (AlgHom.id (invariantRing G) C')).toRingHom) := by
  let _ := invariantRingAlgebraArrow G
  show IsPushout _ G'.objectRingEquiv.toCommRingCatIso.hom
    G'.arrowRingEquiv.toCommRingCatIso.hom _
  refine IsPushout.of_vert_isIso ⟨?_⟩
  ext x
  exact arrowRingEquiv_sourceMap G' x

end AffineInvariantBaseChange

/-! ### Ranks of the source algebra along the groupoid -/

/-- The stalk rank of the arrow ring over the object ring takes the same value at the source
and at the target of an arrow. -/
private theorem rankAtStalk_source_eq_target {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (z : G.arrows.left) :
    letI : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
    Module.rankAtStalk Γ(G.arrows.left, ⊤)
        (G.objects.left.isoSpec.hom (G.source.left z)) =
      Module.rankAtStalk Γ(G.arrows.left, ⊤)
        (G.objects.left.isoSpec.hom (G.target.left z)) := by
  let _ : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
  obtain ⟨hs, hsflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation G.source.left).mp
      inferInstance
  let _ : IsFinite G.source.left := hs
  let _ : Flat G.source.left := hsflat
  have hfinite : RingHom.Finite G.source.left.appTop.hom :=
    RingHom.finite_algebraMap.mpr G.source.left.finite_appTop
  have hflat : RingHom.Flat G.source.left.appTop.hom :=
    RingHom.flat_algebraMap_iff.mpr G.source.left.flat_appTop
  let _ : IsIso G.inverse.left := groupoidInverse_left_isIso G
  have hinv : G.target.left.finrank = G.source.left.finrank := by
    simpa only [show G.inverse.left ≫ G.source.left = G.target.left from
      congrArg Over.Hom.left G.source_inverse] using
      Scheme.Hom.finrank_comp_left_of_isIso G.inverse.left G.source.left
  calc
    Module.rankAtStalk Γ(G.arrows.left, ⊤)
          (G.objects.left.isoSpec.hom (G.source.left z)) =
        G.source.left.finrank (G.source.left z) :=
      (finrank_eq_rankAtStalk_of_isAffine G.source.left hfinite hflat (G.source.left z)).symm
    _ = G.target.left.finrank (G.target.left z) := finrank_source_eq_finrank_target G z
    _ = G.source.left.finrank (G.target.left z) := congrFun hinv _
    _ = _ := finrank_eq_rankAtStalk_of_isAffine G.source.left hfinite hflat (G.target.left z)

/-- The rank decomposition of the arrow ring over the object ring is cut out by idempotents of
the invariant ring, and all the ranks occurring are positive. -/
private theorem exists_invariant_idempotent_rank_decomposition {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] :
    letI : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) := (sourceMap G).toAlgebra
    ∃ (hfinite : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
      (hprojective : Module.Projective Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤)),
      letI := hfinite
      letI := hprojective
      ∃ (ι : Type) (_ : Fintype ι) (rank : ι → ℕ) (e : ι → invariantRing G),
        (∑ i, e i = 1) ∧ (∀ i, e i * e i = e i) ∧ (∀ i, 0 < rank i) ∧
        (∀ (i : ι) (p : PrimeSpectrum Γ(G.objects.left, ⊤)),
          (e i : Γ(G.objects.left, ⊤)) ∉ p.asIdeal ↔
          Module.rankAtStalk Γ(G.arrows.left, ⊤) p = rank i) := by
  classical
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let _ : Algebra A B := (sourceMap G).toAlgebra
  obtain ⟨hfinite, hprojective⟩ := finite_projective_appTop_of_isFiniteLocallyFree G.source.left
  let _ : Module.Finite A B := hfinite
  let _ : Module.Projective A B := hprojective
  obtain ⟨ι, hι, rank, eA, hsum, hid, hchar, hrange⟩ :=
    Module.exists_idempotent_rankAtStalk_decomposition (R := A) (M := B)
  have hinv (i : ι) : sourceMap G (eA i) = targetMap G (eA i) := by
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem
      (show IsIdempotentElem (sourceMap G (eA i)) from by
        show sourceMap G (eA i) * sourceMap G (eA i) = _; rw [← map_mul, hid i])
      (show IsIdempotentElem (targetMap G (eA i)) from by
        show targetMap G (eA i) * targetMap G (eA i) = _; rw [← map_mul, hid i]) ?_
    ext q
    set y := G.arrows.left.isoSpec.inv q with hy
    have hyq : G.arrows.left.isoSpec.hom.base y = q :=
      congrArg (fun f ↦ f q) G.arrows.left.isoSpec.inv_hom_id
    have hcomap (k : A →+* B) (m : G.arrows.left ⟶ G.objects.left)
        (hk : k = (Scheme.Γ.map m.op).hom) :
        q.comap k = G.objects.left.isoSpec.hom (m.base y) := by
      subst hk
      have h := congrArg (fun k ↦ k.base y) (Scheme.isoSpec_hom_naturality m)
      change (Spec.map (CommRingCat.ofHom (Scheme.Γ.map m.op).hom)).base
        (G.arrows.left.isoSpec.hom.base y) = _ at h
      rwa [hyq] at h
    show eA i ∉ (q.comap (sourceMap G)).asIdeal ↔ eA i ∉ (q.comap (targetMap G)).asIdeal
    rw [hchar, hchar, hcomap (sourceMap G) G.source.left rfl,
      hcomap (targetMap G) G.target.left rfl, rankAtStalk_source_eq_target G y]
  have hpos (i : ι) : 0 < rank i := by
    obtain ⟨p, hp⟩ := hrange i
    let rho : B →+* A := (Scheme.Γ.map G.identity.left.op).hom
    have hrho (a : A) : rho (sourceMap G a) = a := by
      have h := congrArg (fun f : G.objects.left ⟶ G.objects.left ↦ f.appTop.hom)
        (show G.identity.left ≫ G.source.left = 𝟙 G.objects.left from by
          simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left G.source_identity)
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp] at h
      exact congrArg (fun f : A →+* A ↦ f a) h
    let retraction : B →ₗ[A] A :=
      { toFun := rho
        map_add' := map_add rho
        map_smul' := fun a b ↦ by
          show rho (sourceMap G a * b) = a * rho b
          rw [map_mul, hrho] }
    let _ : Module.Flat A B := Module.Flat.of_projective
    rw [← hp]
    exact Module.rankAtStalk_pos_of_comp_eq_id (Algebra.linearMap A B) retraction
      (LinearMap.ext hrho) p
  refine ⟨hfinite, hprojective, ι, hι, rank, fun i ↦ ⟨eA i, hinv i⟩, ?_, ?_, hpos, ?_⟩
  · exact Subtype.ext (by simpa using hsum)
  · exact fun i ↦ Subtype.ext (hid i)
  · exact fun i p ↦ hchar i p

/-! ### Lifting a section to a flat cover -/

/-- Every global function on the object scheme of a base change of `G` along `C'` is the image
of an element of the object ring base-changed along a flat cover of `C'`. -/
private theorem exists_flat_cover_lift_objectRing {S : Scheme.{u}} {G : GroupoidScheme S}
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') (f : Γ(G'.groupoid.objects.left, ⊤)) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra (invariantRing G) D)
      (_ : Module.Flat (invariantRing G) D) (φ : D →ₐ[invariantRing G] C')
      (_ : Function.Surjective φ) (g : objectRingBaseChange G D),
      Algebra.TensorProduct.map
        (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤)) φ g = G'.objectRingEquiv f := by
  obtain ⟨D, hDcomm, hDalg, hDflat, φ, hφ⟩ :=
    Algebra.exists_flat_surjective_cover (R := invariantRing G) (A := C')
  let _ : CommRing D := hDcomm
  let _ : Algebra (invariantRing G) D := hDalg
  obtain ⟨g, hg⟩ := Algebra.TensorProduct.map_surjective
    (f := AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤)) (g := φ)
    Function.surjective_id hφ (G'.objectRingEquiv f)
  exact ⟨D, hDcomm, hDalg, hDflat, φ, hφ, g, hg⟩

/-! ### Descent of the norm over a flat base -/

/-- Over a flat extension of the invariant ring, the norm along the source map of a function
pulled back along the target map is the image of an element of the base ring. -/
private theorem exists_canonicalMap_eq_det_lmul_targetMap {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    {E : Type u} [CommRing E] [Algebra (invariantRing G) E] [Module.Flat (invariantRing G) E]
    (G' : AffineInvariantBaseChange G E) (x : Γ(G'.groupoid.objects.left, ⊤)) :
    letI : Algebra Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
      (sourceMap G'.groupoid).toAlgebra
    ∃ (hfinite : Module.Finite Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤))
      (hprojective :
        Module.Projective Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤)),
      letI := hfinite
      letI := hprojective
      ∃ (hmem : ProjectiveDeterminant.det (Algebra.lmul Γ(G'.groupoid.objects.left, ⊤)
          Γ(G'.groupoid.arrows.left, ⊤) (targetMap G'.groupoid x)) ∈
            invariantRing G'.groupoid) (d : E),
        G'.canonicalMapToInvariantFunctions d = ⟨_, hmem⟩ := by
  let _ : IsAffine G'.groupoid.objects.left := IsAffine.of_isIso G'.objectsIso.hom
  let _ : IsFiniteLocallyFree G'.groupoid.source.left := G'.source_isFiniteLocallyFree
  let _ : Algebra Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
    (sourceMap G'.groupoid).toAlgebra
  obtain ⟨hfinite, hprojective, hmem⟩ := det_lmul_targetMap_mem_invariantRing G'.groupoid x
  let _ : Module.Finite Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) := hfinite
  let _ : Module.Projective Γ(G'.groupoid.objects.left, ⊤) Γ(G'.groupoid.arrows.left, ⊤) :=
    hprojective
  obtain ⟨d, hd⟩ :=
    (canonicalMapToInvariantFunctions_bijective_of_flat (G := G) (G' := G')).2 ⟨_, hmem⟩
  exact ⟨hfinite, hprojective, hmem, d, hd⟩

/-! ### Linear polynomials in the base-changed object ring -/

/-- The embedding of the polynomials over the invariant functions of a base change along `D`
into the object ring base-changed along `D[X]`. -/
private def invariantPolynomialEmbedding {S : Scheme.{u}} {G : GroupoidScheme S} {D : Type u}
    [CommRing D] [Algebra (invariantRing G) D] (GD : AffineInvariantBaseChange G D) :
    Polynomial GD.invariantFunctions →+* objectRingBaseChange G (Polynomial D) :=
  (Algebra.TensorProduct.polynomialRight (invariantRing G) Γ(G.objects.left, ⊤) D).toRingHom.comp
    (Polynomial.mapRingHom (GD.objectRingEquiv.toRingHom.comp
      (invariantRing GD.groupoid).subtype))

private theorem invariantPolynomialEmbedding_injective {S : Scheme.{u}} {G : GroupoidScheme S}
    {D : Type u} [CommRing D] [Algebra (invariantRing G) D]
    (GD : AffineInvariantBaseChange G D) :
    Function.Injective (invariantPolynomialEmbedding GD) :=
  (Algebra.TensorProduct.polynomialRight (invariantRing G) Γ(G.objects.left, ⊤) D).injective.comp
    (Polynomial.map_injective _ (GD.objectRingEquiv.injective.comp Subtype.val_injective))

private theorem invariantPolynomialEmbedding_map {S : Scheme.{u}} {G : GroupoidScheme S}
    {D : Type u} [CommRing D] [Algebra (invariantRing G) D]
    (GD : AffineInvariantBaseChange G D) (p : Polynomial D) :
    invariantPolynomialEmbedding GD (p.map GD.canonicalMapToInvariantFunctions) =
      Algebra.TensorProduct.includeRight p := by
  have hcoeff : (GD.objectRingEquiv.toRingHom.comp
        (invariantRing GD.groupoid).subtype).comp GD.canonicalMapToInvariantFunctions =
      (Algebra.TensorProduct.includeRight :
        D →ₐ[invariantRing G] objectRingBaseChange G D).toRingHom :=
    RingHom.ext fun d ↦ GD.objectRingEquiv_canonicalMapToInvariantFunctions d
  show (Algebra.TensorProduct.polynomialRight (invariantRing G) Γ(G.objects.left, ⊤) D)
    ((p.map GD.canonicalMapToInvariantFunctions).map
      (GD.objectRingEquiv.toRingHom.comp (invariantRing GD.groupoid).subtype)) = _
  rw [Polynomial.map_map, hcoeff, Algebra.TensorProduct.polynomialRight_map_includeRight]

private theorem invariantPolynomialEmbedding_X_sub_C {S : Scheme.{u}} {G : GroupoidScheme S}
    {D : Type u} [CommRing D] [Algebra (invariantRing G) D]
    (GD : AffineInvariantBaseChange G D) (f : GD.invariantFunctions) :
    invariantPolynomialEmbedding GD (Polynomial.X - Polynomial.C f) =
      Algebra.TensorProduct.includeRight (Polynomial.X : Polynomial D) -
        Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
          Polynomial.CAlgHom (GD.objectRingEquiv f.val) := by
  simp [invariantPolynomialEmbedding]

/-- A relation between the two scalar extensions of an element of the object ring base-changed
along `E` persists after extending the coefficients to polynomials and subtracting the
variable. -/
private theorem map_sub_includeRight_X_eq {R A B E : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing E] [Algebra R A] [Algebra R B] [Algebra R E] (s t : A →ₐ[R] B)
    (x : A ⊗[R] E)
    (hx : Algebra.TensorProduct.map s (AlgHom.id R E) x =
      Algebra.TensorProduct.map t (AlgHom.id R E) x) :
    Algebra.TensorProduct.map s (AlgHom.id R (Polynomial E))
        (Algebra.TensorProduct.includeRight (Polynomial.X : Polynomial E) -
          Algebra.TensorProduct.map (AlgHom.id R A) Polynomial.CAlgHom x) =
      Algebra.TensorProduct.map t (AlgHom.id R (Polynomial E))
        (Algebra.TensorProduct.includeRight (Polynomial.X : Polynomial E) -
          Algebra.TensorProduct.map (AlgHom.id R A) Polynomial.CAlgHom x) := by
  have hs := congrArg (fun k : A ⊗[R] E →ₐ[R] B ⊗[R] Polynomial E ↦ k x)
    (Algebra.TensorProduct.map_id_comp_map_eq_map_comp_map_id s
      (Polynomial.CAlgHom : E →ₐ[R] Polynomial E))
  have ht := congrArg (fun k : A ⊗[R] E →ₐ[R] B ⊗[R] Polynomial E ↦ k x)
    (Algebra.TensorProduct.map_id_comp_map_eq_map_comp_map_id t
      (Polynomial.CAlgHom : E →ₐ[R] Polynomial E))
  dsimp only [AlgHom.comp_apply] at hs ht
  simp only [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgHom.id_apply]
  rw [hs, ht, hx]

/-- The lifted linear polynomial maps to the linear polynomial of the given invariant
function. -/
private theorem map_mapAlgHom_sub_eq_invariantPolynomialEmbedding {S : Scheme.{u}}
    {G : GroupoidScheme S} {C' D : Type u} [CommRing C'] [CommRing D]
    [Algebra (invariantRing G) C'] [Algebra (invariantRing G) D]
    (G' : AffineInvariantBaseChange G C') (f : G'.invariantFunctions)
    (φ : D →ₐ[invariantRing G] C') (g : objectRingBaseChange G D)
    (hg : Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤)) φ g =
      G'.objectRingEquiv f.val) :
    Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
        (Polynomial.mapAlgHom φ)
        (Algebra.TensorProduct.includeRight (Polynomial.X : Polynomial D) -
          Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
            Polynomial.CAlgHom g) =
      invariantPolynomialEmbedding G' (Polynomial.X - Polynomial.C f) := by
  rw [map_sub, Algebra.TensorProduct.map_id_mapAlgHom_comp_map_id_CAlgHom, hg,
    invariantPolynomialEmbedding_X_sub_C]
  congr 1
  simp

/-- The linear polynomial of an invariant function is itself invariant for the two scalar
extensions of the source and the target map. -/
private theorem map_sourceAlgHom_invariantPolynomialEmbedding {S : Scheme.{u}}
    {G : GroupoidScheme S} {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') (f : G'.invariantFunctions) :
    letI := invariantRingAlgebraArrow G
    Algebra.TensorProduct.map (sourceAlgHom G) (AlgHom.id (invariantRing G) (Polynomial C'))
        (invariantPolynomialEmbedding G' (Polynomial.X - Polynomial.C f)) =
      Algebra.TensorProduct.map (targetAlgHom G) (AlgHom.id (invariantRing G) (Polynomial C'))
        (invariantPolynomialEmbedding G' (Polynomial.X - Polynomial.C f)) := by
  let _ := invariantRingAlgebraArrow G
  rw [invariantPolynomialEmbedding_X_sub_C]
  refine map_sub_includeRight_X_eq (sourceAlgHom G) (targetAlgHom G) _ ?_
  rw [← G'.arrowRingEquiv_sourceMap, ← G'.arrowRingEquiv_targetMap, f.property]

/-! ### From local powers to a global power -/

/-- If the norm of a scalar descends and the rank is constant on each piece of an idempotent
decomposition, then a positive power of the scalar descends. -/
private theorem exists_pow_eq_map_of_det_idempotents {R T U : Type u} {ι : Type*} [CommRing R]
    [CommRing T] [CommRing U] [Algebra T U] [Module.Finite T U] [Module.Projective T U]
    [Fintype ι] (ψ : R →+* T) (d : ι → R) (p : R) (x : T) (r : ι → ℕ) (hsum : ∑ i, d i = 1)
    (hid : ∀ i, d i * d i = d i) (hrpos : ∀ i, 0 < r i) (y : U) (hp : ψ p =
      ProjectiveDeterminant.det (Algebra.lmul T U y)) (hy : y = algebraMap T U x)
    (hrank : ∀ i (q : PrimeSpectrum T), ψ (d i) ∉ q.asIdeal → Module.rankAtStalk U q = r i) :
    ∃ (n : ℕ) (_ : 0 < n) (q : R), ψ q = x ^ n := by
  refine ψ.exists_pow_eq_map_of_idempotents x r d p hsum hid hrpos fun i ↦ ?_
  calc
    ψ (d i) * ψ p = ψ (d i) *
        ProjectiveDeterminant.det (Algebra.lmul T U (algebraMap T U x)) := by rw [hp, hy]
    _ = ψ (d i) * x ^ r i :=
      ProjectiveDeterminant.idempotent_mul_det_lmul_algebraMap (ψ (d i))
        (by rw [← map_mul, hid]) (r i) (hrank i) x

/-! ### Polynomial descent -/

/-- A positive power of the linear polynomial of an invariant function after base change comes
from the new base ring. -/
@[stacks 03BK "polynomial_descent"]
theorem exists_polynomial_map_eq_pow_X_sub_C {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') (f : G'.invariantFunctions) :
    ∃ (n : ℕ) (_hn : 0 < n) (P : Polynomial C'),
      P.map G'.canonicalMapToInvariantFunctions = (Polynomial.X - Polynomial.C f) ^ n := by
  classical
  obtain ⟨D, hDcomm, hDalg, hDflat, φ, hφ, g, hg⟩ :=
    exists_flat_cover_lift_objectRing G' (f : Γ(G'.groupoid.objects.left, ⊤))
  let _ : CommRing D := hDcomm
  let _ : Algebra (invariantRing G) D := hDalg
  let _ : Module.Flat (invariantRing G) D := hDflat
  let _ : Module.Flat (invariantRing G) (Polynomial D) := Module.Flat.polynomial
  let HD : AffineInvariantBaseChange G (Polynomial D) :=
    Classical.choice (exists_affineInvariantBaseChange G (Polynomial D))
  let xD : objectRingBaseChange G (Polynomial D) :=
    Algebra.TensorProduct.includeRight (Polynomial.X : Polynomial D) -
      Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
        Polynomial.CAlgHom g
  let xHD : Γ(HD.groupoid.objects.left, ⊤) := HD.objectRingEquiv.symm xD
  obtain ⟨hfinite, hprojective, hmem, p, hp⟩ :=
    exists_canonicalMap_eq_det_lmul_targetMap G HD xHD
  let _ : IsAffine HD.groupoid.objects.left := IsAffine.of_isIso HD.objectsIso.hom
  let _ : IsAffine HD.groupoid.arrows.left := IsAffine.of_isIso HD.arrowsIso.hom
  let _ : IsFiniteLocallyFree HD.groupoid.source.left := HD.source_isFiniteLocallyFree
  let _ : IsFiniteLocallyFree HD.groupoid.target.left := HD.target_isFiniteLocallyFree
  let _ : Algebra Γ(HD.groupoid.objects.left, ⊤) Γ(HD.groupoid.arrows.left, ⊤) :=
    (sourceMap HD.groupoid).toAlgebra
  let _ : Module.Finite Γ(HD.groupoid.objects.left, ⊤) Γ(HD.groupoid.arrows.left, ⊤) := hfinite
  let _ : Module.Projective Γ(HD.groupoid.objects.left, ⊤) Γ(HD.groupoid.arrows.left, ⊤) :=
    hprojective
  obtain ⟨-, -, ι, hι, r, e, hesum, heid, hrpos, herank⟩ :=
    exists_invariant_idempotent_rank_decomposition HD.groupoid
  let _ : Fintype ι := hι
  have hflat := canonicalMapToInvariantFunctions_bijective_of_flat HD
  choose d hd using fun i : ι ↦ hflat.2 (e i)
  have hdsum : ∑ i, d i = 1 := hflat.1 (by simpa only [map_sum, hd, map_one] using hesum)
  have hdid (i : ι) : d i * d i = d i := hflat.1 (by simpa only [map_mul, hd] using heid i)
  let _ : Algebra (invariantRing G) Γ(G.arrows.left, ⊤) := invariantRingAlgebraArrow G
  let α := Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
    (Polynomial.mapAlgHom φ)
  let β := Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.arrows.left, ⊤))
    (Polynomial.mapAlgHom φ)
  let sT : objectRingBaseChange G (Polynomial C') →+* arrowRingBaseChange G (Polynomial C') :=
    (Algebra.TensorProduct.map (sourceAlgHom G)
      (AlgHom.id (invariantRing G) (Polynomial C'))).toRingHom
  let tT : objectRingBaseChange G (Polynomial C') →+* arrowRingBaseChange G (Polynomial C') :=
    (Algebra.TensorProduct.map (targetAlgHom G)
      (AlgHom.id (invariantRing G) (Polynomial C'))).toRingHom
  let a : Γ(HD.groupoid.objects.left, ⊤) →+* objectRingBaseChange G (Polynomial C') :=
    α.toRingHom.comp HD.objectRingEquiv.toRingHom
  let b : Γ(HD.groupoid.arrows.left, ⊤) →+* arrowRingBaseChange G (Polynomial C') :=
    β.toRingHom.comp HD.arrowRingEquiv.toRingHom
  let _ : Algebra (objectRingBaseChange G (Polynomial C'))
      (arrowRingBaseChange G (Polynomial C')) := sT.toAlgebra
  have hsq : CategoryTheory.IsPushout
      (CommRingCat.ofHom (algebraMap Γ(HD.groupoid.objects.left, ⊤)
        Γ(HD.groupoid.arrows.left, ⊤)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom b)
      (CommRingCat.ofHom (algebraMap (objectRingBaseChange G (Polynomial C'))
        (arrowRingBaseChange G (Polynomial C')))) :=
    HD.isPushout_sourceMap.paste_vert
      (Algebra.TensorProduct.isPushout_map (sourceAlgHom G) (Polynomial.mapAlgHom φ))
  obtain ⟨_, _⟩ := ProjectiveDeterminant.finite_and_projective_of_isPushout a b hsq
  have hnorm := ProjectiveDeterminant.map_det_lmul_of_isPushout a b hsq
  have hrT := ProjectiveDeterminant.rankAtStalk_of_isPushout a b hsq
  let ψ : Polynomial D →+* objectRingBaseChange G (Polynomial C') :=
    (Algebra.TensorProduct.includeRight :
      Polynomial C' →ₐ[invariantRing G] objectRingBaseChange G (Polynomial C')).toRingHom.comp
      (Polynomial.mapRingHom φ.toRingHom)
  have hac (z : Polynomial D) : a (HD.canonicalMapToInvariantFunctions z).val = ψ z := by
    show α (HD.objectRingEquiv (HD.canonicalMapToInvariantFunctions z).val) = ψ z
    rw [HD.objectRingEquiv_canonicalMapToInvariantFunctions]
    show Algebra.TensorProduct.map (AlgHom.id (invariantRing G) Γ(G.objects.left, ⊤))
        (Polynomial.mapAlgHom φ) (1 ⊗ₜ[invariantRing G] z) =
      1 ⊗ₜ[invariantRing G] (z.map φ.toRingHom)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let x : objectRingBaseChange G (Polynomial C') :=
    invariantPolynomialEmbedding G' (Polynomial.X - Polynomial.C f)
  have hax : a xHD = x := by
    show α (HD.objectRingEquiv (HD.objectRingEquiv.symm xD)) = x
    rw [RingEquiv.apply_symm_apply]
    exact map_mapAlgHom_sub_eq_invariantPolynomialEmbedding G' f φ g hg
  have hst : sT x = tT x := map_sourceAlgHom_invariantPolynomialEmbedding G' f
  have hbtarget : b (targetMap HD.groupoid xHD) = sT x := by
    show β (HD.arrowRingEquiv (targetMap HD.groupoid xHD)) = sT x
    rw [HD.arrowRingEquiv_targetMap]
    have ht := congrArg
      (fun k : objectRingBaseChange G (Polynomial D) →ₐ[invariantRing G]
          arrowRingBaseChange G (Polynomial C') ↦ k (HD.objectRingEquiv xHD))
      (Algebra.TensorProduct.map_id_comp_map_eq_map_comp_map_id (targetAlgHom G)
        (Polynomial.mapAlgHom φ))
    change tT (a xHD) = β (Algebra.TensorProduct.map (targetAlgHom G)
      (AlgHom.id (invariantRing G) (Polynomial D)) (HD.objectRingEquiv xHD)) at ht
    exact ht.symm.trans ((congrArg tT hax).trans hst.symm)
  have hae (i : ι) : a (e i).val = ψ (d i) :=
    (congrArg (fun z : HD.invariantFunctions ↦ a z.val) (hd i)).symm.trans (hac (d i))
  have hrank (i : ι) (q : PrimeSpectrum (objectRingBaseChange G (Polynomial C')))
      (hq : ψ (d i) ∉ q.asIdeal) :
      Module.rankAtStalk (arrowRingBaseChange G (Polynomial C')) q = r i := by
    rw [hrT]
    exact (herank i (q.comap a)).mp fun hmem ↦ hq (by rwa [← hae i])
  have hpnorm : ψ p = ProjectiveDeterminant.det
      (Algebra.lmul (objectRingBaseChange G (Polynomial C'))
        (arrowRingBaseChange G (Polynomial C')) (b (targetMap HD.groupoid xHD))) :=
    ((hac p).symm.trans (congrArg (fun z : HD.invariantFunctions ↦ a z.val) hp)).trans
      (hnorm (targetMap HD.groupoid xHD))
  obtain ⟨n, hn, q, hq⟩ :=
    exists_pow_eq_map_of_det_idempotents (R := Polynomial D)
      (T := objectRingBaseChange G (Polynomial C'))
      (U := arrowRingBaseChange G (Polynomial C')) (ι := ι)
      ψ d p x r hdsum hdid hrpos (b (targetMap HD.groupoid xHD)) hpnorm hbtarget hrank
  exact ⟨n, hn, q.map φ.toRingHom, invariantPolynomialEmbedding_injective G'
    (by rwa [map_pow, invariantPolynomialEmbedding_map])⟩

end AlgebraicGeometry.GroupoidScheme

end

end
