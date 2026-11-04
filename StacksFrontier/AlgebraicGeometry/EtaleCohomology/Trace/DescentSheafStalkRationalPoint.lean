module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius

/-!
# The Frobenius element at a point with values in a finite extension

Let `C` be a Galois covering of `X` with group `H` and `D(N)` the descent sheaf of a module `N`
with an action `ρ` of `H`. Let `y` be a point of `X` with values in a finite field `K`, with image
`x`, so that `κ(x) ⊆ K` and `#K = #κ(x)ⁿ`. This file shows that the geometric Frobenius of `K` on
the stalk of `D(N)` at the geometric point over `y` is `ρ(g_xⁿ)`. Here `g_x` is the Frobenius
element at `x` of a point `a` of the covering over the geometric point at `x`
(`AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquiv_frobeniusStalk`). The same `g_x` serves
every `K`, and every `N`, which is what lets the local terms of the trace formula over all finite
extensions be compared with the local factors of the `L`-function.

The comparison goes through a morphism of geometric points `j`, from the geometric point over `y`
to the geometric point at `x`, given by an embedding of the algebraic closure of `κ(x)` into the
algebraically closed extension of `K`. Under `j` the Frobenius of `K` becomes the `n`-th power of
the Frobenius of `κ(x)` (`galoisPointHom_comp_rationalPointHom`). The point `j ≫ a` of the
covering then has group element `g_xⁿ` (`pointElement_comp_eq_pow`).

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.rationalPointHom`: the comparison morphism `j` of
  geometric points.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.galoisPointHom_comp_rationalPointHom`: the Frobenius of
  `K` is the `n`-th power of that of `κ(x)` under `j`.
* `AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquiv_geometricFrobeniusStalk` and
  `.stalkLinearEquivOfIso_geometricFrobeniusStalk`: the Frobenius of `K` acts on the stalk at the
  geometric point over `y` as `ρ(g_xⁿ)`.
* `AlgebraicGeometry.EtaleGaloisCovering.exists_stalk_inverseImage_geometricFrobenius`: the same
  for the inverse image along a morphism `g : X' ⟶ X`, at a point `y'` of `X'`. This is the form
  in which the local term of the trace formula over `K` is read on the base change `X ×_k K`.

## Implementation notes

The convention for the group element is that of
`AlgebraicGeometry.EtaleGaloisCovering.pointElement`, `σ ∘ a ∘ (act g) = a`, so the Frobenius
acts as `ρ g_x`, with no inverse.

No `@[stacks]` attribute appears in this file: it is a step of the proof of Tag 03UZ, which the
source omits.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
* [Stacks Project, Tag 03SW](https://stacks.math.columbia.edu/tag/03SW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius IsLocalRing

universe u r w v

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (C : EtaleGaloisCovering X H)

section Comparison

variable {K : Type u} [Field K] (y : Spec (.of K) ⟶ X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  [Algebra K Ω]

/-- The residue field at the image of a point `y` with values in a field `K` maps to `K`. -/
public def residueFieldToField : X.residueField (y (closedPoint K)) ⟶ CommRingCat.of K :=
  X.descResidueField (Scheme.stalkClosedPointTo y)

/-- The point `y` factors as `Spec K ⟶ Spec κ(x) ⟶ X` through `residueFieldToField y`. -/
public theorem spec_residueFieldToField_fromSpecResidueField :
    Spec.map (residueFieldToField y) ≫ X.fromSpecResidueField (y (closedPoint K)) = y :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y

/-- The embedding over `κ(x)` of the algebraic closure of the residue field `κ(x)` at the image
`x` of `y` into an algebraically closed extension `Ω` of `K`. -/
public def algebraicClosureEmbedding :
    AlgebraicClosure (X.residueField (y (closedPoint K))) →+* Ω :=
  letI : Algebra (X.residueField (y (closedPoint K))) Ω :=
    ((algebraMap K Ω).comp (residueFieldToField y).hom).toAlgebra
  (IsAlgClosed.lift (R := X.residueField (y (closedPoint K)))
    (S := AlgebraicClosure (X.residueField (y (closedPoint K)))) (M := Ω)).toRingHom

/-- `algebraicClosureEmbedding y Ω` restricts on `κ(x)` to the composite `κ(x) ⟶ K ⟶ Ω`. -/
public theorem algebraicClosureEmbedding_algebraMap (z : X.residueField (y (closedPoint K))) :
    algebraicClosureEmbedding y Ω (algebraMap _ (AlgebraicClosure _) z) =
      algebraMap K Ω ((residueFieldToField y).hom z) :=
  let : Algebra (X.residueField (y (closedPoint K))) Ω :=
    ((algebraMap K Ω).comp (residueFieldToField y).hom).toAlgebra
  (IsAlgClosed.lift (R := X.residueField (y (closedPoint K)))
    (S := AlgebraicClosure (X.residueField (y (closedPoint K)))) (M := Ω)).commutes z

/-- **The comparison of geometric points.** The geometric point at `y` with values in `Ω` maps
to the geometric point at the image `x` of `y`, by the embedding of the algebraic closure of
`κ(x)` into `Ω`. -/
public def rationalPointHom :
    GeometricPoint.Hom (rationalGeometricPoint Ω y) (geometricPointAt X (y (closedPoint K))) where
  hom := Spec.map (CommRingCat.ofHom (algebraicClosureEmbedding y Ω))
  comm := by
    have h : CommRingCat.ofHom (algebraMap (X.residueField (y (closedPoint K)))
          (AlgebraicClosure (X.residueField (y (closedPoint K))))) ≫
        CommRingCat.ofHom (algebraicClosureEmbedding y Ω) =
        residueFieldToField y ≫ CommRingCat.ofHom (algebraMap K Ω) := by
      ext z
      exact algebraicClosureEmbedding_algebraMap y Ω z
    change Spec.map _ ≫ Spec.map _ ≫ X.fromSpecResidueField _ = Spec.map _ ≫ y
    conv_rhs => rw [← spec_residueFieldToField_fromSpecResidueField y]
    rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp, h]

/-- The `n`-th power of the endomorphism `Spec σ` of the spectrum of a field is `Spec σⁿ`. -/
public theorem spec_algEquiv_pow {k L : Type u} [Field k] [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (n : ℕ) :
    End.asHom (End.of (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) ^ n) =
      Spec.map (CommRingCat.ofHom (σ ^ n).toAlgHom.toRingHom) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (Spec.map_id _).symm
  | succ n ih =>
    calc End.asHom (End.of (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) ^ (n + 1))
        = Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
            End.asHom (End.of (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) ^ n) := by
          rw [pow_succ, End.mul_def]
      _ = Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (σ ^ n).toAlgHom.toRingHom) := by rw [ih]
      _ = Spec.map (CommRingCat.ofHom (σ ^ (n + 1)).toAlgHom.toRingHom) := by
          rw [← Spec.map_comp, pow_succ']
          rfl

variable [Fintype K] (p f : ℕ) [Fact p.Prime] [CharP Ω p]

/-- **The Frobenius of `K` on the geometric point at `y` is a power of the Frobenius of the
residue field.** If `#K = #κ(x)ⁿ`, then under the comparison morphism of geometric points the
geometric Frobenius of `K` corresponds to the `n`-th power of the geometric Frobenius of `κ(x)`. -/
public theorem galoisPointHom_comp_rationalPointHom (hcard : Fintype.card K = p ^ f)
    [Finite (X.residueField (y (closedPoint K)))] (n : ℕ)
    (hn : Fintype.card K = Nat.card (X.residueField (y (closedPoint K))) ^ n) :
    (galoisPointHom Ω (arithmeticFrobenius K Ω p f hcard).symm y).hom ≫
        (rationalPointHom y Ω).hom =
      (rationalPointHom y Ω).hom ≫
        End.asHom (End.of (frobeniusPointHom X (y (closedPoint K))).hom ^ n) := by
  let F := residueGeometricFrobenius X (y (closedPoint K))
  let A := arithmeticFrobenius K Ω p f hcard
  let ι := algebraicClosureEmbedding y Ω
  have hG : ∀ (m : ℕ) (w : AlgebraicClosure (X.residueField (y (closedPoint K)))),
      (F⁻¹ ^ m) w = w ^ (Nat.card (X.residueField (y (closedPoint K))) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro w
      rw [pow_succ', AlgEquiv.mul_apply, ih, AlgEquiv.aut_inv,
        residueGeometricFrobenius_symm_apply, ← pow_mul, pow_succ, mul_comm]
  have hpt : ∀ z, A (ι ((F ^ n) z)) = ι z := by
    intro z
    rw [arithmeticFrobenius_apply, ← map_pow, hn, ← hG n, inv_pow, ← AlgEquiv.mul_apply,
      inv_mul_cancel, AlgEquiv.one_apply]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ _
  rw [frobeniusPointHom_hom, spec_algEquiv_pow F n, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  show A.symm (ι z) = ι ((F ^ n) z)
  rw [← hpt z, AlgEquiv.symm_apply_apply]

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

omit [Fintype K] in
/-- The point `j ≫ a` of the covering over the geometric point at `y`, for a point `a` of the
covering over the geometric point at the image of `y`. -/
public theorem rationalPointHom_comp_cover_hom
    (a : (geometricPointAt X (y (closedPoint K))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X (y (closedPoint K))).hom) :
    ((rationalPointHom y Ω).hom ≫ a) ≫ C.cover.hom = (rationalGeometricPoint Ω y).hom := by
  rw [Category.assoc, ha, (rationalPointHom y Ω).comm]

/-- The group element of the Frobenius of `K` at the point `j ≫ a` is the `n`-th power of that of
the Frobenius of `κ(x)` at `a`. -/
private theorem pointElement_galoisPointHom_eq_pow (hcard : Fintype.card K = p ^ f)
    [Finite (X.residueField (y (closedPoint K)))] (n : ℕ)
    (hn : Fintype.card K = Nat.card (X.residueField (y (closedPoint K))) ^ n)
    (a : (geometricPointAt X (y (closedPoint K))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X (y (closedPoint K))).hom) :
    C.pointElement ((rationalPointHom y Ω).hom ≫ a) (C.rationalPointHom_comp_cover_hom y Ω a ha)
        (galoisPointHom Ω (arithmeticFrobenius K Ω p f hcard).symm y) =
      C.pointElement a ha (frobeniusPointHom X (y (closedPoint K))) ^ n :=
  C.pointElement_comp_eq_pow (rationalPointHom y Ω) a ha _ _ n
    (galoisPointHom_comp_rationalPointHom y Ω p f hcard n hn)

/-- **(E): the geometric Frobenius of a finite extension on the stalk of a descent sheaf.** Let
`y` be a point of `X` with values in a finite field `K` with `#K = #κ(x)ⁿ`, for the image `x` of
`y`. At the geometric point over `y` with values in `Ω`, the geometric Frobenius of `K` on the
stalk of the descent sheaf of `N` is `ρ(g_xⁿ)`, where `g_x` is the Frobenius element at `x` of a
point `a` of the covering over the geometric point at `x`. The stalk is identified with `N` by
evaluation at the point `j ≫ a`, with `j` the comparison morphism of geometric points. -/
public theorem stalkLinearEquiv_geometricFrobeniusStalk (hcard : Fintype.card K = p ^ f)
    [Finite (X.residueField (y (closedPoint K)))] (n : ℕ)
    (hn : Fintype.card K = Nat.card (X.residueField (y (closedPoint K))) ^ n)
    (a : (geometricPointAt X (y (closedPoint K))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X (y (closedPoint K))).hom)
    (m : ((Scheme.pointSmallEtale (rationalGeometricPoint Ω y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj (C.descentSheaf Λ N ρ)) :
    C.stalkLinearEquiv Λ N ρ ((rationalPointHom y Ω).hom ≫ a)
        (C.rationalPointHom_comp_cover_hom y Ω a ha)
        ((geometricFrobeniusStalk (ModuleCat.{max (u + 1) v} Λ) Ω p f hcard y
          (C.descentSheaf Λ N ρ)).hom m) =
      ρ (C.pointElement a ha (frobeniusPointHom X (y (closedPoint K))) ^ n)
        (C.stalkLinearEquiv Λ N ρ ((rationalPointHom y Ω).hom ≫ a)
          (C.rationalPointHom_comp_cover_hom y Ω a ha) m) := by
  rw [← C.pointElement_galoisPointHom_eq_pow y Ω p f hcard n hn a ha]
  exact C.stalkLinearEquiv_sheafFiber_map Λ N ρ _ _ _ m

/-- **(E) for a sheaf isomorphic to a descent sheaf.** -/
public theorem stalkLinearEquivOfIso_geometricFrobeniusStalk (hcard : Fintype.card K = p ^ f)
    [Finite (X.residueField (y (closedPoint K)))] (n : ℕ)
    (hn : Fintype.card K = Nat.card (X.residueField (y (closedPoint K))) ^ n)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)} (e : F ≅ C.descentSheaf Λ N ρ)
    (a : (geometricPointAt X (y (closedPoint K))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X (y (closedPoint K))).hom)
    (m : ((Scheme.pointSmallEtale (rationalGeometricPoint Ω y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj F) :
    C.stalkLinearEquivOfIso Λ N ρ e ((rationalPointHom y Ω).hom ≫ a)
        (C.rationalPointHom_comp_cover_hom y Ω a ha)
        ((geometricFrobeniusStalk (ModuleCat.{max (u + 1) v} Λ) Ω p f hcard y F).hom m) =
      ρ (C.pointElement a ha (frobeniusPointHom X (y (closedPoint K))) ^ n)
        (C.stalkLinearEquivOfIso Λ N ρ e ((rationalPointHom y Ω).hom ≫ a)
          (C.rationalPointHom_comp_cover_hom y Ω a ha) m) := by
  rw [← C.pointElement_galoisPointHom_eq_pow y Ω p f hcard n hn a ha]
  exact C.stalkLinearEquivOfIso_sheafFiber_map Λ N ρ e _ _ _ m

end Comparison

section InverseImage

open Stacks.EtaleCohomology

variable {X' : Scheme.{u}} (g : X' ⟶ X) {K : Type u} [Field K] [Fintype K] (y' : Spec (.of K) ⟶ X')
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (p f : ℕ) [Fact p.Prime] [CharP Ω p]
  (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) r)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- **(E) for an inverse image.** Let `g : X' ⟶ X`, `y'` a point of `X'` with values in a finite
field `K`, and `x` the image of `y' ≫ g`, with `#K = #κ(x)ⁿ`. For a sheaf `F` on `X` isomorphic to
the descent sheaf of `N`, the stalk of `g⁻¹ F` at the geometric point over `y'` is `N`, and the
geometric Frobenius of `K` acts on it as `ρ(g_xⁿ)`, where `g_x` is the Frobenius element at `x`
of a point `a` of the covering over the geometric point at `x`.

This is the form of the local term of the trace formula over the extension `K` of the base field,
read on the base change `X' = X ×_k K` with `g` the first projection. -/
public theorem exists_stalk_inverseImage_geometricFrobenius (hcard : Fintype.card K = p ^ f)
    [Finite (X.residueField ((y' ≫ g) (closedPoint K)))] (n : ℕ)
    (hn : Fintype.card K = Nat.card (X.residueField ((y' ≫ g) (closedPoint K))) ^ n)
    {F : EtaleModules.{u, r} Λ X} (e : F ≅ C.descentSheaf Λ N ρ)
    (a : (geometricPointAt X ((y' ≫ g) (closedPoint K))).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt X ((y' ≫ g) (closedPoint K))).hom) :
    ∃ ε : (rationalPointStalkFunctor.{u, r} Λ Ω y').obj
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) ≃ₗ[Λ] N,
      ∀ m, ε (((geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) Ω p f hcard y').app
          ((etaleModuleInverseImage.{u, r} Λ g).obj F)).hom m) =
        ρ (C.pointElement a ha (frobeniusPointHom X ((y' ≫ g) (closedPoint K))) ^ n) (ε m) := by
  let ι := (rationalPointStalkPullbackIso Λ g Ω y' (y' ≫ g) rfl).app F
  refine ⟨ι.toLinearEquiv.trans (C.stalkLinearEquivOfIso Λ N ρ e
    ((rationalPointHom (y' ≫ g) Ω).hom ≫ a) (C.rationalPointHom_comp_cover_hom (y' ≫ g) Ω a ha)),
    fun m => ?_⟩
  show C.stalkLinearEquivOfIso Λ N ρ e _ _ (ι.hom.hom
      (((geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) Ω p f hcard y').app
        ((etaleModuleInverseImage.{u, r} Λ g).obj F)).hom m)) = _
  exact (congrArg (C.stalkLinearEquivOfIso Λ N ρ e ((rationalPointHom (y' ≫ g) Ω).hom ≫ a)
    (C.rationalPointHom_comp_cover_hom (y' ≫ g) Ω a ha)) (ConcreteCategory.congr_hom
      (geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ g Ω y' (y' ≫ g)
        rfl p f hcard F) m)).trans
    (C.stalkLinearEquivOfIso_geometricFrobeniusStalk (y' ≫ g) Ω p f Λ N ρ hcard n hn e a ha _)

end InverseImage

end AlgebraicGeometry.EtaleGaloisCovering

end
