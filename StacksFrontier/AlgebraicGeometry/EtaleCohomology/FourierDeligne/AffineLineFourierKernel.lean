module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCompactSupportVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyFreeInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Blowup.Existence
public import StacksFrontier.AlgebraicGeometry.Size.SiteAlgebraClosure

/-!
# The kernel of the composite of two Fourier transforms on the affine line

Let `k` be a finite field, `𝔸¹ = Spec k[X]` with structure map `f : 𝔸¹ ⟶ Spec k`, and
`L = L_ψ(X)` the Artin–Schreier sheaf on `𝔸¹`. The Fourier transform has kernel `μ⁻¹ L` on
`𝔸¹ ×_k 𝔸¹`, where `μ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` is the multiplication `(x, t) ↦ xt`. On the triple
product `Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u` the kernel of the composite of two Fourier transforms is
`q₁₂⁻¹ μ⁻¹ L ⊗ q₂₃⁻¹ μ⁻¹ L`, and this is `s⁻¹ L` for `s = t(x + u) : Q ⟶ 𝔸¹`, because
`xt + tu = t(x + u)`. The sheaf `s⁻¹ L` is the unit on the antidiagonal `Q_Δ = {x + u = 0}`.
These are the geometric inputs of Fourier inversion in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) through Laumon's Fourier transform.

All morphisms into affine spaces are written through their ring maps
(`Stacks.Blowup.specHomRingHom`), and the coordinates `x, t, u` of `Q` assemble into
`e : Q ⟶ Spec k[x, t, u]`, through which `μ ∘ q₁₂`, `μ ∘ q₂₃` and `s` factor.

## Main definitions

* `Stacks.EtaleCohomology.affineLineMul`: `μ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹`.
* `Stacks.EtaleCohomology.fourierTripleCoords`: `e : Q ⟶ Spec k[x, t, u]`.
* `Stacks.EtaleCohomology.fourierTripleKernelMap`: `s = t(x + u) : Q ⟶ 𝔸¹`.
* `Stacks.EtaleCohomology.affineLineOrigin`, `Stacks.EtaleCohomology.affineSpaceOrigin`: the
  origins, as geometric points.
* `Stacks.EtaleCohomology.fourierAntidiagonalι`, `Stacks.EtaleCohomology.fourierOffAntidiagonalι`:
  the closed immersion of `Q_Δ = {x + u = 0}` and the open immersion of its complement.

## Main results

* `Stacks.EtaleCohomology.tripleProduct₁₂_comp_affineLineMul`,
  `Stacks.EtaleCohomology.tripleProduct₂₃_comp_affineLineMul`: `μ ∘ q₁₂ = xt`, `μ ∘ q₂₃ = tu`.
* `Stacks.EtaleCohomology.nonempty_fourierTripleKernel_tensor_iso`:
  `q₁₂⁻¹ μ⁻¹ L ⊗ q₂₃⁻¹ μ⁻¹ L ≅ s⁻¹ L`.
* `Stacks.EtaleCohomology.nonempty_fourierAntidiagonal_kernel_iso_tensorUnit`:
  `(s⁻¹ L)|_{Q_Δ} ≅ 𝟙_`.
* `Stacks.EtaleCohomology.range_fourierOffAntidiagonalι`: `Q_U = Q ∖ Q_Δ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Blowup

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

/-- The ring map of a composite `g ≫ f` is the ring map of `f` followed by `g` on global
sections. -/
theorem specHomRingHom_comp (g : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) :
    specHomRingHom (g ≫ f) = g.appTop.hom.comp (specHomRingHom f) := by
  simp only [specHomRingHom, Scheme.Hom.comp_appTop]
  rfl

/-- The ring map of a composite `g ≫ f` sends `a` to the pullback along `g` of the image of `a`
under the ring map of `f`. -/
theorem specHomRingHom_comp_apply (g : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) (a : R) :
    specHomRingHom (g ≫ f) a = g.appTop.hom (specHomRingHom f a) := by
  rw [specHomRingHom_comp, RingHom.comp_apply]

/-- The ring map of `f ≫ Spec β` is `β` followed by the ring map of `f`. -/
theorem specHomRingHom_comp_specMap (f : X ⟶ Spec (CommRingCat.of R)) (β : S →+* R) :
    specHomRingHom (f ≫ Spec.map (CommRingCat.ofHom β)) = (specHomRingHom f).comp β := by
  have h : (Spec.map (CommRingCat.ofHom β)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom β ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [specHomRingHom, Scheme.Hom.comp_appTop, h, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The ring map of `X.toSpecΓ ≫ Spec α` is `α`. -/
theorem specHomRingHom_toSpecΓ_comp_specMap (α : R →+* Γ(X, ⊤)) :
    specHomRingHom (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom α)) = α := by
  rw [specHomRingHom_comp_specMap]
  change ((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop).hom.comp α = α
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl

/-- Morphisms into `Spec R` are determined by their ring maps. -/
theorem hom_ext_of_specHomRingHom {f f' : X ⟶ Spec (CommRingCat.of R)}
    (h : specHomRingHom f = specHomRingHom f') : f = f' := by
  rw [← toSpecΓ_comp_specMap_specHomRingHom f, ← toSpecΓ_comp_specMap_specHomRingHom f', h]

end Stacks.Blowup

namespace Stacks.EtaleCohomology

open Stacks.Blowup Stacks.ArtinSchreier

variable (k : Type u) [Field k]

section Coordinates

/-- The `k`-algebra map `k → Γ(Y, ⊤)` of a scheme `Y` over `Spec k`. -/
abbrev structureRingHom {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of k)) : k →+* Γ(Y, ⊤) :=
  specHomRingHom π

/-- The coordinate `h^* X ∈ Γ(Y, ⊤)` of a morphism `h : Y ⟶ 𝔸¹_k`. -/
abbrev affineLineCoordinate {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of (Polynomial k))) :
    Γ(Y, ⊤) :=
  specHomRingHom h Polynomial.X

/-- **The multiplication `μ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹`, `(x, t) ↦ xt`**: the morphism with ring map
`X ↦ pr₁^* X · pr₂^* X`. -/
def affineLineMul :
    pullback (affineLineStructureMap k) (affineLineStructureMap k) ⟶
      Spec (CommRingCat.of (Polynomial k)) :=
  Scheme.toSpecΓ _ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
    (structureRingHom k (pullback.fst _ _ ≫ affineLineStructureMap k))
    (affineLineCoordinate k (pullback.fst _ _) * affineLineCoordinate k (pullback.snd _ _))))

local notation "𝔸f" => affineLineStructureMap k

/-- **The coordinates `(x, t, u)` of the triple product `𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹`**, as a morphism to
`Spec k[x, t, u]`. -/
def fourierTripleCoords :
    tripleProduct 𝔸f 𝔸f 𝔸f ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) :=
  Scheme.toSpecΓ _ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (structureRingHom k ((tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f))
    ![affineLineCoordinate k (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _),
      affineLineCoordinate k (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _),
      affineLineCoordinate k (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _)]))

/-- The `k`-algebra map `k[X] → k[x, t, u]`, `X ↦ xt`. -/
abbrev fourierTripleXT : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k :=
  Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The `k`-algebra map `k[X] → k[x, t, u]`, `X ↦ tu`. -/
abbrev fourierTripleTU : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k :=
  Polynomial.aeval (MvPolynomial.X 1 * MvPolynomial.X 2)

/-- The `k`-algebra map `k[X] → k[x, t, u]`, `X ↦ t(x + u)`. -/
abbrev fourierTripleSum : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k :=
  Polynomial.aeval (MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 2))

/-- **The kernel map `s = t(x + u) : 𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹`.** -/
def fourierTripleKernelMap : tripleProduct 𝔸f 𝔸f 𝔸f ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  fourierTripleCoords k ≫ Spec.map (CommRingCat.ofHom (fourierTripleSum k).toRingHom)

/-- The structure morphisms to `Spec k` of `𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹` through `q₂₃` and through `q₁₂`
agree. -/
theorem structureRingHom_tripleProduct₂₃ :
    (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f =
      (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f := by
  rw [← pullback.condition, Category.assoc, Category.assoc, pullback.condition]

/-- The ring map of `fourierTripleCoords` sends `x, t, u` to the three coordinates of
`𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹`. -/
theorem specHomRingHom_fourierTripleCoords :
    specHomRingHom (fourierTripleCoords k) = MvPolynomial.eval₂Hom
      (structureRingHom k ((tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f))
      ![affineLineCoordinate k (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _),
        affineLineCoordinate k (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _),
        affineLineCoordinate k (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _)] :=
  specHomRingHom_toSpecΓ_comp_specMap _

/-- The ring map of `affineLineMul` sends `X` to `pr₁^* X · pr₂^* X`. -/
theorem specHomRingHom_affineLineMul :
    specHomRingHom (affineLineMul k) = Polynomial.eval₂RingHom
      (structureRingHom k (pullback.fst _ _ ≫ affineLineStructureMap k))
      (affineLineCoordinate k (pullback.fst _ _) * affineLineCoordinate k (pullback.snd _ _)) :=
  specHomRingHom_toSpecΓ_comp_specMap _

/-- `q ≫ μ = e ≫ Spec φ` once the ring maps agree on `k` and on `X`. -/
private theorem comp_affineLineMul_eq_coords_comp
    (q : tripleProduct 𝔸f 𝔸f 𝔸f ⟶ pullback 𝔸f 𝔸f)
    (φ : Polynomial k →ₐ[k] MvPolynomial (Fin 3) k)
    (hq : (q ≫ pullback.fst _ _) ≫ 𝔸f = (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f)
    (hφ : specHomRingHom (fourierTripleCoords k) (φ Polynomial.X) =
      affineLineCoordinate k (q ≫ pullback.fst _ _) *
        affineLineCoordinate k (q ≫ pullback.snd _ _)) :
    q ≫ affineLineMul k = fourierTripleCoords k ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  refine hom_ext_of_specHomRingHom ?_
  rw [specHomRingHom_comp, specHomRingHom_comp_specMap, specHomRingHom_affineLineMul]
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, show φ (Polynomial.C c) = MvPolynomial.C c from
      φ.commutes c, specHomRingHom_fourierTripleCoords, MvPolynomial.eval₂Hom_C, ← hq,
      Category.assoc, specHomRingHom_comp_apply]
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ, affineLineCoordinate, specHomRingHom_comp_apply]

/-- **`μ ∘ q₁₂ = xt`** on `𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹`. -/
theorem tripleProduct₁₂_comp_affineLineMul :
    tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ affineLineMul k =
      fourierTripleCoords k ≫ Spec.map (CommRingCat.ofHom (fourierTripleXT k).toRingHom) :=
  comp_affineLineMul_eq_coords_comp k _ _ rfl (by
    simp only [specHomRingHom_fourierTripleCoords, Polynomial.aeval_X, map_mul,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one])

/-- **`μ ∘ q₂₃ = tu`** on `𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹`. -/
theorem tripleProduct₂₃_comp_affineLineMul :
    tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ affineLineMul k =
      fourierTripleCoords k ≫ Spec.map (CommRingCat.ofHom (fourierTripleTU k).toRingHom) :=
  comp_affineLineMul_eq_coords_comp k _ _ (structureRingHom_tripleProduct₂₃ k) (by
    simp only [specHomRingHom_fourierTripleCoords, Polynomial.aeval_X, map_mul,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, show tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f =
        tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f from pullback.condition])

end Coordinates

section Origin

/-- **The origin of `𝔸¹_k`**, as a geometric point with values in an algebraic closure of `k`. -/
def affineLineOrigin : GeometricPoint (Spec (CommRingCat.of (Polynomial k))) where
  residueField := AlgebraicClosure k
  hom := Spec.map
    (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k (AlgebraicClosure k)) 0))

/-- **The origin of `𝔸ⁿ_k = Spec k[X_i, i ∈ σ]`**, as a geometric point with values in an algebraic
closure of `k`. -/
def affineSpaceOrigin (σ : Type) : GeometricPoint (Spec (CommRingCat.of (MvPolynomial σ k))) where
  residueField := AlgebraicClosure k
  hom := Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k (AlgebraicClosure k)) 0))

/-- A `k`-algebra map `k[X] → k[X_i]` vanishing at the origin maps the origin to the origin. -/
theorem affineSpaceOrigin_map {σ : Type} (φ : Polynomial k →ₐ[k] MvPolynomial σ k)
    (hφ : MvPolynomial.constantCoeff (φ Polynomial.X) = 0) :
    (affineSpaceOrigin k σ).map (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      affineLineOrigin k := by
  change GeometricPoint.mk (AlgebraicClosure k) (Spec.map _ ≫ Spec.map _) =
    GeometricPoint.mk (AlgebraicClosure k) (Spec.map _)
  rw [← Spec.map_comp]
  congr 2
  ext1
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_eval₂RingHom,
      ← Polynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂Hom_C]
    change _ = Polynomial.eval₂ _ _ (Polynomial.C c)
    rw [Polynomial.eval₂_C]
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      MvPolynomial.eval₂Hom_zero_apply, hφ, map_zero]

/-- A `k`-algebra map `k[X_i] → k[Y_j]` sending each `X_i` to a polynomial without constant term
maps the origin to the origin. -/
theorem affineSpaceOrigin_map_mvPolynomial {σ τ : Type}
    (φ : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (hφ : ∀ i, MvPolynomial.constantCoeff (φ (.X i)) = 0) :
    (affineSpaceOrigin k τ).map (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      affineSpaceOrigin k σ := by
  change GeometricPoint.mk (AlgebraicClosure k) (Spec.map _ ≫ Spec.map _) =
    GeometricPoint.mk (AlgebraicClosure k) (Spec.map _)
  rw [← Spec.map_comp]
  congr 2
  ext1
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      MvPolynomial.eval₂Hom_zero_apply]
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.constantCoeff_C]
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.eval₂Hom_zero_apply, hφ, map_zero,
      MvPolynomial.eval₂Hom_X', Pi.zero_apply]

end Origin

section Size

/-- **`𝔸ⁿ` over a finite field is an object of every big étale site**: `k[X_i, i ∈ σ]` is
countable for `k` and `σ` finite, and the cutoff is uncountable. -/
theorem schemeSizeBelow_spec_mvPolynomial (B : BigEtaleSite.{u}) [Finite k] (σ : Type)
    [Finite σ] : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (MvPolynomial σ k))) :=
  (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2
    (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)

/-- **`𝔸¹` over a finite field is an object of every big étale site.** -/
theorem schemeSizeBelow_spec_polynomial (B : BigEtaleSite.{u}) [Finite k] :
    schemeSizeBelow B.cutoff (Spec (CommRingCat.of (Polynomial k))) :=
  (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 (Polynomial.cardinalMk_le_max.trans_lt
    (max_lt ((Cardinal.mk_le_aleph0).trans_lt B.aleph0_lt_cutoff) B.aleph0_lt_cutoff))

end Size

section Antidiagonal

/-- The `k`-algebra map `k[x, t, u] → k[x, t]`, `u ↦ -x`, whose kernel is `(x + u)`. -/
abbrev fourierAntidiagonalRingHom : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, -MvPolynomial.X 0]

/-- The section `k[x, t] → k[x, t, u]` of `fourierAntidiagonalRingHom`. -/
abbrev fourierAntidiagonalSection : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1]

/-- `fourierAntidiagonalSection` is a section of `fourierAntidiagonalRingHom`. -/
theorem fourierAntidiagonalRingHom_comp_section :
    (fourierAntidiagonalRingHom k).comp (fourierAntidiagonalSection k) = AlgHom.id k _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp

/-- The `k`-algebra map `k[x, t, u] → k[x, t]`, `u ↦ -x`, is surjective. -/
theorem surjective_fourierAntidiagonalRingHom :
    Function.Surjective (fourierAntidiagonalRingHom k) := fun a =>
  ⟨fourierAntidiagonalSection k a, by
    rw [← AlgHom.comp_apply, fourierAntidiagonalRingHom_comp_section, AlgHom.id_apply]⟩

/-- **The kernel of `u ↦ -x` is the ideal `(x + u)`.** -/
theorem ker_fourierAntidiagonalRingHom :
    RingHom.ker (fourierAntidiagonalRingHom k).toRingHom =
      Ideal.span {(MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)} := by
  set I := Ideal.span {(MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)}
  refine le_antisymm (fun a ha => ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2
    (RingHom.mem_ker.2 (by simp))))
  have h : (Ideal.Quotient.mkₐ k I).comp
      ((fourierAntidiagonalSection k).comp (fourierAntidiagonalRingHom k)) =
      Ideal.Quotient.mkₐ k I := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    fin_cases i
    · simp
    · simp
    · have : (fourierAntidiagonalSection k) ((fourierAntidiagonalRingHom k) (MvPolynomial.X 2)) -
          MvPolynomial.X 2 = -(MvPolynomial.X 0 + MvPolynomial.X 2) := by
        simp only [MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, map_neg, Matrix.cons_val_zero]
        ring
      exact this ▸ I.neg_mem (Ideal.subset_span rfl)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, ← h, AlgHom.comp_apply,
    AlgHom.comp_apply, show (fourierAntidiagonalRingHom k) a = 0 from RingHom.mem_ker.1 ha,
    map_zero, map_zero]

local notation "𝔸f" => affineLineStructureMap k

/-- **The antidiagonal `Q_Δ = {x + u = 0}`** of `𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u`, as the inverse image of
`Spec k[x, t] ↪ Spec k[x, t, u]`, `u = -x`. -/
abbrev fourierAntidiagonal : Scheme.{u} :=
  pullback (fourierTripleCoords k)
    (Spec.map (CommRingCat.ofHom (fourierAntidiagonalRingHom k).toRingHom))

/-- The closed immersion `Q_Δ ⟶ Q`. -/
abbrev fourierAntidiagonalι : fourierAntidiagonal k ⟶ tripleProduct 𝔸f 𝔸f 𝔸f :=
  pullback.fst _ _

/-- The inclusion `Q_Δ ⟶ Q` of the antidiagonal is a closed immersion. -/
instance isClosedImmersion_fourierAntidiagonalι : IsClosedImmersion (fourierAntidiagonalι k) :=
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (fourierAntidiagonalRingHom k).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_fourierAntidiagonalRingHom k)
  inferInstance

/-- **The complement `Q_U = {x + u ≠ 0}` of the antidiagonal**, as the inverse image of the
basic open `D(x + u) ⊆ Spec k[x, t, u]`. -/
abbrev fourierOffAntidiagonal : Scheme.{u} :=
  pullback (fourierTripleCoords k) (Spec.map (CommRingCat.ofHom (algebraMap
    (MvPolynomial (Fin 3) k)
    (Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)))))

/-- The open immersion `Q_U ⟶ Q`. -/
abbrev fourierOffAntidiagonalι : fourierOffAntidiagonal k ⟶ tripleProduct 𝔸f 𝔸f 𝔸f :=
  pullback.fst _ _

/-- The inclusion `Q_U ⟶ Q` of the complement of the antidiagonal is an open immersion. -/
instance isOpenImmersion_fourierOffAntidiagonalι : IsOpenImmersion (fourierOffAntidiagonalι k) :=
  inferInstance

/-- **`Q_U` is the complement of `Q_Δ`.** -/
theorem range_fourierOffAntidiagonalι :
    Set.range (fourierOffAntidiagonalι k).base = (Set.range (fourierAntidiagonalι k).base)ᶜ := by
  have h₁ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 3) k)
      (Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 2 :
        MvPolynomial (Fin 3) k))))).base =
      (PrimeSpectrum.basicOpen (MvPolynomial.X 0 + MvPolynomial.X 2 :
        MvPolynomial (Fin 3) k) : Set (PrimeSpectrum (MvPolynomial (Fin 3) k))) :=
    PrimeSpectrum.localization_away_comap_range _ _
  have h₂ : Set.range (Spec.map (CommRingCat.ofHom
      (fourierAntidiagonalRingHom k).toRingHom)).base =
      PrimeSpectrum.zeroLocus {(MvPolynomial.X 0 + MvPolynomial.X 2 :
        MvPolynomial (Fin 3) k)} := by
    have := range_comap_of_surjective _ (fourierAntidiagonalRingHom k).toRingHom
      (surjective_fourierAntidiagonalRingHom k)
    rw [ker_fourierAntidiagonalRingHom, PrimeSpectrum.zeroLocus_span] at this
    exact this
  have e₁ := Scheme.Pullback.range_fst (fourierTripleCoords k) (Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin 3) k) (Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 2 :
      MvPolynomial (Fin 3) k)))))
  have e₂ := Scheme.Pullback.range_fst (fourierTripleCoords k) (Spec.map (CommRingCat.ofHom
    (fourierAntidiagonalRingHom k).toRingHom))
  rw [h₁] at e₁
  rw [h₂] at e₂
  change Set.range ⇑(fourierOffAntidiagonalι k) = (Set.range ⇑(fourierAntidiagonalι k))ᶜ
  rw [e₁, e₂]
  ext p
  exact Iff.of_eq (congrArg (fun S : Set (PrimeSpectrum (MvPolynomial (Fin 3) k)) =>
    (fourierTripleCoords k) p ∈ S) (PrimeSpectrum.basicOpen_eq_zeroLocus_compl _))

end Antidiagonal

section Kernel

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

local notation "𝔸f" => affineLineStructureMap k

variable [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- Sheafification of étale sheaves of `Λ`-modules, at the universes of `EtaleModules.{u, 0}`
(pinned, so that the monoidal structure does not leave a universe metavariable). -/
local instance hasSheafify_etaleModules_fourierKernel (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafifyEtale X Λ

/-- **The Artin–Schreier sheaf `L_ψ(X)` on `𝔸¹_k`**, with base point the origin. -/
abbrev affineLineArtinSchreierSheaf :
    EtaleModules.{u, 0} Λ (Spec (CommRingCat.of (Polynomial k))) :=
  artinSchreierLevelSheaf k (Polynomial k) Polynomial.X Λ ψ B (schemeSizeBelow_spec_polynomial k B)
    (affineLineOrigin k) p₀

/-- **The kernel of the composite of two Fourier transforms**:
`q₁₂⁻¹ μ⁻¹ L ⊗ q₂₃⁻¹ μ⁻¹ L ≅ s⁻¹ L` on `𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u`, with `s = t(x + u)`, because
`xt + tu = t(x + u)`. -/
theorem nonempty_fourierTripleKernel_tensor_iso :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f)).obj
          ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀)) ⊗
        (etaleModuleInverseImage.{u, 0} Λ (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f)).obj
          ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀)) ≅
      (etaleModuleInverseImage.{u, 0} Λ (fourierTripleKernelMap k)).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀)) := by
  obtain ⟨m⟩ := nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso (k := k)
    (g := Polynomial.X) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (hX' := schemeSizeBelow_spec_mvPolynomial k B (Fin 3)) (e := fourierTripleCoords k)
    (φ₁ := fourierTripleXT k) (φ₂ := fourierTripleTU k) (φ₃ := fourierTripleSum k)
    (hφ := by simp only [Polynomial.aeval_X]; ring)
    (hh₁ := tripleProduct₁₂_comp_affineLineMul k) (hh₂ := tripleProduct₂₃_comp_affineLineMul k)
    (hh₃ := rfl) (p₀ := p₀) (y := affineSpaceOrigin k (Fin 3))
    (hy₁ := affineSpaceOrigin_map k _ (by simp)) (hy₂ := affineSpaceOrigin_map k _ (by simp))
    (hy₃ := affineSpaceOrigin_map k _ (by simp))
  exact ⟨(((etaleModuleInverseImageCompIso Λ _ (affineLineMul k)).app _).symm ⊗ᵢ
    ((etaleModuleInverseImageCompIso Λ _ (affineLineMul k)).app _).symm) ≪≫ m⟩

omit [Fintype k] in
/-- On the antidiagonal `Q_Δ`, the kernel map `s = t(x + u)` is the projection `Q_Δ ⟶ Spec k[x, t]`
followed by the morphism to `𝔸¹` with ring map `X ↦ t(x + (-x))`. -/
theorem fourierAntidiagonalι_comp_fourierTripleKernelMap :
    fourierAntidiagonalι k ≫ fourierTripleKernelMap k = pullback.snd _ _ ≫
      Spec.map (CommRingCat.ofHom
        ((fourierAntidiagonalRingHom k).comp (fourierTripleSum k)).toRingHom) := by
  rw [fourierTripleKernelMap, ← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp]
  rfl

/-- **The kernel `s⁻¹ L = L_ψ(t(x + u))` is the unit on the antidiagonal `x + u = 0`.** -/
theorem nonempty_fourierAntidiagonal_kernel_iso_tensorUnit :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (fourierAntidiagonalι k)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fourierTripleKernelMap k)).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀)) ≅
      𝟙_ (EtaleModules.{u, 0} Λ (fourierAntidiagonal k))) := by
  obtain ⟨a⟩ := nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_tensorUnit (k := k)
    (g := Polynomial.X) (φ := (fourierAntidiagonalRingHom k).comp (fourierTripleSum k)) (Λ := Λ)
    (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (hX' := schemeSizeBelow_spec_mvPolynomial k B (Fin 2)) (e := pullback.snd _ _) (c := 0)
    (hc := by simp [zero_pow Fintype.card_ne_zero])
    (hh := fourierAntidiagonalι_comp_fourierTripleKernelMap k) (p₀ := p₀)
    (y := affineSpaceOrigin k (Fin 2)) (hy := affineSpaceOrigin_map k _ (by simp))
  exact ⟨((etaleModuleInverseImageCompIso Λ _ _).app _).symm ≪≫ a⟩

variable {Λ} in
omit [Finite Λ] in
/-- **Tensoring with an étale-locally free sheaf of finite rank is exact.** -/
theorem isExactTensorRight_of_isLocallyFreeEtaleModule {X : Scheme.{u}}
    {N : EtaleModules.{u, 0} Λ X} (hN : IsLocallyFreeEtaleModule Λ N) : IsExactTensorRight Λ N :=
  additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith N hN

/-- The Artin–Schreier sheaf `L_ψ(X)` is étale-locally free of rank one. -/
theorem isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf :
    IsLocallyFreeEtaleModule Λ (affineLineArtinSchreierSheaf k Λ ψ B p₀) :=
  isLocallyFreeEtaleModule_artinSchreierLevelSheaf (k := k) (A := Polynomial k)
    (g := Polynomial.X) (Λ := Λ) (ψ := ψ) (B := B) (hX := schemeSizeBelow_spec_polynomial k B)
    (affineLineOrigin k) p₀

/-- **The Fourier kernel `μ⁻¹ L_ψ` on `𝔸¹ ×_k 𝔸¹` is étale-locally free of rank one.** -/
theorem isLocallyFreeEtaleModule_fourierKernel :
    IsLocallyFreeEtaleModule Λ ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀)) :=
  isLocallyFreeEtaleModule_inverseImage Λ _
    (isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf k Λ ψ B p₀)

end Kernel

end Stacks.EtaleCohomology
