module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem

/-!
# The triangle thickenings, their two-open cover and the glueing cocycle

Let `K` be a field and let `X_n = Spec R_n`, `R_n = K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)`, be the
`n`-th thickening of the triangle of three lines `x = 0`, `y = 0`, `x + y = 1`. This file sets up
the Čech data out of which the non-torsion objects of Stacks 0CXX are glued.

The two opens `U = D(1 - x)` and `W = D(1 - y)` of `X_n` are the complements of the vertices
`(1, 0)` and `(0, 1)`; they cover `X_n` because the third vertex-free point `(1, 1)` does not lie
on the triangle, that is, `1 - x` and `1 - y` are coprime in `R_n`. Both are connected, and their
intersection `D((1 - x)(1 - y))` is the disjoint union of two pieces: the open edge of the line
`x + y = 1` (where `xy` is a unit) and the union of the two other lines minus the two vertices
(where `x + y - 1` is a unit). Indeed `(1 - x)(1 - y) = xy - (x + y - 1)`, so on the intersection
the two elements `xy` and `x + y - 1` are coprime, while the product of their `(n + 1)`-st powers
vanishes. By the Chinese remainder theorem the coordinate ring of the intersection is the product
of the coordinate rings of the two pieces, and a morphism out of the intersection may be
prescribed piece by piece (`AlgebraicGeometry.specPiecewise`). The glueing cocycle of the source
is the morphism to a group scheme which is a given point `η` on the open edge and the unit on
the other piece.

## Main definitions

* `AlgebraicGeometry.ringEquivProdOfIsCoprime`: a ring split by two coprime ideals meeting in
  zero is the product of the two quotients.
* `AlgebraicGeometry.specPiecewise` and `AlgebraicGeometry.overPiecewise`: a morphism out of the
  spectrum of such a ring, prescribed on the two pieces, as a morphism of schemes and as a
  morphism of schemes over `Spec k`.
* `AlgebraicGeometry.specOverField` and `AlgebraicGeometry.specOverFieldMap`: the spectrum of a
  `K`-algebra as a scheme over `Spec k`, and the morphism induced by a map of `K`-algebras.
* `Deformation.Artin.triangleLevel`, `Deformation.Artin.triangleX`,
  `Deformation.Artin.triangleY`: the ring `R_n` and its two coordinates.
* `Deformation.Artin.triangleLevelLift` and `Deformation.Artin.triangleAwayLift`: the
  `K`-algebra maps out of `R_n`, and out of a localization of it, given by a solution of
  `uv(u + v - 1) = 0`.
* `Deformation.Artin.triangleLeft`, `Deformation.Artin.triangleRight` and
  `Deformation.Artin.triangleOverlap`: the coordinate rings of `U`, `W` and `U ∩ W`, with the
  restrictions `Deformation.Artin.triangleLeftToOverlap` and
  `Deformation.Artin.triangleRightToOverlap`.
* `Deformation.Artin.triangleOverlapRestIdeal` and `Deformation.Artin.triangleOverlapEdgeIdeal`:
  the ideals of the two pieces of `U ∩ W`.
* `Deformation.Artin.triangleCocycle`: the glueing cocycle along a point `pt` of a group scheme,
  `pt` on the open edge and the unit on the other piece.

## Main results

* `Deformation.Artin.isCoprime_one_sub_triangleX_one_sub_triangleY`: the two opens cover `X_n`.
* `Deformation.Artin.isCoprime_triangleOverlapRestIdeal_triangleOverlapEdgeIdeal` and
  `Deformation.Artin.triangleOverlapRestIdeal_inf_triangleOverlapEdgeIdeal`: the two pieces of
  `U ∩ W` are complementary.
* `AlgebraicGeometry.Spec_map_comp_specPiecewise_left`,
  `AlgebraicGeometry.Spec_map_comp_specPiecewise_right` and
  `AlgebraicGeometry.specPiecewise_ext`: a point of one piece sees the value prescribed there, and
  a morphism out of `Spec S` is determined by its two pieces.
* `Deformation.Artin.specOverFieldMap_comp_triangleCocycle_of_rest` and
  `Deformation.Artin.specOverFieldMap_comp_triangleCocycle_of_edge`: the values of the cocycle at
  the points of the two pieces.
* `Deformation.Artin.specOverFieldMap_triangleOverlapTransition_comp_triangleCocycle`: the
  cocycle of level `n + 1` restricts to the cocycle of level `n`.

## Implementation notes

The cover has two members rather than the three complements of the vertices: the two
complements of `(1, 0)` and `(0, 1)` already cover the triangle, and their intersection already
has the two components that make the cocycle non-trivial. Every scheme here is affine and every
open a basic open, so the Čech data are rings and maps of `K`-algebras.

The glueing of the objects of `[Spec(k)/A]` out of this cocycle, by the effectivity of descent
data for the presentation of the quotient stack (Stacks 044X part (4),
`AlgebraicGeometry.Stack.effective_presentingDescentDatum`), is not in this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-! ### Morphisms out of the spectrum of a ring split by two coprime ideals -/

section Piecewise

variable {S : Type u} [CommRing S] {I J : Ideal S} (hIJ : IsCoprime I J) (hIJ0 : I ⊓ J = ⊥)

/-- A ring split by two coprime ideals meeting in zero is the product of the two quotients
(the Chinese remainder theorem). -/
def ringEquivProdOfIsCoprime : S ≃+* (S ⧸ I) × (S ⧸ J) :=
  (RingEquiv.quotientBot S).symm.trans
    ((Ideal.quotEquivOfEq hIJ0.symm).trans (Ideal.quotientInfEquivQuotientProd I J hIJ))

@[simp]
theorem ringEquivProdOfIsCoprime_apply (s : S) :
    ringEquivProdOfIsCoprime hIJ hIJ0 s = (Ideal.Quotient.mk I s, Ideal.Quotient.mk J s) :=
  rfl

/-- The first projection of the splitting is the quotient map by `I`. -/
theorem quotientMk_comp_ringEquivProdOfIsCoprime_symm :
    (Ideal.Quotient.mk I).comp (ringEquivProdOfIsCoprime hIJ hIJ0).symm.toRingHom =
      RingHom.fst _ _ := by
  ext p
  obtain ⟨s, rfl⟩ := (ringEquivProdOfIsCoprime hIJ hIJ0).surjective p
  exact congrArg _ ((ringEquivProdOfIsCoprime hIJ hIJ0).symm_apply_apply s)

/-- The second projection of the splitting is the quotient map by `J`. -/
theorem quotientMk_comp_ringEquivProdOfIsCoprime_symm' :
    (Ideal.Quotient.mk J).comp (ringEquivProdOfIsCoprime hIJ hIJ0).symm.toRingHom =
      RingHom.snd _ _ := by
  ext p
  obtain ⟨s, rfl⟩ := (ringEquivProdOfIsCoprime hIJ hIJ0).surjective p
  exact congrArg _ ((ringEquivProdOfIsCoprime hIJ hIJ0).symm_apply_apply s)

variable {Z : Scheme.{u}}

/-- The morphism out of `Spec S` which is `φ₀` on the piece `Spec (S ⧸ I)` and `φ₁` on the piece
`Spec (S ⧸ J)`, for two coprime ideals `I`, `J` of `S` meeting in zero. -/
def specPiecewise (φ₀ : Spec (.of (S ⧸ I)) ⟶ Z) (φ₁ : Spec (.of (S ⧸ J)) ⟶ Z) :
    Spec (.of S) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (ringEquivProdOfIsCoprime hIJ hIJ0).symm.toRingHom) ≫
    inv (coprodSpec (S ⧸ I) (S ⧸ J)) ≫ coprod.desc φ₀ φ₁

/-- The piecewise morphism restricts to `φ₀` on the piece `Spec (S ⧸ I)`. -/
@[reassoc]
theorem Spec_map_mk_comp_specPiecewise_left (φ₀ : Spec (.of (S ⧸ I)) ⟶ Z)
    (φ₁ : Spec (.of (S ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ specPiecewise hIJ hIJ0 φ₀ φ₁ = φ₀ := by
  rw [specPiecewise, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotientMk_comp_ringEquivProdOfIsCoprime_symm, ← coprodSpec_inl, Category.assoc,
    IsIso.hom_inv_id_assoc, coprod.inl_desc]

/-- The piecewise morphism restricts to `φ₁` on the piece `Spec (S ⧸ J)`. -/
@[reassoc]
theorem Spec_map_mk_comp_specPiecewise_right (φ₀ : Spec (.of (S ⧸ I)) ⟶ Z)
    (φ₁ : Spec (.of (S ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ specPiecewise hIJ hIJ0 φ₀ φ₁ = φ₁ := by
  rw [specPiecewise, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotientMk_comp_ringEquivProdOfIsCoprime_symm', ← coprodSpec_inr, Category.assoc,
    IsIso.hom_inv_id_assoc, coprod.inr_desc]

include hIJ hIJ0 in
/-- Two morphisms out of `Spec S` agree as soon as they agree on the two pieces. -/
theorem specPiecewise_ext {f g : Spec (.of S) ⟶ Z}
    (h₀ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g)
    (h₁ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g) : f = g := by
  set e := ringEquivProdOfIsCoprime hIJ hIJ0
  have hinv : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id]
  have key : ∀ h : Spec (.of S) ⟶ Z, h = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      inv (coprodSpec (S ⧸ I) (S ⧸ J)) ≫ (coprodSpec (S ⧸ I) (S ⧸ J) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ h) := by
    intro h
    rw [IsIso.inv_hom_id_assoc, reassoc_of% hinv]
  have hfst : (RingHom.fst (S ⧸ I) (S ⧸ J)).comp e.toRingHom = Ideal.Quotient.mk I := by
    ext s
    simp [e]
  have hsnd : (RingHom.snd (S ⧸ I) (S ⧸ J)).comp e.toRingHom = Ideal.Quotient.mk J := by
    ext s
    simp [e]
  have hl : ∀ h : Spec (.of S) ⟶ Z, coprod.inl ≫ coprodSpec (S ⧸ I) (S ⧸ J) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ h =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ h := by
    intro h
    rw [coprodSpec_inl_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hfst]
  have hr : ∀ h : Spec (.of S) ⟶ Z, coprod.inr ≫ coprodSpec (S ⧸ I) (S ⧸ J) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ h =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ h := by
    intro h
    rw [coprodSpec_inr_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hsnd]
  rw [key f, key g]
  congr 2
  refine coprod.hom_ext ?_ ?_
  · rw [hl, hl, h₀]
  · rw [hr, hr, h₁]

/-- A point of `Spec S` lying on the piece `Spec (S ⧸ I)` sees `φ₀`. -/
theorem Spec_map_comp_specPiecewise_left {L : Type u} [CommRing L] (ψ : S →+* L)
    (hψ : I ≤ RingHom.ker ψ) (φ₀ : Spec (.of (S ⧸ I)) ⟶ Z) (φ₁ : Spec (.of (S ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom ψ) ≫ specPiecewise hIJ hIJ0 φ₀ φ₁ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ hψ)) ≫ φ₀ := by
  have h : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ hψ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [h, Category.assoc, Spec_map_mk_comp_specPiecewise_left]

/-- A point of `Spec S` lying on the piece `Spec (S ⧸ J)` sees `φ₁`. -/
theorem Spec_map_comp_specPiecewise_right {L : Type u} [CommRing L] (ψ : S →+* L)
    (hψ : J ≤ RingHom.ker ψ) (φ₀ : Spec (.of (S ⧸ I)) ⟶ Z) (φ₁ : Spec (.of (S ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom ψ) ≫ specPiecewise hIJ hIJ0 φ₀ φ₁ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J ψ hψ)) ≫ φ₁ := by
  have h : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J ψ hψ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [h, Category.assoc, Spec_map_mk_comp_specPiecewise_right]

end Piecewise

/-! ### Spectra of algebras over a field, as schemes over a smaller field -/

section SpecOver

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

/-- The spectrum of a `K`-algebra `T`, as a scheme over `Spec k` through `Spec K`. -/
abbrev specOverField (T : Type u) [CommRing T] [Algebra K T] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K T)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k K)))

variable {k K}

/-- The morphism of schemes over `Spec k` induced by a map of `K`-algebras. -/
def specOverFieldMap {T T' : Type u} [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
    (ψ : T →ₐ[K] T') : specOverField k K T' ⟶ specOverField k K T :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    dsimp
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

@[simp]
theorem specOverFieldMap_left {T T' : Type u} [CommRing T] [Algebra K T] [CommRing T']
    [Algebra K T'] (ψ : T →ₐ[K] T') :
    (specOverFieldMap (k := k) ψ).left = Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
  rfl

/-- `specOverFieldMap` sends the identity to the identity. -/
@[simp]
theorem specOverFieldMap_id {T : Type u} [CommRing T] [Algebra K T] :
    specOverFieldMap (k := k) (AlgHom.id K T) = 𝟙 _ := by
  ext1
  simp only [specOverFieldMap_left, Over.id_left]
  exact Spec.map_id _

/-- `specOverFieldMap` turns composition of algebra maps into composition of morphisms. -/
theorem specOverFieldMap_comp {T T' T'' : Type u} [CommRing T] [Algebra K T] [CommRing T']
    [Algebra K T'] [CommRing T''] [Algebra K T''] (ψ : T →ₐ[K] T') (ψ' : T' →ₐ[K] T'') :
    specOverFieldMap (k := k) ψ' ≫ specOverFieldMap ψ = specOverFieldMap (ψ'.comp ψ) := by
  ext1
  simp only [Over.comp_left, specOverFieldMap_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end SpecOver

/-! ### Morphisms to a scheme over `Spec k` prescribed on two pieces -/

section OverPiecewise

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
  {S : Type u} [CommRing S] [Algebra K S] {I J : Ideal S} (hIJ : IsCoprime I J)
  (hIJ0 : I ⊓ J = ⊥) {Z : Over (Spec (.of k))}

/-- The morphism of schemes over `Spec k` out of `Spec S` which is `a` on `Spec (S ⧸ I)` and `b` on
`Spec (S ⧸ J)`. -/
def overPiecewise (a : specOverField k K (S ⧸ I) ⟶ Z) (b : specOverField k K (S ⧸ J) ⟶ Z) :
    specOverField k K S ⟶ Z :=
  Over.homMk (specPiecewise hIJ hIJ0 a.left b.left) (by
    refine specPiecewise_ext hIJ hIJ0 ?_ ?_
    · rw [Spec_map_mk_comp_specPiecewise_left_assoc, Over.w a]
      dsimp
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    · rw [Spec_map_mk_comp_specPiecewise_right_assoc, Over.w b]
      dsimp
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp])

/-- A point of `Spec S` on the piece `Spec (S ⧸ I)` sees `a`. -/
theorem specOverFieldMap_comp_overPiecewise_left {L : Type u} [CommRing L] [Algebra K L]
    (ψ : S →ₐ[K] L) (hψ : ∀ s ∈ I, ψ s = 0) (a : specOverField k K (S ⧸ I) ⟶ Z)
    (b : specOverField k K (S ⧸ J) ⟶ Z) :
    specOverFieldMap ψ ≫ overPiecewise hIJ hIJ0 a b =
      specOverFieldMap (Ideal.Quotient.liftₐ I ψ hψ) ≫ a := by
  ext1
  exact Spec_map_comp_specPiecewise_left hIJ hIJ0 ψ.toRingHom hψ a.left b.left

/-- A point of `Spec S` on the piece `Spec (S ⧸ J)` sees `b`. -/
theorem specOverFieldMap_comp_overPiecewise_right {L : Type u} [CommRing L] [Algebra K L]
    (ψ : S →ₐ[K] L) (hψ : ∀ s ∈ J, ψ s = 0) (a : specOverField k K (S ⧸ I) ⟶ Z)
    (b : specOverField k K (S ⧸ J) ⟶ Z) :
    specOverFieldMap ψ ≫ overPiecewise hIJ hIJ0 a b =
      specOverFieldMap (Ideal.Quotient.liftₐ J ψ hψ) ≫ b := by
  ext1
  exact Spec_map_comp_specPiecewise_right hIJ hIJ0 ψ.toRingHom hψ a.left b.left

include hIJ hIJ0 in
/-- Two morphisms over `Spec k` out of `Spec S` agree as soon as they agree on the two pieces. -/
theorem overPiecewise_ext {f g : specOverField k K S ⟶ Z}
    (h₀ : specOverFieldMap (Ideal.Quotient.mkₐ K I) ≫ f =
      specOverFieldMap (Ideal.Quotient.mkₐ K I) ≫ g)
    (h₁ : specOverFieldMap (Ideal.Quotient.mkₐ K J) ≫ f =
      specOverFieldMap (Ideal.Quotient.mkₐ K J) ≫ g) : f = g := by
  ext1
  exact specPiecewise_ext hIJ hIJ0 (congrArg Over.Hom.left h₀) (congrArg Over.Hom.left h₁)

end OverPiecewise

end AlgebraicGeometry

namespace Deformation.Artin

open AlgebraicGeometry

/-! ### The thickened triangle and its two-open cover -/

section TriangleCover

variable (K : Type u) [CommRing K] (n : ℕ)

/-- The coordinate ring `R_n = K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)` of the `n`-th thickening of
the triangle. -/
abbrev triangleLevel : Type u := MvPolynomial (Fin 2) K ⧸ triangleIdeal K ^ (n + 1)

/-- The coordinate `x` on the thickened triangle. -/
def triangleX : triangleLevel K n := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The coordinate `y` on the thickened triangle. -/
def triangleY : triangleLevel K n := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The triangle polynomial is `xy(x + y - 1)` in the coordinates. -/
theorem mk_trianglePolynomial :
    Ideal.Quotient.mk (triangleIdeal K ^ (n + 1)) (trianglePolynomial K) =
      triangleX K n * triangleY K n * (triangleX K n + triangleY K n - 1) := by
  simp [trianglePolynomial, triangleX, triangleY]

/-- The `(n + 1)`-st power of the triangle polynomial vanishes on the `n`-th thickening. -/
theorem triangle_pow_eq_zero :
    (triangleX K n * triangleY K n * (triangleX K n + triangleY K n - 1)) ^ (n + 1) = 0 := by
  rw [← mk_trianglePolynomial, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (trianglePolynomial K)) _

/-- **The two opens `D(1 - x)` and `D(1 - y)` cover the thickened triangle.** The common zero
`(1, 1)` of `1 - x` and `1 - y` is not on the triangle. -/
theorem isCoprime_one_sub_triangleX_one_sub_triangleY :
    IsCoprime (1 - triangleX K n) (1 - triangleY K n) := by
  set x := triangleX K n
  set y := triangleY K n
  have hnil : IsNilpotent (x * y * (x + y - 1)) := ⟨n + 1, triangle_pow_eq_zero K n⟩
  obtain ⟨v, hv⟩ := hnil.isUnit_one_sub.exists_left_inv
  refine ⟨v * (2 - (1 - x) - 3 * (1 - y) + (1 - x) * (1 - y)),
    v * (2 - (1 - y) + (1 - x) * (1 - y)), ?_⟩
  linear_combination hv

variable {K n}

/-- The `K`-algebra map out of `R_n` sending `x ↦ u` and `y ↦ v`, for a solution of
`uv(u + v - 1) = 0`. -/
def triangleLevelLift {T : Type u} [CommRing T] [Algebra K T] (u v : T)
    (h : u * v * (u + v - 1) = 0) : triangleLevel K n →ₐ[K] T :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![u, v]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (Ideal.pow_le_self (Nat.succ_ne_zero n) ha)
    simp [trianglePolynomial, h])

@[simp]
theorem triangleLevelLift_triangleX {T : Type u} [CommRing T] [Algebra K T] (u v : T)
    (h : u * v * (u + v - 1) = 0) : triangleLevelLift (n := n) u v h (triangleX K n) = u := by
  change MvPolynomial.aeval ![u, v] (MvPolynomial.X 0) = u
  simp

@[simp]
theorem triangleLevelLift_triangleY {T : Type u} [CommRing T] [Algebra K T] (u v : T)
    (h : u * v * (u + v - 1) = 0) : triangleLevelLift (n := n) u v h (triangleY K n) = v := by
  change MvPolynomial.aeval ![u, v] (MvPolynomial.X 1) = v
  simp

/-- Two `K`-algebra maps out of `R_n` agreeing on the coordinates agree. -/
theorem triangleLevel_algHom_ext {T : Type u} [CommRing T] [Algebra K T]
    {f g : triangleLevel K n →ₐ[K] T} (hx : f (triangleX K n) = g (triangleX K n))
    (hy : f (triangleY K n) = g (triangleY K n)) : f = g := by
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i => ?_)
  fin_cases i
  · exact hx
  · exact hy

/-- The `K`-algebra map out of a localization `R_n[1/g]` sending `x ↦ u` and `y ↦ v`, for a
solution of `uv(u + v - 1) = 0` at which `g` is a unit. -/
def triangleAwayLift {T : Type u} [CommRing T] [Algebra K T] (g : triangleLevel K n) (u v : T)
    (h : u * v * (u + v - 1) = 0) (hg : IsUnit (triangleLevelLift u v h g)) :
    Localization.Away g →ₐ[K] T :=
  IsLocalization.Away.liftAlgHom g (f := triangleLevelLift u v h) hg

@[simp]
theorem triangleAwayLift_algebraMap {T : Type u} [CommRing T] [Algebra K T]
    (g : triangleLevel K n) (u v : T) (h : u * v * (u + v - 1) = 0)
    (hg : IsUnit (triangleLevelLift u v h g)) (r : triangleLevel K n) :
    triangleAwayLift g u v h hg (algebraMap _ _ r) = triangleLevelLift u v h r :=
  IsLocalization.Away.lift_eq g hg r

variable (K n)

/-- The coordinate ring of the overlap `U ∩ W = D((1 - x)(1 - y))` of the two opens. -/
abbrev triangleOverlap : Type u :=
  Localization.Away ((1 - triangleX K n) * (1 - triangleY K n))

/-- The ideal of the piece of `U ∩ W` on the two lines `x = 0` and `y = 0`. -/
def triangleOverlapRestIdeal : Ideal (triangleOverlap K n) :=
  Ideal.span {algebraMap _ _ (triangleX K n * triangleY K n) ^ (n + 1)}

/-- The ideal of the piece of `U ∩ W` on the line `x + y = 1`, the open edge. -/
def triangleOverlapEdgeIdeal : Ideal (triangleOverlap K n) :=
  Ideal.span {algebraMap _ _ (triangleX K n + triangleY K n - 1) ^ (n + 1)}

/-- On `U ∩ W` the elements `xy` and `x + y - 1` are coprime: their difference is
`(1 - x)(1 - y)`, a unit there. -/
theorem isCoprime_triangleOverlap :
    IsCoprime (algebraMap _ (triangleOverlap K n) (triangleX K n * triangleY K n))
      (algebraMap _ (triangleOverlap K n) (triangleX K n + triangleY K n - 1)) := by
  obtain ⟨w, hw⟩ := (IsLocalization.Away.algebraMap_isUnit (S := triangleOverlap K n)
    ((1 - triangleX K n) * (1 - triangleY K n))).exists_left_inv
  have hsub : algebraMap _ (triangleOverlap K n) (triangleX K n * triangleY K n) -
      algebraMap _ (triangleOverlap K n) (triangleX K n + triangleY K n - 1) =
        algebraMap _ (triangleOverlap K n) ((1 - triangleX K n) * (1 - triangleY K n)) := by
    rw [← map_sub]
    congr 1
    ring
  exact ⟨w, -w, by linear_combination hw + w * hsub⟩

/-- **The two pieces of `U ∩ W` are complementary**, part one: their ideals are coprime. -/
theorem isCoprime_triangleOverlapRestIdeal_triangleOverlapEdgeIdeal :
    IsCoprime (triangleOverlapRestIdeal K n) (triangleOverlapEdgeIdeal K n) := by
  rw [triangleOverlapRestIdeal, triangleOverlapEdgeIdeal, Ideal.isCoprime_span_singleton_iff]
  exact (isCoprime_triangleOverlap K n).pow

/-- **The two pieces of `U ∩ W` are complementary**, part two: their ideals meet in zero. -/
theorem triangleOverlapRestIdeal_inf_triangleOverlapEdgeIdeal :
    triangleOverlapRestIdeal K n ⊓ triangleOverlapEdgeIdeal K n = ⊥ := by
  rw [← Ideal.mul_eq_inf_of_isCoprime
    (isCoprime_triangleOverlapRestIdeal_triangleOverlapEdgeIdeal K n), triangleOverlapRestIdeal,
    triangleOverlapEdgeIdeal, Ideal.span_singleton_mul_span_singleton, ← mul_pow, ← map_mul,
    ← map_pow, triangle_pow_eq_zero, map_zero, Ideal.span_singleton_eq_bot]

end TriangleCover

/-! ### The two opens and the glueing cocycle -/

section Cocycle

variable (K : Type u) [CommRing K] (n : ℕ)

/-- The coordinate ring of the open `U = D(1 - x)`, the complement of the vertex `(1, 0)`. -/
abbrev triangleLeft : Type u := Localization.Away (1 - triangleX K n)

/-- The coordinate ring of the open `W = D(1 - y)`, the complement of the vertex `(0, 1)`. -/
abbrev triangleRight : Type u := Localization.Away (1 - triangleY K n)

/-- The restriction from `U` to `U ∩ W`. -/
def triangleLeftToOverlap : triangleLeft K n →ₐ[K] triangleOverlap K n :=
  IsLocalization.Away.liftAlgHom (1 - triangleX K n)
    (f := IsScalarTower.toAlgHom K (triangleLevel K n) (triangleOverlap K n))
    (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right (1 - triangleX K n) (1 - triangleY K n)))

/-- The restriction from `W` to `U ∩ W`. -/
def triangleRightToOverlap : triangleRight K n →ₐ[K] triangleOverlap K n :=
  IsLocalization.Away.liftAlgHom (1 - triangleY K n)
    (f := IsScalarTower.toAlgHom K (triangleLevel K n) (triangleOverlap K n))
    (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_left (1 - triangleY K n) (1 - triangleX K n)))

@[simp]
theorem triangleLeftToOverlap_algebraMap (r : triangleLevel K n) :
    triangleLeftToOverlap K n (algebraMap _ _ r) = algebraMap _ _ r :=
  IsLocalization.Away.lift_eq _
    (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_right (1 - triangleX K n) (1 - triangleY K n))) r

@[simp]
theorem triangleRightToOverlap_algebraMap (r : triangleLevel K n) :
    triangleRightToOverlap K n (algebraMap _ _ r) = algebraMap _ _ r :=
  IsLocalization.Away.lift_eq _
    (IsLocalization.Away.isUnit_of_dvd _ (dvd_mul_left (1 - triangleY K n) (1 - triangleX K n))) r

variable {K n}

/-- Two `K`-algebra maps out of a localization of `R_n` agreeing on the coordinates agree. -/
theorem triangleLevel_away_algHom_ext {g : triangleLevel K n} {T : Type u} [CommRing T]
    [Algebra K T] {f₁ f₂ : Localization.Away g →ₐ[K] T}
    (hx : f₁ (algebraMap _ _ (triangleX K n)) = f₂ (algebraMap _ _ (triangleX K n)))
    (hy : f₁ (algebraMap _ _ (triangleY K n)) = f₂ (algebraMap _ _ (triangleY K n))) :
    f₁ = f₂ := by
  have h := triangleLevel_algHom_ext
    (f := f₁.comp (IsScalarTower.toAlgHom K (triangleLevel K n) (Localization.Away g)))
    (g := f₂.comp (IsScalarTower.toAlgHom K (triangleLevel K n) (Localization.Away g))) hx hy
  refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers g) ?_)
  exact RingHom.ext fun r => AlgHom.congr_fun h r

variable {k : Type u} [CommRing k] [Algebra k K] (A : Over (Spec (.of k))) [GrpObj A]

variable (K n) in
/-- **The glueing cocycle.** For a `K`-point `pt` of a group scheme `A` over `Spec k`, the
morphism `U ∩ W ⟶ A` over `Spec k` which is the constant `pt` on the open edge `x + y = 1` and the
unit on the other piece of `U ∩ W`. -/
def triangleCocycle (pt : specOverField k K K ⟶ A) : specOverField k K (triangleOverlap K n) ⟶ A :=
  overPiecewise (isCoprime_triangleOverlapRestIdeal_triangleOverlapEdgeIdeal K n)
    (triangleOverlapRestIdeal_inf_triangleOverlapEdgeIdeal K n) 1
    (specOverFieldMap (Algebra.ofId K _) ≫ pt)

/-- A `K`-point of `U ∩ W` on the piece of the two lines `x = 0`, `y = 0` sees the unit. -/
theorem specOverFieldMap_comp_triangleCocycle_of_rest (pt : specOverField k K K ⟶ A)
    (ψ : triangleOverlap K n →ₐ[K] K)
    (hψ : ψ (algebraMap _ _ (triangleX K n * triangleY K n)) = 0) :
    specOverFieldMap ψ ≫ triangleCocycle K n A pt = 1 := by
  have hI : ∀ s ∈ triangleOverlapRestIdeal K n, ψ s = 0 := by
    intro s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [map_mul, map_pow, hψ, zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [triangleCocycle, specOverFieldMap_comp_overPiecewise_left _ _ ψ hI, MonObj.comp_one]

/-- A `K`-point of `U ∩ W` on the open edge `x + y = 1` sees `pt`. -/
theorem specOverFieldMap_comp_triangleCocycle_of_edge (pt : specOverField k K K ⟶ A)
    (ψ : triangleOverlap K n →ₐ[K] K)
    (hψ : ψ (algebraMap _ _ (triangleX K n + triangleY K n - 1)) = 0) :
    specOverFieldMap ψ ≫ triangleCocycle K n A pt = pt := by
  have hJ : ∀ s ∈ triangleOverlapEdgeIdeal K n, ψ s = 0 := by
    intro s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [map_mul, map_pow, hψ, zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [triangleCocycle, specOverFieldMap_comp_overPiecewise_right _ _ ψ hJ,
    ← Category.assoc, specOverFieldMap_comp,
    Subsingleton.elim ((Ideal.Quotient.liftₐ _ ψ hJ).comp (Algebra.ofId K _)) (AlgHom.id K K),
    specOverFieldMap_id, Category.id_comp]

end Cocycle

/-! ### Compatibility of the cocycle with the transition maps -/

section Transition

variable (K : Type u) [CommRing K] (n : ℕ)

/-- The transition map `R_{n+1} ⟶ R_n` of the thickenings. -/
def triangleTransition : triangleLevel K (n + 1) →ₐ[K] triangleLevel K n :=
  Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

@[simp]
theorem triangleTransition_triangleX :
    triangleTransition K n (triangleX K (n + 1)) = triangleX K n :=
  rfl

@[simp]
theorem triangleTransition_triangleY :
    triangleTransition K n (triangleY K (n + 1)) = triangleY K n :=
  rfl

/-- The unit `(1 - x)(1 - y)` of `U ∩ W` at level `n + 1` stays a unit at level `n`. -/
theorem isUnit_triangleTransition_one_sub_mul :
    IsUnit (((IsScalarTower.toAlgHom K (triangleLevel K n) (triangleOverlap K n)).comp
      (triangleTransition K n)).toRingHom
        ((1 - triangleX K (n + 1)) * (1 - triangleY K (n + 1)))) := by
  have h : triangleTransition K n ((1 - triangleX K (n + 1)) * (1 - triangleY K (n + 1))) =
      (1 - triangleX K n) * (1 - triangleY K n) := by
    rw [map_mul, map_sub, map_sub, map_one, triangleTransition_triangleX,
      triangleTransition_triangleY]
  change IsUnit (algebraMap _ (triangleOverlap K n) (triangleTransition K n _))
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The transition map on the coordinate rings of `U ∩ W`. -/
def triangleOverlapTransition : triangleOverlap K (n + 1) →ₐ[K] triangleOverlap K n :=
  IsLocalization.Away.liftAlgHom ((1 - triangleX K (n + 1)) * (1 - triangleY K (n + 1)))
    (isUnit_triangleTransition_one_sub_mul K n)

@[simp]
theorem triangleOverlapTransition_algebraMap (r : triangleLevel K (n + 1)) :
    triangleOverlapTransition K n (algebraMap _ _ r) = algebraMap _ _ (triangleTransition K n r) :=
  IsLocalization.Away.lift_eq _ (isUnit_triangleTransition_one_sub_mul K n) r

variable {K n} {k : Type u} [CommRing k] [Algebra k K] (A : Over (Spec (.of k))) [GrpObj A]

/-- **The glueing cocycle is compatible with the transition maps**: restricted from `X_{n+1}` to
`X_n`, the cocycle of level `n + 1` is the cocycle of level `n`. -/
theorem specOverFieldMap_triangleOverlapTransition_comp_triangleCocycle
    (pt : specOverField k K K ⟶ A) :
    specOverFieldMap (triangleOverlapTransition K n) ≫ triangleCocycle K (n + 1) A pt =
      triangleCocycle K n A pt := by
  have hgen : ∀ (r : triangleLevel K (n + 1)) (I : Ideal (triangleOverlap K n)),
      algebraMap _ (triangleOverlap K n) (triangleTransition K n r) ^ (n + 1) ∈ I →
      ∀ s ∈ Ideal.span {algebraMap _ (triangleOverlap K (n + 1)) r ^ (n + 1 + 1)},
        ((Ideal.Quotient.mkₐ K I).comp (triangleOverlapTransition K n)) s = 0 := by
    intro r I hr s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    have h : triangleOverlapTransition K n (c * algebraMap _ _ r ^ (n + 1 + 1)) =
        triangleOverlapTransition K n c *
          (algebraMap _ (triangleOverlap K n) (triangleTransition K n r) ^ (n + 1) *
            algebraMap _ (triangleOverlap K n) (triangleTransition K n r)) := by
      rw [map_mul, map_pow, triangleOverlapTransition_algebraMap,
        pow_succ (algebraMap _ (triangleOverlap K n) (triangleTransition K n r)) (n + 1)]
    rw [AlgHom.comp_apply, h, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_left _ (I.mul_mem_right _ hr)
  have hI : ∀ s ∈ triangleOverlapRestIdeal K (n + 1),
      ((Ideal.Quotient.mkₐ K (triangleOverlapRestIdeal K n)).comp
        (triangleOverlapTransition K n)) s = 0 :=
    hgen _ _ (by
      rw [map_mul, triangleTransition_triangleX, triangleTransition_triangleY]
      exact Ideal.mem_span_singleton_self _)
  have hJ : ∀ s ∈ triangleOverlapEdgeIdeal K (n + 1),
      ((Ideal.Quotient.mkₐ K (triangleOverlapEdgeIdeal K n)).comp
        (triangleOverlapTransition K n)) s = 0 :=
    hgen _ _ (by
      rw [map_sub, map_add, map_one, triangleTransition_triangleX, triangleTransition_triangleY]
      exact Ideal.mem_span_singleton_self _)
  have hI' : ∀ s ∈ triangleOverlapRestIdeal K n,
      Ideal.Quotient.mkₐ K (triangleOverlapRestIdeal K n) s = 0 :=
    fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr hs
  have hJ' : ∀ s ∈ triangleOverlapEdgeIdeal K n,
      Ideal.Quotient.mkₐ K (triangleOverlapEdgeIdeal K n) s = 0 :=
    fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr hs
  refine overPiecewise_ext (isCoprime_triangleOverlapRestIdeal_triangleOverlapEdgeIdeal K n)
    (triangleOverlapRestIdeal_inf_triangleOverlapEdgeIdeal K n) ?_ ?_
  · rw [← Category.assoc, specOverFieldMap_comp, triangleCocycle, triangleCocycle,
      specOverFieldMap_comp_overPiecewise_left _ _ _ hI,
      specOverFieldMap_comp_overPiecewise_left _ _ _ hI', MonObj.comp_one, MonObj.comp_one]
  · rw [← Category.assoc, specOverFieldMap_comp, triangleCocycle, triangleCocycle,
      specOverFieldMap_comp_overPiecewise_right _ _ _ hJ,
      specOverFieldMap_comp_overPiecewise_right _ _ _ hJ', ← Category.assoc,
      specOverFieldMap_comp, ← Category.assoc, specOverFieldMap_comp,
      Subsingleton.elim ((Ideal.Quotient.liftₐ _ _ hJ).comp (Algebra.ofId K _))
        ((Ideal.Quotient.liftₐ _ _ hJ').comp (Algebra.ofId K _))]

end Transition

end Deformation.Artin

end
