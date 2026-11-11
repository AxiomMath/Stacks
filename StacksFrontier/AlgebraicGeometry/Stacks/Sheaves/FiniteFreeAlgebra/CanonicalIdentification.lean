module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Scheme

/-!
# The canonical identification of points of the scheme of structure constants

Let `d` be positive, let `R_univ = ℤ[a_{ij}^k]/J` be the universal ring of structure constants
and `X = Spec(R_univ)`. The free `d`-dimensional algebra `m_univ` over `R_univ` has as structure
constants the classes of the variables `a_{ij}^k`. **Stacks 05YM** identifies `X(T)` with the free
`d`-dimensional algebras over `Γ(T, 𝒪_T)`, for every scheme `T`, by sending a point `x` to the
extension of `m_univ` along the ring map `R_univ → Γ(T, 𝒪_T)` that `x` induces.

This file states that identification in this form: every free `d`-dimensional algebra over
`Γ(T, 𝒪_T)` is the extension of `m_univ` along exactly one point, and the identification commutes
with pullback along morphisms of schemes.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.universalRingStructure`: the free `d`-dimensional algebra
  `m_univ` over the universal ring.
* `AlgebraicGeometry.FiniteFreeAlgebra.classifyingRingHom`: the ring map from the universal ring
  to the global sections of `T` induced by a point `x : T ⟶ X`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.map_classifyingRingHom_universalRingStructure`: the
  identification `AlgebraicGeometry.FiniteFreeAlgebra.representation` sends a point to the
  extension of `m_univ` along its classifying ring map.
* `AlgebraicGeometry.FiniteFreeAlgebra.existsUnique_map_universalRingStructure`: for every scheme
  `T`, every free `d`-dimensional algebra over `Γ(T, 𝒪_T)` is the extension of `m_univ` along
  exactly one point of `X` over `T`, and this identification is natural in `T`.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

noncomputable section

variable (d : ℕ) [NeZero d]

/-- The free `d`-dimensional algebra `m_univ` over the universal ring, whose structure constants
are the classes of the variables `a i j k`. -/
def universalRingStructure : FiniteFreeAlgebra (universalRing d) d where
  coeff i j k := Ideal.Quotient.mk _ (universalCoeff d i j k)
  assoc i j k n := by
    refine sub_eq_zero.mp ?_
    simp only [← map_mul, ← map_sum, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inl (Or.inl ⟨i, j, k, n, rfl⟩)))
  comm i j k := by
    refine sub_eq_zero.mp ?_
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inl (Or.inr ⟨i, j, k, rfl⟩)))
  unit_coeff i j := by
    refine sub_eq_zero.mp ?_
    have h : Ideal.Quotient.mk (Ideal.span (universalRelations d))
        (universalCoeff d i 0 j - MvPolynomial.C (if i = j then 1 else 0)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨i, j, rfl⟩))
    rw [map_sub] at h
    split_ifs at h ⊢ <;> simpa using h

variable {d}

/-- The ring map `R_univ → Γ(T, 𝒪_T)` induced by a point `x : T ⟶ X` of the scheme of structure
constants. -/
def classifyingRingHom {T : Scheme.{u}} (x : T ⟶ scheme.{u} d) :
    universalRing d →+* Γ(T, ⊤) :=
  x.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (universalRing d)))).inv.hom.comp
      ULift.ringEquiv.symm.toRingHom)

/-- The identification `representation` sends a point `x` to the extension of `m_univ` along the
ring map that `x` induces on global sections. -/
theorem map_classifyingRingHom_universalRingStructure {T : Scheme.{u}}
    (x : T ⟶ scheme.{u} d) :
    map (classifyingRingHom x) (universalRingStructure d) = (representation.{u} d).equiv T x :=
  rfl

/-- **Stacks 05YM.** For every scheme `T`, every free `d`-dimensional algebra over `Γ(T, 𝒪_T)`
is the extension of the universal algebra `m_univ` along the ring map induced by exactly one
morphism `T ⟶ X = Spec(R_univ)`; and the resulting identification of `X(T)` with free
`d`-dimensional algebras over `Γ(T, 𝒪_T)` commutes with pullback along every morphism of
schemes. -/
@[stacks 05YM "for every scheme `T`, the point `x : T ⟶ Spec(R_univ)` corresponds to the \
extension of the universal algebra along the ring map `R_univ → Γ(T, 𝒪_T)` induced by `x`; \
this is a bijection, natural in `T`"]
theorem existsUnique_map_universalRingStructure :
    (∀ (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d),
      ∃! x : T ⟶ scheme.{u} d, map (classifyingRingHom x) (universalRingStructure d) = m) ∧
    ∀ {T U : Scheme.{u}} (f : T ⟶ U) (x : U ⟶ scheme.{u} d),
      map f.appTop.hom (map (classifyingRingHom x) (universalRingStructure d)) =
        map (classifyingRingHom (f ≫ x)) (universalRingStructure d) := by
  refine ⟨fun T m => ?_, fun f x => ?_⟩
  · refine ⟨((representation.{u} d).equiv T).symm m, ?_, fun y hy => ?_⟩
    · dsimp only
      rw [map_classifyingRingHom_universalRingStructure, Equiv.apply_symm_apply]
    · dsimp only at hy
      rw [map_classifyingRingHom_universalRingStructure] at hy
      rw [← hy, Equiv.symm_apply_apply]
  · rw [map_classifyingRingHom_universalRingStructure,
      map_classifyingRingHom_universalRingStructure]
    exact (representation.{u} d).naturality f x

end

end AlgebraicGeometry.FiniteFreeAlgebra

end
