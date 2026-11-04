module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraOverHomEquiv

/-!
# The canonical morphism into an algebraic space affine over `X` with given direct image

Let `Z` be an algebraic space affine over an algebraic space `X`, and let `Y` be an *arbitrary*
algebraic space over `X`.  The direct image `g ↦ g_*` is a bijection from the morphisms `Y ⟶ Z`
over `X` onto the morphisms `Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` of `𝒪_X`-algebras: this is
`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraOverHomEquiv`.  At
`Z = \underline{Spec}_X(𝒜)` it is the universal property
`Hom_X(Y, \underline{Spec}_X(𝒜)) = Hom_{𝒪_X}(𝒜, f_* 𝒪_Y)` of the relative spectrum, which is
what makes the factorization of Stacks 081X canonical.  This file records the consequences of
that bijection which the factorization uses.

## Main results

* `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom_symm_comp`: naturality of the
  bijection in the source.
* `AlgebraicGeometry.Space.overHomOfPushforwardAlgebraIso`: the canonical morphism `Y ⟶ P` over
  `X` attached to an identification `P_* 𝒪_P ≅ Y_* 𝒪_Y`, for `P` affine over `X`; its
  direct-image map is an isomorphism
  (`AlgebraicGeometry.Space.isIso_pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso`,
  `AlgebraicGeometry.Space.isIso_pushforwardRingMap_overHomOfPushforwardAlgebraIso`), and it is
  the only morphism over `X` with direct-image map that identification.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

variable {Y : Over X}

/-! ### Consequences of the universal property -/

/-- The morphism over `X` attached to an algebra map has that map for its direct image. -/
@[simp]
theorem pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm (Y : Over X)
    (Z : AffineOver B S hS X)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y) :
    pushforwardAlgebraMap B S hS ((overHomEquivPushforwardAlgebraHom B S hS Y Z).symm φ) = φ :=
  (overHomEquivPushforwardAlgebraHom B S hS Y Z).apply_symm_apply φ

/-- Naturality of the universal property in the source: precomposing with a morphism `k : Y' ⟶ Y`
over `X` corresponds to postcomposing with its direct-image map. -/
theorem overHomEquivPushforwardAlgebraHom_symm_comp {Y' : Over X} (k : Y' ⟶ Y)
    (Z : AffineOver B S hS X)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y) :
    k ≫ (overHomEquivPushforwardAlgebraHom B S hS Y Z).symm φ =
      (overHomEquivPushforwardAlgebraHom B S hS Y' Z).symm
        (φ ≫ pushforwardAlgebraMap B S hS k) := by
  refine eq_of_pushforwardAlgebraMap_eq B S hS Z ?_
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm,
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm]

/-! ### The canonical morphism into an algebraic space affine over `X` with given direct image -/

/-- **The canonical morphism `Y ⟶ P` over `X` attached to an identification `P_* 𝒪_P ≅ Y_* 𝒪_Y`
of `𝒪_X`-algebras.**  It is the unique morphism over `X` whose direct-image map is the given
isomorphism, by `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`.  At
`P = \underline{Spec}_X(f_* 𝒪_Y)` with its identification of direct images this is the canonical
morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of Stacks 081X. -/
def overHomOfPushforwardAlgebraIso {P : AffineOver B S hS X}
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS Y) : Y ⟶ P.obj :=
  (overHomEquivPushforwardAlgebraHom B S hS Y P).symm e.hom

/-- The direct-image map of the canonical morphism is the given identification. -/
@[simp]
theorem pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso {P : AffineOver B S hS X}
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS Y) :
    pushforwardAlgebraMap B S hS (overHomOfPushforwardAlgebraIso B S hS e) = e.hom :=
  pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B S hS Y P e.hom

/-- **The canonical morphism induces an isomorphism of direct-image algebras.** -/
instance isIso_pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso {P : AffineOver B S hS X}
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS Y) :
    IsIso (pushforwardAlgebraMap B S hS (overHomOfPushforwardAlgebraIso B S hS e)) := by
  rw [pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso]
  infer_instance

/-- **The canonical morphism induces an isomorphism `P_* 𝒪_P ⟶ Y_* 𝒪_Y` of sheaves of rings.** -/
instance isIso_pushforwardRingMap_overHomOfPushforwardAlgebraIso {P : AffineOver B S hS X}
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS Y) :
    IsIso (pushforwardRingMap B S hS (overHomOfPushforwardAlgebraIso B S hS e)) :=
  (inferInstance : IsIso (AlgebraSheaf.forget.map
    (pushforwardAlgebraMap B S hS (overHomOfPushforwardAlgebraIso B S hS e))))

/-- **Uniqueness of the canonical morphism**: a morphism over `X` is the canonical morphism of
`e` exactly when its direct-image map is `e`. -/
theorem eq_overHomOfPushforwardAlgebraIso_iff {P : AffineOver B S hS X}
    (e : pushforwardAlgebra B S hS P.obj ≅ pushforwardAlgebra B S hS Y) (g : Y ⟶ P.obj) :
    g = overHomOfPushforwardAlgebraIso B S hS e ↔ pushforwardAlgebraMap B S hS g = e.hom := by
  refine ⟨fun h => h ▸ pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso B S hS e,
    fun h => eq_of_pushforwardAlgebraMap_eq B S hS P ?_⟩
  rw [h, pushforwardAlgebraMap_overHomOfPushforwardAlgebraIso]

/-- Every morphism over `X` into an algebraic space affine over `X` whose direct-image map is an
isomorphism is the canonical morphism of that isomorphism. -/
theorem eq_overHomOfPushforwardAlgebraIso_of_isIso {P : AffineOver B S hS X} (g : Y ⟶ P.obj)
    [IsIso (pushforwardAlgebraMap B S hS g)] :
    g = overHomOfPushforwardAlgebraIso B S hS (asIso (pushforwardAlgebraMap B S hS g)) :=
  (eq_overHomOfPushforwardAlgebraIso_iff B S hS _ g).2 rfl

end AlgebraicGeometry.Space

end
