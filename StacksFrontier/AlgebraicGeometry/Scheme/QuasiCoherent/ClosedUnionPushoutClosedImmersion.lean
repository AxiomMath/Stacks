module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout

/-!
# The scheme-theoretic union of two closed subschemes, presented by closed immersions

[Stacks Project, Tag 0C4J] says that the scheme-theoretic union of two closed subschemes is the
pushout of the two of them along their scheme-theoretic intersection.  In
`AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf` it is stated for the canonical
closed subschemes `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` cut out by two sheaves of
ideals.  A consumer
who has the four closed subschemes as abstract closed immersions into the ambient scheme, rather
than in that canonical shape, needs the same statement for those; this file supplies it.

The translation is a single observation: a closed immersion is determined up to a unique
isomorphism over its target by its sheaf of ideals, so a closed immersion `j` with
`j.ker = K` is canonically isomorphic over the target to `K.subschemeι`
(`AlgebraicGeometry.kerIsoSubscheme`).  Four such isomorphisms carry the canonical square of
Tag 0C4J onto the given one, and `CategoryTheory.IsPushout.of_iso` transports the pushout
property along them.  Each of the four compatibilities is checked after composing with a closed
immersion into the ambient scheme, which is a monomorphism.

## Main definitions

* `AlgebraicGeometry.kerIsoSubscheme`: the isomorphism over the target between the source of a
  closed immersion and the closed subscheme cut out by its sheaf of ideals.

## Main results

* `AlgebraicGeometry.isPushout_of_ker_eq_inf`: **Tag 0C4J for closed immersions.**  Given four
  closed immersions into a scheme whose sheaves of ideals are `I`, `J`, `I ⊔ J` and `I ⊓ J`, and
  the four morphisms between their sources over the ambient scheme, the resulting square is a
  pushout square of schemes.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The source of a closed immersion is canonically isomorphic, over the target, to the closed
subscheme cut out by its sheaf of ideals.**

The isomorphism is the universal property of the closed immersion `K.subschemeι` applied to `j`,
which is an isomorphism because the two have the same sheaf of ideals,
`AlgebraicGeometry.IsClosedImmersion.isIso_lift`. -/
noncomputable def kerIsoSubscheme {R V : Scheme.{u}} (j : R ⟶ V) [IsClosedImmersion j]
    (K : V.IdealSheafData) (h : j.ker = K) : R ≅ K.subscheme :=
  haveI hle : K.subschemeι.ker = j.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  haveI : IsIso (IsClosedImmersion.lift K.subschemeι j hle.le) :=
    IsClosedImmersion.isIso_lift _ _ hle
  asIso (IsClosedImmersion.lift K.subschemeι j hle.le)

/-- `AlgebraicGeometry.kerIsoSubscheme` is an isomorphism over the ambient scheme. -/
@[reassoc (attr := simp)]
theorem kerIsoSubscheme_hom_subschemeι {R V : Scheme.{u}} (j : R ⟶ V) [IsClosedImmersion j]
    (K : V.IdealSheafData) (h : j.ker = K) :
    (kerIsoSubscheme j K h).hom ≫ K.subschemeι = j :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse of `AlgebraicGeometry.kerIsoSubscheme` carries the given closed immersion to the
inclusion of the closed subscheme cut out by its sheaf of ideals. -/
@[reassoc (attr := simp)]
theorem kerIsoSubscheme_inv_comp {R V : Scheme.{u}} (j : R ⟶ V) [IsClosedImmersion j]
    (K : V.IdealSheafData) (h : j.ker = K) :
    (kerIsoSubscheme j K h).inv ≫ j = K.subschemeι :=
  (Iso.inv_comp_eq _).2 (kerIsoSubscheme_hom_subschemeι j K h).symm

/-- **[Stacks, Tag 0C4J] for closed immersions.** Let `j₁, j₂, j₃, j₄` be closed immersions into
a scheme `V`, with sheaves of ideals `I`, `J`, `I ⊔ J` and `I ⊓ J`, and let `a₁, a₂, b₁, b₂` be
morphisms of their sources over `V` forming the evident span and cocone.  Then the square
is a pushout square of schemes: the closed subscheme cut out by `I ⊓ J` is the scheme-theoretic
union of those cut out by `I` and by `J`, as a pushout along their scheme-theoretic
intersection.

This is `AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf` transported along the
four isomorphisms `AlgebraicGeometry.kerIsoSubscheme`. -/
theorem isPushout_of_ker_eq_inf {V R₁ R₂ R₃ R₄ : Scheme.{u}}
    (j₁ : R₁ ⟶ V) (j₂ : R₂ ⟶ V) (j₃ : R₃ ⟶ V) (j₄ : R₄ ⟶ V)
    [IsClosedImmersion j₁] [IsClosedImmersion j₂] [IsClosedImmersion j₃] [IsClosedImmersion j₄]
    (a₁ : R₃ ⟶ R₁) (a₂ : R₃ ⟶ R₂) (b₁ : R₁ ⟶ R₄) (b₂ : R₂ ⟶ R₄)
    (ha₁ : a₁ ≫ j₁ = j₃) (ha₂ : a₂ ≫ j₂ = j₃) (hb₁ : b₁ ≫ j₄ = j₁) (hb₂ : b₂ ≫ j₄ = j₂)
    (h₃ : j₃.ker = j₁.ker ⊔ j₂.ker) (h₄ : j₄.ker = j₁.ker ⊓ j₂.ker) :
    IsPushout a₁ a₂ b₁ b₂ := by
  refine (Scheme.IdealSheafData.isPushout_subscheme_inf j₁.ker j₂.ker).of_iso
    (kerIsoSubscheme j₃ (j₁.ker ⊔ j₂.ker) h₃).symm
    (kerIsoSubscheme j₁ j₁.ker rfl).symm
    (kerIsoSubscheme j₂ j₂.ker rfl).symm
    (kerIsoSubscheme j₄ (j₁.ker ⊓ j₂.ker) h₄).symm
    ((cancel_mono j₁).1 ?_) ((cancel_mono j₂).1 ?_)
    ((cancel_mono j₄).1 ?_) ((cancel_mono j₄).1 ?_)
  all_goals simp [ha₁, ha₂, hb₁, hb₂]

end AlgebraicGeometry

end
