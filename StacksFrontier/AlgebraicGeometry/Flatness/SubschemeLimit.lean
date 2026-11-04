module

public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFiltered

/-!
# A closed subscheme is the limit of its finite-presentation enlargements

Fix a scheme `X` and quasi-coherent ideal sheaf data `K` on it. The finite-presentation closed
subschemes of `X` containing the closed subscheme cut out by `K` form an inverse system
`Stacks.Flatness.subschemeDiagram K` over `X`, and the closed subscheme cut out by `K` is the
vertex of a canonical cone `Stacks.Flatness.subschemeCone K` on it. This file shows that this
cone is a limit cone as soon as `K` is the supremum of the ideal sheaves indexing the system.

The hypothesis is also necessary — `Stacks.Flatness.le_iSup_of_isLimit` — so the limit half of
Tag 0EV9 is *equivalent* to that supremum statement, which is the ideal-sheaf case of Tag 01PG.

## Main results

* `Stacks.Flatness.le_ker_of_cone` : every ideal sheaf indexing the system is contained in the
  kernel of the structure morphism of any cone on it.
* `Stacks.Flatness.coneLift` : the factorization of a cone through the closed subscheme cut out
  by `K`.
* `Stacks.Flatness.isLimitSubschemeConeOfLeISup` and
  `Stacks.Flatness.nonempty_isLimit_subschemeCone_of_le_iSup` : the canonical cone is a limit
  cone when `K` is contained in the supremum of the finitely generated ideal sheaves below it.
* `Stacks.Flatness.iSupCone` : the cone with vertex the closed subscheme cut out by that
  supremum.
* `Stacks.Flatness.le_iSup_of_isLimit` : the converse, so the hypothesis cannot be weakened.

## Implementation notes

This is the limit half of Tag 0EV9, reduced to the single statement that a quasi-coherent ideal
sheaf on a quasi-compact and quasi-separated scheme is the supremum of its finite-type
quasi-coherent subsheaves — the ideal-sheaf case of Tag 01PG, which is not available in this
library or in Mathlib. Nothing else of Tag 0EV9 is used: in particular the almost blowup square
of Tag 0EV6 enters neither this result nor the directedness in
`StacksFrontier/AlgebraicGeometry/Flatness/SubschemeFiltered.lean`.

The argument is the universal property of the closed subscheme cut out by an ideal sheaf. A
morphism `t : T ⟶ X` factors through `J.subscheme` exactly when `J ≤ t.ker`, the factorization
being `t.toImage ≫ AlgebraicGeometry.Scheme.IdealSheafData.inclusion`; uniqueness is free
because `J.subschemeι` is a monomorphism. So a cone on the system is the same thing as a
morphism to `X` whose kernel contains every member of the system, which by the hypothesis is the
same thing as a morphism to `X` whose kernel contains `K`.

Since the system is indexed by the opposite of the preorder of ideal sheaves and the diagram
takes values in `CategoryTheory.Over X`, a cone morphism is determined by its underlying
morphism of schemes, which is what `CategoryTheory.Over.homMk` and
`CategoryTheory.Over.OverMorphism.ext` express.

## References

* [Stacks Project, Tag 0EV9](https://stacks.math.columbia.edu/tag/0EV9)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Flatness

/-- Two morphisms into an object of a slice category whose structure morphism is a monomorphism
agree: both compose with it to the structure morphism of the source. -/
theorem over_hom_ext_of_mono_hom {C : Type*} [Category C] {T : C} {U V : Over T}
    (hV : Mono V.hom) (f g : U ⟶ V) : f = g := by
  ext1
  exact hV.right_cancellation _ _ ((Over.w f).trans (Over.w g).symm)

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- A morphism in `Over X` shrinks the kernel of the structure morphism of the target to that of
the source. -/
private theorem ker_hom_le_of_over_hom {U V : Over X} (f : U ⟶ V) : V.hom.ker ≤ U.hom.ker :=
  (Scheme.Hom.le_ker_comp f.left V.hom).trans_eq (congrArg Scheme.Hom.ker (Over.w f))

/-- Any cone on the inverse system of finite-presentation closed enlargements of the closed
subscheme cut out by `K` has a vertex whose structure morphism to `X` kills every ideal sheaf
indexing the system. -/
theorem le_ker_of_cone (s : Cone (subschemeDiagram K)) (J : FinitePresentationSubscheme K) :
    (J : X.IdealSheafData) ≤ s.pt.hom.ker :=
  J.1.ker_subschemeι.ge.trans
    (ker_hom_le_of_over_hom (V := Over.mk J.1.subschemeι) (s.π.app (.op J)))

/-- The factorization of the structure morphism of a cone through the closed subscheme cut out
by `K`, available as soon as `K` is the supremum of the ideal sheaves indexing the system. -/
def coneLift (hK : K ≤ ⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData))
    (s : Cone (subschemeDiagram K)) : s.pt ⟶ (subschemeCone K).pt :=
  Over.homMk (show s.pt.left ⟶ (subschemeCone K).pt.left from s.pt.hom.toImage ≫
    Scheme.IdealSheafData.inclusion (hK.trans (iSup_le (le_ker_of_cone K s))))
    (by simp [subschemeCone])

/-- The closed subscheme cut out by `K` is the limit of its finite-presentation closed
enlargements, provided `K` is the supremum of the ideal sheaves indexing them. -/
def isLimitSubschemeConeOfLeISup
    (hK : K ≤ ⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData)) :
    IsLimit (subschemeCone K) where
  lift := coneLift K hK
  fac _ J := over_hom_ext_of_mono_hom (inferInstanceAs (Mono J.unop.1.subschemeι)) _ _
  uniq _ _ _ := over_hom_ext_of_mono_hom (inferInstanceAs (Mono K.subschemeι)) _ _

/-- The cone on the inverse system of finite-presentation closed enlargements of the closed
subscheme cut out by `K` whose vertex is the closed subscheme cut out by the supremum of the
ideal sheaves indexing the system. -/
def iSupCone : Cone (subschemeDiagram K) where
  pt := Over.mk (⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData)).subschemeι
  π :=
    { app J := Over.homMk (Scheme.IdealSheafData.inclusion (le_iSup _ J.unop))
        (by simp [subschemeDiagram])
      naturality J H _ :=
        over_hom_ext_of_mono_hom (inferInstanceAs (Mono H.unop.1.subschemeι)) _ _ }

/-- The hypothesis of `Stacks.Flatness.isLimitSubschemeConeOfLeISup` is also necessary: the
canonical cone is a limit cone only if `K` is the supremum of the ideal sheaves indexing the
system. So the limit half of Tag 0EV9 is *equivalent* to the ideal-sheaf case of Tag 01PG. -/
theorem le_iSup_of_isLimit (h : IsLimit (subschemeCone K)) :
    K ≤ ⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData) :=
  K.ker_subschemeι.ge.trans
    ((ker_hom_le_of_over_hom (h.lift (iSupCone K))).trans_eq
      (Scheme.IdealSheafData.ker_subschemeι _))

/-- The closed subscheme cut out by `K` is the limit of its finite-presentation closed
enlargements, provided `K` is the supremum of the ideal sheaves indexing them. -/
theorem nonempty_isLimit_subschemeCone_of_le_iSup
    (hK : K ≤ ⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData)) :
    Nonempty (IsLimit (subschemeCone K)) :=
  ⟨isLimitSubschemeConeOfLeISup K hK⟩

end Stacks.Flatness

end
