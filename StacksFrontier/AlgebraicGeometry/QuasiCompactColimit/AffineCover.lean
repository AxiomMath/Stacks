module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Colimit
public import StacksFrontier.AlgebraicGeometry.QuasiCompactColimit.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Subalgebra
public import StacksFrontier.AlgebraicGeometry.QuasiCompactColimit.Pointwise

/-!
# A cocone of algebra sheaves is colimiting as soon as it is so on affine sections

The affine opens of a scheme form a basis of its topology, so the sectionwise criterion of
`Stacks.QuasiCompactColimit.isColimitOfBasis` applies to them, and the `CategoryTheory.Under`
layer is free for a connected diagram
(`Stacks.RelativeSpec.AlgebraSheaf.nonempty_isColimit_iff`).  Combining the two with the
elementwise recognition of filtered colimits of commutative rings reduces the colimit assertion
of Stacks Tag 05JT to one statement of commutative algebra over each affine open: every section
of the algebra comes from a member of the diagram.

## Main definitions

* `Stacks.QuasiCompactColimit.algebraSectionsFunctor`: sections over a fixed open, as a functor
  on algebra sheaves.

## Main results

* `Stacks.QuasiCompactColimit.nonempty_isColimit_of_affineOpens`: **a cocone of algebra sheaves
  over a connected diagram is colimiting as soon as its cocones of sections over the affine
  opens are colimiting.**
* `Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections` and
  `Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections_of_mono`: the same with the
  sectionwise colimit property replaced by its elementwise form, the second discharging the
  injectivity half from a monomorphism hypothesis, which holds for a diagram of subobjects.

## Implementation notes

No quasi-compactness or quasi-separatedness hypothesis is used, and none is available to be
used: a basis suffices for the reduction, and the affine opens are a basis of any scheme
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`). What Tag 05JT needs those two hypotheses for
is the verification of the sectionwise hypothesis -- producing, from a section over an affine
open, a *global* quasi-coherent subalgebra of finite type containing it -- which is not done
here.

The injectivity half of
`Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections_of_mono` is
`Stacks.AlgebraicGeometry.IntegralSubalgebras.injective_app_of_mono`, which is already proved;
nothing is reproved here. One point about it is worth recording: a lemma about
`CategoryTheory.Mono` for morphisms of `TopCat.Sheaf` cannot be proved by handing instance
search the pullback-preservation of `CategoryTheory.sheafToPresheaf`. `TopCat.Sheaf` is a
definition with a derived category instance, so `CategoryTheory.Limits.cospan f f` is formed
over that instance and the preservation instance for the other one does not apply --
even with `CategoryTheory.Limits.HasLimitsOfShape`,
`CategoryTheory.Limits.PreservesLimitsOfShape` and a transported `Mono` hypothesis all present
and the goal still unsolved. The preservation must be stated for `TopCat.Sheaf.forget` itself,
which is what `Stacks.AlgebraicGeometry.IntegralSubalgebras.sheafForget_preservesMonomorphisms`
does.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [The Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec

universe v' u' u

namespace Stacks.QuasiCompactColimit

variable {X : Scheme.{u}}

/-- Sections over a fixed open set, as a functor on algebra sheaves. -/
def algebraSectionsFunctor (U : X.Opens) : AlgebraSheaf X ⥤ CommRingCat.{u} :=
  Under.forget X.sheaf ⋙ sectionsFunctor U

/-- The value of `algebraSectionsFunctor U` on an algebra sheaf `A` is the ring of sections of
`A` over `U`. -/
@[simp]
theorem algebraSectionsFunctor_obj (U : X.Opens) (A : AlgebraSheaf X) :
    (algebraSectionsFunctor U).obj A = A.right.obj.obj (op U) := rfl

/-- The value of `algebraSectionsFunctor U` on a morphism `f` of algebra sheaves is the component
of `f` at `U`. -/
@[simp]
theorem algebraSectionsFunctor_map (U : X.Opens) {A B : AlgebraSheaf X} (f : A ⟶ B) :
    (algebraSectionsFunctor U).map f = f.right.hom.app (op U) := rfl

variable {K : Type u'} [Category.{v'} K] {F : K ⥤ AlgebraSheaf X}

/-- **A cocone of algebra sheaves over a connected diagram is colimiting as soon as its cocones
of sections over the affine opens are colimiting.** -/
theorem nonempty_isColimit_of_affineOpens [IsConnected K] (c : Cocone F)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      Nonempty (IsColimit ((algebraSectionsFunctor U).mapCocone c))) :
    Nonempty (IsColimit c) := by
  refine (AlgebraSheaf.nonempty_isColimit_iff c).2 ?_
  refine nonempty_isColimit_of_basis _ (B := fun U : X.affineOpens => (U : X.Opens)) ?_ ?_
  · rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  · exact fun U => h U U.2

/-- **A cocone of algebra sheaves over a filtered diagram is colimiting as soon as, over every
affine open, its components are injective and jointly surjective on sections.**  This is the
form in which the affine computation of Stacks Tag 05JT supplies the hypothesis. -/
theorem nonempty_isColimit_of_sections [IsFiltered K] (c : Cocone F)
    (hinj : ∀ U : X.Opens, IsAffineOpen U →
      ∀ k : K, Function.Injective ((algebraSectionsFunctor U).map (c.ι.app k)))
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → ∀ x : (algebraSectionsFunctor U).obj c.pt,
      ∃ (k : K) (y : (algebraSectionsFunctor U).obj (F.obj k)),
        (algebraSectionsFunctor U).map (c.ι.app k) y = x) :
    Nonempty (IsColimit c) :=
  let := IsFiltered.isConnected (C := K)
  nonempty_isColimit_of_affineOpens c fun U hU =>
    ⟨isColimitOfInjective _ (hsurj U hU) (hinj U hU)⟩

/-- **A cocone of algebra sheaves over a filtered diagram whose components are monomorphisms is
colimiting as soon as, over every affine open, every section comes from some member of the
diagram.**  For a diagram of subobjects the monomorphism hypothesis is automatic, so joint
surjectivity on affine sections is the only remaining input. -/
theorem nonempty_isColimit_of_sections_of_mono [IsFiltered K] (c : Cocone F)
    (hmono : ∀ k : K, Mono (c.ι.app k))
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → ∀ x : (algebraSectionsFunctor U).obj c.pt,
      ∃ (k : K) (y : (algebraSectionsFunctor U).obj (F.obj k)),
        (algebraSectionsFunctor U).map (c.ι.app k) y = x) :
    Nonempty (IsColimit c) := by
  refine nonempty_isColimit_of_sections c (fun U _ k => ?_) hsurj
  have := hmono k
  exact Stacks.AlgebraicGeometry.IntegralSubalgebras.injective_app_of_mono (c.ι.app k) U

end Stacks.QuasiCompactColimit
