module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiHomGlue
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidStack

/-!
# The transported component of a morphism of Frobenius-colimit descent data

After the reduction of
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoidZariskiDescent.lean`,
condition (1) of Stacks 0EX9 for Stacks Tag 0EXE rests on the single hypothesis that
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` is a stack for every Zariski family of the
big h category over `S`.  Its separated half is
`AlgebraicGeometry.faithful_toDescentData_frobeniusColimitModulePseudofunctor`; the next half is
fullness, which asks that a morphism between the canonical descent data of two sheaves of
`colim_F 𝒪_U`-modules come from a global morphism.

What such a morphism carries is the `CategoryTheory.Pseudofunctor.DescentData.Hom.comm` field: a
compatibility over every object of the site mapping to two members of the family.  The gluing of
morphisms that has to consume it,
`AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion`, asks instead
for an agreement over every *open* below two members.  This file supplies the two passages that
do not depend on the geometry of open immersions: the shape `comm` takes once the two components
have been transported to a common object, and the identification of the comparison through which
that transport is defined with the one the rest of the development speaks.

## Main results

* `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom_eq_of_toDescentData`: **the transported
  component of a morphism between the canonical descent data of two objects does not depend on
  which member of the family it is transported along.**  Stated for an arbitrary pseudofunctor on
  a locally discrete bicategory.
* `AlgebraicGeometry.frobeniusColimitModulePseudofunctor_mapComp'_hom_app` and
  `AlgebraicGeometry.frobeniusColimitModulePseudofunctor_mapComp'_inv_app`: **the composition
  comparison of the pseudofunctor of all Frobenius-colimit modules at a commuting triangle of the
  big h category over `S` is `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` at the
  underlying triangle of schemes**, in both directions.

## Implementation notes

**The transport is Mathlib's `pullHom`, and the passage out of `comm` is already available
there.**  `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` conjugates a morphism
between two pullbacks by the composition comparisons of the pseudofunctor, and
`CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv` identifies the morphisms of
descent data in the image of `CategoryTheory.Pseudofunctor.toDescentData` with the compatible
families of the presheaf of morphisms.  Its inverse is exactly the statement that the transported
components agree, so `pullHom_hom_eq_of_toDescentData` is that identification read at one object
and one pair of indices.  No manipulation of the `mapComp'` isomorphisms is needed, and none is
done there.

**Why the general statement is made at a variable pseudofunctor.**  Proved at
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` instead, the same statement exhausts the
elaborator's `whnf` budget: typing the components forces the Frobenius colimit of the structure
sheaf to be unfolded.  At a variable there is nothing to unfold, and the instance at the
Frobenius pseudofunctor is a plain application.

**Why the two composition comparisons are recorded separately, and not as one equation for
`pullHom`.**  The composite statement — that `pullHom φ g gf₁ gf₂` is the conjugate of `φ` by the
two instances of `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` — elaborates, and the
kernel then refuses it, `(kernel) deterministic timeout`, both from `rfl` after substituting the
two triangle equations and from the `simp only` proof that rewrites with the two identifications
below.  It carries no content beyond them, because `pullHom` *is* that conjugate by definition;
a consumer rewrites with the two identifications at the point of use, where the composite is
short.

**What is still missing for fullness.**  The agreement of the transported components is over the
objects of the site, while the gluing consumes an agreement over the opens of the base.  Crossing
between them needs the compatibility of
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` with passing to a smaller open, which
the development does not have: the natural isomorphism it reduces to is the one written out in
the module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean`.  Nothing here
depends on it, and nothing here supplies it.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat Opposite TopologicalSpace
open Stacks.Frobenius

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {M N : F.obj (.mk (op S))}

/-- **The transported component of a morphism between the canonical descent data of two objects
does not depend on which member of the family it is transported along.**

Let `θ` be a morphism from the descent datum of `M` to the descent datum of `N` along a family
`f i : X i ⟶ S`, and let `q : Z ⟶ S` factor through two members of the family, by `t₁` and `t₂`.
Transporting the component of `θ` at the first index along `t₁` and the component at the second
index along `t₂` gives the same morphism of the pullbacks of `M` and of `N` to `Z`.

This is the `CategoryTheory.Pseudofunctor.DescentData.Hom.comm` field in the form a gluing
argument consumes it, and it is
`CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv` — which identifies such a
`θ` with a compatible family of the presheaf of morphisms — read at `Z` and at the pair of
indices. -/
theorem pullHom_hom_eq_of_toDescentData
    (θ : (F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N)
    {Z : C} (q : Z ⟶ S) {i₁ i₂ : ι} (t₁ : Z ⟶ X i₁) (t₂ : Z ⟶ X i₂)
    (h₁ : t₁ ≫ f i₁ = q) (h₂ : t₂ ≫ f i₂ = q) :
    pullHom (θ.hom i₁) t₁ q q h₁ h₁ = pullHom (θ.hom i₂) t₂ q q h₂ h₂ :=
  ((subtypeCompatibleHomEquiv F f).symm θ).property i₁ i₂ (Over.mk q)
    (Over.homMk t₁ h₁) (Over.homMk t₂ h₂)
    (Over.OverMorphism.ext (by simpa using h₁.trans h₂.symm))

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **The composition comparison of the pseudofunctor of all Frobenius-colimit modules is the
comparison of transition functors at the underlying triangle of schemes.**

For `b : Y ⟶ X₁` and `a : X₁ ⟶ U` in the big h category over `S` with `b ≫ a = q`, the
comparison `CategoryTheory.Pseudofunctor.mapComp'` of
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at that triangle is
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` at the images of `a`, `b` and `q` in the
schemes — read with the opposite orientation, so that the `hom` of one is the `inv` of the other.

Keeping `q` a variable subject to an equation, rather than writing `b ≫ a`, is what makes the
statement usable: the arrow a descent datum is instantiated at is a given arrow of the site, not
a syntactic composite.  The proof substitutes the equation and is left with the pseudofunctor's
own structure map. -/
theorem frobeniusColimitModulePseudofunctor_mapComp'_hom_app
    {U X₁ Y : BigHOver B S hS} (a : X₁ ⟶ U) (b : Y ⟶ X₁) (q : Y ⟶ U) (hq : b ≫ a = q)
    (M : _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS U)) :
    ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp'
        a.op.toLoc b.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).hom.toNatTrans.app M =
      (frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map b)
          ((BigHOver.toScheme B S hS).map a) ((BigHOver.toScheme B S hS).map q)
          (isInCharacteristic_bigHOver B S hS p hpS Y)
          (isInCharacteristic_bigHOver B S hS p hpS X₁)
          (isInCharacteristic_bigHOver B S hS p hpS U)
          (by rw [← Functor.map_comp, hq])).inv.app M := by
  subst hq
  rfl

/-- `AlgebraicGeometry.frobeniusColimitModulePseudofunctor_mapComp'_hom_app` in the other
direction: the inverse of the composition comparison of the pseudofunctor of all
Frobenius-colimit modules is the forward comparison of transition functors at the underlying
triangle of schemes.

Both directions are needed, because
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` conjugates by the `hom` of the
comparison at the source and the `inv` of the comparison at the target. -/
theorem frobeniusColimitModulePseudofunctor_mapComp'_inv_app
    {U X₁ Y : BigHOver B S hS} (a : X₁ ⟶ U) (b : Y ⟶ X₁) (q : Y ⟶ U) (hq : b ≫ a = q)
    (M : _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS U)) :
    ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp'
        a.op.toLoc b.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).inv.toNatTrans.app M =
      (frobeniusColimitPullbackTriangleIso p ((BigHOver.toScheme B S hS).map b)
          ((BigHOver.toScheme B S hS).map a) ((BigHOver.toScheme B S hS).map q)
          (isInCharacteristic_bigHOver B S hS p hpS Y)
          (isInCharacteristic_bigHOver B S hS p hpS X₁)
          (isInCharacteristic_bigHOver B S hS p hpS U)
          (by rw [← Functor.map_comp, hq])).hom.app M := by
  subst hq
  rfl

end AlgebraicGeometry

end
