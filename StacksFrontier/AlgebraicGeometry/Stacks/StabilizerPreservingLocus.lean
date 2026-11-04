module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceBaseChangeSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedLiftingLocus
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Transfer

/-!
# The stabilizer-preserving locus of an unramified morphism (Stacks 0DUA)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site which
is representable by algebraic spaces and unramified, and assume the inertia `ℐ_𝒴 ⟶ 𝒴` of the
target is proper. **Stacks 0DUA** says that the set of `x ∈ |𝒳|` at which `f` induces an
isomorphism between the automorphism groups at `x` and at `f(x)` (**Stacks 0DTW**,
`AlgebraicGeometry.Stack.InducesIsomorphismAt`) is open, and that for the open substack
`𝒰 ⊆ 𝒳` it corresponds to, the canonical comparison `ℐ_𝒰 ⟶ 𝒰 ×_𝒴 ℐ_𝒴` of **Stacks 06R5** is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.stabilizerPreservingLocus`: the set of points of **Stacks 0DUA**.
* `AlgebraicGeometry.Stack.IsStabilizerPreserving`: the condition that the comparison
  `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of **Stacks 06R5** is an isomorphism, read — as in **Stacks 0DUB** and
  **Stacks 0DU9** — as an equivalence over the big fppf site.
* `AlgebraicGeometry.Stack.inertiaPullbackSquare`: the 2-fibre product `𝒳 ×_𝒴 ℐ_𝒴`, whose
  objects are `CategoryTheory.InertiaPullback.Obj`.
* `AlgebraicGeometry.Stack.LiftsAutomorphism`: the objects `(x, (y, α), ψ)` of `𝒳 ×_𝒴 ℐ_𝒴`
  whose automorphism `ψ ≫ α ≫ ψ⁻¹` of `f(x)` comes from a vertical automorphism of `x`.
* `AlgebraicGeometry.Stack.liftsAutomorphismOpenSubstack`: the open substack of `𝒳 ×_𝒴 ℐ_𝒴`
  they form.

## Main results

* `AlgebraicGeometry.Stack.compl_stabilizerPreservingLocus_eq_image`: the complement of the
  locus is the image in `|𝒳|` of the complement of `|liftsAutomorphismOpenSubstack|`.
* `AlgebraicGeometry.Stack.isOpen_stabilizerPreservingLocus`: the locus is open.
* `AlgebraicGeometry.Stack.isStabilizerPreserving_openSubstack_inclusion_comp`: the restriction
  of `f` to an open substack whose point set is the locus is stabilizer preserving.
* `AlgebraicGeometry.Stack.exists_openSubstack_isStabilizerPreserving`: **Stacks 0DUA**.

## Implementation notes

The proof is the source's, with the chart replaced by the 2-fibre product `𝒳 ×_𝒴 ℐ_𝒴` itself.
The source pulls the comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` back to a scheme chart `U → 𝒳`, getting an
open immersion `G → H` of group algebraic spaces over `U` with `H` proper over `U`, and reads the
complement of the locus as the image of `|H| \ |G|` under the closed map `|H| → |U|`. Here the
image of the comparison is the full subcategory `LiftsAutomorphism` of `𝒳 ×_𝒴 ℐ_𝒴`. At a
scheme-valued point `z` of `𝒳 ×_𝒴 ℐ_𝒴` with values in `V`, the automorphism carried by `z`
lifts exactly where two sections of the algebraic space representing the base change of `f`
along `f(x)` agree, and that algebraic space is unramified over `V`, so its diagonal is an open
immersion (**Stacks 05W1**): this is
`AlgebraicGeometry.Stack.exists_isOpen_liftsAutomorphism_iff`, the openness of `G` in `H`. So
`LiftsAutomorphism` cuts out an open substack, by
`AlgebraicGeometry.Stack.openSubstackOfIsOpenSubspace`, whose point set is open by
**Stacks 06FJ**. A point of `|𝒳|` lies outside the locus exactly when some vertical automorphism
of `f(b)` at an object `b` above it fails to lift, and by
`AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_isRelativelyUnramified` it then fails to lift
at a field-valued point already; that is a point of `|𝒳 ×_𝒴 ℐ_𝒴|` outside the open substack.
The projection `𝒳 ×_𝒴 ℐ_𝒴 ⟶ 𝒳` is the base change of `ℐ_𝒴 ⟶ 𝒴` along `f`, which is closed on
points because `ℐ_𝒴 ⟶ 𝒴` is universally closed, so the complement of the locus is closed.

The open substack of the second assertion exists by the surjectivity half of **Stacks 06FJ**,
`AlgebraicGeometry.Stack.exists_openSubstack_pointSet_eq`. The source's last sentence applies
**Stacks 0DU9** to `𝒰 ⟶ 𝒴`; the argument is run directly on `𝒰`, for every open substack with
the locus as its point set: a field-valued point of an object of `𝒰` lies in `𝒰`
(`AlgebraicGeometry.Stack.OpenSubstack.prop_of_hom`), hence in the locus, so a vertical
automorphism lifts at every field-valued point and therefore lifts, `f` being representable and
unramified. This needs neither the injectivity half of **Stacks 06FJ** nor permanence properties
of unramified 1-morphisms of algebraic stacks.

## References

* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 0DU8](https://stacks.math.columbia.edu/tag/0DU8)
* [Stacks Project, Tag 0DU9](https://stacks.math.columbia.edu/tag/0DU9)
* [Stacks Project, Tag 0DUA](https://stacks.math.columbia.edu/tag/0DUA)
-/

@[expose] public section

namespace CategoryTheory.InertiaPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] (pX : 𝒳 ⥤ 𝒞) (pY : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)

/-- The objects of the 2-fibre product `𝒳 ×_𝒴 I_𝒴` of a functor `F : 𝒳 ⥤ 𝒴` and the projection
`(y, α) ↦ y` of the inertia of `pY`: an object `x` of `𝒳`, an object `y` of `𝒴` with a vertical
automorphism `α`, and an isomorphism `F x ≅ y`, all over one object of `𝒞`. -/
abbrev Obj :=
  TwoFibreProductOver pX (RelativeInertia.π pY ⋙ pY) pY F (RelativeInertia.π pY)

variable {pX pY F}

/-- The comparison isomorphism `ψ : F x ≅ y` of an object `(x, (y, α), ψ)` of `𝒳 ×_𝒴 I_𝒴`,
with its target written as the underlying object of `(y, α)`. -/
abbrev isoY (c : Obj pX pY F) : F.obj c.x ≅ c.y.obj := c.iso

/-- The automorphism `ψ ≫ α ≫ ψ⁻¹` of `F x` carried by an object `(x, (y, α), ψ)` of
`𝒳 ×_𝒴 I_𝒴`. -/
def aut (c : Obj pX pY F) : F.obj c.x ⟶ F.obj c.x :=
  (isoY c).hom ≫ c.y.auto.hom ≫ (isoY c).inv

/-- The automorphism carried by an object of `𝒳 ×_𝒴 I_𝒴` lies over an identity. -/
theorem isHomLift_aut (c : Obj pX pY F) : pY.IsHomLift (𝟙 c.base) (aut c) := by
  have h₁ : pY.IsHomLift (𝟙 c.base) (isoY c).hom := c.vertical
  have hy : pY.obj c.y.obj = c.base := c.hy
  have h₃ : pY.IsHomLift (𝟙 c.base) c.y.auto.hom :=
    IsHomLift.of_fac' pY _ _ hy hy (by rw [c.y.cond]; simp)
  exact Functor.isHomLift_id_comp pY _ _ h₁ (Functor.isHomLift_id_comp pY _ _ h₃ inferInstance)

/-- The automorphism carried by an object is natural along morphisms of `𝒳 ×_𝒴 I_𝒴`. -/
theorem aut_naturality {c' c : Obj pX pY F} (u : c' ⟶ c) :
    aut c' ≫ F.map u.a = F.map u.a ≫ aut c := by
  have hw : F.map u.a ≫ (isoY c).hom = (isoY c').hom ≫ u.b.hom := u.w
  have hcomm : u.b.hom ≫ c.y.auto.hom = c'.y.auto.hom ≫ u.b.hom := u.b.comm
  have hw' : (isoY c').inv ≫ F.map u.a = u.b.hom ≫ (isoY c).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hw, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  unfold aut
  rw [Category.assoc, Category.assoc, hw', ← Category.assoc c'.y.auto.hom, ← hcomm,
    Category.assoc, ← Category.assoc (isoY c').hom, ← hw, Category.assoc]

/-- An object `(x, (y, α), ψ)` of `𝒳 ×_𝒴 I_𝒴` *lifts its automorphism* when the automorphism
`ψ ≫ α ≫ ψ⁻¹` of `F x` is the image of a vertical automorphism of `x`. -/
def LiftsAut (c : Obj pX pY F) : Prop :=
  ∃ β : c.x ⟶ c.x, pX.IsHomLift (𝟙 c.base) β ∧ F.map β = aut c

variable (hF : F ⋙ pY = pX)
include hF

/-- **Lifting along a morphism.** Let `u : c' ⟶ c` be a morphism of `𝒳 ×_𝒴 I_𝒴`. Then `c'` lifts
its automorphism exactly when the automorphism of `c`, pulled back along the first component
`u.a`, lifts: some vertical endomorphism `γ` of the first component of `c'` satisfies
`F γ ≫ F u.a = F u.a ≫ aut c`. -/
theorem liftsAut_iff_of_hom (hpY : pY.IsFiberedInGroupoids) {c' c : Obj pX pY F} (u : c' ⟶ c) :
    LiftsAut c' ↔ ∃ γ : c'.x ⟶ c'.x, pX.IsHomLift (𝟙 c'.base) γ ∧
      F.map γ ≫ F.map u.a = F.map u.a ≫ aut c := by
  have hua : pX.IsHomLift u.hbase u.a := u.ha
  have hFua : pY.IsHomLift u.hbase (F.map u.a) := Functor.isHomLift_map_of_comp_eq hF _ u.a
  have _ : pY.IsStronglyCartesian u.hbase (F.map u.a) := hpY.isStronglyCartesian_homLift _ _
  refine ⟨fun ⟨β, hβ, hβeq⟩ => ⟨β, hβ, by rw [hβeq, aut_naturality]⟩,
    fun ⟨γ, hγ, hγeq⟩ => ⟨γ, hγ, ?_⟩⟩
  have _ : pY.IsHomLift (𝟙 c'.base) (F.map γ) := Functor.isHomLift_map_of_comp_eq hF _ γ
  have _ : pY.IsHomLift (𝟙 c'.base) (aut c') := isHomLift_aut c'
  exact Functor.IsStronglyCartesian.ext pY u.hbase (F.map u.a) (𝟙 c'.base)
    (hγeq.trans (aut_naturality u).symm)

/-- **Lifting is inherited along morphisms.** If `c` lifts its automorphism then so does every
object of `𝒳 ×_𝒴 I_𝒴` mapping to `c`: pull the lift back along the first component of the
morphism, which is cartesian. -/
theorem liftsAut_of_hom (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    {c' c : Obj pX pY F} (u : c' ⟶ c) (h : LiftsAut c) : LiftsAut c' := by
  obtain ⟨β, hβ, hβeq⟩ := h
  have hua : pX.IsHomLift u.hbase u.a := u.ha
  have _ : pX.IsStronglyCartesian u.hbase u.a := hpX.isStronglyCartesian_homLift _ _
  have _ : pX.IsHomLift u.hbase (u.a ≫ β) := by
    simpa using (inferInstance : pX.IsHomLift (u.hbase ≫ 𝟙 c.base) (u.a ≫ β))
  let β' := Functor.IsStronglyCartesian.map pX u.hbase u.a (Category.id_comp u.hbase).symm
    (u.a ≫ β)
  have hβ'v : pX.IsHomLift (𝟙 c'.base) β' := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hβ'fac : β' ≫ u.a = u.a ≫ β := Functor.IsStronglyCartesian.fac _ _ _ _ _
  refine (liftsAut_iff_of_hom hF hpY u).2 ⟨β', hβ'v, ?_⟩
  rw [← F.map_comp, hβ'fac, F.map_comp, hβeq]

omit hF in
/-- A morphism of `𝒳 ×_𝒴 I_𝒴` lying over `g` for the structure functor has first component
lying over `g`. -/
theorem isHomLift_a_of_isHomLift {R R' : 𝒞} (g : R ⟶ R') {c' c : Obj pX pY F} (u : c' ⟶ c)
    (hu : (TwoFibreProductOver.structureFunctor _ _ _ _ _).IsHomLift g u) :
    pX.IsHomLift g u.a :=
  Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq g u

end CategoryTheory.InertiaPullback

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Definitions

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *stabilizer preserving*, or
*fixed-point reflecting*, when the canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of **Stacks 06R5**
(`CategoryTheory.inertiaPullbackComparison`) is an isomorphism.

The comparison is read as an equivalence *over* the big fppf site, which is the rendering used
by `AlgebraicGeometry.Stack.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange`
for **Stacks 0DUB** and by
`AlgebraicGeometry.Stack.inducesIsomorphismAt_of_inertiaPullbackComparison_isEquivalenceOver`
for **Stacks 0DU9**. -/
abbrev IsStabilizerPreserving (f : 𝒳 ⟶ 𝒴) : Prop :=
  Nonempty (IsEquivalenceOver
    (RelativeInertia.toBase 𝒳.val.val.p)
    (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴.val.val.p)
      𝒳.val.val.p 𝒴.val.val.p (RelativeInertia.π 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom))
    (inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)))

/-- **The set of points of Stacks 0DUA.** The set of `x ∈ |𝒳|` at which a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` induces an isomorphism between the automorphism groups
at `x` and at `f(x)`, in the sense of **Stacks 0DTW**
(`AlgebraicGeometry.Stack.InducesIsomorphismAt`). -/
def stabilizerPreservingLocus (f : 𝒳 ⟶ 𝒴) : Set (AlgebraicStacks.points B S hS 𝒳) :=
  {x | InducesIsomorphismAt B S hS f x}

end Definitions

section Restriction

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The automorphism groups at an object of an open substack are those of the object.** If a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` induces an isomorphism between the
automorphism groups at an object of `𝒳` lying in an open substack `U`, then its restriction to
`U` does so at the corresponding object of `U`.

The inclusion of `U` is fully faithful over the site, hence bijective on vertical automorphism
groups, and the restriction of `f` is the composite of the inclusion with `f`. -/
theorem bijective_automorphismGroupMap_openSubstackInclusion_comp (U : OpenSubstack 𝒳)
    (f : 𝒳 ⟶ 𝒴) (b : U.toAlgebraicStack.val.val.obj)
    (hb : Function.Bijective (automorphismGroupMap B S hS f b.obj)) :
    Function.Bijective (automorphismGroupMap B S hS (U.inclusion ≫ f) b) :=
  Functor.bijective_verticalAutMap_comp
    (CatFiberedInGroupoids.homFunctor U.inclusion.hom)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p U.inclusion.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (U.inclusion ≫ f).hom) b
    (Functor.bijective_verticalAutMap_of_fullyFaithful _ _
      (Functor.FullyFaithful.ofFullyFaithful _) b) hb

/-- **The condition of Stacks 0DTW restricts to an open substack.** If a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` induces an isomorphism between automorphism groups at
the image in `|𝒳|` of a point of an open substack `U`, then the restriction of `f` to `U` does
so at that point of `|U|`. -/
theorem inducesIsomorphismAt_openSubstackInclusion_comp (U : OpenSubstack 𝒳) (f : 𝒳 ⟶ 𝒴)
    (q : AlgebraicStacks.points B S hS U.toAlgebraicStack)
    (hq : InducesIsomorphismAt B S hS f (AlgebraicStacks.pointsMap B S hS U.inclusion q)) :
    InducesIsomorphismAt B S hS (U.inclusion ≫ f) q := by
  refine (inducesIsomorphismAt_iff_forall_representatives B S hS (U.inclusion ≫ f) q).2
    fun p hp b m => bijective_automorphismGroupMap_openSubstackInclusion_comp B S hS U f b ?_
  exact (inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 hq
    (fieldValuedPointMap B S hS U.toAlgebraicStack.val.val U.inclusion.hom.hom p)
    (by rw [← hp]; rfl) b.obj
    ((CatFiberedInGroupoids.homFunctor U.inclusion.hom).map m)

end Restriction

section InertiaPullback

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The 2-fibre product square `𝒳 ×_𝒴 ℐ_𝒴` of `f : 𝒳 ⟶ 𝒴` and the inertia `ℐ_𝒴 ⟶ 𝒴` of the
target. An object over `T` is an object `x` of `𝒳` over `T`, an object `(y, α)` of `ℐ_𝒴`, that
is an object `y` of `𝒴` over `T` with a vertical automorphism `α`, and an isomorphism
`f(x) ≅ y` over `T`; its objects are `CategoryTheory.InertiaPullback.Obj`. -/
abbrev inertiaPullbackSquare :
    Bicategory.TwoCommSq f (inertiaProjectionAlgebraicStacks B S hS 𝒴) :=
  twoFibreProductSquareAlgebraicStacks B S hS f (inertiaProjectionAlgebraicStacks B S hS 𝒴)

/-- The property of an object `(x, (y, α), ψ)` of `𝒳 ×_𝒴 ℐ_𝒴` that the automorphism of `f(x)`
it carries, `ψ ≫ α ≫ ψ⁻¹`, comes from a vertical automorphism of `x`. These objects are the
image of the canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of **Stacks 06R5**, the `G ⊆ H` of the
proof of **Stacks 0DUA**. -/
abbrev LiftsAutomorphism : ObjectProperty (inertiaPullbackSquare B S hS f).pt.val.val.obj :=
  fun c => InertiaPullback.LiftsAut (pX := 𝒳.val.val.p) (pY := 𝒴.val.val.p)
    (F := CatFiberedInGroupoids.homFunctor f.hom) c

/-- `AlgebraicGeometry.Stack.LiftsAutomorphism` is inherited along morphisms of
`𝒳 ×_𝒴 ℐ_𝒴`. -/
theorem liftsAutomorphism_of_hom {c' c : (inertiaPullbackSquare B S hS f).pt.val.val.obj}
    (m : c' ⟶ c) (h : LiftsAutomorphism B S hS f c) : LiftsAutomorphism B S hS f c' :=
  InertiaPullback.liftsAut_of_hom (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    𝒳.val.property 𝒴.val.property m h

/-- **The lifting locus at a scheme-valued point of `𝒳 ×_𝒴 ℐ_𝒴` is open.** Let `f` be
representable by algebraic spaces and unramified, and let `z` be a scheme-valued point of
`𝒳 ×_𝒴 ℐ_𝒴` with values in `V`. There is an open subset `W` of `V` such that the value of `z`
at an object `a` of the big fppf site of `V` lifts its automorphism exactly when the image of
`a` in `V` lies in `W`.

This is the source's statement that `G ⟶ H` is an open immersion, read at the point `z`: the
automorphism carried by `z` lifts exactly where two sections of the algebraic space representing
the base change of `f` along `f(x)` agree, and that algebraic space is unramified over `V`
(`AlgebraicGeometry.Stack.exists_isOpen_lift_iff_range_subset`). -/
theorem exists_isOpen_liftsAutomorphism_iff
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hur : IsRelativelyUnramified B S hS f.hom) {V : BigFppfOver B S hS}
    (z : BigFppfOver B V.left.1 V.left.2 ⥤ (inertiaPullbackSquare B S hS f).pt.val.val.obj)
    (hz : z ⋙ (inertiaPullbackSquare B S hS f).pt.val.val.p = Over.map V.hom) :
    ∃ W : Set ((BigFppfOver.toScheme B S hS).obj V), IsOpen W ∧
      ∀ (a : BigFppfOver B V.left.1 V.left.2) (t : a ⟶ Over.mk (𝟙 V.left)),
        LiftsAutomorphism B S hS f (z.obj a) ↔
          Set.range ((BigFppfOver.toScheme B V.left.1 V.left.2).map t) ⊆ W := by
  have hF : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒳.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hbase : ∀ a, (z.obj a).base = (Over.map V.hom).obj a := fun a => Functor.congr_obj hz a
  have hT' : (Over.map V.hom).obj (Over.mk (𝟙 V.left)) = V := Functor.overMap_obj_mkId V
  have hcb : (z.obj (Over.mk (𝟙 V.left))).base = V := (hbase _).trans hT'
  have h₁ : 𝒳.val.val.p.obj (z.obj (Over.mk (𝟙 V.left))).x = V :=
    (z.obj (Over.mk (𝟙 V.left))).hx.trans hcb
  have hφ : 𝒴.val.val.p.IsHomLift (𝟙 V)
      (InertiaPullback.aut (pX := 𝒳.val.val.p) (pY := 𝒴.val.val.p)
        (F := CatFiberedInGroupoids.homFunctor f.hom) (z.obj (Over.mk (𝟙 V.left)))) := by
    have h := InertiaPullback.isHomLift_aut (pX := 𝒳.val.val.p) (pY := 𝒴.val.val.p)
      (F := CatFiberedInGroupoids.homFunctor f.hom) (z.obj (Over.mk (𝟙 V.left)))
    rwa [hcb] at h
  obtain ⟨W, hW, hWe⟩ := exists_isOpen_lift_iff_range_subset B S hS f.hom hrep hur h₁ h₁ _ hφ
  refine ⟨W, hW, fun a t => ?_⟩
  have hzt : (TwoFibreProductOver.structureFunctor _ _ _ _ _).IsHomLift
      ((Over.map V.hom).map t) (z.map t) :=
    Functor.isHomLift_map_of_comp_eq hz ((Over.map V.hom).map t) t
  have hm₀ : 𝒳.val.val.p.IsHomLift ((Over.map V.hom).map t) (z.map t).a :=
    InertiaPullback.isHomLift_a_of_isHomLift _ (z.map t) hzt
  have hm : 𝒳.val.val.p.IsHomLift ((Over.map V.hom).map t ≫ eqToHom hT') (z.map t).a :=
    inferInstance
  rw [← hWe a t (z.obj a).x (z.obj a).x (z.map t).a (z.map t).a hm hm]
  refine (InertiaPullback.liftsAut_iff_of_hom hF 𝒴.val.property (z.map t)).trans ?_
  rw [hbase a]

/-- **The base change of the lifting locus along a scheme-valued point is an open subspace.**
For `f` representable by algebraic spaces and unramified, the subfunctor of `yoneda V` that
`AlgebraicGeometry.Stack.LiftsAutomorphism` cuts out at a scheme-valued point of `𝒳 ×_𝒴 ℐ_𝒴`
with values in `V` is the subspace of **Stacks 03BZ** cut out by the open set of points of
`AlgebraicGeometry.Stack.exists_isOpen_liftsAutomorphism_iff`, hence an open subspace. -/
theorem isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_liftsAutomorphism
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hur : IsRelativelyUnramified B S hS f.hom) (V : BigFppfOver B S hS)
    (z : BigFppfOver B V.left.1 V.left.2 ⥤ (inertiaPullbackSquare B S hS f).pt.val.val.obj)
    (hz : z ⋙ (inertiaPullbackSquare B S hS f).pt.val.val.p = Over.map V.hom) :
    Space.IsOpenSubspace B V.left.1 V.left.2
      (fullSubcategoryBaseChangeSubfunctor (inertiaPullbackSquare B S hS f).pt
        (fun m h => liftsAutomorphism_of_hom B S hS f m h) z) := by
  obtain ⟨W, hW, hWe⟩ := exists_isOpen_liftsAutomorphism_iff B S hS f hrep hur z hz
  let W' : Set (Space.points B V.left.1 V.left.2
      (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) :=
    Space.pointsToScheme B V.left.1 V.left.2 (Over.mk (𝟙 V.left)) ⁻¹' W
  have hW' : @IsOpen _ (Space.pointTopology B V.left.1 V.left.2 _) W' := by
    let := Space.pointTopology B V.left.1 V.left.2
      (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    exact (Space.schemePointsHomeomorph B V.left.1 V.left.2 (Over.mk (𝟙 V.left))).continuous
      |>.isOpen_preimage _ hW
  have heq : fullSubcategoryBaseChangeSubfunctor (inertiaPullbackSquare B S hS f).pt
        (fun m h => liftsAutomorphism_of_hom B S hS f m h) z =
      Space.openSubspaceOfPoints B V.left.1 V.left.2
        (yoneda.obj (Over.mk (𝟙 V.left)) : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u) W' := by
    refine Subfunctor.ext (funext fun T => Set.ext fun x => ?_)
    rw [Space.mem_openSubspaceOfPoints_iff, yonedaEquiv_symm_eq_yoneda_map,
      Space.range_pointsMap_yoneda_subset_iff,
      Set.image_preimage_eq _ (Space.surjective_pointsToScheme B V.left.1 V.left.2 _)]
    exact hWe T.unop x
  rw [heq]
  exact Space.isOpenSubspace_openSubspaceOfPoints B V.left.1 V.left.2
    (isAlgebraicSpace_yoneda B V.left.1 V.left.2 (Over.mk (𝟙 V.left))) _ hW'

/-- **The open substack of `𝒳 ×_𝒴 ℐ_𝒴` on which the automorphism lifts.** For `f` representable
by algebraic spaces and unramified, the objects of `𝒳 ×_𝒴 ℐ_𝒴` whose automorphism lifts form an
open substack: this is the image `G ⊆ H` of the comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` in the proof of
**Stacks 0DUA**, which is an open immersion there. -/
noncomputable def liftsAutomorphismOpenSubstack
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f) :
    OpenSubstack (inertiaPullbackSquare B S hS f).pt :=
  openSubstackOfIsOpenSubspace B S hS (inertiaPullbackSquare B S hS f).pt
    (fun m h => liftsAutomorphism_of_hom B S hS f m h)
    (isOpenSubspace_fullSubcategoryBaseChangeSubfunctor_liftsAutomorphism B S hS f hf
      (isRelativelyUnramified_of_isUnramified B S hS f hf hu))

/-- A faithful 1-morphism of algebraic stacks is injective on vertical automorphism groups. -/
theorem injective_automorphismGroupMap
    (hfa : (CatFiberedInGroupoids.homFunctor f.hom).Faithful) (b : 𝒳.val.val.obj) :
    Function.Injective (automorphismGroupMap B S hS f b) := fun _ _ h =>
  Subtype.ext (Iso.ext ((CatFiberedInGroupoids.homFunctor f.hom).map_injective
    (congrArg (fun z => z.1.hom) h)))

/-- An automorphism lying over an identity is a vertical automorphism. -/
private theorem mem_verticalAut_of_isHomLift_id {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜]
    (p : 𝒜 ⥤ 𝒞) {R : 𝒞} {a : 𝒜} (τ : Aut a) (h : p.IsHomLift (𝟙 R) τ.hom) :
    τ ∈ p.verticalAut a := by
  rw [Functor.mem_verticalAut_iff, IsHomLift.fac' p (𝟙 R) τ.hom]
  simp

/-- A vertical automorphism lies over the identity of any base object its object lies over. -/
private theorem isHomLift_id_of_mem_verticalAut {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜]
    (p : 𝒜 ⥤ 𝒞) {R : 𝒞} {a : 𝒜} (ha : p.obj a = R) (σ : p.verticalAut a) :
    p.IsHomLift (𝟙 R) (σ : Aut a).hom := by
  subst ha
  refine IsHomLift.of_fac' p _ _ rfl rfl ?_
  rw [Functor.verticalAut.cond σ]
  simp

/-- A vertical endomorphism `β` of `f(b)` pulls back along `f(m)`, for `m` over `t`, to a vertical
endomorphism `β'` of `f(s)` with `β' ≫ f(m) = f(m) ≫ β`. -/
private theorem exists_isHomLift_comp_map_eq {V : BigFppfOver B S hS}
    {b s : 𝒳.val.val.obj} (t : V ⟶ 𝒳.val.val.p.obj b) (m : s ⟶ b)
    (hm : 𝒳.val.val.p.IsHomLift t m) (β : (CatFiberedInGroupoids.homFunctor f.hom).obj b ⟶
      (CatFiberedInGroupoids.homFunctor f.hom).obj b)
    (hβ : 𝒴.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj b)) β) :
    ∃ β' : (CatFiberedInGroupoids.homFunctor f.hom).obj s ⟶
        (CatFiberedInGroupoids.homFunctor f.hom).obj s,
      𝒴.val.val.p.IsHomLift (𝟙 V) β' ∧ β' ≫ (CatFiberedInGroupoids.homFunctor f.hom).map m =
        (CatFiberedInGroupoids.homFunctor f.hom).map m ≫ β := by
  have hFm : 𝒴.val.val.p.IsHomLift t ((CatFiberedInGroupoids.homFunctor f.hom).map m) :=
    Functor.isHomLift_map_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p f.hom) t m
  have _ : 𝒴.val.val.p.IsStronglyCartesian t ((CatFiberedInGroupoids.homFunctor f.hom).map m) :=
    𝒴.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  let F := CatFiberedInGroupoids.homFunctor f.hom
  exact ⟨Functor.IsCartesian.map 𝒴.val.val.p t (F.map m) (F.map m ≫ β), inferInstance,
    Functor.IsCartesian.fac _ t _ _⟩

/-- A vertical endomorphism `α` of `s₁` with `f(α) ≫ f(m₁) = f(m₁) ≫ β` gives a vertical
morphism `γ : s₁ ⟶ s₂` with `f(γ) ≫ f(m₂) = f(m₁) ≫ β`, for `m₁`, `m₂` over `t`. -/
private theorem exists_isHomLift_map_eq_of_map_comp_eq {V : BigFppfOver B S hS}
    {b s₁ s₂ : 𝒳.val.val.obj} (t : V ⟶ 𝒳.val.val.p.obj b) (m₁ : s₁ ⟶ b) (m₂ : s₂ ⟶ b)
    (hm₁ : 𝒳.val.val.p.IsHomLift t m₁) (hm₂ : 𝒳.val.val.p.IsHomLift t m₂)
    (β : (CatFiberedInGroupoids.homFunctor f.hom).obj b ⟶
      (CatFiberedInGroupoids.homFunctor f.hom).obj b)
    (α : s₁ ⟶ s₁) (hα : 𝒳.val.val.p.IsHomLift (𝟙 V) α)
    (hFα : (CatFiberedInGroupoids.homFunctor f.hom).map α ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map m₁ =
      (CatFiberedInGroupoids.homFunctor f.hom).map m₁ ≫ β) :
    ∃ γ : s₁ ⟶ s₂, 𝒳.val.val.p.IsHomLift (𝟙 V) γ ∧
      (CatFiberedInGroupoids.homFunctor f.hom).map γ ≫
          (CatFiberedInGroupoids.homFunctor f.hom).map m₂ =
        (CatFiberedInGroupoids.homFunctor f.hom).map m₁ ≫ β := by
  have _ : 𝒳.val.val.p.IsStronglyCartesian t m₂ :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift t m₂
  refine ⟨α ≫ Functor.IsCartesian.map 𝒳.val.val.p t m₂ m₁, ?_, ?_⟩
  · simpa using IsHomLift.comp 𝒳.val.val.p (𝟙 V) (𝟙 V) α
      (Functor.IsCartesian.map 𝒳.val.val.p t m₂ m₁)
  · rw [Functor.map_comp, Category.assoc, ← Functor.map_comp,
      Functor.IsCartesian.fac 𝒳.val.val.p t m₂ m₁, hFα]

/-- **A vertical automorphism lifts at an object over a field where the automorphism groups
agree.** Let `m₁ : s₁' ⟶ b`, `m₂ : s₂' ⟶ b` be pullbacks along `t : V ⟶ 𝒳.p b`, and let `β` be a
vertical automorphism of `f(b)`. If `f` induces a bijection of vertical automorphism groups at
`s₁'`, the pullback of `β` to `f(s₁')` is the image of a vertical automorphism `α` of `s₁'`, and
`α` followed by the comparison `s₁' ⟶ s₂'` lifts `β` along `m₁`, `m₂`. -/
theorem exists_lift_of_bijective_automorphismGroupMap {V : BigFppfOver B S hS}
    {b s₁' s₂' : 𝒳.val.val.obj} (t : V ⟶ 𝒳.val.val.p.obj b) (m₁ : s₁' ⟶ b) (m₂ : s₂' ⟶ b)
    (hm₁ : 𝒳.val.val.p.IsHomLift t m₁) (hm₂ : 𝒳.val.val.p.IsHomLift t m₂)
    (β : (CatFiberedInGroupoids.homFunctor f.hom).obj b ⟶
      (CatFiberedInGroupoids.homFunctor f.hom).obj b)
    (hβ : 𝒴.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj b)) β)
    (hbij : Function.Bijective (automorphismGroupMap B S hS f s₁')) :
    ∃ γ : s₁' ⟶ s₂', 𝒳.val.val.p.IsHomLift (𝟙 V) γ ∧
      (CatFiberedInGroupoids.homFunctor f.hom).map γ ≫
          (CatFiberedInGroupoids.homFunctor f.hom).map m₂ =
        (CatFiberedInGroupoids.homFunctor f.hom).map m₁ ≫ β := by
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  obtain ⟨β', hβ'v, hβ'⟩ := exists_isHomLift_comp_map_eq B S hS f t m₁ hm₁ β hβ
  have hV' : pX.obj s₁' = V := IsHomLift.domain_eq pX t m₁
  have _ : IsIso β' :=
    Functor.isIso_of_fiber_isGroupoid (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid V) β' hβ'v
  obtain ⟨α', hα'⟩ := hbij.2 ⟨asIso β', mem_verticalAut_of_isHomLift_id pY (asIso β') hβ'v⟩
  have hFα : F.map (α' : Aut s₁').hom = β' :=
    congrArg (fun z : pY.verticalAut (F.obj s₁') => (z : Aut (F.obj s₁')).hom) hα'
  exact exists_isHomLift_map_eq_of_map_comp_eq B S hS f t m₁ m₂ hm₁ hm₂ β _
    (isHomLift_id_of_mem_verticalAut pX hV' α') (by rw [hFα]; exact hβ')

/-- **The complement of the stabilizer-preserving locus is the image of the non-lifting locus.**
For `f` representable by algebraic spaces and unramified, a point `x ∈ |𝒳|` fails to be in the
locus of **Stacks 0DUA** exactly when it is the image of a point of `|𝒳 ×_𝒴 ℐ_𝒴|` outside the
open substack `AlgebraicGeometry.Stack.liftsAutomorphismOpenSubstack`: the complement of the
locus is the image of the closed set `|H| \ |G|` in the source's proof.

If `f` fails to induce an isomorphism at `x`, some vertical automorphism of `f(b)` at an object
`b` above a representative of `x` does not lift; by
`AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_isRelativelyUnramified` it already fails to
lift at a field-valued point of `b`, and that point, with its automorphism, is a field-valued
point of `𝒳 ×_𝒴 ℐ_𝒴` outside the open substack, by
`AlgebraicGeometry.Stack.prop_of_mem_pointSet_openSubstackOfIsOpenSubspace`. Conversely a point
outside the open substack carries a non-lifting automorphism at an object over a field, which
contradicts the condition of **Stacks 0DTW** at its image. -/
theorem compl_stabilizerPreservingLocus_eq_image
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f) :
    (stabilizerPreservingLocus B S hS f)ᶜ =
      AlgebraicStacks.pointsMap B S hS (inertiaPullbackSquare B S hS f).fst ''
        ((liftsAutomorphismOpenSubstack B S hS f hf hu).pointSet B S hS)ᶜ := by
  classical
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hp := 𝒳.val.isFiberedInGroupoids
  have hq := 𝒴.val.isFiberedInGroupoids
  have hur := isRelativelyUnramified_of_isUnramified B S hS f hf hu
  have hfa : F.Faithful :=
    AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hf
  ext x
  constructor
  · intro hx
    by_contra hcon
    apply hx
    refine (inducesIsomorphismAt_iff_forall_representatives B S hS f x).2 fun p hp' b m => ?_
    refine ⟨injective_automorphismGroupMap B S hS f hfa b, fun δ => ?_⟩
    have hδ := isHomLift_id_of_mem_verticalAut pY (Functor.congr_obj hF b) δ
    have hpt : ∀ (V : BigFppfOver B S hS), IsFieldObject B S hS V → ∀ (t : V ⟶ pX.obj b)
        (s₁' s₂' : 𝒳.val.val.obj) (m₁ : s₁' ⟶ b) (m₂ : s₂' ⟶ b),
        pX.IsHomLift t m₁ → pX.IsHomLift t m₂ →
        ∃ γ : s₁' ⟶ s₂', pX.IsHomLift (𝟙 V) γ ∧
          F.map γ ≫ F.map m₂ = F.map m₁ ≫ (δ : Aut (F.obj b)).hom := by
      intro V hV t s₁' s₂' m₁ m₂ hm₁ hm₂
      by_contra hno
      apply hcon
      obtain ⟨k, hk, ⟨e⟩⟩ := hV
      let : Field k := hk
      obtain ⟨δ', hδ'v, hδ'⟩ :=
        exists_isHomLift_comp_map_eq B S hS f t m₁ hm₁ (δ : Aut (F.obj b)).hom hδ
      have hV' : pX.obj s₁' = V := IsHomLift.domain_eq pX t m₁
      have _ : IsIso δ' := Functor.isIso_of_fiber_isGroupoid (hq.fiber_isGroupoid V) δ' hδ'v
      have hcond : pY.map δ' = 𝟙 (pY.obj (F.obj s₁')) :=
        (Functor.mem_verticalAut_iff pY (asIso δ')).1
          (mem_verticalAut_of_isHomLift_id pY (asIso δ') hδ'v)
      have hy : pY.obj (F.obj s₁') = V := (Functor.congr_obj hF s₁').trans hV'
      let A : RelativeInertia pY := { obj := F.obj s₁', auto := asIso δ', cond := hcond }
      let c' : InertiaPullback.Obj pX pY F :=
        { base := V, x := s₁', y := A, hx := hV', hy := hy, iso := Iso.refl _,
          vertical := IsHomLift.id hy }
      have hnl : ¬ InertiaPullback.LiftsAut c' := by
        rintro ⟨β', hβ', hβ'eq⟩
        have hFβ' : F.map β' = δ' := by
          rw [hβ'eq]
          exact (Category.id_comp _).trans (Category.comp_id _)
        exact hno (exists_isHomLift_map_eq_of_map_comp_eq B S hS f t m₁ m₂ hm₁ hm₂ _ β' hβ'
          (by rw [hFβ']; exact hδ'))
      let qc : FieldValuedPoint B S hS (inertiaPullbackSquare B S hS f).pt.val.val :=
        { carrier := k, field := hk, base := V, isSpec := e, obj := c', «over» := rfl }
      refine ⟨pointClass B S hS _ _ qc, fun hmem => hnl ?_, ?_⟩
      · exact prop_of_mem_pointSet_openSubstackOfIsOpenSubspace B S hS _
          (fun m h => liftsAutomorphism_of_hom B S hS f m h) _ qc hmem
      · rw [← hp']
        refine (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property _ _).2
          ⟨fieldValuedPointMap B S hS _ (inertiaPullbackSquare B S hS f).fst.hom.hom qc,
            ⟨𝟙 _⟩, ⟨(m₁ ≫ m : s₁' ⟶ p.obj)⟩⟩
    obtain ⟨γ, hγ, hFγ⟩ := exists_isHomLift_map_eq_of_isRelativelyUnramified B S hS f.hom hf hur
      (s₁ := b) (s₂ := b) rfl rfl (δ : Aut (F.obj b)).hom hδ hpt
    have _ : IsIso γ := Functor.isIso_of_fiber_isGroupoid (hp.fiber_isGroupoid _) γ hγ
    exact ⟨⟨asIso γ, mem_verticalAut_of_isHomLift_id pX (asIso γ) hγ⟩,
      Subtype.ext (Iso.ext hFγ)⟩
  · rintro ⟨h, hh, rfl⟩ hx
    induction h using Quotient.inductionOn with
    | h q =>
      apply hh
      refine (OpenSubstack.mem_pointSet_iff B S hS _ _).2 ⟨q, ?_, rfl⟩
      have hbij := (inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 hx
        (fieldValuedPointMap B S hS _ (inertiaPullbackSquare B S hS f).fst.hom.hom q) rfl
        q.obj.x (𝟙 _)
      let c : InertiaPullback.Obj pX pY F := q.obj
      obtain ⟨α, hα⟩ := hbij.2 ⟨InertiaPullback.isoY c ≪≫ c.y.auto ≪≫ (InertiaPullback.isoY c).symm,
        mem_verticalAut_of_isHomLift_id pY _ (InertiaPullback.isHomLift_aut c)⟩
      have hFα : F.map (α : Aut c.x).hom = InertiaPullback.aut c :=
        congrArg (fun z : pY.verticalAut (F.obj c.x) => (z : Aut (F.obj c.x)).hom) hα
      exact ⟨(α : Aut c.x).hom, isHomLift_id_of_mem_verticalAut pX c.hx α, hFα⟩

/-- **Stacks 0DUA, openness of the stabilizer-preserving locus.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S` which is representable by algebraic spaces and
unramified, and assume the inertia `ℐ_𝒴 ⟶ 𝒴` is proper. Then the set of `x ∈ |𝒳|` at which `f`
induces an isomorphism between the automorphism groups at `x` and at `f(x)` is open.

Its complement is the image of the complement of the open substack
`AlgebraicGeometry.Stack.liftsAutomorphismOpenSubstack` of `𝒳 ×_𝒴 ℐ_𝒴`
(`AlgebraicGeometry.Stack.compl_stabilizerPreservingLocus_eq_image`), and the projection
`𝒳 ×_𝒴 ℐ_𝒴 ⟶ 𝒳` is a base change of the proper `ℐ_𝒴 ⟶ 𝒴`, hence closed on points. -/
theorem isOpen_stabilizerPreservingLocus
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f)
    (hI : AlgebraicStacks.IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴)) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (stabilizerPreservingLocus B S hS f) := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (inertiaPullbackSquare B S hS f).pt.val
  rw [← isClosed_compl_iff, compl_stabilizerPreservingLocus_eq_image B S hS f hf hu]
  exact hI.2.2 𝒳 f _ (OpenSubstack.isOpen_pointSet B S hS
    (liftsAutomorphismOpenSubstack B S hS f hf hu)).isClosed_compl

/-- **An object of `𝒳` mapping to an object of an open substack lies in it.** The full
subcategory of an open substack is fibred in groupoids, so a morphism `m : b ⟶ x` of `𝒳` into an
object `x` of the substack has a lift `b' ⟶ x` inside the substack over the same morphism of the
site; both are cartesian in `𝒳`, so `b ≅ b'`, and the substack is strictly full. -/
theorem OpenSubstack.prop_of_hom (U : OpenSubstack 𝒳) {b x : 𝒳.val.val.obj} (m : b ⟶ x)
    (hx : U.property x) : U.property b := by
  have hU := U.isAlgebraic.1
  have hp := 𝒳.val.isFiberedInGroupoids
  have _ := U.strictlyFull
  obtain ⟨b', m', hm'⟩ := hU.exists_lift (𝒳.val.val.p.map m) (⟨x, hx⟩ : U.property.FullSubcategory)
    rfl
  have h₁ : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map m) m'.hom :=
    Functor.isHomLift_map_of_comp_eq (p := (fullSubcategoryBased 𝒳 U.property).p)
      (q := 𝒳.val.val.p) (G := U.property.ι) rfl _ m'
  have h₂ : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map m) m := IsHomLift.map _ m
  have _ : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map m) m'.hom :=
    hp.isStronglyCartesian_homLift _ _
  have _ : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map m) m :=
    hp.isStronglyCartesian_homLift _ _
  exact U.property.prop_of_iso
    (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map m) m'.hom m).symm
    b'.property

/-- **The inertia comparison on an open substack cut out by the locus is an isomorphism.** Let
`f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces and unramified, and let `𝒰 ⊆ 𝒳` be an open
substack whose set of points is the stabilizer-preserving locus. Then the restriction
`𝒰 ⟶ 𝒴` of `f` is stabilizer preserving: `ℐ_𝒰 ⟶ 𝒰 ×_𝒴 ℐ_𝒴` is an isomorphism.

This is the source's application of **Stacks 0DU9** to `𝒰 ⟶ 𝒴`, carried out directly: the
restriction is faithful, and a vertical automorphism of `f(x)` for `x` in `𝒰` lifts because it
lifts at every field-valued point of `x` — such a point lies in `𝒰`
(`AlgebraicGeometry.Stack.OpenSubstack.prop_of_hom`), hence in the locus, and the automorphism
lifts there by `AlgebraicGeometry.Stack.exists_lift_of_bijective_automorphismGroupMap` — and `f`
is representable and unramified
(`AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_isRelativelyUnramified`). -/
theorem isStabilizerPreserving_openSubstack_inclusion_comp
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f)
    (U : OpenSubstack 𝒳) (hU : U.pointSet B S hS = stabilizerPreservingLocus B S hS f) :
    IsStabilizerPreserving B S hS (U.inclusion ≫ f) := by
  classical
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hp := 𝒳.val.isFiberedInGroupoids
  have hur := isRelativelyUnramified_of_isUnramified B S hS f hf hu
  have hfa : F.Faithful :=
    AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hf
  let pU := U.toAlgebraicStack.val.val.p
  let F' := CatFiberedInGroupoids.homFunctor (U.inclusion ≫ f).hom
  have hF' : F' ⋙ pY = pU := CatFiberedInGroupoids.homFunctor_comp_p (U.inclusion ≫ f).hom
  have hfa' : F'.Faithful := by
    show (U.property.ι ⋙ F).Faithful
    infer_instance
  refine nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts pU pY F' hF'
    (fun A B m hm => F'.map_injective (by rw [F'.map_comp, F'.map_comp]; exact hm)) ?_
  intro x β hβ
  have hxb : pY.obj (F.obj x.obj) = pX.obj x.obj := Functor.congr_obj hF x.obj
  have hβ₀ : pY.IsHomLift (𝟙 (pY.obj (F.obj x.obj))) β.hom := by
    have h := IsHomLift.map pY β.hom
    rwa [hβ] at h
  have hβ' : pY.IsHomLift (𝟙 (pX.obj x.obj)) β.hom := by rwa [← hxb]
  have hpt : ∀ (V : BigFppfOver B S hS), IsFieldObject B S hS V → ∀ (t : V ⟶ pX.obj x.obj)
      (s₁' s₂' : 𝒳.val.val.obj) (m₁ : s₁' ⟶ x.obj) (m₂ : s₂' ⟶ x.obj),
      pX.IsHomLift t m₁ → pX.IsHomLift t m₂ →
      ∃ γ : s₁' ⟶ s₂', pX.IsHomLift (𝟙 V) γ ∧ F.map γ ≫ F.map m₂ = F.map m₁ ≫ β.hom := by
    intro V hV t s₁' s₂' m₁ m₂ hm₁ hm₂
    obtain ⟨k, hk, ⟨e⟩⟩ := hV
    let : Field k := hk
    let q : FieldValuedPoint B S hS 𝒳.val.val :=
      { carrier := k, field := hk, base := V, isSpec := e, obj := s₁',
        «over» := IsHomLift.domain_eq pX t m₁ }
    have hmem : pointClass B S hS 𝒳.val.val 𝒳.val.property q ∈ U.pointSet B S hS :=
      (OpenSubstack.mem_pointSet_iff B S hS U _).2
        ⟨q, OpenSubstack.prop_of_hom B S hS U m₁ x.property, rfl⟩
    rw [hU] at hmem
    exact exists_lift_of_bijective_automorphismGroupMap B S hS f t m₁ m₂ hm₁ hm₂ β.hom hβ'
      ((inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 hmem q rfl s₁' (𝟙 _))
  obtain ⟨γ, hγ, hFγ⟩ := exists_isHomLift_map_eq_of_isRelativelyUnramified B S hS f.hom hf hur
    (s₁ := x.obj) (s₂ := x.obj) rfl rfl β.hom hβ' hpt
  have _ : IsIso γ := Functor.isIso_of_fiber_isGroupoid (hp.fiber_isGroupoid _) γ hγ
  refine ⟨ObjectProperty.isoMk _ (asIso γ), ?_, hFγ⟩
  show pX.map γ = _
  rw [IsHomLift.fac' pX (𝟙 (pX.obj x.obj)) γ]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- **Stacks 0DUA.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces and unramified, and assume the inertia `ℐ_𝒴 ⟶ 𝒴` is proper.
Then the set of `x ∈ |𝒳|` at which `f` induces an isomorphism between the automorphism groups
at `x` and at `f(x)` (**Stacks 0DTW**) is open; there is an open substack `𝒰 ⊆ 𝒳` with that set
of points (**Stacks 06FJ**); and for every open substack `𝒰 ⊆ 𝒳` with that set of points, the
canonical comparison `ℐ_𝒰 ⟶ 𝒰 ×_𝒴 ℐ_𝒴` of **Stacks 06R5** is an isomorphism. -/
@[stacks 0DUA]
theorem exists_openSubstack_isStabilizerPreserving
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hu : IsUnramified B S hS f)
    (hI : AlgebraicStacks.IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴)) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (stabilizerPreservingLocus B S hS f) ∧
      (∃ U : OpenSubstack 𝒳, U.pointSet B S hS = stabilizerPreservingLocus B S hS f) ∧
        ∀ U : OpenSubstack 𝒳, U.pointSet B S hS = stabilizerPreservingLocus B S hS f →
          IsStabilizerPreserving B S hS (U.inclusion ≫ f) :=
  have hΩ := isOpen_stabilizerPreservingLocus B S hS f hf hu hI
  ⟨hΩ, exists_openSubstack_pointSet_eq B S hS 𝒳 _ hΩ,
    fun U hU => isStabilizerPreserving_openSubstack_inclusion_comp B S hS f hf hu U hU⟩

end InertiaPullback

end AlgebraicGeometry.Stack

end
