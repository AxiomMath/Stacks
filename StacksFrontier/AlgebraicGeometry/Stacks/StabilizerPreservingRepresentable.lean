module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange

/-!
# Stabilizer preserving morphisms are representable by algebraic spaces (Stacks 0DU7)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. Following the literature, `f` is *stabilizer preserving* (or
*fixed-point reflecting*) when the canonical comparison
`ℐ_𝒳 ⟶ ℐ_𝒴 ×_𝒴 𝒳` of Stacks 06R5 (`CategoryTheory.inertiaPullbackComparison`) from the inertia
of `𝒳` to the pullback of the inertia of `𝒴` is an isomorphism. **Stacks 0DU7** says that such
an `f` is representable by algebraic spaces, and its proof is "immediate from Stacks 04YY".

This file proves it. A stabilizer preserving `f` satisfies condition (4) of Stacks 04YY — the
kernel of every induced map on automorphism groups is trivial — hence is faithful, and a faithful
1-morphism of algebraic stacks is representable by algebraic spaces (Stacks 04Y5, the
implication (2) ⟹ (3), which is the implication (3) ⟹ (1) of Stacks 04YY:
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`). The same
hypothesis also gives conditions (2) and (3) of Stacks 04YY, which are recorded here as well.

## Main results

* `CategoryTheory.eq_id_of_map_eq_id_of_inertiaPullbackComparison_full`: the content of the
  reduction, with no geometry. For a 1-morphism `F` of categories over `C` whose source is
  fibred in groupoids and whose inertia comparison is full, an endomorphism of an object of the
  source killed by `F` is an identity.
* `AlgebraicGeometry.Stack.faithful_homFunctor_of_inertiaPullbackComparison_full`: such an `F` is
  faithful, for a 1-morphism of categories fibred in groupoids over the big fppf site.
* `isRepresentableByAlgebraicSpaces_of_inertiaPullbackComparison_isEquivalence` (namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`): **Stacks 0DU7** — a stabilizer preserving
  1-morphism of algebraic stacks is representable by algebraic spaces.
* `isRepresentableByAlgebraicSpaces_of_isStabilizerPreserving` (same namespace): the same
  conclusion for the rendering `AlgebraicGeometry.Stack.IsStabilizerPreserving` of the
  hypothesis as an equivalence over the site.
* `relativeInertiaTrivial_of_inertiaPullbackComparison_isEquivalence` and
  `isEquivalence_secondRelativeDiagonal_of_inertiaPullbackComparison_isEquivalence` (same
  namespace): conditions (3) and (2) of Stacks 04YY for a stabilizer preserving 1-morphism.

## Implementation notes

Only *fullness* of the comparison is used, so the hypothesis is weaker than an isomorphism and
the statements are correspondingly stronger; the geometric results take the isomorphism of the
source, in the form `CategoryTheory.Functor.IsEquivalence` of the comparison functor already used
by `StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreserving` for Stacks 0DUB.

The argument is the one the source's one-line proof contracts. An endomorphism `a` of an object
`x` of `𝒳` with `f a = 𝟙` lies over an identity of the site, hence is an automorphism because the
fibres of `𝒳` are groupoids; so `(x, 𝟙)` and `(x, a)` are two objects of `ℐ_𝒳`, and `𝟙 x`
conjugates the image of the second into the image of the first. A full comparison reflects that
conjugation (`CategoryTheory.inertiaPullbackComparison_reflects_comm`), which says exactly
`𝟙 ≫ a = 𝟙 ≫ 𝟙`, that is, `a = 𝟙`. This is condition (4) of Stacks 04YY, which is faithfulness
of `f` (Stacks 04Y5 (2)).

The fullness hypothesis is taken as an explicit argument rather than as an instance: the
comparison functor mentions the proof `hF` that `f` is a 1-morphism over the site, and keyed
instance search on a functor carrying a propositional argument is unreliable.

The universes are those of the 2-category of algebraic stacks — morphism universe `u`, object
universe `u + 1` — because `AlgebraicGeometry.Stack.secondRelativeDiagonal` and
`AlgebraicGeometry.Stack.relativeInertiaNeutralSection` are stated there.

## References

* [Stacks Project, Tag 0DU7](https://stacks.math.columbia.edu/tag/0DU7)
* [Stacks Project, Tag 04YY](https://stacks.math.columbia.edu/tag/04YY)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe uC vC uX vX uY vY

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y]

/-- **The content of Stacks 0DU7, without geometry.** Let `pX : X ⥤ C` be fibred in groupoids,
let `pY : Y ⥤ C` be a category over `C` and let `F : X ⥤ Y` be a 1-morphism over `C` whose
inertia comparison `ℐ_X ⥤ ℐ_Y ×_Y X` is full. Then every endomorphism of an object of `X` which
`F` sends to an identity is itself an identity.

Such an endomorphism `a` of `x` lies over an identity of `C`, hence is an automorphism, so
`(x, 𝟙)` and `(x, a)` are objects of `ℐ_X`; the identity of `x` conjugates the image of the one
into the image of the other, and a full comparison reflects that conjugation. -/
theorem eq_id_of_map_eq_id_of_inertiaPullbackComparison_full (pX : X ⥤ C) (pY : Y ⥤ C)
    (F : X ⥤ Y) (hF : F ⋙ pY = pX) (hX : pX.IsFiberedInGroupoids)
    (hfull : (inertiaPullbackComparison pX pY F hF).Full) {x : X} (a : x ⟶ x)
    (ha : F.map a = 𝟙 (F.obj x)) : a = 𝟙 x := by
  have := hfull
  have hv : pX.map a = 𝟙 (pX.obj x) := RelativeInertia.map_eq_id_of_comp_eq hF a ha
  have hlift : pX.IsHomLift (𝟙 (pX.obj x)) a :=
    IsHomLift.of_fac' pX _ a rfl rfl (by simpa using hv)
  have : IsIso a :=
    Functor.isIso_of_fiber_isGroupoid (hX.fiber_isGroupoid (pX.obj x)) a hlift
  let A : RelativeInertia pX := ⟨x, Iso.refl x, by simp⟩
  let B : RelativeInertia pX := ⟨x, asIso a, hv⟩
  have hm : F.map (𝟙 x) ≫ F.map B.auto.hom = F.map A.auto.hom ≫ F.map (𝟙 x) := by
    simp [A, B, ha]
  have hcomm := inertiaPullbackComparison_reflects_comm pX pY F hF A B (𝟙 x) hm
  simpa [A, B] using hcomm

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FibredInGroupoids

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Condition (4) of Stacks 04YY from a full inertia comparison.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` whose inertia
comparison is full, every endomorphism of an object of `𝒳` which `f` sends to an identity is an
identity. -/
theorem isomKernel_trivial_of_inertiaPullbackComparison_full (f : 𝒳 ⟶ 𝒴)
    (hfull : (CategoryTheory.inertiaPullbackComparison 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f)).Full) (x : 𝒳.val.obj) (a : x ⟶ x)
    (ha : (CatFiberedInGroupoids.homFunctor f).map a = 𝟙 _) : a = 𝟙 x :=
  CategoryTheory.eq_id_of_map_eq_id_of_inertiaPullbackComparison_full 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f)
    𝒳.isFiberedInGroupoids hfull a ha

/-- **Condition (2) of Stacks 04Y5 from a full inertia comparison.** A 1-morphism of categories
fibred in groupoids over the big fppf site of `S` whose inertia comparison is full has faithful
underlying functor. -/
theorem faithful_homFunctor_of_inertiaPullbackComparison_full (f : 𝒳 ⟶ 𝒴)
    (hfull : (CategoryTheory.inertiaPullbackComparison 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f)).Full) :
    (CatFiberedInGroupoids.homFunctor f).Faithful :=
  (Functor.IsFiberedInGroupoids.faithful_iff_autKernel_trivial 𝒳.isFiberedInGroupoids
      𝒴.isFiberedInGroupoids f.hom.w).mpr
    (isomKernel_trivial_of_inertiaPullbackComparison_full B S hS f hfull)

end FibredInGroupoids

namespace AlgebraicStacks

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Condition (3) of Stacks 04YY for a stabilizer preserving morphism.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S` which is stabilizer preserving, that is, whose canonical
comparison `ℐ_𝒳 ⟶ ℐ_𝒴 ×_𝒴 𝒳` of Stacks 06R5 is an isomorphism. Then the relative inertia group
stack `ℐ_{𝒳/𝒴}` is trivial over `𝒳`, that is, its neutral section `e : 𝒳 ⟶ ℐ_{𝒳/𝒴}` is an
isomorphism. -/
theorem relativeInertiaTrivial_of_inertiaPullbackComparison_isEquivalence (f : 𝒳 ⟶ 𝒴)
    (hf : (CategoryTheory.inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).IsEquivalence) :
    Functor.IsEquivalence (relativeInertiaStackNeutralSection B S hS f).hom.hom.toFunctor := by
  have := hf
  exact (relativeInertiaTrivial_iff_isomKernel_trivial B S hS f).mpr
    (isomKernel_trivial_of_inertiaPullbackComparison_full B S hS f.hom inferInstance)

/-- **Condition (2) of Stacks 04YY for a stabilizer preserving morphism.** The second diagonal
`Δ_{f, 2}` of a stabilizer preserving 1-morphism of algebraic stacks over `S` is an isomorphism.

This is the previous result composed with the equivalence of conditions (2) and (3) of
Stacks 04YY. -/
theorem isEquivalence_secondRelativeDiagonal_of_inertiaPullbackComparison_isEquivalence
    (f : 𝒳 ⟶ 𝒴)
    (hf : (CategoryTheory.inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).IsEquivalence) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor :=
  (isEquivalence_secondRelativeDiagonal_iff_relativeInertiaTrivial B S hS f).mpr
    (relativeInertiaTrivial_of_inertiaPullbackComparison_isEquivalence B S hS f hf)

/-- **Stacks 0DU7.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If the
canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of Stacks 06R5 is an isomorphism, then `f` is
representable by algebraic spaces.

The comparison makes `f` faithful
(`AlgebraicGeometry.Stack.faithful_homFunctor_of_inertiaPullbackComparison_full`, condition (4)
of Stacks 04YY), and a faithful 1-morphism of algebraic stacks is representable by algebraic
spaces (Stacks 04Y5, the implication (2) ⟹ (3)). -/
@[stacks 0DU7]
theorem isRepresentableByAlgebraicSpaces_of_inertiaPullbackComparison_isEquivalence
    (f : 𝒳 ⟶ 𝒴)
    (hf : (CategoryTheory.inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).IsEquivalence) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom := by
  have := hf
  exact isRepresentableByAlgebraicSpaces_of_faithful B S hS f
    (faithful_homFunctor_of_inertiaPullbackComparison_full B S hS f.hom inferInstance)

/-- **Stacks 0DU7, for the comparison read as an equivalence over the site.** A 1-morphism of
algebraic stacks over `S` which is stabilizer preserving in the sense of
`AlgebraicGeometry.Stack.IsStabilizerPreserving` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_of_isStabilizerPreserving (f : 𝒳 ⟶ 𝒴)
    (hf : IsStabilizerPreserving B S hS f) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_inertiaPullbackComparison_isEquivalence B S hS f
    hf.some.isEquivalence

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
