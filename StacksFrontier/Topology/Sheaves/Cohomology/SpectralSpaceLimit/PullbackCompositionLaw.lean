module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.PullbackAsAMorphismOfDeltaFunctors

/-!
# Acting by an exact functor on `Ext` is functorial in the exact functor

`ModuleSheafCohomology.extMapExactHom` makes acting by one exact functor a morphism of
δ-functors.  This file proves that this action is functorial in the exact functor, and the
resulting composition law for `Stacks.Cohomology.AbelianColimit.H'pullbackHom`: `H'pullbackHom`
of a composite map of corepresenting objects is the composite of the two `H'pullbackHom`s.

## Why it is not a Mathlib lemma, and why universality supplies it

Mathlib has `CategoryTheory.Abelian.Ext.mapExactFunctor` compatible with `Ext`-composition
(`…_comp`), with `Ext.mk₀` (`…_mk₀`), with the `Ext`-class of a short exact sequence
(`…_extClass`), with `0` and with `+`.  It does **not** have the composition law in the functor
variable, `Ext.mapExactFunctor (Ψ ⋙ Ψ') = Ext.mapExactFunctor Ψ' ∘ Ext.mapExactFunctor Ψ`, and
that law is not reachable from the ones it has: a general class `e : Ext X Y n` is not a
composite of `Ext.mk₀`s and `Ext`-classes, so there is nothing to induct on.  Working from the
definition means comparing `LocalizerMorphism.smallShiftedHomMap` of a composite against the
composite, across `Functor.mapDerivedCategory` of a composite, which is only *isomorphic* to the
composite of the `mapDerivedCategory`s.

The route taken here avoids all of that.  Both sides are morphisms of δ-functors out of
`ModuleSheafCohomology.extDeltaFunctor (𝟭 A) X`, which is **universal** — `Ext` out of anything
against an injective object vanishes in positive degree
(`CategoryTheory.Abelian.Ext.eq_zero_of_injective`), so
`ModuleSheafCohomology.extDeltaFunctor_isUniversal` applies — and a morphism out of a universal
δ-functor is determined by its degree-zero part
(`CategoryTheory.DeltaFunctor.IsUniversal.hom_ext_zero`).  In degree zero every class *is* an
`Ext.mk₀` (`CategoryTheory.Abelian.Ext.homEquiv₀`), so `Ext.mapExactFunctor_mk₀` finishes, the
remaining step being `(Ψ ⋙ Ψ').map f = Ψ'.map (Ψ.map f)`, which is `rfl`.  The degree-`n`
component of the resulting equality of δ-functor morphisms, read at an arbitrary object and
applied to an arbitrary class, is the pointwise law in full generality.

The identity law is the same argument with `Ψ = 𝟭 A`.

## Main results

* `ModuleSheafCohomology.extMapExactHom_comp` and `…_id`: **acting by an exact functor on `Ext` is
  functorial in the exact functor**, as an identity of morphisms of δ-functors.
* `ModuleSheafCohomology.mapExactFunctor_comp_exactFunctor` and `…mapExactFunctor_id`: the same
  two laws pointwise, at an arbitrary degree and an arbitrary class.  These are the statements
  Mathlib is missing.
* `ModuleSheafCohomology.extPullbackHom_comp`: **the composition law for the comparison across an
  exact functor**: `extPullbackHom` of the composite map of corepresenting objects
  `ρ' ≫ Ψ'.map ρ` is `extPullbackHom` of `ρ` followed by acting with `Ψ'` and precomposing with
  `ρ'`.  Unlike the two laws above this needs no universality: in every degree both sides are
  explicit `Ext`-composites, and the proof is the pointwise composition law together with
  associativity (`CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc`).
* `Stacks.Cohomology.AbelianColimit.H'pullbackHom_comp`: the same law at the native-cohomology
  spelling, which is the statement the stage side of the degree induction consumes.
* `ModuleSheafCohomology.mk₀_id_ne_zero` and
  `ModuleSheafCohomology.mapExactFunctor_comp_exactFunctor_ne_zero`: **the composition law is not
  an equation between zeros** — at the identity of an object with non-zero image both sides are
  non-zero `Ext`-classes.

## Implementation notes

`extMapExactHom_comp` needs the two type equalities `(F ⋙ Ψ) ⋙ Ψ' = F ⋙ (Ψ ⋙ Ψ')` and
`𝟭 A ⋙ Ψ = Ψ`, and the object equality `(Ψ ⋙ Ψ').obj X = Ψ'.obj (Ψ.obj X)`; all three are `rfl`,
so the statement typechecks with no `eqToHom` and nothing is paid for them.

`extDeltaFunctorPrecomp` is stated with `HasExt.{v}` at the same universe as the morphisms, so
`extPullbackHom_comp` and the native-cohomology law are at the diagonal universes, as
`extPullbackHom` itself already is.  The two laws proved by universality are not, and are stated
with `HasExt.{w}` for a free `w` and three independent category universes.

These declarations are a step of the proof of [Stacks, Tag 0A37], not a clause of its statement,
and carry no tag.

## References

* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

namespace ModuleSheafCohomology

/-! ### Functoriality in the exact functor, by universality -/

section NonZeroClass

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- **The degree-zero `Ext`-class of an identity is non-zero exactly when the object is.**
`CategoryTheory.Abelian.Ext.mk₀` is a bijection in degree zero
(`CategoryTheory.Abelian.Ext.mk₀_bijective`), so it carries `𝟙 X ≠ 0` across, and `𝟙 X ≠ 0` is
`CategoryTheory.Limits.IsZero.iff_id_eq_zero`.  This is what makes the functoriality laws below
equations between non-zero classes rather than between zeros. -/
theorem mk₀_id_ne_zero {X : A} (hX : ¬ IsZero X) : Ext.mk₀ (𝟙 X) ≠ (0 : Ext.{w} X X 0) := by
  intro h
  refine hX ((IsZero.iff_id_eq_zero X).2 ((Ext.mk₀_bijective X X).1 ?_))
  rw [h, Ext.mk₀_zero]

end NonZeroClass

section MapExactFunctorial

universe w v v' v'' u u' u''

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]
  {A' : Type u'} [Category.{v'} A'] [Abelian A'] [HasExt.{w} A']
  {A'' : Type u''} [Category.{v''} A''] [Abelian A''] [HasExt.{w} A'']

/-- `ModuleSheafCohomology.extDeltaFunctor (𝟭 A) X` is a universal δ-functor: `Ext` out of `X`
against an injective object vanishes in positive degree. -/
theorem extDeltaFunctor_id_isUniversal (X : A) :
    (extDeltaFunctor (𝟭 A) X).IsUniversal :=
  extDeltaFunctor_isUniversal (𝟭 A) X fun _ _ _ e => Ext.eq_zero_of_injective e

/-- Two morphisms of δ-functors out of `extDeltaFunctor (𝟭 A) X` agree once they agree on the
degree-zero classes `Ext.mk₀ f`. -/
private theorem extDeltaFunctor_id_hom_ext {X : A} {D : DeltaFunctor A Ab.{w}}
    {z z' : extDeltaFunctor (𝟭 A) X ⟶ D}
    (h : ∀ {G : A} (f : X ⟶ G), AddCommGrpCat.Hom.hom ((z.app 0).app G) (Ext.mk₀ f) =
      AddCommGrpCat.Hom.hom ((z'.app 0).app G) (Ext.mk₀ f)) : z = z' := by
  have := extDeltaFunctor_id_isUniversal (A := A) X
  refine DeltaFunctor.IsUniversal.hom_ext_zero _ ?_
  ext G (e : Ext X G 0)
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X G).2 e
  exact h f

/-- **Acting by an exact functor on `Ext`-classes is functorial in the exact functor**, as an
identity of morphisms of δ-functors out of `extDeltaFunctor (𝟭 A) X`.

Both sides are morphisms out of a universal δ-functor, so they agree as soon as they agree in
degree zero, where every class is an `Ext.mk₀` and the claim is
`(Ψ ⋙ Ψ').map f = Ψ'.map (Ψ.map f)`. -/
theorem extMapExactHom_comp (Ψ : A ⥤ A') [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (Ψ' : A' ⥤ A'') [Ψ'.Additive] [PreservesFiniteLimits Ψ']
    [PreservesFiniteColimits Ψ'] (X : A) :
    extMapExactHom (𝟭 A) (Ψ ⋙ Ψ') X =
      extMapExactHom (𝟭 A) Ψ X ≫ extMapExactHom Ψ Ψ' (Ψ.obj X) := by
  refine extDeltaFunctor_id_hom_ext fun f => ?_
  change Ext.mapExactFunctor (Ψ ⋙ Ψ') (Ext.mk₀ f) =
    Ext.mapExactFunctor Ψ' (Ext.mapExactFunctor Ψ (Ext.mk₀ f))
  rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  rfl

/-- **Acting by the identity functor on `Ext`-classes is the identity**, as an identity of
morphisms of δ-functors.  The same argument as `extMapExactHom_comp`. -/
theorem extMapExactHom_id (X : A) :
    extMapExactHom (𝟭 A) (𝟭 A) X = 𝟙 (extDeltaFunctor (𝟭 A) X) := by
  refine extDeltaFunctor_id_hom_ext fun f => ?_
  change Ext.mapExactFunctor (𝟭 A) (Ext.mk₀ f) = Ext.mk₀ f
  rw [Ext.mapExactFunctor_mk₀]
  rfl

/-- **`Ext.mapExactFunctor` is functorial in the exact functor**, pointwise, at an arbitrary
degree and an arbitrary class.  This is the law Mathlib does not have: its
`CategoryTheory.Abelian.Ext.mapExactFunctor_comp` is compatibility with composition of
`Ext`-classes, not with composition of the functors.

It is the degree-`n` component of `extMapExactHom_comp`, read at the object `Y`. -/
theorem mapExactFunctor_comp_exactFunctor (Ψ : A ⥤ A') [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (Ψ' : A' ⥤ A'') [Ψ'.Additive] [PreservesFiniteLimits Ψ']
    [PreservesFiniteColimits Ψ'] {X Y : A} {n : ℕ} (e : Ext.{w} X Y n) :
    e.mapExactFunctor (Ψ ⋙ Ψ') = (e.mapExactFunctor Ψ).mapExactFunctor Ψ' :=
  congrArg (fun z : extDeltaFunctor (𝟭 A) X ⟶ extDeltaFunctor (Ψ ⋙ Ψ') ((Ψ ⋙ Ψ').obj X) =>
    AddCommGrpCat.Hom.hom ((z.app n).app Y) e) (extMapExactHom_comp Ψ Ψ' X)

/-- **Acting by the identity functor on an `Ext`-class is the identity**, pointwise.  The
degree-`n` component of `extMapExactHom_id`, read at the object `Y`. -/
theorem mapExactFunctor_id {X Y : A} {n : ℕ} (e : Ext.{w} X Y n) :
    e.mapExactFunctor (𝟭 A) = e :=
  congrArg (fun z : extDeltaFunctor (𝟭 A) X ⟶ extDeltaFunctor (𝟭 A) ((𝟭 A).obj X) =>
    AddCommGrpCat.Hom.hom ((z.app n).app Y) e) (extMapExactHom_id (A := A) X)

/-! #### Non-degeneracy

An equation between maps is worthless if both sides are zero for every input, so the two laws
above are instantiated here at a class that is provably **not** zero. -/

/-- **The two functoriality laws are non-degenerate.**  At the identity of an object whose image
is not a zero object, both sides of `mapExactFunctor_comp_exactFunctor` are the degree-zero class
of an identity, hence **non-zero** — so the law is not an identity between zeros.  The same
instance of `mapExactFunctor_id` is non-zero for the same reason.

This is the positive test, not an argument: the hypothesis `¬ IsZero (Ψ'.obj (Ψ.obj X))` is
satisfied in every application, since the exact functors of [Stacks, Tag 0A37] are inverse images
of abelian sheaves, which carry a non-zero sheaf to a non-zero sheaf. -/
theorem mapExactFunctor_comp_exactFunctor_ne_zero (Ψ : A ⥤ A') [Ψ.Additive]
    [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (Ψ' : A' ⥤ A'') [Ψ'.Additive]
    [PreservesFiniteLimits Ψ'] [PreservesFiniteColimits Ψ'] {X : A}
    (h : ¬ IsZero (Ψ'.obj (Ψ.obj X))) :
    (Ext.mk₀ (𝟙 X)).mapExactFunctor (Ψ ⋙ Ψ') ≠ 0 ∧
      (Ext.mk₀ (𝟙 X)).mapExactFunctor (Ψ ⋙ Ψ') =
        ((Ext.mk₀ (𝟙 X)).mapExactFunctor Ψ).mapExactFunctor Ψ' := by
  refine ⟨?_, mapExactFunctor_comp_exactFunctor Ψ Ψ' _⟩
  have hid : (Ψ ⋙ Ψ').map (𝟙 X) = 𝟙 ((Ψ ⋙ Ψ').obj X) := (Ψ ⋙ Ψ').map_id X
  rw [Ext.mapExactFunctor_mk₀, hid]
  exact mk₀_id_ne_zero (A := A'') h

end MapExactFunctorial

/-! ### The composition law for the comparison across an exact functor -/

section ExtPullbackComp

universe v u u' u''

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [EnoughInjectives A]
  {A' : Type u'} [Category.{v} A'] [Abelian A'] [HasExt.{v} A']
  {A'' : Type u''} [Category.{v} A''] [Abelian A''] [HasExt.{v} A'']

/-- **The composition law for the comparison of `Ext`-δ-functors across an exact functor.**  For
exact functors `Ψ : A ⥤ A'` and `Ψ' : A' ⥤ A''` and maps of corepresenting objects
`ρ : X' ⟶ Ψ.obj X` and `ρ' : X'' ⟶ Ψ'.obj X'`, the comparison attached to the composite functor
and the composite map `ρ' ≫ Ψ'.map ρ` is the comparison attached to `Ψ` and `ρ`, followed by
acting with `Ψ'` and precomposing with `ρ'`.

Unlike the two functoriality laws above this needs no universality: in every degree both sides
are explicit `Ext`-composites.  Acting with `Ψ'` on the composite
`(Ext.mk₀ ρ).comp (e.mapExactFunctor Ψ)` distributes by
`CategoryTheory.Abelian.Ext.mapExactFunctor_comp`, turns `Ext.mk₀ ρ` into `Ext.mk₀ (Ψ'.map ρ)` by
`…_mk₀`, and `…mapExactFunctor Ψ` into `…mapExactFunctor (Ψ ⋙ Ψ')` by
`mapExactFunctor_comp_exactFunctor`; the two `Ext.mk₀`s then merge by
`CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc`. -/
theorem extPullbackHom_comp (Ψ : A ⥤ A') [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (Ψ' : A' ⥤ A'') [Ψ'.Additive] [PreservesFiniteLimits Ψ']
    [PreservesFiniteColimits Ψ'] (X : A) {X' : A'} (ρ : X' ⟶ Ψ.obj X) {X'' : A''}
    (ρ' : X'' ⟶ Ψ'.obj X') :
    extPullbackHom (Ψ ⋙ Ψ') X (ρ' ≫ Ψ'.map ρ) =
      extPullbackHom Ψ X ρ ≫ extMapExactHom Ψ Ψ' X' ≫
        extDeltaFunctorPrecomp (Ψ ⋙ Ψ') ρ' := by
  refine DeltaFunctor.hom_ext fun n => ?_
  ext G (e : Ext X G n)
  change (Ext.mk₀ (ρ' ≫ Ψ'.map ρ)).comp (e.mapExactFunctor (Ψ ⋙ Ψ')) (zero_add n) =
    (Ext.mk₀ ρ').comp
      (((Ext.mk₀ ρ).comp (e.mapExactFunctor Ψ) (zero_add n)).mapExactFunctor Ψ') (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    mapExactFunctor_comp_exactFunctor]

end ExtPullbackComp

end ModuleSheafCohomology

namespace Stacks.Cohomology.AbelianColimit

/-! ### The composition law at the native-cohomology spelling -/

universe u

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

/-- **The composition law for the pullback map on native sheaf cohomology across two exact
functors.**  For exact functors
`Ψ : Sheaf Z ⥤ Sheaf Y` and `Ψ' : Sheaf Y ⥤ Sheaf X` of abelian sheaf categories and maps of
corepresenting objects `ρ : freeOfOpen V ⟶ Ψ.obj (freeOfOpen W)` and
`ρ' : freeOfOpen U ⟶ Ψ'.obj (freeOfOpen V)`, the morphism of δ-functors attached to the composite
functor and the composite map of corepresenting objects is the one attached to `Ψ` and `ρ`,
followed by acting with `Ψ'` and precomposing with `ρ'`.

This is `ModuleSheafCohomology.extPullbackHom_comp` at the native-cohomology spelling, and it is
the law the index-functoriality of `SpectralDiagram.stageDelta` composes its transition maps
with. -/
theorem H'pullbackHom_comp
    (Ψ : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    (Ψ' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Ψ'.Additive] [PreservesFiniteLimits Ψ'] [PreservesFiniteColimits Ψ']
    {W : Opens Z} {V : Opens Y} {U : Opens X}
    (ρ : freeOfOpen V ⟶ Ψ.obj (freeOfOpen W)) (ρ' : freeOfOpen U ⟶ Ψ'.obj (freeOfOpen V)) :
    H'pullbackHom (Ψ ⋙ Ψ') (ρ' ≫ Ψ'.map ρ) =
      H'pullbackHom Ψ ρ ≫ ModuleSheafCohomology.extMapExactHom Ψ Ψ' (freeOfOpen V) ≫
        ModuleSheafCohomology.extDeltaFunctorPrecomp (Ψ ⋙ Ψ') ρ' :=
  ModuleSheafCohomology.extPullbackHom_comp Ψ Ψ' (freeOfOpen W) ρ ρ'

end Stacks.Cohomology.AbelianColimit

end
