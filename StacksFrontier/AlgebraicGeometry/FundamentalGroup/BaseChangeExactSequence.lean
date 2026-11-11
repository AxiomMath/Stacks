module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.TrivialComposite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategoryExactSequence

/-!
# The exact sequence of fundamental groups attached to two composable morphisms

Let `X ⟶ Y ⟶ Z` be morphisms of connected schemes and let `x` be a geometric point of `X`. Base
change is a functor `FÉt_Z ⥤ FÉt_Y ⥤ FÉt_X`, and the geometric fibre functors of the three
schemes are identified with its composites by the projections of
`AlgebraicGeometry.finiteEtaleFiberProjectionIso`; so base change is exact, and the sequence

```
π₁(X, x) → π₁(Y, f ∘ x) → π₁(Z, g ∘ f ∘ x) → 1
```

is the sequence of automorphism groups attached by Stacks 0BS9 to the two exact functors. That
tag's criterion therefore applies verbatim: the sequence is exact as soon as base change along
`g` is fully faithful and a finite étale cover of `Y` comes from `Z` exactly when its base change
to `X` is a finite coproduct of copies of `X`.

## The hypothesis, and why no `@[stacks]` attribute appears in this file

Everything below needs `FÉt` at the three geometric points to be a Galois category, which is
Stacks Tag 0BNB. The declarations carry
`CategoryTheory.IsGaloisCategory (finiteEtaleFiberFunctor x)` as an instance
hypothesis, as the conditional declarations of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleEquivalence.lean` and
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/EtaleFundamental/ChangeBasePoint.lean` do,
and carry no `@[stacks]` attribute. For a connected scheme that hypothesis always holds: Tag 0BNB
is proved, as the instance `Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleGaloisCategory.lean`, so the instance
hypothesis is redundant there.

## Main definitions

* `AlgebraicGeometry.finiteEtaleFiberFintypeFunctorBaseChangeIso` — the `FintypeCat`-valued form
  of the fibre-functor isomorphism attached to base change along a morphism.

## Main results

* `Stacks.FundamentalGroup.isFiniteCoproductOfTerminal_of_iso` and
  `Stacks.FundamentalGroup.isFiniteCoproductOfTerminal_map` — being a finite coproduct of
  terminal objects is invariant under isomorphism and is preserved by an exact functor.
* `Stacks.FundamentalGroup.isExactSequence_of_equivalences` — exactness of a sequence of
  topological groups transports along isomorphisms of topological groups.
* `AlgebraicGeometry.exactFunctor_finiteEtaleBaseChange` — base change of finite étale covers
  along a morphism of connected schemes is exact.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap` — the criterion of Stacks 0BS9
  read on étale fundamental groups.

## Implementation notes

Stacks 0BS9 is stated for `FintypeCat`-valued fibre functors, so the argument runs through
`AlgebraicGeometry.finiteEtaleFiberFintypeFunctor` and is transported to the étale fundamental
groups by
`AlgebraicGeometry.autContinuousMulEquivEtaleFundamentalGroup`. The compatibility of that
transport with the induced homomorphisms is
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom`, which is proved
pointwise from `AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection`, the
equation determining `AlgebraicGeometry.etaleFundamentalGroupMap`.

## References

* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace Stacks.FundamentalGroup

/-- Being a finite coproduct of terminal objects is invariant under isomorphism. -/
theorem isFiniteCoproductOfTerminal_of_iso {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    (hX : IsFiniteCoproductOfTerminal X) : IsFiniteCoproductOfTerminal Y := by
  obtain ⟨n, A, f, hA, ⟨hc⟩⟩ := hX
  exact ⟨n, A, fun i ↦ f i ≫ e.hom, hA, ⟨IsColimit.ofIsoColimit hc (Cocone.ext e fun _ ↦ rfl)⟩⟩

/-- An exact functor carries a finite coproduct of terminal objects to a finite coproduct of
terminal objects. -/
theorem isFiniteCoproductOfTerminal_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X : C} (hX : IsFiniteCoproductOfTerminal X) :
    IsFiniteCoproductOfTerminal (F.obj X) := by
  obtain ⟨n, A, f, hA, ⟨hc⟩⟩ := hX
  exact ⟨n, fun i ↦ F.obj (A i), fun i ↦ F.map (f i),
    fun i ↦ ⟨(hA i).some.isTerminalObj F (A i)⟩,
    ⟨Cofan.isColimitMapCoconeEquiv F A (Cofan.mk X f) (isColimitOfPreserves F hc)⟩⟩

/-- Exactness of a sequence of topological groups in the sense of
`Stacks.FundamentalGroup.IsExactSequence` transports along isomorphisms of topological groups
intertwining the two sequences. -/
theorem isExactSequence_of_equivalences
    {G₀ G₁ G₂ H₀ H₁ H₂ : Type*}
    [Group G₀] [Group G₁] [Group G₂] [Group H₀] [Group H₁] [Group H₂]
    [TopologicalSpace G₀] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup G₀] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [IsTopologicalGroup H₀] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    (a : G₀ →ₜ* G₁) (b : G₁ →ₜ* G₂) (c : H₀ →ₜ* H₁) (d : H₁ →ₜ* H₂)
    (e₀ : G₀ ≃ₜ* H₀) (e₁ : G₁ ≃ₜ* H₁) (e₂ : G₂ ≃ₜ* H₂)
    (ha : ∀ z, e₁ (a z) = c (e₀ z)) (hb : ∀ z, e₂ (b z) = d (e₁ z))
    (h : IsExactSequence a b) : IsExactSequence c d := by
  obtain ⟨hsurj, hcomp, hker⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨z, rfl⟩ := e₂.surjective y
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨e₁ w, (hb w).symm⟩
  · ext y
    obtain ⟨z, rfl⟩ := e₀.surjective y
    change d (c (e₀ z)) = 1
    rw [← ha, ← hb]
    have hz : b (a z) = 1 := DFunLike.congr_fun hcomp z
    rw [hz, map_one]
  · have hrange : e₁ '' Set.range a = Set.range c := by
      rw [← Set.range_comp, show ⇑e₁ ∘ ⇑a = ⇑c ∘ ⇑e₀ from funext ha, e₀.surjective.range_comp]
    have hn : (Subgroup.normalClosure (Set.range a)).map e₁.toMonoidHom =
        Subgroup.normalClosure (Set.range c) := by
      rw [Subgroup.map_normalClosure _ _ e₁.surjective]
      exact congrArg Subgroup.normalClosure hrange
    have hcl : ((Subgroup.normalClosure (Set.range a)).topologicalClosure).map
        e₁.toMonoidHom = (Subgroup.normalClosure (Set.range c)).topologicalClosure := by
      rw [← hn]
      apply SetLike.coe_injective
      change e₁ '' closure (Subgroup.normalClosure (Set.range a) : Set G₁) =
        closure (e₁ '' (Subgroup.normalClosure (Set.range a) : Set G₁))
      exact e₁.toHomeomorph.image_closure _
    rw [← hcl, ← hker]
    ext y
    obtain ⟨z, rfl⟩ := e₁.surjective y
    change d (e₁ z) = 1 ↔ ∃ w, b w = 1 ∧ e₁ w = e₁ z
    rw [← hb, map_eq_one_iff e₂ e₂.injective]
    exact ⟨fun hz ↦ ⟨z, hz, rfl⟩, fun ⟨w, hw, he⟩ ↦ e₁.injective he ▸ hw⟩

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The `FintypeCat`-valued geometric fibre functor satisfies the Galois category axioms as soon
as the type-valued one does: the two are related by `FintypeCat.incl` on the nose. -/
theorem isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor
    (X : Scheme.{u}) [ConnectedSpace X] (x : GeometricPoint X)
    [hG : IsGaloisCategory (finiteEtaleFiberFunctor x)] :
    IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor X x)) :=
  hG

/-- The `FintypeCat`-valued form of the fibre-functor isomorphism of
`AlgebraicGeometry.finiteEtaleFiberProjectionIso`: the fibre at `x` of a cover of `Y` base changed
along `f` is the fibre at `f ∘ x` of the cover itself, naturally in the cover. -/
def finiteEtaleFiberFintypeFunctorBaseChangeIso [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (x : GeometricPoint X)
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor (x.map f))] :
    finiteEtaleBaseChange f ⋙ finiteEtaleFiberFintypeFunctor X x ≅
      finiteEtaleFiberFintypeFunctor Y (x.map f) :=
  ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
    (FiniteEtaleOver Y)).preimageIso (finiteEtaleFiberProjectionIso f x)

/-- **Base change of finite étale covers along a morphism of connected schemes is exact.** Its
composite with the geometric fibre functor of the source is isomorphic to the geometric fibre
functor of the target, which is exact and reflects isomorphisms. -/
theorem exactFunctor_finiteEtaleBaseChange (f : X ⟶ Y) (x : GeometricPoint X)
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor (x.map f))] :
    exactFunctor (FiniteEtaleOver Y) (FiniteEtaleOver X) (finiteEtaleBaseChange f) := by
  have : PreservesFiniteLimits (finiteEtaleBaseChange f ⋙ finiteEtaleFiberFunctor x) :=
    preservesFiniteLimits_of_natIso (finiteEtaleFiberProjectionIso f x).symm
  have : PreservesFiniteColimits (finiteEtaleBaseChange f ⋙ finiteEtaleFiberFunctor x) :=
    preservesFiniteColimits_of_natIso (finiteEtaleFiberProjectionIso f x).symm
  have : (finiteEtaleFiberFunctor x).ReflectsIsomorphisms :=
    IsGaloisCategory.reflectsIsomorphisms
  rw [exactFunctor_iff]
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves (finiteEtaleBaseChange f)
      (finiteEtaleFiberFunctor x),
    preservesFiniteColimits_of_reflects_of_preserves (finiteEtaleBaseChange f)
      (finiteEtaleFiberFunctor x)⟩

/-- The identification of `Aut` of the `FintypeCat`-valued fibre functor with the étale
fundamental group carries the homomorphism attached by Stacks 0BN5 to base change along `f` to
the induced homomorphism `AlgebraicGeometry.etaleFundamentalGroupMap`. -/
theorem autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor (x.map f))]
    (d : GaloisFunctorData (finiteEtaleFiberFintypeFunctor Y (x.map f))
      (finiteEtaleFiberFintypeFunctor X x) (finiteEtaleBaseChange f)
      (finiteEtaleFiberFintypeFunctorBaseChangeIso f x))
    (σ : Aut (finiteEtaleFiberFintypeFunctor X x)) :
    autMulEquivEtaleFundamentalGroup Y (x.map f) (d.hom σ) =
      etaleFundamentalGroupMap f x (autMulEquivEtaleFundamentalGroup X x σ) := by
  let L := (Functor.whiskeringRight (FiniteEtaleOver Y) FintypeCat.{u} (Type u)).obj
    FintypeCat.incl
  change Aut.of (L.mapIso (d.hom.toMonoidHom σ).asIso) = _
  rw [d.hom_toMonoidHom]
  change Aut.of (L.mapIso ((finiteEtaleFiberFintypeFunctorBaseChangeIso f x).conjAut
    (((Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) FintypeCat.{u}).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberFintypeFunctor X x) σ)).asIso) = _
  rw [Functor.map_conjAut]
  let tL : L.obj (finiteEtaleBaseChange f ⋙ finiteEtaleFiberFintypeFunctor X x) ≅
      L.obj (finiteEtaleFiberFintypeFunctor Y (x.map f)) := finiteEtaleFiberProjectionIso f x
  have ht : L.mapIso (finiteEtaleFiberFintypeFunctorBaseChangeIso f x) = tL :=
    ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
      (FiniteEtaleOver Y)).isoEquiv.right_inv tL
  rw [ht]
  rfl

/-- **The exact sequence of étale fundamental groups of two composable morphisms.** Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of connected schemes and `x` a geometric point of `X`.
If base change along `g` is fully faithful on finite étale covers and a cover of `Y` is in its
essential image exactly when its base change to `X` is a finite coproduct of copies of `X`, then

```
π₁(X, x) → π₁(Y, f ∘ x) → π₁(Z, g ∘ f ∘ x) → 1
```

is exact. This is Stacks 0BS9 for the two base-change functors, transported to the étale
fundamental groups. -/
theorem isExactSequence_etaleFundamentalGroupMap [ConnectedSpace X] [ConnectedSpace Y]
    {Z : Scheme.{u}} [ConnectedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : GeometricPoint X)
    [IsGaloisCategory (finiteEtaleFiberFunctor x)]
    [IsGaloisCategory (finiteEtaleFiberFunctor (x.map f))]
    [IsGaloisCategory (finiteEtaleFiberFunctor ((x.map f).map g))]
    (hff : Nonempty (finiteEtaleBaseChange g).FullyFaithful)
    (himage : ∀ V : FiniteEtaleOver Y,
      (finiteEtaleBaseChange g).essImage V ↔
        IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange f).obj V)) :
    IsExactSequence (etaleFundamentalGroupMap f x) (etaleFundamentalGroupMap g (x.map f)) := by
  let F := finiteEtaleFiberFintypeFunctor Z ((x.map f).map g)
  let F' := finiteEtaleFiberFintypeFunctor Y (x.map f)
  let F'' := finiteEtaleFiberFintypeFunctor X x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso g (x.map f)
  let t' := finiteEtaleFiberFintypeFunctorBaseChangeIso f x
  let d := galoisFunctorDataOfFiberIso F F' (finiteEtaleBaseChange g) t
  let d' := galoisFunctorDataOfFiberIso F' F'' (finiteEtaleBaseChange f) t'
  have _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor Z ((x.map f).map g)
  have _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor Y (x.map f)
  have _gF'' : IsGaloisCategory (setValuedFiberFunctor F'') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X x
  have he : IsExactSequence d'.hom d.hom := by
    apply ((galoisExact_iff_categorical_conditions F F' F''
      (finiteEtaleBaseChange g) (finiteEtaleBaseChange f)
      (exactFunctor_finiteEtaleBaseChange g (x.map f))
      (exactFunctor_finiteEtaleBaseChange f x) t t' d d').out 2 1).mp
    exact ⟨hff, himage⟩
  exact isExactSequence_of_equivalences d'.hom d.hom _ _
    (autContinuousMulEquivEtaleFundamentalGroup X x)
    (autContinuousMulEquivEtaleFundamentalGroup Y (x.map f))
    (autContinuousMulEquivEtaleFundamentalGroup Z ((x.map f).map g))
    (autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom f x d')
    (autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom g (x.map f) d) he

end AlgebraicGeometry

end
