module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre

/-!
# The affine chart in which Stacks 053R becomes an algebra problem

The last paragraph of the proof of Stacks 053R starts from a point `x` of an integral scheme `X`,
dominant and locally of finite type over an integral scheme `S`, and chooses *simultaneous* affine
charts: an affine open `U = Spec A` around `s = f x`, and an affine open `V = Spec B` around `x`
with `f(V) ⊆ U` and with the ideal sheaf `I` principal on `V`. What the source then records about
this data is its first condition,

> (1) `A ⊆ B` is a finitely generated extension of domains,

together with `I|_V = (g)`. This file produces that chart and proves exactly those facts.

The injectivity of `A → B` is where dominance and integrality are used, and it is proved at the
generic point rather than through a scheme-theoretic dominance argument: for `X` integral every
germ map `Γ(X, V) ⟶ 𝒪_{X,x}` is injective, `f` carries the generic point of `X` to the generic
point of `S`, and the stalk of `S` there is the function field of `S`, so the square

```
Γ(S, U) ⟶ Γ(X, V)
  |           |
  v           v
𝒪_{S,f ξ} ⟶ 𝒪_{X,ξ}
```

has an injective left column, an injective bottom row (a ring map out of a field) and an
injective right column, which forces the top row to be injective. No quasi-compactness of `f` is
needed, which is why `AlgebraicGeometry.Scheme.Hom.app_injective` is not used.

## Main results

* `AlgebraicGeometry.genericPoint_mem_of_isOpen`: in an irreducible sober space the generic point
  lies in every nonempty open set.
* `AlgebraicGeometry.injective_appLE_of_isDominant`: for a dominant morphism of integral schemes
  the restriction map `Γ(S, U) ⟶ Γ(X, V)` attached to `V ≤ f ⁻¹ᵁ U` is injective as soon as `V`
  is nonempty.
* `Stacks.Divisors.exists_span_eq_ideal_of_le`: principality of the ideal cut out by an ideal
  sheaf passes to a smaller affine open.
* `Stacks.Divisors.exists_affineOpens_appLE`: **the affine chart of the last paragraph of the
  proof of Stacks 053R.** Simultaneous affine charts `U ∋ f x` and `V ∋ x` with `f(V) ⊆ U`, on
  which `I` is cut out by a single element and `Γ(S, U) ⟶ Γ(X, V)` is an injective ring map of
  finite type.

## Implementation notes

No declaration in this file carries a `@[stacks 053R]` attribute: what is proved here is the
chart and the source's condition (1), one step of the last paragraph of the source's proof. The
tag itself is carried by `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents` (the
Noetherian case) and by
`Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_general` (the general case, in
`StacksFrontier.AlgebraicGeometry.FibreDimension.GeneralCase`), whose own chart step is
`Stacks.Divisors.fiber_support_eq_union_affineChart` and does not go through this file.

The section rings of the chart are domains, by Mathlib's instance
`AlgebraicGeometry.instIsDomainΓ` for an integral scheme and a nonempty open; the nonemptiness
witnesses are the two membership statements in the conclusion, so a consumer obtains
`IsDomain Γ(S, U.1)` and `IsDomain Γ(X, V.1)` by `inferInstance` after introducing
`Nonempty ↥U.1` and `Nonempty ↥V.1` from them. They are not part of the conclusion because an
existential cannot carry instance binders.

`Stacks.Divisors.exists_affineOpens_appLE` returns the generator of `I.ideal V` and the two
ring-theoretic facts about `f.appLE U.1 V.1 hVU` rather than naming `A` and `B` as separate types:
`Γ(S, U.1)` and `Γ(X, V.1)` *are* `A` and `B`, and `f.appLE` is the source's `A → B`.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In an irreducible sober space the generic point lies in every nonempty open set: it
specializes to every point, and a point of an open set is specialized to only from inside that
open set. -/
@[ega "0 2.1.4" "partial"]
public theorem genericPoint_mem_of_isOpen {α : Type*} [TopologicalSpace α] [QuasiSober α]
    [IrreducibleSpace α] {U : Set α} (hU : IsOpen U) (hne : U.Nonempty) : genericPoint α ∈ U :=
  (genericPoint_specializes hne.some).mem_open hU hne.some_mem

/-- **Condition (1) of the last paragraph of the proof of Stacks 053R, the injectivity half.**
For a dominant morphism `f : X ⟶ S` of integral schemes and opens `V ≤ f ⁻¹ᵁ U` with `V`
nonempty, the ring map `Γ(S, U) ⟶ Γ(X, V)` is injective.

Both germ maps at the generic point `ξ` of `X` are injective because `X` and `S` are integral,
and `f.stalkMap ξ` is injective because `f ξ` is the generic point of `S`, so that its stalk is
the function field of `S`. -/
public theorem injective_appLE_of_isDominant {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X]
    [IsIntegral S] [IsDominant f] {U : S.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hne : (V : Set X).Nonempty) : Function.Injective (f.appLE U V hVU).hom := by
  have hξV : genericPoint X ∈ V := genericPoint_mem_of_isOpen V.isOpen hne
  have hfξ : f (genericPoint X) ∈ U := hVU hξV
  -- The germ of a section of `U` at the generic point determines it, on both schemes.
  have hgermS : Function.Injective (S.presheaf.germ U (f (genericPoint X)) hfξ).hom :=
    germ_injective_of_isIntegral S _ hfξ
  -- The stalk of `S` at `f ξ` is the function field of `S`, hence a field.
  have hfield : IsField (S.presheaf.stalk (f (genericPoint X))) := by
    rw [apply_genericPoint_eq_genericPoint f]
    exact Field.toIsField S.functionField
  let : Field (S.presheaf.stalk (f (genericPoint X))) := hfield.toField
  -- The square of germs commutes.
  have hsq : f.appLE U V hVU ≫ X.presheaf.germ V (genericPoint X) hξV =
      S.presheaf.germ U (f (genericPoint X)) hfξ ≫ f.stalkMap (genericPoint X) := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
  have hpt : ∀ c, (X.presheaf.germ V (genericPoint X) hξV).hom ((f.appLE U V hVU).hom c) =
      (f.stalkMap (genericPoint X)).hom
        ((S.presheaf.germ U (f (genericPoint X)) hfξ).hom c) := fun c => by
    simpa using congrArg (fun φ => (CommRingCat.Hom.hom φ) c) hsq
  intro a b hab
  exact hgermS ((f.stalkMap (genericPoint X)).hom.injective (by rw [← hpt, ← hpt, hab]))

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

/-- If the ideal cut out by an ideal sheaf on an affine open `W` is principal, then so is the
ideal it cuts out on any smaller affine open: the latter is the extension of the former along the
restriction map. -/
public theorem exists_span_eq_ideal_of_le {X : Scheme.{u}} (I : X.IdealSheafData)
    {V W : X.affineOpens} (hVW : V ≤ W) (hW : (I.ideal W).IsPrincipal) :
    ∃ g : Γ(X, V.1), I.ideal V = Ideal.span {g} := by
  obtain ⟨g, hg⟩ := hW
  refine ⟨(X.presheaf.map (homOfLE hVW).op).hom g, ?_⟩
  rw [← I.map_ideal hVW, hg, Ideal.map_span, Set.image_singleton]

/-- **The affine chart of the last paragraph of the proof of Stacks 053R.** Let `f : X ⟶ S` be a
dominant morphism of integral schemes, locally of finite type, let `I` be a locally principal
ideal sheaf on `X` and let `x` be a point of `X`. Then there are affine opens `U ∋ f x` of `S` and
`V ∋ x` of `X` with `f(V) ⊆ U` such that

* `I` is cut out on `V` by a single element `g` of `Γ(X, V)`, and
* the ring map `Γ(S, U) ⟶ Γ(X, V)` induced by `f` is injective and of finite type.

Since `X` and `S` are integral and `U` and `V` are nonempty, `Γ(S, U)` and `Γ(X, V)` are domains;
so this is the source's condition (1), "`A ⊆ B` is a finitely generated extension of domains",
together with the equation `I|_V = (g)`. -/
public theorem exists_affineOpens_appLE {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X]
    [IsIntegral S] [IsDominant f] [LocallyOfFiniteType f] {I : X.IdealSheafData}
    (hI : IsLocallyPrincipal I) (x : X) :
    ∃ (U : S.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      f x ∈ U.1 ∧ x ∈ V.1 ∧ (∃ g : Γ(X, V.1), I.ideal V = Ideal.span {g}) ∧
        Function.Injective (f.appLE U.1 V.1 hVU).hom ∧
        (f.appLE U.1 V.1 hVU).hom.FiniteType := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem (f x)
  obtain ⟨W, hxW, hW⟩ := hI x
  have hxWU : x ∈ (W.1 ⊓ f ⁻¹ᵁ U.1 : X.Opens) := ⟨hxW, hxU⟩
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxWU (W.1 ⊓ f ⁻¹ᵁ U.1).isOpen
  have hVW : (⟨V, hV⟩ : X.affineOpens) ≤ W := fun y hy => (hVsub hy).1
  have hVU : V ≤ f ⁻¹ᵁ U.1 := fun y hy => (hVsub hy).2
  exact ⟨U, ⟨V, hV⟩, hVU, hxU, hxV, exists_span_eq_ideal_of_le I hVW hW,
    injective_appLE_of_isDominant f hVU ⟨x, hxV⟩,
    f.finiteType_appLE U.2 hV hVU⟩

/-- **Non-vacuity.** The hypothesis set of `Stacks.Divisors.exists_affineOpens_appLE` is
satisfiable, so the chart it produces is not produced from contradictory hypotheses: the identity
of `Spec ℤ` is a dominant morphism of integral schemes, locally of finite type, and the zero ideal
sheaf is locally principal. -/
public theorem exists_isDominant_locallyOfFiniteType_isLocallyPrincipal :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S) (_ : IsIntegral X) (_ : IsIntegral S) (_ : IsDominant f)
      (_ : LocallyOfFiniteType f) (I : X.IdealSheafData), IsLocallyPrincipal I := by
  have hZ : IsDomain (ULift.{u} ℤ) := Equiv.isDomain Equiv.ulift
  have : IsDomain (CommRingCat.of (ULift.{u} ℤ)) := hZ
  exact ⟨Spec (.of (ULift.{u} ℤ)), Spec (.of (ULift.{u} ℤ)), 𝟙 _, inferInstance, inferInstance,
    inferInstance, inferInstance, ⊥, isLocallyPrincipal_bot⟩

end Stacks.Divisors

end
