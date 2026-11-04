module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# The pasting law for the derived base change map

`Stacks.Cohomology.BaseChange.derived` descends a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` of
underived composites to the bounded below right derived functors. This file proves that the
descent is compatible with horizontal pasting: for two horizontally composable commutative
squares of additive functors

```
A₀ --V₁--> A₁ --V₂--> A₂
|P₀         |P₁        |P₂
v           v          v
B₀ --U₁--> B₁ --U₂--> B₂
```

with exact `U₁`, `U₂`, `U` and `V₂`, and with comparisons `cU : U₁ ⋙ U₂ ≅ U` and
`cV : V₁ ⋙ V₂ ≅ V` of the two composite horizontal legs, the derived comparison of the outer
rectangle is the composite of the derived comparisons of the two squares, read through the
comparisons `RU₁ ⋙ RU₂ ≅ RU` and `RV₁ ⋙ RV₂ ≅ RV` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`.

The hypothesis is exactly the *underived* pasting identity, evaluated at each object of `A₀`.
Nothing else is assumed: the squares are arbitrary, and no acyclicity enters, exactness of the
horizontal functors being enough for every object to be right acyclic for them.

## The route of the descent

`Stacks.Cohomology.BaseChange.derived` is characterized by
`Stacks.Cohomology.BaseChange.derived_fac`: composed with the derived-functor unit of `RP₀` it
is `Stacks.Cohomology.BaseChange.onHomotopy`, the degreewise comparison followed by the units of
`RV'` and `RP'`. Since `RP₀ ⋙ RU` is a right derived functor of `(P₀ ⋙ U)` with that unit,
`CategoryTheory.Functor.rightDerived_ext` reduces the identity of natural transformations to an
identity after the unit, and there each of the three factors is replaced by its `onHomotopy`.
What remains is a computation on bounded below homotopy categories, whose three inputs are

* the degreewise pasting law `Stacks.Cohomology.BaseChange.mapPlus_paste_app`;
* on the base, `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_inv_app` — the
  comparison `RU₁ ⋙ RU₂ ≅ RU` enters contravariantly, so it is consumed in inverse form;
* on the source, `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac` — the
  comparison `RV₁ ⋙ RV₂ ≅ RV` enters covariantly, so the positive form applies.

## Main definitions

* `Stacks.Cohomology.BaseChange.derivedPaste`: the pasted comparison, as a transformation
  `RP₀ ⋙ RU ⟶ RV ⋙ RP₂`.

## Main results

* `Stacks.Cohomology.BaseChange.onHomotopy_app_mapSquarePlus`:
  `Stacks.Cohomology.BaseChange.onHomotopy_app` with the degreewise comparison written as a
  transformation of the composites of the induced functors rather than of the functor induced
  by a composite. This is the form every consumer below uses.
* `Stacks.Cohomology.BaseChange.derivedPaste_target_fac`: the identity on the source side,
  where the comparison of the derived inverse images along the composite enters covariantly.
* `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste` and
  `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app`: **the pasting law for the derived
  comparison**, as an identity of natural transformations and evaluated at an object.

## Implementation notes

*Everything is generic.* No statement here mentions sheaves. The intended instance is the base
change map of abelian sheaves on the small étale sites of schemes, whose concrete coefficient
categories make these rearrangements expensive; stated on variables they are cheap.

*Why the pasting law is not named `derived_paste`.*
`Stacks.Cohomology.BaseChange.derived_paste` is the special case of this law in which the two
composite horizontal legs are the literal composites `U₁ ⋙ U₂` and `V₁ ⋙ V₂`, and the
comparison of the outer rectangle is `Stacks.Cohomology.BaseChange.pasteTrans` of the two
squares. What is proved here takes the two legs as arbitrary functors `U` and `V` together with
comparisons `cU : U₁ ⋙ U₂ ≅ U` and `cV : V₁ ⋙ V₂ ≅ V`, and the comparison of the rectangle as
an arbitrary `τ` satisfying the underived pasting identity; the special case is the one where
`cU` and `cV` are identities. The étale instance needs the general form: there the composite
legs are the inverse images along `u₂ ≫ u₁` and `v₂ ≫ v₁`, not the composites of the inverse
images along `u₁`, `u₂` and along `v₁`, `v₂`.

*Why the identity is stated with `mapPlus` and not with `mapSquarePlus`.* The functors
`(P ⋙ W).mapHomotopyCategoryPlus` and `P.mapHomotopyCategoryPlus ⋙ W.mapHomotopyCategoryPlus`
agree on objects definitionally but are not equal, so the two sides of these identities have
types that are only definitionally equal. On variables the defeq is free; at a concrete sheaf
category discharging it is not, which is why every concrete consumer should instantiate the
`mapPlus` form and apply `Stacks.Cohomology.BaseChange.mapSquarePlus_app` if it needs the
square form.

*The derived-functor units of the exact horizontal functors are inverted by an instance.*
`Stacks.Cohomology.BaseChange.exactUnit_isIso` is registered as an instance where it is
proved, so that `CategoryTheory.asIso` can be applied to those units inside a statement
without a local `letI`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### `onHomotopy` at a bounded below complex, in the normalized square form -/

section Components

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

/-- **`Stacks.Cohomology.BaseChange.onHomotopy_app` in the normalized square form.** The only
difference from `onHomotopy_app` is the spelling of the degreewise comparison: there it is
`Stacks.Cohomology.BaseChange.mapPlus`, a transformation of the functors induced by the two
composites, here `Stacks.Cohomology.BaseChange.mapSquarePlus`, a transformation of the
composites of the induced functors. The two agree on components by
`Stacks.Cohomology.BaseChange.mapSquarePlus_app`, but their sources and targets are only
*definitionally* equal, so the conversion has to be a function application rather than a
rewrite; this is that application, made once. -/
theorem onHomotopy_app_mapSquarePlus (K : HomotopyCategory.Plus A) :
    (onHomotopy F F' G G' τ e).app K =
      e.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((mapSquarePlus F F' G G' τ).app K) ≫
          F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj K) ≫
            F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnit.app K) :=
  (onHomotopy_app F F' G G' τ e K).trans
    (congrArg
      (fun m ↦ e.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map m ≫
          F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj K) ≫
            F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnit.app K))
      (mapSquarePlus_app F F' G G' τ K).symm)

end Components

/-! ### The pasting law -/

section Paste

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives A₂]
  [EnoughInjectives B₀] [EnoughInjectives B₁]
  (P₀ : A₀ ⥤ B₀) (P₁ : A₁ ⥤ B₁) (P₂ : A₂ ⥤ B₂)
  (U₁ : B₀ ⥤ B₁) (U₂ : B₁ ⥤ B₂) (U : B₀ ⥤ B₂)
  (V₁ : A₀ ⥤ A₁) (V₂ : A₁ ⥤ A₂) (V : A₀ ⥤ A₂)
  [P₀.Additive] [P₁.Additive] [P₂.Additive]
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [V₁.Additive] [V₂.Additive] [V.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
  (cU : U₁ ⋙ U₂ ≅ U) (cV : V₁ ⋙ V₂ ≅ V)
  (τ : P₀ ⋙ U ⟶ V ⋙ P₂) (τ₁ : P₀ ⋙ U₁ ⟶ V₁ ⋙ P₁) (τ₂ : P₁ ⋙ U₂ ⟶ V₂ ⋙ P₂)

/-- **The pasted derived comparison**: the derived comparisons of the two squares, read through
the comparisons of the derived composite horizontal legs. -/
def derivedPaste :
    P₀.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus ⟶
      V.rightDerivedFunctorPlus ⋙ P₂.rightDerivedFunctorPlus :=
  Functor.whiskerLeft P₀.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U cU).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derived P₀ P₁ U₁ V₁ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit))
      U₂.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft V₁.rightDerivedFunctorPlus
      (derived P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIsoOfExact V₁ V₂ V cV).hom
      P₂.rightDerivedFunctorPlus

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- The components of `Stacks.Cohomology.BaseChange.derivedPaste`. -/
theorem derivedPaste_app (M : DerivedCategory.Plus A₀) :
    (derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ₁ τ₂).app M =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U cU).inv.app
          (P₀.rightDerivedFunctorPlus.obj M) ≫
        U₂.rightDerivedFunctorPlus.map
            ((derived P₀ P₁ U₁ V₁ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app M) ≫
          (derived P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).app
              (V₁.rightDerivedFunctorPlus.obj M) ≫
            P₂.rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact V₁ V₂ V cV).hom.app M) := by
  simp only [derivedPaste, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator, Category.id_comp]

/-- **The source side of the pasting law.** The derived-functor unit of `RP₂` turns the
comparison of the derived inverse images along the composite source leg into the degreewise
comparison; here the comparison enters covariantly, so
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac` applies directly. -/
theorem derivedPaste_target_fac (K : HomotopyCategory.Plus A₀) :
    P₂.rightDerivedFunctorPlusUnit.app
          (V₂.mapHomotopyCategoryPlus.obj (V₁.mapHomotopyCategoryPlus.obj K)) ≫
        P₂.rightDerivedFunctorPlus.map
            (V₂.rightDerivedFunctorPlusUnit.app (V₁.mapHomotopyCategoryPlus.obj K)) ≫
          P₂.rightDerivedFunctorPlus.map
              (V₂.rightDerivedFunctorPlus.map (V₁.rightDerivedFunctorPlusUnit.app K)) ≫
            P₂.rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact V₁ V₂ V cV).hom.app
                (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          (P₂.mapHomotopyCategoryPlus.map
            ((Functor.mapHomotopyCategoryPlusCompIso cV).hom.app K)) ≫
        P₂.rightDerivedFunctorPlusUnit.app (V.mapHomotopyCategoryPlus.obj K) ≫
          P₂.rightDerivedFunctorPlus.map (V.rightDerivedFunctorPlusUnit.app K) := by
  rw [reassoc_of% (P₂.rightDerivedFunctorPlusUnit.naturality _), ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp,
    Functor.rightDerivedFunctorPlusCompIsoOfExact_fac V₁ V₂ V cV K]
  rfl

/-- The computation that the descent of the pasting law reduces to: after the derived-functor
unit of `RP₀`, the pasted derived comparison is the `onHomotopy` of the outer rectangle. -/
theorem onHomotopy_eq_unit_comp_derivedPaste_app
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (K : HomotopyCategory.Plus A₀) :
    (onHomotopy P₀ P₂ U V τ (asIso U.rightDerivedFunctorPlusUnit)).app K =
      U.rightDerivedFunctorPlus.map (P₀.rightDerivedFunctorPlusUnit.app K) ≫
        (derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ₁ τ₂).app
          (DerivedCategory.Plus.Qh.obj K) := by
  have hnat0 := (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U cU).inv.naturality
    (P₀.rightDerivedFunctorPlusUnit.app K)
  have hfac1 := derived_fac_app P₀ P₁ U₁ V₁ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit) K
  have hfac2 := derived_fac_app P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)
    (V₁.mapHomotopyCategoryPlus.obj K)
  have hnat2 := (derived P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).naturality
    (V₁.rightDerivedFunctorPlusUnit.app K)
  have hnatU := (asIso U₂.rightDerivedFunctorPlusUnit).inv.naturality
    ((mapSquarePlus P₀ P₁ U₁ V₁ τ₁).app K)
  rw [onHomotopy_app_mapSquarePlus,
    mapSquarePlus_paste_app P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ τ₁ τ₂ hτ K]
  simp only [Functor.map_comp, Category.assoc]
  rw [← derivedPaste_target_fac P₂ V₁ V₂ V cV K]
  conv_rhs =>
    rw [derivedPaste_app, reassoc_of% hnat0, ← Functor.map_comp_assoc, hfac1,
      onHomotopy_app_mapSquarePlus]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hnat2, reassoc_of% hfac2, onHomotopy_app_mapSquarePlus]
    simp only [Category.assoc]
    rw [reassoc_of% hnatU,
      reassoc_of% (Functor.rightDerivedFunctorPlusCompIsoOfExact_inv_app U₁ U₂ U cU
        (P₀.mapHomotopyCategoryPlus.obj K))]

/-- **The pasting law for the derived base change comparison.** For two horizontally composable
commutative squares of additive functors with exact horizontal legs, the descent of the
comparison of the outer rectangle is the composite of the descents of the two squares, read
through the comparisons of the derived inverse images along the two composite horizontal legs.

The hypothesis is exactly the underived pasting identity, evaluated at each object. -/
theorem derived_eq_derivedPaste
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X)) :
    derived P₀ P₂ U V τ (asIso U.rightDerivedFunctorPlusUnit) =
      derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ₁ τ₂ := by
  let _ : (P₀.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.whiskerRight P₀.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A₀) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
      (fun K ↦ by dsimp; infer_instance)
  refine Functor.rightDerived_ext (P₀.rightDerivedFunctorPlus ⋙ U.rightDerivedFunctorPlus)
    (Functor.whiskerRight P₀.rightDerivedFunctorPlusUnit U.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A₀) _ _ _ ?_
  rw [Category.assoc, derived_fac]
  refine NatTrans.ext (funext fun K => ?_)
  simpa [Functor.associator] using
    onHomotopy_eq_unit_comp_derivedPaste_app P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ τ₁ τ₂ hτ K

/-- **The pasting law for the derived base change comparison, evaluated at an object.** -/
theorem derived_eq_derivedPaste_app
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (M : DerivedCategory.Plus A₀) :
    (derived P₀ P₂ U V τ (asIso U.rightDerivedFunctorPlusUnit)).app M =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U cU).inv.app
          (P₀.rightDerivedFunctorPlus.obj M) ≫
        U₂.rightDerivedFunctorPlus.map
            ((derived P₀ P₁ U₁ V₁ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app M) ≫
          (derived P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).app
              (V₁.rightDerivedFunctorPlus.obj M) ≫
            P₂.rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact V₁ V₂ V cV).hom.app M) := by
  rw [derived_eq_derivedPaste P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ τ₁ τ₂ hτ, derivedPaste_app]

end Paste

end Stacks.Cohomology.BaseChange

end
