module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.KInjectiveRepresentativesOnAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# Extension by zero between two opens, and the successor stage of Tag 0D6B

Let `(X, 𝒪_X)` be a ringed space and let `V ≤ U` be opens of `X`.  Situation 0D67 displays
restriction from `U` to `V` as `Stacks.DerivedGlueing.openModuleRestriction`, which extends by
zero along `U` to the whole of `X` and then restricts to `V`.  This file produces the *left
adjoint* of that functor — extension by zero from `V` to `U`, in the same two-step model — and
draws from it the one complex-level step of the proof of [Stacks, Tag 0D6B] that the development
did not carry: the construction of the strict transition maps

```
τ_{V,U} : (j_V)_! I^•_V ⟶ (j_U)_! I^•_U
```

realising a prescribed isomorphism of the derived category, which is possible exactly because the
complex upstairs is K-injective.

## The adjunction, and why it is not a composite of two known ones

The composite of the adjunctions `j_{V,!} ⊣ j_V^*` and `j_U^* ⊣ j_{U,*}` gives

```
j_{V,!} ⋙ j_U^*  ⊣  j_{U,*} ⋙ j_V^*
```

whose right-hand side is the *pushforward* followed by restriction, not the extension by zero
followed by restriction that Situation 0D67 displays.  The two agree because `V ≤ U`, and that is
the content of `ExtensionByZeroModules.jShriekJStarIsoJPushJStar`: the canonical comparison
`j_{U,!} ⟹ j_{U,*}` of `ExtensionByZeroModules.jShriekToJPush` becomes invertible after
restriction to any open inside `U`.  Its invertibility after restriction to `U` itself is the
triangle identity (`ExtensionByZeroModules.unit_comp_jStar_map_jShriekToJPush`, which identifies
the comparison with the inverse of `ExtensionByZeroModules.jStarPushIso`), and it propagates to
`V ≤ U` on stalks, by `ExtensionByZeroModules.isIso_jStar_map_of_le`.

## Main definitions

* `ExtensionByZeroModules.jShriekToJPush`: the canonical comparison of extension by zero with the
  pushforward along an open immersion.
* `ExtensionByZeroModules.jShriekJStarIsoJPushJStar`: the two agree after restriction to a
  smaller open.
* `Stacks.DerivedGlueing.openModuleExtension`: extension by zero from an open of `X` to a larger
  one, in the model of Situation 0D67.
* `Stacks.DerivedGlueing.openModuleExtensionAdjunction`: **`j_! ⊣ j^*` for an inclusion of two
  opens of a ringed space**, the adjunction whose right-hand side is the restriction functor
  Situation 0D67 displays.
* `Stacks.DerivedGlueing.openModuleDerivedAdjunction`: the same on unbounded derived categories.

## Main results

* `ExtensionByZeroModules.isIso_jStar_map_of_le`: a morphism invertible after restriction to `U`
  is invertible after restriction to any smaller open.
* `Stacks.DerivedGlueing.isKInjective_openModuleRestriction`: **restriction between two opens
  preserves K-injectivity.**  This is [Stacks, Tag 08BS] for the restriction functor of
  Situation 0D67, and it does not follow from the form the development already carries —
  `ExtensionByZeroModules.isKInjective_jStar`, which restricts *from the whole space* — because
  the displayed restriction begins with an extension by zero along `U`, and that instance applies
  only to a complex already K-injective on `X`.  What makes it true is that the displayed
  restriction is a right adjoint of the exact `Stacks.DerivedGlueing.openModuleExtension`.
* `Stacks.DerivedGlueing.exists_jShriek_complexMap`: **the strict transition map of the successor
  stage of [Stacks, Tag 0D6B].** Given a K-injective complex `I_U` on `U`, a complex `I_V` on `V`
  and a morphism `Q(I_V) ⟶ Q(I_U|_V)` of the derived category on `V`, there is an honest map of
  complexes `(j_V)_! I_V ⟶ (j_U)_! I_U` of `𝒪_X`-modules whose transpose is that morphism.
* `Stacks.DerivedGlueing.exists_jShriek_complexMap_quasiIso`: when the prescribed morphism is an
  isomorphism — which is the case of [Stacks, Tag 0D6B], where it is the inverse of the
  prescribed `ρ^U_V` — the transition map is moreover a quasi-isomorphism after restriction to
  `V`.  That is exactly the hypothesis `hqi`
  of `Stacks.DerivedGlueing.exists_glueing_of_complexSystem`.

## Where this sits in the proof of Tag 0D6B

The source's proof constructs, by transfinite recursion on the index order, maps of complexes
`τ_{β,α} : (j_{β,α})_! I^•_β ⟶ I^•_α` which compose *strictly* and represent the adjoints of the
inverses of the prescribed `ρ^α_β`.  At a successor stage the choice is unconstrained — the
source says only "possible because `I_α^•` is K-injective" — and that choice is
`Stacks.DerivedGlueing.exists_jShriek_complexMap` here, with
`Stacks.DerivedGlueing.exists_jShriek_complexMap_quasiIso` supplying the quasi-isomorphism
property the assembly of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing` consumes.

At the other stages of that recursion the map of complexes is chosen out of the colimit of the
earlier stages by the same theorem, applied to the union of those stages; see
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion`.
Accordingly nothing in this file is tagged: all of it is a step of the source's
*proof*, not a clause of its statement.  In particular
`Stacks.DerivedGlueing.openModuleDerivedAdjunction` is left untagged even though it is
[Stacks, Tag 08BT] read at a pair of opens: that tag is already registered, on
`Stacks.ExtensionByZero.exists_derivedJShriek_restriction_adjunction`, for an open of the whole
space, and a second registration would claim the lemma twice.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

universe u

namespace ExtensionByZeroModules

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **A morphism invertible after restriction to `U` is invertible after restriction to any
smaller open.** Invertibility after restriction to an open is invertibility on every stalk
inside it, and the stalks inside `V` are among the stalks inside `U`. -/
theorem isIso_jStar_map_of_le (V U : Opens Z) (hVU : V ≤ U)
    {M N : SheafOfModules.{u} O} (φ : M ⟶ N) (hφ : IsIso ((jStar U O).map φ)) :
    IsIso ((jStar V O).map φ) :=
  Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_of_stalk_isIso O V φ
    fun z hz => Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map
      O U φ hφ z (hVU hz)

/-- **The canonical comparison `j_! ⟹ j_*`** of extension by zero with the pushforward along an
open immersion.  It is the transpose, along `j_! ⊣ j^*`, of the inverse of the identification
`j^* j_* ≅ id` of `ExtensionByZeroModules.jStarPushIso`: extend by zero the comparison of a
module with the restriction of its pushforward, then apply the counit. -/
def jShriekToJPush (U : Opens Z) : jShriek U O ⟶ jPush U O where
  app M := (jShriek U O).map ((jStarPushIso U O).inv.app M) ≫
    (jShriekAdjunction U O).counit.app ((jPush U O).obj M)
  naturality M N f := by
    have hι := (jStarPushIso U O).inv.naturality f
    have hε := (jShriekAdjunction U O).counit.naturality ((jPush U O).map f)
    simp only [Functor.id_map, Functor.comp_map] at hι hε
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hι, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg _ hε

/-- **The defining equation of `ExtensionByZeroModules.jShriekToJPush`.** Restricted to `U` and
precomposed with the unit of `j_! ⊣ j^*`, the comparison is the inverse of the identification
`j^* j_* ≅ id`.  This is the transpose relation written out, and it is the triangle identity of
`ExtensionByZeroModules.jShriekAdjunction` together with the naturality of its unit. -/
theorem unit_comp_jStar_map_jShriekToJPush (U : Opens Z) (M : SheafOfModules.{u} (resRing U O)) :
    (jShriekAdjunction U O).unit.app M ≫ (jStar U O).map ((jShriekToJPush O U).app M) =
      (jStarPushIso U O).inv.app M := by
  have hu := (jShriekAdjunction U O).unit.naturality ((jStarPushIso U O).inv.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hu
  show (jShriekAdjunction U O).unit.app M ≫ (jStar U O).map
      ((jShriek U O).map ((jStarPushIso U O).inv.app M) ≫
        (jShriekAdjunction U O).counit.app ((jPush U O).obj M)) = _
  rw [Functor.map_comp, ← Category.assoc, ← hu, Category.assoc,
    (jShriekAdjunction U O).right_triangle_components, Category.comp_id]

/-- **`j_U^*` of the comparison is invertible.** By
`ExtensionByZeroModules.unit_comp_jStar_map_jShriekToJPush` it becomes, after precomposition with
the unit of `j_! ⊣ j^*`, the inverse of an isomorphism; and that unit is itself invertible
([Stacks, Tag 00AB], `ExtensionByZeroModules.isIso_jShriekAdjunction_unit`). -/
instance isIso_jStar_map_jShriekToJPush (U : Opens Z) (M : SheafOfModules.{u} (resRing U O)) :
    IsIso ((jStar U O).map ((jShriekToJPush O U).app M)) := by
  have := isIso_jShriekAdjunction_unit U O
  have : IsIso ((jShriekAdjunction U O).unit.app M) := inferInstance
  have : IsIso ((jShriekAdjunction U O).unit.app M ≫
      (jStar U O).map ((jShriekToJPush O U).app M)) := by
    rw [unit_comp_jStar_map_jShriekToJPush O U M]
    infer_instance
  exact IsIso.of_isIso_comp_left ((jShriekAdjunction U O).unit.app M) _

/-- **Extension by zero and the pushforward agree after restriction to a smaller open.** For
`V ≤ U` the comparison `ExtensionByZeroModules.jShriekToJPush` becomes invertible after
restricting to `V`: both readings compute restriction from `U` to `V`. -/
def jShriekJStarIsoJPushJStar {V U : Opens Z} (hVU : V ≤ U) :
    jShriek U O ⋙ jStar V O ≅ jPush U O ⋙ jStar V O :=
  haveI : ∀ M, IsIso ((jStar V O).map ((jShriekToJPush O U).app M)) := fun M =>
    isIso_jStar_map_of_le O V U hVU _ (isIso_jStar_map_jShriekToJPush O U M)
  NatIso.ofComponents (fun M => asIso ((jStar V O).map ((jShriekToJPush O U).app M)))
    (fun {M N} f => by
      have h := (jShriekToJPush O U).naturality f
      simpa only [Functor.comp_map, asIso_hom, ← Functor.map_comp] using congrArg
        (fun g => (jStar V O).map g) h)

end ExtensionByZeroModules

namespace Stacks.DerivedGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **Extension by zero from an open of a ringed space to a larger one.** Extend by zero from `V`
to the whole of `X` and then restrict to `U`.  This is the mirror of
`Stacks.DerivedGlueing.openModuleRestriction`, which extends by zero from `U` and restricts to
`V`, and for `V ≤ U` it is canonically extension by zero inside `U`. -/
def openModuleExtension (X : RingedSpace.{u, u}) (V U : Opens X.carrier) (_ : V ≤ U) :
    SheafOfModules.{u} (restrictedRingSheaf X V) ⥤
      SheafOfModules.{u} (restrictedRingSheaf X U) :=
  jShriek V (underlyingRingSheaf X) ⋙ jStar U (underlyingRingSheaf X)

/-- The extension-by-zero functor `openModuleExtension X V U hVU` is additive. -/
instance openModuleExtension_additive (V U : Opens X.carrier) (hVU : V ≤ U) :
    (openModuleExtension X V U hVU).Additive := by
  change (jShriek V (underlyingRingSheaf X) ⋙ jStar U (underlyingRingSheaf X)).Additive
  infer_instance

/-- The extension-by-zero functor `openModuleExtension X V U hVU` preserves finite limits. -/
instance openModuleExtension_preservesFiniteLimits (V U : Opens X.carrier) (hVU : V ≤ U) :
    PreservesFiniteLimits (openModuleExtension X V U hVU) := by
  change PreservesFiniteLimits (jShriek V (underlyingRingSheaf X) ⋙
    jStar U (underlyingRingSheaf X))
  infer_instance

/-- The extension-by-zero functor `openModuleExtension X V U hVU` preserves finite colimits. -/
instance openModuleExtension_preservesFiniteColimits (V U : Opens X.carrier) (hVU : V ≤ U) :
    PreservesFiniteColimits (openModuleExtension X V U hVU) := by
  change PreservesFiniteColimits (jShriek V (underlyingRingSheaf X) ⋙
    jStar U (underlyingRingSheaf X))
  infer_instance

/-- **`j_! ⊣ j^*` for the inclusion of one open of a ringed space into another.** Extension by
zero from `V` to `U` is left adjoint to the restriction functor that Situation 0D67 displays.

It is the composite of `ExtensionByZeroModules.jShriekAdjunction` at `V` with
`ExtensionByZeroModules.jStarAdjunction` at `U`, whose right-hand side is the pushforward along
`U` followed by restriction to `V`, transported along
`ExtensionByZeroModules.jShriekJStarIsoJPushJStar`, which identifies that with extension by zero
along `U` followed by restriction to `V` — the displayed restriction — because `V ≤ U`. -/
def openModuleExtensionAdjunction (V U : Opens X.carrier) (hVU : V ≤ U) :
    openModuleExtension X V U hVU ⊣ openModuleRestriction X V U hVU :=
  Adjunction.ofNatIsoRight
    ((jShriekAdjunction V (underlyingRingSheaf X)).comp
      (jStarAdjunction U (underlyingRingSheaf X)))
    (jShriekJStarIsoJPushJStar (underlyingRingSheaf X) hVU).symm

/-- **The adjunction on unbounded derived categories.** Both functors are exact, so each induces
a functor on derived categories and the adjunction descends, by
`CategoryTheory.Adjunction.mapDerivedCategory`.  This is [Stacks, Tag 08BT] read at an inclusion
of two opens; it is left untagged, the tag being already registered for an open of the whole
space. -/
def openModuleDerivedAdjunction (V U : Opens X.carrier) (hVU : V ≤ U) :
    (openModuleExtension X V U hVU).mapDerivedCategory ⊣
      (openModuleRestriction X V U hVU).mapDerivedCategory :=
  (openModuleExtensionAdjunction V U hVU).mapDerivedCategory

/-- **Restriction between two opens preserves K-injectivity.** The displayed restriction of
Situation 0D67 from `U` to `V` carries a K-injective complex of `𝒪_U`-modules to a K-injective
complex of `𝒪_V`-modules.

This is [Stacks, Tag 08BS] for that functor.  It does not follow from
`ExtensionByZeroModules.isKInjective_jStar`, which is the same tag for restriction *from the
whole space*: the displayed restriction begins with an extension by zero along `U`, so that
instance would have to be applied to a complex of `𝒪_X`-modules known to be K-injective, and
only the complex on `U` is.  What makes it true is that the displayed restriction is a right
adjoint of the exact functor
`Stacks.DerivedGlueing.openModuleExtension`, which is the criterion
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`. -/
instance isKInjective_openModuleRestriction (V U : Opens X.carrier) (hVU : V ≤ U)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (openModuleRestriction X V U hVU) (openModuleExtension X V U hVU)
    (openModuleExtensionAdjunction V U hVU) J

/-- **The strict transition map of the successor stage of [Stacks, Tag 0D6B].** Let `V ≤ U` be
opens of `X`, let `I_U` be a K-injective complex of `𝒪_U`-modules, let `I_V` be a complex of
`𝒪_V`-modules, and let `g` be a morphism `Q(I_V) ⟶ Q(I_U|_V)` of the derived category on `V`.
Then there is an honest map of complexes of `𝒪_X`-modules

```
t : (j_V)_! I_V ⟶ (j_U)_! I_U
```

whose transpose along `j_{V,!} ⊣ j_V^*` — that is, the unit at `I_V` followed by the restriction
of `t` to `V` — represents `g`.

This is the step the source performs at a successor stage: "we choose any map of complexes
`(j_{α',α})_! I_{α'}^• → I_α^•` which is adjoint to the inverse of the isomorphism `ρ^α_{α'}`
(possible because `I_α^•` is K-injective)".  The K-injectivity used is that of the *restriction*
`I_U|_V`, which is `Stacks.DerivedGlueing.isKInjective_openModuleRestriction`, and the lift is
`StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective`. -/
theorem exists_jShriek_complexMap (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) [J.IsKInjective]
    (g : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj
      (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :
    ∃ t : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C ⟶
          ((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J,
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction
          (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ t) =
        g := by
  have : CochainComplex.IsKInjective (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) := isKInjective_openModuleRestriction V U hVU J
  obtain ⟨f, hf⟩ := StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective
    C (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) g
  refine ⟨((Adjunction.mapHomologicalComplexAdjunction
    (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _).symm f, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hf

/-- **The complex-level unit of `j_! ⊣ j^*` is invertible.** The unit of the prolongation to
complexes is degreewise the unit of `ExtensionByZeroModules.jShriekAdjunction`, which is
invertible by [Stacks, Tag 00AB]; a degreewise isomorphism of complexes is an isomorphism. -/
instance isIso_jShriekComplexAdjunction_unit_app (V : Opens X.carrier)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ) :
    IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app C) := by
  have := isIso_jShriekAdjunction_unit V (underlyingRingSheaf X)
  have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app C).f n) :=
    fun n => by
      change IsIso ((jShriekAdjunction V (underlyingRingSheaf X)).unit.app (C.X n))
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The strict transition map attached to an isomorphism restricts to a quasi-isomorphism.**
In the situation of `Stacks.DerivedGlueing.exists_jShriek_complexMap`, if the prescribed morphism
`g` is an isomorphism — which is the case in [Stacks, Tag 0D6B], where it is the inverse of the
prescribed `ρ^U_V` — then the transition map it produces is a quasi-isomorphism after restriction
to `V`.

That property is exactly the hypothesis `hqi` of
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem`, so this is the form in which the
successor stage feeds the assembly.  The proof is that the transpose of `t` is `g`, the unit of
the complex-level adjunction is invertible, and a morphism of complexes is a quasi-isomorphism
exactly when its image under `DerivedCategory.Q` is invertible. -/
theorem exists_jShriek_complexMap_quasiIso (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) [J.IsKInjective]
    (g : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj
      (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :
    ∃ t : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C ⟶
          ((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J,
      DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ t) =
          g.hom ∧
        QuasiIso (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map t) := by
  obtain ⟨t, ht⟩ := exists_jShriek_complexMap V U hVU C J g.hom
  refine ⟨t, ht, ?_⟩
  have hkey : (Adjunction.mapHomologicalComplexAdjunction
        (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app C ≫
        ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map t =
      (Adjunction.mapHomologicalComplexAdjunction
        (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ t := by
    simp [Adjunction.homEquiv_unit]
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : IsIso (DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ t)) := by
    rw [ht]
    exact g.isIso_hom
  exact IsIso.of_isIso_fac_left (f := DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app C))
    (by rw [← DerivedCategory.Q.map_comp, hkey])

end Stacks.DerivedGlueing

end
