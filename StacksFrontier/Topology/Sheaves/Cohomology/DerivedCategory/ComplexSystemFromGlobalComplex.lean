module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.MayerVietorisTriangle

/-!
# A system of complexes supported stagewise on an increasing cover

`Stacks.DerivedGlueing.exists_glueing_of_complexSystem`, the assembly half of
[Stacks, Tag 0D6B], is a theorem about a datum

```
F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ,  I α,  hsupp : F α ≅ (j_α)_! (I α),  hqi
```

and until this file the development produced **no inhabitant of that datum at all**, so the
theorem covered nothing.  This file supplies one, for an arbitrary increasing family of opens:
the filtration of a fixed global complex `A` by the extensions by zero of its restrictions,

```
F α = (j_α)_! (j_α)^* A,     I α = (j_α)^* A,     hsupp α = Iso.refl _ .
```

Nothing here is tagged.  The datum of [Stacks, Tag 0D6B] is a family of *prescribed* objects of
the derived categories on the stages together with prescribed transitions; this file produces a
family that happens to come from one global complex, which is a witness for the assembly half
and not a clause of the tag.

## What makes the filtration a functor

The transition `(j_W)_!(j_W)^* ⟶ (j_U)_!(j_U)^*` for `W ≤ U` is
`Stacks.ExtensionByZero.extensionRestrictionInclusion`, which this branch makes public — it was
`private`, and a `private` declaration cannot appear in the body of a public definition.  What
was missing for it to be the morphism part of a functor is that it composes *strictly*, and
that is proved here from the factorization
`Stacks.ExtensionByZero.extensionRestrictionInclusion_fac` through the counit on the larger
open: a morphism `(j_W)_!(j_W)^* G ⟶ (j_U)_!(j_U)^* G` is *determined* by its composite with
`ε_U` at `G` (`Stacks.DerivedGlueing.hom_ext_of_comp_counit`), because `ε_U` is invertible at
both the source and the target and `(j_U)_!(j_U)^*` of `ε_U` is invertible by the triangle
identity.  Associativity and unitality are then two applications of that determination.

## Main definitions

* `Stacks.DerivedGlueing.globalFiltrationSystem`: the functor `E ⥤ CochainComplex (Mod 𝒪_X) ℤ`
  carrying `α` to `(j_α)_! (j_α)^* A`.
* `Stacks.DerivedGlueing.globalFiltrationLocal`, `globalFiltrationSupport`: the complex on the
  stage and the identification of the stage with its extension by zero, which is `Iso.refl`.

## Main results

* `Stacks.DerivedGlueing.hom_ext_of_comp_counit`: a morphism between extensions by zero from
  `W ≤ U` is determined by its composite with the counit at `U`.
* `Stacks.DerivedGlueing.extensionRestrictionInclusion_refl`,
  `Stacks.DerivedGlueing.extensionRestrictionInclusion_trans`: the filtration maps are strictly
  unital and strictly transitive — this is what makes `globalFiltrationSystem` a functor rather
  than a lax one.
* `Stacks.DerivedGlueing.isIso_jStar_map_extensionRestrictionInclusion`: a filtration map
  becomes invertible after restriction to the smaller open, which is the `hqi` hypothesis of
  the assembly in its strongest form.
* `Stacks.DerivedGlueing.exists_glueing_of_globalFiltration`: every binder of
  `Stacks.DerivedGlueing.exists_glueing_of_complexSystem` discharged.

## Non-degenerate instances

The index order is arbitrary here.  `Stacks.DerivedGlueing.eq_top_of_isGreatest` says that an
increasing cover indexed by an order with a greatest element `g` has `W g = ⊤`, so an instance
over a nonempty *finite* order — and more generally any instance on a carrier where every
increasing chain of opens stabilises — is degenerate.  A fully non-degenerate instance
therefore needs a non-quasi-compact carrier carrying an infinite strictly increasing chain of
proper opens whose union is everything: `Stacks.DerivedGlueing.natLine` with the stages
`Stacks.DerivedGlueing.natStage`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.NonDegenerateIncreasingCover`.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

section Inclusion

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **The counit of `j_! ⊣ j^*` on the larger open is invertible at an extension by zero from a
smaller one.** -/
theorem isIso_counit_app_extension (W U : Opens Z) (hWU : W ≤ U) (G : SheafOfModules.{u} O) :
    IsIso ((jShriekAdjunction U O).counit.app ((jStar W O ⋙ jShriek W O).obj G)) :=
  counit_isIso_of_stalk_isZero U O _ fun x hx =>
    isZero_stalk_jShriek W O ((jStar W O).obj G) x fun hxW => hx (hWU hxW)

/-- **A morphism out of an extension by zero from `W` into one from `U ⊇ W` is determined by its
composite with the counit at `U`.** -/
theorem hom_ext_of_comp_counit (W U : Opens Z) (hWU : W ≤ U) (G : SheafOfModules.{u} O)
    (f g : (jStar W O ⋙ jShriek W O).obj G ⟶ (jStar U O ⋙ jShriek U O).obj G)
    (h : f ≫ (jShriekAdjunction U O).counit.app G =
      g ≫ (jShriekAdjunction U O).counit.app G) :
    f = g := by
  have h1 := isIso_counit_app_extension O W U hWU G
  have h2 := isIso_counit_app_extension O U U le_rfl G
  have h3 : IsIso ((jStar U O ⋙ jShriek U O).map ((jShriekAdjunction U O).counit.app G)) := by
    have := Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_counit O U G
    exact Functor.map_isIso (jShriek U O) ((jStar U O).map _)
  have hmap : (jStar U O ⋙ jShriek U O).map f = (jStar U O ⋙ jShriek U O).map g := by
    rw [← cancel_mono ((jStar U O ⋙ jShriek U O).map
      ((jShriekAdjunction U O).counit.app G)), ← Functor.map_comp, ← Functor.map_comp, h]
  have hnf := (jShriekAdjunction U O).counit.naturality f
  have hng := (jShriekAdjunction U O).counit.naturality g
  simp only [Functor.id_map] at hnf hng
  rw [← cancel_epi ((jShriekAdjunction U O).counit.app
    ((jStar W O ⋙ jShriek W O).obj G)), ← hnf, ← hng, hmap]

/-- **The filtration map is the unique map over the identity.** -/
theorem extensionRestrictionInclusion_eq (W U : Opens Z) (hWU : W ≤ U)
    (G : SheafOfModules.{u} O)
    (f : (jStar W O ⋙ jShriek W O).obj G ⟶ (jStar U O ⋙ jShriek U O).obj G)
    (h : f ≫ (jShriekAdjunction U O).counit.app G = (jShriekAdjunction W O).counit.app G) :
    f = (Stacks.ExtensionByZero.extensionRestrictionInclusion O W U hWU).app G :=
  hom_ext_of_comp_counit O W U hWU G _ _
    (h.trans (Stacks.ExtensionByZero.extensionRestrictionInclusion_fac O W U hWU G).symm)

/-- **The filtration map at a single open is the identity.** -/
theorem extensionRestrictionInclusion_refl (W : Opens Z) :
    Stacks.ExtensionByZero.extensionRestrictionInclusion O W W le_rfl = 𝟙 _ :=
  NatTrans.ext (funext fun G =>
    (extensionRestrictionInclusion_eq O W W le_rfl G (𝟙 _) (Category.id_comp _)).symm)

/-- **The filtration maps compose strictly.** -/
theorem extensionRestrictionInclusion_trans (W V U : Opens Z) (hWV : W ≤ V) (hVU : V ≤ U) :
    Stacks.ExtensionByZero.extensionRestrictionInclusion O W V hWV ≫
        Stacks.ExtensionByZero.extensionRestrictionInclusion O V U hVU =
      Stacks.ExtensionByZero.extensionRestrictionInclusion O W U (hWV.trans hVU) :=
  NatTrans.ext (funext fun G => extensionRestrictionInclusion_eq O W U (hWV.trans hVU) G _ (by
    rw [NatTrans.comp_app, Category.assoc,
      Stacks.ExtensionByZero.extensionRestrictionInclusion_fac O V U hVU G,
      Stacks.ExtensionByZero.extensionRestrictionInclusion_fac O W V hWV G]))

/-- **The filtration map becomes invertible after restriction to the smaller open.** -/
theorem isIso_jStar_map_extensionRestrictionInclusion (W U : Opens Z) (hWU : W ≤ U)
    (G : SheafOfModules.{u} O) :
    IsIso ((jStar W O).map
      ((Stacks.ExtensionByZero.extensionRestrictionInclusion O W U hWU).app G)) := by
  have h1 := isIso_jStar_map_counit_of_le O W U hWU G
  have h2 := Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_counit O W G
  have key : (jStar W O).map
      ((Stacks.ExtensionByZero.extensionRestrictionInclusion O W U hWU).app G) =
      (jStar W O).map ((jShriekAdjunction W O).counit.app G) ≫
        inv ((jStar W O).map ((jShriekAdjunction U O).counit.app G)) := by
    rw [IsIso.eq_comp_inv, ← Functor.map_comp,
      Stacks.ExtensionByZero.extensionRestrictionInclusion_fac]
  rw [key]
  infer_instance

end Inclusion

section System

variable {X : RingedSpace.{u, u}} {E : Type u} [Preorder E] (W : E → Opens X.carrier)
  (hmono : ∀ β α : E, β ≤ α → W β ≤ W α)
  (A : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)

/-- **The filtration of a global complex by the extensions by zero of its restrictions.** -/
def globalFiltrationSystem :
    E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ where
  obj α := ((jStar (W α) (underlyingRingSheaf X) ⋙
    jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj A
  map {β α} h := (NatTrans.mapHomologicalComplex
    (Stacks.ExtensionByZero.extensionRestrictionInclusion (underlyingRingSheaf X) (W β) (W α)
      (hmono β α (leOfHom h))) (ComplexShape.up ℤ)).app A
  map_id α := by
    rw [extensionRestrictionInclusion_refl, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp {γ β α} f g := by
    rw [← extensionRestrictionInclusion_trans (underlyingRingSheaf X) (W γ) (W β) (W α)
      (hmono γ β (leOfHom f)) (hmono β α (leOfHom g)), NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The prescribed complex on the stage `W α`: the restriction of the global complex. -/
def globalFiltrationLocal (α : E) :
    CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ :=
  ((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj A

/-- **Each stage of the filtration is the extension by zero of the prescribed complex.** -/
def globalFiltrationSupport (α : E) :
    (globalFiltrationSystem W hmono A).obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (globalFiltrationLocal W A α) :=
  Iso.refl _

/-- **Restricting a transition of the filtration to the smaller stage is an isomorphism.** -/
instance isIso_jStar_map_globalFiltrationSystem_map {β α : E} (h : β ≤ α) :
    IsIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((globalFiltrationSystem W hmono A).map h.hom)) := by
  have : ∀ n : ℤ, IsIso ((((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((globalFiltrationSystem W hmono A).map h.hom)).f n) :=
    fun n => isIso_jStar_map_extensionRestrictionInclusion (underlyingRingSheaf X)
      (W β) (W α) (hmono β α h) (A.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

end System

section Inhabitant

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β ≤ α → W β ≤ W α)
  (A : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)

/-- **Every binder of the assembly half of [Stacks, Tag 0D6B] is discharged by the filtration of
a global complex.** -/
theorem exists_glueing_of_globalFiltration (S : LocallyGiven X) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅
        DerivedCategory.Q.obj (globalFiltrationLocal W A α))
      (rho : ∀ (β α : E) (h : β ≤ α),
        (S.restriction (W β) (W α) (hmono β α h)).obj
            (DerivedCategory.Q.obj (globalFiltrationLocal W A α)) ≅
          DerivedCategory.Q.obj (globalFiltrationLocal W A β)),
      ∀ (β α : E) (h : β ≤ α),
        (S.restrictionComp (W β) (W α) ⊤ (hmono β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α) (hmono β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  exists_glueing_of_complexSystem W (globalFiltrationSystem W hmono A)
    (globalFiltrationLocal W A) (globalFiltrationSupport W hmono A) S
    (fun _ _ _ => inferInstance)
    (fun α => DerivedCategory.Q.obj (globalFiltrationLocal W A α)) (fun _ => Iso.refl _) hmono

end Inhabitant

end Stacks.DerivedGlueing

end
