module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference
public import StacksFrontier.Deformation.ToposThickening.Trivialization.SplittingOf

/-!
# The underlying extension class of a module over a trivialized first order thickening

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, and let `π : (Sh(D), O') ⟶ (Sh(C), O)` be a trivialization of it. The trivialization
splits the structure map, so `π^♯ : O ⟶ O'` lets every `O'`-module be read as an `O`-module.
Applied to an extension

```
  0 ⟶ K ⟶ F' ⟶ F ⟶ 0
```

of `O'`-modules whose outer terms are restricted from `O`-modules `F` and `K` (Stacks 08MB),
this gives a short exact sequence of `O`-modules with outer terms `K` and `F` themselves, hence
a class

```
  ξ_{F'} ∈ Ext¹_O(F, K).
```

## Main definitions

* `Deformation.ToposThickening.splitRestriction`: restriction of scalars along the splitting
  `π^♯ : O ⟶ O'` of the structure map supplied by the trivialization.
* `Deformation.ToposThickening.splitRestrictionRestrictScalarsIso`: restricting an `O`-module to
  `O'` along the structure map and back along the splitting returns it.
* `Deformation.ToposThickening.splitExtension`: the short complex of `O`-modules obtained from
  an extension over the thickening by restricting along the splitting and identifying the outer
  terms.
* `Deformation.ToposThickening.underlyingExtensionClass`: the class `ξ_{F'} ∈ Ext¹_O(F, K)` of
  Stacks 08MI of an extension over a trivialized thickening.

## Main results

* `Deformation.ToposThickening.splitExtension_shortExact`: the restricted sequence is short
  exact.

## References

* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe e v u w v' u' w' vv uu ww

namespace Stacks.SheafOfModules

section SplitRestriction

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{ww}}

/-- If `β : R ⟶ R'` and `α : R' ⟶ R` satisfy `β ≫ α = 𝟙 R`, then restricting an `R`-module to
`R'` along `α` and back to `R` along `β` returns it; the isomorphism is the identity on every
section. -/
noncomputable def restrictScalarsSplitIso (β : R ⟶ R') (α : R' ⟶ R) (h : β ≫ α = 𝟙 R)
    (M : SheafOfModules.{ww} R) :
    (SheafOfModules.restrictScalars β).obj ((SheafOfModules.restrictScalars α).obj M) ≅ M := by
  let e (U : Cᵒᵖ) :
      ((SheafOfModules.restrictScalars β).obj
        ((SheafOfModules.restrictScalars α).obj M)).val.obj U ≅ M.val.obj U := by
    have hU : RingHom.id _ = ((α.hom.app U).hom).comp ((β.hom.app U).hom) := by
      simpa using (congrArg (fun q ↦ (q.hom.app U).hom) h).symm
    exact (ModuleCat.restrictScalarsComp'App _ _ (RingHom.id _) hU (M.val.obj U)).symm ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U)
  refine ⟨⟨{ app U := (e U).hom, naturality _ := by ext; exact rfl }⟩,
    ⟨{ app U := (e U).inv, naturality _ := by ext; exact rfl }⟩, ?_, ?_⟩
  all_goals
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
    ext
    exact rfl

/-- The identification of a module with its restriction of scalars along a split pair of ring
maps is the identity on sections. -/
@[simp]
theorem restrictScalarsSplitIso_hom_val_app (β : R ⟶ R') (α : R' ⟶ R) (h : β ≫ α = 𝟙 R)
    (M : SheafOfModules.{ww} R) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars β).obj
      ((SheafOfModules.restrictScalars α).obj M)).val.obj U) :
    (restrictScalarsSplitIso β α h M).hom.val.app U x = x := rfl

end SplitRestriction

end Stacks.SheafOfModules

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}

/-- The splitting of the structure map of a first order thickening supplied by a trivialization,
as a map of the underlying sheaves of rings `O ⟶ O'`. -/
noncomputable def splittingRingHom (i : RingedToposHom X Y) (hi : FirstOrderThickening i)
    (π : Trivialization i) :
    Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf Y.O :=
  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map
    (Sheaf.homEquiv.symm (splittingFromTrivialization i hi π).1)

/-- The splitting followed by the structure map is the identity of `O`. -/
theorem splittingRingHom_comp (i : RingedToposHom X Y) (hi : FirstOrderThickening i)
    (π : Trivialization i) :
    splittingRingHom i hi π ≫
        (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp = 𝟙 _ := by
  let ρ := splittingFromTrivialization i hi π
  have hσ : Sheaf.homEquiv.symm ρ.1 ≫ i.fSharp = 𝟙 _ :=
    Sheaf.homEquiv.injective ((congrArg (ρ.1 ≫ ·) ρ.2.2.2).symm.trans ρ.2.1.id)
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ hσ).trans (CategoryTheory.Functor.map_id _ _))

/-- Restriction of scalars along the splitting `π^♯ : O ⟶ O'` of the structure map of a
trivialized first order thickening, reading a sheaf of `O'`-modules as a sheaf of `O`-modules. -/
noncomputable def splitRestriction (i : RingedToposHom X Y) (hi : FirstOrderThickening i)
    (π : Trivialization i) :
    SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w'}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  SheafOfModules.restrictScalars (splittingRingHom i hi π)

/-- Restriction of scalars along the splitting is additive. -/
instance splitRestriction_additive (i : RingedToposHom X Y) (hi : FirstOrderThickening i)
    (π : Trivialization i) : (splitRestriction i hi π).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars (splittingRingHom i hi π)).Additive

/-- Restriction of scalars along the splitting preserves finite limits. -/
instance splitRestriction_preservesFiniteLimits [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i) :
    PreservesFiniteLimits (splitRestriction i hi π) :=
  inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.restrictScalars (splittingRingHom i hi π)))

/-- Restriction of scalars along the splitting preserves finite colimits. -/
instance splitRestriction_preservesFiniteColimits [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i) :
    PreservesFiniteColimits (splitRestriction i hi π) :=
  inferInstanceAs
    (PreservesFiniteColimits (SheafOfModules.restrictScalars (splittingRingHom i hi π)))

/-- Reading an `O`-module as an `O'`-module along the structure map and then back along the
splitting returns it; the isomorphism is the identity on every section. -/
noncomputable def splitRestrictionRestrictScalarsIso (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    (splitRestriction i hi π).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj M) ≅ M :=
  Stacks.SheafOfModules.restrictScalarsSplitIso _ _ (splittingRingHom_comp i hi π) M

/-- The identification of an `O`-module with its double restriction of scalars is the identity
on sections. -/
@[simp]
theorem splitRestrictionRestrictScalarsIso_hom_val_app (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (U : Y.Cᵒᵖ)
    (x : ((splitRestriction i hi π).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj M)).val.obj U) :
    (splitRestrictionRestrictScalarsIso i hi π M).hom.val.app U x = x := rfl

section Extension

variable [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  (i) (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (E : Abelian.YonedaExtension
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The two maps of the extension, restricted along the splitting and composed with the
identifications of the outer terms, compose to zero. -/
theorem splitExtension_comp_zero :
    ((splitRestrictionRestrictScalarsIso i hi π K).inv ≫
        (splitRestriction i hi π).map E.f) ≫
      ((splitRestriction i hi π).map E.g ≫
        (splitRestrictionRestrictScalarsIso i hi π F).hom) = 0 := by
  have h : (splitRestriction i hi π).map E.f ≫ (splitRestriction i hi π).map E.g = 0 :=
    ((splitRestriction i hi π).map_comp E.f E.g).symm.trans
      ((congrArg (splitRestriction i hi π).map (yonedaExtension_comp_zero E)).trans
        ((splitRestriction i hi π).map_zero _ _))
  rw [Category.assoc, ← Category.assoc ((splitRestriction i hi π).map E.f), h,
    zero_comp, comp_zero]

/-- The extension `0 ⟶ K ⟶ F' ⟶ F ⟶ 0` of `O'`-modules, read as a short complex of
`O`-modules through the splitting supplied by the trivialization. Its outer terms are `K` and
`F` themselves. -/
noncomputable def splitExtension :
    ShortComplex (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :=
  ShortComplex.mk
    ((splitRestrictionRestrictScalarsIso i hi π K).inv ≫ (splitRestriction i hi π).map E.f)
    ((splitRestriction i hi π).map E.g ≫ (splitRestrictionRestrictScalarsIso i hi π F).hom)
    (splitExtension_comp_zero i hi π F K E)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The first map of `splitExtension` is the restriction of the first map of the extension,
precomposed with the identification of `K` with its double restriction. -/
@[simp]
theorem splitExtension_f : (splitExtension i hi π F K E).f =
    (splitRestrictionRestrictScalarsIso i hi π K).inv ≫ (splitRestriction i hi π).map E.f :=
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The second map of `splitExtension` is the restriction of the second map of the extension,
followed by the identification of the double restriction of `F` with `F`. -/
@[simp]
theorem splitExtension_g : (splitExtension i hi π F K E).g =
    (splitRestriction i hi π).map E.g ≫ (splitRestrictionRestrictScalarsIso i hi π F).hom :=
  rfl

/-- The restriction of an extension over a trivialized first order thickening along the
splitting is again short exact. -/
theorem splitExtension_shortExact : (splitExtension i hi π F K E).ShortExact := by
  have hSE : (ShortComplex.mk (C := SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) E.f E.g
        (yonedaExtension_comp_zero E)).ShortExact :=
    yonedaExtension_shortExact E
  have hMap := hSE.map_of_exact (splitRestriction i hi π)
  refine ShortComplex.shortExact_of_iso ?_ hMap
  refine ShortComplex.isoMk (splitRestrictionRestrictScalarsIso i hi π K) (Iso.refl _)
    (splitRestrictionRestrictScalarsIso i hi π F) ?_ ?_
  · exact (Iso.hom_inv_id_assoc (splitRestrictionRestrictScalarsIso i hi π K)
      ((splitRestriction i hi π).map E.f)).trans (Category.comp_id _).symm
  · exact Category.id_comp _

/-- The class `ξ_{F'} ∈ Ext¹_O(F, K)` of Stacks 08MI of an extension of `F` by `K` over a
trivialized first order thickening of ringed topoi: the class of the short exact sequence of
`O`-modules `splitExtension` obtained by restricting the extension along the splitting. -/
noncomputable def underlyingExtensionClass
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))] :
    Abelian.Ext F K 1 :=
  (splitExtension_shortExact i hi π F K E).extClass

end Extension

end Deformation.ToposThickening

end
