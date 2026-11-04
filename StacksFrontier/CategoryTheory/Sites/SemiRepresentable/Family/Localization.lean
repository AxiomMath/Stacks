module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Basic
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.PullbackExact

/-!
# The localization morphism of a ringed semi-representable object

Let `X` be a ringed site and `K = {U i}` a semi-representable object of its underlying site.
The componentwise localization `C / K` carries the structure sheaf `O_K = j⁻¹ O_X`, and the
pair is tied to `X` by the localization morphism of ringed topoi
`j : (Sh(C / K), O_K) ⟶ (Sh(C), O_X)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.familyLocalizationToposMorphism`: the geometric morphism
  `Sh(C / K) ⟶ Sh(C)`.
* `AlgebraicGeometry.RingedSite.familyLocalizationStructureIso`: the identification of the
  inverse image of `O_X` with `O_K`.
* `AlgebraicGeometry.RingedSite.familyLocalizationMorphism`: the localization morphism `j` of
  ringed topoi.
* `AlgebraicGeometry.RingedSite.familyLowerShriek`: the lower shriek `j_!`, the left adjoint of
  restriction of sheaves of modules along the componentwise localization functor.
* `AlgebraicGeometry.RingedSite.familyComponentLowerShriek`: the extension by zero `j_{i,!}` of
  the `i`-th component, and
  `AlgebraicGeometry.RingedSite.familyComponentInclLowerShriek`: the lower shriek of the
  inclusion of the `i`-th component, which is the `i`-th summand inclusion of the
  decomposition `Mod(O_K) = ∏ Mod(O_{U i})`.

## Main results

* `AlgebraicGeometry.RingedSite.forgetRing_familyLocalizationMorphism_fSharpInverseImage`: the
  structure map of `j` is the identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.familyLocalizationMorphism_isFlat` and
  `AlgebraicGeometry.RingedSite.familyLocalizationMorphism_pullback_exact`: `j` is flat and
  `j^*` is exact.
* `AlgebraicGeometry.RingedSite.familyLocalizationMorphism_pullback_isRightAdjoint`: `j^*` has
  a left adjoint `j_!`, so that
  `AlgebraicGeometry.RingedToposHom.lowerShriekModules` is available for `j`.
* `AlgebraicGeometry.RingedSite.familyMorphism_pullback_isRightAdjoint`: the same for the
  morphism `f : K ⟶ L` of semi-representable objects, giving `f_!`.
* `AlgebraicGeometry.RingedSite.familyComponentIncl_comp_familyLocalizationFunctor`: the
  inclusion of the `i`-th component followed by the componentwise localization functor is the
  localization functor of `U i`.
* `AlgebraicGeometry.RingedSite.familyComponentInclLowerShriek_comp_familyLowerShriek`: on the
  `i`-th summand of the decomposition of part (2), `j_!` is the extension by zero `j_{i,!}`.

## Implementation notes

The localization datum feeding the localization functor has both of its semi-representable
objects equal to `K` and the identity between them, exactly as in
`AlgebraicGeometry.RingedSite.localizationStructureSheaf`; only its source object enters the
localization functor and its source topology.

The morphism is given as a morphism together with lemmas pinning down its inverse image and its
structure map, rather than as an element of a subtype as in
`AlgebraicGeometry.RingedSite.familyMorphism`: the existence of the lower shriek is proved by
recognising the inverse image as restriction along a continuous functor, and that recognition
has to hold definitionally rather than only up to a propositional equation.

Here `O_K` *is* the restriction of `O_X` along the componentwise localization functor, so the
structure map is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` and nothing more; on
underlying sheaves of sets it is the identity, which is the content of
`forgetRing_familyLocalizationMorphism_fSharpInverseImage`.

Flatness is stated as flatness of the inverse-image structure map,
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift`, which is what the exactness criterion
consumes and what the flatness predicate for a morphism of ringed topoi unfolds to.

The sections of the structure sheaf live in the universe `max u v w` containing the site and
the index type of the family: the right adjoint of restriction and the sheafification of
presheaves of abelian groups both need the sections to accommodate the site, and the left
adjoint of the inverse image of sheaves of modules needs `C / K` to be essentially small there.

`familyLowerShriek` is the left adjoint of *restriction* of sheaves of modules along the
componentwise localization functor, while
`familyLocalizationMorphism_pullback_isRightAdjoint` produces the left adjoint of the pullback
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of `j`. The two agree
because the structure map of `j` is an isomorphism — which is the source's parenthetical that
`O_K = j⁻¹O_C` — and that identification is
`AlgebraicGeometry.RingedSite.lowerShriekModules_iso_familyLowerShriek`, in
`StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.DirectSum`. The summand statement
below is about the restriction form, which is the one Stacks 03DI's extension by zero is
adjoint to.

The direct sum over the whole index type and the exactness of `j_!` are proved in
`StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.DirectSum`, where the site, its
morphisms and the module sections share a universe; what is proved here is the summandwise
identification `familyComponentInclLowerShriek_comp_familyLowerShriek`, which holds at
independent universes.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentable
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedSite

universe w v u

attribute [local instance] componentwiseTopology_hasSheafCompose_forget₂
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

attribute [local implicit_reducible] LocalizationSites.sourceTopology

/-- The localization datum of a semi-representable object `K`: both of its semi-representable
objects are `K` and the morphism between them is the identity, so that only its localization
functor `C / K ⥤ C` and its topology on `C / K` enter. These are the functor and the topology
that `O_K` is defined by. -/
abbrev familyLocalizationSites (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) : LocalizationSites.{w} X.C X.J :=
  ⟨K, K, 𝟙 K⟩

/-- The componentwise localization functor `C / K ⥤ C` is continuous from the componentwise
topology to `J`. This is
`CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_isContinuous` with the
topology on `C / K` spelled as a `componentwiseTopology`. -/
theorem familyLocalizationFunctor_isContinuous (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    (familyLocalizationSites X K).localizationFunctor.IsContinuous
      (componentwiseTopology X.J K) X.J :=
  LocalizationSites.localizationFunctor_isContinuous (familyLocalizationSites X K)

/-- The componentwise localization functor `C / K ⥤ C` is cocontinuous from the componentwise
topology to `J`. This is
`CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_isCocontinuous` with
the topology on `C / K` spelled as a `componentwiseTopology`. -/
theorem familyLocalizationFunctor_isCocontinuous (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    (familyLocalizationSites X K).localizationFunctor.IsCocontinuous
      (componentwiseTopology X.J K) X.J :=
  LocalizationSites.localizationFunctor_isCocontinuous (familyLocalizationSites X K)

attribute [local instance] familyLocalizationFunctor_isContinuous
  familyLocalizationFunctor_isCocontinuous

/-- **Stacks 0D9U, part (3).** The geometric morphism `Sh(C / K) ⟶ Sh(C)` underlying the
localization morphism of a semi-representable object `K`: its inverse image is restriction
along the componentwise localization functor `C / K ⥤ C` and its direct image is the right
adjoint of that restriction. -/
noncomputable def familyLocalizationToposMorphism (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    MorphismOfTopoi (Sheaf (componentwiseTopology X.J K) (Type (max u v w)))
      (Sheaf X.J (Type (max u v w))) where
  inverseImage := (familyLocalizationSites X K).localizationFunctor.sheafPushforwardContinuous
    (Type (max u v w)) (componentwiseTopology X.J K) X.J
  pushforward := (familyLocalizationSites X K).localizationFunctor.sheafPushforwardCocontinuous
    (Type (max u v w)) (componentwiseTopology X.J K) X.J
  adj := (familyLocalizationSites X K).localizationFunctor.sheafAdjunctionCocontinuous
    (Type (max u v w)) (componentwiseTopology X.J K) X.J
  preservesFiniteLimits := inferInstance

/-- The inverse image of the localization morphism is restriction along the componentwise
localization functor `C / K ⥤ C`. -/
theorem familyLocalizationToposMorphism_inverseImage (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    (familyLocalizationToposMorphism X K).inverseImage =
      (familyLocalizationSites X K).localizationFunctor.sheafPushforwardContinuous
        (Type (max u v w)) (componentwiseTopology X.J K) X.J :=
  rfl

/-- **Stacks 0D9U, part (3).** The structure map of the localization morphism, in inverse-image
form: the inverse image of `O_X` along restriction is the restriction of `O_X`, and that
restriction is `O_K`. -/
noncomputable def familyLocalizationStructureIso (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    (inverseImageCommRingFunctor (familyLocalizationToposMorphism X K)).obj
        (ringedTopos.{u, v, w} X).O ≅
      (localizationRingedTopos X K).O :=
  restrictionCommRingIso (componentwiseTopology X.J K) X.J
    (familyLocalizationSites X K).localizationFunctor X.O

/-- **Stacks 0D9U, part (3).** The localization morphism
`j : (Sh(C / K), O_K) ⟶ (Sh(C), O_X)` of ringed topoi attached to a semi-representable object
`K`: its geometric morphism is restriction along the componentwise localization functor and its
structure map is the canonical identity comparison of structure sheaves. -/
@[stacks 0D9U "part (3): the localization morphism j of ringed topoi"]
noncomputable def familyLocalizationMorphism (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    RingedToposHom (localizationRingedTopos X K) (ringedTopos.{u, v, w} X) where
  toToposHom := familyLocalizationToposMorphism X K
  fSharp := ((commRingImageAdjunction (familyLocalizationToposMorphism X K)).homEquiv _ _)
    (familyLocalizationStructureIso X K).hom

/-- The structure map of the localization morphism, in inverse-image form, is the isomorphism
`familyLocalizationStructureIso`. -/
private theorem familyLocalizationMorphism_fSharpInverseImage_eq
    (X : RingedSite.{u, v, max u v w}) (K : FormalCoproduct.{w} X.C) :
    (familyLocalizationMorphism X K).fSharpInverseImage =
      (familyLocalizationStructureIso X K).hom :=
  Equiv.symm_apply_apply _ _

/-- The structure map of the localization morphism is an isomorphism: it is the transpose of
the isomorphism `familyLocalizationStructureIso`. -/
instance isIso_familyLocalizationMorphism_fSharpInverseImage
    (X : RingedSite.{u, v, max u v w}) (K : FormalCoproduct.{w} X.C) :
    IsIso (familyLocalizationMorphism X K).fSharpInverseImage := by
  change IsIso
    (((commRingImageAdjunction (familyLocalizationToposMorphism X K)).homEquiv _ _).symm
      (((commRingImageAdjunction (familyLocalizationToposMorphism X K)).homEquiv _ _)
        (familyLocalizationStructureIso X K).hom))
  simpa only [Equiv.symm_apply_apply] using (familyLocalizationStructureIso X K).isIso_hom

/-- **Stacks 0D9U, part (3).** The structure map of the localization morphism is the canonical
identity comparison: on underlying sheaves of sets it is the identity, both sides being the
restriction of the underlying sheaf of sets of `O_X` along the componentwise localization
functor. -/
theorem forgetRing_familyLocalizationMorphism_fSharpInverseImage
    (X : RingedSite.{u, v, max u v w}) (K : FormalCoproduct.{w} X.C) :
    (localizationRingedTopos X K).forgetRing.map
        (familyLocalizationMorphism X K).fSharpInverseImage =
      𝟙 ((localizationRingedTopos X K).forgetRing.obj
        ((inverseImageCommRingFunctor (familyLocalizationToposMorphism X K)).obj
          (ringedTopos.{u, v, w} X).O)) := by
  rw [familyLocalizationMorphism_fSharpInverseImage_eq]
  rfl

/-- **Stacks 0D9U.** The localization morphism `j` is flat: its inverse-image structure map is
an isomorphism, and an isomorphism of sheaves of commutative rings is flat. -/
@[stacks 0D9U "part (3): j is flat"]
theorem familyLocalizationMorphism_isFlat (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      (familyLocalizationMorphism X K).fSharpInverseImage := by
  unfold AlgebraicGeometry.SheafOfModules.IsFlatMapULift
  exact SheafOfModules.isFlatMap_of_isIso
    ((AlgebraicGeometry.SheafOfModules.sheafULift (componentwiseTopology X.J K)).map
      (familyLocalizationMorphism X K).fSharpInverseImage)

/-- **Stacks 0D9U.** Pullback of sheaves of modules along the localization morphism is exact,
the morphism being flat. -/
@[stacks 0D9U "part (3): j^* is exact"]
theorem familyLocalizationMorphism_pullback_exact (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    exactFunctor _ _ (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := localizationRingedTopos X K) (Y := ringedTopos.{u, v, w} X)
      (familyLocalizationMorphism X K).toRingedToposModulesHom) :=
  Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (familyLocalizationMorphism X K) (familyLocalizationMorphism_isFlat X K)

/-- **Stacks 0D9U.** Pullback of sheaves of modules along the localization morphism has a left
adjoint `j_!`, namely `AlgebraicGeometry.RingedToposHom.lowerShriekModules` of that morphism:
the structure map is an isomorphism, and the inverse image of sheaves of modules is restriction
along the componentwise localization functor, which has a left adjoint because `C / K` is
essentially small. -/
@[stacks 0D9U "part (3): j^* has a left adjoint j_!"]
theorem familyLocalizationMorphism_pullback_isRightAdjoint (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    (familyLocalizationMorphism X K).toModulesHom.pullbackModules.IsRightAdjoint :=
  AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules
    (familyLocalizationMorphism X K)
    (Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction
      (componentwiseTopology X.J K) X.J
      (familyLocalizationSites X K).localizationFunctor _)

/-- **Stacks 0D9U.** Pullback of sheaves of modules along the morphism of ringed topoi attached
to a morphism `f : K ⟶ L` of semi-representable objects has a left adjoint `f_!`, namely
`AlgebraicGeometry.RingedToposHom.lowerShriekModules` of that morphism: the structure map is an
isomorphism and the inverse image of sheaves of modules is restriction along the componentwise
relocalization functor, which has a left adjoint because `C / K` is essentially small. -/
@[stacks 0D9U "part (3): f^* has a left adjoint f_!"]
theorem familyMorphism_pullback_isRightAdjoint (X : RingedSite.{u, v, max u v w})
    {K L : FormalCoproduct.{w} X.C} (f : K ⟶ L) :
    (familyMorphism.{w, v, u, u} X f).val.toModulesHom.pullbackModules.IsRightAdjoint := by
  let S : LocalizationSites.{w} X.C X.J := ⟨K, L, f⟩
  have hcont : S.relocalizationFunctor.IsContinuous
      (componentwiseTopology X.J K) (componentwiseTopology X.J L) :=
    LocalizationSites.relocalizationFunctor_isContinuous S
  have : IsIso (familyMorphism.{w, v, u, u} X f).val.fSharpInverseImage :=
    (familyMorphism.{w, v, u, u} X f).property.2.2
  exact AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules
    (familyMorphism.{w, v, u, u} X f).val
    (Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction
      (componentwiseTopology X.J K) (componentwiseTopology X.J L) S.relocalizationFunctor _)

/-! ### The components of `j_!`

Because the structure map of `j` is an isomorphism, `j^*` is restriction of sheaves of modules
along the componentwise localization functor; its left adjoint is the lower shriek below. The
site `C / K` is the disjoint union of the slice sites `C / U i`, and the inclusion of the
`i`-th component composed with the componentwise localization functor is the localization
functor `C / U i ⥤ C` of that component, so the `i`-th piece of `j_!` is the extension by zero
`j_{i,!}` of Stacks 03DI. -/

/-- The sheaf of rings `O_K` underlying the structure sheaf of the componentwise localization:
the restriction of the sheaf of rings of `X` along the componentwise localization functor. -/
noncomputable abbrev familyLocalizationRingSheaf (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    Sheaf (componentwiseTopology X.J K) RingCat.{max u v w} :=
  ((familyLocalizationSites X K).localizationFunctor.sheafPushforwardContinuous
    RingCat.{max u v w} (componentwiseTopology X.J K) X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The inclusion of the `i`-th component `C / U i ⥤ C / K` is continuous. This is
`CategoryTheory.SemiRepresentable.incl_isContinuous`. -/
theorem familyComponentIncl_isContinuous (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).IsContinuous
      (X.J.over (K.obj i)) (componentwiseTopology X.J K) :=
  incl_isContinuous X.J K i

/-- The inclusion of the `i`-th component followed by the componentwise localization functor —
which is the localization functor `C / U i ⥤ C` of that component — is continuous. -/
theorem familyComponentIncl_comp_isContinuous (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i ⋙
        (familyLocalizationSites X K).localizationFunctor).IsContinuous
      (X.J.over (K.obj i)) X.J :=
  have := familyComponentIncl_isContinuous X K i
  Functor.isContinuous_comp _ _ _ (componentwiseTopology X.J K) _

attribute [local instance] familyComponentIncl_isContinuous familyComponentIncl_comp_isContinuous

/-- **The inclusion of the `i`-th component followed by the componentwise localization functor
`C / K ⥤ C` is the localization functor `C / U i ⥤ C` of that component.** -/
theorem familyComponentIncl_comp_familyLocalizationFunctor (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i ⋙
        (familyLocalizationSites X K).localizationFunctor =
      Over.forget (K.obj i) :=
  rfl

/-- The sheaf of rings `O_{U i}` on the `i`-th component, obtained as the restriction of `O_K`
along the inclusion of that component. -/
noncomputable abbrev familyComponentRingSheaf (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    Sheaf (X.J.over (K.obj i)) RingCat.{max u v w} :=
  ((CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i
    ).sheafPushforwardContinuous RingCat.{max u v w} (X.J.over (K.obj i))
      (componentwiseTopology X.J K)).obj (familyLocalizationRingSheaf X K)

/-- **Stacks 0D9U, part (3).** The lower shriek `j_! : Mod(O_K) ⥤ Mod(O_C)`, the left adjoint
of restriction of sheaves of modules along the componentwise localization functor. That
restriction is `j^*` because the structure map of `j` is an isomorphism, which is
`isIso_familyLocalizationMorphism_fSharpInverseImage`. -/
noncomputable abbrev familyLowerShriek (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) :
    SheafOfModules.{max u v w} (familyLocalizationRingSheaf X K) ⥤
      SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pullback.{max u v w} (𝟙 (familyLocalizationRingSheaf X K))

/-- The lower shriek of the inclusion of the `i`-th component, left adjoint to restriction of
sheaves of modules along `C / U i ⥤ C / K`. Under the decomposition
`Mod(O_K) = ∏ Mod(O_{U i})` of part (2) this is the inclusion of the `i`-th summand. -/
noncomputable abbrev familyComponentInclLowerShriek (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    SheafOfModules.{max u v w} (familyComponentRingSheaf X K i) ⥤
      SheafOfModules.{max u v w} (familyLocalizationRingSheaf X K) :=
  SheafOfModules.pullback.{max u v w} (𝟙 (familyComponentRingSheaf X K i))

/-- **Stacks 03DI.** The extension by zero `j_{i,!} : Mod(O_{U i}) ⥤ Mod(O_C)` of the `i`-th
component, left adjoint to restriction of sheaves of modules along `Over.forget (U i)`. -/
noncomputable abbrev familyComponentLowerShriek (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    SheafOfModules.{max u v w}
        (((Over.forget (K.obj i)).sheafPushforwardContinuous RingCat.{max u v w}
          (X.J.over (K.obj i)) X.J).obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pullback.{max u v w} (F := Over.forget (K.obj i))
    (𝟙 (((Over.forget (K.obj i)).sheafPushforwardContinuous RingCat.{max u v w}
      (X.J.over (K.obj i)) X.J).obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The structure map of the composite restriction `C / U i ⥤ C / K ⥤ C` is the identity: both
restrictions are taken at the identity of the restricted sheaf of rings. -/
theorem familyComponent_structureMap_comp (X : RingedSite.{u, v, max u v w})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    (𝟙 (familyComponentRingSheaf X K i)) ≫
        ((CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i
          ).sheafPushforwardContinuous RingCat.{max u v w} (X.J.over (K.obj i))
            (componentwiseTopology X.J K)).map
          (𝟙 (familyLocalizationRingSheaf X K)) =
      𝟙 (familyComponentRingSheaf X K i) := by
  simp

/-- **Stacks 0D9U, part (3).** On the `i`-th summand of the decomposition
`Mod(O_K) = ∏ Mod(O_{U i})` the lower shriek `j_!` is the extension by zero `j_{i,!}` of that
component: the inclusion of the `i`-th component followed by the componentwise localization
functor is the localization functor of `U i`, so the two left adjoints agree. This is the
sentence of the source that `j_!` sends `(F i)` to `⨁ j_{i,!} F i`, read one summand at a
time. -/
@[stacks 0D9U "part (3): j_! is j_{i,!} on the i-th summand"]
noncomputable def familyComponentInclLowerShriek_comp_familyLowerShriek
    (X : RingedSite.{u, v, max u v w}) (K : FormalCoproduct.{w} X.C) (i : K.I) :
    familyComponentInclLowerShriek X K i ⋙ familyLowerShriek X K ≅
      familyComponentLowerShriek X K i :=
  SheafOfModules.pullbackComp _ _ ≪≫
    Adjunction.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction _)
      ((SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (((Over.forget (K.obj i)).sheafPushforwardContinuous RingCat.{max u v w}
          (X.J.over (K.obj i)) X.J).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).ofNatIsoRight
        (SheafOfModules.pushforwardCongr (F := Over.forget (K.obj i))
          (familyComponent_structureMap_comp X K i)).symm)

/-- **Stacks 03DJ.** The extension by zero `j_{i,!}` of a component is exact. This is the
exactness of extension by zero along a localization `C / U ⥤ C`, which asks the site,
its morphisms and the module sections to share a universe — the generality at which parts (1)
and (2) of this tag are formalized, namely `RingedSite.{u, u, u}`. -/
@[stacks 03DJ "the extension by zero of a component of a semi-representable object"]
theorem familyComponentLowerShriek_exact (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{u} X.C) (i : K.I) :
    exactFunctor _ _ (familyComponentLowerShriek X K i) :=
  Stacks.Sites.ExtensionByZero.extensionByZero_exact X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (K.obj i)

end AlgebraicGeometry.RingedSite

end
