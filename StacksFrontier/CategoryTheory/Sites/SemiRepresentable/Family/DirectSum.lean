module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroOverMap
public import StacksFrontier.CategoryTheory.Limits.PiCoproductAdjunction
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Localization
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.ModuleProduct

/-!
# The lower shriek of a semi-representable localization is the sum of the component ones

Let `X` be a ringed site and `K = {U i}` a semi-representable object of its underlying site.
The decomposition `Mod(O_K) = ∏ Mod(O_{U i})` of Stacks 0D9U part (2) identifies a sheaf of
`O_K`-modules with the family of its restrictions to the components. Under that identification
the lower shriek `j_!` of part (3) is

`j_! (F i) = ⨁ i, j_{i,!} (F i)`,

because `j^*` is the family of the `j_i^*` and the left adjoint of a functor into a product is
the coproduct of the left adjoints of its components. Since every `j_{i,!}` is exact
(Stacks 03DJ) and coproducts of sheaves of modules are exact (Grothendieck's AB4, which holds
because `Mod(O_C)` is Grothendieck abelian), `j_!` is exact.

## Main definitions

* `AlgebraicGeometry.RingedSite.componentwiseModuleRestrictionEquivalence`: the decomposition
  `Mod(O_K) ≌ ∏ Mod(O_{U i})` of part (2), as an equivalence whose functor is the componentwise
  restriction.
* `AlgebraicGeometry.RingedSite.familyDirectSumLowerShriek`: the functor
  `M ↦ ⨁ i, j_{i,!} (M|_{U i})`.

## Main results

* `AlgebraicGeometry.RingedSite.familyRestrComponentIso`: `j^*` followed by restriction to the
  `i`-th component is `j_i^*`.
* `AlgebraicGeometry.RingedSite.familyLowerShriek_iso_directSum`: **the direct-sum formula**,
  `j_! ≅ ⨁ i, j_{i,!} ∘ (-|_{U i})`.
* `AlgebraicGeometry.RingedSite.familyLowerShriek_exact`: `j_!` is exact.
* `AlgebraicGeometry.RingedSite.lowerShriekModules_iso_familyLowerShriek` and
  `AlgebraicGeometry.RingedSite.lowerShriekModules_exact`: the left adjoint of the *pullback*
  `j^*` of sheaves of modules — which is what the source means by `j_!` — differs from
  `familyLowerShriek` by an equivalence, and is therefore exact as well.

## Implementation notes

**A subtlety for anything touching relocalization.** The sheaf of rings obtained by restricting
`O_L` along the componentwise relocalization functor `v : C / K ⥤ C / L` is `O_K`, but **this
is not true by `rfl`**. Both `v` and the localization functors are built with
`CategoryTheory.Sigma.desc`, whose `map` field reduces only once the index is in constructor
form, so `v ⋙ j_L = j_K` holds by `CategoryTheory.Functor.hext` and not definitionally — even
though every *component* of the two restricted sheaves of rings does agree on the nose.
`AlgebraicGeometry.RingedSite.familyMorphism` builds exactly this comparison internally, as a
local `ecomp`, and does not export it, which is why it is easy to assume the identification is
free. It is proved here as an equality,
`AlgebraicGeometry.RingedSite.familyRelocalizationRingSheaf_eq`, and the structure map of
`f^*` below is its `eqToHom`.

The site, its morphisms and the module sections share a universe here, `RingedSite.{u, u, u}`:
that is the generality at which parts (1) and (2) of the tag are formalized, it is what Mathlib's
`IsGrothendieckAbelian (SheafOfModules R)` — hence AB4 — asks for, and it is what the
exactness of extension by zero (Stacks 03DJ) asks for.

The abstract half of the argument is
`CategoryTheory.Limits.piCoproductAdjunction` and
`CategoryTheory.Limits.preservesFiniteLimits_piCoproduct`; what is added here is the
identification of `j^*` with the family of the `j_i^*`, which rests on the componentwise
localization functor restricted to the `i`-th component being the localization functor of
`U i`.

## Morphisms of semi-representable objects

The same argument runs for `f : K ⟶ L`: `f^*` is restriction along the componentwise
relocalization functor `v`, whose restriction to the `i`-th component of `K` is
`Sigma.incl i ⋙ v = Over.map (f.φ i) ⋙ Sigma.incl (f.f i)` — by `rfl`, both being
`Sigma.desc`. So the `i`-th summand of `f_!` is extension by zero along a relocalization
(`Stacks.Sites.ExtensionByZero.overMap_extensionByZero_exact`, which is Stacks 03DJ transported
along the iterated-slice equivalence) followed by the lower shriek of a component inclusion
(`familyComponentInclLowerShriek_exact`), and both are exact; so `f_!` is exact.

`AlgebraicGeometry.RingedSite.morphismRestr` is `f^*` in its restriction reading: restriction
of sheaves of modules along `v`, with the canonical comparison of structure sheaves as its
structure map, which is what the pullback of Stacks 03D6 comes to when that structure map is an
isomorphism — the source's own parenthetical `O_K = f^{-1}O_L`. For `j` the identification of
that reading with `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` is made
explicitly, in `lowerShriekModules_iso_familyLowerShriek` and `lowerShriekModules_exact`. The
same identification for `f` is not made: it needs
`pushforward (𝟙 …) ⋙ pushforward (F := 𝟭) (eqToHom …)` to be compared with `morphismRestr`,
which is `SheafOfModules.pushforwardComp` at the identity functor plus
`SheafOfModules.pushforwardPushforwardEquivalence` of the identity equivalence. It changes no
mathematics, only the spelling of `f^*`.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentable
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedSite

universe w v u

attribute [local instance] componentwiseTopology_hasSheafCompose_forget₂
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  familyLocalizationFunctor_isContinuous
  familyComponentIncl_isContinuous familyComponentIncl_comp_isContinuous
  familyLocalizationMorphism_pullback_isRightAdjoint

/-- The inclusion of the `i`-th component is continuous, with the topology of the localized
ringed site spelled as `(X.over (K.obj i)).J`. This is the spelling the componentwise
restriction of part (2) is stated in. -/
theorem overComponentIncl_isContinuous (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{u} X.C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).IsContinuous
      (X.over (K.obj i)).J (componentwiseTopology X.J K) :=
  incl_isContinuous X.J K i

attribute [local instance] overComponentIncl_isContinuous

variable (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{u} X.C)

/-- **Stacks 0D9U, part (2).** The decomposition `Mod(O_K) = ∏ Mod(O_{U i})`, as an
equivalence. Its functor is the componentwise restriction, by
`AlgebraicGeometry.RingedSite.moduleSheavesProductEquivalence`. -/
noncomputable abbrev componentwiseModuleRestrictionEquivalence :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O)) ≌
      ((i : K.I) →
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))) :=
  (moduleSheavesProductEquivalence X K).val

/-- The componentwise restriction is the functor of the equivalence of part (2). -/
theorem componentwiseModuleRestrictionEquivalence_functor :
    (componentwiseModuleRestrictionEquivalence X K).functor =
      componentwiseModuleRestriction X K :=
  (moduleSheavesProductEquivalence X K).property

/-- `j_i^*`, restriction of sheaves of modules along the localization `C / U i ⥤ C`. -/
noncomputable abbrev familyComponentRestr (i : K.I) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :=
  restrictionModules (X.J.over (K.obj i)) X.J (Over.forget (K.obj i))
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- `j^*`, restriction of sheaves of modules along the componentwise localization functor. -/
noncomputable abbrev familyRestr :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O)) :=
  restrictionModules (componentwiseTopology X.J K) X.J
    (familyLocalizationSites X K).localizationFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **`j^*` followed by restriction to the `i`-th component is `j_i^*`.** Restriction along a
composite of continuous functors is the composite of the restrictions, and the inclusion of the
`i`-th component followed by the componentwise localization functor is the localization functor
of `U i`. -/
noncomputable def familyRestrComponentIso (i : K.I) :
    familyRestr X K ⋙
        restrictionModules (X.J.over (K.obj i)) (componentwiseTopology X.J K)
          (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i)
          (familyLocalizationRingSheaf X K) ≅
      familyComponentRestr X K i :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr (F := Over.forget (K.obj i))
      (familyComponent_structureMap_comp X K i)

/-- `j^*` followed by the componentwise restriction is the family of the `j_i^*`. -/
noncomputable def familyRestrCompRestrictionIso :
    familyRestr X K ⋙ componentwiseModuleRestriction X K ≅
      Functor.pi' (familyComponentRestr X K) :=
  NatIso.pi' fun i => familyRestrComponentIso X K i

/-- `j^*` followed by the decomposition of part (2) is the family of the `j_i^*`. -/
noncomputable def familyRestrCompEquivalenceIso :
    familyRestr X K ⋙ (componentwiseModuleRestrictionEquivalence X K).functor ≅
      Functor.pi' (familyComponentRestr X K) :=
  eqToIso (by rw [componentwiseModuleRestrictionEquivalence_functor]) ≪≫
    familyRestrCompRestrictionIso X K

/-- The componentwise extensions by zero, as a family of left adjoints of the `j_i^*`. -/
noncomputable def familyComponentLowerShriekAdjunction (i : K.I) :
    familyComponentLowerShriek X K i ⊣ familyComponentRestr X K i :=
  SheafOfModules.pullbackPushforwardAdjunction _

/-- **The functor `M ↦ ⨁ i, j_{i,!} (M|_{U i})`**, read on the product decomposition of
part (2). -/
noncomputable abbrev familyDirectSumLowerShriek :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O)) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (componentwiseModuleRestrictionEquivalence X K).functor ⋙
    piCoproduct (familyComponentLowerShriek X K)

/-- The direct sum of the componentwise extensions by zero is left adjoint to `j^*`. -/
noncomputable def familyDirectSumLowerShriekAdjunction :
    familyDirectSumLowerShriek X K ⊣ familyRestr X K :=
  ((componentwiseModuleRestrictionEquivalence X K).toAdjunction.comp
    (piCoproductAdjunction (familyComponentRestr X K) (familyComponentLowerShriek X K)
      (familyComponentLowerShriekAdjunction X K))).ofNatIsoRight
    (Functor.isoWhiskerRight (familyRestrCompEquivalenceIso X K).symm
        (componentwiseModuleRestrictionEquivalence X K).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (familyRestr X K)
        (componentwiseModuleRestrictionEquivalence X K).unitIso.symm ≪≫
      (familyRestr X K).rightUnitor)

/-- **Stacks 0D9U, part (3): the direct-sum formula.** In terms of the product decomposition of
part (2), `j_!` sends a family `(F i)` to `⨁ i, j_{i,!} F i`: both are left adjoint to `j^*`. -/
@[stacks 0D9U "part (3): j_! is the direct sum of the j_{i,!}"]
noncomputable def familyLowerShriek_iso_directSum :
    familyLowerShriek X K ≅ familyDirectSumLowerShriek X K :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction (𝟙 (familyLocalizationRingSheaf X K)))
    (familyDirectSumLowerShriekAdjunction X K)

/-- Every component extension by zero preserves finite limits, by Stacks 03DJ. -/
theorem preservesFiniteLimits_familyComponentLowerShriek (i : K.I) :
    PreservesFiniteLimits (familyComponentLowerShriek X K i) :=
  ((exactFunctor_iff _).mp (familyComponentLowerShriek_exact X K i)).1

/-- The direct sum of the componentwise extensions by zero preserves finite limits: each
summand does, and coproducts of sheaves of modules are exact because `Mod(O_C)` is Grothendieck
abelian. -/
theorem preservesFiniteLimits_familyDirectSumLowerShriek :
    PreservesFiniteLimits (familyDirectSumLowerShriek X K) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _
    (componentwiseModuleRestrictionEquivalence X K).functor
    (piCoproduct (familyComponentLowerShriek X K)) inferInstance
    (preservesFiniteLimits_piCoproduct _
      (preservesFiniteLimits_familyComponentLowerShriek X K))

/-- **Stacks 0D9U, part (3).** The lower shriek `j_!` is exact: it preserves finite colimits
because it is a left adjoint, and finite limits because it is the direct sum of the exact
functors `j_{i,!}`. -/
@[stacks 0D9U "part (3): j_! is exact"]
theorem familyLowerShriek_exact : exactFunctor _ _ (familyLowerShriek X K) := by
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (familyLowerShriek_iso_directSum X K).symm
      (preservesFiniteLimits_familyDirectSumLowerShriek X K)
  · have : PreservesColimitsOfSize.{0, 0} (familyLowerShriek X K) :=
      (SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (familyLocalizationRingSheaf X K))).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _

/-! ### `j_!` is the left adjoint of the pullback of modules along `j`

`familyLowerShriek` is the left adjoint of *restriction* of sheaves of modules along the
componentwise localization functor, while the source's `j^*` is the pullback of sheaves of
modules along the morphism of ringed topoi `j`. The two differ by two restrictions of scalars
along isomorphisms — the comparison of the inverse image of a sheaf of rings with its
restriction, and the structure map of `j`, which is invertible — so their left adjoints differ
by an equivalence, and in particular one is exact exactly when the other is. -/

section Pullback

variable (X : RingedSite.{u, v, max u v w}) (K : FormalCoproduct.{w} X.C)

/-- The structure map of `j`, in the `RingCat` form that extension of scalars consumes, is an
isomorphism. -/
theorem isIso_familyLocalizationMorphism_toModulesHom_fSharpInverseImage :
    IsIso (familyLocalizationMorphism X K).toModulesHom.fSharpInverseImage :=
  AlgebraicGeometry.RingedToposHom.isIso_toModulesHom_fSharpInverseImage
    (familyLocalizationMorphism X K)

attribute [local instance] isIso_familyLocalizationMorphism_toModulesHom_fSharpInverseImage

/-- The two restrictions of scalars by which `j^*` differs from restriction of modules along
the componentwise localization functor: first along the comparison of the inverse image of the
sheaf of rings with its restriction, then along the inverse of the structure map of `j`. Both
are isomorphisms, so this is an equivalence. -/
noncomputable abbrev familyPullbackScalars :
    SheafOfModules.{max u v w} (familyLocalizationRingSheaf X K) ⥤
      SheafOfModules.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (localizationRingedTopos X K).J))
          (localizationRingedTopos X K).O) :=
  SheafOfModules.restrictScalars
      (restrictionRingIso (componentwiseTopology X.J K) X.J
        (familyLocalizationSites X K).localizationFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom ⋙
    SheafOfModules.restrictScalars
      (asIso (familyLocalizationMorphism X K).toModulesHom.fSharpInverseImage).inv

/-- The composite of the two restrictions of scalars `familyPullbackScalars` is an
equivalence. -/
instance isEquivalence_familyPullbackScalars :
    (familyPullbackScalars X K).IsEquivalence := by
  have h1 : (SheafOfModules.restrictScalars
      (restrictionRingIso (componentwiseTopology X.J K) X.J
        (familyLocalizationSites X K).localizationFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom).IsEquivalence :=
    inferInstance
  have h2 : (SheafOfModules.restrictScalars (asIso
      (familyLocalizationMorphism X K).toModulesHom.fSharpInverseImage).inv).IsEquivalence :=
    inferInstance
  let e1 := (SheafOfModules.restrictScalars
    (restrictionRingIso (componentwiseTopology X.J K) X.J
      (familyLocalizationSites X K).localizationFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom).asEquivalence
  let e2 := (SheafOfModules.restrictScalars (asIso
    (familyLocalizationMorphism X K).toModulesHom.fSharpInverseImage).inv).asEquivalence
  exact (e1.trans e2).isEquivalence_functor

/-- The equivalence `familyPullbackScalars`. -/
noncomputable abbrev familyPullbackScalarsEquivalence :
    SheafOfModules.{max u v w} (familyLocalizationRingSheaf X K) ≌
      SheafOfModules.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (localizationRingedTopos X K).J))
          (localizationRingedTopos X K).O) :=
  (familyPullbackScalars X K).asEquivalence

/-- **`j^*` is restriction of sheaves of modules along the componentwise localization functor,
followed by an equivalence.** The pullback of Stacks 03D6 is the inverse image followed by
extension of scalars along the structure map; the inverse image is restriction up to
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, and extension of scalars along the
invertible structure map is restriction of scalars along its inverse. -/
noncomputable def pullbackModulesIsoFamilyRestrComp :
    restrictionModules (componentwiseTopology X.J K) X.J
          (familyLocalizationSites X K).localizationFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        familyPullbackScalars X K ≅
      (familyLocalizationMorphism X K).toModulesHom.pullbackModules :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (restrictionModuleIso (componentwiseTopology X.J K) X.J
        (familyLocalizationSites X K).localizationFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm
      (SheafOfModules.restrictScalars
        (asIso (familyLocalizationMorphism X K).toModulesHom.fSharpInverseImage).inv) ≪≫
    Functor.isoWhiskerLeft
      (inverseImageModules (familyLocalizationMorphism X K).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
        (familyLocalizationMorphism X K).toModulesHom).symm

/-- The lower shriek `j_!` of the morphism of ringed topoi — the left adjoint of `j^*` — is the
left adjoint of restriction of modules, composed with the inverse of
`familyPullbackScalarsEquivalence`. -/
noncomputable def familyLocalizationLowerShriekAdjunction :
    (familyPullbackScalarsEquivalence X K).inverse ⋙ familyLowerShriek X K ⊣
      (familyLocalizationMorphism X K).toModulesHom.pullbackModules :=
  (((familyPullbackScalarsEquivalence X K).symm.toAdjunction).comp
    (SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (familyLocalizationRingSheaf X K)))).ofNatIsoRight
    (pullbackModulesIsoFamilyRestrComp X K)

/-- **Stacks 0D9U, part (3).** The lower shriek of the morphism of ringed topoi `j` — the left
adjoint of the pullback `j^*` of sheaves of modules, which is what the source means by `j_!` —
is `familyLowerShriek` up to the equivalence by which `j^*` differs from restriction. -/
@[stacks 0D9U "part (3): j_! is the left adjoint of the pullback of modules along j"]
noncomputable def lowerShriekModules_iso_familyLowerShriek :
    (familyLocalizationMorphism X K).lowerShriekModules ≅
      (familyPullbackScalarsEquivalence X K).inverse ⋙ familyLowerShriek X K :=
  Adjunction.leftAdjointUniq
    (AlgebraicGeometry.RingedToposHom.lowerShriekAdjPullbackModules
      (familyLocalizationMorphism X K))
    (familyLocalizationLowerShriekAdjunction X K)

end Pullback

/-- A functor isomorphic to a composite of exact functors is exact. -/
private theorem exactFunctor_of_comp_iso {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H) (hF : exactFunctor C D F)
    (hG : exactFunctor D E G) : exactFunctor C E H := by
  rw [exactFunctor_iff] at hF hG
  have := hF.1
  have := hF.2
  have := hG.1
  have := hG.2
  exact ObjectProperty.prop_of_iso _ e
    ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)

/-- **Stacks 0D9U, part (3).** The lower shriek of the morphism of ringed topoi `j`, the left
adjoint of `j^*`, is exact: it is `familyLowerShriek`, which is exact, composed with an
equivalence. -/
@[stacks 0D9U "part (3): the left adjoint of j^* is exact"]
theorem lowerShriekModules_exact (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{u} X.C) :
    exactFunctor _ _ ((familyLocalizationMorphism X K).lowerShriekModules) := by
  exact exactFunctor_of_comp_iso (lowerShriekModules_iso_familyLowerShriek X K).symm
    ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩) (familyLowerShriek_exact X K)

/-! ### The lower shriek of a component inclusion

Under the decomposition `Mod(O_K) = ∏ Mod(O_{U i})` of part (2), restriction to the `j`-th
component is evaluation at `j`, so its left adjoint is concentration at `j`: extension by zero
into the product. That left adjoint is exact. -/

section ComponentInclusion

open scoped Classical

variable (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{u} X.C)

/-- The componentwise restriction of part (2) is the family of the restrictions to the
components. -/
theorem componentwiseModuleRestriction_eq :
    componentwiseModuleRestriction X K =
      Functor.pi' (fun j => restrictionModules (X.J.over (K.obj j))
        (componentwiseTopology X.J K)
        (CategoryTheory.Sigma.incl (C := fun k : K.I => Over (K.obj k)) j)
        (familyLocalizationRingSheaf X K)) :=
  rfl

/-- Restriction of modules to the `j`-th component is the `j`-th component of the decomposition
of part (2). -/
noncomputable def componentRestrIsoEval (j : K.I) :
    (componentwiseModuleRestrictionEquivalence X K).functor ⋙
        Pi.eval (fun k =>
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj k)).O))) j ≅
      restrictionModules (X.J.over (K.obj j)) (componentwiseTopology X.J K)
        (CategoryTheory.Sigma.incl (C := fun k : K.I => Over (K.obj k)) j)
        (familyLocalizationRingSheaf X K) :=
  eqToIso (by
      rw [componentwiseModuleRestrictionEquivalence_functor,
        componentwiseModuleRestriction_eq]
      rfl) ≪≫
    Functor.pi'CompEval (fun k => restrictionModules (X.J.over (K.obj k))
      (componentwiseTopology X.J K)
      (CategoryTheory.Sigma.incl (C := fun l : K.I => Over (K.obj l)) k)
      (familyLocalizationRingSheaf X K)) j

/-- Concentration at `j`, followed by the decomposition of part (2) read backwards, is left
adjoint to restriction to the `j`-th component. -/
noncomputable def componentInclLowerShriekAdjunction (j : K.I) :
    concentrate
          (B := fun k =>
            SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj k)).O)))
          j ⋙
        (componentwiseModuleRestrictionEquivalence X K).inverse ⊣
      restrictionModules (X.J.over (K.obj j)) (componentwiseTopology X.J K)
        (CategoryTheory.Sigma.incl (C := fun k : K.I => Over (K.obj k)) j)
        (familyLocalizationRingSheaf X K) :=
  ((concentrateAdjunction j).comp
    (componentwiseModuleRestrictionEquivalence X K).symm.toAdjunction).ofNatIsoRight
      (componentRestrIsoEval X K j)

/-- **Stacks 0D9U, part (2).** The lower shriek of the inclusion of the `j`-th component is
concentration at `j` read through the decomposition of part (2). -/
noncomputable def familyComponentInclLowerShriek_iso (j : K.I) :
    familyComponentInclLowerShriek X K j ≅
      concentrate
          (B := fun k =>
            SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj k)).O)))
          j ⋙
        (componentwiseModuleRestrictionEquivalence X K).inverse :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction (𝟙 (familyComponentRingSheaf X K j)))
    (componentInclLowerShriekAdjunction X K j)

/-- **The lower shriek of a component inclusion is exact**: it is concentration at that index,
which is exact, followed by an equivalence. -/
theorem familyComponentInclLowerShriek_exact (j : K.I) :
    exactFunctor _ _ (familyComponentInclLowerShriek X K j) := by
  have hconc : PreservesFiniteLimits
      (concentrate
        (B := fun k =>
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj k)).O)))
          j) :=
    preservesFiniteLimits_concentrate j
  have hcolim : PreservesColimitsOfSize.{0, 0}
      (concentrate
        (B := fun k =>
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj k)).O)))
          j) :=
    (concentrateAdjunction j).leftAdjoint_preservesColimits
  have hinv : exactFunctor _ _ (componentwiseModuleRestrictionEquivalence X K).inverse :=
    (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  exact exactFunctor_of_comp_iso (familyComponentInclLowerShriek_iso X K j).symm
    ((exactFunctor_iff _).2
      ⟨hconc, @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _ hcolim⟩)
    hinv

end ComponentInclusion

/-! ### The relocalization comparison

The sheaf of rings obtained by restricting `O_L` along the componentwise relocalization functor
`v : C / K ⥤ C / L` is `O_K`, but **not by `rfl`**: the underlying site functors satisfy
`v ⋙ j_L = j_K` only by `CategoryTheory.Functor.hext`, both being built with
`CategoryTheory.Sigma.desc`, whose `map` field reduces only once the index is in constructor
form. `AlgebraicGeometry.RingedSite.familyMorphism` builds this comparison internally and does
not export it, so it is proved again here, as an *equality* of sheaves of rings. -/

section Relocalization

variable (X : RingedSite.{u, u, u}) {K L : FormalCoproduct.{u} X.C} (f : K ⟶ L)

/-- The localization datum of a morphism of semi-representable objects: `K`, `L` and `f`. Its
relocalization functor is `v : C / K ⥤ C / L`. -/
abbrev familyRelocalizationSites : LocalizationSites.{u} X.C X.J := ⟨K, L, f⟩

/-- The componentwise relocalization functor is continuous for the componentwise topologies. -/
theorem familyRelocalizationFunctor_isContinuous :
    (familyRelocalizationSites X f).relocalizationFunctor.IsContinuous
      (componentwiseTopology X.J K) (componentwiseTopology X.J L) :=
  LocalizationSites.relocalizationFunctor_isContinuous _

attribute [local instance] familyRelocalizationFunctor_isContinuous

/-- **The componentwise relocalization functor followed by the localization functor of `L` is
the localization functor of `K`.** On the component indexed by `i` both are the slice
projection of `C / U i`. This holds by `CategoryTheory.Functor.hext` and not by `rfl`. -/
theorem familyRelocalization_comp_localizationFunctor :
    (familyRelocalizationSites X f).relocalizationFunctor ⋙
        (familyLocalizationSites X L).localizationFunctor =
      (familyLocalizationSites X K).localizationFunctor := by
  refine CategoryTheory.Functor.hext (fun Y => ?_) (fun Y Z a => ?_)
  · cases Y with
    | mk i V => rfl
  · cases Y with
    | mk i V =>
      cases Z with
      | mk j W =>
        cases a
        change (Over.forget (L.obj (f.f i))).map ((Over.map (f.φ i)).map _) ≍
          (Over.forget (K.obj i)).map _
        simp [Over.map_map_left]

/-- `O_K` read as the restriction of `O_L` along the componentwise relocalization functor. -/
noncomputable abbrev familyRelocalizationRingSheaf :
    Sheaf (componentwiseTopology X.J K) RingCat.{u} :=
  ((familyRelocalizationSites X f).relocalizationFunctor.sheafPushforwardContinuous
    RingCat.{u} (componentwiseTopology X.J K) (componentwiseTopology X.J L)).obj
      (familyLocalizationRingSheaf X L)

/-- **The restriction of `O_L` along the relocalization functor is `O_K`.** An equality of
sheaves of rings, obtained from
`familyRelocalization_comp_localizationFunctor` — and *not* available by `rfl`. -/
theorem familyRelocalizationRingSheaf_eq :
    familyRelocalizationRingSheaf X f = familyLocalizationRingSheaf X K := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  show ((familyRelocalizationSites X f).relocalizationFunctor ⋙
      (familyLocalizationSites X L).localizationFunctor).op ⋙
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    (familyLocalizationSites X K).localizationFunctor.op ⋙
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
  rw [familyRelocalization_comp_localizationFunctor]

end Relocalization

/-! ### `f_!` is the sum of the componentwise lower shrieks, and is exact

For a morphism `f : K ⟶ L` of semi-representable objects, `f^*` is restriction along the
componentwise relocalization functor `v`, whose restriction to the `i`-th component of `K` is
`Over.map (f.φ i)` followed by the inclusion of the `f i`-th component of `L`. So the `i`-th
summand of `f_!` is extension by zero along a relocalization followed by the lower shriek of a
component inclusion, and both of those are exact. -/

section MorphismLowerShriek

variable (X : RingedSite.{u, u, u}) {K L : FormalCoproduct.{u} X.C} (f : K ⟶ L)

attribute [local instance] familyRelocalizationFunctor_isContinuous

/-- The inclusion of the `i`-th component of `K`, followed by the relocalization functor; it is
`Over.map (f.φ i)` followed by the inclusion of the `f i`-th component of `L`. -/
theorem morphismComponentFunctor_isContinuous (i : K.I) :
    (Over.map (f.φ i) ⋙
        CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i)).IsContinuous
      (X.J.over (K.obj i)) (componentwiseTopology X.J L) :=
  have := familyComponentIncl_isContinuous X L (f.f i)
  Functor.isContinuous_comp _ _ _ (X.J.over (L.obj (f.f i))) _

/-- The same, with the source topology spelled as the topology of the localized ringed site,
which is the spelling the componentwise restriction of part (2) is stated in. -/
theorem morphismComponentFunctor_isContinuous' (i : K.I) :
    (Over.map (f.φ i) ⋙
        CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i)).IsContinuous
      (X.over (K.obj i)).J (componentwiseTopology X.J L) :=
  morphismComponentFunctor_isContinuous X f i

attribute [local instance] morphismComponentFunctor_isContinuous
  morphismComponentFunctor_isContinuous'

/-- **`f^*`**, restriction of sheaves of modules along the componentwise relocalization
functor. Its structure map is the `eqToHom` of the comparison
`familyRelocalizationRingSheaf_eq`, which is where the non-definitional identification of the
two readings of `O_K` is absorbed. -/
noncomputable abbrev morphismRestr :
    SheafOfModules.{u} (familyLocalizationRingSheaf X L) ⥤
      SheafOfModules.{u} (familyLocalizationRingSheaf X K) :=
  SheafOfModules.pushforward.{u}
    (F := (familyRelocalizationSites X f).relocalizationFunctor)
    (eqToHom (familyRelocalizationRingSheaf_eq X f).symm)

/-- `f_i^*`: restriction of modules along the inclusion of the `i`-th component of `K` followed
by the relocalization functor. -/
noncomputable abbrev morphismComponentRestr (i : K.I) :
    SheafOfModules.{u} (familyLocalizationRingSheaf X L) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :=
  restrictionModules (X.J.over (K.obj i)) (componentwiseTopology X.J L)
    (Over.map (f.φ i) ⋙
      CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i))
    (familyLocalizationRingSheaf X L)

/-- Restricting the structure map of `f^*` to the `i`-th component gives the identity: the two
readings of `O_K` agree on each component on the nose, so the comparison's `eqToHom` is
`eqToHom` of a reflexivity there. -/
theorem morphismRestr_structureMap_comp (i : K.I) :
    (𝟙 (familyComponentRingSheaf X K i)) ≫
        ((CategoryTheory.Sigma.incl (C := fun k : K.I => Over (K.obj k)) i
          ).sheafPushforwardContinuous RingCat.{u} (X.J.over (K.obj i))
            (componentwiseTopology X.J K)).map
          (eqToHom (familyRelocalizationRingSheaf_eq X f).symm) =
      𝟙 (familyComponentRingSheaf X K i) := by
  rw [Category.id_comp, eqToHom_map]
  exact eqToHom_refl _ _

/-- **`f^*` followed by restriction to the `i`-th component of `K` is `f_i^*`.** -/
noncomputable def morphismRestrComponentIso (i : K.I) :
    morphismRestr X f ⋙
        restrictionModules (X.J.over (K.obj i)) (componentwiseTopology X.J K)
          (CategoryTheory.Sigma.incl (C := fun k : K.I => Over (K.obj k)) i)
          (familyLocalizationRingSheaf X K) ≅
      morphismComponentRestr X f i :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr
      (F := Over.map (f.φ i) ⋙
        CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i))
      (morphismRestr_structureMap_comp X f i)

/-- `f^*` followed by the componentwise restriction is the family of the `f_i^*`. -/
noncomputable def morphismRestrCompRestrictionIso :
    morphismRestr X f ⋙ componentwiseModuleRestriction X K ≅
      Functor.pi' (morphismComponentRestr X f) :=
  NatIso.pi' fun i => morphismRestrComponentIso X f i

/-- `f^*` followed by the decomposition of part (2) is the family of the `f_i^*`. -/
noncomputable def morphismRestrCompEquivalenceIso :
    morphismRestr X f ⋙ (componentwiseModuleRestrictionEquivalence X K).functor ≅
      Functor.pi' (morphismComponentRestr X f) :=
  eqToIso (by
      rw [componentwiseModuleRestrictionEquivalence_functor]) ≪≫
    morphismRestrCompRestrictionIso X f

/-- `f_i^*` has a left adjoint: it is restriction along a continuous functor whose source is
essentially small. -/
instance morphismComponentRestr_isRightAdjoint (i : K.I) :
    (morphismComponentRestr X f i).IsRightAdjoint :=
  Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules
    (X.J.over (K.obj i)) (componentwiseTopology X.J L)
    (Over.map (f.φ i) ⋙
      CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i))
    (familyLocalizationRingSheaf X L)

/-- The `i`-th summand of `f_!`: the left adjoint of `f_i^*`. -/
noncomputable abbrev morphismComponentLowerShriek (i : K.I) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) ⥤
      SheafOfModules.{u} (familyLocalizationRingSheaf X L) :=
  (morphismComponentRestr X f i).leftAdjoint

/-- The structure map of the two-step restriction through the `f i`-th component of `L` is the
identity. -/
theorem morphismComponent_structureMap_comp (i : K.I) :
    (𝟙 (((Over.map (f.φ i)).sheafPushforwardContinuous RingCat.{u}
          (X.J.over (K.obj i)) (X.J.over (L.obj (f.f i)))).obj
        (familyComponentRingSheaf X L (f.f i)))) ≫
        ((Over.map (f.φ i)).sheafPushforwardContinuous RingCat.{u}
          (X.J.over (K.obj i)) (X.J.over (L.obj (f.f i)))).map
          (𝟙 (familyComponentRingSheaf X L (f.f i))) =
      𝟙 (((Over.map (f.φ i)).sheafPushforwardContinuous RingCat.{u}
          (X.J.over (K.obj i)) (X.J.over (L.obj (f.f i)))).obj
        (familyComponentRingSheaf X L (f.f i))) := by
  simp

/-- Restriction to the `j`-th component of `L` has a left adjoint, in the spelling with the
structure map written as the identity of `familyComponentRingSheaf`, which is what splitting a
restriction with `SheafOfModules.pushforwardComp` produces. -/
instance pushforward_familyComponentIncl_isRightAdjoint (j : L.I) :
    (SheafOfModules.pushforward.{u}
        (F := CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) j)
        (𝟙 (familyComponentRingSheaf X L j))).IsRightAdjoint :=
  Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules
    (X.J.over (L.obj j)) (componentwiseTopology X.J L)
    (CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) j)
    (familyLocalizationRingSheaf X L)

/-- **The `i`-th summand of `f_!` is extension by zero along `Over.map (f.φ i)` followed by the
lower shriek of the inclusion of the `f i`-th component of `L`.** -/
noncomputable def morphismComponentLowerShriek_iso (i : K.I) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.φ i)).leftAdjoint ⋙
        familyComponentInclLowerShriek X L (f.f i) ≅
      morphismComponentLowerShriek X f i :=
  SheafOfModules.pullbackComp
      (F := Over.map (f.φ i))
      (G := CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i))
      (𝟙 (((Over.map (f.φ i)).sheafPushforwardContinuous RingCat.{u}
        (X.J.over (K.obj i)) (X.J.over (L.obj (f.f i)))).obj
          (familyComponentRingSheaf X L (f.f i))))
      (𝟙 (familyComponentRingSheaf X L (f.f i))) ≪≫
    Adjunction.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction _)
      ((Adjunction.ofIsRightAdjoint (morphismComponentRestr X f i)).ofNatIsoRight
        (SheafOfModules.pushforwardCongr
          (F := Over.map (f.φ i) ⋙
            CategoryTheory.Sigma.incl (C := fun k : L.I => Over (L.obj k)) (f.f i))
          (morphismComponent_structureMap_comp X f i)).symm)

/-- **Each summand of `f_!` is exact**: extension by zero along a relocalization is exact by
Stacks 03DJ, and the lower shriek of a component inclusion is exact. -/
theorem morphismComponentLowerShriek_exact (i : K.I) :
    exactFunctor _ _ (morphismComponentLowerShriek X f i) := by
  exact exactFunctor_of_comp_iso (morphismComponentLowerShriek_iso X f i)
    (Stacks.Sites.ExtensionByZero.overMap_extensionByZero_exact X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.φ i))
    (familyComponentInclLowerShriek_exact X L (f.f i))

/-- **The direct sum of the componentwise summands is left adjoint to `f^*`.** -/
noncomputable def morphismDirectSumLowerShriekAdjunction :
    (componentwiseModuleRestrictionEquivalence X K).functor ⋙
        piCoproduct (morphismComponentLowerShriek X f) ⊣ morphismRestr X f :=
  ((componentwiseModuleRestrictionEquivalence X K).toAdjunction.comp
    (piCoproductAdjunction (morphismComponentRestr X f) (morphismComponentLowerShriek X f)
      fun i => Adjunction.ofIsRightAdjoint (morphismComponentRestr X f i))).ofNatIsoRight
    (Functor.isoWhiskerRight (morphismRestrCompEquivalenceIso X f).symm
        (componentwiseModuleRestrictionEquivalence X K).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (morphismRestr X f)
        (componentwiseModuleRestrictionEquivalence X K).unitIso.symm ≪≫
      (morphismRestr X f).rightUnitor)

/-- **Stacks 0D9U.** `f^*` has a left adjoint `f_!`. -/
@[stacks 0D9U "f^* has a left adjoint f_!"]
instance morphismRestr_isRightAdjoint : (morphismRestr X f).IsRightAdjoint :=
  (morphismDirectSumLowerShriekAdjunction X f).isRightAdjoint

/-- **Stacks 0D9U.** In terms of the product decomposition of part (2), `f_!` sends a family
`(F i)` to `⨁ i, f_{i,!} F i`: both are left adjoint to `f^*`. -/
@[stacks 0D9U "f_! is the direct sum of the componentwise lower shrieks"]
noncomputable def morphismLowerShriek_iso_directSum :
    (morphismRestr X f).leftAdjoint ≅
      (componentwiseModuleRestrictionEquivalence X K).functor ⋙
        piCoproduct (morphismComponentLowerShriek X f) :=
  Adjunction.leftAdjointUniq (Adjunction.ofIsRightAdjoint (morphismRestr X f))
    (morphismDirectSumLowerShriekAdjunction X f)

/-- **Stacks 0D9U.** The lower shriek `f_!` is exact: it preserves finite colimits because it
is a left adjoint, and finite limits because it is the direct sum of the exact functors
`f_{i,!}`, coproducts of sheaves of modules being exact. -/
@[stacks 0D9U "f_! is exact"]
theorem morphismLowerShriek_exact : exactFunctor _ _ (morphismRestr X f).leftAdjoint := by
  have hsum : PreservesFiniteLimits (piCoproduct (morphismComponentLowerShriek X f)) :=
    preservesFiniteLimits_piCoproduct _ fun i =>
      ((exactFunctor_iff _).mp (morphismComponentLowerShriek_exact X f i)).1
  have hd : PreservesFiniteLimits
      ((componentwiseModuleRestrictionEquivalence X K).functor ⋙
        piCoproduct (morphismComponentLowerShriek X f)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _
      (componentwiseModuleRestrictionEquivalence X K).functor
      (piCoproduct (morphismComponentLowerShriek X f)) inferInstance hsum
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (morphismLowerShriek_iso_directSum X f).symm hd
  · have : PreservesColimitsOfSize.{0, 0} (morphismRestr X f).leftAdjoint :=
      (Adjunction.ofIsRightAdjoint (morphismRestr X f)).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _

end MorphismLowerShriek

end AlgebraicGeometry.RingedSite

end
