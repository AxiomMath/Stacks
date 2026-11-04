module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageFppfVanishing

/-!
# Quasi-coherent modules and the flat-fppf site (Stacks 07B1, part (2))

Let `𝒳` be an algebraic stack and `g : (Sh(𝒳_{flat,fppf}), 𝒪_{𝒳_{flat,fppf}}) ⟶ (Sh(𝒳_fppf), 𝒪_𝒳)`
the morphism of ringed topoi of **Stacks 0788** (2), with `g_! ⊣ g^{-1}` on sheaves of modules
(**Stacks 0789** (2); `g^* = g^{-1}` by **Stacks 0788** (2)(f)). **Stacks 07B1** (2) says:

* (a) `g^{-1}` and `g_!` are mutually inverse functors between `QCoh(𝒪_𝒳)` and
  `QCoh(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}})`;
* (b) for `𝓕` in `LQCoh^fbc(𝒪_𝒳)`, `g^{-1}𝓕` is quasi-coherent on `𝒳_{flat,fppf}`;
* (c) `Q(𝓕) = g_!g^{-1}𝓕`, for `Q` the coherator of **Stacks 0778**.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.quasicoherentSubsiteModules`: `QCoh(𝒳_{flat,fppf})`.
* `AlgebraicGeometry.Stack.FlatFppf.quasicoherentModulePullback` and
  `AlgebraicGeometry.Stack.FlatFppf.quasicoherentModuleLowerShriek`: `g^{-1}` and `g_!`
  restricted to quasi-coherent modules; their composites with the inclusions are `g^{-1}` and
  `g_!` on the nose.
* `AlgebraicGeometry.Stack.FlatFppf.quasicoherentEquivalence`: **Stacks 07B1** (2)(a).
* `AlgebraicGeometry.Stack.FlatFppf.coheratorIsoLowerShriekModulePullback`: **Stacks 07B1**
  (2)(c).

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_modulePullback_of_lqcohSheafFbc`:
  **Stacks 07B1** (2)(b).

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  hasSheafify_fppf_addCommGrpCat wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `QCoh(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}})`: the quasi-coherent modules on the flat-fppf site. -/
abbrev quasicoherentSubsiteModules :=
  (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf
    (subsiteRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
      (objectProperty B S hS 𝒳)).O)).FullSubcategory

/-- `g^{-1} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒳_{flat,fppf})`, the pullback of modules restricted to
quasi-coherent modules. -/
abbrev quasicoherentModulePullback :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ quasicoherentSubsiteModules B S hS 𝒳 :=
  ObjectProperty.lift _ (AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ modulePullback B S hS 𝒳)
    fun G => isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS 𝒳 G.obj G.property

/-- `g_! : QCoh(𝒳_{flat,fppf}) ⥤ QCoh(𝒪_𝒳)`, the lower shriek restricted to quasi-coherent
modules (**Stacks 07B0** (2)). -/
abbrev quasicoherentModuleLowerShriek :
    quasicoherentSubsiteModules B S hS 𝒳 ⥤ AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ moduleLowerShriek B S hS 𝒳)
    fun H => isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite B S hS 𝒳 H.obj
      H.property

/-- The counit `g_!g^{-1}𝓖 ⟶ 𝓖` of `g_! ⊣ g^{-1}`, on quasi-coherent modules. -/
def quasicoherentCounit :
    quasicoherentModulePullback B S hS 𝒳 ⋙ quasicoherentModuleLowerShriek B S hS 𝒳 ⟶ 𝟭 _ where
  app G := ObjectProperty.homMk ((moduleLowerShriekAdjunction B S hS 𝒳).counit.app G.obj)
  naturality {_ _} f := (ObjectProperty.fullyFaithfulι _).map_injective
    ((moduleLowerShriekAdjunction B S hS 𝒳).counit.naturality f.hom)

/-- The counit `g_!g^{-1}𝓖 ⟶ 𝓖` of `g_! ⊣ g^{-1}` is an isomorphism on quasi-coherent modules. -/
instance isIso_quasicoherentCounit : IsIso (quasicoherentCounit B S hS 𝒳) := by
  have : ∀ G, IsIso ((quasicoherentCounit B S hS 𝒳).app G) := fun G => by
    have : IsIso ((AlgebraicStacks.quasicoherentInclusion B S hS 𝒳).map
        ((quasicoherentCounit B S hS 𝒳).app G)) :=
      isIso_moduleLowerShriekAdjunction_counit_app_of_isQuasicoherentOnSite B S hS 𝒳 G.obj
        G.property
    exact isIso_of_reflects_iso _ (AlgebraicStacks.quasicoherentInclusion B S hS 𝒳)
  exact NatIso.isIso_of_isIso_app _

/-- The unit `ℋ ⟶ g^{-1}g_!ℋ` of `g_! ⊣ g^{-1}`, on quasi-coherent modules. -/
def quasicoherentUnit :
    𝟭 _ ⟶ quasicoherentModuleLowerShriek B S hS 𝒳 ⋙ quasicoherentModulePullback B S hS 𝒳 where
  app H := ObjectProperty.homMk ((moduleLowerShriekAdjunction B S hS 𝒳).unit.app H.obj)
  naturality {_ _} f := (ObjectProperty.fullyFaithfulι _).map_injective
    ((moduleLowerShriekAdjunction B S hS 𝒳).unit.naturality f.hom)

/-- The unit `ℋ ⟶ g^{-1}g_!ℋ` of `g_! ⊣ g^{-1}` is an isomorphism on quasi-coherent modules. -/
instance isIso_quasicoherentUnit : IsIso (quasicoherentUnit B S hS 𝒳) := by
  have := isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳
  have : ∀ H, IsIso ((quasicoherentUnit B S hS 𝒳).app H) := fun H => by
    have : IsIso ((ObjectProperty.ι _).map ((quasicoherentUnit B S hS 𝒳).app H)) :=
      (inferInstance : IsIso ((moduleLowerShriekAdjunction B S hS 𝒳).unit.app H.obj))
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact NatIso.isIso_of_isIso_app _

/-- For an algebraic stack `𝒳`, the functors `g^{-1}` and `g_!` are mutually inverse equivalences
between `QCoh(𝒪_𝒳)` and `QCoh(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}})`. The functor of the equivalence
is `g^{-1}` and its inverse is `g_!`, both on the nose (`quasicoherentEquivalence_functor_comp_ι`,
`quasicoherentEquivalence_inverse_comp_ι`); the unit is the inverse of the counit
`g_!g^{-1}𝓖 ⟶ 𝓖` of `g_! ⊣ g^{-1}`, an isomorphism on quasi-coherent modules, and the counit is
the inverse of its unit `ℋ ⟶ g^{-1}g_!ℋ`. -/
@[stacks 07B1 "part (2)(a): g^{-1} and g_! are mutually inverse functors between QCoh(𝒪_𝒳) and \
QCoh(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}})"]
def quasicoherentEquivalence :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ≌ quasicoherentSubsiteModules B S hS 𝒳 :=
  CategoryTheory.Equivalence.mk (quasicoherentModulePullback B S hS 𝒳)
    (quasicoherentModuleLowerShriek B S hS 𝒳) (asIso (quasicoherentCounit B S hS 𝒳)).symm
    (asIso (quasicoherentUnit B S hS 𝒳)).symm

/-- The functor of `quasicoherentEquivalence` is `g^{-1}`. -/
theorem quasicoherentEquivalence_functor_comp_ι :
    (quasicoherentEquivalence B S hS 𝒳).functor ⋙ ObjectProperty.ι _ =
      AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ modulePullback B S hS 𝒳 :=
  rfl

/-- The inverse of `quasicoherentEquivalence` is `g_!`. -/
theorem quasicoherentEquivalence_inverse_comp_ι :
    (quasicoherentEquivalence B S hS 𝒳).inverse ⋙ AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 =
      ObjectProperty.ι _ ⋙ moduleLowerShriek B S hS 𝒳 :=
  rfl

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- For `𝓕` in `LQCoh^fbc(𝒪_𝒳)`, the module `g^{-1}𝓕` on the flat-fppf site is quasi-coherent. -/
@[stacks 07B1 "part (2)(b): for F in LQCoh^fbc(𝒪_𝒳), g^{-1}F is in QCoh(𝒪_{𝒳_{flat,fppf}})"]
theorem isQuasicoherentOnSite_modulePullback_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    ((modulePullback B S hS 𝒳).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isCartesianAlongFlatAffine B S hS 𝒳 F
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF)

/-- The counit `g_!g^{-1}Q(𝓕) ⟶ Q(𝓕)` of `g_! ⊣ g^{-1}` at the quasi-coherent module `Q(𝓕)`, as
a natural transformation in `𝓕 ∈ LQCoh^fbc(𝒪_𝒳)`. -/
def coheratorLowerShriekCounit :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ AlgebraicStacks.coherator B S hS 𝒳 ⋙
        AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ modulePullback B S hS 𝒳 ⋙
          moduleLowerShriek B S hS 𝒳 ⟶
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ AlgebraicStacks.coherator B S hS 𝒳 ⋙
        AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 :=
  Functor.whiskerLeft ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
    AlgebraicStacks.coherator B S hS 𝒳 ⋙ AlgebraicStacks.quasicoherentInclusion B S hS 𝒳)
    (moduleLowerShriekAdjunction B S hS 𝒳).counit

/-- The counit `g_!g^{-1}Q(𝓕) ⟶ Q(𝓕)` is an isomorphism, naturally in `𝓕 ∈ LQCoh^fbc(𝒪_𝒳)`. -/
instance isIso_coheratorLowerShriekCounit : IsIso (coheratorLowerShriekCounit B S hS 𝒳 E h) := by
  have : ∀ F, IsIso ((coheratorLowerShriekCounit B S hS 𝒳 E h).app F) := fun F =>
    isIso_moduleLowerShriekAdjunction_counit_app_of_isQuasicoherentOnSite B S hS 𝒳 _
      ((AlgebraicStacks.coherator B S hS 𝒳).obj F.obj).property
  exact NatIso.isIso_of_isIso_app _

/-- `g_!g^{-1}` of the adjunction map `Q(𝓕) ⟶ 𝓕` of the coherator, natural in `𝓕`. -/
def lowerShriekModulePullbackCoheratorCounit :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ AlgebraicStacks.coherator B S hS 𝒳 ⋙
        AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ modulePullback B S hS 𝒳 ⋙
          moduleLowerShriek B S hS 𝒳 ⟶
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ modulePullback B S hS 𝒳 ⋙
        moduleLowerShriek B S hS 𝒳 :=
  Functor.whiskerRight (Functor.whiskerLeft (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι
    (AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit)
    (modulePullback B S hS 𝒳 ⋙ moduleLowerShriek B S hS 𝒳)

/-- For `𝓕 ∈ LQCoh^fbc(𝒪_𝒳)`, `g_!g^{-1}` of the adjunction map `Q(𝓕) ⟶ 𝓕` is an isomorphism. -/
instance isIso_lowerShriekModulePullbackCoheratorCounit :
    IsIso (lowerShriekModulePullbackCoheratorCounit B S hS 𝒳 E h) := by
  have : ∀ F, IsIso ((lowerShriekModulePullbackCoheratorCounit B S hS 𝒳 E h).app F) := fun F => by
    have := isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳
      (AlgebraicStacks.coheratorAdjunction B S hS 𝒳) F.obj
      (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F.obj F.property)
    exact (Functor.map_isIso (moduleLowerShriek B S hS 𝒳) ((modulePullback B S hS 𝒳).map
      ((AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.app F.obj)) :)
  exact NatIso.isIso_of_isIso_app _

/-- For `𝓕` in `LQCoh^fbc(𝒪_𝒳)`, `Q(𝓕) = g_!g^{-1}𝓕`, naturally in `𝓕`, where
`Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` is the coherator of **Stacks 0778**
(`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator`). The isomorphism at `𝓕` is
`g_!g^{-1}` of the adjunction map `Q(𝓕) ⟶ 𝓕`, preceded by the inverse of the counit
`g_!g^{-1}Q(𝓕) ⟶ Q(𝓕)`. -/
@[stacks 07B1 "part (2)(c): Q(F) = g_! g^{-1} F for F in LQCoh^fbc(𝒪_𝒳), Q the coherator of 0778"]
def coheratorIsoLowerShriekModulePullback :
    AlgebraicStacks.lqcohFbcCoherator B E h S hS 𝒳 ⋙
        AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ≅
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ modulePullback B S hS 𝒳 ⋙
        moduleLowerShriek B S hS 𝒳 :=
  (asIso (coheratorLowerShriekCounit B S hS 𝒳 E h)).symm ≪≫
    @asIso _ _ _ _ (lowerShriekModulePullbackCoheratorCounit B S hS 𝒳 E h)
      (isIso_lowerShriekModulePullbackCoheratorCounit B S hS 𝒳 E h)

end AlgebraicGeometry.Stack.FlatFppf

end
