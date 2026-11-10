module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfQuasicoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LisseEtaleCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LowerShriekQuasicoherent

/-!
# Quasi-coherent modules and the lisse-étale site (Stacks 07B1, part (1))

Let `𝒳` be an algebraic stack and `g : (Sh(𝒳_{lisse,étale}), 𝒪_{𝒳_{lisse,étale}}) ⟶
(Sh(𝒳_étale), 𝒪_𝒳)` the morphism of ringed topoi of **Stacks 0788** (1), with `g_! ⊣ g^{-1}` on
sheaves of modules (**Stacks 0789** (1); `g^* = g^{-1}` by **Stacks 0788** (1)(f)). **Stacks 07B1**
(1) says:

* (a) `g^{-1}` and `g_!` are mutually inverse functors between `QCoh(𝒪_𝒳)` and
  `QCoh(𝒳_{lisse,étale}, 𝒪_{𝒳_{lisse,étale}})`;
* (b) for `𝓕` in `LQCoh^fbc(𝒪_𝒳)`, `g^{-1}𝓕` is quasi-coherent on `𝒳_{lisse,étale}`;
* (c) `Q(𝓕) = g_!g^{-1}𝓕`, for `Q` the coherator of **Stacks 0778**.

`QCoh(𝒪_𝒳)` is `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules`, the quasi-coherent
modules on the fppf site of **Stacks 06WG**. `g^{-1}` of an `𝒪_𝒳`-module is `g^{-1}` of its
underlying étale module (the direct image `ε_*` along `𝒳_fppf ⟶ 𝒳_étale`, which changes nothing
underneath, `AlgebraicGeometry.Stack.fppfModulesToEtaleModules`), and `g_!` of a quasi-coherent
module on the lisse-étale site is an fppf sheaf, quasi-coherent there (**Stacks 07B0** (1)), so it
is read as an object of `QCoh(𝒪_𝒳)` with the same underlying presheaf of modules.

## The proof

* The unit `ℋ ⟶ g^{-1}g_!ℋ` is an isomorphism (**Stacks 0789** (1)).
* For quasi-coherent `𝓖`, `g^{-1}𝓖` is quasi-coherent
  (`LisseEtale.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`),
  so `g_!g^{-1}𝓖` is quasi-coherent (**Stacks 07B0** (1)); the counit `g_!g^{-1}𝓖 ⟶ 𝓖` becomes an
  isomorphism under `g^{-1}`, by the triangle identity, i.e. it is bijective on sections over every
  smooth object, and the smooth objects detect isomorphisms of quasi-coherent modules
  (`AlgebraicGeometry.Stack.isIso_of_smoothObject`). This is (a).
* For `𝓕` in `LQCoh^fbc(𝒪_𝒳)` the adjunction map `Q(𝓕) ⟶ 𝓕` is bijective on sections over every
  flat object (**Stacks 07B1** (2), through
  `AlgebraicGeometry.Stack.isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine`), in
  particular over every smooth object, so `g^{-1}Q(𝓕) ⟶ g^{-1}𝓕` is an isomorphism. As `Q(𝓕)` is
  quasi-coherent, so is `g^{-1}𝓕`, which is (b); and `Q(𝓕) = g_!g^{-1}Q(𝓕) = g_!g^{-1}𝓕` by (a),
  which is (c).

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.quasicoherentSubsiteModules`: `QCoh(𝒳_{lisse,étale})`.
* `AlgebraicGeometry.Stack.LisseEtale.quasicoherentModulePullback` and
  `AlgebraicGeometry.Stack.LisseEtale.quasicoherentModuleLowerShriek`: `g^{-1}` and `g_!` on
  quasi-coherent modules.
* `AlgebraicGeometry.Stack.LisseEtale.quasicoherentEquivalence`: **Stacks 07B1** (1)(a).
* `AlgebraicGeometry.Stack.LisseEtale.coheratorIsoLowerShriekModulePullback`: **Stacks 07B1**
  (1)(c).

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentOnSite_modulePullback_of_lqcohSheafFbc`:
  **Stacks 07B1** (1)(b).

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.LisseEtale

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `QCoh(𝒳_{lisse,étale}, 𝒪_{𝒳_{lisse,étale}})`: the quasi-coherent modules on the lisse-étale
site. -/
abbrev quasicoherentSubsiteModules :=
  (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf
    (ringedTopos.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).O)).FullSubcategory

/-- `g^{-1} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒳_{lisse,étale})`, the pullback of modules restricted to
quasi-coherent modules. -/
abbrev quasicoherentModulePullback :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ quasicoherentSubsiteModules B S hS 𝒳 :=
  ObjectProperty.lift _
    (AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ fppfModulePullback B S hS 𝒳)
    fun G => isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS 𝒳 G.obj
      G.property

/-- `g_!` of a quasi-coherent module on the lisse-étale site, read as an `𝒪_𝒳`-module: it is a
sheaf for the fppf topology (**Stacks 07B0** (1)), with the same underlying presheaf of modules
and the same maps. -/
def fppfModuleLowerShriek :
    quasicoherentSubsiteModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒳 where
  obj H := ⟨((moduleLowerShriek.{u, w} B S hS 𝒳).obj H.obj).val,
    FibredSite.isSheaf_of_isQuasicoherentClause B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf (isQuasicoherentClause_fppf_moduleLowerShriek B S hS 𝒳 H.obj H.property)⟩
  map f := ⟨((moduleLowerShriek.{u, w} B S hS 𝒳).map f.hom).val⟩
  map_id H := (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)).map_injective
    ((moduleLowerShriek.{u, w} B S hS 𝒳).map_id H.obj)
  map_comp f g := (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)).map_injective
    ((moduleLowerShriek.{u, w} B S hS 𝒳).map_comp f.hom g.hom)

/-- `g_! : QCoh(𝒳_{lisse,étale}) ⥤ QCoh(𝒪_𝒳)`, the lower shriek restricted to quasi-coherent
modules (**Stacks 07B0** (1)). -/
abbrev quasicoherentModuleLowerShriek :
    quasicoherentSubsiteModules B S hS 𝒳 ⥤ AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  ObjectProperty.lift _ (fppfModuleLowerShriek B S hS 𝒳) fun H =>
    (isQuasicoherentClause_fppf_moduleLowerShriek B S hS 𝒳 H.obj H.property).2

/-- The counit `g_!g^{-1}𝓖 ⟶ 𝓖` of `g_! ⊣ g^{-1}`, on quasi-coherent modules. -/
def quasicoherentCounit :
    quasicoherentModulePullback B S hS 𝒳 ⋙ quasicoherentModuleLowerShriek B S hS 𝒳 ⟶ 𝟭 _ where
  app G := ObjectProperty.homMk ⟨((moduleLowerShriekAdjunction.{u, w} B S hS 𝒳).counit.app
    ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj G.obj)).val⟩
  naturality _ _ f := (ObjectProperty.fullyFaithfulι _).map_injective
    ((Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).map_injective
      ((moduleLowerShriekAdjunction.{u, w} B S hS 𝒳).counit.naturality
        ((Stacks.SheafOfModules.comparisonPushforward
          (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
          (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids .fppf)).map f.hom)))

/-- **`g_!g^{-1}` is the identity on quasi-coherent modules**: the counit `g_!g^{-1}𝓖 ⟶ 𝓖` is an
isomorphism at every quasi-coherent `𝓖`. Both sides are quasi-coherent, and the counit is bijective
over every smooth object, `g^{-1}` of it being inverse to the unit, which is invertible
(**Stacks 0789** (1)); the smooth objects detect isomorphisms of quasi-coherent modules. -/
instance isIso_quasicoherentCounit : IsIso (quasicoherentCounit B S hS 𝒳) := by
  have := isIso_moduleLowerShriekAdjunction_unit.{u, w} B S hS 𝒳
  have : ∀ G, IsIso ((quasicoherentCounit B S hS 𝒳).app G) := fun G => by
    let adjL := moduleLowerShriekAdjunction.{u, w} B S hS 𝒳
    let M := (Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj G.obj
    have hrκ : IsIso ((modulePullback.{u, w} B S hS 𝒳).map (adjL.counit.app M)) :=
      IsIso.of_isIso_fac_left (adjL.right_triangle_components M)
    let ψ : (fppfModuleLowerShriek B S hS 𝒳).obj ((quasicoherentModulePullback B S hS 𝒳).obj G) ⟶
        G.obj := ⟨(adjL.counit.app M).val⟩
    have : IsIso ((ObjectProperty.ι _).map ((quasicoherentCounit B S hS 𝒳).app G)) :=
      isIso_of_smoothObject ((quasicoherentModuleLowerShriek B S hS 𝒳).obj
        ((quasicoherentModulePullback B S hS 𝒳).obj G)).property G.property ψ
        (bijective_app_of_isIso_modulePullback_map B S hS 𝒳 ψ hrκ)
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact NatIso.isIso_of_isIso_app _

/-- The unit `ℋ ⟶ g^{-1}g_!ℋ` of `g_! ⊣ g^{-1}`, on quasi-coherent modules. -/
def quasicoherentUnit :
    𝟭 _ ⟶ quasicoherentModuleLowerShriek B S hS 𝒳 ⋙ quasicoherentModulePullback B S hS 𝒳 where
  app H := ObjectProperty.homMk ((moduleLowerShriekAdjunction.{u, w} B S hS 𝒳).unit.app H.obj)
  naturality _ _ f := (ObjectProperty.fullyFaithfulι _).map_injective
    ((moduleLowerShriekAdjunction.{u, w} B S hS 𝒳).unit.naturality f.hom)

/-- The unit `ℋ ⟶ g^{-1}g_!ℋ` of `g_! ⊣ g^{-1}` on quasi-coherent modules is an isomorphism. -/
instance isIso_quasicoherentUnit : IsIso (quasicoherentUnit B S hS 𝒳) := by
  have := isIso_moduleLowerShriekAdjunction_unit.{u, w} B S hS 𝒳
  have : ∀ H, IsIso ((quasicoherentUnit B S hS 𝒳).app H) := fun H => by
    have : IsIso ((ObjectProperty.ι _).map ((quasicoherentUnit B S hS 𝒳).app H)) :=
      (inferInstance : IsIso ((moduleLowerShriekAdjunction.{u, w} B S hS 𝒳).unit.app H.obj))
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 07B1 (1)(a).** For an algebraic stack `𝒳`, the functors `g^{-1}` and `g_!` are
mutually inverse equivalences between `QCoh(𝒪_𝒳)` and
`QCoh(𝒳_{lisse,étale}, 𝒪_{𝒳_{lisse,étale}})`. The functor of the equivalence is `g^{-1}` and its
inverse is `g_!`, both on the nose (`quasicoherentEquivalence_functor_comp_ι`,
`quasicoherentEquivalence_inverse_comp_ι`, `fppfModuleLowerShriek_obj_val`); the unit is the
inverse of the counit `g_!g^{-1}𝓖 ⟶ 𝓖` of `g_! ⊣ g^{-1}`, an isomorphism on quasi-coherent
modules, and the counit is the inverse of its unit `ℋ ⟶ g^{-1}g_!ℋ`. -/
@[stacks 07B1 "part (1)(a): g^{-1} and g_! are mutually inverse functors between QCoh(𝒪_𝒳) and \
QCoh(𝒳_{lisse,étale}, 𝒪_{𝒳_{lisse,étale}})"]
def quasicoherentEquivalence :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ≌ quasicoherentSubsiteModules.{u, w} B S hS 𝒳 :=
  CategoryTheory.Equivalence.mk (quasicoherentModulePullback.{u, w} B S hS 𝒳)
    (quasicoherentModuleLowerShriek B S hS 𝒳) (asIso (quasicoherentCounit B S hS 𝒳)).symm
    (asIso (quasicoherentUnit B S hS 𝒳)).symm

/-- The functor of `quasicoherentEquivalence` is `g^{-1}`. -/
theorem quasicoherentEquivalence_functor_comp_ι :
    (quasicoherentEquivalence B S hS 𝒳).functor ⋙ ObjectProperty.ι _ =
      AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 ⋙ fppfModulePullback B S hS 𝒳 :=
  rfl

/-- The inverse of `quasicoherentEquivalence` is `g_!`, read as an `𝒪_𝒳`-module. -/
theorem quasicoherentEquivalence_inverse_comp_ι :
    (quasicoherentEquivalence B S hS 𝒳).inverse ⋙ AlgebraicStacks.quasicoherentInclusion B S hS 𝒳 =
      fppfModuleLowerShriek B S hS 𝒳 :=
  rfl

/-- The underlying presheaf of modules of `g_!ℋ`, read as an `𝒪_𝒳`-module, is that of `g_!ℋ`. -/
theorem fppfModuleLowerShriek_obj_val (H : quasicoherentSubsiteModules B S hS 𝒳) :
    ((fppfModuleLowerShriek B S hS 𝒳).obj H).val =
      ((moduleLowerShriek.{u, w} B S hS 𝒳).obj H.obj).val :=
  rfl

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- The adjunction map `Q(𝓕) ⟶ 𝓕` of the coherator is bijective on sections over every smooth
object, for `𝓕` in `LQCoh^fbc(𝒪_𝒳)`: it is so over every flat object (**Stacks 07B1** (2)), and a
smooth object is flat. -/
theorem isIso_fppfModulePullback_map_coheratorAdjunction_counit_app
    (F : fppfModules B S hS 𝒳) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsIso ((fppfModulePullback B S hS 𝒳).map
      ((AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.app F)) := by
  have hflat := isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳
    (AlgebraicStacks.coheratorAdjunction B S hS 𝒳) F
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF)
  exact isIso_modulePullback_map_of_bijective B S hS 𝒳 _ fun x hx =>
    FlatFppf.bijective_app_of_isIso_modulePullback_map B S hS 𝒳 _ hflat x
      (flatObject_of_smoothObject B S hS 𝒳 hx)

/-- **Stacks 07B1 (1)(b)**, for `𝓕` an `𝒪_𝒳`-module: if `𝓕` is in `LQCoh^fbc(𝒪_𝒳)`, then
`g^{-1}𝓕` is quasi-coherent on the lisse-étale site. It is isomorphic to `g^{-1}Q(𝓕)`, which is
quasi-coherent because `Q(𝓕)` is. -/
theorem isQuasicoherentOnSite_fppfModulePullback_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    ((fppfModulePullback B S hS 𝒳).obj F).IsQuasicoherentOnSite := by
  have := isIso_fppfModulePullback_map_coheratorAdjunction_counit_app B S hS 𝒳 E h F hF
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((fppfModulePullback B S hS 𝒳).map
      ((AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.app F)))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS 𝒳 _
      ((AlgebraicStacks.coherator B S hS 𝒳).obj F).property)

/-- **Stacks 07B1 (1)(b).** For `𝓕` in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)`, the module
`g^{-1}𝓕` on the lisse-étale site is quasi-coherent. -/
@[stacks 07B1 "part (1)(b): for F in LQCoh^fbc(𝒪_𝒳), g^{-1}F is in \
QCoh(𝒪_{𝒳_{lisse,étale}})"]
theorem isQuasicoherentOnSite_modulePullback_of_lqcohSheafFbc
    (F : etaleTopologyModules B S hS 𝒳) (hF : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 F) :
    ((modulePullback.{u, w} B S hS 𝒳).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_fppfModulePullback_of_lqcohSheafFbc B S hS 𝒳 E h
    (fppfModuleOfLqcohSheafFbc B E h S hS 𝒳 F hF).obj
    (fppfModuleOfLqcohSheafFbc B E h S hS 𝒳 F hF).property

/-- `g^{-1} : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒳_{lisse,étale})`, by **Stacks 07B1** (1)(b). -/
abbrev lqcohFbcModulePullback :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      quasicoherentSubsiteModules B S hS 𝒳 :=
  ObjectProperty.lift _ ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
    fppfModulePullback B S hS 𝒳) fun F =>
      isQuasicoherentOnSite_fppfModulePullback_of_lqcohSheafFbc B S hS 𝒳 E h F.obj F.property

/-- `g^{-1}` of the adjunction map `Q(𝓕) ⟶ 𝓕` of the coherator, natural in `𝓕 ∈ LQCoh^fbc(𝒪_𝒳)`. -/
def coheratorCounitModulePullback :
    AlgebraicStacks.lqcohFbcCoherator B E h S hS 𝒳 ⋙ quasicoherentModulePullback B S hS 𝒳 ⟶
      lqcohFbcModulePullback B S hS 𝒳 E h where
  app F := ObjectProperty.homMk ((fppfModulePullback B S hS 𝒳).map
    ((AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.app F.obj))
  naturality {F F'} k := (ObjectProperty.fullyFaithfulι _).map_injective (by
    have hn := congrArg (fppfModulePullback B S hS 𝒳).map
      ((AlgebraicStacks.coheratorAdjunction B S hS 𝒳).counit.naturality k.hom)
    simp only [Functor.map_comp] at hn
    exact hn)

/-- The map `g^{-1}Q(𝓕) ⟶ g^{-1}𝓕` induced by the coherator counit is an isomorphism. -/
instance isIso_coheratorCounitModulePullback :
    IsIso (coheratorCounitModulePullback B S hS 𝒳 E h) := by
  have : ∀ F, IsIso ((coheratorCounitModulePullback B S hS 𝒳 E h).app F) := fun F => by
    have : IsIso ((ObjectProperty.ι _).map ((coheratorCounitModulePullback B S hS 𝒳 E h).app F)) :=
      isIso_fppfModulePullback_map_coheratorAdjunction_counit_app B S hS 𝒳 E h F.obj F.property
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 07B1 (1)(c).** For `𝓕` in `LQCoh^fbc(𝒪_𝒳)`, `Q(𝓕) = g_!g^{-1}𝓕`, naturally in `𝓕`,
as objects of `QCoh(𝒪_𝒳)`, where `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` is the coherator of
**Stacks 0778** (`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator`), `g^{-1}𝓕` is
quasi-coherent by (1)(b) and `g_!` is the inverse equivalence of (1)(a). The isomorphism at `𝓕` is
the unit `Q(𝓕) ≅ g_!g^{-1}Q(𝓕)` of (1)(a) followed by `g_!g^{-1}` of the adjunction map
`Q(𝓕) ⟶ 𝓕`. -/
@[stacks 07B1 "part (1)(c): Q(F) = g_! g^{-1} F for F in LQCoh^fbc(𝒪_𝒳), Q the coherator of 0778"]
def coheratorIsoLowerShriekModulePullback :
    AlgebraicStacks.lqcohFbcCoherator B E h S hS 𝒳 ≅
      lqcohFbcModulePullback B S hS 𝒳 E h ⋙ quasicoherentModuleLowerShriek B S hS 𝒳 :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (AlgebraicStacks.lqcohFbcCoherator B E h S hS 𝒳)
      (quasicoherentEquivalence B S hS 𝒳).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (coheratorCounitModulePullback B S hS 𝒳 E h))
      (quasicoherentModuleLowerShriek B S hS 𝒳)

end AlgebraicGeometry.Stack.LisseEtale

end
