module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposGlobalSectionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseMain
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionInverseImageGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.IsoOfInverseImageStructureSheafIso

/-!
# Isomorphisms of small étale ringed topoi over an affine object of the site

Let `X` and `Y` be algebraic spaces over a scheme `S`, mapping to an affine object `T` of the big
fppf site of `S` by `p_X : X ⟶ T` and `p_Y : Y ⟶ T`, and let
`(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of ringed topoi pulling back
the function `p_Y^♯a` to the function `p_X^♯a`, for every `a` of a set of generators of the ring
`Γ(T, 𝒪_T)`. Then the chart morphisms of `(g, g♯)` (`AlgebraicGeometry.Space.chartSchemeHom`) are
over `T`, hence over `S`: `(g, g♯)` satisfies `AlgebraicGeometry.Space.IsChartOverBase`, the
hypothesis under which Stacks 04KL holds over an arbitrary base
(`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isChartOverBase`).

Consequently Stacks 05YZ holds over `S` for such an isomorphism `(g, g♯)`: it is 2-isomorphic to
`(f_small, f♯)` for a unique `f : X ⟶ Y`, which is an isomorphism, and `f` lies over `T`
(`f ≫ p_Y = p_X`) because a morphism to an affine object is determined by its functions (Stacks
05Z1 over an arbitrary base, `AlgebraicGeometry.Space.pullbackToGlobalFunctions_injective`). For
the isomorphism of the ringed topoi of two thickenings of `X₀` determined by an isomorphism of the
inverse images of their structure sheaves
(`AlgebraicGeometry.RingedToposHom.transferOfInverseImageIso`) this gives an isomorphism of the
thickenings under `X₀` and over `T`.

Over `S = Spec ℤ` every morphism of ringed topoi has its chart morphisms over `S`
(`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal`); over an arbitrary base the condition is
not automatic, and the functions of `T` are what supply it here.

## Main results

* `AlgebraicGeometry.Space.chartRingHom_globalFunctionsOfMap`: the chart ring maps of `(g, g♯)`
  carry `p_Y^♯a` to `p_X^♯a` when `(g, g♯)` pulls back the one to the other.
* `AlgebraicGeometry.Space.isChartOverBase_of_globalSectionPullback`
* `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isChartOverBase_inverse`: Stacks 05YZ
  over an arbitrary base, for an isomorphism whose chart morphisms and those of its inverses are
  over the base.
* `AlgebraicGeometry.Space.exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions`

## References

* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleTopology_subcanonical

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for products of presheaves of sets times out
/-- Products of presheaves of sets, supplied directly: instance search for them times out. -/
local instance (priority := high) hasProducts_presheaf_SpacesTangentSpaceInjectiveChartOverBase
    (C : Type*) [Category C] : HasProducts.{0} (C ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for finite limits of sheaves of sets times out
/-- Finite limits of sheaves of sets, supplied directly: instance search for them times out. -/
local instance (priority := high) hasFiniteLimits_sheaf_SpacesTangentSpaceInjectiveChartOverBase
    {C : Type*} [Category C] (J : GrothendieckTopology C) :
    HasFiniteLimits (Sheaf J (Type u)) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for the terminal sheaf of sets times out
/-- The terminal sheaf of sets, supplied directly: instance search for it times out. -/
local instance (priority := high) hasTerminal_sheaf_SpacesTangentSpaceInjectiveChartOverBase
    {C : Type*} [Category C] (J : GrothendieckTopology C) :
    HasTerminal (Sheaf J (Type u)) :=
  inferInstance

section Functions

variable {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **The global section `p^♯a` of the structure sheaf**, on underlying sheaves of sets: the unit
section followed by multiplication by the function `p^♯a`, for `p : X ⟶ T` and `a ∈ Γ(T, 𝒪_T)`. -/
abbrev functionGlobalSection (p : X ⟶ schemeSpace T) (a : baseRing B S hS T) :
    ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O :=
  ringOneHom (structureRingSheaf B S hS X) ≫
    (moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (unitModuleMul B S hS X (globalFunctionsOfMap p a))

/-- The global section `p^♯a` on a chart is the function `p^♯a` on that chart. -/
theorem functionGlobalSection_app (p : X ⟶ schemeSpace T) (a : baseRing B S hS T)
    (W : SmallEtale B S hS X.1)
    (q : (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj (op W)) :
    (functionGlobalSection p a).hom.app (op W) q = (globalFunctionsOfMap p a).1 (op W) := by
  rw [eq_terminalSheafSection q]
  exact unitModuleMul_val_app_one B S hS X _ W

/-- The global section `p^♯a` on a chart, read through the sections functor. -/
theorem sectionsFunctor_map_functionGlobalSection (p : X ⟶ schemeSpace T) (a : baseRing B S hS T)
    (W : SmallEtale B S hS X.1) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) (op W)).map (functionGlobalSection p a)
        (terminalSheafSection _ (op W)) = (globalFunctionsOfMap p a).1 (op W) :=
  unitModuleMul_val_app_one B S hS X _ W

/-- **Functions are determined by their global sections.** -/
theorem globalFunctionsOfMap_eq_of_functionGlobalSection_eq {T' : BigFppfOver B S hS}
    (p : X ⟶ schemeSpace T) (p' : X ⟶ schemeSpace T') (a : baseRing B S hS T)
    (a' : baseRing B S hS T') (h : functionGlobalSection p a = functionGlobalSection p' a') :
    globalFunctionsOfMap p a = globalFunctionsOfMap p' a' :=
  Subtype.ext (funext fun W =>
    (functionGlobalSection_app p a W.unop (terminalSheafSection _ W)).symm.trans
      ((congrArg (fun m => m.hom.app W (terminalSheafSection _ W)) h).trans
        (functionGlobalSection_app p' a' W.unop (terminalSheafSection _ W))))

/-- **The pullback along `(p_small, p♯)` of the function `a` of `T` is the function `p^♯a`.** -/
theorem globalSectionPullback_functionGlobalSection_id (p : X ⟶ schemeSpace T)
    (a : baseRing B S hS T) :
    (smallEtaleRingedToposHom B S hS p).globalSectionPullback
        (functionGlobalSection (𝟙 (schemeSpace T)) a) = functionGlobalSection p a :=
  (ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B S hS p a).symm

/-- **Pulling back a pulled-back function along a morphism of algebraic spaces**:
`f_small^♯(p^♯a) = (f ≫ p)^♯a`. -/
theorem globalSectionPullback_functionGlobalSection {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (p : X ⟶ schemeSpace T) (a : baseRing B S hS T) :
    (smallEtaleRingedToposHom B S hS f).globalSectionPullback (functionGlobalSection p a) =
      functionGlobalSection (f ≫ p) a :=
  globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage B S hS f p a

end Functions

section Chart

variable {X Y : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (pX : X ⟶ schemeSpace T) (pY : Y ⟶ schemeSpace T)

/-- The coordinate map of `g` at the restriction of a global section factors through the terminal
sheaf, as the pullback along `g` of that global section. -/
theorem invCoord_app_terminalSheafSection
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) (V : SmallEtale B S hS Y.1) :
    invCoord g V ((sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map t
        (terminalSheafSection _ (op V))) =
      terminal.from _ ≫ g.globalSectionPullback t := by
  have hy := GrothendieckTopology.yonedaEquiv_symm_naturality_right (SmallEtale.topology B S hS Y.1)
    V t (terminalSheafSection _ (op V))
  have hterm : IsTerminal (g.toToposHom.inverseImage.obj
      (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u))) :=
    IsTerminal.ofIso terminalIsTerminal (asIso (terminalComparison g.toToposHom.inverseImage)).symm
  have h1 : g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm (terminalSheafSection _ (op V))) =
      terminal.from _ ≫ CategoryTheory.inv (terminalComparison g.toToposHom.inverseImage) :=
    hterm.hom_ext _ _
  have h2 : g.fSharpSet = (smallEtaleRingedTopos B S hS X).forgetRing.map g.fSharpInverseImage :=
    (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget g).symm
  change g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm (t.hom.app (op V) _)) ≫ g.fSharpSet = _
  rw [← hy, Functor.map_comp, h1, h2]
  exact Category.assoc _ _ _

/-- **The chart ring maps of `(g, g♯)` on global sections**: the chart ring map of `g` at a
section `s` carries the restriction of a global section `t` of `𝒪_Y` to the restriction of its
pullback along `g`. -/
theorem chartRingHom_apply_terminalSheafSection
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) (V : SmallEtale B S hS Y.1)
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartRingHom g V U s).hom ((sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map t
        (terminalSheafSection _ (op V))) =
      (sectionsFunctor (SmallEtale.topology B S hS X.1) (op U)).map (g.globalSectionPullback t)
        (terminalSheafSection _ (op U)) := by
  refine (chartRingHom_apply g V U s _).trans ?_
  rw [invCoord_app_terminalSheafSection]
  exact congrArg (fun q => (sectionsFunctor (SmallEtale.topology B S hS X.1) (op U)).map
    (g.globalSectionPullback t) q) (eq_terminalSheafSection _)

/-- **The chart ring maps of `(g, g♯)` on functions of `T`**: if `g` pulls back `p_Y^♯a` to
`p_X^♯a`, then every chart ring map `Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)` of `g` carries `p_Y^♯a` to
`p_X^♯a`. -/
theorem chartRingHom_globalFunctionsOfMap (a : baseRing B S hS T)
    (h : g.globalSectionPullback (functionGlobalSection pY a) = functionGlobalSection pX a)
    (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartRingHom g V U s).hom ((globalFunctionsOfMap pY a).1 (op V)) =
      (globalFunctionsOfMap pX a).1 (op U) :=
  (congrArg (chartRingHom g V U s).hom
      (sectionsFunctor_map_functionGlobalSection pY a V).symm).trans
    ((chartRingHom_apply_terminalSheafSection g _ V U s).trans
      ((congrArg (fun m => (sectionsFunctor (SmallEtale.topology B S hS X.1) (op U)).map m
        (terminalSheafSection _ (op U))) h).trans
        (sectionsFunctor_map_functionGlobalSection pX a U)))

/-- **The chart morphisms are over `S` when they are over an affine `T`**, in ring-theoretic form:
if every chart ring map of `g` is compatible with the pullbacks of functions of `T` along `p_X` and
`p_Y`, then `g` satisfies `AlgebraicGeometry.Space.IsChartOverBase`. -/
theorem isChartOverBase_of_comp_chartRingHom [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (h : ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
      (s : (invRep g V).obj.obj (op U)),
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap pY V)).op ≫
          chartRingHom g V U s =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap pX U)).op) :
    IsChartOverBase g := by
  intro V _ U s
  have key : chartSchemeHom g V U s ≫ (BigFppfOver.toScheme B S hS).map (chartToBaseOfMap pY V) =
      (BigFppfOver.toScheme B S hS).map (chartToBaseOfMap pX U) :=
    ext_of_isAffine (by rw [Scheme.Hom.comp_appTop, chartSchemeHom_appTop]; exact h V U s)
  have hw : ∀ {Z : AlgebraicSpaces B S hS} (p : Z ⟶ schemeSpace T) (W : SmallEtale B S hS Z.1),
      (BigFppfOver.toScheme B S hS).map (chartToBaseOfMap p W) ≫ B.inclusion.map T.hom =
        B.inclusion.map W.obj.left.hom := fun p W =>
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w _))
  rw [← hw pY V, ← Category.assoc, key, hw pX U]

/-- **The chart morphisms of a morphism pulling back functions are over the base.** If `g` pulls
back `p_Y^♯a` to `p_X^♯a` for every `a` of a set generating the ring `Γ(T, 𝒪_T)`, `T` affine, then
the chart morphisms of `g` are over `S`. -/
theorem isChartOverBase_of_globalSectionPullback [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (s : Set (baseRing B S hS T)) (hs : Subring.closure s = ⊤)
    (h : ∀ a ∈ s,
      g.globalSectionPullback (functionGlobalSection pY a) = functionGlobalSection pX a) :
    IsChartOverBase g :=
  isChartOverBase_of_comp_chartRingHom g pX pY fun V _ U σ =>
    CommRingCat.hom_ext (RingHom.eq_of_eqOn_set_dense hs fun a ha =>
      chartRingHom_globalFunctionsOfMap g pX pY a (h a ha) V U σ)

/-- **Pulling back functions along the inverse of an isomorphism of ringed topoi**: if an
isomorphism `g` pulls back `p_Y^♯a` to `p_X^♯a`, its inverse pulls back `p_X^♯a` to `p_Y^♯a`. -/
theorem inverse_globalSectionPullback_functionGlobalSection
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp] (a : baseRing B S hS T)
    (h : g.globalSectionPullback (functionGlobalSection pY a) = functionGlobalSection pX a) :
    g.inverse.globalSectionPullback (functionGlobalSection pX a) = functionGlobalSection pY a := by
  rw [← h, ← globalSectionPullback_functionGlobalSection_id pY a]
  exact RingedToposHom.globalSectionPullback_inverse_globalSectionPullback
    (smallEtaleRingedToposHom B S hS pY) g _

/-- **A morphism 2-isomorphic to one pulling back functions lies over `T`** (Stacks 05Z1 over an
arbitrary base): if `g` pulls back `p_Y^♯a` to `p_X^♯a` for `a` in a set generating `Γ(T, 𝒪_T)`,
`T` affine, and `g` is 2-isomorphic to `(f_small, f♯)`, then `f ≫ p_Y = p_X`. -/
theorem comp_eq_of_twoIso_of_globalSectionPullback [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (s : Set (baseRing B S hS T)) (hs : Subring.closure s = ⊤)
    (h : ∀ a ∈ s, g.globalSectionPullback (functionGlobalSection pY a) = functionGlobalSection pX a)
    (f : X ⟶ Y)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f)) :
    f ≫ pY = pX := by
  refine pullbackToGlobalFunctions_injective B S hS X T
    (RingHom.eq_of_eqOn_set_dense hs fun a ha => ?_)
  have hf := globalFunctionsOfMap_eq_of_functionGlobalSection_eq (f ≫ pY) pX a a
    ((globalSectionPullback_functionGlobalSection f pY a).symm.trans
      ((RingedToposHom.globalSectionPullback_eq_of_twoIso t _).symm.trans (h a ha)))
  exact Subtype.ext (funext fun j => congrArg (fun r => r.1 j) hf)

end Chart

/-! ### Stacks 05YZ over a base -/

section Iso

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 05YZ over an arbitrary base.** An isomorphism `(g, g♯)` of the small étale ringed
topoi of two algebraic spaces over `S`, whose chart morphisms, those of its inverse and those of
the inverse of that are over `S`, is 2-isomorphic to `(f_small, f♯)` for a unique morphism
`f : X ⟶ Y` of algebraic spaces over `S`, and every such `f` is an isomorphism. -/
theorem existsUnique_spaceHom_twoIso_of_isChartOverBase_inverse
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp]
    (hb : IsChartOverBase g) (hb' : IsChartOverBase g.inverse)
    (hb'' : IsChartOverBase g.inverse.inverse) :
    (∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS f))) ∧
    ∀ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS f)) → IsIso f := by
  obtain ⟨f', ⟨s'⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isChartOverBase hb'
    (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g.inverse)
  obtain ⟨f'', ⟨s''⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isChartOverBase hb''
    (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g.inverse.inverse)
  exact ⟨existsUnique_spaceHom_twoIso_of_isChartOverBase hb
      (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g),
    fun _ ⟨s⟩ ↦ isIso_of_twoIso_of_inverse B S hS g s s' s''⟩

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (pX : X ⟶ schemeSpace T) (pY : Y ⟶ schemeSpace T)
  (s : Set (baseRing B S hS T)) (hs : Subring.closure s = ⊤)

include hs in
/-- **Stacks 05YZ over an affine object of the site**: an isomorphism `(g, g♯)` of small étale
ringed topoi pulling back the functions `p_Y^♯a` to `p_X^♯a`, for `a` in a set generating
`Γ(T, 𝒪_T)`, is 2-isomorphic to `(f_small, f♯)` for an isomorphism `f : X ⟶ Y` over `T`. -/
theorem exists_isIso_twoIso_comp_eq_of_globalSectionPullback
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    [g.toToposHom.pushforward.IsEquivalence] [IsIso g.fSharp]
    (h : ∀ a ∈ s,
      g.globalSectionPullback (functionGlobalSection pY a) = functionGlobalSection pX a) :
    ∃ f : X ⟶ Y, IsIso f ∧ Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS f)) ∧ f ≫ pY = pX := by
  have h' : ∀ a ∈ s, g.inverse.globalSectionPullback (functionGlobalSection pX a) =
      functionGlobalSection pY a := fun a ha =>
    inverse_globalSectionPullback_functionGlobalSection g pX pY a (h a ha)
  have h'' : ∀ a ∈ s, g.inverse.inverse.globalSectionPullback (functionGlobalSection pY a) =
      functionGlobalSection pX a := fun a ha =>
    inverse_globalSectionPullback_functionGlobalSection g.inverse pY pX a (h' a ha)
  obtain ⟨⟨f, ⟨t⟩, -⟩, hiso⟩ := existsUnique_spaceHom_twoIso_of_isChartOverBase_inverse g
    (isChartOverBase_of_globalSectionPullback g pX pY s hs h)
    (isChartOverBase_of_globalSectionPullback g.inverse pY pX s hs h')
    (isChartOverBase_of_globalSectionPullback g.inverse.inverse pX pY s hs h'')
  exact ⟨f, hiso f ⟨t⟩, ⟨t⟩, comp_eq_of_twoIso_of_globalSectionPullback g pX pY s hs h f t⟩

end Iso

/-! ### Thickenings with isomorphic inverse images of structure sheaves -/

section Thickening

variable {X X'₁ X'₂ : AlgebraicSpaces B S hS}
  (i₁ : X ⟶ X'₁) (i₂ : X ⟶ X'₂)
  [(smallEtaleRingedToposHom B S hS i₁).toToposHom.pushforward.IsEquivalence]
  [(smallEtaleRingedToposHom B S hS i₂).toToposHom.pushforward.IsEquivalence]
  (d : inverseImageStructureSheaf B S hS i₁ ≅ inverseImageStructureSheaf B S hS i₂)
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (p₁ : X'₁ ⟶ schemeSpace T) (p₂ : X'₂ ⟶ schemeSpace T)
  (s : Set (baseRing B S hS T)) (hs : Subring.closure s = ⊤)

include hs in
/-- **Two thickenings of `X` over an affine `T` whose structure sheaves are isomorphic on `X`
compatibly with the functions of `T` are isomorphic under `X` and over `T`.** Let
`d : i₁⁻¹𝒪_{X'₁} ≅ i₂⁻¹𝒪_{X'₂}` be compatible with the maps to `𝒪_X` and carry, for every `a` in
a set of generators of `Γ(T, 𝒪_T)`, the inverse image of the function `p₁^♯a` to that of `p₂^♯a`.
Then there is an isomorphism `f : X'₁ ≅ X'₂` with `i₁ ≫ f = i₂` and `f ≫ p₂ = p₁`, inducing the
isomorphism of small étale ringed topoi determined by `d`. -/
theorem exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions
    (hd : d.hom ≫ structureSharpInverseImage B S hS i₂ = structureSharpInverseImage B S hS i₁)
    (hfun : ∀ a ∈ s, (smallEtaleRingedToposHom B S hS i₂).toToposHom.inverseImage.globalSectionMap
        (functionGlobalSection p₂ a) =
      (smallEtaleRingedToposHom B S hS i₁).toToposHom.inverseImage.globalSectionMap
          (functionGlobalSection p₁ a) ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map d.hom) :
    ∃ f : X'₁ ≅ X'₂, i₁ ≫ f.hom = i₂ ∧ f.hom ≫ p₂ = p₁ ∧
      InducesSmallEtaleRingedToposHom B S hS f.hom
        (RingedToposHom.transferOfInverseImageIso (X := smallEtaleRingedTopos B S hS X)
          (Y₁ := smallEtaleRingedTopos B S hS X'₁) (Y₂ := smallEtaleRingedTopos B S hS X'₂)
          (smallEtaleRingedToposHom B S hS i₁)
          (smallEtaleRingedToposHom B S hS i₂) d) := by
  have := RingedToposHom.isEquivalence_transferOfInverseImageIso_pushforward
    (smallEtaleRingedToposHom B S hS i₁) (smallEtaleRingedToposHom B S hS i₂) d
  have := RingedToposHom.isIso_transferOfInverseImageIso_fSharp
    (smallEtaleRingedToposHom B S hS i₁) (smallEtaleRingedToposHom B S hS i₂) d
  have hg : ∀ a ∈ s, (RingedToposHom.transferOfInverseImageIso
      (smallEtaleRingedToposHom B S hS i₁) (smallEtaleRingedToposHom B S hS i₂) d
        ).globalSectionPullback (functionGlobalSection p₂ a) = functionGlobalSection p₁ a :=
    fun a ha => RingedToposHom.globalSectionPullback_transferOfInverseImageIso _ _ _
      (smallEtaleRingedToposHom B S hS p₁) _ _
      (globalSectionPullback_functionGlobalSection_id p₁ a) _ (hfun a ha)
  obtain ⟨f, hiso, ⟨t⟩, hp⟩ := exists_isIso_twoIso_comp_eq_of_globalSectionPullback p₁ p₂ s hs _ hg
  exact ⟨asIso f, eq_of_smallEtaleRingedToposHom_twoIso B S hS (i₁ ≫ f) i₂
    (((smallEtaleRingedToposHomCompTwoIso B S hS i₁ f).symm.trans
      (RingedToposHom.TwoIso.whiskerLeft (A := smallEtaleRingedTopos B S hS X)
        (B := smallEtaleRingedTopos B S hS X'₁) (C := smallEtaleRingedTopos B S hS X'₂)
        (smallEtaleRingedToposHom B S hS i₁) t.symm)).trans
      (RingedToposHom.transferOfInverseImageIsoCompTwoIso _ _ d hd)), hp, ⟨t.symm⟩⟩

end Thickening

end AlgebraicGeometry.Space

end
