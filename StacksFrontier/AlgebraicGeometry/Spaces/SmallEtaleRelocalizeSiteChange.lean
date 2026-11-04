module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionBaseChangeIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealQuotientEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# An algebraic space over `S` with a morphism to `W`, read over `W`

Let `h : W ⟶ S` be a morphism of a big fppf site and let `X` be an algebraic space over `S`
with a morphism `π : X ⟶ W`.  By Stacks 04SG there is an algebraic space `X'` over `W` whose
lower-shriek extension `Λ_h X'` is `X` over `W`: this file names it
(`AlgebraicGeometry.Space.siteChangeSpace`) together with the identification
`AlgebraicGeometry.Space.siteChangeIso : Λ_h X' ≅ X`, a morphism over `W`.

It then compares the scalars from `W` on the two sides.  The functions on `W` act on
`𝒪_X`-modules by pulling back along `π` (`AlgebraicGeometry.Space.targetScalars`) and on
`𝒪_{X'}`-modules by pulling back along the structure morphism of `X'`; the equivalence
`Mod(𝒪_X) ≌ Mod(𝒪_{X'})`, the direct image along the identification followed by the
relocalization equivalence of `StacksFrontier/AlgebraicGeometry/Spaces/RelocalizeModules.lean`,
carries the one action to the other.  Consequently it carries quotients `M / J M` by ideals of
functions on `W` to the corresponding quotients (`AlgebraicGeometry.Space.siteChangeQuotientIso`).

## Main definitions

* `AlgebraicGeometry.Space.siteChangeSpace`, `AlgebraicGeometry.Space.siteChangeIso`: the space
  `X'` over `W` and the identification `Λ_h X' ≅ X` over `W`.
* `AlgebraicGeometry.Space.siteChangeModules`: the equivalence `Mod(𝒪_X) ⥤ Mod(𝒪_{X'})`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The structural morphism `Λ_h Y ⟶ W` of the lower-shriek extension of an algebraic space over
`W`, as a morphism of algebraic spaces over `S`. -/
abbrev relocalizeStructure (Y : AlgebraicSpaces B W hW) :
    relocalizeSpace B hW hS h Y ⟶ schemeSpace (Over.mk h) :=
  ObjectProperty.homMk (OverShriek.relocalizeToYoneda h Y.1)

variable {S W hS hW h}
variable (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h))

/-- **The algebraic space over `W` underlying an algebraic space over `S` with a morphism to `W`**
(Stacks 04SG, the quasi-inverse). -/
abbrev siteChangeSpace : AlgebraicSpaces B W hW :=
  (spacesOverSmallerBaseEquivalence B W S hW hS h).inverse.obj ⟨Over.mk π.hom, X.2⟩

/-- The identification `Λ_h X' ≅ X` of the lower-shriek extension of the space over `W` with `X`,
read off the counit of Stacks 04SG. -/
def siteChangeIso :
    relocalizeSpace B hW hS h (siteChangeSpace B X π) ≅ X :=
  let e := (spacesOverSmallerBaseEquivalence B W S hW hS h).counitIso.app ⟨Over.mk π.hom, X.2⟩
  let c := (smallerBasePresheafForgetIso B W S hW hS h).app (siteChangeSpace B X π).1
  ObjectProperty.isoMk _ (c.symm ≪≫ (Over.forget _).mapIso
    ((ObjectProperty.ι _).mapIso e))

/-- The identification `Λ_h X' ≅ X` is a morphism over `W`. -/
@[reassoc (attr := simp)]
theorem siteChangeIso_hom_comp :
    (siteChangeIso B X π).hom ≫ π = relocalizeStructure B W S hW hS h (siteChangeSpace B X π) := by
  let e := (spacesOverSmallerBaseEquivalence B W S hW hS h).counitIso.app ⟨Over.mk π.hom, X.2⟩
  refine ObjectProperty.hom_ext _ ?_
  have hw := Over.w ((ObjectProperty.ι _).map e.hom)
  ext V s
  have h₁ := congrArg Over.Hom.left (ConcreteCategory.congr_hom (congrArg (fun q => q.app V) hw)
    (((smallerBasePresheafForgetIso B W S hW hS h).inv.app (siteChangeSpace B X π).1).app V s))
  exact Over.OverMorphism.ext (h₁.trans (congrArg Over.Hom.left
    (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B W S hW hS h
      (siteChangeSpace B X π) V s)))

/-! ### The scalars from `W` -/

section Scalars

variable {X' Y : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- The scalars of `AlgebraicGeometry.Space.targetScalars` are the pulled-back functions of
`AlgebraicGeometry.Space.pullbackToGlobalFunctions`. -/
theorem targetScalars_apply_eq (π' : X' ⟶ schemeSpace T)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    targetScalars B S hS π' x = pullbackToGlobalFunctions B S hS X' T π' x :=
  rfl

/-- **The direct image commutes with multiplication by pulled-back functions**, in the spelling of
`AlgebraicGeometry.Space.targetScalars`. -/
theorem modulePushforward_map_globalSmul_targetScalars (f : X' ⟶ Y) (ρ : Y ⟶ schemeSpace T)
    (F : Modules.{u, u} B S hS X'.1 X'.2) (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (modulePushforward B S hS f).map
        (Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B S hS (f ≫ ρ) x) F) =
      Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B S hS ρ x)
        ((modulePushforward B S hS f).obj F) :=
  modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS f ρ F x

end Scalars

/-- **Restriction to the small étale site of `Y` carries the scalars of `Λ_h Y ⟶ W` to the scalars
of `Y ⟶ W`.**  The two pulled-back functions on a chart of `Y` and on the corresponding chart of
`Λ_h Y` are pullbacks along the same morphism of schemes, the structure morphism of the chart to
`W`. -/
theorem relocalizeModulesEquivalence_inverse_map_globalSmul (Y : AlgebraicSpaces B W hW)
    (f' : Y ⟶ schemeSpace (baseTerminal B W hW))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (Over.mk h), ⊤))
    (M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h Y).1
      (relocalizeSpace B hW hS h Y).2) :
    (relocalizeModulesEquivalence B hW hS h Y.1 Y.2).inverse.map
        (Stacks.Cohomology.SiteModules.globalSmul _
          (targetScalars B S hS (relocalizeStructure B W S hW hS h Y) x) M) =
      Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B W hW f' x)
        ((relocalizeModulesEquivalence B hW hS h Y.1 Y.2).inverse.obj M) := by
  have hcoef : ∀ V : (SmallEtale B W hW Y.1)ᵒᵖ,
      (targetScalars B S hS (relocalizeStructure B W S hW hS h Y) x).1
        (op ((SmallEtale.relocalize B hW hS h Y.1 Y.2).functor.obj V.unop) :
          (smallEtaleRingedSite B S hS _ (relocalizeSpace B hW hS h Y).2).Cᵒᵖ) =
      (targetScalars B W hW f' x).1 V := by
    intro V
    have h1 : chartToTarget B S hS (relocalizeStructure B W S hW hS h Y)
        ((SmallEtale.relocalize B hW hS h Y.1 Y.2).functor.obj V.unop) =
        relocalizeOverHom B W S hW hS h V.unop.1.left := by
      apply yoneda.map_injective
      rw [yoneda.map_preimage]
      ext V' k
      exact Over.OverMorphism.ext rfl
    have h2 : (chartToTarget B W hW f' V.unop).left = V.unop.1.left.hom := by
      simpa using Over.w (chartToTarget B W hW f' V.unop)
    show ((BigFppfOver.toScheme B S hS).map (chartToTarget B S hS
        (relocalizeStructure B W S hW hS h Y)
        ((SmallEtale.relocalize B hW hS h Y.1 Y.2).functor.obj V.unop))).appTop.hom x =
      ((BigFppfOver.toScheme B W hW).map (chartToTarget B W hW f' V.unop)).appTop.hom x
    rw [h1]
    show ((B.inclusion.map V.unop.1.left.hom).appTop).hom x =
      ((B.inclusion.map (chartToTarget B W hW f' V.unop).left).appTop).hom x
    rw [h2]
  ext V m
  exact congrArg (fun c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS _ (relocalizeSpace B hW hS h Y).2).O).obj.obj
        (op ((SmallEtale.relocalize B hW hS h Y.1 Y.2).functor.obj V.unop) :
          (smallEtaleRingedSite B S hS _ (relocalizeSpace B hW hS h Y).2).Cᵒᵖ) =>
      c • (show M.val.obj (op ((SmallEtale.relocalize B hW hS h Y.1 Y.2).functor.obj
        V.unop) : (smallEtaleRingedSite B S hS _ (relocalizeSpace B hW hS h Y).2).Cᵒᵖ)
          from m)) (hcoef V)

/-! ### The equivalence of module categories -/

/-- The direct image of modules along the inverse of an isomorphism of algebraic spaces is an
equivalence of categories. -/
instance isEquivalence_modulePushforward_inv {X' Y : AlgebraicSpaces B S hS} (e : X' ≅ Y) :
    (modulePushforward B S hS e.inv).IsEquivalence :=
  haveI : (modulePullback B S hS e.inv).IsEquivalence :=
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence e.symm).isEquivalence_functor
  (modulePullbackAdjunction B S hS e.inv).isEquivalence_right_of_isEquivalence_left

/-- **The `𝒪_X`-modules are the `𝒪_{X'}`-modules**: the direct image along the identification
`X ≅ Λ_h X'` followed by restriction to the small étale site of `X'`. -/
def siteChangeModules :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      Modules.{u, u} B W hW (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 :=
  modulePushforward B S hS (siteChangeIso B X π).inv ⋙
    (relocalizeModulesEquivalence B hW hS h (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2).inverse

/-- The functor `siteChangeModules` from `𝒪_X`-modules to `𝒪_{X'}`-modules is an equivalence of
categories. -/
instance isEquivalence_siteChangeModules : (siteChangeModules B X π).IsEquivalence :=
  haveI := isEquivalence_modulePushforward_inv B (siteChangeIso B X π)
  Functor.isEquivalence_trans _ _

/-- **The equivalence of module categories carries the scalars from `W` on `X` to those on
`X'`.** -/
theorem siteChangeModules_map_globalSmul
    (f' : siteChangeSpace B X π ⟶ schemeSpace (baseTerminal B W hW))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (Over.mk h), ⊤))
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (siteChangeModules B X π).map
        (Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B S hS π x) N) =
      Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B W hW f' x)
        ((siteChangeModules B X π).obj N) := by
  show (relocalizeModulesEquivalence B hW hS h _ _).inverse.map
      ((modulePushforward B S hS (siteChangeIso B X π).inv).map
        (Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B S hS π x) N)) = _
  conv_lhs => rw [show targetScalars B S hS π x = targetScalars B S hS ((siteChangeIso B X π).inv ≫
    relocalizeStructure B W S hW hS h (siteChangeSpace B X π)) x by
      rw [← siteChangeIso_hom_comp, Iso.inv_hom_id_assoc]]
  rw [modulePushforward_map_globalSmul_targetScalars,
    relocalizeModulesEquivalence_inverse_map_globalSmul]
  rfl

/-- **The equivalence of module categories carries `N / J N` to `N' / J N'`** for an ideal `J` of
functions on `W`, compatibly with the projections. -/
def siteChangeQuotientIso
    (f' : siteChangeSpace B X π ⟶ schemeSpace (baseTerminal B W hW))
    (N : Modules.{u, u} B S hS X.1 X.2)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj (Over.mk h), ⊤)) :
    (siteChangeModules B X π).obj (idealQuotient (targetScalars B S hS π) N J) ≅
      idealQuotient (targetScalars B W hW f') ((siteChangeModules B X π).obj N) J :=
  idealQuotientEquivalenceIso (targetScalars B S hS π) (targetScalars B W hW f')
    (siteChangeModules B X π) (siteChangeModules_map_globalSmul B X π f') N J

/-- The image under `siteChangeModules` of the projection `N ⟶ N / J N`, followed by
`siteChangeQuotientIso`, is the projection `N' ⟶ N' / J N'`. -/
@[reassoc (attr := simp)]
theorem map_idealQuotientπ_siteChangeQuotientIso_hom
    (f' : siteChangeSpace B X π ⟶ schemeSpace (baseTerminal B W hW))
    (N : Modules.{u, u} B S hS X.1 X.2)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj (Over.mk h), ⊤)) :
    (siteChangeModules B X π).map (idealQuotientπ (targetScalars B S hS π) N J) ≫
        (siteChangeQuotientIso B X π f' N J).hom =
      idealQuotientπ (targetScalars B W hW f') ((siteChangeModules B X π).obj N) J :=
  map_idealQuotientπ_idealQuotientEquivalenceIso_hom _ _ _ _ N J

end AlgebraicGeometry.Space

end
