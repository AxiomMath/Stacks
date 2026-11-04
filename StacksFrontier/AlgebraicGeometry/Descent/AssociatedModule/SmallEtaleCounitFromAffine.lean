module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesUnique

/-!
# Descent, Proposition 03DX (2) at `τ = étale` from quasi-coherence on the affine subsite

Let `S` be a scheme contained in a big étale site `B` and let `𝒢` be a sheaf of modules on the
small étale site of `S`.  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit`
proves that the counit `𝒢^{res,a} ⟶ 𝒢` of the associated-module adjunction is an isomorphism when
`𝒢` is quasi-coherent on `S_étale`, and reads off the essential surjectivity of `𝓕 ↦ 𝓕^a`.

**This file runs the same argument from a weaker hypothesis**: that the restriction of `𝒢` to the
small *affine* étale site of `S`, over the restricted structure sheaf, is quasi-coherent there.
That hypothesis is the one that matters for Stacks 0GZX, whose data is a module on
`S_{affine, étale}` and not on `S_étale`.

(A priori the hypothesis is only *weaker*: quasi-coherence transports *to* the subsite —
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` — and transporting it back appears to
ask for the Comparison Lemma for sheaves of
modules at the raised universe in which a global presentation lives, whereas
`Stacks.DenseSubsiteModules.moduleRestriction` ties the universe of the module sections to the
universe of the ring sections. It does transport back:
`AlgebraicGeometry.smallAffineEtale_isQuasicoherentOnSite_reflect` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesReflect`. The reflection
needs only the full-faithfulness half of the Comparison Lemma, which holds at every universe of
module sections — `Stacks.DenseSubsiteModules.fullyFaithful_moduleRestrictionRaised`. So the
hypothesis carried here is *equivalent* to quasi-coherence of `𝒢` on `S_étale`, and the
statements below are the same statements as the ones they copy rather than more general ones;
they remain the convenient form for Stacks 0GZX, whose data is the affine restriction.)

Nothing is lost in the two steps that consume the hypothesis.  The counit argument uses
quasi-coherence of `𝒢` only through
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`, i.e. only
through the bijectivity of the base-change comparison between *affine* objects, and that proof in
turn uses quasi-coherence only through its restriction to the affine subsite — which is the
hypothesis carried here.  So the statements below are formally more general than the ones they
copy, and the copies they make are of the proofs, not of the mathematics.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_affineRestriction`: a sheaf of
  modules on `S_étale` whose restriction to the affine subsite is quasi-coherent is cartesian
  between affine objects.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_of_affineRestriction`: its
  restriction to the small Zariski site of `S` is a quasi-coherent `𝒪_S`-module.
* `AlgebraicGeometry.SmallEtale.isIso_counit_of_affineRestriction`: **the counit is an
  isomorphism** under that hypothesis alone.
* `AlgebraicGeometry.SmallEtale.essImage_associatedModuleQcoh_of_affineRestriction`: **`𝒢` is the
  associated module of a quasi-coherent `𝒪_S`-module**, namely of its own restriction to the small
  Zariski site of `S`.

## Implementation notes

The hypothesis is phrased with `AlgebraicGeometry.smallAffineEtaleModuleRestriction`, the
restriction functor of the Comparison Lemma along the dense subsite inclusion of Stacks 04HR, so
that it is literally the quasi-coherence of a module over the structure sheaf that the small
affine étale ringed site of Stacks 0GZX carries — see
`AlgebraicGeometry.ringRestriction_smallEtale_structureSheaf`.

No `stacks` attribute is claimed.  Clause (2) of Descent, Proposition 03DX is already registered
unconditionally at `τ = étale` on
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`; what is here is an input
to Stacks 0GZX, registered where that tag is.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf of modules on the small étale site of `S` whose restriction to the affine objects
is quasi-coherent is cartesian between affine objects.**  For a morphism `f : T ⟶ T'` of objects
of `S_étale` whose underlying schemes are affine, the base-change comparison
`Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.

This is `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`
with its hypothesis weakened to the one step of its own proof that consumed it: the sections are
raised to the universe in which a global presentation is indexed, Stacks 0H04 for the chart rings
applies, and bijectivity descends back through the universe lift and through the restriction. -/
public theorem bijective_restrictionBaseChange_of_affineRestriction
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ((smallAffineEtaleModuleRestriction B S hS).obj G).IsQuasicoherentOnSite)
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T'))
    (f : T ⟶ T') :
    Function.Bijective
      (restrictionBaseChange (R := commStructurePresheaf B S hS) G.val f.op) := by
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hG
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, u}
    B S hS _ _ h₂
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) f)
  have h₄ := bijective_restrictionBaseChange_of_uliftForPresentation
    (affineChartRings B S hS) _ _ _ h₃
  have h₅ := bijective_restrictionBaseChange_of_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (commStructurePresheaf B S hS) _ G _ h₄
  rwa [(SmallAffineEtale.inclusion B S hS).map_preimage] at h₅

/-- **The restriction to the small Zariski site of `S` of a sheaf of modules on `S_étale` whose
restriction to the affine objects is quasi-coherent is a quasi-coherent `𝒪_S`-module.**

`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` under the weaker hypothesis: its
base-change comparison between nested affine opens is the comparison of `𝒢` between the
corresponding affine objects of the small étale site, which is bijective by
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_affineRestriction`. -/
public theorem isQuasicoherent_restrictModule_of_affineRestriction
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ((smallAffineEtaleModuleRestriction B S hS).obj G).IsQuasicoherentOnSite) :
    _root_.SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := by
  refine Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction
    _ fun V V' hV hV' hle => bijective_restrictionBaseChange_restrictModule B S hS G hle ?_
  have aV : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)) := hV
  have aV' : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V')) := hV'
  exact bijective_restrictionBaseChange_of_affineRestriction B S hS G hG aV' aV
    ((opensToSmallEtale B S hS).map (homOfLE hle))

/-- **The counit is bijective on sections over an affine object lying over an affine open of
`S`**, under quasi-coherence of the restriction to the affine objects alone.

`AlgebraicGeometry.SmallEtale.bijective_counit_val_app_of_isAffine` with the same proof: the
base-change square of `Stacks.PresheafOfModules.restrictionBaseChange_naturality` along a
morphism `T ⟶ V` has three bijective sides, the third being the counit over `V`.  Only the side
belonging to `𝒢` changes input — it is now
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_affineRestriction`; the side
belonging to `𝓕^a` is unchanged, `𝓕^a` being quasi-coherent on the site outright. -/
public theorem bijective_counit_val_app_of_isAffine_of_affineRestriction
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ((smallAffineEtaleModuleRestriction B S hS).obj G).IsQuasicoherentOnSite)
    (h : _root_.SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    {T : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)))
    (g : T ⟶ (opensToSmallEtale B S hS).obj V) :
    Function.Bijective
      (((associatedModuleAdjunction B S hS).counit.app G).val.app (op T)) := by
  classical
  set θ := (associatedModuleAdjunction B S hS).counit.app G with hθ
  have hqa : ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)
      ).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ h
  -- the two horizontal base-change comparisons are bijective
  have hG' := bijective_restrictionBaseChange_of_affineRestriction B S hS G hG hT hV g
  have hA' := bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS
    ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)) hqa hT hV g
  -- the left vertical map is the extension of scalars of the counit over `V`
  have hV' : Function.Bijective (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) :=
    bijective_counit_val_app_opensObj B S hS G h V
  have hVi : IsIso (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hV'
  have hE : Function.Bijective ((ModuleCat.extendScalars
      ((commStructurePresheaf B S hS).map g.op).hom).map
      (θ.val.app (op ((opensToSmallEtale B S hS).obj V)))) :=
    ConcreteCategory.bijective_of_isIso
      (f := ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).mapIso
        (@asIso _ _ _ _ _ hVi)).hom)
  -- the square, read on elements
  have hsq := Stacks.PresheafOfModules.restrictionBaseChange_naturality
    (R := commStructurePresheaf B S hS) θ.val g.op
  have hpt : ∀ x, Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS) G.val g.op
        ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).map
          (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) x) =
      θ.val.app (op T) (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x) :=
    fun x => ConcreteCategory.congr_hom hsq x
  have hcomp : Function.Bijective (fun x => θ.val.app (op T)
      (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x)) := by
    refine (funext hpt : _ = _) ▸ ?_
    exact hG'.comp hE
  exact (hA'.of_comp_iff _).1 hcomp

/-- **The counit is an isomorphism** whenever the restriction of `𝒢` to the affine objects of the
small étale site is quasi-coherent there.

`AlgebraicGeometry.SmallEtale.isIso_counit` with that hypothesis in place of quasi-coherence of
`𝒢` on `S_étale`; quasi-coherence of the restriction of `𝒢` to the small Zariski site of `S`,
which that statement carries as a second hypothesis, is now a consequence of the first. -/
public theorem isIso_counit_of_affineRestriction
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ((smallAffineEtaleModuleRestriction B S hS).obj G).IsQuasicoherentOnSite) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app G) := by
  have h : _root_.SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) :=
    isQuasicoherent_restrictModule_of_affineRestriction B S hS G hG
  set θ := (associatedModuleAdjunction B S hS).counit.app G with hθ
  have hbij : ∀ (T : SmallEtale B S hS) (i : (affineSubordinateCover B S hS T).I₀),
      Function.Bijective (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((_root_.SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).app
        (op ((affineSubordinateCover B S hS T).X i))) := by
    intro T i
    exact bijective_counit_val_app_of_isAffine_of_affineRestriction B S hS G hG h
      (T := openSubObj B S hS T i.down.1.1) i.down.1.2 i.down.2.1.2
      (openSubHomOver B S hS T i.down.2.2)
  have hinj : Sheaf.IsLocallyInjective
      ((_root_.SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} x y hxy => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T.unop)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    refine (hbij T.unop i).1 ?_
    have hn := fun z => ConcreteCategory.congr_hom
      (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((_root_.SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).naturality
        ((affineSubordinateCover B S hS T.unop).f i).op) z
    exact (hn x).trans ((congrArg _ hxy).trans (hn y).symm)
  have hsurj : Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} s => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (hbij T i).2 _
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((_root_.SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).1 ⟨hinj, hsurj⟩
  exact (isIso_iff_of_reflects_iso θ
    (_root_.SheafOfModules.toSheaf (structureSheaf B S hS))).1 hiso

/-- **A sheaf of modules on `S_étale` whose restriction to the affine objects is quasi-coherent is
the associated module of a quasi-coherent `𝒪_S`-module**, namely of its own restriction to the
small Zariski site of `S`; the isomorphism is the counit of the adjunction.

`AlgebraicGeometry.SmallEtale.essImage_associatedModuleQcoh_of_isQuasicoherent_restrictModule`
under the weaker hypothesis. -/
public theorem essImage_associatedModuleQcoh_of_affineRestriction
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ((smallAffineEtaleModuleRestriction B S hS).obj G).IsQuasicoherentOnSite) :
    (associatedModuleQcoh B S hS).essImage G :=
  ⟨⟨(restrictModule B S hS).obj G,
      isQuasicoherent_restrictModule_of_affineRestriction B S hS G hG⟩,
    ⟨@asIso _ _ _ _ _ (isIso_counit_of_affineRestriction B S hS G hG)⟩⟩

end AlgebraicGeometry.SmallEtale

end
