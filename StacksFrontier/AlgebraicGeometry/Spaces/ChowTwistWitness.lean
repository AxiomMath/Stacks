module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedSheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistCohomology
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.ZeroNotInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapVanishingOffSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The witness of the dévissage for the higher direct images along a proper morphism

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces with `Y` represented by an affine
Noetherian scheme.  The proof of Stacks 08AR applies the dévissage of Stacks 08AN to the property
that all cohomology modules of an `𝒪_X`-module along `f` are finite, and the third condition of
that dévissage asks, for every reduced closed subspace `Z ⊆ X` with irreducible space of points,
for a coherent module with scheme-theoretic support `Z` having the property.  The source builds it
from Chow's lemma for algebraic spaces (Stacks 089J): a proper surjective `π : Z' ⟶ Z` from a
scheme H-quasi-projective over the base, an ample invertible `𝓛` on `Z'`, and the direct image
`π_*(𝓛^{⊗d})` for `d` large, whose higher direct images along `π` vanish by Serre's theorem
(Stacks 02O1, 08AQ), so that its cohomology along `Z ⟶ Y` is the cohomology of `𝓛^{⊗d}` on `Z'`.

This file carries that out.

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteCohomologyOver`: all cohomology modules of an `𝒪_X`-module
  along a morphism to an affine scheme `V` are finite over the functions on `V`.

## Main results

* `AlgebraicGeometry.isZero_pullback_of_generatingSections`: the pullback of a globally generated
  module of a scheme vanishes as soon as it has no nonzero global sections.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_chart`: the higher
  direct images along a representable quasi-compact quasi-separated morphism from a scheme vanish
  as soon as the cohomology of the restriction to the base change of one surjective affine chart
  of the target vanishes.
* `AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver`: the
  third condition of Stacks 08AN for `AlgebraicGeometry.Space.HasFiniteCohomologyOver` along a
  proper morphism to an affine Noetherian scheme.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry

/-- **The pullback of a globally generated module with no global sections is zero.**  Let
`g : T ⟶ W` be a morphism of schemes and `𝒢` an `𝒪_W`-module generated by global sections.  If
`g^*𝒢` has no nonzero global sections then `g^*𝒢 = 0`: the generating sections pull back to
generating sections of `g^*𝒢`, the pullback functor being a left adjoint which preserves the
structure sheaf, and they all vanish, so the zero map out of a free module is an epimorphism
onto `g^*𝒢`. -/
theorem isZero_pullback_of_generatingSections {T W : Scheme.{u}} (g : T ⟶ W) {G : W.Modules}
    (σ : G.GeneratingSections)
    (h : Subsingleton (((Scheme.Modules.pullback g).obj G).val.obj (op ⊤))) :
    IsZero ((Scheme.Modules.pullback g).obj G) := by
  have : (TopologicalSpace.Opens.map g.base).Final := CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.pullback g.toRingCatSheafHom) :=
    (SheafOfModules.pullbackPushforwardAdjunction g.toRingCatSheafHom).leftAdjoint_preservesColimits
  have hiso : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map g.base) g.toRingCatSheafHom
  let τ := σ.map (SheafOfModules.pullback g.toRingCatSheafHom)
    (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) hiso).symm
  have hsec : Subsingleton ((SheafOfModules.pullback g.toRingCatSheafHom).obj G).sections :=
    ⟨fun s t => by
    apply Subtype.ext
    funext U
    have hst := h.elim (s.1 (op ⊤)) (t.1 (op ⊤))
    rw [← s.2 (homOfLE le_top : U.unop ⟶ ⊤).op, ← t.2 (homOfLE le_top : U.unop ⟶ ⊤).op, hst]⟩
  have hπ : τ.π = 0 := ((SheafOfModules.pullback g.toRingCatSheafHom).obj G).freeHomEquiv.injective
    (Subsingleton.elim _ _)
  have : Epi (0 : SheafOfModules.free τ.I ⟶ (SheafOfModules.pullback g.toRingCatSheafHom).obj G) :=
    hπ ▸ τ.epi
  exact IsZero.of_epi_zero (SheafOfModules.free (R := T.ringCatSheaf) τ.I)
    ((SheafOfModules.pullback g.toRingCatSheafHom).obj G)

end AlgebraicGeometry

/-- An isomorphism of sheaves of modules identifies their sections over every object, so a
module whose sections over an object are trivial transports that to any isomorphic module. -/
theorem SheafOfModules.subsingleton_val_obj_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {F G : SheafOfModules.{u} R}
    (e : F ≅ G) (X : Cᵒᵖ) [Subsingleton (G.val.obj X)] : Subsingleton (F.val.obj X) :=
  have e' : F.val.obj X ≅ G.val.obj X :=
    { hom := e.hom.val.app X
      inv := e.inv.val.app X
      hom_inv_id := congrArg (fun k : F ⟶ F => k.val.app X) e.hom_inv_id
      inv_hom_id := congrArg (fun k : G ⟶ G => k.val.app X) e.inv_hom_id }
  e'.toLinearEquiv.toEquiv.subsingleton

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_witness
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-! ### Vanishing of higher direct images tested on one affine chart -/

/-- **The higher direct images along a representable morphism vanish when the cohomology over
one surjective affine chart of the target does.**  Let `ρ : X ⟶ Y` be representable, quasi-compact
and quasi-separated, let `𝓜` be a quasi-coherent `𝒪_X`-module and let `A` be an étale chart of
`Y` with affine scheme which is surjective.  If, for some `q > 0`, the cohomology over the
identity chart of the restriction of `𝓜` to the base change `T = A ×_Y X` vanishes in degree `q`,
then `R^q ρ_*𝓜 = 0`.

The module `R^q ρ_*𝓜` is quasi-coherent (Stacks 0720), and its restriction to `A` is
`R^q ρ'_*(𝓜|_T)` for the base change `ρ' : T ⟶ A` (Stacks 071Z), a quasi-coherent module on the
algebraic space represented by an affine scheme, whose sections over the identity chart are the
cohomology of `𝓜|_T` over the identity chart, by the degeneration of the Leray spectral sequence.
A quasi-coherent module on an affine scheme without sections is zero, and a module whose
restriction to a surjective chart is zero is zero. -/
theorem isZero_rightDerived_modulePushforward_of_isZero_chart {X Y : AlgebraicSpaces B S hS}
    (ρ : X ⟶ Y) (hρ : yoneda.relativelyRepresentable ρ.hom)
    (hρqc : IsQuasiCompact B S hS ρ.hom) (hρqs : IsQuasiSeparated B S hS ρ.hom)
    (A : SmallEtale B S hS Y.1) (hA : IsAffine (chartScheme A))
    (hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf A.1.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q)
    (h : IsZero (((SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS X ((smallBaseChange B S hS ρ hρ).obj A)).1
          (chartSpace B S hS X ((smallBaseChange B S hS ρ hρ).obj A)).2).O))
        (op (idEtaleChart B S hS
          (chartFppfObject B S hS X ((smallBaseChange B S hS ρ hρ).obj A))))).rightDerived q).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS X ((smallBaseChange B S hS ρ hρ).obj A))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS ρ hρ).obj A))).obj M))) :
    IsZero (((modulePushforward B S hS ρ).rightDerived q).obj M) := by
  let T := (smallBaseChange B S hS ρ hρ).obj A
  let ρ' := smallBaseChangeChartMap B S hS ρ hρ A
  let M' := (etaleModulePullback B S hS (chartToSpace B S hS X T)
    (isEtale_chartToSpace B S hS X T)).obj M
  have hM' : M'.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS X T)
      (isEtale_chartToSpace B S hS X T) M hM
  have hsq := isPullback_smallBaseChangeChart B S hS ρ hρ A
  have hρ'qc : IsQuasiCompact B S hS ρ'.hom :=
    isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hsq) hρqc
  have hρ'qs : IsQuasiSeparated B S hS ρ'.hom :=
    isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hsq) hρqs
  have hYA : IsAffineSpace B S hS (chartSpace B S hS Y A).1 :=
    isAffineSpace_yoneda B S hS _ hA
  have hK := fun j : ℕ =>
    isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_target B S hS ρ' hYA
      hρ'qc hρ'qs j M' hM'
  let K := ((modulePushforward B S hS ρ').rightDerived q).obj M'
  have hterm := isTerminalIdEtaleChart B S hS (chartFppfObject B S hS Y A)
  have hR : ∀ j : ℕ, Stacks.RightDerivedComp.acyclic (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS Y A).1 (chartSpace B S hS Y A).2).O))
          (op (idEtaleChart B S hS (chartFppfObject B S hS Y A))))
        (((modulePushforward B S hS ρ').rightDerived j).obj M') := fun j m hm =>
    isZero_rightDerived_evaluation_of_isAffineChart B S hS _ _ _ (hK j)
      (idEtaleChart B S hS (chartFppfObject B S hS Y A)) hA m hm
  have hKz : IsZero K := by
    refine isZero_of_isQuasicoherentOnSite_of_subsingleton_terminal B S hS
      (chartSpace B S hS Y A) hterm hA K (hK q) ?_
    refine ModuleCat.isZero_iff_subsingleton.1 ?_
    refine IsZero.of_iso ?_ (evaluationRightDerivedIso B S hS hterm ρ' M' hR q).symm
    exact isZero_rightDerived_pushforwardEvaluation_of_isZero_rightDerived_evaluation B S hS
      hterm ρ' (isTerminalIdEtaleChart B S hS (chartFppfObject B S hS X T)) M' q h
  refine isZero_of_isZero_modulePullback_chart B S hS (chartFppfObject B S hS Y A)
    (chartToSpace B S hS Y A) (isEtale_chartToSpace B S hS Y A) hsurj ?_
  refine IsZero.of_iso ?_ ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y A)
    (isEtale_chartToSpace B S hS Y A)).app _)
  exact hKz.of_iso ((moduleHigherPushforwardChartBaseChangeIso B S hS ρ hρ A q).app M).symm

/-! ### The property and its witness -/

/-- **Finiteness of the cohomology along a morphism to an affine scheme.**  For a morphism
`f : X ⟶ Y` to the algebraic space represented by `V`, an `𝒪_X`-module has finite cohomology
along `f` when, in every degree, the right derived functor of `Γ(V, f_* −)`, read over the
identity chart of `V`, takes a finite value over the functions on `V`.  For `V` affine this is
finiteness of `H^p(X, −)` over `Γ(V, 𝒪_V)`. -/
def HasFiniteCohomologyOver (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (G : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
    (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  ∀ p : ℕ, Module.Finite (chartRing B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
    (idEtaleChart B S hS V))
    (((modulePushforward B S hS f ⋙ SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))).rightDerived p).obj G)

/-- **An ample invertible module on a scheme H-quasi-projective over an affine scheme.**  An
H-quasi-projective morphism is quasi-projective (Stacks 01VY), the structure sheaf of an affine
scheme is ample, and the source of a quasi-projective morphism to a base carrying an ample
invertible module carries one too (Stacks 0892). -/
@[sga "6 VII 3.3" "special case", sga "6 VIII 3.1" "special case"]
theorem exists_isAmple_of_isHQuasiProjective {T A : Scheme.{u}} (t : T ⟶ A) [IsAffine A]
    (ht : IsHQuasiProjective t) :
    ∃ (L : T.Modules) (_ : Stacks.Ample.IsInvertibleModule T L), Stacks.Ample.IsAmple T L :=
  have := Stacks.Ample.isInvertibleModule_unit A
  exists_isAmple_of_isQuasiProjective t (Stacks.Ample.unitModule A)
    (Stacks.Ample.isAmple_unitModule_of_isQuasiAffine A inferInstance)
    (isQuasiProjective_of_isHQuasiProjective t ht)

/-! ### The base change of a chart along a morphism from a scheme -/

/-- **The base change of an affine chart along a morphism from a scheme is affine over that
scheme.**  Let `ρ : yoneda.obj V ⟶ Y` be representable and let `A` be an étale chart of `Y` whose
structure morphism is affine.  Then the morphism from the scheme of the base change
`A ×_Y V` to the scheme `V`, the scheme map underlying the morphism of that chart to the identity
chart of `yoneda.obj V`, is affine: it is a represented base change of the structure morphism of
`A`, Stacks 03WG. -/
theorem isAffineHom_chartSchemeMap_smallBaseChange {V : BigFppfOver B S hS}
    {Y : AlgebraicSpaces B S hS}
    (ρ : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (hρ : yoneda.relativelyRepresentable ρ.hom) (A : SmallEtale B S hS Y.1)
    (hA : IsAffineHom B S hS A.1.hom) :
    _root_.AlgebraicGeometry.IsAffineHom (chartSchemeMap
      ((isTerminalIdEtaleChart B S hS V).from ((smallBaseChange B S hS ρ hρ).obj A))) := by
  have hP := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_yoneda B S hS _) Y.2 hA).2
  let k := (isTerminalIdEtaleChart B S hS V).from ((smallBaseChange B S hS ρ hρ).obj A)
  have hk : yoneda.map ((SmallEtale.toOver B S hS (yoneda.obj V)).map k) = hρ.fst A.1.hom := by
    have hw := CostructuredArrow.w k.hom
    exact (Category.comp_id _).symm.trans hw
  refine hP.2 ρ.hom (yoneda.map (hρ.snd A.1.hom)) ((SmallEtale.toOver B S hS (yoneda.obj V)).map k)
    ?_
  have hsq := (hρ.isPullback A.1.hom).flip
  exact (congrArg (fun z => IsPullback (yoneda.map (hρ.snd A.1.hom)) z A.1.hom ρ.hom) hk).mpr hsq

/-! ### Proper spaces over an affine Noetherian scheme -/

/-- **A morphism of the site whose Yoneda image is proper is a proper morphism of schemes.**
Properness of the represented morphism is the relative property `IsProper` of the schemes of
its represented base changes, Stacks 03ZM, and the identity square is one of them. -/
theorem isProper_toScheme_map_of_isProper_yoneda_map {U V : BigFppfOver B S hS} (m : U ⟶ V)
    (h : IsProper B S hS (yoneda.map m)) :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) := by
  have hpre := (presheaf_isProper_iff B S hS (yoneda.map m)
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (Functor.relativelyRepresentable.map yoneda m)).mp h
  change (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map m) at hpre
  have hpm := MorphismProperty.of_relative_map hpre
  exact hpm

/-- **An algebraic space proper over an affine Noetherian scheme is Noetherian**: it is
quasi-compact because the morphism and the target are, absolutely quasi-separated because the
morphism is separated and the target is a scheme, and locally Noetherian by Stacks 04ZK. -/
theorem isNoetherian_of_isProper_toAffine (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) : IsNoetherian B S hS B.contains_terminal X.1 :=
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) hf.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal X.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj V)
        B.contains_terminal ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩)
      (isQuasiSeparated_of_isSeparated B S hS hf.1),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (isAlgebraicSpace_yoneda B S hS V)
      f.hom hf.2.1.1
      (hasEtaleLocalProperty_of_representable B S hS _ _ V (Iso.refl _) inferInstance)⟩

/-! ### The witness -/

/-- **Serre's vanishing theorem along a proper morphism from a scheme to a Noetherian algebraic
space.**  Let `Q` be a Noetherian algebraic space separated over an affine object `V` of the site,
`ρ : W ⟶ Q` a proper morphism from a locally Noetherian scheme of the site, and `𝓛` an ample
invertible module on the scheme `W`.  For `d` large the higher direct images along `ρ` of the
module associated with `𝓛^{⊗ d}` vanish.

On a surjective affine Noetherian chart `A` of `Q` the base change of `W` is proper over the affine
scheme of `A`, the pullback of `𝓛` to it is ample (the base change being affine over `W`), and
Serre's theorem (Stacks 02O1) kills its higher cohomology in large degree; that cohomology computes
the higher direct images over `A`, which test their vanishing
(`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_chart`). -/
theorem exists_forall_isZero_rightDerived_modulePushforward_representedTensorPow
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {Q : AlgebraicSpaces B S hS}
    (hQN : IsNoetherian B S hS B.contains_terminal Q.1) (g : Q.1 ⟶ yoneda.obj V)
    (hgsep : IsSeparated B S hS g) (W : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (ρ' : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ Q)
    (hρrep : yoneda.relativelyRepresentable ρ'.hom) (hρp : IsProper B S hS ρ'.hom)
    (L : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    [hLinv : Stacks.Ample.IsInvertibleModule _ L] (hLample : Stacks.Ample.IsAmple _ L) :
    ∃ m : ℕ, ∀ d : ℕ, m ≤ d → ∀ q, 0 < q →
      have := hasInjectiveResolutions_modules B S hS (yoneda.obj W)
        (isAlgebraicSpace_yoneda B S hS W)
      have := modulePushforward_additive B S hS ρ'
      IsZero (((modulePushforward B S hS ρ').rightDerived q).obj
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
          ⟨Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj W) L (d : ℤ),
            Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d⟩).obj) := by
  have := hV
  obtain ⟨A, ⟨hAaff, hANoeth⟩, hAsurj, -⟩ :=
    exists_surjective_isNoetherianAffineChart B S hS B.contains_terminal Q hQN
  have hA : IsAffine (chartScheme A) := hAaff
  have hAln : IsLocallyNoetherian (chartScheme A) := isLocallyNoetherian_chart B S hS hQN.2.2 A
  have hAaffHom : IsAffineHom B S hS A.1.hom := by
    refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS A.1.hom g ?_ hgsep
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
    rw [← Functor.map_preimage yoneda (A.1.hom ≫ g)]
    exact isAffineHom_yoneda_map B S hS _
  let T₂ := (smallBaseChange B S hS ρ' hρrep).obj A
  let r₂ := chartSchemeMap ((isTerminalIdEtaleChart B S hS W).from T₂)
  have hr₂ : _root_.AlgebraicGeometry.IsAffineHom r₂ :=
    isAffineHom_chartSchemeMap_smallBaseChange B S hS ρ' hρrep A hAaffHom
  let g₂ := (BigFppfOver.toScheme B S hS).map ((smallBaseChangeProjection B S hS ρ' hρrep).app A)
  have hg₂ : _root_.AlgebraicGeometry.IsProper g₂ :=
    isProper_toScheme_smallBaseChangeProjection B S hS ρ' hρrep hρp A
  have : Stacks.Ample.IsInvertibleModule (chartScheme (idEtaleChart B S hS W)) L := hLinv
  let L₂ := (Scheme.Modules.pullback r₂).obj L
  have hL₂inv : Stacks.Ample.IsInvertibleModule (chartScheme T₂) L₂ :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback r₂ L
  have hL₂ample : Stacks.Ample.IsAmple (chartScheme T₂) L₂ :=
    Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom r₂ L hLample
  obtain ⟨m₂, hm₂⟩ := Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
    _ _ g₂ hA hAln hg₂ L₂ hL₂ample
  refine ⟨m₂, fun d hd q hq => ?_⟩
  have hFqc := Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d
  have := modulePushforward_additive B S hS ρ'
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
  exact isZero_rightDerived_modulePushforward_of_isZero_chart B S hS ρ' hρrep hρp.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hρp.1) A hA hAsurj _
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨_, hFqc⟩).property q hq
    (isZero_rightDerived_evaluation_etaleModulePullback_of_isZero_hgroup B S hS W _ hFqc T₂
      q hq ((hm₂ d hd q hq).of_iso ((Hfunctor (chartScheme T₂).ringCatSheaf ⊤ q).mapIso
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso r₂ L d))))

/-- **The scheme-theoretic support of the direct image of a globally generated invertible
module along a proper surjection onto a reduced closed subspace.**  Let `Z ⊆ X` be a reduced closed
subspace of a locally Noetherian algebraic space, `ρ : W ⟶ Z` a proper surjective morphism from a
scheme of the site, and `𝓕` an invertible module on the scheme `W` generated by global sections.
Then the direct image `i_* ρ_* 𝓕ᵃ` to `X` of the module `𝓕ᵃ` associated with `𝓕` has
scheme-theoretic support `Z`.

`ρ_* 𝓕ᵃ` has support all of `|Z|`: an étale neighbourhood of a point of `Z` on which it vanished
would give a nonempty scheme over `W` on which the pullback of `𝓕` has no global sections, hence
vanishes (`AlgebraicGeometry.isZero_pullback_of_generatingSections`), which an invertible module
on a nonempty scheme does not.  As `Z` is reduced, a closed subspace containing its points
contains it (Stacks 03JJ). -/
theorem schemeTheoreticSupport_modulePushforward_representedGenerated
    {X : AlgebraicSpaces B S hS}
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z)
    (hZred : HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y))
    (hZN : HasEtaleLocalProperty B S hS Z.toFunctor (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (W : BigFppfOver B S hS) [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (ρ' : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶
      closedSubfunctorSpace B S hS hZ)
    (hρrep : yoneda.relativelyRepresentable ρ'.hom) (hρp : IsProper B S hS ρ'.hom)
    (hρs : IsSurjective B S hS ρ'.hom)
    (F : ((BigFppfOver.toScheme B S hS).obj W).Modules) (hFqc : SheafOfModules.IsQuasicoherent F)
    [hFinv : Stacks.Ample.IsInvertibleModule _ F] (σ : F.GeneratingSections) :
    schemeTheoreticSupport B S hS X ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
      ((modulePushforward B S hS ρ').obj
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨F, hFqc⟩).obj)) = Z := by
  let Ws : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let Zs := closedSubfunctorSpace B S hS hZ
  let i := closedSubfunctorι B S hS hZ
  have hip : IsProper B S hS i.hom := isProper_of_isClosedImmersion B S hS hZ.1 X.2 _ hZ.2
  let M := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨F, hFqc⟩).obj
  have hMqc : M.IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨F, hFqc⟩).property
  have hMcoh : IsCoherent B S hS Ws.1 Ws.2 M :=
    isCoherent_representedQuasicoherentSchemeEquivalence B S hS W F hFqc
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule F)
  let N := (modulePushforward B S hS ρ').obj M
  have hNcoh : IsCoherent B S hS Zs.1 Zs.2 N :=
    isCoherent_modulePushforward_of_isProper B S hS ρ' hρrep hρp hZN M hMcoh
  have hirep : yoneda.relativelyRepresentable i.hom := hZ.2.rep
  have hGcoh : IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj N) :=
    isCoherent_modulePushforward_of_isProper B S hS i hirep hip hXN N hNcoh
  have : SheafOfModules.IsCoherentOnSite ((modulePushforward B S hS i).obj N) :=
    hGcoh.toIsCoherentOnSite
  have hGft := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X
    ((modulePushforward B S hS i).obj N)
  have : SheafOfModules.IsCoherentOnSite N := hNcoh.toIsCoherentOnSite
  have hNft := isFiniteTypeOnSite_of_isCoherentOnSite B S hS Zs N
  obtain ⟨hZ', hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X _
    hGcoh.toIsQuasicoherentOnSite
    (Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ hGft)
  refine le_antisymm (schemeTheoreticSupport_le B S hS X _ ⟨Z, hZ⟩ N (Iso.refl _)) ?_
  -- Every point of `Z` lies in the support of `N = ρ_*(𝓛^{⊗ d})`.
  have hsuppN : supportOfSheaf B S hS Zs.1 ((SheafOfModules.toSheaf _).obj N) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => by_contra fun hz => ?_
    obtain ⟨W₀, ⟨b, hb⟩, hW₀⟩ :=
      exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf B S hS Zs hNft (𝟙 N) hz
    let T₀ := (smallBaseChange B S hS ρ' hρrep).obj W₀
    -- The base change `T₀` of `W` to the chart `W₀` has a point.
    obtain ⟨a, ha⟩ := hρs z
    obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS (hρrep.isPullback W₀.1.hom) a b
      (ha.trans hb.symm)
    have hpt : chartScheme T₀ := pointsToScheme B S hS (hρrep.pullback W₀.1.hom) w
    -- The sections of `N` over `W₀`, which are those of `M` over `T₀`, vanish.
    have hNW₀ : Subsingleton (N.val.obj (op W₀)) :=
      ModuleCat.isZero_iff_subsingleton.1 ((IsZero.iff_id_eq_zero _).2 (hW₀ W₀ (𝟙 W₀)))
    have hMT₀ : Subsingleton (M.val.obj (op T₀)) :=
      SheafOfModules.subsingleton_val_obj_of_iso
        ((modulePushforwardChartIso B S hS ρ' hρrep).app M).symm (op W₀)
    have : Subsingleton (M.val.presheaf.obj (op T₀)) := hMT₀
    have hMtop : Subsingleton (M.val.obj (op ((chartOpens B S hS T₀).obj ⊤))) :=
      (M.val.presheaf.mapIso (@asIso _ _ _ _ (chartOpensTopHom B S hS Ws T₀)
        (isIso_chartOpensTopHom B S hS Ws T₀)).op).addCommGroupIsoToAddEquiv.toEquiv.symm
          |>.subsingleton
    have hR : Subsingleton ((chartRestrictionSheaf B S hS Ws M T₀).val.obj (op ⊤)) :=
      (Equiv.ulift : ULift.{u} (M.val.obj (op ((chartOpens B S hS T₀).obj ⊤))) ≃ _).subsingleton
    have hR₁ : Subsingleton ((restrictToChartScheme B S hS Ws.1 Ws.2 M T₀).val.obj (op ⊤)) :=
      SheafOfModules.subsingleton_val_obj_of_iso
        ((restrictToChartIsoRestrictToChartScheme B S hS Ws.2 M T₀).symm ≪≫
          restrictToChartIsoChartRestrictionSheaf B S hS Ws M T₀) (op ⊤)
    -- Those are the global sections of the pullback of `𝓛^{⊗ d}` to the scheme of `T₀`.
    let r := chartSchemeMap ((isTerminalIdEtaleChart B S hS W).from T₀)
    obtain ⟨e₁⟩ := nonempty_chartZariskiPushforward_idEtaleChart_iso B S hS W F hFqc
    obtain ⟨e₂⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS Ws M hMqc
      ((isTerminalIdEtaleChart B S hS W).from T₀)
    have i₃ := (restrictToChartSchemeIsoChartComparisonPushforward B S hS Ws
      (idEtaleChart B S hS W) M) ≪≫ e₁
    have hR₂ : Subsingleton (((Scheme.Modules.pullback r).obj F).val.obj (op ⊤)) :=
      SheafOfModules.subsingleton_val_obj_of_iso
        ((Scheme.Modules.pullback r).mapIso i₃.symm ≪≫ e₂) (op ⊤)
    -- `F` is generated by global sections, so its pullback vanishes; it is invertible.
    have hzero := isZero_pullback_of_generatingSections r σ hR₂
    have : Stacks.Ample.IsInvertibleModule (chartScheme (idEtaleChart B S hS W)) F := hFinv
    exact (Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_of_isZero_of_isInvertible _ _
      (Stacks.InvertiblePullback.isInvertibleModule_pullback r F) hzero).false hpt
  have hrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) ⊆
      Set.range (pointsMap B S hS
        (schemeTheoreticSupport B S hS X ((modulePushforward B S hS i).obj N)).toFunctor
        (schemeTheoreticSupport B S hS X ((modulePushforward B S hS i).obj N)).ι) := by
    rw [← supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X _
        hGcoh.toIsQuasicoherentOnSite hGft,
      supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite B S hS i hZ.2 N, hsuppN,
      Set.image_univ]
    exact subset_rfl
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS X.2 Zs.2 _
    hZ' hZred Z.ι).2 hrange
  intro U x hx
  have hgx := congrArg (fun φ => φ.app U ⟨x, hx⟩) hg
  rw [← show (Z.ι.app U ⟨x, hx⟩ : X.1.obj U) = x from rfl, ← hgx]
  exact (g.app U ⟨x, hx⟩).2

/-- **The witness of the third condition of Stacks 08AN for finite cohomology along a proper
morphism to an affine Noetherian scheme.**  Let `f : X ⟶ yoneda.obj V` be proper, `V` affine and
Noetherian.  For every reduced closed subspace `Z ⊆ X` with irreducible space of points there is a
coherent `𝒪_X`-module with scheme-theoretic support `Z` all of whose cohomology modules along `f`
are finite.

This is the construction of the proof of Stacks 08AR. Chow's lemma over `V` (Stacks 089J) is
`AlgebraicGeometry.Space.exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine`
and gives a proper surjective `ρ : W ⟶ Z` from a scheme `W` which is H-quasi-projective over an
affine scheme, hence carries an ample invertible `𝓛`. For `d` large, Serre's vanishing theorem
(Stacks 02O1, in the form
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`) kills the higher
cohomology of `𝓛^{⊗ d}` on `W` and of its pullback to the base change of a surjective affine chart
of `Z`; the second gives `R^q ρ_*(𝓛^{⊗ d}) = 0` for `q > 0`
(`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_chart`). The witness is
`G = i_* ρ_*(𝓛^{⊗ d})`. Its cohomology along `f` is the cohomology of `𝓛^{⊗ d}` along
`W ⟶ yoneda.obj V`, by two Leray collapses (`i` is affine, Stacks 073H), which vanishes in positive
degree and is the finite module of global sections in degree zero (Stacks 02O6).

The scheme-theoretic support of `G` is `Z` because `ρ_*(𝓛^{⊗ d})` has support all of `|Z|`; taking
`d` also past the bound beyond which `𝓛^{⊗ d}` is globally generated (Stacks 01Q3, clause (7)),
an étale neighbourhood of a point of `Z` on which `ρ_*(𝓛^{⊗ d})` vanished would give a nonempty
scheme over `W` on which the pullback of `𝓛^{⊗ d}` has no global sections, hence vanishes
(`AlgebraicGeometry.isZero_pullback_of_generatingSections`), which an invertible module on a
nonempty scheme does not.  As `Z` is reduced, a closed subspace containing its points contains it
(Stacks 03JJ). -/
theorem hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) :
    HasCoherentWitnessOnIntegralSubspaces B S hS X (HasFiniteCohomologyOver B S hS V f) := by
  intro Z hZ hZirr
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Zs := closedSubfunctorSpace B S hS hZ
  let i := closedSubfunctorι B S hS hZ
  have hip : IsProper B S hS i.hom := isProper_of_isClosedImmersion B S hS hZ.1 X.2 _ hZ.2
  have hg : IsProper B S hS (i ≫ f).hom :=
    isProper_comp B S hS hZ.1 X.2 Y.2 i.hom f.hom hip hf
  obtain ⟨W, ρ, hρp, hρs, T, t, hT, htq⟩ :=
    exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine B S hS V hV Zs.2
      (i ≫ f).hom hg
  let Ws : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let ρ' : Ws ⟶ Zs := ObjectProperty.homMk ρ
  have hρrep : yoneda.relativelyRepresentable ρ'.hom :=
    Functor.relativelyRepresentable.of_diag Zs.2.diagonal_representable ρ
  -- The scheme `W` is proper over `V`, and carries an ample invertible module.
  have hT' : IsAffine T := hT
  obtain ⟨L, hLinv, hLample⟩ := exists_isAmple_of_isHQuasiProjective t htq
  let w : W ⟶ V := yoneda.preimage (ρ ≫ (i ≫ f).hom)
  have hρg := isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS W) Zs.2 Y.2 ρ (i ≫ f).hom hρp hg
  have hwp : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map w) := by
    refine isProper_toScheme_map_of_isProper_yoneda_map B S hS w ?_
    rw [Functor.map_preimage]
    exact hρg
  have hWln : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map w)
  -- A surjective affine Noetherian chart of `Z`, and the base change of `W` to it.
  have hXN := isNoetherian_of_isProper_toAffine B S hS V hV f hf
  have hZsN := isNoetherian_closedSubfunctor B S hS B.contains_terminal X hXN hZ
  -- The bounds of Serre's vanishing theorem on `W` and on the base change.
  obtain ⟨m₁, hm₁⟩ := Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
    _ _ ((BigFppfOver.toScheme B S hS).map w) hV inferInstance hwp L hLample
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj W) L := hLinv
  obtain ⟨m₂, hm₂⟩ :=
    exists_forall_isZero_rightDerived_modulePushforward_representedTensorPow B S hS V hV hZsN
      (i ≫ f).hom hg.1 W ρ' hρrep hρp L hLample
  -- and the bound of global generation of the twists of `𝒪_W`.
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L
    hLample (Stacks.Ample.unitModule _)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  let d : ℕ := max (max m₁ m₂) n₀.toNat
  have hd₁ : m₁ ≤ d := le_max_of_le_left (le_max_left _ _)
  have hd₂ : m₂ ≤ d := le_max_of_le_left (le_max_right _ _)
  have hd₀ : n₀ ≤ (d : ℤ) := (Int.self_le_toNat n₀).trans (by exact_mod_cast le_max_right _ _)
  let F := Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj W) L (d : ℤ)
  have hFinv : Stacks.Ample.IsInvertibleModule _ F :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ L d
  have hFqc : SheafOfModules.IsQuasicoherent F :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d
  let M := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨F, hFqc⟩).obj
  have hMcoh : IsCoherent B S hS Ws.1 Ws.2 M :=
    isCoherent_representedQuasicoherentSchemeEquivalence B S hS W F hFqc
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule F)
  -- The higher direct images of `M` along `ρ` vanish.
  have := modulePushforward_additive B S hS ρ'
  have hvan : ∀ q, 0 < q → IsZero (((modulePushforward B S hS ρ').rightDerived q).obj M) :=
    hm₂ d hd₂
  -- The witness `G = i_* ρ_* M`.
  let N := (modulePushforward B S hS ρ').obj M
  have hNcoh : IsCoherent B S hS Zs.1 Zs.2 N :=
    isCoherent_modulePushforward_of_isProper B S hS ρ' hρrep hρp hZsN.2.2 M hMcoh
  have hNqc : N.IsQuasicoherentOnSite := hNcoh.toIsQuasicoherentOnSite
  have hirep : yoneda.relativelyRepresentable i.hom := hZ.2.rep
  refine ⟨(modulePushforward B S hS i).obj N,
    isCoherent_modulePushforward_of_isProper B S hS i hirep hip hXN.2.2 N hNcoh, ?_, ?_⟩
  · obtain ⟨σ, -⟩ := hn₀ d hd₀
    have : Stacks.Ample.IsInvertibleModule _ F := hFinv
    exact schemeTheoreticSupport_modulePushforward_representedGenerated B S hS hXN.2.2 hZ hZirr.1
      hZsN.2.2 W ρ' hρrep hρp hρs F hFqc
      (SheafOfModules.GeneratingSections.equivOfIso
        (Stacks.AmpleGlobalGeneration.unitTensorIso L (d : ℤ)) σ)
  -- The cohomology of `G` along `f` is the cohomology of `M` along `W ⟶ V`.
  intro p
  have hterm := isTerminalIdEtaleChart B S hS V
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS (i ≫ f)
  have := modulePushforward_additive B S hS (ρ' ≫ (i ≫ f))
  have : (SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
    (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have e₁ := pushforwardEvaluationRightDerivedCompIso B S hS hterm i f N
    (fun q hq => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S
      hS i (isAffineHom_of_isClosedImmersion B S hS _ hZ.2) N hNqc q hq) p
  have e₂ := pushforwardEvaluationRightDerivedCompIso B S hS hterm ρ' (i ≫ f) M hvan p
  refine (Module.Finite.equiv_iff (e₂ ≪≫ e₁).toLinearEquiv).1 ?_
  have hhrep : yoneda.relativelyRepresentable (ρ' ≫ (i ≫ f)).hom :=
    Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable _
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h₀ := moduleFinite_modulePushforward_val_obj_of_isProper B S hS (ρ' ≫ (i ≫ f)) hhrep
      hρg (hasEtaleLocalProperty_of_representable B S hS _ _ V (Iso.refl _) inferInstance) M hMcoh
      (idEtaleChart B S hS V) hV
    have := hasInjectiveResolutions_modules B S hS Ws.1 Ws.2
    let E := SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))
    have : PreservesFiniteLimits E :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
    have : PreservesFiniteLimits (modulePushforward B S hS (ρ' ≫ (i ≫ f))) :=
      preservesFiniteLimits_modulePushforward B S hS (ρ' ≫ (i ≫ f))
    refine (Module.Finite.equiv_iff
      ((Functor.rightDerivedZeroIsoSelf (modulePushforward B S hS (ρ' ≫ (i ≫ f)) ⋙ E)).app
        M).symm.toLinearEquiv).1 ?_
    exact h₀
  · have hz := isZero_rightDerived_pushforwardEvaluation_of_isZero_rightDerived_evaluation B S hS
      hterm (ρ' ≫ (i ≫ f)) (isTerminalIdEtaleChart B S hS W) M p
      (isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup B S hS W F hFqc p hp
        (hm₁ d hd₁ p hp))
    have := ModuleCat.isZero_iff_subsingleton.1 hz
    infer_instance

end AlgebraicGeometry.Space

end
