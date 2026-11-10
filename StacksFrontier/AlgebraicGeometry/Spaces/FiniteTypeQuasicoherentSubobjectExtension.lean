module

public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.CategoryTheory.Abelian.GraphKernelAdjunction

/-!
# Extending a finite type quasi-coherent submodule from a quasi-compact open of a space

Let `X` be a quasi-compact and quasi-separated algebraic space, `U ⊂ X` a quasi-compact open,
`ℱ` a quasi-coherent `𝒪_X`-module and `𝒢 ⊂ ℱ|_U` a quasi-coherent `𝒪_U`-submodule of finite
type.  Stacks 0853 asserts that `𝒢` is the restriction of a quasi-coherent submodule of `ℱ`
of finite type.  This file proves that, by the source's argument.

An open subspace is an open immersion `j : U ⟶ X` of algebraic spaces, a submodule is a
`CategoryTheory.Subobject` of a sheaf of modules on the small étale site, and restriction is
`AlgebraicGeometry.Space.etaleModulePullback`.  That the extension restricts to `𝒢` is recorded
as an isomorphism of the restricted submodule with `𝒢` commuting with the two inclusions into
`ℱ|_U`, which says that the two subobjects of `ℱ|_U` are equal.

## Main results

* `AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension`: **Stacks 0853**.

## Implementation notes

The construction is the source's.  Writing `j : U ⟶ X` for the open immersion, the module
`ℋ = Ker(ℱ ⊞ j_*𝒢 ⟶ j_*(ℱ|_U))` — the difference of the unit of Stacks 03LU and the direct
image of the inclusion of `𝒢` — is a submodule of `ℱ` restricting to `𝒢` on `U`.  Both of those
statements are formal consequences of the adjunction of Stacks 03LU together with invertibility
of its counit along an open immersion, and are proved for an abstract adjunction of abelian
categories in `StacksFrontier.CategoryTheory.Abelian.GraphKernelAdjunction`; what is used here is
`Stacks.GraphKernel.graphKernelPullbackIso_hom_comp`, that under the identification of `ℋ|_U`
with `𝒢` the restricted projection is the inclusion of `𝒢`, and
`Stacks.GraphKernel.graphKernelProjection_mono`, that the projection `ℋ ⟶ ℱ` is injective.
Invertibility of the counit is
`AlgebraicGeometry.Space.fullyFaithfulModulePushforwardOfIsOpenImmersion`.

Quasi-coherence of `ℋ` needs quasi-coherence of the two direct images `j_*𝒢` and `j_*(ℱ|_U)`,
which is Stacks 03M9 for `j`: the morphism `j` is quasi-compact because `X` is quasi-separated
and `U` is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`), and quasi-separated because
it is a monomorphism (`AlgebraicGeometry.Space.isQuasiSeparated_of_mono`); Stacks 03M9 is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`.  Quasi-coherence of
`ℋ` follows: it is closed under direct sums (`SheafOfModules.IsQuasicoherentOnSite.biprod`) and
under kernels (`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`).

The passage from `ℋ` to a submodule of finite type is the second half of the source's proof:
`ℋ` is the filtered colimit of its finite type quasi-coherent submodules (Stacks 0829), that
colimit is preserved by restriction to `U`, and `ℋ|_U = 𝒢` is of finite type over a
quasi-compact space, so one stage of the restricted colimit is already everything —
`AlgebraicGeometry.Space.exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace`, the analogue
for algebraic spaces of the second assertion of Stacks 01BB.  That stage is the required
submodule, and because the projection `ℋ ⟶ ℱ` is injective it is a submodule of `ℱ` on the
nose, so the source's final passage to the image of `ℋ' ⟶ ℱ` is not needed.  The colimit
assertion of Stacks 0829 is
`AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9`, fed with
Stacks 07V9 for `X`, `AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite`.

Importing Stacks 03M9 brings the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` into scope, which leaves universe
arguments of `IsGrothendieckAbelian` undetermined where the proof asks for the Grothendieck
abelian structure of the module categories; it is removed locally in this file, and that
structure is built by hand at the universe of the schemes.

Two universe constraints shape the statement.  The module universe is the universe `u` of the
schemes, which is where `AlgebraicGeometry.Space.modulePushforward` and
`SheafOfModules.IsFiniteType` live.  The diagram of finite type quasi-coherent submodules of
`ℋ` is indexed by a category whose objects form a `Type (u + 1)`, while the stage lemma asks for
an index category in `Type u`; the two are reconciled by
`CategoryTheory.equivSmallModel`, the diagram being essentially small because the modules on an
algebraic space form a Grothendieck abelian category at `u` and are therefore well-powered
there.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {U X : AlgebraicSpaces B S hS}

/- The global instance `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`, imported with
Stacks 03M9, leaves the universe arguments of `IsGrothendieckAbelian` undetermined where the
proof below asks for the Grothendieck abelian structure of the module categories; that structure
is built by hand there at the universe of the schemes instead. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- The abelian structure on modules over an algebraic space, at the universe of the schemes. -/
private abbrev modulesAbelian (Y : AlgebraicSpaces B S hS) :
    Abelian (Modules.{u, u} B S hS Y.1 Y.2) :=
  SheafOfModules.instAbelian.{u, u, u, u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- Modules over an algebraic space form a Grothendieck abelian category at the universe of the
schemes. -/
private theorem isGrothendieckAbelian_modules (Y : AlgebraicSpaces B S hS) :
    letI := modulesAbelian B S hS Y
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Y.1 Y.2) := by
  let := modulesAbelian B S hS Y
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS Y.1 Y.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS Y.1)
    infer_instance
  exact SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- Étale restriction of modules preserves all colimits indexed in the universe of the
structure rings.  This is the unrestricted form of
`AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback`: small étale
postcomposition is both continuous and cocontinuous, so restriction of modules along it
preserves every `u`-small colimit. -/
theorem preservesColimitsOfSize_etaleModulePullback (h : U ⟶ X)
    (hh : IsEtale B S hS h.hom) :
    PreservesColimitsOfSize.{u, u} (etaleModulePullback.{u, u} B S hS h hh) :=
  Stacks.SheafOfModules.pushforward_preservesColimits.{u + 1, u, u, u + 1, u, u}
    (J := SmallEtale.topology B S hS U.1) (K := SmallEtale.topology B S hS X.1)
    (R := structureRingSheaf B S hS X)
    (smallEtalePostcomp B S hS h hh) (𝟙 (structureRingSheaf B S hS U))

/-- **Stacks Project, Tag 0853.** Let `X` be a quasi-compact and quasi-separated algebraic
space, `U ⊂ X` a quasi-compact open, `ℱ` a quasi-coherent `𝒪_X`-module and `𝒢 ⊂ ℱ|_U` a
quasi-coherent `𝒪_U`-submodule of finite type.  Then there is a quasi-coherent submodule
`𝒢' ⊂ ℱ` of finite type with `𝒢'|_U = 𝒢`, the equality being an isomorphism of `𝒢'|_U` with
`𝒢` commuting with the inclusions into `ℱ|_U`. -/
@[stacks 0853 "submodules as subobjects, restriction to the open as étale module pullback"]
theorem exists_finiteTypeQuasicoherentSubobject_extension (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (G : Subobject ((etaleModulePullback.{u, u} B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).obj F))
    [(G : Modules.{u, u} B S hS U.1 U.2).IsQuasicoherentOnSite]
    [(G : Modules.{u, u} B S hS U.1 U.2).IsFiniteType] :
    ∃ G' : Subobject F, (G' : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite ∧
      (G' : Modules.{u, u} B S hS X.1 X.2).IsFiniteType ∧
      ∃ e : (etaleModulePullback.{u, u} B S hS j
            (isEtale_of_isOpenImmersion B S hS hj)).obj
          (G' : Modules.{u, u} B S hS X.1 X.2) ≅ (G : Modules.{u, u} B S hS U.1 U.2),
        (etaleModulePullback.{u, u} B S hS j
            (isEtale_of_isOpenImmersion B S hS hj)).map G'.arrow = e.hom ≫ G.arrow := by
  classical
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  -- the abelian structure of the two module categories, at the universe of the schemes
  let := modulesAbelian B S hS X
  have := isGrothendieckAbelian_modules B S hS X
  let := modulesAbelian B S hS U
  have := isGrothendieckAbelian_modules B S hS U
  -- restriction along `j` is additive and exact, direct image along `j` is fully faithful
  have hLadd : (etaleModulePullback.{u, u} B S hS j hje).Additive :=
    etaleModulePullback_additive B S hS j hje
  have hLlim : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS j hje) :=
    preservesFiniteLimits_etaleModulePullback B S hS j hje
  have hLcos : PreservesLimitsOfShape WalkingCospan
      (etaleModulePullback.{u, u} B S hS j hje) :=
    hLlim.preservesFiniteLimits WalkingCospan
  have hLcol : PreservesColimitsOfSize.{u, u} (etaleModulePullback.{u, u} B S hS j hje) :=
    preservesColimitsOfSize_etaleModulePullback B S hS j hje
  have hff := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj
  have hRfull : (modulePushforward B S hS j).Full := hff.full
  have hRfaith : (modulePushforward B S hS j).Faithful := hff.faithful
  -- `j` is quasi-compact and quasi-separated
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs hUqc j.hom
  have hjqs : IsQuasiSeparated B S hS j.hom :=
    isQuasiSeparated_of_mono B S hS j.hom (mono_of_presheaf_isOpenImmersion hj)
  -- the graph kernel of the inclusion of `𝒢`
  set adj := etaleModulePullbackAdjunction B S hS j hje with hadj
  have hGmono : Mono G.arrow := inferInstance
  set H : Modules.{u, u} B S hS X.1 X.2 :=
    Stacks.GraphKernel.graphKernel adj F G.arrow with hH
  set p : H ⟶ F := Stacks.GraphKernel.graphKernelProjection adj F G.arrow with hp
  have hpmono : Mono p := Stacks.GraphKernel.graphKernelProjection_mono adj F G.arrow
  set e₀ : (etaleModulePullback.{u, u} B S hS j hje).obj H ≅
      (G : Modules.{u, u} B S hS U.1 U.2) :=
    Stacks.GraphKernel.graphKernelPullbackIso adj F G.arrow with he₀def
  have he₀ : e₀.hom ≫ G.arrow = (etaleModulePullback.{u, u} B S hS j hje).map p :=
    Stacks.GraphKernel.graphKernelPullbackIso_hom_comp adj F G.arrow
  -- `ℋ` is quasi-coherent
  have hRG : ((modulePushforward B S hS j).obj
      (G : Modules.{u, u} B S hS U.1 U.2)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs _ inferInstance
  have hLF : (((etaleModulePullback.{u, u} B S hS j hje).obj F)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS j hje F inferInstance
  have hRLF : ((modulePushforward B S hS j).obj
      ((etaleModulePullback.{u, u} B S hS j hje).obj F)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs _ hLF
  have hsum : (F ⊞ (modulePushforward B S hS j).obj
      (G : Modules.{u, u} B S hS U.1 U.2)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.biprod
      (fun M _ _ a h => Stacks.SheafOfModules.hasGlobalPresentation_overMap M a h)
      inferInstance hRG
  have hHq : H.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_quasicoherent B S hS X.1 X.2
      (Stacks.GraphKernel.graphKernelMap adj F G.arrow)
  -- Stacks 0829 for `ℋ`
  have hcol : IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 H) :=
    isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9 B S hS X.1 X.2 hZ hXqc hXqs
      (fun hqc hqs M hM =>
        exists_isFilteredColimit_isFinitePresentationOnSite B S hS hZ X.2 hqc hqs M hM) H
  have hfil : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS X.1 X.2 H
  -- reindex the diagram by a small model of its index category
  have hsmall : Small.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H) :=
    small_of_injective (f := fun T => T.obj)
      (fun a b h => by cases a; cases b; subst h; rfl)
  have hess : EssentiallySmall.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H) :=
    inferInstance
  set eqv := (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)).symm
    with heqv
  have hfil' : IsFiltered (SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)) :=
    IsFiltered.of_equivalence
      (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H))
  set D' := eqv.functor ⋙ finiteTypeQuasicoherentSubobjectFunctor B S hS X.1 X.2 H with hD'
  set c' := (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 H).whisker eqv.functor
    with hc'
  have hc'col : IsColimit c' := hcol.whiskerEquivalence eqv
  -- the legs of the cocone are the subobject inclusions, hence monomorphisms
  have hιmono : ∀ i, Mono (c'.ι.app i) := by
    intro i
    change Mono (eqv.functor.obj i).obj.arrow
    infer_instance
  have hDmono : ∀ {i i' : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)}
      (f : i ⟶ i'), Mono (D'.map f) := by
    intro i i' f
    have := hιmono i
    exact mono_of_mono_fac (c'.w f)
  have hLDmono : ∀ {i i' : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)}
      (f : i ⟶ i'), Mono ((D' ⋙ etaleModulePullback.{u, u} B S hS j hje).map f) := by
    intro i i' f
    have := hDmono f
    exact preserves_mono_of_preservesLimit (etaleModulePullback.{u, u} B S hS j hje) (D'.map f)
  -- the restricted colimit is `𝒢`, which is of finite type over the quasi-compact `U`
  have hLHft : ((etaleModulePullback.{u, u} B S hS j hje).obj H).IsFiniteType :=
    haveI : Epi e₀.inv := IsIso.epi_of_iso _
    Stacks.SheafOfModules.isFiniteType_of_epi e₀.inv inferInstance
  obtain ⟨i, hi⟩ := exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace B S hS hUqc
    (D' ⋙ etaleModulePullback.{u, u} B S hS j hje)
    ((etaleModulePullback.{u, u} B S hS j hje).mapCocone c')
    (isColimitOfPreserves (etaleModulePullback.{u, u} B S hS j hje) hc'col) hLDmono hLHft
  -- that stage, included into `ℱ`, is the required submodule
  have hιm : Mono (c'.ι.app i) := hιmono i
  have hcomp : Mono (c'.ι.app i ≫ p) :=
    ⟨fun {_} a b hab => hιm.right_cancellation a b
      (hpmono.right_cancellation _ _
        ((Category.assoc a (c'.ι.app i) p).trans
          (hab.trans (Category.assoc b (c'.ι.app i) p).symm)))⟩
  have hiso : IsIso ((etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i)) := hi
  have hKq : (D'.obj i).IsQuasicoherentOnSite := (eqv.functor.obj i).property.1
  have hKf : (D'.obj i).IsFiniteType := (eqv.functor.obj i).property.2
  refine ⟨Subobject.mk (c'.ι.app i ≫ p), ?_, ?_, ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (Subobject.underlyingIso (c'.ι.app i ≫ p)).symm hKq
  · have : Epi (Subobject.underlyingIso (c'.ι.app i ≫ p)).inv := IsIso.epi_of_iso _
    exact Stacks.SheafOfModules.isFiniteType_of_epi
      (Subobject.underlyingIso (c'.ι.app i ≫ p)).inv hKf
  · refine ⟨(etaleModulePullback.{u, u} B S hS j hje).mapIso
      (Subobject.underlyingIso (c'.ι.app i ≫ p)) ≪≫
      asIso ((etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i)) ≪≫ e₀, ?_⟩
    rw [(Iso.inv_comp_eq _).1 (Subobject.underlyingIso_arrow (c'.ι.app i ≫ p))]
    have hmapcomp : ∀ {M N P : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) (g : N ⟶ P),
        (etaleModulePullback.{u, u} B S hS j hje).map (f ≫ g) =
          (etaleModulePullback.{u, u} B S hS j hje).map f ≫
            (etaleModulePullback.{u, u} B S hS j hje).map g :=
      fun f g => Functor.map_comp _ f g
    rw [hmapcomp, hmapcomp (c'.ι.app i) p]
    exact (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) he₀.symm)).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Space

end
