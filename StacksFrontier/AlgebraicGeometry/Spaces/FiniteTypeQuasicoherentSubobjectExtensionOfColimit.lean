module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGluing

/-!
# Extending a finite type quasi-coherent submodule, from the colimit clause of Stacks 0829

`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjectExtension.lean` proves the
extension statement of Stacks 0853 over Stacks 07V9, which it uses only to obtain the colimit
clause of Stacks 0829 for one quasi-coherent module.  This file runs the same argument from that
colimit clause directly, for the ambient space at hand, so that it applies wherever the colimit
clause is known — in particular on an affine algebraic space, where it is the theorem
`Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace` of the
namespace `AlgebraicGeometry`.

The quasi-coherence of the two direct images along the open immersion, which is Stacks 03M9, is
taken as the hypothesis `hpush` here and discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjectExtensionAffine.lean`: the
file proving Stacks 03M9 cannot be imported where the Grothendieck abelian structures of this
proof are built by hand (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjectExtensionOver07V9.lean`).

## Main results

* `AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension_of_isColimit`: the
  extension, from the colimit clause of Stacks 0829 for the ambient space.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U X : AlgebraicSpaces B S hS}

/-- **Extension of a finite type quasi-coherent submodule from an open subspace, from the colimit
clause of Stacks 0829.**  The argument of
`AlgebraicGeometry.Space.exists_finiteTypeQuasicoherentSubobject_extension`, with the colimit
clause of Stacks 0829 for the ambient space and the quasi-coherence of direct images along the
open immersion as inputs, in place of the quasi-compactness and quasi-separatedness of the
ambient space. -/
theorem exists_finiteTypeQuasicoherentSubobject_extension_of_isColimit (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom)
    (hpush : ∀ M : Modules.{u, u} B S hS U.1 U.2, M.IsQuasicoherentOnSite →
      ((modulePushforward B S hS j).obj M).IsQuasicoherentOnSite)
    (hcol : ∀ H : Modules.{u, u} B S hS X.1 X.2, H.IsQuasicoherentOnSite →
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 H)))
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
  have hesX : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  let habX : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have hgrX : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hesU : EssentiallySmall.{u} (smallEtaleRingedSite B S hS U.1 U.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS U.1)
    infer_instance
  let habU : Abelian (Modules.{u, u} B S hS U.1 U.2) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O))
  have hgrU : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS U.1 U.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
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
    hpush _ inferInstance
  have hLF : (((etaleModulePullback.{u, u} B S hS j hje).obj F)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS j hje F inferInstance
  have hRLF : ((modulePushforward B S hS j).obj
      ((etaleModulePullback.{u, u} B S hS j hje).obj F)).IsQuasicoherentOnSite :=
    hpush _ hLF
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
    (hcol H hHq).some
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
  · exact Stacks.SheafOfModules.isFiniteType_of_epi
      (Subobject.underlyingIso (c'.ι.app i ≫ p)).inv hKf
  · refine ⟨(etaleModulePullback.{u, u} B S hS j hje).mapIso
      (Subobject.underlyingIso (c'.ι.app i ≫ p)) ≪≫
      asIso ((etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i)) ≪≫ e₀, ?_⟩
    have harrow : (Subobject.mk (c'.ι.app i ≫ p)).arrow =
        (Subobject.underlyingIso (c'.ι.app i ≫ p)).hom ≫ (c'.ι.app i ≫ p) :=
      (Iso.hom_inv_id_assoc (Subobject.underlyingIso _) (Subobject.mk _).arrow).symm.trans
        (congrArg (fun g => (Subobject.underlyingIso _).hom ≫ g)
          (Subobject.underlyingIso_arrow _))
    have hmapcomp : ∀ {M N P : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) (g : N ⟶ P),
        (etaleModulePullback.{u, u} B S hS j hje).map (f ≫ g) =
          (etaleModulePullback.{u, u} B S hS j hje).map f ≫
            (etaleModulePullback.{u, u} B S hS j hje).map g :=
      fun f g => Functor.map_comp _ f g
    have h1 := hmapcomp (Subobject.underlyingIso (c'.ι.app i ≫ p)).hom (c'.ι.app i ≫ p)
    have h2 := hmapcomp (c'.ι.app i) p
    rw [harrow, h1, h2]
    have hA := Category.assoc
      ((etaleModulePullback.{u, u} B S hS j hje).map
        (Subobject.underlyingIso (c'.ι.app i ≫ p)).hom)
      ((etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i) ≫ e₀.hom) G.arrow
    have hB := Category.assoc
      ((etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i)) e₀.hom G.arrow
    exact (hA.trans (congrArg
      (fun g => (etaleModulePullback.{u, u} B S hS j hje).map
        (Subobject.underlyingIso (c'.ι.app i ≫ p)).hom ≫ g)
      (hB.trans (congrArg
        (fun g => (etaleModulePullback.{u, u} B S hS j hje).map (c'.ι.app i) ≫ g) he₀)))).symm

/-- **Restriction of the image of a monomorphism.**  For an étale `g : Y ⟶ X` and a
monomorphism `m : A ⟶ M`, if the restriction of `m` to `Y` is, up to an isomorphism, the
inclusion of a submodule `𝒢 ⊆ M|_Y`, then the restriction of the image of `m` is `𝒢`. -/
theorem etaleSubmoduleRestrict_monoRange {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) {M A : Modules.{u, u} B S hS X.1 X.2} (m : A ⟶ M) (hm : Mono m)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    (e : (etaleModulePullback.{u, u} B S hS g hg).obj A ≅ G.toSheafOfModules)
    (he : (etaleModulePullback.{u, u} B S hS g hg).map m = e.hom ≫ G.ι) :
    etaleSubmoduleRestrict B S hS g hg (Stacks.SheafOfModules.monoRange m hm) = G := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  ext s
  have hval : ∀ a, m.val.app (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) a =
      (G.ι.val.app V) (e.hom.val.app V a) := fun a =>
    congrArg (fun k => k.val.app V a) he
  constructor
  · rintro ⟨a, rfl⟩
    exact (congrArg (· ∈ G.obj V) (hval a)).mpr (e.hom.val.app V a).2
  · intro hs
    refine ⟨e.inv.val.app V ⟨s, hs⟩, ?_⟩
    have h₁ : e.hom.val.app V (e.inv.val.app V ⟨s, hs⟩) = ⟨s, hs⟩ :=
      congrArg (fun k => k.val.app V ⟨s, hs⟩) e.inv_hom_id
    exact (hval _).trans (congrArg (G.ι.val.app V) h₁)

/-- **Extension of a finite type quasi-coherent submodule from an open subspace, from the colimit
clause of Stacks 0829**, for sheaf submodules: a quasi-coherent submodule `𝒢 ⊆ ℱ|_U` of finite
type is the restriction of a quasi-coherent submodule of `ℱ` of finite type. -/
theorem exists_etaleSubmodule_extension_of_isColimit (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom)
    (hpush : ∀ M : Modules.{u, u} B S hS U.1 U.2, M.IsQuasicoherentOnSite →
      ((modulePushforward B S hS j).obj M).IsQuasicoherentOnSite)
    (hcol : ∀ H : Modules.{u, u} B S hS X.1 X.2, H.IsQuasicoherentOnSite →
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 H)))
    (hUqc : IsQuasiCompactSpace B S hS U.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (G : ((etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj
      F).Submodule)
    (hGq : G.toSheafOfModules.IsQuasicoherentOnSite) (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧
      etaleSubmoduleRestrict B S hS j (isEtale_of_isOpenImmersion B S hS hj) K = G := by
  classical
  let G₀ : Subobject ((etaleModulePullback.{u, u} B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).obj F) := Subobject.mk G.ι
  let eG := Subobject.underlyingIso G.ι
  have : (G₀ : Modules.{u, u} B S hS U.1 U.2).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso eG.symm hGq
  have : (G₀ : Modules.{u, u} B S hS U.1 U.2).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi eG.inv hGf
  have : F.IsQuasicoherentOnSite := hF
  obtain ⟨G', hG'q, hG'f, e, he⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension_of_isColimit B S hS j hj hpush hcol hUqc
      F G₀
  refine ⟨Stacks.SheafOfModules.monoRange G'.arrow inferInstance, ?_, ?_, ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (Stacks.SheafOfModules.monoRangeIso G'.arrow inferInstance) hG'q
  · exact Stacks.SheafOfModules.isFiniteType_of_epi
      (Stacks.SheafOfModules.monoRangeIso G'.arrow inferInstance).hom hG'f
  · refine etaleSubmoduleRestrict_monoRange B S hS j _ G'.arrow inferInstance G
      (e ≪≫ eG) ?_
    rw [he, Iso.trans_hom, Category.assoc]
    congr 1
    exact (Subobject.underlyingIso_hom_comp_eq_mk G.ι).symm

end AlgebraicGeometry.Space

end
