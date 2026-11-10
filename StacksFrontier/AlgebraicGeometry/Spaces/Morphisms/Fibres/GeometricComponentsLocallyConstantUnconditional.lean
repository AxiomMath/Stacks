module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01
public import StacksFrontier.AlgebraicGeometry.Quot.H0FibreRankSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsLowerSemicontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
import StacksCore.Tactic.StacksAttribute

/-!
# Local constancy of the number of geometric connected components of the fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is proper, flat and
of finite presentation, with geometrically reduced fibres. Stacks 0E1E: the function
`n_{X/Y} : |Y| → ℤ` counting the geometric connected components of the fibres (Stacks 0E1B,
`AlgebraicGeometry.Space.numberGeometricConnectedComponents`) is locally constant.

The source's proof: `n_{X/Y}` is lower semicontinuous (Stacks 0E1D); the question is étale local
on `Y`, so `Y` may be taken to be a scheme, where `n_{X/Y}(y) = dim_{κ(y)} H⁰(X_y, 𝒪)` because the
fibres are geometrically reduced (Stacks 0DMY), and `y ↦ dim_{κ(y)} H⁰(X_y, 𝒪)` is upper
semicontinuous (Stacks 0E0R).

The reduction to the two semicontinuity statements on étale charts is
`AlgebraicGeometry.Space.isLocallyConstant_numberGeometricConnectedComponents_of`. This file
supplies its chart input. On an étale chart `U` of `Y`, with `f_U : X_U ⟶ U` the base change,
Stacks 0E0R at `i = 0` is `AlgebraicGeometry.Space.exists_upperSemicontinuous_h0FibreRank`: one
upper semicontinuous function `b` on `U` whose value at the image of a field-valued point
`Spec k ⟶ U` is `dim_k H⁰(X_k, 𝒪)`. At a geometric point `Spec k ⟶ U` over `v`, Stacks 0DMY
(`AlgebraicGeometry.Space.numberGeometricConnectedComponents_class_eq_finrank`) gives
`n_{X_U/U}(v) = dim_k H⁰(X_k, 𝒪)`, the global functions being those of the fibre
formed over the field;
`AlgebraicGeometry.Space.h0FibreRank_eq_toENat_rank_globalFunctions_fibreOverFieldValuedPoint`
compares them with those of the fibre product `X_U ×_U Spec k`, in which `b` is stated.

## Main results

* `AlgebraicGeometry.Space.h0FibreRank_eq_toENat_rank_globalFunctions_fibreOverFieldValuedPoint`:
  `dim_k H⁰(X_k, 𝒪)` read on the fibre product over the site of `S` is the dimension of the
  global functions of the fibre formed over the site of `Spec k`.
* `AlgebraicGeometry.Space.isLocallyConstant_numberGeometricConnectedComponents`: Stacks 0E1E.

## References

* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0E1D](https://stacks.math.columbia.edu/tag/0E1D)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The global functions of the fibre over a field-valued point, on both sites -/

section FibreRank

/-- **Pulling back a constant along the structure map of a lower-shriek extension.** Let `p` be a
field-valued point with field `k` and `F` a presheaf over `Spec k` whose lower-shriek extension
`Λ F` to `S` is an algebraic space. Pulling the constant `c ∈ k` back along `Λ F ⟶ Spec k` and
reading the result on `F` (`AlgebraicGeometry.Space.globalFunctionsRelocalizeEquiv`) gives the
constant `c` of the `k`-algebra of global functions of `F`. -/
theorem globalFunctionsRelocalizeEquiv_globalFunctionsMap_relocalizeToYoneda
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS Y)
    (F : (BigFppfOver B (Spec (.of p.carrier)) p.contained)ᵒᵖ ⥤ Type u)
    (hΛ : IsAlgebraicSpace B S hS
      ((OverShriek.relocalizePresheafFunctor (p.siteObject B S hS Y).hom).obj F))
    (c : p.carrier) :
    globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS
        (p.siteObject B S hS Y).hom F
        (globalFunctionsMap B S hS
          (ObjectProperty.homMk (OverShriek.relocalizeToYoneda (p.siteObject B S hS Y).hom F) :
            (⟨_, hΛ⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace (p.siteObject B S hS Y))
          ((globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm
            ((Scheme.ΓSpecIso (.of p.carrier)).inv c))) =
      algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained F) c := by
  let a := (p.siteObject B S hS Y).hom
  let Λ' : AlgebraicSpaces B S hS := ⟨_, hΛ⟩
  let rTY : Λ' ⟶ schemeSpace (p.siteObject B S hS Y) :=
    ObjectProperty.homMk (OverShriek.relocalizeToYoneda a F)
  let ι : globalFunctions' B S hS (yoneda.obj (p.siteObject B S hS Y)) :=
    (globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm
      ((Scheme.ΓSpecIso (.of p.carrier)).inv c)
  refine Subtype.ext (funext fun V => ?_)
  rw [globalFunctionsRelocalizeEquiv_apply]
  let ψ := relocalizeOverHom B (Spec (.of p.carrier)) S p.contained hS a
    ((SmallEtale.toOver B (Spec (.of p.carrier)) p.contained F).obj V.unop)
  have hψ : yoneda.map ψ ≫ ((SmallEtale.inclusion B S hS (yoneda.obj (p.siteObject B S hS Y))).obj
      (idEtaleChart B S hS (p.siteObject B S hS Y))).hom =
      ((SmallEtale.inclusion B S hS Λ'.obj).obj
        ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
          F).functor.obj V.unop)).hom ≫ rTY.hom := by
    ext W x
    exact Over.OverMorphism.ext rfl
  refine (globalFunctionsMap_val_chart B S hS rTY (idEtaleChart B S hS _)
    ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
      F).functor.obj V.unop) ψ hψ ι).trans ?_
  have hc : ι.val (op (idEtaleChart B S hS (p.siteObject B S hS Y))) =
      (Scheme.ΓSpecIso (.of p.carrier)).inv c :=
    (globalFunctionsYonedaRingEquiv_apply B S hS _ ι).symm.trans
      ((globalFunctionsYonedaRingEquiv B S hS _).apply_symm_apply _)
  exact (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom hc).trans rfl

variable {U : BigFppfOver B S hS} {P : AlgebraicSpaces B S hS} (g : P ⟶ schemeSpace U)
  (p : FieldValuedPoint B S hS (yoneda.obj U))

/-- **`dim_k H⁰(X_k, 𝒪)` on the two sites.** For `g : P ⟶ U` and a field-valued point
`Spec k ⟶ U`, the dimension over `k` of the global functions of the fibre product
`P ×_U Spec k` over the site of `S` (`AlgebraicGeometry.Space.h0FibreRank`) is the dimension of
the global functions of the fibre of `g` formed over the site of `Spec k`. -/
theorem h0FibreRank_eq_toENat_rank_globalFunctions_fibreOverFieldValuedPoint :
    h0FibreRank B S hS g p = Cardinal.toENat (Module.rank p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS g.hom p))) := by
  let F := fiberOverField B S hS g.hom p
  let β : yoneda.obj (p.siteObject B S hS _) ⟶ yoneda.obj U := yonedaEquiv.symm p.value
  have hQ : IsAlgebraicSpace B S hS (pullback g.hom β) :=
    isAlgebraicSpace_pullback B S hS g.hom β P.2 (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS U)
  let Q : AlgebraicSpaces B S hS := ⟨_, hQ⟩
  let E := extendFiberOverFieldIso B S hS g.hom p
  have hΛ : IsAlgebraicSpace B S hS
      ((OverShriek.relocalizePresheafFunctor (p.siteObject B S hS _).hom).obj F) :=
    isAlgebraicSpace_of_iso B S hS E.symm hQ
  let Λ : AlgebraicSpaces B S hS := ⟨_, hΛ⟩
  let I : Λ ≅ Q := (ObjectProperty.fullyFaithfulι _).preimageIso E
  let snd : Q ⟶ schemeSpace (p.siteObject B S hS _) := ObjectProperty.homMk (pullback.snd g.hom β)
  have hI : I.hom ≫ snd =
      ObjectProperty.homMk (OverShriek.relocalizeToYoneda (p.siteObject B S hS _).hom F) :=
    ObjectProperty.hom_ext _ (extendFiberOverFieldIso_hom_snd B S hS g.hom p)
  have hw : β = (schemeSpaceMap p.value).hom := by
    rw [schemeSpaceMap_hom, Equiv.symm_apply_eq]
    exact (yonedaEquiv_yoneda_map _).symm
  let J : h0Fibre B S hS g p ≅ Q :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (pullback.congrHom rfl hw.symm)
  have hJ : J.hom ≫ snd = h0FibreProj B S hS g p := by
    refine ObjectProperty.hom_ext _ ?_
    change (pullback.congrHom rfl hw.symm).hom ≫ pullback.snd g.hom β =
      pullback.snd g.hom (schemeSpaceMap p.value).hom
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let σ : globalFunctions' B S hS (h0Fibre B S hS g p).obj ≃+*
      globalFunctions B (Spec (.of p.carrier)) p.contained F :=
    ((globalFunctionsMapEquiv B S hS J).symm.trans (globalFunctionsMapEquiv B S hS I)).trans
      (globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS
        (p.siteObject B S hS _).hom F)
  have hσ : σ.toRingHom.comp (h0FibreAlgebraMap B S hS g p) =
      baseToGlobalFunctions p.carrier B p.contained F := by
    refine RingHom.ext fun c => ?_
    let ι : globalFunctions' B S hS (schemeSpace (p.siteObject B S hS _)).obj :=
      (globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS _)).symm
        ((Scheme.ΓSpecIso (.of p.carrier)).inv c)
    have h1 : (globalFunctionsMapEquiv B S hS J).symm
        (globalFunctionsMap B S hS (h0FibreProj B S hS g p) ι) =
          globalFunctionsMap B S hS snd ι := by
      rw [RingEquiv.symm_apply_eq, ← hJ, globalFunctionsMap_comp]
      rfl
    change globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS
        (p.siteObject B S hS _).hom F (globalFunctionsMap B S hS I.hom
          ((globalFunctionsMapEquiv B S hS J).symm
            (globalFunctionsMap B S hS (h0FibreProj B S hS g p) ι))) = _
    rw [h1, ← RingHom.comp_apply, ← globalFunctionsMap_comp, hI]
    exact globalFunctionsRelocalizeEquiv_globalFunctionsMap_relocalizeToYoneda B S hS p F hΛ c
  unfold h0FibreRank
  rw [← toENat_rank_comp_ringEquiv (h0FibreAlgebraMap B S hS g p) σ, hσ]
  rfl

end FibreRank

/-! ### Stacks 0E1E -/

section LocallyConstant

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0E1E.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is proper,
flat and of finite presentation, and whose geometric fibres are reduced. Then the function
`n_{X/Y} : |Y| → ℕ∞` counting the geometric connected components of the fibres of `f`
(Stacks 0E1B) is locally constant. -/
@[stacks 0E1E]
theorem isLocallyConstant_numberGeometricConnectedComponents
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsProper B S hS f) (hfl : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f)
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS f hX hY y) :
    IsLocallyConstant (numberGeometricConnectedComponents B S hS f) := by
  refine isLocallyConstant_numberGeometricConnectedComponents_of B S hS hX hY f hf hfl hfp hred
    fun V => ?_
  let W := V.obj.left
  have hW := isAlgebraicSpace_yoneda B S hS W
  let fA : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  let tA : schemeSpace W ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk V.obj.hom
  let P := AlgebraicSpaces.fiberProduct B S hS fA tA
  let g : P ⟶ schemeSpace W := ObjectProperty.homMk (pullback.snd f V.obj.hom)
  have hg : IsProper B S hS g.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS fA tA) hf
  obtain ⟨hgfl, hgfp⟩ :=
    isFlat_and_isFinitePresentation_pullback_snd hX hY f hfl hfp V.obj.hom
  obtain ⟨b, hb, hbq⟩ := exists_upperSemicontinuous_h0FibreRank g hg hgfl hgfp
  let e := schemePointsHomeomorph B S hS W
  have hval : ∀ v, numberGeometricConnectedComponents B S hS (pullback.snd f V.obj.hom)
      (e.symm v) = b v ∧ b v ≠ ⊤ := by
    intro v
    obtain ⟨q, hq⟩ := exists_geometricRepresentative B S hS (yoneda.obj W) (e.symm v)
    have : IsAlgClosed q.val.carrier := q.property
    have hredq : HasEtaleLocalProperty B (Spec (.of q.val.carrier)) q.val.contained
        (fibreOverFieldValuedPoint B S hS g.hom q.val)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T) := by
      have hw : IsGeometricallyReducedFibreAt B S hS (pullback.snd f V.obj.hom) P.2 hW
          q.image := by
        change q.image ∈ geometricallyReducedFibreLocus B S hS _ _ _
        rw [geometricallyReducedFibreLocus_pullback B S hS f V.obj.hom hX hY hW]
        exact hred _
      exact (isGeometricallyReducedFibreAt_iff_forall_isReduced B S hS _ P.2 hW q.image).1 hw
        q.val rfl
    have hz := isProper_toYonedaId_fibreOverFieldValuedPoint B S hS g.hom P.2 hW hg q.val
    have := module_finite_globalFunctions_of_isProper B q.val.carrier q.val.contained
      ⟨_, isAlgebraicSpace_fibreOverFieldValuedPoint B S hS g.hom P.2 hW q.val⟩ _ hz hredq
    have hr := h0FibreRank_eq_toENat_rank_globalFunctions_fibreOverFieldValuedPoint B S hS g q.val
    rw [← Module.finrank_eq_rank, Cardinal.toENat_nat] at hr
    have hv : schemePoint B S hS W q.val = v := by
      rw [← pointsToScheme_class B S hS W q.val]
      change e q.image = v
      rw [hq, e.apply_symm_apply]
    rw [← hv, ← hbq q.val, hr]
    refine ⟨?_, ENat.natCast_ne_top _⟩
    rw [hv, ← hq]
    exact numberGeometricConnectedComponents_class_eq_finrank B S hS P.2 hW g.hom q.val _ hz hredq
  refine ⟨fun v => (b v).toNat, ?_, fun v => ?_⟩
  · intro v n hn
    have hbv : b v < n := by
      rw [← ENat.natCast_toNat (hval v).2]
      exact_mod_cast hn
    filter_upwards [hb v n hbv] with v' hv'
    have hv'' : b v' < n := hv'
    rw [← ENat.natCast_toNat (hval v').2] at hv''
    exact_mod_cast hv''
  · rw [(hval v).1, ENat.natCast_toNat (hval v).2]

end LocallyConstant

end AlgebraicGeometry.Space

end
