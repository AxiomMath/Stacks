module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.RingTheory.Nilpotent.Descent
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
import all StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# Locally Noetherian formal algebraic spaces with a reduction of finite type are limit preserving

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`, and let `W` be a locally
Noetherian formal algebraic space over `S` whose reduction `W_red` is locally of finite type over
`S`. Then `W`, as a functor on the big fppf site of `S`, is limit preserving.

## Main results

* `Algebra.FiniteType.of_quotient_of_fg_of_le_nilradical`: an algebra is of finite type as soon
  as its quotient by a finitely generated nil ideal is.
* `AlgebraicGeometry.locallyOfFiniteType_of_nilradical_subschemeι_comp`: a morphism out of a
  locally Noetherian scheme is locally of finite type as soon as its restriction to the reduction
  is.
* `AlgebraicGeometry.FormalSpace.limitPreserving_of_isLocallyNoetherian_of_isReduction`: a
  locally Noetherian formal algebraic space whose reduction is locally of finite type over a
  locally Noetherian base is limit preserving.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 0G8U](https://stacks.math.columbia.edu/tag/0G8U)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Finite type modulo a finitely generated nil ideal -/

/-- An algebra whose quotient by a finitely generated nil ideal is of finite type is of finite
type. -/
theorem Algebra.FiniteType.of_quotient_of_fg_of_le_nilradical {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {K : Ideal A} (hfg : K.FG) (hK : K ≤ nilradical A)
    [Algebra.FiniteType R (A ⧸ K)] : Algebra.FiniteType R A := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  let C : Subalgebra R A := Algebra.adjoin R (s : Set A)
  let gen : s → C := fun x ↦ ⟨x, Algebra.subset_adjoin x.2⟩
  let I : Ideal C := Ideal.span (Set.range gen)
  have hImap : I.map (algebraMap C A) = Ideal.span (s : Set A) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range]
    exact ⟨by rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact y.2, fun hx ↦ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩⟩
  have hInil : IsNilpotent I := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical
      (show I.FG from Submodule.fg_span (Set.finite_range gen))).mpr ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    refine mem_nilradical.mpr ((IsNilpotent.map_iff (f := C.val) Subtype.val_injective).mp ?_)
    exact mem_nilradical.mp (hK (Ideal.subset_span x.2))
  have hRq : Algebra.FiniteType R (A ⧸ I.map (algebraMap C A)) := by
    rw [hImap]
    infer_instance
  have : IsScalarTower R (C ⧸ I) (A ⧸ I.map (algebraMap C A)) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hCq : Algebra.FiniteType (C ⧸ I) (A ⧸ I.map (algebraMap C A)) :=
    hRq.of_restrictScalars_finiteType R (C ⧸ I) (A ⧸ I.map (algebraMap C A))
  have hCA : Algebra.FiniteType C A := finiteType_of_isNilpotent_quotient_finiteType C I A hInil hCq
  have hRC : Algebra.FiniteType R C :=
    (Subalgebra.fg_iff_finiteType C).mp (Subalgebra.fg_adjoin_finset s)
  exact hRC.trans hCA

/-- If `ψ : A → T` is surjective with finitely generated kernel consisting of nilpotent elements
and `ψ ∘ φ` is of finite type, then `φ` is of finite type. -/
theorem RingHom.FiniteType.of_comp_of_surjective_of_ker_le_nilradical {R A T : Type*}
    [CommRing R] [CommRing A] [CommRing T] (φ : R →+* A) (ψ : A →+* T)
    (hψ : Function.Surjective ψ) (hfg : (RingHom.ker ψ).FG)
    (hnil : RingHom.ker ψ ≤ nilradical A) (h : (ψ.comp φ).FiniteType) : φ.FiniteType := by
  let := φ.toAlgebra
  let e : (A ⧸ RingHom.ker ψ) ≃+* T := RingHom.quotientKerEquivOfSurjective hψ
  have heq : algebraMap R (A ⧸ RingHom.ker ψ) =
      (e.symm : T →+* A ⧸ RingHom.ker ψ).comp (ψ.comp φ) := by
    ext r
    apply e.injective
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hψ (φ r)).trans (by simp)
  have hq : (algebraMap R (A ⧸ RingHom.ker ψ)).FiniteType := by
    rw [heq]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective) h
  have : Algebra.FiniteType R (A ⧸ RingHom.ker ψ) := RingHom.finiteType_algebraMap.mp hq
  exact RingHom.finiteType_algebraMap.mpr
    (Algebra.FiniteType.of_quotient_of_fg_of_le_nilradical hfg hnil)

namespace AlgebraicGeometry

/-- A morphism out of a locally Noetherian scheme is locally of finite type as soon as its
restriction to the reduction is. -/
theorem locallyOfFiniteType_of_nilradical_subschemeι_comp {X Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsLocallyNoetherian X] (f : X ⟶ Y)
    (h : LocallyOfFiniteType (X.nilradical.subschemeι ≫ f)) : LocallyOfFiniteType f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)] at h ⊢
  intro U V e
  let i := X.nilradical.subschemeι
  have hV' : IsAffineOpen (i ⁻¹ᵁ V.1) := V.2.preimage i
  have key := Scheme.Hom.appLE_comp_appLE i f U V (i ⁻¹ᵁ V.1) e le_rfl
  have hc := h U ⟨_, hV'⟩ ((TopologicalSpace.Opens.map i.base).monotone e)
  rw [← key, ← Scheme.Hom.app_eq_appLE, CommRingCat.hom_comp] at hc
  have hnoeth : IsNoetherianRing Γ(X, V.1) :=
    _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian V
  exact RingHom.FiniteType.of_comp_of_surjective_of_ker_le_nilradical _ _
    (X.nilradical.subschemeι_app_surjective V) (IsNoetherian.noetherian _)
    (X.nilradical.ker_subschemeι_app V).le hc

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The reduction of a stage -/

/-- For a directed presentation of `X` by affine thickenings, the composite of the inclusion of
the reduction of the `i`-th stage with the stage map to `X` exhibits it as a reduction of `X` in
the sense of `AlgebraicGeometry.FormalSpace.IsReduction`. -/
theorem isReduction_siteReduction_stage {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : FppfSheaf B S hS)
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X) (i : I) :
    IsReduction B S hS X
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (siteReduction B S hS ((BigAffineFppf.inclusion B S hS).obj (D.obj i))))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (siteReductionMap B S hS ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda JT
  let _ : F.Full := Sheaf.sheafifiedYoneda_full JT
  let _ : F.Faithful := Sheaf.sheafifiedYoneda_faithful JT
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, Sheaf.sheafifiedYoneda]
    infer_instance
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let _ : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  have hstage : MorphismProperty.relative F P
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.hom) :=
    isThickening_colimitι B S hS D hD X e i
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  have hr : MorphismProperty.relative F P
      (F.map (siteReductionMap B S hS T₀) ≫
        (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.hom)) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS T₀)) hstage
  have hrU : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (F.map (siteReductionMap B S hS T₀) ≫
        (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.hom)).hom :=
    relative_uliftYoneda_of_sheafifiedYoneda B S hS P hr
  let ε : F ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  have hatlas : (uliftYoneda.{u + 1}).obj Tred ≅ (F.obj Tred).obj := (ε.app Tred).symm
  refine isReduction_of_isRepresentableThickening B S hS _ ?_ ?_ hrU
  · exact Space.isAlgebraicSpaceULift_of_iso B S hS hatlas
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS Tred)
  · refine ⟨Tred, hatlas.hom, ?_, ?_, isReduced_toScheme_obj_siteReduction B S hS T₀⟩ <;>
      exact hasSchemePropertyULift_of_isoSource B S hS _
        (fun _ _ f hf ↦ by have := hf; infer_instance) hatlas

/-! ### Finitely presented stages of a weak-ideal presentation -/

/-- Let `X` be presented as the colimit of the spectra `Spec(A/J)` of the quotients of a weakly
admissible topological ring `A` by its weak ideals of definition, each locally of finite
presentation over `S`. Then `X` has finitely presented stages in the sense of
`AlgebraicGeometry.FormalSpace.HasFinitelyPresentedStages`. -/
theorem hasFinitelyPresentedStages_of_weakIdealColimitPresentation {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X)
    (hfp : ∀ J : WeakIdeals A, LocallyOfFinitePresentation
      (B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J)).hom)) :
    HasFinitelyPresentedStages B S hS X := by
  classical
  have : Nonempty (WeakIdeals A) := weakIdeals_nonempty A hA
  have : IsDirected (WeakIdeals A) (· ≤ ·) := weakIdeals_directed A
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
    Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
    Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)
  have hm : ∀ {a b : WeakIdeals A} (h : a ≤ b),
      (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (homOfLE h) ≫
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) b ≫ P.colimitIso.inv =
      colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) a ≫ P.colimitIso.inv :=
    fun h ↦ colimit.w_assoc _ (homOfLE h) _
  intro T hT t₁ t₂
  obtain ⟨i₁, g₁, hg₁⟩ := exists_factor_from_affine_stage B S hS (WeakIdeals A) P.diagram
    (fun _ _ f ↦ weak_quotient_transition_closed_immersion B S hS A X P f) X P.colimitIso T hT
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm t₁)
  obtain ⟨i₂, g₂, hg₂⟩ := exists_factor_from_affine_stage B S hS (WeakIdeals A) P.diagram
    (fun _ _ f ↦ weak_quotient_transition_closed_immersion B S hS A X P f) X P.colimitIso T hT
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm t₂)
  obtain ⟨k, h₁, h₂⟩ := directed_of (· ≤ ·) i₁ i₂
  have hmono : Mono (colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ P.colimitIso.inv) := by
    have := weak_quotient_colimit_injection_mono B S hS A X P k
    exact mono_comp _ _
  refine ⟨(BigAffineFppf.inclusion B S hS).obj (P.diagram.obj k),
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ P.colimitIso.inv),
    hfp k, ?_,
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage
      (g₁ ≫ (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (homOfLE h₁)),
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage
      (g₂ ≫ (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (homOfLE h₂)), ?_, ?_⟩
  · intro T' a b _ hab
    apply (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
    rw [← cancel_mono (colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ P.colimitIso.inv)]
    apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
    rwa [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_map_comp]
  · rw [← Sheaf.sectionEquiv_map_comp, Functor.map_preimage, Category.assoc, hm, hg₁,
      Equiv.apply_symm_apply]
  · rw [← Sheaf.sectionEquiv_map_comp, Functor.map_preimage, Category.assoc, hm, hg₂,
      Equiv.apply_symm_apply]

/-! ### Stages over a reduction of finite type -/

/-- Let `f : U ⟶ W` be a morphism of formal algebraic spaces over `S`, representable by algebraic
spaces and étale, let `W_red ⟶ W` be a reduction of `W` whose structure morphism is locally of
finite type, and let the sheaf of an object `Z` of the site be a reduction of `U`. Then `Z` is
locally of finite type over `S`. -/
theorem locallyOfFiniteType_hom_of_isReduction_of_isEtale {W Wred U : FppfSheaf B S hS}
    (hW : IsFormalAlgebraicSpace B S hS W) {iW : Wred ⟶ W}
    (hred : IsReduction B S hS W Wred iW)
    (hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj))
    (hU : IsFormalAlgebraicSpace B S hS U) (f : U ⟶ W)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep)
    (Z : BigFppfOver B S hS)
    {r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶ U}
    (hZ : IsReduction B S hS U _ r) :
    LocallyOfFiniteType (B.inclusion.map Z.hom) := by
  let JT := BigFppfOver.topology B S hS
  let : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  have sq : IsPullback (pullback.fst f iW) (pullback.snd f iW) f iW :=
    IsPullback.of_hasPullback f iW
  have hsmooth : Space.HasPropertyULift.{u + 1} B S hS
      (Space.smoothPropertyULift.{u + 1} B S hS) f.hom hrep := fun V ξ ↦
    holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      (fun k hk ↦ by have : Etale k := hk; infer_instance) _ (het V ξ)
  have hR := isReduction_pullback_reduction_of_smooth B S hS hU hW hrep hsmooth hred sq
  obtain ⟨g, hg, -⟩ := hR.universal _ hZ.algebraic hZ.reduced r
  have hgiso : IsIso g := IsReduction.isIso_of_comp_eq B S hS hZ hR hg
  have hgh : IsIso g.hom := (inferInstance : IsIso ((sheafToPresheaf JT (Type (u + 1))).map g))
  have sqh : IsPullback (pullback.fst f iW).hom (pullback.snd f iW).hom f.hom iW.hom :=
    sq.map (sheafToPresheaf JT (Type (u + 1)))
  have hrep' := Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ sqh hrep
  have hsndP := hasPropertyULift_isEtaleULift_of_isPullback B S hS _ _ _ _ sqh hrep hrep' het
  obtain ⟨V, q, hqS, hqE⟩ := hred.algebraic.exists_atlas
  have hsnd : Space.IsEtaleULift.{u + 1} B S hS (pullback.snd f iW).hom :=
    isEtaleULift_of_targetChart B S hS hred.algebraic _ V q hqS hqE (hsndP V q)
  let ε : Sheaf.sheafifiedYoneda JT ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  have ha := isEtaleULift_precomp_iso B S hS ((ε.app Z).symm ≪≫ asIso g.hom) _ hsnd
  have harel := (Space.isEtaleULift_iff_relative_etale B S hS _).1 ha
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hterm : IsTerminal ((uliftYoneda.{u + 1}).obj T₀) :=
    IsTerminal.isTerminalObj (uliftYoneda.{u + 1}) T₀ Over.mkIdTerminal
  have : IsIso (terminal.from ((uliftYoneda.{u + 1}).obj T₀)) :=
    isIso_of_isTerminal hterm terminalIsTerminal _
  have hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
        (terminal.from ((uliftYoneda.{u + 1}).obj T₀)) := by
    simpa using MorphismProperty.RespectsIso.postcomp _
      (terminal.from ((uliftYoneda.{u + 1}).obj T₀)) _ (Space.relative_id_etale B S hS T₀)
  have key := hlft Z T₀ _ _ (Over.mkIdTerminal.from Z) harel hb (terminal.hom_ext _ _)
  have hmap : (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from Z) =
      B.inclusion.map Z.hom :=
    congrArg B.inclusion.map (show (Over.mkIdTerminal.from Z : Z ⟶ T₀).left = Z.hom by simp)
  rwa [hmap] at key

/-- Let `S` be locally Noetherian, let `f : U ⟶ W` be an étale chart of a formal algebraic space
`W` whose reduction is locally of finite type over `S`, and let `U` be presented by the quotients
`A/J` of a Noetherian weakly admissible ring `A`. Then every stage `Spec(A/J)` is locally of
finite presentation over `S`. -/
theorem locallyOfFinitePresentation_stage_of_isReduction
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] {W Wred U : FppfSheaf B S hS}
    (hW : IsFormalAlgebraicSpace B S hS W) {iW : Wred ⟶ W}
    (hred : IsReduction B S hS W Wred iW)
    (hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj))
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (f : U ⟶ W)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (P : WeakIdealColimitPresentation B S hS A U) (J : WeakIdeals A) :
    LocallyOfFinitePresentation
      (B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J)).hom) := by
  have hne : Nonempty (WeakIdeals A) := weakIdeals_nonempty A hA
  have hdir : IsDirected (WeakIdeals A) (· ≤ ·) := weakIdeals_directed A
  have : Nonempty (ULift.{u + 1} (WeakIdeals A)) := ⟨ULift.up hne.some⟩
  have : IsDirected (ULift.{u + 1} (WeakIdeals A)) (· ≤ ·) := by
    refine ⟨fun i j ↦ ?_⟩
    obtain ⟨k, hik, hjk⟩ := hdir.directed i.down j.down
    exact ⟨ULift.up k, hik, hjk⟩
  let D' := (weakIdealsULiftEquivalence A).functor ⋙ P.diagram
  have hD' : ∀ ⦃i j : ULift.{u + 1} (WeakIdeals A)⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D'.map g)) :=
    fun _ _ g ↦ weak_quotient_transition_isThickening B S hS A U P _
  let e' : colimit (D' ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ U :=
    HasColimit.isoOfEquivalence (weakIdealsULiftEquivalence A) (Iso.refl _) ≪≫ P.colimitIso.symm
  have hZ := isReduction_siteReduction_stage B S hS D' hD' U e' (ULift.up J)
  let Z : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J)
  have hlftZ := locallyOfFiniteType_hom_of_isReduction_of_isEtale B S hS hW hred hlft
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU) f hrep het
    (siteReduction B S hS Z) hZ
  have hcomp : B.inclusion.map (siteReduction B S hS Z).hom =
      ((BigFppfOver.toScheme B S hS).obj Z).nilradical.subschemeι ≫ B.inclusion.map Z.hom := by
    simp only [siteReduction, Over.mk_hom, Functor.map_comp, siteReductionHom,
      Functor.map_preimage]
  rw [hcomp] at hlftZ
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (B.inclusion.obj Z.left) :=
    isLocallyNoetherian_of_isOpenImmersion (P.quotientIso J).hom
  have : LocallyOfFiniteType (B.inclusion.map Z.hom) :=
    locallyOfFiniteType_of_nilradical_subschemeι_comp _ hlftZ
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    ‹_root_.AlgebraicGeometry.IsLocallyNoetherian S›
  infer_instance

/-! ### Limit preservation -/

/-- Let `S` be locally Noetherian, let `W` be a locally Noetherian formal algebraic space over `S`
and let `W_red ⟶ W` be a reduction of `W` which is locally of finite type over `S`. Then `W` is
limit preserving. -/
theorem limitPreserving_of_isLocallyNoetherian_of_isReduction
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] {W Wred : FppfSheaf B S hS}
    (hW : IsLocallyNoetherian B S hS W) {iW : Wred ⟶ W} (hred : IsReduction B S hS W Wred iW)
    (hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj)) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) W.obj := by
  obtain ⟨K, U, f, haff, het, hsurj, hNoeth⟩ := hW.2
  refine limitPreserving_of_atlas B S hS U f haff het hsurj fun k ↦ ?_
  obtain ⟨-, A, _, _, _, _, ⟨hA, ⟨P⟩⟩, _, -⟩ := hNoeth k
  obtain ⟨hrep, hetk⟩ := het k
  exact hasFinitelyPresentedStages_of_weakIdealColimitPresentation B S hS hA P
    (locallyOfFinitePresentation_stage_of_isReduction B S hS hW.1 hred hlft (haff k) (f k) hrep
      hetk hA P)

end FormalSpace

end AlgebraicGeometry

end
