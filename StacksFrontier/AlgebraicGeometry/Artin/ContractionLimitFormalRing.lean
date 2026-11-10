module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFiniteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickening
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalChart

/-!
# The ring map of a morphism from an algebraic space to a formal spectrum

Let `B` be a weakly admissible topological ring and `X` a quasi-compact algebraic space. A
morphism `X ⟶ Spf B` factors through a quotient stage `Spec (B ⧸ J)` (Stacks 0AIA), and pulling
functions back along `X ⟶ Spec (B ⧸ J)` gives a ring map `B ⟶ B ⧸ J ⟶ Γ(X, 𝒪_X)`. It does not
depend on the stage, and it determines the morphism.

## Main definitions

* `AlgebraicGeometry.Artin.FormalRing.formalRingHom`: the ring map `B ⟶ Γ(X, 𝒪_X)` of a morphism
  `X ⟶ Spf B` from a quasi-compact algebraic space.

## Main results

* `AlgebraicGeometry.Artin.FormalRing.formalRingHom_eq`: its value on a morphism factoring through
  a given stage.
* `AlgebraicGeometry.Artin.FormalRing.formalRingHom_injective`: a morphism is determined by its
  ring map.
* `AlgebraicGeometry.Artin.FormalRing.formalRingHom_comp`: naturality in `X`.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  (DB : QuotientSystem B S hS Bt)

/-- The quotient stage `Spec (B ⧸ J)` of a formal spectrum, as an object of the site. -/
abbrev stageObj (J : WeakIdeals Bt) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (DB.diagram.obj J)

/-- The ring map `B ⟶ B ⧸ J ≅ Γ(Spec (B ⧸ J), 𝒪)` of a quotient stage. -/
def stageRingHom (J : WeakIdeals Bt) :
    Bt →+* Γ((BigFppfOver.toScheme B S hS).obj (stageObj DB J), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Bt ⧸ (OrderDual.ofDual J).1))).inv.hom.comp
    (Ideal.Quotient.mk _)

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- The stage ring maps are compatible with the transition morphisms of the stages. -/
theorem appTop_map_comp_stageRingHom {J K : WeakIdeals Bt} (f : J ⟶ K) :
    (((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (DB.diagram.map f))).appTop.hom).comp
        (stageRingHom DB K) = stageRingHom DB J := by
  ext b
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f)))).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ b)) =
    (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ b)
  exact (congrArg (fun φ => φ.hom (Ideal.Quotient.mk _ b))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f))))).symm

include hB in
/-- **Stacks 0AIA for a formal spectrum**: a morphism from (the sheafified universe lift of) a
quasi-compact presheaf into `Spf B` factors through a quotient stage. -/
theorem exists_stage_factor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsQuasiCompactSpace B S hS X)
    (f : sheafifiedULift B S hS X ⟶ formalSpectrum DB) :
    ∃ (J : WeakIdeals Bt) (m : sheafifiedULift B S hS X ⟶ (formalSpectrumDiagram DB).obj J),
      m ≫ formalSpectrumInclusion DB J = f := by
  have : Nonempty (WeakIdeals Bt) := ⟨OrderDual.toDual ⟨hB.1.choose, hB.1.choose_spec⟩⟩
  have : IsDirected (WeakIdeals Bt) (· ≤ ·) := ⟨fun J K ↦ ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 K.2.1⟩,
    show J.1 ⊓ K.1 ≤ J.1 from inf_le_left, show J.1 ⊓ K.1 ≤ K.1 from inf_le_right⟩⟩
  let ι : sheafifiedULift B S hS X ≅
      (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (X ⋙ uliftFunctor.{u + 1}) :=
    (plusPlusSheafIsoPresheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).app
      (X ⋙ uliftFunctor.{u + 1})
  obtain ⟨J, m, hm⟩ := exists_factor_through_thickening' B S hS (WeakIdeals Bt) DB.diagram
    (fun _ _ g => (DB.isThickening_map_diagram g).1) (formalSpectrum DB) (Iso.refl _) X hX
    (ι.inv ≫ f)
  have hm' : m ≫ formalSpectrumInclusion DB J = ι.inv ≫ f :=
    (congrArg (m ≫ ·) (Category.comp_id _).symm).trans hm
  exact ⟨J, ι.hom ≫ m,
    (Category.assoc _ _ _).trans ((congrArg (ι.hom ≫ ·) hm').trans (ι.hom_inv_id_assoc f))⟩

/-- A morphism of sheaves `sheafifiedULift X ⟶ sheafifiedULift Y` between sheafified universe
lifts of fppf sheaves of `Type u` comes from a unique morphism `X ⟶ Y`. -/
theorem existsUnique_sheafifiedULiftMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (m : sheafifiedULift B S hS X ⟶ sheafifiedULift B S hS Y) :
    ∃! t : X ⟶ Y, sheafifiedULiftMap B S hS t = m := by
  let H := uliftWhiskeringFullyFaithful B S hS
  let m' : X ⋙ uliftFunctor.{u + 1} ⟶ Y ⋙ uliftFunctor.{u + 1} :=
    (sheafifiedULiftIso B S hS X hX).hom ≫ m.hom ≫ (sheafifiedULiftIso B S hS Y hY).inv
  have key : ∀ t : X ⟶ Y, sheafifiedULiftMap B S hS t = m ↔ H.preimage m' = t := by
    intro t
    constructor
    · rintro rfl
      apply H.map_injective
      rw [H.map_preimage]
      change (sheafifiedULiftIso B S hS X hX).hom ≫ (sheafifiedULiftMap B S hS t).hom ≫
        (sheafifiedULiftIso B S hS Y hY).inv = Functor.whiskerRight t uliftFunctor.{u + 1}
      rw [← Category.assoc, ← whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX hY t,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rintro rfl
      apply ObjectProperty.hom_ext
      have h1 : Functor.whiskerRight (H.preimage m') uliftFunctor.{u + 1} = m' := H.map_preimage m'
      have h2 := whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX hY (H.preimage m')
      rw [h1] at h2
      rw [← cancel_epi (sheafifiedULiftIso B S hS X hX).hom, ← h2]
      simp [m']
  exact ⟨H.preimage m', (key _).2 rfl, fun t ht => ((key t).1 ht).symm⟩

/-- The identification `sheafifiedULift (yoneda V) ≅ sheafifiedYoneda V` is natural in `V`. -/
@[reassoc]
theorem sheafifiedULiftMap_yoneda_comp_iso {V V' : BigFppfOver B S hS} (g : V ⟶ V') :
    sheafifiedULiftMap B S hS (yoneda.map g) ≫ (sheafifiedULiftIsoYoneda V').hom =
      (sheafifiedULiftIsoYoneda V).hom ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g :=
  (plusPlusSheafIsoPresheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).hom.naturality
    (Functor.whiskerRight (yoneda.map g) uliftFunctor.{u + 1})

/-- `sheafifiedULiftMap` preserves composition. -/
theorem sheafifiedULiftMap_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    sheafifiedULiftMap B S hS (f ≫ g) =
      sheafifiedULiftMap B S hS f ≫ sheafifiedULiftMap B S hS g := by
  rw [sheafifiedULiftMap_eq_map, sheafifiedULiftMap_eq_map, sheafifiedULiftMap_eq_map,
    Functor.whiskerRight_comp, Functor.map_comp]
  rfl

/-- A quotient stage `Spec (B ⧸ J)` is an affine scheme. -/
instance isAffine_stageObj (J : WeakIdeals Bt) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (stageObj DB J)) :=
  inferInstanceAs (IsAffine (Spec (.of (Bt ⧸ (OrderDual.ofDual J).1))))

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- The stage ring map `B ⟶ Γ(Spec (B ⧸ J), 𝒪)` is surjective. -/
theorem stageRingHom_surjective (J : WeakIdeals Bt) : Function.Surjective (stageRingHom DB J) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Bt ⧸ (OrderDual.ofDual J).1))).commRingCatIsoToRingEquiv.symm
    |>.surjective.comp Ideal.Quotient.mk_surjective

/-- The transition morphism `Spec (B ⧸ J) ⟶ Spec (B ⧸ K)` of the stages, as a morphism of the
site. -/
def stageMap {J K : WeakIdeals Bt} (u : J ⟶ K) : stageObj DB J ⟶ stageObj DB K :=
  (BigAffineFppf.inclusion B S hS).map (DB.diagram.map u)

/-- The inclusion of a quotient stage into the formal spectrum. -/
def stageIncl (J : WeakIdeals Bt) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (stageObj DB J) ⟶
      formalSpectrum DB :=
  formalSpectrumInclusion DB J

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- The inclusions of the stages into `Spf B` commute with the transition morphisms. -/
theorem stageIncl_w {J K : WeakIdeals Bt} (u : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (stageMap DB u) ≫
      stageIncl DB K = stageIncl DB J :=
  colimit.w (formalSpectrumDiagram DB) u

include hB in
/-- For weakly admissible `B`, the inclusion of a quotient stage into `Spf B` is a monomorphism. -/
theorem mono_stageIncl (J : WeakIdeals Bt) : Mono (stageIncl DB J) :=
  mono_formalSpectrumInclusion_of_isWeaklyAdmissible hB DB J

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- The stage ring maps are compatible with the transition morphisms `stageMap`. -/
theorem appTop_stageMap_comp_stageRingHom {J K : WeakIdeals Bt} (u : J ⟶ K) :
    (((BigFppfOver.toScheme B S hS).map (stageMap DB u)).appTop.hom).comp
      (stageRingHom DB K) = stageRingHom DB J :=
  appTop_map_comp_stageRingHom DB u

include hB in
/-- A morphism from the sheafified universe lift of a quasi-compact presheaf into `Spf B` factors
through the inclusion `stageIncl` of a quotient stage. -/
theorem exists_stage_factor' (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsQuasiCompactSpace B S hS X)
    (f : sheafifiedULift B S hS X ⟶ formalSpectrum DB) :
    ∃ (J : WeakIdeals Bt) (m : sheafifiedULift B S hS X ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (stageObj DB J)),
      m ≫ stageIncl DB J = f :=
  exists_stage_factor hB DB X hX f

variable {DB} (X : AlgebraicSpaces B S hS)

/-- `t : X ⟶ Spec (B ⧸ J)` is a factorization of `f : X ⟶ Spf B` through the stage `J`. -/
def IsStageFactor (f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB) (J : WeakIdeals Bt)
    (t : X.1 ⟶ yoneda.obj (stageObj DB J)) : Prop :=
  sheafifiedULiftMap B S hS t ≫ (sheafifiedULiftIsoYoneda (stageObj DB J)).hom ≫
    stageIncl DB J = f

include hB in
/-- A morphism from a quasi-compact algebraic space `X` into `Spf B` has a factorization
`X ⟶ Spec (B ⧸ J)` through some quotient stage. -/
theorem exists_isStageFactor (hX : IsQuasiCompactSpace B S hS X.1)
    (f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB) :
    ∃ (J : WeakIdeals Bt) (t : X.1 ⟶ yoneda.obj (stageObj DB J)), IsStageFactor X f J t := by
  obtain ⟨J, m, hm⟩ := exists_stage_factor' hB DB X.1 hX f
  obtain ⟨t, ht, -⟩ := existsUnique_sheafifiedULiftMap X.2.isSheaf
    (isAlgebraicSpace_yoneda B S hS (stageObj DB J)).isSheaf
    (m ≫ (sheafifiedULiftIsoYoneda (stageObj DB J)).inv)
  refine ⟨J, t, ?_⟩
  rwa [IsStageFactor, ht, Category.assoc, Iso.inv_hom_id_assoc]

/-- The common refinement `J ⊓ K` of two stages. -/
def stageInf (J K : WeakIdeals Bt) : WeakIdeals Bt :=
  OrderDual.toDual ⟨(OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right (OrderDual.ofDual J).2
      (OrderDual.ofDual K).2.1⟩

/-- The morphism `Spec (B ⧸ J) ⟶ Spec (B ⧸ J ⊓ K)`. -/
def stageInfLeft (J K : WeakIdeals Bt) : J ⟶ stageInf J K :=
  homOfLE (show (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual J).1 from
    inf_le_left)

/-- The morphism `Spec (B ⧸ K) ⟶ Spec (B ⧸ J ⊓ K)`. -/
def stageInfRight (J K : WeakIdeals Bt) : K ⟶ stageInf J K :=
  homOfLE (show (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual K).1 from
    inf_le_right)

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- Composing a stage factorization through `J` with the transition morphism to a stage `K` gives a
stage factorization through `K`. -/
theorem isStageFactor_comp {f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB}
    {J K : WeakIdeals Bt} {t : X.1 ⟶ yoneda.obj (stageObj DB J)} (h : IsStageFactor X f J t)
    (u : J ⟶ K) : IsStageFactor X f K (t ≫ yoneda.map (stageMap DB u)) := by
  unfold IsStageFactor at h ⊢
  rw [sheafifiedULiftMap_comp, Category.assoc, sheafifiedULiftMap_yoneda_comp_iso_assoc,
    stageIncl_w]
  exact h

include hB in
/-- Two factorizations of the same morphism through two stages agree in the common refinement. -/
theorem comp_eq_of_isStageFactor {f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB}
    {J K : WeakIdeals Bt} {t : X.1 ⟶ yoneda.obj (stageObj DB J)}
    {t' : X.1 ⟶ yoneda.obj (stageObj DB K)} (h : IsStageFactor X f J t)
    (h' : IsStageFactor X f K t') :
    t ≫ yoneda.map (stageMap DB (stageInfLeft J K)) =
      t' ≫ yoneda.map (stageMap DB (stageInfRight J K)) := by
  have h₁ := isStageFactor_comp X h (stageInfLeft J K)
  have h₂ := isStageFactor_comp X h' (stageInfRight J K)
  have := mono_stageIncl hB DB (stageInf J K)
  have e := h₁.trans h₂.symm
  rw [← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at e
  obtain ⟨_, -, huniq⟩ := existsUnique_sheafifiedULiftMap X.2.isSheaf
    (isAlgebraicSpace_yoneda B S hS (stageObj DB (stageInf J K))).isSheaf
    (sheafifiedULiftMap B S hS (t ≫ yoneda.map (stageMap DB (stageInfLeft J K))))
  exact (huniq _ rfl).trans (huniq _ e.symm).symm

/-- Pulling functions back along `t ≫ yoneda.map g` is pulling back along `g`, then along `t`. -/
theorem pullbackRingHom_homMk_comp {V W : BigFppfOver B S hS} (t : X.1 ⟶ yoneda.obj W)
    (g : W ⟶ V) (x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    pullbackRingHom B V (ObjectProperty.homMk (t ≫ yoneda.map g)) x =
      pullbackRingHom B W (ObjectProperty.homMk t)
        (((BigFppfOver.toScheme B S hS).map g).appTop x) :=
  pullbackToGlobalFunctions_comp_schemeSpaceMap B S hS X (ObjectProperty.homMk t) g x

/-- The ring map of a stage factorization. -/
abbrev stageFactorRingHom {J : WeakIdeals Bt} (t : X.1 ⟶ yoneda.obj (stageObj DB J)) :
    Bt →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  (pullbackRingHom B (stageObj DB J) (ObjectProperty.homMk t)).comp (stageRingHom DB J)

omit [IsTopologicalRing Bt] [IsLinearTopology Bt Bt] in
/-- The ring map of a stage factorization is unchanged by composing with a transition morphism. -/
theorem stageFactorRingHom_comp {J K : WeakIdeals Bt} (t : X.1 ⟶ yoneda.obj (stageObj DB J))
    (u : J ⟶ K) :
    stageFactorRingHom X (t ≫ yoneda.map (stageMap DB u)) = stageFactorRingHom X t :=
  RingHom.ext fun b => (pullbackRingHom_homMk_comp X t (stageMap DB u) (stageRingHom DB K b)).trans
    (congrArg (pullbackRingHom B _ (ObjectProperty.homMk t))
      (congrArg (fun φ => φ b) (appTop_stageMap_comp_stageRingHom DB u)))

include hB in
/-- Two factorizations of the same morphism through quotient stages have the same ring map. -/
theorem ringHom_eq_of_isStageFactor {f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB}
    {J K : WeakIdeals Bt} {t : X.1 ⟶ yoneda.obj (stageObj DB J)}
    {t' : X.1 ⟶ yoneda.obj (stageObj DB K)} (h : IsStageFactor X f J t)
    (h' : IsStageFactor X f K t') :
    stageFactorRingHom X t = stageFactorRingHom X t' := by
  rw [← stageFactorRingHom_comp X t (stageInfLeft J K),
    ← stageFactorRingHom_comp X t' (stageInfRight J K), comp_eq_of_isStageFactor hB X h h']

/-- **The ring map `B ⟶ Γ(X, 𝒪_X)` of a morphism `X ⟶ Spf B`** out of a quasi-compact algebraic
space: pull functions back along a factorization `X ⟶ Spec (B ⧸ J)` through a quotient stage
(Stacks 0AIA). -/
def formalRingHom (hX : IsQuasiCompactSpace B S hS X.1)
    (f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB) :
    Bt →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  stageFactorRingHom X (exists_isStageFactor hB X hX f).choose_spec.choose

/-- The ring map of a morphism factoring through a given stage. -/
theorem formalRingHom_eq (hX : IsQuasiCompactSpace B S hS X.1)
    {f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB} {J : WeakIdeals Bt}
    {t : X.1 ⟶ yoneda.obj (stageObj DB J)} (h : IsStageFactor X f J t) :
    formalRingHom hB X hX f = stageFactorRingHom X t :=
  ringHom_eq_of_isStageFactor hB X (exists_isStageFactor hB X hX f).choose_spec.choose_spec h

/-- **A morphism `X ⟶ Spf B` is determined by its ring map.** -/
theorem formalRingHom_injective (hX : IsQuasiCompactSpace B S hS X.1)
    {f f' : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB}
    (h : formalRingHom hB X hX f = formalRingHom hB X hX f') : f = f' := by
  obtain ⟨J, t, ht⟩ := exists_isStageFactor hB X hX f
  obtain ⟨K, t', ht'⟩ := exists_isStageFactor hB X hX f'
  rw [formalRingHom_eq hB X hX ht, formalRingHom_eq hB X hX ht',
    ← stageFactorRingHom_comp X t (stageInfLeft J K),
    ← stageFactorRingHom_comp X t' (stageInfRight J K)] at h
  have h₁ := isStageFactor_comp X ht (stageInfLeft J K)
  have h₂ := isStageFactor_comp X ht' (stageInfRight J K)
  suffices e : t ≫ yoneda.map (stageMap DB (stageInfLeft J K)) =
      t' ≫ yoneda.map (stageMap DB (stageInfRight J K)) by
    unfold IsStageFactor at h₁ h₂
    rw [← h₁, ← h₂, e]
  have hp : pullbackRingHom B _ (ObjectProperty.homMk (t ≫ yoneda.map (stageMap DB
      (stageInfLeft J K))) : X ⟶ schemeSpace _) =
      pullbackRingHom B _ (ObjectProperty.homMk (t' ≫ yoneda.map (stageMap DB
        (stageInfRight J K))) : X ⟶ schemeSpace _) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := stageRingHom_surjective DB (stageInf J K) x
    exact congrArg (fun φ => φ b) h
  exact congrArg (fun m => m.hom) (pullbackToGlobalFunctions_injective B S hS X _ hp)

/-- **Naturality of the ring map** along a morphism `m : X' ⟶ X` of quasi-compact algebraic
spaces. -/
theorem formalRingHom_comp {X' : AlgebraicSpaces B S hS} (m : X' ⟶ X)
    (hX' : IsQuasiCompactSpace B S hS X'.1) (hX : IsQuasiCompactSpace B S hS X.1)
    (f : sheafifiedULift B S hS X.1 ⟶ formalSpectrum DB) :
    formalRingHom hB X' hX' (sheafifiedULiftMap B S hS m.hom ≫ f) =
      (globalSectionsRingHomSite B S hS m).comp (formalRingHom hB X hX f) := by
  obtain ⟨J, t, ht⟩ := exists_isStageFactor hB X hX f
  have ht' : IsStageFactor X' (sheafifiedULiftMap B S hS m.hom ≫ f) J (m.hom ≫ t) := by
    unfold IsStageFactor at ht ⊢
    rw [sheafifiedULiftMap_comp, Category.assoc, ht]
  rw [formalRingHom_eq hB X' hX' ht', formalRingHom_eq hB X hX ht, stageFactorRingHom,
    stageFactorRingHom, ← RingHom.comp_assoc, globalSectionsRingHomSite_comp_pullbackRingHom]
  rfl

end AlgebraicGeometry.Artin.FormalRing

end
