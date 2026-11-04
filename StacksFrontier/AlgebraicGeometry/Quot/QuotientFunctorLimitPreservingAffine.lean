module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorFlatAtStage
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingReduction
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSpaceModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitQuotientClauses
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyLimitStageDescent

/-!
# The affine case of Stacks 082Q

Let `U` and `T₀` be affine schemes of the site, let `f₀ : U ⟶ T₀` be locally of finite
presentation and let `F` be a quasi-coherent module of finite presentation on `U`.  This file
proves that the functor `Q^{fp}_{F/U/T₀}` of finitely presented quotients is limit preserving.
This is the affine case to which the reduction
`limitPreserving_finitePresentationQuotientsFunctor_of_affineCase` (in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorLimitPreservingReduction.lean`) reduces
Stacks 082Q.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.limitPreserving_affineQuotientSituation`: the affine
  case of Stacks 082Q for a morphism of the site.
* `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_affine`: the affine case
  of Stacks 082Q, in the shape of the hypothesis of the reduction.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} {D₃ : Type*} [Category* C] [Category* D₁]
  [Category* D₂] [Category* D₃] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

omit [Abelian D₃] in
/-- **Two quotients related after a composite inverse image have related conjugates.**  If the
images under `L ⋙ L'` of the projections of `P₁ M` onto its quotients by `K` and `K'` differ by
an isomorphism of their targets, then so do the images under `L'` of the projections of `P₂ M`
onto its quotients by the two conjugate subobjects. -/
theorem exists_iso_map_conjSubobject [L.PreservesEpimorphisms] (e : P₂ ≅ P₁ ⋙ L) {M : C}
    (K K' : Subobject (P₁.obj M)) (L' : D₂ ⥤ D₃)
    (h : ∃ ι : (L ⋙ L').obj (cokernel K.arrow) ≅ (L ⋙ L').obj (cokernel K'.arrow),
      (L ⋙ L').map (cokernel.π K.arrow) ≫ ι.hom = (L ⋙ L').map (cokernel.π K'.arrow)) :
    ∃ ι : L'.obj (cokernel (conjSubobject e K).arrow) ≅
        L'.obj (cokernel (conjSubobject e K').arrow),
      L'.map (cokernel.π (conjSubobject e K).arrow) ≫ ι.hom =
        L'.map (cokernel.π (conjSubobject e K').arrow) := by
  obtain ⟨ι, hι⟩ := h
  refine ⟨L'.mapIso (conjSubobjectCokernelIso e K) ≪≫ ι ≪≫
    (L'.mapIso (conjSubobjectCokernelIso e K')).symm, ?_⟩
  have hK := cokernel_π_comp_conjSubobjectCokernelIso_hom e K
  have hK' : cokernel.π (conjSubobject e K').arrow =
      conjQuotientProjection e K' ≫ (conjSubobjectCokernelIso e K').inv := by
    rw [← cokernel_π_comp_conjSubobjectCokernelIso_hom e K', Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [Functor.comp_obj, Functor.comp_map] at hι
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← L'.map_comp_assoc, hK, hK']
  dsimp only [conjQuotientProjection]
  simp only [L'.map_comp, Category.assoc]
  rw [reassoc_of% hι]

/-- The component at `M` of a comparison `e : P₂ ≅ P₁ ⋙ L`, inverted and with its source written
as `L.obj (P₁.obj M)`. -/
def compIsoAppSymm {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {P₂ : C₁ ⥤ C₃} {P₁ : C₁ ⥤ C₂} {L : C₂ ⥤ C₃} (e : P₂ ≅ P₁ ⋙ L) (M : C₁) :
    L.obj (P₁.obj M) ≅ P₂.obj M :=
  (e.app M).symm

/-- The forward map of `compIsoAppSymm e M` is the component of `e.inv` at `M`. -/
@[simp]
theorem compIsoAppSymm_hom {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {P₂ : C₁ ⥤ C₃} {P₁ : C₁ ⥤ C₂} {L : C₂ ⥤ C₃} (e : P₂ ≅ P₁ ⋙ L) (M : C₁) :
    (compIsoAppSymm e M).hom = e.inv.app M :=
  rfl

/-- The inverse map of `compIsoAppSymm e M` is the component of `e.hom` at `M`. -/
@[simp]
theorem compIsoAppSymm_inv {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {P₂ : C₁ ⥤ C₃} {P₁ : C₁ ⥤ C₂} {L : C₂ ⥤ C₃} (e : P₂ ≅ P₁ ⋙ L) (M : C₁) :
    (compIsoAppSymm e M).inv = e.hom.app M :=
  rfl

/-- **A pasting identity of natural isomorphisms, read at an object**, in the orientation in which
the comparisons identify iterated inverse images with single ones: if
`tkr ≪≫ Pp ◁ tk = tr ≪≫ tq ▷ Pf ≪≫ α`, then
`tk_{Pp F} ≫ Pf (tq_F⁻¹) ≫ tr_F⁻¹ = tkr_F⁻¹`. -/
theorem app_symm_coherence_of_pasting {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] {Pp : C₄ ⥤ C₃} {Pq : C₄ ⥤ C₂} {Pr : C₄ ⥤ C₁} {Pk : C₃ ⥤ C₁}
    {Pg : C₃ ⥤ C₂} {Pf : C₂ ⥤ C₁} (tk : Pk ≅ Pg ⋙ Pf) (tq : Pq ≅ Pp ⋙ Pg) (tr : Pr ≅ Pq ⋙ Pf)
    (tkr : Pr ≅ Pp ⋙ Pk)
    (h : tkr ≪≫ isoWhiskerLeft Pp tk = tr ≪≫ isoWhiskerRight tq Pf ≪≫ associator Pp Pg Pf)
    (F : C₄) :
    tk.hom.app (Pp.obj F) ≫ Pf.map (compIsoAppSymm tq F).hom ≫ (compIsoAppSymm tr F).hom =
      (compIsoAppSymm tkr F).hom := by
  have H := congrArg (fun i => i.hom.app F) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, associator_hom_app, Category.comp_id] at H
  have ha : tk.hom.app (Pp.obj F) = tkr.inv.app F ≫ tr.hom.app F ≫ Pf.map (tq.hom.app F) := by
    rw [← H, Iso.inv_hom_id_app_assoc]
  simp only [compIsoAppSymm_hom, ha, Category.assoc]
  rw [← Pf.map_comp_assoc, Iso.hom_inv_id_app, Pf.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id]

/-- `CategoryTheory.Functor.app_symm_coherence_of_pasting` with the object, the two identifications
of iterated inverse images and their source and target objects abstracted into variables pinned
down by equations, so that it can be instantiated at objects and isomorphisms given by
definitions without the kernel having to unfold them inside the inverse images. -/
theorem app_symm_coherence_of_pasting_of_heq {C₁ C₂ C₃ C₄ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₄] {Pp : C₄ ⥤ C₃} {Pq : C₄ ⥤ C₂} {Pr : C₄ ⥤ C₁}
    {Pk : C₃ ⥤ C₁} {Pg : C₃ ⥤ C₂} {Pf : C₂ ⥤ C₁} (tk : Pk ≅ Pg ⋙ Pf) (tq : Pq ≅ Pp ⋙ Pg)
    (tr : Pr ≅ Pq ⋙ Pf) (tkr : Pr ≅ Pp ⋙ Pk)
    (h : tkr ≪≫ isoWhiskerLeft Pp tk = tr ≪≫ isoWhiskerRight tq Pf ≪≫ associator Pp Pg Pf)
    (F : C₄) {M : C₃} (hM : M = Pp.obj F) {N : C₂} (hN : N = Pq.obj F) {L : C₁}
    (hL : L = Pr.obj F) (σ : Pg.obj M ≅ N) (hσ : HEq σ (compIsoAppSymm tq F))
    (τj : Pf.obj N ≅ L) (hτj : HEq τj (compIsoAppSymm tr F)) (τk : Pk.obj M ≅ L)
    (hτk : HEq τk (compIsoAppSymm tkr F)) :
    tk.hom.app M ≫ Pf.map σ.hom ≫ τj.hom = τk.hom := by
  subst hM hN hL
  obtain rfl := eq_of_heq hσ
  obtain rfl := eq_of_heq hτj
  obtain rfl := eq_of_heq hτk
  exact app_symm_coherence_of_pasting tk tq tr tkr h F

/-- `CategoryTheory.Functor.conjSubobject_kernelSubobject_eq` with the identification of the
source and the subobject abstracted into variables pinned down by equations. -/
theorem conjSubobject_eq_kernelSubobject_of_heq {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂] [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁}
    {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M : C} {M₁ : D₁} (hM : M₁ = P₁.obj M)
    (τ : L.obj M₁ ≅ P₂.obj M) (hτ : HEq τ (compIsoAppSymm e M)) {N : D₁} (ψ : M₁ ⟶ N) [Epi ψ]
    (K : Subobject (P₁.obj M)) (hK : HEq K (Limits.kernelSubobject ψ))
    {Q : D₂} (p : P₂.obj M ⟶ Q) (α : L.obj N ≅ Q) (hα : τ.inv ≫ L.map ψ ≫ α.hom = p) :
    conjSubobject e K = Limits.kernelSubobject p := by
  subst hM
  obtain rfl := eq_of_heq hτ
  obtain rfl := eq_of_heq hK
  exact conjSubobject_kernelSubobject_eq e ψ p α hα

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.QuotientSituation

open HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/- The inverse images and their comparisons are not unfolded below. -/
attribute [local irreducible] modulePullback modulePullbackTriangle

section Fiber

variable {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)

/-- The projection `T ×_{T₀} U ⟶ U` of the fibre product in the site, read as a morphism of
represented algebraic spaces. -/
abbrev affineFiberToSource (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    representedAlgebraicSpace B S hS ((affineFiber f₀).obj T) ⟶
      (schemeSpaceFunctor B S hS).obj U :=
  (schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom T) f₀)

/-- The morphisms of fibre products commute with the projections to `U`. -/
theorem affineFiberMap_comp_toSource {T' T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T' ⟶ T) :
    representedSpaceMap B S hS (affineFiberMap f₀ g) ≫ affineFiberToSource f₀ T =
      affineFiberToSource f₀ T' :=
  ((schemeSpaceFunctor B S hS).map_comp _ _).symm.trans
    (congrArg (schemeSpaceFunctor B S hS).map (affineFiberMap_snd f₀ g))

/-- The identification of the represented fibre product with the base change is natural in the
test scheme. -/
theorem affineFiberMap_comp_affineFiberIso_hom
    {T' T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)} (g : T' ⟶ T) :
    representedSpaceMap B S hS (affineFiberMap f₀ g) ≫ (affineFiberIso f₀ T).hom =
      (affineFiberIso f₀ T').hom ≫ baseChangeMap ((schemeSpaceFunctor B S hS).map f₀) g := by
  show (schemeSpaceFunctor B S hS).map (affineFiberMap f₀ g) ≫ (affineFiberIso f₀ T).hom =
    (affineFiberIso f₀ T').hom ≫ baseChangeMap ((schemeSpaceFunctor B S hS).map f₀) g
  refine baseChange_hom_ext ((schemeSpaceFunctor B S hS).map f₀) ?_ ?_
  · simp only [Category.assoc, affineFiberIso_hom_projection, baseChangeMap_comp_projection]
    rw [← Functor.map_comp, affineFiberMap_snd]
  · simp only [Category.assoc, affineFiberIso_hom_inclusion, baseChangeMap_comp_inclusion,
      affineFiberIso_hom_inclusion_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, affineFiberMap_fst]

end Fiber

/-! ### Finite presentation of cokernels -/

/-- **The cokernel of a morphism of modules of finite presentation on an algebraic space is of
finite presentation** (Stacks 0H98 on the small étale ringed site). -/
theorem isFinitePresentationOnSite_cokernel_of_isFinitePresentationOnSite
    {X : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) :
    (cokernel f).IsFinitePresentationOnSite := by
  rw [SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation] at hM hN ⊢
  exact Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel _ f

/-! ### Restriction of quotients along a composite -/

/-- Restricting a quotient along `g` and then along `g'` is restricting it along `g' ≫ g`. -/
theorem quotientRestrictOver_quotientRestrictOver {X W W' W'' : AlgebraicSpaces B S hS}
    {a : W ⟶ X} {a' : W' ⟶ X} {a'' : W'' ⟶ X} (g : W' ⟶ W) (g' : W'' ⟶ W') (h₂ : g ≫ a = a')
    (h₁ : g' ≫ a' = a'') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrictOver g' h₁ F (quotientRestrictOver g h₂ F K) =
      quotientRestrictOver (g' ≫ g) (by rw [Category.assoc, h₂, h₁]) F K :=
  quotientRestrictOver_comp (modulePushforwardCoherence B S hS) rfl h₂ h₁ _ F K

section Translation

variable {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)
  (F : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)
  (hFq : F.IsQuasicoherentOnSite)

/-- The quotient situation of `F` along the represented morphism `f₀ : U ⟶ T₀`. -/
abbrev affineQuotientSituation : QuotientSituation B S hS :=
  QuotientSituation.mk _ _ ((schemeSpaceFunctor B S hS).map f₀) F hFq

/-- The identification of the represented fibre product with the base change, over `U`. -/
theorem affineFiberIso_hom_toSource (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    (affineFiberIso f₀ T).hom ≫ (affineQuotientSituation f₀ F hFq).sourceProjection T =
      affineFiberToSource f₀ T :=
  affineFiberIso_hom_projection f₀ T

/-- The inverse identification, over `U`. -/
theorem affineFiberIso_inv_toSource (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    (affineFiberIso f₀ T).inv ≫ affineFiberToSource f₀ T =
      (affineQuotientSituation f₀ F hFq).sourceProjection T := by
  rw [← affineFiberIso_hom_toSource f₀ F hFq T, Iso.inv_hom_id_assoc]

/-- **A quotient of `F_T`, read on the represented fibre product `T ×_{T₀} U`.** -/
def affineFiberQuotient (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T)) :
    Subobject ((modulePullback B S hS (affineFiberToSource f₀ T)).obj F) :=
  quotientRestrictOver (affineFiberIso f₀ T).hom (affineFiberIso_hom_toSource f₀ F hFq T) F K

/-- A quotient on the represented fibre product `T ×_{T₀} U`, read on `X_T`. -/
def affineFiberQuotientInv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((modulePullback B S hS (affineFiberToSource f₀ T)).obj F)) :
    Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T) :=
  quotientRestrictOver (affineFiberIso f₀ T).inv (affineFiberIso_inv_toSource f₀ F hFq T) F K

/-- Reading a quotient of `F_T` on `T ×_{T₀} U` and back on `X_T` recovers it. -/
theorem affineFiberQuotientInv_affineFiberQuotient
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T)) :
    affineFiberQuotientInv f₀ F hFq T (affineFiberQuotient f₀ F hFq T K) = K :=
  (quotientRestrictOver_quotientRestrictOver _ _ _ _ F K).trans
    ((quotientRestrictOver_congr (Iso.inv_hom_id _) _ (Category.id_comp _) F K).trans
      (quotientRestrictOver_eq_id _ F K))

/-- Reading a quotient on `T ×_{T₀} U` on `X_T` and back on `T ×_{T₀} U` recovers it. -/
theorem affineFiberQuotient_affineFiberQuotientInv
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((modulePullback B S hS (affineFiberToSource f₀ T)).obj F)) :
    affineFiberQuotient f₀ F hFq T (affineFiberQuotientInv f₀ F hFq T K) = K :=
  (quotientRestrictOver_quotientRestrictOver _ _ _ _ F K).trans
    ((quotientRestrictOver_congr (Iso.hom_inv_id _) _ (Category.id_comp _) F K).trans
      (quotientRestrictOver_eq_id _ F K))

/-- Reading quotients of `F_T` on the represented fibre product `T ×_{T₀} U` is injective. -/
theorem affineFiberQuotient_injective (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    Function.Injective (affineFiberQuotient f₀ F hFq T) := fun K K' h => by
  rw [← affineFiberQuotientInv_affineFiberQuotient f₀ F hFq T K, h,
    affineFiberQuotientInv_affineFiberQuotient]

/-- **Reading on the fibre products commutes with pullback of quotients.** -/
theorem affineFiberQuotient_quotientPullback
    {T' T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)} (g : T' ⟶ T)
    (K : Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T)) :
    affineFiberQuotient f₀ F hFq T' ((affineQuotientSituation f₀ F hFq).quotientPullback g K) =
      quotientRestrictOver (representedSpaceMap B S hS (affineFiberMap f₀ g))
        (affineFiberMap_comp_toSource f₀ g) F (affineFiberQuotient f₀ F hFq T K) := by
  refine (quotientRestrictOver_quotientRestrictOver _ _ _ _ F K).trans ?_
  refine Eq.trans ?_ (quotientRestrictOver_quotientRestrictOver _ _ _ _ F K).symm
  exact quotientRestrictOver_congr (affineFiberMap_comp_affineFiberIso_hom f₀ g).symm _ _ F K

/-- The quotient by a quotient read on the fibre product is the inverse image of the quotient. -/
def affineFiberQuotientCokernelIso (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T)) :
    cokernel (affineFiberQuotient f₀ F hFq T K).arrow ≅
      (modulePullback B S hS (affineFiberIso f₀ T).hom).obj (cokernel K.arrow) :=
  quotientRestrictOverCokernelIso _ _ F K

/-- The quotient by a quotient read back on `X_T` is the inverse image of the quotient. -/
def affineFiberQuotientInvCokernelIso (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (K : Subobject ((modulePullback B S hS (affineFiberToSource f₀ T)).obj F)) :
    cokernel (affineFiberQuotientInv f₀ F hFq T K).arrow ≅
      (modulePullback B S hS (affineFiberIso f₀ T).inv).obj (cokernel K.arrow) :=
  quotientRestrictOverCokernelIso _ _ F K

end Translation


section Stage

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS)
  (cV : Cone V) (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hcV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
  {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
  (b : ∀ j, representedAlgebraicSpace B S hS (V.obj j) ⟶ X)
  (bL : representedAlgebraicSpace B S hS cV.pt ⟶ X)
  (hb : ∀ {j k : I} (e : j ⟶ k), representedSpaceMap B S hS (V.map e) ≫ b k = b j)
  (hbL : ∀ j, representedSpaceMap B S hS (conePr B S hS V cV j) ≫ b j = bL)

/-- The inverse image of `F` to a stage of an inverse system of objects of the site, along a
morphism from the represented algebraic space of the stage. -/
def affineSystemStageModule (j : I) :
    Modules.{u, u} B S hS (representedAlgebraicSpace B S hS (V.obj j)).1
      (representedAlgebraicSpace B S hS (V.obj j)).2 :=
  (modulePullback B S hS (b j)).obj F

/-- The identification of the inverse image to the limit of the inverse image of `F` to a stage
with the inverse image of `F` to the limit, in the spelling of the pullback system of the
represented algebraic spaces. -/
def affineSystemStageTau (j : I) :
    ((affineSpacePullbackSystem B S hS V cV).pbL j).obj (affineSystemStageModule V F b j) ≅
      (modulePullback B S hS bL).obj F :=
  Functor.compIsoAppSymm (L := (affineSpacePullbackSystem B S hS V cV).pbL j)
    (modulePullbackTriangle B S hS (hbL j)) F

/-- The identification of the inverse image along a transition morphism of the inverse image of
`F` to a stage with the inverse image of `F` to the earlier stage, in the spelling of the pullback
system of the represented algebraic spaces. -/
def affineSystemStageSigma {j k : I} (e : j ⟶ k) :
    ((affineSpacePullbackSystem B S hS V cV).pb e).obj (affineSystemStageModule V F b k) ≅
      affineSystemStageModule V F b j :=
  Functor.compIsoAppSymm (L := (affineSpacePullbackSystem B S hS V cV).pb e)
    (modulePullbackTriangle B S hS (hb e)) F

include hV hcV hb hbL in
/-- **A finitely presented quotient over the limit comes from a stage**, for an inverse system of
affine schemes of the site read on their represented algebraic spaces, and the inverse images of
a module of finite presentation along compatible morphisms to an algebraic space `X`
(Stacks 07V7 and 05LI). -/
theorem exists_stage_quotient_of_affineSystem (hF : F.IsFinitePresentationOnSite)
    (Kz : Subobject ((modulePullback B S hS bL).obj F))
    (hKz : (cokernel Kz.arrow).IsFinitePresentationOnSite) :
    ∃ (j : I) (Kj : Subobject ((modulePullback B S hS (b j)).obj F)),
      (cokernel Kj.arrow).IsFinitePresentationOnSite ∧
        quotientRestrictOver (representedSpaceMap B S hS (conePr B S hS V cV j)) (hbL j) F Kj =
          Kz := by
  have hFa := affineSpacePullbackSystem_faithfulness B S hS V cV hV hcV
  have hFu := affineSpacePullbackSystem_fullness B S hS V cV hV hcV
  have hEs := affineSpacePullbackSystem_essSurj B S hS V cV hV hcV
  have : ∀ {j k : I} (e : j ⟶ k),
      ((affineSpacePullbackSystem B S hS V cV).pb e).IsLeftAdjoint :=
    fun _ ↦ (modulePullbackAdjunction B S hS _).isLeftAdjoint
  have : ∀ j, ((affineSpacePullbackSystem B S hS V cV).pbL j).IsLeftAdjoint := fun _ ↦
    (modulePullbackAdjunction B S hS _).isLeftAdjoint
  have : ∀ {j k : I} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair
      ((affineSpacePullbackSystem B S hS V cV).pb e) := fun _ ↦
    AlgebraicGeometry.Space.modulePullback_preservesColimitsOfShape B S hS _
  obtain ⟨j, N, ψ, hN, hψ, α, hα⟩ :=
    Stacks.ModuleColimit.PullbackSystem.exists_quotient_of_quotient_pbL
      (affineSpacePullbackSystem B S hS V cV)
      hFa hFu hEs
      (fun _ N hN ↦ isFinitePresentationOnSite_modulePullback B S hS _ N hN)
      (fun _ _ _ f hM hN ↦
        isFinitePresentationOnSite_cokernel_of_isFinitePresentationOnSite f hM hN)
      (Mj := affineSystemStageModule V F b)
      (fun _ ↦ isFinitePresentationOnSite_modulePullback B S hS _ F hF)
      (ML := (modulePullback B S hS bL).obj F)
      (affineSystemStageTau V cV F b bL hbL)
      (@affineSystemStageSigma _ _ _ _ _ _ V cV _ F b hb)
      (fun {j k} e ↦ Functor.app_symm_coherence_of_pasting_of_heq
        ((affineSpacePullbackSystem B S hS V cV).comp e)
        (modulePullbackTriangle B S hS (hb e)) (modulePullbackTriangle B S hS (hbL j))
        (modulePullbackTriangle B S hS (hbL k))
        ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp
          ((representedSpaceMap_comp B S hS _ _).trans
            (congrArg (representedSpaceMap B S hS) (conePr_comp B S hS V cV e)))
          (hb e) (hbL j) (hbL k)) F (M := affineSystemStageModule V F b k) rfl
        (N := affineSystemStageModule V F b j) rfl (L := (modulePullback B S hS bL).obj F) rfl
        (affineSystemStageSigma V cV F b hb e) HEq.rfl
        (affineSystemStageTau V cV F b bL hbL j) HEq.rfl
        (affineSystemStageTau V cV F b bL hbL k) HEq.rfl)
      (Q := cokernel Kz.arrow) hKz (cokernel.π Kz.arrow)
  have := hψ
  refine ⟨j, kernelSubobject ψ, ?_, ?_⟩
  · exact SheafOfModules.IsFinitePresentationOnSite.of_iso
      (Abelian.cokernelKernelSubobjectIso ψ).symm hN
  · refine Eq.trans ?_ (kernelSubobject_cokernel_π Kz)
    exact Functor.conjSubobject_eq_kernelSubobject_of_heq
      (L := (affineSpacePullbackSystem B S hS V cV).pbL j)
      (modulePullbackTriangle B S hS (hbL j)) (M := F) (M₁ := affineSystemStageModule V F b j)
      rfl (affineSystemStageTau V cV F b bL hbL j) HEq.rfl ψ (kernelSubobject ψ) HEq.rfl
      (cokernel.π Kz.arrow) α hα

omit [IsCofiltered I] in
/-- Restricting a quotient along two transition morphisms is restricting it along their
composite. -/
theorem quotientRestrictOver_quotientRestrictOver_map {j j' k : I} (e' : j' ⟶ j) (e : j ⟶ k)
    (K : Subobject ((modulePullback B S hS (b k)).obj F)) :
    quotientRestrictOver (representedSpaceMap B S hS (V.map e')) (hb e') F
        (quotientRestrictOver (representedSpaceMap B S hS (V.map e)) (hb e) F K) =
      quotientRestrictOver (representedSpaceMap B S hS (V.map (e' ≫ e))) (hb (e' ≫ e)) F K :=
  (quotientRestrictOver_quotientRestrictOver _ _ _ _ F K).trans
    (quotientRestrictOver_congr ((representedSpaceMap_comp B S hS _ _).trans
      (congrArg (representedSpaceMap B S hS) (V.map_comp e' e).symm)) _ _ F K)

include hV hcV hb hbL in
/-- **Two finitely presented quotients at a stage with the same restriction to the limit agree at
a later stage**, for an inverse system of affine schemes of the site read on their represented
algebraic spaces (Stacks 07V7). -/
theorem eventually_eq_of_affineSystem (hF : F.IsFinitePresentationOnSite) (i : I)
    (K K' : Subobject ((modulePullback B S hS (b i)).obj F))
    (hK : (cokernel K.arrow).IsFinitePresentationOnSite)
    (hK' : (cokernel K'.arrow).IsFinitePresentationOnSite)
    (h : quotientRestrictOver (representedSpaceMap B S hS (conePr B S hS V cV i)) (hbL i) F K =
      quotientRestrictOver (representedSpaceMap B S hS (conePr B S hS V cV i)) (hbL i) F K') :
    ∃ (j : I) (e : j ⟶ i),
      quotientRestrictOver (representedSpaceMap B S hS (V.map e)) (hb e) F K =
        quotientRestrictOver (representedSpaceMap B S hS (V.map e)) (hb e) F K' := by
  have hFa := affineSpacePullbackSystem_faithfulness B S hS V cV hV hcV
  have hFu := affineSpacePullbackSystem_fullness B S hS V cV hV hcV
  have : ∀ {j k : I} (e : j ⟶ k),
      ((affineSpacePullbackSystem B S hS V cV).pb e).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS _)
  have : ∀ j, ((affineSpacePullbackSystem B S hS V cV).pbL j).PreservesEpimorphisms := fun _ ↦
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS _)
  have : ∀ {j k : I} (e : j ⟶ k),
      ((affineSpacePullbackSystem B S hS V cV).pb e).IsLeftAdjoint :=
    fun _ ↦ (modulePullbackAdjunction B S hS _).isLeftAdjoint
  have : ∀ j, ((affineSpacePullbackSystem B S hS V cV).pbL j).IsLeftAdjoint := fun _ ↦
    (modulePullbackAdjunction B S hS _).isLeftAdjoint
  have : ∀ {j k : I} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair
      ((affineSpacePullbackSystem B S hS V cV).pb e) := fun _ ↦
    AlgebraicGeometry.Space.modulePullback_preservesColimitsOfShape B S hS _
  obtain ⟨ι, hι⟩ := Functor.exists_iso_of_conjSubobject_eq
    (L := (affineSpacePullbackSystem B S hS V cV).pbL i)
    (modulePullbackTriangle B S hS (hbL i)) K K' h
  obtain ⟨j₁, e₁, j₂, e₂, j₃, e₃, j₄, e₄, hker⟩ :=
    Stacks.ModuleColimit.PullbackSystem.exists_kernelSubobject_eq_of_pbL
      (affineSpacePullbackSystem B S hS V cV)
      hFa hFu
      (fun _ N hN ↦ isFinitePresentationOnSite_modulePullback B S hS _ N hN)
      (M := (modulePullback B S hS (b i)).obj F)
      (isFinitePresentationOnSite_modulePullback B S hS _ F hF) hK hK'
      (cokernel.π K.arrow) (cokernel.π K'.arrow) ι hι
  have h₀ := Abelian.exists_iso_of_kernelSubobject_eq _ _ hker
  have h₁ := Functor.exists_iso_map_conjSubobject
    (L := (affineSpacePullbackSystem B S hS V cV).pb e₁)
    (modulePullbackTriangle B S hS (hb e₁)) K K' _ h₀
  have h₂ := Functor.exists_iso_map_conjSubobject
    (L := (affineSpacePullbackSystem B S hS V cV).pb e₂)
    (modulePullbackTriangle B S hS (hb e₂)) _ _ _ h₁
  have h₃ := Functor.exists_iso_map_conjSubobject
    (L := (affineSpacePullbackSystem B S hS V cV).pb e₃)
    (modulePullbackTriangle B S hS (hb e₃)) _ _ _ h₂
  obtain ⟨ι₄, hι₄⟩ := h₃
  have h₄ := Functor.conjSubobject_eq_of_iso_comp
    (L := (affineSpacePullbackSystem B S hS V cV).pb e₄)
    (modulePullbackTriangle B S hS (hb e₄)) _ _ ι₄ hι₄
  refine ⟨j₄, e₄ ≫ e₃ ≫ e₂ ≫ e₁, ?_⟩
  simp only [← quotientRestrictOver_quotientRestrictOver_map V F b hb]
  exact h₄

end Stage

/-! ### The affine case -/

section AffineCase

variable {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)
  (F : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)
  (hFq : F.IsQuasicoherentOnSite)

/-- **The affine case of Stacks 082Q, for a morphism of the site.**  For affine `U` and `T₀`, a
morphism `f₀ : U ⟶ T₀` locally of finite presentation and a quasi-coherent module `F` of finite
presentation on `U`, the functor `Q^{fp}_{F/U/T₀}` is limit preserving.

Along a cofiltered limit `T = lim T_i` of affine test schemes the base changes `U_T` are the
represented fibre products `T ×_{T₀} U` of the site
(`AlgebraicGeometry.Space.HomSituation.affineFiberIso`), which form a limit of affine schemes; a
quotient of `F_T` is read on them by
`AlgebraicGeometry.Space.QuotientSituation.affineFiberQuotient`.  A finitely presented quotient
over the limit comes from a stage by Stacks 07V7 and 05LI
(`AlgebraicGeometry.Space.QuotientSituation.exists_stage_quotient_of_affineSystem`), and is flat
at a later stage by Stacks 02JO
(`AlgebraicGeometry.Space.QuotientSituation.exists_isFlatOver_modulePullback_relativeMap`); two
quotients at a stage with the same pullback to the limit agree at a later stage by Stacks 07V7
(`AlgebraicGeometry.Space.QuotientSituation.eventually_eq_of_affineSystem`). -/
theorem limitPreserving_affineQuotientSituation
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hlfp : IsLocallyOfFinitePresentation B S hS ((schemeSpaceFunctor B S hS).map f₀).hom)
    (hF : F.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, u, u} (affineQuotientSituation f₀ F hFq).testScheme
      (affineQuotientSituation f₀ F hFq).finitePresentationQuotientsFunctor := by
  intro I _ _ E c hc hE hpt
  have hqc : IsQuasiCompact B S hS (affineQuotientSituation f₀ F hFq).f.hom :=
    isQuasiCompact_yoneda_of_isAffine B S hS (yoneda.map f₀) hU hT₀
  have hcV := isLimitAffineFiberMapCone f₀ c hc
  have hV : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj ((E ⋙ affineFiber f₀).obj i)) :=
    fun i ↦ isAffine_affineFiber f₀ hU hT₀ _ (hE i)
  have hb : ∀ {j k : I} (e : j ⟶ k), representedSpaceMap B S hS ((E ⋙ affineFiber f₀).map e) ≫
      affineFiberToSource f₀ (E.obj k) = affineFiberToSource f₀ (E.obj j) :=
    fun e ↦ affineFiberMap_comp_toSource f₀ (E.map e)
  have hbL : ∀ j, representedSpaceMap B S hS
      (conePr B S hS (E ⋙ affineFiber f₀) ((affineFiber f₀).mapCone c) j) ≫
        affineFiberToSource f₀ (E.obj j) = affineFiberToSource f₀ c.pt :=
    fun j ↦ affineFiberMap_comp_toSource f₀ (c.π.app j)
  have hfp : ∀ (T : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
      (K : Subobject ((affineQuotientSituation f₀ F hFq).baseChangeModule T)),
      (cokernel K.arrow).IsFinitePresentationOnSite →
        (cokernel (affineFiberQuotient f₀ F hFq T K).arrow).IsFinitePresentationOnSite :=
    fun T K hK ↦ SheafOfModules.IsFinitePresentationOnSite.of_iso
      (affineFiberQuotientCokernelIso f₀ F hFq T K).symm
      (isFinitePresentationOnSite_modulePullback B S hS _ _ hK)
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · -- Joint surjectivity: a finitely presented flat quotient over the limit comes from a stage.
    rintro ⟨K, hK⟩
    obtain ⟨j, Kjz, hKjz, hrel⟩ := exists_stage_quotient_of_affineSystem (E ⋙ affineFiber f₀)
      ((affineFiber f₀).mapCone c) hV hcV F (fun j ↦ affineFiberToSource f₀ (E.obj j))
      (affineFiberToSource f₀ c.pt) hb hbL hF _ (hfp _ _ hK.2)
    have hpull : (affineQuotientSituation f₀ F hFq).quotientPullback (c.π.app j)
        (affineFiberQuotientInv f₀ F hFq (E.obj j) Kjz) = K := by
      refine affineFiberQuotient_injective f₀ F hFq c.pt ?_
      refine (affineFiberQuotient_quotientPullback f₀ F hFq (c.π.app j) _).trans ?_
      rw [affineFiberQuotient_affineFiberQuotientInv]
      exact hrel
    have hKjfp : SheafOfModules.IsFinitePresentationOnSite
        (cokernel (affineFiberQuotientInv f₀ F hFq (E.obj j) Kjz).arrow) :=
      SheafOfModules.IsFinitePresentationOnSite.of_iso
        (affineFiberQuotientInvCokernelIso f₀ F hFq (E.obj j) Kjz).symm
        (isFinitePresentationOnSite_modulePullback B S hS _ _ hKjz)
    have hflat : IsFlatOver B S hS ((affineQuotientSituation f₀ F hFq).space c.pt).2
        ((affineQuotientSituation f₀ F hFq).projection c.pt).hom
        ((modulePullback B S hS ((affineQuotientSituation f₀ F hFq).relativeMap (c.π.app j))).obj
          (cokernel (affineFiberQuotientInv f₀ F hFq (E.obj j) Kjz).arrow)) := by
      refine IsFlatOver.of_iso B S hS _
        ((affineQuotientSituation f₀ F hFq).quotientPullbackCokernelIso (c.π.app j) _) ?_
      rw [hpull]
      exact hK.1.2
    obtain ⟨j', e', hflat'⟩ :=
      (affineQuotientSituation f₀ F hFq).exists_isFlatOver_modulePullback_relativeMap hqc hlfp E c
        hc hE hpt j _ hKjfp hflat
    have hmem : (affineQuotientSituation f₀ F hFq).quotientPullback (E.map e')
        (affineFiberQuotientInv f₀ F hFq (E.obj j) Kjz) ∈
          (affineQuotientSituation f₀ F hFq).finitePresentationQuotients (E.obj j') := by
      have hfp := SheafOfModules.IsFinitePresentationOnSite.of_iso
        ((affineQuotientSituation f₀ F hFq).quotientPullbackCokernelIso (E.map e') _).symm
        (isFinitePresentationOnSite_modulePullback B S hS _ _ hKjfp)
      have := hfp
      exact ⟨⟨inferInstance, IsFlatOver.of_iso B S hS _
        ((affineQuotientSituation f₀ F hFq).quotientPullbackCokernelIso (E.map e') _).symm
        hflat'⟩, hfp⟩
    refine ⟨op j', ⟨_, hmem⟩, Subtype.ext ?_⟩
    show K = (affineQuotientSituation f₀ F hFq).quotientPullback (c.π.app j')
      ((affineQuotientSituation f₀ F hFq).quotientPullback (E.map e')
        (affineFiberQuotientInv f₀ F hFq (E.obj j) Kjz))
    rw [← (affineQuotientSituation f₀ F hFq).quotientPullback_comp
      (modulePushforwardCoherence B S hS), c.w e']
    exact hpull.symm
  · -- Eventual equality: two members at a stage with equal pullbacks agree at a later stage.
    rintro ⟨i⟩ ⟨K, hK⟩ ⟨K', hK'⟩ heq
    have hpull : (affineQuotientSituation f₀ F hFq).quotientPullback (c.π.app i) K =
        (affineQuotientSituation f₀ F hFq).quotientPullback (c.π.app i) K' :=
      congrArg Subtype.val heq
    have hz := congrArg (affineFiberQuotient f₀ F hFq c.pt) hpull
    rw [affineFiberQuotient_quotientPullback, affineFiberQuotient_quotientPullback] at hz
    obtain ⟨j, e, he⟩ := eventually_eq_of_affineSystem (E ⋙ affineFiber f₀)
      ((affineFiber f₀).mapCone c) hV hcV F (fun j ↦ affineFiberToSource f₀ (E.obj j))
      (affineFiberToSource f₀ c.pt) hb hbL hF i _ _
      (hfp _ _ hK.2) (hfp _ _ hK'.2) hz
    have hval : (affineQuotientSituation f₀ F hFq).quotientPullback (E.map e) K =
        (affineQuotientSituation f₀ F hFq).quotientPullback (E.map e) K' := by
      refine affineFiberQuotient_injective f₀ F hFq (E.obj j) ?_
      rw [affineFiberQuotient_quotientPullback, affineFiberQuotient_quotientPullback]
      exact he
    exact ⟨op j, e.op, Subtype.ext hval⟩

/-- **The affine case of Stacks 082Q.**  Let `U` and `T₀` be affine schemes of the site, let
`f_U : U ⟶ T₀` be a morphism of their algebraic spaces locally of finite presentation, and let
`F'` be a quasi-coherent module of finite presentation on `U`.  Then the functor
`Q^{fp}_{F'/U/T₀}` of finitely presented quotients is limit preserving.

This is exactly the affine case taken as a hypothesis by the reduction
`limitPreserving_finitePresentationQuotientsFunctor_of_affineCase`.
The morphism `f_U` is the image of a morphism `f₀ : U ⟶ T₀` of the site (Yoneda), and the case
of such a morphism is
`AlgebraicGeometry.Space.QuotientSituation.limitPreserving_affineQuotientSituation`. -/
theorem limitPreserving_finitePresentationQuotientsFunctor_affine
    (U T₀ : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (fU : (schemeSpaceFunctor B S hS).obj U ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (hfU : IsLocallyOfFinitePresentation B S hS fU.hom)
    (F' : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hF'q : F'.IsQuasicoherentOnSite) (hF' : F'.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, u, u} (QuotientSituation.mk _ _ fU F' hF'q).testScheme
      (QuotientSituation.mk _ _ fU F' hF'q).finitePresentationQuotientsFunctor := by
  obtain ⟨f₀, rfl⟩ : ∃ f₀ : U ⟶ T₀, (schemeSpaceFunctor B S hS).map f₀ = fU :=
    ⟨Yoneda.fullyFaithful.preimage fU.hom,
      ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)⟩
  exact limitPreserving_affineQuotientSituation f₀ F' hF'q hU hT₀ hfU hF'

end AffineCase

end AlgebraicGeometry.Space.QuotientSituation

end
