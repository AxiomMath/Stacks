module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSourceSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingReduction

/-!
# Stacks 082Q: the change of base to a stage

By Remark 08IT (the quotient analogue of Stacks 08JW), the functor of finitely presented
quotients of the base change `F'/X'/T₀` of the situation to a test scheme `T₀` is the functor of
finitely presented quotients of `F/X/Y` restricted to the test schemes over `T₀`. This
identification is natural in the test scheme, and it reduces the limit preservation of
`Q^{fp}_{F/X/Y}` (Stacks 082Q) to that of the functors of finitely presented quotients of the base
changes to affine test schemes.

## Main results

* `CategoryTheory.Subobject.cokernel_π_comp_cokernelTransportEquivIso_hom`: the identification
  of the quotient by a transported subobject commutes with the projections.
* `AlgebraicGeometry.Space.quotientRestrictOver_eq_id`: restriction of a quotient along an
  identity is the identity.
* `AlgebraicGeometry.Space.quotientTransport_quotientRestrictOver_modulePullback`: restricting
  a quotient of an iterated inverse image and then reading it on a single inverse image is
  reading it on the single inverse image and then restricting.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeSubobjectEquiv_quotientPullback`: the
  bijection of Remark 08IT carries pullback of quotients along a morphism of test schemes over
  `Y'` to pullback of quotients.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctorBaseChangeIso`:
  **Remark 08IT, natural in the test scheme**, for the finite-presentation subfunctor.
* `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_stages` (in the
  namespace `AlgebraicGeometry.Space`): `Q^{fp}_{F/X/Y}` is limit preserving as soon as the
  functor of finitely presented quotients of its base change to every affine test scheme is.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

/-! ### The projection onto a transported quotient -/

namespace CategoryTheory.Subobject

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [Abelian C] [Abelian D]

/-- An identification of two subobjects identifies the projections onto their quotients. -/
private theorem cokernel_π_comp_eqToIso_hom {Y : D} {L₁ L₂ : Subobject Y} (h : L₁ = L₂)
    (h' : cokernel L₁.arrow = cokernel L₂.arrow) :
    cokernel.π L₁.arrow ≫ (eqToIso h').hom = cokernel.π L₂.arrow := by
  subst h
  simp

/-- **The identification of the quotient by a transported subobject commutes with the
projections.**  The projection of `Y` onto its quotient by the transport of `K`, followed by
`CategoryTheory.Subobject.cokernelTransportEquivIso`, is the image under the equivalence of the
projection of `X` onto `X/K`, read through `ι`. -/
theorem cokernel_π_comp_cokernelTransportEquivIso_hom (E : C ≌ D) {X : C} {Y : D}
    (ι : E.functor.obj X ≅ Y) (K : Subobject X) :
    cokernel.π (transportEquiv E ι K).arrow ≫ (cokernelTransportEquivIso E ι K).hom =
      ι.inv ≫ E.functor.map (cokernel.π K.arrow) := by
  have hpres : cokernel.π (E.functor.map K.arrow) ≫
      (PreservesCokernel.iso E.functor K.arrow).inv = E.functor.map (cokernel.π K.arrow) := by
    rw [← PreservesCokernel.π_iso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [cokernelTransportEquivIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [cokernel_π_comp_eqToIso_hom (transportEquiv_eq_mk E ι K)]
  simp only [cokernelMkArrowIso, cokernelCompIsIso, cokernelEpiComp, Iso.trans_hom,
    ← Category.assoc, π_comp_cokernelIsoOfEq_hom, cokernel.π_desc]
  rw [Category.assoc, hpres, IsIso.Iso.inv_hom]

end CategoryTheory.Subobject

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The calculus of restriction of quotients over `X` -/

/-- **Restriction of a quotient along an identity is the identity.** -/
theorem quotientRestrictOver_eq_id {X W : AlgebraicSpaces B S hS} {a : W ⟶ X}
    (h : 𝟙 W ≫ a = a) (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrictOver (𝟙 W) h F K = K :=
  Functor.conjSubobject_id _ _
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_id h) K

/-- Restriction of a quotient depends on the morphism along which it is restricted, not on its
spelling. -/
theorem quotientRestrictOver_congr {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X}
    {a' : W' ⟶ X} {g g' : W' ⟶ W} (hg : g = g') (h : g ≫ a = a') (h' : g' ≫ a = a')
    (F : Modules.{u, u} B S hS X.1 X.2) (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrictOver g h F K = quotientRestrictOver g' h' F K := by
  subst hg
  rfl

/-- If the projection onto the quotient by `K` is `m` after identifying the cokernel with `Q`,
then the transport of `K` along `ι` is the kernel of `ι.hom ≫ m`. -/
private theorem quotientTransport_eq_kernelSubobject_comp {C : Type*} [Category* C] [Abelian C]
    {A A' Q : C} (ι : A' ≅ A) (K : Subobject A) (e : cokernel K.arrow ≅ Q) (m : A ⟶ Q)
    (hm : cokernel.π K.arrow ≫ e.hom = m) :
    quotientTransport ι K = kernelSubobject (ι.hom ≫ m) :=
  (kernelSubobject_eq_of_comp_mono _ _ e.hom (by rw [Category.assoc, hm])).symm

/-- **Restriction commutes with reading a quotient of an iterated inverse image on a single
inverse image.**  Let `a : V ⟶ X` and `b : W ⟶ V`, `b' : W' ⟶ V`, and let `g : W' ⟶ W` be a
morphism over `V`.  For a quotient `K` of `b^* a^* F`, reading its restriction along `g` on
`(b' ≫ a)^* F` is restricting along `g` its reading on `(b ≫ a)^* F`. -/
theorem quotientTransport_quotientRestrictOver_modulePullback
    {X V W W' : AlgebraicSpaces B S hS} {a : V ⟶ X} {b : W ⟶ V} {b' : W' ⟶ V}
    {k : W ⟶ X} {k' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ b = b') (hk : b ≫ a = k)
    (hk' : b' ≫ a = k') (hg : g ≫ k = k') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS b).obj ((modulePullback B S hS a).obj F))) :
    quotientTransport ((modulePullbackTriangle B S hS hk').app F)
        (quotientRestrictOver g h ((modulePullback B S hS a).obj F) K) =
      quotientRestrictOver g hg F
        (quotientTransport ((modulePullbackTriangle B S hS hk).app F) K) := by
  have hcoh := congrArg (fun e ↦ e.hom.app F)
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp h hk hg hk')
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hcoh
  have hl : quotientTransport ((modulePullbackTriangle B S hS hk').app F)
      (quotientRestrictOver g h ((modulePullback B S hS a).obj F) K) =
      kernelSubobject ((modulePullbackTriangle B S hS hk').hom.app F ≫
        (modulePullbackTriangle B S hS h).hom.app ((modulePullback B S hS a).obj F) ≫
          (modulePullback B S hS g).map (cokernel.π K.arrow)) := by
    exact quotientTransport_eq_kernelSubobject_comp _ _
      (quotientRestrictOverCokernelIso g h ((modulePullback B S hS a).obj F) K) _
      (Functor.cokernel_π_comp_conjSubobjectCokernelIso_hom _ K)
  have hr : quotientRestrictOver g hg F
      (quotientTransport ((modulePullbackTriangle B S hS hk).app F) K) =
      kernelSubobject ((modulePullbackTriangle B S hS hg).hom.app F ≫
        (modulePullback B S hS g).map ((modulePullbackTriangle B S hS hk).hom.app F) ≫
          (modulePullback B S hS g).map (cokernel.π K.arrow)) := by
    refine kernelSubobject_eq_of_comp_mono _ _
      ((modulePullback B S hS g).map
        (quotientTransportCokernelIso ((modulePullbackTriangle B S hS hk).app F) K).inv) ?_
    show _ = (modulePullbackTriangle B S hS hg).hom.app F ≫ (modulePullback B S hS g).map
      (cokernel.π (quotientTransport ((modulePullbackTriangle B S hS hk).app F) K).arrow)
    rw [← comp_quotientTransportCokernelIso_inv]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  rw [hl, hr]
  exact kernelSubobject_eq_of_comp_mono _ _ (𝟙 _) (by rw [Category.comp_id, reassoc_of% hcoh])

/-- **Restriction along an isomorphism, read through the equivalence it induces.**  For an
isomorphism `φ : Z ≅ A` over `X` (that is, `φ ≫ s = b ≫ a`), transporting a quotient of `s^* F`
to `b^* a^* F` across the equivalence of module categories induced by `φ`, and then reading it
on the single inverse image `(b ≫ a)^* F`, is restricting it along `φ`. -/
theorem quotientTransport_transportEquiv_modulePullbackSquare
    {X V Z A : AlgebraicSpaces B S hS} {a : V ⟶ X} {b : Z ⟶ V} {s : A ⟶ X} (φ : Z ≅ A)
    (hφ : φ.hom ≫ s = b ≫ a) (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS s).obj F)) :
    quotientTransport ((modulePullbackTriangle B S hS (rfl : b ≫ a = b ≫ a)).app F)
        (Subobject.transportEquiv
          ((modulePushforwardCoherence B S hS).modulePullbackEquivalence φ)
          ((modulePullbackSquare B S hS hφ rfl).app F) K) =
      quotientRestrictOver φ.hom hφ F K := by
  have hπ := Subobject.cokernel_π_comp_cokernelTransportEquivIso_hom
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence φ)
    ((modulePullbackSquare B S hS hφ rfl).app F) K
  refine (quotientTransport_eq_kernelSubobject_comp _ _ _ _ hπ).trans ?_
  unfold quotientRestrictOver Functor.conjSubobject Functor.conjQuotientProjection
  congr 1
  show (modulePullbackTriangle B S hS (rfl : b ≫ a = b ≫ a)).hom.app F ≫
      ((modulePullbackTriangle B S hS (rfl : b ≫ a = b ≫ a)).inv.app F ≫
        (modulePullbackTriangle B S hS hφ).hom.app F) ≫
        (modulePullback B S hS φ.hom).map (cokernel.π K.arrow) =
    (modulePullbackTriangle B S hS hφ).hom.app F ≫
      (modulePullback B S hS φ.hom).map (cokernel.π K.arrow)
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **Naturality of a family of readings of quotients, from the naturality of the morphisms.**
Let `a : V ⟶ X`, let `b : Z ⟶ V` and `b' : Z' ⟶ V` with `r : Z' ⟶ Z` over `V`, let `s : A ⟶ X`
and `s' : A' ⟶ X` with `ρ : A' ⟶ A` over `X`, and let `φ : Z ⟶ A`, `φ' : Z' ⟶ A'` be morphisms
over `X` with `r ≫ φ = φ' ≫ ρ`.  If a quotient `K₁` of `b^* a^* F` reads on `(b ≫ a)^* F` as the
restriction of `K` along `φ`, and `K₂` of `b'^* a^* F` reads as the restriction along `φ'` of the
restriction of `K` along `ρ`, then `K₂` is the restriction of `K₁` along `r`. -/
theorem eq_quotientRestrictOver_of_quotientTransport_eq
    {X V Z Z' A A' : AlgebraicSpaces B S hS} {a : V ⟶ X} {b : Z ⟶ V} {b' : Z' ⟶ V}
    {s : A ⟶ X} {s' : A' ⟶ X} {k : Z ⟶ X} {k' : Z' ⟶ X} (r : Z' ⟶ Z) (hr : r ≫ b = b')
    (ρ : A' ⟶ A) (hρ : ρ ≫ s = s') {φ : Z ⟶ A} {φ' : Z' ⟶ A'} (hk : b ≫ a = k)
    (hk' : b' ≫ a = k') (hφ : φ ≫ s = k) (hφ' : φ' ≫ s' = k') (hm : r ≫ φ = φ' ≫ ρ)
    (F : Modules.{u, u} B S hS X.1 X.2) (K : Subobject ((modulePullback B S hS s).obj F))
    {K₁ : Subobject ((modulePullback B S hS b).obj ((modulePullback B S hS a).obj F))}
    {K₂ : Subobject ((modulePullback B S hS b').obj ((modulePullback B S hS a).obj F))}
    (h₁ : quotientTransport ((modulePullbackTriangle B S hS hk).app F) K₁ =
      quotientRestrictOver φ hφ F K)
    (h₂ : quotientTransport ((modulePullbackTriangle B S hS hk').app F) K₂ =
      quotientRestrictOver φ' hφ' F (quotientRestrictOver ρ hρ F K)) :
    K₂ = quotientRestrictOver r hr ((modulePullback B S hS a).obj F) K₁ := by
  have hc := modulePushforwardCoherence B S hS
  have hg : r ≫ k = k' := by rw [← hk, ← Category.assoc, hr, hk']
  refine quotientTransport_injective ((modulePullbackTriangle B S hS hk').app F) ?_
  rw [h₂, quotientTransport_quotientRestrictOver_modulePullback r hr hk hk' hg, h₁,
    quotientRestrictOver_comp hc rfl hρ hφ' (by rw [Category.assoc, hρ, hφ']),
    quotientRestrictOver_comp hc rfl hφ hg (by rw [Category.assoc, hφ, hg])]
  exact quotientRestrictOver_congr hm.symm _ _ F K

/-! ### Remark 08IT, natural in the test scheme -/

namespace QuotientSituation

variable (D : QuotientSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)

/-- **The identification `X'_T ≅ X_T` of Remark 08IT is natural in the test scheme.** -/
theorem relativeMap_comp_baseChangeFiberIso_hom {T' T : SchemesOver Y'} (h : T' ⟶ T) :
    (D.canonicalBaseChangedSituation p).relativeMap h ≫
        (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T).hom =
      (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T').hom ≫
        D.relativeMap ((CostructuredArrow.map p).map h) := by
  refine baseChange_hom_ext D.f ?_ ?_
  · rw [Category.assoc, Category.assoc, baseChangeFiberIso_hom_comp_sourceProjection,
      baseChangeMap_comp_projection, baseChangeFiberIso_hom_comp_sourceProjection]
    exact baseChangeMap_comp_projection_assoc _ h _
  · rw [Category.assoc, Category.assoc, baseChangeFiberIso_hom_comp_projection,
      baseChangeMap_comp_inclusion, baseChangeFiberIso_hom_comp_projection_assoc]
    exact baseChangeMap_comp_inclusion _ h

/-- **Remark 08IT is natural in the test scheme.**  The bijection between the quotients of
`F_T` and of `F'_T` carries pullback of quotients along a morphism of test schemes over `Y'` to
pullback of quotients. -/
theorem baseChangeSubobjectEquiv_quotientPullback {T' T : SchemesOver Y'} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
        (modulePushforwardCoherence B S hS) T'
        (D.quotientPullback ((CostructuredArrow.map p).map h) K) =
      (D.canonicalBaseChangedSituation p).quotientPullback h
        (D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
          (modulePushforwardCoherence B S hS) T K) :=
  eq_quotientRestrictOver_of_quotientTransport_eq
    ((D.canonicalBaseChangedSituation p).relativeMap h)
    (baseChangeMap_comp_projection _ h) (D.relativeMap ((CostructuredArrow.map p).map h))
    (baseChangeMap_comp_projection _ _) rfl rfl
    (D.baseChangeFiberIso_hom_comp_sourceProjection p
      (D.isQuasicoherentOnSite_baseChangedSourceModule p) T)
    (D.baseChangeFiberIso_hom_comp_sourceProjection p
      (D.isQuasicoherentOnSite_baseChangedSourceModule p) T')
    (D.relativeMap_comp_baseChangeFiberIso_hom p h) D.F K
    (quotientTransport_transportEquiv_modulePullbackSquare _ _ D.F K)
    (quotientTransport_transportEquiv_modulePullbackSquare _ _ D.F _)

/-- **Remark 08IT for the finite-presentation subfunctor, natural in the test scheme.**  The
functor of finitely presented quotients of the base change `F'/X'/Y'` of the situation along
`p : Y' ⟶ Y` is the functor of finitely presented quotients of `F/X/Y` restricted to the test
schemes over `Y'`, the bijection at each test scheme being
`AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsCanonicalBaseChangeEquiv`. -/
def finitePresentationQuotientsFunctorBaseChangeIso :
    (D.canonicalBaseChangedSituation p).finitePresentationQuotientsFunctor ≅
      (CostructuredArrow.map p).op ⋙ D.finitePresentationQuotientsFunctor :=
  (NatIso.ofComponents
    (fun T ↦ (D.finitePresentationQuotientsCanonicalBaseChangeEquiv p T.unop).toIso)
    (fun {T T'} m ↦ by
      ext x
      exact Subtype.ext (D.baseChangeSubobjectEquiv_quotientPullback p m.unop x.1))).symm

/-! ### The change of base to a stage -/

/-- **The change of base to a stage.** The functor `Q^{fp}_{F/X/Y}` is limit preserving as soon
as the functor of finitely presented quotients of the base change `F'/X'/T₀` of the situation to
every affine test scheme `T₀` is. -/
theorem limitPreserving_finitePresentationQuotientsFunctor_of_stages
    (h : ∀ T₀ : SchemesOver D.Y, IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left) →
      LimitPreserving.{u, u + 1, u, u} (D.canonicalBaseChangedSituation T₀.hom).testScheme
        (D.canonicalBaseChangedSituation T₀.hom).finitePresentationQuotientsFunctor) :
    LimitPreserving.{u, u + 1, u, u} D.testScheme D.finitePresentationQuotientsFunctor := by
  intro I _ _ E c hc hE hpt
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  set T₀ := E.obj i₀
  let K : Cone (Over.post E : Over i₀ ⥤ Over T₀) :=
    { pt := Over.mk (c.π.app i₀)
      π :=
        { app := fun A => Over.homMk (c.π.app A.left) (c.w A.hom)
          naturality := fun A A' k => by
            apply Over.OverMorphism.ext
            show 𝟙 c.pt ≫ c.π.app A'.left = c.π.app A.left ≫ E.map k.left
            rw [Category.id_comp, c.w k.left] } }
  let Φ : Over T₀ ⥤ SchemesOver (D.canonicalBaseChangedSituation T₀.hom).Y :=
    D.toHomSituation.overStageSection T₀
  let E' := Over.post E ⋙ Φ
  let c' := Φ.mapCone K
  have hc' : IsLimit ((D.canonicalBaseChangedSituation T₀.hom).testScheme.mapCone c') :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) (D.testScheme.mapCone c)).symm hc
  obtain ⟨hcol⟩ := h T₀ (hE i₀) (Over i₀) E' c' hc' (fun A => hE A.left) hpt
  refine nonempty_isColimit_mapCocone_of_overStage (CostructuredArrow.map T₀.hom)
    (D.finitePresentationQuotientsFunctorBaseChangeIso T₀.hom) E c i₀ E' c'
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.post E) (D.toHomSituation.overStageSectionIso T₀))
    (CostructuredArrow.isoMk (Iso.refl _) ?_) ?_ hcol
  · show (schemeSpaceFunctor B S hS).map (𝟙 _) ≫ c.pt.hom =
      (schemeSpaceFunctor B S hS).map (c.π.app i₀).left ≫ T₀.hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (CostructuredArrow.w (c.π.app i₀)).symm
  · intro A
    refine CostructuredArrow.hom_ext _ _ ?_
    show (c.π.app A.left).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.π.app A.left).left
    rw [Category.comp_id, Category.id_comp]

end QuotientSituation

end AlgebraicGeometry.Space

end
