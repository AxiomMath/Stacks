module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorAssembly

/-!
# The ninth square of the monoidality chase at the base change of the Zariski reading

`AlgebraicGeometry.Space.zariskiReadingTensorSquareAux` asks, among its eleven squares, for the
compatibility of the base change of the restrictions to the Zariski sites with tensor products:
Stacks 01CD for the morphism of schemes underlying `h : T' ⟶ T` against Stacks 03EL for small
étale base change.  This is
`AlgebraicGeometry.SmallEtale.pullbackTensorIso_restrictModulePullbackObjIso` read in the spelling
of the chase, through `CategoryTheory.Functor.restrictionTensorSquare_transport` and
identifications of the categories, functors, objects and morphisms in their two spellings.

## Main results

* `CategoryTheory.Functor.restrictionTensorSquare_transport`: transport of a square of a
  restriction comparison with tensor products across a change of spelling.
* `AlgebraicGeometry.Space.zariskiReadingTensorSquare_restrictPullbackTensor`: the ninth square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- Transport of a square `τ(a) ≫ b ≫ (c ⊗ d) = e ≫ r(f) ≫ g` of a restriction comparison with
tensor products across a change of spelling of the categories, functors, objects and morphisms. -/
theorem _root_.CategoryTheory.Functor.restrictionTensorSquare_transport
    {Z₁ Z Z'₁ Z' E₁ E : Type _} [iZ₁ : Category Z₁] [iZ : Category Z] [iZ'₁ : Category Z'₁]
    [iZ' : Category Z'] [iE₁ : Category E₁] [iE : Category E]
    {τ₁ : Z₁ ⥤ Z'₁} {τ : Z ⥤ Z'} {T₁ : Z'₁ ⥤ Z'₁ ⥤ Z'₁} {T : Z' ⥤ Z' ⥤ Z'}
    {r₁ : E₁ ⥤ Z'₁} {r : E ⥤ Z'}
    {X₁ Y₁ : Z₁} {U₁ U₁' W₁ W₁' : Z'₁} {P₁ P₁' : E₁} {X Y : Z} {U U' W W' : Z'} {P P' : E}
    {a₁ : X₁ ⟶ Y₁} {b₁ : τ₁.obj Y₁ ⟶ (T₁.obj U₁).obj W₁} {c₁ : U₁ ⟶ U₁'} {d₁ : W₁ ⟶ W₁'}
    {e₁ : τ₁.obj X₁ ⟶ r₁.obj P₁} {f₁ : P₁ ⟶ P₁'} {g₁ : r₁.obj P₁' ⟶ (T₁.obj U₁').obj W₁'}
    {a : X ⟶ Y} {b : τ.obj Y ⟶ (T.obj U).obj W} {c : U ⟶ U'} {d : W ⟶ W'}
    {e : τ.obj X ⟶ r.obj P} {f : P ⟶ P'} {g : r.obj P' ⟶ (T.obj U').obj W'}
    (src : τ₁.map a₁ ≫ b₁ ≫ ((T₁.map c₁).app W₁ ≫ (T₁.obj U₁').map d₁) = e₁ ≫ r₁.map f₁ ≫ g₁)
    (eZ : Z₁ = Z) (eZ' : Z'₁ = Z') (eE : E₁ = E) (hiZ : HEq iZ₁ iZ) (hiZ' : HEq iZ'₁ iZ')
    (hiE : HEq iE₁ iE) (hτ : HEq τ₁ τ) (hT : HEq T₁ T) (hr : HEq r₁ r)
    (hX : HEq X₁ X) (hY : HEq Y₁ Y) (hU : HEq U₁ U) (hU' : HEq U₁' U') (hW : HEq W₁ W)
    (hW' : HEq W₁' W') (hP : HEq P₁ P) (hP' : HEq P₁' P')
    (ha : HEq a₁ a) (hb : HEq b₁ b) (hc : HEq c₁ c) (hd : HEq d₁ d) (he : HEq e₁ e)
    (hf : HEq f₁ f) (hg : HEq g₁ g) :
    τ.map a ≫ b ≫ ((T.map c).app W ≫ (T.obj U').map d) = e ≫ r.map f ≫ g := by
  subst eZ eZ' eE; cases hiZ; cases hiZ'; cases hiE; cases hτ; cases hT; cases hr; cases hX
  cases hY; cases hU; cases hU'; cases hW; cases hW'; cases hP; cases hP'; cases ha; cases hb
  cases hc; cases hd; cases he; cases hf; cases hg; exact src

section
variable (A A' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
      T.left.property).toRingedTopos.O))
  (hA : A.IsQuasicoherentOnSite) (hA' : A'.IsQuasicoherentOnSite)
/-- The restriction of a tensor product sheaf to the Zariski site of the scheme underlying `T`, in
two spellings of the scheme. -/
theorem heq_restrictModule_obj_sheafTensor_obj :
    HEq ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
          T.left.property).toRingedTopos.O).obj A).obj A'))
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
          T.left.property).toRingedTopos.O).obj A).obj A')) := HEq.rfl
/-- The tensor product of two restrictions to the Zariski site of the scheme underlying `T`, in two
spellings of the scheme. -/
theorem heq_sheafTensor_obj_restrictModule_obj :
    HEq (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        T.left.obj.zariskiRingedSite.toRingedTopos.O).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj A)).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj A'))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A)).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A')) := HEq.rfl
/-- The inverse image along the morphism of schemes underlying `h` of a restriction, in the
spellings of Stacks 03DX and of the Zariski reading. -/
theorem heq_pullbackFunctor_obj_restrictModule_obj :
    HEq ((Stacks.RingedSpace.pullbackFunctor (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) h.left).toLRSHom.toShHom).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj A))
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A)) := HEq.rfl
/-- The restriction of a small étale base change to the Zariski site of the scheme underlying `T'`,
in two spellings of the base change. -/
theorem heq_restrictModule_obj_pullback_obj :
    HEq ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        T'.left.obj T'.left.property).obj
      ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj A))
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A)) := HEq.rfl
/-- The small étale base change of a tensor product sheaf, in two spellings of the base change. -/
theorem heq_pullback_obj_sheafTensor_obj :
    HEq ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
          T.left.property).toRingedTopos.O).obj A).obj A'))
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
          T.left.property).toRingedTopos.O).obj A).obj A')) := HEq.rfl
/-- The tensor product of two small étale base changes, in two spellings of the base change. -/
theorem heq_sheafTensor_obj_pullback_obj :
    HEq (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
          T'.left.property).toRingedTopos.O).obj
      ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj A)).obj
      ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj A'))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
          T'.left.property).toRingedTopos.O).obj
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A)).obj
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A')) := HEq.rfl
/-- The base change of a restriction as
`AlgebraicGeometry.Space.zariskiReadingRestrictPullbackIso`. -/
theorem heq_restrictModulePullbackObjIso_hom :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
        (associatedBigEtaleSite B) h.left A hA).hom
      (zariskiReadingRestrictPullbackIso h A hA).hom := HEq.rfl
/-- The base change of the restriction of a tensor product sheaf as
`AlgebraicGeometry.Space.zariskiReadingRestrictPullbackIso`. -/
theorem heq_restrictModulePullbackObjIso_hom_sheafTensor :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
        (associatedBigEtaleSite B) h.left _
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
          (associatedBigEtaleSite B) T.left.obj T.left.property _ _ hA hA')).hom
      (zariskiReadingRestrictPullbackIso h _
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
          (associatedBigEtaleSite B) T.left.obj T.left.property _ _ hA hA')).hom := HEq.rfl
/-- Stacks 03EL for small étale base change as
`AlgebraicGeometry.Space.zariskiReadingEtaleBaseChangeTensorIso`. -/
theorem heq_pullbackTensorIsoTransport_hom_zariskiReadingEtaleBaseChangeTensorIso :
    HEq (Stacks.SheafOfModules.pullbackTensorIsoTransport
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom
        (associatedBigEtaleSite B) h.left)
      (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso
        (associatedBigEtaleSite B) h.left) A A').hom
      (zariskiReadingEtaleBaseChangeTensorIso h A A').hom := HEq.rfl

/-- The inverse image along the morphism of schemes underlying `h`, in the spellings of Stacks 03DX
and of the Zariski reading. -/
theorem heq_pullbackFunctor_schemeHom :
    HEq (Stacks.RingedSpace.pullbackFunctor (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) h.left).toLRSHom.toShHom)
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) := HEq.rfl

/-- The restriction to the Zariski site of the scheme underlying `T'`, in two spellings of the
scheme. -/
theorem heq_restrictModule_toScheme :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T'.left.obj
        T'.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property) := HEq.rfl

/-- The tensor product on the Zariski site of the scheme underlying `T'`, in two spellings of the
scheme. -/
theorem heq_sheafTensor_zariskiRingedSite_toScheme :
    HEq (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        T'.left.obj.zariskiRingedSite.toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O) := HEq.rfl

/-- Stacks 01CD for the morphism of schemes underlying `h`, in the spellings of the module limits
and of the ringed spaces. -/
theorem heq_pullbackTensorIso_hom_comparisonBifunctorIso
    (A A' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O)) :
    HEq (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj A)
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T.left.obj
        T.left.property).obj A')).hom
      ((Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A,
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A')) := HEq.rfl

end

variable (N M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
  (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)

/-- The restriction comparison with tensor products at the inverse images under Stacks 04M0 as
`AlgebraicGeometry.Space.zariskiReadingRestrictTensorIso`. -/
theorem heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso_topos :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        T.left.obj T.left.property ((representedReindexEquivalenceTopos T).inverse.obj N)
        ((representedReindexEquivalenceTopos T).inverse.obj M)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom
    (zariskiReadingRestrictTensorIso T N M hN hM).hom := HEq.rfl


/-- The restriction comparison with tensor products after small étale base change, at the inverse
images under Stacks 04M0, as `AlgebraicGeometry.Space.zariskiReadingRestrictPullbackTensorIso`. -/
theorem heq_restrictModuleTensorIso_hom_zariskiReadingRestrictPullbackTensorIso_inverse :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        T'.left.obj T'.left.property
      ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj
        ((representedReindexEquivalenceTopos T).inverse.obj N))
      ((SheafOfModules.pullback (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
        (associatedBigEtaleSite B) h.left)).obj
        ((representedReindexEquivalenceTopos T).inverse.obj M))
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))).hom
    (zariskiReadingRestrictPullbackTensorIso h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom := HEq.rfl



/-- The ninth square of `AlgebraicGeometry.Space.zariskiReadingTensorSquareAux` from
`AlgebraicGeometry.SmallEtale.pullbackTensorIso_restrictModulePullbackObjIso`, as a function of
the identification of the two restriction comparisons with tensor products after base change. -/
theorem zariskiReadingTensorSquareRestrictPullbackAux : type_of% (fun hg => (
  Functor.restrictionTensorSquare_transport
    (_root_.AlgebraicGeometry.SmallEtale.pullbackTensorIso_restrictModulePullbackObjIso
      (associatedBigEtaleSite B) h.left ((representedReindexEquivalenceTopos T).inverse.obj N)
      ((representedReindexEquivalenceTopos T).inverse.obj M)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl (heq_pullbackFunctor_schemeHom h)
    heq_sheafTensor_zariskiRingedSite_toScheme heq_restrictModule_toScheme
    (heq_restrictModule_obj_sheafTensor_obj _ _) (heq_sheafTensor_obj_restrictModule_obj _ _)
    (heq_pullbackFunctor_obj_restrictModule_obj h _) (heq_restrictModule_obj_pullback_obj h _)
    (heq_pullbackFunctor_obj_restrictModule_obj h _)
    (heq_restrictModule_obj_pullback_obj h _) (heq_pullback_obj_sheafTensor_obj h _ _)
    (heq_sheafTensor_obj_pullback_obj h _ _)
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso_topos N M hN hM)
    (heq_pullbackTensorIso_hom_comparisonBifunctorIso h _ _)
    (heq_restrictModulePullbackObjIso_hom h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))
    (heq_restrictModulePullbackObjIso_hom h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    (heq_restrictModulePullbackObjIso_hom_sheafTensor h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    (heq_pullbackTensorIsoTransport_hom_zariskiReadingEtaleBaseChangeTensorIso h _ _) hg :
      HypothesisOf₁₁_9 (zariskiReadingTensorSquareAux h N M hN hM))) :=
  fun hg => (
  Functor.restrictionTensorSquare_transport
    (_root_.AlgebraicGeometry.SmallEtale.pullbackTensorIso_restrictModulePullbackObjIso
      (associatedBigEtaleSite B) h.left ((representedReindexEquivalenceTopos T).inverse.obj N)
      ((representedReindexEquivalenceTopos T).inverse.obj M)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl (heq_pullbackFunctor_schemeHom h)
    heq_sheafTensor_zariskiRingedSite_toScheme heq_restrictModule_toScheme
    (heq_restrictModule_obj_sheafTensor_obj _ _) (heq_sheafTensor_obj_restrictModule_obj _ _)
    (heq_pullbackFunctor_obj_restrictModule_obj h _) (heq_restrictModule_obj_pullback_obj h _)
    (heq_pullbackFunctor_obj_restrictModule_obj h _)
    (heq_restrictModule_obj_pullback_obj h _) (heq_pullback_obj_sheafTensor_obj h _ _)
    (heq_sheafTensor_obj_pullback_obj h _ _)
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso_topos N M hN hM)
    (heq_pullbackTensorIso_hom_comparisonBifunctorIso h _ _)
    (heq_restrictModulePullbackObjIso_hom h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))
    (heq_restrictModulePullbackObjIso_hom h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    (heq_restrictModulePullbackObjIso_hom_sheafTensor h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    (heq_pullbackTensorIsoTransport_hom_zariskiReadingEtaleBaseChangeTensorIso h _ _) hg :
      HypothesisOf₁₁_9 (zariskiReadingTensorSquareAux h N M hN hM))


/-- The compatibility of the base change of the restrictions with tensor products, Stacks 01CD
for the morphism of schemes against Stacks 03EL for small étale base change: the ninth square. -/
theorem zariskiReadingTensorSquare_restrictPullbackTensor :
    HypothesisOf₁₁_9 (zariskiReadingTensorSquareAux h N M hN hM) :=
  zariskiReadingTensorSquareRestrictPullbackAux h N M hN hM
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictPullbackTensorIso_inverse h N M hN hM)

end AlgebraicGeometry.Space
