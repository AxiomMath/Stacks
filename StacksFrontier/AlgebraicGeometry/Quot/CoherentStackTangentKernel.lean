module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackToBase
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace

/-!
# Deformations of `Coh_{X/Y}` in the kernel of the tangent map to `Y`

Let `D` be the situation of Stacks 08KB, `x₀ = (Spec k, g₀, 𝒢₀)` an object of `Coh_{X/Y}` over a
field `k` of finite type over `S`, and `𝓕 ⟶ 𝓖` the `1`-morphism of predeformation categories
induced by the functor `Coh_{X/Y} ⥤ S_Y` forgetting the module. A deformation `x` of `x₀` over
`k[M] = k ⊕ M` whose class has vanishing image in the tangent module of `𝓖` has its point
`Spec k[M] ⟶ Y` factor through `Spec k[M] ⟶ Spec k ⟶ Y`, the first arrow being the spectrum of
`k ⟶ k[M]`: there is a morphism of test schemes `π : T_x ⟶ T₀` whose underlying morphism of
schemes is that spectrum map.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.cohDef` and
  `AlgebraicGeometry.Space.CoherentSituation.baseDef`: the predeformation categories
  `𝓕_{Coh_{X/Y}, k, x₀}` and `𝓕_{Y, k, y₀}`.
* `AlgebraicGeometry.Space.CoherentSituation.cohToBase`: the `1`-morphism between them.
* `AlgebraicGeometry.Space.CoherentSituation.HasTrivialBase`: a deformation over `k[M]` has a
  trivial base when its test scheme maps to that of `x₀` over the spectrum of `k ⟶ k[M]`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.hasTrivialBase_of_tangentMapAt_eq_zero`: a
  deformation over `k[M]` whose class has vanishing image in the tangent module of
  `𝓕_{Y, k, y₀}` has a trivial base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin


universe u

/-- A finite-dimensional `k`-vector space is a `kᵐᵒᵖ`-module through `MulOpposite.unop`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The actions of `k` and `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory

/-- The projection of `Coh_{X/Y}` to the schemes over `S`. -/
abbrev cohQ : CoherentObject D ⥤ Over S :=
  coherentSiteProjection D.categoryData ⋙ Over.post B.inclusion

/-- The projection of `S_Y` to the schemes over `S`. -/
abbrev baseQ : (Stack.fibredCategory B S hS D.Y.1).val.obj ⥤ Over S :=
  (Stack.fibredCategory B S hS D.Y.1).val.p ⋙ Over.post B.inclusion

/-- Forgetting the module and then projecting `S_Y` to the schemes over `S` is the projection of
`Coh_{X/Y}`. -/
theorem toBaseElements_comp_baseQ : D.toBaseElements ⋙ D.baseQ = D.cohQ := rfl

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The predeformation category `𝓕_{Coh_{X/Y}, k, x₀}`. -/
abbrev cohDef : PredeformationConstruction iΛ D.cohQ x₀ hx₀ :=
  predeformationCategory iΛ D.cohQ x₀ hx₀

include hx₀ in
/-- The base point of `S_Y` lies over `Spec k`. -/
theorem baseQ_obj_toBaseElements :
    D.baseQ.obj (D.toBaseElements.obj x₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  imageBasePoint iΛ D.cohQ D.baseQ D.toBaseElements (D.toBaseElements_comp_baseQ) x₀ hx₀

/-- The predeformation category `𝓕_{Y, k, y₀}` of the image of the base point. -/
abbrev baseDef : PredeformationConstruction iΛ D.baseQ (D.toBaseElements.obj x₀)
    (D.baseQ_obj_toBaseElements iΛ x₀ hx₀) :=
  predeformationCategory iΛ D.baseQ (D.toBaseElements.obj x₀)
    (D.baseQ_obj_toBaseElements iΛ x₀ hx₀)

omit D in
/-- The category structure on a predeformation category. -/
abbrev predefCategory {X : Type*} [Category X] (q : X ⥤ Over S) (y₀ : X)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    Category (predeformationCategory iΛ q y₀ hy₀).carrier :=
  (predeformationCategory iΛ q y₀ hy₀).category

attribute [local instance] predefCategory

/-- The `1`-morphism `𝓕_{Coh_{X/Y}, k, x₀} ⟶ 𝓕_{Y, k, y₀}` forgetting the module. -/
abbrev cohToBase :
    BasedFunctor (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      (BasedCategory.ofFunctor (D.baseDef iΛ x₀ hx₀).projection) :=
  (mapPredeformationCategory iΛ D.cohQ D.baseQ D.toBaseElements D.toBaseElements_comp_baseQ x₀
    hx₀).toBasedFunctor

/-- The scheme of the test scheme of a deformation is the spectrum of its algebra. -/
theorem toScheme_deformationPoint (d : DeformationObject iΛ D.cohQ x₀ hx₀) :
    (BigFppfOver.toScheme B S hS).obj d.point.T.left = Spec (CommRingCat.of d.algebra) :=
  congrArg Over.left d.base

include hx₀ in
/-- The scheme of the test scheme of the base point is `Spec k`. -/
theorem toScheme_basePoint :
    (BigFppfOver.toScheme B S hS).obj x₀.T.left = Spec (CommRingCat.of k) :=
  congrArg Over.left hx₀

/-- The underlying morphism of schemes of the base of the arrow of a deformation is the
spectrum of its residue map. -/
theorem toScheme_map_arrow_base (d : DeformationObject iΛ D.cohQ x₀ hx₀) :
    (BigFppfOver.toScheme B S hS).map (D.homOf d.arrow).base.left =
      eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀) ≫
        Spec.map (CommRingCat.ofHom (residueMap d.algebra)) ≫
          eqToHom (D.toScheme_deformationPoint iΛ x₀ hx₀ d).symm := by
  rw [← d.arrow_base]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- The underlying morphism of schemes of the base of a reversed arrow of deformations is the
spectrum of its ring map. -/
theorem toScheme_map_morphism_base {a b : DeformationObject iΛ D.cohQ x₀ hx₀}
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b) :
    (BigFppfOver.toScheme B S hS).map (D.homOf m.arrow).base.left =
      eqToHom (D.toScheme_deformationPoint iΛ x₀ hx₀ b) ≫
        Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          eqToHom (D.toScheme_deformationPoint iΛ x₀ hx₀ a).symm := by
  rw [← m.arrow_base]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- The point of the image under `cohToBase` of an object of `𝓕_{Coh_{X/Y}, k, x₀}` is the image
of its point in `S_Y`. -/
theorem cohToBase_obj_point (a : (D.cohDef iΛ x₀ hx₀).carrier) :
    ((D.baseDef iΛ x₀ hx₀).objects ((D.cohToBase iΛ x₀ hx₀).toFunctor.obj a)).point =
      D.toBaseElements.obj ((D.cohDef iΛ x₀ hx₀).objects a).point := rfl

/-- The image under `cohToBase` of an object of `𝓕_{Coh_{X/Y}, k, x₀}` has the same algebra. -/
theorem cohToBase_obj_algebra (a : (D.cohDef iΛ x₀ hx₀).carrier) :
    ((D.baseDef iΛ x₀ hx₀).objects ((D.cohToBase iΛ x₀ hx₀).toFunctor.obj a)).algebra =
      ((D.cohDef iΛ x₀ hx₀).objects a).algebra := rfl

/-- The point of the source of a reversed arrow of `𝓕_{Y, k, y₀}` is the restriction of the point
of its target along the base of the arrow. -/
theorem baseDef_fiber_eq {a b : DeformationObject iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀)}
    (m : DeformationMorphism iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀) a b) :
    b.point.fiber.as = D.Y.1.map m.arrow.base.op a.point.fiber.as :=
  Discrete.eq_of_hom m.arrow.fiber

/-- The spectrum of the ring map underlying an `eqToHom` of `𝒞_Λ` is an `eqToHom`. -/
theorem spec_map_eqToHom {A A' : ArtinianLocalAlgCat Λ k} (h : A = A') :
    Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
      eqToHom (congrArg (fun A : ArtinianLocalAlgCat Λ k => Spec (CommRingCat.of A))
        h).symm := by
  subst h
  simp only [eqToHom_refl]
  exact Spec.map_id _

/-- A morphism of a predeformation category over an identity has an `eqToHom` as ring map. -/
theorem ringHom_eq_eqToHom_of_isHomLift {X : Type*} [Category X] {q : X ⥤ Over S} {y₀ : X}
    {hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {a b : (predeformationCategory iΛ q y₀ hy₀).carrier}
    (f : a ⟶ b) [(predeformationCategory iΛ q y₀ hy₀).projection.IsHomLift (𝟙 A) f] :
    ((predeformationCategory iΛ q y₀ hy₀).morphisms a b f).ringHom =
      eqToHom ((IsHomLift.domain_eq (predeformationCategory iΛ q y₀ hy₀).projection (𝟙 A) f).trans
        (IsHomLift.codomain_eq (predeformationCategory iΛ q y₀ hy₀).projection (𝟙 A) f).symm) := by
  have h := IsHomLift.fac' (predeformationCategory iΛ q y₀ hy₀).projection (𝟙 A) f
  rwa [Category.id_comp, eqToHom_trans] at h

/-- The base of a reversed arrow of `𝓕_{Y, k, y₀}` read as a morphism of the site, through the
spectrum of its ring map. -/
theorem baseDef_toScheme_map_base {a b : DeformationObject iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀)}
    (m : DeformationMorphism iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀) a b) :
    (BigFppfOver.toScheme B S hS).map m.arrow.base =
      eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          eqToHom (congrArg Over.left a.base).symm := by
  rw [← m.arrow_base]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc,
    Category.id_comp]
  rfl

/-- The base of a reversed arrow of `𝓕_{Y, k, y₀}` over an identity is an `eqToHom`. -/
theorem baseDef_toScheme_map_base_of_eqToHom
    {a b : DeformationObject iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀)}
    (m : DeformationMorphism iΛ D.baseQ (D.toBaseElements.obj x₀)
      (D.baseQ_obj_toBaseElements iΛ x₀ hx₀) a b) (h : a.algebra = b.algebra)
    (hr : m.ringHom = eqToHom h) :
    (BigFppfOver.toScheme B S hS).map m.arrow.base =
      eqToHom (((congrArg Over.left b.base).trans
        (congrArg (fun A : ArtinianLocalAlgCat Λ k => Spec (CommRingCat.of A)) h).symm).trans
          (congrArg Over.left a.base).symm) := by
  rw [D.baseDef_toScheme_map_base iΛ x₀ hx₀ m, hr, spec_map_eqToHom]
  simp only [eqToHom_trans]
  rfl

variable (M : FGModuleCat.{u} k)

/-- The scheme of the test scheme of a deformation over `k[M]` is `Spec k[M]`. -/
theorem toScheme_fiberPoint
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    (BigFppfOver.toScheme B S hS).obj x.1.point.T.left =
      Spec (CommRingCat.of (TrivSqZeroExt k M)) :=
  (D.toScheme_deformationPoint iΛ x₀ hx₀ x.1).trans
    (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of A)) x.2)

/-- A deformation over `k[M]` has a *trivial base* when its test scheme maps to that of `x₀` by
a morphism over `Y` whose underlying morphism of schemes is the spectrum of `k ⟶ k[M]`. -/
def HasTrivialBase
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) : Prop :=
  ∃ π : x.1.point.T ⟶ x₀.T, (BigFppfOver.toScheme B S hS).map π.left =
    eqToHom (D.toScheme_fiberPoint iΛ x₀ hx₀ M x) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
        eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm

/-- Having a trivial base is invariant under isomorphism of the images in the fibre of
`𝓕_{Y, k, y₀}`. -/
theorem hasTrivialBase_of_iso
    (x z : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (e : (fiberFunctor (D.cohToBase iΛ x₀ hx₀)
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj x ≅
      (fiberFunctor (D.cohToBase iΛ x₀ hx₀)
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj z)
    (hz : D.HasTrivialBase iΛ x₀ hx₀ M z) : D.HasTrivialBase iΛ x₀ hx₀ M x := by
  obtain ⟨πz, hπz⟩ := hz
  let f := e.inv.1
  have : (D.baseDef iΛ x₀ hx₀).projection.IsHomLift
      (𝟙 ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) f := e.inv.2
  let m := (D.baseDef iΛ x₀ hx₀).morphisms _ _ f
  have hring := ringHom_eq_eqToHom_of_isHomLift iΛ
    (A := (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) f
  let u : x.1.point.T.left ⟶ z.1.point.T.left := m.arrow.base
  have hfib := D.baseDef_fiber_eq iΛ x₀ hx₀ m
  have hw : yoneda.map u ≫ z.1.point.T.hom.hom = x.1.point.T.hom.hom :=
    yonedaEquiv.injective ((yonedaEquiv_naturality _ _).symm.trans hfib.symm)
  let πx : x.1.point.T ⟶ x₀.T :=
    CostructuredArrow.homMk u (ObjectProperty.hom_ext _ hw) ≫ πz
  refine ⟨πx, ?_⟩
  have hu : (BigFppfOver.toScheme B S hS).map u = _ :=
    D.baseDef_toScheme_map_base_of_eqToHom iΛ x₀ hx₀ m _ hring
  have h1 : (BigFppfOver.toScheme B S hS).map πx.left =
      (BigFppfOver.toScheme B S hS).map u ≫ (BigFppfOver.toScheme B S hS).map πz.left :=
    Functor.map_comp _ _ _
  rw [h1, hπz, hu]
  exact eqToHom_trans_assoc _ _ _

/-- The ring map of the square-zero extension over the residue field object is the inclusion
`k ⟶ k[M]`. -/
theorem squareZeroCrossUnder_residueFieldObject_hom_apply (a : k) :
    (squareZeroCrossUnder.{u, u, u} (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom.hom
      (ULift.up a) =
      algebraMap k (TrivSqZeroExt k M) a := rfl

/-- Having a trivial base, for a deformation object whose algebra is `k[M]`. -/
def HasTrivialBase' (d : DeformationObject iΛ D.cohQ x₀ hx₀)
    (h : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) : Prop :=
  ∃ π : d.point.T ⟶ x₀.T, (BigFppfOver.toScheme B S hS).map π.left =
    eqToHom ((D.toScheme_deformationPoint iΛ x₀ hx₀ d).trans
      (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of A)) h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
        eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm

/-- A deformation over `k[M]` receiving a reversed arrow from an object over the residue field
over the inclusion `k ⟶ k[M]` has a trivial base. -/
theorem hasTrivialBase'_of_morphism (b z : DeformationObject iΛ D.cohQ x₀ hx₀)
    (hb : b.algebra = Deformation.residueFieldObject.{u, u, u} Λ k)
    (hz : z.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ b z)
    (hm : m.ringHom = eqToHom hb ≫ (squareZeroCrossUnder.{u, u, u}
      (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom ≫ eqToHom hz.symm) :
    D.HasTrivialBase' iΛ x₀ hx₀ M z hz := by
  obtain ⟨alb, ptb, arb, basb, abb⟩ := b
  obtain ⟨alz, ptz, arz, basz, abz⟩ := z
  change alb = _ at hb
  change alz = _ at hz
  subst hb hz
  have hr : m.ringHom = (squareZeroCrossUnder.{u, u, u}
      (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom := by
    have e : ∀ {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (p : A = A) (q : A' = A') (g : A ⟶ A'),
        eqToHom p ≫ g ≫ eqToHom q = g := by
      intros
      simp
    exact hm.trans (e _ _ _)
  have hb := D.toScheme_map_morphism_base iΛ x₀ hx₀ m
  have hσ := D.toScheme_map_arrow_base iΛ x₀ hx₀ ⟨_, ptb, arb, basb, abb⟩
  have hres : residueMap (Deformation.residueFieldObject.{u, u, u} Λ k) =
      ULift.ringEquiv.toRingHom := by
    ext a
    rfl
  have hspec : IsIso (Spec.map (CommRingCat.ofHom
      (residueMap (Deformation.residueFieldObject.{u, u, u} Λ k)))) := by
    rw [hres]
    exact inferInstanceAs (IsIso (Spec.map (ULift.ringEquiv (R := k)).toCommRingCatIso.hom))
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map (D.homOf arb).base.left) := by
    rw [hσ]
    infer_instance
  have : IsIso (D.homOf arb).base.left :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  let πb : ptb.T ⟶ x₀.T := CostructuredArrow.homMk (inv (D.homOf arb).base.left) (by
    rw [← CostructuredArrow.w (D.homOf arb).base, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp])
  refine ⟨(D.homOf m.arrow).base ≫ πb, ?_⟩
  have h1 : (BigFppfOver.toScheme B S hS).map ((D.homOf m.arrow).base ≫ πb).left =
      (BigFppfOver.toScheme B S hS).map (D.homOf m.arrow).base.left ≫
        inv ((BigFppfOver.toScheme B S hS).map (D.homOf arb).base.left) := by
    rw [CostructuredArrow.comp_left, Functor.map_comp]
    congr 1
    exact Functor.map_inv _ _
  rw [h1, hb, hr]
  simp only [hσ, IsIso.inv_comp, inv_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have hc : Spec.map (CommRingCat.ofHom (squareZeroCrossUnder.{u, u, u}
      (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
        Spec.map (CommRingCat.ofHom
          (residueMap (Deformation.residueFieldObject.{u, u, u} Λ k))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have key : Spec.map (CommRingCat.ofHom (squareZeroCrossUnder.{u, u, u}
      (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom.hom.toRingHom) ≫
      inv (Spec.map (CommRingCat.ofHom
        (residueMap (Deformation.residueFieldObject.{u, u, u} Λ k)))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) :=
    (IsIso.comp_inv_eq _).2 hc
  exact congrArg (fun t => eqToHom _ ≫ t)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom _) key))

omit D in
/-- The structure map of the square-zero extension of `A` by `M` is that of `A'` precomposed with
`eqToHom h`, for `h : A = A'`. -/
theorem squareZeroCrossUnder_hom_congr {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    (squareZeroCrossUnder.{u, u, u} A M).hom =
      eqToHom h ≫ (squareZeroCrossUnder.{u, u, u} A' M).hom := by
  subst h
  simp

/-- The pushforward to `k[M]` of an object over the residue field has a trivial base. -/
theorem hasTrivialBase_pushforward
    (xb : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      (Deformation.residueFieldObject.{u, u, u} Λ k))
    (P : ChosenPushforwardsAt (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p xb.1) :
    D.HasTrivialBase iΛ x₀ hx₀ M
      (P.obj (squareZeroCrossUnder.{u, u, u}
        ((BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.obj xb.1) M)) := by
  let c := squareZeroCrossUnder.{u, u, u}
    ((BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.obj xb.1) M
  let f := P.inclusion c
  have : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift c.hom f :=
    (P.inclusion_cocartesian c).toIsHomLift
  have h := @IsHomLift.fac' _ _ _ _ (D.cohDef iΛ x₀ hx₀).projection _ _ _ _ c.hom f _
  have hxb : xb.1.algebra = Deformation.residueFieldObject.{u, u, u} Λ k := xb.2
  exact D.hasTrivialBase'_of_morphism iΛ x₀ hx₀ M ((D.cohDef iΛ x₀ hx₀).objects xb.1)
    ((D.cohDef iΛ x₀ hx₀).objects (P.obj c).1) hxb (P.obj c).2
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _ f) (by
      refine h.trans ?_
      have hc := squareZeroCrossUnder_hom_congr (Λ := Λ) M hxb
      have e : ∀ (h₁ : xb.1.algebra = xb.1.algebra) (h₂ : c.right = (P.obj c).1.algebra),
          eqToHom h₁ ≫ c.hom ≫ eqToHom h₂ =
            eqToHom hxb ≫ (squareZeroCrossUnder.{u, u, u}
              (Deformation.residueFieldObject.{u, u, u} Λ k) M).hom ≫ eqToHom (P.obj c).2.symm := by
        intro h₁ h₂
        exact ((congrArg (· ≫ c.hom ≫ eqToHom h₂) (eqToHom_refl _ h₁)).trans
          (Category.id_comp _)).trans ((congrArg (· ≫ eqToHom h₂) hc).trans
            (Category.assoc _ _ _))
      exact e _ _)

/-- A deformation over `k[M]` whose class has vanishing image in the tangent module of
`𝓕_{Y, k, y₀}` has a trivial base. -/
theorem hasTrivialBase_of_tangentMapAt_eq_zero
    (h𝓕 : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection)
    (h𝓖 : IsDeformationCategory.{u, u, u} (D.baseDef iΛ x₀ hx₀).projection)
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (hx : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M
      (tangentClassAt.{u, u, u} _ h𝓕 M x) = 0) :
    D.HasTrivialBase iΛ x₀ hx₀ M x := by
  obtain ⟨E⟩ := h𝓕.predeformation.specialFiber
  let xb := E.inverse.obj ⟨PUnit.unit⟩
  let P := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids h𝓕.predeformation.cofibered xb.1
  have h0 := tangentClassAt_pushforward_eq_zero.{u, u, u}
    (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection) h𝓕 xb.1 P M
  have hz := D.hasTrivialBase_pushforward iΛ x₀ hx₀ M xb P
  have hcl := (tangentMapAt_tangentClassAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M x).symm.trans
    (hx.trans ((map_zero (tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M)).symm.trans
      ((congrArg (tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M) h0.symm).trans
        (tangentMapAt_tangentClassAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M _))))
  obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u, u, u} _ h𝓖 M _ _).1 hcl
  exact D.hasTrivialBase_of_iso iΛ x₀ hx₀ M x _ e hz

end CoherentSituation

end AlgebraicGeometry.Space

end
