module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionPushforwardReflect

/-!
# Deformations of `Coh_{X/Y}` with trivial base over the same algebra

Let `x` and `y` be deformations of `x₀ = (Spec k, g₀, 𝒢₀)` over the same `k[M]` with trivial
base. Their test schemes are the same object `Spec k[M]` over `Y`, and their sections
`Spec k ⟶ Spec k[M]` agree. This file records these identifications, together with the calculus
of the comparisons of Stacks 03LU needed to compose a morphism of `Coh_{X/Y}` with one whose
base is an identification of test schemes: these are the inputs for comparing two such
deformations through their extensions `0 ⟶ 𝒢₀ ⊗ M ⟶ r_*ℱ ⟶ 𝒢₀ ⟶ 0`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.point_T_eq`: the test schemes of two deformations
  over the same algebra with trivial base agree.
* `AlgebraicGeometry.Space.CoherentSituation.comp_mk_eq`: a composite of morphisms of
  `Coh_{X/Y}` from its base and its module comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w' u

local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- A composite of three transports is the transport along the composite equality. -/
theorem CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom_eq {C : Type*} [Category* C] {W X Y Z : C}
    (p : W = X) (q : X = Y) (r : Y = Z) (s : W = Z) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom s := by
  subst p q r
  simp

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

/-- **Two test schemes over `Y` with the same underlying scheme, the same structure morphism to
`S` and maps to a common test scheme with the same underlying morphism of schemes are equal.** -/
theorem schemesOver_eq_of {T T' T₀ : SchemesOver D.Y}
    (e : (BigFppfOver.toScheme B S hS).obj T.left = (BigFppfOver.toScheme B S hS).obj T'.left)
    (hhom : B.inclusion.map T.left.hom = eqToHom e ≫ B.inclusion.map T'.left.hom)
    (π : T ⟶ T₀) (π' : T' ⟶ T₀)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom e ≫ (BigFppfOver.toScheme B S hS).map π'.left) : T = T' := by
  obtain ⟨⟨⟨X, hX⟩, ⟨⟨⟩⟩, h⟩, ⟨⟨⟩⟩, g⟩ := T
  obtain ⟨⟨⟨X', hX'⟩, ⟨⟨⟩⟩, h'⟩, ⟨⟨⟩⟩, g'⟩ := T'
  change X = X' at e
  subst e
  have hh : h = h' := B.inclusion.map_injective (by simpa using hhom)
  subst hh
  have hπl : π.left = π'.left := (BigFppfOver.toScheme B S hS).map_injective (by simpa using hπ)
  have hg : g = g' := by
    have w := CostructuredArrow.w π
    have w' := CostructuredArrow.w π'
    change _ = g at w
    change _ = g' at w'
    rw [← w, ← w', hπl]
  subst hg
  rfl

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The structure morphism to `S` of the test scheme of a deformation. -/
theorem inclusion_map_deformationPoint_hom (d : DeformationObject iΛ D.cohQ x₀ hx₀) :
    B.inclusion.map d.point.T.left.hom =
      eqToHom (D.toScheme_deformationPoint iΛ x₀ hx₀ d) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ iΛ) := by
  have h := Over.w (eqToHom d.base)
  rw [Over.eqToHom_left] at h
  exact h.symm

variable {M : FGModuleCat.{u} k}

/-- **The test schemes of two deformations over the same `k[M]` with trivial base agree.** -/
theorem point_T_eq (a b : DeformationObject iΛ D.cohQ x₀ hx₀)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (πb : b.point.T ⟶ x₀.T)
    (hπb : (BigFppfOver.toScheme B S hS).map πb.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    a.point.T = b.point.T := by
  refine D.schemesOver_eq_of ((D.toScheme_defPoint iΛ x₀ hx₀ M a ha).trans
    (D.toScheme_defPoint iΛ x₀ hx₀ M b hb).symm) ?_ πa πb ?_
  · obtain ⟨ala, pta, ara, basa, aba⟩ := a
    obtain ⟨alb, ptb, arb, basb, abb⟩ := b
    change ala = _ at ha
    change alb = _ at hb
    subst ha hb
    rw [D.inclusion_map_deformationPoint_hom iΛ x₀ hx₀ ⟨_, pta, ara, basa, aba⟩,
      D.inclusion_map_deformationPoint_hom iΛ x₀ hx₀ ⟨_, ptb, arb, basb, abb⟩, eqToHom_trans_assoc]
  · rw [hπa, hπb, eqToHom_trans_assoc]

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- Inverse images along equal morphisms commute with the identification of their values. -/
theorem modulePullback_map_eqToHom {X Y : AlgebraicSpaces B S hS} {i i' : X ⟶ Y} (h : i = i')
    {F F' : Modules.{u, u} B S hS Y.1 Y.2} (θ : F ⟶ F') :
    (modulePullback B S hS i).map θ ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (modulePullback B S hS i').map θ := by
  subst h
  simp

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- The comparison for a composite whose second factor is an identity, followed by the identity
law, is the identification of the inverse images along `h ≫ 𝟙 = h`. -/
theorem compComparison_comp_idComparison_app {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.compComparison h (𝟙 T')).hom.app F ≫ (modulePullback B S hS (D.relativeMap h)).map
        ((D.idComparison (modulePushforwardCoherence B S hS) T').hom.app F) =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  have e := congrArg (fun i => i.hom.app F)
    (comp_idComparison_fac (modulePushforwardCoherence B S hS) D h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at e
  refine (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans (e.trans ?_))
  simp [CoherentSituation.relativeMapComparison]

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- The identity law of Stacks 03LU at a module, with target the module itself. -/
def idApp (T : SchemesOver D.Y) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F :=
  (D.idComparison (modulePushforwardCoherence B S hS) T).hom.app F

omit [CommRing Λ] [Field k] [Algebra Λ k] in
instance (T : SchemesOver D.Y) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    IsIso (D.idApp T F) := by
  unfold idApp
  infer_instance

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- `AlgebraicGeometry.Space.CoherentSituation.compComparison_comp_idComparison_app` through
`AlgebraicGeometry.Space.CoherentSituation.idApp`. -/
theorem compComparison_comp_idApp {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.compComparison h (𝟙 T')).hom.app F ≫ (modulePullback B S hS (D.relativeMap h)).map
        (D.idApp T' F) =
      eqToHom (congrArg (fun g => (modulePullback B S hS (D.relativeMap g)).obj F)
        (Category.comp_id h)) :=
  D.compComparison_comp_idComparison_app h F

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- Inverse images along equal morphisms commute with the identification of their values, the
identification written as a congruence. -/
theorem modulePullback_map_eqToHom_congr {X Y : AlgebraicSpaces B S hS} {i i' : X ⟶ Y}
    (h : i = i') {F F' : Modules.{u, u} B S hS Y.1 Y.2} (θ : F ⟶ F') :
    (modulePullback B S hS i).map θ ≫
        eqToHom (congrArg (fun g => (modulePullback B S hS g).obj F') h) =
      eqToHom (congrArg (fun g => (modulePullback B S hS g).obj F) h) ≫
        (modulePullback B S hS i').map θ := by
  subst h
  simp

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- **A composite of morphisms of `Coh_{X/Y}` from its base and its module comparison**, for a
second factor given by its base `nb` and its module comparison `nf`. -/
theorem comp_mk_eq {A C C' : CoherentObject D} (m : CoherentHom A C') (nb : C'.T ⟶ C.T)
    (nf : (modulePullback B S hS (D.relativeMap nb)).obj C.F ⟶ C'.F) [IsIso nf]
    (p : CoherentHom A C) (hb : m.base ≫ nb = p.base)
    (hf : eqToHom (congrArg (fun g => (modulePullback B S hS (D.relativeMap g)).obj C.F)
        hb.symm) ≫ (D.compComparison m.base nb).hom.app C.F ≫
          (modulePullback B S hS (D.relativeMap m.base)).map nf ≫ m.fibre = p.fibre) :
    m.comp ⟨nb, nf, inferInstance⟩ = p := by
  obtain ⟨pb, pf, pi⟩ := p
  change m.base ≫ nb = pb at hb
  subst hb
  change eqToHom rfl ≫ _ = pf at hf
  rw [eqToHom_refl, Category.id_comp] at hf
  subst hf
  have h0 : (m.comp ⟨nb, nf, inferInstance⟩).fibre =
      (D.compComparison m.base nb).hom.app C.F ≫
        (modulePullback B S hS (D.relativeMap m.base)).map nf ≫ m.fibre := by
    dsimp only [CoherentHom.comp]
    rfl
  refine CoherentHom.ext rfl ?_
  exact (eqToHom_self_comp _ _).trans h0

/-- The base change of `X` along a morphism of test schemes between affine ones is affine. -/
theorem isAffineHom_relativeMap {T T' : SchemesOver D.Y} (g : T ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)] :
    IsAffineHom B S hS (D.relativeMap g).hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _
    (isPullback_baseChangeMap D.f g).flip) (isAffineHom_yoneda_map B S hS g.left)

/-- **The sections of two deformations over `k[M]` with the same test scheme agree.** -/
theorem homOf_arrow_base_eq (a b : DeformationObject iΛ D.cohQ x₀ hx₀)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hT : b.point.T = a.point.T) :
    (D.homOf b.arrow).base = (D.homOf a.arrow).base ≫ eqToHom hT.symm := by
  have := D.isAffine_fiberPoint iΛ x₀ hx₀ M b hb
  refine CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective
    (ext_of_isAffine ?_))
  change siteΓ (D.homOf b.arrow).base.left =
    siteΓ ((D.homOf a.arrow).base.left ≫ (eqToHom hT.symm : a.point.T ⟶ b.point.T).left)
  rw [siteΓ_comp]
  ext t
  obtain ⟨y, rfl⟩ := (D.fiberRingEquiv iΛ x₀ hx₀ M b hb).surjective t
  rw [D.siteΓ_fiberSection iΛ x₀ hx₀ M b hb]
  obtain ⟨ala, pta, ara, basa, aba⟩ := a
  obtain ⟨alb, ⟨Tb, Fb, qb, fb, flb, pb⟩, arb, basb, abb⟩ := b
  change Tb = pta.T at hT
  subst hT
  change _ = (siteΓ (D.homOf ara).base.left).hom ((siteΓ (𝟙 pta.T.left)).hom
    (D.fiberRingEquiv iΛ x₀ hx₀ M ⟨alb, ⟨pta.T, Fb, qb, fb, flb, pb⟩, arb, basb, abb⟩ hb y))
  rw [siteΓ_id]
  exact (D.siteΓ_fiberSection iΛ x₀ hx₀ M ⟨ala, pta, ara, basa, aba⟩ ha y).symm

end CoherentSituation

end AlgebraicGeometry.Space

end
