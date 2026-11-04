module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreClassHom
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSurjectiveLocus

/-!
# The classifying map of the 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a point

Let `y : (Sch/V)_{fppf} ⟶ Coh_{X/B}` be a scheme-valued point and `A = y(V)`.  Given an algebraic
space `H` over the test scheme of `A` representing the relative Hom functor `Hom(F_V, 𝒢)` of
Stacks 08JT (as Stacks 08K6 provides), an object of the 2-fibre product
`(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}` over a scheme `T` determines a section of `H` over `T`: the
point corresponding to the surjection `F_T ⟶ y(x)` it carries.  This file defines that section,
proves that it lies in the locus of surjections of
`AlgebraicGeometry.Space.HomSituation.surjLocus`, and that it is compatible with the morphisms
of the 2-fibre product.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.fibrePoint`: the point of `H` attached to an object of
  the 2-fibre product.
* `AlgebraicGeometry.Space.QuotSituation.fibreClassValue`: the section of `H` over the base of
  the object.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.fibreClassValue_map`: the sections attached to the
  objects of the 2-fibre product are compatible with its morphisms.
* `AlgebraicGeometry.Space.QuotSituation.fibreClassValue_mem`: they lie in the locus of
  surjections.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace HomSituation

variable (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)

/-- The action of the relative Hom functor over the algebraic spaces over `X` on a morphism into
a base change preserves surjections. -/
theorem epi_toModuleHom_moduleHomOver_map {T : s.SchemesOver} {Z : Over s.X}
    (m : op Z ⟶ op ((baseChangeOver s.f).obj T))
    (w : (modulePullback B S hS Z.hom).obj s.F ⟶ (modulePullback B S hS Z.hom).obj s.G)
    (hw : Epi w) :
    Epi (s.toModuleHom (ConcreteCategory.hom ((moduleHomOver hc s.F s.G).map m) w)) := by
  have e : s.toModuleHom (ConcreteCategory.hom ((moduleHomOver hc s.F s.G).map m) w) =
      Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) w := by
    rw [moduleHomOver_map]
    rfl
  have := Functor.preservesEpimorphisms_of_adjunction
    (modulePullbackAdjunction B S hS m.unop.left)
  have h2 : Epi (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) w) :=
    (Functor.epi_conjHom_iff _ _).2 (Functor.map_epi _ _)
  rw [e]
  exact h2

/-- **The action of the relative Hom functor along an isomorphism reflects surjections.** -/
theorem epi_of_epi_toModuleHom_moduleHomOver_map {T : s.SchemesOver} {Z : Over s.X}
    (m : op Z ⟶ op ((baseChangeOver s.f).obj T)) [IsIso m.unop.left]
    (w : (modulePullback B S hS Z.hom).obj s.F ⟶ (modulePullback B S hS Z.hom).obj s.G)
    (hw : Epi (s.toModuleHom (ConcreteCategory.hom ((moduleHomOver hc s.F s.G).map m) w))) :
    Epi w := by
  have e : s.toModuleHom (ConcreteCategory.hom ((moduleHomOver hc s.F s.G).map m) w) =
      Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) w := by
    rw [moduleHomOver_map]
    rfl
  rw [e] at hw
  exact epi_of_epi_conjHom_of_isIso hc m.unop.left _ w hw

end HomSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### Surjectivity of the attached maps -/

/-- The pullback of a surjection along a morphism of test schemes and an isomorphism is a
surjection. -/
theorem epi_pullMapOf {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') [IsIso α]
    (v : D.baseChangeModule T ⟶ M) (hv : Epi v) : Epi (D.pullMapOf h α v) := by
  rw [pullMapOf_def]
  have := Functor.preservesEpimorphisms_of_adjunction
    (modulePullbackAdjunction B S hS (D.relativeMap h))
  exact epi_iso_hom_comp_comp_iso_hom ((D.baseChangeComparison h).app D.F) _ (asIso α)
    (Functor.map_epi _ _)

/-- The homomorphism of inverse images attached to a surjection is a surjection. -/
theorem epi_homOfPullMap {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    (v : D.baseChangeModule T' ⟶ M) (hv : Epi v) : Epi (D.homOfPullMap h ψ v) := by
  rw [homOfPullMap_def]
  exact epi_iso_hom_comp_comp_iso_hom ((D.baseChangeComparison h).app D.F).symm v ψ.symm hv

variable {V : BigFppfOver B S hS}
  (y : (Stack.schemeFibredCategory B S hS V).val ⥤ᵇ D.toCoherentSituation.coherentCFG.val)

/-- The map `F_T ⟶ y(x)` attached to an object of the 2-fibre product is a surjection. -/
theorem epi_fibreClassMap (P : (D.fibreProduct y).val.obj) : Epi (D.fibreClassMap y P) := by
  have := (D.fibreIsoHom y P).isIso_fibre
  exact D.epi_pullMapOf _ _ _ (QuotientSituation.epi_quotientProjection _ _ _)

/-! ### The point of a representing space attached to an object -/

variable {H : AlgebraicSpaces B S hS} (p : H ⟶ (D.fibreHomSituation (D.fibreBase y)).base)
  (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
    (D.fibreHomSituation (D.fibreBase y)).homFunctor (modulePushforwardCoherence B S hS))

/-- The test scheme over `y(V)` underlying an object of the 2-fibre product. -/
abbrev fibreTest (P : (D.fibreProduct y).val.obj) : Over (D.fibreBase y).T :=
  Over.mk (D.fibreArrow y P.x).base

/-- The identification of the relative Hom functor of `y(V)` on the test schemes over its test
scheme with the points of a representing space. -/
def fibrePointIso :
    D.fibreHomFunctor (D.fibreBase y) (modulePushforwardCoherence B S hS) ≅
      (D.fibreTestFunctor (D.fibreBase y)).op ⋙ (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}) :=
  D.fibreHomIso (D.fibreBase y) (modulePushforwardCoherence B S hS) ≪≫
    Functor.isoWhiskerLeft (D.fibreTestFunctor (D.fibreBase y)).op c.symm

/-- **The point of `H` attached to an object of the 2-fibre product**: the point corresponding to
the surjection `F_T ⟶ y(x)` it carries. -/
def fibrePoint (P : (D.fibreProduct y).val.obj) :
    spacePointsOverObj p ((D.fibreTestFunctor (D.fibreBase y)).obj (D.fibreTest y P)) :=
  ((D.fibrePointIso y p c).hom.app (op (D.fibreTest y P))
    (D.fibreClassHom y (modulePushforwardCoherence B S hS) P)).down

/-- The points attached to the objects of the 2-fibre product are compatible with its
morphisms. -/
theorem fibrePoint_map {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    (D.fibrePoint y p c P').1 =
      H.1.map ((D.fibreMapHom y m.a).base.left).op (D.fibrePoint y p c P).1 := by
  refine (congrArg (fun z => ((D.fibrePointIso y p c).hom.app (op (D.fibreTest y P')) z).down.1)
    (D.fibreClassHom_map y (modulePushforwardCoherence B S hS) m)).trans ?_
  exact congrArg (fun z => z.down.1)
    (NatTrans.naturality_apply (D.fibrePointIso y p c).hom (D.fibreOverHom y m).op
      (D.fibreClassHom y (modulePushforwardCoherence B S hS) P))

/-- The scheme of the test scheme of `y(x)` is the base of the object. -/
theorem fibreBaseEq (P : (D.fibreProduct y).val.obj) : (y.obj P.x).T.left = P.base :=
  (Functor.congr_obj y.w P.x).trans P.hx

/-- The morphism of schemes underlying `y(a)` for a morphism of the 2-fibre product is its base
morphism. -/
theorem fibreMapHom_base_left {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    (D.fibreMapHom y m.a).base.left =
      eqToHom (D.fibreBaseEq y P') ≫ m.hbase ≫ eqToHom (D.fibreBaseEq y P).symm := by
  have h' : (D.fibreMapHom y m.a).base.left =
      eqToHom (Functor.congr_obj y.w P'.x) ≫ m.a.left ≫
        eqToHom (Functor.congr_obj y.w P.x).symm := Functor.congr_hom y.w m.a
  rw [h', TwoFibreProductOver.Hom.hbase_eq m]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- **The section of `H` attached to an object of the 2-fibre product**, over its base. -/
def fibreClassValue (P : (D.fibreProduct y).val.obj) : H.1.obj (op P.base) :=
  H.1.map (eqToHom (D.fibreBaseEq y P).symm).op (D.fibrePoint y p c P).1

/-- **The sections attached to the objects of the 2-fibre product are compatible with its
morphisms.** -/
theorem fibreClassValue_map {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    D.fibreClassValue y p c P' = H.1.map m.hbase.op (D.fibreClassValue y p c P) := by
  rw [fibreClassValue, fibreClassValue, D.fibrePoint_map y p c m]
  have hcomp : eqToHom (D.fibreBaseEq y P').symm ≫ (D.fibreMapHom y m.a).base.left =
      m.hbase ≫ eqToHom (D.fibreBaseEq y P).symm := by
    rw [D.fibreMapHom_base_left y m]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  calc H.1.map (eqToHom (D.fibreBaseEq y P').symm).op
        (H.1.map ((D.fibreMapHom y m.a).base.left).op (D.fibrePoint y p c P).1)
      = H.1.map (((D.fibreMapHom y m.a).base.left).op ≫ (eqToHom (D.fibreBaseEq y P').symm).op)
          (D.fibrePoint y p c P).1 :=
        (Functor.map_comp_apply H.1 ((D.fibreMapHom y m.a).base.left).op
          (eqToHom (D.fibreBaseEq y P').symm).op _).symm
    _ = H.1.map ((eqToHom (D.fibreBaseEq y P).symm).op ≫ m.hbase.op)
          (D.fibrePoint y p c P).1 := by
        rw [← op_comp, ← op_comp, hcomp]
    _ = H.1.map m.hbase.op (H.1.map (eqToHom (D.fibreBaseEq y P).symm).op
          (D.fibrePoint y p c P).1) :=
        Functor.map_comp_apply H.1 (eqToHom (D.fibreBaseEq y P).symm).op m.hbase.op _

/-- The identification of the two relative Hom functors of `y(V)` at a test scheme over its test
scheme is the action of the relative Hom functor over the algebraic spaces over `X_V` along the
comparison of the two base changes. -/
theorem fibreHomIso_hom_app (A : CoherentObject D.toCoherentSituation) (Z : Over A.T) :
    (D.fibreHomIso A (modulePushforwardCoherence B S hS)).hom.app (op Z) =
      (moduleHomOver (modulePushforwardCoherence B S hS) (D.baseChangeModule A.T) A.F).map
        ((D.fibreRelativeIso A).inv.app Z).op :=
  rfl

/-- The homomorphism of the point attached to an object of the 2-fibre product is the section of
the relative Hom functor attached to it, read on the iterated base change. -/
theorem pointHom_fibrePoint (P : (D.fibreProduct y).val.obj) :
    (D.fibreHomSituation (D.fibreBase y)).pointHom (modulePushforwardCoherence B S hS) p c
        (D.fibrePoint y p c P) =
      (D.fibreHomIso (D.fibreBase y) (modulePushforwardCoherence B S hS)).hom.app
        (op (D.fibreTest y P)) (D.fibreClassHom y (modulePushforwardCoherence B S hS) P) :=
  types_congr_hom (c.inv_hom_id_app (op ((D.fibreTestFunctor (D.fibreBase y)).obj
    (D.fibreTest y P)))) _

/-- The section of the relative Hom functor attached to an object of the 2-fibre product is a
surjection. -/
theorem epi_fibreClassHom (P : (D.fibreProduct y).val.obj) :
    Epi (D.fibreClassHom y (modulePushforwardCoherence B S hS) P) :=
  D.epi_homOfPullMap _ _ _ (D.epi_fibreClassMap y P)

/-- **The point attached to an object of the 2-fibre product lies in the locus of
surjections.** -/
theorem fibrePoint_mem (P : (D.fibreProduct y).val.obj) :
    (D.fibrePoint y p c P).1 ∈
      ((D.fibreHomSituation (D.fibreBase y)).surjLocus (modulePushforwardCoherence B S hS) p
        c).obj (op (D.fibreTest y P).left.left) := by
  refine (D.fibreHomSituation (D.fibreBase y)).mem_surjLocus_of_epi
    (modulePushforwardCoherence B S hS) p c (D.fibrePoint y p c P) ?_
  rw [D.pointHom_fibrePoint y p c P, D.fibreHomIso_hom_app (D.fibreBase y) (D.fibreTest y P)]
  exact (D.fibreHomSituation (D.fibreBase y)).epi_toModuleHom_moduleHomOver_map
    (modulePushforwardCoherence B S hS) _ _ (D.epi_fibreClassHom y P)

/-- **The section attached to an object of the 2-fibre product lies in the locus of
surjections.** -/
theorem fibreClassValue_mem (P : (D.fibreProduct y).val.obj) :
    D.fibreClassValue y p c P ∈
      ((D.fibreHomSituation (D.fibreBase y)).surjLocus (modulePushforwardCoherence B S hS) p
        c).obj (op P.base) :=
  ((D.fibreHomSituation (D.fibreBase y)).surjLocus (modulePushforwardCoherence B S hS) p c).map
    (eqToHom (D.fibreBaseEq y P).symm).op (D.fibrePoint_mem y p c P)

end QuotSituation

end AlgebraicGeometry.Space

end
