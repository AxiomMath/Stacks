module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorPullback

/-!
# The module attached to the structure sheaf of a scheme chart, and descent of a unit

Let `U` be an object of the big fppf site over `S`.  Stacks 03DX (2) attaches to a quasi-coherent
module `M` on the scheme underlying `U` an `𝒪`-module `M_{yoneda U}` on the representable
algebraic space `yoneda.obj U`,
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`. This file identifies the
module attached to the structure sheaf,

`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}`,

and descends, along a presentation, a morphism out of the structure sheaf attached to a morphism
`u : 𝒪_U ⟶ K` on the scheme of the presentation, given the compatibility of that identification
with inverse images along the two projections.  This is the unit companion of
`AlgebraicGeometry.Space.presentationDescendedMul`.

## Main definitions

* `Stacks.SheafOfModules.pullbackUnitIsoTransport`: the identification `f^*𝒪 ≅ 𝒪` of a morphism of
  ringed topoi, read through an identification of the pullback of modules with another functor.
* `AlgebraicGeometry.Space.quasicoherentUnitObj`: the structure sheaf of the scheme underlying
  `U`, as a quasi-coherent module.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso`: **the module attached to the
  structure sheaf is the structure sheaf.**
* `AlgebraicGeometry.Space.quasicoherentPullbackUnitIso`: `g^*𝒪_U ≅ 𝒪_V` for a morphism of the
  site, as an isomorphism of quasi-coherent modules.
* `AlgebraicGeometry.Space.RepresentedC3UnitCompat`: the compatibility of the identification above
  with inverse images along a morphism of the site.
* `AlgebraicGeometry.Space.representedUnitChartHom`: the morphism `𝒪_{yoneda U} ⟶ K_{yoneda U}`
  attached to `u : 𝒪_U ⟶ K`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.SheafOfModules

universe w w' v u₁ v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  {L : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (α : f.pullbackModules ≅ L)

/-- The identification `f^*𝒪_Y ≅ 𝒪_X` of a morphism of ringed topoi
(`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`), read through an identification
`α` of the pullback of modules along `f` with a functor `L`: `L 𝒪_Y ≅ 𝒪_X`.  It is the unit
companion of `Stacks.SheafOfModules.pullbackTensorIsoTransport`. -/
def pullbackUnitIsoTransport :
    L.obj (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)) ≅
      _root_.SheafOfModules.unit (Tensor.ringSheaf X.O) :=
  α.symm.app _ ≪≫ (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f).symm

end Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

section Abstract

/-- The abstract shape of `AlgebraicGeometry.Space.transitionCommutes_representedUnitChartHom`,
at variables. -/
private theorem transition_unit_of_readings {CU CV : Type*} [Category CU] [Category CV]
    (Pt Ps : CU ⥤ CV) {A1 AK I : CU} {IR Rt1 Rs1 RtK RsK AR1 : CV}
    (Uh : A1 ⟶ I) (Ui : I ⟶ A1) (hU : Ui ≫ Uh = 𝟙 I) (au : A1 ⟶ AK)
    (uIt : Pt.obj I ≅ IR) (uIs : Ps.obj I ≅ IR)
    (ct1 : Pt.obj A1 ⟶ Rt1) (cs1 : Ps.obj A1 ≅ Rs1) (ctK : Pt.obj AK ⟶ RtK)
    (csK : Ps.obj AK ≅ RsK) (UR : AR1 ≅ IR)
    (apt : Rt1 ⟶ AR1) (aps : Rs1 ⟶ AR1) (aps' : AR1 ⟶ Rs1) (hps : aps ≫ aps' = 𝟙 Rs1)
    (at' : Rt1 ⟶ RtK) (as' : Rs1 ⟶ RsK) (aκ : RtK ⟶ RsK)
    (hbt : Pt.map Uh ≫ uIt.hom = ct1 ≫ apt ≫ UR.hom)
    (hbs : Ps.map Uh ≫ uIs.hom = cs1.hom ≫ aps ≫ UR.hom)
    (nt : Pt.map au ≫ ctK = ct1 ≫ at')
    (ns : Ps.map au ≫ csK.hom = cs1.hom ≫ as')
    (hm : apt ≫ aps' ≫ as' = at' ≫ aκ) :
    (uIt.hom ≫ uIs.inv) ≫ Ps.map (Ui ≫ au) = Pt.map (Ui ≫ au) ≫ ctK ≫ aκ ≫ csK.inv := by
  have e1 : uIt.hom = Pt.map Ui ≫ ct1 ≫ apt ≫ UR.hom := by
    rw [← hbt, ← Pt.map_comp_assoc, hU, Pt.map_id, Category.id_comp]
  have e2' : uIs.hom = Ps.map Ui ≫ cs1.hom ≫ aps ≫ UR.hom := by
    rw [← hbs, ← Ps.map_comp_assoc, hU, Ps.map_id, Category.id_comp]
  have e2 : uIs.inv ≫ Ps.map Ui = UR.inv ≫ aps' ≫ cs1.inv := by
    rw [Iso.inv_comp_eq, e2']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hps, Iso.hom_inv_id, Category.comp_id]
  have ns' : cs1.inv ≫ Ps.map au = as' ≫ csK.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% ns, Iso.hom_inv_id, Category.comp_id]
  rw [Ps.map_comp, Pt.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e2, e1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [ns', reassoc_of% hm, reassoc_of% nt]

/-- A functor carries an equation `p⁻¹ ≫ a ≫ k = q⁻¹ ≫ b` to the equation of the images used in
`AlgebraicGeometry.Space.transitionCommutes_representedUnitChartHom`. -/
private theorem map_comp_eq_of_unit_inv_comp_eq {E D : Type*} [Category E] [Category D]
    (G : E ⥤ D) {Pt Ps I Kt Ks : E} (pt : Pt ≅ I) (ps : Ps ≅ I) (mt : Pt ⟶ Kt) (ms : Ps ⟶ Ks)
    (κ : Kt ⟶ Ks) (hm : pt.inv ≫ mt ≫ κ = ps.inv ≫ ms) :
    G.map pt.hom ≫ G.map ps.inv ≫ G.map ms = G.map mt ≫ G.map κ := by
  rw [← G.map_comp, ← G.map_comp, ← G.map_comp, ← hm, Iso.hom_inv_id_assoc]

end Abstract

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the scheme underlying an object `U` of the big fppf site over `S`, as
a quasi-coherent module. -/
abbrev quasicoherentUnitObj (U : BigFppfOver B S hS) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory :=
  ⟨SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf, inferInstance⟩

/-- **The module attached to the structure sheaf of a scheme is the structure sheaf.**  For an
object `U` of the big fppf site over `S`, `(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` on the small étale
site of `yoneda.obj U`, where `(-)_{yoneda U}` is Stacks 03DX (2),
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  Its first factor is the
identification `ε^*𝒪 ≅ 𝒪` of the associated module (Stacks 03LU at `ε`), read through
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` and carried by the comparison of
Stacks 04M0; its second is the identification `f^*𝒪 ≅ 𝒪` at the inverse of that comparison, read
through `Stacks.SheafOfModules.pullbackModulesReindexIso`.  It is the unit companion of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso`. -/
def representedQuasicoherentSchemeUnitIso (U : BigFppfOver B S hS) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (quasicoherentUnitObj B S hS U)).obj ≅
      SheafOfModules.unit (representedStructureRingSheaf B S hS U) :=
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) ≪≫
    Stacks.SheafOfModules.pullbackUnitIsoTransport
      (Stacks.SheafOfModules.reindexRingedToposModulesHom
        (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))
      (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))

/-- **Stacks 03LU for the inverse image along a morphism of the site**: for `g : V ⟶ U`,
`g^*𝒪_U ≅ 𝒪_V` (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` of the underlying morphism
of schemes), as an isomorphism of quasi-coherent modules. -/
def quasicoherentPullbackUnitIso {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    quasicoherentPullbackObj B S hS g (quasicoherentUnitObj B S hS U) ≅
      quasicoherentUnitObj B S hS V :=
  ObjectProperty.isoMk _
    (Scheme.Modules.pullbackUnitIso ((BigFppfOver.toScheme B S hS).map g))

/-- **The identification of Stacks 03DX (2) of the module attached to the structure sheaf is
compatible with inverse images.**  For a morphism `g : V ⟶ U` of the big fppf site, the square

`g^*((𝒪_U)_{yoneda U}) ≅ g^*𝒪_{yoneda U} ≅ 𝒪_{yoneda V}`

and

`g^*((𝒪_U)_{yoneda U}) ≅ (g^*𝒪_U)_{yoneda V} ≅ (𝒪_V)_{yoneda V} ≅ 𝒪_{yoneda V}`

commutes; the first uses `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` on `U`
and Stacks 03LU for the morphism of algebraic spaces, the second the identification
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`, Stacks 03LU on schemes
(`AlgebraicGeometry.Space.quasicoherentPullbackUnitIso`) and
`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` on `V`.  It is the unit companion
of `AlgebraicGeometry.Space.RepresentedC3TensorCompat`. -/
def RepresentedC3UnitCompat {V U : BigFppfOver B S hS} (g : V ⟶ U) : Prop :=
  (modulePullback B S hS (representedSpaceMap B S hS g)).map
      (representedQuasicoherentSchemeUnitIso B S hS U).hom ≫
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).hom =
  (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentUnitObj B S hS U)).hom ≫
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).hom).hom ≫
    (representedQuasicoherentSchemeUnitIso B S hS V).hom

/-- The morphism `𝒪_{yoneda U} ⟶ K_{yoneda U}` attached to a morphism `u : 𝒪_U ⟶ K` of
quasi-coherent modules on the scheme underlying `U`: the inverse of the identification
`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` followed by `u_{yoneda U}`. -/
def representedUnitChartHom {U : BigFppfOver B S hS}
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (u : quasicoherentUnitObj B S hS U ⟶ K) :
    SheafOfModules.unit (representedStructureRingSheaf B S hS U) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj :=
  (representedQuasicoherentSchemeUnitIso B S hS U).inv ≫
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map u).hom

section Concrete

variable {R U : BigFppfOver B S hS} (t s : R ⟶ U)
  {K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  (κ : quasicoherentPullbackObj B S hS t K ⟶ quasicoherentPullbackObj B S hS s K)
  (u : quasicoherentUnitObj B S hS U ⟶ K)

/-- `AlgebraicGeometry.Space.transitionCommutes_representedUnitChartHom` with the attached
transition and the attached morphism written out. -/
private theorem representedUnitChartHom_transition_unfolded
    (hbt : RepresentedC3UnitCompat B S hS t) (hbs : RepresentedC3UnitCompat B S hS s)
    (hm : (quasicoherentPullbackUnitIso B S hS t).inv ≫ quasicoherentPullbackMap B S hS t u ≫ κ =
      (quasicoherentPullbackUnitIso B S hS s).inv ≫ quasicoherentPullbackMap B S hS s u) :
    ((modulePullbackUnitIso B S hS (representedSpaceMap B S hS t)).hom ≫
        (modulePullbackUnitIso B S hS (representedSpaceMap B S hS s)).inv) ≫
      (modulePullback B S hS (representedSpaceMap B S hS s)).map
        ((representedQuasicoherentSchemeUnitIso B S hS U).inv ≫
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map u).hom) =
    (modulePullback B S hS (representedSpaceMap B S hS t)).map
        ((representedQuasicoherentSchemeUnitIso B S hS U).inv ≫
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map u).hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS t K).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS s K).inv :=
  transition_unit_of_readings
    (CU := Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (CV := Modules.{u, u} B S hS (yoneda.obj R)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
    (Pt := modulePullback B S hS (representedSpaceMap B S hS t))
    (Ps := modulePullback B S hS (representedSpaceMap B S hS s))
    (Uh := (representedQuasicoherentSchemeUnitIso B S hS U).hom)
    (Ui := (representedQuasicoherentSchemeUnitIso B S hS U).inv)
    (representedQuasicoherentSchemeUnitIso B S hS U).inv_hom_id
    (au := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map u).hom)
    (uIt := modulePullbackUnitIso B S hS (representedSpaceMap B S hS t))
    (uIs := modulePullbackUnitIso B S hS (representedSpaceMap B S hS s))
    (ct1 := (modulePullbackRepresentedQuasicoherentIso B S hS t
      (quasicoherentUnitObj B S hS U)).hom)
    (cs1 := modulePullbackRepresentedQuasicoherentIso B S hS s (quasicoherentUnitObj B S hS U))
    (ctK := (modulePullbackRepresentedQuasicoherentIso B S hS t K).hom)
    (csK := modulePullbackRepresentedQuasicoherentIso B S hS s K)
    (UR := representedQuasicoherentSchemeUnitIso B S hS R)
    (apt := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
      (quasicoherentPullbackUnitIso B S hS t).hom).hom)
    (aps := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
      (quasicoherentPullbackUnitIso B S hS s).hom).hom)
    (aps' := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
      (quasicoherentPullbackUnitIso B S hS s).inv).hom)
    (congrArg (fun x => x.hom)
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.mapIso
        (quasicoherentPullbackUnitIso B S hS s)).hom_inv_id)
    (at' := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
      (quasicoherentPullbackMap B S hS t u)).hom)
    (as' := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
      (quasicoherentPullbackMap B S hS s u)).hom)
    (aκ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom)
    hbt hbs
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS t u)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS s u)
    (congrArg (fun x => x.hom)
      (map_comp_eq_of_unit_inv_comp_eq (representedQuasicoherentSchemeEquivalence B S hS R).functor
        (quasicoherentPullbackUnitIso B S hS t) (quasicoherentPullbackUnitIso B S hS s)
        (quasicoherentPullbackMap B S hS t u) (quasicoherentPullbackMap B S hS s u) κ hm))

end Concrete

/-- **The attached morphism out of the structure sheaf carries the identification of Stacks 03LU
to the attached transition.**  Let `t s : R ⟶ U` be morphisms of the big fppf site, `(K, κ)` a
quasi-coherent module on the scheme of `U` with `κ : t^*K ⟶ s^*K`, and `u : 𝒪_U ⟶ K` a morphism
carrying `t^*𝒪_U ≅ 𝒪_R ≅ s^*𝒪_U` to `κ`.  If the identification of Stacks 03DX (2) of the
structure sheaf is compatible with inverse images along `t` and `s`, then
`𝒪_{yoneda U} ≅ (𝒪_U)^a ⟶ K^a` carries `t^*𝒪 ≅ 𝒪 ≅ s^*𝒪` (Stacks 03LU for the represented
morphisms) to `κ^a`. -/
theorem transitionCommutes_representedUnitChartHom {R U : BigFppfOver B S hS} (t s : R ⟶ U)
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (κ : quasicoherentPullbackObj B S hS t K ⟶ quasicoherentPullbackObj B S hS s K)
    (u : quasicoherentUnitObj B S hS U ⟶ K)
    (hbt : RepresentedC3UnitCompat B S hS t) (hbs : RepresentedC3UnitCompat B S hS s)
    (hm : (quasicoherentPullbackUnitIso B S hS t).inv ≫ quasicoherentPullbackMap B S hS t u ≫ κ =
      (quasicoherentPullbackUnitIso B S hS s).inv ≫ quasicoherentPullbackMap B S hS s u) :
    TransitionCommutes B S hS
      ((modulePullbackUnitIso B S hS (representedSpaceMap B S hS t)).hom ≫
        (modulePullbackUnitIso B S hS (representedSpaceMap B S hS s)).inv)
      (representedSchemeTransition B S hS t s K κ) (representedUnitChartHom B S hS u) := by
  unfold TransitionCommutes
  exact representedUnitChartHom_transition_unfolded B S hS t s κ u hbt hbs hm

section Descent

attribute [local irreducible] CategoryTheory.yoneda

variable {B S hS} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (κ : quasicoherentPullbackObj B S hS P.target K ⟶ quasicoherentPullbackObj B S hS P.source K)
  (hc : PresentationSchemeCocycle P K κ) (hu : PresentationSchemeUnit P K κ)
  (ν : quasicoherentUnitObj B S hS P.U ⟶ K)
  (hbt : RepresentedC3UnitCompat B S hS P.target)
  (hbs : RepresentedC3UnitCompat B S hS P.source)
  (hm : (quasicoherentPullbackUnitIso B S hS P.target).inv ≫
      quasicoherentPullbackMap B S hS P.target ν ≫ κ =
    (quasicoherentPullbackUnitIso B S hS P.source).inv ≫
      quasicoherentPullbackMap B S hS P.source ν)

include hbt hbs hm in
/-- The attached morphism out of the structure sheaf at a presentation satisfies the hypothesis
of `AlgebraicGeometry.Space.existsUnique_presentationDescendedUnitHom`. -/
theorem transitionCommutes_presentationUnitChartHom :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      ((modulePullbackUnitIso B S hS (presentationGroupoid P).target).hom ≫
        (modulePullbackUnitIso B S hS (presentationGroupoid P).source).inv)
      (presentationSchemeTransition P K κ) (representedUnitChartHom B S hS ν) := by
  exact transitionCommutes_representedUnitChartHom B S hS P.target P.source κ ν hbt hbs hm

/-- **The descended unit**: the morphism `𝒪_X ⟶ D(K)` of `𝒪_X`-modules whose inverse image along
the atlas is `𝒪_U ≅ (𝒪_U)^a ⟶ K^a`, through Stacks 03LU and the chart identification. -/
def presentationDescendedUnit :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (presentationDescendedModule P K κ hc hu).obj :=
  presentationDescendedUnitHom P κ hc hu (representedUnitChartHom B S hS ν)
    (transitionCommutes_presentationUnitChartHom P κ ν hbt hbs hm)

/-- **The inverse image along the atlas of the descended unit is the attached morphism**, through
Stacks 03LU and the chart identification. -/
theorem presentationDescendedUnit_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedUnit P κ hc hu ν hbt hbs hm) ≫
        (presentationDescendedModuleChartIso P K κ hc hu).hom =
      (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫
        representedUnitChartHom B S hS ν :=
  presentationDescendedUnitHom_spec P κ hc hu (representedUnitChartHom B S hS ν)
    (transitionCommutes_presentationUnitChartHom P κ ν hbt hbs hm)

/-- **The descended unit is unique**: a morphism `𝒪_X ⟶ D(K)` whose inverse image along the atlas
is the attached morphism is the descended unit. -/
theorem presentationDescendedUnit_unique
    (ψ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (presentationDescendedModule P K κ hc hu).obj)
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P K κ hc hu).hom =
      (modulePullbackUnitIso B S hS (presentationAtlas P)).hom ≫
        representedUnitChartHom B S hS ν) :
    ψ = presentationDescendedUnit P κ hc hu ν hbt hbs hm :=
  presentationDescendedUnitHom_unique P κ hc hu (representedUnitChartHom B S hS ν)
    (transitionCommutes_presentationUnitChartHom P κ ν hbt hbs hm) ψ hψ

end Descent

end AlgebraicGeometry.Space

end
