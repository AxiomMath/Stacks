module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistSections

/-!
# The squares of the legs of the transitions of the twists, for the chart maps of `θ`

The chart maps of the map `θ` of Tag 07ZG over two charts of `U(ψ)` related by a square commute
with the legs of the transitions of the twists `𝒪(n)` along that square, once the second `θ` is
the transport of the first one (`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`)
and the legs are the comparisons of the twists.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport_of_iso`: the scheme-level
  statement, for modules identified with the twists.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Scheme.Modules (pullback pullbackComp pullbackCongr)

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

section Transport

variable {S₀ S₀' : Scheme.{u}} {A B : SheafGradedAlgebra S₀} {A' B' : SheafGradedAlgebra S₀'}
  (ψ : SheafGradedAlgebraHom A B) (ψ' : SheafGradedAlgebraHom A' B')
  {cA : (relativeProj A').scheme ⟶ (relativeProj A).scheme}
  {cB : (relativeProj B').scheme ⟶ (relativeProj B).scheme}
  (χA : Stacks.RingedSpace.pullbackGradedAlgebra cA.toLRSHom.toShHom (twistAlgebra A) ≅
    twistAlgebra A')
  (χB : Stacks.RingedSpace.pullbackGradedAlgebra cB.toLRSHom.toShHom (twistAlgebra B) ≅
    twistAlgebra B')
  (k : ψ'.relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
  (hr : relativeMapHom ψ' ≫ cA = k ≫ relativeMapHom ψ)
  (hι : k ≫ ψ.relativeMapDomain.ι = ψ'.relativeMapDomain.ι ≫ cB)
  {C P Q C' P' Q' : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q)
  (p : P ⟶ (relativeProj A).scheme) (q : Q ⟶ (relativeProj B).scheme)
  (e : C ⟶ ψ.relativeMapDomain.toScheme) (ha : a ≫ p = e ≫ relativeMapHom ψ)
  (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι) (a' : C' ⟶ P') (b' : C' ⟶ Q')
  (p' : P' ⟶ (relativeProj A').scheme) (q' : Q' ⟶ (relativeProj B').scheme)
  (e' : C' ⟶ ψ'.relativeMapDomain.toScheme) (ha' : a' ≫ p' = e' ≫ relativeMapHom ψ')
  (hb' : b' ≫ q' = e' ≫ ψ'.relativeMapDomain.ι) (j : C' ⟶ C) (yP : P' ⟶ P) (yQ : Q' ⟶ Q)
  (hjA : j ≫ a = a' ≫ yP) (hjB : j ≫ b = b' ≫ yQ) (hyP : yP ≫ p = p' ≫ cA)
  (hyQ : yQ ≫ q = q' ≫ cB)

/-- **The chart maps of `θ` and of its transport commute with the comparisons of modules
identified with the twists**: for modules `M₁`, `N₁`, `M₂`, `N₂` on `P`, `P'`, `Q`, `Q'`
identified with the twists `𝒪(n)` (by `c₁`, `c₁'`, `c₂`, `c₂'`), and maps `α₁ : y_P^*M₁ ⟶ N₁`,
`α₂ : y_Q^*M₂ ⟶ N₂` which are the comparisons of the twists along the squares, the chart map of
`θ' = transport θ` on `C'`, preceded by the leg of `α₁` along `j`, is the pullback along `j` of the
chart map of `θ`, followed by the leg of `α₂`. -/
theorem chartTwistHom_transport_of_iso (hk : e' ≫ k = j ≫ e)
    (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B)))
    (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ').toLRSHom.toShHom
        (twistAlgebra A'))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ'.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B')))
    (hθ' : θ' = transportTwistHom ψ ψ' χA χB k hr hι θ) (n : ℤ) {M₁ : P.Modules}
    {N₁ : P'.Modules} {M₂ : Q.Modules} {N₂ : Q'.Modules}
    (c₁ : M₁ ≅ (pullback p).obj ((twistAlgebra A).piece n))
    (c₁' : N₁ ≅ (pullback p').obj ((twistAlgebra A').piece n))
    (c₂ : M₂ ≅ (pullback q).obj ((twistAlgebra B).piece n))
    (c₂' : N₂ ≅ (pullback q').obj ((twistAlgebra B').piece n))
    (α₁ : (pullback yP).obj M₁ ⟶ N₁) (α₂ : (pullback yQ).obj M₂ ⟶ N₂)
    (ha₁ : α₁ = (pullback yP).map c₁.hom ≫
      (AlgebraicGeometry.Space.pullbackIsoOfSquare p p' yP cA hyP
        (AlgebraicGeometry.Space.gradedPieceIso cA χA n)).hom ≫ c₁'.inv)
    (ha₂ : α₂ = (pullback yQ).map c₂.hom ≫
      (AlgebraicGeometry.Space.pullbackIsoOfSquare q q' yQ cB hyQ
        (AlgebraicGeometry.Space.gradedPieceIso cB χB n)).hom ≫ c₂'.inv) :
    ((pullbackComp j a).hom.app M₁ ≫ (pullbackCongr hjA).hom.app M₁ ≫
        (pullbackComp a' yP).inv.app M₁ ≫ (pullback a').map α₁) ≫
        ((pullback a').map c₁'.hom ≫ chartTwistHom ψ' a' b' p' q' e' ha' hb' θ' n ≫
          (pullback b').map c₂'.inv) =
      (pullback j).map ((pullback a).map c₁.hom ≫ chartTwistHom ψ a b p q e ha hb θ n ≫
          (pullback b).map c₂.inv) ≫
        ((pullbackComp j b).hom.app M₂ ≫ (pullbackCongr hjB).hom.app M₂ ≫
          (pullbackComp b' yQ).inv.app M₂ ≫ (pullback b').map α₂) := by
  subst hθ'
  have T := chartTwistHom_transport ψ ψ' χA χB k hr hι a b p q e ha hb a' b' p' q' e' ha' hb' j
    yP yQ hjA hjB hyP hyQ hk θ n
  have hN₁ : (pullback j).map ((pullback a).map c₁.hom) ≫
      (pullbackComp j a).hom.app ((pullback p).obj ((twistAlgebra A).piece n)) ≫
        (pullbackCongr hjA).hom.app ((pullback p).obj ((twistAlgebra A).piece n)) ≫
        (pullbackComp a' yP).inv.app ((pullback p).obj ((twistAlgebra A).piece n)) =
      (pullbackComp j a).hom.app M₁ ≫ (pullbackCongr hjA).hom.app M₁ ≫
        (pullbackComp a' yP).inv.app M₁ ≫ (pullback a').map ((pullback yP).map c₁.hom) :=
    (pullbackComp j a ≪≫ pullbackCongr hjA ≪≫ (pullbackComp a' yP).symm).hom.naturality c₁.hom
  have hN₂ : (pullback j).map ((pullback b).map c₂.inv) ≫
      (pullbackComp j b).hom.app M₂ ≫ (pullbackCongr hjB).hom.app M₂ ≫
        (pullbackComp b' yQ).inv.app M₂ =
      (pullbackComp j b).hom.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
        (pullbackCongr hjB).hom.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
        (pullbackComp b' yQ).inv.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
        (pullback b').map ((pullback yQ).map c₂.inv) :=
    (pullbackComp j b ≪≫ pullbackCongr hjB ≪≫ (pullbackComp b' yQ).symm).hom.naturality c₂.inv
  rw [ha₁, ha₂]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  have hc : ∀ {Z : C'.Modules}
      (h : (pullback b').obj ((pullback yQ).obj ((pullback q).obj ((twistAlgebra B).piece n))) ⟶ Z),
      (pullback b').map ((pullback yQ).map c₂.inv) ≫ (pullback b').map ((pullback yQ).map c₂.hom) ≫
        h = h := fun h => by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc] at T
  rw [← reassoc_of% hN₁, reassoc_of% hN₂, hc, reassoc_of% T]

end Transport

end Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The legs, written out on the schemes -/

section LegScheme

/-- The leg of a transition along a square, on the schemes. -/
theorem schemeTransitionLeg_hom_hom {U R U' R' : BigFppfOver B S hS} (h : R ⟶ U) (h' : R' ⟶ U')
    (fU : U' ⟶ U) (fR : R' ⟶ R) (hh : h' ≫ fU = fR ≫ h)
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
    (a : quasicoherentPullbackObj B S hS h M ≅ N) :
    (schemeTransitionLeg h h' fU fR hh a).hom.hom =
      (pullbackComp ((BigFppfOver.toScheme B S hS).map h')
          ((BigFppfOver.toScheme B S hS).map fU)).hom.app M.obj ≫
        (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hh)).hom ≫
        (pullbackComp ((BigFppfOver.toScheme B S hS).map fR)
          ((BigFppfOver.toScheme B S hS).map h)).inv.app M.obj ≫
        (pullback ((BigFppfOver.toScheme B S hS).map fR)).map a.hom.hom :=
  rfl

/-- An identification of pullbacks of a quasi-coherent module along equal morphisms of the site
is the identification of the pullbacks along the equal morphisms of schemes. -/
theorem eqToHom_hom_quasicoherentPullbackObj_eq_pullbackCongr {V U : BigFppfOver B S hS}
    {k₁ k₂ : V ⟶ U}
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) (e : k₁ = k₂)
    (h : (BigFppfOver.toScheme B S hS).map k₁ = (BigFppfOver.toScheme B S hS).map k₂) :
    (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) e)).hom =
      (pullbackCongr h).hom.app M.obj := by
  subst e
  rfl

/-- The leg of a transition along a square, on the schemes, with the identification along the
square of morphisms of schemes. -/
theorem schemeTransitionLeg_hom_hom_eq {U R U' R' : BigFppfOver B S hS} (h : R ⟶ U)
    (h' : R' ⟶ U') (fU : U' ⟶ U) (fR : R' ⟶ R) (hh : h' ≫ fU = fR ≫ h)
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
    (a : quasicoherentPullbackObj B S hS h M ≅ N)
    (hh' : (BigFppfOver.toScheme B S hS).map h' ≫ (BigFppfOver.toScheme B S hS).map fU =
      (BigFppfOver.toScheme B S hS).map fR ≫ (BigFppfOver.toScheme B S hS).map h) :
    (schemeTransitionLeg h h' fU fR hh a).hom.hom =
      (pullbackComp ((BigFppfOver.toScheme B S hS).map h')
          ((BigFppfOver.toScheme B S hS).map fU)).hom.app M.obj ≫
        (pullbackCongr hh').hom.app M.obj ≫
        (pullbackComp ((BigFppfOver.toScheme B S hS).map fR)
          ((BigFppfOver.toScheme B S hS).map h)).inv.app M.obj ≫
        (pullback ((BigFppfOver.toScheme B S hS).map fR)).map a.hom.hom := by
  rw [schemeTransitionLeg_hom_hom, eqToHom_hom_quasicoherentPullbackObj_eq_pullbackCongr M hh hh']

/-- The pullback of a morphism of quasi-coherent modules, on the schemes. -/
theorem quasicoherentPullbackMap_hom {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (quasicoherentPullbackMap B S hS g φ).hom =
      (pullback ((BigFppfOver.toScheme B S hS).map g)).map φ.hom :=
  rfl

end LegScheme

namespace RelativeProjHomPoints

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ)

/-! ### The squares of the legs for the chart maps of `θ` -/

section ChartLegs

variable (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj) (n : ℤ)
  {M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre T f)).ringCatSheaf).FullSubcategory}
  (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
  (hp : p = (dP.fibreIso T f).hom)
  (c₁ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf) _ M₁.obj
    ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
  {M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre T f)).ringCatSheaf).FullSubcategory}
  (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
  (hq : q = (dQ.fibreIso T f).hom)
  (c₂ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf) _ M₂.obj
    ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))

/-- The chart map of `θ`, on the schemes. -/
theorem chartTwistMap_hom :
    (hψ.chartTwistMap T f n p hp c₁ q hq c₂).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))).map
          c₁.hom ≫
        Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom (hψ.hom T f)
          ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
          ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
          (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
          (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f)) n ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f))).map
          c₂.inv :=
  rfl

variable {T} {f} (T' : BigFppfOver B S hS) (f' : yoneda.obj T' ⟶ X.obj)
  (t' : hψ.chartObj T' f' ⟶ hψ.chartObj T f) (yP : dP.fibre T' f' ⟶ dP.fibre T f)
  (yQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
  (ht₁ : t' ≫ hψ.chartMapHom T f = hψ.chartMapHom T' f' ≫ yP)
  (ht₂ : t' ≫ hψ.chartIncl T f = hψ.chartIncl T' f' ≫ yQ)
  {N₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre T' f')).ringCatSheaf).FullSubcategory}
  (p' : (BigFppfOver.toScheme B S hS).obj (dP.fibre T' f') ⟶
    (relativeProj (dP.algebra T' f')).scheme)
  (hp' : p' = (dP.fibreIso T' f').hom)
  (c₁' : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T' f')).ringCatSheaf) _ N₁.obj
    ((Scheme.Modules.pullback p').obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T' f')).piece n)))
  {N₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre T' f')).ringCatSheaf).FullSubcategory}
  (q' : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T' f') ⟶
    (relativeProj (dQ.algebra T' f')).scheme)
  (hq' : q' = (dQ.fibreIso T' f').hom)
  (c₂' : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T' f')).ringCatSheaf) _ N₂.obj
    ((Scheme.Modules.pullback q').obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T' f')).piece n)))
  (a₁ : quasicoherentPullbackObj B S hS yP M₁ ≅ N₁)
  (a₂ : quasicoherentPullbackObj B S hS yQ M₂ ≅ N₂)
  {cA : (relativeProj (dP.algebra T' f')).scheme ⟶ (relativeProj (dP.algebra T f)).scheme}
  {cB : (relativeProj (dQ.algebra T' f')).scheme ⟶ (relativeProj (dQ.algebra T f)).scheme}
  (χA : Stacks.RingedSpace.pullbackGradedAlgebra cA.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)) ≅
    Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T' f'))
  (χB : Stacks.RingedSpace.pullbackGradedAlgebra cB.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)) ≅
    Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T' f'))
  (hyP : (BigFppfOver.toScheme B S hS).map yP ≫ p = p' ≫ cA)
  (hyQ : (BigFppfOver.toScheme B S hS).map yQ ≫ q = q' ≫ cB)
  (k : (hψ.hom T' f').relativeMapDomain.toScheme ⟶ (hψ.hom T f).relativeMapDomain.toScheme)
  (hr : relativeMapHom (hψ.hom T' f') ≫ cA = k ≫ relativeMapHom (hψ.hom T f))
  (hι : k ≫ (hψ.hom T f).relativeMapDomain.ι = (hψ.hom T' f').relativeMapDomain.ι ≫ cB)

/-- A functor preserves a commuting square. -/
private theorem map_comp_eq_map_comp_of_comp_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Z} {f' : W ⟶ Y} {g' : Y ⟶ Z}
    (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, h, F.map_comp]

/-- **The chart maps of `θ` commute with the legs of the transitions of the twists**: for a square
`t'` of charts of `U(ψ)` over squares `y_P`, `y_Q` of the charts of `P` and `Q`, comparisons `a₁`,
`a₂` of modules identified with the twists which are the comparisons of the twists along the
squares, and `θ` on the second chart the transport of `θ` on the first (`htr`), the leg of `a₁`
followed by the chart map of `θ` on the second chart is the pullback of the chart map of `θ` on the
first chart followed by the leg of `a₂`. -/
theorem schemeTransitionLeg_hom_comp_chartTwistMap
    (hk : (hψ.chartSchemeIso T' f').hom ≫ k =
      (BigFppfOver.toScheme B S hS).map t' ≫ (hψ.chartSchemeIso T f).hom)
    (ha₁ : a₁.hom.hom = (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map yP)).map
        c₁.hom ≫
      (pullbackIsoOfSquare p p' ((BigFppfOver.toScheme B S hS).map yP) cA hyP
        (gradedPieceIso cA χA n)).hom ≫ c₁'.inv)
    (ha₂ : a₂.hom.hom = (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map yQ)).map
        c₂.hom ≫
      (pullbackIsoOfSquare q q' ((BigFppfOver.toScheme B S hS).map yQ) cB hyQ
        (gradedPieceIso cB χB n)).hom ≫ c₂'.inv)
    (htr : Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T' f') =
      Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom (hψ.hom T f) (hψ.hom T' f') χA χB k
        hr hι (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f))) :
    (schemeTransitionLeg yP t' (hψ.chartMapHom T f) (hψ.chartMapHom T' f') ht₁ a₁).hom ≫
        hψ.chartTwistMap T' f' n p' hp' c₁' q' hq' c₂' =
      quasicoherentPullbackMap B S hS t' (hψ.chartTwistMap T f n p hp c₁ q hq c₂) ≫
        (schemeTransitionLeg yQ t' (hψ.chartIncl T f) (hψ.chartIncl T' f') ht₂ a₂).hom := by
  have hjA := map_comp_eq_map_comp_of_comp_eq (BigFppfOver.toScheme B S hS) ht₁
  have hjB := map_comp_eq_map_comp_of_comp_eq (BigFppfOver.toScheme B S hS) ht₂
  refine ObjectProperty.hom_ext _ ?_
  refine (congrArg₂ (· ≫ ·) (schemeTransitionLeg_hom_hom_eq yP t' _ _ ht₁ a₁ hjA)
    (chartTwistMap_hom hψ T' f' n p' hp' c₁' q' hq' c₂')).trans (Eq.trans ?_
      (congrArg₂ (· ≫ ·) ((quasicoherentPullbackMap_hom t' _).trans
        (congrArg _ (chartTwistMap_hom hψ T f n p hp c₁ q hq c₂)))
        (schemeTransitionLeg_hom_hom_eq yQ t' _ _ ht₂ a₂ hjB)).symm)
  exact Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport_of_iso (hψ.hom T f)
    (hψ.hom T' f') χA χB k hr hι ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom _ _
    ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T' f'))
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T' f')) p' q' (hψ.chartSchemeIso T' f').hom
    _ _ ((BigFppfOver.toScheme B S hS).map t') ((BigFppfOver.toScheme B S hS).map yP)
    ((BigFppfOver.toScheme B S hS).map yQ) hjA hjB hyP hyQ hk
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f))
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T' f')) htr n
    c₁ c₁' c₂ c₂' a₁.hom.hom a₂.hom.hom ha₁ ha₂

/-- The chart `t'` of `U(ψ)`, read on the opens `U(ψ|_T)` of Tag 07ZG: the transport of `r_ψ`. -/
theorem relativeMapHom_comp_of_chartSquare {T T' : BigFppfOver B S hS}
    {f : yoneda.obj T ⟶ X.obj} {f' : yoneda.obj T' ⟶ X.obj}
    (t' : hψ.chartObj T' f' ⟶ hψ.chartObj T f) (yP : dP.fibre T' f' ⟶ dP.fibre T f)
    (ht₁ : t' ≫ hψ.chartMapHom T f = hψ.chartMapHom T' f' ≫ yP)
    (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
    (hp : p = (dP.fibreIso T f).hom)
    (p' : (BigFppfOver.toScheme B S hS).obj (dP.fibre T' f') ⟶
      (relativeProj (dP.algebra T' f')).scheme)
    (hp' : p' = (dP.fibreIso T' f').hom)
    {cA : (relativeProj (dP.algebra T' f')).scheme ⟶ (relativeProj (dP.algebra T f)).scheme}
    (hyP : (BigFppfOver.toScheme B S hS).map yP ≫ p = p' ≫ cA) :
    relativeMapHom (hψ.hom T' f') ≫ cA =
      ((hψ.chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map t' ≫
        (hψ.chartSchemeIso T f).hom) ≫ relativeMapHom (hψ.hom T f) := by
  rw [← cancel_epi (hψ.chartSchemeIso T' f').hom, ← Category.assoc,
    ← hψ.toScheme_map_chartMapHom_comp_of_eq T' f' p' hp', Category.assoc, ← hyP,
    ← Category.assoc, ← Functor.map_comp, ← ht₁, Functor.map_comp, Category.assoc,
    hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The chart `t'` of `U(ψ)`, read on the opens `U(ψ|_T)` of Tag 07ZG: the transport of the
inclusion. -/
theorem comp_ι_of_chartSquare {T T' : BigFppfOver B S hS}
    {f : yoneda.obj T ⟶ X.obj} {f' : yoneda.obj T' ⟶ X.obj}
    (t' : hψ.chartObj T' f' ⟶ hψ.chartObj T f) (yQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (ht₂ : t' ≫ hψ.chartIncl T f = hψ.chartIncl T' f' ≫ yQ)
    (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
    (hq : q = (dQ.fibreIso T f).hom)
    (q' : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T' f') ⟶
      (relativeProj (dQ.algebra T' f')).scheme)
    (hq' : q' = (dQ.fibreIso T' f').hom)
    {cB : (relativeProj (dQ.algebra T' f')).scheme ⟶ (relativeProj (dQ.algebra T f)).scheme}
    (hyQ : (BigFppfOver.toScheme B S hS).map yQ ≫ q = q' ≫ cB) :
    ((hψ.chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map t' ≫
        (hψ.chartSchemeIso T f).hom) ≫ (hψ.hom T f).relativeMapDomain.ι =
      (hψ.hom T' f').relativeMapDomain.ι ≫ cB := by
  rw [← cancel_epi (hψ.chartSchemeIso T' f').hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc (BigFppfOver.toScheme B S hS).map t' ≫ (hψ.chartSchemeIso T f).hom ≫
        (hψ.hom T f).relativeMapDomain.ι
      = (BigFppfOver.toScheme B S hS).map (t' ≫ hψ.chartIncl T f) ≫ q := by
        rw [← hψ.toScheme_map_chartIncl_comp_of_eq T f q hq, Functor.map_comp, Category.assoc]
    _ = (BigFppfOver.toScheme B S hS).map (hψ.chartIncl T' f') ≫ q' ≫ cB := by
        rw [ht₂, Functor.map_comp, Category.assoc, hyQ]
    _ = (hψ.chartSchemeIso T' f').hom ≫ (hψ.hom T' f').relativeMapDomain.ι ≫ cB := by
        rw [← Category.assoc, hψ.toScheme_map_chartIncl_comp_of_eq T' f' q' hq', Category.assoc]

end ChartLegs

end RelativeProjHomPoints

end AlgebraicGeometry.Space

end
