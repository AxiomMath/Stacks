module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiReadingMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSourceMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingLaurent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp
public import StacksFrontier.Tactic.HEqCongr

/-!
# The identification `N ≅ (N_Zar)^a` is multiplicative and unital

Let `T` be an object of the big fppf site and `G` a sheaf of graded algebras on the small étale
site of the represented algebraic space `yoneda.obj T` whose pieces are quasi-coherent.  The
identification `G_n ≅ ((G_n)_Zar)^a` of `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`
(Stacks 03DX (2)) is to carry the multiplication and the unit of `G` to the morphisms attached to
those of the Zariski reading of `G`.  Its inverse is the counit of the Zariski reading adjunction,
so both statements transpose along that adjunction, to the values on pure tensors and on `1` of
the transposes of the comparisons of Stacks 03DX (2) with tensor products and with the unit.  This
file proves both statements by that transposition.  These are steps of the proof that `ψ` of
Stacks 084D is a homomorphism of graded algebras.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso_oneHom`: the identification
  `G_0 ≅ ((G_0)_Zar)^a` carries the unit of `G` to the morphism attached to the unit of the
  Zariski reading of `G`.
* `AlgebraicGeometry.Space.oneHom_zariskiReading_eq_homEquiv`: the unit of the Zariski reading is
  the transpose of `(𝒪_T)^a ≅ 𝒪` followed by the reading of the unit.
* `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso_mulSheaf`: the identification
  `G_n ≅ ((G_n)_Zar)^a` carries the multiplication of `G` to the morphism attached to the
  multiplication of the Zariski reading of `G`.
* `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor_counit`: the transpose of the
  comparison of Stacks 03DX (2) with tensor products, followed by the counits, is the comparison
  `AlgebraicGeometry.Space.zariskiReadingTensorHom` of the Zariski reading with tensor products.
* `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor_counit_eq`: the composite of
  the comparison of Stacks 03DX (2) with tensor products and the counits is the left-hand side of
  `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor`, so its transpose is the
  transport of the two lax comparisons.
* `AlgebraicGeometry.SmallEtale.tensorCounitComposite_toZariski_val_app_unit_tmul`: the lax
  comparison of the Zariski restriction sends `x ⊗ y` to `x ⊗ y`.
* `AlgebraicGeometry.RingedSite.HomGeneral.unit_comp_map_pullbackUnitIsoTransport_val_app_one`
  and its instances at the Zariski restriction and at a reindexing: the lax comparisons with the
  unit send `1` to `1`.
* `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_unit`: the transpose of
  `(𝒪_T)^a ≅ 𝒪` splits into the two lax comparisons with the units.
* `AlgebraicGeometry.Space.comp_comp_hom_eq_tensorHom_comp_inv_comp`,
  `AlgebraicGeometry.Space.comp_hom_eq_inv_comp_of_comp_inv`,
  `AlgebraicGeometry.Space.map_comp_counit_app_eq_of_homEquiv`: the abstract reduction of the
  multiplicativity and unitality squares to the transposes.

## Implementation notes

The composite of the comparison of Stacks 03DX (2) with the counits and the left-hand side of
`AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor` are the same morphism spelled
through two readings of the étale structure sheaf; they are identified by `heq_congr`, which
leaves the comparison of the spellings of objects and categories to the kernel.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.RingedSite

section UnitValue

open Stacks.SheafOfModules

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : HomGeneral X Y)
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {L : _root_.SheafOfModules.{w} (Tensor.ringSheaf Y.toRingedTopos.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.toRingedTopos.O)}
  (α : f.toRingedToposHom.toRingedToposModulesHom.pullbackModules ≅ L)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The lax comparison of a presentation of `f_*` with the units takes `1` to `1`.**  Let
`adj : L ⊣ P` present `f^* ⊣ f_*`, with `P` the direct image along the functor of sites of `f` and
`α : f^* ≅ L` carrying the unit of `adj` to the unit of `f^* ⊣ f_*`.  The composite
`𝒪_Y ⟶ P L 𝒪_Y ⟶ P 𝒪_X` of the unit and of Stacks 03LU read through `α` sends the section `1`
to `1`. -/
theorem HomGeneral.unit_comp_map_pullbackUnitIsoTransport_val_app_one
    {φ : Tensor.ringSheaf Y.toRingedTopos.O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj (Tensor.ringSheaf X.toRingedTopos.O)}
    (adj : L ⊣ _root_.SheafOfModules.pushforward.{w} φ)
    (hadj : ∀ (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf Y.toRingedTopos.O))
      (V : Y.Cᵒᵖ) (x : F.val.obj V), (α.inv.app F).val.app (f.u.op.obj V)
        ((adj.unit.app F).val.app V x) =
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposHom.toRingedToposModulesHom).unit.app F).val.app V x)
    (V : Y.Cᵒᵖ) :
    (adj.unit.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.toRingedTopos.O)) ≫
        (_root_.SheafOfModules.pushforward.{w} φ).map
          (pullbackUnitIsoTransport f.toRingedToposHom.toRingedToposModulesHom α).hom).val.app V
        (1 : (Tensor.ringSheaf Y.toRingedTopos.O).obj.obj V) =
      (1 : (Tensor.ringSheaf X.toRingedTopos.O).obj.obj (f.u.op.obj V)) := by
  have h := hadj (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.toRingedTopos.O)) V
    (1 : (Tensor.ringSheaf Y.toRingedTopos.O).obj.obj V)
  have h2 := Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one
    f.toRingedToposHom.toRingedToposModulesHom V
  rw [Adjunction.homEquiv_unit] at h2
  change ((Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      f.toRingedToposHom.toRingedToposModulesHom).inv).val.app (f.u.op.obj V)
    ((α.inv.app _).val.app (f.u.op.obj V) ((adj.unit.app _).val.app V
      (1 : (Tensor.ringSheaf Y.toRingedTopos.O).obj.obj V))) = _
  rw [h]
  exact h2.trans (CategoryTheory.Sheaf.unitTerminalHomEquiv_id_app_apply _ _ _)

end UnitValue

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

section Reindex

universe uu v w

variable {C : Type uu} [Category.{v} C] {C' : Type uu} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J]
  (O : Sheaf J CommRingCat.{w})
  [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J']
  [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']
  [J.HasSheafCompose (forget CommRingCat.{w})] [J'.HasSheafCompose (forget CommRingCat.{w})]

/-- `AlgebraicGeometry.RingedSite.HomGeneral.unit_comp_map_pullbackUnitIsoTransport_val_app_one`
at a reindexing: the unit of the reindexing equivalence followed by the inverse of Stacks 03LU at
the reindexing sends `1` to `1`. -/
theorem unit_comp_map_pullbackUnitIsoTransport_reindex_val_app_one : type_of% (fun V =>
    (reindexRingedSiteHom J' e O).unit_comp_map_pullbackUnitIsoTransport_val_app_one
      (pullbackModulesReindexIso J' e O) (φ := reindexBackSharp e (Tensor.ringSheaf O))
      (reindexEquivalence.{w, w, uu, v, uu, v} e (Tensor.ringSheaf O)).toAdjunction
      (fun F V x => (reindexRingedSiteHom J' e O)
        |>.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit
          (reindexEquivalence.{w, w, uu, v, uu, v} e (Tensor.ringSheaf O)).toAdjunction F V x) V) :=
  fun V => (reindexRingedSiteHom J' e O).unit_comp_map_pullbackUnitIsoTransport_val_app_one
    _ _ (fun F V x => (reindexRingedSiteHom J' e O)
      |>.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit _ F V x) V

end Reindex

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso_inv_app_val_app_unit` with the
modules on the Zariski site read as modules over the ring sheaf of the Zariski ringed site and the
morphism of ringed topoi read from `AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom`: the
form of the unit hypothesis of
`AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite_val_app_unit_tmul`. -/
theorem pullbackModulesToZariskiIso_inv_app_val_app_unit_ringSheaf
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O))
    (V : (S.zariskiRingedSite).Cᵒᵖ) (x : F.val.obj V) :
    ((pullbackModulesToZariskiIso B S hS).inv.app F).val.app
        ((toZariskiRingedSiteHom B S hS).u.op.obj V)
        (((associatedModuleAdjunction B S hS).unit.app F).val.app V x) =
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (toZariskiRingedSiteHom B S hS).toRingedToposHom.toRingedToposModulesHom).unit.app
        F).val.app V x :=
  pullbackModulesToZariskiIso_inv_app_val_app_unit B S hS F V x

/-- `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite_val_app_unit_tmul` at the
Zariski restriction `ε` of a scheme (Stacks 03DU): the lax comparison of the restriction of
modules from the small étale site to the Zariski site sends `x ⊗ y` to `x ⊗ y`. -/
theorem tensorCounitComposite_toZariski_val_app_unit_tmul
    (M N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).toRingedTopos.O))
    (V : (S.zariskiRingedSite).Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (structureMap B S hS)).obj M).val.obj V)
    (y : ((SheafOfModules.pushforward.{u} (structureMap B S hS)).obj N).val.obj V) :
    ((toZariskiRingedSiteHom B S hS).tensorCounitComposite (pullbackModulesToZariskiIso B S hS)
        (φ := structureMap B S hS) (associatedModuleAdjunction B S hS) M N).val.app V
      (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            S.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := S.zariskiRingedSite.toRingedTopos.O.obj)
          ((SheafOfModules.pushforward.{u} (structureMap B S hS)).obj M).val
          ((SheafOfModules.pushforward.{u} (structureMap B S hS)).obj N).val)) V
        (x ⊗ₜ[(S.zariskiRingedSite.toRingedTopos.O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
    _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).toRingedTopos.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS).toRingedTopos.O).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS).toRingedTopos.O.obj)
        M.val N.val))
      ((toZariskiRingedSiteHom B S hS).u.op.obj V)
      (x ⊗ₜ[((smallEtaleRingedSite B S hS).toRingedTopos.O.obj ⋙ forget₂ CommRingCat RingCat).obj
        ((toZariskiRingedSiteHom B S hS).u.op.obj V)] y) :=
  (toZariskiRingedSiteHom B S hS).tensorCounitComposite_val_app_unit_tmul
    (pullbackModulesToZariskiIso B S hS) (φ := structureMap B S hS)
    (associatedModuleAdjunction B S hS)
    (pullbackModulesToZariskiIso_inv_app_val_app_unit_ringSheaf B S hS) M N V x y

/-- `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite_val_app_unit_tmul` at the
Zariski restriction `ε` of a scheme, stated in the spelling of the general statement:
`AlgebraicGeometry.SmallEtale.tensorCounitComposite_toZariski_val_app_unit_tmul` with the objects,
sites and instances read off the instance of the general statement, the form in which the
transposes along the Zariski reading adjunction are evaluated on pure tensors. -/
theorem toZariskiRingedSiteHom_tensorCounitComposite_val_app_unit_tmul : type_of% (fun M N V x y =>
    (toZariskiRingedSiteHom B S hS).tensorCounitComposite_val_app_unit_tmul
      (pullbackModulesToZariskiIso B S hS) (φ := structureMap B S hS)
      (associatedModuleAdjunction B S hS)
      (pullbackModulesToZariskiIso_inv_app_val_app_unit_ringSheaf B S hS) M N V x y) :=
  tensorCounitComposite_toZariski_val_app_unit_tmul B S hS

/-- `AlgebraicGeometry.RingedSite.HomGeneral.unit_comp_map_pullbackUnitIsoTransport_val_app_one`
at the Zariski restriction `ε` of a scheme: the unit of the adjunction of Stacks 03DU followed by
the restriction of Stacks 03LU at `ε` sends `1` to `1`. -/
theorem unit_comp_map_pullbackUnitIsoTransport_toZariski_val_app_one : type_of% (fun V =>
    (toZariskiRingedSiteHom B S hS).unit_comp_map_pullbackUnitIsoTransport_val_app_one
      (pullbackModulesToZariskiIso B S hS) (φ := structureMap B S hS)
      (associatedModuleAdjunction B S hS)
      (pullbackModulesToZariskiIso_inv_app_val_app_unit_ringSheaf B S hS) V) :=
  fun V => (toZariskiRingedSiteHom B S hS).unit_comp_map_pullbackUnitIsoTransport_val_app_one
    _ _ (pullbackModulesToZariskiIso_inv_app_val_app_unit_ringSheaf B S hS) V

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

universe v' u'

section Abstract

/-- **Moving the identifications of a multiplication square across.**  For isomorphisms
`ζA : A ≅ A'`, `ζB : B ≅ B'`, `ζK : K ≅ K'`, `ρ : W ≅ A' ⊗ B'` and `τ : A ⊗ B ≅ Y`, if
`n ≫ ζK⁻¹ = ρ ≫ (ζA⁻¹ ⊗ ζB⁻¹) ≫ τ ≫ μ` then `τ ≫ μ ≫ ζK = (ζA ⊗ ζB) ≫ ρ⁻¹ ≫ n`. -/
theorem comp_comp_hom_eq_tensorHom_comp_inv_comp {D : Type*} [Category D] [MonoidalCategory D]
    {A B K A' B' K' W Y : D} (ζA : A ≅ A') (ζB : B ≅ B') (ζK : K ≅ K') (ρ : W ≅ A' ⊗ B')
    (τ : A ⊗ B ≅ Y) (μ : Y ⟶ K) (n : W ⟶ K')
    (h : n ≫ ζK.inv = ρ.hom ≫ (ζA.inv ⊗ₘ ζB.inv) ≫ τ.hom ≫ μ) :
    τ.hom ≫ μ ≫ ζK.hom = (ζA.hom ⊗ₘ ζB.hom) ≫ ρ.inv ≫ n := by
  rw [(Iso.comp_inv_eq ζK).1 h]
  simp

/-- **The transpose of a multiplication.**  For an adjunction `L ⊣ R`, if the transpose of
`f : L X ⟶ Y` is `c` and `μR = c ≫ R μ`, then `L μR` followed by the counit is `f ≫ μ`. -/
theorem map_comp_counit_app_eq_of_homEquiv {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y K : D} (f : L.obj X ⟶ Y) (μ : Y ⟶ K)
    (c : X ⟶ R.obj Y) (hc : adj.homEquiv X Y f = c) (μR : X ⟶ R.obj K) (hμ : μR = c ≫ R.map μ) :
    L.map μR ≫ adj.counit.app K = f ≫ μ := by
  rw [hμ, ← hc, ← Adjunction.homEquiv_naturality_right]
  simp [Adjunction.homEquiv_unit]

/-- A composite `(F e ≪≫ β ≪≫ γ⁻¹) ≫ γ ≫ x` of an image of an isomorphism under a functor with
two isomorphisms, the last cancelled, is `F e ≫ β ≫ x`. -/
theorem functor_mapIso_trans_trans_symm_hom_comp_hom_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b : C} {c d e : D} (f : a ≅ b) (β : F.obj b ≅ c) (γ : d ≅ c) (x : c ⟶ e) :
    (F.mapIso f ≪≫ β ≪≫ γ.symm).hom ≫ γ.hom ≫ x = F.map f.hom ≫ β.hom ≫ x := by
  simp

/-- The value of a composite of four morphisms of sheaves of modules on a local section, from the
values of its four factors. -/
theorem comp_comp_comp_val_app_eq {C : Type*} {_ : Category C} {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₀ M₁ M₂ M₃ M₄ : SheafOfModules.{u} R} (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂)
    (c : M₂ ⟶ M₃) (d : M₃ ⟶ M₄) (V : Cᵒᵖ) {z₀ : M₀.val.obj V} {z₁ : M₁.val.obj V}
    {z₂ : M₂.val.obj V} {z₃ : M₃.val.obj V} {z₄ : M₄.val.obj V} (ha : a.val.app V z₀ = z₁)
    (hb : b.val.app V z₁ = z₂) (hc : c.val.app V z₂ = z₃) (hd : d.val.app V z₃ = z₄) :
    (a ≫ b ≫ c ≫ d).val.app V z₀ = z₄ := by
  subst ha hb hc hd
  rfl

/-- The value of a morphism of sheaves of modules on a local section, read off an equal
morphism. -/
theorem val_app_eq_of_eq_of_val_app {C : Type*} {_ : Category C} {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f g : M ⟶ N) (h : f = g)
    (V : Cᵒᵖ) {z : M.val.obj V} {z' : N.val.obj V} (hg : g.val.app V z = z') :
    f.val.app V z = z' := by
  subst h
  exact hg

/-- Two morphisms out of the tensor product sheaf of two sheaves of modules over
`Stacks.SheafOfModules.Tensor.ringSheaf O` agreeing on the images of pure tensors are equal: the
form of `PresheafOfModules.tensorSheaf_hom_ext` with the ring sheaf spelled as the tensor products
are. -/
theorem sheafTensor_hom_ext_tmul {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {O : Sheaf J CommRingCat.{u}}
    {F G K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {φ ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G ⟶ K}
    (h : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      φ.val.app V (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)) V
        (x ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      ψ.val.app V (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)) V
        (x ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y))) : φ = ψ :=
  PresheafOfModules.tensorSheaf_hom_ext (Osharp := O) h

/-- The value of the direct image of a morphism of sheaves of modules on a local section over `V`
is the value of the morphism over the image of `V`, read off an equal morphism. -/
theorem pushforward_map_val_app_eq_of_eq {C D : Type*} {_ : Category C} {_ : Category D}
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {Sr : Sheaf J RingCat.{u}} {Rr : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
    {φ : Sr ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj Rr}
    {M N : SheafOfModules.{u} Rr} (f g : M ⟶ N) (h : f = g) (V : Cᵒᵖ)
    {z : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj V}
    {z' : ((SheafOfModules.pushforward.{u} φ).obj N).val.obj V}
    (hg : g.val.app (F.op.obj V) z = z') :
    ((SheafOfModules.pushforward.{u} φ).map f).val.app V z = z' := by
  subst h
  exact hg

/-- `AlgebraicGeometry.Space.sheafTensor_hom_ext_tmul` with the image of the pure tensor named:
the two morphisms are compared on a local section `z` equal to that image. -/
theorem sheafTensor_hom_ext_of_eq_unit {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {O : Sheaf J CommRingCat.{u}}
    {F G K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {φ ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G ⟶ K}
    (h : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V)
      (z : (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).val.obj V),
      z = _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)) V
        (x ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y) →
      φ.val.app V z = ψ.val.app V z) : φ = ψ :=
  sheafTensor_hom_ext_tmul fun V x y => h V x y _ rfl

/-- The tensor product of two morphisms of sheaves of modules over a ringed topos, written as a
whiskering on the right followed by a whiskering on the left, on the image `z` of a pure tensor:
it is the image of the pure tensor of the images. -/
theorem sheafTensor_map_app_comp_obj_map_val_app_unit_tmul
    {X : AlgebraicGeometry.RingedTopos.{v', u', u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A₁ A₂ B₁ B₂ : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : A₁ ⟶ A₂) (g' : B₁ ⟶ B₂) (U : X.Cᵒᵖ) (x : A₁.val.obj U) (y : B₁.val.obj U)
    {z : (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj A₁).obj B₁).val.obj U}
    (hz : z = _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₁.val B₁.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map g).app B₁ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj A₂).map g').val.app U z =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₂.val B₂.val)) U
        (g.val.app U x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] g'.val.app U y) := by
  subst hz
  exact (congrArg
      (fun t => (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj A₂).map g').val.app U t)
    (Stacks.SheafOfModules.sheafTensor_map_app_val_app_unit_tmul_forget₂ g U x y rfl)).trans
    (Stacks.SheafOfModules.sheafTensor_obj_map_val_app_unit_tmul_forget₂ g' U _ y rfl)

/-- **The transpose along a composite adjunction of a composite through the first left adjoint.**
For adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and `ι : R₂ ⋙ R₁ ≅ R`, the transpose of `L₂ t₁ ≫ t₂` along
the composite adjunction is the transpose of `t₁` followed by `R₁` of the transpose of `t₂`,
transported along `ι`. -/
theorem Adjunction.homEquiv_ofNatIsoRight_comp_map_comp {CX CY CZ : Type*} [Category CX]
    [Category CY] [Category CZ] {L₁ : CX ⥤ CY} {R₁ : CY ⥤ CX} (adj₁ : L₁ ⊣ R₁) {L₂ : CY ⥤ CZ}
    {R₂ : CZ ⥤ CY} (adj₂ : L₂ ⊣ R₂) {R : CZ ⥤ CX} (ι : R₂ ⋙ R₁ ≅ R) (adj : L₁ ⋙ L₂ ⊣ R)
    (hadj : adj = (adj₁.comp adj₂).ofNatIsoRight ι) {X : CX} {Y : CY} {Z : CZ}
    (t₁ : L₁.obj X ⟶ Y) (t₂ : L₂.obj Y ⟶ Z) :
    adj.homEquiv X Z (L₂.map t₁ ≫ t₂) =
      (adj₁.unit.app X ≫ R₁.map t₁) ≫ R₁.map (adj₂.unit.app Y ≫ R₂.map t₂) ≫ ι.hom.app Z := by
  subst hadj
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]

/-- The value of a composite of three morphisms of sheaves of modules on a local section, from the
values of its three factors. -/
theorem comp_comp_val_app_eq {C : Type*} {_ : Category C} {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₀ M₁ M₂ M₃ : SheafOfModules.{u} R} (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂)
    (c : M₂ ⟶ M₃) (V : Cᵒᵖ) {z₀ : M₀.val.obj V} {z₁ : M₁.val.obj V}
    {z₂ : M₂.val.obj V} {z₃ : M₃.val.obj V} (ha : a.val.app V z₀ = z₁)
    (hb : b.val.app V z₁ = z₂) (hc : c.val.app V z₂ = z₃) :
    (a ≫ b ≫ c).val.app V z₀ = z₃ := by
  subst ha hb hc
  rfl

/-- **Moving the identifications of a unit square across.**  For isomorphisms `ζ : A ≅ A'` and
`ρ : W ≅ I`, if `n ≫ ζ⁻¹ = ρ ≫ e` then `e ≫ ζ = ρ⁻¹ ≫ n`. -/
theorem comp_hom_eq_inv_comp_of_comp_inv {D : Type*} [Category D] {A A' W I : D}
    (ζ : A ≅ A') (ρ : W ≅ I) (e : I ⟶ A) (n : W ⟶ A') (h : n ≫ ζ.inv = ρ.hom ≫ e) :
    e ≫ ζ.hom = ρ.inv ≫ n := by
  rw [(Iso.comp_inv_eq ζ).1 h]
  simp

/-- Two morphisms out of the free sheaf of modules of rank one agreeing on the section `1` over
every object are equal. -/
theorem sheafOfModules_unit_hom_ext {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} R} {f g : SheafOfModules.unit R ⟶ M}
    (h : ∀ W : Cᵒᵖ, f.val.app W (1 : R.obj.obj W) = g.val.app W (1 : R.obj.obj W)) : f = g :=
  (SheafOfModules.unitHomEquiv M).injective (by ext W; exact h W)

/-- The image of an isomorphism under a functor followed by a second isomorphism, as a composite
of morphisms. -/
theorem functor_mapIso_trans_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b : C} {c : D} (f : a ≅ b) (β : F.obj b ≅ c) :
    (F.mapIso f ≪≫ β).hom = F.map f.hom ≫ β.hom := rfl

/-- The value of a morphism followed by the direct image of a morphism of sheaves of modules on a
local section, from the values of the two factors. -/
theorem comp_pushforward_map_val_app_eq {C D : Type*} {_ : Category C} {_ : Category D}
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {Sr : Sheaf J RingCat.{u}} {Rr : Sheaf K RingCat.{u}} {_ : Functor.IsContinuous F J K}
    {φ : Sr ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj Rr}
    {X : SheafOfModules.{u} Sr} {M N : SheafOfModules.{u} Rr}
    (c : X ⟶ (SheafOfModules.pushforward.{u} φ).obj M) (g : M ⟶ N) (W : Cᵒᵖ)
    {z : X.val.obj W} {y : M.val.obj (F.op.obj W)} (hc : c.val.app W z = y)
    {y' : N.val.obj (F.op.obj W)} (hg : g.val.app (F.op.obj W) y = y') :
    (c ≫ (SheafOfModules.pushforward.{u} φ).map g).val.app W z = y' := by
  subst hc hg
  rfl

/-- The unit morphism `𝒪 ⟶ A_0` of a sheaf of graded algebras sends the local section `1` to the
global unit of `A`. -/
theorem _root_.SheafOfModules.GradedAlgebra.oneHom_val_app_one {C : Type*} {_ : Category C}
    {J : GrothendieckTopology C} {_ : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})}
    {Osharp : Sheaf J CommRingCat.{u}} {_ : J.WEqualsLocallyBijective AddCommGrpCat.{u}}
    {_ : HasWeakSheafify J AddCommGrpCat.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} (Sheaf.toRingCat J Osharp)) (U : Cᵒᵖ) :
    (SheafOfModules.GradedAlgebra.oneHom A).val.app U (1 : (Sheaf.toRingCat J Osharp).obj.obj U) =
      A.one.eval U :=
  (SheafOfModules.GradedAlgebra.oneHom_val_app A U 1).trans (one_smul _ _)

end Abstract

section ZariskiReading

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (T : BigFppfOver B S hS)

/-- The composite of `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` with the
counits of the Zariski reading adjunction is the left-hand side of
`AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor`, read through the naturality
of the monoidal product: its transpose is the transport of the two lax comparisons. -/
theorem zariskiReadingAdjunction_homEquiv_tensor_counit_eq
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    type_of% ((congrArg ((zariskiReadingAdjunction T).homEquiv _ _)
    (((congrArg (fun k => (representedQuasicoherentSchemeTensorIso B S hS T
      (zariskiReadingQcoh T P hP) (zariskiReadingQcoh T Q hQ)).hom ≫ k)
      (modulesTensorObjIso_hom_naturality B S hS ((zariskiReadingAdjunction T).counit.app P)
        ((zariskiReadingAdjunction T).counit.app Q))).trans
    (functor_mapIso_trans_trans_symm_hom_comp_hom_comp _ _ _ _ _)).trans
      (eq_of_heq (by heq_congr)))).trans (zariskiReadingAdjunction_homEquiv_tensor T P Q)) :=
  (congrArg _ (((congrArg _ (modulesTensorObjIso_hom_naturality B S hS _ _)).trans
    (functor_mapIso_trans_trans_symm_hom_comp_hom_comp _ _ _ _ _)).trans
      (eq_of_heq (by heq_congr)))).trans (zariskiReadingAdjunction_homEquiv_tensor T P Q)

/-- **The transpose of the comparison of Stacks 03DX (2) with tensor products is the comparison of
the Zariski reading with tensor products.**  For quasi-coherent `𝒪`-modules `P`, `Q` on the small
étale site of `yoneda.obj T`, the transpose along the Zariski reading adjunction of
`(P_Zar ⊗ Q_Zar)^a ≅ (P_Zar)^a ⊗ (Q_Zar)^a ⟶ P ⊗ Q` (the comparison
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso`, then the counits) is
`AlgebraicGeometry.Space.zariskiReadingTensorHom`. -/
theorem zariskiReadingAdjunction_homEquiv_tensor_counit
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (zariskiReadingAdjunction T).homEquiv _ _
      ((representedQuasicoherentSchemeTensorIso B S hS T (zariskiReadingQcoh T P hP)
          (zariskiReadingQcoh T Q hQ)).hom ≫
        (MonoidalCategoryStruct.tensorHom
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((zariskiReadingAdjunction T).counit.app P)
          ((zariskiReadingAdjunction T).counit.app Q)) ≫
        (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q).hom) =
      zariskiReadingTensorHom B S hS T P Q hP hQ := by
  refine (zariskiReadingAdjunction_homEquiv_tensor_counit_eq T P Q hP hQ).trans ?_
  refine sheafTensor_hom_ext_of_eq_unit
    (O := ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
    (fun V x y z hz => ?_)
  refine Eq.trans ?_ ((congrArg (ConcreteCategory.hom
    ((zariskiReadingTensorHom B S hS T P Q hP hQ).val.app V)) hz).trans
    (zariskiReadingTensorHom_val_app_unit_tmul B S hS T P Q hP hQ V x y)).symm
  apply comp_comp_comp_val_app_eq
  case ha =>
    exact sheafTensor_map_app_comp_obj_map_val_app_unit_tmul
      (X := ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos) _ _ V x y hz
  case hb =>
    apply val_app_eq_of_eq_of_val_app _ _ _ V
      (AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom_tensorCounitComposite_val_app_unit_tmul
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
        _ _ V _ _)
    exact eq_of_heq (by
      unfold AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite
      heq_congr)
  case hc =>
    apply pushforward_map_val_app_eq_of_eq _
      (representedSmallEtaleModuleInverseTensorHom B S hS T P Q)
    · exact eq_of_heq (by
        unfold representedSmallEtaleModuleInverseTensorHom
          AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite
        heq_congr)
    · exact representedSmallEtaleModuleInverseTensorHom_val_app_unit_tmul B S hS T P Q _ _ _
  case hd => rfl

/-- **The identification `N ≅ (N_Zar)^a` is multiplicative.**  For a sheaf of graded algebras `G`
on the represented algebraic space of `T` with quasi-coherent pieces, the identification
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` carries the multiplication of `G` to the
morphism attached by Stacks 03DX (2) to the multiplication of the Zariski reading of `G`
(`AlgebraicGeometry.Space.ZariskiReadingIsoMulCompat`). -/
theorem zariskiReadingQuasicoherentIso_mulSheaf
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))
    (hG : ∀ n, (G.piece n).IsQuasicoherentOnSite) (i j : ℤ) :
    ZariskiReadingIsoMulCompat B S hS T G i j (hG i) (hG j) (hG (i + j))
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf (zariskiReading T G) i j)) := by
  unfold ZariskiReadingIsoMulCompat representedTensorChartMul
  refine comp_comp_hom_eq_tensorHom_comp_inv_comp _ _ _ _ _ _ _ ?_
  exact map_comp_counit_app_eq_of_homEquiv (zariskiReadingAdjunction T) _ _ _
    (zariskiReadingAdjunction_homEquiv_tensor_counit T (G.piece i) (G.piece j) (hG i) (hG j)) _
    (mulSheaf_zariskiReading B S hS T G hG i j)

/-- `AlgebraicGeometry.Space.Adjunction.homEquiv_ofNatIsoRight_comp_map_comp` at the Zariski
reading adjunction and at Stacks 03LU for the associated module and for the comparison of
Stacks 04M0: the transpose of `(𝒪_T)^a ≅ 𝒪` splits into the two lax comparisons with the
units. -/
theorem zariskiReadingAdjunction_homEquiv_unit :
    type_of% (Adjunction.homEquiv_ofNatIsoRight_comp_map_comp
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (R₁ := (SheafOfModules.pushforward.{u}
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property)))
      (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction (zariskiReadingIso T)
      (zariskiReadingAdjunction T) rfl
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSmallEtaleEquivalence B S hS T)
          (representedSchemeCommRingStructureSheaf B S hS T))
        (Stacks.SheafOfModules.pullbackModulesReindexIso
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSmallEtaleEquivalence B S hS T)
          (representedSchemeCommRingStructureSheaf B S hS T))).hom) :=
  Adjunction.homEquiv_ofNatIsoRight_comp_map_comp
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) _ _ (zariskiReadingAdjunction T) rfl
    _ _

/-- **The transpose of `(𝒪_T)^a ≅ 𝒪` sends `1` to `1`.**  The transpose along the Zariski reading
adjunction of `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` sends the section
`1` of the structure sheaf of the Zariski site of the scheme of `T` to `1`. -/
theorem zariskiReadingAdjunction_homEquiv_unitIso_val_app_one
    (W : (((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite).Cᵒᵖ) :
    ((zariskiReadingAdjunction T).homEquiv _ _
        (representedQuasicoherentSchemeUnitIso B S hS T).hom).val.app W
        (1 : ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.obj.obj W) =
      (1 : (representedStructureRingSheaf B S hS T).obj.obj
        ((selfOpensFunctor B S hS T).op.obj W)) := by
  have e : (zariskiReadingAdjunction T).homEquiv _ _
      (representedQuasicoherentSchemeUnitIso B S hS T).hom = _ :=
    (congrArg ((zariskiReadingAdjunction T).homEquiv _ _) (eq_of_heq (by
      unfold representedQuasicoherentSchemeUnitIso
      refine HEq.trans (heq_of_eq (functor_mapIso_trans_hom _ _ _)) ?_
      heq_congr))).trans (zariskiReadingAdjunction_homEquiv_unit T)
  apply val_app_eq_of_eq_of_val_app _ _ e W
  apply comp_comp_val_app_eq
  case ha =>
    apply val_app_eq_of_eq_of_val_app _ _ _ W
      (AlgebraicGeometry.SmallEtale.unit_comp_map_pullbackUnitIsoTransport_toZariski_val_app_one
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property W)
    exact eq_of_heq (by heq_congr)
  case hb =>
    apply pushforward_map_val_app_eq_of_eq _ _ _ W
      (Stacks.SheafOfModules.unit_comp_map_pullbackUnitIsoTransport_reindex_val_app_one
        (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
        (representedSchemeCommRingStructureSheaf B S hS T) _)
    exact eq_of_heq (by heq_congr)
  case hc => rfl

/-- **The unit of the Zariski reading of a graded algebra**: the unit `𝒪 ⟶ (G_Zar)_0` of the
Zariski reading of a sheaf of graded algebras `G` is the transpose of `(𝒪_T)^a ≅ 𝒪` followed by
the reading of the unit of `G`. -/
theorem oneHom_zariskiReading_eq_homEquiv
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T))) :
    SheafOfModules.GradedAlgebra.oneHom (zariskiReading T G) =
      (zariskiReadingAdjunction T).homEquiv _ _
          (representedQuasicoherentSchemeUnitIso B S hS T).hom ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
          (SheafOfModules.GradedAlgebra.oneHom G) := by
  refine sheafOfModules_unit_hom_ext (fun W => ?_)
  refine (SheafOfModules.GradedAlgebra.oneHom_val_app_one (zariskiReading T G) W).trans
    (Eq.symm ?_)
  apply comp_pushforward_map_val_app_eq _ _ W
    (zariskiReadingAdjunction_homEquiv_unitIso_val_app_one T W)
  exact SheafOfModules.GradedAlgebra.oneHom_val_app_one G _

/-- **The identification `N ≅ (N_Zar)^a` is unital.**  For a sheaf of graded algebras `G` on the
represented algebraic space of `T` with quasi-coherent pieces, the identification
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` in degree `0` carries the unit of `G` to
the morphism attached by Stacks 03DX (2) to the unit of the Zariski reading of `G`
(`AlgebraicGeometry.Space.ZariskiReadingIsoOneCompat`). -/
theorem zariskiReadingQuasicoherentIso_oneHom
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))
    (hG : ∀ n, (G.piece n).IsQuasicoherentOnSite) :
    ZariskiReadingIsoOneCompat B S hS T G (hG 0) (SheafOfModules.GradedAlgebra.oneHom G)
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom (zariskiReading T G))) := by
  unfold ZariskiReadingIsoOneCompat representedUnitChartHom
  exact comp_hom_eq_inv_comp_of_comp_inv _ _ _ _
    (map_comp_counit_app_eq_of_homEquiv (zariskiReadingAdjunction T) _ _ _ rfl _
      (oneHom_zariskiReading_eq_homEquiv T G))

end ZariskiReading

end AlgebraicGeometry.Space
