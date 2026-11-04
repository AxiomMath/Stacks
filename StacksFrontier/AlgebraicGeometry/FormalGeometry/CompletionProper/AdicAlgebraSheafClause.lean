module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicUnitFromSystem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraDataAssembly

/-!
# Pullbacks of the algebra sheaf of module-algebra data

Let `E` be a module on a scheme `W''` carrying a `Stacks.FundamentalGroup.ModuleAlgebraData d`
whose multiplication comes from a morphism `μ` out of the sheafified tensor square of `E`, let
`g : W ⟶ W''`, and let `F` be an algebra sheaf on `W` with an isomorphism `ε : g^*E ⟶ F` of
modules compatible with the multiplications and units. Then the composite

  `θ.iso.hom ≫ g^*(algebraSheafOfModuleIso E d).hom ≫ ε`,

where `θ` identifies the module underlying an algebra pullback with the module pullback, is an
isomorphism of algebra sheaves `(algebraPullback g).obj (algebraSheafOfModule E d) ≅ F`. Applied
to an adic system of algebra sheaves `B n` on the thickenings `Xₙ`, this gives module-algebra data
on the algebraization whose algebra sheaf pulls back to `B n` along `vₙ : Xₙ ⟶ X` for every `n`.

## Main results

* `AlgebraicGeometry.multiplication_algebraSheafOfModule_comp_iso_hom` and
  `AlgebraicGeometry.unitModuleMap_algebraSheafOfModule_comp_iso_hom`: the identification of the
  module underlying `algebraSheafOfModule E d` with `E` carries the multiplication of that algebra
  sheaf to `μ`, and its structure morphism to `d.unit`.
* `AlgebraicGeometry.multiplication_comp_algebraPullbackCompare` and
  `AlgebraicGeometry.unitModuleMap_comp_algebraPullbackCompare`: the composite
  `θ.iso.hom ≫ g^*(ι.hom) ≫ ε` is multiplicative and unital.
* `AlgebraicGeometry.nonempty_algebraPullback_algebraSheafOfModule_iso`: the pullback of
  `algebraSheafOfModule E d` along `g` is isomorphic to `F` as an algebra sheaf.
* `AlgebraicGeometry.exists_moduleAlgebraData_algebraPullback_of_adicAlgebraModuleSystem`: the
  algebraization of an adic system of algebra sheaves carries module-algebra data whose algebra
  sheaf pulls back to the `n`-th algebra sheaf of the system for every `n`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication unitModuleMap mulSection oneSection
  multiplication_tmul multiplication_comp_tmul tensorSheafMap_comp_tmul unitModuleMap_one
  unitModuleMap_comp_one homOfMultiplicative underlyingModuleMap_homOfMultiplicative)
open Stacks.AffineAlgebraEquivalence (algebraPullback)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  hom_ext_toTensorSheafSection tensorSheafMap_app_toTensorSheafSection
  tensorSheafMap_comp)
open Stacks.FundamentalGroup (ModuleAlgebraData algebraSheafOfModule algebraSheafOfModuleIso
  isIso_of_isIso_underlyingModuleMap)
open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso
  schemePullbackTensorIso_tensorSheafMap_hom)
open Stacks.SheafOfModules (comp_val_app_apply)

universe u

namespace AlgebraicGeometry

attribute [local instance] moduleOnSectionsAtSchemePresheaf

/-! ### The two section-level identities about `algebraSheafOfModuleIso` -/

/-- If `d.mul` is `AlgebraicGeometry.mulPresheafOfHom E μ`, then `d.mul` sends a local tensor `t`
to `μ` applied to the section of the sheafified tensor square defined by `t`. -/
public theorem mul_app_of_mulPresheafOfHom {Y : Scheme.{u}} (E : Y.Modules)
    (d : ModuleAlgebraData E)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (hdmul : d.mul = mulPresheafOfHom E μ) (U : (Y.Opens)ᵒᵖ)
    (t : TensorProduct (Y.presheaf.obj U) (E.val.obj U) (E.val.obj U)) :
    PresheafOfModules.Hom.app d.mul U t =
      (μ.val.app U).hom (toTensorSheafSection Y.toRingedSpace E E U t) :=
  (congrArg (fun k : PresheafOfModules.Hom _ _ => PresheafOfModules.Hom.app k U t) hdmul).trans
    (mulPresheafOfHom_app E μ U t)

/-- If `d.mul` comes from a morphism `μ` out of the sheafified tensor square of `E`, then
`Stacks.FundamentalGroup.algebraSheafOfModuleIso` carries the multiplication of
`Stacks.FundamentalGroup.algebraSheafOfModule E d` to `μ`. -/
public theorem multiplication_algebraSheafOfModule_comp_iso_hom {Y : Scheme.{u}} (E : Y.Modules)
    (d : ModuleAlgebraData E)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (hdmul : d.mul = mulPresheafOfHom E μ) :
    multiplication (algebraSheafOfModule E d) ≫ (algebraSheafOfModuleIso E d).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).map
        (((algebraSheafOfModuleIso E d).hom, (algebraSheafOfModuleIso E d).hom) :
          (_, _) ⟶ (_, _))) ≫ μ := by
  refine hom_ext_toTensorSheafSection Y.toRingedSpace _ _ fun U x y => ?_
  refine (multiplication_comp_tmul (algebraSheafOfModuleIso E d).hom U x y).trans ?_
  refine Eq.trans ?_ (comp_val_app_apply _ _ U _).symm
  refine Eq.trans ?_ (congrArg (fun z => (μ.val.app U).hom z)
    (tensorSheafMap_app_toTensorSheafSection Y.toRingedSpace
      (AlgebraSheaf.underlyingModule (algebraSheafOfModule E d))
      (AlgebraSheaf.underlyingModule (algebraSheafOfModule E d)) E E
      (algebraSheafOfModuleIso E d).hom (algebraSheafOfModuleIso E d).hom U.unop x y).symm)
  exact mul_app_of_mulPresheafOfHom E d μ hdmul U _

/-- `Stacks.FundamentalGroup.algebraSheafOfModuleIso` carries the structure morphism of
`Stacks.FundamentalGroup.algebraSheafOfModule E d` to `d.unit`. -/
public theorem unitModuleMap_algebraSheafOfModule_comp_iso_hom {Y : Scheme.{u}} (E : Y.Modules)
    (d : ModuleAlgebraData E) :
    unitModuleMap (algebraSheafOfModule E d) ≫ (algebraSheafOfModuleIso E d).hom = d.unit := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  exact d.toPresheafAlgebraData.algebraMap_eq U r

/-! ### Identities of composites in a category -/

/-- In a category, `mA ≫ th ≫ pi ≫ en = tphi ≫ mM` given the commuting squares `ha`, `hb` and
`hc`, the factorization `hd` of `pmu`, the identities `hcE` and `he`, and the factorization
`hcomp` of `tphi`. -/
private theorem mulCompChain {D : Type*} [Category D]
    {TA TS TT TM A₀ S T M KC KE : D}
    {mA : TA ⟶ A₀} {th : A₀ ⟶ S} {pi : S ⟶ T} {en : T ⟶ M} {dn : M ⟶ T} {mM : TM ⟶ M}
    {tth : TA ⟶ TS} {tpi : TS ⟶ TT} {ten : TT ⟶ TM} {tphi : TA ⟶ TM}
    {cCinv : TS ⟶ KC} {cEinv : TT ⟶ KE} {cEhom : KE ⟶ TT}
    {pmC : KC ⟶ S} {pti : KC ⟶ KE} {pmu : KE ⟶ T}
    (ha : mA ≫ th = tth ≫ cCinv ≫ pmC)
    (hb : pmC ≫ pi = pti ≫ pmu)
    (hc : cCinv ≫ pti = tpi ≫ cEinv)
    (hd : pmu = cEhom ≫ ten ≫ mM ≫ dn)
    (hcE : cEinv ≫ cEhom = 𝟙 TT)
    (he : dn ≫ en = 𝟙 M)
    (hcomp : tth ≫ tpi ≫ ten = tphi) :
    mA ≫ th ≫ pi ≫ en = tphi ≫ mM := by
  simp only [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd, Category.assoc,
    reassoc_of% hcE, he, Category.comp_id, reassoc_of% hcomp]

/-- A functor carries a commuting square of composites to a commuting square of composites. -/
private theorem mapCompChain {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {X Y Z W : D} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W} {d : W ⟶ Z}
    (h : a ≫ b = c ≫ d) :
    G.map a ≫ G.map b = G.map c ≫ G.map d :=
  ((G.map_comp a b).symm.trans (congrArg (G.map (X := X) (Y := Z)) h)).trans (G.map_comp c d)

/-- If `pti ≫ cEhom = cChom ≫ tpi`, `cCinv ≫ cChom = 𝟙` and `cEhom ≫ cEinv = 𝟙`, then
`cCinv ≫ pti = tpi ≫ cEinv`. -/
private theorem comparisonInvChain {D : Type*} [Category D] {TS KC TT KE : D}
    {cChom : KC ⟶ TS} {cCinv : TS ⟶ KC} {cEhom : KE ⟶ TT} {cEinv : TT ⟶ KE}
    {pti : KC ⟶ KE} {tpi : TS ⟶ TT}
    (hnat : pti ≫ cEhom = cChom ≫ tpi)
    (hC : cCinv ≫ cChom = 𝟙 TS)
    (hE : cEhom ≫ cEinv = 𝟙 KE) :
    cCinv ≫ pti = tpi ≫ cEinv := by
  rw [← Category.comp_id pti, ← hE, reassoc_of% hnat, reassoc_of% hC]

/-- If `q ≫ r = qr` and `p ≫ qr = t`, then `p ≫ q ≫ r = t`. -/
private theorem compPairChain {D : Type*} [Category D] {TA TB TC TD : D}
    {p : TA ⟶ TB} {q : TB ⟶ TC} {r : TC ⟶ TD} {qr : TB ⟶ TD} {t : TA ⟶ TD}
    (h₁ : q ≫ r = qr) (h₂ : p ≫ qr = t) :
    p ≫ q ≫ r = t := by
  rw [h₁, h₂]

/-- In a category, `uA ≫ th ≫ pi ≫ en = uM` given the commuting squares `ha`, `hb` and `hc`
and the identity `he`. -/
private theorem unitCompChain {D : Type*} [Category D] {Z KU A₀ S T M : D}
    {uA : Z ⟶ A₀} {th : A₀ ⟶ S} {pi : S ⟶ T} {en : T ⟶ M} {dn : M ⟶ T} {uM : Z ⟶ M}
    {pui : Z ⟶ KU} {pmuC : KU ⟶ S} {pmeta : KU ⟶ T}
    (ha : uA ≫ th = pui ≫ pmuC)
    (hb : pmuC ≫ pi = pmeta)
    (hc : pui ≫ pmeta = uM ≫ dn)
    (he : dn ≫ en = 𝟙 M) :
    uA ≫ th ≫ pi ≫ en = uM := by
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, he, Category.comp_id]

/-- Equal morphisms of modules act equally on sections. -/
private theorem hom_app_apply_congr {Y : Scheme.{u}} {P Q : Y.Modules} {t t' : P ⟶ Q} (h : t = t')
    (U : (Y.Opens)ᵒᵖ) (z : P.val.obj U) : (t.val.app U).hom z = (t'.val.app U).hom z := by
  rw [h]

/-! ### The comparison, and its multiplicativity and unitality -/

section Compare

variable {W W'' : Scheme.{u}} (g : W ⟶ W'') (C : AlgebraSheaf W'') (E : W''.Modules)
  (ι : AlgebraSheaf.underlyingModule C ≅ E) (θ : AlgebraPullbackModuleIso g C)
  {M : W.Modules} (ε : (Scheme.Modules.pullback g).obj E ⟶ M)

/-- Consider the composite

  `underlyingModule ((algebraPullback g).obj C) ⟶ g^*(underlyingModule C) ⟶ g^*E ⟶ M`,

with `θ` the identification of the module underlying `(algebraPullback g).obj C` with `g^*` of the
module underlying `C`, `ι` an identification of the latter with `E` and `ε : g^*E ⟶ M`. If `ι`
carries the multiplication of `C` to `μ`, `δ ≫ ε = 𝟙 M`, and the inverse image of `μ` along `g`
is `AlgebraicGeometry.tensorDescentApp g E M ε δ mul`, then this composite carries the
multiplication of `(algebraPullback g).obj C` to `mul`. -/
public theorem multiplication_comp_algebraPullbackCompare
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (hι : multiplication C ≫ ι.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩)).map
        ((ι.hom, ι.hom) : (_, _) ⟶ (_, _))) ≫ μ)
    (δ : M ⟶ (Scheme.Modules.pullback g).obj E) (hδε : δ ≫ ε = 𝟙 M)
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj (M)).obj (M)) ⟶ M)
    (hμ : (Scheme.Modules.pullback g).map μ = tensorDescentApp g E M ε δ mul) :
    multiplication ((algebraPullback g).obj C) ≫
        (θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((((θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε)),
            ((θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε))) :
          (_, _) ⟶ (_, _))) ≫ mul := by
  have hb := mapCompChain (Scheme.Modules.pullback g) hι
  have hc := comparisonInvChain (schemePullbackTensorIso_tensorSheafMap_hom g ι.hom ι.hom)
    (schemePullbackTensorIso g (AlgebraSheaf.underlyingModule C)
      (AlgebraSheaf.underlyingModule C)).inv_hom_id
    (schemePullbackTensorIso g E E).hom_inv_id
  have hcomp := compPairChain
    (tensorSheafMap_comp W.toRingedSpace ((Scheme.Modules.pullback g).map ι.hom) ε
      ((Scheme.Modules.pullback g).map ι.hom) ε)
    (tensorSheafMap_comp W.toRingedSpace θ.iso.hom
      ((Scheme.Modules.pullback g).map ι.hom ≫ ε) θ.iso.hom
      ((Scheme.Modules.pullback g).map ι.hom ≫ ε))
  exact mulCompChain θ.multiplication_comp_iso_hom hb hc
    (hμ.trans (tensorDescentApp_eq g E M ε δ mul)) (schemePullbackTensorIso g E E).inv_hom_id
    hδε hcomp

/-- If `ι` carries the structure morphism of `C` to `η`, `δ ≫ ε = 𝟙 M`, and the inverse image
of `η` along `g` is `u ≫ δ`, then the composite `θ.iso.hom ≫ g^*(ι.hom) ≫ ε` carries the structure
morphism of `(algebraPullback g).obj C` to `u`. -/
public theorem unitModuleMap_comp_algebraPullbackCompare
    (η : SheafOfModules.unit W''.ringCatSheaf ⟶ E)
    (hι : unitModuleMap C ≫ ι.hom = η)
    (δ : M ⟶ (Scheme.Modules.pullback g).obj E) (hδε : δ ≫ ε = 𝟙 M)
    (u : SheafOfModules.unit W.ringCatSheaf ⟶ M)
    (hη : (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map η = u ≫ δ) :
    unitModuleMap ((algebraPullback g).obj C) ≫
        (θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε) = u :=
  unitCompChain θ.unitModuleMap_comp_iso_hom
    (((Scheme.Modules.pullback g).map_comp (unitModuleMap C) ι.hom).symm.trans
      (congrArg (Scheme.Modules.pullback g).map hι))
    hη hδε

end Compare

/-! ### Pullbacks of the algebra sheaf of module-algebra data -/

/-- Let `E` be a module on `W''` carrying a `Stacks.FundamentalGroup.ModuleAlgebraData d` whose
`mul` comes from a morphism `μ` out of the sheafified tensor square, let `g : W ⟶ W''`, let `F` be
an algebra sheaf on `W`, and let `ε`, `δ` be mutually inverse morphisms between `g^*E` and the
module underlying `F`. If the inverse image of `μ` along `g` is the component
`AlgebraicGeometry.tensorDescentApp` built from the multiplication of `F`, and the inverse image
of `d.unit` is the structure morphism of `F` read through `δ`, then
`(algebraPullback g).obj (algebraSheafOfModule E d)` and `F` are isomorphic as algebra sheaves. -/
public theorem nonempty_algebraPullback_algebraSheafOfModule_iso {W W'' : Scheme.{u}}
    (g : W ⟶ W'') (E : W''.Modules) (d : ModuleAlgebraData E)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (hdmul : d.mul = mulPresheafOfHom E μ)
    (F : AlgebraSheaf W)
    (ε : (Scheme.Modules.pullback g).obj E ⟶ AlgebraSheaf.underlyingModule F)
    (δ : AlgebraSheaf.underlyingModule F ⟶ (Scheme.Modules.pullback g).obj E)
    (hδε : δ ≫ ε = 𝟙 (AlgebraSheaf.underlyingModule F))
    (hεδ : ε ≫ δ = 𝟙 ((Scheme.Modules.pullback g).obj E))
    (hμ : (Scheme.Modules.pullback g).map μ =
      tensorDescentApp g E (AlgebraSheaf.underlyingModule F) ε δ (multiplication F))
    (hη : (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map d.unit = unitModuleMap F ≫ δ) :
    Nonempty ((algebraPullback g).obj (algebraSheafOfModule E d) ≅ F) := by
  have hcmp := isIso_algebraPullbackModuleComparison g (algebraSheafOfModule E d)
  let θ : AlgebraPullbackModuleIso g (algebraSheafOfModule E d) :=
    @algebraPullbackModuleIsoOfIsIso W W'' g (algebraSheafOfModule E d) hcmp
  let ι : AlgebraSheaf.underlyingModule (algebraSheafOfModule E d) ≅ E :=
    algebraSheafOfModuleIso E d
  let φ : AlgebraSheaf.underlyingModule ((algebraPullback g).obj (algebraSheafOfModule E d)) ⟶
      AlgebraSheaf.underlyingModule F :=
    θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε
  have hmulφ : multiplication ((algebraPullback g).obj (algebraSheafOfModule E d)) ≫ φ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((φ, φ) : (_, _) ⟶ (_, _))) ≫ multiplication F :=
    multiplication_comp_algebraPullbackCompare g (algebraSheafOfModule E d) E ι θ ε μ
      (multiplication_algebraSheafOfModule_comp_iso_hom E d μ hdmul) δ hδε (multiplication F) hμ
  have hunitφ : unitModuleMap ((algebraPullback g).obj (algebraSheafOfModule E d)) ≫ φ =
      unitModuleMap F :=
    unitModuleMap_comp_algebraPullbackCompare g (algebraSheafOfModule E d) E ι θ ε d.unit
      (unitModuleMap_algebraSheafOfModule_comp_iso_hom E d) δ hδε (unitModuleMap F) hη
  have hone : ∀ U : (W.Opens)ᵒᵖ,
      (φ.val.app U).hom
          (oneSection ((algebraPullback g).obj (algebraSheafOfModule E d)) U) =
        oneSection F U := fun U =>
    (unitModuleMap_comp_one φ U).symm.trans
      ((hom_app_apply_congr hunitφ U (1 : W.presheaf.obj U)).trans (unitModuleMap_one F U))
  have hmul : ∀ (U : (W.Opens)ᵒᵖ)
      (x y : ((algebraPullback g).obj (algebraSheafOfModule E d)).right.obj.obj U),
      (φ.val.app U).hom
          (mulSection ((algebraPullback g).obj (algebraSheafOfModule E d)) U x y) =
        mulSection F U ((φ.val.app U).hom x) ((φ.val.app U).hom y) := fun U x y =>
    (multiplication_comp_tmul φ U x y).symm.trans
      ((hom_app_apply_congr hmulφ U _).trans
        ((tensorSheafMap_comp_tmul φ (multiplication F) U x y).trans
          (multiplication_tmul F U ((φ.val.app U).hom x) ((φ.val.app U).hom y))))
  have hε : IsIso ε := ⟨δ, hεδ, hδε⟩
  have hφ : IsIso φ :=
    inferInstanceAs (IsIso (θ.iso.hom ≫ (Scheme.Modules.pullback g).map ι.hom ≫ ε))
  refine ⟨@asIso _ _ _ _ (homOfMultiplicative φ hone hmul)
    (isIso_of_isIso_underlyingModuleMap _ ?_)⟩
  rw [underlyingModuleMap_homOfMultiplicative]
  exact hφ

/-! ### Algebraizations of adic systems of algebra sheaves -/

section Descent

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
  (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
    AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
  (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
  (hBtrans : ∀ n, Nonempty
    ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
  (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
  (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
    (AlgebraSheaf.underlyingModule (B 0)))
  (P : Stacks.Algebraization.CoherentModulesProperOver f)
  (e : (adicThickeningCompletionFunctor A I f).obj P ≅
    adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0)

include hpullback hqc hBtrans hMcoh hM0 e in
/-- Let `B` be an adic system of quasi-coherent algebra sheaves on the thickenings `Xₙ`, and let
`e` identify the completion of `P` with the system of modules underlying `B`. If `A` is
`I`-adically complete and the completion functor is an equivalence, then `properModule P` carries
a `Stacks.FundamentalGroup.ModuleAlgebraData` whose algebra sheaf pulls back to `B n` along
`vₙ : Xₙ ⟶ X` for every `n`. -/
public theorem exists_moduleAlgebraData_algebraPullback_of_adicAlgebraModuleSystem
    [IsAdicComplete I A]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence) :
    ∃ d : ModuleAlgebraData (properModule P), ∀ n, Nonempty
      ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj
        (algebraSheafOfModule (properModule P) d) ≅ B n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨μ, hμ, -⟩ := existsUnique_multiplication_of_adicAlgebraModuleSystem A I f hpullback B
    hqc hBtrans hMcoh hM0 P e h088F
  obtain ⟨η, hη⟩ := exists_unit_of_adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
    hM0 P e
  refine ⟨moduleAlgebraDataOfAdicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0 P e
    h088F μ η hμ hη, fun n => ?_⟩
  exact nonempty_algebraPullback_algebraSheafOfModule_iso
    (pullback.fst f (adicThickeningι A I n)) (properModule P) _ μ rfl (B n)
    (e.hom.app n) (e.inv.app n)
    (inv_app_comp_hom_app A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hom_app_comp_inv_app A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hμ n) (hη n)

end Descent

end AlgebraicGeometry

end
