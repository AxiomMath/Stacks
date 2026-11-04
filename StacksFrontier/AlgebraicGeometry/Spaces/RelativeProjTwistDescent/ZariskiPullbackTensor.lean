module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Modules.ZariskiRingedToposPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Stacks 03EL and the square of a morphism of schemes between étale and Zariski sites

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B` and `r` the underlying morphism
of schemes.  The square of morphisms of ringed topoi

```
  X_étale ---- ε_X ----> X_Zar
     |                     |
  base change a            r
     v                     v
  Y_étale ---- ε_Y ----> Y_Zar
```

has four sides in the shape the comparison of Stacks 03EL consumes: the morphisms `ε` of
Stacks 070R (`AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`), small étale base
change (`AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom`) and the Zariski morphism
of `r` (`AlgebraicGeometry.Scheme.Hom.zariskiRingedToposModulesHom`).  Each pullback of modules is
identified with the functor its consumers use: the associated module of Stacks 03DU (4), the
pullback along `smallEtaleStructureMapRing B a`, and the pullback of modules along `r`.

This file takes the upper route as the diagonal, identifies the geometric direct image of the
lower route with that of the diagonal through `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`
(the base change of an open is its preimage), checks that this identification carries the
structure maps to each other (`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso`),
and deduces that the comparisons of Stacks 03EL of the four sides are compatible round the square.
By
`AlgebraicGeometry.Scheme.Hom.pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits`
the comparison for `r` is then the comparison of Stacks 01CD,
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`.

## Main definitions

* `Stacks.SheafOfModules.factorizationTransportIso`: for a morphism of ringed topoi with two
  factorizations, the comparison of the two composite functors identified with the pullbacks,
  read off the comparisons of pullbacks of the factorizations.
* `AlgebraicGeometry.SmallEtale.zariskiSquareHom`: the diagonal `X_étale ⟶ Y_Zar`, the composite
  of `ε_X` with the Zariski morphism of `r`.
* `AlgebraicGeometry.SmallEtale.zariskiSquareDirectImageIso`: **the geometric direct images of the
  two routes agree.**
* `Stacks.SheafOfModules.IsTensorTranspose`, `Stacks.SheafOfModules.IsSquareTranspose`: a
  comparison of a right adjoint with tensor products, resp. a morphism `L_ψ₁ R_ψ₂ N ⟶ R_φ₁ L_φ₂ N`,
  read off Stacks 03EL resp. a comparison of two routes by transposition.

## Main results

* `Stacks.SheafOfModules.whiskered_leftAdjointUniq_eq_leftAdjointUniq`: the comparison of two
  factorizations read off comparisons of left adjoints by uniqueness is the comparison by
  uniqueness along the composite comparison of right adjoints.

* `AlgebraicGeometry.SmallEtale.fSharpSetComp_zariskiSquareDirectImageIso`: that comparison of
  direct images carries the composite structure map of the lower route to the structure map of
  the diagonal.
* `AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIsoTransport`: **Stacks 03EL is
  compatible with the square of `a`.**
* `AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIso`: the same, with the comparison
  for `r` written as the comparison of Stacks 01CD.
* `AlgebraicGeometry.SmallEtale.pushforwardSquareIso_hom_app_eq_zariskiSquare`: the comparison of
  the composite direct images round the square, `SheafOfModules.pushforwardSquareIso`, is the
  composite of the comparisons of direct images that build the comparison of the two routes.
* `AlgebraicGeometry.SmallEtale.factorizationTransportIso_zariskiSquare`: **the comparison of the
  two routes is `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso B a`**, the
  identification `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of Stacks 03LC (1).
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_transpose`: the compatibility of
  Stacks 03EL with a square, transposed along two adjunctions.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor`: the tensor product of two
  quasi-coherent modules on the small étale site is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.pullbackTensorIso_restrictModulePullbackObjIso`: **restriction to
  the small Zariski sites, through `restrictModulePullbackObjIso` and `restrictModuleTensorIso`,
  carries Stacks 03EL for small étale base change to Stacks 01CD for the morphism of schemes**, on
  quasi-coherent modules.

## Implementation notes

The statements of the two compatibilities are written through `type_of%` of the generic
statements they instantiate: a separately written copy differs from them in the spelling of the
categories of modules (the Zariski sites read as ringed topoi against the schemes' own module
categories), and comparing the two spellings exhausts the elaboration budget.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.SheafOfModules

universe wX vX uX wZ vZ uZ wA vA uA wB vB uB

/-- The comparison of two factorizations read off two comparisons of pullbacks `c₁, c₂` and the
four identifications `α`, followed by the identifications, is the second comparison. -/
private theorem comp_factorizationTransportIso_hom_app {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵]
    [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳] {χs : 𝒵 ⥤ 𝒳} {ψ₁s Lψ₁ : 𝒵 ⥤ 𝒴₁}
    {φ₁s Lφ₁ : 𝒴₁ ⥤ 𝒳} {ψ₂s Lψ₂ : 𝒵 ⥤ 𝒴₂} {φ₂s Lφ₂ : 𝒴₂ ⥤ 𝒳} (c₁ : χs ≅ ψ₁s ⋙ φ₁s)
    (c₂ : χs ≅ ψ₂s ⋙ φ₂s) (αψ₁ : ψ₁s ≅ Lψ₁) (αφ₁ : φ₁s ≅ Lφ₁) (αψ₂ : ψ₂s ≅ Lψ₂)
    (αφ₂ : φ₂s ≅ Lφ₂) (M : 𝒵) :
    c₁.hom.app M ≫ φ₁s.map (αψ₁.hom.app M) ≫ αφ₁.hom.app (Lψ₁.obj M) ≫
        ((Functor.isoWhiskerLeft Lψ₁ αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s) ≪≫
          Functor.isoWhiskerLeft Lψ₂ αφ₂).hom.app M =
      c₂.hom.app M ≫ φ₂s.map (αψ₂.hom.app M) ≫ αφ₂.hom.app (Lψ₂.obj M) := by
  simp [← Functor.map_comp_assoc]

variable {X : AlgebraicGeometry.RingedTopos.{vX, uX, wX}}
    {Z : AlgebraicGeometry.RingedTopos.{vZ, uZ, wZ}}
    {Y₁ : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    {Y₂ : AlgebraicGeometry.RingedTopos.{vB, uB, wB}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wX} RingCat.{wX})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{wZ} RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [X.J.HasSheafCompose (forget RingCat.{wX})] [Z.J.HasSheafCompose (forget RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget RingCat.{wA})] [Y₂.J.HasSheafCompose (forget RingCat.{wB})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wX})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [HasWeakSheafify X.J AddCommGrpCat.{wX}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wX}]
  [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}]
  [HasWeakSheafify Y₁.J AddCommGrpCat.{wA}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{wB}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  (φ₁ : RingedToposHom X Y₁) (ψ₁ : RingedToposHom Y₁ Z)
  (φ₂ : RingedToposHom X Y₂) (ψ₂ : RingedToposHom Y₂ Z) (χ : RingedToposHom X Z)
  (τ₁ : φ₁.toToposHom.pushforward ⋙ ψ₁.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₁ : fSharpSetComp φ₁ ψ₁ ≫
    τ₁.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (τ₂ : φ₂.toToposHom.pushforward ⋙ ψ₂.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₂ : fSharpSetComp φ₂ ψ₂ ≫
    τ₂.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ₁ : _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₁ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O)}
  {Lφ₂ : _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₂ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O)}
  (αφ₁ : φ₁.pullbackModules ≅ Lφ₁) (αψ₁ : ψ₁.pullbackModules ≅ Lψ₁)
  (αφ₂ : φ₂.pullbackModules ≅ Lφ₂) (αψ₂ : ψ₂.pullbackModules ≅ Lψ₂)

/-- The comparison of two factorizations of a morphism of ringed topoi `χ`, through `φ₁, ψ₁` and
through `φ₂, ψ₂`, on functors `L` identified with all four pullbacks by isomorphisms `α`:
`Stacks.SheafOfModules.factorizationPullbackIso` followed by the identification `α_φ₂`. -/
noncomputable def factorizationTransportIso : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂ :=
  factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂ ≪≫
    Functor.isoWhiskerLeft Lψ₂ αφ₂

/-- **The transported comparisons of Stacks 03EL along two factorizations agree through the
comparison of the factorizations**, with all four functors identified with pullbacks.  This is
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square` at
`Stacks.SheafOfModules.factorizationTransportIso`, which corresponds to the two comparisons of
pullbacks by construction. -/
theorem pullbackTensorIsoTransport_square_factorizationTransportIso
    (F G : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)) :
    Lφ₁.map (pullbackTensorIsoTransport ψ₁ αψ₁ F G).hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map
            ((factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
              F)).app (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (Lφ₂.obj (Lψ₂.obj F))).map
              ((factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
                G) =
      (factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
          (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        Lφ₂.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ αφ₂ (Lψ₂.obj F) (Lψ₂.obj G)).hom :=
  pullbackTensorIsoTransport_square φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂
    (factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂)
    (fun M => comp_factorizationTransportIso_hom_app (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁)
      (pullbackModulesCompIso φ₂ ψ₂ χ τ₂ hτ₂) αψ₁ αφ₁ αψ₂ αφ₂ M) F G

/-- `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso` with the
transported comparison along `ψ₁` replaced by any isomorphism `I` it is equal to.  This is the
form in which a closed identification of that comparison (for instance with a comparison built by
other means) is substituted without rewriting inside the square. -/
theorem pullbackTensorIsoTransport_square_factorizationTransportIso_of_eq
    (F G : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O))
    {I : Lψ₁.obj (((Tensor.sheafTensor Z.O).obj F).obj G) ≅
      ((Tensor.sheafTensor Y₁.O).obj (Lψ₁.obj F)).obj (Lψ₁.obj G)}
    (hI : pullbackTensorIsoTransport ψ₁ αψ₁ F G = I) :
    Lφ₁.map I.hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map
            ((factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
              F)).app (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (Lφ₂.obj (Lψ₂.obj F))).map
              ((factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
                G) =
      (factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom.app
          (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        Lφ₂.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ αφ₂ (Lψ₂.obj F) (Lψ₂.obj G)).hom := by
  subst hI
  exact pullbackTensorIsoTransport_square_factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂
    αφ₁ αψ₁ αφ₂ αψ₂ F G

/-- For a bifunctor, a morphism in the first variable followed by one in the second, composed with
another such pair, is the pair of composites. -/
private theorem bifunctor_comp_comp {𝒞 𝒟 : Type*} {_ : Category 𝒞} {_ : Category 𝒟}
    (S : 𝒞 ⥤ 𝒞 ⥤ 𝒟) {A A' A'' B B' B'' : 𝒞} (f : A ⟶ A') (g : B ⟶ B') (f' : A' ⟶ A'')
    (g' : B' ⟶ B'') :
    (S.map f).app B ≫ (S.obj A').map g ≫ (S.map f').app B' ≫ (S.obj A'').map g' =
      (S.map (f ≫ f')).app B ≫ (S.obj A'').map (g ≫ g') := by
  rw [reassoc_of% ((S.map f').naturality g)]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- For a bifunctor, a morphism in the second variable followed by one in the first is the
morphism in the first variable followed by the one in the second. -/
private theorem bifunctor_obj_map_comp_map_app {𝒞 𝒟 : Type*} {_ : Category 𝒞} {_ : Category 𝒟}
    (S : 𝒞 ⥤ 𝒞 ⥤ 𝒟) {A A' B B' : 𝒞} (f : A ⟶ A') (g : B ⟶ B') :
    (S.obj A).map g ≫ (S.map f).app B' = (S.map f).app B ≫ (S.obj A').map g :=
  (S.map f).naturality g

/-- For a bifunctor, a pair of morphisms in the two variables followed by another pair, read
through factorizations of the two composites. -/
private theorem bifunctor_comp_comp_eq {𝒞 𝒟 : Type*} {_ : Category 𝒞} {_ : Category 𝒟}
    (S : 𝒞 ⥤ 𝒞 ⥤ 𝒟) {A A' A'' A₀ B B' B'' B₀ : 𝒞} (a : A ⟶ A') (b : B ⟶ B') (c : B' ⟶ B'')
    (d : A' ⟶ A'') (x : A ⟶ A₀) (y : B ⟶ B₀) (x' : A₀ ⟶ A'') (y' : B₀ ⟶ B'')
    (hx : a ≫ d = x ≫ x') (hy : b ≫ c = y ≫ y') :
    (S.map a).app B ≫ (S.obj A').map b ≫ (S.obj A').map c ≫ (S.map d).app B'' =
      (S.map x).app B ≫ (S.obj A₀).map y ≫ (S.map x').app B₀ ≫ (S.obj A'').map y' := by
  rw [bifunctor_obj_map_comp_map_app S d c, bifunctor_comp_comp, hx, hy, bifunctor_comp_comp]

/-- **A comparison of a right adjoint with tensor products read off Stacks 03EL.**  For a morphism
of ringed topoi `f : X ⟶ Z` whose pullback is identified with a left adjoint `L ⊣ R`, a
comparison `t : R(N₁ ⊗ N₂) ≅ R N₁ ⊗ R N₂` is the transpose of Stacks 03EL along `f` when its
inverse is the unit followed by `R` of the transported comparison of Stacks 03EL at
`R N₁, R N₂` and the two counits. -/
def IsTensorTranspose (f : RingedToposHom X Z)
    {L : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
      _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
    {R : _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O) ⥤
      _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)}
    (adj : L ⊣ R) (α : f.pullbackModules ≅ L)
    (N₁ N₂ : _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O))
    (t : R.obj (((Tensor.sheafTensor X.O).obj N₁).obj N₂) ≅
      ((Tensor.sheafTensor Z.O).obj (R.obj N₁)).obj (R.obj N₂)) : Prop :=
  t.inv = adj.unit.app _ ≫ R.map
    ((pullbackTensorIsoTransport f α (R.obj N₁) (R.obj N₂)).hom ≫
      ((Tensor.sheafTensor X.O).obj (L.obj (R.obj N₁))).map (adj.counit.app N₂) ≫
      ((Tensor.sheafTensor X.O).map (adj.counit.app N₁)).app N₂)

/-- If `t` is a transpose of Stacks 03EL (`Stacks.SheafOfModules.IsTensorTranspose`), then `L t⁻¹`
followed by the counit is the transported comparison of Stacks 03EL followed by the two counits. -/
private theorem map_inv_comp_counit_of_isTensorTranspose (f : RingedToposHom X Z)
    {L : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
      _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
    {R : _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O) ⥤
      _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)}
    (adj : L ⊣ R) (α : f.pullbackModules ≅ L)
    (N₁ N₂ : _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O))
    {t : R.obj (((Tensor.sheafTensor X.O).obj N₁).obj N₂) ≅
      ((Tensor.sheafTensor Z.O).obj (R.obj N₁)).obj (R.obj N₂)}
    (ht : IsTensorTranspose f adj α N₁ N₂ t) :
    L.map t.inv ≫ adj.counit.app _ =
      (pullbackTensorIsoTransport f α (R.obj N₁) (R.obj N₂)).hom ≫
        ((Tensor.sheafTensor X.O).obj (L.obj (R.obj N₁))).map (adj.counit.app N₂) ≫
        ((Tensor.sheafTensor X.O).map (adj.counit.app N₁)).app N₂ := by
  refine (adj.homEquiv_counit (g := t.inv)).symm.trans ?_
  rw [ht]
  exact (adj.homEquiv _ _).symm_apply_eq.mpr (adj.homEquiv_unit _ _ _).symm

/-- **A morphism `L_ψ₁ R_ψ₂ N ⟶ R_φ₁ L_φ₂ N` read off a comparison of two routes round a
square.**  For adjunctions `L_φ₁ ⊣ R_φ₁` and `L_ψ₂ ⊣ R_ψ₂` and a comparison
`m : L_ψ₁ ⋙ L_φ₁ ≅ L_ψ₂ ⋙ L_φ₂`, the morphism `p` is the transpose of `m` at `R_ψ₂ N` followed
by `L_φ₂` of the counit. -/
def IsSquareTranspose {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂]
    [Category 𝒳] {Lψ₁ : 𝒵 ⥤ 𝒴₁} {Lφ₁ : 𝒴₁ ⥤ 𝒳} {Lψ₂ : 𝒵 ⥤ 𝒴₂} {Lφ₂ : 𝒴₂ ⥤ 𝒳}
    {Rφ₁ : 𝒳 ⥤ 𝒴₁} {Rψ₂ : 𝒴₂ ⥤ 𝒵} (adj₁ : Lφ₁ ⊣ Rφ₁) (adj₂ : Lψ₂ ⊣ Rψ₂)
    (m : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂) (N : 𝒴₂) (p : Lψ₁.obj (Rψ₂.obj N) ⟶ Rφ₁.obj (Lφ₂.obj N)) :
    Prop :=
  Lφ₁.map p ≫ adj₁.counit.app _ = m.hom.app (Rψ₂.obj N) ≫ Lφ₂.map (adj₂.counit.app N)

/-- **The compatibility of Stacks 03EL with a square, transposed along two adjunctions.**  In the
situation of `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso`,
let `L_φ₁ ⊣ R_φ₁` and `L_ψ₂ ⊣ R_ψ₂`, let the comparison of the two routes be `m`, and let
`I` be the transported comparison of Stacks 03EL along `ψ₁` at `R_ψ₂ N₁, R_ψ₂ N₂`.  Read the
two adjunctions as identifications through comparisons

* `t_Z : R_ψ₂(N₁ ⊗ N₂) ≅ R_ψ₂ N₁ ⊗ R_ψ₂ N₂` and
  `t_Y : R_φ₁(L_φ₂N₁ ⊗ L_φ₂N₂) ≅ R_φ₁L_φ₂N₁ ⊗ R_φ₁L_φ₂N₂`,
  whose inverses are the transposes of Stacks 03EL along `ψ₂` resp. `φ₁` followed by the counits;
* `p : L_ψ₁R_ψ₂ N ⟶ R_φ₁L_φ₂ N`, whose transposes are `m` followed by `L_φ₂` of the counit.

Then `L_ψ₁ t_Z ≫ I ≫ (p₁ ⊗ p₂) = p_{N₁ ⊗ N₂} ≫ R_φ₁(T_φ₂) ≫ t_Y`, where `T_φ₂` is the transported
comparison along `φ₂`: the right adjoints carry Stacks 03EL along `φ₂` to Stacks 03EL along `ψ₁`.

The proof transposes along `L_φ₁ ⊣ R_φ₁` and uses the square at `R_ψ₂ N₁, R_ψ₂ N₂`, the naturality
of the transported comparisons along `φ₁` and `φ₂` and of `m`, and the transpose of `t_Z`. -/
theorem pullbackTensorIsoTransport_square_transpose
    {Rφ₁ : _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O) ⥤
      _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O)} (adj₁ : Lφ₁ ⊣ Rφ₁)
    {Rψ₂ : _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O) ⥤
      _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)} (adj₂ : Lψ₂ ⊣ Rψ₂)
    {m : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂}
    (hm : factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂ = m)
    (N₁ N₂ : _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O))
    {I : Lψ₁.obj (((Tensor.sheafTensor Z.O).obj (Rψ₂.obj N₁)).obj (Rψ₂.obj N₂)) ≅
      ((Tensor.sheafTensor Y₁.O).obj (Lψ₁.obj (Rψ₂.obj N₁))).obj (Lψ₁.obj (Rψ₂.obj N₂))}
    (hI : pullbackTensorIsoTransport ψ₁ αψ₁ (Rψ₂.obj N₁) (Rψ₂.obj N₂) = I)
    (tZ : Rψ₂.obj (((Tensor.sheafTensor Y₂.O).obj N₁).obj N₂) ≅
      ((Tensor.sheafTensor Z.O).obj (Rψ₂.obj N₁)).obj (Rψ₂.obj N₂))
    (htZ : IsTensorTranspose ψ₂ adj₂ αψ₂ N₁ N₂ tZ)
    (tY : Rφ₁.obj (((Tensor.sheafTensor X.O).obj (Lφ₂.obj N₁)).obj (Lφ₂.obj N₂)) ≅
      ((Tensor.sheafTensor Y₁.O).obj (Rφ₁.obj (Lφ₂.obj N₁))).obj (Rφ₁.obj (Lφ₂.obj N₂)))
    (htY : IsTensorTranspose φ₁ adj₁ αφ₁ (Lφ₂.obj N₁) (Lφ₂.obj N₂) tY)
    (p₁ : Lψ₁.obj (Rψ₂.obj N₁) ⟶ Rφ₁.obj (Lφ₂.obj N₁)) (hp₁ : IsSquareTranspose adj₁ adj₂ m N₁ p₁)
    (p₂ : Lψ₁.obj (Rψ₂.obj N₂) ⟶ Rφ₁.obj (Lφ₂.obj N₂)) (hp₂ : IsSquareTranspose adj₁ adj₂ m N₂ p₂)
    (p : Lψ₁.obj (Rψ₂.obj (((Tensor.sheafTensor Y₂.O).obj N₁).obj N₂)) ⟶
      Rφ₁.obj (Lφ₂.obj (((Tensor.sheafTensor Y₂.O).obj N₁).obj N₂)))
    (hp : IsSquareTranspose adj₁ adj₂ m _ p) :
    Lψ₁.map tZ.hom ≫ I.hom ≫
        ((Tensor.sheafTensor Y₁.O).map p₁).app (Lψ₁.obj (Rψ₂.obj N₂)) ≫
          ((Tensor.sheafTensor Y₁.O).obj (Rφ₁.obj (Lφ₂.obj N₁))).map p₂ =
      p ≫ Rφ₁.map (pullbackTensorIsoTransport φ₂ αφ₂ N₁ N₂).hom ≫ tY.hom := by
  unfold IsSquareTranspose at hp₁ hp₂ hp
  have hsq := pullbackTensorIsoTransport_square_factorizationTransportIso_of_eq φ₁ ψ₁ φ₂ ψ₂ χ τ₁
    hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂ (Rψ₂.obj N₁) (Rψ₂.obj N₂) hI
  rw [hm] at hsq
  have hZ : Lψ₂.map tZ.hom ≫ (pullbackTensorIsoTransport ψ₂ αψ₂ (Rψ₂.obj N₁) (Rψ₂.obj N₂)).hom ≫
      ((Tensor.sheafTensor Y₂.O).map (adj₂.counit.app N₁)).app (Lψ₂.obj (Rψ₂.obj N₂)) ≫
        ((Tensor.sheafTensor Y₂.O).obj N₁).map (adj₂.counit.app N₂) =
      adj₂.counit.app _ := by
    have h1 := map_inv_comp_counit_of_isTensorTranspose ψ₂ adj₂ αψ₂ N₁ N₂ htZ
    dsimp only [Functor.id_obj, Functor.comp_obj] at h1 ⊢
    rw [← bifunctor_obj_map_comp_map_app (Tensor.sheafTensor Y₂.O), ← h1,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have n1 := pullbackTensorIsoTransport_hom_naturality φ₁ αφ₁ p₁ p₂
  rw [CategoryTheory.Functor.map_comp, Category.assoc] at n1
  have n2 := pullbackTensorIsoTransport_hom_naturality φ₂ αφ₂ (adj₂.counit.app N₁)
    (adj₂.counit.app N₂)
  have nm := m.hom.naturality tZ.hom
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map] at hsq hZ n1 n2 nm hp hp₁ hp₂ ⊢
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine (Iso.comp_inv_eq tY).mp ?_
  apply (adj₁.homEquiv _ _).symm.injective
  have hk := (adj₁.homEquiv_counit _ _ _).trans
    (map_inv_comp_counit_of_isTensorTranspose φ₁ adj₁ αφ₁ (Lφ₂.obj N₁) (Lφ₂.obj N₂) htY)
  dsimp only [Functor.id_obj] at hk
  rw [adj₁.homEquiv_naturality_left_symm, hk, adj₁.homEquiv_naturality_right_symm,
    adj₁.homEquiv_counit, hp]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, bifunctor_comp_comp_eq (Tensor.sheafTensor X.O) _ _ _ _ _ _ _ _ hp₁ hp₂,
    reassoc_of% hsq, ← n2, reassoc_of% nm, ← hZ]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

/-- The conjugate of the inverse of the comparison of two left adjoints of `R'`, one of them
obtained by changing the right adjoint of `adj` along `e : R ≅ R'`, is `e`. -/
private theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv {𝒜 ℬ : Type*} [Category 𝒜]
    [Category ℬ] {L L' : 𝒜 ⥤ ℬ} {R R' : ℬ ⥤ 𝒜} (adj : L ⊣ R) (e : R ≅ R') (adj' : L' ⊣ R') :
    conjugateEquiv adj adj' (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').inv =
      e.hom := by
  have h := conjugateEquiv_comm (adj₁ := adj) (adj₂ := adj')
    (α := (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').inv)
    (β := (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').hom) (by simp)
  rw [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom] at h
  simpa using congrArg (· ≫ e.hom) h

/-- `conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv` with the comparison taken the other way
round. -/
private theorem conjugateEquiv_leftAdjointUniq_swap_ofNatIsoRight_hom {𝒜 ℬ : Type*} [Category 𝒜]
    [Category ℬ] {L L' : 𝒜 ⥤ ℬ} {R R' : ℬ ⥤ 𝒜} (adj : L ⊣ R) (e : R ≅ R') (adj' : L' ⊣ R') :
    conjugateEquiv adj adj' (Adjunction.leftAdjointUniq adj' (adj.ofNatIsoRight e)).hom =
      e.hom :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv adj e adj'

/-- **Two comparisons of the composite left adjoints round a square agree.**  Let a morphism `χ`
factor as `φ₁ ∘ ψ₁` and as `φ₂ ∘ ψ₂`, each of its five left adjoints (`χ^*`, `ψ_i^*`, `φ_i^*`)
compared with the composite of two by uniqueness of left adjoints along the comparisons `κ_i` of
right adjoints, and let the four functors `L` be other left adjoints of right adjoints `R`
identified with the pushforwards by `ρ`.  The comparison
`L_ψ₁ ⋙ L_φ₁ ≅ L_ψ₂ ⋙ L_φ₂` read off the comparisons of pullbacks of the two factorizations is
the comparison by uniqueness of left adjoints along any isomorphism `σ` of the composite right
adjoints which is the composite of the `ρ` and `κ`.

This is the form in which `Stacks.SheafOfModules.factorizationTransportIso` is compared with a
comparison of composite pullbacks built from a comparison of composite pushforwards, such as
`SheafOfModules.pullbackSquareIso`: the two are equal as soon as the comparisons of right
adjoints agree. -/
theorem whiskered_leftAdjointUniq_eq_leftAdjointUniq {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*}
    [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
    {χs : 𝒵 ⥤ 𝒳} {χp : 𝒳 ⥤ 𝒵} {ψ₁s : 𝒵 ⥤ 𝒴₁} {ψ₁p : 𝒴₁ ⥤ 𝒵} {φ₁s : 𝒴₁ ⥤ 𝒳}
    {φ₁p : 𝒳 ⥤ 𝒴₁} {ψ₂s : 𝒵 ⥤ 𝒴₂} {ψ₂p : 𝒴₂ ⥤ 𝒵} {φ₂s : 𝒴₂ ⥤ 𝒳} {φ₂p : 𝒳 ⥤ 𝒴₂}
    {Lψ₁ : 𝒵 ⥤ 𝒴₁} {Rψ₁ : 𝒴₁ ⥤ 𝒵} {Lφ₁ : 𝒴₁ ⥤ 𝒳} {Rφ₁ : 𝒳 ⥤ 𝒴₁}
    {Lψ₂ : 𝒵 ⥤ 𝒴₂} {Rψ₂ : 𝒴₂ ⥤ 𝒵} {Lφ₂ : 𝒴₂ ⥤ 𝒳} {Rφ₂ : 𝒳 ⥤ 𝒴₂}
    (aχ : χs ⊣ χp) (aψ₁ : ψ₁s ⊣ ψ₁p) (aφ₁ : φ₁s ⊣ φ₁p) (aψ₂ : ψ₂s ⊣ ψ₂p) (aφ₂ : φ₂s ⊣ φ₂p)
    (bψ₁ : Lψ₁ ⊣ Rψ₁) (bφ₁ : Lφ₁ ⊣ Rφ₁) (bψ₂ : Lψ₂ ⊣ Rψ₂) (bφ₂ : Lφ₂ ⊣ Rφ₂)
    (κ₁ : φ₁p ⋙ ψ₁p ≅ χp) (κ₂ : φ₂p ⋙ ψ₂p ≅ χp)
    (ρψ₁ : ψ₁p ≅ Rψ₁) (ρφ₁ : φ₁p ≅ Rφ₁) (ρψ₂ : ψ₂p ≅ Rψ₂) (ρφ₂ : φ₂p ≅ Rφ₂)
    (σ : Rφ₂ ⋙ Rψ₂ ≅ Rφ₁ ⋙ Rψ₁)
    (hσ : ∀ X, σ.hom.app X = Rψ₂.map (ρφ₂.inv.app X) ≫ ρψ₂.inv.app (φ₂p.obj X) ≫
      κ₂.hom.app X ≫ κ₁.inv.app X ≫ ρψ₁.hom.app (φ₁p.obj X) ≫ Rψ₁.map (ρφ₁.hom.app X)) :
    (Functor.isoWhiskerLeft Lψ₁ (Adjunction.leftAdjointUniq (aφ₁.ofNatIsoRight ρφ₁) bφ₁).symm ≪≫
        Functor.isoWhiskerRight (Adjunction.leftAdjointUniq (aψ₁.ofNatIsoRight ρψ₁) bψ₁).symm
          φ₁s ≪≫
        (Adjunction.leftAdjointUniq (aχ.ofNatIsoRight κ₁.symm) (aψ₁.comp aφ₁)).symm ≪≫
        Adjunction.leftAdjointUniq (aχ.ofNatIsoRight κ₂.symm) (aψ₂.comp aφ₂) ≪≫
        Functor.isoWhiskerRight (Adjunction.leftAdjointUniq (aψ₂.ofNatIsoRight ρψ₂) bψ₂) φ₂s) ≪≫
        Functor.isoWhiskerLeft Lψ₂ (Adjunction.leftAdjointUniq (aφ₂.ofNatIsoRight ρφ₂) bφ₂) =
      Adjunction.leftAdjointUniq (bψ₁.comp bφ₁) ((bψ₂.comp bφ₂).ofNatIsoRight σ) := by
  apply Iso.ext
  apply (conjugateEquiv (bψ₂.comp bφ₂) (bψ₁.comp bφ₁)).injective
  rw [conjugateEquiv_leftAdjointUniq_swap_ofNatIsoRight_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp (adj₁ := bψ₂.comp bφ₂) (adj₂ := bψ₂.comp aφ₂)
      (adj₃ := bψ₁.comp bφ₁),
    ← conjugateEquiv_comp (adj₁ := bψ₂.comp aφ₂) (adj₂ := bψ₁.comp aφ₁)
      (adj₃ := bψ₁.comp bφ₁),
    ← conjugateEquiv_comp (adj₁ := bψ₂.comp aφ₂) (adj₂ := aψ₁.comp aφ₁)
      (adj₃ := bψ₁.comp aφ₁),
    ← conjugateEquiv_comp (adj₁ := bψ₂.comp aφ₂) (adj₂ := aχ) (adj₃ := aψ₁.comp aφ₁),
    ← conjugateEquiv_comp (adj₁ := bψ₂.comp aφ₂) (adj₂ := aψ₂.comp aφ₂) (adj₃ := aχ),
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv]
  ext X
  simp [hσ]

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The diagonal `X_étale ⟶ Y_Zar` of the square of `a`: the morphism `ε_X` of Stacks 070R
followed by the Zariski morphism of ringed topoi of the underlying morphism of schemes. -/
abbrev zariskiSquareHom :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.comp.{u, u, u + 1, u, u, u, u}
    (schemeHom B a).zariskiRingedToposModulesHom (toZariskiRingedToposModulesHom B X.obj X.property)

/-- **The geometric direct images of the two routes round the square of `a` agree.**  On sheaves
of sets on the small étale site of `X`, the direct image along small étale base change followed
by restriction to the small Zariski site of `Y` is restriction to the small Zariski site of `X`
followed by the direct image along the underlying morphism of schemes, which is the direct image
of `AlgebraicGeometry.SmallEtale.zariskiSquareHom`.

Both routes are restriction along a continuous functor, and the two functors agree by
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`: the base change of an open is its preimage. -/
def zariskiSquareDirectImageIso :
    (baseChangeRingedToposModulesHom B a).toToposHom.pushforward ⋙
        (toZariskiRingedToposModulesHom B Y.obj Y.property).toToposHom.pushforward ≅
      (zariskiSquareHom B a).toToposHom.pushforward :=
  Functor.sheafPushforwardContinuousComp' (baseChangeOpensIso B a).symm _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- On sections over an open `V` of `S`, the structure map of `ε` is the identification of the
sections of `𝒪_S` over `V` with the global functions of the open subscheme `V`. -/
private theorem fSharpSet_toZariskiRingedToposModulesHom_apply (S : Scheme.{u}) (hS : B.Contains S)
    (V : S.zariskiRingedSite.toRingedTopos.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor S.zariskiRingedSite.toRingedTopos.J V).obj
      (Sheaf.ringSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O))) :
    (Sheaf.sectionsFunctor S.zariskiRingedSite.toRingedTopos.J V).map
        (fSharpSet (toZariskiRingedToposModulesHom B S hS)) x =
      (commRingStructureMap B S hS).hom.app V x :=
  congrArg (fun f => (Sheaf.sectionsFunctor _ V).map f x)
    (show fSharpSet (toZariskiRingedToposModulesHom B S hS) = _ from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget.{u, u + 1, u, u, u, u} _)

/-- On sections over an open `V` of `Y`, the structure map of the Zariski morphism of the
underlying morphism of schemes is pullback of functions along it. -/
private theorem fSharpSet_zariskiRingedToposModulesHom_apply
    (V : Y.obj.zariskiRingedSite.toRingedTopos.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.obj.zariskiRingedSite.toRingedTopos.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        Y.obj.zariskiRingedSite.toRingedTopos.O))) :
    (Sheaf.sectionsFunctor Y.obj.zariskiRingedSite.toRingedTopos.J V).map
        (fSharpSet (schemeHom B a).zariskiRingedToposModulesHom) x =
      (schemeHom B a).c.app V x :=
  congrArg (fun f => (Sheaf.sectionsFunctor _ V).map f x)
    (show fSharpSet (schemeHom B a).zariskiRingedToposModulesHom = _ from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget.{u, u, u, u, u, u} _)

/-- On sections over an étale `W / Y`, the structure map of small étale base change is pullback
of functions along the base-change projection. -/
private theorem fSharpSet_baseChangeRingedToposModulesHom_apply
    (W : (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.J W).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))) :
    (Sheaf.sectionsFunctor (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.J W).map
        (fSharpSet (baseChangeRingedToposModulesHom B a)) x =
      (smallEtaleStructureMapRing B a).hom.app W x :=
  congrArg (fun f => (Sheaf.sectionsFunctor _ W).map f x)
    (show fSharpSet (baseChangeRingedToposModulesHom B a) = _ from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget.{u, u + 1, u, u, u + 1, u} _)

/-- **The comparison of direct images of the square of `a` carries the composite structure map of
the lower route to the structure map of the diagonal.**  The structure map of `ε_Y` followed by
the direct image under `ε_Y` of the structure map of small étale base change, read through
`AlgebraicGeometry.SmallEtale.zariskiSquareDirectImageIso`, is the structure map of
`AlgebraicGeometry.SmallEtale.zariskiSquareHom`.  This is the hypothesis on the comparison `τ` of
direct images that `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` asks for.

Over an open `V` of `Y` both sides send a section of `𝒪_Y` to a function on `r⁻¹(V)`: this is
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso` read on sections. -/
theorem fSharpSetComp_zariskiSquareDirectImageIso :
    fSharpSetComp (baseChangeRingedToposModulesHom B a)
        (toZariskiRingedToposModulesHom B Y.obj Y.property) ≫
      (zariskiSquareDirectImageIso B a).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O)) =
      fSharpSet (zariskiSquareHom B a) := by
  refine Eq.trans ?_ (RingedToposHom.fSharpSetComp_comp.{u, u, u + 1, u, u, u, u}
    (schemeHom B a).zariskiRingedToposModulesHom
    (toZariskiRingedToposModulesHom B X.obj X.property))
  refine Sheaf.hom_ext_sections fun V x ↦ ?_
  have k := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (·.hom) (structureMap_comp_baseChangeOpensIso B a)) V) x
  have h1 := fSharpSet_toZariskiRingedToposModulesHom_apply B Y.obj Y.property V x
  have h2 := fSharpSet_baseChangeRingedToposModulesHom_apply B a
    ((opensToSmallEtale B Y.obj Y.property).op.obj V)
    ((commRingStructureMap B Y.obj Y.property).hom.app V x)
  have h3 := fSharpSet_zariskiRingedToposModulesHom_apply B a V x
  have h4 := fSharpSet_toZariskiRingedToposModulesHom_apply B X.obj X.property
    ((TopologicalSpace.Opens.map (schemeHom B a).base).op.obj V) ((schemeHom B a).c.app V x)
  refine ((congrArg (fun y => (Sheaf.sectionsFunctor Y.obj.zariskiRingedSite.toRingedTopos.J V).map
      ((zariskiSquareDirectImageIso B a).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O)))
      ((Sheaf.sectionsFunctor Y.obj.zariskiRingedSite.toRingedTopos.J V).map
        ((toZariskiRingedToposModulesHom B Y.obj Y.property).toToposHom.pushforward.map
          (fSharpSet (baseChangeRingedToposModulesHom B a))) y)) h1).trans
    ((congrArg (fun y => (Sheaf.sectionsFunctor Y.obj.zariskiRingedSite.toRingedTopos.J V).map
      ((zariskiSquareDirectImageIso B a).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O))) y) h2).trans
      (k.trans ?_)))
  refine Eq.trans ?_ (congrArg (fun y => (Sheaf.sectionsFunctor
      X.obj.zariskiRingedSite.toRingedTopos.J
        ((TopologicalSpace.Opens.map (schemeHom B a).base).op.obj V)).map
      (fSharpSet (toZariskiRingedToposModulesHom B X.obj X.property)) y) h3).symm
  exact h4.symm

/-- The structure map of `AlgebraicGeometry.SmallEtale.zariskiSquareHom` is the composite
structure map of the upper route
(`Stacks.Sheaves.RingedToposModules.RingedToposHom.fSharpSetComp_comp`). -/
theorem fSharpSetComp_zariskiSquareHom :
    fSharpSetComp (toZariskiRingedToposModulesHom B X.obj X.property)
        (schemeHom B a).zariskiRingedToposModulesHom ≫
      (Iso.refl ((toZariskiRingedToposModulesHom B X.obj X.property).toToposHom.pushforward ⋙
        (schemeHom B a).zariskiRingedToposModulesHom.toToposHom.pushforward)).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O)) =
      fSharpSet (zariskiSquareHom B a) :=
  RingedToposHom.fSharpSetComp_comp.{u, u, u + 1, u, u, u, u}
    (schemeHom B a).zariskiRingedToposModulesHom (toZariskiRingedToposModulesHom B X.obj X.property)

/-- **Stacks 03EL is compatible with the square of `a`.**  For `𝒪_Y`-modules `F, G` on the
small Zariski site of `Y`, the comparison of Stacks 03EL for the Zariski morphism of the
underlying morphism of schemes, carried by the associated module of `X` and followed by Stacks
03EL at `ε_X` (`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`), and then by the
comparison of the two routes, is the comparison of the two routes followed by Stacks 03EL at
`ε_Y` pulled back along small étale base change and by Stacks 03EL for small étale base change
(`AlgebraicGeometry.SmallEtale.baseChangeTensorIso`).  The comparison of the two routes is
`Stacks.SheafOfModules.factorizationTransportIso` at the square

```
Scheme.Modules.pullback r ⋙ (-)^a ≅
  (-)^a ⋙ SheafOfModules.pullback (smallEtaleStructureMapRing B a).
```

The statement is that of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso` at the square
of `a`; it is written through `type_of%` so that it is that statement verbatim. -/
theorem zariskiSquare_pullbackTensorIsoTransport (F G : Y.obj.Modules) :
    type_of% (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property) F G) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso
    (toZariskiRingedToposModulesHom B X.obj X.property)
    (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
    (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
    (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
    (fSharpSetComp_zariskiSquareDirectImageIso B a)
    (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
    (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property) F G

/-- **Stacks 03EL is compatible with the square of `a`, with the comparison for the morphism of
schemes written as Stacks 01CD.**  This is
`AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIsoTransport` with its first factor,
the comparison of Stacks 03EL for the Zariski morphism of `r` read on the pullback of modules
along `r`, replaced by `Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso r F G`
(`Scheme.Hom.pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits`).

Written through `type_of%` of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso_of_eq`, so that
the identification is substituted in a closed term and never rewritten inside the square. -/
theorem zariskiSquare_pullbackTensorIso (F G : Y.obj.Modules) :
    type_of%
    (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso_of_eq
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property) F G
      ((schemeHom B a).pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits F G)) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationTransportIso_of_eq
    (toZariskiRingedToposModulesHom B X.obj X.property)
    (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
    (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
    (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
    (fSharpSetComp_zariskiSquareDirectImageIso B a)
    (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
    (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property) F G
    ((schemeHom B a).pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits F G)


section DirectImages

/-! ### The comparison of the composite direct images round the square

The comparison `associatedModuleBaseChangeIso B a` of the two composite pullbacks is
`SheafOfModules.pullbackSquareIso`, the comparison by uniqueness of left adjoints along
`SheafOfModules.pushforwardSquareIso`, which is restriction along `baseChangeOpensIso B a` on
sections.  The comparison `factorizationTransportIso` at the square is built from comparisons of
pullbacks by uniqueness of left adjoints as well, along the identifications `ρ` of the four
pushforwards of modules and the comparisons `κ` of composite pushforwards.  On sections every `ρ`
and the comparison for the upper route are the identity and the comparison for the lower route is
restriction along `baseChangeOpensIso B a`, which is what
`AlgebraicGeometry.SmallEtale.pushforwardSquareIso_hom_app_eq_zariskiSquare` records. -/

variable (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O)) (V : Y.obj.Opensᵒᵖ)

/-- A morphism of sheaves of modules equal on sections to six morphisms applied in turn is their
composite.  Stated at a variable ringed site, so that the composite is split where composition
in the category of sheaves of modules is composition in a variable category. -/
private theorem eq_comp_of_val_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : _root_.SheafOfModules.{u} R}
    (s : M₀ ⟶ M₆) (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃) (f₄ : M₃ ⟶ M₄)
    (f₅ : M₄ ⟶ M₅) (f₆ : M₅ ⟶ M₆)
    (h : ∀ V x, s.val.app V x = f₆.val.app V (f₅.val.app V (f₄.val.app V (f₃.val.app V
      (f₂.val.app V (f₁.val.app V x)))))) :
    s = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => h V x))

/-- The identification of the pushforward of modules along small étale base change, read after the
restriction to the small Zariski site of `Y`, is the identity on sections. -/
private theorem pushforward_map_pushforwardModulesToposIsoGeneral_inv_val_app_baseChange
    (x : ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
      SheafOfModules.pushforward.{u} (structureMap B Y.obj Y.property)).obj N).val.obj V) :
    ((SheafOfModules.pushforward.{u} (structureMap B Y.obj Y.property)).map
      ((smallEtaleRingedSiteHom B a).pushforwardModulesToposIsoGeneral.inv.app N)).val.app V x =
      x :=
  (smallEtaleRingedSiteHom B a).pushforwardModulesToposIsoGeneral_inv_app_val_app N _ x

/-- The identification of the pushforward of modules along `ε_Y` is the identity on sections. -/
private theorem pushforwardModulesToposIsoGeneral_inv_val_app_toZariski (y) :
    ((toZariskiRingedSiteHom B Y.obj Y.property).pushforwardModulesToposIsoGeneral.inv.app
      ((pushforwardModules (baseChangeRingedToposModulesHom B a)).obj N)).val.app V y = y :=
  (toZariskiRingedSiteHom B Y.obj Y.property).pushforwardModulesToposIsoGeneral_inv_app_val_app
    _ V y

/-- The comparison of composite pushforwards for the lower route is restriction along
`baseChangeOpensIso B a` on sections. -/
private theorem pushforwardModulesCompIso_hom_val_app_zariskiSquareDirectImageIso (y) :
    ((pushforwardModulesCompIso (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a)
      (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)).hom.app N).val.app V y =
      N.val.map ((baseChangeOpensIso B a).hom.app V.unop).op y :=
  rfl

/-- The comparison of composite pushforwards for the upper route is the identity on sections. -/
private theorem pushforwardModulesCompIso_inv_val_app_zariskiSquareHom (y) :
    ((pushforwardModulesCompIso (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a)).inv.app N).val.app V y = y :=
  rfl

/-- The identification of the pushforward of modules along the Zariski morphism of `r` is the
identity on sections. -/
private theorem zariskiPushforwardModulesIso_hom_val_app_schemeHom (y) :
    ((schemeHom B a).zariskiPushforwardModulesIso.hom.app
      ((pushforwardModules (toZariskiRingedToposModulesHom B X.obj X.property)).obj N)).val.app
        V y = y :=
  (schemeHom B a).zariskiRingedSiteHom.pushforwardModulesToposIsoGeneral_hom_app_val_app
    _ V y

/-- The identification of the pushforward of modules along `ε_X`, read after the pushforward along
`r`, is the identity on sections. -/
private theorem pushforward_map_pushforwardModulesToposIsoGeneral_hom_val_app_toZariski (y) :
    ((SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).map
      ((toZariskiRingedSiteHom B X.obj X.property).pushforwardModulesToposIsoGeneral.hom.app
        N)).val.app V y = y :=
  (toZariskiRingedSiteHom B X.obj X.property).pushforwardModulesToposIsoGeneral_hom_app_val_app
    N _ y

/-- **The comparison of the composite direct images of `associatedModuleBaseChangeIso` is the
composite of the comparisons that build `factorizationTransportIso` at the square.**  This is the
hypothesis `hσ` of `Stacks.SheafOfModules.whiskered_leftAdjointUniq_eq_leftAdjointUniq` at the
square of `a`: on sections over an open `V` of `Y` both sides are restriction from the base change
`X ×_Y V` to the preimage `r⁻¹(V)`, every other factor being the identity there. -/
theorem pushforwardSquareIso_hom_app_eq_zariskiSquare :
    (SheafOfModules.pushforwardSquareIso.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
      (structureMap_comp_baseChangeOpensIso B a)).hom.app N =
    (SheafOfModules.pushforward.{u} (structureMap B Y.obj Y.property)).map
        ((smallEtaleRingedSiteHom B a).pushforwardModulesToposIsoGeneral.inv.app N) ≫
      (toZariskiRingedSiteHom B Y.obj Y.property).pushforwardModulesToposIsoGeneral.inv.app
        ((pushforwardModules (baseChangeRingedToposModulesHom B a)).obj N) ≫
      (pushforwardModulesCompIso (baseChangeRingedToposModulesHom B a)
        (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a)
        (zariskiSquareDirectImageIso B a)
        (fSharpSetComp_zariskiSquareDirectImageIso B a)).hom.app N ≫
      (pushforwardModulesCompIso (toZariskiRingedToposModulesHom B X.obj X.property)
        (schemeHom B a).zariskiRingedToposModulesHom (zariskiSquareHom B a) (Iso.refl _)
        (fSharpSetComp_zariskiSquareHom B a)).inv.app N ≫
      (schemeHom B a).zariskiPushforwardModulesIso.hom.app
        ((pushforwardModules (toZariskiRingedToposModulesHom B X.obj X.property)).obj N) ≫
      (SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).map
        ((toZariskiRingedSiteHom B X.obj X.property).pushforwardModulesToposIsoGeneral.hom.app
          N) := by
  refine eq_comp_of_val_app_apply _ _ _ _ _ _ _ (fun V x => ?_)
  refine Eq.trans ?_
    (pushforward_map_pushforwardModulesToposIsoGeneral_hom_val_app_toZariski B a N V _).symm
  refine Eq.trans ?_ (zariskiPushforwardModulesIso_hom_val_app_schemeHom B a N V _).symm
  refine Eq.trans ?_ (pushforwardModulesCompIso_inv_val_app_zariskiSquareHom B a N V _).symm
  refine Eq.trans ?_
    (pushforwardModulesCompIso_hom_val_app_zariskiSquareDirectImageIso B a N V _).symm
  refine Eq.trans ?_ (congrArg (N.val.map ((baseChangeOpensIso B a).hom.app V.unop).op)
    ((pushforwardModulesToposIsoGeneral_inv_val_app_toZariski B a N V _).trans
      (pushforward_map_pushforwardModulesToposIsoGeneral_inv_val_app_baseChange B a N V x))).symm
  rfl

end DirectImages

/-- **The comparison of the two routes round the square of `a` is the associated module of Stacks
03LC (1).**  `Stacks.SheafOfModules.factorizationTransportIso` at the square — the comparison
`r^* ⋙ (-)^a ≅ (-)^a ⋙ ε_a^*` read off the comparisons of pullbacks of the two factorizations of
the diagonal — is `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso B a`.

Both are comparisons of composite left adjoints by uniqueness, so this is
`Stacks.SheafOfModules.whiskered_leftAdjointUniq_eq_leftAdjointUniq`, whose hypothesis on the
comparisons of right adjoints is
`AlgebraicGeometry.SmallEtale.pushforwardSquareIso_hom_app_eq_zariskiSquare`. -/
theorem factorizationTransportIso_zariskiSquare :
    Stacks.SheafOfModules.factorizationTransportIso
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property) =
      associatedModuleBaseChangeIso B a :=
  Stacks.SheafOfModules.whiskered_leftAdjointUniq_eq_leftAdjointUniq
    (pullbackAdjPushforwardModules (zariskiSquareHom B a))
    (pullbackAdjPushforwardModules (schemeHom B a).zariskiRingedToposModulesHom)
    (pullbackAdjPushforwardModules (toZariskiRingedToposModulesHom B X.obj X.property))
    (pullbackAdjPushforwardModules (toZariskiRingedToposModulesHom B Y.obj Y.property))
    (pullbackAdjPushforwardModules (baseChangeRingedToposModulesHom B a))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (schemeHom B a).toRingCatSheafHom)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B X.obj X.property))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B Y.obj Y.property))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a))
    (pushforwardModulesCompIso (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a))
    (pushforwardModulesCompIso (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a)
      (zariskiSquareDirectImageIso B a) (fSharpSetComp_zariskiSquareDirectImageIso B a))
    (schemeHom B a).zariskiPushforwardModulesIso
    (toZariskiRingedSiteHom B X.obj X.property).pushforwardModulesToposIsoGeneral
    (toZariskiRingedSiteHom B Y.obj Y.property).pushforwardModulesToposIsoGeneral
    (smallEtaleRingedSiteHom B a).pushforwardModulesToposIsoGeneral
    (SheafOfModules.pushforwardSquareIso.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
      (structureMap_comp_baseChangeOpensIso B a))
    (pushforwardSquareIso_hom_app_eq_zariskiSquare B a)


end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallEtale

section TensorTranspose

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse of `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, unfolded: the unit of
the associated-module adjunction followed by the restriction of Stacks 03EL at `ε` (read through
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`) and of the two counits. -/
theorem restrictModuleTensorIso_inv_eq (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (restrictModuleTensorIso B S hS M N hM hN).inv =
      (associatedModuleAdjunction B S hS).unit.app _ ≫ (restrictModule B S hS).map
        ((Stacks.SheafOfModules.pullbackTensorIsoTransport (toZariskiRingedToposModulesHom B S hS)
            (pullbackModulesToZariskiIso B S hS) ((restrictModule B S hS).obj M)
            ((restrictModule B S hS).obj N)).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj
              ((associatedModule B S hS).obj ((restrictModule B S hS).obj M))).map
            ((associatedModuleAdjunction B S hS).counit.app N) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS).toRingedTopos.O).map
              ((associatedModuleAdjunction B S hS).counit.app M)).app N) :=
  rfl

/-- `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` is the transpose of Stacks 03EL at `ε`
along the associated-module adjunction, in the sense of
`Stacks.SheafOfModules.IsTensorTranspose`. -/
theorem isTensorTranspose_restrictModuleTensorIso
    (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    Stacks.SheafOfModules.IsTensorTranspose (X := (smallEtaleRingedSite B S hS).toRingedTopos)
      (Z := S.zariskiRingedSite.toRingedTopos) (toZariskiRingedToposModulesHom B S hS)
      (associatedModuleAdjunction B S hS) (pullbackModulesToZariskiIso B S hS) M N
      (restrictModuleTensorIso B S hS M N hM hN) := by
  unfold Stacks.SheafOfModules.IsTensorTranspose
  refine (restrictModuleTensorIso_inv_eq B S hS M N hM hN).trans ?_
  congr 1

/-- **The tensor product of two quasi-coherent modules on the small étale site is quasi-coherent.**
It is the associated module of the tensor product of the two restrictions
(`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` and the counits, which are isomorphisms
at quasi-coherent modules by `AlgebraicGeometry.SmallEtale.isIso_counit`), and that tensor product
is quasi-coherent by Stacks 01CE. -/
theorem isQuasicoherentOnSite_sheafTensor (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS).toRingedTopos.O).obj M).obj N).IsQuasicoherentOnSite :=
  have hM₀ : SheafOfModules.IsQuasicoherent ((restrictModule B S hS).obj M) :=
    isQuasicoherent_restrictModule B S hS M hM
  have hN₀ : SheafOfModules.IsQuasicoherent ((restrictModule B S hS).obj N) :=
    isQuasicoherent_restrictModule B S hS N hN
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (associatedModuleTensorIso B S hS _ _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS).toRingedTopos.O).mapIso
          (@asIso _ _ _ _ _ (isIso_counit B S hS M hM hM₀))).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS).toRingedTopos.O).obj M).mapIso
          (@asIso _ _ _ _ _ (isIso_counit B S hS N hN hN₀)))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _
      (isQuasicoherent_tensorSheaf_of_isQuasicoherent S _ _ hM₀ hN₀))

end TensorTranspose

section RestrictPullbackTensor

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` is the transpose of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` along the associated-module
adjunctions, in the sense of `Stacks.SheafOfModules.IsSquareTranspose`; this is
`AlgebraicGeometry.SmallEtale.associatedModule_map_restrictModulePullbackObjIso_hom`, with the
pullback along `r` spelled as the ringed-space pullback the square uses. -/
theorem isSquareTranspose_restrictModulePullbackObjIso
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) (hN : N.IsQuasicoherentOnSite) :
    Stacks.SheafOfModules.IsSquareTranspose
      (Lψ₁ := Stacks.RingedSpace.pullbackFunctor (schemeHom B a).toLRSHom.toShHom)
      (associatedModuleAdjunction B X.obj X.property)
      (associatedModuleAdjunction B Y.obj Y.property) (associatedModuleBaseChangeIso B a) N
      (restrictModulePullbackObjIso B a N hN).hom :=
  associatedModule_map_restrictModulePullbackObjIso_hom B a N hN

/-- **Restriction to the small Zariski sites carries Stacks 03EL for small étale base change to
Stacks 03EL for the morphism of schemes.**  For `a : X ⟶ Y` of a big étale site with underlying
morphism of schemes `r`, and quasi-coherent `𝒪`-modules `𝒢₁, 𝒢₂` on the small étale site of `Y`,

```
r^*((𝒢₁ ⊗ 𝒢₂)|_Y) --r^*(t_Y)--> r^*(𝒢₁|_Y ⊗ 𝒢₂|_Y) --01CD--> r^*(𝒢₁|_Y) ⊗ r^*(𝒢₂|_Y)
                                     --c ⊗ c--> (ε_a^*𝒢₁)|_X ⊗ (ε_a^*𝒢₂)|_X
```

is

```
r^*((𝒢₁ ⊗ 𝒢₂)|_Y) --c--> (ε_a^*(𝒢₁ ⊗ 𝒢₂))|_X --(03EL for ε_a)|_X--> (ε_a^*𝒢₁ ⊗ ε_a^*𝒢₂)|_X
                                     --t_X--> (ε_a^*𝒢₁)|_X ⊗ (ε_a^*𝒢₂)|_X
```

where `c` is `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso`, `t` is
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, `01CD` is
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso r` and Stacks 03EL for `ε_a` is the
transported comparison along `AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso`, that is
`AlgebraicGeometry.SmallEtale.baseChangeTensorIso B a 𝒢₁ 𝒢₂`.

This is `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_transpose` at the square of `a`,
whose comparison of the two routes is `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`
by `AlgebraicGeometry.SmallEtale.factorizationTransportIso_zariskiSquare`; the statement is
written through `type_of%` of that instance, so that it is that statement verbatim (the pullback
along `r` reads as `Stacks.RingedSpace.pullbackFunctor`, which is `Scheme.Modules.pullback r`). -/
theorem pullbackTensorIso_restrictModulePullbackObjIso
    (N₁ N₂ : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (h₁ : N₁.IsQuasicoherentOnSite) (h₂ : N₂.IsQuasicoherentOnSite) :
    type_of% (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_transpose
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property)
      (associatedModuleAdjunction B X.obj X.property)
      (associatedModuleAdjunction B Y.obj Y.property) (factorizationTransportIso_zariskiSquare B a)
      N₁ N₂
      ((schemeHom B a).pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits
        ((restrictModule B Y.obj Y.property).obj N₁) ((restrictModule B Y.obj Y.property).obj N₂))
      (restrictModuleTensorIso B Y.obj Y.property N₁ N₂ h₁ h₂)
      (isTensorTranspose_restrictModuleTensorIso B Y.obj Y.property N₁ N₂ h₁ h₂)
      (restrictModuleTensorIso B X.obj X.property
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₁)
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₂)
        (isQuasicoherentOnSite_pullback B a N₁ h₁) (isQuasicoherentOnSite_pullback B a N₂ h₂))
      (isTensorTranspose_restrictModuleTensorIso B X.obj X.property
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₁)
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₂)
        (isQuasicoherentOnSite_pullback B a N₁ h₁) (isQuasicoherentOnSite_pullback B a N₂ h₂))
      (restrictModulePullbackObjIso B a N₁ h₁).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a N₁ h₁)
      (restrictModulePullbackObjIso B a N₂ h₂).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a N₂ h₂)
      (restrictModulePullbackObjIso B a _
        (isQuasicoherentOnSite_sheafTensor B Y.obj Y.property N₁ N₂ h₁ h₂)).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a _
        (isQuasicoherentOnSite_sheafTensor B Y.obj Y.property N₁ N₂ h₁ h₂))) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_transpose
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property)
      (associatedModuleAdjunction B X.obj X.property)
      (associatedModuleAdjunction B Y.obj Y.property) (factorizationTransportIso_zariskiSquare B a)
      N₁ N₂
      ((schemeHom B a).pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits
        ((restrictModule B Y.obj Y.property).obj N₁) ((restrictModule B Y.obj Y.property).obj N₂))
      (restrictModuleTensorIso B Y.obj Y.property N₁ N₂ h₁ h₂)
      (isTensorTranspose_restrictModuleTensorIso B Y.obj Y.property N₁ N₂ h₁ h₂)
      (restrictModuleTensorIso B X.obj X.property
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₁)
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₂)
        (isQuasicoherentOnSite_pullback B a N₁ h₁) (isQuasicoherentOnSite_pullback B a N₂ h₂))
      (isTensorTranspose_restrictModuleTensorIso B X.obj X.property
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₁)
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N₂)
        (isQuasicoherentOnSite_pullback B a N₁ h₁) (isQuasicoherentOnSite_pullback B a N₂ h₂))
      (restrictModulePullbackObjIso B a N₁ h₁).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a N₁ h₁)
      (restrictModulePullbackObjIso B a N₂ h₂).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a N₂ h₂)
      (restrictModulePullbackObjIso B a _
        (isQuasicoherentOnSite_sheafTensor B Y.obj Y.property N₁ N₂ h₁ h₂)).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a _
        (isQuasicoherentOnSite_sheafTensor B Y.obj Y.property N₁ N₂ h₁ h₂))

end RestrictPullbackTensor

end AlgebraicGeometry.SmallEtale

end
