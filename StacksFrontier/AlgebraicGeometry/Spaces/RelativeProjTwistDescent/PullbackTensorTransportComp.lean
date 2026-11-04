module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSquare

/-!
# Stacks 03EL read through identifications of pullbacks: composition and squares

Let `φ : X ⟶ Y`, `ψ : Y ⟶ Z` and `χ : X ⟶ Z` be morphisms of ringed topoi, `χ` a composite of
`φ` and `ψ` in the sense of a comparison `τ` of geometric direct images carrying the composite
structure map to that of `χ`.  The comparison of Stacks 03EL is compatible with the comparison
`χ^* ≅ ψ^* ⋙ φ^*` of pullbacks: that is the composition law
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` of the base.

The functors that occur in practice are not literally pullbacks of modules along morphisms of
ringed topoi: the associated module `𝓕 ↦ 𝓕^a` of Stacks 03DX (2), the functor of the comparison
of Stacks 04M0, the pullback of modules along a morphism of schemes.  Each is identified with
such a pullback by a named isomorphism `α`, and its comparison of Stacks 03EL is the base one
read through `α`, `Stacks.SheafOfModules.pullbackTensorIsoTransport`.  This file proves that
these transported comparisons satisfy the composition law along *any* identification
`β : L_χ ≅ L_ψ ⋙ L_φ` of the functors which corresponds to the comparison of pullbacks under the
three identifications `α`, and, as a consequence, that they are compatible with any isomorphism
`L_ψ ⋙ L_φ ≅ L_ψ' ⋙ L_φ'` between two factorizations of one morphism.

Everything holds for ringed topoi at arbitrary and independent universes.  The square lemma of
the base, `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackTensorIso_squarePullbackIso`, is
stated for ringed topoi in a single universe and for the literal pullbacks; it does not apply to
the small étale ringed topoi of algebraic spaces and of schemes, whose sites have objects in a
larger universe than their sections, nor to functors only identified with pullbacks.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIsoTransport_comp`: **the transported comparisons of
  Stacks 03EL compose along an identification corresponding to the comparison of pullbacks.**
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_square`: **the transported comparisons of
  Stacks 03EL are compatible with an isomorphism between two factorizations**, as soon as that
  isomorphism corresponds to the comparisons of pullbacks of the two factorizations.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    {Z : AlgebraicGeometry.RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- The two one-variable actions of a curried bifunctor compose: a pair of composable pairs of
morphisms acts as the pair of composites. -/
private theorem bifunctor_map_comp {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    (P : 𝒜 ⥤ ℬ ⥤ 𝒞) {K K' K'' : 𝒜} {L L' L'' : ℬ} (a : K ⟶ K') (a' : K' ⟶ K'')
    (b : L ⟶ L') (b' : L' ⟶ L'') :
    (P.map a).app L ≫ (P.obj K').map b ≫ (P.map a').app L' ≫ (P.obj K'').map b' =
      (P.map (a ≫ a')).app L ≫ (P.obj K'').map (b ≫ b') := by
  rw [(P.map a').naturality_assoc b, Functor.map_comp, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]

section Comp

variable (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  {Lψ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)}
  {Lχ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (αφ : φ.pullbackModules ≅ Lφ) (αψ : ψ.pullbackModules ≅ Lψ) (αχ : χ.pullbackModules ≅ Lχ)

/-- **The transported comparisons of Stacks 03EL compose.**  Let `β : L_χ ≅ L_ψ ⋙ L_φ`
correspond to the comparison `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks of
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` under the identifications
`α_φ, α_ψ, α_χ` of the three functors with the pullbacks.  Then the comparison of Stacks 03EL
for `L_χ`, followed by `β` in each factor, is `β` at the tensor product, followed by `L_φ` of the
comparison for `L_ψ` and by the comparison for `L_φ`.

This is the composition law `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` read through
the identifications. -/
theorem pullbackTensorIsoTransport_comp (β : Lχ ≅ Lψ ⋙ Lφ)
    (hβ : ∀ M, (pullbackModulesCompIso φ ψ χ τ hτ).hom.app M ≫
        φ.pullbackModules.map (αψ.hom.app M) ≫ αφ.hom.app (Lψ.obj M) =
      αχ.hom.app M ≫ β.hom.app M)
    (F G : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O)) :
    (pullbackTensorIsoTransport χ αχ F G).hom ≫
        ((Tensor.sheafTensor X.O).map (β.hom.app F)).app (Lχ.obj G) ≫
          ((Tensor.sheafTensor X.O).obj (Lφ.obj (Lψ.obj F))).map (β.hom.app G) =
      β.hom.app (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        Lφ.map (pullbackTensorIsoTransport ψ αψ F G).hom ≫
          (pullbackTensorIsoTransport φ αφ (Lψ.obj F) (Lψ.obj G)).hom := by
  have hb : ∀ M, β.hom.app M = αχ.inv.app M ≫ (pullbackModulesCompIso φ ψ χ τ hτ).hom.app M ≫
      φ.pullbackModules.map (αψ.hom.app M) ≫ αφ.hom.app (Lψ.obj M) := fun M =>
    (Iso.eq_inv_comp (αχ.app M)).2 (hβ M).symm
  have hlaw := pullbackTensorIso_hom_app_comp φ ψ χ τ hτ F G
  have hnat := pullbackTensorIso_hom_naturality_map φ (αψ.hom.app F) (αψ.hom.app G)
  have hΦ : ∀ {M M' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (k : M ⟶ M'),
      αφ.hom.app M ≫ Lφ.map k ≫ αφ.inv.app M' = φ.pullbackModules.map k := fun k => by
    rw [← αφ.hom.naturality_assoc k, Iso.hom_inv_id_app, Category.comp_id]
  -- the left side
  have hL : (pullbackTensorIsoTransport χ αχ F G).hom ≫
        ((Tensor.sheafTensor X.O).map (β.hom.app F)).app (Lχ.obj G) ≫
          ((Tensor.sheafTensor X.O).obj (Lφ.obj (Lψ.obj F))).map (β.hom.app G) =
      αχ.inv.app _ ≫ (pullbackModulesCompIso φ ψ χ τ hτ).hom.app _ ≫
        φ.pullbackModules.map ((pullbackTensorIso ψ).hom.app (F, G)) ≫
          (pullbackTensorIso φ).hom.app (ψ.pullbackModules.obj F, ψ.pullbackModules.obj G) ≫
            ((Tensor.sheafTensor X.O).map (φ.pullbackModules.map (αψ.hom.app F))).app _ ≫
              ((Tensor.sheafTensor X.O).obj _).map (φ.pullbackModules.map (αψ.hom.app G)) ≫
                ((Tensor.sheafTensor X.O).map (αφ.hom.app (Lψ.obj F))).app _ ≫
                  ((Tensor.sheafTensor X.O).obj _).map (αφ.hom.app (Lψ.obj G)) := by
    simp only [pullbackTensorIsoTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc, Functor.prod_obj]
    rw [bifunctor_map_comp (K'' := Lφ.obj (Lψ.obj F)) _ (αχ.hom.app F) (β.hom.app F)
        (αχ.hom.app G) (β.hom.app G), (hβ F).symm, (hβ G).symm,
      ← bifunctor_map_comp _ ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F),
      ← bifunctor_map_comp _ (φ.pullbackModules.map (αψ.hom.app F))]
    simp only [Functor.uncurry_obj_map, Functor.prod_obj, Functor.comp_obj] at hlaw ⊢
    rw [reassoc_of% hlaw]
    rfl
  have hnat' : φ.pullbackModules.map (((Tensor.sheafTensor Y.O).map (αψ.hom.app F)).app
          (ψ.pullbackModules.obj G)) ≫
        φ.pullbackModules.map (((Tensor.sheafTensor Y.O).obj (Lψ.obj F)).map (αψ.hom.app G)) ≫
          (pullbackTensorIso φ).hom.app (Lψ.obj F, Lψ.obj G) =
      (pullbackTensorIso φ).hom.app (ψ.pullbackModules.obj F, ψ.pullbackModules.obj G) ≫
        ((Tensor.sheafTensor X.O).map (φ.pullbackModules.map (αψ.hom.app F))).app _ ≫
          ((Tensor.sheafTensor X.O).obj _).map (φ.pullbackModules.map (αψ.hom.app G)) := by
    rw [← Functor.map_comp_assoc]
    exact hnat
  rw [hL, hb]
  simp only [pullbackTensorIsoTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hΦ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc φ.pullbackModules (αψ.hom.app _) (αψ.inv.app _),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.prod_obj] at hnat' ⊢
  rw [reassoc_of% hnat']
  rfl

end Comp

section Square

universe w₁ v₁ u₁ w₂ v₂ u₂

variable {Y₁ : AlgebraicGeometry.RingedTopos.{v₁, u₁, w₁}}
    {Y₂ : AlgebraicGeometry.RingedTopos.{v₂, u₂, w₂}}
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Y₁.J.HasSheafCompose (forget RingCat.{w₁})] [Y₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [HasWeakSheafify Y₁.J AddCommGrpCat.{w₁}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{w₂}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  (φ₁ : RingedToposHom X Y₁) (ψ₁ : RingedToposHom Y₁ Z)
  (φ₂ : RingedToposHom X Y₂) (ψ₂ : RingedToposHom Y₂ Z) (χ : RingedToposHom X Z)
  (τ₁ : φ₁.toToposHom.pushforward ⋙ ψ₁.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₁ : fSharpSetComp φ₁ ψ₁ ≫
    τ₁.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (τ₂ : φ₂.toToposHom.pushforward ⋙ ψ₂.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₂ : fSharpSetComp φ₂ ψ₂ ≫
    τ₂.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ₁ : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  {Lψ₁ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O)}
  {Lφ₂ : _root_.SheafOfModules.{w₂} (Tensor.ringSheaf Y₂.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  {Lψ₂ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w₂} (Tensor.ringSheaf Y₂.O)}
  (αφ₁ : φ₁.pullbackModules ≅ Lφ₁) (αψ₁ : ψ₁.pullbackModules ≅ Lψ₁)
  (αφ₂ : φ₂.pullbackModules ≅ Lφ₂) (αψ₂ : ψ₂.pullbackModules ≅ Lψ₂)

/-- The identification `χ^* ≅ L_ψ ⋙ L_φ` read off the comparison of pullbacks of a
factorization of `χ` through `φ` and `ψ` and the identifications `α_φ`, `α_ψ`. -/
private def transportCompIso (φ : RingedToposHom X Y₁) (ψ : RingedToposHom Y₁ Z)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
    (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
    {Lφ : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O) ⥤
      _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
    {Lψ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
      _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O)}
    (αφ : φ.pullbackModules ≅ Lφ) (αψ : ψ.pullbackModules ≅ Lψ) :
    χ.pullbackModules ≅ Lψ ⋙ Lφ :=
  pullbackModulesCompIso φ ψ χ τ hτ ≪≫ Functor.isoWhiskerRight αψ φ.pullbackModules ≪≫
    Functor.isoWhiskerLeft Lψ αφ

/-- The comparison of Stacks 03EL for `χ` followed by `transportCompIso` in each factor is the
composite of the transported comparisons along the factorization. -/
private theorem pullbackTensorIso_transportCompIso (φ : RingedToposHom X Y₁)
    (ψ : RingedToposHom Y₁ Z)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
    (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
    {Lφ : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O) ⥤
      _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
    {Lψ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
      _root_.SheafOfModules.{w₁} (Tensor.ringSheaf Y₁.O)}
    (αφ : φ.pullbackModules ≅ Lφ) (αψ : ψ.pullbackModules ≅ Lψ)
    (F G : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O)) :
    (pullbackTensorIsoTransport χ (Iso.refl _) F G).hom ≫
        ((Tensor.sheafTensor X.O).map ((transportCompIso χ φ ψ τ hτ αφ αψ).hom.app F)).app
          (χ.pullbackModules.obj G) ≫
          ((Tensor.sheafTensor X.O).obj (Lφ.obj (Lψ.obj F))).map
            ((transportCompIso χ φ ψ τ hτ αφ αψ).hom.app G) =
      (transportCompIso χ φ ψ τ hτ αφ αψ).hom.app (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        Lφ.map (pullbackTensorIsoTransport ψ αψ F G).hom ≫
          (pullbackTensorIsoTransport φ αφ (Lψ.obj F) (Lψ.obj G)).hom :=
  pullbackTensorIsoTransport_comp φ ψ χ τ hτ αφ αψ (Iso.refl _)
    (transportCompIso χ φ ψ τ hτ αφ αψ) (fun _ => (Category.id_comp _).symm) F G

/-- **The transported comparisons of Stacks 03EL are compatible with an isomorphism between two
factorizations.**  Let `χ` factor through `φ₁, ψ₁` and through `φ₂, ψ₂`, and let
`m : L_ψ₁ ⋙ L_φ₁ ≅ L_ψ₂ ⋙ L_φ₂` correspond to the two comparisons of pullbacks under the
identifications `α` — that is, the comparison `χ^* ≅ ψ₁^* ⋙ φ₁^*` read through `α_ψ₁, α_φ₁` and
followed by `m` is the comparison `χ^* ≅ ψ₂^* ⋙ φ₂^*` read through `α_ψ₂, α_φ₂`.  Then going
round the square through `L_ψ₁, L_φ₁` and then `m`, or through `m` and then `L_ψ₂, L_φ₂`, gives
the same comparison `L_φ₁ L_ψ₁(F ⊗ G) ⟶ L_φ₂ L_ψ₂ F ⊗ L_φ₂ L_ψ₂ G`.

This is the universe-polymorphic, transported form of
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackTensorIso_squarePullbackIso`: the composition
law `Stacks.SheafOfModules.pullbackTensorIsoTransport_comp` along each factorization, the two
compared through `m`. -/
theorem pullbackTensorIsoTransport_square (m : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂)
    (hm : ∀ M, (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁).hom.app M ≫
        φ₁.pullbackModules.map (αψ₁.hom.app M) ≫ αφ₁.hom.app (Lψ₁.obj M) ≫ m.hom.app M =
      (pullbackModulesCompIso φ₂ ψ₂ χ τ₂ hτ₂).hom.app M ≫
        φ₂.pullbackModules.map (αψ₂.hom.app M) ≫ αφ₂.hom.app (Lψ₂.obj M))
    (F G : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O)) :
    Lφ₁.map (pullbackTensorIsoTransport ψ₁ αψ₁ F G).hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map (m.hom.app F)).app (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (Lφ₂.obj (Lψ₂.obj F))).map (m.hom.app G) =
      m.hom.app (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        Lφ₂.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ αφ₂ (Lψ₂.obj F) (Lψ₂.obj G)).hom := by
  have h₁ := pullbackTensorIso_transportCompIso χ φ₁ ψ₁ τ₁ hτ₁ αφ₁ αψ₁ F G
  have h₂ := pullbackTensorIso_transportCompIso (Y₁ := Y₂) χ φ₂ ψ₂ τ₂ hτ₂ αφ₂ αψ₂ F G
  have hm' : ∀ M, @CategoryStruct.comp _ _ (χ.pullbackModules.obj M) (Lφ₁.obj (Lψ₁.obj M))
      (Lφ₂.obj (Lψ₂.obj M)) ((transportCompIso χ φ₁ ψ₁ τ₁ hτ₁ αφ₁ αψ₁).hom.app M)
      (m.hom.app M) =
      (transportCompIso (Y₁ := Y₂) χ φ₂ ψ₂ τ₂ hτ₂ αφ₂ αψ₂).hom.app M := fun M => by
    simp only [transportCompIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
    exact hm M
  rw [← Iso.cancel_iso_hom_left ((transportCompIso χ φ₁ ψ₁ τ₁ hτ₁ αφ₁ αψ₁).app
    (((Tensor.sheafTensor Z.O).obj F).obj G)), Iso.app_hom, ← reassoc_of% h₁,
    reassoc_of% (hm' _), ← h₂,
    bifunctor_map_comp (K' := Lφ₁.obj (Lψ₁.obj F)) (K'' := Lφ₂.obj (Lψ₂.obj F))
      (L' := Lφ₁.obj (Lψ₁.obj G)) _ ((transportCompIso χ φ₁ ψ₁ τ₁ hτ₁ αφ₁ αψ₁).hom.app F)
      (m.hom.app F) ((transportCompIso χ φ₁ ψ₁ τ₁ hτ₁ αφ₁ αψ₁).hom.app G) (m.hom.app G), hm' F,
    hm' G]

end Square

end Stacks.SheafOfModules

end
