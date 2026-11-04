module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingTensor

/-!
# The lax comparison of a composite adjunction with tensor products

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions and `ι : R₂ ⋙ R₁ ≅ R`, and suppose both left adjoints
carry comparisons `t₁`, `t₂` with tensor products, natural in both factors (in the application,
Stacks 03EL for the associated module of Stacks 03DU and for the comparison of Stacks 04M0).  The
transpose along the composite adjunction `L₁ ⋙ L₂ ⊣ R` of

`L(R P ⊗ R Q) ⟶ L R P ⊗ L R Q ⟶ P ⊗ Q`

(the two comparisons, then the counits) is computed from the two lax comparisons of `R₁` and of
`R₂`.  This is the splitting by which the identification `N ≅ (N_Zar)^a` of
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` is compared with tensor products: its
inverse is the counit of `AlgebraicGeometry.Space.zariskiReadingAdjunction`, the composite of the
adjunction of Stacks 03DU with the equivalence of Stacks 04M0.  These are steps of the proof that
`ψ` of Stacks 084D is a homomorphism of graded algebras.

## Main results

* `AlgebraicGeometry.Space.Adjunction.ofNatIsoRight_comp_counit_app`: the counit of a composite
  adjunction whose right adjoint is replaced by an isomorphic one.
* `AlgebraicGeometry.Space.Adjunction.homEquiv_ofNatIsoRight_comp_tensor`: **the lax comparison
  of a composite adjunction splits**, at arbitrary categories.
* `AlgebraicGeometry.Space.homEquiv_ofNatIsoRight_comp_tensorCounitComposite`: the same when the
  second adjunction presents the direct image along a morphism of ringed sites and its comparison
  is Stacks 03EL; the second lax comparison is then
  `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite`.
* `Stacks.SheafOfModules.homEquiv_comp_reindex_tensor_of_heq`: the same when the second
  adjunction is an equivalence equal to a reindexing, with the ring sheaves, the equivalence, the
  tensor products and the comparison of Stacks 03EL as variables equal to the reindexing data.
* `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor`: its instance at the Zariski
  reading adjunction of a represented algebraic space, stated in the spellings of
  `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` and of the associated-module
  adjunction.

## Implementation notes

The instance at the Zariski reading adjunction is stated with `type_of%` and split into three
declarations, each fixing some of the arguments, so that each stays within the heartbeat budget.
The ring sheaves, the equivalence and the tensor products of
`Stacks.SheafOfModules.homEquiv_comp_reindex_tensor_of_heq` are variables: identifying two
spellings of a composite of morphisms (for instance the étale structure sheaf of the scheme
written as the structure sheaf of its small étale site or as the ring sheaf of its small étale
ringed site) exhausts the heartbeat budget, while the equations between two spellings of a
functor or of a sheaf of rings are checked by `rfl` at once.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory


namespace AlgebraicGeometry.Space


section Abstract

variable {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
  {L₁ : CX ⥤ CY} {R₁ : CY ⥤ CX} (adj₁ : L₁ ⊣ R₁) {L₂ : CY ⥤ CZ} {R₂ : CZ ⥤ CY} (adj₂ : L₂ ⊣ R₂)
  {R : CZ ⥤ CX} (ι : R₂ ⋙ R₁ ≅ R)

/-- The counit of a composite adjunction whose right adjoint is replaced by an isomorphic one. -/
theorem Adjunction.ofNatIsoRight_comp_counit_app (P : CZ) :
    ((adj₁.comp adj₂).ofNatIsoRight ι).counit.app P =
      L₂.map (L₁.map (ι.inv.app P) ≫ adj₁.counit.app (R₂.obj P)) ≫ adj₂.counit.app P := by
  have h := Adjunction.homEquiv_ofNatIsoRight_symm_apply (adj₁.comp adj₂) ι (𝟙 (R.obj P))
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Adjunction.comp_counit_app] at h
  rw [h, Functor.map_comp, Category.assoc]
  rfl

/-- A bifunctor applied to two composites, its second factors moved past the first: the
naturality of the image of a morphism under a bifunctor. -/
theorem bifunctor_map_comp_app_comp_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C ⥤ D) {X X' X'' Y Y' Y'' : C} (a : X ⟶ X') (a' : X' ⟶ X'') (b : Y ⟶ Y')
    (b' : Y' ⟶ Y'') :
    (F.map (a ≫ a')).app Y ≫ (F.obj X'').map (b ≫ b') =
      (F.map a).app Y ≫ (F.obj X').map b ≫ (F.obj X').map b' ≫ (F.map a').app Y'' := by
  rw [F.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    ← (F.map a').naturality_assoc b, ← (F.map a').naturality b']

/-- A comparison `t` of a functor with tensor products, natural in both factors, moves the
images of two morphisms under the functor past it. -/
theorem comp_bifunctor_map_comp_of_natural {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (tC : C ⥤ C ⥤ C) (tD : D ⥤ D ⥤ D)
    (t : ∀ M N : C, F.obj ((tC.obj M).obj N) ⟶ (tD.obj (F.obj M)).obj (F.obj N))
    (ht : ∀ {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N'),
      F.map ((tC.map a).app N ≫ (tC.obj M').map b) ≫ t M' N' =
        t M N ≫ (tD.map (F.map a)).app (F.obj N) ≫ (tD.obj (F.obj M')).map (F.map b))
    {M M' N N' : C} {A B : D} (f : M ⟶ M') (g : N ⟶ N') (e : F.obj M' ⟶ A)
    (e' : F.obj N' ⟶ B) :
    t M N ≫ (tD.map (F.map f ≫ e)).app (F.obj N) ≫ (tD.obj A).map (F.map g ≫ e') =
      F.map ((tC.map f).app N ≫ (tC.obj M').map g) ≫ t M' N' ≫
        (tD.obj (F.obj M')).map e' ≫ (tD.map e).app B := by
  rw [reassoc_of% (ht f g), bifunctor_map_comp_app_comp_map_comp tD]

variable (tX : CX ⥤ CX ⥤ CX) (tY : CY ⥤ CY ⥤ CY) (tZ : CZ ⥤ CZ ⥤ CZ)
  (t₁ : ∀ M N : CX, L₁.obj ((tX.obj M).obj N) ⟶ (tY.obj (L₁.obj M)).obj (L₁.obj N))
  (ht₁ : ∀ {M M' N N' : CX} (a : M ⟶ M') (b : N ⟶ N'),
    L₁.map ((tX.map a).app N ≫ (tX.obj M').map b) ≫ t₁ M' N' =
      t₁ M N ≫ (tY.map (L₁.map a)).app (L₁.obj N) ≫ (tY.obj (L₁.obj M')).map (L₁.map b))
  (t₂ : ∀ M N : CY, L₂.obj ((tY.obj M).obj N) ⟶ (tZ.obj (L₂.obj M)).obj (L₂.obj N))
  (ht₂ : ∀ {M M' N N' : CY} (a : M ⟶ M') (b : N ⟶ N'),
    L₂.map ((tY.map a).app N ≫ (tY.obj M').map b) ≫ t₂ M' N' =
      t₂ M N ≫ (tZ.map (L₂.map a)).app (L₂.obj N) ≫ (tZ.obj (L₂.obj M')).map (L₂.map b))

include ht₁ ht₂ in
/-- **The lax comparison of a composite of two adjunctions with tensor products splits.**  For
adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, an identification `ι : R₂ ⋙ R₁ ≅ R` and comparisons `t₁`, `t₂`
of the left adjoints with tensor products natural in both factors, the transpose along the
composite adjunction of the comparison `L(R P ⊗ R Q) ⟶ L R P ⊗ L R Q ⟶ P ⊗ Q` (the two
comparisons, then maps `ε` that factor through `ι` and maps `e₁`, `e₂` — in practice the counits)
is the transport along `ι` of the transpose `c₁` along `L₁ ⊣ R₁` built from `t₁` and `e₁`, followed
by `R₁` of the transpose `c₂` along `L₂ ⊣ R₂` built from `t₂` and `e₂`. -/
theorem Adjunction.homEquiv_ofNatIsoRight_comp_tensor (P Q : CZ)
    (εP : L₂.obj (L₁.obj (R.obj P)) ⟶ P) (εQ : L₂.obj (L₁.obj (R.obj Q)) ⟶ Q)
    (e₁P : L₁.obj (R₁.obj (R₂.obj P)) ⟶ R₂.obj P) (e₁Q : L₁.obj (R₁.obj (R₂.obj Q)) ⟶ R₂.obj Q)
    (e₂P : L₂.obj (R₂.obj P) ⟶ P) (e₂Q : L₂.obj (R₂.obj Q) ⟶ Q)
    (hεP : εP = L₂.map (L₁.map (ι.inv.app P) ≫ e₁P) ≫ e₂P)
    (hεQ : εQ = L₂.map (L₁.map (ι.inv.app Q) ≫ e₁Q) ≫ e₂Q)
    (c₁ : (tX.obj (R₁.obj (R₂.obj P))).obj (R₁.obj (R₂.obj Q)) ⟶
      R₁.obj ((tY.obj (R₂.obj P)).obj (R₂.obj Q)))
    (hc₁ : c₁ = adj₁.unit.app _ ≫ R₁.map (t₁ (R₁.obj (R₂.obj P)) (R₁.obj (R₂.obj Q)) ≫
      (tY.obj (L₁.obj (R₁.obj (R₂.obj P)))).map e₁Q ≫ (tY.map e₁P).app (R₂.obj Q)))
    (c₂ : (tY.obj (R₂.obj P)).obj (R₂.obj Q) ⟶ R₂.obj ((tZ.obj P).obj Q))
    (hc₂ : c₂ = adj₂.unit.app _ ≫ R₂.map (t₂ (R₂.obj P) (R₂.obj Q) ≫
      (tZ.obj (L₂.obj (R₂.obj P))).map e₂Q ≫ (tZ.map e₂P).app Q)) :
    ((adj₁.comp adj₂).ofNatIsoRight ι).homEquiv _ _
        (L₂.map (t₁ (R.obj P) (R.obj Q)) ≫ t₂ (L₁.obj (R.obj P)) (L₁.obj (R.obj Q)) ≫
          (tZ.map εP).app (L₂.obj (L₁.obj (R.obj Q))) ≫ (tZ.obj P).map εQ) =
      (tX.map (ι.inv.app P)).app (R.obj Q) ≫ (tX.obj (R₁.obj (R₂.obj P))).map (ι.inv.app Q) ≫
        c₁ ≫ R₁.map c₂ ≫ ι.hom.app ((tZ.obj P).obj Q) := by
  have hc₁' := hc₁.trans (adj₁.homEquiv_unit _ _ _).symm
  have hc₂' := hc₂.trans (adj₂.homEquiv_unit _ _ _).symm
  subst hεP hεQ hc₁' hc₂'
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
    comp_bifunctor_map_comp_of_natural L₂ tY tZ t₂ ht₂, ← Category.assoc (L₂.map (t₁ _ _)),
    ← L₂.map_comp, Adjunction.homEquiv_naturality_left,
    comp_bifunctor_map_comp_of_natural L₁ tX tY t₁ ht₁, Category.assoc (L₁.map _),
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  rfl

end Abstract

section TensorCounitSplit

open Stacks.SheafOfModules

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : RingedSite.HomGeneral X Y)
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

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The lax comparison of a composite adjunction ending in a presentation of a direct image
splits.**  `AlgebraicGeometry.Space.Adjunction.homEquiv_ofNatIsoRight_comp_tensor` when the second
adjunction `L ⊣ f_*` presents the direct image along a morphism of ringed sites `f` and its
comparison with tensor products is Stacks 03EL read through `α : f^* ≅ L`: the second lax
comparison is `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite`. -/
theorem homEquiv_ofNatIsoRight_comp_tensorCounitComposite {CX : Type*} [Category CX]
    {L₁ : CX ⥤ _root_.SheafOfModules.{w} (Tensor.ringSheaf Y.toRingedTopos.O)}
    {R₁ : _root_.SheafOfModules.{w} (Tensor.ringSheaf Y.toRingedTopos.O) ⥤ CX} (adj₁ : L₁ ⊣ R₁)
    {φ : Tensor.ringSheaf Y.toRingedTopos.O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj (Tensor.ringSheaf X.toRingedTopos.O)}
    (adj₂ : L ⊣ _root_.SheafOfModules.pushforward.{w} φ)
    {R : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.toRingedTopos.O) ⥤ CX}
    (ι : _root_.SheafOfModules.pushforward.{w} φ ⋙ R₁ ≅ R) (tX : CX ⥤ CX ⥤ CX)
    (t₁ : ∀ M N : CX, L₁.obj ((tX.obj M).obj N) ⟶
      ((Tensor.sheafTensor Y.toRingedTopos.O).obj (L₁.obj M)).obj (L₁.obj N))
    (ht₁ : ∀ {M M' N N' : CX} (a : M ⟶ M') (b : N ⟶ N'),
      L₁.map ((tX.map a).app N ≫ (tX.obj M').map b) ≫ t₁ M' N' =
        t₁ M N ≫ ((Tensor.sheafTensor Y.toRingedTopos.O).map (L₁.map a)).app (L₁.obj N) ≫
          ((Tensor.sheafTensor Y.toRingedTopos.O).obj (L₁.obj M')).map (L₁.map b))
    (P Q : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.toRingedTopos.O))
    (εP : L.obj (L₁.obj (R.obj P)) ⟶ P) (εQ : L.obj (L₁.obj (R.obj Q)) ⟶ Q)
    (e₁P : L₁.obj (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj P)) ⟶
      (_root_.SheafOfModules.pushforward.{w} φ).obj P)
    (e₁Q : L₁.obj (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj Q)) ⟶
      (_root_.SheafOfModules.pushforward.{w} φ).obj Q)
    (hεP : εP = L.map (L₁.map (ι.inv.app P) ≫ e₁P) ≫ adj₂.counit.app P)
    (hεQ : εQ = L.map (L₁.map (ι.inv.app Q) ≫ e₁Q) ≫ adj₂.counit.app Q)
    (c₁ : (tX.obj (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj P))).obj
        (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj Q)) ⟶
      R₁.obj (((Tensor.sheafTensor Y.toRingedTopos.O).obj
        ((_root_.SheafOfModules.pushforward.{w} φ).obj P)).obj
          ((_root_.SheafOfModules.pushforward.{w} φ).obj Q)))
    (hc₁ : c₁ = adj₁.unit.app _ ≫
      R₁.map (t₁ (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj P))
      (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj Q)) ≫
      ((Tensor.sheafTensor Y.toRingedTopos.O).obj
        (L₁.obj (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj P)))).map e₁Q ≫
      ((Tensor.sheafTensor Y.toRingedTopos.O).map e₁P).app
        ((_root_.SheafOfModules.pushforward.{w} φ).obj Q))) :
    ((adj₁.comp adj₂).ofNatIsoRight ι).homEquiv _ _
        (L.map (t₁ (R.obj P) (R.obj Q)) ≫
          (pullbackTensorIsoTransport f.toRingedToposHom.toRingedToposModulesHom α
            (L₁.obj (R.obj P)) (L₁.obj (R.obj Q))).hom ≫
          ((Tensor.sheafTensor X.toRingedTopos.O).map εP).app (L.obj (L₁.obj (R.obj Q))) ≫
          ((Tensor.sheafTensor X.toRingedTopos.O).obj P).map εQ) =
      ((tX.map (ι.inv.app P)).app (R.obj Q) ≫
        (tX.obj (R₁.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj P))).map (ι.inv.app Q)) ≫
        c₁ ≫ R₁.map (f.tensorCounitComposite α adj₂ P Q) ≫ ι.hom.app _ :=
  (Adjunction.homEquiv_ofNatIsoRight_comp_tensor adj₁ adj₂ ι tX
    (Tensor.sheafTensor Y.toRingedTopos.O) (Tensor.sheafTensor X.toRingedTopos.O) t₁ ht₁
    (fun M N => (pullbackTensorIsoTransport f.toRingedToposHom.toRingedToposModulesHom α M N).hom)
    (fun a b => pullbackTensorIsoTransport_hom_naturality _ α a b) P Q εP εQ e₁P e₁Q _ _ hεP hεQ
    c₁ hc₁ _ rfl).trans (Category.assoc _ _ _).symm

end TensorCounitSplit


end AlgebraicGeometry.Space

namespace Stacks.SheafOfModules

section ReindexSpellings

universe uu v w

open AlgebraicGeometry.Space

variable {C : Type uu} [Category.{v} C] {C' : Type uu} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (O : Sheaf J CommRingCat.{w})
  [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J']
  [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']

/-- **The lax comparison of a composite adjunction ending in a reindexing, at arbitrary
spellings.**  `AlgebraicGeometry.Space.Adjunction.homEquiv_ofNatIsoRight_comp_tensor` when the
second adjunction is an equivalence `E` equal to the reindexing equivalence along `e`, its
comparison `t₂` with tensor products equal to Stacks 03EL at the reindexing, and the tensor
products `tY`, `tZ` equal to the tensor product sheaves.  The ring sheaves, `E`, `tY`, `tZ` and
`t₂` are variables, each with an equation to the reindexing construction, so that an instance is
stated in the spelling of its arguments.  The transpose of
`L(R P ⊗ R Q) ⟶ L R P ⊗ L R Q ⟶ P ⊗ Q` (the two comparisons, then the counits of `adj`) is the
transport along `ι` of the lax comparison of `R₁` followed by `R₁` of the lax comparison of the
inverse of `E`. -/
theorem homEquiv_comp_reindex_tensor_of_heq {CX : Type*} [Category CX]
    (Rs : Sheaf J RingCat.{w}) (hRs : Rs = Tensor.ringSheaf O)
    (Rt : Sheaf J' RingCat.{w}) (hRt : Rt = reindexRing J' e (Tensor.ringSheaf O))
    (E : _root_.SheafOfModules.{w} Rs ≌ _root_.SheafOfModules.{w} Rt)
    (hE : HEq E (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)))
    (tY : _root_.SheafOfModules.{w} Rs ⥤ _root_.SheafOfModules.{w} Rs ⥤
      _root_.SheafOfModules.{w} Rs)
    (htY : HEq tY (Tensor.sheafTensor.{uu, v, w, w, w} O))
    (tZ : _root_.SheafOfModules.{w} Rt ⥤ _root_.SheafOfModules.{w} Rt ⥤
      _root_.SheafOfModules.{w} Rt)
    (htZ : HEq tZ (Tensor.sheafTensor.{uu, v, w, w, w} (reindexCommRing J' e O)))
    {L₁ : CX ⥤ _root_.SheafOfModules.{w} Rs} {R₁ : _root_.SheafOfModules.{w} Rs ⥤ CX}
    (adj₁ : L₁ ⊣ R₁) {R : _root_.SheafOfModules.{w} Rt ⥤ CX} (ι : E.inverse ⋙ R₁ ≅ R)
    (adj : L₁ ⋙ E.functor ⊣ R) (hadj : adj = (adj₁.comp E.toAdjunction).ofNatIsoRight ι)
    (tX : CX ⥤ CX ⥤ CX)
    (t₁ : ∀ M N : CX, L₁.obj ((tX.obj M).obj N) ⟶ (tY.obj (L₁.obj M)).obj (L₁.obj N))
    (ht₁ : ∀ {M M' N N' : CX} (a : M ⟶ M') (b : N ⟶ N'),
      L₁.map ((tX.map a).app N ≫ (tX.obj M').map b) ≫ t₁ M' N' =
        t₁ M N ≫ (tY.map (L₁.map a)).app (L₁.obj N) ≫ (tY.obj (L₁.obj M')).map (L₁.map b))
    (t₂ : ∀ M N : _root_.SheafOfModules.{w} Rs, E.functor.obj ((tY.obj M).obj N) ⟶
      (tZ.obj (E.functor.obj M)).obj (E.functor.obj N))
    (ht₂ : HEq t₂ (fun M N => (pullbackTensorIsoTransport (reindexRingedToposModulesHom J' e O)
      (pullbackModulesReindexIso J' e O) M N).hom))
    (P Q : _root_.SheafOfModules.{w} Rt) :
    adj.homEquiv ((tX.obj (R.obj P)).obj (R.obj Q)) ((tZ.obj P).obj Q)
      (E.functor.map (t₁ (R.obj P) (R.obj Q)) ≫
        t₂ (L₁.obj (R.obj P)) (L₁.obj (R.obj Q)) ≫
        (tZ.map (adj.counit.app P)).app (E.functor.obj (L₁.obj (R.obj Q))) ≫
        (tZ.obj P).map (adj.counit.app Q)) =
      ((tX.map (ι.inv.app P)).app (R.obj Q) ≫
          (tX.obj (R₁.obj (E.inverse.obj P))).map (ι.inv.app Q)) ≫
        (adj₁.unit.app _ ≫ R₁.map (t₁ (R₁.obj (E.inverse.obj P)) (R₁.obj (E.inverse.obj Q)) ≫
          (tY.obj (L₁.obj (R₁.obj (E.inverse.obj P)))).map (adj₁.counit.app (E.inverse.obj Q)) ≫
          (tY.map (adj₁.counit.app (E.inverse.obj P))).app (E.inverse.obj Q))) ≫
        R₁.map (E.toAdjunction.unit.app ((tY.obj (E.inverse.obj P)).obj (E.inverse.obj Q)) ≫
          E.inverse.map (t₂ (E.inverse.obj P) (E.inverse.obj Q) ≫
            (tZ.obj (E.functor.obj (E.inverse.obj P))).map (E.toAdjunction.counit.app Q) ≫
            (tZ.map (E.toAdjunction.counit.app P)).app Q)) ≫ ι.hom.app ((tZ.obj P).obj Q) := by
  subst hadj hRs hRt
  obtain rfl := eq_of_heq hE
  obtain rfl := eq_of_heq htY
  obtain rfl := eq_of_heq htZ
  obtain rfl := eq_of_heq ht₂
  have h := Adjunction.homEquiv_ofNatIsoRight_comp_tensor adj₁
    (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).toAdjunction ι tX
    (Tensor.sheafTensor.{uu, v, w, w, w} O)
    (Tensor.sheafTensor.{uu, v, w, w, w} (reindexCommRing J' e O)) t₁ ht₁
    (fun M N => (pullbackTensorIsoTransport (reindexRingedToposModulesHom J' e O)
      (pullbackModulesReindexIso J' e O) M N).hom)
    (fun a b => pullbackTensorIsoTransport_hom_naturality (reindexRingedToposModulesHom J' e O)
      (pullbackModulesReindexIso J' e O) a b)
    P Q _ _ _ _ _ _
    (Adjunction.ofNatIsoRight_comp_counit_app adj₁
      (L₂ := (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).functor)
      (R₂ := (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).inverse)
      (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).toAdjunction ι P)
    (Adjunction.ofNatIsoRight_comp_counit_app adj₁
      (L₂ := (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).functor)
      (R₂ := (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).inverse)
      (reindexEquivalence.{w, w, uu, v, uu, v} (J' := J') e (Tensor.ringSheaf O)).toAdjunction ι Q)
    _ rfl _ rfl
  exact h.trans (Category.assoc _ _ _).symm

end ReindexSpellings

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

section ZariskiReadingTensorTranspose

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)

/-- `Stacks.SheafOfModules.homEquiv_comp_reindex_tensor_of_heq` at the Zariski reading adjunction
of `yoneda.obj T`: the equivalence of Stacks 04M0, the tensor products of the two small étale
sites, the associated-module adjunction of Stacks 03DU and the identification of the reading with
the Zariski restriction fixed. -/
theorem zariskiReadingAdjunction_homEquiv_tensor_of_reindex :
    type_of% (Stacks.SheafOfModules.homEquiv_comp_reindex_tensor_of_heq
      (CX := (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)))
      (L₁ := (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property))
      (R₁ := (SheafOfModules.pushforward.{u}
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property)))
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
      (representedSchemeCommRingStructureSheaf B S hS T)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).toRingedTopos.O) rfl
      (representedStructureRingSheaf B S hS T) rfl
      (representedSmallEtaleModuleEquivalence B S hS T) HEq.rfl
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).toRingedTopos.O) HEq.rfl
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))) HEq.rfl
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (zariskiReadingIso T) (zariskiReadingAdjunction T) rfl) :=
  Stacks.SheafOfModules.homEquiv_comp_reindex_tensor_of_heq
    (CX := (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)))
    (L₁ := (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property))
    (R₁ := (SheafOfModules.pushforward.{u}
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)))
    (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
    (representedSchemeCommRingStructureSheaf B S hS T)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).toRingedTopos.O) rfl
    (representedStructureRingSheaf B S hS T) rfl
    (representedSmallEtaleModuleEquivalence B S hS T) HEq.rfl
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).toRingedTopos.O) HEq.rfl
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))) HEq.rfl
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (zariskiReadingIso T) (zariskiReadingAdjunction T) rfl

/-- `AlgebraicGeometry.Space.zariskiReadingAdjunction_homEquiv_tensor_of_reindex` with the
comparison of Stacks 03EL for the associated module and its naturality fixed. -/
theorem zariskiReadingAdjunction_homEquiv_tensor_of_zariski :
    type_of% (zariskiReadingAdjunction_homEquiv_tensor_of_reindex T
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
      (fun M N => (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        M N).hom)
      (fun a b => Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
        a b)) :=
  zariskiReadingAdjunction_homEquiv_tensor_of_reindex T
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
    (fun M N => (Stacks.SheafOfModules.pullbackTensorIsoTransport
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      M N).hom)
    (fun a b => Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      a b)

/-- **The transpose along the Zariski reading adjunction of the comparison with tensor
products.**  For `𝒪`-modules `P`, `Q` on the small étale site of `yoneda.obj T`, the transpose of
`(P_Zar ⊗ Q_Zar)^a ⟶ (P_Zar)^a ⊗ (Q_Zar)^a ⟶ P ⊗ Q` (Stacks 03EL for the associated module and
for the comparison of Stacks 04M0, then the counits of
`AlgebraicGeometry.Space.zariskiReadingAdjunction`) is the transport along
`AlgebraicGeometry.Space.zariskiReadingIso` of the lax comparison of the Zariski restriction
followed by the restriction of the lax comparison of the inverse of the comparison of
Stacks 04M0. -/
theorem zariskiReadingAdjunction_homEquiv_tensor
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    type_of% (zariskiReadingAdjunction_homEquiv_tensor_of_zariski T
      (fun M N => (Stacks.SheafOfModules.pullbackTensorIsoTransport _
        (Stacks.SheafOfModules.pullbackModulesReindexIso
          (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
          (representedSchemeCommRingStructureSheaf B S hS T)) M N).hom)
      HEq.rfl P Q) :=
  zariskiReadingAdjunction_homEquiv_tensor_of_zariski T
    (fun M N => (Stacks.SheafOfModules.pullbackTensorIsoTransport _
      (Stacks.SheafOfModules.pullbackModulesReindexIso
        (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
        (representedSchemeCommRingStructureSheaf B S hS T)) M N).hom)
    HEq.rfl P Q

end ZariskiReadingTensorTranspose

end AlgebraicGeometry.Space
