module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence

/-! # The composition law for the module-level comparison of Stacks 03EL

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `f' : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi presented by functors of the underlying sites which are morphisms of sites, so that
`f' ∘ f` is one too (**Stacks 03CC**).  For sheaves of `𝒪_E`-modules `A` and `B` there is the
comparison

`h^*(A ⊗_{𝒪_E} B) ⟶ h^*A ⊗ h^*B`

of **Stacks 03EL** for the site-presented pullback — that is,
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` — at each of `f`, `f'` and `f' ∘ f`; and
there is the composition isomorphism `f'^* ⋙ f^* ≅ (f' ∘ f)^*` of the underived half of
**Stacks 0D6D**, `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso`.  This file proves
that the two are compatible: the composition isomorphism followed by the comparison for `f' ∘ f`
is `f^*` of the comparison for `f'`, then the comparison for `f`, then the composition isomorphism
in each tensor factor.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackToposCompTau`: the comparison of the geometric direct
  images of the composite, which is the identity.
* `Stacks.Sheaves.DerivedPullback.pullbackModulesCompSiteIso`: the composition isomorphism of
  pullbacks in the four-field presentation of Stacks 03D6, for the three morphisms attached to a
  composable pair of site-presented ones.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap_comp`: the composition law, with no
  hypothesis beyond the two morphism-of-sites witnesses and for arbitrary sheaves of modules.
* `pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app`: the site-presented
  composition isomorphism agrees with the four-field one, transported along the identification of
  the two pullbacks in each of the three slots.
* `Stacks.Sheaves.DerivedPullback.pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app`:
  the composition law of Tag 03EL for the four-field pullback, read on the *inverse* comparison of
  pullbacks, for an arbitrary comparison `τ` of direct images.
* `Stacks.Sheaves.DerivedPullback.fSharpSetComp_modulesHomOfSiteHom`: the structure map of the
  composite is the composite structure map.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03CC](https://stacks.math.columbia.edu/tag/03CC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules

namespace Stacks.Sheaves.DerivedPullback

universe u

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (f' : RingedToposSiteHom Y Z)
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosf' : f'.u.IsMorphismOfSites Z.J Y.J)

/-! ## The abstract conjugation argument -/

section Abstract

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]

/-- If the conjugate of the forward direction of an isomorphism of left adjoints is the forward
direction of an isomorphism of the right adjoints, the same holds of the two inverses. -/
private theorem conj_inv_eq {L₁ L₂ : 𝒵 ⥤ 𝒳} {R₁ R₂ : 𝒳 ⥤ 𝒵}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) (e : R₁ ≅ R₂)
    (h : conjugateEquiv adj₁ adj₂ α.hom = e.hom) :
    conjugateEquiv adj₂ adj₁ α.inv = e.inv := by
  rw [← e.hom_comp_eq_id, ← h]
  exact conjugateEquiv_comm adj₁ adj₂ α.inv_hom_id

/-- The converse direction of `conj_inv_eq`. -/
private theorem conj_hom_eq {L₁ L₂ : 𝒵 ⥤ 𝒳} {R₁ R₂ : 𝒳 ⥤ 𝒵}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) (e : R₁ ≅ R₂)
    (h : conjugateEquiv adj₂ adj₁ α.inv = e.inv) :
    conjugateEquiv adj₁ adj₂ α.hom = e.hom := by
  rw [← e.comp_inv_eq_id, ← h]
  exact conjugateEquiv_comm adj₁ adj₂ α.inv_hom_id

variable {Pφ Lf : 𝒴 ⥤ 𝒳} {Qφ Rf : 𝒳 ⥤ 𝒴} {Pψ Lf' : 𝒵 ⥤ 𝒴} {Qψ Rf' : 𝒴 ⥤ 𝒵}
  {Pχ Lc : 𝒵 ⥤ 𝒳} {Qχ Rc : 𝒳 ⥤ 𝒵}

/-- **The composition comparisons of two presentations of a composable pair of adjoint pairs
agree, as soon as the comparisons of the right adjoints do.**

Here `Aφ, Aψ, Aχ` and `Bf, Bf', Bc` are two presentations of three adjoint pairs, the second
pair of each presentation being composable; `Pfiso, Pf'iso, Pciso` compare the right adjoints
of the two presentations; `E` and `D` are the two composition comparisons of the right
adjoints.  The hypothesis says that the comparisons are compatible with the two composition
isomorphisms of right adjoints, and the conclusion is the corresponding statement for the left
adjoints, with each comparison of left adjoints the mate of the comparison of right adjoints. -/
private theorem abstract_bridge
    (Aφ : Pφ ⊣ Qφ) (Aψ : Pψ ⊣ Qψ) (Aχ : Pχ ⊣ Qχ)
    (Bf : Lf ⊣ Rf) (Bf' : Lf' ⊣ Rf') (Bc : Lc ⊣ Rc)
    (Pfiso : Qφ ≅ Rf) (Pf'iso : Qψ ≅ Rf') (Pciso : Qχ ≅ Rc)
    (E : Qχ ≅ Qφ ⋙ Qψ) (D : Rc ≅ Rf ⋙ Rf')
    (hstar : Pciso.hom ≫ D.hom =
      E.hom ≫ Functor.whiskerLeft Qφ Pf'iso.hom ≫ Functor.whiskerRight Pfiso.hom Rf') :
    (Adjunction.leftAdjointCompIso Bf' Bf Bc D.symm).hom ≫
        (Adjunction.leftAdjointUniq (Aχ.ofNatIsoRight Pciso) Bc).inv =
      Functor.whiskerLeft Lf' (Adjunction.leftAdjointUniq (Aφ.ofNatIsoRight Pfiso) Bf).inv ≫
        Functor.whiskerRight (Adjunction.leftAdjointUniq (Aψ.ofNatIsoRight Pf'iso) Bf').inv Pφ ≫
          (Adjunction.leftAdjointUniq (Aχ.ofNatIsoRight E) (Aψ.comp Aφ)).inv := by
  have hσ : conjugateEquiv Aφ Bf
      (Adjunction.leftAdjointUniq (Aφ.ofNatIsoRight Pfiso) Bf).inv = Pfiso.hom :=
    conj_inv_eq Bf Aφ _ Pfiso.symm
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom Aφ Pfiso Bf)
  have hσ' : conjugateEquiv Aψ Bf'
      (Adjunction.leftAdjointUniq (Aψ.ofNatIsoRight Pf'iso) Bf').inv = Pf'iso.hom :=
    conj_inv_eq Bf' Aψ _ Pf'iso.symm
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom Aψ Pf'iso Bf')
  have hσc : conjugateEquiv Aχ Bc
      (Adjunction.leftAdjointUniq (Aχ.ofNatIsoRight Pciso) Bc).inv = Pciso.hom :=
    conj_inv_eq Bc Aχ _ Pciso.symm
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom Aχ Pciso Bc)
  have hK : conjugateEquiv Aχ (Aψ.comp Aφ)
      (Adjunction.leftAdjointUniq (Aχ.ofNatIsoRight E) (Aψ.comp Aφ)).inv = E.hom :=
    conj_inv_eq (Aψ.comp Aφ) Aχ _ E.symm
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom Aχ E (Aψ.comp Aφ))
  have hc : conjugateEquiv Bc (Bf'.comp Bf)
      (Adjunction.leftAdjointCompIso Bf' Bf Bc D.symm).hom = D.hom :=
    conj_hom_eq Bc (Bf'.comp Bf) _ D
      (Adjunction.conjugateEquiv_leftAdjointCompIso_inv Bf' Bf Bc D.symm)
  refine (conjugateEquiv Aχ (Bf'.comp Bf)).injective ?_
  rw [← conjugateEquiv_comp Aχ Bc (Bf'.comp Bf), hσc, hc, ← Category.assoc,
    ← conjugateEquiv_comp Aχ (Aψ.comp Aφ) (Bf'.comp Bf),
    ← conjugateEquiv_comp (Aψ.comp Aφ) (Bf'.comp Aφ) (Bf'.comp Bf),
    conjugateEquiv_whiskerRight Aψ Bf' Aφ, conjugateEquiv_whiskerLeft Aφ Bf Bf', hσ, hσ', hK]
  exact hstar

end Abstract

/-! ## Reassociation and cancellation helpers -/

/-- Cancelling a one-sided inverse on the left of an identity. -/
private lemma comp_eq_of_eq_comp {C : Type*} [Category C] {V W T : C} {p : V ⟶ W} {q : W ⟶ V}
    (hqp : q ≫ p = 𝟙 W) {a : V ⟶ T} {b : W ⟶ T} (h : a = p ≫ b) : q ≫ a = b := by
  rw [h, ← Category.assoc, hqp, Category.id_comp]

/-- Moving a one-sided inverse across an identity on the right. -/
private lemma eq_comp_of_comp_eq {C : Type*} [Category C] {V W T : C} {p : W ⟶ T} {q : T ⟶ W}
    (hpq : p ≫ q = 𝟙 W) {a : V ⟶ W} {b : V ⟶ T} (h : a ≫ p = b) : a = b ≫ q := by
  rw [← h, Category.assoc, hpq, Category.comp_id]

/-- Appending a morphism to a two-step identity: the `reassoc` of an identity whose left-hand side
is a two-fold composite. -/
private lemma comp_assoc_of_eq {C : Type*} [Category C] {W X₁ Y₁ T : C} {a : W ⟶ X₁} {b : X₁ ⟶ Y₁}
    {c : W ⟶ Y₁} (h : a ≫ b = c) (k : Y₁ ⟶ T) : a ≫ b ≫ k = c ≫ k := by
  rw [← Category.assoc, h]

/-- Reassociating a fourfold composite. -/
private lemma assoc₄ {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  rw [Category.assoc, Category.assoc]

/-- **Inverting a two-factor identity against a three-factor one.**  Given `a ≫ b = c ≫ d ≫ e`
and one-sided inverses `b'`, `c'`, `d'` for `b`, `c`, `d`, this is the same identity read from the
other end: `e ≫ b' = d' ≫ c' ≫ a`. -/
private lemma invert_three_factor_identity {C : Type*} [Category C] {P₀ P₁ P₂ P₃ Q : C}
    {a : P₀ ⟶ Q} {b : Q ⟶ P₃} {b' : P₃ ⟶ Q}
    {c : P₀ ⟶ P₁} {c' : P₁ ⟶ P₀} {d : P₁ ⟶ P₂} {d' : P₂ ⟶ P₁} {e : P₂ ⟶ P₃}
    (hbb : b ≫ b' = 𝟙 Q) (hcc : c' ≫ c = 𝟙 P₁) (hdd : d' ≫ d = 𝟙 P₂)
    (h : a ≫ b = c ≫ d ≫ e) : e ≫ b' = d' ≫ c' ≫ a := by
  have key : d' ≫ c' ≫ a ≫ b = e := by
    rw [h, ← Category.assoc c' c, hcc, Category.id_comp, ← Category.assoc d' d, hdd,
      Category.id_comp]
  rw [← key, Category.assoc, Category.assoc, Category.assoc, hbb, Category.comp_id]

/-- **The action of an uncurried bifunctor on a pair of morphisms, written out.**  This is the
definition of `CategoryTheory.Functor.uncurry` read at a pair: the action of the uncurried
bifunctor on `(a, b)` is the action of `P` on `a` followed by the action of `P.obj K'` on `b`. -/
private theorem uncurry_obj_map_prod {A₁ : Type*} [Category A₁] {A₂ : Type*} [Category A₂]
    {B : Type*} [Category B] (P : A₁ ⥤ A₂ ⥤ B) {K K' : A₁} {L L' : A₂}
    (a : K ⟶ K') (b : L ⟶ L') :
    (Functor.uncurry.obj P).map ((a, b) : ((K, L) : A₁ × A₂) ⟶ (K', L')) =
      (P.map a).app L ≫ (P.obj K').map b :=
  rfl

/-! ## The composition law for the four-field pullback, on the inverse comparison -/

section Generic

variable (phi : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (psi : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (chi : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (t : phi.toToposHom.pushforward ⋙ psi.toToposHom.pushforward ≅ chi.toToposHom.pushforward)
  (ht : fSharpSetComp phi psi ≫
    t.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet chi)
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- **The composition law for the comparison morphism of Tag 03EL, read on the inverse comparison
of pullbacks.**  Undoing the comparison of pullbacks at `F ⊗_{O_E} G` and then applying the
comparison of Tag 03EL for `χ` is `φ^*` of the comparison for `ψ`, then the comparison for `φ`,
then the inverse comparison of pullbacks in each tensor factor.

This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` with the comparison of pullbacks
moved from the target of the composite to its source. -/
theorem pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app :
    (pullbackModulesCompIso phi psi chi t ht).inv.app
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)).obj (F, G)) ≫
        (pullbackTensorIso chi).hom.app (F, G) =
      phi.pullbackModules.map ((pullbackTensorIso psi).hom.app (F, G)) ≫
        (pullbackTensorIso phi).hom.app (psi.pullbackModules.obj F, psi.pullbackModules.obj G) ≫
          (Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
              (((pullbackModulesCompIso phi psi chi t ht).inv.app F,
                (pullbackModulesCompIso phi psi chi t ht).inv.app G) :
                ((phi.pullbackModules.obj (psi.pullbackModules.obj F),
                  phi.pullbackModules.obj (psi.pullbackModules.obj G)) :
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
                (chi.pullbackModules.obj F, chi.pullbackModules.obj G)) :=
  comp_eq_of_eq_comp ((pullbackModulesCompIso phi psi chi t ht).inv_hom_id_app _)
    ((eq_comp_of_comp_eq
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).mapIso
          (Iso.prod ((pullbackModulesCompIso phi psi chi t ht).app F)
            ((pullbackModulesCompIso phi psi chi t ht).app G))).hom_inv_id)
      (pullbackTensorIso_hom_app_comp phi psi chi t ht F G)).trans
      (assoc₄ _ _ _ _))

/-- **The comparison of Tag 03EL is natural in the pair of modules**, written with the action of
the uncurried tensor bifunctor on a pair on both sides.  This is the naturality of
`Stacks.SheafOfModules.pullbackTensorIso` at a morphism of the product category. -/
theorem pullbackTensorIso_hom_naturality_prod (g
    : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    {F F' G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (a : F ⟶ F') (b : G ⟶ G') :
    g.pullbackModules.map ((Functor.uncurry.obj (
        Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).map ((a, b) :
          ((F, G) : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ×
            SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ (F', G'))) ≫
        (pullbackTensorIso g).hom.app (F', G') =
      (pullbackTensorIso g).hom.app (F, G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map ((
            g.pullbackModules.map a, g.pullbackModules.map b) :
          ((g.pullbackModules.obj F, g.pullbackModules.obj G)
              : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            (g.pullbackModules.obj F', g.pullbackModules.obj G')) :=
  (pullbackTensorIso g).hom.naturality _

/-- `pullbackTensorIso_hom_naturality_prod` with a morphism appended. -/
theorem pullbackTensorIso_hom_naturality_prod_assoc
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    {F F' G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (a : F ⟶ F') (b
        : G ⟶ G') {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k
        : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj (
            g.pullbackModules.obj F', g.pullbackModules.obj G') ⟶ T) :
    g.pullbackModules.map ((Functor.uncurry.obj (
        Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)).map ((a, b) :
          ((F, G)
              : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ×
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ (F', G'))) ≫
        (pullbackTensorIso g).hom.app (F', G') ≫ k =
      (pullbackTensorIso g).hom.app (F, G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map ((
            g.pullbackModules.map a, g.pullbackModules.map b) :
          ((g.pullbackModules.obj F, g.pullbackModules.obj G)
              : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            (g.pullbackModules.obj F', g.pullbackModules.obj G')) ≫ k :=
  (comp_assoc_of_eq (pullbackTensorIso_hom_naturality_prod g a b) k).trans (Category.assoc _ _ _)

/-- `pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app` with a morphism appended, and
with the source of the comparison spelled by the two one-variable actions of the tensor bifunctor
rather than by the uncurried one. -/
theorem pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app_assoc
    {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).obj
        (chi.pullbackModules.obj F, chi.pullbackModules.obj G)) ⟶ T) :
    (pullbackModulesCompIso phi psi chi t ht).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj F).obj G) ≫
        (pullbackTensorIso chi).hom.app (F, G) ≫ k =
      phi.pullbackModules.map ((pullbackTensorIso psi).hom.app (F, G)) ≫
        (pullbackTensorIso phi).hom.app (psi.pullbackModules.obj F, psi.pullbackModules.obj G) ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map (
              ((pullbackModulesCompIso phi psi chi t ht).inv.app F,
                (pullbackModulesCompIso phi psi chi t ht).inv.app G) :
                ((phi.pullbackModules.obj (psi.pullbackModules.obj F),
                  phi.pullbackModules.obj (psi.pullbackModules.obj G))
                      : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
                (chi.pullbackModules.obj F, chi.pullbackModules.obj G)) ≫ k :=
  (comp_assoc_of_eq (
      pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app phi psi chi t ht F G) k).trans (
          assoc₄ _ _ _ _)

end Generic

/-! ## The comparison of pullbacks along a composite of site-presented morphisms -/

/-- **The comparison of the geometric direct images of a composite of site-presented morphisms
of ringed topoi is the identity.**  For `φ`, `ψ` and `χ` the four-field morphisms of Stacks 03D6
attached to `f`, `f'` and `f' ∘ f`, the underlying morphisms of topoi compose on the nose, so the
datum `τ` that `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` asks for is the
identity isomorphism. -/
def pullbackToposCompTau :
    (modulesHomOfSiteHom f hmosf).toToposHom.pushforward ⋙
        (modulesHomOfSiteHom f' hmosf').toToposHom.pushforward ≅
      (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).toToposHom.pushforward :=
  Iso.refl _

/-- **The structure map of the composite is the composite structure map**: the compatibility of
`pullbackToposCompTau` with the structure maps that
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` takes. -/
theorem fSharpSetComp_modulesHomOfSiteHom :
    fSharpSetComp (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf') ≫
        (pullbackToposCompTau f f' hmosf hmosf').hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')) := by
  refine (Category.comp_id (fSharpSetComp (modulesHomOfSiteHom f hmosf)
    (modulesHomOfSiteHom f' hmosf'))).trans ?_
  have hf : fSharpSet (modulesHomOfSiteHom f hmosf) =
      (sheafCompose Y.J (forget CommRingCat.{u})).map f.fSharp :=
    (AlgebraicGeometry.RingedToposHom.ringFsharp_forget _).trans
      (AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom _)
  have hf' : fSharpSet (modulesHomOfSiteHom f' hmosf') =
      (sheafCompose Z.J (forget CommRingCat.{u})).map f'.fSharp :=
    (AlgebraicGeometry.RingedToposHom.ringFsharp_forget _).trans
      (AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom _)
  have hcomp : fSharpSet (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')) =
      (sheafCompose Z.J (forget CommRingCat.{u})).map (f'.comp f).fSharp :=
    (AlgebraicGeometry.RingedToposHom.ringFsharp_forget _).trans
      (AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom _)
  rw [fSharpSetComp_eq, hf, hf', hcomp]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The comparison `(f' ∘ f)^* ≅ f'^* ⋙ f^*` of pullbacks of sheaves of modules in the
four-field presentation of Stacks 03D6**, for the three morphisms attached to a composable pair of
site-presented morphisms of ringed topoi.

This is `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` fed with the identity
comparison of direct images and its compatibility with the structure maps; it is the four-field
counterpart of `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso`. -/
def pullbackModulesCompSiteIso :
    (modulesHomOfSiteHom (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).pullbackModules ≅
      (modulesHomOfSiteHom f' hmosf').pullbackModules ⋙
        (modulesHomOfSiteHom f hmosf).pullbackModules :=
  pullbackModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
    (modulesHomOfSiteHom (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
    (pullbackToposCompTau f f' hmosf hmosf') (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')

/-! ### The reduction of the bridge to an identity of pushforwards -/

private theorem pullbackModulesSiteIso_eq :
    pullbackModulesSiteIso f hmosf =
      Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmosf)).ofNatIsoRight
          (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso)
        f.pullbackPushforwardAdjunctionTopos :=
  rfl

/-- The composition comparison of the two site-presented pullbacks, spelled out. -/
private theorem pullbackToposCompIso_eq :
    RingedToposSiteHom.pullbackToposCompIso f f' =
      Adjunction.leftAdjointCompIso f'.pullbackPushforwardAdjunctionTopos
        f.pullbackPushforwardAdjunctionTopos (f'.comp f).pullbackPushforwardAdjunctionTopos
        (RingedToposSiteHom.pushforwardToposCompIso f f').symm :=
  rfl

/-- The composition comparison of the four-field pullbacks, spelled out. -/
private theorem pullbackModulesCompSiteIso_eq_adj :
    pullbackModulesCompSiteIso f f' hmosf hmosf' =
      Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules (modulesHomOfSiteHom (f'.comp f)
            (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))).ofNatIsoRight
          (pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf)
            (modulesHomOfSiteHom f' hmosf')
            (modulesHomOfSiteHom (f'.comp f)
              (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
            (pullbackToposCompTau f f' hmosf hmosf')
              (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).symm)
        ((pullbackAdjPushforwardModules (modulesHomOfSiteHom f' hmosf')).comp
          (pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmosf))) :=
  rfl

section Factors

variable {X' Y' : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison of the two presentations of the direct image splits, on underlying sheaves of
sets, into the comparison of the four-field and the two-field presentations and the comparison of
the two-field presentation with Mathlib's direct image. -/
private theorem map_pushforwardModulesToposIso_hom_app_comp
    (g : RingedToposSiteHom X' Y') (hmos : g.u.IsMorphismOfSites Y'.J X'.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
        ((RingedSite.Hom.ofRingedToposSiteHom g hmos).pushforwardModulesToposIso.hom.app N) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
          ((AlgebraicGeometry.RingedToposHom.pushforwardModulesIso
            (RingedSite.Hom.ofRingedToposSiteHom g hmos).ringedToposHom).hom.app N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
          ((RingedSite.Hom.ofRingedToposSiteHom g hmos).pushforwardToposIso.hom.app N) :=
  (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map_comp _ _

/-- The comparison of the two-field direct image with Mathlib's is the identity on underlying
sheaves of sets: its component is `Stacks.Sheaves.RingedToposModules.ofSheafHom` of an
identity. -/
private theorem map_pushforwardToposIso_hom_app
    (g : RingedToposSiteHom X' Y') (hmos : g.u.IsMorphismOfSites Y'.J X'.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
        ((RingedSite.Hom.ofRingedToposSiteHom g hmos).pushforwardToposIso.hom.app N) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).obj
        ((RingedSite.Hom.ofRingedToposSiteHom g hmos).ringedToposHom.pushforwardModules.obj N)) :=
  moduleSheafFunctor_map_ofSheafHom _ _ _

open Stacks.Sheaves.GradedAlgebraEssentiallySmall in
/-- The comparison of the four-field and the two-field direct images is the identity on
underlying sheaves of sets. -/
private theorem map_pushforwardModulesIso_hom_app
    (g : RingedToposSiteHom X' Y') (hmos : g.u.IsMorphismOfSites Y'.J X'.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
        ((AlgebraicGeometry.RingedToposHom.pushforwardModulesIso
          (RingedSite.Hom.ofRingedToposSiteHom g hmos).ringedToposHom).hom.app N) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom g hmos)).obj N)) :=
  moduleSheafFunctor_map_pushforwardModulesIso_hom_app _ N

/-- **The comparison of the two presentations of the direct image of sheaves of modules along a
morphism of ringed topoi presented by a morphism of sites is the identity on underlying sheaves
of sets.** -/
private theorem map_pushforwardModulesToposIso_hom_app
    (g : RingedToposSiteHom X' Y') (hmos : g.u.IsMorphismOfSites Y'.J X'.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
        ((RingedSite.Hom.ofRingedToposSiteHom g hmos).pushforwardModulesToposIso.hom.app N) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom g hmos)).obj N)) :=
  (map_pushforwardModulesToposIso_hom_app_comp g hmos N).trans
    ((congrArg (fun q ↦ (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
          ((AlgebraicGeometry.RingedToposHom.pushforwardModulesIso
            (RingedSite.Hom.ofRingedToposSiteHom g hmos).ringedToposHom).hom.app N) ≫ q)
      (map_pushforwardToposIso_hom_app g hmos N)).trans
      ((Category.comp_id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
            ((AlgebraicGeometry.RingedToposHom.pushforwardModulesIso
              (RingedSite.Hom.ofRingedToposSiteHom g hmos).ringedToposHom).hom.app N))).trans
        (map_pushforwardModulesIso_hom_app g hmos N)))

/-- The same comparison, read on sections. -/
private theorem val_app_pushforwardModulesToposIso_hom_app
    (g : RingedToposSiteHom X' Y') (hmos : g.u.IsMorphismOfSites Y'.J X'.J)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) (U : Y'.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y'.J U).obj ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom g hmos)).obj N))) :
    (Sheaf.sectionsFunctor Y'.J U).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
          ((RingedSite.Hom.ofRingedToposSiteHom g hmos).pushforwardModulesToposIso.hom.app N))
        x = x :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor Y'.J U).map m x)
    (map_pushforwardModulesToposIso_hom_app g hmos N)

end Factors

/-! ### The factors of (★) -/

/-- The composition comparison of Mathlib's direct images is the identity on sections. -/
private theorem map_pushforwardToposCompIso_hom_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((RingedToposSiteHom.pushforwardToposCompIso f f').hom.app M) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((f'.comp f).pushforwardTopos.obj M)) :=
  Sheaf.hom_ext_sections fun U x ↦
    RingedToposSiteHom.pushforwardToposCompIso_hom_app_val_app f f' M U x

/-- The inverse of the composition comparison of the four-field direct images is `τ.inv`, hence
the identity, on underlying sheaves of sets. -/
private theorem map_pushforwardModulesCompIso_inv_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
            (modulesHomOfSiteHom (f'.comp f)
              (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
            (pullbackToposCompTau f f' hmosf hmosf')
              (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app M) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))).obj M)) :=
  moduleSheafFunctor_map_pushforwardModulesCompInv (modulesHomOfSiteHom f hmosf)
    (modulesHomOfSiteHom f' hmosf')
    (modulesHomOfSiteHom (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')) M
    (pullbackToposCompTau f f' hmosf hmosf') (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')

/-- The direct image along `f'` of the comparison for `f` is the identity on underlying sheaves
of sets: the direct image is restriction along `f'.u`, so this is the comparison for `f` read on
sections over `f'.u U`. -/
private theorem map_pushforwardTopos_map_hom_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (f'.pushforwardTopos.map
          ((RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom.app M)) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        (f'.pushforwardTopos.obj
          ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M))) :=
  Sheaf.hom_ext_sections fun U x ↦
    val_app_pushforwardModulesToposIso_hom_app f hmosf M (f'.u.op.obj U) x

/-- The two whiskered factors of the right-hand side of (★) compose to the identity on
underlying sheaves of sets. -/
private theorem star_rhs_tail
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((Functor.whiskerLeft (pushforwardModules (modulesHomOfSiteHom f hmosf))
            (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom ≫
          Functor.whiskerRight
            (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom
            f'.pushforwardTopos).app M) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom f' hmosf')).obj
          ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M))) := by
  refine Eq.trans ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp
    ((RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom.app
      ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M))
    (f'.pushforwardTopos.map
      ((RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom.app M))) ?_
  refine Eq.trans (congrArg (fun q ↦ (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom.app
      ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M)) ≫ q)
    (map_pushforwardTopos_map_hom_app f f' hmosf M)) ?_
  refine Eq.trans (Category.comp_id ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom.app
      ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M)))) ?_
  exact map_pushforwardModulesToposIso_hom_app f' hmosf'
    ((pushforwardModules (modulesHomOfSiteHom f hmosf)).obj M)

/-- The left-hand side of (★) is the identity on underlying sheaves of sets. -/
private theorem star_lhs
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (((RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
              (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
                hmosf hmosf')).pushforwardModulesToposIso.hom ≫
            (RingedToposSiteHom.pushforwardToposCompIso f f').hom).app M) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))).obj M)) := by
  refine Eq.trans ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp
    ((RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
          hmosf hmosf')).pushforwardModulesToposIso.hom.app M)
    ((RingedToposSiteHom.pushforwardToposCompIso f f').hom.app M)) ?_
  refine Eq.trans (congrArg (fun q ↦ (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
          hmosf hmosf')).pushforwardModulesToposIso.hom.app M) ≫ q)
    (map_pushforwardToposCompIso_hom_app f f' M)) ?_
  refine Eq.trans (Category.comp_id ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
          hmosf hmosf')).pushforwardModulesToposIso.hom.app M))) ?_
  exact map_pushforwardModulesToposIso_hom_app (f'.comp f)
    (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf') M

/-- The right-hand side of (★) is the identity on underlying sheaves of sets. -/
private theorem star_rhs
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf)
                (modulesHomOfSiteHom f' hmosf')
                (modulesHomOfSiteHom (f'.comp f)
                  (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
                (pullbackToposCompTau f f' hmosf hmosf')
                  (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv ≫
            Functor.whiskerLeft (pushforwardModules (modulesHomOfSiteHom f hmosf))
                (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom ≫
              Functor.whiskerRight
                (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom
                f'.pushforwardTopos).app M) =
      CategoryStruct.id ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules (modulesHomOfSiteHom (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))).obj M)) := by
  refine Eq.trans ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp
    ((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
      (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
      (pullbackToposCompTau f f' hmosf hmosf')
        (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app M)
    ((Functor.whiskerLeft (pushforwardModules (modulesHomOfSiteHom f hmosf))
        (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom ≫
      Functor.whiskerRight
        (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom
        f'.pushforwardTopos).app M)) ?_
  refine Eq.trans (congrArg (fun q ↦ (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
      (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
      (pullbackToposCompTau f f' hmosf hmosf')
        (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app M) ≫ q)
    (star_rhs_tail f f' hmosf hmosf' M)) ?_
  refine Eq.trans (Category.comp_id ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    ((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
      (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
      (pullbackToposCompTau f f' hmosf hmosf')
        (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app M))) ?_
  exact map_pushforwardModulesCompIso_inv_app f f' hmosf hmosf' M

/-- (★) at a single sheaf of modules. -/
private theorem star_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
            (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
              hmosf hmosf')).pushforwardModulesToposIso.hom ≫
        (RingedToposSiteHom.pushforwardToposCompIso f f').hom).app M =
      ((pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
            (modulesHomOfSiteHom (f'.comp f)
              (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
            (pullbackToposCompTau f f' hmosf hmosf')
              (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv ≫
        Functor.whiskerLeft (pushforwardModules (modulesHomOfSiteHom f hmosf))
            (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom ≫
          Functor.whiskerRight
            (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom
            f'.pushforwardTopos).app M :=
  hom_ext_moduleSheafFunctor.{u, u, u}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
    (M := (pushforwardModules (modulesHomOfSiteHom (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))).obj M)
    (N := f'.pushforwardTopos.obj (f.pushforwardTopos.obj M))
    ((star_lhs f f' hmosf hmosf' M).trans (star_rhs f f' hmosf hmosf' M).symm)

/-- **(★)** The two comparisons of the direct image of sheaves of modules along a composite are
compatible with the comparisons of the two presentations of each direct image. -/
private theorem star :
    (RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
            (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
              hmosf hmosf')).pushforwardModulesToposIso.hom ≫
        (RingedToposSiteHom.pushforwardToposCompIso f f').hom =
      (pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
            (modulesHomOfSiteHom (f'.comp f)
              (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
            (pullbackToposCompTau f f' hmosf hmosf')
              (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv ≫
        Functor.whiskerLeft (pushforwardModules (modulesHomOfSiteHom f hmosf))
            (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso.hom ≫
          Functor.whiskerRight
            (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso.hom
            f'.pushforwardTopos :=
  NatTrans.ext (funext fun M ↦ star_app f f' hmosf hmosf' M)

/-- **The two composition isomorphisms of pullbacks agree.**  The composition isomorphism
`f^*f'^* ≅ (f' ∘ f)^*` of `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso`, followed by
the identification of the pullback along `f' ∘ f` with its four-field counterpart, is the
identification for `f` whiskered by `f'^*`, then the identification for `f'` pushed along `f^*`,
then the four-field composition isomorphism `pullbackModulesCompSiteIso`. -/
theorem pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app (M
    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (RingedToposSiteHom.pullbackToposCompIso f f').hom.app M ≫
        (pullbackModulesSiteIso (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).inv.app M =
      (pullbackModulesSiteIso f hmosf).inv.app (f'.pullbackTopos.obj M) ≫
        (modulesHomOfSiteHom f hmosf).pullbackModules.map
            ((pullbackModulesSiteIso f' hmosf').inv.app M) ≫
          (pullbackModulesCompSiteIso f f' hmosf hmosf').inv.app M := by
  rw [pullbackToposCompIso_eq f f', pullbackModulesCompSiteIso_eq_adj f f' hmosf hmosf',
    pullbackModulesSiteIso_eq f hmosf, pullbackModulesSiteIso_eq f' hmosf',
    pullbackModulesSiteIso_eq (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')]
  have key := abstract_bridge
    (pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmosf))
    (pullbackAdjPushforwardModules (modulesHomOfSiteHom f' hmosf'))
    (pullbackAdjPushforwardModules (modulesHomOfSiteHom (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')))
    f.pullbackPushforwardAdjunctionTopos f'.pullbackPushforwardAdjunctionTopos
    (f'.comp f).pullbackPushforwardAdjunctionTopos
    (RingedSite.Hom.ofRingedToposSiteHom f hmosf).pushforwardModulesToposIso
    (RingedSite.Hom.ofRingedToposSiteHom f' hmosf').pushforwardModulesToposIso
    (RingedSite.Hom.ofRingedToposSiteHom (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f'
        hmosf hmosf')).pushforwardModulesToposIso
    (pushforwardModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf')
      (modulesHomOfSiteHom (f'.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
      (pullbackToposCompTau f f' hmosf hmosf')
        (fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).symm
    (RingedToposSiteHom.pushforwardToposCompIso f f')
    (star f f' hmosf hmosf')
  exact congrArg (fun t ↦ NatTrans.app t M) key

/-! ## The composition law -/

/-- **The comparison of Stacks 03EL for the site-presented pullback, with its two tensor-factor
comparisons read as the action of the uncurried tensor bifunctor on a pair.**

This is `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` at a second spelling of its last
two factors, definitionally equal to the first; the source of the comparison keeps the one-variable
spelling `((𝒪_D-tensor).obj A).obj B`. -/
theorem pullbackToposTensorMap_eq_uncurry (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    pullbackToposTensorMap f hmos A B =
      (pullbackModulesSiteIso f hmos).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≫
        (pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app (A, B) ≫
          (Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
              (((pullbackModulesSiteIso f hmos).hom.app A,
                (pullbackModulesSiteIso f hmos).hom.app B) :
                (((modulesHomOfSiteHom f hmos).pullbackModules.obj A,
                  (modulesHomOfSiteHom f hmos).pullbackModules.obj B) :
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
                (f.pullbackTopos.obj A, f.pullbackTopos.obj B)) :=
  rfl

/-- **The bridge, read backwards.**  Undoing the four-field composition isomorphism and then
identifying the pullback along `f' ∘ f` is the identification for `f'` pushed along `f^*`, then the
identification for `f`, then the composition isomorphism of the site-presented pullbacks; it is
`pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app` inverted. -/
theorem pullbackModulesCompSiteIso_inv_app_comp_pullbackModulesSiteIso_hom_app (M
    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackModulesCompSiteIso f f' hmosf hmosf').inv.app M ≫
        (pullbackModulesSiteIso (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).hom.app M =
      (modulesHomOfSiteHom f hmosf).pullbackModules.map
          ((pullbackModulesSiteIso f' hmosf').hom.app M) ≫
        (pullbackModulesSiteIso f hmosf).hom.app (f'.pullbackTopos.obj M) ≫
          (RingedToposSiteHom.pullbackToposCompIso f f').hom.app M :=
  invert_three_factor_identity
    ((pullbackModulesSiteIso (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).inv_hom_id_app M)
    ((pullbackModulesSiteIso f hmosf).hom_inv_id_app (f'.pullbackTopos.obj M))
    (((Functor.map_comp ((modulesHomOfSiteHom f hmosf).pullbackModules) _ _).symm.trans
        (congrArg ((modulesHomOfSiteHom f hmosf).pullbackModules).map
          ((pullbackModulesSiteIso f' hmosf').hom_inv_id_app M))).trans
      (((modulesHomOfSiteHom f hmosf).pullbackModules).map_id _))
    (pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app f f' hmosf hmosf' M)

/-- The naturality of the identification of the two pullbacks of sheaves of modules, with a
morphism appended. -/
private lemma pullbackModulesSiteIso_inv_naturality_assoc
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (h : M ⟶ N)
    {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (k
        : (modulesHomOfSiteHom f hmosf).pullbackModules.obj N ⟶ T) :
    f.pullbackTopos.map h ≫ (pullbackModulesSiteIso f hmosf).inv.app N ≫ k =
      (pullbackModulesSiteIso f hmosf).inv.app M ≫
          (modulesHomOfSiteHom f hmosf).pullbackModules.map h ≫ k := by
  rw [← Category.assoc, (pullbackModulesSiteIso f hmosf).inv.naturality, Category.assoc]

/-- `pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app` with a morphism appended. -/
private lemma pullbackToposCompIso_hom_app_comp_inv_app_assoc (M
    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (k
        : (modulesHomOfSiteHom (f'.comp f) (
            RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).pullbackModules.obj M ⟶
                T) :
    (RingedToposSiteHom.pullbackToposCompIso f f').hom.app M ≫
        (pullbackModulesSiteIso (f'.comp f) (
            RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).inv.app M ≫ k =
      (pullbackModulesSiteIso f hmosf).inv.app (f'.pullbackTopos.obj M) ≫
        (modulesHomOfSiteHom f hmosf).pullbackModules.map ((
            pullbackModulesSiteIso f' hmosf').inv.app M) ≫
                (pullbackModulesCompSiteIso f f' hmosf hmosf').inv.app M ≫ k := by
  rw [← Category.assoc, pullbackToposCompIso_hom_app_comp_pullbackModulesSiteIso_inv_app,
      Category.assoc, Category.assoc]

/-- `pullbackModulesCompSiteIso` written out as the four-field composition isomorphism
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` it is. -/
private lemma pullbackModulesCompSiteIso_eq :
    (pullbackModulesCompSiteIso f f' hmosf hmosf') = (pullbackModulesCompIso (
        modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf') (modulesHomOfSiteHom (
            f'.comp f) (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
    (pullbackToposCompTau f f' hmosf hmosf') (
        fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')) :=
  rfl

/-- **The three tensor-factor comparisons recombine.**  Undoing the four-field composition
isomorphism in each tensor factor and then identifying the two pullbacks along `f' ∘ f` in each
tensor factor is the identification for `f'` pushed along `f^*`, then the identification for `f`,
then the composition isomorphism of the site-presented pullbacks — each in both factors. -/
private lemma tensorFactor_comparisons_comp (A B
    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map
          (((pullbackModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf') (
              modulesHomOfSiteHom (f'.comp f) (
                  RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
    (pullbackToposCompTau f f' hmosf hmosf') (
        fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app A,
            (pullbackModulesCompIso (modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf') (
                modulesHomOfSiteHom (f'.comp f) (
                    RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
    (pullbackToposCompTau f f' hmosf hmosf') (
        fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf')).inv.app B) :
          (((modulesHomOfSiteHom f hmosf).pullbackModules.obj ((
              modulesHomOfSiteHom f' hmosf').pullbackModules.obj A),
            (modulesHomOfSiteHom f hmosf).pullbackModules.obj ((
                modulesHomOfSiteHom f' hmosf').pullbackModules.obj B))
                    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          ((modulesHomOfSiteHom (f'.comp f) (
              RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).pullbackModules.obj A,
                  (modulesHomOfSiteHom (f'.comp f) (
                      RingedToposSiteHom.isMorphismOfSites_comp_u f f'
                        hmosf hmosf')).pullbackModules.obj B)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map (((
            pullbackModulesSiteIso (f'.comp f) (
                RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).hom.app A,
                    (pullbackModulesSiteIso (f'.comp f) (
                        RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).hom.app B) :
          (((modulesHomOfSiteHom (f'.comp f) (
              RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).pullbackModules.obj A,
                  (modulesHomOfSiteHom (f'.comp f) (
                      RingedToposSiteHom.isMorphismOfSites_comp_u f f'
                        hmosf hmosf')).pullbackModules.obj B) :
                  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          ((f'.comp f).pullbackTopos.obj A, (f'.comp f).pullbackTopos.obj B)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map (((
          modulesHomOfSiteHom f hmosf).pullbackModules.map ((
              pullbackModulesSiteIso f' hmosf').hom.app A),
            (modulesHomOfSiteHom f hmosf).pullbackModules.map ((
                pullbackModulesSiteIso f' hmosf').hom.app B)) :
          (((modulesHomOfSiteHom f hmosf).pullbackModules.obj ((
              modulesHomOfSiteHom f' hmosf').pullbackModules.obj A),
            (modulesHomOfSiteHom f hmosf).pullbackModules.obj ((
                modulesHomOfSiteHom f' hmosf').pullbackModules.obj B))
                    : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          ((modulesHomOfSiteHom f hmosf).pullbackModules.obj (f'.pullbackTopos.obj A),
            (modulesHomOfSiteHom f hmosf).pullbackModules.obj (f'.pullbackTopos.obj B))) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map (((
            pullbackModulesSiteIso f hmosf).hom.app (f'.pullbackTopos.obj A),
                (pullbackModulesSiteIso f hmosf).hom.app (f'.pullbackTopos.obj B)) :
            (((modulesHomOfSiteHom f hmosf).pullbackModules.obj (f'.pullbackTopos.obj A),
              (modulesHomOfSiteHom f hmosf).pullbackModules.obj (f'.pullbackTopos.obj B))
                  : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            (f.pullbackTopos.obj (f'.pullbackTopos.obj A),
              f.pullbackTopos.obj (f'.pullbackTopos.obj B))) ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).map (
              ((RingedToposSiteHom.pullbackToposCompIso f f').hom.app A,
                  (RingedToposSiteHom.pullbackToposCompIso f f').hom.app B) :
            ((f.pullbackTopos.obj (f'.pullbackTopos.obj A),
              f.pullbackTopos.obj (f'.pullbackTopos.obj B))
                  : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            ((f'.comp f).pullbackTopos.obj A, (f'.comp f).pullbackTopos.obj B)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Prod.ext (
      pullbackModulesCompSiteIso_inv_app_comp_pullbackModulesSiteIso_hom_app f f' hmosf hmosf' A) (
          pullbackModulesCompSiteIso_inv_app_comp_pullbackModulesSiteIso_hom_app f f'
            hmosf hmosf' B))

/-- **The composition law for the module-level comparison of Stacks 03EL for the site-presented
pullback.**  For sheaves of `𝒪_E`-modules `A` and `B`, the composition isomorphism
`f^*f'^*(A ⊗_{𝒪_E} B) ⟶ (f' ∘ f)^*(A ⊗_{𝒪_E} B)` of Stacks 0D6D followed by the comparison of
Stacks 03EL for `f' ∘ f` is `f^*` of the comparison for `f'`, then the comparison for `f`, then
the composition isomorphism in each tensor factor.  The morphism-of-sites witness for the composite
is `AlgebraicGeometry.RingedToposSiteHom.isMorphismOfSites_comp_u` (Stacks 03CC). -/
theorem pullbackToposTensorMap_comp
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (RingedToposSiteHom.pullbackToposCompIso f f').hom.app (((
        Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).obj B) ≫
        pullbackToposTensorMap (f'.comp f) (
            RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf') A B =
      f.pullbackTopos.map (pullbackToposTensorMap f' hmosf' A B) ≫
        pullbackToposTensorMap f hmosf (f'.pullbackTopos.obj A) (f'.pullbackTopos.obj B) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map ((
              RingedToposSiteHom.pullbackToposCompIso f f').hom.app A)).app
              (f.pullbackTopos.obj (f'.pullbackTopos.obj B)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj ((
                f'.comp f).pullbackTopos.obj A)).map ((
                    RingedToposSiteHom.pullbackToposCompIso f f').hom.app B) := by
  rw [← uncurry_obj_map_prod (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (K := f.pullbackTopos.obj (f'.pullbackTopos.obj A))
      (L := f.pullbackTopos.obj (f'.pullbackTopos.obj B))
      (K' := (f'.comp f).pullbackTopos.obj A) (L' := (f'.comp f).pullbackTopos.obj B)
      ((RingedToposSiteHom.pullbackToposCompIso f f').hom.app A) ((
          RingedToposSiteHom.pullbackToposCompIso f f').hom.app B),
    pullbackToposTensorMap_eq_uncurry f hmosf,
        pullbackToposTensorMap_eq_uncurry (f'.comp f) (
            RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')]
  simp only [Category.assoc]
  rw [pullbackModulesSiteIso_inv_naturality_assoc f hmosf (pullbackToposTensorMap f' hmosf' A B),
    pullbackToposTensorMap_eq_uncurry (X := Y) (Y := Z) f' hmosf', Functor.map_comp,
        Functor.map_comp]
  simp only [Category.assoc]
  rw [pullbackTensorIso_hom_naturality_prod_assoc (modulesHomOfSiteHom f hmosf)
      ((pullbackModulesSiteIso f' hmosf').hom.app A)
      ((pullbackModulesSiteIso f' hmosf').hom.app B),
    pullbackToposCompIso_hom_app_comp_inv_app_assoc, pullbackModulesCompSiteIso_eq,
        pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app_assoc (
            modulesHomOfSiteHom f hmosf) (modulesHomOfSiteHom f' hmosf') (modulesHomOfSiteHom (
                f'.comp f) (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
      (pullbackToposCompTau f f' hmosf hmosf') (
          fSharpSetComp_modulesHomOfSiteHom f f' hmosf hmosf') A B, tensorFactor_comparisons_comp]

end Stacks.Sheaves.DerivedPullback

end
