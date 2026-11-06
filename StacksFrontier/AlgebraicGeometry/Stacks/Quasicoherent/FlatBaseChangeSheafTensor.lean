module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTransposeSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivPairingApp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep2Apply
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# Tensor products of étale sheaves of modules with the flat base change property (Stacks 0764 (5))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0762** attaches to an
étale sheaf of `𝒪_𝒳`-modules the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`; in the source's ambient
category `Mod(𝒳_étale, 𝒪_𝒳)` this is
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`. Part (5) of **Stacks 0764** says
that the tensor product `F ⊗_{𝒪_𝒳} G` of two such modules has the property again, because tensor
products commute with pullbacks, **Stacks 03EL**.

The proof is the source's. Restriction to a small étale site commutes with the tensor product,
`AlgebraicGeometry.Stack.restrictSheafTensorIso` (from
`AlgebraicGeometry.Stack.restrictModuleEtaleTensorSheafIso` of Stacks 06WM (4)); the inverse image
along the morphism of small étale ringed topoi below `φ` commutes with the tensor product,
`Stacks.SheafOfModules.pullbackTensorIso`; and under these identifications `c_φ(F ⊗ G)` is
`c_φ(F) ⊗ c_φ(G)`. The last identity is the substance, and it is proved through adjuncts rather
than by computing `c_φ(F ⊗ G)` itself.

## The argument

* The comparison map is the adjunct, across the adjunction of the sheafified Stacks 06WC pullback
  with the pushforward along the morphism of ringed sites `ε_a` of Stacks 070R (2), of the
  comparison of Stacks 06W2, which on sections is restriction along an arrow between cartesian
  lifts: `AlgebraicGeometry.Stack.homEquiv_restrictSheafPullbackComparison_val_app`.
* The sheafified Stacks 06WC pullback is identified with the pullback of modules of the morphism
  of ringed topoi below `φ` by uniqueness of left adjoints, and the adjuncts across the two
  adjunctions agree on underlying sheaves of sets:
  `RingedSite.HomGeneral.moduleSheafFunctor_map_homEquiv_leftAdjointUniq_hom_app_comp`.
* A morphism out of the pullback of a tensor product is the comparison of Stacks 03EL followed by
  a tensor product of morphisms as soon as the bilinear pairings their adjuncts define agree:
  `Stacks.SheafOfModules.eq_pullbackTensorIso_hom_comp_of_pairing`, read off the four-link
  regrouping of the chain of bijections of Stacks 03EL.
* Bilinear pairings are compared on pure pairs of local sections, where every map involved is a
  restriction map or a sheafification unit:
  `AlgebraicGeometry.Stack.restrictSheafTensorIso_hom_val_app_unit_tmul` and
  `AlgebraicGeometry.Stack.restrictionPushforwardComparison_etaleTensorSheaf_unit_tmul`.

The general mechanism is `AlgebraicGeometry.RingedSite.HomGeneral.isIso_of_tensor_sections`, for
an arbitrary morphism of ringed sites and an arbitrary left adjoint of its pushforward; the
consequence at the stack is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_etaleTensorSheaf`.

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_tensor`: **Stacks 0764, part (5)**,
  for the canonical tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` of
  `Mod(𝒳_étale, 𝒪_𝒳)`, which is `AlgebraicGeometry.Stack.etaleTensorSheaf`.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_etaleTensorSheaf`: the
  comparison map of a tensor product is invertible when those of the factors are, at one arrow.
* `AlgebraicGeometry.RingedSite.HomGeneral.isIso_of_tensor_sections`: the transport of Stacks 03EL
  to an arbitrary left adjoint of the pushforward along a morphism of ringed sites.

## Implementation notes

The sheaves of modules on a small étale site have two spellings in play: over
`AlgebraicGeometry.SmallEtale.structureSheaf`, which the restriction functors and the sheafified
Stacks 06WC pullback use, and over the structure sheaf of the ringed site
`AlgebraicGeometry.smallEtaleRingedSite`, which the morphism of ringed topoi below `φ`, and hence
Stacks 03EL, uses. They are definitionally equal, but reconciling them inside a large composite
exhausts the heartbeat budget of the elaborator, and of the kernel. Every step is therefore
arranged so that the crossing happens on a variable or on a single section: the transport of
Stacks 03EL is proved once at a general morphism of ringed sites, with the left adjoint, the two
tensor identifications and the maps on sections all as arguments, and the stack-specific facts
are fed to it as section formulas. The one section formula that reads an adjunct of the
sheafified pullback is proved with `AlgebraicGeometry.smallEtaleBaseChange` and
`CategoryTheory.Over.post` locally irreducible and at the spelling
`AlgebraicGeometry.Stack.structureMapRingAt`.

The comparison of the two pushforwards of sheaves of modules attached to a morphism of ringed
sites is the identity on underlying sheaves of sets,
`RingedSite.HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app_eq_id`,
from `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso`.

No hypothesis beyond those of the source is carried: the sheafification instances of the
associated étale site that the tensor product needs hold for every `𝒳`, and the registered
statement supplies them from `AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`.

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules CategoryTheory.Sheaf

universe w w' v u v' u'

section TransposeOfComparison

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The image of a product of two morphisms under a functor preserving the binary product,
read through the inverse of the product comparison. -/
theorem preservesLimitPair_iso_inv_map_prodMap {C : Type*} [Category C] {D : Type*} [Category D]
    (H : C ⥤ D) {A A' B B' : C} [HasBinaryProduct A B] [HasBinaryProduct A' B']
    [HasBinaryProduct (H.obj A) (H.obj B)] [HasBinaryProduct (H.obj A') (H.obj B')]
    [PreservesLimit (pair A B) H] [PreservesLimit (pair A' B') H] (a : A ⟶ A') (b : B ⟶ B') :
    (PreservesLimitPair.iso H A B).inv ≫ H.map (prod.map a b) =
      prod.map (H.map a) (H.map b) ≫ (PreservesLimitPair.iso H A' B').inv := by
  rw [Iso.inv_comp_eq, PreservesLimitPair.iso_hom, ← Category.assoc, ← prodComparison_natural,
    Category.assoc,
    ← PreservesLimitPair.iso_hom, Iso.hom_inv_id, Category.comp_id]

/-- A product of two morphisms, followed by the inverse product comparison of a functor and the
image of a product of two morphisms followed by a third, regrouped. -/
theorem prodMap_comp_preservesLimitPair_iso_inv_map_comp {C : Type*} [Category C] {D : Type*}
    [Category D] (H : C ⥤ D) {A A' B B' Z : C} {P Q : D} [HasBinaryProduct A B]
    [HasBinaryProduct A' B'] [HasBinaryProduct (H.obj A) (H.obj B)]
    [HasBinaryProduct (H.obj A') (H.obj B')] [HasBinaryProduct P Q]
    [PreservesLimit (pair A B) H] [PreservesLimit (pair A' B') H]
    (a : P ⟶ H.obj A) (b : Q ⟶ H.obj B) (u : A ⟶ A') (v : B ⟶ B') (q : A' ⨯ B' ⟶ Z) :
    prod.map a b ≫ (PreservesLimitPair.iso H A B).inv ≫ H.map (prod.map u v ≫ q) =
      prod.map (a ≫ H.map u) (b ≫ H.map v) ≫ (PreservesLimitPair.iso H A' B').inv ≫ H.map q := by
  rw [H.map_comp, ← Category.assoc (PreservesLimitPair.iso H A B).inv,
    preservesLimitPair_iso_inv_map_prodMap, ← Category.assoc, ← Category.assoc, prod.map_map,
    Category.assoc]

/-- **A morphism out of the pullback of a tensor product, identified through Stacks 03EL.** Let
`k : f^*(F ⊗ G) ⟶ N` and let `g : M₁ ⊗ M₂ ⟶ N` be preceded by the tensor product of two morphisms
`c₁ : f^*F ⟶ M₁` and `c₂ : f^*G ⟶ M₂`. If the bilinear pairing of `F` and `G` with values in
`f_*N` that the adjunct of `k` defines is the one obtained from the adjuncts of `c₁` and `c₂`
and from the pairing of `g`, then `k` is the comparison of Stacks 03EL followed by
`(c₁ ⊗ c₂) ≫ g`.

The chain of bijections of Stacks 03EL carries the comparison followed by `(c₁ ⊗ c₂) ≫ g` to
`(c₁ ⊗ c₂) ≫ g` itself, and its third link is computed by
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit`, so the hypothesis
is exactly the statement that the chain sends `k` to the same morphism. -/
theorem eq_pullbackTensorIso_hom_comp_of_pairing
    {M₁ M₂ : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (c₁ : (f.pullbackModules).obj F ⟶ M₁) (c₂ : (f.pullbackModules).obj G ⟶ M₂)
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj (M₁, M₂) ⟶ N)
    (k : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
      f.pullbackModules).obj (F, G) ⟶ N)
    (hk : pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app
            (F.val ⊗ G.val) ≫ ((pullbackAdjPushforwardModules f).homEquiv _ _ k).val) =
      prod.map
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).homEquiv _ _ c₁))
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).homEquiv _ _ c₂)) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M₁)
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M₂)).inv ≫
          f.toToposHom.pushforward.map
            (pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
              ((PresheafOfModules.sheafificationAdjunction
                    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
                  (M₁.val ⊗ M₂.val) ≫ g.val))) :
    k = (pullbackTensorIso f).hom.app (F, G) ≫
      ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 _)).map (_root_.PresheafOfModules.tensorHom c₁.val c₂.val) ≫ g) := by
  apply (pullbackTensorHomEquiv f F G N).injective
  rw [pullbackTensorHomEquiv_pullbackTensorIso_hom_comp f F G N, pullbackTensorHomEquiv_apply,
    ← Equiv.eq_symm_apply, ← Equiv.eq_symm_apply]
  apply Subtype.ext
  rw [pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit, pullbackTensorStep2_apply_coe]
  have hT : ((pullbackTensorStepTarget f F G N).symm
      ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 _)).map (_root_.PresheafOfModules.tensorHom c₁.val c₂.val) ≫ g)).1 =
      prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map c₁)
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map c₂) ≫
        pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
          ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
              (M₁.val ⊗ M₂.val) ≫ g.val) :=
    (congrArg Subtype.val (bilinearEquivTensorSheafHom_symm_precomp
        (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) g c₁ c₂)).trans
      (congrArg (fun q ↦ prod.map ((moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map c₁)
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map c₂) ≫ q)
        (bilinearEquivTensorSheafHom_symm_apply_coe
          (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) g))
  rw [hT]
  refine hk.trans ?_
  have h : ∀ {A : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
      {M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (c : (f.pullbackModules).obj A ⟶ M),
      (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).homEquiv _ _ c) =
      (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app A) ≫
        f.toToposHom.pushforward.map
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map c) :=
    fun c => (congrArg (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((pullbackAdjPushforwardModules f).homEquiv_unit _ _ c)).trans
      ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _)
  rw [h c₁, h c₂]
  exact (prodMap_comp_preservesLimitPair_iso_inv_map_comp f.toToposHom.pushforward _ _ _ _ _).symm

end TransposeOfComparison

end Stacks.SheafOfModules




namespace CategoryTheory.Sheaf

universe w₀ v₁ u₁ v₂ u₂

/-- **A pairing pushed forward along a continuous functor, on a pair of local sections.** For the
pushforward `H` of sheaves of sets along a continuous functor `G`, the pushforward of a pairing
`q : A ⨯ B ⟶ Z`, read through the inverse product comparison of `H`, pairs two sections over `U`
as `q` pairs them over `G(U)`. -/
theorem sectionsFunctor_map_preservesLimitPair_iso_inv_comp_map {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (G : C ⥤ D) [G.IsContinuous J K] {A B Z : Sheaf K (Type w₀)}
    [PreservesLimit (pair A B) (G.sheafPushforwardContinuous (Type w₀) J K)]
    (q : A ⨯ B ⟶ Z) (U : Cᵒᵖ) (a : A.obj.obj (G.op.obj U)) (b : B.obj.obj (G.op.obj U)) :
    (sectionsFunctor.{w₀} J U).map
        ((PreservesLimitPair.iso (G.sheafPushforwardContinuous (Type w₀) J K) A B).inv ≫
          (G.sheafPushforwardContinuous (Type w₀) J K).map q)
        (Functor.prodObjMk (P := sectionsFunctor.{w₀} J U) a b) =
      (sectionsFunctor.{w₀} K (G.op.obj U)).map q
        (Functor.prodObjMk (P := sectionsFunctor.{w₀} K (G.op.obj U)) a b) := by
  have hy : (sectionsFunctor.{w₀} J U).map
      (PreservesLimitPair.iso (G.sheafPushforwardContinuous (Type w₀) J K) A B).inv
        (Functor.prodObjMk (P := sectionsFunctor.{w₀} J U) a b) =
      Functor.prodObjMk (P := sectionsFunctor.{w₀} K (G.op.obj U)) a b := by
    refine Functor.prodObjMk_ext (P := sectionsFunctor.{w₀} K (G.op.obj U)) ?_ ?_
    · refine Eq.trans ?_
        (Functor.map_fst_prodObjMk (P := sectionsFunctor.{w₀} K (G.op.obj U)) a b).symm
      refine Eq.trans (((sectionsFunctor.{w₀} J U).map_comp_apply _
        ((G.sheafPushforwardContinuous (Type w₀) J K).map prod.fst) _).symm) ?_
      rw [PreservesLimitPair.iso_inv_fst]
      exact Functor.map_fst_prodObjMk (P := sectionsFunctor.{w₀} J U)
        (A := (G.sheafPushforwardContinuous (Type w₀) J K).obj A)
        (B := (G.sheafPushforwardContinuous (Type w₀) J K).obj B) a b
    · refine Eq.trans ?_
        (Functor.map_snd_prodObjMk (P := sectionsFunctor.{w₀} K (G.op.obj U)) a b).symm
      refine Eq.trans (((sectionsFunctor.{w₀} J U).map_comp_apply _
        ((G.sheafPushforwardContinuous (Type w₀) J K).map prod.snd) _).symm) ?_
      rw [PreservesLimitPair.iso_inv_snd]
      exact Functor.map_snd_prodObjMk (P := sectionsFunctor.{w₀} J U)
        (A := (G.sheafPushforwardContinuous (Type w₀) J K).obj A)
        (B := (G.sheafPushforwardContinuous (Type w₀) J K).obj B) a b
  refine ((sectionsFunctor.{w₀} J U).map_comp_apply _ _ _).trans ?_
  rw [hy]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.RingedSite

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : HomGeneral X Y)

/-- The comparison `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`
of the two pushforwards of sheaves of modules is the identity on underlying sheaves of sets. -/
theorem HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app_eq_id
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (f.pushforwardModulesToposIsoGeneral.hom.app M) = 𝟙 _ :=
  ((Sheaf.moduleSheafFunctor _).map_comp _ _).trans
    ((congrArg (fun t => t ≫ _)
      (AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso
        f.toRingedToposHom M)).trans (Category.id_comp _))

/-- The same for the inverse comparison. -/
theorem HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app_eq_id
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (f.pushforwardModulesToposIsoGeneral.inv.app M) = 𝟙 _ := by
  have hcomp := congrArg
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
    (f.pushforwardModulesToposIsoGeneral.hom_inv_id_app M)
  rw [Functor.map_comp, f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app_eq_id M,
    CategoryTheory.Functor.map_id] at hcomp
  exact (Category.id_comp _).symm.trans hcomp

/-- **An adjunct across the pullback of ringed topoi of a morphism of ringed sites, computed
through any other left adjoint of the site-presented pushforward.** If `L` is left adjoint to
the pushforward of sheaves of modules along `f`, then transposing `c : L M ⟶ N`, precomposed
with the comparison of `L` with the pullback of modules given by uniqueness of left adjoints,
across the adjunction of Stacks 03D7 gives, on underlying sheaves of sets, the transpose of `c`
across the given adjunction. -/
theorem HomGeneral.moduleSheafFunctor_map_homEquiv_leftAdjointUniq_hom_app_comp
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)}
    (adj : L ⊣ f.toRingedToposSiteHom.pushforwardTopos)
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)}
    {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)}
    (c : L.obj M ⟶ N) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposHom.toRingedToposModulesHom).homEquiv M N
          ((Adjunction.leftAdjointUniq
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
              f.toRingedToposHom.toRingedToposModulesHom)
            (adj.ofNatIsoRight f.pushforwardModulesToposIsoGeneral.symm)).hom.app M ≫ c)) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (adj.homEquiv M N c) := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    Functor.map_comp, f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app_eq_id N]
  exact Category.comp_id _

/-- **The comparison of a tensor product, from the comparisons of the factors.** Let `L` be a left
adjoint of the site-presented pushforward of sheaves of modules along `f`, and let
`cᵢ : L Aᵢ ⟶ Nᵢ` be three morphisms, together with isomorphisms `A₁ ⊗ A₂ ≅ A₃` on the target
site and `N₁ ⊗ N₂ ≅ N₃` on the source site, such that on local pure tensors the adjunct of `c₃`
is the tensor product of the adjuncts of `c₁` and `c₂`. If `c₁` and `c₂` are isomorphisms, then
so is `c₃`.

This is the comparison of Stacks 03EL for the morphism of ringed topoi of `f`, transported to `L`
along the comparison of `L` with the pullback of modules given by uniqueness of left adjoints:
the hypothesis on sections identifies, through
`Stacks.SheafOfModules.eq_pullbackTensorIso_hom_comp_of_pairing`, the transported `c₃` with the
comparison of Stacks 03EL followed by the tensor product of the transported `c₁` and `c₂`. -/
theorem HomGeneral.isIso_of_tensor_sections
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)}
    (adj : L ⊣ f.toRingedToposSiteHom.pushforwardTopos)
    {A₁ A₂ A₃ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)}
    {N₁ N₂ N₃ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)}
    (ty : ((Stacks.SheafOfModules.Tensor.sheafTensor.{uY, vY, w, w, w}
      (toRingedTopos Y).O).obj A₁).obj A₂ ≅ A₃)
    (tx : ((Stacks.SheafOfModules.Tensor.sheafTensor.{uX, vX, w, w, w}
      (toRingedTopos X).O).obj N₁).obj N₂ ≅ N₃)
    (c₁ : L.obj A₁ ⟶ N₁) (c₂ : L.obj A₂ ⟶ N₂) (c₃ : L.obj A₃ ⟶ N₃)
    (ρ₁ : ∀ U : Y.Cᵒᵖ, A₁.val.obj U → N₁.val.obj (f.u.op.obj U))
    (ρ₂ : ∀ U : Y.Cᵒᵖ, A₂.val.obj U → N₂.val.obj (f.u.op.obj U))
    (ρ₃ : ∀ U : Y.Cᵒᵖ, A₃.val.obj U → N₃.val.obj (f.u.op.obj U))
    (hρ₁ : ∀ U a, (adj.homEquiv _ _ c₁).val.app U a = ρ₁ U a)
    (hρ₂ : ∀ U a, (adj.homEquiv _ _ c₂).val.app U a = ρ₂ U a)
    (hρ₃ : ∀ U a, (adj.homEquiv _ _ c₃).val.app U a = ρ₃ U a)
    (hc : ∀ (U : Y.Cᵒᵖ) (a : A₁.val.obj U) (b : A₂.val.obj U),
      ρ₃ U (ty.hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O) (𝟙 _)).unit.app
            (A₁.val ⊗ A₂.val)).app U (a ⊗ₜ b))) =
        tx.hom.val.app (f.u.op.obj U)
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) (𝟙 _)).unit.app
              (N₁.val ⊗ N₂.val)).app (f.u.op.obj U) (ρ₁ U a ⊗ₜ ρ₂ U b)))
    (hc₁ : IsIso c₁) (hc₂ : IsIso c₂) : IsIso c₃ := by
  let f₄ := f.toRingedToposHom.toRingedToposModulesHom
  let adj₄ := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f₄
  let ι := Adjunction.leftAdjointUniq adj₄
    (adj.ofNatIsoRight f.pushforwardModulesToposIsoGeneral.symm)
  have hmap : ∀ {A : SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)}
      {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)}
      (c : L.obj A ⟶ N) (U : Y.Cᵒᵖ) (a : A.val.obj U),
      (adj₄.homEquiv A N (ι.hom.app A ≫ c)).val.app U a = (adj.homEquiv A N c).val.app U a :=
    fun c U a => congrArg (fun t => t.hom.app U a)
      (f.moduleSheafFunctor_map_homEquiv_leftAdjointUniq_hom_app_comp adj c)
  have key := Stacks.SheafOfModules.eq_pullbackTensorIso_hom_comp_of_pairing f₄ A₁ A₂ N₃
    (ι.hom.app A₁ ≫ c₁) (ι.hom.app A₂ ≫ c₂) tx.hom
    (f₄.pullbackModules.map ty.hom ≫ ι.hom.app A₃ ≫ c₃) (by
      rw [Adjunction.homEquiv_naturality_left]
      refine Stacks.SheafOfModules.pairing_ext _ fun U a b => ?_
      refine (Stacks.SheafOfModules.pairingApp_pairingOfTensorHom _ U a b).trans ?_
      refine Eq.trans ?_ (Stacks.SheafOfModules.pairingApp_eq_map_prodObjMk_of_eq_prodMap_comp
        _ _ _ _ rfl U a b).symm
      refine Eq.trans ?_
        (CategoryTheory.Sheaf.sectionsFunctor_map_preservesLimitPair_iso_inv_comp_map
        (J := (toRingedTopos Y).J) (K := (toRingedTopos X).J) f.u
        (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) N₁)
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) N₂)
        (Stacks.SheafOfModules.pairingOfTensorHom
          ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)
            (𝟙 _)).unit.app (N₁.val ⊗ N₂.val) ≫ tx.hom.val)) U _ _).symm
      refine (Eq.trans ?_ (hc U a b)).trans ?_
      · exact (hmap c₃ U _).trans (hρ₃ U _)
      · rw [← hρ₁ U a, ← hρ₂ U b]
        exact (Stacks.SheafOfModules.pairingApp_pairingOfTensorHom _ _ _ _).symm.trans
          (congrArg₂ (fun s t => Stacks.SheafOfModules.pairingApp _
              (Stacks.SheafOfModules.pairingOfTensorHom
                ((PresheafOfModules.sheafificationAdjunction
                    (R := Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)
                    (𝟙 _)).unit.app (N₁.val ⊗ N₂.val) ≫ tx.hom.val)) (f.u.op.obj U) s t)
            (hmap c₁ U a).symm (hmap c₂ U b).symm))
  have hR : IsIso ((Stacks.SheafOfModules.pullbackTensorIso f₄).hom.app (A₁, A₂) ≫
      ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (toRingedTopos X).O) (𝟙 _)).map
        (_root_.PresheafOfModules.tensorHom (ι.hom.app A₁ ≫ c₁).val
          (ι.hom.app A₂ ≫ c₂).val) ≫ tx.hom)) := by
    have h₂ : IsIso ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (toRingedTopos X).O) (𝟙 _)).map
        (_root_.PresheafOfModules.tensorHom (ι.hom.app A₁ ≫ c₁).val
          (ι.hom.app A₂ ≫ c₂).val)) := by
      rw [← Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
      exact ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{uX, vX, w, w, w}
        (toRingedTopos X).O)).mapIso
          (Iso.prod (asIso (ι.hom.app A₁ ≫ c₁)) (asIso (ι.hom.app A₂ ≫ c₂)))).isIso_hom
    exact IsIso.comp_isIso' (((Stacks.SheafOfModules.pullbackTensorIso f₄).app (A₁, A₂)).isIso_hom)
      (IsIso.comp_isIso' h₂ tx.isIso_hom)
  rw [← key] at hR
  have h₃ : IsIso (ι.hom.app A₃ ≫ c₃) := IsIso.of_isIso_comp_left (f₄.pullbackModules.map ty.hom) _
  exact IsIso.of_isIso_comp_left (ι.hom.app A₃) c₃

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Stack

open Stacks.Sheaves.RingedToposModules CategoryTheory.Sheaf

universe u v w

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Restriction

variable [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction to the small étale site of the scheme below `z` carries the tensor product
of `Mod(𝒳_ét, 𝒪_𝒳)` to the tensor product sheaf of the two restrictions.

This is `AlgebraicGeometry.Stack.restrictModuleEtaleTensorSheafIso` with the universe lift of the
objectwise tensor product removed, assembled from the same two pieces:
`AlgebraicGeometry.Stack.restrictModuleTensorObjIso` and
`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`. The latter is applied
directly, with its two site instances read off
`AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale` by projection,
so that the composite unfolds definitionally. -/
noncomputable def restrictSheafTensorIso (z : 𝒳)
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (RingedSite.toRingedTopos (smallEtaleRingedSite E (p.obj z).left.1
        (contains_base B E h S hS p z))).O).obj
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj F)).obj
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj G) ≅
      (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj
        (etaleTensorSheaf B S hS p hp F G) :=
  letI := isEquivalence_overPost B S hS p hp z
  haveI := (isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp z).1
  haveI := (isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp z).2
  (PresheafOfModules.sheafification
      (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
      (𝟙 _)).mapIso
      ((PresheafOfModules.uliftObjSelfIso _).symm ≪≫
        restrictModuleTensorObjIso B S hS p hp E h z F.val G.val) ≪≫
    Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (associatedTopology B S hS p (etaleTopology B))
      (smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z) ⋙
        (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget z)
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
      (localStructurePresheafIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B)).hom
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := (structureSheaf B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj) F.val G.val)

/-- `AlgebraicGeometry.Stack.restrictSheafTensorIso` is the sheafification-adjunct of the
restriction of the sheafification unit of `𝒳`. -/
theorem restrictSheafTensorIso_hom_eq (z : 𝒳)
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    (restrictSheafTensorIso B E h S hS p hp z F G).hom =
      (PresheafOfModules.sheafification
          (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
          (𝟙 _)).map
        ((PresheafOfModules.uliftObjSelfIso _).inv ≫
          (restrictModuleTensorObjIso B S hS p hp E h z F.val G.val).hom) ≫
      (PresheafOfModules.sheafification
          (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
          (𝟙 _)).map
          ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B) z).map
            ((PresheafOfModules.sheafificationAdjunction
              (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
                (etaleTopology_le_topology B)) (𝟙 _)).unit.app
              (PresheafOfModulesOfCommRing.Monoidal.tensorObj
                (R := (structureSheaf B S hS p hp (etaleTopology B)
                  (etaleTopology_le_topology B)).obj) F.val G.val))) ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
          (𝟙 _)).counit.app
          ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj
            (etaleTensorSheaf B S hS p hp F G)) :=
  rfl

end Restriction

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The adjunction `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction`, with its two
functors read on the sheaves of modules of the ringed sites of
`AlgebraicGeometry.smallEtaleRingedSiteHom`
and its right adjoint read as the site-presented pushforward of that morphism of ringed sites. -/
noncomputable abbrev sheafifiedPullbackSiteAdjunction :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.toRingedTopos (smallEtaleRingedSite E
          (E.obj (p.obj y).left.1 (contains_base B E h S hS p y)).obj
          (E.obj (p.obj y).left.1 (contains_base B E h S hS p y)).property)).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.toRingedTopos (smallEtaleRingedSite E
          (E.obj (p.obj x).left.1 (contains_base B E h S hS p x)).obj
          (E.obj (p.obj x).left.1 (contains_base B E h S hS p x)).property)).O)) ⊣
      (smallEtaleRingedSiteHom E
        (smallEtaleBaseMorphism B E h S hS p φ)).toRingedToposSiteHom.pushforwardTopos :=
  sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ

/-- The comparison map of Stacks 0761 is the sheafification-adjunct of the presheaf comparison,
spelled with the sheafification adjunction of the small étale site. -/
theorem restrictSheafPullbackComparison_eq
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    restrictSheafPullbackComparison B E h S hS p hp φ M =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B))).obj
            ((SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj y).left.1
              (contains_base B E h S hS p y))).obj
              ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M)))
          ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M)).symm
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) M.val) := rfl

section C1

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post


/-- **The adjunct of the comparison map of Stacks 0761, on sections.** Across the adjunction of
the sheafified Stacks 06WC pullback with the pushforward along `ε_a`, the comparison map
`c_φ^{sh}` transposes to the comparison of Stacks 06W2, on sections. -/
theorem homEquiv_restrictSheafPullbackComparison_val_app
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (U : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ)
    (z : ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M).val.obj U) :
    (((sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).homEquiv _ _
        (restrictSheafPullbackComparison B E h S hS p hp φ M))).val.app U z =
      (restrictionPushforwardComparison B E h S hS p hp φ M.val.presheaf).app U z := by
  have hval := sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at B E h S hS p hp
    (etaleTopology B) (etaleTopology_le_topology B) φ
    ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M)
    ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M)
    (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) M.val)
  rw [restrictSheafPullbackComparison_eq]
  have h2 := congrArg (fun t => t.app U z) hval
  have hadj : (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).homEquiv
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M).val
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M).val
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) M.val) =
      restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) M.val :=
    restrictModulePullbackComparison_adjunct B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) M.val
  refine h2.trans ?_
  have h3 := Stacks.PresheafOfModules.comp_eqToIso_pushforward_hom_app_app_apply_anyUniverse
    (smallEtaleStructureComparison_eq_structureMapRingAt B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ)
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).homEquiv
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M).val
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M).val
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) M.val)) U z
  refine h3.trans ?_
  exact congrArg (fun t => t.app U z) hadj


end C1

/-- `AlgebraicGeometry.Stack.homEquiv_restrictSheafPullbackComparison_val_app`
read through `AlgebraicGeometry.Stack.sheafifiedPullbackSiteAdjunction`. -/
theorem sheafifiedPullbackSiteAdjunction_homEquiv_val_app
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (U : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ)
    (z : ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M).val.obj U) :
    (((sheafifiedPullbackSiteAdjunction B E h S hS p hp φ).homEquiv
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y).obj M)
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj M)
        (restrictSheafPullbackComparison B E h S hS p hp φ M))).val.app U z =
      (restrictionPushforwardComparison B E h S hS p hp φ M.val.presheaf).app U z :=
  homEquiv_restrictSheafPullbackComparison_val_app
    B E h S hS p hp φ M U z


/-- The object of `𝒳` lying over an object `W` of the small étale site of the scheme below `z`:
the source of the cartesian lift to `z` of the structure morphism of `W`. The restriction of a
presheaf on `𝒳` to that small étale site has, over `W`, the sections over this object. -/
noncomputable abbrev smallEtaleCartesianLift (z : 𝒳)
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ) : 𝒳ᵒᵖ :=
  letI := isEquivalence_overPost B S hS p hp z
  Opposite.op ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      W.unop)).left

/-- **The comparison of Stacks 06W2 on the image of a pure tensor in the tensor product.** On the
sheafification-unit image of `a ⊗ b`, the comparison for the tensor product of `F` and `G` is the
sheafification-unit image of the tensor of the comparisons for `F` and for `G`: each is the
restriction along one arrow `φ'` between the cartesian lifts, and the sheafification unit is
natural. -/
theorem restrictionPushforwardComparison_etaleTensorSheaf_unit_tmul
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (U : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ)
    (a : F.val.obj (smallEtaleCartesianLift B E h S hS p hp y U))
    (b : G.val.obj (smallEtaleCartesianLift B E h S hS p hp y U)) :
    (restrictionPushforwardComparison B E h S hS p hp φ
        (etaleTensorSheaf B S hS p hp F G).val.presheaf).app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)) (𝟙 _)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj) F.val G.val)).app
        (smallEtaleCartesianLift B E h S hS p hp y U) (a ⊗ₜ b)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)) (𝟙 _)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj) F.val G.val)).app
        (smallEtaleCartesianLift B E h S hS p hp x
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj U))
        ((restrictionPushforwardComparison B E h S hS p hp φ F.val.presheaf).app U a ⊗ₜ
          (restrictionPushforwardComparison B E h S hS p hp φ G.val.presheaf).app U b) := by
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ U.unop
  rw [restrictionPushforwardComparison_app B E h S hS p hp φ _ U.unop φ' hfac hproj,
    restrictionPushforwardComparison_app B E h S hS p hp φ _ U.unop φ' hfac hproj,
    restrictionPushforwardComparison_app B E h S hS p hp φ _ U.unop φ' hfac hproj]
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
          (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)) (𝟙 _)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj) F.val G.val)) φ'.op (a ⊗ₜ b)).symm

/-- The adjunct of `L(g₁) ≫ L(g₂) ≫ ε` is `g₁ ≫ g₂`. -/
private theorem unit_comp_map_map_comp_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {Rr : D ⥤ C} (adj : L ⊣ Rr) {P Q : C} {N : D} (g₁ : P ⟶ Q) (g₂ : Q ⟶ Rr.obj N) :
    adj.unit.app P ≫ Rr.map (L.map g₁ ≫ L.map g₂ ≫ adj.counit.app N) = g₁ ≫ g₂ := by
  have e : L.map g₁ ≫ L.map g₂ ≫ adj.counit.app N = (adj.homEquiv P N).symm (g₁ ≫ g₂) := by
    rw [Adjunction.homEquiv_counit, L.map_comp, Category.assoc]
  rw [e]
  exact (adj.homEquiv_unit P N _).symm.trans ((adj.homEquiv P N).apply_symm_apply _)

/-- **The restriction of a tensor product, on a pure tensor.** On the sheafification-unit image
of `a ⊗ b` in the tensor product of the restrictions, the comparison
`AlgebraicGeometry.Stack.restrictSheafTensorIso` takes the value the sheafification unit of `𝒳`
takes on `a ⊗ b`. -/
theorem restrictSheafTensorIso_hom_val_app_unit_tmul
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (z : 𝒳) (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (V : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (a : F.val.obj (smallEtaleCartesianLift B E h S hS p hp z V))
    (b : G.val.obj (smallEtaleCartesianLift B E h S hS p hp z V)) :
    (restrictSheafTensorIso B E h S hS p hp z F G).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction
          (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
          (𝟙 _)).unit.app
          (PresheafOfModules.tensorObj
            (O := localCommStructurePresheaf B S hS p E h z)
            ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj F).val
            ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj G).val)).app V
        (a ⊗ₜ b)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)) (𝟙 _)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj) F.val G.val)).app
        (smallEtaleCartesianLift B E h S hS p hp z V) (a ⊗ₜ b) := by
  have hGA := unit_comp_map_map_comp_counit (PresheafOfModules.sheafificationAdjunction
          (R := SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))
          (𝟙 _)) (N := (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj
            (etaleTensorSheaf B S hS p hp F G))
    ((PresheafOfModules.uliftObjSelfIso _).inv ≫
          (restrictModuleTensorObjIso B S hS p hp E h z F.val G.val).hom)
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B) z).map
            ((PresheafOfModules.sheafificationAdjunction
              (R := ringStructureSheafCore B S hS p hp (etaleTopology B)
                (etaleTopology_le_topology B)) (𝟙 _)).unit.app
              (PresheafOfModulesOfCommRing.Monoidal.tensorObj
                (R := (structureSheaf B S hS p hp (etaleTopology B)
                  (etaleTopology_le_topology B)).obj) F.val G.val)))
  rw [restrictSheafTensorIso_hom_eq]
  exact congrArg (fun t => t.app V (a ⊗ₜ b)) hGA

/-- **The comparison map of Stacks 0761 for a tensor product.** If the comparison maps
`c_φ^{sh}` of `F` and of `G` below an arrow `φ` of `𝒳` are isomorphisms, so is the comparison map
of `F ⊗ G`.

This is `AlgebraicGeometry.RingedSite.HomGeneral.isIso_of_tensor_sections` for the morphism of
small étale ringed sites below `φ`, with the left adjoint the sheafified Stacks 06WC pullback,
the two tensor identifications `AlgebraicGeometry.Stack.restrictSheafTensorIso` at the two ends
of `φ`, and the section maps the comparisons of Stacks 06W2; the hypothesis on pure tensors is
`AlgebraicGeometry.Stack.restrictSheafTensorIso_hom_val_app_unit_tmul` at both ends together with
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_etaleTensorSheaf_unit_tmul`. -/
theorem isIso_restrictSheafPullbackComparison_etaleTensorSheaf
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F))
    (hG : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ G)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ (etaleTensorSheaf B S hS p hp F G)) :=
  (smallEtaleRingedSiteHom E (smallEtaleBaseMorphism B E h S hS p φ)).isIso_of_tensor_sections
    (sheafifiedPullbackSiteAdjunction B E h S hS p hp φ)
    (restrictSheafTensorIso B E h S hS p hp y F G)
    (restrictSheafTensorIso B E h S hS p hp x F G)
    (restrictSheafPullbackComparison B E h S hS p hp φ F)
    (restrictSheafPullbackComparison B E h S hS p hp φ G)
    (restrictSheafPullbackComparison B E h S hS p hp φ (etaleTensorSheaf B S hS p hp F G))
    (fun U a => (restrictionPushforwardComparison B E h S hS p hp φ F.val.presheaf).app U a)
    (fun U a => (restrictionPushforwardComparison B E h S hS p hp φ G.val.presheaf).app U a)
    (fun U a => (restrictionPushforwardComparison B E h S hS p hp φ
      (etaleTensorSheaf B S hS p hp F G).val.presheaf).app U a)
    (fun U a => sheafifiedPullbackSiteAdjunction_homEquiv_val_app B E h S hS p hp φ F U a)
    (fun U a => sheafifiedPullbackSiteAdjunction_homEquiv_val_app B E h S hS p hp φ G U a)
    (fun U a => sheafifiedPullbackSiteAdjunction_homEquiv_val_app B E h S hS p hp φ
      (etaleTensorSheaf B S hS p hp F G) U a)
    (fun U a b => by
      refine (congrArg (fun t => (restrictionPushforwardComparison B E h S hS p hp φ
        (etaleTensorSheaf B S hS p hp F G).val.presheaf).app U t)
        (restrictSheafTensorIso_hom_val_app_unit_tmul B E h S hS p hp y F G U a b)).trans ?_
      refine (restrictionPushforwardComparison_etaleTensorSheaf_unit_tmul B E h S hS p hp φ F G U a
        b).trans ?_
      exact (restrictSheafTensorIso_hom_val_app_unit_tmul B E h S hS p hp x F G
        ((smallEtaleRingedSiteHom E (smallEtaleBaseMorphism B E h S hS p φ)).u.op.obj U)
        ((restrictionPushforwardComparison B E h S hS p hp φ F.val.presheaf).app U a)
        ((restrictionPushforwardComparison B E h S hS p hp φ G.val.presheaf).app U b)).symm) hF hG

/-- **Stacks 0764, part (5).** The tensor product, in `Mod(𝒳_étale, 𝒪_𝒳)`, of two étale sheaves of
`𝒪_𝒳`-modules with the flat base change property of **Stacks 0762** has the flat base change
property.

The tensor product is the canonical one, `Stacks.SheafOfModules.Tensor.sheafTensor` at the
structure sheaf of the associated étale site; it is
`AlgebraicGeometry.Stack.etaleTensorSheaf` by `AlgebraicGeometry.Stack.etaleTensorSheaf_eq`. The
sheafification instances it is formed with hold for every `𝒳`, by
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`, and are supplied here.

At an arrow over a flat morphism of schemes this is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_etaleTensorSheaf`: the
restrictions commute with tensor products, the pullback commutes with tensor products by
**Stacks 03EL**, and under these identifications the comparison map of the tensor product is the
tensor product of the comparison maps. -/
@[stacks 0764 "part (5), with the ambient category the étale sheaves of modules, as the source \
  states it -- and so with a_small^* the inverse image of sheaves of modules: the tensor product \
  in Mod(𝒳_étale, 𝒪_𝒳) of two modules with the flat base change property has the flat base \
  change property"]
theorem hasFlatBaseChangePropertySheaf_tensor
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F)
    (hG : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp G) :
    letI := hasSheafify_etaleAssociatedTopology B S hS p hp
    letI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        (structureSheaf B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B))).obj F).obj G) :=
  let := hasSheafify_etaleAssociatedTopology B S hS p hp
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  fun ψ hflat => isIso_restrictSheafPullbackComparison_etaleTensorSheaf B E h S hS p hp ψ F G
    (hF ψ hflat) (hG ψ hflat)

end AlgebraicGeometry.Stack

end
