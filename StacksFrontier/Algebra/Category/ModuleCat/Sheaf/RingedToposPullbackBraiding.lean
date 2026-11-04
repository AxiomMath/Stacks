module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackAssociativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections

/-!
# The braided coherence of Tag 03EL

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The comparison
`Stacks.SheafOfModules.pullbackTensorIso` of Tag 03EL is compatible with the symmetry constraint
of the monoidal structure of Tag 01CA:

`f^*(β_{F,G}) ≫ δ_{G,F} = δ_{F,G} ≫ β_{f^*F, f^*G}`.

## Main results

* `Stacks.SheafOfModules.RingedToposPullback.braiding`: the braided coherence of Tag 03EL.
* `Stacks.SheafOfModules.RingedToposPullback.canonicalPairing_braiding`: following the canonical
  pairing of Tag 05NA of `F` and `G` by `β_{F,G}` is exchanging the two arguments and then
  pairing.
* `Stacks.SheafOfModules.RingedToposPullback.invImageCanonicalPairing_braiding`: the same
  identity after `f⁻¹`.
* `Stacks.SheafOfModules.RingedToposPullback.step123_pullbackMap_braiding_comparison_comp`:
  steps 1 to 3 of the chain of Tag 03EL carry `f^*(β_{F,G}) ≫ v` to the exchange of the two
  arguments followed by the pairing produced from `v` at the splitting `(G, F)`.
* `Stacks.SheafOfModules.RingedToposPullback.residual_braiding`: the identity of pairings over
  `f⁻¹O_D` to which the coherence reduces.

## Implementation notes

Both sides of the coherence are morphisms of sheaves of `O_C`-modules
`f^*(F ⊗ G) ⟶ f^*G ⊗ f^*F`. Steps 1 to 3 of the chain of Tag 03EL identify such morphisms with
bilinear pairings of `f⁻¹F` and `f⁻¹G` over `f⁻¹O_D`, and the two pairings are compared on a pair
of local sections, where both are the exchanged local pure tensor `(1 ⊗ b) ⊗ (1 ⊗ a)` of the two
units of Tag 03CZ.

The computation crosses the spellings `Stacks.Sheaves.RingedToposModules.commRingSheaf J A hA`
and `Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA` of a sheaf of rings, and
`(Tensor.ringSheaf Y.O).obj` and `TensorSheafification.structureRingPresheaf Y.O.obj` of its
underlying presheaf. The second pair agrees only at default transparency, so the reductions are
`congrArg`/`Eq.trans` chains rather than `rw`.

`X : RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}` have independent sites and
coefficient universes. Under the local instances
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` and
`Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf`, the monoidal product is the tensor
product sheaf and the braiding is `Stacks.SheafOfModules.tensorSheafBraiding`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf

namespace Stacks.SheafOfModules.RingedToposPullback

/-! ### Exchanging the two arguments of a pairing, and of a product comparison -/

section Swap

open Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A pairing precomposed with the exchange of the two factors of a product, on a pair of local
sections: it is the given pairing evaluated on the exchanged pair. -/
private lemma pairingApp_swap {R : Sheaf J RingCat.{w}}
    {P Q M : _root_.SheafOfModules.{w} R}
    (q : Sheaf.moduleSheaf R Q ⨯ Sheaf.moduleSheaf R P ⟶ Sheaf.moduleSheaf R M) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R P))
    (b : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R Q)) :
    pairingApp R (prod.lift prod.snd prod.fst ≫ q) U a b = pairingApp R q U b a := by
  simp only [pairingApp, Functor.map_comp_apply, Functor.map_lift_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The identity acts as the identity on a local section. -/
private lemma idHomValApp {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{w} R)
    (U : Cᵒᵖ) (x : M.val.obj U) : (𝟙 M : M ⟶ M).val.app U x = x :=
  rfl

end Swap

/-- **The product comparison of a functor commutes with the exchange of the two factors.** -/
private lemma prodComparison_swap {E : Type*} [Category E] {E' : Type*} [Category E']
    [HasBinaryProducts E] [HasBinaryProducts E'] (Φ : E' ⥤ E) (P Q : E') :
    Φ.map (prod.lift prod.snd prod.fst) ≫ prodComparison Φ Q P =
      prodComparison Φ P Q ≫ prod.lift prod.snd prod.fst := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp, prod.lift_fst,
      Category.assoc, prod.lift_fst, prodComparison_snd]
  · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp, prod.lift_snd,
      Category.assoc, prod.lift_snd, prodComparison_fst]

/-! ### The coherence -/

section Coherence

open Stacks.SheafOfModules Stacks.PresheafOfModules.ChangeOfRings

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The canonical pairing of Tag 05NA is compatible with the symmetry constraint of
Tag 01CA**: following the canonical pairing of `F` and `G` by `β_{F,G}` is the same as exchanging
the two arguments and taking the canonical pairing of `G` and `F`. -/
theorem canonicalPairing_braiding (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    canonicalPairing (Tensor.ringSheaf Y.O).property F G ≫
        (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map (β_ F G).hom =
      prod.lift prod.snd prod.fst ≫ canonicalPairing (Tensor.ringSheaf Y.O).property G F :=
  pairing_ext (Tensor.ringSheaf Y.O) fun U a b ↦
    (pairingApp_comp (canonicalPairing (Tensor.ringSheaf Y.O).property F G)
          (β_ F G).hom U a b).trans
      ((congrArg (fun z ↦ (β_ F G).hom.val.app U z)
            (pairingApp_canonicalPairing (Tensor.ringSheaf Y.O).property F G U a b)).trans
        ((braiding_tensorSectionsAt Y.O.obj (Tensor.ringSheaf Y.O).property U F G a b).trans
          ((pairingApp_canonicalPairing (Tensor.ringSheaf Y.O).property G F U b a).symm.trans
            (pairingApp_swap (canonicalPairing (Tensor.ringSheaf Y.O).property G F)
              U a b).symm)))

/-- **The canonical pairing of two inverse images is compatible with the symmetry constraint of
Tag 01CA.** This is `canonicalPairing_braiding` after `f⁻¹`. -/
theorem invImageCanonicalPairing_braiding
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    invImageCanonicalPairing f F G ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).map (β_ F G).hom) =
      prod.lift prod.snd prod.fst ≫ invImageCanonicalPairing f G F := by
  have := isIso_prodComparison_inverseImage f.toToposHom
    (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F) (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)
  refine (cancel_epi (prodComparison f.toToposHom.inverseImage
    (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
    (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G))).1 ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (prodComparison_comp_invImageCanonicalPairing f F G) _) ?_
  refine Eq.trans (whisker_eq _ (moduleSheafFunctor_map_inverseImageModules_map f.toToposHom
    (Tensor.ringSheaf Y.O) (β_ F G).hom)) ?_
  refine Eq.trans (f.toToposHom.inverseImage.map_comp _ _).symm ?_
  refine Eq.trans (congrArg f.toToposHom.inverseImage.map
    (canonicalPairing_braiding (Y := Y) F G)) ?_
  refine Eq.trans (f.toToposHom.inverseImage.map_comp _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker (prodComparison_swap f.toToposHom.inverseImage
    (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F) (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) G)) _)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact whisker_eq _ (prodComparison_comp_invImageCanonicalPairing f G F).symm

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on a composite beginning with the pullback of the
symmetry constraint.** The pairing of `f⁻¹F` and `f⁻¹G` over `f⁻¹O_D` produced by
`f^*(β_{F,G}) ≫ v` is the exchange of the two arguments followed by the pairing which the chain
at the splitting `(G, F)` produces from `v`. -/
theorem step123_pullbackMap_braiding_comparison_comp
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (v : f.pullbackModules.obj (G ⊗ F) ⟶ N) :
    (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
        (pullbackTensorStep1 f F G N (f.pullbackModules.map (β_ F G).hom ≫ v)))).1 =
      prod.lift prod.snd prod.fst ≫
        (pullbackTensorStep3 f G F N (pullbackTensorStep2 f G F N
          (pullbackTensorStep1 f G F N v))).1 := by
  have hnat : (structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) ≫
        (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map
          (f.pullbackModules.map (β_ F G).hom) =
      (inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).map (β_ F G).hom ≫
        (structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (G ⊗ F)) :=
    ((structureAdjunction f).unit.naturality
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).map (β_ F G).hom)).symm
  have hbody : (structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (F ⊗ G)) ≫
        (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map
          (f.pullbackModules.map (β_ F G).hom ≫ v) =
      (inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).map (β_ F G).hom ≫
        ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj (G ⊗ F)) ≫
          (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map v) :=
    (whisker_eq _ ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker hnat _).trans (Category.assoc _ _ _)))
  refine Eq.trans (step123_eq f F G N (f.pullbackModules.map (β_ F G).hom ≫ v)) ?_
  refine Eq.trans (whisker_eq _ (congrArg _ hbody)) ?_
  refine Eq.trans (whisker_eq _ (Functor.map_comp _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (invImageCanonicalPairing_braiding f F G) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (step123_eq f G F N v).symm

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on a composite beginning with the comparison**: the
pairing produced is `invChainPairing f F G N k`. -/
private lemma step123_comparison_comp
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (k : f.pullbackModules.obj F ⊗ f.pullbackModules.obj G ⟶ N) :
    (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
        (pullbackTensorStep1 f F G N (pullbackTensorComparison f F G ≫ k)))).1 =
      (invChainPairing f F G N k).1 :=
  congrArg Subtype.val
    ((congrArg (pullbackTensorStep3 f F G N)
        ((congrArg (pullbackTensorStep2 f F G N)
            (step1_comparison_comp f F G N k)).trans
          ((pullbackTensorStep2 f F G N).apply_symm_apply _))).trans
      ((pullbackTensorStep3 f F G N).apply_symm_apply _))

open Stacks.SheafOfModules in
/-- **The Yoneda step of the braided coherence**: two morphisms out of `f^*(F ⊗ G)` agree as soon
as steps 1 to 3 of the chain of Tag 03EL carry them to the same pairing of `f⁻¹F` and `f⁻¹G` over
`f⁻¹O_D`. -/
private lemma eq_of_step123_eq
    (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    {u u' : f.pullbackModules.obj (F ⊗ G) ⟶ N}
    (h : (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
          (pullbackTensorStep1 f F G N u))).1 =
        (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
          (pullbackTensorStep1 f F G N u'))).1) :
    u = u' :=
  (pullbackTensorStep1 f F G N).injective
    ((pullbackTensorStep2 f F G N).injective
      ((pullbackTensorStep3 f F G N).injective (Subtype.ext h)))

open Stacks.SheafOfModules in
/-- **The identity of pairings over `f⁻¹O_D` which the braided coherence of Tag 03EL comes down
to.** Both sides carry a pair `(a, b)` of local sections to the exchanged local pure tensor
`(1 ⊗ b) ⊗ (1 ⊗ a)` of the two units of Tag 03CZ. -/
theorem residual_braiding (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    prod.lift prod.snd prod.fst ≫
        (invChainPairing f G F
          (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) (𝟙 _)).1 =
      (invChainPairing f F G (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
        (β_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)).hom).1 := by
  refine pairing_ext (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
    fun U a b ↦ ?_
  refine Eq.trans (pairingApp_swap (invChainPairing f G F
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) (𝟙 _)).1 U a b) ?_
  refine Eq.trans (pairingApp_invChainPairing f G F
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) (𝟙 _) U b a) ?_
  refine Eq.trans (idHomValApp
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) U _) ?_
  refine Eq.trans ?_ (pairingApp_invChainPairing f F G
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
    (β_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)).hom U a b).symm
  exact (braiding_tensorSectionsAt X.O.obj (Tensor.ringSheaf X.O).property U
    (f.pullbackModules.obj F) (f.pullbackModules.obj G) _ _).symm

/-- **The braided coherence of Tag 03EL**: the comparison
`Stacks.SheafOfModules.pullbackTensorIso` is compatible with the symmetry constraint of the
monoidal structure of Tag 01CA. -/
theorem braiding (F G : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map (β_ F G).hom ≫ pullbackTensorComparison f G F =
      pullbackTensorComparison f F G ≫
        (β_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)).hom := by
  refine eq_of_step123_eq f F G
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) ?_
  refine Eq.trans (step123_pullbackMap_braiding_comparison_comp f F G
    (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
    (pullbackTensorComparison f G F)) ?_
  refine Eq.trans (whisker_eq _
    ((congrArg (fun y ↦ (pullbackTensorStep3 f G F
          (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
          (pullbackTensorStep2 f G F (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
            (pullbackTensorStep1 f G F
              (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) y))).1)
        (Category.comp_id (pullbackTensorComparison f G F)).symm).trans
      (step123_comparison_comp f G F
        (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F) (𝟙 _)))) ?_
  exact (residual_braiding f F G).trans
    (step123_comparison_comp f F G
      (f.pullbackModules.obj G ⊗ f.pullbackModules.obj F)
      (β_ (f.pullbackModules.obj F) (f.pullbackModules.obj G)).hom).symm

end Coherence

end Stacks.SheafOfModules.RingedToposPullback

end
