module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ComparisonCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlueDatumClosure
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands

/-!
# The quasi-coherent descent datum of Stacks 03DX (1)

Two members `X i` and `X j` of a family of objects of `(Sch/S)_fppf` have a fibre product
`AlgebraicGeometry.BigFppfOver.memberProd` inside that site, formed over its final object, and the
canonical functor to schemes preserves it, so its scheme is the scheme fibre product `X i ×_S X j`.
This file reads these fibre products as chosen pullbacks of schemes and shows that the transition
isomorphisms `AlgebraicGeometry.BigFppfOver.transitionIso` over them satisfy the two laws of
`CategoryTheory.Pseudofunctor.DescentData'`, given that the comparison isomorphism of Stacks 03DV
is pseudonatural.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.memberChosenPullback`: the fibre product of two members of a
  family of objects of `(Sch/S)_fppf`, read downstairs as a `CategoryTheory.Limits.ChosenPullback`
  of their structure morphisms.
* `AlgebraicGeometry.BigFppfOver.memberChosenPullback₃`: the chosen threefold wide fibre product of
  three members.
* `AlgebraicGeometry.BigFppfOver.memberTransition`: the transition isomorphism of the descent datum
  over the chosen fibre product of two members.
* `AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural`: the comparison isomorphism of
  Stacks 03DV is compatible with composition in the big fppf site.

## Main results

* `AlgebraicGeometry.BigFppfOver.isPullback_objHomOver_memberProd`: the scheme of the fibre product
  of two members of a family is their scheme fibre product over `S`.
* `AlgebraicGeometry.BigFppfOver.pullHom_eq_transitionIso` and
  `AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition`: the transitions, transported to a pair
  of morphisms into two members of the family, are the transition isomorphism at that pair.
* `AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition_self` and
  `AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition_comp`: the two laws of
  `CategoryTheory.Pseudofunctor.DescentData'` for those transitions, in that structure's own
  spelling of the projections of the chosen fibre products.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
  CategoryTheory.Pseudofunctor.DescentData'

universe u w

namespace Stacks

/-- If `u = u'`, `v = v'`, `w = w'` and `u' ≫ v' = w'`, then `u ≫ v = w`. -/
public theorem comp_eq_of_eq {C : Type*} [CategoryTheory.Category C] {A A' A'' : C}
    {u u' : A ⟶ A'} {v v' : A' ⟶ A''} {w w' : A ⟶ A''} (hu : u = u') (hv : v = v')
    (hw : w = w') (h : u' ≫ v' = w') : u ≫ v = w := by
  rwa [hu, hv, hw]

end Stacks

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre products of the site, read downstairs -/

/-- The morphism of schemes underlying a morphism `g` of `(Sch/S)_fppf`: the structure morphism of
the source of `g`, viewed as an object over the scheme of the target of `g`. It is the image of `g`
under `AlgebraicGeometry.BigFppfOver.toScheme`. -/
public abbrev objHomOver {Z W : BigFppfOver B S hS} (g : Z ⟶ W) :
    objScheme B S hS Z ⟶ objScheme B S hS W :=
  objHom B (objScheme B S hS W) (contains_objScheme B S hS W) (Over.mk g.left)

/-- Read on underlying schemes, the unique morphism from an object `T` of `(Sch/S)_fppf` to the
final object `S / S` is the structure morphism of `T`. -/
public theorem toScheme_map_from_mkIdTerminal (T : BigFppfOver B S hS) :
    (toScheme B S hS).map (Over.mkIdTerminal.from T) = objHom B S hS T := by
  show B.inclusion.map (Over.mkIdTerminal.from T).left = objHom B S hS T
  rw [Over.mkIdTerminal_from_left]
  rfl

/-- The scheme of the fibre product `AlgebraicGeometry.BigFppfOver.memberProd` of two members of a
family of objects of `(Sch/S)_fppf` is their scheme fibre product over `S`, with the two
projections and the two structure morphisms as legs. -/
public theorem isPullback_objHomOver_memberProd {I : Type w} (X : I → BigFppfOver B S hS)
    (i j : I) :
    IsPullback (objHomOver B S hS (memberProdFst B S hS X i j))
        (objHomOver B S hS (memberProdSnd B S hS X i j))
      (objHom B S hS (X i)) (objHom B S hS (X j)) := by
  have h : IsPullback (memberProdFst B S hS X i j) (memberProdSnd B S hS X i j)
      (Over.mkIdTerminal.from (X i)) (Over.mkIdTerminal.from (X j)) :=
    IsPullback.of_hasPullback _ _
  have h' := h.map (toScheme B S hS)
  rwa [toScheme_map_from_mkIdTerminal, toScheme_map_from_mkIdTerminal] at h'

/-- The fibre product of two members of a family of objects of `(Sch/S)_fppf`, read as a chosen
pullback of their structure morphisms: its underlying scheme is the scheme of
`AlgebraicGeometry.BigFppfOver.memberProd`, its projections are the two projections of that fibre
product read downstairs, and its morphism to `S` is the structure morphism of the fibre product. -/
public noncomputable abbrev memberChosenPullback {I : Type w} (X : I → BigFppfOver B S hS)
    (i j : I) : ChosenPullback (objHom B S hS (X i)) (objHom B S hS (X j)) where
  pullback := objScheme B S hS (memberProd B S hS X i j)
  p₁ := objHomOver B S hS (memberProdFst B S hS X i j)
  p₂ := objHomOver B S hS (memberProdSnd B S hS X i j)
  condition := (isPullback_objHomOver_memberProd B S hS X i j).w
  isLimit := (isPullback_objHomOver_memberProd B S hS X i j).isLimit
  p := objHom B S hS (memberProd B S hS X i j)
  hp₁ := (hom_hom_comp B S hS (memberProdFst B S hS X i j)).symm

/-- The threefold fibre product `X i₁ ×_S X i₂ ×_S X i₃` of three members of a family, formed
inside `(Sch/S)_fppf` as the fibre product of `X i₁ ×_S X i₂` and `X i₂ ×_S X i₃` over `X i₂`. -/
public noncomputable abbrev memberProd₃ {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) : BigFppfOver B S hS :=
  pullback (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃)

/-- The projection of the threefold fibre product onto the first member. -/
public noncomputable abbrev memberProd₃Fst {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) : memberProd₃ B S hS X i₁ i₂ i₃ ⟶ X i₁ :=
  pullback.fst _ _ ≫ memberProdFst B S hS X i₁ i₂

/-- The projection of the threefold fibre product onto the second member. -/
public noncomputable abbrev memberProd₃Mid {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) : memberProd₃ B S hS X i₁ i₂ i₃ ⟶ X i₂ :=
  pullback.fst _ _ ≫ memberProdSnd B S hS X i₁ i₂

/-- The projection of the threefold fibre product onto the third member. -/
public noncomputable abbrev memberProd₃Snd {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) : memberProd₃ B S hS X i₁ i₂ i₃ ⟶ X i₃ :=
  pullback.snd _ _ ≫ memberProdSnd B S hS X i₂ i₃

/-- The projection of the threefold fibre product onto the fibre product of the first and the third
member, obtained from the universal property over the final object. -/
public noncomputable abbrev memberProd₃Outer {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) : memberProd₃ B S hS X i₁ i₂ i₃ ⟶ memberProd B S hS X i₁ i₃ :=
  pullback.lift (memberProd₃Fst B S hS X i₁ i₂ i₃) (memberProd₃Snd B S hS X i₁ i₂ i₃)
    (Over.mkIdTerminal.hom_ext _ _)

/-- The fibre product of `a : Z ⟶ V` and `b : W ⟶ V` in `(Sch/S)_fppf`, read downstairs as a chosen
pullback of the images of `a` and `b`, with the image of `c` as its morphism to the base. -/
public noncomputable abbrev siteChosenPullback {V Z W : BigFppfOver B S hS} (a : Z ⟶ V)
    (b : W ⟶ V) (c : pullback a b ⟶ V) (hc : pullback.fst a b ≫ a = c) :
    ChosenPullback (objHomOver B S hS a) (objHomOver B S hS b) where
  pullback := objScheme B S hS (pullback a b)
  p₁ := objHomOver B S hS (pullback.fst a b)
  p₂ := objHomOver B S hS (pullback.snd a b)
  condition := ((IsPullback.of_hasPullback a b).map (toScheme B S hS)).w
  isLimit := ((IsPullback.of_hasPullback a b).map (toScheme B S hS)).isLimit
  p := objHomOver B S hS c
  hp₁ := congrArg (toScheme B S hS).map hc

/-- The threefold fibre product of three members, read as a chosen threefold wide pullback of their
structure morphisms: its underlying scheme is the scheme of
`AlgebraicGeometry.BigFppfOver.memberProd₃`, and its three projections and its morphism to the
fibre product of the outer two members are the projections of that object read downstairs. The
projection to the middle member is `AlgebraicGeometry.BigFppfOver.memberProd₃Mid`. -/
public noncomputable abbrev memberChosenPullback₃ {I : Type w} (X : I → BigFppfOver B S hS)
    (i₁ i₂ i₃ : I) :
    ChosenPullback₃ (memberChosenPullback B S hS X i₁ i₂)
      (memberChosenPullback B S hS X i₂ i₃) (memberChosenPullback B S hS X i₁ i₃) where
  chosenPullback :=
    siteChosenPullback B S hS (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃)
      (memberProd₃Mid B S hS X i₁ i₂ i₃) rfl
  p := objHom B S hS (memberProd₃ B S hS X i₁ i₂ i₃)
  p₁ := objHomOver B S hS (memberProd₃Fst B S hS X i₁ i₂ i₃)
  p₃ := objHomOver B S hS (memberProd₃Snd B S hS X i₁ i₂ i₃)
  l :=
    { f := objHomOver B S hS (memberProd₃Outer B S hS X i₁ i₂ i₃)
      f_p₁ := congrArg (toScheme B S hS).map (pullback.lift_fst _ _ _)
      f_p₂ := congrArg (toScheme B S hS).map (pullback.lift_snd _ _ _)
      f_p := (hom_hom_comp B S hS (memberProd₃Outer B S hS X i₁ i₂ i₃)).symm }
  hp₁ := rfl
  hp₃ := rfl

/-! ### The transitions, read on the chosen pullbacks -/

/-- The comparison isomorphism of Stacks 03DV is compatible with composition in the big fppf site:
reading the comparison at `g : Z' ⟶ Z` of the local datum transported along `g₀ : Z ⟶ T` through
the identification of the iterated pullback with the pullback along the composite returns the
comparison at `g ≫ g₀`. -/
public abbrev LocalComparisonPseudonatural (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    Prop :=
  ∀ {T Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) (g₀ : Z ⟶ T)
    (F : (objScheme B S hS T).Modules)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G),
    localAssociatedModuleComparison B S hS G g _
        (localAssociatedModuleComparison B S hS G g₀ F e) =
      (associatedModule B (objScheme B S hS Z')
            (contains_objScheme B S hS Z')).mapIso
          (pullModComp ((toScheme B S hS).map g) ((toScheme B S hS).map g₀)
            ((toScheme B S hS).map (g ≫ g₀))
            ((toScheme B S hS).map_comp g g₀).symm F).symm ≪≫
        localAssociatedModuleComparison B S hS G (g ≫ g₀) F e

/-- Given that the comparison of Stacks 03DV is pseudonatural (`hps`), pulling the transition
isomorphism at `Z` back along `g : Z' ⟶ Z` by
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` returns the transition at `Z'`
between the same two local data, read along `a₁ = g ≫ g₁` and `a₂ = g ≫ g₂`. -/
public theorem pullHom_eq_transitionIso (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hps : LocalComparisonPseudonatural B S hS G) {T₁ T₂ Z Z' : BigFppfOver B S hS}
    (g : Z' ⟶ Z) (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) {a₁ : Z' ⟶ T₁} (ha₁ : g ≫ g₁ = a₁)
    {a₂ : Z' ⟶ T₂} (ha₂ : g ≫ g₂ = a₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    pullHom (F := modulePullbackPseudofunctor)
        (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom (objHomOver B S hS g)
        (objHomOver B S hS a₁) (objHomOver B S hS a₂)
        (by subst ha₁; rfl) (by subst ha₂; rfl) =
      (transitionIso B S hS G a₁ a₂ hF₁ e₁ hF₂ e₂).hom := by
  subst ha₁ ha₂
  exact pullHom_transitionIso_of_comparison_comp B S hS G g g₁ g₂ hF₁ e₁ hF₂ e₂
    (pullModComp ((toScheme B S hS).map g) ((toScheme B S hS).map g₁)
      ((toScheme B S hS).map (g ≫ g₁)) ((toScheme B S hS).map_comp g g₁).symm F₁).symm
    (pullModComp ((toScheme B S hS).map g) ((toScheme B S hS).map g₂)
      ((toScheme B S hS).map (g ≫ g₂)) ((toScheme B S hS).map_comp g g₂).symm F₂).symm
    (hps g g₁ F₁ e₁) (hps g g₂ F₂ e₂)

/-! ### The descent datum -/

/-- The diagonal of the fibre product of a member of a family with itself, obtained from the
universal property over the final object. -/
public noncomputable abbrev memberProdDiag {I : Type w} (X : I → BigFppfOver B S hS) (i : I) :
    X i ⟶ memberProd B S hS X i i :=
  pullback.lift (𝟙 (X i)) (𝟙 (X i)) (Over.mkIdTerminal.hom_ext _ _)

variable {I : Type w} (G : SheafOfModules.{u} (structureSheaf B S hS))
  (X : I → BigFppfOver B S hS) (F : ∀ i, (objScheme B S hS (X i)).Modules)
  (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-- The transition isomorphism of the descent datum over the chosen fibre product
`AlgebraicGeometry.BigFppfOver.memberChosenPullback` of two members of the family: the transition
isomorphism `AlgebraicGeometry.BigFppfOver.transitionIso` at the two projections of
`X i ×_S X j`. -/
public noncomputable def memberTransition (i j : I) :
    pullMod (objHomOver B S hS (memberProdFst B S hS X i j)) (F i) ⟶
      pullMod (objHomOver B S hS (memberProdSnd B S hS X i j)) (F j) :=
  (transitionIso B S hS G (memberProdFst B S hS X i j) (memberProdSnd B S hS X i j)
    (hF i) (e i) (hF j) (e j)).hom

/-- Let `m : Z ⟶ X i₁ ×_S X i₂`, and let `a₁` and `a₂` be its two composites with the projections.
Given that the comparison of Stacks 03DV is pseudonatural, the transport `pullHom'` of the
transitions to the pair `(a₁, a₂)` is the transition isomorphism at `(a₁, a₂)`. -/
public theorem pullHom'_memberTransition (hps : LocalComparisonPseudonatural B S hS G)
    {i₁ i₂ : I} {Z : BigFppfOver B S hS} (m : Z ⟶ memberProd B S hS X i₁ i₂)
    {a₁ : Z ⟶ X i₁} (ha₁ : m ≫ memberProdFst B S hS X i₁ i₂ = a₁)
    {a₂ : Z ⟶ X i₂} (ha₂ : m ≫ memberProdSnd B S hS X i₁ i₂ = a₂)
    (q : objScheme B S hS Z ⟶ S)
    (hf₁ : objHomOver B S hS a₁ ≫ objHom B S hS (X i₁) = q)
    (hf₂ : objHomOver B S hS a₂ ≫ objHom B S hS (X i₂) = q) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberTransition B S hS G X F hF e) q
        (objHomOver B S hS a₁) (objHomOver B S hS a₂) hf₁ hf₂ =
      (transitionIso B S hS G a₁ a₂ (hF i₁) (e i₁) (hF i₂) (e i₂)).hom :=
  (pullHom'_eq_pullHom (sq := memberChosenPullback B S hS X)
      (memberTransition B S hS G X F hF e) q _ _ (objHomOver B S hS m) hf₁ hf₂
      (by subst ha₁; rfl) (by subst ha₂; rfl)).trans
    (pullHom_eq_transitionIso B S hS G hps m (memberProdFst B S hS X i₁ i₂)
      (memberProdSnd B S hS X i₁ i₂) ha₁ ha₂ (hF i₁) (e i₁) (hF i₂) (e i₂))

/-- The transitions are the identity at a repeated member, the `pullHom'_hom_self` field of
`CategoryTheory.Pseudofunctor.DescentData'`, given that the comparison of Stacks 03DV is
pseudonatural. -/
public theorem pullHom'_memberTransition_self (hps : LocalComparisonPseudonatural B S hS G)
    (i : I) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberTransition B S hS G X F hF e)
        (objHom B S hS (X i)) (𝟙 (objScheme B S hS (X i))) (𝟙 (objScheme B S hS (X i)))
        (Category.id_comp _) (Category.id_comp _) = 𝟙 _ :=
  (pullHom'_memberTransition B S hS G X F hF e hps (memberProdDiag B S hS X i)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (objHom B S hS (X i))
      (Category.id_comp _) (Category.id_comp _)).trans
    (transitionIso_self B S hS G (𝟙 (X i)) (hF i) (e i))

/-- The transitions satisfy the cocycle condition, the `pullHom'_hom_comp` field of
`CategoryTheory.Pseudofunctor.DescentData'`: over the threefold fibre product
`X i₁ ×_S X i₂ ×_S X i₃`, the transport of the transitions from `X i₁` to `X i₂` followed by the
transport from `X i₂` to `X i₃` is the transport from `X i₁` to `X i₃`. The pseudonaturality of the
comparison of Stacks 03DV is the only hypothesis. -/
public theorem pullHom'_memberTransition_comp (hps : LocalComparisonPseudonatural B S hS G)
    (i₁ i₂ i₃ : I) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberTransition B S hS G X F hF e)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₁
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₂ ≫
        pullHom' (sq := memberChosenPullback B S hS X) (memberTransition B S hS G X F hF e)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₃ =
      pullHom' (sq := memberChosenPullback B S hS X) (memberTransition B S hS G X F hF e)
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₁
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₃ := by
  have h₁ := pullHom'_memberTransition B S hS G X F hF e hps
    (pullback.fst (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
    (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) rfl
    (a₂ := memberProd₃Mid B S hS X i₁ i₂ i₃) rfl _
    (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₁ (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₂
  have h₂ := pullHom'_memberTransition B S hS G X F hF e hps
    (pullback.snd (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
    (a₁ := memberProd₃Mid B S hS X i₁ i₂ i₃) pullback.condition.symm
    (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) rfl _
    (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₂ (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₃
  have h₃ := pullHom'_memberTransition B S hS G X F hF e hps
    (memberProd₃Outer B S hS X i₁ i₂ i₃)
    (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) (pullback.lift_fst _ _ _)
    (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) (pullback.lift_snd _ _ _) _
    (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₁ (memberChosenPullback₃ B S hS X i₁ i₂ i₃).w₃
  refine Stacks.comp_eq_of_eq h₁ h₂ h₃ ?_
  exact transitionIso_trans B S hS G (memberProd₃Fst B S hS X i₁ i₂ i₃)
    (memberProd₃Mid B S hS X i₁ i₂ i₃) (memberProd₃Snd B S hS X i₁ i₂ i₃)
    (hF i₁) (e i₁) (hF i₂) (e i₂) (hF i₃) (e i₃)

end AlgebraicGeometry.BigFppfOver

end
