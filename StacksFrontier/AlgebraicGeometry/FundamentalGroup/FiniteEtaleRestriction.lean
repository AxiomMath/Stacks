module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of finite étale covers to the neighbourhoods of a closed subscheme

Let `X` be a scheme and `Y ⊆ X` a closed subscheme, given by its ideal sheaf. The open
subschemes `W ⊆ X` containing `Y` form a poset under reverse inclusion, and each of them
carries the category `FÉt_W` of schemes finite étale over it. Restricting a cover along the
inclusion `W' ⊆ W` is base change, so the assignment `W ↦ FÉt_W` is a functor only up to the
canonical isomorphisms between iterated pullbacks: it is a *pseudofunctor* into `Cat`.

This file constructs that pseudofunctor. The input is the composition isomorphism
`AlgebraicGeometry.finiteEtaleBaseChangeComp` for base change on finite étale covers, the
identity isomorphism `AlgebraicGeometry.finiteEtaleBaseChangeId`, and the three coherence
identities they satisfy (the pentagon and the two unitors), all proved here.

## Main definitions

* `AlgebraicGeometry.finiteEtaleBaseChangeProj` — the projection from a base-changed finite
  étale cover back to the original cover.
* `AlgebraicGeometry.finiteEtaleBaseChangeId` — base change along an identity is the identity.
* `AlgebraicGeometry.finiteEtaleBaseChangeComp` — base change along a composite is the
  composite of base changes, in the other order.
* `Stacks.FundamentalGroup.Neighborhood` — the open neighbourhoods of a closed subscheme,
  ordered by reverse inclusion. They are filtered, and the chosen factorisations of the closed
  immersion through them are compatible with shrinking
  (`Stacks.FundamentalGroup.Neighborhood.toSchemeHom_comp`), which is what makes restriction to
  the closed subscheme a cocone.
* `Stacks.FundamentalGroup.finiteEtaleRestrictionPseudofunctor` — the finite étale restriction
  pseudofunctor on those neighbourhoods.
* `Stacks.FundamentalGroup.FiniteEtaleColimitPresentation` — a strict presentation of that
  pseudodiagram together with its restriction cocone to the closed subscheme.

## Main results

* `AlgebraicGeometry.finiteEtaleBaseChangeComp_assoc`,
  `AlgebraicGeometry.finiteEtaleBaseChangeComp_id_right` and
  `AlgebraicGeometry.finiteEtaleBaseChangeComp_id_left` — the pentagon and the two unitor
  identities for the base-change composition isomorphism.

## Implementation notes

`AlgebraicGeometry.finiteEtaleBaseChange` is `MorphismProperty.Over.pullback`, so an object of
`FÉt_{W'}` obtained by base change is a *chosen* pullback and its underlying scheme is
`pullback A.hom u` only up to unfolding. Writing `pullback.fst A.hom u` directly in a goal
therefore produces a term that is not type-correct at the `implicit` transparency level, which
silently blocks `rw` and `simp`. Every projection in this file is accordingly taken in the form
`finiteEtaleBaseChangeProj`, whose stated type already mentions the base-changed object; this
is what makes the coherence proofs go through by rewriting. For the same reason the
extensionality principles `finiteEtaleOver_hom_ext` and `finiteEtaleBaseChangeProj_hom_ext`
are phrased with `finiteEtaleBaseChangeProj` rather than with `pullback.fst`.

The index poset is `OrderDual`, so a morphism `W ⟶ W'` of neighbourhoods is an inclusion
`W' ⊆ W` and restriction goes in the direction of the morphism. Because the index category is
a poset its morphisms are subsingletons, which is why the associativity comparison in a
pseudofunctor out of it lands on `eqToHom` of a reflexivity proof.

## References

* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/-- The projection from the base change of a finite étale cover `A` of `T` along `u : S ⟶ T`
to `A` itself. This is the first projection of the defining pullback, stated at the type of the
base-changed object so that it can be rewritten with. -/
def finiteEtaleBaseChangeProj {S T : Scheme.{u}} (u : S ⟶ T) (A : FiniteEtaleOver T) :
    ((finiteEtaleBaseChange u).obj A).left ⟶ A.left :=
  pullback.fst A.hom u

/-- The projection to the original cover is natural in the cover. -/
theorem finiteEtaleBaseChangeProj_naturality {S T : Scheme.{u}} (u : S ⟶ T)
    {A B : FiniteEtaleOver T} (φ : A ⟶ B) :
    ((finiteEtaleBaseChange u).map φ).left ≫ finiteEtaleBaseChangeProj u B
      = finiteEtaleBaseChangeProj u A ≫ φ.left :=
  finiteEtaleBaseChange_map_left_fst u φ

/-- The defining square of a base-changed finite étale cover commutes. -/
theorem finiteEtaleBaseChangeProj_comp_hom {S T : Scheme.{u}} (u : S ⟶ T)
    (A : FiniteEtaleOver T) :
    finiteEtaleBaseChangeProj u A ≫ A.hom
      = ((finiteEtaleBaseChange u).obj A).hom ≫ u :=
  pullback.condition

/-- Two morphisms of schemes into a base-changed finite étale cover agree as soon as they agree
after the projection to the original cover and after the structure morphism. -/
theorem finiteEtaleBaseChangeProj_hom_ext {S T : Scheme.{u}} (u : S ⟶ T)
    (A : FiniteEtaleOver T) {Z : Scheme.{u}}
    {x y : Z ⟶ ((finiteEtaleBaseChange u).obj A).left}
    (h₁ : x ≫ finiteEtaleBaseChangeProj u A = y ≫ finiteEtaleBaseChangeProj u A)
    (h₂ : x ≫ ((finiteEtaleBaseChange u).obj A).hom
      = y ≫ ((finiteEtaleBaseChange u).obj A).hom) : x = y :=
  pullback.hom_ext h₁ h₂

/-- Two morphisms of finite étale covers with target a base-changed cover agree as soon as they
agree after the projection to the original cover: compatibility with the structure morphisms is
automatic. -/
theorem finiteEtaleOver_hom_ext {S T : Scheme.{u}} (u : S ⟶ T) {A : FiniteEtaleOver T}
    {B : FiniteEtaleOver S} {x y : B ⟶ (finiteEtaleBaseChange u).obj A}
    (h : x.left ≫ finiteEtaleBaseChangeProj u A = y.left ≫ finiteEtaleBaseChangeProj u A) :
    x = y :=
  MorphismProperty.Over.Hom.ext
    (finiteEtaleBaseChangeProj_hom_ext u A h
      ((MorphismProperty.Over.w x).trans (MorphismProperty.Over.w y).symm))

/-- The identity of a finite étale cover, written as a morphism of its underlying schemes. -/
theorem finiteEtaleOver_id_left {S : Scheme.{u}} (A : FiniteEtaleOver S) :
    (𝟙 A : A ⟶ A).left = 𝟙 A.left :=
  rfl

/-- The pullback of a finite étale cover along the identity, as an isomorphism of schemes.

The name says `finiteEtale` because `AlgebraicGeometry.pullbackIdIso` is taken, by the
identity-pullback isomorphism for a sheaf of *modules* in
`StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic`; the two are about different
objects. -/
def finiteEtalePullbackIdIso {S : Scheme.{u}} (A : FiniteEtaleOver S) :
    pullback A.hom (𝟙 S) ≅ A.left where
  hom := pullback.fst A.hom (𝟙 S)
  inv := pullback.lift (𝟙 A.left) A.hom (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition,
        Category.comp_id]
  inv_hom_id := pullback.lift_fst _ _ _

/-- Base change of finite étale covers along the identity is the identity functor. -/
def finiteEtaleBaseChangeId {S : Scheme.{u}} :
    finiteEtaleBaseChange (𝟙 S) ≅ 𝟭 (FiniteEtaleOver S) :=
  NatIso.ofComponents
    (fun A => MorphismProperty.Over.isoMk (finiteEtalePullbackIdIso A)
      (pullback.condition.trans (Category.comp_id _)))
    (fun _ => MorphismProperty.Over.Hom.ext (finiteEtaleBaseChange_map_left_fst _ _))

/-- On underlying schemes, the identity base-change isomorphism is the projection. -/
theorem finiteEtaleBaseChangeId_hom_app_left {S : Scheme.{u}} (A : FiniteEtaleOver S) :
    (finiteEtaleBaseChangeId.hom.app A).left = finiteEtaleBaseChangeProj (𝟙 S) A :=
  rfl

/-- Base change along a composite is the composite of the base changes, in the other order.
The composite is supplied as a separate argument so that the isomorphism can be used for a
morphism that is only *equal* to a composite, which is what happens for the inclusions of a
poset of opens. -/
def finiteEtaleBaseChangeComp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (fg : S ⟶ U := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    finiteEtaleBaseChange fg ≅ finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange f :=
  MorphismProperty.Over.pullbackComp f g fg hfg

/-- The composition isomorphism is compatible with the projections to the original cover. -/
theorem finiteEtaleBaseChangeComp_hom_app_left_proj {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (fg : S ⟶ U) (hfg : fg = f ≫ g) (A : FiniteEtaleOver U) :
    ((finiteEtaleBaseChangeComp f g fg hfg).hom.app A).left ≫
        finiteEtaleBaseChangeProj f ((finiteEtaleBaseChange g).obj A) ≫
        finiteEtaleBaseChangeProj g A
      = finiteEtaleBaseChangeProj fg A := by
  subst hfg
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g A

/-- Two morphisms of finite étale covers into a threefold base change agree as soon as they
agree after all three projections to the original cover. -/
theorem finiteEtaleOver_hom_ext₃ {A₀ B C D : Scheme.{u}} (a : D ⟶ C) (b : C ⟶ B) (c : B ⟶ A₀)
    (A : FiniteEtaleOver A₀) {W : FiniteEtaleOver D}
    {x y : W ⟶ (finiteEtaleBaseChange a).obj
      ((finiteEtaleBaseChange b).obj ((finiteEtaleBaseChange c).obj A))}
    (h : x.left ≫ finiteEtaleBaseChangeProj a _ ≫ finiteEtaleBaseChangeProj b _ ≫
          finiteEtaleBaseChangeProj c A
        = y.left ≫ finiteEtaleBaseChangeProj a _ ≫ finiteEtaleBaseChangeProj b _ ≫
          finiteEtaleBaseChangeProj c A) :
    x = y := by
  have key : ∀ z : W ⟶ (finiteEtaleBaseChange a).obj
      ((finiteEtaleBaseChange b).obj ((finiteEtaleBaseChange c).obj A)),
      (z.left ≫ finiteEtaleBaseChangeProj a
          ((finiteEtaleBaseChange b).obj ((finiteEtaleBaseChange c).obj A))) ≫
        ((finiteEtaleBaseChange b).obj ((finiteEtaleBaseChange c).obj A)).hom
        = W.hom ≫ a := by
    intro z
    rw [Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc,
      MorphismProperty.Over.w]
  refine finiteEtaleOver_hom_ext a (finiteEtaleBaseChangeProj_hom_ext b _ ?_ ?_)
  · refine finiteEtaleBaseChangeProj_hom_ext c A ?_ ?_
    · simpa only [Category.assoc] using h
    · simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
      simp only [← Category.assoc, key x, key y]
  · exact (key x).trans (key y).symm

/-- **The pentagon identity** for the base-change composition isomorphism: the two ways of
comparing base change along a threefold composite with the threefold composite of base changes
agree. -/
theorem finiteEtaleBaseChangeComp_assoc {A₀ B C D : Scheme.{u}} (a : D ⟶ C) (b : C ⟶ B)
    (c : B ⟶ A₀) (bc : C ⟶ A₀) (hbc : bc = b ≫ c) (ab : D ⟶ B) (hab : ab = a ≫ b)
    (w : D ⟶ A₀) (hw : w = a ≫ bc) (hw' : w = ab ≫ c) :
    (finiteEtaleBaseChangeComp a bc w hw).hom ≫
        Functor.whiskerRight (finiteEtaleBaseChangeComp b c bc hbc).hom
          (finiteEtaleBaseChange a) ≫
        (Functor.associator (finiteEtaleBaseChange c) (finiteEtaleBaseChange b)
          (finiteEtaleBaseChange a)).hom ≫
        Functor.whiskerLeft (finiteEtaleBaseChange c)
          (finiteEtaleBaseChangeComp a b ab hab).inv ≫
        (finiteEtaleBaseChangeComp ab c w hw').inv
      = eqToHom (rfl : finiteEtaleBaseChange w = finiteEtaleBaseChange w) := by
  have key : (finiteEtaleBaseChangeComp a bc w hw).hom ≫
      Functor.whiskerRight (finiteEtaleBaseChangeComp b c bc hbc).hom
        (finiteEtaleBaseChange a) ≫
      (Functor.associator (finiteEtaleBaseChange c) (finiteEtaleBaseChange b)
        (finiteEtaleBaseChange a)).hom
      = (finiteEtaleBaseChangeComp ab c w hw').hom ≫
        Functor.whiskerLeft (finiteEtaleBaseChange c)
          (finiteEtaleBaseChangeComp a b ab hab).hom := by
    refine NatTrans.ext (funext fun A => finiteEtaleOver_hom_ext₃ a b c A ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, MorphismProperty.Comma.comp_left, Category.assoc,
      Functor.comp_obj]
    rw [finiteEtaleOver_id_left, Category.id_comp]
    slice_lhs 2 3 => rw [finiteEtaleBaseChangeProj_naturality]
    slice_lhs 3 5 => rw [finiteEtaleBaseChangeComp_hom_app_left_proj b c bc hbc A]
    slice_lhs 1 3 => rw [finiteEtaleBaseChangeComp_hom_app_left_proj a bc w hw A]
    slice_rhs 2 4 => rw [finiteEtaleBaseChangeComp_hom_app_left_proj a b ab hab _]
    slice_rhs 1 3 => rw [finiteEtaleBaseChangeComp_hom_app_left_proj ab c w hw' A]
  slice_lhs 1 3 => rw [key]
  slice_lhs 2 3 => rw [← Functor.whiskerLeft_comp, Iso.hom_inv_id]
  simp

/-- The right unitor identity: comparing base change along `f` with base change along `f`
followed by base change along an identity. -/
theorem finiteEtaleBaseChangeComp_id_right {S T : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ T)
    (hg : g = 𝟙 T) (fg : S ⟶ T) (hfg : fg = f ≫ g) :
    (finiteEtaleBaseChangeComp f g fg hfg).hom ≫
        Functor.whiskerRight (eqToIso (by rw [hg]) ≪≫ finiteEtaleBaseChangeId).hom
          (finiteEtaleBaseChange f) ≫
        (Functor.leftUnitor (finiteEtaleBaseChange f)).hom
      = eqToHom (by rw [hfg, hg, Category.comp_id]) := by
  subst hg
  rw [Category.comp_id] at hfg
  subst hfg
  refine NatTrans.ext (funext fun A => finiteEtaleOver_hom_ext fg ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Functor.leftUnitor_hom_app, MorphismProperty.Comma.comp_left,
    NatTrans.id_app, Category.id_comp, Category.assoc, Functor.comp_obj, Functor.id_obj,
    MorphismProperty.Comma.id_hom, CategoryTheory.Comma.id_left]
  rw [finiteEtaleBaseChangeProj_naturality, finiteEtaleBaseChangeId_hom_app_left]
  exact finiteEtaleBaseChangeComp_hom_app_left_proj fg (𝟙 T) fg hfg A

/-- The left unitor identity: comparing base change along `g` with base change along an
identity followed by base change along `g`. -/
theorem finiteEtaleBaseChangeComp_id_left {S T : Scheme.{u}} (f : S ⟶ S) (hf : f = 𝟙 S)
    (g : S ⟶ T) (fg : S ⟶ T) (hfg : fg = f ≫ g) :
    (finiteEtaleBaseChangeComp f g fg hfg).hom ≫
        Functor.whiskerLeft (finiteEtaleBaseChange g)
          (eqToIso (by rw [hf]) ≪≫ finiteEtaleBaseChangeId).hom ≫
        (Functor.rightUnitor (finiteEtaleBaseChange g)).hom
      = eqToHom (by rw [hfg, hf, Category.id_comp]) := by
  subst hf
  rw [Category.id_comp] at hfg
  subst hfg
  refine NatTrans.ext (funext fun A => finiteEtaleOver_hom_ext fg ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Functor.rightUnitor_hom_app, MorphismProperty.Comma.comp_left,
    NatTrans.id_app, Category.id_comp, Category.assoc, Functor.comp_obj, Functor.id_obj,
    MorphismProperty.Comma.id_hom, CategoryTheory.Comma.id_left]
  rw [finiteEtaleBaseChangeId_hom_app_left]
  exact finiteEtaleBaseChangeComp_hom_app_left_proj (𝟙 S) fg fg hfg A

end AlgebraicGeometry

namespace Stacks.FundamentalGroup

open AlgebraicGeometry

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- The open subschemes of `X` through which the closed subscheme cut out by `Y` factors,
ordered by reverse inclusion. -/
abbrev Neighborhood :=
  OrderDual { W : X.Opens // ∃ r : Y.subscheme ⟶ W.toScheme, r ≫ W.ι = Y.subschemeι }

/-- The open subscheme underlying a neighbourhood. -/
abbrev Neighborhood.open (W : Neighborhood X Y) : X.Opens :=
  (OrderDual.ofDual W).val

/-- A chosen factorisation of the closed subscheme through a neighbourhood. -/
def Neighborhood.toSchemeHom (W : Neighborhood X Y) :
    Y.subscheme ⟶ (Neighborhood.open X Y W).toScheme :=
  Classical.choose (OrderDual.ofDual W).property

private theorem exists_lift_iff_forall_mem {Z T : Scheme.{u}} (f : Z ⟶ T) (W : T.Opens) :
    (∃ r : Z ⟶ W.toScheme, r ≫ W.ι = f) ↔ ∀ z : Z, f z ∈ W := by
  constructor
  · rintro ⟨r, rfl⟩ z
    exact (r z).property
  · intro h
    have hr : Set.range f ⊆ Set.range W.ι := by
      simpa only [Scheme.Opens.range_ι] using Set.range_subset_iff.mpr h
    exact ⟨IsOpenImmersion.lift W.ι f hr, IsOpenImmersion.lift_fac _ _ _⟩

private theorem exists_lift_subschemeι_iff (W : X.Opens) :
    (∃ r : Y.subscheme ⟶ W.toScheme, r ≫ W.ι = Y.subschemeι) ↔
      (Y.support : Set X) ⊆ (W : Set X) := by
  rw [← Y.range_subschemeι, Set.range_subset_iff]
  exact exists_lift_iff_forall_mem Y.subschemeι W

/-- The closed subscheme cut out by `Y` is set-theoretically contained in each of its
neighbourhoods. -/
theorem Neighborhood.support_subset_open (W : Neighborhood X Y) :
    (Y.support : Set X) ⊆ (Neighborhood.open X Y W : Set X) :=
  (exists_lift_subschemeι_iff X Y (Neighborhood.open X Y W)).mp (OrderDual.ofDual W).property

/-- The chosen factorisation does factor the closed immersion of the subscheme. -/
theorem Neighborhood.toSchemeHom_fac (W : Neighborhood X Y) :
    Neighborhood.toSchemeHom X Y W ≫ (Neighborhood.open X Y W).ι = Y.subschemeι :=
  Classical.choose_spec (OrderDual.ofDual W).property

/-- The chosen factorisations are compatible with shrinking a neighbourhood. This is what makes
restriction to the closed subscheme a cocone on the restriction diagram. -/
theorem Neighborhood.toSchemeHom_comp {W W' : Neighborhood X Y} (i : W ⟶ W') :
    Neighborhood.toSchemeHom X Y W' ≫ X.homOfLE i.le =
      Neighborhood.toSchemeHom X Y W := by
  have hi : Neighborhood.open X Y W' ≤ Neighborhood.open X Y W := i.le
  have hinc : X.homOfLE hi ≫ (Neighborhood.open X Y W).ι =
      (Neighborhood.open X Y W').ι := Scheme.homOfLE_ι X hi
  apply (cancel_mono (Neighborhood.open X Y W).ι).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => Neighborhood.toSchemeHom X Y W' ≫ g) hinc).trans
      ((Neighborhood.toSchemeHom_fac X Y W').trans
        (Neighborhood.toSchemeHom_fac X Y W).symm))

/-- The neighbourhoods of a closed subscheme are a filtered category: two of them meet in a
third, and the index category is a poset. -/
instance : IsFiltered (Neighborhood X Y) where
  cocone_objs V W :=
    ⟨⟨Neighborhood.open X Y V ⊓ Neighborhood.open X Y W,
        (exists_lift_subschemeι_iff X Y _).mpr fun _ hz =>
          ⟨Neighborhood.support_subset_open X Y V hz,
            Neighborhood.support_subset_open X Y W hz⟩⟩,
      homOfLE (show Neighborhood.open X Y V ⊓ Neighborhood.open X Y W ≤
        Neighborhood.open X Y V from inf_le_left),
      homOfLE (show Neighborhood.open X Y V ⊓ Neighborhood.open X Y W ≤
        Neighborhood.open X Y W from inf_le_right), trivial⟩
  cocone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
  nonempty := ⟨⟨⊤, (exists_lift_subschemeι_iff X Y ⊤).mpr fun _ _ => trivial⟩⟩

/-- Base change to the closed subscheme factors through base change to a smaller
neighbourhood. This is the comparison that identifies restriction to the closed subscheme with
restriction along the transition maps of the diagram. -/
def Neighborhood.baseChangeCompIso {W W' : Neighborhood X Y} (i : W ⟶ W') :
    finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W) ≅
      finiteEtaleBaseChange (X.homOfLE i.le) ⋙
        finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W') :=
  finiteEtaleBaseChangeComp (Neighborhood.toSchemeHom X Y W') (X.homOfLE i.le)
    (Neighborhood.toSchemeHom X Y W) (Neighborhood.toSchemeHom_comp X Y i).symm

/-- **Restriction of finite étale covers to the neighbourhoods of a closed subscheme.**
The pseudofunctor on the poset of open neighbourhoods of the closed subscheme cut out by `Y`
whose value at `W` is the category of finite étale covers of `W` and whose value on an
inclusion is base change along it. -/
def finiteEtaleRestrictionPseudofunctor :
    { F : Pseudofunctor (LocallyDiscrete (Neighborhood X Y)) Cat.{u, u + 1} //
      ∃ hobj : ∀ W : Neighborhood X Y,
          F.obj ⟨W⟩ = Cat.of (FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
        ∀ {W W' : Neighborhood X Y} (i : W ⟶ W'),
          eqToHom (hobj W).symm ≫ F.map ⟨i⟩ ≫ eqToHom (hobj W') =
            (finiteEtaleBaseChange (X.homOfLE i.le)).toCatHom } :=
  ⟨LocallyDiscrete.mkPseudofunctor
      (fun W => Cat.of (FiniteEtaleOver (Neighborhood.open X Y W).toScheme))
      (fun {_ _} i => (finiteEtaleBaseChange (X.homOfLE i.le)).toCatHom)
      (fun _ => Cat.Hom.isoMk
        (eqToIso (by rw [Scheme.homOfLE_rfl]) ≪≫ finiteEtaleBaseChangeId))
      (fun {_ _ _} i j => Cat.Hom.isoMk
        (finiteEtaleBaseChangeComp (X.homOfLE j.le) (X.homOfLE i.le)
          (X.homOfLE (i ≫ j).le) (Scheme.homOfLE_homOfLE X j.le i.le).symm))
      (fun {_ _ _ _} i j k => Cat.Hom₂.ext
        (finiteEtaleBaseChangeComp_assoc (X.homOfLE k.le) (X.homOfLE j.le) (X.homOfLE i.le)
          (X.homOfLE (i ≫ j).le) (Scheme.homOfLE_homOfLE X j.le i.le).symm
          (X.homOfLE (j ≫ k).le) (Scheme.homOfLE_homOfLE X k.le j.le).symm
          (X.homOfLE (i ≫ j ≫ k).le) _ _))
      (fun {b₀ _} i => Cat.Hom₂.ext
        (finiteEtaleBaseChangeComp_id_right (X.homOfLE i.le) (X.homOfLE (𝟙 b₀).le)
          (Scheme.homOfLE_rfl X _) (X.homOfLE (𝟙 b₀ ≫ i).le) _))
      (fun {_ b₁} i => Cat.Hom₂.ext
        (finiteEtaleBaseChangeComp_id_left (X.homOfLE (𝟙 b₁).le) (Scheme.homOfLE_rfl X _)
          (X.homOfLE i.le) (X.homOfLE (i ≫ 𝟙 b₁).le) _)),
    fun _ => rfl, fun _ => rfl⟩

/-- A strict presentation of the finite étale restriction pseudodiagram, together with its
canonical cocone to the category of finite étale covers of the closed subscheme.

A pseudofunctor into `Cat` is not a functor, so before one can take a colimit of the diagram
`W ↦ FÉt_W` one must replace it by an honest functor: a strict diagram, an equivalence of each
of its values with the corresponding category of finite étale covers, and a strong
transformation identifying the strict diagram with the restriction pseudofunctor coherently.
The cocone records restriction to the closed subscheme, compatibly with the transition
functors. -/
structure FiniteEtaleColimitPresentation where
  /-- The strict diagram replacing the restriction pseudofunctor. -/
  diagram : Neighborhood X Y ⥤ Cat.{u, u + 1}
  /-- Each value of the strict diagram is equivalent to the finite étale covers of the
  corresponding neighbourhood. -/
  stage (W : Neighborhood X Y) : (diagram.obj W) ≌
    FiniteEtaleOver (Neighborhood.open X Y W).toScheme
  /-- The strong transformation identifying the strict diagram with the restriction
  pseudofunctor. -/
  comparison : Pseudofunctor.StrongTrans diagram.toPseudofunctor'
    (finiteEtaleRestrictionPseudofunctor X Y).val
  /-- The identification is the chosen equivalence at every stage. -/
  comparison_stage (W : Neighborhood X Y) :
    ((comparison.app ⟨W⟩) ≫
      eqToHom ((finiteEtaleRestrictionPseudofunctor X Y).property.choose W)).toFunctor =
      (stage W).functor
  /-- The restriction cocone. -/
  cocone : Cocone diagram
  /-- Its point is the category of finite étale covers of the closed subscheme. -/
  coconePointIso : cocone.pt ≅ Cat.of (FiniteEtaleOver Y.subscheme)
  /-- At every stage the cocone is restriction to the closed subscheme. This is an isomorphism
  and not an equality: the two functors send a cover to two independently chosen pullbacks,
  which are canonically isomorphic and not equal. -/
  restriction (W : Neighborhood X Y) :
    (stage W).functor ⋙ finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W) ≅
      (cocone.ι.app W).toFunctor ⋙ coconePointIso.hom.toFunctor

end Stacks.FundamentalGroup

end
