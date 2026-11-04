module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomCompAssoc
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# The cocycle identity for the composition comparisons of sheaves of modules

Let `X ⟶ Y ⟶ Z ⟶ W` be three composable morphisms of ringed topoi
(`AlgebraicGeometry.RingedToposHom`s). Direct image of sheaves of modules carries a comparison
`(g ∘ f)_* ≅ f_* ⋙ g_*` (`pushforwardModulesCompIso`) and inverse image the adjoint one
`(g ∘ f)^* ≅ g^* ⋙ f^*` (`pullbackModulesCompIso`). For a threefold composite there are two ways to
compare the direct image of the composite with the threefold composite of the direct images,
through `g ∘ f` or through `h ∘ g`. They agree, and so do the two adjoint comparisons for inverse
images. The two bracketings of the threefold composite are equal but not definitionally so, and the
statements carry the transport along that equality.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso_assoc`: the cocycle identity for
  the direct-image comparison.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_assoc`: the cocycle identity for the
  inverse-image comparison.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_assoc_of_eq`: the same with the two
  bracketings of the threefold composite each compared with a third morphism instead of with
  each other, so that no type mentions both.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w' v'' u'' w'' v₃ u₃ w₃

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}} {W : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [W.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [W.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]

/-- Transport of the direct image of sheaves of modules along an equality of morphisms of ringed
topoi, read on underlying sheaves of sets: it is the transport along the induced equality of
direct images of the underlying topoi. -/
theorem pushforwardModulesUnderlyingIso_eqToHom (a b : RingedToposHom X W) (e : a = b)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((eqToHom (congrArg (fun m : RingedToposHom X W => pushforwardModules m) e)).app M) ≫
        (pushforwardModulesUnderlyingIso b).hom.app M =
      (pushforwardModulesUnderlyingIso a).hom.app M ≫
        (eqToHom (congrArg (fun m : RingedToposHom X W => m.toToposHom.pushforward) e)).app
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).obj M) := by
  subst e
  simp

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [W.J.HasSheafCompose (forget AddCommGrpCat.{w₃})] in
/-- The transport of direct images of the underlying topoi along the associativity of
composition of morphisms of ringed topoi is the identity. -/
theorem toToposHom_pushforward_eqToHom_app (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) (e : h.comp (g.comp f) = (h.comp g).comp f) (A : X.Topos) :
    (eqToHom (congrArg (fun m : RingedToposHom X W => m.toToposHom.pushforward) e)).app A =
      𝟙 _ :=
  rfl

/-- The comparison `(h ∘ g ∘ f)_*M ⟶ h_*g_*f_*M` of underlying sheaves of sets, computed along
the bracketing through `g ∘ f`: it is the underlying comparison for the threefold composite. -/
theorem pushforwardModulesCompIso_assoc_underlying_right (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) (h : RingedToposHom Z W)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((pushforwardModulesCompIso (g.comp f) h).hom.app M) ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((pushforwardModules h).map ((pushforwardModulesCompIso f g).hom.app M)) ≫
        (pushforwardModulesUnderlyingIso h).hom.app
          ((pushforwardModules g).obj ((pushforwardModules f).obj M)) ≫
        h.toToposHom.pushforward.map ((pushforwardModulesUnderlyingIso g).hom.app
          ((pushforwardModules f).obj M)) ≫
        h.toToposHom.pushforward.map (g.toToposHom.pushforward.map
          ((pushforwardModulesUnderlyingIso f).hom.app M)) =
      (pushforwardModulesUnderlyingIso (h.comp (g.comp f))).hom.app M := by
  simp only [Functor.comp_map]
  rw [dsimp% (pushforwardModulesUnderlyingIso h).hom.naturality_assoc
      ((pushforwardModulesCompIso f g).hom.app M),
    ← h.toToposHom.pushforward.map_comp, ← h.toToposHom.pushforward.map_comp,
    dsimp% (pushforwardModulesCompIso_underlying f g M)]
  exact dsimp% (pushforwardModulesCompIso_underlying (g.comp f) h M)

/-- The same comparison computed along the bracketing through `h ∘ g`: it is the underlying
comparison for the *other* bracketing of the threefold composite. -/
theorem pushforwardModulesCompIso_assoc_underlying_mid (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) (h : RingedToposHom Z W)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((pushforwardModulesCompIso f (h.comp g)).hom.app M) ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((pushforwardModulesCompIso g h).hom.app ((pushforwardModules f).obj M)) ≫
        (pushforwardModulesUnderlyingIso h).hom.app
          ((pushforwardModules g).obj ((pushforwardModules f).obj M)) ≫
        h.toToposHom.pushforward.map ((pushforwardModulesUnderlyingIso g).hom.app
          ((pushforwardModules f).obj M)) ≫
        h.toToposHom.pushforward.map (g.toToposHom.pushforward.map
          ((pushforwardModulesUnderlyingIso f).hom.app M)) =
      (pushforwardModulesUnderlyingIso ((h.comp g).comp f)).hom.app M := by
  simp only [Functor.comp_map]
  rw [reassoc_of% (pushforwardModulesCompIso_underlying g h ((pushforwardModules f).obj M))]
  exact dsimp% (pushforwardModulesCompIso_underlying f (h.comp g) M)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- The transport along an equality `e` of the two bracketings of the threefold composite,
composed with the underlying comparison for one bracketing, is the underlying comparison for the
other. -/
theorem pushforwardModulesUnderlyingIso_eqToHom_assoc (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) (h : RingedToposHom Z W)
    (e : h.comp (g.comp f) = (h.comp g).comp f)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := W.J)) W.O)).map
          ((eqToHom (congrArg (fun m : RingedToposHom X W => pushforwardModules m) e)).app M) ≫
        (pushforwardModulesUnderlyingIso ((h.comp g).comp f)).hom.app M =
      (pushforwardModulesUnderlyingIso (h.comp (g.comp f))).hom.app M := by
  refine (pushforwardModulesUnderlyingIso_eqToHom _ _ e M).trans ?_
  rw [toToposHom_pushforward_eqToHom_app f g h e]
  exact Category.comp_id _

/-- **The cocycle identity for the direct-image composition comparison, componentwise.**
Comparing `(h ∘ g ∘ f)_*M` with `f_*(h ∘ g)_*M` and then with `f_*g_*h_*M` agrees, after the
transport along `e`, with comparing it with `h_*(g ∘ f)_*M` and then pushing the comparison for
`g ∘ f` forward along `h`. -/
theorem pushforwardModulesCompIso_assoc_app (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) (e : h.comp (g.comp f) = (h.comp g).comp f)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (eqToHom (congrArg (fun m : RingedToposHom X W => pushforwardModules m) e)).app M ≫
        (pushforwardModulesCompIso f (h.comp g)).hom.app M ≫
          (pushforwardModulesCompIso g h).hom.app ((pushforwardModules f).obj M) =
      (pushforwardModulesCompIso (g.comp f) h).hom.app M ≫
        (pushforwardModules h).map ((pushforwardModulesCompIso f g).hom.app M) := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  refine (cancel_mono ((pushforwardModulesUnderlyingIso h).hom.app
      ((pushforwardModules g).obj ((pushforwardModules f).obj M)) ≫
    h.toToposHom.pushforward.map ((pushforwardModulesUnderlyingIso g).hom.app
      ((pushforwardModules f).obj M)) ≫
    h.toToposHom.pushforward.map (g.toToposHom.pushforward.map
      ((pushforwardModulesUnderlyingIso f).hom.app M)))).mp ?_
  simp only [Functor.map_comp, Category.assoc]
  exact ((_ ≫= pushforwardModulesCompIso_assoc_underlying_mid f g h M).trans
      (pushforwardModulesUnderlyingIso_eqToHom_assoc f g h e M)).trans
    (pushforwardModulesCompIso_assoc_underlying_right f g h M).symm

/-- **The cocycle identity for the direct-image composition comparison.** The two ways of
identifying the direct image of a threefold composite of morphisms of ringed topoi with the
threefold composite of the direct images agree, up to the transport along the equality `e` of
the two bracketings of the composite. -/
theorem pushforwardModulesCompIso_assoc (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) (e : h.comp (g.comp f) = (h.comp g).comp f) :
    (pushforwardModulesCompIso (g.comp f) h).hom ≫
        Functor.whiskerRight (pushforwardModulesCompIso f g).hom (pushforwardModules h) =
      eqToHom (congrArg (fun m : RingedToposHom X W => pushforwardModules m) e) ≫
        (pushforwardModulesCompIso f (h.comp g)).hom ≫
          Functor.whiskerLeft (pushforwardModules f) (pushforwardModulesCompIso g h).hom ≫
            (Functor.associator _ _ _).inv := by
  apply NatTrans.ext
  funext M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Category.assoc] using
    (pushforwardModulesCompIso_assoc_app f g h e M).symm

/-- The direct-image cocycle with both transformations read out of the direct image of the
bracketing `(h ∘ g) ∘ f`, the other bracketing being reached by the transport along
`AlgebraicGeometry.RingedToposHom.comp_assoc`. -/
theorem pushforwardModulesCompIso_assoc_mate (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) :
    (pushforwardModulesCompIso f (h.comp g)).hom ≫
        Functor.whiskerLeft (pushforwardModules f) (pushforwardModulesCompIso g h).hom =
      (eqToHom (congrArg (fun m : RingedToposHom X W => pushforwardModules m)
            (comp_assoc f g h).symm) ≫
          (pushforwardModulesCompIso (g.comp f) h).hom) ≫
        Functor.whiskerRight (pushforwardModulesCompIso f g).hom (pushforwardModules h) ≫
          (Functor.associator _ _ _).hom := by
  rw [Category.assoc, reassoc_of% (pushforwardModulesCompIso_assoc f g h (comp_assoc f g h))]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-! ## The inverse-image cocycle -/

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The mate of the *inverse* of the inverse-image composition comparison is the direct-image
comparison. -/
theorem conjugateEquiv_pullbackModulesCompIso_inv (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) :
    conjugateEquiv (pullbackAdjPushforwardModules (g.comp f))
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))
        (pullbackModulesCompIso f g).inv =
      (pushforwardModulesCompIso f g).hom :=
  congrArg Iso.inv
    (Iso.ext (conjugateEquiv_pullbackModulesCompIso_hom f g) :
      conjugateIsoEquiv
          ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))
          (pullbackAdjPushforwardModules (g.comp f)) (pullbackModulesCompIso f g) =
        (pushforwardModulesCompIso f g).symm)

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The inverse of the inverse-image composition comparison is the transformation of left
adjoints induced by the direct-image comparison. -/
theorem pullbackModulesCompIso_inv_eq (f : RingedToposHom X Y) (g : RingedToposHom Y Z) :
    (pullbackModulesCompIso f g).inv =
      Adjunction.leftAdjointCompNatTrans (pullbackAdjPushforwardModules g)
        (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules (g.comp f))
        (pushforwardModulesCompIso f g).hom :=
  Eq.symm ((Equiv.symm_apply_eq _).2 (conjugateEquiv_pullbackModulesCompIso_inv f g).symm)

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The same, transported along an equality of the composite with a third morphism `t`. -/
theorem pullbackModulesCompIso_inv_transport (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (t : RingedToposHom X Z) (e : g.comp f = t) :
    (pullbackModulesCompIso f g).inv ≫
        eqToHom (congrArg
          (fun m : RingedToposHom X Z => m.toModulesHom.pullbackModules) e) =
      Adjunction.leftAdjointCompNatTrans (pullbackAdjPushforwardModules g)
        (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules t)
        (eqToHom (congrArg (fun m : RingedToposHom X Z => pushforwardModules m) e.symm) ≫
          (pushforwardModulesCompIso f g).hom) := by
  subst t
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
    pullbackModulesCompIso_inv_eq f g

/-- **The cocycle identity for the inverse-image composition comparison.** The two ways of
identifying the threefold composite of pullbacks of sheaves of modules with the pullback along a
threefold composite of morphisms of ringed topoi agree. -/
theorem pullbackModulesCompIso_assoc (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) :
    Functor.whiskerLeft h.toModulesHom.pullbackModules (pullbackModulesCompIso f g).inv ≫
        (pullbackModulesCompIso (g.comp f) h).inv ≫
          eqToHom (congrArg
            (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) (comp_assoc f g h)) =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackModulesCompIso g h).inv f.toModulesHom.pullbackModules ≫
          (pullbackModulesCompIso f (h.comp g)).inv := by
  rw [pullbackModulesCompIso_inv_eq f g, pullbackModulesCompIso_inv_eq g h,
    pullbackModulesCompIso_inv_eq f (h.comp g),
    pullbackModulesCompIso_inv_transport (g.comp f) h ((h.comp g).comp f) (comp_assoc f g h)]
  exact Adjunction.leftAdjointCompNatTrans_assoc (pullbackAdjPushforwardModules h)
    (pullbackAdjPushforwardModules g) (pullbackAdjPushforwardModules f)
    (pullbackAdjPushforwardModules (h.comp g)) (pullbackAdjPushforwardModules (g.comp f))
    (pullbackAdjPushforwardModules ((h.comp g).comp f)) _ _ _ _
    (pushforwardModulesCompIso_assoc_mate f g h)

/-- `pullbackModulesCompIso_assoc` with the two bracketings of the threefold composite each
compared with a third morphism `t` rather than with each other, so that no type mentions both. -/
theorem pullbackModulesCompIso_assoc_of_eq (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom Z W) (t : RingedToposHom X W) (e : h.comp (g.comp f) = t)
    (e' : (h.comp g).comp f = t) :
    Functor.whiskerLeft h.toModulesHom.pullbackModules (pullbackModulesCompIso f g).inv ≫
        (pullbackModulesCompIso (g.comp f) h).inv ≫
          eqToHom (congrArg
            (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e) =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackModulesCompIso g h).inv f.toModulesHom.pullbackModules ≫
          (pullbackModulesCompIso f (h.comp g)).inv ≫
            eqToHom (congrArg
              (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e') := by
  subst e'
  simpa only [eqToHom_refl, Category.comp_id] using pullbackModulesCompIso_assoc f g h

end Pullback

end AlgebraicGeometry.RingedToposHom

end
