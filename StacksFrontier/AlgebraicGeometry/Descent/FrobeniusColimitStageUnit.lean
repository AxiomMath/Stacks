module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageAdjunction

/-!
# The comparison of Stacks Tag 0EXB on Hom-sets is an adjunct

Let `p` be a prime and let `X` be a scheme in characteristic `p`. Write `φ` for the `p`-th power
endomorphism of `𝒪_X`, `ι_n : 𝒪_X ⟶ colim_F 𝒪_X` for the stage-`n` coprojection, `S_n` for
extension of scalars along `ι_n` and `U_n` for restriction of scalars along `ι_n`.

`AlgebraicGeometry.frobeniusStageHomMap`, the comparison of Tag 0EXB on Hom-sets, conjugates the
stage-`n + j` functor by `AlgebraicGeometry.frobeniusStageFunctorIterIso`. That isomorphism
compares two left adjoints of one and the same functor `U_n` —
`AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter` is the adjunction for one of them —
and is therefore determined by the two units. This file makes that explicit and reads the
comparison on Hom-sets off it: **under the adjunction `S_n ⊣ U_n` the comparison on Hom-sets is
the `j`-fold Frobenius unit at `ℰ` followed by the restriction of the morphism.**

## Main definitions

* `AlgebraicGeometry.frobeniusStageExtendScalarsAdjunction`: a name for the adjunction
  `S_n ⊣ U_n`, which is `SheafOfModules.pullbackPushforwardAdjunction` at the stage-`n`
  coprojection.
* `AlgebraicGeometry.frobeniusStageUnitIter`: **the `j`-fold Frobenius unit at a finite locally
  free module `ℰ`**, the morphism `ℰ ⟶ U_n (S_{n + j}(F^{j,*}ℰ))` assembled from the stage-`n`
  unit and `j` copies of the inverse of the cocone comparison
  `AlgebraicGeometry.frobeniusStageFunctorIso`.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_eq`: **a morphism between two left adjoints
  of one functor is the component of `CategoryTheory.Adjunction.leftAdjointUniq` as soon as it
  carries one unit to the other.** This is the uniqueness half of
  `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft_hom_app`: **transporting the left
  adjoint along an isomorphism conjugates `CategoryTheory.Adjunction.leftAdjointUniq` by that
  isomorphism.**
* `AlgebraicGeometry.leftAdjointUniq_frobeniusStageExtendScalarsAdjunctionIter_succ`: **the
  comparison of the `j + 1`-fold iterate with the stage-`n` extension of scalars is the one for
  `j` of them, preceded by the one-step cocone comparison.**
* `AlgebraicGeometry.frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso`: **the `j`-fold
  Frobenius unit, followed by the restriction of
  `AlgebraicGeometry.frobeniusStageFunctorIterIso`, is the stage-`n` unit.** This says that the
  comparison of the stage functors along `j` Frobenius pullbacks is the comparison of two left
  adjoints of `U_n`, read at an object.
* `AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter_unit_app`: **the `j`-fold
  Frobenius unit is the unit of the `j`-fold adjunction**, transported.
* `AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_hom_app`: **the comparison of the stage
  functors along `j` Frobenius pullbacks is `CategoryTheory.Adjunction.leftAdjointUniq` of the
  `j`-fold adjunction and the stage-`n` one.**
* `AlgebraicGeometry.unit_comp_frobeniusStageHomMap`: **the adjunct of the comparison of Tag 0EXB
  on Hom-sets is the `j`-fold Frobenius unit at `ℰ` followed by the restriction of the
  morphism.**
* `AlgebraicGeometry.ι_frobeniusPullbackIter_obj` and
  `AlgebraicGeometry.frobeniusPullbackStageIso_inv_app`: the two transports which relate the
  `Vect(X)`-level iterate of Frobenius pullback to the iterate of extension of scalars along
  `φ`, needed because `AlgebraicGeometry.pullback_absoluteFrobenius_eq` is an equality of
  functors and not a definitional one.

## Implementation notes

The induction which proves
`AlgebraicGeometry.frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso` is carried out on
`Vect(X)` and on the finite locally free modules over `colim_F 𝒪_X`, where the iterate of
Frobenius pullback is `AlgebraicGeometry.frobeniusPullbackIter` and no transport occurs: that is
why `AlgebraicGeometry.frobeniusStageUnitIter` is defined by its own recursion instead of being
taken to be the unit of `AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter`. The two
agree, but only after the transport
`AlgebraicGeometry.ι_frobeniusPullbackIter_obj`, since the iterate of
`AlgebraicGeometry.frobeniusExtendScalars` and the iterate of pullback along the absolute
Frobenius are equal and not definitionally equal.

`AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter` transports its left adjoint along
`CategoryTheory.Adjunction.ofNatIsoLeft`, so the comparison with the stage-`n` adjunction is
computed by `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft_hom_app`; the
`CategoryTheory.Adjunction.ofNatIsoRight` which
`AlgebraicGeometry.frobeniusExtendScalarsStageIso` carries never has to be unfolded, because the
cocone comparison appearing in the unit of the iterate cancels against the one appearing in the
comparison itself.

What is **not** here is the computation of `U_n (S_n 𝒢)` as the filtered colimit of the
`(U_φ)^j (S_φ)^j 𝒢`, which is the one remaining input to the full faithfulness half of Tag
0EXB; with that colimit in hand, the formula
`AlgebraicGeometry.unit_comp_frobeniusStageHomMap` identifies the map out of
`colim_j Hom_X(F^{j,*}ℰ, F^{j,*}𝒢)` which
`AlgebraicGeometry.bijective_frobeniusColimitVectComparison_map_equalStage` asks to be
bijective with the one `Hom_X(ℰ, -)` produces from that colimit. See the implementation notes
of `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles` for what the colimit
itself still needs.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v v₂ u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/-- **Cancelling a split idempotent inside the image of a functor.** If `a ≫ a' = 𝟙`, then the
image of `a` followed by the image of `a'` composed with anything is that anything. The form is
the one in which the cocone comparisons of Stacks Tag 0EXA cancel against the Frobenius units. -/
lemma Functor.comp_map_comp_map_cancel (U : C ⥤ D) {Z : D} {P Q R : C} (η : Z ⟶ U.obj P)
    (a : P ⟶ Q) (a' : Q ⟶ P) (b : P ⟶ R) (ha : a ≫ a' = 𝟙 P) :
    (η ≫ U.map a) ≫ U.map (a' ≫ b) = η ≫ U.map b := by
  rw [Category.assoc, ← Functor.map_comp, ← Category.assoc, ha, Category.id_comp]

/-- **An identity inside the image of a functor may be dropped.** -/
lemma Functor.comp_map_id_cancel (U : C ⥤ D) {Z : D} {P : C} (η : Z ⟶ U.obj P) :
    η ≫ U.map (𝟙 P) = η := by
  rw [Functor.map_id, Category.comp_id]

/-- **Two factorisations of one morphism give the same composite inside the image of a
functor.** -/
lemma Functor.comp_map_comp_map_congr (U : C ⥤ D) {Z : D} {P Q Q' R : C} (η : Z ⟶ U.obj P)
    {a : P ⟶ Q} {b : Q ⟶ R} {a' : P ⟶ Q'} {b' : Q' ⟶ R} (h : a ≫ b = a' ≫ b') :
    (η ≫ U.map a) ≫ U.map b = (η ≫ U.map a') ≫ U.map b' := by
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h]

/-- **A natural transformation commutes with a transport of objects.** -/
lemma NatTrans.app_comp_eqToHom {F G : C ⥤ D} (α : F ⟶ G) {A B : C} (h : A = B) :
    α.app A ≫ eqToHom (congrArg G.obj h) = eqToHom (congrArg F.obj h) ≫ α.app B := by
  subst h; simp

namespace Adjunction

/-- **A morphism between two left adjoints of one and the same functor is the component of
`CategoryTheory.Adjunction.leftAdjointUniq` as soon as it carries the one unit to the other.**
This is the uniqueness half of `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, and it
holds because the unit determines a morphism out of a left adjoint. -/
lemma leftAdjointUniq_hom_app_eq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) {u : F.obj x ⟶ F'.obj x}
    (h : adj1.unit.app x ≫ G.map u = adj2.unit.app x) :
    u = (leftAdjointUniq adj1 adj2).hom.app x := by
  refine (adj1.homEquiv x (F'.obj x)).injective ?_
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app adj1 adj2, Adjunction.homEquiv_unit]
  exact h

/-- **Transporting the left adjoint of an adjunction along an isomorphism conjugates
`CategoryTheory.Adjunction.leftAdjointUniq` by that isomorphism.** -/
lemma leftAdjointUniq_ofNatIsoLeft_hom_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) (i : F ≅ F'') (x : C) :
    (leftAdjointUniq (adj1.ofNatIsoLeft i) adj2).hom.app x =
      i.inv.app x ≫ (leftAdjointUniq adj1 adj2).hom.app x :=
  (leftAdjointUniq_hom_app_eq (adj1.ofNatIsoLeft i) adj2 x (by
    simp only [ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    exact unit_leftAdjointUniq_hom_app adj1 adj2 x)).symm

/-- `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_eq` for a morphism whose source has been
transported along an isomorphism. -/
lemma leftAdjointUniq_hom_app_eq_comp {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) {Z : D} (c : Z ≅ F.obj x) {u : Z ⟶ F'.obj x}
    (h : adj1.unit.app x ≫ G.map (c.inv ≫ u) = adj2.unit.app x) :
    u = c.hom ≫ (leftAdjointUniq adj1 adj2).hom.app x := by
  rw [← leftAdjointUniq_hom_app_eq adj1 adj2 x h, Iso.hom_inv_id_assoc]

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### The stage adjunctions -/

/-- **Extension of scalars along the stage-`n` coprojection is a left adjoint of restriction of
scalars along it.** This is `SheafOfModules.pullbackPushforwardAdjunction` at
`AlgebraicGeometry.frobeniusStageStructureMap`; only the name is shorter. -/
noncomputable abbrev frobeniusStageExtendScalarsAdjunction (n : ℕ) :
    frobeniusStageExtendScalars X p hX n ⊣
      _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n) :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (frobeniusStageStructureMap X p hX n)

/-- No Frobenius extension of scalars at all leaves the stage-`n` adjunction. -/
lemma frobeniusStageExtendScalarsAdjunctionIter_zero (n : ℕ) :
    frobeniusStageExtendScalarsAdjunctionIter X p hX n 0 =
      frobeniusStageExtendScalarsAdjunction X p hX n :=
  rfl

/-- One more Frobenius extension of scalars than `j` transports the `j`-fold adjunction along the
one-step cocone comparison. -/
lemma frobeniusStageExtendScalarsAdjunctionIter_succ (n j : ℕ) :
    frobeniusStageExtendScalarsAdjunctionIter X p hX n (j + 1) =
      Adjunction.ofNatIsoLeft (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
        (Functor.isoWhiskerLeft ((frobeniusExtendScalars X p hX).endoIter j)
          (frobeniusExtendScalarsStageIso X p hX (n + j))).symm :=
  rfl

/-- **The comparison of the `j + 1`-fold iterate of extension of scalars along Frobenius with
extension of scalars along the stage-`n` coprojection is the comparison for `j` of them,
preceded by the one-step cocone comparison.** -/
lemma leftAdjointUniq_frobeniusStageExtendScalarsAdjunctionIter_succ (n j : ℕ)
    (M : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n (j + 1))
          (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app M =
      (frobeniusExtendScalarsStageIso X p hX (n + j)).hom.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj M) ≫
        (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
          (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app M :=
  Adjunction.leftAdjointUniq_ofNatIsoLeft_hom_app _ _ _ M

/-! ### The two transports between the `Vect(X)`-level and the module-level iterates -/

/-- Pullback along the absolute Frobenius agrees on objects with extension of scalars along the
`p`-th power endomorphism. -/
private lemma pullback_absoluteFrobenius_obj_eq (A : X.Modules) :
    (Scheme.Modules.pullback (absoluteFrobenius X p hX)).obj A =
      (frobeniusExtendScalars X p hX).obj A :=
  congrArg (fun T : X.Modules ⥤ X.Modules ↦ T.obj A) (pullback_absoluteFrobenius_eq X p hX)

/-- **The `j`-fold Frobenius pullback of a finite locally free module is the `j`-fold extension
of scalars along the `p`-th power endomorphism of its underlying module.** The two are equal and
not definitionally equal, since `AlgebraicGeometry.pullback_absoluteFrobenius_eq` is. -/
lemma ι_frobeniusPullbackIter_obj (j : ℕ) (E : X.Vect) :
    (ObjectProperty.ι _).obj ((frobeniusPullbackIter X p hX j).obj E) =
      ((frobeniusExtendScalars X p hX).endoIter j).obj ((ObjectProperty.ι _).obj E) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      refine Eq.trans ?_ (congrArg (frobeniusExtendScalars X p hX).obj ih)
      exact pullback_absoluteFrobenius_obj_eq X p hX _

/-- **The inverse cocone comparison in the form the diagram of Tag 0EXA asks for is the one on
all sheaves of modules, followed by the transport along
`AlgebraicGeometry.pullback_absoluteFrobenius_eq`.** The transport is taken as a hypothesis
because any two proofs of it give the same `eqToHom`. -/
lemma frobeniusPullbackStageIso_inv_app (m : ℕ) (A : X.Modules)
    (e : (frobeniusStageExtendScalars X p hX (m + 1)).obj
        ((frobeniusExtendScalars X p hX).obj A) =
      (frobeniusStageExtendScalars X p hX (m + 1)).obj
        ((Scheme.Modules.pullback (absoluteFrobenius X p hX)).obj A)) :
    (frobeniusPullbackStageIso X p hX m).inv.app A =
      (frobeniusExtendScalarsStageIso X p hX m).inv.app A ≫ eqToHom e :=
  congrArg (fun t ↦ (frobeniusExtendScalarsStageIso X p hX m).inv.app A ≫ t)
    (eqToHom_app (congrArg (fun G ↦ G ⋙ frobeniusStageExtendScalars X p hX (m + 1))
      (pullback_absoluteFrobenius_eq X p hX)).symm A)

/-! ### The `j`-fold Frobenius unit -/

/-- The comparison of the stage functors along `j + 1` Frobenius pullbacks is the comparison
along `j` of them, preceded by the one-step comparison. -/
lemma frobeniusStageFunctorIterIso_hom_app_succ (n j : ℕ) (E : X.Vect) :
    (frobeniusStageFunctorIterIso X p hX n (j + 1)).hom.app E =
      (frobeniusStageFunctorIso X p hX (n + j)).hom.app
          ((frobeniusPullbackIter X p hX j).obj E) ≫
        (frobeniusStageFunctorIterIso X p hX n j).hom.app E :=
  Category.id_comp _

/-- **The `j`-fold Frobenius unit at a finite locally free module `ℰ`**: the morphism
`ℰ ⟶ U_n (S_{n + j}(F^{j,*}ℰ))` of `𝒪_X`-modules obtained from the unit of the stage-`n`
adjunction by inserting, `j` times, the inverse of the cocone comparison
`AlgebraicGeometry.frobeniusStageFunctorIso`. Informally it is the `j`-fold Frobenius unit
`ℰ ⟶ F^{j}_*F^{j,*}ℰ` followed by the stage-`n + j` unit; see
`AlgebraicGeometry.frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso` for the
characterisation which makes that precise. -/
noncomputable def frobeniusStageUnitIter (n : ℕ) (E : X.Vect) : ∀ j : ℕ,
    (E.obj : _root_.SheafOfModules.{u} X.ringSheafOnOpens) ⟶
      (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).obj
        ((frobeniusStageFunctor X p hX (n + j)).obj
          ((frobeniusPullbackIter X p hX j).obj E)).obj
  | 0 => (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E.obj
  | j + 1 =>
      frobeniusStageUnitIter n E j ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          ((frobeniusStageFunctorIso X p hX (n + j)).inv.app
            ((frobeniusPullbackIter X p hX j).obj E)).hom

/-- No Frobenius unit at all is the unit of the stage-`n` adjunction. -/
lemma frobeniusStageUnitIter_zero (n : ℕ) (E : X.Vect) :
    frobeniusStageUnitIter X p hX n E 0 =
      (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E.obj :=
  rfl

/-- One more Frobenius unit than `j` inserts one more inverse cocone comparison. -/
lemma frobeniusStageUnitIter_succ (n : ℕ) (E : X.Vect) (j : ℕ) :
    frobeniusStageUnitIter X p hX n E (j + 1) =
      frobeniusStageUnitIter X p hX n E j ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          ((frobeniusStageFunctorIso X p hX (n + j)).inv.app
            ((frobeniusPullbackIter X p hX j).obj E)).hom :=
  rfl

/-- **The `j`-fold Frobenius unit, followed by the restriction of scalars of the comparison of
the stage functors along `j` Frobenius pullbacks, is the unit of the stage-`n` adjunction.**
Equivalently: `AlgebraicGeometry.frobeniusStageFunctorIterIso` is the comparison of two left
adjoints of one and the same restriction of scalars, read at an object. -/
theorem frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso (n : ℕ) (E : X.Vect) (j : ℕ) :
    frobeniusStageUnitIter X p hX n E j ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          ((frobeniusStageFunctorIterIso X p hX n j).hom.app E).hom =
      (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E.obj := by
  induction j with
  | zero => exact Functor.comp_map_id_cancel _ _
  | succ j ih =>
      refine Eq.trans ?_ ih
      rw [frobeniusStageUnitIter_succ, frobeniusStageFunctorIterIso_hom_app_succ]
      exact Functor.comp_map_comp_map_cancel _ _ _ _ _ (ObjectProperty.isoInv_hom_id_hom
        ((frobeniusStageFunctorIso X p hX (n + j)).app ((frobeniusPullbackIter X p hX j).obj E)))

/-! ### The `j`-fold Frobenius unit is the unit of the `j`-fold adjunction -/

/-- The unit of the `j + 1`-fold adjunction is the unit of the `j`-fold one, followed by the
restriction of scalars of the inverse one-step cocone comparison. -/
lemma frobeniusStageExtendScalarsAdjunctionIter_unit_app_succ (n j : ℕ)
    (M : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (frobeniusStageExtendScalarsAdjunctionIter X p hX n (j + 1)).unit.app M =
      (frobeniusStageExtendScalarsAdjunctionIter X p hX n j).unit.app M ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          ((frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app
            (((frobeniusExtendScalars X p hX).endoIter j).obj M)) :=
  rfl

/-- **The inverse one-step cocone comparison of Tag 0EXA, read through `ObjectProperty.ι`, is
the one on all sheaves of modules conjugated by the transport
`AlgebraicGeometry.ι_frobeniusPullbackIter_obj`.** -/
lemma frobeniusStageFunctorIso_inv_app_hom_comp_eqToHom (n j : ℕ) (E : X.Vect) :
    eqToHom (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
          (ι_frobeniusPullbackIter_obj X p hX j E)) ≫
        (frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj ((ObjectProperty.ι _).obj E)) =
      ((frobeniusStageFunctorIso X p hX (n + j)).inv.app
            ((frobeniusPullbackIter X p hX j).obj E)).hom ≫
        eqToHom (congrArg (frobeniusStageExtendScalars X p hX (n + j + 1)).obj
          (ι_frobeniusPullbackIter_obj X p hX (j + 1) E)) := by
  have e : (frobeniusStageExtendScalars X p hX (n + j + 1)).obj
        ((frobeniusExtendScalars X p hX).obj
          ((ObjectProperty.ι _).obj ((frobeniusPullbackIter X p hX j).obj E))) =
      (frobeniusStageExtendScalars X p hX (n + j + 1)).obj
        ((Scheme.Modules.pullback (absoluteFrobenius X p hX)).obj
          ((ObjectProperty.ι _).obj ((frobeniusPullbackIter X p hX j).obj E))) :=
    congrArg _ (pullback_absoluteFrobenius_obj_eq X p hX _).symm
  have h1 : ((frobeniusStageFunctorIso X p hX (n + j)).inv.app
        ((frobeniusPullbackIter X p hX j).obj E)).hom =
      (frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app
          ((ObjectProperty.ι _).obj ((frobeniusPullbackIter X p hX j).obj E)) ≫ eqToHom e :=
    frobeniusPullbackStageIso_inv_app X p hX (n + j) _ e
  rw [h1]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun t ↦ (frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app
      ((ObjectProperty.ι _).obj ((frobeniusPullbackIter X p hX j).obj E)) ≫ t)
    (eqToHom_trans e _)).symm
  exact (NatTrans.app_comp_eqToHom (frobeniusExtendScalarsStageIso X p hX (n + j)).inv
    (ι_frobeniusPullbackIter_obj X p hX j E)).symm

/-- **The `j`-fold Frobenius unit is the unit of the `j`-fold adjunction**, transported along
`AlgebraicGeometry.ι_frobeniusPullbackIter_obj`. This is what identifies
`AlgebraicGeometry.frobeniusStageUnitIter` as an honest adjunction unit, and so as the `j`-fold
Frobenius unit followed by the stage-`n + j` unit. -/
theorem frobeniusStageExtendScalarsAdjunctionIter_unit_app (n : ℕ) (E : X.Vect) (j : ℕ) :
    (frobeniusStageExtendScalarsAdjunctionIter X p hX n j).unit.app E.obj =
      frobeniusStageUnitIter X p hX n E j ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          (eqToHom (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
            (ι_frobeniusPullbackIter_obj X p hX j E))) := by
  induction j with
  | zero =>
      exact (Functor.comp_map_id_cancel
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)) _).symm
  | succ j ih =>
      rw [frobeniusStageExtendScalarsAdjunctionIter_unit_app_succ X p hX n j E.obj, ih,
        frobeniusStageUnitIter_succ]
      exact Functor.comp_map_comp_map_congr _ _
        (frobeniusStageFunctorIso_inv_app_hom_comp_eqToHom X p hX n j E)

/-- **The comparison of the stage functors along `j` Frobenius pullbacks, read through
`ObjectProperty.ι`, is `CategoryTheory.Adjunction.leftAdjointUniq` of the `j`-fold adjunction and
the stage-`n` one** — the two being adjunctions with one and the same right adjoint `U_n`. The
transport `AlgebraicGeometry.ι_frobeniusPullbackIter_obj` enters because the `Vect(X)`-level
iterate of Frobenius pullback and the iterate of extension of scalars along `φ` are equal and not
definitionally equal. -/
theorem ι_map_frobeniusStageFunctorIterIso_hom_app (n j : ℕ) (E : X.Vect) :
    ((frobeniusStageFunctorIterIso X p hX n j).hom.app E).hom =
      eqToHom (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
          (ι_frobeniusPullbackIter_obj X p hX j E)) ≫
        (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
          (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app E.obj :=
  Adjunction.leftAdjointUniq_hom_app_eq_comp
    (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
    (frobeniusStageExtendScalarsAdjunction X p hX n) E.obj
    (eqToIso (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
      (ι_frobeniusPullbackIter_obj X p hX j E))) (by
    rw [frobeniusStageExtendScalarsAdjunctionIter_unit_app X p hX n E j]
    refine Eq.trans ?_ (frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso X p hX n E j)
    exact Functor.comp_map_comp_map_cancel
      (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)) _ _ _ _
      (Iso.hom_inv_id (eqToIso (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
        (ι_frobeniusPullbackIter_obj X p hX j E)))))

/-! ### The comparison of Tag 0EXB on Hom-sets, as an adjunct -/

/-- **The adjunct of the comparison of Tag 0EXB on Hom-sets is the `j`-fold Frobenius unit at
`ℰ`, followed by the restriction of scalars of the morphism and of the comparison of the stage
functors at `𝒢`.** The two conjugating isomorphisms of
`AlgebraicGeometry.frobeniusStageHomMap` have become the `j`-fold Frobenius unit at the source
and the comparison at the target. -/
theorem unit_comp_frobeniusStageHomMap (n j : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX j).obj E ⟶ (frobeniusPullbackIter X p hX j).obj G) :
    (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E.obj ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          (frobeniusStageHomMap X p hX n j f).hom =
      frobeniusStageUnitIter X p hX n E j ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).map
          (((frobeniusStageFunctor X p hX (n + j)).map f).hom ≫
            ((frobeniusStageFunctorIterIso X p hX n j).hom.app G).hom) := by
  rw [← frobeniusStageUnitIter_comp_frobeniusStageFunctorIterIso X p hX n E j]
  simp only [frobeniusStageHomMap, ObjectProperty.FullSubcategory.comp_hom]
  exact Functor.comp_map_comp_map_cancel _ _ _ _ _ (ObjectProperty.isoHom_inv_id_hom
    ((frobeniusStageFunctorIterIso X p hX n j).app E))

end AlgebraicGeometry

end
