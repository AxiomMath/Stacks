module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictDiagram

/-!
# The Hom-sets of the diagram of Stacks Tag 0EXB

Let `p` be a prime and let `X` be a scheme in characteristic `p`. Write `φ` for the `p`-th power
endomorphism of `𝒪_X`, `S_φ` and `U_φ` for extension and restriction of scalars along it, and
`S_n`, `U_n` for extension and restriction of scalars along the stage-`n` coprojection
`𝒪_X ⟶ colim_F 𝒪_X`. The diagram of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictDiagram` is
`j ↦ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`, and the full faithfulness half of Tag 0EXB asks for its colimit
to be `U_n (S_n 𝒢)`. What one then wants to do with that colimit is to apply
`Hom_{𝒪_X}(ℰ, -)`, which commutes with filtered colimits for `ℰ` finite locally free on a
quasi-compact quasi-separated scheme. This file identifies the Hom-sets which the terms of the
diagram contribute: **`Hom_{𝒪_X}(ℰ, (U_φ)^{∘j}((S_φ)^{∘j}𝒢))` is
`Hom_{𝒪_X}((S_φ)^{∘j}ℰ, (S_φ)^{∘j}𝒢)`**, which is the Hom-set of `Vect(X)` between the `j`-fold
Frobenius pullbacks that Tag 0EXB takes the colimit of.

The identification is an adjunction: **the `j`-fold iterate of a left adjoint is a left adjoint
of the `j`-fold iterate of the right adjoint.** This is not quite formal, because
`CategoryTheory.Functor.endoIter` recurses by composing on the right while
`CategoryTheory.Adjunction.comp` produces the composite of the right adjoints in the other
order; the two agree, but as an equality of functors which has to be proved and then transported
along.

## Main definitions

* `CategoryTheory.Adjunction.endoIter`: **the `j`-fold iterate of a left adjoint is a left
  adjoint of the `j`-fold iterate of its right adjoint.**
* `AlgebraicGeometry.frobeniusExtendScalarsAdjunctionIter`: that adjunction at the Frobenius
  adjunction, `(S_φ)^{∘j} ⊣ (U_φ)^{∘j}`.
* `AlgebraicGeometry.frobeniusStageRestrictGeneralLeg`: the leg of the cocone of Tag 0EXB with an
  arbitrary morphism out of the stage-`n + j` extension of scalars in place of the comparison of
  left adjoints. The generality is what the induction on `j` needs.
* `AlgebraicGeometry.frobeniusStageModuleHomMap`: **the comparison of Tag 0EXB on Hom-sets, at
  the level of all `𝒪_X`-modules** — `AlgebraicGeometry.frobeniusStageHomMap` with `Vect(X)`
  replaced by `𝒪_X`-modules and the comparison of the stage functors by
  `CategoryTheory.Adjunction.leftAdjointUniq`.

## Main results

* `CategoryTheory.Functor.endoIter_comp_self`: the iterates of an endofunctor commute with it,
  `F^j ⋙ F = F ⋙ F^j`. This is the transport the iterated adjunction is built on.
* `CategoryTheory.Adjunction.endoIter_unit_app_succ`: **the unit of the `j + 1`-fold iterated
  adjunction is the unit of the `j`-fold one followed by the transition morphism of the diagram
  of Tag 0EXB.**
* `AlgebraicGeometry.homEquiv_frobeniusRestrictExtendIter`: **a morphism
  `ℰ ⟶ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)` is the same thing as a morphism
  `(S_φ)^{∘j}ℰ ⟶ (S_φ)^{∘j}𝒢`**, that is, as a morphism of the `j`-fold Frobenius pullbacks.
* `AlgebraicGeometry.unit_comp_frobeniusStageRestrictLeg`: **the leg of the cocone, precomposed
  with the `j`-fold Frobenius unit, is the unit of the stage-`n` adjunction.**
* `AlgebraicGeometry.homEquiv_comp_frobeniusStageRestrictLeg`: **the leg of the cocone computes
  the comparison of Tag 0EXB on Hom-sets.** A morphism of the `j`-fold extensions of scalars,
  read by the `j`-fold adjunction as a morphism into the `j`-th term of the diagram and then
  followed by the leg, is the adjunct of `AlgebraicGeometry.frobeniusStageModuleHomMap` at it.
  This is the compatibility which turns the colimit of the diagram, once it is known, into the
  bijectivity of the comparison on Hom-sets.

## Implementation notes

The adjunction is built by recursion on `j`, the zeroth iterate being
`CategoryTheory.Adjunction.id` — which is literally an adjunction between the two iterates,
since `CategoryTheory.Functor.endoIter` takes `0` to the identity functor on the nose.

`AlgebraicGeometry.frobeniusExtendScalarsAdjunctionIter` is **not**
`AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter`: the latter is the adjunction
`(S_φ)^{∘j} ⋙ S_{n + j} ⊣ U_n`, between the whole composite reaching the colimit and restriction
of scalars along the stage-`n` coprojection, and it is the one which identifies the comparison of
the stage functors. The one here never leaves `𝒪_X`-modules, and is what turns a Hom-set of the
diagram into a Hom-set of `Vect(X)`. The two are related by
`AlgebraicGeometry.unit_comp_frobeniusStageRestrictGeneralLeg`, which says that the leg of the
cocone carries the unit of the first to the unit of the second; that is the induction this file
is organised around, and its one step is
`AlgebraicGeometry.unit_comp_map_frobeniusExtendScalarsStageIso_hom_app`, the same lemma the
cocone compatibility is proved from.

What is **not** here is the colimit itself: that
`AlgebraicGeometry.frobeniusStageRestrictCocone` is colimiting is the one remaining input to the
full faithfulness half of Tag 0EXB, and it is unproved. Nor is the comparison of
`AlgebraicGeometry.frobeniusStageModuleHomMap` with `AlgebraicGeometry.frobeniusStageHomMap`,
which is the transport of `AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_hom_app` from
`Vect(X)` to all `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v v₂ u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **The iterates of an endofunctor commute with it**: `F^j ⋙ F = F ⋙ F^j`. The two sides are
not definitionally equal, since `CategoryTheory.Functor.endoIter` recurses by composing on the
right only. -/
lemma Functor.endoIter_comp_self (F : C ⥤ C) : ∀ j : ℕ,
    F.endoIter j ⋙ F = F ⋙ F.endoIter j
  | 0 => (Functor.id_comp F).trans (Functor.comp_id F).symm
  | j + 1 => by
      simp only [Functor.endoIter_succ]
      rw [← Functor.assoc, Functor.endoIter_comp_self F j]

/-- **The `j`-fold iterate of a left adjoint is a left adjoint of the `j`-fold iterate of the
right adjoint.** The transport along `CategoryTheory.Functor.endoIter_comp_self` is needed
because `CategoryTheory.Adjunction.comp` composes the right adjoints in the order opposite to the
one `CategoryTheory.Functor.endoIter` recurses in. -/
def Adjunction.endoIter {L R : C ⥤ C} (adj : L ⊣ R) : ∀ j : ℕ,
    L.endoIter j ⊣ R.endoIter j
  | 0 => Adjunction.id
  | j + 1 =>
      ((adj.endoIter j).comp adj).ofNatIsoRight (eqToIso (R.endoIter_comp_self j).symm)

/-- No iterate at all is the identity adjunction. -/
lemma Adjunction.endoIter_zero {L R : C ⥤ C} (adj : L ⊣ R) :
    adj.endoIter 0 = Adjunction.id :=
  rfl

/-- One more iterate than `j` composes the `j`-fold iterate with the adjunction itself,
transported along `CategoryTheory.Functor.endoIter_comp_self`. -/
lemma Adjunction.endoIter_succ {L R : C ⥤ C} (adj : L ⊣ R) (j : ℕ) :
    adj.endoIter (j + 1) =
      ((adj.endoIter j).comp adj).ofNatIsoRight (eqToIso (R.endoIter_comp_self j).symm) :=
  rfl

/-- **The unit of the `j + 1`-fold iterated adjunction is the unit of the `j`-fold one followed
by the `j`-fold iterate of the right adjoint applied to the unit**, transported along the
comparison `R^j (R Y) = R^{j + 1}Y`. The transported morphism is the transition morphism of the
diagram of Stacks Tag 0EXB. -/
lemma Adjunction.endoIter_unit_app_succ {L R : C ⥤ C} (adj : L ⊣ R) (j : ℕ) (E : C) :
    (adj.endoIter (j + 1)).unit.app E =
      (adj.endoIter j).unit.app E ≫
        ((R.endoIter j).map (adj.unit.app ((L.endoIter j).obj E)) ≫
          eqToHom (R.endoIter_obj_obj j ((L.endoIter (j + 1)).obj E))) := by
  rw [Adjunction.endoIter_succ, Adjunction.ofNatIsoRight_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app,
    Adjunction.comp_unit_app, Category.assoc]
  rfl

/-- **A morphism absorbed into the image of a functor, past a transport.** If `f ≫ a = b`, then
the image of `f` followed by the image of `a` and a transport is the image of `b` and that
transport. -/
lemma Functor.map_comp_map_comp_eqToHom {D : Type u₂} [Category.{v₂} D] (U : C ⥤ D)
    {P Q R : C} {S : D} (f : P ⟶ Q) (a : Q ⟶ R) (b : P ⟶ R) (h : f ≫ a = b) (e : U.obj R = S) :
    U.map f ≫ (U.map a ≫ eqToHom e) = U.map b ≫ eqToHom e := by
  rw [← Category.assoc, ← Functor.map_comp, h]

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **Extending scalars `j` times along the `p`-th power endomorphism of the structure sheaf is
a left adjoint of restricting them `j` times along it.** This is
`CategoryTheory.Adjunction.endoIter` at
`AlgebraicGeometry.frobeniusExtendScalarsAdjunction`, and the object it is an adjunction into is
`AlgebraicGeometry.frobeniusRestrictExtendIter`, the term of the diagram of Tag 0EXB. -/
noncomputable def frobeniusExtendScalarsAdjunctionIter (j : ℕ) :
    (frobeniusExtendScalars X p hX).endoIter j ⊣
      (frobeniusRestrictScalars X p hX).endoIter j :=
  (frobeniusExtendScalarsAdjunction X p hX).endoIter j

/-- **A morphism `ℰ ⟶ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)` into the `j`-th term of the diagram of Stacks
Tag 0EXB is the same thing as a morphism `(S_φ)^{∘j}ℰ ⟶ (S_φ)^{∘j}𝒢` of the `j`-fold Frobenius
pullbacks**, which is the Hom-set of `Vect(X)` whose colimit over `j` Tag 0EXB is about. -/
noncomputable def homEquiv_frobeniusRestrictExtendIter (j : ℕ)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
        ((frobeniusExtendScalars X p hX).endoIter j).obj G) ≃
      (E ⟶ frobeniusRestrictExtendIter X p hX j G) :=
  (frobeniusExtendScalarsAdjunctionIter X p hX j).homEquiv E _

/-- **The transition morphism of the diagram of Stacks Tag 0EXB is what the `j + 1`-fold
Frobenius unit adds to the `j`-fold one.** -/
lemma frobeniusExtendScalarsAdjunctionIter_unit_app_succ (j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (frobeniusExtendScalarsAdjunctionIter X p hX (j + 1)).unit.app G =
      (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
        frobeniusRestrictExtendIterMap X p hX j G :=
  Adjunction.endoIter_unit_app_succ (frobeniusExtendScalarsAdjunction X p hX) j G

/-! ### The legs, and the Frobenius unit -/

/-- **The leg of the cocone of Stacks Tag 0EXB with an arbitrary morphism out of the stage-`n + j`
extension of scalars** in place of the comparison of left adjoints which
`AlgebraicGeometry.frobeniusStageRestrictLeg` uses. The generality is what the induction on `j`
needs: one step of it replaces the comparison by the comparison preceded by the one-step cocone
comparison, which is not of the same form. -/
noncomputable def frobeniusStageRestrictGeneralLeg (n j : ℕ)
    (Z : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    {A : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (t : (frobeniusStageExtendScalars X p hX (n + j)).obj
        (((frobeniusExtendScalars X p hX).endoIter j).obj Z) ⟶ A) :
    frobeniusRestrictExtendIter X p hX j Z ⟶
      (frobeniusStageRestrictScalars X p hX n).obj A :=
  ((frobeniusRestrictScalars X p hX).endoIter j).map
      ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj Z) ≫
        (frobeniusStageRestrictScalars X p hX (n + j)).map t) ≫
    eqToHom (Functor.congr_obj (pushforward_frobeniusStage_comp_iter X p hX n j) A)

/-- The leg of the cocone of Stacks Tag 0EXB is the general leg at the comparison of the `j`-fold
left adjoint of `U_n` with the stage-`n` one. -/
lemma frobeniusStageRestrictLeg_eq (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    frobeniusStageRestrictLeg X p hX n j G =
      frobeniusStageRestrictGeneralLeg X p hX n j G
        ((Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
          (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app G) :=
  rfl

/-- **The general leg absorbs a morphism of the `j`-fold extensions of scalars**: the `j`-fold
restriction of scalars of such a morphism, followed by the general leg, is the general leg at the
stage-`n + j` extension of scalars of it. This is the naturality of the stage-`n + j` unit. -/
lemma map_comp_frobeniusStageRestrictGeneralLeg (n j : ℕ)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    {A : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G)
    (t : (frobeniusStageExtendScalars X p hX (n + j)).obj
        (((frobeniusExtendScalars X p hX).endoIter j).obj G) ⟶ A) :
    ((frobeniusRestrictScalars X p hX).endoIter j).map f ≫
        frobeniusStageRestrictGeneralLeg X p hX n j G t =
      frobeniusStageRestrictGeneralLeg X p hX n j E
        ((frobeniusStageExtendScalars X p hX (n + j)).map f ≫ t) := by
  have hinner : f ≫
        ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
            (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
          (frobeniusStageRestrictScalars X p hX (n + j)).map t) =
      (frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj E) ≫
        (frobeniusStageRestrictScalars X p hX (n + j)).map
          ((frobeniusStageExtendScalars X p hX (n + j)).map f ≫ t) := by
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q ↦ q ≫ (frobeniusStageRestrictScalars X p hX (n + j)).map t)
      ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.naturality f)
  exact Functor.map_comp_map_comp_eqToHom ((frobeniusRestrictScalars X p hX).endoIter j) f _ _
    hinner _

/-- **The general leg of Stacks Tag 0EXB, precomposed with the `j`-fold Frobenius unit, is the
unit of the `j`-fold stage adjunction followed by the restriction of scalars of the morphism.**

The induction on `j` is the one the file's generality exists for: one step of it uses
`AlgebraicGeometry.unit_comp_map_frobeniusExtendScalarsStageIso_hom_app` to peel the one-step
cocone comparison off the morphism, and
`AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter_unit_app_succ` to put it back on the
unit of the `j + 1`-fold stage adjunction. -/
theorem unit_comp_frobeniusStageRestrictGeneralLeg (n j : ℕ)
    (Z : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    {A : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (t : (frobeniusStageExtendScalars X p hX (n + j)).obj
        (((frobeniusExtendScalars X p hX).endoIter j).obj Z) ⟶ A) :
    (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app Z ≫
        frobeniusStageRestrictGeneralLeg X p hX n j Z t =
      (frobeniusStageExtendScalarsAdjunctionIter X p hX n j).unit.app Z ≫
        (frobeniusStageRestrictScalars X p hX n).map t := by
  induction j generalizing Z A with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _)
  | succ j ih =>
      obtain ⟨s, rfl⟩ : ∃ s, t =
          (frobeniusExtendScalarsStageIso X p hX (n + j)).hom.app
            (((frobeniusExtendScalars X p hX).endoIter j).obj Z) ≫ s :=
        ⟨(frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app _ ≫ t,
          ((Category.id_comp t).symm.trans (congrArg (fun q ↦ q ≫ t)
              (Iso.hom_inv_id_app (frobeniusExtendScalarsStageIso X p hX (n + j))
                (((frobeniusExtendScalars X p hX).endoIter j).obj Z)).symm)).trans
            (Category.assoc _ _ t)⟩
      have hleg : frobeniusRestrictExtendIterMap X p hX j Z ≫
            frobeniusStageRestrictGeneralLeg X p hX n (j + 1) Z
              ((frobeniusExtendScalarsStageIso X p hX (n + j)).hom.app
                (((frobeniusExtendScalars X p hX).endoIter j).obj Z) ≫ s) =
          frobeniusStageRestrictGeneralLeg X p hX n j Z s :=
        Functor.endoIter_map_comp_eqToHom_comp (frobeniusRestrictScalars X p hX) j _ _ _ _
          (unit_comp_map_frobeniusExtendScalarsStageIso_hom_app X p hX (n + j) _ _ s) _ _
      rw [frobeniusExtendScalarsAdjunctionIter_unit_app_succ]
      refine Eq.trans ((Category.assoc _ _ _).trans
        (congrArg (fun q ↦ (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app Z ≫ q)
          hleg)) ?_
      refine (ih Z s).trans ?_
      exact (Functor.comp_map_comp_map_cancel
        (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n))
        ((frobeniusStageExtendScalarsAdjunctionIter X p hX n j).unit.app Z)
        ((frobeniusExtendScalarsStageIso X p hX (n + j)).inv.app _)
        ((frobeniusExtendScalarsStageIso X p hX (n + j)).hom.app _) s
        (Iso.inv_hom_id_app _ _)).symm

/-- **The leg of the cocone of Stacks Tag 0EXB, precomposed with the `j`-fold Frobenius unit, is
the unit of the stage-`n` adjunction.** This is the statement that the cocone is the one the
adjunction `S_n ⊣ U_n` produces, and it is what makes the Hom-sets of the diagram the Hom-sets
of `Vect(X)` that Tag 0EXB takes the colimit of. -/
theorem unit_comp_frobeniusStageRestrictLeg (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
        frobeniusStageRestrictLeg X p hX n j G =
      (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app G :=
  (unit_comp_frobeniusStageRestrictGeneralLeg X p hX n j G _).trans
    (Adjunction.unit_leftAdjointUniq_hom_app
      (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
      (frobeniusStageExtendScalarsAdjunction X p hX n) G)

/-! ### The comparison on Hom-sets through the diagram -/

/-- **The comparison of Stacks Tag 0EXB on Hom-sets, at the level of `𝒪_X`-modules**: a morphism
of the `j`-fold extensions of scalars along Frobenius gives a morphism of the stage-`n`
extensions of scalars, by conjugating the stage-`n + j` extension of scalars of it with the
comparison of the `j`-fold left adjoint of `U_n` with the stage-`n` one. This is
`AlgebraicGeometry.frobeniusStageHomMap` with `Vect(X)` replaced by all `𝒪_X`-modules and
`AlgebraicGeometry.frobeniusStageFunctorIterIso` by
`CategoryTheory.Adjunction.leftAdjointUniq`. -/
noncomputable def frobeniusStageModuleHomMap (n j : ℕ)
    {E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens}
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G) :
    (frobeniusStageExtendScalars X p hX n).obj E ⟶
      (frobeniusStageExtendScalars X p hX n).obj G :=
  (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
        (frobeniusStageExtendScalarsAdjunction X p hX n)).inv.app E ≫
    (frobeniusStageExtendScalars X p hX (n + j)).map f ≫
      (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
        (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app G

/-- **The leg of the cocone of Stacks Tag 0EXB computes the comparison on Hom-sets.** A morphism
`f` of the `j`-fold extensions of scalars along Frobenius, read by the `j`-fold adjunction as a
morphism into the `j`-th term of the diagram and then followed by the leg, is the adjunct of
`AlgebraicGeometry.frobeniusStageModuleHomMap` at `f` under the stage-`n` adjunction.

This is the compatibility which turns the colimit of the diagram, once it is known, into the
bijectivity of the comparison of Tag 0EXB on Hom-sets: the map out of
`colim_j Hom_{𝒪_X}((S_φ)^{∘j}ℰ, (S_φ)^{∘j}𝒢)` which the colimit produces is the comparison. -/
theorem homEquiv_comp_frobeniusStageRestrictLeg (n j : ℕ)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G) :
    homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫
        frobeniusStageRestrictLeg X p hX n j G =
      (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E ≫
        (frobeniusStageRestrictScalars X p hX n).map
          (frobeniusStageModuleHomMap X p hX n j f) := by
  have hadj : homEquiv_frobeniusRestrictExtendIter X p hX j E G f =
      (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app E ≫
        ((frobeniusRestrictScalars X p hX).endoIter j).map f :=
    Adjunction.homEquiv_unit _ _ _ _
  set e := Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
    (frobeniusStageExtendScalarsAdjunction X p hX n)
  rw [hadj, ← Adjunction.unit_leftAdjointUniq_hom_app
    (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
    (frobeniusStageExtendScalarsAdjunction X p hX n) E]
  refine Eq.trans ?_ (Functor.comp_map_comp_map_cancel
    (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n))
    ((frobeniusStageExtendScalarsAdjunctionIter X p hX n j).unit.app E) (e.hom.app E)
    (e.inv.app E)
    ((frobeniusStageExtendScalars X p hX (n + j)).map f ≫ e.hom.app G)
    (Iso.hom_inv_id_app _ E)).symm
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg _
    (map_comp_frobeniusStageRestrictGeneralLeg X p hX n j E G f (e.hom.app G))).trans
    (unit_comp_frobeniusStageRestrictGeneralLeg X p hX n j E _)

end AlgebraicGeometry

end
