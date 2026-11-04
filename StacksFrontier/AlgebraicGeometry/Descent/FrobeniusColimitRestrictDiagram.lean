module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageShift
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagram whose colimit computes the restriction of an extension of scalars along Frobenius

Let `p` be a prime and let `X` be a scheme in characteristic `p`. Write `φ` for the `p`-th power
endomorphism of `𝒪_X`, `ι_n : 𝒪_X ⟶ colim_F 𝒪_X` for the stage-`n` coprojection, `S_α` for
extension and `U_α` for restriction of scalars along a morphism `α` of sheaves of rings. The one
remaining input to the full faithfulness half of Stacks Tag 0EXB is the identification

`U_n (S_n 𝒢) ≅ colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`

for an arbitrary sheaf of `𝒪_X`-modules `𝒢` — informally, that the `𝒪_X`-module underlying
`𝒢 ⊗_{𝒪_X} colim_F 𝒪_X` is the filtered colimit of the `F^{j,*}𝒢`. This file builds the diagram
and the morphisms to `U_n (S_n 𝒢)` which that identification is about, so that the statement is
available in the exact shape the rest of Tag 0EXB consumes it in.

The iterates are `CategoryTheory.Functor.endoIter`, the `j`-fold composites of one functor, and
**not** extension or restriction of scalars along `φ^j`: extension of scalars is a sheafified
tensor product and does not compose on the nose, so those would differ from the iterates by an
isomorphism of left adjoints. The iterates are what
`AlgebraicGeometry.frobeniusStageExtendScalarsAdjunctionIter` and
`AlgebraicGeometry.pushforward_frobeniusStage_comp_iter` are stated against, and hence what the
comparison of Tag 0EXB on Hom-sets is stated against.

## Main definitions

* `AlgebraicGeometry.frobeniusRestrictScalars`,
  `AlgebraicGeometry.frobeniusStageRestrictScalars` and
  `AlgebraicGeometry.frobeniusExtendScalarsAdjunction`: names for `U_φ`, `U_n` and the adjunction
  `S_φ ⊣ U_φ`, which are `SheafOfModules.pushforward` and
  `SheafOfModules.pullbackPushforwardAdjunction` at the two structure maps already in use.
* `AlgebraicGeometry.frobeniusRestrictExtendIter`: the object `(U_φ)^{∘j}((S_φ)^{∘j}𝒢)`.
* `AlgebraicGeometry.frobeniusRestrictExtendIterMap`: **the transition morphism of the
  diagram**, `(U_φ)^{∘j}` applied to the Frobenius unit at `(S_φ)^{∘j}𝒢`.
* `AlgebraicGeometry.frobeniusRestrictExtendDiagram`: **the sequential diagram
  `j ↦ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`** of `𝒪_X`-modules.
* `AlgebraicGeometry.frobeniusStageRestrictLeg`: **the morphism
  `(U_φ)^{∘j}((S_φ)^{∘j}𝒢) ⟶ U_n (S_n 𝒢)`**, namely `(U_φ)^{∘j}` applied to the stage-`n + j`
  unit at `(S_φ)^{∘j}𝒢` followed by the restriction of
  `CategoryTheory.Adjunction.leftAdjointUniq` of the `j`-fold adjunction and the stage-`n` one.
* `AlgebraicGeometry.frobeniusStageRestrictCocone`: **the cocone** assembled from the diagram and
  those morphisms.

## Main results

* `CategoryTheory.Functor.map_comp_eqToHom_cancel` and
  `CategoryTheory.Functor.endoIter_map_comp_eqToHom_comp`: the two pieces of category algebra the
  cocone compatibility is assembled from, the second being the naturality of the comparison
  `F^j(F E) = F^{j + 1}E` in the form in which a transition morphism composes with a leg.
* `AlgebraicGeometry.unit_comp_map_frobeniusExtendScalarsStageIso_hom_app`: **one step of the
  cocone compatibility, at the level of `𝒪_X`-modules** — the Frobenius unit followed by the
  stage-`m + 1` unit and the one-step cocone comparison is the stage-`m` unit. This is the
  uniqueness of left adjoints read at an object.
* `AlgebraicGeometry.frobeniusRestrictExtendIterMap_comp_frobeniusStageRestrictLeg`: **the legs
  are compatible with the transitions of the diagram**, which is what makes them a cocone.

## Implementation notes

Three transports occur, all of them equalities of functors or of objects which hold on the nose
and are therefore `eqToHom`s rather than isomorphisms:
`CategoryTheory.Functor.endoIter_obj_obj`, which absorbs one application of `U_φ` into the
`j`-fold iterate in the transition morphism; the same for `S_φ`, which is definitional because
`CategoryTheory.Functor.endoIter` recurses by composing on the right; and
`AlgebraicGeometry.pushforward_frobeniusStage_comp_iter`, which identifies the target
`(U_φ)^{∘j}(U_{n + j}(S_n 𝒢))` of the leg with `U_n (S_n 𝒢)`. That they line up is the whole
content of this file: the types are what force the shape of the statement.

What is **not** here is that the resulting cocone is colimiting. That is the missing input
itself; it needs the
identification of the `𝒪_X`-module underlying an extension of scalars with a tensor product by
the underlying module of the target, of which the repository has only the lax form
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison`, together with a description of the
`𝒪_X`-module underlying `colim_F 𝒪_X`, of which the repository has none — the colimit of sheaves
of rings is formed abstractly, as the sheafification of the colimit of presheaves, and nothing
computes its sections. What is available, and is what such a proof would be assembled from, is
that restriction of scalars preserves all colimits
(`Stacks.SheafOfModules.pushforward_preservesColimits`), that extension of scalars does too,
being a left adjoint, and that tensoring does
(`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits`).

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v v₂ u u₂

namespace CategoryTheory

/-- **Two morphisms which agree after a transport of their target have the same image under a
functor, up to a transport.** The form is the one in which the legs of the cocone of Stacks Tag
0EXB are compared: both are the image of a morphism of `𝒪_X`-modules followed by an `eqToHom`,
and the two morphisms agree only after a transport. -/
lemma Functor.map_comp_eqToHom_cancel {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] (U : C ⥤ D) {P Q R : C} {S : D} (u : P ⟶ Q) (e : Q = R) (v : P ⟶ R)
    (h : u ≫ eqToHom e = v) (h₁ : U.obj Q = S) (h₂ : U.obj R = S) :
    U.map u ≫ eqToHom h₁ = U.map v ≫ eqToHom h₂ := by
  subst e
  rw [eqToHom_refl, Category.comp_id] at h
  rw [h]

/-- **One step of a cocone compatibility for iterates of an endofunctor.** Let `F` be an
endofunctor, let `ε : 𝒵 ⟶ F 𝒵'` and let `f : 𝒵' ⟶ 𝒲`. If `ε` followed by `F f` is, after a
transport, a morphism `g : 𝒵 ⟶ 𝒱`, then the `j`-fold iterate of `F` applied to `ε` followed by
the comparison `F^j (F 𝒵') = F^{j + 1}𝒵'`, followed by `F^{j + 1}f` and a transport, is `F^j g`
followed by a transport. This is the shape in which the transition morphisms and the legs of the
cocone of Stacks Tag 0EXB compose, and the proof is
`CategoryTheory.Functor.endoIter_map_comp_eqToHom` — the naturality of that comparison. -/
lemma Functor.endoIter_map_comp_eqToHom_comp {C : Type u} [Category.{v} C] (F : C ⥤ C) (j : ℕ)
    {Z Z' W V S : C} (ε : Z ⟶ F.obj Z') (f : Z' ⟶ W) (g : Z ⟶ V) (dd : F.obj W = V)
    (h : (ε ≫ F.map f) ≫ eqToHom dd = g) (d₁ : (F.endoIter (j + 1)).obj W = S)
    (d₀ : (F.endoIter j).obj V = S) :
    ((F.endoIter j).map ε ≫ eqToHom (F.endoIter_obj_obj j Z')) ≫
        ((F.endoIter (j + 1)).map f ≫ eqToHom d₁) =
      (F.endoIter j).map g ≫ eqToHom d₀ := by
  rw [Category.assoc, ← Category.assoc (eqToHom (F.endoIter_obj_obj j Z')),
    ← F.endoIter_map_comp_eqToHom j f, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, Category.assoc, eqToHom_trans]
  exact (F.endoIter j).map_comp_eqToHom_cancel _ dd _ h _ _

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### Restriction of scalars along Frobenius and along a coprojection -/

/-- **Restriction of scalars along the `p`-th power endomorphism of the structure sheaf.** This
is `SheafOfModules.pushforward` at `AlgebraicGeometry.frobeniusSelfStructureMap`, the right
adjoint of `AlgebraicGeometry.frobeniusExtendScalars`; only the name is shorter. -/
@[sga "5 IIIB 5.13" "special case"]
noncomputable abbrev frobeniusRestrictScalars :
    _root_.SheafOfModules.{u} X.ringSheafOnOpens ⥤
      _root_.SheafOfModules.{u} X.ringSheafOnOpens :=
  _root_.SheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX)

/-- **Restriction of scalars along the stage-`n` coprojection.** This is
`SheafOfModules.pushforward` at `AlgebraicGeometry.frobeniusStageStructureMap`, the right adjoint
of `AlgebraicGeometry.frobeniusStageExtendScalars`; only the name is shorter. -/
noncomputable abbrev frobeniusStageRestrictScalars (n : ℕ) :
    _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX) ⥤
      _root_.SheafOfModules.{u} X.ringSheafOnOpens :=
  _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)

/-- **Extension of scalars along the `p`-th power endomorphism of the structure sheaf is a left
adjoint of restriction of scalars along it.** This is
`SheafOfModules.pullbackPushforwardAdjunction` at
`AlgebraicGeometry.frobeniusSelfStructureMap`; only the name is shorter. -/
noncomputable abbrev frobeniusExtendScalarsAdjunction :
    frobeniusExtendScalars X p hX ⊣ frobeniusRestrictScalars X p hX :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (frobeniusSelfStructureMap X p hX)

/-! ### The diagram -/

/-- The object `(U_φ)^{∘j}((S_φ)^{∘j}𝒢)`: the `𝒪_X`-module obtained from `𝒢` by extending
scalars `j` times along the `p`-th power endomorphism of the structure sheaf and then restricting
them `j` times along it. Informally it is `F^{j,*}𝒢` read as an `𝒪_X`-module. -/
noncomputable def frobeniusRestrictExtendIter (j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    _root_.SheafOfModules.{u} X.ringSheafOnOpens :=
  ((frobeniusRestrictScalars X p hX).endoIter j).obj
    (((frobeniusExtendScalars X p hX).endoIter j).obj G)

/-- **The transition morphism of the diagram of Stacks Tag 0EXB**: the `j`-fold restriction of
scalars along Frobenius applied to the Frobenius unit at `(S_φ)^{∘j}𝒢`. The transport absorbs the
one extra restriction of scalars into the `j`-fold iterate. -/
noncomputable def frobeniusRestrictExtendIterMap (j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    frobeniusRestrictExtendIter X p hX j G ⟶ frobeniusRestrictExtendIter X p hX (j + 1) G :=
  ((frobeniusRestrictScalars X p hX).endoIter j).map
      ((frobeniusExtendScalarsAdjunction X p hX).unit.app
        (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≫
    eqToHom (Functor.endoIter_obj_obj (frobeniusRestrictScalars X p hX) j
      (((frobeniusExtendScalars X p hX).endoIter (j + 1)).obj G))

/-- **The sequential diagram `j ↦ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)` of `𝒪_X`-modules** whose colimit the
remaining input to Stacks Tag 0EXB asserts to be `U_n (S_n 𝒢)`. -/
noncomputable def frobeniusRestrictExtendDiagram
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    ℕ ⥤ _root_.SheafOfModules.{u} X.ringSheafOnOpens :=
  Functor.ofSequence (X := fun j ↦ frobeniusRestrictExtendIter X p hX j G)
    (fun j ↦ frobeniusRestrictExtendIterMap X p hX j G)

/-- The `j`-th object of the diagram is `(U_φ)^{∘j}((S_φ)^{∘j}𝒢)`. -/
@[simp]
lemma frobeniusRestrictExtendDiagram_obj (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (j : ℕ) :
    (frobeniusRestrictExtendDiagram X p hX G).obj j = frobeniusRestrictExtendIter X p hX j G :=
  rfl

/-- The transition morphism from stage `j` to stage `j + 1` of the diagram is
`AlgebraicGeometry.frobeniusRestrictExtendIterMap`. -/
@[simp]
lemma frobeniusRestrictExtendDiagram_map_succ
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) (j : ℕ) :
    (frobeniusRestrictExtendDiagram X p hX G).map (homOfLE (Nat.le_add_right j 1)) =
      frobeniusRestrictExtendIterMap X p hX j G :=
  Functor.ofSequence_map_homOfLE_succ _ j

/-! ### The morphisms to the restriction of the stage-`n` extension of scalars -/

/-- **The morphism `(U_φ)^{∘j}((S_φ)^{∘j}𝒢) ⟶ U_n (S_n 𝒢)`**: the `j`-fold restriction of scalars
along Frobenius applied to the stage-`n + j` unit at `(S_φ)^{∘j}𝒢`, followed by the restriction of
scalars of the comparison of the `j`-fold left adjoint of `U_n` with the stage-`n` one. The
transport is `AlgebraicGeometry.pushforward_frobeniusStage_comp_iter`, which says that `j`
restrictions along Frobenius after one along the stage-`n + j` coprojection is one along the
stage-`n` coprojection. -/
noncomputable def frobeniusStageRestrictLeg (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    frobeniusRestrictExtendIter X p hX j G ⟶
      (frobeniusStageRestrictScalars X p hX n).obj
        ((frobeniusStageExtendScalars X p hX n).obj G) :=
  ((frobeniusRestrictScalars X p hX).endoIter j).map
      ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
        (frobeniusStageRestrictScalars X p hX (n + j)).map
          ((Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
            (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app G)) ≫
    eqToHom (Functor.congr_obj (pushforward_frobeniusStage_comp_iter X p hX n j)
      ((frobeniusStageExtendScalars X p hX n).obj G))

/-! ### The legs are compatible with the transitions -/

/-- **One step of the cocone compatibility, at the level of `𝒪_X`-modules.** The Frobenius unit
at `𝒵`, followed by the restriction of scalars along Frobenius of the stage-`m + 1` unit and of
anything out of the one-step cocone comparison, is the stage-`m` unit followed by the restriction
of scalars of that thing. Both sides are morphisms `𝒵 ⟶ U_m 𝒜`, the left one after the transport
`AlgebraicGeometry.pushforward_frobeniusStage_comp`.

This is the uniqueness of left adjoints read at an object: the Frobenius unit followed by the
stage-`m + 1` unit is the unit of the composite adjunction, and
`AlgebraicGeometry.frobeniusExtendScalarsStageIso` is by definition
`CategoryTheory.Adjunction.leftAdjointUniq` of that composite and the stage-`m` adjunction. -/
lemma unit_comp_map_frobeniusExtendScalarsStageIso_hom_app (m : ℕ)
    (Z : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (A : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (t : (frobeniusStageExtendScalars X p hX m).obj Z ⟶ A) :
    ((frobeniusExtendScalarsAdjunction X p hX).unit.app Z ≫
          (frobeniusRestrictScalars X p hX).map
            ((frobeniusStageExtendScalarsAdjunction X p hX (m + 1)).unit.app
                ((frobeniusExtendScalars X p hX).obj Z) ≫
              (frobeniusStageRestrictScalars X p hX (m + 1)).map
                ((frobeniusExtendScalarsStageIso X p hX m).hom.app Z ≫ t))) ≫
        eqToHom (Functor.congr_obj (pushforward_frobeniusStage_comp X p hX m) A) =
      (frobeniusStageExtendScalarsAdjunction X p hX m).unit.app Z ≫
        (frobeniusStageRestrictScalars X p hX m).map t := by
  have hcomp : _root_.SheafOfModules.pushforward.{u}
        (frobeniusStageStructureMap X p hX (m + 1)) ⋙ frobeniusRestrictScalars X p hX =
      frobeniusStageRestrictScalars X p hX m :=
    pushforward_frobeniusStage_comp X p hX m
  have key : ((frobeniusExtendScalarsAdjunction X p hX).unit.app Z ≫
        (frobeniusRestrictScalars X p hX).map
          ((frobeniusStageExtendScalarsAdjunction X p hX (m + 1)).unit.app
            ((frobeniusExtendScalars X p hX).obj Z))) ≫
      (frobeniusRestrictScalars X p hX).map
        ((frobeniusStageRestrictScalars X p hX (m + 1)).map
          ((frobeniusExtendScalarsStageIso X p hX m).hom.app Z)) =
      (frobeniusStageExtendScalarsAdjunction X p hX m).unit.app Z ≫
        eqToHom (Functor.congr_obj hcomp
          ((frobeniusStageExtendScalars X p hX m).obj Z)).symm := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app
      ((frobeniusExtendScalarsAdjunction X p hX).comp
        (frobeniusStageExtendScalarsAdjunction X p hX (m + 1)))
      ((frobeniusStageExtendScalarsAdjunction X p hX m).ofNatIsoRight
        (eqToIso (pushforward_frobeniusStage_comp X p hX m).symm)) Z
    have hiso : (Adjunction.leftAdjointUniq
          ((frobeniusExtendScalarsAdjunction X p hX).comp
            (frobeniusStageExtendScalarsAdjunction X p hX (m + 1)))
          ((frobeniusStageExtendScalarsAdjunction X p hX m).ofNatIsoRight
            (eqToIso (pushforward_frobeniusStage_comp X p hX m).symm))).hom.app Z =
        (frobeniusExtendScalarsStageIso X p hX m).hom.app Z := rfl
    rw [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, hiso] at h
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app,
      Functor.comp_map] using h
  rw [Functor.map_comp (frobeniusStageRestrictScalars X p hX (m + 1))]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [key, ← Functor.comp_map, Functor.congr_hom hcomp t]
  simp

/-- **The legs of Stacks Tag 0EXB are compatible with the transitions of the diagram**: the
transition morphism from `j` to `j + 1` followed by the leg at `j + 1` is the leg at `j`. This is
what makes the legs a cocone.

The transition's transport is moved past the leg by
`CategoryTheory.Functor.endoIter_map_comp_eqToHom`, which reduces the identity to
`AlgebraicGeometry.unit_comp_map_frobeniusExtendScalarsStageIso_hom_app` at the stage `n + j`,
applied to `CategoryTheory.Adjunction.leftAdjointUniq` of the `j`-fold adjunction — the one step
of comparison which
`AlgebraicGeometry.leftAdjointUniq_frobeniusStageExtendScalarsAdjunctionIter_succ` peels off
being exactly the one-step cocone comparison that lemma consumes. -/
theorem frobeniusRestrictExtendIterMap_comp_frobeniusStageRestrictLeg (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    frobeniusRestrictExtendIterMap X p hX j G ≫
        frobeniusStageRestrictLeg X p hX n (j + 1) G =
      frobeniusStageRestrictLeg X p hX n j G := by
  simp only [frobeniusRestrictExtendIterMap, frobeniusStageRestrictLeg,
    leftAdjointUniq_frobeniusStageExtendScalarsAdjunctionIter_succ]
  exact Functor.endoIter_map_comp_eqToHom_comp (frobeniusRestrictScalars X p hX) j _ _ _ _
    (unit_comp_map_frobeniusExtendScalarsStageIso_hom_app X p hX (n + j) _ _ _) _ _

/-- **The cocone of Stacks Tag 0EXB**: the diagram `j ↦ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)` with its
morphisms to `U_n (S_n 𝒢)`. The remaining input to the full faithfulness half of Tag 0EXB is
that this cocone is colimiting. -/
noncomputable def frobeniusStageRestrictCocone (n : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    Cocone (frobeniusRestrictExtendDiagram X p hX G) where
  pt := (frobeniusStageRestrictScalars X p hX n).obj
    ((frobeniusStageExtendScalars X p hX n).obj G)
  ι := NatTrans.ofSequence (fun j ↦ frobeniusStageRestrictLeg X p hX n j G) (fun j ↦ by
    have h : (frobeniusRestrictExtendDiagram X p hX G).map (homOfLE (j.le_add_right 1)) ≫
          frobeniusStageRestrictLeg X p hX n (j + 1) G =
        frobeniusStageRestrictLeg X p hX n j G := by
      rw [frobeniusRestrictExtendDiagram_map_succ]
      exact frobeniusRestrictExtendIterMap_comp_frobeniusStageRestrictLeg X p hX n j G
    exact h.trans (Category.comp_id _).symm)

/-- The `j`-th leg of the cocone is `AlgebraicGeometry.frobeniusStageRestrictLeg`. -/
@[simp]
lemma frobeniusStageRestrictCocone_ι_app (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (frobeniusStageRestrictCocone X p hX n G).ι.app j =
      frobeniusStageRestrictLeg X p hX n j G :=
  rfl

end AlgebraicGeometry

end
