module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafDiagram

/-!
# The cocone of Stacks Tag 0EXB is the sheafification of the objectwise one

The legs and the transition morphisms of the cocone of Stacks Tag 0EXB are morphisms of sheaves
of `𝒪_X`-modules between extensions of scalars along two different morphisms of sheaves of
rings, and
`Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo` identifies such a morphism, on the
underlying abelian sheaves, with the sheafification of the objectwise base change — provided it
carries the unit of the one pullback adjunction to the unit of the other and is semilinear. This
file supplies those two inputs for the legs and for the transitions.

## Main definitions

* `AlgebraicGeometry.frobeniusIterStageHom`: the morphism of modules over `𝒪_X` read through
  `φ^j` whose restriction of scalars the leg of the cocone is, and
  `AlgebraicGeometry.frobeniusIterTransitionHom` the same for the transition morphism.

## Main results

* `AlgebraicGeometry.pushforward_frobeniusStage_comp_pushforward_frobeniusIter`: restriction of
  scalars along the stage-`n + j` coprojection followed by restriction of scalars along `φ^j` is
  restriction of scalars along the stage-`n` coprojection.
* `AlgebraicGeometry.unit_comp_frobeniusIterStageLeg`: **the leg carries the unit of the `φ^j`
  pullback adjunction to the unit of the stage-`n` one**, which is
  `AlgebraicGeometry.unit_comp_frobeniusStageRestrictLeg` transported along
  `AlgebraicGeometry.frobeniusExtendScalarsIterIso`.
* `AlgebraicGeometry.pullbackCompToSheafIso_frobeniusIterStageHom`: **the leg of the cocone is
  the sheafification of the objectwise base change along the stage-`n + j` coprojection.**
* `AlgebraicGeometry.unit_comp_frobeniusIterTransitionHom`: the same for the transition
  morphism, which is the adjunct of the `φ^{j+1}` unit.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u v₂ u₂

namespace CategoryTheory

/-- **Rewriting the first two factors of a four-fold composite.** The composite is read
`u ≫ (a ≫ b) ≫ c`, which is the shape a morphism built as an image followed by a transport
composes in; over a variable category `rw` has no trouble reassociating it. -/
lemma comp_comp_comp_congr {D : Type u₂} [Category.{v₂} D] {P Q R S T Q' : D} (u : P ⟶ Q)
    (a : Q ⟶ R) (b : R ⟶ S) (c : S ⟶ T) (v : P ⟶ Q') (w : Q' ⟶ R) (h : u ≫ a = v ≫ w) :
    u ≫ (a ≫ b) ≫ c = v ≫ (w ≫ b) ≫ c := by
  simp only [← Category.assoc, h]

/-- **A transport cancelled against its inverse.** -/
lemma comp_eqToHom_symm_comp_eqToHom_self {D : Type u₂} [Category.{v₂} D] {A B : D} (h : A = B)
    {W : D} (f : W ⟶ B) : (f ≫ eqToHom h.symm) ≫ eqToHom h = f := by
  subst h
  rw [eqToHom_refl, Category.comp_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **Restriction of scalars along the stage-`n + j` coprojection followed by restriction of
scalars along the `j`-th power of Frobenius is restriction of scalars along the stage-`n`
coprojection.** This is `AlgebraicGeometry.pushforward_frobeniusStage_comp_iter` with the
`j`-fold iterate replaced by restriction of scalars along `φ^j`. -/
lemma pushforward_frobeniusStage_comp_pushforward_frobeniusIter (n j : ℕ) :
    _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX (n + j)) ⋙
        _root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j) =
      frobeniusStageRestrictScalars X p hX n := by
  rw [← pushforward_frobeniusRingSheafIter X p hX j]
  exact pushforward_frobeniusStage_comp_iter X p hX n j

/-- **The morphism of modules over `𝒪_X` read through `φ^j` whose restriction of scalars is the
leg of the cocone of Stacks Tag 0EXB**: the comparison of extension of scalars along `φ^j` with
the `j`-fold iterate, followed by the stage-`n + j` unit and the comparison of the `j`-fold left
adjoint of `U_n` with the stage-`n` one. -/
noncomputable def frobeniusIterStageHom (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullback.{u} (frobeniusSelfIterStructureMap X p hX j)).obj G ⟶
      (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX (n + j))).obj
        ((frobeniusStageExtendScalars X p hX n).obj G) :=
  (frobeniusExtendScalarsIterIso X p hX j).inv.app G ≫
    ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
        (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
      (frobeniusStageRestrictScalars X p hX (n + j)).map
        ((Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
          (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app G))

/-- The unit of the pullback adjunction along `φ^j`, followed by restriction of scalars along
`φ^j` of the comparison with the `j`-fold iterate, is the unit of the `j`-fold iterated
adjunction, transported along
`AlgebraicGeometry.pushforward_frobeniusRingSheafIter`. -/
lemma unit_comp_pushforward_map_frobeniusExtendScalarsIterIso_inv_app (j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)).unit.app G ≫
        (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j)).map
          ((frobeniusExtendScalarsIterIso X p hX j).inv.app G) =
      (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
        eqToHom (Functor.congr_obj (pushforward_frobeniusRingSheafIter X p hX j)
          (((frobeniusExtendScalars X p hX).endoIter j).obj G)) := by
  have hi : frobeniusExtendScalarsIterIso X p hX j =
      Adjunction.leftAdjointUniq
        ((frobeniusExtendScalarsAdjunctionIter X p hX j).ofNatIsoRight
          (eqToIso (pushforward_frobeniusRingSheafIter X p hX j)))
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)) := rfl
  rw [hi, Adjunction.leftAdjointUniq_inv_app, Adjunction.unit_leftAdjointUniq_hom_app,
    Adjunction.ofNatIsoRight_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]

/-- **The leg of the cocone of Stacks Tag 0EXB, read as a morphism from the pullback along `φ^j`
pushed forward to the pullback along the stage-`n` coprojection pushed forward.** This is the
shape `Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo` compares with the objectwise base
change. -/
noncomputable def frobeniusIterStageLeg (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j)).obj
        ((_root_.SheafOfModules.pullback.{u} (frobeniusSelfIterStructureMap X p hX j)).obj G) ⟶
      (_root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)).obj
        ((_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n)).obj G) :=
  (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j)).map
      (frobeniusIterStageHom X p hX n j G) ≫
    eqToHom (Functor.congr_obj
      (pushforward_frobeniusStage_comp_pushforward_frobeniusIter X p hX n j)
      ((frobeniusStageExtendScalars X p hX n).obj G))

/-- **The leg carries the unit of the pullback adjunction along `φ^j` to the unit of the
pullback adjunction along the stage-`n` coprojection.** This is
`AlgebraicGeometry.unit_comp_frobeniusStageRestrictLeg` transported along
`AlgebraicGeometry.frobeniusExtendScalarsIterIso`, and it is the hypothesis `hℓ` of
`Stacks.SheafOfModules.toSheaf_map_comp_baseChangeTo`. -/
theorem unit_comp_frobeniusIterStageLeg (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)).unit.app G ≫
        frobeniusIterStageLeg X p hX n j G =
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (frobeniusStageStructureMap X p hX n)).unit.app G := by
  refine Eq.trans (congrArg (fun q ↦ (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusSelfIterStructureMap X p hX j)).unit.app G ≫ q ≫ eqToHom (Functor.congr_obj
        (pushforward_frobeniusStage_comp_pushforward_frobeniusIter X p hX n j)
        ((frobeniusStageExtendScalars X p hX n).obj G)))
    (CategoryTheory.Functor.map_comp
      (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j))
      ((frobeniusExtendScalarsIterIso X p hX j).inv.app G) _)) ?_
  refine Eq.trans (CategoryTheory.comp_comp_comp_congr _ _ _ _ _ _
    (unit_comp_pushforward_map_frobeniusExtendScalarsIterIso_inv_app X p hX j G)) ?_
  refine Eq.trans (congrArg (fun q ↦ (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
      q ≫ eqToHom (Functor.congr_obj
        (pushforward_frobeniusStage_comp_pushforward_frobeniusIter X p hX n j)
        ((frobeniusStageExtendScalars X p hX n).obj G)))
    (Functor.eqToHom_comp_map (pushforward_frobeniusRingSheafIter X p hX j) _)) ?_
  refine Eq.trans (congrArg (fun q ↦ (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫ q)
    ((Category.assoc _ _ _).trans (congrArg
      (fun q ↦ ((frobeniusRestrictScalars X p hX).endoIter j).map _ ≫ q)
      (eqToHom_trans _ _)))) ?_
  exact unit_comp_frobeniusStageRestrictLeg X p hX n j G

/-- The hypothesis `hψres` of
`Stacks.SheafOfModules.pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward` for the
stage-`n` coprojection: `AlgebraicGeometry.restrictScalars_frobeniusRingPresheafι_comp` followed
by restriction of scalars along the identity of the sections of `𝒪_X`. -/
lemma restrictScalars_frobeniusRingPresheafι_comp_restrictScalars_id (n : ℕ) :
    (_root_.SheafOfModules.forget (frobeniusColimitRingSheaf X p hX) ⋙
          PresheafOfModules.restrictScalars (toFrobeniusColimitRingSheaf X p hX)) ⋙
        PresheafOfModules.restrictScalars.{u} (frobeniusRingPresheafι X p hX n) =
      ((_root_.SheafOfModules.forget (frobeniusColimitRingSheaf X p hX) ⋙
            PresheafOfModules.restrictScalars (𝟙 (frobeniusColimitRingSheaf X p hX).obj)) ⋙
          PresheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n).hom) ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj) :=
  (restrictScalars_frobeniusRingPresheafι_comp X p hX n).trans (Functor.comp_id _).symm

set_option maxHeartbeats 400000 in
-- Checking this statement with its proof replaced by `sorry` (drake's fast mode) exceeds the
-- kernel's default budget: `(kernel) deterministic timeout`. 400000 is enough.
/-- **The leg of the cocone of Stacks Tag 0EXB is, on the underlying abelian sheaves and through
`Stacks.SheafOfModules.pullbackCompToSheafIso`, the sheafification of the objectwise base change
along the stage-`n + j` coprojection.** -/
theorem pullbackCompToSheafIso_frobeniusIterStageHom (n j : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    ((_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            (frobeniusIterStageHom X p hX n j G) ≫
          eqToHom (Functor.congr_obj
            (frobeniusStageRestrictScalars_comp_toSheaf X p hX (n + j))
            ((frobeniusStageExtendScalars X p hX n).obj G))) ≫
        (Stacks.SheafOfModules.pullbackCompToSheafIso
          (frobeniusStageStructureMap X p hX n) (toFrobeniusColimitRingSheaf X p hX)
          (frobeniusRingPresheafι X p hX n)
          (restrictScalars_frobeniusRingPresheafι_comp X p hX n)).hom.app G =
      (Stacks.SheafOfModules.pullbackCompToSheafIso
          (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
          (frobeniusRingSheafIter X p hX j).hom
          (restrictScalars_frobeniusRingSheafIter_comp X p hX j)).hom.app G ≫
        (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
          (@CategoryTheory.Functor.map _ _ _ _
            (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
            (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
              (frobeniusRingSheafIter X p hX j).hom G.val)
            (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
              (frobeniusRingPresheafι X p hX n) G.val)
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
              (frobeniusRingSheafIter X p hX j).hom
              (frobeniusRingPresheafι X p hX (n + j)) G.val
              (frobeniusRingPresheafι X p hX n)
              (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n))) :=
  Stacks.SheafOfModules.pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward
    (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
    (frobeniusRingSheafIter X p hX j).hom
    (restrictScalars_frobeniusRingSheafIter_comp X p hX j)
    (frobeniusStageStructureMap X p hX n) (toFrobeniusColimitRingSheaf X p hX)
    (frobeniusRingPresheafι X p hX n)
    (restrictScalars_frobeniusRingPresheafι_comp X p hX n)
    (frobeniusRingPresheafι X p hX (n + j))
    (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n) G
    (frobeniusStageStructureMap X p hX (n + j))
    (restrictScalars_frobeniusRingPresheafι_comp_restrictScalars_id X p hX (n + j))
    (pushforward_frobeniusStage_comp_pushforward_frobeniusIter X p hX n j)
    (frobeniusStageRestrictScalars_comp_toSheaf X p hX (n + j))
    (frobeniusIterStageHom X p hX n j G)
    (unit_comp_frobeniusIterStageLeg X p hX n j G)

/-! ### The transition morphisms

The stage `j + 1` is carried as a variable `k` together with `j + 1 = k` throughout. Without
that, `AlgebraicGeometry.frobeniusRingSheafIter` at `j + 1` reduces by its defining recursion,
and the kernel unfolds it inside every type of the square until it runs out of budget. -/

/-- **The `j`-th power of Frobenius followed by Frobenius is the `k`-th power, read on
sections**, for any `k` equal to `j + 1`. -/
lemma frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' (j k : ℕ) (hk : j + 1 = k) :
    (frobeniusRingSheafIter X p hX j).hom ≫ (frobeniusRingSheafHom X p hX).hom =
      (frobeniusRingSheafIter X p hX k).hom := by
  subst hk
  exact frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom X p hX j

/-- **Restriction of scalars along Frobenius followed by restriction of scalars along `φ^j` is
restriction of scalars along `φ^k`** for any `k` equal to `j + 1`. -/
lemma pushforward_frobeniusSelf_comp_pushforward_frobeniusIter (j k : ℕ) (hk : j + 1 = k) :
    _root_.SheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX) ⋙
        _root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j) =
      _root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX k) := by
  subst hk
  rw [← pushforward_frobeniusRingSheafIter X p hX j,
    ← pushforward_frobeniusRingSheafIter X p hX (j + 1), Functor.endoIter_succ,
    Functor.endoIter_comp_self]

/-- The hypothesis `hψres` of
`Stacks.SheafOfModules.pullbackCompToSheafIso_comp_baseChangeTo_of_pushforward` for one
Frobenius: restriction of scalars along Frobenius read as an endomorphism of the sections and
read as a structure map agree, because the two spellings of Frobenius have the same underlying
morphism of presheaves of rings. -/
lemma restrictScalars_frobeniusRingSheafHom_comp :
    (_root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj)) ⋙
        PresheafOfModules.restrictScalars.{u} (frobeniusRingSheafHom X p hX).hom =
      ((_root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj)) ⋙
          PresheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX).hom) ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringSheafOnOpens.obj) :=
  rfl

/-- **The transition morphism of the diagram of Stacks Tag 0EXB, read as a morphism of modules
over `𝒪_X` through `φ^j`**: the adjunct of the `φ^k` unit. -/
noncomputable def frobeniusIterTransitionHom (j k : ℕ) (hk : j + 1 = k)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullback.{u} (frobeniusSelfIterStructureMap X p hX j)).obj G ⟶
      (_root_.SheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX)).obj
        ((_root_.SheafOfModules.pullback.{u} (frobeniusSelfIterStructureMap X p hX k)).obj G) :=
  ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusSelfIterStructureMap X p hX j)).homEquiv G _).symm
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (frobeniusSelfIterStructureMap X p hX k)).unit.app G ≫
      eqToHom (Functor.congr_obj
        (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j k hk)
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusSelfIterStructureMap X p hX k)).obj G)).symm)

/-- **The transition morphism carries the unit of the `φ^j` pullback adjunction to the unit of
the `φ^k` one.** It is the adjunct of that unit, so this is the adjunction. -/
theorem unit_comp_frobeniusIterTransitionHom (j k : ℕ) (hk : j + 1 = k)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)).unit.app G ≫
        ((_root_.SheafOfModules.pushforward.{u} (frobeniusSelfIterStructureMap X p hX j)).map
            (frobeniusIterTransitionHom X p hX j k hk G) ≫
          eqToHom (Functor.congr_obj
            (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j k hk)
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusSelfIterStructureMap X p hX k)).obj G))) =
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (frobeniusSelfIterStructureMap X p hX k)).unit.app G := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫ eqToHom (Functor.congr_obj
      (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j k hk)
      ((_root_.SheafOfModules.pullback.{u}
        (frobeniusSelfIterStructureMap X p hX k)).obj G)))
    ((Adjunction.homEquiv_unit (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)) G _
        (frobeniusIterTransitionHom X p hX j k hk G)).symm.trans
      (Equiv.apply_symm_apply _ _))) ?_
  exact CategoryTheory.comp_eqToHom_symm_comp_eqToHom_self (Functor.congr_obj
    (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j k hk)
    ((_root_.SheafOfModules.pullback.{u}
      (frobeniusSelfIterStructureMap X p hX k)).obj G)) _

/-- **The transition morphism of the diagram of Stacks Tag 0EXB is, on the underlying abelian
sheaves and through `Stacks.SheafOfModules.pullbackObjToSheafIso`, the sheafification of the
objectwise base change along one Frobenius.**

Both comparisons are read at the single sheaf `𝒢` through
`Stacks.SheafOfModules.pullbackObjToSheafIso`, which is
`Stacks.SheafOfModules.pullbackCompToSheafIso` evaluated there. Here the presheaf of rings is
the sections of the structure sheaf itself on both sides, so the two spellings of the
sheafification of the objectwise tensor product agree only after the sheafification functor is
unfolded, and that one definition is what keeps the kernel from being asked to do it. -/
theorem pullbackCompToSheafIso_frobeniusIterTransitionHom (j k : ℕ) (hk : j + 1 = k)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens) :
    ((_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            (frobeniusIterTransitionHom X p hX j k hk G) ≫
          eqToHom (Functor.congr_obj (frobeniusRestrictScalars_comp_toSheaf X p hX)
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusSelfIterStructureMap X p hX k)).obj G))) ≫
        (Stacks.SheafOfModules.pullbackObjToSheafIso
          (frobeniusSelfIterStructureMap X p hX k) (𝟙 X.ringSheafOnOpens.obj)
          (frobeniusRingSheafIter X p hX k).hom
          (restrictScalars_frobeniusRingSheafIter_comp X p hX k) G).hom =
      (Stacks.SheafOfModules.pullbackObjToSheafIso
          (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
          (frobeniusRingSheafIter X p hX j).hom
          (restrictScalars_frobeniusRingSheafIter_comp X p hX j) G).hom ≫
        (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
          (@CategoryTheory.Functor.map _ _ _ _
            (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
            (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
              (frobeniusRingSheafIter X p hX j).hom G.val)
            (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
              (frobeniusRingSheafIter X p hX k).hom G.val)
            (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
              (frobeniusRingSheafIter X p hX j).hom
              (frobeniusRingSheafHom X p hX).hom G.val
              (frobeniusRingSheafIter X p hX k).hom
              (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' X p hX j k hk))) :=
  Stacks.SheafOfModules.pullbackObjToSheafIso_comp_baseChangeTo_of_pushforward
    (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
    (frobeniusRingSheafIter X p hX j).hom
    (restrictScalars_frobeniusRingSheafIter_comp X p hX j)
    (frobeniusSelfIterStructureMap X p hX k) (𝟙 X.ringSheafOnOpens.obj)
    (frobeniusRingSheafIter X p hX k).hom
    (restrictScalars_frobeniusRingSheafIter_comp X p hX k)
    (frobeniusRingSheafHom X p hX).hom
    (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' X p hX j k hk) G
    (frobeniusSelfStructureMap X p hX) (restrictScalars_frobeniusRingSheafHom_comp X p hX)
    (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j k hk)
    (frobeniusRestrictScalars_comp_toSheaf X p hX)
    (frobeniusIterTransitionHom X p hX j k hk G)
    (unit_comp_frobeniusIterTransitionHom X p hX j k hk G)

end AlgebraicGeometry

end
