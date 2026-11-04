module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SepClosedFieldConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage

/-!
# A boundary class dies where its section lifts

Let `0 → A → I → Q → 0` be a short exact sequence of abelian sheaves on the small étale site of a
scheme `Y`, let `σ` be a global section of `Q` and let `∂σ ∈ H^1(Y, A)` be its boundary. If
`U ⟶ Y` is étale and the restriction of `σ` to `U` lifts to a section of `I` over `U`, then `∂σ`
restricts to zero in `H^1(U, A|_U)`.

This is the statement that the class of a torsor dies on any étale `U` over which the torsor has
a section, in the form the proof of [Stacks, Tag 0EYT] uses: there `A` is a finite constant sheaf,
`I` is injective, the torsor is the fibre of `I → Q` over `σ` and `U` is the finite étale cover
representing it.

## Main definitions

* `Stacks.EtaleCohomology.terminalEtale` — the terminal object `Y ⟶ Y` of the small étale site.
* `Stacks.EtaleCohomology.sectionOfHom` — the global section corresponding to a map out of the
  constant sheaf `ℤ`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_extClass_eq_zero` — the vanishing.

## Implementation notes

Restriction commutes with boundaries (`etaleCohomologyRestrictionMap_comp_extClass`), so it is
enough that the inverse image of `σ` to `U` factors through the inverse image of `I ⟶ Q`. By the
adjunction between inverse and direct image this is a factorization of `σ ≫ η_Q` through
`p_*p^{-1}(I ⟶ Q)`, and that one is produced on global sections: the unit `η_I` carries the lift
over `U` to a section of `p^{-1}I` over `U ×_Y U`, which pulls back along the diagonal to a global
section of `p^{-1}I` over `U` mapping to the image of `σ`.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

variable {Y : Scheme.{u}}

variable (Y) in
/-- The terminal object `Y ⟶ Y` of the small étale site of `Y`. -/
abbrev terminalEtale : Y.Etale := Scheme.Etale.mk (𝟙 Y)

variable (Y) in
/-- `Y ⟶ Y` is terminal in the small étale site of `Y`. -/
def terminalEtaleIsTerminal : IsTerminal (terminalEtale Y) :=
  MorphismProperty.Over.mkIdTerminal _ _

/-- The global section of an abelian sheaf corresponding to a map out of the constant sheaf
`ℤ`: the image of `1` under the adjoint map `ℤ ⟶ Γ(Y, G)`. -/
def sectionOfHom {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (σ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ G) : G.obj.obj (op (terminalEtale Y)) :=
  ((constantSheafAdj _ _ (terminalEtaleIsTerminal Y)).homEquiv _ _ σ) ⟨1⟩

/-- Two maps out of `ULift ℤ` agreeing on `1` are equal. -/
theorem ulift_int_hom_ext {G : AddCommGrpCat.{u + 1}} {f f' : AddCommGrpCat.of (ULift ℤ) ⟶ G}
    (h : f ⟨1⟩ = f' ⟨1⟩) : f = f' := by
  ext ⟨n⟩
  have hn : (⟨n⟩ : ULift ℤ) = n • (⟨1⟩ : ULift ℤ) := by
    ext
    simp
  rw [hn, map_zsmul, map_zsmul, h]

/-- The map `ULift ℤ ⟶ G` sending `1` to `x`. -/
def uliftIntHom {G : AddCommGrpCat.{u + 1}} (x : G) : AddCommGrpCat.of (ULift ℤ) ⟶ G :=
  AddCommGrpCat.ofHom ((zmultiplesHom G x).comp AddEquiv.ulift.toAddMonoidHom)

/-- The map `uliftIntHom x` sends `1` to `x`. -/
@[simp]
theorem uliftIntHom_apply_one {G : AddCommGrpCat.{u + 1}} (x : G) : uliftIntHom x ⟨1⟩ = x :=
  one_zsmul x

section Diagonal

variable (U : Y.Etale)

/-- The base change of the terminal object along `p : U ⟶ Y`. -/
abbrev bcTerminal : U.left.Etale := (smallEtaleBaseChange U.hom).obj (terminalEtale Y)

/-- The structure morphism of the base change of the terminal object is an isomorphism. -/
instance : IsIso (bcTerminal U).hom := by
  change IsIso (pullback.snd (𝟙 Y) U.hom)
  infer_instance

/-- The base change of the terminal object is terminal. -/
def bcTerminalIsTerminal : IsTerminal (bcTerminal U) := isTerminalOfIsIsoHom _

/-- **The diagonal**, as a morphism from the base change of the terminal object to the base change
of `U` itself, over `U`. -/
def bcDiagonal : bcTerminal U ⟶ (smallEtaleBaseChange U.hom).obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.snd (𝟙 Y) U.hom) (pullback.snd (𝟙 Y) U.hom) rfl)
    (pullback.lift_snd _ _ _)

/-- The diagonal followed by the base change of the terminal map is the identity, the base change
of the terminal object being terminal. -/
theorem bcDiagonal_comp_map :
    bcDiagonal U ≫ (smallEtaleBaseChange U.hom).map ((terminalEtaleIsTerminal Y).from U) = 𝟙 _ :=
  (bcTerminalIsTerminal U).hom_ext _ _

end Diagonal

/-- Pulling the unit image of a lift back along the diagonal gives the unit image of the global
section it lifts. -/
private theorem inverseImage_map_bcDiagonal_unit_eq
    {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : A ⟶ B) (U : Y.Etale)
    (t : A.obj.obj (op U)) (s : B.obj.obj (op (terminalEtale Y)))
    (ht : g.hom.app (op U) t = B.obj.map ((terminalEtaleIsTerminal Y).from U).op s) :
    ((etaleAbelianInverseImage.{u, u + 1} U.hom).map g).hom.app (op (bcTerminal U))
        (((etaleAbelianInverseImage.{u, u + 1} U.hom).obj A).obj.map (bcDiagonal U).op
          (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} U.hom).unit.app A).hom.app
            (op U) t)) =
      ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} U.hom).unit.app B).hom.app
        (op (terminalEtale Y)) s := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} U.hom
  let F := etaleAbelianInverseImage.{u, u + 1} U.hom
  let h := (terminalEtaleIsTerminal Y).from U
  have h₁ : (F.map g).hom.app (op (bcTerminal U))
        ((F.obj A).obj.map (bcDiagonal U).op ((adj.unit.app A).hom.app (op U) t)) =
      (F.obj B).obj.map (bcDiagonal U).op
        ((F.map g).hom.app _ ((adj.unit.app A).hom.app (op U) t)) :=
    NatTrans.naturality_apply (F.map g).hom (bcDiagonal U).op _
  have h₂ : (F.map g).hom.app _ ((adj.unit.app A).hom.app (op U) t) =
      (adj.unit.app B).hom.app (op U) (g.hom.app (op U) t) :=
    (congrArg (fun φ => φ.hom.app (op U) t) (adj.unit.naturality g)).symm
  have h₃ : (adj.unit.app B).hom.app (op U) (B.obj.map h.op s) =
      (F.obj B).obj.map ((smallEtaleBaseChange U.hom).map h).op
        ((adj.unit.app B).hom.app (op (terminalEtale Y)) s) :=
    NatTrans.naturality_apply (adj.unit.app B).hom h.op _
  have e : (F.obj B).obj.map ((smallEtaleBaseChange U.hom).map h).op ≫
      (F.obj B).obj.map (bcDiagonal U).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, bcDiagonal_comp_map, op_id,
      CategoryTheory.Functor.map_id]
  refine h₁.trans ?_
  refine (congrArg (ConcreteCategory.hom ((F.obj B).obj.map (bcDiagonal U).op)) h₂).trans ?_
  rw [ht]
  refine (congrArg (ConcreteCategory.hom ((F.obj B).obj.map (bcDiagonal U).op)) h₃).trans ?_
  exact congrArg (fun m : (F.obj B).obj.obj (op (bcTerminal U)) ⟶
      (F.obj B).obj.obj (op (bcTerminal U)) =>
        m ((adj.unit.app B).hom.app (op (terminalEtale Y)) s)) e

/-- **A boundary class dies where its section lifts.** Let `S` be a short exact sequence of
abelian sheaves on the small étale site of `Y`, let `σ : ℤ ⟶ S.X₃` be a global section, and let
`U` be an étale `Y`-scheme over which the restriction of `σ` lifts to a section `t` of `S.X₂`.
Then the restriction to `U` of the boundary `∂σ ∈ H^1(Y, S.X₁)` vanishes. -/
theorem etaleCohomologyRestrictionMap_comp_extClass_eq_zero
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (σ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ S.X₃)
    (U : Y.Etale) (t : S.X₂.obj.obj (op U))
    (ht : S.g.hom.app (op U) t =
      S.X₃.obj.map ((terminalEtaleIsTerminal Y).from U).op (sectionOfHom σ)) :
    etaleCohomologyRestrictionMap.{u, u + 1, u + 1} U.hom S.X₁ 1
      ((Ext.mk₀ σ).comp hS.extClass (zero_add 1)) = 0 := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} U.hom
  let cadj := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    (terminalEtaleIsTerminal Y)
  let F := etaleAbelianInverseImage.{u, u + 1} U.hom
  let x : (F.obj S.X₂).obj.obj (op (bcTerminal U)) :=
    (F.obj S.X₂).obj.map (bcDiagonal U).op ((adj.unit.app S.X₂).hom.app (op U) t)
  let τ' : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ (etaleAbelianDirectImage.{u, u + 1} U.hom).obj (F.obj S.X₂) :=
    (cadj.homEquiv _ _).symm (uliftIntHom x)
  have hτ' : τ' ≫ (etaleAbelianDirectImage.{u, u + 1} U.hom).map (F.map S.g) =
      σ ≫ adj.unit.app S.X₃ := by
    apply (cadj.homEquiv _ _).injective
    rw [cadj.homEquiv_naturality_right, cadj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    refine ulift_int_hom_ext ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact (congrArg _ (uliftIntHom_apply_one x)).trans
      (inverseImage_map_bcDiagonal_unit_eq S.g U t _ ht)
  have hfac : F.map σ = (adj.homEquiv _ _).symm τ' ≫ F.map S.g := by
    rw [← adj.homEquiv_naturality_right_symm, hτ', adj.homEquiv_naturality_left_symm,
      adj.homEquiv_symm_unit, Category.comp_id]
  rw [etaleCohomologyRestrictionMap_comp_extClass.{u, u + 1, u + 1} U.hom hS 0 1 (zero_add 1),
    etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, hfac,
    ← Category.assoc, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    show (Ext.mk₀ (F.map S.g)).comp (hS.map_of_exact F).extClass (zero_add 1) = 0 from
      (hS.map_of_exact F).comp_extClass, Ext.comp_zero]

end Stacks.EtaleCohomology

end
