module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sheaves.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a constant sheaf on an irreducible space

Let `X` be an irreducible topological space and `A` an abelian group. Then the constant sheaf
`A` on `X` has vanishing cohomology in every positive degree: `H^p(X, A) = 0` for all `p > 0`.

## Main definitions

* `Stacks.CohomologyVanishing.irreducibleConstantModel`: the presheaf with value `A` on every
  nonempty open and zero on the empty open.
* `Stacks.CohomologyVanishing.irreducibleConstantModelSheaf`: that presheaf as a sheaf, on a space
  in which any two nonempty opens meet.
* `Stacks.CohomologyVanishing.constantToIrreducibleModel`,
  `Stacks.CohomologyVanishing.irreducibleConstantModelEval`,
  `Stacks.CohomologyVanishing.irreducibleConstantModelExtend`: the comparison with the constant
  presheaf, the value of a section over a nonempty open, and the extension of a morphism out of the
  constant presheaf.
* `Stacks.CohomologyVanishing.constantSheafIsoIrreducibleModel`: the identification of the constant
  sheaf with value `A` with that sheaf.

## Main results

* `Stacks.CohomologyVanishing.subsingleton_sheafH_constantSheaf_of_irreducibleSpace`: higher
  cohomology of a constant abelian sheaf on an irreducible space vanishes.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant abelian
sheaf `ℤ` on the site of opens, and vanishing is expressed as `Subsingleton`, matching
`AboveTheDimension.lean` and `NoetherianSpaces.lean`. The constant sheaf is Mathlib's
`CategoryTheory.constantSheaf`, the sheafification of the constant presheaf. The `HasSheafify`
and `HasExt` assumptions are the data those two constructions presuppose, so they cannot be
built inside the proof of a statement that already mentions them; `HasExt.standard` supplies
the second one.

*The explicit model.* On an irreducible space the constant presheaf is a sheaf away from the
empty open, since any two nonempty opens meet. The sheafification is therefore the presheaf
`U ↦ A` for `U` nonempty and `U ↦ 0` for `U = ∅`, which is `irreducibleConstantModel` below;
`constantSheafIsoIrreducibleModel` is that identification.

*Injectivity for divisible values.* A map into the model is a compatible family of maps
`F(U) → A` indexed by the nonempty opens, which are cofiltered, so maps into the model are maps
out of a filtered colimit of sections. Filtered colimits of abelian groups are exact, hence the
model with a divisible — equivalently injective — value is an injective presheaf, and so an
injective sheaf because sheafification is exact.

*The general case.* Embedding `A` in a divisible group `B` with divisible quotient `B/A` gives,
after applying the exact functor `constantSheaf`, a short exact sequence of abelian sheaves whose
second and third terms are injective. The long exact sequence then kills `H^p` for `p ≥ 2`
outright, and in degree one it reduces the claim to the surjectivity of
`Γ(X, B) → Γ(X, B/A)`, which holds because `constantSheaf` is surjective on sections over every
open of an irreducible space.

## References

* [Stacks Project, Tag 02UW](https://stacks.math.columbia.edu/tag/02UW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat Opposite Presheaf
open CategoryTheory.Limits

namespace Stacks.CohomologyVanishing

universe w v u

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]

/-! ### The constant presheaf extended by zero over the empty open -/

/-- The presheaf of abelian groups on `X` whose value on a nonempty open is `A` and whose value on
the empty open is zero, all restriction maps between nonempty opens being the identity. -/
def irreducibleConstantModel (X : TopCat.{u}) (A : AddCommGrpCat.{v}) :
    TopCat.Presheaf AddCommGrpCat.{v} X where
  obj V := AddCommGrpCat.of (PLift (∃ x : X, x ∈ (V.unop : Opens X)) → A)
  map {V W} f := AddCommGrpCat.ofHom {
    toFun := fun s hW => s ⟨⟨hW.down.choose, f.unop.le hW.down.choose_spec⟩⟩
    map_zero' := rfl
    map_add' _ _ := rfl }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The morphism from the constant presheaf with value `A` to `irreducibleConstantModel X A`
sending an element of `A` to the constant family with that value. -/
def constantToIrreducibleModel (X : TopCat.{u}) (A : AddCommGrpCat.{v}) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ irreducibleConstantModel X A where
  app V := AddCommGrpCat.ofHom {
    toFun := fun a _ => a
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality := by intros; rfl

/-- Over an open with no points, `irreducibleConstantModel X A` has a single section. -/
theorem subsingleton_irreducibleConstantModel_obj (X : TopCat.{u}) (A : AddCommGrpCat.{v})
    {U : Opens X} (hU : ¬∃ x : X, x ∈ U) :
    Subsingleton ((irreducibleConstantModel X A).obj (op U)) :=
  ⟨fun _ _ => by funext q; exact (hU q.down).elim⟩

/-- On a space in which any two nonempty opens meet, `irreducibleConstantModel X A` is a sheaf for
the topology of opens. -/
theorem irreducibleConstantModel_isSheaf (X : TopCat.{u}) [PreirreducibleSpace X]
    (A : AddCommGrpCat.{v}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (irreducibleConstantModel X A) := by
  classical
  intro E U S hS x hx
  by_cases hU : ∃ z : X, z ∈ U
  · obtain ⟨xU, hxU⟩ := hU
    obtain ⟨V, f, hf, hxV⟩ := by
      change ∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U), S f ∧ x ∈ V at hS
      exact hS xU hxU
    let hV : PLift (∃ z : X, z ∈ V) := ⟨⟨xU, hxV⟩⟩
    let a : E ⟶ A := AddCommGrpCat.ofHom {
      toFun := fun e => (x f hf).hom e hV
      map_zero' := congrFun (map_zero (x f hf).hom) hV
      map_add' e e' := congrFun (map_add (x f hf).hom e e') hV }
    let gl : E ⟶ (irreducibleConstantModel X A).obj (op U) := AddCommGrpCat.ofHom {
      toFun := fun e _ => a.hom e
      map_zero' := by funext h; simp
      map_add' := by intro e e'; funext h; simp }
    refine ⟨gl, ?_, ?_⟩
    · intro W g hg
      by_cases hW : ∃ z : X, z ∈ W
      · let T : Opens X := V ⊓ W
        let hTpl : PLift (∃ z : X, z ∈ T) :=
          ⟨nonempty_preirreducible_inter (X := X) V.2 W.2 ⟨xU, hxV⟩ hW⟩
        let iV : T ⟶ V := homOfLE (show T ≤ V by dsimp [T]; exact inf_le_left)
        let iW : T ⟶ W := homOfLE (show T ≤ W by dsimp [T]; exact inf_le_right)
        have hcomm := @hx V W T iV iW f g hf hg (Subsingleton.elim _ _)
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro e
        show (fun q : PLift (∃ z : X, z ∈ W) =>
          gl.hom e ⟨⟨q.down.choose, g.le q.down.choose_spec⟩⟩) = (x g hg).hom e
        funext qW
        have hpoint := congrArg
          (fun q : E ⟶ (irreducibleConstantModel X A).obj (op T) => q.hom e hTpl) hcomm
        convert hpoint using 1 <;> congr 1
      · exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ =>
          @Subsingleton.elim _ (subsingleton_irreducibleConstantModel_obj X A hW) _ _
    · intro y hy
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro e
      show (y.hom e) = (gl.hom e)
      funext qU
      have h := congrArg
        (fun q : E ⟶ (irreducibleConstantModel X A).obj (op V) => q.hom e hV) (hy f hf)
      convert h using 1 <;> congr 1
  · have hs := subsingleton_irreducibleConstantModel_obj X A hU
    refine ⟨(0 : E ⟶ (irreducibleConstantModel X A).obj (op U)), ?_, fun y _ =>
      AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ => @Subsingleton.elim _ hs _ _⟩
    intro W g _
    exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ => @Subsingleton.elim _
      (subsingleton_irreducibleConstantModel_obj X A fun ⟨z, hz⟩ => hU ⟨z, g.le hz⟩) _ _

/-- `irreducibleConstantModel X A` as a sheaf of abelian groups on a space in which any two
nonempty opens meet. -/
def irreducibleConstantModelSheaf (X : TopCat.{u}) [PreirreducibleSpace X]
    (A : AddCommGrpCat.{v}) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  ⟨irreducibleConstantModel X A, irreducibleConstantModel_isSheaf X A⟩

/-- The value in `A` of a section of `irreducibleConstantModel X A` over a nonempty open `U`,
as a morphism of abelian groups. -/
def irreducibleConstantModelEval (X : TopCat.{u}) (A : AddCommGrpCat.{v})
    (U : Opens X) (hU : ∃ x : X, x ∈ U) :
    (irreducibleConstantModel X A).obj (op U) ⟶ A := AddCommGrpCat.ofHom {
  toFun := fun s => s ⟨hU⟩
  map_zero' := rfl
  map_add' _ _ := rfl }

/-- The value of a section of `irreducibleConstantModel X A` is unchanged by restriction along the
inclusion of a nonempty open. -/
theorem irreducibleConstantModel_map_eval (X : TopCat.{u}) (A : AddCommGrpCat.{v})
    {U V : Opens X} (f : V ⟶ U) (hV : ∃ x : X, x ∈ V) :
    (irreducibleConstantModel X A).map f.op ≫ irreducibleConstantModelEval X A V hV =
      irreducibleConstantModelEval X A U ⟨hV.choose, f.le hV.choose_spec⟩ :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s => congrArg s (Subsingleton.elim _ _)

/-- The extension of a morphism `η` out of the constant presheaf with value `A` to a morphism out
of `irreducibleConstantModel X A`, into a sheaf whose value on the empty open is terminal: over a
nonempty open it is the value of the section followed by `η`, and it is zero over the empty
open. -/
noncomputable def irreducibleConstantModelExtend (X : TopCat.{u})
    (A : AddCommGrpCat.{v}) {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}}
    (hG0 : IsTerminal (G.obj.obj (op (⊥ : Opens X))))
    (η : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ G.obj) :
    irreducibleConstantModel X A ⟶ G.obj where
  app U := by
    classical
    by_cases hU : ∃ x : X, x ∈ (U.unop : Opens X)
    · exact irreducibleConstantModelEval X A U.unop hU ≫ η.app U
    · exact 0
  naturality := by
    classical
    intro U V f
    by_cases hV : ∃ x : X, x ∈ (V.unop : Opens X)
    · have hU : ∃ x : X, x ∈ (U.unop : Opens X) :=
        ⟨(f.unop ⟨hV.choose, hV.choose_spec⟩).val,
          (f.unop ⟨hV.choose, hV.choose_spec⟩).property⟩
      rw [dite_eq_left hU, dite_eq_left hV]
      change (irreducibleConstantModel X A).map f ≫
          irreducibleConstantModelEval X A V.unop hV ≫ η.app V =
        irreducibleConstantModelEval X A U.unop hU ≫ η.app U ≫ G.obj.map f
      calc
        (irreducibleConstantModel X A).map f ≫
            irreducibleConstantModelEval X A V.unop hV ≫ η.app V =
            irreducibleConstantModelEval X A U.unop hU ≫ η.app V := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ η.app V)
                (irreducibleConstantModel_map_eval X A (f.unop) hV)
        _ = irreducibleConstantModelEval X A U.unop hU ≫ η.app U ≫ G.obj.map f := by
              simpa [Category.assoc] using congrArg
                (fun q => irreducibleConstantModelEval X A U.unop hU ≫ q)
                (η.naturality f)
    · have hVbot : V.unop = ⊥ := (TopologicalSpace.Opens.not_nonempty_iff_eq_bot V.unop).mp hV
      obtain rfl : V = op (⊥ : Opens X) := by simpa using congrArg op hVbot
      exact hG0.hom_ext _ _

/-- `irreducibleConstantModelExtend X A hG0 η` restricts along `constantToIrreducibleModel X A`
to `η`. -/
theorem irreducibleConstantModelExtend_fac (X : TopCat.{u})
    (A : AddCommGrpCat.{v}) {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}}
    (hG0 : IsTerminal (G.obj.obj (op (⊥ : Opens X))))
    (η : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ G.obj) :
    constantToIrreducibleModel X A ≫ irreducibleConstantModelExtend X A hG0 η = η := by
  ext U x
  refine congrArg (fun f : A ⟶ G.obj.obj U => f.hom x) ?_
  by_cases hU : ∃ x : X, x ∈ (U.unop : Opens X)
  · let α := (constantToIrreducibleModel X A).app U
    let ev := irreducibleConstantModelEval X A U.unop hU
    have hev : α ≫ ev = 𝟙 A := by
      apply AddCommGrpCat.hom_ext
      ext a
      rfl
    have hη : α ≫ (ev ≫ η.app U) = η.app U := by
      rw [← Category.assoc, hev]
      simp
    simp only [NatTrans.comp_app]
    rw [show (irreducibleConstantModelExtend X A hG0 η).app U = ev ≫ η.app U by
      simp [irreducibleConstantModelExtend, ev, hU]]
    exact hη
  · have hUbot : U.unop = ⊥ := (TopologicalSpace.Opens.not_nonempty_iff_eq_bot U.unop).mp hU
    obtain rfl : U = op (⊥ : Opens X) := by simpa using congrArg op hUbot
    exact hG0.hom_ext _ _

/-- On a space in which any two nonempty opens meet, the constant sheaf with value `A` is
`irreducibleConstantModelSheaf X A`. -/
noncomputable def constantSheafIsoIrreducibleModel (X : TopCat.{u})
    [PreirreducibleSpace X] [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj A ≅
      irreducibleConstantModelSheaf X A := by
  let J := Opens.grothendieckTopology X
  let P := (Functor.const (Opens X)ᵒᵖ).obj A
  let Q := irreducibleConstantModelSheaf X A
  let f := constantToIrreducibleModel X A
  let c := sheafifyLift J f Q.property
  let β := irreducibleConstantModelExtend X A
    (TopCat.Sheaf.isTerminalOfEmpty ((constantSheaf J AddCommGrpCat.{v}).obj A))
    (toSheafify J P)
  let cS : (presheafToSheaf J AddCommGrpCat.{v}).obj P ⟶ Q := ⟨c⟩
  let βS : Q ⟶ (presheafToSheaf J AddCommGrpCat.{v}).obj P := ⟨β⟩
  have hc : toSheafify J P ≫ c = f := toSheafify_sheafifyLift J f Q.property
  have hβ : f ≫ β = toSheafify J P :=
    irreducibleConstantModelExtend_fac X A
      (TopCat.Sheaf.isTerminalOfEmpty ((constantSheaf J AddCommGrpCat.{v}).obj A))
      (toSheafify J P)
  have hcb : cS ≫ βS = 𝟙 _ := by
    apply CategoryTheory.Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ ((presheafToSheaf J AddCommGrpCat.{v}).obj P).property
    change toSheafify J P ≫ (c ≫ β) = toSheafify J P ≫ 𝟙 _
    rw [← Category.assoc, hc, hβ]
    rfl
  have hbc : βS ≫ cS = 𝟙 _ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    by_cases hU : ∃ x : X, x ∈ U.unop
    · let ev := irreducibleConstantModelEval X A U.unop hU
      have hβapp : β.app U s = (toSheafify J P).app U (ev.hom s) := by
        simp [β, irreducibleConstantModelExtend, ev, hU]
        rfl
      have hval' : c.app U ((toSheafify J P).app U (ev.hom s)) = f.app U (ev.hom s) := by
        simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
          congrArg (fun θ => θ.app U (ev.hom s)) hc
      change c.app U (β.app U s) = s
      rw [hβapp, hval']
      change (constantToIrreducibleModel X A).app U (ev.hom s) = s
      funext q
      change s ⟨hU⟩ = s q
      exact congrArg s (Subsingleton.elim _ _)
    · exact @Subsingleton.elim _
        (subsingleton_irreducibleConstantModel_obj X A (U := U.unop) hU) _ _
  exact ⟨cS, βS, hcb, hbc⟩

/-! ### Injectivity of the constant sheaf with divisible value -/

private abbrev NonemptyOpens (X : Type u) [TopologicalSpace X] :=
  {U : Opens X // (U : Set X).Nonempty}

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma nonemptyOpens_isCofiltered : IsCofiltered (NonemptyOpens X) where
  cone_objs U V := ⟨⟨U.1 ⊓ V.1, nonempty_preirreducible_inter U.1.2 V.1.2 U.2 V.2⟩,
    homOfLE (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left),
    homOfLE (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right), trivial⟩
  cone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
  nonempty := ⟨⟨⊤, Set.univ_nonempty⟩⟩

private def nonemptyOpensInclusion : NonemptyOpens X ⥤ Opens X :=
  (show Monotone (fun U : NonemptyOpens X => U.1) from fun _ _ h => h).functor

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private def irreducibleConstantModelLift (A : AddCommGrpCat.{v})
    {G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)}
    (b : (nonemptyOpensInclusion (X := X)).op ⋙ G ⋙ AddCommGrpCat.uliftFunctor.{u, v} ⟶
      (Functor.const _).obj (AddCommGrpCat.uliftFunctor.{u, v}.obj A)) :
    G ⟶ irreducibleConstantModel (TopCat.of X) A where
  app U := AddCommGrpCat.ofHom {
    toFun := fun s h => (b.app (op ⟨U.unop, h.down⟩) (ULift.up s)).down
    map_zero' := by
      funext h
      change (b.app (op ⟨U.unop, h.down⟩)
        (0 : AddCommGrpCat.uliftFunctor.{u, v}.obj (G.obj U))).down = 0
      exact congrArg ULift.down ((b.app (op ⟨U.unop, h.down⟩)).hom.map_zero)
    map_add' := by
      intro s t
      funext h
      change (b.app (op ⟨U.unop, h.down⟩) (ULift.up s + ULift.up t)).down = _
      exact congrArg ULift.down ((b.app (op ⟨U.unop, h.down⟩)).hom.map_add
        (ULift.up s) (ULift.up t)) }
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    funext h
    let V' : NonemptyOpens X := ⟨V.unop, h.down⟩
    let U' : NonemptyOpens X := ⟨U.unop, ⟨h.down.choose, i.unop.le h.down.choose_spec⟩⟩
    let i' : op U' ⟶ op V' := (homOfLE (show V' ≤ U' from i.unop.le)).op
    exact congrArg ULift.down (NatTrans.naturality_apply b i' (ULift.up s))

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma irreducibleConstantModel_injective (A : AddCommGrpCat.{v})
    [DivisibleBy A ℤ] : Injective (irreducibleConstantModel (TopCat.of X) A) := by
  have := nonemptyOpens_isCofiltered (X := X)
  have : AB5OfSize.{u, u} AddCommGrpCat.{max u v} := AB5OfSize_shrink _
  let e := (nonemptyOpensInclusion (X := X)).op
  let L := AddCommGrpCat.uliftFunctor.{u, v}
  have : Injective (L.obj A) := AddCommGrpCat.injective_of_divisible (ULift.{u} A)
  have : Injective ((Functor.const (NonemptyOpens X)ᵒᵖ).obj (L.obj A)) :=
    Injective.injective_of_adjoint colimConstAdj (L.obj A)
  constructor
  intro F G g f hf
  let g' : e ⋙ F ⋙ L ⟶ (Functor.const _).obj (L.obj A) := {
    app U := L.map (g.app (op U.unop.1) ≫
      irreducibleConstantModelEval (TopCat.of X) A U.unop.1 U.unop.2)
    naturality := by
      intro U V i
      ext x
      apply ULift.ext
      exact congrFun (NatTrans.naturality_apply g (e.map i) x.down) ⟨V.unop.2⟩ }
  let f' := Functor.whiskerLeft e (Functor.whiskerRight f L)
  have : Mono f' := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro U
    show Mono (L.map (f.app (e.obj U)))
    dsimp [L]
    infer_instance
  obtain ⟨b, hb⟩ := Injective.factors g' f'
  refine ⟨irreducibleConstantModelLift A b, ?_⟩
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  funext h
  exact congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app hb (op ⟨U.unop, h.down⟩)) (ULift.up s))

omit [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma constantSheaf_injective_of_divisible (A : AddCommGrpCat.{v})
    [DivisibleBy A ℤ] :
    Injective ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj A) :=
  Injective.of_iso (constantSheafIsoIrreducibleModel (TopCat.of X) A).symm
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).injective_of_map_injective
      (I := irreducibleConstantModelSheaf (TopCat.of X) A)
      (irreducibleConstantModel_injective (X := X) A))

@[instance_reducible]
private noncomputable def divisibleBy_of_injective (A : AddCommGrpCat.{v}) [Injective A] :
    DivisibleBy A ℤ := by
  apply divisibleByOfSMulRightSurj
  intro n hn a
  let f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ AddCommGrpCat.of (ULift.{v} ℤ) := AddCommGrpCat.ofHom {
      toFun := fun z => ULift.up (z.down * n)
      map_zero' := ULift.ext (by simp)
      map_add' x y := ULift.ext (by simp [add_mul]) }
  let g : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ A := AddCommGrpCat.ofHom {
      toFun := fun z => z.down • a
      map_zero' := by simp
      map_add' x y := by simp [add_zsmul] }
  have hf : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr (by
    intro x y hxy
    apply ULift.ext
    exact (mul_right_cancel₀ hn) (congrArg ULift.down hxy))
  obtain ⟨l, hl⟩ := Injective.factors g f
  refine ⟨l (ULift.up 1), ?_⟩
  have heq : l (ULift.up n) = a := by
    simpa [f, g] using congrArg (fun q : _ ⟶ A => q (ULift.up 1)) hl
  simpa only [show (ULift.up n : ULift.{v} ℤ) = n • ULift.up 1 by ext; simp,
    map_zsmul] using heq

private lemma exists_mono_divisible (A : AddCommGrpCat.{v}) :
    ∃ (B : AddCommGrpCat.{v}) (_ : DivisibleBy B ℤ) (f : A ⟶ B), Mono f := by
  let p := Classical.choice (EnoughInjectives.presentation A)
  let _ := p.injective
  exact ⟨p.J, divisibleBy_of_injective p.J, p.f, p.mono⟩

/-! ### Surjectivity of the constant sheaf on sections -/

omit [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma constantSheafIsoIrreducibleModel_unit (A : AddCommGrpCat.{v}) :
    toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
      (constantSheafIsoIrreducibleModel (TopCat.of X) A).hom.hom =
        constantToIrreducibleModel (TopCat.of X) A :=
  toSheafify_sheafifyLift _ _ _

omit [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma constantSheaf_unit_surjective (A : AddCommGrpCat.{v}) (U : Opens X) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U)) := by
  let e := constantSheafIsoIrreducibleModel (TopCat.of X) A
  have he : Function.Injective (e.hom.hom.app (op U)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro s
  let t := e.hom.hom.app (op U) s
  obtain ⟨a, ha⟩ : ∃ a : A, (constantToIrreducibleModel (TopCat.of X) A).app (op U) a = t := by
    by_cases hU : (U : Set X).Nonempty
    · exact ⟨t ⟨hU⟩, funext (fun h => congrArg t (Subsingleton.elim _ _))⟩
    · exact ⟨0, funext (fun h => (hU h.down).elim)⟩
  exact ⟨a, he <| (ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantSheafIsoIrreducibleModel_unit (X := X) A) (op U)) a).trans ha⟩

omit [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})] in
private lemma constantSheaf_map_app_surjective {A B : AddCommGrpCat.{v}} (f : A ⟶ B)
    [Epi f] (U : Opens X) :
    Function.Surjective (((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).map f).hom.app (op U)) := by
  intro s
  obtain ⟨b, rfl⟩ := constantSheaf_unit_surjective B U s
  obtain ⟨a, rfl⟩ := (AddCommGrpCat.epi_iff_surjective f).mp inferInstance b
  exact ⟨(toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U) a, (ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).map f)) (op U)) a).symm⟩

/-! ### Vanishing -/

/-- **Stacks 02UW.** Let `X` be an irreducible topological space and `A` an abelian group. Then
`H^p(X, A) = 0` for every `p > 0`, where `A` also denotes the constant sheaf with value `A`. -/
@[stacks 02UW]
theorem subsingleton_sheafH_constantSheaf_of_irreducibleSpace (A : AddCommGrpCat.{v}) (p : ℕ)
    (hp : 0 < p) :
    Subsingleton
      (Sheaf.H
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj A) p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  obtain ⟨B, hB, f, hf⟩ := exists_mono_divisible A
  let K := constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}
  have : PreservesFiniteLimits K := by
    dsimp [K, constantSheaf]
    infer_instance
  have : PreservesFiniteColimits K := by
    dsimp [K, constantSheaf]
    infer_instance
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel f⟩
  have hKS : (S.map K).ShortExact := hS.map K
  have : Injective (S.map K).X₂ := constantSheaf_injective_of_divisible (X := X) B
  have : DivisibleBy (cokernel f : AddCommGrpCat.{v}) ℤ :=
    Function.Surjective.divisibleBy (cokernel.π f).hom
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)
    (fun a n => map_zsmul (cokernel.π f).hom n a)
  have : Injective (S.map K).X₃ :=
    constantSheaf_injective_of_divisible (X := X) (cokernel f)
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hKS x
    (Abelian.Ext.eq_zero_of_injective _) (n₀ := n) rfl
  cases n with
  | zero =>
    let hT : IsTerminal (⊤ : Opens X) := isTerminalTop
    obtain ⟨b, hb⟩ := constantSheaf_map_app_surjective (X := X) (cokernel.π f) ⊤
      (Sheaf.H.equiv₀ (K.obj (cokernel f)) hT y)
    let z : Sheaf.H (K.obj B) 0 := (Sheaf.H.equiv₀ (K.obj B) hT).symm b
    have hz : Sheaf.H.map (K.map (cokernel.π f)) 0 z = y := by
      apply (Sheaf.H.equiv₀ (K.obj (cokernel f)) hT).injective
      rw [← Sheaf.H.equiv₀_naturality]
      simpa [z] using hb
    rw [← hy, ← hz]
    show (z.comp (Abelian.Ext.mk₀ (S.map K).g) (add_zero 0)).comp
      hKS.extClass (zero_add 1) = 0
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hKS.comp_extClass,
      Abelian.Ext.comp_zero]
  | succ n =>
    rw [← hy, Abelian.Ext.eq_zero_of_injective y, Abelian.Ext.zero_comp]

end Stacks.CohomologyVanishing

end
