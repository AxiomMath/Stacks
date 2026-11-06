module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGenerated

/-!
# Essential smallness of the cardinally generated modules on a ringed space

For a ringed space and a cardinal `κ`, the sheaves of modules generated locally by at most `κ`
sections form an essentially small class: there is a set of such modules meeting every
isomorphism class.

## Main results

* `AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated`: the `κ`-generated
  sheaves of modules on a ringed space form an essentially small class.

## Implementation notes

The set of representatives of the source is expressed here as essential smallness of an
`ObjectProperty`. The bound lives in a universe containing both the underlying space and the
coefficient rings, so that the carrier and coefficient universes stay independent; for the same
reason the sheafification and locally-bijective instances for the slice sites, and the
preservation of sheaves by the forgetful functor from commutative rings to rings, are taken as
explicit hypotheses rather than derived.

The proof splits on whether the lattice of opens is small. If it is, a single universal object
`cardinalUniversalSource` admits an epimorphism onto every `κ`-generated module — it is the
coproduct of `κ` copies, one for each open, of the sheafification of the free module on the
representable presheaf of that open — and the quotients of a fixed object in a well-powered
abelian category form an essentially small class. If the lattice of opens is not small, then
`Cardinal` itself is small in the larger universe, and the whole category of presheaves of
modules is essentially small, so no selection is needed.

The proof of the source does not use that `κ` is infinite, so the statement is made for every
cardinal.

## References

* [Stacks Project, Tag 077M](https://stacks.math.columbia.edu/tag/077M)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.CardinalGenerated

universe w o h s

private theorem essentiallySmall_epiImages
    {C : Type o} [Category.{h, o} C] [Abelian C]
    [LocallySmall.{s} C] [WellPowered.{s} C] (G : C) :
    ObjectProperty.EssentiallySmall.{s}
      (fun M : C ↦ ∃ f : G ⟶ M, Epi f) := by
  classical
  let Q : ObjectProperty C :=
    .ofObj (fun s : Subobject (Opposite.op G) ↦ (s : Cᵒᵖ).unop)
  have hQ : ObjectProperty.Small.{s} Q := by
    dsimp [Q]
    infer_instance
  refine ⟨Q, hQ, ?_⟩
  intro M ⟨f, hf⟩
  let : Epi f := hf
  let s : Subobject (Opposite.op G) := Subobject.mk f.op
  exact ⟨(s : Cᵒᵖ).unop,
    ObjectProperty.ofObj_apply _ s,
    ⟨(Subobject.underlyingIso f.op).unop⟩⟩

private theorem hom_ext_of_over_cover
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type u} (U : I → C) (hU : J.CoversTop U)
    (a b : M ⟶ N)
    (h : ∀ i, a.over (U i) = b.over (U i)) : a = b := by
  apply (SheafOfModules.toSheaf R).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply N.isSheaf.hom_ext ⟨Sieve.ofObjects U V.unop, hU V.unop⟩
  rintro ⟨W, k, ⟨i, ⟨l⟩⟩⟩
  have hi : a.val.app (Opposite.op W) = b.val.app (Opposite.op W) :=
    congrArg (fun f : M.over (U i) ⟶ N.over (U i) => f.val.app (Opposite.op (Over.mk l))) (h i)
  have hi' : ((SheafOfModules.toSheaf R).map a).hom.app (Opposite.op W) =
      ((SheafOfModules.toSheaf R).map b).hom.app (Opposite.op W) := by
    ext x
    exact congrArg (fun f => f x) hi
  show ((SheafOfModules.toSheaf R).map a).hom.app V ≫
      ((SheafOfModules.toSheaf R).obj N).obj.map k.op =
    ((SheafOfModules.toSheaf R).map b).hom.app V ≫
      ((SheafOfModules.toSheaf R).obj N).obj.map k.op
  calc
    _ = ((SheafOfModules.toSheaf R).obj M).obj.map k.op ≫
        ((SheafOfModules.toSheaf R).map a).hom.app (Opposite.op W) :=
      (((SheafOfModules.toSheaf R).map a).hom.naturality k.op).symm
    _ = ((SheafOfModules.toSheaf R).obj M).obj.map k.op ≫
        ((SheafOfModules.toSheaf R).map b).hom.app (Opposite.op W) := by rw [hi']
    _ = _ := ((SheafOfModules.toSheaf R).map b).hom.naturality k.op

private theorem sectionsMap_over_eq_of_eval_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (U : C) (s : (M.over U).sections) (a b : M ⟶ N)
    (h : (a.over U).val.app (Opposite.op (Over.mk (𝟙 U)))
          (s.eval (Opposite.op (Over.mk (𝟙 U)))) =
        (b.over U).val.app (Opposite.op (Over.mk (𝟙 U)))
          (s.eval (Opposite.op (Over.mk (𝟙 U))))) :
    SheafOfModules.sectionsMap (a.over U) s =
      SheafOfModules.sectionsMap (b.over U) s := by
  apply PresheafOfModules.sections_ext
  intro T
  let k : T.unop ⟶ Over.mk (𝟙 U) := Over.homMk T.unop.hom (by simp)
  have hs' : (M.over U).val.map k.op
      (s.eval (Opposite.op (Over.mk (𝟙 U)))) = s.eval T := by
    simpa only [Opposite.op_unop] using PresheafOfModules.sections_property s (f := k.op)
  show (a.over U).val.app T (s.eval T) = (b.over U).val.app T (s.eval T)
  rw [← hs', PresheafOfModules.naturality_apply (a.over U).val k.op,
    PresheafOfModules.naturality_apply (b.over U).val k.op]
  exact congrArg (fun x => (N.over U).val.map k.op x) h

private theorem over_eq_of_generating_eval_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (U : C) (σ : (M.over U).GeneratingSections) (a b : M ⟶ N)
    (h : ∀ i : σ.I,
      (a.over U).val.app (Opposite.op (Over.mk (𝟙 U)))
          ((σ.s i).eval (Opposite.op (Over.mk (𝟙 U)))) =
        (b.over U).val.app (Opposite.op (Over.mk (𝟙 U)))
          ((σ.s i).eval (Opposite.op (Over.mk (𝟙 U))))) :
    a.over U = b.over U := by
  refine (cancel_epi σ.π).mp ?_
  apply (N.over U).freeHomEquiv.injective
  funext i
  simpa only [SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply] using
    sectionsMap_over_eq_of_eval_eq U (σ.s i) a b (h i)

private theorem overMap_app_id
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    (f : M ⟶ N) (U : C) (x : M.val.obj (Opposite.op U)) :
    (f.over U).val.app (Opposite.op (Over.mk (𝟙 U))) x =
      f.val.app (Opposite.op U) x := rfl

private noncomputable def opensYoneda {C : Type u} [Preorder C] (U : C) :
    Cᵒᵖ ⥤ Type w where
  obj V := ULift.{w, 0} (PLift (V.unop ≤ U))
  map := fun {V W} f => ↾fun x =>
    ⟨⟨le_trans (leOfHom f.unop) x.down.down⟩⟩
  map_id := by
    intro V
    ext x
    exact Subsingleton.elim _ _
  map_comp := by
    intro V W Z f g
    ext x
    exact Subsingleton.elim _ _

private noncomputable def opensYonedaEquiv {C : Type u} [Preorder C]
    {F : Cᵒᵖ ⥤ Type w} (U : C) : (opensYoneda U ⟶ F) ≃ F.obj (Opposite.op U) where
  toFun f := f.app (Opposite.op U) ⟨⟨le_rfl⟩⟩
  invFun x :=
    { app := fun V => ↾fun a => F.map (homOfLE a.down.down).op x
      naturality := by
        intro V W f
        ext a
        let k := (homOfLE a.down.down).op
        let k' := (homOfLE (le_trans (leOfHom f.unop) a.down.down)).op
        have hk : k' = k ≫ f := by apply Subsingleton.elim
        have hmap : F.map k' = F.map k ≫ F.map f := by
          rw [hk, Functor.map_comp]
        exact ConcreteCategory.congr_hom hmap x }
  left_inv f := by
    ext V a
    cases V
    obtain ⟨⟨a⟩⟩ := a
    have hv := ConcreteCategory.congr_hom (f.naturality (homOfLE a).op) ⟨⟨le_rfl⟩⟩
    have hp : (opensYoneda U).map (homOfLE a).op ⟨⟨le_rfl⟩⟩ = ⟨⟨a⟩⟩ := by
      unfold opensYoneda
      apply congrArg ULift.up
      apply congrArg PLift.up
      apply Subsingleton.elim
    change F.map (homOfLE a).op
        (f.app (Opposite.op U) ⟨⟨le_rfl⟩⟩) =
      f.app _ ⟨⟨a⟩⟩
    rw [← hp]
    exact hv.symm
  right_inv x := by
    dsimp
    simp

private noncomputable def freeOpensYonedaLift
    {C : Type u} [Preorder C] {R : Cᵒᵖ ⥤ RingCat.{w}} (U : C) :
    PresheafOfModules.{w} R :=
  (PresheafOfModules.free.{w} R).obj (opensYoneda U)

private noncomputable def freeOpensYonedaEquiv
    {C : Type u} [Preorder C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M : PresheafOfModules.{w} R} (U : C) :
    (freeOpensYonedaLift U ⟶ M) ≃ M.obj (Opposite.op U) :=
  PresheafOfModules.freeHomEquiv.trans (opensYonedaEquiv U)

private theorem freeOpensYonedaEquiv_comp
    {C : Type u} [Preorder C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M N : PresheafOfModules.{w} R}
    (U : C) (f : freeOpensYonedaLift (R := R) U ⟶ M) (a : M ⟶ N) :
    freeOpensYonedaEquiv (M := N) U (f ≫ a) =
      a.app (Opposite.op U) (freeOpensYonedaEquiv (M := M) U f) :=
  rfl

/-- Transposing a section along the sheafification adjunction and back recovers it. -/
private theorem freeOpensYonedaEquiv_sheafificationHomEquiv_symm
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (U : C) (x : M.val.obj (Opposite.op U)) :
    freeOpensYonedaEquiv (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) U
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
          ((freeOpensYonedaEquiv
            (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) U).symm x))) = x := by
  refine (congrArg _ (Equiv.apply_symm_apply _ _)).trans ?_
  exact Equiv.apply_symm_apply _ x

/-- The section of a sheaf corresponding to a morphism out of a sheafified free module is
natural in the target. -/
private theorem freeOpensYonedaEquiv_sheafificationHomEquiv_comp
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (U : C) (f : (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj
      (freeOpensYonedaLift (R := R.obj) U) ⟶ M) (a : M ⟶ N) :
    freeOpensYonedaEquiv (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj N.val) U
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (f ≫ a)) =
    a.val.app (Opposite.op U) (freeOpensYonedaEquiv
      (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) U
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f)) := by
  rw [← PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  exact freeOpensYonedaEquiv_comp U _ _

private instance hasCoproductsOfShape_presheafOfModules_prod
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (κ : Cardinal.{w}) [Small.{w} C] :
    Limits.HasColimitsOfShape (Discrete (C × κ.out)) (PresheafOfModules.{w} R.obj) :=
  haveI : Limits.HasColimitsOfShape (Discrete (Shrink.{w} (C × κ.out))) AddCommGrpCat.{w} :=
    inferInstance
  haveI : Limits.HasColimitsOfShape (Discrete (Shrink.{w} (C × κ.out)))
      (PresheafOfModules.{w} R.obj) := PresheafOfModules.hasColimitsOfShape _ _
  Limits.hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} (C × κ.out)).symm)

private instance hasCoproductsOfShape_sheafOfModules_prod
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (κ : Cardinal.{w}) [Small.{w} C]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    Limits.HasColimitsOfShape (Discrete (C × κ.out)) (SheafOfModules.{w} R) where
  has_colimit F :=
    haveI : Limits.HasColimit (F ⋙ SheafOfModules.forget R) := inferInstance
    haveI : IsIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit := inferInstance
    haveI : Limits.PreservesColimitsOfSize.{max u w, max u w}
        (PresheafOfModules.sheafification.{w} (𝟙 R.obj)) :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits
    haveI : Limits.HasColimit ((F ⋙ SheafOfModules.forget R) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)) :=
      ⟨⟨_, Limits.isColimitOfPreserves _ (Limits.colimit.isColimit _)⟩⟩
    Limits.hasColimit_of_iso
      (F := (F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
      (Functor.isoWhiskerLeft F
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm :
        F ≅ (F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj))

private noncomputable abbrev cardinalUniversalSource
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (κ : Cardinal.{w})
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Small.{w} C] :
    SheafOfModules.{w} R :=
  ∐ fun p : C × κ.out ↦
    (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj
      (freeOpensYonedaLift (R := R.obj) p.1)

private noncomputable def cardinalUniversalMap
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    [Small.{w} C]
    (κ : Cardinal.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (t : ∀ U : C, κ.out → M.val.obj (Opposite.op U)) :
    cardinalUniversalSource R κ ⟶ M :=
  Limits.Sigma.desc fun p ↦
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
      ((freeOpensYonedaEquiv (M := M.val) p.1).symm (t p.1 p.2))

private theorem cardinalUniversalMap_component
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    [Small.{w} C]
    (κ : Cardinal.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (t : ∀ U : C, κ.out → M.val.obj (Opposite.op U)) (U : C) (n : κ.out) :
    freeOpensYonedaEquiv
      (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) U
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        (Limits.Sigma.ι
          (fun p : C × κ.out ↦
            (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj
              (freeOpensYonedaLift (R := R.obj) p.1))
          (U, n) ≫ cardinalUniversalMap M κ t)) = t U n := by
  unfold cardinalUniversalMap
  rw [Limits.Sigma.ι_desc]
  exact freeOpensYonedaEquiv_sheafificationHomEquiv_symm U (t U n)

private theorem cardinalUniversalMap_component_comp
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R}
    [Small.{w} C]
    (κ : Cardinal.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (t : ∀ U : C, κ.out → M.val.obj (Opposite.op U))
    (a : M ⟶ N) (U : C) (n : κ.out) :
    freeOpensYonedaEquiv (M := N.val) U
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        ((Limits.Sigma.ι
          (fun p : C × κ.out ↦
              (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj
                (freeOpensYonedaLift (R := R.obj) p.1))
          (U, n) ≫ cardinalUniversalMap M κ t) ≫ a)) =
      a.val.app (Opposite.op U) (t U n) := by
  exact (freeOpensYonedaEquiv_sheafificationHomEquiv_comp U _ a).trans
    (congrArg (a.val.app (Opposite.op U)) (cardinalUniversalMap_component M κ t U n))

private theorem cardinalUniversalMap_epi
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    [Small.{w} C]
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (σ : M.LocalGeneratorsData.{u})
    (κ : Cardinal.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (t : ∀ U : C, κ.out → M.val.obj (Opposite.op U))
    (ht : ∀ i : σ.I, ∀ j : (σ.generators i).I,
      ∃ n, t (σ.X i) n =
        ((σ.generators i).s j).eval (Opposite.op (Over.mk (𝟙 (σ.X i))))) :
    Epi (cardinalUniversalMap M κ t) := by
  constructor
  intro N a b hab
  apply hom_ext_of_over_cover σ.X σ.coversTop a b
  intro i
  apply over_eq_of_generating_eval_eq (σ.X i) (σ.generators i) a b
  intro j
  obtain ⟨n, hn⟩ := ht i j
  let ι :
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (freeOpensYonedaLift (R := R.obj) (σ.X i)) ⟶
      cardinalUniversalSource R κ :=
    Limits.Sigma.ι
      (fun p : C × κ.out ↦
        (PresheafOfModules.sheafification (𝟙 R.obj)).obj
          (freeOpensYonedaLift (R := R.obj) p.1))
      (σ.X i, n)
  have hcomp : (ι ≫ cardinalUniversalMap M κ t) ≫ a =
      (ι ≫ cardinalUniversalMap M κ t) ≫ b := by
    simpa only [Category.assoc] using congrArg (fun f => ι ≫ f) hab
  have he' : a.val.app (Opposite.op (σ.X i)) (t (σ.X i) n) =
      b.val.app (Opposite.op (σ.X i)) (t (σ.X i) n) :=
    (cardinalUniversalMap_component_comp κ t a (σ.X i) n).symm.trans
      ((congrArg (fun f => freeOpensYonedaEquiv (σ.X i)
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f)) hcomp).trans
        (cardinalUniversalMap_component_comp κ t b (σ.X i) n))
  show (a.over (σ.X i)).val.app (Opposite.op (Over.mk (𝟙 (σ.X i))))
      (((σ.generators i).s j).eval (Opposite.op (Over.mk (𝟙 (σ.X i))))) =
    (b.over (σ.X i)).val.app (Opposite.op (Over.mk (𝟙 (σ.X i))))
      (((σ.generators i).s j).eval (Opposite.op (Over.mk (𝟙 (σ.X i)))))
  rw [hn] at he'
  have hfa := overMap_app_id a (σ.X i)
    (((σ.generators i).s j).eval (Opposite.op (Over.mk (𝟙 (σ.X i)))))
  have hfb := overMap_app_id b (σ.X i)
    (((σ.generators i).s j).eval (Opposite.op (Over.mk (𝟙 (σ.X i)))))
  exact hfa.trans (he'.trans hfb.symm)

private theorem dependent_extension_of_injective
    {α β : Type u} (f : α → β) (hf : Function.Injective f)
    (γ : β → Type v) [∀ b, Inhabited (γ b)] (g : ∀ a, γ (f a)) :
    ∃ h : ∀ b, γ b, ∀ a, h (f a) = g a := by
  classical
  let h : ∀ b, γ b := fun b ↦
    if h : ∃ a, f a = b then
      (Classical.choose_spec h) ▸ g (Classical.choose h)
    else default
  refine ⟨h, fun a => ?_⟩
  dsimp [h]
  split_ifs with he
  · have ha : Classical.choose he = a := hf (Classical.choose_spec he)
    have transport {x y : α} (e : x = y) :
        (congrArg f e) ▸ g x = g y := by cases e; rfl
    exact transport ha
  · exact (he ⟨a, rfl⟩).elim

private theorem cardinalGenerated_has_universal_epimorphism
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (κ : Cardinal.{w})
    [∀ U : C, HasWeakSheafify ((J.over U)) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Small.{w} C]
    (hM : ∃ σ : M.LocalGeneratorsData.{u}, ∀ i, Cardinal.mk (σ.generators i).I ≤ κ) :
    ∃ f : cardinalUniversalSource R κ ⟶ M, Epi f := by
  classical
  obtain ⟨σ, hσ⟩ := hM
  let τ := σ.shrink
  have hτX (i : τ.I) : τ.X i = i.1 := Classical.choose_spec i.2
  have hτinj : Function.Injective τ.X := fun i j hij =>
    Subtype.ext ((hτX i).symm.trans (hij.trans (hτX j)))
  let e (i : τ.I) : (τ.generators i).I ↪ κ.out := by
    have hc : Cardinal.mk (τ.generators i).I ≤ Cardinal.mk κ.out := by
      rw [Cardinal.mk_out]
      exact hσ (Classical.choose i.2)
    exact ((Cardinal.le_def _ _).mp hc).some
  let g (i : τ.I) : κ.out → M.val.obj (Opposite.op (τ.X i)) := fun k =>
    if hk : ∃ j, e i j = k then
      ((τ.generators i).s (Classical.choose hk)).eval
        (Opposite.op (Over.mk (𝟙 (τ.X i))))
    else 0
  let : ∀ U : C, Inhabited (κ.out → M.val.obj (Opposite.op U)) :=
    fun _ => ⟨fun _ => 0⟩
  obtain ⟨t, ht⟩ := dependent_extension_of_injective τ.X hτinj
    (fun U => κ.out → M.val.obj (Opposite.op U)) g
  exact ⟨cardinalUniversalMap M κ t,
    cardinalUniversalMap_epi M τ κ t (fun i j => by
      refine ⟨e i j, ?_⟩
      rw [congrFun (ht i) (e i j)]
      have hk : ∃ j' : (τ.generators i).I, e i j' = e i j := ⟨j, rfl⟩
      have hchoose : Classical.choose hk = j :=
        (e i).injective (Classical.choose_spec hk)
      show (if h : ∃ j', e i j' = e i j then
          ((τ.generators i).s (Classical.choose h)).eval
            (Opposite.op (Over.mk (𝟙 (τ.X i)))) else 0) = _
      rw [dite_eq_left ⟨j, rfl⟩, hchoose])⟩


private theorem wellPowered_sheaf
    {C : Type u} [Preorder C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    WellPowered.{max u w} (SheafOfModules.{w} R) := by
  let F : C → SheafOfModules.{w} R := fun U =>
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (freeOpensYonedaLift U)
  apply wellPowered_of_isDetecting (𝒢 := .ofObj F)
  apply ObjectProperty.IsSeparating.isDetecting
  intro M N a b h
  apply (SheafOfModules.forget R).map_injective
  ext U x
  let g : F U.unop ⟶ M :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
      ((freeOpensYonedaEquiv U.unop).symm x)
  have hg := h (F U.unop) (ObjectProperty.ofObj_apply F U.unop) g
  have hh := congrArg (fun f => freeOpensYonedaEquiv
    (M := (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj N.val) U.unop
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f)) hg
  simp only [freeOpensYonedaEquiv_sheafificationHomEquiv_comp, g] at hh
  have hx := freeOpensYonedaEquiv_sheafificationHomEquiv_symm (M := M) U.unop x
  exact (congrArg (fun z => a.val.app U z) hx).symm.trans
    (hh.trans (congrArg (fun z => b.val.app U z) hx))

/-- If a type in `Type u` is not `v`-small, then every `v`-cardinal is bounded by its
cardinality, so `Cardinal.{v}` is `max u v`-small. -/
public theorem small_cardinal_of_not_small (α : Type u) (h : ¬ Small.{v} α) :
    Small.{max u v} Cardinal.{v} := by
  have hc (c : Cardinal.{v}) : Cardinal.lift.{u} c < Cardinal.lift.{v} (Cardinal.mk α) := by
    apply lt_of_not_ge
    intro hc
    have he : Nonempty (α ↪ c.out) := by
      apply Cardinal.lift_mk_le'.mp
      simpa only [Cardinal.mk_out] using hc
    exact h (small_of_injective he.some.injective)
  exact small_of_injective (f := fun c : Cardinal.{v} =>
    (⟨Cardinal.lift.{u} c, hc c⟩ : Set.Iio (Cardinal.lift.{v} (Cardinal.mk α))))
    (fun a b h => Cardinal.lift_injective (congrArg Subtype.val h))

/-- If `Cardinal.{v}` is `w`-small, then the modules over a ring `R : Type v` admit a `w`-small
family of objects meeting every isomorphism class. -/
theorem module_representatives (R : Type v) [Ring R]
    [Small.{w} Cardinal.{v}] [UnivLE.{v, w}] :
    ∃ (Q : ObjectProperty (ModuleCat.{v} R)),
      ObjectProperty.Small.{w} Q ∧ ∀ M, Q.isoClosure M := by
  classical
  let T := Σ c : Cardinal.{v}, Σ g : AddCommGroup c.out, @Module R c.out _ g.toAddCommMonoid
  let F : T → ModuleCat.{v} R := fun t => @ModuleCat.of R _ t.1.out t.2.1 t.2.2
  refine ⟨.ofObj F, inferInstance, ?_⟩
  intro M
  let e : (Cardinal.mk M).out ≃ M := Cardinal.outMkEquiv
  let g := e.addCommGroup
  let := g
  let e' := e.addEquiv
  let m := e'.module R
  exact ⟨F ⟨Cardinal.mk M, g, m⟩, ObjectProperty.ofObj_apply F _,
    ⟨(e'.linearEquiv R).toModuleIso.symm⟩⟩

/-- The presheaves of `R`-modules with a prescribed module of sections `O U` over every object
`U` form a `max u v`-small type. -/
theorem small_presheaf_fixedObjects {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{v}) (O : ∀ U, ModuleCat.{v} (R.obj U)) :
    Small.{max u v} {M : PresheafOfModules.{v} R // M.obj = O} := by
  let f : {M : PresheafOfModules.{v} R // M.obj = O} →
      (∀ (U V : Cᵒᵖ) (g : U ⟶ V),
        O U ⟶ (ModuleCat.restrictScalars (R.map g).hom).obj (O V)) :=
    fun M => M.2 ▸ (fun U V g => M.1.map (X := U) (Y := V) g)
  apply small_of_injective (f := f)
  rintro ⟨⟨o, m, hi, hc⟩, h⟩ ⟨⟨o', m', hi', hc'⟩, h'⟩ he
  dsimp at h h'
  subst o o'
  apply Subtype.ext
  have hm : @m = @m' := by
    funext U V g
    exact congrFun (congrFun (congrFun he U) V) g
  cases hm
  rfl

/-- If `Cardinal.{v}` is `max u v`-small, then the category of presheaves of modules over a
presheaf of rings `R` on a category `C : Type u` is essentially `max u v`-small. -/
theorem essentiallySmall_presheaf_of_small_cardinal
    {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    [Small.{max u v} Cardinal.{v}] :
    ObjectProperty.EssentiallySmall.{max u v}
      (⊤ : ObjectProperty (PresheafOfModules.{v} R)) := by
  classical
  choose Q hQ hcover using fun U : Cᵒᵖ => module_representatives (R.obj U)
  let := hQ
  let T := Σ O : (∀ U, Subtype (Q U)),
    {M : PresheafOfModules.{v} R // M.obj = fun U => (O U).val}
  have : ∀ O : (∀ U, Subtype (Q U)),
      Small.{max u v} {M : PresheafOfModules.{v} R // M.obj = fun U => (O U).val} :=
    fun O => small_presheaf_fixedObjects R _
  refine ⟨.ofObj (fun t : T => t.2.1), inferInstance, ?_⟩
  intro M _
  choose N hN e using fun U => hcover U (M.obj U)
  let e (U) : N U ≅ M.obj U := (e U).some.symm
  let P : PresheafOfModules.{v} R := {
    obj := N
    map := fun {U V} f =>
      (e U).hom ≫ M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (e V).inv
    map_id := by
      intro U
      ext x
      show (e U).inv (M.map (𝟙 U) ((e U).hom x)) = x
      have h := CategoryTheory.congr_fun (M.map_id U) ((e U).hom x)
      change M.map (𝟙 U) ((e U).hom x) = (e U).hom x at h
      rw [h]
      exact CategoryTheory.congr_fun (e U).hom_inv_id x
    map_comp := by
      intro U V W f g
      ext x
      show (e W).inv (M.map (f ≫ g) ((e U).hom x)) =
        (e W).inv (M.map g ((e V).hom ((e V).inv (M.map f ((e U).hom x)))))
      rw [M.map_comp_apply]
      have h := CategoryTheory.congr_fun (e V).inv_hom_id (M.map f ((e U).hom x))
      change (e V).hom ((e V).inv _) = _ at h
      rw [h]
      rfl }
  have ep : P ≅ M := PresheafOfModules.isoMk e (by
    intro U V f
    ext x
    show (e V).hom ((e V).inv (M.map f ((e U).hom x))) = M.map f ((e U).hom x)
    exact CategoryTheory.congr_fun (e V).inv_hom_id _)
  exact ⟨P, ObjectProperty.ofObj_apply (fun t : T => t.2.1)
    ⟨fun U => ⟨N U, hN U⟩, P, rfl⟩, ⟨ep.symm⟩⟩


/-- The `κ`-generated modules on a ringed space have a set of isomorphism
classes. -/
@[stacks 077M]
theorem essentiallySmall_isCardinalGenerated (X : RingedSpace.{v, u})
    (κ : Cardinal.{v})
    [∀ U : Opens X, HasWeakSheafify
        ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{v}]
    [∀ U : Opens X,
        ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
          AddCommGrpCat.{v}]
    [(Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ CommRingCat.{v} RingCat.{v})] :
    ObjectProperty.EssentiallySmall.{max u v}
      (fun M : SheafOfModules.{v}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{v} RingCat.{v})).obj X.sheaf) ↦
        SheafOfModules.IsCardinalGenerated M κ) := by
  classical
  let R : Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{v} RingCat.{v})).obj X.sheaf
  show ObjectProperty.EssentiallySmall.{max u v}
    (fun M : SheafOfModules.{v} R ↦ SheafOfModules.IsCardinalGenerated M κ)
  by_cases h : Small.{v} (Opens X)
  · let := h
    let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
      hasSheafifyEssentiallySmallSite.{u, v, u, v + 1, v} _ _
    let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{v} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, v, u, v + 1, v} _
    let : WellPowered.{max u v} (SheafOfModules.{v} R) := wellPowered_sheaf R
    let : ObjectProperty.EssentiallySmall.{max u v}
        (fun M : SheafOfModules.{v} R ↦
          ∃ f : cardinalUniversalSource R κ ⟶ M, Epi f) :=
      essentiallySmall_epiImages.{max u (v + 1), max u v, max u v}
        (cardinalUniversalSource R κ)
    exact ObjectProperty.EssentiallySmall.of_le
      (Q := fun M : SheafOfModules.{v} R ↦ ∃ f : cardinalUniversalSource R κ ⟶ M, Epi f)
      fun M hM => cardinalGenerated_has_universal_epimorphism M κ hM
  · let := small_cardinal_of_not_small (Opens X) h
    let := essentiallySmall_presheaf_of_small_cardinal R.obj
    let : EssentiallySmall.{max u v} (PresheafOfModules.{v} R.obj) :=
      (essentiallySmall_iff_objectPropertyEssentiallySmall_top _).mpr inferInstance
    let : EssentiallySmall.{max u v} (SheafOfModules.{v} R) :=
      essentiallySmall_of_fully_faithful (SheafOfModules.forget R)
    exact ObjectProperty.EssentiallySmall.of_le (show
      (fun M : SheafOfModules.{v} R ↦ SheafOfModules.IsCardinalGenerated M κ) ≤ ⊤ from le_top)

end AlgebraicGeometry.CardinalGenerated
