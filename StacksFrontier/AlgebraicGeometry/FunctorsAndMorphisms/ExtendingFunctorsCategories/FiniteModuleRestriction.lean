module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Colimit.Finiteness
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Presentable.ColimitPresentation
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FiniteSubsetCoproduct

/-!
# Recognising additivity and direct sums from the finite modules

A functor out of `ModuleCat A` that preserves filtered colimits is determined on all modules by
its restriction to the finite modules, because every module is the filtered union of its finite
submodules and every pair of maps out of a finite submodule factors through a finite submodule
of the target. Consequently such a functor is additive as soon as its restriction to the finite
modules is additive.

## Main results

* `ModuleCat.additive_of_finiteModuleRestriction`: a filtered-colimit-preserving functor whose
  restriction to the finite modules is additive is additive.
* `ModuleCat.preservesCoproducts_of_finiteModuleRestriction`: such a functor preserves
  coproducts indexed by any type in the module universe.

## Implementation notes

The ring and the module universes are independent: no inequality between them is assumed, and in
particular the ring need not lie in the module universe. The filtered diagram used is the system
of finite submodules, `Module.fgSystem`, whose colimit is the whole module.

## References

* [Stacks Project, Tag 0GP6](https://stacks.math.columbia.edu/tag/0GP6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x z

namespace ModuleCat

/-- The forward direction of the comparison isomorphism for a preserved coproduct, read off on
the summand inclusions: the image of `Sigma.ι f j` followed by `PreservesCoproduct.iso G f`
is the inclusion `Sigma.ι (G ∘ f) j`.

Mathlib records only the backward direction, `PreservesCoproduct.inv_hom`, identifying the
inverse of this isomorphism with `sigmaComparison`; the forward direction is what a
cancellation chain out of `G.obj (∐ f)` needs, and deriving it by `simp` from the definition
of `PreservesCoproduct.iso` does not go. -/
private lemma map_ι_comp_preservesCoproduct_iso_hom {J : Type*} {C : Type*} {D : Type*}
    [Category C] [Category D] (G : C ⥤ D) (f : J → C) [HasCoproduct f]
    [HasCoproduct fun j => G.obj (f j)] [PreservesColimit (Discrete.functor f) G] (j : J) :
    G.map (Sigma.ι f j) ≫ (PreservesCoproduct.iso G f).hom =
      Sigma.ι (fun x => G.obj (f x)) j := by
  have h : (PreservesCoproduct.iso G f).hom = inv (sigmaComparison G f) :=
    (IsIso.inv_eq_of_hom_inv_id (PreservesCoproduct.iso G f).inv_hom_id).symm
  rw [h, map_ι_comp_inv_sigmaComparison]

/-- A filtered-colimit-preserving functor is additive if its restriction to finite modules
is additive, independently of the ring and module universes. -/
theorem additive_of_finiteModuleRestriction
    (A : Type u) [Ring A] {B : Type w} [Category.{x} B] [Preadditive B]
    (E : ModuleCat.{v} A ⥤ B) [PreservesFilteredColimitsOfSize.{v, v} E]
    [(forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E).Additive] :
    E.Additive := by
  classical
  refine ⟨?_⟩
  intro X Y f g
  let IX := {P : Submodule A X // P.FG}
  let IY := {P : Submodule A Y // P.FG}
  let GX : IX → Type v := fun i => i.1
  let GY : IY → Type v := fun i => i.1
  let fx := Module.fgSystem A X
  let fy := Module.fgSystem A Y
  have : DirectedSystem GX (fun {i j} h => fx i j h) := {
    map_self := by intro i x; dsimp [fx, Module.fgSystem]; rfl
    map_map := by intro i j k hij hjk x; dsimp [fx, Module.fgSystem]; rfl }
  have : DirectedSystem GY (fun {i j} h => fy i j h) := {
    map_self := by intro i x; dsimp [fy, Module.fgSystem]; rfl
    map_map := by intro i j k hij hjk x; dsimp [fy, Module.fgSystem]; rfl }
  let DX := ModuleCat.directLimitDiagram GX fx
  let DY := ModuleCat.directLimitDiagram GY fy
  let px : ColimitPresentation IX (ModuleCat.of A (Module.DirectLimit GX fx)) := {
    diag := DX
    ι := (ModuleCat.directLimitCocone GX fx).ι
    isColimit := ModuleCat.directLimitIsColimit GX fx }
  let py : ColimitPresentation IY (ModuleCat.of A (Module.DirectLimit GY fy)) := {
    diag := DY
    ι := (ModuleCat.directLimitCocone GY fy).ι
    isColimit := ModuleCat.directLimitIsColimit GY fy }
  let cX := px.ofIso (Module.fgSystem.equiv A X).toModuleIso
  let cY := py.ofIso (Module.fgSystem.equiv A Y).toModuleIso
  have : PreservesColimitsOfShape IX E :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits IX
  have hcX := isColimitOfPreserves E cX.isColimit
  apply hcX.hom_ext
  intro i
  let ix : cX.diag.obj i ⟶ X := cX.ι.app i
  have : Module.Finite A (cX.diag.obj i) := Module.Finite.of_fg i.property
  let q : Submodule A Y := LinearMap.range (f.hom.comp ix.hom) ⊔ LinearMap.range (g.hom.comp ix.hom)
  have hq : q.FG :=
    (Submodule.fg_range (f.hom.comp ix.hom)).sup (Submodule.fg_range (g.hom.comp ix.hom))
  let k : IY := ⟨q, hq⟩
  let yk : cY.diag.obj k ⟶ Y := cY.ι.app k
  have hqMap (z : GY k) :
      (Module.fgSystem.equiv A Y).toLinearMap
          (Module.DirectLimit.of A IY GY fy k z) = z := by
    simpa using LinearMap.congr_fun (Module.fgSystem.equiv_comp_of (R := A) (M := Y) k) z
  have lift (h : X ⟶ Y) (hle : LinearMap.range (h.hom.comp ix.hom) ≤ q) :
      ∃ a : cX.diag.obj i ⟶ cY.diag.obj k, a ≫ yk = ix ≫ h := by
    refine ⟨ModuleCat.ofHom ((h.hom.comp ix.hom).codRestrict q fun x =>
      hle (LinearMap.mem_range_self _ x)), ?_⟩
    ext x
    change (Module.fgSystem.equiv A Y).toLinearMap
      (Module.DirectLimit.of A IY GY fy k (show GY k from _)) = h.hom (ix.hom x)
    rw [hqMap]
    rfl
  obtain ⟨af, haf⟩ := lift f le_sup_left
  obtain ⟨ag, hag⟩ := lift g le_sup_right
  let X' : FGModuleCat.{v} A := ⟨cX.diag.obj i, Module.Finite.of_fg i.property⟩
  let Y' : FGModuleCat.{v} A := ⟨cY.diag.obj k, Module.Finite.of_fg hq⟩
  have hstage : E.map (af + ag) = E.map af + E.map ag :=
    (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E).map_add
      (f := show X' ⟶ Y' from ObjectProperty.homMk af)
      (g := show X' ⟶ Y' from ObjectProperty.homMk ag)
  have hfg : ix ≫ (f + g) = (af + ag) ≫ yk := by
    rw [Preadditive.comp_add, Preadditive.add_comp, haf, hag]
  change E.map ix ≫ E.map (f + g) =
    E.map ix ≫ (E.map f + E.map g)
  rw [← Functor.map_comp, hfg, Functor.map_comp, hstage, Preadditive.add_comp,
    ← Functor.map_comp, ← Functor.map_comp, haf, hag, Functor.map_comp,
    Functor.map_comp, ← Preadditive.comp_add]

-- The naturality square of `α` below compares `E` applied to the coproduct over a finite subset
-- of the index type with the coproduct of the values of `E`. The two spellings
-- `(liftToFinsetObj K).obj S` and `∐ fun x : S => K.obj x` of that object are definitionally
-- equal but not interchangeable by `rewrite`; each step that crosses the boundary is therefore
-- preceded by a `change` putting the goal in the `∐` spelling, after which
-- `map_ι_comp_preservesCoproduct_iso_hom` and `ι_comp_sigmaComparison` apply syntactically.
/-- A filtered-colimit-preserving functor whose restriction to finite modules is additive
preserves arbitrary direct sums indexed in the module universe. -/
theorem preservesCoproducts_of_finiteModuleRestriction
    (A : Type u) [Ring A] {B : Type w} [Category.{x} B] [Preadditive B]
    [HasFiniteBiproducts B]
    (E : ModuleCat.{v} A ⥤ B) [PreservesFilteredColimitsOfSize.{v, v} E]
    [(forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E).Additive]
    (J : Type v) : PreservesColimitsOfShape (Discrete J) E := by
  have : E.Additive := additive_of_finiteModuleRestriction A E
  have : ∀ (f : J → ModuleCat.{v} A),
      PreservesColimit (Discrete.functor f) E := by
    intro f
    classical
    let K : Discrete J ⥤ ModuleCat.{v} A := Discrete.functor f
    let K' : Discrete J ⥤ B := K ⋙ E
    let D := CoproductsFromFiniteFiltered.liftToFinsetObj K
    let D' := CoproductsFromFiniteFiltered.liftToFinsetObj K'
    let α : D ⋙ E ≅ D' := NatIso.ofComponents
      (fun S => PreservesCoproduct.iso E (fun x : S => K.obj x.val)) (by
      intro S T h
      refine (isColimitOfHasCoproductOfPreservesColimit E
        (fun y : S => K.obj y.val)).hom_ext fun j => ?_
      obtain ⟨x⟩ := j
      change @Eq (E.obj (K.obj x.val) ⟶ ∐ fun y : T => E.obj (K.obj y.val))
        (E.map (Sigma.ι (fun y : S => K.obj y.val) x) ≫
          E.map (Sigma.desc fun y : S =>
              Sigma.ι (fun z : T => K.obj z.val) ⟨y.val, h.down.down y.2⟩) ≫
            (PreservesCoproduct.iso E (fun y : T => K.obj y.val)).hom)
        (E.map (Sigma.ι (fun y : S => K.obj y.val) x) ≫
          (PreservesCoproduct.iso E (fun y : S => K.obj y.val)).hom ≫
            Sigma.desc fun y : S =>
              Sigma.ι (fun z : T => E.obj (K.obj z.val)) ⟨y.val, h.down.down y.2⟩)
      simp only [← Category.assoc, ← E.map_comp, Sigma.ι_comp_desc,
        map_ι_comp_preservesCoproduct_iso_hom])
    let csrc := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f
    have hcsrc : IsColimit csrc :=
      CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f
    have : IsFiltered (Finset (Discrete J)) := inferInstance
    have : PreservesColimitsOfShape (Finset (Discrete J)) E :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits (Finset (Discrete J))
    let cE := E.mapCocone csrc
    have hcE : IsColimit cE := isColimitOfPreserves E hcsrc
    let cD : Cocone D' := (Cocone.precompose α.inv).obj cE
    have hcD : IsColimit cD := (IsColimit.precomposeHomEquiv α.symm cE).2 hcE
    have : HasColimit D' := ⟨⟨cD, hcD⟩⟩
    let ctgt := Limits.finiteSubsetCoproductCocone K'
    have hctgt : IsColimit ctgt.cocone := ctgt.isColimit
    let cCoprod : Cocone K := Cofan.mk (∐ f) (Sigma.ι f)
    have hmap : IsColimit (E.mapCocone cCoprod) := by
      let e := hcD.coconePointUniqueUpToIso (colimit.isColimit D')
      apply IsColimit.ofIsoColimit hctgt
      refine Cocone.ext (show ctgt.cocone.pt ≅ (E.mapCocone cCoprod).pt from ?_) ?_
      · simpa [ctgt, Limits.finiteSubsetCoproductCocone,
          Limits.finiteSubsetCoconeOfColimit, D', cCoprod, cD, cE, csrc,
          CoproductsFromFiniteFiltered.finiteSubcoproductsCocone] using e.symm
      intro j
      have hleg : colimit.ι D' {j} ≫ e.inv = cD.ι.app {j} := by
        change (colimit.cocone D').ι.app {j} ≫ e.inv = cD.ι.app {j}
        rw [← IsColimit.comp_coconePointUniqueUpToIso_hom hcD
          (colimit.isColimit D') {j}]
        simp [e]
      change (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => K'.obj x.val)
          ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι D' {j}) ≫ e.inv =
        E.map (Sigma.ι f j.as)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z : D'.obj {j} ⟶ cD.pt =>
        Sigma.ι (fun x : ({j} : Finset (Discrete J)) => K'.obj x.val)
          ⟨j, Finset.mem_singleton_self j⟩ ≫ z) hleg).trans ?_
      -- `cD.ι.app {j}` is the inverse comparison map followed by `E` applied to the inclusion
      -- of the singleton subcoproduct; both are definitional, and spelling them out turns the
      -- remaining goal into a composite of `Sigma`-inclusions.
      change @Eq (E.obj (f j.as) ⟶ E.obj (∐ f))
        (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => E.obj (K.obj x.val))
            ⟨j, Finset.mem_singleton_self j⟩ ≫
          sigmaComparison E (fun x : ({j} : Finset (Discrete J)) => K.obj x.val) ≫
            E.map (Sigma.desc fun s : ({j} : Finset (Discrete J)) => Sigma.ι f s.val.as))
        (E.map (Sigma.ι f j.as))
      rw [← Category.assoc, ι_comp_sigmaComparison, ← E.map_comp, Sigma.ι_comp_desc]
    exact Limits.preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) hmap
  exact Limits.preservesColimitsOfShape_of_discrete E

end ModuleCat
