module

public import Mathlib.CategoryTheory.Limits.Indization.ParallelPair
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Additivity
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Extension
public import StacksCore.Tactic.StacksAttribute

/-!
# Right exactness of the extension from finitely presented modules

Let `A` be a ring and let `B` be an additive category with cokernels. A right exact functor
from finitely presented `A`-modules to `B` extends, by filtered colimits, to a functor on all
`A`-modules which is additive, right exact, and commutes with arbitrary direct sums.

## Main results

* `ModuleCat.filteredColimitExtension_preservesFiniteColimits`: the extension is right exact.
* `ModuleCat.filteredColimitExtension_additive_of_preservesFiniteColimits`: it is additive.
* `ModuleCat.filteredColimitExtension_preservesCoproducts_of_preservesFiniteColimits`: it
  commutes with arbitrary direct sums.
* `ModuleCat.filteredColimitExtension_functor_additive`,
  `ModuleCat.filteredColimitExtension_functor_preservesFiniteColimits` and
  `ModuleCat.filteredColimitExtension_functor_preservesCoproducts` are the same three
  conclusions for the extension produced by `ModuleCat.filteredColimitExtension`.

## Implementation notes

An additive category is represented by a preadditive category with finite biproducts. Right
exactness is expressed as preservation of finite colimits, and commutation with arbitrary
direct sums as preservation of colimits of diagrams indexed by a discrete category on an
arbitrary type of the size of the module category. The three conclusions apply to any
filtered-colimit extension equipped with the comparison isomorphism of
`ModuleCat.FilteredColimitExtension`, and in particular to the extension constructed by
`ModuleCat.filteredColimitExtension`, which is the one the source speaks about. Right
modules are obtained by applying the result with `Aᵐᵒᵖ`.

Additivity of the extension is read off from its right exactness: the category of all modules
has binary biproducts, so a functor out of it preserving binary coproducts and zero morphisms
is additive. Additivity of the original functor is then recovered from the comparison
isomorphism, which is what lets the commutation with arbitrary direct sums be imported from
the additive case.

The proof reduces right exactness to preservation of cokernels. A parallel pair of maps of
modules is presented as a filtered colimit of parallel pairs of finitely presented modules by
transporting an ind-object presentation of the restricted Yoneda embedding, which is where
`CategoryTheory.Limits.IndParallelPairPresentation` enters; the restricted Yoneda embedding
detects colimits because the rank-one free module corepresents the forgetful functor.

## References

* [Stacks Project, Tag 0GNL](https://stacks.math.columbia.edu/tag/0GNL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w x

namespace ModuleCat

variable (A : Type u) [Ring A]

private abbrev FPCat (A : Type u) [Ring A] := FinitelyPresentedModuleCat.{u, max u v} A

private noncomputable def regFPObj (A : Type u) [Ring A] : FPCat.{u, v} A :=
  ⟨ModuleCat.of A (ULift.{max u v} A), by
    exact Module.FinitePresentation.of_equiv
      (ULift.moduleEquiv.symm : A ≃ₗ[A] ULift.{max u v} A)⟩

private noncomputable def fpYoneda : ModuleCat.{max u v} A ⥤ (FPCat.{u, v} A)ᵒᵖ ⥤ Type (max u v) :=
  yoneda ⋙ (Functor.whiskeringLeft ((FPCat.{u, v} A)ᵒᵖ) (ModuleCat.{max u v} A)ᵒᵖ
    (Type (max u v))).obj (ObjectProperty.ι
      (finitelyPresentedModule.{u, max u v} A)).op

private def regularHomEquiv (A : Type u) [Ring A] (M : ModuleCat.{max u v} A) :
    (ModuleCat.of.{max u v} A (ULift.{max u v} A) ⟶ M) ≃ M where
  toFun f := f.hom (ULift.up 1)
  invFun m := ModuleCat.homEquiv.symm {
    toFun := fun a : ULift.{max u v} A => a.down • m
    map_add' a b := by simp [add_smul]
    map_smul' r a := smul_assoc r a.down m }
  left_inv f := by
    apply ModuleCat.homEquiv.injective
    ext a
    have ha : a = a.down • ULift.up (1 : A) := by
      apply ULift.ext
      simp
    calc
      a.down • f.hom (ULift.up (1 : A)) = f.hom (a.down • ULift.up (1 : A)) :=
        (f.hom.map_smul _ _).symm
      _ = f.hom a := congrArg f.hom ha.symm
  right_inv m := by
    change (ULift.up (1 : A) : ULift.{max u v} A).down • m = m
    simp

private noncomputable def regularCoyonedaForgetIso (A : Type u) [Ring A] :
    coyoneda.obj (Opposite.op (ModuleCat.of.{max u v} A (ULift.{max u v} A))) ≅
      forget (ModuleCat.{max u v} A) :=
  NatIso.ofComponents (fun M => (regularHomEquiv A M).toIso)
    (by
      intro M N f
      ext g
      change (regularHomEquiv A N) (g ≫ f) = f.hom ((regularHomEquiv A M) g)
      rfl)

private noncomputable def moduleColimit_of_freeCoyoneda_colimit
    (A : Type u) [Ring A] {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ ModuleCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit ((coyoneda.obj
      (Opposite.op (ModuleCat.of.{max u v} A (ULift.{max u v} A)))).mapCocone c)) :
    IsColimit c := by
  let e := regularCoyonedaForgetIso A
  let eD := Functor.isoWhiskerLeft D e
  let c' := (coyoneda.obj
    (Opposite.op (ModuleCat.of.{max u v} A (ULift.{max u v} A)))).mapCocone c
  let hc' : IsColimit ((Cocone.precompose eD.symm.hom).obj c') :=
    (IsColimit.precomposeHomEquiv eD.symm c').symm hc
  let ec : (Cocone.precompose eD.symm.hom).obj c' ≅
      (forget (ModuleCat.{max u v} A)).mapCocone c :=
    Cocone.ext (regularHomEquiv A c.pt |>.toIso) (by
      intro i
      ext x
      change (regularHomEquiv A c.pt ((eD.inv.app i) x ≫ c.ι.app i)) =
        (c.ι.app i) x
      change (c.ι.app i).hom (((eD.inv.app i) x).hom (ULift.up (1 : A))) =
        (c.ι.app i).hom x
      have hEval : ((eD.inv.app i) x).hom (ULift.up (1 : A)) = x := by
        change (((regularHomEquiv A (D.obj i)).symm x).hom
          (ULift.up (1 : A))) = x
        change (1 : A) • x = x
        simp
      rw [hEval])
  let G := D ⋙ forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}
  letI : PreservesColimit G (forget AddCommGrpCat.{max u v}) := by infer_instance
  letI : ReflectsColimit G (forget AddCommGrpCat.{max u v}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})
    (isColimitOfReflects (forget AddCommGrpCat.{max u v}) (hc'.ofIsoColimit ec))

private theorem rInd (A : Type u) [Ring A] (X : ModuleCat.{max u v} A) :
    IsIndObject ((fpYoneda.{u, v} A).obj X) := by
  obtain ⟨I, hI, hIf, p, hp⟩ := ind_finitelyPresentedModule A X
  let : SmallCategory I := hI
  let : IsFiltered I := hIf
  let P := finitelyPresentedModule.{u, max u v} A
  let D : I ⥤ FPCat.{u, v} A := P.lift p.diag hp
  let hι : D ⋙ yoneda ⟶ (Functor.const I).obj ((fpYoneda.{u, v} A).obj X) := {
    app i := {
      app Z := ↾fun g => (P.ι.map g) ≫ p.ι.app i
      naturality := by
        intro Z Z' f
        ext g
        rfl }
    naturality := by
      intro i j f
      ext Z g
      show P.ι.map (g ≫ D.map f) ≫ p.ι.app j = P.ι.map g ≫ p.ι.app i
      rw [Functor.map_comp, ObjectProperty.ι_obj_lift_map, Category.assoc, p.w f] }
  let hc : IsColimit (Cocone.mk _ hι) := by
    apply evaluationJointlyReflectsColimits
    intro Z
    let : IsFinitelyPresentable.{max u v} (P.ι.obj Z.unop) :=
      finitePresentation_isFinitelyPresentable A _ Z.unop.property
    let : PreservesFilteredColimitsOfSize.{max u v, max u v}
        (coyoneda.obj (Opposite.op (P.ι.obj Z.unop))) :=
      (isFinitelyPresentable_iff_preservesFilteredColimitsOfSize).mp inferInstance
    have hcol := isColimitOfPreserves
      (coyoneda.obj (Opposite.op (P.ι.obj Z.unop))) p.isColimit
    let e : D ⋙ yoneda ⋙ (evaluation (FPCat.{u, v} A)ᵒᵖ (Type (max u v))).obj Z ≅
        p.diag ⋙ coyoneda.obj (Opposite.op (P.ι.obj Z.unop)) := NatIso.ofComponents
      (fun i =>
        ({ toFun := fun g => P.ι.map g
           invFun := fun g => ObjectProperty.homMk g
           left_inv _ := rfl
           right_inv _ := rfl } :
          ((D ⋙ yoneda ⋙ (evaluation (FPCat.{u, v} A)ᵒᵖ (Type (max u v))).obj Z).obj i) ≃
            ((p.diag ⋙ coyoneda.obj (Opposite.op (P.ι.obj Z.unop))).obj i)).toIso)
      (by
        intro i j f
        ext g
        show P.ι.map (g ≫ D.map f) = P.ι.map g ≫ p.diag.map f
        rw [Functor.map_comp, ObjectProperty.ι_obj_lift_map])
    exact ((IsColimit.precomposeHomEquiv e
      ((coyoneda.obj (Opposite.op (P.ι.obj Z.unop))).mapCocone p.cocone)).2 hcol).ofIsoColimit
      (Cocone.ext (Iso.refl _) fun _ => by ext; rfl)
  exact IsIndObject.mk ⟨I, D, hι, hc⟩

private noncomputable def homOfRestrictedYoneda
    (A : Type u) [Ring A] {X : ModuleCat.{max u v} A} {Z : FPCat.{u, v} A}
    (η : yoneda.obj Z ⟶ (fpYoneda.{u, v} A).obj X) :
    (finitelyPresentedModule.{u, max u v} A).ι.obj Z ⟶ X :=
  yonedaEquiv η

/-- Precomposing `homOfRestrictedYoneda η` with a module map evaluates `η` on it. -/
private lemma map_comp_homOfRestrictedYoneda (A : Type u) [Ring A]
    {X : ModuleCat.{max u v} A} {Z Z' : FPCat.{u, v} A}
    (η : yoneda.obj Z ⟶ (fpYoneda.{u, v} A).obj X) (g : Z' ⟶ Z) :
    (finitelyPresentedModule.{u, max u v} A).ι.map g ≫ homOfRestrictedYoneda A η =
      η.app (Opposite.op Z') g := by
  have ht := yonedaEquiv_naturality η g
  rw [yonedaEquiv_comp (yoneda.map g) η, yonedaEquiv_yoneda_map] at ht
  change (g.hom ≫ yonedaEquiv η) = η.app (Opposite.op Z') g at ht
  simpa [homOfRestrictedYoneda, fpYoneda] using ht

private noncomputable def moduleCoconeOfYoneda (A : Type u) [Ring A]
    {I : Type (max u v)} [SmallCategory I] {F : I ⥤ FPCat.{u, v} A}
    {X : ModuleCat.{max u v} A}
    (η : F ⋙ yoneda ⟶ (Functor.const I).obj ((fpYoneda.{u, v} A).obj X)) :
    Cocone (F ⋙ (finitelyPresentedModule.{u, max u v} A).ι) where
  pt := X
  ι := {
    app i := homOfRestrictedYoneda A (η.app i)
    naturality := by
      intro i j h
      have hP := congrArg (fun α => (α.app (Opposite.op (F.obj i))) (𝟙 _))
        (η.naturality h)
      have h1 := map_comp_homOfRestrictedYoneda A (η.app j) (F.map h)
      have h2 : (η.app j).app (Opposite.op (F.obj i)) (F.map h) =
          homOfRestrictedYoneda A (η.app i) := by
        simpa [homOfRestrictedYoneda, yonedaEquiv_apply, Functor.const] using hP
      change ((finitelyPresentedModule.{u, max u v} A).ι.map
        (F.map h)) ≫ homOfRestrictedYoneda A (η.app j) =
        homOfRestrictedYoneda A (η.app i)
      rw [h1, h2]
      }

private noncomputable def moduleCocone₁ {X Y : ModuleCat.{max u v} A}
    {f g : (fpYoneda.{u, v} A).obj X ⟶ (fpYoneda.{u, v} A).obj Y}
    (P : IndParallelPairPresentation f g) := moduleCoconeOfYoneda A P.ι₁

private noncomputable def moduleCocone₂ {X Y : ModuleCat.{max u v} A}
    {f g : (fpYoneda.{u, v} A).obj X ⟶ (fpYoneda.{u, v} A).obj Y}
    (P : IndParallelPairPresentation f g) := moduleCoconeOfYoneda A P.ι₂

private noncomputable def moduleCoconeOfYoneda_isColimit (A : Type u) [Ring A]
    {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ FPCat.{u, v} A} {X : ModuleCat.{max u v} A}
    (η : F ⋙ yoneda ⟶ (Functor.const I).obj ((fpYoneda.{u, v} A).obj X))
    (hη : IsColimit (Cocone.mk _ η)) : IsColimit (moduleCoconeOfYoneda A η) := by
  let Z := regFPObj A
  let ev := (evaluation (FPCat.{u, v} A)ᵒᵖ (Type (max u v))).obj (Opposite.op Z)
  let inc := (finitelyPresentedModule.{u, max u v} A).ι
  let G := coyoneda.obj (Opposite.op (inc.obj Z))
  letI : IsFinitelyPresentable (inc.obj Z) :=
    finitePresentation_isFinitelyPresentable A _ Z.property
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v} G :=
    (isFinitelyPresentable_iff_preservesFilteredColimitsOfSize).mp inferInstance
  have hEval : IsColimit (ev.mapCocone (Cocone.mk _ η)) :=
    isColimitOfPreserves ev hη
  let e : F ⋙ yoneda ⋙ ev ≅ F ⋙ inc ⋙ G := NatIso.ofComponents
    (fun i =>
      ({ toFun := fun g => inc.map g
         invFun := fun g => ObjectProperty.homMk g
         left_inv _ := rfl
         right_inv _ := rfl } :
        ((F ⋙ yoneda ⋙ ev).obj i) ≃ ((F ⋙ inc ⋙ G).obj i)).toIso)
    (by intro i j f; ext g; rfl)
  let cR := G.mapCocone (moduleCoconeOfYoneda A η)
  let cL := ev.mapCocone (Cocone.mk _ η)
  let ec : (Cocone.precompose e.hom).obj cR ≅ cL := Cocone.ext (Iso.refl _)
    (by
      intro i
      ext g
      exact map_comp_homOfRestrictedYoneda A (η.app i) g)
  exact moduleColimit_of_freeCoyoneda_colimit A
    ((IsColimit.precomposeHomEquiv e cR).1 (hEval.ofIsoColimit ec.symm))

private lemma moduleStageMapCommutes (A : Type u) [Ring A]
    {X Y : ModuleCat.{max u v} A}
    (f₀ : X ⟶ Y)
    {f g : (fpYoneda.{u, v} A).obj X ⟶ (fpYoneda.{u, v} A).obj Y}
    (P : IndParallelPairPresentation f g) (hf₀ : (fpYoneda.{u, v} A).map f₀ = f) (i : P.I) :
    homOfRestrictedYoneda A (P.ι₁.app i) ≫ f₀ =
      (finitelyPresentedModule.{u, max u v} A).ι.map (P.φ.app i) ≫
        homOfRestrictedYoneda A (P.ι₂.app i) := by
  have hη : P.ι₁.app i ≫ (fpYoneda.{u, v} A).map f₀ =
      yoneda.map (P.φ.app i) ≫ P.ι₂.app i := by
    calc
      P.ι₁.app i ≫ (fpYoneda.{u, v} A).map f₀ = P.ι₁.app i ≫ f :=
        congrArg (fun α => P.ι₁.app i ≫ α) hf₀
      _ = P.ι₁.app i ≫ IsColimit.map P.isColimit₁ (Cocone.mk _ P.ι₂)
          (Functor.whiskerRight P.φ yoneda) :=
        congrArg (fun α => P.ι₁.app i ≫ α) P.hf
      _ = yoneda.map (P.φ.app i) ≫ P.ι₂.app i := by
        simpa using P.isColimit₁.ι_map (Cocone.mk _ P.ι₂)
          (Functor.whiskerRight P.φ yoneda) i
  have hL : yonedaEquiv (P.ι₁.app i ≫ (fpYoneda.{u, v} A).map f₀) =
      homOfRestrictedYoneda A (P.ι₁.app i) ≫ f₀ := by
    rw [yonedaEquiv_comp]
    show ((fpYoneda.{u, v} A).map f₀).app (Opposite.op (P.F₁.obj i))
      (homOfRestrictedYoneda A (P.ι₁.app i)) = _
    simp [fpYoneda, homOfRestrictedYoneda]
    rfl
  have hR : yonedaEquiv (yoneda.map (P.φ.app i) ≫ P.ι₂.app i) =
      (finitelyPresentedModule.{u, max u v} A).ι.map (P.φ.app i) ≫
        homOfRestrictedYoneda A (P.ι₂.app i) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact (map_comp_homOfRestrictedYoneda A (P.ι₂.app i) (P.φ.app i)).symm
  exact hL.symm.trans ((congrArg yonedaEquiv hη).trans hR)

private noncomputable def stagePairsC {A : Type u} [Ring A]
    {X Y : ModuleCat.{max u v} A}
    {f g : (fpYoneda.{u, v} A).obj X ⟶ (fpYoneda.{u, v} A).obj Y}
    (P : IndParallelPairPresentation f g) :
    P.I ⥤ (WalkingParallelPair ⥤ FPCat.{u, v} A) where
  obj i := parallelPair (P.φ.app i) (P.ψ.app i)
  map {i j} h := {
    app := fun k => match k with
      | WalkingParallelPair.zero => P.F₁.map h
      | WalkingParallelPair.one => P.F₂.map h
    naturality := by
      intro a b g
      cases g with
      | id a => simp
      | left => exact (P.φ.naturality h).symm
      | right => exact (P.ψ.naturality h).symm }

private noncomputable def stagePairsM {A : Type u} [Ring A]
    {X Y : ModuleCat.{max u v} A}
    {f g : (fpYoneda.{u, v} A).obj X ⟶ (fpYoneda.{u, v} A).obj Y}
    (P : IndParallelPairPresentation f g) :
    P.I ⥤ (WalkingParallelPair ⥤ ModuleCat.{max u v} A) :=
  stagePairsC P ⋙ (Functor.whiskeringRight WalkingParallelPair
    (FPCat.{u, v} A) (ModuleCat.{max u v} A)).obj
      (finitelyPresentedModule.{u, max u v} A).ι

private lemma moduleStageMapCommutes₂ (A : Type u) [Ring A]
    {X Y : ModuleCat.{max u v} A}
    (f₀ : X ⟶ Y)
    (P : IndParallelPairPresentation ((fpYoneda.{u, v} A).map f₀)
      ((fpYoneda.{u, v} A).map (0 : X ⟶ Y))) (i : P.I) :
    homOfRestrictedYoneda A (P.ι₁.app i) ≫ (0 : X ⟶ Y) =
      (finitelyPresentedModule.{u, max u v} A).ι.map (P.ψ.app i) ≫
        homOfRestrictedYoneda A (P.ι₂.app i) := by
  let P' : IndParallelPairPresentation ((fpYoneda.{u, v} A).map (0 : X ⟶ Y))
      ((fpYoneda.{u, v} A).map f₀) := { P with φ := P.ψ, ψ := P.φ, hf := P.hg, hg := P.hf }
  exact moduleStageMapCommutes A (0 : X ⟶ Y) P' rfl i

private noncomputable def modulePairCocone {A : Type u} [Ring A]
    {X Y : ModuleCat.{max u v} A} (f₀ : X ⟶ Y)
    (P : IndParallelPairPresentation ((fpYoneda.{u, v} A).map f₀)
      ((fpYoneda.{u, v} A).map (0 : X ⟶ Y))) :
    Cocone (stagePairsM P) := by
  let cX := moduleCocone₁ A P
  let cY := moduleCocone₂ A P
  let G := parallelPair f₀ (0 : X ⟶ Y)
  refine { pt := G, ι := ?_ }
  refine { app := fun i => ?_, naturality := ?_ }
  · refine { app := ?_, naturality := ?_ }
    · intro j
      cases j with
      | zero => exact cX.ι.app i
      | one => exact cY.ι.app i
    · intro j k h
      cases h with
      | id j => simp
      | left =>
          change ((finitelyPresentedModule.{u, max u v} A).ι.map
              (P.φ.app i)) ≫ cY.ι.app i = cX.ι.app i ≫ f₀
          exact (moduleStageMapCommutes A f₀ P rfl i).symm
      | right =>
          change ((finitelyPresentedModule.{u, max u v} A).ι.map
              (P.ψ.app i)) ≫ cY.ι.app i = cX.ι.app i ≫ (0 : X ⟶ Y)
          exact (moduleStageMapCommutes₂ A f₀ P i).symm
  · intro i j h
    ext k x
    cases k with
    | zero =>
        change (ConcreteCategory.hom ((P.F₁.map h).hom ≫ cX.ι.app j)) x =
          (ConcreteCategory.hom (cX.ι.app i)) x
        exact congrArg (fun m :
          ((finitelyPresentedModule.{u, max u v} A).ι.obj (P.F₁.obj i)) ⟶ X =>
            ConcreteCategory.hom m x) (cX.ι.naturality h)
    | one =>
        change (ConcreteCategory.hom ((P.F₂.map h).hom ≫ cY.ι.app j)) x =
          (ConcreteCategory.hom (cY.ι.app i)) x
        exact congrArg (fun m :
          ((finitelyPresentedModule.{u, max u v} A).ι.obj (P.F₂.obj i)) ⟶ Y =>
            ConcreteCategory.hom m x) (cY.ι.naturality h)

private noncomputable def modulePairCocone_isColimit {A : Type u} [Ring A]
    {X Y : ModuleCat.{max u v} A} (f₀ : X ⟶ Y)
    (P : IndParallelPairPresentation ((fpYoneda.{u, v} A).map f₀)
      ((fpYoneda.{u, v} A).map (0 : X ⟶ Y))) : IsColimit (modulePairCocone f₀ P) := by
  apply evaluationJointlyReflectsColimits
  intro k
  cases k with
  | zero =>
      let ev := (evaluation WalkingParallelPair (ModuleCat.{max u v} A)).obj
        WalkingParallelPair.zero
      let D0 := stagePairsM P ⋙ ev
      let D1 := P.F₁ ⋙ (finitelyPresentedModule.{u, max u v} A).ι
      let e : D1 ≅ D0 := NatIso.ofComponents (fun i => Iso.refl _)
        (by intro i j h; rfl)
      let c0 := ev.mapCocone (modulePairCocone f₀ P)
      let c1 := (Cocone.precompose e.hom).obj c0
      have hc1 : IsColimit c1 :=
        (IsColimit.precomposeHomEquiv e c0).symm
          (moduleCoconeOfYoneda_isColimit A P.ι₁ P.isColimit₁)
      have ec : c1 ≅ moduleCocone₁ A P := Cocone.ext (Iso.refl _) (by
        intro i
        ext x
        rfl)
      exact IsColimit.ofIsoColimit hc1 ec
  | one =>
      let ev := (evaluation WalkingParallelPair (ModuleCat.{max u v} A)).obj
        WalkingParallelPair.one
      let D0 := stagePairsM P ⋙ ev
      let D1 := P.F₂ ⋙ (finitelyPresentedModule.{u, max u v} A).ι
      let e : D1 ≅ D0 := NatIso.ofComponents (fun i => Iso.refl _)
        (by intro i j h; rfl)
      let c0 := ev.mapCocone (modulePairCocone f₀ P)
      let c1 := (Cocone.precompose e.hom).obj c0
      have hc1 : IsColimit c1 :=
        (IsColimit.precomposeHomEquiv e c0).symm
          (moduleCoconeOfYoneda_isColimit A P.ι₂ P.isColimit₂)
      have ec : c1 ≅ moduleCocone₂ A P := Cocone.ext (Iso.refl _) (by
        intro i
        ext x
        rfl)
      exact IsColimit.ofIsoColimit hc1 ec

variable (A : Type u) [Ring A]
variable {B : Type w} [Category.{x} B] [Preadditive B] [HasFiniteBiproducts B]
  [HasCokernels B]
variable {F : CategoryTheory.Functor
  (FinitelyPresentedModuleCat.{u, max u v} A) B}

/-- A filtered-colimit extension of a right exact functor on finitely presented modules is
right exact. -/
public lemma filteredColimitExtension_preservesFiniteColimits
    (E : FilteredColimitExtension A F) [PreservesFiniteColimits F] :
    PreservesFiniteColimits E.functor := by
  classical
  let : PreservesFilteredColimitsOfSize.{max u v, max u v} E.functor :=
    E.preservesFilteredColimits
  have hCoker : ∀ {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) E.functor := by
    intro X Y f
    let : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
    let : HasColimitsOfShape WalkingParallelPair B := inferInstance
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation
      (rInd A X) (rInd A Y) ((fpYoneda.{u, v} A).map f)
        ((fpYoneda.{u, v} A).map (0 : X ⟶ Y))
    let K := stagePairsM P
    let c := modulePairCocone f P
    have hc : IsColimit c := modulePairCocone_isColimit f P
    let W := (Functor.whiskeringRight WalkingParallelPair
      (ModuleCat.{max u v} A) B).obj E.functor
    let colimB : (WalkingParallelPair ⥤ B) ⥤ B := colim
    let colimM : (WalkingParallelPair ⥤ ModuleCat.{max u v} A) ⥤
        ModuleCat.{max u v} A := colim
    let L := W ⋙ colimB
    let L' := colimM ⋙ E.functor
    let α : L ⟶ L' :=
      { app D := colimit.post D E.functor
        naturality := by
          intro D D' g
          exact (colimit.map_post g E.functor).symm }
    have hstage (i : P.I) : IsIso ((Functor.whiskerLeft K α).app i) := by
      let G := (stagePairsC P).obj i
      let ι := finitelyPresentedModule.{u, max u v} A |>.ι
      have hG : PreservesColimit G F := by infer_instance
      have hGE : PreservesColimit G (ι ⋙ E.functor) :=
        preservesColimit_of_natIso G E.iso.symm
      show IsIso (colimit.post (K.obj i) E.functor)
      have hK : PreservesColimit (K.obj i) E.functor := by
        show PreservesColimit (G ⋙ ι) E.functor
        let φ := G.map WalkingParallelPairHom.left
        let ψ := G.map WalkingParallelPairHom.right
        let φM := ι.map φ
        let ψM := ι.map ψ
        let δM := φM - ψM
        let q := (G.obj WalkingParallelPair.one).obj ⧸ LinearMap.range δM.hom
        let Q : FPCat.{u, v} A :=
          ⟨ModuleCat.of A q, by
            show Module.FinitePresentation A q
            let : Module.FinitePresentation A
                (ι.obj (G.obj WalkingParallelPair.zero)) :=
              (G.obj WalkingParallelPair.zero).property
            let : Module.FinitePresentation A
                (ι.obj (G.obj WalkingParallelPair.one)) :=
              (G.obj WalkingParallelPair.one).property
            exact Module.finitePresentation_of_surjective
              (LinearMap.range δM.hom).mkQ (Submodule.mkQ_surjective _)
              (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range δM.hom)⟩
        let cokerCocone := ModuleCat.cokernelCocone δM
        let π : (G.obj WalkingParallelPair.one) ⟶ Q :=
          ObjectProperty.homMk cokerCocone.π
        let cG : Cocone G := Preadditive.coforkOfCokernelCofork
          (CokernelCofork.ofπ π (by
          apply ObjectProperty.hom_ext
          show δM ≫ cokerCocone.π = 0
          exact cokerCocone.condition))
        let cPair : Cocone (parallelPair φM ψM) :=
          Preadditive.coforkOfCokernelCofork cokerCocone
        have hcPair : IsColimit cPair :=
          Preadditive.isColimitCoforkOfCokernelCofork
            (ModuleCat.cokernelIsColimit δM)
        let e : G ⋙ ι ≅ parallelPair φM ψM := NatIso.ofComponents
          (fun j => by cases j <;> exact Iso.refl _)
          (by intro j k h; cases h <;> simp [φM, ψM, φ, ψ])
        let cM : Cocone (G ⋙ ι) := (Cocone.precompose e.hom).obj cPair
        have hcM : IsColimit cM :=
          (IsColimit.precomposeHomEquiv e cPair).2 hcPair
        have he : ι.mapCocone cG ≅ cM := Cocone.ext (Iso.refl _) (by
          intro j
          cases j with
          | zero =>
              show ι.map (φ ≫ π) = φM ≫ cokerCocone.π
              rw [Functor.map_comp]
              rfl
          | one =>
              show ι.map π = cokerCocone.π
              rfl)
        have hcG : IsColimit cG :=
          isColimitOfReflects ι (IsColimit.ofIsoColimit hcM he.symm)
        let : PreservesColimit G (ι ⋙ E.functor) := hGE
        have hcE : IsColimit (E.functor.mapCocone (ι.mapCocone cG)) := by
          show IsColimit ((ι ⋙ E.functor).mapCocone cG)
          exact isColimitOfPreserves (ι ⋙ E.functor) hcG
        have hcE' : IsColimit (E.functor.mapCocone cM) := by
          let heE := (Cocone.functoriality (G ⋙ ι) E.functor).mapIso he
          exact IsColimit.ofIsoColimit hcE heE
        exact preservesColimit_of_preserves_colimit_cocone hcM hcE'
      let := hK
      infer_instance
    have (i : P.I) : IsIso ((Functor.whiskerLeft K α).app i) := hstage i
    have hwhisker : IsIso (Functor.whiskerLeft K α) :=
      NatIso.isIso_of_isIso_app _
    have hW : PreservesColimitsOfShape P.I W := by
      apply preservesColimitsOfShape_of_evaluation W P.I
      intro j
      show PreservesColimitsOfShape P.I
        ((evaluation WalkingParallelPair (ModuleCat.{max u v} A)).obj j ⋙ E.functor)
      infer_instance
    let : PreservesColimitsOfShape P.I W := hW
    let : PreservesColimitsOfShape P.I colimB := by infer_instance
    let : PreservesColimitsOfShape P.I colimM := by infer_instance
    let : PreservesColimitsOfShape P.I L := by infer_instance
    let : PreservesColimitsOfShape P.I L' := by infer_instance
    have hα : IsIso (α.app c.pt) :=
      isIso_app_coconePt_of_preservesColimit K α c hc
    have : IsIso (colimit.post (parallelPair f 0) E.functor) := by
      simpa [L, L', W, c, K, α, modulePairCocone] using hα
    exact preservesColimit_of_isIso_post E.functor (parallelPair f 0)
  let : ∀ {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) E.functor := hCoker
  let : E.functor.PreservesZeroMorphisms := by
    let ι := finitelyPresentedModule.{u, max u v} A |>.ι
    let Z : FinitelyPresentedModuleCat.{u, max u v} A :=
      ⟨ModuleCat.of A PUnit, by
        show Module.FinitePresentation A PUnit
        infer_instance⟩
    have hZ : IsInitial Z := IsInitial.ofUniqueHom
      (fun Y => ObjectProperty.homMk (0 : Z.obj ⟶ Y.obj))
      (by
        intro Y f
        apply ObjectProperty.hom_ext
        exact (ModuleCat.isZero_of_subsingleton Z.obj).eq_of_src _ _)
    let (Y : FinitelyPresentedModuleCat.{u, max u v} A) :
        Unique (Z ⟶ Y) := ⟨⟨hZ.to Y⟩, fun f => hZ.hom_ext _ _⟩
    let : HasInitial (FinitelyPresentedModuleCat.{u, max u v} A) :=
      hasInitial_of_unique Z
    let : PreservesColimit (Functor.empty.{0}
        (FinitelyPresentedModuleCat.{u, max u v} A)) F := by infer_instance
    have zIso : ι.obj Z ≅ (0 : ModuleCat.{max u v} A) :=
      ModuleCat.isZero_of_subsingleton (Z.obj) |>.iso
        (isZero_zero (ModuleCat.{max u v} A))
    have h0 : E.functor.obj (0 : ModuleCat.{max u v} A) ≅ 0 := by
      exact E.functor.mapIso zIso.symm ≪≫ E.iso.app Z ≪≫
        F.mapIso (hZ.uniqueUpToIso initialIsInitial) ≪≫
        PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm
    exact Functor.preservesZeroMorphisms_of_map_zero_object h0
  exact Functor.preservesFiniteColimits_of_preservesCokernels E.functor

/-- A filtered-colimit extension of a right exact functor on finitely presented modules is
additive. -/
public lemma filteredColimitExtension_additive_of_preservesFiniteColimits
    (E : FilteredColimitExtension A F) [PreservesFiniteColimits F] :
    E.functor.Additive := by
  have : PreservesFiniteColimits E.functor :=
    filteredColimitExtension_preservesFiniteColimits A E
  have : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts E.functor
  exact Functor.additive_of_preservesBinaryBiproducts E.functor

/-- A right exact functor on finitely presented modules which admits a filtered-colimit
extension is additive, because its extension is and restricts to it. -/
public lemma additive_of_preservesFiniteColimits
    (E : FilteredColimitExtension A F) [PreservesFiniteColimits F] :
    F.Additive :=
  have : E.functor.Additive := filteredColimitExtension_additive_of_preservesFiniteColimits A E
  Functor.additive_of_iso E.iso

/-- A filtered-colimit extension of a right exact functor on finitely presented modules
commutes with arbitrary direct sums. -/
public lemma filteredColimitExtension_preservesCoproducts_of_preservesFiniteColimits
    (E : FilteredColimitExtension A F) [PreservesFiniteColimits F] (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) E.functor :=
  have : F.Additive := additive_of_preservesFiniteColimits A E
  extension_preserves_discrete_coproducts A E J

section Extension

variable [HasFilteredColimitsOfSize.{max u v, max u v} B]
  (G : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B)
  [PreservesFiniteColimits G]

/-- The extension of a right exact functor on finitely presented modules to all modules is
additive. -/
@[stacks 0GNL "additivity"]
public lemma filteredColimitExtension_functor_additive :
    (filteredColimitExtension A G).functor.Additive :=
  filteredColimitExtension_additive_of_preservesFiniteColimits A (filteredColimitExtension A G)

/-- The extension of a right exact functor on finitely presented modules to all modules is
right exact. -/
@[stacks 0GNL "right exactness"]
public lemma filteredColimitExtension_functor_preservesFiniteColimits :
    PreservesFiniteColimits (filteredColimitExtension A G).functor :=
  filteredColimitExtension_preservesFiniteColimits A (filteredColimitExtension A G)

/-- The extension of a right exact functor on finitely presented modules to all modules
commutes with arbitrary direct sums. -/
@[stacks 0GNL "arbitrary direct sums"]
public lemma filteredColimitExtension_functor_preservesCoproducts (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) (filteredColimitExtension A G).functor :=
  filteredColimitExtension_preservesCoproducts_of_preservesFiniteColimits A
    (filteredColimitExtension A G) J

end Extension

end ModuleCat
