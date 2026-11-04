module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacement
import StacksCore.Tactic.StacksAttribute

/-!
# The simplicial replacement of `j_{U!}ℤ_U` is the free chains on the nerve of `C/U`

Let `C` be a small category with the chaotic topology and `U` an object of `C`, and let
`F = j_{U!}ℤ_U` be the extension by zero of the constant sheaf `ℤ` on the localization at `U`.
On a chaotic site `F` is the free abelian presheaf represented by `U`, so the degree-`n` term of
the simplicial replacement `K_•(F)` is the free abelian group on the strings `Uₙ → ⋯ → U₀` of `C`
together with an arrow `U₀ ⟶ U`, that is, on the `n`-simplices of the nerve of the slice `C/U`.
That nerve is contractible, since `C/U` has the terminal object `𝟙_U`.

## Main definitions

* `Stacks.CategoryHomology.integerSheafOver`: the constant sheaf `ℤ` on the chaotic slice site
  over `U`, and `integerExtensionByZero`: its extension by zero to `C`.
* `Stacks.CategoryHomology.overSimplexEquiv`: strings of `n` composable arrows of `C/U` are the
  same thing as a string of `n` composable arrows of `C` together with an arrow from its right
  endpoint to `U`.
* `Stacks.CategoryHomology.integerExtensionByZero_iso_freeYoneda`: on a chaotic site the
  extension by zero is the free abelian presheaf on `yoneda.obj U`.
* `Stacks.CategoryHomology.representableReplacementComplexIsoFreeNerve`: the resulting
  isomorphism of the simplicial replacement complex with the free chains on the nerve of `C/U`.

## Main results

* `Stacks.CategoryHomology.overSimplexEquiv_forget` and `overSimplexEquiv_last`: the simplex
  comparison preserves the underlying string of arrows and the prescribed arrow to `U`.
* `Stacks.CategoryHomology.representableReplacementComplexIsoFreeNerve_generator`: the value of
  the complex comparison on each generator.
* `Stacks.CategoryHomology.nerveOver_homotopyEquivalent_point`: the nerve of `C/U` is homotopy
  equivalent to a point.

## Implementation notes

`integerExtensionByZero` is the lower shriek `Functor.sheafPullbackConstruction.sheafPullback`
along `Over.forget U`. Its identification with the free abelian representable presheaf uses that
`yoneda.obj U` is the left Kan extension of `yoneda.obj (𝟙_U)` along `(Over.forget U).op`, and
that `AddCommGrpCat.free` preserves the colimits computing it.

`overSimplexEquiv_whisker` is proved by applying the inverse of the equivalence to both sides,
not by `CategoryTheory.Functor.ext`: the two functors agree on objects only propositionally, and
`Functor.ext` produces `eqToHom`s between `Over`-objects that no rewrite cancels.

`replacementTermIso_generator` and `directSumFreeEquiv_of` are applied with all their arguments
given, and `replacementMap_generator` writes its summand index out, because the coercion
`↑((yoneda.obj U ⋙ AddCommGrpCat.free).obj (op y.right))` and `FreeAbelianGroup (y.right ⟶ U)`
are defeq but not syntactically equal, so the rewrites do not fire otherwise.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Opposite
open scoped DirectSum Simplicial

universe u

namespace Stacks.CategoryHomology


variable {C : Type u} [SmallCategory C] (U : C)

/-- The constant integer sheaf on the chaotic slice site over `U`. -/
noncomputable def integerSheafOver :
    Sheaf (GrothendieckTopology.trivial (Over U)) AddCommGrpCat.{u} := by
  letI : HasWeakSheafify (GrothendieckTopology.trivial (Over U))
      AddCommGrpCat.{u} := by
    rw [GrothendieckTopology.trivial_eq_bot]
    infer_instance
  exact (presheafToSheaf (GrothendieckTopology.trivial (Over U))
    AddCommGrpCat.{u}).obj
      ((Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.free.obj PUnit.{u + 1}))

/-- The lower shriek of the constant integer sheaf from the slice site. -/
noncomputable def integerExtensionByZero :
    Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u} := by
  letI : HasWeakSheafify (GrothendieckTopology.trivial C)
      AddCommGrpCat.{u} := by
    rw [GrothendieckTopology.trivial_eq_bot]
    infer_instance
  exact (Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u}
    (GrothendieckTopology.trivial (Over U))
    (GrothendieckTopology.trivial C)).obj (integerSheafOver U)

/-- A string in the slice category is a string in `C` together with a map
from its right endpoint to `U`. -/
@[stacks 08PG "representable_contractible"]
def overSimplexEquiv (n : ℕ) :
    (Σ x : ComposableArrows C n, x.right ⟶ U) ≃
      ComposableArrows (Over U) n := by
  classical
  let Fwd : (Σ x : ComposableArrows C n, x.right ⟶ U) →
      ComposableArrows (Over U) n := fun a =>
    { obj := fun i => Over.mk (a.1.map (homOfLE (show i ≤ Fin.last n from Fin.le_last i)) ≫ a.2)
      map := fun {i j} g => Over.homMk (a.1.map g) (by
        dsimp
        calc
          a.1.map g ≫ a.1.map (homOfLE (show j ≤ Fin.last n from Fin.le_last j)) ≫ a.2 =
              a.1.map (g ≫ homOfLE (show j ≤ Fin.last n from Fin.le_last j)) ≫ a.2 := by
                simp [Category.assoc]
          _ = a.1.map (homOfLE (show i ≤ Fin.last n from Fin.le_last i)) ≫ a.2 := by
                congr 1)
      map_id := by intro i; apply Over.OverMorphism.ext; simp
      map_comp := by intro i j k f g; apply Over.OverMorphism.ext; simp }
  let Bwd : ComposableArrows (Over U) n →
      (Σ x : ComposableArrows C n, x.right ⟶ U) := fun y =>
    ⟨y ⋙ Over.forget U, (y.obj (Fin.last n)).hom⟩
  refine ⟨Fwd, Bwd, ?_, ?_⟩
  · intro a
    apply Sigma.ext
    · refine CategoryTheory.Functor.ext ?_ ?_
      · intro i
        rfl
      · intro i j f
        simp [Fwd, Bwd]
    · change HEq ((Fwd a).obj (Fin.last n)).hom a.2
      simp [Fwd]
  · intro y
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro i
      change Over.mk ((y.map (homOfLE (show i ≤ Fin.last n from Fin.le_last i))).left ≫
        (y.obj (Fin.last n)).hom) = y.obj i
      exact (congrArg Over.mk
        (Over.w (y.map (homOfLE (show i ≤ Fin.last n from Fin.le_last i))))).trans
          (CostructuredArrow.eq_mk (y.obj i)).symm
    · intro i j f
      apply Over.OverMorphism.ext
      simp [Fwd, Bwd]

/-- The simplex comparison preserves the underlying string of arrows. -/
@[stacks 08PG "representable_contractible"]
theorem overSimplexEquiv_forget (n : ℕ)
    (a : Σ x : ComposableArrows C n, x.right ⟶ U) :
    overSimplexEquiv U n a ⋙ Over.forget U = a.1 := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    rfl
  · intro i j f
    simp [overSimplexEquiv]

/-- The last object of the compared simplex has the prescribed arrow to `U`. -/
@[stacks 08PG "representable_contractible"]
theorem overSimplexEquiv_last (n : ℕ)
    (a : Σ x : ComposableArrows C n, x.right ⟶ U) :
    HEq ((overSimplexEquiv U n a).obj (Fin.last n)).hom a.2 := by
  simp [overSimplexEquiv]

/-- The presheaf represented by a terminal object is isomorphic to the constant presheaf on
`PUnit`. -/
def terminalYonedaIsoConst {D : Type u} [SmallCategory D]
    {T : D} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Dᵒᵖ).obj PUnit.{u + 1} :=
  NatIso.ofComponents (fun X => Equiv.toIso
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => hT.from X.unop
      left_inv := fun _ => hT.hom_ext _ _
      right_inv := fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _ }) (by intros; rfl)

/-- On a chaotic site, extension by zero of the constant integer sheaf is the
free abelian presheaf represented by `U`. -/
@[stacks 08PG "representable_contractible"]
def integerExtensionByZero_iso_freeYoneda :
    (sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).obj
        (integerExtensionByZero U) ≅
      ((yoneda.obj U) ⋙ AddCommGrpCat.free) := by
  letI : HasWeakSheafify (GrothendieckTopology.trivial C) AddCommGrpCat.{u} := by
    rw [GrothendieckTopology.trivial_eq_bot]
    infer_instance
  letI : HasWeakSheafify (GrothendieckTopology.trivial (Over U)) AddCommGrpCat.{u} := by
    rw [GrothendieckTopology.trivial_eq_bot]
    infer_instance
  let e : (sheafToPresheaf (GrothendieckTopology.trivial (Over U))
      AddCommGrpCat.{u}).obj (integerSheafOver U) ≅
      yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free :=
    (isoSheafify _ (by simpa only [GrothendieckTopology.trivial_eq_bot] using
      Presheaf.isSheaf_bot ((Functor.const (Over U)ᵒᵖ).obj
        (AddCommGrpCat.free.obj PUnit.{u + 1})))).symm ≪≫
      (Functor.constComp _ _ _).symm ≪≫
      Functor.isoWhiskerRight (terminalYonedaIsoConst (Over.mkIdTerminal (X := U))).symm _
  refine (isoSheafify _ (by
    simpa only [GrothendieckTopology.trivial_eq_bot] using Presheaf.isSheaf_bot _)).symm ≪≫
    (Over.forget U).op.lan.mapIso e ≪≫
    (Functor.leftKanExtensionCompIsoOfPreserves AddCommGrpCat.free
      (yoneda.obj (Over.mk (𝟙 U))) (Over.forget U).op).symm ≪≫ ?_
  letI : (yoneda.obj U).IsLeftKanExtension
      (yonedaMap (Over.forget U) (Over.mk (𝟙 U))) :=
    inferInstanceAs ((yoneda.obj ((Over.forget U).obj (Over.mk (𝟙 U)))).IsLeftKanExtension _)
  exact Functor.isoWhiskerRight (Functor.leftKanExtensionUnique
    ((Over.forget U).op.leftKanExtension (yoneda.obj (Over.mk (𝟙 U))))
    ((Over.forget U).op.leftKanExtensionUnit (yoneda.obj (Over.mk (𝟙 U))))
    (yoneda.obj U) (yonedaMap (Over.forget U) (Over.mk (𝟙 U)))) _

/-- The direct sum of free abelian groups on a family of types is the free abelian group on
the sigma type of the family. -/
def directSumFreeEquiv {I : Type*} (A : I → Type*) :
    (⨁ i, FreeAbelianGroup (A i)) ≃+ FreeAbelianGroup (Σ i, A i) := by
  classical
  let f : (⨁ i, FreeAbelianGroup (A i)) →+ FreeAbelianGroup (Σ i, A i) :=
    DirectSum.toAddMonoid fun i => FreeAbelianGroup.map (Sigma.mk i)
  let g : FreeAbelianGroup (Σ i, A i) →+ (⨁ i, FreeAbelianGroup (A i)) :=
    FreeAbelianGroup.lift fun a => DirectSum.of _ a.1 (FreeAbelianGroup.of a.2)
  refine { f with toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · have h : g.comp f = AddMonoidHom.id _ := by
      apply DirectSum.addHom_ext'
      intro i
      apply FreeAbelianGroup.lift_ext
      intro a
      simp [f, g]
    exact DFunLike.congr_fun h
  · have h : f.comp g = AddMonoidHom.id _ := by
      apply FreeAbelianGroup.lift_ext
      rintro ⟨i, a⟩
      simp [f, g]
    exact DFunLike.congr_fun h

/-- `directSumFreeEquiv` sends the generator `a` of the `i`-th summand to the generator
`⟨i, a⟩`. -/
lemma directSumFreeEquiv_of {I : Type*} (A : I → Type*)
    [DecidableEq I] (i : I) (a : A i) :
    directSumFreeEquiv A (DirectSum.of _ i (FreeAbelianGroup.of a)) =
      FreeAbelianGroup.of ⟨i, a⟩ := by
  show (DirectSum.toAddMonoid (fun i => FreeAbelianGroup.map (Sigma.mk i : A i → Σ i, A i)))
    (DirectSum.of (fun i => FreeAbelianGroup (A i)) i (FreeAbelianGroup.of a)) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- Applying a family of additive equivalences summandwise to `DirectSum.of A i a` gives
`DirectSum.of B i (e i a)`. -/
lemma mapRangeAddEquiv_of {I : Type*} {A B : I → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, AddCommMonoid (B i)]
    (e : ∀ i, A i ≃+ B i) [DecidableEq I] (i : I) (a : A i) :
    DFinsupp.mapRange.addEquiv e (DirectSum.of A i a) = DirectSum.of B i (e i a) := by
  show DFinsupp.mapRange (fun i => e i) (fun i => (e i).map_zero) (DFinsupp.single i a) =
    DFinsupp.single i (e i a)
  exact DFinsupp.mapRange_single

/-- For a presheaf `F` isomorphic to the free abelian presheaf on `yoneda.obj U`, the degree-`n`
term of the simplicial replacement of `F` is the free abelian group on the `n`-simplices of the
nerve of `Over U`. -/
def replacementTermIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : F ≅ yoneda.obj U ⋙ AddCommGrpCat.free) (n : ℕ) :
    replacementGroup F n ≅
      AddCommGrpCat.free.obj (ComposableArrows (Over U) n) :=
  AddEquiv.toAddCommGrpIso <|
    (DFinsupp.mapRange.addEquiv fun x : ComposableArrows C n =>
      (e.app (op x.right)).addCommGroupIsoToAddEquiv).trans
      ((directSumFreeEquiv (fun x : ComposableArrows C n => x.right ⟶ U)).trans
        (FreeAbelianGroup.equivOfEquiv (overSimplexEquiv U n)))

/-- `replacementTermIso` sends the generator indexed by a string `x` and an arrow `f` to `U`
to the corresponding simplex `overSimplexEquiv U n ⟨x, f⟩`. -/
lemma replacementTermIso_generator (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : F ≅ yoneda.obj U ⋙ AddCommGrpCat.free) (n : ℕ)
    (x : ComposableArrows C n) (f : x.right ⟶ U) :
    (replacementTermIso U F e n).hom
      ((@DirectSum.of _ _ _ (Classical.decEq _) x)
        ((e.inv.app (op x.right)) (FreeAbelianGroup.of f))) =
      FreeAbelianGroup.of (overSimplexEquiv U n ⟨x, f⟩) := by
  classical
  show FreeAbelianGroup.equivOfEquiv (overSimplexEquiv U n)
    (directSumFreeEquiv _ (DFinsupp.mapRange.addEquiv
      (fun y : ComposableArrows C n => (e.app (op y.right)).addCommGroupIsoToAddEquiv)
      (DirectSum.of _ x ((e.inv.app (op x.right)) (FreeAbelianGroup.of f))))) = _
  rw [mapRangeAddEquiv_of]
  have h : (e.app (op x.right)).addCommGroupIsoToAddEquiv
      ((e.inv.app (op x.right)) (FreeAbelianGroup.of f)) = FreeAbelianGroup.of f :=
    (e.app (op x.right)).addCommGroupIsoToAddEquiv.apply_symm_apply _
  rw [h]
  show FreeAbelianGroup.equivOfEquiv (overSimplexEquiv U n)
    (directSumFreeEquiv (fun y : ComposableArrows C n => y.right ⟶ U)
      ((@DirectSum.of (ComposableArrows C n)
        (fun y => FreeAbelianGroup (y.right ⟶ U)) _ (Classical.decEq _) x)
        (FreeAbelianGroup.of f))) = _
  rw [directSumFreeEquiv_of (fun y : ComposableArrows C n => y.right ⟶ U) x f]
  rfl

/-- The simplex comparison `overSimplexEquiv` commutes with reindexing a simplex along a
functor `θ : Fin (m + 1) ⥤ Fin (n + 1)`. -/
lemma overSimplexEquiv_whisker {n m : ℕ} (θ : Fin (m + 1) ⥤ Fin (n + 1))
    (x : ComposableArrows C n) (f : x.right ⟶ U) :
    overSimplexEquiv U m ⟨x.whiskerLeft θ,
      x.map (homOfLE (Fin.le_last (θ.obj (Fin.last m)))) ≫ f⟩ =
        (overSimplexEquiv U n ⟨x, f⟩).whiskerLeft θ := by
  apply (overSimplexEquiv U m).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- The value of the simplicial replacement map `replacementMap F g` on the generator indexed
by a string `x` and an arrow `f` to `U`. -/
lemma replacementMap_generator (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : F ≅ yoneda.obj U ⋙ AddCommGrpCat.free)
    {Δ Γ : SimplexCategoryᵒᵖ} (g : Δ ⟶ Γ)
    (x : ComposableArrows C Δ.unop.len) (f : x.right ⟶ U) :
    replacementMap F g
      ((@DirectSum.of _ _ _ (Classical.decEq _) x)
        ((e.inv.app (op x.right)) (FreeAbelianGroup.of f))) =
      (@DirectSum.of _ _ _ (Classical.decEq _)
        (x.whiskerLeft (simplexIndexMap g.unop)))
        ((e.inv.app (op (x.whiskerLeft (simplexIndexMap g.unop)).right))
          (FreeAbelianGroup.of
            (x.map (homOfLE (Fin.le_last
              ((simplexIndexMap g.unop).obj (Fin.last Γ.unop.len)))) ≫ f))) := by
  classical
  rw [replacementMap_on_generator F g x ((e.inv.app (op x.right)) (FreeAbelianGroup.of f))]
  refine congrArg _ ?_
  have h := ConcreteCategory.congr_hom
    (e.inv.naturality (op (x.map (homOfLE (Fin.le_last
      ((simplexIndexMap g.unop).obj (Fin.last Γ.unop.len)))))))
    (FreeAbelianGroup.of f)
  exact h.symm

/-- For a presheaf `F` isomorphic to the free abelian presheaf on `yoneda.obj U`, the
simplicial replacement of `F` is isomorphic to the free abelian simplicial group on the nerve
of `Over U`. -/
def replacementIsoFreeNerve (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : F ≅ yoneda.obj U ⋙ AddCommGrpCat.free) :
    simplicialReplacement F ≅
      (nerve (Over U)) ⋙ AddCommGrpCat.free :=
  NatIso.ofComponents (fun Δ => replacementTermIso U F e Δ.unop.len) (by
    classical
    intro Δ Γ g
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext'
    intro x
    apply (AddMonoidHom.cancel_right
      (f := (e.inv.app (op x.right)).hom)
      (e.app (op x.right)).addCommGroupIsoToAddEquiv.symm.surjective).mp
    apply FreeAbelianGroup.lift_ext
    intro f
    change (replacementTermIso U F e Γ.unop.len).hom
      (replacementMap F g
        (DirectSum.of _ x ((e.inv.app _) (FreeAbelianGroup.of f)))) =
      (AddCommGrpCat.free.map ((nerve (Over U)).map g))
        ((replacementTermIso U F e Δ.unop.len).hom
          (DirectSum.of _ x ((e.inv.app _) (FreeAbelianGroup.of f))))
    rw [replacementMap_generator,
      replacementTermIso_generator U F e Γ.unop.len
        (x.whiskerLeft (simplexIndexMap g.unop))
        (x.map (homOfLE (Fin.le_last
          ((simplexIndexMap g.unop).obj (Fin.last Γ.unop.len)))) ≫ f),
      replacementTermIso_generator U F e Δ.unop.len x f]
    change FreeAbelianGroup.of _ = FreeAbelianGroup.of _
    congr 1
    exact overSimplexEquiv_whisker U _ x f)

/-- The simplicial replacement complex of the extension by zero of the constant integer sheaf is
isomorphic to the free abelian chain complex on the nerve of the category over `U`. -/
@[stacks 08PG "representable_contractible"]
def representableReplacementComplexIsoFreeNerve :
    simplicialReplacementComplex
        ((sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).obj
          (integerExtensionByZero U)) ≅
      (AlgebraicTopology.alternatingFaceMapComplex _).obj
        (((SimplicialObject.whiskering (Type u) AddCommGrpCat).obj
          AddCommGrpCat.free).obj (nerve (Over U))) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (replacementIsoFreeNerve U _ (integerExtensionByZero_iso_freeYoneda U))

/-- The chain-complex comparison takes the generator indexed by a string and
an arrow to `U` to the corresponding simplex of the slice category. -/
@[stacks 08PG "representable_contractible"]
theorem representableReplacementComplexIsoFreeNerve_generator
    (n : ℕ) (x : ComposableArrows C n) (f : x.right ⟶ U) :
    (representableReplacementComplexIsoFreeNerve U).hom.f n
      ((@DirectSum.of (ComposableArrows C n)
        (fun y => ((sheafToPresheaf (GrothendieckTopology.trivial C)
          AddCommGrpCat.{u}).obj (integerExtensionByZero U)).obj (op y.right))
        _ (Classical.decEq _) x)
        (((integerExtensionByZero_iso_freeYoneda U).inv.app (op x.right))
          (FreeAbelianGroup.of f))) =
      FreeAbelianGroup.of (overSimplexEquiv U n ⟨x, f⟩) :=
  replacementTermIso_generator U _ (integerExtensionByZero_iso_freeYoneda U) n x f

/-- The functor `Fin 2 × D ⥤ D` given by the natural transformation from the identity to the
constant functor at a terminal object `T`. -/
def terminalContractionFunctor {D : Type u} [SmallCategory D]
    {T : D} (hT : IsTerminal T) : Fin 2 × D ⥤ D :=
  Functor.uncurry.obj (ComposableArrows.mk₁
    (show 𝟭 D ⟶ (Functor.const D).obj T from
      { app := fun d => hT.from d
        naturality := fun _ _ _ => hT.hom_ext _ _ }))

/-- The simplicial homotopy, on the nerve of a category with a terminal object `T`, from the
identity to the map induced by the constant functor at `T`. -/
def nerveTerminalHomotopy {D : Type u} [SmallCategory D]
    {T : D} (hT : IsTerminal T) :
    SSet.Homotopy (𝟙 (nerve D))
      (nerveMap ((Functor.const D).obj T)) where
  h :=
    { app := fun Δ => ↾fun p =>
        ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor.prod' p.1) ⋙
          terminalContractionFunctor hT
      naturality := by
        intro Δ Γ g
        ext p
        rfl }
  h₀ := by
    ext Δ x
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro i j f
    exact heq_of_eq (Category.id_comp (x.map f))
  h₁ := by
    ext Δ x
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro i j f
    exact heq_of_eq (Category.id_comp (𝟙 T))
  rel := by
    ext Δ ⟨⟨x, hx⟩, t⟩
    exact False.elim hx

/-- The nerve of the category over `U`, the simplicial set of strings of arrows ending in an arrow
to `U`, is homotopy equivalent to a point. -/
@[stacks 08PG "representable_contractible"]
theorem nerveOver_homotopyEquivalent_point :
    ∃ f : nerve (Over U) ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      (SimplicialObject.homotopyEquivalences (Type u)) f := by
  let f : nerve (Over U) ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
    { app := fun _ => ↾fun _ => PUnit.unit }
  let g : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} ⟶ nerve (Over U) :=
    { app := fun Δ => ↾fun _ => (Functor.const (Fin (Δ.unop.len + 1))).obj (Over.mk (𝟙 U)) }
  refine ⟨f, g, ?_, ?_⟩
  · have h : f ≫ g = nerveMap ((Functor.const (Over U)).obj (Over.mk (𝟙 U))) := by
      ext Δ x
      rfl
    rw [h]
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      ⟨(nerveTerminalHomotopy (Over.mkIdTerminal (X := U))).toSimplicialObjectHomotopy⟩)
  · have h : g ≫ f = 𝟙 _ := by
      ext Δ x
      rfl
    rw [h]
    exact Relation.EqvGen.refl _

end Stacks.CategoryHomology

end
