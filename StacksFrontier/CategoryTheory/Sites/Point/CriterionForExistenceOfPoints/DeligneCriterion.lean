module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Point.Conservative
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.UniformRefinement

/-!
# Deligne's criterion for the existence of enough points

The stages of Deligne's construction, the tower of stages and the point it produces, Stacks 00YQ
(`CategoryTheory.GrothendieckTopology.hasEnoughPoints_of_exists_finite_refinement`) and its
localized form
(`CategoryTheory.GrothendieckTopology.hasEnoughPoints_of_coversTop_of_exists_finite_refinement`).
Split out of `StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints`.
-/

section

universe w v u u₁ v₁ u₂ v₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite
open ConcreteCategory GrothendieckTopology.Point.ofIsCofiltered

namespace Stacks.SitePoints.DeligneCriterion

@[expose] public section

variable {C : Type u} [Category.{v} C]

attribute [local instance] hasColimitsOfShapeOpOfInitiallySmall

/-- A *stage* of Deligne's construction for a sieve `S` on `X`: a cofiltered, essentially
`w`-small system `q : M ⥤ C` in `C` with a distinguished object `base` and a morphism
`θ : q(base) ⟶ X` none of whose composites `q(ψ) ≫ θ` lies in the `J`-closure of `S`.

The last condition is, through `Stacks.SitePoints.DeligneCriterion.closeSection_eq_topSection_iff`,
the statement that the germ of the `J`-closure of `S` at the system differs from the germ of the
maximal sieve; that is the invariant Stacks 00YP propagates along a refinement. -/
private structure Stage.{w', v', u'} {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    {X : C} (S : Sieve X) where
  /-- the index category of the system -/
  M : Cat.{max u' v', max u' v'}
  /-- the index category is cofiltered -/
  isCofiltered : IsCofiltered M
  /-- the index category is essentially `w'`-small -/
  essentiallySmall : EssentiallySmall.{w'} M
  /-- the system -/
  q : M ⥤ C
  /-- the index above which the distinguished section lives -/
  base : M
  /-- the structural morphism to `X` -/
  θ : q.obj base ⟶ X
  /-- the invariant: no composite of `θ` with a transition map is in the closure of `S` -/
  notMem : ∀ (i : M) (ψ : i ⟶ base), ¬(J.close S) (q.map ψ ≫ θ)

/-- The datum exhibiting a stage `B` as a refinement of a stage `A`, as produced by Stacks 00YP:
an inclusion of index categories identifying `A`'s system with the restriction of `B`'s, a
compatibility of the structural morphisms, and the property that every section of `A`'s fibre
functor becomes, in `B`, covered by every finite covering of the site. -/
private structure Refines.{w', v', u'} {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {X : C} {S : Sieve X} (A B : Stage.{w', v', u'} J S) where
  /-- the inclusion of index categories -/
  e : A.M ⥤ B.M
  /-- `A`'s system is the restriction of `B`'s -/
  ε : e ⋙ B.q ≅ A.q
  /-- a transition map from `B`'s base to the image of `A`'s base -/
  ψ : B.base ⟶ e.obj A.base
  /-- the structural morphisms are compatible -/
  θ_eq : B.q.map ψ ≫ ε.hom.app A.base ≫ A.θ = B.θ
  /-- every section of `A`'s fibre functor is covered in `B` by every finite covering -/
  cover :
    ∀ {W : C} {ι : Type} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
      Sieve.ofArrows Y g ∈ J W →
        ∀ (j : A.M) (f : A.q.obj j ⟶ W),
          ∃ (k : ι) (i : B.M) (φ : i ⟶ e.obj j) (a : B.q.obj i ⟶ Y k),
            a ≫ g k = B.q.map φ ≫ ε.hom.app j ≫ f

/-- The one-object system with value `X` and structural morphism the identity is a stage, for any
sieve `S` on `X` which is not a covering sieve. -/
private def initialStage (J : GrothendieckTopology C) {X : C} (S : Sieve X) (hS : S ∉ J X) :
    Stage.{w, v, u} J S
    where
  M := Cat.of (Discrete PUnit.{max u v + 1})
  isCofiltered := inferInstanceAs (IsCofiltered (Discrete PUnit.{max u v + 1}))
  essentiallySmall := inferInstanceAs (EssentiallySmall.{w} (Discrete PUnit.{max u v + 1}))
  q := (Functor.const _).obj X
  base := ⟨PUnit.unit⟩
  θ := 𝟙 X
  notMem := by
    intro i ψ hc
    refine hS ?_
    rw [← J.close_eq_top_iff_mem, ← Sieve.id_mem_iff_eq_top]
    simpa using hc

/-- **The refinement step.** Every stage admits a refinement, by the main step of Deligne's
criterion (Stacks 00YP) applied to the sheaf of `J`-closed sieves. -/
private theorem exists_refines [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C} {X : C} {S : Sieve X} (A : Stage.{w, v, u} J S) :
    ∃ B : Stage.{w, v, u} J S, Nonempty (Refines A B) := by
  have := A.isCofiltered
  have := A.essentiallySmall
  -- `HasPullbacks C` supplies the base-change hypothesis of Stacks 00YP; naming it fixes the
  -- universe of the index types of the coverings it speaks about, which is `Type` throughout here.
  have hpb :
    ∀ {W : C} {ι : Type} [Finite ι] {Y : ι → C} (g : ∀ k, Y k ⟶ W),
      Sieve.ofArrows Y g ∈ J W → ∀ (Z : C) (h : Z ⟶ W) (k : ι), HasPullback h (g k) :=
    fun _ _ _ _ _ ↦ inferInstance
  obtain ⟨M, hM, hcof, hess, q, e, _, _, ε, hgerm, hcov⟩ :=
    GrothendieckTopology.exists_refinement_forall_covering_of_ne J
      (classifier_isSheaf J).isSeparated hpb A.q A.base (closeSection J S A.θ)
      (topSection J (A.q.obj A.base)) fun j φ hEq ↦
      A.notMem j φ ((map_closeSection_eq_map_topSection_iff J S A.θ _).1 hEq)
  refine
    ⟨{  M := Cat.of M
        isCofiltered := hcof
        essentiallySmall := hess
        q := q
        base := e.obj A.base
        θ := ε.hom.app A.base ≫ A.θ
        notMem := ?_ }, ⟨{ e := e, ε := ε, ψ := 𝟙 _, θ_eq := by simp, cover := hcov }⟩⟩
  intro i ψ hc
  exact hgerm i ψ ((map_closeSection_eq_map_topSection_iff J S A.θ _).2 (by rwa [Category.assoc]))

/-- The next stage of the tower, chosen by `Stacks.SitePoints.DeligneCriterion.exists_refines`. -/
private noncomputable def nextStage [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C} {X : C} {S : Sieve X} (A : Stage.{w, v, u} J S) :
    Stage.{w, v, u} J S :=
  (exists_refines A).choose

/-- The refinement datum exhibiting `Stacks.SitePoints.DeligneCriterion.nextStage A` as a
refinement of `A`. -/
private noncomputable def stepRefines [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C} {X : C} {S : Sieve X} (A : Stage.{w, v, u} J S) :
    Refines A (nextStage A) :=
  (exists_refines A).choose_spec.some

/-- The tower of stages of a sieve `S` which is not a covering sieve: the one-object system `X`,
refined indefinitely by `Stacks.SitePoints.DeligneCriterion.nextStage`. -/
private noncomputable def stageTower [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) {X : C} (S : Sieve X) (hS : S ∉ J X) (n : ℕ) :
    Stage.{w, v, u} J S :=
  Nat.rec (initialStage J S hS) (fun _ A ↦ nextStage A) n

/-! ### Functoriality of the fibre functor of a system -/

section FiberFunctor

variable [LocallySmall.{w} C] {N : Type u₁} [Category.{v₁} N] [InitiallySmall.{w} N] {N' : Type u₂}
  [Category.{v₂} N'] [InitiallySmall.{w} N'] {p : N ⥤ C} {p' : N' ⥤ C}

/-- Restriction along `e.op` of colimits indexed by `N'ᵒᵖ`, as a natural transformation between
the two functors `(Cᵒᵖ ⥤ Type w) ⥤ Type w` sending a presheaf to the colimit of its restriction
along a system. -/
private noncomputable def colimPre (e : N ⥤ N') (p' : N' ⥤ C) :
    (Functor.whiskeringLeft Nᵒᵖ Cᵒᵖ (Type w)).obj (e.op ⋙ p'.op) ⋙ colim ⟶
      (Functor.whiskeringLeft N'ᵒᵖ Cᵒᵖ (Type w)).obj p'.op ⋙ colim
    where
  app G := colimit.pre (p'.op ⋙ G) e.op
  naturality _ _ β := (colimit.pre_map (Functor.whiskerLeft p'.op β) e.op).symm

/-- The morphism of fibre functors induced by a functor `e : N ⥤ N'` between index categories
together with an identification `ε : e ⋙ p' ≅ p` of the systems: on germs it takes the class of
`f : p.obj i ⟶ Z` to the class of `ε.hom.app i ≫ f`, see
`Stacks.SitePoints.DeligneCriterion.fiberMap_app_fiberMk`. -/
private noncomputable def fiberMap (e : N ⥤ N') (ε : e ⋙ p' ≅ p) : fiber.{w} p ⟶ fiber.{w} p' :=
  Functor.whiskerLeft shrinkYoneda.{w}
    (Functor.whiskerRight
        ((Functor.whiskeringLeft Nᵒᵖ Cᵒᵖ (Type w)).map
          (show p.op ⟶ e.op ⋙ p'.op from NatTrans.op ε.hom))
        colim ≫
      colimPre e p')

/-- The composite of `Stacks.SitePoints.DeligneCriterion.fiberMap` with a structural map of the
colimit describing the source: `fiberMap e ε` restricted to the index `i` is precomposition with
`ε.hom.app i` followed by the structural map at `e.obj i`. -/
private lemma ι_fiberMap_app (e : N ⥤ N') (ε : e ⋙ p' ≅ p) {i : N} {Z : C} :
    colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj Z) (op i) ≫ (fiberMap e ε).app Z =
      (shrinkYoneda.{w}.obj Z).map (ε.hom.app i).op ≫
        colimit.ι (p'.op ⋙ shrinkYoneda.{w}.obj Z) (op (e.obj i)) := by
  dsimp only [fiberMap, colimPre, fiber, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.whiskeringLeft_obj_obj, colim_obj,
    Functor.assoc]
  rw [colimit.ι_map_assoc, colimit.ι_pre]
  rfl

private lemma fiberMap_app_fiberMk (e : N ⥤ N') (ε : e ⋙ p' ≅ p) {i : N} {Z : C}
    (f : p.obj i ⟶ Z) :
    (fiberMap e ε).app Z (fiberMk.{w} f) =
      fiberMk.{w} (show p'.obj (e.obj i) ⟶ Z from ε.hom.app i ≫ f) := by
  -- the ascription is load-bearing: it is what forces `congr_hom`'s implicit type arguments into
  -- the spelling `simp` needs below
  have h :
    ∀ x,
      (colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj Z) (op i) ≫ (fiberMap e ε).app Z) x =
        ((shrinkYoneda.{w}.obj Z).map (ε.hom.app i).op ≫
            colimit.ι (p'.op ⋙ shrinkYoneda.{w}.obj Z) (op (e.obj i)))
          x :=
    fun x ↦ congr_hom (ι_fiberMap_app e ε) x
  refine (h (shrinkYonedaObjObjEquiv.symm f)).trans ?_
  simp only [types_comp_apply, fiberMk, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]
  rfl

end FiberFunctor

/-! ### The tower of stages and the point it produces -/

section Tower

attribute [local instance] Stage.isCofiltered Stage.essentiallySmall

variable [Small.{w} C] [LocallySmall.{w} C] {J : GrothendieckTopology C} {X : C} {S : Sieve X}

omit [Small.{w, u} C] [LocallySmall.{w, v, u} C] in
/-- The index category of a stage is initially `w`-small, being essentially `w`-small. -/
private lemma instInitiallySmallStageM (A : Stage.{w, v, u} J S) : InitiallySmall.{w} A.M :=
  initiallySmall_of_essentiallySmall _

attribute [local instance] instInitiallySmallStageM

/-- The fibre functor of the system underlying a stage. -/
private noncomputable def fib (A : Stage.{w, v, u} J S) : C ⥤ Type w :=
  fiber.{w} A.q

/-- The morphism of fibre functors induced by a refinement of stages. -/
private noncomputable def step {A B : Stage.{w, v, u} J S} (ρ : Refines A B) : fib A ⟶ fib B :=
  fiberMap ρ.e ρ.ε

omit [Small.{w, u} C] in
private lemma step_app_fiberMk {A B : Stage.{w, v, u} J S} (ρ : Refines A B) {Z : C} {i : A.M}
    (f : A.q.obj i ⟶ Z) :
    (step ρ).app Z (fiberMk f) = fiberMk (show B.q.obj (ρ.e.obj i) ⟶ Z from ρ.ε.hom.app i ≫ f) :=
  fiberMap_app_fiberMk ρ.e ρ.ε f

/-- The tower of fibre functors of a tower of stages, as a functor `ℕ ⥤ (C ⥤ Type w)`. -/
private noncomputable def tower (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) : ℕ ⥤ (C ⥤ Type w) :=
  Functor.ofSequence (X := fun n ↦ fib (T n)) (fun n ↦ step (r n))

/-- The sequence of sets of sections over a fixed object `Z` of the tower of fibre functors: the
diagram in `Type w` whose colimit is the value at `Z` of the fibre functor of the tower. -/
private noncomputable abbrev towerAt (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) (Z : C) : ℕ ⥤ Type w :=
  (tower T r).flip.obj Z

/-- The section over `Z` of the `n`-th term of the tower given by a morphism out of the `n`-th
system. This is `fiberMk`, with its type spelled as a value of
`Stacks.SitePoints.DeligneCriterion.towerAt` so that the colimit API applies to it without
unfolding the tower. -/
private noncomputable def towerMk (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z : C}
    (f : (T n).q.obj i ⟶ Z) : (towerAt T r Z).obj n :=
  fiberMk (p := (T n).q) f

omit [Small.{w, u} C] in
private lemma towerMk_jointly_surjective (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {Z : C}
    (x : (towerAt T r Z).obj n) : ∃ (i : (T n).M) (f : (T n).q.obj i ⟶ Z), towerMk T r f = x :=
  fiberMk_jointly_surjective (p := (T n).q) x

omit [Small.{w, u} C] in
private lemma exists_of_towerMk_eq (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z : C}
    {f₁ f₂ : (T n).q.obj i ⟶ Z} (hf : towerMk T r f₁ = towerMk T r f₂) :
    ∃ (j : (T n).M) (c : j ⟶ i), (T n).q.map c ≫ f₁ = (T n).q.map c ≫ f₂ :=
  exists_of_fiberMk_eq_fiberMk hf

omit [Small.{w, u} C] in
private lemma towerMk_map_comp (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i j : (T n).M} (c : j ⟶ i) {Z : C}
    (f : (T n).q.obj i ⟶ Z) : towerMk T r ((T n).q.map c ≫ f) = towerMk T r f :=
  fiberMk_map_comp (T n).q c f

omit [Small.{w, u} C] in
/-- The transition map from the `n`-th to the `(n+1)`-st term of the tower, on the sections of the
form `towerMk`: it is composition with the identification of the systems. -/
private lemma towerAt_map_towerMk_succ (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z : C}
    (f : (T n).q.obj i ⟶ Z) :
    (towerAt T r Z).map (homOfLE (Nat.le_add_right n 1)) (towerMk T r f) =
      towerMk T r (show (T (n + 1)).q.obj ((r n).e.obj i) ⟶ Z from (r n).ε.hom.app i ≫ f) := by
  dsimp only [towerMk, towerAt, tower, Functor.flip_obj_map]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact step_app_fiberMk (r n) f

omit [Small.{w, u} C] in
/-- Functoriality of the tower in the object of `C`, on the sections of the form `towerMk`. -/
private lemma flip_map_app_towerMk (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z Z' : C}
    (f : (T n).q.obj i ⟶ Z) (g : Z ⟶ Z') :
    ((tower T r).flip.map g).app n (towerMk T r f) = towerMk T r (f ≫ g) := by
  dsimp only [towerMk, towerAt, tower, fib, Functor.flip_map_app, Functor.ofSequence_obj]
  exact fiber_map_fiberMk _ f g

/-- The fibre functor of the whole tower: the colimit of the fibre functors of its stages,
computed pointwise via `CategoryTheory.Functor.flip`. -/
private noncomputable def bigFiber (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) : C ⥤ Type w :=
  (tower T r).flip ⋙ colim

/-- The section of `Stacks.SitePoints.DeligneCriterion.bigFiber` over `Z` given by a morphism `f`
out of the system of the `n`-th stage. -/
private noncomputable def bigMk (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z : C}
    (f : (T n).q.obj i ⟶ Z) : (bigFiber T r).obj Z :=
  colimit.ι (towerAt T r Z) n (towerMk T r f)

omit [Small.{w, u} C] in
private lemma bigMk_jointly_surjective (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {Z : C} (x : (bigFiber T r).obj Z) :
    ∃ (n : ℕ) (i : (T n).M) (f : (T n).q.obj i ⟶ Z), bigMk T r f = x := by
  obtain ⟨n, y, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (towerAt T r Z)) x
  obtain ⟨i, f, rfl⟩ := towerMk_jointly_surjective T r y
  exact ⟨n, i, f, rfl⟩

omit [Small.{w, u} C] in
private lemma bigFiber_map_bigMk (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z Z' : C}
    (f : (T n).q.obj i ⟶ Z) (g : Z ⟶ Z') :
    (bigFiber T r).map g (bigMk T r f) = bigMk T r (f ≫ g) := by
  refine (congr_hom (colimit.ι_map ((tower T r).flip.map g) n) (towerMk T r f)).trans ?_
  rw [CategoryTheory.comp_apply, flip_map_app_towerMk]
  rfl

omit [Small.{w, u} C] in
/-- Precomposition with a transition map of the system does not change the section of `bigFiber`
determined by a morphism out of the system. -/
private lemma bigMk_map_comp (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i j : (T n).M} (c : j ⟶ i) {Z : C}
    (f : (T n).q.obj i ⟶ Z) : bigMk T r ((T n).q.map c ≫ f) = bigMk T r f := by
  dsimp only [bigMk]
  rw [towerMk_map_comp]

omit [Small.{w, u} C] in
/-- Passing from a stage to the next one does not change the section of `bigFiber` determined by
a morphism out of the system. -/
private lemma bigMk_step (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {i : (T n).M} {Z : C}
    (f : (T n).q.obj i ⟶ Z) :
    bigMk T r (show (T (n + 1)).q.obj ((r n).e.obj i) ⟶ Z from (r n).ε.hom.app i ≫ f) =
      bigMk T r f := by
  dsimp only [bigMk]
  rw [← towerAt_map_towerMk_succ T r f, colimit.w_apply]

/-- A *descent datum* from the `n`-th to the `m`-th stage of a tower of stages (`n ≤ m`): the
composite of the refinements `r n, …, r (m-1)`, packaged as a single datum.

It is a `Stacks.SitePoints.DeligneCriterion.Refines` in which the identification of the systems has
been weakened to a natural transformation, the covering property has been forgotten, and the
description on germs of the transition map of the tower of fibre functors has been added. Bundling
it lets the induction which produces it (`Stacks.SitePoints.DeligneCriterion.nonempty_descent`)
compose two data and do nothing else; and because the comparison `hnm` is a parameter rather than a
field, proof irrelevance makes the datum produced by
`Stacks.SitePoints.DeligneCriterion.Descent.step` land in the very type the induction asks for, so
no datum is ever transported along an equality of natural numbers. -/
private structure Descent (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n m : ℕ} (hnm : n ≤ m) where
  /-- the functor of index categories -/
  E : (T n).M ⥤ (T m).M
  /-- the earlier system is the restriction of the later one -/
  κ : E ⋙ (T m).q ⟶ (T n).q
  /-- a transition map from the later base to the image of the earlier one -/
  ψ : (T m).base ⟶ E.obj (T n).base
  /-- the structural morphisms are compatible -/
  θ_eq : (T m).q.map ψ ≫ κ.app (T n).base ≫ (T n).θ = (T m).θ
  /-- on germs, the transition map of the tower is composition with `κ` -/
  map_towerMk :
    ∀ (Z : C) (i : (T n).M) (f : (T n).q.obj i ⟶ Z),
      (towerAt T r Z).map (homOfLE hnm) (towerMk T r f) =
        towerMk T r (show (T m).q.obj (E.obj i) ⟶ Z from κ.app i ≫ f)

omit [Small.{w, u} C] in
/-- Naturality of `κ`, in the form the germs are written in: a transition map of the earlier
system, transported along `E`, may be absorbed into the morphism it precedes. -/
private lemma Descent.map_comp_κ_app {T : ℕ → Stage.{w, v, u} J S}
    {r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))} {n m : ℕ} {hnm : n ≤ m}
    (D : Descent T r hnm) {i j : (T n).M} (c : j ⟶ i) {Z : C} (f : (T n).q.obj i ⟶ Z) :
    (T m).q.map (D.E.map c) ≫ D.κ.app i ≫ f = D.κ.app j ≫ (T n).q.map c ≫ f := by
  simpa only [Category.assoc, Functor.comp_map] using D.κ.naturality c =≫ f

omit [Small.{w, u} C] in
/-- The germ in the fibre functor of the tower determined by a morphism out of the `n`-th system
is unchanged by descending that morphism to the `m`-th. -/
private lemma Descent.bigMk_eq {T : ℕ → Stage.{w, v, u} J S}
    {r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))} {n m : ℕ} {hnm : n ≤ m}
    (D : Descent T r hnm) {i : (T n).M} {Z : C} (f : (T n).q.obj i ⟶ Z) :
    bigMk T r (show (T m).q.obj (D.E.obj i) ⟶ Z from D.κ.app i ≫ f) = bigMk T r f := by
  dsimp only [bigMk]
  rw [← D.map_towerMk Z i f, colimit.w_apply]

/-- A descent datum to the `m`-th stage, followed by the refinement of the `m`-th stage by the
`(m+1)`-st, is a descent datum to the `(m+1)`-st. -/
private def Descent.step {T : ℕ → Stage.{w, v, u} J S}
    {r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))} {n m : ℕ} {hnm : n ≤ m}
    (D : Descent T r hnm) : Descent T r (hnm.trans (Nat.le_succ m))
    where
  E := D.E ⋙ (r m).e
  κ := Functor.whiskerLeft D.E (r m).ε.hom ≫ D.κ
  ψ := (r m).ψ ≫ (r m).e.map D.ψ
  θ_eq := by
    have hnat := (r m).ε.hom.naturality D.ψ
    dsimp at hnat ⊢
    simp [reassoc_of% hnat, D.θ_eq, (r m).θ_eq]
  map_towerMk Z i f := by
    have hcomp :
      homOfLE (hnm.trans (Nat.le_succ m)) = homOfLE hnm ≫ homOfLE (Nat.le_add_right m 1) := rfl
    rw [hcomp, CategoryTheory.Functor.map_comp, CategoryTheory.comp_apply, D.map_towerMk Z i f,
      towerAt_map_towerMk_succ]
    simp

omit [Small.{w, u} C] in
/-- Every stage of a tower receives a descent datum from every earlier stage. -/
private lemma nonempty_descent (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n m : ℕ} (hnm : n ≤ m) :
    Nonempty (Descent T r hnm) := by
  induction m, hnm using Nat.le_induction with
  | base =>
    refine ⟨𝟭 _, 𝟙 _, 𝟙 _, by simp, fun Z i f ↦ ?_⟩
    rw [show homOfLE (le_refl n) = 𝟙 n from rfl, CategoryTheory.Functor.map_id]
    simp
  | succ m hnm ih => exact ⟨ih.some.step⟩

omit [Small.{w, u} C] in
/-- **The invariant of a stage, transported back along a descent datum.** No morphism to the
`m`-th stage's index of the image of the `n`-th stage's base, composed with `κ` and with the
`n`-th structural morphism, lies in the `J`-closure of `S`.

This is the only place where `Stacks.SitePoints.DeligneCriterion.Stage.notMem` is used, and it is
what the whole construction is for. The cofiltered index category of the `m`-th stage equalises the
given transition map with the descent datum's `ψ`; after that,
`Stacks.SitePoints.DeligneCriterion.Descent.θ_eq` turns the composite into one with the `m`-th
stage's own structural morphism, where the invariant applies. -/
private lemma Descent.notMem_close {T : ℕ → Stage.{w, v, u} J S}
    {r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))} {n m : ℕ} {hnm : n ≤ m}
    (D : Descent T r hnm) {j : (T m).M} (c : j ⟶ D.E.obj (T n).base) :
    ¬(J.close S) ((T m).q.map c ≫ D.κ.app (T n).base ≫ (T n).θ) := by
  intro hmem
  obtain ⟨p, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j (T m).base
  obtain ⟨p', t, ht⟩ := IsCofilteredOrEmpty.cone_maps (a ≫ c) (b ≫ D.ψ)
  have key := congrArg (T m).q.map ht =≫ (D.κ.app (T n).base ≫ (T n).θ)
  simp only [Functor.map_comp, Category.assoc] at key
  refine (T m).notMem p' (t ≫ b) ?_
  have hθ :
    (T m).q.map (t ≫ b) ≫ (T m).θ =
      (T m).q.map (t ≫ a) ≫ (T m).q.map c ≫ D.κ.app (T n).base ≫ (T n).θ := by
    simp only [Functor.map_comp, Category.assoc, ← D.θ_eq]
    exact key.symm
  rw [hθ]
  exact (J.close S).downward_closed hmem _

omit [Small.{w, u} C] in
/-- The germ of the structural morphism of a stage is the germ of the structural morphism of the
first stage: they differ by precomposition with a transition map, which
`Stacks.SitePoints.DeligneCriterion.bigMk_map_comp` erases. -/
private lemma bigMk_theta (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) (m : ℕ) :
    bigMk (C := C) T r (T m).θ = bigMk (C := C) T r (T 0).θ := by
  obtain ⟨D⟩ := nonempty_descent T r (Nat.zero_le m)
  rw [← D.θ_eq, ← D.bigMk_eq (T 0).θ]
  exact bigMk_map_comp T r D.ψ _

omit [Small.{w, u} C] in
/-- **Germs of the tower are separated at a finite stage.** Two germs given by morphisms out of
the *same* index of the `n`-th system are equal in the fibre functor of the tower only if some
later stage already equalises them.

This is the filtered-colimit criterion
`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'` for the tower, read through
`Stacks.SitePoints.DeligneCriterion.Descent.map_towerMk`. -/
private lemma exists_descent_comp_eq (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {Z : C} {i : (T n).M}
    {f₁ f₂ : (T n).q.obj i ⟶ Z} (hf : bigMk T r f₁ = bigMk T r f₂) :
    ∃ (m : ℕ) (hnm : n ≤ m) (D : Descent T r hnm) (j : (T m).M) (c : j ⟶ D.E.obj i),
      (T m).q.map c ≫ D.κ.app i ≫ f₁ = (T m).q.map c ≫ D.κ.app i ≫ f₂ := by
  obtain ⟨m, u, hu⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (towerAt T r Z)) (towerMk T r f₁)
          (towerMk T r f₂)).1
      hf
  obtain ⟨D⟩ := nonempty_descent T r (leOfHom u)
  have hu' :
    (towerAt T r Z).map (homOfLE (leOfHom u)) (towerMk T r f₁) =
      (towerAt T r Z).map (homOfLE (leOfHom u)) (towerMk T r f₂) :=
    hu
  rw [D.map_towerMk, D.map_towerMk] at hu'
  obtain ⟨j, c, hc⟩ := exists_of_towerMk_eq T r hu'
  exact ⟨m, leOfHom u, D, j, c, hc⟩

omit [Small.{w, u} C] in
/-- `Stacks.SitePoints.DeligneCriterion.exists_descent_comp_eq` for two germs out of *arbitrary*
indices of the `n`-th system: cofilteredness of the index category brings them to a common index
first. -/
private lemma exists_descent_comp_eq' (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n : ℕ} {Z : C} {i₁ i₂ : (T n).M}
    {f₁ : (T n).q.obj i₁ ⟶ Z} {f₂ : (T n).q.obj i₂ ⟶ Z} (hf : bigMk T r f₁ = bigMk T r f₂) :
    ∃ (m : ℕ) (hnm : n ≤ m) (D : Descent T r hnm) (j : (T m).M) (c₁ : j ⟶ D.E.obj i₁) (c₂ :
      j ⟶ D.E.obj i₂), (T m).q.map c₁ ≫ D.κ.app i₁ ≫ f₁ = (T m).q.map c₂ ≫ D.κ.app i₂ ≫ f₂ := by
  obtain ⟨k, d₁, d₂, -⟩ := IsCofilteredOrEmpty.cone_objs i₁ i₂
  obtain ⟨m, hnm, D, j, c, hc⟩ :=
    exists_descent_comp_eq T r
      (show bigMk T r ((T n).q.map d₁ ≫ f₁) = bigMk T r ((T n).q.map d₂ ≫ f₂) by
        rw [bigMk_map_comp, bigMk_map_comp]; exact hf)
  refine ⟨m, hnm, D, j, c ≫ D.E.map d₁, c ≫ D.E.map d₂, ?_⟩
  simp only [Functor.map_comp, Category.assoc, D.map_comp_κ_app]
  exact hc

omit [Small.{w, u} C] in
/-- A morphism out of the `m`-th system, made into a morphism of elements of
`Stacks.SitePoints.DeligneCriterion.bigFiber`: it carries the germ of the identity at its source to
the germ it descends from.

Every cone witnessing that the category of elements of `bigFiber` is cofiltered is of this form,
and this equation — where `Stacks.SitePoints.DeligneCriterion.Descent.bigMk_eq` absorbs the
descent — is all that has to be checked of it. -/
private lemma bigFiber_map_bigMk_id (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {n m : ℕ} {hnm : n ≤ m}
    (D : Descent T r hnm) {i : (T n).M} {j : (T m).M} (c : j ⟶ D.E.obj i) {Z : C}
    (f : (T n).q.obj i ⟶ Z) :
    (bigFiber T r).map ((T m).q.map c ≫ D.κ.app i ≫ f) (bigMk T r (𝟙 ((T m).q.obj j))) =
      bigMk T r f := by
  rw [bigFiber_map_bigMk, Category.id_comp, bigMk_map_comp, D.bigMk_eq]

omit [Small.{w, u} C] in
private lemma isCofilteredOrEmpty_elements_bigFiber (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) :
    IsCofilteredOrEmpty (bigFiber (C := C) T r).Elements
    where
  cone_objs := by
    rintro @⟨Z₁, x₁⟩ @⟨Z₂, x₂⟩
    obtain ⟨n₁, i₁, f₁, rfl⟩ := bigMk_jointly_surjective T r x₁
    obtain ⟨n₂, i₂, f₂, rfl⟩ := bigMk_jointly_surjective T r x₂
    obtain ⟨D₁⟩ := nonempty_descent T r (le_max_left n₁ n₂)
    obtain ⟨D₂⟩ := nonempty_descent T r (le_max_right n₁ n₂)
    obtain ⟨j, c₁, c₂, -⟩ := IsCofilteredOrEmpty.cone_objs (D₁.E.obj i₁) (D₂.E.obj i₂)
    exact
      ⟨(bigFiber T r).elementsMk ((T (max n₁ n₂)).q.obj j) (bigMk T r (𝟙 _)),
        Functor.Elements.homMk _ (bigFiber_map_bigMk_id T r D₁ c₁ f₁),
        Functor.Elements.homMk _ (bigFiber_map_bigMk_id T r D₂ c₂ f₂), trivial⟩
  cone_maps := by
    rintro @⟨Z₁, x₁⟩ @⟨Z₂, x₂⟩ g₁ g₂
    obtain ⟨n, i, f, rfl⟩ := bigMk_jointly_surjective T r x₁
    have hg : bigMk T r (f ≫ g₁.hom) = bigMk T r (f ≫ g₂.hom) := by
      rw [← bigFiber_map_bigMk T r f g₁.hom, ← bigFiber_map_bigMk T r f g₂.hom, g₁.map_val,
        g₂.map_val]
    obtain ⟨m, hnm, D, j, c, hc⟩ := exists_descent_comp_eq T r hg
    refine
      ⟨(bigFiber T r).elementsMk ((T m).q.obj j) (bigMk T r (𝟙 _)),
        Functor.Elements.homMk _ (bigFiber_map_bigMk_id T r D c f),
        Functor.Elements.hom_ext ?_⟩
    change ((T m).q.map c ≫ D.κ.app i ≫ f) ≫ g₁.hom = ((T m).q.map c ≫ D.κ.app i ≫ f) ≫ g₂.hom
    simpa only [Category.assoc] using hc

omit [Small.{w, u} C] in
private lemma isCofiltered_elements_bigFiber (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) :
    IsCofiltered (bigFiber (C := C) T r).Elements := by
  have := isCofilteredOrEmpty_elements_bigFiber (X := X) T r
  have : Nonempty (bigFiber (C := C) T r).Elements :=
    ⟨(bigFiber T r).elementsMk X (bigMk T r (T 0).θ)⟩
  exact {}

private lemma initiallySmall_elements_bigFiber (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) :
    InitiallySmall.{w} (bigFiber (C := C) T r).Elements := by
  have : Small.{w} (bigFiber (C := C) T r).Elements :=
    small_of_surjective.{w} (α := Σ Z : C, (bigFiber T r).obj Z)
      (f := fun x ↦ (bigFiber T r).elementsMk x.1 x.2) (fun x ↦ ⟨⟨x.obj, x.val⟩, rfl⟩)
  exact initiallySmall_of_essentiallySmall _

/-- The point of the site attached to a tower of stages: the colimit of the fibre functors of its
stages. Joint surjectivity for an arbitrary covering sieve comes from joint surjectivity for the
finite coverings, which every covering sieve contains by hypothesis. -/
private noncomputable def bigPoint (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1)))
    (h :
      ∀ ⦃X : C⦄ (S : Sieve X),
        S ∈ J X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → C) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ J X) :
    GrothendieckTopology.Point.{w} J
    where
  fiber := bigFiber T r
  isCofiltered := isCofiltered_elements_bigFiber (X := X) T r
  initiallySmall := initiallySmall_elements_bigFiber (X := X) T r
  jointly_surjective {Z} R hR x := by
    obtain ⟨n, i, f, rfl⟩ := bigMk_jointly_surjective T r x
    obtain ⟨ι, _, Y, g, hle, hg⟩ := h R hR
    obtain ⟨k, i', φ, a, ha⟩ := (r n).cover g hg i f
    refine ⟨Y k, g k, hle _ (Sieve.ofArrows_mk Y g k), bigMk T r a, ?_⟩
    rw [bigFiber_map_bigMk, ha, bigMk_map_comp]
    exact bigMk_step T r f

omit [Small.{w, u} C] in
/-- **The distinguished germ is not hit by `S`.** The germ over `X` of the structural morphism of
the first stage is not the image, under any member `g` of `S`, of a germ of the fibre functor of
the tower.

Were it, the two germs would already agree at some stage `m`
(`Stacks.SitePoints.DeligneCriterion.exists_descent_comp_eq'`); the resulting composite ending in
`g` lies in the `J`-closure of `S`, and it is a composite of the `n`-th structural morphism with
`κ`, which `Stacks.SitePoints.DeligneCriterion.Descent.notMem_close` forbids. -/
private lemma bigMk_ne_bigMk_theta (T : ℕ → Stage.{w, v, u} J S)
    (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) {Y : C} (g : Y ⟶ X) (hg : S g) {n : ℕ}
    {i : (T n).M} (f : (T n).q.obj i ⟶ Y) : bigMk T r (f ≫ g) ≠ bigMk (C := C) T r (T 0).θ := by
  intro hy
  rw [← bigMk_theta T r n] at hy
  obtain ⟨m, hnm, D, j, c₁, c₂, hc⟩ := exists_descent_comp_eq' T r hy
  refine D.notMem_close c₂ ?_
  rw [← hc]
  simpa only [Category.assoc] using
    (J.close S).downward_closed (J.le_close S g hg) ((T m).q.map c₁ ≫ D.κ.app i ≫ f)

/-- Given a tower of stages, each refining the previous one, the colimit of the associated fibre
functors is a point of the site separating the distinguished germ over `X` from every germ coming
from a member of `S`. -/
private theorem exists_point_of_tower
    (h :
      ∀ ⦃X : C⦄ (S : Sieve X),
        S ∈ J X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → C) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ J X)
    (T : ℕ → Stage.{w, v, u} J S) (r : ∀ n : ℕ, Refines.{w, v, u} (T n) (T (n + 1))) :
    ∃ (p : GrothendieckTopology.Point.{w} J) (x : p.fiber.obj X),
      ∀ ⦃Y : C⦄ (g : Y ⟶ X), S g → ∀ (y : p.fiber.obj Y), p.fiber.map g y ≠ x := by
  refine ⟨bigPoint T r h, bigMk T r (T 0).θ, fun {Y} g hg y hy ↦ ?_⟩
  obtain ⟨n, i, f, rfl⟩ := bigMk_jointly_surjective T r y
  exact bigMk_ne_bigMk_theta T r g hg f ((bigFiber_map_bigMk T r f g).symm.trans hy)

end Tower

/-- **The heart of Deligne's criterion.** Let `(C, J)` be a site in which fibre products exist and
in which every covering sieve contains a finite covering. Then for every sieve `S` on an object `X`
which is *not* a covering sieve there is a point `p` of the site and a section `x` of its fibre
functor over `X` which is not in the image of any member of `S`.

The point is the fibre functor of the system obtained by refining the one-object system `X` along
`ω` by the main step of the criterion (Stacks 00YP), the germ kept distinct being that of the
`J`-closure of `S` in the sheaf of `J`-closed sieves. -/
private theorem exists_point_of_notMem [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C)
    (h :
      ∀ ⦃X : C⦄ (S : Sieve X),
        S ∈ J X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → C) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ J X)
    {X : C} (S : Sieve X) (hS : S ∉ J X) :
    ∃ (p : GrothendieckTopology.Point.{w} J) (x : p.fiber.obj X),
      ∀ ⦃Y : C⦄ (g : Y ⟶ X), S g → ∀ (y : p.fiber.obj Y), p.fiber.map g y ≠ x :=
  exists_point_of_tower h (stageTower J S hS) fun _ ↦ stepRefines _

@[sga "2 XIV 1.9" "special case"]
private theorem hasEnoughPoints_of_exists_finite_refinement_proof [HasPullbacks C] [Small.{w} C]
    [LocallySmall.{w} C] (J : GrothendieckTopology C) [HasSheafify J (Type w)]
    (h :
      ∀ ⦃X : C⦄ (S : Sieve X),
        S ∈ J X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → C) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ J X) :
    GrothendieckTopology.HasEnoughPoints.{w} J := by
  classical
  have : ∀ Z : C, Small.{w} (Sieve Z) := fun Z ↦ small_sieve Z
  choose pt xs hxs using fun (t : Σ Z : C, { S : Sieve Z // S ∉ J Z }) ↦
    exists_point_of_notMem J h t.2.1 t.2.2
  refine ⟨⟨ObjectProperty.ofObj pt, inferInstance, ?_⟩⟩
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' (fun {Z} T hT ↦ ?_)
  by_contra hmem
  obtain ⟨Y, g, hg, y, hy⟩ :=
    hT ⟨pt ⟨Z, T, hmem⟩, ObjectProperty.ofObj_apply pt ⟨Z, T, hmem⟩⟩ (xs ⟨Z, T, hmem⟩)
  exact hxs ⟨Z, T, hmem⟩ g hg y hy

end

end Stacks.SitePoints.DeligneCriterion

attribute [local instance] Stacks.SitePoints.DeligneCriterion.hasColimitsOfShapeOpOfInitiallySmall

attribute [local instance] Stacks.SitePoints.DeligneCriterion.instInitiallySmallStageM

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.SitePoints.DeligneCriterion in
/-- **Stacks 00YQ** (Deligne's criterion for the existence of enough points). Let `(C, J)` be a
site in which fibre products exist and in which every covering sieve `S` of an object `X` admits a
refinement by a finite covering — a finite family `g k : Y k ⟶ X` of morphisms of `S` which is
again a covering of `X`. Then the site has enough points: there is a small family of points of
`(C, J)` whose fibre functors jointly reflect isomorphisms of sheaves of sets.

The source asks for all finite limits in `C`; only the fibre products of the members of a finite
covering along an arbitrary morphism are used, whence `HasPullbacks C`. -/
@[stacks 00YQ "Deligne's criterion: a site with fibre products in which every covering has a finite
  refinement has enough points.",
  sga "4 VI 9.0",
  sga "4 VI 9.5" "existence of points",
  sga "2 XIV 1.9" "special case"]
public theorem hasEnoughPoints_of_exists_finite_refinement {C : Type u} [Category.{v} C]
    [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type w)]
    (h :
      ∀ ⦃X : C⦄ (S : Sieve X),
        S ∈ J X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → C) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ J X) :
    HasEnoughPoints.{w} J := by
  apply Stacks.SitePoints.DeligneCriterion.hasEnoughPoints_of_exists_finite_refinement_proof ;
      assumption

end

end CategoryTheory.GrothendieckTopology

end

/-!
# Deligne's criterion, localized on a family of objects covering the final object

Let `(C, J)` be a site and let `U : I → C` be a family of objects which covers the final object of
`Sh(C)`, i.e. the map `∐ᵢ h_{U i} → *` of sheaves of sets is surjective. In elementary terms this
says that for every object `W` of `C` the sieve of those morphisms `Z ⟶ W` whose source admits some
morphism `Z ⟶ U i` is a covering sieve, which is `GrothendieckTopology.CoversTop`.

Deligne's criterion (Stacks 00YQ) produces points on a site in which fibre products exist and every
covering admits a refinement by a *finite* covering. The finiteness condition is a strong one: it
fails already for the site of opens of a space which is not quasi-compact. This file states that it
suffices for it to hold on the localizations: if fibre products exist in each `C/U i` and every
covering of `C/U i` admits a finite refinement, then `(C, J)` has enough points.

The two halves of the argument are separately available. Deligne's criterion applied to `C/U i`
says that each localized site has enough points. A point of `C/U i` is the fibre functor
`V ↦ colim_j Mor(V_j, V)` of a cofiltered system `(V_j)_j` of objects of `C/U i`, and reading that
system in `C` through `Over.forget (U i)` gives the fibre functor `Y ↦ colim_j Mor(V_j, Y)` of a
point of `C` (Stacks 05V1). The union over `i` of the families of points so obtained is small
because `I` is, and it is a conservative family because a morphism of sheaves whose restriction to
each `C/U i` is an isomorphism is an isomorphism (Stacks 06UL): this is where the family `U` is
used, and it is the only place it is used.

## Main results

* `CategoryTheory.GrothendieckTopology.hasEnoughPoints_of_coversTop_of_exists_finite_refinement`:
  Stacks 0DW0, a site covered by objects whose localizations satisfy Deligne's criterion has enough
  points.

## Implementation notes

Four departures from the source's form.

* Hypothesis (2) of the source, that each `C/U i` satisfies the hypotheses of Stacks 00YQ, is
  spelled out as those hypotheses in the form Stacks 00YQ takes them here:
  `HasPullbacks (Over (U i))` in place of "finite limits exist in `C/U i`", since only the fibre
  products of the members of a finite covering along an arbitrary morphism are used; and `h i`, the
  finite refinement condition phrased for covering *sieves* — every covering sieve `S` of an object
  `X` of `C/U i` contains a finite family `g k : Y k ⟶ X` which is again a covering of `X`. Both
  reformulations are Stacks 00YQ's own, and are discussed there.
* Hypothesis (1), that `∐ᵢ h_{U i}` surjects onto the final object of `Sh(C)`, is phrased in the
  equivalent elementary form `J.CoversTop U`: for every `W`, the sieve `Sieve.ofObjects U W` of
  morphisms `Z ⟶ W` such that `Z` admits a morphism to some `U i` belongs to `J W`. The two agree
  because a section of `∐ᵢ h_{U i}` over `Z` is a morphism `Z ⟶ U i` for some `i`, with no
  compatibility to impose over the final sheaf, so surjectivity of `∐ᵢ h_{U i} → *` is local
  surjectivity of that sieve.
* The index type `I` is an arbitrary type which is `w`-small rather than a set. The `w`-smallness
  is used: the family of points produced is indexed by `I` together with the points of the
  `C/U i`, and "enough points" asks for a family which is a set, `ObjectProperty.Small.{w}`.
* Smallness is asked of the localizations rather than of `C`, because that is where the source puts
  hypothesis (2). `Small.{w} (Over (U i))` is Stacks 00YQ's smallness hypothesis for the site
  `C/U i`, and `LocallySmall.{w} C` is the only condition imposed on `C` itself: it is what makes
  the fibre functor `Y ↦ colim_j Mor(V_j, Y)` of the point of `C` produced from a point of `C/U i`
  take values in `Type w`, and it gives `LocallySmall.{w} (Over (U i))`, the other smallness
  hypothesis of Stacks 00YQ. `Small.{w} C` is not needed: nothing in the argument enumerates the
  objects of `C`, only those of the `C/U i`. Neither is `HasSheafify (J.over (U i)) (Type w)`, the
  remaining hypothesis of Stacks 00YQ, which follows from the two smallness conditions because a
  category which is `w`-small and `w`-locally small is `w`-essentially small, and sheafification of
  `Type w`-valued presheaves exists on an essentially small site.

Faithfulness, on the four points a reader should check against the source.

1. No hypothesis is dead: `hU` is what makes the family of points conservative (an isomorphism is
   detected on the `C/U i` only because they cover), `h` and `HasPullbacks (Over (U i))` are what
   supply the points at all, `Small.{w} (Over (U i))` is what keeps each of those families of
   points a set, `Small.{w} I` is what keeps their union a set, and `LocallySmall.{w} C` is what
   keeps the fibre functors `Type w`-valued.
2. The base is the source's: one Grothendieck topology `J` on one category `C`, and the localized
   topologies `J.over (U i)` are `J` restricted to `C/U i`, the source's site `C/U_i`; no auxiliary
   topology on `C` and no change of coefficients.
3. Nothing canonical is left unpinned: "has enough points" is Mathlib's `HasEnoughPoints.{w} J`,
   the existence of a `w`-small family of points of `(C, J)` whose fibre functors
   `Sheaf J (Type w) ⥤ Type w` jointly reflect isomorphisms, which is the source's conservative
   family of points (Stacks 00YJ) indexed by a set; and the objects `U i` are pinned by `hU`, not
   merely asserted to exist.
4. Not degenerate, and not a special case of Stacks 00YQ: let `X` be an infinite disjoint union of
   noetherian topological spaces `U i` and let `C = Opens X` carry its standard topology. Fibre
   products exist throughout (they are intersections), the `U i` cover the final object, and every
   covering of an open of `U i` has a finite refinement because every open of a noetherian space is
   quasi-compact; the conclusion is that a sheaf of sets on `X` is determined by its stalks. The
   covering `{U i → X}` itself has no finite refinement, so Stacks 00YQ does not apply to
   `Opens X`.

## References

* [Stacks 0DW0](https://stacks.math.columbia.edu/tag/0DW0), in the section "Criterion for existence
  of points" (Stacks 00YN); it uses Stacks 00YQ (Deligne's criterion,
  `hasEnoughPoints_of_exists_finite_refinement`) and Stacks 05V1 (points of `C/U` give points
  of `C`), through Stacks 06UL. The definition of a conservative family of points and of "enough
  points" is Stacks 00YJ.
* [SGA4], Exposé VI, appendix by Deligne.
-/

section

universe w v u
open CategoryTheory Limits

namespace Stacks.SitePoints.LocalizedCriterion

@[expose] public section

/-- Deligne's criterion (Stacks 00YQ) for a `w`-small site: if fibre products exist in `D` and
every covering sieve of an object of `D` contains a finite covering, then `(D, K)` has enough
points.

This is `GrothendieckTopology.hasEnoughPoints_of_exists_finite_refinement` with its hypothesis
`HasSheafify K (Type w)` discharged rather than assumed: a category which is `w`-small and
`w`-locally small is `w`-essentially small, and sheafification of `Type w`-valued presheaves exists
on an essentially small site. -/
@[sga "2 XIV 1.9" "special case"]
private theorem hasEnoughPoints_of_exists_finite_refinement' {D : Type u} [Category.{v} D]
    [HasPullbacks D] [Small.{w} D] [LocallySmall.{w} D] (K : GrothendieckTopology D)
    (h :
      ∀ ⦃X : D⦄ (S : Sieve X),
        S ∈ K X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → D) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ K X) :
    GrothendieckTopology.HasEnoughPoints.{w} K :=
  have : HasSheafify K (Type w) := hasSheafifyEssentiallySmallSite K (Type w)
  GrothendieckTopology.hasEnoughPoints_of_exists_finite_refinement K h

end

end Stacks.SitePoints.LocalizedCriterion

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.SitePoints.LocalizedCriterion in
/-- **Stacks 0DW0**. Let `(C, J)` be a site and let `U : I → C` be a family of objects, indexed by
a `w`-small type, which covers the final object of the topos of sheaves on `C`: for every object
`W` of `C`, the sieve of morphisms `Z ⟶ W` whose source `Z` admits a morphism to some `U i` is a
covering sieve. Assume that each localized site `C/U i` satisfies the hypotheses of Deligne's
criterion Stacks 00YQ: fibre products exist in `C/U i`, and every covering sieve `S` of an object
`X` of `C/U i` admits a refinement by a finite covering, i.e. contains a finite family
`g k : Y k ⟶ X` which is again a covering of `X`. Then `(C, J)` has enough points.

The finiteness condition is needed only on the localizations, so a site none of whose coverings
admits a finite refinement can still have enough points, as soon as it is covered by objects whose
localizations are coherent in Deligne's sense. -/
@[stacks 0DW0 "A site covered by objects whose localizations satisfy Deligne's criterion has
  enough points.", sga "2 XIV 1.9" "special case", sga "4 VI 4.12" "more general", sga "4 VI 9.0"]
public theorem hasEnoughPoints_of_coversTop_of_exists_finite_refinement {C : Type u}
    [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C} {I : Type*} [Small.{w} I]
    {U : I → C} [∀ i, HasPullbacks (Over (U i))] [∀ i, Small.{w} (Over (U i))] (hU : J.CoversTop U)
    (h :
      ∀ (i : I) ⦃X : Over (U i)⦄ (S : Sieve X),
        S ∈ (J.over (U i)) X →
          ∃ (ι : Type) (_ : Finite ι) (Y : ι → Over (U i)) (g : ∀ k, Y k ⟶ X),
            Sieve.ofArrows Y g ≤ S ∧ Sieve.ofArrows Y g ∈ (J.over (U i)) X) :
    HasEnoughPoints.{w} J :=
  have : ∀ i, GrothendieckTopology.HasEnoughPoints.{w} (J.over (U i)) := fun i =>
    hasEnoughPoints_of_exists_finite_refinement' (J.over (U i)) (h i)
  GrothendieckTopology.hasEnoughPoints_of_coversTop U hU

end

end CategoryTheory.GrothendieckTopology

end
