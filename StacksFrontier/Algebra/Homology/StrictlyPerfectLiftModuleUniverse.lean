module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08C6 at an arbitrary module universe

Let `X` be a ringed space, let `p : 𝒢 ⟶ ℱ` be an epimorphism of `𝒪_X`-modules and let
`f : ℰ ⟶ ℱ` be a morphism whose source is a direct summand of a finite free `𝒪_X`-module. Then
every point of `X` has an open neighbourhood `U` over which `f` factors through `p`
(Stacks 08C6). This file proves that with the module universe `w` of `ℰ`, `ℱ` and `𝒢`
*independent* of the ring universe `u` and of the space universe `v`, and with restriction to
`U` expressed as `SheafOfModules.over`, i.e. as restriction to the slice site over `U`.

## Main results

* `Stacks.SheafOfModules.exists_mem_forall_exists_preimage_top`: finitely many global sections
  of the target of an epimorphism of sheaves of modules on a space lift over one common open
  neighbourhood of any given point.
* `Stacks.SheafOfModules.exists_over_lift_of_retract_moduleULift`: the lifting statement in the
  form in which it is proved, namely with the hypothesis on `ℰ` spelled out as a retract of the
  universe lift of a finite biproduct of copies of the unit object.
* `StrictlyPerfect.exists_over_lift_of_isDirectSummandOfFiniteFree`: **Stacks 08C6** for a
  ringed space.

## Implementation notes

**Two carriers of this tag already exist, and this is a third.** They differ in the universes
and in the spelling of restriction, and none subsumes another.

* `AlgebraicGeometry.RingedSpace.exists_local_lift_of_isDirectSummandOfFiniteFree`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StrictlyPerfectLift.lean`) collapses all three
  universes (`RingedSpace.{u, u}`, `OXMod.{u, u, u}`) and restricts with
  `AlgebraicGeometry.RingedSpace.restrictModules`, the open-subspace restriction the
  pseudo-coherence development is phrased in.
* `StrictlyPerfect.exists_local_lift_of_isDirectSummandOfFiniteFree`
  (`StacksFrontier/Algebra/Homology/StrictlyPerfectRestriction.lean`) has the space universe free
  but the module universe equal to the ring universe, and restricts with
  `StrictlyPerfect.restrictModules`.
* The theorem here has all three universes independent and restricts with
  `SheafOfModules.over`.

**Why the module universe could not be freed before, and what frees it.** There is no finite
free object at module universe `w`: `StrictlyPerfect.finiteFree X n` is a biproduct of copies of
`𝒪_X`, whose sections are the rings, so it lives at `OXMod.{u, u} X` only. Accordingly
`StrictlyPerfect.IsDirectSummandOfFiniteFree` asks for a retract *after* lifting both objects
into `OXMod.{u, max w u} X` along `StrictlyPerfect.moduleULift`, and
`StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract` — the only route back to retract
data — holds exactly when `w = u`. So the proof cannot destructure the predicate into a retract
of a finite free module, and the earlier two carriers do not try.

What it can do is work with the retract where it lives. The lift of the finite biproduct is a
biproduct of copies of `Stacks.SheafOfModules.uliftUnit`, and a morphism out of that is still a
section of the target (`Stacks.SheafOfModules.uliftUnitHom`), which is all the source proof
needs; `biproduct.total` reassembles the `n` lifted sections into a morphism out of the lift of
`ℰ`, and `Stacks.SheafOfModules.moduleULiftFullyFaithful` brings the resulting factorisation
back down to module universe `w`. No morphism in the argument has a `max` in its type that is
not already in the retract's, and no finite free object at universe `w` is ever needed.

**The two instance hypotheses, and why they are not a weakening.**
`HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{w}` and the corresponding
`WEqualsLocallyBijective` do not synthesize when `w` is independent of the space universe: the
sub-instance that fails is `PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{w})`
(`Small`, `HasLimitsOfSize`, `PreservesLimits`, `HasFiniteLimits`, `HasMultiequalizer` and
`HasColimitsOfShape` all do synthesize). They are exactly the hypotheses under which
`SheafOfModules.{w}` is abelian, which is Stacks' standing convention for `Mod(𝒪_X)`, and they
are what turns `Epi p` into local surjectivity of `p` — the only use `Epi p` has here. They are
taken as hypotheses rather than traded for a universe collapse. This is an
instance-*availability* wall, not a typing one.

**Local surjectivity is taken site-theoretically.** `Stacks.SheafOfModules.EpiMono` supplies it
at an arbitrary module universe, and the covering sieve is turned into an open neighbourhood by
`Opens.mem_grothendieckTopology`. `TopCat.Presheaf.isLocallySurjective_iff` is *not* usable
here: it is declared with `{CC : C → Type v}` and `{X : TopCat.{v}}`, so the carrier universe of
the concrete category must equal the space universe, and that API alone would force a collapse.

**Additivity of the restriction functor** is not in Mathlib and is installed here as a `local
instance`; it holds by `rfl` componentwise.

## References

* [The Stacks Project, Lemma 20.46.4 (08C6)](https://stacks.math.columbia.edu/tag/08C6)
* [The Stacks Project, Section 6.16 (007S)](https://stacks.math.columbia.edu/tag/007S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.EpiMono

universe w u v

namespace Stacks.SheafOfModules

variable {Z : TopCat.{v}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restricting a section along two composable inclusions of opens is restriction along the
composite, whichever inclusion is used. -/
private theorem map_map_apply_eq {Y : Type*} [TopologicalSpace Y] {S : (Opens Y)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{w} S) {A B C : Opens Y} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (x : M.obj (op C)) : M.map f.op (M.map g.op x) = M.map h.op x :=
  (M.map_comp_apply _ _ _).symm.trans
    (M.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) x)

/-- **Finitely many** global sections of the target of an epimorphism of sheaves of modules on a
topological space lift over *one* open neighbourhood of any given point.

An epimorphism is locally surjective, so for each section the sieve of opens along which it
lifts covers the whole space, and a covering sieve of `Opens.grothendieckTopology` contains an
open around every point; the finitely many opens so produced are then intersected. This is the
only place where an open has to be shrunk, and the only place finiteness is used. -/
theorem exists_mem_forall_exists_preimage_top {F G : _root_.SheafOfModules.{w} R} (p : G ⟶ F)
    [Epi p] {n : ℕ} (m : ∀ _ : Fin n, F.val.obj (op ⊤)) (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧ ∀ j : Fin n, ∃ τ : G.val.obj (op V),
      p.val.app (op V) τ = F.val.map (homOfLE le_top : V ⟶ ⊤).op (m j) := by
  have key : ∀ j : Fin n, ∃ V : Opens Z, x ∈ V ∧ ∃ τ : G.val.obj (op V),
      p.val.app (op V) τ = F.val.map (homOfLE le_top : V ⟶ ⊤).op (m j) := by
    intro j
    obtain ⟨S, hS, hlift⟩ := exists_covering_of_epi p (V := ⊤) (m j)
    obtain ⟨V, i, hi, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hS x (by trivial)
    obtain ⟨τ, hτ⟩ := hlift i hi
    exact ⟨V, hxV, τ, hτ.trans
      (F.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) (m j))⟩
  choose V hxV τ hτ using key
  refine ⟨⨅ j, V j, ?_, fun j => ⟨G.val.map (homOfLE (iInf_le V j)).op (τ j), ?_⟩⟩
  · show (x : Z) ∈ (↑(⨅ j, V j) : Set Z)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxV
  · refine (PresheafOfModules.naturality_apply p.val (homOfLE (iInf_le V j)).op (τ j)).trans ?_
    rw [hτ j]
    exact map_map_apply_eq _ _ _ _ _

/-- Restriction to the slice site over an object is additive. It is a `local instance` because
Mathlib does not provide it and it is needed only to move a finite sum of morphisms through the
restriction functor. -/
local instance overFunctorAdditive (V : Opens Z) :
    (_root_.SheafOfModules.overFunctor.{w} R V).Additive where
  map_add := by intros; ext W y; rfl

/-- Stacks 08C6 in the form in which it is proved: if the universe lift of `ℰ` is a retract of
the universe lift of `⨁ (fun _ : Fin n => 𝒪)`, then a morphism `f : ℰ ⟶ ℱ` factors through an
epimorphism `p : 𝒢 ⟶ ℱ` after restriction to a small enough open neighbourhood of any point.

The retract gives `n` morphisms `aⱼ : ULift 𝒪 ⟶ ULift ℰ` and `n` morphisms
`bⱼ : ULift ℰ ⟶ ULift 𝒪` with `∑ⱼ bⱼ ≫ aⱼ = 𝟙` — that is `biproduct.total` pushed through the
universe lift, which is additive. Each `aⱼ ≫ ULift f` is a section of `ℱ`, these lift through
`p` over one common neighbourhood `V`, and `∑ⱼ bⱼ|_V ≫ (the lifted section)` is a factorisation
of `ULift f|_V` through `ULift p|_V`. Full faithfulness of the universe lift over the slice site
then produces the factorisation of `f|_V` itself. -/
theorem exists_over_lift_of_retract_moduleULift
    [HasFiniteBiproducts (_root_.SheafOfModules.{u} R)]
    {E F G : _root_.SheafOfModules.{w} R} (f : E ⟶ F) (p : G ⟶ F) [Epi p] {n : ℕ}
    (ρ : Retract ((moduleULift.{u, w} R).obj E)
      ((moduleULift.{w, u} R).obj (⨁ fun _ : Fin n => _root_.SheafOfModules.unit R)))
    (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧ ∃ l : E.over V ⟶ G.over V, l ≫ p.over V = f.over V := by
  classical
  let Uf : Fin n → _root_.SheafOfModules.{u} R := fun _ => _root_.SheafOfModules.unit R
  let a : ∀ j : Fin n, uliftUnit.{w} R ⟶ (moduleULift.{u, w} R).obj E := fun j =>
    (moduleULift.{w, u} R).map (biproduct.ι Uf j) ≫ ρ.r
  let b : ∀ j : Fin n, (moduleULift.{u, w} R).obj E ⟶ uliftUnit.{w} R := fun j =>
    ρ.i ≫ (moduleULift.{w, u} R).map (biproduct.π Uf j)
  have hterm : ∀ j : Fin n, b j ≫ a j =
      ρ.i ≫ (moduleULift.{w, u} R).map (biproduct.π Uf j ≫ biproduct.ι Uf j) ≫ ρ.r := by
    intro j
    simp only [a, b, CategoryTheory.Functor.map_comp, Category.assoc]
  have htot : ∑ j : Fin n, b j ≫ a j = 𝟙 ((moduleULift.{u, w} R).obj E) := by
    simp only [hterm]
    rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, ← CategoryTheory.Functor.map_sum,
      biproduct.total, CategoryTheory.Functor.map_id, Category.id_comp, ρ.retract]
  obtain ⟨V, hxV, hlift⟩ := exists_mem_forall_exists_preimage_top p
    (fun j => ((uliftUnitSection (a j ≫ (moduleULift.{u, w} R).map f)).eval (op ⊤)).down) x
  choose τ hτ using hlift
  let θ : ∀ j : Fin n, (((moduleULift.{u, w} R).obj G).over V).sections := fun j =>
    PresheafOfModules.sectionsMk (fun W => ULift.up (G.val.map W.unop.hom.op (τ j)))
      (fun {W W'} g => by
        show ULift.up (G.val.map g.unop.left.op (G.val.map W.unop.hom.op (τ j))) =
          ULift.up (G.val.map W'.unop.hom.op (τ j))
        exact congrArg ULift.up (map_map_apply_eq _ _ _ _ _))
  have hkey : ∀ j : Fin n, uliftUnitHom (θ j) ≫
      (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{u, w} R).map p) =
      (_root_.SheafOfModules.overFunctor R V).map (a j ≫ (moduleULift.{u, w} R).map f) := by
    intro j
    refine uliftUnit_hom_ext fun W => ?_
    have h1 : (uliftUnitHom (θ j)).val.app W (ULift.up (1 : (R.over V).obj.obj W)) =
        ULift.up (G.val.map W.unop.hom.op (τ j)) := by
      rw [uliftUnitHom_val_app]
      exact (uliftUnitHomApp_apply (θ j) W _).trans (one_smul _ _)
    have hL : (uliftUnitHom (θ j) ≫ (_root_.SheafOfModules.overFunctor R V).map
          ((moduleULift.{u, w} R).map p)).val.app W (ULift.up (1 : (R.over V).obj.obj W)) =
        ULift.up (p.val.app (op W.unop.left) (G.val.map W.unop.hom.op (τ j))) := by
      show ((moduleULift.{u, w} R).map p).val.app (op W.unop.left)
        ((uliftUnitHom (θ j)).val.app W (ULift.up (1 : (R.over V).obj.obj W))) = _
      rw [h1]
      rfl
    have hσ : (uliftUnitSection (a j ≫ (moduleULift.{u, w} R).map f)).val
          (op W.unop.left) =
        ULift.up (F.val.map (homOfLE le_top : W.unop.left ⟶ ⊤).op
          (((uliftUnitSection (a j ≫ (moduleULift.{u, w} R).map f)).eval (op ⊤)).down)) :=
      (PresheafOfModules.sections_property (uliftUnitSection
        (a j ≫ (moduleULift.{u, w} R).map f)) (homOfLE le_top : W.unop.left ⟶ ⊤).op).symm
    rw [hL]
    show ULift.up (p.val.app (op W.unop.left) (G.val.map W.unop.hom.op (τ j))) =
      (uliftUnitSection (a j ≫ (moduleULift.{u, w} R).map f)).val (op W.unop.left)
    rw [hσ]
    refine congrArg ULift.up ?_
    refine (PresheafOfModules.naturality_apply p.val W.unop.hom.op (τ j)).trans ?_
    rw [hτ j]
    exact map_map_apply_eq _ _ _ _ _
  have hl' : (∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map (b j) ≫
        uliftUnitHom (θ j)) ≫
        (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{u, w} R).map p) =
      (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{u, w} R).map f) :=
    calc (∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map (b j) ≫
          uliftUnitHom (θ j)) ≫
          (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{u, w} R).map p)
        = ∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map (b j) ≫
            (uliftUnitHom (θ j) ≫ (_root_.SheafOfModules.overFunctor R V).map
              ((moduleULift.{u, w} R).map p)) := by
          rw [Preadditive.sum_comp]
          exact Finset.sum_congr rfl fun j _ => Category.assoc _ _ _
      _ = ∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map (b j) ≫
            (_root_.SheafOfModules.overFunctor R V).map
              (a j ≫ (moduleULift.{u, w} R).map f) :=
          Finset.sum_congr rfl fun j _ =>
            congrArg (fun z => (_root_.SheafOfModules.overFunctor R V).map (b j) ≫ z) (hkey j)
      _ = ∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map
            (b j ≫ a j ≫ (moduleULift.{u, w} R).map f) :=
          Finset.sum_congr rfl fun j _ =>
            ((_root_.SheafOfModules.overFunctor R V).map_comp _ _).symm
      _ = (_root_.SheafOfModules.overFunctor R V).map
            (∑ j : Fin n, b j ≫ a j ≫ (moduleULift.{u, w} R).map f) := by
          rw [CategoryTheory.Functor.map_sum]
      _ = (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{u, w} R).map f) := by
          refine congrArg (fun z => (_root_.SheafOfModules.overFunctor R V).map z) ?_
          refine Eq.trans (Finset.sum_congr rfl fun j _ => (Category.assoc _ _ _).symm) ?_
          rw [← Preadditive.sum_comp, htot, Category.id_comp]
  obtain ⟨l, hl⟩ := exists_over_comp_eq_of_moduleULift V p f
    (∑ j : Fin n, (_root_.SheafOfModules.overFunctor R V).map (b j) ≫ uliftUnitHom (θ j)) hl'
  exact ⟨V, hxV, l, hl⟩

end Stacks.SheafOfModules

namespace StrictlyPerfect

variable {X : RingedSpace.{u, v}}
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 08C6.** Let `X` be a ringed space, `p : 𝒢 ⟶ ℱ` an epimorphism of `𝒪_X`-modules and
`f : ℰ ⟶ ℱ` a morphism out of a direct summand of a finite free `𝒪_X`-module. Then every point
of `X` has an open neighbourhood `U` and a morphism `l : ℰ|_U ⟶ 𝒢|_U` with `l ≫ p|_U = f|_U`.

The ring universe, the space universe and the module universe are independent; the price is the
two sheafification hypotheses, which are what make `Mod(𝒪_X)` abelian and are Stacks' standing
convention. See the module docstring for how the module universe is freed and for the two other
carriers of this tag. -/
@[stacks 08C6 "at an arbitrary module universe"]
theorem exists_over_lift_of_isDirectSummandOfFiniteFree {E F G : OXMod.{u, w} X} (f : E ⟶ F)
    (p : G ⟶ F) [Epi p] (hE : IsDirectSummandOfFiniteFree E) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ l : E.over U ⟶ G.over U, l ≫ p.over U = f.over U := by
  intro x
  obtain ⟨n, ⟨ρ⟩⟩ := hE
  exact Stacks.SheafOfModules.exists_over_lift_of_retract_moduleULift f p ρ x

end StrictlyPerfect

end
