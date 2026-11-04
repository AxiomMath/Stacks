module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local lifting of maps out of a retract of a free sheaf of modules, over a slice

`StrictlyPerfect.LocalLifting.exists_local_lift` lifts a map out of a direct summand of a finite
  free module on a
ringed space through an epimorphism, after restricting to a small enough open neighbourhood of
a point. That statement is about `structureSheafOfRings X` for a `RingedSpace X`, which is not
general enough for its intended consumers: in the induction proving
[Stacks, Tag 08C7](https://stacks.math.columbia.edu/tag/08C7) the lifting problem that has to
be solved lives over the *restricted* sheaf of rings `(structureSheafOfRings X).over U`, and
that is not of the form `structureSheafOfRings X'` for any ringed space `X'`.

This file restates the lemma over an arbitrary sheaf of rings on an arbitrary site, and in the
relative form that the induction consumes: the lifting problem is posed over the slice sheaf of
rings `R.over Y` and the conclusion is a covering sieve of `Y` in the *original* topology, with
a lift over each of its arrows `g : V ⟶ Y` taken along `SheafOfModules.overMap R g`. Using
`overMap` rather than restriction to a slice of `Over Y` is what keeps the statement free of
iterated slices: `SheafOfModules.overFunctorMap` identifies `overFunctor R Y ⋙ overMap R g`
with `overFunctor R V`, so a lift produced here can be read as a lift over `V` itself.

The proof is the Stacks argument, as in `StrictlyPerfect.LocalLifting.exists_local_lift`, with the
  two
space-specific steps replaced. A map out of `free I` is a family of global sections indexed by
`I` (`SheafOfModules.freeHomEquiv`); "global" means over the terminal object `Over.mk (𝟙 Y)` of
`Over Y`. Each of those sections lifts through the epimorphism along the arrows of a covering
sieve, because an epimorphism of sheaves of modules is locally surjective
(`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`). Since `I` is finite the intersection
of those sieves is still covering, where `Stacks.StrictlyPerfect.LocalLiftingOverSlice.iInf_mem`
  replaces the intersection of
finitely many open neighbourhoods. Along each arrow of the intersection all the chosen
preimages exist at once and assemble into a map `free I ⟶ P` over the smaller slice, which is
compared with the restriction of the free sheaf by `SheafOfModules.overMapFreeIso`. Composing
with the retract inclusion finishes.

## Main results

* `Stacks.StrictlyPerfect.LocalLiftingOverSlice.iInf_mem`: a finite intersection of covering sieves
  is covering.
* `Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift`: the lifting lemma over a slice.

## Implementation notes

The module universe is the ring universe, as in `StrictlyPerfect.LocalLifting.exists_local_lift`,
  because
`SheafOfModules.free` and the characterisation of epimorphisms as locally surjective maps are
both available only there.

The hypothesis on the source is `Retract M (free I)` for a finite `I`, rather than a
`StrictlyPerfect.IsDirectSummandOfFiniteFree` predicate, since the latter is stated for a
ringed space; `SheafOfModules.overFunctorFreeIso` is what converts between the two at the point
of use.

## References

* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.StrictlyPerfect.LocalLiftingOverSlice

universe v₁ u₁ u

section Sieves

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- **A finite intersection of covering sieves is covering.** This is
`CategoryTheory.GrothendieckTopology.intersection_covering` iterated over a finite index type,
and it replaces the intersection of finitely many open neighbourhoods used in the ringed-space
form of the lemma. -/
@[sga "4 II 1.1.1"]
lemma iInf_mem {X : C} {I : Type*} [Finite I] (S : I → Sieve X) (hS : ∀ i, S i ∈ J X) :
    (⨅ i, S i) ∈ J X := by
  classical
  cases nonempty_fintype I
  have key (t : Finset I) : t.inf S ∈ J X := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t _ ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hS i) ih
  rw [show (⨅ i, S i) = (Finset.univ : Finset I).inf S by simp [Finset.inf_eq_iInf]]
  exact key _

/-- If `g : V ⟶ Y` lies in `Sieve.overEquiv _ S`, then `S` contains the arrow
`Over.mk g ⟶ Over.mk (𝟙 Y)` induced by `g`. -/
lemma mem_of_mem_overEquiv {Y V : C} (S : Sieve (Over.mk (𝟙 Y))) {g : V ⟶ Y}
    (hg : Sieve.overEquiv (Over.mk (𝟙 Y)) S g) :
    S (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 Y)) := by
  have heq : (Over.homMk (𝟙 V) (by simp) : Over.mk g ⟶ Over.mk (g ≫ (Over.mk (𝟙 Y)).hom)) ≫
      (Over.homMk g : Over.mk (g ≫ (Over.mk (𝟙 Y)).hom) ⟶ Over.mk (𝟙 Y)) =
        Over.homMk g (by simp) := by
    ext
    simp
  rw [← heq]
  exact S.downward_closed ((Sieve.overEquiv_iff S g).mp hg) _

end Sieves

section Lift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasPullbacks C] {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

open _root_.SheafOfModules

/-- A section of `P` over `Over.mk g` gives a global section of `(overMap R g).obj P`, by
restricting it along the arrows `(Over.map g).obj W ⟶ Over.mk g`. -/
noncomputable def overMapSectionOfOver {Y : C} (P : SheafOfModules.{u} (R.over Y)) {V : C}
    (g : V ⟶ Y) (x : P.val.obj (op (Over.mk g))) : ((overMap.{u} R g).obj P).sections where
  val W := P.val.map (Over.homMk W.unop.hom : (Over.map g).obj W.unop ⟶ Over.mk g).op x
  property := by
    intro W Z h
    have harr : (Over.map g).map h.unop ≫
        (Over.homMk W.unop.hom : (Over.map g).obj W.unop ⟶ Over.mk g) =
          (Over.homMk Z.unop.hom : (Over.map g).obj Z.unop ⟶ Over.mk g) := by
      ext
      simp
    change P.val.map ((Over.map g).map h.unop).op
      (P.val.map (Over.homMk W.unop.hom : (Over.map g).obj W.unop ⟶ Over.mk g).op x) = _
    rw [← P.val.map_comp_apply, ← op_comp, harr]

/-- **Local lifting over a slice.** Let `M` be a retract of a free sheaf of `R.over Y`-modules
on a finite index type, let `p : P ⟶ N` be an epimorphism and let `f : M ⟶ N` be arbitrary.
Then there is a covering sieve of `Y` along each arrow `g : V ⟶ Y` of which `f` lifts through
`p` after extension along `g`.

This is `StrictlyPerfect.LocalLifting.exists_local_lift` over an arbitrary sheaf of rings on an
  arbitrary site,
and relative to an object `Y` rather than to the whole site. -/
theorem exists_local_lift {Y : C} {M N P : SheafOfModules.{u} (R.over Y)} (f : M ⟶ N)
    (p : P ⟶ N) [Epi p] {I : Type u} [Finite I] (ρ : Retract M (free I)) :
    ∃ S : Sieve Y, S ∈ J Y ∧ ∀ ⦃V : C⦄ (g : V ⟶ Y), S g →
      ∃ l : (overMap.{u} R g).obj M ⟶ (overMap.{u} R g).obj P,
        l ≫ (overMap.{u} R g).map p = (overMap.{u} R g).map f := by
  classical
  -- `TY` is the terminal object of `Over Y`, where the global sections of a sheaf live.
  let TY : Over Y := Over.mk (𝟙 Y)
  let q : free (R := R.over Y) I ⟶ N := ρ.r ≫ f
  let s : I → N.sections := N.freeHomEquiv q
  -- Each of the `I`-many global sections of `N` defining `q` lifts along a covering sieve.
  choose S hS hSlift using fun i : I =>
    Stacks.SheafOfModules.EpiMono.exists_covering_of_epi p ((s i).val (op TY))
  refine ⟨⨅ i, Sieve.overEquiv TY (S i), iInf_mem J _ hS, ?_⟩
  intro V g hg
  -- The unique arrow `Over.mk g ⟶ TY`, along which all the sections are in the image.
  let θ : Over.mk g ⟶ TY := Over.homMk g (by simp [TY])
  have hSθ (i : I) : S i θ :=
    mem_of_mem_overEquiv (S i) (iInf_le (fun i => Sieve.overEquiv TY (S i)) i g hg)
  choose t ht using fun i => hSlift i θ (hSθ i)
  change ∀ i, P.val.obj (op (Over.mk g)) at t
  -- The chosen preimages assemble into `I`-many sections of `P` over the smaller slice.
  let τ : I → ((overMap.{u} R g).obj P).sections := fun i => overMapSectionOfOver P g (t i)
  let k : free (R := R.over V) I ⟶ (overMap.{u} R g).obj P :=
    ((overMap.{u} R g).obj P).freeHomEquiv.symm τ
  have hk : k ≫ (overMap.{u} R g).map p =
      (overMapFreeIso R g I).hom ≫ (overMap.{u} R g).map q := by
    apply ((overMap.{u} R g).obj N).freeHomEquiv.injective
    funext i
    rw [freeHomEquiv_comp_apply]
    dsimp only [k]
    rw [Equiv.apply_symm_apply]
    change sectionsMap ((overMap.{u} R g).map p) (τ i) =
      ((overMap.{u} R g).obj N).unitHomEquiv
        (ιFree i ≫ (overMapFreeIso R g I).hom ≫ (overMap.{u} R g).map q)
    rw [ιFree_overMapFreeIso_hom'_assoc R g I i ((overMap.{u} R g).map q)]
    apply PresheafOfModules.sections_ext
    intro W
    change p.val.app (op ((Over.map g).obj W.unop))
        (P.val.map (Over.homMk W.unop.hom : (Over.map g).obj W.unop ⟶ Over.mk g).op (t i)) =
      (s i).val (op ((Over.map g).obj W.unop))
    rw [PresheafOfModules.naturality_apply]
    have hti : p.val.app (op (Over.mk g)) (t i) = N.val.map θ.op ((s i).val (op TY)) := ht i
    have hsθ : N.val.map θ.op ((s i).val (op TY)) = (s i).val (op (Over.mk g)) :=
      (s i).property θ.op
    rw [hti, hsθ]
    exact (s i).property
      (Over.homMk W.unop.hom : (Over.map g).obj W.unop ⟶ Over.mk g).op
  refine ⟨(overMap.{u} R g).map ρ.i ≫ (overMapFreeIso R g I).inv ≫ k, ?_⟩
  rw [Category.assoc, Category.assoc, hk, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  congr 1
  rw [show q = ρ.r ≫ f from rfl, ← Category.assoc, ρ.retract, Category.id_comp]

end Lift

end Stacks.StrictlyPerfect.LocalLiftingOverSlice

end
