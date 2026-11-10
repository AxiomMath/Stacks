module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent

/-!
# Trivializing a module over a pairwise disjoint open cover

A module which is trivial on each member of an open cover need not be trivial on the union: the
transition data on the overlaps is exactly the obstruction. When the cover is **pairwise
disjoint** there are no overlaps, and the obstruction vanishes for free. This file records that
fact in the form consumed by the star-shaped cover of a one-dimensional scheme: a family of
generators, one over each member of a pairwise disjoint open cover of an open `W`, glues to a
single generator over `W`.

## Why this is needed

A reducible scheme has one generic point per irreducible component, and a trivializing open
neighbourhood of one of them need not contain the others. The centre of the star-shaped cover of
`StacksFrontier/AlgebraicGeometry/LiftInvertible/StarCover.lean` therefore has to be assembled
from one open per component, and those can be taken pairwise disjoint
(`Stacks.Topology.Dimension.exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one`).
The only thing the centre is asked for is a generator of the module over its inverse image, so
the per-component problem is reduced to this gluing.

## Main results

* `Stacks.SheafOfModules.exists_map_eq_of_pairwise_disjoint_sheaf`: a family of sections of a
  sheaf valued in a suitable concrete category, indexed by a pairwise disjoint open cover of an
  open `W`, glues to a section over `W`. No compatibility hypothesis: two distinct members meet
  in `⊥`, where a sheaf has at most one section.
* `Stacks.SheafOfModules.nonempty_generatorSections_of_pairwise_disjoint`: generators over the
  members of a pairwise disjoint open cover of `W` glue to a generator over `W`.

## Implementation notes

The gluing lemma is stated for an arbitrary sheaf rather than twice, because the proof below
needs it for the module `L` (`AddCommGrpCat`-valued) *and* for the ring sheaf of scalars
(`RingCat`-valued, in the spelling `_root_.structureSheaf X.sheaf` in which
`Stacks.SheafOfModules.GeneratorSections` states its bijectivity condition). Note
`_root_.structureSheaf`: the bare name collides with `AlgebraicGeometry.structureSheaf`.

Emptiness of the overlaps is used through `TopCat.Sheaf.eq_of_locally_eq'` with an `Empty`-indexed
cover rather than through `TopCat.Presheaf.section_ext`, whose concrete-category hypotheses
(`Limits.HasColimits`, `Limits.PreservesFilteredColimits (forget C)`) do not hold of a general
`C`.

Restrictions of sections are written through `PresheafOfModules.restrictₛₗ`, not through
`L.val.map`: the latter lands in a `ModuleCat.restrictScalars` of the target, and the scalar
action on it does not elaborate. `Stacks.SheafOfModules.map_restrict_comp` and
`Stacks.SheafOfModules.map_smul_restrict` of
`StacksFrontier/AlgebraicGeometry/PicardGroup/Descent.lean` do apply at this spelling in
*argument* position and are used rather than restated wherever that works. The two uses under
`rw`, which matches syntactically, need the restatements `map_smul_restrictₛₗ` and
`map_restrict_compₛₗ`, each one line and each discharged by the `L.val.map` form in argument
position.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Set TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- **Sections over a pairwise disjoint open cover of an open `W` glue to a section over `W`.**
The compatibility hypothesis of the sheaf condition is vacuous: two distinct members of the cover
meet in `⊥`, where a sheaf has at most one section.

This is the relative form — over an arbitrary open rather than over `⊤` — of
`Stacks.SheafOfModules.exists_sections_eval_eq_of_pairwise_disjoint`, and it is stated for a
general sheaf because it is needed both for a sheaf of modules and for its sheaf of scalars. -/
theorem exists_map_eq_of_pairwise_disjoint_sheaf {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u} [∀ A B, FunLike (FC A B) (CC A) (CC B)]
    [ConcreteCategory C FC] [Limits.HasLimitsOfSize.{u, u} C]
    [(forget C).ReflectsIsomorphisms] [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {ι : Type*} (U : ι → Opens T) (W : Opens T)
    (hUW : ∀ i, U i ≤ W) (hcover : W ≤ ⨆ i, U i)
    (hdisj : Pairwise (Function.onFun Disjoint U))
    (a : ∀ i, ToType (F.1.obj (op (U i)))) :
    ∃ s : ToType (F.1.obj (op W)), ∀ i, (F.1.map (homOfLE (hUW i)).op) s = a i := by
  classical
  have hc : TopCat.Presheaf.IsCompatible F.1 U a := by
    intro i j
    by_cases h : i = j
    · subst h
      rfl
    · exact F.eq_of_locally_eq' (fun _ : Empty => (⊥ : Opens T)) (U i ⊓ U j)
        (fun e => e.elim) ((hdisj h).le_bot.trans bot_le) _ _ (fun e => e.elim)
  exact (F.existsUnique_gluing' U W (fun i => homOfLE (hUW i)) hcover a hc).exists

section RingedSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (_root_.structureSheaf X.sheaf))

/-- `Stacks.SheafOfModules.map_smul_restrict` with both module terms written through
`PresheafOfModules.restrictₛₗ`. The two spellings are equal by `rfl` but not as terms, so `rw`
does not fire across them; this states the law once at the spelling in which the scalar action on
a restricted section elaborates. -/
theorem map_smul_restrictₛₗ {V W : Opens X.carrier} (h : V ≤ W)
    (r : (_root_.structureSheaf X.sheaf).obj.obj (op W)) (x : L.val.obj (op W)) :
    L.val.restrictₛₗ (homOfLE h).op (r • x) =
      ((_root_.structureSheaf X.sheaf).obj.map (homOfLE h).op r) •
        L.val.restrictₛₗ (homOfLE h).op x :=
  map_smul_restrict L h r x

/-- `Stacks.SheafOfModules.map_restrict_comp` with every module term written through
`PresheafOfModules.restrictₛₗ`, for the same reason. -/
theorem map_restrict_compₛₗ {P Q R : Opens X.carrier} (hQP : Q ≤ P) (hPR : P ≤ R)
    (a : L.val.obj (op R)) :
    L.val.restrictₛₗ (homOfLE hQP).op (L.val.restrictₛₗ (homOfLE hPR).op a) =
      L.val.restrictₛₗ (homOfLE (hQP.trans hPR)).op a :=
  map_restrict_comp L hQP hPR a

/-- **Generators over a pairwise disjoint open cover glue.** If `L` is generated over each member
of a pairwise disjoint family of opens covering `W`, it is generated over `W`.

Both halves of the generator condition are local on the cover: injectivity of multiplication by
the glued section descends from injectivity on the pieces by separatedness of the sheaf of
scalars, and surjectivity by gluing the coefficients found on the pieces — which is again free,
the pieces being disjoint. -/
theorem nonempty_generatorSections_of_pairwise_disjoint {ι : Type*} (U : ι → Opens X.carrier)
    (W : Opens X.carrier) (hUW : ∀ i, U i ≤ W) (hcover : W ≤ ⨆ i, U i)
    (hdisj : Pairwise (Function.onFun Disjoint U))
    (g : ∀ i, GeneratorSections X L (U i)) :
    Nonempty (GeneratorSections X L W) := by
  classical
  let FL : TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
    ⟨L.val.presheaf, _root_.SheafOfModules.isSheaf L⟩
  let FR : TopCat.Sheaf RingCat.{u} X.carrier := _root_.structureSheaf X.sheaf
  obtain ⟨s, hs⟩ :=
    exists_map_eq_of_pairwise_disjoint_sheaf FL U W hUW hcover hdisj (fun i => (g i).val)
  have hs' : ∀ i, L.val.map (homOfLE (hUW i)).op s = (g i).val := hs
  refine ⟨⟨s, fun V hV => ?_⟩⟩
  -- the cover of `V` induced by the cover of `W`
  set P : ι → Opens X.carrier := fun i => V ⊓ U i
  have hPV : ∀ i, P i ≤ V := fun _ => inf_le_left
  have hPU : ∀ i, P i ≤ U i := fun _ => inf_le_right
  have hPcover : V ≤ ⨆ i, P i := fun x hx =>
    let ⟨i, hi⟩ := Opens.mem_iSup.1 (hcover (hV hx))
    Opens.mem_iSup.2 ⟨i, hx, hi⟩
  have hPdisj : Pairwise (Function.onFun Disjoint P) := fun i j h =>
    (hdisj h).mono inf_le_right inf_le_right
  -- the glued section restricts to the given generator on every piece
  have hsP : ∀ i, L.val.restrictₛₗ (homOfLE ((hPV i).trans hV)).op s =
      L.val.restrictₛₗ (homOfLE (hPU i)).op ((g i).val) := by
    intro i
    rw [← hs' i]
    exact (map_restrict_comp L (hPU i) (hUW i) s).symm
  -- multiplication by the glued section is bijective on every piece
  have hbijP : ∀ i, Function.Bijective
      (fun r : (_root_.structureSheaf X.sheaf).obj.obj (op (P i)) =>
        r • L.val.restrictₛₗ (homOfLE ((hPV i).trans hV)).op s) := by
    intro i
    rw [funext fun r => congrArg (fun y => r • y) (hsP i)]
    exact (g i).property (P i) (hPU i)
  -- restriction of a scalar multiple of the glued section
  have hmul : ∀ (i : ι) (r : (_root_.structureSheaf X.sheaf).obj.obj (op V)),
      L.val.restrictₛₗ (homOfLE (hPV i)).op (r • L.val.restrictₛₗ (homOfLE hV).op s) =
        ((_root_.structureSheaf X.sheaf).obj.map (homOfLE (hPV i)).op r) •
          L.val.restrictₛₗ (homOfLE ((hPV i).trans hV)).op s := by
    intro i r
    rw [map_smul_restrictₛₗ L (hPV i) r, map_restrict_compₛₗ L (hPV i) hV s]
  refine ⟨fun r r' hrr' => ?_, fun m => ?_⟩
  · refine FR.eq_of_locally_eq' P V (fun i => homOfLE (hPV i)) hPcover r r' fun i => ?_
    refine (hbijP i).injective ?_
    rw [← hmul i r, ← hmul i r']
    exact congrArg (L.val.restrictₛₗ (homOfLE (hPV i)).op) hrr'
  · have hex : ∀ i, ∃ c : (_root_.structureSheaf X.sheaf).obj.obj (op (P i)),
        c • L.val.restrictₛₗ (homOfLE ((hPV i).trans hV)).op s =
          L.val.restrictₛₗ (homOfLE (hPV i)).op m := fun i => (hbijP i).surjective _
    choose c hcmem using hex
    obtain ⟨r, hr⟩ := exists_map_eq_of_pairwise_disjoint_sheaf FR P V hPV hPcover hPdisj c
    have hr' : ∀ i, (_root_.structureSheaf X.sheaf).obj.map (homOfLE (hPV i)).op r = c i := hr
    refine ⟨r, FL.eq_of_locally_eq' P V (fun i => homOfLE (hPV i)) hPcover _ m fun i => ?_⟩
    change L.val.restrictₛₗ (homOfLE (hPV i)).op (r • L.val.restrictₛₗ (homOfLE hV).op s) =
      L.val.restrictₛₗ (homOfLE (hPV i)).op m
    rw [hmul i r, hr' i, hcmem i]

end RingedSpace

end Stacks.SheafOfModules

end
