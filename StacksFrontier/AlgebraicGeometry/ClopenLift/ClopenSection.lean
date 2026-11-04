module

public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# A section of an invertible module cutting out a clopen point

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. If `x : X` is a point whose singleton
`{x}` is both open and closed, then there is a global section `s ∈ Γ(X, L)` whose nonvanishing
locus is exactly `{x}`.

This is the step of the proof of [Stacks, Tag 0B5P] that is performed on the auxiliary closed
subscheme. In the source the auxiliary subscheme is the reduced closed subscheme on
`Z' = (X ∖ U) ∪ {x}` for `U` an affine open containing the closed point `x`, and the whole point
of that choice is that `x` becomes an *isolated* closed point of `Z'`: the source computes
`Γ(Z', 𝒪_{Z'}) = A/𝔪 × (…)` and picks the idempotent. The construction below is the sheaf-level
form of that computation and needs no ring theory: `{x}` and its complement are two disjoint
opens covering `X`, so a local basis section of `L` over `{x}` and the zero section over the
complement are vacuously compatible and glue.

## Main results

* `Stacks.Tag0B5PClopenLift.exists_resTop_eq_of_disjoint_cover`: the gluing. For two disjoint
  opens covering `X`, every section of an `𝒪_X`-module over the first extends to a global
  section restricting to zero on the second.
* `Stacks.Tag0B5PClopenLift.exists_nonvanishingLocus_eq_singleton`: **a global section of an
  invertible module whose nonvanishing locus is a prescribed clopen point.**

## Implementation notes

The nonvanishing germ at `x` is supplied by
`Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis`, the statement that the basis section of
a sectionwise trivialization avoids `𝔪_y · L_y` at every point `y` of the trivializing open. A
trivialization through `x` comes from
`Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization` and is restricted to the open
`{x}` by `Stacks.SheafDescent.Trivialization.comp`.

That route replaces the identification of the stalk `L_x` with `𝒪_{X,x}` as a rank-one free
module, which is the shape this argument is usually given and which is *not* available in this
repository — `StacksFrontier/AlgebraicGeometry/AmpleGlobalGeneration/Basic.lean` records "the
rank of the stalk of an invertible module" as a missing input, and
`StacksFrontier/AlgebraicGeometry/StalkFreeBridge/StalkFree.lean` has the stalk comparison only
through local generators data. Going through the basis section of a trivialization avoids the
stalk computation entirely: the only fact used is that the trivializing function of the basis
section is `1`, hence a unit in every stalk over the trivializing open.

The gluing is Mathlib's `TopCat.Sheaf.existsUnique_gluing'` over the two-element index type
`Bool`, applied to the underlying sheaf of abelian groups `⟨L.presheaf, L.isSheaf⟩`. The
compatibility hypothesis is discharged by *subsingletonness*: the two opens meet in `⊥`, and the
sections of a sheaf over `⊥` form a terminal, hence zero, object
(`TopCat.Sheaf.isTerminalOfEmpty`). No overlap data is needed, which is exactly what makes the
clopen case cheaper than a general two-chart gluing.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)

## What is not done

No `stacks` attribute is attached in this file. Nothing here is the statement of a tag: Tag 0B5P
is the ampleness criterion and this is one step inside its proof, and Tag 01CY's clauses are
already carried elsewhere in the repository.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleStalk
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.Tag0B5PClopenLift

variable {X : Scheme.{u}}

/-! ### Gluing against the zero section -/

/-- The sections of an `𝒪_X`-module over the empty open form a subsingleton: they are a terminal
object of `AddCommGrpCat` by the sheaf condition, hence a zero object. -/
theorem subsingleton_sections_bot (M : X.Modules) {A : X.Opens} (hA : A = ⊥) :
    Subsingleton Γ(M, A) := by
  subst hA
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEmpty (⟨M.presheaf, M.isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X)).isZero

/-- **Gluing a section against zero across a disjoint cover.** If two opens `U` and `V` of `X`
are disjoint and cover `X`, then every section of an `𝒪_X`-module over `U` is the restriction of
a global section whose restriction to `V` vanishes.

There is no compatibility to check: the two opens meet in `⊥`, where the sections of a sheaf are
a subsingleton. -/
theorem exists_resTop_eq_of_disjoint_cover (M : X.Modules) (U V : X.Opens)
    (hdisj : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤) (a : Γ(M, U)) :
    ∃ s : Γ(M, ⊤), resTop M s U = a ∧ resTop M s V = 0 := by
  let W : Bool → X.Opens := fun b => cond b U V
  let t : ∀ b, Γ(M, W b) := fun b =>
    match b with
    | true => a
    | false => 0
  have hc : TopCat.Presheaf.IsCompatible M.presheaf W t := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact @Subsingleton.elim _ (subsingleton_sections_bot M (inf_comm U V ▸ hdisj)) _ _
    · exact @Subsingleton.elim _ (subsingleton_sections_bot M hdisj) _ _
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ W ⊤
    (fun _ => homOfLE le_top) (hcover.ge.trans (iSup_bool_eq (f := W)).ge) t hc
  exact ⟨s, hs true, hs false⟩

/-! ### The section cutting out a clopen point -/

/-- **A global section of an invertible `𝒪_X`-module whose nonvanishing locus is a prescribed
clopen point.** If `{x}` is open and closed in `X` and `L` is invertible, then some
`s ∈ Γ(X, L)` has `X_s = {x}`.

The section is the basis section of a trivialization of `L` over the open `{x}`, glued against
the zero section over the complement. Its germ at `x` avoids `𝔪_x · L_x` because the basis
section of a trivialization does, and its germ at every other point is `0`. -/
theorem exists_nonvanishingLocus_eq_singleton (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (x : X)
    (hopen : IsOpen ({x} : Set X)) (hclosed : IsClosed ({x} : Set X)) :
    ∃ s : Γ(L, ⊤), Stacks.Ample.nonvanishingLocus L s = {x} := by
  set U : X.Opens := ⟨{x}, hopen⟩ with hU
  set V : X.Opens := ⟨{x}ᶜ, hclosed.isOpen_compl⟩ with hV
  have hxU : x ∈ U := rfl
  obtain ⟨W, hxW, -, ⟨t⟩⟩ := Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization L x
  have hUW : U ≤ W := fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hxW
  set t' : Stacks.SheafDescent.Trivialization X.presheaf L.val U := t.comp (homOfLE hUW)
  obtain ⟨s, hsU, hsV⟩ := exists_resTop_eq_of_disjoint_cover L U V
    (by ext y; simp [hU, hV]) (by ext y; simp [hU, hV])
    (Stacks.NonvanishingOpen.basis t')
  have hgerm : ∀ (B : X.Opens) (y : X) (hy : y ∈ B),
      (L.presheaf.Γgerm y).hom s = (L.presheaf.germ B y hy).hom (resTop L s B) := fun B y hy =>
    (TopCat.Presheaf.Γgerm_res_apply (i := homOfLE le_top) L.presheaf y hy s).symm
  refine ⟨s, ?_⟩
  ext y
  simp only [Stacks.Ample.mem_nonvanishingLocus_iff, Set.mem_singleton_iff]
  refine ⟨fun hy => by_contra fun hyx => hy ?_, ?_⟩
  · simp [hgerm V y hyx, hsV]
  · rintro rfl
    rw [hgerm U y hxU, hsU]
    exact Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t' hxU

end Stacks.Tag0B5PClopenLift

end
