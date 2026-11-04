module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexAsTheHomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyBoundedDualComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatFinitelyPresentedSummands
import StacksCore.Tactic.StacksAttribute

/-!
# A complex of modules with a left dual is locally strictly perfect

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
in the monoidal category of complexes of `𝒪`-modules, the tensor product being the total
complex of the tensor product of [Stacks, Tag 01CA]. Then every object `U` of `C` has a
covering `{U_i → U}` on whose members the restriction `ℱ^•|_{U_i}` is **strictly perfect**: it
is bounded, and each of its terms is a direct summand of a finite free `𝒪|_{U_i}`-module.

Both halves of the condition are already available separately — local boundedness
(`Stacks.SheafOfModules.Strict.isLocallyBounded_of_exactPairing`) and the local finite
freeness of each term (`Stacks.SheafOfModules.Strict.isLocallyDirectSummandOfFiniteFree_X`) —
but they produce *different* coverings: one covering for the boundedness, and one covering per
degree for the terms. The content of this file is the single covering that carries both.

It is obtained by composing the two: refine the boundedness covering, and over a member `W` of
it, on which only the degrees in a finite set `S` survive, intersect the finitely many
coverings produced in the degrees belonging to `S`. On a member `V → W` of that finite
intersection the terms in degrees belonging to `S` are finite free summands by construction,
and the terms in the remaining degrees are zero, because vanishing of a sheaf of modules on a
slice is inherited by every smaller slice; a zero module is the retract of the free module on
the empty index type, so the termwise condition holds in every degree. Boundedness over `V`
needs no transport, the boundedness covering being a sieve.

## Main definitions

* `Stacks.SheafOfModules.Strict.restrictComplexOver`: the degreewise restriction `ℱ^•|_V` of a
  complex of `𝒪`-modules to the site over an object `V`.

## Main results

* `Stacks.SheafOfModules.Strict.exists_cover_isStrictlyPerfect_of_exactPairing`: a complex of
  `𝒪`-modules with a left dual is strictly perfect on the members of a covering of any given
  object. This is the first conclusion of [Stacks, Tag 0FPS]; both conclusions of that tag are
  `Stacks.SheafOfModules.Strict.exists_dualComplexIso_of_exactPairing`.
* `Stacks.SheafOfModules.Strict.isZero_over_of_hom`: vanishing of a sheaf of modules over an
  object of the site is inherited along every arrow into that object.
* `Stacks.SheafOfModules.Strict.isDirectSummandOfFiniteFree_of_isZero`: a zero sheaf of
  modules is a direct summand of a finite free one.
* `Stacks.SheafOfModules.Strict.finsetInf_mem`: a finite intersection of covering sieves is a
  covering sieve.

## References

* [Stacks Project, Tag 0FPS](https://stacks.math.columbia.edu/tag/0FPS)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR) — the construction of
  the left dual as the Hom complex into the structure sheaf.
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL) — strictly perfect
  complexes on a ringed site.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal
  structure.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section

variable (Rr : Sheaf J RingCat.{max u v})

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Vanishing on a slice is inherited by smaller slices.** If the restriction of a sheaf of
modules to the site over `W` is a zero object, then so is its restriction to the site over any
object mapping to `W`. -/
theorem isZero_over_of_hom {F : _root_.SheafOfModules.{max u v} Rr} {V W : C} (g : V ⟶ W)
    (h : IsZero (F.over W)) : IsZero (F.over V) := by
  have : (_root_.SheafOfModules.overMap Rr g).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (Functor.map_isZero (_root_.SheafOfModules.overMap Rr g) h).of_iso
    ((_root_.SheafOfModules.overFunctorMap Rr g).app F).symm

/-- **A zero sheaf of modules is a direct summand of a finite free one.** It is a retract of
the free module on the empty index type, both maps being zero. -/
theorem isDirectSummandOfFiniteFree_of_isZero {F : _root_.SheafOfModules.{max u v} Rr}
    (h : IsZero F) : IsDirectSummandOfFiniteFree Rr F :=
  Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free Rr F
    PEmpty.{max u v + 1} 0 0 (by rw [zero_comp]; exact h.eq_of_src _ _)

end

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **A finite intersection of covering sieves is a covering sieve.** The empty intersection is
the maximal sieve, and a twofold intersection of covering sieves is covering. -/
@[sga "4 II 1.1.1"]
theorem finsetInf_mem {X : C} (T : ℤ → Sieve X) :
    ∀ S : Finset ℤ, (∀ n ∈ S, T n ∈ J X) → S.inf T ∈ J X := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hT
    rw [Finset.inf_insert]
    exact J.intersection_covering (hT a (Finset.mem_insert_self a s))
      (ih fun n hn => hT n (Finset.mem_insert_of_mem hn))

variable (R : Sheaf J CommRingCat.{max u v})

/-- The restriction `ℱ^•|_V` of a complex of `𝒪`-modules to the site over an object `V`, formed
degreewise. -/
abbrev restrictComplexOver (K : CochainComplex (Mod R) ℤ) (V : C) :
    CochainComplex
      (_root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf R).over V)) ℤ :=
  ((_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf R)
    V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **A complex of `𝒪`-modules with a left dual is locally strictly perfect.** If `L` is a left
dual of `K` in the monoidal category of complexes of `𝒪`-modules, then every object `U` of the
site has a covering sieve on whose members the restriction of `K` is a strictly perfect complex
of [Stacks, Tag 08FL]: bounded, with every term a direct summand of a finite free module.

This is the first of the two conclusions of [Stacks, Tag 0FPS]; the second, that the left dual
is the dual complex of Example 0FPR with its pairings, needs this one as its input, and the two
together are
`Stacks.SheafOfModules.Strict.exists_dualComplexIso_of_exactPairing`. -/
theorem exists_cover_isStrictlyPerfect_of_exactPairing (K L : CochainComplex (Mod R) ℤ)
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (U : C) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf R).over V)
        (restrictComplexOver R K V) := by
  classical
  obtain ⟨T₀, hT₀, hbnd⟩ := isLocallyBounded_of_exactPairing R K L p U
  have hbnd' : ∀ (W : C) (g : W ⟶ U), T₀ g →
      ∃ S : Finset ℤ, ∀ n ∉ S, IsZero ((K.X n).over W) := fun W g hg => hbnd g hg
  choose Bd hBd using hbnd'
  have hsum : ∀ (n : ℤ) (W : C), ∃ S : Sieve W, S ∈ J W ∧
      ∀ (V : C) (i : V ⟶ W), S i → ∃ I : Type (max u v), Finite I ∧
        Nonempty (Retract ((K.X n).over V)
          (_root_.SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf R).over V) I)) :=
    fun n W => isLocallyDirectSummandOfFiniteFree_X R K L p n W
  choose Sn hSnMem hSnSpec using hsum
  refine ⟨Sieve.bind T₀.arrows fun {W} {f} hf => (Bd W f hf).inf fun n => Sn n W,
    J.bind_covering hT₀ fun {W} {f} hf =>
      finsetInf_mem _ _ fun n _ => hSnMem n W, ?_⟩
  rintro V h ⟨W, g, f, hf, hg, rfl⟩
  have hgf : T₀ (g ≫ f) := T₀.downward_closed hf g
  refine ⟨?_, fun n => ?_⟩
  · refine Set.Finite.subset (Bd V (g ≫ f) hgf).finite_toSet fun n hn => ?_
    rw [Finset.mem_coe]
    by_contra hmem
    exact hn (hBd V (g ≫ f) hgf n hmem)
  · by_cases hn : n ∈ Bd W f hf
    · have hle : (Bd W f hf).inf (fun m => Sn m W) ≤ Sn n W := Finset.inf_le hn
      obtain ⟨I, _, ⟨ρ⟩⟩ := hSnSpec n W V g (hle g hg)
      exact Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free _ _ I ρ.i ρ.r
        ρ.retract
    · exact isDirectSummandOfFiniteFree_of_isZero _
        (isZero_over_of_hom _ g (hBd W f hf n hn))

end Stacks.SheafOfModules.Strict

end

end
