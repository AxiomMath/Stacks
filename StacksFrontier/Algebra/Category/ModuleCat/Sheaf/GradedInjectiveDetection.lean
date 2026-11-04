module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafModulesGrothendieck
public import StacksFrontier.CategoryTheory.Preadditive.Injective.DetectingMonomorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting injectivity of graded modules by a set of monomorphisms

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras.
Injectivity of a right graded `A`-module is a condition quantified over all monomorphisms of
graded modules, hence over a proper class; since the category of right graded `A`-modules is a
Grothendieck abelian category by [Stacks, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD),
a *set* of monomorphisms suffices to test it. That is
[Stacks, Tag 0FSN](https://stacks.math.columbia.edu/tag/0FSN).

If `A` carries a differential, a right differential graded `A`-module is *graded injective*
when it is injective after the differential is forgotten
([Stacks, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)). Applying the differential
graded hull — the left adjoint of forgetting the differential, Tags 0FSK and 0FSL — to a
detecting family of Tag 0FSN produces a set of monomorphisms *between acyclic differential
graded modules* which detects graded injectivity. That is
[Stacks, Tag 0FSS](https://stacks.math.columbia.edu/tag/0FSS); it is the input to the
construction of K-injective resolutions of differential graded modules.

## Main results

* `SheafOfModules.GradedModule.exists_monomorphisms_injective_iff` is **Tag 0FSN**: a set of
  monomorphisms of right graded modules detecting injectivity.
* `SheafOfModules.DifferentialGradedModule.exists_acyclic_monomorphisms_gradedInjective_iff` is
  **Tag 0FSS**: a set of monomorphisms of *acyclic* right differential graded modules detecting
  graded injectivity.

## Implementation notes

Both statements are specializations of the general criterion for Grothendieck abelian
categories, `CategoryTheory.exists_monomorphisms_injective_iff` of
`StacksFrontier.CategoryTheory.Preadditive.Injective.DetectingMonomorphisms`, which is
[Stacks, Tag 079G](https://stacks.math.columbia.edu/tag/079G); the detecting family consists of
the inclusions of the subobjects of the separator `⨁_{k, U} j_{U!} A_U[k]` exhibited by Tag
0FRD. Tag 0FSS is obtained from Tag 0FSN by transporting the extension property along the hull
adjunction with `CategoryTheory.Adjunction.exists_extension_map_iff`, which is exactly the
source's argument: a dotted arrow out of `G(N)` is the same datum as a dotted arrow out of `N`
into the underlying graded module.

The source's "injective map of acyclic differential graded modules" is read as a monomorphism
whose source *and* target are acyclic; both are hulls, so both are acyclic by Tag 0FSL part (3),
and the monomorphism is the hull of a monomorphism by the last assertion of Tag 0FSL.

**Hypotheses and universes.** The base is an arbitrary sheaf of rings on an arbitrary site
rather than the structure sheaf of a ringed site, as everywhere in this development, and the
universes of the site, the ring and the algebra pieces are independent. The module universe is
`max u v a w` for a site `C : Type u` with `Category.{v} C` and algebra pieces in
`SheafOfModules.{a} R`, with `w` free: this is forced by Tag 0FRD, which is available only at
that module universe, since local smallness of the category of graded modules needs `u` and `v`
and a direct sum indexed by the objects of the site needs `u`. The sheafification hypotheses are
those of Tag 0FRD and of the abelian structure of Tag 0FR0. The index type of the detecting
family is then also `Type (max u v a w)`, being a shrinking of the subobjects of the separator.

## References

* [Stacks Project, Tag 0FSN](https://stacks.math.columbia.edu/tag/0FSN)
* [Stacks Project, Tag 0FSS](https://stacks.math.columbia.edu/tag/0FSS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w a t v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J (Type max u v a w)]
  [HasSheafify J AddCommGrpCat.{max u v a w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v a w}]

namespace GradedModule

/-- **Stacks Tag 0FSN.** For a sheaf of graded algebras `A` over a sheaf of rings on a site
there is a set `T` and, for each `t : T`, a monomorphism `N t ⟶ N' t` of right graded
`A`-modules, such that a right graded `A`-module `I` is injective if and only if every
morphism `N t ⟶ I` extends along `N t ⟶ N' t` to a morphism `N' t ⟶ I`.

This is the criterion for Grothendieck abelian categories, Tag 079G, applied to the category of
right graded `A`-modules, which is Grothendieck abelian by Tag 0FRD. -/
@[stacks 0FSN]
theorem exists_monomorphisms_injective_iff (A : GradedAlgebra.{t, a} R) :
    ∃ (T : Type max u v a w) (N N' : T → GradedModule.{t, a, max u v a w} A)
      (i : ∀ s, N s ⟶ N' s),
      (∀ s, Mono (i s)) ∧
        ∀ I : GradedModule.{t, a, max u v a w} A,
          Injective I ↔ ∀ (s : T) (f : N s ⟶ I), ∃ g : N' s ⟶ I, i s ≫ g = f :=
  _root_.CategoryTheory.exists_monomorphisms_injective_iff _

end GradedModule

namespace DifferentialGradedModule

/-- **Stacks Tag 0FSS.** For a sheaf of differential graded algebras `A` over a sheaf of rings
on a site there is a set `T` and, for each `s : T`, a monomorphism `M s ⟶ M' s` of *acyclic*
right differential graded `A`-modules, such that a right differential graded `A`-module `I` is
graded injective (Tag 0FSP) if and only if every morphism `M s ⟶ I` extends along
`M s ⟶ M' s` to a morphism `M' s ⟶ I`.

The family is the image under the differential graded hull of a detecting family for
injectivity of graded modules (Tag 0FSN): the hull preserves monomorphisms and has acyclic
values by Tag 0FSL, and the extension property is transported along the hull adjunction of
Tag 0FSK. -/
@[stacks 0FSS]
theorem exists_acyclic_monomorphisms_gradedInjective_iff
    (A : DifferentialGradedAlgebra.{t, a} R) :
    ∃ (T : Type max u v a w) (M M' : T → DifferentialGradedModule.{t, a, max u v a w} A)
      (i : ∀ s, M s ⟶ M' s),
      (∀ s, Mono (i s)) ∧ (∀ s, (M s).complex.Acyclic) ∧ (∀ s, (M' s).complex.Acyclic) ∧
        ∀ I : DifferentialGradedModule.{t, a, max u v a w} A,
          GradedInjective I ↔
            ∀ (s : T) (f : M s ⟶ I), ∃ g : M' s ⟶ I, i s ≫ g = f := by
  obtain ⟨T, N, N', j, hj, hiff⟩ :=
    GradedModule.exists_monomorphisms_injective_iff (A := A.toGradedAlgebra)
  refine ⟨T, fun s ↦ (forgetToGradedModule.{t, a, max u v a w} A).leftAdjoint.obj (N s),
    fun s ↦ (forgetToGradedModule.{t, a, max u v a w} A).leftAdjoint.obj (N' s),
    fun s ↦ (forgetToGradedModule.{t, a, max u v a w} A).leftAdjoint.map (j s),
    fun s ↦ have := hj s; dgHull_map_mono (j s),
    fun s ↦ dgHull_acyclic A (N s), fun s ↦ dgHull_acyclic A (N' s), fun I ↦ ?_⟩
  exact (hiff _).trans <| forall_congr' fun s ↦
    (Adjunction.exists_extension_map_iff
      (Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, max u v a w} A)) (j s) I).symm

end DifferentialGradedModule

end SheafOfModules

end
