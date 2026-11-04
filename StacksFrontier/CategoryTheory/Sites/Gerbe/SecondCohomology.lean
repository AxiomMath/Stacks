module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs
import StacksCore.Tactic.StacksAttribute

/-! # Second cohomology and gerbes

Let `p : 𝒮 ⥤ 𝒞` be a gerbe over a site `(𝒞, J)` whose automorphism sheaves are abelian and let
`𝒢` be the abelian sheaf of Stacks 0CJY. Stacks 0CK0 says that an object `U` of `𝒞` carries an
object of `𝒮` as soon as

1. there is a cofinal system of coverings `{U_i → U}` of `U` with `H¹(U_i, 𝒢) = 0` and
   `H¹(U_i ×_U U_j, 𝒢) = 0` for all `i`, `j`, and
2. `H²(U, 𝒢) = 0`.

The source's proof has seven steps: choose a covering with objects `x_i` over its members;
refine it inside the cofinal system of (1); make `Isom(x_i|, x_j|)` a `𝒢|`-torsor on `𝒞/U_ij`;
trivialize that torsor by `H¹(U_ij, 𝒢) = 0` (Stacks 03AJ and 03AI) to get `φ_ij`; read the
failure of the cocycle condition as a Čech 2-cocycle `g_ijk` with values in `𝒢`; kill it using
`H²(U, 𝒢) = 0` and the injectivity of `Ȟ²(𝒰, 𝒢) → H²(U, 𝒢)` supplied by the Čech-to-cohomology
spectral sequence (Stacks 03AZ) together with `H¹(U_i, 𝒢) = 0`; and finally descend, the
corrected gluing data being an effective descent datum because `p` is a stack.

The lemma as a whole is `CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing`, in
`StacksFrontier.CategoryTheory.Sites.Gerbe.ExistenceOfAnObject`, which carries all seven steps; this
file carries the first and the last of them separately, each with the vocabulary of the Čech
chapter of this library, and its tag is clause-scoped accordingly.

## Main results

* `CategoryTheory.Gerbe.exists_covering_fiber_nonempty_of_cofinal_h1_isZero`: the refinement
  step. A gerbe is locally nonempty, so `U` has *some* covering along whose members `𝒮` has an
  object; hypothesis (1) refines that covering to one drawn from the cofinal system, which
  therefore carries an object of `𝒮` over each member *and* has the vanishing first cohomology
  on its members and on its double overlaps.
* `CategoryTheory.Gerbe.nonempty_fiber_of_descentDatum`: the descent step. A descent datum
  relative to a covering family of `U` is effective because `p` is a stack, and the object it
  descends to is an object of `𝒮` lying over `U` — the conclusion of Stacks 0CK0.

## Implementation notes

**The cohomology spelling.** `H^n(U, 𝒢)` is `CategoryTheory.Sheaf.H' 𝒢 n U`, Mathlib's
cohomology of an abelian sheaf *over an object* of the site, and its vanishing is
`CategoryTheory.Limits.IsZero`. This is the spelling of the Čech chapter of this library — see
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero` for Stacks 03F9, whose
conclusion is a vanishing of `Sheaf.H'`, and `Stacks.Cohomology.TerminalCohomology.h'IsoH` for
its comparison with the global `CategoryTheory.Sheaf.H`. `Sheaf.H` is cohomology of the site as
a whole and so cannot state a hypothesis about an object `U`; the two agree exactly when `U` is
terminal. Coefficients are `AddCommGrpCat.{v₁}`, with `v₁` the universe of the morphisms of `𝒞`,
which is what `Sheaf.H'` requires.

**Hypothesis (1).** "There is a cofinal system of coverings `{U_i → U}` with `P`" is rendered as
"every covering sieve of `U` is refined by a covering family with `P`", which is what cofinality
of a system says and is how the Čech chapter states it
(`hCovCofinal` of `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero`). Both
halves of (1) are kept: the vanishing is asserted on the members `U_i` *and* on the double
overlaps `U_i ×_U U_j`. A site has no chosen fibre products, so the overlaps are existentially
quantified data carrying `CategoryTheory.IsPullback` proofs, as in
`CategoryTheory.Functor.IsStackInGroupoids`; any two choices are isomorphic, so the vanishing
does not depend on the choice.

**The conclusion.** "There exists an object of `𝒮` lying over `U`" is
`Nonempty (p.Fiber U)`, the spelling of `CategoryTheory.Functor.LocallyNonempty`. It is a
`Prop`, so no choice is used: nothing here invokes `Classical.choose`, and in particular the
object is never extracted from the statement being proved.

**The sheaf `𝒢`.** Stacks 0CJY is `CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self`, an
existence statement; the sheaf it produces, `CategoryTheory.Gerbe.Band.bandSheaf`, is `private`,
and it is valued in `CommGrpCat` while `Sheaf.H'` takes coefficients in `AddCommGrpCat`. The two
statements below do not need the comparison isomorphisms `θ` of 0CJY — the refinement step uses
`𝒢` only as a coefficient sheaf and the descent step not at all — so `𝒢` is taken here as an
arbitrary abelian sheaf. Instantiating it at the band of 0CJY, carried across
`commGroupAddCommGroupEquivalence` as `Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf` does
in the other direction, gives the steps as the source states them.

## References

* [Stacks 0CK0](https://stacks.math.columbia.edu/tag/0CK0)
* [Stacks 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks 06NZ](https://stacks.math.columbia.edu/tag/06NZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe x w v₁ u₁ v₂ u₂

namespace CategoryTheory.Gerbe

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-! ### The refinement step -/

/-- **Stacks 0CK0, the refinement step.** Let `p : 𝒮 ⥤ 𝒞` be locally nonempty for `J` — clause
(2) of the definition of a gerbe, Stacks 06NZ — let `𝒢` be an abelian sheaf on `(𝒞, J)`, and let
`U` be an object of `𝒞` satisfying hypothesis (1) of Stacks 0CK0: there is a cofinal system of
coverings of `U`, that is a family of covering families refining every covering sieve of `U`,
each member `U_i` of which has `H¹(U_i, 𝒢) = 0` and each double overlap `U_i ×_U U_j` of which
has `H¹(U_i ×_U U_j, 𝒢) = 0`.

Then there is a covering family `{U_i → U}` with all of that vanishing which in addition carries
an object of `𝒮` over every member.

This is the source's "Choose a covering `{U_i → U}` and objects `x_i` of `𝒮` over `U_i`. By
assumption (1) we may choose the covering such that `H¹(U_i, 𝒢) = 0` and
`H¹(U_i ×_U U_j, 𝒢) = 0`." Local nonemptiness supplies a covering sieve of `U` along every arrow
of which the fibre of `p` is nonempty; cofinality refines it to a member of the system, whose
every arrow `U_i → U` lies in that sieve. -/
@[stacks 0CK0 "the refinement step of the proof: a covering of U drawn from the cofinal system \
of hypothesis (1), carrying an object of 𝒮 over each of its members"]
theorem exists_covering_fiber_nonempty_of_cofinal_h1_isZero
    (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞)
    [HasSheafify J AddCommGrpCat.{v₁}] [HasExt.{x} (Sheaf J AddCommGrpCat.{v₁})]
    (hne : p.LocallyNonempty J) (𝒢 : Sheaf J AddCommGrpCat.{v₁}) (U : 𝒞)
    (hcof : ∀ R ∈ J U, ∃ (I : Type w) (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ Sieve.ofArrows V f ≤ R ∧
      (∀ i, IsZero (Sheaf.H' 𝒢 1 (V i))) ∧
      ∃ (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j),
        (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)) ∧
        ∀ i j, IsZero (Sheaf.H' 𝒢 1 (Vij i j))) :
    ∃ (I : Type w) (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
      (∀ i, Nonempty (p.Fiber (V i))) ∧
      (∀ i, IsZero (Sheaf.H' 𝒢 1 (V i))) ∧
      ∃ (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j),
        (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)) ∧
        ∀ i j, IsZero (Sheaf.H' 𝒢 1 (Vij i j)) := by
  obtain ⟨S, hS, hfib⟩ := hne U
  obtain ⟨I, V, f, hcovV, hle, h₁, Vij, pr₁, pr₂, hpb, h₁'⟩ := hcof S hS
  exact ⟨I, V, f, hcovV,
    fun i => hfib (f i) (hle _ (Sieve.ofArrows_mk V f i)),
    h₁, Vij, pr₁, pr₂, hpb, h₁'⟩

/-! ### The descent step -/

/-- **Effectivity of a descent datum, read off clause (3) of Stacks 02ZI.** This carries no
`stacks` attribute: it assumes the descent datum whose construction is the content of Stacks
0CK0, and uses none of that tag's hypotheses, so it is plumbing rather than coverage.

A descent datum (Stacks 8.3.1) relative to a covering family
`{U_i → U}` of a stack in groupoids `p : 𝒮 ⥤ 𝒞` is effective, and the object it descends to lies
over `U`; so there is an object of `𝒮` lying over `U`, which is the conclusion of Stacks 0CK0.

This is the source's closing "we see that we obtain a descent datum, which is effective since
`p` is a stack, and the proof is complete." It is the only step of the proof that produces the
asserted object, and it reads off clause (3) of Stacks 02ZI
(`CategoryTheory.Functor.IsStackInGroupoids.effective_descent`); the corrected gluing data that
the source feeds to it is not constructed here. -/
theorem nonempty_fiber_of_descentDatum {p : 𝒮 ⥤ 𝒞} {J : GrothendieckTopology 𝒞}
    (hst : IsStackInGroupoids.{w} p J) {U : 𝒞} {I : Type w}
    (V : I → 𝒞) (f : ∀ i, V i ⟶ U) (hcov : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → 𝒞)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    Nonempty (p.Fiber U) := by
  obtain ⟨y, hy, -⟩ := hst.effective_descent V f hcov Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
    q₁ q₂ q₃ hq₁ hq₂ hq₃ D
  exact ⟨⟨y, hy⟩⟩

end CategoryTheory.Gerbe

end
