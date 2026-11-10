module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Stacks Tag 0E8W: the square of a globally generated invertible sheaf on a curve

Let `k` be a field and `X` a proper scheme over `k` of dimension `1` whose only global regular
functions are the constants, `H⁰(X, 𝒪_X) = k`. Let `ℒ` be an invertible `𝒪_X`-module which is
globally generated, has `H¹(X, ℒ) = 0`, and is ample. **Stacks Tag 0E8W** asserts that `ℒ^{⊗ 2}`
is very ample on `X` over `k`.

Very ampleness is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` for the structure morphism
`f : X ⟶ Spec k`, Stacks Tag 01VM in the spelling that names the twist `𝒪_{𝐏(E)}(1)` as the
glued degree-one twist of `Proj_S(Sym(E))`. There is no absolute very ampleness in this library,
and the relative notion at the structure morphism is the faithful reading of "very ample on `X`
over `k`".

## Main definitions

* `Stacks.Tag0E8WVeryAmpleSquare.VeroneseRelativeProjRealization`: the identification of `X` with
  the relative `Proj` of the second Veronese of the section ring, carried as a hypothesis.

## Main results

* `Stacks.Tag0E8WVeryAmpleSquare.isRelativelyVeryAmple_tensorPowModule_two`: the conclusion of
  Stacks Tag 0E8W, with the definition above as an explicit hypothesis. It carries no tag: Stacks
  Tag 0E8W itself, with no hypothesis beyond the source's, is
  `Stacks.Curves.VeryAmpleSquare.isRelativelyVeryAmple_tensorPowModule_two`
  (`SquareVeryAmpleGloballyGenerated.lean`).

## Hypotheses carried, and why none of them is the conclusion

The source's proof runs: the section ring `S = ⨁_{n ≥ 0} H⁰(X, ℒ^{⊗ n})` is generated in degrees
`0, 1, 2`; hence its second Veronese `S^{(2)} = ⨁_n S_{2n}` is generated in degree `1`; hence
`ℒ^{⊗ 2}` is very ample. The last step is the passage from a graded algebra generated in degree
one to very ampleness of its degree-one twist, which is **Stacks Tag 07ZR** and *is* available
here as `Stacks.Tag07ZRVeryAmple.isRelativelyVeryAmple_twistOne`. What the library lacks is the
bridge from `X` to that graded algebra, and the hypothesis below is exactly that bridge.

**`VeroneseRelativeProjRealization` is the identification `X = Proj(S^{(2)})`, in relative form.**
It asserts: under the hypotheses of Stacks Tag 0E8W there is a quasi-coherent graded
`𝒪_{Spec k}`-algebra `A`, generated in degree one, with an isomorphism `X ≅ Proj_{Spec k}(A)`
over `Spec k` carrying `ℒ^{⊗ 2}` to the degree-one twist `𝒪(1)` of that relative `Proj`. This is
the content of **Stacks Tag 01PZ** clause (4) and **Stacks Tag 0C6J** — `X ≅ Proj Γ_*(X, ℒ)` for
an ample `ℒ` — together with the generation statement in degrees `0, 1, 2` of **Stacks Tag
0E8V**'s argument and the passage from the absolute `Proj` of a graded ring to the relative `Proj`
of a sheaf graded algebra over an affine base. Three of those four pieces are genuinely absent
here: `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` is only ever built from a
symmetric algebra in this library, never from a section ring, so the relative form of the
identification cannot be assembled; and the step from generation in degrees `0, 1, 2` to
generation of the second Veronese in degree one is not derivable from
`Stacks.Veronese.veroneseGeneratedInDegOne_of_multiple`, whose conclusion at a fixed `d` requires
`d` to be divisible by the *number* of generators times a common multiple of their degrees. The
absolute half alone *is* proved, as `Stacks.AlgebraicGeometry.SectionRingProjIso.projIsoOfIsProper`
(**Stacks Tag 0EKI**), and carries a further integrality hypothesis of its own.

This hypothesis is **not** the conclusion of Stacks Tag 0E8W, nor a conjunct of it. The
conclusion asks for an *immersion of `X` into the projective bundle* `𝐏(E) = Proj_{Spec k}(Sym E)`
of a quasi-coherent module `E`, pulling `𝒪_{𝐏(E)}(1)` back to `ℒ^{⊗ 2}`. The hypothesis supplies
an isomorphism onto the relative `Proj` of a graded algebra `A` which is *not* a symmetric
algebra; the morphism `Proj_{Spec k}(A) ⟶ 𝐏(A₁)` that turns the one into the other is Stacks Tag
07ZR's closed immersion, a theorem of this library, and it is where generation of `A` in degree
one is consumed. Neither `E`, nor any immersion into a projective bundle, nor any statement about
`𝒪_{𝐏(E)}(1)` appears in the hypothesis.

## References

* [Stacks Project, Tag 0E8W](https://stacks.math.columbia.edu/tag/0E8W)
* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZR](https://stacks.math.columbia.edu/tag/07ZR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter TopologicalSpace
open Stacks.Ample
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.Tag01VMRelativeVeryAmple

universe u

namespace Stacks.Tag0E8WVeryAmpleSquare

/-- **The identification of a curve with the relative `Proj` of the second Veronese of its
section ring.** Under the hypotheses of Stacks Tag 0E8W — `X` proper of dimension `1` over a
field `k` with `H⁰(X, 𝒪_X) = k`, and `ℒ` invertible, globally generated, with `H¹(X, ℒ) = 0` and
ample — there is a quasi-coherent graded `𝒪_{Spec k}`-algebra `A`, generated in degree one, and an
isomorphism `X ≅ Proj_{Spec k}(A)` over `Spec k` carrying `ℒ^{⊗ 2}` to the degree-one twist of
that relative `Proj`.

This packages the source's own route: the section ring is generated in degrees `0, 1, 2`, so its
second Veronese is generated in degree one, and `X` is the `Proj` of it. It is carried rather than
proved; see the "Hypotheses carried" section of the module docstring for which pieces are absent
and for why this is not the conclusion of Stacks Tag 0E8W. -/
def VeroneseRelativeProjRealization : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [IsInvertibleModule X L],
    topologicalKrullDim X = 1 → SheafOfModules.IsGeneratedByGlobalSections L →
      IsZero (cohomologyOverField k f L 1) → IsAmple X L →
        ∃ (A : SheafGradedAlgebra (Spec (.of k))), ProjRepresentsF1.IsGeneratedInDegreeOne A ∧
          ∃ (e : X ≅ (relativeProj A).scheme),
          e.hom ≫ (relativeProj A).toBase = f ∧
            Nonempty (tensorPowModule X L 2 ≅
              (Scheme.Modules.pullback e.hom).obj (Tag07ZRVeryAmple.twistOne A))

/-- **Stacks Tag 0E8W.** Let `k` be a field and `f : X ⟶ Spec k` proper with `X` of dimension `1`
and `H⁰(X, 𝒪_X) = k`. Let `ℒ` be an invertible `𝒪_X`-module which is globally generated, has
`H¹(X, ℒ) = 0`, and is ample. Then `ℒ^{⊗ 2}` is very ample relative to `f`.

One hypothesis is carried: `hreal`, the identification of `X` with the relative `Proj` of the
second Veronese of the section ring (Stacks Tags 0E8V, 01PZ (4), 0C6J). It is not the conclusion
or a conjunct of it: no immersion into a projective bundle, and no statement about the twist of a
projective bundle, occurs in it. The module docstring sets this out in full.

The proof is the source's last step. From `hreal` the curve is the relative `Proj` of a graded
algebra `A` generated in degree one, with `ℒ^{⊗ 2}` its degree-one twist; Stacks Tag 07ZR then
makes the degree-one twist very ample for `Proj_{Spec k}(A) ⟶ Spec k`; and
`Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_isIso` transports that along the isomorphism,
which lies over `Spec k`. -/
theorem isRelativelyVeryAmple_tensorPowModule_two (hreal : VeroneseRelativeProjRealization.{u})
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [IsInvertibleModule X L] (hdim : topologicalKrullDim X = 1)
    (hgg : SheafOfModules.IsGeneratedByGlobalSections L)
    (hH1 : IsZero (cohomologyOverField k f L 1)) (hample : IsAmple X L) :
    Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L 2) := by
  obtain ⟨A, hgen, e, hover, ⟨etw⟩⟩ := hreal k X f L hdim hgg hH1 hample
  have := Tag07ZRVeryAmple.isInvertibleModule_twistOne A hgen
  have hva := Tag07ZRVeryAmple.isRelativelyVeryAmple_twistOne A hgen
  have hiso := Tag01VMVeryAmple.isRelativelyVeryAmple_of_isIso e.hom (relativeProj A).toBase
    (Tag07ZRVeryAmple.twistOne A) (tensorPowModule X L 2) etw hva
  rwa [hover] at hiso

end Stacks.Tag0E8WVeryAmpleSquare

end
