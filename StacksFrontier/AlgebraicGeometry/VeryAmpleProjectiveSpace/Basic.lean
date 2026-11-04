module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An immersion into `ℙⁿ_S` over an affine base makes the hyperplane sheaf very ample

Clauses (3), (4) of [Stacks, Tag 01VT] say that an invertible `𝒪_X`-module is very ample for
`f : X ⟶ S` as soon as it is the hyperplane sheaf pulled back along an immersion
`X ⟶ ℙⁿ_S` over `S`. The source discharges that direction with "as `𝐏ⁿ_S` is a projective bundle
over `S` … from the definition of a relatively very ample sheaf", which is the appeal to
[Stacks, Tag 01OE].

Both halves of Tag 01OE are now available: the isomorphism
`𝐏(𝒪_S^{n+1}) ≅ ℙⁿ_S` over `S` is `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` with
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst`, and over an **affine** base
its module half — that the isomorphism carries `𝒪_{ℙⁿ_S}(1)` to the degree-one twist
`𝒪_{𝐏(𝒪_S^{n+1})}(1)` — is `Stacks.SymGraded.hasFreeBundleTwistOne`. So the implication is a
transport of the immersion and of the isomorphism along one isomorphism of schemes, and that is
what this file performs.

## Main results

* `Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion`: **an immersion
  `j : X ⟶ ℙⁿ_S` over an affine base `S`, together with an isomorphism of `L` with the pullback
  of the hyperplane sheaf, makes `L` very ample relative to `f`**, in the sense of
  `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` ([Stacks, Tag 01VM]).

## Implementation notes

The quasi-coherent module the definition of relative very ampleness quantifies over is the free
module `𝒪_S^{n+1}`, and the projective bundle it names is `relativeProj (symAlgebra 𝒪_S^{n+1})`;
that scheme is `Stacks.SymGraded.freeProjectiveBundle n` by
`Stacks.SymGraded.freeProjectiveBundle_eq`, which holds by `rfl`, so the two spellings need no
bridge.

The base is affine only through `Stacks.SymGraded.hasFreeBundleTwistOne`. Nothing else below uses
it, and the arbitrary-base case is exactly the module half of Tag 01OE, whose remaining content
is the compatibility of the chart comparisons with [Stacks, Tag 01NO]'s transitions.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample

universe u

namespace Stacks.VeryAmpleProjectiveSpace

variable {X S : Scheme.{u}} (n : ℕ)

/-- **The hyperplane sheaf of `ℙⁿ_S` is the degree-one twist of the projective bundle of
`𝒪_S^{n+1}`, read on the bundle.** This is the module half of [Stacks, Tag 01OE] over an affine
base, `Stacks.SymGraded.hasFreeBundleTwistOne`, pushed across the inverse of the Tag 01OE
isomorphism. -/
theorem nonempty_pullback_inv_twistOne_iso [IsAffine S] :
    Nonempty (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S ≅
      (Scheme.Modules.pullback
          (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) n).inv).obj
        (Stacks.Tag01VMVeryAmple.twistOne
          (Stacks.SymGraded.freeModule (X := S) (Stacks.SymGraded.coordIndex.{u} n)))) := by
  obtain ⟨tw⟩ := Stacks.SymGraded.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne n
    (Stacks.SymGraded.hasFreeBundleTwistOne S n)
  set c := Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) n with hc
  refine ⟨?_⟩
  have v : (Scheme.Modules.pullback c.inv).obj ((Scheme.Modules.pullback c.hom).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) ≅
      Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S :=
    (Scheme.Modules.pullbackComp c.inv c.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr c.inv_hom_id).app _ ≪≫
        (Scheme.Modules.pullbackId _).app _
  exact v.symm ≪≫ (Scheme.Modules.pullback c.inv).mapIso tw

/-- **Clauses (3), (4) of [Stacks, Tag 01VT] in the producing direction, over an affine base.**
Let `S` be an affine scheme, `f : X ⟶ S` a morphism, `L` an invertible `𝒪_X`-module, and
`j : X ⟶ ℙⁿ_S` an immersion over `S` with `L ≅ j^* 𝒪_{ℙⁿ_S}(1)`. Then `L` is very ample relative
to `f`.

The projective bundle witnessing [Stacks, Tag 01VM] is `𝐏(𝒪_S^{n+1})`, which is `ℙⁿ_S` by
[Stacks, Tag 01OE]; the immersion is `j` followed by the inverse of that isomorphism, which lies
over `S` because the isomorphism does, and the twist is carried across by
`Stacks.VeryAmpleProjectiveSpace.nonempty_pullback_inv_twistOne_iso`. -/
theorem isRelativelyVeryAmple_of_immersion [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (j : X ⟶ AlgebraicGeometry.projectiveSpaceOver.{u} n S)
    (hj : IsImmersion j)
    (hover : j ≫ pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) = f)
    (e : L ≅ (Scheme.Modules.pullback j).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  have := hj
  set c := Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) n with hc
  obtain ⟨tw⟩ := nonempty_pullback_inv_twistOne_iso (S := S) n
  refine Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion f L
    (Stacks.SymGraded.freeModule (X := S) (Stacks.SymGraded.coordIndex.{u} n)) (j ≫ c.inv)
    inferInstance ?_ ?_
  · have hfac : c.inv ≫ (Stacks.SymGraded.freeProjectiveBundle (X := S) n).toBase =
        pullback.fst (terminal.from S)
          (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) := by
      rw [← Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := S) n,
        ← hc, Iso.inv_hom_id_assoc]
    rw [Category.assoc]
    show j ≫ c.inv ≫ (Stacks.SymGraded.freeProjectiveBundle (X := S) n).toBase = f
    rw [hfac, hover]
  · exact e ≪≫ (Scheme.Modules.pullback j).mapIso tw ≪≫
      (Scheme.Modules.pullbackComp j c.inv).app _

/-- **The same, with the immersion given over a larger base.** Let `g : S' ⟶ S` be a morphism of
schemes with `S'` affine, let `f : X ⟶ S'`, and let `j : X ⟶ ℙⁿ_S` be an immersion lying over
`f` followed by `g`, with `L ≅ j^* 𝒪_{ℙⁿ_S}(1)`. Then `L` is very ample relative to `f`.

No base-change theorem is used: `ℙⁿ_S` is a fibre product over the terminal scheme, so the
morphism `j' : X ⟶ ℙⁿ_{S'}` with the same projection to the integral model and `f` as its
structure morphism exists with nothing to check
(`Stacks.AmpleProjectiveImmersion.liftOver`), its composite with
`AlgebraicGeometry.projectiveSpaceOverMap n g` is `j` because both sides have the same two
components, and it is therefore an immersion by `AlgebraicGeometry.IsImmersion.of_comp`. The
hyperplane sheaf is carried across by
`Stacks.AmpleProjectiveImmersion.liftOverTwistIso`, both sides being the integral `𝒪(1)` pulled
back along the common projection to the integral model. -/
@[ega "II 4.4.10" "(v)"]
theorem isRelativelyVeryAmple_of_immersion_over {X S' S : Scheme.{u}} [IsAffine S'] (n : ℕ)
    (g : S' ⟶ S) (f : X ⟶ S') (L : X.Modules) [IsInvertibleModule X L]
    (j : X ⟶ AlgebraicGeometry.projectiveSpaceOver.{u} n S) (hj : IsImmersion j)
    (hover : j ≫ pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) = f ≫ g)
    (e : L ≅ (Scheme.Modules.pullback j).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  have := hj
  set g' := j ≫ AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n S with hg'
  set j' := Stacks.AmpleProjectiveImmersion.liftOver f g' with hjj'
  have hcomp : j' ≫ AlgebraicGeometry.projectiveSpaceOverMap n g = j := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, AlgebraicGeometry.projectiveSpaceOverMap_fst, ← Category.assoc, hjj',
        Stacks.AmpleProjectiveImmersion.liftOver_fst, hover]
    · rw [Category.assoc]
      show j' ≫ AlgebraicGeometry.projectiveSpaceOverMap n g ≫
        AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n S = _
      rw [AlgebraicGeometry.projectiveSpaceOverMap_snd, hjj',
        Stacks.AmpleProjectiveImmersion.liftOver_snd]
  have himm : IsImmersion j' := by
    have hc : IsImmersion (j' ≫ AlgebraicGeometry.projectiveSpaceOverMap n g) := by
      rw [hcomp]; assumption
    exact IsImmersion.of_comp j' (AlgebraicGeometry.projectiveSpaceOverMap n g)
  refine isRelativelyVeryAmple_of_immersion n f L j' himm ?_ ?_
  · rw [hjj']
    exact Stacks.AmpleProjectiveImmersion.liftOver_fst f g'
  · exact e ≪≫ (Scheme.Modules.pullbackComp j
        (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n S)).app _ ≪≫
      (Stacks.AmpleProjectiveImmersion.liftOverTwistIso f g').symm

end Stacks.VeryAmpleProjectiveSpace

end
