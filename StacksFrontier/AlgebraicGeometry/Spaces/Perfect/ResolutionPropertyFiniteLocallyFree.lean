module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Descent of the resolution property along a finite locally free morphism of algebraic spaces

Stacks 0GUV asserts that a surjective finite locally free morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S` carries the resolution property from its source to its target.  The
source's proof is: let `𝒢` be a finite type quasi-coherent `𝒪_Y`-module; the resolution
property of `X` applied to `f^*𝒢` produces a finite locally free `𝒪_X`-module `ℰ` and an
epimorphism `p : ℰ ⟶ f^*𝒢`; the direct image is exact along the affine morphism `f`
(Stacks 0A4K, in the section Stacks 0DK2), so `f_*p : f_*ℰ ⟶ f_*f^*𝒢` is again an
epimorphism; `f_*f^*𝒢 = 𝒢 ⊗_{𝒪_Y} f_*𝒪_X`, and tensoring with the dual of the finite locally
free module `f_*𝒪_X` — which has positive rank because `f` is surjective — turns that
epimorphism into an epimorphism `f_*ℰ ⊗ (f_*𝒪_X)^∨ ⟶ 𝒢` whose source is finite locally free.
Stacks 0GUV is
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional`.

## Main definitions

* `AlgebraicGeometry.Space.DirectImageDualDescent` is the statement of the last two steps of
  that proof — the projection formula together with the dual twist: granted that `f` is
  surjective and finite locally free, a finite type quasi-coherent `𝒪_Y`-module whose
  `f_*f^*` is an epimorphic image of a finite locally free module is itself an epimorphic
  image of a finite locally free module.

## Main results

* `AlgebraicGeometry.Space.directImageDualDescent_of_hasResolutionProperty`: the resolution
  property of `Y` implies `AlgebraicGeometry.Space.DirectImageDualDescent` for every `f` into
  `Y`.  This is the machine-checked certificate that the hypothesis
  `AlgebraicGeometry.Space.DirectImageDualDescent` is *strictly weaker* than the conclusion of
  Stacks 0GUV and is therefore not that conclusion in disguise.

## Implementation notes

**`DirectImageDualDescent` is not the conclusion.**  It is a statement about a single module
`𝒢` whose premise — that `f_*f^*𝒢` is an epimorphic image of a finite locally free module —
is not available for free: producing it is what the resolution property of `X` is for in the
proof of Stacks 0GUV.  In the other direction the resolution property of `Y` implies it
outright, which is `AlgebraicGeometry.Space.directImageDualDescent_of_hasResolutionProperty`.
So `DirectImageDualDescent` is implied by, and does not imply, the conclusion of
Stacks 0GUV.  It is existentially quantified, as the resolution property itself is; nothing
below is defined from it.

**The surjectivity and the finite local freeness of `f`** are the two hypotheses of
Stacks 0GUV and are consumed where the source consumes them: in the last step, which needs
`f` affine with `f_*𝒪_X` finite locally free of positive rank.  They are therefore the first
two premises of `DirectImageDualDescent` rather than side conditions of it.
"Surjective" is `AlgebraicGeometry.Space.IsSurjective`, Stacks 03ME, surjectivity of the map
`|X| → |Y|` on points; "finite locally free" is `AlgebraicGeometry.Space.IsFiniteLocallyFree`,
Stacks 03ZV, affineness of `f` together with finite local freeness of `f_*𝒪_X` on the small
étale ringed site of `Y`.

**The universe of the module sections** is the universe `u` of the schemes here, whereas
`AlgebraicGeometry.Space.HasResolutionProperty` leaves it free.  This is forced by the
statement's own hypothesis on `f`: `AlgebraicGeometry.Space.IsFiniteLocallyFree` is a
condition on `AlgebraicGeometry.Space.pushforwardStructureModule`, which is typed at
`AlgebraicGeometry.Space.Modules.{u, u}` because
`AlgebraicGeometry.Space.modulePushforward` is, and the proof applies the inverse and direct
image to the modules in the resolution property itself.

## References

* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 0GTC](https://stacks.math.columbia.edu/tag/0GTC)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0DK2](https://stacks.math.columbia.edu/tag/0DK2)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The projection formula and the dual twist, the last two steps of the proof of
Stacks 0GUV.**  Granted that `f : X ⟶ Y` is surjective and finite locally free, every finite
type quasi-coherent `𝒪_Y`-module `𝒢` such that `f_*f^*𝒢` is the target of an epimorphism from
a finite locally free module is itself the target of an epimorphism from a finite locally free
module.

In the source this is the identification `f_*f^*𝒢 = 𝒢 ⊗_{𝒪_Y} f_*𝒪_X` followed by tensoring
with the dual of `f_*𝒪_X`, which is finite locally free of positive rank because `f` is
surjective and finite locally free. -/
def DirectImageDualDescent (f : X ⟶ Y) : Prop :=
  IsSurjective B S hS f.hom → IsFiniteLocallyFree B S hS f →
    ∀ G : Modules.{u, u} B S hS Y.1 Y.2, SheafOfModules.IsQuasicoherentOnSite G →
      SheafOfModules.IsFiniteTypeOnSite G →
        ∀ M : Modules.{u, u} B S hS Y.1 Y.2, SheafOfModules.IsFiniteLocallyFreeOnSite M →
          ∀ φ : M ⟶ (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj G), Epi φ →
            ∃ (E : Modules.{u, u} B S hS Y.1 Y.2)
              (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E) (ψ : E ⟶ G), Epi ψ

/-- The resolution property of `Y` implies `AlgebraicGeometry.Space.DirectImageDualDescent`
for every morphism `f` of algebraic spaces with target `Y`: the conclusion asked for is
precisely what the resolution property supplies for a finite type quasi-coherent module, and
none of the other premises is needed.

This is the certificate that `AlgebraicGeometry.Space.DirectImageDualDescent` is strictly weaker
than the conclusion of Stacks 0GUV,
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional`.
-/
theorem directImageDualDescent_of_hasResolutionProperty (f : X ⟶ Y)
    (hY : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    DirectImageDualDescent B S hS f := by
  intro _ _ G hG hGft _ _ _ _
  have := hGft
  exact (hasResolutionProperty_iff B S hS Y.1 Y.2).mp hY
    (⟨G, hG⟩ : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)

end AlgebraicGeometry.Space

end
