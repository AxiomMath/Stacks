module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChange
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.UnramifiedConormal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelLocallyFree

/-!
# The excess conormal sheaf of a base-changed factorization

Let `g' ≫ f = f' ≫ g` be a cartesian square of schemes and `f = h ∘ i` a factorization of `f`
with `i : X ⟶ P` an immersion and `h : P ⟶ Y` smooth, and let `f' = h' ∘ i'` be its base change
through `P' = P ×_Y Y'` (`Stacks.Chow.SmoothFactorization.baseChange`). The left square

```
X' --i'--> P'
|          |
g'         p
v          v
X  --i---> P
```

is cartesian, so the canonical map of conormal sheaves of Stacks 01R4

  `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}`

is surjective by Stacks 0473. The proof of Stacks 0FV9 identifies the sheaf `𝒞` of that tag with
the kernel of this map, and observes that it is a kernel of a surjection of finite locally free
modules once `f` and `f'` are local complete intersection morphisms. This file proves the second
half: the kernel is finite locally free, and with it the map sits in a short exact sequence of
finite locally free `𝒪_{X'}`-modules — the sequence which, dualized, is the excess sequence
`0 ⟶ 𝒩_{X'/P'} ⟶ (g')^*𝒩_{X/P} ⟶ 𝒞^∨ ⟶ 0` that Stacks 0FV7 is applied to.

## Main definitions

* `Stacks.Chow.SmoothFactorization.baseChangeConormalMap`: the map
  `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of Stacks 01R4 for the left square.
* `Stacks.Chow.SmoothFactorization.baseChangeExcessConormal`: its kernel.

## Main results

* `Stacks.Chow.SmoothFactorization.epi_baseChangeConormalMap`: the map is an epimorphism
  (Stacks 0473).
* `Stacks.Chow.SmoothFactorization.isFiniteLocallyFree_baseChangeExcessConormal`: for `f` and
  `f'` local complete intersection morphisms, the kernel is finite locally free.
* `Stacks.Chow.SmoothFactorization.shortExact_baseChangeConormal`: the kernel, the pulled-back
  conormal sheaf and the conormal sheaf of `i'` form a short exact sequence.

## Implementation notes

Both conormal sheaves are finite locally free because both immersions are Koszul-regular, by
Stacks 069G (`Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion`), and the conormal sheaf
of a Koszul-regular immersion is finite locally free (Stacks 063M, through quasi-regularity).
The pullback of a finite locally free module is finite locally free, and the kernel of an
epimorphism of finite locally free modules is finite locally free
(`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi`).

The conormal sheaves are `Stacks.Conormal.conormalSheaf`, the sheaf of Stacks 01R2 that
`Stacks.Immersion.immersionConormalSheafMap` — the map Stacks 0FV7 is stated with — reads
through the canonical closed factor of each immersion.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

namespace SmoothFactorization

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

/-- The canonical map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of conormal sheaves (Stacks 01R4) for the
left square of the base change of a factorization `f = h ∘ i` along a cartesian square. -/
def baseChangeConormalMap (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    (modulePullback g'.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf F.imm) ⟶
      Stacks.Conormal.conormalSheaf (F.baseChange hsq).imm :=
  Stacks.Immersion.immersionConormalSheafMap (F.baseChange hsq).imm F.imm g'
    (pullback.fst F.proj g)
    (Stacks.Immersion.toShHom_square (F.isPullback_baseChange hsq).flip.w)

/-- **Stacks 0473 for the base-changed factorization**: the map
`(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` is an epimorphism, the left square being cartesian. -/
theorem epi_baseChangeConormalMap (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    Epi (F.baseChangeConormalMap hsq) :=
  Stacks.Immersion.epi_immersionConormalSheafMap (F.baseChange hsq).imm F.imm g'
    (pullback.fst F.proj g) (F.isPullback_baseChange hsq).flip

/-- The excess conormal sheaf of a base-changed factorization: the kernel of the surjection
`(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}`. The proof of Stacks 0FV9 identifies the sheaf `𝒞` of that tag
with it. -/
def baseChangeExcessConormal (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    X'.Modules :=
  kernel (F.baseChangeConormalMap hsq)

/-- The conormal sheaf of the immersion of a factorization of a local complete intersection
morphism is finite locally free: the immersion is Koszul-regular (Stacks 069G), and the conormal
sheaf of a Koszul-regular immersion is finite locally free (Stacks 063M). -/
theorem isFiniteLocallyFree_conormalSheaf {Z W : Scheme.{u}} {k : Z ⟶ W}
    (F : SmoothFactorization k) (hk : IsLocalCompleteIntersectionMorphism k) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheaf F.imm) :=
  isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion F.imm
    (isQuasiRegularImmersion_of_isH1RegularImmersion F.imm
      (isH1RegularImmersion_of_isKoszulRegularImmersion F.imm
        (F.isKoszulRegularImmersion_of_lci hk)))

/-- **The excess conormal sheaf is finite locally free.** For `f` and `f'` local complete
intersection morphisms, the kernel of `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` is a finite locally free
`𝒪_{X'}`-module: it is the kernel of a surjection between finite locally free modules. -/
theorem isFiniteLocallyFree_baseChangeExcessConormal (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) (hf : IsLocalCompleteIntersectionMorphism f)
    (hf' : IsLocalCompleteIntersectionMorphism f') :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (F.baseChangeExcessConormal hsq) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi _
    (F.epi_baseChangeConormalMap hsq)
    (isFiniteLocallyFree_pullback g' _ (F.isFiniteLocallyFree_conormalSheaf hf))
    ((F.baseChange hsq).isFiniteLocallyFree_conormalSheaf hf')

/-- The excess conormal sheaf, the pulled-back conormal sheaf of `i` and the conormal sheaf of
`i'` form the short exact sequence `0 ⟶ 𝒞 ⟶ (g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'} ⟶ 0`. -/
theorem shortExact_baseChangeConormal (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    (ShortComplex.mk (kernel.ι (F.baseChangeConormalMap hsq)) (F.baseChangeConormalMap hsq)
      (kernel.condition _)).ShortExact :=
  have := F.epi_baseChangeConormalMap hsq
  { exact := ShortComplex.exact_kernel _ }

end SmoothFactorization

end Stacks.Chow

end
