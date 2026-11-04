module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeBaseChangeLocal

/-!
# Conclusion (c) of [Stacks, Tag 0EX3]: the top higher direct image commutes with base change

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes with
`R^i f_* 𝓕 = 0` for `i > d` and every quasi-coherent `𝓕`, and let
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
be a base change diagram; these are the data of a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`. Conclusion (c) of the tag says that
*formation of `R^d f'_* 𝓕'` commutes with arbitrary further base change*, and the source's proof
explains what this means: for every additional cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
and every quasi-coherent `𝒪_{X'}`-module `𝓕'`, the canonical map

> `γ : h^* R^d f'_* 𝓕' ⟶ R^d f''_* (h')^* 𝓕'`,

the degree-`d` cohomology of `Lh^* Rf'_* 𝓕' ⟶ Rf''_* L(h')^* 𝓕' ⟶ Rf''_* (h')^* 𝓕'` read through
`H^d(Lh^* Rf'_* 𝓕') = h^* R^d f'_* 𝓕'`, is an isomorphism. That map is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap`.

The proof follows the source. The statement is local on `Y'` and `Y''`
(`isIso_topDirectImageBaseChangeMap_of_affine`, `TopDegreeBaseChangeLocal.lean`), and over affine
bases it is the computation of `isIso_topDirectImageBaseChangeMap_of_isAffine`
(`AffineBaseChangeTensor.lean`): conclusion (b) at `h_* 𝒪_{Y''}`, the projection formula
`F' ⊗ (f')^* h_* 𝒪_{Y''} ≅ (h')_*(h')^* F'`, and the degeneration of the Leray spectral sequence
along the affine `h`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap`:
  **conclusion (c) of [Stacks, Tag 0EX3]**, with no hypothesis beyond the situation, the
  cartesian square and the quasi-coherence of `𝓕'`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X'' Y'' : Scheme.{u}}

/-- **Conclusion (c) of [Stacks, Tag 0EX3]: formation of `R^d f'_* 𝓕'` commutes with arbitrary
further base change.** For a top-degree base-change situation `S` (a morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes whose higher direct images of quasi-coherent modules vanish
above `d`, and a base change `f' : X' ⟶ Y'` of it), every further cartesian square
`X'' --h'--> X'`, `X'' --f''--> Y''`, `Y'' --h--> Y'` and every quasi-coherent `𝒪_{X'}`-module
`𝓕'`, the canonical map `γ : h^* R^d f'_* 𝓕' ⟶ R^d f''_* (h')^* 𝓕'` is an isomorphism. -/
@[stacks 0EX3 "(c)"]
theorem isIso_topDirectImageBaseChangeMap
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h (toShHom_comm_of_isPullback h' f'' h sq)) :=
  isIso_topDirectImageBaseChangeMap_of_affine
    (fun T _ _ _ _ a' b a sq' G _ => isIso_topDirectImageBaseChangeMap_of_isAffine T a' b a sq' G)
    S F' h' f'' h sq

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
