module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Flatness over the base across an étale square

Let
```
X' --j--> X
|         |
g         f
v         v
S' --e--> S
```
be a commutative square of schemes whose horizontal arrows are étale. Flatness over the base of
a quasi-coherent module `F` on `X` at a point `j y` passes to flatness of `j^* F` over `S'` at
`y`: the composite `j ≫ f` sees `j^* F` as flat by [Stacks, Tag 02JZ] along the flat morphism
`j`, and the square rewrites that composite as `g ≫ e`, where the étale morphism `e` may be
removed by [Stacks, Tag 05B9].

The square formed by an open `U ⊆ S`, its inverse image `f ⁻¹ᵁ U` and the restriction `f ∣_ U`
is the case used to pass between flatness of `F` over `S` at the points lying over `U` and
flatness of the restricted module over `U`; both directions are recorded here.

## Main results

* `AlgebraicGeometry.isFlatOverAt_pullback_of_etale_square`: the transfer across the square.
* `AlgebraicGeometry.isFlatOverAt_of_open_restriction`: flatness of the restricted module over
  `U` gives flatness of `F` over `S` at every point lying over `U`.
* `AlgebraicGeometry.isFlatOver_restrict_of_flatOnPreimage`: the converse, from flatness of `F`
  over `S` at every point lying over `U`.

## Implementation notes

Quasi-coherence is needed because [Stacks, Tag 05B9] is proved for quasi-coherent modules only;
the pullback of a quasi-coherent module is quasi-coherent by [Stacks, Tag 01BG]. The pullback
functor used is `AlgebraicGeometry.Scheme.Modules.pullback`, which is by definition the
`RingedSpaceModuleAdjunction.modulePullback` that [Stacks, Tag 02JZ] is stated with.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private theorem isQuasicoherent_pullback {X Y : Scheme.{u}} (j : X ⟶ Y) (F : Y.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback j).obj F).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ j.toLRSHom.toShHom F ‹F.IsQuasicoherent›

/-- **Flatness over the base transfers across an étale square.** For a commutative square
`j ≫ f = g ≫ e` with `j` and `e` étale and `F` quasi-coherent on `X`, flatness of `F` over `S`
at `j y` gives flatness of `j^* F` over `S'` at `y`. -/
public theorem isFlatOverAt_pullback_of_etale_square
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ S')
    (j : X' ⟶ X) (e : S' ⟶ S) [Etale j] [Etale e]
    (F : X.Modules) [F.IsQuasicoherent] (hcomm : j ≫ f = g ≫ e)
    (y : X') (hflat : IsFlatOverAt f.toLRSHom.toShHom F (j y)) :
    IsFlatOverAt g.toLRSHom.toShHom ((Scheme.Modules.pullback j).obj F) y := by
  have := isQuasicoherent_pullback j F
  have hcomp : IsFlatOverAt (j ≫ f).toLRSHom.toShHom
      ((Scheme.Modules.pullback j).obj F) y :=
    (isFlatOverAt_iff_modulePullback_isFlatOverAt j f F y (Flat.stalkMap j y)).mp hflat
  rw [hcomm] at hcomp
  exact (isFlatOverAt_comp_iff_of_etale g e ((Scheme.Modules.pullback j).obj F) y).mp hcomp

/-- **Flatness of a restriction to an open of the base is flatness at the points over it.** If
the pullback of a quasi-coherent module `F` to `f ⁻¹ᵁ U` is flat over `U`, then `F` is flat over
`S` at every point of `X` lying over `U`. -/
public theorem isFlatOverAt_of_open_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (x : X) (hx : f x ∈ U)
    (hflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  have := isQuasicoherent_pullback (f ⁻¹ᵁ U).ι F
  have h := (isFlatOverAt_comp_iff_of_etale (f ∣_ U) U.ι
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)
    (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme)).mpr (hflat ⟨x, hx⟩)
  rw [morphismRestrict_ι] at h
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt (f ⁻¹ᵁ U).ι f F
    (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme) (Flat.stalkMap (f ⁻¹ᵁ U).ι ⟨x, hx⟩)).mpr h

/-- **Flatness at the points over an open of the base is flatness of the restriction.** If a
quasi-coherent module `F` is flat over `S` at every point of `X` lying over `U`, then its
pullback to `f ⁻¹ᵁ U` is flat over `U`. -/
public theorem isFlatOver_restrict_of_flatOnPreimage
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens)
    (hflat : ∀ x : X, f x ∈ U → IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F) := fun x =>
  isFlatOverAt_pullback_of_etale_square f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι F
    (morphismRestrict_ι f U).symm x (hflat x.1 x.2)

end AlgebraicGeometry
