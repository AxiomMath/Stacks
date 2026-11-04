module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality

/-!
# The canonical map on relative differentials is determined by its square

`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` is selected, out of the unique-existence
statement of Stacks Project, Tag 01UV, by `Classical.choose`. This file turns that choice into a
usable characterization: the canonical map satisfies the defining compatibility with universal
derivations, any morphism satisfying that compatibility equals it, and — because the
compatibility mentions only the three morphisms `f`, `p` and `p'` — the canonical map does not
depend on the base morphism `g` or on the proof that the square commutes.

The last point is what makes the map canonical rather than merely chosen, and it is what the
consumers of Tag 01UV need: the comparison map of Stacks Project, Tag 04FB is built from the
square whose base morphism is the identity, and nothing downstream should have to know which
square was used to produce it. That map is named here as
`AlgebraicGeometry.Scheme.Hom.thickeningRelativeDifferentialsMap`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.thickeningRelativeDifferentialsMap` is the restriction along
  `i : Z ⟶ Z'` of the canonical map `(h')^*Ω_{X/S} ⟶ Ω_{Z'/S}` of a morphism `h' : Z' ⟶ X`,
  which is the morphism Stacks Project, Tag 04FB asserts to be an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap` is the
  defining property of the canonical map.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.eq_relativeDifferentialsMap` and
  `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.unique` are its uniqueness.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_eq_of_comm` says that the canonical
  map depends only on `f`, `p` and `p'`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d` is the defining property in
  applied form: the transpose of the canonical map carries the universal differential of a
  local section to the universal differential of its pullback.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap` does not mention the base morphism
`g`, so `relativeDifferentialsMap_eq_of_comm` is immediate from the characterization: both maps
satisfy the same predicate, and the predicate has at most one solution. The hypothesis that
*some* commutative square exists is still needed, because that is what produces a solution at
all; it enters through the commutative square carried by either side of the equation.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')

/-- The canonical map on relative differentials of a commutative square is compatible with the
universal derivations: this is the property that characterizes it. -/
theorem isRelativeDifferentialsMap_relativeDifferentialsMap (g : S' ⟶ S)
    (hcomm : f ≫ p = p' ≫ g) :
    IsRelativeDifferentialsMap f p p' (relativeDifferentialsMap f p p' g hcomm) :=
  (isRelativeDifferentialsMap_iff_eq f p p' g hcomm _).mpr rfl

variable {f p p'}

/-- A morphism of relative differentials compatible with the universal derivations is the
canonical map of any commutative square with the same three edges. -/
theorem IsRelativeDifferentialsMap.eq_relativeDifferentialsMap
    {c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials p'}
    (hc : IsRelativeDifferentialsMap f p p' c) (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    c = relativeDifferentialsMap f p p' g hcomm :=
  (isRelativeDifferentialsMap_iff_eq f p p' g hcomm c).mp hc

/-- Two morphisms of relative differentials compatible with the universal derivations are equal.
A commutative square is still required, since without one the compatibility condition can be
vacuously unsatisfiable. -/
theorem IsRelativeDifferentialsMap.unique (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    {c d : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials p'}
    (hc : IsRelativeDifferentialsMap f p p' c) (hd : IsRelativeDifferentialsMap f p p' d) :
    c = d :=
  (hc.eq_relativeDifferentialsMap g hcomm).trans (hd.eq_relativeDifferentialsMap g hcomm).symm

/-- The canonical map on relative differentials depends only on the three morphisms `f`, `p` and
`p'`: changing the base morphism of the commutative square, or the proof that the square
commutes, does not change it. -/
theorem relativeDifferentialsMap_eq_of_comm (g₁ g₂ : S' ⟶ S) (hcomm₁ : f ≫ p = p' ≫ g₁)
    (hcomm₂ : f ≫ p = p' ≫ g₂) :
    relativeDifferentialsMap f p p' g₁ hcomm₁ = relativeDifferentialsMap f p p' g₂ hcomm₂ :=
  (isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g₁
    hcomm₁).eq_relativeDifferentialsMap g₂ hcomm₂

/-- The defining property of the canonical map on relative differentials, in applied form: its
transpose across the pullback-pushforward adjunction carries the universal differential of a
local section of `𝒪_X` to the universal differential of its pullback along `f`. -/
theorem relativeDifferentialsMap_app_d (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (U : X.Opens)
    (x : Γ(X, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (relativeDifferentials p)
        (relativeDifferentials p') (relativeDifferentialsMap f p p' g hcomm)).val.app
          (.op U)).hom ((universalRelativeDerivation p).d x) =
      (universalRelativeDerivation p').d ((f.app U).hom x) :=
  isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g hcomm U x

/-- The morphism of Stacks Project, Tag 04FB: for a morphism `h' : Z' ⟶ X` and a closed
subscheme `i : Z ⟶ Z'` of its source, the restriction along `i` of the canonical map
`(h')^*Ω_{X/S} ⟶ Ω_{Z'/S}`. When `Z ⟶ Z'` is the universal first-order thickening of a formally
unramified `Z ⟶ X`, Tag 04FB asserts that this morphism is an isomorphism. -/
noncomputable def thickeningRelativeDifferentialsMap {Z X Z' S : Scheme.{u}} (i : Z ⟶ Z')
    (h' : Z' ⟶ X) (p : X ⟶ S) :
    (Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback h').obj (relativeDifferentials p)) ⟶
      (Scheme.Modules.pullback i).obj (relativeDifferentials (h' ≫ p)) :=
  (Scheme.Modules.pullback i).map (relativeDifferentialsMap h' p (h' ≫ p) (𝟙 S) (by simp))

/-- The morphism of Tag 04FB is the restriction of the canonical map of *any* commutative square
with edges `h'`, `p` and `h' ≫ p`, not just of the one whose base morphism is the identity. -/
theorem thickeningRelativeDifferentialsMap_eq {Z X Z' S : Scheme.{u}} (i : Z ⟶ Z')
    (h' : Z' ⟶ X) (p : X ⟶ S) (g : S ⟶ S) (hcomm : h' ≫ p = (h' ≫ p) ≫ g) :
    thickeningRelativeDifferentialsMap i h' p =
      (Scheme.Modules.pullback i).map (relativeDifferentialsMap h' p (h' ≫ p) g hcomm) :=
  congrArg (Scheme.Modules.pullback i).map
    (relativeDifferentialsMap_eq_of_comm (𝟙 S) g (by simp) hcomm)

end AlgebraicGeometry.Scheme.Hom

end
