module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The intersection of a quasi-coherent module with the direct image of a coherent submodule

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `F` be a
quasi-coherent `𝒪_X`-module, let `G` be a quasi-coherent `𝒪_Y`-module and let
`φ : G ⟶ f^*F` be a map of `𝒪_Y`-modules.  The module `F ∩ f_*G` is the fibre product of

```
                F ⟶ f_*f^*F ⟵ f_*G
```

whose left arrow is the unit of the adjunction `f^* ⊣ f_*` and whose right arrow is the direct
image of `φ`.  **Stacks 0GPR** asserts that `F ∩ f_*G` is a coherent `𝒪_X`-module when `φ` is
injective, `f` is quasi-compact, quasi-separated, flat and surjective, `X` and `Y` are locally
Noetherian, and `G` is coherent.

The module is constructed here, its inclusion into `F` is a monomorphism — so `F ∩ f_*G`
really is a submodule of `F` — and, for `f` flat and `φ` injective, its inverse image
`f^*(F ∩ f_*G)` is a submodule of `G`.  Stacks 0GPR itself is
`AlgebraicGeometry.Space.isCoherent_intersectionPushforward`, in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentIntersectionPushforwardCoherence.lean`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackPushforwardUnit` is the unit `F ⟶ f_*f^*F` of the adjunction
  of Stacks 03LU at a module `F`, the left arrow of the diagram above.
* `AlgebraicGeometry.Space.intersectionPushforward` is `F ∩ f_*G`, the fibre product of that
  diagram, with `AlgebraicGeometry.Space.intersectionPushforwardι` its projection to `F` and
  `AlgebraicGeometry.Space.intersectionPushforwardπ` its projection to `f_*G`.
* `AlgebraicGeometry.Space.intersectionPushforwardAdj` is the morphism `f^*(F ∩ f_*G) ⟶ G`
  adjoint to the projection to `f_*G`.

## Main results

* `AlgebraicGeometry.Space.isPullback_intersectionPushforward`: the defining square is cartesian.
* `AlgebraicGeometry.Space.mono_modulePushforward_map`: the direct image of a monomorphism of
  `𝒪_Y`-modules is a monomorphism, the direct image being a right adjoint.
* `AlgebraicGeometry.Space.mono_intersectionPushforwardι`: **`F ∩ f_*G` is a submodule of `F`**
  as soon as `φ` is injective.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_intersectionPushforward`: `F ∩ f_*G` is
  quasi-coherent as soon as `F`, `f_*G` and `f_*f^*F` are.
* `AlgebraicGeometry.Space.isPullback_map_intersectionPushforward`: **for `f` flat,
  `f^*(F ∩ f_*G)` is `f^*F ∩ f^*f_*G`**, the inverse image carrying the defining square to a
  cartesian square because it is left exact.
* `AlgebraicGeometry.Space.intersectionPushforwardAdj_comp` and
  `AlgebraicGeometry.Space.mono_intersectionPushforwardAdj`: the inverse image of the inclusion
  `F ∩ f_*G ⟶ F` factors through `φ`, so **for `f` flat and `φ` injective, `f^*(F ∩ f_*G)` is a
  submodule of `G`**.

## Implementation notes

### The quasi-coherence step

A fibre product in an abelian category is the kernel of the map `F ⊞ f_*G ⟶ f_*f^*F` induced by
the two arrows of the diagram with one of them negated, which is Mathlib's
`CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`.  Being
cartesian on affine charts is stable under kernels
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isLimit`) and quasi-coherence is stable
under binary biproducts (`SheafOfModules.isQuasicoherentOnSite_biprod`), so quasi-coherence of
the three corners gives quasi-coherence of the fibre product through Descent,
Proposition 03DX(2) in both directions.

### `f^*(F ∩ f_*G)` inside `G`

The source shows that `f^*F ∩ f^*f_*G` lies in the image of `G` by flat base change to
`Y ×_X Y` and a section of the first projection.  The same conclusion is formal here: the
morphism `ψ : f^*(F ∩ f_*G) ⟶ G` adjoint to the projection `F ∩ f_*G ⟶ f_*G` satisfies
`ψ ≫ φ = f^*ι`, because both sides are adjoint to the common composite `F ∩ f_*G ⟶ f_*f^*F` of
the defining square, and `f^*ι` is injective for `f` flat.

### Universes

The module universe is the universe `u` of the schemes throughout.  That is forced twice over:
the direct image and the inverse image of `𝒪`-modules along a morphism of algebraic spaces exist
only at that universe, and it is the universe in which the category of `𝒪_X`-modules is abelian,
hence has the fibre product.

## References

* [Stacks Project, Tag 0GPR](https://stacks.math.columbia.edu/tag/0GPR)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 060U](https://stacks.math.columbia.edu/tag/060U)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The unit `F ⟶ f_*f^*F` of the adjunction between the inverse image and the direct image of
`𝒪`-modules along a morphism `f : Y ⟶ X` of algebraic spaces, which is Stacks 03LU. -/
def pullbackPushforwardUnit (f : Y ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    F ⟶ (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj F) :=
  (modulePullbackAdjunction B S hS f).unit.app F

/-- **The module `F ∩ f_*G`.**  For a morphism `f : Y ⟶ X` of algebraic spaces and a map
`φ : G ⟶ f^*F` of `𝒪_Y`-modules, this is the fibre product of the unit `F ⟶ f_*f^*F` and the
direct image `f_*G ⟶ f_*f^*F` of `φ`.  The fibre product exists because the category of
`𝒪_X`-modules is abelian. -/
def intersectionPushforward (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    Modules.{u, u} B S hS X.1 X.2 :=
  pullback (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ)

/-- The projection of `F ∩ f_*G` to `F`. -/
abbrev intersectionPushforwardι (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    intersectionPushforward B S hS f φ ⟶ F :=
  pullback.fst (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ)

/-- The projection of `F ∩ f_*G` to `f_*G`. -/
abbrev intersectionPushforwardπ (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    intersectionPushforward B S hS f φ ⟶ (modulePushforward B S hS f).obj G :=
  pullback.snd (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ)

/-- The square exhibiting `F ∩ f_*G` as the fibre product of `F ⟶ f_*f^*F ⟵ f_*G` is
cartesian. -/
theorem isPullback_intersectionPushforward (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    IsPullback (intersectionPushforwardι B S hS f φ) (intersectionPushforwardπ B S hS f φ)
      (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ) :=
  IsPullback.of_hasPullback _ _

/-- The direct image of a monomorphism of `𝒪_Y`-modules along a morphism of algebraic spaces is
a monomorphism: the direct image is a right adjoint, by the adjunction of Stacks 03LU, and a
right adjoint preserves monomorphisms. -/
theorem mono_modulePushforward_map (f : Y ⟶ X) {G G' : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : G ⟶ G') (hφ : Mono φ) : Mono ((modulePushforward B S hS f).map φ) :=
  have := hφ
  have : (modulePushforward B S hS f).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction (modulePullbackAdjunction B S hS f)
  inferInstance

/-- **`F ∩ f_*G` is a submodule of `F`.**  If `φ` is injective then so is the direct image
`f_*G ⟶ f_*f^*F` of `φ`, and the projection of a fibre product onto the leg opposite a
monomorphism is a monomorphism. -/
theorem mono_intersectionPushforwardι (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    (hφ : Mono φ) : Mono (intersectionPushforwardι B S hS f φ) := by
  have := mono_modulePushforward_map B S hS f φ hφ
  have h : Mono (pullback.fst (pullbackPushforwardUnit B S hS f F)
      ((modulePushforward B S hS f).map φ)) := inferInstance
  exact h

/-- **`F ∩ f_*G` is quasi-coherent as soon as the three other corners of its defining diagram
are.**

The fibre product is the kernel of the map `F ⊞ f_*G ⟶ f_*f^*F` induced by the unit and the
negative of `f_*φ`; a binary biproduct of quasi-coherent modules is quasi-coherent, being
cartesian on affine charts is stable under kernels, and Descent, Proposition 03DX(2) converts
between the two conditions in both directions. -/
theorem isQuasicoherentOnSite_intersectionPushforward (f : Y ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} {G : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : G ⟶ (modulePullback B S hS f).obj F) (hF : F.IsQuasicoherentOnSite)
    (hpushG : ((modulePushforward B S hS f).obj G).IsQuasicoherentOnSite)
    (hpushPullF : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj F)).IsQuasicoherentOnSite) :
    (intersectionPushforward B S hS f φ).IsQuasicoherentOnSite := by
  have hbip : (F ⊞ (modulePushforward B S hS f).obj G).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_biprod hF hpushG
  have hcart : IsCartesianOnAffineCharts
      (pullback (pullbackPushforwardUnit B S hS f F)
        ((modulePushforward B S hS f).map φ)) := by
    refine isCartesianOnAffineCharts_of_isLimit
      (ι := Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct
        (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ))
      (φ := biprod.desc (pullbackPushforwardUnit B S hS f F)
        (-(modulePushforward B S hS f).map φ)) ?_ ?_
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hbip)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hpushPullF)
    · exact (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork
        (pullbackPushforwardUnit B S hS f F) ((modulePushforward B S hS f).map φ)).condition
    · exact Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _
  exact isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ hcart

/-- The inverse image along a flat morphism of algebraic spaces preserves finite limits. -/
private theorem preservesFiniteLimits_modulePullback_of_flat (f : Y ⟶ X)
    (hflat : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (modulePullback B S hS f) :=
  preservesFiniteLimits_modulePullback_of_isFlat B S hS f
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS f).1 hflat)

/-- **The flat inverse image of `F ∩ f_*G` is `f^*F ∩ f^*f_*G`.**  For `f` flat the inverse
image `f^*` is left exact, by Stacks 04JC at the small étale ringed topoi together with
Stacks 073C, so it carries the cartesian square defining `F ∩ f_*G` to a cartesian square.

This is the step "since `f` is flat this is equal to `f^*F ∩ f^*f_*G`" of the proof of
Stacks 0GPR. -/
theorem isPullback_map_intersectionPushforward (f : Y ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} {G : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : G ⟶ (modulePullback B S hS f).obj F) (hflat : IsFlat B S hS f.hom) :
    IsPullback ((modulePullback B S hS f).map (intersectionPushforwardι B S hS f φ))
      ((modulePullback B S hS f).map (intersectionPushforwardπ B S hS f φ))
      ((modulePullback B S hS f).map (pullbackPushforwardUnit B S hS f F))
      ((modulePullback B S hS f).map ((modulePushforward B S hS f).map φ)) := by
  have := preservesFiniteLimits_modulePullback_of_flat B S hS f hflat
  exact (isPullback_intersectionPushforward B S hS f φ).map (modulePullback B S hS f)

/-! ### The inverse image of `F ∩ f_*G` as a submodule of `G` -/

/-- The morphism `f^*(F ∩ f_*G) ⟶ G` adjoint to the projection `F ∩ f_*G ⟶ f_*G`, under the
adjunction `f^* ⊣ f_*` of Stacks 03LU. -/
def intersectionPushforwardAdj (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    (modulePullback B S hS f).obj (intersectionPushforward B S hS f φ) ⟶ G :=
  ((modulePullbackAdjunction B S hS f).homEquiv _ _).symm (intersectionPushforwardπ B S hS f φ)

/-- **The inverse image of the inclusion `F ∩ f_*G ⟶ F` factors through `φ`**: it is the
morphism `f^*(F ∩ f_*G) ⟶ G` adjoint to the projection onto `f_*G`, followed by `φ`.  Both
sides are adjoint to the common composite `F ∩ f_*G ⟶ f_*f^*F` of the defining square. -/
theorem intersectionPushforwardAdj_comp (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F) :
    intersectionPushforwardAdj B S hS f φ ≫ φ =
      (modulePullback B S hS f).map (intersectionPushforwardι B S hS f φ) := by
  apply ((modulePullbackAdjunction B S hS f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, intersectionPushforwardAdj, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  exact (isPullback_intersectionPushforward B S hS f φ).w.symm

/-- **For `f` flat and `φ` injective, `f^*(F ∩ f_*G)` is a submodule of `G`**: its inclusion
into `f^*F` is injective, `f^*` being left exact, and factors through `φ` by
`AlgebraicGeometry.Space.intersectionPushforwardAdj_comp`.

This is the step of the proof of Stacks 0GPR in which `f^*F ∩ f^*f_*G` is seen to lie in the
image of `G`. -/
theorem mono_intersectionPushforwardAdj (f : Y ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (φ : G ⟶ (modulePullback B S hS f).obj F)
    (mono : Mono φ) (flat : IsFlat B S hS f.hom) :
    Mono (intersectionPushforwardAdj B S hS f φ) := by
  have := preservesFiniteLimits_modulePullback_of_flat B S hS f flat
  have := mono_intersectionPushforwardι B S hS f φ mono
  have h : Mono ((modulePullback B S hS f).map (intersectionPushforwardι B S hS f φ)) :=
    inferInstance
  rw [← intersectionPushforwardAdj_comp B S hS f φ] at h
  exact mono_of_mono _ φ

end AlgebraicGeometry.Space

end
