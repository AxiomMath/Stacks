module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelCategory
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCore.Tactic.StacksAttribute

/-!
# Base change on the category of Fourier-Mukai kernels

Let `s : S₁ ⟶ S` be a morphism of schemes. [Stacks, Tag 0G0G] asserts that the rule sending a
smooth proper scheme `X` over `S` to `X₁ = X ×_S S₁` over `S₁`, and the isomorphism class of a
perfect complex `K` on `X ×_S Y` to the isomorphism class of its derived pullback along the
canonical comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y`, is a functor from the category of
[Stacks, Tag 0G0F] for `S` to the one for `S₁`.

This file assembles that rule and proves everything about it that does not depend on the
category of [Stacks, Tag 0G0F] being available as a `CategoryTheory.Category`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiBaseChangeKernel` — the rule on morphisms, the derived pullback
  along `AlgebraicGeometry.fourierMukaiBaseChangeMap`.
* `AlgebraicGeometry.FourierMukaiKernelObj.baseChange`,
  `AlgebraicGeometry.FourierMukaiKernelObj.baseChangeHom` — the two rules on the objects and the
  morphisms of the category of [Stacks, Tag 0G0F].
* `AlgebraicGeometry.FourierMukaiKernelObj.baseChangeFunctorOf` — the functor they form, between
  the categories `AlgebraicGeometry.FourierMukaiKernelObj.categoryOf hconv` over `S` and over
  `S₁`.

## Main results

* `AlgebraicGeometry.smooth_baseChangeObj`, with Mathlib's instance that a base change of a
  proper morphism is proper — the rule on objects lands in smooth proper schemes over `S₁`, so
  clause (1) of the source is well defined.
* `AlgebraicGeometry.isPerfect_fourierMukaiBaseChangeKernel` and
  `AlgebraicGeometry.isIsomorphic_fourierMukaiBaseChangeKernel` — the rule on morphisms lands
  in `D_perf` and descends to isomorphism classes, so clause (2) is well defined.
* `AlgebraicGeometry.isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel` — **the
  functor axiom for identities**.
* `AlgebraicGeometry.isIsomorphic_fourierMukaiBaseChangeKernel_convolution` — **the
  functor axiom for composition**.

## Implementation notes

**Which side of the fibre product.** The source writes `X₁ = S₁ ×_S X`; here `X₁` is the chosen
pullback `X ×_S S₁` with structure morphism `pullback.snd f s`, the side at which this tree
proves the Tor-independence input [Stacks, Tag 0CTA]
(`AlgebraicGeometry.torIndependent_pullback_product_of_flat`). The two differ by the symmetry of
the fibre product, so nothing of the statement changes.

**The bundling.** The category of [Stacks, Tag 0G0F] is
`AlgebraicGeometry.FourierMukaiKernelObj.categoryOf hconv`, assembled from a proof `hconv` that
the convolution of two perfect kernels is perfect (the perfectness half of [Stacks, Tag 0B91]).
The functor is built for any such `hconv`; the functor axioms do not use it. The `@[stacks 0G0G]`
registration is placed on the instance of this functor at the proved `hconv`, once that exists.

**One copy of each base-change isomorphism.** The two isomorphisms behind the functor axioms are
`AlgebraicGeometry.diagonalKernelBaseChangeIsoOfIsPullback` and
`AlgebraicGeometry.convolutionBaseChangeIsoOfIsPullback` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/KernelBaseChange.lean`,
stated at arbitrary cartesian squares; the axioms here are their instances at the chosen fibre
products, with [Stacks, Tag 08IB] supplied by
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`.

**What the composition axiom needs.** The square carrying `pr₁₃` on `X₁ ×_{S₁} Y₁ ×_{S₁} Z₁` to
`pr₁₃` on `X ×_S Y ×_S Z` is cartesian, and the source quotes [Stacks, Tag 0B91] for the base
change of `R pr_{13,*}`. As in [Stacks, Tag 0G0K] the proof instead uses that `pr₁₃` is
**flat**, being a base change of `pr_X : X ×_S Y ⟶ X` along `pr_X : X ×_S Z ⟶ X`, hence Tor
independent from everything over `X ×_S Z`, so [Stacks, Tag 08IB] applies with no properness.

## References

* [Stacks Project, Tag 0G0G](https://stacks.math.columbia.edu/tag/0G0G)
* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Clause (1): the rule on objects -/

section Object

variable {S S₁ X : Scheme.{u}} (f : X ⟶ S) (s : S₁ ⟶ S)

/-- **The base change of a smooth morphism is smooth**, so the object rule of
[Stacks, Tag 0G0G] carries a smooth scheme over `S` to a smooth scheme over `S₁`. -/
theorem smooth_baseChangeObj [Smooth f] : Smooth (pullback.snd f s) :=
  MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f s) inferInstance

end Object

/-! ### Clause (2): the rule on morphisms -/

section Morphism

variable {S S₁ X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S₁ ⟶ S)

/-- **The comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y` is a base change of `s`.** This is the square
whose derived pullback the morphism rule of [Stacks, Tag 0G0G] is. -/
theorem isPullback_fourierMukaiBaseChangeMap :
    IsPullback (fourierMukaiBaseChangeMap f g s)
      (pullback.fst (pullback.snd f s) (pullback.snd g s) ≫ pullback.snd f s)
      (pullback.fst f g ≫ f) s :=
  isPullback_baseChangePullbackMap_base (IsPullback.of_hasPullback f s)
    (IsPullback.of_hasPullback g s)

/-- **The rule on morphisms of [Stacks, Tag 0G0G]**: the derived pullback
`L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^*K` of a kernel on `X ×_S Y` to a kernel on `X₁ ×_{S₁} Y₁`. -/
abbrev fourierMukaiBaseChangeKernel (K : DerivedCategory (pullback f g).Modules) :
    DerivedCategory (pullback (pullback.snd f s) (pullback.snd g s)).Modules :=
  (dpull (fourierMukaiBaseChangeMap f g s)).obj K

/-- **The base change of a perfect kernel is perfect**, so the rule on morphisms lands in
`D_perf(𝒪_{X₁ ×_{S₁} Y₁})` as [Stacks, Tag 0G0G] clause (2) asserts. This is
[Stacks, Tag 09UA]. -/
theorem isPerfect_fourierMukaiBaseChangeKernel (K : DerivedCategory (pullback f g).Modules)
    (hK : IsPerfect (X := (pullback f g).toRingedSpace) K) :
    IsPerfect (X := (pullback (pullback.snd f s) (pullback.snd g s)).toRingedSpace)
      (fourierMukaiBaseChangeKernel f g s K) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hK

/-- The base change of a kernel with quasi-coherent cohomology has quasi-coherent cohomology,
by [Stacks, Tag 08DW] part (1). -/
theorem isQCohAll_fourierMukaiBaseChangeKernel {K : DerivedCategory (pullback f g).Modules}
    (hK : IsQCohAll K) : IsQCohAll (fourierMukaiBaseChangeKernel f g s K) :=
  isQCohAll_dpull _ hK

/-- **The rule on morphisms descends to isomorphism classes.** Morphisms of the category of
[Stacks, Tag 0G0F] are isomorphism classes of perfect complexes, so this is what makes the rule
of [Stacks, Tag 0G0G] clause (2) well defined. -/
theorem isIsomorphic_fourierMukaiBaseChangeKernel
    (K L : DerivedCategory (pullback f g).Modules) (h : IsIsomorphic K L) :
    IsIsomorphic (fourierMukaiBaseChangeKernel f g s K)
      (fourierMukaiBaseChangeKernel f g s L) :=
  h.elim fun e => ⟨(dpull (fourierMukaiBaseChangeMap f g s)).mapIso e⟩

end Morphism

/-! ### The functor axiom for identities -/

section Identity

variable {S S₁ X : Scheme.{u}} (f : X ⟶ S) (s : S₁ ⟶ S)

/-- **[Stacks, Tag 0CTA] at the diagonal square**: for `f` flat, `X` and `X₁ ×_{S₁} X₁` are Tor
independent over `X ×_S X`. -/
theorem torIndependent_diagonal_fourierMukaiBaseChangeMap [Flat f] :
    TorIndependent (pullback.diagonal f) (fourierMukaiBaseChangeMap f f s) :=
  TorIndependent.symm (torIndependent_pullback_product_of_flat s f f (𝟙 X) (𝟙 X) rfl)

/-- **The base-change rule preserves identities.** For `f : X ⟶ S` flat and separated and any
`s : S₁ ⟶ S`, the derived pullback of the diagonal kernel `𝒪_{Δ_{X/S}}` along
`X₁ ×_{S₁} X₁ ⟶ X ×_S X` is isomorphic to the diagonal kernel `𝒪_{Δ_{X₁/S₁}}`. This is the
identity axiom of the functor of [Stacks, Tag 0G0G], the class of the diagonal kernel being the
identity morphism of the category of [Stacks, Tag 0G0F].

The isomorphism is `AlgebraicGeometry.diagonalKernelBaseChangeIsoOfIsPullback` at the square
`X ×_S S₁ ⟶ X`, with the Tor independence from [Stacks, Tag 0CTA] and [Stacks, Tag 08IB] from
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`. -/
theorem isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel [IsSeparated f] [Flat f] :
    IsIsomorphic (fourierMukaiBaseChangeKernel f f s (diagonalKernel f))
      (diagonalKernel (pullback.snd f s)) :=
  ⟨diagonalKernelBaseChangeIsoOfIsPullback
    (IsPullback.of_hasPullback f s) (torIndependent_diagonal_fourierMukaiBaseChangeMap f s)⟩

end Identity

/-! ### The functor axiom for composition -/

section Composition

variable {S S₁ X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (s : S₁ ⟶ S)

/-- **The base-change rule preserves composition.** For `g : Y ⟶ S` flat, quasi-compact and
quasi-separated, any `f : X ⟶ S`, `h : Z ⟶ S`, any `s : S₁ ⟶ S`, and kernels `K` on `X ×_S Y`
and `M` on `Y ×_S Z` with quasi-coherent cohomology (in particular perfect ones), the derived
pullback of the convolution `R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` of [Stacks, Tag 0FYS]
is isomorphic to the convolution of the derived pullbacks `K₁` of `K` and `M₁` of `M`. This is
the composition axiom of the functor of [Stacks, Tag 0G0G], convolution being composition in
the category of [Stacks, Tag 0G0F].

The isomorphism is `AlgebraicGeometry.convolutionBaseChangeIsoOfIsPullback` at the three squares
`X ×_S S₁ ⟶ X`, `Y ×_S S₁ ⟶ Y`, `Z ×_S S₁ ⟶ Z`, with [Stacks, Tag 08IB] from
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`. The source quotes
[Stacks, Tag 0B91] for the base change of `R pr_{13,*}`; the proof uses instead that `pr₁₃` is
flat, being a base change of `pr_X : X ×_S Y ⟶ X`, so that [Stacks, Tag 08IB] applies with no
properness. Of the source's smooth proper hypotheses only flatness, quasi-compactness and
quasi-separatedness of `g` are used. -/
theorem isIsomorphic_fourierMukaiBaseChangeKernel_convolution
    [QuasiCompact g] [QuasiSeparated g] [Flat g]
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {M : DerivedCategory (pullback g h).Modules} (hM : IsQCohAll M) :
    IsIsomorphic (fourierMukaiBaseChangeKernel f h s (fourierMukaiConvolution f g h K M))
      (fourierMukaiConvolution (pullback.snd f s) (pullback.snd g s) (pullback.snd h s)
        (fourierMukaiBaseChangeKernel f g s K) (fourierMukaiBaseChangeKernel g h s M)) :=
  ⟨convolutionBaseChangeIsoOfIsPullback
    (IsPullback.of_hasPullback f s) (IsPullback.of_hasPullback g s)
    (IsPullback.of_hasPullback h s) hK hM⟩

end Composition


/-! ### The functor on the category of Fourier-Mukai kernels -/

namespace FourierMukaiKernelObj

variable {S S₁ : Scheme.{u}}

/-- **Clause (1) of [Stacks, Tag 0G0G]**: the base change `X ×_S S₁ ⟶ S₁` of an object
`X ⟶ S` of the category of Fourier-Mukai kernels over `S`, which is again smooth and proper. -/
def baseChange (s : S₁ ⟶ S) (X : FourierMukaiKernelObj S) : FourierMukaiKernelObj S₁ where
  X := pullback X.f s
  f := pullback.snd X.f s
  smooth := smooth_baseChangeObj X.f s
  proper := inferInstance

/-- **Clause (2) of [Stacks, Tag 0G0G] on kernels**: the derived pullback
`L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^*K` of a perfect kernel, which is perfect by [Stacks, Tag 09UA]. -/
def baseChangeKernel (s : S₁ ⟶ S) {X Y : FourierMukaiKernelObj S} (K : PerfectKernel X Y) :
    PerfectKernel (X.baseChange s) (Y.baseChange s) :=
  ⟨fourierMukaiBaseChangeKernel X.f Y.f s K.obj,
    isPerfect_fourierMukaiBaseChangeKernel X.f Y.f s K.obj K.property⟩

/-- **Clause (2) of [Stacks, Tag 0G0G]**: the rule on morphisms, on isomorphism classes of
perfect kernels (`isIsomorphic_fourierMukaiBaseChangeKernel` makes it well defined). -/
def baseChangeHom (s : S₁ ⟶ S) {X Y : FourierMukaiKernelObj S} :
    Hom X Y → Hom (X.baseChange s) (Y.baseChange s) :=
  Quotient.map (baseChangeKernel s) fun _ _ ⟨e⟩ =>
    isIsomorphic_mk ((dpull (fourierMukaiBaseChangeMap _ _ s)).mapIso
      ((ObjectProperty.ι _).mapIso e))

/-- `baseChangeHom s` sends the class of a perfect kernel `K` to the class of
`baseChangeKernel s K`. -/
@[simp]
lemma baseChangeHom_mk (s : S₁ ⟶ S) {X Y : FourierMukaiKernelObj S} (K : PerfectKernel X Y) :
    baseChangeHom s ⟦K⟧ = ⟦baseChangeKernel s K⟧ :=
  rfl

/-- **The functor of [Stacks, Tag 0G0G]**, for the category of Fourier-Mukai kernels assembled by
`AlgebraicGeometry.FourierMukaiKernelObj.categoryOf` from a proof `hconv` that the convolution
of two perfect kernels is perfect (over every base, so over `S` and over `S₁`). On objects it is
`X ↦ X ×_S S₁` and on morphisms the class of `K` goes to the class of
`L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^*K`. Identities are preserved by
`isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel` and composition by
`isIsomorphic_fourierMukaiBaseChangeKernel_convolution`; neither uses `hconv`, which only enters
through the construction of the two categories. -/
def baseChangeFunctorOf
    (hconv : ∀ {T : Scheme.{u}} {X Y Z : FourierMukaiKernelObj T} (K : PerfectKernel X Y)
      (K' : PerfectKernel Y Z), IsPerfect (X := (pullback X.f Z.f).toRingedSpace)
        (fourierMukaiConvolution X.f Y.f Z.f K.obj K'.obj))
    (s : S₁ ⟶ S) :
    @Functor (FourierMukaiKernelObj S) (categoryOf hconv)
      (FourierMukaiKernelObj S₁) (categoryOf hconv) :=
  letI := categoryOf (S := S) hconv
  letI := categoryOf (S := S₁) hconv
  { obj := baseChange s
    map := baseChangeHom s
    map_id := fun X => by
      obtain ⟨e⟩ := isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel X.f s
      exact Quotient.sound (isIsomorphic_mk e)
    map_comp := by
      rintro X Y Z ⟨K⟩ ⟨M⟩
      obtain ⟨e⟩ := isIsomorphic_fourierMukaiBaseChangeKernel_convolution X.f Y.f Z.f s
        (isQCohAll_of_isPerfect K.property) (isQCohAll_of_isPerfect M.property)
      exact Quotient.sound (isIsomorphic_mk e) }

end FourierMukaiKernelObj

end AlgebraicGeometry

end
