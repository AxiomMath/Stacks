module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# A blowup for a homomorphism of perfect modules of Tor dimension at most one

Let `X` be a scheme and `φ : ℱ ⟶ 𝒢` a homomorphism of perfect `𝒪_X`-modules of Tor dimension at
most one which vanishes on a scheme-theoretically dense open `U ⊆ X`. Stacks tag 0ESV produces a
`U`-admissible blowup `b : X' ⟶ X` after which the kernel, the image and the cokernel of `b^*φ`
are again perfect `𝒪_{X'}`-modules of Tor dimension at most one.

The source's proof is three steps. The two-term object `(ℱ ⟶ 𝒢)` of `D(𝒪_X)` — the cone of
`φ[0]` — is perfect by tag 08CR, and its restriction to `U` vanishes, so tag 0ESQ supplies a
`U`-admissible blowup on which every cohomology module of its derived pullback is perfect of Tor
dimension at most one. Tag 0ESS identifies the derived pullbacks of `ℱ[0]` and `𝒢[0]` along that
blowup with the ordinary ones, which turns the long exact cohomology sequence of the pulled-back
cone into the statement that its `H^{-1}` is the kernel of `b^*φ` and its `H^0` the cokernel.
Finally the image is the kernel of the cokernel, so it is perfect of Tor dimension at most one by
tag 08CR and the long exact sequences of the two short exact sequences it sits in.

## Main definitions

* `AlgebraicGeometry.IsPerfectTorLEOne`: the source's phrase "a perfect `𝒪_Y`-module of tor
  dimension `≤ 1`", the conjunction of `Stacks.Cohomology.PerfectComplexes.IsPerfect` (tag 08CM)
  and `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` in `[-1, 0]` (tag 08CG) for the module
  placed in degree zero.

## Main results

* Stacks tag 0ESV itself is
  `AlgebraicGeometry.exists_admissibleBlowup_isPerfectTorLEOne_ker_im_coker`, proved without any
  carried hypothesis in `StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphismFittingBlowup`.
* `AlgebraicGeometry.isPerfectTorLEOne_abelianImage`: the last sentence of the source's proof,
  that the image of a homomorphism is perfect of Tor dimension at most one once the source's Tor
  dimension, the target, the kernel's Tor dimension and the cokernel are.
* `AlgebraicGeometry.isZero_derivedPullback_single_of_preservesFiniteLimits`: the derived pullback
  of a module placed in degree zero along a morphism with exact pullback — in particular along the
  inclusion of an open subscheme — vanishes as soon as the ordinary pullback does. This is what
  turns the source's hypotheses `ℱ|_U = 0` and `𝒢|_U = 0`, which are statements about the ordinary
  restriction, into the vanishing of the restriction of the cone in `D(𝒪_U)`.
* `AlgebraicGeometry.derivedToOrdinaryPullbackSingle_naturality`: the canonical comparison
  `Lf^*(ℳ[0]) ⟶ (f^*ℳ)[0]` of
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is natural in
  `ℳ`. This is what makes the square relating `H^0(Lb^*(φ[0]))` to `b^*φ` commute, and hence what
  identifies the kernel and cokernel of `b^*φ` rather than merely some kernel and cokernel.
* `AlgebraicGeometry.homologyKernelIso` and `AlgebraicGeometry.homologyCokernelIso`: in a
  distinguished triangle whose first two vertices are modules in degree zero, the third vertex has
  the kernel of the map for its `H^{-1}` and the cokernel for its `H^0`.

## Implementation notes

**Tag 0ESQ is carried.** The one input of the source's proof that this repository does not have is
tag 0ESQ, the blowup that makes every cohomology module of the derived pullback of a perfect
complex perfect of Tor dimension at most one. It was therefore carried as the explicit hypothesis
`hESQ` of a conditional form of tag 0ESV, now superseded by the unconditional
`AlgebraicGeometry.exists_admissibleBlowup_isPerfectTorLEOne_ker_im_coker`; `hESQ` was phrased
entirely in notions this repository already has: for every perfect `E ∈ D(𝒪_X)` all of whose
cohomology on the scheme-theoretically dense open `U` vanishes, there is a quasi-coherent ideal
sheaf `I` on `X`, cutting out a closed subscheme of finite presentation supported away from `U`,
such that every `H^i(Lb^*E)` is perfect of Tor dimension at most one for the blowup
`b = blowUpToBase I`. Two remarks on that shape.

* It is tag 0ESQ at the rank function `r = 0`: the tag's hypothesis is that `H^i(E|_U)` is finite
  locally free of *constant rank* `r_i`, and a finite locally free module of rank `0` is the zero
  module, which is how the vanishing is written here. Specializing the rank is a *weakening* of
  the hypothesis, so the theorem below is correspondingly stronger than one assuming the tag in
  full.
* The blowup is presented as `blowUpToBase I` rather than as an abstract
  `U`-admissible blowup. That is what the source's proof of tag 0ESQ produces — it blows up the
  product of the Fitting ideal sheaves of `E` — and `Stacks.Blowup.isAdmissibleBlowup_iff`
  turns it into `U`-admissibility, which is what the conclusion asserts. It is needed because tag
  0ESS is available in this repository only at `blowUpToBase I`
  (`AlgebraicGeometry.isIso_derivedPullbackComparison_blowUpToBase`), not at every morphism
  isomorphic to it, and tag 0ESS is the second ingredient of the source's proof.

Every other hypothesis of the source is consumed: `hU` and `hFU`, `hGU` discharge the hypotheses
of `hESQ`, perfectness of `ℱ` and `𝒢` gives perfectness of the cone by tag 08CR, and the Tor
dimension bounds on `ℱ` and `𝒢` feed tag 0ESS and the Tor amplitude of the image. Nothing about
the conclusion is assumed: `hESQ` speaks about the cohomology modules of a derived pullback, and
turning those into the kernel, image and cokernel of `b^*φ` is the content of tag 0ESV.

**Vocabulary.** `Lf^*` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the derived pullback of tag
06YJ, and `f^*` is `RingedSpaceModuleAdjunction.modulePullback`; both are taken at the morphism of
ringed spaces underlying a morphism of schemes, which is the spelling tags 0ESS and 0ESQ are
stated at in this repository. `H^i` is `DerivedCategory.homologyFunctor`, admissibility of a blowup
is `Stacks.Blowup.IsAdmissibleBlowup` (tag 080K) and scheme-theoretic density is
`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` (tag 01RB). The image is
`CategoryTheory.Abelian.image`, which *is* the source's "kernel of the cokernel".

## References

* [Stacks Project, Tag 0ESV](https://stacks.math.columbia.edu/tag/0ESV)
* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0ESS](https://stacks.math.columbia.edu/tag/0ESS)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### The derived pullback of a module placed in degree zero -/

section SingleModule

variable {Y Z : RingedSpace.{u, u}} (f : Y ⟶ Z)

/-- **The canonical map `Lf^*(ℳ[d]) ⟶ (f^*ℳ)[d]` is invertible as soon as the derived-pullback
comparison is invertible at the single complex on `ℳ`.** Three of the four factors of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` are components of
natural isomorphisms; the fourth is that comparison. -/
theorem isIso_derivedToOrdinaryPullbackSingle (M : SheafOfModules.{u} (structureSheafRing Z)) (d : ℤ)
    (h : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)))) :
    IsIso (derivedToOrdinaryPullbackSingle f M d) := by
  have h' : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)) := h
  unfold Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
  infer_instance

/-- **The canonical map `Lf^*(ℳ[d]) ⟶ (f^*ℳ)[d]` is natural in `ℳ`.** Each of the four factors of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is a component of a
natural transformation, so the four naturality squares compose to this one. -/
theorem derivedToOrdinaryPullbackSingle_naturality
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (ψ : M ⟶ N) (d : ℤ) :
    (derivedPullback f).map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).map ψ) ≫
      derivedToOrdinaryPullbackSingle f N d =
    derivedToOrdinaryPullbackSingle f M d ≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
        ((modulePullback f).map ψ) := by
  have h2 : (derivedPullback f).map (DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).map ψ)) ≫
      (derivedPullbackComparison f).app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj N) =
    (derivedPullbackComparison f).app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M) ≫
      DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).map ψ)) :=
    (derivedPullbackComparison f).naturality _
  have h3 : DerivedCategory.Qh.map
        (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).map ψ)) ≫
      DerivedCategory.Qh.map
        (((modulePullback f).mapHomotopyCategorySingleFunctor d).hom.app N) =
    DerivedCategory.Qh.map
        (((modulePullback f).mapHomotopyCategorySingleFunctor d).hom.app M) ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
          ((modulePullback f).map ψ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _
      (((modulePullback f).mapHomotopyCategorySingleFunctor d).hom.naturality ψ)
  have h4 : DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
          ((modulePullback f).map ψ)) ≫
      (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).inv.app
        ((modulePullback f).obj N) =
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).inv.app
        ((modulePullback f).obj M) ≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
        ((modulePullback f).map ψ) :=
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y))
        d).inv.naturality _
  unfold Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [(DerivedCategory.singleFunctorIsoCompQh
    (SheafOfModules.{u} (structureSheafRing Z)) d).hom.naturality ψ]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  congr 1
  rw [reassoc_of% h2, reassoc_of% h3, h4]

/-- **The square identifying `H^0(Lf^*(ψ[0]))` with `f^*ψ`.** Taking `H^0` of the canonical map
`Lf^*(ℳ[0]) ⟶ (f^*ℳ)[0]` and then the canonical identification `H^0(𝒩[0]) = 𝒩` gives a map
`H^0(Lf^*(ℳ[0])) ⟶ f^*ℳ`, and this square says that it carries `H^0(Lf^*(ψ[0]))` to `f^*ψ`. It is
what makes the kernel and cokernel read off a distinguished triangle below the kernel and cokernel
*of `f^*ψ`* rather than of some unrelated map. -/
theorem homologyFunctor_map_derivedToOrdinaryPullbackSingle_comm
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (ψ : M ⟶ N) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        ((derivedPullback f).map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).map ψ)) ≫
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
          (derivedToOrdinaryPullbackSingle f N 0) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app ((modulePullback f).obj N)) =
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
          (derivedToOrdinaryPullbackSingle f M 0) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app ((modulePullback f).obj M)) ≫
      (modulePullback f).map ψ := by
  rw [← Category.assoc, ← Functor.map_comp,
    derivedToOrdinaryPullbackSingle_naturality f ψ 0, Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg _ ((DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.naturality ((modulePullback f).map ψ))

/-- **The derived-pullback comparison is invertible at a single complex when the ordinary pullback
is exact.** A left-exact — hence, pullback being always right exact, exact — pullback functor keeps
a K-flat resolution of the single complex a quasi-isomorphism after applying it degreewise, and the
comparison is invertible at that K-flat resolution by tag 06YJ. -/
theorem isIso_derivedPullbackComparison_app_single_of_preservesFiniteLimits
    [PreservesFiniteLimits (modulePullback f)] (M : SheafOfModules.{u} (structureSheafRing Z)) (d : ℤ) :
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M))) := by
  have hph : (modulePullback f).PreservesHomology := inferInstance
  obtain ⟨K, g, hK, -, hg, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Z
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M)
  have := hg
  exact derivedPullbackComparison_isIso_of_quasiIso f g hg inferInstance
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f K hK)

/-- **A module placed in degree zero whose ordinary pullback vanishes has vanishing derived
pullback, along a morphism whose pullback functor is exact.** For the inclusion of an open
subspace this is the statement that `ℱ|_U = 0` implies `Lj^*(ℱ[0]) = 0`. -/
theorem isZero_derivedPullback_single_of_preservesFiniteLimits
    [PreservesFiniteLimits (modulePullback f)] (M : SheafOfModules.{u} (structureSheafRing Z))
    (hM : IsZero ((modulePullback f).obj M)) :
    IsZero ((derivedPullback f).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).obj M)) :=
  (Functor.map_isZero (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0)
      hM).of_iso
    (@asIso _ _ _ _ _ (isIso_derivedToOrdinaryPullbackSingle f M 0
      (isIso_derivedPullbackComparison_app_single_of_preservesFiniteLimits f M 0)))

end SingleModule

/-! ### Reading a kernel and a cokernel off a distinguished triangle -/

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The `H^{-1}` of the third vertex is the kernel.** Let `T` be a distinguished triangle whose
second vertex has vanishing `H^{-1}` and whose first two vertices have their `H^0` identified with
two objects `A`, `B` of `C` compatibly with a map `f : A ⟶ B`. Then `H^{-1}(T.obj₃)` is the kernel
of `f`: the connecting map `H^{-1}(T.obj₃) ⟶ H^0(T.obj₁)` is a monomorphism because `H^{-1}` of
the second vertex vanishes, and the exact sequence
`H^{-1}(T.obj₃) ⟶ H^0(T.obj₁) ⟶ H^0(T.obj₂)` then exhibits it as the kernel. -/
def homologyKernelIso (T : Triangle (DerivedCategory C)) (hT : T ∈ distinguishedTriangles)
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C (-1)).obj T.obj₂))
    {A B : C} (f : A ⟶ B)
    (e₁ : (DerivedCategory.homologyFunctor C 0).obj T.obj₁ ≅ A)
    (e₂ : (DerivedCategory.homologyFunctor C 0).obj T.obj₂ ≅ B)
    (comm : (DerivedCategory.homologyFunctor C 0).map T.mor₁ ≫ e₂.hom = e₁.hom ≫ f) :
    (DerivedCategory.homologyFunctor C (-1)).obj T.obj₃ ≅ kernel f := by
  have h₃ := DerivedCategory.HomologySequence.exact₃ T hT (-1) 0
  have h₁ := DerivedCategory.HomologySequence.exact₁ T hT (-1) 0
  have : Mono (DerivedCategory.HomologySequence.δ T (-1) 0) :=
    (ShortComplex.exact_iff_mono _ (h₂.eq_zero_of_src _)).mp h₃
  exact h₁.fIsKernel.conePointUniqueUpToIso (kernelIsKernel _) ≪≫
    kernel.mapIso _ f e₁ e₂ comm

/-- **The `H^0` of the third vertex is the cokernel.** Dually to
`AlgebraicGeometry.homologyKernelIso`: vanishing of `H^1` of the first vertex makes
`H^0(T.obj₂) ⟶ H^0(T.obj₃)` an epimorphism, and the exact sequence
`H^0(T.obj₁) ⟶ H^0(T.obj₂) ⟶ H^0(T.obj₃)` then exhibits `H^0(T.obj₃)` as the cokernel. -/
def homologyCokernelIso (T : Triangle (DerivedCategory C)) (hT : T ∈ distinguishedTriangles)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C 1).obj T.obj₁))
    {A B : C} (f : A ⟶ B)
    (e₁ : (DerivedCategory.homologyFunctor C 0).obj T.obj₁ ≅ A)
    (e₂ : (DerivedCategory.homologyFunctor C 0).obj T.obj₂ ≅ B)
    (comm : (DerivedCategory.homologyFunctor C 0).map T.mor₁ ≫ e₂.hom = e₁.hom ≫ f) :
    (DerivedCategory.homologyFunctor C 0).obj T.obj₃ ≅ cokernel f := by
  have h₃ := DerivedCategory.HomologySequence.exact₃ T hT 0 1
  have h₂ := DerivedCategory.HomologySequence.exact₂ T hT 0
  have : Epi ((DerivedCategory.homologyFunctor C 0).map T.mor₂) :=
    (ShortComplex.exact_iff_epi _ (h₁.eq_zero_of_tgt _)).mp h₃
  exact h₂.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel _) ≪≫
    cokernel.mapIso _ f e₁ e₂ comm

end Triangle

/-! ### Perfect modules of Tor dimension at most one -/

/-- **A perfect `𝒪_Y`-module of Tor dimension at most one.** The source's phrase "a perfect
`𝒪_Y`-module of tor dimension `≤ 1`": the module, placed in degree zero, is a perfect object of
`D(𝒪_Y)` in the sense of Stacks tag 08CM and has Tor amplitude in `[-1, 0]` in the sense of Stacks
tag 08CG. This is the spelling of the neighbouring tags 0ESN, 0ESQ and 0ESS in this
repository. -/
abbrev IsPerfectTorLEOne (Y : Scheme.{u}) (M : OXMod.{u, u} Y.toRingedSpace) : Prop :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) ∧
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) (-1) 0

/-- Being perfect of Tor dimension at most one depends only on the isomorphism class of the
module. -/
theorem IsPerfectTorLEOne.of_iso {Y : Scheme.{u}} {M N : OXMod.{u, u} Y.toRingedSpace}
    (e : M ≅ N) (h : IsPerfectTorLEOne Y M) : IsPerfectTorLEOne Y N :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).mapIso e) h.1,
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h.2
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).mapIso e.symm)⟩

/-! ### The image -/

/-- The kernel sequence of an epimorphism is short exact. -/
private theorem shortExact_kernelSequence {C : Type*} [Category C] [Abelian C] {X Y : C}
    (g : X ⟶ Y) [Epi g] : (ShortComplex.kernelSequence g).ShortExact :=
  { exact := ShortComplex.kernelSequence_exact g
    epi_g := by dsimp only [ShortComplex.kernelSequence]; infer_instance }

/-- **The last sentence of the proof of Stacks tag 0ESV.** The image of a homomorphism
`φ : ℱ ⟶ 𝒢` of `𝒪_Y`-modules is perfect of Tor dimension at most one as soon as `𝒢` and the
cokernel of `φ` are, and `ℱ` and the kernel of `φ` have Tor dimension at most one.

Perfectness is Stacks tag 08CR applied to the distinguished triangle of the short exact sequence
`0 ⟶ Im(φ) ⟶ 𝒢 ⟶ Coker(φ) ⟶ 0`, the image being the kernel of the cokernel. For the Tor
amplitude that triangle gives the vanishing in degrees `< -1`, through
`H^{i - 1}(Coker(φ) ⊗^L 𝒩) ⟶ H^i(Im(φ) ⊗^L 𝒩) ⟶ H^i(𝒢 ⊗^L 𝒩)`, and the triangle of
`0 ⟶ Ker(φ) ⟶ ℱ ⟶ Im(φ) ⟶ 0` gives it in degrees `> 0`, through
`H^i(ℱ ⊗^L 𝒩) ⟶ H^i(Im(φ) ⊗^L 𝒩) ⟶ H^{i + 1}(Ker(φ) ⊗^L 𝒩)`. -/
theorem isPerfectTorLEOne_abelianImage {Y : Scheme.{u}} {F G : OXMod.{u, u} Y.toRingedSpace}
    (φ : F ⟶ G)
    (hF : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj F) (-1) 0)
    (hG : IsPerfectTorLEOne Y G)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj (kernel φ)) (-1) 0)
    (hC : IsPerfectTorLEOne Y (cokernel φ)) :
    IsPerfectTorLEOne Y (Abelian.image φ) := by
  have hS := shortExact_kernelSequence (Abelian.factorThruImage φ)
  have hT := shortExact_kernelSequence (cokernel.π φ)
  have hkq : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj
        (kernel (Abelian.factorThruImage φ))) (-1) 0 := by
    refine Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} hK
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).mapIso ?_)
    exact (kernelCompMono (Abelian.factorThruImage φ) (Abelian.image.ι φ)).symm ≪≫
      kernel.mapIso _ φ (Iso.refl _) (Iso.refl _) (by simp)
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    hT.singleTriangle hT.singleTriangle_distinguished hG.1 hC.1, ?_⟩
  intro N i hi
  -- `- ⊗^L 𝒩[0]`, named at the spelling in which the two triangles live.
  let A : DerivedCategory (OXMod.{u, u} Y.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} Y.toRingedSpace) :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj N)
  let hcs : A.CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).commShift_left _
  let hit : A.IsTriangulated :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).exact_left _
  by_cases hn : i < -1
  · have hd : A.mapTriangle.obj hT.singleTriangle ∈ distinguishedTriangles :=
      A.map_distinguished _ hT.singleTriangle_distinguished
    refine (DerivedCategory.HomologySequence.exact₁ _ hd (i - 1) i (by omega)).isZero_X₂ ?_ ?_
    · exact (hC.2 N (i - 1) (by simp only [Set.mem_Icc]; omega)).eq_of_src _ _
    · exact (hG.2 N i (by simp only [Set.mem_Icc]; omega)).eq_of_tgt _ _
  · have hp : 0 < i := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hi
      omega
    have hd : A.mapTriangle.obj hS.singleTriangle ∈ distinguishedTriangles :=
      A.map_distinguished _ hS.singleTriangle_distinguished
    refine (DerivedCategory.HomologySequence.exact₃ _ hd i (i + 1) (by omega)).isZero_X₂ ?_ ?_
    · exact (hF N i (by simp only [Set.mem_Icc]; omega)).eq_of_src _ _
    · exact (hkq N (i + 1) (by simp only [Set.mem_Icc]; omega)).eq_of_tgt _ _

/-! ### Stacks tag 0ESV -/

end AlgebraicGeometry

end
