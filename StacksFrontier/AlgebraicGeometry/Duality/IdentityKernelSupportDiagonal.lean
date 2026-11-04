module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionDisplay
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelStepTwo
public import StacksFrontier.Homology.Tor.DerivedTensorTopDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Blowup.AlmostExactness
public import StacksFrontier.RingTheory.LocalRing.TensorNontrivial
import StacksCore.Tactic.StacksAttribute

/-!
# Step 3 of the proof of Tag 0G0E: the support of the kernel lies over the diagonal

Let `k` be a field, let `X` be a smooth proper `k`-scheme, let `K` be a perfect object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic
to the identity, and let `𝒦` be a module with `K ≅ 𝒦[0]` — which steps 1 and 2 provide.  This
file proves

`Supp 𝒦 ⊆ Δ(X)`,

the set fact that the source's third step extracts from "`R pr_{2,*}(pr_1^*𝓕 ⊗ 𝒦)` is `𝓕`, by
taking `𝓕` supported at closed points".  It is what makes the scheme-theoretic support of `𝒦`
finite over `X` along `pr_2`, which is the hypothesis [Stacks, Tag 0FZP] needs.

## Main results

* `Stacks.DerivedTensor.nontrivial_homologyZero_derivedTensor_triple` — over a local ring, the
  degree-zero cohomology of `M₁[0] ⊗^𝐋 M₂[0] ⊗^𝐋 M₃[0]` is nonzero for three nonzero finite
  modules.  This is Nakayama, twice.
* `AlgebraicGeometry.derivedStalkTripleTensorIso` — the derived stalk of a triple derived tensor
  product of modules in degree zero, computed by the derived form of [Stacks, Tag 01CB].
* `Stacks.Duality.isZero_modulesStalk_of_closedPoint_ne` — at a point of `X ×_k X` whose two
  projections are *distinct closed points*, the stalk of `𝒦` vanishes.
* `Stacks.Duality.supp_subset_range_diagonal` — **the set fact**: `Supp 𝒦 ⊆ Δ(X)`.

## Implementation notes

*The test object.*  For closed points `x ≠ y` of `X` the source's test module at `x` is paired
with a second test module at `y`, and the object tested is

`T = (L pr_1^*(𝒪_X/𝔪_x)[0] ⊗^𝐋 K) ⊗^𝐋 L pr_2^*(𝒪_X/𝔪_y)[0]`.

Along the projection formula of [Stacks, Tag 0B54] — in the assembled form
`AlgebraicGeometry.fourierMukaiTensorSingleIsoOfIsPerfect`, which asks only that the module on
the base be perfect in degree zero, and a coherent module on the regular `X` is —

`R pr_{2,*}T ≅ Φ_K(𝒪_X/𝔪_x[0]) ⊗^𝐋 (𝒪_X/𝔪_y)[0] ≅ (𝒪_X/𝔪_x)[0] ⊗^𝐋 (𝒪_X/𝔪_y)[0]`,

and the right-hand side vanishes because the two test modules have disjoint supports: its
derived stalk at a point `p` is a derived tensor product over `𝒪_{X,p}` one of whose factors is
zero, `p` being different from `x` or from `y`.

So `R pr_{2,*}T` has no cohomology at all, and the conservativity of `R pr_{2,*}` on complexes
supported over a closed subset of an affine open of the first factor
(`SupportedPushforwardReflect.isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd`)
turns that into `T = 0`.  Reading `T = 0` on the derived stalk at a point `w` over `(x, y)`
computes, by the derived form of [Stacks, Tag 01CB], a triple derived tensor product of three
modules over `𝒪_{X ×_k X, w}` placed in degree zero; its degree-zero cohomology is
`((pr_1^*𝒪_X/𝔪_x)_w ⊗ 𝒦_w) ⊗ (pr_2^*𝒪_X/𝔪_y)_w`, and Nakayama makes that nonzero unless
`𝒦_w = 0`.  The two pulled-back test modules have nonzero stalk at `w` because their supports
are `pr_1^{-1}{x}` and `pr_2^{-1}{y}` ([Stacks, Tag 056J]).

*From closed points to all points.*  `Supp 𝒦 \ Δ(X)` is the intersection of a closed set with an
open one, hence locally closed; if it were nonempty it would contain a point closed in
`X ×_k X`, that scheme being a Jacobson space, and the two projections of such a point are
closed points of `X` ([Stacks, Tag 01TB]).  The previous paragraph forbids them from being
distinct, and they cannot be equal either, since then the point would lie on the diagonal.

*Why the flat pullbacks are harmless.*  `pr_1` and `pr_2` are both flat, being base changes of a
morphism to the spectrum of a field, so the derived pullbacks of the test modules placed in
degree zero are their ordinary pullbacks placed in degree zero
(`AlgebraicGeometry.derivedPullbackSingleIsoOfFlat`).

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZP](https://stacks.math.columbia.edu/tag/0FZP)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-! ### Nakayama for a triple derived tensor product over a local ring -/

namespace Stacks.DerivedTensor

open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **The degree-zero cohomology of `M[0] ⊗^𝐋_A N[0]` is nonzero** for two nonzero finite
modules over a local ring: it is `M ⊗_A N`, which Nakayama makes nonzero. -/
theorem nontrivial_homologyZero_derivedTensor_single_single (M N : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Finite A N] [Nontrivial M] [Nontrivial N] :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) :=
  have : Nontrivial (TensorProduct A M N) := Stacks.LocalRing.nontrivial_tensorProduct _ _
  (homologyZeroIsoTensorProduct A M N).toLinearEquiv.toEquiv.nontrivial_congr.mpr
    (by exact inferInstance)

omit [IsLocalRing A] in
/-- The degree-zero cohomology of `M[0] ⊗^𝐋_A N[0]` is a finite module: it is `M ⊗_A N`. -/
theorem finite_homologyZero_derivedTensor_single_single (M N : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Finite A N] :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) :=
  Module.Finite.equiv (homologyZeroIsoTensorProduct A M N).toLinearEquiv.symm

/-- **The degree-zero cohomology of `P ⊗^𝐋_A N[0]` is nonzero** when `P` has no cohomology above
degree zero and both `H⁰(P)` and `N` are nonzero finite modules over a local ring: the
top-degree identification `Stacks.DerivedTensor.nonempty_homology_top_derivedTensor_single_iso`
computes it as `H⁰(P) ⊗_A N`, which Nakayama makes nonzero. -/
theorem nontrivial_homologyZero_derivedTensor_single (P : DObj A) (hP : P.IsLE 0)
    (N : ModuleCat.{u} A)
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)]
    [Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)]
    [Module.Finite A N] [Nontrivial N] :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj P).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  obtain ⟨e⟩ := nonempty_homology_top_derivedTensor_single_iso A P 0 hP N
  have : Nontrivial (TensorProduct A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P) N) :=
    Stacks.LocalRing.nontrivial_tensorProduct _ _
  exact e.toLinearEquiv.toEquiv.nontrivial_congr.mpr (by exact inferInstance)

/-- **Nakayama twice**: over a local ring the degree-zero cohomology of
`(M₁[0] ⊗^𝐋 M₂[0]) ⊗^𝐋 M₃[0]` is nonzero for three nonzero finite modules. -/
theorem nontrivial_homologyZero_derivedTensor_triple (M₁ M₂ M₃ : ModuleCat.{u} A)
    [Module.Finite A M₁] [Module.Finite A M₂] [Module.Finite A M₃]
    [Nontrivial M₁] [Nontrivial M₂] [Nontrivial M₃] :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj
            (((canonicalDerivedTensorProductFunctor A).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₁)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₂))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₃))) :=
  have hLE : (((canonicalDerivedTensorProductFunctor A).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₁)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₂)).IsLE 0 := by
    have h := isLE_tensor (canonicalDerivedTensorProduct A)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₁)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₂) 0 0
    simpa using h
  have := finite_homologyZero_derivedTensor_single_single M₁ M₂
  have := nontrivial_homologyZero_derivedTensor_single_single M₁ M₂
  nontrivial_homologyZero_derivedTensor_single _ hLE M₃

end Stacks.DerivedTensor

/-! ### The derived stalk of a triple derived tensor product -/

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived stalk of a derived tensor product of two modules placed in degree zero. -/
def derivedStalkSingleTensorIso (W : Scheme.{u}) (w : ↥W) (M N : W.Modules) :
    (derivedStalkFunctor w).obj
        ((dtenLeft W ((DerivedCategory.singleFunctor W.Modules 0).obj M)).obj
          ((DerivedCategory.singleFunctor W.Modules 0).obj N)) ≅
      ((localRingDerivedTensor W w).tensor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk w)) 0).obj
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk w)) 0).obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj N)) :=
  derivedStalkTensorIso W w _ _ ≪≫
    ((localRingDerivedTensor W w).tensor.mapIso
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).mapDerivedCategorySingleFunctor
          0).app M)).app _ ≪≫
      ((localRingDerivedTensor W w).tensor.obj _).mapIso
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).mapDerivedCategorySingleFunctor
          0).app N)

/-- **The derived stalk of a triple derived tensor product of modules placed in degree zero**,
computed by the derived form of [Stacks, Tag 01CB]. -/
def derivedStalkTripleTensorIso (W : Scheme.{u}) (w : ↥W) (M₁ M₂ M₃ : W.Modules) :
    (derivedStalkFunctor w).obj
        ((dtenLeft W ((dtenLeft W ((DerivedCategory.singleFunctor W.Modules 0).obj M₁)).obj
            ((DerivedCategory.singleFunctor W.Modules 0).obj M₂))).obj
          ((DerivedCategory.singleFunctor W.Modules 0).obj M₃)) ≅
      ((localRingDerivedTensor W w).tensor.obj
          (((localRingDerivedTensor W w).tensor.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk w)) 0).obj
                ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M₁))).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk w)) 0).obj
              ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M₂)))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk w)) 0).obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M₃)) :=
  derivedStalkTensorIso W w _ _ ≪≫
    ((localRingDerivedTensor W w).tensor.mapIso
        (derivedStalkSingleTensorIso W w M₁ M₂)).app _ ≪≫
      ((localRingDerivedTensor W w).tensor.obj _).mapIso
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).mapDerivedCategorySingleFunctor
          0).app M₃)

/-- Tensoring a zero object of `D(𝒪_{W,w})` on the right with anything is zero: the derived
tensor product of [Stacks, Tag 0BYI] is exact, hence additive, in its second variable. -/
theorem isZero_localRingDerivedTensor_of_isZero_right (W : Scheme.{u}) (w : ↥W)
    (P Q : DerivedCategory (ModuleCat.{u} (W.presheaf.stalk w))) (hQ : IsZero Q) :
    IsZero (((localRingDerivedTensor W w).tensor.obj P).obj Q) :=
  let _ := (localRingDerivedTensor W w).commShift_right P
  let _ := (localRingDerivedTensor W w).exact_right P
  Functor.map_isZero ((localRingDerivedTensor W w).tensor.obj P) hQ

/-- **A module whose stalks all vanish is zero**, in the `modulesStalkFunctor` spelling. -/
theorem isZero_of_forall_isZero_modulesStalk {W : Scheme.{u}} (M : W.Modules)
    (h : ∀ w : ↥W, IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M)) :
    IsZero M :=
  isZero_of_forall_isZero_stalk M fun w =>
    (SheafOfModules.isZero_stalkFunctor_obj_iff _ w M).1
      (isZero_stalkFunctor_of_isZero_modulesStalk w (h w))

/-- **An object of `D(𝒪_W)` whose derived stalks all vanish has vanishing cohomology sheaves.** -/
theorem isZero_homology_of_forall_isZero_derivedStalk {W : Scheme.{u}}
    (E : DerivedCategory W.Modules)
    (h : ∀ w : ↥W, IsZero ((derivedStalkFunctor w).obj E)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj E) :=
  isZero_of_forall_isZero_modulesStalk _ fun w =>
    IsZero.of_iso
      (Functor.map_isZero
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk w)) i) (h w))
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).mapDerivedCategoryHomologyIso i).app
        E).symm

/-- **The derived tensor product of two modules with disjoint supports, placed in degree zero,
has vanishing cohomology sheaves.**  At every point one of the two stalks is zero, so the
derived stalk of the tensor product vanishes by the derived form of [Stacks, Tag 01CB]. -/
@[sga "4 XVIII 1.3.17" "more general"]
theorem isZero_homology_dtenL_single_of_supp_disjoint {W : Scheme.{u}} (M N : W.Modules)
    (h : ∀ w : ↥W, IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M) ∨
      IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj N)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((dtenLeft W ((DerivedCategory.singleFunctor W.Modules 0).obj M)).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj N))) := by
  refine isZero_homology_of_forall_isZero_derivedStalk _ (fun w => ?_) i
  refine IsZero.of_iso ?_ (derivedStalkSingleTensorIso W w M N)
  rcases h w with hM | hN
  · exact Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_isZero_left
      (localRingDerivedTensor W w) _ _
      (Functor.map_isZero (DerivedCategory.singleFunctor _ 0) hM)
  · exact isZero_localRingDerivedTensor_of_isZero_right W w _ _
      (Functor.map_isZero (DerivedCategory.singleFunctor _ 0) hN)

/-! ### Two transports between the two spellings of a stalk -/

/-- **A module whose stalk vanishes in the `Scheme.Modules.stalkFunctor` spelling has vanishing
stalk in the `modulesStalkFunctor` spelling.**  This is the converse of
`AlgebraicGeometry.isZero_stalkFunctor_of_isZero_modulesStalk`; the two stalks have the same
carrier. -/
theorem isZero_modulesStalk_of_isZero_stalkFunctor {W : Scheme.{u}} (w : ↥W) {M : W.Modules}
    (h : IsZero ((Scheme.Modules.stalkFunctor W w).obj M)) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M) := by
  refine IsZero.of_iso ?_ ((restrictScalarsStalkFunctorIso w).app M).symm
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact h

/-- A point outside the support of a module is a point where its stalk vanishes, in the
`modulesStalkFunctor` spelling. -/
theorem isZero_modulesStalk_of_notMem_supp {W : Scheme.{u}} {M : W.Modules} {w : ↥W}
    (h : w ∉ SheafOfModules.supp M) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M) :=
  isZero_modulesStalk_of_isZero_stalkFunctor w
    ((Scheme.Modules.notMem_supp_iff_isZero_stalk M w).1 h)

/-- A point of the support of a module is a point where its stalk is nonzero, in the
`modulesStalkFunctor` spelling. -/
theorem nontrivial_modulesStalk_of_mem_supp {W : Scheme.{u}} {M : W.Modules} {w : ↥W}
    (h : w ∈ SheafOfModules.supp M) :
    Nontrivial ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  exact (Scheme.Modules.notMem_supp_iff_isZero_stalk M w).2
    (isZero_stalkFunctor_of_isZero_modulesStalk w
      (ModuleCat.isZero_iff_subsingleton.2 hs)) h

end AlgebraicGeometry

/-! ### The support of the kernel lies over the diagonal -/

namespace Stacks.Duality

open AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- **The stalk of `𝒦` vanishes at a point whose two projections are distinct closed points.**

For closed points `x ≠ y` the object
`T = (L pr_1^*(𝒪_X/𝔪_x)[0] ⊗^𝐋 K) ⊗^𝐋 L pr_2^*(𝒪_X/𝔪_y)[0]` has zero direct image along `pr_2`,
by the projection formula and the vanishing of `(𝒪_X/𝔪_x)[0] ⊗^𝐋 (𝒪_X/𝔪_y)[0]`; the
conservativity of `R pr_{2,*}` on complexes supported over a closed subset of an affine open of
the first factor makes `T` itself zero, and its derived stalk at `w` is a triple derived tensor
product whose degree-zero cohomology Nakayama would make nonzero.  See the implementation notes
of this file. -/
theorem isZero_modulesStalk_of_closedPoint_ne
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : RepresentsIdentityOnPerfect f K)
    (𝒦 : (Limits.pullback f f).Modules) [𝒦.IsQuasicoherent] [𝒦.IsFiniteType]
    (eK : K ≅ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj 𝒦)
    {x y : ↥X} (hx : IsClosed ({x} : Set ↥X)) (hy : IsClosed ({y} : Set ↥X)) (hxy : x ≠ y)
    (w : ↥(Limits.pullback f f))
    (hw₁ : (Limits.pullback.fst f f).base w = x)
    (hw₂ : (Limits.pullback.snd f f).base w = y) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Limits.pullback f f) w).obj 𝒦) := by
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have := isNoetherian_pullback_self f
  have hFxc : (pointTestModule x 1).IsCoherent := isCoherent_pointTestModule x 1
  have hFyc : (pointTestModule y 1).IsCoherent := isCoherent_pointTestModule y 1
  have : (pointTestModule x 1).IsFiniteType := hFxc.isFiniteType
  have : (pointTestModule y 1).IsFiniteType := hFyc.isFiniteType
  have : (pointTestModule x 1).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (pointTestModule y 1).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hsx : SheafOfModules.supp (pointTestModule x 1) = {x} :=
    supp_pointTestModule x hx one_ne_zero
  have hsy : SheafOfModules.supp (pointTestModule y 1) = {y} :=
    supp_pointTestModule y hy one_ne_zero
  have : ((Scheme.Modules.pullback (Limits.pullback.fst f f)).obj
      (pointTestModule x 1)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  have : ((Scheme.Modules.pullback (Limits.pullback.snd f f)).obj
      (pointTestModule y 1)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  -- the two flat-pullback identifications
  have eNx := derivedPullbackSingleIsoOfFlat (Limits.pullback.fst f f) (pointTestModule x 1)
  have eNy := derivedPullbackSingleIsoOfFlat (Limits.pullback.snd f f) (pointTestModule y 1)
  -- the test object, and the same object written with the ordinary pullbacks
  have eA : (dtenR (Limits.pullback f f) K).obj ((dpull (Limits.pullback.fst f f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule x 1))) ≅
      (dtenLeft (Limits.pullback f f) ((DerivedCategory.singleFunctor
          (Limits.pullback f f).Modules 0).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f f)).obj (pointTestModule x 1)))).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj 𝒦) :=
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (Limits.pullback f f).toRingedSpace.sheaf).flip.obj K).mapIso eNx ≪≫
      (dtenLeft (Limits.pullback f f) _).mapIso eK
  have eT := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Limits.pullback f f).toRingedSpace.sheaf).mapIso eA).app
        ((dpull (Limits.pullback.snd f f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule y 1))) ≪≫
    (dtenLeft (Limits.pullback f f) _).mapIso eNy
  -- the direct image of the test object has no cohomology
  have hFxperf : perfectDerivedObjects X
      ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule x 1)) :=
    perfectDerivedObjects_single_of_coherentObjects hreg ⟨_, hFxc⟩
  have hFyperf : perfectDerivedObjects X
      ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule y 1)) :=
    perfectDerivedObjects_single_of_coherentObjects hreg ⟨_, hFyc⟩
  obtain ⟨eId⟩ := nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect f K hΦ
  have hdisj : ∀ q : ↥X,
      IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X q).obj (pointTestModule x 1)) ∨
      IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X q).obj (pointTestModule y 1)) := by
    intro q
    by_cases hq : q = x
    · refine Or.inr (isZero_modulesStalk_of_notMem_supp ?_)
      rw [hsy, Set.mem_singleton_iff, hq]
      exact hxy
    · refine Or.inl (isZero_modulesStalk_of_notMem_supp ?_)
      rw [hsx, Set.mem_singleton_iff]
      exact hq
  have hpush : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((dpush (Limits.pullback.snd f f)).obj
        ((dtenLeft (Limits.pullback f f) ((dtenR (Limits.pullback f f) K).obj
            ((dpull (Limits.pullback.fst f f)).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule x 1))))).obj
          ((dpull (Limits.pullback.snd f f)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule y 1)))))) := by
    intro i
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((fourierMukaiTensorSingleIsoOfIsPerfect f f K (pointTestModule x 1)
          (pointTestModule y 1) hFyperf).symm ≪≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          X.toRingedSpace.sheaf).mapIso (eId.app ⟨_, hFxperf⟩)).app _))
    exact isZero_homology_dtenL_single_of_supp_disjoint _ _ hdisj i
  -- the test object has quasi-coherent cohomology supported over `x`
  have hqc : ∀ {E : DerivedCategory (Limits.pullback f f).Modules}
      {M : (Limits.pullback f f).Modules} [M.IsQuasicoherent],
      (E ≅ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj M) →
      ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).obj
        E).IsQuasicoherent :=
    fun e j => (SheafOfModules.isQuasicoherent (Limits.pullback f f).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).mapIso e).symm
      (isQuasicoherent_homology_singleFunctor_obj _ _ inferInstance j)
  have hA₀qc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).obj
      ((dtenR (Limits.pullback f f) K).obj ((dpull (Limits.pullback.fst f f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (pointTestModule x 1))))).IsQuasicoherent :=
    TorFormula.isQuasicoherent_homology_derivedTensor (Limits.pullback f f) _ K
      (hqc eNx) (hqc eK)
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).obj
      ((dtenLeft (Limits.pullback f f) ((dtenR (Limits.pullback f f) K).obj
          ((dpull (Limits.pullback.fst f f)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule x 1))))).obj
        ((dpull (Limits.pullback.snd f f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (pointTestModule y 1))))).IsQuasicoherent :=
    fun j => TorFormula.isQuasicoherent_homology_derivedTensor (Limits.pullback f f) _ _
      hA₀qc (hqc eNy) j
  have hsuppA := Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso
    (structureSheafRing (Limits.pullback f f).toRingedSpace)
    ((Limits.pullback.fst f f).base ⁻¹' ({x} : Set ↥X))
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Limits.pullback f f).toRingedSpace.sheaf).flip.obj K).mapIso eNx).symm
    (cohomologySupportedOn_fourierMukaiTensor_singleFunctor_pullback f f K
      (pointTestModule x 1) _ hsx.subset)
  have hsupp := Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left
    (Limits.pullback f f).sheaf ((Limits.pullback.fst f f).base ⁻¹' ({x} : Set ↥X)) _
    ((dpull (Limits.pullback.snd f f)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule y 1))) hsuppA
  -- the test object is zero
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hTvan : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor
      (Limits.pullback f f).Modules i).obj
      ((dtenLeft (Limits.pullback f f)
        ((dtenR (Limits.pullback f f) K).obj ((dpull (Limits.pullback.fst f f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule x 1))))).obj
        ((dpull (Limits.pullback.snd f f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (pointTestModule y 1))))) :=
    fun i =>
      SupportedPushforwardReflect.isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd
        f f hU hx (Set.singleton_subset_iff.2 hxU) _ hcoh hsupp (hpush i)
  -- reading it on the stalk at `w`
  by_contra hne
  have hNxnt : Nontrivial ((Stacks.ModuleSkyscraper.modulesStalkFunctor
      (Limits.pullback f f) w).obj ((Scheme.Modules.pullback
        (Limits.pullback.fst f f)).obj (pointTestModule x 1))) :=
    nontrivial_modulesStalk_of_mem_supp (by
      rw [Stacks.Modules.supp_pullback, hsx]; exact hw₁)
  have hNynt : Nontrivial ((Stacks.ModuleSkyscraper.modulesStalkFunctor
      (Limits.pullback f f) w).obj ((Scheme.Modules.pullback
        (Limits.pullback.snd f f)).obj (pointTestModule y 1))) :=
    nontrivial_modulesStalk_of_mem_supp (by
      rw [Stacks.Modules.supp_pullback, hsy]; exact hw₂)
  have h𝒦nt : Nontrivial ((Stacks.ModuleSkyscraper.modulesStalkFunctor
      (Limits.pullback f f) w).obj 𝒦) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hne (ModuleCat.isZero_iff_subsingleton.2 hs)
  have := finite_modulesStalk_of_isFiniteType ((Scheme.Modules.pullback
    (Limits.pullback.fst f f)).obj (pointTestModule x 1)) w
  have := finite_modulesStalk_of_isFiniteType ((Scheme.Modules.pullback
    (Limits.pullback.snd f f)).obj (pointTestModule y 1)) w
  have := finite_modulesStalk_of_isFiniteType 𝒦 w
  have hnt := Stacks.DerivedTensor.nontrivial_homologyZero_derivedTensor_triple
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Limits.pullback f f) w).obj
      ((Scheme.Modules.pullback (Limits.pullback.fst f f)).obj (pointTestModule x 1)))
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Limits.pullback f f) w).obj 𝒦)
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Limits.pullback f f) w).obj
      ((Scheme.Modules.pullback (Limits.pullback.snd f f)).obj (pointTestModule y 1)))
  have hstalk0 := (Functor.map_isZero
      (Stacks.ModuleSkyscraper.modulesStalkFunctor (Limits.pullback f f) w) (hTvan 0)).of_iso
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor
      (Limits.pullback f f) w).mapDerivedCategoryHomologyIso 0).app _)
  have hzero := hstalk0.of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((Limits.pullback f f).presheaf.stalk w)) 0).mapIso
    ((derivedStalkFunctor w).mapIso eT ≪≫
      derivedStalkTripleTensorIso (Limits.pullback f f) w _ 𝒦 _).symm)
  rw [ModuleCat.isZero_iff_subsingleton] at hzero
  exact (not_subsingleton _) hzero

/-- **The support of `𝒦` sits over the diagonal at a closed point**: a point of `Supp 𝒦` whose
second projection is a closed point `y` has first projection `y` as well.

The closure of such a point lies in `Supp 𝒦`, which is closed, and `X ×_k X` is a Jacobson
space, so that closure is the closure of its points that are closed in `X ×_k X`.  Each of
those has second projection in the closure of `{y}`, hence equal to `y`, and first projection a
closed point of `X` ([Stacks, Tag 01TB]), so
`Stacks.Duality.isZero_modulesStalk_of_closedPoint_ne` forces the two projections to agree
there.  The closed points of the closure therefore lie in the closed set `pr_1^{-1}{y}`, and so
does the whole closure. -/
theorem base_fst_eq_of_mem_supp_of_base_snd_eq
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : RepresentsIdentityOnPerfect f K)
    (𝒦 : (Limits.pullback f f).Modules) [𝒦.IsQuasicoherent] [𝒦.IsFiniteType]
    (eK : K ≅ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj 𝒦)
    {y : ↥X} (hy : IsClosed ({y} : Set ↥X)) {w : ↥(Limits.pullback f f)}
    (hw : w ∈ SheafOfModules.supp 𝒦)
    (hw₂ : (Limits.pullback.snd f f).base w = y) :
    (Limits.pullback.fst f f).base w = y := by
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace f
  have hJ : JacobsonSpace ↥(Limits.pullback f f : Scheme.{u}) := jacobsonSpace_pullback f f
  have hsuppclosed : IsClosed (SheafOfModules.supp 𝒦) := by
    rw [← Scheme.Modules.coe_support_annihilatorIdeal 𝒦]
    exact (Scheme.Modules.annihilatorIdeal 𝒦).support.isClosed
  -- the closed points of the closure of `{w}` all lie over `y` on both sides
  have hsub : closure ({w} : Set ↥(Limits.pullback f f)) ∩
      closedPoints ↥(Limits.pullback f f) ⊆
      (Limits.pullback.fst f f).base ⁻¹' ({y} : Set ↥X) := by
    rintro v ⟨hv, hvc⟩
    have hvsupp : v ∈ SheafOfModules.supp 𝒦 :=
      hsuppclosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hw) hv
    have hvclosed : IsClosed ({v} : Set ↥(Limits.pullback f f)) := mem_closedPoints_iff.1 hvc
    have hv₂ : (Limits.pullback.snd f f).base v = y := by
      have himg := image_closure_subset_closure_image
        (s := ({w} : Set ↥(Limits.pullback f f)))
        (Limits.pullback.snd f f).base.hom.continuous
      have hmem := himg (Set.mem_image_of_mem _ hv)
      rw [Set.image_singleton, hw₂, hy.closure_eq, Set.mem_singleton_iff] at hmem
      exact hmem
    have hv₁closed : IsClosed ({(Limits.pullback.fst f f).base v} : Set ↥X) :=
      isClosed_singleton_base_of_isClosed_singleton (Limits.pullback.fst f f) hvclosed
    by_contra hne
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hne
    exact (Scheme.Modules.notMem_supp_iff_isZero_stalk 𝒦 v).2
      (isZero_stalkFunctor_of_isZero_modulesStalk v
        (isZero_modulesStalk_of_closedPoint_ne f K hΦ 𝒦 eK hv₁closed (hv₂ ▸ hy) hne v rfl hv₂))
      hvsupp
  have hclosure : closure ({w} : Set ↥(Limits.pullback f f)) ⊆
      (Limits.pullback.fst f f).base ⁻¹' ({y} : Set ↥X) := by
    have h := closure_inter_closedPoints (X := ↥(Limits.pullback f f : Scheme.{u}))
      (Z := closure ({w} : Set ↥(Limits.pullback f f))) isClosed_closure
    rw [← h]
    exact (IsClosed.preimage (Limits.pullback.fst f f).base.hom.continuous
      hy).closure_subset_iff.2 hsub
  exact hclosure (subset_closure rfl)

end Stacks.Duality

end
