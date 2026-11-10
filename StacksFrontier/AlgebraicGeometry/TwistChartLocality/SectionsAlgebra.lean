module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY
public import StacksFrontier.AlgebraicGeometry.TwistAwayBridge.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison on twists over a standard chart, in degree-zero localizations

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain
of definition and `θ n` Tag 01MY's comparison map on the `n`-th twist. Over a standard open
`D₊(f)` of `Proj 𝒜` with `f` homogeneous, both sides of the adjoint form of `θ n` have an
algebraic description: the sections of `𝒪_{Proj 𝒜}(n)` over `D₊(f)` are the degree-zero
localization `𝒜(n)₍f₎` by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection`, and the sections of
`𝒪_{Proj ℬ}(n)` over the image of `mapHom ⁻¹ᵁ D₊(f)` are `ℬ(n)₍ψ f₎` in the same way, because
that image is exactly `D₊(ψ f)`.

This file composes the two descriptions. The result is that the comparison on sections is, in
those coordinates, the map

`𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`

obtained by applying `ψ` to a numerator and to a denominator: the homogeneous fraction
`m / f ^ k` of `𝒜(n)₍f₎` goes to `ψ m / (ψ f) ^ k`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistChartLocality.awayLocMap` and
  `Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap`: the maps `A[1/f] ⟶ B[1/ψ f]`
  induced by `ψ`, on the localized ring and on the localized module.
* `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`: **the algebraic map**
  `𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`, applying `ψ` to a numerator and a denominator.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.mem_basicOpen_map_of_mem_image`: a point of the
  image of `mapHom ⁻¹ᵁ D₊(f)` omits `ψ f`, so it lies in `D₊(ψ f)`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.image_preimage_basicOpen`: for `f` of positive
  degree the image of `mapHom ⁻¹ᵁ D₊(f)` in `Proj ℬ` is `D₊(ψ f)`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.twistSection_degreeZeroFraction_val`: **the
  algebraic description.** The comparison on sections carries the section attached to the
  homogeneous fraction `m / f ^ k` to the section attached to `ψ m / (ψ f) ^ k`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.twistPushforwardMap_degreeZeroFraction_val`: the
  same description read off the adjoint morphism, which is `Γ(D₊(f), θ n)` in adjoint form.
* `Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap_mem`: the induced map carries
  `𝒜(t)₍f₎` into `ℬ(t)₍ψ f₎`, which is what makes `twistDegreeZeroMap` exist.
* `Stacks.AlgebraicGeometry.TwistChartLocality.twistFibreMap_moduleToFiber`: the fibre
  comparison is the induced map, on the whole of `A[1/f]` and with no degree condition.
* `Stacks.AlgebraicGeometry.TwistChartLocality.twistSection_degreeZeroToSection_val`: **the
  comparison is the algebraic map**, for every element of `𝒜(n)₍f₎` and not only for a
  homogeneous fraction.

## Implementation notes

The two opens carrying the two sides are equal but not syntactically so, and the sections of
the twisting sheaves over them are therefore equal types with different spellings. The
description is consequently stated *pointwise*, as an identity between the values of the two
sections at a point of the image, which needs no transport; the identification of the opens is
recorded separately in `image_preimage_basicOpen` for the consumer that has to move a section
from one spelling to the other.

The positivity of the degree of `f` is needed only for that identification. The pointwise
description holds for every homogeneous `f`, because a point of the image of
`mapHom ⁻¹ᵁ D₊(f)` omits `ψ f` for the reason that its image point omits `f`, which is
`Stacks.AlgebraicGeometry.ProjTwistCompare.basePoint_asHomogeneousIdeal` and no more.

Every step is taken on elements rather than on morphisms. The index category of a twisting
sheaf is `Opens ↑(ProjectiveSpectrum.top 𝒜)` while that of `AlgebraicGeometry.Scheme.Modules`
is `Opens ↑(AlgebraicGeometry.Proj 𝒜)`, so a `rw` with
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection_val` fails its motive check even with
`AlgebraicGeometry.Proj` made `implicit_reducible`; the equation is definitional and is used
through `Eq.trans` instead.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.TwistAwayBridge

namespace Stacks.AlgebraicGeometry.TwistChartLocality

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The chart on the target -/

/-- **A point of the image of `mapHom ⁻¹ᵁ D₊(f)` omits `ψ f`.** The homogeneous ideal at the
image point is the `ψ`-preimage of the one at the point, so omitting `f` upstairs is omitting
`ψ f` downstairs. No positivity of the degree of `f` is used. -/
public theorem mem_basicOpen_map_of_mem_image (ψ : 𝒜 →+*ᵍ ℬ) {f : A}
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :
    (z.1 : AlgebraicGeometry.Proj ℬ) ∈ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) := by
  have hb : f ∉ (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal := liftPt_mem 𝒜 ℬ ψ z
  rw [basePoint_asHomogeneousIdeal] at hb
  exact hb

/-- **The image of `mapHom ⁻¹ᵁ D₊(f)` is the standard open `D₊(ψ f)`**, for `f` homogeneous of
positive degree.

The inverse image of `D₊(f)` along `mapHom` is the part of `D₊(ψ f)` inside the domain of
definition, which is `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`; and
`D₊(ψ f)` lies in the domain of definition, because positivity of the degree of `f` makes
`D₊(ψ f)` one of the standard opens whose union that domain is. So taking the image undoes
the inverse image. -/
@[ega "II 2.8.1"]
public theorem image_preimage_basicOpen (ψ : 𝒜 →+*ᵍ ℬ) {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (hd : 0 < d) :
    (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) =
      AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) := by
  rw [mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd]
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf hx⟩, hx, rfl⟩

/-! ### The comparison on sections in degree-zero coordinates -/

/-- **The comparison on sections of the `n`-th twist, over a standard chart, is `ψ` on a
numerator and a denominator.**

The section of `𝒪_{Proj 𝒜}(n)` over `D₊(f)` attached to the degree-zero homogeneous fraction
`m / f ^ k` of `𝒜(n)₍f₎` is carried by Tag 01MY's comparison to the section of
`𝒪_{Proj ℬ}(n)` over `D₊(ψ f)` attached to `ψ m / (ψ f) ^ k` of `ℬ(n)₍ψ f₎`. This is the
degree-zero-localization-level description of `Γ(D₊(f), θ n)` in its adjoint form.

The identity is stated at a point `z` of the image of `mapHom ⁻¹ᵁ D₊(f)`, which is `D₊(ψ f)` by
`image_preimage_basicOpen`; the right-hand side reads the value of the target section at `z`
through `mem_basicOpen_map_of_mem_image`. -/
public theorem twistSection_degreeZeroFraction_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (k : ℕ) (m : A) (hm : m ∈ twistGrading (S := A) 𝒜 n (k • (d : ℤ)))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :
    (twistSection 𝒜 ℬ ψ n (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 n) f
          (degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 n) hf k m hm))).1 z =
      (degreeZeroToSection ℬ (twistGrading (S := B) ℬ n) (ψ f)
        (degreeZeroFraction ℬ (twistGrading (S := B) ℬ n) (mem_of_mem 𝒜 ℬ ψ hf) k (ψ m)
          (map_mem_twistGrading 𝒜 ℬ ψ n _ hm))).1
        ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩ := by
  have hzc : ψ f ∈
      (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal.primeCompl :=
    mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z
  refine Eq.trans (twistSection_val 𝒜 ℬ ψ n _ _ z) ?_
  refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (degreeZeroToSection_fraction 𝒜 (twistGrading (S := A) 𝒜 n) hf k m hm _)) ?_
  refine Eq.trans (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) m (f ^ k) _
    (by rw [map_pow]; exact Submonoid.pow_mem _ hzc k)) ?_
  refine Eq.trans ?_
    (degreeZeroToSection_fraction ℬ (twistGrading (S := B) ℬ n) (mem_of_mem 𝒜 ℬ ψ hf) k (ψ m)
      (map_mem_twistGrading 𝒜 ℬ ψ n _ hm)
      ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩).symm
  exact congrArg (LocalizedModule.mk (ψ m)) (Subtype.ext (map_pow ψ f k))

/-- **The same description read off the adjoint morphism**, which is what
`Γ(D₊(f), θ n)` is in its adjoint form: the sections of
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap` over `D₊(f)` send the
homogeneous fraction `m / f ^ k` to `ψ m / (ψ f) ^ k`.

The adjoint morphism acts on sections as
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection` by construction, so this is the
previous result in the spelling a consumer of the morphism meets. -/
public theorem twistPushforwardMap_degreeZeroFraction_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (k : ℕ) (m : A) (hm : m ∈ twistGrading (S := A) 𝒜 n (k • (d : ℤ)))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :
    (((twistPushforwardMap 𝒜 ℬ ψ n).val.app
            (Opposite.op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))).hom'
          (degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 n) f
            (degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 n) hf k m hm))).1 z =
      (degreeZeroToSection ℬ (twistGrading (S := B) ℬ n) (ψ f)
        (degreeZeroFraction ℬ (twistGrading (S := B) ℬ n) (mem_of_mem 𝒜 ℬ ψ hf) k (ψ m)
          (map_mem_twistGrading 𝒜 ℬ ψ n _ hm))).1
        ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩ :=
  twistSection_degreeZeroFraction_val 𝒜 ℬ ψ n hf k m hm z

/-! ### The algebraic map `𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎` -/

/-- **The map on ordinary localizations induced by `ψ`**, `A[1/f] ⟶ B[1/ψ f]`.

This is `Localization.awayMap` of the underlying ring homomorphism, with its type ascribed so
that the denominator reads `ψ f` in the graded-homomorphism spelling rather than in the
`RingHom` one. The two spellings are definitionally equal but not syntactically so, and the
module instances downstream are found by syntactic search, so pinning the type here is what
makes every later statement elaborate. -/
public def awayLocMap (ψ : 𝒜 →+*ᵍ ℬ) (f : A) :
    Localization.Away f →+* Localization.Away (ψ f) :=
  Localization.awayMap (ψ : A →+* B) f

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The map on ordinary localizations applies `ψ` to a numerator and a denominator. -/
public theorem awayLocMap_mk (ψ : 𝒜 →+*ᵍ ℬ) (f x : A) (s : Submonoid.powers f)
    (hs : ψ (s : A) ∈ Submonoid.powers (ψ f)) :
    awayLocMap 𝒜 ℬ ψ f (Localization.mk x s) =
      Localization.mk (ψ x) ⟨ψ (s : A), hs⟩ := by
  change Localization.awayMap (ψ : A →+* B) f (Localization.mk x s) = _
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_mk']
  rfl

/-- **The degree-zero localizations map compatibly with the ordinary ones.** The ring
homomorphism `𝒜₍f₎ ⟶ ℬ₍ψ f₎` of `HomogeneousLocalization.Away.map` becomes `awayLocMap` after
passing to the ordinary localization by `HomogeneousLocalization.val`. This is the square that
makes the module map below semilinear. -/
public theorem val_awayLocMap (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (r : Away 𝒜 f) :
    (HomogeneousLocalization.Away.map ψ f r).val = awayLocMap 𝒜 ℬ ψ f r.val := by
  obtain ⟨r, rfl⟩ := HomogeneousLocalization.mk_surjective r
  change _ = Localization.awayMap (ψ : A →+* B) f _
  rw [HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', Localization.mk_eq_mk', Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_mk']
  rfl

/-- **The map on localized modules induced by `ψ`**, `A[1/f] ⟶ B[1/ψ f]` read with the ring as
a module over itself. It is `awayLocMap` conjugated by
`Stacks.AlgebraicGeometry.TwistAwayBridge.localizedAwayEquiv`, which identifies the localized
module with the localized ring. -/
public def awayModuleMap (ψ : 𝒜 →+*ᵍ ℬ) (f : A) :
    LocalizedModule.Away f A →+ LocalizedModule.Away (ψ f) B :=
  (localizedAwayEquiv (ψ f)).symm.toAddEquiv.toAddMonoidHom.comp
    ((awayLocMap 𝒜 ℬ ψ f).toAddMonoidHom.comp
      (localizedAwayEquiv f).toAddEquiv.toAddMonoidHom)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The comparison of a localized module with the localized ring carries a fraction back to
the same fraction. -/
public theorem localizedAwayEquiv_symm_mk (f x : A) (s : Submonoid.powers f) :
    (localizedAwayEquiv f).symm (Localization.mk x s) = LocalizedModule.mk x s :=
  (localizedAwayEquiv f).injective
    (by rw [LinearEquiv.apply_symm_apply, localizedAwayEquiv_mk])

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The map on localized modules applies `ψ` to a numerator and a denominator. -/
public theorem awayModuleMap_mk (ψ : 𝒜 →+*ᵍ ℬ) (f x : A) (s : Submonoid.powers f)
    (hs : ψ (s : A) ∈ Submonoid.powers (ψ f)) :
    awayModuleMap 𝒜 ℬ ψ f (LocalizedModule.mk x s) =
      LocalizedModule.mk (ψ x) ⟨ψ (s : A), hs⟩ := by
  change (localizedAwayEquiv (ψ f)).symm (awayLocMap 𝒜 ℬ ψ f
    (localizedAwayEquiv f (LocalizedModule.mk x s))) = _
  rw [localizedAwayEquiv_mk, awayLocMap_mk 𝒜 ℬ ψ f x s hs, localizedAwayEquiv_symm_mk]

/-- **The map on localized modules is semilinear over `HomogeneousLocalization.Away.map`.** The
scalar action of `𝒜₍f₎` on `A[1/f]` is through `HomogeneousLocalization.val`, so this is
`val_awayLocMap` together with linearity of the two comparisons over the localized rings. -/
public theorem awayModuleMap_smul_val (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (r : Away 𝒜 f)
    (z : LocalizedModule.Away f A) :
    awayModuleMap 𝒜 ℬ ψ f (r.val • z) =
      (HomogeneousLocalization.Away.map ψ f r).val • awayModuleMap 𝒜 ℬ ψ f z := by
  change (localizedAwayEquiv (ψ f)).symm (awayLocMap 𝒜 ℬ ψ f
    (localizedAwayEquiv f (r.val • z))) = _
  rw [map_smul, smul_eq_mul, map_mul, ← val_awayLocMap, ← smul_eq_mul, map_smul]
  rfl

/-- **The map on localized modules carries `𝒜(t)₍f₎` into `ℬ(t)₍ψ f₎`.** The degree-zero part
is spanned by the fractions `x / f ^ k` with `x` homogeneous of degree `k · deg f + t`, and
`ψ` carries such a fraction to `ψ x / (ψ f) ^ k` with `ψ x` homogeneous of the same degree; the
span is respected because the map is semilinear by `awayModuleMap_smul_val`. -/
public theorem awayModuleMap_mem (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (t : ℤ)
    {z : LocalizedModule.Away (R := A) f A}
    (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f) :
    awayModuleMap 𝒜 ℬ ψ f z ∈
      GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ t) (ψ f) := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨e, k, hfe, x, hx, rfl⟩ := hw
      rw [awayModuleMap_mk 𝒜 ℬ ψ f x _ (by rw [map_pow]; exact ⟨k, rfl⟩)]
      refine Submodule.subset_span ⟨e, k, mem_of_mem 𝒜 ℬ ψ hfe, ψ x,
        map_mem_twistGrading 𝒜 ℬ ψ t _ hx, ?_⟩
      exact congrArg (LocalizedModule.mk (ψ x)) (Subtype.ext (map_pow ψ f k))
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul r a _ ha =>
      change awayModuleMap 𝒜 ℬ ψ f (r.val • a) ∈ _
      rw [awayModuleMap_smul_val]
      exact Submodule.smul_mem _ (HomogeneousLocalization.Away.map ψ f r) ha

/-- **The algebraic map `𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`**: applying `ψ` to a numerator and a
denominator, as an additive map between the degree-zero localizations of the twists. It is
semilinear over `HomogeneousLocalization.Away.map ψ f` by `twistDegreeZeroMap_smul`. -/
public def twistDegreeZeroMap (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (t : ℤ) :
    GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f →+
      GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ t) (ψ f) where
  toFun z := ⟨awayModuleMap 𝒜 ℬ ψ f z.1, awayModuleMap_mem 𝒜 ℬ ψ f t z.2⟩
  map_zero' := Subtype.ext (map_zero (awayModuleMap 𝒜 ℬ ψ f))
  map_add' a b := Subtype.ext (map_add (awayModuleMap 𝒜 ℬ ψ f) a.1 b.1)

/-- The algebraic map is semilinear over the ring homomorphism `𝒜₍f₎ ⟶ ℬ₍ψ f₎`. -/
public theorem twistDegreeZeroMap_smul (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (t : ℤ) (r : Away 𝒜 f)
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f) :
    twistDegreeZeroMap 𝒜 ℬ ψ f t (r • z) =
      HomogeneousLocalization.Away.map ψ f r • twistDegreeZeroMap 𝒜 ℬ ψ f t z :=
  Subtype.ext (awayModuleMap_smul_val 𝒜 ℬ ψ f r z.1)

/-- **The algebraic map on a homogeneous fraction.** `m / f ^ k` goes to `ψ m / (ψ f) ^ k`. -/
public theorem twistDegreeZeroMap_degreeZeroFraction (ψ : 𝒜 →+*ᵍ ℬ) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (t : ℤ) (k : ℕ) (m : A)
    (hm : m ∈ twistGrading (S := A) 𝒜 t (k • (d : ℤ))) :
    twistDegreeZeroMap 𝒜 ℬ ψ f t
        (degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 t) hf k m hm) =
      degreeZeroFraction ℬ (twistGrading (S := B) ℬ t) (mem_of_mem 𝒜 ℬ ψ hf) k (ψ m)
        (map_mem_twistGrading 𝒜 ℬ ψ t _ hm) := by
  refine Subtype.ext ?_
  change awayModuleMap 𝒜 ℬ ψ f (LocalizedModule.mk m ⟨f ^ k, ⟨k, rfl⟩⟩) = _
  rw [awayModuleMap_mk 𝒜 ℬ ψ f m _ (by rw [map_pow]; exact ⟨k, rfl⟩)]
  exact congrArg (LocalizedModule.mk (ψ m)) (Subtype.ext (map_pow ψ f k))

/-! ### The comparison is the algebraic map -/

/-- **The fibre comparison is the algebraic map, on the whole localized module.** Pushing an
element of `A[1/f]` into the fibre at the image point and comparing is the same as applying
`ψ` to a numerator and a denominator and then pushing into the fibre at the point.

Nothing here is restricted to the degree-zero part: both sides are additive in the element and
`LocalizedModule` is generated by its fractions, so the identity is proved by
`LocalizedModule.induction_on` and holds for every element. That is what makes the sections
identity below hold for every element of `𝒜(n)₍f₎` rather than only for a fraction. -/
public theorem twistFibreMap_moduleToFiber (ψ : 𝒜 →+*ᵍ ℬ) {f : A}
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)))
    (v : LocalizedModule.Away (R := A) f A) :
    twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (moduleToFiber (M := A) 𝒜 f
          ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩ v) =
      moduleToFiber (M := B) ℬ (ψ f) ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩
        (awayModuleMap 𝒜 ℬ ψ f v) := by
  have hzc : ψ f ∈
      (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal.primeCompl :=
    mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z
  induction v using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨k, hk⟩ := s.2
    have hs' : ψ (s : A) ∈ Submonoid.powers (ψ f) := ⟨k, by rw [← hk, map_pow]⟩
    have hψs : ψ (s : A) ∈
        (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal.primeCompl := by
      rw [← hk, map_pow]
      exact Submonoid.pow_mem _ hzc k
    refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
      (moduleToFiber_mk 𝒜 f ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩ m s)) ?_
    refine Eq.trans (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) m (s : A) _ hψs) ?_
    refine Eq.trans ?_ (congrArg (moduleToFiber (M := B) ℬ (ψ f)
      ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩)
      (awayModuleMap_mk 𝒜 ℬ ψ f m s hs')).symm
    exact (moduleToFiber_mk ℬ (ψ f) ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩
      (ψ m) ⟨ψ (s : A), hs'⟩).symm

/-- **Tag 01MY's comparison on sections over a standard chart is the algebraic map
`𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`.**

For every element of the degree-zero localization `𝒜(n)₍f₎` — not merely for a homogeneous
fraction — the comparison carries the section it determines over `D₊(f)` to the section
determined by its image under `twistDegreeZeroMap` over `D₊(ψ f)`. Composed with
`image_preimage_basicOpen`, which identifies the open carrying the target section, this is the
degree-zero-localization-level description of `Γ(D₊(f), θ n)`. -/
public theorem twistSection_degreeZeroToSection_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {f : A}
    (v : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :
    (twistSection 𝒜 ℬ ψ n (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 n) f v)).1 z =
      (degreeZeroToSection ℬ (twistGrading (S := B) ℬ n) (ψ f)
        (twistDegreeZeroMap 𝒜 ℬ ψ f n v)).1
        ⟨z.1, mem_basicOpen_map_of_mem_image 𝒜 ℬ ψ z⟩ :=
  twistFibreMap_moduleToFiber 𝒜 ℬ ψ z v.1

end Stacks.AlgebraicGeometry.TwistChartLocality

end
