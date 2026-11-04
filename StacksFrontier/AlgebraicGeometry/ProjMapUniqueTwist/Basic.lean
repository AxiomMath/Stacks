module

public import StacksFrontier.AlgebraicGeometry.ProjMapUniqueTwist.Transport

/-!
# Tag 01MY: uniqueness of the graded-algebra map on twists

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain
of definition and `r_ψ : U(ψ) ⟶ Proj 𝒜` the induced morphism. Tag 01MY asserts that the triple
`(U(ψ), r_ψ, θ)` is *characterized* by its two conditions. This file proves the half about `θ`:
once the morphism of schemes is fixed, condition (1) together with the graded-algebra laws
determines the comparison map on **every** integer twist.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.val_eq_twistFibreMap`: **the content.** A family
  satisfying the pointwise multiplication law and condition (1) has, on every section over every
  open and at every point, the value `ψ a / ψ s` of the fibre comparison.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.eq_twistMap`: the family is `θ`.
* `Stacks.AlgebraicGeometry.ProjMapUniqueTwist.projMapData_twistMap_unique`: **Tag 01MY,
  uniqueness of the graded-algebra map**, written on the canonical bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, which is the spelling of the tagged
  statement.

## The route, and why the source's route is not taken

The source argues on the standard open `D₊(f)`: there `𝒪_X(n)|_{D₊(f)}` is the `A_{(f)}`-module
`(A_f)_n`, so `θ` restricted to `D₊(ψ f)` is a map of `ℤ`-graded `B_{(ψ f)}`-algebras
`A_f ⊗_{A_{(f)}} B_{(ψ f)} ⟶ B_{\psi f}`, and condition (1) plus invertibility of `f` pins it
down as `a/f^m ⊗ b/ψ(f)^e ↦ ψ(a) b / ψ(f)^{m + e}`.

**That route needs a presentation of `Γ(D₊(f), 𝒪(n))` for arbitrary `n`, and this proof does not
use one.** The argument here is generation-and-cancellation at the level of *one local fraction*,
which is exactly the shape in which the sections of a twist are given: a section of `𝒪(n)` over
`V` is a dependent family of elements of the fibres which is, near each point, a single fraction
`β / c` with `c` homogeneous of some degree `K` and `β` homogeneous of degree `K + n`. Multiplying
by the global section of `𝒪(K)` attached to `c` clears the denominator, and the resulting section
has all its values equal to `β / 1`, so it is the restriction of the global section attached to
`β` and condition (1) computes its image. The multiplication law then exhibits that image as
`ψ(c)/1` times the image of the original section, and `ψ(c)/1` is a unit of the local ring of
`Proj ℬ` at the point — because `c ∉ x` forces `ψ c ∉ y` for any `y` over `x`. Cancelling it
gives `ψ(β)/ψ(c)`, which is the fibre comparison of `β / c`.

So the only arithmetic input is cancellation in one local ring, and that is
`Stacks.AlgebraicGeometry.TwistRigidity.eq_of_mkOne_mul_eq`. No trivialization of a twist is
used, and no hypothesis on the degree of `f` or on generation in degree one is needed — which
matters, because the twists of `Proj 𝒜` are *not* locally free on `D₊(f)` unless the degree is a
multiple of `deg f`, and `Proj 𝒜`'s twisting algebra is only known to be invertible under a
degree-one generation hypothesis that Tag 01MY does not grant.

**No sheaf-gluing step is needed either**, for the same reason as in
`StacksFrontier/AlgebraicGeometry/TwistRigidity/Basic.lean`: a section of a twist *is* a
dependent function on points subject to a local condition, and restriction of sections is
restriction of functions, so an equality of two sections over `V` is checked at each point of `V`
separately and each point is handled on its own smaller open.

## What the hypotheses are used for

The unit law is **not used**: the multiplication law together with condition (1) already forces
the family, exactly as in the absolute rigidity statement. It is nevertheless carried in the
statement, because the tagged statement states it and dropping a hypothesis from a `characterized by`
assertion would change what is being claimed.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.TwistTensor Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjMapCardUnit
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjMapUniqueTwist

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {ψ : 𝒜 →+*ᵍ ℬ}

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### The two pointwise hypotheses -/

/-- The pointwise form of Tag 01MY's multiplication law for a family of comparison maps written
in adjoint form: the value on a canonical product of local sections is the product of the two
values. -/
public def IsMultiplicativeOnValues
    (Dp : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))) :
    Prop :=
  ∀ (i j : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj (op V)) (b : (twistingSheaf 𝒜 j).val.obj (op V))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V))),
    (Hom.app (Dp (i + j)).val (op V) (absoluteTwistProduct 𝒜 i j V a b)).1 z =
      (Hom.app (Dp i).val (op V) a).1 z * (Hom.app (Dp j).val (op V) b).1 z

/-- The pointwise form of Tag 01MY's condition (1) for a family of comparison maps written in
adjoint form: the global section attached to a homogeneous `c` of degree `k` goes to the family
whose value everywhere is `ψ c / 1`. -/
public def MapsDegreeSections
    (Dp : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))) :
    Prop :=
  ∀ (k : ℕ) (c : 𝒜 k) (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))),
    (Hom.app (Dp (k : ℤ)).val (op ⊤) (degreeSection 𝒜 k c)).1 z =
      LocalizedModule.mk ((ψ c : B)) 1

variable {Dp : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
  ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))}

/-! ### From condition (1) to an arbitrary constant fraction -/

/-- The value of a restricted section at a point of the smaller image open is its value at the
same point in the larger one. -/
private theorem val_map_restrict {n : ℤ} {V V' : (AlgebraicGeometry.Proj 𝒜).Opens} (i : V' ⟶ V)
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) (p : AlgebraicGeometry.Proj ℬ)
    (hp' : p ∈ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V'))
    (hp : p ∈ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V)) :
    (Hom.app (Dp n).val (op V') ((twistingSheaf 𝒜 n).val.map i.op t)).1 ⟨p, hp'⟩ =
      (Hom.app (Dp n).val (op V) t).1 ⟨p, hp⟩ :=
  Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr ℬ
    (PresheafOfModules.naturality_apply (Dp n).val i.op t) ⟨p, hp'⟩

/-- A section of `𝒪(m)` whose value at every point is `a / 1` for one homogeneous `a` of degree
`N` with `N = m` is the restriction of the global section attached to `a`, so condition (1)
computes its image: the value is `ψ a / 1` at every point.

This is where the natural-number degree of `a` and the integer index of the twist are identified,
and the identification is made by substituting into the free integer index `m`. -/
public theorem val_of_values_mkOne (hfix : MapsDegreeSections Dp)
    {m : ℤ} {N : ℕ} (hm : (N : ℤ) = m) {a : A} (ha : a ∈ 𝒜 N)
    (V : (AlgebraicGeometry.Proj 𝒜).Opens) (s : (twistingSheaf 𝒜 m).val.obj (op V))
    (hs : ∀ y : V, s.1 y = LocalizedModule.mk a 1)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V))) :
    (Hom.app (Dp m).val (op V) s).1 z = LocalizedModule.mk ((ψ a : B)) 1 := by
  subst hm
  have hres : (twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE (le_top : V ≤ ⊤)).op
      (degreeSection 𝒜 N ⟨a, ha⟩) = s :=
    Subtype.ext (funext fun y =>
      (degreeSection_apply 𝒜 N ⟨a, ha⟩ ⟨y.1, trivial⟩).trans (hs y).symm)
  have hz : (z.1 : AlgebraicGeometry.Proj ℬ) ∈ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)) :=
    Scheme.Hom.image_mono (mapDomain 𝒜 ℬ ψ).ι
      (fun p _ => trivial : mapHom 𝒜 ℬ ψ ⁻¹ᵁ V ≤
        mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)) z.2
  have hstep := val_map_restrict (Dp := Dp) (homOfLE (le_top : V ≤ ⊤))
    (degreeSection 𝒜 N ⟨a, ha⟩) z.1 z.2 hz
  exact (Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr ℬ
    (congrArg (Hom.app (Dp (N : ℤ)).val (op V)) hres.symm) z).trans
      (hstep.trans (hfix N ⟨a, ha⟩ ⟨z.1, hz⟩))

/-! ### One local fraction -/

/-- **The generation-and-cancellation step, nonnegative case.** A section of `𝒪(n)` given on the
whole of its open by a single homogeneous fraction `β / c` whose numerator has nonnegative degree
has value `ψ β / ψ c`: multiplying by the homogeneous section of `c` clears the denominator, the
result's values are all `β / 1` so condition (1) computes them, and the unit `ψ c / 1` cancels. -/
public theorem val_of_isFraction_nonneg (hmul : IsMultiplicativeOnValues Dp)
    (hfix : MapsDegreeSections Dp) (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) {K N : ℕ} {β c : A}
    (hN : (N : ℤ) = (K : ℤ) + n) (hβ : β ∈ 𝒜 N) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V)))
    (hψc : ψ c ∉ z.1.asHomogeneousIdeal.toIdeal) :
    (Hom.app (Dp n).val (op V) t).1 z = LocalizedModule.mk (ψ β) ⟨ψ c, hψc⟩ := by
  refine Stacks.AlgebraicGeometry.TwistRigidity.eq_of_mkOne_mul_eq _ hψc ?_
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.TwistRigidity.mkOne_mul_mk _ (ψ β) hψc).symm
  refine Eq.trans (congrArg (fun r => r * (Hom.app (Dp n).val (op V) t).1 z)
    (val_of_values_mkOne hfix (rfl : ((K : ℕ) : ℤ) = (K : ℤ)) hc V
      (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn 𝒜 K hc V)
      (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_apply 𝒜 K hc V) z).symm) ?_
  refine Eq.trans (hmul (K : ℤ) n V
    (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn 𝒜 K hc V) t z).symm ?_
  exact val_of_values_mkOne hfix hN hβ V
    (absoluteTwistProduct 𝒜 (K : ℤ) n V
      (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn 𝒜 K hc V) t)
    (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_mul_apply 𝒜 K hc n V t hnv hval) z

/-- **The generation-and-cancellation step.** A section of `𝒪(n)` given on the whole of its open
by a single homogeneous fraction has, at every point of the image open, the value of the fibre
comparison. If the numerator's degree `K + n` is negative the numerator lies in the zero
submodule and the section vanishes; in the remaining case this is
`val_of_isFraction_nonneg`. -/
public theorem val_of_isFraction (hmul : IsMultiplicativeOnValues Dp)
    (hfix : MapsDegreeSections Dp) (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (t : (twistingSheaf 𝒜 n).val.obj (op V)) {K : ℕ} {β c : A}
    (hβ : β ∈ twistGrading (S := A) 𝒜 n (K : ℤ)) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V))) :
    (Hom.app (Dp n).val (op V) t).1 z =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (t.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) := by
  have hx : c ∉ (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal :=
    hnv ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩
  have hψc : ψ c ∉ (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal :=
    notMem_of_notMem 𝒜 ℬ ψ hc (liftPt 𝒜 ℬ ψ z) hx
  refine Eq.trans ?_ (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (hval ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)).symm
  refine Eq.trans ?_ (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) β c hx hψc).symm
  rcases le_or_gt 0 ((K : ℤ) + n) with hKn | hKn
  · have hβ' : β ∈ 𝒜 ((K : ℤ) + n).toNat := by
      simpa [integerGrading, hKn] using (hβ : β ∈ integerGrading (S := A) 𝒜 ((K : ℤ) + n))
    exact val_of_isFraction_nonneg hmul hfix n V t (Int.toNat_of_nonneg hKn) hβ' hc hnv hval z hψc
  · have hβ0 : β = 0 := by
      have hb : β ∈ (⊥ : Submodule ℤ A) := by
        simpa [integerGrading, not_le.mpr hKn] using
          (hβ : β ∈ integerGrading (S := A) 𝒜 ((K : ℤ) + n))
      simpa using hb
    have ht0 : t = 0 :=
      Subtype.ext (funext fun y => (by rw [hval y, hβ0]; simp : t.1 y = 0))
    have hmapzero : Hom.app (Dp n).val (op V) t = 0 := by
      rw [ht0]; exact map_zero _
    refine Eq.trans (Stacks.AlgebraicGeometry.TwistRigidity.twist_val_congr ℬ hmapzero z) ?_
    rw [hβ0, map_zero]
    exact (LocalizedModule.zero_mk _).symm

/-! ### The value of an arbitrary section -/

/-- **The content of Tag 01MY's uniqueness clause.** A family satisfying the pointwise
multiplication law and condition (1) has, on every section over every open and at every point of
the image open, exactly the value of the fibre comparison `a / s ↦ ψ a / ψ s`. -/
public theorem val_eq_twistFibreMap (hmul : IsMultiplicativeOnValues Dp)
    (hfix : MapsDegreeSections Dp) (n : ℤ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (t : (twistingSheaf 𝒜 n).val.obj (op V))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V))) :
    (Hom.app (Dp n).val (op V) t).1 z =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (t.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) := by
  obtain ⟨V', hxV', i, K, β, c, hβ, hc, hnv, heq⟩ :=
    t.2 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩
  have hzV' : (z.1 : AlgebraicGeometry.Proj ℬ) ∈
      (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V') :=
    mem_image_of_mem 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) hxV'
  exact (val_map_restrict (Dp := Dp) i t z.1 hzV' z.2).symm.trans (val_of_isFraction hmul hfix n V'
    ((twistingSheaf 𝒜 n).val.map i.op t) hβ hc hnv heq ⟨z.1, hzV'⟩)

/-! ### Uniqueness -/

/-- The adjoint transpose of such a family is the adjoint form of `θ`: both have the same value
at every point of every section over every open. -/
public theorem eq_twistPushforwardMap (hmul : IsMultiplicativeOnValues Dp)
    (hfix : MapsDegreeSections Dp) (n : ℤ) : Dp n = twistPushforwardMap 𝒜 ℬ ψ n :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
    (LinearMap.ext fun t => Subtype.ext (funext fun z =>
      (val_eq_twistFibreMap hmul hfix n V.unop t z).trans
        (twistPushforwardMap_app_val 𝒜 ℬ ψ n V t z).symm)))

/-- **Uniqueness of the comparison maps on twists**, for a family satisfying the two pointwise
hypotheses. -/
public theorem eq_twistMap (tw : TwistFamily 𝒜 ℬ ψ)
    (hmul : IsMultiplicativeOnValues (adjointFamily 𝒜 ℬ ψ tw))
    (hfix : MapsDegreeSections (adjointFamily 𝒜 ℬ ψ tw)) (n : ℤ) :
    tw n = twistMap 𝒜 ℬ ψ n :=
  eq_twistMap_of_adjointFamily_eq tw n (eq_twistPushforwardMap hmul hfix n)

/-- **Tag 01MY, uniqueness of the graded-algebra map.** A bundle of the canonical morphism with
maps on all twists which satisfies condition (1) at `⊤`, the multiplication law in all integer
degrees and the unit law is the canonical bundle.

Together with `Stacks.AlgebraicGeometry.ProjMapData.eq_mapHom`, this is uniqueness of the
canonical triple of Tag 01MY. -/
@[stacks 01MY "uniqueness of the graded-algebra map"]
public theorem projMapData_twistMap_unique (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (D : ProjMapData 𝒜 ℬ ψ)
    (hh : D.hom = (projMapData 𝒜 ℬ ψ).hom)
    (hdegree : ∀ (n : ℕ) (a : 𝒜 n),
      (D.twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction D.hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤)
            (degreeSection 𝒜 n a)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
        (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩))
    (hmul : ∀ n m : ℤ,
      pullbackTwistMultiplication 𝒜 D.hom n m ≫ D.twistMap (n + m) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((mapDomain 𝒜 ℬ
        ψ).toScheme.toRingedSpace)).presheaf, (((mapDomain 𝒜 ℬ
        ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((D.twistMap n), (D.twistMap m)) : (_, _) ⟶ (_, _))) ≫
        pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m)
    (hunit : pullbackTwistUnit 𝒜 D.hom ≫ D.twistMap 0 =
      pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι) :
    D = projMapData 𝒜 ℬ ψ := by
  obtain ⟨hom, tw⟩ := D
  have hh' : hom = mapHom 𝒜 ℬ ψ := hh
  subst hh'
  exact congrArg (fun f => (⟨mapHom 𝒜 ℬ ψ, f⟩ : ProjMapData 𝒜 ℬ ψ)) (funext fun n =>
    eq_twistMap tw (adjointFamily_mul_val tw hmul) (adjointFamily_degreeSection_val tw hdegree) n)

section Faithfulness

/-- **Faithfulness.** The uniqueness of the twist maps in Tag 01MY, in the text and binder order of
the tagged statement, written in this library's vocabulary: the domain of the map is
`Stacks.AlgebraicGeometry.ProjShared.mapDomain`, the twisting sheaves of Tag 01MN are
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`, the degree sections of Tag 01MP are
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`, the data of Tag 01MY are
`Stacks.AlgebraicGeometry.ProjTwistCompare.ProjMapData` and
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, and the multiplication and unit of the
pulled-back twists are `Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication` and
`Stacks.AlgebraicGeometry.ProjMapCardUnit.pullbackTwistUnit`. No hypothesis is added, dropped or
reordered, and no quantifier is changed. -/
example {A B : Type u} {σ : Type w} {τ : Type w'}
    [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ)
    (D : ProjMapData 𝒜 ℬ ψ)
    (hh : D.hom = (projMapData 𝒜 ℬ ψ).hom)
    (hdegree : ∀ (n : ℕ) (a : 𝒜 n),
      (D.twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction D.hom).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤)
            (degreeSection 𝒜 n a)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
        (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩))
    (hmul : ∀ n m : ℤ,
      pullbackTwistMultiplication 𝒜 D.hom n m ≫ D.twistMap (n + m) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((mapDomain 𝒜 ℬ
        ψ).toScheme.toRingedSpace)).presheaf, (((mapDomain 𝒜 ℬ
        ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((D.twistMap n), (D.twistMap m)) : (_, _) ⟶ (_, _))) ≫
        pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m)
    (hunit : pullbackTwistUnit 𝒜 D.hom ≫ D.twistMap 0 =
      pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι) :
    D = projMapData 𝒜 ℬ ψ :=
  projMapData_twistMap_unique 𝒜 ℬ ψ D hh hdegree hmul hunit

end Faithfulness

end Stacks.AlgebraicGeometry.ProjMapUniqueTwist

end
