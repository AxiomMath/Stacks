module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelSupportDiagonal
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.InvertiblePushforwardSection
import StacksCore.Tactic.StacksAttribute

/-!
# The scheme-theoretic support of the kernel is finite over `X`

Let `k` be a field, let `X` be a smooth proper `k`-scheme and let `K` be a perfect object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces the identity on `D_perf(𝒪_X)`.  Steps 1 and
2 of the proof of [Stacks, Tag 0G0E] present `K` as a single coherent module `𝒦` in degree zero,
and this file proves the remaining geometric input of the source's third step:

`(annihilatorIdeal 𝒦).subschemeι ≫ pr₂` is a finite morphism,

which is the instance hypothesis of [Stacks, Tag 0FZP].

## Main results

* `AlgebraicGeometry.finite_preimage_singleton_inter_of_isClosed` — for a closed point `y` of a
  scheme `X` locally of finite type over a field, `pr_1^{-1}{y} ∩ pr_2^{-1}{y}` is a finite
  subset of `X ×_k X`.
* `Stacks.Duality.finite_preimage_singleton_subschemeι_comp_snd` — the fibre of
  `Supp 𝒦 ⟶ X` over a closed point is finite.
* `Stacks.Duality.isFinite_subschemeι_comp_snd` — **the instance [Stacks, Tag 0FZP] needs**:
  that morphism is finite.

## Implementation notes

*The fibre over a closed point.*  For a closed point `y` the residue field `κ(y)` is finite over
`k`: `Spec κ(y) ⟶ X` is a closed immersion
(`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`), so `Spec κ(y) ⟶ Spec k` is
locally of finite type, and on a one-point reduced source over a Jacobson base that is the same
as being finite (`AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`).  Its
base change along `f` is then finite, and `pr_1^{-1}{y} ∩ pr_2^{-1}{y}` is the image under
`pr_1`'s fibre inclusion of a fibre of that base change: the fibre of `pr_1` over `y` is
`Spec κ(y) ×_k X` with `pr_2` corresponding to the projection, which is
`CategoryTheory.Limits.pullbackRightPullbackFstIso` after a symmetry.

*From the closed points to all of `X`.*  The fibres over the points that are **not** closed are
not finite in general — over the generic point of `𝔸^1` the set `pr_1^{-1}{y} ∩ pr_2^{-1}{y}` is
the spectrum of `κ(y) ⊗_k κ(y)`, which is one-dimensional — so `LocallyQuasiFinite` cannot be
obtained from `AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton`, which asks for
every fibre.  What is used instead is [Stacks, Tag 02UP],
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`: a finite fibre
over `y` makes the morphism finite over a neighbourhood of `y`.  Those neighbourhoods, taken over
the closed points only, cover `X`, because their union's complement is a closed set containing no
closed point and `X` is a Jacobson space; and `AlgebraicGeometry.IsFinite` is Zariski-local at
the target.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZP](https://stacks.math.columbia.edu/tag/0FZP)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The residue field at a closed point of a scheme locally of finite type over a field is
finite over that field.**  `Spec κ(y) ⟶ X` is a closed immersion, hence locally of finite type,
so the composite to `Spec k` is locally of finite type; on a one-point reduced source over a
Jacobson base, locally of finite type is finite. -/
@[ega "IV 10.4.11.1" "(i), special case"]
theorem isFinite_fromSpecResidueField_comp {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {y : ↥X} (hy : IsClosed ({y} : Set ↥X)) :
    IsFinite (X.fromSpecResidueField y ≫ f) := by
  have : IsClosedImmersion (X.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.1 hy
  exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance

/-- **`pr_1^{-1}{y} ∩ pr_2^{-1}{y}` is finite for a closed point `y`.**  The fibre of `pr_1` over
`y` is `Spec κ(y) ×_k X`, on which `pr_2` is the base change of the finite morphism
`Spec κ(y) ⟶ Spec k`; the set in question is contained in the image of one of its fibres. -/
theorem finite_preimage_singleton_inter_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {y : ↥X} (hy : IsClosed ({y} : Set ↥X)) :
    ((Limits.pullback.fst f f).base ⁻¹' ({y} : Set ↥X) ∩
      (Limits.pullback.snd f f).base ⁻¹' ({y} : Set ↥X)).Finite := by
  have hfin := isFinite_fromSpecResidueField_comp f hy
  set g := X.fromSpecResidueField y with hg
  set ι := Limits.pullback.fst (Limits.pullback.fst f f) g with hι
  set π := Limits.pullback.snd (g ≫ f) f with hπ
  set e : Limits.pullback (Limits.pullback.fst f f) g ≅ Limits.pullback (g ≫ f) f :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f f g with he
  have hfac : e.hom ≫ π = ι ≫ Limits.pullback.snd f f := by rw [he, hι, hπ]; simp
  have hinje : Function.Injective (fun v => e.hom.base v) := by
    simpa using (Scheme.homeoOfIso e).injective
  have hS := Scheme.Hom.finite_preimage_singleton π y
  have hfinpre : ((fun v => e.hom.base v) ⁻¹' (π.base ⁻¹' ({y} : Set ↥X))).Finite :=
    hS.preimage hinje.injOn
  refine Set.Finite.subset (hfinpre.image (fun v => ι.base v)) ?_
  rintro w ⟨hw₁, hw₂⟩
  obtain ⟨v, hv⟩ : w ∈ Set.range (fun v => ι.base v) := by
    have hr : Set.range ⇑(Scheme.Hom.fiberι (Limits.pullback.fst f f) y) =
        Set.range (fun v => ι.base v) := rfl
    rw [← hr, Scheme.Hom.range_fiberι]
    exact hw₁
  refine ⟨v, ?_, hv⟩
  have hpt : π.base (e.hom.base v) = (Limits.pullback.snd f f).base (ι.base v) := by
    have := congrArg (fun φ : Limits.pullback (Limits.pullback.fst f f) g ⟶ X => φ.base v) hfac
    simpa using this
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hpt, hv]
  simpa using hw₂

end AlgebraicGeometry

namespace Stacks.Duality

open AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- **The fibre of `Supp 𝒦 ⟶ X` over a closed point is finite.**  The scheme-theoretic support
is the closed subscheme cut out by the annihilator ideal of `𝒦`, whose underlying set is `Supp 𝒦`
and whose inclusion is injective; `Stacks.Duality.base_fst_eq_of_mem_supp_of_base_snd_eq` puts
the fibre inside `pr_1^{-1}{y} ∩ pr_2^{-1}{y}`, which is finite by
`AlgebraicGeometry.finite_preimage_singleton_inter_of_isClosed`. -/
theorem finite_preimage_singleton_subschemeι_comp_snd
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : RepresentsIdentityOnPerfect f K)
    (𝒦 : (Limits.pullback f f).Modules) [𝒦.IsQuasicoherent] [𝒦.IsFiniteType]
    (eK : K ≅ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj 𝒦)
    {y : ↥X} (hy : IsClosed ({y} : Set ↥X)) :
    (((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι ≫ Limits.pullback.snd f f).base ⁻¹'
      ({y} : Set ↥X)).Finite := by
  have hinj : Function.Injective
      (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.base :=
    (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.isClosedEmbedding.injective
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset (finite_preimage_singleton_inter_of_isClosed f hy) ?_
  rintro w ⟨v, hv, rfl⟩
  have hv₂ : (Limits.pullback.snd f f).base
      ((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.base v) = y := by
    simpa using hv
  have hmem : (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.base v ∈
      SheafOfModules.supp 𝒦 := by
    rw [← Scheme.Modules.coe_support_annihilatorIdeal 𝒦,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self v
  exact ⟨by
      simpa using base_fst_eq_of_mem_supp_of_base_snd_eq f K hΦ 𝒦 eK hy hmem hv₂,
    by simpa using hv₂⟩

/-- **The scheme-theoretic support of `𝒦` is finite over `X` along `pr_2`**, which is the
instance hypothesis of [Stacks, Tag 0FZP].  The fibres over the closed points are finite, so
[Stacks, Tag 02UP] makes the morphism finite over a neighbourhood of each closed point; those
neighbourhoods cover `X` because their union's complement is closed with no closed point and `X`
is Jacobson, and `AlgebraicGeometry.IsFinite` is Zariski-local at the target. -/
theorem isFinite_subschemeι_comp_snd
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : RepresentsIdentityOnPerfect f K)
    (𝒦 : (Limits.pullback f f).Modules) [𝒦.IsQuasicoherent] [𝒦.IsFiniteType]
    (eK : K ≅ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj 𝒦) :
    IsFinite ((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι ≫ Limits.pullback.snd f f) := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace f
  classical
  choose V hV hVfin using fun y : {y : ↥X // IsClosed ({y} : Set ↥X)} =>
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton
      ((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι ≫ Limits.pullback.snd f f) y.1
      (finite_preimage_singleton_subschemeι_comp_snd f K hΦ 𝒦 eK y.2)
  have hloc : IsZariskiLocalAtTarget (@IsFinite) :=
    Morphisms.isFinite_isZariskiLocalAtTarget
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V ?_ hVfin
  by_contra hne
  have hcl : IsClosed ((⨆ y, V y : X.Opens) : Set ↥X)ᶜ :=
    (⨆ y, V y : X.Opens).isOpen.isClosed_compl
  have hnonempty : (((⨆ y, V y : X.Opens) : Set ↥X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hall
    exact hne (TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset hall.ge))
  obtain ⟨z, hz, hzc⟩ := by
    have h := closure_inter_closedPoints (X := ↥X) hcl
    rw [← h] at hnonempty
    exact (closure_nonempty_iff.1 hnonempty)
  exact hz (by
    have : z ∈ V ⟨z, mem_closedPoints_iff.1 hzc⟩ := hV _
    exact Opens.mem_iSup.2 ⟨_, this⟩)

end Stacks.Duality

end
