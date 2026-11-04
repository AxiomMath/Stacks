module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Profinite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Vanishing in degrees `≥ 3` from vanishing at bounded-torsion coefficients

Let `G` be a profinite group. If the continuous cohomology of `G` vanishes in degrees `≥ 2` at
every discrete `G`-module annihilated by a nonzero integer, then it vanishes in degrees `≥ 3` at
*every* discrete `G`-module.

This is the last step of the proof of [Stacks, Tag 03R8], in the form that needs no four-term
exact sequence. For a discrete `G`-module `M` and a nonzero integer `m`, the kernel and the
cokernel of `m • 𝟙 M` are annihilated by `m`, so the hypothesis kills their cohomology in degrees
`≥ 2`; the long exact sequences of the two short exact sequences

`0 ⟶ ker(m • 𝟙) ⟶ M ⟶ coim(m • 𝟙) ⟶ 0`  and  `0 ⟶ coim(m • 𝟙) ⟶ M ⟶ coker(m • 𝟙) ⟶ 0`

then make `H ^ q(G, M) ⟶ H ^ q(G, M)` induced by `m • 𝟙 M` a monomorphism for `q ≥ 3`, that is,
multiplication by `m` injective on `H ^ q(G, M)`. But positive-degree continuous cohomology of a
profinite group is torsion ([Stacks, Tag 0DV3] part (1),
`Stacks.GroupCohomology.continuousGroupCohomology_isTorsion`), so every element is killed by some
nonzero integer, and a torsion group on which multiplication by every nonzero integer is
injective is zero.

The source instead deduces the degrees `≥ 3` from the four-term exact sequence
`0 → A → M → M ⊗ 𝐐 → B → 0`; that route is
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_fourTerm_rat` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.FourTermVanishing`, and it asks a
caller for the sequence, which means constructing `M ⊗ 𝐐` as a discrete `G`-module. The route
here asks for nothing beyond the vanishing hypothesis.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_map_g` and
  `Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_succ_map_f` — the two monomorphism
  corollaries of the long exact sequence of
  `StacksFrontier.Algebra.Homology.RightDerivedDelta`, which records only the vanishing ones.
* `Stacks.Cohomology.RightDerivedDelta.shortExact_coimage_cokernel` — the image sequence
  `0 ⟶ im f ⟶ Y ⟶ coker f ⟶ 0`, with the image presented through the canonical comparison from
  the coimage so that it glues to the coimage-image factorisation of `f`.
* `Stacks.Cohomology.RightDerivedDelta.rightDerived_map_zsmul_id` — the `ℕ`-indexed right derived
  functors send `m • 𝟙 M` to `m • 𝟙`.
* `Stacks.GroupCohomology.mono_rightDerived_continuousGModuleInvariants_map_zsmul_id` —
  multiplication by `m` is injective on `H ^ (n+1)(G, M)` once the cohomology of the kernel of
  `m • 𝟙 M` vanishes in degree `n + 1` and that of its cokernel in degree `n`.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_three_le_of_annihilated` — the
  statement at the head of this file.

## Implementation notes

**Why `m • 𝟙 N = 0` rather than torsion.** The hypothesis is stated for modules annihilated by a
single nonzero integer, not for all torsion modules. That is strictly weaker than part (2) of
[Stacks, Tag 03R8] — a module annihilated by `m` is torsion — and it is all the argument uses:
the kernel and cokernel of `m • 𝟙 M` are annihilated by `m` by a two-line computation with
`cancel_mono` and `cancel_epi`, with no element chase. It also keeps the statement free of any
predicate on the underlying group of a discrete module.

**Why `Functor.rightDerived` sending `m • 𝟙` to `m • 𝟙` is proved rather than inferred.** Mathlib
has no `Additive` instance for `CategoryTheory.Functor.rightDerived`: the functor is
`injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor _ _ n` and
`injectiveResolutions` carries no additivity instance, so `inferInstance` fails. On a single
`m • 𝟙 M` the conclusion is still available, from `CategoryTheory.Functor.rightDerived_map_eq`
read on `m • 𝟙` of a chosen injective resolution, which is
`Stacks.Cohomology.RightDerivedDelta.rightDerived_map_zsmul_id`.

**Why the argument is run at the category of discrete `G`-modules.** The homological content is
not stated for a general additive functor out of an abelian category with enough injectives and
then instantiated, because instantiating such a statement does not elaborate: the `kernel` and
`cokernel` of `m • 𝟙 M` in the general statement carry the `HasKernel`/`HasCokernel` instances
derived from that statement's own `Abelian C` hypothesis, and reconciling those with the ones
instance search finds at `ContinuousGModule` exhausts the `isDefEq` budget — the same failure
mode recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.FourTermVanishing`. What is
general here is only what can be instantiated cheaply: the long exact sequence corollaries, whose
short complexes the caller supplies, and the `zsmul` identity, which mentions no kernels.

**Why the vanishing, and not the monomorphism, crosses between the two indexings.**
`continuousGroupCohomology` is `CategoryTheory.Functor.rightDerivedPlus` and the long exact
sequence is stated for the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`; the two are
compared by `Stacks.DerivedIndexing.rightDerivedIso`. Vanishing transports across it in one step,
as in `FourTermVanishing`, and so does torsion, by injectivity of its components. A monomorphism
of the form `F.map φ` does not: identifying `(Q.rightDerivedPlus n).map φ` with
`(continuousGroupCohomologyFunctor G n).map φ` across the comparison exhausts the `isDefEq`
budget, while the same identification on objects is immediate. So the whole argument is carried
out on the `ℕ`-indexed side and only the final vanishing is transported.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): the proposition whose
  last step this is. No part of that tag is registered here; this is one step of its proof, and
  the hypothesis is weaker than part (2) of the tag.
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3): part (1), the torsion
  statement, which is the other input.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): continuous group
  cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.Cohomology.RightDerivedDelta

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Abelian B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Horseshoe

variable {S : ShortComplex B} (H : Horseshoe S) (Q : B ⥤ D) [Q.Additive]
  [HasInjectiveResolutions B]

include H in
/-- **`RⁿQ X₂ ⟶ RⁿQ X₃` is a monomorphism when `RⁿQ X₁` vanishes**, by exactness of the long
exact sequence at `RⁿQ X₂`. This is the monomorphism half of
`Stacks.Cohomology.RightDerivedDelta.Horseshoe.isIso_rightDerived_map_g`, which assumes the
vanishing of `Rⁿ⁺¹Q X₁` as well in order to get an epimorphism too. -/
theorem mono_rightDerived_map_g (n : ℕ) (h₁ : IsZero ((Q.rightDerived n).obj S.X₁)) :
    Mono ((Q.rightDerived n).map S.g) := by
  have hse := H.shortExact_mapSequence Q
  have hmono : Mono (HomologicalComplex.homologyMap (H.mapSequence Q).g n) :=
    (ShortComplex.exact_iff_mono _
      ((h₁.of_iso (H.J₁.isoRightDerivedObj' Q n).symm).eq_of_src _ 0)).1
      (hse.homology_exact₂ n)
  rw [H.rightDerived_map_g Q n]
  infer_instance

include H in
/-- **`Rⁿ⁺¹Q X₁ ⟶ Rⁿ⁺¹Q X₂` is a monomorphism when `RⁿQ X₃` vanishes**, by exactness of the long
exact sequence at `Rⁿ⁺¹Q X₁`: the incoming connecting morphism has vanishing source, hence is
zero.

At `n = 0` this is `Stacks.Cohomology.RightDerivedDelta.Horseshoe.mono_rightDerived_zero_map_f`
with a hypothesis, the latter needing none because there is no `R⁻¹Q`. -/
theorem mono_rightDerived_succ_map_f (n : ℕ) (h₃ : IsZero ((Q.rightDerived n).obj S.X₃)) :
    Mono ((Q.rightDerived (n + 1)).map S.f) := by
  have hse := H.shortExact_mapSequence Q
  have hmono : Mono (HomologicalComplex.homologyMap (H.mapSequence Q).f (n + 1)) :=
    (ShortComplex.exact_iff_mono _
      ((h₃.of_iso (H.J₃.isoRightDerivedObj' Q n).symm).eq_of_src _ 0)).1
      (hse.homology_exact₁ n (n + 1) (ComplexShape.up_rel_succ n))
  rw [H.rightDerived_map_f Q (n + 1)]
  infer_instance

end Horseshoe

section Existence

variable [EnoughInjectives B] {S : ShortComplex B} (hS : S.ShortExact) (Q : B ⥤ D) [Q.Additive]

include hS in
/-- **`RⁿQ X₂ ⟶ RⁿQ X₃` is a monomorphism when `RⁿQ X₁` vanishes**, with no resolution
mentioned. -/
theorem mono_rightDerived_map_g (n : ℕ) (h₁ : IsZero ((Q.rightDerived n).obj S.X₁)) :
    Mono ((Q.rightDerived n).map S.g) :=
  (horseshoe hS).mono_rightDerived_map_g Q n h₁

include hS in
/-- **`Rⁿ⁺¹Q X₁ ⟶ Rⁿ⁺¹Q X₂` is a monomorphism when `RⁿQ X₃` vanishes**, with no resolution
mentioned. -/
theorem mono_rightDerived_succ_map_f (n : ℕ) (h₃ : IsZero ((Q.rightDerived n).obj S.X₃)) :
    Mono ((Q.rightDerived (n + 1)).map S.f) :=
  (horseshoe hS).mono_rightDerived_succ_map_f Q n h₃

end Existence

section ZsmulId

/-- **The image sequence `0 ⟶ im f ⟶ Y ⟶ coker f ⟶ 0` is short exact**, with the image presented
as the abelian coimage through the canonical comparison, which is the shape in which it glues to
the coimage-image factorisation `CategoryTheory.Abelian.coimage_image_factorisation` of `f`. -/
theorem shortExact_coimage_cokernel {X Y : B} (f : X ⟶ Y) :
    (ShortComplex.mk ((Abelian.coimageIsoImage f).hom ≫ Abelian.image.ι f)
      (cokernel.π f) (by simp)).ShortExact := by
  have himg : (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
      (Abelian.image_ι_comp_eq_zero (cokernel.condition f))).ShortExact :=
    { exact := (ShortComplex.exact_iff_exact_image_ι
        (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))).1
        (ShortComplex.exact_cokernel f) }
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk
      (S₁ := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
        (Abelian.image_ι_comp_eq_zero (cokernel.condition f)))
      (S₂ := ShortComplex.mk ((Abelian.coimageIsoImage f).hom ≫ Abelian.image.ι f)
        (cokernel.π f) (by simp))
      (Abelian.coimageIsoImage f).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)) himg

/-- **The `ℕ`-indexed right derived functors send `m • 𝟙 M` to `m • 𝟙`.** Mathlib has no
`Additive` instance for `CategoryTheory.Functor.rightDerived`, so this is not
`CategoryTheory.Functor.map_zsmul`; it is `CategoryTheory.Functor.rightDerived_map_eq` read on
the morphism `m • 𝟙` of a chosen injective resolution, which descends `m • 𝟙 M`, followed by
additivity of the functor that computes homology degreewise. -/
theorem rightDerived_map_zsmul_id [HasInjectiveResolutions B] (F : B ⥤ D) [F.Additive]
    (M : B) (m : ℤ) (n : ℕ) :
    (F.rightDerived n).map (m • 𝟙 M) = m • 𝟙 ((F.rightDerived n).obj M) := by
  obtain ⟨P⟩ := HasInjectiveResolution.out (Z := M)
  have hw : P.ι ≫ (m • 𝟙 P.cocomplex) =
      (CochainComplex.single₀ B).map (m • 𝟙 M) ≫ P.ι := by
    simp
  have hadd : ∀ X : HomologicalComplex D (ComplexShape.up ℕ),
      HomologicalComplex.homologyMap (m • 𝟙 X) n =
        m • 𝟙 ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj X) := by
    intro X
    show (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map (m • 𝟙 X) = _
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rw [F.rightDerived_map_eq n (m • 𝟙 M) (m • 𝟙 P.cocomplex) hw]
  simp [hadd]

end ZsmulId

end Stacks.Cohomology.RightDerivedDelta

namespace Stacks.GroupCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous group cohomology vanishes iff the `ℕ`-indexed right derived functor of invariants
does. -/
private theorem isZero_continuousGroupCohomology_iff_rightDerived (q : ℕ)
    (N : ContinuousGModule.{u, max u v} G) :
    IsZero (continuousGroupCohomology.{u, v} G q N) ↔
      IsZero (((continuousGModuleInvariants.{u, max u v} G).rightDerived q).obj N) :=
  (Iso.isZero_iff ((Stacks.DerivedIndexing.rightDerivedIso
    (continuousGModuleInvariants.{u, max u v} G) q).app N)).symm

/-- **`Rⁿ⁺¹` of invariants sends `m • 𝟙 M` to a monomorphism**, given that the continuous
cohomology of the kernel of `m • 𝟙 M` vanishes in degree `n + 1` and that of its cokernel
vanishes in degree `n`. Since the right derived functor sends `m • 𝟙 M` to `m • 𝟙`
(`Stacks.Cohomology.RightDerivedDelta.rightDerived_map_zsmul_id`), this says that multiplication
by `m` is injective on the degree-`n + 1` cohomology of `M`.

The coimage-image factorisation writes `m • 𝟙 M` as `M ⟶ coim ⟶ im ⟶ M`. Its first map is the
quotient map of `0 ⟶ ker ⟶ M ⟶ coim ⟶ 0`, so the long exact sequence sends it to a monomorphism
because the cohomology of `ker` vanishes in degree `n + 1`
(`Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_map_g`); its composite tail is the
inclusion of `0 ⟶ im ⟶ M ⟶ coker ⟶ 0`, so the long exact sequence sends it to a monomorphism
because the cohomology of `coker` vanishes in degree `n`
(`Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_succ_map_f`). The hypotheses are stated
in terms of `continuousGroupCohomology` and converted to the `ℕ`-indexed right derived functors
by `Stacks.DerivedIndexing.rightDerivedIso`, exactly as in
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_iff_isZero_rightDerived`. -/
theorem mono_rightDerived_continuousGModuleInvariants_map_zsmul_id
    (M : ContinuousGModule.{u, max u v} G) (m : ℤ) (n : ℕ)
    (hker : IsZero (continuousGroupCohomology.{u, v} G (n + 1) (kernel (m • 𝟙 M))))
    (hcoker : IsZero (continuousGroupCohomology.{u, v} G n (cokernel (m • 𝟙 M)))) :
    Mono (((continuousGModuleInvariants.{u, max u v} G).rightDerived (n + 1)).map
      (m • 𝟙 M)) := by
  have hker' := (isZero_continuousGroupCohomology_iff_rightDerived G (n + 1) _).1 hker
  have hcoker' := (isZero_continuousGroupCohomology_iff_rightDerived G n _).1 hcoker
  have h₁ := Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_map_g
    (S := ShortComplex.mk (kernel.ι (m • 𝟙 M))
      (cokernel.π (kernel.ι (m • 𝟙 M))) (by simp))
    { exact := ShortComplex.exact_cokernel (kernel.ι (m • 𝟙 M)) }
    (continuousGModuleInvariants.{u, max u v} G) (n + 1) hker'
  have h₂ := Stacks.Cohomology.RightDerivedDelta.mono_rightDerived_succ_map_f
    (Stacks.Cohomology.RightDerivedDelta.shortExact_coimage_cokernel (m • 𝟙 M))
    (continuousGModuleInvariants.{u, max u v} G) n hcoker'
  have hcomp : m • 𝟙 M = cokernel.π (kernel.ι (m • 𝟙 M)) ≫
      ((Abelian.coimageIsoImage (m • 𝟙 M)).hom ≫ Abelian.image.ι (m • 𝟙 M)) :=
    (Abelian.coimage_image_factorisation (m • 𝟙 M)).symm
  rw [hcomp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- **Vanishing of continuous group cohomology in degrees `≥ 3` from vanishing in degrees `≥ 2`
at bounded-torsion coefficients.** Let `G` be a profinite group and suppose that for every
discrete `G`-module `N` annihilated by some nonzero integer one has `H ^ q(G, N) = 0` for all
`q ≥ 2`. Then

`H ^ q(G, M) = 0` for every discrete `G`-module `M` and every `q ≥ 3`.

This is the last step of the proof of [Stacks, Tag 03R8] in the form that needs no four-term
exact sequence: the hypothesis is implied by — and is strictly weaker than — part (2) of that
tag, which is quantified over all torsion modules, and nothing else about `M` is used.

The two inputs are
`Stacks.GroupCohomology.mono_rightDerived_continuousGModuleInvariants_map_zsmul_id`, which makes
multiplication by a nonzero integer injective on `H ^ q(G, M)`, and
`Stacks.GroupCohomology.continuousGroupCohomology_isTorsion` ([Stacks, Tag 0DV3] part (1)),
which says every element of `H ^ q(G, M)` is killed by one. -/
theorem isZero_continuousGroupCohomology_of_three_le_of_annihilated
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    (h₂ : ∀ (N : ContinuousGModule.{u, max u v} G) (m : ℤ), m ≠ 0 → m • 𝟙 N = 0 →
      ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q N))
    (M : ContinuousGModule.{u, max u v} G) (q : ℕ) (hq : 3 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} G q M) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by lia⟩
  have hmono : ∀ m : ℤ, m ≠ 0 →
      Mono (m • 𝟙 (((continuousGModuleInvariants.{u, max u v} G).rightDerived
        (n + 1)).obj M)) := by
    intro m hm
    have hkz : m • 𝟙 (kernel (m • 𝟙 M)) = 0 := by
      rw [← cancel_mono (kernel.ι (m • 𝟙 M)), Preadditive.zsmul_comp, Category.id_comp,
        zero_comp]
      simpa only [Preadditive.comp_zsmul, Category.comp_id] using kernel.condition (m • 𝟙 M)
    have hcz : m • 𝟙 (cokernel (m • 𝟙 M)) = 0 := by
      rw [← cancel_epi (cokernel.π (m • 𝟙 M)), Preadditive.comp_zsmul, Category.comp_id,
        comp_zero]
      simpa only [Preadditive.zsmul_comp, Category.id_comp] using cokernel.condition (m • 𝟙 M)
    have hmap := mono_rightDerived_continuousGModuleInvariants_map_zsmul_id G M m n
      (h₂ (kernel (m • 𝟙 M)) m hm hkz (n + 1) (by lia))
      (h₂ (cokernel (m • 𝟙 M)) m hm hcz n (by lia))
    rwa [Stacks.Cohomology.RightDerivedDelta.rightDerived_map_zsmul_id] at hmap
  refine (isZero_continuousGroupCohomology_iff_rightDerived G (n + 1) M).2 ?_
  apply (IsZero.iff_id_eq_zero _).mpr
  ext a
  have eM := (Stacks.DerivedIndexing.rightDerivedIso
    (continuousGModuleInvariants.{u, max u v} G) (n + 1)).app M
  obtain ⟨m, hm⟩ := continuousGroupCohomology_isTorsion.{u, v} G hG (n + 1) (by lia) M
    (x := eM.hom.hom a)
  have hinj : Function.Injective eM.hom.hom :=
    (AddCommGrpCat.mono_iff_injective eM.hom).mp inferInstance
  have hma : (m : ℤ) • a = 0 := hinj (by rw [map_zsmul, map_zero]; exact hm)
  apply (AddCommGrpCat.mono_iff_injective _).mp
    (hmono (m : ℤ) (mem_nonZeroDivisors_iff_ne_zero.mp m.2))
  show (m : ℤ) • a = (m : ℤ) • 0
  rwa [smul_zero]

end Stacks.GroupCohomology

end
