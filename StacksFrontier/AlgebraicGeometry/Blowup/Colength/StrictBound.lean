module

public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
public import StacksFrontier.AlgebraicGeometry.ClopenLift.Cohomology
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering

/-!
# The strict length inequality of Stacks Tag 0AGT, for an arbitrary scheme over an affine base

Let `f : X ⟶ Spec A` be a scheme over an affine base, let `I ⊆ A` be an ideal of finite
colength, let `E` be an effective Cartier divisor on `X` which is not the unit ideal sheaf, and
let `J'` be a sheaf of ideals. This file proves

`length_A Γ(V(J'), 𝒪) < length_A (A / I)`

from four inputs about `X`, `E` and `J'`: the vanishing of the first cohomology of the ideal
sheaf of `J' · E`, the surjectivity of `A ⟶ Γ(X, 𝒪_X)`, the vanishing of `I` in
`Γ(V(J' · E), 𝒪)`, and an injection of `Γ(V(J'), 𝒪)` into the global sections of the twist
`𝒪_X(-E)|_{V(J')}`. None of them is about lengths.

For the blowup of a two-dimensional regular local ring in its maximal ideal, with `E` the `d`-th
power of the exceptional divisor and `J' = I𝒪_X(dE)`, all four hold, and the resulting
unconditional strict inequality of [Stacks, Tag 0AGT] is
`AlgebraicGeometry.length_globalSections_lt_length_quotient_blowUp` in
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/RegularStrictBound.lean`, which discharges the
four inputs there. The lemma of this file is the length-theoretic half of that proof and
carries no `@[stacks]` registration.

## Main results

* `Stacks.Blowup.Colength.length_globalSections_lt_length_quotient` — the strict inequality
  from the four inputs.

## The argument

The source's: since `H¹(X, I𝒪_X) = 0` and `Γ(X, 𝒪_X) = A`, the map

`A / I ⟶ Γ(V(I𝒪_X), 𝒪)`

is surjective; the submodule of sections vanishing on `V(E)` is proper, because the image of
`1` does not vanish there as `E ≠ 𝒪_X`; and that submodule receives `Γ(V(J'), 𝒪)` injectively.
A proper submodule of a module of finite length has strictly smaller length, and length only
decreases along injections and surjections, which gives the display.

The surjectivity is derived here from the vanishing of `H¹`: the ideal-sheaf sequence
`0 ⟶ ℐ ⟶ 𝒪_X ⟶ 𝒪_{V(I𝒪_X)} ⟶ 0` of the closed immersion
(`Stacks.Tag0B5PClopenLift.shortExact_idealShortComplex`) stays exact on global sections where
the first cohomology of its kernel vanishes
(`Stacks.AmpleCohomologicalCriterion.surjective_evaluation_map_g`), and the two spellings of
first cohomology are compared by
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`.

The injection into the vanishing submodule is the left-hand map of the sequence of
[Stacks, Tag 0C4T] for the factorization `I𝒪_X = J' · E`,

`0 ⟶ 𝒪_X(-E)|_{V(J')} ⟶ 𝒪_{V(J' · E)} ⟶ 𝒪_{V(E)} ⟶ 0`

(`Stacks.Divisors.exists_shortExact_mul`): it is a monomorphism, and sections over an open
preserve monomorphisms because they are left exact
(`Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor`), so it is injective on global
sections, and it lands in the kernel of restriction to `V(E)` because the composite of the two
maps of the sequence is zero.

## Implementation notes

The statement is for an arbitrary scheme over an arbitrary affine base: the regular local
surface and the blowup enter only through the four inputs, which are discharged for them in
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/RegularStrictBound.lean`. The `A`-algebra
structures on the rings of global functions of `X` and of the closed subschemes are the ones
induced by the structure morphism, introduced by `letI` in the statement in the spelling
`Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient` uses, so that the two
length statements of the tag are about the same `A`-module. The `A`-module structure on the
sections of the twist is the restriction of scalars of its `Γ(X, 𝒪_X)`-module structure.

Three small facts about morphisms of modules are proved inside the proof rather than named: that
a composite which vanishes vanishes on sections, that a monomorphism is injective on sections,
and the additivity and linearity of `Scheme.Modules.Hom.app`. Stating them would duplicate
`AlgebraicGeometry.Scheme.IdealSheafData.comp_app_apply` and its several copies elsewhere in the
tree; keeping them abstract inside the proof also keeps the kernel from unfolding the concrete
pushforward and pullback of the twist, which it does not survive.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Blowup.Colength

universe u

/-- **Global functions restrict onto a closed subscheme whose ideal sheaf has vanishing first
cohomology.** This is part (3) of [Stacks, Tag 0AGS] consumed: the ideal-sheaf sequence of the
closed immersion stays exact on global sections where the first cohomology of the ideal sheaf
vanishes. -/
private theorem surjective_appTop_subschemeι
    {X : Scheme.{u}} (J : X.IdealSheafData)
    (hH1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom)))) :
    Function.Surjective (J.subschemeι.appTop).hom :=
  Stacks.AmpleCohomologicalCriterion.surjective_evaluation_map_g X ⊤
    (Stacks.Tag0B5PClopenLift.shortExact_idealShortComplex J.subschemeι)
    ((Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ 1 _).2 hH1)

/-- The structure map of the ring of functions of a closed subscheme, as an `A`-algebra over an
affine base, is the restriction along the closed immersion of the structure map of the ambient
scheme. -/
private theorem algebraMap_subscheme_eq
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (J : X.IdealSheafData) :
    letI : Algebra A Γ(J.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
    (algebraMap A Γ(J.subscheme, ⊤)) =
      (J.subschemeι.appTop).hom.comp ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom := by
  change ((Scheme.ΓSpecIso (.of A)).inv ≫ (J.subschemeι ≫ f).appTop).hom = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- **A proper sheaf of ideals cuts out a closed subscheme with a nonzero ring of functions.**
The subscheme is empty only for the unit ideal sheaf, and a nonempty scheme has a nontrivial
ring of global functions. -/
private theorem nontrivial_globalSections_subscheme
    {X : Scheme.{u}} (K : X.IdealSheafData) (hK : K ≠ ⊤) :
    Nontrivial Γ(K.subscheme, ⊤) := by
  rcases isEmpty_or_nonempty K.subscheme with h | h
  · refine absurd ?_ hK
    rwa [← Scheme.IdealSheafData.ker_subschemeι K, Scheme.Hom.ker_eq_top_iff_isEmpty]
  · have : Nonempty (⊤ : (K.subscheme).Opens) := ⟨⟨h.some, trivial⟩⟩
    exact Scheme.component_nontrivial _ _

/-- **The sections of a closed subscheme vanishing on a smaller one have length strictly less
than the colength of the ideal they come from.** Let `J ⊆ K` be sheaves of ideals with `K` proper,
let `A / I` have finite length, let the first cohomology of the ideal sheaf of `J` vanish, let
`A` surject onto `Γ(X, 𝒪_X)` and let `I` die in `Γ(V(J), 𝒪)`. Then `A / I` surjects onto
`Γ(V(J), 𝒪)`, and the kernel of restriction to `V(K)` does not contain the image of `1`, so its
preimage is a proper submodule of `A / I`. -/
private theorem length_ker_inclusion_lt_length_quotient
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (I : Ideal A) (J K : X.IdealSheafData) (hJK : J ≤ K) (hK : K ≠ ⊤)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤)
    (hH1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom))))
    (hΓ : Function.Surjective ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)
    (hI : ∀ a ∈ I, (J.subschemeι.appTop).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) = 0) :
    letI : Algebra A Γ(J.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.length A
        ((RingHom.ker ((Scheme.IdealSheafData.inclusion hJK).appTop).hom).restrictScalars A)
      < Module.length A (A ⧸ I) := by
  classical
  let : Algebra A Γ(J.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (Module.length_ne_top_iff.mp hfin)
  have := nontrivial_globalSections_subscheme K hK
  have hmap := algebraMap_subscheme_eq f J
  have hsurj : Function.Surjective (algebraMap A Γ(J.subscheme, ⊤)) := by
    rw [hmap]
    exact (surjective_appTop_subschemeι J hH1).comp hΓ
  have hker : I ≤ LinearMap.ker (Algebra.linearMap A Γ(J.subscheme, ⊤)) := by
    intro a ha
    simp only [LinearMap.mem_ker, Algebra.linearMap_apply]
    rw [hmap]
    exact hI a ha
  set φ : (A ⧸ I) →ₗ[A] Γ(J.subscheme, ⊤) := I.liftQ (Algebra.linearMap A _) hker
  have hφmk : ∀ a : A, φ (I.mkQ a) = algebraMap A Γ(J.subscheme, ⊤) a := fun a => rfl
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    exact ⟨I.mkQ a, (hφmk a).trans ha⟩
  set ρ := ((Scheme.IdealSheafData.inclusion hJK).appTop).hom
  set N : Submodule A Γ(J.subscheme, ⊤) := (RingHom.ker ρ).restrictScalars A
  set M : Submodule A (A ⧸ I) := N.comap φ
  have hMne : M ≠ ⊤ := fun h => by
    have hz : ρ (φ (I.mkQ 1)) = 0 := (h ▸ Submodule.mem_top : I.mkQ 1 ∈ M)
    rw [hφmk, map_one, map_one] at hz
    exact one_ne_zero hz
  have h2 : Module.length A N ≤ Module.length A M := by
    refine Module.length_le_of_surjective (LinearMap.restrict φ fun _ hx => hx) ?_
    intro y
    obtain ⟨a, ha⟩ := hφ y.1
    refine ⟨⟨a, ?_⟩, Subtype.ext ?_⟩
    · change φ a ∈ N
      rw [ha]
      exact y.2
    · simpa [LinearMap.restrict_apply] using ha
  exact h2.trans_lt (Submodule.length_lt hMne)

/-- **The strict length inequality of [Stacks, Tag 0AGT], from four inputs.** Let
`f : X ⟶ Spec A` be a scheme over an affine base, let `I ⊆ A` be an ideal with `A / I` of finite
length, let `E` be an effective Cartier divisor on `X` which is not the unit ideal sheaf, and let
`J'` be a sheaf of ideals with `J' · E ⊆ E`. Suppose the first cohomology of the ideal sheaf of
`J' · E` vanishes, `A ⟶ Γ(X, 𝒪_X)` is surjective, `I` vanishes in `Γ(V(J' · E), 𝒪)`, and
`Γ(V(J'), 𝒪)` injects `A`-linearly into the global sections of the twist `𝒪_X(-E)|_{V(J')}`.
Then

`length_A Γ(V(J'), 𝒪) < length_A (A / I)`.

For the blowup of a two-dimensional regular local ring in its maximal ideal all four inputs
hold, and `AlgebraicGeometry.length_globalSections_lt_length_quotient_blowUp` is the resulting
unconditional inequality. -/
public theorem length_globalSections_lt_length_quotient
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (I : Ideal A) (E J' : X.IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) (hEtop : E ≠ ⊤)
    (hsub : J' * E ≤ E)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤)
    (hH1 : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit (J' * E).subschemeι.toRingCatSheafHom))))
    (hΓ : Function.Surjective ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)
    (hI : ∀ a ∈ I, ((J' * E).subschemeι.appTop).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) = 0) :
    letI : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra A Γ(J'.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (J'.subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Module A Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist E)),
        (⊤ : X.Opens)) :=
      Module.compHom _ (algebraMap A Γ(X, ⊤))
    ∀ t : Γ(J'.subscheme, ⊤) →ₗ[A] Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist E)),
        (⊤ : X.Opens)),
      Function.Injective t →
      Module.length A Γ(J'.subscheme, ⊤) < Module.length A (A ⧸ I) := by
  classical
  let algX : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
  let algZ' : Algebra A Γ(J'.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (J'.subschemeι ≫ f).appTop).hom.toAlgebra
  let modT : Module A Γ((Scheme.Modules.pushforward J'.subschemeι).obj
        ((Scheme.Modules.pullback J'.subschemeι).obj (Stacks.Divisors.negativeTwist E)),
        (⊤ : X.Opens)) :=
    Module.compHom _ (algebraMap A Γ(X, ⊤))
  let algZ : Algebra A Γ((J' * E).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ ((J' * E).subschemeι ≫ f).appTop).hom.toAlgebra
  intro t ht
  obtain ⟨g, zero, hse⟩ := Stacks.Divisors.exists_shortExact_mul E J' hE hsub
  have hcomp : ∀ {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P), a ≫ b = 0 →
      ∀ (U : X.Opens) (y : Γ(M, U)), b.app U (a.app U y) = 0 := by
    intro M N P a b hab U y
    rw [← Scheme.IdealSheafData.comp_app_apply a b U y, hab]
    simp
  have hmono : ∀ {M N : X.Modules} (a : M ⟶ N), Mono a →
      Function.Injective (fun y : Γ(M, (⊤ : X.Opens)) => a.app ⊤ y) := by
    intro M N a ha
    have := Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor X (⊤ : X.Opens)
    exact (ModuleCat.mono_iff_injective ((Stacks.Cohomology.sectionsFunctor X ⊤).map a)).1
      inferInstance
  let ι : Γ(J'.subscheme, ⊤) →ₗ[A] Γ((J' * E).subscheme, ⊤) :=
    { toFun := fun s => g.app ⊤ (t s)
      map_add' := fun s s' => by
        simp only [map_add]
        rfl
      map_smul' := fun a s => by
        have h1 : t (a • s) = (algebraMap A Γ(X, ⊤) a) • t s := t.map_smul a s
        simp only [RingHom.id_apply]
        rw [h1, Scheme.Modules.Hom.app_smul g (algebraMap A Γ(X, ⊤) a) (t s)]
        rfl }
  have hcod : ∀ s, ι s ∈
      (RingHom.ker ((Scheme.IdealSheafData.inclusion hsub).appTop).hom).restrictScalars A := by
    intro s
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker]
    change ((Scheme.IdealSheafData.inclusion hsub).appTop) (g.app ⊤ (t s)) = 0
    rw [← Scheme.IdealSheafData.closedSubschemeRestriction_appTop hsub (g.app ⊤ (t s))]
    exact hcomp g _ zero ⊤ (t s)
  exact (Module.length_le_of_injective (LinearMap.codRestrict _ ι hcod)
    fun s s' h => ht (hmono g hse.mono_f (congrArg Subtype.val h))).trans_lt
    (length_ker_inclusion_lt_length_quotient f I (J' * E) E hsub hEtop hfin hH1 hΓ hI)

end Stacks.Blowup.Colength

end
