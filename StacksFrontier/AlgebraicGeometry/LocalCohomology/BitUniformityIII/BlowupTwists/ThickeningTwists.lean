module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveAmbientSections
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSerreVanishing
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistMap
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BoundQAndD
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftLocal
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0GA7 for the blowup itself: the cohomology of `𝒪_{Yₙ}(q)` and `𝒪_X(q)`

This file states and proves the four clauses of [Stacks, Tag 0GA7] about the *actual* objects of
the Situation of [Stacks, Tag 0GA6]: the blowup `X` of `Spec(A)` in `I`, the twists `𝒪_X(q)` of
its structure sheaf, the thickenings `Yₙ = nY` of its exceptional divisor with their structure
sheaves `𝒪_{Yₙ}`, and the derived-functor sheaf cohomology of those sheaves.

Concretely:

* `X` is `Stacks.Blowup.blowUpSpec I`, the homogeneous spectrum of the Rees algebra `⨁ₙ Iⁿ`;
* `𝒪_X(q)` is `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` of the Rees grading,
  here `Stacks.LocalCohomology.UniformityIII.blowupTwist`;
* `Yₙ` is the closed subscheme of `X` cut out by the `n`-th power of the inverse image of `I`,
  which is an effective Cartier divisor for `n = 1` by
  `Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec`, and `𝒪_{Yₙ}` is the direct image of
  its structure sheaf, here `Stacks.LocalCohomology.UniformityIII.thickeningSheaf`;
* `𝒪_{Yₙ}(q)` is `𝒪_{Yₙ} ⊗_{𝒪_X} 𝒪_X(q)` for the sheafified tensor product of [Stacks,
  Tag 01CA], here `Stacks.LocalCohomology.UniformityIII.thickeningTwist`;
* `Hⁱ(X, ℱ)` is the `i`-th right derived functor of global sections,
  `Hgroup` at `U = ⊤`, here
  `Stacks.LocalCohomology.UniformityIII.blowupH`;
* the canonical maps `Iᑫ → H⁰(X, 𝒪_X(q))` and `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` are the degree-`q`
  section map of [Stacks, Tag 0AG2] for the Rees grading, respectively that map followed by the
  canonical `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)`; these are
  `Stacks.LocalCohomology.UniformityIII.ambientSections` and
  `Stacks.LocalCohomology.UniformityIII.thickeningSections`. Nothing about them is assumed: they
  are built here out of `Stacks.Blowup.reesGradingEquivPow`, which identifies the degree-`q`
  piece of the Rees algebra with `Iᑫ`, and the canonical section map.

Degree `0` is read as global sections rather than as the zeroth derived functor. The proof below
only ever uses the long exact sequence of a short exact sequence of sheaves *within a single
degree* — never the junction between `H⁰` and `H¹` — so no comparison between `Γ(X, -)` and
`H⁰(X, -)` is needed anywhere, and clauses (2) and (4) are statements about honest global
sections.

## What is proved, and what is assumed

The four clauses are theorems. What they take as input is a
`Stacks.LocalCohomology.UniformityIII.GeometricInput`, which carries exactly the part of the
Situation of Tag 0GA6 that precedes the statement of Tag 0GA7:

* the two short exact sequences of sheaves on `X` that the proof uses,
  `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0` and
  `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`, as *morphisms of sheaves* which form a short exact
  sequence. Of the four maps involved only **one** is data, the first map `divα` of the
  thickening sequence: the identification `𝒪_X(1) = 𝒪_X(-Y)` of [Stacks, Tag 02OS] part (3) that
  produces it is not available here for the ideal-sheaf model of the thickenings. The first map
  of the *ambient* sequence is **not** a field — it is
  `Stacks.LocalCohomology.UniformityIII.ambientTwistMap`, built in
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientTwistMap.lean` out of
  the truncation of a graded module and the eventual-bijectivity comparison, with no generator
  chosen. The second map of each is the canonical restriction to the exceptional
  divisor — `Stacks.LocalCohomology.UniformityIII.thickeningTwistRestrict` and
  `Stacks.LocalCohomology.UniformityIII.thickeningTwistProj` — built from the closed immersion
  `Y ↪ Yₙ` of `Stacks.LocalCohomology.UniformityIII.thickeningRestrict`. The exactness of the
  sequences these induce on cohomology is **not** assumed in any degree: in positive degrees it
  comes from the right derived δ-functor of global sections, by
  `Stacks.LocalCohomology.UniformityIII.exact_blowupHMap`, and in degree `0` from left exactness
  of `Γ(X, -)`, by `Stacks.LocalCohomology.UniformityIII.injective_blowupΓMap` and
  `Stacks.LocalCohomology.UniformityIII.exact_blowupΓMap`;
* the defining property of `q₀ = q(S)`, which is the case `n = 1` of clauses (1) and (2);
* the vanishing `Hⁱ(X, 𝒪_Y(q)) = 0` for `i > d`, the consequence of [Stacks, Tags 02V7 and
  01XK] that the paragraph of Tag 0GA6 defining `d` records, asked for on the exceptional
  divisor only;
**Neither of Serre's two theorems on `X` is assumed.** `Hⁱ(X, 𝒪_X(q)) = 0` for `i > 0` and
`q ≫ 0` is `Stacks.LocalCohomology.UniformityIII.amb_serre` below, which is
`Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading` of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveSerreVanishing.lean`; and
`H⁰(X, 𝒪_X(q)) = Iᑫ` for `q ≫ 0` — [Stacks, Tag 0AG6] part (3), which used to be the field
`amb_serre_sections` — is `Stacks.Blowup.exists_forall_bijective_ambientSections` of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveAmbientSections.lean`, whose injective half is
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientSectionsInjective.lean`.
Clause (4) takes its starting threshold from the second of these, so every input of
`GeometricInput` is now part of the Situation of Tag 0GA6 rather than a theorem of the source,
with the single exception recorded in item (4) below.

No clause of Tag 0GA7 is among the fields, and none of the four is assumed for any `n ≥ 2` or
for any `q` at all. Every cohomological hypothesis is about `n = 1`: the vanishing above `d` for
the higher thickenings is *not* assumed, although the source has it for every coherent sheaf,
because the induction of the Stacks proof carries it up the thickenings exactly as it carries
the vanishing in the range `1 ≤ i ≤ d`.

The `n = 1` fields are not a clause of Tag 0GA7 but the *definition* of the integer `q₀` that
the clauses are stated with. Tag 0GA6 defines `q(S)` as the smallest `q(S) ≥ 0` such that for
all `q ≥ q(S)` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d` and `H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`,
and the proof of Tag 0GA7 opens its induction with "the base case `n = 1` is our definition of
`q₀`, as `Y₁ = Y`". `base_vanishing` is the first of those two properties, with the same
restriction `1 ≤ i ≤ d` the definition carries, and `base_surjective` together with
`base_ker_le` is the second — `base_ker_le` being only the implication of the kernel
computation that does not already follow from the second sequence, the other one being
`Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_of_mem`.

This part contains the generic lemmas the proof needs (the inductive step, whiskering,
kernel lifts, left exactness), the cohomology `blowupH` and global sections `blowupΓMap` on the
blowup with their exactness properties, and the thickenings `𝒪_{Yₙ}`, their twists `𝒪_{Yₙ}(q)`
and the restriction maps between them. The vanishing of the ambient composite is in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists.AmbientComposite`,
and the ambient short exact sequence, `GeometricInput` and the four clauses in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists.GeometricInput`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGlobalSections degreeSection)

universe u
universe v w

namespace Stacks.LocalCohomology.UniformityIII

section StepLemma

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **The inductive step of clauses (2) and (4) of Tag 0GA7.**

Given a map of two-step sequences

```
I^{q+1} ----------→ I^q ========= I^q
   │ u₁              │ u₂          │ u₃
   ↓        g₁        ↓      g₂     ↓
   N₁ --------------→ N₂ ---------→ N₃
```

in which the top map is the inclusion, the bottom row is exact at `N₂` with `g₁` injective, both
squares commute, `u₁` and `u₃` are surjective with kernels `J` and `I^{q+1}` respectively, and
`J ⊆ I^{q+1}`: then `u₂` is surjective with kernel `J`.

This is the short five lemma in the form clauses (2) and (4) need, with the subquotients of the
Stacks diagram replaced by the kernels of the vertical maps, so that both the surjectivity and
the description of the kernel come out as conclusions. -/
theorem surjective_and_ker_of_step {q : ℕ} {J : Ideal A} (hJ : J ≤ I ^ (q + 1))
    {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    (g₁ : N₁ →+ N₂) (g₂ : N₂ →+ N₃)
    (u₁ : (I ^ (q + 1) : Ideal A) →+ N₁) (u₂ : (I ^ q : Ideal A) →+ N₂)
    (u₃ : (I ^ q : Ideal A) →+ N₃)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂)
    (sq₁ : ∀ x : (I ^ (q + 1) : Ideal A),
      g₁ (u₁ x) = u₂ ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩)
    (sq₂ : ∀ x, g₂ (u₂ x) = u₃ x)
    (hs₁ : Function.Surjective u₁) (hs₃ : Function.Surjective u₃)
    (hk₁ : ∀ x : (I ^ (q + 1) : Ideal A), u₁ x = 0 ↔ (x : A) ∈ J)
    (hk₃ : ∀ x : (I ^ q : Ideal A), u₃ x = 0 ↔ (x : A) ∈ I ^ (q + 1)) :
    Function.Surjective u₂ ∧ ∀ x : (I ^ q : Ideal A), u₂ x = 0 ↔ (x : A) ∈ J := by
  refine ⟨fun y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hs₃ (g₂ y)
    obtain ⟨z, hz⟩ := (hg (y - u₂ x)).1 (by rw [map_sub, sq₂, hx, sub_self])
    obtain ⟨w, rfl⟩ := hs₁ z
    refine ⟨x + ⟨(w : A), Ideal.pow_le_pow_right (Nat.le_succ q) w.2⟩, ?_⟩
    rw [map_add, ← sq₁, hz]
    abel
  · have h3 : u₃ x = 0 := by rw [← sq₂, hx, map_zero]
    have hx1 : (x : A) ∈ I ^ (q + 1) := (hk₃ x).1 h3
    refine (hk₁ ⟨(x : A), hx1⟩).1 (hg₁ ?_)
    rw [map_zero, sq₁]
    exact hx
  · have hx1 : (x : A) ∈ I ^ (q + 1) := hJ hx
    have h1 : u₁ (⟨(x : A), hx1⟩ : (I ^ (q + 1) : Ideal A)) = 0 := (hk₁ _).2 hx
    have h2 := sq₁ (⟨(x : A), hx1⟩ : (I ^ (q + 1) : Ideal A))
    rw [h1, map_zero] at h2
    exact h2.symm

end StepLemma

section Whiskering

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Two right whiskerings in a row, after a map into the tensor product, are one whiskering of
the composite.

This is `MonoidalCategory.comp_whiskerRight` with the associativity already done, stated in an
abstract monoidal category. Proving it here rather than inline is what makes it usable on the
sheaves of modules of a scheme: there the monoidal category has two spellings,
`X.Modules` and `SheafOfModules X.ringCatSheaf`, and rewriting with associativity inside a goal
that mentions both makes the goal ill-typed at `implicit` transparency. In this context there is
nothing to unfold. -/
theorem comp_whiskerRight_comp {Y F G H X : C} (u : Y ⟶ F ⊗ X) (φ : F ⟶ G) (ψ : G ⟶ H) :
    (u ≫ φ ▷ X) ≫ ψ ▷ X = u ≫ (φ ≫ ψ) ▷ X := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight]

/-- **The interchange identity for a map out of the monoidal unit.** A morphism `f` followed by
`F ⊗ -` applied through the left unitor is the same thing read in the other order: tensor first,
then whisker `f` on the left.

This is `MonoidalCategory.leftUnitor_inv_naturality` and `MonoidalCategory.whisker_exchange`,
proved in an abstract monoidal category for the same reason as `comp_whiskerRight_comp`: on the
sheaves of modules of a scheme the monoidal category has two spellings and rewriting inside a
goal mentioning both makes it ill-typed at `implicit` transparency. -/
theorem comp_leftUnitor_inv_whiskerRight {F X Y : C} (u : 𝟙_ C ⟶ F) (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv ≫ u ▷ Y = ((λ_ X).inv ≫ u ▷ X) ≫ F ◁ f := by
  simp only [Category.assoc, MonoidalCategory.leftUnitor_inv_naturality_assoc,
    MonoidalCategory.whisker_exchange]

/-- **Two whiskerings through the unit compose to one.** A map `u` into the monoidal unit,
whiskered and read through the left unitor, followed by a map `v` out of the unit read through
the inverse unitor, is the whiskering of `u ≫ v`.

This is the shape in which the first sequence of Tag 0GA7 meets the second: the first map of the
ambient sequence lands in `𝒪_X(q) = 𝟙_ ⊗ 𝒪_X(q)` through `λ_`, and the second map leaves it
through `λ_` inverted. Stated abstractly for the reason `comp_whiskerRight_comp` is: the two
spellings `X.Modules` and `SheafOfModules X.ringCatSheaf` of the monoidal category make a
`rw` with associativity inside a goal mentioning both ill-typed at `implicit` transparency,
and here there is nothing to unfold. -/
theorem whiskerRight_comp_leftUnitor_comp {F G X : C} (u : F ⟶ 𝟙_ C) (v : 𝟙_ C ⟶ G) :
    ((u ▷ X) ≫ (λ_ X).hom) ≫ ((λ_ X).inv ≫ (v ▷ X)) = (u ≫ v) ▷ X := by
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← MonoidalCategory.comp_whiskerRight]

/-- A whiskering which is a monomorphism stays one when read through the left unitor. Stated
abstractly: at the concrete monoidal category `Mono` of a composite with an iso is not found by
instance search, the two spellings of the category giving two spellings of the class. -/
theorem mono_whiskerRight_comp_leftUnitor {F X : C} (f : F ⟶ 𝟙_ C) (hf : Mono (f ▷ X)) :
    Mono ((f ▷ X) ≫ (λ_ X).hom) := by
  have := hf
  infer_instance

/-- A whiskering which is an epimorphism stays one when precomposed with the inverse of the left
unitor; this is the shape of `thickeningTwistProj`. Stated abstractly for the same reason as
`mono_whiskerRight_comp_leftUnitor`. -/
theorem epi_leftUnitor_inv_comp_whiskerRight {G X : C} (f : 𝟙_ C ⟶ G) (hf : Epi (f ▷ X)) :
    Epi ((λ_ X).inv ≫ (f ▷ X)) := by
  have := hf
  infer_instance

end Whiskering

section KernelLift

variable {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]

/-- **A complex whose first map is, up to isomorphism, the kernel inclusion of its second is
short exact.** Precisely: if `f ≫ g = 0`, `g` is an epimorphism and the canonical lift
`X ⟶ ker g` of `f` is an isomorphism, then `0 → X → Y → Z → 0` is short exact.

This is the reduction of a short exactness assertion to a *single* isomorphism, and it is what
turns the exactness field of `GeometricInput` into the one statement left open for it. The proof
is the comparison with `CategoryTheory.ShortComplex.shortExact_mk_kernel_ι`, transported along the
isomorphism of short complexes which is the lift in the first place and the identity elsewhere. -/
theorem shortExact_of_isIso_kernelLift {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    [Epi g] [HasKernel g] (hl : IsIso (kernel.lift g f h)) :
    (ShortComplex.mk f g h).ShortExact := by
  have := hl
  refine ShortComplex.shortExact_of_iso
    (S₁ := ShortComplex.mk (kernel.ι g) g (kernel.condition g)) (S₂ := ShortComplex.mk f g h)
    (ShortComplex.isoMk (asIso (kernel.lift g f h)).symm (Iso.refl _) (Iso.refl _) ?_ ?_)
    (ShortComplex.shortExact_mk_kernel_ι g)
  · show (asIso (kernel.lift g f h)).symm.hom ≫ f = kernel.ι g ≫ (Iso.refl Y).hom
    rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq,
      kernel.lift_ι]
  · show (Iso.refl Y).hom ≫ g = g ≫ (Iso.refl Z).hom
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

end KernelLift

section LeftExact

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **A left exact functor carries a short exact sequence to an exact sequence.** The first map
of a short exact sequence is a kernel of the second, a functor preserving finite limits carries
that kernel to a kernel, and a short complex whose first map is a kernel of its second is
exact. -/
theorem exact_map_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) : (S.map F).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ hS.fIsKernel F)
      (Fork.ext (Iso.refl _) (by simp)))

/-- **A left exact functor carries the first map of a short exact sequence to a monomorphism**,
since preserving finite limits implies preserving monomorphisms. -/
theorem mono_map_f_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    Mono (S.map F).f := by
  have := hS.mono_f
  have := preservesMonomorphisms_of_preservesLimitsOfShape F
  exact F.map_mono S.f

end LeftExact

section IdealSheafKernel

/-- The canonical map `𝒪_Y ⟶ g_* 𝒪_W` of sheaves of modules is, on `⊤`-sections, the map
`g.appTop` on global sections. -/
theorem app_top_unitToPushforwardObjUnit {W Y : Scheme.{u}} (g : W ⟶ Y) (y : Γ(Y, ⊤)) :
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app (op ⊤) y =
      g.appTop.hom y := rfl

/-- **A global section pulled back from an ideal of an affine base dies on the closed subscheme
cut out by the inverse image of that ideal.**

The pullback square behind `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` factors
`(J.comap f).subschemeι ≫ f` through `J.subschemeι`, and on an affine target the kernel of
`J.subschemeι` on global sections is `J` itself,
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` at `⊤`.

The identification `K = J.comap f` is taken as a hypothesis rather than written into the
statement so that `subst` removes it; that is what lets the first thickening of the exceptional
divisor, which is a first power, be read off `pow_one` below. -/
theorem app_top_unitToPushforwardObjUnit_eq_zero_of_comap
    {W Y : Scheme.{u}} [IsAffine Y] (f : W ⟶ Y) (J : Y.IdealSheafData)
    (K : W.IdealSheafData) (hK : K = J.comap f) (y : Γ(Y, ⊤))
    (hy : y ∈ J.ideal ⟨⊤, isAffineOpen_top Y⟩) :
    (SheafOfModules.unitToPushforwardObjUnit K.subschemeι.toRingCatSheafHom).val.app (op ⊤)
        (f.appTop.hom y) = 0 := by
  subst hK
  have h0 : J.subschemeι.appTop.hom y = 0 :=
    (Scheme.IdealSheafData.ker_subschemeι_app J ⟨⊤, isAffineOpen_top Y⟩).ge hy
  have hfac : (J.comap f).subschemeι ≫ f =
      ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι) ≫ J.subschemeι := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have happ := congrArg (fun φ : (J.comap f).subscheme ⟶ Y => φ.appTop.hom y) hfac
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, h0, map_zero] at happ
  rw [app_top_unitToPushforwardObjUnit, happ]
  rfl

end IdealSheafKernel

section Objects

/-- The sheaves of modules on a scheme with the sheafified tensor product of [Stacks, Tag 01CA]:
the tensor product is the sheafified tensor product and the unit is the structure sheaf. The
instance is needed at both spellings of the category, since `AlgebraicGeometry.Scheme.Modules` is
a `def` for `SheafOfModules _.ringCatSheaf` and instance search does not unfold it. -/
@[sga "4 IV 12.7" "special case"]
local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- The monoidal structure of `modulesMonoidal` on the sheaves of modules on a scheme, at the
spelling `SheafOfModules X.ringCatSheaf` of the category. -/
local instance modulesMonoidal' (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- Sheaves of modules on a scheme are a Grothendieck abelian category, hence have enough
injectives; `Hgroup` asks for this at the unfolded spelling of the category, where instance
search does not find it. -/
local instance modulesEnoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

/-- **Sections over an open are left exact**: `Γ(U, -)` on sheaves of abelian groups is the
forgetful functor to presheaves followed by evaluation at `U`, and both preserve limits. This
is what makes the degree-`0` statements of Tag 0GA7 theorems rather than hypotheses. -/
local instance sheafSectionsPreservesFiniteLimits {T : Type w} [TopologicalSpace T]
    (U : Opens T) :
    PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{v}).obj (op U)) := by
  have h : (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{v}).obj (op U)
      = sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{v}
        ⋙ (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{v}).obj (op U) := rfl
  rw [h]; infer_instance

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The sheaf cohomology `Hⁱ(X, ℱ)`** of a sheaf of modules on the blowup: the `i`-th right
derived functor of global sections. -/
abbrev blowupH (i : ℕ) (F : (blowupScheme I).Modules) : AddCommGrpCat.{u} :=
  Hgroup (blowupScheme I).ringCatSheaf ⊤ i F

/-- `Hⁱ(X, -)` of a morphism of sheaves, as an additive map. -/
def blowupHMap (i : ℕ) {F G : (blowupScheme I).Modules} (φ : F ⟶ G) :
    blowupH I i F →+ blowupH I i G :=
  ((Hfunctor (blowupScheme I).ringCatSheaf ⊤ i).map φ).hom

/-- `Γ(X, -)` of a morphism of sheaves, as an additive map. -/
def blowupΓMap {F G : (blowupScheme I).Modules} (φ : F ⟶ G) : blowupΓ I F →+ blowupΓ I G :=
  (φ.val.app (op ⊤)).hom.toAddMonoidHom

/-- **The left-hand square of the diagram in the proof of Tag 0GA7, clause (2), for the ambient
sequence.** The composite `Iᑫ⁺¹ → H⁰(X, 𝒪_X(q+1)) → H⁰(X, 𝒪_X(q))` is the canonical map of `Iᑫ`
along the inclusion `I^{q+1} ⊆ Iᑫ`.

This is a theorem rather than an input — it was the field `amb_sq_left` — because the first map
of the ambient sequence is now `ambientTwistMap`. It is
`Stacks.LocalCohomology.UniformityIII.app_top_ambientTwistMap_ambientSections` read through
`blowupΓMap`, which is that map's action on `⊤`-sections by definition. -/
theorem blowupΓMap_ambientTwistMap_ambientSections (q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    blowupΓMap I (ambientTwistMap I q) (ambientSections I (q + 1) x) =
      ambientSections I q ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩ :=
  app_top_ambientTwistMap_ambientSections I q x

/-- `Γ(X, -)` is a functor. -/
theorem blowupΓMap_comp {F G H : (blowupScheme I).Modules} (φ : F ⟶ G) (ψ : G ⟶ H)
    (x : blowupΓ I F) :
    blowupΓMap I (φ ≫ ψ) x = blowupΓMap I ψ (blowupΓMap I φ x) :=
  rfl

/-- `Γ(X, -)` of the zero morphism is zero. -/
@[simp]
theorem blowupΓMap_zero {F F' : (blowupScheme I).Modules} (x : blowupΓ I F) :
    blowupΓMap I (0 : F ⟶ F') x = 0 := by
  show ((0 : F.val ⟶ F'.val).app (op ⊤)).hom x = 0
  simp

/-- `Γ(X, -)` on the blowup is left exact: it is `secF` at `U = ⊤`, whose two factors preserve
finite limits. -/
local instance secFPreservesFiniteLimits :
    PreservesFiniteLimits (secF (blowupScheme I).ringCatSheaf (⊤ : Opens ↥(blowupScheme I))) := by
  unfold secF; infer_instance

/-- **Left exactness of global sections, first half.** For a short exact sequence of sheaves of
modules on the blowup, `Γ(X, ℱ₁) → Γ(X, ℱ₂)` is injective. -/
theorem injective_blowupΓMap
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact) :
    Function.Injective (blowupΓMap I S.f) :=
  (AddCommGrpCat.mono_iff_injective _).1
    (mono_map_f_of_shortExact (secF (blowupScheme I).ringCatSheaf ⊤) hS)

/-- **Left exactness of global sections, second half.** For a short exact sequence of sheaves of
modules on the blowup, `Γ(X, ℱ₁) → Γ(X, ℱ₂) → Γ(X, ℱ₃)` is exact at the middle term. -/
theorem exact_blowupΓMap
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact) :
    Function.Exact (blowupΓMap I S.f) (blowupΓMap I S.g) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (exact_map_of_shortExact (secF (blowupScheme I).ringCatSheaf ⊤) hS)

/-- **The cohomological δ-functor of [Stacks, Tag 010Q] on the blowup**: the right derived
δ-functor of global sections. This is what turns a short exact sequence of sheaves on `X` into a
long exact sequence of cohomology groups, so that the two sequences used by the proof of
Tag 0GA7 need only be supplied as short exact sequences of sheaves. -/
def blowupDelta :
    CategoryTheory.DeltaFunctor (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)
      AddCommGrpCat.{u} :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF (blowupScheme I).ringCatSheaf ⊤)

/-- **The long exact cohomology sequence in a single degree.** For a short exact sequence of
sheaves of modules on the blowup, `Hⁱ(X, ℱ₁) → Hⁱ(X, ℱ₂) → Hⁱ(X, ℱ₃)` is exact in every
degree. -/
theorem exact_blowupHMap {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)}
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (blowupHMap I i S.f) (blowupHMap I i S.g) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 ((blowupDelta I).exact_map hS i)

/-- **The ideal sheaf of the thickening `Yₙ = nY`** of the exceptional divisor: the `n`-th power
of the inverse image under the blowup morphism of the ideal sheaf cut out by `I`. For `n = 1`
this is an effective Cartier divisor, by
`Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec_ofIdealTop`. -/
abbrev thickeningIdeal (n : ℕ) : (blowupScheme I).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
      (Stacks.Blowup.toSpec I) ^ n

/-- **The structure sheaf `𝒪_{Yₙ}` of the thickening**, read as a sheaf of `𝒪_X`-modules: the
direct image of the structure sheaf of the closed subscheme `Yₙ ⊆ X`. -/
abbrev thickeningSheaf (n : ℕ) : (blowupScheme I).Modules :=
  (Scheme.Modules.pushforward (thickeningIdeal I n).subschemeι).obj (SheafOfModules.unit _)

/-- **The canonical surjection `𝒪_X ⟶ 𝒪_{Yₙ}`** onto the structure sheaf of the thickening. -/
abbrev thickeningProj (n : ℕ) :
    SheafOfModules.unit (blowupScheme I).ringCatSheaf ⟶ thickeningSheaf I n :=
  SheafOfModules.unitToPushforwardObjUnit (thickeningIdeal I n).subschemeι.toRingCatSheafHom

/-- **`𝒪_X ⟶ 𝒪_{Yₙ}` is an epimorphism**, so `𝒪_{Yₙ}` is a quotient of `𝒪_X` and not merely a
sheaf receiving a map from it. `Yₙ` is a closed subscheme of `X`, and for a closed immersion the
comorphism is surjective ([Stacks, Tag 01QO]); the spelling the ideal sequence of [Stacks,
Tag 0C6K] uses for that arrow is the one here on the nose, by
`Stacks.IdealSheafSequence.divisorQuotientMap_eq`.

Together with `Stacks.IdealSheafSequence.divisorIdeal_shortExact` at `thickeningIdeal I n` this
identifies `𝒪_{Yₙ}` with `𝒪_X/ℐ_{Yₙ}` *globally*, which is the identification the exactness
fields of `GeometricInput` were recorded as needing; the module docstring's obstruction register
says what is actually left once it is in hand. -/
instance epi_thickeningProj (n : ℕ) : Epi (thickeningProj I n) :=
  Stacks.IdealSheafSequence.epi_divisorQuotientMap (thickeningIdeal I n)

/-- **`I` kills `𝒪_{Y₁}`**: the global section of `𝒪_X` obtained by pulling back an element of
`I` along the blowup morphism is zero on the exceptional divisor.

This is the *ideal-sheaf* half of the comparison that the complex condition needs. The
exceptional divisor
is cut out by the inverse image of `I`, so this is
`app_top_unitToPushforwardObjUnit_eq_zero_of_comap` at `J = ` the ideal sheaf of `Spec(A)`
attached to `I`, the first thickening being a first power. -/
theorem app_top_thickeningProj_one_eq_zero {b : A} (hb : b ∈ I) :
    (thickeningProj I 1).val.app (op ⊤)
        ((Stacks.Blowup.toSpec I).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) = 0 :=
  app_top_unitToPushforwardObjUnit_eq_zero_of_comap (Stacks.Blowup.toSpec I)
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I))
    (thickeningIdeal I 1) (pow_one _) _
    (by simpa using Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hb)

/-- **The direct image of the unit transported along a factorisation `f ≫ g = g'`**: the direct
image under `g` of the unit maps to the direct image under `g'` of the unit, by pushing the
canonical `𝒪_Z ⟶ f_* 𝒪_Y` forward along `g`.

The factorisation is taken as a hypothesis rather than by writing `f ≫ g`, so that `subst`
removes the transport in every proof about this map. -/
def pushforwardUnitRestrict {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W) (g' : Y ⟶ W)
    (hg : f ≫ g = g') :
    (Scheme.Modules.pushforward g).obj (SheafOfModules.unit _) ⟶
      (Scheme.Modules.pushforward g').obj (SheafOfModules.unit _) :=
  hg ▸ ((Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app _)

/-- The canonical maps out of the structure sheaf of the ambient scheme are compatible with
`pushforwardUnitRestrict`: `𝒪_W ⟶ g_* 𝒪_Z ⟶ g'_* 𝒪_Y` is `𝒪_W ⟶ g'_* 𝒪_Y`. -/
theorem unitToPushforwardObjUnit_comp_pushforwardUnitRestrict
    {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W) (g' : Y ⟶ W) (hg : f ≫ g = g') :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        pushforwardUnitRestrict f g g' hg =
      SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom := by
  subst hg
  exact (SheafOfModules.hom_ext_iff.mpr rfl).symm

/-- `Yₙ ⊆ Yₘ` for `n ≤ m`: the ideal cutting out the larger thickening is the smaller ideal. -/
theorem thickeningIdeal_le {n m : ℕ} (h : n ≤ m) : thickeningIdeal I m ≤ thickeningIdeal I n :=
  pow_le_pow_right_of_le_one' (fun _ ⦃_⦄ _ ↦ trivial) h

/-- **The canonical surjection `𝒪_{Yₘ} ⟶ 𝒪_{Yₙ}`** for `n ≤ m`, the direct image of the
structure-sheaf map of the closed immersion `Yₙ ↪ Yₘ`. For `n = 1` this is the restriction of
`𝒪_{Yₘ}` to the exceptional divisor, the second map of the sequence
`0 → 𝒪_{Yₘ₋₁}(q+1) → 𝒪_{Yₘ}(q) → 𝒪_Y(q) → 0` of the proof of Tag 0GA7. -/
def thickeningRestrict {n m : ℕ} (h : n ≤ m) : thickeningSheaf I m ⟶ thickeningSheaf I n :=
  pushforwardUnitRestrict (Scheme.IdealSheafData.inclusion (thickeningIdeal_le I h))
    (thickeningIdeal I m).subschemeι (thickeningIdeal I n).subschemeι
    (Scheme.IdealSheafData.inclusion_subschemeι _)

/-- The canonical surjections onto the thickenings are compatible: `𝒪_X ⟶ 𝒪_{Yₘ} ⟶ 𝒪_{Yₙ}` is
`𝒪_X ⟶ 𝒪_{Yₙ}`. -/
theorem thickeningProj_comp_thickeningRestrict {n m : ℕ} (h : n ≤ m) :
    thickeningProj I m ≫ thickeningRestrict I h = thickeningProj I n :=
  unitToPushforwardObjUnit_comp_pushforwardUnitRestrict _ _ _ _

/-- **The twist `𝒪_{Yₙ}(q) = 𝒪_{Yₙ} ⊗_{𝒪_X} 𝒪_X(q)`.** -/
abbrev thickeningTwist (n q : ℕ) : (blowupScheme I).Modules :=
  thickeningSheaf I n ⊗ blowupTwist I q

/-- **The canonical map `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)`**: the surjection `𝒪_X ⟶ 𝒪_{Yₙ}` tensored with
`𝒪_X(q)`, read through the left unitor of the sheafified tensor product. -/
abbrev thickeningTwistProj (n q : ℕ) : blowupTwist I q ⟶ thickeningTwist I n q :=
  (λ_ (blowupTwist I q)).inv ≫ (thickeningProj I n ▷ blowupTwist I q)

/-- **The canonical map `𝒪_{Yₘ}(q) ⟶ 𝒪_{Yₙ}(q)`** for `n ≤ m`: the surjection
`𝒪_{Yₘ} ⟶ 𝒪_{Yₙ}` tensored with `𝒪_X(q)`. At `n = 1` this is the second map of the sequence
`0 → 𝒪_{Yₘ₋₁}(q+1) → 𝒪_{Yₘ}(q) → 𝒪_Y(q) → 0` used in the proof of Tag 0GA7. -/
abbrev thickeningTwistRestrict {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    thickeningTwist I m q ⟶ thickeningTwist I n q :=
  thickeningRestrict I h ▷ blowupTwist I q

/-- The canonical maps `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)` are compatible with the restrictions between
thickenings. -/
theorem thickeningTwistProj_comp_thickeningTwistRestrict {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    thickeningTwistProj I m q ≫ thickeningTwistRestrict I h q = thickeningTwistProj I n q :=
  (comp_whiskerRight_comp _ _ _).trans
    (congrArg (fun φ : SheafOfModules.unit (blowupScheme I).ringCatSheaf ⟶ thickeningSheaf I n =>
        (λ_ (blowupTwist I q)).inv ≫ φ ▷ blowupTwist I q)
      (thickeningProj_comp_thickeningRestrict I h))

/-- **The interchange identity of the second sequence of Tag 0GA7.** The composite
`𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q)` equals the restriction to the exceptional divisor in degree `q+1`
followed by `𝒪_Y ⊗ -` applied to the first map.

It would reduce the complex condition to the vanishing of
`thickeningSheaf I 1 ◁ ambientTwistMap I q`, which is strictly stronger and open; that is not
how `ambientTwistMap_comp_thickeningTwistProj_eq_zero` is proved, and the obstruction register
above says why. -/
theorem ambientTwistMap_comp_thickeningTwistProj (q : ℕ) :
    ambientTwistMap I q ≫ thickeningTwistProj I 1 q =
      thickeningTwistProj I 1 (q + 1) ≫ (thickeningSheaf I 1 ◁ ambientTwistMap I q) :=
  comp_leftUnitor_inv_whiskerRight (thickeningProj I 1) (ambientTwistMap I q)

end Objects

end Stacks.LocalCohomology.UniformityIII

end
