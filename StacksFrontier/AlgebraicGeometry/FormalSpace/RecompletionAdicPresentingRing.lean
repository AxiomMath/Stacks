module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# Quotients of an adic completion by the stage ideals of a presentation

Let `A` be a ring, `J ⊆ A` an ideal and `L ⊆ A` an ideal containing a power of `J`. The `J`-adic
completion `A^∧` of `A`, with the inverse-limit topology of its truncations, then surjects onto
`A ⧸ L` through the truncation `A ⧸ J ^ p` at any `p` with `J ^ p ≤ L`; and when moreover
`L ⊆ √J` — and `J` is finitely generated — the kernel of that surjection is a *weak ideal of
definition* of `A^∧`, while `L ≤ J ^ q` forces that kernel inside the kernel of the `q`-th
truncation.

These are the ring-level facts behind the presentation of the completion `X_{/T}` of an adic\*
affine formal algebraic space: the stages of a presentation of `X_{/T}` are the spectra of the
quotients `A ⧸ L` of the presenting ring `A` of `X` by the ideals `L` cut out by those stages,
the two displayed conditions on `L` are what the geometry supplies, and together they are
exactly the data of an `AlgebraicGeometry.FormalSpace.DirectedQuotients` for `A^∧`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.adicCompletionProj`: the surjection `A^∧ ⟶ A ⧸ L` attached to
  an inclusion `J ^ p ≤ L`.
* `AlgebraicGeometry.FormalSpace.pointRingMap` and
  `AlgebraicGeometry.FormalSpace.stageIdeal`: the ring map `A ⟶ Γ(T, 𝒪)` attached to a
  `T`-point of a sheaf presented by `A`, and its kernel — the ideal of `A` cut out by that
  point.

## Main results

* `AlgebraicGeometry.FormalSpace.surjective_adicCompletionProj`: it is surjective.
* `AlgebraicGeometry.FormalSpace.adicCompletionProj_comp_factor`: the surjections attached to
  `J ^ p ≤ L` and `J ^ p' ≤ L'` for `L ≤ L'` are compatible with the transition `A ⧸ L ⟶ A ⧸ L'`,
  which is what makes them a compatible family over a presentation.
* `AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_ker_adicCompletionProj`: for a finitely
  generated `J` and `L ⊆ √J` the kernel is a weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.ker_adicCompletionProj_le_adicCompletionKernel`: for `L ≤ J ^ q`
  the kernel lies inside the kernel of the `q`-th truncation, so that such kernels are a
  fundamental system of neighbourhoods of zero as soon as the `L` are cofinal among the powers
  of `J`.
* `AlgebraicGeometry.FormalSpace.stageIdeal_le_comp` and
  `AlgebraicGeometry.FormalSpace.stageIdeal_comp_le_radical`: a point factoring through another
  cuts out a larger ideal, and one inside the radical of the other's when the factorisation is
  a thickening; `AlgebraicGeometry.FormalSpace.surjective_pointRingMap`: for a closed immersion
  of an affine scheme of the site the ring map is surjective, so the point cuts its target out
  of `Spec A`.
* `AlgebraicGeometry.FormalSpace.le_radical_of_directed_of_le`: in a directed family of ideals
  with those two properties, one member inside `J` puts every member inside `√J`.
* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso_of_stageIdeal`: **a
  closed-immersed subsheaf whose stage ideals have radical `√J` is the formal spectrum of the
  `J`-adic completion of `A`**. This is the assembly: the two displayed conditions on the stage
  ideals are turned into a `AlgebraicGeometry.FormalSpace.DirectedQuotients` and fed to Stacks
  0AIC (4) ⇒ (1).

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {A : Type u} [CommRing A]

/-- The surjection of the `J`-adic completion of `A` onto `A ⧸ L` attached to an inclusion
`J ^ p ≤ L`: the `p`-th truncation `A^∧ ⟶ A ⧸ J ^ p` followed by the quotient map. -/
def adicCompletionProj (J : Ideal A) {L : Ideal A} {p : ℕ} (h : J ^ p ≤ L) :
    AdicCompletion J A →+* A ⧸ L :=
  (Ideal.Quotient.factor h).comp (AdicCompletion.evalₐ J p).toRingHom

/-- The map `A^∧ ⟶ A ⧸ L` sends `x` to the image in `A ⧸ L` of its level-`p` component. -/
theorem adicCompletionProj_apply (J : Ideal A) {L : Ideal A} {p : ℕ} (h : J ^ p ≤ L)
    (x : AdicCompletion J A) :
    adicCompletionProj J h x = Ideal.Quotient.factor h (AdicCompletion.evalₐ J p x) := rfl

/-- The surjection of `A^∧` onto `A ⧸ L` restricts along `A ⟶ A^∧` to the quotient map. -/
theorem adicCompletionProj_algebraMap (J : Ideal A) {L : Ideal A} {p : ℕ} (h : J ^ p ≤ L)
    (a : A) :
    adicCompletionProj J h (algebraMap A (AdicCompletion J A) a) = Ideal.Quotient.mk L a := by
  rw [adicCompletionProj_apply, AlgHom.commutes]
  rfl

/-- The map `A^∧ ⟶ A ⧸ L` is surjective, because `A ⟶ A ⧸ L` is and factors through it. -/
theorem surjective_adicCompletionProj (J : Ideal A) {L : Ideal A} {p : ℕ} (h : J ^ p ≤ L) :
    Function.Surjective (adicCompletionProj J h) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap A (AdicCompletion J A) a, adicCompletionProj_algebraMap J h a⟩

/-- A representative of the level-`n` component of `x` is one of its level-`m` component for
`m ≤ n`. -/
private theorem evalₐ_eq_mk_of_le (J : Ideal A) {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion J A)
    {c : A} (hc : AdicCompletion.evalₐ J n x = Ideal.Quotient.mk (J ^ n) c) :
    AdicCompletion.evalₐ J m x = Ideal.Quotient.mk (J ^ m) c := by
  rw [← AdicCompletion.factorPow_evalₐ J hmn x, hc]
  simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The surjections onto `A ⧸ L` and onto `A ⧸ L'` for `L ≤ L'` are compatible with the
transition map: both are the quotient map on the image of `A`, which is dense in the sense that
`A ⟶ A ⧸ L'` is already surjective. -/
theorem adicCompletionProj_comp_factor (J : Ideal A) {L L' : Ideal A} {p p' : ℕ}
    (h : J ^ p ≤ L) (h' : J ^ p' ≤ L') (hLL' : L ≤ L') :
    (Ideal.Quotient.factor hLL').comp (adicCompletionProj J h) = adicCompletionProj J h' := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J (max p p') x)
  have hp := evalₐ_eq_mk_of_le J (le_max_left p p') x hc.symm
  have hp' := evalₐ_eq_mk_of_le J (le_max_right p p') x hc.symm
  show Ideal.Quotient.factor hLL' (adicCompletionProj J h x) = adicCompletionProj J h' x
  rw [adicCompletionProj_apply, adicCompletionProj_apply, hp, hp']
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

/-- An element of `A^∧` killed by the map to `A ⧸ L` has, at every truncation, a representative
in `L`: the representative at a level above `p` already lies in `L`, and the lower levels are
read off from it. -/
theorem exists_mem_of_mem_ker_adicCompletionProj (J : Ideal A) {L : Ideal A} {p : ℕ}
    (h : J ^ p ≤ L) {x : AdicCompletion J A} (hx : x ∈ RingHom.ker (adicCompletionProj J h))
    (m : ℕ) : ∃ c ∈ L, AdicCompletion.evalₐ J m x = Ideal.Quotient.mk (J ^ m) c := by
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J (max m p) x)
  have hp := evalₐ_eq_mk_of_le J (le_max_right m p) x hc.symm
  rw [RingHom.mem_ker, adicCompletionProj_apply, hp, Ideal.Quotient.factor_mk] at hx
  exact ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp hx,
    evalₐ_eq_mk_of_le J (le_max_left m p) x hc.symm⟩

/-- The kernel of the `p`-th truncation is inside the kernel of the map to `A ⧸ L`. -/
theorem adicCompletionKernel_le_ker_adicCompletionProj (J : Ideal A) {L : Ideal A} {p : ℕ}
    (h : J ^ p ≤ L) :
    adicCompletionKernel J p ≤ RingHom.ker (adicCompletionProj J h) := by
  intro x hx
  rw [RingHom.mem_ker, adicCompletionProj_apply]
  rw [adicCompletionKernel, RingHom.mem_ker] at hx
  change AdicCompletion.evalₐ J p x = 0 at hx
  rw [hx, map_zero]

/-- If `L ≤ J ^ q` then the kernel of the map to `A ⧸ L` is inside the kernel of the `q`-th
truncation: a representative in `L` of a level-`m` component is a representative in `J ^ q`. -/
theorem ker_adicCompletionProj_le_adicCompletionKernel (J : Ideal A) {L : Ideal A} {p q : ℕ}
    (h : J ^ p ≤ L) (hq : L ≤ J ^ q) :
    RingHom.ker (adicCompletionProj J h) ≤ adicCompletionKernel J q := by
  intro x hx
  obtain ⟨c, hcL, hc⟩ := exists_mem_of_mem_ker_adicCompletionProj J h hx q
  rw [adicCompletionKernel, RingHom.mem_ker]
  show AdicCompletion.evalₐ J q x = 0
  rw [hc]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hq hcL)

/-- The `n`-th power of the extension of `J` to `A^∧` is the kernel of the `n`-th truncation. -/
private theorem map_algebraMap_pow_eq_adicCompletionKernel (J : Ideal A) (hJ : J.FG) (n : ℕ) :
    ((Ideal.map (algebraMap A (AdicCompletion J A)) J) ^ n : Ideal (AdicCompletion J A)) =
      adicCompletionKernel J n := by
  rw [← Ideal.map_pow]
  exact map_pow_eq_adicCompletionKernel J hJ n

/-- The kernel of the `n`-th truncation of `A^∧` is open in the inverse-limit topology. -/
private theorem isOpen_adicCompletionKernel (J : Ideal A) (hJ : J.FG) (n : ℕ) :
    letI : TopologicalSpace (AdicCompletion J A) := adicCompletionLimitTopology A J
    IsOpen (adicCompletionKernel J n : Set (AdicCompletion J A)) := by
  let : TopologicalSpace (AdicCompletion J A) := adicCompletionLimitTopology A J
  let := isTopologicalRing_adicCompletion A J
  rw [← map_algebraMap_pow_eq_adicCompletionKernel J hJ n]
  exact (isAdic_iff.mp (isAdic_map_adicCompletion J hJ)).1 n

/-- **The kernel of `A^∧ ⟶ A ⧸ L` is a weak ideal of definition** when `J` is finitely generated
and `L ⊆ √J`: it is open, containing the kernel of the `p`-th truncation, and each of its
elements is topologically nilpotent, a representative in `L` of its level-`m` component having a
power in `J ^ m`. -/
theorem isWeakIdealOfDefinition_ker_adicCompletionProj (J : Ideal A) (hJ : J.FG) {L : Ideal A}
    {p : ℕ} (h : J ^ p ≤ L) (hrad : L ≤ J.radical) :
    letI : TopologicalSpace (AdicCompletion J A) := adicCompletionLimitTopology A J
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (adicCompletionProj J h)) := by
  let : TopologicalSpace (AdicCompletion J A) := adicCompletionLimitTopology A J
  let := isTopologicalRing_adicCompletion A J
  have hdef := isIdealOfDefinition_map_adicCompletion J hJ
  refine ⟨?_, fun x hx ↦ ?_⟩
  · exact Submodule.isOpen_mono (adicCompletionKernel_le_ker_adicCompletionProj J h)
      (isOpen_adicCompletionKernel J hJ p)
  · rw [IsTopologicallyNilpotent, Filter.tendsto_def]
    intro U hU
    obtain ⟨m, hm⟩ := hdef.2 U hU
    rw [map_algebraMap_pow_eq_adicCompletionKernel J hJ m] at hm
    obtain ⟨c, hcL, hc⟩ := exists_mem_of_mem_ker_adicCompletionProj J h hx m
    obtain ⟨e, he⟩ := hrad hcL
    have hmem : ∀ n : ℕ, e * m ≤ n → x ^ n ∈ adicCompletionKernel J m := by
      intro n hn
      have hcn : c ^ n ∈ J ^ m := by
        rw [← Nat.add_sub_of_le hn, pow_add, pow_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow he m)
      rw [adicCompletionKernel, RingHom.mem_ker]
      show AdicCompletion.evalₐ J m (x ^ n) = 0
      rw [map_pow, hc, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcn
    filter_upwards [Filter.eventually_atTop.2 ⟨e * m, fun n hn ↦ hm (hmem n hn)⟩] with n hn
    exact hn

/-! ### The same through an arbitrary quotient of `A` -/

/-- The map of the `J`-adic completion of `A` into a quotient `R` of `A` by an ideal containing
`J ^ p`, read through the `p`-th truncation. This is
`AlgebraicGeometry.FormalSpace.adicCompletionProj` composed with the identification
`A ⧸ ker σ ≃ R`, in the form in which the stage rings of a presentation present themselves. -/
def adicCompletionProjOfSurj {R : Type u} [CommRing R] (J : Ideal A) (σ : A →+* R) {p : ℕ}
    (h : J ^ p ≤ RingHom.ker σ) : AdicCompletion J A →+* R :=
  (Ideal.Quotient.lift (J ^ p) σ h).comp (AdicCompletion.evalₐ J p).toRingHom

/-- The map `A^∧ ⟶ R` restricts along `A ⟶ A^∧` to `σ`. -/
theorem adicCompletionProjOfSurj_algebraMap {R : Type u} [CommRing R] (J : Ideal A) (σ : A →+* R)
    {p : ℕ} (h : J ^ p ≤ RingHom.ker σ) (a : A) :
    adicCompletionProjOfSurj J σ h (algebraMap A (AdicCompletion J A) a) = σ a := by
  show Ideal.Quotient.lift (J ^ p) σ h
    (AdicCompletion.evalₐ J p (algebraMap A (AdicCompletion J A) a)) = σ a
  rw [AlgHom.commutes]
  rfl

/-- The map into a quotient of `A` is surjective. -/
theorem surjective_adicCompletionProjOfSurj {R : Type u} [CommRing R] (J : Ideal A)
    (σ : A →+* R) {p : ℕ} (h : J ^ p ≤ RingHom.ker σ) (hσ : Function.Surjective σ) :
    Function.Surjective (adicCompletionProjOfSurj J σ h) := by
  intro y
  obtain ⟨a, rfl⟩ := hσ y
  exact ⟨algebraMap A (AdicCompletion J A) a, adicCompletionProjOfSurj_algebraMap J σ h a⟩

/-- Its kernel is the kernel of the map to `A ⧸ ker σ`, so the statements about the latter apply
to it. -/
theorem ker_adicCompletionProjOfSurj {R : Type u} [CommRing R] (J : Ideal A) (σ : A →+* R)
    {p : ℕ} (h : J ^ p ≤ RingHom.ker σ) :
    RingHom.ker (adicCompletionProjOfSurj J σ h) = RingHom.ker (adicCompletionProj J h) := by
  ext x
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J p x)
  have h1 : adicCompletionProjOfSurj J σ h x = σ c := by
    show Ideal.Quotient.lift (J ^ p) σ h (AdicCompletion.evalₐ J p x) = σ c
    rw [← hc]
    rfl
  have h2 : adicCompletionProj J h x = Ideal.Quotient.mk (RingHom.ker σ) c := by
    rw [adicCompletionProj_apply, ← hc, Ideal.Quotient.factor_mk]
  rw [RingHom.mem_ker, RingHom.mem_ker, h1, h2, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]

/-- The maps into two quotients of `A` are compatible with a map of the quotients over `A`: they
agree on the image of `A`, and both factor through a common truncation of `A`. -/
theorem adicCompletionProjOfSurj_comp {R R' : Type u} [CommRing R] [CommRing R'] (J : Ideal A)
    (σ : A →+* R) (σ' : A →+* R') (τ : R →+* R') {p p' : ℕ}
    (h : J ^ p ≤ RingHom.ker σ) (h' : J ^ p' ≤ RingHom.ker σ') (hτ : τ.comp σ = σ') :
    τ.comp (adicCompletionProjOfSurj J σ h) = adicCompletionProjOfSurj J σ' h' := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J (max p p') x)
  have hp := evalₐ_eq_mk_of_le J (le_max_left p p') x hc.symm
  have hp' := evalₐ_eq_mk_of_le J (le_max_right p p') x hc.symm
  have h1 : adicCompletionProjOfSurj J σ h x = σ c := by
    show Ideal.Quotient.lift (J ^ p) σ h (AdicCompletion.evalₐ J p x) = σ c
    rw [hp]
    rfl
  have h2 : adicCompletionProjOfSurj J σ' h' x = σ' c := by
    show Ideal.Quotient.lift (J ^ p') σ' h' (AdicCompletion.evalₐ J p' x) = σ' c
    rw [hp']
    rfl
  show τ (adicCompletionProjOfSurj J σ h x) = adicCompletionProjOfSurj J σ' h' x
  rw [h1, h2, ← hτ]
  rfl

/-! ### Directed families of stage ideals -/

/-- **One small stage ideal makes them all small.** Let `L` be a directed family of ideals of
`A` which decreases along the order and in which every member lies in the radical of every
smaller one — the family of ideals cut out by the stages of a presentation by affine
thickenings, by `AlgebraicGeometry.FormalSpace.stageIdeal_le_comp` and
`AlgebraicGeometry.FormalSpace.stageIdeal_comp_le_radical`. If one member is contained in `J`,
every member is contained in `√J`.

This is how the hypothesis `L_k ≤ √J` of
`AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_ker_adicCompletionProj` is met for every
stage of a presentation of a completion once a single stage is known to lie inside `J`. -/
theorem le_radical_of_directed_of_le {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (L : ι → Ideal A) (hmono : ∀ {i j : ι}, i ≤ j → L j ≤ L i)
    (hrad : ∀ {i j : ι}, i ≤ j → L i ≤ (L j).radical) {J : Ideal A} {i₀ : ι} (h₀ : L i₀ ≤ J)
    (i : ι) : L i ≤ J.radical := by
  obtain ⟨j, hij, hi₀j⟩ := directed_of (· ≤ ·) i i₀
  exact (hrad hij).trans (Ideal.radical_mono ((hmono hi₀j).trans h₀))

/-! ### The ideal of `A` cut out by a point of `X` -/

section Stages

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  {X : FppfSheaf B S hS} (P : WeakIdealColimitPresentation B S hS A X)

/-- The ring map `A ⟶ Γ(T, 𝒪)` attached to a `T`-point of `X`, for `T` an object of the site:
the global morphism `X ⟶ Spec A` of condition (2) of Stacks 0AIC, read on global sections. -/
def pointRingMap (T : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) :
    A →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app T g).appTop).hom

/-- The ideal of `A` cut out by a `T`-point of `X`: the kernel of the ring map it induces. For a
closed immersion of an affine scheme of the site into `X` this is the ideal of that closed
subscheme of `Spec A`. -/
def stageIdeal (T : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) : Ideal A :=
  RingHom.ker (pointRingMap B S hS A P T g)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The ring map attached to a point is natural in the object of the site. -/
theorem pointRingMap_comp {T' T : BigFppfOver B S hS} (b : T' ⟶ T)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) (a : A) :
    pointRingMap B S hS A P T'
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ g) a =
      (((BigFppfOver.toScheme B S hS).map b).appTop).hom
        (pointRingMap B S hS A P T g a) := by
  have h := (mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app_naturality T T' b g
  show (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app T'
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ g)).appTop).hom) a = _
  rw [h, Scheme.Hom.comp_appTop]
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A point factoring through another cuts out a larger ideal. -/
theorem stageIdeal_le_comp {T' T : BigFppfOver B S hS} (b : T' ⟶ T)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) :
    stageIdeal B S hS A P T g ≤ stageIdeal B S hS A P T'
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ g) := by
  intro x hx
  rw [stageIdeal, RingHom.mem_ker] at hx ⊢
  rw [pointRingMap_comp B S hS A P b g x, hx, map_zero]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A point factoring through another by a *thickening* cuts out an ideal inside the radical of
the other's: the kernel of a thickening on global sections is locally nilpotent. -/
theorem stageIdeal_comp_le_radical {T' T : BigFppfOver B S hS} (b : T' ⟶ T)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)]
    (hb : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map b))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) :
    stageIdeal B S hS A P T'
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ g) ≤
      (stageIdeal B S hS A P T g).radical := by
  intro x hx
  rw [stageIdeal, RingHom.mem_ker, pointRingMap_comp B S hS A P b g x] at hx
  obtain ⟨n, hn⟩ := locallyNilpotent_ker_appTop_of_isThickening hb _ (RingHom.mem_ker.mpr hx)
  exact ⟨n, by rwa [stageIdeal, RingHom.mem_ker, map_pow]⟩

/-- For a closed immersion of an affine scheme of the site into `X`, the ring map `A ⟶ Γ(T, 𝒪)`
is surjective, so that `T` is the closed subscheme of `Spec A` cut out by
`AlgebraicGeometry.FormalSpace.stageIdeal`. -/
theorem surjective_pointRingMap (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hset : SatisfiesSetTheoreticCondition B S hS X) (T : BigAffineFppf B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X)
    (hg : IsClosedImmersionInto B S hS g) :
    Function.Surjective
      (pointRingMap B S hS A P ((BigAffineFppf.inclusion B S hS).obj T) g) := by
  have hci : IsClosedImmersion ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app
      ((BigAffineFppf.inclusion B S hS).obj T) g) :=
    isClosedImmersion_app_mapToSchemeOfWeakIdealColimitPresentation B S hS A hA hset P T g hg
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app
      ((BigAffineFppf.inclusion B S hS).obj T) g)).2
  intro y
  obtain ⟨z, hz⟩ := hsurj y
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom z, ?_⟩
  show (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ _).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom z) = y
  rw [CommRingCat.comp_apply]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom z) = z from by
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom z = z
    rw [Iso.hom_inv_id]
    rfl]
  exact hz

end Stages

/-! ### The presenting ring of a subsheaf whose stage ideals have radical `√J` -/

section Assembly

attribute [local instance] sheaf_hasColimits

/-- **The adic completion presents a closed-immersed subsheaf whose stage ideals have radical
`√J`.** Let `A` be a weakly admissible topological ring presenting `X`, let `Z` be an affine
formal algebraic space with a morphism `w : Z ⟶ X` along which closed immersions of affine
schemes of the site into `Z` stay closed immersions into `X`, and let `J ⊆ A` be a finitely
generated ideal such that

* every affine scheme of the site closed-immersed in `Z` cuts out an ideal of `A` whose radical
  contains `J`, and
* for every `t` some affine scheme of the site closed-immersed in `Z` cuts out an ideal inside
  `J ^ t`.

Then `Z` is the formal spectrum of the `J`-adic completion of `A`.

The two hypotheses say that the ideals cut out by the stages of a presentation of `Z` have
radical exactly `√J` and are cofinal among the powers of `J`; by
`AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_ker_adicCompletionProj` and
`AlgebraicGeometry.FormalSpace.ker_adicCompletionProj_le_adicCompletionKernel` that is exactly
an `AlgebraicGeometry.FormalSpace.DirectedQuotients` for `A^∧`, and Stacks 0AIC (4) ⇒ (1) turns
it into the formal spectrum. -/
theorem exists_quotientSystem_formalSpectrum_iso_of_stageIdeal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X)
    {Z : FppfSheaf B S hS} (hZ : IsAffineFormalAlgebraicSpace B S hS Z) (w : Z ⟶ X)
    (hw : ∀ (T : BigFppfOver B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Z),
      IsClosedImmersionInto B S hS c → IsClosedImmersionInto B S hS (c ≫ w))
    (J : Ideal A) (hJ : J.FG)
    (hbig : ∀ (T : BigAffineFppf B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Z),
      IsClosedImmersionInto B S hS c →
      J ≤ (stageIdeal B S hS A P ((BigAffineFppf.inclusion B S hS).obj T) (c ≫ w)).radical)
    (hsmall : ∀ t : ℕ, ∃ (T : BigAffineFppf B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Z),
      IsClosedImmersionInto B S hS c ∧
        stageIdeal B S hS A P ((BigAffineFppf.inclusion B S hS).obj T) (c ≫ w) ≤ J ^ t) :
    ∃ D : @QuotientSystem B S hS (AdicCompletion J A) _ (adicCompletionLimitTopology A J),
      Nonempty (Z ≅ @formalSpectrum B S hS (AdicCompletion J A) _
        (adicCompletionLimitTopology A J) D) := by
  classical
  let : TopologicalSpace (AdicCompletion J A) := adicCompletionLimitTopology A J
  let := isTopologicalRing_adicCompletion A J
  let := isLinearTopology_adicCompletion A J
  obtain ⟨-, K, pre, hne, hdir, F, hFth, ⟨eZ⟩⟩ := id hZ
  let : Preorder K := pre
  let : Nonempty K := hne
  let : IsDirected K (· ≤ ·) := hdir
  set G := F ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  -- the stage morphisms into `Z`, closed immersions into `Z` and hence into `X`
  let cZ : ∀ k : K, G.obj k ⟶ Z := fun k ↦ colimit.ι G k ≫ eZ.inv
  have hcZ : ∀ k : K, IsClosedImmersionInto B S hS (cZ k) := fun k ↦
    isClosedImmersionInto_colimitι B S hS F hFth Z eZ.symm k
  have hcX : ∀ k : K, IsClosedImmersionInto B S hS (cZ k ≫ w) := fun k ↦
    hw _ (cZ k) (hcZ k)
  -- the ring maps and the ideals they cut out
  let ρ : ∀ k : K, A →+*
      Γ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (F.obj k)), ⊤) :=
    fun k ↦ pointRingMap B S hS A P _ (cZ k ≫ w)
  have hρsurj : ∀ k : K, Function.Surjective (ρ k) := fun k ↦
    surjective_pointRingMap B S hS A P hA hset (F.obj k) _ (hcX k)
  -- the stage morphisms factor one through the other along the transitions
  have hfac : ∀ {i j : K} (f : i ⟶ j),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (F.map f)) ≫ cZ j = cZ i := fun f ↦
    colimit.w_assoc G f eZ.inv
  have hρcomp : ∀ {i j : K} (f : i ⟶ j),
      (((BigAffineFppf.toScheme B S hS).map (F.map f)).appTop).hom.comp (ρ j) = ρ i := by
    intro i j f
    refine RingHom.ext fun a ↦ ?_
    have h := pointRingMap_comp B S hS A P ((BigAffineFppf.inclusion B S hS).map (F.map f))
      (cZ j ≫ w) a
    rw [← Category.assoc, hfac f] at h
    exact h.symm
  have hLmono : ∀ {i j : K}, i ≤ j → RingHom.ker (ρ j) ≤ RingHom.ker (ρ i) := by
    intro i j hij
    have h := stageIdeal_le_comp B S hS A P ((BigAffineFppf.inclusion B S hS).map
      (F.map (homOfLE hij))) (cZ j ≫ w)
    rwa [← Category.assoc, hfac (homOfLE hij)] at h
  have hLrad : ∀ {i j : K}, i ≤ j → RingHom.ker (ρ i) ≤ (RingHom.ker (ρ j)).radical := by
    intro i j hij
    let : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (F.obj j))) := (F.obj j).property
    have h := stageIdeal_comp_le_radical B S hS A P ((BigAffineFppf.inclusion B S hS).map
      (F.map (homOfLE hij))) (hFth (homOfLE hij)) (cZ j ≫ w)
    rwa [← Category.assoc, hfac (homOfLE hij)] at h
  -- the stage ideals are cofinal among the powers of `J`
  have hsmallk : ∀ t : ℕ, ∃ k : K, RingHom.ker (ρ k) ≤ J ^ t := by
    intro t
    obtain ⟨T, c, hc, hle⟩ := hsmall t
    obtain ⟨k, h, -, hkfac⟩ :=
      exists_stage_isClosedImmersion_of_isClosedImmersionInto B S hS F hFth eZ c hc
    have h2 := stageIdeal_le_comp B S hS A P h (cZ k ≫ w)
    rw [← Category.assoc, show (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h ≫
      cZ k = c from hkfac] at h2
    exact ⟨k, h2.trans hle⟩
  -- and every one of them has `J` inside its radical
  have hJrad : ∀ k : K, J ≤ (RingHom.ker (ρ k)).radical := fun k ↦ hbig (F.obj k) (cZ k) (hcZ k)
  have hpow : ∀ k : K, ∃ n : ℕ, J ^ n ≤ RingHom.ker (ρ k) := fun k ↦
    Ideal.exists_pow_le_of_le_radical_of_fg (hJrad k) hJ
  choose pn hpn using hpow
  have hLJ : ∀ k : K, RingHom.ker (ρ k) ≤ J.radical := by
    intro k
    obtain ⟨k₀, hk₀⟩ := hsmallk 1
    rw [pow_one] at hk₀
    exact le_radical_of_directed_of_le (fun k ↦ RingHom.ker (ρ k)) hLmono hLrad hk₀ k
  -- the presentation of `Z` by the quotients of the `J`-adic completion of `A`
  refine (DirectedQuotients.exists_quotientSystem_formalSpectrum_iso
    (P := { diagram := F
            isThickening := hFth
            colimitIso := eZ
            proj := fun k ↦ adicCompletionProjOfSurj J (ρ k) (hpn k)
            proj_surjective := fun k ↦
              surjective_adicCompletionProjOfSurj J (ρ k) (hpn k) (hρsurj k)
            proj_comp := fun {i j} h ↦
              adicCompletionProjOfSurj_comp J (ρ j) (ρ i) _ (hpn j) (hpn i)
                (hρcomp (homOfLE h))
            isWeakIdealOfDefinition_ker := fun k ↦ ?_
            hasBasis_nhds_zero := ?_ }))
  · rw [ker_adicCompletionProjOfSurj]
    exact isWeakIdealOfDefinition_ker_adicCompletionProj J hJ (hpn k) (hLJ k)
  · refine Filter.HasBasis.mk fun U ↦ ⟨fun hU ↦ ?_, ?_⟩
    · obtain ⟨m, hm⟩ := (isIdealOfDefinition_map_adicCompletion J hJ).2 U hU
      rw [map_algebraMap_pow_eq_adicCompletionKernel J hJ m] at hm
      obtain ⟨k, hk⟩ := hsmallk m
      refine ⟨k, trivial, ?_⟩
      refine subset_trans ?_ hm
      intro x hx
      rw [ker_adicCompletionProjOfSurj] at hx
      exact ker_adicCompletionProj_le_adicCompletionKernel J (hpn k) hk hx
    · rintro ⟨k, -, hsub⟩
      refine Filter.mem_of_superset ?_ hsub
      refine Filter.mem_of_superset
        ((isOpen_adicCompletionKernel J hJ (pn k)).mem_nhds (by simp)) ?_
      rw [ker_adicCompletionProjOfSurj]
      exact adicCompletionKernel_le_ker_adicCompletionProj J (hpn k)

end Assembly

end AlgebraicGeometry.FormalSpace
