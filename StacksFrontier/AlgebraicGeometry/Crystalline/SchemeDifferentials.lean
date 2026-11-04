module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SDerivation

/-!
# The sheaf of divided power differentials of a divided power scheme

Let `(T, J, δ)` be a divided power scheme and let `f : T → Y` be a morphism of schemes.  The
*sheaf of divided power differentials* `Ω_{T/Y,δ}` is a sheaf of `𝒪_T`-modules carrying a divided
power derivation `d_{T/Y,δ} : 𝒪_T → Ω_{T/Y,δ}` through which every divided power derivation of
`𝒪_T` over `Y` factors uniquely.  Here a divided power derivation into a sheaf `ℳ` of
`𝒪_T`-modules is, as in `Crystalline.DividedPowerSchemeDerivation`, a map on sections which over
every open `W ⊆ T` lying above an open `V ⊆ Y` is a divided power `Γ(V, 𝒪_Y)`-derivation: it is
additive, satisfies the Leibniz rule, kills every section pulled back from `V`, and obeys the
divided power chain rule `d (δ_n x) = δ_{n-1} x · d x`.

The construction is the sheafification of an explicit presheaf.  Over an open `W` the presheaf
takes the ring-level module of divided power differentials `Ω¹_{Γ(W,𝒪_T) / Γ(Y,𝒪_Y), δ}` of
[Stacks, Tag 07HZ] and divides out the differentials of all sections of `𝒪_T` over `W` that are
pulled back from the base; the restriction maps are induced by the restriction maps of `𝒪_T`,
which are homomorphisms of divided power rings.

## Main definitions

* `Crystalline.dpDifferentials` — the ring-level module `Ω¹_{B/A,δ}` of divided power
  differentials of a morphism `f : A ⟶ B` of commutative rings, with its universal differential
  `Crystalline.dpd`.
* `Crystalline.dpConstDifferentials` — the same module divided by the differentials of a set `S`
  of sections regarded as constants, with its universal differential `Crystalline.dpConstD`.
* `Crystalline.baseSections` — the sections of `𝒪_T` over an open `W` pulled back from the base
  along `f`, from *some* open `V` of `Y` with `W ≤ f⁻¹V`.
* `Crystalline.dpDifferentialsPresheaf` — the presheaf of `𝒪_T`-modules whose sections over `W`
  are `Ω¹_{Γ(W,𝒪_T)/Γ(Y,𝒪_Y),δ}` modulo the differentials of `Crystalline.baseSections`.
* `Crystalline.dpDifferentialsSheaf` — the sheaf `Ω_{T/Y,δ}` of divided power differentials, the
  sheafification of that presheaf.
* `Crystalline.universalDPSchemeDerivation` — the universal divided power derivation
  `d_{T/Y,δ}`, as a `Crystalline.DividedPowerSchemeDerivation` into `Ω_{T/Y,δ}`.

## Main results

* `Crystalline.dpDifferentials_ext`, `Crystalline.dpDesc`,
  `Crystalline.dpConstDifferentials_ext` and `Crystalline.dpConstDesc` — the ring-level universal
  properties: a divided power derivation obeying the chain rule, and killing the chosen
  constants, descends uniquely.
* `Crystalline.dpConstMap` — the map on divided power differentials induced by a commuting square
  whose vertical edge is a homomorphism of divided power rings carrying constants to constants.
* `Crystalline.sheafApp_add`, `sheafApp_mul`, `sheafApp_base`, `sheafApp_dpow` and
  `sheafApp_naturality` — the derivation axioms for `d_{T/Y,δ}` on sections.
* `Crystalline.universalDPSchemeDerivation_isUniversal` — `d_{T/Y,δ}` is universal: every divided
  power derivation of `𝒪_T` over `Y` into a sheaf of `𝒪_T`-modules is obtained from it by a
  unique map of sheaves of modules.

## Implementation notes

The ring-level object of [Stacks, Tag 07HZ] is relative to a *fixed* base ring, so a choice has
to be made for the base of the presheaf.  The base ring used is `Γ(Y, 𝒪_Y)`, the global sections,
which is always available; but fixing `V = ⊤` in the derivation condition would give the wrong
sheaf, because the resulting differential need not kill a section pulled back from a proper open
`V ⊆ Y` (already for `f = 𝟙` on a scheme with nonconstant rational functions the `V = ⊤` object
is nonzero while the correct one vanishes).  The `V` quantifier of
`Crystalline.DividedPowerSchemeDerivation` is therefore honoured by dividing the presheaf, over
each open `W`, by the differentials of *every* section pulled back from *every* open `V` of `Y`
with `W ≤ f⁻¹V`; this is `Crystalline.baseSections`, and the resulting universal differential is
a divided power `Γ(V, 𝒪_Y)`-derivation for each such `V` simultaneously.

The presheaf route was chosen over gluing a quasi-coherent module from affine opens: the
restriction maps and the objectwise universal property come directly from the ring-level
construction, and Mathlib's `PresheafOfModules.sheafificationAdjunction` then supplies both the
sheaf and the universal property, with no affine covering, no base-change comparison and no
quasi-coherence bookkeeping.  Universality is proved by combining the objectwise descent
`Crystalline.dpConstDesc` (whose compatibility with restriction is checked on the universal
differentials, which generate) with the sheafification adjunction.

Everything is built as data: the module and the derivation are explicit quotients and explicit
maps, and the uniqueness statements are proved rather than used to produce the objects.

Two spelling constraints, inherited from the way the structures are bundled, shape the proofs.
First, the module structure on the sections of the presheaf over an open has to be supplied by
name (`Crystalline.presheafObjModule`, `Crystalline.sheafObjModule`), because a presheaf of
modules is indexed by the structure sheaf in its `RingCat`-valued form while the sections of
`𝒪_T` are spelled through `Scheme.presheaf`.  Second, goals mentioning those objects are not
type-correct at `implicit` transparency, so `rw` and `simp` are unusable inside them and the
proofs are written in term mode.

What is *not* built here: the quasi-coherence of `Ω_{T/Y,δ}` and the identification of its
sections over an affine open `W` lying over an affine open `V` with `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`,
which are the two assertions of [Stacks, Tag 07IY]; the de Rham complex built on it; and the
functoriality of `Ω_{T/Y,δ}` in `(T, Y, f)`.  The first two are proved downstream, in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsQuasicoherent.lean`
(`Crystalline.dpDifferentialsSheaf_isQuasicoherent`) and in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffineSections.lean`
(`Crystalline.affineSectionsEquiv`); both of those rest on the presentation of `Ω_{T/Y,δ}` as the
quotient of the relative differentials by the divided power relations, which is why they cannot
be stated before that presentation is available.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07HR](https://stacks.math.columbia.edu/tag/07HR)
* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ) — the downstream
  consumer, comparing `Ω_{T/Y,δ}` with the restriction of `Ω_{X/S}` to an object `(U, T, δ)` of
  `Cris(X/S)`.  It additionally needs the crystalline structure sheaf `𝒪_{X/S}`, the module
  `Ω_{X/S}` over it, the small crystalline site `Cris(X/S)` and the restriction functor `(−)_T`,
  none of which exist in this library.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### Divided power differentials of a morphism of commutative rings -/

section CommRingCatLevel

variable {A B : CommRingCat.{u}} {J : Ideal B}

/-- The divided power relations `d (δ_{n+1} x) - δ_n x · d x` inside the Kähler differentials of
a morphism `f : A ⟶ B` of commutative rings. -/
def dpRelations (f : A ⟶ B) (hJ : DividedPowers J) :
    Submodule B (CommRingCat.KaehlerDifferential f) :=
  letI := f.hom.toAlgebra
  dividedPowerDifferentialRelations (A := A) hJ

/-- **The module of divided power differentials of a morphism of commutative rings.**  For
`f : A ⟶ B` and divided powers `δ` on an ideal `J` of `B`, this is `Ω¹_{B/A,δ}`, the quotient of
the Kähler differentials of `f` by the divided power relations. -/
def dpDifferentials (f : A ⟶ B) (hJ : DividedPowers J) : ModuleCat.{u} B :=
  letI := f.hom.toAlgebra
  ModuleCat.of B (dividedPowerDifferentials (A := A) hJ)

/-- The quotient map from the Kähler differentials onto the divided power differentials. -/
def dpMkQ (f : A ⟶ B) (hJ : DividedPowers J) :
    CommRingCat.KaehlerDifferential f ⟶ dpDifferentials f hJ :=
  ModuleCat.ofHom (dpRelations f hJ).mkQ

/-- **The universal divided power differential** of a morphism of commutative rings, as a
derivation into the module of divided power differentials. -/
def dpD (f : A ⟶ B) (hJ : DividedPowers J) : (dpDifferentials f hJ).Derivation f :=
  ModuleCat.Derivation.mk (fun b ↦ dpMkQ f hJ (CommRingCat.KaehlerDifferential.d b))
    (fun b b' ↦ by simp) (fun b b' ↦ by simp) (fun a ↦ by simp)

/-- The universal divided power differential `d b ∈ Ω¹_{B/A,δ}` of an element `b` of `B`. -/
abbrev dpd {f : A ⟶ B} (hJ : DividedPowers J) (b : B) : dpDifferentials f hJ :=
  (dpD f hJ).d b

/-- The universal divided power differential of a morphism of commutative rings is the universal
divided power differential of the underlying algebra. -/
theorem dpd_eq (f : A ⟶ B) (hJ : DividedPowers J) (b : B) :
    dpd (f := f) hJ b =
      letI := f.hom.toAlgebra
      dividedPowerDifferential (A := A) hJ b := rfl

/-- The universal divided power differential is additive. -/
@[simp]
theorem dpd_add (f : A ⟶ B) (hJ : DividedPowers J) (b b' : B) :
    dpd (f := f) hJ (b + b') = dpd (f := f) hJ b + dpd (f := f) hJ b' :=
  ModuleCat.Derivation.d_add (dpD f hJ) b b'

/-- The Leibniz rule for the universal divided power differential. -/
@[simp]
theorem dpd_mul (f : A ⟶ B) (hJ : DividedPowers J) (b b' : B) :
    dpd (f := f) hJ (b * b') = b • dpd (f := f) hJ b' + b' • dpd (f := f) hJ b :=
  ModuleCat.Derivation.d_mul (dpD f hJ) b b'

/-- The universal divided power differential kills the image of the base ring. -/
@[simp]
theorem dpd_map (f : A ⟶ B) (hJ : DividedPowers J) (a : A) :
    dpd (f := f) hJ (f a) = 0 :=
  ModuleCat.Derivation.d_map (dpD f hJ) a

/-- The divided power chain rule for the universal divided power differential. -/
theorem dpd_dpow (f : A ⟶ B) (hJ : DividedPowers J) (n : ℕ) (x : B) (hx : x ∈ J) :
    dpd (f := f) hJ (hJ.dpow (n + 1) x) = hJ.dpow n x • dpd (f := f) hJ x :=
  let _ := f.hom.toAlgebra
  dividedPowerDifferential_dpow (A := A) hJ ⟨x, hx⟩ n

/-- Two maps out of the module of divided power differentials agreeing on every universal
differential are equal. -/
@[ext]
theorem dpDifferentials_ext {f : A ⟶ B} {hJ : DividedPowers J} {M : ModuleCat.{u} B}
    {α β : dpDifferentials f hJ ⟶ M} (h : ∀ b : B, α (dpd hJ b) = β (dpd hJ b)) : α = β := by
  let _ := f.hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext_on (dividedPowerDifferentials_span (A := A) hJ) ?_)
  rintro _ ⟨b, rfl⟩
  exact h b

/-- A derivation obeying the divided power chain rule descends to the module of divided power
differentials. -/
def dpDesc {f : A ⟶ B} {hJ : DividedPowers J} {M : ModuleCat.{u} B} (D : M.Derivation f)
    (hD : ∀ (n : ℕ) (x : B), x ∈ J → D.d (hJ.dpow (n + 1) x) = hJ.dpow n x • D.d x) :
    dpDifferentials f hJ ⟶ M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom (M : Type u) f.hom
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  ModuleCat.ofHom ((dividedPowerDifferentialRelations (A := A) hJ).liftQ
    (D : _root_.Derivation A B M).liftKaehlerDifferential (by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨x, n⟩, rfl⟩
      have hdA : ∀ b : B,
          (D : _root_.Derivation A B M).liftKaehlerDifferential
            (KaehlerDifferential.D A B b) = D.d b :=
        fun b ↦ (D : _root_.Derivation A B M).liftKaehlerDifferential_comp_D b
      change (D : _root_.Derivation A B M).liftKaehlerDifferential
        (dividedPowerDifferentialRelation hJ x n) = 0
      simp only [dividedPowerDifferentialRelation, map_sub, map_smul, hdA]
      rw [hD n x x.2, sub_self]))

/-- The descended map sends the universal divided power differential `dpd hJ b` to `D.d b`. -/
@[simp]
theorem dpDesc_d {f : A ⟶ B} {hJ : DividedPowers J} {M : ModuleCat.{u} B} (D : M.Derivation f)
    (hD : ∀ (n : ℕ) (x : B), x ∈ J → D.d (hJ.dpow (n + 1) x) = hJ.dpow n x • D.d x) (b : B) :
    dpDesc D hD (dpd hJ b) = D.d b :=
  let _ := f.hom.toAlgebra
  let _ := Module.compHom (M : Type u) f.hom
  let _ : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (D : _root_.Derivation A B M).liftKaehlerDifferential_comp_D b

end CommRingCatLevel

section Functoriality

variable {A B A' B' : CommRingCat.{u}} {J : Ideal B} {J' : Ideal B'}
  {f : A ⟶ B} {f' : A' ⟶ B'} {g : A ⟶ A'} {g' : B ⟶ B'}

/-- A homomorphism of divided power rings sends the distinguished ideal into the distinguished
ideal. -/
theorem mem_ideal_of_isDPMorphism {hJ : DividedPowers J} {hJ' : DividedPowers J'}
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) {x : B} (hx : x ∈ J) : g' x ∈ J' :=
  hg.ideal_comp (Ideal.mem_map_of_mem _ hx)

/-- A homomorphism of divided power rings commutes with the divided power operations, in the
spelling used for applications of a morphism of `CommRingCat`. -/
theorem dpow_of_isDPMorphism {hJ : DividedPowers J} {hJ' : DividedPowers J'}
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) {n : ℕ} {x : B} (hx : x ∈ J) :
    hJ'.dpow n (g' x) = g' (hJ.dpow n x) :=
  hg.dpow_comp x hx

end Functoriality

/-! ### Divided power differentials vanishing on a set of constants -/

section Constants

variable {A B : CommRingCat.{u}} {J : Ideal B}

/-- The submodule of `Ω¹_{B/A,δ}` spanned by the differentials of the elements of a set `S`. -/
def dpBaseRelations (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) :
    Submodule B (dpDifferentials f hJ) :=
  Submodule.span B (dpd (f := f) hJ '' S)

/-- **The module of divided power differentials vanishing on a set of constants.**  This is
`Ω¹_{B/A,δ}` modulo the differentials of the elements of `S`; it receives the universal divided
power derivation among those killing `A` and `S`. -/
def dpConstDifferentials (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) : ModuleCat.{u} B :=
  ModuleCat.of B (↥(dpDifferentials f hJ) ⧸ dpBaseRelations f hJ S)

/-- The quotient map from the divided power differentials. -/
def dpConstMk (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) :
    dpDifferentials f hJ ⟶ dpConstDifferentials f hJ S :=
  ModuleCat.ofHom (dpBaseRelations f hJ S).mkQ

/-- **The universal divided power differential killing `A` and a set of constants `S`.** -/
def dpConstD (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) :
    (dpConstDifferentials f hJ S).Derivation f :=
  ModuleCat.Derivation.mk (fun b ↦ dpConstMk f hJ S (dpd hJ b))
    (fun b b' ↦ by rw [dpd_add, map_add])
    (fun b b' ↦ by rw [dpd_mul, map_add, map_smul, map_smul])
    (fun a ↦ by rw [dpd_map, map_zero])

/-- The universal divided power differential killing `S` sends `b` to the image of `dpd hJ b`. -/
@[simp]
theorem dpConstD_d (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) (b : B) :
    (dpConstD f hJ S).d b = dpConstMk f hJ S (dpd hJ b) := rfl

/-- The universal divided power differential of a constant vanishes. -/
theorem dpConstD_base (f : A ⟶ B) (hJ : DividedPowers J) {S : Set B} {s : B} (hs : s ∈ S) :
    (dpConstD f hJ S).d s = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨s, hs, rfl⟩)

/-- The divided power chain rule for the universal divided power differential killing `A` and a
set of constants. -/
theorem dpConstD_dpow (f : A ⟶ B) (hJ : DividedPowers J) (S : Set B) (n : ℕ) (x : B)
    (hx : x ∈ J) :
    (dpConstD f hJ S).d (hJ.dpow (n + 1) x) = hJ.dpow n x • (dpConstD f hJ S).d x := by
  rw [dpConstD_d, dpConstD_d, dpd_dpow f hJ n x hx, map_smul]

/-- Two maps out of the module of divided power differentials killing `A` and `S` agreeing on
every universal differential are equal. -/
@[ext]
theorem dpConstDifferentials_ext {f : A ⟶ B} {hJ : DividedPowers J} {S : Set B}
    {M : ModuleCat.{u} B} {α β : dpConstDifferentials f hJ S ⟶ M}
    (h : ∀ b : B, α ((dpConstD f hJ S).d b) = β ((dpConstD f hJ S).d b)) : α = β :=
  ModuleCat.hom_ext (Submodule.linearMap_qext _ (congrArg ModuleCat.Hom.hom
    (dpDifferentials_ext (α := dpConstMk f hJ S ≫ α) (β := dpConstMk f hJ S ≫ β) h)))

/-- A derivation obeying the divided power chain rule and vanishing on `S` descends to the module
of divided power differentials killing `A` and `S`. -/
def dpConstDesc {f : A ⟶ B} {hJ : DividedPowers J} {S : Set B} {M : ModuleCat.{u} B}
    (D : M.Derivation f)
    (hD : ∀ (n : ℕ) (x : B), x ∈ J → D.d (hJ.dpow (n + 1) x) = hJ.dpow n x • D.d x)
    (hS : ∀ s ∈ S, D.d s = 0) :
    dpConstDifferentials f hJ S ⟶ M :=
  ModuleCat.ofHom ((dpBaseRelations f hJ S).liftQ (dpDesc D hD).hom (by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact (dpDesc_d D hD s).trans (hS s hs)))

/-- The descended map sends the universal differential `(dpConstD f hJ S).d b` to `D.d b`. -/
@[simp]
theorem dpConstDesc_d {f : A ⟶ B} {hJ : DividedPowers J} {S : Set B} {M : ModuleCat.{u} B}
    (D : M.Derivation f)
    (hD : ∀ (n : ℕ) (x : B), x ∈ J → D.d (hJ.dpow (n + 1) x) = hJ.dpow n x • D.d x)
    (hS : ∀ s ∈ S, D.d s = 0) (b : B) :
    dpConstDesc D hD hS ((dpConstD f hJ S).d b) = D.d b :=
  dpDesc_d D hD b

end Constants

section ConstFunctoriality

variable {A B A' B' : CommRingCat.{u}} {J : Ideal B} {J' : Ideal B'}
  {f : A ⟶ B} {f' : A' ⟶ B'} {g : A ⟶ A'} {g' : B ⟶ B'}

/-- Composing a homomorphism `g'` of divided power rings over `g` with the universal divided
power differential of `f'` gives a derivation of `B` into the divided power differentials of
`f'`, the latter viewed as a `B`-module along `g'`. -/
def dpConstCompDerivation (fac : g ≫ f' = f ≫ g') (hJ' : DividedPowers J') (S' : Set B') :
    ((ModuleCat.restrictScalars g'.hom).obj (dpConstDifferentials f' hJ' S')).Derivation f :=
  ModuleCat.Derivation.mk (fun b ↦ (dpConstD f' hJ' S').d (g' b))
    (fun b b' ↦ by
      rw [map_add]
      exact ModuleCat.Derivation.d_add (dpConstD f' hJ' S') (g' b) (g' b'))
    (fun b b' ↦ by
      rw [map_mul]
      exact ModuleCat.Derivation.d_mul (dpConstD f' hJ' S') (g' b) (g' b'))
    (fun a ↦ by
      have h : g' (f a) = f' (g a) := by
        rw [← CommRingCat.comp_apply, ← fac, CommRingCat.comp_apply]
      rw [h]
      exact ModuleCat.Derivation.d_map (dpConstD f' hJ' S') (g a))

/-- **The restriction map on divided power differentials killing a set of constants.** -/
def dpConstMap (fac : g ≫ f' = f ≫ g') (hJ : DividedPowers J) (hJ' : DividedPowers J')
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) (S : Set B) (S' : Set B')
    (hS : ∀ s ∈ S, g' s ∈ S') :
    dpConstDifferentials f hJ S ⟶
      (ModuleCat.restrictScalars g'.hom).obj (dpConstDifferentials f' hJ' S') :=
  dpConstDesc (dpConstCompDerivation fac hJ' S')
    (fun n x hx ↦ by
      have hgx : g' x ∈ J' := mem_ideal_of_isDPMorphism hg hx
      have h1 : (dpConstD f' hJ' S').d (g' (hJ.dpow (n + 1) x))
          = hJ'.dpow n (g' x) • (dpConstD f' hJ' S').d (g' x) := by
        rw [← dpow_of_isDPMorphism hg hx]
        exact dpConstD_dpow f' hJ' S' n (g' x) hgx
      have h2 : hJ'.dpow n (g' x) • (dpConstD f' hJ' S').d (g' x)
          = g' (hJ.dpow n x) • (dpConstD f' hJ' S').d (g' x) := by
        rw [dpow_of_isDPMorphism hg hx]
      exact h1.trans h2)
    (fun s hs ↦ dpConstD_base f' hJ' (hS s hs))

/-- The restriction map sends `d b` to `d (g' b)`. -/
@[simp]
theorem dpConstMap_d (fac : g ≫ f' = f ≫ g') (hJ : DividedPowers J) (hJ' : DividedPowers J')
    (hg : DividedPowers.IsDPMorphism hJ hJ' g'.hom) (S : Set B) (S' : Set B')
    (hS : ∀ s ∈ S, g' s ∈ S') (b : B) :
    dpConstMap fac hJ hJ' hg S S' hS ((dpConstD f hJ S).d b)
      = (dpConstD f' hJ' S').d (g' b) :=
  dpConstDesc_d _ _ _ b

end ConstFunctoriality

/-! ### The presheaf of divided power differentials of a divided power scheme -/

section Presheaf

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The map from the global sections of the base to the sections of `T` over an open `W`, along
which the divided power differentials over `W` are formed. -/
def baseAppLE (W : T.scheme.Opens) : Γ(Y, ⊤) ⟶ Γ(T.scheme, W) :=
  f.appLE ⊤ W (le_preimage_top f W)

/-- The base maps are compatible with restriction in `T`. -/
theorem baseAppLE_fac {W W' : (T.scheme.Opens)ᵒᵖ} (i : W ⟶ W') :
    (𝟙 Γ(Y, ⊤)) ≫ baseAppLE T Y f W'.unop =
      baseAppLE T Y f W.unop ≫ T.scheme.presheaf.map i :=
  (Category.id_comp _).trans (f.appLE_map _ i).symm

/-- The sections of `𝒪_T` over an open `W` that are pulled back from the base: the images of the
sections of `𝒪_Y` over *some* open `V` of `Y` with `W ≤ f⁻¹V`.  The divided power differentials
of all of these are killed, which is what makes the universal differential a divided power
`Γ(V, 𝒪_Y)`-derivation for every such `V` and not only for `V = ⊤`. -/
def baseSections (W : T.scheme.Opens) : Set Γ(T.scheme, W) :=
  {b | ∃ (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)), f.appLE V W h a = b}

/-- The image of a section of `𝒪_Y` over `V` is a section pulled back from the base. -/
theorem appLE_mem_baseSections (W : T.scheme.Opens) (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (a : Γ(Y, V)) : f.appLE V W h a ∈ baseSections T Y f W :=
  ⟨V, h, a, rfl⟩

/-- The sections pulled back from the base are stable under restriction. -/
theorem map_mem_baseSections {W W' : (T.scheme.Opens)ᵒᵖ} (i : W ⟶ W')
    {b : Γ(T.scheme, W.unop)} (hb : b ∈ baseSections T Y f W.unop) :
    T.scheme.presheaf.map i b ∈ baseSections T Y f W'.unop := by
  obtain ⟨V, h, a, rfl⟩ := hb
  refine ⟨V, i.unop.le.trans h, a, ?_⟩
  rw [← CommRingCat.comp_apply, f.appLE_map h i]

/-- **The presheaf of divided power differentials.**  Over an open `W` of `T` its sections are
the divided power differentials of `Γ(W, 𝒪_T)` modulo the differentials of all sections pulled
back from the base, and the restriction maps are induced by the restriction maps of `𝒪_T`, which
are homomorphisms of divided power rings. -/
def dpDifferentialsPresheaf : T.scheme.PresheafOfModules where
  obj W := dpConstDifferentials (baseAppLE T Y f W.unop) (T.dividedPowers.dividedPowers W)
    (baseSections T Y f W.unop)
  map {W W'} i := dpConstMap (baseAppLE_fac T Y f i) (T.dividedPowers.dividedPowers W)
    (T.dividedPowers.dividedPowers W') (T.dividedPowers.naturality i)
    (baseSections T Y f W.unop) (baseSections T Y f W'.unop)
    (fun _ hs ↦ map_mem_baseSections T Y f i hs)
  map_id := fun W ↦ by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have hb : T.scheme.presheaf.map (𝟙 W) b = b := by rw [T.scheme.presheaf.map_id]; rfl
    rw [dpConstMap_d (baseAppLE_fac T Y f (𝟙 W)) (T.dividedPowers.dividedPowers W)
      (T.dividedPowers.dividedPowers W) (T.dividedPowers.naturality (𝟙 W))
      (baseSections T Y f W.unop) (baseSections T Y f W.unop)
      (fun _ hs ↦ map_mem_baseSections T Y f (𝟙 W) hs) b, hb]
    rfl
  map_comp := fun {W W' W''} i j ↦ by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have hb : T.scheme.presheaf.map (i ≫ j) b
        = T.scheme.presheaf.map j (T.scheme.presheaf.map i b) := by
      rw [T.scheme.presheaf.map_comp]; rfl
    have e1 := dpConstMap_d (baseAppLE_fac T Y f (i ≫ j)) (T.dividedPowers.dividedPowers W)
      (T.dividedPowers.dividedPowers W'') (T.dividedPowers.naturality (i ≫ j))
      (baseSections T Y f W.unop) (baseSections T Y f W''.unop)
      (fun _ hs ↦ map_mem_baseSections T Y f (i ≫ j) hs) b
    have e2 := dpConstMap_d (baseAppLE_fac T Y f i) (T.dividedPowers.dividedPowers W)
      (T.dividedPowers.dividedPowers W') (T.dividedPowers.naturality i)
      (baseSections T Y f W.unop) (baseSections T Y f W'.unop)
      (fun _ hs ↦ map_mem_baseSections T Y f i hs) b
    have e3 := dpConstMap_d (baseAppLE_fac T Y f j) (T.dividedPowers.dividedPowers W')
      (T.dividedPowers.dividedPowers W'') (T.dividedPowers.naturality j)
      (baseSections T Y f W'.unop) (baseSections T Y f W''.unop)
      (fun _ hs ↦ map_mem_baseSections T Y f j hs) (T.scheme.presheaf.map i b)
    exact e1.trans ((congrArg
      (fun x ↦ (dpConstD (baseAppLE T Y f W''.unop) (T.dividedPowers.dividedPowers W'')
        (baseSections T Y f W''.unop)).d x) hb).trans
          (e3.symm.trans (congrArg (ConcreteCategory.hom
            (dpConstMap (baseAppLE_fac T Y f j) (T.dividedPowers.dividedPowers W')
              (T.dividedPowers.dividedPowers W'') (T.dividedPowers.naturality j)
              (baseSections T Y f W'.unop) (baseSections T Y f W''.unop)
              (fun _ hs ↦ map_mem_baseSections T Y f j hs))) e2).symm))

/-- The universal divided power differential on the sections over an open `W`. -/
abbrev presheafD (W : T.scheme.Opens) :
    ((dpDifferentialsPresheaf T Y f).obj (op W)).Derivation (baseAppLE T Y f W) :=
  dpConstD (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W)) (baseSections T Y f W)

/-- The restriction maps of the presheaf of divided power differentials send `d b` to the
differential of the restriction of `b`. -/
@[simp]
theorem dpDifferentialsPresheaf_map {W W' : (T.scheme.Opens)ᵒᵖ} (i : W ⟶ W')
    (b : Γ(T.scheme, W.unop)) :
    (dpDifferentialsPresheaf T Y f).map i ((presheafD T Y f W.unop).d b) =
      (presheafD T Y f W'.unop).d (T.scheme.presheaf.map i b) :=
  dpConstMap_d (baseAppLE_fac T Y f i) _ _ (T.dividedPowers.naturality i) _ _
    (fun _ hs ↦ map_mem_baseSections T Y f i hs) b

end Presheaf

/-! ### The sheaf of divided power differentials -/

section Sheaf

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- **The sheaf of divided power differentials** `Ω_{T/Y,δ}` of a divided power scheme `T` over a
scheme `Y`: the sheaf of `𝒪_T`-modules associated with the presheaf of divided power
differentials. -/
@[stacks 07IW "the sheaf Ω_{T/Y,δ} of divided power differentials of a divided power
  scheme over a scheme"]
def dpDifferentialsSheaf : T.scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 T.scheme.ringCatSheaf.obj)).obj
    (dpDifferentialsPresheaf T Y f)

/-- The unit of the sheafification, comparing the presheaf of divided power differentials with
the sheaf of `𝒪_T`-modules it generates. -/
def dpDifferentialsToSheaf :
    dpDifferentialsPresheaf T Y f ⟶
      (Scheme.Modules.toPresheafOfModules T.scheme).obj (dpDifferentialsSheaf T Y f) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 T.scheme.ringCatSheaf.obj)).unit.app _

/-- The sections of the presheaf of divided power differentials over `W`, as a module over the
ring of sections of `𝒪_T` over `W`; the two rings are the same, but a presheaf of modules is
indexed by the sheaf of rings in its `RingCat`-valued form, so the instance is supplied by
name. -/
instance presheafObjModule (W : T.scheme.Opens) :
    Module Γ(T.scheme, W) ↥((dpDifferentialsPresheaf T Y f).obj (op W)) :=
  ((dpDifferentialsPresheaf T Y f).obj (op W)).isModule

/-- The sections over `W` of the underlying presheaf of modules of the sheaf of divided power
differentials, as a module over the ring of sections of `𝒪_T` over `W`. -/
instance sheafObjModule (W : T.scheme.Opens) :
    Module Γ(T.scheme, W)
      ↥(((Scheme.Modules.toPresheafOfModules T.scheme).obj
        (dpDifferentialsSheaf T Y f)).obj (op W)) :=
  inferInstanceAs (Module Γ(T.scheme, W) Γ(dpDifferentialsSheaf T Y f, W))

/-- The map on sections of the universal divided power derivation of `T` over `Y`: the universal
divided power differential, followed by the comparison with the associated sheaf. -/
def sheafApp (W : T.scheme.Opens) :
    Γ(T.scheme, W) → Γ(dpDifferentialsSheaf T Y f, W) :=
  fun x ↦ (dpDifferentialsToSheaf T Y f).app (op W) ((presheafD T Y f W).d x)

/-- The universal divided power derivation is additive on sections. -/
theorem sheafApp_add (W : T.scheme.Opens) (x y : Γ(T.scheme, W)) :
    sheafApp T Y f W (x + y) = sheafApp T Y f W x + sheafApp T Y f W y :=
  (congrArg (fun z ↦ (dpDifferentialsToSheaf T Y f).app (op W) z)
      (ModuleCat.Derivation.d_add (presheafD T Y f W) x y)).trans
    (map_add ((dpDifferentialsToSheaf T Y f).app (op W)).hom
      ((presheafD T Y f W).d x) ((presheafD T Y f W).d y))

/-- The Leibniz rule for the universal divided power derivation, on sections. -/
theorem sheafApp_mul (W : T.scheme.Opens) (x y : Γ(T.scheme, W)) :
    sheafApp T Y f W (x * y) = x • sheafApp T Y f W y + y • sheafApp T Y f W x := by
  have ha : (dpDifferentialsToSheaf T Y f).app (op W) (x • (presheafD T Y f W).d y)
      = x • sheafApp T Y f W y :=
    map_smul ((dpDifferentialsToSheaf T Y f).app (op W)).hom x ((presheafD T Y f W).d y)
  have hb : (dpDifferentialsToSheaf T Y f).app (op W) (y • (presheafD T Y f W).d x)
      = y • sheafApp T Y f W x :=
    map_smul ((dpDifferentialsToSheaf T Y f).app (op W)).hom y ((presheafD T Y f W).d x)
  refine (congrArg (fun z ↦ (dpDifferentialsToSheaf T Y f).app (op W) z)
      (ModuleCat.Derivation.d_mul (presheafD T Y f W) x y)).trans
    ((map_add ((dpDifferentialsToSheaf T Y f).app (op W)).hom
      (x • (presheafD T Y f W).d y) (y • (presheafD T Y f W).d x)).trans ?_)
  exact (congrArg (fun z ↦ z + (dpDifferentialsToSheaf T Y f).app (op W)
    (y • (presheafD T Y f W).d x)) ha).trans
      (congrArg (fun z ↦ x • sheafApp T Y f W y + z) hb)

/-- The universal divided power derivation kills every section pulled back from the base. -/
theorem sheafApp_base (W : T.scheme.Opens) {x : Γ(T.scheme, W)}
    (hx : x ∈ baseSections T Y f W) : sheafApp T Y f W x = 0 :=
  (congrArg (fun z ↦ (dpDifferentialsToSheaf T Y f).app (op W) z)
      (dpConstD_base (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W)) hx)).trans
    (map_zero ((dpDifferentialsToSheaf T Y f).app (op W)).hom)

/-- The divided power chain rule for the universal divided power derivation, on sections. -/
theorem sheafApp_dpow (W : T.scheme.Opens) (n : ℕ) (x : Γ(T.scheme, W))
    (hx : x ∈ T.ideal.obj (op W)) :
    sheafApp T Y f W
        ((T.dividedPowers.toDividedPowerRing (op W)).dividedPowers.dpow (n + 1) x) =
      (T.dividedPowers.toDividedPowerRing (op W)).dividedPowers.dpow n x •
        sheafApp T Y f W x :=
  (congrArg (fun z ↦ (dpDifferentialsToSheaf T Y f).app (op W) z)
      (dpConstD_dpow (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W))
        (baseSections T Y f W) n x hx)).trans
    (map_smul ((dpDifferentialsToSheaf T Y f).app (op W)).hom
      (@id Γ(T.scheme, W) ((T.dividedPowers.dividedPowers (op W)).dpow n x))
      ((presheafD T Y f W).d x))

/-- The maps on sections commute with restriction. -/
theorem sheafApp_naturality {W W' : T.scheme.Opens} (i : W' ⟶ W) (x : Γ(T.scheme, W)) :
    (dpDifferentialsSheaf T Y f).presheaf.map i.op (sheafApp T Y f W x) =
      sheafApp T Y f W' (T.scheme.presheaf.map i.op x) :=
  (PresheafOfModules.naturality_apply (dpDifferentialsToSheaf T Y f) i.op
      ((presheafD T Y f W).d x)).symm.trans
    (congrArg (fun z ↦ (dpDifferentialsToSheaf T Y f).app (op W') z)
      (dpDifferentialsPresheaf_map T Y f i.op x))

/-- **The universal divided power derivation over an open of `T`, relative to an open `V` of the
base.**  For every open `V` of `Y` with `W ≤ f⁻¹V` the map on sections is a divided power
`Γ(V, 𝒪_Y)`-derivation, because the differentials of all sections pulled back from the base have
been killed. -/
def dpDerivationAt (W : T.scheme.Opens) (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(Y, V) (T.dividedPowers.toDividedPowerRing (op W))
      (f.appLE V W h).hom Γ(dpDifferentialsSheaf T Y f, W) where
  toDerivation :=
    Derivation.mk'
      (AddMonoidHom.toIntLinearMap
        (AddMonoidHom.mk' (sheafApp T Y f W) (sheafApp_add T Y f W)))
      (sheafApp_mul T Y f W)
  map_ringHom' a := sheafApp_base T Y f W (appLE_mem_baseSections T Y f W V h a)
  map_dpow' n hn x hx := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact sheafApp_dpow T Y f W k x hx

/-- **The universal divided power derivation of a divided power scheme over a scheme**, with
values in the sheaf of divided power differentials. -/
def universalDPSchemeDerivation :
    DividedPowerSchemeDerivation T Y f (dpDifferentialsSheaf T Y f) where
  app W := sheafApp T Y f W
  naturality i x := sheafApp_naturality T Y f i x
  dividedPowerDerivation W V h := dpDerivationAt T Y f W V h
  dividedPowerDerivation_apply _ _ _ _ := rfl

/-- On sections over `W`, the universal divided power derivation is `sheafApp T Y f W`. -/
@[simp]
theorem universalDPSchemeDerivation_app (W : T.scheme.Opens) (x : Γ(T.scheme, W)) :
    (universalDPSchemeDerivation T Y f).app W x = sheafApp T Y f W x := rfl

end Sheaf

/-! ### Universality -/

section Universal

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  (N : T.scheme.Modules) (E : DividedPowerSchemeDerivation T Y f N)

/-- A divided power derivation of `𝒪_T` over `Y` into `N`, read on the sections over an open `W`
as a derivation relative to the global sections of the base. -/
def descDerivation (W : T.scheme.Opens) :
    (((Scheme.Modules.toPresheafOfModules T.scheme).obj N).obj (op W)).Derivation
      (baseAppLE T Y f W) :=
  ModuleCat.Derivation.mk (E.app W) (E.app_add W) (E.leibniz W)
    (fun a ↦ E.app_appLE W ⊤ (le_preimage_top f W) a)

/-- The map on sections over `W` through which a divided power derivation into `N` factors. -/
def descApp (W : T.scheme.Opens) :
    (dpDifferentialsPresheaf T Y f).obj (op W) ⟶
      ((Scheme.Modules.toPresheafOfModules T.scheme).obj N).obj (op W) :=
  dpConstDesc (descDerivation T Y f N E W)
    (fun n x hx ↦ E.app_dpow W (n + 1) (Nat.succ_pos n) x hx)
    (fun _ hs ↦ by
      obtain ⟨V, h, a, rfl⟩ := hs
      exact E.app_appLE W V h a)

/-- The map `descApp` sends the universal differential `d x` to `E.app W x`. -/
@[simp]
theorem descApp_d (W : T.scheme.Opens) (x : Γ(T.scheme, W)) :
    descApp T Y f N E W ((presheafD T Y f W).d x) = E.app W x :=
  dpConstDesc_d _ _ _ x

/-- **The factorization of a divided power derivation through the presheaf of divided power
differentials.** -/
def descHom : dpDifferentialsPresheaf T Y f ⟶
    (Scheme.Modules.toPresheafOfModules T.scheme).obj N where
  app X := descApp T Y f N E X.unop
  naturality {X X'} i := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have h1 := dpDifferentialsPresheaf_map T Y f i b
    have h2 := descApp_d T Y f N E X'.unop (T.scheme.presheaf.map i b)
    have h3 := descApp_d T Y f N E X.unop b
    have h4 := E.naturality i.unop b
    exact ((congrArg (fun z ↦ descApp T Y f N E X'.unop z) h1).trans h2).trans
      (h4.symm.trans (congrArg (fun z ↦ (Scheme.Modules.presheaf N).map i z) h3).symm)

/-- The factorization `descHom` sends the universal differential `d x` over `W` to
`E.app W x`. -/
@[simp]
theorem descHom_app_d (W : T.scheme.Opens) (x : Γ(T.scheme, W)) :
    (descHom T Y f N E).app (op W) ((presheafD T Y f W).d x) = E.app W x :=
  descApp_d T Y f N E W x

/-- The factorization through the presheaf of divided power differentials is the only one. -/
theorem descHom_unique
    (χ : dpDifferentialsPresheaf T Y f ⟶ (Scheme.Modules.toPresheafOfModules T.scheme).obj N)
    (hχ : ∀ (W : T.scheme.Opens) (x : Γ(T.scheme, W)),
      χ.app (op W) ((presheafD T Y f W).d x) = E.app W x) :
    χ = descHom T Y f N E :=
  PresheafOfModules.hom_ext fun X ↦ dpConstDifferentials_ext fun b ↦
    (hχ X.unop b).trans (descApp_d T Y f N E X.unop b).symm

end Universal

section Universality

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The sheafification adjunction for presheaves of `𝒪_T`-modules. -/
def sheafificationAdj :
    PresheafOfModules.sheafification (𝟙 T.scheme.ringCatSheaf.obj) ⊣
      SheafOfModules.forget T.scheme.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 T.scheme.ringCatSheaf.obj) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 T.scheme.ringCatSheaf.obj)

/-- **The universal property of the sheaf of divided power differentials.**  Every divided power
derivation of `𝒪_T` over `Y` into a sheaf of `𝒪_T`-modules factors uniquely through the universal
one. -/
@[stacks 07IW "the universal divided power derivation d_{T/Y,δ} and its universal property"]
theorem universalDPSchemeDerivation_isUniversal :
    (universalDPSchemeDerivation T Y f).IsUniversal := by
  intro N E
  have key : ∀ ψ : (PresheafOfModules.sheafification (𝟙 T.scheme.ringCatSheaf.obj)).obj
      (dpDifferentialsPresheaf T Y f) ⟶ N,
      (sheafificationAdj T).unit.app (dpDifferentialsPresheaf T Y f) ≫
        (SheafOfModules.forget T.scheme.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 T.scheme.ringCatSheaf.obj)).map ψ =
      (sheafificationAdj T).homEquiv (dpDifferentialsPresheaf T Y f) N ψ :=
    fun ψ ↦ ((sheafificationAdj T).homEquiv_unit (dpDifferentialsPresheaf T Y f) N ψ).symm
  refine ⟨((sheafificationAdj T).homEquiv (dpDifferentialsPresheaf T Y f) N).symm
    (descHom T Y f N E), ?_, ?_⟩
  · intro W x
    exact (congrArg (fun ρ ↦ ρ.app (op W) ((presheafD T Y f W).d x))
      ((key _).trans (Equiv.apply_symm_apply _ (descHom T Y f N E)))).trans
      (descHom_app_d T Y f N E W x)
  · intro φ hφ
    refine ((sheafificationAdj T).homEquiv (dpDifferentialsPresheaf T Y f) N).injective ?_
    exact (key φ).symm.trans ((descHom_unique T Y f N E _ (fun W x ↦ hφ W x)).trans
      (Equiv.apply_symm_apply _ _).symm)

end Universality

end Crystalline

end
