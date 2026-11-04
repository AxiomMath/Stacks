module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingEval
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerLocal
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleHomGlue
public import StacksFrontier.RingTheory.ReesAlgebra.SmulDescend

/-!
# The graded splitting exists as soon as the splitting kills relations on every open

Let `I = (f₁, …, f_r)` be an ideal of a commutative ring `A`, let `X` be a scheme over `Spec A`,
let `F` be an `𝒪_X`-module and let `ψ_j : I ^ d ⟶ A` be a family of linear functionals. This
file shows that the graded map of [Stacks, Tag 0EH6]

`Φ_F : ⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]`

**exists** as soon as `ψ` kills the relations of the sections `Γ(F, V)` over *every* open `V` of
`X`, in the sense of `Stacks.ReesAlgebra.KillsRelationsHom`. Together with
`Stacks.Coherent.gradedSplitting_unique` and `Stacks.Coherent.gradedSplittingEvalHom_eq_ι` this
reduces [Stacks, Tag 0EH6] to that one hypothesis: no sheaf theory is left in it, only the
identifications of `Γ(F, V)` and of its germs with modules that commutative algebra has already
been applied to.

The construction is the glueing of
`StacksFrontier/AlgebraicGeometry/Modules/SubmoduleHomGlue.lean`. Relation-killing over `V` hands
over, by `Stacks.ReesAlgebra.KillsRelationsHom.exists_linearMap`, a `Γ(X, V)`-linear map on the
span `I(V) ^ (n d) · Γ(F, V)` of the products — and *only* on that span, while a section of
`I ^ (n d) F` over `V` is merely locally such a product
(`Stacks.Algebraization.mem_idealPowerMultiple_iff`). Those local values glue, because `F` is a
sheaf and because the per-open maps are compatible with restriction; the compatibility is proved
here, by the span induction that the uniqueness of the lift
(`Stacks.ReesAlgebra.linearMap_ext_of_smul`) is proved by.

## Main definitions

* `Stacks.Coherent.baseSpan` — the span, over an arbitrary open, of the products `g · m` with `g`
  in the image of an ideal of the base. This is the submodule relation-killing speaks about, and
  it makes sense over every open, not only the affine ones.
* `Stacks.Coherent.gradedComponentLift` — the component at a monomial `σ` of the graded map, on
  the sections over a single open: the linear map relation-killing asserts exists.
* `Stacks.Coherent.gradedLocalData` — that family of maps, packaged as the local data the
  glueing consumes.

## Main results

* `Stacks.Coherent.gradedComponentLift_apply` — the per-open map takes the prescribed value
  `Φ(g)_σ · m` on a product.
* `Stacks.Coherent.gradedComponentLift_map` — and it is compatible with restriction.
* `Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom` — **the existence half of
  [Stacks, Tag 0EH6], granted relation-killing over every open.**
* `Stacks.Coherent.killsRelationsHom_sections_of_affineOpens` — relation-killing over the affine
  opens gives it over every open, the restrictions to the affine opens inside an open being
  jointly injective.
* `Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_affineOpens` — hence the existence
  half granted relation-killing over every *affine* open, which is the form the geometry of
  [Stacks, Tag 087W] produces.

## Implementation notes

`Stacks.Coherent.baseSpan` is `Ideal.map (baseSectionHom A fX V) K · Γ(F, V)`, not
`(I · 𝒪_X)(V) ^ k · Γ(F, V)`: the latter needs `V` affine, since a quasi-coherent ideal sheaf
only has an ideal on the affine opens, whereas the glueing needs its family of submodules over
*every* open. Over an affine open the two agree
(`Stacks.Coherent.baseIdealSheaf_ideal_pow_eq_map`), which is what connects the family to
`I ^ k F` in both directions: `Stacks.Coherent.baseSpan_le_idealPowerMultiple` and
`Stacks.Coherent.loc_idealPowerMultiple`.

The exponent appears as `(I ^ d) ^ n` on the algebra side and as `I ^ (n d)` on the sheaf side;
`Stacks.ReesAlgebra.mem_pow_pow_of_mem_pow_mul` and `pow_mul` reconcile them, and the two are
kept apart deliberately — `Stacks.ReesAlgebra.extendCoeff` is indexed by the pair `(d, n)` and
not by the product.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions Stacks.ReesAlgebra
open Stacks.AlgebraicGeometry.SubmoduleHomGlue
open scoped AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules.Submodule (asModules)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### The span of the products over an arbitrary open -/

/-- The span, over an arbitrary open `V`, of the products `g · m` with `g` in the image of an
ideal `K` of the base ring. This is the submodule of `Γ(F, V)` that relation-killing along
`Stacks.Coherent.baseSectionHom` speaks about. -/
public abbrev baseSpan (A : Type u) [CommRing A] {X : Scheme.{u}} (fX : X ⟶ Spec (.of A))
    (K : Ideal A) (F : X.Modules) (V : X.Opens) : Submodule Γ(X, V) Γ(F, V) :=
  Ideal.map (baseSectionHom A fX V) K • (⊤ : Submodule Γ(X, V) Γ(F, V))

/-- Restriction after the structure map of the base is the structure map of the smaller open. -/
public lemma baseSectionHom_comp_presheaf_map (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (baseSectionHom A fX U) =
      baseSectionHom A fX V :=
  RingHom.ext fun a => baseSectionHom_map A fX h a

/-- A product `g · m` with `g` in the image of `K` is a section of
`Stacks.Coherent.baseSpan`. -/
public lemma mem_baseSpan (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) {K : Ideal A} (F : X.Modules) (V : X.Opens) {g : A} (hg : g ∈ K)
    (m : Γ(F, V)) : baseSectionHom A fX V g • m ∈ baseSpan A fX K F V :=
  Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hg) Submodule.mem_top

/-- **`Stacks.Coherent.baseSpan` is stable under restriction.** The ideal it is cut out by is
generated by the image of `K`, and restriction carries that image to the image over the smaller
open. -/
public lemma map_mem_baseSpan (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (K : Ideal A) (F : X.Modules) {V W : X.Opens} (h : W ≤ V)
    {s : Γ(F, V)} (hs : s ∈ baseSpan A fX K F V) :
    F.presheaf.map (homOfLE h).op s ∈ baseSpan A fX K F W := by
  have hideal : Ideal.map (X.presheaf.map (homOfLE h).op).hom
      (Ideal.map (baseSectionHom A fX V) K) = Ideal.map (baseSectionHom A fX W) K := by
    rw [Ideal.map_map, baseSectionHom_comp_presheaf_map]
  refine Submodule.smul_induction_on hs ?_ ?_
  · intro c hc m _
    have hc' : (X.presheaf.map (homOfLE h).op).hom c ∈
        Ideal.map (baseSectionHom A fX W) K := by
      rw [← hideal]
      exact Ideal.mem_map_of_mem _ hc
    exact Eq.mpr (congrArg (· ∈ baseSpan A fX K F W) (F.map_smul (homOfLE h) c m))
      (Submodule.smul_mem_smul hc' Submodule.mem_top)
  · intro y z hy hz
    have hyz : F.presheaf.map (homOfLE h).op (y + z) =
        F.presheaf.map (homOfLE h).op y + F.presheaf.map (homOfLE h).op z :=
      map_add _ y z
    exact Eq.mpr (congrArg (· ∈ baseSpan A fX K F W) hyz) (Submodule.add_mem _ hy hz)

/-- Restriction carries a product `g · m` to the product of `g` and the restriction of `m`. -/
private theorem map_baseSectionHom_smul (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (F : X.Modules) {V W : X.Opens} (h : W ≤ V) (a : A) (x : Γ(F, V)) :
    F.presheaf.map (homOfLE h).op (baseSectionHom A fX V a • x) =
      baseSectionHom A fX W a • F.presheaf.map (homOfLE h).op x := by
  rw [F.map_smul (homOfLE h), baseSectionHom_map]

/-- A section of `Stacks.Coherent.baseSpan` at the ideal `I ^ k` is a section of `I ^ k F`.

Over an affine open the two submodules agree; over an arbitrary open the section is shrunk to an
affine neighbourhood of each point, which is exactly the local description of `I ^ k F`. -/
public lemma baseSpan_le_idealPowerMultiple (A : Type u) [CommRing A] (J : Ideal A)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (F : X.Modules) (k : ℕ) (V : X.Opens)
    {s : Γ(F, V)} (hs : s ∈ baseSpan A fX (J ^ k) F V) :
    s ∈ (idealPowerMultiple (baseIdealSheaf A J fX) k F).toSubmodule.obj (op V) := by
  rw [mem_idealPowerMultiple_iff]
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  refine ⟨⟨W, hW⟩, hWsub, hxW, ?_⟩
  rw [baseIdealSheaf_ideal_pow_eq_map]
  exact map_mem_baseSpan A fX (J ^ k) F (show (W : X.Opens) ≤ V from hWsub) hs

/-- A section of `I ^ k F` lies in `Stacks.Coherent.baseSpan` near every point of its domain. -/
public lemma loc_idealPowerMultiple (A : Type u) [CommRing A] (J : Ideal A) {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (F : X.Modules) (k : ℕ) (V : X.Opens) (s : Γ(F, V))
    (hs : s ∈ (idealPowerMultiple (baseIdealSheaf A J fX) k F).toSubmodule.obj (op V))
    (x : X) (hx : x ∈ V) :
    ∃ W : X.Opens, ∃ h : W ≤ V, x ∈ W ∧
      F.presheaf.map (homOfLE h).op s ∈ baseSpan A fX (J ^ k) F W := by
  rw [mem_idealPowerMultiple_iff] at hs
  obtain ⟨W, h, hxW, hspan⟩ := hs x hx
  rw [baseIdealSheaf_ideal_pow_eq_map] at hspan
  exact ⟨W.1, h, hxW, hspan⟩

/-- The exponent of the sheaf side and the exponent of the algebra side agree. -/
public lemma pow_pow_eq_pow_mul {A : Type u} [CommRing A] (J : Ideal A) (d n : ℕ) :
    ((J ^ d : Ideal A) ^ n) = J ^ (n * d) := by
  rw [← pow_mul, mul_comm]

/-! ### The component of the graded map over one open -/

variable {A : Type u} [CommRing A] {J : Ideal A} {X : Scheme.{u}} {fX : X ⟶ Spec (.of A)}
  {F : X.Modules} {r d : ℕ} {ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A}

/-- **The component at a monomial `σ` of the graded map of [Stacks, Tag 0EH6], over one open.**

Relation-killing over `V` asserts that the prescription `g · m ↦ Φ(g)_σ · m` respects the
relations among the products, hence defines a `Γ(X, V)`-linear map on their span; this is that
map. It is unique by `Stacks.ReesAlgebra.linearMap_ext_of_smul`. -/
public def gradedComponentLift
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) (V : X.Opens) :
    ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F V) →ₗ[Γ(X, V)] Γ(F, V) :=
  ((hkill V).exists_linearMap n σ).choose

/-- `Stacks.Coherent.gradedComponentLift` takes the prescribed value on a product. -/
public lemma gradedComponentLift_apply
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) (V : X.Opens) (g : A) (hg : g ∈ ((J ^ d : Ideal A) ^ n))
    (m : Γ(F, V)) (hmem : baseSectionHom A fX V g • m ∈
      baseSpan A fX ((J ^ d : Ideal A) ^ n) F V) :
    gradedComponentLift hkill n σ V ⟨baseSectionHom A fX V g • m, hmem⟩ =
      baseSectionHom A fX V (extendCoeff J d n ψ σ ⟨g, hg⟩) • m :=
  ((hkill V).exists_linearMap n σ).choose_spec g hg m hmem

/-- The value of `Stacks.Coherent.gradedComponentLift` depends on the section, not on the proof
that it is in the span. -/
public lemma gradedComponentLift_congr
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) (V : X.Opens) {y y' : Γ(F, V)}
    (hy : y ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F V)
    (hy' : y' ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F V) (e : y = y') :
    gradedComponentLift hkill n σ V ⟨y, hy⟩ = gradedComponentLift hkill n σ V ⟨y', hy'⟩ := by
  subst e
  rfl

/-- **`Stacks.Coherent.gradedComponentLift` is compatible with restriction.**

Both sides are additive and semilinear along the restriction of scalars, and they agree on a
product `g · m`, whose restriction is the product of the restrictions; the products span, so the
span induction of `Stacks.ReesAlgebra.span_smul_pairs` closes the comparison. -/
public lemma gradedComponentLift_map
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V))
    (hs : s ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F V) :
    gradedComponentLift hkill n σ W
        ⟨F.presheaf.map (homOfLE h).op s,
          map_mem_baseSpan A fX ((J ^ d : Ideal A) ^ n) F h hs⟩ =
      F.presheaf.map (homOfLE h).op (gradedComponentLift hkill n σ V ⟨s, hs⟩) := by
  have hsub : ∀ {z : Γ(F, V)}, z ∈ Submodule.span Γ(X, V)
      (Set.range fun p : ↥((J ^ d : Ideal A) ^ n) × Γ(F, V) =>
        baseSectionHom A fX V (p.1 : A) • p.2) →
      z ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F V :=
    fun hz => (span_smul_pairs (M := Γ(F, V)) (baseSectionHom A fX V)
      ((J ^ d : Ideal A) ^ n)).le hz
  have hres : ∀ {z : Γ(F, V)}, z ∈ Submodule.span Γ(X, V)
      (Set.range fun p : ↥((J ^ d : Ideal A) ^ n) × Γ(F, V) =>
        baseSectionHom A fX V (p.1 : A) • p.2) →
      F.presheaf.map (homOfLE h).op z ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F W :=
    fun hz => map_mem_baseSpan A fX _ F h (hsub hz)
  have key : ∀ z ∈ Submodule.span Γ(X, V)
      (Set.range fun p : ↥((J ^ d : Ideal A) ^ n) × Γ(F, V) =>
        baseSectionHom A fX V (p.1 : A) • p.2),
      ∀ (hzW : F.presheaf.map (homOfLE h).op z ∈
          baseSpan A fX ((J ^ d : Ideal A) ^ n) F W)
        (hz : z ∈ baseSpan A fX ((J ^ d : Ideal A) ^ n) F V),
        gradedComponentLift hkill n σ W ⟨F.presheaf.map (homOfLE h).op z, hzW⟩ =
          F.presheaf.map (homOfLE h).op (gradedComponentLift hkill n σ V ⟨z, hz⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        intro hzW hz
        obtain ⟨p, rfl⟩ := hw
        have hr := map_baseSectionHom_smul A fX F h (p.1 : A) p.2
        have hmem2 : baseSectionHom A fX W (p.1 : A) •
            F.presheaf.map (homOfLE h).op p.2 ∈
            baseSpan A fX ((J ^ d : Ideal A) ^ n) F W :=
          mem_baseSpan A fX F W p.1.2 _
        rw [gradedComponentLift_congr hkill n σ W hzW hmem2 hr,
          gradedComponentLift_apply hkill n σ W (p.1 : A) p.1.2 _ hmem2,
          gradedComponentLift_apply hkill n σ V (p.1 : A) p.1.2 p.2 hz,
          map_baseSectionHom_smul A fX F h]
    | zero =>
        intro hzW hz
        have hz0 : F.presheaf.map (homOfLE h).op (0 : Γ(F, V)) = 0 := map_zero _
        rw [gradedComponentLift_congr hkill n σ W hzW (Submodule.zero_mem _) hz0,
          show (⟨(0 : Γ(F, W)), Submodule.zero_mem _⟩ :
            ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F W)) = 0 from rfl,
          show (⟨(0 : Γ(F, V)), hz⟩ :
            ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F V)) = 0 from rfl,
          map_zero, map_zero, map_zero]
    | add a b ha hb iha ihb =>
        intro hzW hab
        have haW := hres ha
        have hbW := hres hb
        have hadd : F.presheaf.map (homOfLE h).op (a + b) =
            F.presheaf.map (homOfLE h).op a + F.presheaf.map (homOfLE h).op b :=
          map_add _ a b
        rw [gradedComponentLift_congr hkill n σ W hzW
            (Submodule.add_mem _ haW hbW) hadd,
          show (⟨F.presheaf.map (homOfLE h).op a + F.presheaf.map (homOfLE h).op b,
              Submodule.add_mem _ haW hbW⟩ :
              ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F W)) =
            ⟨_, haW⟩ + ⟨_, hbW⟩ from rfl,
          show (⟨a + b, hab⟩ : ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F V)) =
            ⟨a, hsub ha⟩ + ⟨b, hsub hb⟩ from rfl,
          map_add, map_add, map_add, iha haW (hsub ha), ihb hbW (hsub hb)]
    | smul c a ha iha =>
        intro hzW hca
        have haW := hres ha
        have hsm : F.presheaf.map (homOfLE h).op (c • a) =
            (X.presheaf.map (homOfLE h).op).hom c • F.presheaf.map (homOfLE h).op a :=
          F.map_smul (homOfLE h) c a
        rw [gradedComponentLift_congr hkill n σ W hzW
            (Submodule.smul_mem _ _ haW) hsm,
          show (⟨(X.presheaf.map (homOfLE h).op).hom c •
              F.presheaf.map (homOfLE h).op a, Submodule.smul_mem _ _ haW⟩ :
              ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F W)) =
            (X.presheaf.map (homOfLE h).op).hom c • ⟨_, haW⟩ from rfl,
          show (⟨c • a, hca⟩ : ↥(baseSpan A fX ((J ^ d : Ideal A) ^ n) F V)) =
            c • ⟨a, hsub ha⟩ from rfl,
          map_smul, map_smul, iha haW (hsub ha), F.map_smul (homOfLE h)]
  exact key s ((span_smul_pairs (M := Γ(F, V)) (baseSectionHom A fX V)
    ((J ^ d : Ideal A) ^ n)).ge hs) _ hs

/-! ### The glueing -/

/-- **The local data the glueing of `Stacks.Coherent.gradedComponentLift` consumes.** -/
public def gradedLocalData
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) :
    LocalData F F (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F) where
  D V := baseSpan A fX ((J ^ d : Ideal A) ^ n) F V
  le_P V _s hs := baseSpan_le_idealPowerMultiple A J fX F (n * d) V
    (by rwa [pow_pow_eq_pow_mul] at hs)
  map_mem h _s hs := map_mem_baseSpan A fX _ F h hs
  μ V s hs := gradedComponentLift hkill n σ V ⟨s, hs⟩
  μ_add V s t hs ht := map_add (gradedComponentLift hkill n σ V) ⟨s, hs⟩ ⟨t, ht⟩
  μ_smul V c s hs := map_smul (gradedComponentLift hkill n σ V) c ⟨s, hs⟩
  μ_map h s hs := gradedComponentLift_map hkill n σ h s hs
  loc V s hs x hx := by
    refine loc_idealPowerMultiple A J fX F (n * d) V s hs x hx |>.imp fun W => ?_
    refine Exists.imp fun hW => And.imp_right fun hmem => ?_
    rwa [pow_pow_eq_pow_mul]

/-- **Stacks Project, Tag 0EH6**, the existence of the graded map, granted that the splitting
kills the relations of the sections over every open.

The components are the glueings of the per-open maps relation-killing supplies; the
local-section formula is their defining property, read through
`Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.gluedHom_app_of_mem`. -/
public theorem exists_gradedSplitting_of_killsRelationsHom (A : Type u) [CommRing A]
    (J : Ideal A) {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (F : X.Modules) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (hkill : ∀ V : X.Opens, KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ) :
    ∃ Ψ : GradedSplittingComponents A J fX F r d, IsGradedSplitting A J fX F d ψ Ψ := by
  refine ⟨fun σ => (gradedLocalData hkill (Finsupp.degree σ) σ).gluedHom,
    fun σ U g hg m hmem => ?_⟩
  have hgK : g ∈ ((J ^ d : Ideal A) ^ Finsupp.degree σ) :=
    mem_pow_pow_of_mem_pow_mul J d (Finsupp.degree σ) hg
  have hs : baseSectionHom A fX U g • m ∈
      baseSpan A fX ((J ^ d : Ideal A) ^ Finsupp.degree σ) F U :=
    mem_baseSpan A fX F U hgK m
  refine ((gradedLocalData hkill (Finsupp.degree σ) σ).gluedHom_app_of_mem U _ hs).trans ?_
  refine (gradedComponentLift_apply hkill (Finsupp.degree σ) σ U g hgK m hs).trans ?_
  refine congrArg (fun a => baseSectionHom A fX U a • m) ?_
  exact extendCoeff_apply J d (Finsupp.degree σ) ψ σ g hgK
    (reesMonomial J d (Finsupp.degree σ) ⟨g, hg⟩).2

/-! ### From the affine opens to every open -/

/-- The affine opens inside an open cover it. -/
public lemma le_iSup_affineOpens_le {X : Scheme.{u}} (V : X.Opens) :
    V ≤ ⨆ W : { W : X.affineOpens // W.1 ≤ V }, W.1.1 := by
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWsub⟩, hxW⟩

/-- A section of a sheaf of modules vanishing on every affine open inside its domain is zero. -/
public lemma eq_zero_of_map_affineOpens_eq_zero {X : Scheme.{u}} (F : X.Modules) (V : X.Opens)
    (s : Γ(F, V)) (h : ∀ W : { W : X.affineOpens // W.1 ≤ V },
      F.presheaf.map (homOfLE W.2).op s = 0) : s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf F.isSheaf
    (fun W : { W : X.affineOpens // W.1 ≤ V } => W.1.1) (fun W => W.2)
    (le_iSup_affineOpens_le V) fun W => ?_
  have h2 : F.presheaf.map (homOfLE W.2).op (0 : Γ(F, V)) = 0 := map_zero _
  exact (h W).trans h2.symm

/-- **Relation-killing over the affine opens gives it over every open.**

The restrictions to the affine opens inside `V` are jointly injective, because `F` is a sheaf and
the affine opens form a basis, and they are compatible with the scalars by
`Stacks.Coherent.baseSectionHom_map`; so `Stacks.ReesAlgebra.killsRelationsHom_of_compat`
applies. -/
public theorem killsRelationsHom_sections_of_affineOpens (A : Type u) [CommRing A] (J : Ideal A)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (F : X.Modules) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (haff : ∀ W : X.affineOpens, KillsRelationsHom (baseSectionHom A fX W.1) Γ(F, W.1) J d ψ)
    (V : X.Opens) : KillsRelationsHom (baseSectionHom A fX V) Γ(F, V) J d ψ := by
  refine killsRelationsHom_of_compat (baseSectionHom A fX V)
    (ι := { W : X.affineOpens // W.1 ≤ V })
    (fun W => baseSectionHom A fX W.1.1)
    (fun W => (F.presheaf.map (homOfLE W.2).op).hom) ?_ ?_ fun W => haff W.1
  · intro W a x
    exact map_baseSectionHom_smul A fX F W.2 a x
  · intro s hs
    exact eq_zero_of_map_affineOpens_eq_zero F V s hs

/-- **Stacks Project, Tag 0EH6**, the existence of the graded map, granted that the splitting
kills the relations of the sections over every *affine* open.

That relation-killing hypothesis is not proved here, so Tag 0EH6 is not registered on this
theorem. -/
public theorem exists_gradedSplitting_of_killsRelationsHom_affineOpens (A : Type u) [CommRing A]
    (J : Ideal A) {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (F : X.Modules) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (haff : ∀ W : X.affineOpens, KillsRelationsHom (baseSectionHom A fX W.1) Γ(F, W.1) J d ψ) :
    ∃ Ψ : GradedSplittingComponents A J fX F r d, IsGradedSplitting A J fX F d ψ Ψ :=
  exists_gradedSplitting_of_killsRelationsHom A J fX F ψ
    (killsRelationsHom_sections_of_affineOpens A J fX F ψ haff)

end Stacks.Coherent

end
