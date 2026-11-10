module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSpanDescent

/-!
# The subsheaf of sections whose coaction lands in a given submodule

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `ℱ` a quasi-coherent module on
its fppf site, `u` an object of `𝒳` and `H ⊆ ℱ(u)` a submodule.  The sections `g ∈ ℱ(y)` such that
for every pair of arrows `c : z ⟶ y`, `b : z ⟶ u` out of an object `z` over an affine scheme the
restriction `c^*g` lies in the `Γ(z)`-span of `b^*H` form a subsheaf `ℱ ∩ u_*H` of `ℱ`.

When `u` is a smooth chart and `ℱ ↔ (M, ψ)` is read as a comodule over the groupoid
`u ×_𝒳 u`, its sections over `u` are the elements of `M` whose coaction lies in `H ⊗ Γ(u ×_𝒳 u)`;
this is the module `ℱ ∩ s_*t^*ℋ` of the proof of Stacks 0GPS, built here without the groupoid.

## Main definitions

* `AlgebraicGeometry.FibredSite.comoduleSubmodule`: the sections over one object.
* `AlgebraicGeometry.FibredSite.comoduleSubsheaf`: the subsheaf.
* `AlgebraicGeometry.FibredSite.IsUniversalPair`: a pair of arrows `w ⟶ y`, `w ⟶ u` through which
  every pair out of an object over an affine scheme factors fppf locally (the affine objects of the
  fibre product `y ×_𝒳 u`).

## Main results

* `AlgebraicGeometry.FibredSite.comoduleSubmodule_le`: over `u` the sections lie in `H`.
* `AlgebraicGeometry.FibredSite.mem_comoduleSubmodule_iff_of_isUniversalPair`: over an object
  with a universal pair the condition is a single one.
* `AlgebraicGeometry.FibredSite.exists_fg_mem_comoduleSubmodule`: every section over `u` lies in
  the subsheaf of a finitely generated `H`, given a universal pair over an affine scheme for
  `(u, u)`.

## References

* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

attribute [local instance] objModule

section Universal

variable (B S hS p)

/-- **A universal pair** for `(y, u)`: arrows `pr₁ : w ⟶ y` and `pr₂ : w ⟶ u` through which every
pair `c : z ⟶ y`, `b : z ⟶ u` out of an object over an affine scheme factors on the members over
affine schemes of an fppf covering sieve of `z`. -/
def IsUniversalPair {y u w : 𝒳} (pr₁ : w ⟶ y) (pr₂ : w ⟶ u) : Prop :=
  ∀ ⦃z : 𝒳⦄ (c : z ⟶ y) (b : z ⟶ u), IsAffineOver B S hS (p.obj z) →
    ∃ T : Sieve z, T ∈ BigFppfOver.associatedTopology B S hS p .fppf z ∧
      ∀ ⦃z' : 𝒳⦄ (g : z' ⟶ z), T g → IsAffineOver B S hS (p.obj z') →
        ∃ r : z' ⟶ w, r ≫ pr₁ = g ≫ c ∧ r ≫ pr₂ = g ≫ b

end Universal

variable (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) {u : 𝒳}
  (H : Submodule (objRing B S hS p u) (F.val.obj (op u)))

/-- **The sections of `ℱ ∩ u_*H` over `y`**: the `g ∈ ℱ(y)` such that `c^*g` lies in the
`Γ(z)`-span of `b^*H` for all arrows `c : z ⟶ y`, `b : z ⟶ u` out of objects over affine
schemes. -/
def comoduleSubmodule (y : 𝒳) : Submodule (objRing B S hS p y) (F.val.obj (op y)) :=
  ⨅ (z : 𝒳) (c : z ⟶ y) (b : z ⟶ u) (_ : IsAffineOver B S hS (p.obj z)),
    (restrictedSpan F b H).comap (F.val.restrictₛₗ c.op)

variable {F} in
/-- The `Γ(y)`-span of the restriction of a submodule `N ⊆ ℱ(y)` along `𝟙 y` is `N`. -/
theorem restrictedSpan_id {y : 𝒳} (N : Submodule (objRing B S hS p y) (F.val.obj (op y))) :
    restrictedSpan F (𝟙 y) N = N := by
  have e : (F.val.restrictₛₗ (𝟙 y).op '' (N : Set (F.val.obj (op y)))) = N := by
    ext x; constructor
    · rintro ⟨n, hn, rfl⟩; rw [restrictₛₗ_id_apply F]; exact hn
    · intro hx; exact ⟨x, hx, restrictₛₗ_id_apply F x⟩
  rw [restrictedSpan, e, Submodule.span_eq]

variable {F H} in
/-- `g ∈ ℱ ∩ u_*H` over `y` if and only if `c^*g` lies in the `Γ(z)`-span of `b^*H` for all
arrows `c : z ⟶ y`, `b : z ⟶ u` out of objects over affine schemes. -/
theorem mem_comoduleSubmodule_iff {y : 𝒳} {g : F.val.obj (op y)} :
    g ∈ comoduleSubmodule F H y ↔ ∀ ⦃z : 𝒳⦄ (c : z ⟶ y) (b : z ⟶ u),
      IsAffineOver B S hS (p.obj z) → F.val.restrictₛₗ c.op g ∈ restrictedSpan F b H := by
  simp only [comoduleSubmodule, Submodule.mem_iInf]
  rfl

variable {F H} in
/-- The restriction along `k : y' ⟶ y` of a section of `ℱ ∩ u_*H` over `y` is a section of
`ℱ ∩ u_*H` over `y'`. -/
theorem map_mem_comoduleSubmodule {y y' : 𝒳} (k : y' ⟶ y) {g : F.val.obj (op y)}
    (hg : g ∈ comoduleSubmodule F H y) : F.val.restrictₛₗ k.op g ∈ comoduleSubmodule F H y' := by
  refine mem_comoduleSubmodule_iff.2 fun z c b hz => ?_
  rw [← restrictₛₗ_comp_apply]
  exact mem_comoduleSubmodule_iff.1 hg (c ≫ k) b hz

/-- A section of `ℱ ∩ u_*H` over an object `y` over an affine scheme lies in the span of `b^*H`
for every `b : y ⟶ u`. -/
private theorem mem_restrictedSpan_of_mem_comoduleSubmodule {y : 𝒳}
    (hy : IsAffineOver B S hS (p.obj y)) (b : y ⟶ u) {g : F.val.obj (op y)}
    (hg : g ∈ comoduleSubmodule F H y) : g ∈ restrictedSpan F b H := by
  simpa only [restrictₛₗ_id_apply F] using mem_comoduleSubmodule_iff.1 hg (𝟙 y) b hy

/-- **Over `u` itself the sections of `ℱ ∩ u_*H` lie in `H`**, when `u` lies over an affine
scheme. -/
theorem comoduleSubmodule_le (hu : IsAffineOver B S hS (p.obj u)) :
    comoduleSubmodule F H u ≤ H := by
  intro g hg
  simpa only [restrictedSpan_id] using mem_restrictedSpan_of_mem_comoduleSubmodule F H hu (𝟙 u) hg

variable {F H} in
include hp in
/-- **A single condition suffices over an object with a universal pair.**  If `pr₁ : w ⟶ y`,
`pr₂ : w ⟶ u` is a universal pair and `pr₁^*g` lies in the span of `pr₂^*H`, then
`g ∈ ℱ ∩ u_*H`. -/
theorem mem_comoduleSubmodule_of_isUniversalPair (hF : F.IsQuasicoherentOnSite) {y w : 𝒳}
    {pr₁ : w ⟶ y} {pr₂ : w ⟶ u} (hpr : IsUniversalPair B S hS p pr₁ pr₂)
    {g : F.val.obj (op y)} (hg : F.val.restrictₛₗ pr₁.op g ∈ restrictedSpan F pr₂ H) :
    g ∈ comoduleSubmodule F H y := by
  refine mem_comoduleSubmodule_iff.2 fun z c b hz => ?_
  obtain ⟨T, hT, hfac⟩ := hpr c b hz
  refine mem_of_forall_mem_restrictedSpan F hF hz _ hT fun z' g' hg' hz' => ?_
  obtain ⟨r, hr₁, hr₂⟩ := hfac g' hg' hz'
  rw [← restrictedSpan_comp, ← restrictₛₗ_comp_apply, ← hr₁, ← hr₂, restrictₛₗ_comp_apply]
  exact map_mem_restrictedSpan_comp F pr₂ r hg

variable {F H} in
include hp in
/-- If `pr₁ : w ⟶ y`, `pr₂ : w ⟶ u` is a universal pair with `w` over an affine scheme, then
`g ∈ ℱ ∩ u_*H` if and only if `pr₁^*g` lies in the `Γ(w)`-span of `pr₂^*H`. -/
theorem mem_comoduleSubmodule_iff_of_isUniversalPair (hF : F.IsQuasicoherentOnSite) {y w : 𝒳}
    {pr₁ : w ⟶ y} {pr₂ : w ⟶ u} (hpr : IsUniversalPair B S hS p pr₁ pr₂)
    (hw : IsAffineOver B S hS (p.obj w)) {g : F.val.obj (op y)} :
    g ∈ comoduleSubmodule F H y ↔ F.val.restrictₛₗ pr₁.op g ∈ restrictedSpan F pr₂ H :=
  ⟨fun hg => mem_comoduleSubmodule_iff.1 hg pr₁ pr₂ hw,
    mem_comoduleSubmodule_of_isUniversalPair hF hpr⟩

include hp in
/-- **`ℱ ∩ u_*H` is a sheaf**: membership is fppf local. -/
theorem mem_comoduleSubmodule_of_locally (hF : F.IsQuasicoherentOnSite) {y : 𝒳}
    (g : F.val.obj (op y)) {T : Sieve y}
    (hT : T ∈ BigFppfOver.associatedTopology B S hS p .fppf y)
    (hg : ∀ ⦃y' : 𝒳⦄ (k : y' ⟶ y), T k → F.val.restrictₛₗ k.op g ∈ comoduleSubmodule F H y') :
    g ∈ comoduleSubmodule F H y := by
  refine mem_comoduleSubmodule_iff.2 fun z c b hz => ?_
  refine mem_of_forall_mem_restrictedSpan F hF hz _
    ((BigFppfOver.associatedTopology B S hS p .fppf).pullback_stable c hT) fun z' g' hg' hz' => ?_
  rw [← restrictedSpan_comp, ← restrictₛₗ_comp_apply]
  exact mem_restrictedSpan_of_mem_comoduleSubmodule F H hz' _ (hg (g' ≫ c) hg')

/-- **The subsheaf `ℱ ∩ u_*H`** of `ℱ`. -/
def comoduleSubsheaf (hF : F.IsQuasicoherentOnSite) : F.Submodule where
  obj Y := comoduleSubmodule F H Y.unop
  map {Y Y'} k g hg := by
    have h := map_mem_comoduleSubmodule (F := F) (H := H) k.unop hg
    exact h
  isSheaf {Y} g hg := by
    refine mem_comoduleSubmodule_of_locally F H hF g hg fun y' k hk => ?_
    exact hk

variable {F H} in
include hp in
/-- **Every section over `u` lies in `ℱ ∩ u_*H` for some finitely generated `H`**, given a
universal pair `pr₁, pr₂ : w ⟶ u` with `w` over an affine scheme and `u` over an affine scheme. -/
theorem exists_fg_mem_comoduleSubmodule (hF : F.IsQuasicoherentOnSite)
    (hu : IsAffineOver B S hS (p.obj u)) {w : 𝒳} (hw : IsAffineOver B S hS (p.obj w))
    {pr₁ pr₂ : w ⟶ u} (hpr : IsUniversalPair B S hS p pr₁ pr₂) (f : F.val.obj (op u)) :
    ∃ H : Submodule (objRing B S hS p u) (F.val.obj (op u)), H.FG ∧
      f ∈ comoduleSubmodule F H u := by
  classical
  let := objAlgebra B S hS p pr₂
  let : Module (objRing B S hS p u) (F.val.obj (op w)) :=
    Module.compHom _ (algebraMap (objRing B S hS p u) (objRing B S hS p w))
  have : IsScalarTower (objRing B S hS p u) (objRing B S hS p w) (F.val.obj (op w)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj := (bijective_liftBaseChange_of_eq_restriction F hF pr₂ hu hw
    (restrictionLinear F pr₂) fun _ => rfl).2
  have hrange : ∀ t : TensorProduct (objRing B S hS p u) (objRing B S hS p w) (F.val.obj (op u)),
      (restrictionLinear F pr₂).liftBaseChange (objRing B S hS p w) t ∈
        Submodule.span (objRing B S hS p w) (Set.range (restrictionLinear F pr₂)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c m =>
      rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  obtain ⟨t, ht⟩ := hsurj (F.val.restrictₛₗ pr₁.op f)
  have hmem := hrange t
  rw [ht] at hmem
  obtain ⟨T, hTsub, hT⟩ := Submodule.mem_span_finite_of_mem_span hmem
  choose m hm using fun x : (T : Set (F.val.obj (op w))) => hTsub x.2
  refine ⟨Submodule.span _ (Set.range m), Submodule.fg_span (Set.finite_range m), ?_⟩
  refine mem_comoduleSubmodule_of_isUniversalPair hF hpr ?_
  refine Submodule.span_mono ?_ hT
  intro x hx
  exact ⟨m ⟨x, hx⟩, Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩, hm ⟨x, hx⟩⟩

end AlgebraicGeometry.FibredSite

end
