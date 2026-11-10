module

public import StacksFrontier.Deformation.Artin.FormalObject.TruncationHom
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCovering
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Effectivity descends along finite étale extensions of complete local bases

Let `p` be a stack in groupoids over the big fppf site of `S` whose isomorphism presheaves are
algebraic spaces, for instance an algebraic stack. Let `ξ = (R, ξ_n, f_n)` be a formal object of
`p` (**Stacks 07X4**), let `R ⊆ R'` be a finite étale local extension of Noetherian complete local
`S`-algebras, and let `ξ'` be the base change of `ξ` to `R'`. If `ξ'` is realized by an object `x'`
of `p` over `Spec R'`, then `ξ` is realized by an object over `Spec R`.

This is the descent step of the proof of the essential surjectivity in **Stacks 07X8**: "Note
that `R' ⊗_R R'` is a finite product of spectra of Noetherian complete local rings to which our
current discussion applies. Denote `p_0, p_1 : Spec(R' ⊗_R R') → Spec(R')` the two projections.
By the fully faithfulness shown above there exists a canonical isomorphism
`φ : p_0^*x' → p_1^*x'` because we have such isomorphisms over
`Spec((R' ⊗_R R')/𝔪^n(R' ⊗_R R'))`. We omit the proof that the isomorphism `φ` satisfies the
cocycle condition. Since `{Spec(R') → Spec(R)}` is an fppf covering we conclude that `x'` descends
to an object `x` of `𝒳` over `Spec(R)`. We omit the proof that `x_n` is the restriction of `x` to
`Spec(R/𝔪^n)`."

## Main definitions

* `Deformation.Artin.transportAlong`: over two maps `v₀, v₁ : Y ⟶ Spec(R' / 𝔪'^{n+1})` agreeing in
  `Spec(R / 𝔪^{n+1})`, the transport of a morphism to `x'` lying over `v₀` to one lying over `v₁`,
  through the identifications of `ξ'_n` with `x'` and with `ξ_n`.

## Main results

* `Deformation.Artin.FormalObject.exists_realization_of_realization_baseChange`: the descent
  statement above.
* `Deformation.Artin.FormalObject.isEffective_of_isEffective_baseChange`: the same statement in
  terms of effectivity.

## Implementation notes

The descent datum is the morphism `σ : t ⟶ x'` over the second projection
`Spec(R' ⊗_R R') ⟶ Spec R'`, from an object `t` over the fibre product with a morphism `ρ : t ⟶ x'`
over the first. It is produced by
`Deformation.Artin.existsUnique_hom_over_of_truncations` from its values on the base-changed
thickenings, which are the transports of `ρ`. The fibre product and its triple version are not
local rings: they are spectra of finite `R`-algebras, which
`Deformation.Artin.existsUnique_hom_over_of_truncations` allows.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w w'

namespace Deformation.Artin

variable {𝒞 : Type*} [Category 𝒞] {F : Type v} [Category.{w} F] {q : F ⥤ 𝒞}

/-! ### Transport through a base-changed level -/

section Transport

variable (hq : q.IsFiberedInGroupoids) {Tn T'n T' : 𝒞} (ι' : T'n ⟶ T') (π : T'n ⟶ Tn)
  {x' ξ' ξ : F} (b : ξ' ⟶ ξ) [q.IsHomLift π b] (r : ξ' ⟶ x') [q.IsHomLift ι' r]

/-- **Transport along a base-changed level.** Let `r : ξ' ⟶ x'` lie over `ι' : T'n ⟶ T'` and
`b : ξ' ⟶ ξ` over `π : T'n ⟶ Tn`. For `v₀, v₁ : Y ⟶ T'n` with `v₀ ≫ π = v₁ ≫ π` and a morphism
`a : z ⟶ x'` over `v₀ ≫ ι'`, factor `a` through `r` over `v₀`, compose with `b`, factor back
through `b` over `v₁` and compose with `r`: the result lies over `v₁ ≫ ι'`. -/
def transportAlong {Y : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π) {z : F} (a : z ⟶ x')
    (ha : q.IsHomLift (v₀ ≫ ι') a) : z ⟶ x' :=
  haveI := ha
  haveI : q.IsHomLift v₀ (hq.fill (f := ι') (g := v₀) rfl r a) := hq.fill_isHomLift _ _ _
  hq.fill (f := π) (g := v₁) (f' := v₀ ≫ π) hv b (hq.fill (f := ι') (g := v₀) rfl r a ≫ b) ≫ r

variable {ι' π b r}

/-- The transport of `a` is `a₁ ≫ r` for lifts `a₀` of `v₀` and `a₁` of `v₁` with `a₀ ≫ r = a` and
`a₁ ≫ b = a₀ ≫ b`. -/
private theorem exists_transportAlong_factor {Y : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π)
    {z : F} (a : z ⟶ x') (ha : q.IsHomLift (v₀ ≫ ι') a) :
    ∃ a₀ a₁ : z ⟶ ξ', q.IsHomLift v₀ a₀ ∧ q.IsHomLift v₁ a₁ ∧ a₀ ≫ r = a ∧ a₁ ≫ b = a₀ ≫ b ∧
      transportAlong hq ι' π b r v₀ v₁ hv a ha = a₁ ≫ r := by
  have := ha
  have : q.IsHomLift v₀ (hq.fill (f := ι') (g := v₀) rfl r a) := hq.fill_isHomLift _ _ _
  have : q.IsHomLift v₁ (hq.fill (f := π) (g := v₁) (f' := v₀ ≫ π) hv b
      (hq.fill (f := ι') (g := v₀) rfl r a ≫ b)) := hq.fill_isHomLift _ _ _
  exact ⟨_, _, inferInstance, inferInstance, hq.fill_fac _ _ _, hq.fill_fac _ _ _, rfl⟩

/-- The characterization of the transport: if `a₀ : z ⟶ ξ'` over `v₀` factors `a` through `r` and
`a₁ : z ⟶ ξ'` over `v₁` has `a₁ ≫ b = a₀ ≫ b`, then the transport of `a` is `a₁ ≫ r`. -/
theorem transportAlong_eq {Y : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π) {z : F}
    (a : z ⟶ x') (ha : q.IsHomLift (v₀ ≫ ι') a) (a₀ a₁ : z ⟶ ξ') (h₀ : q.IsHomLift v₀ a₀)
    (h₁ : q.IsHomLift v₁ a₁) (ha₀ : a₀ ≫ r = a) (ha₁ : a₁ ≫ b = a₀ ≫ b) :
    transportAlong hq ι' π b r v₀ v₁ hv a ha = a₁ ≫ r := by
  obtain ⟨c₀, c₁, hc₀, hc₁, e₀, e₁, e⟩ :=
    exists_transportAlong_factor (b := b) (r := r) hq v₀ v₁ hv a ha
  have ec₀ : c₀ = a₀ := hq.hom_ext (f := ι') v₀ r (by rw [e₀, ha₀])
  have ec₁ : c₁ = a₁ := hq.hom_ext (f := π) v₁ b (by rw [e₁, ha₁, ec₀])
  rw [e, ec₁]

/-- The transport of a morphism over `v₀ ≫ ι'` lies over `v₁ ≫ ι'`. -/
theorem transportAlong_isHomLift {Y : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π) {z : F}
    (a : z ⟶ x') (ha : q.IsHomLift (v₀ ≫ ι') a) :
    q.IsHomLift (v₁ ≫ ι') (transportAlong hq ι' π b r v₀ v₁ hv a ha) := by
  obtain ⟨-, c₁, -, hc₁, -, -, e⟩ :=
    exists_transportAlong_factor (b := b) (r := r) hq v₀ v₁ hv a ha
  rw [e]
  infer_instance

/-- The transport does not depend on how its base maps and its morphism are spelled. -/
theorem transportAlong_congr {Y : 𝒞} {v₀ v₁ v₀' v₁' : Y ⟶ T'n} (h₀ : v₀ = v₀') (h₁ : v₁ = v₁')
    (hv : v₀ ≫ π = v₁ ≫ π) (hv' : v₀' ≫ π = v₁' ≫ π) {z : F} {a a' : z ⟶ x'} (h : a = a')
    (ha : q.IsHomLift (v₀ ≫ ι') a) (ha' : q.IsHomLift (v₀' ≫ ι') a') :
    transportAlong hq ι' π b r v₀ v₁ hv a ha = transportAlong hq ι' π b r v₀' v₁' hv' a' ha' := by
  subst h₀ h₁ h; rfl

/-- The transport is natural in its source. -/
theorem transportAlong_comp {Y Y₂ : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π) {z z₂ : F}
    (a : z ⟶ x') (ha : q.IsHomLift (v₀ ≫ ι') a) (h : Y₂ ⟶ Y) (g : z₂ ⟶ z) [q.IsHomLift h g]
    (hv₂ : (h ≫ v₀) ≫ π = (h ≫ v₁) ≫ π) (ha₂ : q.IsHomLift ((h ≫ v₀) ≫ ι') (g ≫ a)) :
    transportAlong hq ι' π b r (h ≫ v₀) (h ≫ v₁) hv₂ (g ≫ a) ha₂ =
      g ≫ transportAlong hq ι' π b r v₀ v₁ hv a ha := by
  obtain ⟨c₀, c₁, hc₀, hc₁, e₀, e₁, e⟩ :=
    exists_transportAlong_factor (b := b) (r := r) hq v₀ v₁ hv a ha
  rw [e, transportAlong_eq hq (h ≫ v₀) (h ≫ v₁) hv₂ (g ≫ a) ha₂ (g ≫ c₀) (g ≫ c₁) inferInstance
    inferInstance (by rw [Category.assoc, e₀]) (by rw [Category.assoc, Category.assoc, e₁]),
    Category.assoc]

/-- The transport is transitive. -/
theorem transportAlong_trans {Y : 𝒞} (v₀ v₁ v₂ : Y ⟶ T'n) (h₀₁ : v₀ ≫ π = v₁ ≫ π)
    (h₁₂ : v₁ ≫ π = v₂ ≫ π) (h₀₂ : v₀ ≫ π = v₂ ≫ π) {z : F} (a : z ⟶ x')
    (ha : q.IsHomLift (v₀ ≫ ι') a) (ha' : q.IsHomLift (v₁ ≫ ι')
      (transportAlong hq ι' π b r v₀ v₁ h₀₁ a ha)) :
    transportAlong hq ι' π b r v₁ v₂ h₁₂ (transportAlong hq ι' π b r v₀ v₁ h₀₁ a ha) ha' =
      transportAlong hq ι' π b r v₀ v₂ h₀₂ a ha := by
  have := ha
  set a₀ := hq.fill (f := ι') (g := v₀) rfl r a
  have h₀ : q.IsHomLift v₀ a₀ := hq.fill_isHomLift _ _ _
  set a₁ := hq.fill (f := π) (g := v₁) (f' := v₀ ≫ π) h₀₁ b (a₀ ≫ b)
  have h₁ : q.IsHomLift v₁ a₁ := hq.fill_isHomLift _ _ _
  set a₂ := hq.fill (f := π) (g := v₂) (f' := v₁ ≫ π) h₁₂ b (a₁ ≫ b)
  have h₂ : q.IsHomLift v₂ a₂ := hq.fill_isHomLift _ _ _
  have e₁ : transportAlong hq ι' π b r v₀ v₁ h₀₁ a ha = a₁ ≫ r := rfl
  rw [transportAlong_eq hq v₁ v₂ h₁₂ _ ha' a₁ a₂ h₁ h₂ e₁.symm (hq.fill_fac _ _ _),
    transportAlong_eq hq v₀ v₂ h₀₂ a ha a₀ a₂ h₀ h₂ (hq.fill_fac _ _ _)
      (by rw [hq.fill_fac, hq.fill_fac])]

end Transport

/-- **The transport commutes with passing to the next level.** -/
theorem transportAlong_succ (hq : q.IsFiberedInGroupoids) {Tn Tn₁ T'n T'n₁ T' : 𝒞}
    {ι' : T'n ⟶ T'} {π : T'n ⟶ Tn} {ι'₁ : T'n₁ ⟶ T'} {π₁ : T'n₁ ⟶ Tn₁} (s : T'n ⟶ T'n₁)
    (u : Tn ⟶ Tn₁) (_hs : s ≫ ι'₁ = ι') (_hsu : s ≫ π₁ = π ≫ u)
    {x' ξ' ξ ξ'₁ ξ₁ : F} {b : ξ' ⟶ ξ} [q.IsHomLift π b] {r : ξ' ⟶ x'} [q.IsHomLift ι' r]
    {b₁ : ξ'₁ ⟶ ξ₁} [q.IsHomLift π₁ b₁] {r₁ : ξ'₁ ⟶ x'} [q.IsHomLift ι'₁ r₁]
    (t' : ξ' ⟶ ξ'₁) [q.IsHomLift s t'] (tξ : ξ ⟶ ξ₁) (htb : t' ≫ b₁ = b ≫ tξ)
    (htr : t' ≫ r₁ = r)
    {Y : 𝒞} (v₀ v₁ : Y ⟶ T'n) (hv : v₀ ≫ π = v₁ ≫ π) (hv₁ : (v₀ ≫ s) ≫ π₁ = (v₁ ≫ s) ≫ π₁)
    {z : F} (a : z ⟶ x') (ha : q.IsHomLift (v₀ ≫ ι') a) (ha₁ : q.IsHomLift ((v₀ ≫ s) ≫ ι'₁) a) :
    transportAlong hq ι'₁ π₁ b₁ r₁ (v₀ ≫ s) (v₁ ≫ s) hv₁ a ha₁ =
      transportAlong hq ι' π b r v₀ v₁ hv a ha := by
  obtain ⟨c₀, c₁, hc₀, hc₁, e₀, e₁, e⟩ :=
    exists_transportAlong_factor (b := b) (r := r) hq v₀ v₁ hv a ha
  rw [e, transportAlong_eq hq (v₀ ≫ s) (v₁ ≫ s) hv₁ a ha₁ (c₀ ≫ t') (c₁ ≫ t') inferInstance
    inferInstance (by rw [Category.assoc, htr, e₀])
    (by rw [Category.assoc, Category.assoc, htb, ← Category.assoc, e₁, Category.assoc]),
    Category.assoc, htr]

/-! ### Coverings by one étale surjective morphism -/

section Cover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A single étale surjective morphism of the big fppf site generates a covering sieve, indexed
by a one-point type in any universe. -/
theorem ofArrows_pUnit_mem_topology_of_etale {V U : BigFppfOver B S hS} (f : V ⟶ U)
    [Etale ((BigFppfOver.toScheme B S hS).map f)]
    [Surjective ((BigFppfOver.toScheme B S hS).map f)] :
    Sieve.ofArrows (fun _ : PUnit.{w' + 1} => V) (fun _ => f) ∈
      BigFppfOver.topology B S hS U := by
  have h := BigFppfOver.ofArrows_mem_topology_of_etale B S hS (I := PUnit.{u + 2})
    (fun _ => V) (fun _ => f) (fun _ => inferInstance)
    (fun y => ⟨PUnit.unit, ((BigFppfOver.toScheme B S hS).map f).surjective y⟩)
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using h

end Cover

/-! ### The descent -/

section Descent

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Effectivity descends along a finite étale extension of complete local bases** (the descent
step of the essential surjectivity in Stacks 07X8). Let `p` be a stack in groupoids over the big
fppf site of `S` whose isomorphism presheaves are algebraic spaces, `ξ` a formal object of `p`
whose complete local base `R` has its spectrum in the site, and `R ⊆ R'` a finite étale local
extension of complete local bases over `S`. If the base change of `ξ` to `R'` is realized by an
object over `Spec R'`, then `ξ` is realized by an object over `Spec R`. -/
theorem FormalObject.exists_realization_of_realization_baseChange
    (hp : p.IsFiberedInGroupoids)
    (hst : p.IsStackInGroupoids.{w'} (BigFppfOver.topology B S hS))
    (hI : letI : p.IsFibered := hp.isFibered; IsAlgebraicSpaceIsom p)
    (ξ : FormalObject B S hS p) (hA : B.Contains (Spec (.of ξ.base.R)))
    (A' : FormalBase S) [Algebra ξ.base.R A'.R] [IsLocalHom (algebraMap ξ.base.R A'.R)]
    [Module.Finite ξ.base.R A'.R] [Algebra.Etale ξ.base.R A'.R]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R A'.R)) ≫ ξ.base.toS = A'.toS)
    (hA' : B.Contains (Spec (.of A'.R)))
    {x' : F} (hx' : p.obj x' = baseOver B S hS A' hA')
    (R' : (ξ.baseChange hp A' (algebraMap ξ.base.R A'.R) hφ
      (truncationContains B S A' hA')).Realization hA' x' hx') :
    ∃ (x : F) (hx : p.obj x = baseOver B S hS ξ.base hA), Nonempty (ξ.Realization hA x hx) := by
  classical
  let : p.IsFibered := hp.isFibered
  let c' : ∀ n, B.Contains (A'.truncation n) := truncationContains B S A' hA'
  let T := baseOver B S hS ξ.base hA
  let T' := baseOver B S hS A' hA'
  let π : T' ⟶ T := baseOverMap ξ.base A' hφ hA hA'
  let ιn : ∀ n, truncationOver B S hS ξ.base ξ.contains n ⟶ T :=
    fun n => restrictionToBase B S hS ξ.base hA ξ.contains n
  let ι'n : ∀ n, truncationOver B S hS A' c' n ⟶ T' :=
    fun n => restrictionToBase B S hS A' hA' c' n
  let πn : ∀ n, truncationOver B S hS A' c' n ⟶ truncationOver B S hS ξ.base ξ.contains n :=
    fun n => truncationOverMap ξ.base A' (algebraMap ξ.base.R A'.R) hφ ξ.contains c' n
  have hsq : ∀ n, πn n ≫ ιn n = ι'n n ≫ π := fun n =>
    truncationOverMap_restrictionToBase ξ.base A' hφ hA hA' ξ.contains c' n
  have hpb : ∀ n, IsPullback (ι'n n) (πn n) π (ιn n) := fun n =>
    isPullback_truncationOverMap ξ.base A' hφ hA hA' ξ.contains c' n
  have hsucc : ∀ n, truncationOverSucc B S hS ξ.base ξ.contains n ≫ ιn (n + 1) = ιn n :=
    fun n => restrictionToBase_succ B S hS ξ.base hA ξ.contains n
  have hsucc' : ∀ n, truncationOverSucc B S hS A' c' n ≫ ι'n (n + 1) = ι'n n :=
    fun n => restrictionToBase_succ B S hS A' hA' c' n
  have hsuccπ : ∀ n, truncationOverSucc B S hS A' c' n ≫ πn (n + 1) =
      πn n ≫ truncationOverSucc B S hS ξ.base ξ.contains n :=
    fun n => truncationOverSucc_truncationOverMap ξ.base A' _ hφ ξ.contains c' n
  set ξ' := ξ.baseChange hp A' (algebraMap ξ.base.R A'.R) hφ c' with hξ'
  let b : ∀ n, ξ'.level n ⟶ ξ.level n := fun n => ξ.baseChangeπ hp A' _ hφ c' n
  have hb : ∀ n, p.IsHomLift (πn n) (b n) := fun n => ξ.isHomLift_baseChangeπ hp A' _ hφ c' n
  have hbt : ∀ n, ξ'.transition n ≫ b (n + 1) = b n ≫ ξ.transition n := fun n =>
    ξ.transition_baseChangeπ hp A' _ hφ c' n
  have hr' : ∀ n, p.IsHomLift (ι'n n) (R'.r n) := fun n => by
    refine IsHomLift.of_fac' _ _ _ (ξ'.level_eq n) hx' ?_
    rw [R'.map_eq n]
    rfl
  have ht' : ∀ n, p.IsHomLift (truncationOverSucc B S hS A' c' n) (ξ'.transition n) :=
    ξ'.transition_lift
  have htξ : ∀ n, p.IsHomLift (truncationOverSucc B S hS ξ.base ξ.contains n) (ξ.transition n) :=
    ξ.transition_lift
  have hπ : (BigFppfOver.toScheme B S hS).map π =
      Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R A'.R)) := rfl
  have hπfin : IsFinite ((BigFppfOver.toScheme B S hS).map π) := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R A'.R))) := by
      rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.2 inferInstance
    exact this
  have hπet : Etale ((BigFppfOver.toScheme B S hS).map π) := by
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R A'.R))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.2 inferInstance
    exact this
  have hπsurj : Surjective ((BigFppfOver.toScheme B S hS).map π) := by
    have : Module.FaithfullyFlat ξ.base.R A'.R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact ((flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 this)).2
  have hpbS : ∀ n, IsPullback ((BigFppfOver.toScheme B S hS).map (ι'n n))
      ((BigFppfOver.toScheme B S hS).map (πn n)) ((BigFppfOver.toScheme B S hS).map π)
      ((BigFppfOver.toScheme B S hS).map (ιn n)) := fun n => (hpb n).map _
  have hπnet : ∀ n, Etale ((BigFppfOver.toScheme B S hS).map (πn n)) := fun n =>
    MorphismProperty.of_isPullback (hpbS n) hπet
  have hπnsurj : ∀ n, Surjective ((BigFppfOver.toScheme B S hS).map (πn n)) := fun n =>
    MorphismProperty.of_isPullback (P := @Surjective) (hpbS n) hπsurj
  obtain ⟨W, pr₁, pr₂, hW⟩ : ∃ (W : BigFppfOver B S hS) (pr₁ pr₂ : W ⟶ T'),
      IsPullback pr₁ pr₂ π π := ⟨_, _, _, IsPullback.of_hasPullback π π⟩
  obtain ⟨W₃, s₁₂, s₂₃, hW₃⟩ : ∃ (W₃ : BigFppfOver B S hS) (s₁₂ s₂₃ : W₃ ⟶ W),
      IsPullback s₁₂ s₂₃ pr₂ pr₁ := ⟨_, _, _, IsPullback.of_hasPullback pr₂ pr₁⟩
  have hW₃w : (s₁₂ ≫ pr₁) ≫ π = (s₂₃ ≫ pr₂) ≫ π := by
    simp only [Category.assoc]
    rw [hW.w, ← Category.assoc, hW₃.w, Category.assoc, hW.w]
  let s₁₃ : W₃ ⟶ W := hW.lift (s₁₂ ≫ pr₁) (s₂₃ ≫ pr₂) hW₃w
  have hs₁₃₁ : s₁₃ ≫ pr₁ = s₁₂ ≫ pr₁ := hW.lift_fst _ _ _
  have hs₁₃₂ : s₁₃ ≫ pr₂ = s₂₃ ≫ pr₂ := hW.lift_snd _ _ _
  let fW : W ⟶ T := pr₁ ≫ π
  let fW₃ : W₃ ⟶ T := s₁₂ ≫ fW
  have hWS := hW.map (BigFppfOver.toScheme B S hS)
  have hW₃S := hW₃.map (BigFppfOver.toScheme B S hS)
  have hpr₁fin : IsFinite ((BigFppfOver.toScheme B S hS).map pr₁) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hWS.flip hπfin
  have hpr₂fin : IsFinite ((BigFppfOver.toScheme B S hS).map pr₂) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hWS hπfin
  have hs₁₂fin : IsFinite ((BigFppfOver.toScheme B S hS).map s₁₂) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hW₃S.flip hpr₁fin
  have hfW : IsFinite ((BigFppfOver.toScheme B S hS).map fW) := by
    simp only [fW, Functor.map_comp]; infer_instance
  have hfW₃ : IsFinite ((BigFppfOver.toScheme B S hS).map fW₃) := by
    simp only [fW₃, Functor.map_comp]; infer_instance
  have := hb
  have := hr'
  let trn : ∀ (n : ℕ) {Y : BigFppfOver B S hS} (v₀ v₁ : Y ⟶ truncationOver B S hS A' c' n)
      (_ : v₀ ≫ πn n = v₁ ≫ πn n) {z : F} (a : z ⟶ x') (_ : p.IsHomLift (v₀ ≫ ι'n n) a),
      z ⟶ x' := fun n _ v₀ v₁ hv _ a ha =>
    transportAlong hp (ι'n n) (πn n) (b n) (R'.r n) v₀ v₁ hv a ha
  let qW : ∀ n, pullback fW (ιn n) ⟶ truncationOver B S hS A' c' n := fun n =>
    (hpb n).lift (pullback.fst fW (ιn n) ≫ pr₁) (pullback.snd fW (ιn n))
      (by rw [Category.assoc]; exact pullback.condition (f := fW) (g := ιn n))
  let qW' : ∀ n, pullback fW (ιn n) ⟶ truncationOver B S hS A' c' n := fun n =>
    (hpb n).lift (pullback.fst fW (ιn n) ≫ pr₂) (pullback.snd fW (ιn n))
      (by rw [Category.assoc, ← hW.w, ← Category.assoc]
          exact pullback.condition (f := fW) (g := ιn n))
  have hqW₁ : ∀ n, qW n ≫ ι'n n = pullback.fst fW (ιn n) ≫ pr₁ := fun n => (hpb n).lift_fst _ _ _
  have hqW₂ : ∀ n, qW n ≫ πn n = pullback.snd fW (ιn n) := fun n => (hpb n).lift_snd _ _ _
  have hqW'₁ : ∀ n, qW' n ≫ ι'n n = pullback.fst fW (ιn n) ≫ pr₂ := fun n =>
    (hpb n).lift_fst _ _ _
  have hqW'₂ : ∀ n, qW' n ≫ πn n = pullback.snd fW (ιn n) := fun n => (hpb n).lift_snd _ _ _
  have hqWπ : ∀ n, qW n ≫ πn n = qW' n ≫ πn n := fun n => by rw [hqW₂, hqW'₂]
  have hqsucc : ∀ (pr : W ⟶ T') (q : ∀ n, pullback fW (ιn n) ⟶ truncationOver B S hS A' c' n),
      (∀ n, q n ≫ ι'n n = pullback.fst fW (ιn n) ≫ pr) →
      (∀ n, q n ≫ πn n = pullback.snd fW (ιn n)) → ∀ n,
      truncationPullbackSucc ξ.base hA ξ.contains fW n ≫ q (n + 1) =
        q n ≫ truncationOverSucc B S hS A' c' n := fun pr q hq₁ hq₂ n => by
    refine (hpb (n + 1)).hom_ext ?_ ?_
    · rw [Category.assoc, hq₁, ← Category.assoc, truncationPullbackSucc_fst, Category.assoc,
        hsucc', hq₁]
    · rw [Category.assoc, hq₂, truncationPullbackSucc_snd, Category.assoc, hsuccπ,
        ← Category.assoc, hq₂]
  have hqWsucc := hqsucc pr₁ qW hqW₁ hqW₂
  have hqW'succ := hqsucc pr₂ qW' hqW'₁ hqW'₂
  obtain ⟨t, ρ, hρ⟩ := hp.exists_lift' pr₁ x' hx'
  have htW : p.obj t = W := IsHomLift.domain_eq p pr₁ ρ
  have mkTz : ∀ {V : BigFppfOver B S hS} (f : V ⟶ T) {tt : F} (z : ℕ → F) (k : ∀ n, z n ⟶ tt),
      (∀ n, p.IsHomLift (pullback.fst f (ιn n)) (k n)) → ∃ tz : ∀ n, z n ⟶ z (n + 1),
      (∀ n, p.IsHomLift (truncationPullbackSucc ξ.base hA ξ.contains f n) (tz n)) ∧
        ∀ n, tz n ≫ k (n + 1) = k n := fun {_} f {_} z k hk => by
    have := hk
    exact ⟨fun n => hp.fill (f := pullback.fst f (ιn (n + 1)))
      (g := truncationPullbackSucc ξ.base hA ξ.contains f n) (f' := pullback.fst f (ιn n))
      (truncationPullbackSucc_fst ξ.base hA ξ.contains f n).symm (k (n + 1)) (k n),
      fun n => hp.fill_isHomLift _ _ _, fun n => hp.fill_fac _ _ _⟩
  choose z k hk using fun n => hp.exists_lift' (pullback.fst fW (ιn n)) t htW
  obtain ⟨tz, htz, htzk⟩ := mkTz fW z k hk
  have hkρ : ∀ n, p.IsHomLift (qW n ≫ ι'n n) (k n ≫ ρ) := fun n => by
    rw [hqW₁]; infer_instance
  let ψ : ∀ n, z n ⟶ x' := fun n => trn n (qW n) (qW' n) (hqWπ n) (k n ≫ ρ) (hkρ n)
  have hψl : ∀ n, p.IsHomLift (pullback.fst fW (ιn n) ≫ pr₂) (ψ n) := fun n => by
    rw [← hqW'₁]; exact transportAlong_isHomLift hp _ _ _ _ _
  have hψ : ∀ n, tz n ≫ ψ (n + 1) = ψ n := fun n => by
    have hc := transportAlong_comp hp (ι' := ι'n (n + 1)) (π := πn (n + 1)) (b := b (n + 1))
      (r := R'.r (n + 1)) (qW (n + 1)) (qW' (n + 1)) (hqWπ (n + 1)) (k (n + 1) ≫ ρ) (hkρ (n + 1))
      (truncationPullbackSucc ξ.base hA ξ.contains fW n) (tz n)
      (by rw [Category.assoc, Category.assoc, hqWπ])
      (by rw [Category.assoc]; have := hkρ (n + 1); infer_instance)
    refine hc.symm.trans ?_
    rw [transportAlong_congr hp (hqWsucc n) (hqW'succ n) _
        (by rw [Category.assoc, Category.assoc, hsuccπ, ← Category.assoc, hqWπ, Category.assoc])
        (show tz n ≫ k (n + 1) ≫ ρ = k n ≫ ρ by rw [← Category.assoc, htzk]) _
        (by rw [Category.assoc, hsucc']; exact hkρ n)]
    exact transportAlong_succ hp (truncationOverSucc B S hS A' c' n)
      (truncationOverSucc B S hS ξ.base ξ.contains n) (hsucc' n) (hsuccπ n) (ξ'.transition n)
      (ξ.transition n) (hbt n) (R'.comp_transition n) (qW n) (qW' n) (hqWπ n) _ _ (hkρ n) _
  have := htz
  have := hψl
  obtain ⟨σ, ⟨hσ, hkσ⟩, -⟩ := existsUnique_hom_over_of_truncations ξ.base hA ξ.contains fW hp hI
    htW pr₂ hx' z k tz htzk ψ hψ
  have hWlift : ∀ (n : ℕ) {Y : BigFppfOver B S hS} (v₀ v₁ : Y ⟶ truncationOver B S hS A' c' n),
      v₀ ≫ πn n = v₁ ≫ πn n → (v₀ ≫ ι'n n) ≫ π = (v₁ ≫ ι'n n) ≫ π := fun n Y v₀ v₁ hv => by
    rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hv, Category.assoc]
  have hσext : ∀ (n : ℕ) {Y : BigFppfOver B S hS} {zz : F}
      (v₀ v₁ : Y ⟶ truncationOver B S hS A' c' n) (hv : v₀ ≫ πn n = v₁ ≫ πn n) (g : zz ⟶ t)
      (_ : p.IsHomLift (hW.lift (v₀ ≫ ι'n n) (v₁ ≫ ι'n n) (hWlift n v₀ v₁ hv)) g)
      (hgρ : p.IsHomLift (v₀ ≫ ι'n n) (g ≫ ρ)),
      g ≫ σ = trn n v₀ v₁ hv (g ≫ ρ) hgρ := by
    intro n Y zz v₀ v₁ hv g hg hgρ
    have hw₁ : hW.lift (v₀ ≫ ι'n n) (v₁ ≫ ι'n n) (hWlift n v₀ v₁ hv) ≫ pr₁ = v₀ ≫ ι'n n :=
      hW.lift_fst _ _ _
    have hw₂ : hW.lift (v₀ ≫ ι'n n) (v₁ ≫ ι'n n) (hWlift n v₀ v₁ hv) ≫ pr₂ = v₁ ≫ ι'n n :=
      hW.lift_snd _ _ _
    let w' : Y ⟶ pullback fW (ιn n) :=
      pullback.lift (hW.lift (v₀ ≫ ι'n n) (v₁ ≫ ι'n n) (hWlift n v₀ v₁ hv)) (v₀ ≫ πn n) (by
        simp only [fW]; rw [← Category.assoc, hw₁, Category.assoc, ← hsq, Category.assoc])
    have hw'₁ : w' ≫ pullback.fst _ _ = hW.lift (v₀ ≫ ι'n n) (v₁ ≫ ι'n n) (hWlift n v₀ v₁ hv) :=
      pullback.lift_fst _ _ _
    have hw'₂ : w' ≫ pullback.snd _ _ = v₀ ≫ πn n := pullback.lift_snd _ _ _
    have hw'q : w' ≫ qW n = v₀ := (hpb n).hom_ext
      (by rw [Category.assoc, hqW₁, ← Category.assoc, hw'₁, hw₁])
      (by rw [Category.assoc, hqW₂, hw'₂])
    have hw'q' : w' ≫ qW' n = v₁ := (hpb n).hom_ext
      (by rw [Category.assoc, hqW'₁, ← Category.assoc, hw'₁, hw₂])
      (by rw [Category.assoc, hqW'₂, hw'₂, hv])
    have := hg
    let g' := hp.fill (f := pullback.fst fW (ιn n)) (g := w') hw'₁.symm (k n) g
    have hg'l : p.IsHomLift w' g' := hp.fill_isHomLift _ _ _
    have hg'k : g' ≫ k n = g := hp.fill_fac _ _ _
    have hv₂ : (w' ≫ qW n) ≫ πn n = (w' ≫ qW' n) ≫ πn n := by
      rw [Category.assoc, Category.assoc, hqWπ]
    have ha₂ : p.IsHomLift ((w' ≫ qW n) ≫ ι'n n) (g' ≫ k n ≫ ρ) := by
      rw [Category.assoc]; have := hkρ n; infer_instance
    calc g ≫ σ = g' ≫ ψ n := by rw [← hg'k, Category.assoc, hkσ]
      _ = trn n (w' ≫ qW n) (w' ≫ qW' n) hv₂ (g' ≫ k n ≫ ρ) ha₂ :=
          (transportAlong_comp hp _ _ _ _ _ w' g' hv₂ ha₂).symm
      _ = trn n v₀ v₁ hv (g ≫ ρ) hgρ :=
          transportAlong_congr hp hw'q hw'q' _ _ (by rw [← Category.assoc, hg'k]) _ _
  have hcocycle : ∀ (rr : F) (m₁₂ : rr ⟶ t) (m₂₃ : rr ⟶ t) (m₁₃ : rr ⟶ t),
      p.IsHomLift s₁₂ m₁₂ → p.IsHomLift s₂₃ m₂₃ → p.IsHomLift s₁₃ m₁₃ → m₁₂ ≫ σ = m₂₃ ≫ ρ →
      m₁₂ ≫ ρ = m₁₃ ≫ ρ → m₂₃ ≫ σ = m₁₃ ≫ σ := by
    intro rr m₁₂ m₂₃ m₁₃ h₁₂ h₂₃ h₁₃ e₁ e₂
    have hrr : p.obj rr = W₃ := IsHomLift.domain_eq p s₁₂ m₁₂
    choose z₃ k₃ hk₃ using fun n => hp.exists_lift' (pullback.fst fW₃ (ιn n)) rr hrr
    obtain ⟨tz₃, htz₃, htz₃k⟩ := mkTz fW₃ z₃ k₃ hk₃
    have : p.IsHomLift (s₂₃ ≫ pr₂) (m₂₃ ≫ σ) := inferInstance
    have : p.IsHomLift (s₂₃ ≫ pr₂) (m₁₃ ≫ σ) := by
      rw [← hs₁₃₂]; infer_instance
    refine hom_ext_of_truncations ξ.base hA ξ.contains fW₃ hp hI hrr (s₂₃ ≫ pr₂) hx' z₃ k₃ tz₃
      htz₃k fun n => ?_
    have hcomm : ∀ (g : W₃ ⟶ T'), g ≫ π = fW₃ → (pullback.fst fW₃ (ιn n) ≫ g) ≫ π =
        pullback.snd fW₃ (ιn n) ≫ ιn n := fun g hg => by
      rw [Category.assoc, hg]; exact pullback.condition
    have hf₀ : (s₁₂ ≫ pr₁) ≫ π = fW₃ := by simp only [fW₃, fW, Category.assoc]
    have hf₁ : (s₁₂ ≫ pr₂) ≫ π = fW₃ := by simp only [fW₃, fW, Category.assoc, hW.w]
    have hf₂ : (s₂₃ ≫ pr₂) ≫ π = fW₃ := by
      rw [← hW₃w, Category.assoc, ← hf₀, Category.assoc]
    have hu : ∀ g : W₃ ⟶ T', g ≫ π = fW₃ → ∃ u : pullback fW₃ (ιn n) ⟶ _,
        u ≫ ι'n n = pullback.fst fW₃ (ιn n) ≫ g ∧ u ≫ πn n = pullback.snd fW₃ (ιn n) :=
      fun g hg => ⟨(hpb n).lift _ _ (hcomm g hg), (hpb n).lift_fst _ _ _, (hpb n).lift_snd _ _ _⟩
    obtain ⟨u₀, hu₀, hu₀'⟩ := hu _ hf₀
    obtain ⟨u₁, hu₁, hu₁'⟩ := hu _ hf₁
    obtain ⟨u₂, hu₂, hu₂'⟩ := hu _ hf₂
    have h₀₁ : u₀ ≫ πn n = u₁ ≫ πn n := by rw [hu₀', hu₁']
    have h₁₂' : u₁ ≫ πn n = u₂ ≫ πn n := by rw [hu₁', hu₂']
    have h₀₂ : u₀ ≫ πn n = u₂ ≫ πn n := by rw [hu₀', hu₂']
    have hg : ∀ (m : W₃ ⟶ W) (m' : rr ⟶ t) (ua ub : pullback fW₃ (ιn n) ⟶ _)
        (h : ua ≫ πn n = ub ≫ πn n), p.IsHomLift m m' →
        ua ≫ ι'n n = pullback.fst fW₃ (ιn n) ≫ m ≫ pr₁ →
        ub ≫ ι'n n = pullback.fst fW₃ (ιn n) ≫ m ≫ pr₂ →
        p.IsHomLift (hW.lift (ua ≫ ι'n n) (ub ≫ ι'n n) (hWlift n ua ub h)) (k₃ n ≫ m') :=
      fun m m' ua ub h _ ha hb => by
      have : pullback.fst fW₃ (ιn n) ≫ m = hW.lift (ua ≫ ι'n n) (ub ≫ ι'n n) (hWlift n ua ub h) :=
        hW.hom_ext (by rw [hW.lift_fst, ha, Category.assoc])
          (by rw [hW.lift_snd, hb, Category.assoc])
      rw [← this]; infer_instance
    have hg₁₂ := hg s₁₂ m₁₂ u₀ u₁ h₀₁ h₁₂ hu₀ hu₁
    have hg₂₃ := hg s₂₃ m₂₃ u₁ u₂ h₁₂' h₂₃ (hu₁.trans (by rw [hW₃.w])) hu₂
    have hg₁₃ := hg s₁₃ m₁₃ u₀ u₂ h₀₂ h₁₃ (hu₀.trans (by rw [hs₁₃₁])) (hu₂.trans (by rw [hs₁₃₂]))
    have hρ₁₂ : p.IsHomLift (u₀ ≫ ι'n n) ((k₃ n ≫ m₁₂) ≫ ρ) := by
      rw [hu₀, ← Category.assoc]; infer_instance
    have hρ₂₃ : p.IsHomLift (u₁ ≫ ι'n n) ((k₃ n ≫ m₂₃) ≫ ρ) := by
      rw [hu₁, hW₃.w, ← Category.assoc]; infer_instance
    have hρ₁₃ : p.IsHomLift (u₀ ≫ ι'n n) ((k₃ n ≫ m₁₃) ≫ ρ) := by
      rw [hu₀, ← Category.assoc, Category.assoc _ s₁₂, ← hs₁₃₁, ← Category.assoc]; infer_instance
    have hρ₁₂' : p.IsHomLift (u₁ ≫ ι'n n) (trn n u₀ u₁ h₀₁ ((k₃ n ≫ m₁₂) ≫ ρ) hρ₁₂) :=
      transportAlong_isHomLift hp _ _ _ _ _
    calc k₃ n ≫ m₂₃ ≫ σ = trn n u₁ u₂ h₁₂' ((k₃ n ≫ m₂₃) ≫ ρ) hρ₂₃ := by
          rw [← Category.assoc]; exact hσext n u₁ u₂ h₁₂' _ hg₂₃ hρ₂₃
      _ = trn n u₁ u₂ h₁₂' (trn n u₀ u₁ h₀₁ ((k₃ n ≫ m₁₂) ≫ ρ) hρ₁₂) hρ₁₂' := by
          refine transportAlong_congr hp rfl rfl _ _ ?_ _ _
          rw [← hσext n u₀ u₁ h₀₁ _ hg₁₂ hρ₁₂, Category.assoc, Category.assoc, e₁]
      _ = trn n u₀ u₂ h₀₂ ((k₃ n ≫ m₁₂) ≫ ρ) hρ₁₂ :=
          transportAlong_trans hp _ _ _ _ _ _ _ _ _
      _ = trn n u₀ u₂ h₀₂ ((k₃ n ≫ m₁₃) ≫ ρ) hρ₁₃ :=
          transportAlong_congr hp rfl rfl _ _ (by rw [Category.assoc, Category.assoc, e₂]) _ _
      _ = k₃ n ≫ m₁₃ ≫ σ := by
          rw [← Category.assoc]; exact (hσext n u₀ u₂ h₀₂ _ hg₁₃ hρ₁₃).symm
  have := hπet
  have := hπsurj
  have : ∀ (_ _ : PUnit.{w' + 1}), p.IsHomLift pr₁ ρ := fun _ _ => hρ
  have : ∀ (_ _ : PUnit.{w' + 1}), p.IsHomLift pr₂ σ := fun _ _ => hσ
  obtain ⟨x, ζ, hx, hζ, hρζ⟩ := hst.exists_glue (I := PUnit.{w' + 1}) (V₁ := fun _ => T')
    (fun _ => π) (ofArrows_pUnit_mem_topology_of_etale π) (V₂ := fun _ _ => W) (fun _ _ => pr₁)
    (fun _ _ => pr₂) (fun _ _ => hW) (V₃ := fun _ _ _ => W₃) (fun _ _ _ => s₁₂)
    (fun _ _ _ => s₂₃) (fun _ _ _ => hW₃) (fun _ _ _ => s₁₃) (fun _ _ _ => hs₁₃₁)
    (fun _ _ _ => hs₁₃₂) (z := fun _ => x') (fun _ => hx') (t := fun _ _ => t) (fun _ _ => ρ)
    (fun _ _ => σ) (fun _ _ _ rr m₁₂ m₂₃ m₁₃ => hcocycle rr m₁₂ m₂₃ m₁₃)
  let ζ₀ : x' ⟶ x := ζ PUnit.unit
  have hζ₀ : p.IsHomLift π ζ₀ := hζ PUnit.unit
  have hρζ₀ : ρ ≫ ζ₀ = σ ≫ ζ₀ := hρζ PUnit.unit PUnit.unit
  have hrx : ∀ n, ∃! rx : ξ.level n ⟶ x,
      p.IsHomLift (ιn n) rx ∧ ∀ _ : PUnit.{w' + 1}, b n ≫ rx = R'.r n ≫ ζ₀ := fun n => by
    have := hπnet n
    have := hπnsurj n
    obtain ⟨P, q₁, q₂, hP⟩ : ∃ (P : BigFppfOver B S hS) (q₁ q₂ : P ⟶ truncationOver B S hS A' c' n),
        IsPullback q₁ q₂ (πn n) (πn n) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    have : ∀ _ : PUnit.{w' + 1}, p.IsHomLift (πn n) (b n) := fun _ => hb n
    have hrζ : p.IsHomLift (πn n ≫ ιn n) (R'.r n ≫ ζ₀) := by
      rw [hsq]; infer_instance
    have : ∀ k : PUnit.{w' + 1}, p.IsHomLift ((fun _ => πn n) k ≫ ιn n)
        ((fun _ => R'.r n ≫ ζ₀) k) := fun _ => hrζ
    refine hst.existsUnique_hom_of_cover (I := PUnit.{w' + 1}) (fun _ => πn n)
      (ofArrows_pUnit_mem_topology_of_etale (πn n)) (V₂ := fun _ _ => P) (fun _ _ => q₁)
      (fun _ _ => q₂) (fun _ _ => hP) (ιn n) (ξ.level_eq n) (fun _ => b n) hx
      (fun _ => R'.r n ≫ ζ₀) (fun _ _ x₂ r₁ r₂ h₁ h₂ e => ?_)
    have := h₁
    have := h₂
    let L := hW.lift (q₁ ≫ ι'n n) (q₂ ≫ ι'n n) (hWlift n q₁ q₂ hP.w)
    have hL₁ : L ≫ pr₁ = q₁ ≫ ι'n n := hW.lift_fst _ _ _
    have : p.IsHomLift (L ≫ pr₁) (r₁ ≫ R'.r n) := by rw [hL₁]; infer_instance
    let g := hp.fill (f := pr₁) (g := L) rfl ρ (r₁ ≫ R'.r n)
    have hg : p.IsHomLift L g := hp.fill_isHomLift _ _ _
    have hgρ : g ≫ ρ = r₁ ≫ R'.r n := hp.fill_fac _ _ _
    have hgρl : p.IsHomLift (q₁ ≫ ι'n n) (g ≫ ρ) := by rw [hgρ]; infer_instance
    have key := hσext n q₁ q₂ hP.w g hg hgρl
    have htr : trn n q₁ q₂ hP.w (g ≫ ρ) hgρl = r₂ ≫ R'.r n :=
      transportAlong_eq hp q₁ q₂ hP.w _ hgρl r₁ r₂ h₁ h₂ hgρ.symm e.symm
    change r₁ ≫ R'.r n ≫ ζ₀ = r₂ ≫ R'.r n ≫ ζ₀
    rw [← Category.assoc, ← hgρ, ← Category.assoc, ← htr, ← key, Category.assoc, Category.assoc,
      hρζ₀]
  choose rx hrxl hrxb using fun n => (hrx n).exists
  refine ⟨x, hx, ⟨⟨rx, fun n => ?_, fun n => ?_⟩⟩⟩
  · refine ((hrx n).unique ⟨?_, fun _ => ?_⟩ ⟨hrxl n, hrxb n⟩)
    · have := hrxl (n + 1)
      have : p.IsHomLift (truncationOverSucc B S hS ξ.base ξ.contains n ≫ ιn (n + 1))
        (ξ.transition n ≫ rx (n + 1)) := inferInstance
      rwa [hsucc] at this
    · rw [← Category.assoc, ← hbt, Category.assoc, hrxb (n + 1) PUnit.unit, ← Category.assoc,
        R'.comp_transition]
  · have := hrxl n
    rw [IsHomLift.fac' p (ιn n) (rx n)]

/-- **Effectivity descends along a finite étale extension of complete local bases**, in terms of
effectivity: if the base change of `ξ` to `R'` is effective, so is `ξ`. -/
theorem FormalObject.isEffective_of_isEffective_baseChange
    (hp : p.IsFiberedInGroupoids)
    (hst : p.IsStackInGroupoids.{w'} (BigFppfOver.topology B S hS))
    (hI : letI : p.IsFibered := hp.isFibered; IsAlgebraicSpaceIsom p)
    (ξ : FormalObject B S hS p) (hA : B.Contains (Spec (.of ξ.base.R)))
    (A' : FormalBase S) [Algebra ξ.base.R A'.R] [IsLocalHom (algebraMap ξ.base.R A'.R)]
    [Module.Finite ξ.base.R A'.R] [Algebra.Etale ξ.base.R A'.R]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap ξ.base.R A'.R)) ≫ ξ.base.toS = A'.toS)
    (hA' : B.Contains (Spec (.of A'.R)))
    (h : FormalObject.IsEffective B S hS p hp (ξ.baseChange hp A' (algebraMap ξ.base.R A'.R) hφ
      (truncationContains B S A' hA'))) :
    FormalObject.IsEffective B S hS p hp ξ := by
  obtain ⟨x', hx', ⟨R'⟩⟩ := FormalObject.exists_realization_of_isEffective
    (ξ := ξ.baseChange hp A' (algebraMap ξ.base.R A'.R) hφ (truncationContains B S A' hA'))
    (hA := hA') hp h
  obtain ⟨x, hx, ⟨R⟩⟩ := ξ.exists_realization_of_realization_baseChange hp hst hI hA A' hφ hA'
    hx' R'
  exact FormalObject.isEffective_of_realization (ξ := ξ) (hA := hA) hp R

end Descent

end Deformation.Artin

end
