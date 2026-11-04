module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.NonvanishingEq
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.LinearAlgebra.SymmetricPower.DegreeOneGeneration

/-!
# The hyperplane of a rational point of a projective space

Let `k` be a field and `V` a `k`-module. A point `q` of `P(V) = Proj (Sym_k V)` whose residue
field is `k` has a hyperplane of degree-one forms: the vectors `v` with `ι v` in the homogeneous
prime of `q` are exactly the kernel of a nonzero linear functional on `V`. Consequently that
hyperplane cuts out `q` alone, and over an infinite field a single degree-one form vanishes at a
rational point and at none of finitely many other points.

## Main definitions

* `AlgebraicGeometry.IsRationalPoint`: the canonical map `k → κ(x)` from the base field to the
  residue field at a point of a `k`-scheme is an isomorphism.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_dual_pointSubmodule_eq_ker`: the degree-one
  forms vanishing at a `k`-rational point of `P(V)` are the kernel of a nonzero functional.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace_pointSubmodule_of_isRationalPoint`
  and `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_of_pointSubmodule_le`: that hyperplane cuts
  out the rational point alone.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_mem_pointSubmodule_forall_notMem`: over an
  infinite field one degree-one form vanishes at a rational point and at none of finitely many
  points distinct from it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_homogeneousSection_vanishing_at_point`:
  the same statement for the global section `ι v / 1` of `𝒪_{P(V)}(1)` that such a form
  determines; this is [Stacks, Tag 0B58] for `X = 𝐏(V)` and `ℒ = 𝒪(1)`.

## What is not proved

Tag 0B58 is stated for an arbitrary scheme `X` of finite type over `k` and an arbitrary very
ample invertible `ℒ`, and its proof opens by reducing to `X = 𝐏(V)` with `ℒ = 𝒪(1)` "by
definition of a very ample invertible sheaf". That reduction is **not** carried out here, and
the tag is attached to the case it reduces to. What the reduction needs is a comparison between
relative very ampleness, `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, whose projective
bundle is the relative `Proj` of the *sectionwise* symmetric algebra of a quasi-coherent module,
and `AlgebraicGeometry.projectiveSpaceOfModule`, whose graded ring is the symmetric algebra of
the *global sections*. Over an affine base the two schemes are identified by
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule`, and that identification *is* one
of schemes over `Spec k`
(`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule_hom_toSpec`). What it still does
not give is the sectionwise algebra: it is stated for the global-sections symmetric algebra, and
the twists are not compared along it.

## Implementation notes

The hyperplane is read off an affine chart. A vector `v₀` with `ι v₀` outside the prime of `q`
puts `q` in the standard open `D₊(ι v₀)`, which is `Spec` of the degree-zero homogeneous
localization `A = (Sym_k V)_{(ι v₀)}`; rationality of `q` gives a `k`-point of `P(V)` through
`q`, which factors through that chart as a `k`-algebra map `ψ : A → k`, and the functional is
`v ↦ ψ (ι v / ι v₀)`. Its kernel is the prime of `q` because the standard open `D₊(ι v)` pulls
back along the chart to the basic open of `ι v / ι v₀`.

Nothing here needs `V` finite-dimensional or `k` algebraically closed, which the versions in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/LinesAvoidingSubvariety.lean` for *closed*
points do. Over a field that is not algebraically closed a closed point of `P(V)` need not have
a hyperplane of degree-one forms, and rationality is exactly what repairs that.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u v

/-! ### Rational points of a scheme over a field -/

section RationalPoint

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A point `x` of a `k`-scheme is a **`k`-rational point** when the canonical map from the base
field to the residue field `κ(x)` is an isomorphism, i.e. `κ(x) = k`. -/
@[ega "I 3.4.5", sga "3 V 4.1.2" "special case"]
def IsRationalPoint (f : X ⟶ Spec (.of k)) (x : X) : Prop :=
  IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f))

variable (f : X ⟶ Spec (.of k)) (x : X) (hx : IsRationalPoint f x)

/-- The residue field at a `k`-rational point, identified with `k`. -/
def residueFieldIsoOfIsRationalPoint : X.residueField x ≅ .of k :=
  have : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := hx
  (asIso (Spec.preimage (X.fromSpecResidueField x ≫ f))).symm

@[simp]
lemma SpecMap_residueFieldIsoOfIsRationalPoint_inv :
    Spec.map (residueFieldIsoOfIsRationalPoint f x hx).inv =
      X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- The `k`-point of `X` attached to a `k`-rational point. -/
def ptOfIsRationalPoint : Spec (.of k) ⟶ X :=
  Spec.map (residueFieldIsoOfIsRationalPoint f x hx).hom ≫ X.fromSpecResidueField x

@[simp]
lemma ptOfIsRationalPoint_comp : ptOfIsRationalPoint f x hx ≫ f = 𝟙 _ := by
  rw [ptOfIsRationalPoint, Category.assoc, ← SpecMap_residueFieldIsoOfIsRationalPoint_inv f x hx,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

@[simp]
lemma ptOfIsRationalPoint_apply (a : Spec (.of k)) : (ptOfIsRationalPoint f x hx).base a = x := by
  simp [ptOfIsRationalPoint]

end RationalPoint

/-! ### The hyperplane of a rational point -/

namespace ProjectiveSpaceOfModule

open HomogeneousLocalization

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- A vector has degree `1 • 1` in the symmetric algebra, the form in which
`HomogeneousLocalization.Away.mk` asks for it. -/
theorem ι_mem_symmetricPower_one_smul (v : V) :
    SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower (1 • 1) k V := by
  simp only [smul_eq_mul, mul_one]
  exact ι_mem_symmetricPower_one k V v

variable {V}

/-- The degree-zero fraction `ι v / ι v₀` in the homogeneous localization of `Sym_k V` away from
a degree-one form `ι v₀`. -/
def awayFraction {v₀ : V} (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V)
    (v : V) : Away (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀) :=
  Away.mk _ hv₀ 1 (SymmetricAlgebra.ι k V v) (ι_mem_symmetricPower_one_smul k V v)

variable {k}

/-- The degree-zero fraction attached to a vector, read in the localization. -/
private theorem val_awayFraction {v₀ : V}
    (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V) (v : V) :
    (awayFraction k hv₀ v).val = Localization.mk (SymmetricAlgebra.ι k V v)
      ⟨SymmetricAlgebra.ι k V v₀ ^ 1, (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ :=
  rfl

/-- A degree-zero scalar is the fraction with denominator one. -/
private theorem val_fromZeroRingHom (x : Submonoid (SymmetricAlgebra k V))
    (c : SymPow.symmetricPower 0 k V) :
    (fromZeroRingHom (fun n => SymPow.symmetricPower n k V) x c).val =
      Localization.mk (c : SymmetricAlgebra k V) 1 :=
  rfl

@[simp]
theorem awayFraction_add {v₀ : V} (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V)
    (v w : V) : awayFraction k hv₀ (v + w) = awayFraction k hv₀ v + awayFraction k hv₀ w := by
  apply val_injective
  rw [val_add, val_awayFraction, val_awayFraction, val_awayFraction, Localization.add_mk_self,
    map_add]

theorem awayFraction_self {v₀ : V} (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V) :
    awayFraction k hv₀ v₀ = 1 := by
  apply val_injective
  rw [val_one, val_awayFraction]
  simp only [pow_one]
  exact Localization.mk_self_mk _ _

/-- Scaling a vector scales its fraction by the corresponding degree-zero scalar. -/
theorem awayFraction_smul {v₀ : V}
    (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V) (c : k) (v : V) :
    awayFraction k hv₀ (c • v) =
      fromZeroRingHom (fun n => SymPow.symmetricPower n k V) _
          (algebraMap k (SymPow.symmetricPower 0 k V) c) * awayFraction k hv₀ v := by
  apply val_injective
  rw [val_mul, val_awayFraction, val_awayFraction, val_fromZeroRingHom, Localization.mk_mul,
    one_mul, map_smul, Algebra.smul_def]
  rfl

/-- **The hyperplane of a rational point.** The degree-one forms vanishing at a `k`-rational
point of `P(V)` are exactly the kernel of a nonzero linear functional on `V`.

This is where rationality of the point enters, and it is the only place it is used: the chart
`D₊(ι v₀)` around the point is the spectrum of the degree-zero homogeneous localization, the
rational point is a `k`-algebra map from that localization to `k`, and the functional is the
value of that map on `ι v / ι v₀`. -/
@[sga "7 XVII 2.1" "partial"]
theorem exists_dual_pointSubmodule_eq_ker (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    (q : projectiveSpaceOfModule k V)
    (hq : IsRationalPoint (projectiveSpaceOfModuleToSpec k V) q) :
    ∃ φ : Module.Dual k V, φ ≠ 0 ∧ pointSubmodule k V q = LinearMap.ker φ := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ι_notMem k V q
  obtain ⟨cp⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  have hdeg : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V :=
    ι_mem_symmetricPower_one k V v₀
  -- the affine chart `D₊(ι v₀)` around the point
  have hrange : Set.range (ptOfIsRationalPoint (projectiveSpaceOfModuleToSpec k V) q hq).base ⊆
      Set.range (Proj.awayι (fun n => SymPow.symmetricPower n k V)
        (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos).base := by
    rintro _ ⟨a, rfl⟩
    rw [ptOfIsRationalPoint_apply]
    have hmem : q ∈ (↑(Proj.awayι (fun n => SymPow.symmetricPower n k V)
        (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos).opensRange :
          Set (projectiveSpaceOfModule k V)) := by
      rw [Proj.opensRange_awayι]
      exact hv₀
    exact hmem
  -- the rational point, read on that chart as a `k`-algebra map `ψ` to `k`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : CommRingCat.of (Away (fun n => SymPow.symmetricPower n k V)
        (SymmetricAlgebra.ι k V v₀)) ⟶ CommRingCat.of k,
      Spec.map ψ ≫ Proj.awayι (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos =
        ptOfIsRationalPoint (projectiveSpaceOfModuleToSpec k V) q hq :=
    ⟨Spec.preimage (IsOpenImmersion.lift _ _ hrange),
      by rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ hrange⟩
  have hqψ : (Spec.map ψ ≫ Proj.awayι (fun n => SymPow.symmetricPower n k V)
      (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos).base cp = q := by
    rw [hψ, ptOfIsRationalPoint_apply]
  -- `ψ` is a `k`-algebra map: the point is a point over `Spec k`
  have hψk : ∀ c : k, ψ.hom (fromZeroRingHom (fun n => SymPow.symmetricPower n k V)
      (Submonoid.powers (SymmetricAlgebra.ι k V v₀))
      (algebraMap k (SymPow.symmetricPower 0 k V) c)) = c := by
    have hcomp : CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V)) ≫
        CommRingCat.ofHom (fromZeroRingHom (fun n => SymPow.symmetricPower n k V)
          (Submonoid.powers (SymmetricAlgebra.ι k V v₀))) ≫ ψ = 𝟙 (CommRingCat.of k) := by
      apply Spec.map_injective
      rw [Spec.map_id, Spec.map_comp, Spec.map_comp,
        ← Proj.awayι_toSpecZero (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos, Category.assoc, Category.assoc,
        ← Category.assoc (Spec.map ψ), hψ]
      exact ptOfIsRationalPoint_comp _ _ hq
    exact fun c => congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of k => g.hom c) hcomp
  -- the fraction `ι v / ι v₀` is killed by `ψ` exactly when `ι v` lies in the prime of `q`
  have hbot : ∀ (b : Spec (CommRingCat.of k)) (z : k), z ∈ b.asIdeal ↔ z = 0 := by
    intro b z
    rw [(Ideal.eq_bot_or_top b.asIdeal).resolve_right b.isPrime.ne_top, Ideal.mem_bot]
  have hmem : ∀ v : V, ψ.hom (awayFraction k hdeg v) = 0 ↔
      SymmetricAlgebra.ι k V v ∈ q.asHomogeneousIdeal := by
    intro v
    have hdv : SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower 1 k V :=
      ι_mem_symmetricPower_one k V v
    have hiso : Away.isLocalizationElem (𝒜 := fun n => SymPow.symmetricPower n k V)
        (d := 1) (e := 1) hdeg hdv = awayFraction k hdeg v := by
      apply val_injective
      rw [val_awayFraction]
      change Localization.mk _ _ = Localization.mk _ _
      simp only [pow_one]
    have hpre : Proj.awayι (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos ⁻¹ᵁ
            Proj.basicOpen (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v) =
        PrimeSpectrum.basicOpen (awayFraction k hdeg v) := by
      rw [← hiso]
      exact Proj.awayι_preimage_basicOpen (𝒜 := fun n => SymPow.symmetricPower n k V)
        (f := SymmetricAlgebra.ι k V v₀) (g := SymmetricAlgebra.ι k V v)
        (f_deg := hdeg) (hm := Nat.one_pos) (g_deg := hdv) (hm' := Nat.one_pos)
    have h1 : q ∈ Proj.basicOpen (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v) ↔
        (Spec.map ψ).base cp ∈ Proj.awayι (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v₀) hdeg Nat.one_pos ⁻¹ᵁ
            Proj.basicOpen (fun n => SymPow.symmetricPower n k V)
              (SymmetricAlgebra.ι k V v) :=
      Iff.of_eq (congrArg (fun y : projectiveSpaceOfModule k V =>
        y ∈ Proj.basicOpen (fun n => SymPow.symmetricPower n k V)
          (SymmetricAlgebra.ι k V v)) hqψ.symm)
    have h2 : awayFraction k hdeg v ∈ ((Spec.map ψ).base cp).asIdeal ↔
        ψ.hom (awayFraction k hdeg v) = 0 := by
      change awayFraction k hdeg v ∈ Ideal.comap ψ.hom cp.asIdeal ↔ _
      rw [Ideal.mem_comap]
      exact hbot cp _
    have h4 : SymmetricAlgebra.ι k V v ∉ q.asHomogeneousIdeal ↔
        ψ.hom (awayFraction k hdeg v) ≠ 0 := by
      rw [← Proj.mem_basicOpen, h1, hpre]
      exact (PrimeSpectrum.mem_basicOpen _ _).trans (not_congr h2)
    exact (not_iff_not.mp h4).symm
  -- assemble the functional
  refine ⟨{ toFun := fun v => ψ.hom (awayFraction k hdeg v)
            map_add' := fun v w => by simp only [awayFraction_add, map_add]
            map_smul' := fun c v => by
              rw [awayFraction_smul hdeg c v, _root_.map_mul, hψk c]
              rfl }, ?_, ?_⟩
  · intro h0
    refine hv₀ ((hmem v₀).mp ?_)
    have h1 := LinearMap.congr_fun h0 v₀
    simpa using h1
  · ext v
    rw [mem_pointSubmodule_iff, LinearMap.mem_ker]
    exact (hmem v).symm

/-! ### The hyperplane cuts out the rational point alone -/

/-- **The hyperplane of a `k`-rational point cuts out that point alone.** The closed subset of
`P(V)` on which all the degree-one forms vanishing at a rational point vanish is the point
itself. No algebraic closedness and no finite-dimensionality is needed. -/
theorem linearSubspace_pointSubmodule_of_isRationalPoint (k V : Type u) [Field k]
    [AddCommGroup V] [Module k V] (q : projectiveSpaceOfModule k V)
    (hq : IsRationalPoint (projectiveSpaceOfModuleToSpec k V) q) :
    linearSubspace k V (pointSubmodule k V q) = {q} := by
  obtain ⟨φ, hφ, hker⟩ := exists_dual_pointSubmodule_eq_ker k V q hq
  have hmemq : q ∈ linearSubspace k V (LinearMap.ker φ) := by
    rw [← hker]
    exact (mem_linearSubspace_iff k V _ q).mpr le_rfl
  rw [linearSubspace_ker k V φ hφ, Set.mem_singleton_iff] at hmemq
  rw [hker, linearSubspace_ker k V φ hφ, hmemq]

/-- A point of `P(V)` at which every degree-one form vanishing at a `k`-rational point vanishes
is that point. -/
theorem eq_of_pointSubmodule_le (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    {q q' : projectiveSpaceOfModule k V}
    (hq : IsRationalPoint (projectiveSpaceOfModuleToSpec k V) q)
    (h : pointSubmodule k V q ≤ pointSubmodule k V q') : q' = q := by
  have hmem := (mem_linearSubspace_iff k V (pointSubmodule k V q) q').mpr h
  rwa [linearSubspace_pointSubmodule_of_isRationalPoint k V q hq, Set.mem_singleton_iff] at hmem

/-! ### A form vanishing at the rational point and at none of finitely many others -/

/-- **One degree-one form vanishing at a rational point and at no other given point.** Over an
infinite field, given a `k`-rational point `q` of `P(V)` and finitely many points distinct from
it, some vector lies in the hyperplane of `q` and in no other point's space of degree-one forms.

The hyperplane of `q` is not the union of its intersections with the other points' spaces,
because `k` is infinite and each of those intersections is proper. -/
theorem exists_mem_pointSubmodule_forall_notMem (k V : Type u) [Field k] [Infinite k]
    [AddCommGroup V] [Module k V] {ι : Type v} [Finite ι]
    (q : projectiveSpaceOfModule k V) (qs : ι → projectiveSpaceOfModule k V)
    (hq : IsRationalPoint (projectiveSpaceOfModuleToSpec k V) q)
    (hne : ∀ j, q ≠ qs j) :
    ∃ v : V, v ∈ pointSubmodule k V q ∧ ∀ j, v ∉ pointSubmodule k V (qs j) := by
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun j => (pointSubmodule k V (qs j)).comap (pointSubmodule k V q).subtype) (by
      intro j htop
      refine hne j (eq_of_pointSubmodule_le k V hq ?_).symm
      intro x hx
      have hmem : (⟨x, hx⟩ : pointSubmodule k V q) ∈
          (pointSubmodule k V (qs j)).comap (pointSubmodule k V q).subtype := by
        rw [htop]; exact Submodule.mem_top
      exact hmem)
  exact ⟨w.1, w.2, fun j hj => hw j hj⟩

/-! ### Stacks Tag 0B58 on a projective space -/

/-- **Stacks Tag 0B58 for `X = 𝐏(V)` and `ℒ = 𝒪(1)`.** Let `k` be an infinite field, `q` a
`k`-rational point of `P(V)` and `q₁, …, qₙ` finitely many points of `P(V)` distinct from `q`.
Then some vector `v` of `V` gives a global section `ι v / 1` of `𝒪_{P(V)}(1)` that vanishes at
`q` but at none of the `qⱼ`.

This is the case the source's proof reduces the lemma to; the reduction, which unfolds the
definition of a very ample invertible sheaf, is not formalized here. -/
@[stacks 0B58 "the case `X = 𝐏(V)`, `ℒ = 𝒪(1)` that the source's proof reduces the lemma to; the
reduction itself is not formalized"]
theorem exists_homogeneousSection_vanishing_at_point
    (k V : Type u) [Field k] [Infinite k] [AddCommGroup V] [Module k V]
    {ι : Type v} [Finite ι] (q : projectiveSpaceOfModule k V)
    (qs : ι → projectiveSpaceOfModule k V)
    (hq : IsRationalPoint (projectiveSpaceOfModuleToSpec k V) q)
    (hne : ∀ j, q ≠ qs j) :
    ∃ v : V,
      q ∉ Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).toRingedSpace)
          (Stacks.ProjTwistSection.twistingModule (fun n => SymPow.symmetricPower n k V) 1)
          (Stacks.ProjTwistSection.homogeneousSection (fun n => SymPow.symmetricPower n k V)
            (SymmetricAlgebra.ι k V v) (ι_mem_symmetricPower_one k V v)) ∧
      ∀ j, qs j ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).toRingedSpace)
          (Stacks.ProjTwistSection.twistingModule (fun n => SymPow.symmetricPower n k V) 1)
          (Stacks.ProjTwistSection.homogeneousSection (fun n => SymPow.symmetricPower n k V)
            (SymmetricAlgebra.ι k V v) (ι_mem_symmetricPower_one k V v)) := by
  classical
  let hinv : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule (fun n => SymPow.symmetricPower n k V) 1) :=
    Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf
      (fun n => SymPow.symmetricPower n k V)
      (SymmetricAlgebra.adjoin_symmetricPower_one_eq_top k V) 1
  have hcov : ∀ x : ProjectiveSpectrum.top (fun n => SymPow.symmetricPower n k V),
      ∃ g : SymmetricAlgebra k V, g ∈ SymPow.symmetricPower 1 k V ∧
        x ∈ ProjectiveSpectrum.basicOpen (fun n => SymPow.symmetricPower n k V) g := by
    intro x
    obtain ⟨w, hw⟩ := exists_ι_notMem k V x
    exact ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w, hw⟩
  obtain ⟨v, hv, hvs⟩ := exists_mem_pointSubmodule_forall_notMem k V q qs hq hne
  have hdict := Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen
    (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v)
    (ι_mem_symmetricPower_one k V v) hcov
  have hiff : ∀ y : projectiveSpaceOfModule k V,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).toRingedSpace)
          (Stacks.ProjTwistSection.twistingModule (fun n => SymPow.symmetricPower n k V) 1)
          (Stacks.ProjTwistSection.homogeneousSection (fun n => SymPow.symmetricPower n k V)
            (SymmetricAlgebra.ι k V v) (ι_mem_symmetricPower_one k V v)) ↔
        v ∉ pointSubmodule k V y := by
    intro y
    change y ∈ Stacks.SheafOfModules.nonvanishingOpen
      (X := (AlgebraicGeometry.Proj (fun n => SymPow.symmetricPower n k V)).toRingedSpace) _ _ ↔ _
    rw [hdict, mem_pointSubmodule_iff]
    exact Iff.rfl
  exact ⟨v, fun h => (hiff q).1 h hv, fun j => (hiff _).2 (hvs j)⟩

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
