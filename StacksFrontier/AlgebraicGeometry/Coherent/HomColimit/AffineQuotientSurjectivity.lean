module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AffineQuotientHom
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplaySurjectivity
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.AffineSchemeBridge

/-!
# The affine-local surjectivity of the second display of Tag 01PQ

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals of finite type, let `F` be a
quasi-coherent `𝒪_X`-module, let `F_n` be the subsheaf of sections annihilated by `Iⁿ` and write
`U = X ∖ V(I)`.  This file proves that over an **affine** open `W` every section `s ∈ Γ(U, F)`
is in the image of the second display: there are an `n` and a morphism
`θ : Iⁿ|_W ⟶ (F/F_n)|_W` whose value on the unit section of `Iⁿ` is `s`, over every open of `W`
missing the support of `I`.

This is the affine case of the surjectivity half of [Stacks, Tag 01PQ], in the language of
`𝒪_X`-modules.  What remains for the global statement is the Zariski glueing of these local
morphisms over a finite affine covering, which is where quasi-separatedness of `X` enters.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.eq_of_pow_smul_eq_of_le_basicOpen`: on an open
  contained in the basic open of `b` multiplication by a power of `b` is injective on sections
  of any `𝒪_X`-module, `b` being invertible there.  No affineness and no quasi-coherence is
  needed, unlike in `Stacks.LocalCohomology.eq_of_pow_smul_eq_of_basicOpen`, which asks for the
  open to be the basic open itself.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_affine_restrictSections_oneSection_eq`:
  **the affine-local surjectivity.**

## Implementation notes

The proof is the source's affine argument, assembled from existing pieces:

* `Stacks.LocalCohomology.exists_compatible_family` puts `s` in normal form over `W`: one
  exponent `k` and sections `m i` of `F` over `W` with `m i = (a i)^k · s` on the basic open of
  each generator `a i` of `I(W)`, satisfying the *exact* cross relations
  `(a j)^k • m i = (a i)^k • m j`;
* `Stacks.LocalCohomology.exists_idealPow_linearMap_of_cross_relations` turns that family into a
  `Γ(X, W)`-linear map `I(W)^N → Γ(F, W)/Γ(F, W)_N`, characterised by
  `(a i)^k • φ x = x • [m i]`;
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_restrictSections_eq_of_affineQuotientHom`
  reads that linear map as a morphism of the restrictions to `W`.

The exponent is bumped from `k` to `k + 1` by replacing `m i` with `a i • m i`, because the
cross-relation lemma needs a positive exponent.

That the resulting morphism really sends the unit section to `s` is checked on the basic opens of
the generators, which cover `W ⊓ U`: there `a i` is invertible, and the characterisation of `φ`
at the element `(a i)^N ∈ I(W)^N` gives
`(a i)^(N+k+1) • θ(1) = (a i)^(N+k+1) • [s]`, which may be cancelled.  This is the step for
which the `IsValue` machinery of
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Surjectivity.lean` is unusable: there the
local value of `a • s` is pinned by the absence of `I`-power torsion, whereas here the values
form a coset of the whole torsion submodule and it is the *quotient* that makes the choice
coherent.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM) (the affine case)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Cancelling a power of an invertible function -/

/-- **A function is invertible on any open inside its basic open.**

DEDUP OWED: `Stacks.AlgebraicGeometry.AnnihilatorQcoh.isUnit_map_of_le_basicOpen` is the same
statement with the inclusion `V ≤ W` presented as the composite `(V ≤ X.basicOpen b) ≤ W`
instead of as an independent hypothesis; that file is not in this one's import closure. -/
theorem isUnit_restrict_of_le_basicOpen {W : X.Opens} (b : Γ(X, W)) {V : X.Opens}
    (hV : V ≤ X.basicOpen b) (hVW : V ≤ W) :
    IsUnit (X.presheaf.map (homOfLE hVW).op b) := by
  have hcomp : X.presheaf.map (homOfLE hVW).op b
      = X.presheaf.map (homOfLE hV).op
        (X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) := by
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    congr 2
  rw [hcomp]
  exact (RingedSpace.isUnit_res_basicOpen X.toRingedSpace b).map
    (X.presheaf.map (homOfLE hV).op).hom

/-- **Multiplication by a power of `b` is injective on the sections over an open inside the
basic open of `b`.** Unlike `Stacks.LocalCohomology.eq_of_pow_smul_eq_of_basicOpen` this needs
neither affineness nor quasi-coherence: on such an open `b` is simply invertible. -/
theorem eq_of_pow_smul_eq_of_le_basicOpen {G : X.Modules} {W : X.Opens} (b : Γ(X, W))
    {V : X.Opens} (hV : V ≤ X.basicOpen b) (hVW : V ≤ W) (p : ℕ) (x y : Γ(G, V))
    (h : (X.presheaf.map (homOfLE hVW).op b) ^ p • x
      = (X.presheaf.map (homOfLE hVW).op b) ^ p • y) : x = y :=
  ((isUnit_restrict_of_le_basicOpen b hV hVW).pow p).smul_left_cancel.mp h

/-- **Bumping the exponent of a cross relation.** If `bᵏ • x = aᵏ • y`, then
`bᵏ⁺¹ • (a • x) = aᵏ⁺¹ • (b • y)`. -/
theorem pow_succ_smul_smul_eq_of_pow_smul_eq {A M : Type*} [CommSemiring A] [AddCommMonoid M]
    [Module A M] {a b : A} {x y : M} {k : ℕ} (h : b ^ k • x = a ^ k • y) :
    b ^ (k + 1) • (a • x) = a ^ (k + 1) • (b • y) := by
  rw [smul_smul, smul_smul]
  calc (b ^ (k + 1) * a) • x
      = (a * b) • (b ^ k • x) := by
        rw [smul_smul]
        congr 1
        ring
    _ = (a * b) • (a ^ k • y) := by rw [h]
    _ = (a ^ (k + 1) * b) • y := by
        rw [smul_smul]
        congr 1
        ring

/-! ### The affine-local surjectivity -/

open Stacks.LocalCohomology in
/-- **The morphism attached to a family satisfying the cross relations.** If `I(W)` is generated
by `a` and `(a j)^(k+1) • m i = (a i)^(k+1) • m j`, there are an `N` and a morphism
`θ : Iᴺ|_W ⟶ (F/F_N)|_W` with `(a i)^(k+1) • θ((a i)^N) = (a i)^N • [m i]` over `W`. -/
theorem exists_affineQuotientHom_pow_smul_eq (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) (W : X.affineOpens)
    {ι : Type*} [Finite ι] (a : ι → Γ(X, W.1)) (hspan : I.ideal W = Ideal.span (Set.range a))
    (k : ℕ) (m : ι → Γ(F, W.1)) (hrel : ∀ i j, a j ^ (k + 1) • m i = a i ^ (k + 1) • m j) :
    ∃ (N : ℕ) (θ : Scheme.Modules.restrict (idealPow I N) W.1.ι ⟶
        Scheme.Modules.restrict (quotientModule I F N) W.1.ι),
      ∀ (i : ι) (x : Γ(idealPow I N, W.1)), (x.1 : Γ(X, W.1)) = a i ^ N →
        a i ^ (k + 1) • restrictSections θ W.1 le_rfl x
          = a i ^ N • (quotientπ I F N).app W.1 (m i) := by
  classical
  obtain ⟨N, φ, hφ⟩ := exists_idealPow_linearMap_of_cross_relations
    (A := Γ(X, W.1)) (M := Γ(F, W.1)) a (k + 1) (Nat.le_add_left 1 k) m hrel
  have hpow : (I.ideal W ^ N : Ideal Γ(X, W.1)) = Ideal.span (Set.range a) ^ N := by rw [hspan]
  have htor : Submodule.torsionBySet Γ(X, W.1) Γ(F, W.1)
        ((Ideal.span (Set.range a) ^ N : Ideal Γ(X, W.1)) : Set Γ(X, W.1))
      = Submodule.torsionBySet Γ(X, W.1) Γ(F, W.1)
        ((I.ideal W ^ N : Ideal Γ(X, W.1)) : Set Γ(X, W.1)) := by rw [hpow]
  set ψ : ↥(I.ideal W ^ N : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F N W :=
    (Submodule.quotEquivOfEq _ _ htor).toLinearMap ∘ₗ φ ∘ₗ Submodule.inclusion hpow.le
  obtain ⟨θ, hθ⟩ := exists_restrictSections_eq_of_affineQuotientHom I F hFG N W ψ
  refine ⟨N, θ, fun i x hx => ?_⟩
  rw [hθ x]
  obtain ⟨x, hxm⟩ := x
  obtain rfl : x = a i ^ N := hx
  have hmem : (a i ^ N : Γ(X, W.1)) ∈ Ideal.span (Set.range a) ^ N :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) N
  calc _ = a i ^ (k + 1) • quotientSectionsAffineEquiv I F N hFG W
          ((Submodule.quotEquivOfEq _ _ htor) (φ ⟨a i ^ N, hmem⟩)) := rfl
    _ = quotientSectionsAffineEquiv I F N hFG W ((Submodule.quotEquivOfEq _ _ htor)
          (a i ^ (k + 1) • φ ⟨a i ^ N, hmem⟩)) := by rw [map_smul, map_smul]
    _ = quotientSectionsAffineEquiv I F N hFG W ((Submodule.quotEquivOfEq _ _ htor)
          ((a i ^ N : Γ(X, W.1)) • Submodule.mkQ _ (m i))) := by rw [hφ i ⟨a i ^ N, hmem⟩]
    _ = a i ^ N • (quotientπ I F N).app W.1 (m i) := by
        rw [map_smul, map_smul, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
          ← Submodule.mkQ_apply, quotientSectionsAffineEquiv_mkQ]

open Stacks.LocalCohomology in
/-- **The local check over the basic open of a generator.** If `m = bᵏ · s` on the basic open
of `b ∈ I(W)` and `bᵏ⁺¹ • θ(bᴺ) = bᴺ • [b • m]` over `W`, then `θ` sends the unit section of
`Iᴺ` to `[s]` over every open inside that basic open and missing the support of `I`. -/
theorem restrictSections_oneSection_eq_of_le_basicOpen (I : X.IdealSheafData) (F : X.Modules)
    (W : X.affineOpens) {N k : ℕ} (θ : Scheme.Modules.restrict (idealPow I N) W.1.ι ⟶
      Scheme.Modules.restrict (quotientModule I F N) W.1.ι)
    {b : Γ(X, W.1)} (hb : b ∈ I.ideal W) (s : Γ(F, (I.support.compl : X.Opens)))
    {m : Γ(F, W.1)} (hm : F.presheaf.map (homOfLE (X.basicOpen_le b)).op m =
      (X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) ^ k •
        F.presheaf.map (homOfLE (basicOpen_le_idealComplement I W hb)).op s)
    {x : Γ(idealPow I N, W.1)} (hx : (x.1 : Γ(X, W.1)) = b ^ N)
    (hθ : b ^ (k + 1) • restrictSections θ W.1 le_rfl x
      = b ^ N • (quotientπ I F N).app W.1 (b • m))
    {V : X.Opens} (hVb : V ≤ X.basicOpen b) (hVW : V ≤ W.1)
    (hVU : V ≤ (I.support.compl : X.Opens)) :
    restrictSections θ V hVW ((idealPow I N).presheaf.map (homOfLE hVU).op (oneSection I N))
      = (quotientπ I F N).app V (F.presheaf.map (homOfLE hVU).op s) := by
  set r : Γ(X, V) := X.presheaf.map (homOfLE hVW).op b with hrdef
  refine eq_of_pow_smul_eq_of_le_basicOpen b hVb hVW (N + (k + 1)) _ _ ?_
  have hscal : ∀ p q : ℕ, r ^ (p + q) = X.presheaf.map (homOfLE hVW).op (b ^ q) * r ^ p := by
    intro p q
    rw [hrdef, ← map_pow, ← map_pow, ← map_mul]
    congr 1
    ring
  have hres : (idealPow I N).presheaf.map (homOfLE hVW).op x
      = r ^ N • (idealPow I N).presheaf.map (homOfLE hVU).op (oneSection I N) :=
    eq_smul_map_oneSection I N hVU _ (by rw [val_map_idealPow, hx, hrdef, map_pow])
  have hL : r ^ (N + (k + 1)) • restrictSections θ V hVW
        ((idealPow I N).presheaf.map (homOfLE hVU).op (oneSection I N))
      = (quotientModule I F N).presheaf.map (homOfLE hVW).op
          (b ^ (k + 1) • restrictSections θ W.1 le_rfl x) := by
    rw [Scheme.Modules.map_smul, ← restrictSections_res θ V W.1 hVW le_rfl x, hres,
      restrictSections_smul, smul_smul, hscal]
  have hmV : F.presheaf.map (homOfLE hVW).op (b • m)
      = r ^ (k + 1) • F.presheaf.map (homOfLE hVU).op s := by
    have h := congrArg (F.presheaf.map (homOfLE hVb).op) hm
    rw [Stacks.LocalCohomology.map_homOfLE_map_homOfLE, Scheme.Modules.map_smul, map_pow,
      Stacks.LocalCohomology.structureSheaf_map_homOfLE_map_homOfLE] at h
    rw [Stacks.LocalCohomology.map_homOfLE_map_homOfLE F
      (basicOpen_le_idealComplement I W hb) hVb s] at h
    rw [hrdef, Scheme.Modules.map_smul, h, smul_smul, ← pow_succ']
    rfl
  have hR : r ^ (N + (k + 1)) • (quotientπ I F N).app V (F.presheaf.map (homOfLE hVU).op s)
      = (quotientModule I F N).presheaf.map (homOfLE hVW).op
          (b ^ N • (quotientπ I F N).app W.1 (b • m)) := by
    rw [Scheme.Modules.map_smul, app_naturality (quotientπ I F N) hVW, hmV,
      Scheme.Modules.Hom.app_smul, smul_smul, add_comm N (k + 1), hscal]
  rw [hL, hR, hθ]

open Stacks.LocalCohomology in
/-- **The affine-local surjectivity of the second display of [Stacks, Tag 01PQ].** Let `I` be a
quasi-coherent sheaf of ideals of finite type, let `F` be quasi-coherent and let `s` be a section
of `F` over `U = X ∖ V(I)`.  Over an affine open `W` there are an exponent `n` and a morphism
`θ : Iⁿ|_W ⟶ (F/F_n)|_W` which sends the unit section of `Iⁿ` to `s` over every open of `W`
missing the support of `I`. -/
theorem exists_affine_restrictSections_oneSection_eq (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) (W : X.affineOpens)
    (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (θ : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
        Scheme.Modules.restrict (quotientModule I F n) W.1.ι),
      ∀ (V : X.Opens) (hVW : V ≤ W.1) (hVU : V ≤ (I.support.compl : X.Opens)),
        restrictSections θ V hVW
            ((idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n))
          = (quotientπ I F n).app V (F.presheaf.map (homOfLE hVU).op s) := by
  classical
  obtain ⟨T, hT⟩ := hFG W
  set ι : Type u := {x : Γ(X, W.1) // x ∈ T}
  set a : ι → Γ(X, W.1) := Subtype.val
  have hspan : I.ideal W = Ideal.span (Set.range a) := by
    rw [show Set.range a = (T : Set Γ(X, W.1)) from Subtype.range_coe]
    exact hT.symm
  have ha : ∀ i, a i ∈ I.ideal W := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨k, m, hm, hrel⟩ := exists_compatible_family I F W a ha s
  obtain ⟨N, θ, hθ⟩ := exists_affineQuotientHom_pow_smul_eq I F hFG W a hspan k
    (fun i => a i • m i) fun i j => pow_succ_smul_smul_eq_of_pow_smul_eq (hrel i j)
  have hxi : ∀ i, (a i ^ N : Γ(X, W.1)) ∈
      (idealPowerMultiple I N (structureModule X)).toSubmodule.obj (op W.1) := fun i => by
    rw [obj_idealPow_affineOpen I N W]
    exact Ideal.pow_mem_pow (ha i) N
  set xi : ι → Γ(idealPow I N, W.1) := fun i => ⟨a i ^ N, hxi i⟩
  refine ⟨N, θ, fun V hVW hVU => ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (quotientModule I F N).isSheaf fun y hy => ?_
  obtain ⟨i, hyi⟩ := exists_mem_basicOpen_of_span I W a hspan (hVW hy) (hVU hy)
  refine ⟨V ⊓ X.basicOpen (a i), inf_le_left, ⟨hy, hyi⟩, ?_⟩
  rw [← restrictSections_res θ (V ⊓ X.basicOpen (a i)) V inf_le_left hVW,
    Stacks.LocalCohomology.map_homOfLE_map_homOfLE,
    app_naturality (quotientπ I F N) (inf_le_left : V ⊓ X.basicOpen (a i) ≤ V),
    Stacks.LocalCohomology.map_homOfLE_map_homOfLE]
  exact restrictSections_oneSection_eq_of_le_basicOpen I F W θ (ha i) s (hm i) (x := xi i) rfl
    (hθ i (xi i) rfl) inf_le_right (inf_le_left.trans hVW) (inf_le_left.trans hVU)

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
