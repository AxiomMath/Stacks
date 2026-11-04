module

public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.AmpleDegree
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.CoherentFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.TwistShift
public import StacksFrontier.AlgebraicGeometry.ProjSerreDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCoherence.Noetherian
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic

/-!
# Assertions (1) and (3) of [Stacks, Tag 0B5Q], through an ample twist

Let `A` be a Noetherian commutative ring with an `ℕ`-grading `𝒜` and let `X = Proj 𝒜`. Let
`d > 0` be a degree whose ratio locus `Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 d` is all
of `X`, such that the twist `𝒪(d)` is an ample invertible `𝒪_X`-module whose integer tensor powers
are the twists `𝒪(dn)`. Then every coherent `𝒪_X`-module is a quotient of a finite direct sum of
twisting sheaves, and for every `p > 0` and every coherent `ℱ` the cohomology `Hᵖ(X, ℱ(e))`
vanishes for all large `e`. Both statements also hold for an arbitrary Noetherian graded ring, with
no degree in the hypotheses.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjNoetherian.twistTensorPowIso`: the isomorphism
  `ℱ(q) ⊗ 𝒪(d) ^⊗ n ≅ ℱ(q + dn)`.
* `Stacks.AlgebraicGeometry.ProjNoetherian.biconeMapIso`: a bicone transported along
  componentwise isomorphisms of its summands.
* `Stacks.AlgebraicGeometry.ProjNoetherian.biconeMapIsoIsBilimit`: the transported bicone of a
  bilimit bicone is a bilimit.

## Main results

* `Stacks.AlgebraicGeometry.ProjNoetherian.exists_isZero_hgroup_twist_mul`: for coherent `ℱ` and
  an integer `q`, `Hᵖ(X, ℱ(q + dm)) = 0` for all large `m` and every `p > 0`.
* `Stacks.AlgebraicGeometry.ProjNoetherian.exists_isZero_hgroup_twist`: for `p > 0` and coherent
  `ℱ` there is an `e₀` with `Hᵖ(X, ℱ(e)) = 0` for all `e ≥ e₀`.
* `Stacks.AlgebraicGeometry.ProjNoetherian.exists_epi_biproduct_twistingSheaf_of_isCoherent`:
  a surjection onto a coherent module from a finite direct sum of twisting sheaves `𝒪(dⱼ)`.
* `Stacks.AlgebraicGeometry.ProjNoetherian.hasTwistQuotients_of_isAmple`: every coherent
  `𝒪_X`-module is a quotient of a finite direct sum of twisting sheaves.
* `Stacks.AlgebraicGeometry.ProjNoetherian.hasTwistQuotients` and
  `Stacks.AlgebraicGeometry.ProjNoetherian.exists_isZero_hgroup_twist_of_isCoherent`: the same
  two statements for an arbitrary Noetherian graded ring.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u v

namespace Stacks.AlgebraicGeometry.ProjNoetherian

section AmpleTwist

variable {A : Type u} {σ : Type v} [CommRing A] [IsNoetherianRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable (d : ℕ) (hd : 0 < d)
  (hrl : Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 d = ⊤)
  [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ))]
  (hamp : Stacks.Ample.IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)))
  (htw : ∀ n : ℤ, Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
           (twistingSheaf 𝒜 (d : ℤ)) n ≅ twistingSheaf 𝒜 ((d : ℤ) * n))

/-! ### The twist as an ample tensor power -/

/-- When the ratio locus of `d` is all of `Proj 𝒜` and `htw` identifies the tensor powers of
`𝒪(d)` with twists, the isomorphism `ℱ(q) ⊗ 𝒪(d) ^⊗ n ≅ ℱ(q + dn)` between the tensor product of
the twist `ℱ(q)` with the `n`-th tensor power of `𝒪(d)` and the twist `ℱ(q + dn)`. -/
def twistTensorPowIso (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (q n : ℤ) :
    Stacks.RelativeVeryAmple.tensorModules (AlgebraicGeometry.Proj 𝒜)
        (twistSheafOfModules 𝒜 F q)
        (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 (d : ℤ)) n) ≅
      twistSheafOfModules 𝒜 F (q + (d : ℤ) * n) :=
  Stacks.RelativeVeryAmple.tensorModulesMapIso (AlgebraicGeometry.Proj 𝒜) (Iso.refl _)
      (htw n) ≪≫
    ProjNoetherianTwistShift.twistSheafOfModulesShiftIso 𝒜 hrl F q n

/-! ### Assertion (3): the higher cohomology of the high twists vanishes -/

include hrl hamp htw in
/-- If `𝒪(d)` is ample, then for a coherent `ℱ` on `Proj 𝒜` and an integer `q` there is an `m₀`
with `Hᵖ(Proj 𝒜, ℱ(q + dm)) = 0` for every `m ≥ m₀` and every `p > 0`. -/
theorem exists_isZero_hgroup_twist_mul
    (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (hF : _root_.SheafOfModules.IsCoherent F)
    (q : ℤ) :
    ∃ m₀ : ℕ, ∀ m p : ℕ, m₀ ≤ m → 0 < p →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p
        (twistSheafOfModules 𝒜 F (q + (d : ℤ) * m))) := by
  have : IsNoetherianRing (𝒜 0) := isNoetherianRing_gradeZero 𝒜
  have : IsProper (AlgebraicGeometry.Proj.toSpecZero 𝒜) := isProper_toSpecZero 𝒜
  let G : (AlgebraicGeometry.Proj 𝒜).Modules := twistSheafOfModules 𝒜 F q
  have : _root_.SheafOfModules.IsCoherent G :=
    isCoherent_twistSheafOfModules_of_isNoetherianRing 𝒜 F hF q
  obtain ⟨m₀, hm₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      (AlgebraicGeometry.Proj.toSpecZero 𝒜) G (twistingSheaf 𝒜 (d : ℤ)) hamp
  exact ⟨m₀, fun m p hm hp => IsZero.of_iso (hm₀ m p hm hp)
    ((Hfunctor (projRingSheaf 𝒜) ⊤ p).mapIso (twistTensorPowIso 𝒜 d hrl htw F q m)).symm⟩

include hd hrl hamp htw in
/-- If `𝒪(d)` is ample for some `d > 0`, then for `p > 0` and a coherent `𝒪_{Proj 𝒜}`-module `ℱ`
there is an `e₀` with `Hᵖ(Proj 𝒜, ℱ(e)) = 0` for every `e ≥ e₀`. -/
theorem exists_isZero_hgroup_twist (p : ℕ) (hp : 0 < p)
    (F : SheafOfModules.{u} (projRingSheaf 𝒜))
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F e)) := by
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  choose m₀ hm₀ using fun q : Fin d =>
    exists_isZero_hgroup_twist_mul 𝒜 d hrl hamp htw F hF (q : ℕ)
  refine ⟨d * (Finset.univ.sup m₀ : ℕ) + d, fun e he => ?_⟩
  have h₁ := Int.emod_nonneg e hd0.ne'
  have h₂ := Int.emod_lt_of_pos e hd0
  have h₃ := Int.mul_ediv_add_emod e d
  have hM : ((Finset.univ.sup m₀ : ℕ) : ℤ) ≤ e / d := le_of_mul_le_mul_left (by lia) hd0
  have hq : (e % d).toNat < d := by lia
  have hle := Finset.le_sup (f := m₀) (Finset.mem_univ ⟨(e % d).toNat, hq⟩)
  have h := hm₀ ⟨(e % d).toNat, hq⟩ (e / d).toNat p (by lia) hp
  rwa [show (((e % d).toNat : ℕ) : ℤ) + d * (e / d).toNat = e by
    rw [Int.toNat_of_nonneg (by lia : 0 ≤ e / d)]; lia] at h

/-! ### Assertion (1): every coherent module is a quotient of a sum of twisting sheaves -/

/-- The bicone over `g` obtained from a bicone `c` over `f` and isomorphisms `w j : f j ≅ g j`:
it has the cone point of `c`, projections `c.π j ≫ (w j).hom` and injections
`(w j).inv ≫ c.ι j`. -/
def biconeMapIso {C : Type*} [Category C] [Preadditive C] {J : Type} {f g : J → C}
    (c : Bicone f) (w : ∀ j, f j ≅ g j) : Bicone g where
  pt := c.pt
  π j := c.π j ≫ (w j).hom
  ι j := (w j).inv ≫ c.ι j
  ι_π j j' := by
    rw [Category.assoc, ← Category.assoc (c.ι j), c.ι_π]
    by_cases h : j = j'
    · subst h; simp
    · simp [h]

/-- Over a finite index type, `biconeMapIso c w` is a bilimit bicone when `c` is. -/
def biconeMapIsoIsBilimit {C : Type*} [Category C] [Preadditive C] {J : Type} [Fintype J]
    {f g : J → C} {c : Bicone f} (hc : c.IsBilimit) (w : ∀ j, f j ≅ g j) :
    (biconeMapIso c w).IsBilimit :=
  isBilimitOfTotal _ (by
    change ∑ j : J, (c.π j ≫ (w j).hom) ≫ (w j).inv ≫ c.ι j = 𝟙 c.pt
    simpa using CategoryTheory.Limits.IsBilimit.total hc)

include hamp htw in
/-- If `𝒪(d)` is ample, then for a coherent `𝒪_{Proj 𝒜}`-module `ℱ` there are an `r`, exponents
`dⱼ` for `j < r`, a bilimit bicone over the twisting sheaves `𝒪(dⱼ)` and an epimorphism from its
cone point onto `ℱ`. -/
theorem exists_epi_biproduct_twistingSheaf_of_isCoherent
    (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ (r : ℕ) (dj : Fin r → ℤ) (b : Bicone fun j : Fin r => twistingSheaf 𝒜 (dj j))
      (_ : b.IsBilimit) (φ : b.pt ⟶ F), Epi φ := by
  obtain ⟨ι, hfin, dj, b, hb, φ, hφ⟩ :=
    @Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_epi_biproduct_tensorPowModule_of_isAmple
      (AlgebraicGeometry.Proj 𝒜) F (twistingSheaf 𝒜 (d : ℤ)) hF inferInstance hamp
  have : Finite ι := hfin
  obtain ⟨e⟩ : Nonempty (Fin (Nat.card ι) ≃ ι) := ⟨(Finite.equivFin ι).symm⟩
  exact ⟨Nat.card ι, fun j => (d : ℤ) * dj (e j),
    biconeMapIso (b.whisker e) fun j => htw (dj (e j)),
    biconeMapIsoIsBilimit ((Bicone.whiskerIsBilimitIff b e).symm hb)
      (fun j => htw (dj (e j))), φ, hφ⟩

include hamp htw in
/-- If `𝒪(d)` is ample, then every coherent `𝒪_{Proj 𝒜}`-module is the target of an epimorphism
from a finite direct sum of twisting sheaves. -/
theorem hasTwistQuotients_of_isAmple :
    Stacks.AlgebraicGeometry.ProjSerreDevissage.HasTwistQuotients 𝒜 :=
  fun F hF => exists_epi_biproduct_twistingSheaf_of_isCoherent 𝒜 d hamp htw F hF

end AmpleTwist

/-! ### The assertions for a Noetherian graded ring -/

section Noetherian

variable {A : Type u} {σ : Type u} [CommRing A] [IsNoetherianRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A Noetherian graded ring has a degree `d > 0` with `𝒪(d)` ample and its tensor powers the
twists `𝒪(dn)`; any statement derived from such data therefore holds. -/
private theorem exists_ample_twist {P : Prop}
    (h : ∀ d : ℕ, 0 < d → Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 d = ⊤ →
      ∀ [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ))],
      Stacks.Ample.IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) →
      (∀ n : ℤ, Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 (d : ℤ)) n ≅ twistingSheaf 𝒜 ((d : ℤ) * n)) → P) : P := by
  obtain ⟨d, hd, -, htop, hrl⟩ :=
    ProjNoetherianTwistShift.exists_pos_ratioLocus_eq_top 𝒜 1 Nat.one_pos
  have := ProjAmpleDegree.isInvertibleModule_twistingSheaf 𝒜 htop
  have := ProjAmpleDegree.isInvertible_twistingSheaf 𝒜 htop
  exact h d hd hrl
    (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 (d : ℤ)) (ProjAmpleDegree.isAmple_twistingSheaf 𝒜 hd htop))
    (ProjAmpleDegree.tensorPowModuleIsoTwistingSheaf 𝒜 d htop)

/-- For a Noetherian graded ring `𝒜`, every coherent `𝒪_{Proj 𝒜}`-module is the target of an
epimorphism from a finite direct sum of twisting sheaves. -/
theorem hasTwistQuotients :
    Stacks.AlgebraicGeometry.ProjSerreDevissage.HasTwistQuotients 𝒜 :=
  exists_ample_twist 𝒜 fun d _ _ _ hamp htw => hasTwistQuotients_of_isAmple 𝒜 d hamp htw

/-- For a Noetherian graded ring `𝒜`, `p > 0` and a coherent `𝒪_{Proj 𝒜}`-module `ℱ`, there is
an `e₀` with `Hᵖ(Proj 𝒜, ℱ(e)) = 0` for every `e ≥ e₀`. -/
theorem exists_isZero_hgroup_twist_of_isCoherent (p : ℕ) (hp : 0 < p)
    (F : SheafOfModules.{u} (projRingSheaf 𝒜))
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F e)) :=
  exists_ample_twist 𝒜 fun d hd hrl _ hamp htw =>
    exists_isZero_hgroup_twist 𝒜 d hd hrl hamp htw p hp F hF

end Noetherian

end Stacks.AlgebraicGeometry.ProjNoetherian

end
