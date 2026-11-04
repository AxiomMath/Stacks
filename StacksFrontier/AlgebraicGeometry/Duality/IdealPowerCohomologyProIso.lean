module

public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# The pro-isomorphism of [Stacks, Tag 0G4R] as a `ProIso` of inverse sequences

`Stacks.Duality.cohomologyIdealPowers_proIsomorphic` states [Stacks, Tag 0G4R] as raw data: a
family of transition maps `τ`, a constant `c > 0`, comparison maps `ρ` and `ψ` and the explicit
cofinal maps `forward` and `backward` between `H^p(𝓘^n𝓕^•)` and `𝓘^n H^p(𝓕^•)`, together with
the equations they satisfy. Consumers of a pro-isomorphism in this library — above all
`CategoryTheory.RestrictionLifting.of_proIso`, which is how the identification of
[Stacks, Tag 0G2H] is transported along one — take instead a `ProIso` of two *functors*
`ℕᵒᵖ ⥤ 𝒟`. This file packages the data as such a `ProIso`.

The two inverse sequences are assembled from their successive transitions by
`CategoryTheory.Functor.ofOpSequence`: `Stacks.Duality.cohomologySystem` from the canonical
`H^p(𝓘^{n+1}𝓕^•) ⟶ H^p(𝓘^n𝓕^•)` and `Stacks.Duality.idealPowerSystem` from the inclusions
`𝓘^{n+1}𝓗 ⟶ 𝓘^n𝓗`. What has to be checked is that the transition of such a functor from level
`m` down to level `n` is the map the tag supplies for that pair of levels, and that is
`Stacks.Duality.tr_ofOpSequence_eq`: a sequence of maps indexed by pairs `n ≤ m` which is the
identity on the diagonal, composes, and has the given successive maps is the transition system
of the functor. It is applied twice — on the cohomology side to the family `τ` the tag produces,
whose first three stated properties are exactly those three hypotheses, and on the ideal-power
side to the inclusions, through `AlgebraicGeometry.subHom_rfl` and
`AlgebraicGeometry.subHom_comp`.

With the transitions identified, the six remaining equations of a `ProIso` are exactly six of
the conclusions of the tag, for the reindexings `α = β = (· + c)`.

## Main definitions

* `Stacks.Duality.cohomologySystem`: the inverse sequence `n ↦ H^p(𝓘^n𝓕^•)`.
* `Stacks.Duality.idealPowerSystem`: the inverse sequence `n ↦ 𝓘^n𝓗`.

## Main results

* `Stacks.Duality.tr_ofOpSequence_eq`: the transitions of a functor built from successive maps.
* `Stacks.Duality.cohomologyIdealPowersProIso`: **[Stacks, Tag 0G4R]** as a `ProIso`.
* `Stacks.Duality.cohomologyIdealPowersProIso_comp`: the same after any functor — in particular
  after `DerivedCategory.singleFunctor _ p`, which is the form in which the core case of
  [Stacks, Tag 0G2H] would consume it.

## References

* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open InverseSequence

universe v v' u u' w

namespace Stacks.Duality

/-! ### The transitions of a functor assembled from its successive maps -/

/-- The transition maps of an inverse sequence assembled from its successive maps are determined
by any family indexed by pairs `n ≤ m` that is the identity on the diagonal, composes, and
reduces to the given successive maps. This is what identifies the transitions of
`Stacks.Duality.cohomologySystem` with the maps `τ` supplied by [Stacks, Tag 0G4R], and those of
`Stacks.Duality.idealPowerSystem` with the inclusions of ideal-power subsheaves. -/
lemma tr_ofOpSequence_eq {D : Type w} [Category.{v} D] {Y : ℕ → D}
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n) (τ : ∀ m n : ℕ, n ≤ m → (Y m ⟶ Y n))
    (hid : ∀ n : ℕ, τ n n le_rfl = 𝟙 (Y n))
    (hcomp : ∀ (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m),
      τ k m hkm ≫ τ m n hmn = τ k n (hmn.trans hkm))
    (hsucc : ∀ n : ℕ, τ (n + 1) n (Nat.le_succ n) = f n)
    {m n : ℕ} (h : n ≤ m) :
    tr (Functor.ofOpSequence f) h = τ m n h := by
  induction m, h using Nat.le_induction with
  | base => exact (ProIso.tr_refl (Functor.ofOpSequence f) le_rfl).trans (hid n).symm
  | succ m hm ih =>
    have key : f m ≫ τ m n hm = τ (m + 1) n (hm.trans (Nat.le_succ m)) :=
      (congrArg (fun t => t ≫ τ m n hm) (hsucc m)).symm.trans
        (hcomp (m + 1) m n (Nat.le_succ m) hm)
    have hstep : tr (Functor.ofOpSequence f) (Nat.le_succ m) = f m :=
      Functor.ofOpSequence_map_homOfLE_succ f m
    exact (ProIso.tr_trans (Functor.ofOpSequence f) hm (Nat.le_succ m)).symm.trans
      (((congrArg (fun t => t ≫ tr (Functor.ofOpSequence f) hm) hstep).trans
        (congrArg (fun t => f m ≫ t) ih)).trans key)

variable {X : Scheme.{u}}

/-! ### The two inverse sequences -/

/-- The inverse sequence `n ↦ H^p(𝓘^n𝓕^•)` of the cohomology sheaves of the ideal-power
subcomplexes, with the canonical transitions. -/
def cohomologySystem {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (p : ℤ) : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n => S.cohomology n p)
    (fun n => S.cohomologyTransition n p)

/-- The `n`-th term of `cohomologySystem S p` is `H^p(𝓘^n𝓕^•)`. -/
@[simp]
lemma cohomologySystem_obj {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (p : ℤ) (n : ℕ) :
    (cohomologySystem S p).obj (op n) = S.cohomology n p :=
  rfl

/-- The inverse sequence `n ↦ 𝓘^n𝓗` of the ideal-power subsheaves of a sheaf of modules, with
the inclusions as transitions. -/
def idealPowerSystem (I : X.IdealSheafData) (M : X.Modules) : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence
    (X := fun n : ℕ =>
      ((Stacks.Algebraization.idealPowerMultiple I n M).toSheafOfModules : X.Modules))
    (fun n : ℕ =>
      subHom (idealPowerMultiple_antitone I M (Nat.le_succ n)))

/-- The `n`-th term of `idealPowerSystem I M` is the subsheaf `𝓘^n M`. -/
@[simp]
lemma idealPowerSystem_obj (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (idealPowerSystem I M).obj (op n) =
      ((Stacks.Algebraization.idealPowerMultiple I n M).toSheafOfModules : X.Modules) :=
  rfl

/-- The transition of the ideal-power sequence from level `m` to level `n` is the inclusion
`𝓘^m M ⟶ 𝓘^n M`. -/
lemma tr_idealPowerSystem (I : X.IdealSheafData) (M : X.Modules) {m n : ℕ} (h : n ≤ m) :
    tr (idealPowerSystem I M) h =
      subHom (idealPowerMultiple_antitone I M h) :=
  tr_ofOpSequence_eq _
    (fun _ _ h => subHom (idealPowerMultiple_antitone I M h))
    (fun n => subHom_rfl (Stacks.Algebraization.idealPowerMultiple I n M))
    (fun _ _ _ _ _ => subHom_comp _ _) (fun _ => rfl) h

/-- The transition of the cohomology sequence from level `m` to level `n` is any family of maps
satisfying the first three conclusions of [Stacks, Tag 0G4R] — in particular the family `τ` that
tag supplies. -/
lemma tr_cohomologySystem {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (p : ℤ)
    (τ : ∀ m n : ℕ, n ≤ m → (S.cohomology m p ⟶ S.cohomology n p))
    (hid : ∀ n : ℕ, τ n n le_rfl = 𝟙 (S.cohomology n p))
    (hcomp : ∀ (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m),
      τ k m hkm ≫ τ m n hmn = τ k n (hmn.trans hkm))
    (hsucc : ∀ n : ℕ, τ (n + 1) n (Nat.le_succ n) = S.cohomologyTransition n p)
    {m n : ℕ} (h : n ≤ m) :
    tr (cohomologySystem S p) h = τ m n h :=
  tr_ofOpSequence_eq _ τ hid hcomp hsucc h

/-! ### The pro-isomorphism -/

variable (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (p : ℤ)

/-- **[Stacks, Tag 0G4R] as a `ProIso`.** Let `X` be a Noetherian scheme, `𝓘 ⊆ 𝒪_X` a
quasi-coherent sheaf of ideals and `𝓕^•` a complex of coherent `𝒪_X`-modules. The inverse
sequence `n ↦ H^p(𝓘^n𝓕^•)` and the inverse sequence `n ↦ 𝓘^n H^p(𝓕^•)` are pro-isomorphic, in
the explicit "up to refinement" form `ProIso`: with `c` the Artin-Rees constant of
`Stacks.Duality.cohomologyIdealPowers_proIsomorphic`, both reindexings are `m ↦ m + c`, the
forward maps are the factorizations `H^p(𝓘^{m+c}𝓕^•) ⟶ 𝓘^m H^p(𝓕^•)` and the backward maps are
the comparisons `𝓘^{m+c} H^p(𝓕^•) ⟶ H^p(𝓘^m𝓕^•)`.

This is the form a pro-isomorphism is consumed in by
`CategoryTheory.RestrictionLifting.of_proIso`, which is how the core case of
[Stacks, Tag 0G2H] is transported from the ideal powers of the cohomology to the cohomology of
the ideal powers. -/
@[stacks 0G4R "the pro-isomorphism, packaged as a `ProIso` of the two inverse sequences
`n ↦ H^p(I^n F^•)` and `n ↦ I^n H^p(F^•)`; the underlying data and its equations are
`Stacks.Duality.cohomologyIdealPowers_proIsomorphic`."]
theorem cohomologyIdealPowersProIso [IsNoetherian X] (hF : TermsCoherent F)
    (S : IdealPowerComplexSystem I F) :
    Nonempty (ProIso (cohomologySystem S p) (idealPowerSystem I (F.homology p))) := by
  obtain ⟨τ, hτid, hτcomp, hτsucc, -, c, -, ρ, ψ, -, -, -, -, -, -, forward, backward, -, -,
    hfnat, hbnat, hfb, hbf⟩ := cohomologyIdealPowers_proIsomorphic I F p hF S
  have htr : ∀ {m n : ℕ} (h : n ≤ m), tr (cohomologySystem S p) h = τ m n h :=
    fun h => tr_cohomologySystem S p τ hτid hτcomp hτsucc h
  refine ⟨{
    α := fun m => m + c
    β := fun m => m + c
    αmono := fun a b h => Nat.add_le_add_right h c
    βmono := fun a b h => Nat.add_le_add_right h c
    αle := fun m => Nat.le_add_right m c
    βle := fun m => Nat.le_add_right m c
    φ := forward
    ψ := backward
    φnat := ?_
    ψnat := ?_
    ψφ := ?_
    φψ := ?_ }⟩
  all_goals simp only [htr, tr_idealPowerSystem]
  exacts [fun h => hfnat _ _ h, fun h => hbnat _ _ h, hfb, hbf]

/-- **[Stacks, Tag 0G4R] after a functor.** A pro-isomorphism pushes forward along any functor
(`CategoryTheory.Pro.proIsoWhiskerRight`), so the two inverse sequences of
`Stacks.Duality.cohomologyIdealPowersProIso` stay pro-isomorphic after any `H : X.Modules ⥤ 𝒟`.

The case that matters is `H = DerivedCategory.singleFunctor X.Modules p`, which places both
sequences in cohomological degree `p`: that is the form `CategoryTheory.RestrictionLifting`, and
hence the core case of [Stacks, Tag 0G2H], is stated in. -/
theorem cohomologyIdealPowersProIso_comp [IsNoetherian X] (hF : TermsCoherent F)
    (S : IdealPowerComplexSystem I F) {𝒟 : Type u'} [Category.{v'} 𝒟] (H : X.Modules ⥤ 𝒟) :
    Nonempty (ProIso (cohomologySystem S p ⋙ H)
      (idealPowerSystem I (F.homology p) ⋙ H)) :=
  (cohomologyIdealPowersProIso I F p hF S).map fun e => Pro.proIsoWhiskerRight e H

end Stacks.Duality

end
