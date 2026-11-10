module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule

/-!
# Cohomology of the ideal-power subcomplexes of a complex of module sheaves

For a quasi-coherent ideal sheaf `I` on a scheme `X` and a cochain complex `F` of sheaves of
modules on `X`, the termwise ideal-power multiples `I^n F^i` form subcomplexes `I^n F` of `F`.
Their inclusions, together with the inclusions `I^(n+1) F ⟶ I^n F`, make the cohomology sheaves
into an inverse system

`⋯ → H^p(I³F) → H^p(I²F) → H^p(IF) → H^p(F)`

whose zeroth term is the cohomology of `F` itself.

## Main definitions

* `AlgebraicGeometry.IdealPowerComplexSystem` records the ideal-power subcomplexes and their
  canonical inclusions, together with the resulting inverse system of cohomology sheaves.

## Main results

* `AlgebraicGeometry.idealPowerComplexSystem` constructs the system, including its transition
  maps.
* `AlgebraicGeometry.idealPowerMultiple_le_comap`: a morphism of sheaves of modules carries
  `I^n M` into any subsheaf of the target containing `I^n N`.
* `AlgebraicGeometry.idealPowerMultiple_zero`: the zeroth ideal-power multiple is everything.

## Implementation notes

The termwise ideal powers are `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, and the
transition in each degree is the filtration inclusion `idealPowerMultipleMap`. The construction
is valid for every complex of module sheaves: Noetherianity and coherence are needed only for
subsequent comparison results. The structure explicitly identifies the inclusion in every
degree and requires each transition to commute with the inclusions into the original complex, so
its induced cohomology maps are the canonical ones.

## References

* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.IdealPower

namespace AlgebraicGeometry

/-- The system of termwise ideal-power subcomplexes of `F`, together with
their inclusions and canonical transitions. -/
public structure IdealPowerComplexSystem {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) where
  /-- The complex `I^n F`. -/
  complex : ℕ → CochainComplex X.Modules ℤ
  /-- Inclusion into `F`. -/
  inclusion : ∀ n, complex n ⟶ F
  /-- Its term in degree `i` is the ideal-power multiple of `F^i`. -/
  termIso : ∀ n i, (complex n).X i ≅
    (idealPowerMultiple I n (F.X i)).toSheafOfModules
  /-- The inclusion is the usual inclusion of the ideal-power multiple. -/
  include_f : ∀ n i, (termIso n i).hom ≫
    (idealPowerMultiple I n (F.X i)).ι = (inclusion n).f i
  /-- The transition from `I^(n+1) F` to `I^n F`. -/
  transition : ∀ n, complex (n + 1) ⟶ complex n
  /-- The transition is the inclusion, viewed inside `F`. -/
  transition_include : ∀ n, transition n ≫ inclusion n = inclusion (n + 1)
  /-- The zeroth subcomplex is canonically the original complex. -/
  zeroIso : complex 0 ≅ F
  /-- Its identification with `F` is the inclusion. -/
  zeroIso_hom : zeroIso.hom = inclusion 0

/-- The sheaf `H^p(I^n F)`. -/
public noncomputable abbrev IdealPowerComplexSystem.cohomology
    {X : Scheme.{u}} {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (n : ℕ) (p : ℤ) : X.Modules :=
  (S.complex n).homology p

/-- The canonical identification `H^p(I^0 F) ≅ H^p(F)`. -/
public noncomputable abbrev IdealPowerComplexSystem.cohomologyZeroIso
    {X : Scheme.{u}} {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (p : ℤ) :
    S.cohomology 0 p ≅ F.homology p :=
  HomologicalComplex.homologyMapIso S.zeroIso p

/-- The canonical cohomology transition `H^p(I^(n+1) F) → H^p(I^n F)`. -/
public noncomputable abbrev IdealPowerComplexSystem.cohomologyTransition
    {X : Scheme.{u}} {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (n : ℕ) (p : ℤ) :
    S.cohomology (n + 1) p ⟶ S.cohomology n p :=
  HomologicalComplex.homologyMap (S.transition n) p

/-- The canonical cohomology map `H^p(I^n F) → H^p(F)`. -/
public noncomputable abbrev IdealPowerComplexSystem.cohomologyToOriginal
    {X : Scheme.{u}} {I : X.IdealSheafData} {F : CochainComplex X.Modules ℤ}
    (S : IdealPowerComplexSystem I F) (n : ℕ) (p : ℤ) :
    S.cohomology n p ⟶ F.homology p :=
  HomologicalComplex.homologyMap (S.inclusion n) p

/-- A morphism of sheaves of modules carries `I^n M` into any subsheaf of the target
containing `I^n N`. -/
public lemma idealPowerMultiple_le_comap {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (hq : idealPowerMultiple I n N ≤ Q) :
    idealPowerMultiple I n M ≤ sheafSubmoduleComap f Q := by
  apply (idealPowerMultiple_le_iff I n M _).2
  intro U
  let J := I.ideal U ^ n
  let fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    ModuleCat.Hom.hom (f.val.app (op U.1))
  have hqU : J • (⊤ : Submodule Γ(X, U) Γ(N, U)) ≤ Q.toSubmodule.obj (op U.1) :=
    (idealPowerMultiple_le_iff I n N Q).mp hq U
  have hgen : J • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      (Q.toSubmodule.obj (op U.1)).comap fU := by
    calc
      J • (⊤ : Submodule Γ(X, U) Γ(M, U)) =
          J • ((⊤ : Submodule Γ(X, U) Γ(N, U)).comap fU) := by simp
      _ ≤ (J • (⊤ : Submodule Γ(X, U) Γ(N, U))).comap fU :=
        Submodule.smul_comap_le_comap_smul fU _ _
      _ ≤ (Q.toSubmodule.obj (op U.1)).comap fU := Submodule.comap_mono hqU
  change I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
    (Q.toSubmodule.obj (op U.1)).comap fU
  simpa [J] using hgen

/-- The zeroth ideal-power multiple of `M` is all of `M`. -/
public lemma idealPowerMultiple_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) : idealPowerMultiple I 0 M = ⊤ := by
  apply sheafSubmodule_eq_top_of_affine
  intro U
  simpa using le_idealPowerMultiple_obj I 0 M U

/-- **Stacks Project, Tag 0G4R (transition maps).** The ideal-power
subcomplexes `I^n F` exist and carry their canonical compatible inclusions.
Taking cohomology in any degree gives the maps
`⋯ → H^p(I³F) → H^p(I²F) → H^p(IF) → H^p(F)`. -/
@[stacks 0G4R "transition maps only. This supplies the canonical maps
`… → H^p(I³F) → H^p(I²F) → H^p(IF) → H^p(F)` of the statement, for an arbitrary scheme and an
arbitrary complex of module sheaves. The Artin-Rees part of the tag — the constant `c > 0`, the
inclusion of the image of `H^p(I^nF) → H^p(F)` in `I^(n-c)H^p(F)`, the maps back, and the resulting
pro-isomorphism — is not proved here and needs Noetherianness and coherence."]
public noncomputable def idealPowerComplexSystem {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) :
    IdealPowerComplexSystem I F :=
  let P : ∀ (n : ℕ) (i : ℤ), (F.X i).Submodule := fun n i =>
    idealPowerMultiple I n (F.X i)
  let Q (n : ℕ) (i : ℤ) : X.Modules := (P n i).toSheafOfModules
  let incl (n : ℕ) (i : ℤ) : Q n i ⟶ F.X i := (P n i).ι
  let dmap (n : ℕ) (i j : ℤ) : Q n i ⟶ Q n j :=
    sheafSubmoduleMap (F.d i j) (P n i) (P n j)
      (idealPowerMultiple_le_comap I n (F.d i j) (P n j) le_rfl)
  have dmap_include (n : ℕ) (i j : ℤ) :
      dmap n i j ≫ incl n j = incl n i ≫ F.d i j := by
    change dmap n i j ≫ (P n j).ι = (P n i).ι ≫ F.d i j
    exact sheafSubmoduleMap_comp_ι (F.d i j) (P n i) (P n j)
      (idealPowerMultiple_le_comap I n (F.d i j) (P n j) le_rfl)
  let K : ℕ → CochainComplex X.Modules ℤ := fun n =>
    { X := fun i => Q n i
      d := fun i j => dmap n i j
      shape := by
        intro i j hij
        dsimp [dmap]
        rw [F.shape i j hij]
        exact sheafSubmoduleMap_zero _ _ _
      d_comp_d' := by
        intro i j k hij hjk
        apply cancel_sheafSubmodule_ι (P n k)
        change (dmap n i j ≫ dmap n j k) ≫ incl n k = 0 ≫ incl n k
        rw [Category.assoc, dmap_include, ← Category.assoc, dmap_include,
          Category.assoc, F.d_comp_d]
        simp }
  let inc (n : ℕ) : K n ⟶ F :=
    { f := fun i => incl n i
      comm' := by
        intro i j hij
        change incl n i ≫ F.d i j = dmap n i j ≫ incl n j
        exact (dmap_include n i j).symm }
  let tmap (n : ℕ) (i : ℤ) : Q (n + 1) i ⟶ Q n i :=
    idealPowerMultipleMap I (F.X i) (Nat.le_succ n)
  have tmap_include (n : ℕ) (i : ℤ) :
      tmap n i ≫ incl n i = incl (n + 1) i :=
    idealPowerMultipleMap_comp_ι I (F.X i) (Nat.le_succ n)
  let transition (n : ℕ) : K (n + 1) ⟶ K n :=
    { f := tmap n
      comm' := by
        intro i j hij
        change tmap n i ≫ dmap n i j = dmap (n + 1) i j ≫ tmap n j
        apply cancel_sheafSubmodule_ι (P n j)
        calc
          (tmap n i ≫ dmap n i j) ≫ incl n j =
              tmap n i ≫ (dmap n i j ≫ incl n j) := Category.assoc _ _ _
          _ = tmap n i ≫ (incl n i ≫ F.d i j) :=
            congrArg (fun f => tmap n i ≫ f) (dmap_include n i j)
          _ = (tmap n i ≫ incl n i) ≫ F.d i j := (Category.assoc _ _ _).symm
          _ = incl (n + 1) i ≫ F.d i j :=
            congrArg (fun f => f ≫ F.d i j) (tmap_include n i)
          _ = dmap (n + 1) i j ≫ incl (n + 1) j := by
                symm
                exact dmap_include (n + 1) i j
          _ = dmap (n + 1) i j ≫ (tmap n j ≫ incl n j) :=
            congrArg (fun f => dmap (n + 1) i j ≫ f) (tmap_include n j).symm
          _ = (dmap (n + 1) i j ≫ tmap n j) ≫ incl n j :=
            (Category.assoc _ _ _).symm }
  haveI : ∀ i : ℤ, IsIso ((inc 0).f i) := by
    intro i
    change IsIso ((P 0 i).ι)
    change IsIso ((idealPowerMultiple I 0 (F.X i)).ι)
    rw [idealPowerMultiple_zero I (F.X i)]
    exact (sheafTopIso (F.X i)).isIso_hom
  let zeroIso : K 0 ≅ F :=
    HomologicalComplex.Hom.isoOfComponents (fun i => asIso ((inc 0).f i))
      (by intro i j hij; exact (inc 0).comm i j)
  { complex := K
    inclusion := inc
    termIso := fun n i => Iso.refl _
    include_f := by intro n i; rfl
    transition := transition
    transition_include := by
      intro n
      apply HomologicalComplex.Hom.ext
      funext i
      change tmap n i ≫ incl n i = incl (n + 1) i
      exact tmap_include n i
    zeroIso := zeroIso
    zeroIso_hom := by
      apply HomologicalComplex.Hom.ext
      funext i
      change (asIso ((inc 0).f i)).hom = (inc 0).f i
      rfl }

end AlgebraicGeometry
