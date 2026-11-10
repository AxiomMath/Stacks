module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.DFinsupp
public import StacksFrontier.Algebra.Homology.Eta

/-!
# Iterated décalage: `η_f ∘ η_g = η_{fg}`

Let `A` be a commutative ring, `f, g ∈ A`, and let `M^•` be a cochain complex of `A`-modules.
Inside the localization `M^i_{fg}`, in which `f`, `g` and `f * g` are units, the décalage of a
degreewise family of submodules `C` with respect to a unit `u` is
`(η_u C)^i = { x ∈ u^i C^i : d^i x ∈ u^{i+1} C^{i+1} }`. We show that
`η_f (η_g M^•) = η_{fg} M^•`, both degreewise and as cochain complexes.

## Main definitions

* `EtaDecalage.fUnit`, `EtaDecalage.gUnit`, `EtaDecalage.fgUnit`: the units of `A_{fg}` given
  by `f`, `g` and `f * g`.
* `EtaDecalage.SubmoduleFamily`: a degreewise family of submodules of the localized
  complex `M^•_{fg}`.
* `EtaDecalage.dLoc`: the localized differential `M^i_{fg} → M^{i+1}_{fg}`.
* `EtaDecalage.SubmoduleFamily.toCochainComplex`: the cochain complex of `A`-modules formed by
  a family preserved by the localized differential.
* `EtaDecalage.baseFamily`: the family whose degree-`i` term is the image of `M^i` in
  `M^i_{fg}`.
* `EtaDecalage.etaSub`: the décalage of a family with respect to a unit of `A_{fg}`.
* `EtaDecalage.etaG`, `EtaDecalage.etaFG`, `EtaDecalage.etaFetaG`: the décalage families
  `η_g M^•`, `η_{fg} M^•` and `η_f (η_g M^•)`.

## Main results

* `EtaDecalage.etaFetaG_eq_etaFG`: `η_f (η_g M^•)` and `η_{fg} M^•` agree in every degree.
* `EtaDecalage.etaFetaG_eq_etaFG_cochainComplex`: `η_f (η_g M^•)` and `η_{fg} M^•` are equal
  as cochain complexes.

## Implementation notes

All submodules are taken inside the single ambient localization
`LocalizedModule (Submonoid.powers (f * g)) (M i)`, which serves simultaneously as `(M^i_g)_f`
and `(M^i_f)_g`. A cochain complex is encoded by the modules `M`, the differentials `d` of
degree `+1`, and the relation `d^{i+1} ∘ d^i = 0`.

## References

* [Stacks, Tag 0F7U]
-/

@[expose] public section

namespace EtaDecalage

open Eta

variable {A : Type*} [CommRing A] (f g : A)

/-- The multiplicative submonoid of powers of `f * g`. -/
abbrev powersFG : Submonoid A := Submonoid.powers (f * g)

/-- The unit of `A_{fg}` given by `f`. -/
noncomputable def fUnit : (Localization.Away (f * g))ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_right f g)).unit

/-- The unit of `A_{fg}` given by `g`. -/
noncomputable def gUnit : (Localization.Away (f * g))ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_left g f)).unit

/-- The unit `fUnit * gUnit` of `A_{fg}`, the image of `f * g`. -/
noncomputable def fgUnit : (Localization.Away (f * g))ˣ := fUnit f g * gUnit f g

/-- `fgUnit f g` is the product `fUnit f g * gUnit f g`. -/
theorem fgUnit_def : fgUnit f g = fUnit f g * gUnit f g := rfl

/-- The unit `fUnit` acts on any localization at the powers of `f * g` by the `A`-scalar `f`. -/
@[simp]
theorem fUnit_units_smul {N : Type*} [AddCommGroup N] [Module A N]
    (x : LocalizedModule (powersFG f g) N) : (fUnit f g) • x = f • x := by
  rw [Units.smul_def, fUnit, IsUnit.unit_spec]
  exact algebraMap_smul (Localization.Away (f * g)) f x

/-- The unit `gUnit` acts on any localization at the powers of `f * g` by the `A`-scalar `g`. -/
@[simp]
theorem gUnit_units_smul {N : Type*} [AddCommGroup N] [Module A N]
    (x : LocalizedModule (powersFG f g) N) : (gUnit f g) • x = g • x := by
  rw [Units.smul_def, gUnit, IsUnit.unit_spec]
  exact algebraMap_smul (Localization.Away (f * g)) g x

/-! ## The complex data

A cochain complex of `A`-modules with differential of degree `+1` is modeled by the
family of modules `M`, the differentials `d`, and the cochain relation
`d^{i+1} ∘ d^i = 0`. -/

variable (M : ℤ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  (d : ∀ i, M i →ₗ[A] M (i + 1))

/-- The localized differential in degree `i`, `M^i_{fg} → M^{i+1}_{fg}`. -/
noncomputable def dLoc (i : ℤ) :
    LocalizedModule (powersFG f g) (M i) →ₗ[A] LocalizedModule (powersFG f g) (M (i + 1)) :=
  locMap (powersFG f g) (d i)

/-- The localized differentials compose to zero, given the ambient cochain relation. -/
theorem dLoc_comp_dLoc (i : ℤ) (hdd : (d (i + 1)).comp (d i) = 0) :
    (dLoc f g M d (i + 1)).comp (dLoc f g M d i) = 0 :=
  locMap_comp_locMap (powersFG f g) (d i) (d (i + 1)) hdd

/-- `dLoc` in degree `i` is the localization of `d i` at the powers of `f * g`. -/
theorem dLoc_def (i : ℤ) : dLoc f g M d i = locMap (powersFG f g) (d i) := rfl

/-- A degreewise family of submodules of the localized complex, with degree-`i` term a
submodule of `M^i_{fg}`. -/
abbrev SubmoduleFamily : Type _ := ∀ i, Submodule A (LocalizedModule (powersFG f g) (M i))

namespace SubmoduleFamily

variable {f g M d}

/-- The cochain complex of `A`-modules with terms `N i` and differential the restriction of
the localized differential `dLoc`, for a family `N` preserved by `dLoc`. -/
noncomputable def toCochainComplex (N : SubmoduleFamily f g M)
    (preserve : ∀ i, (N i).map (dLoc f g M d i) ≤ N (i + 1))
    (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.of (fun i => ModuleCat.of A (N i))
    (fun i => ModuleCat.ofHom ((dLoc f g M d i).restrict
      (fun _ hx => preserve i (Submodule.mem_map_of_mem hx))))
    (fun i => by
      ext x
      have hcomp := LinearMap.congr_fun (dLoc_comp_dLoc f g M d i (hdd i))
        (x : LocalizedModule (powersFG f g) (M i))
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hcomp
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, LinearMap.restrict_apply,
        ZeroMemClass.coe_zero]
      exact hcomp)

section

variable {N : SubmoduleFamily f g M}
  {preserve : ∀ i, (N i).map (dLoc f g M d i) ≤ N (i + 1)}
  {hdd : ∀ i, (d (i + 1)).comp (d i) = 0}

/-- The degree-`i` term of `toCochainComplex N preserve hdd` is `N i`. -/
@[simp]
theorem toCochainComplex_X (i : ℤ) :
    (toCochainComplex N preserve hdd).X i = ModuleCat.of A (N i) := rfl

/-- The differential of `toCochainComplex N preserve hdd` from degree `i` to `i + 1` is the
restriction of `dLoc` to `N i`. -/
@[simp]
theorem toCochainComplex_d (i : ℤ) :
    (toCochainComplex N preserve hdd).d i (i + 1) =
      ModuleCat.ofHom ((dLoc f g M d i).restrict
        (fun _ hx => preserve i (Submodule.mem_map_of_mem hx))) :=
  CochainComplex.of_d (fun i => ModuleCat.of A (N i))
    (fun i => ModuleCat.ofHom ((dLoc f g M d i).restrict
      (fun _ hx => preserve i (Submodule.mem_map_of_mem hx)))) i

end

end SubmoduleFamily

/-- The family whose degree-`i` term is the image of `M^i` in `M^i_{fg}`. -/
noncomputable def baseFamily : SubmoduleFamily f g M :=
  fun i => LinearMap.range (LocalizedModule.mkLinearMap (powersFG f g) (M i))

/-- The degree-`i` term of `baseFamily` is the image of `M^i` in `M^i_{fg}`. -/
theorem baseFamily_apply (i : ℤ) :
    baseFamily f g M i =
      LinearMap.range (LocalizedModule.mkLinearMap (powersFG f g) (M i)) := rfl

/-- The décalage operator on families of submodules with respect to a unit `u` of `A_{fg}`.
Given a family `C` (degree-`i` term `C i ⊆ M^i_{fg}`),
`(η_u C)^i = { x ∈ u^i (C i) : d^i x ∈ u^{i+1} (C (i+1)) }`. -/
noncomputable def etaSub (u : (Localization.Away (f * g))ˣ) (C : SubmoduleFamily f g M) :
    SubmoduleFamily f g M :=
  fun i => etaTerm (powersFG f g) u (d i) i (C i) (C (i + 1))

/-- The degree-`i` term of `etaSub f g M d u C` is `etaTerm` applied to `C i` and `C (i + 1)`. -/
theorem etaSub_apply (u : (Localization.Away (f * g))ˣ) (C : SubmoduleFamily f g M) (i : ℤ) :
    etaSub f g M d u C i = etaTerm (powersFG f g) u (d i) i (C i) (C (i + 1)) := rfl

/-- An element `x` of `M^i_{fg}` lies in `(η_u C)^i` if and only if `x ∈ u^i (C i)` and
`dLoc x ∈ u^{i+1} (C (i + 1))`. -/
theorem mem_etaSub (u : (Localization.Away (f * g))ˣ) (C : SubmoduleFamily f g M) (i : ℤ)
    {x : LocalizedModule (powersFG f g) (M i)} :
    x ∈ etaSub f g M d u C i ↔ x ∈ zsmulSub (powersFG f g) u i (C i) ∧
      dLoc f g M d i x ∈ zsmulSub (powersFG f g) u (i + 1) (C (i + 1)) :=
  Iff.rfl

/-- The localized differential carries the degree-`i` term of a décalage into its
degree-`(i + 1)` term, so every décalage family is preserved by `dLoc`. -/
theorem etaSub_map_le (u : (Localization.Away (f * g))ˣ) (C : SubmoduleFamily f g M)
    (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) (i : ℤ) :
    (etaSub f g M d u C i).map (dLoc f g M d i) ≤ etaSub f g M d u C (i + 1) := by
  rintro y ⟨x, hx, rfl⟩
  exact locMap_etaTerm_mem _ u (d i) (d (i + 1)) (hdd i) i (C i) (C (i + 1)) (C (i + 1 + 1)) hx

/-- `η_g M^•`: the décalage of the localized complex with respect to `g`. -/
noncomputable def etaG : SubmoduleFamily f g M :=
  etaSub f g M d (gUnit f g) (baseFamily f g M)

/-- `η_{fg} M^•`: the décalage of the localized complex with respect to `f * g`. -/
noncomputable def etaFG : SubmoduleFamily f g M :=
  etaSub f g M d (fgUnit f g) (baseFamily f g M)

/-- `η_f (η_g M^•)`: the iterated décalage, first by `g`, then by `f`. -/
noncomputable def etaFetaG : SubmoduleFamily f g M :=
  etaSub f g M d (fUnit f g) (etaG f g M d)

/-- `etaG` is the décalage of `baseFamily` with respect to `gUnit`. -/
theorem etaG_def : etaG f g M d = etaSub f g M d (gUnit f g) (baseFamily f g M) := rfl

/-- `etaFG` is the décalage of `baseFamily` with respect to `fgUnit`. -/
theorem etaFG_def : etaFG f g M d = etaSub f g M d (fgUnit f g) (baseFamily f g M) := rfl

/-- `etaFetaG` is the décalage of `etaG` with respect to `fUnit`. -/
theorem etaFetaG_def : etaFetaG f g M d = etaSub f g M d (fUnit f g) (etaG f g M d) := rfl

/-- The localized differential carries the degree-`i` term of `etaG` into its degree-`(i + 1)`
term. -/
theorem etaG_map_le (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) (i : ℤ) :
    (etaG f g M d i).map (dLoc f g M d i) ≤ etaG f g M d (i + 1) :=
  etaSub_map_le f g M d _ _ hdd i

/-- The localized differential carries the degree-`i` term of `etaFG` into its
degree-`(i + 1)` term. -/
theorem etaFG_map_le (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) (i : ℤ) :
    (etaFG f g M d i).map (dLoc f g M d i) ≤ etaFG f g M d (i + 1) :=
  etaSub_map_le f g M d _ _ hdd i

/-- The localized differential carries the degree-`i` term of `etaFetaG` into its
degree-`(i + 1)` term. -/
theorem etaFetaG_map_le (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) (i : ℤ) :
    (etaFetaG f g M d i).map (dLoc f g M d i) ≤ etaFetaG f g M d (i + 1) :=
  etaSub_map_le f g M d _ _ hdd i

variable {f g M d} in
/-- For a cochain complex `M^•` of `A`-modules, `η_f (η_g M^•)` and `η_{fg} M^•` are the same
submodule of the localization `M^i_{fg}` in every degree `i`. -/
theorem etaFetaG_eq_etaFG (hdd : ∀ i, (d (i + 1)).comp (d i) = 0) :
    etaFetaG f g M d = etaFG f g M d := by
  funext i
  change zsmulSub (powersFG f g) (fUnit f g) i
        (zsmulSub (powersFG f g) (gUnit f g) i (baseFamily f g M i) ⊓
          (zsmulSub (powersFG f g) (gUnit f g) (i + 1) (baseFamily f g M (i + 1))).comap
            (dLoc f g M d i)) ⊓
      (zsmulSub (powersFG f g) (fUnit f g) (i + 1)
        (zsmulSub (powersFG f g) (gUnit f g) (i + 1) (baseFamily f g M (i + 1)) ⊓
          (zsmulSub (powersFG f g) (gUnit f g) (i + 1 + 1)
            (baseFamily f g M (i + 1 + 1))).comap
            (dLoc f g M d (i + 1)))).comap (dLoc f g M d i)
      = zsmulSub (powersFG f g) (fgUnit f g) i (baseFamily f g M i) ⊓
        (zsmulSub (powersFG f g) (fgUnit f g) (i + 1) (baseFamily f g M (i + 1))).comap
          (dLoc f g M d i)
  simp only [dLoc_def]
  rw [zsmulSub_inf, zsmulSub_zsmulSub, zsmulSub_comap,
      zsmulSub_inf, zsmulSub_zsmulSub, zsmulSub_comap,
      Submodule.comap_inf, fgUnit_def]
  have hZ : ((zsmulSub (powersFG f g) (fUnit f g) (i + 1)
        (zsmulSub (powersFG f g) (gUnit f g) (i + 1 + 1)
          (baseFamily f g M (i + 1 + 1)))).comap (locMap (powersFG f g) (d (i + 1)))).comap
            (locMap (powersFG f g) (d i)) = ⊤ := by
    ext x
    have hcomp := LinearMap.congr_fun (dLoc_comp_dLoc f g M d i (hdd i)) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, dLoc_def] at hcomp
    simp only [Submodule.mem_comap, Submodule.mem_top, iff_true, hcomp]
    exact Submodule.zero_mem _
  rw [hZ, inf_top_eq]
  have hincl :
      zsmulSub (powersFG f g) (fUnit f g * gUnit f g) i (baseFamily f g M i) ⊓
        (zsmulSub (powersFG f g) (fUnit f g * gUnit f g) (i + 1)
          (baseFamily f g M (i + 1))).comap (locMap (powersFG f g) (d i))
      ≤ (zsmulSub (powersFG f g) (fUnit f g) i
          (zsmulSub (powersFG f g) (gUnit f g) (i + 1) (baseFamily f g M (i + 1)))).comap
          (locMap (powersFG f g) (d i)) := by
    rintro x ⟨_, hxY⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, mem_zsmulSub] at hxY ⊢
    obtain ⟨b', hb', hb'eq⟩ := hxY
    have hc : ((fUnit f g : (Localization.Away (f * g))ˣ)) • b' ∈ baseFamily f g M (i + 1) := by
      rw [baseFamily_apply, fUnit_units_smul]
      exact Submodule.smul_mem _ f hb'
    refine ⟨(gUnit f g) ^ (i + 1) • ((fUnit f g : (Localization.Away (f * g))ˣ) • b'),
      ⟨_, hc, rfl⟩, ?_⟩
    rw [← hb'eq, mul_zpow, smul_smul, smul_smul]
    congr 1
    rw [mul_right_comm, ← zpow_add_one]
  rw [inf_right_comm]
  exact inf_of_le_left hincl

/-- For a cochain complex `M^•` of `A`-modules, the cochain complexes `η_f (η_g M^•)` and
`η_{fg} M^•` in `CochainComplex (ModuleCat A) ℤ` are equal. -/
@[stacks 0F7U]
theorem etaFetaG_eq_etaFG_cochainComplex (hdd : ∀ i, (d (i + 1)).comp (d i) = 0)
    (preserve : ∀ i, ((etaFetaG (f := f) (g := g) (d := d)) i).map (dLoc f g M d i)
      ≤ (etaFetaG (f := f) (g := g) (d := d)) (i + 1)) :
    (etaFetaG (f := f) (g := g) (d := d)).toCochainComplex preserve hdd
      = (etaFG (f := f) (g := g) (d := d)).toCochainComplex
          (by rw [← etaFetaG_eq_etaFG hdd]; exact preserve) hdd := by
  congr 1
  exact etaFetaG_eq_etaFG hdd

end EtaDecalage
