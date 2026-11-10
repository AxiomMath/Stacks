module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The value at the ring of an exact linear endofunctor of modules

Let `Λ` be a commutative ring and `G` an exact `Λ`-linear endofunctor of the category of
`Λ`-modules, for instance taking sections over an object on which sections are exact of the
constant sheaf. Then `G(Λ)` controls `G` on quotients: for a finitely generated ideal `K`, the
map `G(Λ) → G(Λ/K)` is surjective with kernel `K·G(Λ)`. If `Λ` is Noetherian, `G(Λ)` is a flat
`Λ`-module: a relation `∑ fᵢ aᵢ = 0` in `G(Λ)` lifts to an element of `G(Λⁿ)` killed by
`G(f) : G(Λⁿ) → G(Λ)`, hence comes from `G(ker f)`, and the finitely many generators of `ker f`
make the relation trivial.

## Main results

* `CategoryTheory.Functor.surjective_map_mkQ` and `CategoryTheory.Functor.ker_map_mkQ`:
  `G(Λ) → G(Λ/K)` is surjective with kernel `K·G(Λ)`.
* `CategoryTheory.Functor.flat_obj_unitModule`: `G(Λ)` is flat over a Noetherian ring.

## Implementation notes

Exactness of `G` is asked as preservation of finite limits and of finite colimits. Flatness is
checked with the equational criterion `Module.Flat.iff_forall_isTrivialRelation`.

## References

* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {Λ : Type u} [CommRing Λ] (G : ModuleCat.{u} Λ ⥤ ModuleCat.{u} Λ) [G.Additive]
  [G.Linear Λ] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The `Λ`-module `Λ`. -/
abbrev unitModule (Λ : Type u) [CommRing Λ] : ModuleCat.{u} Λ := ModuleCat.of Λ Λ

omit [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- `G` sends multiplication by `r` on `M` to multiplication by `r` on `G(M)`. -/
theorem map_smul_id_apply (r : Λ) {M : ModuleCat.{u} Λ} (x : G.obj M) :
    (G.map (r • 𝟙 M)).hom x = r • x := by
  rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- An element of `G(M)` killed by `G(g)` comes from `G(f)` when `f` is the kernel of `g`. -/
private theorem exists_map_apply_of_forall_exists {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {K M M' : ModuleCat.{u} R} (f : K ⟶ M) (g : M ⟶ M')
    (hfg : f ≫ g = 0) (h : ∀ y, g.hom y = 0 → ∃ z, f.hom z = y) (x : F.obj M)
    (hx : (F.map g).hom x = 0) : ∃ y, (F.map f).hom y = x := by
  have hS : (ShortComplex.mk f g hfg).Exact := (ShortComplex.moduleCat_exact_iff _).2 h
  exact (ShortComplex.moduleCat_exact_iff _).1 (hS.map F) x hx

/-- `G` sends a surjection to a surjection. -/
private theorem surjective_map_of_surjective {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (hf : Function.Surjective f.hom) : Function.Surjective (F.map f).hom := by
  have : Epi f := (ModuleCat.epi_iff_surjective _).2 hf
  exact (ModuleCat.epi_iff_surjective _).1 (F.map_epi _)

omit [Linear Λ G] in
/-- An element of `G(M)` killed by `G(M → M/N)` comes from `G(N)`. -/
theorem exists_map_subtype_apply {M : ModuleCat.{u} Λ} (N : Submodule Λ M) (x : G.obj M)
    (hx : (G.map (ModuleCat.ofHom N.mkQ)).hom x = 0) :
    ∃ y, (G.map (ModuleCat.ofHom N.subtype)).hom y = x :=
  G.exists_map_apply_of_forall_exists (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
    (by ext; simp)
    (fun y hy => ⟨⟨y, (Submodule.Quotient.mk_eq_zero N).1 hy⟩, rfl⟩) x hx

omit [Linear Λ G] in
/-- An element of `G(M)` killed by `G(g)` comes from `G(ker g)`. -/
theorem exists_map_subtype_apply_of_ker {M M' : ModuleCat.{u} Λ} (g : M ⟶ M') (x : G.obj M)
    (hx : (G.map g).hom x = 0) :
    ∃ y, (G.map (ModuleCat.ofHom (LinearMap.ker g.hom).subtype)).hom y = x :=
  G.exists_map_apply_of_forall_exists (ModuleCat.ofHom (LinearMap.ker g.hom).subtype) g
    (by ext ⟨y, hy⟩; exact hy) (fun y hy => ⟨⟨y, hy⟩, rfl⟩) x hx

omit [Linear Λ G] in
/-- **`G` is surjective on the quotient map by a submodule.** -/
theorem surjective_map_mkQ {M : ModuleCat.{u} Λ} (N : Submodule Λ M) :
    Function.Surjective (G.map (ModuleCat.ofHom N.mkQ)).hom :=
  G.surjective_map_of_surjective _ (Submodule.mkQ_surjective N)

/-- The surjection `Λᵏ → N` given by a finite family `v` spanning a submodule `N`. -/
def linearCombinationOfSpanEq {M : Type u} [AddCommGroup M] [Module Λ M] {k : ℕ} (v : Fin k → M)
    {N : Submodule Λ M} (hv : Submodule.span Λ (Set.range v) = N) : (Fin k → Λ) →ₗ[Λ] N :=
  Fintype.linearCombination Λ (fun i => ⟨v i, hv ▸ Submodule.subset_span ⟨i, rfl⟩⟩)

/-- The map `linearCombinationOfSpanEq v hv` sends `c` to `∑ i, c i • v i`. -/
theorem subtype_linearCombinationOfSpanEq_apply {M : Type u} [AddCommGroup M] [Module Λ M]
    {k : ℕ} (v : Fin k → M) {N : Submodule Λ M} (hv : Submodule.span Λ (Set.range v) = N)
    (c : Fin k → Λ) : (linearCombinationOfSpanEq v hv c : M) = ∑ i, c i • v i := by
  simp [linearCombinationOfSpanEq, Fintype.linearCombination_apply]

/-- The map `linearCombinationOfSpanEq v hv : Λᵏ → N` is surjective. -/
theorem surjective_linearCombinationOfSpanEq {M : Type u} [AddCommGroup M] [Module Λ M]
    {k : ℕ} (v : Fin k → M) {N : Submodule Λ M} (hv : Submodule.span Λ (Set.range v) = N) :
    Function.Surjective (linearCombinationOfSpanEq v hv) := by
  rintro ⟨x, hx⟩
  rw [← hv] at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hx
  exact ⟨c, Subtype.ext (subtype_linearCombinationOfSpanEq_apply v hv c)⟩

omit [Linear Λ G] in
/-- **`G` is surjective on a surjection from a finite free module.** -/
theorem surjective_map_linearCombinationOfSpanEq {M : ModuleCat.{u} Λ} {k : ℕ} (v : Fin k → M)
    {N : Submodule Λ M} (hv : Submodule.span Λ (Set.range v) = N) :
    Function.Surjective (G.map (ModuleCat.ofHom (linearCombinationOfSpanEq v hv))).hom :=
  G.surjective_map_of_surjective _ (surjective_linearCombinationOfSpanEq v hv)

/-- The projection `Λᵏ → Λ` onto a coordinate. -/
abbrev coordProj (k : ℕ) (i : Fin k) : ModuleCat.of Λ (Fin k → Λ) ⟶ unitModule Λ :=
  ModuleCat.ofHom (LinearMap.proj i)

/-- The inclusion `Λ → Λᵏ` of a coordinate. -/
abbrev coordSingle (k : ℕ) (i : Fin k) : unitModule Λ ⟶ ModuleCat.of Λ (Fin k → Λ) :=
  ModuleCat.ofHom (LinearMap.single Λ (fun _ => Λ) i)

/-- A map out of `Λᵏ` into `Λ` is a linear combination of the coordinate projections. -/
theorem eq_sum_smul_coordProj {k : ℕ} (f : ModuleCat.of Λ (Fin k → Λ) ⟶ unitModule Λ) :
    f = ∑ i, f.hom (Pi.single i 1) • coordProj k i := by
  ext c
  simp [Pi.single_apply]

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- For `f : Λᵏ → Λ`, the map `G(f)` is the combination of the maps `G(coordProj k i)` with
coefficients `f(eᵢ)`. -/
theorem map_apply_eq_sum {k : ℕ} (f : ModuleCat.of Λ (Fin k → Λ) ⟶ unitModule Λ)
    (z : G.obj (ModuleCat.of Λ (Fin k → Λ))) :
    (G.map f).hom z = ∑ i, f.hom (Pi.single i 1) • (G.map (coordProj k i)).hom z := by
  conv_lhs => rw [eq_sum_smul_coordProj f, G.map_sum]
  simp

/-- For an ideal `N` of `Λ`, the submodule `N • ⊤` of `Λ` is `N`. -/
theorem smul_top_unitModule (N : Ideal Λ) : (N • ⊤ : Submodule Λ (unitModule Λ)) = N := by
  change N • (⊤ : Ideal Λ) = N
  rw [smul_eq_mul, Ideal.mul_top]

/-- **The kernel of `G(Λ) → G(Λ/N)` is `N·G(Λ)`**, for a finitely generated ideal `N`. -/
theorem ker_map_mkQ (N : Ideal Λ) (hN : N.FG) :
    LinearMap.ker (G.map (ModuleCat.ofHom (N • ⊤ : Submodule Λ (unitModule Λ)).mkQ)).hom =
      (N • ⊤ : Submodule Λ (G.obj (unitModule Λ))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := G.exists_map_subtype_apply _ x hx
    obtain ⟨k, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
    have hv' : Submodule.span Λ (Set.range (v : Fin k → unitModule Λ)) =
        (N • ⊤ : Submodule Λ (unitModule Λ)) := by
      rw [smul_top_unitModule]
      exact hv
    obtain ⟨w, rfl⟩ := G.surjective_map_linearCombinationOfSpanEq v hv' y
    rw [← ModuleCat.comp_apply, ← G.map_comp, map_apply_eq_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h : ((linearCombinationOfSpanEq v hv' (Pi.single i 1) : _) : Λ) ∈
        (N • ⊤ : Submodule Λ (unitModule Λ)) := (linearCombinationOfSpanEq v hv' (Pi.single i 1)).2
    exact (smul_top_unitModule N).le h
  · rw [Submodule.smul_le]
    intro r hr a _
    rw [LinearMap.mem_ker, LinearMap.map_smul_of_tower, ← G.map_smul_id_apply r,
      ← ModuleCat.comp_apply, ← G.map_comp]
    have : ModuleCat.ofHom (N • ⊤ : Submodule Λ (unitModule Λ)).mkQ ≫
        (r • 𝟙 (ModuleCat.of Λ (unitModule Λ ⧸ (N • ⊤ : Submodule Λ (unitModule Λ))))) = 0 := by
      ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ModuleCat.hom_ofHom, Submodule.mkQ_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr trivial
    rw [this, G.map_zero]
    rfl

omit [Linear Λ G] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- The `j`-th coordinate projection under `G` of `∑ i, G(coordSingle l i)(x i)` is `x j`. -/
theorem map_coordProj_sum_map_coordSingle {l : ℕ} (x : Fin l → G.obj (unitModule Λ)) (j : Fin l) :
    (G.map (coordProj l j)).hom (∑ i, (G.map (coordSingle l i)).hom (x i)) = x j := by
  rw [_root_.map_sum]
  simp_rw [← ModuleCat.comp_apply, ← G.map_comp]
  rw [Finset.sum_eq_single j]
  · have : coordSingle (Λ := Λ) l j ≫ coordProj l j = 𝟙 (unitModule Λ) := by
      ext; simp
    rw [this, G.map_id]
    rfl
  · intro i _ hij
    have : coordSingle (Λ := Λ) l i ≫ coordProj l j = 0 := by
      ext; simp [Ne.symm hij]
    rw [this, G.map_zero]
    rfl
  · simp

/-- **The value at `Λ` of an exact `Λ`-linear endofunctor of `Λ`-modules is flat**, for a
Noetherian ring `Λ`. -/
theorem flat_obj_unitModule [IsNoetherianRing Λ] : Module.Flat Λ (G.obj (unitModule Λ)) := by
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hfx
  let F : ModuleCat.of Λ (Fin l → Λ) ⟶ unitModule Λ :=
    ModuleCat.ofHom (Fintype.linearCombination Λ f)
  obtain ⟨z, hzdef⟩ : ∃ z, z = ∑ i, (G.map (coordSingle l i)).hom (x i) := ⟨_, rfl⟩
  have hz : (G.map F).hom z = 0 := by
    rw [map_apply_eq_sum, hzdef]
    simp_rw [map_coordProj_sum_map_coordSingle]
    simpa [F, Fintype.linearCombination_apply, Pi.single_apply] using hfx
  let Kf : Submodule Λ (Fin l → Λ) := LinearMap.ker (Fintype.linearCombination Λ f)
  obtain ⟨k, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian Kf)
  obtain ⟨y, hy⟩ := G.exists_map_subtype_apply_of_ker F z hz
  obtain ⟨t, rfl⟩ := G.surjective_map_linearCombinationOfSpanEq
    (M := ModuleCat.of Λ (Fin l → Λ)) w (N := LinearMap.ker F.hom) hw y
  refine ⟨k, fun i j => w j i, fun j => (G.map (coordProj k j)).hom t, fun i => ?_, fun j => ?_⟩
  · have hx : x i = (G.map (coordProj l i)).hom z := by
      rw [hzdef, map_coordProj_sum_map_coordSingle]
    rw [hx, ← hy, ← ModuleCat.comp_apply, ← G.map_comp, ← ModuleCat.comp_apply, ← G.map_comp,
      map_apply_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change ((linearCombinationOfSpanEq w hw (Pi.single j 1) : Kf) : Fin l → Λ) i = w j i
    rw [subtype_linearCombinationOfSpanEq_apply, Finset.sum_apply,
      Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · have hwj : w j ∈ Kf := hw ▸ Submodule.subset_span ⟨j, rfl⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hwj
    simpa [mul_comm] using hwj

end CategoryTheory.Functor
