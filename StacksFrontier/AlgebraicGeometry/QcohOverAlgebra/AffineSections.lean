module

public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Locality
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# The sections of a finite-type quasi-coherent module over an algebra sheaf

Let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras on a scheme `X` and let `N` be
a module over the sheaf of rings underlying `A` which is quasi-coherent and of finite type.
Over an affine open `U` of `X` the sections `Γ(N, U)` form a finite `A(U)`-module.

## Main definitions

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.multiplierIdeal`: for a ring map `φ : R →+* S`, an
  `S`-submodule `T` and an element `t`, the ideal of `r : R` with `φ r • t ∈ T`.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.baseModule`: `N` read as an `𝒪_X`-module.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.moduleSections`: the `A(U)`-module structure on
  `Γ(N, U)`.

## Main results

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.base_smul_eq`: the `Γ(X, U)`-action on `Γ(N, U)` is
  the `A(U)`-action along the structure map of `A`.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.span_eq_top_of_generatesLocally`: a finite family of
  sections generating `N` locally over an affine open `U`, in the sense of
  `Stacks.SheafOfModules.GeneratesLocally`, spans `Γ(N, U)` over `A(U)`.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.module_finite_sections_of_generatesLocally`: hence
  `Γ(N, U)` is a finite `A(U)`-module.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.exists_affineCover_module_finite`: for `N` of finite
  type, the affine opens with finite sections cover `X`.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.QcohOverAlgebra

/-! ### Denominator clearing, over an abstract ring map -/

section Algebra

variable {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M]

/-- The ideal of `r : R` with `φ r • t` in a given `S`-submodule, for a ring map
`φ : R →+* S`. -/
def multiplierIdeal (φ : R →+* S) (T : Submodule S M) (t : M) : Ideal R where
  carrier := {r | φ r • t ∈ T}
  add_mem' := by
    intro p q hp hq
    have hp' : φ p • t ∈ T := hp
    have hq' : φ q • t ∈ T := hq
    change φ (p + q) • t ∈ T
    rw [map_add, add_smul]
    exact T.add_mem hp' hq'
  zero_mem' := by
    change φ 0 • t ∈ T
    rw [map_zero, zero_smul]
    exact T.zero_mem
  smul_mem' := by
    intro p q hq
    have hq' : φ q • t ∈ T := hq
    change φ (p • q) • t ∈ T
    rw [smul_eq_mul, map_mul, mul_smul]
    exact T.smul_mem _ hq'

/-- Membership in `multiplierIdeal φ T t` is the condition `φ r • t ∈ T`. -/
theorem mem_multiplierIdeal_iff {φ : R →+* S} {T : Submodule S M} {t : M} {r : R} :
    r ∈ multiplierIdeal φ T t ↔ φ r • t ∈ T := Iff.rfl

/-- If `1` multiplies `t` into `T`, then `t` is in `T`. -/
theorem mem_of_one_mem_multiplierIdeal {φ : R →+* S} {T : Submodule S M} {t : M}
    (h : (1 : R) ∈ multiplierIdeal φ T t) : t ∈ T := by
  have h' : φ 1 • t ∈ T := h
  rwa [map_one, one_smul] at h'

/-- **The semilinear denominator-clearing identity.** If a family of sections becomes a
spanning family after applying a semilinear map, with the coefficients cleared of denominators,
then a suitable multiple of the target section differs from a combination of the family by
something the map kills. -/
theorem semilinear_sub_eq_zero {S' M' : Type*} [CommRing S'] [AddCommGroup M'] [Module S' M']
    (ψ : S →+* S') (ρ : M →+ M') (hρ : ∀ (y : S) (z : M), ρ (y • z) = ψ y • ρ z)
    {ι : Type*} [Fintype ι] (s : ι → M) (t : M) (a : ι → S')
    (ha : ∑ i, a i • ρ (s i) = ρ t) (b : S) (c : ι → S)
    (hc : ∀ i, ψ (c i) = ψ b * a i) :
    ρ (b • t - ∑ i, c i • s i) = 0 := by
  rw [map_sub, map_sum, hρ, ← ha, Finset.smul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hρ, hc i, smul_smul]

/-- If `φ d • (b • t - ∑ i, c i • s i) = 0` with `d = g ^ k` and `b = φ g ^ m`, then `g ^ (k + m)`
multiplies `t` into the span of `s`. -/
theorem pow_mem_multiplierIdeal (φ : R →+* S) {ι : Type*} [Fintype ι] (s : ι → M) (t : M)
    {g d : R} {b : S} {c : ι → S} {k m : ℕ} (hd : d = g ^ k) (hb : b = φ g ^ m)
    (h : φ d • (b • t - ∑ i, c i • s i) = 0) :
    g ^ (k + m) ∈ multiplierIdeal φ (Submodule.span S (Set.range s)) t := by
  have h2 : φ d • (b • t) = φ d • ∑ i, c i • s i := by
    rw [← sub_eq_zero, ← smul_sub]
    exact h
  rw [mem_multiplierIdeal_iff]
  have h3 : φ (g ^ (k + m)) • t = φ d • (b • t) := by
    rw [smul_smul, hd, hb, map_pow, map_pow, pow_add]
  rw [h3, h2, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Under the hypotheses of `pow_mem_multiplierIdeal`, `g ^ (k + m + 1)` also multiplies `t` into
the span of `s`. -/
theorem pow_succ_mem_multiplierIdeal (φ : R →+* S) {ι : Type*} [Fintype ι] (s : ι → M) (t : M)
    {g d : R} {b : S} {c : ι → S} {k m : ℕ} (hd : d = g ^ k) (hb : b = φ g ^ m)
    (h : φ d • (b • t - ∑ i, c i • s i) = 0) :
    g ^ (k + m + 1) ∈ multiplierIdeal φ (Submodule.span S (Set.range s)) t := by
  have h' := pow_mem_multiplierIdeal φ s t hd hb h
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ h'

end Algebra

/-! ### The sections over an affine open -/

variable {X : Scheme.{u}}

/-- `N`, a module over the sheaf of rings underlying an algebra sheaf `A`, read as an
`𝒪_X`-module. -/
noncomputable def baseModule (A : AlgebraSheaf X)
    (N : SheafOfModules.{u} (AlgebraSheaf.ringSheaf A)) : X.Modules :=
  (SheafOfModules.restrictScalars.{u} (AlgebraSheaf.structureMap A)).obj N

/-- The `A(U)`-module structure on the sections of `N` over `U`. -/
@[instance_reducible]
noncomputable def moduleSections (A : AlgebraSheaf X)
    (N : SheafOfModules.{u} (AlgebraSheaf.ringSheaf A)) (U : X.Opens) :
    Module ↥(AlgebraSheaf.sections A U) Γ(baseModule A N, U) :=
  inferInstanceAs (Module ↥((AlgebraSheaf.ringSheaf A).obj.obj (op U)) ↥(N.val.obj (op U)))

variable (A : AlgebraSheaf X) (N : SheafOfModules.{u} (AlgebraSheaf.ringSheaf A))

/-- `N` is quasi-coherent as an `𝒪_X`-module. -/
theorem isQuasicoherent_baseModule [A.IsQuasicoherent] [N.IsQuasicoherent] :
    (baseModule A N).IsQuasicoherent :=
  isQuasicoherent_restrictScalars (AlgebraSheaf.structureMap A) ‹A.IsQuasicoherent› N

/-- The `Γ(X, U)`-action on the sections of `N` over `U` is the `A(U)`-action along the
structure map of `A`. -/
theorem base_smul_eq (U : X.Opens) (c : Γ(X, U)) (x : Γ(baseModule A N, U)) :
    letI := moduleSections A N U
    c • x = (A.hom.hom.app (op U)).hom c • x := rfl

/-- Restriction of sections of `N` is semilinear over restriction of sections of `A`. -/
theorem restrictₗ_smul {U V : X.Opens} (h : U ≤ V) (a : ↥(AlgebraSheaf.sections A V))
    (x : Γ(baseModule A N, V)) :
    letI := moduleSections A N U
    letI := moduleSections A N V
    letI := moduleOfLE (baseModule A N) h
    restrictₗ (baseModule A N) h (a • x) =
      (A.right.obj.map (homOfLE h).op).hom a • restrictₗ (baseModule A N) h x :=
  N.val.map_smul (homOfLE h).op a x

/-- **A finite family of sections generating `N` locally over an affine open spans the sections
over that open.** -/
theorem span_eq_top_of_generatesLocally [A.IsQuasicoherent] [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type*} [Fintype ι]
    (s : ι → Γ(baseModule A N, U))
    (hs : Stacks.SheafOfModules.GeneratesLocally (Opens.grothendieckTopology ↥X) N.val s) :
    letI := moduleSections A N U
    Submodule.span ↥(AlgebraSheaf.sections A U) (Set.range s) = ⊤ := by
  classical
  let := moduleSections A N U
  let := AlgebraSheaf.algebraSections A U
  have hqc : (baseModule A N).IsQuasicoherent := isQuasicoherent_baseModule A N
  refine eq_top_iff.mpr fun t _ => ?_
  set J : Ideal Γ(X, U) := multiplierIdeal (A.hom.hom.app (op U)).hom
    (Submodule.span ↥(AlgebraSheaf.sections A U) (Set.range s)) t with hJdef
  have hJ : Ideal.span (J : Set Γ(X, U)) = ⊤ := by
    refine hU.self_le_iSup_basicOpen_iff.mp fun x hx => ?_
    obtain ⟨S, hS, hcov⟩ := hs U (𝟙 U) t
    obtain ⟨V, f, hf, hxV⟩ := hS x hx
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx
    have harrow : S.arrows (homOfLE (X.basicOpen_le g)) :=
      S.downward_closed hf (homOfLE hgV)
    obtain ⟨a, ha⟩ := hcov (X.basicOpen g) (homOfLE (X.basicOpen_le g)) harrow
    let := moduleSections A N (X.basicOpen g)
    let := moduleOfLE (baseModule A N) (X.basicOpen_le g)
    let := AlgebraSheaf.algebraRestrict A (X.basicOpen_le g)
    let := Stacks.FPAlgebraSheaf.isLocalization_away_sections A hU g
    have := isLocalizedModule_restrictₗ (baseModule A N) hU g rfl (X.basicOpen_le g)
    set a' : ι → ↥(AlgebraSheaf.sections A (X.basicOpen g)) := a with ha'def
    have ha2 : ∑ i, a' i • restrictₗ (baseModule A N) (X.basicOpen_le g) (s i) =
        restrictₗ (baseModule A N) (X.basicOpen_le g) t := ha
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (Submonoid.powers ((A.hom.hom.app (op U)).hom g)) a'
    have hb' : ∀ i, ∃ y : ↥(AlgebraSheaf.sections A U),
        (A.right.obj.map (homOfLE (X.basicOpen_le g)).op).hom y
          = (b : ↥(AlgebraSheaf.sections A U)) • a' i :=
      fun i => RingHom.mem_range.mp (hb i)
    choose c hc using hb'
    obtain ⟨m, hm⟩ := b.2
    have hcc : ∀ i, (A.right.obj.map (homOfLE (X.basicOpen_le g)).op).hom (c i)
        = (A.right.obj.map (homOfLE (X.basicOpen_le g)).op).hom
            (b : ↥(AlgebraSheaf.sections A U)) * a' i :=
      fun i => (hc i).trans (Algebra.smul_def _ _)
    have key := semilinear_sub_eq_zero
      (A.right.obj.map (homOfLE (X.basicOpen_le g)).op).hom
      (restrictₗ (baseModule A N) (X.basicOpen_le g)).toAddMonoidHom
      (fun y z => restrictₗ_smul A N (X.basicOpen_le g) y z) s t a' ha2
      (b : ↥(AlgebraSheaf.sections A U)) c hcc
    obtain ⟨d, hd⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g)
      (f := restrictₗ (baseModule A N) (X.basicOpen_le g))
      (key.trans (map_zero (restrictₗ (baseModule A N) (X.basicOpen_le g))).symm)
    obtain ⟨k, hk⟩ := d.2
    have hzero : (A.hom.hom.app (op U)).hom (d : Γ(X, U)) •
        ((b : ↥(AlgebraSheaf.sections A U)) • t - ∑ i, c i • s i) = 0 :=
      hd.trans (smul_zero _)
    refine Opens.mem_iSup.mpr ⟨⟨g ^ (k + m + 1),
      pow_succ_mem_multiplierIdeal (A.hom.hom.app (op U)).hom s t hk.symm hm.symm hzero⟩, ?_⟩
    exact Eq.mp (congrArg (fun W : X.Opens => x ∈ W)
      (X.basicOpen_pow g (Nat.succ_pos (k + m))).symm) hxg
  have hJtop : J = ⊤ := (Ideal.span_eq J).symm.trans hJ
  exact mem_of_one_mem_multiplierIdeal
    (Eq.mp (congrArg (fun I : Ideal Γ(X, U) => (1 : Γ(X, U)) ∈ I) hJtop.symm) Submodule.mem_top)

/-- If a finite family of sections of `N` generates it locally over an affine open `U`, then
`Γ(N, U)` is a finite `A(U)`-module. -/
theorem module_finite_sections_of_generatesLocally [A.IsQuasicoherent] [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type*} [Fintype ι]
    (s : ι → Γ(baseModule A N, U))
    (hs : Stacks.SheafOfModules.GeneratesLocally (Opens.grothendieckTopology ↥X) N.val s) :
    letI := moduleSections A N U
    Module.Finite ↥(AlgebraSheaf.sections A U) Γ(baseModule A N, U) := by
  classical
  let := moduleSections A N U
  refine ⟨⟨Finset.image s Finset.univ, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact span_eq_top_of_generatesLocally A N hU s hs

/-- A quasi-coherent `A`-module of finite type has finite sections over the members of some
affine open cover of `X`. -/
theorem exists_affineCover_module_finite [A.IsQuasicoherent] [N.IsQuasicoherent]
    [N.IsFiniteType] :
    ∃ (κ : Type u) (W : κ → X.Opens), IsOpenCover W ∧ (∀ j, IsAffineOpen (W j)) ∧
      ∀ j, letI := moduleSections A N (W j)
        Module.Finite ↥(AlgebraSheaf.sections A (W j)) Γ(baseModule A N, W j) := by
  classical
  have := Stacks.SheafOfModules.isFiniteTypeSections_of_isFiniteType
    (J := Opens.grothendieckTopology ↥X) N
  obtain ⟨κ₀, W₀, hcov₀, hgen⟩ :=
    Stacks.SheafOfModules.IsFiniteTypeSections.exists_generators
      (J := Opens.grothendieckTopology ↥X) (M := N.val)
  have hcov₀' : IsOpenCover W₀ := (Opens.coversTop_iff _ W₀).mp hcov₀
  refine ⟨_, _, X.isBasis_affineOpens.isOpenCover_mem_and_le hcov₀',
    fun p => p.2.1, fun p => ?_⟩
  obtain ⟨n, s, hs⟩ := hgen p.1.2
  exact module_finite_sections_of_generatesLocally A N p.2.1
    (fun i => N.val.restrictₛₗ (homOfLE p.2.2).op (s i))
    (Stacks.SheafOfModules.generatesLocally_restrict (homOfLE p.2.2) hs)

end Stacks.AlgebraicGeometry.QcohOverAlgebra

end
