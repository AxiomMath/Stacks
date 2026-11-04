module

public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSite

/-!
# The annihilator sequence of a principal ideal on the one-point ringed site

Let `A` be a commutative ring and `x, e ∈ A` with `ann(xⁿ) = e A` and `ann(e) = xⁿ A`. On the
one-point ringed site of `A`, with `ℐ = (x)`, this file builds the short exact sequence of
sheaves of modules

`0 → 𝒪/ℐⁿ --e--> 𝒪 --xⁿ--> ℐⁿ → 0`

presenting the annihilator of `xⁿ`, and the maps between two consecutive such sequences when
`x e' = e`.

## Main definitions

* `Stacks.PointRingedSite.annihilatorα`: `𝒪/ℐⁿ ⟶ 𝒪`, multiplication by `e`.
* `Stacks.PointRingedSite.annihilatorβ`: `𝒪 ⟶ ℐⁿ`, multiplication by `xⁿ`.
* `Stacks.PointRingedSite.annihilatorShortComplex`: the sequence.
* `Stacks.PointRingedSite.annihilatorShortComplexMap`: the map from the sequence of `(e', n + 1)`
  to that of `(e, n)` when `x e' = e`.

## Main results

* `Stacks.PointRingedSite.annihilatorShortComplex_shortExact`: the sequence is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.PointRingedSite

universe u

variable {A : Type u} [CommRing A]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- Two maps out of a sheaf of modules on the point agree once they agree on the sections over
the point. -/
theorem hom_ext_pt {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))}
    {f g : M ⟶ N}
    (h : ∀ m : M.val.obj (op (pt A)), f.val.app (op (pt A)) m = g.val.app (op (pt A)) m) :
    f = g :=
  (ev A).map_injective (ModuleCat.hom_ext (LinearMap.ext h))

/-- A section of the unit over the point, read as an element of `A`. -/
abbrev unitToA
    (s : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))).val.obj
      (op (pt A))) :
    A := s

/-- A section of the structure sheaf over the point, read as an element of `A`. -/
abbrev oToA (s : (site A).O.obj.obj (op (pt A))) : A := s

/-- Multiplication by `a` acts on the sections of the unit by multiplication. -/
theorem mulEnd_app_unit_apply (a : A)
    (s : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))).val.obj
      (op (pt A))) :
    unitToA (((mulEnd A a).app (SheafOfModules.unit _)).val.app (op (pt A)) s) =
      a * unitToA s :=
  rfl

/-- Equal endomorphisms of the unit agree on the sections over the point. -/
private theorem app_pt_congr {f g : SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) ⟶ SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))} (h : f = g) (s : A) :
    f.val.app (op (pt A)) s = g.val.app (op (pt A)) s :=
  congrArg (fun φ => φ.val.app (op (pt A)) s) h

variable (x e : A) (n : ℕ)

/-- **Multiplication by `e` on `𝒪/ℐⁿ`**, defined when `e xⁿ = 0`. -/
def annihilatorα (h1 : e * x ^ n = 0) :
    Stacks.Sites.adicQuotientModule (X := site A) (idealX A x) n ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) :=
  cokernel.desc (Stacks.Sites.idealPow (idealX A x) n).ι
    ((mulEnd A e).app (SheafOfModules.unit _)) (by
      refine hom_ext_pt fun s => ?_
      obtain ⟨t, ht⟩ := s
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((mem_idealPow_iff A x n t).1 ht)
      change e * (oToA c * x ^ n) = 0
      rw [mul_left_comm, h1, mul_zero])

/-- The projection `𝒪 ⟶ 𝒪/ℐⁿ` followed by `annihilatorα` is multiplication by `e` on `𝒪`. -/
theorem adicQuotientModuleπ_comp_annihilatorα (h1 : e * x ^ n = 0) :
    Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n ≫ annihilatorα x e n h1 =
      (mulEnd A e).app (SheafOfModules.unit _) :=
  cokernel.π_desc _ _ _

/-- The sections of `ℐⁿ` die in `𝒪/ℐⁿ`, read on the point. -/
theorem adicQuotientModuleπ_app_eq_zero {a : A}
    (ha : a ∈ Ideal.span {toO A x ^ n}) :
    (Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n).val.app (op (pt A)) a = 0 :=
  Stacks.SheafOfModules.val_app_apply_eq_zero _ _
    (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := site A) (idealX A x) n) (op (pt A))
    ⟨a, (mem_idealPow_iff A x n a).2 ha⟩

/-- **Multiplication by `xⁿ`, as a map `𝒪 ⟶ ℐⁿ`.** -/
def annihilatorβ :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) ⟶
      (Stacks.Sites.idealPow (idealX A x) n).toSheafOfModules :=
  Abelian.monoLift (Stacks.Sites.idealPow (idealX A x) n).ι
    ((mulEnd A (x ^ n)).app (SheafOfModules.unit _)) (by
      refine hom_ext_pt fun s => ?_
      exact adicQuotientModuleπ_app_eq_zero x n
        (Ideal.mem_span_singleton'.2 ⟨s, mul_comm _ _⟩))

/-- `annihilatorβ` followed by the inclusion `ℐⁿ ⟶ 𝒪` is multiplication by `xⁿ` on `𝒪`. -/
theorem annihilatorβ_comp_ι :
    annihilatorβ x n ≫ (Stacks.Sites.idealPow (idealX A x) n).ι =
      (mulEnd A (x ^ n)).app (SheafOfModules.unit _) :=
  Abelian.monoLift_comp _ _ _

/-- On the sections over the point, `annihilatorβ` sends `s` to `xⁿ s`. -/
theorem annihilatorβ_app_val (s : A) :
    unitToA ((annihilatorβ x n).val.app (op (pt A)) s).1 = x ^ n * unitToA s :=
  app_pt_congr (annihilatorβ_comp_ι x n) s

/-- The projection `𝒪 ⟶ 𝒪/ℐⁿ` is surjective on the sections over the point. -/
theorem adicQuotientModuleπ_app_surjective :
    Function.Surjective
      ((Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n).val.app (op (pt A))) := by
  have : Epi ((ev A).map (Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n)) :=
    inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

variable (h1 : e * x ^ n = 0)

/-- The composite `𝒪/ℐⁿ ⟶ 𝒪 ⟶ ℐⁿ` vanishes, since `e xⁿ = 0`. -/
theorem annihilatorα_comp_annihilatorβ : annihilatorα x e n h1 ≫ annihilatorβ x n = 0 := by
  rw [← cancel_epi (Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n),
    ← cancel_mono (Stacks.Sites.idealPow (idealX A x) n).ι, comp_zero, zero_comp,
    Category.assoc, Category.assoc, annihilatorβ_comp_ι,
    ← Category.assoc, adicQuotientModuleπ_comp_annihilatorα]
  refine hom_ext_pt fun s => ?_
  change x ^ n * (e * unitToA s) = 0
  rw [mul_left_comm, mul_comm (x ^ n), mul_left_comm, h1, mul_zero]

/-- **The annihilator sequence `0 → 𝒪/ℐⁿ --e--> 𝒪 --xⁿ--> ℐⁿ → 0`.** -/
def annihilatorShortComplex :
    ShortComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))) :=
  ShortComplex.mk (annihilatorα x e n h1) (annihilatorβ x n)
    (annihilatorα_comp_annihilatorβ x e n h1)

/-- **The annihilator sequence is short exact** as soon as `ann(xⁿ) = e A` and `ann(e) = xⁿ A`. -/
theorem annihilatorShortComplex_shortExact
    (h2 : ∀ a : A, x ^ n * a = 0 → ∃ c, a = c * e)
    (h3 : ∀ a : A, e * a = 0 → ∃ c, a = x ^ n * c) :
    (annihilatorShortComplex x e n h1).ShortExact := by
  refine shortExact_of_evaluation A (ShortComplex.ShortExact.mk' ?_ ?_ ?_)
  · rw [ShortComplex.moduleCat_exact_iff]
    intro b hb
    change (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))).val.obj
      (op (pt A)) at b
    have hb' : x ^ n * unitToA b = 0 :=
      (annihilatorβ_app_val x n b).symm.trans (congrArg Subtype.val hb)
    obtain ⟨c, hc⟩ := h2 _ hb'
    refine ⟨(Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) n).val.app
      (op (pt A)) c, ?_⟩
    refine (app_pt_congr (adicQuotientModuleπ_comp_annihilatorα x e n h1) c).trans ?_
    change e * unitToA c = unitToA b
    rw [hc, mul_comm]
  · rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := adicQuotientModuleπ_app_surjective x n y
    have ha : e * unitToA a = 0 := by
      exact (app_pt_congr (adicQuotientModuleπ_comp_annihilatorα x e n h1) a).symm.trans hy
    obtain ⟨c, hc⟩ := h3 _ ha
    exact adicQuotientModuleπ_app_eq_zero x n
      (Ideal.mem_span_singleton'.2 ⟨toO A c, by
        change c * x ^ n = unitToA a
        rw [hc, mul_comm]⟩)
  · rw [ModuleCat.epi_iff_surjective]
    intro t'
    change (Stacks.Sites.idealPow (idealX A x) n).toSheafOfModules.val.obj (op (pt A)) at t'
    obtain ⟨t, ht⟩ := t'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((mem_idealPow_iff A x n (oToA t)).1 ht)
    refine ⟨c, Subtype.ext ((annihilatorβ_app_val x n c).trans ((mul_comm _ _).trans hc))⟩

/-- **The map between consecutive annihilator sequences.** If `x e' = e`, the transition map
`𝒪/ℐⁿ⁺¹ ⟶ 𝒪/ℐⁿ`, multiplication by `x` on `𝒪` and the inclusion `ℐⁿ⁺¹ ⊆ ℐⁿ` form a map from
the sequence of `(e', n + 1)` to that of `(e, n)`. -/
def annihilatorShortComplexMap (e' : A) (h1' : e' * x ^ (n + 1) = 0) (he : x * e' = e) :
    annihilatorShortComplex x e' (n + 1) h1' ⟶ annihilatorShortComplex x e n h1 where
  τ₁ := Stacks.Sites.adicQuotientModuleMap (X := site A) (idealX A x) (Nat.le_succ n)
  τ₂ := (mulEnd A x).app (SheafOfModules.unit _)
  τ₃ := Stacks.SheafOfModules.Submodule.homOfLE
    (Stacks.Sites.idealPow_antitone (idealX A x) (Nat.le_succ n))
  comm₁₂ := by
    change Stacks.Sites.adicQuotientModuleMap (X := site A) (idealX A x) (Nat.le_succ n) ≫
        annihilatorα x e n h1 =
      annihilatorα x e' (n + 1) h1' ≫ (mulEnd A x).app (SheafOfModules.unit _)
    symm
    rw [← cancel_epi (Stacks.Sites.adicQuotientModuleπ (X := site A) (idealX A x) (n + 1)),
      ← Category.assoc, adicQuotientModuleπ_comp_annihilatorα, ← Category.assoc,
      Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap,
      adicQuotientModuleπ_comp_annihilatorα]
    refine hom_ext_pt fun s => ?_
    change x * (e' * unitToA s) = e * unitToA s
    rw [← mul_assoc, he]
  comm₂₃ := by
    change (mulEnd A x).app (SheafOfModules.unit _) ≫ annihilatorβ x n =
      annihilatorβ x (n + 1) ≫ Stacks.SheafOfModules.Submodule.homOfLE
        (Stacks.Sites.idealPow_antitone (idealX A x) (Nat.le_succ n))
    symm
    rw [← cancel_mono (Stacks.Sites.idealPow (idealX A x) n).ι, Category.assoc,
      Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, annihilatorβ_comp_ι, Category.assoc,
      annihilatorβ_comp_ι]
    refine hom_ext_pt fun s => ?_
    change x ^ (n + 1) * unitToA s = x ^ n * (x * unitToA s)
    rw [pow_succ, mul_assoc]

/-- **`𝒪/(x)` is not zero** when `x` is not a unit. -/
theorem not_isZero_adicQuotientModule_one (hx : (1 : A) ∉ Ideal.span {x}) :
    ¬ IsZero (Stacks.Sites.adicQuotientModule (X := site A) (idealX A x) 1) := by
  intro hz
  have hepi : Epi (Stacks.Sites.idealPow (idealX A x) 1).ι :=
    Preadditive.epi_of_isZero_cokernel _ hz
  have : Epi ((ev A).map (Stacks.Sites.idealPow (idealX A x) 1).ι) := inferInstance
  obtain ⟨b', hb1⟩ := (ModuleCat.epi_iff_surjective _).1 this (1 : A)
  have hmem : (1 : (site A).O.obj.obj (op (pt A))) ∈
      (Stacks.Sites.idealPow (idealX A x) 1).obj (op (pt A)) := hb1 ▸ b'.2
  have hb' := (mem_idealPow_iff A x 1 1).1 hmem
  rw [pow_one] at hb'
  exact hx hb'

end Stacks.PointRingedSite
