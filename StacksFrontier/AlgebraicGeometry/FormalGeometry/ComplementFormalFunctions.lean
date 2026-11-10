module

public import StacksFrontier.Algebra.Module.AdicCompletionTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsComplete
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.ComplementLongExact
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.PowerSequenceMaps
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections
public import StacksFrontier.Examples.Completion.CompleteModuleCategory

/-!
# Formal functions in degree zero: sections away from a closed set commute with reduction

Let `A` be a Noetherian ring, `f ∈ I`, and `M` a finite `A`-module. Assume `A` is `f`-adically
complete and that `H¹_I(M)` and `H²_I(M)` are annihilated by powers of `f`. Then the sections of
`M̃` on `U = Spec A ∖ V(I)` are the inverse limit of the sections of the sheaves associated to the
quotients `M / fⁿM`.

## Main results

* `Stacks.Algebraization.ComplementTower.sectionsToLimit_isIso` — **Stacks 0EII**: the canonical
  map from the sections of `M̃` on `U` to the inverse limit of the sections of the `(M/fⁿM)̃` is an
  isomorphism.

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.LocalCohomology Stacks.ProZero

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Cohomology of derived sections on the complement, as a single functor -/

variable {A : Type u} [CommRing A] {r : ℕ} (fam : Fin r → A)

/-- The degree-`i` cohomology of derived sections on `U = Spec A ∖ V(I)`, modelled by the cone of
the Čech augmentation of a finite family of generators, as a functor of the module. -/
def complementCohomologyFunctor (i : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  cechComplementFunctor.{u} fam ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

/-- The cohomology of derived sections on `U` is an additive functor of the module. -/
instance complementCohomologyFunctor_additive (i : ℤ) :
    (complementCohomologyFunctor fam i).Additive :=
  inferInstanceAs (cechComplementFunctor.{u} fam ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).Additive

/-- Applying the cohomology of derived sections to a composite. -/
theorem complementCohomologyFunctor_map_comp_apply (i : ℤ) {X Y Z : ModuleCat.{u} A}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : (complementCohomologyFunctor fam i).obj X) :
    (complementCohomologyFunctor fam i).map (a ≫ b) x =
      (complementCohomologyFunctor fam i).map b
        ((complementCohomologyFunctor fam i).map a x) := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The cohomology of derived sections kills the zero map. -/
theorem complementCohomologyFunctor_map_zero_apply (i : ℤ) {X Y : ModuleCat.{u} A}
    (x : (complementCohomologyFunctor fam i).obj X) :
    (complementCohomologyFunctor fam i).map (0 : X ⟶ Y) x = 0 := by
  rw [CategoryTheory.Functor.map_zero]
  rfl

/-- Multiplication by a scalar on the module induces multiplication by that scalar on the
cohomology of derived sections on `U`. -/
theorem complementCohomologyFunctor_map_smul_id_apply (i : ℤ) (N : ModuleCat.{u} A) (a : A)
    (x : (complementCohomologyFunctor fam i).obj N) :
    (complementCohomologyFunctor fam i).map (a • 𝟙 N) x = a • x :=
  homologyComplement_map_smul_id_apply.{u} fam i N a x

/-- A module annihilated by a scalar has all of its derived sections on `U` annihilated by that
scalar. -/
theorem smul_complementCohomologyFunctor_eq_zero (i : ℤ) (N : ModuleCat.{u} A) (a : A)
    (hN : ∀ y : N, a • y = 0) (x : (complementCohomologyFunctor fam i).obj N) : a • x = 0 :=
  smul_homologyComplement_eq_zero.{u} fam i N a hN x

/-- Exactness of the long exact sequence at the middle term. -/
theorem exact_complementCohomologyFunctor_map (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.ShortExact) (i : ℤ) :
    Function.Exact ((complementCohomologyFunctor fam i).map S.f)
      ((complementCohomologyFunctor fam i).map S.g) :=
  exact_homologyComplement_map.{u} fam S hS i

/-- Exactness of the long exact sequence at the third term. -/
theorem exact_complementCohomologyFunctor_δ (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact ((complementCohomologyFunctor fam n₀).map S.g)
      (DerivedCategory.HomologySequence.δ (cechComplementTriangle.{u} fam S hS) n₀ n₁ h) :=
  exact_homologyComplement_δ.{u} fam S hS n₀ n₁ h

/-- Naturality of the connecting map in the short exact sequence. -/
theorem complementCohomologyFunctorδ_naturality {S₁ S₂ : ShortComplex (ModuleCat.{u} A)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (y : (complementCohomologyFunctor fam n₀).obj S₁.X₃) :
    DerivedCategory.HomologySequence.δ (cechComplementTriangle.{u} fam S₂ h₂) n₀ n₁ h
        ((complementCohomologyFunctor fam n₀).map φ.τ₃ y) =
      (complementCohomologyFunctor fam n₁).map φ.τ₁
        (DerivedCategory.HomologySequence.δ (cechComplementTriangle.{u} fam S₁ h₁) n₀ n₁ h y) :=
  cechComplementδ_naturality.{u} fam h₁ h₂ φ n₀ n₁ h y

/-! ### The two pro-zero steps -/

section ProZeroSteps

variable (f : A) (M : ModuleCat.{u} A)

/-- Applying the cohomology of derived sections to a composite equal to a given map. -/
private theorem complementCohomologyFunctor_map_apply_of_comp_eq (i : ℤ) {X Y Z : ModuleCat.{u} A}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c)
    (x : (complementCohomologyFunctor fam i).obj X) :
    (complementCohomologyFunctor fam i).map b ((complementCohomologyFunctor fam i).map a x) =
      (complementCohomologyFunctor fam i).map c x := by
  subst h
  exact (complementCohomologyFunctor_map_comp_apply fam i a b x).symm

/-- Let `p ≤ m` with `f ^ (m - p)` annihilating `M[fᵐ]`. The inclusion `fᵐM ⊆ fᵖM` on cohomology
of derived sections lands in the image of the map induced by `M ⟶ fᵖM`. -/
private theorem exists_map_powerTorsion_g_eq_map_powerSmulTopLE {p m : ℕ} (hpm : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0) (i j : ℤ) (h : i + 1 = j)
    (z : (complementCohomologyFunctor fam i).obj (powerTorsionShortComplex f M m).X₃) :
    ∃ w : (complementCohomologyFunctor fam i).obj (powerTorsionShortComplex f M p).X₂,
      (complementCohomologyFunctor fam i).map (powerTorsionShortComplex f M p).g w =
        (complementCohomologyFunctor fam i).map (powerSmulTopLE f M hpm) z := by
  refine (exact_complementCohomologyFunctor_δ fam (powerTorsionShortComplex f M p)
    (powerTorsionShortComplex_shortExact f M p) i j h _).1 ?_
  refine (complementCohomologyFunctorδ_naturality fam
    (powerTorsionShortComplex_shortExact f M m) (powerTorsionShortComplex_shortExact f M p)
    (powerTorsionSESMap f M hpm hkill) i j h z).trans ?_
  rw [powerTorsionSESMap_τ₁]
  exact complementCohomologyFunctor_map_zero_apply fam j _

/-- Let `p ≤ m` and suppose `f ^ (m - p)` annihilates `M[fᵐ]`. A class in `H⁰(U, M̃)` whose image
in `H⁰(U, (M/fᵐM)̃)` vanishes is `f ^ p` times a class in `H⁰(U, M̃)`. -/
theorem exists_pow_smul_of_complementCohomology_quotient_eq_zero {p m : ℕ} (hpm : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0)
    (s : (complementCohomologyFunctor fam 0).obj M)
    (hs : (complementCohomologyFunctor fam 0).map (powerQuotientShortComplex f M m).g s = 0) :
    ∃ w : (complementCohomologyFunctor fam 0).obj M, s = f ^ p • w := by
  obtain ⟨u, hu⟩ := (exact_complementCohomologyFunctor_map fam (powerQuotientShortComplex f M m)
    (powerQuotientShortComplex_shortExact f M m) 0 s).1 hs
  obtain ⟨w, hw⟩ := exists_map_powerTorsion_g_eq_map_powerSmulTopLE fam f M hpm hkill 0 1
    (by lia) u
  refine ⟨w, ?_⟩
  have key : (complementCohomologyFunctor fam 0).map ((f ^ p) • 𝟙 M) w = s := by
    rw [← powerSmulToSmulTop_comp_subtype f M p]
    refine (complementCohomologyFunctor_map_comp_apply fam 0 _ _ w).trans ?_
    rw [hw]
    exact (complementCohomologyFunctor_map_apply_of_comp_eq fam 0
      (powerSmulTopLE_comp_subtype f M hpm) u).trans hu
  rw [← key, complementCohomologyFunctor_map_smul_id_apply fam 0 M (f ^ p) w]

/-- Let `n ≤ p ≤ m`, suppose `f ^ (m - p)` annihilates `M[fᵐ]`, and suppose `f ^ (p - n)`
annihilates `H¹(U, M̃)`. Then every class in `H⁰(U, (M/fᵐM)̃)` has its image in `H⁰(U, (M/fⁿM)̃)`
in the image of `H⁰(U, M̃)`. -/
theorem exists_complementCohomology_preimage_of_quotient {n p m : ℕ} (hnp : n ≤ p) (hpm : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0)
    (hc : ∀ x : (complementCohomologyFunctor fam 1).obj M, f ^ (p - n) • x = 0)
    (y : (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M m).X₃) :
    ∃ s : (complementCohomologyFunctor fam 0).obj M,
      (complementCohomologyFunctor fam 0).map (powerQuotientShortComplex f M n).g s =
        (complementCohomologyFunctor fam 0).map
          (powerQuotientSESMap f M (hnp.trans hpm)).τ₃ y := by
  obtain ⟨z, hzdef⟩ : ∃ z, DerivedCategory.HomologySequence.δ
      (cechComplementTriangle.{u} fam (powerQuotientShortComplex f M m)
        (powerQuotientShortComplex_shortExact f M m)) 0 1 (by lia) y = z := ⟨_, rfl⟩
  have hnat := complementCohomologyFunctorδ_naturality fam
    (powerQuotientShortComplex_shortExact f M m) (powerQuotientShortComplex_shortExact f M n)
    (powerQuotientSESMap f M (hnp.trans hpm)) 0 1 (by lia) y
  rw [hzdef] at hnat
  obtain ⟨w, hw⟩ := exists_map_powerTorsion_g_eq_map_powerSmulTopLE fam f M hpm hkill 1 2
    (by lia) z
  have hzero : (complementCohomologyFunctor fam 1).map
      (powerSmulTopLE f M (hnp.trans hpm)) z = 0 := by
    rw [← complementCohomologyFunctor_map_apply_of_comp_eq fam 1
      (powerSmulTopLE_trans f M hnp hpm) z, ← hw]
    refine (complementCohomologyFunctor_map_apply_of_comp_eq fam 1
      (powerSmulToSmulTop_comp_powerSmulTopLE f M hnp) w).trans ?_
    refine (complementCohomologyFunctor_map_comp_apply fam 1 ((f ^ (p - n)) • 𝟙 M)
      (powerTorsionShortComplex f M n).g w).trans ?_
    rw [complementCohomologyFunctor_map_smul_id_apply fam 1 M (f ^ (p - n)) w, hc w]
    exact map_zero _
  exact (exact_complementCohomologyFunctor_δ fam (powerQuotientShortComplex f M n)
    (powerQuotientShortComplex_shortExact f M n) 0 1 (by lia)
    ((complementCohomologyFunctor fam 0).map
      (powerQuotientSESMap f M (hnp.trans hpm)).τ₃ y)).1 (hnat.trans hzero)

end ProZeroSteps

/-! ### Transporting a tower along a functor -/

/-- **A levelwise bijective map of towers is a bijection on compatible sequences.** -/
theorem bijective_towerSectionsMap_of_bijective {X Y : ℕ → ModuleCat.{u} A}
    (dx : ∀ n, X (n + 1) ⟶ X n) (dy : ∀ n, Y (n + 1) ⟶ Y n) (ψ : ∀ n, X n ⟶ Y n)
    (hψ : ∀ (n : ℕ) (x : X (n + 1)), dy n (ψ (n + 1) x) = ψ n (dx n x))
    (hbij : ∀ n, Function.Bijective (ψ n)) :
    Function.Bijective (towerSectionsMap dx dy ψ hψ) := by
  refine bijective_towerSectionsMap_of_proZero dx dy ψ hψ ?_ ?_
  · refine fun n ↦ ⟨n, le_rfl, fun x hx ↦ ?_⟩
    rw [towerMapLE_self X dx le_rfl, (hbij n).1 (hx.trans (map_zero _).symm)]
    exact map_zero _
  · refine fun n ↦ ⟨n, le_rfl, fun y ↦ ?_⟩
    rw [towerMapLE_self Y dy le_rfl]
    exact (hbij n).2 y

/-- The composite transition maps of the image of a tower under a functor are the image of the
composite transition maps. -/
theorem towerMapLE_functor (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A)
    (T : ℕ → ModuleCat.{u} A) (t : ∀ n, T (n + 1) ⟶ T n) {n m : ℕ} (h : n ≤ m) :
    towerMapLE (fun k ↦ F.obj (T k)) (fun k ↦ F.map (t k)) h = F.map (towerMapLE T t h) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [towerMapLE_self _ _ le_rfl, towerMapLE_self _ _ le_rfl,
        CategoryTheory.Functor.map_id]
  | succ m hnm ih =>
      rw [← towerMapLE_trans _ _ hnm (Nat.le_succ m), ← towerMapLE_trans T t hnm (Nat.le_succ m),
        CategoryTheory.Functor.map_comp, ih, towerMapLE_succ _ _ m (Nat.le_succ m),
        towerMapLE_succ T t m (Nat.le_succ m)]

end Stacks.Algebraization

namespace Stacks.Algebraization

/-! ### The sections functor and its comparison with degree-zero cohomology -/

/-- Sections on `U = Spec A ∖ V(I)` of the sheaf associated to a module, as a functor. -/
abbrev complementSectionsFunctor (A : Type u) [CommRing A] (I : Ideal A) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙ sectionsOnAffineComplement A I

variable {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}

/-- **The degree-zero cohomology of derived sections on `U` is the sections on `U` of the
associated sheaf.** It is the comparison of the localization triangle data with the global sections
of the restriction to `U`, followed by `Stacks.LocalCohomology.sectionsOnAffineComplementIso`. -/
def complementCohomologyZeroEquivSections (D : LocalizationTriangleData.{u, u} A I hI)
    (N : ModuleCat.{u} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (D.complement.obj N) ≃ₗ[A]
      (complementSectionsFunctor A I).obj N :=
  (D.sectionsIso N).trans
    ((sectionsOnAffineComplementIso I).app (associatedSheaf A N)).toLinearEquiv

/-- The comparison is natural in the module. -/
theorem complementCohomologyZeroEquivSections_naturality
    (D : LocalizationTriangleData.{u, u} A I hI) {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (D.complement.obj M)) :
    complementCohomologyZeroEquivSections D N
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (D.complement.map g) x) =
      (complementSectionsFunctor A I).map g (complementCohomologyZeroEquivSections D M x) := by
  change complementSectionsHom I (associatedSheaf A N)
      (D.sectionsIso N ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (D.complement.map g) x)) = _
  rw [D.sectionsIso_naturality g x]
  exact ConcreteCategory.congr_hom
    (complementSectionsHom_naturality I (AlgebraicGeometry.tilde.map (R := .of A) g))
    (D.sectionsIso M x)

/-! ### The comparison of the two towers of degree-zero cohomology -/

section Tower

variable {r : ℕ} (fam : Fin r → A) (f : A) (M : ModuleCat.{u} A)

/-- `fⁿ` annihilates `M / fⁿM`. -/
theorem pow_smul_powerQuotient_eq_zero (n : ℕ)
    (y : (powerQuotientShortComplex f M n).X₃) : f ^ n • y = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact (Submodule.Quotient.mk_eq_zero _).2 (powerSmul_mem_powerSmulTop f M n x)

/-- `fⁿ` annihilates the degree-zero cohomology of derived sections of `M / fⁿM` on `U`. -/
theorem pow_smul_complementCohomology_powerQuotient_eq_zero (n : ℕ)
    (y : (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃) :
    f ^ n • y = 0 :=
  smul_complementCohomologyFunctor_eq_zero fam 0 _ (f ^ n)
    (pow_smul_powerQuotient_eq_zero f M n) y

/-- Reducing modulo `fⁿ` after reducing modulo `fᵐ` is reducing modulo `fⁿ`. -/
theorem powerQuotient_g_comp_τ₃ {n m : ℕ} (h : n ≤ m) :
    (powerQuotientShortComplex f M m).g ≫ (powerQuotientSESMap f M h).τ₃ =
      (powerQuotientShortComplex f M n).g :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The composite transition maps of the quotient tower are the projections between the
quotients. -/
theorem towerMapLE_powerQuotient {n m : ℕ} (h : n ≤ m) :
    towerMapLE (fun k ↦ (powerQuotientShortComplex f M k).X₃)
        (fun k ↦ (powerQuotientSESMap f M (Nat.le_succ k)).τ₃) h =
      (powerQuotientSESMap f M h).τ₃ :=
  towerMapLE_adicTower (Ideal.span {f}) M h

/-- The map on degree-zero cohomology of derived sections on `U` induced by the reduction
`M ⟶ M / fⁿM`. -/
def complementQuotientMap (n : ℕ) :
    (complementCohomologyFunctor fam 0).obj M ⟶
      (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃ :=
  (complementCohomologyFunctor fam 0).map (powerQuotientShortComplex f M n).g

/-- `complementQuotientMap` is the map on cohomology of the reduction `M ⟶ M / fⁿM`. -/
theorem complementQuotientMap_apply (n : ℕ)
    (s : (complementCohomologyFunctor fam 0).obj M) :
    complementQuotientMap fam f M n s =
      (complementCohomologyFunctor fam 0).map (powerQuotientShortComplex f M n).g s := rfl

/-- `fⁿ H⁰(U, M̃)` is killed by the reduction map, because `fⁿ` annihilates its target. -/
theorem powerSmulTop_le_ker_complementQuotientMap (n : ℕ) :
    (Ideal.span {f}) ^ n • (⊤ : Submodule A ((complementCohomologyFunctor fam 0).obj M)) ≤
      LinearMap.ker (complementQuotientMap fam f M n).hom := by
  refine Submodule.smul_le.2 ?_
  intro a ha x _
  rw [Ideal.span_singleton_pow] at ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [LinearMap.mem_ker, map_smul, mul_comm b (f ^ n), mul_smul]
  exact pow_smul_complementCohomology_powerQuotient_eq_zero fam f M n _

/-- **The level-`n` comparison `H⁰(U, M̃) / fⁿ H⁰(U, M̃) ⟶ H⁰(U, (M/fⁿM)̃)`.** It is induced by the
map on cohomology of the reduction `M ⟶ M / fⁿM`, which kills `fⁿ H⁰(U, M̃)` because `fⁿ`
annihilates its target. -/
def complementQuotientCompare (n : ℕ) :
    adicTower (Ideal.span {f}) ((complementCohomologyFunctor fam 0).obj M) n ⟶
      (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃ :=
  ModuleCat.ofHom (Submodule.liftQ _ (complementQuotientMap fam f M n).hom
    (powerSmulTop_le_ker_complementQuotientMap fam f M n))

/-- The level-`n` comparison sends the class of `s` to the reduction of `s` modulo `fⁿ`. -/
theorem complementQuotientCompare_mk (n : ℕ)
    (s : (complementCohomologyFunctor fam 0).obj M) :
    complementQuotientCompare fam f M n (Submodule.Quotient.mk s) =
      (complementCohomologyFunctor fam 0).map (powerQuotientShortComplex f M n).g s := rfl

/-- The comparison maps commute with the transition maps of the two towers. -/
theorem complementQuotientCompare_comm (n : ℕ)
    (x : adicTower (Ideal.span {f}) ((complementCohomologyFunctor fam 0).obj M) (n + 1)) :
    (complementCohomologyFunctor fam 0).map (powerQuotientSESMap f M (Nat.le_succ n)).τ₃
        (complementQuotientCompare fam f M (n + 1) x) =
      complementQuotientCompare fam f M n
        (adicTowerTransition (Ideal.span {f}) ((complementCohomologyFunctor fam 0).obj M) n x) := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [complementQuotientCompare_mk]
  refine Eq.trans ?_ (complementQuotientCompare_mk fam f M n s).symm
  exact complementCohomologyFunctor_map_apply_of_comp_eq fam 0
    (powerQuotient_g_comp_τ₃ f M (Nat.le_succ n)) s

/-- **The comparison of the two towers is a bijection on compatible sequences**, when `H¹(U, M̃)`
is killed by `f ^ c`. -/
theorem bijective_towerSectionsMap_complementQuotientCompare [IsNoetherian A M] (c : ℕ)
    (hc : ∀ x : (complementCohomologyFunctor fam 1).obj M, f ^ c • x = 0) :
    Function.Bijective (towerSectionsMap
      (adicTowerTransition (Ideal.span {f}) ((complementCohomologyFunctor fam 0).obj M))
      (fun n ↦ (complementCohomologyFunctor fam 0).map
        (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
      (complementQuotientCompare fam f M) (complementQuotientCompare_comm fam f M)) := by
  obtain ⟨Nst, hNst⟩ := exists_powerTorsion_stable f M
  refine bijective_towerSectionsMap_of_proZero _ _ _ _ ?_ ?_
  · intro n
    refine ⟨n + Nst, Nat.le_add_right n Nst, fun x hx ↦ ?_⟩
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := exists_pow_smul_of_complementCohomology_quotient_eq_zero fam f M
      (Nat.le_add_right n Nst)
      (pow_smul_eq_zero_of_powerTorsion_stable f M hNst (by omega) (by omega)) s hx
    rw [towerMapLE_adicTower]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (powerSmul_mem_powerSmulTop f ((complementCohomologyFunctor fam 0).obj M) n w)
  · intro n
    refine ⟨n + c + Nst, by omega, fun y ↦ ?_⟩
    obtain ⟨s, hs⟩ := exists_complementCohomology_preimage_of_quotient fam f M
      (Nat.le_add_right n c) (Nat.le_add_right (n + c) Nst)
      (pow_smul_eq_zero_of_powerTorsion_stable f M hNst (by omega) (by omega))
      (fun x ↦ by rw [Nat.add_sub_cancel_left]; exact hc x) y
    refine ⟨Submodule.Quotient.mk s, ?_⟩
    rw [complementQuotientCompare_mk,
      towerMapLE_functor (complementCohomologyFunctor fam 0)
        (fun k ↦ (powerQuotientShortComplex f M k).X₃)
        (fun k ↦ (powerQuotientSESMap f M (Nat.le_succ k)).τ₃) (by omega : n ≤ n + c + Nst),
      towerMapLE_powerQuotient]
    exact hs

end Tower

end Stacks.Algebraization

/-! ### The statement of Stacks 0EII -/

namespace Stacks.Algebraization.ComplementTower

open Stacks.Algebraization

/-- The open complement `Spec(A) \ V(I)`. -/
def openComplement (A : Type u) [CommRing A] (I : Ideal A) :
    (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The quotient module `M / fⁿM`. -/
def quotientModule (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (M ⧸ ((Ideal.span {f}) ^ n • (⊤ : Submodule A M)))

/-- The canonical map from `M` to `M / fⁿM`. -/
def quotientMap (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) : M ⟶ quotientModule A f M n :=
  ModuleCat.ofHom (Submodule.mkQ _)

/-- The canonical transition map `M / fⁿ⁺¹M → M / fⁿM`. -/
def quotientTransition (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    quotientModule A f M (n + 1) ⟶ quotientModule A f M n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id fun _ hx ↦
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ) hx)

/-- Sections of `(M / fⁿM)̃` on `Spec(A) \ V(I)`, regarded as an `A`-module. -/
def sectionsModPower (A : Type u) [CommRing A] (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  (modulesSpecToSheaf.obj (tilde (quotientModule A f M n))).presheaf.obj
    (.op (openComplement A I))

/-- The transition map on sections induced by `M / fⁿ⁺¹M → M / fⁿM`. -/
def sectionsTransition (A : Type u) [CommRing A] (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    sectionsModPower A I f M (n + 1) ⟶ sectionsModPower A I f M n :=
  ((modulesSpecToSheaf.map
    (tilde.map (R := .of A) (quotientTransition A f M n))).1.app _)

/-- The inverse limit of the modules of sections of `(M / fⁿM)̃`, represented as
compatible sequences. -/
def compatibleSections (A : Type u) [CommRing A] (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A) : Submodule A (∀ n, sectionsModPower A I f M n) where
  carrier x := ∀ n, sectionsTransition A I f M n (x (n + 1)) = x n
  zero_mem' n := by simp
  add_mem' hx hy n := by simp [hx n, hy n]
  smul_mem' a x hx n := by simp [hx n]

/-- Sections of `M̃` on `Spec(A) \ V(I)`, regarded as an `A`-module. -/
def sections (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op (openComplement A I))

/-- The map on sections induced by `M → M / fⁿM`. -/
def sectionQuotientMap (A : Type u) [CommRing A] (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A) (n : ℕ) : sections A I M ⟶ sectionsModPower A I f M n :=
  ((modulesSpecToSheaf.map (tilde.map (R := .of A) (quotientMap A f M n))).1.app _)

/-- The canonical map from sections of `M̃` to the inverse limit of the sections of
`(M / fⁿM)̃`. -/
def sectionsToLimit (A : Type u) [CommRing A] (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A) : sections A I M →ₗ[A] compatibleSections A I f M where
  toFun x := ⟨fun n ↦ sectionQuotientMap A I f M n x, by
    intro n
    change sectionsTransition A I f M n (sectionQuotientMap A I f M (n + 1) x) =
      sectionQuotientMap A I f M n x
    have ht : tilde.map (R := .of A) (quotientMap A f M (n + 1)) ≫
        tilde.map (R := .of A) (quotientTransition A f M n) =
          tilde.map (R := .of A) (quotientMap A f M n) := by
      rw [← tilde.map_comp]
      congr 1
    have hs := congrArg (fun k ↦ modulesSpecToSheaf.map k) ht
    rw [CategoryTheory.Functor.map_comp] at hs
    have ha := congrArg (fun k ↦ k.1.app (.op (openComplement A I))) hs
    exact congrArg (fun k : sections A I M ⟶ sectionsModPower A I f M n ↦ k.hom x) ha⟩
  map_add' x y := by ext n; simp
  map_smul' a x := Subtype.ext <| funext fun n ↦ map_smul (sectionQuotientMap A I f M n).hom a x

/-! ### The proof -/

section Proof

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG) {r : ℕ} (fam : Fin r → A)
  (hfam : Ideal.span (Set.range fam) = I) (f : A) (M : ModuleCat.{u} A)

/-- The transition map of the quotient tower is the projection between the quotients. -/
theorem quotientTransition_eq (n : ℕ) :
    quotientTransition A f M n = (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl)

/-- The transition map on sections is induced by the projection between the quotients. -/
theorem sectionsTransition_eq (n : ℕ) :
    sectionsTransition A I f M n =
      (complementSectionsFunctor A I).map (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ :=
  congrArg (complementSectionsFunctor A I).map (quotientTransition_eq f M n)

/-- **The level-`n` comparison** of the degree-zero cohomology of derived sections of `M / fⁿM`
with the sections of `(M/fⁿM)̃` on `U`. -/
def sectionsCompare (n : ℕ) :
    (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃ ⟶
      sectionsModPower A I f M n :=
  CategoryTheory.ConcreteCategory.ofHom (C := ModuleCat.{u} A)
    (complementCohomologyZeroEquivSections (cechLocalizationTriangleData.{u} fam I hI hfam)
      (quotientModule A f M n)).toLinearMap

/-- `sectionsCompare` is a bijection. -/
theorem sectionsCompare_bijective (n : ℕ) :
    Function.Bijective (sectionsCompare hI fam hfam f M n) :=
  (complementCohomologyZeroEquivSections (cechLocalizationTriangleData.{u} fam I hI hfam)
    (quotientModule A f M n)).bijective

/-- `sectionsCompare` commutes with the transition maps of the two towers. -/
theorem sectionsCompare_comm (n : ℕ)
    (x : (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M (n + 1)).X₃) :
    sectionsTransition A I f M n (sectionsCompare hI fam hfam f M (n + 1) x) =
      sectionsCompare hI fam hfam f M n
        ((complementCohomologyFunctor fam 0).map
          (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ x) := by
  rw [sectionsTransition_eq]
  exact (complementCohomologyZeroEquivSections_naturality
    (cechLocalizationTriangleData.{u} fam I hI hfam)
    (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ x).symm

/-- `sectionsCompare` is a bijection on compatible sequences. -/
theorem bijective_towerSectionsMap_sectionsCompare :
    Function.Bijective (towerSectionsMap
      (X := fun n ↦ (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃)
      (Y := fun n ↦ sectionsModPower A I f M n)
      (fun n ↦ (complementCohomologyFunctor fam 0).map
        (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
      (sectionsTransition A I f M) (sectionsCompare hI fam hfam f M)
      (sectionsCompare_comm hI fam hfam f M)) :=
  bijective_towerSectionsMap_of_bijective
    (X := fun n ↦ (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃)
    (Y := fun n ↦ sectionsModPower A I f M n)
    (fun n ↦ (complementCohomologyFunctor fam 0).map
      (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
    (sectionsTransition A I f M) (sectionsCompare hI fam hfam f M)
    (sectionsCompare_comm hI fam hfam f M) (sectionsCompare_bijective hI fam hfam f M)

include hfam

/-- **The canonical map of Stacks 0EII is a bijection**, for a chosen finite family of generators
of `I`. -/
theorem bijective_sectionsToLimit_of_family [IsNoetherianRing A] [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A] (c₁ c₂ : ℕ)
    (h1 : ∀ x : localCohomologyModule A I hI M 1, f ^ c₁ • x = 0)
    (h2 : ∀ x : localCohomologyModule A I hI M 2, f ^ c₂ • x = 0) :
    Function.Bijective (sectionsToLimit A I f M) := by
  have hAC : IsAdicComplete (Ideal.span {f})
      ((complementCohomologyFunctor fam 0).obj M) :=
    Stacks.Examples.isAdicComplete_of_linearEquiv
      ((cechLocalizationTriangleData.{u} fam I hI hfam).sectionsIso M)
      (isAdicComplete_complementGlobalSections A I hI f M c₁ h1)
  have hinj : Function.Injective (homologyComplementIsoLocalCohomologyModule
      (cechLocalizationTriangleData.{u} fam I hI hfam) M 1 le_rfl).hom.hom := fun _ _ hh ↦
    (ModuleCat.mono_iff_injective _).1 inferInstance hh
  have hc (x : (complementCohomologyFunctor fam 1).obj M) : f ^ c₂ • x = 0 :=
    hinj ((map_smul _ (f ^ c₂) x).trans ((h2 _).trans (map_zero _).symm))
  have hcomposite : ∀ x : (complementCohomologyFunctor fam 0).obj M,
      sectionsToLimit A I f M
          (complementCohomologyZeroEquivSections
            (cechLocalizationTriangleData.{u} fam I hI hfam) M x) =
        towerSectionsMap
          (X := fun n ↦
            (complementCohomologyFunctor fam 0).obj (powerQuotientShortComplex f M n).X₃)
          (Y := fun n ↦ sectionsModPower A I f M n)
          (fun n ↦ (complementCohomologyFunctor fam 0).map
            (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
          (sectionsTransition A I f M) (sectionsCompare hI fam hfam f M)
          (sectionsCompare_comm hI fam hfam f M)
          (towerSectionsMap
            (adicTowerTransition (Ideal.span {f}) ((complementCohomologyFunctor fam 0).obj M))
            (fun n ↦ (complementCohomologyFunctor fam 0).map
              (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
            (complementQuotientCompare fam f M) (complementQuotientCompare_comm fam f M)
            (toAdicTowerSections (Ideal.span {f})
              ((complementCohomologyFunctor fam 0).obj M) x)) := fun x ↦
    Subtype.ext <| funext fun n ↦ (complementCohomologyZeroEquivSections_naturality
      (cechLocalizationTriangleData.{u} fam I hI hfam) (quotientMap A f M n) x).symm
  have hb : Function.Bijective (fun x : (complementCohomologyFunctor fam 0).obj M ↦
      sectionsToLimit A I f M
        (complementCohomologyZeroEquivSections
          (cechLocalizationTriangleData.{u} fam I hI hfam) M x)) := by
    rw [funext hcomposite]
    exact (bijective_towerSectionsMap_sectionsCompare hI fam hfam f M).comp
      ((bijective_towerSectionsMap_complementQuotientCompare fam f M c₂ hc).comp
        (bijective_toAdicTowerSections (Ideal.span {f})
          ((complementCohomologyFunctor fam 0).obj M)))
  exact (Function.Bijective.of_comp_iff (fun y ↦ sectionsToLimit A I f M y)
    (complementCohomologyZeroEquivSections
      (cechLocalizationTriangleData.{u} fam I hI hfam) M).bijective).1 hb

end Proof

/-- **The canonical map of Stacks 0EII is a bijection.** -/
theorem bijective_sectionsToLimit {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (M : ModuleCat.{u} A) [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A]
    (c₁ c₂ : ℕ)
    (h1 : ∀ x : localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M 1, f ^ c₁ • x = 0)
    (h2 : ∀ x : localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M 2, f ^ c₂ • x = 0) :
    Function.Bijective (sectionsToLimit A I f M) := by
  obtain ⟨r, fam, hfam⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Ideal.fg_of_isNoetherianRing I)
  exact bijective_sectionsToLimit_of_family (Ideal.fg_of_isNoetherianRing I) fam hfam f M
    c₁ c₂ h1 h2

/-- **Stacks 0EII.** For a finite module over a Noetherian ring complete at `(f)`,
if its first two local cohomology modules are killed by powers of `f`, then sections
away from `V(I)` commute with reduction modulo all powers of `f`. -/
theorem sectionsToLimit_isIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (f : A) (hf : f ∈ I) (M : ModuleCat.{u} A)
    [Module.Finite A M] (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (h1 : ∃ n, ∀ x : localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M 1,
      f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M 2,
      f ^ n • x = 0) :
    IsIso (ModuleCat.ofHom (sectionsToLimit A I f M)) := by
  -- The membership `f ∈ I` is not consumed: the argument uses only the completeness of `A` and
  -- the two annihilation hypotheses, so the conclusion holds for every `f`.
  have : f ∈ I := hf
  have := hcomplete
  obtain ⟨c₁, h1'⟩ := h1
  obtain ⟨c₂, h2'⟩ := h2
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
    (bijective_sectionsToLimit I f M c₁ c₂ h1' h2')

end Stacks.Algebraization.ComplementTower
