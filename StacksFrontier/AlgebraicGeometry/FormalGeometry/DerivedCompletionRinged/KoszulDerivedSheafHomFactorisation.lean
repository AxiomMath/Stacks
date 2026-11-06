module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulConstantSystemAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulStupidFiltration
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomLinearSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness

/-!
# After `R𝑆heafHom(Kᵏ, -)`, the Koszul tower factors through `R𝑆heafHom(𝒪, K)`

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, let `Kⁿ` be the
Koszul complex on `f_1^{n+1}, …, f_r^{n+1}` and let `K ∈ D(𝒪)`. [Stacks, Tag 0A0E] presents the
derived completion of `K` as the derived limit of the tower `n ↦ R𝑆heafHom_𝒪(Kⁿ, K)`, whose
transitions are induced by the maps `Kⁿ ⟶ Kᵐ` of the Koszul tower; the augmentation
`Kⁿ ⟶ 𝒪[0]` (the comparison with the extended Čech complex followed by the Čech augmentation)
induces maps `K = R𝑆heafHom_𝒪(𝒪, K) ⟶ R𝑆heafHom_𝒪(Kⁿ, K)`.

This file proves that **after applying `R𝑆heafHom_𝒪(Kᵏ, -)` for a fixed `k`, every transition
`R𝑆heafHom_𝒪(Kᵐ, K) ⟶ R𝑆heafHom_𝒪(Kⁿ, K)` with `m ≥ n + r(k+1)` factors through the map induced
by the augmentation of `Kⁿ`**, with no Noetherian or finiteness hypothesis. This is the
Koszul-index input which, combined with the Artin–Rees pro-isomorphism already in the library,
kills the phantom indeterminacy in part (1) of [Stacks, Tag 0A0K]: the maps out of the derived
limit are determined only up to phantoms, and the factorisation shows that, seen through
`R𝑆heafHom_𝒪(Kᵏ, -)`, the tower is pro-constant with value `R𝑆heafHom_𝒪(𝒪, K)`.

The proof runs the brutal filtration `σ^{≥p}Kᵐ` of the Koszul complexes. Write
`A(C) = R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(C, K))`, contravariant in a complex `C`.

1. A short exact sequence of complexes `C₁ ⟶ C₂ ⟶ C₃` gives a distinguished triangle in `D(𝒪)`,
   which `R𝑆heafHom_𝒪(-, K)` and then `R𝑆heafHom_𝒪(Kᵏ, -)` carry to distinguished triangles
   ([Stacks, Tag 08JC], in both variables). So a map into `A(C₂)` killed by `A(C₁ ⟶ C₂)`
   factors through `A(C₂ ⟶ C₃)`.
2. A compatible family `a` of local sections of `𝒪` acts on `A(C)` through either variable; in
   particular multiplication by `a` on `C` induces on `A(C)` the map induced by multiplication
   by `a` on `Kᵏ`. Multiplication by `f_i^{k+1}` is null-homotopic on `Kᵏ` ([Stacks, Tag 0663]),
   so it induces zero on `A(C)`.
3. On the graded piece `(Kᵐ)ᵖ[-p]` with `p ≥ 1`, the transition to `Kᵐ'` with `m' ≥ m + k + 1`
   multiplies the factor indexed by `S`, `|S| = p`, by `f_S^{m'-m}`, which is divisible by
   `f_i^{k+1}` for any `i ∈ S`. So it induces zero on `A`.
4. A downward induction on `p` along the triangles of `σ^{≥p+1}Kᵐ ⟶ σ^{≥p}Kᵐ ⟶ (Kᵐ)ᵖ[-p]` shows
   that the transition induces zero on `A(σ^{≥p}-)` once `m' ≥ m + (r + 1 - p)(k + 1)`; only
   exactness of the triangles in the middle is used, never the connecting maps.
5. At `p = 1`, the triangle of `σ^{≥1}Kⁿ ⟶ Kⁿ ⟶ 𝒪[0]`, whose second map is exactly the
   augmentation, turns the vanishing into the factorisation.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomIterated`: the functor
  `C ↦ R𝑆heafHom_𝒪(E, R𝑆heafHom_𝒪(C, K))` on cochain complexes.

## Main results

* `AlgebraicGeometry.RingedSite.exists_eq_comp_derivedSheafHomIterated_map_g`: exactness of the
  iterated derived internal Hom at the middle of a short exact sequence of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomIterated_map_smul_id_eq_zero`: a scalar which
  annihilates `E` in `D(𝒪)` induces zero on the iterated derived internal Hom.
* `AlgebraicGeometry.RingedSite.smul_id_Q_obj_koszulPowerComplex_eq_zero`: multiplication by
  `f_i^{k+1}` is zero on the class of the Koszul complex on the `(k+1)`-st powers.
* `AlgebraicGeometry.RingedSite.derivedSheafHomIterated_map_stupidTruncMap_eq_zero`: the
  vanishing on the stupid filtration.
* `AlgebraicGeometry.RingedSite.exists_factor_derivedSheafHomSystem_koszulPowerSystem`: **the
  factorisation**.

## References

* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  HomologicalComplex ComplexShape

namespace AlgebraicGeometry.RingedSite

universe u

-- The priority is the one `LocalCalculationFiniteType.lean` and
-- `KoszulAdicAffineSliceDerivedLimit.lean` use: without it, instance search for the additive
-- structure of the iterated derived internal Hom settles on the wrong morphism universe.
attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] linearCatCenterRingSheaf

section General

variable (X : RingedSite.{u, u, u})

/-- The functor `HomologicalComplex.single` carries multiplication by a compatible family of
local sections of `𝒪` to multiplication by the same family. -/
theorem single_map_globalSectionToEnd_app
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections) (p : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).map
        ((Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.app M) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 ((single (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).obj M) := by
  have key : ∀ {Y Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : Y ≅ Z),
      e.hom ≫ (Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.app Z ≫ e.inv =
        (Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.app Y := fun e => by
    have hnat : e.hom ≫ (Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.app _ =
        (Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.app _ ≫ e.hom :=
      (Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).asHom.naturality e.hom
    rw [← Category.assoc, hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = p
  · subst hn
    rw [single_map_f_self, smul_f_apply, id_f]
    refine (key _).trans ?_
    exact (Category.comp_id _).symm
  · exact (isZero_single_obj_X (up ℤ) p M n hn).eq_of_src _ _

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The iterated derived internal Hom** `C ↦ R𝑆heafHom_𝒪(E, R𝑆heafHom_𝒪(C, K))`, as a functor
on cochain complexes, contravariant in the complex. -/
abbrev derivedSheafHomIterated
    (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  DerivedCategory.Q.op ⋙ (derivedSheafHomBifunctor X).flip.obj K ⋙
    (derivedSheafHomBifunctor X).obj (op E)

/-- The iterated derived internal Hom is additive, both derived internal Homs being additive. -/
instance additive_derivedSheafHomIterated
    (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedSheafHomIterated X E K).Additive :=
  have : (DerivedCategory.Q
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).op.Additive :=
    inferInstance
  have : ((derivedSheafHomBifunctor X).flip.obj K).Additive :=
    additive_derivedSheafHom_flip_obj X K
  have : ((derivedSheafHomBifunctor X).obj (op E)).Additive := additive_derivedSheafHom_obj X E
  inferInstance

/-- **The iterated derived internal Hom is exact in the middle of a short exact sequence.**
A short exact sequence of complexes `C₁ ⟶ C₂ ⟶ C₃` gives a distinguished triangle of `D(𝒪)`,
carried to distinguished triangles by `R𝑆heafHom_𝒪(-, K)` and then by `R𝑆heafHom_𝒪(E, -)`
([Stacks, Tag 08JC]); so a map into the value at `C₂` killed by the map induced by
`C₁ ⟶ C₂` factors through the map induced by `C₂ ⟶ C₃`. -/
theorem exists_eq_comp_derivedSheafHomIterated_map_g
    (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)}
    (hS : S.ShortExact)
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : Z ⟶ (derivedSheafHomIterated X E K).obj (op S.X₂))
    (hφ : φ ≫ (derivedSheafHomIterated X E K).map S.f.op = 0) :
    ∃ ψ : Z ⟶ (derivedSheafHomIterated X E K).obj (op S.X₃),
      φ = ψ ≫ (derivedSheafHomIterated X E K).map S.g.op := by
  obtain ⟨δ, h₁⟩ := exists_distinguished_derivedSheafHom X K _
    (DerivedCategory.triangleOfSES_distinguished hS)
  obtain ⟨δ', h₂⟩ := exists_distinguished_derivedSheafHom_second X E _ h₁
  exact Triangle.coyoneda_exact₂ _ h₂ φ hφ

/-- **A scalar annihilating `E` induces zero on the iterated derived internal Hom.**
Multiplication by a compatible family `a` of local sections on a complex `C` induces on
`R𝑆heafHom_𝒪(E, R𝑆heafHom_𝒪(C, K))` multiplication by `a`, moved first out of the contravariant
variable of the inner Hom, then out of the covariant variable of the outer one; read back into
the contravariant variable of the outer Hom, it is the map induced by multiplication by `a`
on `E`. -/
theorem derivedSheafHomIterated_map_smul_id_eq_zero
    (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections)
    (hE : Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
      𝟙 E = 0)
    (C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedSheafHomIterated X E K).map
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 C).op = 0 := by
  show ((derivedSheafHomBifunctor X).obj (op E)).map
      (((derivedSheafHomBifunctor X).flip.obj K).map (DerivedCategory.Q.map
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 C)).op) = 0
  have hQ : DerivedCategory.Q.map (Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a • 𝟙 C) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (DerivedCategory.Q.obj C) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rw [hQ, Functor.flip_obj_map, derivedSheafHom_map_globalSectionToEnd_source X a _ K]
  erw [derivedSheafHom_map_globalSectionToEnd X a _ _]
  rw [← derivedSheafHom_map_globalSectionToEnd_source X a E _, hE]
  show ((derivedSheafHomBifunctor X).flip.obj _).map (0 : E ⟶ E).op = 0
  rw [op_zero, Functor.map_zero]

end General

section Koszul

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

open CategoryTheory.AlternatingCech

/-- **Multiplication by `f_i^{k+1}` is zero on the class of the Koszul complex on the `(k+1)`-st
powers** in `D(𝒪)`: it is null-homotopic on the complex ([Stacks, Tag 0663]), the Koszul complex
being the constant Koszul system of the multiplications by monomials. -/
theorem smul_id_Q_obj_koszulPowerComplex_eq_zero (i : Fin r) (k : ℕ) :
    Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (koszulFamily X f (singleExp i k)) •
      𝟙 (DerivedCategory.Q.obj (koszulPowerComplex X f k)) = 0 := by
  have h : Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (koszulFamily X f (singleExp i k)) • 𝟙 (koszulPowerComplex X f k) =
      constSmulMap (koszulScalar X f) (koszulScalar_zero X f) (koszulScalar_comp X f) k
        (singleExp i k) := by
    refine HomologicalComplex.hom_ext _ _ fun p => Pi.hom_ext _ _ fun A => ?_
    have e1 : (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (koszulFamily X f (singleExp i k)) • 𝟙 (koszulPowerComplex X f k)).f p =
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (koszulFamily X f (singleExp i k))).asHom.app _ := by
      rw [smul_f_apply, id_f]
      exact Category.comp_id _
    rw [e1]
    exact ((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (koszulFamily X f (singleExp i k))).asHom.naturality _).symm.trans
        (constSmulTerm_comp_pi (koszulScalar X f) (koszulScalar_zero X f)
          (koszulScalar_comp X f) k (singleExp i k) p A).symm
  rw [← CategoryTheory.Functor.map_id, ← Functor.Linear.map_smul, h]
  exact (DerivedCategory.Q_map_eq_of_homotopy (h :=
    constSmulNullHomotopic (koszulScalar X f) (koszulScalar_zero X f)
      (koszulScalar_comp X f) i k)).trans (Functor.map_zero _ _ _)

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Multiplication by a monomial with some exponent at least `k + 1` on `𝒪[-p]` induces zero on
`R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`. -/
theorem derivedSheafHomIterated_map_single_map_koszulScalar_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : ℕ) (p : ℤ) (e : Fin r → ℕ)
    {i : Fin r} (hi : k + 1 ≤ e i) :
    (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).map
        (koszulScalar X f e)).op = 0 := by
  have he : koszulScalar X f e =
      koszulScalar X f (singleExp i k) ≫ koszulScalar X f (e - singleExp i k) := by
    rw [koszulScalar_comp]
    refine koszulScalar_congr X f fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [singleExp, Pi.add_apply, Pi.sub_apply, if_true]
      omega
    · simp [singleExp, hj]
  have h1 : koszulScalar X f (singleExp i k) =
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (koszulFamily X f (singleExp i k))).asHom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    rfl
  rw [he, CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp, h1,
    single_map_globalSectionToEnd_app,
    derivedSheafHomIterated_map_smul_id_eq_zero X _ K _
      (smul_id_Q_obj_koszulPowerComplex_eq_zero X f i k), comp_zero]

/-- On the factor indexed by a subset `S` containing some index, a transition of the Koszul tower
across at least `k + 1` steps, placed in degree `p`, induces zero on
`R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`. -/
theorem derivedSheafHomIterated_map_single_map_koszulPowerTransLE_app_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : ℕ) {m m' : ℕ}
    (h : m + (k + 1) ≤ m') (p : ℤ) {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S) :
    (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).map
        ((koszulPowerTransLE X f ((Nat.le_add_right m (k + 1)).trans h)).app S)).op = 0 :=
  derivedSheafHomIterated_map_single_map_koszulScalar_eq_zero X f K k p _ (i := i)
    (by simp only [koszulPowerTransExp, hi, if_true]; omega)

/-- **The graded vanishing**, on the degree-`p` term of the Koszul complex itself: for
`p ≥ 1` and `m' ≥ m + k + 1`, multiplication by `f_S^{m'-m}` in the factor indexed by every
subset `S` of cardinality `p`, placed in degree `p`, induces zero on
`R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`. Each `S` is non-empty, so `f_S^{m'-m}` is divisible by
`f_i^{k+1}` for any `i ∈ S`. -/
theorem derivedSheafHomIterated_map_single_map_mapX_koszulPowerTransLE_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : ℕ) {m m' : ℕ}
    (h : m + (k + 1) ≤ m') {p : ℤ} (hp : 1 ≤ p) :
    (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).map
        (mapX (koszulPowerTransLE X f ((Nat.le_add_right m (k + 1)).trans h)) p)).op = 0 := by
  have hg : mapX (koszulPowerTransLE X f ((Nat.le_add_right m (k + 1)).trans h)) p =
      ∑ A : Idx r p, Pi.π (fun T : Idx r p => (koszulPowerFunctor X f m).obj T.1) A ≫
        (koszulPowerTransLE X f ((Nat.le_add_right m (k + 1)).trans h)).app A.1 ≫
          termι (koszulPowerFunctor X f m') A := by
    rw [← Category.id_comp (mapX _ p), ← π_comp_termι_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Category.assoc, termι_comp_mapX]
  rw [hg, Functor.map_sum, op_sum, Functor.map_sum]
  refine Finset.sum_eq_zero fun A _ => ?_
  obtain ⟨i, hiA⟩ : A.1.Nonempty := Finset.card_pos.mp (by have := A.2; omega)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, op_comp, op_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    derivedSheafHomIterated_map_single_map_koszulPowerTransLE_app_eq_zero X f K k h p hiA,
    comp_zero, zero_comp]

/-- **The graded vanishing.** For `p ≥ 1` and `m' ≥ m + k + 1`, the map
`(Kᵐ)ᵖ[-p] ⟶ (Kᵐ')ᵖ[-p]` induced by the transition of the Koszul tower induces zero on
`R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`: in the factor indexed by `S`, `|S| = p ≥ 1`, the transition
is multiplication by `f_S^{m'-m}`, which is divisible by `f_i^{k+1}` for any `i ∈ S`. -/
theorem derivedSheafHomIterated_map_single_map_koszulPowerSystem_map_f_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : ℕ) {m m' : ℕ}
    (h : m + (k + 1) ≤ m') {p : ℤ} (hp : 1 ≤ p) :
    (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (up ℤ) p).map
        (((koszulPowerSystem X f).map (homOfLE ((Nat.le_add_right m (k + 1)).trans h))).f p)).op =
      0 := by
  rw [koszulPowerSystem_map_f]
  exact derivedSheafHomIterated_map_single_map_mapX_koszulPowerTransLE_eq_zero X f K k h hp

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The brutal truncations `σ^{≥p}Kᵐ` vanish for `p ≥ r + 1`. -/
theorem isZero_stupidTrunc_koszulPowerComplex (m : ℕ) {p : ℤ} (hp : (r : ℤ) + 1 ≤ p) :
    IsZero ((koszulPowerComplex X f m).stupidTrunc (embeddingUpIntGE p)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  refine IsZero.eq_of_src ?_ _ _
  by_cases hpn : p ≤ n
  · exact (isZero_koszulPowerComplex_X_of_lt X f m (by omega)).of_iso
      (StacksDraft.StupidTruncation.stupidTruncGEXIso _ p n hpn)
  · exact CochainComplex.isZero_of_isStrictlyGE _ p n (by omega)

/-- **The vanishing on the stupid filtration.** For `p ≥ 1` and
`m' ≥ m + j(k + 1)` with `p + j ≥ r + 1`, the transition `Kᵐ ⟶ Kᵐ'`, restricted to the brutal
truncations `σ^{≥p}`, induces zero on `R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`.

By induction on `j`: for `j = 0` the truncation vanishes. For the step, the transition factors
through `Kᵐ⁺ᵏ⁺¹`; by induction its second half vanishes on `σ^{≥p+1}`, so by exactness along
`σ^{≥p+1} ⟶ σ^{≥p} ⟶ (-)ᵖ[-p]` it factors through the graded piece, where the first half
vanishes by the graded vanishing. -/
theorem derivedSheafHomIterated_map_stupidTruncMap_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k j : ℕ) :
    ∀ (p : ℤ), 1 ≤ p → (r : ℤ) + 1 ≤ p + j → ∀ {m m' : ℕ} (h : m + j * (k + 1) ≤ m'),
      (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
        (stupidTruncMap ((koszulPowerSystem X f).map
          (homOfLE ((Nat.le_add_right m (j * (k + 1))).trans h))) (embeddingUpIntGE p)).op = 0 := by
  induction j with
  | zero =>
    intro p _ hpr m m' h
    refine IsZero.eq_of_tgt ?_ _ _
    exact Functor.map_isZero _ (IsZero.op (isZero_stupidTrunc_koszulPowerComplex X f m
      (by omega)))
  | succ j ih =>
    intro p hp hpr m m' h
    have h₁ : m + (k + 1) ≤ m + (k + 1) := le_rfl
    have h₂ : m + (k + 1) + j * (k + 1) ≤ m' := by
      rw [Nat.succ_mul] at h
      omega
    rw [show homOfLE ((Nat.le_add_right m ((j + 1) * (k + 1))).trans h) =
        homOfLE ((Nat.le_add_right m (k + 1)).trans h₁) ≫
          homOfLE ((Nat.le_add_right (m + (k + 1)) (j * (k + 1))).trans h₂) from rfl,
      CategoryTheory.Functor.map_comp, stupidTruncMap_comp, op_comp,
      CategoryTheory.Functor.map_comp]
    have hT₂ : (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
          (stupidTruncMap ((koszulPowerSystem X f).map
            (homOfLE ((Nat.le_add_right (m + (k + 1)) (j * (k + 1))).trans h₂)))
              (embeddingUpIntGE p)).op ≫
        (derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
          (StacksDraft.StupidTruncation.stupidTruncGEMapLE
            ((koszulPowerSystem X f).obj (m + (k + 1))) (show p ≤ p + 1 by omega)).op = 0 := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp,
        ← StacksDraft.StupidTruncation.stupidTruncMap_comp_stupidTruncGEMapLE, op_comp,
        CategoryTheory.Functor.map_comp, ih (p + 1) (by omega) (by omega) h₂, comp_zero]
    obtain ⟨ψ, hψ⟩ := exists_eq_comp_derivedSheafHomIterated_map_g X
      (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K
      (StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact
        ((koszulPowerSystem X f).obj (m + (k + 1))) p) _ hT₂
    rw [hψ]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ψ ≫ ·) ?_).trans comp_zero
    refine ((derivedSheafHomIterated X _ K).map_comp _ _).symm.trans ?_
    show (derivedSheafHomIterated X _ K).map
      (stupidTruncMap ((koszulPowerSystem X f).map
          (homOfLE ((Nat.le_add_right m (k + 1)).trans h₁))) (embeddingUpIntGE p) ≫
        StacksDraft.StupidTruncation.stupidTruncGEπ _ p).op = 0
    rw [StacksDraft.StupidTruncation.stupidTruncMap_comp_stupidTruncGEπ, op_comp,
      CategoryTheory.Functor.map_comp,
      derivedSheafHomIterated_map_single_map_koszulPowerSystem_map_f_eq_zero X f K k h₁ hp,
      zero_comp]

variable [HasWeakSheafify X.J CommRingCat.{u}]

/-- The short complex `σ^{≥1}Kⁿ ⟶ Kⁿ ⟶ 𝒪[0]`, whose second map is the augmentation, is short
exact. -/
theorem shortExact_koszulAugmentationShortComplex (n : ℕ) :
    (koszulAugmentationShortComplex X f n).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun d =>
    (Classical.choice (nonempty_splitting_koszulAugmentationShortComplex X f n d)).shortExact

/-- **After `R𝑆heafHom_𝒪(Kᵏ, -)`, the transitions of the tower `n ↦ R𝑆heafHom_𝒪(Kⁿ, K)` of
[Stacks, Tag 0A0E] factor through `R𝑆heafHom_𝒪(𝒪[0], K)`.** For every `k` and `n` there is
`m ≥ n` — `m = n + r(k + 1)` works — such that, after applying `R𝑆heafHom_𝒪(Kᵏ, -)`, the
transition `R𝑆heafHom_𝒪(Kᵐ, K) ⟶ R𝑆heafHom_𝒪(Kⁿ, K)` factors through the map
`R𝑆heafHom_𝒪(𝒪[0], K) ⟶ R𝑆heafHom_𝒪(Kⁿ, K)` induced by the augmentation `Kⁿ ⟶ 𝒪[0]` (the
comparison with the extended Čech complex followed by the Čech augmentation). No Noetherian or
finiteness hypothesis is needed.

This is the Koszul-index input which, combined with the Artin–Rees pro-isomorphism, kills the
phantom indeterminacy in part (1) of [Stacks, Tag 0A0K]. The transition vanishes on the first
brutal truncation `σ^{≥1}Kⁿ` after `R𝑆heafHom_𝒪(Kᵏ, R𝑆heafHom_𝒪(-, K))`
(`AlgebraicGeometry.RingedSite.derivedSheafHomIterated_map_stupidTruncMap_eq_zero`), and the
triangle of `σ^{≥1}Kⁿ ⟶ Kⁿ ⟶ 𝒪[0]` turns that vanishing into the factorisation. -/
theorem exists_factor_derivedSheafHomSystem_koszulPowerSystem
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k n : ℕ) :
    ∃ (m : ℕ) (h : n ≤ m)
      (t : ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).obj
          ((derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op m)) ⟶
        ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).obj
          (((derivedSheafHomBifunctor X).flip.obj K).obj
            (op (DerivedCategory.Q.obj (structureSheafComplex X))))),
      t ≫ ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).map
          (((derivedSheafHomBifunctor X).flip.obj K).map
            (DerivedCategory.Q.map (koszulCechComplexMap X f n ≫ cechAugmentation X f)).op) =
        ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).map
          ((derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).map
            (homOfLE h).op) := by
  have hnm : n ≤ n + r * (k + 1) := Nat.le_add_right n (r * (k + 1))
  have hvan := derivedSheafHomIterated_map_stupidTruncMap_eq_zero X f K k r 1 le_rfl
    (by omega) (m := n) (m' := n + r * (k + 1)) le_rfl
  have hι := stupidTruncMap_ιStupidTrunc (e := embeddingUpIntGE (1 : ℤ))
    ((koszulPowerSystem X f).map (homOfLE hnm))
  obtain ⟨t, ht⟩ := exists_eq_comp_derivedSheafHomIterated_map_g X
    (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K
    (shortExact_koszulAugmentationShortComplex X f n)
    ((derivedSheafHomIterated X (DerivedCategory.Q.obj (koszulPowerComplex X f k)) K).map
      ((koszulPowerSystem X f).map (homOfLE hnm)).op) (by
      refine ((derivedSheafHomIterated X _ K).map_comp _ _).symm.trans ?_
      show (derivedSheafHomIterated X _ K).map
        (((koszulPowerSystem X f).obj n).ιStupidTrunc (embeddingUpIntGE (1 : ℤ)) ≫
          (koszulPowerSystem X f).map (homOfLE hnm)).op = 0
      rw [← hι, op_comp, CategoryTheory.Functor.map_comp, hvan, comp_zero])
  exact ⟨n + r * (k + 1), hnm, t, ht.symm⟩

end Koszul

end AlgebraicGeometry.RingedSite

end
