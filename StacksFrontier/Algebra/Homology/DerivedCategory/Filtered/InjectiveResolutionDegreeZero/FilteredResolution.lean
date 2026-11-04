module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.TowerComplex
import all StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel
import all StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.InjectiveEmbedding
import all StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.TowerComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered injective resolutions of a filtered object

Over an abelian category with enough injectives, a filtered complex concentrated in degree `0`
with finite filtration — that is, `A[0]` for an object `A` of `Fil^f(𝒜)` — admits a filtered
quasi-isomorphism into a complex of filtered injective objects vanishing in negative degrees.

The resolution is built one degree at a time. The input is that every object of `Fil^f(𝒜)` admits
a strict monomorphism into a filtered injective object
(`CategoryTheory.FilteredObject.exists_mono_isStrict_isFilteredInjective`, [Stacks, Tag 05TS]),
which over an abelian category with enough injectives is obtained by embedding each quotient
`A / F^{c + 1} A` into an injective object and taking the direct sum of finitely many of these;
iterating it on the cokernels produces a complex `I^•` together with a morphism from `A[0]`
(`exists_isFilteredResolution`). That the resulting morphism is a filtered quasi-isomorphism is the
statement that each `gr^p(I^•)` is an injective resolution of `gr^p(A)`, which holds because the
graded pieces of a strict monomorphism with filtered injective target form a short exact sequence
in each degree.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveResolutionDegreeZero

namespace CochainComplex.FilteredInjective.Resolution

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

section Resolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The property that `A ⟶ I^0 ⟶ I^1 ⟶ ⋯`, given by `α` and the `d n`, is a *filtered injective
resolution* of the filtered object `A` of `𝒜`: every `I^n` is a filtered injective object of
`Fil^f(𝒜)`, the composites of consecutive maps vanish, and for every `p` the complex
`gr^p A → gr^p I^0 → gr^p I^1 → ⋯` is exact, i.e. an injective resolution of `gr^p A`. -/
private def IsFilteredResolution (A : FilteredObject 𝒜 ℤᵒᵖ) (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (α : A ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1)) : Prop :=
  (∀ n : ℕ, (I n).IsFilteredInjective) ∧
  (α ≫ d 0).hom = 0 ∧
  (∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) ∧
  (∀ p : ℤ, Mono ((gr p).map α)) ∧
  (∀ (p : ℤ) (h : (gr p).map α ≫ (gr p).map (d 0) = 0),
    (ShortComplex.mk _ _ h).Exact) ∧
  (∀ (n : ℕ) (p : ℤ) (h : (gr p).map (d n) ≫ (gr p).map (d (n + 1)) = 0),
    (ShortComplex.mk _ _ h).Exact)

/-- **Stacks 05TS.** Let `𝒜` be an abelian category with enough injectives. Every object `A` of
`Fil^f(𝒜)` admits a strict monomorphism `u : A ⟶ I` into a filtered injective object `I`: the
underlying morphism of `u` is a monomorphism of `𝒜` and `u` is strict. -/
@[stacks 05TS]
public theorem _root_.CategoryTheory.FilteredObject.exists_mono_isStrict_isFilteredInjective
    [EnoughInjectives 𝒜] (A : FilteredObject 𝒜 ℤᵒᵖ) (hA : A.filtration.IsFinite) :
    ∃ (I : FilteredObject 𝒜 ℤᵒᵖ) (u : A ⟶ I), Mono u.hom ∧ IsStrict u ∧ I.IsFilteredInjective := by
  obtain ⟨a, b, hab, hiso, hzero⟩ := exists_bounds A.filtration hA
  obtain ⟨I, u, hpb, hmono, hIiso, hIzero, hinj⟩ :=
    exists_biprodInjective (b - a).toNat A a b (by omega) hzero
  have hstrict : IsStrictHom u := ⟨fun i => by
    rcases lt_or_ge i.unop (a + 1) with h | h
    · have : IsIso (A.filtration.ι.app i) :=
        Filtration.isIso_ι_app_of_le A.filtration (show i.unop ≤ a by omega) hiso
      exact isPullback_of_isIso_of_mono _ _ _ _ (u.comm i)
    · exact hpb i.unop h⟩
  exact ⟨I, u, hmono, (isStrict_iff_isStrictHom_of_mono u).2 hstrict,
    ⟨.of_exists ⟨a, hIiso⟩ ⟨b + 1, hIzero⟩, hinj⟩⟩

/-- Iterating the embedding of a finitely filtered object into a filtered injective object
(`FilteredObject.exists_mono_isStrict_isFilteredInjective`, i.e. [Stacks, Tag 05TS]) on the
cokernels `Coker(u_n)` produces a filtered injective resolution of `A`: the graded pieces of the
strict short exact sequences `0 → Coker(u_n) → I^{n + 1} → Coker(u_{n + 1}) → 0` are short exact
([Stacks, Tag 0127]), and splicing them gives exactness of `gr^p A → gr^p I^0 → gr^p I^1 → ⋯`. -/
private theorem exists_isFilteredResolution
    (h05TS : ∀ A : FilteredObject 𝒜 ℤᵒᵖ, A.filtration.IsFinite →
      ∃ (I : FilteredObject 𝒜 ℤᵒᵖ) (u : A ⟶ I), Mono u.hom ∧ IsStrict u ∧ I.IsFilteredInjective)
    (A : FilteredObject 𝒜 ℤᵒᵖ) (hA : A.filtration.IsFinite) :
    ∃ (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : A ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1)),
      IsFilteredResolution A I α d := by
  -- Make the choice of an embedding total, so that the source's iteration is a plain recursion on
  -- `ℕ`: for a filtered object whose filtration is infinite the identity is a strict monomorphism
  -- and serves, the conclusion at such an object being unused.
  have htotal : ∀ C : FilteredObject 𝒜 ℤᵒᵖ, ∃ (I : FilteredObject 𝒜 ℤᵒᵖ) (u : C ⟶ I),
      IsStrictHom u ∧ Mono u.hom ∧ (C.filtration.IsFinite → I.IsFilteredInjective) := by
    intro C
    by_cases hC : C.filtration.IsFinite
    · obtain ⟨I, u, h1, h2, h3⟩ := h05TS C hC
      exact ⟨I, u, (isStrict_iff_isStrictHom_of_mono u).1 h2, h1, fun _ => h3⟩
    · exact ⟨C, 𝟙 C, inferInstance, inferInstanceAs (Mono (𝟙 C.X)), fun h => absurd h hC⟩
  choose Iof uof hstrict hmono hfin using htotal
  -- `C n` is the object resolved at stage `n`: `C 0 = A` and `C (n + 1) = Coker(u_n)`.
  let C : ℕ → FilteredObject 𝒜 ℤᵒᵖ := fun n =>
    Nat.rec (motive := fun _ => FilteredObject 𝒜 ℤᵒᵖ) A (fun _ D => cokernelObj (uof D)) n
  have hCfin : ∀ n, (C n).filtration.IsFinite := by
    intro n
    induction n with
    | zero => exact hA
    | succ n ih => exact cokernelObj_filtration_isFinite (uof (C n)) (hfin (C n) ih).isFinite
  refine ⟨fun n => Iof (C n), uof (C 0), fun n => cokernelπ (uof (C n)) ≫ uof (C (n + 1)), ?_⟩
  refine ⟨fun n => hfin (C n) (hCfin n), ?_, ?_,
    fun p => mono_gradedPiece_map (uof (C 0)) p, ?_, ?_⟩
  · show (uof (C 0)).hom ≫ (cokernelπ (uof (C 0))).hom ≫ (uof (C 1)).hom = 0
    rw [← Category.assoc, hom_comp_cokernelπ_hom, zero_comp]
  · intro n
    show ((cokernelπ (uof (C n))).hom ≫ (uof (C (n + 1))).hom) ≫
      ((cokernelπ (uof (C (n + 1)))).hom ≫ (uof (C (n + 1 + 1))).hom) = 0
    rw [Category.assoc, ← Category.assoc (uof (C (n + 1))).hom, hom_comp_cokernelπ_hom, zero_comp,
      comp_zero]
  · intro p _
    have hm : Mono ((gr p).map (uof (C 1))) := mono_gradedPiece_map _ p
    have hz : (gr p).map (uof (C 0)) ≫ (gr p).map (cokernelπ (uof (C 0))) ≫
        (gr p).map (uof (C 1)) = 0 := by
      rw [← Category.assoc, gradedPiece_map_comp_cokernelπ, zero_comp]
    exact exact_of_eq (h := hz) rfl (Functor.map_comp _ _ _).symm
      (exact_comp_mono (h' := hz) (shortExact_gradedPiece_cokernelπ (uof (C 0)) p
        (gradedPiece_map_comp_cokernelπ _ p)).exact)
  · intro n p _
    have he := epi_gradedPiece_map_cokernelπ (uof (C n)) p
    have hm : Mono ((gr p).map (uof (C (n + 1 + 1)))) := mono_gradedPiece_map _ p
    have hz : ((gr p).map (cokernelπ (uof (C n))) ≫
          (gr p).map (uof (C (n + 1)))) ≫
        (gr p).map (cokernelπ (uof (C (n + 1)))) ≫
          (gr p).map (uof (C (n + 1 + 1))) = 0 := by
      rw [Category.assoc, ← Category.assoc ((gr p).map (uof (C (n + 1)))),
        gradedPiece_map_comp_cokernelπ, zero_comp, comp_zero]
    exact exact_of_eq (h := hz) (Functor.map_comp _ _ _).symm (Functor.map_comp _ _ _).symm
      (exact_epi_comp_comp_mono (h' := hz) (shortExact_gradedPiece_cokernelπ (uof (C (n + 1))) p
        (gradedPiece_map_comp_cokernelπ _ p)).exact)

/-- A filtered injective resolution of the degree `0` filtered object of a filtered complex `K^•`
concentrated in degree `0` assembles into a filtered complex `I^•`: the terms form a cochain
complex in degrees `≥ 0`, the filtration steps `F^p I^n` form subcomplexes because the
differentials are morphisms of filtered objects, and `gr^p(I^•)` is the complex of the graded
pieces `gr^p(I^n)`, so the exactness recorded by the resolution is quasi-isomorphy of
`gr^p(K^•) ⟶ gr^p(I^•)`. -/
private theorem exists_filteredQuasiIso_towerFilteredComplex
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) [K.X.IsStrictlyGE 0] [K.X.IsStrictlyLE 0]
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (h : IsFilteredResolution (evalFil K 0) I α d) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) :
    ∃ β : K ⟶ towerFilteredComplex I d hd, CochainComplex.filteredQuasiIso 𝒜 β ∧
      ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj
        (towerFilteredComplex I d hd)).X n) := by
  obtain ⟨hIinj, hαd, -, hmono, hex0, hexn⟩ := id h
  have hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n) := by
    intro n hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact K.X.isZero_of_isStrictlyGE 0 n hlt
    · exact K.X.isZero_of_isStrictlyLE 0 n hgt
  have hKz : ∀ (p n : ℤ), n ≠ 0 → IsZero (((gr p).obj K).X n) := fun p n hn =>
    isZero_gradedPiece_X K p n (isZero_filtration_obj_X K hK (op p) hn)
  refine ⟨towerHom K I α d hd hK hαd, fun p => ?_, fun p n => ?_⟩
  · rw [← quasiIso_iff_comp_right _ (gradedPieceTowerIso I d hd p).hom, quasiIso_iff]
    intro n
    by_cases hn : n = 0
    · subst hn
      have hz3 : IsZero ((gradedPieceTower I d hd p).X (-1)) :=
        isZero_gradedPieceTower_X I d hd p (by decide)
      rw [quasiIsoAt_iff' _ (-1) 0 1
          (ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp))
          (ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel 0 1 by simp)),
        ShortComplex.quasiIso_iff_of_zeros _ ((hKz p (-1) (by decide)).eq_of_src _ _)
          ((hKz p 1 (by decide)).eq_of_tgt _ _)
          (hz3.eq_of_src _ _)]
      have hτ : ((HomologicalComplex.shortComplexFunctor' 𝒜 (ComplexShape.up ℤ) (-1) 0 1).map
            ((gr p).map (towerHom K I α d hd hK hαd) ≫
              (gradedPieceTowerIso I d hd p).hom)).τ₂ =
          (evalGradedPieceIso K p 0).hom ≫ (gr p).map α ≫
            (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).inv :=
        towerHom_gradedPiece_f_zero K I α d hd hK hαd p
      have hg2 : ((HomologicalComplex.shortComplexFunctor' 𝒜 (ComplexShape.up ℤ) (-1) 0 1).obj
            (gradedPieceTower I d hd p)).g =
          (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).hom ≫
            (gr p).map (d 0) ≫
            (gradedPieceTowerXIso I d hd p (k := 0 + 1) (n := 1) rfl).inv :=
        gradedPieceTower_d I d hd p 0 (i := 0) (j := 1) rfl rfl
      refine ⟨ShortComplex.exact_of_iso (ShortComplex.isoMk
        (evalGradedPieceIso K p 0).symm (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).symm
        (gradedPieceTowerXIso I d hd p (k := 0 + 1) (n := 1) rfl).symm ?_ ?_)
        (hex0 p (gradedPiece_map_comp_eq_zero α (d 0) hαd p)), ?_⟩
      · dsimp only [Iso.symm_hom]
        rw [hτ]
        exact inv_comp_hom_comp _ _
      · dsimp only [Iso.symm_hom]
        rw [hg2]
        exact inv_comp_hom_comp _ _
      · have hm : Mono ((gr p).map α) := hmono p
        have h2 : Mono ((gr p).map α ≫
            (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).inv) := mono_comp _ _
        have h3 : Mono ((evalGradedPieceIso K p 0).hom ≫ (gr p).map α ≫
            (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).inv) := mono_comp _ _
        rwa [hτ]
    · refine (quasiIsoAt_iff_exactAt _ n (exactAt_of_isZero_X _ n (hKz p n hn))).mpr ?_
      rcases lt_trichotomy n 0 with hlt | heq | hgt
      · exact exactAt_of_isZero_X _ n (isZero_gradedPieceTower_X I d hd p hlt)
      · exact absurd heq hn
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) + 1 = n := ⟨(n - 1).toNat, by omega⟩
        exact exactAt_gradedPieceTower I d hd p k
          (hexn k p (gradedPiece_map_comp_eq_zero (d k) (d (k + 1)) (hd k) p))
  · rcases lt_or_ge n 0 with hn | hn
    · exact (isZero_gradedPiece_X (towerFilteredComplex I d hd) p n
        (isZero_towerStepComplex_X I d hd p hn)).injective
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact Injective.of_iso
        (((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (k : ℤ)).mapIso
          (gradedPieceTowerIso I d hd p)).trans
          (gradedPieceTowerXIso I d hd p (k := k) rfl)).symm ((hIinj k).injective_gr p)

private theorem exists_filteredQuasiIso_of_isFilteredResolution
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) [K.X.IsStrictlyGE 0] [K.X.IsStrictlyLE 0]
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (h : IsFilteredResolution (evalFil K 0) I α d) :
    ∃ (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (β : K ⟶ J)
      (_ : CochainComplex.filteredQuasiIso 𝒜 β) (_ : J.X.IsStrictlyGE 0)
      (_ : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
            IsZero ((J.filtration.obj (op q)).X n)),
      ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj J).X n) := by
  obtain ⟨hI, -, hdd, -, -, -⟩ := id h
  obtain ⟨β, hβ, hinj⟩ := exists_filteredQuasiIso_towerFilteredComplex K I α d h hdd
  exact ⟨towerFilteredComplex I d hdd, β, hβ, isStrictlyGE_towerFilteredComplex I d hdd,
    exists_isIso_isZero_towerFilteredComplex I d hdd fun n => (hI n).isFinite, hinj⟩

end Resolution

end CochainComplex.FilteredInjective.Resolution

namespace CochainComplex

open FilteredInjective.Resolution in
/-- **Stacks 05TT.** Let `𝒜` be an abelian category with enough injectives and let `K^•` be a
filtered cochain complex of `𝒜` concentrated in degree `0` with finite filtration, i.e. `K^•` is
`A[0]` for an object `A` of `Fil^f(𝒜)`. Then there is a filtered quasi-isomorphism
`α : K^• ⟶ I^•`, that is, one whose graded pieces `gr^p(α)` are all quasi-isomorphisms, where
`I^•` is a complex of filtered injective objects with `I^n = 0` for `n < 0`: every term
`(I^n, F^• I^n)` is a filtered injective object of `Fil^f(𝒜)`. -/
@[stacks 05TT, ega "0 13.6.2" "existence of resolution"]
public theorem exists_filteredQuasiIso_isStrictlyGE_injective_gradedPiece {𝒜 : Type u}
    [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) [K.X.IsStrictlyGE 0] [K.X.IsStrictlyLE 0]
    (hK : K.filtration.IsFinite) :
    ∃ (I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : K ⟶ I)
      (_ : CochainComplex.filteredQuasiIso 𝒜 α) (_ : I.X.IsStrictlyGE 0),
      ∀ n : ℤ, (evalFil I n).IsFilteredInjective := by
  obtain ⟨I, α, d, h⟩ :=
    exists_isFilteredResolution FilteredObject.exists_mono_isStrict_isFilteredInjective
      (evalFil K 0) (isFinite_eval hK 0)
  obtain ⟨J, β, hβ, hJ, hfin, hinj⟩ := exists_filteredQuasiIso_of_isFilteredResolution K I α d h
  exact ⟨J, β, hβ, hJ, fun n => (isFilteredInjective_evalFil_iff J n).2 ⟨hfin n, fun p => hinj p n⟩⟩

end CochainComplex

end FilteredInjectiveResolutionDegreeZero

end
