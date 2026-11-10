module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteAdjoinField

/-!
# A directed system of finite type algebras over a field exhausting an ind-quasi-finite algebra

Let `R → O` be a ring map such that every element of `O` lies in a finitely generated
`R`-subalgebra quasi-finite over `R`, let `T₀ ⊆ O` be a finite set and `ψ : L → O` a ring map
from a field. Consider the finitely generated `R`-subalgebras `D ⊆ O` quasi-finite over `R` and
containing `T₀`; they form a nonempty directed set, and the subalgebras
`B_D = R[D ∪ ψ(L)] ⊆ O` exhaust `O`, so that `O` is the filtered colimit of the `B_D`.

When `R` is of finite type over a field `K` compatibly with `ψ`, each `B_D` is of finite type over
`L`; when every element of `L` is a root of a polynomial with coefficients in `R[T₀]` whose
leading coefficient lies in `ψ(L ∖ 0)`, the residue fields of `B_D` are algebraic over those of
`R`. This is the system of the proof of [Stacks, Tag 0F0X], where `O` is a strict henselization,
`L` a separable closure of a purely transcendental extension of `K` inside it and `T₀` the
images of the transcendental generators.

## Main definitions

* `AlgebraicGeometry.QFSubalgebras`: the finitely generated quasi-finite `R`-subalgebras of `O`
  containing `T₀`.
* `AlgebraicGeometry.levelAlg`: the subalgebra `R[D ∪ ψ(L)]`.
* `AlgebraicGeometry.levelRingDiagram`, `AlgebraicGeometry.levelRingCocone`: the system of the
  `B_D` and its cocone with apex `O`.

## Main results

* `AlgebraicGeometry.isColimit_levelRingCocone`: `O` is the colimit of the `B_D`.
* `AlgebraicGeometry.finiteType_levelAlg`: each `B_D` is of finite type over `L`.
* `AlgebraicGeometry.isIntegral_residueFieldMap_levelAlg`: the residue field extensions of
  `R → B_D` are integral.

## References

* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry

variable {R O : Type u} [CommRing R] [CommRing O] [Algebra R O] (T₀ : Set O)

/-- The finitely generated `R`-subalgebras of `O` which are quasi-finite over `R` and contain
`T₀`, ordered by inclusion. -/
abbrev QFSubalgebras : Type u :=
  {D : Subalgebra R O // D.FG ∧ Algebra.QuasiFinite R D ∧ T₀ ⊆ D}

/-- Two members of `QFSubalgebras` are contained in their supremum, which is again one. -/
theorem QFSubalgebras.exists_ge (D₁ D₂ : QFSubalgebras (R := R) T₀) :
    ∃ D₃ : QFSubalgebras (R := R) T₀, D₁ ≤ D₃ ∧ D₂ ≤ D₃ := by
  have := D₁.2.2.1
  have := D₂.2.2.1
  exact ⟨⟨D₁.1 ⊔ D₂.1, D₁.2.1.sup D₂.2.1, quasiFinite_sup D₁.1 D₂.1,
    D₁.2.2.2.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩,
    show D₁.1 ≤ D₁.1 ⊔ D₂.1 from le_sup_left,
    show D₂.1 ≤ D₁.1 ⊔ D₂.1 from le_sup_right⟩

/-- `QFSubalgebras T₀` is directed under inclusion. -/
instance QFSubalgebras.isDirectedOrder : IsDirectedOrder (QFSubalgebras (R := R) T₀) :=
  ⟨QFSubalgebras.exists_ge T₀⟩

/-- The subalgebra `⊥` of `O` is quasi-finite over `R`. -/
theorem quasiFinite_bot : Algebra.QuasiFinite R (⊥ : Subalgebra R O) :=
  Algebra.QuasiFinite.of_surjective_algHom (Algebra.ofId R (⊥ : Subalgebra R O))
    (fun x => by
      obtain ⟨r, hr⟩ := Algebra.mem_bot.1 x.2
      exact ⟨r, Subtype.ext hr⟩)

variable {T₀}

/-- If every element of `O` lies in a finitely generated quasi-finite `R`-subalgebra, so does
every finite subset of `O`. -/
theorem exists_qfSubalgebra_of_finite
    (hcov : ∀ o : O, ∃ D : Subalgebra R O, D.FG ∧ Algebra.QuasiFinite R D ∧ o ∈ D)
    {S : Set O} (hS : S.Finite) :
    ∃ D : Subalgebra R O, D.FG ∧ Algebra.QuasiFinite R D ∧ S ⊆ D := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⊥, Subalgebra.fg_bot, quasiFinite_bot, Set.empty_subset _⟩
  | @insert a S _ _ ih =>
    obtain ⟨D₁, hfg₁, hqf₁, hS₁⟩ := ih
    obtain ⟨D₂, hfg₂, hqf₂, ha₂⟩ := hcov a
    refine ⟨D₁ ⊔ D₂, hfg₁.sup hfg₂, quasiFinite_sup D₁ D₂, ?_⟩
    rintro x (rfl | hx)
    · exact (le_sup_right : D₂ ≤ D₁ ⊔ D₂) ha₂
    · exact (le_sup_left : D₁ ≤ D₁ ⊔ D₂) (hS₁ hx)

/-- Every element of `O` lies in a member of `QFSubalgebras T₀`. -/
theorem QFSubalgebras.exists_mem (hT₀ : T₀.Finite)
    (hcov : ∀ o : O, ∃ D : Subalgebra R O, D.FG ∧ Algebra.QuasiFinite R D ∧ o ∈ D) (o : O) :
    ∃ D : QFSubalgebras (R := R) T₀, o ∈ D.1 := by
  obtain ⟨D, hfg, hqf, hD⟩ := exists_qfSubalgebra_of_finite hcov (hT₀.insert o)
  exact ⟨⟨D, hfg, hqf, (Set.subset_insert _ _).trans hD⟩, hD (Set.mem_insert _ _)⟩

/-- `QFSubalgebras T₀` is nonempty. -/
theorem QFSubalgebras.nonempty (hT₀ : T₀.Finite)
    (hcov : ∀ o : O, ∃ D : Subalgebra R O, D.FG ∧ Algebra.QuasiFinite R D ∧ o ∈ D) :
    Nonempty (QFSubalgebras (R := R) T₀) :=
  ⟨(QFSubalgebras.exists_mem hT₀ hcov 0).choose⟩

variable {L : Type u} [Field L] (ψ : L →+* O)

/-- **The level `B_D = R[D ∪ ψ(L)]`.** -/
def levelAlg (D : Subalgebra R O) : Subalgebra R O :=
  Algebra.adjoin R ((D : Set O) ∪ Set.range ψ)

/-- `levelAlg ψ` is monotone in `D`. -/
theorem levelAlg_mono {D₁ D₂ : Subalgebra R O} (h : D₁ ≤ D₂) : levelAlg ψ D₁ ≤ levelAlg ψ D₂ :=
  Algebra.adjoin_mono (Set.union_subset_union_left _ h)

/-- `D` is contained in `levelAlg ψ D`. -/
theorem le_levelAlg (D : Subalgebra R O) : D ≤ levelAlg ψ D :=
  fun _ hx => Algebra.subset_adjoin (Or.inl hx)

/-- The image of `ψ` is contained in `levelAlg ψ D`. -/
theorem range_le_levelAlg (D : Subalgebra R O) (ℓ : L) : ψ ℓ ∈ levelAlg ψ D :=
  Algebra.subset_adjoin (Or.inr ⟨ℓ, rfl⟩)

/-- The inclusion `D → B_D`. -/
def levelAlgIncl (D : Subalgebra R O) : D →ₐ[R] levelAlg ψ D :=
  Subalgebra.inclusion (le_levelAlg ψ D)

/-- The map `L → B_D`. -/
def levelAlgField (D : Subalgebra R O) : L →+* levelAlg ψ D :=
  ψ.codRestrict (levelAlg ψ D).toSubring (range_le_levelAlg ψ D)

/-- `B_D` is generated as a ring by `D` and `L`. -/
theorem closure_levelAlg_eq_top (D : Subalgebra R O) :
    Subring.closure (Set.range (levelAlgIncl ψ D) ∪ Set.range (levelAlgField ψ D)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨b, hb⟩ -
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨ℓ, rfl⟩
    · exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨ℓ, rfl⟩)
  | algebraMap r =>
    exact Subring.subset_closure (Or.inl ⟨algebraMap R D r, rfl⟩)
  | add x y hx hy ihx ihy =>
    exact (Subring.add_mem _ ihx ihy : (⟨x, hx⟩ + ⟨y, hy⟩ : levelAlg ψ D) ∈ _)
  | mul x y hx hy ihx ihy =>
    exact (Subring.mul_mem _ ihx ihy : (⟨x, hx⟩ * ⟨y, hy⟩ : levelAlg ψ D) ∈ _)

/-! ### The colimit -/

/-- The system of the levels `B_D`, the arrows being the inclusions. -/
abbrev levelRingDiagram : QFSubalgebras (R := R) T₀ ⥤ CommRingCat.{u} where
  obj D := CommRingCat.of (levelAlg ψ D.1)
  map h := CommRingCat.ofHom (Subalgebra.inclusion (levelAlg_mono ψ (leOfHom h))).toRingHom

/-- The cocone of the levels with apex `O`. -/
abbrev levelRingCocone : Cocone (levelRingDiagram (R := R) (T₀ := T₀) ψ) where
  pt := CommRingCat.of O
  ι := { app := fun D => CommRingCat.ofHom (levelAlg ψ D.1).val.toRingHom }

/-- **`O` is the filtered colimit of the levels `B_D`.** The forgetful functor to sets reflects
filtered colimits, and on underlying sets the levels form a directed union of subsets exhausting
`O`. -/
def isColimit_levelRingCocone (hT₀ : T₀.Finite)
    (hcov : ∀ o : O, ∃ D : Subalgebra R O, D.FG ∧ Algebra.QuasiFinite R D ∧ o ∈ D) :
    IsColimit (levelRingCocone (R := R) (T₀ := T₀) ψ) := by
  haveI := QFSubalgebras.nonempty hT₀ hcov
  haveI : ReflectsColimitsOfShape (QFSubalgebras (R := R) T₀) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun o => ?_) (fun D₁ D₂ x₁ x₂ h => ?_))
  · obtain ⟨D, hD⟩ := QFSubalgebras.exists_mem hT₀ hcov o
    exact ⟨D, ⟨o, le_levelAlg ψ D.1 hD⟩, rfl⟩
  · obtain ⟨D₃, h₁, h₂⟩ := QFSubalgebras.exists_ge T₀ D₁ D₂
    exact ⟨D₃, homOfLE h₁, homOfLE h₂, Subtype.ext h⟩

/-! ### Finiteness over the field -/

section FiniteType

variable (K : Type u) [Field K] [Algebra K R] [Algebra K L]
  (hK : ∀ k : K, ψ (algebraMap K L k) = algebraMap R O (algebraMap K R k))

/-- A subring pulled back along a ring hom contains the `F`-adjoin of a set if it contains the set
and the image of `F`. -/
private theorem mem_of_mem_adjoin {F S B : Type*} [CommRing F] [CommRing S] [CommRing B]
    [Algebra F S] (f : S →+* B) (A : Subring B) {X : Set S} (hX : ∀ x ∈ X, f x ∈ A)
    (hF : ∀ a : F, f (algebraMap F S a) ∈ A) {x : S} (hx : x ∈ Algebra.adjoin F X) : f x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hX x hx
  | algebraMap a => exact hF a
  | add x y _ _ hx hy => simpa using A.add_mem hx hy
  | mul x y _ _ hx hy => simpa using A.mul_mem hx hy

include hK in
/-- **Each level is of finite type over `L`**, when `R` is of finite type over a field `K`
compatibly with `ψ` and `D` is finitely generated over `R`: `B_D` is generated over `L` by
generators of `D` over `R` and the images of generators of `R` over `K`. -/
theorem finiteType_levelAlg [Algebra.FiniteType K R] (D : Subalgebra R O) (hD : D.FG) :
    letI := (levelAlgField ψ D).toAlgebra
    Algebra.FiniteType L (levelAlg ψ D) := by
  let := (levelAlgField ψ D).toAlgebra
  obtain ⟨s, rfl⟩ := hD
  let D := Algebra.adjoin R (s : Set O)
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra K R).FG)
  classical
  let j := levelAlgIncl ψ D
  let gens : Finset (levelAlg ψ D) :=
    s.attach.image (fun x => j ⟨x.1, Algebra.subset_adjoin x.2⟩) ∪
      t.image (fun r => j (algebraMap R _ r))
  refine ⟨⟨gens, eq_top_iff.2 fun b _ => ?_⟩⟩
  let A := (Algebra.adjoin L (gens : Set (levelAlg ψ D))).toSubring
  have hR : ∀ r : R, j (algebraMap R _ r) ∈ A := fun r =>
    mem_of_mem_adjoin (F := K) (j.toRingHom.comp (algebraMap R _)) A
      (fun x hx => Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hx))))
      (fun k => by
        change j (algebraMap R _ (algebraMap K R k)) ∈ A
        rw [show j (algebraMap R _ (algebraMap K R k)) = algebraMap L _ (algebraMap K L k) from
          Subtype.ext (hK k).symm]
        exact Subalgebra.algebraMap_mem _ _)
      (ht ▸ Algebra.mem_top)
  have hDA : ∀ d, j d ∈ A := fun d =>
    mem_of_mem_adjoin (F := R) j.toRingHom A
      (fun x hx => Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, rfl⟩))))
      hR (Algebra.adjoin_adjoin_coe_preimage (R := R) (s := (s : Set O)) ▸ Algebra.mem_top)
  have hle : Subring.closure (Set.range j ∪ Set.range (levelAlgField ψ D)) ≤ A := by
    rw [Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨ℓ, rfl⟩)
    · exact hDA d
    · exact Subalgebra.algebraMap_mem _ ℓ
  exact hle (closure_levelAlg_eq_top ψ D ▸ Subring.mem_top b)

end FiniteType

/-! ### Residue fields -/

include ψ in
/-- **The residue field extensions of `R → B_D` are integral**, when every element of `L` is a
root of a polynomial whose coefficients lie in `R[T₀]` and whose leading coefficient lies in
`ψ(L ∖ 0)`. This is `AlgebraicGeometry.isIntegral_residueFieldMap_of_closure_eq_top` at
`D → B_D ← L`. -/
theorem isIntegral_residueFieldMap_levelAlg
    (hL : ∀ ℓ : L, ∃ p : O[X], (∀ n, p.coeff n ∈ Algebra.adjoin R T₀) ∧
      (∃ c : L, c ≠ 0 ∧ p.leadingCoeff = ψ c) ∧ p.eval (ψ ℓ) = 0)
    (D : QFSubalgebras (R := R) T₀) (P : Ideal (levelAlg ψ D.1)) [P.IsPrime] :
    (Ideal.ResidueField.map (P.comap (algebraMap R (levelAlg ψ D.1))) P
      (algebraMap R (levelAlg ψ D.1)) rfl).IsIntegral := by
  have := D.2.2.1
  refine isIntegral_residueFieldMap_of_closure_eq_top (levelAlgIncl ψ D.1) (levelAlgField ψ D.1)
    (closure_levelAlg_eq_top ψ D.1) (fun ℓ => ?_) P
  obtain ⟨p, hcoeff, ⟨c, hc0, hc⟩, hp⟩ := hL ℓ
  obtain ⟨p', hp'⟩ : p ∈ Polynomial.lifts (D.1.val : D.1 →ₐ[R] O).toRingHom :=
    (Polynomial.lifts_iff_coeff_lifts p).2 fun n =>
      ⟨⟨p.coeff n, Algebra.adjoin_le D.2.2.2 (hcoeff n)⟩, rfl⟩
  have hinj : Function.Injective (D.1.val : D.1 →ₐ[R] O).toRingHom := Subtype.val_injective
  have hlead : (D.1.val : D.1 →ₐ[R] O) p'.leadingCoeff = ψ c := by
    rw [← hc, ← hp', Polynomial.coe_mapRingHom, Polynomial.leadingCoeff_map_of_injective hinj]
    rfl
  refine ⟨p', ?_, ?_⟩
  · rw [show levelAlgIncl ψ D.1 p'.leadingCoeff = levelAlgField ψ D.1 c from Subtype.ext hlead]
    exact (Units.mk0 c hc0).isUnit.map _
  · apply Subtype.val_injective
    rw [← hp', Polynomial.coe_mapRingHom, Polynomial.eval_map] at hp
    rw [ZeroMemClass.coe_zero, ← hp]
    change ((levelAlg ψ D.1).val : levelAlg ψ D.1 →+* O) _ = _
    rw [Polynomial.hom_eval₂]
    rfl

end AlgebraicGeometry

end
