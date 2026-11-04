module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.Algebra.Homology.TotalComplex

/-!
# The total complex of a double complex concentrated in one row

Let `A` be an additive category with a zero object and let `W` be a cochain complex of objects
of `A`.  Placing `W` in the single second degree `q` produces the double complex
`singleRow W q`, which vanishes outside the row `q` and whose row `q` is `W`.  This module
identifies its total complex: `Tot(singleRow W q)` is the shift `W⟦-q⟧`.

The companion statement for a double complex concentrated in one *column* is
`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit`, and the case `q = 0` of the row
statement is `StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit`.  Neither covers a
general row, which is what the base case of Stacks Tag 06YQ needs: the double complex
`F(Gᵖ, Mᵣ)` attached to a bifunctor and a complex concentrated in the degree `q` is
concentrated in the row `q`.

## Main results

* `StacksDraft.TotalSingleRow.ιTotal_d_up_ℤ'`: the differential of a total complex on one
  summand, with the two target indices given explicitly rather than as `i + 1`.
* `StacksDraft.TotalSingleRow.totalSingleRowUnit`,
  `StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit`: the isomorphism
  `W⟦-q⟧ ≅ Tot(singleRow W q)`.
* `StacksDraft.TotalSingleRow.acyclic_shiftFunctor_obj`: a shift of an acyclic complex is
  acyclic.
* `StacksDraft.TotalSingleRow.acyclic_total_singleRow`: the total complex of a double complex
  concentrated in one row is acyclic as soon as that row is.

## Implementation notes

The identification carries a sign which the column statement does not.  In total degree `n`
the only possibly nonzero summand of `Tot(singleRow W q)` is the one indexed by `(n - q, q)`,
on which the vertical differential vanishes and the horizontal one is `d_W` with *no* sign,
because the sign `(-1)^p` of [Stacks, Tag 012Z] decorates the vertical differential only.  The
differential of `W⟦-q⟧`, on the other hand, is `(-1)^q d_W`.  The two therefore differ by a
sign which is constant in `n`, and it is absorbed by scaling the degree-`n` component of the
comparison map by `(-1)^{qn}`: the required recursion `ε n = (-1)^q ε (n + 1)` is exactly what
that choice satisfies.

Acyclicity of a shift is obtained from `CochainComplex.ShiftSequence.shiftIso`, the natural
isomorphism `(K⟦n⟧).homology a ≅ K.homology a'` for `n + a = a'`.

## References

* [Stacks, Tag 012Z]
* [The Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace StacksDraft.TotalSingleRow

noncomputable section

variable {A : Type*} [Category A] [Preadditive A]

/-- **The differential of a total complex on one summand, with explicit target indices.**  This
is `HomologicalComplex₂.ιTotal_d_up_ℤ` with the three successor indices `p + 1`, `r + 1` and
`n + 1` supplied as separate variables, so that an identity such as `n + -q + 1 = n + 1 + -q`
can be discharged by linear arithmetic instead of forcing a transport along it. -/
lemma ιTotal_d_up_ℤ' (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)] (p p' r r' n n' : ℤ)
    (hp : p + 1 = p') (hr : r + 1 = r') (h : p + r = n) (hn : n + 1 = n') :
    Z.ιTotal (ComplexShape.up ℤ) p r n h ≫ (Z.total (ComplexShape.up ℤ)).d n n' =
      (Z.d p p').f r ≫ Z.ιTotal (ComplexShape.up ℤ) p' r n' (by dsimp; omega) +
        p.negOnePow • ((Z.X p).d r r' ≫
          Z.ιTotal (ComplexShape.up ℤ) p r' n' (by dsimp; omega)) := by
  rw [Z.total_d, Preadditive.comp_add, Z.ι_D₁, Z.ι_D₂,
    Z.d₁_eq (ComplexShape.up ℤ) (i₁ := p) (i₁' := p') hp r n' (by dsimp; omega),
    Z.d₂_eq (ComplexShape.up ℤ) p (i₂ := r) (i₂' := r') hr n' (by dsimp; omega)]
  simp

/-- A scalar multiple of an isomorphism by a unit of `ℤ` is an isomorphism. -/
lemma isIso_units_zsmul {X Y : A} (u : ℤˣ) (f : X ⟶ Y) [IsIso f] : IsIso (u • f) := by
  refine ⟨(u⁻¹ : ℤˣ) • inv f, ?_, ?_⟩ <;>
    simp [Units.smul_def, smul_smul, ← Units.val_mul]

section Naturality

variable {B' D' : Type*} [Category B'] [Category D'] [Preadditive B'] [Preadditive D']
  [HasZeroObject B'] [HasZeroObject D']

/-- **`HomologicalComplex.singleMapHomologicalComplex` is natural in the functor.**  For a
natural transformation `α : Φ ⟶ Ψ` of additive functors, placing an object in the degree `q`
and then applying `α` termwise is the same as applying `α` and then placing the result in the
degree `q`.  Mathlib has the naturality in the object but not this one. -/
lemma singleMapHomologicalComplex_naturality {Φ Ψ : B' ⥤ D'} [Φ.Additive] [Ψ.Additive]
    (α : Φ ⟶ Ψ) (q : ℤ) (M : B') :
    ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) q).app M).hom ≫
        (HomologicalComplex.single D' (ComplexShape.up ℤ) q).map (α.app M) =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single B' (ComplexShape.up ℤ) q).obj M) ≫
        ((HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) q).app
          M).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun r => ?_)
  by_cases hr : r = q
  · obtain rfl := hr.symm
    have hnat := α.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q M).hom
    simp only [HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, NatTrans.mapHomologicalComplex_app_f,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hnat]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q (Ψ.obj M) r
      hr).eq_of_tgt _ _

end Naturality

variable [HasZeroObject A]

/-- The double complex concentrated in the row `r = q`, that row being the complex `W`. -/
noncomputable abbrev singleRow (W : CochainComplex A ℤ) (q : ℤ) :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((HomologicalComplex.single A (ComplexShape.up ℤ) q).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj W

variable (W : CochainComplex A ℤ) (q : ℤ)

/-- Outside the row `q` the double complex concentrated in the row `q` vanishes. -/
lemma isZero_singleRow_X_X (p r : ℤ) (hr : r ≠ q) : IsZero (((singleRow W q).X p).X r) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q (W.X p) r hr

/-- A double complex concentrated in one row has, in each total degree, exactly one possibly
nonzero term. -/
lemma finite_not_isZero_singleRow (n : ℤ) :
    {pr : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pr = n ∧ ¬ IsZero (((singleRow W q).X pr.1).X pr.2)}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton (n + -q, q)) ?_
  rintro ⟨p, r⟩ ⟨hpr, hz⟩
  have hpr' : p + r = n := hpr
  by_cases hr : r = q
  · have hp : p = n + -q := by omega
    simp [hp, hr]
  · exact absurd (isZero_singleRow_X_X W q p r hr) hz

/-- The total complex of a double complex concentrated in one row exists. -/
lemma hasTotal_singleRow [HasFiniteCoproducts A] :
    (singleRow W q).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (finite_not_isZero_singleRow W q)

section HasTotal

variable [(singleRow W q).HasTotal (ComplexShape.up ℤ)]

/-- The projection of `Tot(singleRow W q)^n` onto its only possibly nonzero summand, the one
indexed by `(n - q, q)`, followed by the identification of that summand with `W^{n - q}`. -/
noncomputable def totalSingleRowDesc (n : ℤ) :
    ((singleRow W q).total (ComplexShape.up ℤ)).X n ⟶
      ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-q)).obj W).X n :=
  (singleRow W q).totalDesc (fun p r h =>
    if hr : r = q then
      eqToHom (by
        have h' : p + r = n := h
        obtain rfl := hr.symm
        obtain rfl : p = n + -q := by omega
        rfl) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + -q))).hom
    else (isZero_singleRow_X_X W q p r hr).to_ _)

/-- The inclusion of the summand of `Tot(singleRow W q)^n` indexed by `(n - q, q)`, followed by
`totalSingleRowDesc`, is the identification of that summand with `W^{n - q}`. -/
@[reassoc]
lemma ι_totalSingleRowDesc (n : ℤ) :
    (singleRow W q).ιTotal (ComplexShape.up ℤ) (n + -q) q n (by dsimp; omega) ≫
        totalSingleRowDesc W q n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + -q))).hom := by
  rw [totalSingleRowDesc, HomologicalComplex₂.ι_totalDesc]
  simp

/-- **The total complex of a double complex concentrated in the row `q` is the shift by `-q` of
that row.**  In total degree `n` the only possibly nonzero summand of `Tot(singleRow W q)` is
`W^{n - q}`; by [Stacks, Tag 012Z] its differential is `d_W` with no sign, whereas that of
`W⟦-q⟧` is `(-1)^q d_W`, so the comparison map carries the sign `(-1)^{qn}` in degree `n`.
This is the morphism `W⟦-q⟧ ⟶ Tot(singleRow W q)`; it is an isomorphism. -/
noncomputable def totalSingleRowUnit :
    (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-q)).obj W ⟶
      (singleRow W q).total (ComplexShape.up ℤ) where
  f n := (q * n).negOnePow •
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + -q))).inv ≫
      (singleRow W q).ιTotal (ComplexShape.up ℤ) (n + -q) q n (by dsimp; omega))
  comm' n n' hnn' := by
    obtain rfl : n + 1 = n' := hnn'
    have hd2 : ((singleRow W q).X (n + -q)).d q (q + 1) = 0 :=
      HomologicalComplex.single_obj_d _ _ _ _ _
    have hd1 : ((singleRow W q).d (n + -q) (n + 1 + -q)).f q =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + -q))).hom ≫
          W.d (n + -q) (n + 1 + -q) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
            (W.X (n + 1 + -q))).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    have hqn : -q + q * (n + 1) = q * n := by
      rw [mul_add, mul_one, add_comm (q * n) q, ← add_assoc, neg_add_cancel, zero_add]
    have hsign : (q * n).negOnePow = (-q).negOnePow * (q * (n + 1)).negOnePow := by
      rw [← Int.negOnePow_add, hqn]
    have key : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + -q))).inv ≫
          (singleRow W q).ιTotal (ComplexShape.up ℤ) (n + -q) q n (by dsimp; omega)) ≫
          ((singleRow W q).total (ComplexShape.up ℤ)).d n (n + 1) =
        W.d (n + -q) (n + 1 + -q) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (W.X (n + 1 + -q))).inv ≫
            (singleRow W q).ιTotal (ComplexShape.up ℤ) (n + 1 + -q) q (n + 1)
              (by dsimp; omega) := by
      rw [Category.assoc,
        ιTotal_d_up_ℤ' (singleRow W q) (n + -q) (n + 1 + -q) q (q + 1) n (n + 1)
          (by omega) rfl (by omega) rfl,
        hd1, hd2, zero_comp, smul_zero, add_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Linear.units_smul_comp, key, CochainComplex.shiftFunctor_obj_d',
      Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, ← hsign]

/-- Each component of `totalSingleRowUnit` is an isomorphism: up to its sign it is the inclusion
of the only possibly nonzero summand, whose inverse is `totalSingleRowDesc`. -/
lemma isIso_totalSingleRowUnit_f (n : ℤ) : IsIso ((totalSingleRowUnit W q).f n) := by
  have h : IsIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
      (W.X (n + -q))).inv ≫
      (singleRow W q).ιTotal (ComplexShape.up ℤ) (n + -q) q n (by dsimp; omega)) := by
    refine ⟨totalSingleRowDesc W q n, ?_, ?_⟩
    · rw [Category.assoc, ι_totalSingleRowDesc]
      simp
    · refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p r h => ?_)
      by_cases hr : r = q
      · have h' : p + r = n := h
        obtain rfl := hr.symm
        obtain rfl : p = n + -q := by omega
        rw [Category.comp_id, ← Category.assoc, ι_totalSingleRowDesc, ← Category.assoc,
          Iso.hom_inv_id, Category.id_comp]
      · exact (isZero_singleRow_X_X W q p r hr).eq_of_src _ _
  exact isIso_units_zsmul _ _

/-- The comparison map `totalSingleRowUnit W q : W⟦-q⟧ ⟶ Tot(singleRow W q)` is an
isomorphism, since it is one in each degree. -/
lemma isIso_totalSingleRowUnit : IsIso (totalSingleRowUnit W q) := by
  have := isIso_totalSingleRowUnit_f W q
  exact HomologicalComplex.Hom.isIso_of_components _

end HasTotal

end

section Acyclic

noncomputable section

variable {A : Type*} [Category A] [Abelian A]

/-- **A shift of an acyclic complex is acyclic.**  The homology of `K⟦a⟧` in degree `i` is the
homology of `K` in degree `a + i`, by `CochainComplex.ShiftSequence.shiftIso`. -/
lemma acyclic_shiftFunctor_obj {K : CochainComplex A ℤ} (hK : K.Acyclic) (a : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) a).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hK (a + i)))
    ((CochainComplex.ShiftSequence.shiftIso A a i (a + i) rfl).app K)

/-- **The total complex of a double complex concentrated in one row is acyclic as soon as that
row is.**  It is the shift `W⟦-q⟧` by `totalSingleRowUnit`, and a shift of an acyclic complex
is acyclic. -/
lemma acyclic_total_singleRow (W : CochainComplex A ℤ) (q : ℤ)
    [(singleRow W q).HasTotal (ComplexShape.up ℤ)] (hW : W.Acyclic) :
    ((singleRow W q).total (ComplexShape.up ℤ)).Acyclic := by
  have := isIso_totalSingleRowUnit W q
  intro n
  exact HomologicalComplex.ExactAt.of_iso (acyclic_shiftFunctor_obj hW (-q) n)
    (asIso (totalSingleRowUnit W q))

end

end Acyclic

end StacksDraft.TotalSingleRow

end
