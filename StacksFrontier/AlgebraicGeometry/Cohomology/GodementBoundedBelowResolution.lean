module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.ComplexOfFunctorsLift
public import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
public import StacksFrontier.Topology.Sheaves.Flasque.Biproducts
import StacksCore.Tactic.StacksAttribute

/-!
# The Godement resolution of a bounded below complex of modules

Let `(X, 𝒪_X)` be a ringed space and let `F^•` be a bounded below complex of `𝒪_X`-modules.
Applying the Godement complex `G` of [Stacks, Tag 0FKS] to every term of `F` produces a double
complex

```
A^{p, q} = G^p(F^q)
```

(`godementDoubleComplex`), zero for `p < 0` and, `F` being bounded below, with finite diagonals.
Its total complex is the **Godement resolution of the complex `F`**: the augmentation
`F^q ⟶ G^0(F^q)` induces a quasi-isomorphism `F^• ⟶ Tot(A)`, every term of `Tot(A)` is flasque, and
`Tot(A)` is bounded below in the same degree as `F`.

## Main results

* `godementDoubleComplex`, `godementRowAugmentation`: the double complex and the augmentation of
  `F` into its row `p = 0`.
* `hypotheses_godementRowAugmentation`: the hypotheses of [Stacks, Tag 0133] hold for that
  augmentation.
* `isFlasque_total_godementDoubleComplex`: every term of the total complex is flasque.

## References

* [Stacks Project, Tag 0FKT](https://stacks.math.columbia.edu/tag/0FKT)
* [Stacks Project, Tag 0FKS](https://stacks.math.columbia.edu/tag/0FKS)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomologicalComplex

universe u

namespace AlgebraicGeometry.GodementResolution

open RingedSpaceModuleAdjunction

variable (X : RingedSpace.{u, u})

/-! ### The Godement complex preserves zero morphisms -/

/-- Every iterate of an additive endofunctor is additive. -/
private lemma additive_iterate {C : Type*} [Category C] [Preadditive C] (T : C ⥤ C) [T.Additive] :
    ∀ n : ℕ, (T.iterate n).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | n + 1 => by
    have := additive_iterate T n
    exact inferInstanceAs (T.iterate n ⋙ T).Additive

/-- **The Godement complex preserves zero morphisms.** -/
instance preservesZeroMorphisms_godementComplex :
    (godementComplex X).PreservesZeroMorphisms := by
  refine HomologicalComplex.preservesZeroMorphisms_of_eval_iso _
    (fun n => (modulePullback (fromDiscrete X) ⋙
      modulePushforward (fromDiscrete X)).iterate (n + 1))
    (godementComplexEvalIso X) (fun n => ?_)
  have := additive_iterate
    (modulePullback (fromDiscrete X) ⋙ modulePushforward (fromDiscrete X)) (n + 1)
  infer_instance

/-! ### The Godement double complex of a complex -/

variable (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- **The rows of the Godement double complex**: the complex, indexed by the Godement degree,
whose term in degree `p` is the complex `q ↦ G^p(F^q)`. -/
noncomputable abbrev godementRows :
    CochainComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) ℕ :=
  HomologicalComplex.liftFunctorToComplex (godementComplex X)
    (fun _ => inferInstance) F

/-- **The Godement double complex of a complex** `A^{p, q} = G^p(F^q)`, with the Godement degree
`p` extended from `ℕ` to `ℤ` by zero. -/
noncomputable abbrev godementDoubleComplex :
    HomologicalComplex₂ (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) :=
  HomologicalComplex.liftFunctorToComplexExtend (godementComplex X)
    (fun _ => inferInstance) F

/-- The augmentation of `F` into the row `p = 0` of `godementRows`: in degree `q` it is the
degree-`0` component of the Godement augmentation of `F^q`. -/
noncomputable def godementRowZeroAugmentation : F ⟶ (godementRows X F).X 0 where
  f q := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.X q)).inv ≫
    ((godementAugmentation X).app (F.X q)).f 0
  comm' q q' _ := by
    have h := congrArg (fun φ => φ.f 0) ((godementAugmentation X).naturality (F.d q q'))
    change (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℕ) 0).map (F.d q q')) ≫
        (godementAugmentation X).app (F.X q')).f 0 = _ at h
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self] at h
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            (F.X q)).inv ≫ g) h.symm).trans
        ((congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              (F.X q)).inv ≫ g) (Category.assoc _ _ _)).trans
          ((Iso.inv_hom_id_assoc _ _).trans (Category.assoc _ _ _))))

/-- **The augmentation of `F` into the row `p = 0` of the Godement double complex.** -/
noncomputable def godementRowAugmentation :
    F ⟶ rowZero (godementDoubleComplex X F).flip :=
  godementRowZeroAugmentation X F ≫
    ((godementRows X F).extendXIso ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl).inv

/-- **The augmentation of `F^p` into the `p`-th column of the Godement double complex**: the
Godement augmentation of the module `F^p`, extended from `ℕ` to `ℤ`. -/
noncomputable def godementColumnAugmentation (p : ℤ) :
    (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ) 0).obj (F.X p) ⟶ (godementDoubleComplex X F).flip.X p :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (F.X p) 0 0 rfl).inv ≫
    HomologicalComplex.extendMap ((godementAugmentation X).app (F.X p))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.liftFunctorToComplexExtendFlipXIso (godementComplex X)
      (fun _ => inferInstance) F p).inv

/-- **The columns of the Godement double complex are flasque resolutions**: the column
augmentation is a quasi-isomorphism, by clause (3) of [Stacks, Tag 0FKS]. -/
theorem quasiIso_godementColumnAugmentation (p : ℤ) :
    QuasiIso (godementColumnAugmentation X F p) := by
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((godementAugmentation X).app (F.X p)) ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((godementAugmentation X).app (F.X p))
      ComplexShape.embeddingUpNat).2 (quasiIso_godementAugmentation X (F.X p))
  dsimp only [godementColumnAugmentation]
  infer_instance

/-- The column of the Godement double complex vanishes in degree `-1`. -/
theorem isZero_godementDoubleComplex_flip_X_X_neg_one (p : ℤ) :
    IsZero (((godementDoubleComplex X F).flip.X p).X (-1)) := by
  have hneg : IsZero ((((godementComplex X).obj (F.X p)).extend
      ComplexShape.embeddingUpNat).X (-1)) :=
    ((godementComplex X).obj (F.X p)).isZero_extend_X ComplexShape.embeddingUpNat (-1)
      (by intro n hn; change ((n : ℕ) : ℤ) = -1 at hn; omega)
  exact hneg.of_iso ((HomologicalComplex.eval (SheafOfModules.{u} (structureSheafRing X))
    (ComplexShape.up ℤ) (-1)).mapIso
      (HomologicalComplex.liftFunctorToComplexExtendFlipXIso (godementComplex X)
        (fun _ => inferInstance) F p))

/-- The two cancellations that identify the row augmentation with the column augmentation in degree
`0`, stated for abstract morphisms. -/
private lemma cancel_extendXIso_bridge {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (u : A₀ ⟶ A₁) (s : A₁ ⟶ A₂) (eS : A₃ ≅ A₂) (a : A₂ ⟶ A₄) (eG : A₅ ≅ A₄) (r : A₄ ⟶ A₆) :
    u ≫ ((s ≫ a) ≫ r) =
      (u ≫ s ≫ eS.inv) ≫ ((eS.hom ≫ a ≫ eG.inv) ≫ (eG.hom ≫ r)) := by
  simp

/-- **The row augmentation and the column augmentations agree in degree `0`.** -/
theorem godementRowAugmentation_f (p : ℤ) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.X p)).hom ≫
        (godementRowAugmentation X F).f p =
      (godementColumnAugmentation X F p).f 0 := by
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have hL : (godementRowAugmentation X F).f p =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.X p)).inv ≫
          ((godementAugmentation X).app (F.X p)).f 0) ≫
        ((godementRows X F).extendXIso ComplexShape.embeddingUpNat h0).inv.f p :=
    HomologicalComplex.comp_f _ _ p
  have hR0 : (godementColumnAugmentation X F p).f 0 =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (F.X p) 0 0 h0).inv.f 0 ≫
        ((HomologicalComplex.extendMap ((godementAugmentation X).app (F.X p))
              ComplexShape.embeddingUpNat).f 0 ≫
          (HomologicalComplex.liftFunctorToComplexExtendFlipXIso (godementComplex X)
            (fun _ => inferInstance) F p).inv.f 0) :=
    (HomologicalComplex.comp_f _ _ 0).trans
      (congrArg (fun g =>
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          (F.X p) 0 0 h0).inv.f 0 ≫ g) (HomologicalComplex.comp_f _ _ 0))
  have hR := hR0.trans (congrArg₂ (fun a b => a ≫ b)
    (HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat (F.X p) 0 0 h0)
    (congrArg₂ (fun a b => a ≫ b)
      (HomologicalComplex.extendMap_f ((godementAugmentation X).app (F.X p))
        ComplexShape.embeddingUpNat h0)
      (HomologicalComplex.liftFunctorToComplexExtendFlipXIso_inv_f_zero
        (godementComplex X) (fun _ => inferInstance) F p)))
  exact (congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (F.X p)).hom ≫ g) hL).trans
      ((cancel_extendXIso_bridge _ _ _ _ _ _).trans hR.symm)

/-- **The hypotheses of [Stacks, Tag 0133] for the Godement double complex of a bounded below
complex**: the diagonals are finite, the complex vanishes in the negative Godement degrees, each
column is exact away from degree `0`, and the augmentation identifies `F^p` with the kernel of
the first differential of the `p`-th column. -/
theorem hypotheses_godementRowAugmentation (a : ℤ) [F.IsStrictlyGE a] :
    Hypotheses F (godementDoubleComplex X F).flip (godementRowAugmentation X F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    show {p : ℤ | ¬ IsZero (((godementDoubleComplex X F).X (n - p)).X p)}.Finite
    refine ((HomologicalComplex.diagonalFinite_liftFunctorToComplexExtend (godementComplex X)
      (fun _ => inferInstance) F a n).image
        (fun p : ℤ => n - p)).subset ?_
    intro p hp
    refine ⟨n - p, ?_, ?_⟩
    · show ¬ IsZero (((godementDoubleComplex X F).X (n - p)).X (n - (n - p)))
      rw [show n - (n - p) = p by omega]
      exact hp
    · show n - (n - p) = p
      omega
  · intro p q hq
    exact HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X_of_neg
      (godementComplex X) (fun _ => inferInstance) F q p hq
  · intro p q hq
    exact (HomologicalComplex.exactAt_and_isIso_kernelLift_of_quasiIso_single (F.X p)
      ((godementDoubleComplex X F).flip.X p) (godementColumnAugmentation X F p)
      (quasiIso_godementColumnAugmentation X F p)
      (isZero_godementDoubleComplex_flip_X_X_neg_one X F p)).1 q hq
  · intro p
    obtain ⟨hβ, hiso⟩ :=
      (HomologicalComplex.exactAt_and_isIso_kernelLift_of_quasiIso_single (F.X p)
        ((godementDoubleComplex X F).flip.X p) (godementColumnAugmentation X F p)
        (quasiIso_godementColumnAugmentation X F p)
        (isZero_godementDoubleComplex_flip_X_X_neg_one X F p)).2
    set u := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.X p) with hu
    have hβ' : (godementRowAugmentation X F).f p ≫
        ((godementDoubleComplex X F).flip.X p).d 0 1 = 0 := by
      apply (cancel_epi u.hom).1
      calc
        u.hom ≫ ((godementRowAugmentation X F).f p ≫
            ((godementDoubleComplex X F).flip.X p).d 0 1) =
            (godementColumnAugmentation X F p).f 0 ≫
              ((godementDoubleComplex X F).flip.X p).d 0 1 := by
          rw [← Category.assoc, godementRowAugmentation_f]
        _ = 0 := hβ
        _ = u.hom ≫ 0 := by simp
    refine ⟨hβ', ?_⟩
    have heq : u.hom ≫ kernel.lift (((godementDoubleComplex X F).flip.X p).d 0 1)
          ((godementRowAugmentation X F).f p) hβ' =
        kernel.lift (((godementDoubleComplex X F).flip.X p).d 0 1)
          ((godementColumnAugmentation X F p).f 0) hβ := by
      apply (cancel_mono (kernel.ι (((godementDoubleComplex X F).flip.X p).d 0 1))).mp
      simp only [Category.assoc, kernel.lift_ι]
      exact godementRowAugmentation_f X F p
    have hcomp : IsIso (u.hom ≫ kernel.lift
        (((godementDoubleComplex X F).flip.X p).d 0 1)
        ((godementRowAugmentation X F).f p) hβ') := by
      rw [heq]
      exact hiso
    exact IsIso.of_isIso_comp_left u.hom _

/-! ### The terms of the total complex are flasque -/

/-- **A coproduct of flasque sheaves with finitely many nonzero terms is flasque.** -/
private lemma isFlasque_cofan_pt {Y : TopCat.{u}} {J : Type*}
    (A : J → TopCat.Sheaf AddCommGrpCat.{u} Y) (c : Cofan A) (hc : IsColimit c)
    (S : Set J) [Finite S] (hS : ∀ j, j ∉ S → IsZero (A j))
    (hA : ∀ j, (A j).IsFlasque) : c.pt.IsFlasque := by
  have : HasFiniteBiproducts (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let hcS := StacksDraft.TotalComplexQuasiIso.isColimitRestrictCofan c hc S hS
  let B := ⨁ fun j : S => A (j : J)
  let e : c.pt ≅ B := hcS.coconePointUniqueUpToIso (biproduct.isColimit _)
  have hB : B.IsFlasque := by
    simpa [B] using TopCat.Sheaf.isFlasque_biproduct (Y := Y) (I := ↥S)
      (fun j : S => A (j : J)) (fun j => hA j.1)
  exact TopCat.Sheaf.IsFlasque.of_iso e hB

/-- A diagonal of a double complex that vanishes for `p < 0` and for `q < a` is finite. -/
private lemma finite_diagonal_of_vanishing (Q : ℤ × ℤ → Prop) (a n : ℤ)
    (hp : ∀ p q, p < 0 → ¬ Q (p, q)) (hq : ∀ p q, q < a → ¬ Q (p, q)) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        pq = n ∧ Q pq}.Finite := by
  refine (Set.finite_Icc 0 (n - a)).image (fun p => (p, n - p)) |>.subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hQ⟩
  have hpq' : p + q = n := hpq
  have hp0 : 0 ≤ p := by
    by_contra hneg
    exact hp p q (by omega) hQ
  have hqa : a ≤ q := by
    by_contra hneg
    exact hq p q (by omega) hQ
  refine ⟨p, ⟨hp0, by omega⟩, ?_⟩
  show (p, n - p) = (p, q)
  exact Prod.ext rfl (by omega)

/-- **Every term of the total complex of the Godement double complex is flasque.** -/
theorem isFlasque_total_godementDoubleComplex (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (structureSheafRing X)).obj
      (((godementDoubleComplex X F).total (ComplexShape.up ℤ)).X n)) := by
  classical
  let O := structureSheafRing X
  let Z := (godementDoubleComplex X F).toGradedObject
  let Dg : Set (ℤ × ℤ) := {pq | ComplexShape.π (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n}
  let S : Set ↥Dg := {i | ¬ IsZero (((godementDoubleComplex X F).X i.1.1).X i.1.2)}
  have hdiag := finite_diagonal_of_vanishing
    (fun pq => ¬ IsZero (((godementDoubleComplex X F).X pq.1).X pq.2)) a n
    (fun p q hp h => h (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X_of_neg
      (godementComplex X) (fun _ => inferInstance) F p q hp))
    (fun p q hq h => h (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X
      (godementComplex X) (fun _ => inferInstance) F a p q hq))
  have hfin : S.Finite := by
    let e : ↥S → ↥{pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n ∧
          ¬ IsZero (((godementDoubleComplex X F).X pq.1).X pq.2)} :=
      fun i => ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
    have he : Function.Injective e := by
      intro i j hij
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hij))
    have : Finite ↥{pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n ∧
          ¬ IsZero (((godementDoubleComplex X F).X pq.1).X pq.2)} := hdiag.to_subtype
    exact Finite.of_injective e he
  have : Finite ↥S := hfin.to_subtype
  let c := Z.cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)) n
  let hc := Z.isColimitCofanMapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n
  let cS := StacksDraft.TotalComplexQuasiIso.restrictCofan c S
  let hcS := StacksDraft.TotalComplexQuasiIso.isColimitRestrictCofan c hc S
    (fun i hi => by
      by_contra h
      exact hi h)
  let A : S → TopCat.Sheaf AddCommGrpCat.{u} X := fun i =>
    (SheafOfModules.toSheaf O).obj (Z i.1.1)
  have : Fintype ↥S := Fintype.ofFinite ↥S
  have : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf O) := inferInstance
  have : Limits.PreservesColimitsOfShape (Discrete S) (SheafOfModules.toSheaf O) :=
    inferInstance
  have hcS' : IsColimit ((SheafOfModules.toSheaf O).mapCocone cS) :=
    (inferInstance : Limits.PreservesColimitsOfShape (Discrete S)
      (SheafOfModules.toSheaf O)).preservesColimit.preserves hcS |>.some
  have hA : ∀ i, (A i).IsFlasque := by
    intro i
    have hp0 : 0 ≤ i.1.1.1 := by
      by_contra hneg
      exact i.2 (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X_of_neg
        (godementComplex X) (fun _ => inferInstance) F
        i.1.1.1 i.1.1.2 (by omega))
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = i.1.1.1 :=
      ⟨i.1.1.1.toNat, Int.toNat_of_nonneg hp0⟩
    have hterm : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf O).obj
        (((godementRows X F).X k).X i.1.1.2)) := by
      rw [HomologicalComplex.liftFunctorToComplex_X_X]
      exact isFlasque_godementComplex X (F.X i.1.1.2) k
    refine TopCat.Sheaf.IsFlasque.of_iso ((SheafOfModules.toSheaf O).mapIso
      ((HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) i.1.1.2).mapIso
        ((godementRows X F).extendXIso ComplexShape.embeddingUpNat hk))) hterm
  let cA : Cofan A := Cofan.mk ((SheafOfModules.toSheaf O).obj cS.pt)
    (fun i => (SheafOfModules.toSheaf O).map (cS.inj i))
  have hcA : IsColimit cA :=
    (Cofan.isColimitMapCoconeEquiv (SheafOfModules.toSheaf O)
      (fun i : S => Z i.1.1) cS).toFun hcS'
  have hfl' : TopCat.Sheaf.IsFlasque cA.pt :=
    isFlasque_cofan_pt A cA hcA Set.univ (by intro i hi; simp at hi) hA
  exact hfl'

/-- **The diagonals of `godementDoubleComplex X F` are finite.** -/
theorem finite_diagonal_godementDoubleComplex (a : ℤ) [F.IsStrictlyGE a] (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        pq = n ∧
      ¬ IsZero (((godementDoubleComplex X F).X pq.1).X pq.2)}.Finite :=
  finite_diagonal_of_vanishing _ a n
    (fun p q hp h => h (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X_of_neg
      (godementComplex X) (fun _ => inferInstance) F p q hp))
    (fun p q hq h => h (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X
      (godementComplex X) (fun _ => inferInstance) F a p q hq))

/-! ### The comparison map, as data -/

/-- **The comparison map of [Stacks, Tag 0133], for the Godement double complex of `F`.** The
hypotheses verified by `hypotheses_godementRowAugmentation` are the `q`-variant ones -- the
augmentation lands in the row `p = 0` of the *flip* -- so the "as data" comparison `comparisonMapP`
is formed for `(godementDoubleComplex X F).flip` and then carried across the column/row flip by
`totalFlipIso`. -/
noncomputable def godementComparisonMap (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] :
    F ⟶ (godementDoubleComplex X F).total (ComplexShape.up ℤ) :=
  comparisonMapP F (godementDoubleComplex X F).flip (godementRowAugmentation X F)
      (hypotheses_godementRowAugmentation X F a) ≫
    ((godementDoubleComplex X F).totalFlipIso (ComplexShape.up ℤ)).hom

/-- The component of `godementComparisonMap` in degree `n`: the row augmentation followed by the
inclusion of the summand `A^{0,n}` of `Tot^n`. -/
lemma godementComparisonMap_f (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    (godementComparisonMap X F a).f n =
      (godementRowAugmentation X F).f n ≫
        (godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) := by
  show (comparisonMapP F (godementDoubleComplex X F).flip
        (godementRowAugmentation X F) (hypotheses_godementRowAugmentation X F a)).f n ≫
      ((godementDoubleComplex X F).totalFlipIso (ComplexShape.up ℤ)).hom.f n = _
  rw [comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp [ComplexShape.σ]

/-- **The comparison map is a quasi-isomorphism.** -/
instance quasiIso_godementComparisonMap (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (godementComparisonMap X F a) := by
  obtain ⟨_, f, hf, hq⟩ := quasiIso_total_of_resolution_flip
    F (godementDoubleComplex X F) (godementRowAugmentation X F)
    (hypotheses_godementRowAugmentation X F a)
  have hfeq : f = godementComparisonMap X F a :=
    HomologicalComplex.hom_ext _ _ fun n => (hf n).trans (godementComparisonMap_f X F a n).symm
  rw [hfeq] at hq
  exact hq

/-- **Three of the four conclusions of [Stacks, Tag 0FKT] for the Godement resolution.** The
comparison map `godementComparisonMap` is a quasi-isomorphism from `F` onto a complex that is
bounded below in the same degree as `F` and whose every term is flasque. -/
theorem exists_quasiIso_isStrictlyGE_isFlasque_godement (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (godementComparisonMap X F a) ∧
      CochainComplex.IsStrictlyGE ((godementDoubleComplex X F).total (ComplexShape.up ℤ)) a ∧
      ∀ i : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (structureSheafRing X)).obj
        (((godementDoubleComplex X F).total (ComplexShape.up ℤ)).X i)) :=
  ⟨inferInstance, isStrictlyGE_total_liftFunctorToComplexExtend (godementComplex X)
      (fun _ => inferInstance) F a,
    fun i => isFlasque_total_godementDoubleComplex X F a i⟩

/-! ### Clause (4) of [Stacks, Tag 0FKT]: the stalkwise homotopy equivalence

For every `x ∈ X`, the stalk at `x` of `godementComparisonMap X F a`, a map of complexes of
`𝒪_{X,x}`-modules from `F_x` to the stalk of the total complex, is a homotopy equivalence. -/

section StalkHomotopyEquivalence

variable (x : X)

/-- The functor sending a sheaf of modules to the complex, concentrated in degree `0`, of its
stalk at `x`. -/
noncomputable abbrev stalkSingleFunctor :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      CochainComplex (GodementResolution.StalkModuleCat X x) ℕ :=
  CochainComplex.single₀ (SheafOfModules.{u} (structureSheafRing X)) ⋙
    (SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The functor sending a sheaf of modules to its Godement complex, taken stalkwise at `x`. -/
noncomputable abbrev stalkGodementFunctor :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      CochainComplex (GodementResolution.StalkModuleCat X x) ℕ :=
  godementComplex X ⋙
    (SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The stalk functor, applied termwise to complexes of sheaves of modules indexed by `ℤ`. -/
noncomputable abbrev stalkComplexFunctor :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ ⥤
      CochainComplex (GodementResolution.StalkModuleCat X x) ℤ :=
  (SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Evaluating `stalkSingleFunctor` in any degree preserves zero morphisms. -/
theorem preservesZeroMorphisms_stalkSingleFunctor_eval (n : ℕ) :
    (stalkSingleFunctor X x ⋙ HomologicalComplex.eval
      (GodementResolution.StalkModuleCat X x) (ComplexShape.up ℕ) n).PreservesZeroMorphisms :=
  HomologicalComplex.preservesZeroMorphisms_single_mapHomologicalComplex_eval
    (ComplexShape.up ℕ) 0 (SheafOfModules.stalkFunctor (structureSheafRing X) x) n

/-- Evaluating `stalkGodementFunctor` in any degree preserves zero morphisms. -/
theorem preservesZeroMorphisms_stalkGodementFunctor_eval (n : ℕ) :
    (stalkGodementFunctor X x ⋙ HomologicalComplex.eval
      (GodementResolution.StalkModuleCat X x) (ComplexShape.up ℕ) n).PreservesZeroMorphisms :=
  HomologicalComplex.preservesZeroMorphisms_mapHomologicalComplex_comp_eval
    (godementComplex X) n (SheafOfModules.stalkFunctor (structureSheafRing X) x)

/-! #### The data of clause (5) of [Stacks, Tag 0FKS]

The five components of the iterated existential `hasNaturalStalkHomotopy_godementAugmentation X x`.
-/

/-- The complex of functors homotopy equivalent to the stalk functor placed in degree `0`. -/
noncomputable def stalkHtpyH :
    CochainComplex
      (SheafOfModules.{u} (structureSheafRing X) ⥤ GodementResolution.StalkModuleCat X x) ℕ :=
  (hasNaturalStalkHomotopy_godementAugmentation X x).choose

/-- The complex of functors concentrated at the stalk functor in degree `0`, as the source of
`stalkHtpyE`. -/
noncomputable abbrev stalkSingleComplexOfFunctors :
    CochainComplex
      (SheafOfModules.{u} (structureSheafRing X) ⥤ GodementResolution.StalkModuleCat X x) ℕ :=
  (HomologicalComplex.single
      (SheafOfModules.{u} (structureSheafRing X) ⥤ GodementResolution.StalkModuleCat X x)
      (ComplexShape.up ℕ) 0).obj (SheafOfModules.stalkFunctor (structureSheafRing X) x)

/-- The homotopy equivalence from the stalk functor in degree `0` to `stalkHtpyH`. -/
noncomputable def stalkHtpyE :
    HomotopyEquiv (stalkSingleComplexOfFunctors X x) (stalkHtpyH X x) :=
  (hasNaturalStalkHomotopy_godementAugmentation X x).choose_spec.choose

/-- The identification of `stalkHtpyH.asFunctor` with the stalkwise Godement complex. -/
noncomputable def stalkHtpyI : (stalkHtpyH X x).asFunctor ≅ stalkGodementFunctor X x :=
  (hasNaturalStalkHomotopy_godementAugmentation X x).choose_spec.choose_spec.choose

/-- The identification of the `asFunctor` of the degree-`0` complex of functors with the stalk
functor placed in degree `0`. -/
noncomputable def stalkHtpyJ :
    (stalkSingleComplexOfFunctors X x).asFunctor ≅ stalkSingleFunctor X x :=
  (hasNaturalStalkHomotopy_godementAugmentation X x).choose_spec.choose_spec.choose_spec.choose

/-- The compatibility equation pinning `stalkHtpyE` to the Godement augmentation. -/
theorem stalkHtpyHe :
    (stalkHtpyJ X x).hom ≫ Functor.whiskerRight (godementAugmentation X)
        ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
          (ComplexShape.up ℕ)) =
      HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (stalkHtpyE X x).hom ≫
        (stalkHtpyI X x).hom :=
  (hasNaturalStalkHomotopy_godementAugmentation X
    x).choose_spec.choose_spec.choose_spec.choose_spec

/-- Every term of `stalkHtpyH` preserves zero morphisms. -/
theorem preservesZeroMorphisms_stalkHtpyH_X (n : ℕ) :
    ((stalkHtpyH X x).X n).PreservesZeroMorphisms :=
  HomologicalComplex.preservesZeroMorphisms_X_of_asFunctor_iso (stalkHtpyH X x)
    (stalkGodementFunctor X x) (stalkHtpyI X x)
    (preservesZeroMorphisms_stalkGodementFunctor_eval X x) n

/-- Every term of `stalkSingleComplexOfFunctors` preserves zero morphisms. -/
theorem preservesZeroMorphisms_stalkHtpySingle_X (n : ℕ) :
    ((stalkSingleComplexOfFunctors X x).X n).PreservesZeroMorphisms :=
  HomologicalComplex.preservesZeroMorphisms_X_of_asFunctor_iso (stalkSingleComplexOfFunctors X x)
    (stalkSingleFunctor X x) (stalkHtpyJ X x)
    (preservesZeroMorphisms_stalkSingleFunctor_eval X x) n

/-! #### Lifting the stalkwise homotopy equivalence along `F` -/

/-- **Lifting `stalkHtpyE` along `F`.** A homotopy equivalence of double complexes -- outer index
`ℕ` (the Godement degree), inner index `ℤ` (the degree of `F`) -- between applying
`stalkSingleComplexOfFunctors` and `stalkHtpyH` termwise to `F`. -/
noncomputable def bigHtpy :
    HomotopyEquiv
      (HomologicalComplex.liftComplexOfFunctors (stalkSingleComplexOfFunctors X x)
        (preservesZeroMorphisms_stalkHtpySingle_X X x) F)
      (HomologicalComplex.liftComplexOfFunctors (stalkHtpyH X x)
        (preservesZeroMorphisms_stalkHtpyH_X X x) F) :=
  HomologicalComplex.liftComplexOfFunctorsHomotopyEquiv (stalkHtpyE X x)
    (preservesZeroMorphisms_stalkHtpySingle_X X x) (preservesZeroMorphisms_stalkHtpyH_X X x) F

/-- The comparison identifying the lift of `stalkSingleComplexOfFunctors` with the lift of the
functor `stalkSingleFunctor`. -/
noncomputable def leftComparisonIso :
    HomologicalComplex.liftComplexOfFunctors (stalkSingleComplexOfFunctors X x)
        (preservesZeroMorphisms_stalkHtpySingle_X X x) F ≅
      HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
        (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F :=
  HomologicalComplex.liftComplexOfFunctorsIso (preservesZeroMorphisms_stalkHtpySingle_X X x)
    (stalkSingleFunctor X x) (preservesZeroMorphisms_stalkSingleFunctor_eval X x)
    (stalkHtpyJ X x) F

/-- The comparison identifying the lift of `stalkHtpyH` with the lift of the functor
`stalkGodementFunctor`. -/
noncomputable def rightComparisonIso :
    HomologicalComplex.liftComplexOfFunctors (stalkHtpyH X x)
        (preservesZeroMorphisms_stalkHtpyH_X X x) F ≅
      HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
        (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F :=
  HomologicalComplex.liftComplexOfFunctorsIso (preservesZeroMorphisms_stalkHtpyH_X X x)
    (stalkGodementFunctor X x) (preservesZeroMorphisms_stalkGodementFunctor_eval X x)
    (stalkHtpyI X x) F

/-- **The stalkwise homotopy equivalence, in the "functor applied to a complex" presentation.**
Conjugating `bigHtpy` by `leftComparisonIso` and `rightComparisonIso` carries it from the
complex-of-functors presentation to the presentation by `liftFunctorToComplex`. -/
noncomputable def bigHtpy' :
    HomotopyEquiv
      (HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
        (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F)
      (HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
        (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F) :=
  (HomotopyEquiv.ofIso (leftComparisonIso X F x)).symm.trans
    ((bigHtpy X F x).trans (HomotopyEquiv.ofIso (rightComparisonIso X F x)))

/-- **The compatibility equation for the stalkwise homotopy equivalence.** In bidegree `(0, q)` the
forward map of `bigHtpy'` is the stalk functor at `x` applied to the degree-`0` component of the
Godement augmentation at `F.X q`. -/
theorem bigHtpy'_hom_f_zero_f (q : ℤ) :
    ((bigHtpy' X F x).hom.f 0).f q =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        (((godementAugmentation X).app (F.X q)).f 0) := by
  have he := congrArg (fun φ : _ ⟶ _ => (φ.app (F.X q)).f 0) (stalkHtpyHe X x)
  change ((stalkHtpyJ X x).hom.app (F.X q)).f 0 ≫
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        (((godementAugmentation X).app (F.X q)).f 0) =
    ((stalkHtpyE X x).hom.f 0).app (F.X q) ≫ ((stalkHtpyI X x).hom.app (F.X q)).f 0 at he
  have hL0 : ((leftComparisonIso X F x).hom.f 0).f q = ((stalkHtpyJ X x).hom.app (F.X q)).f 0 :=
    rfl
  have hR0 : ((rightComparisonIso X F x).hom.f 0).f q =
      ((stalkHtpyI X x).hom.app (F.X q)).f 0 := rfl
  have hE0 : ((bigHtpy X F x).hom.f 0).f q = ((stalkHtpyE X x).hom.f 0).app (F.X q) := rfl
  rw [← hL0, ← hR0, ← hE0] at he
  have hb0 : ((bigHtpy' X F x).hom.f 0).f q =
      ((leftComparisonIso X F x).inv.f 0).f q ≫
        (((bigHtpy X F x).hom.f 0).f q ≫ ((rightComparisonIso X F x).hom.f 0).f q) := by
    show (((leftComparisonIso X F x).inv ≫ (bigHtpy X F x).hom ≫
        (rightComparisonIso X F x).hom).f 0).f q = _
    simp only [HomologicalComplex.comp_f]
  have hcancel : ((leftComparisonIso X F x).inv.f 0).f q ≫
      ((leftComparisonIso X F x).hom.f 0).f q = 𝟙 _ := by
    have h := (leftComparisonIso X F x).inv_hom_id
    have h2 := congrArg (fun φ : _ ⟶ _ => (φ.f 0).f q) h
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h2
    exact h2
  -- `rw` on this composite is not type-correct at implicit transparency (the intermediate
  -- objects only agree up to unfolding `leftComparisonIso`/`bigHtpy`), so the final steps are a
  -- term-mode `Eq.trans`/`congrArg` chain instead.
  have step1 : ((bigHtpy' X F x).hom.f 0).f q =
      ((leftComparisonIso X F x).inv.f 0).f q ≫
        (((leftComparisonIso X F x).hom.f 0).f q ≫
          (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementAugmentation X).app (F.X q)).f 0)) :=
    hb0.trans (congrArg (fun z => ((leftComparisonIso X F x).inv.f 0).f q ≫ z) he.symm)
  have step2 :
      ((leftComparisonIso X F x).inv.f 0).f q ≫
        (((leftComparisonIso X F x).hom.f 0).f q ≫
          (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementAugmentation X).app (F.X q)).f 0)) =
      (((leftComparisonIso X F x).inv.f 0).f q ≫ ((leftComparisonIso X F x).hom.f 0).f q) ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementAugmentation X).app (F.X q)).f 0) :=
    (Category.assoc _ _ _).symm
  have step3 :
      (((leftComparisonIso X F x).inv.f 0).f q ≫ ((leftComparisonIso X F x).hom.f 0).f q) ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementAugmentation X).app (F.X q)).f 0) =
      𝟙 _ ≫ (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        (((godementAugmentation X).app (F.X q)).f 0) :=
    congrArg (fun z => z ≫ (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
      (((godementAugmentation X).app (F.X q)).f 0)) hcancel
  exact step1.trans (step2.trans (step3.trans (Category.id_comp _)))

/-! #### Extending along `embeddingUpNat` and comparing with the Godement double complex -/

/-- **`bigHtpy'`, extended from the Godement degree `ℕ` to `ℤ`.** A homotopy equivalence of
double complexes, both indexed by `ℤ` in the outer (Godement) degree. -/
noncomputable def extBigHtpy :
    HomotopyEquiv
      (HomologicalComplex.liftFunctorToComplexExtend (stalkSingleFunctor X x)
        (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F)
      (HomologicalComplex.liftFunctorToComplexExtend (stalkGodementFunctor X x)
        (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F) :=
  HomologicalComplex.extendHomotopyEquiv (bigHtpy' X F x) ComplexShape.embeddingUpNat

/-- **The source of `extBigHtpy` is `F`, applied stalkwise and placed in degree `0`.** The lift
of the degree-`0`-concentrated stalk functor is, by `liftFunctorToComplexSingleIso`, the complex
`stalkComplexFunctor.obj F` placed in degree `0` of the Godement index, and `extendSingleIso`
identifies the extension of that degree-`0` placement (from `ℕ` to `ℤ`) with placing it directly
in degree `0` of the `ℤ`-indexed double complex, which is `singleObjComplex`. -/
noncomputable def leftIso :
    HomologicalComplex.liftFunctorToComplexExtend (stalkSingleFunctor X x)
        (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F ≅
      singleObjComplex ((stalkComplexFunctor X x).obj F) :=
  (ComplexShape.embeddingUpNat.extendFunctor
      (CochainComplex (GodementResolution.StalkModuleCat X x) ℤ)).mapIso
    (HomologicalComplex.liftFunctorToComplexSingleIso
      (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F) ≪≫
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    ((stalkComplexFunctor X x).obj F) 0 0 rfl

/-- **The target of `extBigHtpy` is the stalk functor applied termwise to the Godement double
complex of `F`.** The lift of `stalkGodementFunctor` is, by `liftFunctorToComplexMapIso`, the
same double complex as applying the stalk functor termwise to `godementRows`, and
`mapExtendIso` identifies the extension of that termwise application (an additive functor
commutes with extension) with applying the stalk functor termwise to the already-extended
`godementDoubleComplex`. -/
noncomputable def rightIso :
    HomologicalComplex.liftFunctorToComplexExtend (stalkGodementFunctor X x)
        (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F ≅
      HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F) :=
  (ComplexShape.embeddingUpNat.extendFunctor
      (CochainComplex (GodementResolution.StalkModuleCat X x) ℤ)).mapIso
    (HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
      (fun _ => inferInstance)
      (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F) ≪≫
  (HomologicalComplex.mapExtendIso
    ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
      (ComplexShape.up ℤ))
    ComplexShape.embeddingUpNat (godementRows X F)).symm

/-- **The homotopy equivalence `extBigHtpy`, transported to the presentation compared with
[Stacks, Tag 0FKH]**: between `F`, applied stalkwise and placed in degree `0`, and the stalk
functor applied termwise to the Godement double complex of `F`. -/
noncomputable def a' :
    HomotopyEquiv (singleObjComplex ((stalkComplexFunctor X x).obj F))
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)) :=
  (HomotopyEquiv.ofIso (leftIso X F x)).symm.trans
    ((extBigHtpy X F x).trans (HomotopyEquiv.ofIso (rightIso X F x)))

/-! #### Finiteness of the stalkwise Godement double complex, and the totalisation comparison -/

/-- **The diagonals of `mapBicomplex T (godementDoubleComplex X F)` are finite**, `T` being the
stalk functor at `x`. -/
theorem finite_diagonal_mapBicomplex_godementDoubleComplex (a : ℤ) [F.IsStrictlyGE a] (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        pq = n ∧
      ¬ IsZero (((HomologicalComplex₂.TotalMap.mapBicomplex
          (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).X
        pq.1).X pq.2)}.Finite :=
  finite_diagonal_of_vanishing _ a n
    (fun p q hp h => h ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map_isZero
      (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X_of_neg (godementComplex X)
        (fun _ => inferInstance) F p q hp)))
    (fun p q hq h => h ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map_isZero
      (HomologicalComplex.isZero_liftFunctorToComplexExtend_X_X (godementComplex X)
        (fun _ => inferInstance) F a p q hq)))

/-- **The stalkwise Godement double complex has a total complex.** -/
theorem hasTotal_mapBicomplex_godementDoubleComplex (a : ℤ) [F.IsStrictlyGE a] :
    (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (godementDoubleComplex X F)).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _
    (finite_diagonal_mapBicomplex_godementDoubleComplex X F x a)

/-! #### The stalkwise homotopy equivalence in bidegree `(0, n)` -/

/-- `a'.hom`, as a composite of the three comparison isomorphisms. -/
theorem a'_hom_eq :
    (a' X F x).hom =
      (leftIso X F x).inv ≫ (extBigHtpy X F x).hom ≫ (rightIso X F x).hom := by
  simp only [a', HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom, HomotopyEquiv.ofIso]

/-- `leftIso.inv`, unfolded to its two defining factors. -/
theorem leftIso_inv_eq :
    (leftIso X F x).inv =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          ((stalkComplexFunctor X x).obj F) 0 0
          (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv ≫
        HomologicalComplex.extendMap
          (HomologicalComplex.liftFunctorToComplexSingleIso
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).inv
          ComplexShape.embeddingUpNat := by
  rfl

/-- Two composites that cancel a shared isomorphism in the middle, stated for abstract objects and
morphisms. -/
private lemma cancel_mid_iso {C : Type*} [Category C] {A₁ A₂ A₃ : C}
    (e : A₁ ≅ A₂) (r : A₂ ⟶ A₃) : e.inv ≫ e.hom ≫ r = r := by
  simp

/-- `leftIso.inv`, read off in bidegree `(0, n)`, in closed form. -/
theorem leftIso_inv_f_zero_f (n : ℤ) :
    ((leftIso X F x).inv.f 0).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom.f n ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((stalkComplexFunctor X x).obj F)).inv.f n ≫
          ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
              (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
            ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n := by
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have hL0 : (leftIso X F x).inv.f 0 =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          ((stalkComplexFunctor X x).obj F) 0 0 h0).inv.f 0 ≫
        (HomologicalComplex.extendMap
            (HomologicalComplex.liftFunctorToComplexSingleIso
              (SheafOfModules.stalkFunctor (structureSheafRing X) x)
              (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).inv
            ComplexShape.embeddingUpNat).f 0 :=
    (congrArg (fun φ => HomologicalComplex.Hom.f φ 0) (leftIso_inv_eq X F x)).trans
      (HomologicalComplex.comp_f _ _ 0)
  have hExt0 := HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat
    ((stalkComplexFunctor X x).obj F) 0 0 h0
  have hR0 := HomologicalComplex.extendMap_f
    (HomologicalComplex.liftFunctorToComplexSingleIso
      (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).inv
    ComplexShape.embeddingUpNat h0
  have hcomp0 : (leftIso X F x).inv.f 0 =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((stalkComplexFunctor X x).obj F)).inv) ≫
        ((HomologicalComplex.liftFunctorToComplexSingleIso
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).inv.f 0 ≫
          ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
              (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
            ComplexShape.embeddingUpNat h0).inv) := by
    refine hL0.trans ((congrArg₂ (· ≫ ·) hExt0 hR0).trans ?_)
    simp only [Category.assoc]
    exact congrArg (fun ψ =>
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((stalkComplexFunctor X x).obj F)).inv ≫ ψ)
      (cancel_mid_iso _ _)
  have hcollapse := HomologicalComplex.liftFunctorToComplexSingleIso_inv_f_zero_f
    (SheafOfModules.stalkFunctor (structureSheafRing X) x)
    (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F n
  have step1 := congrArg (fun φ => HomologicalComplex.Hom.f φ n) hcomp0
  have step2 := step1.trans (HomologicalComplex.comp_f _ _ n)
  have step3 := step2.trans (congrArg (fun ψ =>
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((stalkComplexFunctor X x).obj F)).inv).f n ≫ ψ)
      (HomologicalComplex.comp_f _ _ n))
  have step4 := step3.trans (congrArg (fun ψ => ψ ≫
      (((HomologicalComplex.liftFunctorToComplexSingleIso
          (SheafOfModules.stalkFunctor (structureSheafRing X) x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).inv.f 0).f n ≫
        ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
            (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
          ComplexShape.embeddingUpNat h0).inv.f n))
      (HomologicalComplex.comp_f _ _ n))
  exact step4.trans (by
    simp only [hcollapse]
    rfl)

/-- `extBigHtpy.hom`, read off in bidegree `(0, n)`, in closed form: the `extendXIso` at outer
degree `0` on each side, with the middle factor given by `bigHtpy'_hom_f_zero_f`. -/
theorem extBigHtpy_hom_f_zero_f (n : ℤ) :
    ((extBigHtpy X F x).hom.f 0).f n =
      ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).hom.f n ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementAugmentation X).app (F.X n)).f 0) ≫
        ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
            (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
          ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n := by
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have hhom0 : (extBigHtpy X F x).hom.f 0 =
      (HomologicalComplex.extendMap (bigHtpy' X F x).hom ComplexShape.embeddingUpNat).f 0 :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ 0)
      (HomologicalComplex.extendHomotopyEquiv_hom (bigHtpy' X F x) ComplexShape.embeddingUpNat)
  have hExt0 := HomologicalComplex.extendMap_f (bigHtpy' X F x).hom
    ComplexShape.embeddingUpNat h0
  have hcomp0 : (extBigHtpy X F x).hom.f 0 =
      ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom ≫
        ((bigHtpy' X F x).hom.f 0 ≫
          ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
              (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
            ComplexShape.embeddingUpNat h0).inv) :=
    hhom0.trans hExt0
  have step1 := congrArg (fun φ => HomologicalComplex.Hom.f φ n) hcomp0
  have step2 := step1.trans (HomologicalComplex.comp_f _ _ n)
  have step3 := step2.trans (congrArg (fun ψ =>
      ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom.f n ≫ ψ)
      (HomologicalComplex.comp_f _ _ n))
  exact step3.trans (congrArg (fun ψ =>
      ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom.f n ≫ ψ ≫
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).inv.f n)
    (bigHtpy'_hom_f_zero_f X F x n))

/-- `rightIso.hom`, read off in bidegree `(0, n)`, in closed form. -/
theorem rightIso_hom_f_zero_f (n : ℤ) :
    ((rightIso X F x).hom.f 0).f n =
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).hom.f n ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementRows X F).extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n) := by
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have hhom0 : (rightIso X F x).hom.f 0 =
      (HomologicalComplex.extendMap
          (HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
            (fun _ => inferInstance)
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).hom
          ComplexShape.embeddingUpNat).f 0 ≫
        (HomologicalComplex.mapExtendIso
          ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
            (ComplexShape.up ℤ))
          ComplexShape.embeddingUpNat (godementRows X F)).inv.f 0 :=
    HomologicalComplex.comp_f _ _ 0
  have hExt0 := HomologicalComplex.extendMap_f
    (HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
      (fun _ => inferInstance)
      (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).hom
    ComplexShape.embeddingUpNat h0
  have hR0 := HomologicalComplex.mapExtendIso_inv_f
    ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
      (ComplexShape.up ℤ))
    ComplexShape.embeddingUpNat (godementRows X F) (0 : ℕ) (0 : ℤ) h0
  have hcomp0 : (rightIso X F x).hom.f 0 =
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom ≫
        ((HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
            (fun _ => inferInstance)
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).hom.f 0 ≫
          ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            ((godementRows X F).extendXIso ComplexShape.embeddingUpNat h0).inv) := by
    refine hhom0.trans ((congrArg₂ (· ≫ ·) hExt0 hR0).trans ?_)
    simp only [Category.assoc]
    exact congrArg (fun ψ =>
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom ≫
        ((HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
            (fun _ => inferInstance)
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).hom.f 0 ≫ ψ))
      (cancel_mid_iso _ _)
  have hmid : ((HomologicalComplex.liftFunctorToComplexMapIso (godementComplex X)
        (fun _ => inferInstance)
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).hom.f 0).f n = 𝟙 _ := rfl
  have hmap := Functor.mapHomologicalComplex_map_f
    (SheafOfModules.stalkFunctor (structureSheafRing X) x) (ComplexShape.up ℤ)
    ((godementRows X F).extendXIso ComplexShape.embeddingUpNat h0).inv n
  have step1 := congrArg (fun φ => HomologicalComplex.Hom.f φ n) hcomp0
  have step2 := step1.trans (HomologicalComplex.comp_f _ _ n)
  have step3 := step2.trans (congrArg (fun ψ =>
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat h0).hom.f n ≫ ψ)
      (HomologicalComplex.comp_f _ _ n))
  exact step3.trans (by
    simp only [hmid, hmap]
    rfl)

/-- Degreewise analogue of `cancel_mid_iso`: for an isomorphism `e` of complexes, the two
degreewise components `e.inv.f i` and `e.hom.f i` cancel a shared factor in the middle of a
composite. -/
private lemma cancel_mid_degree {V : Type*} [Category V] [HasZeroMorphisms V] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex V c} (e : K ≅ L) (i : ι) {M : V}
    (r : L.X i ⟶ M) :
    e.inv.f i ≫ e.hom.f i ≫ r = r := by
  simp

/-- A seven-morphism associativity-and-cancellation identity: composing `a ≫ b ≫ cinv` with
`chom ≫ d ≫ einv` with `ehom ≫ g` collapses to `a ≫ b ≫ d ≫ g`, given the two cancellations
`cinv ≫ chom ≫ r = r` and `einv ≫ ehom ≫ r = r`. -/
private lemma assoc_cancel_cancel {V : Type*} [Category V]
    {X0 X1 X2 X3 X4 X5 X6 : V}
    (a : X0 ⟶ X1) (b : X1 ⟶ X2) (cinv : X2 ⟶ X3) (chom : X3 ⟶ X2)
    (hc : ∀ {M : V} (r : X2 ⟶ M), cinv ≫ chom ≫ r = r)
    (d : X2 ⟶ X4) (einv : X4 ⟶ X5) (ehom : X5 ⟶ X4)
    (he : ∀ {M : V} (r : X4 ⟶ M), einv ≫ ehom ≫ r = r) (g : X4 ⟶ X6) :
    (a ≫ b ≫ cinv) ≫ (chom ≫ d ≫ einv) ≫ ehom ≫ g = a ≫ b ≫ d ≫ g := by
  simp only [Category.assoc]
  rw [hc, he]

/-- `a'.hom`, read off in bidegree `(0, n)`, in closed form: the two `singleObjXSelf` comparisons,
the stalk of the degree-`0` component of the Godement augmentation, and the stalk of the
`extendXIso` of the Godement double complex. -/
theorem a'_hom_f_zero_f (n : ℤ) :
    ((a' X F x).hom.f 0).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom.f n ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((stalkComplexFunctor X x).obj F)).inv.f n ≫
          (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementAugmentation X).app (F.X n)).f 0) ≫
          (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementRows X F).extendXIso ComplexShape.embeddingUpNat
              (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n) := by
  have step0a := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) (a'_hom_eq X F x)
  have step0b := step0a.trans (HomologicalComplex.comp_f _ _ 0)
  have step0c := step0b.trans (congrArg (fun ψ => (leftIso X F x).inv.f 0 ≫ ψ)
    (HomologicalComplex.comp_f _ _ 0))
  have step1 := congrArg (fun φ => HomologicalComplex.Hom.f φ n) step0c
  have step2 := step1.trans (HomologicalComplex.comp_f _ _ n)
  have step3 := step2.trans (congrArg (fun ψ => ((leftIso X F x).inv.f 0).f n ≫ ψ)
    (HomologicalComplex.comp_f _ _ n))
  have step4 := step3.trans (congrArg₂ (· ≫ ·) (leftIso_inv_f_zero_f X F x n)
    (congrArg₂ (· ≫ ·) (extBigHtpy_hom_f_zero_f X F x n) (rightIso_hom_f_zero_f X F x n)))
  exact step4.trans (assoc_cancel_cancel _ _ _ _
    (cancel_mid_degree
      ((HomologicalComplex.liftFunctorToComplex (stalkSingleFunctor X x)
          (preservesZeroMorphisms_stalkSingleFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))) n)
    _ _ _
    (cancel_mid_degree
      ((HomologicalComplex.liftFunctorToComplex (stalkGodementFunctor X x)
          (preservesZeroMorphisms_stalkGodementFunctor_eval X x) F).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))) n)
    _)

/-- **`a'.hom`, read off in bidegree `(0, n)`, identified with the stalk of the row
augmentation.** -/
theorem a'_hom_f_zero_f_eq_stalk_rowAugmentation (n : ℤ) :
    ((a' X F x).hom.f 0).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom.f n ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementRowAugmentation X F).f n) := by
  have hsingleF : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.X n)).inv =
      𝟙 (F.X n) := by
    rw [CochainComplex.single₀ObjXSelf]; rfl
  have hsingleM : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      ((stalkComplexFunctor X x).obj F)).inv.f n = 𝟙 _ := by
    rw [CochainComplex.single₀ObjXSelf]; rfl
  have hL : (godementRowAugmentation X F).f n =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.X n)).inv ≫
          ((godementAugmentation X).app (F.X n)).f 0) ≫
        ((godementRows X F).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n :=
    HomologicalComplex.comp_f _ _ n
  have hL' : (godementRowAugmentation X F).f n =
      ((godementAugmentation X).app (F.X n)).f 0 ≫
        ((godementRows X F).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n :=
    hL.trans ((congrArg (fun g => (g ≫ ((godementAugmentation X).app (F.X n)).f 0) ≫
        ((godementRows X F).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n) hsingleF).trans
      (congrArg (fun g => g ≫
          ((godementRows X F).extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n)
        (Category.id_comp _)))
  have hT : (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
      ((godementRowAugmentation X F).f n) =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementAugmentation X).app (F.X n)).f 0) ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          (((godementRows X F).extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n) :=
    (congrArg (SheafOfModules.stalkFunctor (structureSheafRing X) x).map hL').trans
      (Functor.map_comp _ _ _)
  exact (a'_hom_f_zero_f X F x n).trans
    (((congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((stalkComplexFunctor X x).obj F)).hom.f n ≫
        (g ≫ ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementAugmentation X).app (F.X n)).f 0) ≫
          (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            (((godementRows X F).extendXIso ComplexShape.embeddingUpNat
              (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))).inv.f n)))) hsingleM).trans
      (congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom.f n ≫ g) (Category.id_comp _))).trans
      (congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((stalkComplexFunctor X x).obj F)).hom.f n ≫ g) hT.symm))

/-- **Tag 0FKH's induced map, read off in degree `n`, identified with the stalk of the row
augmentation followed by the inclusion into the total complex.** -/
theorem totalAlphaF_a'_hom_eq
    [(HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).HasTotal
      (ComplexShape.up ℤ)]
    (n : ℤ) :
    totalAlphaF ((stalkComplexFunctor X x).obj F)
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (godementDoubleComplex X F)) (a' X F x).hom n =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementRowAugmentation X F).f n) ≫
        (HomologicalComplex₂.TotalMap.mapBicomplex
          (SheafOfModules.stalkFunctor (structureSheafRing X) x)
          (godementDoubleComplex X F)).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) :=
  (congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((stalkComplexFunctor X x).obj F)).inv.f n ≫
      g ≫ (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).ιTotal
        (ComplexShape.up ℤ) 0 n n (by simp))
    (a'_hom_f_zero_f_eq_stalk_rowAugmentation X F x n)).trans
    ((congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((stalkComplexFunctor X x).obj F)).inv.f n ≫ g) (Category.assoc
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((stalkComplexFunctor X x).obj F)).hom.f n)
      ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementRowAugmentation X F).f n))
      ((HomologicalComplex₂.TotalMap.mapBicomplex
          (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).ιTotal
        (ComplexShape.up ℤ) 0 n n (by simp)))).trans
      (cancel_mid_degree (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((stalkComplexFunctor X x).obj F)) n
        ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            ((godementRowAugmentation X F).f n) ≫
          (HomologicalComplex₂.TotalMap.mapBicomplex
              (SheafOfModules.stalkFunctor (structureSheafRing X) x)
              (godementDoubleComplex X F)).ιTotal
            (ComplexShape.up ℤ) 0 n n (by simp))))

/-- **The stalked inclusion into the total complex, followed by the finite-support comparison
isomorphism, equals the stalk of the unstalked inclusion.** -/
theorem ιTotal_totalIsoOfFinite_hom_f (a : ℤ) [F.IsStrictlyGE a] (n : ℤ) :
    (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (godementDoubleComplex X F)).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫
      (HomologicalComplex₂.TotalMap.totalIsoOfFinite
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)
        (fun n => finite_diagonal_godementDoubleComplex X F a n)).hom.f n =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) :=
  (congrArg (fun g => (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).ιTotal
      (ComplexShape.up ℤ) 0 n n (by simp) ≫ g.f n)
    (HomologicalComplex₂.TotalMap.totalIsoOfFinite_hom_eq_totalMap
      (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)
      (fun n => finite_diagonal_godementDoubleComplex X F a n))).trans
    (HomologicalComplex₂.TotalMap.ι_totalMapf (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (godementDoubleComplex X F) n 0 n (by simp))

/-- **The degreewise assembly of Tag 0FKH's comparison map with the finite-support isomorphism,
read off against `godementComparisonMap`.** -/
theorem totalAlphaF_a'_hom_comp_totalIsoOfFinite_hom_f (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)]
    [(HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)).HasTotal
      (ComplexShape.up ℤ)]
    (n : ℤ) :
    totalAlphaF ((stalkComplexFunctor X x).obj F)
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (godementDoubleComplex X F)) (a' X F x).hom n ≫
      (HomologicalComplex₂.TotalMap.totalIsoOfFinite
        (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)
        (fun n => finite_diagonal_godementDoubleComplex X F a n)).hom.f n =
      ((stalkComplexFunctor X x).map (godementComparisonMap X F a)).f n := by
  set e2 := HomologicalComplex₂.TotalMap.totalIsoOfFinite
    (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)
    (fun n => finite_diagonal_godementDoubleComplex X F a n) with he2
  have hA : totalAlphaF ((stalkComplexFunctor X x).obj F)
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.stalkFunctor (structureSheafRing X) x)
        (godementDoubleComplex X F)) (a' X F x).hom n ≫ e2.hom.f n =
      ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            ((godementRowAugmentation X F).f n) ≫
          (HomologicalComplex₂.TotalMap.mapBicomplex
              (SheafOfModules.stalkFunctor (structureSheafRing X) x)
              (godementDoubleComplex X F)).ιTotal
            (ComplexShape.up ℤ) 0 n n (by simp)) ≫ e2.hom.f n :=
    congrArg (fun g => g ≫ e2.hom.f n) (totalAlphaF_a'_hom_eq X F x n)
  have hassoc : ((SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementRowAugmentation X F).f n) ≫
      (HomologicalComplex₂.TotalMap.mapBicomplex
          (SheafOfModules.stalkFunctor (structureSheafRing X) x)
          (godementDoubleComplex X F)).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) ≫
        e2.hom.f n =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementRowAugmentation X F).f n) ≫
        ((HomologicalComplex₂.TotalMap.mapBicomplex
              (SheafOfModules.stalkFunctor (structureSheafRing X) x)
              (godementDoubleComplex X F)).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫
          e2.hom.f n) :=
    Category.assoc _ _ _
  have hι : (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementRowAugmentation X F).f n) ≫
      ((HomologicalComplex₂.TotalMap.mapBicomplex
            (SheafOfModules.stalkFunctor (structureSheafRing X) x)
            (godementDoubleComplex X F)).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫
        e2.hom.f n) =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementRowAugmentation X F).f n) ≫
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) :=
    congrArg (fun g =>
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
            ((godementRowAugmentation X F).f n) ≫ g)
      (ιTotal_totalIsoOfFinite_hom_f X F x a n)
  have hmap : (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementRowAugmentation X F).f n) ≫
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
        ((godementRowAugmentation X F).f n ≫
          (godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) :=
    (Functor.map_comp (SheafOfModules.stalkFunctor (structureSheafRing X) x) _ _).symm
  have hcomp : (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
      ((godementRowAugmentation X F).f n ≫
        (godementDoubleComplex X F).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) =
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
          ((godementComparisonMap X F a).f n) :=
    congrArg (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
      (godementComparisonMap_f X F a n).symm
  have hfunc : (SheafOfModules.stalkFunctor (structureSheafRing X) x).map
      ((godementComparisonMap X F a).f n) =
      ((stalkComplexFunctor X x).map (godementComparisonMap X F a)).f n :=
    (Functor.mapHomologicalComplex_map_f (SheafOfModules.stalkFunctor (structureSheafRing X) x)
      (ComplexShape.up ℤ) (godementComparisonMap X F a) n).symm
  exact hA.trans (hassoc.trans (hι.trans (hmap.trans (hcomp.trans hfunc))))

/-- **The stalk at `x` of `godementComparisonMap` is a homotopy equivalence.** -/
@[sga "4 XVII 4.2.9" "special case"]
theorem isHomotopyEquiv_stalkMap_godementComparisonMap (a : ℤ) [F.IsStrictlyGE a]
    [(godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ)] :
    ∃ e : HomotopyEquiv ((stalkComplexFunctor X x).obj F)
        ((stalkComplexFunctor X x).obj ((godementDoubleComplex X F).total (ComplexShape.up ℤ))),
      e.hom = (stalkComplexFunctor X x).map (godementComparisonMap X F a) := by
  have := hasTotal_mapBicomplex_godementDoubleComplex X F x a
  obtain ⟨⟨e1, he1⟩⟩ := isHomotopyEquiv_total_of_isHomotopyEquiv
    ((stalkComplexFunctor X x).obj F)
    (HomologicalComplex₂.TotalMap.mapBicomplex
      (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)) (a' X F x)
  set e2 := HomologicalComplex₂.TotalMap.totalIsoOfFinite
    (SheafOfModules.stalkFunctor (structureSheafRing X) x) (godementDoubleComplex X F)
    (fun n => finite_diagonal_godementDoubleComplex X F a n) with he2
  refine ⟨e1.trans (HomotopyEquiv.ofIso e2), ?_⟩
  have hhom : (e1.trans (HomotopyEquiv.ofIso e2)).hom = e1.hom ≫ e2.hom :=
    HomotopyEquiv.trans_hom e1 (HomotopyEquiv.ofIso e2)
  have hhom' : e1.hom ≫ e2.hom =
      totalAlpha ((stalkComplexFunctor X x).obj F)
        (HomologicalComplex₂.TotalMap.mapBicomplex
          (SheafOfModules.stalkFunctor (structureSheafRing X) x)
          (godementDoubleComplex X F)) (a' X F x).hom ≫ e2.hom :=
    congrArg (fun g => g ≫ e2.hom) he1
  refine hhom.trans (hhom'.trans ?_)
  exact HomologicalComplex.hom_ext _ _
    (fun n => totalAlphaF_a'_hom_comp_totalIsoOfFinite_hom_f X F x a n)

end StalkHomotopyEquivalence

/-- **[Stacks, Tag 0FKT], all four clauses, for the Godement resolution.** For a bounded below
complex `F` of `𝒪_X`-modules there is a quasi-isomorphism `F ⟶ G` with `G` bounded below in the
same degree, every term of `G` flasque, and, for every `x ∈ X`, the stalk map `F_x ⟶ G_x` a
homotopy equivalence of complexes of `𝒪_{X,x}`-modules. The map is `godementComparisonMap` onto
the totalisation of the Godement double complex of `F`. -/
@[stacks 0FKT "Godement resolution; all four clauses, including the stalkwise homotopy equivalence"]
theorem exists_quasiIso_boundedBelow_isFlasque_isHomotopyEquiv_stalk_godement
    (hF : ∃ n : ℤ, F.IsStrictlyGE n) :
    ∃ (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (f : F ⟶ G),
      QuasiIso f ∧ (∃ n : ℤ, G.IsStrictlyGE n) ∧
        (∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf (structureSheafRing X)).obj (G.X i))) ∧
        (∀ x : X, ∃ e : HomotopyEquiv ((stalkComplexFunctor X x).obj F)
            ((stalkComplexFunctor X x).obj G), e.hom = (stalkComplexFunctor X x).map f) := by
  obtain ⟨a, ha⟩ := hF
  have : F.IsStrictlyGE a := ha
  have : (godementDoubleComplex X F).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ (finite_diagonal_godementDoubleComplex X F a)
  obtain ⟨hqi, hge, hfl⟩ := exists_quasiIso_isStrictlyGE_isFlasque_godement X F a
  exact ⟨(godementDoubleComplex X F).total (ComplexShape.up ℤ), godementComparisonMap X F a,
    hqi, ⟨a, hge⟩, hfl, fun x => isHomotopyEquiv_stalkMap_godementComparisonMap X F x a⟩

end AlgebraicGeometry.GodementResolution

end
