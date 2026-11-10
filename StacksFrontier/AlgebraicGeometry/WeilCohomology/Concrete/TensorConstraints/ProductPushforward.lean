module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Commutativity

/-!
# Associativity of fibre products and pushforward along products of morphisms

The associativity isomorphism `(A₁ × A₂) × A₃ ⟶ A₁ × (A₂ × A₃)` of fibre products, and the
compatibility of the tensor product of correspondences with pushforward along `iA × 1` and
`1 × iB` for open and closed immersions `iA`, `iB`.

## Main definitions

* `Stacks.WeilCohomology.prodAssocHom`: the associativity isomorphism of fibre products.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-! ### Associativity -/

section AssocHom

variable {S A₁ A₂ A₃ : Scheme.{u}} (sA₁ : A₁ ⟶ S) (sA₂ : A₂ ⟶ S) (sA₃ : A₃ ⟶ S)

/-- The projections `(A₁ × A₂) × A₃ ⟶ A₂` and `(A₁ × A₂) × A₃ ⟶ A₃` agree after composing to
`S`. -/
theorem prodAssocHom_cond₁ :
    (Limits.pullback.fst (prodBase sA₁ sA₂) sA₃ ≫ Limits.pullback.snd sA₁ sA₂) ≫ sA₂ =
      Limits.pullback.snd (prodBase sA₁ sA₂) sA₃ ≫ sA₃ := by
  rw [Category.assoc, ← Limits.pullback.condition (f := sA₁) (g := sA₂)]
  exact Limits.pullback.condition (f := prodBase sA₁ sA₂) (g := sA₃)

/-- The associativity isomorphism `(A₁ × A₂) × A₃ ⟶ A₁ × (A₂ × A₃)` of fibre products over `S`. -/
def prodAssocHom :
    Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
    (Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
      (Limits.pullback.snd _ _) (prodAssocHom_cond₁ sA₁ sA₂ sA₃))
    (by
      change _ = _ ≫ Limits.pullback.fst sA₂ sA₃ ≫ sA₂
      rw [Limits.pullback.lift_fst_assoc, Category.assoc, Category.assoc,
        Limits.pullback.condition (f := sA₁) (g := sA₂)])

/-- `prodAssocHom` followed by the projection to `A₁` is the projection `(A₁ × A₂) × A₃ ⟶ A₁`. -/
@[reassoc (attr := simp)]
theorem prodAssocHom_fst : prodAssocHom sA₁ sA₂ sA₃ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ := by
  unfold prodAssocHom
  exact Limits.pullback.lift_fst _ _ _

/-- `prodAssocHom` followed by the projection to `A₂` is the projection `(A₁ × A₂) × A₃ ⟶ A₂`. -/
@[reassoc (attr := simp)]
theorem prodAssocHom_snd_fst :
    prodAssocHom sA₁ sA₂ sA₃ ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ := by
  unfold prodAssocHom
  rw [Limits.pullback.lift_snd_assoc]
  exact Limits.pullback.lift_fst _ _ _

/-- `prodAssocHom` followed by the projection to `A₃` is the projection `(A₁ × A₂) × A₃ ⟶ A₃`. -/
@[reassoc (attr := simp)]
theorem prodAssocHom_snd_snd :
    prodAssocHom sA₁ sA₂ sA₃ ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ := by
  unfold prodAssocHom
  rw [Limits.pullback.lift_snd_assoc]
  exact Limits.pullback.lift_snd _ _ _

/-- The projections `A₁ × (A₂ × A₃) ⟶ A₁` and `A₁ × (A₂ × A₃) ⟶ A₂` agree after composing to
`S`. -/
theorem prodAssocInv_cond₁ :
    Limits.pullback.fst sA₁ (prodBase sA₂ sA₃) ≫ sA₁ =
      (Limits.pullback.snd sA₁ (prodBase sA₂ sA₃) ≫ Limits.pullback.fst sA₂ sA₃) ≫ sA₂ := by
  rw [Category.assoc]
  exact Limits.pullback.condition (f := sA₁) (g := prodBase sA₂ sA₃)

/-- The induced map `A₁ × (A₂ × A₃) ⟶ A₁ × A₂` and the projection `A₁ × (A₂ × A₃) ⟶ A₃` agree
after composing to `S`. -/
theorem prodAssocInv_cond₂ :
    Limits.pullback.lift _ _ (prodAssocInv_cond₁ sA₁ sA₂ sA₃) ≫ prodBase sA₁ sA₂ =
      (Limits.pullback.snd sA₁ (prodBase sA₂ sA₃) ≫ Limits.pullback.snd sA₂ sA₃) ≫ sA₃ := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst sA₁ sA₂ ≫ sA₁ = _
  rw [Limits.pullback.lift_fst_assoc, prodAssocInv_cond₁, Category.assoc, Category.assoc,
    Limits.pullback.condition (f := sA₂) (g := sA₃)]

/-- The inverse of `Stacks.WeilCohomology.prodAssocHom`. -/
def prodAssocInv :
    Limits.pullback sA₁ (prodBase sA₂ sA₃) ⟶ Limits.pullback (prodBase sA₁ sA₂) sA₃ :=
  Limits.pullback.lift (Limits.pullback.lift _ _ (prodAssocInv_cond₁ sA₁ sA₂ sA₃))
    (Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _) (prodAssocInv_cond₂ sA₁ sA₂ sA₃)

/-- `prodAssocInv` followed by the projection to `A₁` is the projection `A₁ × (A₂ × A₃) ⟶ A₁`. -/
@[reassoc (attr := simp)]
theorem prodAssocInv_fst_fst :
    prodAssocInv sA₁ sA₂ sA₃ ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ := by
  unfold prodAssocInv
  rw [Limits.pullback.lift_fst_assoc]
  exact Limits.pullback.lift_fst _ _ _

/-- `prodAssocInv` followed by the projection to `A₂` is the projection `A₁ × (A₂ × A₃) ⟶ A₂`. -/
@[reassoc (attr := simp)]
theorem prodAssocInv_fst_snd :
    prodAssocInv sA₁ sA₂ sA₃ ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ := by
  unfold prodAssocInv
  rw [Limits.pullback.lift_fst_assoc]
  exact Limits.pullback.lift_snd _ _ _

/-- `prodAssocInv` followed by the projection to `A₃` is the projection `A₁ × (A₂ × A₃) ⟶ A₃`. -/
@[reassoc (attr := simp)]
theorem prodAssocInv_snd :
    prodAssocInv sA₁ sA₂ sA₃ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ := by
  unfold prodAssocInv
  exact Limits.pullback.lift_snd _ _ _

/-- The associativity morphism `prodAssocHom` is an isomorphism, with inverse `prodAssocInv`. -/
instance : IsIso (prodAssocHom sA₁ sA₂ sA₃) := by
  refine ⟨prodAssocInv sA₁ sA₂ sA₃, ?_, ?_⟩
  · apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;> simp
    · simp
  · apply Limits.pullback.hom_ext
    · simp
    · apply Limits.pullback.hom_ext <;> simp

end AssocHom

section TensorIntId

variable {A B P Q P' Q' : Scheme.{u}}
  {sA : A ⟶ (fieldChowSituation k).S} {sB : B ⟶ (fieldChowSituation k).S}
  {sP : P ⟶ (fieldChowSituation k).S} {sQ : Q ⟶ (fieldChowSituation k).S}
  {sP' : P' ⟶ (fieldChowSituation k).S} {sQ' : Q' ⟶ (fieldChowSituation k).S}
  [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [Smooth sP] [IsSeparated sP]
  [Smooth sQ] [IsSeparated sQ] [Smooth sP'] [IsSeparated sP'] [Smooth sQ'] [IsSeparated sQ']
  (iA : A ⟶ P) (iB : B ⟶ Q) [IsOpenImmersion iA] [IsProper iA] [IsOpenImmersion iB]
  [IsProper iB] (hiA : iA ≫ sP = sA) (hiB : iB ≫ sQ = sB)

/-- Pushforward along `1 × 1` is the identity. -/
theorem properChowPushforward_prodHom_id {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (i : ℤ) (x : chowGroup (fieldChowSituation k) (prodBase sX sY) i) :
    pf[prodBase sX sY, prodBase sX sY, prodHom sX sY sX sY (𝟙 X) (𝟙 Y) (Category.id_comp _)
      (Category.id_comp _), prodHom_comp_prodBase _ _ _ _ _ _ _ _, i] x = x := by
  rw [properChowPushforward_congr_hom (fieldChowSituation k) _ _ (prodHom_id sX sY) _
    (Category.id_comp _) _ _ (properPushforwardDescends _ _ _ _ _ _), properChowPushforward_id]
  rfl

/-- `(iA × iB)_* x ⊗ x' = ((iA × 1) × (iB × 1))_*(x ⊗ x')`, for the canonical diagonal classes. -/
theorem tensorInt_properChowPushforward_prodHom_left {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hP' : RelativeDimension sP' d')
    (hB : RelativeDimension sB e) (hQ' : RelativeDimension sQ' e')
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (r r' : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (x' : chowGroup (fieldChowSituation k) (prodBase sP' sQ') ((e' : ℤ) - r')) :
    tensorInt k sP sP' sQ sQ' (canonicalDiagonalClassFamily k) hP hP' hQ hQ' r r'
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x) x' =
      pf[tensorBase sA sP' sB sQ', tensorBase sP sP' sQ sQ',
          prodHom (prodBase sP sP') (prodBase sQ sQ') (prodBase sA sP') (prodBase sB sQ')
            (prodHom sP sP' sA sP' iA (𝟙 P') hiA (Category.id_comp _))
            (prodHom sQ sQ' sB sQ' iB (𝟙 Q') hiB (Category.id_comp _))
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _),
          prodHom_comp_prodBase _ _ _ _ _ _ _ _, ((e + e' : ℕ) : ℤ) - (r + r')]
        (tensorInt k sA sP' sB sQ' (canonicalDiagonalClassFamily k) hA hP' hB hQ' r r' x x') := by
  have h := tensorInt_properChowPushforward_prodHom iA iB hiA hiB (𝟙 P') (𝟙 Q')
    (Category.id_comp _) (Category.id_comp _) (canonicalDiagonalClassFamily_projectionFormula k)
    hA hP' hB hQ' hP hP' hQ hQ' r r' x x'
  rwa [properChowPushforward_prodHom_id] at h

/-- `x ⊗ (iA × iB)_* x' = ((1 × iA) × (1 × iB))_*(x ⊗ x')`, for the canonical diagonal classes. -/
theorem tensorInt_properChowPushforward_prodHom_right {d d' e e' : ℕ}
    (hP' : RelativeDimension sP' d') (hA : RelativeDimension sA d)
    (hQ' : RelativeDimension sQ' e') (hB : RelativeDimension sB e)
    (hP : RelativeDimension sP d) (hQ : RelativeDimension sQ e) (r r' : ℤ)
    (x' : chowGroup (fieldChowSituation k) (prodBase sP' sQ') ((e' : ℤ) - r'))
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r)) :
    tensorInt k sP' sP sQ' sQ (canonicalDiagonalClassFamily k) hP' hP hQ' hQ r' r x'
        (pf[prodBase sA sB, prodBase sP sQ, prodHom sP sQ sA sB iA iB hiA hiB,
          prodHom_comp_prodBase sP sQ sA sB iA iB hiA hiB, (e : ℤ) - r] x) =
      pf[tensorBase sP' sA sQ' sB, tensorBase sP' sP sQ' sQ,
          prodHom (prodBase sP' sP) (prodBase sQ' sQ) (prodBase sP' sA) (prodBase sQ' sB)
            (prodHom sP' sP sP' sA (𝟙 P') iA (Category.id_comp _) hiA)
            (prodHom sQ' sQ sQ' sB (𝟙 Q') iB (Category.id_comp _) hiB)
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _),
          prodHom_comp_prodBase _ _ _ _ _ _ _ _, ((e' + e : ℕ) : ℤ) - (r' + r)]
        (tensorInt k sP' sA sQ' sB (canonicalDiagonalClassFamily k) hP' hA hQ' hB r' r x' x) := by
  have h := tensorInt_properChowPushforward_prodHom (𝟙 P') (𝟙 Q') (Category.id_comp _)
    (Category.id_comp _) iA iB hiA hiB (canonicalDiagonalClassFamily_projectionFormula k)
    hP' hA hQ' hB hP' hP hQ' hQ r' r x' x
  rwa [properChowPushforward_prodHom_id] at h

end TensorIntId

end Stacks.WeilCohomology

end
