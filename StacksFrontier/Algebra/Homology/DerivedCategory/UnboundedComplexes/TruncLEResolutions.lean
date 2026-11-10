module

public import Mathlib.Algebra.Category.Grp.AB
import StacksFrontier.Homology.HomologyColimit
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolving the truncations `τ_{≤ n}` of an unbounded complex compatibly

The twisted extension `glue h u` of a complex by a resolution of a mapping cone, and the
inductive construction of a commutative ladder of resolutions of the canonical truncations
`τ_{≤ n} K` of an arbitrary cochain complex `K` (Stacks 06XX,
`CochainComplex.exists_sequence_quasiIso_truncLE`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

universe v u

/-! ### Resolving the truncations `τ_{≤ n} K` compatibly -/

section TruncLE

open Category Preadditive Pretriangulated HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] HasDerivedCategory.standard

section Glue

variable {Q R L : CochainComplex A ℤ} (h : Q ⟶ L) (u : R ⟶ mappingCone h)

/-- The `(p, p + 1)` entry of the twisting cochain: the first component of `u`. -/
public noncomputable def ent (p q : ℤ) : R.X p ⟶ Q.X q :=
  if hpq : p + 1 = q then u.f p ≫ (mappingCone.fst h).1.v p q hpq else 0

public lemma ent_eq (p q : ℤ) (hpq : p + 1 = q) :
    ent h u p q = u.f p ≫ (mappingCone.fst h).1.v p q hpq := dite_eq_left hpq

public lemma ent_eq_zero (p q : ℤ) (hpq : ¬ p + 1 = q) : ent h u p q = 0 := dite_eq_right hpq

/-- The second component of `u`. -/
public noncomputable def bet (p : ℤ) : R.X p ⟶ L.X p :=
  u.f p ≫ (mappingCone.snd h).v p p (add_zero p)

public lemma d_ent (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) :
    R.d p q ≫ ent h u q r + ent h u p q ≫ Q.d q r = 0 := by
  rw [ent_eq _ _ _ _ hpq, ent_eq _ _ _ _ hqr, ← assoc, ← u.comm p q, assoc,
    mappingCone.d_fst_v h p q r hpq hqr]
  simp

public lemma d_bet (p q : ℤ) (hpq : p + 1 = q) :
    R.d p q ≫ bet h u q = ent h u p q ≫ h.f q + bet h u p ≫ L.d p q := by
  rw [ent_eq _ _ _ _ hpq]
  simp only [bet]
  rw [← assoc, ← u.comm p q, assoc, mappingCone.d_snd_v h p q hpq]
  simp

/-- The differential of the twisted extension in degrees `p, q`: the differential of the
biproduct `Q ⊞ R` corrected by the twisting cochain `ent h u`. -/
public noncomputable def glueD (p q : ℤ) : (Q.X p ⊞ R.X p) ⟶ (Q.X q ⊞ R.X q) :=
  biprod.lift (biprod.fst ≫ Q.d p q - biprod.snd ≫ ent h u p q) (biprod.snd ≫ R.d p q)

public lemma glueD_fst (p q : ℤ) :
    glueD h u p q ≫ biprod.fst = biprod.fst ≫ Q.d p q - biprod.snd ≫ ent h u p q := by
  simp [glueD]

public lemma glueD_snd (p q : ℤ) :
    glueD h u p q ≫ biprod.snd = biprod.snd ≫ R.d p q := by
  simp [glueD]

public lemma inl_glueD (p q : ℤ) :
    (biprod.inl : Q.X p ⟶ Q.X p ⊞ R.X p) ≫ glueD h u p q
      = Q.d p q ≫ (biprod.inl : Q.X q ⟶ Q.X q ⊞ R.X q) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [glueD]

public lemma inr_glueD (p q : ℤ) :
    (biprod.inr : R.X p ⟶ Q.X p ⊞ R.X p) ≫ glueD h u p q
      = -(ent h u p q ≫ (biprod.inl : Q.X q ⟶ Q.X q ⊞ R.X q))
        + R.d p q ≫ (biprod.inr : R.X q ⟶ Q.X q ⊞ R.X q) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [glueD]

public lemma glueD_comp_glueD (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) :
    glueD h u p q ≫ glueD h u q r = 0 := by
  have key : ent h u p q ≫ Q.d q r = -(R.d p q ≫ ent h u q r) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact d_ent h u p q r hpq hqr
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp only [glueD, assoc, biprod.lift_fst, biprod.lift_snd, comp_sub, sub_comp, comp_zero,
      zero_comp, biprod.lift_fst_assoc, biprod.lift_snd_assoc, d_comp_d, zero_sub, key,
      comp_neg, neg_neg, sub_self]

/-- The extension of `Q` by `R` twisted by the first component of `u`: degreewise the
biproduct `Q.X p ⊞ R.X p`, with the differential `glueD h u`. -/
public noncomputable def glue : CochainComplex A ℤ where
  X p := Q.X p ⊞ R.X p
  d p q := glueD h u p q
  shape p q hpq := by
    have h1 : Q.d p q = 0 := Q.shape p q hpq
    have h2 : R.d p q = 0 := R.shape p q hpq
    have h3 : ent h u p q = 0 := ent_eq_zero h u p q hpq
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [glueD, h1, h2, h3]
  d_comp_d' p q r hpq hqr := glueD_comp_glueD h u p q r hpq hqr

public lemma glue_X (p : ℤ) : (glue h u).X p = (Q.X p ⊞ R.X p) := rfl

public lemma glue_d (p q : ℤ) : (glue h u).d p q = glueD h u p q := rfl

/-- The degreewise split inclusion `Q ⟶ glue h u`. -/
public noncomputable def glueIn : Q ⟶ glue h u where
  f _ := biprod.inl
  comm' p q _ := inl_glueD h u p q

/-- The degreewise split projection `glue h u ⟶ R`. -/
public noncomputable def gluePr : glue h u ⟶ R where
  f _ := biprod.snd
  comm' p q _ := (glueD_snd h u p q).symm

public lemma glueD_desc (p q : ℤ) (hpq : p + 1 = q) :
    biprod.desc (h.f p) (bet h u p) ≫ L.d p q
      = glueD h u p q ≫ biprod.desc (h.f q) (bet h u q) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← assoc, biprod.inl_desc, ← assoc, inl_glueD, assoc, biprod.inl_desc]
    exact h.comm p q
  · rw [← assoc, biprod.inr_desc, ← assoc, inr_glueD]
    simp only [add_comp, neg_comp, assoc, biprod.inl_desc, biprod.inr_desc]
    rw [d_bet h u p q hpq]
    abel

/-- The map `glue h u ⟶ L` extending `h` by the second component of `u`. -/
public noncomputable def glueDesc : glue h u ⟶ L where
  f p := biprod.desc (h.f p) (bet h u p)
  comm' p q hpq := glueD_desc h u p q hpq

public lemma glueIn_glueDesc : glueIn h u ≫ glueDesc h u = h := by
  ext p
  exact biprod.inl_desc (h.f p) (bet h u p)

public lemma epi_snd_v (p : ℤ) : Epi ((mappingCone.snd h).v p p (add_zero p)) :=
  epi_of_epi_fac (mappingCone.inr_f_snd_v h p)

public lemma epi_glueDesc_f (hu : ∀ p, Epi (u.f p)) (p : ℤ) : Epi ((glueDesc h u).f p) := by
  have : Epi (bet h u p) := by
    have := hu p
    have := epi_snd_v h p
    exact epi_comp _ _
  exact epi_of_epi_fac (biprod.inr_desc (h.f p) (bet h u p))

/-- The degreewise split short exact sequence `0 ⟶ Q ⟶ glue h u ⟶ R ⟶ 0`. -/
public noncomputable abbrev glueSC : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (glueIn h u) (gluePr h u) (by ext p; exact biprod.inl_snd)

public noncomputable def glueSplitting (p : ℤ) :
    ((glueSC h u).map (HomologicalComplex.eval A (ComplexShape.up ℤ) p)).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := biprod.inl_fst
  s_g := biprod.inr_snd
  id := biprod.total

public lemma tri_mor₃_f (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.triangle h).mor₃.f p =
      -((mappingCone.fst h).1.v p q hpq ≫ (Q.shiftFunctorObjXIso 1 p q hpq.symm).inv) := by
  subst hpq
  dsimp [mappingCone.triangle]
  simp [HomComplex.Cochain.rightShift_v _ 1 0 (zero_add 1) p p (add_zero p) (p + 1) (by omega)]

/-- The homotopy identity underlying `glueHomotopy`, in degree `i`. -/
public lemma glue_homotopy_comm (i : ℤ) :
    biprod.desc (h.f i) (bet h u i) ≫ (mappingCone.inr h).f i =
      glueD h u i (i + 1) ≫ biprod.fst ≫ (mappingCone.inl h).v (i + 1) i (by omega) +
        ((biprod.fst : Q.X i ⊞ R.X i ⟶ Q.X i) ≫
            (mappingCone.inl h).v i (i - 1) (by omega)) ≫ (mappingCone h).d (i - 1) i +
        (biprod.snd : Q.X i ⊞ R.X i ⟶ R.X i) ≫ u.f i := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    refine (mappingCone.ext_to_iff h i (i + 1) rfl _ _).2 ⟨?_, ?_⟩ <;>
    simp [glueD, bet, ent_eq h u i (i + 1) rfl,
      mappingCone.d_fst_v h (i - 1) i (i + 1) (by omega) (by omega),
      mappingCone.d_snd_v h (i - 1) i (by omega)]

/-- The square `glue h u ⟶ L ⟶ mappingCone h` versus `glue h u ⟶ R ⟶ mappingCone h`
commutes up to the homotopy given by the first component. -/
public noncomputable def glueHomotopy :
    Homotopy (glueDesc h u ≫ mappingCone.inr h) (gluePr h u ≫ u) where
  hom i j := if hij : j + 1 = i then biprod.fst ≫ (mappingCone.inl h).v i j (by omega) else 0
  zero i j hij := dite_eq_right (by simpa using hij)
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from by simp),
      dite_eq_left rfl, dite_eq_left (show i - 1 + 1 = i by omega)]
    exact glue_homotopy_comm h u i

public lemma homOfDegreewiseSplit_glueSC :
    CochainComplex.homOfDegreewiseSplit (glueSC h u) (glueSplitting h u) =
      u ≫ (mappingCone.triangle h).mor₃ := by
  ext n
  change (CochainComplex.homOfDegreewiseSplit (glueSC h u) (glueSplitting h u)).f n
      = u.f n ≫ (mappingCone.triangle h).mor₃.f n
  rw [CochainComplex.homOfDegreewiseSplit_f, tri_mor₃_f h n (n + 1) rfl]
  simp only [CochainComplex.cocycleOfDegreewiseSplit, glueSC, glueSplitting,
    HomComplex.Cocycle.mk_coe, HomComplex.Cochain.mk_v, ShortComplex.map_X₂,
    HomologicalComplex.eval_obj]
  rw [glue_d]
  have key : (biprod.inr : R.X n ⟶ Q.X n ⊞ R.X n) ≫ glueD h u n (n + 1) ≫ biprod.fst
      = u.f n ≫ (-((mappingCone.fst h).1.v n (n + 1) rfl ≫
          (Q.shiftFunctorObjXIso 1 n (n + 1) rfl).inv)) := by
    rw [glueD_fst, ent_eq h u n (n + 1) rfl]
    simp
  exact key

/-- The connecting morphism `mappingCone h ⟶ Q⟦1⟧` of the standard triangle of `h`, named so
that its source is spelled `mappingCone h`. -/
@[sga "4½ Etat_0 1.2.1" "special case"]
public noncomputable def coneδ : mappingCone h ⟶ Q⟦(1 : ℤ)⟧ := (mappingCone.triangle h).mor₃

public lemma homOfDegreewiseSplit_glueSC' :
    CochainComplex.homOfDegreewiseSplit (glueSC h u) (glueSplitting h u) = u ≫ coneδ h :=
  homOfDegreewiseSplit_glueSC h u

/-- If the image of `f` under the localization functor `DerivedCategory.Qh` on the homotopy
category is an isomorphism, then `f` is a quasi-isomorphism. -/
public lemma quasiIso_of_isIso_Qh_map {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    (hf : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))) : QuasiIso f := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) f).1 hf

/-- A quasi-isomorphism of cochain complexes becomes an isomorphism in the derived category,
even after passing through the homotopy category. -/
public lemma isIso_Qh_map_of_quasiIso {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [QuasiIso f] :
    IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) := by
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) f).2
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 ‹_›)

/-- The morphism of triangles in the homotopy category from the triangle of the degreewise split
short exact sequence `0 ⟶ Q ⟶ glue h u ⟶ R ⟶ 0` to the triangle of the mapping cone of `h`,
with components the identity of `Q`, the map `glueDesc h u` and `u`. -/
public noncomputable def glueTriangleMap :
    trianglehOfDegreewiseSplit (glueSC h u) (glueSplitting h u) ⟶ mappingCone.triangleh h where
  hom₁ := 𝟙 _
  hom₂ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (glueDesc h u)
  hom₃ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u
  comm₁ := by
    have key : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (glueIn h u) ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (glueDesc h u)
        = 𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Q) ≫
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map h := by
      rw [← CategoryTheory.Functor.map_comp, glueIn_glueDesc, id_comp]
    exact key
  comm₂ := by
    have key : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (gluePr h u) ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u
        = (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (glueDesc h u) ≫
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (mappingCone.inr h) := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact (HomotopyCategory.eq_of_homotopy _ _ (glueHomotopy h u)).symm
    exact key
  comm₃ := by
    have key : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (CochainComplex.homOfDegreewiseSplit (glueSC h u) (glueSplitting h u)) ≫
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app Q) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)).map
          (𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Q))
        = (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u ≫
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (coneδ h) ≫
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso
              (1 : ℤ)).hom.app Q) := by
      rw [homOfDegreewiseSplit_glueSC', CategoryTheory.Functor.map_comp]
      simp
    exact key

public lemma quasiIso_glueDesc (hu : QuasiIso u) : QuasiIso (glueDesc h u) := by
  have hT₁ := CochainComplex.trianglehOfDegreewiseSplit_distinguished (glueSC h u)
    (glueSplitting h u)
  have hT₂ := HomotopyCategory.mappingCone_triangleh_distinguished h
  have hiso₁ : IsIso (DerivedCategory.Qh.mapTriangle.map (glueTriangleMap h u)).hom₁ := by
    have key : IsIso (DerivedCategory.Qh.map
        (𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Q))) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    exact key
  have hiso₃ : IsIso (DerivedCategory.Qh.mapTriangle.map (glueTriangleMap h u)).hom₃ := by
    have key : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u)) :=
      isIso_Qh_map_of_quasiIso u
    exact key
  have key := isIso₂_of_isIso₁₃ (DerivedCategory.Qh.mapTriangle.map (glueTriangleMap h u))
    (DerivedCategory.Qh.map_distinguished _ hT₁) (DerivedCategory.Qh.map_distinguished _ hT₂)
    hiso₁ hiso₃
  exact quasiIso_of_isIso_Qh_map (glueDesc h u) key

end Glue

section Induction

variable (P : ObjectProperty A) (K : CochainComplex A ℤ)

/-- A stage of the ladder: a degreewise epimorphic quasi-isomorphism onto `τ_{≤n}K` from a
complex which is strictly bounded above by `n` with all terms satisfying `P`. -/
private structure Res (n : ℕ) where
  /-- the resolving complex -/
  Q : CochainComplex A ℤ
  /-- the resolution -/
  f : Q ⟶ K.truncLE (n : ℤ)
  quasiIso : QuasiIso f
  epi : ∀ i, Epi (f.f i)
  isStrictlyLE : Q.IsStrictlyLE (n : ℤ)
  props : ∀ i, P (Q.X i)

variable {P K}

/-- One step of the ladder. -/
private structure Ext {n : ℕ} (s : Res P K n) where
  /-- the next stage -/
  next : Res P K (n + 1)
  /-- the horizontal arrow -/
  g : s.Q ⟶ next.Q
  split : ∀ i : ℤ, ∃ (C : A) (_ : P C) (e : (next.Q).X i ≅ s.Q.X i ⊞ C),
    g.f i ≫ e.hom = biprod.inl
  ladder : g ≫ next.f ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) = s.f ≫ K.ιTruncLE ((n : ℕ) : ℤ)

private lemma nonempty_ext [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    {n : ℕ} (s : Res P K n) : Nonempty (Ext s) := by
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have := s.isStrictlyLE
  have : s.Q.IsStrictlyLE ((n + 1 : ℕ) : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ (n : ℤ) _ (by omega)
  -- the transition map to the next truncation
  set h : s.Q ⟶ K.truncLE ((n + 1 : ℕ) : ℤ) :=
    inv (s.Q.ιTruncLE ((n + 1 : ℕ) : ℤ)) ≫
      CochainComplex.truncLEMap (s.f ≫ K.ιTruncLE ((n : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) with hdef
  have hh : h ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) = s.f ≫ K.ιTruncLE ((n : ℕ) : ℤ) := by
    rw [hdef, assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]
  -- the cone of `h` is strictly bounded above by `n + 1`
  have : (mappingCone h).IsStrictlyLE ((n + 1 : ℕ) : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨s.Q.isZero_of_isStrictlyLE ((n + 1 : ℕ) : ℤ) (i + 1) (by omega),
      (K.truncLE ((n + 1 : ℕ) : ℤ)).isZero_of_isStrictlyLE ((n + 1 : ℕ) : ℤ) i hi⟩
  obtain ⟨R, uu, hepi, hqis, hPR, hRLE⟩ :=
    (CochainComplex.exists_quasiIso_prop P hP ((n + 1 : ℕ) : ℤ)).1 (mappingCone h)
  refine ⟨{ next := { Q := glue h uu
                      f := glueDesc h uu
                      quasiIso := quasiIso_glueDesc h uu hqis
                      epi := epi_glueDesc_f h uu hepi
                      isStrictlyLE := ?_
                      props := ?_ }
            g := glueIn h uu
            split := ?_
            ladder := ?_ }⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    refine (biprod_isZero_iff _ _).2 ⟨?_, ?_⟩
    · exact s.Q.isZero_of_isStrictlyLE ((n + 1 : ℕ) : ℤ) i (by omega)
    · exact R.isZero_of_isStrictlyLE ((n + 1 : ℕ) : ℤ) i (by omega)
  · exact fun i => hsum _ _ (s.props i) (hPR i)
  · exact fun i => ⟨R.X i, hPR i, Iso.refl _, comp_id _⟩
  · rw [← assoc, glueIn_glueDesc, hh]

/-- The chosen step. -/
private noncomputable def step [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    {n : ℕ} (s : Res P K n) : Ext s := (nonempty_ext hsum hP s).some

/-- The chosen ladder. -/
private noncomputable def tower [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (s₀ : Res P K 0) : ∀ n : ℕ, Res P K n
  | 0 => s₀
  | (n + 1) => (step hsum hP (tower hsum hP s₀ n)).next

end Induction

/-- **Stacks 06XX.** Let `A` be an abelian category and let `P` be a class of objects of `A`
which contains a zero object, is closed under finite direct sums, and is such that every object
of `A` is a quotient of an object satisfying `P`. Let `K` be a cochain complex. Then there are
complexes `Q n`, quasi-isomorphisms `f n : Q n ⟶ τ_{≤ n} K` and morphisms
`g n : Q n ⟶ Q (n + 1)` forming a commutative ladder over the canonical truncations of `K`,
such that (1) each `f n` is degreewise epimorphic, (2) each `Q n` is bounded above with all
terms satisfying `P`, and (3) each `g n` is degreewise a split injection whose cokernel
satisfies `P`. -/
@[stacks 06XX]
public theorem exists_sequence_quasiIso_truncLE (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (K : CochainComplex A ℤ) :
    ∃ (Q : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, Q n ⟶ K.truncLE n)
      (g : ∀ n : ℕ, Q n ⟶ Q (n + 1)),
      (∀ n, QuasiIso (f n)) ∧ (∀ (n : ℕ) (i : ℤ), Epi ((f n).f i)) ∧
        (∀ n : ℕ, (Q n).IsStrictlyLE n) ∧ (∀ (n : ℕ) (i : ℤ), P ((Q n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P C) (e : (Q (n + 1)).X i ≅ (Q n).X i ⊞ C),
          (g n).f i ≫ e.hom = biprod.inl) ∧
        (∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)
          = f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) := by
  obtain ⟨Q₀, f₀, hepi₀, hqis₀, hP₀, hLE₀⟩ :=
    (CochainComplex.exists_quasiIso_prop P hP ((0 : ℕ) : ℤ)).1 (K.truncLE ((0 : ℕ) : ℤ))
  let s₀ : Res P K 0 :=
    { Q := Q₀, f := f₀, quasiIso := hqis₀, epi := hepi₀, isStrictlyLE := hLE₀, props := hP₀ }
  let T : ∀ n : ℕ, Res P K n := tower hsum hP s₀
  refine ⟨fun n => (T n).Q, fun n => (T n).f, fun n => (step hsum hP (T n)).g,
    fun n => (T n).quasiIso, fun n i => (T n).epi i, fun n => (T n).isStrictlyLE,
    fun n i => (T n).props i, fun n i => (step hsum hP (T n)).split i,
    fun n => (step hsum hP (T n)).ladder⟩

end TruncLE

end CochainComplex
