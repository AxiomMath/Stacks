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
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.TruncLEResolutions

/-!
# Resolving the truncations `τ_{≥ -n}` of an unbounded complex compatibly

Replacing the terms of a complex by isomorphic objects, the duality between cochain complexes of
`A` and of `Aᵒᵖ` used to dualise the ladder of `CochainComplex.exists_sequence_quasiIso_truncLE`,
and the dual ladder of resolutions of the canonical truncations `τ_{≥ -n} K` (Stacks 070F,
`CochainComplex.exists_sequence_quasiIso_truncGE`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

universe v u

/-! ### Replacing the terms of a complex by isomorphic objects -/

section ReplaceTerms

open Opposite ComplexShape HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The complex with terms `Y i` obtained from `K` by conjugating the differentials by a
family of isomorphisms `K.X i ≅ Y i`. -/
private noncomputable def replaceTerms (K : HomologicalComplex A c) (Y : ι → A)
    (e : ∀ i, K.X i ≅ Y i) : HomologicalComplex A c where
  X := Y
  d i j := (e i).inv ≫ K.d i j ≫ (e j).hom
  shape i j h := by rw [K.shape i j h]; simp
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc,
      Limits.comp_zero, Limits.zero_comp]

private lemma replaceTerms_X (K : HomologicalComplex A c) (Y : ι → A) (e : ∀ i, K.X i ≅ Y i)
    (i : ι) : (replaceTerms K Y e).X i = Y i := rfl

attribute [local simp] replaceTerms_X

/-- The isomorphism between `K` and `replaceTerms K Y e`. -/
private noncomputable def replaceTermsIso (K : HomologicalComplex A c) (Y : ι → A)
    (e : ∀ i, K.X i ≅ Y i) : K ≅ replaceTerms K Y e where
  hom := { f := fun i ↦ (e i).hom, comm' := fun i j _ ↦ by simp [replaceTerms] }
  inv := { f := fun i ↦ (e i).inv, comm' := fun i j _ ↦ by simp [replaceTerms] }
  hom_inv_id := by ext i; simp
  inv_hom_id := by ext i; simp

private lemma replaceTermsIso_hom_f (K : HomologicalComplex A c) (Y : ι → A)
    (e : ∀ i, K.X i ≅ Y i) (i : ι) : (replaceTermsIso K Y e).hom.f i = (e i).hom := rfl

private lemma replaceTermsIso_inv_f (K : HomologicalComplex A c) (Y : ι → A)
    (e : ∀ i, K.X i ≅ Y i) (i : ι) : (replaceTermsIso K Y e).inv.f i = (e i).inv := rfl

attribute [local simp] replaceTermsIso_hom_f replaceTermsIso_inv_f

end ReplaceTerms

/-! ### The dual: resolving the truncations `τ_{≥ -n} K` compatibly -/

section TruncGE

open Opposite ComplexShape HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

section Duality

/-- The biproduct of `X` and `Y` in `Aᵒᵖ` is opposite to the biproduct of `X.unop` and
`Y.unop`. -/
private noncomputable def biprodUnopIso (X Y : Aᵒᵖ) : (X ⊞ Y).unop ≅ X.unop ⊞ Y.unop where
  hom := biprod.lift (biprod.inl : X ⟶ X ⊞ Y).unop (biprod.inr : Y ⟶ X ⊞ Y).unop
  inv := biprod.desc (biprod.fst : X ⊞ Y ⟶ X).unop (biprod.snd : X ⊞ Y ⟶ Y).unop
  hom_inv_id := by
    rw [biprod.lift_desc, ← unop_comp, ← unop_comp, ← unop_add, biprod.total]
    simp
  inv_hom_id := by ext <;> simp [← unop_comp]

private lemma biprodUnopIso_inv_unop_inl (X Y : Aᵒᵖ) :
    (biprodUnopIso X Y).inv ≫ (biprod.inl : X ⟶ X ⊞ Y).unop = biprod.fst := by
  ext <;> simp [biprodUnopIso, ← unop_comp]

omit [Abelian A] in
/-- The isomorphism closure of `P.op` contains a zero object as soon as `P` does. -/
private lemma containsZero_op_isoClosure (P : ObjectProperty A) [P.ContainsZero] :
    (P.op.isoClosure).ContainsZero := by
  obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
  exact ⟨op Z, hZ.op, P.op.le_isoClosure _ hPZ⟩

/-- The isomorphism closure of `P.op` is closed under binary biproducts as soon as `P` is. -/
private lemma biprod_op_isoClosure (P : ObjectProperty A)
    (hprod : ∀ X Y : A, P X → P Y → P (X ⊞ Y)) (X Y : Aᵒᵖ)
    (hX : P.op.isoClosure X) (hY : P.op.isoClosure Y) : P.op.isoClosure (X ⊞ Y) := by
  obtain ⟨X', hX', ⟨εX⟩⟩ := hX
  obtain ⟨Y', hY', ⟨εY⟩⟩ := hY
  exact ⟨op (X'.unop ⊞ Y'.unop), hprod _ _ hX' hY',
    ⟨biprod.mapIso εX εY ≪≫ (biprodUnopIso X' Y').op.symm⟩⟩

omit [Abelian A] in
/-- Every object of `Aᵒᵖ` is a quotient of an object satisfying the isomorphism closure of
`P.op`, as soon as every object of `A` is a subobject of an object satisfying `P`. -/
private lemma exists_epi_op_isoClosure (P : ObjectProperty A)
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (X : Aᵒᵖ) :
    ∃ (Y : Aᵒᵖ) (_ : P.op.isoClosure Y) (p : Y ⟶ X), Epi p := by
  obtain ⟨Y, hY, i, hi⟩ := hP X.unop
  exact ⟨op Y, P.op.le_isoClosure _ hY, i.op, inferInstance⟩

/-- The chain complex of `Aᵒᵖ` opposite to a cochain complex `K` of `A`. -/
private noncomputable abbrev opCC (K : CochainComplex A ℤ) : ChainComplex Aᵒᵖ ℤ := K.op

/-- The morphism of chain complexes of `Aᵒᵖ` opposite to `φ`. -/
private noncomputable abbrev opCCMap {K L : CochainComplex A ℤ} (φ : K ⟶ L) : opCC L ⟶ opCC K :=
  (opFunctor A (ComplexShape.up ℤ)).map φ.op

/-- The chain complex of `A` opposite to a cochain complex `Q` of `Aᵒᵖ`. -/
private noncomputable abbrev unopCC (Q : CochainComplex Aᵒᵖ ℤ) : ChainComplex A ℤ := Q.unop

/-- The morphism of chain complexes of `A` opposite to a morphism `φ` of cochain complexes
of `Aᵒᵖ`. -/
private noncomputable abbrev unopCCMap {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') :
    unopCC Q' ⟶ unopCC Q := (unopFunctor A (ComplexShape.up ℤ)).map φ.op

/-- The cochain complex of `Aᵒᵖ` opposite to `K`; its term in degree `n` is `op (K.X (-n))`. -/
private noncomputable abbrev opCx (K : CochainComplex A ℤ) : CochainComplex Aᵒᵖ ℤ :=
  (opCC K).restriction embeddingUpIntDownInt

/-- The morphism of cochain complexes of `Aᵒᵖ` opposite to `φ`. -/
private noncomputable abbrev opCxMap {K L : CochainComplex A ℤ} (φ : K ⟶ L) : opCx L ⟶ opCx K :=
  restrictionMap (opCCMap φ) embeddingUpIntDownInt

/-- The cochain complex of `A` opposite to a cochain complex `Q` of `Aᵒᵖ`; its term in degree
`n` is `(Q.X (-n)).unop`. -/
private noncomputable abbrev unopCx (Q : CochainComplex Aᵒᵖ ℤ) : CochainComplex A ℤ :=
  (unopCC Q).restriction embeddingUpIntDownInt

/-- The morphism of cochain complexes of `A` opposite to a morphism `φ` of cochain complexes
of `Aᵒᵖ`. -/
private noncomputable abbrev unopCxMap {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') :
    unopCx Q' ⟶ unopCx Q := restrictionMap (unopCCMap φ) embeddingUpIntDownInt

private lemma unopCx_X (Q : CochainComplex Aᵒᵖ ℤ) (n : ℤ) :
    (unopCx Q).X n = (Q.X (-n)).unop := rfl

private lemma unopCxMap_f {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') (n : ℤ) :
    (unopCxMap φ).f n = (φ.f (-n)).unop := rfl

private lemma unopCxMap_comp {Q Q' Q'' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') (ψ : Q' ⟶ Q'') :
    unopCxMap (φ ≫ ψ) = unopCxMap ψ ≫ unopCxMap φ := rfl

/-- The comparison isomorphisms of a restriction of complexes are natural. -/
private lemma restrictionXIso_hom_naturality {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C : Type*} [Category C] [HasZeroMorphisms C]
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (e : c.Embedding c') [e.IsRelIff]
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (K.restrictionXIso e h).hom ≫ φ.f i' =
      (restrictionMap φ e).f i ≫ (L.restrictionXIso e h).hom := by
  subst h
  rw [show (K.restrictionXIso e (rfl : e.f i = e.f i)).hom = 𝟙 _ from rfl,
    show (L.restrictionXIso e (rfl : e.f i = e.f i)).hom = 𝟙 _ from rfl]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- A morphism of complexes is a quasi-isomorphism in a degree `j'` in the image of an embedding
`e` of complex shapes if and only if its restriction along `e` is one in the corresponding
degree, provided the neighbouring degrees correspond as well. -/
private lemma quasiIsoAt_restrictionMap_iff {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C : Type*} [Category C] [Abelian C]
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) {i' j' k' : ι'} (hi : c.prev j = i) (hk : c.next j = k)
    (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k') :
    QuasiIsoAt (restrictionMap φ e) j ↔ QuasiIsoAt φ j' := by
  rw [quasiIsoAt_iff' _ i j k hi hk, quasiIsoAt_iff' φ i' j' k' hi'' hk'']
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'')
      (restriction.sc'Iso L e i j k hi' hj' hk' hi'' hk'')
      (by
        ext
        · exact restrictionXIso_hom_naturality φ e hi'
        · exact restrictionXIso_hom_naturality φ e hj'
        · exact restrictionXIso_hom_naturality φ e hk'))

/-- Quasi-isomorphisms are reflected by passing to the opposite cochain complexes. -/
private lemma quasiIsoAt_unopCxMap_iff {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') (i : ℤ) :
    QuasiIsoAt (unopCxMap φ) i ↔ QuasiIsoAt φ (-i) :=
  (quasiIsoAt_restrictionMap_iff (unopCCMap φ) embeddingUpIntDownInt (i - 1) i (i + 1)
    (by simp) (by simp) (i' := -i + 1) (j' := -i) (k' := -i - 1) (by simp; omega) (by simp)
    (by simp; omega) (by simp) (by simp)).trans (quasiIsoAt_unopFunctor_map_iff φ (-i))

private lemma quasiIso_unopCxMap {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') [QuasiIso φ] :
    QuasiIso (unopCxMap φ) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_unopCxMap_iff]
  infer_instance

private lemma mono_unopCxMap_f {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') (i : ℤ)
    (h : Epi (φ.f (-i))) : Mono ((unopCxMap φ).f i) := by
  rw [unopCxMap_f]
  exact unop_mono_of_epi _

private lemma isStrictlyGE_unopCx (Q : CochainComplex Aᵒᵖ ℤ) (n : ℤ) [Q.IsStrictlyLE n] :
    (unopCx Q).IsStrictlyGE (-n) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (Q.isZero_of_isStrictlyLE n (-i) (by omega)).unop

/-- Two comparison isomorphisms of the terms of a complex are compatible with the
differentials. -/
private lemma XIsoOfEq_hom_comp_d {B : Type*} [Category B] [HasZeroMorphisms B] {ι : Type*}
    {c : ComplexShape ι} (M : HomologicalComplex B c) {i i' j j' : ι} (hi : i = i')
    (hj : j = j') : (M.XIsoOfEq hi).hom ≫ M.d i' j' = M.d i j ≫ (M.XIsoOfEq hj).hom := by
  subst hi
  subst hj
  simp

/-- Passing twice to the opposite cochain complex returns the complex itself, up to the
reindexing `i ↦ - -i`. -/
private noncomputable def doubleOpIso (M : CochainComplex A ℤ) : M ≅ unopCx (opCx M) :=
  Hom.isoOfComponents (fun i ↦ M.XIsoOfEq (neg_neg i).symm)
    (fun i j _ ↦ XIsoOfEq_hom_comp_d M (neg_neg i).symm (neg_neg j).symm)

private lemma doubleOpIso_hom_f (M : CochainComplex A ℤ) (i : ℤ) :
    (doubleOpIso M).hom.f i = (M.XIsoOfEq (neg_neg i).symm).hom := rfl

private lemma doubleOpIso_hom_naturality {M N : CochainComplex A ℤ} (φ : M ⟶ N) :
    (doubleOpIso M).hom ≫ unopCxMap (opCxMap φ) = φ ≫ (doubleOpIso N).hom := by
  ext i
  exact (XIsoOfEq_hom_naturality φ (neg_neg i).symm).symm

private lemma isStrictlyLE_opCx (M : CochainComplex A ℤ) (b : ℤ) [M.IsStrictlyGE (-b)] :
    (opCx M).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (M.isZero_of_isStrictlyGE (-b) (-i) (by omega)).op

private lemma epi_unopCxMap_f {Q Q' : CochainComplex Aᵒᵖ ℤ} (φ : Q ⟶ Q') (i : ℤ)
    (h : Mono (φ.f (-i))) : Epi ((unopCxMap φ).f i) := by
  rw [unopCxMap_f]
  exact unop_epi_of_mono _

omit [Abelian A] in
/-- If an object of `Aᵒᵖ` is isomorphic to the opposite of an object satisfying `P`, then its
opposite is isomorphic to an object satisfying `P`. -/
private lemma isoClosure_unop_of_op_isoClosure (P : ObjectProperty A) {X : Aᵒᵖ}
    (hX : P.op.isoClosure X) : P.isoClosure X.unop := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  exact ⟨Y.unop, hY, ⟨e.symm.unop⟩⟩

/-- The factorisation of a morphism to a complex which is strictly `≥ a` through the canonical
truncation `M ⟶ M.truncGE a`; this is the universal property of `CochainComplex.πTruncGE`. -/
private noncomputable def descTruncGE {B : Type*} [Category B] [Abelian B]
    {M N : CochainComplex B ℤ} (u : M ⟶ N) (a : ℤ) [N.IsStrictlyGE a] : M.truncGE a ⟶ N :=
  CochainComplex.truncGEMap u a ≫ inv (N.πTruncGE a)

private lemma πTruncGE_comp_descTruncGE {B : Type*} [Category B] [Abelian B]
    {M N : CochainComplex B ℤ} (u : M ⟶ N) (a : ℤ) [N.IsStrictlyGE a] :
    M.πTruncGE a ≫ descTruncGE u a = u := by
  rw [show descTruncGE u a = CochainComplex.truncGEMap u a ≫ inv (N.πTruncGE a) from rfl,
    ← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- The dual of a canonical truncation is a canonical truncation: the complex opposite to
`τ_{≤ n}` of the opposite complex is `τ_{≥ -n}`, compatibly with the canonical morphisms out
of `K`. -/
private lemma exists_truncGE_iso (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ ε : K.truncGE (-n) ≅ unopCx ((opCx K).truncLE n),
      K.πTruncGE (-n) ≫ ε.hom = (doubleOpIso K).hom ≫ unopCxMap ((opCx K).ιTruncLE n) := by
  have : (unopCx ((opCx K).truncLE n)).IsStrictlyGE (-n) := isStrictlyGE_unopCx _ n
  have : (opCx (K.truncGE (-n))).IsStrictlyLE n := isStrictlyLE_opCx _ n
  have : Epi (K.πTruncGE (-n)) :=
    inferInstanceAs (Epi (HomologicalComplex.πTruncGE K (embeddingUpIntGE (-n))))
  obtain ⟨v, hv⟩ : ∃ v : K ⟶ unopCx ((opCx K).truncLE n),
      v = (doubleOpIso K).hom ≫ unopCxMap ((opCx K).ιTruncLE n) := ⟨_, rfl⟩
  have : Epi v := by
    have h : ∀ i : ℤ, Epi ((unopCxMap ((opCx K).ιTruncLE n)).f i) := fun i ↦
      epi_unopCxMap_f _ i (inferInstanceAs
        (Mono ((HomologicalComplex.ιTruncLE (opCx K) (embeddingUpIntLE n)).f (-i))))
    have := epi_of_epi_f _ h
    rw [hv]
    infer_instance
  obtain ⟨w, hw⟩ : ∃ w : K.truncGE (-n) ⟶ unopCx ((opCx K).truncLE n),
      w = descTruncGE v (-n) := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : unopCx ((opCx K).truncLE n) ⟶ K.truncGE (-n),
      w' = unopCxMap (liftTruncLE (opCxMap (K.πTruncGE (-n))) n)
        ≫ (doubleOpIso (K.truncGE (-n))).inv := ⟨_, rfl⟩
  have hπw : K.πTruncGE (-n) ≫ w = v := by
    rw [hw]
    exact πTruncGE_comp_descTruncGE v (-n)
  have hvw' : v ≫ w' = K.πTruncGE (-n) := by
    rw [hv, hw', Category.assoc, ← Category.assoc (unopCxMap ((opCx K).ιTruncLE n)),
      ← unopCxMap_comp, liftTruncLE_ιTruncLE, ← Category.assoc,
      doubleOpIso_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨⟨w, w', ?_, ?_⟩, by rw [hπw, hv]⟩
  · rw [← cancel_epi (K.πTruncGE (-n)), ← Category.assoc, hπw, hvw', Category.comp_id]
  · rw [← cancel_epi v, ← Category.assoc, hvw', hπw, Category.comp_id]

end Duality

/-- The ladder of Stacks 070F, with the terms of its complexes and the kernels of its
transition maps only known to be isomorphic to objects satisfying `P`. -/
private lemma exists_ladder_isoClosure (P : ObjectProperty A) [P.ContainsZero]
    (hprod : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (K : CochainComplex A ℤ) :
    ∃ (I : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ I n)
      (g : ∀ n : ℕ, I (n + 1) ⟶ I n),
      (∀ n, QuasiIso (f n)) ∧ (∀ (n : ℕ) (i : ℤ), Mono ((f n).f i)) ∧
        (∀ n : ℕ, (I n).IsStrictlyGE (-(n : ℤ))) ∧
        (∀ (n : ℕ) (i : ℤ), P.isoClosure ((I n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P.isoClosure C)
          (e : (I (n + 1)).X i ≅ (I n).X i ⊞ C), e.inv ≫ (g n).f i = biprod.fst) ∧
        (∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ g n
          = K.πTruncGE (-(n : ℤ)) ≫ f n) := by
  have hZ := containsZero_op_isoClosure P
  obtain ⟨Q, F, G, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P.op.isoClosure
      (biprod_op_isoClosure P hprod) (exists_epi_op_isoClosure P hP) (opCx K)
  choose ε hε using fun n : ℕ ↦ exists_truncGE_iso K (n : ℤ)
  have key : ∀ m : ℕ, K.πTruncGE (-(m : ℤ)) ≫ (ε m).hom ≫ unopCxMap (F m)
      = (doubleOpIso K).hom ≫ unopCxMap (F m ≫ (opCx K).ιTruncLE (m : ℤ)) := fun m ↦ by
    rw [← Category.assoc, hε m, unopCxMap_comp, Category.assoc]
  refine ⟨fun n ↦ unopCx (Q n), fun n ↦ (ε n).hom ≫ unopCxMap (F n),
    fun n ↦ unopCxMap (G n), fun n ↦ ?_, fun n i ↦ ?_, fun n ↦ ?_, fun n i ↦ ?_,
    fun n i ↦ ?_, fun n ↦ ?_⟩
  · have := hQ1 n
    have : QuasiIso (unopCxMap (F n)) := quasiIso_unopCxMap _
    infer_instance
  · rw [comp_f]
    have : IsIso (ε n).hom := inferInstance
    have := mono_unopCxMap_f (F n) i (hQ2 n (-i))
    infer_instance
  · have := hQ3 n
    exact isStrictlyGE_unopCx (Q n) (n : ℤ)
  · exact isoClosure_unop_of_op_isoClosure P (hQ4 n (-i))
  · obtain ⟨C, hC, e', he'⟩ := hQ5 n (-i)
    refine ⟨C.unop, isoClosure_unop_of_op_isoClosure P hC,
      e'.symm.unop ≪≫ biprodUnopIso ((Q n).X (-i)) C, ?_⟩
    show ((biprodUnopIso ((Q n).X (-i)) C).inv ≫ e'.hom.unop) ≫ ((G n).f (-i)).unop
      = biprod.fst
    rw [Category.assoc, ← unop_comp, he']
    exact biprodUnopIso_inv_unop_inl _ _
  · have e1 : K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ ((ε (n + 1)).hom ≫ unopCxMap (F (n + 1)))
        ≫ unopCxMap (G n)
        = ((doubleOpIso K).hom ≫ unopCxMap (F (n + 1) ≫ (opCx K).ιTruncLE ((n + 1 : ℕ) : ℤ)))
          ≫ unopCxMap (G n) := by
      rw [← key (n + 1)]
      simp only [Category.assoc]
    rw [e1, Category.assoc, ← unopCxMap_comp, hQ6 n, key n]

/-- Passage from the isomorphism closure of `P` to `P` itself: each term of each complex of the
ladder is replaced by an isomorphic object satisfying `P`. -/
private lemma exists_ladder_of_isoClosure (P : ObjectProperty A) (K : CochainComplex A ℤ)
    (I : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ I n)
    (g : ∀ n : ℕ, I (n + 1) ⟶ I n) (hqi : ∀ n, QuasiIso (f n))
    (hmono : ∀ (n : ℕ) (i : ℤ), Mono ((f n).f i))
    (hGE : ∀ n : ℕ, (I n).IsStrictlyGE (-(n : ℤ)))
    (hterm : ∀ (n : ℕ) (i : ℤ), P.isoClosure ((I n).X i))
    (hker : ∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P.isoClosure C)
      (e : (I (n + 1)).X i ≅ (I n).X i ⊞ C), e.inv ≫ (g n).f i = biprod.fst)
    (hcomm : ∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ g n
      = K.πTruncGE (-(n : ℤ)) ≫ f n) :
    ∃ (I : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ I n)
      (g : ∀ n : ℕ, I (n + 1) ⟶ I n),
      (∀ n, QuasiIso (f n)) ∧ (∀ (n : ℕ) (i : ℤ), Mono ((f n).f i)) ∧
        (∀ n : ℕ, (I n).IsStrictlyGE (-(n : ℤ))) ∧ (∀ (n : ℕ) (i : ℤ), P ((I n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P C) (e : (I (n + 1)).X i ≅ (I n).X i ⊞ C),
          e.inv ≫ (g n).f i = biprod.fst) ∧
        (∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ g n
          = K.πTruncGE (-(n : ℤ)) ≫ f n) := by
  choose Z hZ he using hterm
  set e : ∀ (n : ℕ) (i : ℤ), (I n).X i ≅ Z n i := fun n i ↦ (he n i).some with hedef
  -- the replacements of the complexes `I n` and the isomorphisms with them
  set I' : ℕ → CochainComplex A ℤ := fun n ↦ replaceTerms (I n) (Z n) (e n) with hI'
  set ρ : ∀ n : ℕ, I n ≅ I' n := fun n ↦ replaceTermsIso (I n) (Z n) (e n) with hρ
  have hρf : ∀ (n : ℕ) (i : ℤ), (ρ n).hom.f i = (e n i).hom := fun n i ↦ rfl
  have hρinv : ∀ (n : ℕ) (i : ℤ), (ρ n).inv.f i = (e n i).inv := fun n i ↦ rfl
  refine ⟨I', fun n ↦ f n ≫ (ρ n).hom, fun n ↦ (ρ (n + 1)).inv ≫ g n ≫ (ρ n).hom,
    fun n ↦ ?_, fun n i ↦ ?_, fun n ↦ ?_, fun n i ↦ hZ n i, fun n i ↦ ?_, fun n ↦ ?_⟩
  · have := hqi n
    infer_instance
  · have := hmono n i
    rw [comp_f]
    infer_instance
  · have := hGE n
    exact CochainComplex.isStrictlyGE_of_iso (ρ n) _
  · obtain ⟨C, hC, ε, hε⟩ := hker n i
    obtain ⟨C', hC', ⟨δ⟩⟩ := hC
    show ∃ (D : A) (_ : P D) (ee : Z (n + 1) i ≅ Z n i ⊞ D),
      ee.inv ≫ ((ρ (n + 1)).inv ≫ g n ≫ (ρ n).hom).f i = biprod.fst
    refine ⟨C', hC', (e (n + 1) i).symm ≪≫ ε ≪≫ biprod.mapIso (e n i) δ, ?_⟩
    show ((biprod.map (e n i).inv δ.inv ≫ ε.inv) ≫ (e (n + 1) i).hom) ≫
        (e (n + 1) i).inv ≫ (g n).f i ≫ (e n i).hom = biprod.fst
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ε.inv, hε, biprod.map_fst_assoc]
    simp
  · show K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ (f (n + 1) ≫ (ρ (n + 1)).hom) ≫
      ((ρ (n + 1)).inv ≫ g n ≫ (ρ n).hom) = K.πTruncGE (-(n : ℤ)) ≫ f n ≫ (ρ n).hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (f (n + 1)) (g n), ← Category.assoc (K.πTruncGE _) (f (n + 1) ≫ g n),
      hcomm n, Category.assoc]

/-- **Stacks 070F.** Let `A` be an abelian category and let `P` be a class of objects of `A`
which contains a zero object, is closed under finite products, and is such that every object of
`A` is a subobject of an object satisfying `P`. Let `K` be a cochain complex. Then there are
complexes `I n`, quasi-isomorphisms `f n : τ_{≥ -n} K ⟶ I n` and morphisms
`g n : I (n + 1) ⟶ I n` forming a commutative ladder under the canonical truncations of `K`,
such that (1) each `f n` is degreewise monomorphic, (2) each `I n` is bounded below with all
terms satisfying `P`, and (3) each `g n` is degreewise a split surjection whose kernel satisfies
`P`. This is the dual of Stacks 06XX. -/
@[stacks 070F]
public theorem exists_sequence_quasiIso_truncGE (P : ObjectProperty A) [P.ContainsZero]
    (hprod : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i) (K : CochainComplex A ℤ) :
    ∃ (I : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, K.truncGE (-(n : ℤ)) ⟶ I n)
      (g : ∀ n : ℕ, I (n + 1) ⟶ I n),
      (∀ n, QuasiIso (f n)) ∧ (∀ (n : ℕ) (i : ℤ), Mono ((f n).f i)) ∧
        (∀ n : ℕ, (I n).IsStrictlyGE (-(n : ℤ))) ∧ (∀ (n : ℕ) (i : ℤ), P ((I n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P C) (e : (I (n + 1)).X i ≅ (I n).X i ⊞ C),
          e.inv ≫ (g n).f i = biprod.fst) ∧
        (∀ n : ℕ, K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ g n
          = K.πTruncGE (-(n : ℤ)) ≫ f n) := by
  obtain ⟨I, f, g, h1, h2, h3, h4, h5, h6⟩ := exists_ladder_isoClosure P hprod hP K
  exact exists_ladder_of_isoClosure P K I f g h1 h2 h3 h4 h5 h6

end TruncGE

end CochainComplex
