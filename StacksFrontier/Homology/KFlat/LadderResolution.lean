module
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.KFlat.Flat

/-!
# K-flat resolutions by a class of flat objects

Let `F : A ⥤ A ⥤ A` be a bifunctor on an abelian category, additive in each variable, with
total complexes, and let `P` be a class of objects of `A` — the *flat* objects — such that

* `P` contains a zero object, is closed under isomorphisms and binary biproducts, and every
  object is a quotient of an object of `P`;
* `P` is closed under sequential colimits, and sequential colimits in `A` are exact;
* for `M` in `P`, both `F(-, M)` and `F(M, -)` carry acyclic complexes to acyclic complexes;
* `F(X, -)` and `F(-, X)` commute with sequential colimits.

Then every complex `G` of objects of `A` receives a quasi-isomorphism `Q ⟶ G`, an epimorphism in
each degree, from a complex `Q` whose terms are in `P` and which is K-flat for `F` in both
variables. This is the argument of Stacks 06YS: `Q` is the colimit of the ladder of Stacks 077J
(06XX, `CochainComplex.exists_sequence_quasiIso_truncLE`), each rung of which is a bounded above
complex of objects of `P`, hence K-flat (Stacks 06YQ), and K-flatness passes to the colimit
(Stacks 06YR).

## Main results

* `CochainComplex.KFlatBifunctor.exists_resolution_colimit_of_flat`: the resolution, as a
  sequential colimit of bounded above complexes with terms in `P`.
* `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_flat`,
  `CochainComplex.KFlatBifunctor.kFlatLeft_of_isStrictlyLE_of_flat`: a bounded above complex
  with terms in `P` is K-flat in each variable.
* `CochainComplex.KFlatBifunctor.exists_kFlatResolution_of_flat`: the K-flat resolution with
  terms in `P`.

## References

* [The Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [The Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [The Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A : Type*} [Category A] [Abelian A] [HasColimitsOfShape ℕ A]
  [HasExactColimitsOfShape ℕ A]

/-- A sequential colimit of acyclic complexes is acyclic, at an arbitrary colimit cocone, in an
abelian category whose sequential colimits are exact. -/
lemma acyclic_of_isColimit_nat (E : ℕ ⥤ CochainComplex A ℤ) (s : Cocone E) (hs : IsColimit s)
    (hE : ∀ i, (E.obj i).Acyclic) : s.pt.Acyclic := fun n ↦
  (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
  (hcover : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
  (hcolim : ∀ D : ℕ ⥤ A, (∀ n, P (D.obj n)) → P (colimit D))

omit [HasExactColimitsOfShape ℕ A] [P.ContainsZero] in
include hcolim in
/-- The terms of a sequential colimit of complexes with terms in `P` are in `P`. -/
lemma prop_colimit_X (D : ℕ ⥤ CochainComplex A ℤ) (hD : ∀ (n : ℕ) (i : ℤ), P ((D.obj n).X i))
    (i : ℤ) : P ((colimit D).X i) :=
  P.prop_of_iso (preservesColimitIso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) D).symm
    (hcolim _ fun n ↦ hD n i)

omit [P.IsClosedUnderIsomorphisms] in
include hsum hcover in
/-- **The resolution of Stacks 06YS, presented as a sequential colimit.** Every complex receives
a quasi-isomorphism, an epimorphism in each degree, from the colimit of a sequence of bounded
above complexes with terms in `P`. -/
theorem exists_resolution_colimit_of_flat (G : CochainComplex A ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex A ℤ) (f : colimit D ⟶ G),
      (∀ n : ℕ, (D.obj n).IsStrictlyLE n) ∧ (∀ (n : ℕ) (i : ℤ), P ((D.obj n).X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  obtain ⟨Q, q, g, hq, hepi, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover G
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n ↦ q n ≫ G.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ G := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ G.ιTruncLE (n : ℤ) := fun n ↦ hc.fac s n
  refine ⟨D, α, hle, hflat,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α
      hα, fun i ↦ ?_⟩
  have hlt : i < ((i.toNat + 1 : ℕ) : ℤ) := by
    have := Int.self_le_toNat i
    push_cast
    omega
  have h1 : Epi ((q (i.toNat + 1)).f i) := hepi (i.toNat + 1) i
  have h2 : Epi ((G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    G.epi_ιTruncLE_f_of_lt _ i hlt
  have hfac : (c.ι.app (i.toNat + 1)).f i ≫ α.f i
      = (q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i :=
    congrArg (fun φ ↦ φ.f i) (hα (i.toNat + 1))
  have h3 : Epi ((q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    @epi_comp _ _ _ _ _ _ h1 _ h2
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ h3 hfac

variable (F : A ⥤ A ⥤ A) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [∀ X, PreservesColimitsOfShape ℕ (F.obj X)] [∀ X, PreservesColimitsOfShape ℕ (F.flip.obj X)]
  (hright : ∀ M, P M → ∀ G : CochainComplex A ℤ, G.Acyclic →
    (((F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic)
  (hleft : ∀ M, P M → ∀ G : CochainComplex A ℤ, G.Acyclic →
    (((F.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic)

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [∀ (X : A), PreservesColimitsOfShape ℕ (F.flip.obj X)] in
include hright in
/-- **A bounded above complex with terms in `P` is K-flat** (Stacks 06YQ). -/
theorem kFlat_of_isStrictlyLE_of_flat (K : CochainComplex A ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i, P (K.X i)) : KFlat F K :=
  kFlat_of_isStrictlyLE F K b (fun _ ↦ inferInstance) acyclic_of_isColimit_nat
    fun q ↦ kFlat_single_of_exact F _ q fun G hG ↦ hright _ (hK q) G hG

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [∀ (X : A), PreservesColimitsOfShape ℕ (F.obj X)] in
include hleft in
/-- **A bounded above complex with terms in `P` is K-flat in the left variable** (Stacks
06YQ). -/
theorem kFlatLeft_of_isStrictlyLE_of_flat (K : CochainComplex A ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i, P (K.X i)) : KFlatLeft F K :=
  (kFlatLeft_iff_kFlat_flip _ _).2 (kFlat_of_isStrictlyLE_of_flat P F.flip hleft K b hK)

/-- The colimit of a sequence of bounded above complexes with terms in `P` is K-flat. -/
private theorem kFlat_colimit_of_flat (Q : ObjectProperty A) (F : A ⥤ A ⥤ A) [F.Additive]
    [∀ X, (F.obj X).Additive] [∀ X, PreservesColimitsOfShape ℕ (F.obj X)]
    (hright : ∀ M, Q M → ∀ G : CochainComplex A ℤ, G.Acyclic →
      (((F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic)
    (D : ℕ ⥤ CochainComplex A ℤ) (hle : ∀ n : ℕ, (D.obj n).IsStrictlyLE n)
    (hflat : ∀ (n : ℕ) (i : ℤ), Q ((D.obj n).X i)) : KFlat F (colimit D) :=
  kFlat_of_isColimit F (colimit.cocone D) (colimit.isColimit _) (fun _ ↦ inferInstance)
    acyclic_of_isColimit_nat fun n ↦ kFlat_of_isStrictlyLE_of_flat Q F hright (D.obj n) n (hflat n)

include hsum hcover hcolim hright hleft in
/-- **K-flat resolutions with terms in `P`** (Stacks 06YS). Every complex receives a
quasi-isomorphism, an epimorphism in each degree, from a complex with terms in `P` which is
K-flat for `F` in both variables. -/
theorem exists_kFlatResolution_of_flat (G : CochainComplex A ℤ) :
    ∃ (Q : CochainComplex A ℤ) (p : Q ⟶ G), KFlat F Q ∧ KFlatLeft F Q ∧ (∀ i, P (Q.X i)) ∧
      QuasiIso p ∧ (∀ i, Epi (p.f i)) := by
  obtain ⟨D, f, hle, hflat, hqis, hepi⟩ := exists_resolution_colimit_of_flat P hsum hcover G
  refine ⟨colimit D, f, ?_, ?_, prop_colimit_X P hcolim D hflat, hqis, hepi⟩
  · exact kFlat_colimit_of_flat P F hright D hle hflat
  · exact (kFlatLeft_iff_kFlat_flip _ _).2 (kFlat_colimit_of_flat P F.flip hleft D hle hflat)

end CochainComplex.KFlatBifunctor

end
