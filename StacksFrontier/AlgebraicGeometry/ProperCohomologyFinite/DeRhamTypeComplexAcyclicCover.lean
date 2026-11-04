module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIsoShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedDerivedSections

/-!
# An acyclic covering computes derived sections, with module coefficients

Let `(X, O_X)` be a ringed space, let `U` be an open subset covered by a family `Ui`, and let `K^•`
be a bounded below complex of `O_X`-modules each term of which has vanishing higher cohomology on
every finite intersection `U_{i_0} ∩ ⋯ ∩ U_{i_p}`. Then the canonical comparison
`Tot(Č^•(Ui, K^•)) ⟶ RΓ(U, K^•)` of [Stacks, Tag 08BN] with module coefficients,
`Stacks.Cech.Linear.cechToDerivedSections`, is an isomorphism in `D(O_X(U))`. This is the
module-coefficient form of [Stacks, Tag 0FLH], whose abelian-group form is
`Stacks.Cech.isIso_cechToDerivedGlobalSections_app`.

## Main results

* `AlgebraicGeometry.DeRhamTypeComplex.rightAcyclic_cechTermFunctor`: a sheaf of modules acyclic
  on the intersections of the cover is right acyclic for the Čech cochains in each degree.
* `AlgebraicGeometry.DeRhamTypeComplex.quasiIso_totalCechComplexFunctor_map`: the total Čech
  complex carries a quasi-isomorphism into a bounded below complex of injectives, out of a complex
  acyclic on the intersections, to a quasi-isomorphism.
* `AlgebraicGeometry.DeRhamTypeComplex.isIso_cechToDerivedSections_app`: the module-coefficient
  form of [Stacks, Tag 0FLH].

## Implementation notes

The proof is that of the abelian-group form. By
`Stacks.Cech.Linear.totalCechToDerivedSections_app` the comparison at `K^•` is the Čech map of
the functorial injective resolution `K^• ⟶ L^•`, followed by maps which are invertible as soon
as the terms of `L^•` are right acyclic for sections over `U`, which injective objects are. The
Čech map is a quasi-isomorphism by Weibel's acyclic assembly lemma, its columns being the Čech
cochain functors in a fixed degree applied termwise; those functors carry a quasi-isomorphism
between bounded below complexes of right acyclic objects to a quasi-isomorphism, and the terms of
`K^•` are right acyclic for them because the Čech cochains of an injective resolution of an
acyclic sheaf are exact away from degree zero
(`Stacks.Cohomology.CechAcyclic.exactAt_cechTerm_cochainComplex`, the core of [Stacks, Tag 01ET]).

## References

* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

namespace AlgebraicGeometry.DeRhamTypeComplex

variable (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The Čech cochains in a fixed degree form an additive functor: the functor preserves finite
limits, in particular binary products, and zero morphisms. -/
instance additive_cechTermFunctor (n : ℕ) :
    (Stacks.Cohomology.CechAcyclic.cechTermFunctor O U Ui hU n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **A sheaf of modules acyclic on the intersections of the cover is right acyclic for the
Čech cochains of the cover in each degree.** The Čech cochains of an injective resolution of such
a sheaf are exact away from degree zero ([Stacks, Tag 01ET], in the form
`Stacks.Cohomology.CechAcyclic.exactAt_cechTerm_cochainComplex`), which says that the higher
right derived functors of the Čech cochain functor vanish on it. -/
theorem rightAcyclic_cechTermFunctor (n : ℕ) (F : SheafOfModules.{u} O)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    (Stacks.Cohomology.CechAcyclic.cechTermFunctor O U Ui hU n).rightAcyclic F := by
  rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
  intro m hm
  let G := Stacks.Cohomology.CechAcyclic.cechTermFunctor O U Ui hU n
  let J := injectiveResolution F
  have hex' := (Stacks.Cohomology.CechAcyclic.exactAt_cechTerm_cochainComplex O U Ui hU J n hac
    (m : ℤ) (by omega)).of_iso (G.mapExtendIso J.cocomplex embeddingUpNat)
  rw [HomologicalComplex.extend_exactAt_iff _ embeddingUpNat (embeddingUpNat_f m)] at hex'
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ m).1 hex').of_iso
    (J.isoRightDerivedObj G m)

/-- A homological complex whose terms are all zero objects is a zero object. -/
private theorem isZero_of_forall_isZero_X {C ι : Type*} [Category C] [HasZeroMorphisms C]
    {c : ComplexShape ι} {K : HomologicalComplex C c} (h : ∀ q, IsZero (K.X q)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun q => (h q).eq_of_src _ _

/-- **The columns of the Čech double complex carry a quasi-isomorphism to a quasi-isomorphism**:
in Čech degree `p` the column is the Čech cochain functor of that degree applied termwise, and
it is a quasi-isomorphism when the source is acyclic on the intersections of the cover and the
target has injective terms. -/
theorem quasiIso_cechComplexIntFunctor_eval_map (p : ℤ)
    {K L : CochainComplex (SheafOfModules.{u} O) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L)
    (hLinj : ∀ q : ℤ, Injective (L.X q))
    (hac : ∀ (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj
        (K.X q))) :
    QuasiIso (((cechComplexIntFunctor O U Ui hU ⋙
      HomologicalComplex.eval _ (up ℤ) p).mapHomologicalComplex (up ℤ)).map φ) := by
  rcases lt_or_ge p 0 with hneg | hpos
  · have hzero (M : CochainComplex (SheafOfModules.{u} O) ℤ) :
        IsZero (((cechComplexIntFunctor O U Ui hU ⋙
          HomologicalComplex.eval _ (up ℤ) p).mapHomologicalComplex (up ℤ)).obj M) := by
      exact isZero_of_forall_isZero_X fun q =>
        isZero_cechComplexIntFunctor_X O U Ui hU (M.X q) p hneg
    rw [(hzero K).eq_of_src (((cechComplexIntFunctor O U Ui hU ⋙
      HomologicalComplex.eval _ (up ℤ) p).mapHomologicalComplex (up ℤ)).map φ)
        ((hzero K).iso (hzero L)).hom]
    infer_instance
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    let G := Stacks.Cohomology.CechAcyclic.cechTermFunctor O U Ui hU n
    have hq : QuasiIso ((G.mapHomologicalComplex (up ℤ)).map φ) :=
      Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic G φ hK hL
        (fun q => rightAcyclic_cechTermFunctor X O U Ui hU n (K.X q) (hac q))
        (fun q => haveI := hLinj q; Functor.rightAcyclic_of_injective _ _)
    let α := NatIso.mapHomologicalComplex
      (Stacks.Cohomology.CechAcyclic.cechEvalIso O U Ui hU n) (up ℤ)
    have hnat : ((cechComplexIntFunctor O U Ui hU ⋙
        HomologicalComplex.eval _ (up ℤ) (n : ℤ)).mapHomologicalComplex (up ℤ)).map φ =
        α.hom.app K ≫ (G.mapHomologicalComplex (up ℤ)).map φ ≫ α.inv.app L := by
      rw [← Category.assoc, ← α.hom.naturality φ, Category.assoc, α.hom_inv_id_app,
        Category.comp_id]
    rw [hnat]
    infer_instance

/-- **The total Čech complex carries a quasi-isomorphism into a complex of injectives to a
quasi-isomorphism**, when the source is acyclic on the intersections of the cover: Weibel's
acyclic assembly lemma, from the columns
(`quasiIso_cechComplexIntFunctor_eval_map`) to the total complexes. -/
theorem quasiIso_totalCechComplexFunctor_map
    {K L : CochainComplex (SheafOfModules.{u} O) ℤ} (φ : K ⟶ L) [QuasiIso φ] (a : ℤ)
    (hKa : K.IsStrictlyGE a) (hLa : L.IsStrictlyGE a)
    (hLinj : ∀ q : ℤ, Injective (L.X q))
    (hac : ∀ (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj
        (K.X q))) :
    QuasiIso ((Stacks.Cech.Linear.totalCechComplexFunctor X O U Ui hU).map φ) := by
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_lowerBound
    ((HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
      (((cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ)).map φ)) 0 a
    (fun p q hq => isZero_cechBicomplex_X_X O U Ui hU K q p
      (Or.inl (K.isZero_of_isStrictlyGE a q hq)))
    (fun p hp => ?_)
    (fun p q hq => isZero_cechBicomplex_X_X O U Ui hU L q p
      (Or.inl (L.isZero_of_isStrictlyGE a q hq)))
    (fun p hp => ?_) (fun p => ?_)
  · exact isZero_of_forall_isZero_X fun q => isZero_cechBicomplex_X_X O U Ui hU K q p (Or.inr hp)
  · exact isZero_of_forall_isZero_X fun q => isZero_cechBicomplex_X_X O U Ui hU L q p (Or.inr hp)
  · exact quasiIso_cechComplexIntFunctor_eval_map X O U Ui hU p φ ⟨a, hKa⟩ ⟨a, hLa⟩ hLinj hac

/-- **[Stacks, Tag 0FLH] with module coefficients.** Let `(X, O_X)` be a ringed space, let `Ui`
be an open covering of an open `U`, and let `K^•` be a bounded below complex of `O_X`-modules with
`H^m(U_{i_0 … i_p}, K^q) = 0` for all `m > 0`, all tuples `i_0, …, i_p` and all degrees `q`. Then
the canonical comparison `Tot(Č^•(Ui, K^•)) ⟶ RΓ(U, K^•)` of
`Stacks.Cech.Linear.cechToDerivedSections` is an isomorphism in `D(O_X(U))`. -/
theorem isIso_cechToDerivedSections_app
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hac : ∀ (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj
        (K.1.X q))) :
    IsIso (((Stacks.Cech.Linear.cechToDerivedSections X O U).map Ui hU).app K) := by
  set L := (Stacks.Cech.injectiveResolutionFunctor X O).obj K
  set η := (Stacks.Cech.injectiveResolutionUnit X O).app K
  have hqi : QuasiIso η.hom := Stacks.Cech.injectiveResolution_quasiIso X O K
  have hLinj : ∀ q : ℤ, Injective (L.1.X q) := fun q => by
    change Injective ((InjectiveObject.ι (SheafOfModules.{u} O)).obj _)
    infer_instance
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff _ L.1).mp L.2
  have hcech : IsIso ((Stacks.Cech.Linear.totalCechDerivedFunctor X O U Ui hU).map η) := by
    change IsIso (DerivedCategory.Q.map
      ((Stacks.Cech.Linear.totalCechComplexFunctor X O U Ui hU).map η.hom))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_totalCechComplexFunctor_map X O U Ui hU η.hom (min a b)
        (K.1.isStrictlyGE_of_ge _ a (min_le_left a b))
        (L.1.isStrictlyGE_of_ge _ b (min_le_right a b)) hLinj hac)
  have hunit : IsIso ((Stacks.Cech.Linear.sectionsToDerivedNat X O U).app L) :=
    Stacks.Cech.Linear.isIso_sectionsToDerived_of_rightAcyclic X O U L fun n =>
      haveI := hLinj n; Functor.rightAcyclic_of_injective _ _
  change IsIso ((Stacks.Cech.Linear.totalCechToDerivedSections X O U Ui hU).app K)
  rw [Stacks.Cech.Linear.totalCechToDerivedSections_app]
  infer_instance

end AlgebraicGeometry.DeRhamTypeComplex

end
