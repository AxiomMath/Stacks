module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksCore.Algebra.Homology.SpectralSequence.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.StupidTruncation
public import StacksFrontier.Homology.Injectives.Ext.FilteredPageOne
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Ext spectral sequences of the truncation filtrations of an object of the derived category

Let `A` be a Grothendieck abelian category and let `M`, `K` be objects of its derived category.
Any cochain complex `M'` representing `M` can be filtered by its canonical truncations,
`F^pM'^• = τ_{≤ -p}M'^•`, and the Ext spectral sequence of that filtered complex has graded
pieces `gr^{-p}M'^•`, which represent `H^p(M)[-p]`.  Its first page is therefore
`E_1^{p,q} = Ext^{2p+q}(H^p(M), K)`.

The construction uses a chosen representative, but the resulting spectral sequence does not
depend on it: two representatives of `M` are connected, in the homotopy category, by a pair of
quasi-isomorphisms out of a common complex, a quasi-isomorphism induces a quasi-isomorphism on
each canonical truncation and hence on each graded piece, and a comparison morphism of Ext
spectral sequences which is an isomorphism on the graded pieces is an isomorphism on the first
page, hence on the whole spectral sequence.

Filtering `M'` instead by its brutal truncations, `F^pM'^• = σ_{≥ p}M'^•`, whose graded piece
`gr^{-p}M'^•` is the term `M'^{-p}[p]`, gives a spectral sequence with
`E_1^{p,q} = Ext^q(M'^{-p}, K)`.

## Main definitions

* `Stacks.Injectives.CanonicalExtSpectralSequence`: the canonical truncation filtration of a
  representative, its Ext spectral sequence, and the identification of the first page.
* `Stacks.Injectives.CanonicalExtSpectralSequence.spectralSequence`: the underlying spectral
  sequence, namely the Ext spectral sequence of the canonical truncation filtration.
* `Stacks.Injectives.canonicalExtSpectralSequence`: the canonical truncation filtration of a
  representative is such data.
* `Stacks.Injectives.extOfGradedPieceShiftIso`: an identification of the first argument of an Ext
  group with a shift, moved into the degree.
* `Stacks.Injectives.stupidExtSpectralSequence`: the Ext spectral sequence of the brutal
  truncation filtration of a representative.
* `Stacks.Injectives.stupidExtSpectralSequenceE₁`: the identification
  `E_1^{p,q} = Ext^q(M'^{-p}, K)`.

## Main results

* `Stacks.Injectives.exists_canonicalExtSpectralSequence`: such data exists for every complex
  representing `M`.
* `Stacks.Injectives.canonicalExtSpectralSequence_iso`: the spectral sequences obtained from two
  representatives of `M` are isomorphic.

## Implementation notes

The filtration of a representative is recorded only up to isomorphism over that representative,
which is the categorical form of the equality `F^pM'^• = τ_{≤ -p}M'^•`; the field
`stepIso_hom_comp` pins the identification down by requiring it to commute with the inclusions
into the representative.  The spectral sequence is definitionally the construction of Tag 0G1Z
applied to the filtered complex, not merely some spectral sequence with an isomorphic first page,
so the independence statement identifies every page, differential and page-turning isomorphism.

The graded piece of either filtration represents a shift, and `Ext` out of a shift is `Ext` in a
shifted degree; `extOfGradedPieceShiftIso` performs that transfer once, with the shift as a
parameter, for both filtrations.

## References

* [Stacks Project, Tag 0G20](https://stacks.math.columbia.edu/tag/0G20)
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace Stacks.Injectives

/-- The spectral sequence associated to the canonical truncation filtration
`F^p M^• = τ_{≤ -p} M^•` of a representative of an object of the derived category. -/
structure CanonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj M' ≅ M) where
  /-- The representative equipped with its canonical truncation filtration. -/
  filtered : CochainComplex.Filtered A
  /-- The underlying complex of the filtration is the chosen representative. -/
  underlyingIso : filtered.X ≅ M'
  /-- The `p`-th filtration step is the canonical truncation `τ_{≤ -p} M'`. -/
  stepIso (p : ℤ) : filtered.filtration.obj (op p) ≅ M'.truncLE (-p)
  /-- The identification of a filtration step with the corresponding truncation commutes with
  their inclusions into the chosen representative. -/
  stepIso_hom_comp (p : ℤ) :
    (stepIso p).hom ≫ M'.ιTruncLE (-p) =
      filtered.filtration.ι.app (op p) ≫ underlyingIso.hom
  /-- Its first page is
  `E₁^{p,q} = Ext^{2p+q}(H^p(M), K)`. -/
  e₁Iso (p q : ℤ) :
    ((extSpectralSequence K filtered).1.page 1).X (p, q) ≅
      AddCommGrpCat.of
      (DerivedCategory.Ext ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A p).obj M)) K (2 * p + q))

/-- The spectral sequence of the canonical truncation filtration, namely the construction of
Tag 0G1Z applied to that filtered complex. -/
noncomputable abbrev CanonicalExtSpectralSequence.spectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  (extSpectralSequence K S.filtered).1

/-- If `X ≅ H⟦s⟧` then `Ext^n(X, K) ≅ Ext^{n - s}(H, K)`: a shift of the first argument of an Ext
group moves into the degree.  The degree `m = n - s` is a parameter constrained by an equation,
so that it can be used in reduced form. -/
noncomputable def extOfGradedPieceShiftIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {X H K : DerivedCategory A} {s : ℤ} (e : X ≅ H⟦s⟧) (n m : ℤ) (hm : m + s = n) :
    AddCommGrpCat.of (DerivedCategory.Ext X K n) ≅
      AddCommGrpCat.of (DerivedCategory.Ext H K m) := by
  let adj : shiftFunctor (DerivedCategory A) s ⊣ shiftFunctor (DerivedCategory A) (-s) :=
    (shiftEquiv' (DerivedCategory A) s (-s) (add_neg_cancel s)).toAdjunction
  let eK : (K⟦n⟧)⟦-s⟧ ≅ K⟦m⟧ :=
    (shiftFunctorAdd' (DerivedCategory A) n (-s) m (by omega)).symm.app K
  exact (((Linear.homCongr ℤ e (Iso.refl _)).toAddEquiv).trans
    ((adj.homAddEquiv H (K⟦n⟧)).trans
      ((Linear.homCongr ℤ (Iso.refl _) eK).toAddEquiv))).toAddCommGrpIso

/-- **Stacks 0G20, the canonical truncation filtration.** Let `A` be a Grothendieck abelian
category and let `M, K ∈ D(A)`.  Every cochain complex representing `M`, filtered by
`F^p M^• = τ_{≤ -p} M^•`, gives a cohomological spectral sequence whose first page is
`E₁^{p,q} = Ext^{2p+q}(H^p(M), K)`. -/
@[stacks 0G20 "canonical_e1"]
noncomputable def canonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj M' ≅ M) :
    CanonicalExtSpectralSequence M K M' e where
  filtered := CochainComplex.canonicalTruncationFiltration M'
  underlyingIso := Iso.refl _
  stepIso _ := Iso.refl _
  stepIso_hom_comp p := by
    change (𝟙 _) ≫ M'.ιTruncLE (-p) = M'.ιTruncLE (-p) ≫ (𝟙 _)
    simp
  e₁Iso p q :=
    (extSpectralSequence K (CochainComplex.canonicalTruncationFiltration M')).2 p q ≪≫
      extOfGradedPieceShiftIso
        (CochainComplex.canonicalGradedPieceIso M' (-p) p (by omega) ≪≫
          (shiftFunctor (DerivedCategory A) (-p)).mapIso
            ((DerivedCategory.singleFunctor A 0).mapIso
              ((DerivedCategory.homologyFunctor A p).mapIso e)))
        (p + q) (2 * p + q) (by omega)

/-- **Stacks 0G20, the canonical truncation filtration.** Let `A` be a Grothendieck abelian
category and let `M, K ∈ D(A)`.  Every cochain complex representing `M`, filtered by
`F^p M^• = τ_{≤ -p} M^•`, gives a cohomological spectral sequence whose first page is
`E₁^{p,q} = Ext^{2p+q}(H^p(M), K)`.  This is `canonicalExtSpectralSequence` forgetting the
construction. -/
@[stacks 0G20 "canonical_e1"]
theorem exists_canonicalExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) (M' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj M' ≅ M) :
    Nonempty (CanonicalExtSpectralSequence M K M' e) :=
  ⟨canonicalExtSpectralSequence M K M' e⟩

/-- **Stacks 0G20, the brutal truncation filtration.** The Ext spectral sequence of the
filtration `F^p M^• = σ_{≥ p} M^•` of a cochain complex `M^•`, a cohomological spectral sequence
`(E_r, d_r)_{r ≥ 1}`.  It is definitionally the construction of Tag 0G1Z applied to that filtered
complex, so every page, differential and page-turning isomorphism is specified. -/
@[stacks 0G20 "stupid_e1"]
noncomputable def stupidExtSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  (extSpectralSequence K (CochainComplex.stupidTruncationFiltration M')).1

/-- **Stacks 0G20, the brutal truncation filtration.** The first page of the Ext spectral
sequence of the filtration `F^p M^• = σ_{≥ p} M^•` is `E₁^{p,q} = Ext^q(M^{-p}, K)`.

The index is `-p`, not `p`: the first page at `(p, q)` is `Ext^{p+q}` of the graded piece
`gr^{-p}M^• = M^{-p}[p]`, and the shift moves `p + q` down to `q`. -/
@[stacks 0G20 "stupid_e1"]
noncomputable def stupidExtSpectralSequenceE₁
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) (M' : CochainComplex A ℤ) (p q : ℤ) :
    ((stupidExtSpectralSequence K M').page 1).X (p, q) ≅
      AddCommGrpCat.of (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor A 0).obj (M'.X (-p))) K q) :=
  (extSpectralSequence K (CochainComplex.stupidTruncationFiltration M')).2 p q ≪≫
    extOfGradedPieceShiftIso (CochainComplex.stupidGradedPieceDerivedIso M' (-p))
      (p + q) q (by omega)

section RepresentativeIndependence

attribute [local instance] HasDerivedCategory.standard

/-- Any filtration of a representative satisfying the axioms of
`CanonicalExtSpectralSequence` is isomorphic, as a filtered complex, to the canonical truncation
filtration. -/
private noncomputable def canonicalFiltrationIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A] {M K : DerivedCategory A} {M' : CochainComplex A ℤ}
    {e : DerivedCategory.Q.obj M' ≅ M}
    (S : CanonicalExtSpectralSequence M K M' e) :
    S.filtered ≅ CochainComplex.canonicalTruncationFiltration M' :=
  FilteredObject.isoMk S.underlyingIso (fun p ↦ S.stepIso p.unop)
    (fun p ↦ S.stepIso_hom_comp p.unop)

/-- An isomorphism of filtered complexes induces an isomorphism of Ext spectral sequences. -/
private noncomputable def extSpectralSequenceIsoOfFilteredIso
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {F G : CochainComplex.Filtered A} (e : F ≅ G) :
    (extSpectralSequence K F).1 ≅ (extSpectralSequence K G).1 := by
  refine
    { hom := extSpectralSequence_map K e.inv
      inv := extSpectralSequence_map K e.hom
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← extSpectralSequence_map_comp, e.hom_inv_id, extSpectralSequence_map_id]
  · rw [← extSpectralSequence_map_comp, e.inv_hom_id, extSpectralSequence_map_id]

/-- Precomposition by a quasi-isomorphism is a quasi-isomorphism of Hom complexes into the chosen
K-injective representative. -/
private lemma precompCM_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A)
    {L L' : CochainComplex A ℤ} (f : L' ⟶ L) [QuasiIso f] :
    QuasiIso (Stacks.Cohomology.Locality.precompCM
      (L := (kInjectiveRepresentative A K).complex) f) := by
  let I := (kInjectiveRepresentative A K).complex
  let : I.IsKInjective := (kInjectiveRepresentative A K).isKInjective
  let eL := homologyToExt A K L
  let eL' := homologyToExt A K L'
  let eF : DerivedCategory.Q.obj L' ≅ DerivedCategory.Q.obj L :=
    asIso (DerivedCategory.Q.map f)
  let eExt (n : ℤ) : DerivedCategory.Ext (DerivedCategory.Q.obj L)
      K n ≃+ DerivedCategory.Ext (DerivedCategory.Q.obj L') K n :=
    homCongrAddEquiv eF.symm (Iso.refl (K⟦n⟧))
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmap : HomologicalComplex.homologyMap
      (Stacks.Cohomology.Locality.precompCM (L := I) f) n =
    ((eL n).trans ((eExt n).trans (eL' n).symm)).toAddCommGrpIso.hom := by
    ext x
    apply (eL' n).injective
    rw [homologyToExt_precomp]
    show DerivedCategory.Q.map f ≫ eL n x =
      eL' n ((eL' n).symm (eExt n (eL n x)))
    simp [eExt, eF, homCongrAddEquiv_apply]
  rw [hmap]
  infer_instance

/-- The identification of the graded pieces of the filtered Hom complex is natural in the
filtered complex. -/
private lemma filteredHomMap_grMap_naturality
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (K : DerivedCategory B) {F G : CochainComplex.Filtered B} (f : F ⟶ G) (p : ℤ) :
    (FilteredObject.gr p).map (filteredHomMap B K f) ≫
        (filteredHomComplexFiltrationGrIso B K F p).hom =
        (filteredHomComplexFiltrationGrIso B K G p).hom ≫
        Stacks.Cohomology.Locality.precompCM ((FilteredObject.gr (-p)).map f) := by
  have hcomp (H : CochainComplex.Filtered B) :
      FilteredObject.grMapπ (FilteredObject.succHom p) (filteredHomFilteredComplex B K H) ≫
      (filteredHomComplexFiltrationGrIso B K H p).hom =
      (filteredHomComplexFiltrationStepIso B K H p).hom ≫ Stacks.Cohomology.Locality.precompCM
        (FilteredObject.grMapι (FilteredObject.succHom (-p)) H) := by
    simpa only [filteredHomFilteredComplex, filteredHomComplexFiltration,
      filteredHomComplexFiltrationGrIso, filteredHomComplexFiltrationStepIso] using
      (filteredHomComplexData B K H).grIso_hom_comp p
  apply (cancel_epi (FilteredObject.grMapπ (FilteredObject.succHom p)
    (filteredHomFilteredComplex B K G))).1
  rw [← Category.assoc, FilteredObject.grMapπ_map]
  dsimp [filteredHomMap]
  have hn' := congrArg
    (fun g => g ≫ Stacks.Cohomology.Locality.precompCM ((FilteredObject.gr (-p)).map f))
    (hcomp G)
  rw [Category.assoc, hcomp F]
  apply Eq.trans ?_ hn'.symm
  show ((filteredHomComplexFiltrationStepIso B K G p).hom ≫
      Stacks.Cohomology.Locality.precompCM ((FilteredObject.quot (op (-p + 1))).map f) ≫
      (filteredHomComplexFiltrationStepIso B K F p).inv) ≫
      (filteredHomComplexFiltrationStepIso B K F p).hom ≫
      Stacks.Cohomology.Locality.precompCM (FilteredObject.grMapι (FilteredObject.succHom (-p)) F) =
        _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [precompCM_comp, FilteredObject.grMapι_map, ← precompCM_comp]
  rfl

/-- If a morphism of filtered complexes is a quasi-isomorphism on every graded piece, then so is
the induced morphism of filtered Hom complexes. -/
private lemma filteredHomMap_grMap_quasiIso
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (K : DerivedCategory B) {F G : CochainComplex.Filtered B} (f : F ⟶ G)
    (hf : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map f))
    (p : ℤ) :
    QuasiIso ((FilteredObject.gr p).map (filteredHomMap B K f)) := by
  refine (quasiIso_iff _).2 ?_
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let E := filteredHomComplexFiltrationGrIso B K F p
  let E' := filteredHomComplexFiltrationGrIso B K G p
  let : QuasiIso ((FilteredObject.gr (-p)).map f) := hf (-p)
  have hpreq := precompCM_quasiIso K ((FilteredObject.gr (-p)).map f)
  let : IsIso (HomologicalComplex.homologyMap
      (Stacks.Cohomology.Locality.precompCM ((FilteredObject.gr (-p)).map f)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hpreq.quasiIsoAt n)
  let : IsIso E.hom := E.isIso_hom
  let : IsIso E'.hom := E'.isIso_hom
  have hnat := filteredHomMap_grMap_naturality K f p
  have hnat' := congrArg (fun g => HomologicalComplex.homologyMap g n) hnat
  simp only [HomologicalComplex.homologyMap_comp] at hnat'
  have hcomp : IsIso
      (HomologicalComplex.homologyMap
        ((FilteredObject.gr p).map (filteredHomMap B K f)) n ≫
       HomologicalComplex.homologyMap E.hom n) := by
    rw [hnat']
    infer_instance
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap
      ((FilteredObject.gr p).map (filteredHomMap B K f)) n)
    (HomologicalComplex.homologyMap E.hom n)

/-- Shrinking Hom universes preserves the property of being a quasi-isomorphism on every graded
piece. -/
private lemma shrinkGrMap_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G)
    (hf : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map f)) (p : ℤ) :
    QuasiIso ((FilteredObject.gr p).map (shrinkFilteredComplexMap f)) := by
  let e := ShrinkHoms.equivalence.{w} A
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let : e.functor.Additive := by
    show (ShrinkHoms.functor A).Additive
    infer_instance
  let : eC.functor.IsEquivalence := eC.isEquivalence_functor
  let : eC.functor.PreservesZeroMorphisms := inferInstance
  let : eC.functor.Additive :=
    Functor.map_homogical_complex_additive e.functor (ComplexShape.up ℤ)
  let : e.functor.PreservesHomology := by infer_instance
  have : Limits.PreservesColimitsOfShape Limits.WalkingParallelPair eC.functor := by
    infer_instance
  let stepF := F.filtration.step (FilteredObject.succHom p)
  let stepG := G.filtration.step (FilteredObject.succHom p)
  let eF : eC.functor.obj ((FilteredObject.gr p).obj F) ≅
      (FilteredObject.gr p).obj (shrinkFilteredComplex F) :=
    Limits.PreservesCokernel.iso eC.functor stepF
  let eG : eC.functor.obj ((FilteredObject.gr p).obj G) ≅
      (FilteredObject.gr p).obj (shrinkFilteredComplex G) :=
    Limits.PreservesCokernel.iso eC.functor stepG
  let m := (FilteredObject.gr p).map f
  let m' := (FilteredObject.gr p).map (shrinkFilteredComplexMap f)
  let mE := eC.functor.map m
  have hstep : stepF ≫ f.natTrans.app (op p) =
      f.natTrans.app (op (p + 1)) ≫ stepG := by
    simp [stepF, stepG]
  have hnat : eF.hom ≫ m' = mE ≫ eG.hom := by
    show (Limits.PreservesCokernel.iso eC.functor stepF).hom ≫
        Limits.cokernel.map (eC.functor.map stepF) (eC.functor.map stepG)
          (eC.functor.map (f.natTrans.app (op (p + 1))))
          (eC.functor.map (f.natTrans.app (op p)))
          (by rw [← eC.functor.map_comp, hstep, eC.functor.map_comp]) =
      eC.functor.map (Limits.cokernel.map stepF stepG
        (f.natTrans.app (op (p + 1))) (f.natTrans.app (op p)) hstep) ≫
        (Limits.PreservesCokernel.iso eC.functor stepG).hom
    exact Limits.preserves_cokernel_iso_comp_cokernel_map
      eC.functor stepF stepG (f.natTrans.app (op (p + 1))) (f.natTrans.app (op p))
      hstep
  let : QuasiIso m := hf p
  let : QuasiIso mE :=
    HomologicalComplex.quasiIso_map_of_preservesHomology m e.functor
  exact quasiIso_of_arrow_mk_iso mE m' (Arrow.isoMk eF eG hnat)

/-- A morphism of filtered complexes which is a quasi-isomorphism on every graded piece induces
an isomorphism of the associated Ext spectral sequences. -/
private lemma extSpectralSequenceIsoOfFilteredQuasiIso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {F G : CochainComplex.Filtered A} (f : F ⟶ G)
    (hf : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map f)) :
    Nonempty ((extSpectralSequence K F).1 ≅ (extSpectralSequence K G).1) := by
  let φ := extSpectralSequence_map K f
  have hfirst : IsIso
      (φ.hom 1 (show (1 : ℤ) ≤ 1 from le_rfl)) := by
    have hgr (p : ℤ) : QuasiIso ((FilteredObject.gr p).map (extFilteredHomMap K f)) := by
      let e := ShrinkHoms.equivalence.{w} A
      let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
      let _std := HasDerivedCategory.standard (ShrinkHoms A)
      let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
      show QuasiIso ((FilteredObject.gr p).map
        (filteredHomMap (ShrinkHoms A) K' (shrinkFilteredComplexMap f)))
      exact filteredHomMap_grMap_quasiIso (B := ShrinkHoms A) K'
        (shrinkFilteredComplexMap f) (shrinkGrMap_quasiIso f hf) p
    have heq : φ.hom 1 (show (1 : ℤ) ≤ 1 from le_rfl) =
        (CochainComplex.filteredSpectralSequenceMap (extFilteredHomMap K f)).hom 1 (by omega) :=
      rfl
    rw [heq]
    exact FilteredComplexSpectralSequence.isIso_filteredSpectralSequenceMap_hom_one
      (extFilteredHomMap K f) hgr
  obtain ⟨g, hfg, hgf⟩ := (extSpectralSequence_map_isIso_of_isIso_firstPage K f hfirst).out
  exact ⟨⟨g, extSpectralSequence_map K f, hgf, hfg⟩⟩

/-- The canonical-truncation Ext spectral sequence is independent of the choice of complex
representing `M`, as a spectral sequence from `E₁` onward. -/
@[stacks 0G20 "representative_independence"]
theorem canonicalExtSpectralSequence_iso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{w} A] (M K : DerivedCategory A)
    (M₁ M₂ : CochainComplex A ℤ)
    (e₁ : DerivedCategory.Q.obj M₁ ≅ M) (e₂ : DerivedCategory.Q.obj M₂ ≅ M)
    (S₁ : CanonicalExtSpectralSequence M K M₁ e₁)
    (S₂ : CanonicalExtSpectralSequence M K M₂ e₂) :
    Nonempty (S₁.spectralSequence ≅ S₂.spectralSequence) := by
  let f : DerivedCategory.Q.obj M₁ ⟶ DerivedCategory.Q.obj M₂ := e₁.hom ≫ e₂.inv
  have hf : IsIso f := by
    dsimp [f]
    infer_instance
  obtain ⟨X, s, hs, g, hfac⟩ := DerivedCategory.right_fac f
  have hEq : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ f := by
    calc
      DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫
          inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by simp
      _ = DerivedCategory.Q.map s ≫ f := by rw [hfac]
  have hgIso : IsIso (DerivedCategory.Q.map g) := by
    rw [hEq]
    infer_instance
  have hsQI : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  have hgQI : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).1 hgIso
  obtain ⟨h₁⟩ := extSpectralSequenceIsoOfFilteredQuasiIso K
    (CochainComplex.truncationFiltrationMap s)
    (fun p => CochainComplex.truncationGradedMap_quasiIso s p)
  obtain ⟨h₂⟩ := extSpectralSequenceIsoOfFilteredQuasiIso K
    (CochainComplex.truncationFiltrationMap g)
    (fun p => CochainComplex.truncationGradedMap_quasiIso g p)
  let hS₁ := extSpectralSequenceIsoOfFilteredIso K (canonicalFiltrationIso S₁)
  let hS₂ := extSpectralSequenceIsoOfFilteredIso K (canonicalFiltrationIso S₂)
  exact ⟨by simpa [extSpectralSequence,
      CanonicalExtSpectralSequence.spectralSequence] using
      hS₁ ≪≫ h₁.symm ≪≫ h₂ ≪≫ hS₂.symm⟩

end RepresentativeIndependence

end Stacks.Injectives
