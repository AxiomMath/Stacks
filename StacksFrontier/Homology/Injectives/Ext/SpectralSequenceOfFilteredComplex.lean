module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Algebra.Homology.SpectralSequence.Basic
public import StacksCore.Algebra.Homology.SpectralSequence.EdgeStep
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Ext spectral sequence of a filtered complex

Let `A` be a Grothendieck abelian category, let `K` be an object of its derived category and let
`M` be a filtered cochain complex in `A`.  Filtering the Hom complex `Hom^•(M^•, I^•)` into a
K-injective representative `I` of `K` by the Hom complexes out of the quotients `M^•/F^{-p+1}M^•`
produces a filtered complex of abelian groups, and the spectral sequence of that filtered
complex is a cohomological spectral sequence with
`E_1^{p,q} = Ext^{p+q}(gr^{-p}M^•, K)`.

The construction is functorial: a morphism `f : M ⟶ N` of filtered complexes induces, by
precomposition, a morphism of the associated spectral sequences in the opposite direction, which
respects identities and composition; and a morphism which is an isomorphism on the first page is
an isomorphism of the whole spectral sequence, hence of every page, every differential and every
page-turning isomorphism.

## Main definitions

* `Stacks.Injectives.shrinkFilteredComplex`, `Stacks.Injectives.shrinkFilteredComplexMap`:
  transport of a filtered complex and of a filtered morphism along the equivalence which shrinks
  the Hom universe of `A`.
* `Stacks.Injectives.extFilteredHom`: the filtered Hom complex used in the construction, with its
  abelian groups placed in the derived Hom universe.
* `Stacks.Injectives.extFilteredHomSpectralSequence`: its spectral sequence, from page one on.
* `Stacks.Injectives.extSpectralSequence`: the Ext spectral sequence of `M` and `K`, bundled with
  the identification of its first page.
* `Stacks.Injectives.extSpectralSequence_map`: the contravariant comparison morphism.

## Main results

* `Stacks.Injectives.extSpectralSequence_fst`: the spectral sequence is, as a whole, the spectral
  sequence of the filtered Hom complex, so every page and page transition is specified.
* `Stacks.Injectives.extSpectralSequence_map_id`,
  `Stacks.Injectives.extSpectralSequence_map_comp`: functoriality of the comparison morphism.
* `Stacks.Injectives.extSpectralSequence_map_isIso_of_isIso_firstPage`: a first-page
  isomorphism propagates to the entire spectral sequence.

## Implementation notes

The assertion that the differential on page `r` has bidegree `(r, -r + 1)` is built into
`CohomologicalSpectralSequence`, so it is not restated.  A complex represents the object obtained
by applying the localization functor `DerivedCategory.Q`; this is used explicitly for each
associated graded piece.  `ShrinkHoms` moves the abelian groups of the Hom complex into the
derived Hom universe without forcing the object and morphism universes of `A` to be related.

## References

* [Stacks Project, Tag 0G1Z](https://stacks.math.columbia.edu/tag/0G1Z)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace Stacks.Injectives

/-- An additive equivalence which commutes with the shift induces an isomorphism of the additive
groups of shifted homomorphisms. -/
noncomputable def shiftedHomMapAddEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D)
    [G.Additive] [G.IsEquivalence] [G.CommShift ℤ]
    (X Y : C) (n : ℤ) : ShiftedHom X Y n ≃+ ShiftedHom (G.obj X) (G.obj Y) n := by
  let h : ShiftedHom X Y n →+ ShiftedHom (G.obj X) (G.obj Y) n :=
    { toFun := fun f => f.map G
      map_zero' := by simp
      map_add' := by simp }
  refine AddEquiv.ofBijective h ⟨?_, ?_⟩
  · intro f g hfg
    apply G.map_injective
    have hh : G.map f ≫ (G.commShiftIso n).hom.app Y =
        G.map g ≫ (G.commShiftIso n).hom.app Y := hfg
    simpa using (cancel_mono ((G.commShiftIso n).hom.app Y)).mp hh
  · intro f
    obtain ⟨g, hg⟩ := G.map_surjective (f ≫ (G.commShiftIso n).inv.app Y)
    refine ⟨g, ?_⟩
    change G.map g ≫ (G.commShiftIso n).hom.app Y = f
    simp [hg, Category.assoc]

/-- Conjugating by isomorphisms of the source and the target is an isomorphism of the additive
groups of shifted homomorphisms. -/
noncomputable def shiftedHomIsoAddEquiv
    {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℤ) :
    ShiftedHom X Y n ≃+ ShiftedHom X' Y' n := by
  let h : ShiftedHom X Y n →+ ShiftedHom X' Y' n :=
    { toFun := fun f => eX.inv ≫ f ≫ (eY.hom)⟦n⟧'
      map_zero' := by simp
      map_add' := by simp }
  refine AddEquiv.ofBijective h ⟨?_, ?_⟩
  · intro f g hfg
    simpa [h, Category.assoc] using congrArg (fun z => eX.hom ≫ z ≫ (eY.inv)⟦n⟧') hfg
  · intro f
    refine ⟨eX.hom ≫ f ≫ (eY.inv)⟦n⟧', ?_⟩
    simp [h, Category.assoc]

/-- Transport a filtered complex along the equivalence that shrinks its Hom universe. -/
noncomputable def shrinkFilteredComplex
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (M : CochainComplex.Filtered A) : CochainComplex.Filtered.{w} (ShrinkHoms A) :=
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  { X := eC.functor.obj M.X
    filtration := ⟨M.filtration.toMonoOver ⋙ (MonoOver.congr M.X eC).functor⟩ }

/-- Transport a filtered morphism along the same equivalence. -/
noncomputable def shrinkFilteredComplexMap
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    {M N : CochainComplex.Filtered A} (f : M ⟶ N) :
    shrinkFilteredComplex.{w} M ⟶ shrinkFilteredComplex.{w} N :=
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  FilteredObject.homMk (eC.functor.map f.hom)
    (fun i => eC.functor.map (f.natTrans.app i)) (fun i => by
      change eC.functor.map (f.natTrans.app i) ≫ eC.functor.map _ =
        eC.functor.map _ ≫ eC.functor.map f.hom
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg eC.functor.map (f.comm i))

section

attribute [local instance] HasDerivedCategory.standard

/-- Precomposition by a filtered morphism respects the quotient Hom filtrations. -/
noncomputable def filteredHomMap
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (K : DerivedCategory A) {M N : CochainComplex.Filtered A} (f : M ⟶ N) :
    filteredHomFilteredComplex A K N ⟶ filteredHomFilteredComplex A K M := by
  let eM := filteredHomComplexFiltrationStepIso A K M
  let eN := filteredHomComplexFiltrationStepIso A K N
  refine FilteredObject.homMk (Stacks.Cohomology.Locality.precompCM f.hom)
    (fun i => (eN i.unop).hom ≫
      Stacks.Cohomology.Locality.precompCM ((FilteredObject.quot (op (-i.unop + 1))).map f) ≫
        (eM i.unop).inv) ?_
  intro i
  have hM := (filteredHomComplexData A K M).stepIso_hom_comp i.unop
  have hN := (filteredHomComplexData A K N).stepIso_hom_comp i.unop
  change (eM i.unop).hom ≫ _ =
    (filteredHomFilteredComplex A K M).filtration.ι.app i at hM
  change (eN i.unop).hom ≫ _ =
    (filteredHomFilteredComplex A K N).filtration.ι.app i at hN
  change _ = _ ≫ Stacks.Cohomology.Locality.precompCM f.hom
  rw [← hM, ← hN]
  dsimp only [filteredHomFilteredComplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [filteredHomComplexQuotientPrecomp]
  rw [precompCM_comp, precompCM_comp, FilteredObject.quotπ_map]

end

/-- The filtered Hom complex used in the proof of Tag 0G1Z. Its filtration in degree `p`
is Hom out of the quotient at index `-p + 1`. Shrinking Hom sets allows arbitrary independent
object, morphism, and derived Hom universes. -/
noncomputable def extFilteredHom
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    CochainComplex.Filtered AddCommGrpCat.{w} :=
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  letI := HasDerivedCategory.standard (ShrinkHoms A)
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  filteredHomFilteredComplex (ShrinkHoms A) K' (shrinkFilteredComplex M)

/-- The contravariant map of the actual filtered Hom complexes. -/
noncomputable def extFilteredHomMap
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N : CochainComplex.Filtered A} (f : M ⟶ N) :
    extFilteredHom K N ⟶ extFilteredHom K M :=
  let eC := (ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)
  letI := HasDerivedCategory.standard (ShrinkHoms A)
  let K' := DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  filteredHomMap (ShrinkHoms A) K' (shrinkFilteredComplexMap f)

/-- Precomposition by the identity is the identity filtered Hom map. -/
theorem extFilteredHomMap_id
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    extFilteredHomMap K (𝟙 M) = 𝟙 (extFilteredHom K M) := by
  apply FilteredObject.hom_ext
  dsimp only [extFilteredHomMap, filteredHomMap]
  change Stacks.Cohomology.Locality.precompCM
    (((ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)).functor.map
      (𝟙 M.X)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  exact precompCM_id

/-- Filtered Hom maps reverse composition. -/
theorem extFilteredHomMap_comp
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N P : CochainComplex.Filtered A} (f : M ⟶ N) (g : N ⟶ P) :
    extFilteredHomMap K (f ≫ g) = extFilteredHomMap K g ≫ extFilteredHomMap K f := by
  apply FilteredObject.hom_ext
  dsimp only [extFilteredHomMap, filteredHomMap]
  change Stacks.Cohomology.Locality.precompCM
    (((ShrinkHoms.equivalence.{w} A).mapHomologicalComplex (ComplexShape.up ℤ)).functor.map
      (f.hom ≫ g.hom)) = _
  rw [Functor.map_comp, ← precompCM_comp]
  rfl

/-- The full spectral sequence of the filtered Hom complex, starting at page one. The
restriction retains the page complexes and the page-turning isomorphisms of Tag 012M. -/
noncomputable def extFilteredHomSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  let E := CochainComplex.filteredSpectralSequence (extFilteredHom K M)
  { page := fun r hr => E.page r (by omega)
    iso := fun r r' pq hrr' hr => E.iso r r' pq hrr' (by omega) }

/-- **Stacks 0G1Z.** The Ext spectral sequence associated to a filtered complex `M`, bundled with
the identifications `E₁^{p,q} = Ext^{p+q}(gr^{-p} M, K)`.  Its differential on page `r` has
bidegree `(r, -r + 1)` by the definition of `CohomologicalSpectralSequence`. -/
@[stacks 0G1Z "spectral_sequence"]
noncomputable def extSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    Σ E : CohomologicalSpectralSequence AddCommGrpCat.{w} 1,
      ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ AddCommGrpCat.of
          (DerivedCategory.Ext
            (DerivedCategory.Q.obj
              ((FilteredObject.gr (C := (CochainComplex A ℤ)) (-p)).obj M))
            K (p + q)) := by
  let e := ShrinkHoms.equivalence.{w} A
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  letI := HasDerivedCategory.standard (ShrinkHoms A)
  let K' : DerivedCategory (ShrinkHoms A) :=
    DerivedCategory.Q.obj (eC.functor.obj (DerivedCategory.Q.objPreimage K))
  let M' : CochainComplex.Filtered (ShrinkHoms A) := shrinkFilteredComplex M
  let N := filteredHomFilteredComplex (ShrinkHoms A) K' M'
  let F : ℤ → ∀ n : ℤ, Subobject (N.X.X n) :=
    fun p n => Subobject.mk ((N.filtration.ι.app (op p)).f n)
  have hF : ∀ p n : ℤ,
      F p n = Subobject.mk ((N.filtration.ι.app (op p)).f n) :=
    fun _ _ => rfl
  let E := extFilteredHomSpectralSequence K M
  refine ⟨E, fun p q => ?_⟩
  let h := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage N F hF
    (fun _ _ n hp => F_antitone N F hF hp n)
  let e₁ := ((Classical.choose_spec h).2.2 p q (p + q) rfl).some
  let egr := HomologicalComplex.homologyMapIso
    (filteredHomComplexFiltrationGrIso (ShrinkHoms A) K' M' p) (p + q)
  letI : e.functor.Additive := by
    change (ShrinkHoms.functor A).Additive
    infer_instance
  letI := eC.isEquivalence_functor
  let eGr : ((FilteredObject.gr (-p)).obj M') ≅
      eC.functor.obj ((FilteredObject.gr (-p)).obj M) :=
    (PreservesCokernel.iso eC.functor
      (M.filtration.step (FilteredObject.succHom (-p)))).symm
  let ext := filteredHomComplexHomologyAddEquivExt (ShrinkHoms A) K'
    (FilteredObject.ofTop (((FilteredObject.gr (-p)).obj M'))) (p + q)
  let G := e.functor.mapDerivedCategory
  letI : G.IsEquivalence := mapDerivedCategory_isEquivalence e.functor
  let xIso : G.obj (DerivedCategory.Q.obj ((FilteredObject.gr (-p)).obj M)) ≅
      DerivedCategory.Q.obj ((FilteredObject.gr (-p)).obj M') :=
    e.functor.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eGr.symm
  let kIso : G.obj K ≅ K' :=
    G.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      e.functor.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
  let bridge : DerivedCategory.Ext (DerivedCategory.Q.obj
        ((FilteredObject.gr (-p)).obj M')) K' (p + q) ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj
        ((FilteredObject.gr (-p)).obj M)) K (p + q) :=
    ((shiftedHomMapAddEquiv G _ _ (p + q)).trans
      (shiftedHomIsoAddEquiv xIso kIso (p + q))).symm
  exact e₁ ≪≫ egr ≪≫ (ext.trans bridge).toAddCommGrpIso

/-- The comparison with the filtered Hom construction is equality of full spectral sequences;
it therefore identifies every page, differential, and page-turning isomorphism. -/
theorem extSpectralSequence_fst
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    (extSpectralSequence K M).1 = extFilteredHomSpectralSequence K M := rfl

/-- The natural contravariant morphism of Ext spectral sequences. It is induced by
precomposition on filtered Hom complexes and commutes with all differentials and transitions. -/
noncomputable def extSpectralSequence_map
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N : CochainComplex.Filtered A} (f : M ⟶ N) :
    (extSpectralSequence K N).1 ⟶ (extSpectralSequence K M).1 :=
  let φ := CochainComplex.filteredSpectralSequenceMap (extFilteredHomMap K f)
  { hom := fun r hr => φ.hom r (by omega)
    comm := fun r r' pq hrr' hr => φ.comm r r' pq hrr' (by omega) }

/-- The natural Ext comparison preserves identities. -/
theorem extSpectralSequence_map_id
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    extSpectralSequence_map K (𝟙 M) = 𝟙 (extSpectralSequence K M).1 := by
  apply SpectralSequence.hom_ext
  intro r hr
  change (CochainComplex.filteredSpectralSequenceMap (extFilteredHomMap K (𝟙 M))).hom
    r (by omega) = 𝟙 _
  rw [extFilteredHomMap_id, CochainComplex.filteredSpectralSequenceMap_id]
  rfl

/-- The natural Ext comparison reverses composition. -/
theorem extSpectralSequence_map_comp
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N P : CochainComplex.Filtered A} (f : M ⟶ N) (g : N ⟶ P) :
    extSpectralSequence_map K (f ≫ g) = extSpectralSequence_map K g ≫
      extSpectralSequence_map K f := by
  apply SpectralSequence.hom_ext
  intro r hr
  change (CochainComplex.filteredSpectralSequenceMap (extFilteredHomMap K (f ≫ g))).hom
    r (by omega) = _
  rw [extFilteredHomMap_comp, CochainComplex.filteredSpectralSequenceMap_comp]
  rfl

/-- An isomorphism on the first page of the natural comparison is an isomorphism on every
later page, with the transition compatibility already part of `extSpectralSequence_map`. -/
theorem extSpectralSequence_map_isIso_hom_of_isIso_firstPage
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N : CochainComplex.Filtered A} (f : M ⟶ N)
    (h : IsIso ((extSpectralSequence_map K f).hom 1)) (r : ℤ) (hr : 1 ≤ r) :
    IsIso ((extSpectralSequence_map K f).hom r hr) :=
  SpectralSequence.isIso_hom_of_GE (extSpectralSequence_map K f) 1 r hr h

/-- A first-page comparison isomorphism gives an isomorphism of the entire spectral sequence,
including its differentials and page-turning isomorphisms. -/
theorem extSpectralSequence_map_isIso_of_isIso_firstPage
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) {M N : CochainComplex.Filtered A} (f : M ⟶ N)
    (h : IsIso ((extSpectralSequence_map K f).hom 1)) :
    IsIso (extSpectralSequence_map K f) := by
  let φ := extSpectralSequence_map K f
  have hφ (r : ℤ) (hr : 1 ≤ r) : IsIso (φ.hom r hr) :=
    extSpectralSequence_map_isIso_hom_of_isIso_firstPage K f h r hr
  let ψ : (extSpectralSequence K M).1 ⟶ (extSpectralSequence K N).1 :=
    { hom := fun r hr => inv (φ.hom r hr)
      comm := by
        intro r r' pq hrr' hr
        have hr' : 1 ≤ r' := by omega
        have := hφ r hr
        have := hφ r' hr'
        apply (cancel_mono ((φ.hom r' hr').f pq)).1
        simp only [Category.assoc, HomologicalComplex.Hom.inv_f_apply, IsIso.inv_hom_id,
          Category.comp_id]
        rw [← φ.comm r r' pq hrr' hr]
        simp only [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          IsIso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp] }
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply SpectralSequence.hom_ext
    intro r hr
    have := hφ r hr
    exact IsIso.hom_inv_id (φ.hom r hr)
  · apply SpectralSequence.hom_ext
    intro r hr
    have := hφ r hr
    exact IsIso.inv_hom_id (φ.hom r hr)

end Stacks.Injectives
