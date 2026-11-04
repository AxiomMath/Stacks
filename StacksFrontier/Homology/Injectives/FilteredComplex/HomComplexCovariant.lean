module

public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.Injectives.FilteredComplex.KInjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# The covariant filtered Hom complex, and its cohomology as Ext groups

Let `A` be a Grothendieck abelian category, let `M` be an object of `D(A)` and let `K^•` be a
filtered complex of `A`.  Choosing a complex `M^•` representing `M` and a filtered K-injective
resolution `j : K^• ⟶ J^•` as in Tag 0BKI, the Hom complex `Hom^•(M^•, J^•)` carries the
decreasing filtration whose `p`-th step is `Hom^•(M^•, F^pJ^•)`.  The cohomology of the whole
complex, of every filtration step, and of every associated graded piece computes the
corresponding Ext group out of `M`.

This is the second-argument (covariant) half of Section 19.13, and the one used by Tag 0G1X.  Its
first-argument (contravariant) dual lives in
`StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex` and
`StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex` (Tag 0G1Z): there the
filtered complex sits in the *source* of the Hom complex and the induced maps are given by
*pre*composition, so none of those declarations applies here.

## Main definitions

* `Stacks.Injectives.FilteredHomComplexSetup` is the standing filtered-resolution situation: the
  filtered complex, the object of `D(A)`, a complex representing it, and the chosen filtered
  K-injective resolution together with all the properties Tag 0BKI supplies.
* `Stacks.Injectives.homComplex`, `Stacks.Injectives.filtrationHomComplex`,
  `Stacks.Injectives.gradedHomComplex` are the Hom complex, its filtration steps and its graded
  pieces; `Stacks.Injectives.underlyingDerived`, `Stacks.Injectives.filtrationDerived` and
  `Stacks.Injectives.gradedDerived` are the objects of `D(A)` they compute Ext into.
* `Stacks.Injectives.FilteredHomComplexRealization` records the filtration on the Hom complex as a
  filtered complex, and `Stacks.Injectives.filteredHomComplexRealization` realizes it.
* `Stacks.Injectives.extPostcomp` is the map on Ext induced by its second argument.
* `Stacks.Injectives.CohomologyExtComparison` packages compatible cohomology--Ext
  identifications.

## Main results

* `Stacks.Injectives.cohomologyExtComparison_nonempty` supplies the compatible
  cohomology--Ext identifications.

## Implementation notes

The degreewise covariant functoriality of a Hom complex is **not** rebuilt here: the morphism of
Hom complexes induced by postcomposition is `homComplexPostcomp` and its effect on cohomology
classes is `homologyAddEquiv_postcomp`, both already in the tree in the root namespace next to the
`cocyclePostcompAddMonoidHom`/`cohomologyClassPostcomp` of `StacksFrontier.Homology.HomComplex.RHom`
that they are about.  That is why this file imports
`StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf`, which is where
those two currently live.

The cohomology identifications are additive equivalences, which permits the locally small Hom
groups and the chosen derived category to live in different universes: the Grothendieck universe
`w'` and the derived-category universe `w` are independent throughout, as they are in the filtered
resolution theorem of Tag 0BKI.

The filtration is recorded together with isomorphisms to the Hom complexes named in the setup.
The transition and inclusion equations ensure that these isomorphisms identify the bundled
filtration with the prescribed maps.  The graded piece in degree `p` is the cokernel of
`F^{p+1} ⟶ F^p`.

## References

* [Stacks Project, Section 19.13](https://stacks.math.columbia.edu/tag/07D6)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w' w v u

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The collection of injectivity, K-injectivity, and quasi-isomorphism properties meant by a
filtered resolution "as in Tag 0BKI"; this is the conclusion of
`Stacks.Injectives.exists_filtered_quasiIso_isKInjective`. -/
public def IsFilteredKInjectiveResolution (K J : CochainComplex.Filtered A) (j : K ⟶ J) : Prop :=
  (∀ n : ℤ, Injective (J.X.X n)) ∧
    (∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n)) ∧
    (∀ p n : ℤ, Injective ((cokernel (J.filtration.ι.app (op p))).X n)) ∧
    (∀ (p p' : ℤ) (h : p ≤ p') n,
      Injective ((cokernel (J.filtration.diagram.map (opHomOfLE h))).X n)) ∧
    J.X.IsKInjective ∧
    (∀ p : ℤ, (J.filtration.obj (op p)).IsKInjective) ∧
    (∀ p : ℤ, (cokernel (J.filtration.ι.app (op p))).IsKInjective) ∧
    (∀ (p p' : ℤ) (h : p ≤ p'),
      (cokernel (J.filtration.diagram.map (opHomOfLE h))).IsKInjective) ∧
    QuasiIso j.hom ∧
    (∀ p : ℤ, QuasiIso (j.natTrans.app (op p))) ∧
    (∀ p : ℤ, QuasiIso (filtrationQuotientMap j p)) ∧
    ∀ (p p' : ℤ) (h : p ≤ p'),
      QuasiIso (filtrationSubquotientMap j h)

/-- The standing data for the covariant filtered Hom-complex construction. -/
public structure FilteredHomComplexSetup [IsGrothendieckAbelian.{w'} A]
    [HasDerivedCategory.{w} A] where
  /-- The filtered complex. -/
  K : CochainComplex.Filtered A
  /-- The object in the derived category occurring in the first Hom argument. -/
  M : DerivedCategory A
  /-- A complex representing `M`. -/
  MComplex : CochainComplex A ℤ
  /-- The specified identification of the chosen complex with `M`. -/
  representsM : DerivedCategory.Q.obj MComplex ≅ M
  /-- The chosen filtered K-injective resolution. -/
  J : CochainComplex.Filtered A
  /-- The filtered quasi-isomorphism into the resolution. -/
  j : K ⟶ J
  /-- The properties supplied by the filtered K-injective resolution theorem. -/
  resolution : IsFilteredKInjectiveResolution K J j

variable [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- The Hom complex `Hom^•(M^•, J^•)`. -/
public abbrev homComplex (S : FilteredHomComplexSetup (A := A)) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.HomComplex S.MComplex S.J.X

/-- Its `p`-th filtration step `Hom^•(M^•, F^pJ^•)`. -/
public abbrev filtrationHomComplex (S : FilteredHomComplexSetup (A := A)) (p : ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.HomComplex S.MComplex (S.J.filtration.obj (op p))

/-- The transition map `F^{p'}C ⟶ F^pC` for `p ≤ p'`. -/
public noncomputable def filtrationHomComplexMap (S : FilteredHomComplexSetup (A := A))
    {p p' : ℤ} (h : p ≤ p') :
    filtrationHomComplex S p' ⟶ filtrationHomComplex S p :=
  homComplexPostcomp S.MComplex (S.J.filtration.diagram.map (opHomOfLE h))

/-- The canonical map from the `p`-th filtration step to the full Hom complex. -/
public noncomputable def filtrationHomComplexι (S : FilteredHomComplexSetup (A := A)) (p : ℤ) :
    filtrationHomComplex S p ⟶ homComplex S :=
  homComplexPostcomp S.MComplex (S.J.filtration.ι.app (op p))

/-- The `p`-th associated graded Hom complex. -/
public noncomputable abbrev gradedHomComplex
    (S : FilteredHomComplexSetup (A := A)) (p : ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  cokernel (filtrationHomComplexMap S (show p ≤ p + 1 by omega))

/-- The derived-category object represented by the underlying filtered complex. -/
public noncomputable abbrev underlyingDerived (S : FilteredHomComplexSetup (A := A)) :
    DerivedCategory A :=
  DerivedCategory.Q.obj S.K.X

/-- The derived-category object represented by the `p`-th filtration step. -/
public noncomputable abbrev filtrationDerived (S : FilteredHomComplexSetup (A := A)) (p : ℤ) :
    DerivedCategory A :=
  DerivedCategory.Q.obj (S.K.filtration.obj (op p))

/-- The derived-category object represented by the `p`-th associated graded complex. -/
public noncomputable abbrev gradedDerived (S : FilteredHomComplexSetup (A := A)) (p : ℤ) :
    DerivedCategory A :=
  DerivedCategory.Q.obj
    (cokernel (S.K.filtration.diagram.map (opHomOfLE (show p ≤ p + 1 by omega))))

/-- Covariance of `Extⁿ(M,-)` in its second argument. -/
public noncomputable def extPostcomp (M : DerivedCategory A) (n : ℤ)
    {X Y : DerivedCategory A} (f : X ⟶ Y) :
    DerivedCategory.Ext M X n →+ DerivedCategory.Ext M Y n :=
  { toFun := fun g ↦ g ≫ (shiftFunctor (DerivedCategory A) n).map f
    map_zero' := by simp
    map_add' := by simp }

/-- A realization of the Hom complex and its prescribed filtration as a filtered complex. -/
public structure FilteredHomComplexRealization
    (S : FilteredHomComplexSetup (A := A)) where
  /-- The filtered Hom complex. -/
  complex : CochainComplex.Filtered AddCommGrpCat
  /-- Identification of its underlying complex with `Hom•(M•,J•)`. -/
  underlyingIso : complex.X ≅ homComplex S
  /-- Identification of its `p`-th step with `Hom•(M•,FᵖJ•)`. -/
  stepIso (p : ℤ) : complex.filtration.obj (op p) ≅ filtrationHomComplex S p
  /-- The step identifications respect all transition maps. -/
  stepIso_naturality {p p' : ℤ} (h : p ≤ p') :
    complex.filtration.diagram.map (opHomOfLE h) ≫ (stepIso p).hom =
      (stepIso p').hom ≫ filtrationHomComplexMap S h
  /-- The step identifications respect the inclusions into the underlying complex. -/
  stepIso_hom_comp (p : ℤ) :
    (stepIso p).hom ≫ filtrationHomComplexι S p =
      complex.filtration.ι.app (op p) ≫ underlyingIso.hom
  /-- Its associated graded complex is the prescribed cokernel of adjacent filtration steps. -/
  gradedIso (p : ℤ) :
    (FilteredObject.gr p).obj complex ≅ gradedHomComplex S p
  /-- The graded identification is the one induced by the step identifications. -/
  cokernel_π_comp_gradedIso_hom (p : ℤ) :
    cokernel.π
          (complex.filtration.diagram.map
            (opHomOfLE (show p ≤ p + 1 by omega))) ≫
        (gradedIso p).hom =
      (stepIso p).hom ≫
        cokernel.π (filtrationHomComplexMap S (show p ≤ p + 1 by omega))

/-- The Hom complexes in the setup form the specified filtered complex. -/
public noncomputable def filteredHomComplexRealization
    (S : FilteredHomComplexSetup (A := A)) :
    FilteredHomComplexRealization S := by
  have postcomp_apply (M : CochainComplex A ℤ)
      {J J' : CochainComplex A ℤ} (f : J ⟶ J') (n : ℤ)
      (z : CochainComplex.HomComplex.Cochain M J n) :
      (ConcreteCategory.hom ((homComplexPostcomp M f).f n)) z =
        z.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) := rfl
  have monoPostcomp (M : CochainComplex A ℤ)
      {J J' : CochainComplex A ℤ} (f : J ⟶ J') [Mono f] :
      Mono (homComplexPostcomp M f) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    apply CochainComplex.HomComplex.Cochain.ext x y
    intro p q hpq
    have h₁ := postcomp_apply M f n x
    have h₂ := postcomp_apply M f n y
    have hxy : x.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) =
        y.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) :=
      h₁.symm.trans (h.trans h₂)
    have h' := congrArg (fun z ↦ z.v p q hpq) hxy
    rw [CochainComplex.HomComplex.Cochain.comp_v x
        (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)
        p q q hpq (add_zero q),
      CochainComplex.HomComplex.Cochain.comp_v y
        (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)
        p q q hpq (add_zero q)] at h'
    apply (cancel_mono (f.f q)).1
    simpa only [CochainComplex.HomComplex.Cochain.ofHom_v] using h'
  have postcomp_comp (M : CochainComplex A ℤ)
      {J J' J'' : CochainComplex A ℤ} (f : J ⟶ J') (g : J' ⟶ J'') :
      homComplexPostcomp M f ≫ homComplexPostcomp M g = homComplexPostcomp M (f ≫ g) := by
    ext n z
    rw [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
    change CochainComplex.HomComplex.Cochain M J n at z
    have hf := postcomp_apply M f n z
    have hg := postcomp_apply M g n
      (z.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n))
    have hfg := postcomp_apply M (f ≫ g) n z
    rw [hf, hg, hfg, CochainComplex.HomComplex.Cochain.ofHom_comp]
    exact CochainComplex.HomComplex.Cochain.comp_assoc z
      (CochainComplex.HomComplex.Cochain.ofHom f)
      (CochainComplex.HomComplex.Cochain.ofHom g)
      (add_zero n) (zero_add 0) (by omega)
  let C : CochainComplex.Filtered AddCommGrpCat :=
    { X := homComplex S
      filtration := ⟨{
        obj := fun i ↦
          letI : Mono (filtrationHomComplexι S i.unop) :=
            monoPostcomp _ _
          MonoOver.mk (filtrationHomComplexι S i.unop)
        map := fun {i j} f ↦ MonoOver.homMk
          (filtrationHomComplexMap S (leOfHom f.unop)) (by
            change homComplexPostcomp S.MComplex
                (S.J.filtration.diagram.map (opHomOfLE (leOfHom f.unop))) ≫
                  homComplexPostcomp S.MComplex (S.J.filtration.ι.app j) =
                homComplexPostcomp S.MComplex (S.J.filtration.ι.app i)
            rw [postcomp_comp]
            congr 1
            exact S.J.filtration.diagram_map_comp_ι_app f)
        map_id := fun _ ↦ Subsingleton.elim _ _
        map_comp := fun _ _ ↦ Subsingleton.elim _ _ }⟩ }
  exact
    { complex := C
      underlyingIso := Iso.refl _
      stepIso := fun _ ↦ Iso.refl _
      stepIso_naturality := by intros; rfl
      stepIso_hom_comp := by intros; rfl
      gradedIso := fun _ ↦ Iso.refl _
      cokernel_π_comp_gradedIso_hom := by intros; rfl }

section

omit [IsGrothendieckAbelian.{w'} A]

private noncomputable def homologyExtOfIsKInjective
    (P I : CochainComplex A ℤ) [I.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex P I).homology n ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) n := by
  let q := DerivedCategory.quotientCompQhIso A
  let e : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj P := q.app P
  let e' : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I⟦n⟧)) ≅
      (DerivedCategory.Q.obj I)⟦n⟧ :=
    q.app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I
  exact (CochainComplex.HomComplex.homologyAddEquiv P I n).trans
    ((cohomologyClassRHomAddEquivOfIsKInjective P I n).trans
      (CategoryTheory.Linear.homCongr ℤ e e').toAddEquiv)

private lemma homologyExtOfIsKInjective_naturality
    (P : CochainComplex A ℤ) {I I' : CochainComplex A ℤ}
    [I.IsKInjective] [I'.IsKInjective] (f : I ⟶ I') (n : ℤ)
    (x : (CochainComplex.HomComplex P I).homology n) :
    homologyExtOfIsKInjective P I' n
        (HomologicalComplex.homologyMap (homComplexPostcomp P f) n x) =
      homologyExtOfIsKInjective P I n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  let q := DerivedCategory.quotientCompQhIso A
  change
    ((q.app P).inv ≫ DerivedCategory.Qh.map
        ((CochainComplex.HomComplex.homologyAddEquiv P I' n
          (HomologicalComplex.homologyMap (homComplexPostcomp P f) n x)).toHom)) ≫
        ((q.app (I'⟦n⟧)).hom ≫ (DerivedCategory.Q.commShiftIso n).hom.app I') =
      (((q.app P).inv ≫ DerivedCategory.Qh.map
          ((CochainComplex.HomComplex.homologyAddEquiv P I n x).toHom)) ≫
        ((q.app (I⟦n⟧)).hom ≫ (DerivedCategory.Q.commShiftIso n).hom.app I)) ≫
          (DerivedCategory.Q.map f)⟦n⟧'
  rw [← homologyAddEquiv_postcomp, toHom_cohomologyClassPostcomp, Functor.map_comp]
  simp only [Category.assoc]
  congr 2
  have h : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (f⟦n⟧')) ≫
        (q.app (I'⟦n⟧)).hom =
      (q.app (I⟦n⟧)).hom ≫ DerivedCategory.Q.map (f⟦n⟧') :=
    q.hom.naturality (f⟦n⟧')
  rw [← Category.assoc, h, Category.assoc, Functor.commShiftIso_hom_naturality]

private noncomputable def extCongrIso
    {X X' Y Y' : DerivedCategory A} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℤ) :
    DerivedCategory.Ext X Y n ≃+ DerivedCategory.Ext X' Y' n :=
  (CategoryTheory.Linear.homCongr ℤ eX
    ((shiftFunctor (DerivedCategory A) n).mapIso eY)).toAddEquiv

private noncomputable def homologyExtAlongQuasiIso
    (P K J : CochainComplex A ℤ) (f : K ⟶ J) [J.IsKInjective] [QuasiIso f]
    (M : DerivedCategory A) (representsM : DerivedCategory.Q.obj P ≅ M) (n : ℤ) :
    (CochainComplex.HomComplex P J).homology n ≃+
      DerivedCategory.Ext M (DerivedCategory.Q.obj K) n :=
  (homologyExtOfIsKInjective P J n).trans
    (extCongrIso representsM ((asIso (DerivedCategory.Q.map f)).symm) n)

private lemma homologyExtAlongQuasiIso_naturality
    (P : CochainComplex A ℤ) {K K' J J' : CochainComplex A ℤ}
    (f : K ⟶ J) (f' : K' ⟶ J') [J.IsKInjective] [J'.IsKInjective]
    [QuasiIso f] [QuasiIso f'] (a : K ⟶ K') (b : J ⟶ J')
    (h : a ≫ f' = f ≫ b)
    (M : DerivedCategory A) (e : DerivedCategory.Q.obj P ≅ M) (n : ℤ)
    (x : (CochainComplex.HomComplex P J).homology n) :
    homologyExtAlongQuasiIso P K' J' f' M e n
        (HomologicalComplex.homologyMap (homComplexPostcomp P b) n x) =
      homologyExtAlongQuasiIso P K J f M e n x ≫ (DerivedCategory.Q.map a)⟦n⟧' := by
  have hQ : DerivedCategory.Q.map b ≫ inv (DerivedCategory.Q.map f') =
      inv (DerivedCategory.Q.map f) ≫ DerivedCategory.Q.map a := by
    apply (cancel_epi (DerivedCategory.Q.map f)).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← Functor.map_comp, ← h, Functor.map_comp, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  show (e.inv ≫ homologyExtOfIsKInjective P J' n
      (HomologicalComplex.homologyMap (homComplexPostcomp P b) n x)) ≫
        (inv (DerivedCategory.Q.map f'))⟦n⟧' =
    ((e.inv ≫ homologyExtOfIsKInjective P J n x) ≫
      (inv (DerivedCategory.Q.map f))⟦n⟧') ≫ (DerivedCategory.Q.map a)⟦n⟧'
  rw [homologyExtOfIsKInjective_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hQ]

omit [HasDerivedCategory.{w} A] in
private lemma homComplexPostcomp_apply (P : CochainComplex A ℤ)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain P X n) :
    (homComplexPostcomp P f).f n z =
      z.comp (Cochain.ofHom f) (add_zero n) := rfl

omit [HasDerivedCategory.{w} A] in
private lemma homComplexPostcomp_comp (P : CochainComplex A ℤ)
    {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homComplexPostcomp P f ≫ homComplexPostcomp P g = homComplexPostcomp P (f ≫ g) := by
  ext n z
  rw [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  change CochainComplex.HomComplex.Cochain P X n at z
  rw [homComplexPostcomp_apply, homComplexPostcomp_apply, homComplexPostcomp_apply,
    CochainComplex.HomComplex.Cochain.ofHom_comp]
  exact CochainComplex.HomComplex.Cochain.comp_assoc z
    (Cochain.ofHom f) (Cochain.ofHom g) (add_zero n) (zero_add 0) (by omega)

omit [HasDerivedCategory.{w} A] in
private lemma homComplexPostcomp_zero (P : CochainComplex A ℤ)
    {X Y : CochainComplex A ℤ} :
    homComplexPostcomp P (0 : X ⟶ Y) = 0 := by
  ext n z
  have key (w : Cochain P X n) :
      w.comp (Cochain.ofHom (0 : X ⟶ Y)) (add_zero n) = 0 := by
    rw [Cochain.ofHom_zero, Cochain.comp_zero]
  exact ((homComplexPostcomp_apply P (0 : X ⟶ Y) n z).trans (key z)).trans rfl

private noncomputable def homComplexCokernelIso
    (P : CochainComplex A ℤ) {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f]
    (hX : ∀ q, Injective (X.X q)) :
    cokernel (homComplexPostcomp P f) ≅
      CochainComplex.HomComplex P (cokernel f) := by
  let π := cokernel.π f
  let S : ShortComplex (CochainComplex A ℤ) := ShortComplex.mk f π (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  let Sq (q : ℤ) := S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
  let sp (q : ℤ) : (Sq q).Splitting := by
    have : Mono (Sq q).f := by change Mono (f.f q); infer_instance
    have : Injective (Sq q).X₁ := by change Injective (X.X q); exact hX q
    exact ShortComplex.Splitting.ofExactOfRetraction (Sq q)
      (hS.map (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).exact
      (Injective.factorThru (𝟙 (Sq q).X₁) (Sq q).f) (Injective.comp_factorThru _ _)
      ((hS.map (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).epi_g)
  let r (q : ℤ) : Y.X q ⟶ X.X q := (sp q).r
  let t (q : ℤ) : (cokernel f).X q ⟶ Y.X q := (sp q).s
  let ιH := homComplexPostcomp P f
  let πH := homComplexPostcomp P π
  let HS : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
    ShortComplex.mk ιH πH (by
      calc
        ιH ≫ πH = homComplexPostcomp P (f ≫ π) := homComplexPostcomp_comp P f π
        _ = homComplexPostcomp P (0 : X ⟶ cokernel f) := by rw [cokernel.condition]
        _ = 0 := homComplexPostcomp_zero P)
  have hHS : HS.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact HS (fun n => by
      let Sr : AddCommGrpCat.of (CochainComplex.HomComplex.Cochain P Y n) ⟶
          AddCommGrpCat.of (CochainComplex.HomComplex.Cochain P X n) :=
        AddCommGrpCat.ofHom {
          toFun := fun z => Cochain.mk (fun p q hpq => z.v p q hpq ≫ r q)
          map_zero' := by apply Cochain.ext; intro p q hpq; simp
          map_add' := by intro z w; apply Cochain.ext; intro p q hpq; simp }
      let Ss : AddCommGrpCat.of (CochainComplex.HomComplex.Cochain P (cokernel f) n) ⟶
          AddCommGrpCat.of (CochainComplex.HomComplex.Cochain P Y n) :=
        AddCommGrpCat.ofHom {
          toFun := fun z => Cochain.mk (fun p q hpq => z.v p q hpq ≫ t q)
          map_zero' := by apply Cochain.ext; intro p q hpq; simp
          map_add' := by intro z w; apply Cochain.ext; intro p q hpq; simp }
      let Sn : ShortComplex AddCommGrpCat :=
        HS.map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n)
      -- The three splitting identities, each stated at the *raw* cochain type.  Stated
      -- about an element of `↑Sn.Xᵢ` instead, `simp` and `rw` match at `implicit`
      -- transparency, cannot see through `CochainComplex.HomComplex`, and fire on no
      -- `Cochain.comp` lemma at all.
      have key_f_r (w : Cochain P X n) :
          Cochain.mk (fun p q hpq =>
            (w.comp (Cochain.ofHom f) (add_zero n)).v p q hpq ≫ r q) = w := by
        apply Cochain.ext
        intro p q hpq
        have hfr : f.f q ≫ r q = 𝟙 _ := (sp q).f_r
        simp only [Cochain.mk_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
          Category.assoc, hfr, Category.comp_id]
      have key_s_g (w : Cochain P (cokernel f) n) :
          (Cochain.mk (fun p q hpq => w.v p q hpq ≫ t q)).comp
            (Cochain.ofHom π) (add_zero n) = w := by
        apply Cochain.ext
        intro p q hpq
        have hsg : t q ≫ π.f q = 𝟙 _ := (sp q).s_g
        simp only [Cochain.comp_zero_cochain_v, Cochain.mk_v, Cochain.ofHom_v,
          Category.assoc, hsg, Category.comp_id]
      have key_id (w : Cochain P Y n) :
          (Cochain.mk (fun p q hpq => w.v p q hpq ≫ r q)).comp
              (Cochain.ofHom f) (add_zero n) +
            Cochain.mk (fun p q hpq =>
              (w.comp (Cochain.ofHom π) (add_zero n)).v p q hpq ≫ t q) = w := by
        apply Cochain.ext
        intro p q hpq
        have hid : r q ≫ f.f q + π.f q ≫ t q = 𝟙 _ := (sp q).id
        simp only [Cochain.add_v, Cochain.mk_v, Cochain.comp_zero_cochain_v,
          Cochain.ofHom_v, Category.assoc, ← Preadditive.comp_add, hid, Category.comp_id]
      have hsplit : Sn.Splitting := {
        r := Sr
        s := Ss
        f_r := by ext z; exact key_f_r z
        s_g := by ext z; exact key_s_g z
        id := by ext z; exact key_id z }
      exact ShortComplex.ShortExact.mk' hsplit.exact hsplit.mono_f hsplit.epi_g)
  letI : Epi HS.g := hHS.epi_g
  exact (hHS.exact.gIsCokernel.coconePointUniqueUpToIso
    (cokernelIsCokernel ιH)).symm

end

/-- Compatible identifications of the cohomology of the filtered Hom complex, its
filtration steps, and its graded pieces with the corresponding Ext groups. -/
public structure CohomologyExtComparison
    (S : FilteredHomComplexSetup (A := A)) where
  /-- The cohomology of the underlying Hom complex computes `Extⁿ(M,K)`. -/
  homComplexIso (n : ℤ) :
    ((homComplex S).homology n : Type v) ≃+
      DerivedCategory.Ext S.M (underlyingDerived S) n
  /-- The cohomology of the `p`-th filtration step computes `Extⁿ(M,FᵖK)`. -/
  filtrationHomComplexIso (p n : ℤ) :
    ((filtrationHomComplex S p).homology n : Type v) ≃+
      DerivedCategory.Ext S.M (filtrationDerived S p) n
  /-- The cohomology of the `p`-th associated graded Hom complex computes
  `Extⁿ(M,grᵖK)`. -/
  gradedHomComplexIso (p n : ℤ) :
    ((gradedHomComplex S p).homology n : Type v) ≃+
      DerivedCategory.Ext S.M (gradedDerived S p) n
  /-- The identifications commute with the maps from a filtration step to the
  underlying complex. -/
  filtration_naturality (p n : ℤ)
      (x : (filtrationHomComplex S p).homology n) :
    homComplexIso n
        (HomologicalComplex.homologyMap (filtrationHomComplexι S p) n x) =
      extPostcomp S.M n (DerivedCategory.Q.map (S.K.filtration.ι.app (op p)))
        (filtrationHomComplexIso p n x)

/-- The filtered Hom complex admits compatible cohomology--Ext identifications. -/
public theorem cohomologyExtComparison_nonempty
    (S : FilteredHomComplexSetup (A := A)) :
    Nonempty (CohomologyExtComparison S) := by
  rcases S.resolution with
    ⟨hJ, hFil, hCok, hSub, hKJ, hKFil, hKCok, hKSub, hq, hqFil, hqCok, hqSub⟩
  have (p : ℤ) : (S.J.filtration.obj (op p)).IsKInjective := hKFil p
  have (p : ℤ) : QuasiIso (S.j.natTrans.app (op p)) := hqFil p
  let : S.J.X.IsKInjective := hKJ
  let : QuasiIso S.j.hom := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact homologyExtAlongQuasiIso S.MComplex S.K.X S.J.X S.j.hom S.M S.representsM n
  · intro p n
    exact homologyExtAlongQuasiIso S.MComplex (S.K.filtration.obj (op p))
      (S.J.filtration.obj (op p)) (S.j.natTrans.app (op p)) S.M S.representsM n
  · intro p n
    let h : p ≤ p + 1 := by omega
    let := hKSub p (p + 1) h
    let := hqSub p (p + 1) h
    let e := homComplexCokernelIso S.MComplex
      (S.J.filtration.diagram.map (opHomOfLE h)) (hFil (p + 1))
    exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso
      e).addCommGroupIsoToAddEquiv.trans
        (homologyExtAlongQuasiIso S.MComplex _ _
          (filtrationSubquotientMap S.j h) S.M S.representsM n)
  · intro p n x
    exact homologyExtAlongQuasiIso_naturality S.MComplex
      (S.j.natTrans.app (op p)) S.j.hom
      (S.K.filtration.ι.app (op p)) (S.J.filtration.ι.app (op p))
      (S.j.comm (op p)).symm S.M S.representsM n x

end Stacks.Injectives

end
