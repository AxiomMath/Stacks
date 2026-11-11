module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.Cotangent.DirectedColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of the cotangent complex passes to a filtered colimit

Let `A → B` be a filtered system of ring maps whose relative cotangent complexes all vanish in
the derived category. Then the colimit map `colim A → colim B` has vanishing cotangent complex
as well.

The proof is the one the cotangent complex's compatibility with directed colimits makes
available. A filtered category admits a cofinal functor from a directed partial order, so the
two colimits may be computed over a directed index set; the stages and the colimit then form a
system of commutative squares of ring maps to which
`CommAlgCat.isColimit_cotangentComplexAbCocone` applies, exhibiting `L_{Binf⁄Ainf}` as a
filtered colimit of the `L_{B i⁄A i}` in complexes of abelian groups. Vanishing in the derived
category is acyclicity, acyclicity is exactness in every degree, and a filtered colimit of
exact sequences of abelian groups is exact; so the colimit complex is acyclic, hence zero in
the derived category.

## Main results

* `CommAlgCat.cotangentComplex_isZero_of_filtered_colimit`: the cotangent complex of the
  colimit map vanishes.

## Implementation notes

Exactness is transported between the complex of `B`-modules and its complex of underlying
abelian groups by `CochainComplex.exactAt_forget₂_addCommGrp_iff`: the forgetful functor is
exact and faithful, so it both preserves and reflects exactness of a short complex. That is
what lets the colimit be taken in abelian groups, where the ring over which the modules live is
allowed to vary along the system.

The exactness of the colimit is obtained by viewing the degreewise short complexes of the
system as a short complex of functors `I ⥤ AddCommGrpCat` and applying `colim`, which is exact
on a filtered index category. Identifying the result with the degreewise short complex of the
colimit complex uses only that evaluation preserves the colimit, which it does because colimits
of complexes are computed degreewise.

## References

* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

/-- A complex of modules which vanishes in the derived category is exact in every degree. -/
theorem exactAt_of_isZero_Q {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : IsZero (DerivedCategory.Q.obj K)) : K.ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology K n).2
    (((DerivedCategory.homologyFunctor (ModuleCat R) n).map_isZero hK).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app K).symm)

/-- An acyclic complex of modules vanishes in the derived category. -/
theorem isZero_Q_obj_of_acyclic {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  let q : K ⟶ K := 0
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) q).2
      ⟨fun n => (quasiIsoAt_iff_exactAt q n (hK n)).2 (hK n)⟩
  refine (IsZero.iff_id_eq_zero _).2 ((cancel_mono (DerivedCategory.Q.map q)).1 ?_)
  simp [q]

/-- A complex of modules is exact in a degree exactly when its complex of underlying abelian
groups is: the forgetful functor is exact, and it is faithful, so it preserves and reflects
exactness of the short complex in that degree. -/
@[ega "III 7.1.2" "partial"]
theorem exactAt_forget₂_addCommGrp_iff {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt n ↔ K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff]
  exact ⟨fun hK => Functor.reflects_exact_of_faithful
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (K.sc n) hK,
    fun hK => hK.map (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})⟩

/-- The degreewise short complex of a diagram of complexes of abelian groups, read as a short
complex in the functor category. -/
noncomputable def functorShortComplex {I : Type u} [Category I]
    (D : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    ShortComplex (I ⥤ AddCommGrpCat.{u}) := by
  let c := ComplexShape.up ℤ
  let X₁ := D ⋙ HomologicalComplex.eval AddCommGrpCat c (c.prev n)
  let X₂ := D ⋙ HomologicalComplex.eval AddCommGrpCat c n
  let X₃ := D ⋙ HomologicalComplex.eval AddCommGrpCat c (c.next n)
  let f : X₁ ⟶ X₂ :=
    { app := fun i => (D.obj i).d (c.prev n) n
      naturality := by
        intro i j g
        simp [X₁, X₂, c] }
  let g : X₂ ⟶ X₃ :=
    { app := fun i => (D.obj i).d n (c.next n)
      naturality := by
        intro i j g
        simp [X₂, X₃, c] }
  exact ShortComplex.mk f g (by
    ext i x
    exact ConcreteCategory.congr_hom
      ((D.obj i).d_comp_d (c.prev n) n (c.next n)) x)

/-- Evaluating the degreewise short complex of a diagram at an index gives the degreewise short
complex of the complex sitting there. -/
noncomputable def functorShortComplexEvaluationIso {I : Type u} [Category I]
    (D : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) (i : I) :
    (functorShortComplex D n).map ((evaluation I AddCommGrpCat).obj i) ≅
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).obj
        (D.obj i) := by
  refine ShortComplex.isoMk
    (Iso.refl ((D.obj i).X ((ComplexShape.up ℤ).prev n)))
    (Iso.refl ((D.obj i).X n))
    (Iso.refl ((D.obj i).X ((ComplexShape.up ℤ).next n))) ?_ ?_ <;> ext x <;> rfl

/-- If every complex of the diagram is exact in degree `n`, the degreewise short complex of the
diagram is exact in the functor category. -/
theorem functorShortComplex_exact {I : Type u} [SmallCategory I]
    (D : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (n : ℤ) (hD : ∀ i, (D.obj i).ExactAt n) :
    (functorShortComplex D n).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  intro i
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1
      ((ShortComplex.exact_iff_of_iso (functorShortComplexEvaluationIso D n i)).mpr (hD i)))
    ((functorShortComplex D n).mapHomologyIso ((evaluation I AddCommGrpCat).obj i)).symm

end CochainComplex

namespace CommRingCat

/-- A colimit cocone on a diagram of commutative rings over a directed index set exhibits its
vertex as the elementwise directed colimit of the diagram. -/
theorem isDirectedColimitOfTypes_of_isColimit
    {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [PreservesColimit F (forget CommRingCat)]
    (c : Cocone F) (hc : IsColimit c) :
    IsDirectedColimitOfTypes (F := fun i => (F.obj i)) (X := ↑c.pt)
      (fun _ _ hij x => (F.map (homOfLE hij)).hom x)
      (fun i x => (c.ι.app i).hom x) := by
  refine ⟨fun i x => by simp, ?_, fun i j hij x => by simp,
    fun x => Concrete.isColimit_exists_rep F hc x, ?_⟩
  · intro i j k hij hjk x
    have hm : homOfLE hij ≫ homOfLE hjk = homOfLE (hij.trans hjk) :=
      Subsingleton.elim _ _
    have hcomp := congrArg (fun g => g.hom) (F.map_comp (homOfLE hij) (homOfLE hjk))
    rw [hm] at hcomp
    simpa [RingHom.comp_apply] using (congrArg (fun g => g x) hcomp).symm
  · intro i x y hxy
    obtain ⟨k, g, g', hg⟩ := Concrete.isColimit_exists_of_rep_eq F hc x y hxy
    refine ⟨k, leOfHom g, ?_⟩
    simpa [Subsingleton.elim g (homOfLE (leOfHom g)),
      Subsingleton.elim g' (homOfLE (leOfHom g))] using hg

end CommRingCat

namespace CommAlgCat

-- Keep the filtered-colimit instance from the proof imports from changing the
-- `colimit` elaboration in the statement.
attribute [-instance] CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits in
/-- **Stacks Project, Tag 08R2, filtered colimits.** If every map of a filtered system of ring
maps has vanishing relative cotangent complex, so has the map induced on the colimits. -/
@[stacks 08R2 "item (6) of the lemma, `A → B` a filtered colimit of ring maps for which the \
cotangent complex vanishes: a filtered system `f : A ⟶ B` of ring maps in `CommRingCat` with \
`L_{B_i/A_i} = 0` at every stage gives `L_{colim B/colim A} = 0`. NOTHING is carried; the \
source's route through Stacks 08S9 is followed (the cotangent complexes form a colimit \
cocone, `CommAlgCat.isColimit_cotangentComplexAbCocone`), after replacing the filtered index \
category by a cofinal directed order"]
theorem cotangentComplex_isZero_of_filtered_colimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A B : J ⥤ CommRingCat.{u}) (f : A ⟶ B)
    (h : ∀ i : J,
      letI : Algebra (A.obj i) (B.obj i) := (f.app i).hom.toAlgebra
      IsZero (DerivedCategory.Q.obj
        (cotangentComplex (A.obj i) (CommAlgCat.of (A.obj i) (B.obj i))))) :
    letI : Algebra (colimit A : CommRingCat.{u}) (colimit B : CommRingCat.{u}) :=
      (colim.map f).hom.toAlgebra
    IsZero (DerivedCategory.Q.obj
      (cotangentComplex (colimit A : CommRingCat.{u})
        (CommAlgCat.of (colimit A : CommRingCat.{u})
          (colimit B : CommRingCat.{u})))) := by
  classical
  obtain ⟨I, hIle, hIdir, hIne, F, hF⟩ := IsFiltered.exists_directed J
  let : PartialOrder I := hIle
  have : IsDirected I (· ≤ ·) := hIdir
  have : Nonempty I := hIne
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  have : F.Final := hF
  have hcol (G : J ⥤ CommRingCat.{u}) : IsColimit (Cocone.whisker F (colimit.cocone G)) :=
    (Functor.Final.isColimitWhiskerEquiv F (colimit.cocone G)).symm (colimit.isColimit G)
  let Bstage : ∀ i : I, CommAlgCat.{u} (A.obj (F.obj i)) := fun i =>
    letI := (f.app (F.obj i)).hom.toAlgebra
    CommAlgCat.of (A.obj (F.obj i)) (B.obj (F.obj i))
  let sq : ∀ ⦃i j : I⦄, i ≤ j →
      AlgebraSquare.{u, u, u} (A.obj (F.obj i)) (A.obj (F.obj j)) (Bstage i) (Bstage j) := by
    intro i j hij
    refine ⟨(A.map (F.map (homOfLE hij))).hom, (B.map (F.map (homOfLE hij))).hom, fun a => ?_⟩
    change (B.map (F.map (homOfLE hij))).hom ((f.app (F.obj i)).hom a) =
      (f.app (F.obj j)).hom ((A.map (F.map (homOfLE hij))).hom a)
    simp
  let : Algebra (colimit A : CommRingCat.{u}) (colimit B : CommRingCat.{u}) :=
    (colim.map f).hom.toAlgebra
  let cocone : ∀ i : I,
      AlgebraSquare.{u, u, u} (A.obj (F.obj i)) (colimit A : CommRingCat.{u}) (Bstage i)
        (CommAlgCat.of (colimit A : CommRingCat.{u}) (colimit B : CommRingCat.{u})) := by
    intro i
    let : Algebra (A.obj (F.obj i)) (B.obj (F.obj i)) :=
      (f.app (F.obj i)).hom.toAlgebra
    refine ⟨(colimit.ι A (F.obj i)).hom, (colimit.ι B (F.obj i)).hom, fun a => ?_⟩
    change (colimit.ι B (F.obj i)).hom ((f.app (F.obj i)).hom a) =
      (colim.map f).hom ((colimit.ι A (F.obj i)).hom a)
    simp
  have hA' : IsDirectedColimitOfTypes
      (fun i j hij a => (sq hij).base a) (fun i a => (cocone i).base a) := by
    simpa [sq, cocone, Bstage] using
      CommRingCat.isDirectedColimitOfTypes_of_isColimit (F ⋙ A) _ (hcol A)
  have hB' : IsDirectedColimitOfTypes
      (fun i j hij b => (sq hij).map b) (fun i b => (cocone i).map b) := by
    simpa [sq, cocone, Bstage] using
      CommRingCat.isDirectedColimitOfTypes_of_isColimit (F ⋙ B) _ (hcol B)
  have hstage : ∀ (i : I) (n : ℤ), (cotangentComplexAb (A.obj (F.obj i)) (Bstage i)).ExactAt n := by
    intro i n
    let : Algebra (A.obj (F.obj i)) (B.obj (F.obj i)) := (f.app (F.obj i)).hom.toAlgebra
    exact (CochainComplex.exactAt_forget₂_addCommGrp_iff _ n).2
      (CochainComplex.exactAt_of_isZero_Q _ n (h (F.obj i)))
  have hc := isColimit_cotangentComplexAbCocone sq cocone hA' hB'
  have hcAcyclic : (cotangentComplexAbCocone sq cocone hA' hB').pt.Acyclic := by
    intro n
    let S := CochainComplex.functorShortComplex (cotangentComplexAbFunctor sq cocone hA' hB') n
    let G : I ⥤ ShortComplex AddCommGrpCat.{u} :=
      (cotangentComplexAbFunctor sq cocone hA' hB') ⋙
        HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n
    have hS := (CochainComplex.functorShortComplex_exact
      (cotangentComplexAbFunctor sq cocone hA' hB') n (fun i => hstage i n)).map
        (colim : (I ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
    have hev (m : ℤ) := isColimitOfPreserves
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) m) hc
    have hcSc : IsColimit ((HomologicalComplex.shortComplexFunctor AddCommGrpCat
        (ComplexShape.up ℤ) n).mapCocone (cotangentComplexAbCocone sq cocone hA' hB')) :=
      ShortComplex.isColimitOfIsColimitπ _ (hev _) (hev _) (hev _)
    let cS : Cocone G :=
      { pt := S.map (colim : (I ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
        ι :=
          { app := fun i =>
              { τ₁ := (CochainComplex.functorShortComplexEvaluationIso
                  (cotangentComplexAbFunctor sq cocone hA' hB') n i).inv.τ₁ ≫ colimit.ι S.X₁ i
                τ₂ := (CochainComplex.functorShortComplexEvaluationIso
                  (cotangentComplexAbFunctor sq cocone hA' hB') n i).inv.τ₂ ≫ colimit.ι S.X₂ i
                τ₃ := (CochainComplex.functorShortComplexEvaluationIso
                  (cotangentComplexAbFunctor sq cocone hA' hB') n i).inv.τ₃ ≫ colimit.ι S.X₃ i
                comm₁₂ := by
                  change colimit.ι S.X₁ i ≫ colim.map S.f = S.f.app i ≫ colimit.ι S.X₂ i
                  rw [← colimMap_eq, ι_colimMap]
                comm₂₃ := by
                  change colimit.ι S.X₂ i ≫ colim.map S.g = S.g.app i ≫ colimit.ι S.X₃ i
                  rw [← colimMap_eq, ι_colimMap] }
            naturality := by
              intro i j g
              ext x
              · exact ConcreteCategory.congr_hom (colimit.w S.X₁ g) x
              · exact ConcreteCategory.congr_hom (colimit.w S.X₂ g) x
              · exact ConcreteCategory.congr_hom (colimit.w S.X₃ g) x } }
    have hcS : IsColimit cS :=
      ShortComplex.isColimitOfIsColimitπ cS (colimit.isColimit S.X₁) (colimit.isColimit S.X₂)
        (colimit.isColimit S.X₃)
    exact (ShortComplex.exact_iff_of_iso (hcS.coconePointUniqueUpToIso hcSc)).mp hS
  exact CochainComplex.isZero_Q_obj_of_acyclic _ (fun n =>
    (CochainComplex.exactAt_forget₂_addCommGrp_iff _ n).1 (hcAcyclic n))

end CommAlgCat

end
