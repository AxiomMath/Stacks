module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalLiftingThroughCohomologyIsomorphisms

/-!
# Finiteness of the top cohomology of a pseudo-coherent complex on a ringed site

Let `(C, O)` be a ringed site and let `K` be an `m`-pseudo-coherent object of the derived
category of `O`-modules. Stacks 08FX says two things about the highest degree in which the
cohomology of `K` can be nonzero: if the cohomology vanishes above `m`, then `H^m(K)` is of
finite type; and if it vanishes above `m + 1`, then `H^{m+1}(K)` is finitely presented.

Both are local statements, and locally `K` is computed by a strictly perfect complex `P`
concentrated in degrees at most the degree in question, by Stacks 08FT bounded above (which
is `exists_local_strictlyPerfect_approximation_boundedAbove`). For the finite-type half, `P`
has nothing one degree up, so its top cohomology is a quotient of its top term, a direct
summand of a finite free module. For the finite-presentation half, the top cohomology of `P`
is moreover the cokernel of the last differential, whose source and target are both direct
summands of finite free modules; such a cokernel has a finite presentation.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteType_homology`: Stacks 08FX, the finite-type half.
* `AlgebraicGeometry.RingedSite.isFinitePresentation_homology`: Stacks 08FX, the
  finite-presentation half.

## Implementation notes

The universes are pinned to `RingedSite.{u, u, 0}` and `SheafOfModules.{0}` for the reason
recorded in the implementation notes of `LocalNullHomotopyOfStrictlyPerfect`, where Stacks
08FP is proved: the predicate carrying Stacks 08FL admits only ring universe = module
universe = 0, because it is phrased through `SheafOfModules.free (Fin n)`. In particular the
index sets of the finite free modules are already `Fin n : Type 0`, so no universe lifting of
the index is needed.

Exactness of restriction to a slice, which is what makes the comparison of cohomology with
its restriction available, is the `Stacks.SheafOfModules.LocalCokernel` material.

`finitePresentation_cokernel_of_retracts` is the one piece of local input for the second
half: the cokernel of a map between two direct summands of finite free modules has a finite
presentation. Its generators are the finite free module containing the target; its relations
are the finite free module containing the source, together with the complementary idempotent
of the target, which is what cuts the free cover down to the summand.

## References

* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v d

namespace AlgebraicGeometry.RingedSite

/-- The index set of the local strictly perfect approximations produced by Stacks 08FT: the
objects of the site carrying one of them. -/
private def approximationIndex (X : RingedSite.{u, u, 0}) (S : ∀ U : X.C, Presieve U) :=
  {V : X.C // ∃ U : X.C, ∃ f : V ⟶ U, S U f}

/-- **Stacks 08FX**, finite type of the top cohomology. The degree-`m` cohomology of an
`m`-pseudo-coherent object of the derived category whose higher cohomology vanishes is of
finite type. -/
@[stacks 08FX "finite_type_top_cohomology"]
theorem isFiniteType_homology (X : RingedSite.{u, u, 0})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
    [HasSheafify X.J AddCommGrpCat.{0}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{0} AddCommGrpCat.{0})]
    [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hK : X.IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).obj K).IsFiniteType := by
  classical
  let A := SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let H := (DerivedCategory.homologyFunctor A m).obj K
  obtain ⟨E, hEK, hlocal⟩ :=
    exists_local_strictlyPerfect_approximation_boundedAbove X K m m le_rfl hK hvanish
  let S : ∀ U : X.C, Presieve U := fun U => Classical.choose (hlocal U)
  have hScov (U : X.C) : Sieve.generate (S U) ∈ X.J U := (Classical.choose_spec (hlocal U)).1
  let I := approximationIndex X S
  let V (i : I) := i.1
  have hgen : ∀ i : I, ∃ σ : (H.over (V i)).GeneratingSections, σ.IsFiniteType := by
    intro i
    let W := i.1
    obtain ⟨U, f, hf⟩ := i.2
    obtain ⟨P, hP, hbound, α, _, hepi⟩ := (Classical.choose_spec (hlocal U)).2 f hf
    let F := SheafOfModules.overFunctor R₀ W
    have : PreservesFiniteLimits F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
    have : Functor.PreservesEpimorphisms F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms W
    have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
    let hEhom : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology m ≅
        F.obj (E.homology m) := (E.sc m).mapHomologyIso F
    let hFac := (DerivedCategory.homologyFunctorFactors A m).app E
    let eK : (DerivedCategory.homologyFunctor A m).obj (DerivedCategory.Q.obj E) ≅ H :=
      (DerivedCategory.homologyFunctor A m).mapIso (Classical.choice hEK)
    let hTarget : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology m ≅
        F.obj H := hEhom ≪≫ F.mapIso hFac.symm ≪≫ F.mapIso eK
    obtain ⟨n, iP, rP, hir⟩ :=
      (isDirectSummandOfFiniteFree_iff_free _ _).mp (hP.termDirectSummand m)
    have hd : P.d m (m + 1) = 0 := (hbound (m + 1) (by omega)).eq_of_tgt _ _
    have : IsIso (P.iCycles m) := P.isIso_iCycles m (m + 1) (by simp) hd
    let e := asIso (P.iCycles m)
    let fTerm : P.X m ⟶ P.homology m := e.inv ≫ P.homologyπ m
    have : IsSplitEpi rP := IsSplitEpi.mk' ⟨iP, hir⟩
    have : Epi (HomologicalComplex.homologyMap α m) := hepi
    let fFree : SheafOfModules.free (R := R₀.over W) (ULift.{0} (Fin n)) ⟶ H.over W :=
      rP ≫ fTerm ≫ HomologicalComplex.homologyMap α m ≫ hTarget.hom
    have : Epi fFree := by
      dsimp [fFree]
      infer_instance
    exact ⟨(SheafOfModules.free.generatingSections
        (R := R₀.over W) (ULift.{0} (Fin n))).ofEpi fFree,
      ⟨inferInstanceAs (Finite (ULift.{0} (Fin n)))⟩⟩
  exact ⟨{ I := I
           X := V
           coversTop := fun U => X.J.superset_covering
             ((Sieve.generate_le_iff _ _).2 fun Z f hf => ⟨⟨Z, U, f, hf⟩, ⟨𝟙 Z⟩⟩) (hScov U)
           generators := fun i => Classical.choose (hgen i) },
    ⟨fun i => Classical.choose_spec (hgen i)⟩⟩

/-- The cokernel of a map between two direct summands of finite free sheaves of modules has a
finite presentation: the target's free cover gives the generators, and the source's free cover
together with the complementary idempotent of the target gives the relations. -/
private theorem finitePresentation_cokernel_of_retracts
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [HasSheafify J AddCommGrpCat.{0}]
    {A B : SheafOfModules.{0} R} {I K : Type 0} [Finite I] [Finite K]
    (a : Retract A (SheafOfModules.free (R := R) K))
    (b : Retract B (SheafOfModules.free (R := R) I))
    (f : A ⟶ B) : ∃ p : (cokernel f).Presentation, p.IsFinite := by
  let h₁ : SheafOfModules.free (R := R) K ⟶ SheafOfModules.free (R := R) I :=
    a.r ≫ f ≫ b.i
  let h₂ : SheafOfModules.free (R := R) I ⟶ SheafOfModules.free (R := R) I :=
    𝟙 _ - b.r ≫ b.i
  let hc : SheafOfModules.free (R := R) K ⨿ SheafOfModules.free (R := R) I ⟶
      SheafOfModules.free (R := R) I := coprod.desc h₁ h₂
  let h : SheafOfModules.free (R := R) (K ⊕ I) ⟶ SheafOfModules.free (R := R) I :=
    (SheafOfModules.freeSumIso (R := R) K I).inv ≫ hc
  let g : SheafOfModules.free (R := R) I ⟶ cokernel f := b.r ≫ cokernel.π f
  have h₁g : h₁ ≫ g = 0 := by
    simp [h₁, g, Category.assoc, cokernel.condition]
  have h₂g : h₂ ≫ g = 0 := by
    simp [h₂, g, Preadditive.sub_comp, Category.assoc]
  have hcg : hc ≫ g = 0 := by
    show coprod.desc h₁ h₂ ≫ g = 0
    rw [coprod.desc_comp, h₁g, h₂g]
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      simp
    · rw [coprod.inr_desc]
      simp
  have hg : h ≫ g = 0 := by
    dsimp [h]
    rw [Category.assoc, hcg, comp_zero]
  have hcomp_of {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : hc ≫ k = 0 :=
    (cancel_epi (SheafOfModules.freeSumIso (R := R) K I).inv).1 <| by
      rwa [comp_zero, ← Category.assoc]
  have h₁k_of {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : h₁ ≫ k = 0 := by
    have hh : coprod.inl ≫ hc ≫ k = 0 := by rw [hcomp_of k hk, comp_zero]
    rwa [← Category.assoc, show coprod.inl ≫ hc = h₁ from coprod.inl_desc _ _] at hh
  have h₂k_of {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : h₂ ≫ k = 0 := by
    have hh : coprod.inr ≫ hc ≫ k = 0 := by rw [hcomp_of k hk, comp_zero]
    rwa [← Category.assoc, show coprod.inr ≫ hc = h₂ from coprod.inr_desc _ _] at hh
  have hfk_of {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : f ≫ b.i ≫ k = 0 := by
    apply (cancel_epi a.r).1
    rw [comp_zero]
    simpa [h₁, Category.assoc] using h₁k_of k hk
  have hfactor {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : k = b.r ≫ b.i ≫ k := by
    have hr := h₂k_of k hk
    rwa [show h₂ = 𝟙 _ - b.r ≫ b.i from rfl, Preadditive.sub_comp, Category.id_comp,
      sub_eq_zero, Category.assoc] at hr
  have hfac {Z : SheafOfModules.{0} R} (k : SheafOfModules.free (R := R) I ⟶ Z)
      (hk : h ≫ k = 0) : g ≫ cokernel.desc f (b.i ≫ k) (hfk_of k hk) = k := by
    dsimp [g]
    rw [Category.assoc, cokernel.π_desc]
    exact (hfactor k hk).symm
  have hcol : IsColimit (CokernelCofork.ofπ g hg) :=
    CokernelCofork.IsColimit.ofπ g hg (fun k hk => cokernel.desc f (b.i ≫ k) (hfk_of k hk))
      (fun k hk => hfac k hk) fun k hk _ hn => (cancel_epi g).1 (hn.trans (hfac k hk).symm)
  exact ⟨SheafOfModules.presentationOfIsCokernelFree h g hg hcol,
    ⟨⟨inferInstanceAs (Finite I)⟩, ⟨inferInstanceAs (Finite (K ⊕ I))⟩⟩⟩

/-- **Stacks 08FX**, finite presentation of the top cohomology. The degree-`m + 1` cohomology
of an `m`-pseudo-coherent object of the derived category whose cohomology vanishes above
`m + 1` is finitely presented. -/
@[stacks 08FX "finite_presentation_top_cohomology"]
theorem isFinitePresentation_homology (X : RingedSite.{u, u, 0})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
    [HasSheafify X.J AddCommGrpCat.{0}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{0} AddCommGrpCat.{0})]
    [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hK : X.IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m + 1)).obj
        K).IsFinitePresentation := by
  classical
  let Amod := SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let H := (DerivedCategory.homologyFunctor Amod (m + 1)).obj K
  obtain ⟨E, eE, hlocal⟩ :=
    exists_local_strictlyPerfect_approximation_boundedAbove X K m (m + 1) (by omega)
      hK hvanish
  let S (U : X.C) : Presieve U := Classical.choose (hlocal U)
  have hScov (U : X.C) : Sieve.generate (S U) ∈ X.J U := (Classical.choose_spec (hlocal U)).1
  let I := Σ U : X.C, Σ V : X.C, {f : V ⟶ U // S U f}
  have hlocalPresentation (i : I) : ∃ p : (H.over i.2.1).Presentation, p.IsFinite := by
    rcases i with ⟨U, V, ⟨f, hf⟩⟩
    obtain ⟨P, hP, hbounded, α, hiso, _⟩ := (Classical.choose_spec (hlocal U)).2 f hf
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V
    let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
    let a := m + 1
    have : PreservesFiniteLimits F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
    have : Functor.PreservesEpimorphisms F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms V
    have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
    have : IsIso (HomologicalComplex.homologyMap α a) := hiso a (by dsimp [a]; omega)
    let hEhom := (E.sc a).mapHomologyIso F
    let hFac := (DerivedCategory.homologyFunctorFactors Amod a).app E
    let hEK := (DerivedCategory.homologyFunctor Amod a).mapIso (Classical.choice eE)
    let hTarget : P.homology a ≅ H.over V :=
      asIso (HomologicalComplex.homologyMap α a) ≪≫ hEhom ≪≫
        F.mapIso hFac.symm ≪≫ F.mapIso hEK
    have hnext : IsZero (P.X (a + 1)) := hbounded (a + 1) (by dsimp [a]; omega)
    have hdnext : P.d a (a + 1) = 0 := hnext.eq_of_tgt _ _
    let d := P.d (a - 1) a
    let eCoker : cokernel d ≅ P.homology a :=
      (cokernelIsCokernel d).coconePointUniqueUpToIso
          (P.opcyclesIsCokernel (a - 1) a (by simp)) ≪≫
        (P.isoHomologyι a (a + 1) (by simp) hdnext).symm
    obtain ⟨n₀, i₀, r₀, h₀⟩ :=
      (isDirectSummandOfFiniteFree_iff_free _ _).mp (hP.termDirectSummand (a - 1))
    obtain ⟨n₁, i₁, r₁, h₁⟩ :=
      (isDirectSummandOfFiniteFree_iff_free _ _).mp (hP.termDirectSummand a)
    obtain ⟨pCoker, hpCoker⟩ :=
      finitePresentation_cokernel_of_retracts (R := R) ⟨i₀, r₀, h₀⟩ ⟨i₁, r₁, h₁⟩ d
    exact ⟨pCoker.ofIsIso (eCoker ≪≫ hTarget).hom, by infer_instance⟩
  let q : H.QuasicoherentData :=
    { I := I
      X := fun i => i.2.1
      coversTop := fun W => X.J.superset_covering
        ((Sieve.generate_le_iff _ _).2 fun V f hf => ⟨⟨W, V, ⟨f, hf⟩⟩, ⟨𝟙 V⟩⟩) (hScov W)
      presentation := fun i => Classical.choose (hlocalPresentation i) }
  exact ⟨q.shrink, { isFinite_presentation := fun i =>
    Classical.choose_spec (hlocalPresentation i.2.choose) }⟩

end AlgebraicGeometry.RingedSite

end
