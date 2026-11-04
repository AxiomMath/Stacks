module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# Presheaves with vanishing sheafification, and detecting them degreewise

A presheaf is *locally zero* when its sheafification vanishes. This file records closure
properties of that condition used in the sum formula of Stacks 09WG, and the degreewise criterion
for it on the total site of a simplicial-site situation: a presheaf on the total site all of whose
degreewise restrictions are locally zero is locally zero, and a morphism of presheaves on the total
site whose degreewise restrictions sheafify to monomorphisms sheafifies to a monomorphism.

## Main results

* `Stacks.Sites.AbelianSumFormula.isZero_presheafToSheaf_iff`: the sheafification of `P` is zero
  exactly when every morphism from `P` to a sheaf is zero.
* `Stacks.Sites.AbelianSumFormula.isZero_presheafToSheaf_sigma`: a coproduct of locally zero
  presheaves is locally zero.
* `Stacks.Sites.AbelianSumFormula.mono_presheafToSheaf_map_iff`: a morphism sheafifies to a
  monomorphism exactly when its kernel is locally zero.
* `Stacks.Sites.AbelianSumFormula.isZero_presheafToSheaf_of_forall_comp` and
  `Stacks.Sites.AbelianSumFormula.mono_presheafToSheaf_map_of_forall_comp`: both conditions are
  detected along a family of continuous functors which is jointly surjective on objects.
* `Stacks.Sites.AbelianSumFormula.isZero_presheafToSheaf_totalTopology_of_forall_degree` and
  `Stacks.Sites.AbelianSumFormula.mono_presheafToSheaf_map_totalTopology_of_forall_degree`: the
  degreewise criterion on the total site of a simplicial-site situation, in either of the two
  cases of Stacks 09WE.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Sites.AbelianSumFormula

variable (A : Type v) [Category.{u} A]

section Criterion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [Preadditive A] [HasWeakSheafify J A]

/-- The sheafification of `P` is a zero object if and only if every morphism from `P` to the
presheaf underlying a sheaf is zero. -/
theorem isZero_presheafToSheaf_iff (P : Cᵒᵖ ⥤ A) :
    IsZero ((presheafToSheaf J A).obj P) ↔ ∀ (T : Sheaf J A) (f : P ⟶ T.obj), f = 0 := by
  refine ⟨fun hP T f => ?_, fun h => ?_⟩
  · have hg : ((sheafificationAdjunction J A).homEquiv P T).symm f = 0 := hP.eq_of_src _ _
    have he := ((sheafificationAdjunction J A).homEquiv P T).apply_symm_apply f
    rw [hg, Adjunction.homEquiv_unit] at he
    simpa using he.symm
  · refine (IsZero.iff_id_eq_zero _).mpr ?_
    have e1 : (sheafificationAdjunction J A).homEquiv P ((presheafToSheaf J A).obj P) (𝟙 _) = 0 :=
      h _ _
    have e2 : (sheafificationAdjunction J A).homEquiv P ((presheafToSheaf J A).obj P) 0 = 0 := by
      rw [Adjunction.homEquiv_unit]
      simp
    exact ((sheafificationAdjunction J A).homEquiv P _).injective (e1.trans e2.symm)

/-- A coproduct of locally zero presheaves is locally zero. -/
theorem isZero_presheafToSheaf_sigma {I : Type w} (P : I → (Cᵒᵖ ⥤ A)) [HasCoproduct P]
    (h : ∀ i, IsZero ((presheafToSheaf J A).obj (P i))) :
    IsZero ((presheafToSheaf J A).obj (∐ P)) := by
  refine (isZero_presheafToSheaf_iff A J _).mpr fun T f ↦ Sigma.hom_ext _ _ fun i ↦ ?_
  exact ((isZero_presheafToSheaf_iff A J (P i)).mp (h i) T _).trans comp_zero.symm

end Criterion

section Kernel

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [Abelian A] [HasSheafify J A] {P Q : Cᵒᵖ ⥤ A}

/-- A morphism of presheaves sheafifies to a monomorphism exactly when its kernel is locally
zero. -/
theorem mono_presheafToSheaf_map_iff (h : P ⟶ Q) :
    Mono ((presheafToSheaf J A).map h) ↔ IsZero ((presheafToSheaf J A).obj (kernel h)) := by
  rw [Preadditive.mono_iff_isZero_kernel]
  exact (PreservesKernel.iso (presheafToSheaf J A) h).isZero_iff.symm

end Kernel

section Transfer

variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  {I : Type w} {Cs : I → Type u} [∀ i, SmallCategory (Cs i)]
  (Js : ∀ i, GrothendieckTopology (Cs i)) (v : ∀ i, Cs i ⥤ D)

section

variable [Preadditive A] [HasWeakSheafify K A] [∀ i, HasWeakSheafify (Js i) A]
  [∀ i, (v i).IsContinuous (Js i) K]

/-- If every object of `D` is isomorphic to one in the image of some `v i`, and the restriction
of `R` along each `v i` is locally zero, then `R` is locally zero. -/
theorem isZero_presheafToSheaf_of_forall_comp
    (hsurj : ∀ X : D, ∃ (i : I) (Y : Cs i), Nonempty ((v i).obj Y ≅ X))
    {R : Dᵒᵖ ⥤ A}
    (h : ∀ i, IsZero ((presheafToSheaf (Js i) A).obj ((v i).op ⋙ R))) :
    IsZero ((presheafToSheaf K A).obj R) := by
  rw [isZero_presheafToSheaf_iff]
  intro T f
  ext ⟨X⟩
  obtain ⟨i, Y, ⟨e⟩⟩ := hsurj X
  have hres : Functor.whiskerLeft (v i).op f = 0 :=
    (isZero_presheafToSheaf_iff A (Js i) _).mp (h i)
      ⟨(v i).op ⋙ T.obj, (v i).op_comp_isSheaf (Js i) K T⟩ (Functor.whiskerLeft (v i).op f)
  have h0 : f.app (op ((v i).obj Y)) = 0 := congrArg (fun α => NatTrans.app α (op Y)) hres
  have hnat := f.naturality e.hom.op
  rw [h0, comp_zero] at hnat
  simpa using (cancel_mono (T.obj.map e.hom.op)).mp (hnat.symm.trans zero_comp.symm)

end

/-- If every object of `D` is isomorphic to one in the image of some `v i`, and the restriction
of `h` along each `v i` sheafifies to a monomorphism, then `h` sheafifies to a monomorphism. -/
theorem mono_presheafToSheaf_map_of_forall_comp [Abelian A] [HasSheafify K A]
    [∀ i, HasSheafify (Js i) A] [∀ i, (v i).IsContinuous (Js i) K]
    (hsurj : ∀ X : D, ∃ (i : I) (Y : Cs i), Nonempty ((v i).obj Y ≅ X))
    {P Q : Dᵒᵖ ⥤ A} (h : P ⟶ Q)
    (hmono : ∀ i, Mono ((presheafToSheaf (Js i) A).map (Functor.whiskerLeft (v i).op h))) :
    Mono ((presheafToSheaf K A).map h) := by
  rw [mono_presheafToSheaf_map_iff]
  refine isZero_presheafToSheaf_of_forall_comp A K Js v hsurj fun i => ?_
  exact IsZero.of_iso ((mono_presheafToSheaf_map_iff A (Js i) _).mp (hmono i))
    ((presheafToSheaf (Js i) A).mapIso
      (PreservesKernel.iso ((Functor.whiskeringLeft _ _ A).obj (v i).op) h))

end Transfer

section Simplicial

variable (S : CategoryTheory.SimplicialSiteSituation.{u})

/-- A presheaf on the total site of a simplicial-site situation whose degreewise restrictions
are locally zero is locally zero. -/
theorem isZero_presheafToSheaf_totalTopology_of_forall_degree [Preadditive A]
    [HasWeakSheafify S.totalTopology A]
    [∀ n : SimplexCategory, HasWeakSheafify (S.componentTopology n) A]
    {R : S.totalCategoryᵒᵖ ⥤ A}
    (h : ∀ n : SimplexCategory, IsZero ((presheafToSheaf (S.componentTopology n) A).obj
      ((CategoryTheory.SimplicialSiteSituation.componentFunctor S n).op ⋙ R))) :
    IsZero ((presheafToSheaf S.totalTopology A).obj R) :=
  isZero_presheafToSheaf_of_forall_comp A S.totalTopology S.componentTopology
    (CategoryTheory.SimplicialSiteSituation.componentFunctor S)
    (fun X =>
      let ⟨n, Y, hY⟩ := CategoryTheory.SimplicialSiteSituation.exists_componentFunctor_obj S X
      ⟨n, Y, ⟨eqToIso hY⟩⟩) h

/-- A morphism of presheaves on the total site of a simplicial-site situation whose degreewise
restrictions sheafify to monomorphisms sheafifies to a monomorphism. -/
theorem mono_presheafToSheaf_map_totalTopology_of_forall_degree [Abelian A]
    [HasSheafify S.totalTopology A]
    [∀ n : SimplexCategory, HasSheafify (S.componentTopology n) A]
    {P Q : S.totalCategoryᵒᵖ ⥤ A} (h : P ⟶ Q)
    (hmono : ∀ n : SimplexCategory,
      Mono ((presheafToSheaf (S.componentTopology n) A).map (Functor.whiskerLeft
        (CategoryTheory.SimplicialSiteSituation.componentFunctor S n).op h))) :
    Mono ((presheafToSheaf S.totalTopology A).map h) :=
  mono_presheafToSheaf_map_of_forall_comp A S.totalTopology S.componentTopology
    (CategoryTheory.SimplicialSiteSituation.componentFunctor S)
    (fun X =>
      let ⟨n, Y, hY⟩ := CategoryTheory.SimplicialSiteSituation.exists_componentFunctor_obj S X
      ⟨n, Y, ⟨eqToIso hY⟩⟩) h hmono

end Simplicial

end Stacks.Sites.AbelianSumFormula

end
