module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact

/-! # Stalkwise detection of exactness and acyclicity for sheaves of modules

Let `(C, J)` be a site and let `P` be a conservative family of points of it, in the sense of
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`. For a sheaf of rings `R` on `C`,
taking the stalk at a point is an exact functor on sheaves of `R`-modules
(`Stacks.exactFunctor_sheafModuleFiber`), and the stalks at a conservative family jointly reflect
isomorphisms (`Stacks.isIso_of_isIso_sheafModuleFiber`). This file proves that a short complex,
or a complex, of sheaves of `R`-modules is exact, or acyclic, if and only if its stalks at `P`
are.

## Main results

* `Stacks.isZero_sheafModuleFiber_obj_iff`: a sheaf of modules is zero if and only if its stalks
  at a conservative family of points are zero.
* `Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiber`: a short complex of sheaves
  of modules is exact if and only if its stalks are exact.
* `Stacks.exactAt_iff_forall_exactAt_mapSheafModuleFiber` and
  `Stacks.acyclic_iff_forall_acyclic_mapSheafModuleFiber`: exactness at an index, and acyclicity,
  of a complex of sheaves of modules in any complex shape are detected by the stalk complexes.
* `Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing`,
  `Stacks.exactAt_iff_forall_exactAt_mapSheafModuleFiberOfCommRing` and
  `Stacks.acyclic_iff_forall_acyclic_mapSheafModuleFiberOfCommRing`: the same three criteria for
  modules over the ring sheaf of a sheaf of *commutative* rings, with the stalk taken as a module
  over the `CommRingCat`-valued stalk of that sheaf.

## References

* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 00YL](https://stacks.math.columbia.edu/tag/00YL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u

/-- The short complex at an index of the degreewise image of a complex under a functor preserving
zero morphisms is the image of the short complex at that index. -/
lemma sc_mapHomologicalComplex {A B : Type*} [Category A] [Category B] [Preadditive A]
    [Preadditive B] (F : A ⥤ B) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).sc i = (K.sc i).map F :=
  rfl

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The stalk functor on sheaves of modules preserves homology. -/
noncomputable instance preservesHomology_sheafModuleFiber (Φ : J.Point.{w}) :
    (sheafModuleFiber Φ R).PreservesHomology := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp (exactFunctor_sheafModuleFiber Φ R)
  infer_instance

/-- The stalk of a zero sheaf of modules is zero. -/
lemma isZero_sheafModuleFiber_obj (Φ : J.Point.{w}) {M : SheafOfModules.{w} R} (hM : IsZero M) :
    IsZero ((sheafModuleFiber Φ R).obj M) := by
  rw [IsZero.iff_id_eq_zero] at hM ⊢
  rw [← (sheafModuleFiber Φ R).map_id M, hM, (sheafModuleFiber Φ R).map_zero]

/-- The stalk of an exact short complex of sheaves of modules is exact. -/
lemma shortComplex_exact_map_sheafModuleFiber (Φ : J.Point.{w})
    {S : ShortComplex (SheafOfModules.{w} R)} (hS : S.Exact) :
    (S.map (sheafModuleFiber Φ R)).Exact :=
  hS.map _

section Conservative

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-! ### Detection of the zero object -/

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A sheaf of modules whose stalks at a conservative family of points all vanish is zero. -/
lemma isZero_of_isZero_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    {M : SheafOfModules.{w} R}
    (hM : ∀ Φ : P.FullSubcategory, IsZero ((sheafModuleFiber Φ.obj R).obj M)) : IsZero M := by
  have h : IsIso (0 : M ⟶ M) := by
    refine isIso_of_isIso_sheafModuleFiber R hP 0 fun Φ ↦ ?_
    rw [(hM Φ).eq_of_src ((sheafModuleFiber Φ.obj R).map (0 : M ⟶ M)) (𝟙 _)]
    exact inferInstanceAs (IsIso (𝟙 _))
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : M ⟶ M), zero_comp]

/-- A sheaf of modules on a site with a conservative family of points is zero if and only if all
its stalks at that family are zero. -/
lemma isZero_sheafModuleFiber_obj_iff (hP : P.IsConservativeFamilyOfPoints)
    {M : SheafOfModules.{w} R} :
    IsZero M ↔ ∀ Φ : P.FullSubcategory, IsZero ((sheafModuleFiber Φ.obj R).obj M) :=
  ⟨fun hM Φ ↦ isZero_sheafModuleFiber_obj R Φ.obj hM, isZero_of_isZero_sheafModuleFiber R hP⟩

/-! ### Detection of exactness of a short complex -/

/-- A short complex of sheaves of modules whose stalks at a conservative family of points are
all exact is exact. -/
lemma shortComplex_exact_of_forall_exact_map_sheafModuleFiber
    (hP : P.IsConservativeFamilyOfPoints) {S : ShortComplex (SheafOfModules.{w} R)}
    (hS : ∀ Φ : P.FullSubcategory, (S.map (sheafModuleFiber Φ.obj R)).Exact) : S.Exact := by
  rw [S.leftHomologyData.exact_iff]
  exact isZero_of_isZero_sheafModuleFiber R hP fun Φ ↦
    (S.leftHomologyData.exact_map_iff (sheafModuleFiber Φ.obj R)).mp (hS Φ)

/-- A short complex of sheaves of modules on a site with a conservative family of points is exact
if and only if all its stalks at that family are exact. -/
theorem shortComplex_exact_iff_forall_exact_map_sheafModuleFiber
    (hP : P.IsConservativeFamilyOfPoints) {S : ShortComplex (SheafOfModules.{w} R)} :
    S.Exact ↔ ∀ Φ : P.FullSubcategory, (S.map (sheafModuleFiber Φ.obj R)).Exact :=
  ⟨fun hS Φ ↦ shortComplex_exact_map_sheafModuleFiber R Φ.obj hS,
    shortComplex_exact_of_forall_exact_map_sheafModuleFiber R hP⟩

/-! ### Detection of exactness and acyclicity of a complex -/

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (SheafOfModules.{w} R) c)

/-- A complex of sheaves of modules on a site with a conservative family of points is exact at an
index if and only if all its stalk complexes are. -/
theorem exactAt_iff_forall_exactAt_mapSheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    (i : ι) :
    K.ExactAt i ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiber Φ.obj R).mapHomologicalComplex c).obj K).ExactAt i := by
  simp only [HomologicalComplex.exactAt_iff, sc_mapHomologicalComplex]
  exact shortComplex_exact_iff_forall_exact_map_sheafModuleFiber R hP

/-- A complex of sheaves of modules on a site with a conservative family of points is acyclic if
and only if all its stalk complexes are acyclic. -/
theorem acyclic_iff_forall_acyclic_mapSheafModuleFiber (hP : P.IsConservativeFamilyOfPoints) :
    K.Acyclic ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiber Φ.obj R).mapHomologicalComplex c).obj K).Acyclic := by
  simp only [HomologicalComplex.acyclic_iff]
  rw [forall_comm]
  exact forall_congr' fun i ↦ exactAt_iff_forall_exactAt_mapSheafModuleFiber R K hP i

end Conservative

/-! ### The same criteria for modules over the ring sheaf of a sheaf of commutative rings

The stalk is taken as a module over the `CommRingCat`-valued stalk of the sheaf of rings, by
`Stacks.sheafModuleFiberOfCommRing`.
-/

section CommRing

variable (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}

/-- The stalk functor on sheaves of modules over the ring sheaf of a sheaf of commutative rings
preserves zero morphisms. -/
instance preservesZeroMorphisms_sheafModuleFiberOfCommRing (Φ : J.Point.{w}) :
    (sheafModuleFiberOfCommRing Φ O).PreservesZeroMorphisms := by
  have := preservesFiniteLimits_sheafModuleFiberOfCommRing Φ O
  infer_instance

/-- The stalk functor on sheaves of modules over the ring sheaf of a sheaf of commutative rings
preserves homology. -/
noncomputable instance preservesHomology_sheafModuleFiberOfCommRing (Φ : J.Point.{w}) :
    (sheafModuleFiberOfCommRing Φ O).PreservesHomology := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp (exactFunctor_sheafModuleFiberOfCommRing Φ O)
  infer_instance

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Taking the stalk of a short complex as a module over the `CommRingCat`-valued stalk of `O`
detects exactness exactly as taking it over the `RingCat`-valued stalk does. -/
lemma shortComplex_exact_map_sheafModuleFiberOfCommRing_iff (Φ : J.Point.{w})
    (S : ShortComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O))) :
    (S.map (sheafModuleFiberOfCommRing Φ O)).Exact ↔
      (S.map (sheafModuleFiber Φ (commRingSheafToRingSheaf O))).Exact := by
  have h₁ : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
    preservesFiniteLimits_restrictScalars _
  have h₂ : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
    preservesFiniteColimits_restrictScalars _
  exact ShortComplex.exact_map_iff_of_faithful
    (S.map (sheafModuleFiber Φ (commRingSheafToRingSheaf O)))
    (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom)

/-- A short complex of sheaves of modules over the ring sheaf of a sheaf of commutative rings is
exact if and only if all its stalks at a conservative family of points are exact. -/
theorem shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
    (hP : P.IsConservativeFamilyOfPoints)
    {S : ShortComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O))} :
    S.Exact ↔ ∀ Φ : P.FullSubcategory, (S.map (sheafModuleFiberOfCommRing Φ.obj O)).Exact :=
  (shortComplex_exact_iff_forall_exact_map_sheafModuleFiber _ hP).trans <| forall_congr' fun Φ ↦
    (shortComplex_exact_map_sheafModuleFiberOfCommRing_iff O Φ.obj S).symm

variable {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) c)

/-- Exactness at an index of a complex of sheaves of modules over the ring sheaf of a sheaf of
commutative rings is detected by the stalk complexes at a conservative family of points. -/
theorem exactAt_iff_forall_exactAt_mapSheafModuleFiberOfCommRing
    (hP : P.IsConservativeFamilyOfPoints) (i : ι) :
    K.ExactAt i ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiberOfCommRing Φ.obj O).mapHomologicalComplex c).obj K).ExactAt i := by
  simp only [HomologicalComplex.exactAt_iff, sc_mapHomologicalComplex]
  exact shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing O hP

/-- A complex of sheaves of modules over the ring sheaf of a sheaf of commutative rings is acyclic
if and only if all its stalk complexes at a conservative family of points are acyclic. -/
theorem acyclic_iff_forall_acyclic_mapSheafModuleFiberOfCommRing
    (hP : P.IsConservativeFamilyOfPoints) :
    K.Acyclic ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiberOfCommRing Φ.obj O).mapHomologicalComplex c).obj K).Acyclic := by
  simp only [HomologicalComplex.acyclic_iff]
  rw [forall_comm]
  exact forall_congr' fun i ↦
    exactAt_iff_forall_exactAt_mapSheafModuleFiberOfCommRing O K hP i

end CommRing

end Stacks

end
