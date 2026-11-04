module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAdditive
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact

/-!
# Exactness and acyclicity of complexes of sheaves of modules, tested at the stalks

Let `(C, J)` be a site, `R` a sheaf of rings on it, and `P` a conservative family of points.
This file proves that exactness of a short complex of sheaves of `R`-modules, and hence
acyclicity of a cochain complex of them, may be tested at the stalks at the points of `P`.

This is the module-valued form of Stacks 05V3 at the generality of a site, and it is the
statement that the proof of the stalk criterion for K-flatness (Stacks 0DEN) invokes as "we
can check exactness at stalks".

## Main results

* `Stacks.isZero_of_forall_isZero_sheafModuleFiber`: a sheaf of modules whose stalk at every
  point of a conservative family is a zero object is itself a zero object.
* `Stacks.exact_iff_forall_exact_map_sheafModuleFiber`: a short complex of sheaves of modules
  is exact if and only if its image under every one of the stalk functors is.
* `Stacks.acyclic_iff_forall_acyclic_sheafModuleFiber`: a cochain complex of sheaves of
  modules is acyclic if and only if the complex of stalks at every point of the family is.
* `Stacks.acyclic_iff_forall_acyclic_sheafModuleFiberOfCommRing`: the same, over the
  `CommRingCat`-valued stalk of a sheaf of commutative rings.

## Implementation notes

The reflection is organised around zero objects rather than around kernels and images. In an
abelian category a short complex is exact exactly when its homology object is zero
(`CategoryTheory.ShortComplex.exact_iff_isZero_homology`), and a stalk functor is exact, so it
carries the homology of a short complex to the homology of the image short complex
(`CategoryTheory.ShortComplex.mapHomologyIso`). What has to be reflected is therefore only the
property of *being a zero object*, and that is reflected because the family reflects
isomorphisms: `X` is a zero object exactly when `0 : X ⟶ X` is an isomorphism, a reading of
`IsZero` which needs no zero object in the ambient category and so costs nothing.

`Stacks.isIso_of_isIso_sheafModuleFiber` is the input, and it is used at the morphism
`0 : M ⟶ M` rather than at a morphism out of a zero object: there is then nothing to transport
across the comparison of `F.obj 0` with `0`.

The degreewise statement needs no transport. Both
`((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc i = (K.sc i).map F` and
`CategoryTheory.ShortComplex.map_comp` hold by definition, so the short complex cut out of the
stalk complex in degree `i` *is* the image under `F` of the short complex cut out of `K`.

For the `CommRingCat`-valued form the extra factor is `ModuleCat.restrictScalars` along the
comparison of the two stalk rings. That functor is faithful and exact, so it neither creates
nor destroys exactness of a short complex, and `exact_map_iff_of_faithful` passes between the
two readings.

## References

* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 00YL](https://stacks.math.columbia.edu/tag/00YL)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The stalk functor on sheaves of modules preserves finite limits and finite colimits. This
is `Stacks.exactFunctor_sheafModuleFiber` (Stacks 04EQ (1)) read as the pair of instances its
consumers need. -/
noncomputable instance preservesFiniteLimits_sheafModuleFiber' (Φ : J.Point.{w}) :
    PreservesFiniteLimits (sheafModuleFiber Φ R) :=
  ((exactFunctor_iff _).mp (exactFunctor_sheafModuleFiber Φ R)).1

/-- The stalk functor on sheaves of modules at a point of a site preserves finite colimits. -/
noncomputable instance preservesFiniteColimits_sheafModuleFiber (Φ : J.Point.{w}) :
    PreservesFiniteColimits (sheafModuleFiber Φ R) :=
  ((exactFunctor_iff _).mp (exactFunctor_sheafModuleFiber Φ R)).2

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A sheaf of `R`-modules all of whose stalks at a conservative family of points are zero
objects is a zero object. -/
theorem isZero_of_forall_isZero_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    {M : SheafOfModules.{w} R}
    (h : ∀ Φ : P.FullSubcategory, IsZero ((sheafModuleFiber Φ.obj R).obj M)) :
    IsZero M := by
  have hiso : IsIso (0 : M ⟶ M) := by
    refine isIso_of_isIso_sheafModuleFiber R hP 0 (fun Φ => ?_)
    rw [(sheafModuleFiber Φ.obj R).map_zero, (h Φ).eq_of_src 0 (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : M ⟶ M), comp_zero]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Taking stalks at a point of a site carries an acyclic cochain complex of sheaves of modules
to an acyclic complex of modules over the stalk of `R`. -/
theorem acyclic_map_sheafModuleFiber (Φ : J.Point.{w})
    {K : CochainComplex (SheafOfModules.{w} R) ℤ} (hK : K.Acyclic) :
    (((sheafModuleFiber Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff K i).mp (hK i)).map (sheafModuleFiber Φ R)

/-- **Exactness of a short complex of sheaves of modules is tested at the stalks.** A short
complex of sheaves of `R`-modules is exact if and only if its image under the stalk functor at
every point of a conservative family is exact.

This is the module-valued form of Stacks 05V3 at the generality of a site. -/
theorem exact_iff_forall_exact_map_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    (S : ShortComplex (SheafOfModules.{w} R)) :
    S.Exact ↔ ∀ Φ : P.FullSubcategory, (S.map (sheafModuleFiber Φ.obj R)).Exact := by
  refine ⟨fun hS _ => hS.map _, fun h => ?_⟩
  rw [S.exact_iff_isZero_homology]
  refine isZero_of_forall_isZero_sheafModuleFiber R hP fun Φ => ?_
  exact ((ShortComplex.exact_iff_isZero_homology _).mp (h Φ)).of_iso
    (S.mapHomologyIso (sheafModuleFiber Φ.obj R)).symm

/-- **Acyclicity of a complex of sheaves of modules is tested at the stalks.** A cochain
complex of sheaves of `R`-modules is acyclic if and only if, for every point of a conservative
family, the cochain complex of modules over the stalk of `R` obtained by taking stalks
degreewise is acyclic. -/
theorem acyclic_iff_forall_acyclic_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    (K : CochainComplex (SheafOfModules.{w} R) ℤ) :
    K.Acyclic ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiber Φ.obj R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  refine ⟨fun h Φ => acyclic_map_sheafModuleFiber R Φ.obj h, fun h i => ?_⟩
  rw [HomologicalComplex.exactAt_iff]
  exact (exact_iff_forall_exact_map_sheafModuleFiber R hP _).mpr
    fun Φ => (HomologicalComplex.exactAt_iff _ _).mp (h Φ i)

section CommRing

variable (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction of scalars along the comparison of the two stalk rings preserves finite
limits. -/
private instance preservesFiniteLimits_restrictScalars_commRingSheafFiberIso (Φ : J.Point.{w}) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
  preservesFiniteLimits_restrictScalars _

/-- Restriction of scalars along the comparison of the two stalk rings preserves finite
colimits. -/
private instance preservesFiniteColimits_restrictScalars_commRingSheafFiberIso
    (Φ : J.Point.{w}) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
  preservesFiniteColimits_restrictScalars _

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Taking stalks at a point of a site, over the `CommRingCat`-valued stalk of `O`, carries an
acyclic cochain complex of sheaves of modules to an acyclic complex. -/
theorem acyclic_map_sheafModuleFiberOfCommRing (Φ : J.Point.{w})
    {K : CochainComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ℤ} (hK : K.Acyclic) :
    (((sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  have h := (HomologicalComplex.exactAt_iff K i).mp (hK i)
  exact (h.map (sheafModuleFiber Φ (commRingSheafToRingSheaf O))).map
    (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom)

/-- Exactness of a short complex of sheaves of modules over the ring sheaf of a sheaf of
commutative rings, tested at the stalks over the `CommRingCat`-valued stalk of `O`. Restriction
of scalars along the comparison of the two stalk rings is faithful and exact, so it changes
nothing. -/
theorem exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
    (hP : P.IsConservativeFamilyOfPoints)
    (S : ShortComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O))) :
    S.Exact ↔ ∀ Φ : P.FullSubcategory,
      (S.map (sheafModuleFiberOfCommRing Φ.obj O)).Exact := by
  rw [exact_iff_forall_exact_map_sheafModuleFiber (commRingSheafToRingSheaf O) hP S]
  refine forall_congr' fun Φ => ?_
  exact ((S.map (sheafModuleFiber Φ.obj (commRingSheafToRingSheaf O))).exact_map_iff_of_faithful
    (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ.obj O).inv.hom)).symm

/-- **Acyclicity over the stalk of a sheaf of commutative rings.** A cochain complex of
sheaves of modules over the ring sheaf of `O` is acyclic if and only if, for every point of a
conservative family, the complex of modules over the `CommRingCat`-valued stalk of `O` obtained
by taking stalks degreewise is acyclic.

This is the form consumed by statements about complexes of modules over the stalk ring, where
the ring has to be commutative: K-flatness of `K_Φ` over `O_Φ` in Stacks 0DEN is the case at
hand. -/
theorem acyclic_iff_forall_acyclic_sheafModuleFiberOfCommRing
    (hP : P.IsConservativeFamilyOfPoints)
    (K : CochainComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ℤ) :
    K.Acyclic ↔ ∀ Φ : P.FullSubcategory,
      (((sheafModuleFiberOfCommRing Φ.obj O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic := by
  refine ⟨fun h Φ => acyclic_map_sheafModuleFiberOfCommRing O Φ.obj h, fun h i => ?_⟩
  rw [HomologicalComplex.exactAt_iff]
  exact (exact_iff_forall_exact_map_sheafModuleFiberOfCommRing O hP _).mpr
    fun Φ => (HomologicalComplex.exactAt_iff _ i).mp (h Φ i)

end CommRing

end Stacks

end
