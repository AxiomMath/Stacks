module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleMorphismHomology
public import StacksFrontier.Algebra.Homology.HomologyOfADegreewiseEpi
public import StacksFrontier.Algebra.Homology.ExactAtMapOfProjectiveTail
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerTensorBaseChange
public import StacksFrontier.Cotangent.TensorProductNineDiagramCanonical

/-!
# The object `E` of the tensor-product nine diagram, compared with Lichtenbaum–Schlessinger

Let `R` be a ring, `A` and `B` two `R`-algebras and `P → B` a polynomial presentation of `B`
over `R`. Write `L` for the Lichtenbaum–Schlessinger complex of `P` and `L_A` for that of the
base-changed presentation of `A ⊗_R B` over `A`. This file carries out the comparison step of
the proof of [Stacks, Tag 09DB]: for every object `E` sitting in a distinguished triangle

`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A} ⟶ E ⟶`

on the canonical map of the right column of Equation 92.15.0.1, the cohomology of `E` in degrees
`≥ -2` is that of the cokernel of the map `(A ⊗_R B) ⊗_B L ⟶ L_A` of Tag 09D7, provided that
map is onto in the degrees `-1` and `0`, injective there, and that `L` has projective terms in
those degrees.

The canonical maps `L_{B/R} → L` and `L_{A ⊗_R B/A} → L_A` of Tag 09CG commute with the two maps
up to homotopy (Tag 09D7), and both are isomorphisms on cohomology in degrees `≥ -2`; the first
remains so after base change in degrees `≥ -1` and onto in degree `-2`, by the splitting argument
of `CochainComplex.exactAt_mapHomologicalComplex_of_projective_tail` applied to its mapping
cone. The five lemma on the induced morphism of triangles then concludes.

## Main results

* `CommAlgCat.lsHomotopy`: the homotopy of Tag 09D7 between the two composites, over `A ⊗_R B`.
* `CommAlgCat.isIso_homologyMap_comparisonMor₃`: the five lemma step.

## References

* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

/-- A complex of modules is isomorphic to its universe lift along `ModuleCat.uliftFunctor`, in
its own universe. -/
def uliftComplexIso {B : Type u} [Ring B] (K : CochainComplex (ModuleCat.{u} B) ℤ) :
    K ≅ ((ModuleCat.uliftFunctor.{u} B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (ULift.moduleEquiv.{u, u, u} (R := B) (M := _)).symm.toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The cotangent complex is isomorphic to its universe lift used by the
Lichtenbaum–Schlessinger comparison, in its own universe. -/
def cotangentComplexULiftSelfIso (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    cotangentComplex.{u, u} A (CommAlgCat.of A B) ≅
      Algebra.Presentation.cotangentComplexULift.{u, u, u} A B :=
  uliftComplexIso _

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {X T : Type u} (P : Algebra.Presentation R B X T)

/-- Extension of scalars along `B → A ⊗_R B`, on complexes. -/
abbrev tensorExt :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  (ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical map `L_{B/R} → L` of Tag 09CG, out of the cotangent complex itself. -/
def lsMapB : cotangentComplex.{u, u} R (CommAlgCat.of R B) ⟶
    (Algebra.Presentation.lichtenbaumSchlessingerComplex P).complex :=
  (cotangentComplexULiftSelfIso R B).hom ≫ Algebra.Presentation.lsChainMap.{u, u, u} P

/-- The canonical map `L_{A ⊗_R B/A} → L_A` of Tag 09CG, out of the cotangent complex itself. -/
def lsMapC : cotangentComplex.{u, u} A (CommAlgCat.of A (A ⊗[R] B)) ⟶
    (Algebra.Presentation.lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex :=
  (cotangentComplexULiftSelfIso A (A ⊗[R] B)).hom ≫
    Algebra.Presentation.lsChainMap.{u, u, u} (P.tensorBaseChange A)

/-- The universe lift commutes with the map of cotangent complexes of a square. -/
theorem uliftComplexIso_hom_comp_cotangentComplexULiftSquareMap :
    (cotangentComplexULiftSelfIso R B).hom ≫
        Algebra.Presentation.cotangentComplexULiftSquareMap.{u, u, u, u} R A B (A ⊗[R] B) =
      squareCotangentComplexMap.{u, u, u}
          (algebraSquareOfAlgHom (tensorProductIncludeRight R A B)) ≫
        ((ModuleCat.restrictScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (cotangentComplexULiftSelfIso A (A ⊗[R] B)).hom :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **Tag 09D7 over `B`, up to homotopy.** The canonical map `L_{B/R} → L` followed by the map
`L → L_A` of Lichtenbaum–Schlessinger complexes is homotopic to the map
`L_{B/R} → L_{A ⊗_R B/A}` of the square followed by the canonical map `L_{A ⊗_R B/A} → L_A`. -/
def lsHomotopyB :
    Homotopy (lsMapB R B P ≫ (P.tensorBaseChangeHom A).complexMap)
      (squareCotangentComplexMap.{u, u, u}
          (algebraSquareOfAlgHom (tensorProductIncludeRight R A B)) ≫
        ((ModuleCat.restrictScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (lsMapC R A B P)) := by
  let H₀ := Algebra.Presentation.homotopyOfIsLichtenbaumSchlessingerRelativeComparison.{u, u, u, u}
    (P.tensorBaseChange A)
    ((P.tensorBaseChangeHom A).isLichtenbaumSchlessingerRelativeComparison_outer)
    (Algebra.Presentation.isLichtenbaumSchlessingerRelativeComparison_inner.{u, u, u, u}
      (A := R) (B := B) (P.tensorBaseChange A))
  let x := (cotangentComplexULiftSelfIso R B).hom ≫
    (Algebra.Presentation.cotangentComplexULiftIso.{u, u, u, u} R B).hom
  refine (Homotopy.ofEq ?_).trans ((H₀.compLeft x).trans (Homotopy.ofEq ?_))
  · rw [Category.assoc, Iso.hom_inv_id_assoc, lsMapB, Category.assoc]
    rfl
  · rw [Category.assoc, Iso.hom_inv_id_assoc, lsMapC, Functor.map_comp]
    change (cotangentComplexULiftSelfIso R B).hom ≫
      (Algebra.Presentation.cotangentComplexULiftSquareMap.{u, u, u, u} R A B (A ⊗[R] B) ≫ _) = _
    rw [← Category.assoc, uliftComplexIso_hom_comp_cotangentComplexULiftSquareMap]
    exact Category.assoc _ _ _

/-- **Tag 09D7 over `A ⊗_R B`, up to homotopy.** The canonical map
`(A ⊗_R B) ⊗_B L_{B/R} ⟶ L_{A ⊗_R B/A}` of the right column followed by the canonical map
`L_{A ⊗_R B/A} → L_A` is homotopic to the base change of the canonical map `L_{B/R} → L` followed
by the map `(A ⊗_R B) ⊗_B L ⟶ L_A`. -/
def lsHomotopy :
    Homotopy (cotangentExtendScalarsComplexMap (tensorProductIncludeRight R A B) ≫ lsMapC R A B P)
      ((tensorExt R A B).map (lsMapB R B P) ≫ P.tensorBaseChangeComplexMap A) := by
  let H := ((ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).mapHomotopy
    (lsHomotopyB R A B P)).compRight
      (ModuleCat.extendRestrictScalarsAdjCounitComplex (algebraMap B (A ⊗[R] B))
        (ComplexShape.up ℤ)
        (Algebra.Presentation.lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex)
  refine (Homotopy.ofEq ?_).trans (H.symm.trans (Homotopy.ofEq ?_))
  · rw [cotangentExtendScalarsComplexMap_eq_counit]
    exact (Category.assoc _ _ _).trans ((whisker_eq _
      (ModuleCat.extendRestrictScalarsAdjCounitComplex_naturality (algebraMap B (A ⊗[R] B))
        (ComplexShape.up ℤ) (lsMapC R A B P)).symm).trans
      ((Category.assoc _ _ _).symm.trans (eq_whisker (Functor.map_comp _ _ _).symm _)))
  · rw [Functor.map_comp, Category.assoc]
    rfl

/-- **Tag 09D7 over `A ⊗_R B`, in `D(A ⊗_R B)`.** -/
theorem Q_map_lsSquare :
    DerivedCategory.Q.map
        (cotangentExtendScalarsComplexMap (tensorProductIncludeRight R A B) ≫ lsMapC R A B P) =
      DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P) ≫
        P.tensorBaseChangeComplexMap A) :=
  DerivedCategory.Q_map_eq_of_homotopy (h := lsHomotopy R A B P)

/-! ### Cohomology of the two comparison maps -/

/-- A map of complexes induces an epimorphism on cohomology in degree `n` through the derived
category if and only if it induces an epimorphism on homology in degree `n`. -/
theorem epi_homologyFunctor_map_Q_map_iff {S : Type u} [Ring S]
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map (DerivedCategory.Q.map f)) ↔
      Epi (HomologicalComplex.homologyMap f n) :=
  (MorphismProperty.epimorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n) f)

/-- A map of complexes induces a monomorphism on cohomology in degree `n` through the derived
category if and only if it induces a monomorphism on homology in degree `n`. -/
theorem mono_homologyFunctor_map_Q_map_iff {S : Type u} [Ring S]
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map (DerivedCategory.Q.map f)) ↔
      Mono (HomologicalComplex.homologyMap f n) :=
  (MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n) f)

/-- The degree `n` cohomology of a complex in the derived category vanishes if and only if the
complex is exact in degree `n`. -/
theorem isZero_homologyFunctor_obj_Q_obj_iff {S : Type u} [Ring S]
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj (DerivedCategory.Q.obj K)) ↔
      K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n).app K).isZero_iff

/-- Precomposing with an isomorphism of complexes preserves being an isomorphism on cohomology. -/
private theorem isIso_homologyFunctor_map_Q_map_iso_comp {S : Type u} [Ring S]
    {K L M : CochainComplex (ModuleCat.{u} S) ℤ} (e : K ≅ L) (g : L ⟶ M) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
      (DerivedCategory.Q.map g))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
      (DerivedCategory.Q.map (e.hom ≫ g))) := by
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **Tag 09CG over `A ⊗_R B`.** The canonical map `L_{A ⊗_R B/A} → L_A` is an isomorphism on
cohomology in every degree `≥ -2`. -/
theorem isIso_homologyFunctor_map_Q_map_lsMapC (n : ℤ) (hn : -2 ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (DerivedCategory.Q.map (lsMapC R A B P))) := by
  exact isIso_homologyFunctor_map_Q_map_iso_comp (cotangentComplexULiftSelfIso A (A ⊗[R] B)) _ n
    (Algebra.Presentation.isIso_homologyFunctor_map_canonicalCotangentToLichtenbaumSchlessinger
      (P.tensorBaseChange A) n hn)

/-- **Tag 09CG over `B`.** The canonical map `L_{B/R} → L` is an isomorphism on cohomology in
every degree `≥ -2`. -/
theorem isIso_homologyFunctor_map_Q_map_lsMapB (n : ℤ) (hn : -2 ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map
      (DerivedCategory.Q.map (lsMapB R B P))) := by
  exact isIso_homologyFunctor_map_Q_map_iso_comp (cotangentComplexULiftSelfIso R B) _ n
    (Algebra.Presentation.isIso_homologyFunctor_map_canonicalCotangentToLichtenbaumSchlessinger
      P n hn)

/-- The mapping cone of the canonical map `L_{B/R} → L` is exact in every degree `≥ -2`. -/
theorem exactAt_mappingCone_lsMapB (n : ℤ) (hn : -2 ≤ n) :
    (CochainComplex.mappingCone (lsMapB R B P)).ExactAt n := by
  rw [← isZero_homologyFunctor_obj_Q_obj_iff]
  have hT := DerivedCategory.mappingCone_triangle_distinguished (lsMapB R B P)
  have h₁ := isIso_homologyFunctor_map_Q_map_lsMapB R B P n hn
  have h₂ := isIso_homologyFunctor_map_Q_map_lsMapB R B P (n + 1) (by omega)
  exact DerivedCategory.isZero_homologyFunctor_obj₃ hT n (@IsIso.epi_of_iso _ _ _ _ _ h₁)
    (@IsIso.mono_of_iso _ _ _ _ _ h₂)

variable {R B P} in
/-- The terms of the mapping cone of `L_{B/R} → L` are projective in every degree `> -2`, as
soon as those of `L` are. -/
theorem projective_mappingCone_lsMapB_X
    (hproj : ∀ n : ℤ, -2 < n → Projective
      ((Algebra.Presentation.lichtenbaumSchlessingerComplex P).complex.X n))
    (n : ℤ) (hn : -2 < n) :
    Projective ((CochainComplex.mappingCone (lsMapB R B P)).X n) := by
  have := projective_cotangentComplex_X R (CommAlgCat.of R B) (n + 1)
  have := hproj n hn
  exact Projective.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (lsMapB R B P) n (n + 1) rfl).symm
    inferInstance

/-- The mapping cone of `L_{B/R} → L` vanishes in positive degrees. -/
theorem isZero_mappingCone_lsMapB_X (n : ℤ) (hn : 0 < n) :
    IsZero ((CochainComplex.mappingCone (lsMapB R B P)).X n) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨cotangentComplex_isZero_pos R (CommAlgCat.of R B) (n + 1) (by omega),
    (Algebra.Presentation.lichtenbaumSchlessingerComplex P).isZero_X n (by omega) (by omega)
      (by omega)⟩

variable {R B P} in
/-- **The canonical map `L_{B/R} → L`, base changed to `A ⊗_R B`.** It is onto on cohomology in
every degree `≥ -2` and injective in every degree `≥ -1`: the mapping cone of `L_{B/R} → L` is
exact in degrees `≥ -2` with projective terms in degrees `> -2`, so its base change is still exact
there. -/
theorem homologyFunctor_map_Q_map_tensorExt_lsMapB
    (hproj : ∀ n : ℤ, -2 < n → Projective
      ((Algebra.Presentation.lichtenbaumSchlessingerComplex P).complex.X n)) (n : ℤ)
    (hn : -2 ≤ n) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
        (DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P)))) ∧
      (-1 ≤ n → Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
        (DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P))))) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap B (A ⊗[R] B))
  have hex : ∀ m : ℤ, -2 ≤ m →
      (CochainComplex.mappingCone ((tensorExt R A B).map (lsMapB R B P))).ExactAt m :=
    fun m hm => (CochainComplex.exactAt_mapHomologicalComplex_of_projective_tail F (-2) 0
      (isZero_mappingCone_lsMapB_X R B P) (exactAt_mappingCone_lsMapB R B P)
      (projective_mappingCone_lsMapB_X hproj) m hm).of_iso
        (CochainComplex.mappingCone.mapHomologicalComplexIso (lsMapB R B P) F)
  have hT := DerivedCategory.mappingCone_triangle_distinguished
    ((tensorExt R A B).map (lsMapB R B P))
  refine ⟨DerivedCategory.epi_homologyFunctor_map_mor₁_of_isZero hT n
    ((isZero_homologyFunctor_obj_Q_obj_iff _ n).2 (hex n hn)), fun hn' => ?_⟩
  have h := DerivedCategory.mono_homologyFunctor_map_mor₁_of_isZero hT (n - 1)
    ((isZero_homologyFunctor_obj_Q_obj_iff _ (n - 1)).2 (hex (n - 1) (by omega)))
  rwa [sub_add_cancel] at h

/-! ### The image factorization of `(A ⊗_R B) ⊗_B L ⟶ L_A` -/

/-- The short exact sequence `0 → Im ⟶ L_A ⟶ Coker → 0` of the map
`(A ⊗_R B) ⊗_B L ⟶ L_A`. -/
abbrev tensorBaseChangeImageSES : ShortComplex (CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ) :=
  ShortComplex.mk (Abelian.image.ι (P.tensorBaseChangeComplexMap A))
    (cokernel.π (P.tensorBaseChangeComplexMap A)) (kernel.condition _)

/-- The sequence `0 → Im ⟶ L_A ⟶ Coker → 0` of the map `(A ⊗_R B) ⊗_B L ⟶ L_A` is short exact. -/
theorem tensorBaseChangeImageSES_shortExact : (tensorBaseChangeImageSES R A B P).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstance : Mono (kernel.ι (cokernel.π (P.tensorBaseChangeComplexMap A))))
    (inferInstance : Epi (cokernel.π (P.tensorBaseChangeComplexMap A)))

/-- The degree `n` term of the cokernel of a map of complexes is the cokernel of its degree `n`
component. -/
def cokernelXIso {S : Type u} [Ring S] {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L)
    (n : ℤ) : (cokernel f).X n ≅ cokernel (f.f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval _ _ n) f

variable {R A B P}
variable (hepi : ∀ n : ℤ, n ≠ -2 → Epi ((P.tensorBaseChangeComplexMap A).f n))
  (hmono : ∀ n : ℤ, -2 < n → Mono ((P.tensorBaseChangeComplexMap A).f n))

include hepi in
/-- The cokernel of `(A ⊗_R B) ⊗_B L ⟶ L_A` vanishes in every degree `n ≠ -2`. -/
theorem isZero_cokernel_tensorBaseChangeComplexMap_X (n : ℤ) (hn : n ≠ -2) :
    IsZero ((cokernel (P.tensorBaseChangeComplexMap A)).X n) := by
  have := hepi n hn
  exact (isZero_cokernel_of_epi _).of_iso (cokernelXIso _ n)

include hmono in
/-- The map from `(A ⊗_R B) ⊗_B L` onto the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` is injective in
every degree `> -2`. -/
theorem mono_factorThruImage_f (n : ℤ) (hn : -2 < n) :
    Mono ((Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)).f n) := by
  have := hmono n hn
  have h : (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)).f n ≫
      (Abelian.image.ι (P.tensorBaseChangeComplexMap A)).f n =
        (P.tensorBaseChangeComplexMap A).f n := by
    rw [← HomologicalComplex.comp_f, Abelian.image.fac]
  exact mono_of_mono_fac h

include hmono in
/-- The map from `(A ⊗_R B) ⊗_B L` onto the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` is an isomorphism
on homology in every degree `≥ -1`. -/
theorem isIso_homologyMap_factorThruImage (n : ℤ) (hn : -1 ≤ n) :
    IsIso (HomologicalComplex.homologyMap
      (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)) n) := by
  let p := Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)
  have h₁ : Epi (p.f (n - 1)) := inferInstance
  have : Mono (p.f n) := mono_factorThruImage_f hmono n (by omega)
  have : Epi (p.f n) := inferInstance
  have h₂ : IsIso (p.f n) := isIso_of_mono_of_epi _
  have h₃ : Mono (p.f (n + 1)) := mono_factorThruImage_f hmono (n + 1) (by omega)
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map p)
    (by change Epi (p.f ((ComplexShape.up ℤ).prev n)); rw [CochainComplex.prev]; exact h₁) h₂
    (by change Mono (p.f ((ComplexShape.up ℤ).next n)); rw [CochainComplex.next]; exact h₃)

include hmono in
/-- The map from `(A ⊗_R B) ⊗_B L` onto the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` is onto on homology
in degree `-2`. -/
theorem epi_homologyMap_factorThruImage :
    Epi (HomologicalComplex.homologyMap
      (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)) (-2)) :=
  HomologicalComplex.epi_homologyMap_of_epi_f _ (-2) inferInstance
    (by rw [CochainComplex.next]; exact mono_factorThruImage_f hmono (-2 + 1) (by omega))

/-! ### The morphism of triangles and the five lemma -/

variable (R A B P) in
/-- The comparison of the first vertices: `L_{B/R} ⊗^L_B (A ⊗_R B)`, computed degreewise, maps to
the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` through the base change of `L_{B/R} → L`. -/
def comparisonMor₁ :
    cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
      DerivedCategory.Q.obj (Abelian.image (P.tensorBaseChangeComplexMap A)) :=
  (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R B) (A ⊗[R] B)).hom ≫
    DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P) ≫
      Abelian.factorThruImage (P.tensorBaseChangeComplexMap A))

variable (R A B P) in
/-- The square formed by the canonical map `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`, the
canonical map `L_{A ⊗_R B/A} → L_A`, `comparisonMor₁` and the inclusion of the image into `L_A`
commutes in `D(A ⊗_R B)`. -/
theorem comparison_comm :
    cotangentTensorProductBaseChangeMapRight R A B ≫ DerivedCategory.Q.map (lsMapC R A B P) =
      comparisonMor₁ R A B P ≫
        DerivedCategory.Q.map (Abelian.image.ι (P.tensorBaseChangeComplexMap A)) := by
  have h : DerivedCategory.Q.map
      (cotangentExtendScalarsComplexMap (tensorProductIncludeRight R A B) ≫ lsMapC R A B P) =
      DerivedCategory.Q.map (((tensorExt R A B).map (lsMapB R B P) ≫
        Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)) ≫
          Abelian.image.ι (P.tensorBaseChangeComplexMap A)) :=
    (Q_map_lsSquare R A B P).trans (congrArg DerivedCategory.Q.map
      ((whisker_eq _ (Abelian.image.fac (P.tensorBaseChangeComplexMap A)).symm).trans
        (Category.assoc _ _ _).symm))
  exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Functor.map_comp _ _ _).symm.trans
    (h.trans (Functor.map_comp _ _ _)))).trans (Category.assoc _ _ _).symm)

section Triangle

variable {E : DerivedCategory (ModuleCat.{u} (A ⊗[R] B))}
  {b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E}
  {e : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
  (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _)

variable (P) in
/-- **The morphism of triangles** from the right column of Equation 92.15.0.1 to the triangle of
the short exact sequence `0 → Im ⟶ L_A ⟶ Coker → 0`, on the comparison maps of Tag 09CG. -/
def comparisonTriangleHom :
    Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ⟶
      DerivedCategory.triangleOfSES (tensorBaseChangeImageSES_shortExact R A B P) :=
  let h := complete_distinguished_triangle_morphism _ _ hE
    (DerivedCategory.triangleOfSES_distinguished (tensorBaseChangeImageSES_shortExact R A B P))
    (comparisonMor₁ R A B P) (DerivedCategory.Q.map (lsMapC R A B P)) (comparison_comm R A B P)
  { hom₁ := comparisonMor₁ R A B P
    hom₂ := DerivedCategory.Q.map (lsMapC R A B P)
    hom₃ := h.choose
    comm₁ := comparison_comm R A B P
    comm₂ := h.choose_spec.1
    comm₃ := h.choose_spec.2 }

end Triangle

variable (hproj : ∀ n : ℤ, -2 < n → Projective
  ((Algebra.Presentation.lichtenbaumSchlessingerComplex P).complex.X n))

include hmono in
/-- The map from `(A ⊗_R B) ⊗_B L` onto the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` is an isomorphism
on cohomology in `D(A ⊗_R B)` in every degree `≥ -1`. -/
theorem isIso_homologyFunctor_map_Q_map_factorThruImage (n : ℤ) (hn : -1 ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (DerivedCategory.Q.map (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)))) :=
  (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (A ⊗[R] B)) n)
    _).2 (isIso_homologyMap_factorThruImage hmono n hn)

include hmono in
/-- The map from `(A ⊗_R B) ⊗_B L` onto the image of `(A ⊗_R B) ⊗_B L ⟶ L_A` is onto on
cohomology in `D(A ⊗_R B)` in every degree `≥ -2`. -/
theorem epi_homologyFunctor_map_Q_map_factorThruImage (n : ℤ) (hn : -2 ≤ n) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (DerivedCategory.Q.map (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A)))) := by
  by_cases h : n = -2
  · rw [h]
    exact (epi_homologyFunctor_map_Q_map_iff _ _).2 (epi_homologyMap_factorThruImage hmono)
  · have := isIso_homologyFunctor_map_Q_map_factorThruImage hmono n (by omega)
    exact IsIso.epi_of_iso _

/-- On cohomology, `comparisonMor₁` is the composite of the termwise identification of the derived
base change, the base change of `L_{B/R} → L` and the map onto the image of
`(A ⊗_R B) ⊗_B L ⟶ L_A`. -/
theorem homologyFunctor_map_comparisonMor₁_eq (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map (comparisonMor₁ R A B P) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
          (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R B) (A ⊗[R] B)).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
          (DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P))) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
            (DerivedCategory.Q.map (Abelian.factorThruImage (P.tensorBaseChangeComplexMap A))) :=
  (Functor.map_comp _ _ _).trans (whisker_eq _
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (DerivedCategory.Q.map_comp _ _)).trans (Functor.map_comp _ _ _)))

include hmono hproj in
/-- The map `comparisonMor₁` is onto on cohomology in every degree `≥ -2`. -/
theorem epi_homologyFunctor_map_comparisonMor₁ (n : ℤ) (hn : -2 ≤ n) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
        (comparisonMor₁ R A B P)) := by
  rw [homologyFunctor_map_comparisonMor₁_eq]
  have h₁ := (homologyFunctor_map_Q_map_tensorExt_lsMapB (A := A) hproj n hn).1
  have h₃ := epi_homologyFunctor_map_Q_map_factorThruImage hmono n hn
  exact epi_comp _ _

include hmono hproj in
/-- The map `comparisonMor₁` is an isomorphism on cohomology in every degree `≥ -1`. -/
theorem isIso_homologyFunctor_map_comparisonMor₁ (n : ℤ) (hn : -1 ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
        (comparisonMor₁ R A B P)) := by
  rw [homologyFunctor_map_comparisonMor₁_eq]
  have h₁ := (homologyFunctor_map_Q_map_tensorExt_lsMapB (A := A) hproj n (by omega)).1
  have h₁' := (homologyFunctor_map_Q_map_tensorExt_lsMapB (A := A) hproj n (by omega)).2 hn
  have h₂ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (DerivedCategory.Q.map ((tensorExt R A B).map (lsMapB R B P)))) :=
    isIso_of_mono_of_epi _
  have h₃ := isIso_homologyFunctor_map_Q_map_factorThruImage hmono n hn
  exact IsIso.comp_isIso

variable {E : DerivedCategory (ModuleCat.{u} (A ⊗[R] B))}
  {b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E}
  {e : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
  (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _)

include hmono hproj hE in
/-- **The five lemma step.** In every degree `≥ -2` the third map of the morphism of triangles
is an isomorphism on cohomology. -/
theorem isIso_homologyMap_comparisonMor₃ (n : ℤ) (hn : -2 ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).map
      (comparisonTriangleHom P hE).hom₃) :=
  DerivedCategory.isIso_homologyFunctor_map_hom₃ hE
    (DerivedCategory.triangleOfSES_distinguished (tensorBaseChangeImageSES_shortExact R A B P))
    (comparisonTriangleHom P hE) n
    (epi_homologyFunctor_map_comparisonMor₁ hmono hproj n hn)
    (isIso_homologyFunctor_map_Q_map_lsMapC R A B P n hn)
    (isIso_homologyFunctor_map_comparisonMor₁ hmono hproj (n + 1) (by omega))
    (@IsIso.mono_of_iso _ _ _ _ _ (isIso_homologyFunctor_map_Q_map_lsMapC R A B P (n + 1)
      (by omega)))

include hepi hmono hproj hE in
/-- **The vanishing.** Under the three hypotheses on `(A ⊗_R B) ⊗_B L ⟶ L_A`, the object `E`
has no cohomology in degrees `≥ -1`. -/
theorem isZero_homology_of_tensorBaseChangeComplexMap (n : ℤ) (hn : -1 ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) n).obj E) := by
  have := isIso_homologyMap_comparisonMor₃ hmono hproj hE n (by omega)
  refine IsZero.of_iso ?_ (asIso ((DerivedCategory.homologyFunctor _ n).map
    (comparisonTriangleHom P hE).hom₃))
  refine ((DerivedCategory.homologyFunctorFactors _ n).app _).isZero_iff.2 ?_
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (isZero_cokernel_tensorBaseChangeComplexMap_X hepi n (by omega))

include hepi hmono hproj hE in
/-- **The degree `-2` cohomology.** Under the three hypotheses on `(A ⊗_R B) ⊗_B L ⟶ L_A`, the
degree `-2` cohomology of `E` is the cokernel of that map in degree `-2`. -/
def homologyNegTwoIsoCokernel :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj E ≅
      cokernel ((P.tensorBaseChangeComplexMap A).f (-2)) :=
  have := isIso_homologyMap_comparisonMor₃ hmono hproj hE (-2) le_rfl
  let K := cokernel (P.tensorBaseChangeComplexMap A)
  asIso ((DerivedCategory.homologyFunctor _ (-2)).map (comparisonTriangleHom P hE).hom₃) ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-2)).app K ≪≫
    (K.isoHomologyπ (-3) (-2) (by simp)
      ((isZero_cokernel_tensorBaseChangeComplexMap_X hepi (-3) (by omega)).eq_of_src _ _)).symm ≪≫
    K.iCyclesIso (-2) (-1) (by simp)
      ((isZero_cokernel_tensorBaseChangeComplexMap_X hepi (-1) (by omega)).eq_of_tgt _ _) ≪≫
    cokernelXIso _ (-2)

end CommAlgCat
