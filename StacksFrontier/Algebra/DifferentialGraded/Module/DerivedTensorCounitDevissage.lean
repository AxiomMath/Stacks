module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorCoproduct
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryProducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPFiltrationInduction
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure

/-! # The closure properties of the comparison from the derived to the plain tensor product

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. The comparison
`DifferentialGraded.Bimodule.derivedTensorFunctorCounit` of Tag 0BZ2 is a morphism
`- ⊗_A^𝐋 N ⟶ - ⊗_A N` of functors `K(A, d) ⥤ D(B, d)`. This file collects the closure properties
of the class of differential graded `A`-modules at which that comparison is invertible: direct
sums, translations, and the two remaining terms of an admissible short exact sequence.

## Main results

* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_propertyP`: the comparison
  is invertible at a module with property (P).
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_directSumObj`: invertibility
  passes to a direct sum.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_shift` and
  `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_shiftObj`: invertibility
  passes to a translation.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_middle_of_admissible` and
  `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_quotient_of_admissible`:
  invertibility at two terms of an admissible short exact sequence gives it at the third.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_iff_quasiIso`: **the
  comparison at `M` is invertible exactly when the plain tensor product of a property-(P)
  resolution `P → M` with `N` is a quasi-isomorphism.**

## Implementation notes

The closure properties are instances of generic dévissage lemmas for a morphism between exact
functors that preserve the colimit in question and are compatible with the translation, collected
in the namespace `StacksDraft.NatTransDevissage`. Exactness of `- ⊗_A^𝐋 N` is
`DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated`, exactness of `- ⊗_A N` on
homotopy categories is Tag 09LR, and the compatibility of the comparison with the translation is
`DifferentialGraded.Bimodule.derivedTensorFunctorCounit_commShift`.

The direct sum step is proved on the plain side, through
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_iff_quasiIso`: each module of
the family is resolved by one orthogonal on the left to the acyclic modules, and the direct sum
of those resolutions is again orthogonal on the left
(`DifferentialGradedModule.leftOrthogonal_acyclic_directSumObj`).

## References

* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2), the comparison.
* [Stacks Project, Tag 09LR](https://stacks.math.columbia.edu/tag/09LR), exactness of the plain
  tensor functor.
* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT), the adjunction.
* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW), saturation of the
  quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped DirectSum

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'


universe u

namespace StacksDraft.NatTransDevissage


/-! ### Generic dévissage lemmas for a morphism of functors -/

section Colimits

variable {D : Type*} [Category D] {D' : Type*} [Category D'] {F G : D ⥤ D'} (τ : F ⟶ G)

/-- Invertibility of `τ` at an object only depends on the isomorphism class of that object. -/
lemma isIso_app_of_iso {X Y : D} (e : X ≅ Y) (hX : IsIso (τ.app X)) : IsIso (τ.app Y) := by
  have h : τ.app Y = inv (F.map e.hom) ≫ τ.app X ≫ G.map e.hom := by
    rw [← τ.naturality e.hom, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- If `τ` is invertible on a diagram whose colimit both `F` and `G` preserve, it is invertible
at the colimit. -/
lemma isIso_app_of_isColimit {J : Type*} [Category J] (Z : J ⥤ D) {c : Cocone Z}
    (hc : IsColimit c) [PreservesColimit Z F] [PreservesColimit Z G]
    (h : ∀ j, IsIso (τ.app (Z.obj j))) : IsIso (τ.app c.pt) := by
  have hF := isColimitOfPreserves F hc
  have hG := isColimitOfPreserves G hc
  have heq : τ.app c.pt =
      (IsColimit.coconePointsIsoOfNatIso hF hG
        (NatIso.ofComponents (fun j => asIso (τ.app (Z.obj j))) (fun _ => by simp))).hom := by
    refine hF.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact τ.naturality (c.ι.app j)
  rw [heq]
  infer_instance

end Colimits

section Shift

variable {D : Type*} [Category D] [HasShift D ℤ] {D' : Type*} [Category D'] [HasShift D' ℤ]
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- The morphism of triangles `F.mapTriangle.obj T ⟶ G.mapTriangle.obj T` induced by a morphism
`τ : F ⟶ G` of functors compatible with the shift. All three components are `τ` itself. -/
def mapTriangleHom (T : Triangle D) : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := τ.app _
  hom₂ := τ.app _
  hom₃ := τ.app _
  comm₁ := τ.naturality _
  comm₂ := τ.naturality _
  comm₃ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => F.map T.mor₃ ≫ z)
          (NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
              (τ.naturality T.mor₃)).trans (Category.assoc _ _ _))))

/-- If `τ` is invertible at `X` it is invertible at every shift of `X`. -/
lemma isIso_app_shift {X : D} (hX : IsIso (τ.app X)) (n : ℤ) : IsIso (τ.app (X⟦n⟧)) := by
  rw [NatTrans.app_shift τ n X]
  infer_instance

end Shift

section Triangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type*} [Category D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- If `τ` is invertible at the first two vertices of a distinguished triangle it is invertible
at the third. -/
lemma isIso_app_obj₃ (T : Triangle D) (hT : T ∈ distTriang D) (h₁ : IsIso (τ.app T.obj₁))
    (h₂ : IsIso (τ.app T.obj₂)) : IsIso (τ.app T.obj₃) :=
  isIso₃_of_isIso₁₂ (mapTriangleHom τ T) (F.map_distinguished T hT)
    (G.map_distinguished T hT) h₁ h₂

/-- If `τ` is invertible at the outer two vertices of a distinguished triangle it is invertible
at the middle one. -/
lemma isIso_app_obj₂ (T : Triangle D) (hT : T ∈ distTriang D) (h₁ : IsIso (τ.app T.obj₁))
    (h₃ : IsIso (τ.app T.obj₃)) : IsIso (τ.app T.obj₂) :=
  isIso₂_of_isIso₁₃ (mapTriangleHom τ T) (F.map_distinguished T hT)
    (G.map_distinguished T hT) h₁ h₃

end Triangulated

end StacksDraft.NatTransDevissage

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- **A morphism of `K(A, d)` becomes invertible in `D(A, d)` exactly when it is a
quasi-isomorphism.** -/
theorem isIso_q_map_iff_quasiIsomorphisms {X Y : HomotopyCategory A} (s : X ⟶ Y) :
    IsIso ((quasiIsomorphisms' A).Q.map s) ↔ quasiIsomorphisms' A s := by
  rw [← MorphismProperty.mem_invertedClosure_iff,
    (quasiIsomorphisms_isSaturated' A).invertedClosure_eq]

/-- **A homomorphism of differential graded modules becomes invertible in `D(A, d)` exactly when
it is a quasi-isomorphism.** -/
theorem isIso_q_map_toHomotopyCategory_map_iff {M N : DifferentialGradedModule A} (f : M ⟶ N) :
    IsIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f)) ↔
      QuasiIso ((forgetToCochainComplex A).map f) :=
  (isIso_q_map_iff_quasiIsomorphisms A _).trans (quasiIsomorphisms_map_iff' A f)

/-- **A functor preserving two direct sums inverts the map between them induced by a family of
morphisms it inverts.** -/
theorem isIso_map_directSumMap {ι : Type u} [DecidableEq ι]
    (N : ι → DifferentialGradedModule A) {N' : ι → DifferentialGradedModule A}
    (f : ∀ i, N i ⟶ N' i)
    {E : Type*} [Category E] (Φ : DifferentialGradedModule A ⥤ E)
    [PreservesColimit (Discrete.functor N) Φ] [PreservesColimit (Discrete.functor N') Φ]
    (hf : ∀ i, IsIso (Φ.map (f i))) : IsIso (Φ.map (directSumMap N f)) := by
  have hc := isColimitOfPreserves Φ (isColimit_directSumObj N)
  have hc' := isColimitOfPreserves Φ (isColimit_directSumObj N')
  let β : Discrete.functor N ⋙ Φ ≅ Discrete.functor N' ⋙ Φ :=
    Discrete.natIso (fun j => asIso (Φ.map (f j.as)))
  have heq : Φ.map (directSumMap N f) =
      (IsColimit.coconePointsIsoOfNatIso hc hc' β).hom := by
    refine hc.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    change Φ.map (directSumInj N j.as) ≫ Φ.map (directSumMap N f) =
      Φ.map (f j.as) ≫ Φ.map (directSumInj N' j.as)
    rw [← Φ.map_comp, ← Φ.map_comp]
    exact congrArg Φ.map (directSumInj_comp_directSumDesc N _ j.as)
  rw [heq]
  infer_instance

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule StacksDraft.NatTransDevissage

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-! ### The comparison at a module with property (P) -/

/-- **The comparison `P ⊗_A^𝐋 N → P ⊗_A N` is invertible at a module with property (P).** -/
theorem isIso_derivedTensorFunctorCounit_app_of_propertyP (N : Bimodule A B)
    (P : DifferentialGradedModule A) (hP : Nonempty (PropertyPFiltration P)) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj P)) :=
  isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N _
    (leftOrthogonal_acyclic_of_propertyP hP.some)

/-! ### The plain side of the comparison and direct sums -/

/-- The plain side of the comparison, read as a functor on `Mod_{(A, d)}`, preserves the direct
sum of a family of differential graded modules. -/
theorem preservesColimit_tensorFunctorToDerivedCategory (N : Bimodule A B) {ι : Type u}
    (M : ι → DifferentialGradedModule A) :
    PreservesColimit (Discrete.functor M)
      (tensorCompFunctor N ⋙ toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q) := by
  have := preservesColimit_tensorCompFunctor N M
  have : PreservesColimit (Discrete.functor M ⋙ tensorCompFunctor N)
      (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q) := inferInstance
  infer_instance

/-! ### The criterion in terms of the plain tensor product -/

/-- **The comparison at `M` is invertible exactly when the plain tensor product with `N` of a
resolution `P → M` by a left-orthogonal module is a quasi-isomorphism.** -/
theorem isIso_derivedTensorFunctorCounit_app_iff_quasiIso (N : Bimodule A B)
    {P M : DifferentialGradedModule A} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex A).map f))
    (hP : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P)) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) ↔
      QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor N).map f)) := by
  have hPiso := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N _ hP
  have hfiso : IsIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f)) :=
    (isIso_q_map_toHomotopyCategory_map_iff A f).2 hf
  have hTf : IsIso (((quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N).map
      ((toHomotopyCategory A).map f)) := by
    change IsIso ((derivedTensorFunctor N).map
      ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map f)))
    infer_instance
  have hplain :
      IsIso ((tensorFunctorToDerivedCategory N).map ((toHomotopyCategory A).map f)) ↔
        QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor N).map f)) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (tensorCompFunctor_quotient N) (quasiIsomorphisms' B).Q)
        f).symm.trans (isIso_q_map_toHomotopyCategory_map_iff B ((tensorCompFunctor N).map f))
  rw [← hplain]
  have hnat := (derivedTensorFunctorCounit N).naturality ((toHomotopyCategory A).map f)
  refine ⟨fun hM => ?_, fun hordinary => ?_⟩
  · have : IsIso (((quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N).map
        ((toHomotopyCategory A).map f) ≫ (derivedTensorFunctorCounit N).app _) := inferInstance
    exact IsIso.of_isIso_fac_left (f := (derivedTensorFunctorCounit N).app _) hnat.symm
  · have : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj P) ≫
        (tensorFunctorToDerivedCategory N).map ((toHomotopyCategory A).map f)) := inferInstance
    exact IsIso.of_isIso_fac_left (f := ((quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N).map
      ((toHomotopyCategory A).map f)) hnat

/-- **The comparison at `M` is invertible exactly when the plain tensor product with `N` of a
property-(P) resolution `P → M` is a quasi-isomorphism.** -/
theorem isIso_derivedTensorFunctorCounit_app_iff_quasiIso_of_propertyP (N : Bimodule A B)
    {P M : DifferentialGradedModule A} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex A).map f))
    (hP : Nonempty (PropertyPFiltration P)) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) ↔
      QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor N).map f)) :=
  isIso_derivedTensorFunctorCounit_app_iff_quasiIso N f hf
    (leftOrthogonal_acyclic_of_propertyP hP.some)

/-! ### The closure properties -/

/-- **Invertibility of the comparison passes to a direct sum.** -/
theorem isIso_derivedTensorFunctorCounit_app_directSumObj (N : Bimodule A B) {ι : Type u}
    [DecidableEq ι] (M : ι → DifferentialGradedModule A)
    (h : ∀ i, IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj (M i)))) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj (directSumObj M))) := by
  choose P g hg hPorth using fun i => exists_quasiIso_leftOrthogonal_acyclic A (M i)
  have := preservesColimit_tensorFunctorToDerivedCategory N P
  have := preservesColimit_tensorFunctorToDerivedCategory N M
  refine (isIso_derivedTensorFunctorCounit_app_iff_quasiIso N (directSumMap P g)
    (quasiIso_directSumMap P g
      (fun i => isQuasiIsomorphism_of_quasiIso (g i) (hg i)))
    (leftOrthogonal_acyclic_directSumObj P hPorth)).2 ?_
  rw [← isIso_q_map_toHomotopyCategory_map_iff B]
  exact isIso_map_directSumMap A P g
    (tensorCompFunctor N ⋙ toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q)
    (fun i => (isIso_q_map_toHomotopyCategory_map_iff B _).2
      ((isIso_derivedTensorFunctorCounit_app_iff_quasiIso N (g i) (hg i) (hPorth i)).1 (h i)))

/-- **Invertibility of the comparison passes to a translation.** -/
theorem isIso_derivedTensorFunctorCounit_app_shift (N : Bimodule A B) (X : HomotopyCategory A)
    (k : ℤ) (h : IsIso ((derivedTensorFunctorCounit N).app X)) :
    IsIso ((derivedTensorFunctorCounit N).app (X⟦k⟧)) :=
  isIso_app_shift (derivedTensorFunctorCounit N) h k

/-- The image in `K(A, d)` of a translated differential graded module is the translation of its
image. -/
theorem toHomotopyCategory_obj_shift (A : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule A) (k : ℤ) :
    ((toHomotopyCategory A).obj M)⟦k⟧ = (toHomotopyCategory A).obj (shift M k) := by
  rw [Quotient.functor_obj_shift]
  exact congrArg (fun F : DifferentialGradedModule A ⥤ DifferentialGradedModule A => _root_.id
    ((toHomotopyCategory A).obj (F.obj M))) (shiftFunctor_eq_shiftFunctor (A := A) k)

/-- **Invertibility of the comparison passes to a translated module.** -/
theorem isIso_derivedTensorFunctorCounit_app_shiftObj (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ)
    (h : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M))) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj (shift M k))) :=
  isIso_app_of_iso (derivedTensorFunctorCounit N)
    (eqToIso (toHomotopyCategory_obj_shift A M k))
    (isIso_app_shift (derivedTensorFunctorCounit N) h k)

/-- **Invertibility of the comparison at the outer terms of an admissible short exact sequence
gives it at the middle term.** -/
theorem isIso_derivedTensorFunctorCounit_app_middle_of_admissible (N : Bimodule A B)
    {K L M : DifferentialGradedModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hip : IsAdmissibleShortExact i p)
    (hK : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj K)))
    (hM : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M))) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj L)) :=
  isIso_app_obj₂ (derivedTensorFunctorCounit N) (associatedTriangle A i p hip)
    (associatedTriangle_mem_distTriang A i p hip) hK hM

/-- **Invertibility of the comparison at the first two terms of an admissible short exact
sequence gives it at the quotient.** -/
theorem isIso_derivedTensorFunctorCounit_app_quotient_of_admissible (N : Bimodule A B)
    {K L M : DifferentialGradedModule A} (i : K ⟶ L) (p : L ⟶ M)
    (hip : IsAdmissibleShortExact i p)
    (hK : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj K)))
    (hL : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj L))) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) :=
  isIso_app_obj₃ (derivedTensorFunctorCounit N) (associatedTriangle A i p hip)
    (associatedTriangle_mem_distTriang A i p hip) hK hL

/-- Invertibility of the comparison only depends on the isomorphism class of the module. -/
theorem isIso_derivedTensorFunctorCounit_app_of_iso (N : Bimodule A B)
    {M M' : DifferentialGradedModule A} (e : M ≅ M')
    (h : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M))) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M')) :=
  isIso_app_of_iso (Functor.whiskerLeft (toHomotopyCategory A) (derivedTensorFunctorCounit N))
    e h

end DifferentialGraded.Bimodule

end
