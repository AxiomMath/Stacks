module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftFlipApp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.LeftFactorTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESNatTrans
public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Connecting maps of `P ⊗^L (short exact sequence)` for a K-flat complex `P`

Let `X` be a ringed space, `P` a K-flat complex of `O_X`-modules and
`0 → A₁ → A₂ → A₃ → 0` a short exact sequence of `O_X`-modules. Tensoring the distinguished
triangle of the sequence with `P` in `D(O_X)` gives a distinguished triangle, whose connecting
map on cohomology sheaves is
`H^{n₀}(P ⊗^L A₃) ⟶ H^{n₁}(P ⊗^L A₁)`, `n₀ + 1 = n₁`.
Since `P` is K-flat, `P ⊗^L A` is computed by the total complex `Tot(P ⊗ A)`. When the sequence
of total complexes `0 → Tot(P ⊗ A₁) → Tot(P ⊗ A₂) → Tot(P ⊗ A₃) → 0` is short exact, it has its
own snake-lemma connecting map on cohomology, and this file proves that the two connecting maps
agree under the identifications `H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))`.

## Main definitions

All declarations are in the namespace `Stacks.IdealTorsion.ReductionDerived`.

* `toTensorNatTrans`: the canonical map `Q P ⊗^L Q L ⟶ Q Tot(P ⊗ L)`, as a transformation
  natural in the complex `L`.
* `derivedTensorSingleHomologyIso`: the identification `H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))` for a
  K-flat `P` and a sheaf `A` placed in degree `0`.

## Main results

* `map_descShortComplex_eq_bifunctorMappingConeIso`: the cone comparison
  `Tot(F(G, cone φ)) ≅ cone(Tot(F(G, φ)))` is compatible with the projections of mapping cones
  to the third term of a short complex.
* `toTensorNatTrans_commShift`: the canonical map commutes with the shifts, for the
  commutation of `Q P ⊗^L -` with the shift that is the structure field of the derived tensor
  product.
* `homologySequenceδ_mapTriangle_triangleOfSES_toTensorNatTrans`: the canonical map
  intertwines the connecting maps of `Q P ⊗^L (triangle of S)` and of the triangle of
  `Tot(P ⊗ S)`, for a short exact sequence `S` of complexes.
* `derivedTensorSingleHomologyIso_hom_naturality`: the identification
  `H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))` is natural in the sheaf.
* `homologySequenceδ_mapTriangle_singleTriangle`: the connecting map of
  `P ⊗^L (triangle of the sequence)` is the snake-lemma connecting map of the sequence of total
  complexes.

## Implementation notes

The comparison of the two connecting maps is a morphism of triangles from the image under
`Q P ⊗^L -` of the triangle of the sequence of single complexes to the triangle of the sequence
of total complexes (`DerivedCategory.triangleOfSESNatTrans`), whose components are the canonical
maps to the total tensor complex. Its third square needs two inputs: the canonical map commutes
with the shifts, and the total complex `Tot(P ⊗ -)` carries the mapping cone of a morphism to
the mapping cone of its image compatibly with the projections of the mapping-cone triangle.

The shift compatibility of the canonical map is
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShift₂`, which is stated for the
curried form of the canonical map and for shift data transported to the curried functors. The
two identifications of curried functors with `Q ⋙ (Q P ⊗^L -)` and `Tot(P ⊗ -) ⋙ Q` used here
are components of the isomorphisms along which those data were transported, so that their
compatibility with the shifts is `CategoryTheory.Functor.CommShift.ofIso_compatibility`. The
only datum which is not definitionally the one wanted is that of the derived tensor product:
the transported datum is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, while the Bockstein
operator uses the structure field `commShift₂`; the two are equal by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`.

The cone comparison for the left factor is
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso`; its compatibility with
`CochainComplex.mappingCone.descShortComplex` is proved here.

The passage from the triangle of the sequence of single complexes to the single triangle
`ShortComplex.ShortExact.singleTriangle`, and from `S.map (single ⋙ Tot(P ⊗ -))` to
`(S.map single).map Tot(P ⊗ -)`, are definitional equalities. Checked at the concrete total
tensor complex, they unfold the tensor product of sheaves and exhaust the heartbeat budget, so
they are proved once for an arbitrary functor `Ψ` and transformation `τ`, where unfolding is
cheap, and the concrete statement is obtained by instantiating that lemma. For the same reason
the concrete proofs chain their steps with `Eq.trans` and `congrArg` instead of `rw`, whose
motives are checked at a transparency at which the objects do not unify.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Pretriangulated

universe u

namespace Stacks.IdealTorsion.ReductionDerived

/-! ### The cone comparison of a total complex with a fixed left factor -/

section Generic

open Stacks.SheafOfModules.Tensor.Reduction CochainComplex.HomComplex

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex B (ComplexShape.up ℤ)), K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (G : HomologicalComplex A (ComplexShape.up ℤ))

attribute [local instance] map₂HomologicalComplex_obj_additive

/-- The transport of the zero cochain through `Tot(F(G, -))` is zero. -/
private theorem Ψcoch_zero {K L : CochainComplex B ℤ} {n : ℤ} :
    Ψcoch F G (0 : Cochain K L n) = 0 := by
  apply Cochain.ext
  intro a a' h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq2 : p + q = a := hpq
  rw [Ψcoch_v F G (0 : Cochain K L n) a a' h p q hpq2]
  simp only [Cochain.zero_v, Functor.map_zero, zero_comp, smul_zero, Cochain.zero_v]
  exact comp_zero.symm

/-- The first summand of a mapping cone is killed by the projection to the third term of the
short complex. -/
private theorem inl_v_descShortComplex_f (S' : ShortComplex (CochainComplex D ℤ)) (p q : ℤ)
    (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl S'.f).v p q h ≫
      (CochainComplex.mappingCone.descShortComplex S').f q = 0 := by
  simp [CochainComplex.mappingCone.descShortComplex]

/-- **The cone comparison `Tot(F(G, cone φ)) ≅ cone(Tot(F(G, φ)))` is compatible with the
projections onto the third term** of a short complex. -/
public theorem map_descShortComplex_eq_bifunctorMappingConeIso
    (S : ShortComplex (CochainComplex B ℤ)) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).map (CochainComplex.mappingCone.descShortComplex S) =
      (bifunctorMappingConeIso F G S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex
          (S.map ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj G)) := by
  have hinl : (CochainComplex.mappingCone.inl S.f).comp
      (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S)) (add_zero _) = 0 :=
    CochainComplex.mappingCone.inl_desc _ _ _ _
  rw [← Iso.inv_comp_eq]
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.mappingCone.ext_from (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).map S.f) (n + 1) n rfl
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    simp only [bifunctorMappingConeIso]
    rw [CochainComplex.mappingCone.inl_v_desc_f]
    have e1 : (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).map (CochainComplex.mappingCone.descShortComplex S)).f n =
        (Ψcoch F G (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S))).v n n
          (add_zero n) := by
      rw [Ψcoch_ofHom, Cochain.ofHom_v]
    rw [e1, ← Cochain.comp_v _ _ (add_zero (-1)) (n + 1) n n (by omega) (by omega),
      ← Ψcoch_comp, hinl, Ψcoch_zero, Cochain.zero_v]
    exact (inl_v_descShortComplex_f (S.map ((F.map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G)) (n + 1) n (by omega)).symm
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    simp only [bifunctorMappingConeIso]
    rw [CochainComplex.mappingCone.inr_f_desc_f, ← HomologicalComplex.comp_f,
      ← Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex,
      ← HomologicalComplex.comp_f]
    exact (congrArg (fun φ => φ.f n)
      (CochainComplex.mappingCone.inr_descShortComplex (S.map ((F.map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G)))).symm

/-- **The cone comparison is compatible with the third morphisms of the cone triangles**, for
Mathlib's commutation of `Tot(F(G, -))` with the shift. -/
public theorem map_mappingConeTriangle_mor₃_eq_bifunctorMappingConeIso {K L : CochainComplex B ℤ}
    (φ : K ⟶ L) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).commShiftIso (1 : ℤ)).hom.app K =
      (bifunctorMappingConeIso F G φ).hom ≫
        (CochainComplex.mappingCone.triangle (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).map φ)).mor₃ := by
  have h := (bifunctorMapTriangleIso F G φ).hom.comm₃
  have h1 : (bifunctorMapTriangleIso F G φ).hom.hom₁ = 𝟙 _ := rfl
  have h3 : (bifunctorMapTriangleIso F G φ).hom.hom₃ = (bifunctorMappingConeIso F G φ).hom :=
    rfl
  rw [h1, h3] at h
  refine Eq.trans ?_ h
  exact (Category.comp_id _).symm.trans (congrArg _
    (CategoryTheory.Functor.map_id (shiftFunctor (HomologicalComplex D (ComplexShape.up ℤ))
      (1 : ℤ)) _).symm)

end Generic

/-- The snake-lemma connecting map of a short exact sequence `S.map (F ⋙ Ψ)` is the one of
`(S.map F).map Ψ`: the two short complexes agree by definition. -/
private theorem shortExact_δ_map_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] (F : C ⥤ CochainComplex D ℤ)
    (Ψ : CochainComplex D ℤ ⥤ CochainComplex E ℤ) [F.PreservesZeroMorphisms]
    [Ψ.PreservesZeroMorphisms] {S : ShortComplex C} (h₁ : (S.map (F ⋙ Ψ)).ShortExact)
    (h₂ : ((S.map F).map Ψ).ShortExact) (n₀ n₁ : ℤ) (h : (ComplexShape.up ℤ).Rel n₀ n₁) :
    h₁.δ n₀ n₁ h = h₂.δ n₀ n₁ h :=
  rfl

/-! ### Connecting maps of single triangles, for an arbitrary transformation -/

section GenericSingle

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  (Ψ : CochainComplex C ℤ ⥤ CochainComplex C ℤ) [Ψ.PreservesZeroMorphisms]
  (G : DerivedCategory C ⥤ DerivedCategory C) [G.CommShift ℤ]
  (τ : DerivedCategory.Q ⋙ G ⟶ Ψ ⋙ DerivedCategory.Q)

local notation "single₀" => HomologicalComplex.single C (ComplexShape.up ℤ) 0

/-- Let `τ : Q ⋙ G ⟶ Ψ ⋙ Q` and let `S` be a short exact sequence in `C` such that the image of
the sequence of single complexes under `Ψ` is short exact. If `τ` intertwines the connecting
maps of `G (triangle of the single complexes)` and of the triangle of their image under `Ψ`,
then it intertwines the connecting map of `G (triangle of S)` with the snake-lemma connecting
map of the image under `Ψ`, read through `DerivedCategory.homologyFunctorFactors`. -/
private theorem homologySequenceδ_mapTriangle_singleTriangle_of_natTrans
    {S : ShortComplex C} (hS : S.ShortExact)
    (hS₀ : (S.map single₀).ShortExact)
    (hS' : (S.map (single₀ ⋙ Ψ)).ShortExact)
    (hS'' : ((S.map single₀).map Ψ).ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hcx : DerivedCategory.HomologySequence.δ
          (G.mapTriangle.obj (DerivedCategory.triangleOfSES hS₀)) n₀ n₁ h ≫
        (DerivedCategory.homologyFunctor C n₁).map
          (τ.app (S.map single₀).X₁) =
      (DerivedCategory.homologyFunctor C n₀).map
          (τ.app (S.map single₀).X₃) ≫
        DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS'') n₀ n₁ h) :
    DerivedCategory.HomologySequence.δ (G.mapTriangle.obj hS.singleTriangle) n₀ n₁ h ≫
      ((DerivedCategory.homologyFunctor C n₁).map
          (G.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app S.X₁) ≫
            τ.app ((single₀).obj S.X₁)) ≫
        (DerivedCategory.homologyFunctorFactors C n₁).hom.app
          (Ψ.obj ((single₀).obj S.X₁))) =
    ((DerivedCategory.homologyFunctor C n₀).map
          (G.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app S.X₃) ≫
            τ.app ((single₀).obj S.X₃)) ≫
        (DerivedCategory.homologyFunctorFactors C n₀).hom.app
          (Ψ.obj ((single₀).obj S.X₃))) ≫
      hS'.δ n₀ n₁ h := by
  have he : ∀ A : C, G.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app A) ≫
      τ.app ((single₀).obj A) = τ.app ((single₀).obj A) := fun A => by
    have he' : (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app A = 𝟙 _ := rfl
    rw [he', CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hδ : DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS'') n₀ n₁ h ≫
        (DerivedCategory.homologyFunctorFactors C n₁).hom.app ((S.map single₀).map Ψ).X₁ =
      (DerivedCategory.homologyFunctorFactors C n₀).hom.app ((S.map single₀).map Ψ).X₃ ≫
        hS''.δ n₀ n₁ h :=
    (DerivedCategory.homologySequenceδ_triangleOfSES hS'' n₀ n₁ h).symm
  -- The steps below cross definitional equalities (the single triangle of `S` is the triangle of
  -- the sequence of single complexes, and `S.map (single₀ ⋙ Ψ)` is `(S.map single₀).map Ψ`)
  -- under which the types of the two sides change, so they are chained with `Eq.trans`.
  refine Eq.trans (b := DerivedCategory.HomologySequence.δ
      (G.mapTriangle.obj hS.singleTriangle) n₀ n₁ h ≫
        ((DerivedCategory.homologyFunctor C n₁).map (τ.app ((single₀).obj S.X₁)) ≫
          (DerivedCategory.homologyFunctorFactors C n₁).hom.app (Ψ.obj ((single₀).obj S.X₁))))
    (congrArg (fun t => DerivedCategory.HomologySequence.δ
      (G.mapTriangle.obj hS.singleTriangle) n₀ n₁ h ≫
        ((DerivedCategory.homologyFunctor C n₁).map t ≫
          (DerivedCategory.homologyFunctorFactors C n₁).hom.app (Ψ.obj ((single₀).obj S.X₁))))
      (he S.X₁)) ?_
  refine Eq.trans (b := DerivedCategory.HomologySequence.δ
      (G.mapTriangle.obj (DerivedCategory.triangleOfSES hS₀)) n₀ n₁ h ≫
        ((DerivedCategory.homologyFunctor C n₁).map (τ.app (S.map single₀).X₁) ≫
          (DerivedCategory.homologyFunctorFactors C n₁).hom.app ((S.map single₀).map Ψ).X₁))
    rfl ?_
  refine Eq.trans (b := ((DerivedCategory.homologyFunctor C n₀).map (τ.app (S.map single₀).X₃) ≫
      (DerivedCategory.homologyFunctorFactors C n₀).hom.app ((S.map single₀).map Ψ).X₃) ≫
        hS''.δ n₀ n₁ h)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcx).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hδ).trans (Category.assoc _ _ _).symm))))
    ?_
  refine Eq.trans (b := ((DerivedCategory.homologyFunctor C n₀).map (τ.app ((single₀).obj S.X₃)) ≫
      (DerivedCategory.homologyFunctorFactors C n₀).hom.app (Ψ.obj ((single₀).obj S.X₃))) ≫
        hS'.δ n₀ n₁ h) rfl ?_
  exact congrArg (fun t => ((DerivedCategory.homologyFunctor C n₀).map t ≫
      (DerivedCategory.homologyFunctorFactors C n₀).hom.app (Ψ.obj ((single₀).obj S.X₃))) ≫
        hS'.δ n₀ n₁ h) (he S.X₃).symm

end GenericSingle

/-! ### The canonical map to the total tensor complex, with a fixed left factor -/

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf

/-- `Tot(P ⊗ -)` is additive. -/
public instance tensorComplex_obj_additive (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).Additive :=
  Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive _ P

/-- `Tot(P ⊗ -)` commutes with the shift, by Mathlib's commutation of the total complex of a
bifunctor with the shift in the second variable. -/
public noncomputable instance tensorComplex_obj_commShift
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).CommShift ℤ :=
  inferInstanceAs (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.sheaf).map₂CochainComplex.obj P).CommShift ℤ)

section AnyModel

variable [HasDerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)]

/-- **The canonical map `Q P ⊗^L Q L ⟶ Q Tot(P ⊗ L)`**, as a transformation natural in the
complex `L`: its components are `DerivedTensorProduct.toTensor` of the derived tensor product of
`X`. -/
public noncomputable def toTensorNatTrans (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    DerivedCategory.Q ⋙ (canonicalDerivedTensorProduct X.sheaf).tensor.obj
        (DerivedCategory.Q.obj P) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P ⋙ DerivedCategory.Q where
  app L := (canonicalDerivedTensorProduct X.sheaf).toTensor P L
  naturality L L' g := by
    have h := (canonicalDerivedTensorProduct X.sheaf).toTensor_naturality (𝟙 P) g
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
    exact h

/-- The component of `toTensorNatTrans` at `L` is the canonical map at `(P, L)`. -/
@[simp]
public theorem toTensorNatTrans_app (P L : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    (toTensorNatTrans X P).app L = (canonicalDerivedTensorProduct X.sheaf).toTensor P L :=
  rfl

/-! ### Cohomology of `P ⊗^L A` for a sheaf `A` -/

omit [HasDerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)] in
/-- The K-flatness of `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback`, the predicate of the
K-flat resolutions of a ringed space, is the K-flatness asked for by the comparisons of the
derived tensor product. -/
public theorem kFlat_of_kFlatDerivedPullback {P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ}
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P) :
    Stacks.SheafOfModules.KFlat X.sheaf P :=
  (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.sheaf P).2 hP

/-- For a K-flat complex `P`, the canonical map `Q P ⊗^L Q L ⟶ Q Tot(P ⊗ L)` is an isomorphism:
it is the K-flat comparison `DerivedTensorProduct.comparisonLeft`. -/
public theorem isIso_toTensorNatTrans_app (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (L : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) : IsIso ((toTensorNatTrans X P).app L) := by
  rw [toTensorNatTrans_app, (canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonLeft _ _
    (kFlat_of_kFlatDerivedPullback X hP)]
  infer_instance

/-- **`H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))`** for a K-flat complex `P` and a sheaf `A` placed in
degree `0`: the cohomology of the canonical map `Q P ⊗^L Q A ⟶ Q Tot(P ⊗ A)`, which for a
K-flat left factor is the comparison `DerivedTensorProduct.comparisonLeft`
(`isIso_toTensorNatTrans_app`), read through `DerivedCategory.singleFunctorIsoCompQ` and the
identification `DerivedCategory.homologyFunctorFactors` of the cohomology of the image of a
complex in the derived category with its cohomology. -/
public noncomputable def derivedTensorSingleHomologyIso
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (A : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj
        (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor _ 0).obj A)) ≅
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A)).homology n :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app A) ≪≫
        @asIso _ _ _ _ ((toTensorNatTrans X P).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A))
          (isIso_toTensorNatTrans_app X P hP _)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app _

/-- The identification `H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))` is the cohomology of the canonical
map to the total tensor complex. -/
public theorem derivedTensorSingleHomologyIso_hom (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (A : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (derivedTensorSingleHomologyIso X P hP A n).hom =
      (DerivedCategory.homologyFunctor _ n).map
          (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
              ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app A) ≫
            (toTensorNatTrans X P).app
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A)) ≫
        (DerivedCategory.homologyFunctorFactors _ n).hom.app _ :=
  rfl

/-- **The identification `H^n(P ⊗^L A) ≅ H^n(Tot(P ⊗ A))` is natural in the sheaf `A`.** -/
public theorem derivedTensorSingleHomologyIso_hom_naturality
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    {A B : SheafOfModules.{u} Oₓ} (g : A ⟶ B) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map
        (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
          ((DerivedCategory.singleFunctor _ 0).map g)) ≫
      (derivedTensorSingleHomologyIso X P hP B n).hom =
    (derivedTensorSingleHomologyIso X P hP A n).hom ≫
      HomologicalComplex.homologyMap
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)) n := by
  have hsf : (DerivedCategory.singleFunctor _ 0).map g ≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app B =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app A ≫
        DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.naturality g
  have key : ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
        (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)) ≫
      (toTensorNatTrans X P).app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B) =
      (toTensorNatTrans X P).app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)) :=
    (toTensorNatTrans X P).naturality ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)
  have hF := DerivedCategory.homologyFunctorFactors_hom_naturality
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)) n
  have hmid : ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
        ((DerivedCategory.singleFunctor _ 0).map g) ≫
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app B) ≫
        (toTensorNatTrans X P).app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B) =
      (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app A) ≫
        (toTensorNatTrans X P).app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A)) ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (toTensorNatTrans X P).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))
        (CategoryTheory.Functor.map_comp
          ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P))
          ((DerivedCategory.singleFunctor _ 0).map g)
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app B)).symm).trans
      ((congrArg (fun t =>
          ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P)).map t ≫
          (toTensorNatTrans X P).app
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) hsf).trans
      ((congrArg (· ≫ (toTensorNatTrans X P).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))
        (CategoryTheory.Functor.map_comp
          ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P))
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app A)
          (DerivedCategory.Q.map
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)))).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) key).trans
        (Category.assoc _ _ _).symm)))))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _).symm).trans
    ((congrArg (fun t => (DerivedCategory.homologyFunctor _ n).map t ≫
        (DerivedCategory.homologyFunctorFactors _ n).hom.app
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))) hmid).trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans
      (Category.assoc _ _ _).symm)))))

end AnyModel

attribute [local instance] HasDerivedCategory.standard

/-- The functor `L ↦ Q P ⊗^L Q L` is the curried form at `P` of `(K, L) ↦ Q K ⊗^L Q L`; this is
the component at `P` of `curryComplexesDerivedTensorIso`. -/
public noncomputable def toTensorSourceIso (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    DerivedCategory.Q ⋙ (canonicalDerivedTensorProduct X.sheaf).tensor.obj
        (DerivedCategory.Q.obj P) ≅
      (Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))).obj P :=
  (curryComplexesDerivedTensorIso X).app P

/-- The functor `L ↦ Q Tot(P ⊗ L)` is the curried form at `P` of `(K, L) ↦ Q Tot(K ⊗ L)`; this
is the component at `P` of `curryComplexesTotalIso`. -/
public noncomputable def toTensorTargetIso (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P ⋙ DerivedCategory.Q ≅
      (Functor.curry.obj (totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) ⋙
          DerivedCategory.Q)).obj P :=
  (curryComplexesTotalIso X).app P

/-- `toTensorNatTrans` is the curried canonical map of `derivedToTensorNatTrans`, conjugated by
`toTensorSourceIso` and `toTensorTargetIso`. -/
public theorem toTensorNatTrans_eq_conj (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    toTensorNatTrans X P =
      (toTensorSourceIso X P).hom ≫
        (Functor.curry.map (derivedToTensorNatTrans X)).app P ≫ (toTensorTargetIso X P).inv := by
  ext L
  change _ = 𝟙 _ ≫ (canonicalDerivedTensorProduct X.sheaf).toTensor P L ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, toTensorNatTrans_app]

/-- **The canonical map `Q P ⊗^L Q(-) ⟶ Q Tot(P ⊗ -)` commutes with the shifts**, for the
commutation of `Q P ⊗^L -` with the shift given by the structure field
`DerivedTensorProduct.commShift_right` of the derived tensor product. -/
public theorem toTensorNatTrans_commShift (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :
    letI := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
    NatTrans.CommShift (toTensorNatTrans X P) ℤ := by
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
  let := curryComplexesDerivedTensor_commShift₂Int X
  let := curryComplexesTotal_commShift₂Int X
  have hc : NatTrans.CommShift ((Functor.curry.map (derivedToTensorNatTrans X)).app P) ℤ := by
    have h := derivedToTensorCommShift₂ X
    unfold DerivedToTensorCommShift₂ at h
    exact h.commShift_app P
  have hT : NatTrans.CommShift (toTensorTargetIso X P).hom ℤ := by
    let := curriedComplexesTotal_commShift₂Int X
    exact Functor.CommShift.ofIso_compatibility ((curryComplexesTotalIso X).app P) ℤ
  have hT' : NatTrans.CommShift (toTensorTargetIso X P).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have key : ∀ d : (canonicalDerivedTensorProduct X.sheaf).tensor.CommShift₂Int,
      d = Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int X.sheaf →
      letI := d.commShiftObj (DerivedCategory.Q.obj P)
      NatTrans.CommShift (toTensorSourceIso X P).hom ℤ := by
    rintro d rfl
    let := curriedComplexesDerivedTensor_commShift₂Int X
    exact Functor.CommShift.ofIso_compatibility ((curryComplexesDerivedTensorIso X).app P) ℤ
  have hD : NatTrans.CommShift (toTensorSourceIso X P).hom ℤ := key _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq X.sheaf)
  rw [toTensorNatTrans_eq_conj]
  infer_instance

/-! ### Connecting maps of short exact sequences of complexes -/

/-- **The connecting map of `Q P ⊗^L (triangle of a short exact sequence of complexes)`.** For a
short exact sequence `S` of complexes whose image under `Tot(P ⊗ -)` is short exact, the
canonical maps to the total tensor complex intertwine the connecting map on cohomology of the
image under `Q P ⊗^L -` of the triangle of `S` with the connecting map of the triangle of the
sequence of total complexes. -/
public theorem homologySequenceδ_mapTriangle_triangleOfSES_toTensorNatTrans
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    {S : ShortComplex (CochainComplex (SheafOfModules.{u} Oₓ) ℤ)} (hS : S.ShortExact)
    (hS' : (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P)).ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    letI := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
    DerivedCategory.HomologySequence.δ
        (((canonicalDerivedTensorProduct X.sheaf).tensor.obj
          (DerivedCategory.Q.obj P)).mapTriangle.obj (DerivedCategory.triangleOfSES hS)) n₀ n₁ h ≫
      (DerivedCategory.homologyFunctor _ n₁).map ((toTensorNatTrans X P).app S.X₁) =
    (DerivedCategory.homologyFunctor _ n₀).map ((toTensorNatTrans X P).app S.X₃) ≫
      DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS') n₀ n₁ h := by
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
  have := toTensorNatTrans_commShift X P
  have he₃ := map_mappingConeTriangle_mor₃_eq_bifunctorMappingConeIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) P S.f
  have hed := map_descShortComplex_eq_bifunctorMappingConeIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) P S
  exact ((DerivedCategory.homologyFunctor _ 0).homologySequenceδ_naturality
    (DerivedCategory.triangleOfSESNatTrans
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P)
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj P))
      (toTensorNatTrans X P) hS hS'
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) P S.f).hom
      he₃ hed) n₀ n₁ h).symm

/-! ### The connecting maps -/

/-- **The connecting map of `P ⊗^L (triangle of a short exact sequence)` is the snake-lemma
connecting map of the sequence of total complexes.** For a K-flat complex `P` and a short exact
sequence `S` of `O_X`-modules such that `0 → Tot(P ⊗ S.X₁) → Tot(P ⊗ S.X₂) → Tot(P ⊗ S.X₃) → 0`
is short exact, the connecting map on cohomology of the image of the triangle of `S` under
`Q P ⊗^L -`, for the commutation with the shift `DerivedTensorProduct.commShift_right`, is the
connecting map of the sequence of total complexes, read through
`derivedTensorSingleHomologyIso`. -/
public theorem homologySequenceδ_mapTriangle_singleTriangle
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    {S : ShortComplex (SheafOfModules.{u} Oₓ)} (hS : S.ShortExact)
    (hS' : (S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
      (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P)).ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    letI := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
    DerivedCategory.HomologySequence.δ
        (((canonicalDerivedTensorProduct X.sheaf).tensor.obj
          (DerivedCategory.Q.obj P)).mapTriangle.obj hS.singleTriangle) n₀ n₁ h ≫
      (derivedTensorSingleHomologyIso X P hP S.X₁ n₁).hom =
    (derivedTensorSingleHomologyIso X P hP S.X₃ n₀).hom ≫ hS'.δ n₀ n₁ h := by
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right (DerivedCategory.Q.obj P)
  have hS₀ : (S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)).ShortExact :=
    hS.map_of_exact _
  have hS'' : ((S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)).map
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P)).ShortExact := hS'
  have hcx := homologySequenceδ_mapTriangle_triangleOfSES_toTensorNatTrans X P hS₀ hS'' n₀ n₁ h
  exact homologySequenceδ_mapTriangle_singleTriangle_of_natTrans _ _ (toTensorNatTrans X P) hS hS₀
    hS' hS'' n₀ n₁ h hcx

end Stacks.IdealTorsion.ReductionDerived

end
