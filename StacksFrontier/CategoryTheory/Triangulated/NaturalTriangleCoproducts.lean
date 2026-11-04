module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison

/-!
# Direct sums across a natural family of distinguished triangles

Let `C` be a category, `D` a pre-triangulated category, and let

`R_X E ⟶ R_U E ⊞ R_V E ⟶ R_P E ⟶ (R_X E)[1]`

be a family of distinguished triangles in `D`, natural in `E ∈ C`, whose first two morphisms are
`biprod.lift (f_U) (f_V)` and `biprod.desc (g_U) (-g_V)` — the shape of the Mayer–Vietoris
triangles of [Stacks, Tag 0CRS] and [Stacks, Tag 08JK]. If `R_U`, `R_V` and `R_P` commute with
the direct sum of a family of objects of `C`, so does `R_X`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_sigmaComparison_of_natTrans_distTriang`: the
  comparison morphism of `R_X` is invertible when those of `R_U`, `R_V`, `R_P` are.
* `CategoryTheory.Pretriangulated.preservesColimit_of_natTrans_distTriang`: the same for
  preservation of the colimit of the discrete diagram.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 0CRG](https://stacks.math.columbia.edu/tag/0CRG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (RX RU RV RP : C ⥤ D) (fU : RX ⟶ RU) (fV : RX ⟶ RV) (gU : RU ⟶ RP) (gV : RV ⟶ RP)
  (δ : RP ⟶ RX ⋙ shiftFunctor D (1 : ℤ))

/-- The Mayer–Vietoris-shaped triangle at an object `E`. -/
abbrev natMVTriangle (E : C) : Triangle D :=
  Triangle.mk (biprod.lift (fU.app E) (fV.app E)) (biprod.desc (gU.app E) (-(gV.app E)))
    (δ.app E)

variable {J : Type w} [HasCoproductsOfShape J D] (K : J → C) [HasCoproduct K]

/-- The comparison morphism between the middle vertices: from the direct sum of the
`R_U(K j) ⊞ R_V(K j)` to `R_U(∐ K) ⊞ R_V(∐ K)`. -/
def natMVMiddleComparison :
    (∐ fun j ↦ RU.obj (K j) ⊞ RV.obj (K j)) ⟶ RU.obj (∐ K) ⊞ RV.obj (∐ K) :=
  Sigma.desc fun j ↦ biprod.map (RU.map (Sigma.ι K j)) (RV.map (Sigma.ι K j))

/-- The composite of the coprojection at `j` with `natMVMiddleComparison` is the biproduct map of
the images under `R_U` and `R_V` of the coprojection `K j ⟶ ∐ K`. -/
@[reassoc (attr := simp)]
lemma ι_natMVMiddleComparison (j : J) :
    Sigma.ι (fun j ↦ RU.obj (K j) ⊞ RV.obj (K j)) j ≫ natMVMiddleComparison RU RV K =
      biprod.map (RU.map (Sigma.ι K j)) (RV.map (Sigma.ι K j)) := by
  simp [natMVMiddleComparison]

/-- If the direct-sum comparison morphisms of `R_U` and `R_V` at `K` are invertible, then so is
`natMVMiddleComparison`. -/
lemma isIso_natMVMiddleComparison (hU : IsIso (sigmaComparison RU K))
    (hV : IsIso (sigmaComparison RV K)) : IsIso (natMVMiddleComparison RU RV K) := by
  let inv' : RU.obj (∐ K) ⊞ RV.obj (∐ K) ⟶ ∐ fun j ↦ RU.obj (K j) ⊞ RV.obj (K j) :=
    biprod.desc (inv (sigmaComparison RU K) ≫ Limits.Sigma.map fun j ↦ biprod.inl)
      (inv (sigmaComparison RV K) ≫ Limits.Sigma.map fun j ↦ biprod.inr)
  refine ⟨inv', ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun j ↦ biprod.hom_ext' _ _ ?_ ?_
    · have h : RU.map (Sigma.ι K j) ≫ inv (sigmaComparison RU K) =
          Sigma.ι (fun j ↦ RU.obj (K j)) j := by
        rw [IsIso.comp_inv_eq, ι_comp_sigmaComparison]
      simp [inv', reassoc_of% h]
    · have h : RV.map (Sigma.ι K j) ≫ inv (sigmaComparison RV K) =
          Sigma.ι (fun j ↦ RV.obj (K j)) j := by
        rw [IsIso.comp_inv_eq, ι_comp_sigmaComparison]
      simp [inv', reassoc_of% h]
  · refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← cancel_epi (sigmaComparison RU K)]
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      simp [inv']
    · rw [← cancel_epi (sigmaComparison RV K)]
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      simp [inv']

/-- The comparison morphism of triangles, from the direct sum of the triangles at the members of
the family to the triangle at their direct sum. -/
def natMVTriangleComparison :
    coproductTriangle (fun j ↦ natMVTriangle RX RU RV RP fU fV gU gV δ (K j)) ⟶
      natMVTriangle RX RU RV RP fU fV gU gV δ (∐ K) :=
  Triangle.homMk _ _ (sigmaComparison RX K) (natMVMiddleComparison RU RV K)
    (sigmaComparison RP K)
    (by
      refine Sigma.hom_ext _ _ fun j ↦ biprod.hom_ext _ _ ?_ ?_ <;>
        simp [coproductTriangle, Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison_assoc])
    (by
      refine Sigma.hom_ext _ _ fun j ↦ biprod.hom_ext' _ _ ?_ ?_ <;>
        simp [coproductTriangle, Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison])
    (by
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      simp only [coproductTriangle, natMVTriangle, Triangle.mk_obj₃, Triangle.mk_obj₁,
        Triangle.mk_mor₃, Sigma.ι_desc_assoc, Category.assoc, ι_comp_sigmaComparison_assoc]
      rw [shift_ι_comp_shift_sigmaComparison]
      exact (δ.naturality (Sigma.ι K j)).symm)

/-- **Direct sums across a natural family of distinguished triangles.** If the triangles
`R_X E ⟶ R_U E ⊞ R_V E ⟶ R_P E ⟶ (R_X E)[1]` are distinguished for every `E`, and the
direct-sum comparison morphisms of `R_U`, `R_V`, `R_P` at a family `K` are invertible, then so is
that of `R_X`. -/
theorem isIso_sigmaComparison_of_natTrans_distTriang
    (hT : ∀ E, natMVTriangle RX RU RV RP fU fV gU gV δ E ∈ distTriang D)
    (hU : IsIso (sigmaComparison RU K)) (hV : IsIso (sigmaComparison RV K))
    (hP : IsIso (sigmaComparison RP K)) :
    IsIso (sigmaComparison RX K) := by
  have := isIso_natMVMiddleComparison RU RV K hU hV
  exact isIso₁_of_isIso₂₃ (natMVTriangleComparison RX RU RV RP fU fV gU gV δ K)
    (coproductTriangle_distinguished _ fun j ↦ hT (K j)) (hT (∐ K))
    (inferInstanceAs (IsIso (natMVMiddleComparison RU RV K)))
    (inferInstanceAs (IsIso (sigmaComparison RP K)))

/-- **Direct sums across a natural family of distinguished triangles**, read as preservation of
the colimit of the discrete diagram on the family. -/
theorem preservesColimit_of_natTrans_distTriang
    (hT : ∀ E, natMVTriangle RX RU RV RP fU fV gU gV δ E ∈ distTriang D)
    (hU : PreservesColimit (Discrete.functor K) RU)
    (hV : PreservesColimit (Discrete.functor K) RV)
    (hP : PreservesColimit (Discrete.functor K) RP) :
    PreservesColimit (Discrete.functor K) RX :=
  preservesColimit_discreteFunctor_of_isIso_sigmaComparison RX K
    (isIso_sigmaComparison_of_natTrans_distTriang RX RU RV RP fU fV gU gV δ K hT
      (isIso_sigmaComparison_of_preservesColimit RU K hU)
      (isIso_sigmaComparison_of_preservesColimit RV K hV)
      (isIso_sigmaComparison_of_preservesColimit RP K hP))

section Whisker

variable {D' : Type*} [Category D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  (G : D ⥤ D') [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]

/-- The third morphism of the image under an exact functor `G` of the natural triangles: the
image of `δ` followed by the commutation of `G` with the shift. -/
def natMVδWhisker : RP ⋙ G ⟶ (RX ⋙ G) ⋙ shiftFunctor D' (1 : ℤ) :=
  Functor.whiskerRight δ G ≫ Functor.whiskerLeft RX (G.commShiftIso (1 : ℤ)).hom

/-- The image under an exact functor of a natural family of Mayer–Vietoris-shaped distinguished
triangles is again one, with the four functors composed with `G`. -/
theorem natMVTriangle_whiskerRight_mem_distTriang
    (hT : ∀ E, natMVTriangle RX RU RV RP fU fV gU gV δ E ∈ distTriang D) (E : C) :
    natMVTriangle (RX ⋙ G) (RU ⋙ G) (RV ⋙ G) (RP ⋙ G) (Functor.whiskerRight fU G)
      (Functor.whiskerRight fV G) (Functor.whiskerRight gU G) (Functor.whiskerRight gV G)
      (natMVδWhisker RX RP δ G) E ∈ distTriang D' := by
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  refine isomorphic_distinguished _ (G.map_distinguished _ (hT E)) _
    (Triangle.isoMk _ _ (Iso.refl _) (G.mapBiprod (RU.obj E) (RV.obj E)).symm (Iso.refl _) ?_ ?_ ?_)
  · dsimp [Functor.mapTriangle]
    rw [biprod.lift_mapBiprod, Category.id_comp]
  · dsimp [Functor.mapTriangle]
    rw [biprod.mapBiprod_inv_map_desc, Category.comp_id, G.map_neg]
  · dsimp [Functor.mapTriangle, natMVδWhisker]
    simp

end Whisker

end CategoryTheory.Pretriangulated

end
