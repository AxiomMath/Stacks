module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PointClassComposition

/-!
# The two summands cut out by a rational point

Let `k` be a field, let `X` be a smooth projective scheme over `k` of constant dimension `d`, and
let `x : Spec k ⟶ X` be a rational point. In the category `M_k = ChowMotiveCat k` of Chow motives,
formed with the composition of correspondences `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` and the
canonical diagonal classes, the following summands of the motive of `X` are those of Stacks 0FGD
(stated there for `X = P¹_k`):

* `(X, c₀, 0) ≅ 1 = (Spec k, 1, 0)`, for `c₀ = [Γ_{X → x → X}] = [x × X]`;
* `(X, c₂, 0) ≅ 1(-d) = (Spec k, 1, -d)`, for `c₂ = [X × x]`.

The first is given by the graph classes `a = [Γ_{X → Spec k}]` and `b = [Γ_x]`, with `b ∘ a = 1`
and `a ∘ b = c₀`; the second by the class `a' = [x] ∈ Corr^d(Spec k, X)` and the fundamental class
`b' = [X] ∈ Corr^{-d}(X, Spec k)`, with `b' ∘ a' = 1` and `a' ∘ b' = c₂`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.isoOfSplit`: a twisted idempotent whose
  idempotent splits through `(Y, 𝟙, n)` is isomorphic to it.
* `Stacks.WeilCohomology.ChowMotiveCat.pointClassCorr`, `fundamentalClassCorr`, `fibreClassCorr`,
  `constantGraphCorr`: the correspondences `a'`, `b'`, `c₂` and `c₀`.
* `Stacks.WeilCohomology.ChowMotiveCat.pointGraphMotiveIso`: `(X, c₀, 0) ≅ 1`.
* `Stacks.WeilCohomology.ChowMotiveCat.pointFibreMotiveIso`: `(X, c₂, 0) ≅ 1(-d)`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.pointClass_comp_fundamentalClass`: `b' ∘ a' = 1`.
* `Stacks.WeilCohomology.ChowMotiveCat.fundamentalClass_comp_pointClass`: `a' ∘ b' = c₂`.
* `Stacks.WeilCohomology.ChowMotiveCat.fibreClassCorr_comp_self`,
  `Stacks.WeilCohomology.ChowMotiveCat.constantGraphCorr_comp_self`: `c₂` and `c₀` are idempotent.

## References

* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Section 0FG9](https://stacks.math.columbia.edu/tag/0FG9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory
  MonoidalCategory Stacks.Chow

universe u

namespace CategoryTheory.GradedCategory.TwistedKaroubi

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [GradedCategory R C]

/-- A twisted idempotent `M` is isomorphic to a twisted idempotent `N` with identity idempotent
as soon as the idempotent of `M` splits through `N` in the right degrees: given `a : N ⟶ M` of
degree `M.twist - N.twist` and `b : M ⟶ N` of degree `N.twist - M.twist` with `a ≫ b = 𝟙` and
`b ≫ a = M.p`, the two are mutually inverse morphisms of the twisted Karoubi envelope. -/
def isoOfSplit {M N : TwistedKaroubi R C} (hN : N.p = 𝟙 N.X) (a : N.X ⟶ M.X)
    (ha : a ∈ grade (R := R) N.X M.X (M.twist - N.twist)) (b : M.X ⟶ N.X)
    (hb : b ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (hab : a ≫ b = 𝟙 N.X)
    (hba : b ≫ a = M.p) : M ≅ N where
  hom := Hom.mk b ⟨hb, by rw [← hba, Category.assoc, hab, Category.comp_id],
    by rw [hN, Category.comp_id]⟩
  inv := Hom.mk a ⟨ha, by rw [hN, Category.id_comp],
    by rw [← hba, ← Category.assoc, hab, Category.id_comp]⟩
  hom_inv_id := hom_ext hba
  inv_hom_id := hom_ext (hab.trans hN.symm)

/-- The triple `(X, p, m)` is isomorphic to `(Y, 𝟙, n)` when `p` splits through `Y` in the right
degrees. -/
def isoOfSplitMk {X Y : C} {p : X ⟶ X} (hp : p ∈ grade (R := R) X X 0) (hpp : p ≫ p = p)
    {m n : ℤ} (a : Y ⟶ X) (ha : a ∈ grade (R := R) Y X (m - n)) (b : X ⟶ Y)
    (hb : b ∈ grade (R := R) X Y (n - m)) (hab : a ≫ b = 𝟙 Y) (hba : b ≫ a = p) :
    (⟨X, p, hp, hpp, m⟩ : TwistedKaroubi R C) ≅
      ⟨Y, 𝟙 Y, id_mem Y, Category.comp_id _, n⟩ :=
  isoOfSplit rfl a ha b hb hab hba

end CategoryTheory.GradedCategory.TwistedKaroubi

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- Transport along `r = r` is the identity. -/
theorem correspondenceCongr_self {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    {e r : ℤ} (h : r = r)
    (c : Correspondence (fieldChowSituation k) sX sY e r) :
    correspondenceCongr k sX sY h c = c := by
  induction c using TensorProduct.inductionOn with
  | tmul q y => rfl
  | add a b ha hb => rw [map_add, ha, hb]

namespace ChowMotiveCat

/-- Two homogeneous morphisms between equidimensional schemes agree once their equidimensional
forms agree, after transport of degrees. -/
theorem homOf_eq_homOf {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) {r r' : ℤ}
    (h : r = r') (a : SmoothProjectiveCorr X Y r) (b : SmoothProjectiveCorr X Y r')
    (hab : correspondenceCongr k X.obj.hom Y.obj.hom h
        (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r
          (SmoothProjectiveCorr.toCorr X Y r a)) =
      corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r'
        (SmoothProjectiveCorr.toCorr X Y r' b)) :
    homOf r a = homOf r' b := by
  subst h
  rw [correspondenceCongr_self] at hab
  exact congrArg (homOf r) ((SmoothProjectiveCorr.toCorr X Y r).injective
    ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r).injective hab))

local notation "𝟙ₛ" => 𝟙_ (ObjectProperty.FullSubcategory (SmoothProjectiveScheme k))

attribute [local instance] isClosedImmersion_pointSectionEmbedding
  isClosedImmersion_unitSectionEmbedding isClosedImmersion_constantFibreEmbedding

/-- The monoidal unit `Spec k` has dimension zero. -/
theorem relativeDimension_tensorUnit_hom : RelativeDimension (𝟙ₛ).obj.hom 0 :=
  relativeDimension_of_isOpenImmersion _

variable {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}

/-- The class `a' = [x] ∈ Corr^d(Spec k, X) = CH^d(X)` of a rational point. -/
def pointClassCorr (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) :
    SmoothProjectiveCorr 𝟙ₛ X d :=
  (SmoothProjectiveCorr.toCorr _ _ d).symm
    ((corrEquivCorrespondence k (𝟙ₛ).obj.hom X.obj.hom relativeDimension_tensorUnit_hom hX d).symm
      ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙ₛ).obj.hom X.obj.hom)
        (pointSectionEmbedding k X.obj.hom (𝟙ₛ).obj.hom x.hom.left (Over.w x.hom))
        ((d : ℤ) - d))))

/-- The fundamental class `b' = [X] ∈ Corr^{-d}(X, Spec k) = CH_d(X)`. -/
def fundamentalClassCorr (hX : RelativeDimension X.obj.hom d) : SmoothProjectiveCorr X 𝟙ₛ (-d) :=
  (SmoothProjectiveCorr.toCorr _ _ (-d)).symm
    ((corrEquivCorrespondence k X.obj.hom (𝟙ₛ).obj.hom hX relativeDimension_tensorUnit_hom
        (-d)).symm
      ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase X.obj.hom (𝟙ₛ).obj.hom) (unitSectionEmbedding k X.obj.hom (𝟙ₛ).obj.hom)
        (((0 : ℕ) : ℤ) - -d))))

/-- **`b' ∘ a' = 1`** in the category of correspondences, for the class `a'` of a rational point
and the fundamental class `b'`. -/
theorem pointClass_comp_fundamentalClass (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) :
    homOf d (pointClassCorr hX x) ≫ homOf (-d) (fundamentalClassCorr hX) =
      𝟙 (GradedCompositionData.Obj.mk 𝟙ₛ : (canonicalCorrespondenceCompositionData k).Obj) := by
  rw [homOf_comp_homOf, id_eq_homOf]
  refine homOf_eq_homOf relativeDimension_tensorUnit_hom relativeDimension_tensorUnit_hom
    (by omega) _ _ ?_
  rw [toCorr_correspondenceCompositionData_comp, corrEquivCorrespondence_comp k _ _ _
    (canonicalDiagonalClassFamily_isoInvariant k) _ relativeDimension_tensorUnit_hom hX
    relativeDimension_tensorUnit_hom]
  simp only [pointClassCorr, fundamentalClassCorr, LinearEquiv.apply_symm_apply]
  have key := DiagonalClassFamily.ProperIntersectionFormula.compositionInt_pointSection_unitSection
    X.obj.hom (𝟙ₛ).obj.hom x.hom.left (Over.w x.hom)
    (canonicalDiagonalClassFamily_properIntersectionFormula k) hX relativeDimension_tensorUnit_hom
  rw [composition_tmul]
  simp only [key, mul_one, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme, correspondenceDiagonal,
    LinearEquiv.apply_symm_apply]
  rw [corrEquivCorrespondence_diagonalCorr, graphCorrespondence]

/-- The class `c₂ = [X × x] ∈ Corr⁰(X, X)` of the fibre over a rational point. -/
def fibreClassCorr (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) : SmoothProjectiveCorr X X 0 :=
  (SmoothProjectiveCorr.toCorr _ _ 0).symm
    ((corrEquivCorrespondence k X.obj.hom X.obj.hom hX hX 0).symm
      ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase X.obj.hom X.obj.hom)
        (constantFibreEmbedding k X.obj.hom (𝟙ₛ).obj.hom x.hom.left (Over.w x.hom))
        ((d : ℤ) - 0))))

/-- **`a' ∘ b' = c₂`** in the category of correspondences, for the class `a'` of a rational point,
the fundamental class `b'` and the class `c₂` of the fibre over the point. -/
theorem fundamentalClass_comp_pointClass (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) :
    homOf (-d) (fundamentalClassCorr hX) ≫ homOf d (pointClassCorr hX x) =
      homOf 0 (fibreClassCorr hX x) := by
  rw [homOf_comp_homOf]
  refine homOf_eq_homOf hX hX (by omega) _ _ ?_
  rw [toCorr_correspondenceCompositionData_comp, corrEquivCorrespondence_comp k _ _ _
    (canonicalDiagonalClassFamily_isoInvariant k) _ hX relativeDimension_tensorUnit_hom hX]
  simp only [pointClassCorr, fundamentalClassCorr, fibreClassCorr, LinearEquiv.apply_symm_apply]
  have key := DiagonalClassFamily.ProperIntersectionFormula.compositionInt_unitSection_pointSection
    X.obj.hom (𝟙ₛ).obj.hom x.hom.left (Over.w x.hom)
    (canonicalDiagonalClassFamily_properIntersectionFormula k) hX relativeDimension_tensorUnit_hom
  rw [composition_tmul]
  simp only [key, mul_one, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]

/-- A degree-zero correspondence `c` which is `g ≫ f` for `f ≫ g = 𝟙` is idempotent. -/
private theorem comp_self_of_homOf_comp_eq_id {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : SmoothProjectiveCorr X X 0}
    (f : (GradedCompositionData.Obj.mk Y : (canonicalCorrespondenceCompositionData k).Obj) ⟶
      GradedCompositionData.Obj.mk X)
    (g : (GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
      GradedCompositionData.Obj.mk Y)
    (hfg : f ≫ g = 𝟙 _) (hgf : g ≫ f = homOf 0 c) :
    (canonicalCorrespondenceCompositionData k).comp c c = c := by
  apply homOf_injective 0
  change homOf (0 + 0) _ = _
  rw [← homOf_comp_homOf, ← hgf, Category.assoc, ← Category.assoc f, hfg, Category.id_comp]

/-- `c₂ ∘ c₂ = c₂`: the class of the fibre over a rational point is idempotent. -/
theorem fibreClassCorr_comp_self (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) :
    (canonicalCorrespondenceCompositionData k).comp (fibreClassCorr hX x) (fibreClassCorr hX x) =
      fibreClassCorr hX x := by
  exact comp_self_of_homOf_comp_eq_id _ _ (pointClass_comp_fundamentalClass hX x)
    (fundamentalClass_comp_pointClass hX x)

/-- **Stacks 0FGD (2), for a smooth projective scheme of constant dimension `d` with a rational
point.** The motive `(X, c₂, 0)`, with `c₂ = [X × x]` the class of the fibre over `x`, is
isomorphic to `1(-d) = (Spec k, 1, -d)`. The two mutually inverse morphisms are the class
`a' = [x] ∈ Corr^d(Spec k, X)` and the fundamental class `b' = [X] ∈ Corr^{-d}(X, Spec k)`. -/
def pointFibreMotiveIso (hX : RelativeDimension X.obj.hom d) (x : 𝟙ₛ ⟶ X) :
    mk' X (fibreClassCorr hX x) (fibreClassCorr_comp_self hX x) 0 ≅ tate k (-d) :=
  TwistedKaroubi.isoOfSplitMk (X := GradedCompositionData.Obj.mk X)
    (Y := GradedCompositionData.Obj.mk 𝟙ₛ) (m := 0) (n := -d) (homOf_mem_grade _) _
    (homOf (X := 𝟙ₛ) (Y := X) d (pointClassCorr hX x))
    (by rw [show (0 : ℤ) - -(d : ℤ) = d by ring]; exact homOf_mem_grade _)
    (homOf (X := X) (Y := 𝟙ₛ) (-d) (fundamentalClassCorr hX))
    (by rw [show -(d : ℤ) - 0 = -d by ring]; exact homOf_mem_grade _)
    (pointClass_comp_fundamentalClass hX x) (fundamentalClass_comp_pointClass hX x)

/-- The structure morphism `X ⟶ Spec k`, as a morphism to the monoidal unit. -/
def toTensorUnit (X : (SmoothProjectiveScheme k).FullSubcategory) : X ⟶ 𝟙ₛ :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (by
    rw [SmoothProjectiveScheme.tensorUnit_hom]; exact Category.comp_id _))

/-- A rational point is a section of the structure morphism. -/
theorem comp_toTensorUnit (x : 𝟙ₛ ⟶ X) : x ≫ toTensorUnit X = 𝟙 𝟙ₛ := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  have h := Over.w x.hom
  rw [SmoothProjectiveScheme.tensorUnit_hom] at h
  exact h

/-- The class `c₀ = [Γ_{X → x → X}] ∈ Corr⁰(X, X)` of the graph of the constant morphism through a
rational point, i.e. the fibre `x × X`. -/
def constantGraphCorr (x : 𝟙ₛ ⟶ X) : SmoothProjectiveCorr X X 0 :=
  graphCorrespondenceSP (toTensorUnit X ≫ x)

/-- The graph class, as a morphism of the category of correspondences, is `graphHom`. -/
theorem homOf_graphCorrespondenceSP {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    homOf 0 (graphCorrespondenceSP f) = graphHom (Δ := canonicalDiagonalClassFamily k)
      (hassoc := canonicalDiagonalClassFamily_compositionAssoc k)
      (hΔ := canonicalDiagonalClassFamily_properIntersectionFormula k) f := by
  rw [homOf, DirectSum.lof_eq_of]
  rfl

/-- `b ∘ a = 1`: the graph of the rational point composed after the graph of the structure
morphism is the identity of `Spec k`. -/
theorem graph_point_comp_graph_toTensorUnit (x : 𝟙ₛ ⟶ X) :
    homOf (X := 𝟙ₛ) (Y := X) 0 (graphCorrespondenceSP (toTensorUnit X)) ≫
      homOf (X := X) (Y := 𝟙ₛ) 0 (graphCorrespondenceSP x) =
      𝟙 (GradedCompositionData.Obj.mk 𝟙ₛ : (canonicalCorrespondenceCompositionData k).Obj) := by
  rw [homOf_graphCorrespondenceSP, homOf_graphCorrespondenceSP, graphHom_comp,
    comp_toTensorUnit]
  exact graphHom_id _

/-- `a ∘ b = c₀`: the graph of the structure morphism composed after the graph of the rational
point is the graph of the constant morphism. -/
theorem graph_toTensorUnit_comp_graph_point (x : 𝟙ₛ ⟶ X) :
    homOf (X := X) (Y := 𝟙ₛ) 0 (graphCorrespondenceSP x) ≫
      homOf (X := 𝟙ₛ) (Y := X) 0 (graphCorrespondenceSP (toTensorUnit X)) =
      homOf 0 (constantGraphCorr x) := by
  rw [homOf_graphCorrespondenceSP, homOf_graphCorrespondenceSP, graphHom_comp,
    constantGraphCorr, homOf_graphCorrespondenceSP]

/-- `c₀ ∘ c₀ = c₀`. -/
theorem constantGraphCorr_comp_self (x : 𝟙ₛ ⟶ X) :
    (canonicalCorrespondenceCompositionData k).comp (constantGraphCorr x) (constantGraphCorr x) =
      constantGraphCorr x := by
  exact comp_self_of_homOf_comp_eq_id _ _ (graph_point_comp_graph_toTensorUnit x)
    (graph_toTensorUnit_comp_graph_point x)

/-- **Stacks 0FGD (1), for a smooth projective scheme with a rational point.** The motive
`(X, c₀, 0)`, with `c₀ = [Γ_{X → x → X}]` the graph of the constant morphism through `x`, is
isomorphic to `1 = (Spec k, 1, 0)`. The two mutually inverse morphisms are the graph classes
`a = [Γ_{X → Spec k}]` and `b = [Γ_x]`. -/
def pointGraphMotiveIso (x : 𝟙ₛ ⟶ X) :
    mk' X (constantGraphCorr x) (constantGraphCorr_comp_self x) 0 ≅ tate k 0 :=
  TwistedKaroubi.isoOfSplitMk (X := GradedCompositionData.Obj.mk X)
    (Y := GradedCompositionData.Obj.mk 𝟙ₛ) (m := 0) (n := 0) (homOf_mem_grade _) _
    (homOf (X := 𝟙ₛ) (Y := X) 0 (graphCorrespondenceSP (toTensorUnit X))) (homOf_mem_grade _)
    (homOf (X := X) (Y := 𝟙ₛ) 0 (graphCorrespondenceSP x)) (homOf_mem_grade _)
    (graph_point_comp_graph_toTensorUnit x) (graph_toTensorUnit_comp_graph_point x)

end ChowMotiveCat

end Stacks.WeilCohomology

end
