module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareLimit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTriangle
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChange

/-!
# The square of topoi `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}`

For a morphism of global crystalline situations, the canonical `2`-cell
`f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` between direct images of sheaves on the small
crystalline site is an isomorphism. Read at an open `V` of `X`, it is the comparison
`CategoryTheory.Limits.limit.pre` along `dominationProj` from the limit over the objects of
`Cris(X'/S)` lying over `f^{-1}V` to the limit over the dominating pairs over `V`. As a natural
transformation it is the base change of a right Kan extension,
`CategoryTheory.TwoSquare.ranBaseChange`, along the square of categories `crisZariskiTwoSquare`.

## Main definitions

* `dominationDiagram`: the diagram over the dominating pairs over `V` whose limit is the sections
  of `u_{X/S, *}f_{cris, *}ℋ` over `V`.
* `dominationRefine`, `dominationCompare`: morphisms of dominating pairs changing the object of
  `Cris(X'/S)`, respectively the object of `Cris(X/S)`.
* `dominationChoice`, `dominationPi`: a chosen dominating pair over `V` with a prescribed object of
  `Cris(X'/S)`, and the limit projection at it.
* `dominationCover`: the covering sieve of the dominated refinements of an object of `Cris(X'/S)`.
* `dominationLeg`: the amalgamation of the projections `dominationPi` over `dominationCover`.
* `dominationInv`: the inverse of the comparison of the two limits at `V`.
* `crisZariskiTwoSquare`: the square of categories underlying the square of topoi.
* `crisZariskiCell`: the `2`-cell `f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` on abelian
  sheaves.
* `crisZariskiSquare`: the commutation `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}`, a term of
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrisZariskiSquare`.

## Main results

* `limit_π_dominationStructuredArrow_eq`: two dominating pairs over `V` with the same object of
  `Cris(X'/S)` have the same limit projection.
* `dominationPi_comp_map`: restricting the projection at a dominated object along a morphism of
  `Cris(X'/S)` gives the projection at its source.
* `isIso_limit_pre_dominationProj`: the comparison of the two limits at `V` is an isomorphism.
* `isIso_crisZariskiCellApp`: the canonical `2`-cell, read at an open `V` of `X`, is an
  isomorphism.
* `crisZariskiRanBaseChange_app_app`: at `V`, the base change along `crisZariskiTwoSquare` is the
  comparison of the two limits.
* `isIso_crisZariskiCell`, `hasCrisZariskiSquare`: the square of topoi commutes, for every
  morphism of global crystalline situations.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

variable (E : Type (u + 2)) [Category.{u + 1} E] [HasLimitsOfSize.{u, u + 1} E]

/-- The diagram over the dominating pairs over `V` whose limit is the sections of
`u_{X/S, *}f_{cris, *}ℋ` over `V`: the restriction along `dominationProj` of the diagram whose
limit is the sections of `f_{Zar, *}u_{X'/S, *}ℋ` over `V`. -/
abbrev dominationDiagram (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    StructuredArrow (op V) (dominationToOpens S S' fS fX hf) ⥤ E :=
  dominationProj S S' fS fX hf V ⋙
    StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj

/-- The object of `Cris(X/S)` of a dominating pair over `V` lies over `V`. -/
theorem dominationPairs_mem (V : S'.X.Opens)
    (d : StructuredArrow (op V) (dominationToOpens S S' fS fX hf)) :
    ∀ z : d.right.left.unop.obj.thickening.source,
      d.right.left.unop.obj.toX.base z ∈ V :=
  fun y ↦ leOfHom d.hom.unop ⟨y, rfl⟩

/-- The refinement of a dominating pair along a morphism of `Cris(X'/S)`: a morphism `g : Z ⟶ A'`
gives the morphism of dominating pairs `(A, A', k) ⟶ (A, Z, K g ≫ k)` with components `(𝟙, g)`. -/
def dominationRefine (V : S'.X.Opens)
    (d : StructuredArrow (op V) (dominationToOpens S S' fS fX hf))
    (Z : CrystallineThickening S) (g : Z ⟶ d.right.right.unop) :
    d ⟶ dominationStructuredArrow S S' fS fX hf V Z d.right.left.unop
      (dominationPairs_mem S S' fS fX hf V d)
      ((crisToBig S S' fS fX hf).map g ≫ d.right.hom.unop) :=
  StructuredArrow.homMk
    (({ left := 𝟙 _, right := g.op, w := by simp only; rfl } :
      d.right ⟶ (⟨op d.right.left.unop, op Z,
        ((crisToBig S S' fS fX hf).map g ≫ d.right.hom.unop).op⟩ :
          DominationPairs S S' fS fX hf)))
    (Subsingleton.elim _ _)

/-- If the domination `k₁` of `C` by `B₁` factors through the domination `k` of `C` by `B` along
`a : B ⟶ B₁`, the morphism of dominating pairs `(B₁, C, k₁) ⟶ (B, C, k)` with components `(a, 𝟙)`.
-/
def dominationCompare (V : S'.X.Opens) (C : CrystallineThickening S)
    (B₁ B : CrystallineThickening S')
    (hB₁ : ∀ z : B₁.obj.thickening.source, B₁.obj.toX.base z ∈ V)
    (hB : ∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V)
    (k₁ : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₁)
    (k : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B)
    (a : B ⟶ B₁) (ha : k ≫ (CrystallineThickening.ι S').map a = k₁) :
    dominationStructuredArrow S S' fS fX hf V C B₁ hB₁ k₁ ⟶
      dominationStructuredArrow S S' fS fX hf V C B hB k :=
  StructuredArrow.homMk
    (({ left := a.op, right := 𝟙 _, w := by
          simp only
          exact congrArg Quiver.Hom.op ha } :
      (⟨op B₁, op C, k₁.op⟩ : DominationPairs S S' fS fX hf) ⟶ ⟨op B, op C, k.op⟩))
    (Subsingleton.elim _ _)

/-- Two dominating pairs over `V` with the same object of `Cris(X'/S)` have the same limit
projection. -/
theorem limit_π_dominationStructuredArrow_eq
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens)
    (C : CrystallineThickening S) (B₁ B₂ : CrystallineThickening S')
    (hB₁ : ∀ z : B₁.obj.thickening.source, B₁.obj.toX.base z ∈ V)
    (hB₂ : ∀ z : B₂.obj.thickening.source, B₂.obj.toX.base z ∈ V)
    (k₁ : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₁)
    (k₂ : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B₂) :
    limit.π (dominationDiagram S S' fS fX hf E G V)
        (dominationStructuredArrow S S' fS fX hf V C B₁ hB₁ k₁) =
      limit.π (dominationDiagram S S' fS fX hf E G V)
        (dominationStructuredArrow S S' fS fX hf V C B₂ hB₂ k₂) := by
  obtain ⟨B, a, b, k, hBV, ha, hb⟩ := exists_cone_domination S S' fS fX hf V
    ((CrystallineThickening.ι S).obj C) hB₁ k₁ k₂
  have key : ∀ (B' : CrystallineThickening S')
      (hB' : ∀ z : B'.obj.thickening.source, B'.obj.toX.base z ∈ V)
      (k' : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B')
      (a' : B ⟶ B') (ha' : k ≫ (CrystallineThickening.ι S').map a' = k'),
      limit.π (dominationDiagram S S' fS fX hf E G V)
          (dominationStructuredArrow S S' fS fX hf V C B' hB' k') =
        limit.π (dominationDiagram S S' fS fX hf E G V)
          (dominationStructuredArrow S S' fS fX hf V C B hBV k) := by
    intro B' hB' k' a' ha'
    rw [← limit.w (dominationDiagram S S' fS fX hf E G V)
      (dominationCompare S S' fS fX hf V C B' B hB' hBV k' k a' ha')]
    exact (Category.comp_id _).symm.trans (congrArg _ (G.obj.map_id (op C)).symm)
  exact (key B₁ hB₁ k₁ a ha).trans (key B₂ hB₂ k₂ b hb).symm

/-- A chosen dominating pair over `V` whose object of `Cris(X'/S)` is a given object `C` admitting,
after change of divided power base, a morphism to an object of `Cris(X/S)` lying over `V`. -/
def dominationChoice (V : S'.X.Opens) {C : CrystallineThickening S}
    (hC : ∃ B : CrystallineThickening S',
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        Nonempty ((crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B)) :
    StructuredArrow (op V) (dominationToOpens S S' fS fX hf) :=
  dominationStructuredArrow S S' fS fX hf V C hC.choose hC.choose_spec.1
    hC.choose_spec.2.some

/-- The projection of the limit over the dominating pairs over `V` at the dominating pair
`dominationChoice` of a dominated object of `Cris(X'/S)`. -/
def dominationPi (G : Sheaf (smallTopology S) E) (V : S'.X.Opens)
    {C : CrystallineThickening S}
    (hC : ∃ B : CrystallineThickening S',
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        Nonempty ((crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B)) :
    limit (dominationDiagram S S' fS fX hf E G V) ⟶ G.obj.obj (op C) :=
  limit.π (dominationDiagram S S' fS fX hf E G V) (dominationChoice S S' fS fX hf V hC)

/-- Restricting the projection `dominationPi` at a dominated object `C` along a morphism
`g : Z ⟶ C` of `Cris(X'/S)` gives the projection `dominationPi` at `Z`. -/
theorem dominationPi_comp_map (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) {C Z : CrystallineThickening S}
    (hC : ∃ B : CrystallineThickening S',
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        Nonempty ((crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B))
    (hZ : ∃ B : CrystallineThickening S',
      (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
        Nonempty ((crisToBig S S' fS fX hf).obj Z ⟶ (CrystallineThickening.ι S').obj B))
    (g : Z ⟶ C) :
    dominationPi S S' fS fX hf E G V hC ≫ G.obj.map g.op =
      dominationPi S S' fS fX hf E G V hZ :=
  (limit.w (dominationDiagram S S' fS fX hf E G V)
    (dominationRefine S S' fS fX hf V (dominationChoice S S' fS fX hf V hC) Z g)).trans
      (limit_π_dominationStructuredArrow_eq S S' fS fX hf E G V Z _ _ _ _ _ _)

/-- The covering sieve of the dominated refinements of an object of `Cris(X'/S)` lying over
`f^{-1}V`, as a cover of the small crystalline site. -/
def dominationCover (V : S'.X.Opens)
    (i : StructuredArrow (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op) :
    (smallTopology S).Cover i.right.unop :=
  ⟨smallDominatedSieve S S' fS fX hf V i.right.unop,
    smallDominatedSieve_mem S S' fS fX hf V i.right.unop fun z ↦ leOfHom i.hom.unop ⟨z, rfl⟩⟩

/-- The amalgamation over `dominationCover` of the projections `dominationPi` of the limit over the
dominating pairs over `V`. -/
def dominationLeg (G : Sheaf (smallTopology S) E) (V : S'.X.Opens)
    (i : StructuredArrow (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op) :
    limit (dominationDiagram S S' fS fX hf E G V) ⟶ G.obj.obj i.right :=
  G.cond.amalgamate (dominationCover S S' fS fX hf V i)
    (fun I ↦ dominationPi S S' fS fX hf E G V I.hf)
    (fun {I₁ I₂} r ↦ by
      have hZ : ∃ B : CrystallineThickening S',
          (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
            Nonempty ((crisToBig S S' fS fX hf).obj r.Z ⟶
              (CrystallineThickening.ι S').obj B) :=
        (smallDominatedSieve S S' fS fX hf V i.right.unop).downward_closed I₁.hf r.g₁
      exact (dominationPi_comp_map S S' fS fX hf E G V I₁.hf hZ r.g₁).trans
        (dominationPi_comp_map S S' fS fX hf E G V I₂.hf hZ r.g₂).symm)

/-- Restricting `dominationLeg` along an arrow of `dominationCover` gives the projection
`dominationPi` at the source of that arrow. -/
theorem dominationLeg_comp_map (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) (i : StructuredArrow (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op)
    (I : (dominationCover S S' fS fX hf V i).Arrow) :
    dominationLeg S S' fS fX hf E G V i ≫ G.obj.map I.f.op =
      dominationPi S S' fS fX hf E G V I.hf :=
  G.cond.amalgamate_map _ _ _ I

/-- The morphism from the limit over the dominating pairs over `V` to the limit over the objects of
`Cris(X'/S)` lying over `f^{-1}V` whose legs are the amalgamations `dominationLeg`. -/
def dominationInv (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    limit (dominationDiagram S S' fS fX hf E G V) ⟶
      limit (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj) :=
  limit.lift _
    { pt := limit (dominationDiagram S S' fS fX hf E G V)
      π :=
        { app := dominationLeg S S' fS fX hf E G V
          naturality := fun i j ψ ↦ by
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
              StructuredArrow.proj_map]
            rw [Category.id_comp]
            refine (G.cond.hom_ext (dominationCover S S' fS fX hf V j) _ _ fun I ↦ ?_).symm
            have h1 : dominationLeg S S' fS fX hf E G V i ≫ G.obj.map (ψ.right ≫ I.f.op) =
                dominationPi S S' fS fX hf E G V I.hf :=
              dominationLeg_comp_map S S' fS fX hf E G V i
                ⟨I.Y, I.f ≫ ψ.right.unop, I.hf⟩
            rw [Category.assoc, ← G.obj.map_comp, h1,
              dominationLeg_comp_map S S' fS fX hf E G V j I] } }

/-- The projections of `dominationInv` are the legs `dominationLeg`. -/
theorem dominationInv_comp_π (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) (i : StructuredArrow (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op) :
    dominationInv S S' fS fX hf E G V ≫
        limit.π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj) i =
      dominationLeg S S' fS fX hf E G V i :=
  limit.lift_π _ _

/-- The comparison `CategoryTheory.Limits.limit.pre` along `dominationProj` between the two limits
at an open `V` of `X` is an isomorphism, with inverse `dominationInv`. -/
instance isIso_limit_pre_dominationProj (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) :
    IsIso (limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
      (dominationProj S S' fS fX hf V)) := by
  refine ⟨dominationInv S S' fS fX hf E G V, limit.hom_ext fun i ↦ ?_,
    limit.hom_ext fun d ↦ ?_⟩
  · rw [Category.assoc, dominationInv_comp_π, Category.id_comp]
    refine G.cond.hom_ext (dominationCover S S' fS fX hf V i) _ _ fun I ↦ ?_
    have hA : limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          (dominationProj S S' fS fX hf V) ≫
            dominationPi S S' fS fX hf E G V I.hf =
        limit.π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          ((dominationProj S S' fS fX hf V).obj
            (dominationChoice S S' fS fX hf V I.hf)) :=
      limit.pre_π _ _ _
    have hB : limit.π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj) i ≫
          G.obj.map I.f.op =
        limit.π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          ((dominationProj S S' fS fX hf V).obj
            (dominationChoice S S' fS fX hf V I.hf)) :=
      limit.w (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
        (StructuredArrow.homMk (f' := (dominationProj S S' fS fX hf V).obj
          (dominationChoice S S' fS fX hf V I.hf)) I.f.op (Subsingleton.elim _ _))
    rw [Category.assoc, dominationLeg_comp_map, hA, hB]
  · rw [Category.assoc, limit.pre_π, dominationInv_comp_π, Category.id_comp]
    refine G.cond.hom_ext (dominationCover S S' fS fX hf V
      ((dominationProj S S' fS fX hf V).obj d)) _ _ fun I ↦ ?_
    have hA : limit.π (dominationDiagram S S' fS fX hf E G V) d ≫ G.obj.map I.f.op =
        limit.π (dominationDiagram S S' fS fX hf E G V)
          (dominationStructuredArrow S S' fS fX hf V I.Y d.right.left.unop
            (dominationPairs_mem S S' fS fX hf V d)
            ((crisToBig S S' fS fX hf).map I.f ≫ d.right.hom.unop)) :=
      limit.w (dominationDiagram S S' fS fX hf E G V)
        (dominationRefine S S' fS fX hf V d I.Y I.f)
    have hB : dominationPi S S' fS fX hf E G V I.hf =
        limit.π (dominationDiagram S S' fS fX hf E G V)
          (dominationStructuredArrow S S' fS fX hf V I.Y d.right.left.unop
            (dominationPairs_mem S S' fS fX hf V d)
            ((crisToBig S S' fS fX hf).map I.f ≫ d.right.hom.unop)) :=
      limit_π_dominationStructuredArrow_eq S S' fS fX hf E G V I.Y _ _ _ _ _ _
    rw [dominationLeg_comp_map, hB, hA]

/-- The canonical `2`-cell `crisZariskiCellApp` of the square of topoi, read at an open `V` of `X`,
is an isomorphism. -/
instance isIso_crisZariskiCellApp (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) :
    IsIso (crisZariskiCellApp S S' fS fX hf E G V) := by
  rw [crisZariskiCellApp]
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (IsIso.comp_isIso' (isIso_limit_pre_dominationProj S S' fS fX hf E G V)
      (Iso.isIso_inv (crisZariskiLeftObjIsoCoeff S S' fS fX hf E G V)))

/-! ### The `2`-cell as the base change of a right Kan extension -/

/-- The square of categories formed by `dominationToOpens`, the projection of the dominating pairs
to `Cris(X'/S)`, the preimage of opens along `f` and `forgetToOpens`, commuting up to the `2`-cell
which at a dominating pair `(A, A', k)` is the inclusion `U_{A'} ⊆ f^{-1}U_A`. -/
def crisZariskiTwoSquare :
    TwoSquare (dominationToOpens S S' fS fX hf)
      (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf))
      (TopologicalSpace.Opens.map fX.base).op (forgetToOpens S).op :=
  TwoSquare.mk _ _ _ _
    { app := fun d ↦ (homOfLE (dominationPairs_le_preimage S S' fS fX hf _
        (StructuredArrow.mk (Y := d) (𝟙 _)))).op
      naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }

/-- At an open `V` of `X`, the base change of right Kan extensions along `crisZariskiTwoSquare`,
composed with the limit formulas for the two right Kan extensions, is the comparison
`CategoryTheory.Limits.limit.pre` along `dominationProj`. -/
theorem crisZariskiRanBaseChange_app_app
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
          (D := E)).app G.obj).app (op V) ≫
        ((dominationToOpens S S' fS fX hf).ranObjObjIsoLimit
          (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj)
          (op V)).hom =
      ((forgetToOpens S).op.ranObjObjIsoLimit G.obj (op (fX ⁻¹ᵁ V))).hom ≫
        limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
          (dominationProj S S' fS fX hf V) := by
  refine limit.hom_ext fun d ↦ ?_
  have hs : ((dominationProj S S' fS fX hf V).obj d).hom =
      (TopologicalSpace.Opens.map fX.base).op.map d.hom ≫
        (crisZariskiTwoSquare S S' fS fX hf).natTrans.app d.right :=
    Subsingleton.elim _ _
  have hpre : limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
        (dominationProj S S' fS fX hf V) ≫
      limit.π (StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
        Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) d =
    limit.π (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
      ((dominationProj S S' fS fX hf V).obj d) :=
    limit.pre_π _ _ _
  refine ((Category.assoc _ _ _).trans
    (TwoSquare.ranBaseChange_app_app_comp_π _ G.obj (op V) d)).trans ?_
  refine (congrArg (fun m ↦ ((forgetToOpens S).op.ran.obj G.obj).map m ≫
    ((forgetToOpens S).op.ranCounit.app G.obj).app
      ((Comma.snd (CrystallineThickening.ι S').op
        (crisToBigOp S S' fS fX hf)).obj d.right)) hs.symm).trans ?_
  exact (Functor.ranObjObjIsoLimit_hom_π (forgetToOpens S).op G.obj (op (fX ⁻¹ᵁ V))
    ((dominationProj S S' fS fX hf V).obj d)).symm.trans
      ((congrArg (fun m ↦ ((forgetToOpens S).op.ranObjObjIsoLimit G.obj (op (fX ⁻¹ᵁ V))).hom ≫ m)
        hpre).symm.trans (Category.assoc _ _ _).symm)

/-- The base change along `crisZariskiTwoSquare` is an isomorphism at each open `V` of `X`. -/
instance isIso_crisZariskiRanBaseChange_app_app
    (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    IsIso ((((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
      (D := E)).app G.obj).app (op V)) := by
  have hu : IsIso ((((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
        (D := E)).app G.obj).app (op V) ≫
      ((dominationToOpens S S' fS fX hf).ranObjObjIsoLimit
        (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj)
        (op V)).hom) := by
    rw [crisZariskiRanBaseChange_app_app S S' fS fX hf E G V]
    exact IsIso.comp_isIso' (Iso.isIso_hom _)
      (isIso_limit_pre_dominationProj S S' fS fX hf E G V)
  exact IsIso.of_isIso_comp_right _ ((dominationToOpens S S' fS fX hf).ranObjObjIsoLimit
    (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) (op V)).hom

/-- The base change along `crisZariskiTwoSquare` is an isomorphism at each sheaf. -/
instance isIso_crisZariskiRanBaseChange_app
    (G : Sheaf (smallTopology S) E) :
    IsIso (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
      (D := E)).app G.obj) := by
  have : ∀ X, IsIso ((((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
      (D := E)).app G.obj).app X) := fun X ↦
    isIso_crisZariskiRanBaseChange_app_app S S' fS fX hf E G X.unop
  exact NatIso.isIso_of_isIso_app _

/-- The `2`-cell `f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` on underlying presheaves, with
coefficients in `E`: the base change along `crisZariskiTwoSquare` followed by the inverse of
`crisZariskiLeftIsoCoeff`. -/
def crisZariskiCellPreCoeff :
    sheafToPresheaf (smallTopology S) E ⋙
        (forgetToOpens S).op.ran ⋙
          (Functor.whiskeringLeft _ _ E).obj
            (TopologicalSpace.Opens.map fX.base).op ⟶
      crisDirectImageCoeff S S' fS fX hf E ⋙ zariskiDirectImageCoeff S' E ⋙
        sheafToPresheaf (opensTopology S') E :=
  Functor.whiskerLeft (sheafToPresheaf (smallTopology S) E)
      (crisZariskiTwoSquare S S' fS fX hf).ranBaseChange ≫
    (crisZariskiLeftIsoCoeff S S' fS fX hf E).inv

/-- `crisZariskiCellPreCoeff` at one sheaf is the base change followed by the flattening. -/
theorem crisZariskiCellPreCoeff_app (G : Sheaf (smallTopology S) E) :
    (crisZariskiCellPreCoeff S S' fS fX hf E).app G =
      (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange (D := E)).app G.obj) ≫
        ((crisZariskiLeftIsoCoeff S S' fS fX hf E).app G).inv :=
  rfl

/-- `crisZariskiCellPreCoeff` is invertible at one sheaf. -/
instance isIso_crisZariskiCellPreCoeff_app (G : Sheaf (smallTopology S) E) :
    IsIso ((crisZariskiCellPreCoeff S S' fS fX hf E).app G) := by
  rw [crisZariskiCellPreCoeff_app]
  exact IsIso.comp_isIso' (isIso_crisZariskiRanBaseChange_app S S' fS fX hf E G)
    (Iso.isIso_inv _)

/-- The `2`-cell `f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` of the square of topoi, with
coefficients in `E`, whose underlying morphisms of presheaves are `crisZariskiCellPreCoeff`. -/
def crisZariskiCellCoeff :
    zariskiDirectImageCoeff S E ⋙
        (TopologicalSpace.Opens.map fX.base).sheafPushforwardContinuous E
          (opensTopology S') (opensTopology S) ⟶
      crisDirectImageCoeff S S' fS fX hf E ⋙ zariskiDirectImageCoeff S' E where
  app G := Sheaf.Hom.mk ((crisZariskiCellPreCoeff S S' fS fX hf E).app G)
  naturality _ _ ψ :=
    (sheafToPresheaf (opensTopology S') E).map_injective
      ((crisZariskiCellPreCoeff S S' fS fX hf E).naturality ψ)

/-- The `2`-cell `crisZariskiCellCoeff` is an isomorphism. -/
instance isIso_crisZariskiCellCoeff : IsIso (crisZariskiCellCoeff S S' fS fX hf E) := by
  have : ∀ G, IsIso ((crisZariskiCellCoeff S S' fS fX hf E).app G) := fun G ↦
    haveI : IsIso ((sheafToPresheaf (opensTopology S') E).map
        ((crisZariskiCellCoeff S S' fS fX hf E).app G)) :=
      isIso_crisZariskiCellPreCoeff_app S S' fS fX hf E G
    (fullyFaithfulSheafToPresheaf (opensTopology S') E).isIso_of_isIso_map _
  exact NatIso.isIso_of_isIso_app _

/-- The commutation `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}` of the square of topoi with
coefficients in `E`: the inverse of `crisZariskiCellCoeff`. -/
def crisZariskiSquareCoeff :
    crisDirectImageCoeff S S' fS fX hf E ⋙ zariskiDirectImageCoeff S' E ≅
      zariskiDirectImageCoeff S E ⋙
        (TopologicalSpace.Opens.map fX.base).sheafPushforwardContinuous E
          (opensTopology S') (opensTopology S) :=
  (asIso (crisZariskiCellCoeff S S' fS fX hf E)).symm

/-! ### Abelian coefficients -/

/-- `crisZariskiCellPreCoeff` with abelian coefficients, phrased with `crisDirectImage` and
`zariskiDirectImage`. -/
def crisZariskiCellPre :
    sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (forgetToOpens S).op.ran ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
            (TopologicalSpace.Opens.map fX.base).op ⟶
      crisDirectImage S S' fS fX hf ⋙ zariskiDirectImage S' ⋙
        sheafToPresheaf (opensTopology S') AddCommGrpCat.{u + 1} :=
  crisZariskiCellPreCoeff S S' fS fX hf AddCommGrpCat.{u + 1}

/-- `crisZariskiCellPre` at one abelian sheaf is the base change followed by the flattening. -/
theorem crisZariskiCellPre_app (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (crisZariskiCellPre S S' fS fX hf).app G =
      (((crisZariskiTwoSquare S S' fS fX hf).ranBaseChange
          (D := AddCommGrpCat.{u + 1})).app G.obj) ≫
        ((crisZariskiLeftIsoCoeff S S' fS fX hf AddCommGrpCat.{u + 1}).app G).inv :=
  rfl

/-- `crisZariskiCellPre` is invertible at one abelian sheaf. -/
instance isIso_crisZariskiCellPre_app
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    IsIso ((crisZariskiCellPre S S' fS fX hf).app G) :=
  isIso_crisZariskiCellPreCoeff_app S S' fS fX hf AddCommGrpCat.{u + 1} G

/-- The `2`-cell `f_{Zar, *}u_{X'/S, *} ⟶ u_{X/S, *}f_{cris, *}` of the square of topoi on abelian
sheaves: `crisZariskiCellCoeff` at `AddCommGrpCat.{u + 1}`. -/
def crisZariskiCell :
    zariskiDirectImage S ⋙ zariskiPushforward S S' fX ⟶
      crisDirectImage S S' fS fX hf ⋙ zariskiDirectImage S' :=
  crisZariskiCellCoeff S S' fS fX hf AddCommGrpCat.{u + 1}

/-- The `2`-cell `crisZariskiCell` is an isomorphism. -/
instance isIso_crisZariskiCell : IsIso (crisZariskiCell S S' fS fX hf) :=
  isIso_crisZariskiCellCoeff S S' fS fX hf AddCommGrpCat.{u + 1}

/-- The commutation `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}` of the square of topoi on
abelian sheaves: the inverse of `crisZariskiCell`. -/
def crisZariskiSquare : CrisZariskiSquare S S' fS fX hf :=
  (asIso (crisZariskiCell S S' fS fX hf)).symm

/-- The square of topoi `u_{X/S, *}f_{cris, *} ≅ f_{Zar, *}u_{X'/S, *}` commutes. -/
theorem hasCrisZariskiSquare : HasCrisZariskiSquare S S' fS fX hf :=
  ⟨crisZariskiSquare S S' fS fX hf⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
