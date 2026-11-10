module

public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Multiplication
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic

/-!
# The multiplication morphism `ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹`

The morphism sending a pair `((x : y), A)` of a point of the projective line and a binary form
`A(T) = a₀ Tⁿ + … + aₙ` to the product `(x T + y) A(T)` is glued from the two chart morphisms of
`StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Multiplication`, over the cover of
`ℙ¹ × ℙⁿ = ℙ¹_{ℙⁿ}` by the preimages of the two standard charts of the projective line.

## Main definitions

* `Stacks.ProjectiveLineCover.multiplication`: the morphism
  `ProjectiveSpace 1 (ProjectiveSpaceZ n) ⟶ ProjectiveSpaceZ (n + 1)` over the integers.

## Implementation notes

The `i`-th piece of the cover is the fibre product of `ℙⁿ_ℤ` with the chart `Spec B_i` of
`ℙ¹_ℤ`, i.e. projective `n`-space over `B_i`, and on it the morphism is the chart morphism read
through `Stacks.ProjectiveCohomology.projModelIso`. Two pieces meet over the overlap
`Spec B_{01}` of the two charts, by `AlgebraicGeometry.Proj.pullbackAwayιIso`, and the agreement
there is `Stacks.ProjectiveLineCover.projModelMap_comp_mulMapX_eq`, carried along the naturality
of `Stacks.ProjectiveCohomology.projModelIso` in the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open Stacks.ProjectiveCohomology Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveLineCover

/-! ### The charts of the projective line -/

/-- The coordinate ring `ℤ[y/x]` or `ℤ[x/y]` of a standard chart of `ℙ¹_ℤ`. -/
abbrev chartRing (i : Fin 2) : Type u :=
  Away (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) (X i)

/-- The coordinate ring of the overlap of the two standard charts of `ℙ¹_ℤ`. -/
abbrev overlapRing : Type u :=
  Away (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
    (X 0 * X 1 : MvPolynomial (Fin 2) (ULift.{u} ℤ))

/-- The affine coordinate `t = y / x` on the chart `x ≠ 0`. -/
def coordT : chartRing.{u} 0 :=
  Away.mk _ (X_mem_one (ULift.{u} ℤ) 1 0) 1 (X 1) (X_mem_smul (ULift.{u} ℤ) 1 1)

/-- The affine coordinate `σ = x / y` on the chart `y ≠ 0`. -/
def coordS : chartRing.{u} 1 :=
  Away.mk _ (X_mem_one (ULift.{u} ℤ) 1 1) 1 (X 0) (X_mem_smul (ULift.{u} ℤ) 1 0)

/-- Restriction from the chart `x ≠ 0` to the overlap. -/
def toOverlapX : chartRing.{u} 0 →+* overlapRing.{u} :=
  awayMap _ (X_mem_one (ULift.{u} ℤ) 1 1) rfl

/-- Restriction from the chart `y ≠ 0` to the overlap. -/
def toOverlapY : chartRing.{u} 1 →+* overlapRing.{u} :=
  awayMap _ (X_mem_one (ULift.{u} ℤ) 1 0) (mul_comm _ _)

/-- On the overlap `t σ = 1`. -/
theorem toOverlapX_mul_toOverlapY : toOverlapX.{u} coordT * toOverlapY.{u} coordS = 1 := by
  rw [toOverlapX, toOverlapY, coordT, coordS, awayMap_mk, awayMap_mk]
  ext
  simp only [val_mul, Away.val_mk, val_one]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-! ### The cover of `ℙ¹ × ℙⁿ` by the two charts of the projective line -/

variable (n : ℕ)

/-- The open immersion of the `i`-th standard chart into `ℙ¹_ℤ`. -/
def lineChart (i : Fin 2) :
    Spec (CommRingCat.of (chartRing.{u} i)) ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Proj.awayι (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) (X i)
    (X_mem_one (ULift.{u} ℤ) 1 i) Nat.one_pos

/-- Each standard chart of `ℙ¹_ℤ` is an open immersion. -/
instance (i : Fin 2) : IsOpenImmersion (lineChart.{u} i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι
    (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) (X i)
    (X_mem_one (ULift.{u} ℤ) 1 i) Nat.one_pos))

/-- The two charts of the projective line meet in the spectrum of `overlapRing`. -/
theorem isPullback_lineChart :
    IsPullback (Spec.map (CommRingCat.ofHom toOverlapX.{u}))
      (Spec.map (CommRingCat.ofHom toOverlapY.{u})) (lineChart.{u} 0) (lineChart.{u} 1) :=
  IsPullback.of_iso_pullback
    ⟨(Proj.SpecMap_awayMap_awayι _ (X_mem_one (ULift.{u} ℤ) 1 0) Nat.one_pos
        (X_mem_one (ULift.{u} ℤ) 1 1) (rfl : (X 0 * X 1 : MvPolynomial (Fin 2) (ULift.{u} ℤ)) =
          X 0 * X 1)).trans
      (Proj.SpecMap_awayMap_awayι _ (X_mem_one (ULift.{u} ℤ) 1 1) Nat.one_pos
        (X_mem_one (ULift.{u} ℤ) 1 0) (mul_comm _ _)).symm⟩
    (Proj.pullbackAwayιIso (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
      (X_mem_one (ULift.{u} ℤ) 1 0) Nat.one_pos (X_mem_one (ULift.{u} ℤ) 1 1) Nat.one_pos
      (rfl : (X 0 * X 1 : MvPolynomial (Fin 2) (ULift.{u} ℤ)) = X 0 * X 1)).symm
    (Proj.pullbackAwayιIso_inv_fst _ _ _ _ _
      (rfl : (X 0 * X 1 : MvPolynomial (Fin 2) (ULift.{u} ℤ)) = X 0 * X 1))
    (Proj.pullbackAwayιIso_inv_snd _ _ _ _ _
      (rfl : (X 0 * X 1 : MvPolynomial (Fin 2) (ULift.{u} ℤ)) = X 0 * X 1))

/-- `ℙ¹ × ℙⁿ`, as the projective line over `ℙⁿ_ℤ`. -/
abbrev Prod : Scheme.{u} := projectiveSpaceOver 1 (projectiveSpaceAtUniverse.{u} n)

/-- The preimage in `ℙ¹ × ℙⁿ` of the `i`-th chart of the projective line. -/
abbrev Piece (i : Fin 2) : Scheme.{u} :=
  pullback (terminal.from (projectiveSpaceAtUniverse.{u} n))
    (terminal.from (Spec (CommRingCat.of (chartRing.{u} i))))

/-- The inclusion of the `i`-th piece. -/
def pieceι (i : Fin 2) : Piece.{u} n i ⟶ Prod.{u} n :=
  pullback.map _ _ _ _ (𝟙 _) (lineChart.{u} i) (𝟙 _) (by simp) (terminal.hom_ext _ _)

/-- The inclusion of the `i`-th piece commutes with the projections to `ℙⁿ_ℤ`. -/
@[reassoc (attr := simp)]
theorem pieceι_fst (i : Fin 2) : pieceι n i ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [pieceι, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The inclusion of the `i`-th piece lies over the `i`-th chart of the projective line. -/
@[reassoc (attr := simp)]
theorem pieceι_snd (i : Fin 2) :
    pieceι n i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ lineChart.{u} i := by
  rw [pieceι, pullback.map, pullback.lift_snd]

/-- The cover of `ℙ¹_ℤ` by its two standard charts. -/
abbrev lineCover : (projectiveSpaceAtUniverse.{u} 1).OpenCover :=
  (affineChartCover (ULift.{u} ℤ) 1).openCover

/-- The `i`-th piece is the preimage of the `i`-th chart of the projective line. -/
theorem isPullback_pieceι (i : Fin 2) :
    IsPullback (pieceι.{u} n i) (pullback.snd _ _) (pullback.snd _ _) (lineChart.{u} i) := by
  refine IsPullback.of_right ?_ (pieceι_snd n i) (IsPullback.of_hasPullback _ _)
  rw [pieceι_fst, show lineChart.{u} i ≫ terminal.from (projectiveSpaceAtUniverse.{u} 1) =
    terminal.from _ from terminal.hom_ext _ _]
  exact IsPullback.of_hasPullback _ _

/-- The inclusion of each piece into `ℙ¹ × ℙⁿ` is an open immersion. -/
instance (i : Fin 2) : IsOpenImmersion (pieceι.{u} n i) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_pieceι n i).flip inferInstance

/-- The cover of `ℙ¹ × ℙⁿ` by its two pieces. -/
def productCover : (Prod.{u} n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2) (Piece.{u} n) (pieceι n) fun x => by
    have hx : pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
        (terminal.from (projectiveSpaceAtUniverse.{u} 1)) x ∈ (⨆ i : Fin 2,
          Proj.basicOpen (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
            (X i)) := by
      rw [iSup_basicOpen_X_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    rw [← Proj.opensRange_awayι _ _ (X_mem_one (ULift.{u} ℤ) 1 i) Nat.one_pos] at hi
    obtain ⟨y, hy⟩ := hi
    change lineChart.{u} i y = _ at hy
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨i, (isPullback_pieceι n i).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]

/-- The `i`-th morphism of `productCover` is the inclusion of the `i`-th piece. -/
@[simp] theorem productCover_f (i : Fin 2) : (productCover.{u} n).f i = pieceι n i := rfl

/-- The `i`-th piece, read as projective `n`-space over the chart ring. -/
abbrev pieceIso (i : Fin 2) :
    Piece.{u} n i ≅ projectiveSpaceOverRing n (CommRingCat.of (chartRing.{u} i)) :=
  pullbackSymmetry _ _

/-- A morphism to projective `n`-space over `R` whose coefficient component factors through
`Spec S → Spec R` factors through `projectiveSpaceOverRingMap n f`. -/
theorem lift_comp_projectiveSpaceOverRingMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {W : Scheme.{u}} (δ : W ⟶ Spec (CommRingCat.of S))
    (β : W ⟶ projectiveSpaceAtUniverse.{u} n) :
    (pullback.lift (δ ≫ Spec.map (CommRingCat.ofHom f)) β (terminal.hom_ext _ _) :
        W ⟶ projectiveSpaceOverRing n (CommRingCat.of R)) =
      pullback.lift δ β (terminal.hom_ext _ _) ≫
        projectiveSpaceOverRingMap n (CommRingCat.ofHom f) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, projectiveSpaceOverRingMap, projectiveSpaceOverMap_fst,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, projectiveSpaceOverRingMap, projectiveSpaceOverMap_snd,
      pullback.lift_snd]

/-- Naturality of `projModelIso` in the coefficient ring: under it, the base change morphism
`projectiveSpaceOverRingMap n f` corresponds to `projModelMap n f`. -/
theorem projectiveSpaceOverRingMap_comp_projModelIso_inv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    projectiveSpaceOverRingMap n (CommRingCat.ofHom f) ≫ (projModelIso R n).inv =
      (projModelIso S n).inv ≫ projModelMap n f := by
  rw [Iso.comp_inv_eq, Category.assoc, projModelMap_comp_projModelIso_hom, Iso.inv_hom_id_assoc]

/-- The multiplication morphism on the `i`-th piece. -/
def chartMul : (i : Fin 2) → (Piece.{u} n i ⟶ projectiveSpaceAtUniverse.{u} (n + 1))
  | 0 => (pieceIso n 0).hom ≫ (projModelIso (chartRing.{u} 0) n).inv ≫ mulMapX n coordT
  | 1 => (pieceIso n 1).hom ≫ (projModelIso (chartRing.{u} 1) n).inv ≫ mulMapY n coordS

/-- The `i`-th chart morphism on a point of the piece whose chart coordinate factors through a
ring homomorphism `f : chartRing i → R`. -/
theorem lift_comp_pieceIso_projModelIso {W : Scheme.{u}} {R : Type u} [CommRing R] (i : Fin 2)
    (f : chartRing.{u} i →+* R) (δ : W ⟶ Spec (CommRingCat.of R))
    (β : W ⟶ projectiveSpaceAtUniverse.{u} n) :
    (pullback.lift β (δ ≫ Spec.map (CommRingCat.ofHom f)) (terminal.hom_ext _ _) :
        W ⟶ Piece.{u} n i) ≫ (pieceIso n i).hom ≫ (projModelIso (chartRing.{u} i) n).inv =
      pullback.lift δ β (terminal.hom_ext _ _) ≫ (projModelIso R n).inv ≫ projModelMap n f := by
  have h1 : (pullback.lift β (δ ≫ Spec.map (CommRingCat.ofHom f)) (terminal.hom_ext _ _) :
        W ⟶ Piece.{u} n i) ≫ (pieceIso n i).hom =
      pullback.lift (δ ≫ Spec.map (CommRingCat.ofHom f)) β (terminal.hom_ext _ _) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]
  rw [← Category.assoc, h1, lift_comp_projectiveSpaceOverRingMap, Category.assoc,
    projectiveSpaceOverRingMap_comp_projModelIso_inv]

/-- **The two chart morphisms agree on the overlap of the pieces.** -/
theorem chartMul_compat {W : Scheme.{u}} (a : W ⟶ Piece.{u} n 0) (b : W ⟶ Piece.{u} n 1)
    (hab : a ≫ pieceι n 0 = b ≫ pieceι n 1) :
    a ≫ chartMul n 0 = b ≫ chartMul n 1 := by
  have hP : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
    simpa using congrArg (· ≫ pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} 1))) hab
  have hL : (a ≫ pullback.snd _ _) ≫ lineChart.{u} 0 =
      (b ≫ pullback.snd _ _) ≫ lineChart.{u} 1 := by
    simpa using congrArg (· ≫ pullback.snd (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} 1))) hab
  obtain ⟨δ, hδx, hδy⟩ : ∃ δ : W ⟶ Spec (CommRingCat.of overlapRing.{u}),
      δ ≫ Spec.map (CommRingCat.ofHom toOverlapX.{u}) = a ≫ pullback.snd _ _ ∧
      δ ≫ Spec.map (CommRingCat.ofHom toOverlapY.{u}) = b ≫ pullback.snd _ _ :=
    ⟨isPullback_lineChart.lift _ _ hL, isPullback_lineChart.lift_fst _ _ _,
      isPullback_lineChart.lift_snd _ _ _⟩
  have ha : a = pullback.lift (a ≫ pullback.fst _ _)
      (δ ≫ Spec.map (CommRingCat.ofHom toOverlapX.{u})) (terminal.hom_ext _ _) :=
    pullback.hom_ext (by rw [pullback.lift_fst]) (by rw [pullback.lift_snd, hδx])
  have hb : b = pullback.lift (a ≫ pullback.fst _ _)
      (δ ≫ Spec.map (CommRingCat.ofHom toOverlapY.{u})) (terminal.hom_ext _ _) :=
    pullback.hom_ext (by rw [pullback.lift_fst, hP]) (by rw [pullback.lift_snd, hδy])
  have hx : a ≫ chartMul n 0 = pullback.lift δ (a ≫ pullback.fst _ _) (terminal.hom_ext _ _) ≫
      (projModelIso overlapRing.{u} n).inv ≫ projModelMap n toOverlapX.{u} ≫ mulMapX n coordT := by
    conv_lhs => rw [ha]
    change _ ≫ (pieceIso n 0).hom ≫ (projModelIso (chartRing.{u} 0) n).inv ≫ mulMapX n coordT = _
    rw [← Category.assoc (pieceIso n 0).hom, ← Category.assoc,
      lift_comp_pieceIso_projModelIso]
    simp only [Category.assoc]
  have hy : b ≫ chartMul n 1 = pullback.lift δ (a ≫ pullback.fst _ _) (terminal.hom_ext _ _) ≫
      (projModelIso overlapRing.{u} n).inv ≫ projModelMap n toOverlapY.{u} ≫ mulMapY n coordS := by
    conv_lhs => rw [hb]
    change _ ≫ (pieceIso n 1).hom ≫ (projModelIso (chartRing.{u} 1) n).inv ≫ mulMapY n coordS = _
    rw [← Category.assoc (pieceIso n 1).hom, ← Category.assoc,
      lift_comp_pieceIso_projModelIso]
    simp only [Category.assoc]
  rw [hx, hy, projModelMap_comp_mulMapX_eq n coordT coordS toOverlapX toOverlapY
    toOverlapX_mul_toOverlapY]

/-- The gluing condition for the chart morphisms. -/
theorem chartMul_glue (i j : Fin 2) :
    pullback.fst (pieceι.{u} n i) (pieceι n j) ≫ chartMul n i =
      pullback.snd (pieceι.{u} n i) (pieceι n j) ≫ chartMul n j := by
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [fst_eq_snd_of_mono_eq]
  · exact chartMul_compat n _ _ pullback.condition
  · exact (chartMul_compat n _ _ pullback.condition.symm).symm
  · simp only [Fin.mk_one, Fin.isValue]
    rw [fst_eq_snd_of_mono_eq]

/-- **The multiplication morphism `ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹`**, sending `((x : y), A)` to `(x T + y) A`. -/
def multiplication : Prod.{u} n ⟶ projectiveSpaceAtUniverse.{u} (n + 1) :=
  (productCover.{u} n).glueMorphisms (chartMul n) fun i j => chartMul_glue n i j

/-- On the `i`-th piece, `multiplication` restricts to the chart morphism `chartMul n i`. -/
@[reassoc (attr := simp)]
theorem pieceι_multiplication (i : Fin 2) :
    pieceι.{u} n i ≫ multiplication.{u} n = chartMul.{u} n i :=
  (productCover.{u} n).ι_glueMorphisms _ _ i

end Stacks.ProjectiveLineCover
