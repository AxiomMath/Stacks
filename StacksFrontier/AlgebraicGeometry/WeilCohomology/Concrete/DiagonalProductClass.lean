module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassMap
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionExteriorClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The class of the diagonal of a product

Let `X` and `Y` be smooth projective schemes over a field `k`, of constant dimensions `d` and
`e`. The diagonal `Δ_{X × Y}` of `X × Y` is the inverse image of `Δ_X × Δ_Y ⊆ (X × X) × (Y × Y)`
under the isomorphism `σ : (X × Y) × (X × Y) ⟶ (X × X) × (Y × Y)`, `(x, y, x', y') ↦
(x, x', y, y')`, whose components are the products `p = pr₁ × pr₁` and `q = pr₂ × pr₂` of the
projections. On Chow groups graded by codimension this reads

  `[Δ_{X × Y}] = σ^!([Δ_X] × [Δ_Y])`   in   `CH^{d+e}((X × Y) × (X × Y))`,

with `×` the exterior product of Stacks 0FBV and `σ^!` the Gysin map of Stacks 0FF3: the exterior
product of the classes of the two diagonals is the class of their product
(`Stacks.Chow.codimensionExteriorProduct_closedSubschemeClass`), and the Gysin map of the flat
morphism `σ` carries it to the class of its inverse image
(`Stacks.Chow.codimensionGysin_closedSubschemeClass_of_flat`). This is the observation in the
proof of Stacks 0FIL that "the diagonal `Δ_{X × Y}` is the intersection product of the pullbacks of
the diagonals `Δ_X` and `Δ_Y` by the projections `p` and `q`", since
`α × β = pr₁^!α · pr₂^!β`
(`Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct`).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.prodShuffle`: the isomorphism
  `σ : (X × Y) × (X × Y) ⟶ (X × X) × (Y × Y)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass_prod`:
  `[Δ_{X × Y}] = σ^!([Δ_X] × [Δ_Y])`.

## References

* [Stacks Project, Tag 0FIL](https://stacks.math.columbia.edu/tag/0FIL)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **The shuffle `σ : (X × Y) × (X × Y) ⟶ (X × X) × (Y × Y)`**, `(x, y, x', y') ↦
(x, x', y, y')`, with components `pr₁ × pr₁` and `pr₂ × pr₂`. -/
def prodShuffle (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X Y) (prod X Y) ⟶ prod (prod X X) (prod Y Y) :=
  prodLift (prodMap (fst X Y) (fst X Y)) (prodMap (snd X Y) (snd X Y))

/-- The first component of the shuffle is `pr₁ × pr₁ : (X × Y) × (X × Y) ⟶ X × X`. -/
@[reassoc (attr := simp)]
theorem prodShuffle_fst (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prodShuffle X Y ≫ fst (prod X X) (prod Y Y) = prodMap (fst X Y) (fst X Y) :=
  prodLift_fst _ _

/-- The second component of the shuffle is `pr₂ × pr₂ : (X × Y) × (X × Y) ⟶ Y × Y`. -/
@[reassoc (attr := simp)]
theorem prodShuffle_snd (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prodShuffle X Y ≫ snd (prod X X) (prod Y Y) = prodMap (snd X Y) (snd X Y) :=
  prodLift_snd _ _

/-- The inverse `(X × X) × (Y × Y) ⟶ (X × Y) × (X × Y)` of the shuffle. -/
def prodShuffleInv (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X X) (prod Y Y) ⟶ prod (prod X Y) (prod X Y) :=
  prodLift (prodMap (fst X X) (fst Y Y)) (prodMap (snd X X) (snd Y Y))

/-- `prodShuffleInv` is a right inverse of the shuffle. -/
theorem prodShuffle_prodShuffleInv (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prodShuffle X Y ≫ prodShuffleInv X Y = 𝟙 _ := by
  refine prod_hom_ext (prod_hom_ext ?_ ?_) (prod_hom_ext ?_ ?_) <;> simp [prodShuffleInv]

/-- `prodShuffleInv` is a left inverse of the shuffle. -/
theorem prodShuffleInv_prodShuffle (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prodShuffleInv X Y ≫ prodShuffle X Y = 𝟙 _ := by
  refine prod_hom_ext (prod_hom_ext ?_ ?_) (prod_hom_ext ?_ ?_) <;> simp [prodShuffleInv]

/-- The underlying morphism of schemes of the shuffle is an isomorphism. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) : IsIso (prodShuffle X Y).hom.left :=
  ⟨(prodShuffleInv X Y).hom.left, congrArg (fun φ ↦ φ.hom.left) (prodShuffle_prodShuffleInv X Y),
    congrArg (fun φ ↦ φ.hom.left) (prodShuffleInv_prodShuffle X Y)⟩

/-- The diagonal composed with its structure morphism is the structure morphism. -/
theorem diag_left_comp_hom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (diag X).hom.left ≫ (prod X X).obj.hom = X.obj.hom :=
  Over.w (diag X).hom

/-- The product `Δ_X × Δ_Y : X ×_k Y ⟶ (X × X) ×_k (Y × Y)` of the two diagonals, on the fibre
products of the structure morphisms. -/
abbrev diagProdDiag (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (Limits.pullback X.obj.hom Y.obj.hom : Scheme.{u}) ⟶
      Limits.pullback (prod X X).obj.hom (prod Y Y).obj.hom :=
  Limits.pullback.map X.obj.hom Y.obj.hom (prod X X).obj.hom (prod Y Y).obj.hom
    (diag X).hom.left (diag Y).hom.left (𝟙 _) (by rw [diag_left_comp_hom]; simp)
    (by rw [diag_left_comp_hom]; simp)

/-- `Δ_X × Δ_Y` is the product of the morphisms `Δ_X` and `Δ_Y` of smooth projective schemes. -/
theorem prodMap_diag_left (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (prodMap (diag X) (diag Y)).hom.left = diagProdDiag X Y :=
  rfl

/-- `σ ∘ Δ_{X × Y} = Δ_X × Δ_Y`. -/
theorem diag_prodShuffle (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    diag (prod X Y) ≫ prodShuffle X Y = prodMap (diag X) (diag Y) :=
  prod_hom_ext (prod_hom_ext (by simp) (by simp)) (prod_hom_ext (by simp) (by simp))

/-- `Δ_X × Δ_Y` is a closed immersion. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    IsClosedImmersion (diagProdDiag X Y) :=
  Intersection.isClosedImmersion_pullbackMap _ _ _ _ _ _ _ _

/-- The shuffle on the fibre products of the structure morphisms. -/
abbrev prodShuffleLeft (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (prod (prod X Y) (prod X Y)).obj.left ⟶ Limits.pullback (prod X X).obj.hom (prod Y Y).obj.hom :=
  (prodShuffle X Y).hom.left

/-- The shuffle on the fibre products commutes with the structure morphisms to `Spec k`. -/
theorem prodShuffleLeft_comp (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    prodShuffleLeft X Y ≫ prodBase (prod X X).obj.hom (prod Y Y).obj.hom =
      (prod (prod X Y) (prod X Y)).obj.hom :=
  Over.w (prodShuffle X Y).hom

/-- The shuffle on the fibre products is an isomorphism. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) : IsIso (prodShuffleLeft X Y) :=
  inferInstanceAs (IsIso (prodShuffle X Y).hom.left)

/-- The shuffle on the fibre products is locally of finite type. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    LocallyOfFiniteType (prodShuffleLeft X Y) :=
  inferInstanceAs (LocallyOfFiniteType (prodShuffle X Y).hom.left)

/-- **`Δ_{X × Y}` is the inverse image of `Δ_X × Δ_Y` under the shuffle.** -/
theorem isPullback_diag_prodShuffle (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback (diag (prod X Y)).hom.left (𝟙 (prod X Y).obj.left)
      (prodShuffleLeft X Y) (diagProdDiag X Y) :=
  IsPullback.of_vert_isIso ⟨(congrArg (fun φ ↦ φ.hom.left) (diag_prodShuffle X Y)).trans
    (Category.id_comp _).symm⟩

/-- The class of `Δ_X × Δ_Y` in either presentation of its source as a fibre product. -/
theorem closedSubschemeClass_diagProdDiag (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (c : ℤ) :
    closedSubschemeClass (prodBase (prod X X).obj.hom (prod Y Y).obj.hom)
        (Limits.pullback.map ((diag X).hom.left ≫ (prod X X).obj.hom)
          ((diag Y).hom.left ≫ (prod Y Y).obj.hom) (prod X X).obj.hom (prod Y Y).obj.hom
          (diag X).hom.left (diag Y).hom.left (𝟙 _) (by simp) (by simp)) c =
      closedSubschemeClass (prodBase (prod X X).obj.hom (prod Y Y).obj.hom)
        (diagProdDiag X Y) c := by
  refine (closedSubschemeClass_congr_iso _ _ _ (asIso (Limits.pullback.map
    ((diag X).hom.left ≫ (prod X X).obj.hom) ((diag Y).hom.left ≫ (prod Y Y).obj.hom)
    X.obj.hom Y.obj.hom (𝟙 _) (𝟙 _) (𝟙 _) (by rw [diag_left_comp_hom]; simp)
    (by rw [diag_left_comp_hom]; simp))) ?_ c)
  exact Limits.pullback.hom_ext (by simp [-diag_left]) (by simp [-diag_left])

/-- **The class of the diagonal of a product**: for `X` and `Y` smooth projective over `k` of
constant dimensions `d` and `e`, `[Δ_{X × Y}] = σ^!([Δ_X] × [Δ_Y])` in `CH^{d+e}((X × Y)²)`, for
`σ` the shuffle, `σ^!` its Gysin map (Stacks 0FF3) and `×` the exterior product (Stacks 0FBV). -/
theorem diagonalClass_prod (X Y : (SmoothProjectiveScheme k).FullSubcategory) {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) :
    diagonalClass (prod X Y) (d + e) =
      codimensionGysin (prod (prod X Y) (prod X Y)).obj.hom (prod (prod X X) (prod Y Y)).obj.hom
        (SmoothProjectiveScheme.w (prodShuffle X Y)) ((d + e : ℕ) : ℤ)
        (codimensionExteriorProduct k (prod X X).obj.hom (prod Y Y).obj.hom d e
          (diagonalClass X d) (diagonalClass Y e)) := by
  have hsq : ∀ {Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ},
      RelativeDimension Z.obj.hom n → RelativeDimension (prod Z Z).obj.hom (n + n) :=
    fun h ↦ relativeDimension_prodBase_add k _ _ h h
  have hdiag : ∀ {Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ},
      RelativeDimension Z.obj.hom n →
        RelativeDimension ((diag Z).hom.left ≫ (prod Z Z).obj.hom) n :=
    fun h ↦ RelativeDimension.congr (diag_left_comp_hom _).symm h
  have hXX := hsq hX
  have hYY := hsq hY
  have hP := hsq (Z := prod X Y) (relativeDimension_prodBase_add k _ _ hX hY)
  have hQ : RelativeDimension (prod (prod X X) (prod Y Y)).obj.hom ((d + d) + (e + e)) :=
    relativeDimension_prodBase_add k _ _ hXX hYY
  -- `[Δ_X] × [Δ_Y] = [Δ_X × Δ_Y]`
  have hext := codimensionExteriorProduct_closedSubschemeClass k (prod X X).obj.hom
    (prod Y Y).obj.hom (diag X).hom.left (diag Y).hom.left hXX hYY (hdiag hX) (hdiag hY) d e
    (by push_cast; ring) (by push_cast; ring)
  -- the class of `Δ_X × Δ_Y` pulls back to the class of its inverse image
  have hZ : RelativeDimension (diagProdDiag X Y ≫ prodBase (prod X X).obj.hom (prod Y Y).obj.hom)
      (d + e) := by
    refine RelativeDimension.congr ?_ (relativeDimension_prodBase_add k _ _ hX hY)
    simp [prodBase, -diag_left]
  have hZ' : schemeDeltaDimension (fieldChowSituation k)
      (diagProdDiag X Y ≫ prodBase (prod X X).obj.hom (prod Y Y).obj.hom) ≤
        (((((d + d) + (e + e) : ℕ) : ℤ) - ((d : ℤ) + e) : ℤ) : EInt) :=
    iSup_le fun Z ↦ (congrArg (fun z : ℤ ↦ (z : EInt))
      (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hZ
        (m := (((d + d) + (e + e) : ℕ) : ℤ) - ((d : ℤ) + e)) (by push_cast; ring) Z)).le
  have hgys := codimensionGysin_closedSubschemeClass_of_flat (k := k)
    (prod (prod X Y) (prod X Y)).obj.hom (prodBase (prod X X).obj.hom (prod Y Y).obj.hom)
    (prodShuffleLeft_comp X Y) hP hQ (relativeDimension_of_isIso (prodShuffleLeft X Y))
    (by omega : 0 + ((d + d) + (e + e)) = (d + e) + (d + e)) (diagProdDiag X Y) ((d : ℤ) + e) hZ'
  have hsq := isPullback_diag_prodShuffle X Y
  have hcl := closedSubschemeClass_congr_iso (prod (prod X Y) (prod X Y)).obj.hom
    (diag (prod X Y)).hom.left (Limits.pullback.fst (prodShuffleLeft X Y) (diagProdDiag X Y))
    hsq.isoPullback hsq.isoPullback_hom_fst ((d : ℤ) + e)
  exact hcl.trans (hgys.symm.trans (congrArg (codimensionGysin _ _ _ _)
    ((closedSubschemeClass_diagProdDiag X Y _).symm.trans hext.symm)))

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
