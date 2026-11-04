module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeCycleClass
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeLinear
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeBlowup
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeGraded
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeTrace

/-!
# Axiom (A6) descends along a field extension (Lemma 0FVT)

The paragraph (A6) of the proof of Lemma 0FVT of the Stacks Project, for the cycle
class maps `γ`, `γ'` of Lemma 0FIF of cohomological Chern characters `h`, `h'` of the two data
(`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`).
It rests on the compatibility of the classes of the diagonals with the comparison isomorphisms
(`Stacks.WeilDeRham.FieldBaseChangeData.pullTw_codimensionCycleClass_diagonalClass`): the class
`γ([Δ])` of the diagonal of `X` maps to the class of the diagonal of `X_{k'}` in the fibre product
`(X × X)_{k'}` of `X_{k'}` with itself, which is `γ'([Δ'])` pulled back along
`(X × X)_{k'} ≅ X_{k'} × X_{k'}`. Then a normalised form over `F'` gives one over `F`
(`Stacks.WeilDeRham.exists_isDiagonalNormalized_of_fieldBaseChange`).

## Main results

* `Stacks.WeilDeRham.isNonemptyEquidimensional_fieldBaseChange`.
* `Stacks.WeilDeRham.FieldBaseChangeData.traceContract_fieldBaseChange`: the normalisation of
  (A6) for `X_{k'}` read on `(X × X)_{k'}`.
* `Stacks.WeilDeRham.traceAxiom_of_fieldBaseChange`: (A6) descends.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow
open Stacks.WeilCohomology
open Stacks.WeilCohomology.SmoothProjectiveScheme hiding specStructure
open Stacks.WeilCohomology.DiagonalExpansion (contractRight contractRight_tmul)

universe u w w'

namespace Stacks.WeilDeRham

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The base change of a nonempty scheme along a field extension is nonempty. -/
theorem nonempty_fieldBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory)
    (hX : Nonempty ((toScheme k).obj X)) :
    Nonempty ((toScheme k').obj ((fieldBaseChange k k').obj X)) := by
  obtain ⟨x⟩ := hX
  have : Surjective (specStructure k k') := by
    rw [surjective_iff]
    intro y
    exact ⟨Classical.choice (inferInstance : Nonempty (Spec (.of k'))), Subsingleton.elim _ _⟩
  have : Surjective (fieldBaseChangeProj (k' := k') X) :=
    MorphismProperty.of_isPullback (isPullback_fieldBaseChangeProj (k' := k') X).flip
      inferInstance
  obtain ⟨x', -⟩ := this.surj x
  exact ⟨x'⟩

/-- The base change of an equidimensional scheme of dimension `d` is equidimensional of
dimension `d`. -/
theorem isEquidim_fieldBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hd : RelativeDimension X.obj.hom d) :
    RelativeDimension ((fieldBaseChange k k').obj X).obj.hom d :=
  RelativeDimension.of_isPullback (isPullback_fieldBaseChangeProj (k' := k') X) hd

/-- The base change of a nonempty equidimensional scheme of dimension `d` is nonempty and
equidimensional of dimension `d`. -/
theorem isNonemptyEquidimensional_fieldBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory)
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    IsNonemptyEquidimensional ((fieldBaseChange k k').obj X) d where
  nonempty := nonempty_fieldBaseChange X hX.nonempty
  relativeDimension := isEquidim_fieldBaseChange X hX.relativeDimension

variable {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldBaseChangeData

variable (B : FieldBaseChangeData 𝔇 𝔇') (X : (SmoothProjectiveScheme k).FullSubcategory)

end FieldBaseChangeData

/-! ### The classes of the diagonals -/

section Diagonal

variable [CharZero F] [CharZero F']

/-- The comparison `(X × X)_{k'} ⟶ X_{k'} × X_{k'}` of the base change of `X × X`, a fibre
product of `X_{k'}` with itself, with the product. -/
abbrev prodFieldBaseChangeHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (fieldBaseChange k k').obj (prod X X) ⟶
      prod ((fieldBaseChange k k').obj X) ((fieldBaseChange k k').obj X) :=
  toProdOfIsPullback ((fieldBaseChange k k').map (fst X X)) ((fieldBaseChange k k').map (snd X X))

/-- The comparison `(X × X)_{k'} ⟶ X_{k'} × X_{k'}` is an isomorphism. -/
instance isIso_prodFieldBaseChangeHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsIso (prodFieldBaseChangeHom (k' := k') X) :=
  ⟨⟨ofProdOfIsPullback _ _ (isPullback_fieldBaseChange_of_isPullback (isPullback_fst_snd X X)),
    toProdOfIsPullback_ofProdOfIsPullback _ _ _, ofProdOfIsPullback_toProdOfIsPullback _ _ _⟩⟩

/-- The base change of the diagonal of `X`, followed by `(X × X)_{k'} ≅ X_{k'} × X_{k'}`, is the
diagonal of `X_{k'}`. -/
theorem fieldBaseChange_map_diag_comp_prodFieldBaseChangeHom
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (fieldBaseChange k k').map (diag X) ≫ prodFieldBaseChangeHom X =
      diag ((fieldBaseChange k k').obj X) := by
  refine prod_hom_ext ?_ ?_ <;>
    simp [prodFieldBaseChangeHom, toProdOfIsPullback, ← CategoryTheory.Functor.map_comp]

/-- **The Gysin pullback of `[Δ_{X_{k'}}]` along `(X × X)_{k'} ≅ X_{k'} × X_{k'}` is the class of
the base change of the diagonal of `X`**, for `X` equidimensional of dimension `d`: the Gysin map
of the flat morphism carries the class of the diagonal to that of its inverse image
(`Stacks.WeilCohomology.codimensionGysin_closedSubschemeClass_of_flat`), which is the closed
subscheme `Δ_{k'}`. -/
theorem codimensionGysin_diagonalClass_fieldBaseChange
    (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    codimensionGysin ((fieldBaseChange k k').obj (prod X X)).obj.hom
        (prod ((fieldBaseChange k k').obj X) ((fieldBaseChange k k').obj X)).obj.hom
        (w (prodFieldBaseChangeHom X)) d
        (diagonalClass ((fieldBaseChange k k').obj X) d) =
      closedSubschemeClass ((fieldBaseChange k k').obj (prod X X)).obj.hom
        ((fieldBaseChange k k').map (diag X)).hom.left d := by
  set X' := (fieldBaseChange k k').obj X
  set φ := prodFieldBaseChangeHom (k' := k') X
  have hX' := isNonemptyEquidimensional_fieldBaseChange (k' := k') X hX
  have hP' : RelativeDimension ((fieldBaseChange k k').obj (prod X X)).obj.hom (d + d) :=
    isEquidim_fieldBaseChange _ (isNonemptyEquidimensional_prod hX hX).relativeDimension
  have : IsIso ((toScheme k').map φ) := Functor.map_isIso (toScheme k') φ
  have key : ∀ (q : X'.obj.left ⟶ (fieldChowSituation k').S) [LocallyOfFiniteType q],
      q = X'.obj.hom →
        schemeDeltaDimension (fieldChowSituation k') q ≤ ((((d + d : ℕ) : ℤ) - d : ℤ) : EInt) := by
    intro q _ hq
    subst hq
    rw [show (((d + d : ℕ) : ℤ) - d : ℤ) = d by push_cast; ring]
    exact Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _ hX'.relativeDimension
  rw [diagonalClass, codimensionGysin_closedSubschemeClass_of_flat _ _ (w φ) hP'
    (isNonemptyEquidimensional_prod hX' hX').relativeDimension
    (relativeDimension_of_isOpenImmersion ((toScheme k').map φ)) (zero_add _) (diag X').hom.left d
    (key _ (w (diag X')))]
  -- the inverse image of the diagonal is the base change of the diagonal of `X`
  have hcomp : pullback.snd ((toScheme k').map φ) (diag X').hom.left ≫
      ((fieldBaseChange k k').map (diag X)).hom.left =
        pullback.fst ((toScheme k').map φ) (diag X').hom.left := by
    rw [← cancel_mono ((toScheme k').map φ), Category.assoc]
    have h1 : ((fieldBaseChange k k').map (diag X)).hom.left ≫ (toScheme k').map φ =
        (diag X').hom.left := congrArg (fun f => f.hom.left)
      (fieldBaseChange_map_diag_comp_prodFieldBaseChangeHom (k' := k') X)
    rw [h1, pullback.condition]
  have : IsIso (pullback.snd ((toScheme k').map φ) (diag X').hom.left) := inferInstance
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    @cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k') _ _ _ _ _
      (pullback.fst ((toScheme k').map φ) (diag X').hom.left) inferInstance
      ((fieldBaseChange k k').map (diag X)).hom.left inferInstance
      (asIso (pullback.snd ((toScheme k').map φ) (diag X').hom.left)) hcomp]

namespace FieldBaseChangeData

variable (B : FieldBaseChangeData 𝔇 𝔇') (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)
  (hA1' : 𝔇'.CoproductAxiom) (hA3' : 𝔇'.ProjectiveBundleAxiom)
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  {ch' : ∀ X : (SmoothProjectiveScheme k').FullSubcategory,
    VectorBundleKZero ((toScheme k').obj X) → ∀ n : ℕ, tateTwist F' 𝔇'.tate (𝔇'.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (h' : 𝔇'.IsCohomologicalChernCharacter ch')

include hA1 hA3 hA1' hA3' in
/-- **The class of the diagonal is compatible with base change** (the interruption of the proof of
Lemma 0FVT): for `X` nonempty equidimensional of dimension `d`, the comparison isomorphisms carry
`γ([Δ_X]) ∈ H^{2d}(X × X)(d)` to the pullback of `γ'([Δ_{X_{k'}}])` along
`(X × X)_{k'} ≅ X_{k'} × X_{k'}`, `γ`, `γ'` the cycle class maps of Lemma 0FIF. -/
theorem pullTw_codimensionCycleClass_diagonalClass (X : (SmoothProjectiveScheme k).FullSubcategory)
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    𝔇'.pullTw (prodFieldBaseChangeHom X) d
        (h'.codimensionCycleClass (prod ((fieldBaseChange k k').obj X)
          ((fieldBaseChange k k').obj X)) d (diagonalClass ((fieldBaseChange k k').obj X) d)) =
      B.twistHom (prod X X) d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) := by
  rw [B.twistHom_cycleClass hA1 hA3 hA1' hA3' h h', ← h'.codimensionCycleClass_codimensionGysin,
    codimensionGysin_diagonalClass_fieldBaseChange X hX, diagonalClass,
    chowCodimBaseChange_closedSubschemeClass (diag X) d
      (isNonemptyEquidimensional_prod hX hX).relativeDimension hX.relativeDimension
      (by push_cast; ring)]

include hA1 hA3 hA1' hA3' in
/-- **The normalisation of (A6) for `X_{k'}`, read on `(X × X)_{k'}`**: for `λ'` on
`(H')^{2d}(X_{k'})(d)`, `(id ⊗ λ')γ'([Δ_{X_{k'}}])` is the contraction, on the fibre product
`(X × X)_{k'}` of `X_{k'}` with itself, of the image of `γ([Δ_X])`. -/
theorem traceContract_fieldBaseChange (hA5' : 𝔇'.KunnethAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (l' : tateTwist F' 𝔇'.tate (𝔇'.grade ((fieldBaseChange k k').obj X) (2 * (d : ℤ))) (d : ℤ)
      →ₗ[F'] F') :
    𝔇'.traceContract hA5' ((fieldBaseChange k k').obj X) d l'
        (h'.codimensionCycleClass (prod ((fieldBaseChange k k').obj X)
          ((fieldBaseChange k k').obj X)) d (diagonalClass ((fieldBaseChange k k').obj X) d)) =
      traceContractOfIsPullback hA5' ((fieldBaseChange k k').map (fst X X))
        ((fieldBaseChange k k').map (snd X X))
        (isPullback_fieldBaseChange_of_isPullback (isPullback_fst_snd X X)) d l'
        (B.twistHom (prod X X) d (h.codimensionCycleClass (prod X X) d (diagonalClass X d))) := by
  rw [traceContract_eq_traceContractOfIsPullback,
    ← B.pullTw_codimensionCycleClass_diagonalClass hA1 hA3 hA1' hA3' h h' X hX,
    traceContractOfIsPullback_pullTw _ _ _ _ _ _ _ _ (prodFieldBaseChangeHom X)
      (prodLift_fst _ _) (prodLift_snd _ _)]

end FieldBaseChangeData

/-- **The axiom (A6) descends along the field extension** (Lemma 0FVT, paragraph (A6)), for the
cycle class maps `γ`, `γ'` of Lemma 0FIF of cohomological Chern characters `h`, `h'` of the two
data: the class of the diagonal is compatible with the comparison isomorphisms
(`Stacks.WeilDeRham.FieldBaseChangeData.traceContract_fieldBaseChange`), and a normalised form for
`X_{k'}` gives one for `X` (`Stacks.WeilDeRham.exists_isDiagonalNormalized_of_fieldBaseChange`). -/
theorem traceAxiom_of_fieldBaseChange (B : FieldBaseChangeData 𝔇 𝔇')
    (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA1' : 𝔇'.CoproductAxiom)
    (hA3' : 𝔇'.ProjectiveBundleAxiom)
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    {ch' : ∀ X : (SmoothProjectiveScheme k').FullSubcategory,
      VectorBundleKZero ((toScheme k').obj X) → ∀ n : ℕ, tateTwist F' 𝔇'.tate (𝔇'.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) (h' : 𝔇'.IsCohomologicalChernCharacter ch')
    (hA5 : 𝔇.KunnethAxiom) (hA5' : 𝔇'.KunnethAxiom)
    (hA6' : 𝔇'.TraceAxiomFor hA5' h'.codimensionCycleClass) :
    𝔇.TraceAxiomFor hA5 h.codimensionCycleClass := by
  intro X d hX
  obtain ⟨l', hl'⟩ := hA6' _ d (isNonemptyEquidimensional_fieldBaseChange X hX)
  rw [B.traceContract_fieldBaseChange hA1 hA3 hA1' hA3' h h' hA5' X hX] at hl'
  have hg : 𝔇.κ (prod X X) d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) ∈
      𝔇.grade (prod X X) (2 * (d : ℤ)) :=
    (𝔇.mem_range_tateTwistMap_iff _ _ _).mp (h.codimensionCycleClass_mem hA1 hA3 _ d _)
  exact exists_isDiagonalNormalized_of_fieldBaseChange B hA5 hA5' (fst X X) (snd X X)
    (isPullback_fst_snd X X) d _ hg l' hl'

end Diagonal

end Stacks.WeilDeRham

end
