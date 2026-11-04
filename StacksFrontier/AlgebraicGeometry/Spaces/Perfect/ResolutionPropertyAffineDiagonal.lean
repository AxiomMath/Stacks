module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjectionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffineMain
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# A quasi-compact quasi-separated algebraic space with the resolution property has affine diagonal

Stacks 0GV3: let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`
with the resolution property.  Then `X` has affine diagonal over `ℤ`, that is, the diagonal
`X ⟶ X ×_{Spec ℤ} X` of `X` viewed as an algebraic space over `Spec ℤ` is affine.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_viewOverIntegers_diag_of_hasResolutionProperty`:
  **Stacks 0GV3.**
* `AlgebraicGeometry.Space.isAffineHom_diag_yoneda_of_isAffineHom_diagonal`: over `Spec ℤ`, the
  presheaf represented by a scheme with affine diagonal has affine diagonal.

## Proof

This is the source's proof.  Stacks 09YB gives a scheme `Y` and a surjective integral, hence
affine, morphism `f : Y ⟶ X`.  By the affine case of Stacks 0GUU
(`AlgebraicGeometry.Space.hasResolutionProperty_source_of_isAffineHom`) the algebraic space `Y`
has the resolution property, hence so does the scheme `Y`
(`AlgebraicGeometry.Space.hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda`); it is
quasi-compact and quasi-separated, so its diagonal over `ℤ` is affine by Stacks 0F8C.

Everything is then read on the big fppf site of `Spec ℤ`, through the lower-shriek extension
`AlgebraicGeometry.Space.viewOverIntegers` of Stacks 03I5: there `f` stays surjective, affine and
universally closed.  Let `W` be an affine scheme with a morphism to `X ×_ℤ X`.  The base change
`X ×_{X ×_ℤ X} W` is a scheme `P` since the diagonal of `X` is representable.  The base change
`Y ×_{X ×_ℤ X} W` along `Y ⟶ X ⟶ X ×_ℤ X = Y ⟶ Y ×_ℤ Y ⟶ X ×_ℤ X` is affine, the two factors
being affine.  It is also `Y ×_X P`, so it maps to `P` by a surjective universally closed
morphism, and `P` is affine by Stacks 07VT
(`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`).

## Implementation notes

"Affine diagonal over `ℤ`" is `AlgebraicGeometry.Space.IsAffineHom` (Stacks 03WF) of the diagonal
of `AlgebraicGeometry.Space.viewOverIntegers`, the convention of the absolute separation
properties of Stacks 03BS in `StacksFrontier.AlgebraicGeometry.Spaces.Separated`, with the
containment `hZ` of the terminal scheme in the site.  The resolution property is the one of
Stacks 0GUS at the module universe of the schemes, the universe at which the direct and inverse
images of modules used by Stacks 0GUU are defined.

## References

* [Stacks Project, Tag 0GV3](https://stacks.math.columbia.edu/tag/0GV3)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A functor preserving the binary product `T ⨯ T` sends the diagonal of `T` to the diagonal of
`F.obj T`, up to the comparison isomorphism. -/
private theorem map_diag_comp_preservesLimitPair_iso_hom {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (T : C) [PreservesLimit (pair T T) F] :
    F.map (diag T) ≫ (PreservesLimitPair.iso F T T).hom = diag (F.obj T) := by
  apply prod.hom_ext
  · rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd, ← Functor.map_comp]
    simp

/-- **A scheme with affine diagonal represents a presheaf with affine diagonal over `Spec ℤ`.**
The diagonal of the represented presheaf is the image under Yoneda of the diagonal in the site,
whose underlying morphism of schemes is the diagonal `T ⟶ T ×_ℤ T`. -/
theorem isAffineHom_diag_yoneda_of_isAffineHom_diagonal (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hT : _root_.AlgebraicGeometry.IsAffineHom (pullback.diagonal
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T)))) :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (yoneda.obj T)) := by
  let Z := (⊤_ Scheme.{u})
  let q := BigFppfOver.toScheme B Z hZ
  let : HasPullbacks (BigFppfOver B Z hZ) := inferInstance
  let : HasTerminal (BigFppfOver B Z hZ) :=
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hZ)))).hasTerminal
  let : HasBinaryProducts (BigFppfOver B Z hZ) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hqTerminal : q.obj (⊤_ (BigFppfOver B Z hZ)) ≅ ⊤_ Scheme := by
    let Tz : BigFppfOver B Z hZ := Over.mk (𝟙 (B.obj hZ))
    let hTz : IsTerminal Tz := (Over.mkIdTerminal : IsTerminal Tz)
    let e := hTz.uniqueUpToIso
      (terminalIsTerminal : IsTerminal (⊤_ (BigFppfOver B Z hZ)))
    simpa [q, BigFppfOver.toScheme, BigFppfOver.forget,
      Tz, BigFppfSite.obj] using (q.mapIso e).symm
  let : PreservesLimit (Functor.empty _) q := preservesTerminal_of_iso q hqTerminal
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) q :=
    preservesLimitsOfShape_pempty_of_preservesTerminal q
  let : PreservesLimitsOfShape WalkingCospan q := by
    apply comp_preservesLimitsOfShape
  have hSchemeDiag : _root_.AlgebraicGeometry.IsAffineHom (diag (q.obj T)) := by
    have heq : diag (q.obj T) ≫ (prodIsoPullback (q.obj T) (q.obj T)).hom =
        pullback.diagonal (terminal.from (q.obj T)) := by
      apply pullback.hom_ext <;> simp
    rw [(Iso.eq_comp_inv _).2 heq]
    infer_instance
  let : PreservesLimitsOfShape (Discrete WalkingPair) q :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks q
  have hDiag : _root_.AlgebraicGeometry.IsAffineHom (q.map (diag T)) := by
    have heq := map_diag_comp_preservesLimitPair_iso_hom q T
    rw [(Iso.eq_comp_inv _).2 heq]
    infer_instance
  have heq := map_diag_comp_preservesLimitPair_iso_hom yoneda T
  rw [← heq]
  exact isAffineHom_comp_iso _ (isAffineHom_yoneda_map_of_isAffineHom (diag T) hDiag)

/-- **Stacks 0GV3.**  Let `X` be a quasi-compact and quasi-separated algebraic space over a
scheme `S` with the resolution property.  Then `X` has affine diagonal over `ℤ`: the diagonal of
`X` viewed as an algebraic space over `Spec ℤ` is an affine morphism. -/
@[stacks 0GV3]
theorem isAffineHom_viewOverIntegers_diag_of_hasResolutionProperty
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hXres : HasResolutionProperty.{u, u} B S hS X hX) :
    IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X)) := by
  -- A scheme `Y` with a surjective integral morphism to `X` (Stacks 09YB).
  obtain ⟨Y, f, hfsurj, hfint⟩ :=
    (existsIntegralSurjectiveSchemeCover_and_refining B S hS hZ X hX hXqc hXqs).1
  have hfaff : IsAffineHom B S hS f := isAffineHom_of_isIntegralHom f hfint
  -- `Y` has the resolution property (Stacks 0GUU), hence affine diagonal (Stacks 0F8C).
  have hYalg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨yoneda.obj Y, hYalg⟩
  have hYres := hasResolutionProperty_source_of_isAffineHom hZ
    (ObjectProperty.homMk f : Ys ⟶ Xs) hfaff hXqc hXqs hXres
  have hYres' := hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda B S hS Y hYres
  obtain ⟨hYc, hYqs⟩ :=
    compactSpace_and_quasiSeparatedSpace_of_isIntegralHom B S hS hZ Y f hX hXqc hXqs hfint
  have hYdiag := HasResolutionProperty.isAffineHom_diagonal ((BigFppfOver.toScheme B S hS).obj Y)
  -- Pass to the big fppf site of `Spec ℤ`.
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let Λ := OverShriek.relocalizePresheafFunctor k
  let X' := viewOverIntegers B S hS hZ X
  have hX' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X' :=
    isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) k X hX
  let Y'' := Λ.obj (yoneda.obj Y)
  have hY'' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y'' :=
    isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) k _ hYalg
  let f' : Y'' ⟶ X' := Λ.map f
  have hf'aff : IsAffineHom B (⊤_ Scheme.{u}) hZ f' := isAffineHom_relocalize B S hS hZ k hfaff
  have hf'surj : IsSurjective B (⊤_ Scheme.{u}) hZ f' :=
    isSurjective_relocalize B S hS (⊤_ Scheme.{u}) hZ k f hfsurj
  have hf'uc : UniversallyClosed B (⊤_ Scheme.{u}) hZ f' :=
    (universallyClosed_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ k hYalg hX f).2
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hYalg hX f).1 hfint).2
  -- The diagonal of `Y` over `Spec ℤ` is affine.
  let Y' : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map k).obj Y
  let e : Y'' ≅ yoneda.obj Y' := (OverShriek.relocalizeYonedaIso k).app Y
  have hY'diag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (yoneda.obj Y')) :=
    isAffineHom_diag_yoneda_of_isAffineHom_diagonal hZ Y' hYdiag
  have hY''diag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag Y'') := by
    have h : diag Y'' = e.hom ≫ diag (yoneda.obj Y') ≫ prod.map e.inv e.inv := by
      apply prod.hom_ext <;> simp
    rw [h]
    exact isAffineHom_iso_comp e.hom (isAffineHom_comp_iso (prod.map e.inv e.inv) hY'diag)
  -- The product `f' × f'` is affine, hence so is `Y ⟶ X ⟶ X × X`.
  have hprod : IsAffineHom B (⊤_ Scheme.{u}) hZ (prod.map f' f') := by
    have h1 : IsAffineHom B (⊤_ Scheme.{u}) hZ (prod.map f' (𝟙 Y'')) :=
      isAffineHom_of_isPullback (IsPullback.of_prod_fst_with_id f' Y'') hf'aff
    have h2 : IsAffineHom B (⊤_ Scheme.{u}) hZ (prod.map (𝟙 X') f') := by
      have h : prod.map (𝟙 X') f' =
          (prod.braiding X' Y'').hom ≫ prod.map f' (𝟙 X') ≫ (prod.braiding X' X').hom := by
        apply prod.hom_ext <;> simp
      rw [h]
      exact isAffineHom_iso_comp _ (isAffineHom_comp_iso _
        (isAffineHom_of_isPullback (IsPullback.of_prod_fst_with_id f' X') hf'aff))
    have h : prod.map f' f' = prod.map f' (𝟙 Y'') ≫ prod.map (𝟙 X') f' := by
      apply prod.hom_ext <;> simp
    rw [h]
    exact isAffineHom_comp B (⊤_ Scheme.{u}) hZ _ _ h1 h2
  have hcomp : IsAffineHom B (⊤_ Scheme.{u}) hZ (f' ≫ diag X') := by
    have h : f' ≫ diag X' = diag Y'' ≫ prod.map f' f' := by
      apply prod.hom_ext <;> simp
    rw [h]
    exact isAffineHom_comp B (⊤_ Scheme.{u}) hZ _ _ hY''diag hprod
  -- The base change of the diagonal of `X` to an affine scheme `W`.
  intro W g
  have hrep := hX'.diagonal_representable
  let P₀ := hrep.pullback g
  have hP := hrep.isPullback g
  have hQ : IsPullback (pullback.snd (hrep.fst g) f')
      (pullback.fst (hrep.fst g) f' ≫ yoneda.map (hrep.snd g)) (f' ≫ diag X') g :=
    (IsPullback.of_hasPullback (hrep.fst g) f').flip.paste_vert hP
  obtain ⟨W', p', q', hpq⟩ := hcomp W g
  let eQ : pullback (hrep.fst g) f' ≅ yoneda.obj ((BigAffineFppf.inclusion _ _ _).obj W') :=
    hQ.isoIsPullback _ _ hpq
  have hQaff : IsAffineSpace B (⊤_ Scheme.{u}) hZ (pullback (hrep.fst g) f') :=
    ⟨_, W'.property, ⟨eQ⟩⟩
  have hQalg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (pullback (hrep.fst g) f') :=
    isAlgebraicSpace_of_iso B (⊤_ Scheme.{u}) hZ eQ.symm
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _)
  have hP₀alg := AlgebraicGeometry.isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ P₀
  have hsurj : IsSurjective B (⊤_ Scheme.{u}) hZ (pullback.fst (hrep.fst g) f') :=
    isSurjective_pullback_fst B (⊤_ Scheme.{u}) hZ hP₀alg hX' hY'' _ _ hf'surj
  have huc : UniversallyClosed B (⊤_ Scheme.{u}) hZ (pullback.fst (hrep.fst g) f') :=
    fun Z _ w => isClosedMap_pointsMap_pullback_fst_pullback_fst B (⊤_ Scheme.{u}) hZ f'
      (hrep.fst g) w (hf'uc Z ‹_› (w ≫ hrep.fst g))
  obtain ⟨T, hT, ⟨eT⟩⟩ := isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace
    B (⊤_ Scheme.{u}) hZ (pullback.fst (hrep.fst g) f') hQalg hP₀alg hsurj huc hQaff
  have hP₀aff : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj P₀) := by
    let e₀ : P₀ ≅ T := Yoneda.fullyFaithful.preimageIso eT
    have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T) := hT
    exact IsAffine.of_isIso ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map e₀.hom)
  exact ⟨⟨P₀, hP₀aff⟩, hrep.fst g, hrep.snd g, hP⟩

end AlgebraicGeometry.Space

end
