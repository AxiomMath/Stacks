module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Schemes with affine diagonal

For a scheme `X`, affineness of its diagonal is equivalent to affineness of the intersection of
any two affine open subschemes. It is also enough that one affine open cover have affine
nonempty finite intersections. In particular every separated scheme has affine diagonal.

## Main results

* `AlgebraicGeometry.isAffineHom_diagonal_tfae` gives the three equivalent characterizations of
  a scheme with affine diagonal.
* `AlgebraicGeometry.Scheme.IsSeparated.isSeparated_terminal_from`,
  `AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal` and
  `AlgebraicGeometry.IsClosedImmersion.instIsAffineHom` together say that the diagonal of a
  separated scheme is affine.
* `AlgebraicGeometry.quasiSeparatedSpace_of_isAffineHom_diagonal`: a scheme with affine diagonal
  is quasi-separated.

## Implementation notes

The diagonal is represented by the pullback diagonal of the structure morphism to the terminal
scheme. In the covering condition the case `p = 0` already requires every member of the cover to
be affine, so the cover is packaged as a `Scheme.AffineOpenCover` and its `(p + 1)`-fold
intersections are indexed by `Fin (p + 1)`.

For the final assertion the three cited results state respectively that the structure morphism
of a separated scheme is separated, that the diagonal of a separated morphism is a closed
immersion, and that every closed immersion is affine.

## References

* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0BDX "separated case: the structure morphism is separated"
  AlgebraicGeometry.Scheme.IsSeparated.isSeparated_terminal_from
add_to_stacks 0BDX "separated case: the diagonal is a closed immersion"
  AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal
add_to_stacks 0BDX "separated case: closed immersions are affine"
  AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_sga "3 VIB 2.9.1" "special case" AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_sga "3 XXV 4.3" "partial" AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_ega "I 4.2.3" "more general" AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_ega "II 1.2.2" AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_ega "II 1.6.2" AlgebraicGeometry.IsClosedImmersion.instIsAffineHom

/-- A scheme with an affine open cover whose pairwise intersections are affine has affine
diagonal. -/
private theorem isAffineHom_diagonal_of_affineOpenCover {X : Scheme.{u}}
    (𝒰 : Scheme.AffineOpenCover.{u} X)
    (h𝒰 : ∀ i j : 𝒰.I₀, IsAffineOpen ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange)) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  let Q : AffineTargetMorphismProperty := fun T _ _ => IsAffine T
  have : HasAffineProperty @IsAffineHom Q := by
    show HasAffineProperty @IsAffineHom (fun T _ _ _ => IsAffine T)
    exact instHasAffinePropertyIsAffineHomIsAffine
  have : Q.IsLocal := HasAffineProperty.isLocal_affineProperty (P := @IsAffineHom)
  have : ∀ i, IsAffine (𝒰.openCover.X i) := Scheme.isAffine_affineOpenCover X 𝒰
  have hLocal (i j : 𝒰.I₀) :
      Q (pullback.mapDesc (𝒰.f i) (𝒰.f j) (terminal.from X)) := by
    have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
    let g := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have hg : g.opensRange = (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange :=
      TopologicalSpace.Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left _ _)
    have : IsAffine (pullback (𝒰.f i ≫ terminal.from X) (𝒰.f j ≫ terminal.from X)) :=
      inferInstance
    show IsAffine (pullback (𝒰.f i) (𝒰.f j))
    have : IsAffine g.opensRange := by
      rw [hg]
      exact h𝒰 i j
    exact IsAffine.of_isIso g.isoOpensRange.hom
  exact (HasAffineProperty.diagonal_iff (P := @IsAffineHom) (Q := Q)).mp
    (AffineTargetMorphismProperty.diagonal_of_openCover_source (Q := Q)
      (terminal.from X) 𝒰.openCover hLocal)

/-- **Stacks Project, Tag 0BDX.** For a scheme `X`, the following are
equivalent: its diagonal is affine; intersections of two affine opens are
affine; and it admits an affine open cover all of whose nonempty finite
intersections are affine. -/
@[stacks 0BDX "equivalent conditions"]
theorem isAffineHom_diagonal_tfae (X : Scheme.{u}) : List.TFAE [
    IsAffineHom (pullback.diagonal (terminal.from X)),
    ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V),
    ∃ 𝒰 : Scheme.AffineOpenCover.{u} X,
      ∀ (p : ℕ) (i : Fin (p + 1) → 𝒰.I₀),
        IsAffineOpen (⨅ j, (𝒰.f (i j)).opensRange)] := by
  tfae_have 1 → 2 := fun h U V hU hV =>
    (isAffineHom_diagonal_iff (f := terminal.from X)).mp h
      ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
  tfae_have 2 → 3 := fun h =>
    ⟨X.affineOpenCover, fun p i =>
      InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
        (fun U hU V hV => h U V hU hV) fun j => isAffineOpen_opensRange _⟩
  tfae_have 3 → 1 := by
    rintro ⟨𝒰, h𝒰⟩
    refine isAffineHom_diagonal_of_affineOpenCover 𝒰 fun i j => ?_
    let e : Fin 2 → 𝒰.I₀ := fun k => if k.val = 0 then i else j
    have hInf : (⨅ k : Fin 2, (𝒰.f (e k)).opensRange) =
        (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange := by
      apply le_antisymm
      · simpa [e] using le_inf (iInf_le (fun k : Fin 2 => (𝒰.f (e k)).opensRange) 0)
          (iInf_le (fun k : Fin 2 => (𝒰.f (e k)).opensRange) 1)
      · refine le_iInf fun k => ?_
        fin_cases k <;> simp [e]
    simpa [hInf] using h𝒰 1 e
  tfae_finish

/-- **A scheme with affine diagonal is quasi-separated.**  An affine morphism is quasi-compact,
and quasi-separatedness of a scheme is quasi-compactness of its diagonal. -/
instance quasiSeparatedSpace_of_isAffineHom_diagonal (Z : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from Z))] : QuasiSeparatedSpace Z :=
  have : QuasiSeparated (terminal.from Z) := ⟨inferInstance⟩
  quasiSeparatedSpace_of_quasiSeparated (terminal.from Z)

end AlgebraicGeometry
