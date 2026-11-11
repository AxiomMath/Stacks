module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.ShortExact
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalCompatibility
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalSplitSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of the diagonal: `0 → 𝒞_{X/X ×_S X} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S} → 0`

Let `f : X ⟶ S` be a morphism of schemes, with diagonal `Δ : X ⟶ X ×_S X`, and give `X ×_S X`
the structure morphism `pr₁ ≫ f`.  [Stacks, Tag 060N] observes that the conormal sequence of the
immersion `Δ` ([Stacks, Tag 01UZ])

```
0 → 𝒞_{X/X ×_S X} → Δ^* Ω_{X ×_S X/S} → Ω_{X/S} → 0
```

is a canonical short exact sequence ([Stacks, Tag 0474], `Δ` having the left inverse `pr₁`), that
under `Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}` ([Stacks, Tag 01V1]) its right arrow is `(1, 1)`,
and that under the identification `Ω_{X/S} = 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2], with the
convention `d b = s₂(b) - s₁(b)`, its left arrow is `(-1, 1)`.

## Main definitions

* `Stacks.DiagonalSplitSequence.relativeDifferentialsIsoConormalSheaf`: the isomorphism
  `Ω_{X/S} ≅ 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2], landing in the conormal sheaf on which the
  first arrow of the conormal sequence is defined.
* `Stacks.DiagonalSplitSequence.diagonalShortComplexIso`: **[Stacks, Tag 060N]**, an isomorphism
  from the complex `Ω_{X/S} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S}` with arrows `(-1, 1)`, `(1, 1)` to the
  conormal sequence of the diagonal.
* `Stacks.DiagonalSplitSequence.conormalShortComplexDiagonalSplitting`: a splitting of the
  conormal sequence of the diagonal.

## Main results

* `Stacks.DiagonalSplitSequence.conormalShortComplex_diagonal_shortExact`:
  **[Stacks, Tag 060N]**, the conormal sequence of the diagonal is short exact.
* `relativeDifferentialsIsoDiagonalConormal_hom_comp_conormalDifferential`:
  **[Stacks, Tag 060N]**, the isomorphism of [Stacks, Tag 08S2] followed by the first arrow
  `𝒞_{X/X ×_S X} ⟶ Δ^* Ω_{X ×_S X/S}` is `(-1, 1)`.
* `Stacks.DiagonalSplitSequence.diagonalBiprodIso_hom_comp_conormalShortComplex_g`: through
  `Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}` the second arrow is `(1, 1)`.

## Implementation notes

The first arrow `Stacks.ConormalSequenceRight.conormalDifferential` is defined on the conormal
sheaf `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`, while [Stacks, Tag 08S2] lands
in `Stacks.Conormal.conormalSheaf`; the two are matched by
`Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge`.  The sign of the left arrow is checked
on the generators `d b` of `Ω_{X/S}`: [Stacks, Tag 08S2] sends `d b` to the conormal class of
`p_2^♯ b - p_1^♯ b`, the first arrow sends that class to `Δ^* d_{X ×_S X/S}(p_2^♯ b - p_1^♯ b)`
(`Stacks.ConormalSequenceRight.conormalDifferential_canonicalConormalQuotientMap`), and the
footnote `Stacks.DiagonalSplitSequence.pullbackSection_d_diffSection` identifies this with
`(-1, 1)` applied to `d b`.  The third term of the conormal sequence is the sheaf of relative
differentials of the composite `Δ ≫ pr₁ ≫ f`, identified with `Ω_{X/S}` by `eqToHom`.

## References

* [Stacks Project, Tag 060N](https://stacks.math.columbia.edu/tag/060N)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.DiagonalSplitSequence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The conormal sequence of the diagonal -/

/-- The diagonal followed by the structure morphism `pr₁ ≫ f` of `X ×_S X` is `f`. -/
theorem diagonal_comp_fst_comp : pullback.diagonal f ≫ (pullback.fst f f ≫ f) = f := by simp

/-- `pr₁` is a left inverse of the diagonal over `S`. -/
theorem fst_comp_diagonal_comp_fst_comp :
    pullback.fst f f ≫ (pullback.diagonal f ≫ (pullback.fst f f ≫ f)) = pullback.fst f f ≫ f := by
  rw [diagonal_comp_fst_comp]

/-- Changing the target morphism of the canonical map of [Stacks, Tag 01UV] along an equality
is composition with the corresponding `eqToHom`. -/
private theorem relativeDifferentialsMap_comp_eqToHom {Z Y T : Scheme.{u}} (i : Z ⟶ Y)
    (p : Y ⟶ T) {q q' : Z ⟶ T} (hq : q = q') (h : i ≫ p = q ≫ 𝟙 T) (h' : i ≫ p = q' ≫ 𝟙 T) :
    relativeDifferentialsMap i p q (𝟙 T) h ≫
        eqToHom (congrArg Scheme.Hom.relativeDifferentials hq) =
      relativeDifferentialsMap i p q' (𝟙 T) h' := by
  subst hq
  simp

/-- Changing the target morphism of the canonical map of [Stacks, Tag 01UV] along an equality,
read on a composite. -/
private theorem comp_relativeDifferentialsMap_eq {Z Y T : Scheme.{u}} (i : Z ⟶ Y)
    (p : Y ⟶ T) {q q' : Z ⟶ T} (hq : q = q') (h : i ≫ p = q ≫ 𝟙 T) (h' : i ≫ p = q' ≫ 𝟙 T)
    {M : Z.Modules} (e : M ⟶ (Scheme.Modules.pullback i).obj (relativeDifferentials p))
    (d : M ⟶ relativeDifferentials q') (H : e ≫ relativeDifferentialsMap i p q' (𝟙 T) h' = d) :
    e ≫ relativeDifferentialsMap i p q (𝟙 T) h =
      d ≫ eqToHom (congrArg Scheme.Hom.relativeDifferentials hq).symm := by
  subst hq
  simpa using H

/-- The second arrow of the conormal sequence of `Δ`, followed by the identification
`Ω_{X/X ×_S X ≫ S} = Ω_{X/S}` coming from `Δ ≫ pr₁ ≫ f = f`, is
`Stacks.DiagonalSplitSequence.diagonalDifferentialsMap`. -/
theorem conormalShortComplex_g_comp_eqToHom :
    (Stacks.ConormalSequenceRight.conormalShortComplex (pullback.diagonal f)
        (pullback.fst f f ≫ f)).g ≫
        eqToHom (congrArg Scheme.Hom.relativeDifferentials (diagonal_comp_fst_comp f)) =
      diagonalDifferentialsMap f :=
  relativeDifferentialsMap_comp_eqToHom _ _ (diagonal_comp_fst_comp f) (by simp) _

/-- **[Stacks, Tag 060N]: under the identification of [Stacks, Tag 08S2] the left arrow is
`(-1, 1)`.**  The first arrow `𝒞_{X/X ×_S X} ⟶ Δ^* Ω_{X ×_S X/S}` of the conormal sequence of
the diagonal ([Stacks, Tag 01UZ]), precomposed with the isomorphism
`Ω_{X/S} ≅ 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2] (which sends `d b` to the class of
`p₂^♯ b - p₁^♯ b`, the convention `d = s₂ - s₁`), is the map `(-1, 1)` into
`Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}`.

Both sides are maps out of `Ω_{X/S}`, so it suffices to compare them on `d b`; the left side
gives `Δ^* d_{X ×_S X/S}(p₂^♯ b - p₁^♯ b)` and the right side is computed by the footnote
`Stacks.DiagonalSplitSequence.pullbackSection_d_diffSection`. -/
@[stacks 060N "under the identification Ω_{X/S} ≅ 𝒞_{X/X ×_S X} of Tag 08S2 (convention
d = s₂ - s₁), the first arrow 𝒞_{X/X ×_S X} ⟶ Δ^*Ω_{X ×_S X/S} of the conormal sequence of the
diagonal is (-1,1) into Ω_{X/S} ⊕ Ω_{X/S} = Δ^*Ω_{X ×_S X/S}"]
theorem relativeDifferentialsIsoDiagonalConormal_hom_comp_conormalDifferential :
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f).hom ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge (pullback.diagonal f)).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential (pullback.diagonal f)
            (pullback.fst f f ≫ f) =
      leftArrow f := by
  refine Stacks.ConormalSequenceRight.relativeDifferentials_hom_ext f _ _ fun U b => ?_
  rw [← pullbackSection_d_diffSection]
  obtain ⟨y, hy⟩ := (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff
    (pullback.diagonal f) (Stacks.Diagonal.prodOpen f U) (Stacks.Diagonal.diffSection f U b)).2
    (Stacks.Diagonal.app_diffSection f U b)
  have hV := Stacks.Diagonal.le_diagonal_preimage_prodOpen f U
  let B := (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge (pullback.diagonal f)).inv ≫
    Stacks.ConormalSequenceRight.conormalDifferential (pullback.diagonal f) (pullback.fst f f ≫ f)
  have h1 := Stacks.Thickenings.relativeDifferentialsIsoDiagonalConormal_hom_d (q := f) U b
  rw [Stacks.Conormal.conormalClass_eq_canonicalConormalQuotientMap _ _ hV _ _ y hy] at h1
  have h2 := Stacks.ConormalSequenceRight.conormalDifferential_canonicalConormalQuotientMap
    (pullback.diagonal f) (pullback.fst f f ≫ f) (Stacks.Diagonal.prodOpen f U) y
  have hy' : Stacks.Conormal.idealSection (pullback.diagonal f) (Stacks.Diagonal.prodOpen f U) y =
      Stacks.Diagonal.diffSection f U b := hy
  rw [hy'] at h2
  have hnat := ConcreteCategory.congr_hom (B.val.naturality (homOfLE hV).op)
    ((Stacks.Immersion.canonicalConormalQuotientMap (pullback.diagonal f)).val.app
      (op (Stacks.Diagonal.prodOpen f U)) y)
  refine Eq.trans (congrArg (B.val.app (op U)).hom h1) ?_
  refine hnat.trans ?_
  exact congrArg (fun z => (ConcreteCategory.hom
    (((Scheme.Modules.pullback (pullback.diagonal f)).obj
      (relativeDifferentials (pullback.fst f f ≫ f))).val.map (homOfLE hV).op)) z) h2


/-- **[Stacks, Tag 060N]: the canonical short exact sequence.**  The conormal sequence
`0 → 𝒞_{X/X ×_S X} → Δ^* Ω_{X ×_S X/S} → Ω_{X/S} → 0` of the diagonal
([Stacks, Tag 01UZ], with structure morphism `pr₁ ≫ f` of `X ×_S X` over `S`) is short exact: the
diagonal is an immersion with the left inverse `pr₁` over `S`, so [Stacks, Tag 0474] applies.
Through `Stacks.DiagonalSplitSequence.diagonalBiprodIso` the middle term is
`Ω_{X/S} ⊕ Ω_{X/S}`; the arrows are identified by
`Stacks.DiagonalSplitSequence.diagonalShortComplexIso`. -/
@[stacks 060N "the canonical short exact sequence 0 → 𝒞_{X/X ×_S X} → Δ^*Ω_{X ×_S X/S} →
Ω_{X/S} → 0: the conormal sequence of the diagonal (Tag 01UZ) is short exact, by Tag 0474 for
the left inverse pr₁ of Δ"]
theorem conormalShortComplex_diagonal_shortExact :
    (Stacks.ConormalSequenceRight.conormalShortComplex (pullback.diagonal f)
      (pullback.fst f f ≫ f)).ShortExact :=
  Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_retraction
    (pullback.diagonal f) (pullback.fst f f ≫ f) (pullback.fst f f) (pullback.diagonal_fst f)
    (fst_comp_diagonal_comp_fst_comp f)

/-- The canonical short exact sequence of the diagonal is split. -/
noncomputable def conormalShortComplexDiagonalSplitting :
    (Stacks.ConormalSequenceRight.conormalShortComplex (pullback.diagonal f)
      (pullback.fst f f ≫ f)).Splitting :=
  Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction
    (pullback.diagonal f) (pullback.fst f f ≫ f) (pullback.fst f f) (pullback.diagonal_fst f)
    (fst_comp_diagonal_comp_fst_comp f)

/-- The identification `Ω_{X/S} ≅ 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2], landing in the
conormal sheaf through which the first arrow of the conormal sequence is defined. -/
noncomputable def relativeDifferentialsIsoConormalSheaf :
    relativeDifferentials f ≅
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (pullback.diagonal f) :
        X.Modules) :=
  Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f ≪≫
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge (pullback.diagonal f)).symm

/-- The first arrow of the conormal sequence of the diagonal, precomposed with
`Stacks.DiagonalSplitSequence.relativeDifferentialsIsoConormalSheaf`, is `(-1, 1)`. -/
theorem relativeDifferentialsIsoConormalSheaf_hom_comp_conormalDifferential :
    (relativeDifferentialsIsoConormalSheaf f).hom ≫
        Stacks.ConormalSequenceRight.conormalDifferential (pullback.diagonal f)
          (pullback.fst f f ≫ f) =
      leftArrow f := by
  exact relativeDifferentialsIsoDiagonalConormal_hom_comp_conormalDifferential f

/-- The second arrow of the conormal sequence of the diagonal, through
`Stacks.DiagonalSplitSequence.diagonalBiprodIso`, is `(1, 1)`. -/
theorem diagonalBiprodIso_hom_comp_conormalShortComplex_g :
    (diagonalBiprodIso f).hom ≫
        (Stacks.ConormalSequenceRight.conormalShortComplex (pullback.diagonal f)
          (pullback.fst f f ≫ f)).g =
      biprod.desc (𝟙 (relativeDifferentials f)) (𝟙 (relativeDifferentials f)) ≫
        eqToHom (congrArg Scheme.Hom.relativeDifferentials (diagonal_comp_fst_comp f)).symm := by
  exact comp_relativeDifferentialsMap_eq _ _ (diagonal_comp_fst_comp f) (by simp) _ _ _
    (diagonalBiprodIso_hom_comp_diagonalDifferentialsMap f)

/-- **[Stacks, Tag 060N]: the canonical sequence, with its arrows identified.**  An
isomorphism from the three-term complex
`Ω_{X/S} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S}` with arrows `(-1, 1)` and `(1, 1)`
(`Stacks.DiagonalSplitSequence.shortComplex`) to the conormal sequence
`𝒞_{X/X ×_S X} → Δ^* Ω_{X ×_S X/S} → Ω_{X/S}` of the diagonal.  Its components are the
isomorphism `Ω_{X/S} ≅ 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2] (`d = s₂ - s₁`), the
identification `Ω_{X/S} ⊕ Ω_{X/S} ≅ Δ^* Ω_{X ×_S X/S}` coming from [Stacks, Tag 01V1], and the
identity of `Ω_{X/S}` (read through `Δ ≫ pr₁ ≫ f = f`).  Commutativity of the two squares says
that the left arrow is `(-1, 1)` and the right arrow is `(1, 1)`. -/
@[stacks 060N "the canonical sequence 0 → 𝒞_{X/X ×_S X} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S} → 0,
identified: an isomorphism of short complexes from Ω → Ω ⊕ Ω → Ω with arrows (-1,1), (1,1) to
the conormal sequence of the diagonal, through Tag 08S2 on the left and Tag 01V1 in the
middle"]
noncomputable def diagonalShortComplexIso :
    shortComplex f ≅ Stacks.ConormalSequenceRight.conormalShortComplex (pullback.diagonal f)
      (pullback.fst f f ≫ f) :=
  ShortComplex.isoMk (relativeDifferentialsIsoConormalSheaf f) (diagonalBiprodIso f)
    (eqToIso (congrArg Scheme.Hom.relativeDifferentials (diagonal_comp_fst_comp f)).symm)
    (by exact relativeDifferentialsIsoConormalSheaf_hom_comp_conormalDifferential f)
    (by exact diagonalBiprodIso_hom_comp_conormalShortComplex_g f)

end Stacks.DiagonalSplitSequence

end
