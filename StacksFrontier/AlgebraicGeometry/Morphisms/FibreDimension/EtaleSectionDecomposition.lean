module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalDecomposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The clopen decomposition of an étale scheme along a section, and the drop in fibre degree

Let `f : X ⟶ Y` be a separated étale morphism of schemes and let `s : Y ⟶ X` be a section of
`f`. Then `X` decomposes into the range of `s`, which is open and closed, and its complement,
and the fibre degrees of the complement over `Y` are bounded by one less than a bound for the
fibre degrees of `f`.

This is the mechanism of the inductive step of the second proof of Stacks 04DZ, where a scheme
étale over an affine scheme is dominated by one admitting a section, and the section is split off
to drop the bound on the fibre degrees by one.

## The shape of the argument

Both statements are read off the corresponding statements for the relative diagonal, which
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalDecomposition` proves,
because the pair (`f`, `s`) is the base change along `s` of the pair
(`X ×_Y X ⟶ X`, `AlgebraicGeometry.pullback.diagonal`): the *graph* of the section,
`AlgebraicGeometry.sectionGraph`, exhibits `X` as the fibre product of the first projection
`X ×_Y X ⟶ X` with `s`, and under it the range of `s` is the preimage of the range of the
diagonal. So the range of `s` is open and closed because the range of the diagonal is
(`AlgebraicGeometry.isClopen_range_diagonal`), and the degree drop is the degree drop for the
off-diagonal part (`AlgebraicGeometry.boundsFiberDegrees_offDiagonal_fst`) transported along
that fibre square by the stability of a bound on the fibre degrees under base change,
Stacks 03J7.

## Main definitions

* `AlgebraicGeometry.sectionGraph`: the graph of a section `s` of `f`, as a morphism
  `X ⟶ X ×_Y X`. **This is a new definition.**
* `AlgebraicGeometry.offSection`: the open subscheme of `X` whose points are those not in the
  range of the section. **This is a new definition.**

## Main results

* `AlgebraicGeometry.isPullback_sectionGraph`: the graph of a section exhibits `f` as the base
  change of the first projection `X ×_Y X ⟶ X` along the section.
* `AlgebraicGeometry.isClopen_range_section`: the range of a section of a separated étale
  morphism is open and closed.
* `AlgebraicGeometry.isCompl_opensRange_offSection`: the range of the section and the
  off-section part are complementary open subschemes of `X`.
* `AlgebraicGeometry.isAffine_offSection`: the off-section part is affine when `X` is.
* `AlgebraicGeometry.boundsFiberDegrees_offSection`: **the degree drop.** If `n + 1` bounds the
  degrees of the fibres of a separated étale `f` admitting a section, then `n` bounds the degrees
  of the fibres of the off-section part over `Y`.

## Implementation notes

Nothing here carries a tag: splitting off a section and dropping the bound is one sentence of the
second proof of Stacks 04DZ, not a statement of a tag of its own.

`AlgebraicGeometry.offSection` is defined as the preimage of
`AlgebraicGeometry.offDiagonal` along the graph rather than directly as the complement of the
range of the section, so that the fibre square which carries the degree drop is the restriction
square of the graph over an open subscheme,
`AlgebraicGeometry.isPullback_morphismRestrict`, pasted onto the fibre square of the graph.
That the two descriptions agree is
`AlgebraicGeometry.coe_offSection`.

`AlgebraicGeometry.isCompl_opensRange_offSection` asks for the section to be an open immersion as
a hypothesis, which it always is
(`AlgebraicGeometry.isOpenImmersion_of_section_of_etale`), so that this file does not have to
import the étale descent machinery which proves that.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)

/-! ### The graph of a section -/

/-- **The graph of a section.** For a section `s` of `f : X ⟶ Y` this is the morphism
`X ⟶ X ×_Y X` whose first component is `f ≫ s` and whose second component is the identity. It
exhibits `f` as the base change of the first projection of `X ×_Y X` along `s`. -/
def sectionGraph (hs : s ≫ f = 𝟙 Y) : X ⟶ pullback f f :=
  pullback.lift (f ≫ s) (𝟙 X) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- The first component of the graph `sectionGraph f s hs` is `f ≫ s`. -/
@[reassoc (attr := simp)]
lemma sectionGraph_fst (hs : s ≫ f = 𝟙 Y) :
    sectionGraph f s hs ≫ pullback.fst f f = f ≫ s := by
  simp only [sectionGraph]
  exact pullback.lift_fst _ _ _

/-- The second component of the graph `sectionGraph f s hs` is the identity of `X`. -/
@[reassoc (attr := simp)]
lemma sectionGraph_snd (hs : s ≫ f = 𝟙 Y) :
    sectionGraph f s hs ≫ pullback.snd f f = 𝟙 X := by
  simp only [sectionGraph]
  exact pullback.lift_snd _ _ _

/-- **A section is a base change of the diagonal's projection.** The graph of a section `s` of
`f : X ⟶ Y`, together with `f` itself, exhibits `X` as the fibre product of the first projection
`X ×_Y X ⟶ X` with `s`. -/
@[ega "IV 14.5.11.1" "special case"]
theorem isPullback_sectionGraph (hs : s ≫ f = 𝟙 Y) :
    IsPullback (sectionGraph f s hs) f (pullback.fst f f) s := by
  have hcomm : sectionGraph f s hs ≫ pullback.fst f f = f ≫ s := sectionGraph_fst f s hs
  apply IsPullback.of_isLimit (c := PullbackCone.mk (sectionGraph f s hs) f hcomm)
  refine PullbackCone.IsLimit.mk hcomm (fun c => c.fst ≫ pullback.snd f f) ?_ ?_ ?_
  · intro c
    refine pullback.hom_ext ?_ ?_
    · calc
        (c.fst ≫ pullback.snd f f) ≫ sectionGraph f s hs ≫ pullback.fst f f =
            c.fst ≫ (pullback.snd f f ≫ f) ≫ s := by
          rw [hcomm]; simp [Category.assoc]
        _ = c.fst ≫ (pullback.fst f f ≫ f) ≫ s := by rw [pullback.condition]
        _ = (c.fst ≫ pullback.fst f f) ≫ f ≫ s := by simp [Category.assoc]
        _ = (c.snd ≫ s) ≫ f ≫ s := by rw [c.condition]
        _ = c.snd ≫ (s ≫ f) ≫ s := by simp [Category.assoc]
        _ = c.snd ≫ s := by rw [hs, Category.id_comp]
        _ = c.fst ≫ pullback.fst f f := c.condition.symm
    · calc
        (c.fst ≫ pullback.snd f f) ≫ sectionGraph f s hs ≫ pullback.snd f f =
            (c.fst ≫ pullback.snd f f) ≫ 𝟙 X := by rw [sectionGraph_snd]
        _ = c.fst ≫ pullback.snd f f := Category.comp_id _
  · intro c
    calc
      (c.fst ≫ pullback.snd f f) ≫ f = c.fst ≫ pullback.snd f f ≫ f := by
        simp [Category.assoc]
      _ = c.fst ≫ pullback.fst f f ≫ f := by rw [← pullback.condition]
      _ = (c.snd ≫ s) ≫ f := by rw [← Category.assoc, c.condition]
      _ = c.snd := by rw [Category.assoc, hs, Category.comp_id]
  · intro c m h₁ h₂
    calc
      m = m ≫ 𝟙 X := (Category.comp_id m).symm
      _ = m ≫ sectionGraph f s hs ≫ pullback.snd f f := by rw [sectionGraph_snd]
      _ = c.fst ≫ pullback.snd f f := by rw [← Category.assoc, h₁]

/-- **The range of a section is where the graph meets the diagonal.** A point of `X` lies in the
range of the section `s` exactly when its image under the graph of `s` lies in the range of the
relative diagonal of `f`. -/
theorem range_section_eq_preimage_range_diagonal (hs : s ≫ f = 𝟙 Y) :
    Set.range s.base =
      (sectionGraph f s hs).base ⁻¹' Set.range (pullback.diagonal f).base := by
  have hgraph : s ≫ sectionGraph f s hs = s ≫ pullback.diagonal f := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, sectionGraph_fst, pullback.diagonal_fst, Category.comp_id]
      rw [← Category.assoc, hs, Category.id_comp]
    · simp only [Category.assoc, sectionGraph_snd, pullback.diagonal_snd, Category.comp_id]
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨s.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgraph]
  · rintro ⟨x', hx'⟩
    have key : ∀ g : pullback f f ⟶ X,
        (pullback.diagonal f ≫ g).base x' = (sectionGraph f s hs ≫ g).base x := fun g => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx']
    have hx : x' = x := by simpa using key (pullback.snd f f)
    exact ⟨f.base x, by simpa [hx] using (key (pullback.fst f f)).symm⟩

/-- **The range of a section of a separated étale morphism is open and closed.** It is the
preimage under the graph of the section of the range of the relative diagonal, which is open and
closed by `AlgebraicGeometry.isClopen_range_diagonal`. -/
theorem isClopen_range_section [Etale f] [IsSeparated f] (hs : s ≫ f = 𝟙 Y) :
    IsClopen (Set.range s.base) := by
  rw [range_section_eq_preimage_range_diagonal f s hs]
  exact (isClopen_range_diagonal f).preimage (sectionGraph f s hs).base.hom.continuous

/-! ### The off-section part of `X` -/

/-- **The off-section part of `X`.** For a separated morphism `f : X ⟶ Y` with a section `s` this
is the open subscheme of `X` whose points are those outside the range of `s`, presented as the
preimage of `AlgebraicGeometry.offDiagonal` along the graph of `s`. -/
def offSection [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : X.Opens :=
  sectionGraph f s hs ⁻¹ᵁ offDiagonal f

/-- The points of `AlgebraicGeometry.offSection` are exactly those outside the range of the
section. -/
theorem coe_offSection [IsSeparated f] (hs : s ≫ f = 𝟙 Y) :
    (offSection f s hs : Set X) = (Set.range s.base)ᶜ := by
  show (sectionGraph f s hs).base ⁻¹' (offDiagonal f : Set (pullback f f : Scheme.{u})) = _
  rw [coe_offDiagonal, Set.preimage_compl, range_section_eq_preimage_range_diagonal f s hs]

/-- For a separated étale morphism the off-section part is closed as well as open, being the
complement of the open range of the section. -/
theorem isClosed_offSection [Etale f] [IsSeparated f] (hs : s ≫ f = 𝟙 Y) :
    IsClosed (offSection f s hs : Set X) := by
  rw [coe_offSection, isClosed_compl_iff]
  exact (isClopen_range_section f s hs).isOpen

/-- **`X` is the disjoint union of the range of the section and the off-section part.** -/
theorem isCompl_opensRange_offSection [IsSeparated f] [IsOpenImmersion s] (hs : s ≫ f = 𝟙 Y) :
    IsCompl s.opensRange (offSection f s hs) := by
  have hcoe : (offSection f s hs : Set X) = (Set.range s.base)ᶜ := coe_offSection f s hs
  constructor
  · refine disjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hmem : x ∈ (s.opensRange ⊓ offSection f s hs : X.Opens) := hx
    have h₂ : x ∈ (Set.range s.base)ᶜ := hcoe ▸ hmem.2
    exact h₂ hmem.1
  · refine codisjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    show x ∈ (s.opensRange ⊔ offSection f s hs : X.Opens)
    by_cases h : x ∈ Set.range s.base
    · exact Or.inl h
    · exact Or.inr (by rw [show ((offSection f s hs : X.Opens) : Set X) = _ from hcoe]; exact h)

/-- The off-section part of `X` is affine when `X` is: it is a closed subscheme of the affine
scheme `X`, being an open subscheme whose point set is closed, and a closed immersion is
affine. -/
theorem isAffine_offSection [Etale f] [IsSeparated f] [IsAffine X] (hs : s ≫ f = 𝟙 Y) :
    IsAffine (offSection f s hs).toScheme := by
  have hci : IsClosedImmersion (offSection f s hs).ι :=
    IsClosedImmersion.of_isPreimmersion (offSection f s hs).ι
      (by simpa using isClosed_offSection f s hs)
  exact isAffine_of_isAffineHom (offSection f s hs).ι

/-! ### The drop in fibre degree -/

/-- **The degree drop off a section.** If `n + 1` bounds the degrees of the fibres of a separated
étale morphism `f : X ⟶ Y` which admits a section `s`, then `n` bounds the degrees of the fibres
of the off-section part of `X` over `Y`.

The pair (`f`, `s`) is the base change along `s` of the pair
(`X ×_Y X ⟶ X`, `pullback.diagonal f`), by
`AlgebraicGeometry.isPullback_sectionGraph`, and under that base change the off-section part is
the off-diagonal part; so this is
`AlgebraicGeometry.boundsFiberDegrees_offDiagonal_fst` carried along the fibre square by
Stacks 03J7. -/
theorem boundsFiberDegrees_offSection [Etale f] [IsSeparated f] (hs : s ≫ f = 𝟙 Y) (n : ℕ)
    (h : BoundsFiberDegrees f ((n + 1 : ℕ) : ℤ)) :
    BoundsFiberDegrees ((offSection f s hs).ι ≫ f) ((n : ℕ) : ℤ) := by
  have hoff : BoundsFiberDegrees ((offDiagonal f).ι ≫ pullback.fst f f) ((n : ℕ) : ℤ) :=
    boundsFiberDegrees_offDiagonal_fst f n h
  have hsq : IsPullback (sectionGraph f s hs ∣_ offDiagonal f)
      ((offSection f s hs).ι ≫ f) ((offDiagonal f).ι ≫ pullback.fst f f) s :=
    (isPullback_morphismRestrict (sectionGraph f s hs) (offDiagonal f)).paste_vert
      (isPullback_sectionGraph f s hs)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {_ _ : Scheme.{u}} (p : _ ⟶ _) ↦ BoundsFiberDegrees p ((n : ℕ) : ℤ)) hsq hoff

end AlgebraicGeometry

end

end
