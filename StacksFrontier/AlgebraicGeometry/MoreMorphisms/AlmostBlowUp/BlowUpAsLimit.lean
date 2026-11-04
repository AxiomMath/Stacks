module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeLimitQcqs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter

/-!
# The blowup of an almost blowup square is the limit of the finite-presentation subschemes

Consider an almost blowup square with centre `Z = I.subscheme`, modification `b : X' ⟶ X` and
exceptional subscheme `E = (I.comap b).subscheme`, and assume the base `X` is quasi-compact and
quasi-separated. The blowup `X''` of `X` in `Z` is then the limit
`X'' = lim X'ᵢ` of the inverse system of the closed subschemes `X'ᵢ ⊆ X'` which are of finite
presentation over `X'` and satisfy the equivalent conditions of Tag 0EV8.

## Main definitions

* `AlgebraicGeometry.almostBlowUpIdeal`: the ideal sheaf of sections of `𝒪_{X'}` supported on
  the exceptional subscheme; for an almost blowup square it cuts out the blowup of `X` in the
  centre, viewed as a closed subscheme of `X'`.
* `AlgebraicGeometry.blowUpOverHom`: an identification of the blowup with that closed subscheme,
  as a morphism of `X'`-schemes.
* `AlgebraicGeometry.blowUpCone`: the cone with vertex the blowup on the inverse system of those
  finite-presentation closed subschemes.

## Main results

* `AlgebraicGeometry.le_almostBlowUpIdeal_iff`: the condition indexing the system is the
  condition of Tag 0EV8.
* `AlgebraicGeometry.isLimitBlowUpCone` and
  `AlgebraicGeometry.exists_isLimit_blowUpCone`: the cone is a limit cone.
* `AlgebraicGeometry.isFiltered_and_exists_isLimit_blowUpCone`: the system is directed and the
  blowup is its limit, over `X'` and in schemes.

## Implementation notes

The index of the system is `Stacks.Flatness.FinitePresentationSubscheme (almostBlowUpIdeal I b)`,
the ideal sheaves `J ≤ almostBlowUpIdeal I b` whose closed immersion is of finite presentation.
Since `almostBlowUpIdeal I b` is the ideal sheaf of `X'' ⊆ X'`, the condition `J ≤
almostBlowUpIdeal I b` says exactly that `X''` is scheme theoretically contained in the closed
subscheme cut out by `J`, which is condition (2) of Tag 0EV8;
`AlgebraicGeometry.le_almostBlowUpIdeal_iff` restates it as condition (1), that the closed
subscheme contains `X' ∖ E` scheme theoretically, i.e. that it is an isomorphism over the
complement of `E`.

## References

* [Stacks Project, Tag 0EV9](https://stacks.math.columbia.edu/tag/0EV9)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Flatness

universe u

namespace AlgebraicGeometry

variable {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)

/-- The ideal sheaf of sections of `𝒪_{X'}` supported on the exceptional subscheme of an almost
blowup square. By the definition of an almost blowup square the closed subscheme it cuts out is
the blowup of `X` in the centre of the square. -/
public noncomputable abbrev almostBlowUpIdeal : X'.IdealSheafData :=
  supportedSectionsIdeal (I.comap b).support

/-- **Stacks Project, Tag 0EV8.** A closed subscheme of the modification of an almost blowup
square contains the blowup — its ideal sheaf is contained in `almostBlowUpIdeal I b` — exactly
when it is an isomorphism over the complement of the exceptional subscheme. -/
public theorem le_almostBlowUpIdeal_iff (J : X'.IdealSheafData) :
    J ≤ almostBlowUpIdeal I b ↔
      IsIso (J.subschemeι ∣_ (⟨((I.comap b).support : Set X')ᶜ,
        (I.comap b).support.isClosed.isOpen_compl⟩ : X'.Opens)) :=
  (isIso_restrict_iff_le_supportedSectionsIdeal _ (I.comap b).support.isClosed J).symm

/-- An identification `i` of the blowup of `X` in the centre of an almost blowup square with the
closed subscheme of `X'` cut out by `almostBlowUpIdeal I b`, read as a morphism of `X'`-schemes
onto the vertex of `Stacks.Flatness.subschemeCone`. -/
public noncomputable def blowUpOverHom (i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme) :
    Over.mk (i ≫ (almostBlowUpIdeal I b).subschemeι) ⟶
      (subschemeCone (almostBlowUpIdeal I b)).pt :=
  Over.homMk i rfl

/-- The cone with vertex the blowup of `X` in the centre of an almost blowup square on the
inverse system of the finite-presentation closed subschemes of `X'` containing it, built from an
identification `i` of the blowup with the closed subscheme of `X'` cut out by
`almostBlowUpIdeal I b`. -/
public noncomputable def blowUpCone (i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme) :
    Cone (subschemeDiagram (almostBlowUpIdeal I b)) :=
  (subschemeCone (almostBlowUpIdeal I b)).extend (blowUpOverHom I b i)

/-- The vertex of `AlgebraicGeometry.blowUpCone` is the blowup, with its closed immersion into
the modification as structure morphism. -/
public theorem blowUpCone_pt (i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme) :
    (blowUpCone I b i).pt = Over.mk (i ≫ (almostBlowUpIdeal I b).subschemeι) :=
  rfl

/-- Over a quasi-compact and quasi-separated modification, the blowup of `X` in the centre of an
almost blowup square is the limit of the inverse system of the closed subschemes of `X'` of finite
presentation containing it. -/
public noncomputable def isLimitBlowUpCone [CompactSpace X'] [QuasiSeparatedSpace X']
    (i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme) [IsIso i] :
    IsLimit (blowUpCone I b i) :=
  have : IsIso ((Over.forget X').map (blowUpOverHom I b i)) := ‹IsIso i›
  have : IsIso (blowUpOverHom I b i) := isIso_of_reflects_iso _ (Over.forget X')
  IsLimit.extendIso _ (isLimitSubschemeCone (almostBlowUpIdeal I b))

/-- Consider an almost blowup square with centre `I.subscheme` and modification `b : X' ⟶ X`,
with `X` quasi-compact and quasi-separated. Then the blowup of `X` in the centre, identified by
`i` with a closed subscheme of `X'` over `X`, is the limit of the inverse system of the closed
subschemes of `X'` of finite presentation satisfying the equivalent conditions of Tag 0EV8, as
recorded by `AlgebraicGeometry.le_almostBlowUpIdeal_iff`. -/
public theorem exists_isLimit_blowUpCone [CompactSpace X] [QuasiSeparatedSpace X]
    (h : IsAlmostBlowUpSquare I b) :
    ∃ i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme, IsIso i ∧
      i ≫ (almostBlowUpIdeal I b).subschemeι ≫ b = blowUpToBase I ∧
      Nonempty (IsLimit (blowUpCone I b i)) := by
  obtain ⟨e⟩ := h.blowUp
  have : QuasiCompact b := h.finitePresentation.quasiCompact
  have : QuasiSeparated b := h.finitePresentation.quasiSeparated
  have : CompactSpace X' := (quasiCompact_iff_compactSpace b).mp inferInstance
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated b
  have hi : IsIso e.inv.left := (Over.forget X).map_isIso e.inv
  exact ⟨e.inv.left, hi, Over.w e.inv, ⟨isLimitBlowUpCone I b e.inv.left⟩⟩

/-- Consider an almost blowup square with centre `I.subscheme` and modification `b : X' ⟶ X`,
with `X` quasi-compact and quasi-separated. The closed subschemes `X'ᵢ ⊆ X'` of finite
presentation satisfying the equivalent conditions of Tag 0EV8 — their ideal sheaves `J` are
finitely presented with `J ≤ almostBlowUpIdeal I b`, that is, the blowup `X''` is scheme
theoretically contained in `X'ᵢ` (condition (2)), equivalently `X'ᵢ` contains `X' ∖ E` scheme
theoretically (condition (1), `AlgebraicGeometry.le_almostBlowUpIdeal_iff`) — form a directed
system, and the blowup `X''` of `X` in the centre, identified by `i` over `X` with the closed
subscheme of `X'` cut out by `almostBlowUpIdeal I b`, is its limit `X'' = lim X'ᵢ`, both as
schemes over `X'` and as schemes. -/
@[stacks 0EV9]
public theorem isFiltered_and_exists_isLimit_blowUpCone [CompactSpace X] [QuasiSeparatedSpace X]
    (h : IsAlmostBlowUpSquare I b) :
    IsFiltered (FinitePresentationSubscheme (almostBlowUpIdeal I b)) ∧
      ∃ i : blowUp I ⟶ (almostBlowUpIdeal I b).subscheme, IsIso i ∧
        i ≫ (almostBlowUpIdeal I b).subschemeι ≫ b = blowUpToBase I ∧
        Nonempty (IsLimit (blowUpCone I b i)) ∧
        Nonempty (IsLimit ((Over.forget X').mapCone (blowUpCone I b i))) := by
  have hF := finitePresentationSubscheme_isFiltered (almostBlowUpIdeal I b)
  have : IsConnected (FinitePresentationSubscheme (almostBlowUpIdeal I b))ᵒᵖ :=
    have := IsFiltered.isConnected (FinitePresentationSubscheme (almostBlowUpIdeal I b))
    isConnected_op
  obtain ⟨i, hi, hb, ⟨hl⟩⟩ := exists_isLimit_blowUpCone I b h
  exact ⟨hF, i, hi, hb, ⟨hl⟩, ⟨isLimitOfPreserves (Over.forget X') hl⟩⟩

end AlgebraicGeometry

end
