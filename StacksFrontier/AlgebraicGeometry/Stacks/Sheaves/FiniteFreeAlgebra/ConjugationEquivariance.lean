module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingGroupScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalCoverAffine

/-!
# The universal degree-`d` cover is equivariant for the conjugation action

Clause (a) of the proof of Stacks 05YQ says that two free `d`-dimensional algebra structures
differing by the conjugation action of a unit-fixing matrix have the same spectrum. Over an
affine base this is
`AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_pullback_universalCoverHom_conjugation`, read off
the algebra isomorphism; over an arbitrary base there is no such algebra, and the statement is
obtained instead by base change from a single universal case.

The universal case is the affine scheme `G ×_{Spec ℤ} X` of pairs consisting of a unit-fixing
matrix and a free `d`-dimensional structure. A pair `(g, x)` over any scheme `T` is a morphism
`T ⟶ G ×_{Spec ℤ} X`, the two points of `X` it induces are `x` and its image under the
conjugation action, and the degree-`d` covers over `T` are the base changes of the two
degree-`d` covers over `G ×_{Spec ℤ} X`. Transporting the isomorphism of those two covers along
the classifying morphism gives the statement over `T`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.pairScheme`: the affine scheme of pairs `(g, m)`, with its
  two projections `AlgebraicGeometry.FiniteFreeAlgebra.pairMatrix` and
  `AlgebraicGeometry.FiniteFreeAlgebra.pairPoint`.
* `AlgebraicGeometry.FiniteFreeAlgebra.pairUniversalMatrix`: the tautological unit-fixing matrix
  over the global sections of the scheme of pairs.
* `AlgebraicGeometry.FiniteFreeAlgebra.pairAction`: the image of the tautological point under
  the conjugation action of the tautological matrix.
* `AlgebraicGeometry.FiniteFreeAlgebra.pairClassify`: the morphism to the scheme of pairs
  classifying a unit-fixing matrix and a point over an arbitrary scheme.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.pairClassify_comp_pairPoint`,
  `AlgebraicGeometry.FiniteFreeAlgebra.map_pairUniversalMatrix` and
  `AlgebraicGeometry.FiniteFreeAlgebra.pairClassify_comp_pairAction`: the classifying morphism
  pulls the tautological point, matrix and action back to the given ones.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_pullback_universalCoverHom_of_comp_eq`: an
  isomorphism of two degree-`d` covers over a base transports along base change.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_pullback_universalCoverHom_conjugation'`:
  clause (a) of the proof of Stacks 05YQ for the universal cover over an arbitrary base.

## Implementation notes

The scheme of pairs is affine because `Spec ℤ` is terminal, so it is the fibre product of two
affine schemes over an affine one; `AlgebraicGeometry.isAffine_of_isAffineHom` supplies the
instance through the pullback of an affine morphism.

The transport along base change is the pullback calculus only: each degree-`d` cover over the
base change is the base change of the cover, by `CategoryTheory.IsPullback.of_right'`, and the
given isomorphism is read as a cartesian square over the identity, so pasting and
`CategoryTheory.IsPullback.isoIsPullback` identify the two base changes. The two points over the
base are introduced as variables constrained by equations, rather than written out, because the
classifying morphism itself mentions them and a rewrite in the goal would be circular.

## References

* [Stacks Project, Tag 05YN](https://stacks.math.columbia.edu/tag/05YN)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The affine scheme of pairs `(g, m)` consisting of a unit-fixing matrix and a free
`d`-dimensional algebra structure: the product of the unit-fixing group scheme with the scheme of
structure constants over the integers. -/
noncomputable abbrev pairScheme : Scheme.{u} :=
  pullback (specULiftZIsTerminal.from (unitFixingScheme.{u} d))
    (specULiftZIsTerminal.from (scheme.{u} d))

/-- The scheme of pairs is affine: it is the fibre product of two affine schemes over the
terminal affine scheme `Spec ℤ`. -/
instance : IsAffine (pairScheme.{u} d) := inferInstance

/-- The projection of the scheme of pairs to the unit-fixing group scheme. -/
noncomputable abbrev pairMatrix : pairScheme.{u} d ⟶ unitFixingScheme.{u} d := pullback.fst _ _

/-- The projection of the scheme of pairs to the scheme of structure constants. -/
noncomputable abbrev pairPoint : pairScheme.{u} d ⟶ scheme.{u} d := pullback.snd _ _

/-- The tautological unit-fixing matrix over the global sections of the scheme of pairs. -/
noncomputable abbrev pairUniversalMatrix : UnitFixingMatrix Γ(pairScheme.{u} d, ⊤) d :=
  unitFixingSchemeHomEquiv d (pairScheme.{u} d) (pairMatrix.{u} d)

/-- The morphism to the scheme of pairs classifying a unit-fixing matrix over the global
sections of a scheme together with a point of the scheme of structure constants. -/
noncomputable abbrev pairClassify {T : Scheme.{u}} (g : UnitFixingMatrix Γ(T, ⊤) d)
    (x : T ⟶ scheme.{u} d) : T ⟶ pairScheme.{u} d :=
  pullback.lift ((unitFixingSchemeHomEquiv d T).symm g) x
    (IsTerminal.hom_ext specULiftZIsTerminal _ _)

/-- The classifying morphism of a pair pulls the tautological point back to the given point. -/
theorem pairClassify_comp_pairPoint {T : Scheme.{u}} (g : UnitFixingMatrix Γ(T, ⊤) d)
    (x : T ⟶ scheme.{u} d) : pairClassify d g x ≫ pairPoint.{u} d = x :=
  pullback.lift_snd _ _ _

/-- The classifying morphism of a pair pulls the tautological unit-fixing matrix back to the
given matrix. -/
theorem map_pairUniversalMatrix {T : Scheme.{u}} (g : UnitFixingMatrix Γ(T, ⊤) d)
    (x : T ⟶ scheme.{u} d) :
    UnitFixingMatrix.map (pairClassify d g x).appTop.hom (pairUniversalMatrix.{u} d) = g := by
  refine (unitFixingSchemeHomEquiv_comp d (pairClassify d g x) (pairMatrix.{u} d)).symm.trans ?_
  rw [pullback.lift_fst]
  exact Equiv.apply_symm_apply _ _


/-- The image of the tautological point of the scheme of structure constants under the
conjugation action of the tautological unit-fixing matrix. -/
noncomputable abbrev pairAction (laws : ConjugationPreservesAlgebraLaws.{u} d) :
    pairScheme.{u} d ⟶ scheme.{u} d :=
  conjugationOnPoints laws (pairScheme.{u} d) (pairUniversalMatrix.{u} d) (pairPoint.{u} d)

/-- The classifying morphism of a pair pulls the tautological conjugated point back to the
conjugate of the given point. -/
theorem pairClassify_comp_pairAction (laws : ConjugationPreservesAlgebraLaws.{u} d)
    {T : Scheme.{u}} (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    pairClassify d g x ≫ pairAction.{u} d laws = conjugationOnPoints laws T g x := by
  have h := conjugationOnPoints_naturality laws (pairClassify d g x)
    (pairUniversalMatrix.{u} d) (pairPoint.{u} d)
  rw [map_pairUniversalMatrix, pairClassify_comp_pairPoint] at h
  exact h.symm

/-- An isomorphism over the base between the degree-`d` covers attached to two points of the
scheme of structure constants transports along base change. -/
theorem exists_iso_pullback_universalCoverHom_of_comp_eq {T W : Scheme.{u}} (u : T ⟶ W)
    (y₁ y₂ : W ⟶ scheme.{u} d)
    (e : pullback (universalCoverHom.{u} d) y₁ ≅ pullback (universalCoverHom.{u} d) y₂)
    (he : e.hom ≫ pullback.snd (universalCoverHom.{u} d) y₂ =
      pullback.snd (universalCoverHom.{u} d) y₁)
    {x₁ x₂ : T ⟶ scheme.{u} d} (h₁ : u ≫ y₁ = x₁) (h₂ : u ≫ y₂ = x₂) :
    ∃ e' : pullback (universalCoverHom.{u} d) x₁ ≅ pullback (universalCoverHom.{u} d) x₂,
      e'.hom ≫ pullback.snd (universalCoverHom.{u} d) x₂ =
        pullback.snd (universalCoverHom.{u} d) x₁ := by
  subst h₁
  subst h₂
  have sq := fun y : W ⟶ scheme.{u} d => IsPullback.of_right'
    (IsPullback.of_hasPullback (universalCoverHom.{u} d) (u ≫ y))
    (IsPullback.of_hasPullback (universalCoverHom.{u} d) y)
  have hiso : IsPullback e.hom (pullback.snd (universalCoverHom.{u} d) y₁)
      (pullback.snd (universalCoverHom.{u} d) y₂) (𝟙 W) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact he⟩
  have sq₁' := (sq y₁).paste_horiz hiso
  rw [Category.comp_id] at sq₁'
  exact ⟨sq₁'.isoIsPullback _ _ (sq y₂), IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

/-- **Clause (a) of the proof of Stacks 05YQ for the universal cover**, over an arbitrary base:
the degree-`d` cover attached to a point `x` of the scheme of structure constants and the one
attached to its image under the conjugation action of a unit-fixing matrix over the global
sections of the base are isomorphic as schemes over the base. -/
theorem exists_iso_pullback_universalCoverHom_conjugation'
    (laws : ConjugationPreservesAlgebraLaws.{u} d) {T : Scheme.{u}}
    (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    ∃ e : pullback (universalCoverHom.{u} d) x ≅
        pullback (universalCoverHom.{u} d) (conjugationOnPoints laws T g x),
      e.hom ≫ pullback.snd (universalCoverHom.{u} d) (conjugationOnPoints laws T g x) =
        pullback.snd (universalCoverHom.{u} d) x := by
  obtain ⟨eW, heW⟩ := exists_iso_pullback_universalCoverHom_conjugation (d := d) laws
    (pairUniversalMatrix.{u} d) (pairPoint.{u} d)
  exact exists_iso_pullback_universalCoverHom_of_comp_eq d (pairClassify d g x)
    (pairPoint.{u} d) (pairAction.{u} d laws) eW heW
    (pairClassify_comp_pairPoint d g x) (pairClassify_comp_pairAction d laws g x)

end AlgebraicGeometry.FiniteFreeAlgebra

end
