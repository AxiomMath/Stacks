module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.GroupStructure

/-!
# The diagonal of the source-target morphism of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U`, arrow space `R`,
source `s`, target `t`, and stabilizer group algebraic space `S ⟶ U` with unit section
`e : U ⟶ S`. The relative diagonal of `j = (t, s) : R ⟶ U ×_B U` fits into the commutative
diagram
```
R                --- f ↦ (f, s f) --->   R ×_{s, U} U  --->  U
|                                            |               |
| Δ                                          |               | e
v                                            v               v
R ×_{U ×_B U} R  --- (f, g) ↦ (f, f⁻¹ g) --> R ×_{s, U} S  --->  S
```
whose two horizontal morphisms are isomorphisms and whose right hand square is cartesian. In
particular the diagonal of `j` is, up to those two isomorphisms, a base change of the unit
section of the stabilizer.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowPairs`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowsOverObjects` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowsOverStabilizer`: the three fibre products
  `R ×_{U ×_B U} R`, `R ×_{s, U} U` and `R ×_{s, U} S` appearing in the diagram.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowToArrowsOverObjects`: the upper horizontal
  morphism `f ↦ (f, s f)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowDifference`: the arrow `f⁻¹ g` of a pair of
  arrows with the same source and the same target, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowPairsToArrowsOverStabilizer`: the lower
  horizontal morphism `(f, g) ↦ (f, f⁻¹ g)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowsOverObjectsUnit`: the middle vertical
  morphism, which applies the unit section of the stabilizer to the second coordinate.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_arrowToArrowsOverObjects`: **Stacks
  0454**, the upper horizontal morphism is an isomorphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_arrowPairsToArrowsOverStabilizer`:
  **Stacks 0454**, the lower horizontal morphism is an isomorphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.diagonal_comp_arrowPairsToArrowsOverStabilizer`:
  **Stacks 0454**, the left hand square commutes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_stabilizerUnit`: **Stacks 0454**, the
  right hand square is cartesian.

## Implementation notes

Everything is computed with generalized arrows, that is with morphisms of presheaves into the
arrow space, and with their composition
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose` and its groupoid laws; no point
of a test object is ever named. The inverse of a generalized arrow is postcomposition with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`, so the second coordinate of the
lower horizontal morphism is the single generalized arrow
`groupoidCompose G (arrowPairsFst G ≫ groupoidInverse G) (arrowPairsSnd G)`, and the two
inverse laws `groupoidCompose_inverseLeft` and `groupoidCompose_inverseRight` are exactly what
makes it invertible: both round trips reduce, by associativity, to composing with an identity
arrow.

That a generalized arrow whose source and target agree factors through the stabilizer is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_condition`, which supplies the
compatibility for every morphism into the stabilizer constructed here; that the unit section
of the stabilizer is the identity arrow is read off from
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrowHom_one`.

The right hand square is obtained by cancellation rather than by exhibiting a limit: pasted
below the cartesian square of `R ×_{s, U} S` it becomes the cartesian square of
`R ×_{s, U} U`, because the unit section is a section of the structure morphism of the
stabilizer, so `CategoryTheory.IsPullback.of_bot` applies.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 0454](https://stacks.math.columbia.edu/tag/0454)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The unit section of the stabilizer -/

/-- The unit section of the stabilizer is a section of its structure morphism. -/
theorem stabilizerUnit_comp_hom (G : GroupoidInAlgebraicSpaces C S hS B) :
    (η[stabilizer G]).left ≫ (stabilizer G).hom = 𝟙 G.objects.obj := by
  simpa using Over.w (η[stabilizer G])

/-- The arrow of the groupoid underlying the unit section of the stabilizer is the identity
arrow. -/
theorem stabilizerUnit_comp_stabilizerArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    (η[stabilizer G]).left ≫ stabilizerArrow G = (identityArrow G).hom := by
  have h := stabilizerArrowHom_one G (𝟙 (𝟙_ (Over G.objects.obj)))
  rw [Category.id_comp] at h
  change (stabilizerOne G).left ≫ stabilizerArrow G = (identityArrow G).hom
  simpa [stabilizerArrowHom] using h

/-! ### The three fibre products of the diagram -/

/-- The space `R ×_{U ×_B U} R` of pairs of arrows of a groupoid in algebraic spaces having the
same source and the same target. -/
noncomputable abbrev arrowPairs (G : GroupoidInAlgebraicSpaces C S hS B) :
    (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback (sourceTarget G).hom (sourceTarget G).hom

/-- The first arrow of a pair of arrows with the same source and the same target. -/
noncomputable abbrev arrowPairsFst (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ G.arrows.obj :=
  pullback.fst (sourceTarget G).hom (sourceTarget G).hom

/-- The second arrow of a pair of arrows with the same source and the same target. -/
noncomputable abbrev arrowPairsSnd (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ G.arrows.obj :=
  pullback.snd (sourceTarget G).hom (sourceTarget G).hom

/-- The space `R ×_{s, U} U` of an arrow together with a point of the object space equal to its
source. -/
noncomputable abbrev arrowsOverObjects (G : GroupoidInAlgebraicSpaces C S hS B) :
    (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback G.source.hom (𝟙 G.objects.obj)

/-- The projection of `R ×_{s, U} U` to the object space. -/
noncomputable abbrev arrowsOverObjectsToObjects (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverObjects G ⟶ G.objects.obj :=
  pullback.snd G.source.hom (𝟙 G.objects.obj)

/-- The space `R ×_{s, U} S` of an arrow together with a point of the stabilizer lying over its
source. -/
noncomputable abbrev arrowsOverStabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback G.source.hom (stabilizer G).hom

/-- The arrow coordinate of a point of `R ×_{s, U} S`. -/
noncomputable abbrev arrowsOverStabilizerFst (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizer G ⟶ G.arrows.obj :=
  pullback.fst G.source.hom (stabilizer G).hom

/-- The projection of `R ×_{s, U} S` to the stabilizer. -/
noncomputable abbrev arrowsOverStabilizerToStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizer G ⟶ (stabilizer G).left :=
  pullback.snd G.source.hom (stabilizer G).hom

/-- The arrow of the groupoid underlying the stabilizer coordinate of a point of
`R ×_{s, U} S`. -/
noncomputable abbrev arrowsOverStabilizerArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizer G ⟶ G.arrows.obj :=
  arrowsOverStabilizerToStabilizer G ≫ stabilizerArrow G

/-! ### The upper horizontal morphism -/

/-- The upper horizontal morphism `f ↦ (f, s f)` of the diagram of **Stacks 0454**. -/
noncomputable def arrowToArrowsOverObjects (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ arrowsOverObjects G :=
  pullback.lift (𝟙 _) G.source.hom (by simp)

/-- The first coordinate of `f ↦ (f, s f)` is the arrow itself. -/
theorem arrowToArrowsOverObjects_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowToArrowsOverObjects G ≫ pullback.fst G.source.hom (𝟙 G.objects.obj) =
      𝟙 G.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `f ↦ (f, s f)` is the source of the arrow. -/
theorem arrowToArrowsOverObjects_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowToArrowsOverObjects G ≫ arrowsOverObjectsToObjects G = G.source.hom :=
  pullback.lift_snd _ _ _

/-- **Stacks 0454.** The upper horizontal morphism `f ↦ (f, s f)` of the diagram is an
isomorphism, its inverse being the first projection of `R ×_{s, U} U`. -/
@[stacks 0454 "the upper horizontal morphism is an isomorphism"]
theorem isIso_arrowToArrowsOverObjects (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsIso (arrowToArrowsOverObjects G) := by
  refine ⟨⟨pullback.fst G.source.hom (𝟙 G.objects.obj),
    arrowToArrowsOverObjects_comp_fst G, pullback.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, arrowToArrowsOverObjects_comp_fst, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, arrowToArrowsOverObjects_comp_snd, Category.id_comp]
    simpa using (pullback.condition :
      pullback.fst G.source.hom (𝟙 G.objects.obj) ≫ G.source.hom =
        pullback.snd G.source.hom (𝟙 G.objects.obj) ≫ 𝟙 G.objects.obj)

/-! ### The lower horizontal morphism -/

/-- The two arrows of a pair in `R ×_{U ×_B U} R` have the same target. -/
theorem arrowPairsFst_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsFst G ≫ G.target.hom = arrowPairsSnd G ≫ G.target.hom := by
  calc
    arrowPairsFst G ≫ G.target.hom
        = (arrowPairsFst G ≫ (sourceTarget G).hom) ≫ (objectPairsTarget G).hom := by
          rw [Category.assoc, sourceTarget_target_projection]
    _ = (arrowPairsSnd G ≫ (sourceTarget G).hom) ≫ (objectPairsTarget G).hom := by
          rw [pullback.condition]
    _ = arrowPairsSnd G ≫ G.target.hom := by
          rw [Category.assoc, sourceTarget_target_projection]

/-- The two arrows of a pair in `R ×_{U ×_B U} R` have the same source. -/
theorem arrowPairsFst_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsFst G ≫ G.source.hom = arrowPairsSnd G ≫ G.source.hom := by
  calc
    arrowPairsFst G ≫ G.source.hom
        = (arrowPairsFst G ≫ (sourceTarget G).hom) ≫ (objectPairsSource G).hom := by
          rw [Category.assoc, sourceTarget_source_projection]
    _ = (arrowPairsSnd G ≫ (sourceTarget G).hom) ≫ (objectPairsSource G).hom := by
          rw [pullback.condition]
    _ = arrowPairsSnd G ≫ G.source.hom := by
          rw [Category.assoc, sourceTarget_source_projection]

/-- The inverse of the first arrow of a pair in `R ×_{U ×_B U} R` is composable after the
second. -/
theorem arrowPairs_inverse_composable (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowPairsFst G ≫ groupoidInverse G) ≫ G.source.hom =
      arrowPairsSnd G ≫ G.target.hom := by
  rw [Category.assoc, groupoidInverse_source]
  exact arrowPairsFst_comp_target G

/-- The arrow `f⁻¹ g` attached to a pair `(f, g)` of arrows with the same source and the same
target. -/
noncomputable def arrowDifference (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ G.arrows.obj :=
  groupoidCompose G (arrowPairsFst G ≫ groupoidInverse G) (arrowPairsSnd G)
    (arrowPairs_inverse_composable G)

/-- The source of `f⁻¹ g` is the common source of `f` and `g`. -/
theorem arrowDifference_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowDifference G ≫ G.source.hom = arrowPairsFst G ≫ G.source.hom := by
  rw [arrowDifference, groupoidCompose_source]
  exact (arrowPairsFst_comp_source G).symm

/-- The target of `f⁻¹ g` is the common source of `f` and `g`. -/
theorem arrowDifference_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowDifference G ≫ G.target.hom = arrowPairsFst G ≫ G.source.hom := by
  rw [arrowDifference, groupoidCompose_target, Category.assoc, groupoidInverse_target]

/-- The arrow `f⁻¹ g`, read as a point of the stabilizer over the common source of `f` and
`g`. -/
noncomputable def arrowDifferenceToStabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ (stabilizer G).left :=
  pullback.lift (arrowDifference G) (arrowPairsFst G ≫ G.source.hom)
    (stabilizerArrow_condition G (arrowDifference G) _
      (arrowDifference_comp_source G) (arrowDifference_comp_target G))

/-- The arrow underlying the stabilizer point `f⁻¹ g` is `f⁻¹ g`. -/
theorem arrowDifferenceToStabilizer_comp_arrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowDifferenceToStabilizer G ≫ stabilizerArrow G = arrowDifference G :=
  pullback.lift_fst _ _ _

/-- The stabilizer point `f⁻¹ g` lies over the common source of `f` and `g`. -/
theorem arrowDifferenceToStabilizer_comp_hom (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowDifferenceToStabilizer G ≫ (stabilizer G).hom =
      arrowPairsFst G ≫ G.source.hom :=
  pullback.lift_snd _ _ _

/-- The lower horizontal morphism `(f, g) ↦ (f, f⁻¹ g)` of the diagram of **Stacks 0454**. -/
noncomputable def arrowPairsToArrowsOverStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ arrowsOverStabilizer G :=
  pullback.lift (arrowPairsFst G) (arrowDifferenceToStabilizer G)
    (arrowDifferenceToStabilizer_comp_hom G).symm

/-- The first coordinate of `(f, g) ↦ (f, f⁻¹ g)` is `f`. -/
theorem arrowPairsToArrowsOverStabilizer_comp_fst
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerFst G = arrowPairsFst G :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `(f, g) ↦ (f, f⁻¹ g)` is the stabilizer point `f⁻¹ g`. -/
theorem arrowPairsToArrowsOverStabilizer_comp_snd
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerToStabilizer G =
      arrowDifferenceToStabilizer G :=
  pullback.lift_snd _ _ _

/-- On `R ×_{s, U} S` the arrow coordinate is composable after the arrow underlying the
stabilizer coordinate. -/
theorem arrowsOverStabilizer_composable (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerFst G ≫ G.source.hom =
      arrowsOverStabilizerArrow G ≫ G.target.hom := by
  rw [arrowsOverStabilizerArrow, Category.assoc, stabilizerArrow_target]
  exact pullback.condition

/-- The composite `f h` of the two coordinates of a point `(f, h)` of `R ×_{s, U} S`. -/
noncomputable def arrowsOverStabilizerCompose (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizer G ⟶ G.arrows.obj :=
  groupoidCompose G (arrowsOverStabilizerFst G) (arrowsOverStabilizerArrow G)
    (arrowsOverStabilizer_composable G)

/-- The target of `f h` is the target of `f`. -/
theorem arrowsOverStabilizerCompose_comp_target
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerCompose G ≫ G.target.hom =
      arrowsOverStabilizerFst G ≫ G.target.hom := by
  rw [arrowsOverStabilizerCompose, groupoidCompose_target]

/-- The source of `f h` is the source of `f`. -/
theorem arrowsOverStabilizerCompose_comp_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerCompose G ≫ G.source.hom =
      arrowsOverStabilizerFst G ≫ G.source.hom := by
  rw [arrowsOverStabilizerCompose, groupoidCompose_source, arrowsOverStabilizerArrow,
    Category.assoc, stabilizerArrow_source]
  exact pullback.condition.symm

/-- The morphism `(f, h) ↦ (f, f h)`, inverse to the lower horizontal morphism of the
diagram. -/
noncomputable def arrowsOverStabilizerToArrowPairs
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizer G ⟶ arrowPairs G :=
  pullback.lift (arrowsOverStabilizerFst G) (arrowsOverStabilizerCompose G) (by
    refine pullback.hom_ext ?_ ?_
    · change (arrowsOverStabilizerFst G ≫ (sourceTarget G).hom) ≫
          (objectPairsTarget G).hom =
        (arrowsOverStabilizerCompose G ≫ (sourceTarget G).hom) ≫
          (objectPairsTarget G).hom
      rw [Category.assoc, Category.assoc, sourceTarget_target_projection,
        arrowsOverStabilizerCompose_comp_target]
    · change (arrowsOverStabilizerFst G ≫ (sourceTarget G).hom) ≫
          (objectPairsSource G).hom =
        (arrowsOverStabilizerCompose G ≫ (sourceTarget G).hom) ≫
          (objectPairsSource G).hom
      rw [Category.assoc, Category.assoc, sourceTarget_source_projection,
        arrowsOverStabilizerCompose_comp_source])

/-- The first coordinate of `(f, h) ↦ (f, f h)` is `f`. -/
theorem arrowsOverStabilizerToArrowPairs_comp_fst
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerToArrowPairs G ≫ arrowPairsFst G = arrowsOverStabilizerFst G :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `(f, h) ↦ (f, f h)` is `f h`. -/
theorem arrowsOverStabilizerToArrowPairs_comp_snd
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerToArrowPairs G ≫ arrowPairsSnd G =
      arrowsOverStabilizerCompose G :=
  pullback.lift_snd _ _ _

/-- An arrow equal to the identity at the target of `c` is a left unit for `c`. -/
private theorem groupoidCompose_eq_of_eq_identityAfterTarget
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (c e : T ⟶ G.arrows.obj) (he : e = identityAfterTarget G c)
    (w : e ≫ G.source.hom = c ≫ G.target.hom) : groupoidCompose G e c w = c := by
  subst he
  exact groupoidCompose_leftIdentity G c

/-- If `f` and `g` have the same target then `f (f⁻¹ g) = g`. -/
private theorem groupoidCompose_compose_inverse
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f g : T ⟶ G.arrows.obj) (h : f ≫ G.target.hom = g ≫ G.target.hom)
    (w : (f ≫ groupoidInverse G) ≫ G.source.hom = g ≫ G.target.hom)
    (wR : f ≫ G.source.hom =
      groupoidCompose G (f ≫ groupoidInverse G) g w ≫ G.target.hom) :
    groupoidCompose G f (groupoidCompose G (f ≫ groupoidInverse G) g w) wR = g := by
  have wab : f ≫ G.source.hom = (f ≫ groupoidInverse G) ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_target]
  rw [← groupoidCompose_assoc G f (f ≫ groupoidInverse G) g wab w
    ((groupoidCompose_source G _ _ wab).trans w) wR]
  refine groupoidCompose_eq_of_eq_identityAfterTarget G g _
    ((groupoidCompose_inverseLeft G f).trans ?_) _
  change f ≫ G.target.hom ≫ (identityArrow G).hom = g ≫ G.target.hom ≫ (identityArrow G).hom
  rw [← Category.assoc, ← Category.assoc, h]

/-- If `h` starts at the source of `f` then `f⁻¹ (f h) = h`. -/
private theorem groupoidCompose_inverse_compose
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f h : T ⟶ G.arrows.obj) (w : f ≫ G.source.hom = h ≫ G.target.hom)
    (w' : (f ≫ groupoidInverse G) ≫ G.source.hom = groupoidCompose G f h w ≫ G.target.hom) :
    groupoidCompose G (f ≫ groupoidInverse G) (groupoidCompose G f h w) w' = h := by
  have wab : (f ≫ groupoidInverse G) ≫ G.source.hom = f ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  rw [← groupoidCompose_assoc G (f ≫ groupoidInverse G) f h wab w
    ((groupoidCompose_source G _ _ wab).trans w) w']
  refine groupoidCompose_eq_of_eq_identityAfterTarget G h _
    ((groupoidCompose_inverseRight G f).trans ?_) _
  change f ≫ G.source.hom ≫ (identityArrow G).hom = h ≫ G.target.hom ≫ (identityArrow G).hom
  rw [← Category.assoc, ← Category.assoc, w]

/-- Composing `(f, g) ↦ (f, f⁻¹ g)` with `(f, h) ↦ (f, f h)` recovers the second arrow:
`f (f⁻¹ g) = g`. -/
private theorem arrowPairsToArrowsOverStabilizer_comp_compose
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerCompose G =
      arrowPairsSnd G := by
  have hsnd : arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerArrow G =
      arrowDifference G := by
    rw [arrowsOverStabilizerArrow, ← Category.assoc,
      arrowPairsToArrowsOverStabilizer_comp_snd, arrowDifferenceToStabilizer_comp_arrow]
  have wR : arrowPairsFst G ≫ G.source.hom = arrowDifference G ≫ G.target.hom :=
    (arrowDifference_comp_target G).symm
  calc
    arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerCompose G
        = groupoidCompose G
            (arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerFst G)
            (arrowPairsToArrowsOverStabilizer G ≫ arrowsOverStabilizerArrow G) _ :=
          groupoidCompose_pre G _ _ _ (arrowsOverStabilizer_composable G)
    _ = groupoidCompose G (arrowPairsFst G) (arrowDifference G) wR :=
          groupoidCompose_congr G _ wR
            (arrowPairsToArrowsOverStabilizer_comp_fst G) hsnd
    _ = arrowPairsSnd G :=
          groupoidCompose_compose_inverse G _ _ (arrowPairsFst_comp_target G) _ wR

/-- Composing `(f, h) ↦ (f, f h)` with `(f, g) ↦ (f, f⁻¹ g)` recovers the stabilizer
coordinate: `f⁻¹ (f h) = h`. -/
private theorem arrowsOverStabilizerToArrowPairs_comp_arrowDifference
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverStabilizerToArrowPairs G ≫ arrowDifference G =
      arrowsOverStabilizerArrow G := by
  have hfst : arrowsOverStabilizerToArrowPairs G ≫ (arrowPairsFst G ≫ groupoidInverse G) =
      arrowsOverStabilizerFst G ≫ groupoidInverse G := by
    rw [← Category.assoc, arrowsOverStabilizerToArrowPairs_comp_fst]
  have wR : (arrowsOverStabilizerFst G ≫ groupoidInverse G) ≫ G.source.hom =
      arrowsOverStabilizerCompose G ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source, arrowsOverStabilizerCompose_comp_target]
  calc
    arrowsOverStabilizerToArrowPairs G ≫ arrowDifference G
        = groupoidCompose G
            (arrowsOverStabilizerToArrowPairs G ≫ (arrowPairsFst G ≫ groupoidInverse G))
            (arrowsOverStabilizerToArrowPairs G ≫ arrowPairsSnd G) _ :=
          groupoidCompose_pre G _ _ _ (arrowPairs_inverse_composable G)
    _ = groupoidCompose G (arrowsOverStabilizerFst G ≫ groupoidInverse G)
          (arrowsOverStabilizerCompose G) wR :=
          groupoidCompose_congr G _ wR hfst
            (arrowsOverStabilizerToArrowPairs_comp_snd G)
    _ = arrowsOverStabilizerArrow G :=
          groupoidCompose_inverse_compose G _ _ (arrowsOverStabilizer_composable G) wR

/-- **Stacks 0454.** The lower horizontal morphism `(f, g) ↦ (f, f⁻¹ g)` of the diagram is an
isomorphism, its inverse being `(f, h) ↦ (f, f h)`. -/
@[stacks 0454 "the lower horizontal morphism is an isomorphism"]
theorem isIso_arrowPairsToArrowsOverStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsIso (arrowPairsToArrowsOverStabilizer G) := by
  refine ⟨⟨arrowsOverStabilizerToArrowPairs G, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, arrowsOverStabilizerToArrowPairs_comp_fst,
        arrowPairsToArrowsOverStabilizer_comp_fst, Category.id_comp]
    · rw [Category.assoc, arrowsOverStabilizerToArrowPairs_comp_snd, Category.id_comp]
      exact arrowPairsToArrowsOverStabilizer_comp_compose G
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, arrowPairsToArrowsOverStabilizer_comp_fst,
        arrowsOverStabilizerToArrowPairs_comp_fst, Category.id_comp]
    · rw [Category.assoc, arrowPairsToArrowsOverStabilizer_comp_snd, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, arrowDifferenceToStabilizer_comp_arrow]
        exact arrowsOverStabilizerToArrowPairs_comp_arrowDifference G
      · change arrowsOverStabilizerToArrowPairs G ≫
            arrowDifferenceToStabilizer G ≫ (stabilizer G).hom =
          arrowsOverStabilizerToStabilizer G ≫ (stabilizer G).hom
        rw [arrowDifferenceToStabilizer_comp_hom, ← Category.assoc,
          arrowsOverStabilizerToArrowPairs_comp_fst]
        exact pullback.condition

/-! ### The middle vertical morphism and the two squares -/

/-- The middle vertical morphism of the diagram of **Stacks 0454**: it applies the unit section
of the stabilizer to the second coordinate. -/
noncomputable def arrowsOverObjectsUnit (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverObjects G ⟶ arrowsOverStabilizer G :=
  pullback.lift (pullback.fst G.source.hom (𝟙 G.objects.obj))
    (arrowsOverObjectsToObjects G ≫ (η[stabilizer G]).left) (by
      rw [Category.assoc, stabilizerUnit_comp_hom]
      simpa using (pullback.condition :
        pullback.fst G.source.hom (𝟙 G.objects.obj) ≫ G.source.hom =
          pullback.snd G.source.hom (𝟙 G.objects.obj) ≫ 𝟙 G.objects.obj))

/-- The middle vertical morphism does not change the arrow coordinate. -/
theorem arrowsOverObjectsUnit_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverObjectsUnit G ≫ arrowsOverStabilizerFst G =
      pullback.fst G.source.hom (𝟙 G.objects.obj) :=
  pullback.lift_fst _ _ _

/-- The stabilizer coordinate of the middle vertical morphism is the unit section. -/
theorem arrowsOverObjectsUnit_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowsOverObjectsUnit G ≫ arrowsOverStabilizerToStabilizer G =
      arrowsOverObjectsToObjects G ≫ (η[stabilizer G]).left :=
  pullback.lift_snd _ _ _

/-- The second coordinate of the diagonal of `j` composed with `(f, g) ↦ (f, f⁻¹ g)` is the
identity arrow: `f⁻¹ f` is the identity at the source of `f`. -/
private theorem diagonal_comp_arrowDifference (G : GroupoidInAlgebraicSpaces C S hS B) :
    pullback.diagonal (sourceTarget G).hom ≫ arrowDifference G =
      G.source.hom ≫ (identityArrow G).hom := by
  have hfst : pullback.diagonal (sourceTarget G).hom ≫
      (arrowPairsFst G ≫ groupoidInverse G) = 𝟙 G.arrows.obj ≫ groupoidInverse G := by
    rw [← Category.assoc, pullback.diagonal_fst]
  have wab : (𝟙 G.arrows.obj ≫ groupoidInverse G) ≫ G.source.hom =
      𝟙 G.arrows.obj ≫ G.target.hom := by
    rw [Category.id_comp, Category.id_comp, groupoidInverse_source]
  calc
    pullback.diagonal (sourceTarget G).hom ≫ arrowDifference G
        = groupoidCompose G
            (pullback.diagonal (sourceTarget G).hom ≫
              (arrowPairsFst G ≫ groupoidInverse G))
            (pullback.diagonal (sourceTarget G).hom ≫ arrowPairsSnd G) _ :=
          groupoidCompose_pre G _ _ _ (arrowPairs_inverse_composable G)
    _ = groupoidCompose G (𝟙 G.arrows.obj ≫ groupoidInverse G) (𝟙 G.arrows.obj) wab :=
          groupoidCompose_congr G _ wab hfst (pullback.diagonal_snd _)
    _ = identityAfterSource G (𝟙 G.arrows.obj) := groupoidCompose_inverseRight G _
    _ = G.source.hom ≫ (identityArrow G).hom := Category.id_comp _

/-- **Stacks 0454.** The left hand square of the diagram commutes: the relative diagonal of
`j = (t, s)`, followed by `(f, g) ↦ (f, f⁻¹ g)`, is `f ↦ (f, s f)` followed by the unit
section of the stabilizer. -/
@[stacks 0454 "commutativity of the left hand square"]
theorem diagonal_comp_arrowPairsToArrowsOverStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    pullback.diagonal (sourceTarget G).hom ≫ arrowPairsToArrowsOverStabilizer G =
      arrowToArrowsOverObjects G ≫ arrowsOverObjectsUnit G := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, arrowPairsToArrowsOverStabilizer_comp_fst,
      arrowsOverObjectsUnit_comp_fst, arrowToArrowsOverObjects_comp_fst,
      pullback.diagonal_fst]
  · rw [Category.assoc, Category.assoc, arrowPairsToArrowsOverStabilizer_comp_snd,
      arrowsOverObjectsUnit_comp_snd, ← Category.assoc,
      arrowToArrowsOverObjects_comp_snd]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, arrowDifferenceToStabilizer_comp_arrow, Category.assoc,
        stabilizerUnit_comp_stabilizerArrow]
      exact diagonal_comp_arrowDifference G
    · change pullback.diagonal (sourceTarget G).hom ≫
          arrowDifferenceToStabilizer G ≫ (stabilizer G).hom =
        (G.source.hom ≫ (η[stabilizer G]).left) ≫ (stabilizer G).hom
      rw [arrowDifferenceToStabilizer_comp_hom, ← Category.assoc,
        pullback.diagonal_fst, Category.id_comp, Category.assoc, stabilizerUnit_comp_hom,
        Category.comp_id]

/-- **Stacks 0454.** The right hand square of the diagram is cartesian: `R ×_{s, U} S` is the
base change of the unit section `e : U ⟶ S` of the stabilizer along the projection
`R ×_{s, U} S ⟶ S`, the base change being `R ×_{s, U} U`. -/
@[stacks 0454 "the right hand square is cartesian"]
theorem isPullback_stabilizerUnit (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback (arrowsOverObjectsToObjects G) (arrowsOverObjectsUnit G)
      (η[stabilizer G]).left (arrowsOverStabilizerToStabilizer G) := by
  refine IsPullback.of_bot (v₂₁ := arrowsOverStabilizerFst G)
    (v₂₂ := (stabilizer G).hom) ?_ (arrowsOverObjectsUnit_comp_snd G).symm
    (IsPullback.of_hasPullback G.source.hom (stabilizer G).hom).flip
  rw [arrowsOverObjectsUnit_comp_fst, stabilizerUnit_comp_hom]
  exact (IsPullback.of_hasPullback G.source.hom (𝟙 G.objects.obj)).flip

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
