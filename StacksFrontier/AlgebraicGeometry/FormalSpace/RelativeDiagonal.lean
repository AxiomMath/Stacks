module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.DiagonalFunctor

/-!
# The relative diagonal of a morphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
fppf sheaves on the big fppf site of `S`. **Stacks 0AN2** says that if `X` is a formal
algebraic space then the relative diagonal `Δ : X ⟶ X ×_Y X` is representable by schemes, a
monomorphism, locally quasi-finite, locally of finite type and separated.

## Main results

* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_pullback_diagonal`,
  `AlgebraicGeometry.FormalSpace.relative_pullback_diagonal`: the relative diagonal of a
  morphism out of `X` is representable, respectively has every represented base change in a
  given class `Q` of morphisms of the site, whenever the absolute diagonal of `X` is.
* `AlgebraicGeometry.FormalSpace.relative_isClosedImmersion_diag_of_isAffineFormal`:
  **Stacks 0AI8** for the affine formal algebraic space condition rather than for a chosen
  presentation of it.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_isClosedImmersion_of_isAffineFormal`:
  **Stacks 0AI8** as a statement about a pair of scheme-valued points — their fibre product
  over an affine formal algebraic space is an object of the site, by a closed immersion into
  the product of the two sources.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isAffineFormal`,
  `…relative_locallyQuasiFinite_diag_of_isAffineFormal`,
  `…relative_locallyOfFiniteType_diag_of_isAffineFormal`,
  `…relative_isSeparated_diag_of_isAffineFormal`: four of the five assertions of **Stacks
  0AIP** for an *affine* formal algebraic space.
* `AlgebraicGeometry.FormalSpace.mono_diag_of_isFormalAlgebraicSpace`: the remaining assertion
  of **Stacks 0AIP**, that the absolute diagonal is a monomorphism, for an *arbitrary* formal
  algebraic space.
* `AlgebraicGeometry.FormalSpace.mono_pullback_diagonal_of_isFormalAlgebraicSpace`: the same
  assertion of **Stacks 0AN2**, for a morphism whose source is an *arbitrary* formal algebraic
  space.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_pullback_diagonal_of_isAffineFormal`,
  `…relative_locallyQuasiFinite_pullback_diagonal_of_isAffineFormal`,
  `…relative_locallyOfFiniteType_pullback_diagonal_of_isAffineFormal`,
  `…relative_isSeparated_pullback_diagonal_of_isAffineFormal`: four of the five assertions of
  **Stacks 0AN2** for a morphism whose source is an *affine* formal algebraic space.

## Implementation notes

`AlgebraicGeometry.FormalSpace.relativelyRepresentable_pullback_diagonal` and
`AlgebraicGeometry.FormalSpace.relative_pullback_diagonal` take the corresponding assertion of
Stacks 0AIP for the absolute diagonal as a hypothesis, because that assertion for an arbitrary
formal algebraic space is proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable`, which imports this module.
The four affine-source results are special cases of the general forms there, kept for their
sharper conclusion: the represented base changes of the diagonal are closed immersions.

The monomorphism assertions hold because a diagonal is a split monomorphism, so the hypothesis
that `X` is a formal algebraic space is carried only to match the statements of Stacks 0AIP and
Stacks 0AN2. The underlying Mathlib instances, `CategoryTheory.Limits.instIsSplitMonoDiag` and
`CategoryTheory.Limits.pullback.instIsSplitMonoDiagonal`, are registered at the end of the file.

Local quasi-finiteness is recorded as the infimum of `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.LocallyQuasiFinite`, because Mathlib's `LocallyQuasiFinite` for schemes
does not itself include local finite type whereas the source's notion does.

## References

* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Categorical

variable {C : Type*} [Category* C] [HasPullbacks C] [HasBinaryProducts C]

/-- In a category with fibre products and binary products the relative diagonal of a morphism
`f : X ⟶ Y` is a base change of the absolute diagonal of `X`, along the comparison morphism
from the relative self-product of `X` over `Y` to the absolute one. -/
private theorem relativeDiagonal_isPullback {X Y : C} (f : X ⟶ Y) :
    IsPullback (𝟙 X) (pullback.diagonal f) (diag X)
      (prod.lift (pullback.fst f f) (pullback.snd f f)) := by
  have hd : 𝟙 X ≫ diag X =
      pullback.diagonal f ≫ prod.lift (pullback.fst f f) (pullback.snd f f) := by
    rw [Category.id_comp]
    apply prod.hom_ext <;> simp
  refine ⟨⟨hd⟩, ⟨PullbackCone.IsLimit.mk hd (fun s ↦ s.fst) ?_ ?_ ?_⟩⟩
  · intro s
    simp
  · intro s
    apply pullback.hom_ext
    · simpa using congrArg (fun k ↦ k ≫ prod.fst) s.condition
    · simpa using congrArg (fun k ↦ k ≫ prod.snd) s.condition
  · intro s m hm₁ _
    simpa using hm₁

end Categorical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the absolute diagonal of an fppf sheaf `X` on the big fppf site of `S` is representable by
objects of the site, then so is the relative diagonal of every morphism out of `X`. -/
@[stacks 0AN2 "representability, by base change from the representability assertion of Stacks \
0AIP for the absolute diagonal of the source, which is available for an arbitrary formal \
algebraic space in StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable, where this \
reduction is fed it"]
theorem relativelyRepresentable_pullback_diagonal {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (diag X)) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (pullback.diagonal f) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).of_isPullback
    (relativeDiagonal_isPullback f) hX

/-- If every represented base change of the absolute diagonal of an fppf sheaf `X` on the big
fppf site of `S` is a morphism of the site with `Q`, then the same holds for the relative
diagonal of every morphism out of `X`. -/
@[stacks 0AN2 "the locally quasi-finite, locally of finite type and separated assertions at \
once, by base change from the corresponding assertion of Stacks 0AIP for the absolute diagonal \
of the source, taken uniformly in the property of morphisms of the site; all three are \
available for an arbitrary formal algebraic space in \
StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable, where this reduction is fed \
them"]
theorem relative_pullback_diagonal (Q : MorphismProperty (BigFppfOver B S hS))
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : Q.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X)) :
    Q.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (pullback.diagonal f) :=
  (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
    (relativeDiagonal_isPullback f) hX

/-- A morphism property of schemes implied by closed immersions is implied for every represented
base change of a morphism whose represented base changes are closed immersions. -/
private theorem relative_inverseImage_of_isClosedImmersion
    {P : MorphismProperty Scheme.{u}}
    (hP : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion g], P g)
    {X Y : FppfSheaf B S hS} (g : X ⟶ Y)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g :=
  MorphismProperty.relative_monotone (fun _ _ t ht ↦ by
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map t) := ht
    exact hP _) g h

/-- **Stacks 0AI8** in terms of the affine formal algebraic space condition: every represented
base change of the absolute diagonal of an affine formal algebraic space is a closed immersion
of objects of the site. -/
theorem relative_isClosedImmersion_diag_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) := by
  obtain ⟨-, I, pre, hI, hdir, D, hD, ⟨e⟩⟩ := hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hI
  let _ : IsDirected I (· ≤ ·) := hdir
  exact diagonal_isClosedImmersion B S hS D hD X e.symm

/-- **Stacks 0AI8** as a statement about a pair of scheme-valued points rather than about the
diagonal: for an affine formal algebraic space `X` over `S` and points `α`, `β` of it over
objects `A`, `C` of the site, the fibre product `h_A^# ×_X h_C^#` is represented by an object
`W` of the site whose canonical morphism to `A ⨯ C` is a closed immersion of schemes. -/
theorem exists_isPullback_isClosedImmersion_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (A C : BigFppfOver B S hS)
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj A ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj C ⟶ X) :
    ∃ (W : BigFppfOver B S hS)
      (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ≅ pullback α β)
      (f : W ⟶ A ⨯ C),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.fst) =
          i.hom ≫ pullback.fst α β ∧
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.snd) =
          i.hom ≫ pullback.snd α β ∧
        AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  exact MorphismProperty.exists_isPullback_of_relative_diag _ _
    (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX) A C α β

/-- The absolute diagonal of an affine formal algebraic space is representable by objects of the
site. -/
@[stacks 0AIP "representable by schemes, for an affine formal algebraic space"]
theorem relativelyRepresentable_diag_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable (diag X) :=
  (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX).rep

/-- Every represented base change of the absolute diagonal of an affine formal algebraic space is
a locally quasi-finite, locally of finite type morphism of schemes. -/
@[stacks 0AIP "locally quasi-finite, for an affine formal algebraic space"]
theorem relative_locallyQuasiFinite_diag_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) :=
  relative_inverseImage_of_isClosedImmersion B S hS
    (by intros; exact ⟨inferInstance, inferInstance⟩)
    (diag X)
    (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX)

/-- Every represented base change of the absolute diagonal of an affine formal algebraic space is
a locally of finite type morphism of schemes. -/
@[stacks 0AIP "locally of finite type, for an affine formal algebraic space"]
theorem relative_locallyOfFiniteType_diag_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) :=
  relative_inverseImage_of_isClosedImmersion B S hS (by intros; infer_instance) (diag X)
    (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX)

/-- Every represented base change of the absolute diagonal of an affine formal algebraic space is
a separated morphism of schemes. -/
@[stacks 0AIP "separated, for an affine formal algebraic space"]
theorem relative_isSeparated_diag_of_isAffineFormal {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) :=
  relative_inverseImage_of_isClosedImmersion B S hS (by intros; infer_instance) (diag X)
    (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX)

/-- The absolute diagonal of a formal algebraic space over `S` is a monomorphism of fppf sheaves,
which by **Stacks 0AQB** is what it is for a morphism of formal algebraic spaces to be a
monomorphism. -/
@[stacks 0AIP "monomorphism, for an arbitrary formal algebraic space"]
theorem mono_diag_of_isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (_hX : IsFormalAlgebraicSpace B S hS X) : Mono (diag X) :=
  inferInstance

/-- Every represented base change of the relative diagonal of a morphism out of an affine
formal algebraic space is a closed immersion of objects of the site. -/
theorem relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_pullback_diagonal B S hS _ f
    (relative_isClosedImmersion_diag_of_isAffineFormal B S hS hX)

/-- The relative diagonal of a morphism out of an affine formal algebraic space is representable
by objects of the site. -/
@[stacks 0AN2 "representable by schemes, for a morphism whose source is an affine formal \
algebraic space"]
theorem relativelyRepresentable_pullback_diagonal_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (pullback.diagonal f) :=
  (relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal B S hS f hX).rep

/-- Every represented base change of the relative diagonal of a morphism out of an affine formal
algebraic space is a locally quasi-finite, locally of finite type morphism of schemes. -/
@[stacks 0AN2 "locally quasi-finite, for a morphism whose source is an affine formal algebraic \
space"]
theorem relative_locallyQuasiFinite_pullback_diagonal_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_inverseImage_of_isClosedImmersion B S hS
    (by intros; exact ⟨inferInstance, inferInstance⟩)
    (pullback.diagonal f)
    (relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal B S hS f hX)

/-- Every represented base change of the relative diagonal of a morphism out of an affine formal
algebraic space is a locally of finite type morphism of schemes. -/
@[stacks 0AN2 "locally of finite type, for a morphism whose source is an affine formal \
algebraic space"]
theorem relative_locallyOfFiniteType_pullback_diagonal_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_inverseImage_of_isClosedImmersion B S hS (by intros; infer_instance)
    (pullback.diagonal f)
    (relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal B S hS f hX)

/-- Every represented base change of the relative diagonal of a morphism out of an affine formal
algebraic space is a separated morphism of schemes. -/
@[stacks 0AN2 "separated, for a morphism whose source is an affine formal algebraic space"]
theorem relative_isSeparated_pullback_diagonal_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_inverseImage_of_isClosedImmersion B S hS (by intros; infer_instance)
    (pullback.diagonal f)
    (relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal B S hS f hX)

/-- The relative diagonal of a morphism of fppf sheaves out of a formal algebraic space is a
monomorphism, which by **Stacks 0AQB** is the monomorphism condition for a morphism of formal
algebraic spaces. -/
@[stacks 0AN2 "monomorphism, for a morphism whose source is an arbitrary formal algebraic \
space"]
theorem mono_pullback_diagonal_of_isFormalAlgebraicSpace {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (_hX : IsFormalAlgebraicSpace B S hS X) : Mono (pullback.diagonal f) :=
  inferInstance

end AlgebraicGeometry.FormalSpace

add_to_stacks 0AN2 "monomorphism" CategoryTheory.Limits.pullback.instIsSplitMonoDiagonal

add_to_stacks 0AIP "monomorphism" CategoryTheory.Limits.instIsSplitMonoDiag

end
