module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData

/-!
# The canonical descent datum of a scheme, relative to a family of morphisms

Let `S` be a scheme and let `{X i ⟶ S}` be a family of morphisms with target `S`. A scheme `U`
over `S` carries a trivial descent datum relative to the family of identities of `S`; pulling
that datum back along the morphism of families `{X i ⟶ S} ⟶ {𝟙 S}` gives the *canonical*
descent datum of `U` relative to `{X i ⟶ S}`, whose member over `X i` is `X i ×_S U`. A descent
datum relative to the family is *effective* when it is isomorphic to a canonical one.

For a *single* morphism these are `AlgebraicGeometry.DescentData.trivialFunctor` and its pullback
(Stacks 023Z); this file constructs them for a family (Stacks 02VU), the setting of the effectivity
statements for families, Stacks 0245, 0247, 02W0 and 02W3.

## Main definitions

* `AlgebraicGeometry.DescentData.trivialFamilyFunctor` sends a scheme over `S` to its trivial
  descent datum relative to a constant family of identities of `S`. It generalizes
  `AlgebraicGeometry.DescentData.trivialFunctor` from a one-member family to an arbitrary one;
  see `AlgebraicGeometry.DescentData.trivialFunctor_eq_trivialFamilyFunctor`.
* `AlgebraicGeometry.DescentData.toIdFamily` is the morphism of families from `{X i ⟶ S}` to the
  family of identities of `S` indexed by the same type, whose component at `i` is `X i ⟶ S`
  itself.
* `AlgebraicGeometry.DescentData.canonicalFamilyFunctor` sends a scheme over `S` to its
  canonical descent datum relative to `{X i ⟶ S}`.
* `AlgebraicGeometry.DescentData.IsEffectiveFamily` says that a descent datum relative to a
  family is isomorphic to a canonical one.

## Main results

* `AlgebraicGeometry.DescentData.trivialFunctor_eq_trivialFamilyFunctor`: the one-member case of
  the trivial-datum functor is the existing one, on the nose.
* `AlgebraicGeometry.DescentData.canonicalFamilyFunctor_obj_obj`: the member of the canonical
  descent datum over `X i` is the base change of `U` along `X i ⟶ S`.
* `AlgebraicGeometry.DescentData.isEffectiveFamily_canonicalFamilyFunctor`: a canonical descent
  datum is effective.

## Implementation notes

*The index universe.* `AlgebraicGeometry.DescentData` lets the index type of the family live in
its own universe, and `trivialFamilyFunctor` is stated there. The canonical datum, however, is
built from `AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackFunctor`, and a
`AlgebraicGeometry.MorphismOfSchemeFamilies` carries its families as
`CategoryTheory.PreZeroHypercover` objects indexed in the universe of the schemes. So
`canonicalFamilyFunctor` and `IsEffectiveFamily` are stated for `ι : Type u` with
`S : Scheme.{u}`. This is the same restriction the pullback functor of Stacks 02VT already
carries, and it is no restriction for the coverings of the fpqc precoverage, whose index types
are of that universe.

*Why the trivial datum is taken over a constant family rather than a singleton.* The source
pulls back the trivial datum of the singleton family `{𝟙 S}` along a morphism of families whose
index map is constant. Taking instead the family of identities indexed by `ι` and the identity
index map gives the same descent datum — the gluing isomorphism of the trivial datum is the
symmetry of the product at every pair of indices, so re-indexing does not change it — and it
avoids a `ULift` on the index type of the singleton family, which is what
`AlgebraicGeometry.DescentData.pullbackFunctor` has to transport along.

*The orientation of the fibre product.* The member of the canonical datum over `X i` is
`CategoryTheory.Over.pullback (f i) |>.obj U`, whose underlying scheme is `U ×_S X i` viewed
over `X i`, where the source writes `X i ×_S U`. The two differ by the symmetry of the fibre
product only.

## References

* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VT](https://stacks.math.columbia.edu/tag/02VT)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.DescentData

/-- The functor sending a scheme over `S` to its trivial descent datum relative to the constant
family of identities of `S` indexed by `ι`: the member over each index is the scheme itself, and
the gluing isomorphism is the symmetry of the product. -/
@[implicit_reducible]
def trivialFamilyFunctor (S : Scheme.{u}) (ι : Type v) :
    Over S ⥤ DescentData (S := S) (X := fun _ : ι ↦ S) (fun _ ↦ 𝟙 S) where
  obj U :=
    { obj := fun _ ↦ U
      gluing := fun _ _ ↦ Over.isoMk (prod.braiding _ _) (by
        apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext)
      cocycle := by
        intros
        apply prod.hom_ext
        · apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird] }
  map g :=
    { hom := fun _ ↦ g
      comm := by intros; simp }
  map_id U := by ext; simp
  map_comp g h := by ext; simp

/-- The trivial-datum functor `trivialFunctor S` is the trivial-datum functor of the one-member
family of identities of `S`. -/
lemma trivialFunctor_eq_trivialFamilyFunctor (S : Scheme.{u}) :
    trivialFunctor S = trivialFamilyFunctor S Unit := rfl

variable {ι : Type u} {S : Scheme.{u}} {X : ι → Scheme.{u}}

/-- The morphism of families from `{X i ⟶ S}` to the family of identities of `S` indexed by the
same type: the index map is the identity, and the component at `i` is the morphism `X i ⟶ S`
itself. -/
def toIdFamily (f : ∀ i, X i ⟶ S) : MorphismOfSchemeFamilies.{u} where
  sourceBase := S
  targetBase := S
  sourceFamily := { I₀ := ι, X := X, f := f }
  targetFamily := { I₀ := ι, X := fun _ ↦ S, f := fun _ ↦ 𝟙 S }
  baseHom := 𝟙 S
  familyHom := { s₀ := id, h₀ := f, w₀ := fun _ ↦ by simp }

/-- **The canonical descent datum relative to a family.** The functor sending a scheme `U` over
`S` to the descent datum relative to `{X i ⟶ S}` whose member over `X i` is the base change of
`U` along `X i ⟶ S`, obtained by pulling back the trivial descent datum of `U`. -/
@[stacks 02VU "(1) canonical descent datum on the family X i ×_S U", implicit_reducible]
def canonicalFamilyFunctor (f : ∀ i, X i ⟶ S) : Over S ⥤ DescentData f :=
  trivialFamilyFunctor S ι ⋙ (MorphismOfSchemeFamilies.pullbackFunctor (toIdFamily f)).functor

/-- The member of the canonical descent datum of `U` over `X i` is the base change of `U` along
`X i ⟶ S`. -/
lemma canonicalFamilyFunctor_obj_obj (f : ∀ i, X i ⟶ S) (U : Over S) (i : ι) :
    ((canonicalFamilyFunctor f).obj U).obj i = (Over.pullback (f i)).obj U :=
  rfl

/-- **Effectivity of a descent datum relative to a family.** A descent datum relative to
`{X i ⟶ S}` is effective if it is isomorphic to the canonical descent datum of a scheme over
`S`. -/
@[stacks 02VU "(2) effective descent datum relative to a family", sga "3 IV 3.5.1"]
abbrev IsEffectiveFamily {f : ∀ i, X i ⟶ S} (D : DescentData f) : Prop :=
  (canonicalFamilyFunctor f).essImage D

/-- The canonical descent datum of a scheme over `S` is effective. -/
lemma isEffectiveFamily_canonicalFamilyFunctor (f : ∀ i, X i ⟶ S) (U : Over S) :
    IsEffectiveFamily ((canonicalFamilyFunctor f).obj U) :=
  (canonicalFamilyFunctor f).obj_mem_essImage U

end AlgebraicGeometry.DescentData
