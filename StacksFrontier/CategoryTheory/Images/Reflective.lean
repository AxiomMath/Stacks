module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Images in a reflective subcategory

If `i : D ⥤ C` is fully faithful with a left adjoint `L`, the category `C` has images, and `L`
preserves monomorphisms, then `D` has images: the image of `f : X ⟶ Y` in `D` is the reflection
`L.obj (image (i.map f))` of the image of `f` read in `C`.

Both halves of the statement use one of the two hypotheses on the adjunction and nothing else.
The factorisation needs `L` to preserve monomorphisms, so that the reflected inclusion is still
a monomorphism; the universal property needs `i` to preserve monomorphisms, so that an arbitrary
mono factorisation in `D` can be read in `C` and compared with the image there.  The second is
automatic -- a right adjoint preserves limits, and being a monomorphism is a limit condition --
which is why only the first appears as a hypothesis of `hasImages_of_reflective`.  Full
faithfulness of `i` enters only through the counit of the adjunction being an isomorphism, which
is what identifies `L.obj (i.obj X)` with `X`.

## Main definitions

* `Stacks.ReflectiveImages.mapMonoFactorisation`: a mono factorisation in `D`, read in `C`.
* `Stacks.ReflectiveImages.monoFactorisation`: the reflection of the image factorisation of
  `i.map f`, as a mono factorisation of `f`.
* `Stacks.ReflectiveImages.isImage`: that factorisation is the image.

## Main results

* `Stacks.ReflectiveImages.preservesMonomorphisms_of_isRightAdjoint`: a functor with a left
  adjoint preserves monomorphisms.
* `Stacks.ReflectiveImages.hasImages_of_reflective`: `D` has images.

## Implementation notes

`preservesMonomorphisms_of_isRightAdjoint` is stated for a given adjunction rather than for
`CategoryTheory.Functor.IsRightAdjoint`, and it is deliberately *not* an instance: it would
have to guess the left adjoint.  It is introduced with `haveI` at the one place it is needed, in
`hasImages_of_reflective`, and the construction section takes
`CategoryTheory.Functor.PreservesMonomorphisms i` as a hypothesis instead.

`mapMonoFactorisation` is `@[reducible]`.  As in `Stacks.FunctorImages` this is load-bearing:
`CategoryTheory.Limits.image.lift (mapMonoFactorisation F')` has
`(mapMonoFactorisation F').I` in its type, which is `i.obj F'.I` only after the definition is
unfolded, and `rw` elaborates its congruence motive at a transparency that does not unfold a
semireducible definition.

The counit appears in both legs of `monoFactorisation`, on the right of the monomorphism and
inverted on the left of the epimorphism-like leg, and `fac` is then exactly the naturality
square `CategoryTheory.Adjunction.counit_naturality` of the counit at `f`.  The universal
property is the same square at `F'.m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.ReflectiveImages

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {i : D ⥤ C}

/-- A functor with a left adjoint preserves monomorphisms: it preserves all limits, and being a
monomorphism is the statement that a certain cospan has a pullback of a particular shape. -/
@[sga "4 I 6.2" "(ii), special case"]
theorem preservesMonomorphisms_of_isRightAdjoint (adj : L ⊣ i) : i.PreservesMonomorphisms :=
  have := adj.rightAdjoint_preservesLimits.{0, 0}
  preservesMonomorphisms_of_preservesLimitsOfShape i

section Construction

variable [i.Full] [i.Faithful] [i.PreservesMonomorphisms] [HasImages C]
  [L.PreservesMonomorphisms]

/-- An arbitrary mono factorisation of a morphism of `D`, read in `C` along the right adjoint.
Its middle morphism is still a monomorphism because `i` preserves monomorphisms. -/
@[reducible]
def mapMonoFactorisation {X Y : D} {f : X ⟶ Y} (F' : MonoFactorisation f) :
    MonoFactorisation (i.map f) where
  I := i.obj F'.I
  m := i.map F'.m
  m_mono := i.map_mono F'.m
  e := i.map F'.e
  fac := by rw [← i.map_comp, F'.fac]

/-- **The reflection of the image factorisation of `i.map f`, as a factorisation of `f`.**  The
two legs are the reflections of the two legs of the image factorisation in `C`, corrected by the
counit isomorphism of the adjunction at the source and at the target. -/
noncomputable def monoFactorisation (adj : L ⊣ i) {X Y : D} (f : X ⟶ Y) :
    MonoFactorisation f where
  I := L.obj (image (i.map f))
  m := L.map (image.ι (i.map f)) ≫ adj.counit.app Y
  m_mono := mono_comp _ _
  e := inv (adj.counit.app X) ≫ L.map (factorThruImage (i.map f))
  fac := by
    rw [Category.assoc, ← Category.assoc (L.map (factorThruImage (i.map f))), ← L.map_comp,
      image.fac, adj.counit_naturality, IsIso.inv_hom_id_assoc]

/-- **The reflected image factorisation is the image.**  The comparison morphism is the
reflection of the comparison morphism in `C`, again corrected by the counit. -/
noncomputable def isImage (adj : L ⊣ i) {X Y : D} (f : X ⟶ Y) :
    IsImage (monoFactorisation adj f) where
  lift F' := L.map (image.lift (mapMonoFactorisation F')) ≫ adj.counit.app F'.I
  lift_fac F' := by
    have h : image.lift (mapMonoFactorisation F') ≫ i.map F'.m = image.ι (i.map f) :=
      image.lift_fac (mapMonoFactorisation F')
    have hn : adj.counit.app F'.I ≫ F'.m = L.map (i.map F'.m) ≫ adj.counit.app Y :=
      (adj.counit_naturality F'.m).symm
    change (L.map (image.lift (mapMonoFactorisation F')) ≫ adj.counit.app F'.I) ≫ F'.m
      = L.map (image.ι (i.map f)) ≫ adj.counit.app Y
    rw [Category.assoc, hn, ← Category.assoc, ← L.map_comp, h]

/-- Every morphism of `D` has an image. -/
theorem hasImage (adj : L ⊣ i) {X Y : D} (f : X ⟶ Y) : HasImage f :=
  HasImage.mk ⟨_, isImage adj f⟩

end Construction

/-- **A reflective subcategory of a category with images has images, provided the reflector
preserves monomorphisms.** -/
theorem hasImages_of_reflective (adj : L ⊣ i) [i.Full] [i.Faithful] [HasImages C]
    [L.PreservesMonomorphisms] : HasImages D :=
  have := preservesMonomorphisms_of_isRightAdjoint adj
  { has_image := fun f => hasImage adj f }

end Stacks.ReflectiveImages
