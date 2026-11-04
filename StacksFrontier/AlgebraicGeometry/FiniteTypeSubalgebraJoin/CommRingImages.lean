module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images in the category of commutative rings

A morphism of commutative rings factors as a surjection onto its range followed by the
inclusion of that range, and this factorisation is the categorical image: it is least among
all factorisations of the morphism through a monomorphism. Hence `CommRingCat` has images.

## Main definitions

* `Stacks.CommRingImages.monoFactorisation`: the factorisation of a ring morphism through its
  range.
* `Stacks.CommRingImages.liftHom`: the comparison morphism from the range to the middle object
  of an arbitrary mono factorisation.
* `Stacks.CommRingImages.isImage`: the range factorisation is the image.

## Main results

* `Stacks.CommRingImages.hasImages`: `CommRingCat` has images.

## Implementation notes

`liftHom` is the only place a choice is made.  A point of the range has a preimage, and
`liftFun` sends it to the image of a chosen one under `F'.e`.  Nothing about the choice survives:
`m_liftFun` pins the composite with `F'.m` to be the inclusion, and since `F'.m` is injective
every ring axiom for `liftFun` follows from the corresponding axiom in the target.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CommRingImages

variable {R S : CommRingCat.{u}}

/-- The factorisation of a morphism of commutative rings through its range: the surjection onto
the range followed by the inclusion of the range as a subring of the target. -/
def monoFactorisation (f : R ⟶ S) : MonoFactorisation f where
  I := CommRingCat.of f.hom.range
  m := CommRingCat.ofHom f.hom.range.subtype
  m_mono := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  e := CommRingCat.ofHom f.hom.rangeRestrict
  fac := by ext x; rfl

/-- The middle object of `monoFactorisation f` is the range of `f`. -/
@[simp]
theorem monoFactorisation_I (f : R ⟶ S) :
    (monoFactorisation f).I = CommRingCat.of f.hom.range :=
  rfl

variable (f : R ⟶ S) (F' : MonoFactorisation f)

/-- The underlying function of the comparison morphism out of the range: a point of the range is
sent to the image under `F'.e` of a chosen preimage of it. -/
noncomputable def liftFun (y : f.hom.range) : F'.I :=
  F'.e.hom (RingHom.mem_range.mp y.2).choose

/-- The comparison function composed with the monomorphism of the factorisation is the inclusion
of the range. -/
theorem m_liftFun (y : f.hom.range) : F'.m.hom (liftFun f F' y) = y.val := by
  exact (ConcreteCategory.congr_hom F'.fac _).trans (RingHom.mem_range.mp y.2).choose_spec

/-- The comparison ring homomorphism from the range of `f` to the middle object of a mono
factorisation `F'` of `f`, with underlying function `liftFun f F'`. -/
noncomputable def liftHom : f.hom.range →+* F'.I where
  toFun := liftFun f F'
  map_one' := ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
    (by rw [m_liftFun, map_one]; rfl)
  map_mul' a b := ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
    (by rw [m_liftFun, map_mul, m_liftFun, m_liftFun]; rfl)
  map_zero' := ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
    (by rw [m_liftFun, map_zero]; rfl)
  map_add' a b := ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
    (by rw [m_liftFun, map_add, m_liftFun, m_liftFun]; rfl)

/-- **The range factorisation of a morphism of commutative rings is its image.** -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift F' := CommRingCat.ofHom (liftHom f F')
  lift_fac F' := by ext y; exact m_liftFun f F' y

/-- A morphism of commutative rings has an image. -/
instance hasImage (f : R ⟶ S) : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

/-- **The category of commutative rings has images.** -/
instance hasImages : HasImages CommRingCat.{u} where
  has_image f := hasImage f

end Stacks.CommRingImages
