module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkPushforwardModule
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# The length of a module at a point is unchanged by a closed immersion

Let `i : Z ⟶ X` be a closed immersion, let `G` be an `𝒪_Z`-module and let `z : Z` with image
`x = i(z)`. The *length of `G` at `z`* is the length of the stalk `G_z` over the local ring
`𝒪_{Z,z}`, a value in `ℕ∞ = {0, 1, 2, …, ∞}`. This file proves that it agrees with the length
of `i_* G` at `x`, so that `G` has length `d` at `z` if and only if `i_* G` has length `d`
at `x`.

The proof has exactly two inputs. On the image of an inducing map the stalk of a direct image
is the stalk itself, `(i_* G)_{x} ≅ (𝒪_{X,x} → 𝒪_{Z,z})^* (G_z)`, which is
`Stacks.ClosedImmersion.stalkPushforwardModuleIso`; and the germ map `𝒪_{X,x} → 𝒪_{Z,z}` of a
closed immersion is surjective, so restricting scalars along it does not change the lattice of
submodules and hence not its Krull dimension, which is the length.

## Main results

* `Stacks.ClosedImmersion.length_restrictScalars_obj_of_surjective`: restriction of scalars
  along a surjective ring homomorphism preserves the length of a module.
* `Stacks.ClosedImmersion.surjective_stalkRingMap_of_surjective_stalkMap`: the `RingCat`-valued
  germ map of a morphism of ringed spaces is surjective as soon as the `CommRingCat`-valued one
  is.
* `Stacks.ClosedImmersion.length_stalkObj_modulePushforward`: the length of `i_* G` at the
  image of `z` equals the length of `G` at `z`, for a morphism of ringed spaces whose base map
  is inducing and whose germ map on structure sheaves at `z` is surjective.
* `Stacks.ClosedImmersion.length_stalkObj_pushforward` and
  `Stacks.ClosedImmersion.length_stalkObj_pushforward_eq_iff`: the same equality, and the
  equivalence it gives for a value `d : ℕ∞`, for a closed immersion of schemes, where both
  hypotheses hold automatically.

## Implementation notes

The statement is proved for a morphism of ringed spaces and then specialised to schemes, rather
than proved for schemes directly: the stalk comparison it rests on is a statement about ringed
spaces, and the hypotheses it needs of a closed immersion of schemes — that the base map is a
closed embedding, hence inducing, and that the germ maps are surjective — are precisely the two
fields of `AlgebraicGeometry.IsClosedImmersion`. No scheme-theoretic input beyond those two is
used, and in particular the module is an arbitrary `𝒪_Z`-module and is not assumed
quasi-coherent.

Everything in sight is stated for the `RingCat`-valued structure sheaf `structureSheafRing`,
which is what `SheafOfModules` and hence `AlgebraicGeometry.Scheme.Modules` are stated over; the
`CommRingCat`-valued germ map `PresheafedSpace.Hom.stalkMap`, which is what
`AlgebraicGeometry.IsClosedImmersion` speaks about, is matched to it by
`Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso`. For a scheme `Z` the two spellings
`Z.Modules` and `SheafOfModules (structureSheafRing Z.toRingedSpace)` of the category of
modules, and the two spellings `AlgebraicGeometry.Scheme.Modules.pushforward i` and
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom` of the direct image, agree
definitionally, so the scheme statements are about Mathlib's own direct image of modules on
schemes.

The length of a module over a not-necessarily-commutative ring is available, and the stalk of
`structureSheafRing` carries only a `Ring` instance, so the restriction-of-scalars comparison is
proved here for `Ring`s rather than reusing `length_restrictScalars_eq_of_surjective`, which is
stated for `CommRing`s.

This is Stacks 0EE3 for a closed immersion of schemes. The source states it for a closed
immersion of algebraic spaces, with the length taken at a geometric point over the given point
of `|Y|`; see the note on the tag below.

## References

* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 00IX](https://stacks.math.columbia.edu/tag/00IX)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- **Restriction of scalars along a surjection preserves length.** For a surjective ring
homomorphism `φ : R → S` and an `S`-module `M`, the `R`-submodules of `M` obtained by
restricting scalars along `φ` are exactly the `S`-submodules of `M`, since the operators
`r • -` are the operators `φ r • -` and every `s • -` is of that form. The two submodule
lattices are therefore order isomorphic, and the length — the Krull dimension of the submodule
lattice — is the same.

This is Stacks 00IX, part (2) read for `ModuleCat.restrictScalars` and for rings that are not
assumed commutative; `length_restrictScalars_eq_of_surjective` is the commutative form. -/
theorem length_restrictScalars_obj_of_surjective {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars φ).obj M) = Module.length S M := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  exact
    { toFun := fun N =>
        { carrier := {m : M | m ∈ N}
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun s m hm => by
            obtain ⟨r, rfl⟩ := hφ s
            exact N.smul_mem r hm }
      invFun := fun N =>
        { carrier := {m : ((ModuleCat.restrictScalars φ).obj M) | m ∈ N}
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun r m hm => N.smul_mem (φ r) hm }
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl
      map_rel_iff' := Iff.rfl }

/-- **The two germ maps of a morphism of ringed spaces have the same surjectivity.** The
`RingCat`-valued germ map `Stacks.RingedSpace.stalkRingMap i z` and the `CommRingCat`-valued
`PresheafedSpace.Hom.stalkMap i.hom z` differ by the isomorphisms
`Stacks.RingedSpace.ringStalkCommIso` on either side, so surjectivity of the latter gives
surjectivity of the former. -/
theorem surjective_stalkRingMap_of_surjective_stalkMap {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (z : Z.carrier)
    (h : Function.Surjective (PresheafedSpace.Hom.stalkMap i.hom z).hom) :
    Function.Surjective (Stacks.RingedSpace.stalkRingMap i z).hom := by
  have hZ := ConcreteCategory.bijective_of_isIso (Stacks.RingedSpace.ringStalkCommIso Z z).hom
  have hX := (ConcreteCategory.bijective_of_isIso (Stacks.RingedSpace.ringStalkCommIso X
    (ConcreteCategory.hom i.hom.base z)).hom).2
  intro b
  obtain ⟨a', ha'⟩ := h ((Stacks.RingedSpace.ringStalkCommIso Z z).hom.hom b)
  obtain ⟨a, ha⟩ := hX a'
  refine ⟨a, hZ.1 ?_⟩
  have key := ConcreteCategory.congr_hom
    (Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso i z) a
  simp only [RingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at key
  rw [key, ha]
  exact ha'

/-- **The length of a direct image at a point of the image.** Let `i : Z ⟶ X` be a morphism of
ringed spaces whose underlying continuous map is inducing, let `z : Z`, and suppose the germ map
`𝒪_{X,i(z)} → 𝒪_{Z,z}` is surjective. Then for every `𝒪_Z`-module `G` the length of the stalk
of `i_* G` at `i(z)` over `𝒪_{X,i(z)}` equals the length of the stalk of `G` at `z` over
`𝒪_{Z,z}`.

The stalk of `i_* G` at `i(z)` is the stalk of `G` at `z` with scalars restricted along the
germ map (`Stacks.ClosedImmersion.stalkPushforwardModuleIso`), and the length is unchanged by
restriction of scalars along a surjection. -/
theorem length_stalkObj_modulePushforward {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (z : Z.carrier) (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (hs : Function.Surjective (Stacks.RingedSpace.stalkRingMap i z).hom)
    (G : SheafOfModules.{u} (structureSheafRing Z)) :
    Module.length
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj
          (ConcreteCategory.hom i.hom.base z))
        (SheafOfModules.stalkObj (structureSheafRing X) (ConcreteCategory.hom i.hom.base z)
          ((modulePushforward i).obj G)) =
      Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing Z).obj z)
        (SheafOfModules.stalkObj (structureSheafRing Z) z G) := by
  rw [(stalkPushforwardModuleIso i z hi G).toLinearEquiv.length_eq]
  exact length_restrictScalars_obj_of_surjective _ hs _

/-- **Stacks 0EE3 for a closed immersion of schemes.** Let `i : Z ⟶ X` be a closed immersion of
schemes, let `G` be an `𝒪_Z`-module and let `z : Z` with image `i(z)` in `X`. The length of the
stalk of `i_* G` at `i(z)` over `𝒪_{X,i(z)}` equals the length of the stalk of `G` at `z` over
`𝒪_{Z,z}`.

Both hypotheses of `Stacks.ClosedImmersion.length_stalkObj_modulePushforward` are fields of
`AlgebraicGeometry.IsClosedImmersion`: the base map is a closed embedding, hence inducing, and
the germ maps are surjective. -/
theorem length_stalkObj_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Z.Modules) (z : Z) :
    Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj (i.base z))
        (SheafOfModules.stalkObj X.ringCatSheaf (i.base z)
          ((Scheme.Modules.pushforward i).obj G)) =
      Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) Z.ringCatSheaf.obj z)
        (SheafOfModules.stalkObj Z.ringCatSheaf z G) :=
  length_stalkObj_modulePushforward i.toLRSHom.toShHom z
    i.isClosedEmbedding.isInducing
    (surjective_stalkRingMap_of_surjective_stalkMap _ _ (i.stalkMap_surjective z)) G

/-- **Stacks 0EE3 for a closed immersion of schemes**, in the form the source states: for
`d ∈ {0, 1, 2, …, ∞}`, the module `G` has length `d` at `z` if and only if `i_* G` has length
`d` at the image `i(z)`.

Both sides are read off `Stacks.ClosedImmersion.length_stalkObj_pushforward`, which says the
two lengths are equal. -/
@[stacks 0EE3 "for a closed immersion of schemes"]
theorem length_stalkObj_pushforward_eq_iff {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Z.Modules) (z : Z) (d : ℕ∞) :
    Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) Z.ringCatSheaf.obj z)
          (SheafOfModules.stalkObj Z.ringCatSheaf z G) = d ↔
      Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj (i.base z))
          (SheafOfModules.stalkObj X.ringCatSheaf (i.base z)
            ((Scheme.Modules.pushforward i).obj G)) = d := by
  rw [length_stalkObj_pushforward i G z]

end Stacks.ClosedImmersion

end
