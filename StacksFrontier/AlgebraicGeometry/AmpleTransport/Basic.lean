module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness under an isomorphism of schemes

An invertible sheaf on a scheme is ample when every point lies in an affine nonvanishing locus of
a global section of some positive tensor power of the sheaf, and the scheme is quasi-compact.
This file transports that property along an isomorphism of schemes and along an isomorphism of
invertible sheaves, and in doing so identifies the pullback of a tensor power with the tensor
power of the pullback.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorPowerCongr`: isomorphic invertible sheaves have
  isomorphic tensor powers, in every nonnegative exponent.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`: the pullback of a nonnegative tensor
  power of an invertible sheaf is the corresponding tensor power of its pullback.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonvanishingOpen_pullbackTensorPowerIso`: the nonvanishing
  locus of a pulled-back section of a nonnegative tensor power is the preimage of the
  nonvanishing locus, for an arbitrary morphism of schemes.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_iso`: ampleness depends only on the isomorphism
  class of the invertible sheaf.
* `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso`: the pullback of an ample
  invertible sheaf along an isomorphism of schemes is ample.
* `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_isIso`: the existence of an ample
  invertible sheaf transports along an isomorphism of schemes.
* `AlgebraicGeometry.Scheme.Modules.exists_isAmple_pullback_comm`: the two factors of a fibre
  product may be taken in either order without affecting whether it carries an ample invertible
  sheaf.

## Implementation notes

Both isomorphisms of tensor powers are built by induction on the exponent, over `ℕ` rather than
over `ℤ`, from the successor comparison
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso`. The nonnegative exponents are all that
`AlgebraicGeometry.Scheme.Modules.IsAmple` quantifies over, and the induction is available there
and not for negative exponents: a negative power is the image of the structure sheaf under the
chosen *quasi-inverse* of the autoequivalence given by tensoring, and commuting a pullback past a
chosen quasi-inverse is a statement about the mate of
[Stacks, Tag 01CD] that this repository does not have.

The two steps of the induction are the only inputs. For `tensorPowerCongr`, tensoring is
functorial in each argument separately, and both one-variable functors are read off the curried
tensor bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`: tensoring on the right by `L` is
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L` and tensoring on the left by `A` is
`(Stacks.SheafOfModules.Tensor.sheafTensor _).obj A`. The value of the first at `A` and of the
second at `L` are both `((Stacks.SheafOfModules.Tensor.sheafTensor _).obj A).obj L`, which is the
spelling `Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` is stated at, so no comparison has
to be built. For `pullbackTensorPowerIso` the base case is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` — the zeroth power is the structure sheaf
by definition — and the successor step is
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`, which is [Stacks, Tag 01CD] for a
morphism of schemes and is unconditional.

Ampleness itself transports because its three ingredients do: the nonvanishing locus of the image
of a section under an isomorphism of sheaves is unchanged
(`Stacks.SheafOfModules.nonvanishingLocus_sectionsMap`), the nonvanishing locus of a pulled-back
section is the preimage of the nonvanishing locus
(`Stacks.SheafOfModules.preimage_nonvanishingOpen`, [Stacks, Tag 0H78]), and the preimage of an
affine open along an isomorphism is affine. The invertibility of the pullback, which the tensor
powers of the pullback need before they can be written down, is
`Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` of [Stacks, Tag 0B8L]; it is
not found by instance search and is supplied as an instance binder, which is harmless because
`AlgebraicGeometry.SheafOfModules.IsInvertible` is `Prop`-valued and therefore proof-irrelevant.

Isomorphism of schemes, rather than an arbitrary immersion, is the generality reached here. The
statement of [Stacks, Tag 0B3E] for a quasi-compact immersion needs the nonvanishing locus of the
restricted section to be affine, which is a further input and is not used by anything below.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible

universe u v w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : CategoryTheory.Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO M]

/-- Isomorphic invertible sheaves of modules have isomorphic tensor powers, in every nonnegative
exponent. The isomorphism is built by induction on the exponent: the zeroth powers are both the
structure sheaf, and the successor step tensors the previous comparison with the isomorphism
itself. -/
public def tensorPowerCongr (e : L ≅ M) : ∀ n : ℕ,
    tensorPower O hO L (n : ℤ) ≅ tensorPower O hO M (n : ℤ)
  | 0 => Iso.refl _
  | (n + 1) =>
      (tensorPowerSuccIso O hO L (n : ℤ)).symm ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
              (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).mapIso
          (tensorPowerCongr e n) ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
              (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO M (n : ℤ))).mapIso e ≪≫
        tensorPowerSuccIso O hO M (n : ℤ)

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)]

/-- The pullback of the `n`th tensor power of an invertible sheaf of modules is the `n`th tensor
power of its pullback, for every `n : ℕ`. The zeroth powers are the two structure sheaves, and
the successor step is [Stacks, Tag 01CD] for a morphism of schemes. -/
public def pullbackTensorPowerIso : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj
        (tensorPower Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property L (n : ℤ)) ≅
      tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        ((Scheme.Modules.pullback f).obj L) (n : ℤ)
  | 0 => AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f
  | (n + 1) =>
      (Scheme.Modules.pullback f).mapIso
          (tensorPowerSuccIso Y.toRingedSpace.presheaf
            (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).symm ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f _ L ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
              X.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
              (structureSheafRing X.toRingedSpace).property⟩).flip.obj
          ((Scheme.Modules.pullback f).obj L)).mapIso (pullbackTensorPowerIso n) ≪≫
        tensorPowerSuccIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback f).obj L) (n : ℤ)

/-- **The nonvanishing locus of a pulled-back section is the preimage of the nonvanishing
locus**, for a global section of a nonnegative tensor power. The section is pulled back and then
carried across `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`, which does not move its
nonvanishing locus; what remains is
`Stacks.SheafOfModules.preimage_nonvanishingOpen`, [Stacks, Tag 0H78].

The morphism is arbitrary: nothing here needs it to be an isomorphism, an immersion or affine. -/
@[ega "II 4.6.13.1" "(i)"]
public theorem nonvanishingOpen_pullbackTensorPowerIso (n : ℕ)
    (s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections) :
    Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback f).obj L) (n : ℤ))
        (SheafOfModules.sectionsMap (pullbackTensorPowerIso f L n).hom
          (Stacks.SheafOfModules.modulePullbackSection f.toLRSHom _ s)) =
      f ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property L (n : ℤ)) s :=
  (TopologicalSpace.Opens.ext (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap
    X.toRingedSpace (pullbackTensorPowerIso f L n) _)).trans
      (Stacks.SheafOfModules.preimage_nonvanishingOpen f _ s).symm

/-- The pullback of an ample invertible sheaf of modules along an isomorphism of schemes is
ample. Each witnessing section is pulled back and carried across
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`, which leaves its nonvanishing locus
the preimage of the original one
(`AlgebraicGeometry.Scheme.Modules.nonvanishingOpen_pullbackTensorPowerIso`), and the preimage of
an affine open along an isomorphism is affine. -/
public theorem isAmple_pullback_of_isIso [IsIso f] (h : IsAmple Y L) :
    IsAmple X ((Scheme.Modules.pullback f).obj L) := by
  refine ⟨?_, fun x => ?_⟩
  · have : CompactSpace Y := h.compactSpace
    exact (Scheme.Hom.homeomorph f).symm.compactSpace
  · obtain ⟨n, hn, s, hxs, haff⟩ := h.exists_affine_nonvanishingLocus (f.base x)
    have key := nonvanishingOpen_pullbackTensorPowerIso f L n s
    exact ⟨n, hn, SheafOfModules.sectionsMap (pullbackTensorPowerIso f L n).hom
      (Stacks.SheafOfModules.modulePullbackSection f.toLRSHom _ s), key.ge hxs,
      key ▸ haff.preimage_of_isIso f⟩

/-- Ampleness of an invertible sheaf of modules depends only on its isomorphism class. -/
public theorem isAmple_of_iso {Z : Scheme.{u}} {L M : Z.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property M]
    (e : L ≅ M) (h : IsAmple Z L) : IsAmple Z M := by
  refine ⟨h.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hxs, haff⟩ := h.exists_affine_nonvanishingLocus x
  have ep := Stacks.SheafOfModules.Invertible.tensorPowerCongr
    Z.toRingedSpace.presheaf (structureSheafRing Z.toRingedSpace).property L M e n
  have key : Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower Z.toRingedSpace.presheaf
          (structureSheafRing Z.toRingedSpace).property M (n : ℤ))
        (SheafOfModules.sectionsMap ep.hom s) =
      Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower Z.toRingedSpace.presheaf
          (structureSheafRing Z.toRingedSpace).property L (n : ℤ)) s :=
    TopologicalSpace.Opens.ext
      (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap Z.toRingedSpace ep s)
  exact ⟨n, hn, SheafOfModules.sectionsMap ep.hom s, key.ge hxs, key ▸ haff⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The existence of an ample invertible sheaf of modules transports along an isomorphism of
schemes: if the target of an isomorphism carries one, so does the source, namely the pullback.

This is the existential form of `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso`. It
is stated separately because the invertibility of the pullback is not found by instance search —
it is `Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` of [Stacks, Tag 0B8L],
supplied here by hand — so a consumer holding only an existential statement cannot write the
conclusion of the non-existential form down without first discharging that instance. -/
public theorem exists_isAmple_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (h : ∃ L : Y.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L,
      IsAmple Y L) :
    ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
      IsAmple X M := by
  obtain ⟨L, hL, hamp⟩ := h
  have i : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback g).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback g.toLRSHom.toShHom L
  exact ⟨_, i, isAmple_pullback_of_isIso g L hamp⟩

/-- The two factors of a fibre product may be written in either order without affecting whether
the fibre product carries an ample invertible sheaf. The two schemes are identified by
`CategoryTheory.Limits.pullbackSymmetry`, which is an isomorphism, so this is
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_isIso` in both directions.

The statement is needed because the base change of a scheme along a morphism has two equally
natural spellings, and a result proved at one of them does not apply at the other: ampleness is
not a property of a morphism but of a sheaf on its source, so there is no base-change formalism
to appeal to. -/
public theorem exists_isAmple_pullback_comm {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (∃ L : (Limits.pullback f g).Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        (Limits.pullback f g).toRingedSpace.presheaf
        (structureSheafRing (Limits.pullback f g).toRingedSpace).property L,
      IsAmple (Limits.pullback f g) L) ↔
    (∃ M : (Limits.pullback g f).Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        (Limits.pullback g f).toRingedSpace.presheaf
        (structureSheafRing (Limits.pullback g f).toRingedSpace).property M,
      IsAmple (Limits.pullback g f) M) :=
  ⟨exists_isAmple_of_isIso (Limits.pullbackSymmetry f g).inv,
    exists_isAmple_of_isIso (Limits.pullbackSymmetry f g).hom⟩

end AlgebraicGeometry.Scheme.Modules

end
