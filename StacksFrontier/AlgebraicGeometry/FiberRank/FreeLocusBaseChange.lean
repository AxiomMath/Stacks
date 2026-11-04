module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
import StacksCore.Tactic.StacksAttribute

/-!
# The free locus of a finitely presented flat module and base change

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation and let `F` be a
finitely presented `𝒪_X`-module which is flat over `S`. The set of points of `X` at which `F`
is free of finite rank on a neighbourhood is open, and its formation commutes with an arbitrary
base change `S' ⟶ S`. This is Stacks Tag 0CZR.

Openness is immediate from the shape of the condition. For base change, the free locus is
identified with the locus where `F` is flat *over `X` itself*, that is over the identity
morphism of `X`: freeness on a neighbourhood gives a free, hence flat, stalk, which is flatness
over the identity by `AlgebraicGeometry.isFlatOverAt_id_iff`; conversely flatness over the
identity feeds Stacks Tag 080Q at the identity morphism, whose fibre hypothesis holds because
the local ring of the fibre of `𝟙 X` through `x` is the residue field `κ(x)`. The relative flat
locus commutes with arbitrary base change by Stacks Tag 05VJ, which applied to the pair
`𝟙 X, f` gives the assertion for the free locus.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.freeLocus` is the set of points admitting a neighbourhood
  on which the module is free of finite rank.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isOpen_freeLocus`: **Stacks Tag 0CZR (openness).**
* `AlgebraicGeometry.Scheme.Modules.mem_freeLocus_iff_isFlatOverAt_id`: the free locus of a
  finitely presented module is the locus where it is flat over the identity of `X`.
* `AlgebraicGeometry.Scheme.Modules.freeLocus_pullback`: **Stacks Tag 0CZR (base change).**

## Implementation notes

The free neighbourhood is taken against `SheafOfModules.free (ULift (Fin n))`, which is the
shape in which Stacks Tag 080Q delivers it, so that the rank is a natural number.

The stalk of a module free on a neighbourhood is read off through
`Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv`, whose input is a family of generating
sections of `F.over U` with invertible structure map; such a family is produced from the
trivialising isomorphism by
`AlgebraicGeometry.SheafOfModules.isIso_free_generatingSections_ofEpi_π`. The stalk module
structure is fixed to `Stacks.Flatness.stalkModule` before that equivalence is obtained, since
that is the structure in which `AlgebraicGeometry.isFlatOverAt_id_iff` phrases flatness.

The fibre of an isomorphism `f` through `x` maps isomorphically to `Spec κ(f x)`, being the
second projection of a pullback along an isomorphism; since every point of the spectrum of a
local ring with trivial maximal ideal is its closed point, the local ring of that fibre is
`κ(f x)`, a field. This is `isField_stalk_fiber_of_isIso`, used at `f = 𝟙 X`.

## References

* [Stacks Project, Tag 0CZR](https://stacks.math.columbia.edu/tag/0CZR)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 05VJ](https://stacks.math.columbia.edu/tag/05VJ)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The set of points of `X` at which a sheaf of `𝒪_X`-modules is free of finite rank on an open
neighbourhood. -/
public def freeLocus {X : Scheme.{u}} (F : X.Modules) : Set X :=
  {x | ∃ U : X.Opens, x ∈ U ∧ ∃ n : ℕ,
    Nonempty (F.over U ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n)))}

/-- **Stacks Project, Tag 0CZR (openness).** The locus of points at which a sheaf of modules on
a scheme is free of finite rank on a neighbourhood is open: the trivialising neighbourhood of a
point of the locus is contained in the locus. -/
@[stacks 0CZR "openness"]
public theorem isOpen_freeLocus {X : Scheme.{u}} (F : X.Modules) :
    IsOpen (freeLocus F) :=
  isOpen_iff_forall_mem_open.mpr fun _ hx => by
    obtain ⟨U, hxU, n, e⟩ := hx
    exact ⟨U, fun y hy => ⟨U, hy, n, e⟩, U.2, hxU⟩

/-- Flatness transported along an equality of the module structures involved. -/
private theorem flat_of_instance_eq {R N : Type u} [CommRing R] [AddCommGroup N]
    {i j : Module R N} (h : i = j) (hf : @Module.Flat R N _ _ i) :
    @Module.Flat R N _ _ j := by
  subst h; exact hf

/-- A module linearly equivalent to a free module of finitely supported functions is flat, with
the module structure on the source given explicitly rather than by instance search. -/
@[ega "III 6.5.10" "special case"]
private theorem flat_of_linearEquiv_finsupp {R N : Type u} [CommRing R] [AddCommGroup N]
    (i : Module R N) {ι : Type u}
    (e : @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ N (ι →₀ R) _ _ i _) :
    @Module.Flat R N _ _ i := by
  let := i
  exact Module.Flat.of_linearEquiv e

/-- The stalk module structure that `AlgebraicGeometry.isFlatOverAt_id_iff` phrases flatness in
is the one instance search finds for a module on a scheme. -/
private theorem flatness_stalkModule_eq {X : Scheme.{u}} (F : X.Modules) (x : X) :
    (Stacks.Flatness.stalkModule F x :
        Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) =
      AlgebraicGeometry.Scheme.Modules.moduleStalk F x :=
  rfl

/-- A module free of finite rank on a neighbourhood of `x` has a free, hence flat, stalk at `x`,
and that is flatness over the identity morphism of `X` at `x`. -/
private theorem isFlatOverAt_id_of_mem_freeLocus {X : Scheme.{u}} (F : X.Modules)
    (x : X) (hx : x ∈ freeLocus F) :
    AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom (𝟙 X)).toShHom F x := by
  obtain ⟨U, hxU, n, ⟨e⟩⟩ := hx
  have : IsIso ((_root_.SheafOfModules.free.generatingSections
      (ULift.{u} (Fin n))).ofEpi e.symm.hom).π :=
    AlgebraicGeometry.SheafOfModules.isIso_free_generatingSections_ofEpi_π
      (ULift.{u} (Fin n)) e.symm
  obtain ⟨le⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv U F
    ((_root_.SheafOfModules.free.generatingSections (ULift.{u} (Fin n))).ofEpi e.symm.hom) hxU
  refine (AlgebraicGeometry.isFlatOverAt_id_iff F x).mpr ?_
  exact flat_of_instance_eq (flatness_stalkModule_eq F x).symm
    (flat_of_linearEquiv_finsupp (AlgebraicGeometry.Scheme.Modules.moduleStalk F x) le)

/-- The local ring of the fibre of an isomorphism of schemes through a point is a field: that
fibre is carried isomorphically onto `Spec κ(f x)` by the second projection, and every point of
the spectrum of a local ring whose maximal ideal is trivial is its closed point. -/
private theorem isField_stalk_fiber_of_isIso {X S : Scheme.{u}} (f : X ⟶ S) [IsIso f] (x : X) :
    IsField (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) := by
  have hi : IsIso (f.fiberToSpecResidueField (f x)) :=
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))).isIso_snd_of_isIso
  have : IsIso ((f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)) :=
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap
      (f.fiberToSpecResidueField (f x))).mp hi).2 (f.asFiber x)
  have : IsIso (((f.fiberToSpecResidueField (f x)).toLRSHom.toShHom).hom.stalkMap
      (f.asFiber x)) :=
    inferInstanceAs (IsIso ((f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)))
  have hring : ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (f.asFiber x))) ≃+*
      ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    (asIso (((f.fiberToSpecResidueField (f x)).toLRSHom.toShHom).hom.stalkMap
      (f.asFiber x))).commRingCatIsoToRingEquiv
  have hclosed : (f.fiberToSpecResidueField (f x)) (f.asFiber x) =
      IsLocalRing.closedPoint (S.residueField (f x)) :=
    Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)
  have hfield : IsField (ToType ((Spec (S.residueField (f x))).presheaf.stalk
      ((f.fiberToSpecResidueField (f x)) (f.asFiber x)))) := by
    rw [hclosed]
    exact (stalkClosedPointIso (S.residueField (f x))).commRingCatIsoToRingEquiv.isField
      (Field.toIsField (S.residueField (f x)))
  exact hring.symm.toMulEquiv.isField hfield

/-- **The free locus of a finitely presented module is its flat locus over the identity.** A
module free of finite rank near `x` is flat over `𝟙 X` at `x`; conversely Stacks Tag 080Q
applied to `𝟙 X` turns flatness over `𝟙 X` at `x` into freeness of finite rank near `x`, the
fibre hypothesis of that tag holding because the local ring of the fibre of `𝟙 X` through `x`
is a field. -/
public theorem mem_freeLocus_iff_isFlatOverAt_id {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (x : X) :
    x ∈ freeLocus F ↔
      AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom (𝟙 X)).toShHom F x := by
  refine ⟨isFlatOverAt_id_of_mem_freeLocus F x, fun hflat => ?_⟩
  have hfp : AlgebraicGeometry.FinitePresentation (𝟙 X) :=
    AlgebraicGeometry.FinitePresentation.mk inferInstance inferInstance inferInstance
  have hfiber :
      let := Stacks.Flatness.stalkModule
        ((Scheme.Modules.pullback ((𝟙 X : X ⟶ X).fiberι ((𝟙 X : X ⟶ X) x))).obj F)
        ((𝟙 X : X ⟶ X).asFiber x)
      Module.Flat (ToType (((𝟙 X : X ⟶ X).fiber ((𝟙 X : X ⟶ X) x)).presheaf.stalk
          ((𝟙 X : X ⟶ X).asFiber x)))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((Scheme.Modules.pullback ((𝟙 X : X ⟶ X).fiberι ((𝟙 X : X ⟶ X) x))).obj
            F).val.presheaf ((𝟙 X : X ⟶ X).asFiber x))) := by
    let := Stacks.Flatness.stalkModule
      ((Scheme.Modules.pullback ((𝟙 X : X ⟶ X).fiberι ((𝟙 X : X ⟶ X) x))).obj F)
      ((𝟙 X : X ⟶ X).asFiber x)
    let : Field (ToType (((𝟙 X : X ⟶ X).fiber ((𝟙 X : X ⟶ X) x)).presheaf.stalk
        ((𝟙 X : X ⟶ X).asFiber x))) := (isField_stalk_fiber_of_isIso (𝟙 X) x).toField
    infer_instance
  obtain ⟨U, hxU, n, hU⟩ :=
    exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk (𝟙 X) hfp F x hflat hfiber
  exact ⟨U, hxU, n, hU⟩

/-- **Stacks Project, Tag 0CZR (base change).** Let `f : X ⟶ S` be locally of finite presentation
and let `F` be a finitely presented `𝒪_X`-module flat over `S`. The formation of the locus of
points at which `F` is free of finite rank on a neighbourhood commutes with an arbitrary base
change `g : S' ⟶ S`: the locus of the pulled-back module is the preimage of the original locus
under the projection. -/
@[stacks 0CZR "base change"]
public theorem freeLocus_pullback {X S S' : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsFinitePresentation] [LocallyOfFinitePresentation f]
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (g : S' ⟶ S) :
    freeLocus ((Scheme.Modules.pullback (pullback.fst f g)).obj F) =
      pullback.fst f g ⁻¹' freeLocus F := by
  have hid : (𝟙 X : X ⟶ X) ≫ f = f := Category.id_comp f
  have hfpRS : _root_.SheafOfModules.IsFinitePresentation
      (R := structureSheafRing X.toRingedSpace) F := ‹F.IsFinitePresentation›
  have hqcRS : _root_.SheafOfModules.IsQuasicoherent
      (R := structureSheafRing X.toRingedSpace) F :=
    _root_.isQuasicoherent_of_isFinitePresentation F
  have : LocallyOfFinitePresentation ((𝟙 X : X ⟶ X) ≫ f) := by rw [hid]; infer_instance
  have hfpP : ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation
      (pullback.fst f g).toLRSHom.toShHom F
  have hF' : AlgebraicGeometry.IsFlatOver ((𝟙 X : X ⟶ X) ≫ f).toLRSHom.toShHom F := by
    rw [hid]; exact hF
  have key := AlgebraicGeometry.setOf_isFlatOverAt_modulePullback_of_isFlatOver
    (IsPullback.of_hasPullback f g)
    (IsPullback.of_id_snd (f := Limits.pullback.fst f g)) F hF'
  ext z
  rw [mem_freeLocus_iff_isFlatOverAt_id, Set.mem_preimage, mem_freeLocus_iff_isFlatOverAt_id]
  exact Set.ext_iff.mp key z

end AlgebraicGeometry.Scheme.Modules

end

end
