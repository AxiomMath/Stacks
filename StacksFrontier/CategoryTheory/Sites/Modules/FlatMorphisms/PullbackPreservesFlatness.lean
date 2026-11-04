module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of a flat sheaf of modules along a morphism of ringed topoi is flat

Let `f : (Sh(C), O_X) ⟶ (Sh(D), O_Y)` be a morphism of ringed topoi, presented by a continuous
functor `f.u : D.C ⥤ X.C` of the underlying sites which is a morphism of sites, and let `M` be a
flat sheaf of `O_Y`-modules.  Then the pullback `f^*M` is a flat `O_X`-module, where `f^*` is
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, the abstract left adjoint of the
pushforward.

## What was missing, and what closes it

Stacks 05VD is already proved for the pullback that Stacks 03D6 part (2) *constructs* from the
inverse image of Stacks 03D2, namely
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`.  It was **not** available for the
abstract left adjoint, and the two are identified only through a comparison of the transported
and the restriction direct images.  Of that comparison the geometric half is already in the
tree: `Stacks.Sheaves.InverseImageExactness.pullbackIsoInverseImageModules` identifies the
geometric factor `g^*` of the factorization `f^* ≅ g^* ⋙ h^*` with the inverse image of
sheaves of modules, read over `f⁻¹O_Y` through an isomorphism `ringCompare` of sheaves of
rings.  The change-of-rings factor `h^*` preserves flatness by Stacks 05V4
(`Stacks.Sheaves.DerivedPullback.FlatExtendScalars.isFlat_pullbackTopos_auxHomH`).

The one step that was absent is transporting flatness across `ringCompare`: *flatness over a
sheaf of commutative rings is invariant under restriction of scalars along an isomorphism.*
`restrictScalarsIsoExtendScalars` below supplies it, and it needs no new work on tensor
products — restriction of scalars along the inverse of an isomorphism **is** extension of
scalars along the isomorphism, both being left adjoint to restriction of scalars along it, so
the transport is one more application of Stacks 05V4.

## Main definitions

* `Stacks.SheafOfModules.FlatRingTransport.restrictScalarsIsoExtendScalars`: for an
  isomorphism `e` of sheaves of commutative rings, restriction of scalars along `e.inv` is
  extension of scalars along `e.hom`.

## Main results

* `Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso`: **flatness
  is invariant under transport along an isomorphism of structure sheaves.**
* `AlgebraicGeometry.RingedToposSiteHom.isFlat_inverseImageModules`: Stacks 05VD for the
  inverse image with no change of rings, at an arbitrary morphism of topoi between the two
  sheaf topoi.
* `AlgebraicGeometry.RingedToposSiteHom.isFlat_pullbackTopos_auxHomG`: the same for the
  geometric half `g^*` of the factorization of `f^*`.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat`: **Stacks 05VD for the
  abstract module pullback**, in the spelling
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` that Stacks 0G7E and
  Stacks 0G6R consume.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv`: its universally
  quantified form, which is what the reduction of Stacks 0G6R takes.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact`: **Stacks 0G6R with no
  hypothesis left over**, obtained from the previous result and
  `Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact`.

## Implementation notes

*Why the transport lemma is phrased with `restrictScalarsEquivalenceOfIso`.*  Its consumer,
`Stacks.Sheaves.InverseImageExactness.pullbackIsoInverseImageModules`, is stated with the
equivalence rather than with `SheafOfModules.restrictScalars` of the inverse, so the lemma is
stated at that spelling and no retyping intervenes at the point of use.

*No tag is placed in this file.*  Stacks 05VD already carries two part-qualified attributes —
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules` for the constructed pullback along a
morphism of ringed topoi and `Stacks.ModuleUp.isFlat_pullback` for a morphism of ringed sites
given by a representably flat functor — and the statement below is the first of those two
assertions read at the other pullback of this development, not a third assertion of the
source.  Stacks 0G6R likewise is registered on its statement with a bare attribute, and the
placement of these two tags is not decided here.

*Universes.*  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The narrowing is
inherited: it is forced four independent ways on this chain, recorded in the implementation
notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/ChangeOfRingsReduction.lean`, and
additionally by `CategoryTheory.Functor.IsMorphismOfSites`, which is declared for
`{C D : Type u}` with `SmallCategory` on both.  Nothing here narrows further.  The two
`HasSheafCompose` hypotheses that `Stacks.Sheaves.ToposPullback.isFlat_pullbackModuleObj_of_isFlat`
carries beyond the six of this chain — `(forget RingCat)` and `(forget AddCommGrpCat)` on each
site — are found by instance search at this size, so no instance binder is added for them.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules
open StacksPullbackFactorization

noncomputable section

universe u

namespace Stacks.SheafOfModules.FlatRingTransport

section Transport

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- **Restriction of scalars along the inverse of an isomorphism is extension of scalars along
the isomorphism.**  Both functors are left adjoint to restriction of scalars along `e.hom`:
the first because `e` is invertible, so restriction of scalars along it is an equivalence, and
the second by the change-of-rings adjunction.  Uniqueness of left adjoints does the rest. -/
def restrictScalarsIsoExtendScalars (e : O₁ ≅ O₂) :
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        ((Stacks.forgetCommRingSheaf J).mapIso e)).functor ≅
      Stacks.Sheaves.ModuleAdjunction.extendScalars.{u}
        ((Stacks.forgetCommRingSheaf J).map e.hom) :=
  Adjunction.leftAdjointUniq
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      ((Stacks.forgetCommRingSheaf J).mapIso e)).toAdjunction
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction.{u}
      ((Stacks.forgetCommRingSheaf J).map e.hom))

/-- **Flatness of a sheaf of modules is invariant under transport along an isomorphism of the
structure sheaf.**  If `M` is a flat `O₁`-module and `e : O₁ ≅ O₂`, then `M` read as an
`O₂`-module by restriction of scalars along `e.inv` is a flat `O₂`-module.

By `restrictScalarsIsoExtendScalars` that module is isomorphic to the extension of scalars of
`M` along `e.hom`, so this is Stacks 05V4. -/
theorem isFlat_restrictScalarsEquivalenceOfIso (e : O₁ ≅ O₂)
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf O₁))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O₁) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O₂)
      ((Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        ((Stacks.forgetCommRingSheaf J).mapIso e)).functor.obj M) :=
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso O₂
    ((restrictScalarsIsoExtendScalars e).app M).symm
    (Stacks.Sheaves.DerivedPullback.FlatExtendScalars.isFlat_extendScalars e.hom M hM)

end Transport

end Stacks.SheafOfModules.FlatRingTransport

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 05VD for the inverse image with no change of rings.**  Along any morphism of topoi
between the two sheaf topoi, the inverse image of a flat sheaf of `O_Y`-modules is flat over the
inverse image of the structure sheaf.

This is `Stacks.Sheaves.ToposPullback.isFlat_pullbackModuleObj_of_isFlat` with its three
hypotheses on the functor supplied from the morphism of topoi: left exactness is a field of it,
and preservation of colimits and of epimorphisms come from its being a left adjoint. -/
@[sga "4 V 1.7.1" "special case", sga "4 VI 8.6.4" "special case"]
theorem isFlat_inverseImageModules
    (φ : MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : Stacks.SheafOfModules.IsFlat (O := Y.O) M) :
    Stacks.SheafOfModules.IsFlat
      (O := pullbackCommRingSheaf X.J φ.inverseImage Y.O)
      ((inverseImageModules φ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) := by
  have : φ.inverseImage.IsLeftAdjoint := ⟨_, ⟨φ.adj⟩⟩
  have : PreservesFiniteLimits φ.inverseImage := φ.preservesFiniteLimits
  have : φ.inverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  exact isFlat_pullbackModuleObj_of_isFlat φ.inverseImage Y.O M hM

/-- **Stacks 05VD for the geometric half `g^*` of the factorization of `f^*`.**  The inverse
image with no change of rings carries a flat sheaf of `O_Y`-modules to a flat sheaf of
`f⁻¹O_Y`-modules.

`Stacks.Sheaves.InverseImageExactness.pullbackIsoInverseImageModules` identifies `g^*` with the
inverse image of sheaves of modules followed by transport along the comparison of the two
inverse images of the structure sheaf; the first factor preserves flatness by
`isFlat_inverseImageModules` and the second by
`Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso`. -/
@[sga "4 V 1.7.1" "Case A′ = u⁻¹A", sga "4 V 8.2.9" "special case", sga "4 VI 8.6.4" "special case"]
theorem isFlat_pullbackTopos_auxHomG (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (auxTopos f).O)
      ((auxHomG f).pullbackTopos.obj M) := by
  refine AlgebraicGeometry.SheafOfModules.IsFlat.of_iso (invRing f)
    ((Stacks.Sheaves.InverseImageExactness.pullbackIsoInverseImageModules f hmos).app M).symm ?_
  exact Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso
    ((Stacks.Sheaves.InverseImageExactness.invCommRingIso f hmos).app Y.O) _
    (isFlat_inverseImageModules (Stacks.Sheaves.InverseImageExactness.toposHom f hmos) M hM)

open Stacks.Sheaves.DerivedPullback.FlatExtendScalars in
/-- **Stacks 05VD for the abstract module pullback.**  For a morphism of ringed topoi whose
underlying continuous functor is a morphism of sites, the pullback of a flat sheaf of modules is
flat.

This is the geometric half above followed by the change-of-rings half, which is Stacks 05V4;
the assembly along `StacksPullbackFactorization.pullbackFactorIso` is
`isFlat_pullbackTopos_of_isFlat_pullbackTopos_auxHomG` of
`Stacks.Sheaves.DerivedPullback.FlatExtendScalars`. -/
theorem pullbackPreservesIsFlat (f : RingedToposSiteHom X Y) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat f := fun hmos M hM =>
  isFlat_pullbackTopos_of_isFlat_pullbackTopos_auxHomG f M
    (isFlat_pullbackTopos_auxHomG f hmos M hM)

end AlgebraicGeometry.RingedToposSiteHom

namespace AlgebraicGeometry.RingedToposSiteHom

/-- **Stacks 05VD at every morphism of ringed topoi at once.**  This is the form in which the
reduction of Stacks 0G6R consumes Stacks 05VD, since the source applies it not to `f` but to the
geometric half of its factorization. -/
@[sga "4 VI 8.6.4" "special case"]
theorem pullbackPreservesIsFlatUniv :
    Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u} := by
  intro X Y _ _ _ _ _ _ f
  exact pullbackPreservesIsFlat f

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0G6R, with nothing left over.**  For a morphism of ringed topoi whose underlying
continuous functor is a morphism of sites, pullback keeps a short exact sequence of sheaves of
modules short exact when its third term is flat.

`Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact` reduces this to universally
quantified Stacks 05VD, which is `pullbackPreservesIsFlatUniv`. -/
theorem pullbackPreservesShortExact (f : RingedToposSiteHom X Y) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f :=
  Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact f
    pullbackPreservesIsFlatUniv.{u}

end AlgebraicGeometry.RingedToposSiteHom

end

end
