module

public import Mathlib.Algebra.Ring.Ext
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf

/-!
# The big étale ringed topos of an algebraic space

The big étale site of an algebraic space `X` carries the sheaf of global regular functions, and
a morphism `f : Y ⟶ X` of algebraic spaces induces a morphism of the resulting ringed topoi.
The inverse image of the structure sheaf of `X` is canonically isomorphic to the structure sheaf
of `Y`, because restriction along composition with `f` is the identity on rings of regular
functions.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedTopos`: the big étale site of `X` together
  with its structure sheaf, as a ringed topos.
* `AlgebraicGeometry.BigEtaleSpaceSite.restrictionStructureIso`: restriction of the structure
  sheaf of `X` along composition with `f`, identified with the structure sheaf of `Y`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleStructureIso`: the canonical isomorphism from the
  inverse image of the structure sheaf of `X` to the structure sheaf of `Y`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedMorphism`: the induced morphism of big étale
  ringed topoi.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleStructureIso_hom_app`: on each object over `Y` the
  canonical isomorphism is the identity on the ring of regular functions.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedMorphism_fSharpInverseImage`: the
  inverse-image form of the structure map of the induced morphism is that canonical isomorphism.

## References

* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry

/-- A morphism of commutative rings whose carriers agree and which acts as the transport of that
agreement is the identity, after the two objects of `CommRingCat` are identified. -/
private theorem commRingCat_hom_heq_id {A B : CommRingCat} (g : A ⟶ B)
    (hType : (A : Type _) = (B : Type _)) (hfun : ∀ x, g x = cast hType x) :
    HEq g (𝟙 B) := by
  obtain @⟨R, iA⟩ := A
  obtain @⟨T, iB⟩ := B
  obtain rfl : R = T := hType
  obtain rfl : iA = iB := CommRing.ext
    (funext₂ fun x y => by simpa [hfun] using g.hom.map_add x y)
    (funext₂ fun x y => by simpa [hfun] using g.hom.map_mul x y)
  exact heq_of_eq (CommRingCat.hom_ext (RingHom.ext hfun))

namespace BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- The big étale site of an algebraic space together with its sheaf of global regular
functions, as a ringed topos. -/
noncomputable abbrev bigEtaleRingedTopos (X : T.Spaces) : RingedTopos where
  C := Over X
  J := T.bigEtaleTopology X
  O := T.structureSheaf X

/-- Restriction along composition with `f` identifies the big étale structure sheaf of `X` with
that of `Y`: on each object over `Y` both are the ring of global regular functions of its
underlying algebraic space, and the restriction maps agree. -/
noncomputable def restrictionStructureIso {X Y : T.Spaces} (f : Y ⟶ X) :
    ((Over.map f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (T.bigEtaleTopology Y) (T.bigEtaleTopology X)).obj (T.structureSheaf X) ≅
      T.structureSheaf Y :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)

/-- The canonical isomorphism from the inverse image of the big étale structure sheaf of `X` to
the big étale structure sheaf of `Y`. -/
noncomputable def bigEtaleStructureIso {X Y : T.Spaces} (f : Y ⟶ X) :
    (inverseImageCommRingFunctor (T.bigEtaleMorphism f)).obj (bigEtaleRingedTopos T X).O ≅
      (bigEtaleRingedTopos T Y).O :=
  restrictionCommRingIso (T.bigEtaleTopology Y) (T.bigEtaleTopology X) (Over.map f)
      (T.structureSheaf X) ≪≫
    restrictionStructureIso T f

/-- On each object over `Y` the canonical structure-sheaf isomorphism is the identity on the ring
of global regular functions. The heterogeneous equality accounts for the two presentations of
that ring: the sections of a pullback of sheaves of commutative rings on the one side, and
`CommRingCat.of` of the ring of regular functions on the other. -/
theorem bigEtaleStructureIso_hom_app {X Y : T.Spaces} (f : Y ⟶ X) (U : Over Y) :
    HEq ((bigEtaleStructureIso T f).hom.hom.app (Opposite.op U))
      (𝟙 (CommRingCat.of (Space.globalFunctions' T.fppfSite S T.fppf_mem U.left.obj))) := by
  have hcomponent := congrArg (fun η => η.hom.app (Opposite.op U))
    (restrictionCommRingIso_hom_forget (T.bigEtaleTopology Y) (T.bigEtaleTopology X)
      (Over.map f) (T.structureSheaf X))
  exact commRingCat_hom_heq_id _ rfl fun x => congrArg (· x) hcomponent

/-- The morphism of big étale ringed topoi induced by a morphism of algebraic spaces: the big
étale morphism of topoi, with the adjunct of the canonical structure-sheaf isomorphism as its
structure map. -/
noncomputable def bigEtaleRingedMorphism {X Y : T.Spaces} (f : Y ⟶ X) :
    RingedToposHom (bigEtaleRingedTopos T Y) (bigEtaleRingedTopos T X) where
  toToposHom := T.bigEtaleMorphism f
  fSharp :=
    ((commRingImageAdjunction (T.bigEtaleMorphism f)).homEquiv _ _)
      (bigEtaleStructureIso T f).hom

/-- The inverse-image form of the structure map of the induced morphism of ringed topoi is the
canonical isomorphism of big étale structure sheaves. -/
theorem bigEtaleRingedMorphism_fSharpInverseImage {X Y : T.Spaces} (f : Y ⟶ X) :
    (bigEtaleRingedMorphism T f).fSharpInverseImage = (bigEtaleStructureIso T f).hom :=
  Equiv.symm_apply_apply _ _

end BigEtaleSpaceSite

end AlgebraicGeometry

end
