module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem
public import StacksFrontier.Deformation.ToposThickening.UniversalFirstOrder.ImageComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The square-zero extension problem on arbitrary equivalent sites

`StacksFrontier/Deformation/ToposThickening/ExtensionProblem.lean` poses the extension problem of
Stacks 08UF with both thickenings presented on the *same* site, so that the displayed diagram of
sheaves lives on the site of the source ringed topos. This file poses the same problem without
that choice: the thickening of the base is an arbitrary first order thickening `B ⟶ B'`, a
solution is an arbitrary first order thickening `X ⟶ X'` together with a morphism `X' ⟶ B'`, and
the square of ringed topoi is required to commute only up to an invertible 2-morphism.

## Main definitions

* `Deformation.ToposThickening.ArbitrarySiteExtensionProblem`: the fixed data — the first order
  thickening of the base, the morphism to the reduced base, the transported inverse-image ideal,
  the prescribed module, and the map on ideals.
* `Deformation.ToposThickening.ArbitrarySiteExtensionProblem.CompatibleFirstOrderThickening`: a
  solution on a *given* thickened source ringed topos.
* `Deformation.ToposThickening.ArbitrarySiteSolution`: a solution with the thickened source
  ringed topos included in the datum rather than fixed in advance, with
  `.Iso`, `.IsomorphismClasses` and `.AutomorphismGroup`.

## Main results

* `Deformation.ToposThickening.ArbitrarySiteSolution.groupoid`: arbitrary-site solutions and
  their isomorphisms form a groupoid.

## Implementation notes

The underlying topoi of a first order thickening are identified by its geometric part, but the
*sites* presenting them need not be the same; the general presentation therefore keeps the
equivalences of topoi as part of the first order thickenings, and the displayed diagram of
sheaves is pulled back to the fixed reduced topos of `X`.

The middle vertical arrow of the diagram is not free data. It is the transport of the structure
map of `f'` through the specified invertible 2-morphism, and `baseMap_eq` says exactly that: the
comparison isomorphism `comparison` of the two inverse images of the thickened base structure
sheaf is required by `comparison_forget` to be the mate of the geometric 2-morphism, not an
independently chosen automorphism of that sheaf.

Isomorphisms of arbitrary-site solutions are measured on the common reduced topos of `X`, by
isomorphisms of the pulled-back thickened structure sheaves over the fixed reduced diagram. Since
both geometric morphisms are equivalences this loses nothing, and it makes the isomorphism classes
independent of any choice of site presentation.

Two further departures from the source's phrasing, both forced by the declarations this file
builds on and neither a change to what is asserted.

* The instance arguments recording that the Grothendieck topologies allow the forgetful sheaf
  compositions are placed after the ringed topoi, because `AlgebraicGeometry.RingedToposHom` needs
  them to elaborate its own type — as in `…/ExtensionProblem.lean`. For the thickened source
  ringed topos, which is part of the solution rather than fixed in advance,
  `ArbitrarySiteSolution` carries *two* such instance fields, one for each of the two forgetful
  functors that a morphism of ringed topoi out of it requires.
* `AlgebraicGeometry.RingedToposHom.comp` and `MorphismOfTopoi.comp` are made locally
  `implicit_reducible`, because the composite's underlying morphism of topoi is the composite of
  the underlying morphisms of topoi only at default transparency, and the equation `baseMap_eq`
  mentions both spellings.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

namespace Deformation.ToposThickening

-- The fixed-site presentation of the problem, stated in
-- `StacksFrontier/Deformation/ToposThickening/ExtensionProblem.lean`, is the other half of the
-- covering set of Stacks 08UF.
add_to_stacks 08UF
  Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening
add_to_stacks 08V4 "the displayed diagram, same-site presentation"
  Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

/-- The fixed data of the square-zero extension problem of Stacks 08UF, without choosing
identical sites for the two first order thickenings: a first order thickening `B ⟶ B'` of the
base, a morphism `X ⟶ B` to the reduced base, the inverse image of the base ideal transported to
the site of `X`, a module on `X`, and the prescribed map from that ideal to that module. -/
public structure ArbitrarySiteExtensionProblem
    (X : RingedTopos.{v, u, w})
    (B : RingedTopos.{v', u', w'})
    (B' : RingedTopos.{v'', u'', w''})
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [B.J.HasSheafCompose (forget RingCat.{w'})]
    [B'.J.HasSheafCompose (forget RingCat.{w''})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [B'.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})] where
  /-- The thickening of the base, whose geometric part is an equivalence. -/
  t : RingedToposHom B B'
  /-- The thickening of the base is of first order. -/
  firstOrder : FirstOrderThickening t
  /-- The morphism to the reduced base. -/
  f : RingedToposHom X B
  /-- The transported inverse-image ideal of the base thickening. -/
  I : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
  /-- The prescribed kernel module of a solution. -/
  G : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)
  /-- Identification of `I` with the kernel of the pulled-back base reduction. -/
  idealInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor f.toToposHom).map t.fSharpInverseImage))).obj I ⟶
      SheafOfModules.unit
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor f.toToposHom).obj
            ((inverseImageCommRingFunctor t.toToposHom).obj B'.O)))
  /-- The specified map on ideals. -/
  c : I ⟶
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        f.fSharpInverseImage)).obj G
  /-- The inclusion lands in the kernel of the pulled-back base reduction. -/
  idealZero : ∀ (U : X.Cᵒᵖ) (a : I.val.obj U),
    ((inverseImageCommRingFunctor f.toToposHom).map t.fSharpInverseImage).hom.app U
      (show ((inverseImageCommRingFunctor f.toToposHom).obj
        ((inverseImageCommRingFunctor t.toToposHom).obj B'.O)).obj.obj U from
          idealInclusion.val.app U a) = 0
  /-- The ideal exhausts that kernel, uniquely, on every section. -/
  idealUniversal : ∀ (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor f.toToposHom).obj
      ((inverseImageCommRingFunctor t.toToposHom).obj B'.O)).obj.obj U),
    ((inverseImageCommRingFunctor f.toToposHom).map t.fSharpInverseImage).hom.app U a = 0 →
      ∃! x : I.val.obj U,
        (show ((inverseImageCommRingFunctor f.toToposHom).obj
          ((inverseImageCommRingFunctor t.toToposHom).obj B'.O)).obj.obj U from
            idealInclusion.val.app U x) = a

namespace ArbitrarySiteExtensionProblem

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  {B' : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B'.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- **Stacks 08UF on arbitrary equivalent sites.** A solution of the extension problem on a given
thickened source ringed topos `X'`. The displayed diagram of sheaves is pulled back along the
equivalence underlying `i`, and the invertible 2-morphism records the morphism of thickenings. -/
@[stacks 08UF "arbitrary equivalent sites",
  stacks 08V4 "the same square-zero extension problem, as stated in the Cotangent chapter"]
public structure CompatibleFirstOrderThickening
    (S : ArbitrarySiteExtensionProblem X B B')
    (X' : RingedTopos.{v''', u''', w'''})
    [X'.J.HasSheafCompose (forget RingCat.{w'''})]
    [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})] where
  /-- The thickening of the source. -/
  i : RingedToposHom X X'
  /-- The thickening of the source is of first order. -/
  firstOrder : FirstOrderThickening i
  /-- The morphism from the thickened source to the thickened base. -/
  f' : RingedToposHom X' B'
  /-- The invertible 2-morphism in the square of ringed topoi. -/
  commutes : RingedToposHom.TwoMorphism (f'.comp i) (S.t.comp S.f)
  /-- The 2-morphism is invertible. -/
  commutesIsIso : IsIso commutes.t
  /-- Its induced transport on the pulled-back thickened base ring. -/
  comparison :
    (inverseImageCommRingFunctor (S.t.comp S.f).toToposHom).obj B'.O ≅
      (inverseImageCommRingFunctor (f'.comp i).toToposHom).obj B'.O
  /-- The comparison is the mate of the geometric 2-morphism, not an independently chosen
  automorphism of the base ring. -/
  comparison_forget :
    X.forgetRing.map comparison.hom =
      ((CategoryTheory.conjugateEquiv
        (f'.comp i).toToposHom.adj
        (S.t.comp S.f).toToposHom.adj).symm commutes.t).app
          (B'.forgetRing.obj B'.O)
  /-- The map in the middle column of the pulled-back diagram. -/
  baseMap : (inverseImageCommRingFunctor S.f.toToposHom).obj
      ((inverseImageCommRingFunctor S.t.toToposHom).obj B'.O) ⟶
    (inverseImageCommRingFunctor i.toToposHom).obj X'.O
  /-- The middle arrow is obtained from the actual structure map of `f'` by transport through the
  specified 2-morphism. -/
  baseMap_eq : baseMap =
    (S.f.toToposHom.inverseImageCommRingCompIso S.t.toToposHom).inv.app B'.O ≫
      comparison.hom ≫
      (i.toToposHom.inverseImageCommRingCompIso f'.toToposHom).hom.app B'.O ≫
      (inverseImageCommRingFunctor i.toToposHom).map f'.fSharpInverseImage
  /-- The right-hand square of the diagram commutes. -/
  baseMap_reduction : baseMap ≫ i.fSharpInverseImage =
    (inverseImageCommRingFunctor S.f.toToposHom).map S.t.fSharpInverseImage ≫
      S.f.fSharpInverseImage
  /-- The identification of `G` with the kernel of the upper reduction. -/
  kernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        i.fSharpInverseImage)).obj S.G ⟶
      SheafOfModules.unit
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor i.toToposHom).obj X'.O))
  /-- The chosen inclusion lands in the upper kernel. -/
  kernelZero : ∀ (U : X.Cᵒᵖ) (a : S.G.val.obj U),
    i.fSharpInverseImage.hom.app U
      (show ((inverseImageCommRingFunctor i.toToposHom).obj X'.O).obj.obj U from
        kernelInclusion.val.app U a) = 0
  /-- The chosen inclusion identifies `G` with the entire upper kernel. -/
  kernelUniversal : ∀ (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor i.toToposHom).obj X'.O).obj.obj U),
    i.fSharpInverseImage.hom.app U a = 0 →
      ∃! g : S.G.val.obj U,
        (show ((inverseImageCommRingFunctor i.toToposHom).obj X'.O).obj.obj U from
          kernelInclusion.val.app U g) = a
  /-- The left-hand square induces the prescribed map on kernels. -/
  baseMap_ideal : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
    baseMap.hom.app U
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj
        ((inverseImageCommRingFunctor S.t.toToposHom).obj B'.O)).obj.obj U from
          S.idealInclusion.val.app U a) =
      (show ((inverseImageCommRingFunctor i.toToposHom).obj X'.O).obj.obj U from
        kernelInclusion.val.app U (S.c.val.app U a))

end ArbitrarySiteExtensionProblem

/-- A solution of the extension problem on an arbitrary equivalent source site, with the site
itself included in the object rather than fixed in advance. -/
public structure ArbitrarySiteSolution
    {X : RingedTopos.{v, u, w}}
    {B : RingedTopos.{v', u', w'}}
    {B' : RingedTopos.{v'', u'', w''}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [B.J.HasSheafCompose (forget RingCat.{w'})]
    [B'.J.HasSheafCompose (forget RingCat.{w''})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [B'.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
    (S : ArbitrarySiteExtensionProblem X B B') where
  /-- The thickened source ringed topos. -/
  sourceExtension : RingedTopos.{v''', u''', w'''}
  /-- Its topology admits the forgetful sheaf composition to sheaves of sets. -/
  sourceHasSheafComposeForget : sourceExtension.J.HasSheafCompose (forget RingCat.{w'''})
  /-- Its topology admits the forgetful sheaf composition to sheaves of rings. -/
  sourceHasSheafCompose : sourceExtension.J.HasSheafCompose
    (forget₂ CommRingCat.{w'''} RingCat.{w'''})
  /-- The solution on that thickened source ringed topos. -/
  solution : letI := sourceHasSheafComposeForget
    letI := sourceHasSheafCompose
    S.CompatibleFirstOrderThickening sourceExtension

attribute [instance] ArbitrarySiteSolution.sourceHasSheafComposeForget
  ArbitrarySiteSolution.sourceHasSheafCompose

namespace ArbitrarySiteSolution

variable {X : RingedTopos.{v, u, w}}
    {B : RingedTopos.{v', u', w'}}
    {B' : RingedTopos.{v'', u'', w''}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [B.J.HasSheafCompose (forget RingCat.{w'})]
    [B'.J.HasSheafCompose (forget RingCat.{w''})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [B'.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
    {S : ArbitrarySiteExtensionProblem X B B'}

/-- An isomorphism of arbitrary-site solutions, measured on the common reduced topos. Because
both geometric morphisms are equivalences this is the site-independent isomorphism of their
thickened structure sheaves. -/
public structure Iso (P Q : ArbitrarySiteSolution S) where
  /-- The isomorphism of the pulled-back thickened structure sheaves. -/
  hom : (inverseImageCommRingFunctor P.solution.i.toToposHom).obj P.sourceExtension.O ≅
    (inverseImageCommRingFunctor Q.solution.i.toToposHom).obj Q.sourceExtension.O
  /-- It is over the reduced structure sheaf. -/
  reduction_comm : hom.hom ≫ Q.solution.i.fSharpInverseImage =
    P.solution.i.fSharpInverseImage
  /-- It respects the map from the thickened base. -/
  baseMap_comm : P.solution.baseMap ≫ hom.hom = Q.solution.baseMap
  /-- It is the identity on the specified kernel module. -/
  kernel_comm : ∀ (U : X.Cᵒᵖ) (g : S.G.val.obj U),
    hom.hom.hom.app U
      (show ((inverseImageCommRingFunctor P.solution.i.toToposHom).obj
        P.sourceExtension.O).obj.obj U from
        P.solution.kernelInclusion.val.app U g) =
      (show ((inverseImageCommRingFunctor Q.solution.i.toToposHom).obj
        Q.sourceExtension.O).obj.obj U from
        Q.solution.kernelInclusion.val.app U g)

namespace Iso

/-- The identity isomorphism of an arbitrary-site solution. -/
public noncomputable def refl (P : ArbitrarySiteSolution S) : Iso P P where
  hom := CategoryTheory.Iso.refl _
  reduction_comm := Category.id_comp P.solution.i.fSharpInverseImage
  baseMap_comm := Category.comp_id P.solution.baseMap
  kernel_comm _ _ := rfl

/-- The inverse of an isomorphism of arbitrary-site solutions. -/
public noncomputable def symm {P Q : ArbitrarySiteSolution S} (e : Iso P Q) : Iso Q P where
  hom := e.hom.symm
  reduction_comm := by
    rw [← e.reduction_comm, ← Category.assoc, CategoryTheory.Iso.symm_hom, e.hom.inv_hom_id,
      Category.id_comp]
  baseMap_comm := by
    rw [← e.baseMap_comm, Category.assoc, CategoryTheory.Iso.symm_hom, e.hom.hom_inv_id,
      Category.comp_id]
  kernel_comm := by
    intro U g
    rw [← e.kernel_comm U g]
    change e.hom.inv.hom.app U
      (e.hom.hom.hom.app U (P.solution.kernelInclusion.val.app U g)) =
        P.solution.kernelInclusion.val.app U g
    exact congrArg
      (fun m : (inverseImageCommRingFunctor P.solution.i.toToposHom).obj P.sourceExtension.O ⟶
          (inverseImageCommRingFunctor P.solution.i.toToposHom).obj P.sourceExtension.O ↦
        m.hom.app U (P.solution.kernelInclusion.val.app U g)) e.hom.hom_inv_id

/-- Composition of isomorphisms of arbitrary-site solutions. -/
public noncomputable def trans {P Q R : ArbitrarySiteSolution S}
    (e : Iso P Q) (f : Iso Q R) : Iso P R where
  hom := e.hom ≪≫ f.hom
  reduction_comm := by
    rw [CategoryTheory.Iso.trans_hom, Category.assoc, f.reduction_comm, e.reduction_comm]
  baseMap_comm := by
    rw [← f.baseMap_comm, ← e.baseMap_comm]
    exact (Category.assoc _ _ _).symm
  kernel_comm := by
    intro U g
    change f.hom.hom.hom.app U
      (e.hom.hom.hom.app U (P.solution.kernelInclusion.val.app U g)) =
        R.solution.kernelInclusion.val.app U g
    exact (congrArg (f.hom.hom.hom.app U) (e.kernel_comm U g)).trans (f.kernel_comm U g)

/-- Isomorphisms of arbitrary-site solutions are determined by their underlying sheaf
isomorphisms. -/
public theorem ext {P Q : ArbitrarySiteSolution S} {e f : Iso P Q} (h : e.hom = f.hom) : e = f := by
  cases e
  cases f
  cases h
  rfl

end Iso

/-- Two arbitrary-site solutions are isomorphic over the fixed reduced diagram. -/
public def Isomorphic (P Q : ArbitrarySiteSolution S) : Prop := Nonempty (Iso P Q)

/-- Isomorphism of arbitrary-site solutions is an equivalence relation. -/
public noncomputable def isomorphicSetoid (S : ArbitrarySiteExtensionProblem X B B') :
    Setoid (ArbitrarySiteSolution S) where
  r := Isomorphic
  iseqv := {
    refl := fun P => ⟨Iso.refl P⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Isomorphism classes of solutions, allowing all equivalent source sites. -/
public noncomputable def IsomorphismClasses (S : ArbitrarySiteExtensionProblem X B B') :=
  Quotient (isomorphicSetoid S)

/-- Arbitrary-site solutions and their isomorphisms form a groupoid. -/
public noncomputable instance groupoid (S : ArbitrarySiteExtensionProblem X B B') :
    Groupoid (ArbitrarySiteSolution S) where
  Hom := Iso
  id := Iso.refl
  comp e f := e.trans f
  id_comp e := Iso.ext (CategoryTheory.Iso.refl_trans e.hom)
  comp_id e := Iso.ext (CategoryTheory.Iso.trans_refl e.hom)
  assoc e f g := Iso.ext (CategoryTheory.Iso.trans_assoc e.hom f.hom g.hom)
  inv e := e.symm
  inv_comp e := Iso.ext (CategoryTheory.Iso.symm_self_id e.hom)
  comp_inv e := Iso.ext (CategoryTheory.Iso.self_symm_id e.hom)

/-- The automorphism group of an arbitrary-site solution, fixing the reduced structure sheaf, the
map from the thickened base, and the chosen kernel identification. -/
public abbrev AutomorphismGroup (P : ArbitrarySiteSolution S) := Aut P

end ArbitrarySiteSolution

end Deformation.ToposThickening

end
