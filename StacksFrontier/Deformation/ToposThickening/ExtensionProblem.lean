module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom

/-!
# A square-zero extension problem for ringed topoi

Fix a first order thickening of a base ringed topos, a morphism from another ringed topos to
its reduction, a module on the latter, and a prescribed map from the inverse image of the base
ideal to that module. A solution is a compatible first order thickening of the source ringed
topos. This file records the fixed data of that problem and the notion of a solution, together
with the isomorphisms of solutions over the fixed diagram.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem`: the fixed lower row of the
  diagram and the map on ideals.
* `Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening`: a
  solution, i.e. the thickened structure sheaf and the exact upper row.
* `Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening.Iso`:
  an isomorphism of solutions over the fixed diagram, with
  `.IsomorphismClasses` the solutions up to isomorphism and
  `.AutomorphismGroup` the automorphisms of one solution.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.compatibleFirstOrderThickeningGroupoid`:
  solutions and their compatible isomorphisms form a groupoid.

## Implementation notes

Both thickenings are presented on the same site, so the displayed diagram of sheaves lives on
the site of the source ringed topos. The module `I` is the inverse image of the base ideal: its
inclusion is required, section by section, to be the kernel of the inverse-image base-ring map.
The two exact rows are locally surjective, not necessarily surjective on sections. The
square-zero and kernel identification conditions make the given module structures canonical.

The instance arguments recording that the Grothendieck topologies admit the forgetful sheaf
compositions are placed after the two ringed topoi, because
`AlgebraicGeometry.RingedToposHom` needs them to elaborate its own type.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

/-- The fixed data of a square-zero extension problem of ringed topoi: a morphism `f : X ⟶ B`,
a first order thickening of the base, the inverse image of its ideal, a module on `X`, and the
prescribed map from that ideal to that module. -/
public structure RingedToposExtensionProblem
    (X : RingedTopos.{v, u, w})
    (B : RingedTopos.{v', u', w'})
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [B.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})] where
  /-- The given map of ringed topoi. -/
  f : RingedToposHom X B
  /-- The structure sheaf of the thickened base topos, on the identified site. -/
  baseExtension : Sheaf B.J CommRingCat.{w'}
  /-- The reduction map of the base thickening. -/
  baseReduction : baseExtension ⟶ B.O
  /-- The base reduction is locally surjective. -/
  baseLocallySurjective : Presheaf.IsLocallySurjective B.J baseReduction.hom
  /-- The ideal of the base first order thickening has square zero. -/
  baseSquareZero : ∀ U : B.Cᵒᵖ,
    (RingHom.ker (baseReduction.hom.app U).hom) ^ 2 = ⊥
  /-- The inverse image of the base ideal, as a module over the inverse image of the reduced
  base structure sheaf. -/
  I : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
  /-- The prescribed module on the source ringed topos. -/
  G : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)
  /-- Inclusion of the inverse-image base ideal into the inverse image of the thickened base
  structure sheaf. -/
  idealInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor f.toToposHom).map baseReduction))).obj I ⟶
      SheafOfModules.unit
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor f.toToposHom).obj baseExtension))
  /-- The prescribed map from the inverse image of the base ideal to `G`, linear over the
  inverse image of the reduced base structure sheaf. -/
  c : I ⟶
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        f.fSharpInverseImage)).obj G
  /-- The inclusion lands in the kernel of the pulled-back reduction map. -/
  idealZero : ∀ (U : X.Cᵒᵖ) (a : I.val.obj U),
    ((inverseImageCommRingFunctor f.toToposHom).map baseReduction).hom.app U
      (show ((inverseImageCommRingFunctor f.toToposHom).obj baseExtension).obj.obj U from
        idealInclusion.val.app U a) = 0
  /-- The ideal exhausts that kernel, uniquely, on every section. -/
  idealUniversal : ∀ (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor f.toToposHom).obj baseExtension).obj.obj U),
    ((inverseImageCommRingFunctor f.toToposHom).map baseReduction).hom.app U a = 0 →
      ∃! x : I.val.obj U,
        (show ((inverseImageCommRingFunctor f.toToposHom).obj baseExtension).obj.obj U from
          idealInclusion.val.app U x) = a

namespace RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A solution of the extension problem: a square-zero extension of the structure sheaf of `X`
by `G` over the thickened base, inducing the prescribed map on ideals. -/
public structure CompatibleFirstOrderThickening
    (S : RingedToposExtensionProblem X B) where
  /-- The thickened structure sheaf of the source. -/
  extension : Sheaf X.J CommRingCat.{w}
  /-- Reduction to the given structure sheaf. -/
  reduction : extension ⟶ X.O
  /-- The extension is locally surjective onto the reduction. -/
  locallySurjective : Presheaf.IsLocallySurjective X.J reduction.hom
  /-- Its kernel has square zero. -/
  squareZero : ∀ U : X.Cᵒᵖ,
    (RingHom.ker (reduction.hom.app U).hom) ^ 2 = ⊥
  /-- The map from the inverse image of the thickened base ring. -/
  baseMap : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ extension
  /-- The right-hand square of the diagram commutes. -/
  baseMap_reduction : baseMap ≫ reduction =
    (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage
  /-- The identification of `G` with the kernel of the upper reduction. -/
  kernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map reduction)).obj
        S.G ⟶
      SheafOfModules.unit
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj extension)
  /-- The chosen inclusion lands in the upper kernel. -/
  kernelZero : ∀ (U : X.Cᵒᵖ) (a : S.G.val.obj U),
    reduction.hom.app U
      (show extension.obj.obj U from kernelInclusion.val.app U a) = 0
  /-- The chosen inclusion identifies `G` with the entire upper kernel. -/
  kernelUniversal : ∀ (U : X.Cᵒᵖ) (a : extension.obj.obj U),
    reduction.hom.app U a = 0 →
      ∃! g : S.G.val.obj U,
        (show extension.obj.obj U from kernelInclusion.val.app U g) = a
  /-- The left-hand square induces the prescribed map on kernels. -/
  baseMap_ideal : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
    baseMap.hom.app U
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U a) =
      (show extension.obj.obj U from kernelInclusion.val.app U (S.c.val.app U a))

namespace CompatibleFirstOrderThickening

/-- An isomorphism of solutions inducing the identity on the reduced structure sheaf and on the
identified kernel. -/
public structure Iso {S : RingedToposExtensionProblem X B}
    (P Q : S.CompatibleFirstOrderThickening) where
  /-- The isomorphism of the thickened structure sheaves. -/
  hom : P.extension ≅ Q.extension
  /-- It is over the reduced structure sheaf. -/
  reduction_comm : hom.hom ≫ Q.reduction = P.reduction
  /-- It respects the map from the thickened base. -/
  baseMap_comm : P.baseMap ≫ hom.hom = Q.baseMap
  /-- It is the identity on the specified kernel module. -/
  kernel_comm : ∀ (U : X.Cᵒᵖ) (g : S.G.val.obj U),
    hom.hom.hom.app U
      (show P.extension.obj.obj U from P.kernelInclusion.val.app U g) =
    (show Q.extension.obj.obj U from Q.kernelInclusion.val.app U g)

namespace Iso

/-- The identity isomorphism of a solution. -/
public def refl {S : RingedToposExtensionProblem X B}
    (P : S.CompatibleFirstOrderThickening) : Iso P P where
  hom := CategoryTheory.Iso.refl P.extension
  reduction_comm := by simp
  baseMap_comm := Category.comp_id P.baseMap
  kernel_comm _ _ := rfl

/-- The inverse of an isomorphism of solutions. -/
public def symm {S : RingedToposExtensionProblem X B}
    {P Q : S.CompatibleFirstOrderThickening} (e : Iso P Q) : Iso Q P where
  hom := e.hom.symm
  reduction_comm := by simp [← e.reduction_comm]
  baseMap_comm := by
    calc
      Q.baseMap ≫ e.hom.inv = (P.baseMap ≫ e.hom.hom) ≫ e.hom.inv := by
        rw [e.baseMap_comm]
      _ = P.baseMap := by
        rw [Category.assoc, e.hom.hom_inv_id, Category.comp_id]
  kernel_comm := by
    intro U g
    rw [← e.kernel_comm U g]
    change e.hom.inv.hom.app U
      (e.hom.hom.hom.app U (P.kernelInclusion.val.app U g)) =
        P.kernelInclusion.val.app U g
    have h := congrArg
      (fun (m : P.extension ⟶ P.extension) => m.hom.app U
        (P.kernelInclusion.val.app U g)) e.hom.hom_inv_id
    change e.hom.inv.hom.app U
      (e.hom.hom.hom.app U (P.kernelInclusion.val.app U g)) =
        P.kernelInclusion.val.app U g at h
    exact h

/-- Composition of isomorphisms of solutions. -/
public def trans {S : RingedToposExtensionProblem X B}
    {P Q R : S.CompatibleFirstOrderThickening}
    (e : Iso P Q) (f : Iso Q R) : Iso P R where
  hom := e.hom ≪≫ f.hom
  reduction_comm := by simp [e.reduction_comm, f.reduction_comm, Category.assoc]
  baseMap_comm := by
    rw [← f.baseMap_comm, ← e.baseMap_comm]
    exact (Category.assoc _ _ _).symm
  kernel_comm := by
    intro U g
    change f.hom.hom.hom.app U
      (e.hom.hom.hom.app U (P.kernelInclusion.val.app U g)) =
        R.kernelInclusion.val.app U g
    exact (congrArg (f.hom.hom.hom.app U) (e.kernel_comm U g)).trans
      (f.kernel_comm U g)

/-- Isomorphisms of solutions are determined by their underlying sheaf isomorphisms. -/
public theorem ext {S : RingedToposExtensionProblem X B}
    {P Q : S.CompatibleFirstOrderThickening} {e f : Iso P Q}
    (h : e.hom = f.hom) : e = f := by
  cases e
  cases f
  cases h
  rfl

end Iso

/-- Two solutions are isomorphic over the fixed diagram. -/
public def Isomorphic {S : RingedToposExtensionProblem X B}
    (P Q : S.CompatibleFirstOrderThickening) : Prop := Nonempty (Iso P Q)

/-- Isomorphism of solutions is an equivalence relation. -/
public def isomorphicSetoid (S : RingedToposExtensionProblem X B) :
    Setoid S.CompatibleFirstOrderThickening where
  r := Isomorphic
  iseqv := {
    refl := fun P => ⟨Iso.refl P⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Isomorphism classes of solutions to the ringed-topos extension problem. -/
public def IsomorphismClasses (S : RingedToposExtensionProblem X B) :=
  Quotient (isomorphicSetoid S)

end CompatibleFirstOrderThickening

/-- Solutions and their compatible isomorphisms form a groupoid. -/
public instance compatibleFirstOrderThickeningGroupoid
    (S : RingedToposExtensionProblem X B) :
    Groupoid S.CompatibleFirstOrderThickening where
  Hom := CompatibleFirstOrderThickening.Iso
  id := CompatibleFirstOrderThickening.Iso.refl
  comp e f := e.trans f
  id_comp e := CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.refl_trans e.hom)
  comp_id e := CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.trans_refl e.hom)
  assoc e f g :=
    CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.trans_assoc e.hom f.hom g.hom)
  inv e := e.symm
  inv_comp e := CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.symm_self_id e.hom)
  comp_inv e := CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.self_symm_id e.hom)

/-- The automorphism group of a solution, fixing the reduced structure sheaf, the base map, and
the chosen kernel identification. -/
public abbrev CompatibleFirstOrderThickening.AutomorphismGroup
    {S : RingedToposExtensionProblem X B}
    (P : S.CompatibleFirstOrderThickening) := Aut P

end RingedToposExtensionProblem

end Deformation.ToposThickening

end
