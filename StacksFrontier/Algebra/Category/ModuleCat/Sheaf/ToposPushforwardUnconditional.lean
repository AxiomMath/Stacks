module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# ToposPushforwardUnconditional

Stronger forms of declarations of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built
on them.
-/

@[expose] public section

universe v u v' u' w w'

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable [BraidedCategory C]

namespace ModuleObj

open scoped RingObj

variable {R M : C} [RingObj R] [ModuleObj R M] {X : C}

end ModuleObj

namespace Functor

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided]

open scoped Obj RingObj ModuleObj

end Functor

namespace Functor

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

open scoped RingObj CommRingObj


end Functor

end CategoryTheory

namespace Stacks.InternalObj

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj CommRingObj ModuleObj RingObj

section Evaluation

variable {C : Type u} [Category.{v} C]

end Evaluation


section Presheaf

variable {C : Type u} [Category.{v} C]

end Presheaf

end Stacks.InternalObj

namespace Stacks

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj CommRingObj RingObj ModuleObj
open Stacks.InternalObj

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget CommRingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The sheaf of rings underlying a sheaf of commutative rings. Sheaves of modules over a
sheaf of commutative rings are taken over this. -/
noncomputable abbrev ringSheaf [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (forgetCommRingSheaf J).obj O

end Stacks

namespace MorphismOfTopoi

universe tt ww ww' vv uu vv' uu'

open CategoryTheory Limits

variable {E : Type uu} [Category.{vv} E] {F : Type uu'} [Category.{vv'} F]
  (f : MorphismOfTopoi E F)

end MorphismOfTopoi

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf J RingCat.{ww})

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  {O : Sheaf J RingCat.{ww}}

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})
  (Ψ : Sheaf J (Type ww) ⥤ Type tt) [PreservesFiniteProducts Ψ]

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf K RingCat.{ww'})

end Stacks.Sheaves.ToposPushforward
