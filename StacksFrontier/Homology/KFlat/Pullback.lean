module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of sheaves of modules, in the ring-sheaf spelling the tensor product uses

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. Two developments meet on
`Mod(𝒪_X)` and name its sheaf of rings differently:

* `structureSheafRing X`, a `def`, is the ring sheaf over which the
  pullback `f^*` and pushforward `f_*` of Stacks 0096 are stated;
* `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, an `abbrev`, is the ring sheaf over which the
  tensor
  product `⊗_{𝒪_X}`, the total complex `Tot(- ⊗ -)` and hence K-flatness are stated.

The two are the same expression, `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`,
and `ringSheaf_eq` below is `rfl`. They are nevertheless *not* interchangeable in practice:
`structureSheafRing` is a `def`, so the `Category`, `Preadditive` and
`Abelian` instances on `SheafOfModules (structureSheafRing X)` are
different *terms* from the ones on `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
  X.sheaf)`, and
typeclass synthesis does not unfold a `def` to see that they agree. Concretely, writing

```
CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
  (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K)
```

fails to elaborate — synthesis of `∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
  M).Additive`
is performed against the `structureSheafRing` spelling and fails — even
with the instance available as a hypothesis, and even with a type ascription on the pullback
functor. So the statements of Stacks 06YC (K-flatness is stable under pullback) and of the
derived pullback of Stacks 06YJ, 079W and 0D5T cannot be written down at all until the
pullback functor is given a name whose declared type is in the tensor-product spelling.

That name is `modulePullback` below. It is *the same functor* —
`modulePullback_eq_modulePullback` is `rfl` — only retyped, so every fact about
`RingedSpaceModuleAdjunction.modulePullback` transports along that equation.
`modulePullback_additive` re-registers additivity at the new type, which is what
`Functor.mapHomologicalComplex` and `Functor.mapHomotopyCategory` consume.

Nothing here is K-flatness-specific; the file carries no mathematical content beyond the
identification of the two ring sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace StacksDraft.KFlat

universe u

/-- The ring sheaf of a ringed space as named by the pullback/pushforward development and as
named by the tensor-product development agree: both are
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`. -/
theorem ringSheaf_eq (X : RingedSpace.{u, u}) :
    structureSheafRing X = Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf :=
  rfl

/-- Pullback of sheaves of modules along a morphism of ringed spaces, `f^* : Mod(𝒪_Y) ⥤
Mod(𝒪_X)`, with its type written over `Stacks.SheafOfModules.Tensor.ringSheaf` rather than over
`structureSheafRing`.

This is `RingedSpaceModuleAdjunction.modulePullback f` and nothing else, as
`modulePullback_eq_modulePullback` records. The point of the declaration is its *type*:
only in this spelling does typeclass synthesis match the instances carried by the tensor
product `Stacks.SheafOfModules.Tensor.sheafTensor`, so only in this spelling can the degreewise
  pullback of
a complex appear as an argument of K-flatness. -/
@[ega "IV 2.1.4"]
def modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  RingedSpaceModuleAdjunction.modulePullback f

/-- `StacksDraft.KFlat.modulePullback f` is `RingedSpaceModuleAdjunction.modulePullback f`:
the retyping of `ringSheaf_eq` changes no data. Use this to transport any statement proved
about the latter. -/
theorem modulePullback_eq_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    modulePullback f = RingedSpaceModuleAdjunction.modulePullback f :=
  rfl

/-- `f^*` is additive, in the retyped spelling. This is
`RingedSpaceModuleAdjunction.modulePullback_additive` re-registered at the type declared by
`modulePullback`, and it is what lets `f^*` be applied to cochain complexes and to the
homotopy category *inside* a statement about `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
instance modulePullback_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).Additive :=
  inferInstanceAs (RingedSpaceModuleAdjunction.modulePullback f).Additive

/-- Pushforward of sheaves of modules along a morphism of ringed spaces, `f_* : Mod(𝒪_X) ⥤
Mod(𝒪_Y)`, with its type written over `Stacks.SheafOfModules.Tensor.ringSheaf` rather than over
`structureSheafRing`.

This is `RingedSpaceModuleAdjunction.modulePushforward f` and nothing else, as
`modulePushforward_eq_modulePushforward` records; the point is again the *type*. The
elaboration failure described in the module docstring for the pullback is not specific to
the pullback: any statement placing `f_*` of a complex inside a predicate stated over
`Stacks.SheafOfModules.Tensor.ringSheaf` — the derived pushforward of Stacks 079W, for instance —
  hits it
in the same way, and is repaired in the same way. -/
def modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  RingedSpaceModuleAdjunction.modulePushforward f

/-- `StacksDraft.KFlat.modulePushforward f` is
`RingedSpaceModuleAdjunction.modulePushforward f`: the retyping of `ringSheaf_eq` changes no
data. Use this to transport any statement proved about the latter. -/
theorem modulePushforward_eq_modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    modulePushforward f = RingedSpaceModuleAdjunction.modulePushforward f :=
  rfl

/-- `f_*` is additive, in the retyped spelling. This is
`RingedSpaceModuleAdjunction.modulePushforward_additive` re-registered at the type declared
by `modulePushforward`, and it is what lets `f_*` be applied to cochain complexes and to the
homotopy category *inside* a statement about `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
instance modulePushforward_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePushforward f).Additive :=
  inferInstanceAs (RingedSpaceModuleAdjunction.modulePushforward f).Additive

end StacksDraft.KFlat

end

end
