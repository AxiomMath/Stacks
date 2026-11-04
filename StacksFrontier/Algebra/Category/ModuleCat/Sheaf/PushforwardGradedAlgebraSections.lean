module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPull
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite

/-!
# The pushforward of a sheaf of graded algebras along a morphism of ringed spaces, on sections

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `A` be a sheaf of graded `𝒪_X`-algebras.
`Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra` is the sheaf of graded
`𝒪_Y`-algebras `f_*A`, obtained by transporting `A` along the lax monoidal direct image of
sheaves of modules. Its homogeneous pieces are the direct images of those of `A`, so a section
of `(f_*A)_n` over `U` *is* a section of `A_n` over `f⁻¹U`; what the transport does not say is
what the multiplication and the unit of `f_*A` do to such sections. This file says it: they are
the multiplication and the unit of `A`, read over `f⁻¹U`.

The content is a section formula for the lax monoidal structure of the direct image. That
structure is `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`, so its tensorator is the
adjoint transpose of the oplax tensorator of the inverse image followed by the two counits, and
nothing about it is `rfl`. The computation is **not** redone here:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite` has already done it
for a continuous functor of sites, and a morphism of ringed spaces *is* such a functor —
`RingedSpaceModuleAdjunction.opensMap f` on the lattices of opens, with structure morphism
`f.hom.c`. What this file contributes is that the two constructions agree, which they do by
`rfl` once the tensorator is read through
`Stacks.DifferentialGradedPullbackConstruction.mu_pushforwardLaxMonoidal`.

## Main results

* `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_app`: **the multiplication of
  `f_*A` on two local sections over `U` is the multiplication of `A` read over `f⁻¹U`.**
* `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_one_eval`: the unit of `f_*A` over
  `U` is the unit of `A` read over `f⁻¹U`.
* `Stacks.PushforwardGradedAlgebra.mu_pushforwardFunctorLaxMonoidal_eq` and
  `epsilon_pushforwardFunctorLaxMonoidal_eq`: the tensorator and the unit morphism of
  `pushforwardFunctorLaxMonoidal`, as the adjoint transposes they are by construction, written
  with the monoidal structure on the inverse image that the site files use.

## Implementation notes

**Why the agreement of the two monoidal structures is never stated as an equality of
structures.** `Stacks.DifferentialGradedInverseImage.inverseImageMonoidal` is
`Stacks.PullbackMonoidalSite.pullbackMonoidalStrict`, which transports
`pullbackStrictMonoidal` along an equality of functors; the `Eq.mpr` that transport leaves
behind makes `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal f = inverseImageMonoidal …`
cost more than the heartbeat budget of one declaration, even though each half of it —
`pullbackStrictMonoidal f = pullbackStrictMonoidal …` and `pullbackMonoidalStrict … =
pullbackStrictMonoidal …` — is cheap. The two equalities here go around it: they are read at
the level of `Functor.LaxMonoidal.μ` and `Functor.LaxMonoidal.ε`, where the only monoidal
structure that appears is `pullbackStrictMonoidal`, and both are `rfl`.

**Why the right-adjointness datum is passed by name.** `Stacks.PullbackMonoidalSite.sheafRingHom`
is `RingedSpaceModuleAdjunction.structureSheafHom f` by `rfl`, but the instance
`pushforward_structureSheafHom_isRightAdjoint` is not found for the site spelling: the morphism
of sites is `Opens.map f.hom.base`, in which `f` occurs only under projections, so instance
search cannot solve for it. `isRightAdjoint_pushforward_sheafRingHom` is the datum at that
spelling, and it is supplied as the named argument `radj`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096) — the adjunction
  between pullback and pushforward of sheaves of modules on ringed spaces.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open TopologicalSpace
open SheafOfModules.GradedAlgebra
open Stacks.SheafOfModules.TensorSheafification
open Stacks.PullbackMonoidalSite Stacks.DifferentialGradedInverseImage
open Stacks.DifferentialGradedPullbackConstruction

open scoped TensorProduct

universe u

namespace Stacks.PushforwardGradedAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The direct image of sheaves of modules along a morphism of ringed spaces has a left
adjoint, at the site spelling of the structure morphism.** The morphism of sites is
`Opens.map f.hom.base`, in which `f` occurs only under projections, so the instance for
`RingedSpaceModuleAdjunction.structureSheafHom f` — the same morphism, by `rfl` — is not found
by instance search at this spelling. -/
theorem isRightAdjoint_pushforward_sheafRingHom :
    (SheafOfModules.pushforward.{u} (sheafRingHom (F := opensMap f)
      (O := Y.presheaf) (P := X.presheaf) f.hom.c
      (structureSheafRing Y).property
      (structureSheafRing X).property)).IsRightAdjoint :=
  pushforward_structureSheafHom_isRightAdjoint f

/-- **The tensorator of the lax monoidal direct image is an adjoint transpose**: the oplax
tensorator of the inverse image, followed by the two counits, transposed across `f^* ⊣ f_*`.
This is what `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` makes it, written with
`Stacks.PullbackMonoidalSite.pullbackStrictMonoidal` in place of
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`; the two are the same monoidal structure
on the same functor. -/
theorem mu_pushforwardFunctorLaxMonoidal_eq
    (_radj : (SheafOfModules.pushforward.{u} (sheafRingHom (F := opensMap f)
      (O := Y.presheaf) (P := X.presheaf) f.hom.c
      (structureSheafRing Y).property
      (structureSheafRing X).property)).IsRightAdjoint)
    (M N : SheafOfModules.{u} (structureRingSheaf X)) :
    Functor.LaxMonoidal.μ (self := pushforwardFunctorLaxMonoidal f)
        (pushforwardFunctor f) M N =
      (pullbackAdjunction f).homEquiv _ _
        (Functor.OplaxMonoidal.δ
            (self := (Stacks.PullbackMonoidalSite.pullbackStrictMonoidal (F := opensMap f)
              (O := Y.presheaf) (P := X.presheaf) f.hom.c
              (structureSheafRing Y).property
              (structureSheafRing X).property).toOplaxMonoidal)
            (pullbackFunctor f) ((pushforwardFunctor f).obj M) ((pushforwardFunctor f).obj N) ≫
          ((pullbackAdjunction f).counit.app M ⊗ₘ (pullbackAdjunction f).counit.app N)) :=
  rfl

/-- **The unit morphism of the lax monoidal direct image is an adjoint transpose**: the oplax
unit morphism of the inverse image, transposed across `f^* ⊣ f_*`. -/
theorem epsilon_pushforwardFunctorLaxMonoidal_eq
    (_radj : (SheafOfModules.pushforward.{u} (sheafRingHom (F := opensMap f)
      (O := Y.presheaf) (P := X.presheaf) f.hom.c
      (structureSheafRing Y).property
      (structureSheafRing X).property)).IsRightAdjoint) :
    Functor.LaxMonoidal.ε (self := pushforwardFunctorLaxMonoidal f) (pushforwardFunctor f) =
      (pullbackAdjunction f).homEquiv _ _
        (Functor.OplaxMonoidal.η
          (self := (Stacks.PullbackMonoidalSite.pullbackStrictMonoidal (F := opensMap f)
            (O := Y.presheaf) (P := X.presheaf) f.hom.c
            (structureSheafRing Y).property
            (structureSheafRing X).property).toOplaxMonoidal)
          (pullbackFunctor f)) :=
  rfl

/-- **The unit morphism of the lax monoidal direct image at a continuous functor of sites is an
adjoint transpose.** This is the unit analogue of
`Stacks.DifferentialGradedPullbackConstruction.mu_pushforwardLaxMonoidal`, stated here because
that file states only the tensorator. -/
theorem epsilon_pushforwardLaxMonoidal_eq
    (radj : (SheafOfModules.pushforward.{u} (sheafRingHom (F := opensMap f)
      (O := Y.presheaf) (P := X.presheaf) f.hom.c
      (structureSheafRing Y).property
      (structureSheafRing X).property)).IsRightAdjoint) :
    Functor.LaxMonoidal.ε
        (self := Stacks.DifferentialGradedPullbackConstruction.pushforwardLaxMonoidal
          (F := opensMap f) (Osharp := Y.sheaf) (Psharp := X.sheaf) (radj := radj) f.hom.c
          (structureSheafRing Y).property (structureSheafRing X).property)
        (SheafOfModules.pushforward.{u} (inverseImageRingHom (F := opensMap f)
          (Osharp := Y.sheaf) (Psharp := X.sheaf) f.hom.c
          (structureSheafRing Y).property (structureSheafRing X).property)) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom (F := opensMap f)
          (O := Y.presheaf) (P := X.presheaf) f.hom.c
          (structureSheafRing Y).property
          (structureSheafRing X).property)).homEquiv _ _
        (Functor.OplaxMonoidal.η
          (self := (Stacks.PullbackMonoidalSite.pullbackStrictMonoidal (F := opensMap f)
            (O := Y.presheaf) (P := X.presheaf) f.hom.c
            (structureSheafRing Y).property
            (structureSheafRing X).property).toOplaxMonoidal)
          (Stacks.PullbackMonoidalSite.pullbackStrict (F := opensMap f)
            (O := Y.presheaf) (P := X.presheaf) f.hom.c
            (structureSheafRing Y).property
            (structureSheafRing X).property)) :=
  rfl

attribute [local instance] pushforwardFunctorLaxMonoidal

/-- Applying a morphism after a section formula: if `a = b = c` and `c` sends `z` to `w`, then
`g ∘ a` sends `z` to `g w`. -/
private theorem map_app_congr {R : Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u}}
    {M N P : SheafOfModules.{u} R} (g : N ⟶ P) {a b c : M ⟶ N} (hab : a = b) (hbc : b = c)
    (U : (Opens ↥X)ᵒᵖ) (z : M.val.obj U) {w : N.val.obj U} (h : c.val.app U z = w) :
    g.val.app U (a.val.app U z) = g.val.app U w :=
  congrArg _ ((SheafOfModules.hom_congr_app_apply hab U z).trans
    ((SheafOfModules.hom_congr_app_apply hbc U z).trans h))

/-- **The multiplication of `f_*A` on two local sections over `U` is the multiplication of `A`
read over `f⁻¹U`.** This is the section formula for the lax monoidal tensorator of the direct
image of sheaves of modules along a morphism of ringed spaces: the sections of `(f_*A)_n` over
`U` are the sections of `A_n` over `f⁻¹U` on the nose, and multiplying two of them in `f_*A` is
multiplying them in `A`. -/
theorem pushforwardGradedAlgebra_mul_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)) (i j : ℤ)
    (U : (Opens Y.carrier)ᵒᵖ)
    (x : ((pushforwardFunctor f).obj (A.piece i)).val.obj U)
    (y : ((pushforwardFunctor f).obj (A.piece j)).val.obj U) :
    ((pushforwardGradedAlgebra f A).mul i j).app U x y =
      (A.mul i j).app ((opensMap f).op.obj U) x y := by
  refine Eq.trans (transport_mul_app (pushforwardFunctor f) A
    (structureSheafRing X).property (structureSheafRing Y).property i j U x y) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Functor.LaxMonoidal.μ (pushforwardFunctor f) (A.piece i) (A.piece j))
    ((pushforwardFunctor f).map (mulSheaf A i j)) U _) ?_
  refine (map_app_congr _ (mu_pushforwardFunctorLaxMonoidal_eq f
      (isRightAdjoint_pushforward_sheafRingHom f) (A.piece i) (A.piece j))
    (mu_pushforwardLaxMonoidal (F := opensMap f) (Osharp := Y.sheaf) (Psharp := X.sheaf)
      (radj := isRightAdjoint_pushforward_sheafRingHom f) f.hom.c
      (structureSheafRing Y).property (structureSheafRing X).property
      (A.piece i) (A.piece j)).symm U _
    (isPushforwardMuSections (F := opensMap f) (Osharp := Y.sheaf) (Psharp := X.sheaf)
      (radj := isRightAdjoint_pushforward_sheafRingHom f) f.hom.c
      (structureSheafRing Y).property (structureSheafRing X).property
      (A.piece i) (A.piece j) U x y)).trans ?_
  exact mulSheaf_unit A i j ((opensMap f).op.obj U) x y

/-- **The unit of `f_*A` over `U` is the unit of `A` read over `f⁻¹U`.** This is the section
formula for the unit morphism of the lax monoidal direct image. -/
theorem pushforwardGradedAlgebra_one_eval
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X))
    (U : (Opens Y.carrier)ᵒᵖ) :
    (pushforwardGradedAlgebra f A).one.eval U = A.one.eval ((opensMap f).op.obj U) := by
  have h : (pushforwardGradedAlgebra f A).one.eval U =
      ((pushforwardFunctor f).map (oneHom A)).val.app U
        ((Functor.LaxMonoidal.ε (pushforwardFunctor f)).val.app U
          (1 : (structureRingSheaf Y).obj.obj U)) :=
    rfl
  refine h.trans ?_
  refine (map_app_congr _ (epsilon_pushforwardFunctorLaxMonoidal_eq f
      (isRightAdjoint_pushforward_sheafRingHom f))
    (epsilon_pushforwardLaxMonoidal_eq f (isRightAdjoint_pushforward_sheafRingHom f)).symm U _
    (isPushforwardEpsilonSections (F := opensMap f) (Osharp := Y.sheaf) (Psharp := X.sheaf)
      (radj := isRightAdjoint_pushforward_sheafRingHom f) f.hom.c
      (structureSheafRing Y).property (structureSheafRing X).property U)).trans ?_
  exact (oneHom_val_app A ((opensMap f).op.obj U) 1).trans (one_smul _ _)

end Stacks.PushforwardGradedAlgebra

end
