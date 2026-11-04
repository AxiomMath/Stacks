module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackSheafDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Inertia
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaIsStack
public import StacksFrontier.CategoryTheory.RelativeInertia

/-!
# The inertia stack of `[[X/G]]` is a stack

Let `X` be a sheaf on `(Sch/S)_fppf` with an action of an abstract group `G`. The quotient
`[[X/G]]` of Stacks 0371 is a stack in groupoids
(`AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStack`). This file shows that its
inertia `I_{[X/G]}` (Stacks 034I, `CategoryTheory.AbsoluteInertia`) is a stack as well — the
case of `[[X/G]]` of Stacks 036Y (1).

## Main results

* `AlgebraicGeometry.AbstractGroupQuotientStack.inertia_isStack`: `I_{[X/G]}` is a stack over
  `(Sch/S)_fppf`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace AbstractGroupQuotientStack

universe t z w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X}

section Inertia

variable (B S hS G X ρ) in
/-- The inertia `I_{[X/G]}` of `[[X/G]]`. -/
abbrev Inertia := AbsoluteInertia
  (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ BigFppfOver B S hS)

/-- The forgetful functor from the relative inertia of `[[X/G]]` to `[[X/G]]` is faithful. -/
instance π_faithful :
    (RelativeInertia.π (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _)).Faithful
    where
  map_injective h := RelativeInertiaHom.ext h

/-- The automorphism of an object of `I_{[X/G]}` lies over the identity of the site. -/
lemma auto_base (Z : Inertia.{t} B S hS G X ρ) : Z.auto.hom.base = 𝟙 Z.obj.base := Z.cond

/-- The structure functor of the inertia is fibred in groupoids (Stacks 042I). -/
lemma inertia_isFiberedInGroupoids :
    (relativeInertiaStruct (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _)
      projection).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.absoluteInertia _ projection_isFiberedInGroupoids

/-- **Stacks 036Y (1) for `[[X/G]]`.** If `X` is a sheaf on `(Sch/S)_fppf`, the inertia
`I_{[X/G]}` of `[[X/G]]`, with torsors whose sections lie in a universe at least that of the
objects of the site, is a stack over `(Sch/S)_fppf`. -/
theorem inertia_isStack (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (relativeInertiaStruct
      (projection : AbstractGroupQuotientStack.{max (u + 1) t} B S hS G X ρ ⥤ _)
      projection).IsStack (BigFppfOver.topology B S hS) :=
  RelativeInertia.isStack_toBase (projection_isStack hX)

end Inertia

end AbstractGroupQuotientStack

end AlgebraicGeometry
