module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of topoi

A *morphism of topoi* `f : E → F` between Grothendieck topoi is a pair of adjoint functors
`f⁻¹ ⊣ f_*` with `f_* : E ⥤ F` and `f⁻¹ : F ⥤ E` such that `f⁻¹` is left exact. It is stated
for arbitrary categories, so that it applies both to sheaf categories `Sheaf J A` and to the
category of sets in the guise of `Type w` (which is `Sh(pt)`).

## Main definitions

* `MorphismOfTopoi`: a morphism of topoi, i.e. an adjoint pair whose left adjoint is left exact.
* `MorphismOfTopoi.id`: the identity morphism of topoi.
* `MorphismOfTopoi.comp`: composition of morphisms of topoi.

## Main results

* `Adjunction.comp_homEquiv_apply`: transposing along a composite adjunction is transposing
  twice.
* `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`: a morphism of sites `f : D → C`,
  given by a continuous functor `u : C ⥤ D` whose sheaf pullback `u_s` is exact, induces a
  morphism of topoi `Sh(D) → Sh(C)` with `f⁻¹ = u_s` and `f_* = u^s`.
-/

@[expose] public section

open CategoryTheory Limits

/-- A *morphism of topoi* `f : E → F` is the data of a *pushforward* `f_* : E ⥤ F`, an *inverse
image* `f⁻¹ : F ⥤ E`, an adjunction `f⁻¹ ⊣ f_*`, and the requirement that `f⁻¹` be left exact, i.e.
commute with finite limits.

Note the direction: `E` is the source topos and `F` the target, so that a morphism
`f : Sh(D) → Sh(C)` is a `MorphismOfTopoi (Sheaf K A) (Sheaf J A)`. -/
structure MorphismOfTopoi.{v, u, v', u'} (E : Type u) [Category.{v} E]
    (F : Type u') [Category.{v'} F] where
  /-- The direct image (pushforward) `f_* : E ⥤ F`. -/
  pushforward : E ⥤ F
  /-- The inverse image `f⁻¹ : F ⥤ E`. -/
  inverseImage : F ⥤ E
  /-- The inverse image is left adjoint to the pushforward. -/
  adj : inverseImage ⊣ pushforward
  /-- The inverse image is left exact: it commutes with finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits inverseImage

namespace MorphismOfTopoi

universe v u v' u' v'' u''

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  {G : Type u''} [Category.{v''} G]

/-- The identity morphism of topoi: pushforward and inverse image are both the identity
functor, compared by the identity adjunction. It is the geometric morphism underlying a change
of structure sheaf on a fixed site.

Note that this declaration shadows `_root_.id` inside the `MorphismOfTopoi` namespace, so a bare
`id` there now resolves here; `MorphismOfTopoiRing.lean` uses `_root_.id` for that reason. -/
@[sga "4 IV 3.3.1"]
def id (T : Type u) [Category.{v} T] : MorphismOfTopoi T T where
  pushforward := 𝟭 T
  inverseImage := 𝟭 T
  adj := Adjunction.id
  preservesFiniteLimits := inferInstance

/-- Composition of morphisms of topoi: the pushforwards compose covariantly and the inverse
images contravariantly, and the composite inverse image is again left exact because a
composition of left exact functors is left exact. -/
@[simps, sga "4 IV 3.3.1"]
def comp (g : MorphismOfTopoi F G) (f : MorphismOfTopoi E F) : MorphismOfTopoi E G where
  pushforward := f.pushforward ⋙ g.pushforward
  inverseImage := g.inverseImage ⋙ f.inverseImage
  adj := g.adj.comp f.adj
  preservesFiniteLimits :=
    have := g.preservesFiniteLimits
    have := f.preservesFiniteLimits
    comp_preservesFiniteLimits _ _

end MorphismOfTopoi

/-- Transposing along a composite adjunction is transposing twice, evaluated at a morphism. -/
theorem Adjunction.comp_homEquiv_apply {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ E} {R₂ : E ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {X : A} {Y : E} (g : L₂.obj (L₁.obj X) ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y g = adj₁.homEquiv X _ (adj₂.homEquiv _ Y g) := by
  simp [Adjunction.comp_homEquiv]

universe w

/-- Given a morphism of sites `f : D → C`, i.e. a continuous functor `u : C ⥤ D` whose associated
functor `u_s` on sheaves of sets is exact, the pair `(f⁻¹ = u_s, f_* = u^s)` is a morphism of topoi
`Sh(D) → Sh(C)`. Here `u_s` is `Functor.sheafPullback`, `u^s` is
`Functor.sheafPushforwardContinuous` and the adjunction is `Functor.sheafAdjunctionContinuous`. -/
@[stacks 00XC]
noncomputable def CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi
    {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    (h : u.IsMorphismOfSites J K) :
    MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)) :=
  haveI := h.isContinuous
  { pushforward := u.sheafPushforwardContinuous (Type w) J K
    inverseImage := u.sheafPullback (Type w) J K
    adj := u.sheafAdjunctionContinuous (Type w) J K
    preservesFiniteLimits := h.preservesFiniteLimits }
