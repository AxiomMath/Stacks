module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperSurjectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidOfStack
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Descent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StackOfZariskiProper
public import StacksFrontier.CategoryTheory.FiberedCategory.CoGrothendieckPullbackPseudofunctor

/-!
# Small étale sheaves form a stack in groupoids on the big h site

Let `S` be a scheme. Stacks 0GF5 says that the category fibred in groupoids
`p : 𝒮 ⟶ (Sch/S)_h` whose fibre over `U` is the category `Sh(U_étale)` of sheaves on the small
étale site of `U` is a stack in groupoids.

## Main definitions

* `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor`: the pseudofunctor `U ↦ Sh(U_étale)` on
  the big h category over `S`, with the inverse images along small étale base change.
* `AlgebraicGeometry.BigHOver.EtaleSheafFibred` and
  `AlgebraicGeometry.BigHOver.etaleSheafProjection`: its Grothendieck construction, the fibred
  category whose fibre over `U` is `Sh(U_étale)`.
* `AlgebraicGeometry.BigHOver.EtaleSheafGroupoid` and
  `AlgebraicGeometry.BigHOver.etaleSheafGroupoidProjection`: the associated category fibred in
  groupoids (Stacks 03WQ), with the same objects and the strongly cartesian morphisms.

## Main results

* `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor_isEquivalence_of_properFP`: Stacks 0GF0
  read on the big h site, descent along a proper surjection.
* `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor_isEquivalence_of_zariski`: descent along a
  Zariski covering, by the glueing of sheaves on the small étale site (Stacks 04TR).
* `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor_isStack` and
  `AlgebraicGeometry.BigHOver.etaleSheafProjection_isStack`: the pseudofunctor and its
  Grothendieck construction are stacks for the h topology.
* `AlgebraicGeometry.BigHOver.isStackInGroupoids_etaleSheafGroupoid`: **Stacks 0GF5**.

## Implementation notes

The small étale sites are those of a big étale site `E` whose cutoff is at least the cutoff of
the big h site `B`, so that every scheme of `B` is a scheme of `E`.

The source checks the three conditions of Stacks 0EX9: the Zariski stack condition, descent along
a flat proper surjection of finite presentation onto an affine (by Stacks 0GF0 or 0GF2), and the
almost blowup squares (by Stacks 0GF4). Since Stacks 0GF0 gives descent along every proper
surjection, the almost blowup squares are not needed: a pseudofunctor on `(Sch/S)_h` which has
effective descent along Zariski coverings and along proper surjections of finite presentation is
a stack for the h topology, by `AlgebraicGeometry.BigHOver.isStack_of_zariski_of_properFP`, the
stack analogue of the sufficiency direction of Stacks 0EU5. The fibred category of the statement
is the Grothendieck construction, which is a stack by
`CategoryTheory.Pseudofunctor.CoGrothendieck.isStack_forget_of_isStack`, and the associated
category fibred in groupoids is a stack in groupoids by Stacks 03YI.

The fibres of `AlgebraicGeometry.BigHOver.EtaleSheafGroupoid` are the groupoids of sheaves on the
small étale sites and their isomorphisms: a stack *in groupoids* is fibred in groupoids by
definition, and the source's phrase "whose fibre category over `U` is `Sh(U_étale)`" is read as
the category fibred in groupoids associated to the fibred category of sheaves (Stacks 03WQ). The
stronger statement that the fibred category of sheaves itself is a stack is
`AlgebraicGeometry.BigHOver.etaleSheafProjection_isStack`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

/-- The direct image of sheaves of sets along a small étale base change is a right adjoint. -/
public instance smallEtaleSheafPushforward_isRightAdjoint (E : BigEtaleSite.{u}) (S T : E.Scheme)
    (f : T ⟶ S) :
    ((smallEtaleBaseChange E f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology E S.obj S.property)
      (SmallEtale.topology E T.obj T.property)).IsRightAdjoint :=
  ⟨_, ⟨(smallEtaleBaseChange E f).sheafAdjunctionContinuous (Type (u + 1)) _ _⟩⟩

/-- The pseudofunctor of small étale sheaves of sets built from the bicategory of adjunctions is
the pseudofunctor of small étale inverse images built from the left adjoints of the direct
images. -/
public theorem smallEtaleSheafInverseImagePseudofunctor_eq_gluing (E : BigEtaleSite.{u}) :
    smallEtaleSheafInverseImagePseudofunctor E =
      SmallEtaleGluing.pseudofunctor E (Type (u + 1)) := by
  refine Pseudofunctor.ext_of_locallyDiscrete _ _ (fun _ ↦ rfl) (fun f ↦ ?_) (fun f g ↦ ?_)
  · rfl
  · apply heq_of_eq
    rfl

namespace BigHOver

variable (B : BigHSite.{u}) (E : BigEtaleSite.{u}) (hBE : B.cutoff ≤ E.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor from the big h category over `S` to the category of schemes of a big étale site
with a larger cutoff: forget the structure morphism to `S`. -/
public def toBigEtaleSite : BigHOver B S hS ⥤ E.Scheme :=
  Over.forget (B.obj S hS) ⋙ ObjectProperty.ιOfLE (fun _ h ↦ lt_of_lt_of_le h hBE)

/-- **The pseudofunctor of small étale sheaves on `(Sch/S)_h`.** Its fibre over an object `U` is
the category of sheaves of sets on the small étale site of the underlying scheme of `U`, and its
transition functors are the inverse images along small étale base change. -/
public abbrev etaleSheafPseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat :=
  (smallEtaleSheafInverseImagePseudofunctor E).restrict (toBigEtaleSite B E hBE S hS)

/-- The fibre of `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor` over `U` is the category of
sheaves on the small étale site of the underlying scheme of `U`. -/
public theorem etaleSheafPseudofunctor_obj (U : BigHOver B S hS) :
    (etaleSheafPseudofunctor B E hBE S hS).obj (.mk (op U)) =
      Cat.of (Sheaf (SmallEtale.topology E ((BigHOver.toScheme B S hS).obj U)
        (lt_of_lt_of_le U.left.property hBE)) (Type (u + 1))) :=
  rfl

/-- **The fibred category of small étale sheaves on `(Sch/S)_h`**: the Grothendieck construction
of `AlgebraicGeometry.BigHOver.etaleSheafPseudofunctor`. An object is an object `U` of the big h
category over `S` together with a sheaf on the small étale site of `U`. -/
public abbrev EtaleSheafFibred :=
  Pseudofunctor.CoGrothendieck (etaleSheafPseudofunctor B E hBE S hS)

/-- The projection of the fibred category of small étale sheaves to `(Sch/S)_h`. -/
public abbrev etaleSheafProjection : EtaleSheafFibred B E hBE S hS ⥤ BigHOver B S hS :=
  Pseudofunctor.CoGrothendieck.forget _

/-- The fibre of the projection over `U` is equivalent to the category of sheaves on the small
étale site of the underlying scheme of `U`. -/
public def etaleSheafProjectionFiberEquivalence (U : BigHOver B S hS) :
    Sheaf (SmallEtale.topology E ((BigHOver.toScheme B S hS).obj U)
        (lt_of_lt_of_le U.left.property hBE)) (Type (u + 1)) ≌
      (etaleSheafProjection B E hBE S hS).Fiber U :=
  (Functor.Fiber.inducedFunctor
    (Pseudofunctor.CoGrothendieck.comp_const (etaleSheafPseudofunctor B E hBE S hS)
      U)).asEquivalence

public instance :
    (stronglyCartesianOver (etaleSheafProjection B E hBE S hS)).IsMultiplicative :=
  stronglyCartesianOver_isMultiplicative _

/-- **The category fibred in groupoids of small étale sheaves on `(Sch/S)_h`** (Stacks 03WQ):
the objects are those of `AlgebraicGeometry.BigHOver.EtaleSheafFibred` and the morphisms are its
strongly cartesian morphisms. Its fibre over `U` is the groupoid of sheaves on the small étale
site of `U` and their isomorphisms. -/
public abbrev EtaleSheafGroupoid :=
  WideSubcategory (stronglyCartesianOver (etaleSheafProjection B E hBE S hS))

/-- The projection of the category fibred in groupoids of small étale sheaves to `(Sch/S)_h`. -/
public abbrev etaleSheafGroupoidProjection : EtaleSheafGroupoid B E hBE S hS ⥤ BigHOver B S hS :=
  wideSubcategoryInclusion _ ⋙ etaleSheafProjection B E hBE S hS

public instance preservesPullbacks_toBigEtaleSite :
    PreservesLimitsOfShape WalkingCospan (toBigEtaleSite B E hBE S hS) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan E.cutoff
  have h : schemeSizeBelow B.cutoff ≤ schemeSizeBelow E.cutoff := fun _ h ↦ lt_of_lt_of_le h hBE
  have : PreservesLimitsOfShape WalkingCospan (ObjectProperty.ιOfLE h ⋙ E.inclusion) :=
    preservesLimitsOfShape_of_natIso (ObjectProperty.ιOfLECompιIso h).symm
  have : PreservesLimitsOfShape WalkingCospan (ObjectProperty.ιOfLE h) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ E.inclusion
  dsimp only [toBigEtaleSite]
  infer_instance

/-- **Stacks 0GF0 on the big h site.** Descent of small étale sheaves along a proper
surjection of the site is effective. -/
public theorem etaleSheafPseudofunctor_isEquivalence_of_properFP {X Y : BigHOver B S hS}
    (g : Y ⟶ X) (hproper : IsProper ((BigHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map g)) :
    ((etaleSheafPseudofunctor B E hBE S hS).toDescentData (fun _ : Unit ↦ g)).IsEquivalence := by
  rw [Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves]
  have : Surjective (E.inclusion.map ((toBigEtaleSite B E hBE S hS).map g)) := hsurj
  have : IsProper (E.inclusion.map ((toBigEtaleSite B E hBE S hS).map g)) := hproper
  exact
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
    E _ (fun f g g' f' sq _ ↦
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)

/-- **Zariski descent of small étale sheaves on the big h site.** -/
public theorem etaleSheafPseudofunctor_isEquivalence_of_zariski {X : BigHOver B S hS}
    (Ez : PreZeroHypercover.{u + 1} X)
    (hEz : (Ez.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X)) :
    ((etaleSheafPseudofunctor B E hBE S hS).toDescentData Ez.f).IsEquivalence := by
  rw [Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves,
    smallEtaleSheafInverseImagePseudofunctor_eq_gluing]
  rw [Scheme.presieve₀_mem_precoverage_iff] at hEz
  obtain ⟨hsurj, hopen⟩ := hEz
  let X' := (toBigEtaleSite B E hBE S hS).obj X
  let V : Ez.I₀ → SmallEtale E X'.1 X'.property := fun k ↦
    ⟨Over.mk ((toBigEtaleSite B E hBE S hS).map (Ez.f k)), by
      have : IsOpenImmersion (E.inclusion.map ((toBigEtaleSite B E hBE S hS).map (Ez.f k))) :=
        hopen k
      show Etale (E.inclusion.map ((toBigEtaleSite B E hBE S hS).map (Ez.f k)))
      infer_instance⟩
  have hV : Sieve.ofArrows V (fun k ↦ (SmallEtale.finalIsTerminal E X'.obj X'.property).from
      (V k)) ∈
      SmallEtale.topology E X'.obj X'.property (SmallEtale.final E X'.obj X'.property) := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    obtain ⟨k, y, hy⟩ := hsurj x
    refine ⟨V k, _, Sieve.ofArrows_mk _ _ k, y, ?_⟩
    have hw : ((SmallEtale.finalIsTerminal E X'.obj X'.property).from (V k)).hom.left =
        (toBigEtaleSite B E hBE S hS).map (Ez.f k) := by
      have h := Over.w ((SmallEtale.finalIsTerminal E X'.obj X'.property).from (V k)).hom
      simpa [SmallEtale.final, V] using h
    show (E.inclusion.map
      ((SmallEtale.finalIsTerminal E X'.obj X'.property).from (V k)).hom.left) y = x
    rw [hw]
    exact hy
  exact SmallEtaleGluing.isEquivalence_toDescentData E (Type (u + 1)) X' V hV

/-- **Small étale sheaves form a stack for the h topology**, as a pseudofunctor on `(Sch/S)_h`. -/
public theorem etaleSheafPseudofunctor_isStack :
    (etaleSheafPseudofunctor B E hBE S hS).IsStack (BigHOver.topology B S hS) :=
  isStack_of_zariski_of_properFP
    (fun _ Ez hEz ↦ etaleSheafPseudofunctor_isEquivalence_of_zariski B E hBE S hS Ez hEz)
    (fun _ _ g hp hs _ ↦ etaleSheafPseudofunctor_isEquivalence_of_properFP B E hBE S hS g hp hs)

/-- **The fibred category of small étale sheaves is a stack for the h topology** (Stacks 026F). -/
public theorem etaleSheafProjection_isStack :
    (etaleSheafProjection B E hBE S hS).IsStack (BigHOver.topology B S hS) :=
  have := etaleSheafPseudofunctor_isStack B E hBE S hS
  Pseudofunctor.CoGrothendieck.isStack_forget_of_isStack.{u, u + 1, u + 1, u + 2} _

/-- **Stacks 0GF5.** The category fibred in groupoids over the big h site `(Sch/S)_h` whose fibre
over `U` is the category of sheaves on the small étale site of `U` is a stack in groupoids. -/
@[stacks 0GF5]
public theorem isStackInGroupoids_etaleSheafGroupoid :
    (etaleSheafGroupoidProjection B E hBE S hS).IsStackInGroupoids.{w}
      (BigHOver.topology B S hS) :=
  (etaleSheafProjection_isStack B E hBE S hS).isStackInGroupoids_stronglyCartesianOver

end BigHOver

end AlgebraicGeometry

end
