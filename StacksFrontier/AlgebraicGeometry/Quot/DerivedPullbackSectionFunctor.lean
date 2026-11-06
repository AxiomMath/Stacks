module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# The sections of a derived pullback on the test schemes over an algebraic space

Let `S` be a scheme, let `B` be an algebraic space over `S` and let `K` be a pseudo-coherent
object of `D(𝒪_B)`.  Stacks 08JX studies two functors on the test schemes over `B`,

> `(g : T → B) ↦ H⁰(T, H⁰(Lg^*K))`  and  `(g : T → B) ↦ H⁰(T, Lg^*K)`,

and asserts, under a vanishing hypothesis on the cohomology of the derived pullbacks, that each
is an algebraic space affine and of finite presentation over `B` — and, for the second, that `K`
is moreover perfect and locally of Tor amplitude in `[0, b]`.

This file constructs the **second** functor, together with its projection to `B`, and states both
vanishing hypotheses and the conclusions.  Nothing in the chapter constructed either functor
before.

## Main definitions

* `CategoryTheory.PullbackData`: **a pullback pseudofunctor datum**, and
  `CategoryTheory.PullbackData.IsCoherent` its coherence.  This is the abstract shape of the
  pseudofunctoriality of an inverse image, recorded so that the relative Hom construction is
  carried out once and for all.
* `CategoryTheory.PullbackData.relHomFunctor`: **the relative Hom functor of a pullback
  pseudofunctor datum on the test objects over an object**, the generic construction.
* `AlgebraicGeometry.Space.derivedPull`: `Lf^*` for a morphism of algebraic spaces, with the
  existence premise discharged from a hypothesis rather than carried as an instance argument.
* `AlgebraicGeometry.Space.DerivedPullbackCoherence`: the pseudofunctoriality of the derived
  pullback, **as data** — the unit law, the composition comparison of Stacks 0D6D, the
  identification `Lf^*𝒪_Y ≅ 𝒪_X`, and the coherence of the first two.
* `AlgebraicGeometry.Space.derivedPullbackHomFunctor`: the relative derived Hom functor of two
  objects of `D(𝒪_B)` on the test schemes over `B`.
* `AlgebraicGeometry.Space.derivedPullbackSectionFunctor`: **the functor of Stacks 08JX,
  part (2)**, `(g : T → B) ↦ H⁰(T, Lg^*K)`.
* `AlgebraicGeometry.Space.degreeZeroPullbackSections`: **the value of the functor of Stacks
  08JX, part (1)**, the group `H⁰(T, H⁰(Lg^*K))`.
* `AlgebraicGeometry.Space.HasVanishingDegreeNegOneDerivedPullback` and
  `AlgebraicGeometry.Space.HasVanishingNegativeDerivedPullback`: the hypotheses of the two parts.

## Main results

* `AlgebraicGeometry.Space.derivedPullbackSectionFunctor_obj_equiv`: the value of the functor of
  part (2) at a test scheme is `Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)`, the degree-zero hypercohomology of
  `Lg^*K`.
* `AlgebraicGeometry.Space.derivedPullbackSectionFunctorToBase`: **the projection to `B`** of the
  functor of part (2).
* `AlgebraicGeometry.Space.degreeZeroPullbackSections_equiv`: the value of the functor of
  part (1) read as `Hom_{𝒪_T}(𝒪_T, H⁰(Lg^*K))`.
* `AlgebraicGeometry.Space.HasVanishingNegativeDerivedPullback.hasVanishingDegreeNegOne`: the
  hypothesis of part (2) implies the hypothesis of part (1).

## Where the conclusions of the tag are proved

The conclusions of both parts are named here and proved elsewhere in the chapter:
`isAffineFinitePresentationSectionFunctor_of_hasVanishingNegativeDerivedPullback`
(`StacksFrontier/AlgebraicGeometry/Quot/DerivedSectionsFunctor.lean`) is part (2) for the functor
built here, `isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor`
(`StacksFrontier/AlgebraicGeometry/Quot/DegreeZeroSectionsRepresentable.lean`) is part (1), and
`isPerfect_and_locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback`
(`StacksFrontier/AlgebraicGeometry/Quot/PerfectOfVanishingPullbacks.lean`) is the perfectness of
`K` together with its local Tor amplitude in `[0, b]`.

**The functor of part (1).**  Only its values are constructed here, not its restriction maps.
The degree-zero cohomology of a derived pullback is not the pullback of the degree-zero
cohomology — that identification is precisely the base-change comparison recorded as
`AlgebraicGeometry.Space.BottomRankStratum.BottomRankBaseChange` — so the restriction map along a
morphism of test schemes would need a comparison `g^*H⁰(E) ⟶ H⁰(Lg^*E)`, for which this
development has no declaration.  Part (1) is proved instead on the degree-zero sections functor
of a K-flat complex representing `K`, which takes these values by
`AlgebraicGeometry.Space.degreeZeroSectionsEquiv`.  The functor of part (2) needs no such
comparison, which is the reason it and not the functor of part (1) is the one built here:
degree-zero hypercohomology is a Hom *in the derived category*, so derived inverse image of
morphisms is all its functoriality needs.

## Implementation notes

**Why the pseudofunctoriality is data.**  The composition comparison `L(f ≫ g)^* ≅ Lg^* ∘ Lf^*`
of Stacks 0D6D is taken as data rather than built in place, so that a consumer may supply its own
inverse images, exactly as `AlgebraicGeometry.Space.ModulePushforwardCoherence` does for the
pseudofunctoriality of Stacks 03LU of the *underived* inverse image, and as the relative Hom
functor of Stacks 08JT consumes it in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.  For the derived pullback of
`𝒪`-modules on algebraic spaces the datum is built with no hypothesis by
`AlgebraicGeometry.Space.derivedPullbackCoherence`
(`StacksFrontier/AlgebraicGeometry/Quot/SmallEtaleDerivedPullbackCoherence.lean`), its composition
comparison coming from the ringed-topos Stacks 0D6D of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/CompositionOnRingedTopoi.lean`.

**Why the calculus is generic.**  The triangle calculus and the two functor laws are proved for
an abstract `CategoryTheory.PullbackData` rather than for the derived pullback, because the
derived categories of modules on algebraic spaces are expensive to compare: at the abstract level
the two laws are `CategoryTheory.Functor.conjHom_id` and
`CategoryTheory.Functor.conjHom_comp` applied to a coherence equation, and the instantiation is a
syntactic match.  The same two generic lemmas are what
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean` uses for Stacks 08JT.

**The existence premise.**  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` carries
`CategoryTheory.Functor.HasLeftDerivedFunctor` as an instance argument.  It is threaded through
this file as `AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks`, as it is in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BottomRankStratum.lean`, and the theorem
`AlgebraicGeometry.Space.hasDerivedModulePullbacks`
(`StacksFrontier/AlgebraicGeometry/Quot/DerivedPullbackPseudofunctor.lean`) discharges it for every
morphism of algebraic spaces.

**The value universe.**  The sections of a sheaf of `𝒪`-modules on the small étale site of an
algebraic space, and the Hom sets of `D(𝒪)`, both live in `Type (u + 1)`, which is the value
universe of `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver`; so the
conclusion predicate applies to both functors with no further universe lift.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]

/-- **A pullback pseudofunctor datum on `A` with fibres `D`**: a contravariant assignment of a
functor `D b ⥤ D a` to each morphism `a ⟶ b`, together with the comparison of the inverse image
along an identity with the identity functor and the comparison of the inverse image along a
composite with the composite of the inverse images. -/
structure PullbackData (A : Type u₁) [Category.{v₁} A] (D : A → Type u₂)
    [∀ a, Category.{v₂} (D a)] where
  /-- The inverse image along a morphism of `A`. -/
  pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a)
  /-- The inverse image along an identity is the identity functor. -/
  idIso : ∀ a : A, pull (𝟙 a) ≅ 𝟭 (D a)
  /-- The inverse image along a composite is the composite of the inverse images. -/
  compIso : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f

namespace PullbackData

variable (P : PullbackData A D)

/-- The inverse image along a morphism `k` presented as a composite `f ≫ g = k`, compared with
the composite of the inverse images along `g` and along `f`.

Taking the composite as a hypothesis rather than writing `f ≫ g` is what lets a consumer indexed
by a category of test objects use the comparison at a morphism that *equals* a composite without
first rewriting. -/
def triangle {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) :
    P.pull k ≅ P.pull g ⋙ P.pull f :=
  eqToIso (congrArg (fun m : a ⟶ c => P.pull m) hk.symm) ≪≫ P.compIso f g

/-- `CategoryTheory.PullbackData.triangle` written out. -/
theorem triangle_eq {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) :
    P.triangle hk =
      eqToIso (congrArg (fun m : a ⟶ c => P.pull m) hk.symm) ≪≫ P.compIso f g :=
  rfl

/-- At the composite itself the comparison is the composition comparison. -/
theorem triangle_rfl {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    P.triangle (f := f) (g := g) rfl = P.compIso f g := by
  rw [triangle_eq]
  simp

/-- Replacing the first factor of the composite by an equal morphism changes the comparison only
by the induced identification of the two inverse images. -/
theorem triangle_congr_left {a b c : A} {f f' : a ⟶ b} (hff : f = f') {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (hk' : f' ≫ g = k) :
    P.triangle hk =
      P.triangle hk' ≪≫ Functor.isoWhiskerLeft (P.pull g)
        (eqToIso (congrArg (fun m : a ⟶ b => P.pull m) hff.symm)) := by
  subst hff
  have hE : P.triangle hk = P.triangle hk' := rfl
  rw [hE]
  simp

/-- **Coherence of a pullback pseudofunctor datum**: the unit law, in the form that identifies
the comparison for a composite whose first factor is an identity, and the associativity law for
three composable morphisms. -/
structure IsCoherent (P : PullbackData A D) : Prop where
  /-- The comparison for `𝟙 a ≫ g` is the unit law. -/
  triangle_id : ∀ {a b : A} (g : a ⟶ b) (hk : 𝟙 a ≫ g = g),
    P.triangle hk = (Functor.rightUnitor (P.pull g)).symm ≪≫
      Functor.isoWhiskerLeft (P.pull g) (P.idIso a).symm
  /-- Breaking the inverse image along a triple composite into three steps through either of the
  two intermediate composites gives the same comparison. -/
  triangle_comp : ∀ {a b c d : A} {f : a ⟶ b} {g : b ⟶ c} {p : c ⟶ d}
      {k : a ⟶ c} {q : b ⟶ d} {r : a ⟶ d}
      (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r),
    P.triangle hkr ≪≫ Functor.isoWhiskerLeft (P.pull p) (P.triangle hk) =
      P.triangle hr ≪≫ Functor.isoWhiskerRight (P.triangle hq) (P.pull f) ≪≫
        Functor.associator (P.pull p) (P.pull g) (P.pull f)

namespace IsCoherent

variable {P}

/-- The associativity law, solved for the comparison along the triple composite.  This is the
shape `CategoryTheory.Functor.conjHom_comp` consumes. -/
theorem triangle_comp' (hP : P.IsCoherent) {a b c d : A} {f : a ⟶ b} {g : b ⟶ c} {p : c ⟶ d}
    {k : a ⟶ c} {q : b ⟶ d} {r : a ⟶ d}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    P.triangle hkr =
      (P.triangle hr ≪≫ Functor.isoWhiskerRight (P.triangle hq) (P.pull f) ≪≫
          Functor.associator (P.pull p) (P.pull g) (P.pull f)) ≪≫
        (Functor.isoWhiskerLeft (P.pull p) (P.triangle hk)).symm := by
  rw [← hP.triangle_comp hk hq hr hkr, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- The unit law with the identity presented as an arbitrary morphism equal to it.  This is the
shape `CategoryTheory.Functor.conjHom_id` consumes. -/
theorem triangle_id' (hP : P.IsCoherent) {a b : A} {e : a ⟶ a} (he : e = 𝟙 a) {g : a ⟶ b}
    (hk : e ≫ g = g) :
    P.triangle hk = (Functor.rightUnitor (P.pull g)).symm ≪≫
      Functor.isoWhiskerLeft (P.pull g)
        ((P.idIso a).symm ≪≫ eqToIso (congrArg (fun m : a ⟶ a => P.pull m) he.symm)) := by
  have hk' : 𝟙 a ≫ g = g := Category.id_comp g
  rw [P.triangle_congr_left he hk hk', hP.triangle_id g hk', Functor.isoWhiskerLeft_trans,
    Iso.trans_assoc]

end IsCoherent

/-- **A cone from a functor to an object**: a morphism `π i ⟶ a₀` for each index, compatible
with the transition morphisms.  The test objects over an object of `A` form such a cone. -/
structure ConeTo {I : Type*} [Category* I] (π : I ⥤ A) (a₀ : A) where
  /-- The structure morphism of the index `i`. -/
  leg : ∀ i : I, π.obj i ⟶ a₀
  /-- The structure morphisms are compatible with the transition morphisms. -/
  w : ∀ {i j : I} (g : i ⟶ j), π.map g ≫ leg j = leg i

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- The set of morphisms between the two inverse images of `M` and `N` along the structure
morphism of a test object. -/
abbrev relHomObj (κ : ConeTo π a₀) (M N : D a₀) (i : I) : Type v₂ :=
  (P.pull (κ.leg i)).obj M ⟶ (P.pull (κ.leg i)).obj N

/-- The inverse image of a morphism of inverse images along a transition morphism of test
objects: its image under the inverse image along `π g`, read through the comparison of the two
structure morphisms. -/
def relHomMap (κ : ConeTo π a₀) (M N : D a₀) {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ M N i) : P.relHomObj κ M N j :=
  Functor.conjHom (P.triangle (κ.w g)) α

/-- The inverse image of a morphism of inverse images along an identity is itself. -/
theorem relHomMap_id (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) (i : I)
    (α : P.relHomObj κ M N i) : P.relHomMap κ M N (𝟙 i) α = α :=
  Functor.conjHom_id _ _ (hP.triangle_id' (π.map_id i) (κ.w (𝟙 i))) α

/-- The inverse image of a morphism of inverse images along a composite is the composite of the
inverse images. -/
theorem relHomMap_comp (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) {k j i : I}
    (g : k ⟶ j) (h : j ⟶ i) (α : P.relHomObj κ M N i) :
    P.relHomMap κ M N (g ≫ h) α = P.relHomMap κ M N g (P.relHomMap κ M N h α) :=
  Functor.conjHom_comp (P.triangle (κ.w h)) (P.triangle (κ.w g)) (P.triangle (κ.w (g ≫ h)))
    (P.triangle (π.map_comp g h).symm)
    (hP.triangle_comp' (π.map_comp g h).symm (κ.w h) (κ.w g) (κ.w (g ≫ h))) α

/-- **The relative Hom functor of a pullback pseudofunctor datum on the test objects over
`a₀`**: it sends a test object `i` to the morphisms `(π i)^*M ⟶ (π i)^*N` between the two inverse
images along the structure morphism of `i`, and a transition morphism to inverse image of
morphisms.

The two functor laws are the unit law and the associativity law of the datum. -/
def relHomFunctor (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) : Iᵒᵖ ⥤ Type v₂ where
  obj i := P.relHomObj κ M N i.unop
  map g := ↾fun α => P.relHomMap κ M N g.unop α
  map_id i := congrArg TypeCat.ofHom (funext fun α => P.relHomMap_id hP κ M N i.unop α)
  map_comp g h :=
    congrArg TypeCat.ofHom (funext fun α => P.relHomMap_comp hP κ M N h.unop g.unop α)

/-- The value of the relative Hom functor at a test object. -/
theorem relHomFunctor_obj (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) (i : I) :
    (P.relHomFunctor hP κ M N).obj (Opposite.op i) = P.relHomObj κ M N i :=
  rfl

/-- The action of the relative Hom functor on a transition morphism. -/
theorem relHomFunctor_map (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) {j i : I}
    (g : j ⟶ i) (α : P.relHomObj κ M N i) :
    (P.relHomFunctor hP κ M N).map (Opposite.op g) α = P.relHomMap κ M N g α :=
  rfl

end PullbackData

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derived pullback as a pullback pseudofunctor datum -/

/-- The derived category of `𝒪`-modules on an algebraic space, as a family indexed by the
algebraic spaces over `S`. -/
abbrev derivedModules (X : AlgebraicSpaces B S hS) :=
  DerivedCategory (Modules.{u, u} B S hS X.1 X.2)

/-- The structure sheaf of an algebraic space as an object of `D(𝒪_X)`, placed in degree
zero. -/
abbrev structureObject (X : AlgebraicSpaces B S hS) : derivedModules B S hS X :=
  (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj (SheafOfModules.unit _)

/-- **The derived pullback `Lf^*` along a morphism of algebraic spaces**, with the existence
premise of `AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks` discharged from
`hL` rather than carried as an instance argument.

This is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, Tag 06YY for the morphism of
small étale ringed topoi of Stacks 03G8. -/
abbrev derivedPull (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    derivedModules B S hS Y ⥤ derivedModules B S hS X :=
  haveI := hL f
  smallEtaleDerivedModulePullback B S hS f

/-- **The pseudofunctoriality of the derived pullback of `𝒪`-modules on algebraic spaces, as
data.**  The unit law `L(𝟙 X)^* ≅ 𝟭`, the composition comparison `L(f ≫ g)^* ≅ Lg^* ∘ Lf^*` of
Stacks 0D6D, the identification `Lf^*𝒪_Y ≅ 𝒪_X` of the pulled-back structure sheaf, and the
coherence of the first two.

This structure takes that data rather than building it, so that a consumer may supply its own
inverse images; it records nothing missing.  For the derived pullback of `𝒪`-modules on algebraic
spaces `AlgebraicGeometry.Space.derivedPullbackCoherence`
(`StacksFrontier/AlgebraicGeometry/Quot/SmallEtaleDerivedPullbackCoherence.lean`) builds the datum
with no hypothesis, its composition comparison coming from the ringed-topos Stacks 0D6D of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/CompositionOnRingedTopoi.lean`. -/
structure DerivedPullbackCoherence (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS) where
  /-- The derived pullback along an identity is the identity functor. -/
  idIso : ∀ X : AlgebraicSpaces B S hS,
    derivedPull B S hS hL (𝟙 X) ≅ 𝟭 (derivedModules B S hS X)
  /-- **Stacks 0D6D.**  The derived pullback along a composite is the composite of the derived
  pullbacks. -/
  compIso : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
    derivedPull B S hS hL (f ≫ g) ≅ derivedPull B S hS hL g ⋙ derivedPull B S hS hL f
  /-- The derived pullback of the structure sheaf is the structure sheaf. -/
  unitPullIso : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    (derivedPull B S hS hL f).obj (structureObject B S hS Y) ≅ structureObject B S hS X
  /-- The unit law and the composition comparison are coherent. -/
  isCoherent : PullbackData.IsCoherent (A := AlgebraicSpaces B S hS)
    { pull := fun {_ _} f => derivedPull B S hS hL f, idIso := idIso, compIso := compIso }

namespace DerivedPullbackCoherence

variable {B S hS} {hL : BottomRankStratum.HasDerivedModulePullbacks B S hS}

/-- The pseudofunctor datum of a coherence datum, whose inverse images are the derived
pullbacks. -/
abbrev toPullbackData (hc : DerivedPullbackCoherence B S hS hL) :
    PullbackData (AlgebraicSpaces B S hS) (derivedModules B S hS) where
  pull := fun {_ _} f => derivedPull B S hS hL f
  idIso := hc.idIso
  compIso := hc.compIso

end DerivedPullbackCoherence

/-! ### The functor on the test schemes -/

variable {B S hS}

/-- The test schemes over an algebraic space, with their structure morphisms, as a cone to it:
the structure morphism of a test scheme is compatible with the transition morphisms, which is the
commuting triangle defining a morphism of test schemes. -/
def schemesOverCone (X : AlgebraicSpaces B S hS) :
    PullbackData.ConeTo
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) X ⋙ schemeSpaceFunctor B S hS) X where
  leg T := T.hom
  w g := CostructuredArrow.w g

variable {hL : BottomRankStratum.HasDerivedModulePullbacks B S hS}
  {X : AlgebraicSpaces B S hS}

/-- The algebraic space of a test scheme over `X`: the scheme of the big fppf site underlying
it, regarded as an algebraic space through the Yoneda embedding. -/
abbrev testSpace (T : SchemesOver X) : AlgebraicSpaces B S hS :=
  (schemeSpaceFunctor B S hS).obj T.left

/-- **The relative derived Hom functor of two objects of `D(𝒪_X)` on the test schemes over
`X`**: it sends a test scheme `g : T → X` to the morphisms `Lg^*M ⟶ Lg^*N` in `D(𝒪_T)`, and a
morphism of test schemes to derived inverse image of morphisms.

Its two functor laws are the unit law and the associativity law of the coherence datum. -/
def derivedPullbackHomFunctor (hc : DerivedPullbackCoherence B S hS hL)
    (M N : derivedModules B S hS X) : (SchemesOver X)ᵒᵖ ⥤ Type (u + 1) :=
  hc.toPullbackData.relHomFunctor hc.isCoherent (schemesOverCone X) M N

/-- The value of the relative derived Hom functor at a test scheme is the set of morphisms
between the two derived pullbacks. -/
theorem derivedPullbackHomFunctor_obj (hc : DerivedPullbackCoherence B S hS hL)
    (M N : derivedModules B S hS X) (T : SchemesOver X) :
    (derivedPullbackHomFunctor hc M N).obj (Opposite.op T) =
      ((derivedPull B S hS hL T.hom).obj M ⟶ (derivedPull B S hS hL T.hom).obj N) :=
  rfl

/-- **The degree-zero hypercohomology functor of Stacks 08JX, part (2)**: the functor sending a
test scheme `g : T → B` to `H⁰(T, Lg^*K)`, read as the derived Hom out of the pulled-back
structure sheaf.

`AlgebraicGeometry.Space.derivedPullbackSectionFunctor_obj_equiv` identifies its value at `T`
with `Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)`, which is that degree-zero hypercohomology group. -/
@[stacks 08JX "the functor of part (2), `(g : T → B) ↦ H⁰(T, Lg^*K)`, on the test schemes \
  over `B`; its value is `Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)` by `derivedPullbackSectionFunctor_obj_equiv`. \
  The datum `hc` -- Stacks 0D6D and the unit law for `L(-)^*` -- is built with no hypothesis by \
  `AlgebraicGeometry.Space.derivedPullbackCoherence`. Its representability is \
  `isAffineFinitePresentationSectionFunctor_of_hasVanishingNegativeDerivedPullback` and the two \
  conclusions about `K` are \
  `isPerfect_and_locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback`."]
def derivedPullbackSectionFunctor (hc : DerivedPullbackCoherence B S hS hL)
    (K : derivedModules B S hS X) : (SchemesOver X)ᵒᵖ ⥤ Type (u + 1) :=
  derivedPullbackHomFunctor hc (structureObject B S hS X) K

/-- **The value of the functor of Stacks 08JX part (2) is the degree-zero hypercohomology
`H⁰(T, Lg^*K) = Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)`.**  The identification is precomposition with the
comparison `Lg^*𝒪_B ≅ 𝒪_T` of the pulled-back structure sheaf. -/
def derivedPullbackSectionFunctor_obj_equiv (hc : DerivedPullbackCoherence B S hS hL)
    (K : derivedModules B S hS X) (T : SchemesOver X) :
    (derivedPullbackSectionFunctor hc K).obj (Opposite.op T) ≃
      (structureObject B S hS (testSpace T) ⟶ (derivedPull B S hS hL T.hom).obj K) :=
  Iso.homCongr (hc.unitPullIso T.hom) (Iso.refl _)

/-- **The projection to the base of the functor of Stacks 08JX part (2)**: the unique morphism
to the functor of points of `X` over itself, which is the terminal functor on the test schemes
over `X`.

This is the morphism to `B` that the source attaches to the functor; on the test schemes over
`B` it is the unique one, the functor of points of `B` over itself being a singleton at every
test scheme. -/
def derivedPullbackSectionFunctorToBase (hc : DerivedPullbackCoherence B S hS hL)
    (K : derivedModules B S hS X) :
    derivedPullbackSectionFunctor hc K ⟶
      spacePointsOver (𝟙 X) ⋙ uliftFunctor.{u + 1, u} where
  app T := ↾fun _ => ⟨⟨testPoint T.unop, rfl⟩⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun _ => ?_
    exact ULift.ext (Subtype.ext (testPoint_naturality g.unop).symm)

/-! ### The functor of part (1), and the two hypotheses -/

/-- **The value at a test scheme of the functor of Stacks 08JX, part (1)**: the group
`H⁰(T, H⁰(Lg^*K))` of global sections of the degree-zero cohomology sheaf of the derived pullback
of `K` along `g : T → B`. -/
@[stacks 08JX "the value at a test scheme `g : T → B` of the functor of part (1), the group \
  `H⁰(T, H⁰(Lg^*K))`. Its restriction maps are not constructed here, for want of a comparison \
  `g^*H⁰(E) ⟶ H⁰(Lg^*E)`; part (1) is proved on the degree-zero sections functor of a K-flat \
  complex representing `K`, which takes these values by \
  `AlgebraicGeometry.Space.degreeZeroSectionsEquiv`."]
abbrev degreeZeroPullbackSections (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (K : derivedModules B S hS X) (T : SchemesOver X) : Type (u + 1) :=
  (BottomRankStratum.pullbackHomology hL K 0 T.hom).sections

/-- **The global sections of the degree-zero cohomology of a derived pullback are the
`𝒪_T`-module homomorphisms out of the structure sheaf.**  This is the sheaf-theoretic reading
`H⁰(T, M) = Hom_{𝒪_T}(𝒪_T, M)` of the value of the functor of part (1). -/
def degreeZeroPullbackSections_equiv
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (K : derivedModules B S hS X) (T : SchemesOver X) :
    (SheafOfModules.unit _ ⟶ BottomRankStratum.pullbackHomology hL K 0 T.hom) ≃
      degreeZeroPullbackSections hL K T :=
  SheafOfModules.unitHomEquiv _

/-- **The hypothesis of Stacks 08JX, part (1)**: for every test scheme `g : T → B` the
cohomology sheaf `H⁻¹(Lg^*K)` is zero. -/
@[stacks 08JX "the hypothesis of part (1): `H⁻¹(Lg^*K) = 0` for every test scheme \
  `g : T → B`. The hypothesis of part (2) is \
  `AlgebraicGeometry.Space.HasVanishingNegativeDerivedPullback`."]
def HasVanishingDegreeNegOneDerivedPullback
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (K : derivedModules B S hS X) : Prop :=
  ∀ T : SchemesOver X, IsZero (BottomRankStratum.pullbackHomology hL K (-1) T.hom)

/-- **The hypothesis of Stacks 08JX, part (2)**: for every test scheme `g : T → B` the
cohomology sheaves `Hⁱ(Lg^*K)` are zero for every `i < 0`. -/
@[stacks 08JX "the hypothesis of part (2): `Hⁱ(Lg^*K) = 0` for every test scheme \
  `g : T → B` and every `i < 0`. The hypothesis of part (1) is \
  `AlgebraicGeometry.Space.HasVanishingDegreeNegOneDerivedPullback`."]
def HasVanishingNegativeDerivedPullback
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (K : derivedModules B S hS X) : Prop :=
  ∀ (T : SchemesOver X) (i : ℤ), i < 0 →
    IsZero (BottomRankStratum.pullbackHomology hL K i T.hom)

/-- **The hypothesis of part (2) implies the hypothesis of part (1).**  Degree `-1` is a
negative degree. -/
theorem HasVanishingNegativeDerivedPullback.hasVanishingDegreeNegOne
    {hL : BottomRankStratum.HasDerivedModulePullbacks B S hS} {K : derivedModules B S hS X}
    (h : HasVanishingNegativeDerivedPullback hL K) :
    HasVanishingDegreeNegOneDerivedPullback hL K :=
  fun T => h T (-1) (by norm_num)

/-! ### The conclusions -/

/-- **The conclusion of Stacks 08JX, part (2), at the functor of part (2)**: the degree-zero
hypercohomology functor is an algebraic space affine and of finite presentation over `B`. -/
abbrev IsAffineFinitePresentationSectionFunctor (hc : DerivedPullbackCoherence B S hS hL)
    (K : derivedModules B S hS X) : Prop :=
  IsAffineFinitePresentationAlgebraicSpaceOver X (derivedPullbackSectionFunctor hc K)

/-- **The first of the two conclusions of Stacks 08JX, part (2), about `K` itself**: `K` is a
perfect object of `D(𝒪_B)` in the sense of Stacks 08G5.

This names the conclusion; it is proved as the first half of
`isPerfect_and_locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback` in
`StacksFrontier/AlgebraicGeometry/Quot/PerfectOfVanishingPullbacks.lean`, by the source's route
through a strictly perfect approximation near every point rather than by the criterion of
Stacks 08G8 or by `AlgebraicGeometry.RingedSite.isPerfect_of_locally`, both of which are pinned
to `AlgebraicGeometry.RingedSite.{0, 0, 0}` while the small étale ringed site of an algebraic
space is `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. -/
abbrev IsPerfectPseudoCoherentObject (K : derivedModules B S hS X) : Prop :=
  (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K

/-- **The hypothesis of Stacks 08JX on `K`**: `K` is a pseudo-coherent object of `D(𝒪_B)` in the
sense of Stacks 08FT. -/
abbrev IsPseudoCoherentObject (K : derivedModules B S hS X) : Prop :=
  (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K

end AlgebraicGeometry.Space

end
