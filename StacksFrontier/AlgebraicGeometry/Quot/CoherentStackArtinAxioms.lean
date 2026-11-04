module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackMorSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation

/-!
# The Artin's-axioms interface of `Coh_{X/Y}`

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB, and let `Coh_{X/Y}` be the category of coherent
sheaves with proper support of that tag.  Two of the Artin's-axioms checks of Section 99.5 of
the source — Stacks 08W8, on the tangent space and the infinitesimal automorphisms at a
finite-type field point, and Stacks 08W9, on the functor of Artin's Axioms, Equation 07X6 —
speak about `Coh_{X/Y}` through the machinery of
`StacksFrontier/Deformation/Artin/`, and every statement of that machinery is phrased for a
functor `p : 𝒳 ⥤ (Sch/S)_fppf` fibred in groupoids.  This file is the single place where
`Coh_{X/Y}` is presented to it: it puts Stacks 08W5 in the shape the machinery consumes, builds
the functor of Equation 07X6 at `Coh_{X/Y}`, builds the predeformation category of a finite-type
field point of `Coh_{X/Y}`, and turns a compatible system of coherent sheaves over the
infinitesimal thickenings of a complete local base into a formal object of `Coh_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.approximationFunctor`: **the functor of Artin's
  Axioms, Equation 07X6, at `Coh_{X/Y}`** — the rule taking an object of `Coh_{X/Y}` over the
  spectrum of a Noetherian complete local ring with residue field of finite type over `S` to
  its compatible system of restrictions to the infinitesimal thickenings of that spectrum.
  This is the functor Stacks 08W9 asserts to be an equivalence.
* `AlgebraicGeometry.Space.CoherentSituation.formalObjectOfSystem`: a formal object of
  `Coh_{X/Y}` from a complete local base and a compatible system of objects of `Coh_{X/Y}` over
  its infinitesimal thickenings.
* `Deformation.Artin.FormalObject.isoOfLevels`: an isomorphism of formal objects of any
  category fibred in groupoids over the site, from a family of isomorphisms of the levels
  commuting with the transitions.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isApproximationFunctor_approximationFunctor`: the
  functor of Equation 07X6 at `Coh_{X/Y}` satisfies the equations characterizing restriction to
  all the infinitesimal thickenings.
* `AlgebraicGeometry.Space.CoherentSituation.formalObject_transition_base`: the transitions of
  a formal object of `Coh_{X/Y}` are morphisms of `Coh_{X/Y}` above the canonical closed
  immersions of the infinitesimal thickenings — the condition
  `AlgebraicGeometry.Space.CoherentSituation.formalObjectOfSystem` asks for, so that the two
  together say that a formal object of `Coh_{X/Y}` is exactly such a system.
* `AlgebraicGeometry.Space.CoherentSituation.isCompleteLocalObject_of_base_eq`: an object of
  `Coh_{X/Y}` over the spectrum of a Noetherian complete local ring with residue field of
  finite type over `S` is an object of the source of the functor of Equation 07X6.
* `AlgebraicGeometry.Space.CoherentSituation.isEffective_of_isoLevels`: a formal object of
  `Coh_{X/Y}` whose system is isomorphic to the restrictions of an object of `Coh_{X/Y}` over a
  complete local base is effective in the sense of [Stacks, Tag 07X7].  This is the shape in
  which Grothendieck's existence theorem is applied in the source's proof of Stacks 08W9.
* `CoherentSituation.isEquivalence_approximationFunctor_of_full_of_faithful_of_forall_isEffective`
  in `AlgebraicGeometry.Space`: the assertion of Stacks 08W9 split into the three obligations of
  `CategoryTheory.Functor.IsEquivalence`, essential surjectivity being effectivity of every
  formal object of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.isPredeformationCategory_predeformationCategory`:
  the predeformation category `F_{Coh_{X/Y}, k, x₀}` of a finite-type field point `x₀` of
  `Coh_{X/Y}` is a predeformation category.  Unconditional.
* `AlgebraicGeometry.Space.CoherentSituation.isDeformationCategory_predeformationCategory`: it
  is a deformation category as soon as `Coh_{X/Y}` satisfies the Rim–Schlessinger condition
  (RS) of Stacks 07WP.  This is the sentence the source's proof of Stacks 08W8 opens with, and
  the hypothesis is the one Stacks 08LQ supplies.

## Where Stacks 08W8 and Stacks 08W9 are proved

No declaration below carries `@[stacks 08W8]` or `@[stacks 08W9]`.

**Stacks 08W8** is proved in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackInfFinite.lean`
(`CoherentSituation.finiteDimensional_tangentSpace_and_infinitesimalAutomorphisms_cohDef` in
`AlgebraicGeometry.Space`).
The source opens with (RS) for `Coh_{X/B}`, which is Stacks 08LQ, so that `F_{Coh_{X/B}, k, x₀}`
is a deformation category by
`AlgebraicGeometry.Space.CoherentSituation.isDeformationCategory_predeformationCategory` below.
The tangent space is bounded through the map to the tangent space of `B` (Stacks 07X1), whose
kernel embeds into `Ext¹_{𝒪_{X₀}}(G₀, G₀ ⊗ ε)`
(`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackTangentFinite.lean`), and the infinitesimal
automorphisms embed into `Hom_{𝒪_{X₀}}(G₀, G₀ ⊗ ε)`; both are finite-dimensional by Stacks 0D0T
on the closed subspace of `X₀ = Spec k ×_B X` cut out by the square of the ideal of the support
of `G₀`.

**Stacks 08W9** is proved in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackApproximation.lean`
(`AlgebraicGeometry.Space.CoherentSituation.isEquivalence_approximationFunctor`), through the
three obligations of
`CoherentSituation.isEquivalence_approximationFunctor_of_full_of_faithful_of_forall_isEffective`
below.  The base change `X_A` of `f` to a complete local base `Spec A` and its restrictions
`X_n` to the thickenings `Spec(A/𝔪ⁿ⁺¹)` form an `AlgebraicGeometry.Space.SiteChangeTower`, on
which Stacks 08B9 and 08BE are available through the change of site of Stacks 04SG; full
faithfulness is 08B9 for the modules and Stacks 07X8 for the morphisms to `Y`
(`Deformation.Artin.HasUniqueExtensions`), essential surjectivity is 08BE with Stacks 08VP for
flatness.

## Implementation notes

The category structure on `AlgebraicGeometry.Space.CoherentObject` is a parameter throughout
the `Coh_{X/Y}` files, so every statement below installs
`AlgebraicGeometry.Space.CoherentSituation.categoryData`, the canonical one of Stacks 08KB, with
`letI`; this is the same convention as
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackCanonical.lean`.

`AlgebraicGeometry.Space.CoherentSituation.formalObjectOfSystem` takes the transition morphisms
as values of `AlgebraicGeometry.Space.CoherentHom` rather than as morphisms of the category,
because the hom-sets of the category structure are only *equal* to those and a binder whose type
needs the installed instance cannot be written before the instance is installed.  The
`CategoryTheory.Functor.IsHomLift` condition on a transition is then the condition on the
underlying morphism of test schemes alone, the structure functor of `Coh_{X/Y}` being the rule
which forgets both the module and the morphism to `Y`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08W9](https://stacks.math.columbia.edu/tag/08W9)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 07T5](https://stacks.math.columbia.edu/tag/07T5)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin.FormalObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- **An isomorphism of formal objects from a compatible family of isomorphisms of the
levels.**  Morphisms of formal objects are families of morphisms of the levels commuting with
the transitions, and the category structure is componentwise, so a family of isomorphisms of
the levels commuting with the transitions is an isomorphism. -/
def isoOfLevels {ξ η : FormalObject B S hS p}
    (e : ∀ n, ξ.level n ≅ η.level n)
    (he : ∀ n, ξ.transition n ≫ (e (n + 1)).hom = (e n).hom ≫ η.transition n) : ξ ≅ η where
  hom := { app := fun n => (e n).hom, naturality := he }
  inv :=
    { app := fun n => (e n).inv
      naturality := fun n => by
        apply (cancel_epi (e n).hom).1
        apply (cancel_mono (e (n + 1)).hom).1
        simpa [Category.assoc] using (he n).symm }
  hom_inv_id := by
    apply Hom.ext
    intro n
    change (e n).hom ≫ (e n).inv = 𝟙 _
    simp
  inv_hom_id := by
    apply Hom.ext
    intro n
    change (e n).inv ≫ (e n).hom = 𝟙 _
    simp

end Deformation.Artin.FormalObject

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-! ### The functor of Artin's Axioms, Equation 07X6 -/

/-- **The functor of Artin's Axioms, Equation 07X6, at `Coh_{X/Y}`.**  It takes an object
`(Spec A, g, ℱ)` of `Coh_{X/Y}` whose base is the spectrum of a Noetherian complete local ring
`A` with residue field of finite type over `S` to the compatible system of its restrictions to
the infinitesimal thickenings `Spec (A / 𝔪^{n+1})` of the closed point.

**Stacks 08W9** asserts that this functor is an equivalence. -/
def approximationFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.CompleteLocalObjects B S hS (coherentSiteProjection D.categoryData) ⥤
      Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData) :=
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  Deformation.Artin.approximationFunctor B S hS (coherentSiteProjection D.categoryData)
    D.isFiberedInGroupoids_siteProjection

/-- The functor of Equation 07X6 at `Coh_{X/Y}` satisfies the equations of
`Deformation.Artin.IsApproximationFunctor`: its levels carry cartesian maps to the original
object which commute with the transitions, naturally in the object, and which lie over the
canonical closed immersions of the infinitesimal thickenings into the complete local base. -/
theorem isApproximationFunctor_approximationFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.IsApproximationFunctor B S hS (coherentSiteProjection D.categoryData)
      D.approximationFunctor :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  (Deformation.Artin.approximationFunctorData B S hS (coherentSiteProjection D.categoryData)
    D.isFiberedInGroupoids_siteProjection).2

/-! ### Formal objects of `Coh_{X/Y}` -/

/-- **A compatible system of coherent sheaves with proper support over the infinitesimal
thickenings of a complete local base is a formal object of `Coh_{X/Y}`.**  The data is a
Noetherian complete local `S`-algebra `A` with residue field of finite type over `S`, membership
of each `Spec (A / 𝔪^{n+1})` in the site, an object of `Coh_{X/Y}` over each of them, and
morphisms of `Coh_{X/Y}` from each to the next whose underlying morphisms of test schemes are
the canonical closed immersions.

This is the shape in which Grothendieck's existence theorem is applied in the source's proof of
Stacks 08W9. -/
def formalObjectOfSystem
    (A : Deformation.Artin.FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (level : ℕ → CoherentObject D)
    (hlevel : ∀ n, (level n).T.left =
      Deformation.Artin.truncationOver B S hS A contains n)
    (transition : ∀ n, CoherentHom (level n) (level (n + 1)))
    (htransition : ∀ n, (transition n).base.left =
      eqToHom (hlevel n) ≫
        Deformation.Artin.truncationOverSucc B S hS A contains n ≫
          eqToHom (hlevel (n + 1)).symm) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData) :=
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  { base := A
    contains := contains
    level := level
    level_eq := hlevel
    transition := fun n => (Equiv.cast (D.categoryData.hom_type _ _)).symm (transition n)
    transition_lift := fun n =>
      IsHomLift.of_fac' (coherentSiteProjection D.categoryData)
        (Deformation.Artin.truncationOverSucc B S hS A contains n)
        ((Equiv.cast (D.categoryData.hom_type _ _)).symm (transition n))
        (hlevel n) (hlevel (n + 1)) (by
          change ((Equiv.cast (D.categoryData.hom_type _ _))
            ((Equiv.cast (D.categoryData.hom_type _ _)).symm (transition n))).base.left = _
          rw [Equiv.apply_symm_apply]
          exact htransition n) }

/-- The base of the formal object built from a system is the given complete local base. -/
@[simp]
theorem formalObjectOfSystem_base
    (A : Deformation.Artin.FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (level : ℕ → CoherentObject D)
    (hlevel : ∀ n, (level n).T.left =
      Deformation.Artin.truncationOver B S hS A contains n)
    (transition : ∀ n, CoherentHom (level n) (level (n + 1)))
    (htransition : ∀ n, (transition n).base.left =
      eqToHom (hlevel n) ≫
        Deformation.Artin.truncationOverSucc B S hS A contains n ≫
          eqToHom (hlevel (n + 1)).symm) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    (D.formalObjectOfSystem A contains level hlevel transition htransition).base = A :=
  rfl

/-- The levels of the formal object built from a system are the given objects of
`Coh_{X/Y}`. -/
@[simp]
theorem formalObjectOfSystem_level
    (A : Deformation.Artin.FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (level : ℕ → CoherentObject D)
    (hlevel : ∀ n, (level n).T.left =
      Deformation.Artin.truncationOver B S hS A contains n)
    (transition : ∀ n, CoherentHom (level n) (level (n + 1)))
    (htransition : ∀ n, (transition n).base.left =
      eqToHom (hlevel n) ≫
        Deformation.Artin.truncationOverSucc B S hS A contains n ≫
          eqToHom (hlevel (n + 1)).symm)
    (n : ℕ) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    (D.formalObjectOfSystem A contains level hlevel transition htransition).level n =
      level n :=
  rfl

/-- **The transitions of a formal object of `Coh_{X/Y}` are morphisms of `Coh_{X/Y}` over the
canonical closed immersions of the infinitesimal thickenings.**  This is the condition
`AlgebraicGeometry.Space.CoherentSituation.formalObjectOfSystem` asks for, read off a formal
object; the two together say that a formal object of `Coh_{X/Y}` is exactly a compatible system
of coherent sheaves with proper support over the infinitesimal thickenings of a complete local
base. -/
theorem formalObject_transition_base
    (ξ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData))
    (n : ℕ) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    (Equiv.cast (D.categoryData.hom_type (ξ.level n) (ξ.level (n + 1)))
        (ξ.transition n)).base.left =
      eqToHom (ξ.level_eq n) ≫
        Deformation.Artin.truncationOverSucc B S hS ξ.base ξ.contains n ≫
          eqToHom (ξ.level_eq (n + 1)).symm := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have := ξ.transition_lift n
  exact IsHomLift.fac' (coherentSiteProjection D.categoryData)
    (Deformation.Artin.truncationOverSucc B S hS ξ.base ξ.contains n) (ξ.transition n)

/-- **An object of `Coh_{X/Y}` over the spectrum of a Noetherian complete local ring with
residue field of finite type over `S` is a complete local object**, that is, an object of the
source of the functor of Equation 07X6. -/
theorem isCompleteLocalObject_of_base_eq
    (x : CoherentObject D) (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R)))
    (hx : x.T.left = Deformation.Artin.baseOver B S hS A hA) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.IsCompleteLocalObject B S hS (coherentSiteProjection D.categoryData) x :=
  ⟨A, hA, hx⟩

/-- **A formal object of `Coh_{X/Y}` whose system is algebraized is effective.**  If an object
`x` of `Coh_{X/Y}` over the spectrum of a Noetherian complete local ring has restrictions to the
infinitesimal thickenings isomorphic to the levels of a formal object `ξ`, compatibly with the
transitions, then `ξ` is in the essential image of the functor of Equation 07X6, that is,
effective in the sense of [Stacks, Tag 07X7].

This is the shape in which Grothendieck's existence theorem delivers essential surjectivity of
the functor of Equation 07X6 in the source's proof of Stacks 08W9. -/
theorem isEffective_of_isoLevels
    (ξ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData))
    (x : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.CompleteLocalObjects B S hS (coherentSiteProjection D.categoryData))
    (e : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ n, (D.approximationFunctor.obj x).level n ≅ ξ.level n)
    (he : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ n, (D.approximationFunctor.obj x).transition n ≫ (e (n + 1)).hom =
        (e n).hom ≫ ξ.transition n) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.FormalObject.IsEffective B S hS (coherentSiteProjection D.categoryData)
      D.isFiberedInGroupoids_siteProjection ξ :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  ⟨x, ⟨Deformation.Artin.FormalObject.isoOfLevels e he⟩⟩

/-- **The functor of Equation 07X6 at `Coh_{X/Y}` is an equivalence as soon as it is full and
faithful and every formal object of `Coh_{X/Y}` is effective.**  This is the decomposition of
the assertion of Stacks 08W9 into the three obligations of
`CategoryTheory.Functor.IsEquivalence`; essential surjectivity is effectivity of every formal
object. -/
theorem isEquivalence_approximationFunctor_of_full_of_faithful_of_forall_isEffective
    (hfull : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      D.approximationFunctor.Full)
    (hfaithful : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      D.approximationFunctor.Faithful)
    (heff : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ ξ : Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData),
        Deformation.Artin.FormalObject.IsEffective B S hS
          (coherentSiteProjection D.categoryData)
          D.isFiberedInGroupoids_siteProjection ξ) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    D.approximationFunctor.IsEquivalence :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  { faithful := hfaithful
    full := hfull
    essSurj := ⟨heff⟩ }

/-! ### Predeformation categories of `Coh_{X/Y}` -/

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)

/-- **The predeformation category of a finite-type field point of `Coh_{X/Y}` is a
predeformation category.**  For a point `x₀ = (Spec k, g₀, G₀)` of `Coh_{X/Y}` over a field `k`
factored through `Spec Λ`, the category `F_{Coh_{X/Y}, k, x₀}` of Stacks 07T4 is cofibered in
groupoids over the Artinian local `Λ`-algebras with residue field `k` and has a trivial fibre
over `k`.  Nothing beyond the standing data of Stacks 08KB is needed. -/
theorem isPredeformationCategory_predeformationCategory
    (x₀ : CoherentObject D)
    (hx₀ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    let C := Deformation.Artin.predeformationCategory iΛ
      (coherentSiteProjection D.categoryData ⋙ Over.post B.inclusion) x₀ hx₀
    letI : Category C.carrier := C.category
    Deformation.IsPredeformationCategory C.projection :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  Deformation.Artin.predeformationCategory_isPredeformationCategory B hS iΛ
    (coherentSiteProjection D.categoryData) x₀ hx₀ D.isFiberedInGroupoids_siteProjection

/-- **Granted the Rim–Schlessinger condition (RS) of Stacks 07WP for `Coh_{X/Y}`, the
predeformation category of a finite-type field point of `Coh_{X/Y}` is a deformation
category.**  This is the sentence the source's proof of Stacks 08W8 opens with, and the
hypothesis `hRS` is what Stacks 08LQ supplies. -/
theorem isDeformationCategory_predeformationCategory
    (hRS : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.SatisfiesRS B S hS (coherentSiteProjection D.categoryData)
        D.isFiberedInGroupoids_siteProjection)
    (x₀ : CoherentObject D)
    (hx₀ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    let C := Deformation.Artin.predeformationCategory iΛ
      (coherentSiteProjection D.categoryData ⋙ Over.post B.inclusion) x₀ hx₀
    letI : Category C.carrier := C.category
    Deformation.IsDeformationCategory C.projection :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  Deformation.Artin.isDeformationCategory_predeformationCategory B S hS
    (coherentSiteProjection D.categoryData) D.isFiberedInGroupoids_siteProjection hRS
    iΛ x₀ hx₀ hfinite hqc

end CoherentSituation

end AlgebraicGeometry.Space

end
