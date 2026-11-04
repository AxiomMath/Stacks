module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplexMain
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConnectedConstantModels

/-!
# One finite projective complex on an étale covering of a connected scheme

Let `X` be a connected scheme in a big étale site `B` and let `Λ` be a Noetherian coefficient
ring. A bounded object `K` of the derived category of sheaves of `Λ`-modules on the small étale
site of `X` whose cohomology sheaves are locally constant of finite type is, over the members of
a single étale covering of `X`, the constant complex attached to one finite complex of finite
projective `Λ`-modules.

This is the small étale instantiation of the site-theoretic trivialization
`Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_point'`: the realization of
the small étale site in the space of `X` is the open image of an object
(`AlgebraicGeometry.siteEtaleImageOpen`), a family of arrows to the final object is covering
exactly when those images cover (`AlgebraicGeometry.SmallEtale.ofArrows_mem_topology_final_iff`)
and two objects whose images meet carry lifts of one point of the site
(`AlgebraicGeometry.exists_sitePoint_fiber_nonempty`), so the three properties the site-theoretic
statement asks of a realization all hold here and connectedness of `X` is connectedness of the
realizing space.

## Main results

* `AlgebraicGeometry.additive_smallEtaleSheafFiberOver` and
  `AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafFiberOver`: the fibre functor at a
  localized point of the small étale site is additive and left exact on sheaves of `Λ`-modules,
  as instances at the single module universe `u + 1` the site forces.
* `AlgebraicGeometry.exists_etaleCover_constantFiniteProjectiveComplex`: **Tag 09BI with its
  finite-Tor-dimension input named at the points of the site.** One finite complex of finite
  projective `Λ`-modules whose constant complex represents `K` over every member of one étale
  covering of `X`.

## Implementation notes

The hypothesis `hflat` is the finite-Tor-dimension half of membership of `K` in
`D_{ctf}(X_{étale}, Λ)`, read where the trivialization consumes it: at a point `q` of the site
lifting to an object `V`, the derived fibre of the restriction of a representative `T` of `K` to
the slice over `V` is asked to have a bounded flat representative over `Λ`. Nothing about the
conclusion enters that hypothesis — it speaks only about `K` and the site — and it is turned into
the Tor-dimension input of the site-theoretic statement by
`Stacks.ConstantSheaf.hasFlatRepresentative_of_constantComplexModel_of_point'`, which identifies
the derived fibre of a complex carrying a constant model over `V` with the complex of
coefficients of that model. The constructible half of `D_{ctf}` is carried by `hK`, as local
constancy of finite type of the cohomology sheaves.

Deriving `hflat` from locally finite Tor dimension of the reading of `K` over the constant
coefficient ring sheaf of Stacks 03TR is the one step not taken here. Its ingredients are in the
tree — `AlgebraicGeometry.exists_hasTorAmplitude_derivedRestriction_of_point`, Stacks 08G1
(`Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude`), the
slice comparison `AlgebraicGeometry.moduleSheafOverConstantCoefficientsSheafFiberComplexIso`,
the exactness of slice restriction at the slice spelling of the sheaf of rings
(`Stacks.SheafOfModules.sliceRestrictionOfSize`) and the flatness of the stalk
`AlgebraicGeometry.flat_coefficientStalk` — but assembling them asks for the derived tensor
products of the slices of the constant coefficient ringed site, which this file does not build.

The universes collapse: the objects of the small étale site lie in `Type (u + 1)`, its morphisms
in `Type u` and the coefficients in `Type u`, so the module universe `max u v r` of the
site-theoretic statements is `u + 1`. The limits instance for `ModuleCat.{u + 1} Λ` is therefore
seated by hand from `AlgebraicGeometry.hasLimits_moduleCat` with its universes written out: the
library instance for modules is stated at `ModuleCat.{max v w}`, and a search at
`ModuleCat.{u + 1}` leaves the universe equation `max (u + 1) ? = u + 1`, which has no unique
solution. The colimits instance needs no such help: instance search finds Mathlib's
`ModuleCat.hasColimitsOfSize` at `ModuleCat.{u + 1}` directly. The exactness of the fibre functor
is re-seated by hand like the limits, from the universe-free
`AlgebraicGeometry.preservesFiniteLimits_sheafFiberOver`.

## References

* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type u) [CommRing Λ]
  [∀ U : SmallEtale B X.obj X.property,
    HasSheafify ((SmallEtale.topology B X.obj X.property).over U) (ModuleCat.{u + 1} Λ)]

/-! ### Exactness of the fibre functor at the module universe of the small étale site -/

/-- The fibre functor at the lift to the slice over `V` of a point of the small étale site is
additive on sheaves of `Λ`-modules. This is
`AlgebraicGeometry.additive_sheafFiberOver` with the three universes of the site instantiated. -/
instance additive_smallEtaleSheafFiberOver
    (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1})
    {V : SmallEtale B X.obj X.property} (z : q.fiber.obj V) :
    ((q.over z).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
  additive_sheafFiberOver.{u, u, u + 1} (SmallEtale.topology B X.obj X.property) Λ q z

/-- The fibre functor at the lift to the slice over `V` of a point of the small étale site is
left exact on sheaves of `Λ`-modules. This is
`AlgebraicGeometry.preservesFiniteLimits_sheafFiberOver` with the three universes of the site
instantiated. -/
instance preservesFiniteLimits_smallEtaleSheafFiberOver
    (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1})
    {V : SmallEtale B X.obj X.property} (z : q.fiber.obj V) :
    PreservesFiniteLimits ((q.over z).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  preservesFiniteLimits_sheafFiberOver.{u, u, u + 1}
    (SmallEtale.topology B X.obj X.property) Λ q z

/-- Modules over a ring in `Type u` have all limits at the carrier universe `u + 1`. -/
local instance hasLimitsOfSize_moduleCat_succ :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
  hasLimits_moduleCat.{u, u + 1} Λ

/-- Modules over a ring in `Type u` have all colimits at the carrier universe `u + 1`. -/
local instance hasColimitsOfSize_moduleCat_succ :
    HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
  inferInstance

/-! ### One finite projective complex on an étale covering -/

variable [IsNoetherianRing Λ] [ConnectedSpace X.obj]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)]

/-- **Tag 09BI, with its finite-Tor-dimension input named at the points of the site.**

Let `X` be a connected scheme in a big étale site and `Λ` a Noetherian ring. Let `K` be a bounded
object of the derived category of sheaves of `Λ`-modules on the small étale site of `X` whose
cohomology sheaves are locally constant of finite type, and suppose that at every point `q` of
the site lifting to an object `V` the derived fibre of the restriction to the slice over `V` of a
representative of `K` has a bounded flat representative over `Λ` — the finite-Tor-dimension half
of membership in `D_{ctf}(X_{étale}, Λ)`. Then there is a single finite complex `E` of finite
projective `Λ`-modules and an étale covering of `X` over every member of which `K` becomes the
constant complex attached to `E`. -/
@[stacks 09BI]
theorem exists_etaleCover_constantFiniteProjectiveComplex
    (K : DerivedCategory.Bounded
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)))
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u, u}
      (SmallEtale.topology B X.obj X.property) Λ
      ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) n).obj K.obj))
    (hflat : ∀ (T : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ)
      (V : SmallEtale B X.obj X.property)
      (q : (SmallEtale.topology B X.obj X.property).Point.{u + 1}) (z : q.fiber.obj V),
      (K.obj ≅ DerivedCategory.Q.obj T) →
      ∃ c d : ℤ, StacksDraft.Perfect.HasFlatRepresentative.{u, u + 1}
        (((q.over z).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj
            ((((SmallEtale.topology B X.obj X.property).overPullback
              (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj T))) c d) :
    ∃ (E : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ)
      (T : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Finite Λ (E.X n)) ∧ (∀ n : ℤ, Module.Projective Λ (E.X n)) ∧
      ∃ (I : Type (u + 1)) (U : I → SmallEtale B X.obj X.property)
        (f : ∀ i, U i ⟶ SmallEtale.final B X.obj X.property),
        Sieve.ofArrows U f ∈ SmallEtale.topology B X.obj X.property
          (SmallEtale.final B X.obj X.property) ∧
        ∀ i, Nonempty (DerivedCategory.Q.obj
            ((((SmallEtale.topology B X.obj X.property).overPullback
              (ModuleCat.{u + 1} Λ) (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf ((SmallEtale.topology B X.obj X.property).over (U i))
              (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
  Stacks.ConstantSheaf.exists_cover_constantFiniteProjectiveComplex_of_point'
    (SmallEtale.topology B X.obj X.property) Λ (SmallEtale.final B X.obj X.property)
    (fun U => (siteEtaleImageOpen B X.obj X.property U : Set X.obj))
    (fun U => (siteEtaleImageOpen B X.obj X.property U).2)
    (fun U g => SmallEtale.ofArrows_mem_topology_final_iff B X.obj X.property U g)
    (exists_sitePoint_fiber_nonempty.{u + 1, u} B X.obj X.property) K hK
    (fun T V P q z e emodel =>
      have ⟨c, d, h⟩ := hflat T V q z e
      ⟨c, d, Stacks.ConstantSheaf.hasFlatRepresentative_of_constantComplexModel_of_point'
        (SmallEtale.topology B X.obj X.property) Λ q z T P emodel c d h⟩)

end AlgebraicGeometry

end
