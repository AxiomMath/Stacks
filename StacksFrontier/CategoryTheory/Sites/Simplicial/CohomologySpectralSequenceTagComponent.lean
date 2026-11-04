module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInjective
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of a component of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_n`. This file identifies the cohomology of the complex of sections

```
H^q(Γ(C_n, I^•_n))
```

of a bounded-below complex of injectives `I^•` representing an abelian sheaf on `C_total` with
the sheaf cohomology `H^q(C_n, F_n)` of the restriction to the component. This is the step the
proof of Stacks 09WJ takes when it says *"since restriction to `C_p` is exact the complex
`I_p^•` represents `K_p`"* and *"the sheaves `I^q_p` are injective abelian sheaves on `C_p`"*,
i.e. the step citing Stacks 09WG (7) and Stacks 09WH.

Formally the content is a comparison of right derived functors. `Γ(C_n, (-)_n)` is the composite
`restrictAb n ⋙ Γ(C_n, -)`; restriction is exact and preserves injectives, so every abelian
sheaf on the total site is acyclic for it, and `Stacks.RightDerivedComp.objIso` collapses

```
R^q (Γ(C_n, (-)_n)) ≅ R^q Γ(C_n, -) ∘ (-)_n,
```

the right-hand side being the sheaf cohomology of the restriction.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentCohomologyFunctor`: **`H^q(C_n, (-)_n)`**, the
  `q`-th right derived functor of global sections on the component site `C_n`, applied to the
  restriction of an abelian sheaf on the total site.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isZero_rightDerived_restrictAb`: every abelian sheaf on
  the total site is acyclic for the restriction to a component.
* `CategoryTheory.SimplicialSiteSituation.rightDerivedComponentSectionsNatIso`:
  **`R^q Γ(C_n, (-)_n) ≅ H^q(C_n, (-)_n)`**, naturally in the abelian sheaf. This is the first
  of the three identifications the proof of Stacks 09WJ needs, in the form in which
  `H^q(Γ(C_n, I^•_n))` -- the first page of the spectral sequence of
  `StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean` -- becomes the
  cohomology of a component.

## Implementation notes

The coefficients are the abelian groups of the site's own universe, where the exactness of
Stacks 09WG (7) and the injectivity statement of Stacks 09WH are the instances
`CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_componentRestrictionAb`,
`CategoryTheory.SimplicialSiteSituation.preservesFiniteColimits_componentRestrictionAb` and
`CategoryTheory.SimplicialSiteSituation.preservesInjectiveObjects_componentRestrictionAb`.

`EnoughInjectives` on sheaves of abelian groups over a component or the total site is not an
instance Mathlib finds unaided: it comes from the Grothendieck abelian structure, whose universe
parameter is not determined by the goal. Both are therefore supplied as instances below, through
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`, the component and total
categories being small.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### Enough injectives on the sites of a simplicial-site situation -/

/-- Abelian sheaves on the total site form a Grothendieck abelian category, the total category
being small. -/
instance isGrothendieckAbelian_sheaf_totalTopology :
    IsGrothendieckAbelian.{u} (Sheaf S.totalTopology Ab.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} S.totalTopology Ab.{u}

/-- Abelian sheaves on a component site form a Grothendieck abelian category, the component
category being small. -/
instance isGrothendieckAbelian_sheaf_componentTopology (n : SimplexCategory) :
    IsGrothendieckAbelian.{u} (Sheaf (S.componentTopology n) Ab.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} (S.componentTopology n) Ab.{u}

/-- Abelian sheaves on the total site have enough injectives, being a Grothendieck abelian
category (Stacks 079H). -/
@[sga "4 I 7.13" "special case",
  sga "4 V 0.1.1" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
instance enoughInjectives_sheaf_totalTopology :
    EnoughInjectives (Sheaf S.totalTopology Ab.{u}) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- Abelian sheaves on a component site have enough injectives, being a Grothendieck abelian
category (Stacks 079H). -/
@[sga "4 I 7.13" "special case",
  sga "4 V 0.1.1" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
instance enoughInjectives_sheaf_componentTopology (n : SimplexCategory) :
    EnoughInjectives (Sheaf (S.componentTopology n) Ab.{u}) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

variable (n : SimplexCategory)

/-! ### The cohomology of a component -/

/-- **`H^q(C_n, (-)_n)`**: the `q`-th right derived functor of the global sections on the
component site `C_n`, applied to the restriction of an abelian sheaf on the total site. This is
the first page that Stacks 09WJ asserts. -/
def componentCohomologyFunctor (q : ℕ) : Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u} :=
  S.restrictAb n ⋙ (Sheaf.Γ (S.componentTopology n) Ab.{u}).rightDerived q

/-- **Every abelian sheaf on the total site is acyclic for the restriction to a component**:
restriction is exact, so it carries a chosen injective resolution to a complex which is exact in
the positive degrees. -/
theorem isZero_rightDerived_restrictAb (F : Sheaf S.totalTopology Ab.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (((S.restrictAb n).rightDerived q).obj F) :=
  Functor.isZero_rightDerived_of_exact (S.restrictAb n) F q hq

/-- **Stacks 09WG (7) and Stacks 09WH, in the form the proof of Stacks 09WJ uses them.** The
`q`-th right derived functor of `Γ(C_n, (-)_n)` at an abelian sheaf `F` on the total site is the
sheaf cohomology `H^q(C_n, F_n)` of its restriction: restriction to the component is exact and
preserves injective abelian sheaves, so applying it to an injective resolution of `F` gives an
injective resolution of `F_n`. -/
@[sga "4 VI 7.4.15" "(F)"]
def rightDerivedComponentSectionsIso (q : ℕ) (F : Sheaf S.totalTopology Ab.{u}) :
    ((S.componentSectionsFunctor n).rightDerived q).obj F ≅
      (S.componentCohomologyFunctor n q).obj F :=
  Stacks.RightDerivedComp.objIso (S.restrictAb n) (injectiveResolution F)
    (S.isZero_rightDerived_restrictAb n F) (Sheaf.Γ (S.componentTopology n) Ab.{u}) q

/-- `rightDerivedComponentSectionsIso` is natural in the abelian sheaf. -/
theorem rightDerivedComponentSectionsIso_hom_naturality (q : ℕ)
    {F F' : Sheaf S.totalTopology Ab.{u}} (f : F ⟶ F') :
    ((S.componentSectionsFunctor n).rightDerived q).map f ≫
        (S.rightDerivedComponentSectionsIso n q F').hom =
      (S.rightDerivedComponentSectionsIso n q F).hom ≫
        (S.componentCohomologyFunctor n q).map f :=
  Stacks.RightDerivedComp.objIso_hom_naturality (S.restrictAb n)
    (Sheaf.Γ (S.componentTopology n) Ab.{u}) q
    (S.isZero_rightDerived_restrictAb n F) (S.isZero_rightDerived_restrictAb n F') f

/-- **The first identification of Stacks 09WJ**: `R^q Γ(C_n, (-)_n) ≅ H^q(C_n, (-)_n)`,
naturally in the abelian sheaf on the total site.

The left-hand side is what the first page of the spectral sequence of
`CategoryTheory.SimplicialSiteSituation.sectionsSpectralSequence` computes, by
`CategoryTheory.SimplicialSiteSituation.pageOneIsoComponentSections` together with
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`; the right-hand side is the first page
that Stacks 09WJ asserts. -/
def rightDerivedComponentSectionsNatIso (q : ℕ) :
    (S.componentSectionsFunctor n).rightDerived q ≅ S.componentCohomologyFunctor n q :=
  NatIso.ofComponents (S.rightDerivedComponentSectionsIso n q)
    fun f => S.rightDerivedComponentSectionsIso_hom_naturality n q f

end CategoryTheory.SimplicialSiteSituation

end
