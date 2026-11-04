module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.InjectiveLevelAcyclicity
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLefflerDerivedVanishing

/-!
# The derived limits of the level sections compute the derived level-limit functor

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]), and fix a completed
thickening `B` together with a finite-level system `T` for it, so that `T` presents `B` as the
limit of its finite levels `B_e`.  The *level functor*

`L_B : 𝓖 ↦ (e ↦ 𝓖(B_e))`

from abelian sheaves on `𝒞 = (Cris(C/A))ᵒᵖ` to inverse systems of abelian groups is exact, and
`lim ∘ L_B` is the functor whose value at `𝓖` is `lim_e 𝓖(B_e)` — the sections over `B` of the
direct image `g_* 𝓖` of [Stacks, Tag 07JL], by the degree-zero half of that tag
(`Crystalline.abelianDirectImageIsoLevelLimitPresheaf`).

This file proves the derived statement of that tag for `lim ∘ L_B`:

`R ⁿ (lim ∘ L_B)(𝓖) ≅ R ⁿ lim (L_B 𝓖)`,

by the resolution-by-acyclics argument of the source.  The input is that `L_B` carries injective
abelian sheaves to `lim`-acyclic inverse systems, which is
`Crystalline.surjective_finiteLevelSections_transition_of_injective` followed by
`Rlim.acyclic_lim_of_isMittagLeffler`, and the engine is
`Stacks.RightDerivedComp.objIsoOfAcyclicImage`.  Together with the vanishing of the higher derived
limits of a Mittag-Leffler system it gives `R ⁿ (lim ∘ L_B)(𝓖) = 0` for `n ≥ 1` whenever the
level restriction maps of `𝓖` are surjective.

## Main definitions

* `Crystalline.finiteLevelSectionsFunctor` — the level functor on abelian *presheaves* on
  `Cris(C/A)`, `𝓕 ↦ (e ↦ 𝓕(B_e))`, as the precomposition functor along
  `Crystalline.FiniteLevelSystem.diagram`.  Its value is `Crystalline.finiteLevelSections` on the
  nose.
* `Crystalline.sheafFiniteLevelSectionsFunctor` — the level functor `L_B` on abelian *sheaves*
  on `𝒞`, obtained from the previous one through `Crystalline.abelianSheafEquivalence`.

## Main results

* `Crystalline.enoughInjectives_crystallinePresheaf` — **abelian presheaves on `Cris(C/A)` have
  enough injectives.**  It is a Grothendieck abelian category.
* `Crystalline.acyclic_lim_sheafFiniteLevelSections_of_injective` — **the level sections of an
  injective abelian sheaf are `lim`-acyclic** in the `ℕ`-indexed sense of
  `Stacks.RightDerivedComp.acyclic`, which is the hypothesis the collapse consumes.
* `Crystalline.rightDerivedLevelLimitIso` — **`R ⁿ (lim ∘ L_B)(𝓖) ≅ R ⁿ lim (L_B 𝓖)`.**
* `Crystalline.isZero_rightDerivedLevelLimit_of_surjective` — **`R ⁿ (lim ∘ L_B)(𝓖) = 0` for
  `n ≥ 1`** when the level restrictions of `𝓖` are surjective.

## Relation to the derived half of [Stacks, Tag 07JL]

The derived half `R ⁿ g_* ≅ R ⁿ lim_e` of [Stacks, Tag 07JL] also needs the identification
`ev_B ∘ g_* ≅ lim ∘ L_B` naturally in the coefficient sheaf, which is
`Crystalline.pushforwardCompSectionsIso`, and the collapse `R ⁿ (ev_B ∘ g_*) ≅ ev_B (R ⁿ g_*)` for
the exact functor `ev_B`, which is `CategoryTheory.Functor.rightDerivedCompIso`. Together with the
collapse proved here they give `Crystalline.rightDerivedPushforwardSectionsIsoRightDerivedLimit`.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Crystalline

universe u v w

variable {s : AffineCrystallineSituation.{u, v}}

/-! ### Enough injectives on the two abelian categories in play -/

/-- **Filtered colimits of abelian presheaves on `Cris(C/A)` are exact.**  Colimits in a functor
category are computed pointwise, so this reduces to the exactness of filtered colimits
of abelian groups. -/
instance ab5OfSize_crystallinePresheaf :
    AB5OfSize.{max u v (w + 1), max u v (w + 1)}
      (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) where
  ofShape _ _ _ := inferInstance

/-- **Abelian presheaves on `Cris(C/A)` have a separator.**  A presheaf category `Cᵒᵖ ⥤ Ab` has
one, built from the free presheaves on a separator of `Ab`, and `Cris(C/A)` is the opposite of
its own opposite. -/
instance hasSeparator_crystallinePresheaf :
    HasSeparator (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :=
  HasSeparator.of_equivalence
    (Equivalence.congrLeft (E := Ab.{max u v (w + 1)})
      (opOpEquivalence (CrystallineThickening.{u, v, w} s)))

/-- **Abelian presheaves on `Cris(C/A)` form a Grothendieck abelian category**
([Stacks, Tag 079B]). -/
instance isGrothendieckAbelian_crystallinePresheaf :
    IsGrothendieckAbelian.{max u v (w + 1)}
      (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) where

/-- **Abelian presheaves on `Cris(C/A)` have enough injectives**, by Grothendieck's theorem.
This is what makes the right derived functors of a functor out of that category defined, and in
particular what makes the resolution-by-acyclics argument below available. -/
instance enoughInjectives_crystallinePresheaf :
    EnoughInjectives (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :=
  IsGrothendieckAbelian.enoughInjectives.{max u v (w + 1)}

/-- **The identification of chaotic abelian sheaves on `𝒞` with abelian presheaves on
`Cris(C/A)` is additive**: it is an equivalence, hence preserves binary products. -/
instance abelianSheafEquivalence_functor_additive :
    ((abelianSheafEquivalence.{u, v, w} s).functor).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The level functor -/

variable {X : CompletedCrystallineThickening.{u, v, w} s}

/-- **The level functor on abelian presheaves**, `𝓕 ↦ (e ↦ 𝓕(B_e))`, for a finite-level system
of a completed thickening.  It is precomposition with the diagram of finite levels
`Crystalline.FiniteLevelSystem.diagram`, so it is exact, and its value at `𝓕` is
`Crystalline.finiteLevelSections` of `𝓕`. -/
abbrev finiteLevelSectionsFunctor (T : FiniteLevelSystem X) :
    (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) ⥤
      Rlim.InvSystemAb.{max u v (w + 1)} :=
  (Functor.whiskeringLeft ℕᵒᵖ (CrystallineThickening.{u, v, w} s)
    Ab.{max u v (w + 1)}).obj T.diagram

/-- **The level functor evaluates to the inverse system of level sections**, on the nose. -/
theorem finiteLevelSectionsFunctor_obj (T : FiniteLevelSystem X)
    (F : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    (finiteLevelSectionsFunctor T).obj F = finiteLevelSections T F :=
  rfl

/-- The level functor preserves finite limits: limits in a functor category are computed
pointwise, so precomposition preserves them. -/
instance preservesFiniteLimits_finiteLevelSectionsFunctor (T : FiniteLevelSystem X) :
    PreservesFiniteLimits (finiteLevelSectionsFunctor T) :=
  ⟨fun _ => inferInstance⟩

/-- The level functor preserves finite colimits, by the same pointwise computation. -/
instance preservesFiniteColimits_finiteLevelSectionsFunctor (T : FiniteLevelSystem X) :
    PreservesFiniteColimits (finiteLevelSectionsFunctor T) :=
  ⟨fun _ => inferInstance⟩

/-- **The level functor `L_B` on abelian sheaves on `𝒞 = (Cris(C/A))ᵒᵖ`**,
`𝓖 ↦ (e ↦ 𝓖(B_e))`: the identification of chaotic abelian sheaves with abelian presheaves on
`Cris(C/A)`, followed by `Crystalline.finiteLevelSectionsFunctor`.  It is additive and exact,
being a composite of an equivalence with a precomposition functor. -/
abbrev sheafFiniteLevelSectionsFunctor (T : FiniteLevelSystem X) :
    Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)} ⥤
      Rlim.InvSystemAb.{max u v (w + 1)} :=
  (abelianSheafEquivalence.{u, v, w} s).functor ⋙ finiteLevelSectionsFunctor T

/-! ### The collapse -/

/-- **The level sections of an injective abelian sheaf are `lim`-acyclic**, in the `ℕ`-indexed
sense of `Stacks.RightDerivedComp.acyclic`: `R ⁿ lim` of the inverse system `e ↦ I(B_e)` vanishes
for every `n > 0`.

The transitions of that system are surjective by
`Crystalline.surjective_finiteLevelSections_transition_of_injective`, so the system is
Mittag-Leffler, and a Mittag-Leffler system is `lim`-acyclic by
`Rlim.acyclic_lim_of_isMittagLeffler`.  This is the hypothesis that replaces the unknown
statement that `L_B` carries injectives to injectives. -/
theorem acyclic_lim_sheafFiniteLevelSections_of_injective (T : FiniteLevelSystem X)
    (I : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) [Injective I] :
    Stacks.RightDerivedComp.acyclic
      (lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)})
      ((sheafFiniteLevelSectionsFunctor T).obj I) :=
  Rlim.acyclic_lim_of_isMittagLeffler _
    (Rlim.isMittagLeffler_of_surjective_succ _
      (surjective_finiteLevelSections_transition_of_injective T I))

/-- **The derived level-limit functor is the derived limit of the level sections**:

`R ⁿ (lim ∘ L_B)(𝓖) ≅ R ⁿ lim (L_B 𝓖)`

for every abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ` and every `n`.  This is the derived statement
of [Stacks, Tag 07JL] for the functor `lim ∘ L_B`, whose degree-zero value is the sections of the
direct image `g_* 𝓖` over the completed thickening.

It is `Stacks.RightDerivedComp.objIsoOfAcyclicImage` at `G = L_B` and `T = lim`: the level functor
`L_B` is exact, so its own higher right derived functors vanish and the image under `L_B` of an
injective resolution of `𝓖` is again a resolution, and its terms are `lim`-acyclic by
`Crystalline.acyclic_lim_sheafFiniteLevelSections_of_injective`.  An acyclic resolution computes a
right derived functor just as well as an injective one, which is what lets the argument run
without knowing that `L_B` carries injectives to injectives. -/
def rightDerivedLevelLimitIso (T : FiniteLevelSystem X)
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) (n : ℕ) :
    ((sheafFiniteLevelSectionsFunctor T ⋙ lim).rightDerived n).obj 𝓖 ≅
      ((lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)}).rightDerived n).obj
        ((sheafFiniteLevelSectionsFunctor T).obj 𝓖) :=
  Stacks.RightDerivedComp.objIsoOfAcyclicImage (sheafFiniteLevelSectionsFunctor T) lim
    (fun m hm => Functor.isZero_rightDerived_of_exact _ _ m hm)
    (fun Z hZ => haveI := hZ; acyclic_lim_sheafFiniteLevelSections_of_injective T Z) n

/-- **The higher derived level limits of a sheaf with surjective level restrictions vanish**:
`R ⁿ (lim ∘ L_B)(𝓖) = 0` for every `n ≥ 1`, when the restriction maps of `𝓖` along the level
transitions `B_{e+1} ↠ B_e` are surjective.

Read through the degree-zero identification of `lim ∘ L_B` with the sections of the direct image
of [Stacks, Tag 07JL], this is the vanishing `R ⁿ g_* 𝓖 = 0` for `n ≥ 1` that the Leray
degeneration of [Stacks, Tag 07JN] needs.  The surjectivity hypothesis is hypothesis (2) of
[Stacks, Tag 07JN]. -/
theorem isZero_rightDerivedLevelLimit_of_surjective (T : FiniteLevelSystem X)
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (h𝓖 : ∀ e : ℕ, Function.Surjective (ConcreteCategory.hom
      (((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖).map
        (T.transition (Nat.le_succ e)))))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((sheafFiniteLevelSectionsFunctor T ⋙ lim).rightDerived n).obj 𝓖) :=
  (Rlim.isZero_rightDerived_lim_of_isMittagLeffler _
    (Rlim.isMittagLeffler_of_surjective_succ _ h𝓖) n hn).of_iso
      (rightDerivedLevelLimitIso T 𝓖 n)

end Crystalline

end
