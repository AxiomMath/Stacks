module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The completed internal hom on an algebraic space

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale ringed site and let `M`, `N` be `𝒪_F`-modules.  Writing `𝓗 = 𝓗om_{𝒪_F}(M, N)`, the
inverse limit of the global sections of the ideal-power quotients of `𝓗` is the set of
morphisms of inverse systems from `(M / 𝓘 ^ n M)` to `(N / 𝓘 ^ n N)`:

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`.

The right-hand side is the set of morphisms of `Coh(F, 𝓘)`, that category being a full
subcategory of the inverse systems of `𝒪_F`-modules, whenever the two completions are objects of
it.  The identity is checked étale locally and the chartwise statement is the case of schemes;
what is proved here is the étale-descent globalisation, the chartwise input being carried as a
hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.idealPowerSubsheaf` — the subsheaf `𝓘 ^ n M`, at a module universe
  that may differ from the universe of the schemes, which is what the internal hom needs.
* `AlgebraicGeometry.Space.smallEtaleAdicQuotient`,
  `AlgebraicGeometry.Space.smallEtaleAdicQuotientTransition` and
  `AlgebraicGeometry.Space.smallEtaleAdicQuotientSystem` — the quotient `M / 𝓘 ^ n M`, the
  transition maps between the quotients, and the resulting inverse system.
* `AlgebraicGeometry.Space.adicSectionsAt` and `AlgebraicGeometry.Space.adicSections` — the
  inverse limit of the sections of an inverse system of `𝒪_F`-modules over one étale chart, and
  the inverse limit of its global sections.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` — the comparison
  `𝓗 / 𝓘 ^ n 𝓗 ⟶ 𝓗om(M, N / 𝓘 ^ n N)`.

## Main results

* `AlgebraicGeometry.Space.isPowAnnihilated_idealPowerQuotient` — `𝓘 ^ k` annihilates the
  sections of `M / 𝓘 ^ k M`.
* `AlgebraicGeometry.Space.smul_smallEtaleInternalHom_eq_zero` — a power of `𝓘` which
  annihilates `N` annihilates the internal hom into `N`.
* `AlgebraicGeometry.Space.bijective_adicSectionsMap_of_bijective_adicSectionsMapAt` — étale
  descent: a morphism of inverse systems which is bijective on the inverse limits of the
  sections over every chart is bijective on the inverse limits of the global sections.
* `AlgebraicGeometry.Space.smallEtaleInternalHomSectionsEquiv` — the global sections of the
  internal hom are the morphisms.
* `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomAdicSection` — morphisms of the
  inverse systems of ideal-power quotients are the compatible families of global sections of
  the internal homs.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` — **Stacks 08B6**, as a bijection.

## Implementation notes

The internal hom of two `𝒪_F`-modules with sections in the universe `u` of the schemes has its
own sections in `u + 1`, since a section over a chart `U` is a morphism of modules on the slice
of the small étale site at `U`, whose objects form a `Type (u + 1)`.  So
`AlgebraicGeometry.Space.idealPowerMultiple` and
`AlgebraicGeometry.Space.idealPowerQuotient`, which are pinned to the module universe `u`, do
not apply to `𝓗om(M, N)`; `AlgebraicGeometry.Space.idealPowerSubsheaf` and
`AlgebraicGeometry.Space.smallEtaleAdicQuotient` are the same constructions at a free module
universe, the latter under the hypothesis that cokernels exist there.  At the module universe
`u` the two agree by `rfl`, which is
`AlgebraicGeometry.Space.idealPowerSubsheaf_eq_idealPowerMultiple` and
`AlgebraicGeometry.Space.smallEtaleAdicQuotientSystem_obj_eq_idealPowerQuotient`.

The small étale site has no terminal object, so `H⁰(F, -)` is taken as
`CategoryTheory.SheafOfModules.sections`, a compatible family of sections over every chart.
That is exactly what makes the descent step cheap: a global section *is* a compatible family of
local ones, so the chartwise bijections glue once their inverses are seen to commute with
restriction, which they do because the comparison is a morphism of sheaves.

The inverse systems carrying the sections are presented as a sequence of modules together with
a sequence of transition maps rather than as functors out of `ℕᵒᵖ`.  Both are needed — the
morphisms of `Coh(F, 𝓘)` are natural transformations of functors — and
`AlgebraicGeometry.Space.systemHomEquiv` is the bridge; but every rewrite inside a term whose
type is `(Functor.ofOpSequence _).obj _` has to re-derive that object, and the two
presentations of the sheaf of rings of the small étale ringed site are definitionally but not
syntactically equal, so such rewrites build motives that are not type correct.  The sequence
presentation avoids this entirely.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 089N](https://stacks.math.columbia.edu/tag/089N)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PresheafOfModules.InternalHom

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### The subsheaf `𝓘 ^ n M` at an arbitrary module universe -/

/-- The subsheaf `𝓘 ^ n M` of an `𝒪_F`-module `M` whose sections may live in any universe:
the least sheaf submodule of `M` which over every étale chart `U` contains
`𝓘(U) ^ n • M(U)`. -/
def idealPowerSubsheaf (n : ℕ) (M : Modules.{u, m} B S hS F hF) : M.Submodule :=
  sInf { N | ∀ U : SmallEtale B S hS F,
    chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
      (M.val.obj (op U))) ≤ N.toSubmodule.obj (op U) }

/-- At the module universe of the schemes the subsheaf `𝓘 ^ n M` is
`AlgebraicGeometry.Space.idealPowerMultiple`, on the nose. -/
theorem idealPowerSubsheaf_eq_idealPowerMultiple (n : ℕ) (M : Modules.{u, u} B S hS F hF) :
    idealPowerSubsheaf B S hS F hF 𝓘 n M = idealPowerMultiple B S hS F hF 𝓘 n M := rfl

/-- The chartwise universal property of `𝓘 ^ n M`: it is contained in a sheaf submodule `N`
exactly when `N` contains `𝓘(U) ^ n • M(U)` over every étale chart. -/
theorem idealPowerSubsheaf_le_iff (n : ℕ) (M : Modules.{u, m} B S hS F hF) (N : M.Submodule) :
    idealPowerSubsheaf B S hS F hF 𝓘 n M ≤ N ↔
      ∀ U : SmallEtale B S hS F,
        chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
          (M.val.obj (op U))) ≤ N.toSubmodule.obj (op U) := by
  constructor
  · intro h U
    refine le_trans ?_ (h (op U))
    change _ ≤ (sInf ((fun P : M.Submodule => P.toSubmodule) ''
      { P : M.Submodule | ∀ V : SmallEtale B S hS F,
        chartIdeal B S hS ⟨F, hF⟩ 𝓘 V ^ n • (⊤ : Submodule (chartRing B S hS F hF V)
          (M.val.obj (op V))) ≤ P.toSubmodule.obj (op V) })).obj (op U)
    rw [PresheafOfModules.Submodule.sInf_obj]
    refine le_iInf₂ fun P hP => ?_
    obtain ⟨Q, hQ, rfl⟩ := hP
    exact hQ U
  · intro h
    exact sInf_le h

/-- Over every étale chart, the subsheaf `𝓘 ^ n M` contains `𝓘(U) ^ n • M(U)`. -/
theorem le_idealPowerSubsheaf_obj (n : ℕ) (M : Modules.{u, m} B S hS F hF)
    (U : SmallEtale B S hS F) :
    chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
      (M.val.obj (op U))) ≤ (idealPowerSubsheaf B S hS F hF 𝓘 n M).toSubmodule.obj (op U) :=
  (idealPowerSubsheaf_le_iff B S hS F hF 𝓘 n M _).1 le_rfl U

/-- The subsheaves `𝓘 ^ n M` decrease in `n`, which is what makes the quotients
`M / 𝓘 ^ n M` into an inverse system. -/
theorem idealPowerSubsheaf_succ_le (n : ℕ) (M : Modules.{u, m} B S hS F hF) :
    idealPowerSubsheaf B S hS F hF 𝓘 (n + 1) M ≤ idealPowerSubsheaf B S hS F hF 𝓘 n M := by
  rw [idealPowerSubsheaf_le_iff]
  refine fun U => le_trans (Submodule.smul_mono ?_ le_rfl)
    (le_idealPowerSubsheaf_obj B S hS F hF 𝓘 n M U)
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The inclusion of a sheaf submodule `P` of `M` is annihilated by `h : M ⟶ N` exactly when
`P` is contained in the kernel of `h`. -/
theorem submodule_ι_comp_zero_iff {M N : Modules.{u, m} B S hS F hF}
    (P : M.Submodule) (h : M ⟶ N) :
    P.ι ≫ h = 0 ↔ P ≤ SheafOfModules.Submodule.ker h := by
  constructor
  · intro hh X x hx
    exact congrArg (fun k : P.toSheafOfModules ⟶ N => k.val.app X ⟨x, hx⟩) hh
  · intro hh
    ext X x
    exact hh X x.property

/-- The inclusion of `𝓘 ^ k M` is annihilated by `h : M ⟶ N` exactly when `h` kills every
product of a section of `𝓘 ^ k` with a section of `M` over a common étale chart. -/
theorem idealPowerSubsheaf_ι_comp_zero_iff (k : ℕ) {M N : Modules.{u, m} B S hS F hF}
    (h : M ⟶ N) :
    (idealPowerSubsheaf B S hS F hF 𝓘 k M).ι ≫ h = 0 ↔
      ∀ (U : SmallEtale B S hS F) (r : chartRing B S hS F hF U),
        r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k →
        ∀ x : M.val.obj (op U), h.val.app (op U) (r • x) = 0 := by
  rw [submodule_ι_comp_zero_iff, idealPowerSubsheaf_le_iff]
  constructor
  · intro hh U r hr x
    exact (SheafOfModules.Submodule.mem_ker _ (op U) _).mp
      (hh U (Submodule.smul_mem_smul hr Submodule.mem_top))
  · intro hh U
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    exact (SheafOfModules.Submodule.mem_ker _ (op U) _).mpr (hh U r hr x)

/-! ### The inverse system `(M / 𝓘 ^ n M)` -/

section Quotient

variable [HasCokernels (Modules.{u, m} B S hS F hF)]

/-- The quotient `M / 𝓘 ^ n M` of an `𝒪_F`-module whose sections may live in any universe. -/
abbrev smallEtaleAdicQuotient (n : ℕ) (M : Modules.{u, m} B S hS F hF) :
    Modules.{u, m} B S hS F hF :=
  cokernel (idealPowerSubsheaf B S hS F hF 𝓘 n M).ι

/-- The projection `M ⟶ M / 𝓘 ^ n M`. -/
abbrev smallEtaleAdicQuotientProjection (n : ℕ) (M : Modules.{u, m} B S hS F hF) :
    M ⟶ smallEtaleAdicQuotient B S hS F hF 𝓘 n M :=
  cokernel.π (idealPowerSubsheaf B S hS F hF 𝓘 n M).ι

/-- The transition map `M / 𝓘 ^ (n + 1) M ⟶ M / 𝓘 ^ n M`, induced by the inclusion
`𝓘 ^ (n + 1) M ≤ 𝓘 ^ n M`. -/
def smallEtaleAdicQuotientTransition (n : ℕ) (M : Modules.{u, m} B S hS F hF) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M ⟶
      smallEtaleAdicQuotient B S hS F hF 𝓘 n M :=
  cokernel.desc _ (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n M)
    ((submodule_ι_comp_zero_iff B S hS F hF _ _).mpr
      (le_trans (idealPowerSubsheaf_succ_le B S hS F hF 𝓘 n M)
        ((submodule_ι_comp_zero_iff B S hS F hF _ _).mp (cokernel.condition _))))

/-- The transition map is compatible with the projections from `M`. -/
@[simp]
theorem smallEtaleAdicQuotientProjection_comp_transition (n : ℕ)
    (M : Modules.{u, m} B S hS F hF) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n M =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n M :=
  cokernel.π_desc _ _ _

/-- The inverse system `(M / 𝓘 ^ (n + 1) M)` of the ideal-power quotients of `M`, indexed so
that its term at `n` is the quotient by the `(n + 1)`-st power of `𝓘`. -/
def smallEtaleAdicQuotientSystem (M : Modules.{u, m} B S hS F hF) :
    ℕᵒᵖ ⥤ Modules.{u, m} B S hS F hF :=
  Functor.ofOpSequence (X := fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M)
    fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M

/-- The term of the inverse system of ideal-power quotients at `n`. -/
@[simp]
theorem smallEtaleAdicQuotientSystem_obj (M : Modules.{u, m} B S hS F hF) (n : ℕ) :
    (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M).obj (op n) =
      smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M := rfl

/-- The transition map of the inverse system of ideal-power quotients. -/
@[simp]
theorem smallEtaleAdicQuotientSystem_map_succ (M : Modules.{u, m} B S hS F hF) (n : ℕ)
    (h : n ≤ n + 1) :
    (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE h).op =
      smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Two maps out of `M / 𝓘 ^ (n + 1) M` agree after the transition map once they agree after the
projection. -/
private theorem transition_comp_eq_of_projection_comp (M : Modules.{u, m} B S hS F hF) (n : ℕ)
    {X Y : Modules.{u, m} B S hS F hF}
    (a : smallEtaleAdicQuotient B S hS F hF 𝓘 n M ⟶ X)
    (b : smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M ⟶ Y) (c : Y ⟶ X)
    (h : smallEtaleAdicQuotientProjection B S hS F hF 𝓘 n M ≫ a =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫ b ≫ c) :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n M ≫ a = b ≫ c := by
  rw [← cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M),
    ← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition, h]

end Quotient

/-! ### Annihilation of the ideal-power quotients and of the internal hom -/


/-- **A power of `𝓘` which annihilates `N` annihilates `𝓗om(M, N)`.**  A section of the
internal hom over a chart `U` is a morphism `M|_U ⟶ N|_U`, and multiplying it by a section of
`𝓘(U) ^ k` multiplies each of its components by a section of `𝓘 ^ k` over a smaller chart,
which kills the target. -/
theorem smul_smallEtaleInternalHom_eq_zero (k : ℕ) (M N : Modules.{u, u} B S hS F hF)
    (hN : IsPowAnnihilated B S hS F hF 𝓘 k N) (U : (smallEtaleRingedSite B S hS F hF).C)
    (r : chartRing B S hS F hF U) (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k)
    (α : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) : r • α = 0 := by
  change α ≫ multEndoHom (smallEtaleRingedSite B S hS F hF).O.obj N.val U r = 0
  refine PresheafOfModules.hom_ext fun V => ?_
  rw [PresheafOfModules.zero_app]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change fRestr (smallEtaleRingedSite B S hS F hF).O.obj U r V • (α.app V).hom x = 0
  exact hN V.unop.left (chartRestrict (hF := hF) V.unop.hom r)
    (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 V.unop.hom k hr) _

/-- A morphism of `𝒪_F`-modules into a module whose sections are annihilated by `𝓘 ^ k` kills
`𝓘 ^ k M`, and so factors through `M / 𝓘 ^ k M`. -/
theorem idealPowerSubsheaf_ι_comp_eq_zero (k : ℕ) (M N : Modules.{u, u} B S hS F hF)
    (hN : IsPowAnnihilated B S hS F hF 𝓘 k N) (g : M ⟶ N) :
    (idealPowerSubsheaf B S hS F hF 𝓘 k M).ι ≫ g = 0 :=
  (idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 k g).mpr fun U r hr x =>
    (map_smul (g.val.app (op U)).hom r x).trans (hN U r hr _)

/-! ### Compatible families of sections of an inverse system of modules -/

section Sections

variable (X Y : ℕ → Modules.{u, m} B S hS F hF) (trX : ∀ n, X (n + 1) ⟶ X n)
    (trY : ∀ n, Y (n + 1) ⟶ Y n)

/-- The inverse limit of the sections over one étale chart of an inverse system of
`𝒪_F`-modules. -/
def adicSectionsAt (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) : Type m :=
  { t : ∀ n : ℕ, (X n).val.obj U // ∀ n : ℕ, (trX n).val.app U (t (n + 1)) = t n }

/-- The inverse limit `lim_n H⁰(F, X_n)` of the global sections of an inverse system of
`𝒪_F`-modules. -/
def adicSections : Type (max (u + 1) m) :=
  { s : ∀ n : ℕ, (X n).sections //
      ∀ n : ℕ, SheafOfModules.sectionsMap (trX n) (s (n + 1)) = s n }

/-- The sections over a single chart of a compatible family of global sections. -/
def adicSectionsFibre (s : adicSections B S hS F hF X trX)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) : adicSectionsAt B S hS F hF X trX U :=
  ⟨fun n => (s.1 n).val U, fun n => congrArg (fun z : (X n).sections => z.val U) (s.2 n)⟩

/-- A compatible family of global sections is determined by its sections over the charts. -/
theorem adicSections_ext (s s' : adicSections B S hS F hF X trX)
    (h : ∀ U, adicSectionsFibre B S hS F hF X trX s U =
      adicSectionsFibre B S hS F hF X trX s' U) : s = s' := by
  refine Subtype.ext (funext fun n => ?_)
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  exact congrArg (fun z : adicSectionsAt B S hS F hF X trX U => z.1 n) (h U)

variable (β : ∀ n : ℕ, X n ⟶ Y n) (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)

/-- A morphism of inverse systems acts on the inverse limits of the sections over a chart. -/
def adicSectionsMapAt (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)
    (t : adicSectionsAt B S hS F hF X trX U) : adicSectionsAt B S hS F hF Y trY U :=
  ⟨fun n => (β n).val.app U (t.1 n), fun n => by
    have h := congrArg (fun k : X (n + 1) ⟶ Y n => k.val.app U (t.1 (n + 1))) (hβ n)
    exact h.symm.trans (congrArg ((β n).val.app U) (t.2 n))⟩

/-- A morphism of inverse systems acts on the inverse limits of the global sections. -/
def adicSectionsMap (s : adicSections B S hS F hF X trX) : adicSections B S hS F hF Y trY :=
  ⟨fun n => SheafOfModules.sectionsMap (β n) (s.1 n), fun n => by
    refine PresheafOfModules.sections_ext _ _ fun U => ?_
    exact (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U
      (adicSectionsFibre B S hS F hF X trX s U)).2 n⟩

/-- Taking sections over a chart commutes with the action of a morphism of inverse systems. -/
theorem adicSectionsFibre_adicSectionsMap (s : adicSections B S hS F hF X trX)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    adicSectionsFibre B S hS F hF Y trY (adicSectionsMap B S hS F hF X Y trX trY β hβ s) U =
      adicSectionsMapAt B S hS F hF X Y trX trY β hβ U
        (adicSectionsFibre B S hS F hF X trX s U) := rfl

/-- **Étale descent for the inverse limit of the global sections.**  A morphism of inverse
systems of `𝒪_F`-modules which is bijective on the inverse limits of the sections over every
étale chart is bijective on the inverse limits of the global sections: a global section is a
compatible family of sections over the charts, and the preimages over the charts are compatible
with restriction because the morphism is. -/
theorem bijective_adicSectionsMap_of_bijective_adicSectionsMapAt
    (h : ∀ U, Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U)) :
    Function.Bijective (adicSectionsMap B S hS F hF X Y trX trY β hβ) := by
  let e : ∀ U, adicSectionsAt B S hS F hF X trX U ≃ adicSectionsAt B S hS F hF Y trY U :=
    fun U => Equiv.ofBijective _ (h U)
  refine ⟨fun {s s'} hss => ?_, fun t' => ?_⟩
  · refine adicSections_ext B S hS F hF X trX s s' fun U => ?_
    refine (h U).1 ?_
    rw [← adicSectionsFibre_adicSectionsMap, ← adicSectionsFibre_adicSectionsMap, hss]
  · set t : ∀ U, adicSectionsAt B S hS F hF X trX U :=
      fun U => (e U).symm (adicSectionsFibre B S hS F hF Y trY t' U) with ht
    have hte : ∀ U, adicSectionsMapAt B S hS F hF X Y trX trY β hβ U (t U) =
        adicSectionsFibre B S hS F hF Y trY t' U := fun U => (e U).apply_symm_apply _
    have hres : ∀ (U V : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (g : U ⟶ V) (n : ℕ),
        (X n).val.map g ((t U).1 n) = (t V).1 n := by
      intro U V g
      have hw : ∀ n : ℕ, (trX n).val.app V ((X (n + 1)).val.map g ((t U).1 (n + 1))) =
          (X n).val.map g ((t U).1 n) := by
        intro n
        rw [PresheafOfModules.naturality_apply (trX n).val g, (t U).2 n]
      have hwmap : adicSectionsMapAt B S hS F hF X Y trX trY β hβ V
            ⟨fun n => (X n).val.map g ((t U).1 n), hw⟩ =
          adicSectionsFibre B S hS F hF Y trY t' V := by
        refine Subtype.ext (funext fun n => ?_)
        change (β n).val.app V ((X n).val.map g ((t U).1 n)) = _
        rw [PresheafOfModules.naturality_apply (β n).val g]
        change (Y n).val.map g
          ((adicSectionsMapAt B S hS F hF X Y trX trY β hβ U (t U)).1 n) = _
        rw [hte U]
        exact PresheafOfModules.sections_property (t'.1 n) g
      have heq := (h V).1 (hwmap.trans (hte V).symm)
      intro n
      exact congrArg (fun z : adicSectionsAt B S hS F hF X trX V => z.1 n) heq
    refine ⟨⟨fun n => PresheafOfModules.sectionsMk (fun U => (t U).1 n)
      (fun {U V} g => hres U V g n), fun n => ?_⟩, ?_⟩
    · refine PresheafOfModules.sections_ext _ _ fun U => ?_
      exact (t U).2 n
    · refine adicSections_ext B S hS F hF Y trY _ t' fun U => ?_
      exact hte U

/-- Morphisms of the inverse systems assembled from two sequences of transition maps are
exactly the compatible families of their components. -/
def systemHomEquiv :
    (Functor.ofOpSequence trX ⟶ Functor.ofOpSequence trY) ≃
      { γ : ∀ n : ℕ, X n ⟶ Y n // ∀ n : ℕ, trX n ≫ γ n = γ (n + 1) ≫ trY n } where
  toFun φ := ⟨fun n => φ.app (op n), fun n => by
    have h := φ.naturality (homOfLE (n.le_add_right 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h⟩
  invFun γ := NatTrans.ofOpSequence (fun n => γ.1 n) fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
    exact γ.2 n
  left_inv φ := by
    refine NatTrans.ext (funext fun Z => ?_)
    obtain ⟨n⟩ := Z
    rfl
  right_inv γ := rfl

end Sections

/-! ### The internal hom and its global sections -/

/-- Postcomposition with a morphism of `𝒪_F`-modules, as a morphism of internal homs. -/
def smallEtaleInternalHomMapRight (M : Modules.{u, m} B S hS F hF)
    {N N' : Modules.{u, m} B S hS F hF} (f : N ⟶ N') :
    smallEtaleInternalHom B S hS F hF M N ⟶ smallEtaleInternalHom B S hS F hF M N' :=
  ⟨internalHomMapRight (smallEtaleRingedSite B S hS F hF).O.obj M.val f.val⟩

/-- Postcomposition on the internal hom respects composition. -/
theorem smallEtaleInternalHomMapRight_comp (M : Modules.{u, m} B S hS F hF)
    {N N' N'' : Modules.{u, m} B S hS F hF} (f : N ⟶ N') (g : N' ⟶ N'') :
    smallEtaleInternalHomMapRight B S hS F hF M (f ≫ g) =
      smallEtaleInternalHomMapRight B S hS F hF M f ≫
        smallEtaleInternalHomMapRight B S hS F hF M g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun α =>
      (congrArg (fun k => α ≫ k)
          ((restrFun (smallEtaleRingedSite B S hS F hF).O.obj U.unop).map_comp
            f.val g.val)).trans
        (Category.assoc α _ _).symm))

/-- **The global sections of `𝓗om(M, N)` are the morphisms `M ⟶ N`.**  A global section of the
internal hom is a morphism `M|_U ⟶ N|_U` for every étale chart `U`, compatibly with
restriction, which is exactly a morphism `M ⟶ N`. -/
def smallEtaleInternalHomSectionsEquiv (M N : Modules.{u, m} B S hS F hF) :
    (smallEtaleInternalHom B S hS F hF M N).sections ≃ (M ⟶ N) :=
  (internalHomSectionsEquiv (smallEtaleRingedSite B S hS F hF).O.obj M.val N.val).trans
    (SheafOfModules.fullyFaithfulForget _).homEquiv.symm

/-- The identification of the global sections of the internal hom with the morphisms is natural
in the target. -/
theorem smallEtaleInternalHomSectionsEquiv_map (M : Modules.{u, m} B S hS F hF)
    {N N' : Modules.{u, m} B S hS F hF} (f : N ⟶ N')
    (s : (smallEtaleInternalHom B S hS F hF M N).sections) :
    smallEtaleInternalHomSectionsEquiv B S hS F hF M N'
        (SheafOfModules.sectionsMap (smallEtaleInternalHomMapRight B S hS F hF M f) s) =
      smallEtaleInternalHomSectionsEquiv B S hS F hF M N s ≫ f :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- At the module universe of the schemes, the term at `n` of the inverse system of ideal-power
quotients is the quotient `M / 𝓘 ^ (n + 1) M` of
`AlgebraicGeometry.Space.idealPowerQuotient`, on the nose. -/
theorem smallEtaleAdicQuotientSystem_obj_eq_idealPowerQuotient
    (M : Modules.{u, u} B S hS F hF) (n : ℕ) :
    (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M).obj (op n) =
      idealPowerQuotient B S hS F hF 𝓘 (n + 1) M := rfl

/-- `𝓘 ^ k` annihilates the sections of `M / 𝓘 ^ k M`. -/
theorem isPowAnnihilated_smallEtaleAdicQuotient (k : ℕ) (M : Modules.{u, u} B S hS F hF) :
    IsPowAnnihilated B S hS F hF 𝓘 k (smallEtaleAdicQuotient B S hS F hF 𝓘 k M) :=
  isPowAnnihilated_idealPowerQuotient B S hS F hF 𝓘 k M

/-! ### The comparison with the internal hom of the completion -/

section Comparison

variable (M N : Modules.{u, u} B S hS F hF)

/-- **The comparison at level `n`.**  A section of `𝓗om(M, N) / 𝓘 ^ n 𝓗om(M, N)` is a morphism
`M ⟶ N / 𝓘 ^ n N`: reducing the target modulo `𝓘 ^ n` kills `𝓘 ^ n 𝓗om(M, N)`, because `𝓘 ^ n`
annihilates `𝓗om(M, N / 𝓘 ^ n N)`. -/
def smallEtaleInternalHomAdicComparisonApp (n : ℕ) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS F hF M N) ⟶
      smallEtaleInternalHom B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) :=
  cokernel.desc _ (smallEtaleInternalHomMapRight B S hS F hF M
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N))
    ((idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 (n + 1) _).mpr fun U r hr α =>
      (map_smul ((smallEtaleInternalHomMapRight B S hS F hF M
            (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N)).val.app (op U)).hom
          r α).trans
        (smul_smallEtaleInternalHom_eq_zero B S hS F hF 𝓘 (n + 1) M _
          (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) U r hr _))

/-- The comparison at level `n` is compatible with the projection from the internal hom. -/
@[simp]
theorem smallEtaleAdicQuotientProjection_comp_comparisonApp (n : ℕ) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N) ≫
        smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N n =
      smallEtaleInternalHomMapRight B S hS F hF M
        (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N) :=
  cokernel.π_desc _ _ _

/-- **The comparison is a morphism of inverse systems**, from the completion of `𝓗om(M, N)` to
the internal homs out of `M` into the completion of `N`. -/
theorem smallEtaleInternalHomAdicComparison_compat (n : ℕ) :
    smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N) ≫
        smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N n =
      smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N (n + 1) ≫
        smallEtaleInternalHomMapRight B S hS F hF M
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N) := by
  refine transition_comp_eq_of_projection_comp B S hS F hF 𝓘 (smallEtaleInternalHom B S hS F hF M N)
    (n + 1) _ _ _ ?_
  simp [← Category.assoc, ← smallEtaleInternalHomMapRight_comp]

/-! ### Morphisms of the completions as compatible families of sections -/

/-- A morphism of the inverse systems of ideal-power quotients, read as a compatible family of
global sections of the internal homs: the component at `n` is the morphism
`M ⟶ N / 𝓘 ^ (n + 1) N` obtained from the projection of `M` onto `M / 𝓘 ^ (n + 1) M`. -/
def smallEtaleInternalHomAdicSection
    (γ : { γ : ∀ n : ℕ, smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) M ⟶
          smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N //
        ∀ n : ℕ, smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M ≫ γ n =
          γ (n + 1) ≫ smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N }) :
    adicSections B S hS F hF
      (fun n => smallEtaleInternalHom B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleInternalHomMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N)) :=
  ⟨fun n => (smallEtaleInternalHomSectionsEquiv B S hS F hF M
      (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).symm
        (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫ γ.1 n), by
    intro n
    have key : (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1 + 1) M ≫ γ.1 (n + 1)) ≫
          smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N =
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫ γ.1 n := by
      rw [Category.assoc, ← γ.2 n, ← Category.assoc,
        smallEtaleAdicQuotientProjection_comp_transition]
    refine (smallEtaleInternalHomSectionsEquiv B S hS F hF M
      (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).injective ?_
    rw [smallEtaleInternalHomSectionsEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact key⟩

/-- **Morphisms of the inverse systems of ideal-power quotients are exactly the compatible
families of global sections of the internal homs.**  Injectivity is surjectivity of the
projections; surjectivity is that a morphism `M ⟶ N / 𝓘 ^ n N` factors through
`M / 𝓘 ^ n M`, the factorisations being automatically compatible. -/
theorem bijective_smallEtaleInternalHomAdicSection :
    Function.Bijective (smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N) := by
  refine ⟨fun {γ γ'} hγ => ?_, fun s => ?_⟩
  · refine Subtype.ext (funext fun n => ?_)
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M)).mp ?_
    refine (smallEtaleInternalHomSectionsEquiv B S hS F hF M
      (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).symm.injective ?_
    exact congrArg (fun z => z.1 n) hγ
  · have hkill : ∀ n : ℕ, (idealPowerSubsheaf B S hS F hF 𝓘 (n + 1) M).ι ≫
        smallEtaleInternalHomSectionsEquiv B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n) = 0 :=
      fun n => idealPowerSubsheaf_ι_comp_eq_zero B S hS F hF 𝓘 (n + 1) M _
        (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) _
    have hπ : ∀ n : ℕ, smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫
          cokernel.desc _ (smallEtaleInternalHomSectionsEquiv B S hS F hF M
            (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n)) (hkill n) =
        smallEtaleInternalHomSectionsEquiv B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n) :=
      fun n => cokernel.π_desc _ _ _
    have hαtr : ∀ n : ℕ, smallEtaleInternalHomSectionsEquiv B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n) =
        smallEtaleInternalHomSectionsEquiv B S hS F hF M
            (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1 + 1) N) (s.1 (n + 1)) ≫
          smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N := by
      intro n
      have h2 := congrArg (smallEtaleInternalHomSectionsEquiv B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)) (s.2 n)
      rw [smallEtaleInternalHomSectionsEquiv_map] at h2
      exact h2.symm
    refine ⟨⟨fun n => cokernel.desc _ (smallEtaleInternalHomSectionsEquiv B S hS F hF M
      (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n)) (hkill n), fun n => ?_⟩, ?_⟩
    · refine transition_comp_eq_of_projection_comp B S hS F hF 𝓘 _ (n + 1) _ _ _ ?_
      simpa [hπ] using hαtr n
    · refine Subtype.ext (funext fun n => ?_)
      change (smallEtaleInternalHomSectionsEquiv B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).symm
          (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) M ≫
            cokernel.desc _ (smallEtaleInternalHomSectionsEquiv B S hS F hF M
              (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) (s.1 n)) (hkill n)) = s.1 n
      rw [hπ n]
      exact (smallEtaleInternalHomSectionsEquiv B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).symm_apply_apply (s.1 n)

/-- **Stacks 08B6.**  Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf
of ideals and let `M`, `N` be `𝒪_F`-modules.  Put `𝓗 = 𝓗om_{𝒪_F}(M, N)`.  Then

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`,

the inverse limit of the global sections of the ideal-power quotients of `𝓗` being the
morphisms of inverse systems of `𝒪_F`-modules from the completion of `M` to the completion of
`N`.  Since `Coh(F, 𝓘)` is a full subcategory of the inverse systems of `𝒪_F`-modules, the
right-hand side is `Mor_{Coh(F, 𝓘)}(M^∧, N^∧)` whenever the two completions are objects of
it.

The source argues that both sides are sheaves on `F_étale` and so the identity may be checked
étale locally, where it is the case of schemes.  That reduction is the hypothesis `h0882`: it
asks, for every étale chart `U`, that the comparison be bijective on the inverse limits of the
sections over `U`, which on a chart is Stacks 0882 for the scheme `U`.  What is proved here is
the globalisation, in three steps: the comparison is a morphism of inverse systems of sheaves
(`smallEtaleInternalHomAdicComparison_compat`), so a chartwise bijection is a bijection on
global sections (`bijective_adicSectionsMap_of_bijective_adicSectionsMapAt`); the global
sections of `𝓗om(M, N / 𝓘 ^ n N)` are the morphisms `M ⟶ N / 𝓘 ^ n N`
(`smallEtaleInternalHomSectionsEquiv`); and such a morphism is the same as a morphism
`M / 𝓘 ^ n M ⟶ N / 𝓘 ^ n N`, compatibly in `n`
(`bijective_smallEtaleInternalHomAdicSection`).

The Noetherian hypothesis on `F` and the coherence of `M` and `N` are not used: they enter only
through `h0882`, whose chartwise content is the Noetherian scheme case. -/
@[stacks 08B6 "granted Stacks 0882, the case of schemes, on each étale chart as the hypothesis
h0882; the étale-descent globalisation is proved"]
def smallEtaleInternalHomAdicEquiv
    (h0882 : ∀ U, Function.Bijective (adicSectionsMapAt B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS F hF M N))
      (fun n => smallEtaleInternalHom B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS F hF M N))
      (fun n => smallEtaleInternalHomMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
      (smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N)
      (smallEtaleInternalHomAdicComparison_compat B S hS F hF 𝓘 M N) U)) :
    adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) :=
  ((Equiv.ofBijective _ (bijective_adicSectionsMap_of_bijective_adicSectionsMapAt
        B S hS F hF _ _ _ _ _
        (smallEtaleInternalHomAdicComparison_compat B S hS F hF 𝓘 M N) h0882)).trans
      (Equiv.ofBijective _
        (bijective_smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N)).symm).trans
    (systemHomEquiv B S hS F hF _ _ _ _).symm

end Comparison

end AlgebraicGeometry.Space

end
