module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteNotExact
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf Hom does not commute with `𝓕 ↦ 𝓕^a` on a big site

Descent, Lemma 06VE (9) says that for quasi-coherent `𝒪_S`-modules `𝓕`, `𝓖` one does **not**
have `(SheafHom_{𝒪_S}(𝓕, 𝓖))^a = SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod((Sch/S)_τ, 𝒪)` in general, even
if `𝓕` is of finite presentation.  Clause (8) says the corresponding statement *is* true on the
small Zariski and small étale sites, so clause (9) is the assertion that passing to a big site
destroys it, and a faithful formalization has to exhibit the failure.

This file does what the source's proof does, at the witness already in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BigSiteNotExact.lean`.  Take
`S = Spec(ℤ)`, `𝓕 = Coker(2 : 𝒪_S → 𝒪_S)` and `𝓖 = 𝒪_S`.

* `SheafHom_{𝒪_S}(𝓕, 𝓖) = 0`: the sections of `𝓕` are killed by `2`, so a morphism
  `𝓕|_U ⟶ 𝒪_S|_U` lands in the `2`-torsion of the sections of `𝒪_{Spec(ℤ)}`, and those sections
  have none — which is `AlgebraicGeometry.AssociatedModuleNotExact.injective_two_sections`, the
  computation clause (6) is built on, read in the opposite direction.  Hence the left-hand side
  is `0^a = 0`.
* `SheafHom_𝒪(𝓕^a, 𝓖^a) ≠ 0`: it is the `2`-torsion `𝒪[2]` of the source's proof, and it is
  nonzero for the very reason clause (6) fails — `Spec(𝔽₂)` is an object of `(Sch/S)_τ` and
  `2 = 0` in `𝔽₂`.  Over that object the restriction of `𝓕^a` is the cokernel of
  `2 • 𝟙 : 𝒪|_{Spec(𝔽₂)} → 𝒪|_{Spec(𝔽₂)}`, which is the cokernel of the **zero** map because
  every ring of sections of `𝒪` over a scheme over `Spec(𝔽₂)` has characteristic `2`; so that
  restriction is `𝒪|_{Spec(𝔽₂)}` itself, and the resulting isomorphism is a nonzero section of
  the sheaf Hom.

Nothing is assumed about the big site beyond its existence: the statements below hold for
**every** `B : AlgebraicGeometry.BigFppfSite` and **every** `τ : AlgebraicGeometry.SiteKind`,
exactly as in `BigSiteNotExact.lean`, from which `Spec(ℤ)`, `Spec(𝔽₂)`, the object
`Spec(𝔽₂) → Spec(ℤ)` of the big site, `𝒪_S^a = 𝒪`, the additivity of `𝓕 ↦ 𝓕^a` and the two
torsion computations are all taken unchanged.

## Main definitions

* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.cokerTwo`:
  `𝓕 = Coker(2 : 𝒪_S → 𝒪_S)` for `S = Spec(ℤ)`, the first argument of the sheaf Hom.
* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.restrictFtwo`: restriction of
  `𝒪`-modules on `(Sch/S)_τ` to the slice site at `Spec(𝔽₂) → Spec(ℤ)`.
* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.associatedCokerTwoRestrictIso`:
  `𝓕^a|_{Spec(𝔽₂)} ≅ 𝓖^a|_{Spec(𝔽₂)}`, the nonzero section of the right-hand side.

## Main results

* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.isZero_sheafHomModules`:
  `SheafHom_{𝒪_S}(𝓕, 𝒪_S) = 0`, and
  `…isZero_associatedModule_sheafHomModules`: hence so is `(SheafHom_{𝒪_S}(𝓕, 𝒪_S))^a`.
* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.not_isZero_internalHomSheaf`:
  `SheafHom_𝒪(𝓕^a, 𝒪^a) ≠ 0`, on every big site and at every `τ`.
* `AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.exists_isQuasicoherent_not_iso_sheafHom`:
  **Stacks 06VE (9)** — the refutation.

## Implementation notes

**Which internal Hom, and in which universe.**  The internal Hom of Stacks 03EM on the big
`τ`-site of `S` is `AlgebraicGeometry.RingedSite.internalHomSheaf` at
`AlgebraicGeometry.BigFppfOver.baseRingedSite`, the spelling at which Stacks 0GNC (6) is proved
in `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteProperties.lean`.
That site is a `AlgebraicGeometry.RingedSite.{u + 1, u, u}` — the objects of the big category of
schemes over `S` lie in `Type (u + 1)` while its morphisms and structure rings lie in `Type u` —
and the sections of the internal Hom over an object are morphisms of modules on a slice, which
live in the universe of the objects.  So the internal Hom of two `SheafOfModules.{u}` on the big
site is a `SheafOfModules.{u + 1}`, while `(SheafHom_{𝒪_S}(𝓕, 𝓖))^a` is a `SheafOfModules.{u}`:
the small Zariski site of `S` has its objects in `Type u`, so the sheaf Hom downstairs does not
leave the module universe, and neither does `𝓕 ↦ 𝓕^a`.

The two sides of clause (9) are therefore not objects of one category and literal equality
between them is not even typeable.  The statement proved is that they are not isomorphic after
the canonical sectionwise universe lift `Stacks.SheafOfModules.moduleULift`, which is fully
faithful and additive (`Stacks.SheafOfModules.moduleULiftFullyFaithful`) and so loses nothing.
Nothing is weakened by this: what is proved is that the left-hand side is a **zero** object
while the right-hand side is **not**, and that dichotomy is universe-free — it is recorded
separately as `isZero_associatedModule_sheafHomModules` and `not_isZero_internalHomSheaf`, and
it rules out either spelling of the right-hand side, this one or the shrunken model
`AlgebraicGeometry.RingedSite.internalHomSheafSmall` of an essentially small site.

**Finite presentation, and why the refutation asserts it.**  The claim clause (9) denies is
*weaker* the more it assumes of `𝓕`, so a refutation is only a refutation of the clause if its
witness carries the clause's own rider "even if `𝓕` is of finite presentation": an `𝓕` that is
merely quasi-coherent refutes the statement without the rider and leaves the statement with it
untouched.  So `SheafOfModules.IsFinitePresentation 𝓕` is a conjunct of the existential below.
It costs nothing, `𝓕` being *defined* as the cokernel of `2 • 𝟙 : 𝒪_S → 𝒪_S`: the structure
sheaf is of finite presentation over itself
(`Stacks.SheafOfModules.Site.unit_isFinitePresentation`) and hence of finite type, so the cokernel
is of finite presentation by Stacks 0H96,
`Stacks.SheafOfModules.isFinitePresentation_cokernel`.

The notion is the one of Modules, Definition 01BZ for an `𝒪_S`-module, which is what the
source's rider is about.  Clause (8) — the positive statement on the small sites that clause (9)
denies on a big one — is stated in this library with the site spelling of the same notion,
`SheafOfModules.IsFinitePresentationOnSite` (Stacks 03DL (7)), on
`AlgebraicGeometry.SmallEtale.associatedModuleInternalHomSheafIso`; no lemma identifying the two
spellings is in the library, so the two clauses are stated at two spellings of "of finite
presentation" and the reader has to supply the identification.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe t w v₁ u₁ u

namespace AlgebraicGeometry.AssociatedModuleSheafHomNotCommute

open AssociatedModuleNotExact
open Stacks.AlgebraicGeometry.InternalHomModules (sheafHomModules)

/-! ### Reading `IsZero` and `2 • 𝟙 = 0` on sections

Three elementary transfers between a statement about a sheaf of modules and the corresponding
statement about each of its modules of sections, all via `CategoryTheory.SheafOfModules.evaluation`
and its additivity. -/

private theorem isZero_of_sections {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (h : ∀ (W : Cᵒᵖ) (s : M.val.obj W), s = 0) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rw [h W s]
  simp

private theorem eq_zero_of_isZero {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{t} R} (h : IsZero M) (W : Cᵒᵖ)
    (s : M.val.obj W) : s = 0 := by
  have : (SheafOfModules.evaluation R W).Additive := ⟨rfl⟩
  have h2 := congrArg (SheafOfModules.evaluation R W).map ((IsZero.iff_id_eq_zero M).1 h)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h2
  have h3 := congrArg
    (fun g : (SheafOfModules.evaluation R W).obj M ⟶ (SheafOfModules.evaluation R W).obj M =>
      ModuleCat.Hom.hom g s) h2
  simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_coe] at h3
  exact h3

private theorem two_nsmul_id_eq_zero_iff {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R) :
    (2 : ℕ) • 𝟙 M = 0 ↔ ∀ (W : Cᵒᵖ) (x : M.val.obj W), x + x = 0 := by
  have key (W : Cᵒᵖ) (x : M.val.obj W) : ((2 : ℕ) • 𝟙 M).val.app W x = x + x := by
    simp [two_nsmul]
  refine ⟨fun h W x => ?_, fun h => ?_⟩
  · rw [← key, h]
    rfl
  · refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
      (LinearMap.ext fun x => ?_))
    exact (key W x).trans (h W x)

/-! ### `𝓕 = Coker(2 : 𝒪_S → 𝒪_S)` and its `2`-torsion -/

/-- `𝓕 = Coker(2 : 𝒪_S → 𝒪_S)` for `S = Spec(ℤ)`: the first argument of the sheaf Hom in the
source's counterexample.  Being the cokernel of a map `𝒪_S → 𝒪_S`, it comes with the global
finite presentation `𝒪_S → 𝒪_S → 𝓕 → 0`. -/
public abbrev cokerTwo : specInt.{u}.Modules := cokernel (2 • 𝟙 unitModule.{u})

/-- **`2 • 𝟙 = 0` on `𝓕`.**  The cokernel projection is epi and kills `2 • 𝟙`. -/
public theorem two_nsmul_id_cokerTwo : (2 : ℕ) • 𝟙 cokerTwo.{u} = 0 := by
  have h : (2 • 𝟙 unitModule.{u}) ≫ cokernel.π (2 • 𝟙 unitModule.{u}) = 0 :=
    cokernel.condition _
  rw [Preadditive.nsmul_comp, Category.id_comp] at h
  refine zero_of_epi_comp (cokernel.π (2 • 𝟙 unitModule.{u})) ?_
  rw [Preadditive.comp_nsmul, Category.comp_id]
  exact h

/-- **Every section of `𝓕` is killed by `2`.** -/
public theorem add_self_sections_cokerTwo (W : (specInt.{u}.Opens)ᵒᵖ)
    (y : cokerTwo.{u}.val.obj W) : y + y = 0 :=
  (two_nsmul_id_eq_zero_iff _).1 two_nsmul_id_cokerTwo.{u} W y

/-! ### The left-hand side is zero -/

/-- **`SheafHom_{𝒪_S}(𝓕, 𝒪_S) = 0` for `S = Spec(ℤ)`.**  A morphism `𝓕|_U ⟶ 𝒪_S|_U` sends a
section `x` to a section killed by `2`, because `x + x = 0`; and multiplication by `2` is
injective on every ring of sections of `𝒪_{Spec(ℤ)}`
(`AlgebraicGeometry.AssociatedModuleNotExact.injective_two_sections`). -/
public theorem isZero_sheafHomModules :
    IsZero (sheafHomModules cokerTwo.{u} unitModule.{u}) := by
  refine isZero_of_sections _ ?_
  intro U s
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x + x = 0 := add_self_sections_cokerTwo.{u} (op W.unop.left) x
  refine injective_two_sections.{u} W.unop.left ?_
  change (s.app W).hom x + (s.app W).hom x = 0 + 0
  rw [add_zero, ← map_add, hx, map_zero]

/-- **`SheafHom_{𝒪_S}(𝓕, 𝒪_S)` is quasi-coherent**, being a zero object: it is isomorphic to
the cokernel of `𝟙 : 𝒪_S → 𝒪_S`, and a cokernel of quasi-coherent modules is quasi-coherent
(Tag 01LB).  So the left-hand side of clause (9) lies in the domain `QCoh(𝒪_S)` of the functor
the clause is about, and not merely in `Mod(𝒪_S)`. -/
public instance isQuasicoherent_sheafHomModules :
    (sheafHomModules cokerTwo.{u} unitModule.{u}).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent specInt.{u}.ringCatSheaf).prop_of_iso
    (IsZero.iso (isZero_cokernel_of_epi (𝟙 unitModule.{u})) isZero_sheafHomModules.{u})
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (𝟙 unitModule.{u}))

section

variable (B : BigFppfSite.{u}) (τ : SiteKind)

/-- **On a quasi-coherent module, `AlgebraicGeometry.AssociatedModuleNotExact.associatedModule`
is the functor `QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪)` of Stacks 06VE**, on the nose: the latter is the
former precomposed with the inclusion of the quasi-coherent modules.  This is what makes the
statements of this file, which are written with `associatedModule`, statements about the functor
clause (9) is about. -/
public theorem associatedModuleQcoh_obj (M : specInt.{u}.Modules) (hM : M.IsQuasicoherent) :
    (associatedModuleQcoh B τ).obj ⟨M, hM⟩ = (associatedModule B τ).obj M := rfl

variable (B : BigFppfSite.{u}) (τ : SiteKind)

/-- **`(SheafHom_{𝒪_S}(𝓕, 𝒪_S))^a = 0`.**  The functor `𝓕 ↦ 𝓕^a` is additive, so it carries the
zero object to a zero object. -/
public theorem isZero_associatedModule_sheafHomModules :
    IsZero ((associatedModule B τ).obj (sheafHomModules cokerTwo.{u} unitModule.{u})) := by
  have := additive_associatedModule B τ
  exact (associatedModule B τ).map_isZero isZero_sheafHomModules.{u}

/-! ### The right-hand side is not zero -/

/-- `2 = 0` in `Γ(Spec(𝔽₂), 𝒪)`, the sections of `𝒪` over the object `Spec(𝔽₂) → Spec(ℤ)`. -/
public theorem two_eq_zero_sections_ftwoObject :
    (2 : ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u)) = 0 := by
  apply (sectionsRingEquiv B τ).injective
  rw [map_ofNat, map_zero]
  decide

/-- **`2 = 0` in the sections of `𝒪` over every object of the big site lying over `Spec(𝔽₂)`.**
The restriction map is a ring homomorphism, so it carries `2` to `2` and `0` to `0`. -/
public theorem two_eq_zero_sections_over
    (W : BigFppfOver B specInt.{u} (contains_specInt B)) (g : W ⟶ ftwoObject B) :
    (2 : ((bigStructureSheaf B τ).obj.obj (op W) : Type u)) = 0 := by
  have h := congrArg ((bigStructureSheaf B τ).obj.map g.op).hom
    (two_eq_zero_sections_ftwoObject.{u} B τ)
  rw [map_ofNat, map_zero] at h
  exact h

/-- Restriction of `𝒪`-modules on `(Sch/Spec(ℤ))_τ` to the slice site at the object
`Spec(𝔽₂) → Spec(ℤ)`. -/
public abbrev restrictFtwo :
    SheafOfModules.{u} (bigStructureSheaf B τ) ⥤
      SheafOfModules.{u} ((bigStructureSheaf B τ).over (ftwoObject B)) :=
  SheafOfModules.overFunctor (bigStructureSheaf B τ) (ftwoObject B)

/-- Restriction to the slice at `Spec(𝔽₂) → Spec(ℤ)` is additive. -/
public instance additive_restrictFtwo : (restrictFtwo B τ).Additive :=
  ⟨by intros; ext W; rfl⟩

/-- Restriction to the slice at `Spec(𝔽₂) → Spec(ℤ)` preserves finite colimits. -/
public instance preservesFiniteColimits_restrictFtwo :
    PreservesFiniteColimits (restrictFtwo B τ) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (ftwoObject B)

/-- **`2 • 𝟙 = 0` on `𝒪|_{Spec(𝔽₂)}`.**  Every object of the slice site lies over `Spec(𝔽₂)`, so
its ring of sections has characteristic `2`. -/
public theorem two_nsmul_id_restrictFtwo_unit :
    (2 : ℕ) • 𝟙 ((restrictFtwo B τ).obj (SheafOfModules.unit (bigStructureSheaf B τ))) = 0 := by
  refine (two_nsmul_id_eq_zero_iff _).2 ?_
  intro W x
  have h : ∀ z : ((bigStructureSheaf B τ).obj.obj (op W.unop.left) : Type u), z + z = 0 := by
    intro z
    rw [← two_mul, two_eq_zero_sections_over.{u} B τ W.unop.left W.unop.hom, zero_mul]
  exact h x

/-- **`2 • 𝟙 = 0` on `𝒪_S^a|_{Spec(𝔽₂)}`**, transported from `𝒪|_{Spec(𝔽₂)}` along
`AlgebraicGeometry.AssociatedModuleNotExact.associatedModuleUnitIso`, which says `𝒪_S^a = 𝒪`. -/
public theorem two_nsmul_id_restrictFtwo_associated :
    (2 : ℕ) • 𝟙 ((restrictFtwo B τ).obj ((associatedModule B τ).obj unitModule.{u})) = 0 := by
  have e := (restrictFtwo B τ).mapIso (associatedModuleUnitIso B τ)
  have hconj : (2 : ℕ) • 𝟙 ((restrictFtwo B τ).obj ((associatedModule B τ).obj unitModule.{u}))
      = e.hom ≫ ((2 : ℕ) • 𝟙 ((restrictFtwo B τ).obj
        (SheafOfModules.unit (bigStructureSheaf B τ)))) ≫ e.inv := by
    simp
  rw [hconj, two_nsmul_id_restrictFtwo_unit, zero_comp, comp_zero]

/-- **`𝒪|_{Spec(𝔽₂)} ≠ 0`.**  Its sections over the identity of `Spec(𝔽₂) → Spec(ℤ)` are `𝔽₂`,
which is nontrivial. -/
public theorem not_isZero_restrictFtwo_unit :
    ¬ IsZero ((restrictFtwo B τ).obj (SheafOfModules.unit (bigStructureSheaf B τ))) := by
  intro h
  have : Nontrivial ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u) :=
    (sectionsRingEquiv B τ).toEquiv.nontrivial
  have h1 : (1 : ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u)) = 0 :=
    eq_zero_of_isZero h (op (Over.mk (𝟙 (ftwoObject B)))) _
  exact one_ne_zero h1

/-- The functor `𝓕 ↦ 𝓕^a|_{Spec(𝔽₂)}`: the associated module on `(Sch/Spec(ℤ))_τ` followed by
restriction to the slice at `Spec(𝔽₂) → Spec(ℤ)`. -/
public abbrev associatedRestrictFtwo :
    specInt.{u}.Modules ⥤
      SheafOfModules.{u} ((bigStructureSheaf B τ).over (ftwoObject B)) :=
  associatedModule B τ ⋙ restrictFtwo B τ

/-- **The image of `2 : 𝒪_S → 𝒪_S` under `𝓕 ↦ 𝓕^a|_{Spec(𝔽₂)}` is zero.** -/
public theorem map_two_nsmul_associatedRestrictFtwo :
    (associatedRestrictFtwo B τ).map (2 • 𝟙 unitModule.{u}) = 0 := by
  have := additive_associatedModule B τ
  have : (associatedRestrictFtwo B τ).Additive := inferInstance
  rw [two_nsmul, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_id, ← two_nsmul]
  exact two_nsmul_id_restrictFtwo_associated.{u} B τ

/-- **`𝓕^a|_{Spec(𝔽₂)} ≅ 𝒪_S^a|_{Spec(𝔽₂)}`.**  Both `𝓕 ↦ 𝓕^a` and restriction to a slice
preserve finite colimits, so the restriction of `𝓕^a = Coker(2 : 𝒪_S → 𝒪_S)^a` is the cokernel
of the image of `2 : 𝒪_S → 𝒪_S`, and that image is the **zero** map because every ring of
sections of `𝒪` on the slice has characteristic `2`. -/
public def associatedCokerTwoRestrictIso :
    (associatedRestrictFtwo B τ).obj cokerTwo.{u} ≅
      (associatedRestrictFtwo B τ).obj unitModule.{u} :=
  have := additive_associatedModule B τ
  have : PreservesFiniteColimits (associatedModule B τ) := inferInstance
  have : PreservesFiniteColimits (associatedRestrictFtwo B τ) := inferInstance
  PreservesCokernel.iso (associatedRestrictFtwo B τ) (2 • 𝟙 unitModule.{u}) ≪≫
    cokernelIsoOfEq (map_two_nsmul_associatedRestrictFtwo.{u} B τ) ≪≫ cokernelZeroIsoTarget

/-- **`SheafHom_𝒪(𝓕^a, 𝒪_S^a) ≠ 0` on `(Sch/Spec(ℤ))_τ`.**  The sections of the internal Hom of
Stacks 03EM over the object `Spec(𝔽₂) → Spec(ℤ)` are the morphisms
`𝓕^a|_{Spec(𝔽₂)} ⟶ 𝒪_S^a|_{Spec(𝔽₂)}`, and `associatedCokerTwoRestrictIso` is an isomorphism
between those two modules, hence a nonzero such morphism — this is the `2`-torsion `𝒪[2] ≠ 0`
of the source's proof. -/
public theorem not_isZero_internalHomSheaf :
    ¬ IsZero (RingedSite.internalHomSheaf
      (BigFppfOver.baseRingedSite B specInt.{u} (contains_specInt B) τ)
      ((associatedModule B τ).obj cokerTwo.{u})
      ((associatedModule B τ).obj unitModule.{u})) := by
  intro h
  have hval : (associatedCokerTwoRestrictIso.{u} B τ).hom.val = 0 :=
    eq_zero_of_isZero h (op (ftwoObject B)) _
  have hhom : (associatedCokerTwoRestrictIso.{u} B τ).hom = 0 :=
    SheafOfModules.hom_ext hval
  have hzero : IsZero ((associatedRestrictFtwo B τ).obj unitModule.{u}) := by
    rw [IsZero.iff_id_eq_zero, ← (associatedCokerTwoRestrictIso.{u} B τ).inv_hom_id, hhom,
      comp_zero]
  exact not_isZero_restrictFtwo_unit.{u} B τ
    (IsZero.of_iso hzero ((restrictFtwo B τ).mapIso (associatedModuleUnitIso B τ)).symm)

/-! ### The refutation -/

/-- **Stacks 06VE (9).**  Given two quasi-coherent `𝒪_S`-modules `𝓕`, `𝓖` one does **not** have
`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a = SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod((Sch/S)_τ, 𝒪)` in general: at
`S = Spec(ℤ)`, on every big fppf site containing it and at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the two are not isomorphic, for
`𝓕 = Coker(2 : 𝒪_S → 𝒪_S)` and `𝓖 = 𝒪_S`.

This is the example the source gives, and the two halves are the two named statements of this
file: the left-hand side is a zero object
(`AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.isZero_associatedModule_sheafHomModules`)
and the right-hand side is not
(`…not_isZero_internalHomSheaf`), the latter for the very reason clause (6) fails —
`Spec(𝔽₂)` is an object of `(Sch/S)_τ`.

`𝓕` is asserted to be **of finite presentation**, which is the source's "even if `𝓕` is of
finite presentation": the failure is not repaired by the hypothesis under which clause (8) holds
on the small sites.  It holds by construction, `𝓕` being the cokernel of a map
`𝒪_S → 𝒪_S` (Stacks 0H96, `Stacks.SheafOfModules.isFinitePresentation_cokernel`).  See the
implementation notes for why the conjunct is needed and not merely true.

All three modules in play — `𝓕`, `𝓖` and `SheafHom_{𝒪_S}(𝓕, 𝓖)` — are asserted to be
quasi-coherent, so both sides of the clause are values of the functor
`QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪)` the clause is about and not of some extension of it to all
`𝒪_S`-modules; that functor is
`AlgebraicGeometry.AssociatedModuleNotExact.associatedModuleQcoh`, and
`AlgebraicGeometry.AssociatedModuleSheafHomNotCommute.associatedModuleQcoh_obj` says it agrees
with the `associatedModule` written here on every quasi-coherent module, on the nose.

The universe lift is the canonical fully faithful `Stacks.SheafOfModules.moduleULift`: the
internal Hom of Stacks 03EM on the big site raises the module universe by construction, so the
two sides of the clause are objects of two different categories.  See the implementation notes
of this file; the zero/nonzero dichotomy above is universe-free and is the real content. -/
@[stacks 06VE "part (9): the sheaf Hom does NOT commute with 𝓕 ↦ 𝓕ᵃ on the big site, at \
S = Spec ℤ, and not even when 𝓕 is of finite presentation"]
public theorem exists_isQuasicoherent_not_iso_sheafHom :
    ∃ F G : specInt.{u}.Modules, F.IsQuasicoherent ∧ G.IsQuasicoherent ∧
      F.IsFinitePresentation ∧ (sheafHomModules F G).IsQuasicoherent ∧
      ¬ Nonempty ((Stacks.SheafOfModules.moduleULift.{u + 1, u}
            (bigStructureSheaf B τ)).obj
            ((associatedModule B τ).obj (sheafHomModules F G)) ≅
          RingedSite.internalHomSheaf
            (BigFppfOver.baseRingedSite B specInt.{u} (contains_specInt B) τ)
            ((associatedModule B τ).obj F) ((associatedModule B τ).obj G)) := by
  refine ⟨cokerTwo.{u}, unitModule.{u}, inferInstance, inferInstance,
    Stacks.SheafOfModules.isFinitePresentation_cokernel (2 • 𝟙 unitModule.{u}),
    inferInstance, ?_⟩
  rintro ⟨e⟩
  refine not_isZero_internalHomSheaf.{u} B τ (IsZero.of_iso ?_ e.symm)
  exact (Stacks.SheafOfModules.moduleULift.{u + 1, u} (bigStructureSheaf B τ)).map_isZero
    (isZero_associatedModule_sheafHomModules.{u} B τ)

end

end AlgebraicGeometry.AssociatedModuleSheafHomNotCommute

end

end
