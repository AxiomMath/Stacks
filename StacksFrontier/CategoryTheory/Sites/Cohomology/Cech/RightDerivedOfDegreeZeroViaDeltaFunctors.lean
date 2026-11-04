module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianPresheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology is the right derived functor of its degree-zero part

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of whose
finite nonempty fibre products exist. Stacks 03AU asserts that the Čech cohomology functors
`ČH ⁿ(E, -)` on abelian presheaves are the higher right derived functors of `ČH ⁰(E, -)`.

The proof is the one in the source, Stacks 010T and 010U. Both families are cohomological
δ-functors: Čech cohomology by Stacks 03AR, the right derived functors by Stacks 05TE. Both are
universal, because both vanish on injective presheaves in positive degrees — the Čech side by
Stacks 03OR, the derived side because higher right derived functors always do. Two universal
δ-functors with isomorphic degree-zero parts are isomorphic in every degree (Stacks 010U), and
the degree-zero parts agree because the degree-zero part of *any* δ-functor is left exact, so
`R ⁰` of it is itself.

## Main definitions

* `Stacks.CechSite.cechCohomologyZeroFunctor`: degree-zero Čech cohomology as a functor on
  abelian presheaves.
* `Stacks.CechSite.cechCohomologyRightDerived`,
  `Stacks.CechSite.cechCohomologyRightDerivedPlus`: its higher right derived functors, in
  Mathlib's `ℕ`-indexed and the derived category's `ℤ`-indexed form.
* `Stacks.CechSite.cechCohomologyDeltaIsoRightDerived`: the isomorphism of δ-functors between
  Čech cohomology and the right derived functors of its degree-zero part.
* `Stacks.CechSite.rightDerivedCechDeltaFunctor`: those right derived functors packaged with
  their universal δ-functor structure.
* `Stacks.CechSite.cechH0IsoRightDerivedPlusZero`: the normalized degree-zero comparison.

## Main results

* `Stacks.CechSite.cechCohomologyIsoRightDerived`: for each `n`, the natural isomorphism
  `ČH ⁿ(E, -) ≅ R ⁿ(ČH ⁰(E, -))` of functors on abelian presheaves.
* `Stacks.CechSite.cechCohomologyIsoRightDerivedPlus`: the same against
  `CategoryTheory.Functor.rightDerivedPlus`.
* `Stacks.CechSite.existsUnique_cechCohomologyDeltaFunctorIso`: the δ-functor isomorphism is
  unique with its prescribed degree-zero component.
* `Stacks.CechSite.presheafEnoughInjectives`: abelian presheaves have enough injectives
  (Stacks 01DK). Every result above discharges its `EnoughInjectives` need from this, so none
  of them carries it as a hypothesis.

## Implementation notes

**Left exactness of `ČH ⁰` is not proved here, and needs nothing about `homologyFunctor`.** It
is a formal consequence of the δ-functor structure of Stacks 03AR: `exact_map` at degree `0`
together with `mono_map_f` says exactly that `0 → ČH ⁰(F₁) → ČH ⁰(F₂) → ČH ⁰(F₃)` is exact for
every short exact sequence of presheaves, and for an additive functor between abelian
categories that is `PreservesFiniteLimits`. This is
`Stacks.Cohomology.CechDerived.preservesFiniteLimits_functor_zero`, already proved generically
for every `DeltaFunctor`; `Stacks.Cohomology.CechDerived.isoRightDerivedZero` and
`Stacks.RightDerivedPlus.rightDerivedPlusZeroIso` are the two degree-zero comparisons built
from it.

**No part of the δ-functor structure on the right derived functors is rebuilt here.** It is the
generic `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, whose
component functors are `Functor.rightDerived` by `rfl`, transported to the `ℤ`-indexing by
`Stacks.DerivedIndexing.deltaFunctorOfNatIso` along
`Stacks.DerivedIndexing.rightDerivedIso`. The elaboration cost of the assembly is paid once
inside `CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal`, so nothing
here needs a heartbeat allowance: `rightDerivedCechDeltaFunctor` costs 6177
heartbeats and `existsUnique_cechCohomologyDeltaFunctorIso` 1268, against a default of 200000.

**`EnoughInjectives` cannot be an instance at this universe shape, and is discharged in bodies
instead.** The coefficient universe is `max w u v a`, with `w` (the family index) and `a` (the
coefficients) free, so an instance asserting enough injectives for
`Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}` has universe parameters occurring only inside a `max`, and
instance search is left with `max u v ?w ?a =?= max w u v a`, on which the level unifier is
stuck (`stuck at solving universe constraint`). It is therefore supplied by an
explicitly universe-ascribed `letI` inside each definition and proof, which is why no statement
in this file carries it. The same applies to `PreservesFiniteLimits` of `ČH ⁰`, which is a
`local instance` here because its universes are all pinned by its subject.

**Two elaboration pitfalls.** First, writing
`Stacks.DerivedIndexing.rightDerivedIso _ n` or
`Functor.isZero_rightDerivedPlus_obj_injective _ i h I` with the functor left implicit makes
the elaborator solve `?F.rightDerivedPlus i ≟ cechCohomologyRightDerivedPlus E i`, and that
times out at 200000 heartbeats; naming the functor makes the same declaration elaborate in
seconds. Second, `(rightDerivedPlusDeltaFunctor F _ _ _).functor n = _` by `rfl` also times
out, because the projection forces the whole δ-functor assembly through `whnf`; going through
`deltaFunctorOfNatIso`, whose `functor` field is the given family, makes it immediate.

The coefficient universe contains the object, morphism and family-index universes, so that the
vanishing result of Stacks 03OR, whose integral Čech complex lives in that universe, applies.

## References

* [Stacks Project, Tag 03AU](https://stacks.math.columbia.edu/tag/03AU)
* [Stacks Project, Tag 03AR](https://stacks.math.columbia.edu/tag/03AR)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
* [Stacks Project, Tag 01DK](https://stacks.math.columbia.edu/tag/01DK)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DeltaFunctor

universe v v' u u'

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] {F G : DeltaFunctor A B}

/-- The degree-`n` component of an isomorphism of cohomological δ-functors, as an isomorphism
of functors. -/
def isoApp (e : F ≅ G) (n : ℕ) : F.functor n ≅ G.functor n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := congrArg (fun η : F ⟶ F ↦ η.app n) e.hom_inv_id
  inv_hom_id := congrArg (fun η : G ⟶ G ↦ η.app n) e.inv_hom_id

/-- The forward map of `CategoryTheory.DeltaFunctor.isoApp` is the degree-`n` component of the
forward map of the isomorphism of δ-functors. -/
@[simp]
lemma isoApp_hom (e : F ≅ G) (n : ℕ) : (isoApp e n).hom = e.hom.app n := rfl

/-- The inverse of `CategoryTheory.DeltaFunctor.isoApp` is the degree-`n` component of the inverse
of the isomorphism of δ-functors. -/
@[simp]
lemma isoApp_inv (e : F ≅ G) (n : ℕ) : (isoApp e n).inv = e.inv.app n := rfl

end CategoryTheory.DeltaFunctor

namespace Stacks.CechSite

universe w v a u t

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- **Stacks 01DK.** Abelian presheaves on `C` have enough injectives, in any coefficient
universe containing those of the site. Every result below discharges its `EnoughInjectives`
need from this, so none of them carries it as a hypothesis. -/
theorem presheafEnoughInjectives :
    EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u v t}) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    (Stacks.Injectives.presheaf_hasFunctorialInjectiveEmbeddings.{u, v, t} C)

/-- Degree-zero Čech cohomology of the family `E`, as a functor on abelian presheaves: the
degree-zero part of the cohomological δ-functor of Stacks 03AR. -/
noncomputable abbrev cechCohomologyZeroFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) ⥤ AddCommGrpCat.{max w u v a} :=
  (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1.functor 0

/-- The `n`-th right derived functor of degree-zero Čech cohomology. -/
noncomputable def cechCohomologyRightDerived (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) ⥤ AddCommGrpCat.{max w u v a} :=
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  (cechCohomologyZeroFunctor.{w, v, a, u} E).rightDerived n

/-- The `n`-th right derived functor of degree-zero Čech cohomology in the `ℤ`-indexed form of
the bounded-below derived category. -/
noncomputable def cechCohomologyRightDerivedPlus (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) ⥤ AddCommGrpCat.{max w u v a} :=
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  (cechCohomologyZeroFunctor.{w, v, a, u} E).rightDerivedPlus (n : ℤ)

/-- The right derived functors of degree-zero Čech cohomology as a cohomological δ-functor:
the generic `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, with
the `EnoughInjectives` need discharged. -/
noncomputable def cechRightDerivedDeltaFunctor :
    DeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) AddCommGrpCat.{max w u v a} :=
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (cechCohomologyZeroFunctor.{w, v, a, u} E)

/-- Its component functors are the right derived functors, on the nose. -/
theorem cechRightDerivedDeltaFunctor_functor (n : ℕ) :
    (cechRightDerivedDeltaFunctor.{w, v, a, u} E).functor n =
      cechCohomologyRightDerived.{w, v, a, u} E n := rfl

/-- **Stacks 03OR, 010T.** The Čech cohomology δ-functor is universal: its higher terms vanish
on injective presheaves. -/
theorem isUniversal_cechCohomologyDeltaFunctor :
    (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1.IsUniversal := by
  have : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  refine DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ ↦ ?_
  rw [(cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).2 (n + 1)]
  exact injective_presheaf_cechCohomology_isZero.{w, v, u, a} E I (n + 1) n.succ_pos

/-- **Stacks 010T.** The δ-functor of the higher right derived functors of degree-zero Čech
cohomology is universal: higher right derived functors vanish on injectives. -/
theorem isUniversal_cechRightDerivedDeltaFunctor :
    (cechRightDerivedDeltaFunctor.{w, v, a, u} E).IsUniversal := by
  have : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  exact DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ ↦
    Functor.isZero_rightDerived_obj_injective_succ (cechCohomologyZeroFunctor.{w, v, a, u} E) n I

/-- **Stacks 03AU.** Čech cohomology and the higher right derived functors of its degree-zero
part are isomorphic as cohomological δ-functors: both are universal (Stacks 010T) and their
degree-zero parts agree, so Stacks 010U applies. -/
noncomputable def cechCohomologyDeltaIsoRightDerived :
    (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1 ≅
      cechRightDerivedDeltaFunctor.{w, v, a, u} E := by
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  letI := isUniversal_cechCohomologyDeltaFunctor.{w, v, a, u} E
  letI := isUniversal_cechRightDerivedDeltaFunctor.{w, v, a, u} E
  exact DeltaFunctor.IsUniversal.isoOfIso
    (Stacks.Cohomology.CechDerived.isoRightDerivedZero
      (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1).symm

/-- **Stacks 03AU.** For each `n`, the natural isomorphism `ČH ⁿ(E, -) ≅ R ⁿ(ČH ⁰(E, -))` of
functors on abelian presheaves.

This is also [Stacks Project, Tag 03OS], the Étale Cohomology chapter's form of the same
statement: on abelian presheaves the functors `Ȟ ᵖ(U, -)` are the right derived functors of
`Ȟ ⁰(U, -)`. -/
@[stacks 03OS "the isomorphism in each degree"]
noncomputable def cechCohomologyIsoRightDerived (n : ℕ) :
    cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max w u v a} (ComplexShape.up ℕ) n ≅
      cechCohomologyRightDerived.{w, v, a, u} E n :=
  eqToIso ((cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).2 n).symm ≪≫
    DeltaFunctor.isoApp (cechCohomologyDeltaIsoRightDerived.{w, v, a, u} E) n ≪≫
    eqToIso (cechRightDerivedDeltaFunctor_functor.{w, v, a, u} E n)

/-- **Stacks 03AU.** The same comparison against the `ℤ`-indexed right derived functor of the
bounded-below derived category. -/
noncomputable def cechCohomologyIsoRightDerivedPlus (n : ℕ) :
    cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max w u v a} (ComplexShape.up ℕ) n ≅
      cechCohomologyRightDerivedPlus.{w, v, a, u} E n :=
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  cechCohomologyIsoRightDerived.{w, v, a, u} E n ≪≫
    Stacks.DerivedIndexing.rightDerivedIso (cechCohomologyZeroFunctor.{w, v, a, u} E) n

/-! ### The packaging of Tag 03AU

The three statements below are the same mathematics in the shape the statement of Tag 03AU has: the
right derived functors as a universal δ-functor, the normalized degree-zero comparison, and the
unique δ-functor isomorphism between the two. -/

/-- Degree-zero Čech cohomology is left exact. This is `exact_map` at degree `0` together with
`mono_map_f` for the δ-functor of Stacks 03AR, and nothing else. -/
local instance preservesFiniteLimits_cechCohomologyZeroFunctor :
    PreservesFiniteLimits (cechCohomologyZeroFunctor.{w, v, a, u} E) :=
  Stacks.Cohomology.CechDerived.preservesFiniteLimits_functor_zero
    (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1

/-- The canonical comparison `R ⁰(ČH ⁰) ≅ ČH ⁰`: `H ⁰` of the unit of the right derived functor,
invertible because `ČH ⁰` is left exact. -/
noncomputable def cechH0RightDerivedPlusZeroIso :
    cechCohomologyRightDerivedPlus.{w, v, a, u} E 0 ≅
      cechCohomologyZeroFunctor.{w, v, a, u} E :=
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (cechCohomologyZeroFunctor.{w, v, a, u} E)

/-- **Stacks 03AU.** The degree-zero Čech cohomology functor is its own zeroth right derived
functor, normalized by `H ⁰` of the unit of the right derived functor. -/
@[stacks 03AU "the degree-zero comparison"]
noncomputable def cechH0IsoRightDerivedPlusZero :
    { e : cechCohomologyZeroFunctor.{w, v, a, u} E ≅
        cechCohomologyRightDerivedPlus.{w, v, a, u} E 0 //
      e.hom = (cechH0RightDerivedPlusZeroIso.{w, v, a, u} E).inv } :=
  ⟨(cechH0RightDerivedPlusZeroIso.{w, v, a, u} E).symm, rfl⟩

/-- **Stacks 03AU.** The higher right derived functors of degree-zero Čech cohomology, equipped
with their universal cohomological δ-functor structure. -/
@[stacks 03AU "the delta functor of higher right derived functors"]
noncomputable def rightDerivedCechDeltaFunctor :
    { R : DeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) AddCommGrpCat.{max w u v a} //
      (∀ n : ℕ, R.functor n = cechCohomologyRightDerivedPlus.{w, v, a, u} E n) ∧
      R.IsUniversal } := by
  letI : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  refine ⟨Stacks.DerivedIndexing.deltaFunctorOfNatIso
      (cechRightDerivedDeltaFunctor.{w, v, a, u} E)
      (fun n ↦ cechCohomologyRightDerivedPlus.{w, v, a, u} E n)
      (fun n ↦ Stacks.DerivedIndexing.rightDerivedIso
        (cechCohomologyZeroFunctor.{w, v, a, u} E) n), fun _ ↦ rfl, ?_⟩
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  change IsZero ((cechCohomologyRightDerivedPlus.{w, v, a, u} E (n + 1)).obj I)
  exact Functor.isZero_rightDerivedPlus_obj_injective
    (cechCohomologyZeroFunctor.{w, v, a, u} E) ((n + 1 : ℕ) : ℤ) (by omega) I

/-- **Stacks 03AU.** Čech cohomology is canonically isomorphic, as a cohomological δ-functor, to
the higher right derived functors of degree-zero Čech cohomology. The isomorphism is unique with
its prescribed degree-zero component. -/
@[stacks 03AU "the canonical delta-functor isomorphism",
  stacks 03OS "the delta-functor isomorphism", sga "7 VI 3.1(b)" "H^p = R^p H^0 of cover"]
theorem existsUnique_cechCohomologyDeltaFunctorIso :
    ∃! e : (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1 ≅
        (rightDerivedCechDeltaFunctor.{w, v, a, u} E).1,
      e.hom.app 0 = (cechH0IsoRightDerivedPlusZero.{w, v, a, u} E).1.hom ≫
        eqToHom ((rightDerivedCechDeltaFunctor.{w, v, a, u} E).2.1 0).symm := by
  have : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max w u v a}) :=
    presheafEnoughInjectives.{v, u, max w a} (C := C)
  have := isUniversal_cechCohomologyDeltaFunctor.{w, v, a, u} E
  have := (rightDerivedCechDeltaFunctor.{w, v, a, u} E).2.2
  set e₀ := (cechH0IsoRightDerivedPlusZero.{w, v, a, u} E).1 ≪≫
    eqToIso ((rightDerivedCechDeltaFunctor.{w, v, a, u} E).2.1 0).symm with he₀
  refine ⟨DeltaFunctor.IsUniversal.isoOfIso e₀, ?_, fun e' he' ↦
    DeltaFunctor.IsUniversal.iso_ext (he'.trans ?_)⟩ <;> simp [he₀]

end Stacks.CechSite

end
