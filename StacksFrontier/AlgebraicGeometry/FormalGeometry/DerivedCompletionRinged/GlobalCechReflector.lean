module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionIdempotent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeLocalReflector
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalExtendedCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.NilpotentIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafCondition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# From the global complex of Tag 099E to the reflector of Tag 099F

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊆ 𝒪` a sheaf of ideals of finite type. This file carries
out the globalization step of [Stacks, Tag 099F]: the passage from a single map of complexes
`a : K ⟶ 𝒪` which is locally the extended alternating Čech complex of a generating family —
the conclusion `AlgebraicGeometry.RingedSite.IsGlobalExtendedCech` of [Stacks, Tag 099E] — to
the left adjoint of the inclusion `D_comp(𝒪, ℐ) ⥤ D(𝒪)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.completionFunctorOfComplex`: the endofunctor
  `E ↦ R𝑆heafHom_𝒪(K, E)` of `D(𝒪)` attached to a complex `K`.
* `AlgebraicGeometry.RingedSite.completionUnitOfComplex`: the map `E ⟶ R𝑆heafHom_𝒪(K, E)`
  attached to `a : K ⟶ 𝒪`, natural in `E`.
* `AlgebraicGeometry.RingedSite.structureSheafComplexOverIso`: the restriction of `𝒪` placed in
  degree zero, identified with the structure sheaf of the slice placed in degree zero.

## Main results

* `AlgebraicGeometry.RingedSite.completionFunctorOfComplexOverIso`: **the completion functor of
  a complex restricts to the completion functor of its restriction**, which is
  [Stacks, Tag 08JB] read at the first argument of the derived internal Hom.
* `AlgebraicGeometry.RingedSite.overTerminalRingHom_eq_globalSectionToEnd_awayFamily`: the two
  readings of multiplication by a section of `𝒪` over `U` on `D(𝒪_U)` — as a section over the
  terminal object of `𝒞/U`, and as a global section of `𝒪_U` — are the same central
  endomorphism.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_completionFunctorOfComplex`: **clause 1**,
  that `R𝑆heafHom_𝒪(K, E)` is derived complete along `ℐ` for every `E`.
* `AlgebraicGeometry.RingedSite.exists_eq_Q_map_cechAugmentation` and
  `RingedSite.exists_eq_derivedSheafHom_map_cechAugmentation_app_of_isGlobalExtendedCech`:
  the restriction of `a` to a slice, and the restriction of the completion map it induces, read
  as the Čech augmentation of that slice and the map it induces, up to isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_completionUnitOfComplex_app_of_isDerivedComplete`:
  **clause 2**, that `E ⟶ R𝑆heafHom_𝒪(K, E)` is invertible on derived-complete `E`.
* `AlgebraicGeometry.RingedSite.isIso_completionFunctorOfComplex_map_completionUnitOfComplex_app`:
  **clause 3**, that the completion functor carries the completion map to an isomorphism.
* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_isGlobalExtendedCech` and
  `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_exists_isGlobalExtendedCech`:
  **[Stacks, Tag 099F] for a finite-type sheaf of ideals, from the map of [Stacks, Tag 099E]**.
* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_isNilpotent_of_sieve`:
  the conclusion of [Stacks, Tag 099F] for a finite-type sheaf of ideals whose local sections
  become nilpotent on a covering, with the identity as left adjoint.

## Implementation notes

**Which locality does the work.** The reduction of `Reflection.lean` which this file feeds,
`Stacks.Algebraization.isRightAdjoint_ι_of_completionFunctor`, asks for the *invertibility* of
`Φ η_E` and not for the equality `Φ η_E = η_{Φ E}`; that is the form `CompletionIdempotent.lean`
discharges for the Čech completion, and it is what makes the globalization possible. All three
of its hypotheses are then local conditions: invertibility in `D(𝒪)` is local on the site by
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, the locality step of
[Stacks, Tag 08JJ], and derived completeness along `ℐ` is local by the sheaf condition of
[Stacks, Tag 0998], `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`. So no
reflector and no object of a derived category is ever glued: what is globalized is each clause
of the universal property, at the single global candidate `(Φ, η)` which [Stacks, Tag 099E]
supplies. In particular the slice reflectors of
`FiniteTypeLocalReflector.lean` never have to be glued as objects; that would be a route the
source does not take, and this file does not take it either.

**Why clause 1 needs no locality principle for the predicate.** Derived completeness along `ℐ`
is the Milnor condition at every local section of `ℐ`, and that condition is local on the site
by itself; the predicate `AlgebraicGeometry.RingedSite.IsDerivedComplete` never has to be
descended or ascended as a whole. At an object `Z` admitting a morphism to a member of the
finite-type covering family, the generating family restricts
(`Stacks.SheafOfModules.generates_restrict`), the Čech completion of [Stacks, Tag 099B] applies
on `𝒞/Z`, and `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_awayFamily_of_isDerivedComplete`
turns completeness along `ℐ|_Z` into the condition at the one section in hand.

**Term mode, and why.** `X.ringSheaf.over U` and `(X.over U).ringSheaf` are the same sheaf of
rings only after `AlgebraicGeometry.RingedSite.over` is unfolded, which the elaborator does and
the transparency at which `rw` and `simp` match their patterns does not. A composite that
crosses between them carries two instance terms which print identically and do not unify by
keyed matching, so `rw [Functor.map_comp]` and even `simp only [Category.assoc]` fail on it with
"did not find an occurrence" against a goal that displays the pattern verbatim. Every such step
below is therefore a term: `congrArg`, `Eq.trans`, `Eq.mpr (congrArg (fun m => IsIso m) h)`, and
`Stacks.Algebraization.isIso_map_of_isIso_map_middle`, which is stated for a bare functor
between bare categories precisely so that its one `Functor.map_comp` rewriting happens inside a
single category.

The functor and the unit are the ones of `Completion.lean` with the extended alternating Čech
complex `Č(f)` of a finite family of global sections replaced by an arbitrary complex: the
definitions there are this one at `K = Č(f)` and `a = cechAugmentation`, which is
`completionFunctorOfComplex_extendedAlternatingCech` and
`completionUnitOfComplex_cechAugmentation`, both true by `rfl`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u

namespace Stacks.Algebraization

/-- **A functor carries a composite whose outer factors are isomorphisms and whose middle factor
it inverts to an isomorphism.** Stated for a bare functor between bare categories, so that the
`CategoryTheory.Functor.map_comp` rewriting happens inside one category and not across two
spellings of the same sheaf of rings. -/
theorem isIso_map_of_isIso_map_middle {C : Type*} [CategoryTheory.Category C] {D : Type*}
    [CategoryTheory.Category D] (F : C ⥤ D) {W X Y Z : C} (α : W ≅ X) {m : X ⟶ Y} (β : Y ≅ Z)
    (hm : IsIso (F.map m)) :
    IsIso (F.map (α.hom ≫ m ≫ β.hom)) := by
  rw [F.map_comp, F.map_comp]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hm inferInstance)

end Stacks.Algebraization

namespace AlgebraicGeometry.RingedSite

section Complex

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]

/-- **The completion functor of a complex**: the endofunctor `E ↦ R𝑆heafHom_𝒪(K, E)` of `D(𝒪)`,
derived internal Hom out of a fixed complex `K` of `𝒪`-modules. For `K` the extended
alternating Čech complex of a finite family of global sections this is
`AlgebraicGeometry.RingedSite.completionFunctor` of [Stacks, Tag 099B]. -/
def completionFunctorOfComplex (K : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))

/-- **The completion map of a map of complexes `a : K ⟶ 𝒪`**, naturally in `E`: the
identification `E = R𝑆heafHom_𝒪(𝒪, E)` followed by the map which `a` induces on derived
internal Hom into `E`. -/
def completionUnitOfComplex {K : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : K ⟶ structureSheafComplex X) :
    𝟭 (DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶ completionFunctorOfComplex X K :=
  (derivedStructureSheafHomNatIso X).inv ≫
    (derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The completion functor of the extended alternating Čech complex of `f_1, …, f_r` is the
completion functor of [Stacks, Tag 099B] at those sections. -/
theorem completionFunctorOfComplex_extendedAlternatingCech :
    completionFunctorOfComplex X (extendedAlternatingCech X f) = completionFunctor X f :=
  rfl

/-- The completion map of the augmentation `Č(f) ⟶ 𝒪` is the completion map of
[Stacks, Tag 099B] at those sections. -/
theorem completionUnitOfComplex_cechAugmentation :
    completionUnitOfComplex X (cechAugmentation X f) = completionUnit X f :=
  rfl

end Complex

section Restrict

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] (U : X.C)
  [HasWeakSheafify (X.over U).J CommRingCat.{u}]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]

/-- **The completion functor of a complex restricts to the completion functor of the restricted
complex.** For every `K` and every `E` there is an isomorphism

`R𝑆heafHom_𝒪(K, E)|_U ≅ R𝑆heafHom_{𝒪_U}(K|_U, E|_U)`

in `D(𝒪_U)`. This is [Stacks, Tag 08JB] — `AlgebraicGeometry.RingedSite.derivedHomRestriction`
— followed by the identification of the restriction of the class of `K` with the class of the
restricted complex, `AlgebraicGeometry.RingedSite.restrictionComparison`, read in the
contravariant argument of the derived internal Hom. -/
def completionFunctorOfComplexOverIso (K : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
        ((completionFunctorOfComplex X K).obj E) ≅
      (completionFunctorOfComplex (X.over U) (restrictComplex X K U)).obj
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) :=
  (derivedHomRestriction X U).iso (DerivedCategory.Q.obj K) E ≪≫
    (((derivedSheafHomBifunctor (X.over U)).mapIso
      (restrictionComparison X U K).op).app
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)).symm

end Restrict

section Complete

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two readings of multiplication by a section of `𝒪` over `U` on the slice site agree.**
A section `y` of `𝒪` over `U` is a section over the terminal object `U ⟶ U` of `𝒞/U`, and it is
also a global section of the structure sheaf `𝒪_U` of the localized ringed site; the central
endomorphism of `D(𝒪_U)` it gives is the same both ways, because both compatible families take
the value `y|_{V}` at an object `V ⟶ U`. -/
theorem overTerminalRingHom_eq_globalSectionToEnd_awayFamily (U : X.C)
    [HasWeakSheafify (X.over U).J CommRingCat.{u}]
    (y : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) :
    overTerminalRingHom X U y =
      Stacks.SheafOfModules.globalSectionToEnd
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)
        (awayFamily (X.over U) (globalSectionOfSection X U y)) :=
  congrArg (Stacks.SheafOfModules.globalSectionToEnd
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))
    (Subtype.ext (funext fun V =>
      (Stacks.SheafOfModules.terminalSection_over_val
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U y V).trans
        (globalSectionVal_globalSectionOfSection X U y V).symm))

variable (I : SheafOfModules.Submodule (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The completion of a complex which restricts to a Čech complex is derived complete at every
section of `ℐ` over an object carrying a finite generating family.** Let `a : K ⟶ 𝒪` satisfy the
condition of [Stacks, Tag 099E] for `ℐ`, let `U` be an object on which finitely many global
sections `g_1, …, g_s` of `𝒪_U` generate `ℐ|_U`, and let `y` be a section of `ℐ` over `U`. Then
`T(R𝑆heafHom_𝒪(K, E)|_U, y) = 0`.

The restriction of the completion to `𝒞/U` is the Čech completion of `E|_U` at `g_1, …, g_s`,
by `completionFunctorOfComplexOverIso` and the isomorphism which [Stacks, Tag 099E] supplies;
that Čech completion is derived complete along `(g_1, …, g_s) = ℐ|_U` with no hypothesis, by
`isDerivedComplete_completionFunctor` of `CompletionIdempotent.lean`, which is clause 1 of
[Stacks, Tag 099B]; and `y` is a global section of `𝒪_U` all of whose restrictions are sections
of `ℐ|_U`, so `isDerivedCompleteAt_awayFamily_of_isDerivedComplete` of
`CompleteGlobalSection.lean` applies to it. -/
theorem isDerivedCompleteAtSection_completionFunctorOfComplex
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {a : K ⟶ structureSheafComplex X}
    (ha : IsGlobalExtendedCech X I K a) (U : X.C)
    [HasWeakSheafify (X.over U).J CommRingCat.{u}]
    [HasSheafify (X.over U).J AddCommGrpCat.{u}]
    [(X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
    (hg : idealOfGlobalSections (X.over U) g = overIdeal I U)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (y : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (hy : y ∈ I.toSubmodule.obj (op U)) :
    IsDerivedCompleteAtSection X ((completionFunctorOfComplex X K).obj E) U y := by
  obtain ⟨e, -⟩ := ha U s g hg
  have hiso : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
        ((completionFunctorOfComplex X K).obj E) ≅
      (completionFunctor (X.over U) g).obj
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) :=
    completionFunctorOfComplexOverIso X U K E ≪≫
      ((derivedSheafHomBifunctor (X.over U)).mapIso e.op).app
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)
  have hmem : ∀ V : (X.over U).C,
      globalSectionVal (globalSectionOfSection X U y) (op V) ∈
        (idealOfGlobalSections (X.over U) g).toSubmodule.obj (op V) := by
    intro V
    rw [hg]
    exact I.toSubmodule.map_mem (V.hom).op hy
  have hcomp := isDerivedCompleteAt_awayFamily_of_isDerivedComplete (X.over U)
    ((completionFunctor (X.over U) g).obj
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E))
    (globalSectionOfSection X U y) (idealOfGlobalSections (X.over U) g) hmem
    (isDerivedComplete_completionFunctor (X.over U) g _)
  show IsDerivedCompleteAt _ (overTerminalRingHom X U y)
  rw [overTerminalRingHom_eq_globalSectionToEnd_awayFamily X U y]
  exact (isDerivedCompleteAt_iff_of_iso hiso _).2 hcomp

variable [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **Clause 1 of [Stacks, Tag 099F] for a finite-type sheaf of ideals**: if `a : K ⟶ 𝒪`
satisfies the condition of [Stacks, Tag 099E] for a sheaf of ideals `ℐ` of finite type, then
`R𝑆heafHom_𝒪(K, E)` is derived complete along `ℐ` for every `E`.

Derived completeness along `ℐ` is the Milnor condition at every local section of `ℐ`, and that
condition is local on the site by
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve` — the sheaf condition of
[Stacks, Tag 0998]. The family of objects which the finite-type condition provides covers the
site, so every object is covered by objects admitting a morphism to a member `V_i`; over such an
object the generating family of `ℐ` over `V_i` restricts to a generating family, by
`Stacks.SheafOfModules.generates_restrict`, and
`isDerivedCompleteAtSection_completionFunctorOfComplex` applies there. -/
theorem isDerivedComplete_completionFunctorOfComplex
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {a : K ⟶ structureSheafComplex X}
    (ha : IsGlobalExtendedCech X I K a)
    (hI : PresheafOfModules.IsFiniteType X.J I.toSheafOfModules.val)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsDerivedComplete.{u, u, u, u} X I ((completionFunctorOfComplex X K).obj E) := by
  obtain ⟨κ, V, hV, hgen⟩ := hI.exists_generators
  rw [isDerivedComplete_iff_forall_isDerivedCompleteAtSection]
  intro W y hy
  refine IsDerivedCompleteAtSection.of_sieve X _ y (Sieve.ofObjects V W) (hV W) ?_
  intro Z c hc
  obtain ⟨i, ⟨d⟩⟩ := hc
  obtain ⟨n, s, hs⟩ := hgen i
  have : HasSheafify (X.J.over Z) AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u} (J := X.J.over Z)
  have : (X.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
      (J := X.J.over Z)
  exact isDerivedCompleteAtSection_completionFunctorOfComplex X I ha Z
    (fun j => globalSectionOfSection X Z (I.toSheafOfModules.val.restrictₛₗ d.op (s j)).val)
    (overIdeal_eq_idealOfGlobalSections_of_generates X Z I
      (fun j => I.toSheafOfModules.val.restrictₛₗ d.op (s j))
      (Stacks.SheafOfModules.generates_restrict (J := X.J) d s hs)).symm
    E _ (I.toSubmodule.map_mem c.op hy)

end Complete

section Unit

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] (U : X.C)
  [HasWeakSheafify (X.over U).J CommRingCat.{u}]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]

/-- **The restriction of `𝒪` placed in degree zero is the structure sheaf of the slice placed in
degree zero**: the component of `HomologicalComplex.singleMapHomologicalComplex` for the
restriction functor. This is the second factor of
`AlgebraicGeometry.RingedSite.restrictStructureSheafMap`. -/
def structureSheafComplexOverIso :
    restrictComplex X (structureSheafComplex X) U ≅ structureSheafComplex (X.over U) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (ComplexShape.up ℤ) (0 : ℤ)).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify (X.over U).J AddCommGrpCat.{u}] in
/-- `AlgebraicGeometry.RingedSite.restrictStructureSheafMap` is the degreewise restriction of
`a` followed by that identification. -/
theorem restrictStructureSheafMap_eq
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : K ⟶ structureSheafComplex X) :
    restrictStructureSheafMap X U a =
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a ≫ (structureSheafComplexOverIso X U).hom :=
  rfl

variable (I : SheafOfModules.Submodule (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The restriction of `a : K ⟶ 𝒪` to a slice is the Čech augmentation there, up to
isomorphism.** If `a` satisfies the condition of [Stacks, Tag 099E] for `ℐ` and the finitely
many global sections `g_1, …, g_s` of `𝒪_U` generate `ℐ|_U`, then the image of `a` in `D(𝒪_U)`
is the augmentation `Č(g) ⟶ 𝒪_U` of `Completion.lean` pre- and post-composed with
isomorphisms.

Two inputs: the compatibility clause of [Stacks, Tag 099E], which says that the isomorphism it
provides carries the restricted `a` to the augmentation; and the identification of the
restriction of the class of a complex with the class of the restricted complex,
`AlgebraicGeometry.RingedSite.restrictionComparison`, which is natural in the complex. The
equality is up to isomorphism rather than on the nose because the restriction of `𝒪` placed in
degree zero is the structure sheaf of the slice only up to the comparison
`structureSheafComplexOverIso`. -/
theorem exists_eq_Q_map_cechAugmentation
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {a : K ⟶ structureSheafComplex X}
    (ha : IsGlobalExtendedCech X I K a)
    {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
    (hg : idealOfGlobalSections (X.over U) g = overIdeal I U) :
    ∃ (uu : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj K) ≅
          DerivedCategory.Q.obj (extendedAlternatingCech (X.over U) g))
      (w : DerivedCategory.Q.obj (structureSheafComplex (X.over U)) ≅
          (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj (structureSheafComplex X))),
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          (DerivedCategory.Q.map a) =
        uu.hom ≫ DerivedCategory.Q.map (cechAugmentation (X.over U) g) ≫ w.hom := by
  obtain ⟨e, he⟩ := ha U s g hg
  have h2 : e.inv ≫ DerivedCategory.Q.map (cechAugmentation (X.over U) g) =
      DerivedCategory.Q.map (restrictStructureSheafMap X U a) :=
    (congrArg (fun m => e.inv ≫ m) he.symm).trans (Iso.inv_hom_id_assoc e _)
  have h1 : DerivedCategory.Q.map
        (((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a) ≫
        DerivedCategory.Q.map (structureSheafComplexOverIso X U).hom =
      DerivedCategory.Q.map (restrictStructureSheafMap X U a) :=
    (DerivedCategory.Q.map_comp _ _).symm
  have hkey0 : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (DerivedCategory.Q.map a) ≫
        ((DerivedCategory.Q.mapIso (structureSheafComplexOverIso X U)).symm ≪≫
          (restrictionComparison X U (structureSheafComplex X)).symm).inv =
      (restrictionComparison X U K).hom ≫ e.inv ≫
        DerivedCategory.Q.map (cechAugmentation (X.over U) g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ DerivedCategory.Q.map (structureSheafComplexOverIso X U).hom)
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors_hom_naturality
          a)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun m => (restrictionComparison X U K).hom ≫ m) (h1.trans h2.symm))))
  exact ⟨restrictionComparison X U K ≪≫ e.symm,
    (DerivedCategory.Q.mapIso (structureSheafComplexOverIso X U)).symm ≪≫
      (restrictionComparison X U (structureSheafComplex X)).symm,
    ((Iso.comp_inv_eq _).1 hkey0).trans
      (((Category.assoc _ _ _).trans
          (congrArg (fun m => (restrictionComparison X U K).hom ≫ m)
            (Category.assoc _ _ _))).trans (Category.assoc _ _ _).symm)⟩

/-- **The map which the restricted `a` induces on derived internal Hom is the one the Čech
augmentation of the slice induces, up to isomorphism.** This is
`exists_eq_Q_map_cechAugmentation` read through the contravariant argument of the derived
internal Hom of the slice, where a composite becomes a composite and an isomorphism stays an
isomorphism. Stated as an equality, not merely as an equivalence of invertibility, because the
third clause of [Stacks, Tag 099F] needs it under a further functor. -/
theorem exists_eq_derivedSheafHomBifunctor_map_cechAugmentation_app
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {a : K ⟶ structureSheafComplex X}
    (ha : IsGlobalExtendedCech X I K a)
    {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
    (hg : idealOfGlobalSections (X.over U) g = overIdeal I U)
    (M : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) :
    ∃ (i : (((derivedSheafHomBifunctor (X.over U)).obj
            (op ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (structureSheafComplex X))))).obj M) ≅
          (((derivedSheafHomBifunctor (X.over U)).obj
            (op (DerivedCategory.Q.obj (structureSheafComplex (X.over U))))).obj M))
      (j : (((derivedSheafHomBifunctor (X.over U)).obj
            (op (DerivedCategory.Q.obj (extendedAlternatingCech (X.over U) g)))).obj M) ≅
          (((derivedSheafHomBifunctor (X.over U)).obj
            (op ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
              (DerivedCategory.Q.obj K)))).obj M)),
      (((derivedSheafHomBifunctor (X.over U)).map
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
            (DerivedCategory.Q.map a)).op).app M) =
        i.hom ≫ (((derivedSheafHomBifunctor (X.over U)).map
          (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op).app M) ≫ j.hom := by
  obtain ⟨uu, w, hkey⟩ := exists_eq_Q_map_cechAugmentation X U I ha g hg
  refine ⟨((derivedSheafHomBifunctor (X.over U)).mapIso w.op).app M,
    ((derivedSheafHomBifunctor (X.over U)).mapIso uu.op).app M, ?_⟩
  rw [hkey]
  refine Eq.trans (congrArg (fun α => NatTrans.app α M)
    ((((derivedSheafHomBifunctor (X.over U)).map_comp
        (w.hom.op ≫ (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op)
        uu.hom.op).trans
      (congrArg (fun β => β ≫ (derivedSheafHomBifunctor (X.over U)).map uu.hom.op)
        ((derivedSheafHomBifunctor (X.over U)).map_comp w.hom.op
          (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op))))) ?_
  exact Category.assoc _ _ _

end Unit

section Reflector

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : SheafOfModules.Submodule (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

omit [HasWeakSheafify X.J CommRingCat.{u}] [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Derived completeness descends to a slice**, in the spelling of this file: if `E` is derived
complete along `ℐ` then `E|_U` is derived complete along `ℐ|_U`. This is [Stacks, Tag 0A0F] with
the instances of the restriction functor fixed rather than quantified, which is the form the
clauses below consume. -/
theorem isDerivedComplete_overIdeal_overFunctor_mapDerivedCategory_obj
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : IsDerivedComplete.{u, u, u, u} X I E) (U : X.C) :
    IsDerivedComplete.{u, u, u, u} (X.over U) (overIdeal I U)
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E) :=
  (isDerivedComplete_iff_forall_isDerivedCompleteAtSection (X.over U) _ _).2 fun W y hy =>
    isDerivedCompleteAt_overFunctor_of_isDerivedCompleteAtSection X E U W y
      ((isDerivedComplete_iff_forall_isDerivedCompleteAtSection X E I).1 hE W.left y hy)

variable {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  {a : K ⟶ structureSheafComplex X}

omit [HasWeakSheafify X.J CommRingCat.{u}] [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The restriction to a slice of the map which `a` induces on derived internal Hom.** The
first-variable naturality of [Stacks, Tag 08JB], with the comparison isomorphism moved to the
right-hand side. -/
theorem overFunctor_mapDerivedCategory_map_derivedSheafHomBifunctor_map_app (U : X.C)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app E) =
      ((derivedHomRestriction X U).iso
          (DerivedCategory.Q.obj (structureSheafComplex X)) E).hom ≫
        (((derivedSheafHomBifunctor (X.over U)).map
          ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
            (DerivedCategory.Q.map a)).op).app
              ((SheafOfModules.overFunctor.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)) ≫
          ((derivedHomRestriction X U).iso (DerivedCategory.Q.obj K) E).inv :=
  ((Iso.eq_comp_inv _).2 ((derivedHomRestriction X U).natural_left
      (K := DerivedCategory.Q.obj (structureSheafComplex X)) (K' := DerivedCategory.Q.obj K)
      (L := E) (DerivedCategory.Q.map a))).trans (Category.assoc _ _ _)

omit [HasWeakSheafify X.J CommRingCat.{u}] [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction of the completion map of `a` splits as the restriction of the identification
`E = R𝑆heafHom_𝒪(𝒪, E)` followed by the restriction of the map `a` induces. -/
theorem overFunctor_mapDerivedCategory_map_completionUnitOfComplex_app (U : X.C)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        ((completionUnitOfComplex X a).app E) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          ((derivedStructureSheafHomNatIso X).inv.app E) ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app E) :=
  (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map_comp _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The completion map of the Čech augmentation splits as the identification
`M = R𝑆heafHom_{𝒪_U}(𝒪_U, M)` followed by the map the augmentation induces. -/
theorem completionUnit_app_eq (U : X.C) [HasWeakSheafify (X.over U).J CommRingCat.{u}]
    {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
    (M : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) :
    (completionUnit (X.over U) g).app M =
      (derivedStructureSheafHomNatIso (X.over U)).inv.app M ≫
        (((derivedSheafHomBifunctor (X.over U)).map
          (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op).app M) :=
  rfl

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The restriction of the completion map of `a` to a slice is the map the Čech augmentation of
that slice induces, up to isomorphism.** Three inputs: the splitting of the completion map into
the identification `E = R𝑆heafHom_𝒪(𝒪, E)` and the map `a` induces; the first-variable
naturality of [Stacks, Tag 08JB], which restricts the second factor; and
`exists_eq_derivedSheafHomBifunctor_map_cechAugmentation_app`, which recognises the restricted
`a` as the Čech augmentation of the slice. Both clauses below are read off this.

The middle factor is left as the three-fold composite the last of those produces, rather than
absorbed into the two isomorphisms, so that the only category-theoretic step here is a single
associativity. -/
theorem exists_eq_derivedSheafHom_map_cechAugmentation_app_of_isGlobalExtendedCech
    (ha : IsGlobalExtendedCech X I K a) (U : X.C)
    {s : ℕ} (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}))
    (hg : idealOfGlobalSections (X.over U) g = overIdeal I U)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (A B : DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))
      (α : (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E ≅ A)
      (β : B ≅ (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
            ((completionFunctorOfComplex X K).obj E))
      (p : A ≅ (((derivedSheafHomBifunctor (X.over U)).obj
            (op (DerivedCategory.Q.obj (structureSheafComplex (X.over U))))).obj
              ((SheafOfModules.overFunctor.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)))
      (q : (((derivedSheafHomBifunctor (X.over U)).obj
            (op (DerivedCategory.Q.obj (extendedAlternatingCech (X.over U) g)))).obj
              ((SheafOfModules.overFunctor.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)) ≅ B),
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
          ((completionUnitOfComplex X a).app E) =
        α.hom ≫ (p.hom ≫ (((derivedSheafHomBifunctor (X.over U)).map
          (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op).app
            ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)) ≫
              q.hom) ≫ β.hom := by
  obtain ⟨p, q, hpq⟩ := exists_eq_derivedSheafHomBifunctor_map_cechAugmentation_app X U I ha g hg
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)
  refine ⟨_, _, (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.mapIso
        ((derivedStructureSheafHomNatIso X).symm.app E) ≪≫
      (derivedHomRestriction X U).iso (DerivedCategory.Q.obj (structureSheafComplex X)) E,
    ((derivedHomRestriction X U).iso (DerivedCategory.Q.obj K) E).symm, p, q, ?_⟩
  refine Eq.trans
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map_comp
      ((derivedStructureSheafHomNatIso X).inv.app E)
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map a).op).app E)) ?_
  refine Eq.trans (congrArg (fun m =>
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        ((derivedStructureSheafHomNatIso X).inv.app E) ≫ m)
    ((overFunctor_mapDerivedCategory_map_derivedSheafHomBifunctor_map_app X U E).trans
      (congrArg (fun m => ((derivedHomRestriction X U).iso
          (DerivedCategory.Q.obj (structureSheafComplex X)) E).hom ≫ m ≫
            ((derivedHomRestriction X U).iso (DerivedCategory.Q.obj K) E).inv) hpq))) ?_
  exact (Category.assoc _ _ _).symm

/-- A map in `D(𝒪)` is invertible if its restriction to every slice carrying a finite generating
family of `ℐ` is, for every such family. -/
private theorem isIso_of_forall_generators (X : RingedSite.{u, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : SheafOfModules.Submodule (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K' L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K' ⟶ L) (hI : PresheafOfModules.IsFiniteType X.J I.toSheafOfModules.val)
    (h : ∀ (U : X.C) {s : ℕ}
      (g : Fin s → Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u})),
      idealOfGlobalSections (X.over U) g = overIdeal I U →
      IsIso ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map f)) :
    IsIso f := by
  obtain ⟨κ, V, hV, hgen⟩ := hI.exists_generators
  refine Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory hV _ fun i => ?_
  obtain ⟨n, s, hs⟩ := hgen i
  exact h (V i) _ (overIdeal_eq_idealOfGlobalSections_of_generates X (V i) I s hs).symm

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **Clause 2 of [Stacks, Tag 099F] for a finite-type sheaf of ideals**: if `a : K ⟶ 𝒪`
satisfies the condition of [Stacks, Tag 099E] for `ℐ` of finite type, the completion map
`E ⟶ R𝑆heafHom_𝒪(K, E)` is invertible on every `E` derived complete along `ℐ`.

Invertibility in `D(𝒪)` is local on the site
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, the locality step of
[Stacks, Tag 08JJ]). On a member of the covering family which the finite-type condition supplies
the restricted map is, by
`exists_eq_derivedSheafHom_map_cechAugmentation_app_of_isGlobalExtendedCech`, the map which the
Čech augmentation of the slice induces, up to isomorphism; and that one is invertible because
the Čech completion map of [Stacks, Tag 099B] is invertible on the restriction of `E`, which is
derived complete along the restricted ideal sheaf. -/
theorem isIso_completionUnitOfComplex_app_of_isDerivedComplete
    (ha : IsGlobalExtendedCech X I K a)
    (hI : PresheafOfModules.IsFiniteType X.J I.toSheafOfModules.val)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : IsDerivedComplete.{u, u, u, u} X I E) :
    IsIso ((completionUnitOfComplex X a).app E) := by
  refine isIso_of_forall_generators X I _ hI fun U s g hg => ?_
  obtain ⟨A, B, α, β, p, q, hαβ⟩ :=
    exists_eq_derivedSheafHom_map_cechAugmentation_app_of_isGlobalExtendedCech X I ha U g hg E
  have hcu : IsIso ((completionUnit (X.over U) g).app
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)) :=
    isIso_completionUnit_app_of_isDerivedComplete_idealOfGlobalSections (X.over U) _ _
      (hg ▸ isDerivedComplete_overIdeal_overFunctor_mapDerivedCategory_obj X I E hE U)
  have hcech := @IsIso.of_isIso_comp_left _ _ _ _ _
    ((derivedStructureSheafHomNatIso (X.over U)).inv.app _)
    (((derivedSheafHomBifunctor (X.over U)).map
      (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op).app _) _ hcu
  exact Eq.mpr (congrArg (fun m => IsIso m) hαβ)
    (IsIso.comp_isIso' (Iso.isIso_hom α)
      (IsIso.comp_isIso' (IsIso.comp_isIso' (Iso.isIso_hom p)
        (IsIso.comp_isIso' hcech (Iso.isIso_hom q))) (Iso.isIso_hom β)))

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **Clause 3 of [Stacks, Tag 099F] for a finite-type sheaf of ideals**: the completion functor
of `K` carries its own completion map to an isomorphism. This is the hypothesis `hΦη` of
`Stacks.Algebraization.isRightAdjoint_ι_of_completionFunctor`, the one the two-object
counterexample of `DerivedCompletion.lean` shows cannot be dropped.

Again by locality of invertibility. On a member of the covering family the second-variable
naturality of [Stacks, Tag 08JB] turns the restriction of `Φ η_E` into the image, under the
derived internal Hom out of the restricted `K`, of the restricted `η_E`; the restricted `K` is
the Čech complex of the slice up to isomorphism, so that functor is the Čech completion functor
up to isomorphism; and the Čech completion functor carries the Čech completion map to an
isomorphism with no hypothesis at all, by
`AlgebraicGeometry.RingedSite.isIso_completionFunctor_map_completionUnit_app`. -/
theorem isIso_completionFunctorOfComplex_map_completionUnitOfComplex_app
    (ha : IsGlobalExtendedCech X I K a)
    (hI : PresheafOfModules.IsFiniteType X.J I.toSheafOfModules.val)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso ((completionFunctorOfComplex X K).map ((completionUnitOfComplex X a).app E)) := by
  refine isIso_of_forall_generators X I _ hI fun U s g hg => ?_
  obtain ⟨uu, w, -⟩ := exists_eq_Q_map_cechAugmentation X U I ha g hg
  obtain ⟨A, B, α, β, p, q, hαβ⟩ :=
    exists_eq_derivedSheafHom_map_cechAugmentation_app_of_isGlobalExtendedCech X I ha U g hg E
  have hΦη := isIso_completionFunctor_map_completionUnit_app (X.over U) g
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj E)
  have hcech := @IsIso.of_isIso_comp_left _ _ _ _ _
    ((completionFunctor (X.over U) g).map
      ((derivedStructureSheafHomNatIso (X.over U)).inv.app _))
    ((completionFunctor (X.over U) g).map
      (((derivedSheafHomBifunctor (X.over U)).map
        (DerivedCategory.Q.map (cechAugmentation (X.over U) g)).op).app _)) _
    (Eq.mpr (congrArg (fun m => IsIso m) ((completionFunctor (X.over U) g).map_comp _ _).symm) hΦη)
  have h2 := Stacks.Algebraization.isIso_map_of_isIso_map_middle (completionFunctor (X.over U) g)
    α β (Stacks.Algebraization.isIso_map_of_isIso_map_middle (completionFunctor (X.over U) g)
      p q hcech)
  have hmid : IsIso (((derivedSheafHomBifunctor (X.over U)).obj
      (op ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)))).map
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        ((completionUnitOfComplex X a).app E))) :=
    (NatIso.isIso_map_iff ((derivedSheafHomBifunctor (X.over U)).mapIso uu.op) _).1
      (Eq.mpr (congrArg (fun m => IsIso ((completionFunctor (X.over U) g).map m)) hαβ) h2)
  exact Eq.mpr (congrArg (fun m => IsIso m)
      (((Iso.eq_comp_inv _).2 ((derivedHomRestriction X U).natural_right
        (K := DerivedCategory.Q.obj K) (L := E)
        (L' := (completionFunctorOfComplex X K).obj E)
        ((completionUnitOfComplex X a).app E))).trans (Category.assoc _ _ _)))
    (IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' hmid (Iso.isIso_inv _)))

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **[Stacks, Tag 099F] for a finite-type sheaf of ideals, from the map `K ⟶ 𝒪` of
[Stacks, Tag 099E].** If `a : K ⟶ 𝒪` has the property that tag asserts — on every object `U`
carrying finitely many sections generating `ℐ|_U` its restriction is the extended alternating
Čech complex of those sections, compatibly with the maps to `𝒪_U` — and `ℐ` is of finite type,
then the inclusion `D_comp(𝒪, ℐ) ⥤ D(𝒪)` has a left adjoint, namely
`E ↦ R𝑆heafHom_𝒪(K, E)`.

This is the globalization step of the source's proof, and it is all of that proof after
[Stacks, Tag 099E]: the three clauses of
`Stacks.Algebraization.isRightAdjoint_ι_of_completionFunctor` are the three theorems above.
What the source does before this point is build `K`, which for an ideal sheaf generated by
finitely many global sections is
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech_idealOfGlobalSections` of
`GlobalExtendedCech.lean`.

No `@[stacks 099F]` attribute is attached here: this statement takes `a` as data. The tag is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`,
which feeds this statement the map of
[Stacks, Tag 099E]. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_isGlobalExtendedCech
    (ha : IsGlobalExtendedCech X I K a)
    (hI : PresheafOfModules.IsFiniteType X.J I.toSheafOfModules.val) :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint :=
  Stacks.Algebraization.isRightAdjoint_ι_of_completionFunctor (completionUnitOfComplex X a)
    (fun E => isDerivedComplete_completionFunctorOfComplex X I ha hI E)
    (fun Z hZ => isIso_completionUnitOfComplex_app_of_isDerivedComplete X I ha hI Z hZ)
    (fun E => isIso_completionFunctorOfComplex_map_completionUnitOfComplex_app X I ha hI E)

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **[Stacks, Tag 099F] at the tag's own hypothesis, from [Stacks, Tag 099E].** The same
statement with Mathlib's categorical finite-type condition, which is the tag's, in place of the
sectionwise one; the two are compared by
`Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType`. The existence of `K` is
quantified away, so the hypothesis is exactly the conclusion of [Stacks, Tag 099E] for `ℐ`. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_exists_isGlobalExtendedCech
    [I.toSheafOfModules.IsFiniteType]
    (ha : ∃ (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (a : K ⟶ structureSheafComplex X), IsGlobalExtendedCech X I K a) :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_isGlobalExtendedCech X I ha.choose_spec.choose_spec
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType I.toSheafOfModules
      inferInstance)

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) CommRingCat.{u}] in
/-- **The reduction recovers [Stacks, Tag 099B]**, and so is not vacuous: fed the witness which
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech_idealOfGlobalSections` of
`GlobalExtendedCech.lean` supplies for an ideal sheaf generated by finitely many global
sections, it returns the left adjoint on `D(𝒪)` which `CompletionIdempotent.lean` proves
directly. No `@[stacks]` attribute: the statement is
`isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections` of `CompletionIdempotent.lean`,
which carries [Stacks, Tag 099B], reached by a different route and recorded here as the check
that the hypothesis of the reduction is inhabited at the case the library already has. -/
theorem isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections_of_isGlobalExtendedCech
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
    {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    (ObjectProperty.ι
      (IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f))).IsRightAdjoint :=
  have : (idealOfGlobalSections X f).toSheafOfModules.IsFiniteType :=
    isFiniteType_idealOfGlobalSections X f
  isRightAdjoint_ι_isDerivedComplete_of_exists_isGlobalExtendedCech X _
    (exists_isGlobalExtendedCech_idealOfGlobalSections X f)

end Reflector

section LocallyNilpotent

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : SheafOfModules.Submodule (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **A nilpotent section of `𝒪` over `U` satisfies the Milnor condition on every object**: if
`f` is nilpotent then multiplication by it is a nilpotent endomorphism of the restriction of any
`E` to the slice at `U`, so `T(E|_U, f) = 0`. -/
theorem isDerivedCompleteAtSection_of_isNilpotent (U : X.C)
    {f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)} (hf : IsNilpotent f) :
    IsDerivedCompleteAtSection X E U f := by
  obtain ⟨n, hn⟩ := Stacks.SheafOfModules.isNilpotent_terminalSectionToEnd
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) (Over.mk (𝟙 U)) Over.mkIdTerminal hf
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  rw [smul_pow, one_pow, overTerminalRingHom_apply, hn, zero_smul]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Every object of `D(𝒪)` is derived complete along a sheaf of ideals whose local sections
become nilpotent on a covering.** The Milnor condition at a section is local on the site, by the
sheaf condition of [Stacks, Tag 0998]
(`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`), and it holds at a
nilpotent section by `isDerivedCompleteAtSection_of_isNilpotent`. -/
theorem isDerivedComplete_of_isNilpotent_of_sieve
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) →
      ∃ S : Sieve U, S ∈ X.J U ∧ ∀ {V : X.C} (b : V ⟶ U), S.arrows b →
        IsNilpotent (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map b.op f)) :
    IsDerivedComplete.{u, u, u, u} X I E :=
  (isDerivedComplete_iff_forall_isDerivedCompleteAtSection X E I).2 fun U f hf =>
    let ⟨S, hS, hnil⟩ := hI U f hf
    IsDerivedCompleteAtSection.of_sieve X E f S hS fun b hb =>
      isDerivedCompleteAtSection_of_isNilpotent X E _ (hnil b hb)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The conclusion of [Stacks, Tag 099F] for a sheaf of ideals of finite type whose local
sections become nilpotent on a covering.** Every object of `D(𝒪)` is then derived complete
along `ℐ`, so the identity functor with the identity natural transformation is a completion
functor and the inclusion of the derived-complete objects has a left adjoint — the identity.

The hypothesis is the local form of the one in `NilpotentIdeal.lean`, which asks that the local
sections of `ℐ` be nilpotent outright. It is strictly weaker: the order of nilpotence may vary
from one member of the covering to another, and a section nilpotent on each member of a covering
need not be nilpotent. The Milnor condition being local is what closes that gap, and it is the
sheaf condition of [Stacks, Tag 0998]. This is a special case of
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`,
which carries the tag, but it identifies the left adjoint
as the identity. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_isNilpotent_of_sieve
    [I.toSheafOfModules.IsFiniteType]
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) →
      ∃ S : Sieve U, S ∈ X.J U ∧ ∀ {V : X.C} (b : V ⟶ U), S.arrows b →
        IsNilpotent (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map b.op f)) :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_completionFunctor X I
    (𝟙 (𝟭 (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))))
    (fun L => isDerivedComplete_of_isNilpotent_of_sieve X I L hI)
    (fun L _ => by simpa using (inferInstance : IsIso (𝟙 L)))
    (fun _ => rfl)

end LocallyNilpotent

end AlgebraicGeometry.RingedSite

end
