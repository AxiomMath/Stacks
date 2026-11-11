module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine vanishing for an unbounded complex: the reduction, and the bounded below case

Let `X` be a scheme over a commutative ring `A` and let `K` be a cochain complex of
`𝒪_X`-modules. There is a canonical comparison
`AlgebraicGeometry.globalSectionsComplexComparison`
$$ Q(\Gamma(X, K^\bullet)) \longrightarrow R\Gamma(X, Q(K^\bullet)) $$
in `D(A)` from the complex of `A`-linear global sections to unbounded derived global sections,
and the remaining content of the affine derived Spec–Γ equivalence (Stacks 06Z0) is that this
comparison is invertible for every complex of the form `K = M̃^•`, the degreewise sheafification
of a complex of `A`-modules. That is affine vanishing for an *unbounded* complex, Stacks 08D4
with `N = 1`.

Two things are proved here.

**The reduction.** The comparison is invertible at `K` *exactly* when termwise global sections
carries one K-injective resolution of `K` to a quasi-isomorphism, and this condition does not
depend on the resolution chosen. So the statement becomes an elementary assertion about a single
map of cochain complexes: for a quasi-isomorphism `s : K ⟶ I` with `I` K-injective, `Γ(X, s)`
must again be a quasi-isomorphism. The mechanism is general and is proved for an arbitrary right
derived functor along the quasi-isomorphisms: the structure map of such a functor is invertible
at a K-injective complex (Stacks 070K), so the naturality square at `s` identifies invertibility
of the structure map at `K` with invertibility of the image of `s`.

**The bounded below case.** If `K` is bounded below and each `K^n` is right acyclic for
`Γ(X, -)`, then the comparison *is* invertible. This is Leray's acyclicity lemma: by the
reduction it suffices to see that `Γ(X, -)` inverts a quasi-isomorphism from `K` into a bounded
below complex of injective `𝒪_X`-modules — which is K-injective (Mathlib's
`CochainComplex.isKInjective_of_injective`) — and the class of `Γ(X, -)`-acyclic objects
satisfies the hypotheses of Stacks 05T8, injective objects being acyclic and the acyclic objects
being closed under the relevant extensions by Stacks 015D. This is the bounded input of the
`E = R\lim \tau_{\geq -n}E` argument.

Also recorded is Stacks 08U1 for `RΓ(X, -)`: derived global sections carries the derived limit of
an `ℕᵒᵖ`-tower in `D(𝒪_X)` to a derived limit in `D(A)`. That is the other named input of the
unbounded argument.

## Main results

* `Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff` — the criterion for an
  arbitrary right derived functor along the quasi-isomorphisms.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_iff` — the comparison
  `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible iff `Γ(X, -)` carries a K-injective resolution of `K`
  to a quasi-isomorphism.
* `AlgebraicGeometry.quasiIso_mapHomologicalComplex_globalSectionsOver_iff` — that condition is
  independent of the K-injective resolution.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic` — the
  bounded below case.
* `AlgebraicGeometry.isDerivedLimit_map_derivedGlobalSectionsOver` — Stacks 08U1 for
  `RΓ(X, -)`.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_iff` and
  `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` — the
  reduction of unbounded affine vanishing, and of the derived Spec–Γ unit, to that elementary
  condition on the complexes `M̃^•`.

## Implementation notes

The general criterion is stated for abstract abelian categories and instantiated afterwards, for
the reason recorded in
`StacksFrontier/AlgebraicGeometry/DerivedTildeEquivalence/DerivedAdjunction.lean`: `X.Modules` and
`SheafOfModules X.ringCatSheaf` are definitionally equal but carry separately declared
`Preadditive` instances that instance search does not cross.

The two derived categories are taken at free `[HasDerivedCategory.{w₁} X.Modules]` and
`[HasDerivedCategory.{w₂} (ModuleCat.{u} A)]` binders, with independent morphism universes; see
the implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`. The
default a consumer gets, from `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and
`ModuleCat.hasDerivedCategory`, is the locally small model.

Limit preservation by `AlgebraicGeometry.globalSectionsOver` is assembled from its two factors by
an explicit application of `CategoryTheory.Limits.comp_preservesFiniteLimits` rather than by
instance search. Search does find each factor separately — the sheaf-sections functor by
`SheafOfModules.Finite.evaluationPreservesFiniteLimits` and restriction of scalars from its left
adjoint — but it does not find the one for restriction of scalars in the position where the
composite puts it, so the two factors are supplied by name.

No `@[stacks 08D4]` attribute appears *below*, and none is needed: that tag's covering set is
complete elsewhere, at `AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι`
and `AlgebraicGeometry.isGE_rightDerivedFunctor_obj` in
`StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/DerivedBounds.lean`, and at
`AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero` and
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero` in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedAmplitude/UpperBounds.lean`. What this file proves
is a *reduction* of the affine case to an elementary condition on the complexes `M̃^•`, which is
not one of the tag's clauses. Nor is `@[stacks 015E]` placed on the bounded
below case: Leray's acyclicity lemma is already carried by
`CategoryTheory.Functor.isIso_ι_app_of_computesRightDerived_single_of_isRightDerivedValueAt`,
whose enough injectives case is
`CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`, and the statement below
is an instance of the latter for the *unbounded* derived global sections of a scheme, which the
tag does not mention. Likewise `@[stacks 08U1]` stays on
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated Opposite

universe w₁ w₂ u

namespace Stacks.SmallDerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {H : Type*} [Category* H]

/-- A morphism of cochain complexes becomes invertible in the derived category, through the
homotopy category, exactly when it is a quasi-isomorphism. -/
private theorem isIso_Qh_quotient_map_iff {K L : CochainComplex A ℤ} (s : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) ↔
      QuasiIso s :=
  (DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).trans
      (HomologicalComplex.mem_quasiIso_iff _))

/-- **The structure map of an unbounded right derived functor, tested on a K-injective
resolution.** Let `RF` be a right derived functor of `F : K(A) ⥤ H` along the
quasi-isomorphisms, in an abelian category where every complex admits a quasi-isomorphism into a
K-injective complex, and let `s : K ⟶ I` be a quasi-isomorphism with `I` K-injective. Then the
structure map `F(K) ⟶ RF(K)` is invertible precisely when `F` inverts `s`.

Indeed the structure map is invertible at `I` (Stacks 070K) and `s` becomes invertible in `D(A)`,
so the two vertical maps of the naturality square of the structure map at `s` are invertible and
the two horizontal ones are invertible together. -/
theorem isIso_rightDerivedUnit_app_quotient_iff
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory A ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {K I : CochainComplex A ℤ} (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ↔
      IsIso (F.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) := by
  have hαI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      F hA).2 DerivedCategory.Qh RF α I hI
  have hQh : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) := by
    rwa [isIso_Qh_quotient_map_iff]
  have hnat := α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  rw [← isIso_comp_right_iff (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
      (RF.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s))),
    ← hnat, isIso_comp_right_iff]

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### Exactness and limit preservation of `A`-linear global sections -/

/-- Restriction of scalars along the ring map underlying a scheme over `A` preserves finite
limits: it is a right adjoint, its left adjoint being extension of scalars. -/
theorem preservesFiniteLimits_restrictScalars_appTop :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Scheme.Hom.appTop f))) := by
  infer_instance

/-- Restriction of scalars along the ring map underlying a scheme over `A` preserves countable
products. -/
theorem preservesLimitsOfShape_restrictScalars_appTop :
    PreservesLimitsOfShape (Discrete ℕ) (ModuleCat.restrictScalars.{u} (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Scheme.Hom.appTop f))) := by
  infer_instance

variable [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- `A`-linear global sections is left exact: sections of a sheaf of modules over a fixed open
are a limit, and restriction of scalars is a right adjoint. -/
instance globalSectionsOver_preservesFiniteLimits :
    PreservesFiniteLimits (globalSectionsOver f) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _)
    (preservesFiniteLimits_restrictScalars_appTop f)

/-- `A`-linear global sections preserves countable products. This is the hypothesis under which
a right derived functor carries derived limits of `ℕᵒᵖ`-towers to derived limits, Stacks 08U1. -/
instance globalSectionsOver_preservesLimitsOfShape_discrete_nat :
    PreservesLimitsOfShape (Discrete ℕ) (globalSectionsOver f) :=
  @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.evaluationPreservesLimitsOfShape _ _ _)
    (preservesLimitsOfShape_restrictScalars_appTop f)

/-- `A`-linear global sections has a right derived functor on the bounded below derived
category: every functor out of `K⁺(𝒪_X)` does, `𝒪_X`-modules having enough injectives. This is
what makes `CategoryTheory.Functor.rightAcyclic` available for `Γ(X, -)`. -/
instance globalSectionsOver_hasPointwiseRightDerivedFunctorPlus :
    ((globalSectionsOver f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso X.Modules) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).hasPointwiseRightDerivedFunctor

/-- An injective `𝒪_X`-module is right acyclic for `A`-linear global sections: the complex
`J[0]` has injective terms, and the structure map of a right derived functor on `K⁺` is
invertible at such a complex. -/
theorem rightAcyclic_globalSectionsOver_of_injective (J : X.Modules) [Injective J] :
    (globalSectionsOver f).rightAcyclic J := by
  have hinj : ∀ n : ℤ,
      Injective (((HomotopyCategory.Plus.singleFunctor X.Modules 0).obj J).obj.as.X n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Injective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) J).symm ‹_›
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 J n hn).injective
  dsimp only [Functor.rightAcyclic]
  infer_instance

/-- Every `𝒪_X`-module is a subobject of one that is right acyclic for `A`-linear global
sections: embed it into an injective. -/
theorem exists_mono_rightAcyclic_globalSectionsOver (Y : X.Modules) :
    ∃ (Z : X.Modules) (_ : (globalSectionsOver f).rightAcyclic Z) (j : Y ⟶ Z), Mono j :=
  ⟨Injective.under Y, rightAcyclic_globalSectionsOver_of_injective f _, Injective.ι Y,
    inferInstance⟩

/-- In a short exact sequence of `𝒪_X`-modules whose first two terms are right acyclic for
`A`-linear global sections, the third is right acyclic too and global sections carries the
sequence to a short exact sequence. This is Stacks 015D. -/
theorem rightAcyclic_X₃_and_shortExact_map_globalSectionsOver
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : (globalSectionsOver f).rightAcyclic S.X₁)
    (h₂ : (globalSectionsOver f).rightAcyclic S.X₂) :
    (globalSectionsOver f).rightAcyclic S.X₃ ∧
      (S.map (globalSectionsOver f)).ShortExact :=
  (Functor.rightAcyclic_and_shortExact_map_of_shortExact (globalSectionsOver f) S hS).2.1 h₁ h₂

/-! ### The comparison tested on a K-injective resolution -/

/-- The structure map of unbounded derived global sections at a complex `K` of `𝒪_X`-modules is
invertible precisely when termwise global sections carries a K-injective resolution of `K` to a
quasi-isomorphism. -/
theorem isIso_derivedGlobalSectionsOverUnit_app_quotient_iff
    {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s) :
    IsIso ((derivedGlobalSectionsOverUnit f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ↔
      QuasiIso (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  rw [Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff
    (Scheme.Modules.exists_quasiIso_isKInjective X) _ _ _ s hI hs]
  exact Stacks.SmallDerivedCategory.isIso_Qh_quotient_map_iff _

/-- **The comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` tested on a K-injective resolution.** For a
scheme `X` over `A` and a cochain complex `K` of `𝒪_X`-modules, the canonical comparison from the
complex of `A`-linear global sections of `K` to the unbounded derived global sections of the
object it represents is invertible precisely when termwise global sections carries a
quasi-isomorphism `s : K ⟶ I` into a K-injective complex to a quasi-isomorphism.

The remaining three factors of `AlgebraicGeometry.globalSectionsComplexComparison` are
isomorphisms outright, so the content is
`AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_quotient_iff`. -/
theorem isIso_globalSectionsComplexComparison_iff
    {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s) :
    IsIso (globalSectionsComplexComparison f K) ↔
      QuasiIso (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  rw [← isIso_derivedGlobalSectionsOverUnit_app_quotient_iff f s hI hs]
  dsimp only [globalSectionsComplexComparison]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Termwise global sections inverts one K-injective resolution iff it inverts every one.**
Both conditions say that the comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible. -/
theorem quasiIso_mapHomologicalComplex_globalSectionsOver_iff
    {K I J : CochainComplex X.Modules ℤ} (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s)
    (t : K ⟶ J) (hJ : J.IsKInjective) (ht : QuasiIso t) :
    QuasiIso (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ↔
      QuasiIso (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  rw [← isIso_globalSectionsComplexComparison_iff f s hI hs,
    isIso_globalSectionsComplexComparison_iff f t hJ ht]

/-- The comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible at a K-injective complex: a
K-injective complex computes its own derived global sections. -/
theorem isIso_globalSectionsComplexComparison_of_isKInjective
    {K : CochainComplex X.Modules ℤ} (hK : K.IsKInjective) :
    IsIso (globalSectionsComplexComparison f K) := by
  rw [isIso_globalSectionsComplexComparison_iff f (𝟙 K) hK inferInstance,
    CategoryTheory.Functor.map_id]
  infer_instance

/-- **Invariance of the comparison along a quasi-isomorphism on which global sections is
already known to be a quasi-isomorphism.** If `u : K ⟶ L` is a quasi-isomorphism of complexes of
`𝒪_X`-modules and `Γ(X, u)` is again a quasi-isomorphism, then the comparison
`Q(Γ(X, -)) ⟶ RΓ(X, Q(-))` is invertible at `K` precisely when it is invertible at `L`. -/
theorem isIso_globalSectionsComplexComparison_iff_of_quasiIso
    {K L : CochainComplex X.Modules ℤ} (u : K ⟶ L) (hu : QuasiIso u)
    (hΓu : QuasiIso (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map u)) :
    IsIso (globalSectionsComplexComparison f K) ↔
      IsIso (globalSectionsComplexComparison f L) := by
  obtain ⟨I, t, hI, ht⟩ := Scheme.Modules.exists_quasiIso_isKInjective X L
  have hΓu' : IsIso (DerivedCategory.Q.map
      (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map u)) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  rw [isIso_globalSectionsComplexComparison_iff f (u ≫ t) hI inferInstance,
    isIso_globalSectionsComplexComparison_iff f t hI ht,
    ← DerivedCategory.isIso_Q_map_iff_quasiIso, ← DerivedCategory.isIso_Q_map_iff_quasiIso,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, isIso_comp_left_iff]

/-! ### The bounded below case -/

/-- **Leray's acyclicity lemma for unbounded derived global sections.** Let `X` be a scheme over
`A` and let `K` be a *bounded below* cochain complex of `𝒪_X`-modules each of whose terms is
right acyclic for `Γ(X, -)`. Then the comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible: the
complex of global sections of `K` already computes unbounded derived global sections.

This is the bounded input of the `E = R\lim \tau_{\geq -n}E` argument for an unbounded complex
(Stacks 08D4). On an affine scheme the hypothesis holds for a complex of quasi-coherent modules,
by Serre vanishing (Stacks 01XB).

The proof resolves `K` by a bounded below complex `L` of injective `𝒪_X`-modules; such an `L` is
K-injective, so by `isIso_globalSectionsComplexComparison_iff` it suffices that `Γ(X, -)` carry
the resolution `K ⟶ L` to a quasi-isomorphism, and that is Stacks 05T8 applied to the class of
`Γ(X, -)`-acyclic objects, whose two hypotheses are
`exists_mono_rightAcyclic_globalSectionsOver` and
`rightAcyclic_X₃_and_shortExact_map_globalSectionsOver`. -/
@[ega "0 11.5.4" "special case"]
theorem isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic
    (K : CochainComplex X.Modules ℤ) (hK : CochainComplex.plus X.Modules K)
    (hac : ∀ n : ℤ, (globalSectionsOver f).rightAcyclic (K.X n)) :
    IsIso (globalSectionsComplexComparison f K) := by
  obtain ⟨n, hn⟩ := hK
  obtain ⟨L, s, hs, hLinj, hLn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have hLK : L.IsKInjective := CochainComplex.isKInjective_of_injective L n
  rw [isIso_globalSectionsComplexComparison_iff f s hLK hs]
  exact Functor.RightAcyclicCriterion.map_quasiIso (globalSectionsOver f)
    (globalSectionsOver f).rightAcyclic (exists_mono_rightAcyclic_globalSectionsOver f)
    (rightAcyclic_X₃_and_shortExact_map_globalSectionsOver f)
    s ⟨n, hn⟩ ⟨n, hLn⟩ hac
    (fun m => have := hLinj m; rightAcyclic_globalSectionsOver_of_injective f (L.X m))

/-! ### Derived global sections and derived limits -/

/-- **Stacks 08U1 for unbounded derived global sections.** If an object `K` of `D(𝒪_X)` is the
derived limit of an `ℕᵒᵖ`-tower `Y`, then `RΓ(X, K)` is the derived limit of the tower
`Y ⋙ RΓ(X, -)` in `D(A)`.

This holds because `𝒪_X`-modules form a Grothendieck abelian category, `A`-modules have exact
countable products, and `Γ(X, -)` preserves countable products. It is the interchange of `RΓ`
with `R\lim` used in the proof of Stacks 08D4. -/
theorem isDerivedLimit_map_derivedGlobalSectionsOver
    (Y : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ ↦ Y.obj ⟨n⟩]
    (K : DerivedCategory X.Modules) (hK : IsDerivedLimit Y K) :
    ∃ _ : HasProduct fun n : ℕ ↦ (Y ⋙ derivedGlobalSectionsOver f).obj ⟨n⟩,
      IsDerivedLimit (Y ⋙ derivedGlobalSectionsOver f)
        ((derivedGlobalSectionsOver f).obj K) := by
  obtain ⟨p, δ, hT⟩ := hK
  obtain ⟨h, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (globalSectionsOver f) (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    Y K p ⟨δ, hT⟩
  exact ⟨h, ⟨_, δ', hT'⟩⟩

/-! ### The affine case -/

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- **Unbounded affine vanishing, reduced to a statement about complexes.** The hypothesis of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app` — invertibility of the
comparison `Q(Γ(Spec R, M̃^•)) ⟶ RΓ(Spec R, Q(M̃^•))` for every cochain complex `M^•` of
`R`-modules, which is the affine case of Stacks 08D4 — holds if and only if for every `M^•` and
every quasi-isomorphism `s` from `M̃^•` into a K-injective complex of `𝒪_{Spec R}`-modules, the
map `Γ(Spec R, s)` of complexes of `R`-modules is again a quasi-isomorphism. -/
theorem isIso_globalSectionsComplexComparison_tilde_iff :
    (∀ M : CochainComplex (ModuleCat.{u} R) ℤ,
        IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) ↔
      ∀ (M : CochainComplex (ModuleCat.{u} R) ℤ) (I : CochainComplex (Spec R).Modules ℤ)
        (s : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I),
        I.IsKInjective → QuasiIso s →
          QuasiIso (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map s) := by
  refine ⟨fun h M I s hI hs ↦ (isIso_globalSectionsComplexComparison_iff (𝟙 (Spec R)) s hI hs).1
    (h M), fun h M ↦ ?_⟩
  obtain ⟨I, s, hI, hs⟩ := Scheme.Modules.exists_quasiIso_isKInjective (Spec R)
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  exact (isIso_globalSectionsComplexComparison_iff (𝟙 (Spec R)) s hI hs).2 (h M I s hI hs)

/-- **The derived Spec–Γ unit is invertible as soon as global sections inverts the K-injective
resolutions of the complexes `M̃^•`.** Combining
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_iff` with
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app`, this is the form in which
unbounded affine vanishing feeds the derived Spec–Γ equivalence of Stacks 06Z0. -/
theorem isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso
    (h : ∀ (M : CochainComplex (ModuleCat.{u} R) ℤ) (I : CochainComplex (Spec R).Modules ℤ)
      (s : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ I),
      I.IsKInjective → QuasiIso s →
        QuasiIso (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s))
    (M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M) :=
  isIso_derivedTildeGlobalSectionsAdjunction_unit_app R
    ((isIso_globalSectionsComplexComparison_tilde_iff R).2 h) M

end AlgebraicGeometry

end
