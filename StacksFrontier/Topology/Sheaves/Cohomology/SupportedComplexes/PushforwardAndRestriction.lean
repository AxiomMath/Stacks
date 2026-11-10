module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact
-- Not a `public import`: this module needs `exactFunctorHomologyIso` and
-- `exactFunctorDerivedHomologyIso` only inside private proofs, and re-exporting
-- `ClosedSubsetPushforward` would make `AlgebraicGeometry.CohomologySupportedOn` visible
-- alongside this module's own `CohomologySupportedOn` in every importer.
import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Pushforward and restriction for complexes with closed support

Let `U` be an open subspace of a ringed space and let `T` be a closed subset contained in
`U`. An object of the derived category whose cohomology sheaves are supported on `T` is
canonically isomorphic to the derived pushforward of its restriction to `U`. Likewise,
extension by zero and derived pushforward agree on objects over `U` whose cohomology is
supported on `T`.

## Main definitions

* `CohomologySupportedOn` says that every cohomology sheaf of a derived object has vanishing
  stalks away from a specified subset.
* `derivedPushforwardRestrictionUnit` is the canonical map from an object to the derived
  pushforward of its restriction.
* `extensionByZeroToDerivedPushforward` is the canonical comparison from extension by zero to
  derived pushforward.
* `derivedOpenPushforward` is the derived pushforward `Rj_*` along the open subspace, the total
  right derived functor of `j_*`, with comparison map `derivedOpenPushforwardUnit`.

## Main results

* `isIso_derivedOpenPushforward_restrictionUnit_app_of_supported` is part (1) of Tag 08DF:
  `E ⟶ Rj_*(E|_U)` is an isomorphism for `E` supported on `T`.
* `isIso_extensionByZeroToDerivedOpenPushforward_app_of_supported` is part (2) of Tag 08DF:
  `j_! F ⟶ Rj_* F` is an isomorphism for `F` supported on `T`.
* `isIso_derivedPushforwardRestriction_unit_of_supported` and
  `isIso_extensionByZeroToDerivedPushforward_app_of_supported` are the same two assertions for
  an arbitrary right derived functor of `j_*`.
* `isZero_Q_restrictPush_of_supported` is the vanishing of `j_*(K|_A)` on an open `A` disjoint
  from the support, at a K-injective representative of `K`.
* `isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar`: a morphism of the derived category
  whose restrictions to two opens covering the space are invertible is invertible.

## Implementation notes

Additivity and exactness of `j^*`, `j_!` and `j_*` are **not** hypotheses of anything below.
They are unconditional global instances, proved once in
`StacksFrontier/Topology/Sheaves/OpenImmersion/ModuleExtensionByZeroExact.lean` —
`ExtensionByZeroModules.jStar_additive`, `jStar_preservesFiniteLimits`,
`jStar_preservesFiniteColimits`, `jShriek_additive`, `jShriek_preservesFiniteLimits`,
`jShriek_preservesColimitsOfSize` and `jPush_additive` — and are synthesized at each use here.
`j_*` is additive and left exact only, and nothing below asks more of it than additivity.

The two derived categories are **instance arguments**: every statement below takes
`[HasDerivedCategory (SheafOfModules O)]` and, where the open subspace appears,
`[HasDerivedCategory (SheafOfModules (resRing U O))]`, rather than fixing a model with a
file-level `attribute [local instance] HasDerivedCategory.standard`. Nothing in the argument
needs the standard model, and no input to it mentions one. Keeping
the model free is what makes these results usable at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the only model at which the
compact-generation statements of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content; a
statement proved for the standard model says nothing about that one. The derived category of the
complement `X \ T` is a different matter — it occurs only inside the proof of part (2), as the
second half of a cover on which an isomorphism is detected, so there the standard model is
chosen locally and no binder is spent on it.

A ringed space is presented by a topological space and a sheaf of possibly noncommutative
rings; this harmlessly generalizes the source. Support is stated stalkwise, in the module-sheaf
category used by the derived functors. The two main results state parts (1) and (2),
respectively. Their natural transformations are constructed using the fully faithful
precomposition functor associated to localization. For part (1), the transformation on
the homotopy category is the unit of `j^* ⊣ j_*` followed by the right-derived comparison;
for part (2), it is the canonical `j_! ⟶ j_*` transformation of the underived adjoint
triple followed by that comparison. Thus neither map depends on an independently chosen
derived adjunction, and both are natural in the derived object.

The route to part (1) is the one the Stacks text takes, by way of the cover `X = U ∪ (X \ T)`.
Concretely the input is the *sheaf-level* Mayer--Vietoris short exact sequence of Tag 08BV,
`Stacks.Cohomology.RestrictionCover.restrictionCoverShortExact`, applied to a K-injective
resolution with injective terms; it is turned into a distinguished triangle by
`DerivedCategory.triangleOfSES`. The functorial unbounded Mayer--Vietoris triangle in the
derived category is *not* used: the triangle is needed only at a K-injective representative,
where the short exact sequence of complexes already provides it, and the two terms that must
vanish do so because an acyclic K-injective complex is null-homotopic and additive functors
preserve null-homotopy. See `isZero_Q_restrictPush_of_supported`.

## References

* [The Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [The Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace
open CategoryTheory.Pretriangulated
open AlgebraicGeometry
open ZeroObject
open ExtensionByZeroModules
open Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.PushforwardRestriction

open Stacks.Cohomology.SupportedComplexes (exactFunctorHomologyIso exactFunctorDerivedHomologyIso)

/-- The open subspace and the complement of a closed subset contained in it cover the space. -/
private lemma open_sup_compl_closed_eq_top {X : TopCat.{u}} (U : Opens X)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U) :
    U ⊔ ⟨Tᶜ, hT.isOpen_compl⟩ = ⊤ := by
  ext x
  change (x ∈ U ∨ x ∉ T) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : x ∈ T
    · exact Or.inl (hTU hx)
    · exact Or.inr hx

/-- Restriction to an open preserves K-injective complexes because extension by zero is exact. -/
private lemma isKInjective_jStar
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : Opens X) (I : CochainComplex (SheafOfModules.{u} O) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((jStar V O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (jStar V O) (jShriek V O) (jShriekAdjunction V O) I

/-- An acyclic K-injective complex is already zero in the homotopy category. -/
lemma isZero_homotopyCategory_of_acyclic_isKInjective
    {A : Type*} [Category* A] [Abelian A]
    (I : CochainComplex A ℤ) [I.IsKInjective] (hI : I.Acyclic) :
    IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) := by
  have hid : (𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) = 0 := by
    calc
      _ = (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (𝟙 I) :=
        (CategoryTheory.Functor.map_id (HomotopyCategory.quotient A (ComplexShape.up ℤ)) I).symm
      _ = 0 := (HomotopyCategory.quotient_map_eq_zero_iff (𝟙 I)).2
        (CochainComplex.IsKInjective.nonempty_homotopy_zero (𝟙 I) hI)
  exact (IsZero.iff_id_eq_zero _).2 hid

/-- Every cohomology sheaf of `E` has support contained in `T`, expressed equivalently by
vanishing of all stalks at points outside `T`. -/
noncomputable abbrev CohomologySupportedOn {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)] (T : Set X)
    (E : DerivedCategory (SheafOfModules.{u} O)) : Prop :=
  ∀ (i : ℤ) (x : X), x ∉ T →
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E).val.presheaf) x)

/-- Cohomological support is invariant under isomorphism in the derived category. -/
lemma cohomologySupportedOn_of_iso
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)]
    (T : Set X) {E F : DerivedCategory (SheafOfModules.{u} O)}
    (e : E ≅ F) (hE : CohomologySupportedOn O T E) :
    CohomologySupportedOn O T F := by
  intro i x hx
  exact (hE i x hx).of_iso
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb O).mapIso ((DerivedCategory.homologyFunctor _ i).mapIso e))).symm)

/-- Extension by zero preserves support inside a closed subset of the open. -/
lemma isZero_stalk_jShriek_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X)
    (M : SheafOfModules.{u} (resRing U O))
    (hM : ∀ (x : Usp U), x.1 ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := Usp U) M.val.presheaf x))
    (x : X) (hx : x ∉ T) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((jShriek U O).obj M).val.presheaf) x) := by
  by_cases hxU : x ∈ U
  · let y : Usp U := ⟨x, hxU⟩
    let := isIso_jShriekAdjunction_unit U O
    have hz : IsZero (TopCat.Presheaf.stalk (X := Usp U)
        (((jStar U O).obj ((jShriek U O).obj M)).val.presheaf) y) :=
      (hM y hx).of_iso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
          ((toAb (resRing U O)).mapIso
            (asIso ((jShriekAdjunction U O).unit.app M)))).symm)
    exact hz.of_iso
      (TopCat.Presheaf.stalkRestrictIso U
        (((jShriek U O).obj M).val.presheaf) y).symm
  · exact isZero_stalk_jShriek U O M x hxU

/-- A module sheaf is zero when all its underlying additive stalks are zero. -/
lemma isZero_sheafOfModules_of_stalk_isZero
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (M : SheafOfModules.{u} O)
    (hM : ∀ x : X, IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf x)) :
    IsZero M := by
  let f : M ⟶ (0 : SheafOfModules.{u} O) := 0
  have hf : IsIso f := isIso_of_stalk_isIso O f fun x => by
    let : HasZeroMorphisms (TopCat.Presheaf AddCommGrpCat.{u} X) :=
      inferInstanceAs (HasZeroMorphisms ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    have hpres : (toAb O).PreservesZeroMorphisms := by
      change (SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj).PreservesZeroMorphisms
      infer_instance
    let := hpres
    apply (hM x).isIso
    exact Functor.map_isZero _ (Functor.map_isZero (toAb O) (isZero_zero _))
  exact (isZero_zero _).of_iso (asIso f)

/-- Restriction to an open is zero when all stalks on that open vanish. -/
lemma isZero_jStar_obj_of_stalk_isZero
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : Opens X) (M : SheafOfModules.{u} O)
    (hM : ∀ x : X, x ∈ V →
      IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf x)) :
    IsZero ((jStar V O).obj M) := by
  apply isZero_sheafOfModules_of_stalk_isZero (resRing V O)
  intro x
  exact (hM x.1 x.2).of_iso
    (TopCat.Presheaf.stalkRestrictIso V M.val.presheaf x)

-- NO `exactFunctorHomologyIso` / `exactFunctorDerivedHomologyIso` HERE. The two private
-- definitions that stood here were byte-identical to
-- `Stacks.Cohomology.SupportedComplexes.exactFunctorHomologyIso` and
-- `...exactFunctorDerivedHomologyIso`
-- (`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/ClosedSubsetPushforward.lean`
-- :115, :130), which this module now imports and whose names the uses below resolve to.

/-- Exact extension by zero preserves cohomological support inside a subset of the open. -/
lemma cohomologySupportedOn_jShriek
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O)
      ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    CohomologySupportedOn O T ((jShriek U O).mapDerivedCategory.obj F) := by
  intro i x hx
  have hz := isZero_stalk_jShriek_of_supported O U T
    ((DerivedCategory.homologyFunctor _ i).obj F)
    (fun y hy => hF i y hy) x hx
  exact hz.of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb O).mapIso ((exactFunctorDerivedHomologyIso (jShriek U O) i).app F)))

/-- Restriction of extension by zero recovers a complex on the open. -/
private noncomputable def jStar_jShriek_complexIso
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ) :
    I ≅ ((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((jShriek U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  letI := isIso_jShriekAdjunction_unit U O
  exact ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).symm.app I) ≪≫
    (NatIso.mapHomologicalComplex (asIso (jShriekAdjunction U O).unit)
      (ComplexShape.up ℤ)).app I ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (jShriek U O ⋙ jStar U O)) (ComplexShape.up ℤ)).symm.app I

/-- An object of a derived category is zero if all of its cohomology objects are zero. -/
lemma isZero_derived_of_homology_isZero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (E : DerivedCategory C)
    (hE : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj E)) :
    IsZero E := by
  have hzero : IsIso (0 : E ⟶ E) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    exact (hE n).isIso (hE n) _
  exact (IsZero.iff_id_eq_zero E).2 (isIsoZeroSelfEquiv E hzero)

/-- A complex supported on a closed set vanishes on its open complement. -/
lemma isZero_derived_restrict_compl_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (T : Set X) (hT : IsClosed T)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing ⟨Tᶜ, hT.isOpen_compl⟩ O))]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O T E) :
    IsZero ((jStar ⟨Tᶜ, hT.isOpen_compl⟩ O).mapDerivedCategory.obj E) := by
  let V : Opens X := ⟨Tᶜ, hT.isOpen_compl⟩
  apply isZero_derived_of_homology_isZero
  intro i
  have hzero : IsZero ((jStar V O).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E)) := by
    apply isZero_jStar_obj_of_stalk_isZero O V
    intro x hx
    exact hE i x hx
  exact hzero.of_iso ((exactFunctorDerivedHomologyIso (jStar V O) i).app E)

/-- On an open disjoint from the support, any complex representing the derived object is acyclic
after restriction. -/
private lemma acyclic_restrict_complex_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)]
    (V : Opens X) (T : Set X) (hVT : ∀ x : X, x ∈ V → x ∉ T)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hI : CohomologySupportedOn O T (DerivedCategory.Q.obj I)) :
    (((jStar V O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hzero : IsZero ((jStar V O).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj
        (DerivedCategory.Q.obj I))) := by
    apply isZero_jStar_obj_of_stalk_isZero O V
    intro x hx
    exact hI i x (hVT x hx)
  have hzero' : IsZero ((jStar V O).obj (I.homology i)) :=
    hzero.of_iso
      ((jStar V O).mapIso
        ((DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} O) i).app I)).symm
  exact hzero'.of_iso ((exactFunctorHomologyIso (jStar V O) i).app I)

/-- On an open disjoint from the support, the restriction of a K-injective representative
is zero already in the homotopy category. -/
private lemma isZero_homotopy_restrict_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)]
    (V : Opens X) (T : Set X) (hVT : ∀ x : X, x ∈ V → x ∉ T)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hKI : I.IsKInjective)
    (hI : CohomologySupportedOn O T (DerivedCategory.Q.obj I)) :
    IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((jStar V O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  let := hKI
  let : CochainComplex.IsKInjective
      (((jStar V O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_jStar O V I
  exact isZero_homotopyCategory_of_acyclic_isKInjective _
    (acyclic_restrict_complex_of_supported O V T hVT I hI)

/-! ### The vanishing terms of the Mayer--Vietoris sequence

On an open `A` disjoint from the support, the restriction of a K-injective representative is
null-homotopic, and `jPush A O` is additive, so `restrictPush O A` applied to that
representative is null-homotopic too, hence zero in the derived category. This is the step
that replaces any appeal to a derived base-change formula. -/

/-- On an open disjoint from the support, restriction followed by pushforward sends a
K-injective representative to zero in the derived category. -/
lemma isZero_Q_restrictPush_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)]
    (A : Opens X) (T : Set X) (hAT : ∀ x : X, x ∈ A → x ∉ T)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hKI : I.IsKInjective)
    (hI : CohomologySupportedOn O T (DerivedCategory.Q.obj I)) :
    IsZero (DerivedCategory.Q.obj
      (((restrictPush O A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have hz := isZero_homotopy_restrict_of_supported O A T hAT I hKI hI
  have hz₁ : IsZero (((jPush A O).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((jStar A O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    Functor.map_isZero _ hz
  have hz₂ : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((jPush A O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((jStar A O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    hz₁.of_iso (((jPush A O).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _).symm
  have hz₃ : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((restrictPush O A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    hz₂.of_iso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (jStar A O ⋙ jPush A O)) (ComplexShape.up ℤ)).app I).symm)
  exact (Functor.map_isZero DerivedCategory.Qh hz₃).of_iso
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).app _).symm

/-! ### The biproduct projections of the middle term -/

/-- The projection of the Mayer--Vietoris middle term onto its `U` factor. -/
private noncomputable def restrictionCoverFst
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) :
    restrictionCoverMiddle O U V ⟶ restrictPush O U where
  app _ := biprod.fst
  naturality _ _ _ := biprod.map_fst _ _

/-- The projection of the Mayer--Vietoris middle term onto its `V` factor. -/
private noncomputable def restrictionCoverSnd
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) :
    restrictionCoverMiddle O U V ⟶ restrictPush O V where
  app _ := biprod.snd
  naturality _ _ _ := biprod.map_snd _ _

/-- The inclusion of the `U` factor into the Mayer--Vietoris middle term. -/
private noncomputable def restrictionCoverInl
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) :
    restrictPush O U ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inl
  naturality _ _ _ := (biprod.inl_map _ _).symm

/-- The inclusion of the `V` factor into the Mayer--Vietoris middle term. -/
private noncomputable def restrictionCoverInr
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) :
    restrictPush O V ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inr
  naturality _ _ _ := (biprod.inr_map _ _).symm

/-- The first map of the Mayer--Vietoris sequence followed by the projection onto the `U`
factor is the unit of restriction and pushforward along `U`. -/
private lemma restrictionCoverFirst_comp_fst
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) :
    restrictionCoverFirst O U V ≫ restrictionCoverFst O U V = (jStarAdjunction U O).unit := by
  apply NatTrans.ext
  funext M
  exact biprod.lift_fst _ _

/-! ### The restriction unit is invertible on a supported K-injective representative -/

/-- **The core of Tag 08DF.** For a K-injective complex with injective terms whose cohomology
is supported on a closed `T ⊆ U`, the unit `I ⟶ j_{U,*}(I|_U)` is a quasi-isomorphism.

The Mayer--Vietoris short exact sequence of Tag 08BV for the cover `X = U ∪ (X \ T)` gives a
distinguished triangle; its third term and the `X \ T` summand of its middle term both vanish
in the derived category by `isZero_Q_restrictPush_of_supported`. -/
private lemma isIso_Q_map_restrictPush_unit_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} O)]
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hKI : I.IsKInjective)
    (hInj : ∀ n : ℤ, Injective (I.X n))
    (hI : CohomologySupportedOn O T (DerivedCategory.Q.obj I)) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (jStarAdjunction U O).unit
        (ComplexShape.up ℤ)).app I)) := by
  let c := ComplexShape.up ℤ
  let V : Opens X := ⟨Tᶜ, hT.isOpen_compl⟩
  have hUV : U ⊔ V = ⊤ := open_sup_compl_closed_eq_top U T hT hTU
  let : ∀ n : ℤ, Injective (I.X n) := hInj
  -- the short exact sequence of complexes, from the sheaf half of 08BV
  have hSE : (restrictionCoverShortComplex O U V I).ShortExact :=
    restrictionCoverShortExact O U V hUV I
  -- the third term vanishes
  have h₃ : IsZero (DerivedCategory.Q.obj (restrictionCoverShortComplex O U V I).X₃ ) :=
    isZero_Q_restrictPush_of_supported O (U ⊓ V) T (fun _ hx => hx.2) I hKI hI
  have hf : IsIso (DerivedCategory.Q.map (restrictionCoverShortComplex O U V I).f) :=
    (Triangle.isZero₃_iff_isIso₁ _ (DerivedCategory.triangleOfSES_distinguished hSE)).mp h₃
  -- restated on the natural transformation itself, so that composing with the projection
  -- below never asks the elaborator to reduce the `X₂` projection of a semireducible
  -- definition
  have hf' : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (restrictionCoverFirst O U V) c).app I)) := hf
  -- the `V` summand of the middle term vanishes
  have hV : IsZero (DerivedCategory.Q.obj
      (((restrictPush O V).mapHomologicalComplex c).obj I)) :=
    isZero_Q_restrictPush_of_supported O V T (fun _ hx => hx) I hKI hI
  -- the projection onto the `U` summand is therefore invertible
  set Fst := (NatTrans.mapHomologicalComplex (restrictionCoverFst O U V) c).app I with hFstDef
  set Snd := (NatTrans.mapHomologicalComplex (restrictionCoverSnd O U V) c).app I with hSndDef
  set Inl := (NatTrans.mapHomologicalComplex (restrictionCoverInl O U V) c).app I with hInlDef
  set Inr := (NatTrans.mapHomologicalComplex (restrictionCoverInr O U V) c).app I with hInrDef
  have htotal : Fst ≫ Inl + Snd ≫ Inr = 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 _
    exact biprod.total
  have hinlfst : Inl ≫ Fst = 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    change biprod.inl ≫ biprod.fst = 𝟙 _
    exact biprod.inl_fst
  have hQsnd : DerivedCategory.Q.map Snd = 0 := hV.eq_of_tgt _ _
  have hFstIso : IsIso (DerivedCategory.Q.map Fst) := by
    refine ⟨DerivedCategory.Q.map Inl, ?_, ?_⟩
    · have hsum : DerivedCategory.Q.map (Fst ≫ Inl) +
          DerivedCategory.Q.map (Snd ≫ Inr) = 𝟙 _ := by
        rw [← CategoryTheory.Functor.map_add, htotal, CategoryTheory.Functor.map_id]
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hQsnd,
        Limits.zero_comp, add_zero] at hsum
      exact hsum
    · rw [← CategoryTheory.Functor.map_comp, hinlfst, CategoryTheory.Functor.map_id]
  -- the composite is the unit
  have hcomp : (NatTrans.mapHomologicalComplex (restrictionCoverFirst O U V) c).app I ≫ Fst =
      (NatTrans.mapHomologicalComplex (jStarAdjunction U O).unit c).app I := by
    rw [hFstDef, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      restrictionCoverFirst_comp_fst]
  have := hf'
  have := hFstIso
  rw [← hcomp, CategoryTheory.Functor.map_comp]
  exact IsIso.comp_isIso

/-! ### K-injective resolutions -/

/-- The accepted Grothendieck-category resolution theorem supplies K-injective representatives
for complexes of sheaves of modules. -/
private lemma exists_quasiIso_isKInjective_sheafOfModules
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    ∀ K : CochainComplex (SheafOfModules.{u} O) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} O) ℤ) (f : K ⟶ I),
        I.IsKInjective ∧ QuasiIso f := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) := inferInstance
  let R := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective
    (SheafOfModules.{u} O)).some
  intro K
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩

/-- The same resolution has injective terms, which is what the Mayer--Vietoris short exact
sequence of Tag 08BV requires. -/
lemma exists_quasiIso_isKInjective_injective_sheafOfModules
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} O) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ (∀ n : ℤ, Injective (I.X n)) ∧ QuasiIso f := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) := inferInstance
  let R := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective
    (SheafOfModules.{u} O)).some
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K,
    fun n => R.injective K n, R.quasiIso K⟩

/-! ### The comparison maps -/

/-- The specified comparison for derived pushforward is invertible on K-injective input. -/
private lemma isIso_alpha_j_at_isKInjective
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ)
    (hI : I.IsKInjective) :
    IsIso (αj.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_sheafOfModules (resRing U O))).2
      DerivedCategory.Qh Rj αj I hI

/-- An isomorphism after restriction induces isomorphisms on stalks in that open. -/
private lemma isIso_stalk_of_isIso_jStar_map
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : Opens X) {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (hf : IsIso ((jStar V O).map f)) (x : X) (hx : x ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toAb O).map f)) := by
  have hab : IsIso ((toAb (resRing V O)).map ((jStar V O).map f)) :=
    Functor.map_isIso _ _
  have hrestr : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : Usp V)).map
        (Functor.whiskerLeft (TopCat.Presheaf.imF V).op ((toAb O).map f))) := by
    rw [← toAb_jStar_map V O f]
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ hab
  exact (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff V _ _
    ((toAb O).map f) ⟨x, hx⟩).mp hrestr

/-- Isomorphisms of module sheaves can be checked on two opens covering the space. -/
private lemma isIso_of_isIso_jStar_map_on_cover
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V W : Opens X) (hVW : ∀ x : X, x ∈ V ∨ x ∈ W)
    {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (hV : IsIso ((jStar V O).map f)) (hW : IsIso ((jStar W O).map f)) :
    IsIso f := by
  apply isIso_of_stalk_isIso O f
  intro x
  rcases hVW x with hx | hx
  · exact isIso_stalk_of_isIso_jStar_map O V f hV x hx
  · exact isIso_stalk_of_isIso_jStar_map O W f hW x hx

/-- If the derived restriction of a morphism to `V` is invertible, so is the restriction to `V` of
each of its cohomology sheaves. -/
private lemma isIso_jStar_map_homology_of_isIso_mapDerived
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing V O))]
    {E F : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ F) (i : ℤ)
    (hV : IsIso ((jStar V O).mapDerivedCategory.map f)) :
    IsIso ((jStar V O).map ((DerivedCategory.homologyFunctor _ i).map f)) := by
  apply (NatIso.isIso_map_iff (exactFunctorDerivedHomologyIso (jStar V O) i) f).mp
  change IsIso ((DerivedCategory.homologyFunctor _ i).map ((jStar V O).mapDerivedCategory.map f))
  exact Functor.map_isIso _ _

/-- Restriction to a two-open cover jointly detects isomorphisms in the derived category. -/
private lemma isIso_derived_of_isIso_restrictions_on_cover
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V W : Opens X) (hVW : ∀ x : X, x ∈ V ∨ x ∈ W)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing V O))]
    [HasDerivedCategory (SheafOfModules.{u} (resRing W O))]
    {E F : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ F)
    (hV : IsIso ((jStar V O).mapDerivedCategory.map f))
    (hW : IsIso ((jStar W O).mapDerivedCategory.map f)) :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  exact isIso_of_isIso_jStar_map_on_cover O V W hVW _
    (isIso_jStar_map_homology_of_isIso_mapDerived O V f i hV)
    (isIso_jStar_map_homology_of_isIso_mapDerived O W f i hW)

/-- **Restriction to a two-open cover jointly detects isomorphisms in the derived category.**
A morphism of `D(𝒪_X)` whose restrictions to two opens covering `X` are invertible is itself
invertible: by `DerivedCategory.isIso_iff` the question is one about the cohomology sheaves, and
there it is settled on the stalks, every point lying in one of the two opens. -/
lemma isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V W : Opens X) (hVW : ∀ x : X, x ∈ V ∨ x ∈ W)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing V O))]
    [HasDerivedCategory (SheafOfModules.{u} (resRing W O))]
    [(jStar V O).Additive] [PreservesFiniteLimits (jStar V O)]
    [PreservesFiniteColimits (jStar V O)]
    [(jStar W O).Additive] [PreservesFiniteLimits (jStar W O)]
    [PreservesFiniteColimits (jStar W O)]
    {E F : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ F)
    (hV : IsIso ((jStar V O).mapDerivedCategory.map f))
    (hW : IsIso ((jStar W O).mapDerivedCategory.map f)) :
    IsIso f := by
  exact isIso_derived_of_isIso_restrictions_on_cover O V W hVW f hV hW

/-- The canonical restriction unit, obtained by descending the underived unit followed by
the comparison to the chosen right derived pushforward. -/
noncomputable def derivedPushforwardRestrictionUnit
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (alpha_j : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj) :
    𝟭 (DerivedCategory (SheafOfModules.{u} O)) ⟶
      (jStar U O).mapDerivedCategory ⋙ Rj := by
  let e : (𝟭 (SheafOfModules.{u} O)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ))
        (HomotopyCategory.quotient _ _))
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _).preimage
      (whiskerRight e.inv DerivedCategory.Qh ≫
        whiskerRight (NatTrans.mapHomotopyCategory (jStarAdjunction U O).unit
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        whiskerRight (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (jStar U O ⋙ jPush U O)) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        whiskerLeft ((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)) alpha_j ≫
        whiskerRight (jStar U O).mapDerivedCategoryFactorsh.inv Rj)

/-- The canonical comparison from extension by zero to derived pushforward, obtained by
descending the comparison of the underived adjoint triple followed by the right-derived
comparison map. -/
noncomputable def extensionByZeroToDerivedPushforward
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (alpha_j : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj) :
    (jShriek U O).mapDerivedCategory ⟶ Rj := by
  letI : (jShriek U O).Full := (jShriekFullyFaithful U O).full
  letI : (jShriek U O).Faithful := (jShriekFullyFaithful U O).faithful
  letI : (jPush U O).Full :=
    (jStarAdjunction U O).fullyFaithfulROfIsIsoCounit.full
  letI : (jPush U O).Faithful :=
    (jStarAdjunction U O).fullyFaithfulROfIsIsoCounit.faithful
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _).preimage
      ((jShriek U O).mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (NatTrans.mapHomotopyCategory (openImmersionTriple U O).leftToRight
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ alpha_j)

/-- Whiskering the preimage of a transformation along a localization functor gives it back. -/
private lemma whiskerLeft_preimage_fullyFaithfulWhiskeringLeft
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (L : C ⥤ D)
    (W : MorphismProperty C) [L.IsLocalization W] {F G : D ⥤ E} (θ : L ⋙ F ⟶ L ⋙ G) :
    whiskerLeft L ((Localization.fullyFaithfulWhiskeringLeft L W E).preimage θ) = θ :=
  (Localization.fullyFaithfulWhiskeringLeft L W E).map_preimage θ

/-- The specified derived unit is invertible on a supported K-injective representative with
injective terms. -/
private lemma isIso_derivedPushforwardRestrictionUnit_at_isKInjective
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hKI : I.IsKInjective)
    (hInj : ∀ n : ℤ, Injective (I.X n))
    (hI : CohomologySupportedOn O T (DerivedCategory.Q.obj I)) :
    IsIso ((derivedPushforwardRestrictionUnit O U Rj αj).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  -- the unit of restriction and pushforward is a quasi-isomorphism on `I`
  have hQu : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (jStarAdjunction U O).unit
        (ComplexShape.up ℤ)).app I)) :=
    isIso_Q_map_restrictPush_unit_of_supported O U T hT hTU I hKI hInj hI
  have hQhu : IsIso (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (jStarAdjunction U O).unit
        (ComplexShape.up ℤ)).app K)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O))
      ((NatTrans.mapHomologicalComplex (jStarAdjunction U O).unit
        (ComplexShape.up ℤ)).app I)).mpr hQu
  let := hKI
  have hKI' : CochainComplex.IsKInjective
      (((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_jStar O U I
  have hα : IsIso (αj.app ((jStar U O).mapHomotopyCategory
      (ComplexShape.up ℤ) |>.obj K)) := by
    have hα' := isIso_alpha_j_at_isKInjective O U Rj αj _ hKI'
    exact (NatTrans.isIso_app_iff_of_iso αj
      (((jStar U O).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I)).mpr hα'
  let e : (𝟭 (SheafOfModules.{u} O)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ))
        (HomotopyCategory.quotient _ _))
  let θ := whiskerRight e.inv DerivedCategory.Qh ≫
    whiskerRight (NatTrans.mapHomotopyCategory (jStarAdjunction U O).unit
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (jStar U O ⋙ jPush U O)) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    whiskerLeft ((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)) αj ≫
    whiskerRight (jStar U O).mapDerivedCategoryFactorsh.inv Rj
  have hθ : IsIso (θ.app K) := by
    let := hQhu
    let := hα
    simp only [θ, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  have heq : whiskerLeft DerivedCategory.Qh
      (derivedPushforwardRestrictionUnit O U Rj αj) = θ := by
    unfold derivedPushforwardRestrictionUnit
    exact whiskerLeft_preimage_fullyFaithfulWhiskeringLeft _ _
      (F := 𝟭 (DerivedCategory (SheafOfModules.{u} O))) (G := (jStar U O).mapDerivedCategory ⋙ Rj) θ
  change IsIso ((whiskerLeft DerivedCategory.Qh
    (derivedPushforwardRestrictionUnit O U Rj αj)).app K)
  rw [heq]
  exact hθ

/-- If every cohomology sheaf of `E` is supported on the closed subset `T ⊆ U`, the unit from
`E` to `Rj(E|_U)` is an isomorphism, for every right derived functor `Rj` of the pushforward
along the open subspace. -/
theorem isIso_derivedPushforwardRestriction_unit_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O T E) :
    IsIso ((derivedPushforwardRestrictionUnit O U Rj αj).app E) := by
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} O)
  let K := Q.objPreimage E
  obtain ⟨I, f, hKI, hInj, hf⟩ :=
    exists_quasiIso_isKInjective_injective_sheafOfModules O K
  let := hf
  let e : E ≅ Q.obj I := (Q.objObjPreimageIso E).symm ≪≫ asIso (Q.map f)
  have hI : CohomologySupportedOn O T (Q.obj I) :=
    cohomologySupportedOn_of_iso O T e hE
  have hQh := isIso_derivedPushforwardRestrictionUnit_at_isKInjective
    O U T hT hTU Rj αj I hKI hInj hI
  have hQI : IsIso ((derivedPushforwardRestrictionUnit O U Rj αj).app (Q.obj I)) :=
    (NatTrans.isIso_app_iff_of_iso (derivedPushforwardRestrictionUnit O U Rj αj)
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).app I)).mp hQh
  exact (NatTrans.isIso_app_iff_of_iso
    (derivedPushforwardRestrictionUnit O U Rj αj) e).mpr hQI

/-- Derived pushforward of an object supported in a closed subset of the open has the same
support, using the derived unit for its extension by zero. -/
private lemma cohomologySupportedOn_derivedPushforward_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ)
    (hI : CohomologySupportedOn (resRing U O)
      ((fun x : Usp U ↦ x.1) ⁻¹' T) (DerivedCategory.Q.obj I)) :
    CohomologySupportedOn O T (Rj.obj (DerivedCategory.Q.obj I)) := by
  let J := ((jShriek U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hD := cohomologySupportedOn_jShriek O U T (DerivedCategory.Q.obj I) hI
  have hJ : CohomologySupportedOn O T (DerivedCategory.Q.obj J) :=
    cohomologySupportedOn_of_iso O T
      (((jShriek U O).mapDerivedCategoryFactors).app I) hD
  have hunit := isIso_derivedPushforwardRestriction_unit_of_supported
    O U T hT hTU Rj αj (DerivedCategory.Q.obj J) hJ
  let eStar : ((jStar U O).mapDerivedCategory).obj (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj I :=
    ((jStar U O).mapDerivedCategoryFactors).app J ≪≫
      (DerivedCategory.Q.mapIso (jStar_jShriek_complexIso O U I)).symm
  let e : DerivedCategory.Q.obj J ≅ Rj.obj (DerivedCategory.Q.obj I) :=
    asIso ((derivedPushforwardRestrictionUnit O U Rj αj).app
      (DerivedCategory.Q.obj J)) ≪≫ Rj.mapIso eStar
  exact cohomologySupportedOn_of_iso O T e hJ

/-- Restriction takes the underived comparison between extension by zero and pushforward
to an isomorphism. -/
private lemma isIso_jStar_map_leftToRight
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [(jShriek U O).Full] [(jShriek U O).Faithful]
    [(jPush U O).Full] [(jPush U O).Faithful]
    (M : SheafOfModules.{u} (resRing U O)) :
    IsIso ((jStar U O).map ((openImmersionTriple U O).leftToRight.app M)) := by
  let := isIso_jShriekAdjunction_unit U O
  have hunit : IsIso ((jStar U O).map
      ((jStarAdjunction U O).unit.app ((jShriek U O).obj M))) := by
    have hcomp : IsIso ((jStar U O).map
        ((jStarAdjunction U O).unit.app ((jShriek U O).obj M)) ≫
        (jStarAdjunction U O).counit.app
          ((jStar U O).obj ((jShriek U O).obj M))) := by
      have htri := (jStarAdjunction U O).left_triangle_components
        ((jShriek U O).obj M)
      rw [htri]
      infer_instance
    let := hcomp
    exact IsIso.of_isIso_comp_right
      ((jStar U O).map ((jStarAdjunction U O).unit.app ((jShriek U O).obj M)))
      ((jStarAdjunction U O).counit.app
        ((jStar U O).obj ((jShriek U O).obj M)))
  rw [(openImmersionTriple U O).leftToRight_app, Functor.map_comp]
  infer_instance

/-- The termwise comparison becomes an isomorphism after restriction. -/
private lemma isIso_jStar_map_complex_leftToRight
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [(jShriek U O).Full] [(jShriek U O).Faithful]
    [(jPush U O).Full] [(jPush U O).Faithful]
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ) :
    IsIso (((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (openImmersionTriple U O).leftToRight
        (ComplexShape.up ℤ)).app I)) := by
  let f := ((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex (openImmersionTriple U O).leftToRight
      (ComplexShape.up ℤ)).app I)
  have : ∀ i : ℤ, IsIso (f.f i) := fun i =>
    isIso_jStar_map_leftToRight O U (I.X i)
  exact HomologicalComplex.Hom.isIso_of_components f

/-- The derived restriction of the comparison is invertible on represented objects. -/
private lemma isIso_jStar_mapDerived_leftToRight
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    [(jShriek U O).Full] [(jShriek U O).Faithful]
    [(jPush U O).Full] [(jPush U O).Faithful]
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ) :
    IsIso ((jStar U O).mapDerivedCategory.map
      (DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (openImmersionTriple U O).leftToRight
          (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) := by
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let f := (NatTrans.mapHomologicalComplex (openImmersionTriple U O).leftToRight
    (ComplexShape.up ℤ)).app I
  have hcomplex : IsIso (((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    isIso_jStar_map_complex_leftToRight O U I
  have hhom : IsIso (((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomotopyCategory (openImmersionTriple U O).leftToRight
        (ComplexShape.up ℤ)).app K)) := by
    change IsIso (((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f))
    exact (NatIso.isIso_map_iff
      ((jStar U O).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) f).mpr
        (Functor.map_isIso (HomotopyCategory.quotient _ _) _)
  exact (NatIso.isIso_map_iff ((jStar U O).mapDerivedCategoryFactorsh)
    ((NatTrans.mapHomotopyCategory (openImmersionTriple U O).leftToRight
      (ComplexShape.up ℤ)).app K)).mpr (Functor.map_isIso DerivedCategory.Qh _)

/-- The chosen comparison is invertible after restricting back to the open. -/
private lemma isIso_jStar_extensionByZeroToDerivedPushforward_at_isKInjective
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ)
    (hKI : I.IsKInjective) :
    IsIso ((jStar U O).mapDerivedCategory.map
      ((extensionByZeroToDerivedPushforward O U Rj αj).app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) := by
  let : (jShriek U O).Full := (jShriekFullyFaithful U O).full
  let : (jShriek U O).Faithful := (jShriekFullyFaithful U O).faithful
  let := isIso_jStarAdjunction_counit U O
  let : (jPush U O).Full :=
    (jStarAdjunction U O).fullyFaithfulROfIsIsoCounit.full
  let : (jPush U O).Faithful :=
    (jStarAdjunction U O).fullyFaithfulROfIsIsoCounit.faithful
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  have hα : IsIso (αj.app K) := isIso_alpha_j_at_isKInjective O U Rj αj I hKI
  have hraw := isIso_jStar_mapDerived_leftToRight O U I
  let θ := (jShriek U O).mapDerivedCategoryFactorsh.hom ≫
    whiskerRight (NatTrans.mapHomotopyCategory (openImmersionTriple U O).leftToRight
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ αj
  have hθ : IsIso ((jStar U O).mapDerivedCategory.map (θ.app K)) := by
    let := hα
    let := hraw
    dsimp [θ]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have heq : whiskerLeft DerivedCategory.Qh
      (extensionByZeroToDerivedPushforward O U Rj αj) = θ := by
    unfold extensionByZeroToDerivedPushforward
    exact whiskerLeft_preimage_fullyFaithfulWhiskeringLeft _ _
      (F := (jShriek U O).mapDerivedCategory) (G := Rj) θ
  change IsIso ((jStar U O).mapDerivedCategory.map
    ((whiskerLeft DerivedCategory.Qh
      (extensionByZeroToDerivedPushforward O U Rj αj)).app K))
  rw [heq]
  exact hθ

/-- If every cohomology sheaf of `F` is supported on the closed subset `T ⊆ U`, the canonical
natural map from extension by zero to `Rj` is an isomorphism at `F`, for every right derived
functor `Rj` of the pushforward along the open subspace. -/
theorem isIso_extensionByZeroToDerivedPushforward_app_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O)
      ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    IsIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F) := by
  let V : Opens X := ⟨Tᶜ, hT.isOpen_compl⟩
  -- The derived category of the complement open occurs only as a device for detecting
  -- isomorphisms, never in the statement, so any model of it will do.
  let : HasDerivedCategory (SheafOfModules.{u} (resRing V O)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} (resRing ⟨Tᶜ, hT.isOpen_compl⟩ O)) :=
    HasDerivedCategory.standard _
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (resRing U O))
  let K := Q.objPreimage F
  obtain ⟨I, f, hKI, hf⟩ := exists_quasiIso_isKInjective_sheafOfModules
    (resRing U O) K
  let := hf
  let e : F ≅ Q.obj I := (Q.objObjPreimageIso F).symm ≪≫ asIso (Q.map f)
  have hI : CohomologySupportedOn (resRing U O)
      ((fun x : Usp U ↦ x.1) ⁻¹' T) (Q.obj I) :=
    cohomologySupportedOn_of_iso (resRing U O) _ e hF
  let β := extensionByZeroToDerivedPushforward O U Rj αj
  have hUQh := isIso_jStar_extensionByZeroToDerivedPushforward_at_isKInjective
    O U Rj αj I hKI
  have hU : IsIso ((jStar U O).mapDerivedCategory.map (β.app (Q.obj I))) :=
    (NatTrans.isIso_app_iff_of_iso
      (whiskerRight β (jStar U O).mapDerivedCategory)
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (resRing U O))).app I)).mp hUQh
  have hsource := cohomologySupportedOn_jShriek O U T (Q.obj I) hI
  have htarget := cohomologySupportedOn_derivedPushforward_of_supported
    O U T hT hTU Rj αj I hI
  have hV : IsIso ((jStar V O).mapDerivedCategory.map (β.app (Q.obj I))) := by
    have hs := isZero_derived_restrict_compl_of_supported
      O T hT ((jShriek U O).mapDerivedCategory.obj (Q.obj I)) hsource
    have ht := isZero_derived_restrict_compl_of_supported
      O T hT (Rj.obj (Q.obj I)) htarget
    exact hs.isIso ht _
  have hQI : IsIso (β.app (Q.obj I)) :=
    isIso_derived_of_isIso_restrictions_on_cover O U V
      (fun x => by
        have h := (show U ⊔ V = ⊤ from open_sup_compl_closed_eq_top U T hT hTU)
        have hx : x ∈ (⊤ : Opens X) := trivial
        rw [← h] at hx
        exact hx) (β.app (Q.obj I)) hU hV
  exact (NatTrans.isIso_app_iff_of_iso β e).mpr hQI

/-! ### The derived pushforward along the open subspace -/

/-- The pushforward `j_*` on homotopy categories followed by the localization
`K(O_X) ⥤ D(O_X)`: the functor whose right derived functor is `Rj_* : D(O_U) ⥤ D(O_X)`. -/
noncomputable abbrev openPushforwardToDerived
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)] :
    HomotopyCategory (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O) :=
  (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The pushforward along the open subspace has a pointwise right derived functor on the
unbounded derived category, every complex of sheaves of modules having a K-injective
resolution. -/
theorem openPushforwardToDerived_hasPointwiseRightDerivedFunctor
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)] :
    (openPushforwardToDerived O U).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u, _,
    0, u + 1, u + 1, 0} (openPushforwardToDerived O U)
    (exists_quasiIso_isKInjective_sheafOfModules (resRing U O))).1

/-- The pushforward along the open subspace has a right derived functor on the unbounded
derived category. -/
instance openPushforwardToDerived_hasRightDerivedFunctor
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)] :
    (openPushforwardToDerived O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  haveI := openPushforwardToDerived_hasPointwiseRightDerivedFunctor O U
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **The derived pushforward `Rj_* : D(O_U) ⥤ D(O_X)`** along the inclusion `j : U → X` of an
open subspace: the total right derived functor of `j_*` on the unbounded derived categories of
sheaves of modules. -/
noncomputable def derivedOpenPushforward
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))] :
    DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O) :=
  (openPushforwardToDerived O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison map `K(j_*) ⋙ Q ⟶ Q ⋙ Rj_*` of the derived pushforward along the open
subspace. -/
noncomputable def derivedOpenPushforwardUnit
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))] :
    (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedOpenPushforward O U :=
  (openPushforwardToDerived O U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- `Rj_*` with its comparison map is the right derived functor of `j_*`. -/
instance isRightDerivedFunctor_derivedOpenPushforward
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))] :
    (derivedOpenPushforward O U).IsRightDerivedFunctor (derivedOpenPushforwardUnit O U)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  inferInstanceAs (((openPushforwardToDerived O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((openPushforwardToDerived O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) _)

/-- **Stacks Project, Tag 08DF, part (1).** Let `j : U → X` be the inclusion of an open
subspace of a ringed space and `T ⊆ U` a closed subset of `X`. If every cohomology sheaf of
`E ∈ D(O_X)` is supported on `T`, then the canonical map `E ⟶ Rj_*(E|_U)` is an
isomorphism. -/
@[stacks 08DF "part (1)"]
theorem isIso_derivedOpenPushforward_restrictionUnit_app_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O T E) :
    IsIso ((derivedPushforwardRestrictionUnit O U (derivedOpenPushforward O U)
      (derivedOpenPushforwardUnit O U)).app E) :=
  isIso_derivedPushforwardRestriction_unit_of_supported O U T hT hTU
    (derivedOpenPushforward O U) (derivedOpenPushforwardUnit O U) E hE

/-- **Stacks Project, Tag 08DF, part (2).** Let `j : U → X` be the inclusion of an open
subspace of a ringed space and `T ⊆ U` a closed subset of `X`. If every cohomology sheaf of
`F ∈ D(O_U)` is supported on `T`, then the canonical map `j_! F ⟶ Rj_* F` is an
isomorphism. -/
@[stacks 08DF "part (2)"]
theorem isIso_extensionByZeroToDerivedOpenPushforward_app_of_supported
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U)
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O)
      ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    IsIso ((extensionByZeroToDerivedPushforward O U (derivedOpenPushforward O U)
      (derivedOpenPushforwardUnit O U)).app F) :=
  isIso_extensionByZeroToDerivedPushforward_app_of_supported O U T hT hTU
    (derivedOpenPushforward O U) (derivedOpenPushforwardUnit O U) F hF

end Stacks.Cohomology.PushforwardRestriction

end
