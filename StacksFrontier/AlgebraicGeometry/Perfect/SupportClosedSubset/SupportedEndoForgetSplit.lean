module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetUnits

/-!
# Splitting the exact direct image out of the two readings of Stacks 0G74 part (2)

[Stacks, Tag 0G74] part (2) is stated twice in the library: on the closed subset `T`, as
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`, and with the direct
image `i_*` folded in, as
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`.  Both are
`CategoryTheory.Functor.rightDerivedDesc` of the *same* ambient derived functor
`i_* R𝓗_T ⋙ Φ_X^D`, at the derivation unit
`Stacks.Cohomology.AbelianSupportedCounit.forgetfulSupportedEndoUnit`, so
`CategoryTheory.Functor.rightDerived_ext` reduces their comparison to one identity of the two
transported units at an object of the homotopy category:

`forgetfulSupportedEndoUnit ≫ Qh ⋆ (RH_T ⋆ cmp ≫ 0G74-on-T ⋆ i_*^{ab,D})`
  `= abelianSupportedEndoForgetUnit`,

where `cmp` is
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` — the move
of the direct image past the forgetful functor on *derived* categories, without which the two
transformations do not even have the same source.

This file proves everything that identity needs, and records the rearrangement that assembles
them.

## Main results

* `unitComp_eq`: **the left-hand side, with the exact direct image split off.**  It is the
  reassociation `derivedSupportedPushforwardSplit`, forgotten, followed by `cmp` at the image of
  `ℋ_T`, followed by the direct image of
  `Stacks.Cohomology.SupportedComplexes.supportedSheafForgetUnit`.
* `fach_comp`: **what `cmp` contributes.**  Flanked by the two
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the two forgetful functors it is the
  comparison of the direct images read degreewise — the `DerivedCategory.Qh` form of
  `derivedModulePushforwardCompToSheafIso_fac`, solved for the three leading factors.
* `derivedAbelianSupportedPushforwardUnit_app`, `..._app'` and `..._app_forget`: the abelian
  derivation unit of `i_* R𝓗_T^{ab}` at an object, opened up, in the spelling the right-hand side
  of the identity presents it in.
* `factorsh_naturality_forget`, `factorsh_naturality_closedPushforward`: the two naturality
  squares of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` that move the two comparisons of
  [Stacks, Tag 0G6N] from one side of a descent to the other.
* `Qh_forgetPushforwardSquare`:
  `Stacks.Cohomology.SupportedSectionsForgetPushforward.forgetPushforwardSquare_homotopy`
  localized to the derived category — the only factor of the identity carrying mathematical
  content.
* `unitIdentity_formal`: **the rearrangement, at a variable category.**  Given the five identities
  above in the shape they occur in, it produces the unit identity.

## Where the assembly happens

`unitIdentity_formal` is not applied here.  It is applied in
`StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetIdentity`, to the
five inputs above — `unitComp_eq` normalizes the left-hand side, `fach_comp` is `hB`,
`factorsh_naturality_forget` is `hnat1`, `factorsh_naturality_closedPushforward` is `hnat2`,
`Qh_forgetPushforwardSquare` is `hM`, and `hR7` is `rfl` — which yields the unit identity and so,
by `CategoryTheory.Functor.rightDerived_ext`, the equality of the two readings of
[Stacks, Tag 0G74] part (2).

The application has to be a declaration of its own: opening the two seven-factor units up and
then instantiating `unitIdentity_formal` at them exceeds the default heartbeat limit in one
declaration, and `set_option maxHeartbeats` is not used in this development.  It also has to be an
`apply` rather than an `exact`, so that the conclusion is unified with the goal before any
hypothesis is elaborated, and `hM` has to be discharged before `hnat2`, which is why the
hypotheses are named.

## Implementation notes

**Everything is applied with `exact` or `refine`, never `rw` or `simp`, wherever a composite
crosses between the two spellings `i_* ⋙ Φ_X` and `Φ_T ⋙ i_*^{ab}` of one functor.**  Those two
are definitionally equal and syntactically distinct, so a rewrite whose motive mentions the
crossing is reported as not type-correct at the implicit transparency level.  Each such step is
therefore a lemma stated at a variable category — `head_split`, `mid4`, `tail3`, `map_merge` and
`map_pair_eq` here, and
`Stacks.Cohomology.SupportedSectionsForgetPushforward.map_comp_head_id` and
`Stacks.Perfect.SupportedEndoForget.comp_assoc_id` taken from where they already were — applied
with `exact`, which checks up to definitional equality.  This is the device of
`Stacks.Perfect.AbelianCechDerivedSquare.square_formal`.

**The exactness instances are written into the statements, not assumed.**  `i_*` is exact only
because `T` is closed, so `PreservesFiniteColimits` is not an instance; the statements carry the
proofs as `letI`, spelled exactly as the definitions of
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward` and
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward` spell them.  A
`letI` in a tactic block introduces a local hypothesis instead, and instance search then produces
that free variable where the goal has the closed term, which is invisible to `rw`; that is why
`fach_comp_factorsh` passes the instances to
`derivedModulePushforwardCompToSheafIso_fach` positionally.

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.SupportedSectionsForgetPushforward
open Stacks.Cohomology.AbelianSupportedCounitForget (forgetCompIso)
open Stacks.Cohomology.UnderlyingAbelianSheaf (underlyingDerivedSheaf)
open Stacks.Perfect.SupportedEndoForget
open Stacks.Perfect.SupportedQuasicoherent
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedEndoForgetSplit

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

private lemma map_merge {D₀ E₀ : Type*} [Category* D₀] [Category* E₀] (F : D₀ ⥤ E₀)
    {A B C : D₀} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (hh : f ≫ g = h) :
    F.map f ≫ F.map g = F.map h := by rw [← F.map_comp, hh]

private lemma map_pair_eq {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {A B B' C : C₀} (a : A ⟶ B) (b : B ⟶ C) (a' : A ⟶ B') (b' : B' ⟶ C)
    (h : a ≫ b = a' ≫ b') : W.map a ≫ W.map b = W.map a' ≫ W.map b' := by
  rw [← W.map_comp, ← W.map_comp, h]

/-- **The formal skeleton of the remaining identity.**  See the implementation notes: this is
the rearrangement that turns `unitComp_eq`, `fach_comp`, the two naturalities and
`Qh_forgetPushforwardSquare` into the unit identity of [Stacks, Tag 0G74] part (2). -/
lemma unitIdentity_formal {B₀ C₀ : Type*} [Category* B₀] [Category* C₀] (P : B₀ ⥤ C₀)
    {p q₀ r₀ t₀ u₀ : B₀} (f1 : p ⟶ q₀) (f3 : q₀ ⟶ r₀) (f6 : r₀ ⟶ t₀) (f7 : t₀ ⟶ u₀)
    {A A' B C G G' H : C₀} (s₁ : A ⟶ B) (s₂ : B ⟶ C) (cm : C ⟶ P.obj p)
    (r : B ⟶ G) (qq : G ⟶ P.obj q₀) (hB : s₂ ≫ cm ≫ P.map f1 = r ≫ qq)
    (r' : A ⟶ A') (t₁ : A' ⟶ G) (hnat1 : s₁ ≫ r = r' ≫ t₁)
    (t₂ : G ⟶ G') (q' : G' ⟶ P.obj r₀) (hnat2 : qq ≫ P.map f3 = t₂ ≫ q')
    (v₁ : A' ⟶ H) (v₂ : H ⟶ G') (hM : t₁ ≫ t₂ = v₁ ≫ v₂)
    (R7 : P.obj t₀ ⟶ P.obj u₀) (hR7 : P.map f7 = R7) :
    s₁ ≫ s₂ ≫ cm ≫ P.map (f1 ≫ f3 ≫ f6 ≫ f7) =
      r' ≫ v₁ ≫ (v₂ ≫ q' ≫ P.map f6) ≫ R7 := by
  subst hR7
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hB, reassoc_of% hnat1, reassoc_of% hnat2, reassoc_of% hM]

private lemma head_split {C₀ : Type*} [Category* C₀] {A B M A' : C₀} (u : A ⟶ B)
    (a : A ⟶ A') (b : A' ⟶ B) (h : u = a ≫ b) (z : B ⟶ M) :
    u ≫ z = a ≫ b ≫ z := by rw [h, Category.assoc]

private lemma mid4 {C₀ : Type*} [Category* C₀] {A B C D M C' : C₀} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (b' : B ⟶ C') (c' : C' ⟶ D) (h : b ≫ c = b' ≫ c') (d : D ⟶ M) :
    a ≫ b ≫ c ≫ d = a ≫ b' ≫ c' ≫ d := by
  rw [← Category.assoc b c d, h, Category.assoc]

private lemma tail3 {C₀ : Type*} [Category* C₀] {W V A B M : C₀} (a : W ⟶ V) (b : V ⟶ A)
    (c : A ⟶ B) (d : B ⟶ M) (e : A ⟶ M) (h : c ≫ d = e) : a ≫ b ≫ c ≫ d = a ≫ b ≫ e := by
  rw [h]

/-- **The left-hand side of the unit identity, with the exact direct image split off.**

The derivation unit of `i_* R𝓗_T`, forgotten, composed with the comparison of
[Stacks, Tag 0G74] part (2) on `T` read through the derived pushforward/forget comparison, is the
reassociation that splits the exact direct image off, followed by that comparison at the image of
`ℋ_T`, followed by the direct image of `supportedSheafForgetUnit`.

The proof moves the derivation unit of `R𝓗_T` across the derived pushforward/forget comparison by
its naturality, and then collapses what is left by the characterising factorization
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison_fac`. -/
theorem unitComp_eq
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    (forgetfulSupportedEndoUnit X T (derivedSupportedPushforward X T hT)
          (derivedSupportedPushforwardUnit X T hT)).app K ≫
        ((derivedSupportedSectionsOnClosed X T hT).whiskerLeft
              (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom ≫
            Functor.whiskerRight
              (localCohomologySheafForgetComparison X T hT
                (derivedAbelianSupportedSectionsOnClosed X T hT)
                (derivedAbelianSupportedSectionsOnClosedUnit X T hT)
                (derivedSupportedSectionsOnClosed X T hT)
                (derivedSupportedSectionsOnClosedUnit X T hT))
              (abelianClosedPushforward T).mapDerivedCategory).app
          (DerivedCategory.Qh.obj K) =
      (underlyingDerivedSheaf (structureSheafRing X)).map
          ((derivedSupportedPushforwardSplit X T hT).hom.app K) ≫
        (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.app
          (DerivedCategory.Qh.obj (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((supportedSheafForgetUnit X T hT
            (derivedAbelianSupportedSectionsOnClosed X T hT)
            (derivedAbelianSupportedSectionsOnClosedUnit X T hT)).app K) := by
  let := pushforward_preservesFiniteLimits X T
  let := pushforward_preservesFiniteColimits X T hT
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  let : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
    abelianClosedPushforward_preservesFiniteColimits X T hT
  have hnat := (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.naturality
    ((derivedSupportedSectionsOnClosedUnit X T hT).app K)
  simp only [Functor.comp_map] at hnat
  have e1 : (forgetfulSupportedEndoUnit X T (derivedSupportedPushforward X T hT)
        (derivedSupportedPushforwardUnit X T hT)).app K =
      (underlyingDerivedSheaf (structureSheafRing X)).map
          ((derivedSupportedPushforwardSplit X T hT).hom.app K) ≫
        (underlyingDerivedSheaf (structureSheafRing X)).map
          ((modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory.map
            ((derivedSupportedSectionsOnClosedUnit X T hT).app K)) :=
    (forgetfulSupportedEndoUnit_app X T _ _ K).trans
      ((congrArg (underlyingDerivedSheaf (structureSheafRing X)).map
        (derivedSupportedPushforwardUnit_app X T hT K)).trans
        ((underlyingDerivedSheaf (structureSheafRing X)).map_comp _ _))
  simp only
  refine Eq.trans (head_split _ _ _ e1 _) (Eq.trans (mid4 _ _ _ _ _ hnat _) ?_)
  exact tail3 _ _ _ _ _
    (map_merge _ (localCohomologySheafForgetComparison_fac_app X T hT _ _ _ _ K))

/-- At an object `L`, the derivation unit of `i_* R𝓗_T^{ab}` is the reassociation
`derivedAbelianSupportedPushforwardSplit` followed by the direct image of the derivation unit of
`R𝓗_T^{ab}` at `L`. -/
theorem derivedAbelianSupportedPushforwardUnit_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    (derivedAbelianSupportedPushforwardUnit X T hT).app L =
      (derivedAbelianSupportedPushforwardSplit X T hT).hom.app L ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((derivedAbelianSupportedSectionsOnClosedUnit X T hT).app L) := by
  simp only [derivedAbelianSupportedPushforwardUnit]
  exact SupportedEndoForget.comp_assoc_id _ _

/-- At an object `L`, the derivation unit of `i_* R𝓗_T^{ab}` is the localization of the inverse
of `mapHomotopyCategoryCompIso` of `abelianSupportedSectionsRealizedCompPushforwardIso`, followed
by the inverse of `mapDerivedCategoryFactorsh` of the abelian direct image, followed by the direct
image of the derivation unit of `R𝓗_T^{ab}` at `L`. -/
theorem derivedAbelianSupportedPushforwardUnit_app'
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    (derivedAbelianSupportedPushforwardUnit X T hT).app L =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (abelianSupportedSectionsRealizedCompPushforwardIso T hT)
            (ComplexShape.up ℤ)).inv.app L) ≫
        (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj L) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((derivedAbelianSupportedSectionsOnClosedUnit X T hT).app L) := by
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  rw [derivedAbelianSupportedPushforwardUnit_app,
    derivedAbelianSupportedPushforwardSplit_hom_app, Category.assoc]

/-- `derivedModulePushforwardCompToSheafIso_fach` with the inverse of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the direct image of modules cancelled off
in front. -/
theorem fach_comp_factorsh
    (J : HomotopyCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X T))) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    ((underlyingDerivedSheaf (structureSheafRing X)).map
            ((modulePushforward
              (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.inv.app J) ≫
          (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.app
            (DerivedCategory.Qh.obj J) ≫
          (abelianPushforward (closedSubsetInclusion X T)).mapDerivedCategory.map
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing
                (closedSubsetRingedSpace X T))).mapDerivedCategoryFactorsh.hom.app J)) ≫
        (abelianPushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.hom.app
          (((_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X T))).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
        (((modulePushforward (closedSubsetInclusion X T)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj J) := by
  rw [Category.assoc, Category.assoc,
    @derivedModulePushforwardCompToSheafIso_fach _ _ (closedSubsetInclusion X T)
      (pushforward_preservesFiniteLimits X T) (pushforward_preservesFiniteColimits X T hT)
      (abelianClosedPushforward_preservesFiniteColimits X T hT) J]
  exact Stacks.Cohomology.SupportedSectionsForgetPushforward.map_comp_head_id _ _ _
    (Iso.inv_hom_id_app _ _) _

/-- `fach_comp_factorsh` solved for the three leading factors: the derived pushforward/forget
comparison, flanked by the two `mapDerivedCategoryFactorsh` of the two forgetful functors, is the
comparison of the direct images read degreewise.  Stated in the
`Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward` spelling of the abelian direct
image, which is the one the abelian derived functor of supported sections uses. -/
theorem fach_comp
    (J : HomotopyCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X T))) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    letI : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
      abelianClosedPushforward_preservesFiniteColimits X T hT
    (underlyingDerivedSheaf (structureSheafRing X)).map
          ((modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.inv.app J) ≫
        (derivedModulePushforwardCompToSheafIso (closedSubsetInclusion X T)).hom.app
          (DerivedCategory.Qh.obj J) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing
              (closedSubsetRingedSpace X T))).mapDerivedCategoryFactorsh.hom.app J) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
          (((modulePushforward (closedSubsetInclusion X T)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) ≫
        (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X T))).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) := by
  let := pushforward_preservesFiniteLimits X T
  let := pushforward_preservesFiniteColimits X T hT
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  let : PreservesFiniteColimits (abelianPushforward (closedSubsetInclusion X T)) :=
    abelianClosedPushforward_preservesFiniteColimits X T hT
  exact ((abelianClosedPushforward T).mapDerivedCategoryFactorsh.app _).eq_comp_inv.2
    (fach_comp_factorsh X T hT J)

/-- `derivedAbelianSupportedPushforwardUnit_app'` at the underlying abelian complex, with the
middle factor written at the composite functor `Φ ⋙ ℋ_T` rather than at `ℋ_T` applied to `Φ`:
the two spellings are definitionally equal, and this is where that identification is made. -/
theorem derivedAbelianSupportedPushforwardUnit_app_forget
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    (derivedAbelianSupportedPushforwardUnit X T hT).app
        (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (abelianSupportedSectionsRealizedCompPushforwardIso T hT)
            (ComplexShape.up ℤ)).inv.app
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
            abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          ((derivedAbelianSupportedSectionsOnClosedUnit X T hT).app
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) := by
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  exact derivedAbelianSupportedPushforwardUnit_app' X T hT _

/-- Naturality of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the forgetful functor on
`X`, at the localization of the comparison of [Stacks, Tag 0G6N] for modules. -/
theorem factorsh_naturality_forget
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (underlyingDerivedSheaf (structureSheafRing X)).map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
              (ComplexShape.up ℤ)).inv.app K)) ≫
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
          (((modulePushforward (closedSubsetInclusion X T)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
            (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsFunctor X T).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso
              (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
              (ComplexShape.up ℤ)).inv.app K)) :=
  (_root_.SheafOfModules.toSheaf
      (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
      (ComplexShape.up ℤ)).inv.app K)

/-- Naturality of the inverse of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the
abelian direct image, at the localization of the comparison of homotopy categories of
[Stacks, Tag 0G6N] on `T`. -/
theorem factorsh_naturality_closedPushforward
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := abelianClosedPushforward_preservesFiniteLimits X T hT
    letI := abelianClosedPushforward_preservesFiniteColimits X T hT
    (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X T))).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
            (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (abelianClosedPushforward T).mapDerivedCategory.map
          (DerivedCategory.Qh.map ((forgetCompIsoOnClosed X T hT).hom.app K)) =
      DerivedCategory.Qh.map
          (((abelianClosedPushforward T).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((forgetCompIsoOnClosed X T hT).hom.app K)) ≫
        (abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
            abelianSupportedSectionsOnClosed X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) := by
  let := abelianClosedPushforward_preservesFiniteLimits X T hT
  let := abelianClosedPushforward_preservesFiniteColimits X T hT
  exact ((abelianClosedPushforward T).mapDerivedCategoryFactorsh.inv.naturality
    ((forgetCompIsoOnClosed X T hT).hom.app K)).symm

/-- The square `forgetPushforwardSquare_homotopy`, localized to the derived category. -/
theorem Qh_forgetPushforwardSquare
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso
              (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
              (ComplexShape.up ℤ)).inv.app K)) ≫
        DerivedCategory.Qh.map
          (((abelianClosedPushforward T).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((forgetCompIsoOnClosed X T hT).hom.app K)) =
      DerivedCategory.Qh.map ((forgetCompIso X T).hom.app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (abelianSupportedSectionsRealizedCompPushforwardIso T hT)
            (ComplexShape.up ℤ)).inv.app
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) :=
  map_pair_eq DerivedCategory.Qh _ _ _ _ (forgetPushforwardSquare_homotopy X T hT K)

end Stacks.Perfect.SupportedEndoForgetSplit

end
