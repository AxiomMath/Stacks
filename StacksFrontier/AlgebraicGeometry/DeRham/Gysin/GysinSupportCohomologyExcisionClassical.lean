module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinSupportCohomologyOnBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionComp
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportPushExcisionFold
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonSourceNaturality
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsKInjective

/-!
# The derived excision of 0G78 in degree `n` is the classical excision for `Rⁿ H_T`

`Stacks.Gysin.supportCohomologyPullbackIso` is the derived excision of [Stacks, Tag 0G78] read on
degree-`n` cohomology sheaves: for an open immersion of ringed spaces `f : X' ⟶ X`, a closed
`T ⊆ X` and `T' = f^{-1}(T)`, it identifies `f^*(i_*ℋ ⁿ_T(ℱ))` with `i'_*ℋ ⁿ_{T'}(f^*ℱ)`.
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso` is the
*classical* excision for the same situation: `Rⁿ H_T(ℱ)|_{X'} ≅ Rⁿ H_{T'}(f^*ℱ)` for the right
derived functors, in Mathlib's `CategoryTheory.Functor.rightDerived`, of the subsheaf
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` of sections with support.  The
two were built by different routes — the universal property of right derivation on the unbounded
derived category, and [Stacks, Tag 015Z] on injective resolutions — and nothing related them.

This file relates them, for the ringed-space inclusion of an open subscheme: the derived excision
is the classical one conjugated by `Stacks.Gysin.supportCohomologyOnIso`, the identification of
the two spellings of the target of the Gysin map of [Stacks, Tag 0G86].  That is
`supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback`.

## Main results

* `Stacks.Gysin.supportedSectionsOnClosedComp_foldZero_compat`: **the two degree-zero excisions
  correspond** under the identification `i_* H_T^{on T} ≅ H_T` of [Stacks, Tag 0G6N] on the two
  spaces: whiskering that identification into
  `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` gives
  `Stacks.Perfect.SupportPushExcision.foldZeroIso`.  This is the hypothesis `hκ` of
  `Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app`.
* `Stacks.Gysin.transportedClassicalExcision_eq_derivedExcision_app`: **the two coherences,
  pasted**, for an abstract excision datum: the degree-`n` cohomology of the derived excision,
  followed by the derived/classical bridge for the target and the right derived functor of `κ'`,
  is `L` pulled out of the cohomology, followed by the bridge for the source and the right derived
  functor of `κ` under `L`, followed by the classical excision at the *second* spelling of the
  degree-zero functors.
* `Stacks.Gysin.supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback`:
  **the derived excision in degree `n` is the classical excision**, conjugated by
  `Stacks.Gysin.supportCohomologyOnIso`.

## Implementation notes

**The derivation, in five steps.**  Write `S₁ = H_T^{on T} ⋙ i_*` and `S₂ = H_T` for the two
degree-zero endofunctors of `Mod(𝒪_X)`, `κ : S₁ ≅ S₂` for the identification of
[Stacks, Tag 0G6N], primed versions on `X'`, `L = f^*`, and `b`, `b'` for the derived/classical
bridges `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` of `S₁` and `S₁'`.

1. The left-hand side is, **by `rfl`**, the comparison of `Hⁿ` with `f^*` inverted, followed by
   `Hⁿ` of a three-factor composite whose middle factor is the derived excision of
   [Stacks, Tag 0G78]; `Stacks.Perfect.SupportPushExcision`
   `.derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision` rewrites that middle
   factor, and the two copies of
   `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` it carries cancel
   against the outer two factors.
2. The copy of "an exact functor commutes with `Hⁿ`" that
   `Stacks.Gysin.supportCohomologyPullbackIso` is built from is the one the coherences are stated
   at, by `Stacks.Gysin.mapDerivedCategoryHomologyIso_eq` and
   `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`.
3. `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision_app` at the excision datum
   `(S₁, S₁', L, foldZeroIso)` turns what is left into `b`, the classical excision for `S₁`, and
   `b'` inverted.  Its three sides are the written-out transformations
   `Stacks.DerivedIndexing.derivedExcisionSingleHomologyNatTrans`,
   `Stacks.DerivedIndexing.postCompSingleHomologyNatTrans` and
   `Stacks.DerivedIndexing.preCompSingleHomologyNatTrans`, which agree with the factors of step 1
   **by `rfl`**.
4. `Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app` moves the classical
   excision from `S₁` to `S₂`, where it is
   `Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso` by
   definition.  Its hypothesis is `supportedSectionsOnClosedComp_foldZero_compat`, which is
   `Stacks.Perfect.SupportPushExcision.foldZeroIso_hom_app` with `κ'` cancelled.
5. `Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_bridge` says `β = b ≫ Rⁿκ` on each space, so
   the two bridges and the two transports of `κ` assemble into the two copies of
   `supportCohomologyOnIso` the statement conjugates by.

**Why steps 3 and 4 are joined at an abstract excision datum.**  The two coherences are stated in
different files, so the instance arguments their statements carry for the shared factor
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₁ L (L ⋙ S₁') e₁ n ≪≫
Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₁' n` are two different, merely
definitionally equal, terms.  Unifying them over the concrete functors of this file exhausts the
heartbeat budget at `whnf`, in either direction.
`transportedClassicalExcision_eq_derivedExcision_app` performs that unification once, with
abstract categories and functors, where it is cheap; the concrete proof applies the result.

**No other step is ascribed a type.**  Each intermediate fact is a `have` whose type is *inferred*
from the lemma applied, and the assembling is done by `private` helpers at a variable category with
the objects implicit and the morphisms explicit, applied with a single `exact`.  This is the house
style of `StacksDraft.Topology.Sheaves.Cohomology.SupportedComplexes`
`.ExcisionDerivedClassicalBridge`, and here it is also what keeps the elaboration affordable.  For
the same reason `rw` is unusable throughout: `(w ⋙ P).mapHomotopyCategory c` and
`w.mapHomotopyCategory c ⋙ P.mapHomotopyCategory c` are definitionally but not syntactically
equal, so the motive `rw` builds is not type-correct, `CategoryTheory.Functor.map_comp` included.

**The closedness of `T'` is the natural proof term inside the proof, not the hypothesis `hTW`.**
The statement must use `hTW`, because `Stacks.Gysin.supportCohomologyOnIso` on the open subscheme
does; but the instances the four composites need are found only when the subset is spelled
`Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage f T` rather than `W.ι ⁻¹' T`, and then
the natural closedness proof is `Stacks.Cohomology.SupportedComplexes`
`.isClosed_closedSubsetPreimage`.  The two are interchangeable by proof irrelevance, which is what
makes the final `exact` typecheck.

**Right-exactness of the two direct images is carried, not assumed**, exactly as in
`Stacks.Perfect.SupportPushExcision`: `IsClosed T` is not a class, so
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits` is a `let` in the
proof and an instance-implicit hypothesis of the degree-zero compatibility.

**No `@[stacks ...]` attribute is attached**: every statement here identifies two of the project's
own constructions and none is the statement of a tag, exactly as recorded for
`Stacks.Gysin.supportCohomologyPullbackIso` itself.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.4 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedOpenImmersion (derivedPullbackOpenImmersionIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open Stacks.Perfect.SupportPushExcision (foldZeroIso
  derivedSupportedPushforwardPullbackIso
  derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision
  isRightDerivedFunctor_postcompose_closedPushforward
  isRightDerivedFunctor_derivedSupportedPushforward_comp_pullback
  isRightDerivedFunctor_pullback_comp_derivedSupportedPushforward)
open StacksDraft.DerivedCategoryHomology (mapDerivedCategoryHomologyIso)

universe wA vA uA wA' vA' uA' u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.openImmersionModulePullback_preservesHomology
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback
attribute [local instance]
  Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
attribute [local instance] pushforward_preservesFiniteLimits
attribute [local instance] isRightDerivedFunctor_postcompose_closedPushforward
attribute [local instance] isRightDerivedFunctor_derivedSupportedPushforward_comp_pullback
attribute [local instance] isRightDerivedFunctor_pullback_comp_derivedSupportedPushforward

/-! ### The chases -/

/-- A functor applied to two equal morphisms.  Stated separately because the morphisms are not
spelled out by the caller. -/
private theorem map_congr {E D : Type*} [Category* E] [Category* D] (Φ : E ⥤ D)
    {a b : E} {g h : a ⟶ b} (e : g = h) : Φ.map g = Φ.map h :=
  congrArg Φ.map e


/-- A functor applied to a morphism cancelled against the leading factor of a composite.  Stated
at arbitrary categories with the objects implicit and the morphisms explicit, so that it applies
by `exact` across the definitionally equal spellings of a derived functor. -/
private theorem map_cancel_inv {E D : Type*} [Category* E] [Category* D] (Φ : E ⥤ D)
    {a b c : E} (u : a ⟶ b) (v : b ⟶ a) (x : a ⟶ c)
    (h : u ≫ v = CategoryStruct.id a) : Φ.map u ≫ Φ.map (v ≫ x) = Φ.map x := by
  rw [← Φ.map_comp, ← Category.assoc, h, Category.id_comp]

/-- The chase behind `supportedSectionsOnClosedComp_foldZero_compat`: the degree-zero excision for
the composites is the degreewise one with an isomorphism appended, so appending its inverse
recovers the degreewise one.  Stated at an arbitrary category with the objects implicit and the
morphisms explicit. -/
private theorem kappa_square_chase {D : Type*} [Category* D] {a b c d : D}
    (u : a ⟶ b) (v : b ⟶ c) (i : c ⟶ d) (h : d ⟶ c) (g : a ⟶ d)
    (hg : g = u ≫ v ≫ i) (hih : i ≫ h = CategoryStruct.id c) : u ≫ v = g ≫ h := by
  simp [hg, hih]

/-- The chase of step 1: inside the functor `Hn` the leading factor cancels against the first
factor of the excision (`ha`), what is left of the excision is the derived comparison `exc`, and
the trailing two factors merge by `hm`.  Stated at arbitrary categories with the objects implicit
and the morphisms explicit. -/
private theorem fold_excision_inner {E D : Type*} [Category* E] [Category* D] (Hn : E ⥤ D)
    {u t p y z : E} {o : D} (a : u ⟶ t) (dh : t ⟶ u) (b : t ⟶ y) (exc : u ⟶ p) (dd : p ⟶ y)
    (c : y ⟶ z) (m : p ⟶ z) (vi : o ⟶ Hn.obj u) (lhs : o ⟶ Hn.obj z)
    (hlhs : lhs = vi ≫ Hn.map (a ≫ b ≫ c)) (hb : b = dh ≫ exc ≫ dd)
    (ha : a ≫ dh = CategoryStruct.id u) (hm : dd ≫ c = m) :
    lhs = vi ≫ Hn.map exc ≫ Hn.map m := by
  rw [hlhs, ← Hn.map_comp, ← hm, hb]
  simp only [Category.assoc, reassoc_of% ha]

/-- A cancellation read at a re-spelling of its first factor.  Stated at an arbitrary category
with the objects implicit and the morphisms explicit. -/
private theorem respell_cancel {D : Type*} [Category* D] {a b : D}
    (vi vi' : a ⟶ b) (vh : b ⟶ a) (h : vi = vi')
    (hc : vi' ≫ vh = CategoryStruct.id a) : vi ≫ vh = CategoryStruct.id a := by
  rwa [h]

/-- The chase joining steps 3 and 4: the right edge of the derived/classical square, followed by
the transport of the degree-zero identification, is the left edge followed by the classical
excision at the second spelling.  Stated at an arbitrary category with the objects implicit and
the morphisms explicit. -/
private theorem combine_chase {D : Type*} [Category* D] {o₁ o₂ p q r r₂ s s₂ : D}
    (ex : o₁ ⟶ p) (pc : p ⟶ q) (bh : q ⟶ r) (rk : r ⟶ r₂) (pcomp : o₁ ⟶ o₂)
    (lb : o₂ ⟶ s) (c1 : s ⟶ r) (lrk : s ⟶ s₂) (c2 : s₂ ⟶ r₂) (lbv : o₂ ⟶ s₂)
    (h3 : ex ≫ pc ≫ bh = pcomp ≫ lb ≫ c1) (h4 : lrk ≫ c2 = c1 ≫ rk)
    (hlb : lbv = lb ≫ lrk) : ex ≫ pc ≫ bh ≫ rk = pcomp ≫ lbv ≫ c2 := by
  rw [hlb]
  simp only [Category.assoc, reassoc_of% h3, h4]

/-- The final chase: the two verticals of the joined square are invertible, so the left-hand side
is the right-hand side conjugated by them.  Stated at an arbitrary category with the objects
implicit and the morphisms explicit; `hbb`, `hlbeta` and `hc2` are the three re-spellings the
statement of the main result asks for. -/
private theorem final_chase {D : Type*} [Category* D] {o₁ o₂ p q r₂ s₂ : D}
    (vi : o₂ ⟶ o₁) (pcomp : o₁ ⟶ o₂) (ex : o₁ ⟶ p) (pc : p ⟶ q) (bb bb' : q ⟶ r₂)
    (bi : r₂ ⟶ q) (lbv lbeta : o₂ ⟶ s₂) (c2 c2' : s₂ ⟶ r₂) (lhs : o₂ ⟶ q)
    (hlhs : lhs = vi ≫ ex ≫ pc) (hgen : ex ≫ pc ≫ bb = pcomp ≫ lbv ≫ c2)
    (hbb : bb' = bb) (hbi : bb' ≫ bi = CategoryStruct.id q)
    (hvi : vi ≫ pcomp = CategoryStruct.id o₂) (hlbeta : lbeta = lbv) (hc2 : c2 = c2') :
    lhs = lbeta ≫ c2' ≫ bi := by
  subst hbb hlbeta hc2 hlhs
  calc vi ≫ ex ≫ pc = vi ≫ ex ≫ pc ≫ bb' ≫ bi := by rw [hbi, Category.comp_id]
    _ = lbeta ≫ c2 ≫ bi := by simp only [reassoc_of% hgen, reassoc_of% hvi]

/-! ### The two coherences, pasted at an abstract excision datum -/

/-- **The derived/classical square and the transport of the degree-zero identification, pasted.**
For two excision data `(S₁, S₁', L, e₁)` and `(S₂, S₂', L, e₂)` of
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge`
related by isomorphisms `κ : S₁ ≅ S₂` and `κ' : S₁' ≅ S₂'` of the degree-zero functors carrying
`e₁` to `e₂`, the degree-`n` cohomology of the derived excision of `e₁`, followed by the
derived/classical bridge for `S₁'` and `CategoryTheory.NatTrans.rightDerived κ'.hom n`, is `L`
pulled out of the cohomology, followed by `L` applied to the bridge for `S₁` and
`CategoryTheory.NatTrans.rightDerived κ.hom n`, followed by the **classical** excision of `e₂`.

This is `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision_app` followed by
`Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app`.  It is stated at an
abstract datum because the shared factor — the classical excision of `e₁` — carries different
instance arguments in those two, and identifying them over concrete functors is unaffordable; see
the module docstring. -/
theorem transportedClassicalExcision_eq_derivedExcision_app
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory.{wA} A]
    {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
    [HasDerivedCategory.{wA'} A']
    (S₁ : A ⥤ A) [S₁.Additive] (S₂ : A ⥤ A) [S₂.Additive] (κ : S₁ ≅ S₂)
    (S₁' : A' ⥤ A') [S₁'.Additive] (S₂' : A' ⥤ A') [S₂'.Additive] (κ' : S₁' ≅ S₂')
    (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects]
    (e₁ : S₁ ⋙ L ≅ L ⋙ S₁') (e₂ : S₂ ⋙ L ≅ L ⋙ S₂')
    (RS₁ : DerivedCategory A ⥤ DerivedCategory A)
    (α₁ : S₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RS₁)
    [RS₁.IsRightDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (RS₁' : DerivedCategory A' ⥤ DerivedCategory A')
    (α₁' : S₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RS₁')
    [RS₁'.IsRightDerivedFunctor α₁' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    [(RS₁ ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.postcomposeUnit S₁ L RS₁ α₁)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [(L.mapDerivedCategory ⋙ RS₁').IsRightDerivedFunctor
      (Stacks.DerivedFunctor.precomposeUnit L S₁' RS₁' α₁')
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hκ : Functor.whiskerRight κ.hom L ≫ e₂.hom = e₁.hom ≫ Functor.whiskerLeft L κ'.hom)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (hres' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (n : ℕ) (X : A) :
    (Stacks.DerivedIndexing.derivedExcisionSingleHomologyNatTrans S₁ S₁' L e₁ RS₁ α₁ RS₁' α₁'
          (n : ℤ)).app X ≫
        (Stacks.DerivedIndexing.preCompSingleHomologyNatTrans L RS₁' (n : ℤ)).app X ≫
          ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S₁' RS₁' α₁'
                hres' n).hom.app (L.obj X) ≫
            (NatTrans.rightDerived κ'.hom n).app (L.obj X)) =
      (Stacks.DerivedIndexing.postCompSingleHomologyNatTrans L RS₁ (n : ℤ)).app X ≫
        L.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S₁ RS₁ α₁
              hres n).hom.app X ≫
            (NatTrans.rightDerived κ.hom n).app X) ≫
          (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₂ L (L ⋙ S₂') e₂ n ≪≫
            Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₂' n).hom.app X :=
  combine_chase _ _ _ _ _ _ _ _ _ _
    (Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision_app S₁ S₁' L e₁ RS₁ α₁ RS₁' α₁'
      hres hres' n X)
    (Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app S₁ S₂ κ S₁' S₂' κ' L
      e₁ e₂ hκ n X)
    (L.map_comp _ _)

/-! ### The two degree-zero excisions correspond -/

/-- **The degree-zero excision for the composites and the degree-zero excision for the subsheaf of
supported sections correspond under the identification of [Stacks, Tag 0G6N].**  For an open
immersion of ringed spaces `f : X' ⟶ X`, a closed `Z ⊆ X` and `Z' = f^{-1}(Z)`, let
`κ : H_Z^{on Z} ⋙ i_* ≅ H_Z` be
`Stacks.SheafOfModules.SupportedSections`
`.supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` and `κ'` its counterpart on `X'`.
Then whiskering `κ` into
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` and whiskering `κ'` into
`Stacks.Perfect.SupportPushExcision.foldZeroIso` give the same comparison
`(H_Z^{on Z} ⋙ i_*) ⋙ f^* ⟶ f^* ⋙ H_{Z'}`.

This is `Stacks.Perfect.SupportPushExcision.foldZeroIso_hom_app` with the trailing copy of `κ'`
cancelled, and it is the hypothesis `hκ` of
`Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app`, which is what carries the
classical degree-`n` excision between the two spellings.

Right-exactness of the two direct images is an instance-implicit hypothesis rather than a `let`
because this equation is only ever consumed inside a proof that already has it; it is
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits` at `hZ` and at
`hZ'`. -/
theorem supportedSectionsOnClosedComp_foldZero_compat {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    [SheafedSpace.IsOpenImmersion f] (Z : Set X.carrier) (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
    [PreservesFiniteColimits
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] :
    Functor.whiskerRight
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom
          (modulePullback f) ≫
        (supportedSectionsPullbackNatIso f Z).hom =
      (foldZeroIso f Z hZ hZ').hom ≫
        Functor.whiskerLeft (modulePullback f)
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
            (closedSubsetPreimage f Z) hZ').hom := by
  refine NatTrans.ext (funext fun G => ?_)
  exact kappa_square_chase _ _ _ _ _
    (Stacks.Perfect.SupportPushExcision.foldZeroIso_hom_app f Z hZ hZ' G)
    ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
      (closedSubsetPreimage f Z) hZ').inv_hom_id_app ((modulePullback f).obj G))

/-- **The classical excision for the subsheaf of supported sections is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso`**, which is by
definition `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` at the degree-zero excision
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso`.  Stated so that the
spelling `transportedClassicalExcision_eq_derivedExcision_app` produces is exchanged for the
library's name before it meets the goal. -/
private theorem classical_respell {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    [SheafedSpace.IsOpenImmersion f] (Z : Set X.carrier) (n : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (supportedSectionsFunctor X Z)
          (modulePullback f)
          (modulePullback f ⋙ supportedSectionsFunctor X' (closedSubsetPreimage f Z))
          (supportedSectionsPullbackNatIso f Z) n ≪≫
        Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (modulePullback f)
          (supportedSectionsFunctor X' (closedSubsetPreimage f Z)) n).hom.app F =
      (supportedSectionsRightDerivedPullbackNatIso f Z n).hom.app F := rfl

/-! ### The derived excision in degree `n` is the classical excision -/

/-- **The derived excision of [Stacks, Tag 0G78], read on degree-`n` cohomology sheaves along the
ringed-space inclusion of an open subscheme, is the classical excision for the right derived
functors of the sections with support, conjugated by `Stacks.Gysin.supportCohomologyOnIso`.**

For `W ⊆ Y` open, `T ⊆ Y` closed, `T' = W ∩ T` and `f : W ⟶ Y` the inclusion of `W` as a ringed
space,

`Θ_ℱ = f^*(β_ℱ) ≫ (Rⁿ H_T(ℱ)|_W ≅ Rⁿ H_{T'}(ℱ|_W)) ≫ (β'_{f^*ℱ})⁻¹`,

where `Θ` is `Stacks.Gysin.supportCohomologyPullbackIso`, the derived excision of
[Stacks, Tag 0G78] in degree `n`; the middle factor is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso`, the classical
excision built from [Stacks, Tag 015Z] out of the degree-zero excision
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso`; and `β`, `β'` are
`Stacks.Gysin.supportCohomologyOnIso` on `Y` and on `W`, the identification of the cohomology
sheaf of `i_* R𝓗_T(ℱ[0])` with `Rⁿ H_T(ℱ)`.

This is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` record as the missing
coherence between the derived excision and the abelian one, in the
`RingedSpaceModuleAdjunction.modulePullback` spelling of the restriction: the one statement the
square of [Stacks, Tag 0G87] needs from the abelian model.  Its five steps are listed in the
module docstring. -/
theorem supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback
    {Y : Scheme.{u}} (W : Y.Opens) (T : Set Y) (hT : IsClosed T)
    (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℕ) (F : Y.Modules) :
    (supportCohomologyPullbackIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
        T hT (n : ℤ) F).hom =
      (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).map
          ((supportCohomologyOnIso Y T hT n).hom.app F) ≫
        (supportedSectionsRightDerivedPullbackNatIso
            (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T n).hom.app F ≫
          (supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
            ((modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F) := by
  let := pushforward_preservesFiniteColimits Y.toRingedSpace T hT
  let := pushforward_preservesFiniteColimits
    (Y.toRingedSpace.restrict W.isOpenEmbedding)
    (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
    (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT)
  -- step 1: the left-hand side, by `rfl`
  have h1 : (supportCohomologyPullbackIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
        T hT (n : ℤ) F).hom =
      (mapDerivedCategoryHomologyIso
            (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)) (n : ℤ)).inv.app
          ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F)) ≫
        (DerivedCategory.homologyFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing
              (Y.toRingedSpace.restrict W.isOpenEmbedding))) (n : ℤ)).map
          ((derivedPullbackOpenImmersionIso
                (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv.app
              ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
                ((DerivedCategory.singleFunctor
                  (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F)) ≫
            (derivedSupportedPushforwardPullbackIso
                (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT).hom.app
              ((DerivedCategory.singleFunctor
                (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F) ≫
            (derivedSupportedPushforward (Y.toRingedSpace.restrict W.isOpenEmbedding)
                (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
                (isClosed_closedSubsetPreimage
                  (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT)).map
              ((derivedPullbackOpenImmersionIso
                    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).hom.app
                  ((DerivedCategory.singleFunctor
                    (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F) ≫
                ((modulePullback (Y.toRingedSpace.ofRestrict
                  W.isOpenEmbedding)).mapDerivedCategorySingleFunctor 0).hom.app F)) := rfl
  -- the derived excision of 0G78 is the derived excision of the composites
  have hB := derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision
      (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT
      (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT)
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F)
  have hm := map_cancel_inv
    (derivedSupportedPushforward (Y.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
      (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
    ((derivedPullbackOpenImmersionIso
        (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv.app
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F))
    ((derivedPullbackOpenImmersionIso
        (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).hom.app
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F))
    (((modulePullback (Y.toRingedSpace.ofRestrict
      W.isOpenEmbedding)).mapDerivedCategorySingleFunctor 0).hom.app F)
    ((derivedPullbackOpenImmersionIso
        (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv_hom_id_app
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F))
  have hI := fold_excision_inner
    (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing
        (Y.toRingedSpace.restrict W.isOpenEmbedding))) (n : ℤ))
    _ _ _ _ _ _ _ _ _ h1 hB
    ((derivedPullbackOpenImmersionIso
        (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).inv_hom_id_app
      ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F)))
    hm
  -- step 2: the copy of "an exact functor commutes with `Hⁿ`" the coherences are stated at
  have h2 := congrArg (fun i => i.inv.app
      ((derivedSupportedPushforward Y.toRingedSpace T hT).obj
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj F)))
    ((mapDerivedCategoryHomologyIso_eq
        (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)) (n : ℤ)).trans
      (Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso
        (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)) (n : ℤ)).symm)
  have hvi := respell_cancel _ _ _ h2 (Iso.inv_hom_id_app _ _)
  -- steps 3 and 4: the derived/classical square, and the classical excision across 0G6N
  have hgen := transportedClassicalExcision_eq_derivedExcision_app
    (supportedSectionsOnClosedFunctor Y.toRingedSpace T hT ⋙
      modulePushforward (closedSubsetInclusion Y.toRingedSpace T))
    (supportedSectionsFunctor Y.toRingedSpace T)
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso Y.toRingedSpace T hT)
    (supportedSectionsOnClosedFunctor (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
        (isClosed_closedSubsetPreimage
          (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT) ⋙
      modulePushforward (closedSubsetInclusion (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)))
    (supportedSectionsFunctor (Y.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T))
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso
      (Y.toRingedSpace.restrict W.isOpenEmbedding)
      (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
      (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
    (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding))
    (foldZeroIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT
      (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
    (supportedSectionsPullbackNatIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
    (derivedSupportedSectionsOnClosed Y.toRingedSpace T hT ⋙
      (modulePushforward (closedSubsetInclusion Y.toRingedSpace T)).mapDerivedCategory)
    (Stacks.DerivedFunctor.postcomposeUnit
      (supportedSectionsOnClosedFunctor Y.toRingedSpace T hT)
      (modulePushforward (closedSubsetInclusion Y.toRingedSpace T))
      (derivedSupportedSectionsOnClosed Y.toRingedSpace T hT)
      (derivedSupportedSectionsOnClosedUnit Y.toRingedSpace T hT))
    (derivedSupportedSectionsOnClosed (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
        (isClosed_closedSubsetPreimage
          (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT) ⋙
      (modulePushforward (closedSubsetInclusion (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage
          (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T))).mapDerivedCategory)
    (Stacks.DerivedFunctor.postcomposeUnit
      (supportedSectionsOnClosedFunctor (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
        (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
      (modulePushforward (closedSubsetInclusion (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)))
      (derivedSupportedSectionsOnClosed (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
        (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
      (derivedSupportedSectionsOnClosedUnit (Y.toRingedSpace.restrict W.isOpenEmbedding)
        (closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T)
        (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT)))
    (supportedSectionsOnClosedComp_foldZero_compat
      (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT
      (isClosed_closedSubsetPreimage (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT))
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives n F
  -- step 5: the two bridges and the two transports of `κ` are `β` and `β'`
  have hC := supportCohomologyOnIso_hom_app_eq_bridge Y T hT n F
  have hC' := supportCohomologyOnIso_hom_app_eq_bridge W.toScheme (W.ι ⁻¹' T) hTW n
    ((modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).obj F)
  exact final_chase _ _ _ _ _ _ _ _ _ _ _ _ hI hgen hC' (Iso.hom_inv_id_app _ _) hvi
    (congrArg (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).map hC)
    (classical_respell (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T n F)

end Stacks.Gysin

end
