module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.AffineVanishingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Eventual vanishing of Ext from a finite locally free module

Let `X` be a quasi-compact and quasi-separated scheme and let `E` be an object of
`D^b_{QCoh}(𝒪_X)`, that is, a cohomologically bounded object of `D(𝒪_X)` all of whose cohomology
sheaves are quasi-coherent. Then `Ext^n_{D(𝒪_X)}(ℰ, E) = 0` for every finite locally free
`𝒪_X`-module `ℰ` and every sufficiently large `n`, with a bound that does not depend on `ℰ`.
This is [Stacks, Tag 08EF].

The Ext group is read as the group of morphisms `ℰ ⟶ E⟦n⟧` in `D(𝒪_X)`, with `ℰ` placed in
cohomological degree zero by `DerivedCategory.singleFunctor`, and its vanishing as
subsingletonness of that group. Being bounded with quasi-coherent cohomology is
`DerivedCategoryB.derivedCategoryBBounded (SheafOfModules.isQuasicoherent X.ringCatSheaf)`.

## Main definitions

* `Stacks.DerivedQCoh.HasUniformExtBound` and `Stacks.DerivedQCoh.HasUniformExtBounds`: the
  conclusion of the tag for one object of `D(𝒪_X)`, and for all bounded quasi-coherent objects
  at once, the latter being what the induction runs on.

## Main results

* `Stacks.DerivedQCoh.exists_pos_subsingleton_hom_singleFunctor_of_isFiniteLocallyFree` is the
  tag.
* `Stacks.DerivedQCoh.hasUniformExtBound_spec` is the affine case, on the spectrum of a ring.
* `Stacks.DerivedQCoh.subsingleton_hom_of_cover` is the Mayer--Vietoris step: a morphism group
  in degree `n + 1` over a scheme covered by two opens vanishes once the corresponding groups
  vanish in degree `n + 1` over each of the two opens and in degree `n` over their
  intersection.
* `Stacks.DerivedQCoh.mapDerivedCategoryCongr`, `...Comp` and `...Id`: the functor induced on
  unbounded derived categories by an exact functor is compatible with isomorphisms,
  composition and the identity.

## Implementation notes

**The proof.** Mayer--Vietoris for morphisms in the derived category ([Stacks, Tag 08BW]) says
that if `Y = U ∪ V` and the conclusion holds over `U`, over `V` and over `U ∩ V` with bound
`n₀`, then it holds over `Y` with bound `n₀ + 1`. The induction principle for quasi-compact
opens of a quasi-separated scheme ([Stacks, Tag 08DR]) therefore reduces the tag to the affine
case. On `Spec R` the derived sheafification–sections adjunction of [Stacks, Tag 06Z0]
identifies `Hom_{D(𝒪_X)}(ℰ, E⟦n⟧)` with `Hom_{D(R)}(P, RΓ(X, E)⟦n⟧)`, where `ℰ = P̃` for a
finite projective `R`-module `P`; that group vanishes for `n` beyond the upper bound of
`RΓ(X, E)`, because `P` is projective and sits in degree zero.

**The upper bound on `RΓ`.** That `RΓ(Spec R, -)` does not raise the upper bound of a complex
with quasi-coherent cohomology is [Stacks, Tag 08D4] at `N = 1`, whose hypothesis is affine
Serre vanishing; it is *not* read off the degreewise comparison
`Hⁿ(RΓ(X, E)) ≅ Γ(X, Hⁿ(E))` of [Stacks, Tag 06Z0], which is stated at the locally small
derived category of `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` while
[Stacks, Tag 08BW] is stated at `CategoryTheory.HasDerivedCategory.standard`, and
`HasDerivedCategory` carries the localized category as data. Everything here is at the standard
model, installed with a raised priority because the import closure carries the locally small
instances as global ones and at equal priority instance search picks those for the sheaf
categories while picking `standard` for `ModuleCat`.

**Two spellings of restriction to an open.** [Stacks, Tag 08BW] is stated for the restriction
functor `ExtensionByZeroModules.jStar` of a sheaf of rings on a topological space, while the
induction needs restriction along the inclusion of an open subscheme,
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The two are *equal*, not merely isomorphic
— both are the pushforward along the image functor on opens, along the identity morphism of the
restricted sheaf of rings — which is `Stacks.DerivedQCoh.jStar_eq_restrictFunctor`. The
exactness hypotheses of `Stacks.DerivedQCoh.mapDerivedCategory_congr` are explicit arguments
rather than instances, so that the equality can be lifted to the derived categories without
putting a statement about `jStar` into the instance cache, where it would be tried, by
unfolding, against every statement about `restrictFunctor`.

## References

* [Stacks Project, Tag 08EF](https://stacks.math.columbia.edu/tag/08EF)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe u u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-! ### `mapDerivedCategory` of an isomorphism, a composite and the identity -/

section MapDerivedCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- Isomorphic exact functors induce isomorphic functors on the unbounded derived
categories. -/
def mapDerivedCategoryCongr (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- A composite of exact functors induces the composite of the functors it induces on the
unbounded derived categories. -/
def mapDerivedCategoryComp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm)

/-- Equal exact functors induce the same functor on the unbounded derived categories. The
exactness hypotheses are explicit arguments: the two functors are equal but not syntactically
so, and keeping them out of the instance cache is what lets the two sides be compared. -/
theorem mapDerivedCategory_congr {F G : C₁ ⥤ C₂} (h : F = G)
    (hF : F.Additive) (hF₁ : PreservesFiniteLimits F) (hF₂ : PreservesFiniteColimits F)
    (hG : G.Additive) (hG₁ : PreservesFiniteLimits G) (hG₂ : PreservesFiniteColimits G) :
    @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ F hF hF₁ hF₂ =
      @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ G hG hG₁ hG₂ := by
  subst h
  rfl

end MapDerivedCategory

/-! ### Restriction of the unbounded derived category along an open immersion -/

/-- Alias of `Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor`. -/
alias preservesFiniteLimits_restrictFunctor :=
    Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor

attribute [local instance] preservesFiniteLimits_restrictFunctor

/-- Restriction of modules along an open immersion is right exact, being a left adjoint. -/
theorem preservesFiniteColimits_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteColimits (Scheme.Modules.restrictFunctor f) :=
  inferInstance

/-- Restriction of modules along an open immersion is additive. -/
theorem additive_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Additive :=
  inferInstance

section Restriction

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The restriction of a finite locally free sheaf of modules along an open immersion is
finite locally free. -/
theorem isFiniteLocallyFree_restrict (F : Y.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor f).obj F) :=
  (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators _).1
    (((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators F).2 hF).restrict f)

/-- Restriction along an open immersion commutes with the cohomology of the unbounded derived
category. -/
abbrev derivedRestrictHomologyIso (n : ℤ) :
    derivedRestrict f ⋙ DerivedCategory.homologyFunctor X.Modules n ≅
      DerivedCategory.homologyFunctor Y.Modules n ⋙ Scheme.Modules.restrictFunctor f :=
  (Scheme.Modules.restrictFunctor f).mapDerivedCategoryHomologyIso n

/-- The restriction of a bounded complex with quasi-coherent cohomology along an open
immersion is again bounded with quasi-coherent cohomology. -/
theorem derivedCategoryBBounded_derivedRestrict (E : DerivedCategory Y.Modules)
    (hE : DerivedCategoryB.derivedCategoryBBounded
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryBBounded
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((derivedRestrict f).obj E) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hq⟩ := hE
  refine ⟨⟨⟨a, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, fun i => ?_⟩
  · exact ((Scheme.Modules.restrictFunctor f).map_isZero (ha i hi)).of_iso
      ((derivedRestrictHomologyIso f i).app E)
  · exact ((Scheme.Modules.restrictFunctor f).map_isZero (hb i hi)).of_iso
      ((derivedRestrictHomologyIso f i).app E)
  · let : ((DerivedCategory.homologyFunctor Y.Modules i).obj E).IsQuasicoherent := hq i
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((derivedRestrictHomologyIso f i).app E).symm
      (show ((Scheme.Modules.restrictFunctor f).obj
        ((DerivedCategory.homologyFunctor Y.Modules i).obj E)).IsQuasicoherent from
          inferInstance)

end Restriction


/-! ### The uniform bound as a property of a scheme and a complex -/

/-- `HasUniformExtBound X E` says that `Ext^n_{D(𝒪_X)}(ℰ, E)` vanishes for every finite locally
free `𝒪_X`-module `ℰ` and every `n` beyond some positive bound which does not depend on `ℰ`. -/
def HasUniformExtBound (X : Scheme.{u}) (E : DerivedCategory X.Modules) : Prop :=
  ∃ n₀ : ℤ, 0 < n₀ ∧
    ∀ F : X.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
      ∀ n : ℤ, n₀ ≤ n →
        Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ E⟦n⟧)

/-- Subsingletonness of a morphism group only depends on the isomorphism classes of its two
arguments. -/
theorem subsingleton_hom_of_iso {C : Type*} [Category* C] {A B A' B' : C}
    (e : A ≅ A') (e' : B ≅ B') (h : Subsingleton (A' ⟶ B')) : Subsingleton (A ⟶ B) :=
  ⟨fun _f _g => (e.homCongr e').injective (h.elim _ _)⟩

/-! ### Transport along an isomorphism of schemes -/

section Transport

variable {A B : Scheme.{u}} (e : A ≅ B)

/-- Restricting along an isomorphism of schemes and then along its inverse is the identity on
the unbounded derived category. -/
def derivedRestrictCompIso :
    derivedRestrict e.inv ⋙ derivedRestrict e.hom ≅ 𝟭 (DerivedCategory A.Modules) :=
  (mapDerivedCategoryComp (Scheme.Modules.restrictFunctor e.inv)
      (Scheme.Modules.restrictFunctor e.hom)).symm ≪≫
    mapDerivedCategoryCongr _ _
      ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
        Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId) ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A.Modules)

/-- Restriction along an isomorphism of schemes is faithful on the unbounded derived
category. -/
theorem derivedRestrict_faithful : (derivedRestrict e.inv).Faithful := by
  refine ⟨fun {M N a b} hab => ?_⟩
  set α := derivedRestrictCompIso e with hα
  have h : (derivedRestrict e.inv ⋙ derivedRestrict e.hom).map a =
      (derivedRestrict e.inv ⋙ derivedRestrict e.hom).map b :=
    congrArg (derivedRestrict e.hom).map hab
  let : IsIso (α.hom.app M) := (α.app M).isIso_hom
  refine (cancel_epi (α.hom.app M)).mp ?_
  exact (α.hom.naturality a).symm.trans
    ((congrArg (fun t => t ≫ α.hom.app N) h).trans (α.hom.naturality b))

/-- **Transport of the uniform bound along an isomorphism of schemes.** -/
theorem hasUniformExtBound_of_derivedRestrict (E : DerivedCategory A.Modules)
    (h : HasUniformExtBound B ((derivedRestrict e.inv).obj E)) : HasUniformExtBound A E := by
  obtain ⟨N, hN, h⟩ := h
  refine ⟨N, hN, fun F hF n hn => ?_⟩
  have hs := h ((Scheme.Modules.restrictFunctor e.inv).obj F)
    (isFiniteLocallyFree_restrict e.inv F hF) n hn
  have hs' : Subsingleton ((derivedRestrict e.inv).obj
      ((DerivedCategory.singleFunctor A.Modules 0).obj F) ⟶
      (derivedRestrict e.inv).obj (E⟦n⟧)) :=
    subsingleton_hom_of_iso
      (((Scheme.Modules.restrictFunctor e.inv).mapDerivedCategorySingleFunctor 0).app F)
      (((derivedRestrict e.inv).commShiftIso n).app E) hs
  let := derivedRestrict_faithful e
  exact ⟨fun a b => (derivedRestrict e.inv).map_injective (hs'.elim _ _)⟩

end Transport


/-! ### Mayer--Vietoris -/

section MayerVietoris

/-- The comparison `Γ(Y, U.ι(W)) ≅ Γ(U, W)` attached to the inclusion of an open subscheme is
the identity: the structure sheaf of the open subscheme is by definition the image presheaf. -/
theorem appIso_ι_inv {Y : Scheme.{u}} (U : Y.Opens) (W : U.toScheme.Opens) :
    (U.ι.appIso W).inv = 𝟙 _ := by
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- The restriction functor on modules used by the Mayer--Vietoris sequence of Stacks 08BW is
restriction along the inclusion of the open subscheme: both are the pushforward along the
image functor on opens, along the identity morphism of the restricted sheaf of rings. -/
theorem jStar_eq_restrictFunctor {Y : Scheme.{u}} (U : Y.Opens) :
    (ExtensionByZeroModules.jStar U Y.ringCatSheaf : Y.Modules ⥤ U.toScheme.Modules) =
      Scheme.Modules.restrictFunctor U.ι := by
  delta ExtensionByZeroModules.jStar Scheme.Modules.restrictFunctor
  congr 1
  ext W : 3
  simp only [appIso_ι_inv]
  rfl

/-- Restriction of modules to an open subspace is left exact. -/
theorem preservesFiniteLimits_jStar {Y : Scheme.{u}} (U : Y.Opens) :
    PreservesFiniteLimits (ExtensionByZeroModules.jStar U Y.ringCatSheaf) :=
  (jStar_eq_restrictFunctor U).symm ▸ preservesFiniteLimits_restrictFunctor U.ι

/-- Restriction of modules to an open subspace is right exact. -/
theorem preservesFiniteColimits_jStar {Y : Scheme.{u}} (U : Y.Opens) :
    PreservesFiniteColimits (ExtensionByZeroModules.jStar U Y.ringCatSheaf) :=
  (jStar_eq_restrictFunctor U).symm ▸ preservesFiniteColimits_restrictFunctor U.ι

/-- Restriction of modules to an open subspace is additive. -/
theorem additive_jStar {Y : Scheme.{u}} (U : Y.Opens) :
    (ExtensionByZeroModules.jStar U Y.ringCatSheaf).Additive :=
  (jStar_eq_restrictFunctor U).symm ▸ additive_restrictFunctor U.ι

/-- The restriction of unbounded derived modules of Stacks 08BW is the functor induced by
restriction along the inclusion of the open subscheme. -/
theorem derivedRestriction_eq {Y : Scheme.{u}} (U : Y.Opens) :
    Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf U = derivedRestrict U.ι :=
  mapDerivedCategory_congr (jStar_eq_restrictFunctor U) (additive_jStar U)
    (preservesFiniteLimits_jStar U) (preservesFiniteColimits_jStar U)
    (additive_restrictFunctor U.ι) (preservesFiniteLimits_restrictFunctor U.ι)
    (preservesFiniteColimits_restrictFunctor U.ι)

/-- The restriction of unbounded derived modules of Stacks 08BW agrees with restriction along
the inclusion of the open subscheme. -/
def derivedRestrictionIso {Y : Scheme.{u}} (U : Y.Opens) :
    Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf U ≅ derivedRestrict U.ι :=
  eqToIso (derivedRestriction_eq U)

/-- **Mayer--Vietoris for vanishing of a morphism group.** If `Y` is covered by two opens `U`
and `V` and the groups `Hom_U(A|_U, E|_U⟦n + 1⟧)`, `Hom_V(A|_V, E|_V⟦n + 1⟧)` and
`Hom_{U ∩ V}(A|_{U ∩ V}, E|_{U ∩ V}⟦n⟧)` all vanish, then `Hom_Y(A, E⟦n + 1⟧)` vanishes. -/
theorem subsingleton_hom_of_cover {Y : Scheme.{u}} (U V : Y.Opens) (hUV : U ⊔ V = ⊤)
    (A E : DerivedCategory Y.Modules) (n : ℤ)
    (hU : Subsingleton ((derivedRestrict U.ι).obj A ⟶ ((derivedRestrict U.ι).obj E)⟦n + 1⟧))
    (hV : Subsingleton ((derivedRestrict V.ι).obj A ⟶ ((derivedRestrict V.ι).obj E)⟦n + 1⟧))
    (hW : Subsingleton ((derivedRestrict (U ⊓ V).ι).obj A ⟶
      ((derivedRestrict (U ⊓ V).ι).obj E)⟦n⟧)) :
    Subsingleton (A ⟶ E⟦n + 1⟧) := by
  have key : ∀ (W : Y.Opens) (m : ℤ),
      Subsingleton ((derivedRestrict W.ι).obj A ⟶ ((derivedRestrict W.ι).obj E)⟦m⟧) →
      Subsingleton ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj A ⟶
        ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj E)⟦m⟧) :=
    fun W m => subsingleton_hom_of_iso ((derivedRestrictionIso W).app A)
      ((shiftFunctor _ m).mapIso ((derivedRestrictionIso W).app E))
  have hU' := key U _ hU
  have hV' := key V _ hV
  have hW' := key (U ⊓ V) _ hW
  obtain ⟨r, d, δ, hex⟩ :=
    Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence Y.ringCatSheaf U V hUV A E
  refine ⟨fun f g => ?_⟩
  obtain ⟨y, hy⟩ := ((hex n).2.2 f).mp (Prod.ext (hU'.elim _ _) (hV'.elim _ _))
  obtain ⟨z, hz⟩ := ((hex n).2.2 g).mp (Prod.ext (hU'.elim _ _) (hV'.elim _ _))
  rw [← hy, ← hz, hW'.elim y z]

end MayerVietoris


/-! ### The affine case -/

section Affine

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **Derived global sections on an affine scheme does not raise the upper bound of a complex
with quasi-coherent cohomology.** This is Stacks 08D4 at `N = 1`, the hypothesis being affine
Serre vanishing. -/
theorem isLE_derivedGlobalSectionsOver_obj [IsAffine X]
    (E : DerivedCategory X.Modules) (b : ℤ) (hE : E.IsLE b)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    ((derivedGlobalSectionsOver f).obj E).IsLE b := by
  have key := AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus
    X (AlgebraicGeometry.secsOver f) (AlgebraicGeometry.derSecs f)
    (AlgebraicGeometry.derSecsUnit f) 1
    (fun M hM p hp =>
      AlgebraicGeometry.isZero_rightDerivedPlus_gam f M hM p (by exact_mod_cast hp))
    E hcoh b hE
  rwa [show b + ((1 : ℕ) : ℤ) - 1 = b by ring] at key

/-- A finite locally free sheaf of modules is quasi-coherent: its local generators, having
invertible evaluation maps, present it locally with no relations at all. -/
theorem isQuasicoherent_of_isFiniteLocallyFree {Y : Scheme.{u}} (F : Y.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    F.IsQuasicoherent := by
  obtain ⟨q, hq, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  exact q.quasiCoherentData.isQuasicoherent

/-- On the spectrum of a ring, a finite locally free sheaf of modules is the sheaf associated
with a projective module. -/
theorem exists_projective_tilde_iso (R : CommRingCat.{u}) (F : (Spec R).Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    ∃ P : ModuleCat.{u} R, Module.Projective R P ∧
      Nonempty (AlgebraicGeometry.tilde P ≅ F) := by
  have hIso : IsIso F.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ F).mp (isQuasicoherent_of_isFiniteLocallyFree F hF)
  let eΓ : AlgebraicGeometry.tilde (AlgebraicGeometry.moduleSpecΓFunctor.obj F) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hIso
  refine ⟨AlgebraicGeometry.moduleSpecΓFunctor.obj F, ?_, ⟨eΓ⟩⟩
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraicGeometry.tilde (AlgebraicGeometry.moduleSpecΓFunctor.obj F)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso eΓ.symm
  exact ((Module.isFiniteLocallyFree_iff_finite_projective (R : Type u)
    (AlgebraicGeometry.moduleSpecΓFunctor.obj F)).mp
      ((tilde_isFiniteLocallyFree_iff (R : Type u)
        (AlgebraicGeometry.moduleSpecΓFunctor.obj F)).mp
        ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr h₁))).2

/-- Morphisms from a projective module placed in degree zero into the `n`-th shift of a complex
concentrated in degrees `≤ b` vanish as soon as `b < n`. -/
theorem subsingleton_hom_single_shift_of_projective {B : Type u} [CommRing B]
    (P : ModuleCat.{u} B) [CategoryTheory.Projective P]
    (M : DerivedCategory (ModuleCat.{u} B)) (b n : ℤ) [M.IsLE b] (hbn : b < n) :
    Subsingleton ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj P ⟶ M⟦n⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := M.exists_iso_Q_obj_of_isLE b
  have hK' :
      ((shiftFunctor (CochainComplex (ModuleCat.{u} B) ℤ) n).obj K).IsStrictlyLE (b - n) :=
    K.isStrictlyLE_shift b n (b - n) (by omega)
  let e₁ : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj P ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj P) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app P
  let e₂ : M⟦n⟧ ≅
      DerivedCategory.Q.obj ((shiftFunctor (CochainComplex (ModuleCat.{u} B) ℤ) n).obj K) :=
    (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) n).mapIso e ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm
  have key : ∀ g : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj P ⟶ M⟦n⟧,
      e₁.inv ≫ g ≫ e₂.hom = 0 := fun g =>
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective (e₁.inv ≫ g ≫ e₂.hom)
      (b - n) (by omega)
  refine ⟨fun g h => (cancel_mono e₂.hom).1 ((cancel_epi e₁.inv).1 ?_)⟩
  rw [key g, key h]

/-- **The affine case of Stacks 08EF**, on the spectrum of a ring. The derived
sheafification–sections adjunction of Stacks 06Z0 turns the Ext group into a morphism group in
`D(R)` out of a projective module placed in degree zero, and derived global sections of a
complex concentrated in degrees `≤ b` is again concentrated in degrees `≤ b`. -/
theorem hasUniformExtBound_spec (R : CommRingCat.{u}) (E : DerivedCategory (Spec R).Modules)
    (hE : DerivedCategoryB.derivedCategoryBBounded
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) E) :
    HasUniformExtBound (Spec R) E := by
  obtain ⟨⟨-, ⟨b, hb⟩⟩, hq⟩ := hE
  refine ⟨max 1 (b + 1), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun F hF n hn => ?_⟩
  have hbn : b < n := lt_of_lt_of_le (by omega) (le_trans (le_max_right 1 (b + 1)) hn)
  set Γ := AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec R))
  have hM : (Γ.obj E).IsLE b :=
    isLE_derivedGlobalSectionsOver_obj (𝟙 (Spec R)) E b
      ((DerivedCategory.isLE_iff E b).2 hb) hq
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_projective_tilde_iso R F hF
  let P0 := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj P
  let eSource : (AlgebraicGeometry.derivedTilde R ⋙
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).obj P0 ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj F :=
    (AlgebraicGeometry.derivedTildeCompι R).app P0 ≪≫
      ((AlgebraicGeometry.tilde.functor R).mapDerivedCategorySingleFunctor 0).app P ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso eP
  let adj := (AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction R).val
  let eShift : Γ.obj (E⟦n⟧) ≅ (Γ.obj E)⟦n⟧ := (Γ.commShiftIso n).app E
  refine ⟨fun g h => ?_⟩
  have hinj : adj.homEquiv P0 (E⟦n⟧) (eSource.hom ≫ g) ≫ eShift.hom =
      adj.homEquiv P0 (E⟦n⟧) (eSource.hom ≫ h) ≫ eShift.hom :=
    (subsingleton_hom_single_shift_of_projective P (Γ.obj E) b n hbn).elim _ _
  exact (cancel_epi eSource.hom).1 ((adj.homEquiv P0 (E⟦n⟧)).injective
    ((cancel_mono eShift.hom).1 hinj))

end Affine


/-! ### The induction on quasi-compact opens -/

section Induction

/-- The property, of a scheme, that every bounded complex with quasi-coherent cohomology on it
has a uniform Ext bound from finite locally free modules. -/
def HasUniformExtBounds (X : Scheme.{u}) : Prop :=
  ∀ E : DerivedCategory X.Modules, DerivedCategoryB.derivedCategoryBBounded
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) E → HasUniformExtBound X E

attribute [local instance] preservesFiniteLimits_restrictFunctor

/-- Having uniform Ext bounds is invariant under isomorphism of schemes. -/
theorem hasUniformExtBounds_of_iso {A B : Scheme.{u}} (e : A ≅ B) (h : HasUniformExtBounds B) :
    HasUniformExtBounds A := fun E hE =>
  hasUniformExtBound_of_derivedRestrict e E
    (h _ (derivedCategoryBBounded_derivedRestrict e.inv E hE))

/-- **Stacks 08EF on an affine scheme.** -/
theorem hasUniformExtBounds_of_isAffine (Z : Scheme.{u}) [IsAffine Z] :
    HasUniformExtBounds Z :=
  hasUniformExtBounds_of_iso Z.isoSpec (fun E hE => hasUniformExtBound_spec _ E hE)

/-- The uniform bound, read on the restriction of a single global finite locally free module to
an open subscheme. -/
theorem exists_bound_derivedRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (E : DerivedCategory Y.Modules) (h : HasUniformExtBound X ((derivedRestrict f).obj E)) :
    ∃ n₀ : ℤ, 0 < n₀ ∧
      ∀ F : Y.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
        ∀ n : ℤ, n₀ ≤ n →
          Subsingleton ((derivedRestrict f).obj
              ((DerivedCategory.singleFunctor Y.Modules 0).obj F) ⟶
            ((derivedRestrict f).obj E)⟦n⟧) := by
  obtain ⟨N, hN, h⟩ := h
  refine ⟨N, hN, fun F hF n hn => ?_⟩
  exact subsingleton_hom_of_iso
    (((Scheme.Modules.restrictFunctor f).mapDerivedCategorySingleFunctor 0).app F) (Iso.refl _)
    (h ((Scheme.Modules.restrictFunctor f).obj F) (isFiniteLocallyFree_restrict f F hF) n hn)

/-- An open of an open subscheme is isomorphic, as a scheme, to its image in the ambient
scheme. -/
def imageOpensIso {X : Scheme.{u}} (W : X.Opens) (U : W.toScheme.Opens) :
    U.toScheme ≅ (W.ι ''ᵁ U).toScheme :=
  (IsOpenImmersion.isoOfRangeEq (W.ι ''ᵁ U).ι (U.ι ≫ W.ι) (by simp [Set.range_comp])).symm

/-- **The Mayer--Vietoris step.** If the two opens `U` and `V` of a scheme, and their
intersection, have uniform Ext bounds, then so does their union: the Mayer--Vietoris sequence of
Stacks 08BW raises the bound by one. -/
theorem hasUniformExtBounds_sup {X : Scheme.{u}} (U V : X.Opens)
    (hU : HasUniformExtBounds U.toScheme) (hV : HasUniformExtBounds V.toScheme)
    (hUV : HasUniformExtBounds (U ⊓ V).toScheme) :
    HasUniformExtBounds (U ⊔ V).toScheme := by
  intro E hE
  set j := (U ⊔ V).ι with hj
  set U' : (U ⊔ V).toScheme.Opens := j ⁻¹ᵁ U with hU'def
  set V' : (U ⊔ V).toScheme.Opens := j ⁻¹ᵁ V with hV'def
  have hcover : U' ⊔ V' = ⊤ := by
    rw [hU'def, hV'def, ← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self _
  have hinf : U' ⊓ V' = j ⁻¹ᵁ (U ⊓ V) := (Scheme.Hom.preimage_inf j).symm
  have himg : ∀ W : X.Opens, W ≤ U ⊔ V → j ''ᵁ (j ⁻¹ᵁ W) = W := fun W hW => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  have step : ∀ (T : (U ⊔ V).toScheme.Opens) (W : X.Opens), j ''ᵁ T = W →
      HasUniformExtBounds W.toScheme → HasUniformExtBounds T.toScheme := fun T W h hW =>
    hasUniformExtBounds_of_iso
      (imageOpensIso (U ⊔ V) T ≪≫ eqToIso (congrArg Scheme.Opens.toScheme h)) hW
  have hU'b := step U' U (himg U le_sup_left) hU
  have hV'b := step V' V (himg V le_sup_right) hV
  have hWb := step (U' ⊓ V') (U ⊓ V)
    (by rw [hinf]; exact himg _ (inf_le_left.trans le_sup_left)) hUV
  obtain ⟨a, ha, hUa⟩ := exists_bound_derivedRestrict U'.ι E
    (hU'b _ (derivedCategoryBBounded_derivedRestrict U'.ι E hE))
  obtain ⟨b, hb, hVb⟩ := exists_bound_derivedRestrict V'.ι E
    (hV'b _ (derivedCategoryBBounded_derivedRestrict V'.ι E hE))
  obtain ⟨c, hc, hWc⟩ := exists_bound_derivedRestrict (U' ⊓ V').ι E
    (hWb _ (derivedCategoryBBounded_derivedRestrict (U' ⊓ V').ι E hE))
  refine ⟨max a (max b c) + 1, by omega, fun F hF n hn => ?_⟩
  have h := subsingleton_hom_of_cover U' V' hcover
    ((DerivedCategory.singleFunctor (U ⊔ V).toScheme.Modules 0).obj F) E (n - 1)
    (by simpa using hUa F hF (n - 1 + 1) (by omega))
    (by simpa using hVb F hF (n - 1 + 1) (by omega))
    (by simpa using hWc F hF (n - 1) (by omega))
  rwa [show n - 1 + 1 = n from by omega] at h

/-- Every quasi-compact open of a quasi-separated scheme has uniform Ext bounds: the induction
principle of Stacks 08DR reduces this to the affine case and the Mayer--Vietoris step. -/
theorem hasUniformExtBounds_of_isCompact {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) : HasUniformExtBounds W.toScheme :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (fun W => HasUniformExtBounds W.toScheme)
    (fun _ hV => have : IsAffine _ := hV; hasUniformExtBounds_of_isAffine _)
    (fun U V _ _ hU hV hUV => hasUniformExtBounds_sup U V hU hV hUV) W hW

end Induction


/-! ### Stacks 08EF -/

/-- **Stacks Project, Tag 08EF.** Let `X` be a quasi-compact and quasi-separated scheme and let
`E ∈ D^b_{QCoh}(𝒪_X)`. There exists an integer `n₀ > 0` such that
`Ext^n_{D(𝒪_X)}(ℰ, E) = 0` for every finite locally free `𝒪_X`-module `ℰ` and every `n ≥ n₀`.

The Ext group is the group of morphisms `ℰ ⟶ E⟦n⟧` in `D(𝒪_X)`, with `ℰ` placed in
cohomological degree zero, and its vanishing is subsingletonness of that group. -/
@[stacks 08EF]
theorem exists_pos_subsingleton_hom_singleFunctor_of_isFiniteLocallyFree
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryBBounded
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    ∃ n₀ : ℤ, 0 < n₀ ∧
      ∀ ℰ : X.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℰ →
        ∀ n : ℤ, n₀ ≤ n →
          Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj ℰ ⟶ E⟦n⟧) :=
  hasUniformExtBounds_of_iso X.topIso.symm
    (hasUniformExtBounds_of_isCompact ⊤ (by simpa using isCompact_univ (X := X))) E hE

end Stacks.DerivedQCoh

end
