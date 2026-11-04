module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compactifications induced on an open and on a closed subscheme

Let `f : X ⟶ Y` be a morphism of schemes and let `j : X ⟶ X̄` be a compactification of `X` over
`Y`, with structure morphism `f̄ : X̄ ⟶ Y`.

* For an open immersion `j_U : U ⟶ X` the composite `j ∘ j_U : U ⟶ X̄` is again an open
  immersion into a scheme proper over `Y`, so it is a compactification of `U` over `Y`.
* For a closed immersion `i : Z ⟶ X`, with `f` quasi-compact, the composite `j ∘ i` is a
  quasi-compact immersion; it factors as an open immersion `t : Z ⟶ Z̄` into its scheme-theoretic
  image followed by the closed immersion `ι : Z̄ ⟶ X̄`, and `Z̄` is proper over `Y`. So `t` is a
  compactification of `Z` over `Y`, and the square formed by `i`, `t`, `j` and `ι` is cartesian.

These are the compactifications through which the derived lower shriek functors of the
restrictions of `f` to an open and to its closed complement are computed in [Stacks, Tag 0GKP]
and [Stacks, Tag 0GKN].

On sheaves of `Λ`-modules on the small étale sites this file proves the two identifications those
computations rest on: extension by zero composes, `(j ∘ j_U)_! ≅ j_! ∘ j_{U!}`, and for the closed
immersion `j_! ∘ i_* ≅ ι_* ∘ t_!`.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.restrictOpen`: the compactification `j ∘ j_U` of `U`.
* `AlgebraicGeometry.CompactificationOf.restrictClosed`: the compactification of `Z` given by the
  scheme-theoretic image of `j ∘ i`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso`: `(j ∘ j_U)_! ≅ j_! ∘ j_{U!}`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso`: extension by zero along an
  étale morphism commutes with inverse image along an arbitrary morphism, for module coefficients
  ([Stacks, Tag 03S6]).
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageIso`:
  `j_! ∘ i_* ≅ ι_* ∘ t_!` for a cartesian square with `j`, `t` open immersions and `i`, `ι` closed
  immersions.
* `Stacks.EtaleCohomology.derivedLowerShriekRestrictOpenIso` and
  `Stacks.EtaleCohomology.derivedLowerShriekRestrictClosedIso`: `Rg_! = Rf_! ∘ Rj_{U!}` and
  `Rh_! = Rf_! ∘ Ri_*` on bounded below derived categories, for `g = f ∘ j_U` and `h = f ∘ i`
  with the induced compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictOpenIso` and
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictClosedIso`: the same on unbounded
  derived categories.

## Main results

* `AlgebraicGeometry.CompactificationOf.isPullback_restrictClosed`: the square of `i`, `t`, `j`,
  `ι` is cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace AlgebraicGeometry.CompactificationOf

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The structure morphism of a compactification restricts to `f` on the interior. -/
@[reassoc (attr := simp)]
lemma immersion_toBase (j : CompactificationOf (Over.mk f)) : j.immersion ≫ j.toBase = f :=
  Over.w j.obj.hom

/-! ### The compactification induced on an open -/

section Open

variable (j : CompactificationOf (Over.mk f)) {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]

/-- The compactification of an open `j_U : U ⟶ X` induced by a compactification `j : X ⟶ X̄`
over `Y`: the open immersion `j ∘ j_U : U ⟶ X̄`, into the same scheme proper over `Y`. -/
def restrictOpen : CompactificationOf (Over.mk (jU ≫ f)) :=
  ⟨StructuredArrow.mk (Y := j.obj.right)
      (Over.homMk (U := Over.mk (jU ≫ f)) (V := j.obj.right) (jU ≫ j.immersion)
        (by simp [Over.mk, CompactificationOf.immersion])),
    ⟨(inferInstance : IsOpenImmersion (jU ≫ j.immersion)), j.property.2⟩⟩

/-- The compactification induced on an open has the same ambient scheme. -/
@[simp]
lemma restrictOpen_space : (j.restrictOpen jU).space = j.space := rfl

/-- The open immersion of the compactification induced on an open is `j ∘ j_U`. -/
@[simp]
lemma restrictOpen_immersion : (j.restrictOpen jU).immersion = jU ≫ j.immersion := rfl

/-- The compactification induced on an open has the same structure morphism to `Y`. -/
@[simp]
lemma restrictOpen_toBase : (j.restrictOpen jU).toBase = j.toBase := rfl

end Open

/-! ### The compactification induced on a closed subscheme -/

section Closed

variable (j : CompactificationOf (Over.mk f)) [QuasiCompact f]
  {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The open immersion of a compactification over a quasi-separated base is quasi-compact as soon
as `f` is: it is the first factor of `f = f̄ ∘ j` with `f̄` separated. -/
instance quasiCompact_immersion : QuasiCompact j.immersion := by
  have : QuasiCompact (j.immersion ≫ j.toBase) := by rw [immersion_toBase]; infer_instance
  exact QuasiCompact.of_comp j.immersion j.toBase

/-- The composite `j ∘ i` of the closed immersion with the open immersion of the
compactification, a quasi-compact immersion. -/
abbrev closedImmersion : Z ⟶ j.space := i ≫ j.immersion

/-- The ambient scheme of the compactification induced on `Z`: the scheme-theoretic image of
`j ∘ i`. -/
abbrev closedSpace : Scheme.{u} := (j.closedImmersion i).image

/-- The closed immersion of the scheme-theoretic image of `j ∘ i` into `X̄`. -/
abbrev closedSpaceι : j.closedSpace i ⟶ j.space := (j.closedImmersion i).imageι

/-- The compactification of a closed subscheme `i : Z ⟶ X` induced by a compactification
`j : X ⟶ X̄` over `Y`: the open immersion of `Z` into the scheme-theoretic image of `j ∘ i`, which
is a closed subscheme of `X̄` and hence proper over `Y`. -/
def restrictClosed : CompactificationOf (Over.mk (i ≫ f)) :=
  ⟨StructuredArrow.mk (Y := Over.mk (j.closedSpaceι i ≫ j.toBase))
      (Over.homMk (U := Over.mk (i ≫ f)) (V := Over.mk (j.closedSpaceι i ≫ j.toBase))
        (j.closedImmersion i).toImage (by simp)),
    ⟨(inferInstance : IsOpenImmersion (j.closedImmersion i).toImage),
      (inferInstance : IsProper (j.closedSpaceι i ≫ j.toBase))⟩⟩

/-- The ambient scheme of the compactification induced on `Z` is the scheme-theoretic image
of `j ∘ i`. -/
@[simp]
lemma restrictClosed_space : (j.restrictClosed i).space = j.closedSpace i := rfl

/-- The open immersion of the compactification induced on `Z` is the map of `Z` into the
scheme-theoretic image of `j ∘ i`. -/
@[simp]
lemma restrictClosed_immersion :
    (j.restrictClosed i).immersion = (j.closedImmersion i).toImage := rfl

/-- The structure morphism of the compactification induced on `Z` is the closed immersion into
`X̄` followed by the structure morphism of `X̄`. -/
@[simp]
lemma restrictClosed_toBase : (j.restrictClosed i).toBase = j.closedSpaceι i ≫ j.toBase := rfl

/-- The square of `i : Z ⟶ X`, of the open immersion `t : Z ⟶ Z̄` of the induced
compactification, of `j : X ⟶ X̄` and of the closed immersion `Z̄ ⟶ X̄` is cartesian: the
scheme-theoretic image of `Z` in `X̄`, restricted to the open `X`, is the scheme-theoretic image of
`Z` in `X`, which is `Z` itself. -/
theorem isPullback_restrictClosed :
    IsPullback i (j.closedImmersion i).toImage j.immersion (j.closedSpaceι i) := by
  refine isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_
  rw [show (j.closedSpaceι i).ker = (j.closedImmersion i).ker from
    IdealSheafData.ker_subschemeι _]
  ext W : 2
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion,
    ker_ideal_of_isPullback_of_isOpenImmersion (i ≫ j.immersion) i (𝟙 Z)
      j.immersion (IsPullback.of_vert_isIso_mono ⟨by simp⟩) W]

end Closed

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

variable (Λ : Type r) [Ring Λ]

/-! ### Extension by zero along a composite of étale morphisms -/

section Composition

variable {U X W : Scheme.{u}} (a : U ⟶ X) (b : X ⟶ W) [Etale a] [Etale b]

/-- Composing with `a ≫ b` is composing with `a` and then with `b`, as functors of small étale
sites; each component is the identity of the underlying scheme. -/
def smallEtaleComposeCompIso :
    smallEtaleCompose (a ≫ b) ≅ smallEtaleCompose a ⋙ smallEtaleCompose b :=
  MorphismProperty.Over.mapComp (P := @Etale) (Q := ⊤) ‹Etale a› ‹Etale b›

/-- Restriction along `a ≫ b` is restriction along `b` followed by restriction along `a`, on
sheaves of `Λ`-modules. -/
def etaleModuleRestrictionCompIso :
    etaleModuleRestriction.{u, r} Λ b ⋙ etaleModuleRestriction.{u, r} Λ a ≅
      etaleModuleRestriction.{u, r} Λ (a ≫ b) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleComposeCompIso a b).symm
    (ModuleCat.{max (u + 1) r} Λ) U.smallEtaleTopology X.smallEtaleTopology W.smallEtaleTopology

/-- **Extension by zero composes**: `(b ∘ a)_! ≅ b_! ∘ a_!` for étale morphisms `a` and `b`, on
sheaves of `Λ`-modules. Both sides are left adjoint to restriction along `a ≫ b`. -/
def etaleModuleExtensionByZeroCompIso :
    etaleModuleExtensionByZero.{u, r} Λ (a ≫ b) ≅
      etaleModuleExtensionByZero.{u, r} Λ a ⋙ etaleModuleExtensionByZero.{u, r} Λ b :=
  Adjunction.leftAdjointUniq (etaleModuleExtensionByZeroAdj.{u, r} Λ (a ≫ b))
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ a).comp
      (etaleModuleExtensionByZeroAdj.{u, r} Λ b)).ofNatIsoRight
        (etaleModuleRestrictionCompIso.{u, r} Λ a b))

end Composition

/-! ### Extension by zero and inverse image around a cartesian square -/

section BaseChange

variable {X Y U YU : Scheme.{u}} {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y}
  [Etale pY]

/-- **Extension by zero commutes with inverse image**, for sheaves of `Λ`-modules and an
arbitrary cartesian square
```
YU --pY--> Y
|hU        |h
U  --j-->  X
```
with `j` étale: `pY_! ∘ hU^{-1} ≅ h^{-1} ∘ j_!`. Both sides are left adjoints, of
`hU_* ∘ pY^{-1}` and of `j^{-1} ∘ h_*`, and those agree by
`Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback`. -/
def etaleModuleInverseImageExtensionByZeroIso (upper : IsPullback hU pY j h) :
    etaleModuleInverseImage.{u, r} Λ hU ⋙ etaleModuleExtensionByZero.{u, r} Λ pY ≅
      etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ h :=
  Adjunction.leftAdjointUniq
    ((etaleModuleInverseImageAdj.{u, r} Λ hU).comp (etaleModuleExtensionByZeroAdj.{u, r} Λ pY))
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ j).comp
      (etaleModuleInverseImageAdj.{u, r} Λ h)).ofNatIsoRight
        (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) upper).symm)

end BaseChange

/-! ### Extension by zero and direct image along a closed immersion -/

section ClosedImmersion

/-- Along a closed immersion `ι : Z ⟶ X`, the unit `N ⟶ ι_* ι^{-1} N` is an isomorphism as soon
as `N` restricts to zero on an open `o : O ⟶ X` complementary to the image of `ι`: it is the
cokernel map of the short exact sequence `0 → o_! o^{-1} N → N → ι_* ι^{-1} N → 0` of
[Stacks, Tag 095L]. -/
theorem isIso_etaleModuleInverseImageAdj_unit_app_of_isZero {Z O X : Scheme.{u}} (ι : Z ⟶ X)
    [IsClosedImmersion ι] (o : O ⟶ X) [IsOpenImmersion o]
    (ho : Set.range o.base = (Set.range ι.base)ᶜ) (N : EtaleModules.{u, r} Λ X)
    (hN : IsZero ((etaleModuleRestriction.{u, r} Λ o).obj N)) :
    IsIso ((etaleModuleInverseImageAdj.{u, r} Λ ι).unit.app N) := by
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ ι o ho N
  exact hS.isIso_g_iff.2 ((etaleModuleExtensionByZero.{u, r} Λ o).map_isZero hN)

variable {Z X Zb Xb : Scheme.{u}} (i : Z ⟶ X) (t : Z ⟶ Zb) (j : X ⟶ Xb) (ι : Zb ⟶ Xb)
  [IsOpenImmersion j] [IsOpenImmersion t] [IsClosedImmersion ι]

/-- The comparison `j_! ∘ i_* ⟶ ι_* ∘ t_!` attached to a cartesian square
```
Z  --t--> Zb
|i        |ι
X  --j--> Xb
```
with `j`, `t` open and `ι` closed immersions: the unit of `ι^{-1} ⊣ ι_*`, followed by
`ι^{-1} j_! ≅ t_! i^{-1}` and by the counit `i^{-1} i_* ≅ 𝟭`. -/
def etaleModuleExtensionByZeroDirectImageHom (sq : IsPullback i t j ι) :
    etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ t ⋙ etaleModuleDirectImage.{u, r} Λ ι :=
  Functor.whiskerLeft (etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleExtensionByZero.{u, r} Λ j)
      (etaleModuleInverseImageAdj.{u, r} Λ ι).unit ≫
    Functor.whiskerLeft (etaleModuleDirectImage.{u, r} Λ i)
      (Functor.whiskerRight (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ sq).inv
        (etaleModuleDirectImage.{u, r} Λ ι)) ≫
    Functor.whiskerRight (etaleModuleInverseImageAdj.{u, r} Λ i).counit
      (etaleModuleExtensionByZero.{u, r} Λ t ⋙ etaleModuleDirectImage.{u, r} Λ ι)

/-- The comparison `j_! ∘ i_* ⟶ ι_* ∘ t_!` is an isomorphism. Its first factor, the unit
`N ⟶ ι_* ι^{-1} N` at `N = j_! i_* F`, is invertible because `N` vanishes on the open complement
`O` of `Zb`: by base change of extension by zero along `O ⟶ Xb`, its restriction to `O` is the
extension by zero of the restriction of `i_* F` to `O ∩ X`, which misses `Z`. -/
@[sga "4½ Arcata 4.5.2" "p_*(j_{2!}F) = j_{1!}F"]
instance isIso_etaleModuleExtensionByZeroDirectImageHom (sq : IsPullback i t j ι) :
    IsIso (etaleModuleExtensionByZeroDirectImageHom.{u, r} Λ i t j ι sq) := by
  have : IsClosedImmersion i := MorphismProperty.of_isPullback sq.flip inferInstance
  let O : Xb.Opens := ⟨(Set.range ι.base)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hO : Set.range O.ι.base = (Set.range ι.base)ᶜ := by simp [O]
  have hunit : ∀ F, IsIso ((etaleModuleInverseImageAdj.{u, r} Λ ι).unit.app
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((etaleModuleDirectImage.{u, r} Λ i).obj F))) := by
    intro F
    refine isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ ι O.ι hO _ ?_
    let P := IsPullback.of_hasPullback j O.ι
    have : Etale (pullback.snd j O.ι) := etale_of_isPullback_snd P
    have hdisj : Disjoint (Set.range (pullback.fst j O.ι).base) (Set.range i.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, rfl⟩ ⟨z, hz⟩
      have h1 : j.base (i.base z) = ι.base (t.base z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
      have h2 : j.base ((pullback.fst j O.ι).base w) = O.ι.base ((pullback.snd j O.ι).base w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have : O.ι.base ((pullback.snd j O.ι).base w) ∈ Set.range O.ι.base := ⟨_, rfl⟩
      rw [hO, ← h2, ← hz, h1] at this
      exact this ⟨_, rfl⟩
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, r} Λ O.ι).symm.app _)
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ P).symm.app _)
    refine (etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j O.ι)).map_isZero ?_
    refine IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, r} Λ
      (pullback.fst j O.ι)).app _)
    · exact isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint Λ i _ hdisj.symm F
  have : ∀ F, IsIso ((etaleModuleExtensionByZeroDirectImageHom.{u, r} Λ i t j ι sq).app F) := by
    intro F
    dsimp only [etaleModuleExtensionByZeroDirectImageHom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have h1 : IsIso ((etaleModuleInverseImageAdj.{u, r} Λ ι).unit.app
        ((etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleExtensionByZero.{u, r} Λ j).obj F)) :=
      hunit F
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).full
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).faithful
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **`j_! ∘ i_* ≅ ι_* ∘ t_!`** for a cartesian square of schemes
```
Z  --t--> Zb
|i        |ι
X  --j--> Xb
```
with `j`, `t` open immersions and `ι` a closed immersion, on sheaves of `Λ`-modules. -/
def etaleModuleExtensionByZeroDirectImageIso (sq : IsPullback i t j ι) :
    etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleExtensionByZero.{u, r} Λ j ≅
      etaleModuleExtensionByZero.{u, r} Λ t ⋙ etaleModuleDirectImage.{u, r} Λ ι :=
  asIso (etaleModuleExtensionByZeroDirectImageHom.{u, r} Λ i t j ι sq)

end ClosedImmersion

/-! ### The derived lower shriek of a restriction, on bounded below derived categories -/

section DerivedPlus

attribute [local instance] HasDerivedCategory.standard

open Stacks.DerivedFunctor

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- **The derived lower shriek of the restriction to an open.** For an open immersion
`j_U : U ⟶ X` and the induced compactification `j ∘ j_U` of `U`, the derived lower shriek of
`f ∘ j_U` is `Rf_! ∘ Rj_{U!}`, on bounded below derived categories of sheaves of `Λ`-modules:
`R(j ∘ j_U)_! = Rj_! ∘ Rj_{U!}` because extension by zero composes and is exact. -/
def derivedLowerShriekRestrictOpenIso {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] :
    derivedLowerShriek.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ ≅
      etaleModuleDerivedExtensionByZero.{u, r} Λ jU ⋙ derivedLowerShriek.{u, r} f j Λ :=
  Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusCompIsoOfExact
      (etaleModuleExtensionByZero.{u, r} Λ jU) (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
      (etaleModuleExtensionByZero.{u, r} Λ (jU ≫ j.immersion))
      (etaleModuleExtensionByZeroCompIso.{u, r} Λ jU j.immersion).symm).symm
    (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase) ≪≫
  Functor.associator _ _ _

/-- **The derived lower shriek of the restriction to a closed subscheme.** For a closed
immersion `i : Z ⟶ X` and the induced compactification of `Z` by the scheme-theoretic image
`Z̄` of `Z` in `X̄`, the derived lower shriek of `f ∘ i` is `Rf_! ∘ Ri_*`, on bounded below
derived categories of sheaves of `Λ`-modules: with `t : Z ⟶ Z̄` and `ι : Z̄ ⟶ X̄`,
`R(f̄ ∘ ι)_* ∘ Rt_! = Rf̄_* ∘ Rι_* ∘ Rt_! = Rf̄_* ∘ Rj_! ∘ Ri_*` because `ι_* ∘ t_! = j_! ∘ i_*`
and all four functors are exact. -/
def derivedLowerShriekRestrictClosedIso [QuasiCompact f] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    derivedLowerShriek.{u, r} (i ≫ f) (j.restrictClosed i) Λ ≅
      etaleModuleDerivedDirectImage.{u, r} Λ i ⋙ derivedLowerShriek.{u, r} f j Λ :=
  Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZero.{u, r} Λ (j.closedImmersion i).toImage)
      (etaleModuleDerivedDirectImageComp.{u, r} Λ (j.closedSpaceι i) j.toBase _ rfl) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusCompIsoOfExact
        (etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion i).toImage)
        (etaleModuleDirectImage.{u, r} Λ (j.closedSpaceι i)) _
        (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i (j.closedImmersion i).toImage
          j.immersion (j.closedSpaceι i) (j.isPullback_restrictClosed i)).symm ≪≫
      (Functor.rightDerivedFunctorPlusCompIsoOfExact
        (etaleModuleDirectImage.{u, r} Λ i) (etaleModuleExtensionByZero.{u, r} Λ j.immersion) _
        (Iso.refl _)).symm)
      (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase) ≪≫
    Functor.associator _ _ _

end DerivedPlus

/-! ### The derived lower shriek of a restriction, on unbounded derived categories -/

section DerivedUnbounded

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- **The derived lower shriek of the restriction to an open, on `D(X_étale, Λ)`.** For an open
immersion `j_U : U ⟶ X` and the induced compactification `j ∘ j_U` of `U`, the derived lower
shriek of `f ∘ j_U` on unbounded derived categories is `Rf_! ∘ Rj_{U!}`. -/
def derivedLowerShriekUnboundedRestrictOpenIso {U : Scheme.{u}} (jU : U ⟶ X)
    [IsOpenImmersion jU] :
    derivedLowerShriekUnbounded.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ jU ⋙
        derivedLowerShriekUnbounded.{u, r} f j Λ :=
  Functor.isoWhiskerRight
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ (jU ≫ j.immersion) ≪≫
        DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (etaleModuleExtensionByZeroCompIso.{u, r} Λ jU j.immersion) ≪≫
        DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.isoWhiskerRight
          (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ jU).symm _ ≪≫
        Functor.isoWhiskerLeft _
          (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion).symm)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase) ≪≫
    Functor.associator _ _ _

/-- **The derived lower shriek of the restriction to a closed subscheme, on `D(X_étale, Λ)`.**
For a closed immersion `i : Z ⟶ X` and the compactification of `Z` induced through the
scheme-theoretic image of `Z` in `X̄`, the derived lower shriek of `f ∘ i` on unbounded derived
categories is `Rf_! ∘ i_*`. -/
def derivedLowerShriekUnboundedRestrictClosedIso [QuasiCompact f] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    derivedLowerShriekUnbounded.{u, r} (i ≫ f) (j.restrictClosed i) Λ ≅
      (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategory ⋙
        derivedLowerShriekUnbounded.{u, r} f j Λ :=
  Functor.isoWhiskerLeft
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ (j.closedImmersion i).toImage)
      (etaleModuleDerivedDirectImageUnboundedCompIso.{u, r} Λ (j.closedSpaceι i) j.toBase) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ (j.closedImmersion i).toImage)
          _ ≪≫
        (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
        DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i (j.closedImmersion i).toImage
            j.immersion (j.closedSpaceι i) (j.isPullback_restrictClosed i)).symm ≪≫
        DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.isoWhiskerLeft _
          (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion).symm)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase) ≪≫
    Functor.associator _ _ _

end DerivedUnbounded

end Stacks.EtaleCohomology

end
