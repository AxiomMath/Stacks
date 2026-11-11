module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictUnit
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.MayerVietorisInjective
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlueData
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# The Mayer--Vietoris triangle of two opens of a scheme

For opens `U`, `V` of a scheme `X` and an object `K` of the unbounded derived category `D(𝒪_X)`
there is a distinguished triangle

`Rj_{U ∪ V,*}(K|_{U ∪ V}) ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶`

in `D(𝒪_X)`, where `j_W : W → X` are the inclusions of the open subschemes; and when `U` and `V`
cover `X` its first term is `K` itself.

## Main definitions

* `Stacks.Duality.Coherator.restrictPushforwardFunctor` — the endofunctor `Rj_{W,*}(-|_W)` of
  `D(𝒪_X)`.
* `Stacks.Duality.Coherator.pushRestrictFunctor` — the endofunctor `j_{W,*} j_W^*` of
  `𝒪_X`-modules.
* `Stacks.Duality.Coherator.mvResNat` and `Stacks.Duality.Coherator.mvDiffNat` — the two maps of
  the Mayer--Vietoris sequence of endofunctors.
* `Stacks.Duality.Coherator.pushRestrictDerivedIso` — a K-injective complex computes
  `Rj_{W,*}(-|_W)`.
* `Stacks.Duality.Coherator.restrictPushforwardTopIso` — `Rj_{⊤,*}(K|_⊤) ≅ K`.
* `Stacks.Duality.Coherator.restrictPushforwardRes` — the restriction map
  `Rj_{W,*}(K|_W) ⟶ Rj_{W',*}(K|_{W'})` for opens `W' ≤ W`.
* `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle` — the triangle with first term `K` for a
  cover `U ∪ V = X`, with its maps: the pair of units of `j_W^* ⊣ Rj_{W,*}`, the difference of
  the restriction maps, and the connecting map `Stacks.Duality.Coherator.mayerVietorisDerivedδ`.

## Main results

* `Stacks.Duality.Coherator.exists_distTriang_restrictPushforward_sup` — the triangle with first
  term `Rj_{U ∪ V,*}(K|_{U ∪ V})`, for arbitrary opens `U`, `V`.
* `Stacks.Duality.Coherator.exists_distTriang_self` — the triangle with first term `K`, for a
  cover `U ∪ V = X`.
* `Stacks.Duality.Coherator.derivedRestrictPushforwardAdjunction_unit_app_Q` — on a K-injective
  complex the unit of `j_W^* ⊣ Rj_{W,*}` is the degreewise unit of `j_W^* ⊣ j_{W,*}`.
* `Stacks.Duality.Coherator.unit_app_comp_restrictPushforwardRes` — the restriction maps are
  compatible with the units.
* `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle_distinguished` — the triangle with its
  maps is distinguished.

## Implementation notes

The source's dévissage is performed in the scheme vocabulary. A K-injective representative with
injective terms ([Stacks, Tag 079P]) is chosen for `K`; the degreewise Mayer--Vietoris sequence of
injective `𝒪_X`-modules is short exact
(`Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective`, which is
[Stacks, Tag 01EA] on sections), so the three complexes form a short exact sequence and hence a
distinguished triangle; and the three terms are identified with `Rj_{W,*}(K|_W)` because
restriction to an open subscheme preserves K-injectivity ([Stacks, Tag 08BS]) and a K-injective
complex computes `Rj_{W,*}` ([Stacks, Tag 070K]).

The two `exists_distTriang` results assert only the existence of the three maps.
`Stacks.Duality.Coherator.mayerVietorisDerivedTriangle` names them: the first is stated without
reference to a model, while the restriction maps and the connecting map are read on the
K-injective model `Stacks.Duality.Coherator.kInjectiveModel K` of `K`, where `Rj_{W,*}(K|_W)` is
the naive complex `j_{W,*}(I|_W)` (`Stacks.Duality.Coherator.pushRestrictDerivedIso`), and the
connecting map is that of the short exact sequence
`0 ⟶ I ⟶ j_{U,*}(I|_U) ⊕ j_{V,*}(I|_V) ⟶ j_{U ∩ V,*}(I|_{U ∩ V}) ⟶ 0`
(`Stacks.Duality.Coherator.mvSelfShortComplex`).

The statements carry no `[HasDerivedCategory.{w}]` binder and are therefore at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, as the vocabulary of
[Stacks, Tag 0CR2] is. The ringed-space form of the triangle,
`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover`, uses
`HasDerivedCategory.standard` and derives the endofunctors `j_{W,*} j_W^*` as single functors
rather than as the composites `Rj_{W,*} ∘ j_W^*` across the open subschemes.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeMayerVietoris

universe u

namespace Stacks.Duality.Coherator

variable {X : Scheme.{u}}

/-! ### The endofunctor `Rj_{W,*}(-|_W)` of `D(𝒪_X)` -/

/-- `Rj_{W,*}(-|_W)` as an endofunctor of `D(𝒪_X)`, for `W` an open of `X`: restrict to the open
subscheme `W`, then take the unbounded derived direct image along the inclusion `j_W : W → X`.
Its value at `K` is the term `Rj_{W,*}(K|_W)` of the Mayer--Vietoris triangle. -/
abbrev restrictPushforwardFunctor (W : X.Opens) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  Stacks.Duality.OpenImmersion.derivedRestrict W.ι ⋙ Stacks.Duality.derivedPushforward W.ι

/-! ### The endofunctor `j_{W,*} j_W^*` of `𝒪_X`-modules -/

/-- The endofunctor `j_{W,*} j_W^*` of `𝒪_X`-modules attached to an open `W` of `X`: restrict to
the open subscheme `W`, then push forward along the inclusion. Its value at `F` is
`Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushRestrict F W`. -/
abbrev pushRestrictFunctor (W : X.Opens) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pushforward W.ι

/-- On sections over an open `T`, the map `j_{W,*} j_W^* φ` is `φ` on the open `W ∩ T`, written as
the image of `j_W⁻¹ T` under `j_W`. -/
lemma pushRestrictFunctor_map_app {F G : X.Modules} (φ : F ⟶ G) (W T : X.Opens) :
    ((pushRestrictFunctor W).map φ).app T = φ.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ T)) := rfl

/-- The restriction morphisms `j_{W,*} j_W^* ⟶ j_{W',*} j_{W'}^*` for `W' ≤ W` are natural in the
module: on sections both sides are a single restriction map of the module. -/
def resPushNat {W W' : X.Opens} (h : W' ≤ W) :
    pushRestrictFunctor (X := X) W ⟶ pushRestrictFunctor W' where
  app F := resPush F h
  naturality F G φ := by
    refine Scheme.Modules.hom_ext _ _ fun T => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, resPush_app, resPush_app,
      pushRestrictFunctor_map_app, pushRestrictFunctor_map_app]
    exact (φ.mapPresheaf.naturality (Opposite.op (homOfLE (image_preimage_mono h T)))).symm

/-- The component of `Stacks.Duality.Coherator.resPushNat` at a module `F` is the restriction
morphism `Stacks.AlgebraicGeometry.RelativeMayerVietoris.resPush F`. -/
@[simp] lemma resPushNat_app {W W' : X.Opens} (h : W' ≤ W) (F : X.Modules) :
    (resPushNat h).app F = resPush F h := rfl

/-! ### The Mayer--Vietoris short complex of endofunctors -/

variable (U V : X.Opens)

/-- The middle term `j_{U,*} j_U^* ⊕ j_{V,*} j_V^*` of the Mayer--Vietoris sequence, as an
endofunctor of `𝒪_X`-modules. -/
def mvMiddleFunctor : X.Modules ⥤ X.Modules where
  obj F := pushRestrict F U ⊞ pushRestrict F V
  map φ := biprod.map ((pushRestrictFunctor U).map φ) ((pushRestrictFunctor V).map φ)
  map_id _ := by apply biprod.hom_ext <;> simp
  map_comp _ _ := by apply biprod.hom_ext <;> simp [Functor.map_comp]

/-- The endofunctor `j_{U,*} j_U^* ⊕ j_{V,*} j_V^*` is additive. -/
instance mvMiddleFunctor_additive : (mvMiddleFunctor (X := X) U V).Additive := ⟨by
  intro A B f g
  change biprod.map ((pushRestrictFunctor U).map (f + g)) ((pushRestrictFunctor V).map (f + g)) =
    biprod.map ((pushRestrictFunctor U).map f) ((pushRestrictFunctor V).map f) +
      biprod.map ((pushRestrictFunctor U).map g) ((pushRestrictFunctor V).map g)
  rw [Functor.map_add, Functor.map_add]
  apply biprod.hom_ext <;> simp [Preadditive.comp_add]⟩

/-- The pair of restrictions `j_{U ∪ V,*} j_{U ∪ V}^* ⟶ j_{U,*} j_U^* ⊕ j_{V,*} j_V^*`. -/
def mvResNat : pushRestrictFunctor (X := X) (U ⊔ V) ⟶ mvMiddleFunctor U V where
  app F := mvRes F U V
  naturality F G φ := by
    apply biprod.hom_ext
    · simpa [mvMiddleFunctor, mvRes, Category.assoc] using
        (resPushNat (X := X) (le_sup_left (b := V))).naturality φ
    · simpa [mvMiddleFunctor, mvRes, Category.assoc] using
        (resPushNat (X := X) (le_sup_right (a := U))).naturality φ

/-- The difference of the two restrictions
`j_{U,*} j_U^* ⊕ j_{V,*} j_V^* ⟶ j_{U ∩ V,*} j_{U ∩ V}^*`. -/
def mvDiffNat : mvMiddleFunctor (X := X) U V ⟶ pushRestrictFunctor (U ⊓ V) where
  app F := mvDiff F U V
  naturality F G φ := by
    apply biprod.hom_ext'
    · simpa [mvMiddleFunctor, mvDiff, Category.assoc] using
        (resPushNat (X := X) (inf_le_left (b := V))).naturality φ
    · simpa [mvMiddleFunctor, mvDiff, Category.assoc, Preadditive.neg_comp,
        Preadditive.comp_neg] using
        congrArg Neg.neg ((resPushNat (X := X) (inf_le_right (a := U))).naturality φ)

/-- The composite of the two maps of the Mayer--Vietoris sequence of endofunctors is zero. -/
lemma mvResNat_comp_mvDiffNat :
    mvResNat (X := X) U V ≫ mvDiffNat U V = 0 :=
  NatTrans.ext (funext fun F => mvRes_comp_mvDiff F U V)

/-! ### The Mayer--Vietoris short exact sequence of complexes -/

/-- The Mayer--Vietoris short complex of cochain complexes attached to a complex `I` of
`𝒪_X`-modules: the three endofunctors applied to `I` degreewise. -/
def mvShortComplex (I : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk
    (((mvResNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I)
    (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I)
    (by
      ext n : 1
      exact NatTrans.congr_app (mvResNat_comp_mvDiffNat U V) (I.X n))

/-- **The Mayer--Vietoris sequence of a complex of injective `𝒪_X`-modules is short exact.** It
is short exact in each degree by
`Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective`. -/
lemma mvShortComplex_shortExact (I : CochainComplex X.Modules ℤ)
    (hinj : ∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (I.X n)) :
    (mvShortComplex U V I).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective
    (I.X n) (hinj n) U V

/-! ### Identifying the three terms in the derived category -/

/-- Restriction to an open subscheme preserves K-injective complexes: this is [Stacks, Tag 08BS],
`ExtensionByZeroModules.isKInjective_jStar`, read through the identification of `j_W^*` with
Mathlib's restriction functor. -/
lemma isKInjective_restrictFunctor (W : X.Opens) {F : X.Modules ⥤ W.toScheme.Modules}
    [F.Additive] (hF : F = ExtensionByZeroModules.jStar W X.ringCatSheaf)
    (I : CochainComplex X.Modules ℤ) (hI : CochainComplex.IsKInjective I) :
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  subst hF
  exact @ExtensionByZeroModules.isKInjective_jStar _ W X.ringCatSheaf I hI

/-- The restriction `I|_W` of a K-injective complex of `𝒪_X`-modules to an open subscheme `W` is
K-injective. -/
instance isKInjective_restrict (W : X.Opens) (I : CochainComplex X.Modules ℤ)
    [hI : CochainComplex.IsKInjective I] :
    CochainComplex.IsKInjective
      (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  isKInjective_restrictFunctor W
    (Stacks.Duality.OpenImmersion.jStar_eq_restrictFunctor X W).symm I hI

/-- `Rj_{W,*}` is computed by the naive direct image on a K-injective complex: the unit of the
total right derived functor is invertible there, which is [Stacks, Tag 070K]. -/
lemma isIso_derivedPushforwardUnit (W : X.Opens) (J : CochainComplex W.toScheme.Modules ℤ)
    (hJ : CochainComplex.IsKInjective J) :
    IsIso (((Stacks.Duality.homotopyPushforward W.ι).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient W.toScheme.Modules (ComplexShape.up ℤ)).obj J)) :=
  ((Stacks.Duality.homotopyPushforward
      W.ι).hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (fun L => AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective
      W.toScheme L)).2 DerivedCategory.Qh (Stacks.Duality.derivedPushforward W.ι) _ J hJ

/-- **`Rj_{W,*}(K|_W)` is the naive direct image of the restriction, for a K-injective `K`.** -/
def pushRestrictDerivedIso (W : X.Opens) (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I) :
    DerivedCategory.Q.obj
        (((pushRestrictFunctor W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (restrictPushforwardFunctor W).obj (DerivedCategory.Q.obj I) :=
  letI := hI
  letI A := ((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  haveI hiso : IsIso
      (((Stacks.Duality.homotopyPushforward W.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.quotient W.toScheme.Modules (ComplexShape.up ℤ)).obj A)) :=
    isIso_derivedPushforwardUnit W A inferInstance
  ((DerivedCategory.quotientCompQhIso X.Modules).app
      (((Scheme.Modules.pushforward W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)).symm ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    (Stacks.Duality.derivedPushforward W.ι).mapIso
      ((DerivedCategory.quotientCompQhIso W.toScheme.Modules).app A) ≪≫
    (Stacks.Duality.derivedPushforward W.ι).mapIso
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategoryFactors.app I).symm

/-! ### The middle term in the derived category -/

/-- The first projection of the middle term. -/
def mvFstNat : mvMiddleFunctor (X := X) U V ⟶ pushRestrictFunctor U where
  app _ := biprod.fst
  naturality _ _ _ := by simp [mvMiddleFunctor]

/-- The second projection of the middle term. -/
def mvSndNat : mvMiddleFunctor (X := X) U V ⟶ pushRestrictFunctor V where
  app _ := biprod.snd
  naturality _ _ _ := by simp [mvMiddleFunctor]

/-- The first inclusion into the middle term. -/
def mvInlNat : pushRestrictFunctor (X := X) U ⟶ mvMiddleFunctor U V where
  app _ := biprod.inl
  naturality _ _ _ := by simp [mvMiddleFunctor]

/-- The second inclusion into the middle term. -/
def mvInrNat : pushRestrictFunctor (X := X) V ⟶ mvMiddleFunctor U V where
  app _ := biprod.inr
  naturality _ _ _ := by simp [mvMiddleFunctor]

/-- The middle term of the Mayer--Vietoris sequence of complexes is the biproduct of the two
restriction–pushforward complexes: the biproduct of cochain complexes is formed degreewise. -/
def mvBicone (I : CochainComplex X.Modules ℤ) :
    BinaryBicone (((pushRestrictFunctor U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (((pushRestrictFunctor V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  pt := ((mvMiddleFunctor U V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  fst := ((mvFstNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I
  snd := ((mvSndNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I
  inl := ((mvInlNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I
  inr := ((mvInrNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I
  inl_fst := by ext n : 1; exact biprod.inl_fst
  inl_snd := by ext n : 1; exact biprod.inl_snd
  inr_fst := by ext n : 1; exact biprod.inr_fst
  inr_snd := by ext n : 1; exact biprod.inr_snd

/-- `Stacks.Duality.Coherator.mvBicone` is a biproduct diagram. -/
def mvBiconeIsBilimit (I : CochainComplex X.Modules ℤ) : (mvBicone U V I).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
  ext n : 1
  exact biprod.total (X := (pushRestrictFunctor U).obj (I.X n))
    (Y := (pushRestrictFunctor V).obj (I.X n))

/-- The localization functor from cochain complexes of `𝒪_X`-modules to `D(𝒪_X)` preserves
binary biproducts. -/
instance derivedQ_preservesBinaryBiproducts :
    PreservesBinaryBiproducts (DerivedCategory.Q (C := X.Modules)) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- **The middle term of the Mayer--Vietoris triangle**: the derived category of the degreewise
biproduct is the biproduct of `Rj_{U,*}(K|_U)` and `Rj_{V,*}(K|_V)`, for a K-injective `K`. -/
def mvMiddleDerivedIso (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I) :
    DerivedCategory.Q.obj
        (((mvMiddleFunctor U V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (restrictPushforwardFunctor U).obj (DerivedCategory.Q.obj I) ⊞
        (restrictPushforwardFunctor V).obj (DerivedCategory.Q.obj I) :=
  biprod.uniqueUpToIso _ _
      (isBinaryBilimitOfPreserves DerivedCategory.Q (mvBiconeIsBilimit U V I)) ≪≫
    biprod.mapIso (pushRestrictDerivedIso U I hI) (pushRestrictDerivedIso V I hI)

/-! ### Transport of a distinguished triangle along isomorphisms of its three terms

The three identities a triangle isomorphism asks for are composites of an isomorphism with its
inverse. They are discharged by the two abstract lemmas below: in the concrete goals the two
spellings of the localization functor out of cochain complexes are only definitionally equal, so
`rw` and `simp` cannot act on those targets, whereas `exact` against an abstract lemma can. -/

/-- Existence of a distinguished triangle on three prescribed objects of `D(𝒪_X)` only depends on
their isomorphism classes. -/
private theorem exists_distTriang_of_iso {A A' B B' D D' : DerivedCategory X.Modules}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D')
    (h : ∃ (f : A ⟶ B) (g : B ⟶ D) (δ : D ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory X.Modules)) :
    ∃ (f : A' ⟶ B') (g : B' ⟶ D') (δ : D' ⟶ A'⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory X.Modules) := by
  obtain ⟨f, g, δ, hT⟩ := h
  refine ⟨eA.inv ≫ f ≫ eB.hom, eB.inv ≫ g ≫ eD.hom,
    eD.inv ≫ δ ≫ (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map eA.hom, ?_⟩
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _ eA.symm eB.symm eD.symm ?_ ?_ ?_
  all_goals simp

/-! ### The Mayer--Vietoris triangle -/

/-- **The Mayer--Vietoris triangle for a K-injective complex of injective `𝒪_X`-modules.** -/
theorem exists_distTriang_Q_obj (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I)
    (hinj : ∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (I.X n)) :
    ∃ (f : (restrictPushforwardFunctor (U ⊔ V)).obj (DerivedCategory.Q.obj I) ⟶
          (restrictPushforwardFunctor U).obj (DerivedCategory.Q.obj I) ⊞
            (restrictPushforwardFunctor V).obj (DerivedCategory.Q.obj I))
      (g : (restrictPushforwardFunctor U).obj (DerivedCategory.Q.obj I) ⊞
            (restrictPushforwardFunctor V).obj (DerivedCategory.Q.obj I) ⟶
          (restrictPushforwardFunctor (U ⊓ V)).obj (DerivedCategory.Q.obj I))
      (δ : (restrictPushforwardFunctor (U ⊓ V)).obj (DerivedCategory.Q.obj I) ⟶
          ((restrictPushforwardFunctor (U ⊔ V)).obj (DerivedCategory.Q.obj I))⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory X.Modules) :=
  have hSE := mvShortComplex_shortExact U V I hinj
  exists_distTriang_of_iso (pushRestrictDerivedIso (U ⊔ V) I hI) (mvMiddleDerivedIso U V I hI)
    (pushRestrictDerivedIso (U ⊓ V) I hI)
    ⟨DerivedCategory.Q.map (mvShortComplex U V I).f,
      DerivedCategory.Q.map (mvShortComplex U V I).g,
      DerivedCategory.triangleOfSESδ hSE,
      DerivedCategory.triangleOfSES_distinguished hSE⟩

/-- A K-injective representative with injective terms of an object of `D(𝒪_X)`: the functorial
K-injective resolution ([Stacks, Tag 079P]) of a cochain complex representing it. -/
def kInjectiveModel (K : DerivedCategory X.Modules) : CochainComplex X.Modules ℤ :=
  (Stacks.Injectives.kInjectiveResolutionFunctor X.Modules).obj
    (DerivedCategory.Q.objPreimage K)

/-- The K-injective model of an object of `D(𝒪_X)` is K-injective. -/
instance kInjectiveModel_isKInjective (K : DerivedCategory X.Modules) :
    CochainComplex.IsKInjective (kInjectiveModel K) :=
  Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective X.Modules _

/-- Every term of the K-injective model of an object of `D(𝒪_X)` is an injective `𝒪_X`-module. -/
lemma kInjectiveModel_injective (K : DerivedCategory X.Modules) (n : ℤ) :
    Injective (C := SheafOfModules.{u} X.ringCatSheaf) ((kInjectiveModel K).X n) :=
  Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective X.Modules _ n

/-- The K-injective model represents the object it was built from. -/
def kInjectiveModelIso (K : DerivedCategory X.Modules) :
    DerivedCategory.Q.obj (kInjectiveModel K) ≅ K :=
  haveI : IsIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app
        (DerivedCategory.Q.objPreimage K))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  (asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app
        (DerivedCategory.Q.objPreimage K)))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- **The Mayer--Vietoris triangle of two opens of a scheme.** For opens `U`, `V` of a scheme `X`
and any object `K` of the unbounded derived category `D(𝒪_X)` there is a distinguished triangle

`Rj_{U ∪ V,*}(K|_{U ∪ V}) ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶`

in `D(𝒪_X)`, where `j_W : W → X` are the inclusions of the open subschemes. -/
theorem exists_distTriang_restrictPushforward_sup (K : DerivedCategory X.Modules) :
    ∃ (f : (restrictPushforwardFunctor (U ⊔ V)).obj K ⟶
          (restrictPushforwardFunctor U).obj K ⊞ (restrictPushforwardFunctor V).obj K)
      (g : (restrictPushforwardFunctor U).obj K ⊞ (restrictPushforwardFunctor V).obj K ⟶
          (restrictPushforwardFunctor (U ⊓ V)).obj K)
      (δ : (restrictPushforwardFunctor (U ⊓ V)).obj K ⟶
          ((restrictPushforwardFunctor (U ⊔ V)).obj K)⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory X.Modules) :=
  exists_distTriang_of_iso
    ((restrictPushforwardFunctor (U ⊔ V)).mapIso (kInjectiveModelIso K))
    (biprod.mapIso ((restrictPushforwardFunctor U).mapIso (kInjectiveModelIso K))
      ((restrictPushforwardFunctor V).mapIso (kInjectiveModelIso K)))
    ((restrictPushforwardFunctor (U ⊓ V)).mapIso (kInjectiveModelIso K))
    (exists_distTriang_Q_obj U V (kInjectiveModel K) inferInstance (kInjectiveModel_injective K))

/-! ### The triangle for a cover of the whole scheme -/

/-- For `W = ⊤` the endofunctor `j_{W,*} j_W^*` is the identity on `𝒪_X`-modules: on sections over
an open `T` the unit of the restriction–pushforward adjunction is the restriction from `T` to
`⊤ ⊓ T`. -/
def pushRestrictTopIso : 𝟭 X.Modules ≅ pushRestrictFunctor (⊤ : X.Opens) :=
  haveI : ∀ M : X.Modules,
      IsIso ((Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app M) := fun M => by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    exact AlgebraicGeometry.ReconstructionGlue.isIso_restrictAdjunctionUnit_app
      (⊤ : X.Opens).ι M W (by simp)
  haveI := NatIso.isIso_of_isIso_app (Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit
  asIso (Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit

/-- `Rj_{⊤,*}(K|_⊤) ≅ K` for a K-injective representative. -/
def restrictPushforwardTopIsoQ (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I) :
    (restrictPushforwardFunctor (⊤ : X.Opens)).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj I :=
  (pushRestrictDerivedIso (⊤ : X.Opens) I hI).symm ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (pushRestrictTopIso (X := X))
          (ComplexShape.up ℤ)).symm.app I ≪≫
        (Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)).app I)

/-- **`Rj_{⊤,*}(K|_⊤) ≅ K`**: pushing forward the restriction to the whole of `X` changes
nothing. -/
def restrictPushforwardTopIso (K : DerivedCategory X.Modules) :
    (restrictPushforwardFunctor (⊤ : X.Opens)).obj K ≅ K :=
  (restrictPushforwardFunctor (⊤ : X.Opens)).mapIso (kInjectiveModelIso K).symm ≪≫
    restrictPushforwardTopIsoQ (kInjectiveModel K) inferInstance ≪≫ kInjectiveModelIso K

/-- **The Mayer--Vietoris triangle of a cover of a scheme by two opens.** If the opens `U`, `V`
cover the scheme `X`, then every object `K` of `D(𝒪_X)` itself sits in a distinguished triangle

`K ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ K⟦1⟧`.

This is `Stacks.Duality.Coherator.exists_distTriang_restrictPushforward_sup` for the cover, whose
first term `Rj_{U ∪ V,*}(K|_{U ∪ V})` is `K`. -/
theorem exists_distTriang_self (hUV : U ⊔ V = ⊤) (K : DerivedCategory X.Modules) :
    ∃ (f : K ⟶ (restrictPushforwardFunctor U).obj K ⊞ (restrictPushforwardFunctor V).obj K)
      (g : (restrictPushforwardFunctor U).obj K ⊞ (restrictPushforwardFunctor V).obj K ⟶
          (restrictPushforwardFunctor (U ⊓ V)).obj K)
      (δ : (restrictPushforwardFunctor (U ⊓ V)).obj K ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang (DerivedCategory X.Modules) := by
  have e : (restrictPushforwardFunctor (U ⊔ V)).obj K ≅ K := by
    rw [hUV]
    exact restrictPushforwardTopIso K
  exact exists_distTriang_of_iso e (Iso.refl _) (Iso.refl _)
    (exists_distTriang_restrictPushforward_sup U V K)

/-! ### The canonical triangle: the units on modules and on complexes -/

/-- The unit `M ⟶ j_{W,*}(M|_W)` followed by the restriction to `W' ≤ W` is the unit for `W'`. -/
lemma restrictAdjunction_unit_app_comp_resPush (M : X.Modules) {W W' : X.Opens} (h : W' ≤ W) :
    (Scheme.Modules.restrictAdjunction W.ι).unit.app M ≫ resPush M h =
      (Scheme.Modules.restrictAdjunction W'.ι).unit.app M := by
  refine Scheme.Modules.hom_ext _ _ fun T => ?_
  rw [Scheme.Modules.Hom.comp_app, resPush_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  exact (M.presheaf.map_comp _ _).symm

/-- The unit `M ⟶ j_{W,*}(M|_W)` is an isomorphism when `W` is the whole scheme. -/
lemma isIso_restrictAdjunction_unit_app_of_eq_top {W : X.Opens} (hW : W = ⊤) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app M) := by
  subst hW
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  exact AlgebraicGeometry.ReconstructionGlue.isIso_restrictAdjunctionUnit_app
    (⊤ : X.Opens).ι M T (by simp)

/-- The unit `I ⟶ j_{W,*}(I|_W)` of a complex of `𝒪_X`-modules, degreewise. -/
abbrev pushRestrictUnitComplex (W : X.Opens) (I : CochainComplex X.Modules ℤ) :
    I ⟶ ((pushRestrictFunctor W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  ((Scheme.Modules.restrictAdjunction W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app I

/-- The degreewise unit followed by the degreewise restriction to `W' ≤ W` is the unit for
`W'`. -/
lemma pushRestrictUnitComplex_comp_resPushNat {W W' : X.Opens} (h : W' ≤ W)
    (I : CochainComplex X.Modules ℤ) :
    pushRestrictUnitComplex W I ≫
        ((resPushNat h).mapHomologicalComplex (ComplexShape.up ℤ)).app I =
      pushRestrictUnitComplex W' I := by
  ext n : 1
  exact restrictAdjunction_unit_app_comp_resPush (I.X n) h

/-- The pair of units `I ⟶ j_{U,*}(I|_U) ⊕ j_{V,*}(I|_V)`, degreewise. -/
def mvUnitComplex (I : CochainComplex X.Modules ℤ) :
    I ⟶ ((mvMiddleFunctor U V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I where
  f n := biprod.lift ((Scheme.Modules.restrictAdjunction U.ι).unit.app (I.X n))
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app (I.X n))
  comm' i j _ := by
    change biprod.lift _ _ ≫ biprod.map ((pushRestrictFunctor U).map (I.d i j))
      ((pushRestrictFunctor V).map (I.d i j)) = I.d i j ≫ biprod.lift _ _
    apply biprod.hom_ext
    · rw [Category.assoc, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
      exact ((Scheme.Modules.restrictAdjunction U.ι).unit.naturality (I.d i j)).symm
    · rw [Category.assoc, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
      exact ((Scheme.Modules.restrictAdjunction V.ι).unit.naturality (I.d i j)).symm

/-- The first component of `Stacks.Duality.Coherator.mvUnitComplex` is the unit for `U`. -/
lemma mvUnitComplex_comp_fst (I : CochainComplex X.Modules ℤ) :
    mvUnitComplex U V I ≫ (mvBicone U V I).fst = pushRestrictUnitComplex U I := by
  ext n : 1
  exact biprod.lift_fst _ _

/-- The second component of `Stacks.Duality.Coherator.mvUnitComplex` is the unit for `V`. -/
lemma mvUnitComplex_comp_snd (I : CochainComplex X.Modules ℤ) :
    mvUnitComplex U V I ≫ (mvBicone U V I).snd = pushRestrictUnitComplex V I := by
  ext n : 1
  exact biprod.lift_snd _ _

/-- The Mayer--Vietoris short complex `I ⟶ j_{U,*}(I|_U) ⊕ j_{V,*}(I|_V) ⟶ j_{U ∩ V,*}(I|_{U ∩ V})`
of a complex `I` of `𝒪_X`-modules: the pair of units, then the difference of the restrictions. -/
def mvSelfShortComplex (I : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk (mvUnitComplex U V I)
    (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I)
    (by
      ext n : 1
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
        NatTrans.mapHomologicalComplex_app_f]
      change biprod.lift _ _ ≫ mvDiff (I.X n) U V = 0
      rw [mvDiff, biprod.lift_desc, Preadditive.comp_neg, restrictAdjunction_unit_app_comp_resPush,
        restrictAdjunction_unit_app_comp_resPush, add_neg_cancel])

/-- **The Mayer--Vietoris sequence of a complex of injective `𝒪_X`-modules, for a cover.** If
`U ∪ V = X`, the short complex `Stacks.Duality.Coherator.mvSelfShortComplex` of a complex of
injective modules is short exact: it is isomorphic to
`Stacks.Duality.Coherator.mvShortComplex`, through the unit `I ⟶ j_{U ∪ V,*}(I|_{U ∪ V})`, which
is invertible. -/
lemma mvSelfShortComplex_shortExact (hUV : U ⊔ V = ⊤) (I : CochainComplex X.Modules ℤ)
    (hinj : ∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (I.X n)) :
    (mvSelfShortComplex U V I).ShortExact := by
  have : ∀ n, IsIso ((pushRestrictUnitComplex (U ⊔ V) I).f n) := fun n =>
    isIso_restrictAdjunction_unit_app_of_eq_top hUV (I.X n)
  have : IsIso (pushRestrictUnitComplex (U ⊔ V) I) :=
    HomologicalComplex.Hom.isIso_of_components _
  have h₁ : pushRestrictUnitComplex (U ⊔ V) I ≫
      ((mvResNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I = mvUnitComplex U V I := by
    ext n : 1
    rw [HomologicalComplex.comp_f]
    change (Scheme.Modules.restrictAdjunction (U ⊔ V).ι).unit.app (I.X n) ≫
      mvRes (I.X n) U V = biprod.lift _ _
    apply biprod.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.lift_fst _ _)).trans
        ((restrictAdjunction_unit_app_comp_resPush _ _).trans (biprod.lift_fst _ _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.lift_snd _ _)).trans
        ((restrictAdjunction_unit_app_comp_resPush _ _).trans (biprod.lift_snd _ _).symm))
  let e₁ : I ≅ ((pushRestrictFunctor (U ⊔ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
    asIso (pushRestrictUnitComplex (U ⊔ V) I)
  let e : mvSelfShortComplex U V I ≅ mvShortComplex U V I :=
    ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _) (h₁.trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ShortComplex.shortExact_of_iso e.symm (mvShortComplex_shortExact U V I hinj)

/-! ### The derived unit on a K-injective complex -/

/-- **The unit of `j_W^* ⊣ Rj_{W,*}` on a K-injective complex.** For a K-injective complex `I` of
`𝒪_X`-modules, the unit `I ⟶ Rj_{W,*}(I|_W)` in `D(𝒪_X)` is the degreewise unit
`I ⟶ j_{W,*}(I|_W)` followed by the identification
`Stacks.Duality.Coherator.pushRestrictDerivedIso` of `j_{W,*}(I|_W)` with `Rj_{W,*}(I|_W)`. -/
theorem derivedRestrictPushforwardAdjunction_unit_app_Q (W : X.Opens)
    (I : CochainComplex X.Modules ℤ) (hI : CochainComplex.IsKInjective I) :
    (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (pushRestrictUnitComplex W I) ≫
        (pushRestrictDerivedIso W I hI).hom := by
  have h := Stacks.SmallDerivedCategory.derivedAdjunction_unit_app_Q
    (Scheme.Modules.restrictAdjunction W.ι) (Iso.refl _)
    ((Stacks.Duality.homotopyPushforward W.ι).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ)))
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective W.toScheme) I
  rw [← cancel_mono ((Stacks.Duality.derivedPushforward W.ι).map
    ((Stacks.SmallDerivedCategory.leftDerivedFactorsQ
      (Iso.refl (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory)).hom.app I))]
  refine h.trans ?_
  have hG : ((Scheme.Modules.pushforward W.ι).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.app
        (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) =
      𝟙 _ := rfl
  rw [Category.assoc]
  refine congrArg (DerivedCategory.Q.map (pushRestrictUnitComplex W I) ≫ ·) ?_
  rw [Stacks.SmallDerivedCategory.rightDerivedComparisonQ_app]
  have hQ : DerivedCategory.Qh.map (((Scheme.Modules.pushforward W.ι).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.app
        (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      ((Stacks.Duality.homotopyPushforward W.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.quotient W.toScheme.Modules (ComplexShape.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) =
      ((Stacks.Duality.homotopyPushforward W.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ))).app
          ((HomotopyCategory.quotient W.toScheme.Modules (ComplexShape.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) := by
    rw [hG]
    exact (congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)
  rw [reassoc_of% hQ]
  simp [pushRestrictDerivedIso, Stacks.SmallDerivedCategory.leftDerivedFactorsQ]

/-- The unit of `j_W^* ⊣ Rj_{W,*}` at an object `K` of `D(𝒪_X)`, read on the K-injective model
of `K`. -/
lemma derivedRestrictPushforwardAdjunction_unit_app_eq (W : X.Opens)
    (K : DerivedCategory X.Modules) :
    (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.app K =
      (kInjectiveModelIso K).inv ≫
        (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.app
          (DerivedCategory.Q.obj (kInjectiveModel K)) ≫
        (restrictPushforwardFunctor W).map (kInjectiveModelIso K).hom := by
  have := (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.naturality
    (kInjectiveModelIso K).hom
  dsimp only [Functor.id_map, Functor.id_obj] at this
  rw [← this, Iso.inv_hom_id_assoc]

/-! ### The restriction maps -/

/-- The restriction map `Rj_{W,*}(K|_W) ⟶ Rj_{W',*}(K|_{W'})` for opens `W' ≤ W` of `X` and an
object `K` of `D(𝒪_X)`: on the K-injective model `I` of `K` it is the restriction morphism
`j_{W,*}(I|_W) ⟶ j_{W',*}(I|_{W'})` of complexes. -/
def restrictPushforwardRes {W W' : X.Opens} (h : W' ≤ W) (K : DerivedCategory X.Modules) :
    (restrictPushforwardFunctor W).obj K ⟶ (restrictPushforwardFunctor W').obj K :=
  (restrictPushforwardFunctor W).map (kInjectiveModelIso K).inv ≫
    (pushRestrictDerivedIso W (kInjectiveModel K) inferInstance).inv ≫
    DerivedCategory.Q.map (((resPushNat h).mapHomologicalComplex (ComplexShape.up ℤ)).app
      (kInjectiveModel K)) ≫
    (pushRestrictDerivedIso W' (kInjectiveModel K) inferInstance).hom ≫
    (restrictPushforwardFunctor W').map (kInjectiveModelIso K).hom

/-- **The restriction maps are compatible with the units**: the unit `K ⟶ Rj_{W,*}(K|_W)`
followed by the restriction to `W' ≤ W` is the unit `K ⟶ Rj_{W',*}(K|_{W'})`. -/
theorem unit_app_comp_restrictPushforwardRes {W W' : X.Opens} (h : W' ≤ W)
    (K : DerivedCategory X.Modules) :
    (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.app K ≫
        restrictPushforwardRes h K =
      (OpenImmersion.derivedRestrictPushforwardAdjunction W'.ι).unit.app K := by
  rw [derivedRestrictPushforwardAdjunction_unit_app_eq W K,
    derivedRestrictPushforwardAdjunction_unit_app_eq W' K,
    derivedRestrictPushforwardAdjunction_unit_app_Q W _ inferInstance,
    derivedRestrictPushforwardAdjunction_unit_app_Q W' _ inferInstance, restrictPushforwardRes]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  rw [pushRestrictUnitComplex_comp_resPushNat]

/-! ### The middle term on the K-injective model -/

/-- On the K-injective model, the pair of units of complexes is the pair of derived units. -/
lemma Q_map_mvUnitComplex_comp_mvMiddleDerivedIso (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I) :
    DerivedCategory.Q.map (mvUnitComplex U V I) ≫ (mvMiddleDerivedIso U V I hI).hom =
      biprod.lift
        ((OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).unit.app
          (DerivedCategory.Q.obj I))
        ((OpenImmersion.derivedRestrictPushforwardAdjunction V.ι).unit.app
          (DerivedCategory.Q.obj I)) := by
  have hMI : (mvMiddleDerivedIso U V I hI).hom =
      biprod.lift (DerivedCategory.Q.map (mvBicone U V I).fst)
          (DerivedCategory.Q.map (mvBicone U V I).snd) ≫
        biprod.map (pushRestrictDerivedIso U I hI).hom (pushRestrictDerivedIso V I hI).hom := rfl
  have hfst : DerivedCategory.Q.map (mvUnitComplex U V I) ≫
      DerivedCategory.Q.map (mvBicone U V I).fst =
        DerivedCategory.Q.map (pushRestrictUnitComplex U I) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg _ (mvUnitComplex_comp_fst U V I))
  have hsnd : DerivedCategory.Q.map (mvUnitComplex U V I) ≫
      DerivedCategory.Q.map (mvBicone U V I).snd =
        DerivedCategory.Q.map (pushRestrictUnitComplex V I) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg _ (mvUnitComplex_comp_snd U V I))
  rw [derivedRestrictPushforwardAdjunction_unit_app_Q U I hI,
    derivedRestrictPushforwardAdjunction_unit_app_Q V I hI, hMI, ← hfst, ← hsnd]
  apply biprod.hom_ext
  · exact (Category.assoc _ _ _).trans (congrArg (DerivedCategory.Q.map (mvUnitComplex U V I) ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.map_fst _ _)).trans
        (biprod.lift_fst_assoc _ _ _))))|>.trans
      ((Category.assoc _ _ _).symm.trans (biprod.lift_fst _ _).symm)
  · exact (Category.assoc _ _ _).trans (congrArg (DerivedCategory.Q.map (mvUnitComplex U V I) ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.map_snd _ _)).trans
        (biprod.lift_snd_assoc _ _ _))))|>.trans
      ((Category.assoc _ _ _).symm.trans (biprod.lift_snd _ _).symm)

/-- On the K-injective model, the difference of the restrictions of complexes is the difference
of the derived restrictions. -/
lemma mvMiddleDerivedIso_inv_comp_Q_map_mvDiff (I : CochainComplex X.Modules ℤ)
    (hI : CochainComplex.IsKInjective I) :
    (mvMiddleDerivedIso U V I hI).inv ≫
        DerivedCategory.Q.map (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I) =
      biprod.desc
        ((pushRestrictDerivedIso U I hI).inv ≫
          DerivedCategory.Q.map
            (((resPushNat (inf_le_left : U ⊓ V ≤ U)).mapHomologicalComplex
              (ComplexShape.up ℤ)).app I))
        (-((pushRestrictDerivedIso V I hI).inv ≫
          DerivedCategory.Q.map
            (((resPushNat (inf_le_right : U ⊓ V ≤ V)).mapHomologicalComplex
              (ComplexShape.up ℤ)).app I))) := by
  have hl : (mvBicone U V I).inl ≫
      ((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I =
      ((resPushNat (inf_le_left : U ⊓ V ≤ U)).mapHomologicalComplex (ComplexShape.up ℤ)).app I := by
    ext n : 1
    exact biprod.inl_desc _ _
  have hr : (mvBicone U V I).inr ≫
      ((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I =
      -((resPushNat (inf_le_right : U ⊓ V ≤ V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).app I := by
    ext n : 1
    exact biprod.inr_desc _ _
  have hMI : (mvMiddleDerivedIso U V I hI).inv =
      biprod.map (pushRestrictDerivedIso U I hI).inv (pushRestrictDerivedIso V I hI).inv ≫
        biprod.desc (DerivedCategory.Q.map (mvBicone U V I).inl)
          (DerivedCategory.Q.map (mvBicone U V I).inr) := rfl
  have hl' : DerivedCategory.Q.map (mvBicone U V I).inl ≫
      DerivedCategory.Q.map (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I) =
      DerivedCategory.Q.map (((resPushNat (inf_le_left : U ⊓ V ≤ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).app I) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg _ hl)
  have hr' : DerivedCategory.Q.map (mvBicone U V I).inr ≫
      DerivedCategory.Q.map (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I) =
      -DerivedCategory.Q.map (((resPushNat (inf_le_right : U ⊓ V ≤ V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).app I) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg _ hr).trans DerivedCategory.Q.map_neg)
  rw [hMI]
  apply biprod.hom_ext'
  · exact ((congrArg (biprod.inl ≫ ·) (Category.assoc _ _ _)).trans
      ((biprod.inl_map_assoc _ _ _).trans (congrArg (_ ≫ ·)
        ((biprod.inl_desc_assoc _ _ _).trans hl')))).trans (biprod.inl_desc _ _).symm
  · exact ((congrArg (biprod.inr ≫ ·) (Category.assoc _ _ _)).trans
      ((biprod.inr_map_assoc _ _ _).trans ((congrArg (_ ≫ ·)
        ((biprod.inr_desc_assoc _ _ _).trans hr')).trans (Preadditive.comp_neg _ _)))).trans
      (biprod.inr_desc _ _).symm

/-! ### The triangle -/

/-- The connecting map `Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ K⟦1⟧` of the Mayer--Vietoris triangle of a
cover `X = U ∪ V`: the connecting map of the short exact sequence of complexes
`Stacks.Duality.Coherator.mvSelfShortComplex` on the K-injective model of `K`. -/
def mayerVietorisDerivedδ (hUV : U ⊔ V = ⊤) (K : DerivedCategory X.Modules) :
    (restrictPushforwardFunctor (U ⊓ V)).obj K ⟶ K⟦(1 : ℤ)⟧ :=
  (restrictPushforwardFunctor (U ⊓ V)).map (kInjectiveModelIso K).inv ≫
    (pushRestrictDerivedIso (U ⊓ V) (kInjectiveModel K) inferInstance).inv ≫
    DerivedCategory.triangleOfSESδ
      (mvSelfShortComplex_shortExact U V hUV (kInjectiveModel K) (kInjectiveModel_injective K)) ≫
    (kInjectiveModelIso K).hom⟦(1 : ℤ)⟧'

/-- **The Mayer--Vietoris triangle of a cover of a scheme by two opens**, with its maps:

`K ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ K⟦1⟧`,

where the first map is the pair of units of `j_W^* ⊣ Rj_{W,*}`, the second is the difference
`(a, b) ↦ a|_{U ∩ V} - b|_{U ∩ V}` of the restriction maps
`Stacks.Duality.Coherator.restrictPushforwardRes`, and the third is the connecting map
`Stacks.Duality.Coherator.mayerVietorisDerivedδ`. -/
def mayerVietorisDerivedTriangle (hUV : U ⊔ V = ⊤) (K : DerivedCategory X.Modules) :
    Triangle (DerivedCategory X.Modules) :=
  Triangle.mk
    (biprod.lift ((OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).unit.app K)
      ((OpenImmersion.derivedRestrictPushforwardAdjunction V.ι).unit.app K))
    (biprod.desc (restrictPushforwardRes (inf_le_left : U ⊓ V ≤ U) K)
      (-restrictPushforwardRes (inf_le_right : U ⊓ V ≤ V) K))
    (mayerVietorisDerivedδ U V hUV K)

section

variable (hUV : U ⊔ V = ⊤) (K : DerivedCategory X.Modules)

/-- The first square of the isomorphism from the triangle of the short exact sequence on the
K-injective model to `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle`. -/
lemma mayerVietorisDerivedTriangle_comm₁ :
    DerivedCategory.Q.map (mvUnitComplex U V (kInjectiveModel K)) ≫
        ((mvMiddleDerivedIso U V (kInjectiveModel K) inferInstance).hom ≫
          biprod.map ((restrictPushforwardFunctor U).map (kInjectiveModelIso K).hom)
            ((restrictPushforwardFunctor V).map (kInjectiveModelIso K).hom)) =
      (kInjectiveModelIso K).hom ≫
        biprod.lift ((OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).unit.app K)
          ((OpenImmersion.derivedRestrictPushforwardAdjunction V.ι).unit.app K) := by
  rw [reassoc_of% (Q_map_mvUnitComplex_comp_mvMiddleDerivedIso U V (kInjectiveModel K)
    inferInstance)]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst]
    exact (biprod.lift_fst_assoc _ _ _).trans
      ((OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).unit.naturality _).symm
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd]
    exact (biprod.lift_snd_assoc _ _ _).trans
      ((OpenImmersion.derivedRestrictPushforwardAdjunction V.ι).unit.naturality _).symm

/-- The second square of the isomorphism from the triangle of the short exact sequence on the
K-injective model to `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle`. -/
lemma mayerVietorisDerivedTriangle_comm₂ :
    DerivedCategory.Q.map
        (((mvDiffNat U V).mapHomologicalComplex (ComplexShape.up ℤ)).app (kInjectiveModel K)) ≫
        ((pushRestrictDerivedIso (U ⊓ V) (kInjectiveModel K) inferInstance).hom ≫
          (restrictPushforwardFunctor (U ⊓ V)).map (kInjectiveModelIso K).hom) =
      ((mvMiddleDerivedIso U V (kInjectiveModel K) inferInstance).hom ≫
          biprod.map ((restrictPushforwardFunctor U).map (kInjectiveModelIso K).hom)
            ((restrictPushforwardFunctor V).map (kInjectiveModelIso K).hom)) ≫
        biprod.desc (restrictPushforwardRes (inf_le_left : U ⊓ V ≤ U) K)
          (-restrictPushforwardRes (inf_le_right : U ⊓ V ≤ V) K) := by
  rw [← cancel_epi (mvMiddleDerivedIso U V (kInjectiveModel K) inferInstance).inv,
    Category.assoc, Iso.inv_hom_id_assoc,
    reassoc_of% (mvMiddleDerivedIso_inv_comp_Q_map_mvDiff U V (kInjectiveModel K) inferInstance)]
  apply biprod.hom_ext'
  · simp [restrictPushforwardRes]
  · simp [restrictPushforwardRes]

/-- The third square of the isomorphism from the triangle of the short exact sequence on the
K-injective model to `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle`. -/
lemma mayerVietorisDerivedTriangle_comm₃ :
    DerivedCategory.triangleOfSESδ
        (mvSelfShortComplex_shortExact U V hUV (kInjectiveModel K) (kInjectiveModel_injective K)) ≫
        (kInjectiveModelIso K).hom⟦(1 : ℤ)⟧' =
      ((pushRestrictDerivedIso (U ⊓ V) (kInjectiveModel K) inferInstance).hom ≫
          (restrictPushforwardFunctor (U ⊓ V)).map (kInjectiveModelIso K).hom) ≫
        mayerVietorisDerivedδ U V hUV K := by
  simp [mayerVietorisDerivedδ]
  rfl

end

/-- **[Stacks, Tag 08BV] for a scheme, with its maps.** If the opens `U`, `V` cover the scheme
`X`, then for every object `K` of `D(𝒪_X)` the triangle
`Stacks.Duality.Coherator.mayerVietorisDerivedTriangle`

`K ⟶ Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V) ⟶ Rj_{U ∩ V,*}(K|_{U ∩ V}) ⟶ K⟦1⟧`

is distinguished: it is isomorphic to the triangle of the short exact sequence
`Stacks.Duality.Coherator.mvSelfShortComplex` on the K-injective model of `K`. -/
theorem mayerVietorisDerivedTriangle_distinguished (hUV : U ⊔ V = ⊤)
    (K : DerivedCategory X.Modules) :
    mayerVietorisDerivedTriangle U V hUV K ∈ distTriang (DerivedCategory X.Modules) := by
  have hSE := mvSelfShortComplex_shortExact U V hUV (kInjectiveModel K)
    (kInjectiveModel_injective K)
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hSE) _
    (Iso.symm ?_)
  exact Triangle.isoMk _ _ (kInjectiveModelIso K)
    (mvMiddleDerivedIso U V (kInjectiveModel K) inferInstance ≪≫
      biprod.mapIso ((restrictPushforwardFunctor U).mapIso (kInjectiveModelIso K))
        ((restrictPushforwardFunctor V).mapIso (kInjectiveModelIso K)))
    (pushRestrictDerivedIso (U ⊓ V) (kInjectiveModel K) inferInstance ≪≫
      (restrictPushforwardFunctor (U ⊓ V)).mapIso (kInjectiveModelIso K))
    (mayerVietorisDerivedTriangle_comm₁ U V K) (mayerVietorisDerivedTriangle_comm₂ U V K)
    (mayerVietorisDerivedTriangle_comm₃ U V hUV K)

end Stacks.Duality.Coherator

end
