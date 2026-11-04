module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.BundleEmbeddingTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.QuotientComparisonLocal

/-!
# The twist of `𝐏(ℰ)` restricted to `𝐏(ℱ)`

Let `X` be an algebraic space and `q : ℰ ⟶ ℱ` a surjection of finite locally free `𝒪_X`-modules,
surjective on every étale chart. The morphism `ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)` of projective bundles glued
from the closed immersions of the chart bundles pulls the twist back to the twist:

  `ι^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℱ)}(1)`,

by the isomorphism carrying the pulled-back tautological quotient `π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ ⟶ ι^*𝒪(1)`
to the composite `π_ℱ^*ℰ ⟶ π_ℱ^*ℱ ⟶ 𝒪_{𝐏(ℱ)}(1)`. Both are quotients of `π_ℱ^*ℰ`, so by
`AlgebraicGeometry.Space.PrivateChern.exists_iso_comp_eq_of_modulePullback` it suffices to compare
them on the presenting chart `𝐏(ℱ_U)` of `𝐏(ℱ)`; read on the scheme `𝐏(ℱ_U)` (Stacks 03DX (2))
they are the pulled-back tautological quotient of `𝐏(ℰ_U)` and the tautological quotient of
`𝐏(ℱ_U)` precomposed with `q_U`, which agree by
`AlgebraicGeometry.Space.PrivateChern.exists_situationEmbedding_twistIso`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_projectiveBundleEmbedding_twistIso`: the
  restriction of `𝒪_{𝐏(ℰ)}(1)` to `𝐏(ℱ)` is `𝒪_{𝐏(ℱ)}(1)`, compatibly with the tautological
  quotients.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_comp_eq_of_readingMap`: two quotients of a
  quasi-coherent module on a representable algebraic space agree as soon as their readings on the
  scheme agree.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_readingMap_embedding`: the comparison of the two
  readings on a chart, at variable data.
* `AlgebraicGeometry.Space.PrivateChern.projectiveBundleAtlas_comp_projectiveBundleEmbedding`:
  the glued morphism restricts on the presenting chart to the closed immersion of chart bundles.

## Implementation notes

The comparisons are proved at variable data (arbitrary charts, projections and quotients) and
instantiated once. The scheme-level comparison of
`AlgebraicGeometry.Space.PrivateChern.exists_situationEmbedding_twistIso` is stated for the
projective bundles of `Stacks.RelativeProj.projectiveBundle`, while the chart of `𝐏(ℰ)` carries
the scheme of a site object; the two are identified by
`AlgebraicGeometry.Space.PrivateChern.exists_iso_pullback_map_comp_eq_of_heq`, through
heterogeneous equalities of the data, which are definitional.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-! ### Quotients up to an isomorphism of the target -/

section Quotients

variable {C : Type*} [Category C] {M A A' A'' : C}

/-- Every morphism out of `M` agrees with itself up to an automorphism of its target. -/
theorem exists_iso_comp_eq_refl (x : M ⟶ A) : ∃ θ : A ≅ A, x ≫ θ.hom = x :=
  ⟨Iso.refl A, Category.comp_id x⟩

/-- Agreeing up to an isomorphism of the targets is symmetric. -/
theorem exists_iso_comp_eq_symm {x : M ⟶ A} {y : M ⟶ A'} :
    (∃ θ : A ≅ A', x ≫ θ.hom = y) → ∃ θ : A' ≅ A, y ≫ θ.hom = x := by
  rintro ⟨θ, hθ⟩
  exact ⟨θ.symm, by rw [← hθ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

/-- Agreeing up to an isomorphism of the targets is transitive. -/
theorem exists_iso_comp_eq_trans {x : M ⟶ A} {y : M ⟶ A'} {z : M ⟶ A''} :
    (∃ θ : A ≅ A', x ≫ θ.hom = y) → (∃ θ : A' ≅ A'', y ≫ θ.hom = z) →
      ∃ θ : A ≅ A'', x ≫ θ.hom = z := by
  rintro ⟨θ, hθ⟩ ⟨θ', hθ'⟩
  exact ⟨θ ≪≫ θ', by rw [Iso.trans_hom, ← Category.assoc, hθ, hθ']⟩

/-- A morphism agrees with its composite with an isomorphism `e`, up to `e`. -/
theorem exists_iso_comp_eq_of_iso (x : M ⟶ A) (e : A ≅ A') :
    ∃ θ : A ≅ A', x ≫ θ.hom = x ≫ e.hom :=
  ⟨e, rfl⟩

/-- Agreeing up to an isomorphism of the targets is preserved by precomposition. -/
theorem exists_iso_comp_eq_precomp {M' : C} (a : M' ⟶ M) {x : M ⟶ A} {y : M ⟶ A'} :
    (∃ θ : A ≅ A', x ≫ θ.hom = y) → ∃ θ : A ≅ A', (a ≫ x) ≫ θ.hom = a ≫ y := by
  rintro ⟨θ, hθ⟩
  exact ⟨θ, by rw [Category.assoc, hθ]⟩

/-- Agreeing up to an isomorphism of the targets is preserved by every functor. -/
theorem exists_iso_comp_eq_map {D : Type*} [Category D] (G : C ⥤ D) {x : M ⟶ A} {y : M ⟶ A'} :
    (∃ θ : A ≅ A', x ≫ θ.hom = y) → ∃ θ : G.obj A ≅ G.obj A', G.map x ≫ θ.hom = G.map y := by
  rintro ⟨θ, hθ⟩
  exact ⟨G.mapIso θ, by rw [Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, hθ]⟩

end Quotients

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Reading modules on a represented space -/

section Reading


/-- The inverse of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, on the modules
of the represented algebraic space. -/
abbrev readingInverse (T : BigFppfOver B S hS) :
    Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2 ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :=
  (representedSmallEtaleModuleEquivalence B S hS T).inverse

/-- **The reading of a morphism of modules on a represented algebraic space** on its scheme. -/
abbrev readingMap (T : BigFppfOver B S hS)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (f : M ⟶ N) :
    representedZariskiModule B S hS T M ⟶ representedZariskiModule B S hS T N :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map f)

/-- The reading of an isomorphism of modules on a represented algebraic space. -/
abbrev readingIso (T : BigFppfOver B S hS)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (e : M ≅ N) :
    representedZariskiModule B S hS T M ≅ representedZariskiModule B S hS T N :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso e)

/-- The reading of a composite is the composite of the readings. -/
theorem readingMap_comp (T : BigFppfOver B S hS)
    {M N K : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (f : M ⟶ N) (g : N ⟶ K) :
    readingMap T (f ≫ g) = readingMap T f ≫ readingMap T g := by
  simp only [readingMap, Functor.map_comp]

/-- The forward map of the reading of an isomorphism is the reading of its forward map. -/
theorem readingIso_hom (T : BigFppfOver B S hS)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (e : M ≅ N) :
    (readingIso T e).hom = readingMap T e.hom := by
  simp only [readingIso, readingMap, Functor.mapIso_hom]

/-- The inverse of the reading of an isomorphism is the reading of its inverse. -/
theorem readingIso_inv (T : BigFppfOver B S hS)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (e : M ≅ N) :
    (readingIso T e).inv = readingMap T e.inv := by
  simp only [readingIso, readingMap, Functor.mapIso_inv]

/-- **Two quotients of a quasi-coherent module on a representable algebraic space agree as soon
as their readings on the scheme agree**, reading being fully faithful on quasi-coherent modules
(Stacks 03DX (2)). -/
theorem exists_iso_comp_eq_of_readingMap {T : BigFppfOver B S hS}
    {M A A' : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (hM : M.IsQuasicoherentOnSite) (hA : A.IsQuasicoherentOnSite)
    (hA' : A'.IsQuasicoherentOnSite) (x : M ⟶ A) (y : M ⟶ A')
    (h : ∃ θ : representedZariskiModule B S hS T A ≅ representedZariskiModule B S hS T A',
      readingMap T x ≫ θ.hom = readingMap T y) :
    ∃ θ : A ≅ A', x ≫ θ.hom = y := by
  obtain ⟨θ, hθ⟩ := h
  obtain ⟨t, ht : readingMap T t = θ.hom⟩ :=
    (QuasiCoherentDescent.bijective_representedZariski_map B S hS A A' hA).2 θ.hom
  obtain ⟨t', ht' : readingMap T t' = θ.inv⟩ :=
    (QuasiCoherentDescent.bijective_representedZariski_map B S hS A' A hA').2 θ.inv
  have inv_of_reading : ∀ {Z Z'} (hZ : SheafOfModules.IsQuasicoherentOnSite Z) (u : Z ⟶ Z')
      (v : Z' ⟶ Z)
      (e : representedZariskiModule B S hS T Z ≅ representedZariskiModule B S hS T Z'),
      readingMap T u = e.hom → readingMap T v = e.inv → u ≫ v = 𝟙 Z := fun {Z _} hZ u v e hu hv =>
    (QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _ hZ).1 (by
      change readingMap T (u ≫ v) = readingMap T (𝟙 Z)
      rw [readingMap_comp, hu, hv, e.hom_inv_id]
      simp only [readingMap, CategoryTheory.Functor.map_id])
  refine ⟨⟨t, t', inv_of_reading hA t t' θ ht ht', inv_of_reading hA' t' t θ.symm ht' ht⟩, ?_⟩
  refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS M A' hM).1 ?_
  change readingMap T (x ≫ t) = readingMap T y
  rw [readingMap_comp, ht, hθ]

end Reading

/-- **The comparisons of inverse images around the square `φ_ℱ ≫ ι = g ≫ φ_ℰ`**: reading
`(φ_ℱ ≫ π_ℱ)^*ℰ` through `π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ` and the square is reading it through `φ_ℱ ≫ π_ℱ`
directly. -/
theorem pullbackComparison_square_inv {X PE PF T T' : AlgebraicSpaces B S hS}
    (πE : PE ⟶ X) (πF : PF ⟶ X) (ι : PF ⟶ PE) (hιπ : ι ≫ πE = πF) (φE : T ⟶ PE) (φF : T' ⟶ PF)
    (g : T' ⟶ T) (ψ' : T' ⟶ PE) (hglue : φF ≫ ι = ψ') (hg : g ≫ φE = ψ') (ψ : T' ⟶ X)
    (hψ : φF ≫ πF = ψ) (w' : g ≫ (φE ≫ πE) = ψ) (E : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS φF).map
        (QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS φF ι ψ' hglue
        ((modulePullback B S hS πE).obj E)).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g φE ψ' hg
        ((modulePullback B S hS πE).obj E)).hom ≫
      (modulePullback B S hS g).map
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g (φE ≫ πE) ψ w' E).inv =
    (QuasiCoherentDescent.pullbackComparison B S hS φF πF ψ hψ E).inv := by
  have hst : ψ' ≫ πE = ψ := by rw [← hglue, Category.assoc, hιπ, hψ]
  have h1 := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS φF ι πE πF hιπ ψ' hglue ψ
    hψ hst E
  have h2 := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS g φE πE (φE ≫ πE) rfl ψ' hg ψ
    w' hst E
  have h1' : (modulePullback B S hS φF).map
        (QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS φF ι ψ' hglue
        ((modulePullback B S hS πE).obj E)).inv =
      (QuasiCoherentDescent.pullbackComparison B S hS φF πF ψ hψ E).inv ≫
        (QuasiCoherentDescent.pullbackComparison B S hS ψ' πE ψ hst E).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2' : (QuasiCoherentDescent.pullbackComparison B S hS ψ' πE ψ hst E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g φE ψ' hg
        ((modulePullback B S hS πE).obj E)).hom ≫
      (modulePullback B S hS g).map
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g (φE ≫ πE) ψ w' E).inv = 𝟙 _ := by
    rw [← Category.assoc, ← h2, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  rw [← Category.assoc, h1', Category.assoc, h2', Category.comp_id]


/-! ### The comparisons of readings, written with `readingMap` -/

section Readings

variable {X : AlgebraicSpaces B S hS} (E : Modules.{u, u} B S hS X.1 X.2)
  (hE : E.IsQuasicoherentOnSite)

/-- The forward map of `schemeReadingPullbackIso` written out: the comparison of the reading
with inverse images, followed by the reading of the inverse of the pullback comparison. -/
theorem schemeReadingPullbackIso_hom_eq_restrictModule {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    (schemeReadingPullbackIso E hE g w).hom =
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          ((modulePullback B S hS ψ).obj E)
          (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ)).hom ≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
            E).inv) := by
  rw [schemeReadingPullbackIso_eq, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    Iso.symm_hom]

/-- `AlgebraicGeometry.Space.quotientReadingOf` written out. -/
theorem quotientReadingOf_eq {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψU : representedAlgebraicSpace B S hS T ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading E ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) :
    quotientReadingOf E hE wρ univ εL κ₀ =
      readingMap T κ₀.hom ≫ (schemeReadingPullbackIso E hE ρ wρ).inv ≫ univ ≫ εL.inv := by
  unfold quotientReadingOf
  rw [Functor.mapIso_hom, Functor.mapIso_hom]

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_naturality`, with the readings
through `AlgebraicGeometry.Space.PrivateChern.readingInverse`. -/
theorem representedZariskiModulePullbackIso_naturality_readingInverse {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N) :
    (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
        ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ((readingInverse T).map f)) ≫
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        N hN).hom =
    (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        M hM).hom ≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((readingInverse T').map ((modulePullback B S hS (representedSpaceMap B S hS g)).map f)) :=
  representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) hM hN f

/-- The comparison of the reading with inverse images
(`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`), on modules of the represented
algebraic space. -/
def readingPullbackComparison {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2) (hM : M.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback (siteSchemeHom g)).obj
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj ((readingInverse T).obj M)) ≅
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj ((readingInverse T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj M)) :=
  representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g) M hM

omit E hE in
/-- `readingPullbackComparison` is natural in the module. -/
theorem readingPullbackComparison_naturality {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N) :
    (Scheme.Modules.pullback (siteSchemeHom g)).map
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ((readingInverse T).map f)) ≫
      (readingPullbackComparison g N hN).hom =
      (readingPullbackComparison g M hM).hom ≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map ((readingInverse T').map
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map f)) :=
  representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) hM hN f

omit E hE in
/-- **A morphism whose inverse image to `T'` vanishes reads as a morphism whose inverse image along
`T' ⟶ T` vanishes**, for quasi-coherent modules. -/
theorem pullback_map_readingMap_eq_zero {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : (modulePullback B S hS (representedSpaceMap B S hS g)).map f = 0) :
    (Scheme.Modules.pullback (siteSchemeHom g)).map
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((readingInverse T).map f)) = 0 := by
  have : (readingInverse T').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).PreservesZeroMorphisms :=
    have := (SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).isRightAdjoint
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have h := readingPullbackComparison_naturality g hM hN f
  rw [hf, Functor.map_zero, Functor.map_zero, Limits.comp_zero] at h
  have h' := congrArg (fun k => k ≫ (readingPullbackComparison g N hN).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Limits.zero_comp] using h'

omit E hE in
/-- `readingPullbackComparison` is natural in the module, for isomorphisms of modules. -/
theorem readingPullbackComparison_naturality_iso {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (ψ : M ≅ N) :
    (Scheme.Modules.pullback (siteSchemeHom g)).mapIso
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((readingInverse T).mapIso ψ)) ≪≫
      readingPullbackComparison g N hN =
      readingPullbackComparison g M hM ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso ((readingInverse T').mapIso
          ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso ψ)) :=
  representedZariskiModulePullbackIso_naturality_iso B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) hM hN ψ

/-- `schemeReadingPullbackIso` is `readingPullbackComparison` followed by the reading of the
inverse of the pullback comparison. -/
theorem schemeReadingPullbackIso_eq_comparison {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    schemeReadingPullbackIso E hE g w =
      readingPullbackComparison g ((modulePullback B S hS ψ).obj E)
          (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ) ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso ((readingInverse T').mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
            E).symm) :=
  schemeReadingPullbackIso_eq E hE g w

/-- `AlgebraicGeometry.Space.quotientReadingOf` written out, with the readings
through `AlgebraicGeometry.Space.PrivateChern.readingInverse`. -/
theorem quotientReadingOf_eq_readingInverse {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading E ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (εL : representedZariskiModule B S hS T L ≅ TU)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) :
    quotientReadingOf E hE wρ univ εL κ₀ =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((readingInverse T).mapIso κ₀)).hom ≫
        (schemeReadingPullbackIso E hE ρ wρ).inv ≫ univ ≫ εL.inv :=
  rfl

end Readings

section SpaceSquare

variable {X PE PF T T' : AlgebraicSpaces B S hS} {E : Modules.{u, u} B S hS X.1 X.2}
  (πE : PE ⟶ X) (πF : PF ⟶ X) (ι : PF ⟶ PE) (hιπ : ι ≫ πE = πF) (φE : T ⟶ PE) (φF : T' ⟶ PF)
  (g : T' ⟶ T) (hglue : φF ≫ ι = g ≫ φE)

include hιπ hglue in
/-- **The space-level square** for the pullback comparisons, as an identity of morphisms
through the composite `φE ≫ πE`. -/
theorem pullbackComparison_square_inv_of_comp (w' : g ≫ (φE ≫ πE) = φF ≫ πF) :
    (modulePullback B S hS φF).map
        (QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue
        ((modulePullback B S hS πE).obj E)).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl
        ((modulePullback B S hS πE).obj E)).hom ≫
      (modulePullback B S hS g).map
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g (φE ≫ πE) _ w' E).inv =
    (QuasiCoherentDescent.pullbackComparison B S hS φF πF _ rfl E).inv :=
  pullbackComparison_square_inv πE πF ι hιπ φE φF g _ hglue rfl (φF ≫ πF) rfl w' E

include hιπ hglue in
/-- **The space-level square**, as an identity of isomorphisms. -/
theorem squareComparison_trans (w' : g ≫ (φE ≫ πE) = φF ≫ πF) :
    ((modulePullback B S hS φF).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E) ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue
          ((modulePullback B S hS πE).obj E)).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl
          ((modulePullback B S hS πE).obj E)) ≪≫
        (modulePullback B S hS g).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS g (φE ≫ πE) (φF ≫ πF) w' E).symm =
      (QuasiCoherentDescent.pullbackComparison B S hS φF πF _ rfl E).symm := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
    Category.assoc]
  exact pullbackComparison_square_inv_of_comp πE πF ι hιπ φE φF g hglue w'

/-- **The inverse image along `φ_ℱ` of the pulled-back quotient `π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ ⟶ ι^*𝒜`**
is the inverse image along `g` of the quotient `φ_ℰ^*τ`, through the comparisons. -/
theorem modulePullback_map_comparison_comp {A : Modules.{u, u} B S hS PE.1 PE.2}
    (τ : (modulePullback B S hS πE).obj E ⟶ A) {L : Modules.{u, u} B S hS T.1 T.2}
    (aE : (modulePullback B S hS φE).obj A ≅ L)
    (χ : (modulePullback B S hS φE).obj ((modulePullback B S hS πE).obj E) ⟶ L)
    (hτ : (modulePullback B S hS φE).map τ ≫ aE.hom = χ) :
    (modulePullback B S hS φF).map
        ((QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
          (modulePullback B S hS ι).map τ) =
      ((modulePullback B S hS φF).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E) ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue
          ((modulePullback B S hS πE).obj E)).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl
          ((modulePullback B S hS πE).obj E)).hom ≫ (modulePullback B S hS g).map χ ≫
        ((modulePullback B S hS g).mapIso aE.symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl A).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue A).hom := by
  have n1 := QuasiCoherentDescent.pullbackComparison_naturality B S hS φF ι _ hglue τ
  have n2 := QuasiCoherentDescent.pullbackComparison_naturality B S hS g φE _ rfl τ
  have hχ' : (modulePullback B S hS g).map χ ≫ (modulePullback B S hS g).map aE.inv =
      (modulePullback B S hS g).map ((modulePullback B S hS φE).map τ) := by
    rw [← CategoryTheory.Functor.map_comp, ← hτ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have n2' : (QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl
        ((modulePullback B S hS πE).obj E)).hom ≫
      (modulePullback B S hS g).map ((modulePullback B S hS φE).map τ) ≫
      (QuasiCoherentDescent.pullbackComparison B S hS g φE _ rfl A).inv =
      (modulePullback B S hS (g ≫ φE)).map τ := by
    rw [← Category.assoc, ← n2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have n1' : (QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue
        ((modulePullback B S hS πE).obj E)).inv ≫
      (modulePullback B S hS (g ≫ φE)).map τ ≫
      (QuasiCoherentDescent.pullbackComparison B S hS φF ι _ hglue A).hom =
      (modulePullback B S hS φF).map ((modulePullback B S hS ι).map τ) := by
    rw [n1, Iso.inv_hom_id_assoc]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hχ', reassoc_of% n2', n1']

end SpaceSquare

private theorem inv_shape {C₀ : Type*} [Category C₀] {o₁ o₂ o₃ o₄ o₅ : C₀} (a : o₁ ≅ o₂)
    (b : o₂ ≅ o₃) (c : o₃ ≅ o₄) (d : o₁ ≅ o₅) (e : o₅ ≅ o₄)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) : c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
  have h' : a ≪≫ b ≪≫ c = d ≪≫ e := Iso.ext (by simpa only [Iso.trans_hom] using h)
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv h'

/-- The shape of the comparison of readings around the square, at an abstract category. -/
private theorem source_shape {C₀ : Type*} [Category C₀]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ : C₀} {x₁ : o₀ ⟶ o₁} {x₂ : o₁ ⟶ o₂} {x₃ : o₂ ⟶ o₃}
    (r : o₄ ≅ o₃) {n : o₄ ⟶ o₅} (r' : o₅ ≅ o₆) {y : o₃ ⟶ o₆} {p : o₆ ⟶ o₇} {k : o₀ ⟶ o₇}
    (M : o₅ ≅ o₇) {m : o₅ ⟶ o₈} {c : o₇ ⟶ o₉} {cg : o₉ ⟶ o₁₀} {cp : o₁₀ ⟶ o₈}
    (hcoc : M.inv ≫ m = (c ≫ cg) ≫ cp) (hsq : x₁ ≫ x₂ ≫ x₃ ≫ y ≫ p = k)
    (hM : M.hom = r'.hom ≫ p) (hnat : n ≫ r'.hom = r.hom ≫ y) :
    x₁ ≫ x₂ ≫ x₃ ≫ r.inv ≫ n ≫ m = k ≫ c ≫ cg ≫ cp := by
  have h1 : r.inv ≫ n = y ≫ r'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : p ≫ M.inv = r'.inv := by
    rw [Iso.comp_inv_eq, hM, Iso.inv_hom_id_assoc]
  rw [← Category.assoc c, ← hcoc, ← hsq]
  simp only [Category.assoc]
  rw [reassoc_of% h1, ← Category.assoc p, h2]

/-- The shape of the comparison of readings around the square, as an identity of isomorphisms. -/
private theorem iso_shape {C₀ C₁ : Type*} [Category C₀] [Category C₁] (Fσ : C₁ ⥤ C₀)
    {a₀ a₁ m₁ : C₁} {o₂ o₃ o₄ o₅ o₆ : C₀}
    {a : a₀ ≅ a₁} {r' : Fσ.obj a₁ ≅ o₂} {r : Fσ.obj a₀ ≅ o₃} {b : o₃ ≅ o₂}
    {M : Fσ.obj a₁ ≅ o₄} {p : o₂ ≅ o₄} {m : m₁ ≅ a₁} {c : Fσ.obj m₁ ≅ o₅} {d : o₅ ≅ o₆}
    {e : o₆ ≅ o₄}
    (hN : Fσ.mapIso a ≪≫ r' = r ≪≫ b) (hH : M = r' ≪≫ p)
    (hC : Fσ.mapIso m ≪≫ M = c ≪≫ d ≪≫ e) :
    r.symm ≪≫ Fσ.mapIso a ≪≫ (Fσ.mapIso m).symm ≪≫ c ≪≫ d = b ≪≫ p ≪≫ e.symm := by
  have hC' : (Fσ.mapIso m).symm ≪≫ c ≪≫ d = M ≪≫ e.symm := by
    ext
    have h := congrArg Iso.hom hC
    simp only [Iso.trans_hom, Functor.mapIso_hom] at h
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    rw [← cancel_epi (Fσ.map m.hom), ← Fσ.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc, h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH' : M ≪≫ e.symm = r' ≪≫ p ≪≫ e.symm := by rw [hH, Iso.trans_assoc]
  have hN' : r.symm ≪≫ Fσ.mapIso a ≪≫ r' = b := by
    rw [hN, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  have hC'' : r.symm ≪≫ Fσ.mapIso a ≪≫ (Fσ.mapIso m).symm ≪≫ c ≪≫ d =
      r.symm ≪≫ Fσ.mapIso a ≪≫ (M ≪≫ e.symm) := by
    rw [← hC']
  rw [hC'', hH']
  simp only [← Iso.trans_assoc] at hN' ⊢
  rw [hN']

/-- The shape of the reading of the pulled-back tautological quotient of `𝐏(ℰ)` on the chart of
`𝐏(ℱ)`, at abstract categories. -/
private theorem twist_shape {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀]
    [Category D₁] (Fσ : C₁ ⥤ C₀) (R₁ : D₀ ⥤ C₀) (R₂ : D₁ ⥤ D₀)
    {A₁ L₁ a₁ m₁ TU : C₁} {X₁ G₁ H₁ Z₁ o₂' o₄' : D₁} {o₅ o₆ W : C₀}
    {x : R₁.obj (R₂.obj X₁) ⟶ R₁.obj (R₂.obj Z₁)} {Ssp : X₁ ≅ G₁} {gχ : G₁ ⟶ H₁} {t : H₁ ≅ Z₁}
    {Rf : A₁ ⟶ L₁} {rL : Fσ.obj L₁ ≅ R₁.obj (R₂.obj H₁)} {r : Fσ.obj A₁ ≅ R₁.obj (R₂.obj G₁)}
    {a : A₁ ≅ a₁} {m : m₁ ≅ a₁} {univ : m₁ ⟶ TU} {ε : L₁ ≅ TU} {c : Fσ.obj m₁ ≅ o₅} {d : o₅ ≅ o₆}
    {b : G₁ ≅ o₂'} {p : o₂' ≅ o₄'} {e : o₆ ≅ R₁.obj (R₂.obj o₄')} {K : X₁ ≅ o₄'} {z : o₆ ⟶ W}
    {θ₀ : Fσ.obj TU ≅ W}
    (hnat : Fσ.map Rf ≫ rL.hom = r.hom ≫ R₁.map (R₂.map gχ))
    (hx : x = R₁.map (R₂.map (Ssp.hom ≫ gχ ≫ t.hom)))
    (hRf : Rf = a.hom ≫ m.inv ≫ univ ≫ ε.inv)
    (key : r.symm ≪≫ Fσ.mapIso a ≪≫ (Fσ.mapIso m).symm ≪≫ c ≪≫ d =
      R₁.mapIso (R₂.mapIso b) ≪≫ R₁.mapIso (R₂.mapIso p) ≪≫ e.symm)
    (sq : Ssp ≪≫ b ≪≫ p = K) (hspec : Fσ.map univ ≫ θ₀.hom = c.hom ≫ d.hom ≫ z) :
    ∃ θ : R₁.obj (R₂.obj Z₁) ≅ W, x ≫ θ.hom = (R₁.mapIso (R₂.mapIso K)).hom ≫ e.inv ≫ z := by
  refine ⟨R₁.mapIso (R₂.mapIso t.symm) ≪≫ rL.symm ≪≫ Fσ.mapIso ε ≪≫ θ₀, ?_⟩
  have hkey := congrArg Iso.hom key
  have hsq := congrArg (fun i => (R₁.mapIso (R₂.mapIso i)).hom) sq
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp] at hkey hsq
  have h1 : R₁.map (R₂.map gχ) ≫ rL.inv = r.inv ≫ Fσ.map Rf := by
    rw [Iso.comp_inv_eq, Category.assoc, hnat, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, hx, Category.assoc,
    Functor.map_comp]
  rw [← R₁.map_comp_assoc (R₂.map t.hom) (R₂.map t.inv), ← R₂.map_comp, Iso.hom_inv_id, R₂.map_id,
    R₁.map_id, Category.id_comp]
  rw [reassoc_of% h1, ← Fσ.map_comp_assoc, hRf]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Fσ.map_comp]
  rw [hspec, reassoc_of% hkey, ← reassoc_of% hsq]

section Square

variable {X PE PF : AlgebraicSpaces B S hS} {E : Modules.{u, u} B S hS X.1 X.2}
  (hE : E.IsQuasicoherentOnSite) (πE : PE ⟶ X) (πF : PF ⟶ X) (ι : PF ⟶ PE) (hιπ : ι ≫ πE = πF)
  {TE TF Y : BigFppfOver B S hS} (s : TF ⟶ TE) {ρE : TE ⟶ Y} {ρF : TF ⟶ Y} (hs : s ≫ ρE = ρF)
  {ψY : representedAlgebraicSpace B S hS Y ⟶ X} (φE : representedAlgebraicSpace B S hS TE ⟶ PE)
  (φF : representedAlgebraicSpace B S hS TF ⟶ PF)
  (hglue : φF ≫ ι = representedSpaceMap B S hS s ≫ φE)
  (wρE : representedSpaceMap B S hS ρE ≫ ψY = φE ≫ πE)
  (wρF : representedSpaceMap B S hS ρF ≫ ψY = φF ≫ πF)

omit hglue in
/-- The comparison of readings along `s ≫ ρ_ℰ` is the one along `ρ_ℱ`, up to
`Scheme.Modules.pullbackCongr`, as an identity of isomorphisms. -/
theorem schemeReadingPullbackIso_congr_iso
    (w'' : representedSpaceMap B S hS (s ≫ ρE) ≫ ψY = φF ≫ πF) :
    schemeReadingPullbackIso E hE (s ≫ ρE) w'' =
      (Scheme.Modules.pullbackCongr (congrArg (fun x : TF ⟶ Y => siteSchemeHom x) hs)).app
        (schemeReading E ψY) ≪≫ schemeReadingPullbackIso E hE ρF wρF :=
  Iso.ext (pullbackCongr_hom_app_schemeReadingPullbackIso E hE hs w'' wρF).symm

include hιπ hglue in
/-- **The cocycle of the comparisons of readings along `ρ_ℱ = s ≫ ρ_ℰ`**, as an identity of
isomorphisms. -/
theorem schemeReadingPullbackIso_cocycle_square
    (w' : representedSpaceMap B S hS s ≫ (φE ≫ πE) = φF ≫ πF)
    (w'' : representedSpaceMap B S hS (s ≫ ρE) ≫ ψY = φF ≫ πF) :
    (Scheme.Modules.pullback (siteSchemeHom s)).mapIso (schemeReadingPullbackIso E hE ρE wρE) ≪≫
        schemeReadingPullbackIso E hE s w' =
      (Scheme.Modules.pullbackComp (siteSchemeHom s) (siteSchemeHom ρE)).app (schemeReading E ψY) ≪≫
        (Scheme.Modules.pullbackCongr (congrArg (fun x : TF ⟶ Y => siteSchemeHom x) hs)).app
          (schemeReading E ψY) ≪≫ schemeReadingPullbackIso E hE ρF wρF := by
  rw [schemeReadingPullbackIso_comp E hE s ρE wρE w' w'',
    schemeReadingPullbackIso_congr_iso hE πF s hs φF wρF w'']




include hιπ hs hglue in
/-- **The reading on the chart of `𝐏(ℱ)` of the pulled-back quotient
`π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ ⟶ ι^*𝒜`**, at variable data: if `φ_ℰ^*τ` reads as `univ : ρ_ℰ^*ℰ_Y ⟶ T_U` on
the chart of `𝐏(ℰ)` and the inverse image of `univ` along `s` agrees with `z` through the
comparisons, then the pulled-back quotient reads as `z`, through the comparison of readings along
`ρ_ℱ`. -/
theorem exists_iso_readingMap_comparison_comp {A : Modules.{u, u} B S hS PE.1 PE.2}
    (hA : A.IsQuasicoherentOnSite)
    (τ : (modulePullback B S hS πE).obj E ⟶ A)
    {L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS TE).1
      (representedAlgebraicSpace B S hS TE).2} (hL : L.IsQuasicoherentOnSite)
    (aE : (modulePullback B S hS φE).obj A ≅ L)
    (χ : (modulePullback B S hS φE).obj ((modulePullback B S hS πE).obj E) ⟶ L)
    (hτ : (modulePullback B S hS φE).map τ ≫ aE.hom = χ)
    {TU : ((BigFppfOver.toScheme B S hS).obj TE).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρE)).obj (schemeReading E ψY) ⟶ TU)
    (εL : representedZariskiModule B S hS TE L ≅ TU)
    (hχ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TE) TE.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS TE).inverse.map χ) =
      quotientReadingOf E hE wρE univ εL
      (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).symm)
    {Wz : ((BigFppfOver.toScheme B S hS).obj TF).Modules}
    (z : (Scheme.Modules.pullback (siteSchemeHom ρF)).obj (schemeReading E ψY) ⟶ Wz)
    (θ₀ : (Scheme.Modules.pullback (siteSchemeHom s)).obj TU ≅ Wz)
    (hsc : siteSchemeHom s ≫ siteSchemeHom ρE = siteSchemeHom ρF)
    (hspec : (Scheme.Modules.pullback (siteSchemeHom s)).map
        univ ≫ θ₀.hom =
      ((Scheme.Modules.pullbackComp (siteSchemeHom s) (siteSchemeHom ρE)).app
        (schemeReading E ψY)).hom ≫
      ((Scheme.Modules.pullbackCongr hsc).app (schemeReading E ψY)).hom ≫ z) :
    ∃ θ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS TF).inverse.obj
        ((modulePullback B S hS φF).obj ((modulePullback B S hS ι).obj A))) ≅ Wz,
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS TF).inverse.map
          ((modulePullback B S hS φF).map
        ((QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
          (modulePullback B S hS ι).map τ))) ≫ θ.hom =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS TF).inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS φF πF _ rfl E).symm)).hom ≫
        (schemeReadingPullbackIso E hE ρF wρF).inv ≫ z := by
  have w' : representedSpaceMap B S hS s ≫ (φE ≫ πE) = φF ≫ πF := by
    rw [← Category.assoc, ← hglue, Category.assoc, hιπ]
  have w'' : representedSpaceMap B S hS (s ≫ ρE) ≫ ψY = φF ≫ πF := by
    rw [hs, wρF]
  have hχ' : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TE) TE.left.property).map ((readingInverse TE).map χ) =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TE) TE.left.property).mapIso ((readingInverse TE).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).symm)).hom ≫
        (schemeReadingPullbackIso E hE ρE wρE).inv ≫ univ ≫ εL.inv :=
    hχ.trans (quotientReadingOf_eq_readingInverse E hE wρE univ εL _)
  have hspec' : (Scheme.Modules.pullback (siteSchemeHom s)).map univ ≫ θ₀.hom =
      ((Scheme.Modules.pullbackComp (siteSchemeHom s) (siteSchemeHom ρE)).app
        (schemeReading E ψY)).hom ≫
      ((Scheme.Modules.pullbackCongr (congrArg (fun x : TF ⟶ Y => siteSchemeHom x) hs)).app
          (schemeReading E ψY)).hom ≫ z := hspec
  exact twist_shape (Scheme.Modules.pullback (siteSchemeHom s))
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property) (readingInverse TF)
    (hx := by
      convert congrArg (fun f => (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property).map ((readingInverse TF).map f))
        (modulePullback_map_comparison_comp πE πF ι hιπ φE φF (representedSpaceMap B S hS s) hglue τ
          aE χ hτ) using 3)
    (hnat := readingPullbackComparison_naturality s
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φE _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS πE E hE)) hL χ)
    (hRf := hχ')
    (key := iso_shape (Scheme.Modules.pullback (siteSchemeHom s))
      (hN := readingPullbackComparison_naturality_iso s
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φE _
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS πE E hE))
        (isQuasicoherentOnSite_modulePullback_schemeReading E hE (φE ≫ πE))
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).symm)
      (hH := schemeReadingPullbackIso_eq_comparison E hE s w')
      (hC := schemeReadingPullbackIso_cocycle_square hE πE πF ι hιπ s hs φE φF hglue wρE wρF w'
        w''))
    (sq := squareComparison_trans πE πF ι hιπ φE φF (representedSpaceMap B S hS s) hglue w')
    (hspec := hspec')

end Square

/-! ### The comparison on the presenting chart -/

section Chart


/-- **The reading of a quotient of `φ^*π^*ℰ` given on the scheme**: for `φ : T ⟶ P` and
`π : P ⟶ X` with `φ ≫ π` factoring as `ρ ≫ ψ_Y` through a scheme `Y` over `X`, and a morphism
`univ : ρ^*ℱ_Y ⟶ T_U`, the composite of the reading of `φ^*π^*ℰ ≅ (φ ≫ π)^*ℰ`, the comparison
`ℰ_{φ ≫ π} ≅ ρ^*ℰ_Y`, `ρ^*q_Y` and `univ`. -/
abbrev pulledBackQuotientReading {X P : AlgebraicSpaces B S hS}
    {E F : Modules.{u, u} B S hS X.1 X.2} (hE : E.IsQuasicoherentOnSite) (q : E ⟶ F)
    {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    (φ : representedAlgebraicSpace B S hS T ⟶ P) (π : P ⟶ X)
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = φ ≫ π)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading F ψY) ⟶ TU) :
    representedZariskiModule B S hS T
        ((modulePullback B S hS φ).obj ((modulePullback B S hS π).obj E)) ⟶ TU :=
  readingMap T (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl E).inv ≫
    (schemeReadingPullbackIso E hE ρ wρ).inv ≫
    (Scheme.Modules.pullback (siteSchemeHom ρ)).map (moduleReadingMap q ψY) ≫ univ

/-- **The reading of a pulled-back quotient precomposed with the pullback of `q : ℰ ⟶ ℱ`**, at
variable data: if `φ^*τ`, followed by `φ^*𝒜 ≅ 𝓛`, reads as `univ : ρ^*ℱ_Y ⟶ T_U`, then
`φ^*(π^*q ≫ τ)` reads as `ρ^*q_Y ≫ univ`. -/
theorem exists_iso_readingMap_comp {X P : AlgebraicSpaces B S hS}
    {E F : Modules.{u, u} B S hS X.1 X.2} (hE : E.IsQuasicoherentOnSite)
    (hF : F.IsQuasicoherentOnSite) (q : E ⟶ F) {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} (φ : representedAlgebraicSpace B S hS T ⟶ P)
    (π : P ⟶ X) (wρ : representedSpaceMap B S hS ρ ≫ ψY = φ ≫ π)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading F ψY) ⟶ TU)
    {L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (εL : representedZariskiModule B S hS T L ≅ TU) {A : Modules.{u, u} B S hS P.1 P.2}
    (τ : (modulePullback B S hS π).obj F ⟶ A) (aI : (modulePullback B S hS φ).obj A ≅ L)
    (χ : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj F) ⟶ L)
    (hτ : (modulePullback B S hS φ).map τ ≫ aI.hom = χ)
    (hχ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map
        χ) =
      quotientReadingOf F hF wρ univ εL
        (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl F).symm) :
    ∃ θ : representedZariskiModule B S hS T ((modulePullback B S hS φ).obj A) ≅ TU,
      readingMap T ((modulePullback B S hS φ).map ((modulePullback B S hS π).map q ≫ τ)) ≫
          θ.hom = pulledBackQuotientReading hE q φ π wρ univ := by
  refine ⟨readingIso T aI ≪≫ εL, ?_⟩
  have hχ' : readingMap T χ = quotientReadingOf F hF wρ univ εL
      (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl F).symm := hχ
  have hnat := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS φ π _ rfl q
  have hmr := schemeReadingPullbackIso_naturality q hE hF ρ wρ
  have h3 : moduleReadingMap q (φ ≫ π) ≫ (schemeReadingPullbackIso F hF ρ wρ).inv =
      (schemeReadingPullbackIso E hE ρ wρ).inv ≫
        (Scheme.Modules.pullback (siteSchemeHom ρ)).map (moduleReadingMap q ψY) := by
    rw [Iso.comp_inv_eq, Category.assoc, hmr, Iso.inv_hom_id_assoc]
  have h2 : readingMap T ((modulePullback B S hS φ).map ((modulePullback B S hS π).map q)) ≫
      readingMap T (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl F).inv =
      readingMap T (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl E).inv ≫
        moduleReadingMap q (φ ≫ π) := by
    rw [← readingMap_comp, hnat, readingMap_comp]
  rw [Iso.trans_hom, readingIso_hom, CategoryTheory.Functor.map_comp, readingMap_comp,
    Category.assoc, ← Category.assoc (readingMap T ((modulePullback B S hS φ).map τ)),
    ← readingMap_comp, hτ, hχ', quotientReadingOf_eq, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, h2, Category.assoc, ← Category.assoc (moduleReadingMap q (φ ≫ π)), h3,
    Category.assoc]

/-- **The readings on the chart of `𝐏(ℱ)` of `π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ ⟶ ι^*𝒜` and of
`π_ℱ^*q ≫ τ_ℱ` agree up to an isomorphism of the targets**, at variable data: the first is read
through the chart of `𝐏(ℰ)`
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_readingMap_comparison_comp`),
the second directly (`AlgebraicGeometry.Space.PrivateChern.exists_iso_readingMap_comp`), and the
inverse image along `s` of the tautological quotient of the chart of `𝐏(ℰ)` agrees, up to an
isomorphism of the targets, with that of `𝐏(ℱ)` precomposed with `q`. -/
theorem exists_iso_readingMap_embedding {X PE PF : AlgebraicSpaces B S hS}
    {E F : Modules.{u, u} B S hS X.1 X.2} (hE : E.IsQuasicoherentOnSite)
    (hF : F.IsQuasicoherentOnSite) (q : E ⟶ F) (πE : PE ⟶ X) (πF : PF ⟶ X) (ι : PF ⟶ PE)
    (hιπ : ι ≫ πE = πF) {TE TF Y : BigFppfOver B S hS} (s : TF ⟶ TE) {ρE : TE ⟶ Y}
    {ρF : TF ⟶ Y} (hs : s ≫ ρE = ρF) {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    (φE : representedAlgebraicSpace B S hS TE ⟶ PE)
    (φF : representedAlgebraicSpace B S hS TF ⟶ PF)
    (hglue : φF ≫ ι = representedSpaceMap B S hS s ≫ φE)
    (wρE : representedSpaceMap B S hS ρE ≫ ψY = φE ≫ πE)
    (wρF : representedSpaceMap B S hS ρF ≫ ψY = φF ≫ πF)
    {A : Modules.{u, u} B S hS PE.1 PE.2} (hA : A.IsQuasicoherentOnSite)
    (τ : (modulePullback B S hS πE).obj E ⟶ A)
    {L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS TE).1
      (representedAlgebraicSpace B S hS TE).2} (hL : L.IsQuasicoherentOnSite)
    (aE : (modulePullback B S hS φE).obj A ≅ L)
    (χ : (modulePullback B S hS φE).obj ((modulePullback B S hS πE).obj E) ⟶ L)
    (hτ : (modulePullback B S hS φE).map τ ≫ aE.hom = χ)
    {TU : ((BigFppfOver.toScheme B S hS).obj TE).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρE)).obj (schemeReading E ψY) ⟶ TU)
    (εL : representedZariskiModule B S hS TE L ≅ TU)
    (hχ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TE) TE.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS TE).inverse.map χ) =
      quotientReadingOf E hE wρE univ εL
        (QuasiCoherentDescent.pullbackComparison B S hS φE πE _ rfl E).symm)
    {AF : Modules.{u, u} B S hS PF.1 PF.2} (τF : (modulePullback B S hS πF).obj F ⟶ AF)
    {LF : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS TF).1
      (representedAlgebraicSpace B S hS TF).2}
    (aF : (modulePullback B S hS φF).obj AF ≅ LF)
    (χF : (modulePullback B S hS φF).obj ((modulePullback B S hS πF).obj F) ⟶ LF)
    (hτF : (modulePullback B S hS φF).map τF ≫ aF.hom = χF)
    {TUF : ((BigFppfOver.toScheme B S hS).obj TF).Modules}
    (univF : (Scheme.Modules.pullback (siteSchemeHom ρF)).obj (schemeReading F ψY) ⟶ TUF)
    (εF : representedZariskiModule B S hS TF LF ≅ TUF)
    (hχF : (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj TF) TF.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS TF).inverse.map χF) =
      quotientReadingOf F hF wρF univF εF
        (QuasiCoherentDescent.pullbackComparison B S hS φF πF _ rfl F).symm)
    (hsc : siteSchemeHom s ≫ siteSchemeHom ρE = siteSchemeHom ρF)
    (hspec : ∃ θ₀ : (Scheme.Modules.pullback (siteSchemeHom s)).obj TU ≅ TUF,
      (Scheme.Modules.pullback (siteSchemeHom s)).map univ ≫ θ₀.hom =
      ((Scheme.Modules.pullbackComp (siteSchemeHom s) (siteSchemeHom ρE)).app
        (schemeReading E ψY)).hom ≫
      ((Scheme.Modules.pullbackCongr hsc).app (schemeReading E ψY)).hom ≫
        (Scheme.Modules.pullback (siteSchemeHom ρF)).map (moduleReadingMap q ψY) ≫ univF) :
    ∃ θ : representedZariskiModule B S hS TF
        ((modulePullback B S hS φF).obj ((modulePullback B S hS ι).obj A)) ≅
        representedZariskiModule B S hS TF ((modulePullback B S hS φF).obj AF),
      readingMap TF ((modulePullback B S hS φF).map
          ((QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
            (modulePullback B S hS ι).map τ)) ≫ θ.hom =
        readingMap TF ((modulePullback B S hS φF).map
          ((modulePullback B S hS πF).map q ≫ τF)) := by
  obtain ⟨θ₀, hθ₀⟩ := hspec
  have h1 := exists_iso_readingMap_comparison_comp hE πE πF ι hιπ s hs φE φF hglue wρE wρF hA τ hL
    aE χ hτ univ εL hχ _ θ₀ hsc hθ₀
  have h2 := exists_iso_readingMap_comp hE hF q φF πF wρF univF εF τF aF χF hτF hχF
  exact exists_iso_comp_eq_trans h1 (exists_iso_comp_eq_symm h2)

/-- **Two quotients of `π_ℱ^*ℰ` are isomorphic as soon as their readings on a flat surjective
chart are**: the readings detect morphisms of quasi-coherent modules on the chart
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_comp_eq_of_readingMap`), and two quotients
which are flat locally isomorphic are isomorphic
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_comp_eq_of_modulePullback`). -/
theorem exists_iso_of_readingMap_chart {X PE PF : AlgebraicSpaces B S hS}
    {E F : Modules.{u, u} B S hS X.1 X.2} (hE : E.IsQuasicoherentOnSite) (q : E ⟶ F) [Epi q]
    (πE : PE ⟶ X) (πF : PF ⟶ X) (ι : PF ⟶ PE) (hιπ : ι ≫ πE = πF) {TF : BigFppfOver B S hS}
    (φF : representedAlgebraicSpace B S hS TF ⟶ PF) (hφ : IsFlat B S hS φF.hom)
    (hsurj : Function.Surjective (pointsMap B S hS (representedAlgebraicSpace B S hS TF).1 φF.hom))
    {A : Modules.{u, u} B S hS PE.1 PE.2} (hA : A.IsQuasicoherentOnSite)
    (τ : (modulePullback B S hS πE).obj E ⟶ A) [Epi τ]
    {AF : Modules.{u, u} B S hS PF.1 PF.2} (hAF : AF.IsQuasicoherentOnSite)
    (τF : (modulePullback B S hS πF).obj F ⟶ AF) [Epi τF]
    (H : ∃ θ : representedZariskiModule B S hS TF
        ((modulePullback B S hS φF).obj ((modulePullback B S hS ι).obj A)) ≅
        representedZariskiModule B S hS TF ((modulePullback B S hS φF).obj AF),
      readingMap TF ((modulePullback B S hS φF).map
          ((QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
            (modulePullback B S hS ι).map τ)) ≫ θ.hom =
        readingMap TF ((modulePullback B S hS φF).map
          ((modulePullback B S hS πF).map q ≫ τF))) :
    ∃ e : (modulePullback B S hS ι).obj A ≅ AF,
      ((QuasiCoherentDescent.pullbackComparison B S hS ι πE πF hιπ E).hom ≫
          (modulePullback B S hS ι).map τ) ≫ e.hom =
        (modulePullback B S hS πF).map q ≫ τF := by
  have hι : Epi ((modulePullback B S hS ι).map τ) :=
    (Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS ι)).preserves τ
  have hπ : Epi ((modulePullback B S hS πF).map q) :=
    (Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS πF)).preserves q
  refine @exists_iso_comp_eq_of_modulePullback _ _ _ _ Unit _ (fun _ => φF) (fun _ => hφ) ?_ _ _ _
    _ (epi_comp' (IsIso.epi_of_iso _) hι) _ (epi_comp' hπ inferInstance)
    fun _ => exists_iso_comp_eq_of_readingMap
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ E hE))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hA))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hAF) _ _ H
  show (⋃ _ : Unit, Set.range (pointsMap B S hS _ φF.hom)) = Set.univ
  rw [Set.iUnion_const]
  exact Set.range_eq_univ.mpr hsurj

variable {X : AlgebraicSpaces B S hS} {E F : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V))

/-- **The glued morphism restricts on the presenting chart to the closed immersion of chart
bundles.** -/
theorem projectiveBundleAtlas_comp_projectiveBundleEmbedding :
    projectiveBundleAtlas F hfreeF ≫ projectiveBundleEmbedding hfreeE hfreeF q hq =
      representedSpaceMap B S hS
          ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X)) ≫
        projectiveBundleAtlas E hfreeE :=
  ObjectProperty.hom_ext _
    ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).quotientChart_comp_glued
    (presentationRelationTargetHom (projectiveBundlePresentation X))
    (presentationRelationSourceHom (projectiveBundlePresentation X))
    (isPullback_projectiveBundlePresentation X))

include hE hF in
/-- **The restriction of `𝒪_{𝐏(ℰ)}(1)` to `𝐏(ℱ)` is `𝒪_{𝐏(ℱ)}(1)`**: for a surjection
`q : ℰ ⟶ ℱ` of finite locally free modules, an isomorphism `ι^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℱ)}(1)` carries
the pulled-back tautological quotient of `ℰ`, read on `π_ℱ^*ℰ ≅ ι^*π_ℰ^*ℰ`, to the tautological
quotient of `ℱ` precomposed with `π_ℱ^*q`. -/
theorem exists_projectiveBundleEmbedding_twistIso [Epi q] :
    ∃ e : (modulePullback B S hS (projectiveBundleEmbedding hfreeE hfreeF q hq)).obj
        (projectiveBundleTwist E hfreeE).obj ≅ (projectiveBundleTwist F hfreeF).obj,
      ((QuasiCoherentDescent.pullbackComparison B S hS
          (projectiveBundleEmbedding hfreeE hfreeF q hq) (projectiveBundleProj E hfreeE)
          (projectiveBundleProj F hfreeF)
          (projectiveBundleEmbedding_comp_proj hfreeE hfreeF q hq) E).hom ≫
        (modulePullback B S hS (projectiveBundleEmbedding hfreeE hfreeF q hq)).map
          (projectiveBundleTautological E hfreeE).hom) ≫ e.hom =
        (modulePullback B S hS (projectiveBundleProj F hfreeF)).map q ≫
          (projectiveBundleTautological F hfreeF).hom := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  have H1 := exists_iso_readingMap_embedding hE hF q (projectiveBundleProj E hfreeE)
    (projectiveBundleProj F hfreeF) (projectiveBundleEmbedding hfreeE hfreeF q hq)
    (projectiveBundleEmbedding_comp_proj hfreeE hfreeF q hq)
    (TE := (projectiveBundleChartPresentation E hfreeE).U)
    (TF := (projectiveBundleChartPresentation F hfreeF).U)
    (Y := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
    (ρE := projectiveBundleChartProj E hfreeE) (ρF := projectiveBundleChartProj F hfreeF)
    ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X))
    ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp_siteToChart (bundleBaseChart X))
    (projectiveBundleAtlas E hfreeE) (projectiveBundleAtlas F hfreeF)
    (projectiveBundleAtlas_comp_projectiveBundleEmbedding hfreeE hfreeF q hq)
    (representedSpaceMap_projectiveBundleChartProj_comp E hfreeE)
    (representedSpaceMap_projectiveBundleChartProj_comp F hfreeF)
    (projectiveBundleTwist E hfreeE).property (projectiveBundleTautological E hfreeE).hom
    (isQuasicoherentOnSite_projectiveBundleChartTwist E hfreeE)
    (projectiveBundleTwistAtlasIso E hfreeE) (projectiveBundleChartQuotient E hfreeE)
    (by convert modulePullback_map_projectiveBundleTautological E hfreeE using 2)
    (chartBundleTautological E (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso E hfreeE)
    (representedZariski_map_projectiveBundleChartQuotient E hfreeE)
    (projectiveBundleTautological F hfreeF).hom (projectiveBundleTwistAtlasIso F hfreeF)
    (projectiveBundleChartQuotient F hfreeF)
    (by convert modulePullback_map_projectiveBundleTautological F hfreeF using 2)
    (chartBundleTautological F (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso F hfreeF)
    (representedZariski_map_projectiveBundleChartQuotient F hfreeF)
    (congrArg (fun x => siteSchemeHom x)
      ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp_siteToChart
        (bundleBaseChart X)))
    (by
      have e : siteSchemeHom ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp
          (bundleBaseChart X)) = situationEmbedding (chartModuleMap q (bundleBaseChart X)) :=
        (situationEmbedding_eq (chartModuleMap q (bundleBaseChart X))).symm
      exact exists_iso_pullback_map_comp_eq_of_heq
        (P := (BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfreeE).U)
        (P' := (BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation F hfreeF).U)
        (Y := (BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X)))
        (P₀ := Stacks.RelativeProj.projectiveBundle (chartScheme (bundleBaseChart X))
          (chartBundleModule E (bundleBaseChart X)))
        (P₀' := Stacks.RelativeProj.projectiveBundle (chartScheme (bundleBaseChart X))
          (chartBundleModule F (bundleBaseChart X)))
        (Y₀ := chartScheme (bundleBaseChart X))
        (f := siteSchemeHom ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp
          (bundleBaseChart X)))
        (f₀ := situationEmbedding (chartModuleMap q (bundleBaseChart X)))
        (π := siteSchemeHom (projectiveBundleChartProj E hfreeE))
        (π₀ := Stacks.RelativeProj.projectiveBundleToBase (chartScheme (bundleBaseChart X))
          (chartBundleModule E (bundleBaseChart X)))
        (π' := siteSchemeHom (projectiveBundleChartProj F hfreeF))
        (π₀' := Stacks.RelativeProj.projectiveBundleToBase (chartScheme (bundleBaseChart X))
          (chartBundleModule F (bundleBaseChart X)))
        (M := schemeReading E (chartToSpace B S hS X (bundleBaseChart X)))
        (M₀ := chartBundleModule E (bundleBaseChart X))
        (T := chartBundleTwist E (bundleBaseChart X))
        (T₀ := Stacks.RelativeProj.tautologicalDatumTwist (chartBundleModule E (bundleBaseChart X)))
        (T' := chartBundleTwist F (bundleBaseChart X))
        (T₀' := Stacks.RelativeProj.tautologicalDatumTwist
          (chartBundleModule F (bundleBaseChart X)))
        (u := chartBundleTautological E (bundleBaseChart X))
        (u₀ := Stacks.RelativeProj.tautologicalDatumUniv (chartBundleModule E (bundleBaseChart X)))
        (w := (Scheme.Modules.pullback (siteSchemeHom (projectiveBundleChartProj F hfreeF))).map
            (moduleReadingMap q (chartToSpace B S hS X (bundleBaseChart X))) ≫
          chartBundleTautological F (bundleBaseChart X))
        (w₀ := (Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase
            (chartScheme (bundleBaseChart X)) (chartBundleModule F (bundleBaseChart X)))).map
            (chartModuleMap q (bundleBaseChart X)) ≫
          Stacks.RelativeProj.tautologicalDatumUniv (chartBundleModule F (bundleBaseChart X)))
        rfl rfl rfl (heq_of_eq e) HEq.rfl HEq.rfl
        (congrArg (fun x => siteSchemeHom x)
          ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp_siteToChart
            (bundleBaseChart X)))
        (situationEmbedding_comp_toBase' (chartModuleMap q (bundleBaseChart X)))
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
        (exists_situationEmbedding_twistIso (chartModuleMap q (bundleBaseChart X))))
  exact exists_iso_of_readingMap_chart hE q (projectiveBundleProj E hfreeE)
    (projectiveBundleProj F hfreeF) (projectiveBundleEmbedding hfreeE hfreeF q hq)
    (projectiveBundleEmbedding_comp_proj hfreeE hfreeF q hq)
    (TF := (projectiveBundleChartPresentation F hfreeF).U) (projectiveBundleAtlas F hfreeF)
    (isFlat_of_isEtale B S hS (presentationAtlas_isEtale _))
    (surjective_pointsMap_projectiveBundleAtlas F hfreeF)
    (projectiveBundleTwist E hfreeE).property (projectiveBundleTautological E hfreeE).hom
    (projectiveBundleTwist F hfreeF).property (projectiveBundleTautological F hfreeF).hom H1

end Chart

end AlgebraicGeometry.Space.PrivateChern

end
