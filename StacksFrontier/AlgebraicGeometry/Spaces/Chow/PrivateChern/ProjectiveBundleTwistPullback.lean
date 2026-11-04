module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundlePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.QuotientComparisonLocal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec

/-!
# The twist of the projective bundle of an inverse image

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `ℰ` a finite locally free `𝒪_X`-module and
`φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` the comparison over `f`. The identification `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(f^*ℰ)}(1)`
is a comparison of two quotients of `π'^*f^*ℰ`, which may be made flat locally. This file
provides the local inputs: the twists `𝒪(1)` of the reading bundles `𝐏(ℰ_ψ)` on the represented
spaces, with their tautological quotients, and their behaviour under the base-change morphisms
`𝐏(ℰ_{ψ'}) ⟶ 𝐏(ℰ_ψ)` and the comparisons `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})` (Stacks 01O3), read through
the comparisons of readings (Stacks 03DX (2)).

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.readingBundleTwist`,
  `AlgebraicGeometry.Space.PrivateChern.readingBundleQuotient`: the twist of `𝐏(ℰ_ψ)` and its
  tautological quotient, on the represented space.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_iso_pullbackComparison_hom_comp_map_of_reading`:
  quotients of inverse images of `ℰ` on represented spaces are compared through their readings.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_readingBundleSiteMap_quotient`: Stacks 01O3
  along the base-change morphisms of the reading bundles.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_readingBundleSitePullback_quotient`: Stacks 01O3
  along `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`.

## Implementation notes

Equations between composites containing the comparisons of inverse images are stated with the
same proof terms on both sides and with the composite `v ≫ f` replaced by a morphism `u` with
`v ≫ f = u`; the comparisons are otherwise identified only up to their proofs, which the
definitional checks do not exploit inside composites.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

/-! ### Inverse images of quotients of inverse images -/

section Quotients

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2)

/-- **Inverse images of quotients compose**: for a quotient `q : v^*ℰ ⟶ ℒ` and `s' ≫ s`, the
inverse image of the inverse image of `q` is the inverse image of `q` along the composite. -/
theorem pullbackComparison_hom_comp_map_pullbackComparison_hom_comp_map
    {Z Z' Z'' : AlgebraicSpaces B S hS} (s' : Z'' ⟶ Z') (s : Z' ⟶ Z) {v : Z ⟶ X} {v' : Z' ⟶ X}
    {v'' : Z'' ⟶ X} (h : s ≫ v = v') (h' : s' ≫ v' = v'') (h'' : (s' ≫ s) ≫ v = v'')
    {L : Modules.{u, u} B S hS Z.1 Z.2} (q : (modulePullback B S hS v).obj E ⟶ L) :
    ((QuasiCoherentDescent.pullbackComparison B S hS s' v' v'' h' E).hom ≫
      (modulePullback B S hS s').map
        ((QuasiCoherentDescent.pullbackComparison B S hS s v v' h E).hom ≫
          (modulePullback B S hS s).map q)) ≫ (modulePullbackCompIso B S hS s' s).hom.app L =
    (QuasiCoherentDescent.pullbackComparison B S hS (s' ≫ s) v v'' h'' E).hom ≫
      (modulePullback B S hS (s' ≫ s)).map q := by
  have key := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS s' s v v' h (s' ≫ s) rfl
    v'' h' h'' E
  have nat : (modulePullback B S hS s').map ((modulePullback B S hS s).map q) ≫
      (modulePullbackCompIso B S hS s' s).hom.app L =
      (modulePullbackCompIso B S hS s' s).hom.app _ ≫ (modulePullback B S hS (s' ≫ s)).map q :=
    (modulePullbackCompIso B S hS s' s).hom.naturality q
  have e1 : (QuasiCoherentDescent.pullbackComparison B S hS s' s (s' ≫ s) rfl
      ((modulePullback B S hS v).obj E)).hom = (modulePullbackCompIso B S hS s' s).inv.app _ := by
    rw [QuasiCoherentDescent.pullbackComparison_rfl]
    rfl
  rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, nat, ← Category.assoc,
    ← Category.assoc, key, e1, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]

variable {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- **The comparisons of inverse images along a factorization through `f` are compatible with
inverse images**: the inverse image along `s` of a quotient of `v^*f^*ℰ`, read as a quotient of
`u^*ℰ`, is the inverse image of the quotient read along `v' = s ≫ v`. -/
theorem pullbackComparison_hom_comp_map_pullbackComparison_hom_comp
    {Z Z' : AlgebraicSpaces B S hS} (s : Z' ⟶ Z) {v : Z ⟶ Y}
    {v' : Z' ⟶ Y} {u : Z ⟶ X} {u' : Z' ⟶ X} (hv : s ≫ v = v') (hu : v ≫ f = u)
    (hu' : v' ≫ f = u') (h : s ≫ u = u') {L : Modules.{u, u} B S hS Z.1 Z.2}
    (q : (modulePullback B S hS v).obj ((modulePullback B S hS f).obj E) ⟶ L) :
    (QuasiCoherentDescent.pullbackComparison B S hS s u u' h E).hom ≫
      (modulePullback B S hS s).map
        ((QuasiCoherentDescent.pullbackComparison B S hS v f u hu E).hom ≫ q) =
      (QuasiCoherentDescent.pullbackComparison B S hS v' f u' hu' E).hom ≫
        ((QuasiCoherentDescent.pullbackComparison B S hS s v v' hv
          ((modulePullback B S hS f).obj E)).hom ≫ (modulePullback B S hS s).map q) := by
  have key := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS s v f u hu v' hv u' h
    hu' E
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, key, Category.assoc]

/-- The inverse image of a quotient only depends on the morphism, up to isomorphism. -/
theorem exists_iso_pullbackComparison_hom_comp_map_of_eq {Z Z' : AlgebraicSpaces B S hS}
    {s₁ s₂ : Z' ⟶ Z} (hs : s₁ = s₂) {v : Z ⟶ X} {v' : Z' ⟶ X} (h₁ : s₁ ≫ v = v')
    (h₂ : s₂ ≫ v = v') {L : Modules.{u, u} B S hS Z.1 Z.2}
    (q : (modulePullback B S hS v).obj E ⟶ L) :
    ∃ θ : (modulePullback B S hS s₁).obj L ≅ (modulePullback B S hS s₂).obj L,
      ((QuasiCoherentDescent.pullbackComparison B S hS s₁ v v' h₁ E).hom ≫
        (modulePullback B S hS s₁).map q) ≫ θ.hom =
      (QuasiCoherentDescent.pullbackComparison B S hS s₂ v v' h₂ E).hom ≫
        (modulePullback B S hS s₂).map q := by
  subst hs
  obtain rfl : h₂ = h₁ := rfl
  exact ⟨Iso.refl _, Category.comp_id _⟩

/-- Isomorphic quotients have isomorphic inverse images. -/
theorem exists_iso_pullbackComparison_hom_comp_map_of_exists_iso {Z Z' : AlgebraicSpaces B S hS}
    (s : Z' ⟶ Z) {v : Z ⟶ X} {v' : Z' ⟶ X} (h : s ≫ v = v') {L₁ L₂ : Modules.{u, u} B S hS Z.1 Z.2}
    {q₁ : (modulePullback B S hS v).obj E ⟶ L₁} {q₂ : (modulePullback B S hS v).obj E ⟶ L₂}
    (hq : ∃ θ : L₁ ≅ L₂, q₁ ≫ θ.hom = q₂) :
    ∃ θ : (modulePullback B S hS s).obj L₁ ≅ (modulePullback B S hS s).obj L₂,
      ((QuasiCoherentDescent.pullbackComparison B S hS s v v' h E).hom ≫
        (modulePullback B S hS s).map q₁) ≫ θ.hom =
      (QuasiCoherentDescent.pullbackComparison B S hS s v v' h E).hom ≫
        (modulePullback B S hS s).map q₂ := by
  obtain ⟨θ, hθ⟩ := hq
  exact ⟨(modulePullback B S hS s).mapIso θ, by
    rw [Category.assoc, Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, hθ]⟩

/-- An identity through the hom of a natural isomorphism, read through its inverse. -/
theorem comp_inv_app_eq_of_comp_hom_app_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ≅ G) (Z : C) {P : D} (a : P ⟶ F.obj Z) (b : P ⟶ G.obj Z)
    (h : a ≫ α.hom.app Z = b) : b ≫ α.inv.app Z = a := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {P a₀' a₁ a₂ a₃ a₄ a₅ : C}
    {s₀ : P ⟶ a₀'} {s₁ : P ⟶ a₁} {s₂ : P ⟶ a₂} {s₃ : P ⟶ a₃} {s₄ : P ⟶ a₄} {s₅ : P ⟶ a₅}
    (x₁ : a₀' ⟶ a₁) (x₂ : a₁ ⟶ a₂) (x₃ : a₂ ⟶ a₃) (x₄ : a₃ ⟶ a₄) (x₅ : a₄ ⟶ a₅)
    (h₁ : s₀ ≫ x₁ = s₁) (h₂ : s₁ ≫ x₂ = s₂) (h₃ : s₂ ≫ x₃ = s₃) (h₄ : s₃ ≫ x₄ = s₄)
    (h₅ : s₄ ≫ x₅ = s₅) :
    s₀ ≫ x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ = s₅ := by
  rw [← h₅, ← h₄, ← h₃, ← h₂, ← h₁]
  simp only [Category.assoc]

end Quotients

/-! ### Readings of inverse images of quotients -/

section Reading

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : E.IsQuasicoherentOnSite)

/-- **The reading of the inverse image of a quotient along a morphism of the site** is the inverse
image of its reading, through the comparisons `g^*ℰ_v ≅ ℰ_{v'}` and
`g^*(ℒ read on T) ≅ (g^*ℒ) read on T'`. -/
theorem readingFunctor_map_pullbackComparison_hom_comp_map {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) {v : representedAlgebraicSpace B S hS T ⟶ X}
    {v' : representedAlgebraicSpace B S hS T' ⟶ X} (w : representedSpaceMap B S hS g ≫ v = v')
    {L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2} (hL : L.IsQuasicoherentOnSite)
    (q : (modulePullback B S hS v).obj E ⟶ L) :
    (readingFunctor T').map
        ((QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) v v' w
          E).hom ≫ (modulePullback B S hS (representedSpaceMap B S hS g)).map q) ≫
      (representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        L hL).inv =
      (schemeReadingPullbackIso E hE g w).inv ≫
        (Scheme.Modules.pullback (siteSchemeHom g)).map ((readingFunctor T).map q) := by
  have h1 := schemeReadingPullbackIso_hom_eq hE g w
  have h2 := representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS
        g) (isQuasicoherentOnSite_modulePullback_schemeReading E hE v)
    hL q
  rw [← readingFunctor_map, ← readingFunctor_map] at h2
  rw [Iso.comp_inv_eq, Category.assoc]
  refine (Iso.eq_inv_comp _).2 ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)).trans h2.symm
  rw [← CategoryTheory.Functor.map_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Reading

/-! ### The twists of the reading bundles, on the represented spaces -/

section ReadingTwist

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

include hfree in
/-- The twist of a reading bundle is quasi-coherent, being invertible. -/
theorem isQuasicoherent_readingBundleTwist {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    (Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ)).IsQuasicoherent := by
  have := isFiniteLocallyFree_schemeReading E hfree ψ
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ)) 1 :=
    Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible _ _
      (Stacks.RelativeProj.isInvertible_tautologicalDatumTwist (schemeReading E ψ))
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  obtain ⟨c, hc, _⟩ := h2.exists_isFiniteLocallyFreeData
  have : c.IsLocallyFreeData := hc
  exact c.quasiCoherentData.isQuasicoherent

/-- **The twist `𝒪(1)` of the reading bundle `𝐏(ℰ_ψ)`, as a quasi-coherent module on the
represented space** (Stacks 03DX (2)). -/
def readingBundleTwist {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    Modules.{u, u} B S hS (representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ)).1
      (representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ)).2 :=
  ((representedQuasicoherentSchemeEquivalence B S hS (readingBundleSite E hfree ψ)).functor.obj
    ⟨Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ),
      isQuasicoherent_readingBundleTwist E hfree ψ⟩).obj

/-- The twist of a reading bundle is quasi-coherent on the site of the represented space. -/
theorem isQuasicoherentOnSite_readingBundleTwist {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    (readingBundleTwist E hfree ψ).IsQuasicoherentOnSite :=
  ((representedQuasicoherentSchemeEquivalence B S hS (readingBundleSite E hfree ψ)).functor.obj
    ⟨Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ),
      isQuasicoherent_readingBundleTwist E hfree ψ⟩).property

/-- The reading of the twist on the scheme is the twist. -/
def readingBundleTwistReadingIso {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    (readingFunctor (readingBundleSite E hfree ψ)).obj (readingBundleTwist E hfree ψ) ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ) :=
  representedZariskiModuleQuasicoherentSchemeIso B S hS (readingBundleSite E hfree ψ)
    ⟨Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ),
      isQuasicoherent_readingBundleTwist E hfree ψ⟩

/-- **The tautological quotient `v^*ℰ ⟶ 𝒪(1)` of the reading bundle `𝐏(ℰ_ψ)` on the represented
space**, the morphism whose reading on the scheme is the tautological quotient
(Stacks 03DX (2)). -/
def readingBundleQuotient {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v) :
    (modulePullback B S hS v).obj E ⟶ readingBundleTwist E hfree ψ :=
  ((QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE v)).2
      (quotientReadingOf E hE hv (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ))
        (readingBundleTwistReadingIso E hfree ψ) (Iso.refl _))).choose

/-- The reading of `readingBundleQuotient` on the scheme is the tautological quotient of
`𝐏(ℰ_ψ)`, through `readingBundleTwistReadingIso`. -/
theorem quotientReadingHyp_readingBundleQuotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v) :
    QuotientReadingHyp E hE hv (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ))
      (readingBundleTwistReadingIso E hfree ψ) (readingBundleQuotient E hfree ψ hv) (Iso.refl _) :=
  ((QuasiCoherentDescent.bijective_representedZariski_map B S hS _ _
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE v)).2
      (quotientReadingOf E hE hv (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ))
        (readingBundleTwistReadingIso E hfree ψ) (Iso.refl _))).choose_spec

/-- The reading of `κ₀⁻¹ ≫ q` for a quotient `q` whose reading is `univ`. -/
theorem readingFunctor_map_inv_comp_of_quotientReadingHyp {T Y : BigFppfOver B S hS}
    {ρ : T ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback (siteSchemeHom ρ)).obj (schemeReading E ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) (hq : QuotientReadingHyp E hE wρ univ εL q κ₀) :
    (readingFunctor T).map (κ₀.inv ≫ q) =
      (schemeReadingPullbackIso E hE ρ wρ).inv ≫ univ ≫ εL.inv := by
  have hid : (readingFunctor T).map κ₀.inv ≫ (readingFunctor T).map κ₀.hom = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact (CategoryTheory.Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·) hq).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hid).trans (Category.id_comp _))))

private theorem inv_comp_inv_comp_eq_of_shape {C : Type*} [Category C]
    {P₁ P₂ Q₁ Q₂ Q₃ R₁ R₂ W W' : C} (m₁ : P₁ ≅ P₂) (m₂ : Q₁ ≅ P₁) (U : Q₁ ⟶ W) (Θ : W ⟶ W')
    (c₁ : Q₁ ⟶ Q₂) (c₂ : Q₂ ⟶ Q₃) (c₃ : Q₃ ⟶ R₁) (k : R₁ ⟶ R₂) (m₃ : R₂ ≅ P₂) (u' : R₂ ⟶ W')
    (hspec : U ≫ Θ = c₁ ≫ c₂ ≫ c₃ ≫ k ≫ u')
    (hsq : m₂.hom ≫ m₁.hom = c₁ ≫ c₂ ≫ c₃ ≫ k ≫ m₃.hom) :
    m₁.inv ≫ (m₂.inv ≫ U) ≫ Θ = m₃.inv ≫ u' := by
  have h' : c₁ ≫ c₂ ≫ c₃ ≫ k = (m₂.hom ≫ m₁.hom) ≫ m₃.inv := by
    rw [hsq]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : c₁ ≫ c₂ ≫ c₃ ≫ k ≫ u' = (c₁ ≫ c₂ ≫ c₃ ≫ k) ≫ u' := by
    simp only [Category.assoc]
  rw [Category.assoc, hspec, h'', h']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **Stacks 01O3 for the reading bundles, read through the comparisons of readings.** -/
theorem schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ X} (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    {v' : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ') ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v)
    (hv' : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ') ≫ ψ' = v')
    (h : representedSpaceMap B S hS (readingBundleSiteMap E hfree g w) ≫ v = v') :
    (schemeReadingPullbackIso E hE (readingBundleSiteMap E hfree g w) h).inv ≫
        (Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteMap E hfree g w))).map
          ((schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree ψ) hv).inv ≫
            Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ)) ≫
        (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (siteSchemeHom g)
          (schemeReading E ψ) (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm).hom =
      (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree ψ') hv').inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ') := by
  have heq := (isPullback_readingBundleSiteMap E hfree g w).w
  have hsq := congrArg Iso.hom (schemeReadingPullbackIso_square E hE heq hv h w hv')
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv] at hsq
  exact (congrArg (fun z => _ ≫ z ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans
    (inv_comp_inv_comp_eq_of_shape
      (schemeReadingPullbackIso E hE (readingBundleSiteMap E hfree g w) h)
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteMap E hfree g w))).mapIso
        (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree ψ) hv))
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteMap E hfree g w))).map
        (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ)))
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (siteSchemeHom g)
        (schemeReading E ψ) (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm).hom
      ((Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSiteMap E hfree g w))
          (siteSchemeHom (readingBundleSiteToBase E hfree ψ))).hom.app (schemeReading E ψ))
      ((Scheme.Modules.pullbackCongr (congrArg (fun x => siteSchemeHom x) heq)).hom.app
          (schemeReading E ψ))
      ((Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSiteToBase E hfree ψ'))
          (siteSchemeHom g)).inv.app (schemeReading E ψ))
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase E hfree ψ'))).map
          (schemeReadingPullbackIso E hE g w).hom)
      (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree ψ') hv')
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ'))
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec (siteSchemeHom g)
        (schemeReading E ψ) (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm) hsq)

/-- Two quotients of a quasi-coherent module on a represented space are isomorphic as soon as
their readings are, the reading being fully faithful on quasi-coherent modules
(Stacks 03DX (2)). -/
private theorem exists_iso_comp_eq_of_reading {T : BigFppfOver B S hS}
    {M A A' : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
      (representedAlgebraicSpace B S hS T).2}
    (hM : M.IsQuasicoherentOnSite) (hA : A.IsQuasicoherentOnSite)
    (hA' : A'.IsQuasicoherentOnSite) (x : M ⟶ A) (y : M ⟶ A')
    (θr : (readingFunctor T).obj A ≅ (readingFunctor T).obj A')
    (h : (readingFunctor T).map x ≫ θr.hom = (readingFunctor T).map y) :
    ∃ θ : A ≅ A', x ≫ θ.hom = y := by
  obtain ⟨t, ht⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS A A' hA).2
    θr.hom
  obtain ⟨t', ht'⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS A' A hA').2
    θr.inv
  have hfA := (QuasiCoherentDescent.bijective_representedZariski_map B S hS A A hA).1
  have hfA' := (QuasiCoherentDescent.bijective_representedZariski_map B S hS A' A' hA').1
  have hfM := (QuasiCoherentDescent.bijective_representedZariski_map B S hS M A' hM).1
  refine ⟨⟨t, t', hfA ?_, hfA' ?_⟩, hfM ?_⟩
  · exact (CategoryTheory.Functor.map_comp (readingFunctor T) t t').trans
      (((congrArg₂ (· ≫ ·) ht ht').trans θr.hom_inv_id).trans
        (CategoryTheory.Functor.map_id (readingFunctor T) A).symm)
  · exact (CategoryTheory.Functor.map_comp (readingFunctor T) t' t).trans
      (((congrArg₂ (· ≫ ·) ht' ht).trans θr.inv_hom_id).trans
        (CategoryTheory.Functor.map_id (readingFunctor T) A').symm)
  · exact (CategoryTheory.Functor.map_comp (readingFunctor T) x t).trans
      ((congrArg ((readingFunctor T).map x ≫ ·) ht).trans h)

private theorem comp_hom_eq_of_shape {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M Z₁ L₁ W' : D} {P₁ Q₂ Q₃ : C}
    (Rx : M ⟶ Z₁) (rz : F.obj Q₂ ≅ Z₁) (mb : F.obj P₁ ≅ M) (Rq : P₁ ⟶ Q₂) (a : P₁ ⟶ Q₃)
    (εL : Q₂ ≅ Q₃) (Θ : F.obj Q₃ ⟶ W') (εL' : L₁ ≅ W') (a' : M ⟶ W') (Ry : M ⟶ L₁)
    (hQ4 : Rx ≫ rz.inv = mb.inv ≫ F.map Rq) (hL1 : Rq = a ≫ εL.inv)
    (hL2 : mb.inv ≫ F.map a ≫ Θ = a') (hL1' : Ry = a' ≫ εL'.inv) :
    Rx ≫ rz.inv ≫ F.map εL.hom ≫ Θ ≫ εL'.inv = Ry := by
  rw [← Category.assoc, hQ4, hL1', ← hL2, Category.assoc, ← F.map_comp_assoc, hL1,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc]

/-- **Two quotients of inverse images of `ℰ` on represented spaces related through their
readings**: along a morphism `b : T' ⟶ T` of the site, the inverse image of a quotient of `v^*ℰ`
whose reading is `a` is isomorphic to a quotient `x'` of `v''^*ℰ` whose reading is `a'`, as soon as
the inverse image of `a` along `b` is `a'` up to an isomorphism `Θ` of the targets. -/
theorem exists_iso_pullbackComparison_hom_comp_map_of_reading {T' T : BigFppfOver B S hS}
    (b : T' ⟶ T) {v : representedAlgebraicSpace B S hS T ⟶ X}
    {v'' : representedAlgebraicSpace B S hS T' ⟶ X} (h : representedSpaceMap B S hS b ≫ v = v'')
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hL : L.IsQuasicoherentOnSite) (q : N ⟶ L) (κ₀ : N ≅ (modulePullback B S hS v).obj E)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (εL : representedZariskiModule B S hS T L ≅ TU) (a : schemeReading E v ⟶ TU)
    (hq : (readingFunctor T).map (κ₀.inv ≫ q) = a ≫ εL.inv)
    {L' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (hL' : L'.IsQuasicoherentOnSite) (x' : (modulePullback B S hS v'').obj E ⟶ L')
    {TU' : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (εL' : representedZariskiModule B S hS T' L' ≅ TU') (a' : schemeReading E v'' ⟶ TU')
    (hx' : (readingFunctor T').map x' = a' ≫ εL'.inv)
    (Θ : (Scheme.Modules.pullback (siteSchemeHom b)).obj TU ≅ TU')
    (hΘ : (schemeReadingPullbackIso E hE b h).inv ≫
      (Scheme.Modules.pullback (siteSchemeHom b)).map a ≫ Θ.hom = a') :
    ∃ θ : (modulePullback B S hS (representedSpaceMap B S hS b)).obj L ≅ L',
      ((QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS b) v v'' h
          E).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS b)).map (κ₀.inv ≫ q)) ≫ θ.hom = x' := by
  have hbL := isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS b
    (relativelyRepresentable_yoneda_map B S hS b) L hL
  exact exists_iso_comp_eq_of_reading (isQuasicoherentOnSite_modulePullback_schemeReading E hE
      v'') hbL hL' _ _
    ((representedZariskiModulePullbackIso B S hS b (relativelyRepresentable_yoneda_map B S hS b)
        L hL).symm ≪≫ (Scheme.Modules.pullback (siteSchemeHom b)).mapIso εL ≪≫ Θ ≪≫ εL'.symm)
    (comp_hom_eq_of_shape (Scheme.Modules.pullback (siteSchemeHom b)) _
      (representedZariskiModulePullbackIso B S hS b (relativelyRepresentable_yoneda_map B S hS b)
        L hL)
      (schemeReadingPullbackIso E hE b h) ((readingFunctor T).map (κ₀.inv ≫ q)) a εL Θ.hom εL'
      a' ((readingFunctor T').map x')
      (readingFunctor_map_pullbackComparison_hom_comp_map E hE b h hL (κ₀.inv ≫ q)) hq hΘ hx')

/-- **Stacks 01O3 on the represented spaces**: along the base-change morphism
`b : 𝐏(ℰ_{ψ'}) ⟶ 𝐏(ℰ_ψ)` of a morphism `g : T' ⟶ T` over `X`, the inverse image of a quotient whose
reading is the tautological quotient of `𝐏(ℰ_ψ)` is, up to an isomorphism of the targets, a
quotient whose reading is the tautological quotient of `𝐏(ℰ_{ψ'})`. -/
theorem exists_iso_readingBundleSiteMap_quotient {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    {v' : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ') ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v)
    (hv' : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ') ≫ ψ' = v')
    (h : representedSpaceMap B S hS (readingBundleSiteMap E hfree g w) ≫ v = v')
    {N L : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite E hfree ψ))
      (isAlgebraicSpace_yoneda B S hS _)}
    (hL : L.IsQuasicoherentOnSite) (q : N ⟶ L) (κ₀ : N ≅ (modulePullback B S hS v).obj E)
    (εL : representedZariskiModule B S hS _ L ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ))
    (hq : QuotientReadingHyp E hE hv (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ))
      εL q κ₀)
    {N' L' : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite E hfree ψ'))
      (isAlgebraicSpace_yoneda B S hS _)}
    (hL' : L'.IsQuasicoherentOnSite) (q' : N' ⟶ L') (κ₀' : N' ≅ (modulePullback B S hS v').obj E)
    (εL' : representedZariskiModule B S hS _ L' ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E ψ'))
    (hq' : QuotientReadingHyp E hE hv'
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ')) εL' q' κ₀') :
    ∃ θ : (modulePullback B S hS
        (representedSpaceMap B S hS (readingBundleSiteMap E hfree g w))).obj L ≅ L',
      ((QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (readingBundleSiteMap E hfree g w)) v v' h E).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS (readingBundleSiteMap E hfree g w))).map
          (κ₀.inv ≫ q)) ≫ θ.hom = κ₀'.inv ≫ q' := by
  exact exists_iso_pullbackComparison_hom_comp_map_of_reading E (readingBundleSiteMap E hfree g w)
    h hL q κ₀ εL _
    ((readingFunctor_map_inv_comp_of_quotientReadingHyp E hv _ εL q κ₀ hq).trans
      (Category.assoc _ _ _).symm)
    hL' _ εL' _
    ((readingFunctor_map_inv_comp_of_quotientReadingHyp E hv' _ εL' q' κ₀' hq').trans
      (Category.assoc _ _ _).symm)
    (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (siteSchemeHom g)
      (schemeReading E ψ) (schemeReading E ψ') (schemeReadingPullbackIso E hE g w).symm)
    (schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv E hfree g w hv hv' h)

/-- The identifications `a^*M ≅ b^*M` and `b^*M ≅ c^*M` given by equalities `a = b` and `b = c`
of morphisms of schemes compose to the one given by `a = c`. -/
theorem pullbackCongr_app_trans_pullbackCongr_app {Z₁ Z₂ : Scheme.{u}}
    {a b c : Z₁ ⟶ Z₂} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (M : Z₂.Modules) :
    (Scheme.Modules.pullbackCongr h₁).app M ≪≫ (Scheme.Modules.pullbackCongr h₂).app M =
      (Scheme.Modules.pullbackCongr h₃).app M := by
  subst h₁ h₂
  ext1
  simp [Scheme.Modules.pullbackCongr]

variable {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- The cocycle condition for the comparisons of readings, at a factorization `t ≫ ρ = ρ'`. -/
theorem schemeReadingPullbackIso_comp_of_eq {T'' T' T : BigFppfOver B S hS} (t : T'' ⟶ T')
    (ρ : T' ⟶ T) (ρ' : T'' ⟶ T) (hg : t ≫ ρ = ρ') {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψP : representedAlgebraicSpace B S hS T' ⟶ X}
    {ψP' : representedAlgebraicSpace B S hS T'' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψ = ψP) (wt : representedSpaceMap B S hS t ≫ ψP = ψP')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψ = ψP') :
    (Scheme.Modules.pullback (siteSchemeHom t)).mapIso (schemeReadingPullbackIso E hE ρ wρ) ≪≫
      schemeReadingPullbackIso E hE t wt =
      (Scheme.Modules.pullbackComp (siteSchemeHom t) (siteSchemeHom ρ)).app (schemeReading E ψ) ≪≫
        (Scheme.Modules.pullbackCongr (f := siteSchemeHom t ≫ siteSchemeHom ρ)
          (g := siteSchemeHom ρ') (congrArg (fun x => siteSchemeHom x) hg)).app
          (schemeReading E ψ) ≪≫ schemeReadingPullbackIso E hE ρ' wρ' := by
  subst hg
  rw [schemeReadingPullbackIso_comp E hE t ρ wρ wt wρ']
  ext1
  simp [Scheme.Modules.pullbackCongr]

private theorem symm_trans_symm_trans_eq_of_shape {C : Type*} [Category C]
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ Q₄ R₁ R₂ : C} (m₁ : P₁ ≅ P₂) (m₂ : Q₁ ≅ P₁) (c₁ : Q₁ ≅ Q₂)
    (c₂ : Q₂ ≅ Q₃) (c₃ : Q₃ ≅ R₁) (k : R₁ ≅ R₂) (d : Q₃ ≅ Q₄) (ρ : R₂ ≅ Q₄) (e : Q₂ ≅ Q₄)
    (n : Q₄ ≅ P₂) (m₄ : R₂ ≅ P₃) (r : P₃ ≅ P₂)
    (hk : c₃ ≪≫ k = d ≪≫ ρ.symm) (hce : c₂ ≪≫ d = e) (hcoc : m₂ ≪≫ m₁ = c₁ ≪≫ e ≪≫ n)
    (hrpi : ρ ≪≫ n = m₄ ≪≫ r) :
    m₁.symm ≪≫ m₂.symm ≪≫ c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ k = r.symm ≪≫ m₄.symm := by
  ext1
  have hk' := congrArg Iso.hom hk
  have hce' := congrArg Iso.hom hce
  have hcoc' := congrArg Iso.hom hcoc
  have hrpi' := congrArg Iso.hom hrpi
  simp only [Iso.trans_hom, Iso.symm_hom] at hk' hce' hcoc' hrpi' ⊢
  have h₁ : c₁.hom ≫ e.hom = (m₂.hom ≫ m₁.hom) ≫ n.inv := by
    rw [hcoc']
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ : n.inv ≫ ρ.inv = r.inv ≫ m₄.inv :=
    calc n.inv ≫ ρ.inv = (r.inv ≫ m₄.inv) ≫ (m₄.hom ≫ r.hom) ≫ n.inv ≫ ρ.inv := by simp
      _ = (r.inv ≫ m₄.inv) ≫ (ρ.hom ≫ n.hom) ≫ n.inv ≫ ρ.inv := by rw [hrpi']
      _ = r.inv ≫ m₄.inv := by simp
  rw [hk', ← Category.assoc c₂.hom, hce', ← Category.assoc c₁.hom, h₁]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact h₂

section PullbackCoherence

variable {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ Y)
  {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree (ψ ≫ f)) ⟶ X}
  {v' : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
    (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ Y}
  (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree (ψ ≫ f)) ≫ (ψ ≫ f) = v)
  (hv' : representedSpaceMap B S hS (readingBundleSiteToBase (pullbackModule f E)
    (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ≫ ψ = v')
  (h : representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ) ≫ v = v' ≫ f)

/-- The identification `(f^*ℰ)_{ψ'} ≅ ℰ_u` of readings, for `ψ' ≫ f = u`. -/
def readingPullbackIsoOfEq {T₀ : BigFppfOver B S hS} (ψ' : representedAlgebraicSpace B S hS T₀ ⟶ Y)
    {u : representedAlgebraicSpace B S hS T₀ ⟶ X} (hu : ψ' ≫ f = u) :
    schemeReading (pullbackModule f E) ψ' ≅ schemeReading E u :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T₀)
      T₀.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T₀).inverse.mapIso
      (QuasiCoherentDescent.pullbackComparison B S hS ψ' f u hu E).symm)

/-- The comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})` lies over `T`: followed by the projection of
`𝐏(ℰ_{ψ ≫ f})` it is the projection of `𝐏((f^*ℰ)_ψ)`. -/
theorem readingBundleSitePullback_comp_toBase :
    readingBundleSitePullback f E hfree ψ ≫ readingBundleSiteToBase E hfree (ψ ≫ f) =
      readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ :=
  (isPullback_readingBundleSitePullback f E hfree ψ).w.trans (Category.comp_id _)

include hv' in
/-- The projection of `𝐏((f^*ℰ)_ψ)` to `T`, followed by `ψ ≫ f`, is `v' ≫ f`. -/
theorem representedSpaceMap_readingBundleSiteToBase_comp_comp :
    representedSpaceMap B S hS (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ≫ (ψ ≫ f) = v' ≫ f := by
  rw [← hv', Category.assoc]

/-- The two identifications of the inverse image of `ℰ_{ψ ≫ f}` along the projection of
`𝐏((f^*ℰ)_ψ)` with the inverse image of `(f^*ℰ)_ψ`, through `readingBundlePullbackIso` and through
`readingPullbackIso`, agree. -/
theorem pullbackComp_inv_app_comp_map_readingBundlePullbackIso_inv :
    ((Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSiteToBase
        (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))
        (𝟙 ((BigFppfOver.toScheme B S hS).obj T))).app (schemeReading E (ψ ≫ f))).symm ≪≫
      (Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))).mapIso
        (readingBundlePullbackIso f E ψ).symm =
      (Scheme.Modules.pullbackCongr (Category.comp_id _)).app (schemeReading E (ψ ≫ f)) ≪≫
        ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))).mapIso
          (readingPullbackIso f E ψ)).symm := by
  have hk := pullbackComp_id_hom_app (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)) (schemeReading E (ψ ≫ f))
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, readingBundlePullbackIso_inv, CategoryTheory.Functor.map_comp]
  rw [← hk, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

include hv in
/-- The comparisons of readings along `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f}) ⟶ T` compose to the comparison
along the projection of `𝐏((f^*ℰ)_ψ)`, up to the identification of the two composites. -/
theorem map_moduleReadingPullbackIso_hom_comp_moduleReadingPullbackIso_hom_pullback :
    (Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).mapIso
        (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv) ≪≫
      schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h =
      (Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSitePullback f E hfree ψ))
          (siteSchemeHom (readingBundleSiteToBase E hfree (ψ ≫ f)))).app
          (schemeReading E (ψ ≫ f)) ≪≫
        (Scheme.Modules.pullbackCongr
          (f := siteSchemeHom (readingBundleSitePullback f E hfree ψ) ≫
            siteSchemeHom (readingBundleSiteToBase E hfree (ψ ≫ f)))
          (g := siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))
          (congrArg (fun x => siteSchemeHom x)
          (readingBundleSitePullback_comp_toBase E hfree f ψ))).app
          (schemeReading E (ψ ≫ f)) ≪≫
        schemeReadingPullbackIso E hE (readingBundleSiteToBase (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
          (representedSpaceMap_readingBundleSiteToBase_comp_comp E hfree f ψ hv') :=
  schemeReadingPullbackIso_comp_of_eq E _ _ _ (readingBundleSitePullback_comp_toBase E hfree f
      ψ) hv h
    (representedSpaceMap_readingBundleSiteToBase_comp_comp E hfree f ψ hv')

include hv' in
/-- The comparisons of readings of `ℰ` and of `f^*ℰ` along the projection of `𝐏((f^*ℰ)_ψ)` are
intertwined by `readingPullbackIso`. -/
theorem map_readingPullbackIso_hom_comp_moduleReadingPullbackIso_hom :
    (Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))).mapIso
        (readingPullbackIso f E ψ) ≪≫
      schemeReadingPullbackIso E hE (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
        (representedSpaceMap_readingBundleSiteToBase_comp_comp E hfree f ψ hv') =
      schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
        (readingBundleSiteToBase (pullbackModule f E)
          (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv' ≪≫
        readingPullbackIso f E v' :=
  readingPullbackIso_comp f E
    (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv'
      (representedSpaceMap_readingBundleSiteToBase_comp_comp E hfree f ψ hv')

/-- `readingBundleSitePullback_comp_toBase` on the underlying schemes, with an identity appended
on the right. -/
theorem siteSchemeHom_readingBundleSitePullback_comp_toBase :
    siteSchemeHom (readingBundleSitePullback f E hfree ψ) ≫
      siteSchemeHom (readingBundleSiteToBase E hfree (ψ ≫ f)) =
      siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ≫
        𝟙 ((BigFppfOver.toScheme B S hS).obj T) :=
  (congrArg (fun x => siteSchemeHom x) (readingBundleSitePullback_comp_toBase E hfree f ψ)).trans
    (Category.comp_id _).symm

include hv hv' h in
/-- The comparison of Stacks 01O3 along `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`, through the comparisons of
readings. -/
theorem symm_trans_symm_trans_tautologicalBaseChangeIso_pullback :
    (schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h).symm ≪≫
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).mapIso
        (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv)).symm ≪≫
      Stacks.RelativeProj.tautologicalBaseChangeIso (𝟙 _) (schemeReading E (ψ ≫ f))
        (schemeReading (pullbackModule f E) ψ) (readingBundlePullbackIso f E ψ) =
      (readingPullbackIso f E v').symm ≪≫
        (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv').symm :=
  symm_trans_symm_trans_eq_of_shape
    (schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h)
    ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).mapIso
      (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv))
    ((Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSitePullback f E hfree ψ))
      (siteSchemeHom (readingBundleSiteToBase E hfree (ψ ≫ f)))).app (schemeReading E (ψ ≫ f)))
    ((Scheme.Modules.pullbackCongr
      (siteSchemeHom_readingBundleSitePullback_comp_toBase E hfree f ψ)).app
        (schemeReading E (ψ ≫ f)))
    ((Scheme.Modules.pullbackComp (siteSchemeHom (readingBundleSiteToBase
      (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))
      (𝟙 ((BigFppfOver.toScheme B S hS).obj T))).app (schemeReading E (ψ ≫ f))).symm
    ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))).mapIso
      (readingBundlePullbackIso f E ψ).symm)
    ((Scheme.Modules.pullbackCongr (Category.comp_id _)).app (schemeReading E (ψ ≫ f)))
    ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))).mapIso (readingPullbackIso f E ψ))
    ((Scheme.Modules.pullbackCongr
      (f := siteSchemeHom (readingBundleSitePullback f E hfree ψ) ≫
        siteSchemeHom (readingBundleSiteToBase E hfree (ψ ≫ f)))
      (g := siteSchemeHom (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ))
      (congrArg (fun x => siteSchemeHom x)
        (readingBundleSitePullback_comp_toBase E hfree f ψ))).app (schemeReading E (ψ ≫ f)))
    (schemeReadingPullbackIso E hE (readingBundleSiteToBase (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
      (representedSpaceMap_readingBundleSiteToBase_comp_comp E hfree f ψ hv'))
    (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
      (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv')
    (readingPullbackIso f E v')
    (pullbackComp_inv_app_comp_map_readingBundlePullbackIso_inv E hfree f ψ)
    (pullbackCongr_app_trans_pullbackCongr_app _ _ _ _)
    (map_moduleReadingPullbackIso_hom_comp_moduleReadingPullbackIso_hom_pullback E hfree f ψ hv hv'
      h)
    (map_readingPullbackIso_hom_comp_moduleReadingPullbackIso_hom E hfree f ψ hv')

private theorem inv_comp_inv_comp_eq_of_iso_shape {C : Type*} [Category C]
    {P₁ P₂ P₃ Q₁ R₂ W W' : C} (m₁ : P₁ ≅ P₂) (m₂ : Q₁ ≅ P₁) (U : Q₁ ⟶ W) (Θ : W ⟶ W')
    (c : Q₁ ≅ R₂) (u' : R₂ ⟶ W') (m₄ : R₂ ≅ P₃) (r : P₃ ≅ P₂)
    (hspec : U ≫ Θ = c.hom ≫ u') (hI : m₁.symm ≪≫ m₂.symm ≪≫ c = r.symm ≪≫ m₄.symm) :
    m₁.inv ≫ (m₂.inv ≫ U) ≫ Θ = r.inv ≫ m₄.inv ≫ u' := by
  have h := congrArg Iso.hom hI
  simp only [Iso.trans_hom, Iso.symm_hom] at h
  rw [Category.assoc, hspec, ← Category.assoc m₂.inv, ← Category.assoc m₁.inv, h,
    Category.assoc]

include hv hv' h in
/-- **Stacks 01O3 along the comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`, read through the comparisons
of readings.** -/
theorem schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv_pullback :
    (schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h).inv ≫
        (Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).map
          ((schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv).inv ≫
            Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E (ψ ≫ f))) ≫
        (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (𝟙 _)
          (schemeReading E (ψ ≫ f)) (schemeReading (pullbackModule f E) ψ)
          (readingBundlePullbackIso f E ψ)).hom =
      (readingPullbackIso f E v').inv ≫
        (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv').inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ) :=
  (congrArg (fun z => _ ≫ z ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans
    (inv_comp_inv_comp_eq_of_iso_shape
      (schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h)
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).mapIso
        (schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv))
      ((Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).map
        (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E (ψ ≫ f))))
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (𝟙 _)
          (schemeReading E (ψ ≫ f)) (schemeReading (pullbackModule f E) ψ)
          (readingBundlePullbackIso f E ψ)).hom
      (Stacks.RelativeProj.tautologicalBaseChangeIso (𝟙 _) (schemeReading E (ψ ≫ f))
        (schemeReading (pullbackModule f E) ψ) (readingBundlePullbackIso f E ψ))
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ))
      (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv')
      (readingPullbackIso f E v')
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec' (𝟙 _)
          (schemeReading E (ψ ≫ f)) (schemeReading (pullbackModule f E) ψ)
          (readingBundlePullbackIso f E ψ))
      (symm_trans_symm_trans_tautologicalBaseChangeIso_pullback E hfree f ψ hv hv' h))

include hv hv' in
/-- `schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv_pullback` with the composite
`v' ≫ f` replaced by a morphism `u` with `v' ≫ f = u`. -/
theorem schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv_pullback_of_eq
    {u : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ X} (hu : v' ≫ f = u)
    (h' : representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ) ≫ v = u) :
    (schemeReadingPullbackIso E hE (readingBundleSitePullback f E hfree ψ) h').inv ≫
        (Scheme.Modules.pullback (siteSchemeHom (readingBundleSitePullback f E hfree ψ))).map
          ((schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree (ψ ≫ f)) hv).inv ≫
            Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E (ψ ≫ f))) ≫
        (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (𝟙 _)
          (schemeReading E (ψ ≫ f)) (schemeReading (pullbackModule f E) ψ)
          (readingBundlePullbackIso f E ψ)).hom =
      (readingPullbackIsoOfEq E f v' hu).inv ≫
        (schemeReadingPullbackIso (pullbackModule f E)
          (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv').inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ) := by
  subst hu
  exact schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv_pullback E hfree f ψ hv hv' h'

include hv' in
/-- The reading of `pullbackComparison ≫ κ₀'⁻¹ ≫ q'` along `v' ≫ f`, for a quotient `q'` of
`v'^*f^*ℰ` whose reading is the tautological quotient of `𝐏((f^*ℰ)_ψ)`. -/
theorem readingFunctor_map_pullbackComparison_hom_comp_inv_comp_of_quotientReadingHyp_comp
    {N' L' : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)) (isAlgebraicSpace_yoneda B S hS _)}
    (q' : N' ⟶ L')
    (κ₀' : N' ≅ (modulePullback B S hS v').obj (pullbackModule f E))
    (εL' : representedZariskiModule B S hS _ L' ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading (pullbackModule f E) ψ))
    (hq' : QuotientReadingHyp (pullbackModule f E)
      (isQuasicoherentOnSite_pullbackModule f E) hv'
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ)) εL' q'
      κ₀') : (readingFunctor (readingBundleSite (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).map
        ((QuasiCoherentDescent.pullbackComparison B S hS v' f (v' ≫ f) rfl E).hom ≫ κ₀'.inv ≫ q') =
      ((readingPullbackIso f E v').inv ≫
        (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv').inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ)) ≫
        εL'.inv :=
  (CategoryTheory.Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·)
      ((readingFunctor_map_inv_comp_of_quotientReadingHyp (pullbackModule f E) hv' _ εL' q' κ₀'
        hq').trans (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm)

include hv' in
/-- `readingFunctor_map_pullbackComparison_hom_comp_inv_comp_of_quotientReadingHyp_comp` with the
composite `v' ≫ f` replaced by a morphism `u` with `v' ≫ f = u`. -/
theorem readingFunctor_map_pullbackComparison_hom_comp_inv_comp_of_quotientReadingHyp
    {u : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ X} (hu : v' ≫ f = u)
    {N' L' : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)) (isAlgebraicSpace_yoneda B S hS _)}
    (q' : N' ⟶ L')
    (κ₀' : N' ≅ (modulePullback B S hS v').obj (pullbackModule f E))
    (εL' : representedZariskiModule B S hS _ L' ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading (pullbackModule f E) ψ))
    (hq' : QuotientReadingHyp (pullbackModule f E)
      (isQuasicoherentOnSite_pullbackModule f E) hv'
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ)) εL' q'
      κ₀') :
    (readingFunctor (readingBundleSite (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)).map
        ((QuasiCoherentDescent.pullbackComparison B S hS v' f u hu E).hom ≫ κ₀'.inv ≫ q') =
      ((readingPullbackIsoOfEq E f v' hu).inv ≫
        (schemeReadingPullbackIso (pullbackModule f E)
        (isQuasicoherentOnSite_pullbackModule f E)
          (readingBundleSiteToBase (pullbackModule f E)
            (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) hv').inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ)) ≫
        εL'.inv := by
  subst hu
  exact readingFunctor_map_pullbackComparison_hom_comp_inv_comp_of_quotientReadingHyp_comp E hfree f
    ψ hv' q' κ₀' εL' hq'

include hv hv' in
/-- **Stacks 01O3 on the represented spaces along `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`**: the inverse
image of a quotient whose reading is the tautological quotient of `𝐏(ℰ_{ψ ≫ f})` is, up to an
isomorphism of the targets, a quotient whose reading is the tautological quotient of
`𝐏((f^*ℰ)_ψ)`, read through `v'^*f^*ℰ ≅ u^*ℰ` for `v' ≫ f = u`. -/
theorem exists_iso_readingBundleSitePullback_quotient
    {u : representedAlgebraicSpace B S hS (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶ X} (hu : v' ≫ f = u)
    (h' : representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ) ≫ v = u)
    {N L : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite E hfree (ψ ≫ f)))
      (isAlgebraicSpace_yoneda B S hS _)}
    (hL : L.IsQuasicoherentOnSite) (q : N ⟶ L) (κ₀ : N ≅ (modulePullback B S hS v).obj E)
    (εL : representedZariskiModule B S hS _ L ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading E (ψ ≫ f)))
    (hq : QuotientReadingHyp E hE hv
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E (ψ ≫ f))) εL q κ₀)
    {N' L' : Modules.{u, u} B S hS (yoneda.obj (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)) (isAlgebraicSpace_yoneda B S hS _)}
    (hL' : L'.IsQuasicoherentOnSite) (q' : N' ⟶ L')
    (κ₀' : N' ≅ (modulePullback B S hS v').obj (pullbackModule f E))
    (εL' : representedZariskiModule B S hS _ L' ≅
      Stacks.RelativeProj.tautologicalDatumTwist (schemeReading (pullbackModule f E) ψ))
    (hq' : QuotientReadingHyp (pullbackModule f E)
      (isQuasicoherentOnSite_pullbackModule f E) hv'
      (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading (pullbackModule f E) ψ)) εL' q'
      κ₀') :
    ∃ θ : (modulePullback B S hS
        (representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ))).obj L ≅ L',
      ((QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ)) v u h' E).hom ≫
        (modulePullback B S hS
          (representedSpaceMap B S hS (readingBundleSitePullback f E hfree ψ))).map
          (κ₀.inv ≫ q)) ≫ θ.hom =
        (QuasiCoherentDescent.pullbackComparison B S hS v' f u hu E).hom ≫ κ₀'.inv ≫ q' :=
  exists_iso_pullbackComparison_hom_comp_map_of_reading E (readingBundleSitePullback f E hfree ψ) h'
    hL q κ₀ εL _ ((readingFunctor_map_inv_comp_of_quotientReadingHyp E hv _ εL q κ₀ hq).trans
      (Category.assoc _ _ _).symm) hL' _ εL' _
    (readingFunctor_map_pullbackComparison_hom_comp_inv_comp_of_quotientReadingHyp E hfree f ψ hv'
      hu q' κ₀' εL' hq')
    (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso (𝟙 _)
          (schemeReading E (ψ ≫ f)) (schemeReading (pullbackModule f E) ψ)
          (readingBundlePullbackIso f E ψ))
    (schemeReadingPullbackIso_inv_comp_map_tautologicalDatumUniv_pullback_of_eq E hfree f ψ hv hv'
      hu h')

end PullbackCoherence

/-- The comparison `𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)`, as a morphism of algebraic spaces. -/
abbrev readingBundleSpaceMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ projectiveBundle E hfree :=
  ObjectProperty.homMk (readingBundleToSpace ψ E hfree)

/-- The morphism `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)`, into the presenting chart of `𝐏(ℰ)`. -/
abbrev bundleCoverToAtlas {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    readingBundleSite E hfree (chartBaseChangeToSpace ψ) ⟶
      (projectiveBundleChartPresentation E hfree).U :=
  bundleCoverToChart ψ E hfree

/-- The square formed by the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_ψ)`, the comparison `𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)`, the
morphism to the presenting chart and the atlas of `𝐏(ℰ)` commutes. -/
theorem representedSpaceMap_bundleCover_comp_readingBundleSpaceMap {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    representedSpaceMap B S hS (bundleCover ψ E hfree) ≫ readingBundleSpaceMap E hfree ψ =
      representedSpaceMap B S hS (bundleCoverToAtlas E hfree ψ) ≫ projectiveBundleAtlas E hfree :=
  ObjectProperty.hom_ext _ (bundleCover_comp_readingBundleToSpace ψ E hfree)

/-- On the presenting chart, the pulled-back tautological quotient of `𝐏(ℰ)` is the chart
quotient. -/
theorem exists_iso_projectiveBundleTautological_atlas :
    ∃ θ : (modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
        (projectiveBundleTwist E hfree).obj ≅ projectiveBundleChartTwist E hfree,
      ((QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).hom ≫
        (modulePullback B S hS (projectiveBundleAtlas E hfree)).map
          (projectiveBundleTautological E hfree).hom) ≫ θ.hom =
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm.inv ≫
        projectiveBundleChartQuotient E hfree := by
  refine ⟨projectiveBundleTwistAtlasIso E hfree, ?_⟩
  rw [Iso.symm_inv, Category.assoc, modulePullback_map_projectiveBundleTautological]

/-- The reading of the chart quotient of `𝐏(ℰ)` on the presenting chart is the tautological
quotient of the chart bundle, through the comparisons of readings. -/
theorem readingFunctor_map_inv_comp_projectiveBundleChartQuotient :
    (readingFunctor (projectiveBundleChartPresentation E hfree).U).map
        ((QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm.inv ≫
        projectiveBundleChartQuotient E hfree) =
      ((schemeReadingPullbackIso E hE (projectiveBundleChartProj E hfree)
          (representedSpaceMap_projectiveBundleChartProj_comp E hfree)).inv ≫
        chartBundleTautological E (bundleBaseChart X)) ≫
        (projectiveBundleChartTwistReadingIso E hfree).inv :=
  (readingFunctor_map_inv_comp_of_quotientReadingHyp E
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
    (chartBundleTautological E (bundleBaseChart X)) (projectiveBundleChartTwistReadingIso E hfree)
    (projectiveBundleChartQuotient E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm
    (quotientReadingHyp_projectiveBundle E hfree)).trans (Category.assoc _ _ _).symm

/-- The reading of `readingBundleQuotient` is the tautological quotient of `𝐏(ℰ_ψ)`, through the
comparisons of readings. -/
theorem readingFunctor_map_inv_comp_readingBundleQuotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v) :
    (readingFunctor (readingBundleSite E hfree ψ)).map
        ((Iso.refl _).inv ≫ readingBundleQuotient E hfree ψ hv) =
      ((schemeReadingPullbackIso E hE (readingBundleSiteToBase E hfree ψ) hv).inv ≫
        Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ)) ≫
        (readingBundleTwistReadingIso E hfree ψ).inv :=
  (readingFunctor_map_inv_comp_of_quotientReadingHyp E hv
    (Stacks.RelativeProj.tautologicalDatumUniv (schemeReading E ψ))
    (readingBundleTwistReadingIso E hfree ψ) (readingBundleQuotient E hfree ψ hv) (Iso.refl _)
    (quotientReadingHyp_readingBundleQuotient E hfree ψ hv)).trans (Category.assoc _ _ _).symm

/-- The morphism `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)` to the presenting chart bundle lies over `T' ⟶ U`. -/
theorem bundleCoverToChart_comp_projectiveBundleChartProj {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    bundleCoverToAtlas E hfree ψ ≫ projectiveBundleChartProj E hfree =
      readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ) ≫ chartBaseChangeToChart ψ :=
  (isPullback_readingBundleSiteMap E hfree (chartBaseChangeToChart ψ) (chartBaseChange_w ψ)).w

end ReadingTwist

end AlgebraicGeometry.Space.PrivateChern

end
