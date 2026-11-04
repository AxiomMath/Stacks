module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChangeDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image along a finite morphism of finite presentation: abelian and module coefficients

This file carries the geometric argument of the proof of [Stacks, Tag 095R] for an arbitrary
property `P` of sheaves on the small étale sites of a big étale site, with values in an arbitrary
coefficient category `A`: if `P` is invariant under isomorphism and inverse image (Stacks 095G),
local for open coverings (Stacks 095F) and for coverings by immersions with constructible images
of a quasi-compact quasi-separated scheme (Stacks 09YR), descends along surjections of
quasi-compact quasi-separated schemes (Stacks 095Q), and is preserved by direct image along finite
étale morphisms (Stacks 095H), then it is preserved by direct image along every finite morphism of
finite presentation.

The argument is the source's, with the stratification of Stacks 095K (2) in place of the
surjection of 095K (1):

* by Stacks 095F, and the base change of a finite direct image along the open immersions of an
  affine open covering (Stacks 0959), the base may be assumed affine;
* over an affine base `S`, Stacks 095K (2) partitions `S` into finitely many affine constructible
  locally closed strata `S_i`, each with a surjective finite locally free `S'_i ⟶ S_i` over which
  the reduction of the base change of `f` is a finite disjoint union of copies of the reduction of
  `S'_i`; by Stacks 09YR it suffices to treat the restriction to each `S_i`, by Stacks 095Q its
  inverse image on `S'_i`, and by Stacks 0959 that is the direct image along the base change
  `f'_i : T'_i ⟶ S'_i`;
* the reductions `ν : (T'_i)_red ⟶ T'_i` and `ν' : (S'_i)_red ⟶ S'_i` are universal
  homeomorphisms, so their direct images are equivalences of categories of sheaves
  (`AlgebraicGeometry.isEquivalence_smallPushforward_of_universalHomeomorphism`, from the
  topological invariance of the small étale site, Stacks 04DZ/03SI); hence every sheaf on `T'_i`
  is `ν_*` of its inverse image, and
  `f'_{i,*} = f'_{i,*} ν_* ν⁻¹ = ν'_* q_* ν⁻¹` for the finite étale codiagonal
  `q : (T'_i)_red ≅ ∐ (S'_i)_red ⟶ (S'_i)_red`; `q_*` is handled by Stacks 095H and `ν'_*` by
  Stacks 095Q along `ν'`, the counit `ν'⁻¹ν'_* ⟶ 1` being invertible.

The base change of a finite direct image is used only up to *some* isomorphism, so it is taken as
a hypothesis of the generic statement in that form, and supplied for each coefficient category
from the library's Stacks 0959 for abelian sheaves and for sheaves of modules on Mathlib's small
étale site, carried to the bounded site along
`AlgebraicGeometry.SmallEtale.sheafEquiv`
(`AlgebraicGeometry.nonempty_smallInverseImage_smallPushforward_iso_of_etaleSite`).

## Main results

* `AlgebraicGeometry.isEquivalence_smallPushforward_of_universalHomeomorphism` — the direct image
  along a universal homeomorphism of a big étale site is an equivalence, for any coefficients.
* `AlgebraicGeometry.nonempty_smallInverseImage_smallPushforward_iso_of_etaleSite` — an
  identification of `g⁻¹ f_*` with `f'_* g'⁻¹` on Mathlib's small étale sites gives one on the
  bounded sites.
* `AlgebraicGeometry.prop_smallPushforward_of_isFinite_of_finitePresentation` — the generic form of
  Stacks 095R.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward_of_isFinite_of_finitePresentation` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_pushforward_of_isFinite_of_finitePresentation` —
  **Stacks 095R** for abelian sheaves and for sheaves of modules over a Noetherian ring. The case
  of sheaves of sets is `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_isFinite`.

## References

* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 095K](https://stacks.math.columbia.edu/tag/095K)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-! ### Universal homeomorphisms -/

section UniversalHomeomorphism

variable {S T : B.Scheme} (f : T ⟶ S) [UniversalHomeomorphism (B.inclusion.map f)]
  (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u + 1} A]

/-- **The direct image along a universal homeomorphism of a big étale site is an equivalence**, for
sheaves with values in any category with small limits. On Mathlib's small étale sites base change
along a universal homeomorphism exhibits the site of the target as a dense subsite of that of the
source (`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`), so restriction along it
is an equivalence; the direct images of the two presentations of the small étale site agree up to
the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv`
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`). -/
theorem isEquivalence_smallPushforward_of_universalHomeomorphism :
    (B.smallPushforward f A).IsEquivalence := by
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsDenseSubsite
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism (B.inclusion.map f)
  have hS : ((SmallEtale.toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology).IsEquivalence :=
    inferInstanceAs (SmallEtale.sheafEquiv B S.obj S.property A).inverse.IsEquivalence
  have hT : ((SmallEtale.toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology).IsEquivalence :=
    inferInstanceAs (SmallEtale.sheafEquiv B T.obj T.property A).inverse.IsEquivalence
  have : ((Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous
      A S.obj.smallEtaleTopology T.obj.smallEtaleTopology ⋙
        (SmallEtale.toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
          (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology).IsEquivalence :=
    inferInstance
  have : ((SmallEtale.toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology ⋙
        B.smallPushforward f A).IsEquivalence :=
    Functor.isEquivalence_of_iso (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f A)
  exact Functor.isEquivalence_of_comp_left
    ((SmallEtale.toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology) _

variable [(B.smallPushforward f A).IsRightAdjoint]

/-- Along a universal homeomorphism, the unit `F ⟶ f_* f⁻¹ F` is an isomorphism. -/
theorem isIso_smallPullbackAdjunction_unit_app_of_universalHomeomorphism
    (F : Sheaf (SmallEtale.topology B S.1 S.property) A) :
    IsIso ((B.smallPullbackAdjunction f A).unit.app F) := by
  have := isEquivalence_smallPushforward_of_universalHomeomorphism B f A
  exact (B.smallPullbackAdjunction f A).isIso_unit_app_of_iso
    ((B.smallPushforward f A).objObjPreimageIso F).symm

/-- Along a universal homeomorphism, the counit `f⁻¹ f_* G ⟶ G` is an isomorphism. -/
theorem isIso_smallPullbackAdjunction_counit_app_of_universalHomeomorphism
    (G : Sheaf (SmallEtale.topology B T.1 T.property) A) :
    IsIso ((B.smallPullbackAdjunction f A).counit.app G) := by
  have := isEquivalence_smallPushforward_of_universalHomeomorphism B f A
  infer_instance

end UniversalHomeomorphism

/-! ### Base change of a direct image, from Mathlib's small étale site -/

section Transport

/-- **An identification of `g⁻¹ f_*` with `f'_* g'⁻¹` on Mathlib's small étale sites gives one on
the bounded small étale sites.** The two presentations of the small étale site have equivalent
categories of sheaves (`AlgebraicGeometry.SmallEtale.sheafEquiv`), compatibly with direct images
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`) and with inverse images
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`). -/
theorem nonempty_smallInverseImage_smallPushforward_iso_of_etaleSite (A : Type u')
    [Category.{v'} A] [HasLimitsOfSize.{u, u} A] {S S' T T' : B.Scheme} (f : T ⟶ S)
    (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    [(B.smallPushforward g A).IsRightAdjoint] [(B.smallPushforward g' A).IsRightAdjoint]
    {LUg : Sheaf S.obj.smallEtaleTopology A ⥤ Sheaf S'.obj.smallEtaleTopology A}
    (adjUg : LUg ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map g)).sheafPushforwardContinuous A S.obj.smallEtaleTopology
        S'.obj.smallEtaleTopology)
    {LUg' : Sheaf T.obj.smallEtaleTopology A ⥤ Sheaf T'.obj.smallEtaleTopology A}
    (adjUg' : LUg' ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map g')).sheafPushforwardContinuous A T.obj.smallEtaleTopology
        T'.obj.smallEtaleTopology)
    (h : ∀ F : Sheaf T.obj.smallEtaleTopology A, Nonempty (LUg.obj
      (((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
        A S.obj.smallEtaleTopology T.obj.smallEtaleTopology).obj F) ≅
      ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f')).sheafPushforwardContinuous
        A S'.obj.smallEtaleTopology T'.obj.smallEtaleTopology).obj (LUg'.obj F)))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) A) :
    Nonempty ((B.smallInverseImage g A).obj ((B.smallPushforward f A).obj F) ≅
      (B.smallPushforward f' A).obj ((B.smallInverseImage g' A).obj F)) := by
  let ES' := SmallEtale.sheafEquiv B S'.obj S'.property A
  let ET := SmallEtale.sheafEquiv B T.obj T.property A
  have pg := SmallEtale.sheafEquivPullbackBaseChangeIso B g A adjUg (B.smallPullbackAdjunction g A)
  have pg' :=
    SmallEtale.sheafEquivPullbackBaseChangeIso B g' A adjUg' (B.smallPullbackAdjunction g' A)
  have hpush : ∀ {X Y : B.Scheme} (u : Y ⟶ X) (G : Sheaf (SmallEtale.topology B Y.1 Y.property) A),
      (SmallEtale.sheafEquiv B X.obj X.property A).functor.obj ((B.smallPushforward u A).obj G) ≅
        ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (B.inclusion.map u)).sheafPushforwardContinuous
          A X.obj.smallEtaleTopology Y.obj.smallEtaleTopology).obj
          ((SmallEtale.sheafEquiv B Y.obj Y.property A).functor.obj G) := fun u G =>
    (SmallEtale.sheafEquiv B _ _ A).functor.mapIso
      ((B.smallPushforward u A).mapIso ((SmallEtale.sheafEquiv B _ _ A).unitIso.app G) ≪≫
        ((SmallEtale.toEtaleSitePushforwardBaseChangeIso B u A).app _).symm) ≪≫
      (SmallEtale.sheafEquiv B _ _ A).counitIso.app _
  obtain ⟨e⟩ := h (ET.functor.obj F)
  exact ⟨ES'.functor.preimageIso ((pg.app _).symm ≪≫ LUg.mapIso (hpush f F) ≪≫ e ≪≫
    ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f')).sheafPushforwardContinuous
          A S'.obj.smallEtaleTopology T'.obj.smallEtaleTopology).mapIso (pg'.app F) ≪≫
      (hpush f' _).symm)⟩

end Transport


/-! ### The generic statement -/

section Generic

variable (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u + 1} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S), (B.smallPushforward f A).IsRightAdjoint]
  (P : ∀ X : B.Scheme, Sheaf (SmallEtale.topology B X.1 X.property) A → Prop)
  (hiso : ∀ (X : B.Scheme) {F G : Sheaf (SmallEtale.topology B X.1 X.property) A},
    (F ≅ G) → P X F → P X G)
  (hpull : ∀ {X Y : B.Scheme} (f : X ⟶ Y) (F : Sheaf (SmallEtale.topology B Y.1 Y.property) A),
    P Y F → P X ((B.smallInverseImage f A).obj F))
  (hopen : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.1 X.property) A) {I : Type u}
    (U : I → B.Scheme) (j : ∀ k, U k ⟶ X), (∀ k, IsOpenImmersion (B.inclusion.map (j k))) →
    Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base →
    (∀ k, P (U k) ((B.smallInverseImage (j k) A).obj F)) → P X F)
  (himm : ∀ (X : B.Scheme), CompactSpace X.obj → QuasiSeparatedSpace X.obj →
    ∀ (F : Sheaf (SmallEtale.topology B X.1 X.property) A) {n : ℕ} (T : Fin n → B.Scheme)
      (j : ∀ i, T i ⟶ X), (∀ i, IsImmersion (B.inclusion.map (j i))) →
      (∀ i, Topology.IsConstructible (Set.range (B.inclusion.map (j i)).base)) →
      (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base →
      (∀ i, P (T i) ((B.smallInverseImage (j i) A).obj F)) → P X F)
  (hdesc : ∀ {X Y : B.Scheme} (f : X ⟶ Y), Function.Surjective (B.inclusion.map f).base →
    CompactSpace X.obj → QuasiSeparatedSpace X.obj → CompactSpace Y.obj →
    QuasiSeparatedSpace Y.obj → ∀ G : Sheaf (SmallEtale.topology B Y.1 Y.property) A,
      P X ((B.smallInverseImage f A).obj G) → P Y G)
  (hetale : ∀ {T S : B.Scheme} (p : T ⟶ S), IsFinite (B.inclusion.map p) →
    Etale (B.inclusion.map p) → ∀ F : Sheaf (SmallEtale.topology B T.1 T.property) A,
      P T F → P S ((B.smallPushforward p A).obj F))
  (hbc : ∀ {S S' T T' : B.Scheme} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T),
    IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g) → IsFinite (B.inclusion.map f) →
    ∀ F : Sheaf (SmallEtale.topology B T.1 T.property) A,
      Nonempty ((B.smallInverseImage g A).obj ((B.smallPushforward f A).obj F) ≅
        (B.smallPushforward f' A).obj ((B.smallInverseImage g' A).obj F)))

include hiso hpull hdesc hetale in
/-- **The direct image of the reduction of a split finite cover.** Let `f' : T' ⟶ S'` be a morphism
of a big étale site with `S'` affine, and suppose the reduction of `T'` is identified, over the
reduction of `S'`, with a finite disjoint union of copies of the reduction of `S'`. Then `f'_*`
preserves `P`. Every sheaf on `T'` is the direct image of its inverse image to `(T')_red`, the
reduction being a universal homeomorphism, so `f'_*` is `ν'_* q_*` of that inverse image, with
`q : (T')_red ⟶ (S')_red` finite étale and `ν'` the reduction of `S'`. -/
theorem prop_smallPushforward_of_split_reduction {T' S' : B.Scheme} (f' : T' ⟶ S')
    [IsAffine (B.inclusion.obj S')] [IsAffine (B.inclusion.obj T')] {m : ℕ}
    (q : (B.inclusion.obj T').nilradical.subscheme ⟶ (B.inclusion.obj S').nilradical.subscheme)
    (e : (B.inclusion.obj T').nilradical.subscheme ≅
      ∐ (fun _ : Fin m ↦ (B.inclusion.obj S').nilradical.subscheme))
    (hq : q ≫ (B.inclusion.obj S').nilradical.subschemeι =
      (B.inclusion.obj T').nilradical.subschemeι ≫ B.inclusion.map f')
    (he : e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 (B.inclusion.obj S').nilradical.subscheme) = q)
    (G : Sheaf (SmallEtale.topology B T'.1 T'.property) A) (hG : P T' G) :
    P S' ((B.smallPushforward f' A).obj G) := by
  have hZ : B.Contains (B.inclusion.obj T').nilradical.subscheme :=
    Scheme.size_lt_of_isClosedImmersion (B.inclusion.obj T').nilradical.subschemeι T'.property
  have hS'r : B.Contains (B.inclusion.obj S').nilradical.subscheme :=
    Scheme.size_lt_of_isClosedImmersion (B.inclusion.obj S').nilradical.subschemeι S'.property
  let ZB : B.Scheme := B.obj _ hZ
  let S'rB : B.Scheme := B.obj _ hS'r
  let νB : ZB ⟶ T' := ObjectProperty.homMk (B.inclusion.obj T').nilradical.subschemeι
  let ν'B : S'rB ⟶ S' := ObjectProperty.homMk (B.inclusion.obj S').nilradical.subschemeι
  let qB : ZB ⟶ S'rB := ObjectProperty.homMk q
  have hqB : qB ≫ ν'B = νB ≫ f' :=
    B.inclusion.map_injective (by simp only [Functor.map_comp]; exact hq)
  have : UniversalHomeomorphism (B.inclusion.map νB) :=
    inferInstanceAs (UniversalHomeomorphism (B.inclusion.obj T').nilradical.subschemeι)
  have : UniversalHomeomorphism (B.inclusion.map ν'B) :=
    inferInstanceAs (UniversalHomeomorphism (B.inclusion.obj S').nilradical.subschemeι)
  have hqfin : IsFinite (B.inclusion.map qB) := by
    change IsFinite q
    rw [← he]
    infer_instance
  have hqet : Etale (B.inclusion.map qB) := by
    change Etale q
    rw [← he]
    have : IsZariskiLocalAtSource @Etale :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    have : Etale (Sigma.desc (fun _ : Fin m ↦ 𝟙 (B.inclusion.obj S').nilradical.subscheme)) :=
      IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun _ => inferInstance)
    infer_instance
  have : IsAffine S'rB.obj :=
    isAffine_of_isAffineHom (B.inclusion.obj S').nilradical.subschemeι
  have : IsAffine S'.obj := ‹IsAffine (B.inclusion.obj S')›
  let K := (B.smallInverseImage νB A).obj G
  let L := (B.smallPushforward qB A).obj K
  have := isIso_smallPullbackAdjunction_unit_app_of_universalHomeomorphism B νB A G
  have := isIso_smallPullbackAdjunction_counit_app_of_universalHomeomorphism B ν'B A L
  let φ : (B.smallPushforward f' A).obj G ≅ (B.smallPushforward ν'B A).obj L :=
    (B.smallPushforward f' A).mapIso (asIso ((B.smallPullbackAdjunction νB A).unit.app G)) ≪≫
      (smallEtaleSheafPushforwardCompIso B ZB T' S' νB f' A).app K ≪≫
      eqToIso (by rw [← hqB]) ≪≫
      ((smallEtaleSheafPushforwardCompIso B ZB S'rB S' qB ν'B A).app K).symm
  refine hiso S' φ.symm (hdesc ν'B
    (Stacks.Etale.surjective_of_universalHomeomorphism (B.inclusion.map ν'B)).surj
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _)
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _ ?_)
  exact hiso S'rB (asIso ((B.smallPullbackAdjunction ν'B A).counit.app L)).symm
    (hetale qB hqfin hqet K (hpull νB G hG))

include hiso hpull himm hdesc hetale hbc in
/-- **The generic form of Stacks 095R over an affine base.** By Stacks 095K (2) the affine base
`S` is partitioned into finitely many affine constructible locally closed strata `S_i`, each with
a surjective finite locally free `S'_i ⟶ S_i` over which the reduction of the base change of `f`
is split. By Stacks 09YR, 095Q and 0959 it suffices that the direct image along the base change
`T ×_S S'_i ⟶ S'_i` preserves `P`, which is `prop_smallPushforward_of_split_reduction`. -/
theorem prop_smallPushforward_of_isAffine {T S : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] (hfp : FinitePresentation (B.inclusion.map f))
    [IsAffine (B.inclusion.obj S)] (F : Sheaf (SmallEtale.topology B T.1 T.property) A)
    (hF : P T F) : P S ((B.smallPushforward f A).obj F) := by
  classical
  have : IsAffine (B.inclusion.obj T) := isAffine_of_isAffineHom (B.inclusion.map f)
  obtain ⟨n, Si, s, hS, -, hcover, hsplit⟩ :=
    exists_finite_affine_stratification_split_reduction (B.inclusion.map f) hfp
  have : ∀ i, IsAffine (Si i) := fun i => (hS i).1
  have : ∀ i, IsImmersion (s i) := fun i => (hS i).2.1
  have hSi : ∀ i, B.Contains (Si i) := fun i =>
    Scheme.size_lt_of_mono_quasiCompact (s i) S.property
  let SB : Fin n → B.Scheme := fun i => B.obj (Si i) (hSi i)
  let sB : ∀ i, SB i ⟶ S := fun i => ObjectProperty.homMk (s i)
  have : IsAffine S.obj := ‹IsAffine (B.inclusion.obj S)›
  refine himm S (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _ SB sB
    (fun i => (hS i).2.1) (fun i => (hS i).2.2.2) hcover.symm fun i => ?_
  obtain ⟨S', g, hg, hgf, m, q, e, hq, he⟩ := hsplit i
  have : IsFinite g :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      hgf).1
  have : IsAffine S' := isAffine_of_isAffineHom g
  have hS' : B.Contains S' := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g (hSi i)
  let S'B : B.Scheme := B.obj S' hS'
  let gB : S'B ⟶ SB i := ObjectProperty.homMk g
  have : IsAffine (SB i).obj := (hS i).1
  have : IsAffine S'B.obj := ‹IsAffine S'›
  refine hdesc gB hg.surj (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _)
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _ ?_
  refine hiso S'B ((smallEtaleSheafPullbackCompIso B S'B (SB i) S gB (sB i) A).app _).symm ?_
  have hT' : B.Contains (pullback (B.inclusion.map f) (g ≫ s i)) :=
    Scheme.size_pullback_lt _ _ T.property hS'
  let T'B : B.Scheme := B.obj _ hT'
  let f'B : T'B ⟶ S'B := ObjectProperty.homMk (pullback.snd (B.inclusion.map f) (g ≫ s i))
  let g'B : T'B ⟶ T := ObjectProperty.homMk (pullback.fst (B.inclusion.map f) (g ≫ s i))
  obtain ⟨φ⟩ := hbc f (gB ≫ sB i) f'B g'B
    (IsPullback.of_hasPullback (B.inclusion.map f) (g ≫ s i)) inferInstance F
  refine hiso S'B φ.symm ?_
  have : IsAffine (B.inclusion.obj S'B) := ‹IsAffine S'›
  have : IsFinite (B.inclusion.map f'B) :=
    inferInstanceAs (IsFinite (pullback.snd (B.inclusion.map f) (g ≫ s i)))
  have : IsAffine (B.inclusion.obj T'B) := isAffine_of_isAffineHom (B.inclusion.map f'B)
  exact prop_smallPushforward_of_split_reduction B A P hiso hpull hdesc hetale f'B q e hq he _
    (hpull g'B F hF)

include hiso hpull hopen himm hdesc hetale hbc in
/-- **The generic form of Stacks 095R.** Let `P` be a property of sheaves on the small étale sites
of a big étale site which is invariant under isomorphism and inverse image, local for open
coverings and for finite coverings of a quasi-compact quasi-separated scheme by immersions with
constructible images, descends along surjections of quasi-compact quasi-separated schemes, and is
preserved by direct image along finite étale morphisms; and suppose the base change of a finite
direct image holds up to isomorphism. Then direct image along every finite morphism of finite
presentation preserves `P`.

By the open covering condition and the base change of a finite direct image along the members of
an affine open covering of the base, it suffices to treat an affine base, which is
`prop_smallPushforward_of_isAffine`. -/
theorem prop_smallPushforward_of_isFinite_of_finitePresentation {T S : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] (hfp : FinitePresentation (B.inclusion.map f))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) A) (hF : P T F) :
    P S ((B.smallPushforward f A).obj F) := by
  have : LocallyOfFinitePresentation (B.inclusion.map f) := hfp.1
  have : QuasiCompact (B.inclusion.map f) := hfp.2.1
  have : QuasiSeparated (B.inclusion.map f) := hfp.2.2
  let 𝒰 := (B.inclusion.obj S).affineOpenCover.openCover
  have hUc : ∀ i, B.Contains (𝒰.X i) := fun i =>
    Scheme.size_lt_of_isOpenImmersion (𝒰.f i) S.property
  let U : 𝒰.I₀ → B.Scheme := fun i => B.obj (𝒰.X i) (hUc i)
  let j : ∀ i, U i ⟶ S := fun i => ObjectProperty.homMk (𝒰.f i)
  refine hopen S _ U j (fun i => 𝒰.map_prop i) 𝒰.iUnion_range.symm fun i => ?_
  have hTi : B.Contains (pullback (B.inclusion.map f) (𝒰.f i)) :=
    Scheme.size_pullback_lt _ _ T.property (hUc i)
  let TB : B.Scheme := B.obj _ hTi
  let fB : TB ⟶ U i := ObjectProperty.homMk (pullback.snd (B.inclusion.map f) (𝒰.f i))
  let gB : TB ⟶ T := ObjectProperty.homMk (pullback.fst (B.inclusion.map f) (𝒰.f i))
  obtain ⟨φ⟩ := hbc f (j i) fB gB
    (IsPullback.of_hasPullback (B.inclusion.map f) (𝒰.f i)) inferInstance F
  refine hiso (U i) φ.symm ?_
  have : IsAffine (B.inclusion.obj (U i)) := Scheme.isAffine_affineCover (B.inclusion.obj S) i
  have : IsFinite (B.inclusion.map fB) :=
    inferInstanceAs (IsFinite (pullback.snd (B.inclusion.map f) (𝒰.f i)))
  have hfpB : FinitePresentation (B.inclusion.map fB) :=
    show FinitePresentation (pullback.snd (B.inclusion.map f) (𝒰.f i)) from
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact prop_smallPushforward_of_isAffine B A P hiso hpull himm hdesc hetale hbc fB hfpB _
    (hpull gB F hF)

end Generic

/-! ### The abelian and module cases of Stacks 095R

The case of sheaves of sets is `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_isFinite`
on the base; the generic statement above gives it as well. -/


section Abelian

/-- Sheafification of presheaves of `ℤ`-modules on the localizations of the bounded small étale
sites, at the universe of the abelian descent of Stacks 095Q (2). -/
local instance hasWeakSheafify_over_moduleCatInt (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
  have := Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
    (SmallEtale.topology B T.obj T.property) V
  inferInstance

/-- **Stacks 095Q (2), in the form consumed by Stacks 095H for abelian sheaves**, discharged by
the library's unconditional descent
`AlgebraicGeometry.isConstructibleAbelianSheaf_pullback_iff_of_surjective`. -/
theorem abelianConstructibilityDescendsAlongSurjective :
    AbelianConstructibilityDescendsAlongSurjective B :=
  fun _ _ f hf hXc hXq hYc hYq G hG =>
    (isConstructibleAbelianSheaf_pullback_iff_of_surjective B f hXc hXq hYc hYq hf G).2 hG

/-- **[Stacks, Tag 095R], abelian sheaves.** Let `f : T ⟶ S` be a finite and finitely presented
morphism of a big étale site. If `ℱ` is a constructible abelian sheaf on `T_étale`, then `f_*ℱ`
is a constructible abelian sheaf on `S_étale`. -/
@[stacks 095R "abelian groups"]
theorem isConstructibleAbelianSheaf_pushforward_of_isFinite_of_finitePresentation {T S : B.Scheme}
    (f : T ⟶ S) [IsFinite (B.inclusion.map f)] (hfp : FinitePresentation (B.inclusion.map f))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj F) :=
  prop_smallPushforward_of_isFinite_of_finitePresentation B AddCommGrpCat.{u + 1}
    (fun X F => IsConstructibleAbelianSheaf B X F)
    (fun X _ _ e h => isConstructibleAbelianSheaf_congr B X e h)
    (fun f F hF => isConstructibleFiniteSheaf_pullback B f F hF)
    (fun X F _ U j hj hcover hlocal => isConstructibleFiniteSheaf_of_openCover B X F U j hj hcover
      hlocal)
    (fun X _ _ F _ T j hj hc hcover hF =>
      isConstructibleFiniteSheaf_of_constructible_immersion_cover B X F T j hj hc hcover hF)
    (fun f hf hXc hXq hYc hYq G hG =>
      (isConstructibleAbelianSheaf_pullback_iff_of_surjective B f hXc hXq hYc hYq hf G).2 hG)
    (fun p _ _ F hF => isConstructibleAbelianSheaf_pushforward B p
      (abelianConstructibilityDescendsAlongSurjective B) F hF)
    (fun f g f' g' sq _ F =>
      nonempty_smallInverseImage_smallPushforward_iso_of_etaleSite B AddCommGrpCat.{u + 1} f g f' g'
        (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map g))
        (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map g'))
        (fun F => by
          have := Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite B f g g' f' sq
          exact ⟨asIso ((Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, 0} (B.inclusion.map f)
            (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') sq.w).app F)⟩) F)
    f hfp F hF

end Abelian

section Modules

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- Limits of size `u` in `ModuleCat.{u + 1} Λ`. -/
local instance moduleCatSucc_hasLimitsOfSize_small : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- Limits of size `(u, u + 1)` in `ModuleCat.{u + 1} Λ`. -/
local instance moduleCatSucc_hasLimitsOfSize_large :
    HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

omit [IsNoetherianRing Λ] in
/-- **Stacks 0959 for sheaves of modules on Mathlib's small étale site**: forgetting the module
structure carries the module base change comparison to the abelian one
(`Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange`), which
is invertible for a finite morphism, and reflects isomorphisms. -/
theorem isIso_etaleModuleBaseChange_app_of_isPullback_of_isFinite {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) [IsFinite f]
    (M : Stacks.EtaleCohomology.EtaleModules.{u, u + 1} Λ X) :
    IsIso ((Stacks.EtaleCohomology.etaleModuleBaseChange Λ f f' g g' sq.w.symm).app M) := by
  have h1 : IsIso (Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, u + 1} f g g' f' sq.w) :=
    Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback f g g' f' sq
  have h2 := Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange
    Λ f f' g g' sq.w M
  have : IsIso ((Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ Y').map
      ((Stacks.EtaleCohomology.etaleModuleBaseChange Λ f f' g g' sq.w.symm).app M)) := by
    have h3 : IsIso ((Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso Λ g).hom.app
        ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u + 1} Λ f).obj M) ≫
      (Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ Y').map
        ((Stacks.EtaleCohomology.etaleModuleBaseChange Λ f f' g g' sq.w.symm).app M)) := by
      rw [h2]
      have : IsIso ((Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, u + 1} f g g' f' sq.w).app
          ((Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X).obj M)) :=
        NatIso.isIso_app_of_isIso _ _
      exact IsIso.comp_isIso' this (Functor.map_isIso _ _)
    exact IsIso.of_isIso_comp_left ((Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso Λ
      g).hom.app ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u + 1} Λ f).obj M)) _
  exact isIso_of_reflects_iso _ (Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ Y')

/-- **[Stacks, Tag 095R], sheaves of modules.** Let `f : T ⟶ S` be a finite and finitely
presented morphism of a big étale site and let `Λ` be a Noetherian ring. If `ℱ` is a
constructible sheaf of `Λ`-modules on `T_étale`, then `f_*ℱ` is a constructible sheaf of
`Λ`-modules on `S_étale`. -/
@[stacks 095R "sheaves of Λ-modules, Λ Noetherian",
  sga "4 IX 2.14" "(i), A-module variant",
  sga "5 I 1.14" "b)"]
theorem isConstructibleModuleSheaf_pushforward_of_isFinite_of_finitePresentation {T S : B.Scheme}
    (f : T ⟶ S) [IsFinite (B.inclusion.map f)] (hfp : FinitePresentation (B.inclusion.map f))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ ((B.smallPushforward f (ModuleCat.{u + 1} Λ)).obj F) :=
  prop_smallPushforward_of_isFinite_of_finitePresentation B (ModuleCat.{u + 1} Λ)
    (fun X F => IsConstructibleModuleSheaf B X Λ F)
    (fun X _ _ e h => isConstructibleModuleSheaf_congr B Λ X e h)
    (fun f F hF => isConstructibleModuleSheaf_pullback B Λ f F hF)
    (fun X F _ U j hj hcover hlocal => isConstructibleModuleSheaf_of_openCover B Λ X F U j hj hcover
      hlocal)
    (fun X _ _ F _ T j hj hc hcover hF =>
      isConstructibleModuleSheaf_of_constructible_immersion_cover B X Λ F T j hj hc hcover hF)
    (fun f hf hXc hXq hYc hYq G hG =>
      isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback B Λ f hYc hYq hXc hXq hf G
        hG)
    (fun p _ _ F hF => isConstructibleModuleSheaf_pushforward B p Λ F hF)
    (fun f g f' g' sq _ F =>
      nonempty_smallInverseImage_smallPushforward_iso_of_etaleSite B (ModuleCat.{u + 1} Λ) f g f' g'
        (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, u + 1} Λ (B.inclusion.map g))
        (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, u + 1} Λ (B.inclusion.map g'))
        (fun F => by
          have := isIso_etaleModuleBaseChange_app_of_isPullback_of_isFinite Λ (B.inclusion.map f)
            (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') sq F
          exact ⟨asIso ((Stacks.EtaleCohomology.etaleModuleBaseChange Λ (B.inclusion.map f)
            (B.inclusion.map f') (B.inclusion.map g) (B.inclusion.map g') sq.w.symm).app F)⟩) F)
    f hfp F hF

end Modules

end AlgebraicGeometry

end
