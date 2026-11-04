module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgePullback
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeArrow
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseGysinSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamKoszul
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the Gysin map on cohomology, at the source's hypotheses

[Stacks, Tag 0G8D]: for a diagram

```
Z' → X' → S'
↓h   ↓g    ↓t
Z  → X  → S
```

satisfying the assumptions of [Stacks, Tag 0G89], with `X → S`, `X' → S'` smooth and `Z → X`,
`Z' → X'` Koszul regular immersions, the cohomological Gysin maps `γ^{p,q}` of
[Stacks, Tag 0G8A] commute with the pullback maps on cohomology.  The proof is the source's:
"combine Lemma 0G89 and Cohomology, Lemma 0G79".

As in `StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChange` and in the registered
[Stacks, Tag 0G8B], the cohomology of the closed subscheme is read on the ambient scheme as
`H^q(X, i_*Ω^p_{Z/S})`, which is how [Stacks, Tag 0G8A] itself builds `γ^{p,q}`.  Every input of
that file's framework is now constructed rather than assumed:

* the comparisons of [Stacks, Tag 01F8] and [Stacks, Tag 01EZ] behind the pullback maps are
  `CohomologyPullbackComparison.canonical`;
* the vanishing of `ℋ^j_Z(Ω^{p+c}_{X/S})` for `j < c` is
  `Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms`, from
  smoothness and Koszul regularity through [Stacks, Tag 0G7P];
* the Gysin maps are `conormalGysinHom`, the `γ^p` of [Stacks, Tag 0G86];
* the right vertical arrow of [Stacks, Tag 0G89] is `Stacks.Gysin.gysinBaseChangeTargetHom`,
  built from Remark [Stacks, Tag 0G78] and [Stacks, Tag 0G7N];
* the edge compatibility of [Stacks, Tag 0G78] and [Stacks, Tag 0G79] is `gysinEdge_baseChange`,
  proved from `supportedGysinEdge_derivedPushforwardMap`;
* the two vertical maps are the standard pullback maps of [Stacks, Tag 01F9], each with its module
  placed in degree `0`: the Gysin construction places the source in degree `c`, and the passage
  between the two placements is `pullbackHgroup_canonical_eq`, which says the pullback map does
  not depend on the placement degree.

**The one reading kept from the base.** The cohomology of the closed subschemes is read on the
ambient schemes, as `H^q(X, i_*Ω^p_{Z/S})` and `H^q(X', i'_*Ω^p_{Z'/S'})`, exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalBaseChange` and in the registered
[Stacks, Tag 0G8B]; this is how [Stacks, Tag 0G8A] itself forms `γ^{p,q}`
(`H^q(Z, -) = H^q(X, i_*-)`), and the left vertical map is accordingly the pullback along `g`
of the `g`-map `i_*Ω^p_{Z/S} ⟶ g_*i'_*Ω^p_{Z'/S'}` given on sections by pullback of forms along
`h` (`Stacks.Gysin.gysinBaseChangeSourceHom`).

## Main results

* `gysinBaseChangeTargetHom_homEquiv_symm`: the right vertical arrow of 0G89 read through the
  front of the Gysin edge is `H^c` of the derived map of [Stacks, Tag 0G78].
* `gysinEdge_baseChange`: the edge compatibility at the arrows of 0G89.
* `conormalGysinCohomologyMap_pullback_of_sheafSquare`: the cohomology square, from the sheaf
  square of [Stacks, Tag 0G89].

## References

* [Stacks Project, Tag 0G8D](https://stacks.math.columbia.edu/tag/0G8D)
* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
* [Stacks Project, Tag 0G79](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open _root_.DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

open AlgebraicGeometry.Scheme.Hom Stacks.Gysin
open Stacks.AlgebraicGeometry.ConormalEquations Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Transposing `a ≫ φ(b) ≫ G(c)` back along an adjunction. -/
theorem homEquiv_symm_comp_homEquiv_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {A A' : 𝒞} {B B' : 𝒟} (a : A ⟶ A')
    (b : F.obj A' ⟶ B) (c : B ⟶ B') :
    (adj.homEquiv _ _).symm (a ≫ adj.homEquiv _ _ b ≫ G.map c) = F.map a ≫ b ≫ c := by
  rw [Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right,
    Equiv.symm_apply_apply]

variable {Z X S : Scheme.{u}}

/-- `conormalGysinTargetIso` is the identification the front of the Gysin edge induces. -/
theorem conormalGysinTargetIso_inv_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (c p : ℕ) (hvan : AmbientVanishing π (Set.range i.base) (isClosed_range_base i) c p) :
    (conormalGysinTargetIso i π c p).inv =
      supportedGysinEdgeFrontHomology (Set.range i.base) (isClosed_range_base i) (c : ℤ) _
        hvan := by
  rw [supportedGysinEdgeFrontHomology_eq]
  rfl

variable {Z' X' S' : Scheme.{u}}

/-- The right vertical arrow of 0G89, read through the front of the Gysin edge, is `H^c` of the
derived map `θ`. -/
theorem gysinBaseChangeTargetHom_homEquiv_symm (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z)
    (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i']
    (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c)
    (hvan : AmbientVanishing π (Set.range i.base) (isClosed_range_base i) c p)
    (hvan' : AmbientVanishing π' (Set.range i'.base) (isClosed_range_base i') c p) :
    haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
      isQuasicoherent_relativeDifferentialForms_natCast_add π p c
    (modulePullback g.toLRSHom.toShHom).map
        (supportedGysinEdgeFrontHomology (Set.range i.base) (isClosed_range_base i) (c : ℤ) _
          hvan) ≫
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          g.toLRSHom.toShHom _ (c : ℤ) (isLE_supportPush_range_of_conormalRank i hE _)).inv ≫
        (homologyFunctor _ (c : ℤ)).map
          (supportedBaseChangeDerived g.toLRSHom.toShHom (Set.range i.base) (isClosed_range_base i)
            (formsBaseChangeDerived g π π' t right_comm ((p : ℤ) + (c : ℤ)))) ≫
        eqToHom (homology_supportPush_congr (range_base_eq_closedSubsetPreimage i i' h g hcart).symm
          _ (isClosed_range_base i') (c : ℤ) _) =
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _).symm
          (gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE) ≫
        supportedGysinEdgeFrontHomology (Set.range i'.base) (isClosed_range_base i') (c : ℤ) _
          hvan' := by
  rw [← conormalGysinTargetIso_inv_eq i π c p hvan,
    ← conormalGysinTargetIso_inv_eq i' π' c p hvan', gysinBaseChangeTargetHom]
  refine Eq.trans ?_ (congrArg (· ≫ (conormalGysinTargetIso i' π' c p).inv)
    (homEquiv_symm_comp_homEquiv_comp _ _ _ _).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun z => (modulePullback g.toLRSHom.toShHom).map
    (conormalGysinTargetIso i π c p).inv ≫ z) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_
    (congrArg (fun z => gysinBaseChangePull i i' h g π π' t hcart right_comm p hE ≫ z)
      (Iso.hom_inv_id (conormalGysinTargetIso i' π' c p)).symm)
  exact (Category.comp_id _).symm

/-- **The edge compatibility of [Stacks, Tag 0G78] and [Stacks, Tag 0G79] at the arrows of
[Stacks, Tag 0G89]**, in the shape `derivedPushforwardMap_paste` consumes. -/
theorem gysinEdge_baseChange (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
    (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i']
    (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c)
    (hvan : AmbientVanishing π (Set.range i.base) (isClosed_range_base i) c p)
    (hvan' : AmbientVanishing π' (Set.range i'.base) (isClosed_range_base i') c p) :
    (singleFunctor (RModules X.toRingedSpace) (c : ℤ)).map (𝟙 _) ≫
          ambientGysinEdge π (Set.range i.base) (isClosed_range_base i) c p hvan ≫
          derivedPushforwardMap (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
            (formsBaseChangeHom g π π' t right_comm ((p : ℤ) + (c : ℤ)))
        = derivedPushforwardMap (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (c : ℤ)
            (gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE ≫
              (modulePushforward g.toLRSHom.toShHom).map (𝟙 _)) ≫
          (derivedPushforward g.toLRSHom.toShHom).map
            (ambientGysinEdge π' (Set.range i'.base) (isClosed_range_base i') c p hvan') := by
  have : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  refine supportedGysinEdge_derivedPushforwardMap_of_eq g.toLRSHom.toShHom (Set.range i.base)
    (isClosed_range_base i) (Set.range i'.base) (isClosed_range_base i')
    (closedSubsetPreimage g.toLRSHom.toShHom (Set.range i.base))
    (isClosed_closedSubsetPreimage g.toLRSHom.toShHom _ (isClosed_range_base i))
    (range_base_eq_closedSubsetPreimage i i' h g hcart) c _ _ hvan hvan'
    (isLE_supportPush_range_of_conormalRank i hE _) _
    (supportedBaseChangeDerived g.toLRSHom.toShHom (Set.range i.base) (isClosed_range_base i)
      (formsBaseChangeDerived g π π' t right_comm ((p : ℤ) + (c : ℤ)))) ?_ _
    (homology_supportPush_congr (range_base_eq_closedSubsetPreimage i i' h g hcart).symm
      _ (isClosed_range_base i') (c : ℤ) _) ?_
  · refine (supportedBaseChangeDerived_comp_counit g.toLRSHom.toShHom _ _ _).trans ?_
    congr 1
    rw [formsBaseChangeDerived, formsBaseChangeHom]
    exact congrArg₂ (fun a b => a ≫ (singleFunctor _ 0).map b)
      (derivedPullbackSingleObj_eq_derivedToOrdinaryPullbackSingle g.toLRSHom.toShHom _)
      (Equiv.symm_apply_apply _ _).symm
  · exact gysinBaseChangeTargetHom_homEquiv_symm i i' h g π π' t hcart right_comm p hE hvan hvan'

/-- **The cohomology square of [Stacks, Tag 0G8D] from the sheaf square of [Stacks, Tag 0G89].**
Everything except that sheaf square is constructed here or upstream; the vanishing comes from
smoothness and Koszul regularity.  Both vertical maps are the standard pullback maps, with the
module in degree `0`. -/
theorem conormalGysinCohomologyMap_pullback_of_sheafSquare (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z)
    (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    [IsClosedImmersion i'] [LocallyOfFinitePresentation i']
    {c : ℕ} (hE : ConormalRank i c) (hE' : ConormalRank i' c)
    (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t)
    [Smooth π] [Smooth π'] (hkos : IsKoszulRegularImmersion i)
    (hkos' : IsKoszulRegularImmersion i') (p q : ℕ)
    (hsheaf : (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) ≫
        gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE =
      gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ) ≫
        (modulePushforward g.toLRSHom.toShHom).map
          (conormalGysinHom i' π' p hE' ≫ (conormalGysinTargetIso i' π' c p).hom)) :
    gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
          (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
            i π hkos c hE p)
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
          ((q : ℤ) + (c : ℤ)) (q + c) (by omega)
          (formsBaseChangeHom g π π' t right_comm ((p : ℤ) + (c : ℤ)))
      = pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
          (q : ℤ) q (by omega)
          (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ)) ≫
        gysinCohomologyMap (Set.range i'.base) (isClosed_range_base i') c
          (pushforwardRelativeForms i' π' (p : ℤ))
          (relativeDifferentialForms π' ((p : ℤ) + (c : ℤ)))
          (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
            i' π' hkos' c hE' p)
          (conormalGysinHom i' π' p hE' ≫ (conormalGysinTargetIso i' π' c p).hom) q := by
  have hv := Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
    i π hkos c hE p
  have hv' := Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
    i' π' hkos' c hE' p
  have key := cohomologyMapOfSingleHom_pullbackHgroup
    (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) c q
    (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ))
    (formsBaseChangeHom g π π' t right_comm ((p : ℤ) + (c : ℤ))) _ _
    (derivedPushforwardMap_paste (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) c
      (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom)
      (conormalGysinHom i' π' p hE' ≫ (conormalGysinTargetIso i' π' c p).hom) (𝟙 _) (𝟙 _)
      (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ))
      (gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE)
      (formsBaseChangeHom g π π' t right_comm ((p : ℤ) + (c : ℤ)))
      (ambientGysinEdge π (Set.range i.base) (isClosed_range_base i) c p hv)
      (ambientGysinEdge π' (Set.range i'.base) (isClosed_range_base i') c p hv') hsheaf
      (gysinEdge_baseChange i i' h g π π' t hcart right_comm p hE hv hv'))
  simp only at key
  exact key.trans (congrArg (fun z => z ≫ _)
    (pullbackHgroup_canonical_eq g.toLRSHom.toShHom (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega)
      (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ))))

/-- **Stacks Project, Tag 0G8D.** Let `c ≥ 0` and let

```
Z' → X' → S'
↓h   ↓g    ↓t
Z  → X  → S
```

satisfy the assumptions of [Stacks, Tag 0G89]: `Z → X` and `Z' → X'` are closed immersions of
finite presentation whose conormal sheaves are locally free of rank `c`, the left square is
cartesian and `h^*𝒞_{Z/X} → 𝒞_{Z'/X'}` is an isomorphism.  Assume in addition that `X → S`,
`X' → S'` are smooth and `Z → X`, `Z' → X'` are Koszul regular immersions.  Then

```
H^q(Z, Ω^p_{Z/S})  ----γ^{p,q}---→ H^{q+c}(X, Ω^{p+c}_{X/S})
       ↓                                    ↓
H^q(Z', Ω^p_{Z'/S'}) --γ^{p,q}---→ H^{q+c}(X', Ω^{p+c}_{X'/S'})
```

commutes, `γ^{p,q}` being the Gysin map of [Stacks, Tag 0G8A] at the `γ^p` of
[Stacks, Tag 0G86].

The cohomology of the closed subschemes is read on the ambient schemes, `H^q(X, i_*Ω^p_{Z/S})`,
which is how [Stacks, Tag 0G8A] constructs `γ^{p,q}` (and how the registered [Stacks, Tag 0G8B]
reads it); the vertical maps are the pullback maps on cohomology of [Stacks, Tag 01F9] built from
the canonical comparisons `CohomologyPullbackComparison.canonical` of [Stacks, Tag 01F8] and
[Stacks, Tag 01EZ], at the `g`-maps of relative differential forms — on the left the pullback of
forms along `h`, read on `X` (`Stacks.Gysin.gysinBaseChangeSourceHom`), on the right
functoriality of `Ω^{p+c}` (`Stacks.Gysin.formsBaseChangeHom`).  Both are the standard pullback
maps, with the module placed in degree `0`; that the placement degree does not matter is
`pullbackHgroup_canonical_eq`.

Nothing is assumed beyond the source: the vanishing that [Stacks, Tag 0G8A] needs is derived
from smoothness and Koszul regularity by [Stacks, Tag 0G7P]; the sheaf square is
[Stacks, Tag 0G89] (`Stacks.Gysin.conormalGysinHom_comp_gysinBaseChangeTargetHom`, whose
binder `_hconormal` is hypothesis (3) as the source states it); and the compatibility of the
Gysin edge morphisms with pullback, [Stacks, Tag 0G78] and
[Stacks, Tag 0G79], is `gysinEdge_baseChange`. -/
@[stacks 0G8D]
theorem conormalGysinCohomologyMap_pullback (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z)
    (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    [IsClosedImmersion i'] [LocallyOfFinitePresentation i']
    {c : ℕ} (hE : ConormalRank i c) (hE' : ConormalRank i' c)
    (hcart : IsPullback h i' i g) (right_comm : g ≫ π = π' ≫ t)
    (hconormal : IsIso (Stacks.Immersion.immersionConormalSheafMap i' i h g
      (congrArg (fun k => k.toLRSHom.toShHom) hcart.w.symm)))
    [Smooth π] [Smooth π'] (hkos : IsKoszulRegularImmersion i)
    (hkos' : IsKoszulRegularImmersion i') (p q : ℕ) :
    gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
          (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
            i π hkos c hE p)
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
          ((q : ℤ) + (c : ℤ)) (q + c) (by omega)
          (formsBaseChangeHom g π π' t right_comm ((p : ℤ) + (c : ℤ)))
      = pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (0 : ℤ)
          (q : ℤ) q (by omega)
          (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ)) ≫
        gysinCohomologyMap (Set.range i'.base) (isClosed_range_base i') c
          (pushforwardRelativeForms i' π' (p : ℤ))
          (relativeDifferentialForms π' ((p : ℤ) + (c : ℤ)))
          (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
            i' π' hkos' c hE' p)
          (conormalGysinHom i' π' p hE' ≫ (conormalGysinTargetIso i' π' c p).hom) q :=
  conormalGysinCohomologyMap_pullback_of_sheafSquare i i' h g π π' t hE hE' hcart right_comm
    hkos hkos' p q
    (conormalGysinHom_comp_gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE hE'
      hconormal)

end Stacks.DeRham.GysinCohomologyBaseChange

end
