module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeMergeCoherence
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeOnImage
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback

/-!
# Base change of relative pseudo-coherence

Let `f : X ⟶ S` be locally of finite type, let `E` be an object of `D(𝒪_X)` which is
`m`-pseudo-coherent relative to `S`, and let `g : S' ⟶ S` be a morphism of schemes. Set
`X' = X ×_S S'`. If `S'` and `X` are Tor independent over `S`, then the derived pullback of `E`
to `X'` is `m`-pseudo-coherent relative to `S'`.

## Main definitions

* `AlgebraicGeometry.DerivedBaseChangeIsoOfTorIndependent`: invertibility of the canonical
  derived base change map at a Tor-independent cartesian square whose vertical arrow is a closed
  immersion (the statement of Stacks 0E23).
* `AlgebraicGeometry.Scheme.Hom.ChartTorIndependence`: Tor independence of `X` and `S'` over `S`
  at the affine-space charts.
* `AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`: restriction to an open
  subscheme agrees with derived pullback along the open immersion.
* `AlgebraicGeometry.Scheme.Modules.openRestrictionDerivedPullbackIso`: the two ways of
  restricting a derived pullback around a commutative square of open immersions agree.

## Main results

* `AlgebraicGeometry.derivedBaseChangeIsoOfTorIndependent`: Stacks 0E23.
* `AlgebraicGeometry.exists_isClosedImmersion_baseChange_affineSpace`: a closed immersion of an
  affine open of `X` into affine space over an affine open of `S` base changes to a closed
  immersion of the corresponding affine open of `X'` into affine space over `S'`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_baseChange`: the local
  condition of relative pseudo-coherence is inherited by such a base change once the derived base
  change map is invertible.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts`:
  relative `m`-pseudo-coherence is preserved by the base change, assuming Tor independence at
  the charts.

## Implementation notes

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 37.59.15 (09UR)](https://stacks.math.columbia.edu/tag/09UR)
* [The Stacks Project, Definition 37.59.2 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 37.59.4 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Remark 20.28.3 (08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [The Stacks Project, Lemma 20.47.3 (09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [The Stacks Project, Lemma 36.22.9 (0E23)](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction to an open subscheme as a derived pullback -/

namespace Scheme.Modules

/-- Restriction to an open subscheme is isomorphic to the derived pullback along the open
immersion. -/
public def derivedRestrictIsoDerivedPullback {W Z : Scheme.{u}} (j : W ⟶ Z)
    [IsOpenImmersion j] :
    (restrictFunctor j).mapDerivedCategory ≅ derivedPullback j.toLRSHom.toShHom := by
  letI : (pullback j).Additive := Functor.additive_of_iso (restrictFunctorIsoPullback j)
  letI : PreservesFiniteLimits (pullback j) :=
    preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback j)
  letI : PreservesFiniteColimits (pullback j) :=
    preservesFiniteColimits_of_natIso (restrictFunctorIsoPullback j)
  letI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) := by
    change PreservesFiniteLimits (pullback j); infer_instance
  letI : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) := by
    change PreservesFiniteColimits (pullback j); infer_instance
  exact Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
      (restrictFunctor j) (pullback j) (restrictFunctorIsoPullback j) ≪≫
    (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso j.toLRSHom.toShHom).symm

/-- For a commutative square `j ≫ p = v ≫ u` of morphisms of schemes with `j` and `u` open
immersions, the restriction along `j` of the derived pullback along `p` is the derived pullback
along `v` of the restriction along `u`. -/
public def openRestrictionDerivedPullbackIso {X' X U W : Scheme.{u}}
    (j : W ⟶ X') (p : X' ⟶ X) (u₀ : U ⟶ X) (v : W ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion u₀] (h : j ≫ p = v ≫ u₀)
    (E : DerivedCategory X.Modules) :
    (restrictFunctor j).mapDerivedCategory.obj
        ((derivedPullback p.toLRSHom.toShHom).obj E) ≅
      (derivedPullback v.toLRSHom.toShHom).obj
        ((restrictFunctor u₀).mapDerivedCategory.obj E) :=
  have hs : j.toLRSHom.toShHom ≫ p.toLRSHom.toShHom =
      v.toLRSHom.toShHom ≫ u₀.toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : W ⟶ X => k.toLRSHom.toShHom) h
  (derivedRestrictIsoDerivedPullback j).app _ ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      j.toLRSHom.toShHom p.toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun k : W.toRingedSpace ⟶ X.toRingedSpace =>
      (derivedPullback k).obj E) hs) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      v.toLRSHom.toShHom u₀.toLRSHom.toShHom).app E).symm ≪≫
    (derivedPullback v.toLRSHom.toShHom).mapIso
      ((derivedRestrictIsoDerivedPullback u₀).app E).symm

end Scheme.Modules

/-! ### Derived base change along a closed immersion, and Tor independence at charts -/

/-- The statement of Stacks 0E23: in a cartesian square of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion and `Z` and `X'` Tor independent over `X`, the canonical derived base
change map `Lf^*(Ri_*K) ⟶ Ri'_*(Lg^*K)` of Stacks 08HY is invertible for every `K` in
`D(𝒪_Z)`. -/
public abbrev DerivedBaseChangeIsoOfTorIndependent : Prop :=
  ∀ {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}
    (sq : IsPullback i' g f i), IsClosedImmersion i → TorIndependent i f →
    ∀ K : DerivedCategory Z.Modules,
      IsIso (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom
        i.toLRSHom.toShHom f.toLRSHom.toShHom
        (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) K)

/-- Stacks 0E23: the canonical derived base change map of Stacks 08HY is invertible on a cartesian
square with `i` a closed immersion and `Z`, `X'` Tor independent over `X`. -/
public theorem derivedBaseChangeIsoOfTorIndependent :
    DerivedBaseChangeIsoOfTorIndependent.{u} := fun sq hi htor K =>
  let := hi
  Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeMap_of_torIndependent
    sq htor K

/-- For every closed immersion `i : U ⟶ 𝔸ⁿ_V` of an affine open `U ⊆ f⁻¹(V)` of `X` into affine
space over an affine open `V` of `S` factoring `f|_U`, and every affine open `V' ⊆ g⁻¹(V)` of `S'`,
the schemes `U` and `𝔸ⁿ_{V'}` are Tor independent over `𝔸ⁿ_V`. -/
public abbrev Scheme.Hom.ChartTorIndependence {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) : Prop :=
  ∀ (V : S.affineOpens) (V' : S'.affineOpens) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (n : ℕ)
    (i : (U.1 : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u}))),
    IsClosedImmersion i →
      i ≫ 𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u}) =
        f.resLE V.1 U.1 hUV →
        TorIndependent i (AffineSpace.map (ULift.{u} (Fin n)) (g.resLE V.1 V'.1 hV'))

/-! ### Base change of a chart -/

/-- Let `U ⊆ f⁻¹(V)` and `V' ⊆ g⁻¹(V)` be opens and let `i : U ⟶ 𝔸ⁿ_V` be a closed immersion over
`V` factoring `f|_U`. The open `W = p_X⁻¹(U) ⊓ p_{S'}⁻¹(V')` of `X ×_S S'` carries a closed
immersion into `𝔸ⁿ_{V'}` over `V'` factoring the second projection restricted to `W`, and the
resulting square over `𝔸ⁿ_V` is cartesian. -/
public theorem exists_isClosedImmersion_baseChange_affineSpace {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {U : X.Opens} {V : S.Opens} {V' : S'.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) (ι : Type u)
    (i : U.toScheme ⟶ 𝔸(ι; V.toScheme)) [IsClosedImmersion i]
    (hif : i ≫ 𝔸(ι; V.toScheme) ↘ V.toScheme = f.resLE V U hUV) :
    ∃ e : (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V' : (pullback f g).Opens).toScheme ⟶
        𝔸(ι; V'.toScheme),
      IsClosedImmersion e ∧
        e ≫ 𝔸(ι; V'.toScheme) ↘ V'.toScheme =
          (pullback.snd f g).resLE V' _ inf_le_right ∧
        IsPullback ((pullback.fst f g).resLE U _ inf_le_left) e i
          (AffineSpace.map ι (g.resLE V V' hV')) := by
  set W : (pullback f g).Opens := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V' with hW
  set wU := (pullback.fst f g).resLE U W inf_le_left with hwU
  set wV := (pullback.snd f g).resLE V' W inf_le_right with hwV
  set q := g.resLE V V' hV' with hq
  set pA := 𝔸(ι; V.toScheme) ↘ V.toScheme with hpA
  have hWpb : IsPullback wU wV (f.resLE V U hUV) q :=
    Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hV' hUV rfl
  have hSpace : IsPullback (AffineSpace.map ι q) (𝔸(ι; V'.toScheme) ↘ V'.toScheme) pA q :=
    AffineSpace.isPullback_map (n := ι) q
  have hpbA : IsPullback (pullback.fst pA q) (pullback.snd pA q) pA q :=
    IsPullback.of_hasPullback pA q
  have hcomm : (wU ≫ i) ≫ pA = wV ≫ q := by rw [Category.assoc, hif]; exact hWpb.w
  set b : W.toScheme ⟶ pullback pA q := hpbA.lift (wU ≫ i) wV hcomm with hb
  have hpbChart : IsPullback wU b i (pullback.fst pA q) := by
    rw [hb]
    exact IsPullback.of_bot' (by simpa only [hif] using hWpb) hpbA
  have hSq : IsPullback wU (b ≫ hSpace.isoPullback.inv) i (AffineSpace.map ι q) := by
    refine hpbChart.of_iso (Iso.refl _) (Iso.refl _) hSpace.isoPullback.symm (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [hSpace.isoPullback_inv_fst]
  refine ⟨b ≫ hSpace.isoPullback.inv,
    MorphismProperty.of_isPullback hSq ‹IsClosedImmersion i›, ?_, hSq⟩
  rw [Category.assoc, hSpace.isoPullback_inv_snd, hb]
  exact hpbA.lift_snd _ _ _

/-! ### Base change of the local condition -/

namespace Scheme.Modules

/-- Let

```
W --e--> P'
|wU       |q
U --i--> P
```

be a commutative square with `i` and `e` closed immersions, and let `F` be an object of `D(𝒪_U)`
whose derived pushforward along `i` is `m`-pseudo-coherent. If the canonical derived base change
map is invertible at `F`, then the derived pushforward along `e` of `Lw_U^*F` is
`m`-pseudo-coherent. -/
public theorem isPseudoCoherentFromAfterPushforward_baseChange {U W P P' : Scheme.{u}}
    (i : U ⟶ P) (e : W ⟶ P') (wU : W ⟶ U) (q : P' ⟶ P)
    [IsClosedImmersion i] [IsClosedImmersion e] (F : DerivedCategory U.Modules) (m : ℤ)
    (hsq : wU.toLRSHom.toShHom ≫ i.toLRSHom.toShHom =
      e.toLRSHom.toShHom ≫ q.toLRSHom.toShHom)
    (hF : IsPseudoCoherentFromAfterPushforward i F m)
    (hBC : IsIso (derivedBaseChangeMap wU.toLRSHom.toShHom e.toLRSHom.toShHom
      i.toLRSHom.toShHom q.toLRSHom.toShHom hsq F)) :
    IsPseudoCoherentFromAfterPushforward e
      ((derivedPullback wU.toLRSHom.toShHom).obj F) m := by
  have h2 : RingedSpace.IsPseudoCoherentFrom (X := P.toRingedSpace)
      ((derivedPushforward i.toLRSHom.toShHom).obj F) m :=
    ((isPseudoCoherentFromAfterPushforward_iff i F m).mp hF).of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app F).symm
  have h3 : RingedSpace.IsPseudoCoherentFrom (X := P'.toRingedSpace)
      ((derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj F)) m :=
    RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
      q.toLRSHom.toShHom ((derivedPushforward i.toLRSHom.toShHom).obj F) m h2
  have eBC : (derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj F) ≅
      (derivedPushforward e.toLRSHom.toShHom).obj
        ((derivedPullback wU.toLRSHom.toShHom).obj F) :=
    asIso (derivedBaseChangeMap _ _ _ _ hsq F)
  exact (isPseudoCoherentFromAfterPushforward_iff e _ m).mpr
    ((h3.of_iso eBC).of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes e).app _))

end Scheme.Modules

/-! ### Base change of relative pseudo-coherence -/

/-- Let `f : X ⟶ S` be locally of finite type, let `E` be an object of `D(𝒪_X)` which is
`m`-pseudo-coherent relative to `S`, and let `g : S' ⟶ S` be a morphism of schemes such that `X`
and `S'` are Tor independent over `S` at the affine-space charts
(`AlgebraicGeometry.Scheme.Hom.ChartTorIndependence`). Then the derived pullback of `E` to
`X ×_S S'` is `m`-pseudo-coherent relative to `S'`. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hchart : f.ChartTorIndependence g) (hE : f.IsPseudoCoherentFrom E m) :
    (pullback.snd f g).IsPseudoCoherentFrom
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj E) m := by
  classical
  refine ⟨Σ V : S.affineOpens, {V' : S'.affineOpens // V'.1 ≤ g ⁻¹ᵁ V.1}, fun a => a.2.1,
    ?_, fun a => ?_⟩
  · refine le_antisymm le_top fun y _ => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := g.base y) (U := (⊤ : S.Opens)) trivial
    obtain ⟨V'₀, hV'₀, hyV'₀, hV'sub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S') (x := y) (U := g ⁻¹ᵁ V₀) hyV₀
    exact Opens.mem_iSup.mpr ⟨⟨⟨V₀, hV₀⟩, ⟨⟨V'₀, hV'₀⟩, hV'sub⟩⟩, hyV'₀⟩
  · set V : S.affineOpens := a.1 with hV
    set V' : S'.affineOpens := a.2.1 with hV'def
    have hV' : V'.1 ≤ g ⁻¹ᵁ V.1 := a.2.2
    have : IsAffine (V.1 : Scheme.{u}) := V.2
    have : IsAffine (V'.1 : Scheme.{u}) := V'.2
    refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1},
      fun p => ⟨pullback.fst f g ⁻¹ᵁ p.1.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1,
        have : IsAffine (p.1.1 : Scheme.{u}) := p.1.2
        isAffineOpen_inf_preimage f g p.2 hV'⟩, ?_, fun p => ?_⟩
    · refine le_antisymm (iSup_le fun p => inf_le_right) fun z hz => ?_
      have hxy : f.base ((pullback.fst f g).base z) = g.base ((pullback.snd f g).base z) := by
        simpa [Scheme.Hom.comp_base] using
          congrArg (fun k : pullback f g ⟶ S => k.base z) (pullback.condition (f := f) (g := g))
      have hfxV : f.base ((pullback.fst f g).base z) ∈ V.1 := hxy ▸ hV' hz
      obtain ⟨U₀, hU₀, hzU₀, hU₀sub⟩ :=
        exists_isAffineOpen_mem_and_subset (X := X) (x := (pullback.fst f g).base z)
          (U := f ⁻¹ᵁ V.1) hfxV
      exact Opens.mem_iSup.mpr ⟨⟨⟨U₀, hU₀⟩, hU₀sub⟩, ⟨hzU₀, hz⟩⟩
    · obtain ⟨n, i, hi, hio, hafter⟩ :=
        Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE p.1 V p.2
      obtain ⟨e, he, hebase, hSq⟩ :=
        exists_isClosedImmersion_baseChange_affineSpace f g p.2 hV' (ULift.{u} (Fin n)) i hio
      have hTorChart := hchart V V' hV' p.1 p.2 n i hi hio
      have hbase := Scheme.Modules.isPseudoCoherentFromAfterPushforward_baseChange i e
        ((pullback.fst f g).resLE p.1.1 _ inf_le_left) (AffineSpace.map (ULift.{u} (Fin n))
          (g.resLE V.1 V'.1 hV')) _ m
        (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback hSq.flip)
        hafter (derivedBaseChangeIsoOfTorIndependent hSq.flip hi hTorChart _)
      refine ⟨inf_le_right, n, e, he, hebase, hbase.of_iso e ?_⟩
      exact (Scheme.Modules.openRestrictionDerivedPullbackIso
        (pullback.fst f g ⁻¹ᵁ p.1.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1 : (pullback f g).Opens).ι
        (pullback.fst f g) p.1.1.ι ((pullback.fst f g).resLE p.1.1 _ inf_le_left)
        (Scheme.Hom.resLE_comp_ι (pullback.fst f g) inf_le_left).symm E).symm

end AlgebraicGeometry

end
