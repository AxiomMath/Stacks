module

public import StacksFrontier.AlgebraicGeometry.GenericPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingPropertyTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyLiftingSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback

/-!
# Residual gerbes of locally Noetherian algebraic stacks (Stacks 0H22)

Let `𝒳` be a locally Noetherian algebraic stack and `x ∈ |𝒳|`. Stacks 0H22 asserts that the
residual gerbe of `𝒳` at `x` exists. This file proves it, in the form of the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MT (the residual gerbe of Stacks 06MU).

The proof is the source's. Choose a smooth surjective atlas `U₀ ⟶ 𝒳` with `U₀` locally
Noetherian, an affine open `W = Spec R` of `U₀` meeting the preimage `E` of `x`, and a point
`u ∈ E ∩ W` whose closure in `W` meets `E` only in `u`; the ring `R` being Noetherian, the prime
of `u` is taken maximal among those of `E ∩ W`. Let `Z = Spec(R/𝔭_u)` be the reduced closure and
`K` its function field, and let `f : Spec K ⟶ 𝒳` be the field point at `u`. With
`F = Spec K ×_𝒳 U₀`, the self-intersection `Spec K ×_𝒳 Spec K` is `F ×_{U₀} Spec K`; every point
of `F` lies over `x`, so the base change of `Spec K ⟶ U₀` to any scheme chart of `F` meets `Z`
only at its generic point, and is therefore the base change of `Z ⟶ U₀`
(`AlgebraicGeometry.locallyOfFinitePresentation_pullback_fst_of_iso_fractionRing`). Hence the
projection `Spec K ×_𝒳 Spec K ⟶ Spec K` is locally of finite presentation, being the composite of
that base change with the smooth `F ⟶ Spec K` (Stacks 04ZK, 084Q, 03XQ). The residual gerbe is
then the substack of objects lifting locally to `f`, of
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_fieldSpectrum`.

The source obtains the algebraicity of that substack, `[u/R']`, from Stacks 06FI and its
monomorphy into `𝒳` from Stacks 046S and 04ZZ. The library's Stacks 06FI carries Artin's theorem
Stacks 06DC as a hypothesis, so the substack is shown algebraic directly instead, through the
bootstrap theorem Stacks 04S6 and Stacks 05UM, in
`StacksFrontier.AlgebraicGeometry.Stacks.LocallyLiftingSubstack`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_lfp_twoFibreProductSquare_fst_of_fractionRing`:
  the base change of the field point to a represented category over the chart is locally of
  finite presentation.
* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isLocallyNoetherianStack`:
  **Stacks 0H22**.

## References

* [Stacks Project, Tag 0H22](https://stacks.math.columbia.edu/tag/0H22)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of a field point through the generic point of a closed subscheme is
locally of finite presentation.** Let `𝒜` be represented by an algebraic space `F`, let
`s : 𝒜 ⟶ U₀` be a 1-morphism to (the stack of) an object of the site, and let `j : Z ⟶ U₀` be a
morphism of the site whose underlying morphism of schemes is `Spec K ⟶ Spec A ⟶ U₀` for a domain
`A` with fraction field `K` and a morphism `i : Spec A ⟶ U₀` locally of finite presentation.
Suppose every scheme-valued point of `U₀` which factors through `F ⟶ U₀` meets the image of `i`
only in the image of the generic point. Then the first projection of `𝒜 ×_{U₀} Z ⟶ 𝒜` is locally
of finite presentation. -/
theorem hasRelativeProperty_lfp_twoFibreProductSquare_fst_of_fractionRing
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U₀ Z : BigFppfOver B S hS} (s : 𝒜 ⟶ schemeFibredCategory B S hS U₀) (j : Z ⟶ U₀)
    {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (i : Spec (.of A) ⟶ (BigFppfOver.toScheme B S hS).obj U₀) [LocallyOfFinitePresentation i]
    (eZ : (BigFppfOver.toScheme B S hS).obj Z ≅ Spec (.of K))
    (hj : (BigFppfOver.toScheme B S hS).map j =
      eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i)
    (hpts : ∀ (V : BigFppfOver B S hS) (r : V ⟶ U₀) (g : yoneda.obj V ⟶ F),
      g ≫ representingMap B S hS 𝒜 (schemeFibredCategory B S hS U₀) F (yoneda.obj U₀) eF
        (PresheafOfCategories.sliceElementsEquivalenceOver U₀) s = yoneda.map r →
      ∀ (v : (BigFppfOver.toScheme B S hS).obj V) (z : Spec (.of A)),
        ((BigFppfOver.toScheme B S hS).map r).base v = i.base z → z.asIdeal = ⊥) :
    ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (schemeFibredCategoryMap B S hS j)).fst h := by
  let j' := schemeFibredCategoryMap B S hS j
  let Bsq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s j'
  have hj'rep := isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS j
  obtain ⟨P, hP, ⟨eP⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (schemeFibredCategory B S hS U₀) 𝒜 (schemeFibredCategory B S hS Z) s.hom j'.hom hj'rep
    ⟨F, hF, ⟨eF⟩⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS Bsq.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS Z) (schemeFibredCategory B S hS U₀) 𝒜 j' s Bsq
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} s j')
      hj'rep
  refine ⟨hrep, ?_⟩
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U₀
  let eZ' := PresheafOfCategories.sliceElementsEquivalenceOver Z
  refine (hasRelativeProperty_iff_prop_representingMap B S hS _ Bsq.fst hrep P F hP hF eP eF).2 ?_
  set φ := representingMap B S hS Bsq.pt 𝒜 P F eP eF Bsq.fst
  set ψ := representingMap B S hS 𝒜 (schemeFibredCategory B S hS U₀) F (yoneda.obj U₀) eF eU s
  set ρ := representingMap B S hS Bsq.pt (schemeFibredCategory B S hS Z) P (yoneda.obj Z) eP eZ'
    Bsq.snd
  have hsq : IsPullback φ ρ ψ (yoneda.map j) := by
    have : (twoFibreProductStructureFunctor B S hS 𝒜 (schemeFibredCategory B S hS Z)
        (schemeFibredCategory B S hS U₀) s j').IsFibered := Bsq.pt.property.isFibered
    exact representingMap_schemeFibredCategoryMap B S hS j ▸
      isPullback_representingMap_twoFibreProductSquare B S hS 𝒜
        (schemeFibredCategory B S hS Z) (schemeFibredCategory B S hS U₀) F (yoneda.obj Z)
        (yoneda.obj U₀) eF eZ' eU s j' P eP
  have hlfpE : IsEtaleLocalOnSourceAndTarget (@LocallyOfFinitePresentation.{u}) :=
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
  have : MorphismProperty.IsLocalAtTarget (@LocallyOfFinitePresentation.{u})
      Scheme.zariskiPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le (P := @LocallyOfFinitePresentation.{u})
      Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  refine ((Space.holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget B S hS _ hlfpE hP hF φ).out 1 2).2
    fun V g => ?_
  let r : V ⟶ U₀ := Yoneda.fullyFaithful.preimage (g ≫ ψ)
  have hr : yoneda.map r = g ≫ ψ := Yoneda.fullyFaithful.map_preimage _
  have hcomb : IsPullback (pullback.snd φ g) (pullback.fst φ g ≫ ρ) (yoneda.map r)
      (yoneda.map j) :=
    hr ▸ (IsPullback.of_hasPullback φ g).flip.paste_vert hsq
  have hsch := (IsPullback.of_hasPullback r j).map yoneda
  refine holdsOnEveryEtaleChart_of_prop_toScheme_map _ hlfpE B S hS (pullback.fst r j)
    (pullback.snd φ g) (hcomb.isoIsPullback _ _ hsch) (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp]
    exact hcomb.isoIsPullback_hom_fst _ _ hsch
  · have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      comp_preservesLimitsOfShape (Over.forget (B.obj hS)) B.inclusion
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) r j]
    have := locallyOfFinitePresentation_pullback_fst_of_iso_fractionRing i
      ((BigFppfOver.toScheme B S hS).map r) (hpts V r g hr.symm)
      ((BigFppfOver.toScheme B S hS).map j) eZ hj
    infer_instance

/-- **A Noetherian ring has, in every nonempty set of primes, one contained in no other member.**
-/
theorem exists_mem_forall_le_imp_eq {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : Set (PrimeSpectrum R)) (hE : E.Nonempty) :
    ∃ p ∈ E, ∀ q ∈ E, p.asIdeal ≤ q.asIdeal → q = p := by
  obtain ⟨I, ⟨p, hp, rfl⟩, hmax⟩ :=
    (wellFounded_gt (α := Ideal R)).has_min (PrimeSpectrum.asIdeal '' E) (hE.image _)
  exact ⟨p, hp, fun q hq hle =>
    PrimeSpectrum.ext (eq_of_le_of_not_lt hle (hmax _ ⟨q, hq, rfl⟩)).symm⟩


/-- The map on points induced by a morphism of the site is the map on the underlying schemes. -/
private theorem pointsMap_yoneda_map_pointsEquivScheme_symm {V U : BigFppfOver B S hS} (r : V ⟶ U)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    Space.pointsMap B S hS _ (yoneda.map r) ((Space.pointsEquivScheme B S hS V).symm v) =
      (Space.pointsEquivScheme B S hS U).symm ((BigFppfOver.toScheme B S hS).map r v) := by
  rw [Equiv.eq_symm_apply]
  change Space.pointsToScheme B S hS U _ = _
  rw [Space.pointsToScheme_pointsMap_yoneda]
  exact congrArg _ ((Space.pointsEquivScheme B S hS V).apply_symm_apply v)

/-- **Stacks 0H22.** Let `𝒳` be a locally Noetherian algebraic stack. Then the residual gerbe of
`𝒳` at `x` exists for every `x ∈ |𝒳|`: some strictly full subcategory of `𝒳` meets the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MT at `x`.

See the module documentation for the argument. -/
@[stacks 0H22]
theorem exists_isResidualGerbeAt_of_isLocallyNoetherianStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack B S hS 𝒳) (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P := by
  classical
  obtain ⟨U₀, a, ha_surj, ha_smooth, hNoeth⟩ := h𝒳
  let X := (BigFppfOver.toScheme B S hS).obj U₀
  let 𝒱 := schemeFibredCategory B S hS U₀
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U₀
  let sp𝒱 := spacePointMap B S hS (yoneda.obj U₀) 𝒱
    (representingEquivalence B S hS (yoneda.obj U₀) 𝒱 eU).functor
  let E : Set X := {e | AlgebraicStacks.pointsMap B S hS a
    (sp𝒱 ((Space.pointsEquivScheme B S hS U₀).symm e)) = x}
  -- a point of the chart over `x`
  obtain ⟨w₀, hw₀⟩ := ha_surj x
  obtain ⟨s₀, hs₀⟩ := (bijective_spacePointMap_representing B S hS (yoneda.obj U₀) 𝒱 eU).2 w₀
  let e₀ := Space.pointsEquivScheme B S hS U₀ s₀
  have he₀ : e₀ ∈ E := by
    change AlgebraicStacks.pointsMap B S hS a (sp𝒱 _) = x
    rw [Equiv.symm_apply_apply]
    exact (congrArg _ hs₀).trans hw₀
  -- an affine open neighbourhood, Noetherian
  obtain ⟨W, hW, he₀W, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := e₀)
    (U := ⊤) (Set.mem_univ e₀)
  let R := Γ(X, W)
  have : IsNoetherianRing R := hNoeth.component_noetherian ⟨W, hW⟩
  let E' : Set (PrimeSpectrum R) := {q | hW.fromSpec.base q ∈ E}
  have hE' : E'.Nonempty := ⟨hW.primeIdealOf ⟨e₀, he₀W⟩, by
    change hW.fromSpec.base _ ∈ E
    rwa [hW.fromSpec_primeIdealOf]⟩
  obtain ⟨p, hpE, hpmin⟩ := exists_mem_forall_le_imp_eq E' hE'
  -- the closure of the chosen point, and its generic point
  let A := R ⧸ p.asIdeal
  let K := FractionRing A
  let πA : Spec (.of A) ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  let i : Spec (.of A) ⟶ X := πA ≫ hW.fromSpec
  have : LocallyOfFinitePresentation πA :=
    (LocallyOfFinitePresentation.SpecMap_iff _).2
      (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective (by
        change (RingHom.ker (Ideal.Quotient.mk p.asIdeal)).FG
        rw [Ideal.mk_ker]
        exact IsNoetherian.noetherian _))
  let g : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
  -- the minimality of `p`, read on `Spec A`
  have hmin : ∀ z : Spec (.of A), i.base z ∈ E → z.asIdeal = ⊥ := by
    intro z hz
    have hq := hpmin (PrimeSpectrum.comap (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal)).hom z)
      hz (Ideal.mk_ker.ge.trans (Ideal.comap_mono bot_le))
    refine (Submodule.eq_bot_iff _).2 fun b hb => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq_zero_iff_mem.2 (congrArg PrimeSpectrum.asIdeal hq ▸ hb)
  -- the field point `Spec K ⟶ X` as a morphism of the site
  have : IsPreimmersion g := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  have : AlgebraicGeometry.IsClosedImmersion πA :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hK : B.Contains (Spec (.of K)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (g ≫ πA))
      (Scheme.size_lt_of_isOpenImmersion hW.fromSpec U₀.left.2)
  let φK : Spec (.of K) ⟶ X := g ≫ i
  let jl : B.obj hK ⟶ U₀.left := B.inclusion.preimage φK
  let Fb : BigFppfOver B S hS := Over.mk (jl ≫ U₀.hom)
  let jsite : Fb ⟶ U₀ := Over.homMk jl rfl
  have hjs' : (BigFppfOver.toScheme B S hS).map jsite = g ≫ i :=
    Functor.map_preimage B.inclusion (X := B.obj hK) (Y := U₀.left) φK
  let F : FieldSpectrum B S hS := ⟨K, Fb, Iso.refl _⟩
  have hjs : (BigFppfOver.toScheme B S hS).map jsite = F.isSpec.hom ≫ g ≫ i :=
    hjs'.trans (Category.id_comp _).symm
  let j' : schemeFibredCategory B S hS F.base ⟶ schemeFibredCategory B S hS U₀ :=
    schemeFibredCategoryMap B S hS jsite
  let f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom j' ≫ a
  let 𝒰 := schemeFibredCategory B S hS F.base
  have h𝒰 := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base
  have ha_rep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U₀) a.hom
  have hf_rep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒰 f.hom
  -- the base change of the chart along the field point
  let A₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom a.hom
  have hA₁ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    f.hom a.hom
  obtain ⟨Fsp, hFsp, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    𝒰 𝒱 f.hom.hom a.hom.hom ha_rep h𝒰
  let ψ := representingMap B S hS A₁.pt 𝒱 Fsp (yoneda.obj U₀) eF eU A₁.snd
  -- every point of the field point lies over `x`
  let eU' := PresheafOfCategories.sliceElementsEquivalenceOver F.base
  let pt : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have hpt : πA.base (g.base pt) = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk p.asIdeal) (Ideal.comap (algebraMap A K) ⊥) = p.asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K), ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
  have hmemE : (BigFppfOver.toScheme B S hS).map jsite pt ∈ E := by
    rw [hjs']
    change hW.fromSpec.base (πA.base (g.base pt)) ∈ E
    rwa [hpt]
  let s_q := (Space.pointsEquivScheme B S hS F.base).symm pt
  let q₀ := spacePointMap B S hS (yoneda.obj F.base) 𝒰
    (representingEquivalence B S hS (yoneda.obj F.base) 𝒰 eU').functor s_q
  have hfx : ∀ q, AlgebraicStacks.pointsMap B S hS f q = x := by
    intro q
    have h1 := pointsMap_yoneda_map_pointsEquivScheme_symm B S hS jsite pt
    rw [(subsingleton_points_fieldSpectrumStack.{u, w} B S hS F).elim q q₀,
      AlgebraicStacks.pointsMap_comp]
    change AlgebraicStacks.pointsMap B S hS a (Stack.pointsMap B S hS 𝒰.val 𝒰.property 𝒱.property
      j'.hom q₀) = x
    rwa [← spacePointMap_representing_naturality B S hS (yoneda.obj F.base) (yoneda.obj U₀) 𝒰 𝒱
      eU' eU j' s_q, representingMap_schemeFibredCategoryMap, h1]
  -- every point of the base change of the chart lies over `x`
  have hFpts : ∀ t : Space.points B S hS Fsp, AlgebraicStacks.pointsMap B S hS a
      (sp𝒱 (Space.pointsMap B S hS Fsp ψ t)) = x := by
    intro t
    rw [show sp𝒱 (Space.pointsMap B S hS Fsp ψ t) = _ from
      spacePointMap_representing_naturality B S hS Fsp (yoneda.obj U₀) A₁.pt 𝒱 eF eU A₁.snd t]
    change Stack.pointsMap B S hS 𝒱.val 𝒱.property 𝒳.val.property a.hom.hom
      (Stack.pointsMap B S hS A₁.pt.val A₁.pt.property 𝒱.property A₁.snd.hom _) = x
    rw [Stack.pointsMap_comp B S hS A₁.pt.val A₁.pt.property 𝒱.property 𝒳.val.property
        A₁.snd.hom a.hom.hom,
      ← pointsMap_eq_of_basedNatTrans B S hS A₁.pt.val A₁.pt.property 𝒳.val.property
        (F := BasedFunctor.comp A₁.fst.hom f.hom.hom) (G := BasedFunctor.comp A₁.snd.hom a.hom.hom)
        A₁.iso.hom.hom,
      ← Stack.pointsMap_comp B S hS A₁.pt.val A₁.pt.property 𝒰.property 𝒳.val.property
        A₁.fst.hom f.hom.hom]
    exact hfx _
  have hpts : ∀ (V : BigFppfOver B S hS) (r : V ⟶ U₀) (gV : yoneda.obj V ⟶ Fsp),
      gV ≫ ψ = yoneda.map r → ∀ (v : (BigFppfOver.toScheme B S hS).obj V) (z : Spec (.of A)),
        ((BigFppfOver.toScheme B S hS).map r).base v = i.base z → z.asIdeal = ⊥ := by
    intro V r gV hgr v z hvz
    apply hmin z
    rw [← hvz]
    change AlgebraicStacks.pointsMap B S hS a (sp𝒱 ((Space.pointsEquivScheme B S hS U₀).symm
      ((BigFppfOver.toScheme B S hS).map r v))) = x
    let z₀ := (Space.pointsEquivScheme B S hS V).symm v
    have h2 : Space.pointsMap B S hS Fsp ψ (Space.pointsMap B S hS _ gV z₀) =
        Space.pointsMap B S hS _ (yoneda.map r) z₀ := by
      rw [← hgr, Space.pointsMap_comp]
      rfl
    have h1 : (Space.pointsEquivScheme B S hS U₀).symm ((BigFppfOver.toScheme B S hS).map r v) =
        Space.pointsMap B S hS Fsp ψ (Space.pointsMap B S hS _ gV z₀) := by
      rw [h2]
      exact (pointsMap_yoneda_map_pointsEquivScheme_symm B S hS r v).symm
    rw [h1]
    exact hFpts _
  -- the projection of the self-intersection of the field point is locally of finite presentation
  let lfpP : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
      Space.IsLocallyOfFinitePresentation B S hS k.hom
  obtain ⟨hBrep, hBlfp⟩ := hasRelativeProperty_lfp_twoFibreProductSquare_fst_of_fractionRing B S hS
    Fsp hFsp eF A₁.snd jsite i F.isSpec hjs hpts
  let Bsq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} A₁.snd j'
  have hBsq := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    A₁.snd j'
  have ha_lfpRel : HasRelativeProperty.{u, u, u + 1, u} B S hS lfpP a.hom ha_rep :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) a.hom ha_rep
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        (schemeStack.{u, w} B S hS U₀).property 𝒳.property a.hom).1
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a ha_smooth))
  have hArep : IsRepresentableByAlgebraicSpaces B S hS A₁.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒱 𝒳.val 𝒰 a.hom f.hom A₁ hA₁
      ha_rep
  have hAlfp : HasRelativeProperty.{u, u, u + 1, u} B S hS lfpP A₁.fst hArep :=
    hasRelativeProperty_baseChange.{u, u, u, u} B S hS lfpP 𝒱 𝒳.val 𝒰 a.hom f.hom A₁ hA₁ ha_rep
      ha_lfpRel
  have : lfpP.IsStableUnderComposition :=
    GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_isStableUnderComposition B S hS
  have hDlfp := hasRelativeProperty_comp.{u, u, u + 1, u} B S hS lfpP Bsq.fst A₁.fst hBrep hArep
    hBlfp hAlfp
  let D : Bicategory.TwoCommSq f.hom f.hom := A₁.paste Bsq
  have hD : Bicategory.IsTwoFibreProduct D := Bicategory.isTwoFibreProduct_paste hA₁ hBsq
  -- carried to the canonical self-intersection square, which is equivalent to `D`
  let c := Bicategory.twoFibreProductPreHom hD (selfSquare f.hom)
  have hc : c.hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom f.hom) hD c
  have hselfrep : IsRepresentableByAlgebraicSpaces B S hS (selfSquare f.hom).fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒰 𝒳.val 𝒰 f.hom f.hom
      (selfSquare f.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom f.hom) hf_rep
  let α : BasedFunctor.comp c.hom.hom D.fst.hom ≅
      BasedFunctor.comp (selfSquare f.hom).fst.hom (BasedFunctor.id 𝒰.val) :=
    { hom := c.isoFst.inv.hom
      inv := c.isoFst.hom.hom
      hom_inv_id := congrArg (fun t => t.hom) c.isoFst.inv_hom_id
      inv_hom_id := congrArg (fun t => t.hom) c.isoFst.hom_inv_id }
  have : (BasedFunctor.id 𝒰.val).toFunctor.IsEquivalence :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  have hself : HasRelativeProperty.{u, u, u + 1, u} B S hS lfpP (selfSquare f.hom).fst hselfrep :=
    hasRelativeProperty_of_equivalences B S hS lfpP (selfSquare f.hom).fst D.fst c.hom.hom
      (BasedFunctor.id 𝒰.val) α _ hselfrep hDlfp
  -- the residual gerbe at the image of the field point
  obtain ⟨P, hres⟩ := exists_isResidualGerbeAt_of_fieldSpectrum 𝒳 F f ⟨hselfrep, hself⟩ q₀
  exact ⟨P, hfx q₀ ▸ hres⟩


end AlgebraicGeometry.Stack

end
