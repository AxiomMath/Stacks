module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective

/-!
# Extending a morphism across a point with valuation local ring

Let `X` and `Y` be schemes over a scheme `S`, and let a morphism from an open subscheme
`U ⊆ X` to `Y` be given. If a point `x` lies in the closure of `U`, the local ring of `X`
at `x` is a valuation ring, `Y` is proper over `S`, and `X` satisfies the stated finiteness
hypothesis, then the morphism extends to an open neighbourhood of `U ∪ {x}`.

## Main results

* `AlgebraicGeometry.exists_open_extension_of_valuationRing_stalk` extends the given morphism
  across `x`.

## Implementation notes

Schemes over `S` are presented by their structure morphisms, so the assertion that a morphism
is over `S` is an equality of composites. A valuation ring in Mathlib is a domain equipped
with the `ValuationRing` class, so the domain and valuation-ring assumptions appear as
typeclass hypotheses. The extension is produced by the valuative criterion for properness,
spread out to an open neighbourhood, and then glued to the given morphism along the
separatedness of `pY`.

## References

* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A scheme that is reduced with finitely many irreducible components, or Noetherian, is
germ-injective at every point. -/
private lemma Scheme.isGermInjectiveAt_of_isReduced_finite_or_isNoetherian {X : Scheme.{u}}
    (hX : (IsReduced X ∧ (irreducibleComponents X).Finite) ∨ IsNoetherian X) (x : X) :
    X.IsGermInjectiveAt x := by
  rcases hX with ⟨hred, hfin⟩ | hnoeth
  · have : X.IsGermInjective :=
      X.isGermInjective_of_isReduced_of_finite_irreducibleComponents hfin
    infer_instance
  · have : IsLocallyNoetherian X := hnoeth.toIsLocallyNoetherian
    infer_instance

/-- The range of a morphism out of the spectrum of a field is its value at the generic point. -/
private lemma range_eq_singleton_genericPoint {K : Type u} [Field K] {Z : Scheme.{u}}
    (q : Spec (.of K) ⟶ Z) : Set.range q = {q (genericPoint (Spec (.of K)))} := by
  ext z
  refine ⟨?_, fun hz => ⟨_, (Set.mem_singleton_iff.mp hz).symm⟩⟩
  rintro ⟨w, rfl⟩
  simp [Subsingleton.elim w (genericPoint (Spec (.of K)))]

/-- A morphism out of the spectrum of a field lands in a set iff its generic point does. -/
private lemma range_subset_iff_genericPoint_mem {K : Type u} [Field K] {Z : Scheme.{u}}
    (q : Spec (.of K) ⟶ Z) {s : Set Z} :
    Set.range q ⊆ s ↔ q (genericPoint (Spec (.of K))) ∈ s := by
  rw [range_eq_singleton_genericPoint, Set.singleton_subset_iff]

/-- A dominant morphism out of the spectrum of a field sends the point to a generic point. -/
private lemma isGenericPoint_of_isDominant {K : Type u} [Field K] {Z : Scheme.{u}}
    (q : Spec (.of K) ⟶ Z) [hq : IsDominant q] :
    IsGenericPoint (q (genericPoint (Spec (.of K)))) Set.univ := by
  rw [isGenericPoint_def, ← range_eq_singleton_genericPoint]
  exact hq.denseRange.closure_range

/-- If the germ map of an affine open `A` at `x` is injective and the stalk at `x` is a domain,
then the fraction field of the stalk maps dominantly to `A`. -/
private lemma isDominant_specMap_algebraMap_comp_fromSpecStalkOfMem {X : Scheme.{u}} {A : X.Opens}
    (hA : IsAffineOpen A) {x : X} (hxA : x ∈ A)
    (hinj : Function.Injective (X.presheaf.germ A x hxA)) [IsDomain (X.presheaf.stalk x)] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ A.fromSpecStalkOfMem x hxA) := by
  let φ : CommRingCat.of Γ(X, A) ⟶ CommRingCat.of (FractionRing (X.presheaf.stalk x)) :=
    CommRingCat.ofHom ((algebraMap _ _).comp (X.presheaf.germ A x hxA).hom)
  have hqSpec : (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ A.fromSpecStalkOfMem x hxA) ≫ A.toSpecΓ =
        Spec.map φ := by
    dsimp [φ]
    rw [Category.assoc, A.fromSpecStalkOfMem_toSpecΓ, ← Spec.map_comp]
  have : IsDominant ((Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ A.fromSpecStalkOfMem x hxA) ≫
        hA.isoSpec.hom) := by
    rw [hA.isoSpec_hom, hqSpec, isDominant_iff]
    change DenseRange (PrimeSpectrum.comap φ.hom)
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot φ.hom).mp fun _ _ hab =>
        hinj (IsFractionRing.injective (X.presheaf.stalk x) _ hab)).le.trans bot_le)
  exact IsDominant.of_comp_of_isOpenImmersion _ hA.isoSpec.hom

/-- A morphism from the fraction field of a valuation-ring stalk to a proper scheme, over `S`,
spreads out to an open neighbourhood of `x` inside a given open `A`. -/
private lemma exists_open_of_valuationRing_stalk {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsProper pY] {x : X} [X.IsGermInjectiveAt x] [IsDomain (X.presheaf.stalk x)]
    [ValuationRing (X.presheaf.stalk x)] {A : X.Opens} (hxA : x ∈ A)
    (i : Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ Y)
    (hi : i ≫ pY = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ X.fromSpecStalk x ≫ pX) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_ : V ≤ A) (g : (V : Scheme.{u}) ⟶ Y),
      g ≫ pY = V.ι ≫ pX ∧ Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x)))) ≫ V.fromSpecStalkOfMem x hxV ≫ g = i := by
  let valSq : ValuativeCommSq pY :=
    { R := X.presheaf.stalk x, domain := ‹IsDomain (X.presheaf.stalk x)›,
      valuationRing := ‹ValuationRing (X.presheaf.stalk x)›,
      K := FractionRing (X.presheaf.stalk x), i₁ := i, i₂ := X.fromSpecStalk x ≫ pX,
      commSq := ⟨hi⟩ }
  have hP : IsProper pY := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hP
  obtain ⟨t, htK, htS⟩ := hP.1.1.1.existence valSq |>.exists_lift
  dsimp [valSq] at t htK htS
  obtain ⟨V₀, hxV₀, g₀, hgStalk₀, hgBase₀⟩ := spread_out_of_isGermInjective' pX pY t htS
  have hxV : x ∈ V₀ ⊓ A := ⟨hxV₀, hxA⟩
  have hrestr : (V₀ ⊓ A).fromSpecStalkOfMem x hxV ≫ X.homOfLE inf_le_left =
      V₀.fromSpecStalkOfMem x hxV₀ := by
    apply (cancel_mono V₀.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨V₀ ⊓ A, hxV, inf_le_right, X.homOfLE inf_le_left ≫ g₀, ?_, ?_⟩
  · rw [Category.assoc, hgBase₀, ← Category.assoc, Scheme.homOfLE_ι]
  · rwa [reassoc_of% hrestr, ← hgStalk₀]

/-- Two morphisms over `S` from opens `U, V` of a reduced open to a separated scheme agree on
the overlap if they agree after a dominant morphism into `V`. -/
private lemma pullback_fst_comp_eq_snd_comp_of_isDominant {S X Y T : Scheme.{u}} (pX : X ⟶ S)
    (pY : Y ⟶ S) [IsSeparated pY] {U V U' : X.Opens} (hU : U ≤ U') (hV : V ≤ U')
    [IsReduced (V : Scheme.{u})] (f : (U : Scheme.{u}) ⟶ Y) (g : (V : Scheme.{u}) ⟶ Y)
    (hf : f ≫ pY = U.ι ≫ pX) (hg : g ≫ pY = V.ι ≫ pX) (q₁ : T ⟶ U) (q₂ : T ⟶ V)
    [IsDominant q₂] (hq : q₁ ≫ X.homOfLE hU = q₂ ≫ X.homOfLE hV) (hfg : q₁ ≫ f = q₂ ≫ g) :
    Limits.pullback.fst (X.homOfLE hU) (X.homOfLE hV) ≫ f =
      Limits.pullback.snd (X.homOfLE hU) (X.homOfLE hV) ≫ g := by
  have : IsDominant (Limits.pullback.lift q₁ q₂ hq ≫
      Limits.pullback.snd (X.homOfLE hU) (X.homOfLE hV)) := by
    rw [Limits.pullback.lift_snd]
    infer_instance
  have : IsDominant (Limits.pullback.lift q₁ q₂ hq) :=
    IsDominant.of_comp_of_isOpenImmersion _ (Limits.pullback.snd (X.homOfLE hU) (X.homOfLE hV))
  have : IsReduced (Limits.pullback (X.homOfLE hU) (X.homOfLE hV)) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd (X.homOfLE hU) (X.homOfLE hV))
  refine ext_of_isDominant_of_isSeparated pY ?_ (Limits.pullback.lift q₁ q₂ hq) ?_
  · simp only [Category.assoc, hf, hg, ← Scheme.homOfLE_ι X hU, ← Scheme.homOfLE_ι X hV]
    rw [← Category.assoc (Limits.pullback.fst _ _) (X.homOfLE hU), Limits.pullback.condition]
    simp only [Category.assoc]
  · simpa only [← Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_snd] using hfg

/-- Morphisms over `S` from opens `U, V` that agree on the overlap glue to `U ⊔ V`. -/
private lemma exists_glue_of_pullback_eq {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    {U V U' : X.Opens} (hU : U ≤ U') (hV : V ≤ U') (hUV : U' ≤ U ⊔ V)
    (f : (U : Scheme.{u}) ⟶ Y) (g : (V : Scheme.{u}) ⟶ Y)
    (hf : f ≫ pY = U.ι ≫ pX) (hg : g ≫ pY = V.ι ≫ pX)
    (hfg : Limits.pullback.fst (X.homOfLE hU) (X.homOfLE hV) ≫ f =
      Limits.pullback.snd (X.homOfLE hU) (X.homOfLE hV) ≫ g) :
    ∃ f' : (U' : Scheme.{u}) ⟶ Y, f' ≫ pY = U'.ι ≫ pX ∧ X.homOfLE hU ≫ f' = f := by
  let W : Bool → X.Opens := fun | true => U | false => V
  obtain rfl : U' = ⨆ b, W b :=
    le_antisymm (hUV.trans (sup_le (le_iSup W true) (le_iSup W false)))
      (iSup_le fun | true => hU | false => hV)
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  have hfgCover : Limits.pullback.fst (𝒰.f true) (𝒰.f false) ≫ f =
      Limits.pullback.snd (𝒰.f true) (𝒰.f false) ≫ g := hfg
  let F : ∀ b, 𝒰.X b ⟶ Y := fun | true => f | false => g
  have hcompat : ∀ b c,
      Limits.pullback.fst (𝒰.f b) (𝒰.f c) ≫ F b =
        Limits.pullback.snd (𝒰.f b) (𝒰.f c) ≫ F c := by
    intro b c
    cases b <;> cases c
    · have : IsOpenImmersion (𝒰.f false) := 𝒰.map_prop false
      simp [F, (cancel_mono (𝒰.f false)).mp Limits.pullback.condition]
    · calc
        Limits.pullback.fst (𝒰.f false) (𝒰.f true) ≫ F false =
            (Limits.pullbackSymmetry (𝒰.f false) (𝒰.f true)).hom ≫
              Limits.pullback.snd (𝒰.f true) (𝒰.f false) ≫ g :=
          (Limits.pullbackSymmetry_hom_comp_snd_assoc
            (𝒰.f false) (𝒰.f true) (h := g)).symm
        _ = (Limits.pullbackSymmetry (𝒰.f false) (𝒰.f true)).hom ≫
              (Limits.pullback.fst (𝒰.f true) (𝒰.f false) ≫ f) := by rw [hfgCover]
        _ = Limits.pullback.snd (𝒰.f false) (𝒰.f true) ≫ F true :=
          Limits.pullbackSymmetry_hom_comp_fst_assoc
            (𝒰.f false) (𝒰.f true) (h := f)
    · exact hfgCover
    · have : IsOpenImmersion (𝒰.f true) := 𝒰.map_prop true
      simp [F, (cancel_mono (𝒰.f true)).mp Limits.pullback.condition]
  have hUbase : 𝒰.f true ≫ (⨆ b, W b).ι = U.ι := Scheme.homOfLE_ι X hU
  have hVbase : 𝒰.f false ≫ (⨆ b, W b).ι = V.ι := Scheme.homOfLE_ι X hV
  refine ⟨𝒰.glueMorphisms F hcompat, 𝒰.hom_ext _ _ fun b => ?_,
    𝒰.ι_glueMorphisms F hcompat true⟩
  cases b
  · rwa [← Category.assoc, 𝒰.ι_glueMorphisms F hcompat false, ← Category.assoc, hVbase]
  · rwa [← Category.assoc, 𝒰.ι_glueMorphisms F hcompat true, ← Category.assoc, hUbase]

/-- **Stacks Project, Tag 0BX7.** A morphism from an open subscheme extends across a point
whose local ring is a valuation ring, provided the target is proper over the base and the
source is either reduced with finitely many irreducible components or Noetherian. -/
@[stacks 0BX7,
  stacks 0BXY "the case of a curve over a field with proper target, where the stalk is a"]
lemma exists_open_extension_of_valuationRing_stalk
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (x : X) (U : X.Opens) (f : (U : Scheme.{u}) ⟶ Y)
    (hf : f ≫ pY = U.ι ≫ pX)
    (hxU : x ∈ closure (U : Set X))
    (hX : (IsReduced X ∧ (irreducibleComponents X).Finite) ∨
      IsNoetherian X)
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)]
    [IsProper pY] :
    ∃ (U' : X.Opens) (hUU' : U ≤ U') (_ : x ∈ U')
      (f' : (U' : Scheme.{u}) ⟶ Y),
      f' ≫ pY = U'.ι ≫ pX ∧ X.homOfLE hUU' ≫ f' = f := by
  have := Scheme.isGermInjectiveAt_of_isReduced_finite_or_isNoetherian hX x
  obtain ⟨A, hxA, hA, hinj⟩ := X.exists_germ_injective x
  let A' : Scheme := A
  have : IsAffine A' := hA
  have : Nonempty A' := ⟨⟨x, hxA⟩⟩
  have : IsDomain Γ(X, A) := hinj.isDomain
  have : IsDomain Γ(A', ⊤) := A.topIso.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have : IsIntegral A' := isIntegral_of_isAffine_of_isDomain A'
  let qK : Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ A' :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ A.fromSpecStalkOfMem x hxA
  have : IsDominant qK := isDominant_specMap_algebraMap_comp_fromSpecStalkOfMem hA hxA hinj
  have hqGen := isGenericPoint_of_isDominant qK
  have hqX : qK ≫ A.ι = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ X.fromSpecStalk x := by
    simp only [qK, Category.assoc, A.fromSpecStalkOfMem_ι]
  have hlift : ∀ W : X.Opens, (∃ z : A, (z : X) ∈ W) →
      ∃ q : Spec (.of (FractionRing (X.presheaf.stalk x))) ⟶ W, q ≫ W.ι = qK ≫ A.ι := by
    rintro W ⟨z, hz⟩
    have hgen : qK (genericPoint _) ∈ A.ι ⁻¹ᵁ W :=
      (hqGen.mem_open_set_iff (A.ι ⁻¹ᵁ W).2).2 ⟨z, Set.mem_univ _, hz⟩
    exact ⟨IsOpenImmersion.lift W.ι (qK ≫ A.ι) ((range_subset_iff_genericPoint_mem _).2
      ⟨⟨A.ι (qK (genericPoint _)), hgen⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨z, hzU, hzA⟩ := (closure_inter_open_nonempty_iff A.2).mp ⟨x, hxU, hxA⟩
  obtain ⟨topU, htopU⟩ := hlift U ⟨⟨z, hzA⟩, hzU⟩
  obtain ⟨V, hxV, hVA, g, hgBase, hgK⟩ := exists_open_of_valuationRing_stalk pX pY hxA
    (topU ≫ f) (by rw [Category.assoc, hf, ← Category.assoc, htopU, hqX, Category.assoc])
  obtain ⟨qV, hqV⟩ := hlift V ⟨⟨x, hxA⟩, hxV⟩
  have hqVmap : qV = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x)))) ≫ V.fromSpecStalkOfMem x hxV := by
    rw [← cancel_mono V.ι, hqV, hqX, Category.assoc, V.fromSpecStalkOfMem_ι]
  have hgeneric : topU ≫ f = qV ≫ g := by
    rw [← hgK, ← Category.assoc, ← hqVmap]
  have : IsDominant (qV ≫ X.homOfLE hVA) := by
    rwa [show qV ≫ X.homOfLE hVA = qK by
      rw [← cancel_mono A.ι, Category.assoc, Scheme.homOfLE_ι, hqV]]
  have : IsDominant qV := IsDominant.of_comp_of_isOpenImmersion qV (X.homOfLE hVA)
  have : IsReduced (V : Scheme) := isReduced_of_isOpenImmersion (X.homOfLE hVA)
  have hmaps : topU ≫ X.homOfLE (le_sup_left : U ≤ U ⊔ V) =
      qV ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V) := by
    rw [← cancel_mono (U ⊔ V).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, htopU, hqV]
  obtain ⟨f', hf'base, hf'⟩ := exists_glue_of_pullback_eq pX pY _ _ le_rfl f g hf hgBase
    (pullback_fst_comp_eq_snd_comp_of_isDominant pX pY _ _ f g hf hgBase topU qV hmaps
      hgeneric)
  exact ⟨U ⊔ V, le_sup_left, (le_sup_right : V ≤ U ⊔ V) hxV, f', hf'base, hf'⟩

end AlgebraicGeometry

end
