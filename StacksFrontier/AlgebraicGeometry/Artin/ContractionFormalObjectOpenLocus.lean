module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessOfProper
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObject
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicCompletionRigidity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness
public import StacksFrontier.RingTheory.DiscreteValuationRing.CompleteDominating

/-!
# A modification of a complete local base maps its open part into `U'`

In the situation of Stacks 0GH8 let `V = Spec R` with `R` a Noetherian complete local ring, let
`Z ⊆ |V|` be closed and contain the closed point, and let `x̂ : V_{/Z} ⟶ W` be adic. Let
`q : Y ⟶ V` be a proper morphism of algebraic spaces with a section `j_Y` over `V ∖ Z`, and let
`y : Y ⟶ X'` carry `|q|⁻¹ Z` into `T'` with `g ∘ y_{/Z} = x̂ ∘ q_{/Z}`. Then `y ∘ j_Y` lands in
`U' = X' ∖ T'`.

The proof of Stacks 0GI8 uses this silently when it calls the restriction of `x'` to `V ∖ Z` the
component `u'` of the triple. The argument: if a point of `V ∖ Z`, with prime `𝔭`, mapped into
`T'`, take a complete discrete valuation ring `D` with a local map `R ⟶ D` of kernel `𝔭`, lift
`Spec D ⟶ V` to `t : Spec D ⟶ Y` by the valuative criterion for the proper `q`, and observe that
`y ∘ t` has image in `T'` (both points of `Spec D` do). The section `ω = g(y ∘ t)` of `W` over
`Spec D` then restricts on the truncations `Spec(D/𝔪ⁿ⁺¹)` to `x̂` of the truncations of
`Spec D ⟶ V`, and adicness of `x̂` forces `Spec D ⟶ V` to have image in `Z`
(`AlgebraicGeometry.FormalSpace.hasImageIn_of_isAdicMorphism_of_truncations`); but its generic
point is `𝔭 ∉ Z`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_comp_U'_ι_of_isProper`.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
* [Stacks Project, Tag 0A3Y](https://stacks.math.columbia.edu/tag/0A3Y)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace Space

/-- The map on points of a morphism of the site, read through the comparison bijections. -/
private theorem pointsMap_yoneda_map_pointsEquivScheme_symm_aux {T V : BigFppfOver B S hS}
    (f : T ⟶ V) (a : (BigFppfOver.toScheme B S hS).obj T) :
    pointsMap B S hS (yoneda.obj T) (yoneda.map f) ((pointsEquivScheme B S hS T).symm a) =
      (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map f a) := by
  refine (pointsEquivScheme B S hS V).injective ?_
  rw [Equiv.apply_symm_apply]
  refine (pointsToScheme_pointsMap_yoneda B S hS f _).trans ?_
  exact congrArg _ ((pointsEquivScheme B S hS T).apply_symm_apply a)

/-- A morphism of the site has point-set image in `Z` exactly when every point of the source
scheme maps into `Z`, read through the comparison bijection of Stacks 03BV. -/
theorem hasImageIn_yoneda_iff_forall_scheme {T V : BigFppfOver B S hS}
    (Z : Set (points B S hS (yoneda.obj V))) (f : T ⟶ V) :
    HasImageIn B S hS (yoneda.obj V) Z T f ↔
      ∀ a : (BigFppfOver.toScheme B S hS).obj T,
        (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map f a) ∈ Z := by
  have hf : yonedaEquiv.symm f = yoneda.map f :=
    (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map f).symm
  rw [hasImageIn_iff_range_subset, hf]
  constructor
  · intro h a
    rw [← pointsMap_yoneda_map_pointsEquivScheme_symm_aux]
    exact h ⟨_, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (pointsEquivScheme B S hS T).symm.surjective x
    rw [pointsMap_yoneda_map_pointsEquivScheme_symm_aux]
    exact h a

/-- The map on points of a morphism of the site, read through the comparison bijections. -/
theorem pointsMap_yoneda_map_pointsEquivScheme_symm {T V : BigFppfOver B S hS} (f : T ⟶ V)
    (a : (BigFppfOver.toScheme B S hS).obj T) :
    pointsMap B S hS (yoneda.obj T) (yoneda.map f) ((pointsEquivScheme B S hS T).symm a) =
      (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map f a) :=
  pointsMap_yoneda_map_pointsEquivScheme_symm_aux f a

end Space

namespace FormalSpace

/-- The powers of the maximal ideal decrease. -/
theorem maximalIdeal_pow_succ_le (D : Type u) [CommRing D] [IsLocalRing D] (n : ℕ) :
    maximalIdeal D ^ (n + 1 + 1) ≤ maximalIdeal D ^ (n + 1) :=
  Ideal.pow_le_pow_right (Nat.le_add_right _ _)

/-- **Stacks 0AQH on the tower of truncations of a complete local ring in the site.** For a
Noetherian complete local ring `D` with `Spec D` in the site, sections of an algebraic space over
`Spec D` are the compatible families over the truncations `Spec(D/𝔪ⁿ⁺¹)`. -/
theorem existsUnique_section_affineOver_truncations {D : Type u} [CommRing D] [IsLocalRing D]
    (hD : IsNoetherianCompleteLocalRing D) (hc : B.Contains (Spec (.of D)))
    (str : Spec (.of D) ⟶ S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (x : ∀ n, F.obj (op ((BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hc (maximalIdeal D ^ (n + 1))))))
    (hx : ∀ n, F.map ((BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS str hc
      (maximalIdeal_pow_succ_le D n))).op (x (n + 1)) = x n) :
    ∃! y : F.obj (op (affineOver B S hS hc str)), ∀ n,
      F.map (Space.quotientToAffineOver B S hS str hc (maximalIdeal D ^ (n + 1))).op y = x n :=
  existsUnique_section_of_compatible_truncations hD (fun n => maximalIdeal D ^ (n + 1))
    (fun n => Ideal.pow_le_self (Nat.succ_ne_zero n))
    (fun n => maximalIdeal_pow_succ_le D n) (fun n => ⟨n + 1, le_rfl⟩)
    (fun k => ⟨k, Ideal.pow_le_pow_right (Nat.le_succ k)⟩) hF (affineOver B S hS hc str)
    (Iso.refl _) _ (fun _ => Iso.refl _) (fun n => Space.quotientToAffineOver B S hS str hc _)
    (fun n => by simp only [Iso.refl_hom]; rfl)
    (fun n => (BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS str hc
      (maximalIdeal_pow_succ_le D n)))
    (fun n => Space.quotientOverTransition_comp_quotientToAffineOver B S hS _ _ _) x hx

end FormalSpace

namespace Artin.ContractionSituation

variable (c : ContractionSituation B S hS)

/-- **The image-in-`Z` step.** Let `Spec D ⟶ V = Spec R` be given by a local homomorphism
`ρ : R ⟶ D` from a local ring to a Noetherian complete local ring, let `Z` contain the closed
point of `V`, and let `t : Spec D ⟶ Y` lie over `V` along a morphism `q : Y ⟶ V` with
`y ∘ t` of image in `T'`. If `y : Y ⟶ X'` carries `|q|⁻¹ Z` into `T'` with
`g ∘ y_{/Z} = x̂ ∘ q_{/Z}` for an adic `x̂`, then `Spec D ⟶ V` has image in `Z`. -/
theorem hasImageIn_affineOverHom_of_lift {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : B.Contains (Spec (.of R))) (str : Spec (.of R) ⟶ S)
    {Z : Set (Space.points B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)))}
    (hm : (Space.pointsEquivScheme B S hS (FormalSpace.affineOver B S hS hR str)).symm
      (IsLocalRing.closedPoint R : Spec (.of R)) ∈ Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Z ⟶
      c.W) (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : Y ⟶ yoneda.obj (FormalSpace.affineOver B S hS hR str)) (y : Y ⟶ c.X')
    (hT : Space.pointsMap B S hS Y q ⁻¹' Z ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (hformal : Space.completionSheafRestrict B S hS q (Space.pointsMap B S hS Y q ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS y (Space.pointsMap B S hS Y q ⁻¹' Z) c.T' hT ≫ c.g)
    {D : Type u} [CommRing D] [IsLocalRing D] (hDc : IsNoetherianCompleteLocalRing D)
    (ρ : R →+* D) [IsLocalHom ρ] (hD : B.Contains (Spec (.of D)))
    (t : yoneda.obj (FormalSpace.affineOver B S hS hD (Spec.map (CommRingCat.ofHom ρ) ≫ str)) ⟶ Y)
    (ht : t ≫ q = yoneda.map (FormalSpace.affineOverHom B S hS hD
      (Spec.map (CommRingCat.ofHom ρ) ≫ str) (V := FormalSpace.affineOver B S hS hR str)
      (Spec.map (CommRingCat.ofHom ρ)) rfl))
    (hb : Space.HasImageIn B S hS c.X' c.T' _ (yonedaEquiv (t ≫ y))) :
    Space.HasImageIn B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Z _
      (FormalSpace.affineOverHom B S hS hD (Spec.map (CommRingCat.ofHom ρ) ≫ str)
        (V := FormalSpace.affineOver B S hS hR str) (Spec.map (CommRingCat.ofHom ρ)) rfl) := by
  let baseD := Spec.map (CommRingCat.ofHom ρ) ≫ str
  let sp := FormalSpace.affineOverHom B S hS hD baseD
    (V := FormalSpace.affineOver B S hS hR str) (Spec.map (CommRingCat.ofHom ρ)) rfl
  let Wn : ℕ → BigFppfOver B S hS := fun n => (BigAffineFppf.inclusion B S hS).obj
    (FormalSpace.quotientOver B S hS baseD hD (maximalIdeal D ^ (n + 1)))
  let ιn : ∀ n, Wn n ⟶ FormalSpace.affineOver B S hS hD baseD := fun n =>
    Space.quotientToAffineOver B S hS baseD hD _
  let τn : ∀ n, Wn n ⟶ Wn (n + 1) := fun n => (BigAffineFppf.inclusion B S hS).map
    (FormalSpace.quotientOverTransition B S hS baseD hD
      (FormalSpace.maximalIdeal_pow_succ_le D n))
  have hτ : ∀ n, τn n ≫ ιn (n + 1) = ιn n := fun n =>
    Space.quotientOverTransition_comp_quotientToAffineOver B S hS _ _ _
  -- every truncation maps to the closed point
  have hφ : ∀ n, Space.HasImageIn B S hS _ Z (Wn n) (ιn n ≫ sp) := fun n => by
    rw [Space.hasImageIn_yoneda_iff_forall_scheme]
    intro e
    let e' : PrimeSpectrum (D ⧸ maximalIdeal D ^ (n + 1)) := e
    suffices h : PrimeSpectrum.comap ρ (PrimeSpectrum.comap (Ideal.Quotient.mk _) e') =
        IsLocalRing.closedPoint R by
      have h' : (BigFppfOver.toScheme B S hS).map (ιn n ≫ sp) e =
          (IsLocalRing.closedPoint R : Spec (.of R)) := h
      rw [h']
      exact hm
    have hle : maximalIdeal D ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk
        (maximalIdeal D ^ (n + 1))) e').asIdeal := by
      refine (PrimeSpectrum.comap (Ideal.Quotient.mk _) e').isPrime.le_of_pow_le (n := n + 1) ?_
      intro z hz
      show Ideal.Quotient.mk _ z ∈ e'.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hz]
      exact e'.asIdeal.zero_mem
    have hcl : PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal D ^ (n + 1))) e' =
        IsLocalRing.closedPoint D := PrimeSpectrum.ext
      ((IsLocalRing.maximalIdeal.isMaximal D).eq_of_le
        (PrimeSpectrum.comap (Ideal.Quotient.mk _) e').isPrime.ne_top hle).symm
    rw [hcl, IsLocalRing.comap_closedPoint]
  -- the section `ω = g(y ∘ t)` of `W` over `Spec D`
  let ω : c.W.obj.obj (op (FormalSpace.affineOver B S hS hD baseD)) :=
    c.g.hom.app _ (FormalSpace.presheafSection B S hS (F := c.X') (yonedaEquiv (t ≫ y)) hb)
  have hω : ∀ n, xhat.hom.app (op (Wn n)) (FormalSpace.presheafSection B S hS
      (F := yoneda.obj (FormalSpace.affineOver B S hS hR str)) (ιn n ≫ sp) (hφ n)) =
      c.W.obj.map (ιn n).op ω := fun n => by
    let tn : Y.obj (op (Wn n)) := yonedaEquiv (yoneda.map (ιn n) ≫ t)
    have hqtn : q.app _ tn = ιn n ≫ sp := by
      show yonedaEquiv ((yoneda.map (ιn n) ≫ t) ≫ q) = _
      rw [Category.assoc, ht, ← Functor.map_comp, yonedaEquiv_yoneda_map]
    have htn : Space.HasImageIn B S hS Y (Space.pointsMap B S hS Y q ⁻¹' Z) (Wn n) tn :=
      (FormalSpace.hasImageIn_preimage_iff B S hS q Z (Wn n) tn).2 (hqtn ▸ hφ n)
    have hytn : y.app _ tn = c.X'.map (ιn n).op (yonedaEquiv (t ≫ y)) := by
      show yonedaEquiv ((yoneda.map (ιn n) ≫ t) ≫ y) = _
      rw [Category.assoc, yonedaEquiv_naturality]
    have hytn' : Space.HasImageIn B S hS c.X' c.T' (Wn n) (y.app _ tn) :=
      (FormalSpace.hasImageIn_preimage_iff B S hS y c.T' (Wn n) tn).1 fun p => hT (htn p)
    have hf : xhat.hom.app _ ((Space.completionSheafRestrict B S hS q
        (Space.pointsMap B S hS Y q ⁻¹' Z) Z (fun _ hz => hz)).hom.app _
          (FormalSpace.presheafSection B S hS tn htn)) =
        c.g.hom.app _ ((Space.completionSheafRestrict B S hS y
          (Space.pointsMap B S hS Y q ⁻¹' Z) c.T' hT).hom.app _
            (FormalSpace.presheafSection B S hS tn htn)) :=
      congrArg (fun φ => φ.hom.app (op (Wn n)) (FormalSpace.presheafSection B S hS tn htn)) hformal
    have e1 := FormalSpace.completionSheafRestrict_presheafSection B S hS q _ Z (fun _ hz => hz)
      tn htn (hqtn ▸ hφ n)
    have e2 := FormalSpace.completionSheafRestrict_presheafSection B S hS y _ c.T' hT tn htn
      hytn'
    have pc1 := FormalSpace.presheafSection_congr B S hS hqtn (hqtn ▸ hφ n) (hφ n)
    have hbn : Space.HasImageIn B S hS c.X' c.T' (Wn n)
        (c.X'.map (ιn n).op (yonedaEquiv (t ≫ y))) := hytn ▸ hytn'
    have pc2 := FormalSpace.presheafSection_congr B S hS hytn hytn' hbn
    have pm := FormalSpace.presheafSection_map B S hS (ιn n) (yonedaEquiv (t ≫ y)) hb hbn
    exact (congrArg (xhat.hom.app _) (pc1.symm.trans e1.symm)).trans (hf.trans
      ((congrArg (c.g.hom.app _) ((e2.trans pc2).trans pm.symm)).trans
        (c.g.hom.naturality_apply (ιn n).op _)))
  exact FormalSpace.hasImageIn_of_isAdicMorphism_of_truncations xhat hxhat Wn ιn τn hτ
    (fun F hF x hx => FormalSpace.existsUnique_section_affineOver_truncations hDc hD baseD F hF
      x hx) sp hφ ω hω

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A point of `V ∖ Z` is not carried into `T'`.** Let `V = Spec R` for a Noetherian local
ring `R`, let `Z ⊆ |V|` contain the closed point and let `x̂ : V_{/Z} ⟶ W` be adic. Let
`q : Y ⟶ V` be proper with a section `j_Y` over `V ∖ Z`, and let `y : Y ⟶ X'` carry `|q|⁻¹ Z`
into `T'` with `g ∘ y_{/Z} = x̂ ∘ q_{/Z}`. Then `y ∘ j_Y` carries no point of `V ∖ Z` into
`T'`. -/
theorem pointsMap_notMem_T'_of_isProper {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hR : B.Contains (Spec (.of R))) (str : Spec (.of R) ⟶ S)
    {Z : Set (Space.points B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)))}
    (hm : (Space.pointsEquivScheme B S hS (FormalSpace.affineOver B S hS hR str)).symm
      (IsLocalRing.closedPoint R : Spec (.of R)) ∈ Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Z ⟶
      c.W) (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (q : Y ⟶ yoneda.obj (FormalSpace.affineOver B S hS hR str)) (hq : Space.IsProper B S hS q)
    (jY : (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).toFunctor ⟶ Y)
    (hjY : jY ≫ q = (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).ι)
    (y : Y ⟶ c.X')
    (hT : Space.pointsMap B S hS Y q ⁻¹' Z ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (hformal : Space.completionSheafRestrict B S hS q (Space.pointsMap B S hS Y q ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS y (Space.pointsMap B S hS Y q ⁻¹' Z) c.T' hT ≫ c.g)
    (w : Space.points B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).toFunctor) :
    Space.pointsMap B S hS _ (jY ≫ y) w ∉ c.T' := by
  intro hw
  let Vo := FormalSpace.affineOver B S hS hR str
  let O := Space.openSubspaceOfPoints B S hS (yoneda.obj Vo) Zᶜ
  let v := Space.pointsMap B S hS _ O.ι w
  have hv : v ∈ Zᶜ := by
    obtain ⟨p, rfl⟩ := Quot.exists_rep w
    have h1 := Space.range_pointsMap_yonedaEquiv_symm B S hS
      (Space.FieldValuedPoint.map B S hS _ O.ι p)
    exact p.value.2 (h1.symm.subset (Set.mem_singleton _))
  let a : PrimeSpectrum R := Space.pointsEquivScheme B S hS Vo v
  have hva : (Space.pointsEquivScheme B S hS Vo).symm (a : Spec (.of R)) = v :=
    (Space.pointsEquivScheme B S hS Vo).symm_apply_apply v
  have h𝔭 : a.asIdeal ≠ maximalIdeal R := fun h => hv (by
    have ha : a = IsLocalRing.closedPoint R := PrimeSpectrum.ext h
    rw [← hva, ha]
    exact hm)
  obtain ⟨D, _, _, _, ρ, hDc, hρ, hker, hcard⟩ :=
    IsLocalRing.exists_isAdicComplete_isDiscreteValuationRing_ker_eq a.asIdeal h𝔭
  have := hρ
  have hD : B.Contains (Spec (.of D)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of D) hR
      (by rw [Scheme.size_Spec]; exact hcard)
  let K := FractionRing D
  have hK : B.Contains (Spec (.of K)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of K) hR
      (by
        rw [Scheme.size_Spec]
        show Cardinal.mk (FractionRing D) ≤ _
        rw [Cardinal.mk_fractionRing]
        exact hcard)
  let baseD := Spec.map (CommRingCat.ofHom ρ) ≫ str
  let sp : FormalSpace.affineOver B S hS hD baseD ⟶ Vo :=
    FormalSpace.affineOverHom B S hS hD baseD (V := Vo) (Spec.map (CommRingCat.ofHom ρ)) rfl
  let ιK : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D K)) ≫ baseD) ⟶
      FormalSpace.affineOver B S hS hD baseD :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap D K))) :
      B.obj hK ⟶ B.obj hD)
  let gV := ιK ≫ sp
  have hgV : ∀ b, (BigFppfOver.toScheme B S hS).map gV b = (a : Spec (.of R)) := fun b => by
    let b' : PrimeSpectrum K := b
    show PrimeSpectrum.comap ρ (PrimeSpectrum.comap (algebraMap D K) b') = a
    refine PrimeSpectrum.ext ?_
    show Ideal.comap ρ (Ideal.comap (algebraMap D K) b'.asIdeal) = a.asIdeal
    have hb0 : b'.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right b'.isPrime.ne_top
    rw [hb0, Ideal.comap_bot_of_injective _ (IsFractionRing.injective D K), ← hker]
    rfl
  obtain ⟨k, hk⟩ := (Space.exists_factor_openSubspaceOfPoints_iff B S hS Zᶜ (yoneda.map gV)).2
    (by
      rintro _ ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := (Space.pointsEquivScheme B S hS _).symm.surjective x
      rw [Space.pointsMap_yoneda_map_pointsEquivScheme_symm, hgV b, hva]
      exact hv)
  let q₀ : Space.ValuativeSquare q :=
    { R := D
      K := K
      ring_mem := hD
      field_mem := hK
      base := baseD
      generic := k ≫ jY
      special := yoneda.map sp
      comm := by
        rw [Category.assoc, hjY, hk]
        exact yoneda.map_comp ιK sp }
  obtain ⟨L⟩ := ((Space.isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated hY
    (isAlgebraicSpace_yoneda B S hS Vo) q hq.2.1
    (Space.isQuasiSeparated_of_isSeparated B S hS hq.1)).mp hq q₀).1
  let t : yoneda.obj (FormalSpace.affineOver B S hS hD baseD) ⟶ Y := L.map
  have ht1 : yoneda.map ιK ≫ t = k ≫ jY := L.generic_comm
  have ht2 : t ≫ q = yoneda.map sp := L.special_comm
  let ptK : (BigFppfOver.toScheme B S hS).obj
      (siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D K)) ≫ baseD)) :=
    (IsLocalRing.closedPoint K : PrimeSpectrum K)
  let x₀ := (Space.pointsEquivScheme B S hS
    (siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D K)) ≫ baseD))).symm
      ptK
  have hx₀ : Space.pointsMap B S hS _ k x₀ = w := by
    refine Space.pointsMap_injective_of_mono B S hS O.ι ?_
    rw [← Space.pointsMap_comp_apply, hk]
    exact (Space.pointsMap_yoneda_map_pointsEquivScheme_symm gV _).trans
      ((congrArg _ (hgV _)).trans hva)
  have hb : Space.HasImageIn B S hS c.X' c.T' _ (yonedaEquiv (t ≫ y)) := by
    rw [Space.hasImageIn_iff_range_subset, Equiv.symm_apply_apply]
    rintro _ ⟨x, rfl⟩
    obtain ⟨d, rfl⟩ := (Space.pointsEquivScheme B S hS _).symm.surjective x
    let d' : PrimeSpectrum D := d
    by_cases hd : d'.asIdeal = ⊥
    · have hdK : d = (BigFppfOver.toScheme B S hS).map ιK ptK := by
        refine PrimeSpectrum.ext ?_
        show d'.asIdeal = Ideal.comap (algebraMap D K) (maximalIdeal K)
        rw [hd, IsLocalRing.maximalIdeal_eq_bot,
          Ideal.comap_bot_of_injective _ (IsFractionRing.injective D K)]
      have e : (Space.pointsEquivScheme B S hS _).symm d =
          Space.pointsMap B S hS _ (yoneda.map ιK) x₀ := by
        rw [hdK]
        exact (Space.pointsMap_yoneda_map_pointsEquivScheme_symm ιK ptK).symm
      have e' : Space.pointsMap B S hS _ (t ≫ y) (Space.pointsMap B S hS _ (yoneda.map ιK) x₀) =
          Space.pointsMap B S hS _ (jY ≫ y) w := by
        have h1 : yoneda.map ιK ≫ t ≫ y = k ≫ jY ≫ y :=
          (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y) ht1).trans (Category.assoc _ _ _))
        calc Space.pointsMap B S hS _ (t ≫ y) (Space.pointsMap B S hS _ (yoneda.map ιK) x₀)
            = Space.pointsMap B S hS _ (yoneda.map ιK ≫ t ≫ y) x₀ :=
              (Space.pointsMap_comp_apply B S hS _ _ x₀).symm
          _ = Space.pointsMap B S hS _ (k ≫ jY ≫ y) x₀ := by rw [h1]
          _ = Space.pointsMap B S hS _ (jY ≫ y) (Space.pointsMap B S hS _ k x₀) :=
              Space.pointsMap_comp_apply B S hS _ _ x₀
          _ = _ := by rw [hx₀]
      rw [e, e']
      exact hw
    · have hdm : d' = IsLocalRing.closedPoint D :=
        PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (d'.isPrime.isMaximal hd))
      have hz : Space.pointsMap B S hS Y q (Space.pointsMap B S hS _ t
          ((Space.pointsEquivScheme B S hS _).symm d)) ∈ Z := by
        rw [← Space.pointsMap_comp_apply, ht2,
          Space.pointsMap_yoneda_map_pointsEquivScheme_symm sp d]
        show (Space.pointsEquivScheme B S hS Vo).symm (PrimeSpectrum.comap ρ d') ∈ Z
        rw [hdm, IsLocalRing.comap_closedPoint]
        exact hm
      rw [Space.pointsMap_comp_apply]
      exact hT hz
  have hImg := c.hasImageIn_affineOverHom_of_lift hR str hm xhat hxhat q y hT hformal hDc ρ hD
    t ht2 hb
  have h0 := (Space.hasImageIn_yoneda_iff_forall_scheme Z sp).1 hImg
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D)
  have h0a : (BigFppfOver.toScheme B S hS).map sp (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) =
      (a : Spec (.of R)) := by
    show PrimeSpectrum.comap ρ ⟨⊥, Ideal.isPrime_bot⟩ = a
    refine PrimeSpectrum.ext ?_
    show Ideal.comap ρ ⊥ = a.asIdeal
    rw [← hker]
    rfl
  rw [h0a, hva] at h0
  exact hv h0

/-- **The open part of a modification of a complete local base maps into `U'`.** Under the
hypotheses of `AlgebraicGeometry.Artin.ContractionSituation.pointsMap_notMem_T'_of_isProper`,
the composite `y ∘ j_Y : V ∖ Z ⟶ X'` factors through `U' = X' ∖ T'`. -/
theorem exists_comp_U'_ι_of_isProper {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hR : B.Contains (Spec (.of R))) (str : Spec (.of R) ⟶ S)
    {Z : Set (Space.points B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)))}
    (hm : (Space.pointsEquivScheme B S hS (FormalSpace.affineOver B S hS hR str)).symm
      (IsLocalRing.closedPoint R : Spec (.of R)) ∈ Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Z ⟶
      c.W) (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (q : Y ⟶ yoneda.obj (FormalSpace.affineOver B S hS hR str)) (hq : Space.IsProper B S hS q)
    (jY : (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).toFunctor ⟶ Y)
    (hjY : jY ≫ q = (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).ι)
    (y : Y ⟶ c.X')
    (hT : Space.pointsMap B S hS Y q ⁻¹' Z ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (hformal : Space.completionSheafRestrict B S hS q (Space.pointsMap B S hS Y q ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS y (Space.pointsMap B S hS Y q ⁻¹' Z) c.T' hT ≫ c.g) :
    ∃ u : (Space.openSubspaceOfPoints B S hS
        (yoneda.obj (FormalSpace.affineOver B S hS hR str)) Zᶜ).toFunctor ⟶ c.U'.toFunctor,
      jY ≫ y = u ≫ c.U'.ι := by
  have h : ∀ U x, (jY ≫ y).app U x ∈ c.U'.obj U := by
    intro U x
    show Set.range (Space.pointsMap B S hS _ (yonedaEquiv.symm ((jY ≫ y).app U x))) ⊆ c.T'ᶜ
    rw [← yonedaEquiv_symm_naturality_right]
    rintro _ ⟨z, rfl⟩
    rw [Space.pointsMap_comp_apply]
    exact c.pointsMap_notMem_T'_of_isProper hR str hm xhat hxhat hY q hq jY hjY y hT hformal _
  exact ⟨Subfunctor.lift (jY ≫ y) (by rintro U _ ⟨x, rfl⟩; exact h U x),
    (Subfunctor.lift_ι _ _).symm⟩

end Artin.ContractionSituation

end AlgebraicGeometry

end
