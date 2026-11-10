module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionExistenceFamily
public import StacksFrontier.AlgebraicGeometry.Quot.CompletionSubalgebraLimit
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyLimitDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeStageApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletionComparisonEtale

/-!
# Contractions of families of curves over an elementary étale neighbourhood

This file carries the step of the proof of Stacks 0E7C over a Noetherian base whose local ring at
the point is a G-ring: let `R` be a Noetherian ring, `𝔭` a prime with `R_𝔭` a G-ring, `F` a family
of curves over `Spec R` whose fibre over `𝔭` is the scheme `X₀`, and `h₀ : X₀ ⟶ Y₀` a morphism
over `κ(𝔭)` to a proper scheme with `𝒪_{Y₀} ≅ h₀,*𝒪_{X₀}` and `R¹h₀,*𝒪_{X₀} = 0`. Then over an
elementary étale neighbourhood `Spec D ⟶ Spec R` of `𝔭` there are a family of curves `G` and a
morphism from the base change of `F` to `G` whose fibre over the point is `h₀`.

The contraction exists over the completion `R_𝔭^∧`
(`AlgebraicGeometry.CurveFamily.exists_contraction_of_isAdicComplete`); `R_𝔭^∧` is the filtered
colimit of its finitely generated `R`-subalgebras, so the contraction descends to one of them, `E`
(Stacks 0D55, 07SK); and Artin approximation over `R` (Stacks 0CAU, in the form
`StacksDraft.ArtinApproximation.exists_etaleApproximation_mem_maximalIdeal_pow`) maps `E` to an
elementary étale `R`-algebra `D` compatibly with the residue fields, along which the descended
data are pulled back. This replaces, in the source's proof, the passage through the henselization
and the approximation property of henselian G-rings.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_contraction_of_isGRing_localization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- An isomorphism of schemes of the site, read in the site over the integers. -/
def integerSiteIso {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T') (e : T ≅ T') :
    integerSiteObject B hZ hT ≅ integerSiteObject B hZ hT' where
  hom := integerSiteMap B hZ hT hT' e.hom
  inv := integerSiteMap B hZ hT' hT e.inv
  hom_inv_id := by rw [integerSiteMap_comp, e.hom_inv_id, integerSiteMap_id]
  inv_hom_id := by rw [integerSiteMap_comp, e.inv_hom_id, integerSiteMap_id]

/-- Composition of morphisms of schemes of the site, read on representable presheaves. -/
@[reassoc]
theorem yoneda_map_integerSiteMap_comp {T T' T'' : Scheme.{u}} {hT : B.Contains T}
    {hT' : B.Contains T'} {hT'' : B.Contains T''} (f : T ⟶ T') (g : T' ⟶ T'') :
    yoneda.map (integerSiteMap B hZ hT hT' f) ≫ yoneda.map (integerSiteMap B hZ hT' hT'' g) =
      yoneda.map (integerSiteMap B hZ hT hT'' (f ≫ g)) :=
  (yoneda.map_comp _ _).symm.trans (congrArg _ (integerSiteMap_comp f g))

/-- The structure morphism of a family read over its own base, as `toBaseYoneda`. -/
theorem toBaseYonedaOfEq_rfl' (F : CurveFamily B hZ) : F.toBaseYonedaOfEq rfl = F.toBaseYoneda :=
  toBaseYonedaOfEq_rfl F

section Completion

open CompletionSubalgebra

variable (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- The spectra of the residue fields of `Λ` and of its completion, identified. -/
def residueSpecIso : Spec (.of (ResidueField Λ)) ≅ Spec (.of (ResidueField (Completion Λ))) where
  hom := Spec.map (CommRingCat.ofHom (AdicCompletion.residueFieldCompletionEquiv Λ).symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (AdicCompletion.residueFieldCompletionEquiv Λ).toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AdicCompletion.residueFieldCompletionEquiv Λ).symm_apply_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AdicCompletion.residueFieldCompletionEquiv Λ).apply_symm_apply x

end Completion

open StacksDraft.ArtinApproximation in
/-- **The residue field of an elementary étale approximation.** Let `χ : E ⟶ D` approximate a
subalgebra `E ⊆ R_𝔭^∧` modulo the maximal ideal, through an elementary étale `R`-algebra `D` at a
prime `𝔭_D` over `𝔭`. Then the residue map of `D` at `𝔭_D`, composed with `χ`, factors the residue
map of `R_𝔭^∧` restricted to `E` through a homomorphism `κ(𝔭_D) ⟶ κ(R_𝔭^∧)`. -/
theorem exists_residueField_hom_of_etaleApproximation {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] [IsNoetherianRing (Localization.AtPrime p)]
    {D : Type u} [CommRing D] [Algebra R D] [Algebra.Etale R D] (pD : Ideal D) [pD.IsPrime]
    (hpD : p = pD.comap (algebraMap R D))
    (hres : Function.Bijective (Ideal.ResidueField.map p pD (algebraMap R D) hpD))
    {E : Subalgebra R (Completion p)} (χ : E →+* D)
    (hcong : ∀ e : E, completionComparison p pD (algebraMap R D) hpD (e : Completion p) -
      toCompletion pD (χ e) ∈ completionIdeal pD 1) :
    ∃ θ : pD.ResidueField →+* ResidueField (Completion p), ∀ e : E,
      θ (algebraMap D pD.ResidueField (χ e)) = residue (Completion p) (e : Completion p) := by
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing R D
  have : IsNoetherianRing (Localization.AtPrime pD) :=
    IsLocalization.isNoetherianRing pD.primeCompl _ inferInstance
  let Φ := RingEquiv.ofBijective _ (bijective_completionComparison p pD hpD hres)
  have : IsLocalHom Φ.symm.toRingHom := ⟨fun a ha => (isUnit_map_iff Φ.symm a).mp ha⟩
  refine ⟨(ResidueField.map Φ.symm.toRingHom).comp (ResidueField.map (ofLocalization pD)),
    fun e => ?_⟩
  change ResidueField.map Φ.symm.toRingHom (ResidueField.map (ofLocalization pD)
    (residue _ (algebraMap D (Localization.AtPrime pD) (χ e)))) = _
  rw [ResidueField.map_residue, ResidueField.map_residue]
  have he : (e : Completion p) = Φ.symm (Φ e) := (Φ.symm_apply_apply _).symm
  rw [he]
  refine Ideal.Quotient.eq.mpr ?_
  change Φ.symm _ - Φ.symm _ ∈ _
  rw [← Φ.symm.map_sub]
  refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
  have hmem : ofLocalization pD (algebraMap D (Localization.AtPrime pD) (χ e)) - Φ e ∈
      maximalIdeal (Completion pD) := by
    have h1 : _ ∈ Ideal.map (ofLocalization pD) (maximalIdeal (Localization.AtPrime pD) ^ 1) :=
      hcong e
    rw [pow_one, ← AdicCompletion.maximalIdeal_eq_map] at h1
    rw [← neg_sub]
    exact neg_mem h1
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem ((isUnit_map_iff Φ.symm _).mp hu)

section Localization

open CompletionSubalgebra ContractionUniquenessComplete

variable (B hZ) {R : Type u} [CommRing R]
  (p : Ideal R) [p.IsPrime] [IsNoetherianRing (Localization.AtPrime p)]

/-- `Spec R_𝔭^∧ ⟶ Spec R` in the site over the integers, with source the vertex of
`AlgebraicGeometry.CompletionSubalgebra.cone` for `R`-subalgebras. -/
abbrev localCompletionSiteMap (hR : B.Contains (Spec (.of R)))
    (hΛ' : B.Contains (Spec (.of (Completion (Localization.AtPrime p))))) :
    (BigAffineFppf.inclusion B integerBase hZ).obj
        (cone (Completion (Localization.AtPrime p)) R B hZ hΛ').pt ⟶ integerSiteObject B hZ hR :=
  integerSiteMap B hZ hΛ' hR
    (Spec.map (CommRingCat.ofHom (algebraMap R (Completion (Localization.AtPrime p)))))

/-- The closed point of `Spec R_𝔭^∧` in the site over the integers, with target the vertex of
`AlgebraicGeometry.CompletionSubalgebra.cone` for `R`-subalgebras. -/
abbrev localCompletionClosedPoint
    (hκ' : B.Contains (Spec (.of (ResidueField (Completion (Localization.AtPrime p))))))
    (hΛ' : B.Contains (Spec (.of (Completion (Localization.AtPrime p))))) :
    integerSiteObject B hZ hκ' ⟶
      (BigAffineFppf.inclusion B integerBase hZ).obj
        (cone (Completion (Localization.AtPrime p)) R B hZ hΛ').pt :=
  integerSiteMap B hZ hκ' hΛ' (closedPoint (Completion (Localization.AtPrime p)))

/-- `Spec R[s] ⟶ Spec R` in the site over the integers, for an `R`-subalgebra `R[s] ⊆ R_𝔭^∧`, with
source the stage of `AlgebraicGeometry.CompletionSubalgebra.diagram`. -/
abbrev localSubSiteMap (hR : B.Contains (Spec (.of R)))
    (hΛ' : B.Contains (Spec (.of (Completion (Localization.AtPrime p)))))
    (s : (Finset (Completion (Localization.AtPrime p)))ᵒᵖ) :
    (BigAffineFppf.inclusion B integerBase hZ).obj
        ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').obj s) ⟶
      integerSiteObject B hZ hR :=
  integerSiteMap B hZ (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' s.unop) hR
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (sub (Completion (Localization.AtPrime p)) R s.unop))))

end Localization

/-- The cartesian square of the base change of a family along a map to its own base. -/
private theorem isPullback_pullbackHom_yoneda_self (F : CurveFamily B hZ)
    {T : BigFppfOver B integerBase hZ} (g : T ⟶ F.base) :
    IsPullback ((F.ofBaseEq rfl).pullbackHom g).totalMap.hom
      ((F.ofBaseEq rfl).pullback g).toBaseYoneda F.toBaseYoneda (yoneda.map g) := by
  simpa only [toBaseYonedaOfEq_rfl'] using F.isPullback_pullbackHom_yoneda rfl g

open ContractionUniquenessComplete CompletionSubalgebra in
/-- **Stacks 0E7C over an elementary étale neighbourhood of a point with a G-ring as local ring,
for families of curves.** Let `R` be a Noetherian ring, `𝔭 ⊂ R` a prime with `R_𝔭` a G-ring, and
`F` a family of curves over `Spec R` whose fibre over `𝔭` is the scheme `X₀` (the cartesian
square `ι` over `Spec κ(𝔭) ⟶ Spec R`). Let `h₀ : X₀ ⟶ Y₀` be a morphism over `κ(𝔭)` to a proper
scheme with `𝒪_{Y₀} ≅ h₀,*𝒪_{X₀}` and `R¹h₀,*𝒪_{X₀} = 0`. Then there are an étale `R`-algebra `D`
with a prime `𝔭_D` over `𝔭` and the same residue field (an elementary étale neighbourhood of
`𝔭`), a point `t : Spec κ(𝔭) ⟶ Spec D` of `Spec D` at `𝔭_D` over `Spec κ(𝔭) ⟶ Spec R`, a family of
curves `G` over `Spec D`, and a morphism `h` from the total space of the base change `F_D` of `F`
to that of `G` over `Spec D`, such that the fibres of `F_D` and `G` over `t` are `X₀` and `Y₀`
and `h` restricts to `h₀` on them. -/
theorem exists_contraction_of_isGRing_localization
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hGR : IsGRing (Localization.AtPrime p))
    (hR : B.Contains (Spec (.of R))) (hκ : B.Contains (Spec (.of p.ResidueField)))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hR)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of p.ResidueField))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ hκ hR
        (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))))))
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of p.ResidueField))
    [IsProper pY₀] (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra.Etale R D) (pD : Ideal D)
      (_ : pD.IsPrime) (hpD : p = pD.comap (algebraMap R D)),
      Function.Bijective (Ideal.ResidueField.map p pD (algebraMap R D) hpD) ∧
      ∃ (hD : B.Contains (Spec (.of D))) (θ : pD.ResidueField →+* p.ResidueField),
        (Spec.map (CommRingCat.ofHom θ) ≫
            Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R D)) =
            Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)) ∧
        ∃ (G : CurveFamily B hZ) (hG : G.base = integerSiteObject B hZ hD)
          (h : ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hD hR
            (Spec.map (CommRingCat.ofHom (algebraMap R D))))).total.obj ⟶ G.total.obj),
          h ≫ G.toBaseYonedaOfEq hG = ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hD hR
            (Spec.map (CommRingCat.ofHom (algebraMap R D))))).toBaseYoneda ∧
          ∃ ιD : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ ((F.ofBaseEq hF).pullback
              (integerSiteMap B hZ hD hR
                (Spec.map (CommRingCat.ofHom (algebraMap R D))))).total.obj,
            ιD ≫ ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hD hR
              (Spec.map (CommRingCat.ofHom (algebraMap R D))))).totalMap.hom = ι ∧
            IsPullback ιD (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀))
              ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hD hR
                (Spec.map (CommRingCat.ofHom (algebraMap R D))))).toBaseYoneda
              (yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
                Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))))) ∧
            ∃ j : yoneda.obj (integerSiteObject B hZ hY₀) ⟶ G.total.obj,
              IsPullback j (yoneda.map (integerSiteMap B hZ hY₀ hκ pY₀)) (G.toBaseYonedaOfEq hG)
                (yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))))) ∧
              ιD ≫ h = yoneda.map (integerSiteMap B hZ hX₀ hY₀ h₀) ≫ j := by
  classical
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have := isNoetherianRing_adicCompletion (Localization.AtPrime p)
  -- the local ring, its completion and their residue fields
  have hΛ : B.Contains (Spec (.of (Localization.AtPrime p))) :=
    BigFppfSite.contains_spec_of_mk_lt_cutoff B
      ((Cardinal.mk_le_of_isLocalization p.primeCompl (Localization.AtPrime p)).trans_lt
        (max_lt B.aleph0_lt_cutoff (BigFppfSite.mk_lt_cutoff_of_contains_spec B hR)))
  have hΛ' : B.Contains (Spec (.of (Completion (Localization.AtPrime p)))) :=
    BigFppfSite.contains_spec_adicCompletion B hΛ _
  have hκ' : B.Contains (Spec (.of (ResidueField (Completion (Localization.AtPrime p))))) := by
    refine BigFppfSite.contains_spec_of_mk_lt_cutoff B ?_
    calc Cardinal.mk (ResidueField (Completion (Localization.AtPrime p))) =
          Cardinal.mk p.ResidueField :=
          (Cardinal.mk_congr
            (AdicCompletion.residueFieldCompletionEquiv (Localization.AtPrime p)).toEquiv).symm
      _ < B.cutoff := BigFppfSite.mk_lt_cutoff_of_contains_spec B hκ
  let Ψ := yoneda.mapIso
    (integerSiteIso (hZ := hZ) hκ hκ' (residueSpecIso (Localization.AtPrime p)))
  have hΨ : Ψ.hom = yoneda.map
      (integerSiteMap B hZ hκ hκ' (residueSpecIso (Localization.AtPrime p)).hom) := rfl
  have hΨ' : Ψ.inv = yoneda.map
      (integerSiteMap B hZ hκ' hκ (residueSpecIso (Localization.AtPrime p)).inv) := rfl
  have hiso : ∀ {P X Y Y' Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {fst : P ⟶ X}
      {snd : P ⟶ Y'} {f : X ⟶ Z} {g : Y' ⟶ Z}, IsPullback fst snd f g → ∀ e : Y ≅ Y',
        IsPullback fst (snd ≫ e.inv) f (e.hom ≫ g) := fun h e =>
    h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  -- the closed point of the completion lies over the point `𝔭`
  have K1 : (residueSpecIso (Localization.AtPrime p)).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)) =
        closedPoint (Completion (Localization.AtPrime p)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Completion (Localization.AtPrime p)))) := by
    change Spec.map (CommRingCat.ofHom
      (AdicCompletion.residueFieldCompletionEquiv (Localization.AtPrime p)).toRingHom) ≫ _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  -- the family over the completion and its closed fibre
  let F' := (F.ofBaseEq hF).pullback (localCompletionSiteMap B hZ p hR hΛ')
  have hF' : F'.base = integerSiteObject B hZ hΛ' := rfl
  have eF' : F'.toBaseYonedaOfEq hF' = F'.toBaseYoneda := toBaseYonedaOfEq_rfl' F'
  have sqF' := F.isPullback_pullbackHom_yoneda hF (localCompletionSiteMap B hZ p hR hΛ')
  have hι2 : IsPullback ι
      (yoneda.map (integerSiteMap B hZ hX₀ hκ'
        (pX₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)))
      (F.toBaseYonedaOfEq hF)
      (yoneda.map (localCompletionClosedPoint B hZ p hκ' hΛ') ≫
        yoneda.map (localCompletionSiteMap B hZ p hR hΛ')) :=
    IsPullback.of_eq (hiso hι Ψ.symm) rfl (yoneda_map_integerSiteMap_comp _ _) rfl
      ((yoneda_map_integerSiteMap_comp _ _).trans
        ((congrArg (fun f => yoneda.map (integerSiteMap B hZ hκ' hR f)) K1).trans
          (yoneda_map_integerSiteMap_comp _ _).symm))
  obtain ⟨ι', hι'e, hι'0⟩ : ∃ ι' : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F'.total.obj,
      ι' ≫ ((F.ofBaseEq hF).pullbackHom (localCompletionSiteMap B hZ p hR hΛ')).totalMap.hom =
        ι ∧
        IsPullback ι' (yoneda.map (integerSiteMap B hZ hX₀ hκ'
            (pX₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)))
          F'.toBaseYoneda (yoneda.map (localCompletionClosedPoint B hZ p hκ' hΛ')) :=
    ⟨_, sqF'.lift_fst _ _ _, IsPullback.of_right' hι2 sqF'⟩
  have hι' : IsPullback ι'
      (yoneda.map (integerSiteMap B hZ hX₀ hκ'
        (pX₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)))
      (F'.toBaseYonedaOfEq hF')
      (yoneda.map (integerSiteMap B hZ hκ' hΛ'
        (closedPoint (Completion (Localization.AtPrime p))))) := by
    rwa [eF']
  -- the contraction over the completion
  obtain ⟨G', hG', h', hh', j', hj', hιh'⟩ := exists_contraction_of_isAdicComplete hΛ' hκ'
    F' hF' hX₀ (pX₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom) ι' hι' hY₀
    (pY₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom) h₀
    (by rw [← Category.assoc, hh₀]) h0 hR1
  have hGc : G'.base = (BigAffineFppf.inclusion B integerBase hZ).obj
      (cone (Completion (Localization.AtPrime p)) R B hZ hΛ').pt := hG'
  have hh'' : h' ≫ G'.toBaseYonedaOfEq hGc = F'.toBaseYoneda := hh'.trans eF'
  have hj'' : IsPullback j'
      (yoneda.map (integerSiteMap B hZ hY₀ hκ'
        (pY₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)))
      (G'.toBaseYonedaOfEq hGc) (yoneda.map (localCompletionClosedPoint B hZ p hκ' hΛ')) := hj'
  -- descent of the contraction to a finitely generated `R`-subalgebra of the completion
  obtain ⟨i, Gi, hGi, δ, hδ⟩ := exists_hom_to_stage_of_isLimit
    (cone (Completion (Localization.AtPrime p)) R B hZ hΛ')
    (isLimit (Completion (Localization.AtPrime p)) R B hZ hΛ') G' hGc
  obtain ⟨iG, hiG1, hiG2⟩ := exists_iso_pullback_of_hom hGc hGi
    ((BigAffineFppf.inclusion B integerBase hZ).map
      ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i)) δ hδ
  let Fi := (F.ofBaseEq hF).pullback (localSubSiteMap B hZ p hR hΛ' i)
  have hFi : Fi.base = (BigAffineFppf.inclusion B integerBase hZ).obj
      ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').obj i) := rfl
  have sqB := F.isPullback_pullbackHom_yoneda hF (localSubSiteMap B hZ p hR hΛ' i)
  have sqA := isPullback_pullbackHom_yoneda_self Fi
    ((BigAffineFppf.inclusion B integerBase hZ).map
      ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))
  have hπρ0 : (BigAffineFppf.inclusion B integerBase hZ).map
      ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i) ≫
      localSubSiteMap B hZ p hR hΛ' i = localCompletionSiteMap B hZ p hR hΛ' := by
    change integerSiteMap B hZ hΛ'
        (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' i.unop)
        (Spec.map (CommRingCat.ofHom
          (sub (Completion (Localization.AtPrime p)) R i.unop).val.toRingHom)) ≫
      integerSiteMap B hZ (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' i.unop) hR
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (sub (Completion (Localization.AtPrime p)) R i.unop)))) =
      integerSiteMap B hZ hΛ' hR
        (Spec.map (CommRingCat.ofHom (algebraMap R (Completion (Localization.AtPrime p)))))
    rw [integerSiteMap_comp, ← Spec.map_comp]
    congr 1
  have hπρ : yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
      ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i)) ≫
      yoneda.map (localSubSiteMap B hZ p hR hΛ' i) =
        yoneda.map (localCompletionSiteMap B hZ p hR hΛ') := by
    rw [← yoneda.map_comp, hπρ0]
  have sqAB := sqA.paste_horiz sqB
  rw [hπρ] at sqAB
  let iF := sqF'.isoIsPullback _ _ sqAB
  have hiF1 := sqF'.isoIsPullback_hom_fst _ _ sqAB
  have hiF2 := sqF'.isoIsPullback_hom_snd _ _ sqAB
  -- the morphism of total spaces over the completion, read on the base change of `Fᵢ`
  let hInf := iF.inv ≫ h' ≫ iG.hom
  have hhInf : hInf ≫ ((Gi.ofBaseEq hGi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
      ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))).toBaseYoneda =
      ((Fi.ofBaseEq hFi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))).toBaseYoneda := by
    change (iF.inv ≫ h' ≫ iG.hom) ≫ _ = _
    exact (Category.assoc _ _ _).trans ((congrArg (iF.inv ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (h' ≫ ·) hiG1).trans hh''))).trans ((Iso.inv_comp_eq _).mpr hiF2.symm))
  obtain ⟨k, s, hk, εF, εG, hhk, hεF, hεG, hεFc, hεGc, hcomm⟩ :=
    exists_stage_totalMap_of_isLimit (cone (Completion (Localization.AtPrime p)) R B hZ hΛ')
      (isLimit (Completion (Localization.AtPrime p)) R B hZ hΛ') i Fi Gi hFi hGi
      (ObjectProperty.homMk hInf) (ObjectProperty.hom_ext _ hhInf)
  -- Artin approximation of the stage `R[s_k] ⟶ R_𝔭^∧` through an elementary étale `R`-algebra
  have : Algebra.FiniteType R (sub (Completion (Localization.AtPrime p)) R k.unop) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  obtain ⟨D, _, _, _, pD, _, hpD, hres, χ, hχR, -, hcong⟩ :=
    StacksDraft.ArtinApproximation.exists_etaleApproximation_mem_maximalIdeal_pow p hGR 1 le_rfl
      (sub (Completion (Localization.AtPrime p)) R k.unop).val.toRingHom (RingHom.ext fun _ => rfl)
  obtain ⟨θ₁, hθ₁⟩ := exists_residueField_hom_of_etaleApproximation p pD hpD hres χ hcong
  have hD : B.Contains (Spec (.of D)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap R D))) hR
  let θ : pD.ResidueField →+* p.ResidueField :=
    (AdicCompletion.residueFieldCompletionEquiv (Localization.AtPrime p)).symm.toRingHom.comp θ₁
  -- the point `t` of `Spec D` and its compatibilities
  have K2 : (Spec.map (CommRingCat.ofHom θ₁) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))) ≫
        Spec.map (CommRingCat.ofHom χ) =
      closedPoint (Completion (Localization.AtPrime p)) ≫
        Spec.map (CommRingCat.ofHom
          (sub (Completion (Localization.AtPrime p)) R k.unop).val.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext e
    exact hθ₁ e
  have Kt : Spec.map (CommRingCat.ofHom θ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)) =
      (residueSpecIso (Localization.AtPrime p)).hom ≫ Spec.map (CommRingCat.ofHom θ₁) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)) := by
    change _ = Spec.map (CommRingCat.ofHom (AdicCompletion.residueFieldCompletionEquiv
      (Localization.AtPrime p)).symm.toRingHom) ≫ _
    simp only [← Spec.map_comp]
    rfl
  have K2' : (residueSpecIso (Localization.AtPrime p)).hom ≫
      closedPoint (Completion (Localization.AtPrime p)) ≫
        Spec.map (CommRingCat.ofHom
          (sub (Completion (Localization.AtPrime p)) R k.unop).val.toRingHom) =
      (Spec.map (CommRingCat.ofHom θ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))) ≫
          Spec.map (CommRingCat.ofHom χ) := by
    rw [Kt, Category.assoc, K2]
  have K3 : (Spec.map (CommRingCat.ofHom θ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R D)) =
      Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)) := by
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap R D)) = Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (sub (Completion (Localization.AtPrime p)) R k.unop))) := by
      rw [← Spec.map_comp, ← hχR]
      rfl
    have e2 : Spec.map (CommRingCat.ofHom
          (sub (Completion (Localization.AtPrime p)) R k.unop).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (sub (Completion (Localization.AtPrime p)) R k.unop))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Completion (Localization.AtPrime p)))) := by
      rw [← Spec.map_comp]
      rfl
    rw [e1, ← Category.assoc, ← K2', Category.assoc, Category.assoc, e2, ← K1,
      Iso.hom_inv_id_assoc]
  -- the stage maps
  let τ : integerSiteObject B hZ hD ⟶ (BigAffineFppf.inclusion B integerBase hZ).obj
      ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').obj k) :=
    integerSiteMap B hZ hD (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' k.unop)
      (Spec.map (CommRingCat.ofHom χ))
  have hτ : τ ≫ (BigAffineFppf.inclusion B integerBase hZ).map
      ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').map s) ≫
        localSubSiteMap B hZ p hR hΛ' i =
        integerSiteMap B hZ hD hR (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    change integerSiteMap B hZ hD
        (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' k.unop)
        (Spec.map (CommRingCat.ofHom χ)) ≫
      integerSiteMap B hZ (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' k.unop)
        (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' i.unop)
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion
          (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom s.unop)))).toRingHom)) ≫
      integerSiteMap B hZ (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' i.unop) hR
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (sub (Completion (Localization.AtPrime p)) R i.unop)))) = _
    rw [integerSiteMap_comp, integerSiteMap_comp]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change χ (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom s.unop)))
      (algebraMap R (sub (Completion (Localization.AtPrime p)) R i.unop) x)) = algebraMap R D x
    rw [AlgHom.commutes]
    exact RingHom.congr_fun hχR x
  -- the base change of `F` to `Spec D`
  let FD := (F.ofBaseEq hF).pullback
    (integerSiteMap B hZ hD hR (Spec.map (CommRingCat.ofHom (algebraMap R D))))
  have sqFD := F.isPullback_pullbackHom_yoneda hF
    (integerSiteMap B hZ hD hR (Spec.map (CommRingCat.ofHom (algebraMap R D))))
  have eι : yoneda.map (integerSiteMap B hZ hκ hR
      (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) =
      yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)))) ≫
      yoneda.map (integerSiteMap B hZ hD hR (Spec.map (CommRingCat.ofHom (algebraMap R D)))) :=
    ((yoneda_map_integerSiteMap_comp _ _).trans
      (congrArg (fun f => yoneda.map (integerSiteMap B hZ hκ hR f)) K3)).symm
  obtain ⟨ιD, hιDe, hιD⟩ : ∃ ιD : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ FD.total.obj,
      ιD ≫ ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hD hR
        (Spec.map (CommRingCat.ofHom (algebraMap R D))))).totalMap.hom = ι ∧
      IsPullback ιD (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) FD.toBaseYoneda
        (yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))))) :=
    ⟨_, sqFD.lift_fst _ _ _, IsPullback.of_right' (IsPullback.of_eq hι rfl rfl rfl eι) sqFD⟩
  -- the base change of `F` to the stage `k`
  let Fk := (Fi.ofBaseEq hFi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
    ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').map s))
  have sqK := isPullback_pullbackHom_yoneda_self Fi
    ((BigAffineFppf.inclusion B integerBase hZ).map
      ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').map s))
  have sqKB := sqK.paste_horiz sqB
  let mF : FD.total.obj ⟶ Fk.total.obj := sqKB.lift
    ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hD hR
      (Spec.map (CommRingCat.ofHom (algebraMap R D))))).totalMap.hom
    (FD.toBaseYoneda ≫ yoneda.map τ)
    (by
      rw [Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, hτ]
      exact sqFD.w)
  have hmF1 : mF ≫ _ = ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hD hR
      (Spec.map (CommRingCat.ofHom (algebraMap R D))))).totalMap.hom := sqKB.lift_fst _ _ _
  have hmF2 : mF ≫ Fk.toBaseYoneda = FD.toBaseYoneda ≫ yoneda.map τ := sqKB.lift_snd _ _ _
  -- the family `G` over `Spec D` and the morphism `h`
  let Gk := (Gi.ofBaseEq hGi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
    ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').map s))
  have hGk : Gk.base = (BigAffineFppf.inclusion B integerBase hZ).obj
      ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').obj k) := rfl
  let G := (Gk.ofBaseEq hGk).pullback τ
  have hG : G.base = integerSiteObject B hZ hD := rfl
  have eG : G.toBaseYonedaOfEq hG = G.toBaseYoneda := toBaseYonedaOfEq_rfl' G
  have sqG := isPullback_pullbackHom_yoneda_self Gk τ
  have hhk' : hk.hom ≫ Gk.toBaseYoneda = Fk.toBaseYoneda := congrArg (fun t => t.hom) hhk
  let h := sqG.lift (mF ≫ hk.hom) FD.toBaseYoneda (by rw [Category.assoc, hhk', hmF2])
  have hlift1 : h ≫ ((Gk.ofBaseEq hGk).pullbackHom τ).totalMap.hom = mF ≫ hk.hom :=
    sqG.lift_fst _ _ _
  have hlift2 : h ≫ G.toBaseYoneda = FD.toBaseYoneda := sqG.lift_snd _ _ _
  -- the fibre of `G` over `t`
  have hεGsq : IsPullback εG.totalMap.hom
      ((Gi.ofBaseEq hGi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))).toBaseYoneda
      Gk.toBaseYoneda
      (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app k))) := by
    have h1 := AlgebraicSpaces.isPullback_hom B integerBase hZ εG.cartesian
    rwa [hεG] at h1
  have hj1 : IsPullback (j' ≫ iG.hom)
      (yoneda.map (integerSiteMap B hZ hY₀ hκ'
        (pY₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)))
      ((Gi.ofBaseEq hGi).pullback ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))).toBaseYoneda
      (yoneda.map (localCompletionClosedPoint B hZ p hκ' hΛ')) :=
    hj''.of_iso (Iso.refl _) iG (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      ((Category.comp_id _).trans hiG1.symm) (by simp)
  have e3 : yoneda.map (integerSiteMap B hZ hY₀ hκ'
      (pY₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)) ≫ Ψ.inv =
      yoneda.map (integerSiteMap B hZ hY₀ hκ pY₀) := by
    rw [hΨ', yoneda_map_integerSiteMap_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e4 : Ψ.hom ≫ yoneda.map (localCompletionClosedPoint B hZ p hκ' hΛ') ≫
      yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app k)) =
        yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)))) ≫ yoneda.map τ := by
    change yoneda.map (integerSiteMap B hZ hκ hκ' (residueSpecIso (Localization.AtPrime p)).hom) ≫
        yoneda.map (integerSiteMap B hZ hκ' hΛ'
          (closedPoint (Completion (Localization.AtPrime p)))) ≫
          yoneda.map (integerSiteMap B hZ hΛ'
            (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' k.unop)
            (Spec.map (CommRingCat.ofHom
              (sub (Completion (Localization.AtPrime p)) R k.unop).val.toRingHom))) =
      yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)))) ≫
        yoneda.map (integerSiteMap B hZ hD
          (contains_sub (Completion (Localization.AtPrime p)) R B hΛ' k.unop)
          (Spec.map (CommRingCat.ofHom χ)))
    rw [yoneda_map_integerSiteMap_comp, yoneda_map_integerSiteMap_comp,
      yoneda_map_integerSiteMap_comp, K2']
  have hj3 := IsPullback.of_eq (hiso (hj1.paste_horiz hεGsq) Ψ) rfl e3 rfl e4
  obtain ⟨j, hjτ, hj⟩ : ∃ j : yoneda.obj (integerSiteObject B hZ hY₀) ⟶ G.total.obj,
      j ≫ ((Gk.ofBaseEq hGk).pullbackHom τ).totalMap.hom =
        ((j' ≫ iG.hom) ≫ εG.totalMap.hom) ∧
      IsPullback j (yoneda.map (integerSiteMap B hZ hY₀ hκ pY₀)) G.toBaseYoneda
        (yoneda.map (integerSiteMap B hZ hκ hD (Spec.map (CommRingCat.ofHom θ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField))))) :=
    ⟨_, sqG.lift_fst _ _ _, IsPullback.of_right' hj3 sqG⟩
  -- the fibre of `F_D` maps to the base change of `F` to the stage `k` compatibly
  have hεFc' : εF.totalMap.hom ≫ ((Fi.ofBaseEq hFi).pullbackHom
      ((BigAffineFppf.inclusion B integerBase hZ).map
        ((diagram (Completion (Localization.AtPrime p)) R B hZ hΛ').map s))).totalMap.hom =
      ((Fi.ofBaseEq hFi).pullbackHom ((BigAffineFppf.inclusion B integerBase hZ).map
        ((cone (Completion (Localization.AtPrime p)) R B hZ hΛ').π.app i))).totalMap.hom := by
    simpa only [comp_totalMap, ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun t => t.totalMap.hom) hεFc
  have e5 : yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀) ≫ Ψ.hom =
      yoneda.map (integerSiteMap B hZ hX₀ hκ'
        (pX₀ ≫ (residueSpecIso (Localization.AtPrime p)).hom)) := by
    rw [hΨ, yoneda_map_integerSiteMap_comp]
  have hιmF : ιD ≫ mF = ι' ≫ iF.hom ≫ εF.totalMap.hom := by
    apply sqKB.hom_ext
    · simp only [Category.assoc]
      rw [hmF1, hιDe, reassoc_of% hεFc', hiF1, hι'e]
    · simp only [Category.assoc]
      rw [hmF2, reassoc_of% hιD.w, totalMap_toBaseYoneda, reassoc_of% hiF2, reassoc_of% hι'0.w,
        hεF, ← e4, reassoc_of% e5]
  have hcomm' : εF.totalMap.hom ≫ hk.hom = hInf ≫ εG.totalMap.hom :=
    congrArg (fun t => t.hom) hcomm
  refine ⟨D, inferInstance, inferInstance, inferInstance, pD, inferInstance, hpD, hres, hD, θ,
    K3, G, hG, h, by rwa [eG], ιD, hιDe, hιD, j, by rwa [eG], ?_⟩
  apply sqG.hom_ext
  · rw [Category.assoc, Category.assoc, hjτ, hlift1, reassoc_of% hιmF, hcomm']
    change ι' ≫ iF.hom ≫ (iF.inv ≫ h' ≫ iG.hom) ≫ εG.totalMap.hom = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hιh']
  · rw [Category.assoc, Category.assoc, hlift2, hj.w, hιD.w, ← yoneda.map_comp_assoc,
      integerSiteMap_comp, hh₀]

end CurveFamily

end AlgebraicGeometry

end
