module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.ClosedImmersionThroughAdicPieces
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral

/-!
# Morphisms out of the spectrum of a flat algebra agreeing off and along `V(I)`

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `D` a flat `R`-algebra, and let `Spec D` be
an object of the big fppf site of `S`. Two morphisms `c, d : Spec D ⟶ W` to an algebraic space
over `S` are equal as soon as

* they agree over the open complement `U_D` of `V(I D)`,
* they agree on every closed subscheme `Spec (D / I ^ n D)`, and
* they agree after a proper morphism `q : Y ⟶ Spec D` from an algebraic space which is
  surjective over `U_D`.

This is the step of the existence half of [Stacks, Tag 0GI3] which shows that the morphism
`Spec Â ⟶ W` algebraizing a formal morphism satisfies the cocycle condition on the overlap
`Spec (Â ⊗_A Â)` of the fpqc covering `{U ⟶ X, Spec Â ⟶ X}`; there `R = Â`, `D = Â ⊗_A Â`
(which is not Noetherian, but is flat over `Â`) and `Y` is the base change of the proper
modification `X' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.eq_of_eq_off_zeroLocus_of_eq_on_quotients_of_isProper`: the statement
  above.

## Implementation notes

Let `e : E ⟶ Spec D` be the locus where `c` and `d` agree, the base change of the diagonal of
`W` along `(c, d)`; it is a monomorphism of schemes locally of finite type (Stacks 02X4), and a
site object `Z ⟶ Spec D` factors through `E` exactly when `c` and `d` agree on it.

*`e` is universally closed.* By Chow's lemma (Stacks 089J,
`AlgebraicGeometry.Space.exists_chowSchemeCover_over_spec`) there is a scheme `X''` with a proper
surjective morphism `h_{X''} ⟶ Y`; the composite `ψ : X'' ⟶ Spec D` is a universally closed
morphism of schemes on which `c` and `d` agree, so it factors through `E`. So does the closed
immersion `Spec (D / I D) ⟶ Spec D`. The induced morphism `X'' ⨿ Spec (D / I D) ⟶ E` is
surjective — `e` is injective on points, `ψ` hits every point of `U_D` and `Spec (D / I D)`
every point of `V(I D)` — and its composite with `e` is universally closed, so `e` is
universally closed (`AlgebraicGeometry.UniversallyClosed.of_comp_surjective`).

*`e` is an isomorphism.* Being a proper monomorphism, `e` is a closed immersion (Stacks 04XV).
Every `Spec D_g` with `g ∈ I` lies over `U_D` and every `Spec (D / I ^ n D)` factors through
`E`, so `e` is an isomorphism by
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_factors_away_quotient`, the place where the
flatness of `D` over the Noetherian ring `R` enters.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Morphisms out of the spectrum of a flat algebra agreeing off `V(I)`, along `V(I)` and
after a proper modification are equal.** Let `R` be a Noetherian ring, `I ⊆ R` an ideal, `D` a
flat `R`-algebra with `Spec D` an object of the big fppf site of `S`, and `c, d : Spec D ⟶ W`
morphisms to an algebraic space over `S`. Suppose that `c` and `d` agree on every site object
mapping into the complement of `V(I D)`, on every site object mapping into some
`Spec (D / I ^ n D)`, and after a proper morphism `q : Y ⟶ Spec D` from an algebraic space
whose image contains the complement of `V(I D)`. Then `c = d`. -/
theorem eq_of_eq_off_zeroLocus_of_eq_on_quotients_of_isProper
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {R D : Type u} [CommRing R] [IsNoetherianRing R] [CommRing D] [Algebra R D]
    [Module.Flat R D] (I : Ideal R)
    (hD : B.Contains (Spec (.of D))) (a : Spec (.of D) ⟶ S)
    (c d : yoneda.obj (siteObject B S hS hD a) ⟶ W)
    (hoff : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ siteObject B S hS hD a),
      Set.range ((BigFppfOver.toScheme B S hS).map z).base ⊆
        (PrimeSpectrum.zeroLocus ((I.map (algebraMap R D) : Ideal D) : Set D))ᶜ →
      yoneda.map z ≫ c = yoneda.map z ≫ d)
    (hquot : ∀ (n : ℕ) (Zo : BigFppfOver B S hS) (z : Zo ⟶ siteObject B S hS hD a),
      (∃ t : (BigFppfOver.toScheme B S hS).obj Zo ⟶
          Spec (.of (D ⧸ (I ^ n).map (algebraMap R D))),
        (BigFppfOver.toScheme B S hS).map z =
          t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ n).map (algebraMap R D))))) →
      yoneda.map z ≫ c = yoneda.map z ≫ d)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (q : Y ⟶ yoneda.obj (siteObject B S hS hD a)) (hq : IsProper B S hS q)
    (hqsurj : ∀ x : Spec (.of D),
      x ∉ PrimeSpectrum.zeroLocus ((I.map (algebraMap R D) : Ideal D) : Set D) →
      ∃ y : points B S hS Y,
        pointsToScheme B S hS _ (pointsMap B S hS Y q y) = x)
    (hqcd : q ≫ c = q ≫ d) :
    c = d := by
  let V := siteObject B S hS hD a
  -- the locus where `c` and `d` agree
  have hrep : yoneda.relativelyRepresentable (diag W) := hW.diagonal_representable
  let E := hrep.pullback (prod.lift c d)
  let e : E ⟶ V := hrep.snd (prod.lift c d)
  let eS : (BigFppfOver.toScheme B S hS).obj E ⟶ Spec (.of D) :=
    (BigFppfOver.toScheme B S hS).map e
  have hmono : Mono eS := (presheaf_monomorphisms_diag B S hS W hW).property_snd _
  have : LocallyOfFiniteType eS := (presheaf_locallyOfFiniteType_diag B S hS W hW).property_snd _
  have hdict : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      yoneda.map z ≫ c = yoneda.map z ≫ d → ∃ w : Zo ⟶ E, w ≫ e = z := by
    intro Zo z hz
    have hi : (yoneda.map z ≫ c) ≫ diag W = yoneda.map z ≫ prod.lift c d := by
      simp only [diag, prod.comp_lift, Category.comp_id, hz]
    exact ⟨hrep.lift (yoneda.map z ≫ c) z hi, hrep.lift_snd _ _ _⟩
  -- sections of `e` over monomorphisms into `Spec D` on which `c` and `d` agree
  have hsec : ∀ {A : Scheme.{u}} (h : A ⟶ Spec (.of D)), Mono h →
      (∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
        (∃ t : (BigFppfOver.toScheme B S hS).obj Zo ⟶ A,
          (BigFppfOver.toScheme B S hS).map z = t ≫ h) →
        yoneda.map z ≫ c = yoneda.map z ≫ d) →
      ∃ s : A ⟶ (BigFppfOver.toScheme B S hS).obj E, s ≫ eS = h := by
    intro A h hh hagree
    have hA : B.Contains A := B.contains_of_mono h hD
    let Zo : BigFppfOver B S hS :=
      Over.mk (ObjectProperty.homMk (X := B.obj hA) (Y := B.obj hS) (h ≫ a))
    let z : Zo ⟶ V := Over.homMk (ObjectProperty.homMk (X := B.obj hA) (Y := B.obj hD) h)
      (by apply ObjectProperty.hom_ext; rfl)
    obtain ⟨w, hw⟩ := hdict Zo z (hagree Zo z ⟨𝟙 A, (Category.id_comp h).symm⟩)
    exact ⟨_, by simpa [eS, z] using congrArg (BigFppfOver.toScheme B S hS).map hw⟩
  -- the pieces away from `V(I)`
  have haway : ∀ g ∈ I, ∃ s : Spec (.of (Localization.Away (algebraMap R D g))) ⟶
      (BigFppfOver.toScheme B S hS).obj E,
      s ≫ eS = Spec.map (CommRingCat.ofHom
        (algebraMap D (Localization.Away (algebraMap R D g)))) := by
    intro g hg
    refine hsec _ inferInstance fun Zo z ⟨t, ht⟩ => hoff Zo z ?_
    rw [ht]
    rintro _ ⟨x, rfl⟩ hx
    change (Spec.map (CommRingCat.ofHom
      (algebraMap D (Localization.Away (algebraMap R D g))))).base (t.base x) ∈ _ at hx
    generalize t.base x = x at hx
    have hmem : algebraMap R D g ∈ (I.map (algebraMap R D) : Ideal D) :=
      Ideal.mem_map_of_mem _ hg
    have h1 := (PrimeSpectrum.mem_zeroLocus _ _).mp hx hmem
    change algebraMap D (Localization.Away (algebraMap R D g)) (algebraMap R D g) ∈
      x.asIdeal at h1
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1
      (IsLocalization.Away.algebraMap_isUnit _))
  -- the pieces along `V(I)`
  have hQCI (n : ℕ) : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap R D))))) :=
    .spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hquot' : ∀ n : ℕ, ∃ s : Spec (.of (D ⧸ (I ^ n).map (algebraMap R D))) ⟶
      (BigFppfOver.toScheme B S hS).obj E,
      s ≫ eS = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ n).map (algebraMap R D)))) :=
    fun n => hsec _ inferInstance fun Zo z ht => hquot n Zo z ht
  -- a scheme proper over `Spec D` on which `c` and `d` agree, by Chow's lemma
  obtain ⟨X'', ψ, p, hp, hpsurj, hpq, -⟩ :=
    exists_chowSchemeCover_over_spec B S hS (.of D) hD a hY q hq.1 hq.2.1
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hψuc : AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map ψ) := by
    have huc : UniversallyClosed B S hS (yoneda.map ψ) := by
      rw [← hpq]
      exact universallyClosed_comp B S hS hY hV p q hp.2.2 hq.2.2
    exact (presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.UniversallyClosed.{u}) inferInstance ψ).mp
      ((presheaf_universallyClosed_iff B S hS (isAlgebraicSpace_yoneda B S hS X'') hV
        (Functor.relativelyRepresentable.map yoneda ψ)).mpr huc)
  obtain ⟨ψE, hψE⟩ := hdict X'' ψ (by rw [← hpq, Category.assoc, Category.assoc, hqcd])
  have hψEe : (BigFppfOver.toScheme B S hS).map ψE ≫ eS = (BigFppfOver.toScheme B S hS).map ψ := by
    simpa [eS] using congrArg (BigFppfOver.toScheme B S hS).map hψE
  obtain ⟨sQ, hsQ⟩ := hquot' 1
  -- `e` is universally closed
  let P : Bool → Scheme.{u} := fun b =>
    cond b ((BigFppfOver.toScheme B S hS).obj X'') (Spec (.of (D ⧸ (I ^ 1).map (algebraMap R D))))
  let fam : ∀ b, P b ⟶ (BigFppfOver.toScheme B S hS).obj E := fun b =>
    Bool.rec (motive := fun b => P b ⟶ (BigFppfOver.toScheme B S hS).obj E) sQ
      ((BigFppfOver.toScheme B S hS).map ψE) b
  have hfam : ∀ b, AlgebraicGeometry.UniversallyClosed (fam b ≫ eS) := by
    intro b
    cases b
    · show AlgebraicGeometry.UniversallyClosed (sQ ≫ eS)
      rw [hsQ]
      have := hQCI 1
      infer_instance
    · show AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map ψE ≫ eS)
      rw [hψEe]
      exact hψuc
  have hcomp : Sigma.desc fam ≫ eS = Sigma.desc (fun b => fam b ≫ eS) := by
    ext b
    simp
  have hUC : AlgebraicGeometry.UniversallyClosed (Sigma.desc fam ≫ eS) := by
    rw [hcomp]
    exact universallyClosed_sigmaDesc _
  have hinj : Function.Injective eS.base := eS.injective
  have hι : ∀ (b : Bool) (x : P b), (Sigma.desc fam).base ((Sigma.ι P b).base x) = (fam b).base x :=
    fun b x => by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hsurj : Surjective (Sigma.desc fam) := by
    refine ⟨fun z => ?_⟩
    by_cases hv : eS.base z ∈
      PrimeSpectrum.zeroLocus ((I.map (algebraMap R D) : Ideal D) : Set D)
    · have hv' : eS.base z ∈
          PrimeSpectrum.zeroLocus (((I ^ 1).map (algebraMap R D) : Ideal D) : Set D) := by
        rwa [pow_one]
      rw [← Ideal.mk_ker (I := (I ^ 1).map (algebraMap R D)),
        ← _root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective] at hv'
      obtain ⟨y, hy⟩ := hv'
      refine ⟨(Sigma.ι P false).base y, ?_⟩
      apply hinj
      refine (congrArg eS.base (hι false y)).trans ?_
      show (sQ ≫ eS).base y = _
      rw [hsQ]
      exact hy
    · obtain ⟨y, hy⟩ := hqsurj _ hv
      obtain ⟨y'', rfl⟩ := hpsurj y
      refine ⟨(Sigma.ι P true).base (pointsToScheme B S hS X'' y''), ?_⟩
      apply hinj
      refine (congrArg eS.base (hι true _)).trans ?_
      show ((BigFppfOver.toScheme B S hS).map ψE ≫ eS).base _ = _
      rw [hψEe, ← hy, ← pointsMap_comp_apply, hpq, pointsToScheme_pointsMap_yoneda]
  have : AlgebraicGeometry.UniversallyClosed eS :=
    AlgebraicGeometry.UniversallyClosed.of_comp_surjective (Sigma.desc fam) eS
  -- `e` is a closed immersion, hence an isomorphism
  have : AlgebraicGeometry.IsClosedImmersion eS :=
    (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono eS).mpr ⟨{}, hmono⟩
  have hiso : IsIso eS :=
    isIso_of_isClosedImmersion_of_factors_away_quotient I eS haway hquot'
  have h1 : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map e)) := hiso
  have h2 : IsIso ((Over.forget (B.obj hS)).map e) := isIso_of_reflects_iso _ B.inclusion
  have h3 : IsIso e := isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have hw := hrep.w (prod.lift c d)
  have hG : prod.lift c d = (inv (yoneda.map e) ≫ hrep.fst (prod.lift c d)) ≫ diag W := by
    rw [Category.assoc, hw, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have h4 := congrArg (fun α : yoneda.obj V ⟶ W ⨯ W => α ≫ prod.fst) hG
  have h5 := congrArg (fun α : yoneda.obj V ⟶ W ⨯ W => α ≫ prod.snd) hG
  simp only [diag, Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h4 h5
  exact h4.trans h5.symm

end Space

end AlgebraicGeometry

end
