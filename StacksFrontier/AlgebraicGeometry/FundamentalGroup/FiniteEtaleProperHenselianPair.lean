module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianPairGRing
public import StacksFrontier.AlgebraicGeometry.Limits.ProperLimitOfFiniteTypeOverZ
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
import all StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation

/-!
# Finite étale covers of a proper scheme over a henselian pair

Let `(A, I)` be a henselian pair and `X` a proper scheme over `A`, with closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`. This file proves [Stacks, Tag 0GS2]: base change
`FÉt_X ⥤ FÉt_{X₀}, U ↦ U ×_X X₀` is an equivalence of categories.

## The argument

The first four paragraphs of the source's proof (the complete case and the case of a Noetherian
G-ring) are `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianPairGRing`.
This file carries out the last one, the general case. Full faithfulness is deduced from essential
surjectivity, for the schemes finite étale over `X`, by
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`.

For essential surjectivity, Tag 0A0P writes `p : X ⟶ Spec A` as the limit of proper morphisms
`fᵢ : Xᵢ ⟶ Sᵢ` with `Sᵢ` of finite type over `ℤ` and affine transition morphisms; the targets are
eventually affine (Tag 01Z6), so `Sᵢ = Spec Rᵢ` with `Rᵢ` a finitely generated `ℤ`-algebra. Base
change commutes with the limit, so `X₀` is the limit of the `Xᵢ ×_{Sᵢ} Spec (A ⧸ I)`, and these
in turn are the limit of the `Xᵢ ×_{Rᵢ} Spec C` over the finitely generated `Rᵢ`-subalgebras `C` of
`A ⧸ I`. A finite étale cover of `X₀` therefore comes from one of some `Xᵢ ×_{Rᵢ} Spec C`
(Tags 01ZM, 01ZO, 07RP). Lift the generators of `C` to `A` and let `E ⊆ A` be the `Rᵢ`-subalgebra
they generate, so that `E` maps onto `C` with kernel `I ∩ E`. The henselization `Eʰ` of the pair
`(E, I ∩ E)` is a henselian pair with a Noetherian G-ring (Tags 07PX, 0AH3), and it maps to `A`
compatibly with `I` (Tag 0A02). The scheme `Y = Xᵢ ×_{Rᵢ} Spec Eʰ` is proper over `Eʰ`, so by the
G-ring case the cover, pulled back to the closed fibre of `Y`, which maps to `Xᵢ ×_{Rᵢ} Spec C`,
comes from a finite étale cover of `Y`; its pullback along `X ⟶ Y` is the required cover of `X`.

The lifting through the two limits and the stage is organised around the statement "every finite
étale cover of `W` pulled back to `X₀` along `q : X₀ ⟶ W` is the restriction of a finite étale
cover of `X`", which composes (`AlgebraicGeometry.finiteEtale_lift_comp`), passes to limits
(`AlgebraicGeometry.finiteEtale_lift_of_isLimit`), and holds when `q` factors through a base
change along which pulling back is essentially surjective
(`AlgebraicGeometry.finiteEtale_lift_of_factors`).

## Main results

* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_isProper_of_henselianPair`: essential
  surjectivity of base change to the closed fibre.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair`:
  **Tag 0GS2**.

The case of a henselian local ring and its maximal ideal is Tag 0A48,
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
* [Stacks Project, Tag 0AH3](https://stacks.math.columbia.edu/tag/0AH3)
* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Lifting finite étale covers along a morphism to the closed fibre -/

section Lifting

/-- **Lifting composes with a further morphism.** If every finite étale cover of `W`, pulled back
along `q : X₀ ⟶ W`, is the pullback along `g : X₀ ⟶ X` of a finite étale cover of `X`, then the
same holds for `q ≫ s` and any `s : W ⟶ W'`. -/
theorem finiteEtale_lift_comp {X X₀ W W' : Scheme.{u}} (g : X₀ ⟶ X) (q : X₀ ⟶ W) (s : W ⟶ W')
    (h : ∀ B : FiniteEtaleOver W, ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange q).obj B))
    {q' : X₀ ⟶ W'} (hq : q ≫ s = q') (B : FiniteEtaleOver W') : ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange q').obj B) := by
  subst hq
  obtain ⟨V, ⟨e⟩⟩ := h ((finiteEtaleBaseChange s).obj B)
  exact ⟨V, ⟨e ≪≫ ((finiteEtaleBaseChangeComp q s).app B).symm⟩⟩

/-- **Lifting passes to a cofiltered limit.** Let `c` be a limit of a cofiltered system of
quasi-compact quasi-separated schemes with affine transition morphisms, and `q : X₀ ⟶ c.pt`. If
lifting along `g : X₀ ⟶ X` holds for each `q ≫ c.π.app j`, it holds for `q`: a finite étale cover
of the limit comes from a stage (Tags 01ZM, 01ZO, 07RP). -/
theorem finiteEtale_lift_of_isLimit {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : J, CompactSpace (D.obj i)] [∀ i : J, QuasiSeparatedSpace (D.obj i)]
    {X X₀ : Scheme.{u}} (g : X₀ ⟶ X) (q : X₀ ⟶ c.pt)
    (h : ∀ (j : J) (B : FiniteEtaleOver (D.obj j)), ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange (q ≫ c.π.app j)).obj B))
    (B : FiniteEtaleOver c.pt) : ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange q).obj B) := by
  obtain ⟨j, B', ⟨ε⟩⟩ := exists_finiteEtale_model D c hc B
  obtain ⟨V, ⟨e⟩⟩ := h j B'
  exact ⟨V, ⟨e ≪≫ (finiteEtaleBaseChangeComp q (c.π.app j)).app B' ≪≫
    (finiteEtaleBaseChange q).mapIso ε.symm⟩⟩

/-- **Lifting through a factorization.** If `q = z ≫ w` where `z : X₀ ⟶ Y₀` is compatible, through
`r : Y₀ ⟶ Y` and `a : X ⟶ Y`, with `g : X₀ ⟶ X`, and pulling back along `r` is essentially
surjective on finite étale covers, then every finite étale cover of the target of `w`, pulled
back along `q`, is the pullback along `g` of a finite étale cover of `X`. -/
theorem finiteEtale_lift_of_factors {X X₀ Y Y₀ W : Scheme.{u}} (g : X₀ ⟶ X) (a : X ⟶ Y)
    (r : Y₀ ⟶ Y) (z : X₀ ⟶ Y₀) (w : Y₀ ⟶ W) [(finiteEtaleBaseChange r).EssSurj]
    (hzr : z ≫ r = g ≫ a) {q : X₀ ⟶ W} (hq : z ≫ w = q) (B : FiniteEtaleOver W) :
    ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange q).obj B) := by
  subst hq
  let V' := (finiteEtaleBaseChange r).objPreimage ((finiteEtaleBaseChange w).obj B)
  exact ⟨(finiteEtaleBaseChange a).obj V', ⟨
    (finiteEtaleBaseChangeComp g a (g ≫ a) rfl).symm.app V' ≪≫
    (finiteEtaleBaseChangeComp z r (g ≫ a) hzr.symm).app V' ≪≫
    (finiteEtaleBaseChange z).mapIso ((finiteEtaleBaseChange r).objObjPreimageIso _) ≪≫
    ((finiteEtaleBaseChangeComp z w).app B).symm⟩⟩

/-- **Essential surjectivity from lifting along the identity.** -/
theorem essSurj_finiteEtaleBaseChange_of_finiteEtale_lift {X X₀ : Scheme.{u}} (g : X₀ ⟶ X)
    (h : ∀ B : FiniteEtaleOver X₀, ∃ V : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange g).obj V ≅ (finiteEtaleBaseChange (𝟙 X₀)).obj B)) :
    (finiteEtaleBaseChange g).EssSurj :=
  ⟨fun B =>
    let ⟨V, ⟨e⟩⟩ := h B
    ⟨V, ⟨e ≪≫ finiteEtaleBaseChangeId.app B⟩⟩⟩

end Lifting

/-! ### One stage of the limit -/

/-- **The global sections of an affine scheme of finite type over `ℤ` form a G-ring.** Such a ring
is a finitely generated `ℤ`-algebra (Tag 07PX). -/
theorem isGRing_Γ_of_locallyOfFiniteType_terminal (S : Scheme.{u}) [IsAffine S]
    [LocallyOfFiniteType (terminal.from S)] : IsGRing Γ(S, ⊤) := by
  let R : Type u := Γ(S, ⊤)
  let tZ : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let ρZ : ULift.{u} ℤ →+* R := (Int.castRingHom R).comp ULift.ringEquiv.toRingHom
  have e1 : Spec.map (CommRingCat.ofHom ρZ) = S.isoSpec.inv ≫ terminal.from S ≫ tZ.hom :=
    specULiftZIsTerminal.hom_ext _ _
  have hρ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ρZ)) := by
    rw [e1]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hρ
  have hsurj : Function.Surjective (algebraMap ℤ (ULift.{u} ℤ)) := fun y =>
    ⟨y.down, by ext; simp⟩
  have hft : (ρZ.comp (algebraMap ℤ (ULift.{u} ℤ))).FiniteType :=
    RingHom.FiniteType.comp hρ (RingHom.FiniteType.of_surjective _ hsurj)
  have : Algebra.FiniteType ℤ R := by
    rw [← RingHom.finiteType_algebraMap]
    convert hft
    exact Subsingleton.elim _ _
  exact isGRing_basic_examples.{0, u}.2.2.2.2 ℤ R isGRing_basic_examples.{0, 0}.2.2.1

/-- **Lifting a finitely generated subalgebra of `A ⧸ I`.** For a finite set `μ ⊆ A ⧸ I`, there
is an `R`-subalgebra `E` of `A` of finite type over `R` with a surjective `R`-algebra map
`E → R[μ] ⊆ A ⧸ I` given by reduction modulo `I`; one takes `E` generated by lifts of `μ`. -/
theorem exists_finiteType_surjective_adjoin {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal A) (μ : Finset (A ⧸ I)) :
    ∃ (E : Subalgebra R A) (ψ : E →ₐ[R] Algebra.adjoin R (μ : Set (A ⧸ I))),
      Algebra.FiniteType R E ∧ Function.Surjective ψ ∧
        ∀ x : E, (ψ x : A ⧸ I) = Ideal.Quotient.mk I (x : A) := by
  classical
  let s : A ⧸ I → A := Function.surjInv Ideal.Quotient.mk_surjective
  have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := Function.surjInv_eq Ideal.Quotient.mk_surjective
  let E : Subalgebra R A := Algebra.adjoin R ((μ.image s : Finset A) : Set A)
  let ψE : E →ₐ[R] A ⧸ I := (Ideal.Quotient.mkₐ R I).comp E.val
  have hrange : ψE.range = Algebra.adjoin R (μ : Set (A ⧸ I)) := by
    rw [AlgHom.range_comp, Subalgebra.range_val, AlgHom.map_adjoin, Finset.coe_image,
      Set.image_image]
    congr 1
    ext x
    simp [hs]
  refine ⟨E, ψE.codRestrict (Algebra.adjoin R (μ : Set (A ⧸ I)))
    fun x => hrange ▸ ψE.mem_range_self x,
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _), fun y => ?_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : (y : A ⧸ I) ∈ ψE.range := by
    rw [hrange]
    exact y.2
  exact ⟨x, Subtype.ext hx⟩

/-- **A henselian G-ring between `R[μ] ⊆ A ⧸ I` and `A`.** Let `R` be a Noetherian G-ring, `(A, I)`
a henselian pair over `R` and `C = R[μ] ⊆ A ⧸ I` for a finite set `μ`. Then there are a henselian
pair `(Bʰ, J)` with `Bʰ` a G-ring, ring maps `R → Bʰ → A` composing to the structure map with `J`
mapping into `I`, and a ring map `C → Bʰ ⧸ J` over `R` whose composite with `Bʰ ⧸ J → A ⧸ I` is
the inclusion. One takes `Bʰ` the henselization of the subalgebra of `A` generated by lifts of
`μ` (Tags 07PX, 0AH3, 0A02). -/
theorem exists_henselianPair_isGRing_factor_adjoin {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hGR : IsGRing R) (I : Ideal A) (hI : HenselianPair A I)
    (μ : Finset (A ⧸ I)) :
    ∃ (Bh : Type u) (_ : CommRing Bh) (J : Ideal Bh) (ρ : R →+* Bh) (β : Bh →+* A)
      (κ : Algebra.adjoin R (μ : Set (A ⧸ I)) →+* Bh ⧸ J) (hβJ : J ≤ I.comap β),
      HenselianPair Bh J ∧ IsGRing Bh ∧ β.comp ρ = algebraMap R A ∧
      κ.comp (algebraMap R _) = (Ideal.Quotient.mk J).comp ρ ∧
      (Ideal.quotientMap I β hβJ).comp κ = (Algebra.adjoin R (μ : Set (A ⧸ I))).val.toRingHom := by
  let C := Algebra.adjoin R (μ : Set (A ⧸ I))
  obtain ⟨E, ψ', _, hψ', hψ'v⟩ := exists_finiteType_surjective_adjoin (R := R) I μ
  have hGE : IsGRing E := isGRing_basic_examples.{u, u}.2.2.2.2 R E hGR
  let IE : Ideal E := I.comap (algebraMap E A)
  obtain ⟨Bh, _, ι, hhB, hu⟩ := exists_henselization.{u, u} E IE
  let : Algebra E Bh := ι.toAlgebra
  let J : Ideal Bh := IE.map ι
  obtain ⟨β, ⟨hβ, hβJ⟩, -⟩ := hu A inferInstance I hI (algebraMap E A) le_rfl
  have hβι : ∀ x, β (ι x) = (x : A) := RingHom.congr_fun hβ
  have hker : RingHom.ker ψ'.toRingHom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp ι) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hxI : (x : A) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hψ'v]
      exact congrArg Subtype.val hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem ι hxI
  let κ : C →+* Bh ⧸ J := (ψ'.toRingHom.liftOfSurjective hψ') ⟨_, hker⟩
  have hκ : ∀ x : E, κ (ψ' x) = Ideal.Quotient.mk J (ι x) := fun x =>
    RingHom.liftOfSurjective_comp_apply ψ'.toRingHom hψ' ⟨_, hker⟩ x
  refine ⟨Bh, inferInstance, J, ι.comp (algebraMap R E), β, κ, hβJ, hhB,
    isGRing_henselization hGE IE Bh hhB hu, ?_, ?_, ?_⟩
  · ext r
    exact hβι _
  · ext r
    rw [RingHom.comp_apply, ← ψ'.commutes r]
    exact hκ _
  · ext y
    obtain ⟨x, rfl⟩ := hψ' y
    rw [RingHom.comp_apply, hκ]
    show Ideal.quotientMap I β hβJ (Ideal.Quotient.mk J (ι x)) = (ψ' x : A ⧸ I)
    rw [Ideal.quotientMap_mk, hψ'v, hβι]

/-- **Lifting at one stage of the limit, over a G-ring.** Let `R` be a Noetherian G-ring, `(A, I)`
a henselian pair over `R`, `p : X ⟶ Spec A`, and `a : X ⟶ Xₖ` over a proper `f : Xₖ ⟶ Spec R`.
Then every finite étale cover of `Spec (A ⧸ I) ×_R Xₖ`, pulled back to the closed fibre `X₀` of
`p` along the map `q` induced by `a`, is the restriction of a finite étale cover of `X`. -/
theorem finiteEtale_lift_closedFibre_of_isGRing {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hGR : IsGRing R) (I : Ideal A) (hI : HenselianPair A I) {X Xk : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (f : Xk ⟶ Spec (.of R)) [IsProper f] (a : X ⟶ Xk)
    (w : a ≫ f = p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))
    {q : pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) f}
    (hq₁ : q ≫ pullback.fst _ _ = pullback.snd _ _)
    (hq₂ : q ≫ pullback.snd _ _ = pullback.fst _ _ ≫ a)
    (B : FiniteEtaleOver (pullback (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) f)) :
    ∃ V : FiniteEtaleOver X, Nonempty
      ((finiteEtaleBaseChange
          (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj V ≅
        (finiteEtaleBaseChange q).obj B) := by
  let t : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have ht : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = t := rfl
  have : IsNoetherianRing R := hGR.1
  have := fun i => (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace R (A ⧸ I) f i).1
  have := fun i => (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace R (A ⧸ I) f i).2
  have : ∀ {i j : (Finset (A ⧸ I))ᵒᵖ} (e : i ⟶ j),
      IsAffineHom ((AdjoinFinset.bcDiagram R (A ⧸ I) f).map e) :=
    fun e => AdjoinFinset.bcDiagram_isAffineHom R (A ⧸ I) f e
  refine finiteEtale_lift_of_isLimit (AdjoinFinset.bcDiagram R (A ⧸ I) f)
    (AdjoinFinset.bcCone R (A ⧸ I) f) (AdjoinFinset.isLimitBcCone R (A ⧸ I) f)
    (pullback.fst p t) q (fun μ B' => ?_) B
  let C := Algebra.adjoin R (μ.unop : Set (A ⧸ I))
  obtain ⟨Bh, _, J, ρ, β, κ, hβJ, hhB, hGB, E1, E3, E4⟩ :=
    exists_henselianPair_isGRing_factor_adjoin hGR I hI μ.unop
  let ρS : Spec (.of Bh) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ρ)
  let qY : pullback f ρS ⟶ Spec (.of Bh) := pullback.snd f ρS
  let mkJ : Spec (.of (Bh ⧸ J)) ⟶ Spec (.of Bh) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let r : pullback qY mkJ ⟶ pullback f ρS := pullback.fst qY mkJ
  have : (finiteEtaleBaseChange r).EssSurj :=
    (isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair Bh J hhB hGB
      qY).essSurj
  let aY : X ⟶ pullback f ρS := pullback.lift a (p ≫ Spec.map (CommRingCat.ofHom β)) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, E1, w])
  let z : pullback p t ⟶ pullback qY mkJ := pullback.lift (pullback.fst p t ≫ aY)
    (pullback.snd p t ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap I β hβJ))) (by
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, ← ht]
      simp only [mkJ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk hβJ])
  let wμ : pullback qY mkJ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) f :=
    pullback.lift (pullback.snd qY mkJ ≫ Spec.map (CommRingCat.ofHom κ))
      (r ≫ pullback.fst f ρS) (by
        rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, E3, Category.assoc,
          pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hzr : z ≫ r = pullback.fst p t ≫ aY := pullback.lift_fst _ _ _
  have hzw : z ≫ wμ = q ≫ (AdjoinFinset.bcCone R (A ⧸ I) f).π.app μ := by
    show z ≫ wμ = q ≫ AdjoinFinset.bcProj R (A ⧸ I) f μ
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_snd, Category.assoc,
        Category.assoc, AdjoinFinset.bcProj_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, E4,
        ← Category.assoc q, hq₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hzr, Category.assoc,
        pullback.lift_fst, Category.assoc, AdjoinFinset.bcProj_snd, hq₂]
  exact finiteEtale_lift_of_factors (pullback.fst p t) aY r z wμ hzr hzw B'

/-- **Lifting at one stage of the limit.** Let `(A, I)` be a henselian pair, `p : X ⟶ Spec A`, and
let `X ⟶ Xₖ`, `Spec A ⟶ S` be a commutative square over a proper `fₖ : Xₖ ⟶ S` with `S` affine of
finite type over `ℤ`. Then every finite étale cover of `Xₖ ×_S Spec (A ⧸ I)`, pulled back to the
closed fibre `X₀` of `p`, is the restriction of a finite étale cover of `X`.

This is the stage of the general case of the source's proof; see the module docstring. -/
theorem finiteEtale_lift_closedFibre_of_isAffine (A : Type u) [CommRing A] (I : Ideal A)
    (hI : HenselianPair A I) {X Xk S : Scheme.{u}} (p : X ⟶ Spec (.of A)) (fk : Xk ⟶ S)
    [IsProper fk] [IsAffine S] [LocallyOfFiniteType (terminal.from S)] (a : X ⟶ Xk)
    (π : Spec (.of A) ⟶ S) (w : a ≫ fk = p ≫ π)
    {q' : pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
      pullback fk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ π)}
    (hq : pullback.map p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) fk
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ π) a (𝟙 _) π w.symm (by simp) = q')
    (B : FiniteEtaleOver
      (pullback fk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ π))) :
    ∃ V : FiniteEtaleOver X, Nonempty
      ((finiteEtaleBaseChange
          (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj V ≅
        (finiteEtaleBaseChange q').obj B) := by
  subst hq
  let t : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have ht : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = t := rfl
  let q := pullback.map p t fk (t ≫ π) a (𝟙 _) π w.symm (by simp)
  let R : Type u := Γ(S, ⊤)
  let ψ : S ≅ Spec (.of R) := S.isoSpec
  let f' : Xk ⟶ Spec (.of R) := fk ≫ ψ.hom
  let h : CommRingCat.of R ⟶ CommRingCat.of A := Spec.preimage (π ≫ ψ.hom)
  have hh : Spec.map h = π ≫ ψ.hom := Spec.map_preimage _
  let : Algebra R A := h.hom.toAlgebra
  have hπt : t ≫ π ≫ ψ.hom = Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I))) := by
    rw [← hh, ← ht, ← Spec.map_comp]
    rfl
  let m : pullback fk (t ≫ π) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) f' :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _) (by
      rw [← hπt]
      simp only [f', Category.assoc, pullback.condition_assoc])
  let m' : pullback (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) f' ⟶
      pullback fk (t ≫ π) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _) (by
      rw [← cancel_mono ψ.hom, Category.assoc, Category.assoc, Category.assoc, hπt]
      exact pullback.condition.symm)
  have hmm' : m ≫ m' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  have hw : a ≫ f' = p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    show a ≫ fk ≫ ψ.hom = p ≫ Spec.map h
    rw [hh, ← Category.assoc, w, Category.assoc]
  have : IsProper f' := by
    dsimp [f']
    infer_instance
  exact finiteEtale_lift_comp (pullback.fst p t) (q ≫ m) m'
    (finiteEtale_lift_closedFibre_of_isGRing (isGRing_Γ_of_locallyOfFiniteType_terminal S) I hI
      p f' a hw (q := q ≫ m)
      (by rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_fst]))
    (by rw [Category.assoc, hmm', Category.comp_id]) B

/-! ### Base change of a system of proper morphisms -/

section BaseChangeSystem

variable {K : Type u} [Category.{u} K] {X S : K ⥤ Scheme.{u}} (φ : X ⟶ S)
  {cS : Cone S} {T : Scheme.{u}} (g : T ⟶ cS.pt)

/-- The stages of the base change of a system of proper morphisms along a morphism from a
quasi-compact scheme are quasi-compact. -/
theorem compactSpace_baseChangeSystem_obj [∀ j, IsProper (φ.app j)] [CompactSpace T] (j : K) :
    CompactSpace ((baseChangeSystem φ g).obj j) := by
  show CompactSpace ((pullback (φ.app j) (g ≫ cS.π.app j) : Scheme.{u}) : Type u)
  infer_instance

/-- The stages of the base change of a system of proper morphisms along a morphism from a
quasi-separated scheme are quasi-separated. -/
theorem quasiSeparatedSpace_baseChangeSystem_obj [∀ j, IsProper (φ.app j)]
    [QuasiSeparatedSpace T] (j : K) : QuasiSeparatedSpace ((baseChangeSystem φ g).obj j) := by
  show QuasiSeparatedSpace ((pullback (φ.app j) (g ≫ cS.π.app j) : Scheme.{u}) : Type u)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd _ _)

/-- The transition morphisms of the base change of a system with affine transition morphisms are
affine. -/
theorem isAffineHom_baseChangeSystem_map [∀ {i j : K} (e : i ⟶ j), IsAffineHom (X.map e)]
    [∀ {i j : K} (e : i ⟶ j), IsAffineHom (S.map e)] {i j : K} (e : i ⟶ j) :
    IsAffineHom ((baseChangeSystem φ g).map e) :=
  Stacks.AlgebraicGeometry.Fibres.isAffineHom_pullback_map _ _ _ _ (X.map e) (𝟙 _) (S.map e)
    (φ.naturality e).symm (by
      rw [Category.id_comp, Category.assoc]
      exact congrArg (g ≫ ·) (cS.w e))

end BaseChangeSystem

/-! ### The general case -/

/-- **Stacks Tag 0GS2, essential surjectivity.** Let `(A, I)` be a henselian pair and let
`p : X ⟶ Spec A` be proper. Then every finite étale cover of the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is the base change of a finite étale cover of `X`.

This is the general case of the source's proof; see the module docstring. -/
theorem essSurj_finiteEtaleBaseChange_of_isProper_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
    [IsProper p] :
    (finiteEtaleBaseChange (pullback.fst p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).EssSurj := by
  obtain ⟨K, _, hne, hdir, D, c, hproper, hftype, haff, ⟨hc⟩, ⟨iso⟩⟩ :=
    exists_isLimit_isProper_finiteType_arrow p
  have : IsCofilteredOrEmpty Kᵒᵖ := isCofilteredOrEmpty_opposite_of_isDirected
  have : Nonempty Kᵒᵖ := Nonempty.map op hne
  have : IsCofiltered Kᵒᵖ := ⟨⟩
  have : ∀ {i j : Kᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.leftFunc).map g) :=
    fun g => (haff g).1
  have : ∀ {i j : Kᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.rightFunc).map g) :=
    fun g => (haff g).2
  have : ∀ j, IsProper (D.obj j).hom := hproper
  let c' : Cone D := c.extend iso.inv
  have hc' : IsLimit c' := hc.extendIso iso.inv
  let φ : (D ⋙ Arrow.leftFunc) ⟶ (D ⋙ Arrow.rightFunc) :=
    { app := fun j => (D.obj j).hom
      naturality := fun _ _ g => (D.map g).w }
  let cX : Cone (D ⋙ Arrow.leftFunc) := ⟨X, (Arrow.leftFunc.mapCone c').π⟩
  let cS : Cone (D ⋙ Arrow.rightFunc) := ⟨Spec (.of A), (Arrow.rightFunc.mapCone c').π⟩
  have hX : IsLimit cX := Stacks.AlgebraicGeometry.Fibres.isLimitLeftFuncMapCone D c' hc'
  have hS : IsLimit cS := Stacks.AlgebraicGeometry.Fibres.isLimitRightFuncMapCone D c' hc'
  have hp : ∀ j, cX.π.app j ≫ φ.app j = p ≫ cS.π.app j := fun j => (c'.π.app j).w
  let t : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hW := isLimitBaseChangeSystemCone φ hX hS hp t
  have : ∀ j, IsNoetherian ((D ⋙ Arrow.rightFunc).obj j) := fun j =>
    have : LocallyOfFiniteType (terminal.from ((D ⋙ Arrow.rightFunc).obj j)) := (hftype j).1
    have : QuasiCompact (terminal.from ((D ⋙ Arrow.rightFunc).obj j)) := (hftype j).2
    isNoetherian_of_locallyOfFiniteType_terminal_from _
  have : ∀ j, IsProper (φ.app j) := hproper
  have := compactSpace_baseChangeSystem_obj (cS := cS) φ t
  have := quasiSeparatedSpace_baseChangeSystem_obj (cS := cS) φ t
  have : ∀ {i j : Kᵒᵖ} (g : i ⟶ j), IsAffineHom ((baseChangeSystem (cS := cS) φ t).map g) :=
    fun g => isAffineHom_baseChangeSystem_map (cS := cS) φ t g
  obtain ⟨i₀, hi₀⟩ := Scheme.exists_isAffine_of_isLimit (D ⋙ Arrow.rightFunc) cS hS
  refine essSurj_finiteEtaleBaseChange_of_finiteEtale_lift _ ?_
  refine finiteEtale_lift_of_isLimit (baseChangeSystem (cS := cS) φ t)
    (baseChangeSystemCone φ hp t) hW
    (pullback.fst p t) (𝟙 _) fun j B => ?_
  let k := IsCofiltered.min j i₀
  have : IsAffine ((D ⋙ Arrow.rightFunc).obj k) :=
    isAffine_of_isAffineHom ((D ⋙ Arrow.rightFunc).map (IsCofiltered.minToRight j i₀))
  have hk := (baseChangeSystemCone φ hp t).w (IsCofiltered.minToLeft j i₀)
  refine finiteEtale_lift_comp (pullback.fst p t) (𝟙 _ ≫ (baseChangeSystemCone φ hp t).π.app k)
    _ (fun B' => ?_) (by rw [Category.assoc, hk]) B
  have : LocallyOfFiniteType (terminal.from ((D ⋙ Arrow.rightFunc).obj k)) := (hftype k).1
  exact finiteEtale_lift_closedFibre_of_isAffine A I hI p (φ.app k) (cX.π.app k) (cS.π.app k)
    (hp k) (by rw [Category.id_comp]) B'

/-- **Stacks Project, Tag 0GS2.** Let `(A, I)` be a henselian pair and let `X` be a proper scheme
over `A`, with closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)`. Then base change
`FÉt_X ⥤ FÉt_{X₀}, U ↦ U ×_X X₀` is an equivalence of categories.

Essential surjectivity is `essSurj_finiteEtaleBaseChange_of_isProper_of_henselianPair`, applied to
every scheme finite étale over `X` (each again proper over `A`); full faithfulness follows from it
by `isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`, as in the
source. -/
@[stacks 0GS2 "the full statement: any henselian pair `(A, I)` and any proper `X` over `Spec A`, \
with nothing granted or assumed", sga "4 XII 6.13" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair (A : Type u)
    [CommRing A] (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A I hI f fun P =>
    have : IsProper (P.hom ≫ f) := isProper_comp_of_finiteEtaleOver f P
    essSurj_finiteEtaleBaseChange_of_isProper_of_henselianPair A I hI (P.hom ≫ f)

end AlgebraicGeometry

end
