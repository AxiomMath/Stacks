module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicDvrPointOfPrime
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyFiniteTypeChartMap
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveChartPoint
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.RingTheory.Rig.RigSmoothPointwiseDescent

/-!
# Descent of rig-smoothness and rig-étaleness along a rig-surjective morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GH6** says that if
`g` is locally of finite type, `f` is rig-smooth (resp. rig-étale) and rig-surjective, and
`g ∘ f` is rig-smooth (resp. rig-étale), then `g` is rig-smooth (resp. rig-étale).

## Main results

* `AlgebraicGeometry.FormalSpace.exists_chart_prime_of_isRigSurjective`: the geometric half of
  the source's proof, for any property of arrows of `WAdm^{Noeth}`.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_of_comp_of_isRigSurjective_of_isLocallyNoetherian`:
  **Stacks 0GH6**, the rig-smooth case.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isRigSurjective_of_isLocallyNoetherian`:
  **Stacks 0GH6**, the rig-étale case.

## Implementation notes

Rig-smoothness (resp. rig-étaleness) of `g` is the chart condition of Stacks 0GCQ (resp. 0GCZ):
for every affine étale chart square

```
V ⟶ W
↓     ↓
Y ⟶ Z
```

over `g` and every presentation `V ≅ Spf B`, `W ≅ Spf C` by Noetherian adic rings, the
continuous homomorphism `γ : C → B` realizing `V ⟶ W` is rig-smooth (resp. rig-étale). It is
adic and topologically of finite type because `V ⟶ W` is locally of finite type
(`finiteTypeAdicAlgebraForEveryIdeal_of_isLocallyOfFiniteType`). Following the source, fix a
prime `𝔮` of `B` off the ideal of definition. Stacks 00PH gives an adic point
`Spf R ⟶ V` out of a complete discrete valuation ring with `B → R` of kernel `𝔮`
(`exists_adic_completeDvr_point_of_isPrime`); after an extension of `R` it lifts to an affine
étale chart `Spf A ⟶ X` over `V` (`exists_affine_chart_lift_of_isRigSurjective`, through
Stacks 0AQU). The ring maps `B → A` and `C → A` of that chart are rig-smooth (resp. rig-étale)
by the chart conditions for `f` and `g ∘ f`, and the kernel of `A → R'` is a prime of `A` over
`𝔮`. The ring-theoretic half of the source's proof — the six-term sequence of Stacks 0ALM,
Stacks 0GH2, the flatness of Stacks 0GH1 and faithfully flat descent — is
`Rig.isRigSmooth_of_forall_prime_exists_rigSmooth` (resp.
`Rig.isRigEtale_of_forall_prime_exists_rigEtale`).

Of the source's hypotheses, local Noetherianity of `Y` and `Z` is not used: the presenting rings
of the charts of `Y` and `Z` are Noetherian and adic by the definition of the chart conditions.
Neither is local finite type of `f`, which Definition 0AQQ presupposes: the predicate
`IsRigSurjective` is the lifting condition alone. Both are dropped, which only generalizes the
statement.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Condition (1) of Stacks 0ANG for a property `P` of arrows descends along a commutative
square whose horizontal maps are representable étale: if `q ≫ f = p ≫ a` with `q` and `a`
representable étale, then `P` on every affine étale diagram over `f` gives `P` on every affine
étale diagram over `p`. A chart square over `p` becomes one over `f` by composing its vertical
maps with `q` and `a`, and its upper horizontal map is unchanged, so nothing is assumed of `P`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comm_of_isRepresentableEtale
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    {X' X Y' Y : FppfSheaf B S hS} (q : X' ⟶ X) (p : X' ⟶ Y') (a : Y' ⟶ Y) (f : X ⟶ Y)
    (hq : IsRepresentableEtale B S hS q) (ha : IsRepresentableEtale B S hS a)
    (hcomm : q ≫ f = p ≫ a)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P p := by
  intro U V u v t hU hV hu hv hsq
  exact hf U V (u ≫ q) (v ≫ a) t hU hV (IsRepresentableEtale.comp B S hS hu hq)
    (IsRepresentableEtale.comp B S hS hv ha)
    (by rw [Category.assoc, hcomm, ← Category.assoc, hsq, Category.assoc])

/-- **The geometric half of the proof of Stacks 0GH6.** Let `f : X ⟶ Y` be rig-surjective with
`X` locally Noetherian, `g : Y ⟶ Z`, and let `P` be a property of arrows of `WAdm^{Noeth}` holding
on every affine étale diagram over `f` and over `f ≫ g`. Let `V ⟶ W` be the map `t` of an affine
étale chart square over `g`, realized by `γ : C → B` for presentations of `V` and `W` by
Noetherian adic rings. Then every prime `𝔮` of `B` not containing an ideal of definition is the
contraction of a prime of a Noetherian adic ring `A` along a continuous homomorphism
`ψ : B → A` such that `P ψ` and `P (ψ ∘ γ)` hold. -/
theorem exists_chart_prime_of_isRigSurjective
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hfs : IsRigSurjective B S hS f)
    (hfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hgfP : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g))
    {V W : FppfSheaf B S hS} (a : V ⟶ Y) (b : W ⟶ Z) (t : V ⟶ W)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hcomm : a ≫ g = t ≫ b)
    {Rc Rb : Type u} [CommRing Rc] [TopologicalSpace Rc] [IsTopologicalRing Rc]
    [IsLinearTopology Rc Rc] [CommRing Rb] [TopologicalSpace Rb] [IsTopologicalRing Rb]
    [IsLinearTopology Rb Rb] [IsNoetherianRing Rc] [IsNoetherianRing Rb]
    (hRc : TopologicalRing.IsAdic Rc) (hRb : TopologicalRing.IsAdic Rb)
    (D : QuotientSystem B S hS Rc) (E : QuotientSystem B S hS Rb)
    (eU : V ≅ formalSpectrum E) (eV : W ≅ formalSpectrum D) (γ : ContinuousHom D E)
    (ht : t = eU.hom ≫ formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hRc) γ ≫ eV.inv)
    (q : Ideal Rb) [q.IsPrime] {J : Ideal Rb} (hJ : TopologicalRing.IsIdealOfDefinition J)
    (hqJ : ¬ J ≤ q) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
      ∃ ψ : Rb →+* A, Continuous ψ ∧ P ψ ∧ P (ψ.comp γ.toRingHom) ∧
        ∃ p : Ideal A, p.IsPrime ∧ p.comap ψ = q := by
  classical
  have hRcw := Rig.weaklyAdmissible_of_isAdicRing hRc
  have hRbw := Rig.weaklyAdmissible_of_isAdicRing hRb
  -- the adic point through `𝔮`
  obtain ⟨W₀, _, _, _, _, _, _, hW₀adic, hW₀complete, hW₀w, DW, χ, hχker, hχrep⟩ :=
    exists_adic_completeDvr_point_of_isPrime B S hS hRb E q hJ hqJ
  have hy : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hRbw χ ≫ eU.inv).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hχrep
      (isRepresentableEtale_of_isIso B S hS eU.inv).1
  -- its lift to an affine étale chart of `X` over `V`
  obtain ⟨A, _, _, _, _, _, hA, DA, c, s, hAaff, hc, hcs, R', hR'ring, hR'dom, hR'dvr, hR'alg,
    hR'ext, hR'top, hR'topring, hR'lin, hR'adic, hR'complete, D', e, ζ, he, hζ⟩ :=
    exists_affine_chart_lift_of_isRigSurjective B S hS f hX hfs a ha hW₀adic hW₀complete hW₀w DW
      (formalSpectrumMap hRbw χ ≫ eU.inv) hy
  let : CommRing R' := hR'ring
  let : IsDomain R' := hR'dom
  let : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra W₀ R' := hR'alg
  let : IsDiscreteValuationRing.IsExtension W₀ R' := hR'ext
  let : TopologicalSpace R' := hR'top
  let : IsTopologicalRing R' := hR'topring
  let : IsLinearTopology R' R' := hR'lin
  have hR'w : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  have hAw := Rig.weaklyAdmissible_of_isAdicRing hA
  -- the ring maps of the chart
  obtain ⟨ψ, hψ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hRbw hAw (s ≫ eU.hom)
  obtain ⟨χ', hχ', -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hR'w ζ
  have hs : s = (Iso.refl _).hom ≫ formalSpectrumMap hRbw ψ ≫ eU.inv := by
    rw [hψ]; simp
  have hPψ : P ψ.toRingHom :=
    hfP (formalSpectrum DA) V c a s hAaff hV hc ha hcs Rb A ⟨hRb, inferInstance⟩
      ⟨hA, inferInstance⟩ hRbw E DA (Iso.refl _) eU ψ hs
  have hst : s ≫ t = (Iso.refl _).hom ≫
      formalSpectrumMap hRcw (ContinuousHom.comp hRbw hRcw ψ γ) ≫ eV.inv := by
    rw [← formalSpectrumMap_comp_eq hRbw hRcw ψ γ, ht, hψ]
    simp
  have hPψγ : P (ContinuousHom.comp hRbw hRcw ψ γ).toRingHom :=
    hgfP (formalSpectrum DA) W c b (s ≫ t) hAaff hW hc hb
      (by rw [← Category.assoc, hcs, Category.assoc, hcomm, Category.assoc]) Rc A
      ⟨hRc, inferInstance⟩ ⟨hA, inferInstance⟩ hRcw D DA (Iso.refl _) eV _ hst
  -- the prime of `A` over `𝔮`
  have hring : χ'.toRingHom.comp ψ.toRingHom = e.toRingHom.comp χ.toRingHom := by
    have h1 := ContinuousHom.comp_toRingHom hAw hRbw χ' ψ
    have h2 := ContinuousHom.comp_toRingHom hW₀w hRbw e χ
    rw [← h1, ← h2]
    refine toRingHom_eq_of_formalSpectrumMap_eq B S hS hRbw hR'w ?_
    rw [← formalSpectrumMap_comp_eq hAw hRbw χ' ψ, ← formalSpectrumMap_comp_eq hW₀w hRbw e χ,
      hχ', hψ, ← Category.assoc, hζ, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hinj : Function.Injective e.toRingHom := by
    rw [he]; exact FaithfulSMul.algebraMap_injective W₀ R'
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA,
    ψ.toRingHom, ψ.continuous, hPψ, hPψγ, RingHom.ker χ'.toRingHom,
    RingHom.ker_isPrime _, ?_⟩
  rw [RingHom.comap_ker, hring, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj,
    ← RingHom.ker_eq_comap_bot, hχker]

/-- The chart homomorphism of an affine étale chart square over a morphism locally of finite type
is adic and topologically of finite type. -/
theorem finiteTypeAdicAlgebraForEveryIdeal_of_chartSquare {Y Z V W : FppfSheaf B S hS}
    (g : Y ⟶ Z) (hgft : IsLocallyOfFiniteType B S hS g) (a : V ⟶ Y) (b : W ⟶ Z) (t : V ⟶ W)
    (hW : IsAffineFormalAlgebraicSpace B S hS W) (ha : IsRepresentableEtale B S hS a)
    (hcomm : a ≫ g = t ≫ b)
    {Rc Rb : Type u} [CommRing Rc] [TopologicalSpace Rc] [IsTopologicalRing Rc]
    [IsLinearTopology Rc Rc] [CommRing Rb] [TopologicalSpace Rb] [IsTopologicalRing Rb]
    [IsLinearTopology Rb Rb] [IsNoetherianRing Rc] [IsNoetherianRing Rb]
    (hRc : TopologicalRing.IsAdic Rc) (hRb : TopologicalRing.IsAdic Rb)
    (D : QuotientSystem B S hS Rc) (E : QuotientSystem B S hS Rb)
    (eU : V ≅ formalSpectrum E) (eV : W ≅ formalSpectrum D) (γ : ContinuousHom D E)
    (ht : t = eU.hom ≫ formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hRc) γ ≫ eV.inv) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal γ.toRingHom := by
  have htb : IsLocallyOfFiniteType B S hS (t ≫ b) := by
    rw [← hcomm]
    exact IsLocallyOfFiniteType.comp B S hS a g
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS a ha) hgft
  have htft : IsLocallyOfFiniteType B S hS t :=
    IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t b hW htb
  have hγ : formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hRc) γ =
      eU.inv ≫ t ≫ eV.hom := by
    rw [ht]; simp
  have hLFT : IsLocallyOfFiniteType B S hS
      (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hRc) γ) := by
    rw [hγ]
    exact IsLocallyOfFiniteType.comp B S hS _ _
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _
        (isRepresentableEtale_of_isIso B S hS eU.inv))
      (IsLocallyOfFiniteType.comp B S hS _ _ htft
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _
          (isRepresentableEtale_of_isIso B S hS eV.hom)))
  exact finiteTypeAdicAlgebraForEveryIdeal_of_isLocallyOfFiniteType hRc hRb D E
    (isAffineFormalAlgebraicSpace_formalSpectrum (Rig.weaklyAdmissible_of_isAdicRing hRc) D
      (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hRc D)))
    (isAffineFormalAlgebraicSpace_formalSpectrum (Rig.weaklyAdmissible_of_isAdicRing hRb) E
      (hasLargeSite_of_mk_lt_cutoff E (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hRb E)))
    γ hLFT

/-- The argument shared by both cases of Stacks 0GH6, for a chart-defined property `IsP`. -/
private theorem isP_of_comp_of_isRigSurjective
    (IsP : ∀ {X Y : FppfSheaf B S hS}, (X ⟶ Y) → Prop)
    (Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [IsLinearTopology R₁ R₁] [IsNoetherianRing R₁] [CommRing R₂] [TopologicalSpace R₂]
      [IsTopologicalRing R₂] [IsLinearTopology R₂ R₂] [IsNoetherianRing R₂],
      (R₁ →+* R₂) → Prop)
    (hiff : ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y), IsP f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          ∀ [IsLinearTopology R₁ R₁] [IsLinearTopology R₂ R₂] [IsNoetherianRing R₁]
            [IsNoetherianRing R₂], Continuous φ ∧ Q φ) f)
    (hdesc : ∀ {C R : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
      [IsLinearTopology C C] [IsNoetherianRing C] [CommRing R] [TopologicalSpace R]
      [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R]
      (_ : TopologicalRing.IsAdic C) (_ : TopologicalRing.IsAdic R) (φ : C →+* R)
      (_ : Continuous φ) (_ : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ),
      (∀ I : Ideal C, TopologicalRing.IsIdealOfDefinition I → ∀ q : Ideal R, q.IsPrime →
        ¬ I.map φ ≤ q →
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
          (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
          ∃ ψ : R →+* A, Continuous ψ ∧ Q ψ ∧ Q (ψ.comp φ) ∧
            ∃ p : Ideal A, p.IsPrime ∧ p.comap ψ = q) → Q φ)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hgft : IsLocallyOfFiniteType B S hS g) (hf : IsP f) (hfs : IsRigSurjective B S hS f)
    (hgf : IsP (f ≫ g)) : IsP g := by
  have hfP := (hiff f).mp hf
  have hgfP := (hiff (f ≫ g)).mp hgf
  refine (hiff g).mpr ?_
  intro V W a b t hV hW ha hb hcomm Rc Rb _ _ _ _ _ _ _ _ hRcC hRbC hRcw D E eU eV γ ht
  have := hRcC.2
  have := hRbC.2
  have ht' : t = eU.hom ≫ formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hRcC.1) γ ≫
      eV.inv := ht
  have hft := finiteTypeAdicAlgebraForEveryIdeal_of_chartSquare B S hS g hgft a b t hW ha hcomm
    hRcC.1 hRbC.1 D E eU eV γ ht'
  intro _ _ _ _
  refine ⟨γ.continuous, hdesc hRcC.1 hRbC.1 γ.toRingHom γ.continuous hft fun I hI q _ hq ↦ ?_⟩
  obtain ⟨A, _, _, _, _, _, hA, ψ, hψ, hPψ, hPψγ, p, hp, hpq⟩ :=
    exists_chart_prime_of_isRigSurjective B S hS _ f g hX hfs hfP hgfP a b t hV hW ha hb hcomm
      hRcC.1 hRbC.1 D E eU eV γ ht' q (Rig.isIdealOfDefinition_of_isAdic (hft I hI).1) hq
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA, ψ, hψ,
    hPψ.2, hPψγ.2, p, hp, hpq⟩

/-- **Stacks 0GH6**, the rig-smooth case. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of formal
algebraic spaces over `S` with `X` locally Noetherian. If `g` is locally of finite type, `f` is
rig-smooth and rig-surjective, and `g ∘ f` is rig-smooth, then `g` is rig-smooth.

The source also assumes `Y` and `Z` locally Noetherian and `f` locally of finite type; none of
these is used, see the module documentation. -/
@[stacks 0GH6 "the rig-smooth case"]
theorem isRigSmooth_of_comp_of_isRigSurjective_of_isLocallyNoetherian
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hgft : IsLocallyOfFiniteType B S hS g) (hf : IsRigSmooth B S hS f)
    (hfs : IsRigSurjective B S hS f) (hgf : IsRigSmooth B S hS (f ≫ g)) :
    IsRigSmooth B S hS g :=
  isP_of_comp_of_isRigSurjective B S hS (IsRigSmooth B S hS) @RingHom.IsRigSmooth
    (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS)
    Rig.isRigSmooth_of_forall_prime_exists_rigSmooth f g hX hgft hf hfs hgf

/-- **Stacks 0GH6**, the rig-étale case. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of formal
algebraic spaces over `S` with `X` locally Noetherian. If `g` is locally of finite type, `f` is
rig-étale and rig-surjective, and `g ∘ f` is rig-étale, then `g` is rig-étale.

The source also assumes `Y` and `Z` locally Noetherian and `f` locally of finite type; none of
these is used, see the module documentation. -/
@[stacks 0GH6 "the rig-étale case"]
theorem isRigEtale_of_comp_of_isRigSurjective_of_isLocallyNoetherian
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hgft : IsLocallyOfFiniteType B S hS g) (hf : IsRigEtale B S hS f)
    (hfs : IsRigSurjective B S hS f) (hgf : IsRigEtale B S hS (f ≫ g)) :
    IsRigEtale B S hS g :=
  isP_of_comp_of_isRigSurjective B S hS (IsRigEtale B S hS) @RingHom.IsRigEtale
    (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS)
    Rig.isRigEtale_of_forall_prime_exists_rigEtale f g hX hgft hf hfs hgf

end AlgebraicGeometry.FormalSpace

end
