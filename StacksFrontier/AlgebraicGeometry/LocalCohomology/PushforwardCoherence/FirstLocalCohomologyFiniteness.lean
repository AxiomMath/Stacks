module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.SectionsFiniteness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeReflexiveRank
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the first local cohomology module

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `M` a finite `A`-module.
[Stacks, Tag 0BL9] characterises finiteness of `H¹_Z(M)`: it holds exactly when, for every
associated prime `𝔭` of `M` with `𝔭 ∉ Z` and every `𝔮 ∈ V(𝔭 + I)`, the completion of
`(A/𝔭)_𝔮` has no associated prime of dimension `1`.

This file proves everything that equivalence needs apart from Kollár's criterion,
[Stacks, Tag 0BK3]; the tag itself is
`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one` in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyKollar`,
which is downstream of the criterion — see the implementation notes.

The two halves of the argument are the finiteness chain and the translation.

* **The finiteness chain.** `H¹_Z(M)` is a finite `A`-module exactly when `Γ(U, M̃|_U)` is, by
  the four-term sequence of [Stacks, Tag 0BK0]
  (`Stacks.LocalCohomology.finite_complementGlobalSections_iff_finite_localCohomologyModule`),
  and that happens exactly when the direct image of `M̃|_U` along `U ⟶ Spec A` is coherent, by
  the degree-zero clause of the same tag
  (`Stacks.LocalCohomology.isCoherent_pushforward_iff_module_finite_sections`). This is
  `Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_isCoherent_pushforward`.
* **The translation.** The geometric condition of [Stacks, Tag 0BK3] is imposed at the points of
  the reduced closure of an associated point of `M̃|_U`. Over an affine base that closure is
  `Spec (A ⧸ 𝔭)` and its local rings are the localizations `(A/𝔭)_𝔮`, so the condition becomes
  the condition of [Stacks, Tag 0BL9] at the primes `𝔮 ⊇ 𝔭 + I`, once `2 ≤ dim` is traded for
  `dim ≠ 1`. The trade is legitimate because `1 ≤ dim` holds automatically: `𝔭 ∉ Z` provides an
  element of `I` outside `𝔭`, which is a nonzerodivisor in the maximal ideal of `(A/𝔭)_𝔮`, and a
  nonzerodivisor in the maximal ideal keeps every associated prime of the completion away from
  the maximal ideal.

## Main definitions

* `Stacks.LocalCohomology.adicCompletionRingEquivCongr`: a ring equivalence `R ≃+* S` induces
  `AdicCompletion I R ≃+* AdicCompletion (I.map e) S`.
* `Stacks.LocalCohomology.subschemeIsoSpecQuotient`: for an ideal sheaf `W` on `Spec A` whose
  ideal of global sections is the image of `J ⊆ A`, an isomorphism of `Spec (A ⧸ J)` with the
  closed subscheme `Z(W)`.
* `Stacks.LocalCohomology.pointClosureIso`: its case `J = 𝔭`, `W` the vanishing ideal of the
  closure of a prime `𝔭` — an isomorphism of `Spec (A ⧸ 𝔭)` with the reduced closure of `𝔭`.

## Main results

* `Stacks.LocalCohomology.subschemeIsoSpecQuotient_hom_comp_subschemeι`: that isomorphism
  commutes with the two closed immersions into `Spec A`, which is what makes it usable for
  transporting sheaves. `Stacks.LocalCohomology.pointClosureIso_hom_comp_subschemeι` is its
  case at the closure of a prime.
* `Stacks.LocalCohomology.isAssociatedPoint_tilde_iff`: a point of `Spec A` is an associated
  point of `M̃` exactly when the corresponding prime is an associated prime of `M`.
* `Stacks.LocalCohomology.subschemeι_pointClosureIso_hom`: the isomorphism `pointClosureIso`
  commutes with the two maps to `Spec A`, on points.
* `Stacks.LocalCohomology.forall_adicCompletion_pointClosure_iff_forall_quotientPrime`: the
  condition of [Stacks, Tag 0BK3] at the points of the reduced closure of `𝔭` outside `U`,
  rewritten as a condition on the completions of `(A/𝔭)_𝔮` for `𝔮 ∈ V(𝔭 + I)`.
* `Stacks.LocalCohomology.one_le_ringKrullDim_quotient_adicCompletion_localization`: for
  `𝔭 ∉ V(I)` and `𝔮 ∈ V(𝔭 + I)`, every associated prime of the completion of `(A/𝔭)_𝔮` has
  quotient of dimension at least one — the inequality that turns `2 ≤ dim` into `dim ≠ 1`.
* `Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_isCoherent_pushforward`: `H¹_Z(M)`
  is a finite `A`-module exactly when the direct image of `M̃|_U` along `U ⟶ Spec A` is coherent.
* `Stacks.LocalCohomology.isCoherent_pushforward_complementTilde_iff_forall_two_le_ringKrullDim`:
  Kollár's criterion at this open immersion and this module, from [Stacks, Tag 0BJZ] and
  [Stacks, Tag 0BK1].

## Implementation notes

[Stacks, Tag 0BL9] itself is stated downstream, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyKollar`,
and not here. Kollár's criterion is
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`, which rests on
[Stacks, Tag 0BK1], and the module proving that tag imports this one, for the identification of
the reduced closure of a point of an affine scheme with the spectrum of the quotient
(`Stacks.LocalCohomology.pointClosureIso`). So the
criterion cannot be applied in this file, and the tag is stated where it can be.

Associated primes are taken in the Stacks Project's sense (`IsAssociatedPrimeStacks`, the
annihilator of a single element), which is the spelling [Stacks, Tag 0BK3] is stated in; over a
Noetherian ring it agrees with Mathlib's `associatedPrimes`.

The local ring `(A/𝔭)_𝔮` is spelled `Localization.AtPrime (𝔮.map (Ideal.Quotient.mk 𝔭))` and its
completion is taken at the image of that prime in the localization, which is its maximal ideal.
The dimension of an associated prime of the completion is the Krull dimension of the
corresponding quotient, an element of `WithBot ℕ∞`; `dim ≠ 1` is the source's "does not have
associated primes of dimension 1".

## References

* [Stacks Project, Tag 0BL9](https://stacks.math.columbia.edu/tag/0BL9)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.CodimensionOneObstruction
  (isAssociatedPoint_restrict_iff isAssociatedPrimeStacks_iff_of_semilinear)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### The reduced closure of a point of an affine scheme -/

/-- The prime of `Γ(Spec A, ⊤)` corresponding to a point of `Spec A` is the image of that point's
prime under `A ≃ Γ(Spec A, ⊤)`. -/
theorem primeIdealOf_top_eq_map (A : Type u) [CommRing A] (x : PrimeSpectrum A) :
    ((isAffineOpen_top (Spec (CommRingCat.of A))).primeIdealOf ⟨x, trivial⟩).asIdeal =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) x.asIdeal := by
  classical
  set X := Spec (CommRingCat.of A)
  let hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let y := hU.primeIdealOf ⟨x, trivial⟩
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  have hy : y = PrimeSpectrum.comap (e.symm : Γ(X, ⊤) →+* A) x := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [hU.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    have hcomp : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id A :=
      congrArg CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id)
    have hx : PrimeSpectrum.comap
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) x = x := by
      rw [hcomp]
      simp
    exact hx.symm.trans (PrimeSpectrum.comap_comp_apply
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x)
  show y.asIdeal = Ideal.map (e : A →+* Γ(X, ⊤)) x.asIdeal
  ext s
  rw [hy, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.mem_map_iff_of_surjective (e : A →+* Γ(X, ⊤)) e.surjective]
  refine ⟨fun hs => ⟨e.symm s, hs, e.apply_symm_apply s⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  simpa using ha

/-- A closed subscheme of an affine scheme cut out by an ideal sheaf is the spectrum of the
quotient of the global sections by the ideal on the whole space.

The affine cover of the closed subscheme attached to the affine open `⊤` has that spectrum as its
source, and it is an open immersion whose range is everything, hence an isomorphism. -/
def subschemeIsoSpecTop (X : Scheme.{u}) [IsAffine X] (W : Scheme.IdealSheafData X) :
    Spec (CommRingCat.of (Γ(X, ⊤) ⧸ W.ideal ⟨⊤, isAffineOpen_top X⟩)) ≅ W.subscheme := by
  classical
  let htop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let f := W.subschemeCover.f htop
  have : IsOpenImmersion f := W.subschemeCover.map_prop htop
  have hf : f.opensRange = ⊤ := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
    ext z
    simp [htop]
  exact @asIso _ _ _ _ f (AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top f hf)

/-- **The closed subscheme cut out by an ideal sheaf on `Spec A` is `Spec` of a quotient of `A`.**
For an ideal sheaf `W` on `Spec A` whose ideal of global sections is the image of `J ⊆ A` under
`A ≃ Γ(Spec A, ⊤)`, the quotient `A ⧸ J` is the quotient of `Γ(Spec A, ⊤)` by that ideal. -/
def subschemeQuotientEquiv (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).IdealSheafData) (J : Ideal A)
    (hW : W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) J) :
    (A ⧸ J) ≃+*
      (Γ(Spec (CommRingCat.of A), ⊤) ⧸
        W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) :=
  Ideal.quotientEquiv J (W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩)
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm hW

/-- **`Z(W) ≅ Spec (A ⧸ J)`** for an ideal sheaf `W` on `Spec A` cut out by `J ⊆ A`: the closed
subscheme of an ideal sheaf on an affine scheme is the spectrum of the quotient by its ideal of
global sections. -/
def subschemeIsoSpecQuotient (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).IdealSheafData) (J : Ideal A)
    (hW : W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) J) :
    Spec (CommRingCat.of (A ⧸ J)) ≅ W.subscheme :=
  (Scheme.Spec.mapIso (subschemeQuotientEquiv A W J hW).toCommRingCatIso.symm.op) ≪≫
    subschemeIsoSpecTop (Spec (CommRingCat.of A)) _

/-- **`subschemeIsoSpecQuotient` is compatible with the two closed immersions into `Spec A`**:
composing it with the inclusion of the closed subscheme gives `Spec` of the quotient map
`A ⟶ A ⧸ J`.

This is what makes the identification of `Z(W)` with `Spec (A ⧸ J)` usable: without it the two
closed immersions into `Spec A` are only known to have isomorphic sources, and no sheaf on
`Spec A` can be transported along the isomorphism. -/
theorem subschemeIsoSpecQuotient_hom_comp_subschemeι (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).IdealSheafData) (J : Ideal A)
    (hW : W.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) J) :
    (subschemeIsoSpecQuotient A W J hW).hom ≫ W.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  let V : (Spec (CommRingCat.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  -- The cover map of the closed subscheme attached to `⊤`, composed with the closed immersion,
  -- is `Spec` of the quotient map followed by the identification of `Spec Γ(X, ⊤)` with `X`.
  have step : W.subschemeCover.f V ≫ W.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal V))) ≫
        (isAffineOpen_top (Spec (CommRingCat.of A))).fromSpec :=
    (W.subschemeCover_map_subschemeι V).trans (W.glueDataObjι_ι V)
  -- With that identification the composite is `Spec` of a single ring map, which is the
  -- quotient map of `J` because `subschemeQuotientEquiv` sends `a` to the class of `a / 1`.
  have tail : Spec.map (subschemeQuotientEquiv A W J hW).toCommRingCatIso.inv ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.ideal V))) ≫
          (isAffineOpen_top (Spec (CommRingCat.of A))).fromSpec) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    show (subschemeQuotientEquiv A W J hW).symm
      (Ideal.Quotient.mk (W.ideal V) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
        Ideal.Quotient.mk J a
    apply (subschemeQuotientEquiv A W J hW).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Ideal.quotientEquiv_mk J (W.ideal V)
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm _ a).symm
  show Spec.map (subschemeQuotientEquiv A W J hW).toCommRingCatIso.inv ≫
    (W.subschemeCover.f V ≫ W.subschemeι) = _
  exact (congrArg (Spec.map (subschemeQuotientEquiv A W J hW).toCommRingCatIso.inv ≫ ·) step).trans
    tail

/-- On the whole of an affine scheme, the ideal cut out by the reduced closure of a point `𝔭` is
the image of `𝔭` under `A ≃ Γ(Spec A, ⊤)`. -/
theorem ideal_vanishingIdeal_closure_top (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm :
        A →+* Γ(Spec (CommRingCat.of A), ⊤)) p.asIdeal :=
  (Stacks.Divisors.ideal_vanishingIdeal_closure_singleton
      (X := Spec (CommRingCat.of A)) p ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
      (isAffineOpen_top (Spec (CommRingCat.of A))) trivial).trans
    (primeIdealOf_top_eq_map A p)

/-- For a prime `𝔭` of `A`, the quotient `A ⧸ 𝔭` is the quotient of `Γ(Spec A, ⊤)` by the
vanishing ideal of the closure of `𝔭`, along `A ≃ Γ(Spec A, ⊤)`. -/
def pointClosureQuotientEquiv (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    (A ⧸ p.asIdeal) ≃+*
      (Γ(Spec (CommRingCat.of A), ⊤) ⧸
        (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).ideal
          ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) :=
  subschemeQuotientEquiv A _ p.asIdeal (ideal_vanishingIdeal_closure_top A p)

/-- **The reduced closure of a point of an affine scheme is the spectrum of the quotient.** For a
prime `𝔭` of `A`, the closed subscheme of `Spec A` cut out by the vanishing ideal of the closure
of `𝔭` is `Spec (A ⧸ 𝔭)`. -/
def pointClosureIso (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    Spec (CommRingCat.of (A ⧸ p.asIdeal)) ≅
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).subscheme :=
  subschemeIsoSpecQuotient A _ p.asIdeal (ideal_vanishingIdeal_closure_top A p)

/-- `pointClosureIso` is compatible with the two maps to `Spec A`: composing it with the closed
immersion of the reduced closure gives `Spec` of the quotient map. -/
theorem pointClosureIso_hom_comp_subschemeι (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    (pointClosureIso A p).hom ≫
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal)) :=
  subschemeIsoSpecQuotient_hom_comp_subschemeι A _ p.asIdeal
    (ideal_vanishingIdeal_closure_top A p)

/-- On points, `pointClosureIso` followed by the closed immersion of the reduced closure of `𝔭`
is the map `Spec (A ⧸ 𝔭) → Spec A`, that is, contraction along `A → A ⧸ 𝔭`. -/
theorem subschemeι_pointClosureIso_hom (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (z : PrimeSpectrum (A ⧸ p.asIdeal)) :
    (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).subschemeι.base
        ((pointClosureIso A p).hom.base z) =
      PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) z :=
  congrArg (fun f : Spec (CommRingCat.of (A ⧸ p.asIdeal)) ⟶ Spec (CommRingCat.of A) => f.base z)
    (pointClosureIso_hom_comp_subschemeι A p)

/-! ### Adic completion along a ring equivalence -/

/-- **A ring equivalence induces an equivalence of adic completions.** For `e : R ≃+* S` and an
ideal `I` of `R`, completing `R` at `I` and `S` at `I.map e` give isomorphic rings.

Mathlib's `AdicCompletion.congr` varies the module over a fixed ring and ideal; this varies the
ring. It is built level by level from the quotient equivalences `R ⧸ Iⁿ ≃+* S ⧸ (I.map e)ⁿ`,
which are compatible with the transition maps of the two inverse systems. -/
def adicCompletionRingEquivCongr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) : AdicCompletion I R ≃+* AdicCompletion (I.map e) S := by
  classical
  let q (n : ℕ) : (R ⧸ I ^ n • ⊤ : Type _) ≃+* (S ⧸ (I.map e) ^ n • ⊤ : Type _) :=
    Ideal.quotientEquiv (I ^ n • ⊤) ((I.map e) ^ n • ⊤) e (by
      simp only [Ideal.smul_eq_mul, Ideal.mul_top]
      exact (Ideal.map_pow (e : R →+* S) I n).symm)
  have q_mk (n : ℕ) (r : R) :
      q n (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r) =
        Ideal.Quotient.mk ((I.map e) ^ n • ⊤ : Ideal S) (e r) :=
    Ideal.quotientEquiv_mk _ _ _ _ r
  have hcompat (m n : ℕ) (hmn : m ≤ n) (z : R ⧸ I ^ n • ⊤) :
      q m (AdicCompletion.transitionMap I R hmn z) =
        AdicCompletion.transitionMap (I.map e) S hmn (q n z) := by
    refine Quotient.inductionOn z fun r => ?_
    change q m (AdicCompletion.transitionMap I R hmn
        (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r)) =
      AdicCompletion.transitionMap (I.map e) S hmn
        (q n (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r))
    rw [AdicCompletion.transitionMap_ideal_mk, q_mk, q_mk, AdicCompletion.transitionMap_ideal_mk]
  let toMap (x : AdicCompletion I R) : AdicCompletion (I.map e) S :=
    ⟨fun n => q n (x.1 n), by
      intro m n hmn
      change AdicCompletion.transitionMap (I.map e) S hmn (q n (x.1 n)) = q m (x.1 m)
      rw [← x.2 hmn]
      exact (hcompat m n hmn (x.1 n)).symm⟩
  let invMap (y : AdicCompletion (I.map e) S) : AdicCompletion I R :=
    ⟨fun n => (q n).symm (y.1 n), by
      intro m n hmn
      change AdicCompletion.transitionMap I R hmn ((q n).symm (y.1 n)) = (q m).symm (y.1 m)
      apply (q m).injective
      rw [hcompat]
      simpa using y.2 hmn⟩
  exact
    { toFun := toMap, invFun := invMap
      left_inv := fun x => AdicCompletion.ext fun n => (q n).symm_apply_apply (x.1 n)
      right_inv := fun y => AdicCompletion.ext fun n => (q n).apply_symm_apply (y.1 n)
      map_mul' := fun x y => AdicCompletion.ext fun n => map_mul (q n) (x.1 n) (y.1 n)
      map_add' := fun x y => AdicCompletion.ext fun n => map_add (q n) (x.1 n) (y.1 n) }

/-- A property of the dimensions of the associated quotients of a ring transfers along a ring
equivalence. -/
theorem forall_associatedPrime_ringKrullDim_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (f : R ≃+* S) (P : WithBot ℕ∞ → Prop)
    (h : ∀ r : Ideal S, IsAssociatedPrimeStacks S S r → P (ringKrullDim (S ⧸ r))) :
    ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → P (ringKrullDim (R ⧸ r)) := by
  intro r hr
  have hd := h (r.map f)
    (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPrimeStacks_map_ringEquiv f hr)
  rwa [← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv r (r.map f) f rfl)] at hd

/-- A property of the dimensions of the associated quotients of the completion of a local ring at
its maximal ideal depends only on the isomorphism class of that local ring. -/
theorem forall_associatedPrime_ringKrullDim_adicCompletion_congr {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (P : WithBot ℕ∞ → Prop) :
    (∀ r : Ideal (AdicCompletion (maximalIdeal A) A),
        IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
          (AdicCompletion (maximalIdeal A) A) r →
        P (ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ r))) ↔
      ∀ r : Ideal (AdicCompletion (maximalIdeal B) B),
        IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal B) B)
          (AdicCompletion (maximalIdeal B) B) r →
        P (ringKrullDim (AdicCompletion (maximalIdeal B) B ⧸ r)) := by
  have e' : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B := by
    have h := adicCompletionRingEquivCongr e (maximalIdeal A)
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal e] at h
  exact ⟨forall_associatedPrime_ringKrullDim_of_ringEquiv e'.symm P,
    forall_associatedPrime_ringKrullDim_of_ringEquiv e' P⟩

/-! ### The criterion at a point closure, read on the quotient -/

/-- **The condition of [Stacks, Tag 0BK3] at a point closure of an affine scheme, read on the
quotient.** For a prime `𝔭` of `A` and a property `P` of Krull dimensions, imposing `P` on the
dimensions of the associated quotients of the completed local rings of the reduced closure of
`𝔭` at the points lying over `V(I)` is the same as imposing it on the completions of
`(A/𝔭)_𝔷` for the primes `𝔷` of `A ⧸ 𝔭` whose contraction contains `I`.

The reduced closure is `Spec (A ⧸ 𝔭)` by `pointClosureIso`, its local rings are therefore the
localizations of `A ⧸ 𝔭`, and `forall_associatedPrime_ringKrullDim_adicCompletion_congr`
transports the condition across those identifications. -/
theorem forall_adicCompletion_pointClosure_iff (A : Type u) [CommRing A] (I : Ideal A)
    (p : PrimeSpectrum A) (P : WithBot ℕ∞ → Prop) :
    (let W := Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))
     ∀ w : W.subscheme, I ≤ (W.subschemeι.base w).asIdeal →
       let B := W.subscheme.presheaf.stalk w
       let R := AdicCompletion (maximalIdeal B) B
       ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → P (ringKrullDim (R ⧸ r))) ↔
    (∀ z : PrimeSpectrum (A ⧸ p.asIdeal),
      I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) z).asIdeal →
      let B := Localization.AtPrime z.asIdeal
      let R := AdicCompletion (maximalIdeal B) B
      ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → P (ringKrullDim (R ⧸ r))) := by
  dsimp only
  let e := pointClosureIso A p
  have he (z : PrimeSpectrum (A ⧸ p.asIdeal)) :
      (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({p} : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk
            (e.hom.base z) ≃+* Localization.AtPrime z.asIdeal :=
    have := ((AlgebraicGeometry.isIso_iff_isIso_stalkMap e.hom).mp e.isIso_hom).2 z
    ((asIso (e.hom.stalkMap z)) ≪≫
      Spec.stalkIso (CommRingCat.of (A ⧸ p.asIdeal)) z).commRingCatIsoToRingEquiv
  refine ⟨fun h z hz => ?_, fun h w hw => ?_⟩
  · exact (forall_associatedPrime_ringKrullDim_adicCompletion_congr (he z) P).mp
      (h (e.hom.base z) (by rwa [subschemeι_pointClosureIso_hom A p z]))
  · obtain ⟨z, rfl⟩ := e.hom.surjective w
    exact (forall_associatedPrime_ringKrullDim_adicCompletion_congr (he z) P).mpr
      (h z (by rwa [← subschemeι_pointClosureIso_hom A p z]))

/-- Completing a localization at a prime `J` along the image of `J` is completing at its maximal
ideal. -/
private theorem forall_adicCompletion_map_iff {R : Type*} [CommRing R] (J : Ideal R) [J.IsPrime]
    (P : WithBot ℕ∞ → Prop) :
    (∀ r : Ideal (AdicCompletion (maximalIdeal (Localization.AtPrime J))
        (Localization.AtPrime J)), IsAssociatedPrimeStacks _
          (AdicCompletion (maximalIdeal (Localization.AtPrime J)) (Localization.AtPrime J)) r →
        P (ringKrullDim (_ ⧸ r))) ↔
      ∀ r : Ideal (AdicCompletion (J.map (algebraMap R (Localization.AtPrime J)))
        (Localization.AtPrime J)), IsAssociatedPrimeStacks _
          (AdicCompletion (J.map (algebraMap R (Localization.AtPrime J)))
            (Localization.AtPrime J)) r → P (ringKrullDim (_ ⧸ r)) := by
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal J (Localization.AtPrime J)]

/-- **Reindexing the criterion by the primes of `A` above `𝔭 + I`.** For ideals `I` and `𝔭` of `A`
with `𝔭` prime, a condition imposed at every prime `𝔷` of `A ⧸ 𝔭` whose contraction contains `I`
is the same as the condition imposed at every prime `𝔮` of `A` with `𝔭 ⊆ 𝔮` and `I ⊆ 𝔮`, the
local ring being `A ⧸ 𝔭` localized at the image of `𝔮`. -/
theorem forall_quotientPrime_iff (A : Type u) [CommRing A] (I p : Ideal A)
    (P : WithBot ℕ∞ → Prop) :
    (∀ z : PrimeSpectrum (A ⧸ p),
      I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p) z).asIdeal →
      let B := Localization.AtPrime z.asIdeal
      let R := AdicCompletion (maximalIdeal B) B
      ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → P (ringKrullDim (R ⧸ r))) ↔
    (∀ (q : PrimeSpectrum A) (hpq : p ≤ q.asIdeal) (_hq : I ≤ q.asIdeal),
      let J := q.asIdeal.map (Ideal.Quotient.mk p)
      letI : J.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
      let B := Localization.AtPrime J
      let R := AdicCompletion (J.map (algebraMap (A ⧸ p) B)) B
      ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → P (ringKrullDim (R ⧸ r))) := by
  refine ⟨fun h q hpq hq => ?_, fun h z hz => ?_⟩
  · have : (q.asIdeal.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    exact (forall_adicCompletion_map_iff _ P).mp
      (h ⟨_, this⟩ (by simpa only [PrimeSpectrum.comap, Ideal.comap_map_mk hpq] using hq))
  · let q := PrimeSpectrum.comap (Ideal.Quotient.mk p) z
    have hpq : p ≤ q.asIdeal := fun a ha => by
      show Ideal.Quotient.mk p a ∈ z.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact z.asIdeal.zero_mem
    have heq : q.asIdeal.map (Ideal.Quotient.mk p) = z.asIdeal :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    have : (q.asIdeal.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    have hz' : z = ⟨q.asIdeal.map (Ideal.Quotient.mk p), this⟩ := PrimeSpectrum.ext heq.symm
    rw [hz']
    exact (forall_adicCompletion_map_iff _ P).mpr (h q hpq hz)

/-! ### A nonzerodivisor in the maximal ideal forces dimension at least one -/

/-- **A nonzerodivisor in the maximal ideal keeps the associated primes of the completion off the
maximal ideal.** If `a` is a nonzerodivisor in the maximal ideal of a Noetherian local ring `A`,
then every prime associated to the completion `Â` has `1 ≤ dim(Â/𝔯)`.

Were `𝔯` the maximal ideal of `Â`, the element it annihilates would be killed by the image of
`a`, which is a nonzerodivisor on `Â` because `Â` is flat over `A`. So `𝔯` is a non-maximal
prime, and a ring with a non-maximal prime has positive Krull dimension. -/
theorem one_le_ringKrullDim_quotient_adicCompletion_of_isSMulRegular (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (a : A) (ha : IsSMulRegular A a)
    (ham : a ∈ maximalIdeal A) (r : Ideal (AdicCompletion (maximalIdeal A) A))
    (hr : IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A) r) :
    1 ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ r) := by
  let B := AdicCompletion (maximalIdeal A) A
  have hprime : r.IsPrime := hr.1
  have hnotmax : ¬ r.IsMaximal := by
    intro hmax
    obtain ⟨-, b, hb⟩ := hr
    have hb0 : b ≠ 0 := by
      intro hz
      have h1 : (1 : B) ∈ r := by
        rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot, hz, smul_zero]
      exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    have hab : a • b = 0 := by
      have ha' : algebraMap A B a ∈ r := by
        rw [IsLocalRing.eq_maximalIdeal hmax, AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem _ ham
      rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot] at ha'
      simpa only [smul_eq_mul, Algebra.smul_def] using ha'
    exact hb0 ((ha.of_flat (S := B)) (by simpa [Algebra.smul_def] using hab))
  have hpos : 0 < ringKrullDim (B ⧸ r) := by
    by_contra h
    have : Ring.KrullDimLE 0 (B ⧸ r) := Ring.krullDimLE_iff.mpr (not_lt.mp h)
    exact hnotmax ((Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp
      this) r (by simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]))
  exact_mod_cast ENat.WithBot.add_one_le_iff.mpr hpos

/-- **Dimension at least one at the completions of [Stacks, Tag 0BL9].** Let `A` be Noetherian,
`I` an ideal, `𝔭` a prime with `I ⊄ 𝔭`, and `𝔷` a prime of `A ⧸ 𝔭` whose contraction to `A`
contains `I`. Then every prime associated to the completion of `(A/𝔭)_𝔷` has quotient of
dimension at least one.

An element of `I` outside `𝔭` is nonzero in the domain `A ⧸ 𝔭`, hence a nonzerodivisor in its
localization at `𝔷`, and it lies in the maximal ideal there because `I ⊆ 𝔷` pulled back. So
`one_le_ringKrullDim_quotient_adicCompletion_of_isSMulRegular` applies.

This is what lets the bound `2 ≤ dim` of [Stacks, Tag 0BK3] be traded for the condition
`dim ≠ 1` of [Stacks, Tag 0BL9]. -/
theorem one_le_ringKrullDim_quotient_adicCompletion_localization (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (p : PrimeSpectrum A) (hpI : ¬ I ≤ p.asIdeal)
    (z : PrimeSpectrum (A ⧸ p.asIdeal))
    (hz : I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) z).asIdeal)
    (r : Ideal (AdicCompletion (maximalIdeal (Localization.AtPrime z.asIdeal))
      (Localization.AtPrime z.asIdeal)))
    (hr : IsAssociatedPrimeStacks _
      (AdicCompletion (maximalIdeal (Localization.AtPrime z.asIdeal))
        (Localization.AtPrime z.asIdeal)) r) :
    1 ≤ ringKrullDim (AdicCompletion (maximalIdeal (Localization.AtPrime z.asIdeal))
      (Localization.AtPrime z.asIdeal) ⧸ r) := by
  obtain ⟨a, haI, hap⟩ := SetLike.not_le_iff_exists.mp hpI
  let B := Localization.AtPrime z.asIdeal
  let b := Ideal.Quotient.mk p.asIdeal a
  have hbl : algebraMap (A ⧸ p.asIdeal) B b ≠ 0 := fun h =>
    hap <| Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsLocalization.injective B z.asIdeal.primeCompl_le_nonZeroDivisors)
        (h.trans (map_zero _).symm))
  exact one_le_ringKrullDim_quotient_adicCompletion_of_isSMulRegular B _
    (IsSMulRegular.of_ne_zero hbl)
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff B z.asIdeal b).mpr (hz haI)) r hr

/-! ### Associated points of the sheaf associated to a module -/

/-- **The associated points of `M̃` are the associated primes of `M`.** For a finite-free-free
Noetherian ring `A` and an `A`-module `M`, a point of `Spec A` is an associated point of the
quasi-coherent sheaf `M̃` exactly when the corresponding prime is associated to `M` in the Stacks
Project's sense.

This is the affine comparison of [Stacks, Tag 02OK] at the open `⊤`, together with the
identification of `Γ(M̃, ⊤)` with `M` as a module over `Γ(Spec A, ⊤) ≃ A`. -/
@[ega "IV 3.1.2"]
theorem isAssociatedPoint_tilde_iff (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) (p : PrimeSpectrum A) :
    Stacks.Divisors.IsAssociatedPoint
        ((tilde.functor (CommRingCat.of A)).obj M) p ↔
      IsAssociatedPrimeStacks A M p.asIdeal := by
  let X := Spec (CommRingCat.of A)
  let G := (tilde.functor (CommRingCat.of A)).obj M
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  let f : M ≃+ Γ(G, ⊤) := (tilde.isoTop (R := CommRingCat.of A) M).toLinearEquiv.toAddEquiv
  have hf : ∀ r m, f (r • m) = e r • f m := by
    intro r m
    show (tilde.isoTop (R := CommRingCat.of A) M).hom (r • m) = _
    rw [map_smul]
    exact Scheme.Modules.smul_Spec_def r (f m)
  have h := isAssociatedPrimeStacks_iff_of_semilinear e f hf (p := p.asIdeal)
  change IsAssociatedPrimeStacks A M p.asIdeal ↔
    IsAssociatedPrimeStacks Γ(X, ⊤) Γ(G, ⊤) (p.asIdeal.map e) at h
  have heq : ((isAffineOpen_top X).primeIdealOf ⟨p, trivial⟩).asIdeal =
      p.asIdeal.map (e : A →+* Γ(X, ⊤)) := primeIdealOf_top_eq_map A p
  rw [Ideal.map_coe] at heq
  rw [← heq] at h
  exact (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
    G ⊤ (isAffineOpen_top X) trivial).symm.trans h.symm

/-! ### Finiteness of `H¹_Z(M)` as coherence of a direct image -/

/-- The degree-zero clause of [Stacks, Tag 0BK0] in the spelling the low-degree sequence uses:
over a Noetherian base the direct image of a coherent module on `U = Spec A \ V(I)` is coherent
exactly when its sections over `U` are a finite module.

This is `Stacks.LocalCohomology.isCoherent_pushforward_iff_module_finite_sections` with the two
descriptions of those sections — `Γ(j_*F, ⊤)` over `Γ(Spec A, ⊤) ≃ A` and
`complementGlobalSections` — identified. The ring is kept bundled so that the module structure on
`Γ(j_*F, ⊤)` is the one Mathlib's instance provides. -/
theorem isCoherent_pushforward_iff_finite_complementGlobalSections (R : CommRingCat.{u})
    [IsNoetherianRing R] (I : Ideal (ToType R))
    (F : (complementZeroLocus (ToType R) I : Scheme).Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward (complementZeroLocus (ToType R) I).ι).obj F).IsCoherent ↔
      Module.Finite (ToType R) (complementGlobalSections (ToType R) I F) :=
  isCoherent_pushforward_iff_module_finite_sections R _ F

/-- The sheaf `M̃|_U` on `U = Spec A \ V(I)` is coherent when `M` is a finite module over a
Noetherian ring. -/
theorem isCoherent_complementTilde (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] : (complementTilde A I M).IsCoherent :=
  have : ((tilde.functor (CommRingCat.of A)).obj M).IsCoherent :=
    AlgebraicGeometry.tilde_isCoherent_of_finite (R := CommRingCat.of A) M
  Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion
    (complementZeroLocus A I).ι ((tilde.functor (CommRingCat.of A)).obj M)

/-- **Finiteness of `H¹_Z(M)` is coherence of the direct image.** For a finite module `M` over a
Noetherian ring `A` and `U = Spec A \ V(I)`, the module `H¹_{V(I)}(M)` is a finite `A`-module
exactly when the direct image of `M̃|_U` along `U ⟶ Spec A` is coherent.

This is the composite of the two clauses of [Stacks, Tag 0BK0] the library has in degree zero:
finiteness of `H¹_{V(I)}(M)` is finiteness of `Γ(U, M̃|_U)` by the four-term sequence
(`finite_complementGlobalSections_iff_finite_localCohomologyModule`), and that is coherence of
the direct image (`isCoherent_pushforward_iff_finite_complementGlobalSections`). -/
theorem finite_localCohomologyModule_one_iff_isCoherent_pushforward (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite A (localCohomologyModule A I I.fg_of_isNoetherianRing M 1) ↔
      ((Scheme.Modules.pushforward (complementZeroLocus A I).ι).obj
        (complementTilde A I M)).IsCoherent := by
  have : (complementTilde A I M).IsCoherent := isCoherent_complementTilde A I M
  exact (finite_complementGlobalSections_iff_finite_localCohomologyModule A I
    I.fg_of_isNoetherianRing M (complementTilde A I M) (Iso.refl _)).symm.trans
    (isCoherent_pushforward_iff_finite_complementGlobalSections
      (CommRingCat.of A) I (complementTilde A I M)).symm

/-! ### Kollár's criterion at `U = Spec A \ V(I)` and `M̃|_U` -/

/-- **[Stacks, Tag 0BK3] at `U = Spec A \ V(I)` and `M̃|_U`, from [Stacks, Tag 0BJZ] and
[Stacks, Tag 0BK1].** This is
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure`
instantiated at the one open immersion and the one coherent module
`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one` needs
it at, so it records that the criterion there is exactly what [Stacks, Tag 0BJZ] and
[Stacks, Tag 0BK1] provide, with no gap between the two spellings.

The two hypotheses are [Stacks, Tag 0BJZ] at this open immersion and this module, and
[Stacks, Tag 0BK1] in full generality. -/
theorem isCoherent_pushforward_complementTilde_iff_forall_two_le_ringKrullDim (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hBJZ : ((Scheme.Modules.pushforward (complementZeroLocus A I).ι).obj
          (complementTilde A I M)).IsCoherent ↔
      ∀ x : (complementZeroLocus A I : Scheme),
        x ∈ Stacks.Divisors.associatedPoints (complementTilde A I M) →
        ((Scheme.Modules.pushforward ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure
                ({x} : Set (complementZeroLocus A I : Scheme)))).subschemeι ≫
            (complementZeroLocus A I).ι)).obj
          (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure
              ({x} : Set (complementZeroLocus A I : Scheme)))).subscheme.ringCatSheaf)).IsCoherent)
    (hBK1 : ∀ (W Z : Scheme.{u}) (j' : W ⟶ Z), IsOpenImmersion j' → IsIntegral Z →
      IsLocallyNoetherian Z → Nonempty W →
      (∀ z : Z, z ∉ Set.range j'.base →
        ∀ q : Ideal (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)),
          IsAssociatedPrimeStacks
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) q →
          (2 : WithBot ℕ∞) ≤ ringKrullDim
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z) ⧸ q)) →
      ((Scheme.Modules.pushforward j').obj
        (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward (complementZeroLocus A I).ι).obj
        (complementTilde A I M)).IsCoherent ↔
    ∀ x : (complementZeroLocus A I : Scheme),
      x ∈ Stacks.Divisors.associatedPoints (complementTilde A I M) →
      ∀ w : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          ({(complementZeroLocus A I).ι.base x} : Set (Spec (CommRingCat.of A))))).subscheme,
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            ({(complementZeroLocus A I).ι.base x}
              : Set (Spec (CommRingCat.of A))))).subschemeι.base w ∉
          Set.range (complementZeroLocus A I).ι.base →
        ∀ r : Ideal (AdicCompletion (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({(complementZeroLocus A I).ι.base x}
                : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w))
            ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
              ({(complementZeroLocus A I).ι.base x}
                : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w)),
          IsAssociatedPrimeStacks _ (AdicCompletion
              (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
                ({(complementZeroLocus A I).ι.base x}
                  : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
                ({(complementZeroLocus A I).ι.base x}
                  : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w)) r →
            (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
              (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
                ({(complementZeroLocus A I).ι.base x}
                  : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w))
              ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
                ({(complementZeroLocus A I).ι.base x}
                  : Set (Spec (CommRingCat.of A))))).subscheme.presheaf.stalk w) ⧸ r) := by
  have : (complementTilde A I M).IsCoherent := isCoherent_complementTilde A I M
  have : IsLocallyNoetherian (complementZeroLocus A I : Scheme) :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion (complementZeroLocus A I).ι
  exact isCoherent_pushforward_iff_forall_two_le_ringKrullDim_of_pointClosure
    (complementZeroLocus A I).ι (complementTilde A I M) hBJZ hBK1

end Stacks.LocalCohomology

end
