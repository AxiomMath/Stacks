module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationMorphism
public import StacksFrontier.RingTheory.AdicCompletion.FlatLocalSquare
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale neighbourhoods and Artin approximation, for schemes

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` and `g : Y ⟶ S` be locally of finite
type, and let `x ∈ X` and `y ∈ Y` lie over the same point `s ∈ S`. Suppose `𝒪_{S, s}` is a
G-ring and suppose given a local homomorphism `φ : 𝒪_{Y, y} → 𝒪^∧_{X, x}` over `𝒪_{S, s}`. Then
for every `N ≥ 1` there are an elementary étale neighbourhood `(U, u)` of `(X, x)` and an
`S`-morphism `F : U → Y` carrying `u` to `y` whose induced map of local rings agrees with `φ`
modulo `𝔪_u^N` after both are read in `𝒪^∧_{U, u}`. This is Stacks 37.39.1, Tag 0CAU.

## Main results

* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_approximation`: Artin
  approximation for schemes, Tag 0CAU.

## Implementation notes

*The reduction to the affine case.* The affine case is
`StacksDraft.ArtinApproximation.exists_etaleApproximation`, and the statement is local on `X`.
The reduction is: choose affine opens `W ∋ s` in `S`, `U₀ ∋ x` in `f⁻¹W` and `V₀ ∋ y` in `g⁻¹W`,
put `R = Γ(S, W)`, `A = Γ(X, U₀)`, `B = Γ(Y, V₀)` with the primes `𝔭 ⊂ A` and `𝔮 ⊂ B` of `x` and
of `y`; transport `φ` along the canonical identifications `𝒪_{X, x} ≅ A_𝔭` and `𝒪_{Y, y} ≅ B_𝔮`;
apply the affine case to get an étale `A`-algebra `A'`, a prime `𝔭'` over `𝔭` with the same
residue field and a map `B → A'`; and read `Spec A' → Spec A ≅ U₀ ↪ X` back as an elementary
étale neighbourhood of `(X, x)` and `Spec A' → Spec B ≅ V₀ ↪ Y` as the morphism to `Y`.

*The three bridges that reduction needs.* First, `𝒪_{S, s}` is a G-ring implies `𝒪_{X, x}` is
one, because the stalk map of a morphism locally of finite type is essentially of finite type
(Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`) and an algebra essentially of finite
type over a G-ring is a G-ring (Tag 07PV, `isGRing_of_essFiniteType`). Second, the ring-level
statement that the residue field does not grow has to become the scheme-level statement that
`AlgebraicGeometry.EtaleNeighborhood.residueFieldMap` is an isomorphism; this is
`spec_residueFieldMap_eq` below, built from Mathlib's comparison of the residue field of a point
of `Spec R` with `Ideal.ResidueField`. Third, the congruence has to be transported from the
completion of `A'_{𝔭'}` to the completion of `𝒪_{U, u}`, which is `completionEquiv` below: a ring
isomorphism of local rings induces one of their completions, and the induced maps on completions
are functorial, so the square of stalks over the square of charts completes to a square of
completions.

*The affine case.* It rests on Tag 0CAR,
`StacksDraft.ArtinApproximation.artinApproximationGRing`, whose input, Tag 07QZ in the form
`StacksDraft.ArtinApproximation.LocalApproximationProperty`, is
`StacksDraft.ArtinApproximation.localApproximationProperty`, deduced from
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`.

## References

* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 0CAR](https://stacks.math.columbia.edu/tag/0CAR)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-! ### Functoriality of adic completions, in the form used below -/

/-- The composition law for the maps induced on adic completions, with the hypothesis on the
composite supplied. -/
private theorem adicCompletionMap_comp' {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (h : B →+* C) (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (hg : I.map g ≤ J) (hh : J.map h ≤ K) :
    (adicCompletionMap h J K hh).comp (adicCompletionMap g I J hg) =
      adicCompletionMap (h.comp g) I K
        (by rw [← Ideal.map_map]; exact (Ideal.map_mono hg).trans hh) :=
  adicCompletionMap_comp_adicCompletionMap g h I J K hg hh _

/-- The map induced on adic completions commutes with the canonical maps from the rings. -/
private theorem adicCompletionMap_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) (J : Ideal B) (hg : I.map g ≤ J) (a : A) :
    adicCompletionMap g I J hg (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion J B) (g a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_adicCompletionMap]
  simp

/-- A ring isomorphism of local rings carries the maximal ideal into the maximal ideal. -/
private theorem map_maximalIdeal_le_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Ideal.map e.toRingHom (maximalIdeal A) ≤ maximalIdeal B := by
  have : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  exact map_maximalIdeal_le e.toRingHom

/-- The local homomorphism of localizations at two primes, one the contraction of the other,
carries the maximal ideal into the maximal ideal. -/
@[ega "IV 1.3.10" "locality of A_p → C_q"]
private theorem map_maximalIdeal_le_localRingHom {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g) :
    Ideal.map (Localization.localRingHom p q g hpq) (maximalIdeal (Localization.AtPrime p)) ≤
      maximalIdeal (Localization.AtPrime q) := by
  have := Localization.isLocalHom_localRingHom p q g hpq
  exact map_maximalIdeal_le (Localization.localRingHom p q g hpq)

/-- A ring isomorphism of local rings induces a ring isomorphism of the completions at the
maximal ideals. -/
private noncomputable def completionEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofRingHom
    (adicCompletionMap e.toRingHom _ _ (map_maximalIdeal_le_ringEquiv e))
    (adicCompletionMap e.symm.toRingHom _ _ (map_maximalIdeal_le_ringEquiv e.symm))
    (by rw [adicCompletionMap_comp']
        simpa using _root_.completionMapOfRingHom_id (maximalIdeal B) (by simp))
    (by rw [adicCompletionMap_comp']
        simpa using _root_.completionMapOfRingHom_id (maximalIdeal A) (by simp))

/-- The isomorphism of completions induced by a ring isomorphism of local rings is the map
induced by that isomorphism. -/
private theorem completionEquiv_toRingHom {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    (completionEquiv e).toRingHom =
      adicCompletionMap e.toRingHom (maximalIdeal A) (maximalIdeal B)
        (map_maximalIdeal_le_ringEquiv e) :=
  rfl

/-- The isomorphism of completions induced by a ring isomorphism of local rings commutes with
the canonical maps from the rings. -/
private theorem completionEquiv_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (a : A) :
    completionEquiv e (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (e a) :=
  adicCompletionMap_algebraMap e.toRingHom _ _ (map_maximalIdeal_le_ringEquiv e) a

/-- The comparison map of completed local rings at two primes is the map induced on adic
completions by `Localization.localRingHom`.

`StacksDraft.ArtinApproximation.completionComparison` is built from the comparison map of
`Stacks.Nagata.PthRootDescent`; this identifies it with the root-level `adicCompletionMap`, so
that the functoriality above applies to it. -/
private theorem completionComparison_eq_adicCompletionMap {A B : Type u} [CommRing A]
    [CommRing B] (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B)
    (hpq : p = q.comap g) :
    completionComparison p q g hpq =
      adicCompletionMap (Localization.localRingHom p q g hpq)
        (maximalIdeal (Localization.AtPrime p)) (maximalIdeal (Localization.AtPrime q))
        (map_maximalIdeal_le_localRingHom p q g hpq) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q g hpq).toAlgebra
  refine RingHom.ext fun z => AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_adicCompletionMap]
  exact Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion _ n z

/-! ### Residue fields of points of an affine scheme -/

attribute [local instance] PrimeSpectrum.isPrime

/-- The residue field map of `Spec f` at a point, read through Mathlib's identification of the
residue field of a point of `Spec R` with the residue field of the corresponding prime, is
`Ideal.ResidueField.map` of `f`. -/
private theorem spec_residueFieldMap_eq {R S : CommRingCat.{u}} (f : R ⟶ S) (z : Spec S) :
    ((Scheme.Spec.residueFieldIso R (Spec.map f z)).inv ≫ (Spec.map f).residueFieldMap z ≫
        (Scheme.Spec.residueFieldIso S z).hom).hom =
      (letI : z.asIdeal.IsPrime := z.isPrime
       let : (Spec.map f z).asIdeal.IsPrime := (Spec.map f z).isPrime
       Ideal.ResidueField.map (Spec.map f z).asIdeal z.asIdeal f.hom
         (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom z)) := by
  let : z.asIdeal.IsPrime := z.isPrime
  let : (Spec.map f z).asIdeal.IsPrime := (Spec.map f z).isPrime
  apply Ideal.ResidueField.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  have H := (Spec.map f).SpecMap_residueFieldMap_fromSpecResidueField z
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R (Spec.map f z),
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField S z] at H
  simp only [← Spec.map_comp, Category.assoc] at H
  have H' := Spec.map_injective H
  have H'' := congrArg
    (fun h : R ⟶ (Spec S).residueField z => h ≫ (Scheme.Spec.residueFieldIso S z).hom) H'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at H''
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using
    congrArg (fun h : R ⟶ CommRingCat.of z.asIdeal.ResidueField => h.hom r) H''

/-- The residue field map of `Spec f` at a point, transported along an equality identifying its
image, is `Ideal.ResidueField.map` of `f`. -/
theorem spec_residueFieldMap_eq_of_eq {R S : CommRingCat.{u}} (f : R ⟶ S) (z : Spec S)
    (p : PrimeSpectrum R) (hp : Spec.map f z = p)
    (hover : Ideal.comap f.hom z.asIdeal = p.asIdeal) :
    ((Scheme.Spec.residueFieldIso R p).inv ≫ (Scheme.residueFieldCongr hp).inv ≫
        (Spec.map f).residueFieldMap z ≫ (Scheme.Spec.residueFieldIso S z).hom).hom =
      (letI : p.asIdeal.IsPrime := p.isPrime
       let : z.asIdeal.IsPrime := z.isPrime
       Ideal.ResidueField.map p.asIdeal z.asIdeal f.hom hover.symm) := by
  cases hp
  simpa only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp] using
    spec_residueFieldMap_eq f z

/-! ### Germs, charts and stalks -/

/-- The section-level restriction map of a morphism, followed by the germ at a point of the
smaller open, is the germ on the base followed by the map of stalks. -/
theorem appLE_germ {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens) (V : X.Opens)
    (hVW : V ≤ f ⁻¹ᵁ W) (x : X) (hx : x ∈ V) (hs : f x ∈ W) :
    f.appLE W V hVW ≫ X.presheaf.germ V x hx =
      S.presheaf.germ W (f x) hs ≫ f.stalkMap x := by
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVW) x hx,
    Scheme.Hom.germ_stalkMap]

/-- Germs at two equal points are identified by the canonical isomorphism of their stalks. -/
private theorem germ_stalkCongr {S : Scheme.{u}} (W : S.Opens) {s₁ s₂ : S} (h : s₁ = s₂)
    (hw : s₁ ∈ W) :
    S.presheaf.germ W s₁ hw ≫ (S.presheaf.stalkCongr (.of_eq h)).hom =
      S.presheaf.germ W s₂ (h ▸ hw) := by
  cases h
  simp

/-- The germ on an affine open, followed by the stalk map of the canonical morphism
`Spec Γ(X, U) ⟶ X`, is the germ at the top on `Spec Γ(X, U)`. -/
private theorem fromSpec_germ_stalkMap {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (v : ↥(Spec Γ(X, U))) (hv : v ∈ hU.fromSpec ⁻¹ᵁ U) :
    X.presheaf.germ U (hU.fromSpec v) hv ≫ hU.fromSpec.stalkMap v =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.germ ⊤ v trivial := by
  have key : X.presheaf.germ U (hU.fromSpec v) hv ≫ hU.fromSpec.stalkMap v =
      hU.fromSpec.app U ≫ (Spec Γ(X, U)).presheaf.germ (hU.fromSpec ⁻¹ᵁ U) v hv :=
    Scheme.Hom.germ_stalkMap hU.fromSpec U v hv
  rw [key, hU.fromSpec_app_of_le U le_rfl]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  rw [TopCat.Presheaf.germ_res]

/-- The germ at the top, followed by the stalk map of `Spec f`, is the global sections map of
`Spec f` followed by the germ at the top. -/
private theorem specMap_germ {R S : CommRingCat.{u}} (f : R ⟶ S) (u : ↥(Spec S)) :
    (Spec R).presheaf.germ ⊤ (Spec.map f u) trivial ≫ (Spec.map f).stalkMap u =
      (Spec.map f).appTop ≫ (Spec S).presheaf.germ ⊤ u trivial :=
  Scheme.Hom.germ_stalkMap (Spec.map f) ⊤ u trivial

/-- Naturality of the identification of a ring with the global sections of its spectrum. -/
private theorem gammaSpecIso_inv_appTop {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The germ on an affine open `U` of `X`, followed by the stalk map of
`Spec E ⟶ Spec Γ(X, U) ≅ U ↪ X` attached to a ring map `r : Γ(X, U) → E`, is `r` followed by the
canonical map from `E` to the stalk of `Spec E` at the chosen point. This is the identity that
transports the chart description of a stalk along the morphisms built below. -/
theorem chart_germ_toSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {E : Type u} [CommRing E] (r : Γ(X, U) →+* E)
    (u : ↥(Spec (CommRingCat.of E))) (x : X) (hx : x ∈ U)
    (hw : hU.fromSpec (Spec.map (CommRingCat.ofHom r) u) = x) :
    X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫
      (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).stalkMap u =
      CommRingCat.ofHom r ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (Spec (CommRingCat.of E)).presheaf.germ ⊤ u trivial := by
  cases hw
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, Scheme.Hom.stalkMap_comp]
  rw [← Category.assoc, fromSpec_germ_stalkMap hU (Spec.map (CommRingCat.ofHom r) u) hx,
    Category.assoc, specMap_germ, ← Category.assoc, gammaSpecIso_inv_appTop, Category.assoc]

/-- Mathlib's isomorphism between the stalk of `Spec E` at a prime and the localization of `E`
there carries the canonical map from `E` to the canonical map from `E`. -/
theorem stalkIso_hom_germ {E : Type u} [CommRing E] (u : PrimeSpectrum E) (z : E) :
    (Spec.stalkIso (CommRingCat.of E) u).hom.hom
        (((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (Spec (CommRingCat.of E)).presheaf.germ ⊤ u trivial).hom z) =
      algebraMap E (Localization.AtPrime u.asIdeal) z := by
  have h := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of E) u
  have h2 := congrArg
    (fun k : CommRingCat.of E ⟶ _ => k ≫ (Spec.stalkIso (CommRingCat.of E) u).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
  exact (congrArg (fun k : CommRingCat.of E ⟶ _ => k.hom z) h2).symm

/-- The chart morphism `Spec E ⟶ Spec Γ(X, U) ≅ U ↪ X` of a ring map `r : Γ(X, U) → E`, followed by
`f`, factors through the chart of the base attached to the composite ring map. -/
private theorem spec_comp_fromSpec_comp {X S : Scheme.{u}} (f : X ⟶ S) {W : S.Opens}
    (hW : IsAffineOpen W) {U : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W)
    {E : Type u} [CommRing E] (r : Γ(X, U) →+* E) :
    Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (r.comp (f.appLE W U hUW).hom)) ≫ hW.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hW hU hUW, ← Spec.map_comp_assoc]
  rfl

/-- The map of stalks of the chart morphism `Spec E ⟶ Spec Γ(X, U) ≅ U ↪ X` of a ring map
`r : Γ(X, U) → E`, read in the localizations at the primes, is the induced map of localizations. -/
private theorem stalkMap_chart_comp_localRingHom {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {E : Type u} [CommRing E] (r : Γ(X, U) →+* E) (u : PrimeSpectrum E)
    (x : X) (hx : x ∈ U) (hw : hU.fromSpec (Spec.map (CommRingCat.ofHom r) u) = x)
    (p : Ideal Γ(X, U)) [p.IsPrime] (hp : p = u.asIdeal.comap r)
    [Algebra Γ(X, U) (X.presheaf.stalk x)] [IsLocalization.AtPrime (X.presheaf.stalk x) p]
    (halg : ∀ a, algebraMap Γ(X, U) (X.presheaf.stalk x) a = (X.presheaf.germ U x hx).hom a)
    (e : X.presheaf.stalk x ≃+* Localization.AtPrime p)
    (he : ∀ a, e ((X.presheaf.germ U x hx).hom a) = algebraMap Γ(X, U) _ a) :
    (Spec.stalkIso (CommRingCat.of E) u).commRingCatIsoToRingEquiv.toRingHom.comp
        (((X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫
          (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).stalkMap u).hom) =
      (Localization.localRingHom p u.asIdeal r hp).comp e.toRingHom := by
  refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun c => ?_)
  have h1 := congrArg (fun k : Γ(X, U) ⟶ _ => k.hom c) (chart_germ_toSpec hU r u x hx hw)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
  rw [RingHom.comp_apply, RingHom.comp_apply, halg]
  change (Spec.stalkIso (CommRingCat.of E) u).hom.hom
    (((X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫
      (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).stalkMap u).hom
        ((X.presheaf.germ U x hx).hom c)) = _
  rw [show (((X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫
        (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).stalkMap u).hom
          ((X.presheaf.germ U x hx).hom c)) =
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (Spec (CommRingCat.of E)).presheaf.germ ⊤ u trivial).hom (r c) from h1,
    stalkIso_hom_germ]
  rw [RingHom.comp_apply, RingHom.comp_apply, halg]
  change _ = Localization.localRingHom p u.asIdeal r hp (e ((X.presheaf.germ U x hx).hom c))
  rw [he, Localization.localRingHom_to_map]

/-! ### From the ring-level residue field equality to an elementary neighbourhood -/

/-- If a ring map `r : Γ(X, U) → E` induces a bijection of residue fields at a prime `𝔭'` of `E`
and its contraction, then the residue field map of `Spec E ⟶ Spec Γ(X, U) ≅ U ↪ X` at `𝔭'` is an
isomorphism. This is the step from the ring-level statement that the residue field does not grow
to the scheme-level condition defining an *elementary* étale neighbourhood. -/
theorem isIso_residueFieldMap_chart {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {E : Type u} [CommRing E] (r : Γ(X, U) →+* E) (u : PrimeSpectrum E)
    (v : PrimeSpectrum Γ(X, U)) (hv : Spec.map (CommRingCat.ofHom r) u = v)
    (hover : Ideal.comap r u.asIdeal = v.asIdeal)
    (hbij : Function.Bijective
      (letI : v.asIdeal.IsPrime := v.isPrime
       let : u.asIdeal.IsPrime := u.isPrime
       Ideal.ResidueField.map v.asIdeal u.asIdeal r hover.symm)) :
    IsIso ((Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).residueFieldMap u) := by
  let : v.asIdeal.IsPrime := v.isPrime
  let : u.asIdeal.IsPrime := u.isPrime
  have : IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map v.asIdeal u.asIdeal r hover.symm)) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  have hres : (Scheme.Spec.residueFieldIso Γ(X, U) v).inv ≫
      (Scheme.residueFieldCongr hv).inv ≫
      (Spec.map (CommRingCat.ofHom r)).residueFieldMap u ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of E) u).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map v.asIdeal u.asIdeal r hover.symm) :=
    CommRingCat.hom_ext
      (spec_residueFieldMap_eq_of_eq (CommRingCat.ofHom r) u v hv hover)
  have hfull : IsIso ((Scheme.Spec.residueFieldIso Γ(X, U) v).inv ≫
      (Scheme.residueFieldCongr hv).inv ≫
      (Spec.map (CommRingCat.ofHom r)).residueFieldMap u ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of E) u).hom) := by
    rw [hres]
    infer_instance
  have h1 : IsIso ((Scheme.residueFieldCongr hv).inv ≫
      (Spec.map (CommRingCat.ofHom r)).residueFieldMap u ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of E) u).hom) :=
    IsIso.of_isIso_comp_left (Scheme.Spec.residueFieldIso Γ(X, U) v).inv _
  have h2 : IsIso ((Spec.map (CommRingCat.ofHom r)).residueFieldMap u ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of E) u).hom) :=
    IsIso.of_isIso_comp_left (Scheme.residueFieldCongr hv).inv _
  have h3 : IsIso ((Spec.map (CommRingCat.ofHom r)).residueFieldMap u) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso (CommRingCat.of E) u).hom
  have hdecomp : (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec).residueFieldMap u =
      hU.fromSpec.residueFieldMap (Spec.map (CommRingCat.ofHom r) u) ≫
        (Spec.map (CommRingCat.ofHom r)).residueFieldMap u :=
    Scheme.residueFieldMap_comp (Spec.map (CommRingCat.ofHom r)) hU.fromSpec u
  have hOpen : ∀ w : ↥(Spec Γ(X, U)), IsIso (hU.fromSpec.residueFieldMap w) :=
    fun _ => inferInstance
  rw [hdecomp]
  exact IsIso.comp_isIso' (hOpen _) h3

/-! ### Transporting the congruence from the chart to the stalks -/

/-- A ring isomorphism of local rings carries the maximal ideal onto the maximal ideal. -/
theorem map_maximalIdeal_eq_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Ideal.map e.toRingHom (maximalIdeal A) = maximalIdeal B := by
  refine le_antisymm (map_maximalIdeal_le_ringEquiv e) fun b hb => ?_
  have h1 : e.symm b ∈ maximalIdeal A :=
    map_maximalIdeal_le_ringEquiv e.symm (Ideal.mem_map_of_mem _ hb)
  simpa using Ideal.mem_map_of_mem e.toRingHom h1

/-- The congruence produced by the affine case of the approximation, read in the completed local
rings of the schemes rather than in the completed local rings of the charts.

The data `eX`, `eU`, `eY` are the identifications of the three local rings with the localizations
of the three coordinate rings, `hA` and `hB` say that the two maps of local rings agree with the
corresponding maps of localizations, and `hagree` is the conclusion of the affine case. -/
private theorem transport_congruence {SX SU SY : Type u} [CommRing SX] [CommRing SU]
    [CommRing SY] [IsLocalRing SX] [IsLocalRing SU]
    {A B E : Type u} [CommRing A] [CommRing B] [CommRing E]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (p' : Ideal E) [p'.IsPrime]
    (g : A →+* E) (hcp : p = p'.comap g) (ψ : B →+* E) (hcq : q = p'.comap ψ)
    (eX : SX ≃+* Localization.AtPrime p) (eU : SU ≃+* Localization.AtPrime p')
    (eY : SY ≃+* Localization.AtPrime q)
    (σ : SX →+* SU) (hσ : Ideal.map σ (maximalIdeal SX) ≤ maximalIdeal SU) (τ : SY →+* SU)
    (φ : SY →+* AdicCompletion (maximalIdeal SX) SX) (N : ℕ)
    (φq : Localization.AtPrime q →+* Completion p)
    (hφq : ∀ a : SY, φq (eY a) = completionEquiv eX (φ a))
    (hA : eU.toRingHom.comp σ = (Localization.localRingHom p p' g hcp).comp eX.toRingHom)
    (hB : eU.toRingHom.comp τ = (Localization.localRingHom q p' ψ hcq).comp eY.toRingHom)
    (hagree : ∀ z : Localization.AtPrime q,
      completionComparison p p' g hcp (φq z) -
        ofLocalization p' (Localization.localRingHom q p' ψ hcq z) ∈ completionIdeal p' N)
    (a : SY) :
    adicCompletionMap σ (maximalIdeal SX) (maximalIdeal SU) hσ (φ a) -
      algebraMap SU (AdicCompletion (maximalIdeal SU) SU) (τ a) ∈
      Ideal.map (algebraMap SU (AdicCompletion (maximalIdeal SU) SU))
        (maximalIdeal SU ^ N) := by
  classical
  set θ := completionEquiv eU with hθ
  set J : Ideal (AdicCompletion (maximalIdeal SU) SU) :=
    Ideal.map (algebraMap SU (AdicCompletion (maximalIdeal SU) SU))
      (maximalIdeal SU ^ N) with hJ
  have key : θ.toRingHom.comp (adicCompletionMap σ (maximalIdeal SX) (maximalIdeal SU) hσ) =
      (completionComparison p p' g hcp).comp (completionEquiv eX).toRingHom := by
    rw [hθ, completionEquiv_toRingHom, completionEquiv_toRingHom,
      completionComparison_eq_adicCompletionMap, adicCompletionMap_comp',
      adicCompletionMap_comp']
    exact adicCompletionMap_congr _ _ _ _ hA
  have hdiff : θ (adicCompletionMap σ (maximalIdeal SX) (maximalIdeal SU) hσ (φ a) -
      algebraMap SU (AdicCompletion (maximalIdeal SU) SU) (τ a)) =
      completionComparison p p' g hcp (φq (eY a)) -
        ofLocalization p' (Localization.localRingHom q p' ψ hcq (eY a)) := by
    rw [map_sub]
    congr 1
    · have h := DFunLike.congr_fun key (φ a)
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe] at h
      rw [h, hφq a]
    · rw [hθ, completionEquiv_algebraMap]
      exact congrArg (ofLocalization p') (DFunLike.congr_fun hB a)
  have hideal : Ideal.map θ.toRingHom J = completionIdeal p' N := by
    rw [hJ, Ideal.map_map]
    have hcomp : θ.toRingHom.comp (algebraMap SU (AdicCompletion (maximalIdeal SU) SU)) =
        (ofLocalization p').comp eU.toRingHom :=
      RingHom.ext fun z => by rw [hθ]; exact completionEquiv_algebraMap eU z
    rw [hcomp, ← Ideal.map_map, Ideal.map_pow, map_maximalIdeal_eq_ringEquiv eU]
  have hmem : θ (adicCompletionMap σ (maximalIdeal SX) (maximalIdeal SU) hσ (φ a) -
      algebraMap SU (AdicCompletion (maximalIdeal SU) SU) (τ a)) ∈
      Ideal.map θ.toRingHom J := by
    rw [hideal, hdiff]
    exact hagree (eY a)
  have hcm : Ideal.comap θ.toRingHom (Ideal.map θ.toRingHom J) = J :=
    Ideal.comap_map_of_bijective θ.toRingHom θ.bijective
  rw [← hcm]
  exact hmem

/-! ### G-rings and the local rings of schemes -/

/-- A ring isomorphic to a G-ring is a G-ring. -/
private theorem isGRing_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : IsGRing A) : IsGRing B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Algebra.FiniteType A B :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective)
  exact isGRing_of_essFiniteType hA

/-- **Stacks 07PV on a scheme.** If the local ring of the base at the image of a point is a
G-ring and the morphism is locally of finite type, then the local ring at the point is a G-ring:
the stalk map is essentially of finite type. -/
private theorem isGRing_stalk {S X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hS : IsGRing (S.presheaf.stalk (f x))) : IsGRing (X.presheaf.stalk x) := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  exact isGRing_of_essFiniteType hS

/-- The map of local rings induced by the structure morphism of an étale neighbourhood, read as a
map out of the local ring at the base point, carries the maximal ideal into the maximal ideal. -/
theorem map_maximalIdeal_le_etaleNeighborhood {X : Scheme.{u}} {x : X}
    (U : EtaleNeighborhood X x) :
    Ideal.map (((X.presheaf.stalkCongr (.of_eq U.map_point.symm)).hom ≫
        U.toBase.stalkMap U.point).hom) (maximalIdeal (X.presheaf.stalk x)) ≤
      maximalIdeal (U.scheme.presheaf.stalk U.point) :=
  map_maximalIdeal_le _

/-! ### Stacks 0CAU -/

/-- **Stacks Project, Tag 0CAU (More on Morphisms, Lemma 37.39.1).** Let `S` be a locally
Noetherian scheme, let `f : X ⟶ S` and `g : Y ⟶ S` be locally of finite type, and let `x ∈ X`
and `y ∈ Y` lie over the same point `s = f x = g y` of `S`. Assume `𝒪_{S, s}` is a G-ring, and
let `φ : 𝒪_{Y, y} → 𝒪^∧_{X, x}` be a local homomorphism of `𝒪_{S, s}`-algebras. Then for every
`N ≥ 1` there are an elementary étale neighbourhood `(U, u)` of `(X, x)` and a morphism
`F : U ⟶ Y` over `S` with `F u = y` such that the square formed by `φ`, the map
`𝒪^∧_{X, x} → 𝒪^∧_{U, u}`, the map `F^♯_u : 𝒪_{Y, y} → 𝒪_{U, u}` and `𝒪_{U, u} → 𝒪^∧_{U, u}`
commutes modulo `𝔪_u^N`.

The proof reduces to the affine case
`StacksDraft.ArtinApproximation.exists_etaleApproximation`, which rests on Stacks 0CAR
`StacksDraft.ArtinApproximation.artinApproximationGRing`: it chooses affine charts, transports
`φ` to the charts, and reads `Spec A'` as an elementary étale neighbourhood of `(X, x)` with a
morphism to `Y` over `S`. -/
@[stacks 0CAU "the full scheme-level statement, with the congruence in the completed local ring \
of the neighbourhood. The hypotheses are exactly the source's own: `S` locally Noetherian, `f` \
and `g` locally of finite type, `x` and `y` over the same point, `𝒪_{S, s}` a G-ring, and the \
local `𝒪_{S, s}`-algebra map `φ : 𝒪_{Y, y} → 𝒪^∧_{X, x}`. The affine case enters through the \
unconditional Stacks 0CAR `StacksDraft.ArtinApproximation.artinApproximationGRing`. The \
source's own proof of 37.39.1 is the reduction to the affine case, and that reduction is what \
is PROVED here on top of the affine case \
`StacksDraft.ArtinApproximation.exists_etaleApproximation`: the affine charts, the chart \
descriptions of the three local rings, the elementariness of the neighbourhood from the \
ring-level residue field equality, and the transport of the congruence. The source states the \
conclusion for a diagram; here it is the single congruence that the diagram expresses."]
theorem exists_elementaryEtaleNeighborhood_approximation
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) (hxy : f x = g y)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (N : ℕ) (hN : 1 ≤ N)
    (φ : Y.presheaf.stalk y →+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hφ : IsLocalHom φ)
    (hbase : φ.comp ((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫ g.stalkMap y).hom =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (f.stalkMap x).hom) :
    ∃ U : EtaleNeighborhood X x, U.IsElementary ∧
      ∃ (F : U.scheme ⟶ Y) (hF : F U.point = y), F ≫ g = U.toBase ≫ f ∧
        ∀ a : Y.presheaf.stalk y,
          adicCompletionMap
              (((X.presheaf.stalkCongr (.of_eq U.map_point.symm)).hom ≫
                U.toBase.stalkMap U.point).hom)
              (maximalIdeal (X.presheaf.stalk x))
              (maximalIdeal (U.scheme.presheaf.stalk U.point))
              (map_maximalIdeal_le_etaleNeighborhood U) (φ a) -
            algebraMap (U.scheme.presheaf.stalk U.point)
              (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
                (U.scheme.presheaf.stalk U.point))
              (((Y.presheaf.stalkCongr (.of_eq hF.symm)).hom ≫ F.stalkMap U.point).hom a) ∈
            Ideal.map
              (algebraMap (U.scheme.presheaf.stalk U.point)
                (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
                  (U.scheme.presheaf.stalk U.point)))
              (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) := by
  classical
  have hCAR : ArtinApproximationGRing.{u} := artinApproximationGRing
  -- Affine charts around the three points.
  obtain ⟨W, hW, hsW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f x) (by simp)
  have hgW : g y ∈ W := hxy ▸ hsW
  obtain ⟨U₀, hU₀, hxU₀, hU₀sub⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := f ⁻¹ᵁ W) (x := x) hsW
  obtain ⟨V₀, hV₀, hyV₀, hV₀sub⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := g ⁻¹ᵁ W) (x := y) hgW
  have hU₀W : U₀ ≤ f ⁻¹ᵁ W := SetLike.coe_subset_coe.mp hU₀sub
  have hV₀W : V₀ ≤ g ⁻¹ᵁ W := SetLike.coe_subset_coe.mp hV₀sub
  let α : Γ(S, W) →+* Γ(X, U₀) := (f.appLE W U₀ hU₀W).hom
  let β : Γ(S, W) →+* Γ(Y, V₀) := (g.appLE W V₀ hV₀W).hom
  let : Algebra Γ(S, W) Γ(X, U₀) := α.toAlgebra
  let : Algebra Γ(S, W) Γ(Y, V₀) := β.toAlgebra
  have : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : Algebra.FiniteType Γ(S, W) Γ(X, U₀) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hW hU₀ hU₀W)
  have : Algebra.FiniteType Γ(S, W) Γ(Y, V₀) :=
    RingHom.finiteType_algebraMap.mp (g.finiteType_appLE hW hV₀ hV₀W)
  -- The chart descriptions of the three local rings.
  let pS : PrimeSpectrum Γ(X, U₀) := hU₀.primeIdealOf ⟨x, hxU₀⟩
  let qS : PrimeSpectrum Γ(Y, V₀) := hV₀.primeIdealOf ⟨y, hyV₀⟩
  have : pS.asIdeal.IsPrime := pS.isPrime
  have : qS.asIdeal.IsPrime := qS.isPrime
  let : Algebra Γ(X, U₀) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU₀⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) pS.asIdeal :=
    hU₀.isLocalization_stalk ⟨x, hxU₀⟩
  let : Algebra Γ(Y, V₀) (Y.presheaf.stalk y) :=
    Y.presheaf.algebra_section_stalk ⟨y, hyV₀⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) qS.asIdeal :=
    hV₀.isLocalization_stalk ⟨y, hyV₀⟩
  let eX := (IsLocalization.algEquiv pS.asIdeal.primeCompl (X.presheaf.stalk x)
    (Localization.AtPrime pS.asIdeal)).toRingEquiv
  let eY := (IsLocalization.algEquiv qS.asIdeal.primeCompl (Y.presheaf.stalk y)
    (Localization.AtPrime qS.asIdeal)).toRingEquiv
  have heX : ∀ a : Γ(X, U₀), eX ((X.presheaf.germ U₀ x hxU₀).hom a) =
      algebraMap Γ(X, U₀) (Localization.AtPrime pS.asIdeal) a :=
    fun a => (IsLocalization.algEquiv pS.asIdeal.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime pS.asIdeal)).commutes a
  have heY : ∀ b : Γ(Y, V₀), eY ((Y.presheaf.germ V₀ y hyV₀).hom b) =
      algebraMap Γ(Y, V₀) (Localization.AtPrime qS.asIdeal) b :=
    fun b => (IsLocalization.algEquiv qS.asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime qS.asIdeal)).commutes b
  -- The chart-level map into the completion, and the fact that it is local over the base.
  let φq : Localization.AtPrime qS.asIdeal →+* Completion pS.asIdeal :=
    (completionEquiv eX).toRingHom.comp (φ.comp eY.symm.toRingHom)
  have hlocX : IsLocalHom (completionEquiv eX).toRingHom :=
    isLocalHom_of_leftInverse (completionEquiv eX).symm (completionEquiv eX).left_inv
  have hlocY : IsLocalHom eY.symm.toRingHom := isLocalHom_of_leftInverse eY eY.right_inv
  have hφq : IsLocalHom φq :=
    ⟨fun a ha => hlocY.map_nonunit a (hφ.map_nonunit _ (hlocX.map_nonunit _ ha))⟩
  have hφqeq : ∀ a : Y.presheaf.stalk y, φq (eY a) = completionEquiv eX (φ a) := by
    intro a
    show completionEquiv eX (φ (eY.symm (eY a))) = _
    rw [eY.symm_apply_apply]
  -- The hypothesis on `φ`, read on the charts.
  have hstalks : ∀ r : Γ(S, W),
      φ ((Y.presheaf.germ V₀ y hyV₀).hom (β r)) =
        algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
          ((X.presheaf.germ U₀ x hxU₀).hom (α r)) := by
    intro r
    have hX := congrArg (fun k : Γ(S, W) ⟶ _ => k.hom r) (appLE_germ f W U₀ hU₀W x hxU₀ hsW)
    have hY := congrArg (fun k : Γ(S, W) ⟶ _ => k.hom r) (appLE_germ g W V₀ hV₀W y hyV₀ hgW)
    have hC := congrArg (fun k : Γ(S, W) ⟶ _ => k.hom r) (germ_stalkCongr (S := S) W hxy hsW)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hX hY hC
    have hb := DFunLike.congr_fun hbase ((S.presheaf.germ W (f x) hsW).hom r)
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp] at hb
    rw [hY, ← hC, hb, hX]
  have hbaseq : φq.comp ((algebraMap Γ(Y, V₀) (Localization.AtPrime qS.asIdeal)).comp
      (algebraMap Γ(S, W) Γ(Y, V₀))) =
      (toCompletion pS.asIdeal).comp (algebraMap Γ(S, W) Γ(X, U₀)) := by
    refine RingHom.ext fun r => ?_
    have hsy : eY.symm (algebraMap Γ(Y, V₀) (Localization.AtPrime qS.asIdeal) (β r)) =
        (Y.presheaf.germ V₀ y hyV₀).hom (β r) := by
      refine eY.injective ?_
      rw [eY.apply_symm_apply, heY]
    show completionEquiv eX
      (φ (eY.symm (algebraMap Γ(Y, V₀) (Localization.AtPrime qS.asIdeal) (β r)))) = _
    rw [hsy, hstalks r, completionEquiv_algebraMap, heX]
    rfl
  -- The affine case.
  have hGx : IsGRing (X.presheaf.stalk x) := isGRing_stalk f x hG
  have hGp : IsGRing (Localization.AtPrime pS.asIdeal) := isGRing_of_ringEquiv eX hGx
  have : IsNoetherianRing Γ(X, U₀) := Algebra.FiniteType.isNoetherianRing Γ(S, W) Γ(X, U₀)
  obtain ⟨Ea⟩ := exists_etaleApproximation (R := Γ(S, W)) (A := Γ(X, U₀)) (B := Γ(Y, V₀))
    hCAR pS.asIdeal qS.asIdeal hGp N hN φq hφq hbaseq
  -- The elementary étale neighbourhood and the morphism to `Y`.
  let pE : PrimeSpectrum Ea.carrier := ⟨Ea.prime, Ea.isPrime⟩
  let gE : Γ(X, U₀) →+* Ea.carrier := algebraMap Γ(X, U₀) Ea.carrier
  have : Etale (Spec.map (CommRingCat.ofHom gE)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr Ea.etale
  have hvX : Spec.map (CommRingCat.ofHom gE) pE = pS := PrimeSpectrum.ext Ea.comap_prime.symm
  have hvY : Spec.map (CommRingCat.ofHom Ea.toCarrier) pE = qS :=
    PrimeSpectrum.ext Ea.comap_toCarrier.symm
  have hUpoint : hU₀.fromSpec (Spec.map (CommRingCat.ofHom gE) pE) = x := by
    rw [hvX]; exact hU₀.fromSpec_primeIdealOf ⟨x, hxU₀⟩
  have hFpoint : hV₀.fromSpec (Spec.map (CommRingCat.ofHom Ea.toCarrier) pE) = y := by
    rw [hvY]; exact hV₀.fromSpec_primeIdealOf ⟨y, hyV₀⟩
  let Ue : EtaleNeighborhood X x :=
    ⟨Spec (CommRingCat.of Ea.carrier), pE,
      Spec.map (CommRingCat.ofHom gE) ≫ hU₀.fromSpec, hUpoint⟩
  let F : Ue.scheme ⟶ Y := Spec.map (CommRingCat.ofHom Ea.toCarrier) ≫ hV₀.fromSpec
  -- It is elementary.
  have hElementary : Ue.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_chart hU₀ gE pE pS hvX Ea.comap_prime.symm
      Ea.residueField_bijective
  -- The morphism to `Y` is a morphism over `S`.
  have hFover : F ≫ g = Ue.toBase ≫ f := by
    show (Spec.map (CommRingCat.ofHom Ea.toCarrier) ≫ hV₀.fromSpec) ≫ g =
      (Spec.map (CommRingCat.ofHom gE) ≫ hU₀.fromSpec) ≫ f
    rw [Category.assoc, Category.assoc, spec_comp_fromSpec_comp g hW hV₀ hV₀W,
      spec_comp_fromSpec_comp f hW hU₀ hU₀W]
    congr 2
    exact congrArg CommRingCat.ofHom Ea.toCarrier_base
  refine ⟨Ue, hElementary, F, hFpoint, hFover, ?_⟩
  intro a
  -- The identification of the local ring of the neighbourhood with a localization.
  let eU := (Spec.stalkIso (CommRingCat.of Ea.carrier) pE).commRingCatIsoToRingEquiv
  have hA := stalkMap_chart_comp_localRingHom hU₀ gE pE x hxU₀ hUpoint pS.asIdeal
    Ea.comap_prime (fun _ => rfl) eX heX
  have hB := stalkMap_chart_comp_localRingHom hV₀ Ea.toCarrier pE y hyV₀ hFpoint qS.asIdeal
    Ea.comap_toCarrier (fun _ => rfl) eY heY
  have hlocStalk : ∀ (Z : Scheme.{u}) (z : Z), IsLocalRing (Z.presheaf.stalk z) :=
    fun _ _ => inferInstance
  have := hlocStalk (Spec (CommRingCat.of Ea.carrier)) pE
  exact transport_congruence pS.asIdeal qS.asIdeal pE.asIdeal gE Ea.comap_prime
    Ea.toCarrier Ea.comap_toCarrier eX eU eY _ (map_maximalIdeal_le_etaleNeighborhood Ue) _
    φ N φq hφqeq hA hB Ea.agree a

end StacksDraft.ArtinApproximation

end
