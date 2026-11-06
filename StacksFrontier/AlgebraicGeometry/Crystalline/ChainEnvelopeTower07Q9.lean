module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChainEnvelope07Q9

/-!
# The completed envelope of a chain presentation as an iterated `p`-th root extension

Let `C = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n` be a chain of `α_p`-extensions and `P → C` a surjective polynomial
presentation with `p`-adically completed divided power envelope `D_0`.  This file proves that the
completed envelope `D'` of the presentation `P[z_1, …, z_n] → R_n` (with `z_i` going to the
`i`-th root) is, as a divided power ring, the last stage `D_n` of a tower

`D_0 ⟶ D_1 ⟶ ⋯ ⟶ D_n`,   `D_{k+1} = (D_k[z]⟨ξ⟩/(ξ - (z^p - λ_k)))^∧`

of the extensions of [Stacks, Tag 07N1], compatibly with the maps out of `D_0`; this is the
identification on which the proof of [Stacks, Tag 07Q9] applies Lemma 07N1 once per stage.
Each `λ_k` is a lift to `D_k` of the constant of the `k`-th stage of the chain.

The one-stage identification is `Crystalline.alphaPCompletedEnvelopeIso`.  To iterate it the
construction `B ↦ (B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧` is made functorial for divided power isomorphisms
(`Crystalline.completedPrimeStepIso07Q9`), through the universal properties of `B⟨ξ⟩`
([Stacks, Tag 07H6]), of `AdjoinRoot` and of the `p`-adic completion.

## Main definitions

* `Crystalline.completedPrimeStep07Q9` — `(B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧` with its completed divided
  powers; it is `Crystalline.alphaPCompletedPrimeDPRing` for `B` a completed envelope, and the ring
  `Crystalline.PthRootExtension.completedPrimeDPRing` of the 07N1 development, both by definition.
* `Crystalline.PrimeTower07Q9` — a tower `D_0 ⟶ D_1 ⟶ ⋯ ⟶ D_n` of such extensions, with
  `Crystalline.PrimeTower07Q9.top` its last ring and `Crystalline.PrimeTower07Q9.toTop` the
  composite of its structure maps.
* `Crystalline.GlobalCrystallineSituation.SmallSite.chainTower07Q9` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.chainTowerIso07Q9` — the tower over `D(0)` and
  the isomorphism `D'(0) ≅ D_n` for the chain presentation of `Γ(f⁻¹(W))`.

## Main results

* `Crystalline.exists_chainTower07Q9` — the identification for an arbitrary chain.
* `Crystalline.GlobalCrystallineSituation.SmallSite.chainTowerIso07Q9_hom_completedEnvelopeMap` —
  the isomorphism composed with `D(0) → D'(0)` is the composite of the structure maps of the
  tower.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
-/

@[expose] public section

noncomputable section

open DividedPowers CategoryTheory

universe u v w

namespace Crystalline

open PthRootExtension MvPolynomial

/-! ### Functoriality of `B ↦ B[z]⟨ξ⟩/(ξ - (z^p - λ))` -/

section PrimeFunctoriality

variable {B : DividedPowerRing.{u}} (p : ℕ) (hp : p ≠ 0) {lam : (B : Type u)}

/-- The divided power inclusion `B⟨ξ⟩ → B[z]⟨ξ⟩/(ξ - (z^p - λ))`. -/
def xiToPrimeDP07Q9 :
    DPMorphism (xiDPRing B).dividedPowers (primeDividedPowers B p lam hp) :=
  (DPMorphism.mk' (isDPMorphism_relationQuotientMk B p lam hp)).comp
    (DPMorphism.mk' (isDPMorphism_C_polynomialDividedPowerRing (xiDPRing B)))

/-- **Divided power morphisms out of `B[z]⟨ξ⟩/(ξ - (z^p - λ))` are determined by their values on
`B` and on `z`**: the universal property of `B⟨ξ⟩` ([Stacks, Tag 07H6]), the image of `ξ` being
`z^p - λ`, and that of `AdjoinRoot`. -/
theorem primeDP_ext07Q9 {T : DividedPowerRing.{u}}
    (q₁ q₂ : DPMorphism (primeDividedPowers B p lam hp) T.dividedPowers)
    (hb : ∀ b, q₁ (algebraMap (B : Type u) (primeRing B p lam) b) =
      q₂ (algebraMap (B : Type u) (primeRing B p lam) b))
    (hz : q₁ (zElt B p lam) = q₂ (zElt B p lam)) : q₁ = q₂ := by
  have hcoeff : ∀ (q : DPMorphism (primeDividedPowers B p lam hp) T.dividedPowers) (b : B),
      (q.comp (xiToPrimeDP07Q9 p hp))
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit b) =
        q (algebraMap (B : Type u) (primeRing B p lam) b) := by
    intro q b
    rw [IsScalarTower.algebraMap_apply (B : Type u) (XiAlg B) (primeRing B p lam),
      AdjoinRoot.algebraMap_eq]
    rfl
  have hxi : ∀ q : DPMorphism (primeDividedPowers B p lam hp) T.dividedPowers,
      (q.comp (xiToPrimeDP07Q9 p hp)) (dividedPowerPolynomialVariable (B : Type u) ()) =
        q (xiElt B p lam 1 0) := by
    intro q
    rw [xiElt_one_zero_eq_mk]
    rfl
  have hmem : q₁ (xiElt B p lam 1 0) ∈ T.ideal :=
    q₁.ideal_comp (Ideal.mem_map_of_mem _ (xiElt_one_zero_mem B p lam hp))
  have hU := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B Unit T
    ((q₁.comp (xiToPrimeDP07Q9 p hp)).comp
      (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit))
    (fun _ => ⟨q₁ (xiElt B p lam 1 0), hmem⟩)
  have h2 : (q₂.comp (xiToPrimeDP07Q9 p hp)).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit) =
      (q₁.comp (xiToPrimeDP07Q9 p hp)).comp
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit) ∧
      ∀ i : Unit, (q₂.comp (xiToPrimeDP07Q9 p hp)) (dividedPowerPolynomialVariable _ i) =
        q₁ (xiElt B p lam 1 0) := by
    refine ⟨?_, fun _ => ?_⟩
    · apply DPMorphism.ext
      funext b
      show (q₂.comp (xiToPrimeDP07Q9 p hp))
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit b) =
        (q₁.comp (xiToPrimeDP07Q9 p hp))
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit b)
      rw [hcoeff, hcoeff, hb]
    · rw [hxi, xiElt_one_zero_eq]
      have e₁ := map_sub q₁.toRingHom (zElt B p lam ^ p)
        (algebraMap (B : Type u) (primeRing B p lam) lam)
      have e₂ := map_sub q₂.toRingHom (zElt B p lam ^ p)
        (algebraMap (B : Type u) (primeRing B p lam) lam)
      have f₁ := map_pow q₁.toRingHom (zElt B p lam) p
      have f₂ := map_pow q₂.toRingHom (zElt B p lam) p
      simp only [DPMorphism.toRingHom_apply] at e₁ e₂ f₁ f₂
      rw [e₁, e₂, f₁, f₂, hz, hb]
  have heq := hU.unique h2 ⟨rfl, fun _ => hxi q₁⟩
  apply DPMorphism.ext
  have hR : q₂.toRingHom = q₁.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro y
      exact congrArg (fun q : DPMorphism _ _ => q y) heq
    · exact hz.symm
  exact congrArg (fun f : _ →+* _ => (f : _ → _)) hR.symm

variable {B' : DividedPowerRing.{u}} {lam' : (B' : Type u)}
  (θ : DPMorphism B.dividedPowers B'.dividedPowers) (hθ : θ lam = lam')

/-- The divided power morphism `B⟨ξ⟩ → B'[z]⟨ξ⟩/(ξ - (z^p - λ'))` extending `θ` and sending `ξ`
to `ξ`. -/
def xiPrimeMap07Q9 :
    DPMorphism (xiDPRing B).dividedPowers (primeDividedPowers B' p lam' hp) :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B Unit (primeDPRing B' p lam' hp)
    ((alphaPAlgebraMapDP B' p lam' hp).comp θ)
    (fun _ => ⟨xiElt B' p lam' 1 0, xiElt_one_zero_mem B' p lam' hp⟩)).exists.choose

/-- The defining property of `Crystalline.xiPrimeMap07Q9`. -/
theorem xiPrimeMap07Q9_spec :
    (xiPrimeMap07Q9 p hp θ).comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism B Unit) =
        (alphaPAlgebraMapDP B' p lam' hp).comp θ ∧
      ∀ i : Unit, xiPrimeMap07Q9 p hp θ (dividedPowerPolynomialVariable _ i) =
        xiElt B' p lam' 1 0 :=
  (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B Unit (primeDPRing B' p lam' hp)
    ((alphaPAlgebraMapDP B' p lam' hp).comp θ)
    (fun _ => ⟨xiElt B' p lam' 1 0, xiElt_one_zero_mem B' p lam' hp⟩)).exists.choose_spec

/-- `Crystalline.xiPrimeMap07Q9` extends `θ`. -/
theorem xiPrimeMap07Q9_algebraMap (b : (B : Type u)) :
    xiPrimeMap07Q9 p hp θ (algebraMap (B : Type u) (XiAlg B) b) =
      algebraMap (B' : Type u) (primeRing B' p lam') (θ b) :=
  congrArg (fun q : DPMorphism _ _ => q b) (xiPrimeMap07Q9_spec p hp θ).1

include hθ in
/-- The relation `z^p - ξ - λ` holds for `z` and `ξ` in `B'[z]⟨ξ⟩/(ξ - (z^p - λ'))`. -/
theorem xiPrimeMap07Q9_eval₂_primePoly :
    (primePoly B p lam).eval₂ (xiPrimeMap07Q9 p hp θ).toRingHom (zElt B' p lam') = 0 := by
  rw [primePoly_eq B p lam, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
    map_add]
  show _ - (xiPrimeMap07Q9 p hp θ (xi B) + xiPrimeMap07Q9 p hp θ (algebraMap _ _ lam)) = 0
  rw [xi, (xiPrimeMap07Q9_spec p hp θ).2, xiPrimeMap07Q9_algebraMap, hθ, xiElt_one_zero_eq]
  ring

/-- **The ring map `B[z]⟨ξ⟩/(ξ - (z^p - λ)) → B'[z]⟨ξ⟩/(ξ - (z^p - λ'))`** induced by a divided
power morphism `θ : B → B'` with `θ(λ) = λ'`, sending `z` to `z` and `ξ` to `ξ`. -/
def primeMap07Q9 : primeRing B p lam →+* primeRing B' p lam' :=
  AdjoinRoot.lift (xiPrimeMap07Q9 p hp θ).toRingHom (zElt B' p lam')
    (xiPrimeMap07Q9_eval₂_primePoly p hp θ hθ)

/-- The induced map sends `z` to `z`. -/
theorem primeMap07Q9_zElt : primeMap07Q9 p hp θ hθ (zElt B p lam) = zElt B' p lam' :=
  AdjoinRoot.lift_root _

/-- The induced map extends `θ`. -/
theorem primeMap07Q9_algebraMap (b : (B : Type u)) :
    primeMap07Q9 p hp θ hθ (algebraMap (B : Type u) (primeRing B p lam) b) =
      algebraMap (B' : Type u) (primeRing B' p lam') (θ b) := by
  rw [IsScalarTower.algebraMap_apply (B : Type u) (XiAlg B) (primeRing B p lam),
    AdjoinRoot.algebraMap_eq, primeMap07Q9, AdjoinRoot.lift_of]
  exact xiPrimeMap07Q9_algebraMap p hp θ b

/-- The induced map is a divided power morphism. -/
theorem primeMap07Q9_isDPMorphism :
    IsDPMorphism (primeDividedPowers B p lam hp) (primeDividedPowers B' p lam' hp)
      (primeMap07Q9 p hp θ hθ) := by
  have h0 : IsDPMorphism (zPolyDPRing B).dividedPowers (primeDividedPowers B' p lam' hp)
      (Polynomial.eval₂RingHom (xiPrimeMap07Q9 p hp θ).toRingHom (zElt B' p lam')) :=
    IsDPMorphism.of_comp (hI := (xiDPRing B).dividedPowers)
      (hJ := (zPolyDPRing B).dividedPowers) (hK := primeDividedPowers B' p lam' hp)
      Polynomial.C _ rfl (isDPMorphism_C_polynomialDividedPowerRing _)
      (by
        convert (xiPrimeMap07Q9 p hp θ).isDPMorphism using 1
        exact RingHom.ext fun x => Polynomial.eval₂_C _ _)
  refine IsDPMorphism.of_comp (hI := (zPolyDPRing B).dividedPowers)
    (hJ := primeDividedPowers B p lam hp) (hK := primeDividedPowers B' p lam' hp)
    (relationQuotientMk B p lam) _ rfl (isDPMorphism_relationQuotientMk B p lam hp) ?_
  convert h0 using 1
  exact RingHom.ext fun x =>
    AdjoinRoot.lift_mk (xiPrimeMap07Q9_eval₂_primePoly p hp θ hθ) x

/-- The induced map as a divided power morphism. -/
def primeMapDP07Q9 :
    DPMorphism (primeDividedPowers B p lam hp) (primeDividedPowers B' p lam' hp) :=
  DPMorphism.mk' (primeMap07Q9_isDPMorphism p hp θ hθ)

/-- **The induced maps of an inverse pair are inverse**: if `θ' ∘ θ = id`, the composite of the
induced maps is the identity. -/
theorem primeMapDP07Q9_comp (θ' : DPMorphism B'.dividedPowers B.dividedPowers)
    (hθ' : θ' lam' = lam) (h : ∀ b, θ' (θ b) = b) :
    (primeMapDP07Q9 p hp θ' hθ').comp (primeMapDP07Q9 p hp θ hθ) = DPMorphism.id _ := by
  refine primeDP_ext07Q9 (T := primeDPRing B p lam hp) p hp _ _ (fun b => ?_) ?_
  · show primeMap07Q9 p hp θ' hθ' (primeMap07Q9 p hp θ hθ (algebraMap _ _ b)) = _
    rw [primeMap07Q9_algebraMap, primeMap07Q9_algebraMap, h]
    rfl
  · show primeMap07Q9 p hp θ' hθ' (primeMap07Q9 p hp θ hθ (zElt _ p lam)) = _
    rw [primeMap07Q9_zElt, primeMap07Q9_zElt]
    rfl

end PrimeFunctoriality

/-! ### The completed extension and its functoriality -/

section CompletedStep

variable (B : DividedPowerRing.{u}) (p : ℕ) (hp : p ≠ 0)
  (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) (lam : (B : Type u))

/-- **The ring `D' = (B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧` of [Stacks, Tag 07N1]**, with the completed
divided powers of [Stacks, Tag 07KD].  For `B` a completed envelope it is
`Crystalline.alphaPCompletedPrimeDPRing`, and it is the ring
`Crystalline.PthRootExtension.completedPrimeDPRing B p lam hp hB` of the 07N1 development: both
are this `Crystalline.pAdicCompletedDPRing` by definition. -/
abbrev completedPrimeStep07Q9 : DividedPowerRing.{u} :=
  pAdicCompletedDPRing (primeDPRing B p lam hp) p (alphaP_isNilpotent_mk_primeIdeal B p lam hp hB)

/-- `p` is nilpotent modulo the divided power ideal of the completed extension. -/
theorem completedPrimeStep07Q9_isNilpotent :
    IsNilpotent (Ideal.Quotient.mk (completedPrimeStep07Q9 B p hp hB lam).ideal
      ((p : ℕ) : (completedPrimeStep07Q9 B p hp hB lam : Type u))) :=
  isNilpotent_mk_completionIdeal _ p _

/-- **The structure map `B → D'`**, the structure map of the extension followed by the completion
map, as a divided power morphism. -/
def completedPrimeStepι07Q9 : B ⟶ completedPrimeStep07Q9 B p hp hB lam :=
  (completionDPMorphism _ _ p (alphaP_isNilpotent_mk_primeIdeal B p lam hp hB)).comp
    (alphaPAlgebraMapDP B p lam hp)

/-- The structure map `B → D'` on elements. -/
theorem completedPrimeStepι07Q9_apply (b : (B : Type u)) :
    completedPrimeStepι07Q9 B p hp hB lam b =
      AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p lam) b) :=
  rfl

variable {B} {B' : DividedPowerRing.{u}}
  (hB' : IsNilpotent (Ideal.Quotient.mk B'.ideal ((p : ℕ) : (B' : Type u)))) {lam}
  {lam' : (B' : Type u)} (θ : DPMorphism B.dividedPowers B'.dividedPowers) (hθ : θ lam = lam')

/-- **The map of completed extensions** induced by a divided power morphism `θ` with
`θ(λ) = λ'`: the completion of `Crystalline.primeMapDP07Q9`. -/
def completedPrimeStepMap07Q9 :
    completedPrimeStep07Q9 B p hp hB lam ⟶ completedPrimeStep07Q9 B' p hp hB' lam' :=
  DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ p _ _ (primeMapDP07Q9 p hp θ hθ))

/-- The map of completed extensions is compatible with the structure maps. -/
theorem completedPrimeStepMap07Q9_ι (b : (B : Type u)) :
    completedPrimeStepMap07Q9 p hp hB hB' θ hθ (completedPrimeStepι07Q9 B p hp hB lam b) =
      completedPrimeStepι07Q9 B' p hp hB' lam' (θ b) := by
  rw [completedPrimeStepι07Q9_apply, completedPrimeStepι07Q9_apply]
  exact (adicCompletionRingMap_of _ _ _).trans
    (congrArg (AdicCompletion.of _ _) (primeMap07Q9_algebraMap p hp θ hθ b))

include hθ in
/-- The composite of the maps of completed extensions of an inverse pair is the identity. -/
theorem completedPrimeStepMap07Q9_comp (θ' : DPMorphism B'.dividedPowers B.dividedPowers)
    (hθ' : θ' lam' = lam) (h : ∀ b, θ' (θ b) = b) :
    completedPrimeStepMap07Q9 p hp hB hB' θ hθ ≫ completedPrimeStepMap07Q9 p hp hB' hB θ' hθ' =
      𝟙 _ := by
  apply DPMorphism.ext
  funext x
  have hc := RingHom.congr_fun (adicCompletionRingMap_comp p
    (primeMapDP07Q9 p hp θ hθ).toRingHom (primeMapDP07Q9 p hp θ' hθ').toRingHom) x
  have hi := congrArg (fun q : DPMorphism _ _ =>
    adicCompletionRingMap q.toRingHom (map_pAdicIdeal_le p q.toRingHom) x)
    (primeMapDP07Q9_comp p hp θ hθ θ' hθ' h)
  exact hc.symm.trans (hi.trans (RingHom.congr_fun (adicCompletionRingMap_id p) x))

/-- **The completed extension is functorial for divided power isomorphisms**: an isomorphism
`Θ : B ≅ B'` with `Θ(λ) = λ'` induces an isomorphism of the completed extensions. -/
def completedPrimeStepIso07Q9 (Θ : B ≅ B') (hθ : Θ.hom lam = lam') :
    completedPrimeStep07Q9 B p hp hB lam ≅ completedPrimeStep07Q9 B' p hp hB' lam' where
  hom := completedPrimeStepMap07Q9 p hp hB hB' Θ.hom hθ
  inv := completedPrimeStepMap07Q9 p hp hB' hB Θ.inv (by
    rw [← hθ]
    exact congrArg (fun q : B ⟶ B => q lam) Θ.hom_inv_id)
  hom_inv_id := completedPrimeStepMap07Q9_comp p hp hB hB' _ hθ _ _
    (fun b => congrArg (fun q : B ⟶ B => q b) Θ.hom_inv_id)
  inv_hom_id := completedPrimeStepMap07Q9_comp p hp hB' hB _ _ _ hθ
    (fun b => congrArg (fun q : B' ⟶ B' => q b) Θ.inv_hom_id)

/-- The isomorphism of completed extensions is compatible with the structure maps. -/
theorem completedPrimeStepIso07Q9_hom_ι (Θ : B ≅ B') (hθ : Θ.hom lam = lam') (b : (B : Type u)) :
    (completedPrimeStepIso07Q9 p hp hB hB' Θ hθ).hom (completedPrimeStepι07Q9 B p hp hB lam b) =
      completedPrimeStepι07Q9 B' p hp hB' lam' (Θ.hom b) :=
  completedPrimeStepMap07Q9_ι p hp hB hB' Θ.hom hθ b

end CompletedStep

/-! ### Towers of completed extensions -/

/-- **A tower `D_0 ⟶ D_1 ⟶ ⋯ ⟶ D_n` of completed extensions of [Stacks, Tag 07N1]**: over a
divided power ring `D_0 = B`, each stage is `D_{k+1} = (D_k[z]⟨ξ⟩/(ξ - (z^p - λ_k)))^∧` for an
element `λ_k ∈ D_k`, `p` being nonzero and nilpotent modulo the divided power ideal of `D_k`.
`cons hp hB λ rest` is the tower whose first stage is the extension by `λ`, followed by
`rest`. -/
inductive PrimeTower07Q9 (p : ℕ) : DividedPowerRing.{u} → ℕ → Type (u + 1)
  /-- The tower of length `0`. -/
  | nil (B : DividedPowerRing.{u}) : PrimeTower07Q9 p B 0
  /-- The tower whose first stage is the completed extension by `λ`. -/
  | cons {B : DividedPowerRing.{u}} {n : ℕ} (hp : p ≠ 0)
      (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
      (lam : (B : Type u))
      (rest : PrimeTower07Q9 p (completedPrimeStep07Q9 B p hp hB lam) n) :
      PrimeTower07Q9 p B (n + 1)

namespace PrimeTower07Q9

variable {p : ℕ}

/-- The last ring `D_n` of a tower. -/
def top : {B : DividedPowerRing.{u}} → {n : ℕ} → PrimeTower07Q9 p B n → DividedPowerRing.{u}
  | B, _, nil _ => B
  | _, _, cons _ _ _ rest => rest.top

/-- The composite `D_0 ⟶ D_n` of the structure maps of a tower. -/
def toTop : {B : DividedPowerRing.{u}} → {n : ℕ} → (T : PrimeTower07Q9 p B n) → (B ⟶ T.top)
  | B, _, nil _ => 𝟙 B
  | B, _, cons hp hB lam rest => completedPrimeStepι07Q9 B p hp hB lam ≫ rest.toTop

/-- The last ring of the tower of length `0` is its base. -/
@[simp]
theorem top_nil (B : DividedPowerRing.{u}) : (nil (p := p) B).top = B :=
  rfl

/-- The last ring of a tower is that of the rest of the tower. -/
@[simp]
theorem top_cons {B : DividedPowerRing.{u}} {n : ℕ} (hp : p ≠ 0)
    (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) (lam : (B : Type u))
    (rest : PrimeTower07Q9 p (completedPrimeStep07Q9 B p hp hB lam) n) :
    (cons hp hB lam rest).top = rest.top :=
  rfl

/-- The structure map of the tower of length `0` is the identity. -/
theorem toTop_nil (B : DividedPowerRing.{u}) : (nil (p := p) B).toTop = 𝟙 B :=
  rfl

/-- The structure map of a tower is the first structure map followed by that of the rest. -/
theorem toTop_cons {B : DividedPowerRing.{u}} {n : ℕ} (hp : p ≠ 0)
    (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) (lam : (B : Type u))
    (rest : PrimeTower07Q9 p (completedPrimeStep07Q9 B p hp hB lam) n) :
    (cons hp hB lam rest).toTop = completedPrimeStepι07Q9 B p hp hB lam ≫ rest.toTop :=
  rfl

end PrimeTower07Q9

/-! ### The tower of a chain -/

section ChainTower

open AlgebraicGeometry

variable {p : ℕ} (hp : p ≠ 0)

/-- The image of `z` in `(B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`. -/
abbrev completedPrimeStepRoot07Q9 (B : DividedPowerRing.{u})
    (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) (lam : (B : Type u)) :
    completedPrimeStep07Q9 B p hp hB lam :=
  AdicCompletion.of _ _ (zElt B p lam)

/-- The isomorphism of completed extensions sends `z` to `z`. -/
theorem completedPrimeStepIso07Q9_hom_root {B B' : DividedPowerRing.{u}}
    (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
    (hB' : IsNilpotent (Ideal.Quotient.mk B'.ideal ((p : ℕ) : (B' : Type u))))
    {lam : (B : Type u)} {lam' : (B' : Type u)} (Θ : B ≅ B') (hθ : Θ.hom lam = lam') :
    (completedPrimeStepIso07Q9 p hp hB hB' Θ hθ).hom (completedPrimeStepRoot07Q9 hp B hB lam) =
      completedPrimeStepRoot07Q9 hp B' hB' lam' :=
  (adicCompletionRingMap_of _ _ _).trans
    (congrArg (AdicCompletion.of _ _) (primeMap07Q9_zElt p hp Θ.hom hθ))

variable {R : CommRingCat.{v}} (B : DividedPowerRing.{u})
  (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (φ : R →+* (B : Type u) ⧸ B.ideal) (c : R)

/-- **The lift `λ ∈ B` of the constant `c` of a stage**: a chosen preimage of the image of `c` in
`B / J` under the identification `φ`. -/
def chainLift07Q9 : (B : Type u) := (Ideal.Quotient.mk_surjective (φ c)).choose

/-- The lift is a lift. -/
theorem chainLift07Q9_spec : Ideal.Quotient.mk B.ideal (chainLift07Q9 B φ c) = φ c :=
  (Ideal.Quotient.mk_surjective (φ c)).choose_spec

/-- In the completed extension by a lift of `c`, the image of `z` is a `p`-th root of the image of
`c` modulo the divided power ideal. -/
theorem chainStepQuotient07Q9_aux :
    Polynomial.eval₂ ((DividedPowerRing.quotientRingHom
        (completedPrimeStepι07Q9 B p hp hB (chainLift07Q9 B φ c))).comp φ)
      (Ideal.Quotient.mk _ (completedPrimeStepRoot07Q9 hp B hB (chainLift07Q9 B φ c)))
      (Polynomial.X ^ p - Polynomial.C c) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, RingHom.comp_apply,
    ← chainLift07Q9_spec B φ c, DividedPowerRing.quotientRingHom_mk,
    ← map_pow (Ideal.Quotient.mk _), ← RingHom.map_sub,
    Ideal.Quotient.eq_zero_iff_mem, completedPrimeStepι07Q9_apply]
  have h : zElt B p (chainLift07Q9 B φ c) ^ p -
      algebraMap (B : Type u) (primeRing B p (chainLift07Q9 B φ c)) (chainLift07Q9 B φ c) =
      xiElt B p (chainLift07Q9 B φ c) 1 0 := xiElt_one_zero_eq.symm
  have h2 : completedPrimeStepRoot07Q9 hp B hB (chainLift07Q9 B φ c) ^ p -
      AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p (chainLift07Q9 B φ c))
        (chainLift07Q9 B φ c)) =
      AdicCompletion.of _ _ (xiElt B p (chainLift07Q9 B φ c) 1 0) := by
    rw [← h]
    simp only [AdicCompletion.of_eq_algebraMap, map_sub, map_pow]
  rw [h2]
  exact (completionDPMorphism _ (primeDividedPowers B p _ hp) p _).ideal_comp
    (Ideal.mem_map_of_mem _ (xiElt_one_zero_mem B p _ hp))

/-- **The identification of the next stage modulo its divided power ideal**: the ring map
`R[z]/(z^p - c) → D'/J'` extending `φ` and sending `z` to the image of `z`, for
`D' = (B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧` with `λ` the chosen lift of `c`. -/
def chainStepQuotient07Q9 :
    CommRingCat.of (alphaPAlgebra p R c) →+*
      (completedPrimeStep07Q9 B p hp hB (chainLift07Q9 B φ c) : Type u) ⧸
        (completedPrimeStep07Q9 B p hp hB (chainLift07Q9 B φ c)).ideal :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom ((DividedPowerRing.quotientRingHom
      (completedPrimeStepι07Q9 B p hp hB (chainLift07Q9 B φ c))).comp φ)
      (Ideal.Quotient.mk _ (completedPrimeStepRoot07Q9 hp B hB (chainLift07Q9 B φ c)))) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Polynomial.coe_eval₂RingHom, chainStepQuotient07Q9_aux, mul_zero])

/-- The identification of the next stage extends `φ`. -/
theorem chainStepQuotient07Q9_algebraMap (r : R) :
    chainStepQuotient07Q9 hp B hB φ c (algebraMap R (alphaPAlgebra p R c) r) =
      DividedPowerRing.quotientRingHom
        (completedPrimeStepι07Q9 B p hp hB (chainLift07Q9 B φ c)) (φ r) := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (Polynomial.C r)) = _
  rw [Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

/-- The identification of the next stage sends `z` to the image of `z`. -/
theorem chainStepQuotient07Q9_root :
    chainStepQuotient07Q9 hp B hB φ c (Ideal.Quotient.mk _ Polynomial.X) =
      Ideal.Quotient.mk _ (completedPrimeStepRoot07Q9 hp B hB (chainLift07Q9 B φ c)) := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ Polynomial.X) = _
  rw [Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- **The tower of completed extensions of a chain of `α_p`-extensions**: over a divided power ring
`B` with an identification `φ : R_0 → B / J`, the `k`-th stage is the completed extension of the
previous one by a lift `λ_k` of the constant `c_k` of the `k`-th stage of the chain, read in it
through the identification of the previous stage (`Crystalline.chainLift07Q9`,
`Crystalline.chainStepQuotient07Q9`). -/
def chainTower07Q9 : {R : CommRingCat.{v}} → {n : ℕ} → AlphaPChain p R n →
    (B : DividedPowerRing.{u}) →
    IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))) →
    (R →+* (B : Type u) ⧸ B.ideal) → PrimeTower07Q9 p B n
  | _, _, .nil _, B, _, _ => .nil B
  | _, _, .cons c rest, B, hB, φ => .cons hp hB (chainLift07Q9 B φ c)
      (chainTower07Q9 rest _ (completedPrimeStep07Q9_isNilpotent B p hp hB _)
        (chainStepQuotient07Q9 hp B hB φ c))

/-- The tower of the empty chain is empty. -/
theorem chainTower07Q9_nil : chainTower07Q9 hp (.nil R) B hB φ = .nil B :=
  rfl

/-- The tower of a chain whose first stage adjoins a `p`-th root of `c` starts with the completed
extension by the chosen lift of `c`. -/
theorem chainTower07Q9_cons {n : ℕ}
    (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p R c)) n) :
    chainTower07Q9 hp (.cons c rest) B hB φ = .cons hp hB (chainLift07Q9 B φ c)
      (chainTower07Q9 hp rest _ (completedPrimeStep07Q9_isNilpotent B p hp hB _)
        (chainStepQuotient07Q9 hp B hB φ c)) :=
  rfl

end ChainTower

/-! ### The completed envelope modulo its divided power ideal -/

section EnvelopeQuotient

variable (s : AffineCrystallineSituation.{u, v}) {κ : Type w} (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
  (hg : Function.Surjective g)

/-- The reduction `P → E → D → D/J` of a presentation modulo the divided power ideal of its
completed envelope. -/
def envelopeReduction07Q9 :
    MvPolynomial κ s.A →+* (envelopeCompletedDPRing s g : Type (max u w)) ⧸
      (envelopeCompletedDPRing s g).ideal :=
  (Ideal.Quotient.mk _).comp ((algebraMap (polynomialDividedPowerEnvelope s g).object
    (envelopeCompletedDPRing s g)).comp (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom)

/-- The reduction kills the kernel of the presentation. -/
theorem ker_le_ker_envelopeReduction07Q9 :
    RingHom.ker g.toRingHom ≤ RingHom.ker (envelopeReduction07Q9 s g) := by
  intro x hx
  rw [RingHom.mem_ker, envelopeReduction07Q9, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact (envelopeCompletionDP s g).ideal_comp (Ideal.mem_map_of_mem _
    ((polynomialDividedPowerEnvelope s g).algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hx)))

/-- **The identification `C → D/J`** of the target of a surjective presentation with its completed
envelope modulo the divided power ideal (one direction of it). -/
def envelopeQuotient07Q9 :
    s.C →+* (envelopeCompletedDPRing s g : Type (max u w)) ⧸ (envelopeCompletedDPRing s g).ideal :=
  (Ideal.Quotient.lift _ (envelopeReduction07Q9 s g)
    (fun _ ha => RingHom.mem_ker.mp (ker_le_ker_envelopeReduction07Q9 s g ha))).comp
    (g.toRingHom.quotientKerEquivOfSurjective hg).symm.toRingHom

/-- The identification `C → D/J` sends `g(x)` to the class of the image of `x`. -/
theorem envelopeQuotient07Q9_apply (x : MvPolynomial κ s.A) :
    envelopeQuotient07Q9 s g hg (g x) = Ideal.Quotient.mk _
      (AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x)) := by
  have h : (g.toRingHom.quotientKerEquivOfSurjective hg).symm (g.toRingHom x) =
      Ideal.Quotient.mk (RingHom.ker g.toRingHom) x :=
    RingHom.quotientKerEquivOfSurjective_symm_apply hg x
  rw [envelopeQuotient07Q9, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, show g x = g.toRingHom x from rfl, h, Ideal.Quotient.lift_mk]
  rfl

end EnvelopeQuotient

/-! ### The identification along a chain -/

section ChainIso

variable {s t : AffineCrystallineSituation.{u, v}} (σ : AffineCrystallineSituation.Hom s t)
  (τb : DPMorphism t.A.dividedPowers s.A.dividedPowers) (h₁ : ∀ a, τb (σ.base a) = a)
  (h₂ : ∀ a, σ.base (τb a) = a) {R : Type v} [CommRing R] (ψ : s.C ≃+* R) (ε : t.C ≃+* R)
  (hε : ∀ x, ε (σ.target x) = ψ x) {κ κ' : Type w} {g : MvPolynomial κ s.A →ₐ[s.A] s.C}
  {g' : MvPolynomial κ' t.A →ₐ[t.A] t.C} (e : κ ≃ κ')
  (hvar : ∀ k, g' (X (e k)) = σ.target (g (X k)))
  (hq : IsNilpotent (Ideal.Quotient.mk (polynomialDividedPowerEnvelope t g').object.ideal
    ((s.p : ℕ) : (polynomialDividedPowerEnvelope t g').object)))

/-- Maps of envelopes induced by mutually inverse maps of the variables compose to the identity. -/
private theorem variableEnvelopeMap07Q9_comp_eq_id
    {s t : AffineCrystallineSituation.{u, v}} {κ κ' : Type w}
    {g : MvPolynomial κ s.A →ₐ[s.A] s.C} {g' : MvPolynomial κ' t.A →ₐ[t.A] t.C}
    (σ : AffineCrystallineSituation.Hom s t) (τ : AffineCrystallineSituation.Hom t s)
    (e : κ ≃ κ') (e' : κ' ≃ κ) (he : ∀ k, e' (e k) = k) (h : ∀ a, τ.base (σ.base a) = a)
    (hvar : ∀ k, g' (X (e k)) = σ.target (g (X k)))
    (hvar' : ∀ v, g (X (e' v)) = τ.target (g' (X v))) :
    (variableEnvelopeMap07Q9 τ g' g hvar').comp (variableEnvelopeMap07Q9 σ g g' hvar) =
      DPMorphism.id _ := by
  refine (polynomialDividedPowerEnvelope s g).dpMorphism_ext _ _ fun x => ?_
  show variableEnvelopeMap07Q9 τ g' g hvar' (variableEnvelopeMap07Q9 σ g g' hvar
    ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x)) = _
  rw [variableEnvelopeMap07Q9_algebraMap, variableEnvelopeMap07Q9_algebraMap]
  have hr : (variableMapRingHom07Q9 τ e').comp (variableMapRingHom07Q9 σ e) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro b
      rw [RingHom.comp_apply, variableMapRingHom07Q9_C, variableMapRingHom07Q9_C]
      exact congrArg C (h b)
    · intro k
      rw [RingHom.comp_apply, variableMapRingHom07Q9_X, variableMapRingHom07Q9_X, he]
      rfl
  exact congrArg _ (RingHom.congr_fun hr x)

include h₁ h₂ hε in
/-- The two maps of envelopes induced by `σ` and its inverse compose to the identity. -/
theorem variableEnvelopeMap07Q9_inverse :
    (variableEnvelopeMap07Q9 (inverseHom07Q9 σ τb h₂ ψ ε hε) g' g
        (inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar)).comp (variableEnvelopeMap07Q9 σ g g' hvar) =
      DPMorphism.id _ ∧
    (variableEnvelopeMap07Q9 σ g g' hvar).comp (variableEnvelopeMap07Q9
        (inverseHom07Q9 σ τb h₂ ψ ε hε) g' g (inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar)) =
      DPMorphism.id _ :=
  ⟨variableEnvelopeMap07Q9_comp_eq_id σ _ e e.symm e.symm_apply_apply h₁ hvar _,
    variableEnvelopeMap07Q9_comp_eq_id _ σ e.symm e e.apply_symm_apply h₂ _ hvar⟩

include h₁ in
/-- **The completed envelopes of two presentations related by an isomorphism of situations and a
bijection of the variables are isomorphic** divided power rings. -/
def completedVariableEnvelopeIso07Q9 :
    envelopeCompletedDPRing s g ≅
      pAdicCompletedDPRing (polynomialDividedPowerEnvelope t g').object s.p hq where
  hom := DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ s.p
    (polynomialDividedPowerEnvelope_prime_nilpotent s g) hq (variableEnvelopeMap07Q9 σ g g' hvar))
  inv := DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ s.p hq
    (polynomialDividedPowerEnvelope_prime_nilpotent s g)
    (variableEnvelopeMap07Q9 (inverseHom07Q9 σ τb h₂ ψ ε hε) g' g
      (inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar)))
  hom_inv_id := by
    apply DPMorphism.ext
    funext x
    have hc := RingHom.congr_fun (adicCompletionRingMap_comp s.p
      (variableEnvelopeMap07Q9 σ g g' hvar).toRingHom
      (variableEnvelopeMap07Q9 (inverseHom07Q9 σ τb h₂ ψ ε hε) g' g
        (inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar)).toRingHom) x
    have hi := congrArg (fun q : DPMorphism _ _ =>
      adicCompletionRingMap q.toRingHom (map_pAdicIdeal_le s.p q.toRingHom) x)
      (variableEnvelopeMap07Q9_inverse σ τb h₁ h₂ ψ ε hε e hvar).1
    exact hc.symm.trans (hi.trans (RingHom.congr_fun (adicCompletionRingMap_id s.p) x))
  inv_hom_id := by
    apply DPMorphism.ext
    funext x
    have hc := RingHom.congr_fun (adicCompletionRingMap_comp s.p
      (variableEnvelopeMap07Q9 (inverseHom07Q9 σ τb h₂ ψ ε hε) g' g
        (inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar)).toRingHom
      (variableEnvelopeMap07Q9 σ g g' hvar).toRingHom) x
    have hi := congrArg (fun q : DPMorphism _ _ =>
      adicCompletionRingMap q.toRingHom (map_pAdicIdeal_le s.p q.toRingHom) x)
      (variableEnvelopeMap07Q9_inverse σ τb h₁ h₂ ψ ε hε e hvar).2
    exact hc.symm.trans (hi.trans (RingHom.congr_fun (adicCompletionRingMap_id s.p) x))

/-- The isomorphism of completed envelopes is the completed map of envelopes. -/
theorem completedVariableEnvelopeIso07Q9_hom (x : envelopeCompletedDPRing s g) :
    (completedVariableEnvelopeIso07Q9 σ τb h₁ h₂ ψ ε hε e hvar hq).hom x =
      completedVariableEnvelopeMap07Q9 σ hvar s.p x :=
  rfl

end ChainIso

section ChainStage

open AlgebraicGeometry

variable {s : AffineCrystallineSituation.{u, v}} {κ : Type w} {g : MvPolynomial κ s.A →ₐ[s.A] s.C}
  (hg : Function.Surjective g) (hp0 : s.p ≠ 0) {R : CommRingCat.{v}} (ψ : s.C ≃+* R) (c : R)
  {ct : MvPolynomial κ s.A} (hct : g ct = ψ.symm c) {B : DividedPowerRing.{max u w}}
  (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((s.p : ℕ) : (B : Type (max u w)))))
  (φ : R →+* (B : Type (max u w)) ⧸ B.ideal) (θ : envelopeCompletedDPRing s g ≅ B)
  (hφ : ∀ x, Ideal.Quotient.mk B.ideal (θ.hom (AdicCompletion.of _ _
    ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x))) = φ (ψ (g x)))

include hct hφ in
/-- The pull-back to the completed envelope of the chosen lift of the constant of the first
stage is a lift of that constant. -/
theorem chainStage_lam_mem07Q9 :
    θ.inv (chainLift07Q9 B φ c) - AdicCompletion.of _ _
        ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct) ∈
      (envelopeCompletedDPRing s g).ideal := by
  set y := AdicCompletion.of (pAdicIdeal (A := (polynomialDividedPowerEnvelope s g).object) s.p) _
    ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct)
  have h1 : θ.hom y - chainLift07Q9 B φ c ∈ B.ideal := by
    rw [← Ideal.Quotient.eq, hφ, hct, RingEquiv.apply_symm_apply, chainLift07Q9_spec]
  have h2 := (DPMorphism.ideal_comp θ.inv) (Ideal.mem_map_of_mem
    (DPMorphism.toRingHom θ.inv) h1)
  rw [map_sub] at h2
  have h4 : DPMorphism.toRingHom θ.inv (θ.hom y) = y :=
    congrArg (fun q : envelopeCompletedDPRing s g ⟶ envelopeCompletedDPRing s g => q y)
      θ.hom_inv_id
  rw [h4] at h2
  rw [← neg_sub]
  exact neg_mem h2

/-- The `α_p`-extension condition on the new variable. -/
theorem chainStage_hnone07Q9 :
    alphaPPresentation s (ψ.symm c) g (X ((Equiv.refl (Option κ)) none)) =
      alphaPRoot s (ψ.symm c) :=
  alphaPPresentation_X_none s _ g

/-- The transport along `θ` of the completed extension by the pull-back of the chosen lift. -/
abbrev chainStageTransport07Q9 :
    completedPrimeStep07Q9 (envelopeCompletedDPRing s g) s.p hp0
        (envelopeCompletedDPRing_isNilpotent (g := g)) (θ.inv (chainLift07Q9 B φ c)) ≅
      completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c) :=
  completedPrimeStepIso07Q9 s.p hp0 (envelopeCompletedDPRing_isNilpotent (g := g)) hB θ
    (congrArg (fun q : B ⟶ B => q (chainLift07Q9 B φ c)) θ.inv_hom_id)

/-- The identification `Crystalline.alphaPCompletedEnvelopeIso` of the first stage, for the
pull-back of the chosen lift. -/
abbrev chainStageAlphaP07Q9 :
    envelopeCompletedDPRing (alphaPSituation s (ψ.symm c)) (alphaPPresentation s (ψ.symm c) g) ≅
      completedPrimeStep07Q9 (envelopeCompletedDPRing s g) s.p hp0
        (envelopeCompletedDPRing_isNilpotent (g := g)) (θ.inv (chainLift07Q9 B φ c)) :=
  alphaPCompletedEnvelopeIso hg (chainStage_hnone07Q9 ψ c) (alphaPStep_hsome07Q9 (ψ.symm c)) hct
    (chainStage_lam_mem07Q9 ψ c hct φ θ hφ)

/-- **The identification of the completed envelope of the first stage** with the completed
extension of `B` by the chosen lift `λ` of the constant: `Crystalline.alphaPCompletedEnvelopeIso`
followed by the transport along `θ`, `Crystalline.completedPrimeStepIso07Q9`. -/
def chainStageIso07Q9 :
    envelopeCompletedDPRing (alphaPSituation s (ψ.symm c)) (alphaPPresentation s (ψ.symm c) g) ≅
      completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c) :=
  chainStageAlphaP07Q9 hg hp0 ψ c hct φ θ hφ ≪≫ chainStageTransport07Q9 hp0 c hB φ θ

/-- The identification of the first stage is compatible with the structure maps out of `D` and
out of `B`. -/
theorem chainStageIso07Q9_hom_envelopeMap (a : envelopeCompletedDPRing s g) :
    (chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom
        (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 (ψ.symm c)) a) =
      completedPrimeStepι07Q9 B s.p hp0 hB (chainLift07Q9 B φ c) (θ.hom a) :=
  (congrArg (chainStageTransport07Q9 hp0 c hB φ θ).hom
    (alphaPCompletedEnvelopeToPrime_envelopeMap hg (chainStage_hnone07Q9 ψ c)
      (alphaPStep_hsome07Q9 (ψ.symm c)) hct (chainStage_lam_mem07Q9 ψ c hct φ θ hφ) a)).trans
    (completedPrimeStepIso07Q9_hom_ι s.p hp0 _ hB θ _ a)

/-- The identification of the first stage sends `z` to `z`. -/
theorem chainStageIso07Q9_hom_root :
    (chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom (alphaPCompletedRoot s (ψ.symm c)
        (alphaPPresentation s (ψ.symm c) g) (Equiv.refl (Option κ))) =
      completedPrimeStepRoot07Q9 hp0 B hB (chainLift07Q9 B φ c) :=
  (congrArg (chainStageTransport07Q9 hp0 c hB φ θ).hom
    (alphaPCompletedEnvelopeToPrime_root hg (chainStage_hnone07Q9 ψ c)
      (alphaPStep_hsome07Q9 (ψ.symm c)) hct (chainStage_lam_mem07Q9 ψ c hct φ θ hφ))).trans
    (completedPrimeStepIso07Q9_hom_root hp0 _ hB θ _)

/-- The identification of the first stage on the image of `D`, modulo the divided power
ideal. -/
theorem chainStageIso07Q9_quotient_old (y : MvPolynomial κ s.A) :
    Ideal.Quotient.mk (completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c)).ideal
        ((chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom
          (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 (ψ.symm c)) (AdicCompletion.of _ _
            ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom y)))) =
      chainStepQuotient07Q9 hp0 B hB φ c (alphaPAlgebraEquiv07Q9 rfl ψ c
        (algebraMap s.C (alphaPSituation s (ψ.symm c)).C (g y))) := by
  rw [chainStageIso07Q9_hom_envelopeMap, ← DividedPowerRing.quotientRingHom_mk, hφ,
    alphaPAlgebraEquiv07Q9_algebraMap, chainStepQuotient07Q9_algebraMap]

/-- The identification of the first stage on the old variables, modulo the divided power
ideal. -/
theorem chainStageIso07Q9_quotient_rename (y : MvPolynomial κ s.A) :
    Ideal.Quotient.mk (completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c)).ideal
        ((chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom (AdicCompletion.of _ _
          ((polynomialDividedPowerEnvelope (alphaPSituation s (ψ.symm c))
            (alphaPPresentation s (ψ.symm c) g)).algebraMap.toRingHom
              (rename (⇑(Equiv.refl (Option κ)) ∘ some) y)))) =
      chainStepQuotient07Q9 hp0 B hB φ c (alphaPAlgebraEquiv07Q9 rfl ψ c
        (alphaPPresentation s (ψ.symm c) g (rename (⇑(Equiv.refl (Option κ)) ∘ some) y))) := by
  have e1 := alphaPEnvelopeMap_algebraMap (alphaPStep_hsome07Q9 (g := g) (ψ.symm c)) y
  have e2 := alphaPCompletedEnvelopeMap_of (alphaPStep_hsome07Q9 (g := g) (ψ.symm c))
    ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom y)
  rw [e1] at e2
  refine (congrArg (fun w => Ideal.Quotient.mk
    (completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c)).ideal
    ((chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom w)) e2.symm).trans ?_
  refine (chainStageIso07Q9_quotient_old hg hp0 ψ c hct hB φ θ hφ y).trans ?_
  exact congrArg (fun z => chainStepQuotient07Q9 hp0 B hB φ c (alphaPAlgebraEquiv07Q9 rfl ψ c z))
    (alphaPPresentation_rename_some s _ g y).symm

/-- **The identification of the first stage is compatible with the identifications modulo the
divided power ideals**: those of `C[z]/(z^p - c)` with `D_1/J_1` and with `B'/J'`. -/
theorem chainStageIso07Q9_quotient (x : MvPolynomial (Option κ) s.A) :
    Ideal.Quotient.mk (completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c)).ideal
        ((chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom (AdicCompletion.of _ _
          ((polynomialDividedPowerEnvelope (alphaPSituation s (ψ.symm c))
            (alphaPPresentation s (ψ.symm c) g)).algebraMap.toRingHom x))) =
      chainStepQuotient07Q9 hp0 B hB φ c (alphaPAlgebraEquiv07Q9 rfl ψ c
        (alphaPPresentation s (ψ.symm c) g x)) := by
  have key : (Ideal.Quotient.mk (completedPrimeStep07Q9 B s.p hp0 hB (chainLift07Q9 B φ c)).ideal
      ).comp ((DPMorphism.toRingHom (chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ).hom).comp
        ((algebraMap (polynomialDividedPowerEnvelope (alphaPSituation s (ψ.symm c))
          (alphaPPresentation s (ψ.symm c) g)).object
          (envelopeCompletedDPRing (alphaPSituation s (ψ.symm c))
            (alphaPPresentation s (ψ.symm c) g))).comp
          (polynomialDividedPowerEnvelope (alphaPSituation s (ψ.symm c))
            (alphaPPresentation s (ψ.symm c) g)).algebraMap.toRingHom)) =
      (chainStepQuotient07Q9 hp0 B hB φ c).comp ((alphaPAlgebraEquiv07Q9 rfl ψ c).toRingHom.comp
        (alphaPPresentation s (ψ.symm c) g).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have h := chainStageIso07Q9_quotient_rename hg hp0 ψ c hct hB φ θ hφ (C a)
      rw [rename_C] at h
      exact h
    · intro o
      cases o with
      | none =>
        refine (congrArg (Ideal.Quotient.mk _)
          (chainStageIso07Q9_hom_root hg hp0 ψ c hct hB φ θ hφ)).trans ?_
        show _ = chainStepQuotient07Q9 hp0 B hB φ c (alphaPAlgebraEquiv07Q9 rfl ψ c
          (alphaPPresentation s (ψ.symm c) g (X none)))
        rw [alphaPPresentation_X_none, alphaPAlgebraEquiv07Q9_root, chainStepQuotient07Q9_root]
      | some k =>
        have h := chainStageIso07Q9_quotient_rename hg hp0 ψ c hct hB φ θ hφ (X k)
        rw [rename_X] at h
        exact h
  exact RingHom.congr_fun key x

end ChainStage

section ChainIsoInduction

open AlgebraicGeometry

/-- **The completed envelope of a chain presentation is the last stage of the tower of the chain.**
Let `ch` be a chain `R = R_0 ⟶ ⋯ ⟶ R_n` of `α_p`-extensions, `g : P → C` a surjective presentation
of `C ≅ R` in a situation `s` with prime `p`, and `g' : P' → C'` a presentation in a situation `t`
over an isomorphic base with `C' ≅ R_n`, whose variables are those of `P` and the roots.  Let
`θ : D ≅ B` identify the completed envelope of `g` with a divided power ring `B`, compatibly with
an identification `φ : R → B/J`.  Then the completed envelope `D'` of `g'` is isomorphic, as a
divided power ring, to the last stage of the tower `Crystalline.chainTower07Q9` over `B`, by an
isomorphism under which `D → D'` becomes `θ` followed by the structure maps of the tower.

By induction on the chain: the first stage is `Crystalline.alphaPCompletedEnvelopeIso` transported
along `θ` (`Crystalline.completedPrimeStepIso07Q9`); the empty chain is
`Crystalline.completedVariableEnvelopeIso07Q9`. -/
theorem exists_chainTowerIso07Q9 {p : ℕ} (hp0 : p ≠ 0) : ∀ {R : CommRingCat.{v}} {n : ℕ}
    (ch : AlphaPChain p R n)
    (s : AffineCrystallineSituation.{u, v}) (_hp : s.p = p) (ψ : s.C ≃+* R) {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C) (_hg : Function.Surjective g)
    (t : AffineCrystallineSituation.{u, v}) (σ : AffineCrystallineSituation.Hom s t)
    (τb : DPMorphism t.A.dividedPowers s.A.dividedPowers) (_h₁ : ∀ a, τb (σ.base a) = a)
    (_h₂ : ∀ a, σ.base (τb a) = a) (ε : t.C ≃+* ch.top)
    (_hε : ∀ x, ε (σ.target x) = ch.toTop.hom (ψ x)) {κ' : Type w}
    (g' : MvPolynomial κ' t.A →ₐ[t.A] t.C) (e : κ ⊕ Fin n ≃ κ')
    (hvar : ∀ k, g' (X (e (Sum.inl k))) = σ.target (g (X k)))
    (_hroot : ∀ i, g' (X (e (Sum.inr i))) = ε.symm (ch.roots i))
    (hq : IsNilpotent (Ideal.Quotient.mk (polynomialDividedPowerEnvelope t g').object.ideal
      ((s.p : ℕ) : (polynomialDividedPowerEnvelope t g').object)))
    (B : DividedPowerRing.{max u w})
    (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type (max u w)))))
    (φ : R →+* (B : Type (max u w)) ⧸ B.ideal) (θ : envelopeCompletedDPRing s g ≅ B)
    (_hφ : ∀ x, Ideal.Quotient.mk B.ideal (θ.hom (AdicCompletion.of _ _
      ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x))) = φ (ψ (g x))),
    ∃ Θ : pAdicCompletedDPRing (polynomialDividedPowerEnvelope t g').object s.p hq ≅
        (chainTower07Q9 hp0 ch B hB φ).top,
      ∀ a, Θ.hom (completedVariableEnvelopeMap07Q9 σ (j := e ∘ Sum.inl) hvar s.p a) =
        (chainTower07Q9 hp0 ch B hB φ).toTop (θ.hom a) := by
  intro R n ch
  induction ch with
  | nil R =>
    intro s hp ψ κ g hg t σ τb h₁ h₂ ε hε κ' g' e hvar hroot hq B hB φ θ hφ
    refine ⟨(completedVariableEnvelopeIso07Q9 σ τb h₁ h₂ ψ ε hε
      ((Equiv.sumEmpty κ (Fin 0)).symm.trans e) hvar hq).symm ≪≫ θ, fun a => ?_⟩
    have h := congrArg (fun y => θ.hom y) (congrArg (fun q => q a)
      (congrArg DPMorphism.toRingHom ((completedVariableEnvelopeIso07Q9 σ τb h₁ h₂ ψ ε hε
        ((Equiv.sumEmpty κ (Fin 0)).symm.trans e) hvar hq).hom_inv_id)))
    exact h
  | @cons R n c rest ih =>
    intro s hp ψ κ g hg t σ τb h₁ h₂ ε hε κ' g' e hvar hroot hq B hB φ θ hφ
    subst hp
    obtain ⟨ct, hct⟩ := hg (ψ.symm c)
    let T₁ : (alphaPSituation s (ψ.symm c)).C →+* t.C :=
      ε.symm.toRingHom.comp (rest.toTop.hom.comp (alphaPAlgebraEquiv07Q9 rfl ψ c).toRingHom)
    have hT : ∀ y, T₁ (algebraMap s.C (alphaPSituation s (ψ.symm c)).C y) = σ.target y := by
      intro y
      show ε.symm (rest.toTop.hom (alphaPAlgebraEquiv07Q9 rfl ψ c (algebraMap s.C _ y))) = _
      rw [alphaPAlgebraEquiv07Q9_algebraMap]
      show ε.symm ((AlphaPChain.cons c rest).toTop.hom (ψ y)) = _
      rw [← hε, RingEquiv.symm_apply_apply]
    have hj₁ : ∀ o, g' (X (((optionSumFinEquiv07Q9 κ n).trans e) (Sum.inl o))) =
        (alphaPStepHom07Q9 σ (ψ.symm c) T₁ hT).target
          (alphaPPresentation s (ψ.symm c) g (X o)) := by
      intro o
      cases o with
      | none =>
        rw [alphaPPresentation_X_none]
        show g' (X (e (Sum.inr 0))) = ε.symm (rest.toTop.hom (alphaPAlgebraEquiv07Q9 rfl ψ c
          (Ideal.Quotient.mk _ Polynomial.X)))
        rw [hroot, alphaPAlgebraEquiv07Q9_root]
        rfl
      | some k =>
        rw [alphaPPresentation_X_some]
        exact (hvar k).trans (hT _).symm
    obtain ⟨Θ, hΘ⟩ := ih (alphaPSituation s (ψ.symm c)) rfl (alphaPAlgebraEquiv07Q9 rfl ψ c)
      (alphaPPresentation s (ψ.symm c) g) (alphaPPresentation_surjective s _ g hg) t
      (alphaPStepHom07Q9 σ (ψ.symm c) T₁ hT) τb h₁ h₂ ε
      (fun x => RingEquiv.apply_symm_apply ε _) g' ((optionSumFinEquiv07Q9 κ n).trans e)
      hj₁ (fun i => hroot i.succ) hq _ (completedPrimeStep07Q9_isNilpotent B s.p hp0 hB _)
      (chainStepQuotient07Q9 hp0 B hB φ c) (chainStageIso07Q9 hg hp0 ψ c hct hB φ θ hφ)
      (chainStageIso07Q9_quotient hg hp0 ψ c hct hB φ θ hφ)
    refine ⟨Θ, fun a => ?_⟩
    have h1 := completedVariableEnvelopeMap07Q9_eq_comp σ (ψ.symm c) T₁ hT hvar hj₁
      (fun _ => rfl) a
    have h2 := hΘ (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 (ψ.symm c)) a)
    rw [chainStageIso07Q9_hom_envelopeMap] at h2
    exact (congrArg Θ.hom h1).trans h2

end ChainIsoInduction

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline AlgebraicGeometry MvPolynomial

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {X' : Scheme.{u}} (f : X' ⟶ S.X)
  (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {p n : ℕ} (ch : AlphaPChain p Γ(S.X, W) n)
  (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top) (he : f.app W ≫ e.hom = ch.toTop) (hp : S.p = p)

include hp in
/-- The prime of the chain is nonzero. -/
theorem chain_p_ne_zero07Q9 : p ≠ 0 := hp ▸ (Fact.out : S.p.Prime).ne_zero

/-- The identification `Γ(S.X, W) → D(0)/J(0)` of the ring of `W` with the completed envelope of
degree zero of the canonical presentation modulo its divided power ideal. -/
def chainBaseQuotient07Q9 :
    Γ(S.X, W) →+* (completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _) 0 : Type u) ⧸
      (completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _) 0).ideal :=
  (envelopeQuotient07Q9 _ _ (tensorPowerPresentation_surjective _ _
    (canonicalPresentation_surjective _) 0)).comp W.topIso.commRingCatIsoToRingEquiv.symm.toRingHom

/-- **The tower `D(0) = D_0 ⟶ D_1 ⟶ ⋯ ⟶ D_n` of the chain**: over the completed envelope `D(0)` of
degree zero of the canonical presentation of `Γ(W)`, the `k`-th stage is the completed extension
`(D_k[z]⟨ξ⟩/(ξ - (z^p - λ_k)))^∧` of [Stacks, Tag 07N1] by a lift `λ_k` of the constant of the
`k`-th stage of the chain (`Crystalline.chainTower07Q9`). -/
def chainEnvelopeTower07Q9 :
    PrimeTower07Q9 p (completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
      (canonicalPresentation_surjective _) 0) n :=
  chainTower07Q9 (chain_p_ne_zero07Q9 S hp) ch _
    (hp ▸ envelopeCompletedDPRing_isNilpotent (s := openAffineSituation07Q9 S hW hVW)
      (g := tensorPowerPresentation _ (canonicalPresentation (openAffineSituation07Q9 S hW hVW)) 0))
    (chainBaseQuotient07Q9 S hW hVW)

include he in
/-- The identification of `D'(0)` with the last stage of the tower exists. -/
theorem exists_chainEnvelopeTowerIso07Q9 :
    ∃ Θ : completedTensorPowerDividedPowerRing (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0 ≅
        (chainEnvelopeTower07Q9 S hW hVW ch hp).top,
      ∀ a, Θ.hom (completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
          (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
          (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
          (chainPresentationRename07Q9 S hW hVW f hW₂)
          (chainPresentationRename07Q9_C S hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 a) =
        (chainEnvelopeTower07Q9 S hW hVW ch hp).toTop a := by
  obtain ⟨Θ, hΘ⟩ := exists_chainTowerIso07Q9 (chain_p_ne_zero07Q9 S hp) ch
    (openAffineSituation07Q9 S hW hVW) hp W.topIso.commRingCatIsoToRingEquiv _
    (tensorPowerPresentation_surjective _ _ (canonicalPresentation_surjective _) 0)
    (openAffineSituation₂07Q9 S hVW f hW₂) (openAffineSituationHom07Q9 S hW hVW f hW₂)
    (DPMorphism.id _) (fun _ => rfl) (fun _ => rfl)
    (chainSectionsIso07Q9 S f ch e).commRingCatIsoToRingEquiv
    (fun x => congrArg (fun k => k.hom x) (chainSectionsIso07Q9_restrictMap S hVW f ch e he))
    _ (chainDegreeZeroVariables07Q9 _ n) (chainDegreeZero07Q9_var S hW hVW f hW₂ ch e)
    (chainDegreeZero07Q9_root S hW hVW f hW₂ ch e)
    (polynomialDividedPowerEnvelope_prime_nilpotent _ _) _
    (hp ▸ envelopeCompletedDPRing_isNilpotent (s := openAffineSituation07Q9 S hW hVW)
      (g := tensorPowerPresentation _ (canonicalPresentation (openAffineSituation07Q9 S hW hVW)) 0))
    (chainBaseQuotient07Q9 S hW hVW) (Iso.refl _) (fun x =>
      ((congrArg (envelopeQuotient07Q9 (openAffineSituation07Q9 S hW hVW) _
        (tensorPowerPresentation_surjective _ _ (canonicalPresentation_surjective _) 0))
        (W.topIso.commRingCatIsoToRingEquiv.symm_apply_apply
          (tensorPowerPresentation _ (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
            0 x))).trans (envelopeQuotient07Q9_apply _ _ _ x)).symm)
  refine ⟨Θ, fun a => ?_⟩
  exact (congrArg Θ.hom (adicCompletionRingMap_envelopeMap07Q9_chain S hW hVW f hW₂ ch e a)).trans
    (hΘ a)

/-- **The identification `D'(0) ≅ D_n` of [Stacks, Tag 07Q9], proof**: the completed envelope of
degree zero of the chain presentation of `Γ(f⁻¹(W))`, as a divided power ring, is the last stage
of the tower `chainEnvelopeTower07Q9` of completed extensions of [Stacks, Tag 07N1] over the
completed envelope `D(0)` of degree zero of the canonical presentation of `Γ(W)`. -/
def chainEnvelopeTowerIso07Q9 :
    completedTensorPowerDividedPowerRing (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0 ≅
      (chainEnvelopeTower07Q9 S hW hVW ch hp).top :=
  (exists_chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he hp).choose

/-- **The identification composed with `D(0) → D'(0)` is the composite of the structure maps of
the tower**, `D_0 → D_1 → ⋯ → D_n`. -/
theorem chainEnvelopeTowerIso07Q9_hom_completedEnvelopeMap
    (a : completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
      (canonicalPresentation_surjective _) 0) :
    (chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he hp).hom
        (completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
          (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
          (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
          (chainPresentationRename07Q9 S hW hVW f hW₂)
          (chainPresentationRename07Q9_C S hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 a) =
      (chainEnvelopeTower07Q9 S hW hVW ch hp).toTop a :=
  (exists_chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he hp).choose_spec a

/-- The morphism form of `chainEnvelopeTowerIso07Q9_hom_completedEnvelopeMap`. -/
theorem completedEnvelopeMap07Q9_comp_chainEnvelopeTowerIso07Q9 :
    completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
        (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
        (chainPresentationRename07Q9 S hW hVW f hW₂)
        (chainPresentationRename07Q9_C S hW hVW f hW₂)
        (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 ≫
      (chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he hp).hom =
      (chainEnvelopeTower07Q9 S hW hVW ch hp).toTop :=
  DPMorphism.ext <| funext <|
    chainEnvelopeTowerIso07Q9_hom_completedEnvelopeMap S hW hVW f hW₂ ch e he hp

/-- `DividedPowerRing.dpMorphismCongr` commutes with the identifications `eqToHom` of the rings. -/
theorem dpMorphismCongr_comp_eqToHom07Q9 {R R' T T' : DividedPowerRing.{u}} (hR : R' = R)
    (hT : T' = T) (q : R ⟶ T) :
    DividedPowerRing.dpMorphismCongr hR hT q ≫ eqToHom hT = eqToHom hR ≫ q := by
  cases hR
  cases hT
  rfl

/-- **The identification `D'(0) ≅ D_n` on the ring of the object `D'(0)` of the Čech system**:
`chainEnvelopeTowerIso07Q9` read through the identification
`Crystalline.tensorPowerEnvelopeThickening_ring_eq` of the ring of the object
`Crystalline.tensorPowerEnvelopeThickening` with the transparent completed envelope. -/
def chainEnvelopeTowerThickeningIso07Q9 :
    (tensorPowerEnvelopeThickening (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0).thickening.ring ≅
      (chainEnvelopeTower07Q9 S hW hVW ch hp).top :=
  eqToIso (tensorPowerEnvelopeThickening_ring_eq _ _ _ 0) ≪≫
    chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he hp

/-- **The identification on the rings of the Čech systems composed with `envelopeRingMap07Q9` of
degree zero is the composite of the structure maps of the tower**, read on the ring of the object
`D(0)` of the Čech system of `W`. -/
theorem envelopeRingMap07Q9_comp_chainEnvelopeTowerThickeningIso07Q9 :
    envelopeRingMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
        (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
        (chainPresentationRename07Q9 S hW hVW f hW₂)
        (chainPresentationRename07Q9_C S hW hVW f hW₂)
        (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 ≫
      (chainEnvelopeTowerThickeningIso07Q9 S hW hVW f hW₂ ch e he hp).hom =
      eqToHom (tensorPowerEnvelopeThickening_ring_eq _ _ _ 0) ≫
        (chainEnvelopeTower07Q9 S hW hVW ch hp).toTop := by
  rw [chainEnvelopeTowerThickeningIso07Q9, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    envelopeRingMap07Q9, dpMorphismCongr_comp_eqToHom07Q9, Category.assoc,
    completedEnvelopeMap07Q9_comp_chainEnvelopeTowerIso07Q9]

end Crystalline.GlobalCrystallineSituation.SmallSite
