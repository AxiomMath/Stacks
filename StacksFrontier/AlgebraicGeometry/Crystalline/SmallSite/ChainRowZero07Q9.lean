module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairPullbackHom07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ChainDeRhamBridge07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ChainTowerStep07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChainOpenDeRham07Q9

/-!
# The cone of the row-zero map of [Stacks, Tag 07Q9] is killed by `p ^ n`

Over a chain open `W` (the morphism `f` restricted to `W` is a chain of `n` successive
`α_p`-extensions), the morphism of the rows zero of the double complexes of [Stacks, Tag 07LG]
attached to the crystal and to its pullback, `M ⊗^∧_D Ω^•_D ⟶ M' ⊗^∧_{D'} Ω^•_{D'}`, is the base
change map along `D = D(0) → D'(0) = D'`.  By [Stacks, Tag 07N1] its cone is killed by `p` along a
single completed `p`-th root extension, and `D(0) → D'(0)` is identified with a tower of `n` of
them (`Crystalline.GlobalCrystallineSituation.SmallSite.chainEnvelopeTowerIso07Q9`), so the cone is
killed by `p ^ n`.

## Main results

* `Crystalline.CosimplicialCompletedModule.coneKilledNat07Q9_pairPullbackHom` — the de Rham map
  in degree `0` of `pairPullbackHom07Q9` has the cone of the base change map.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open CategoryTheory Simplicial DividedPowers Crystalline.CompletedDeRham Crystalline.PrimeTower07Q9
open scoped TensorProduct

universe u

namespace Crystalline.CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p) (g : E.Hom E')
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)
  (hδ : ∀ x : V.carrier 0,
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
  (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
    (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
    (E.isGradedLeibniz p 0))

include hbeta in
/-- **The de Rham map in degree `0` of the base change of a cosimplicial pair of base-change
connections has the cone of the base change map**: if `q` kills the cones of the base change
maps along `D̂(0) → D̂'(0)`, it kills the cone of `(pairPullbackHom07Q9 …).degreeDeRhamMap 0`. -/
theorem coneKilledNat07Q9_pairPullbackHom {q : ℤ}
    (h : letI := g.completedAlgebra07Q9 p 0
      BaseChangeConeKilled07Q9 p (E.completedRing p 0) (E'.completedRing p 0)
        (fun i ↦ E.forms p i 0) (fun i ↦ E'.forms p i 0) (fun i ↦ g.formsMap p 0 i)
        (E.wedge p 0) (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0) (E.differential p 0)
        (E'.differential p 0) (completedFormsDifferential_add p A _)
        (completedFormsDifferential_mul p A _) (g.formsMap_differential07Q9 p 0)
        (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0)
        (fun i ω η ↦ g.formsMap_wedge p 0 i ω η) (fun i ω ↦ g.formsMap_deRham p 0 i ω) q) :
    ConeKilledNat07Q9 q ((V.pairPullbackHom07Q9 g nabla beta hbeta hδ hint).degreeDeRhamMap 0) := by
  let := g.completedAlgebra07Q9 p 0
  rw [CosimplicialCompletedPair.Hom.degreeDeRhamMap_eq_comparisonComplexHom07Q9]
  have hsq := isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection p A
    (E.dividedPowers 0) nabla hint
  have hsq' := g.isSquareZero_baseChange07Q9 p 0 (V.carrier 0) nabla hint
  refine coneKilledNat07Q9_comparison_congr (nabla₂ := nabla)
    (nabla₂' := CompletedConnection.baseChange p (E.completedRing p 0) (E'.completedRing p 0)
      (V.carrier 0) (E.forms p 1 0) (E'.forms p 1 0) (E'.differential p 0) (g.formsMap p 0 1) nabla
      (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
      (g.formsMap_differential07Q9 p 0))
    (h₁ := V.baseChangeConnection_zero nabla beta hbeta)
    (h₂ := (V.pullback07Q9 g).baseChangeConnection_zero _ _ (V.pullbackBeta07Q9_tmul g beta hbeta))
    (hsq₂ := hsq) (hsq₂' := hsq')
    (hnabla₂ := baseChange_inclusion07Q9 p _ _ (V.carrier 0) _ _ _ _ nabla _ _ _) (h := ?_) ..
  exact h (V.carrier 0) nabla hint hsq hsq'

/-- The completed components of a morphism of cosimplicial divided power algebras are maps of
`A`-algebras. -/
theorem _root_.Crystalline.CosimplicialDPAlgebra.Hom.completedRingMap_algebraMap07Q9
    (b : ℕ) (a : A) :
    g.completedRingMap p b (algebraMap A (E.completedRing p b) a) =
      algebraMap A (E'.completedRing p b) a := by
  rw [AdicCompletion.algebraMap_apply]
  exact (adicCompletionRingMap_of _ _ _).trans
    ((congrArg (AdicCompletion.of _ _) ((g.app b).commutes a)).trans
      (AdicCompletion.algebraMap_apply _ a).symm)

include hbeta in
/-- **The cone of the de Rham map in degree `0` of the base change along `g` is killed by
`p ^ n`**, as soon as `D̂(0) → D̂'(0)` is identified with a tower of `n` completed `p`-th root
extensions of [Stacks, Tag 07N1] along which, one step at a time, the cones are killed by `p`,
and the completed forms of `E(0)` and `E'(0)` are those of their completions. -/
theorem coneKilledNat07Q9_pairPullbackHom_of_tower
    (hp : IsNilpotent (Ideal.Quotient.mk (E.ideal 0) (p : E.carrier 0)))
    (hp' : IsNilpotent (Ideal.Quotient.mk (E'.ideal 0) (p : E'.carrier 0)))
    (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] {n : ℕ} (T : PrimeTower07Q9 p B n)
    (θ₀ : E.completedRing p 0 ≃ₐ[A] (B : Type u))
    (hθ₀ : IsDPMorphism (completedDividedPowers (E.ideal 0) (E.dividedPowers 0) p hp).1
      B.dividedPowers θ₀.toAlgHom.toRingHom)
    (hθ₀' : IsDPMorphism B.dividedPowers
      (completedDividedPowers (E.ideal 0) (E.dividedPowers 0) p hp).1 θ₀.symm.toAlgHom.toRingHom)
    (Θ : E'.completedRing p 0 ≃+* (T.top : Type u))
    (hΘ : IsDPMorphism (completedDividedPowers (E'.ideal 0) (E'.dividedPowers 0) p hp').1
      T.top.dividedPowers Θ.toRingHom)
    (hΘ' : IsDPMorphism T.top.dividedPowers
      (completedDividedPowers (E'.ideal 0) (E'.dividedPowers 0) p hp').1 Θ.symm.toRingHom)
    (hcomm : ∀ x, Θ (g.completedRingMap p 0 x) = T.toTop (θ₀ x))
    (hstep : ∀ (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (hp : p ≠ 0)
      (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
      (lam : (B : Type u)),
      GenuineBaseChangeConeKilled07Q9 p A (B : Type u) B.dividedPowers
        (completedPrimeStep07Q9 B p hp hB lam : Type u)
        (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
        (IsScalarTower.toAlgHom A (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u))
        (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) (fun _ ↦ rfl) (p : ℤ))
    (hbij : ∀ i, Function.Bijective (completionFormsMap07Q9 p A (E.dividedPowers 0) hp i))
    (hbij' : ∀ i, Function.Bijective (completionFormsMap07Q9 p A (E'.dividedPowers 0) hp' i)) :
    ConeKilledNat07Q9 ((p : ℤ) ^ n)
      ((V.pairPullbackHom07Q9 g nabla beta hbeta hδ hint).degreeDeRhamMap 0) := by
  let : Algebra A (T.top : Type u) :=
    (Θ.toRingHom.comp (algebraMap A (E'.completedRing p 0))).toAlgebra
  have hc : ∀ a : A, T.toTop (algebraMap A (B : Type u) a) = algebraMap A (T.top : Type u) a := by
    intro a
    rw [← θ₀.commutes a, ← hcomm]
    exact congrArg Θ (g.completedRingMap_algebraMap07Q9 (p := p) 0 a)
  let := algebraTop07Q9 T
  let θ' : E'.completedRing p 0 ≃ₐ[A] (T.top : Type u) := AlgEquiv.ofRingEquiv (f := Θ)
    (fun _ ↦ rfl)
  refine coneKilledNat07Q9_pairPullbackHom V g nabla beta hbeta hδ hint ?_
  exact baseChangeConeKilled07Q9_of_genuine p A g hp hp' (B : Type u) B.dividedPowers
    (T.top : Type u) T.top.dividedPowers (toTopAlgHom07Q9 T hc) T.toTop.isDPMorphism
    (fun _ ↦ rfl) θ₀ hθ₀ hθ₀' θ' hΘ hΘ' hcomm hbij hbij'
    (genuineBaseChangeConeKilled07Q9_tower A hstep T hc)

end Crystalline.CosimplicialCompletedModule

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry PrimeTower07Q9

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {n : ℕ}
  (ch : AlphaPChain S.p Γ(S.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
  (he : f.app W ≫ e.hom = ch.toTop)
  (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F)
  [IsAffine (restrict S V W hVW).X] [IsAffine (restrict S V W hVW).S.scheme]

/-- The completed ring `D'(0)` of the chain presentation is an `A`-algebra through its
identification with the last stage of the tower. -/
abbrev chainTowerTopAlgebra07Q9 :
    Algebra ((openAffineSituation07Q9 S hW hVW).A : Type u)
      ((chainEnvelopeTower07Q9 S hW hVW ch rfl).top : Type u) :=
  ((chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he rfl).hom.toRingHom.comp
    (algebraMap ((openAffineSituation₂07Q9 S hVW f hW₂).A : Type u)
      ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)).completedRing S.p 0))).toAlgebra

/-- An isomorphism of divided power rings, as a ring isomorphism. -/
def dpIsoRingEquiv07Q9 {X Y : DividedPowerRing.{u}} (Θ : X ≅ Y) :
    (X : Type u) ≃+* (Y : Type u) where
  toFun := Θ.hom
  invFun := Θ.inv
  left_inv x := congrArg (fun q : X ⟶ X ↦ q x) Θ.hom_inv_id
  right_inv y := congrArg (fun q : Y ⟶ Y ↦ q y) Θ.inv_hom_id
  map_mul' := map_mul Θ.hom.toRingHom
  map_add' := map_add Θ.hom.toRingHom

include he in
/-- **The cone of the row-zero map over a chain open is killed by `p ^ n`**, given the one-step
statement of [Stacks, Tag 07N1] for the genuine completed forms and the bijectivity of the
comparison of the completed forms of a divided power ring with those of its completion
([Stacks, Tag 07KK]). -/
theorem smul_id_homology_chainRowZero07Q9_of
    (hstep : ∀ (B : DividedPowerRing.{u}) [Algebra ((openAffineSituation07Q9 S hW hVW).A : Type u)
      (B : Type u)] (hp : S.p ≠ 0)
      (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((S.p : ℕ) : (B : Type u))))
      (lam : (B : Type u)),
      GenuineBaseChangeConeKilled07Q9 S.p ((openAffineSituation07Q9 S hW hVW).A : Type u)
        (B : Type u) B.dividedPowers (completedPrimeStep07Q9 B S.p hp hB lam : Type u)
        (completedPrimeStep07Q9 B S.p hp hB lam).dividedPowers
        (IsScalarTower.toAlgHom _ (B : Type u) (completedPrimeStep07Q9 B S.p hp hB lam : Type u))
        (isDPMorphism_completedPrimeStep07Q9 _ B S.p hp hB lam) (fun _ ↦ rfl) (S.p : ℤ))
    (hbij : ∀ (B : Type u) [CommRing B] [Algebra ((openAffineSituation07Q9 S hW hVW).A : Type u) B]
      {J : Ideal B} (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (S.p : B)))
      (i : ℕ), Function.Bijective
        (completionFormsMap07Q9 S.p ((openAffineSituation07Q9 S hW hVW).A : Type u) hJ hp i))
    (j : ℤ) :
    ((S.p ^ n : ℕ) : ℤ) • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((chainPullbackHom07Q9 S hW hVW f hW₂ ch e F hF).degreeDeRhamMap 0)
      ComplexShape.embeddingUpNat)).homology j) = 0 := by
  let : Algebra ((openAffineSituation07Q9 S hW hVW).A : Type u)
      (completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _) 0 : Type u) :=
    inferInstanceAs (Algebra _ ((envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))).completedRing S.p 0))
  have hp := (completedTensorPowerDifferential (openAffineSituation07Q9 S hW hVW)
    (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
    (canonicalPresentation_surjective _) 0).1
  have hp' := (completedTensorPowerDifferential (openAffineSituation₂07Q9 S hVW f hW₂)
    (chainPresentation07Q9 S hW hVW f hW₂ ch e)
    (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0).1
  rw [Nat.cast_pow]
  exact (CosimplicialCompletedModule.coneKilledNat07Q9_pairPullbackHom_of_tower _
    (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e) _ _ _ _ _ hp hp' _
    (chainEnvelopeTower07Q9 S hW hVW ch rfl) AlgEquiv.refl
    (DPMorphism.id _).isDPMorphism (DPMorphism.id _).isDPMorphism
    (dpIsoRingEquiv07Q9 (chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he rfl))
    (chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he rfl).hom.isDPMorphism
    (chainEnvelopeTowerIso07Q9 S hW hVW f hW₂ ch e he rfl).inv.isDPMorphism
    (chainEnvelopeTowerIso07Q9_hom_completedEnvelopeMap S hW hVW f hW₂ ch e he rfl) hstep
    (hbij _ _ hp)
    (@hbij _ _ ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂)
      (chainPresentation07Q9 S hW hVW f hW₂ ch e)).algebra 0) _ _ hp')).homology j

include he in
/-- **[Stacks, Tag 07Q9], the row-zero step over a chain open.**  Let `W ⊆ X` be an affine open
over which `f` is a chain of `n` successive `α_p`-extensions (`ch`, `e`, `he`) and `ℱ` a crystal
in quasi-coherent modules.  The morphism of the rows zero of the double complexes of
[Stacks, Tag 07LG] of `ℱ` over `W` and of its pullback over `f⁻¹(W)` — the base change map
`M ⊗^∧_D Ω^•_D ⟶ M' ⊗^∧_{D'} Ω^•_{D'}` along `D(0) → D'(0)` — has the cohomology of its cone
killed by `p ^ n`: `D(0) → D'(0)` is a tower of `n` completed `p`-th root extensions
(`chainEnvelopeTowerIso07Q9`), along each of which the cone is killed by `p`
([Stacks, Tag 07N1], `genuineBaseChangeConeKilled07Q9_completedPrimeStep`), the forms of the
envelopes being identified with those of their completions by [Stacks, Tag 07KK]
(`bijective_completionFormsMap07Q9`). -/
theorem smul_id_homology_chainRowZero07Q9 (j : ℤ) :
    ((S.p ^ n : ℕ) : ℤ) • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((chainPullbackHom07Q9 S hW hVW f hW₂ ch e F hF).degreeDeRhamMap 0)
      ComplexShape.embeddingUpNat)).homology j) = 0 :=
  let : Algebra (IntegersAtPrime S.p) ((openAffineSituation07Q9 S hW hVW).A : Type u) :=
    (openAffineSituation07Q9 S hW hVW).algebraAtPrime
  smul_id_homology_chainRowZero07Q9_of S hW hVW f hW₂ ch e he F hF
    (fun B _ hp hB lam ↦ genuineBaseChangeConeKilled07Q9_completedPrimeStep _ S.p B hp hB lam)
    (fun _ _ _ _ hJ hp i ↦ bijective_completionFormsMap07Q9 S.p _ hJ hp i) j

end Crystalline.GlobalCrystallineSituation.SmallSite
