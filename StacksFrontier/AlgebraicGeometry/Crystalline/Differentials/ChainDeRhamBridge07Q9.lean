module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ChainDeRham07Q9

/-!
# From the genuine completed forms to the forms of a cosimplicial divided power algebra

The forms `Ω̂^a_{D(b)}` of a cosimplicial divided power algebra `E`
(`Crystalline.CosimplicialDPAlgebra.forms`) are the `p`-adic completions of the divided power
forms of the **uncompleted** carrier `E(b)`, read over the completion `Ê(b)`.  The completed
`p`-th root extensions of [Stacks, Lemma 60.25.3, Tag 07N1] are stated with the completed forms of
the **completed** divided power ring itself.  This file transports the annihilation of the cones
of the base change maps from the second convention to the first, along isomorphisms of divided
power rings `θ₀ : Ê(0) ≅ D₀` and `θ' : Ê'(0) ≅ D'` compatible with a morphism `g : E ⟶ E'` and
a divided power morphism `f : D₀ → D'`, given that the comparison of the completed forms of
`E(0)` (resp. `E'(0)`) with those of its completion is bijective
([Stacks, Lemma 60.20.1, Tag 07KK]).

## Main definitions

* `Crystalline.CompletedDeRham.completionFormsLinear07Q9` — the comparison
  `Ω̂^i_{E(0)} → Ω̂^i_{Ê(0)}`, linear over `Ê(0)`.

## Main results

* `Crystalline.CompletedDeRham.baseChangeConeKilled07Q9_of_genuine` — the transport.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

namespace CompletedDeRham

section Linear

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The comparison of the completed forms of `B` with those of its completion `B̂`, as a
`B̂`-linear map.** -/
def completionFormsLinear07Q9 (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerForms p A (completedDividedPowers J hJ p hp).1 i where
  toFun := completionFormsMap07Q9 p A hJ hp i
  map_add' := map_add _
  map_smul' := completionFormsMap07Q9_smul p A hJ hp i

/-- The `B̂`-linear comparison has the values of the semilinear one. -/
@[simp] theorem completionFormsLinear07Q9_apply (i : ℕ) (ω : completedDividedPowerForms p A hJ i) :
    completionFormsLinear07Q9 p A hJ hp i ω = completionFormsMap07Q9 p A hJ hp i ω :=
  rfl

end Linear

section IsoForms

variable (p : ℕ) (A : Type u) [CommRing A] {R S : Type u} [CommRing R] [CommRing S] [Algebra A R]
  [Algebra A S] {I : Ideal R} {K : Ideal S} (hI : DividedPowers I) (hK : DividedPowers K)
  (θ : R ≃ₐ[A] S) (hθ : IsDPMorphism hI hK θ.toAlgHom.toRingHom)
  (hθ' : IsDPMorphism hK hI θ.symm.toAlgHom.toRingHom)

include hθ' in
/-- The comparisons of completed forms along a divided power isomorphism and its inverse are
inverse to each other. -/
theorem completedMapDifferentialForms_symm_apply07Q9 (i : ℕ)
    (ω : completedDividedPowerForms p A hI i) :
    completedMapDifferentialForms p A hK hI θ.symm.toAlgHom hθ' i
        (completedMapDifferentialForms p A hI hK θ.toAlgHom hθ i ω) = ω := by
  have hid : θ.symm.toAlgHom.comp θ.toAlgHom = AlgHom.id A R := AlgHom.ext fun x ↦ by simp
  have hgf : IsDPMorphism hI hI (θ.symm.toAlgHom.comp θ.toAlgHom).toRingHom := by
    rw [hid]
    exact (DPMorphism.id hI).isDPMorphism
  rw [← completedMapDifferentialForms_comp p A hI hK θ.toAlgHom hθ hI θ.symm.toAlgHom hθ'
    hgf i ω, completedMapDifferentialForms_congr p A hI hI hid hgf
      (DPMorphism.id hI).isDPMorphism]
  exact completedMapDifferentialForms_id p A hI i _ ω

end IsoForms

section Bridge

variable (p : ℕ) (A : Type u) [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} (g : E.Hom E')
  (hp : IsNilpotent (Ideal.Quotient.mk (E.ideal 0) (p : E.carrier 0)))
  (hp' : IsNilpotent (Ideal.Quotient.mk (E'.ideal 0) (p : E'.carrier 0)))
  (D₀ : Type u) [CommRing D₀] [Algebra A D₀] {J₀ : Ideal D₀} (δ₀ : DividedPowers J₀)
  (D' : Type u) [CommRing D'] [Algebra A D'] {J' : Ideal D'} (δ' : DividedPowers J')
  [Algebra D₀ D'] (f : D₀ →ₐ[A] D') (hf : IsDPMorphism δ₀ δ' f.toRingHom)
  (hfa : ∀ x, f.toRingHom x = algebraMap D₀ D' x)
  (θ₀ : E.completedRing p 0 ≃ₐ[A] D₀)
  (hθ₀ : IsDPMorphism (completedDividedPowers (E.ideal 0) (E.dividedPowers 0) p hp).1 δ₀
    θ₀.toAlgHom.toRingHom)
  (hθ₀' : IsDPMorphism δ₀ (completedDividedPowers (E.ideal 0) (E.dividedPowers 0) p hp).1
    θ₀.symm.toAlgHom.toRingHom)
  (θ' : E'.completedRing p 0 ≃ₐ[A] D')
  (hθ' : IsDPMorphism (completedDividedPowers (E'.ideal 0) (E'.dividedPowers 0) p hp').1 δ'
    θ'.toAlgHom.toRingHom)
  (hθ'' : IsDPMorphism δ' (completedDividedPowers (E'.ideal 0) (E'.dividedPowers 0) p hp').1
    θ'.symm.toAlgHom.toRingHom)
  (hθ : ∀ x, θ' (g.completedRingMap p 0 x) = f (θ₀ x))
  (hbij : ∀ i, Function.Bijective (completionFormsMap07Q9 p A (E.dividedPowers 0) hp i))
  (hbij' : ∀ i, Function.Bijective (completionFormsMap07Q9 p A (E'.dividedPowers 0) hp' i))

/-- **The identification of the forms of `E` in degree `0` with the genuine forms of `D₀`**:
the comparison with the forms of the completion, followed by the comparison along `θ₀`. -/
def bridgeForms07Q9 (i : ℕ) :
    E.forms p i 0 →ₛₗ[(θ₀.toRingEquiv : E.completedRing p 0 →+* D₀)]
      completedDividedPowerForms p A δ₀ i :=
  semilinearCast07Q9 (fun _ ↦ rfl) (semilinearComp
    (completedMapDifferentialForms p A _ δ₀ θ₀.toAlgHom hθ₀ i)
    (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i))

include hbij in
/-- The inverse of `Crystalline.CompletedDeRham.bridgeForms07Q9`. -/
def bridgeFormsInv07Q9 (i : ℕ) :
    completedDividedPowerForms p A δ₀ i →ₛₗ[(θ₀.toRingEquiv.symm : D₀ →+* E.completedRing p 0)]
      E.forms p i 0 :=
  semilinearCast07Q9 (fun _ ↦ rfl) (semilinearComp
    (LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i)
      (hbij i)).symm.toLinearMap
    (completedMapDifferentialForms p A δ₀ _ θ₀.symm.toAlgHom hθ₀' i))

/-- The identification of forms, as a formula. -/
theorem bridgeForms07Q9_apply (i : ℕ) (ω : E.forms p i 0) :
    bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i ω =
      completedMapDifferentialForms p A _ δ₀ θ₀.toAlgHom hθ₀ i
        (completionFormsMap07Q9 p A (E.dividedPowers 0) hp i ω) :=
  rfl

/-- The inverse identification of forms, as a formula. -/
theorem bridgeFormsInv07Q9_apply (i : ℕ) (ω : completedDividedPowerForms p A δ₀ i) :
    bridgeFormsInv07Q9 p A hp D₀ δ₀ θ₀ hθ₀' hbij i ω =
      (LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i)
        (hbij i)).symm (completedMapDifferentialForms p A δ₀ _ θ₀.symm.toAlgHom hθ₀' i ω) :=
  rfl

/-- The inverse identification undoes the identification. -/
theorem bridgeFormsInv07Q9_bridgeForms07Q9 (i : ℕ) (ω : E.forms p i 0) :
    bridgeFormsInv07Q9 p A hp D₀ δ₀ θ₀ hθ₀' hbij i (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i ω) =
      ω :=
  (bridgeFormsInv07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀' hbij i _).trans <|
    (congrArg (fun z ↦ (LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0)
      hp i) (hbij i)).symm (completedMapDifferentialForms p A δ₀ _ θ₀.symm.toAlgHom hθ₀' i z))
      (bridgeForms07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀ i ω)).trans <|
    (congrArg (LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i)
      (hbij i)).symm (completedMapDifferentialForms_symm_apply07Q9 p A _ δ₀ θ₀ hθ₀ hθ₀' i
        (completionFormsMap07Q9 p A (E.dividedPowers 0) hp i ω))).trans
    ((LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i)
      (hbij i)).symm_apply_apply ω)

/-- The identification undoes the inverse identification. -/
theorem bridgeForms07Q9_bridgeFormsInv07Q9 (i : ℕ) (ω : completedDividedPowerForms p A δ₀ i) :
    bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i (bridgeFormsInv07Q9 p A hp D₀ δ₀ θ₀ hθ₀' hbij i ω) =
      ω :=
  (bridgeForms07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀ i _).trans <|
    (congrArg (fun z ↦ completedMapDifferentialForms p A _ δ₀ θ₀.toAlgHom hθ₀ i
      (completionFormsMap07Q9 p A (E.dividedPowers 0) hp i z))
      (bridgeFormsInv07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀' hbij i ω)).trans <|
    (congrArg (completedMapDifferentialForms p A _ δ₀ θ₀.toAlgHom hθ₀ i)
      ((LinearEquiv.ofBijective (completionFormsLinear07Q9 p A (E.dividedPowers 0) hp i)
        (hbij i)).apply_symm_apply
        (completedMapDifferentialForms p A δ₀ _ θ₀.symm.toAlgHom hθ₀' i ω))).trans
    (completedMapDifferentialForms_symm_apply07Q9 p A δ₀ _ θ₀.symm hθ₀' hθ₀ i ω)

/-- The identification of forms carries the universal differential to the universal
differential. -/
theorem bridgeForms07Q9_differential (x : E.completedRing p 0) :
    bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ 1 (E.differential p 0 x) =
      completedDividedPowerDifferentialOnRing p A δ₀ (θ₀.toRingEquiv x) := by
  refine (bridgeForms07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀ 1 _).trans ?_
  refine (congrArg (completedMapDifferentialForms p A _ δ₀ θ₀.toAlgHom hθ₀ 1)
    (completionFormsMap07Q9_differential p A (E.dividedPowers 0) hp x)).trans ?_
  exact completedMapDifferentialForms_differentialOnRing p A _ δ₀ θ₀.toAlgHom hθ₀ x

/-- The identification of forms respects the wedge product. -/
theorem bridgeForms07Q9_wedge (i : ℕ) (ω : E.forms p i 0) (η : E.forms p 1 0) :
    bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ (i + 1) (E.wedge p 0 i ω η) =
      completedDividedPowerWedgeOnRing p A δ₀ i (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i ω)
        (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ 1 η) := by
  simp only [bridgeForms07Q9_apply]
  exact (congrArg _ (completedMapDifferentialForms_wedge p A _ _ _ _ i ω η)).trans
    (completedMapDifferentialForms_wedge p A _ _ _ _ i _ _)

/-- The identification of forms commutes with the de Rham differential. -/
theorem bridgeForms07Q9_deRham (i : ℕ) (ω : E.forms p i 0) :
    bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ (i + 1) (E.deRham p 0 i ω) =
      completedDividedPowerDeRham p A δ₀ i (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i ω) := by
  simp only [bridgeForms07Q9_apply]
  exact (congrArg _ (completedMapDifferentialForms_deRham p A _ _ _ _ i ω)).trans
    (completedMapDifferentialForms_deRham p A _ _ _ _ i _)

include hθ in
/-- The identifications of forms are compatible with the comparisons of forms of `g` and of `f`.
Both sides are comparisons of completed forms along `E(0) → D'`, along the two composites
`E(0) → E'(0) → Ê'(0) → D'` and `E(0) → Ê(0) → D₀ → D'`, which agree. -/
theorem bridgeForms07Q9_comm (i : ℕ) (ω : E.forms p i 0) :
    bridgeForms07Q9 p A hp' D' δ' θ' hθ' i (g.formsMap p 0 i ω) =
      genuineFormsMap07Q9 p A D₀ δ₀ D' δ' f hf hfa i (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ i ω) := by
  have hcomp : θ'.toAlgHom.comp ((completionDPAlgHom (A := A) p).comp
      (g.app 0)) = f.comp (θ₀.toAlgHom.comp (completionDPAlgHom (A := A) p)) :=
    AlgHom.ext fun x ↦ by
      have hx : g.completedRingMap p 0 (AdicCompletion.of _ _ x) =
          AdicCompletion.of _ _ (g.app 0 x) :=
        adicCompletionRingMap_of _ _ x
      simp only [AlgHom.comp_apply]
      exact (congrArg θ' hx.symm).trans (hθ _)
  have hc := completionDPAlgHom_isDPMorphism (A := A) _ (E.dividedPowers 0) p hp
  have hc' := completionDPAlgHom_isDPMorphism (A := A) _ (E'.dividedPowers 0) p hp'
  have hg := IsDPMorphism.comp _ hc' (g.isDPMorphism 0)
  have hθg := IsDPMorphism.comp _ hθ' hg
  have hθc := IsDPMorphism.comp _ hθ₀ hc
  have hfc := IsDPMorphism.comp _ hf hθc
  have hc := completionDPAlgHom_isDPMorphism (A := A) _ (E.dividedPowers 0) p hp
  have hc' := completionDPAlgHom_isDPMorphism (A := A) _ (E'.dividedPowers 0) p hp'
  have hg := IsDPMorphism.comp _ hc' (g.isDPMorphism 0)
  have hθg := IsDPMorphism.comp _ hθ' hg
  have hθc := IsDPMorphism.comp _ hθ₀ hc
  have hfc := IsDPMorphism.comp _ hf hθc
  have h1 := completedMapDifferentialForms_comp p A (E.dividedPowers 0) (E'.dividedPowers 0)
    (g.app 0) (g.isDPMorphism 0) _ (completionDPAlgHom (A := A) p) hc' hg i ω
  have h2 := completedMapDifferentialForms_comp p A (E.dividedPowers 0) _
    ((completionDPAlgHom (A := A) p).comp (g.app 0)) hg δ' θ'.toAlgHom hθ' hθg i ω
  have h3 := completedMapDifferentialForms_comp p A (E.dividedPowers 0) _
    (completionDPAlgHom (A := A) p) hc δ₀ θ₀.toAlgHom hθ₀ hθc i ω
  have h4 := completedMapDifferentialForms_comp p A (E.dividedPowers 0) δ₀
    (θ₀.toAlgHom.comp (completionDPAlgHom (A := A) p)) hθc δ' f hf hfc i ω
  have h5 := completedMapDifferentialForms_congr p A (E.dividedPowers 0) δ' hcomp hθg hfc i ω
  refine (bridgeForms07Q9_apply p A hp' D' δ' θ' hθ' i _).trans ?_
  refine Eq.trans ?_ (congrArg (genuineFormsMap07Q9 p A D₀ δ₀ D' δ' f hf hfa i)
    (bridgeForms07Q9_apply p A hp D₀ δ₀ θ₀ hθ₀ i ω)).symm
  refine (congrArg (completedMapDifferentialForms p A _ δ' θ'.toAlgHom hθ' i) h1.symm).trans ?_
  refine h2.symm.trans (h5.trans ?_)
  exact h4.trans (congrArg (completedMapDifferentialForms p A δ₀ δ' f hf i) h3)

include hθ₀ hθ₀' hθ' hθ'' hθ hbij hbij' in
/-- **The annihilation of the base change cones transports from the genuine completed forms to
the forms of the cosimplicial divided power algebras**: if `q` kills the cones of the base change
maps along `f : D₀ → D'` for the genuine completed forms of `D₀` and `D'`, then `q` kills the
cones of the base change maps along `Ê(0) → Ê'(0)` for the forms `Ω̂_{E(0)}`, `Ω̂_{E'(0)}` and
the comparison of forms of `g`. -/
theorem baseChangeConeKilled07Q9_of_genuine {q : ℤ}
    (h : GenuineBaseChangeConeKilled07Q9 p A D₀ δ₀ D' δ' f hf hfa q) :
    letI := (g.completedRingMap p 0).toAlgebra
    BaseChangeConeKilled07Q9 p (E.completedRing p 0) (E'.completedRing p 0)
      (fun i ↦ E.forms p i 0) (fun i ↦ E'.forms p i 0) (fun i ↦ g.formsMap p 0 i) (E.wedge p 0)
      (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0) (E.differential p 0) (E'.differential p 0)
      (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
      (g.formsMap_differential07Q9 p 0) (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0)
      (fun i ω η ↦ g.formsMap_wedge p 0 i ω η) (fun i ω ↦ g.formsMap_deRham p 0 i ω) q := by
  let := (g.completedRingMap p 0).toAlgebra
  exact baseChangeConeKilled07Q9_of_iso p θ₀.toRingEquiv θ'.toRingEquiv
    (fun x ↦ (hθ x).trans (hfa _)) _ _ _ _ _ _
    (bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀) (bridgeFormsInv07Q9 p A hp D₀ δ₀ θ₀ hθ₀' hbij)
    (bridgeForms07Q9 p A hp' D' δ' θ' hθ') (bridgeFormsInv07Q9 p A hp' D' δ' θ' hθ'' hbij')
    (bridgeFormsInv07Q9_bridgeForms07Q9 p A hp D₀ δ₀ θ₀ hθ₀ hθ₀' hbij)
    (bridgeForms07Q9_bridgeFormsInv07Q9 p A hp D₀ δ₀ θ₀ hθ₀ hθ₀' hbij)
    (bridgeFormsInv07Q9_bridgeForms07Q9 p A hp' D' δ' θ' hθ' hθ'' hbij')
    (bridgeForms07Q9_bridgeFormsInv07Q9 p A hp' D' δ' θ' hθ' hθ'' hbij')
    (bridgeForms07Q9_comm p A g hp hp' D₀ δ₀ D' δ' f hf hfa θ₀ hθ₀ θ' hθ' hθ)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (bridgeForms07Q9_differential p A hp D₀ δ₀ θ₀ hθ₀)
    (bridgeForms07Q9_differential p A hp' D' δ' θ' hθ') _ _ _ _ _ _ _ _
    (bridgeForms07Q9_wedge p A hp D₀ δ₀ θ₀ hθ₀) (bridgeForms07Q9_deRham p A hp D₀ δ₀ θ₀ hθ₀)
    (bridgeForms07Q9_wedge p A hp' D' δ' θ' hθ') (bridgeForms07Q9_deRham p A hp' D' δ' θ' hθ') h

include hθ₀ hθ₀' hθ' hθ'' hθ hbij hbij' in
/-- **The cohomology of the cone of the base change map along `Ê(0) → Ê'(0)` is killed by `q`**,
for every module with an integrable completed connection over `Ê(0)`, as soon as the cones of
the base change maps along `f : D₀ → D'` are killed by `q` for the genuine completed forms. -/
theorem homology_mappingCone_baseChange07Q9_of_genuine {q : ℤ}
    (h : GenuineBaseChangeConeKilled07Q9 p A D₀ δ₀ D' δ' f hf hfa q) (M : Type u)
    [AddCommGroup M] [Module (E.completedRing p 0) M]
    (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0) M)
    (hint : HasIntegrableConnection p (E.completedRing p 0) (fun i ↦ E.forms p i 0)
      (E.wedge p 0) (E.deRham p 0) M nabla (E.isGradedLeibniz p 0))
    (hsq : IsSquareZero p (E.completedRing p 0) (fun i ↦ E.forms p i 0) (E.wedge p 0)
      (E.deRham p 0) M nabla (E.isGradedLeibniz p 0)) (j : ℤ) :
    letI := (g.completedRingMap p 0).toAlgebra
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (baseChangeComplexHom p (E.completedRing p 0) (E'.completedRing p 0) M
        (fun i ↦ E.forms p i 0) (fun i ↦ E'.forms p i 0) (fun i ↦ g.formsMap p 0 i) (E.wedge p 0)
        (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0) (E'.differential p 0) nabla
        (completedFormsDifferential_add p A _) (completedFormsDifferential_mul p A _)
        (g.formsMap_differential07Q9 p 0) (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0)
        (fun i ω η ↦ g.formsMap_wedge p 0 i ω η) (fun i ω ↦ g.formsMap_deRham p 0 i ω) hsq
        (g.isSquareZero_baseChange07Q9 p 0 M nabla hint))
      ComplexShape.embeddingUpNat)).homology j) = 0 :=
  let := (g.completedRingMap p 0).toAlgebra
  ConeKilledNat07Q9.homology (baseChangeConeKilled07Q9_of_genuine p A g hp hp' D₀ δ₀ D' δ' f hf
    hfa θ₀ hθ₀ hθ₀' θ' hθ' hθ'' hθ hbij hbij' h M nabla hint hsq _) j

end Bridge

end CompletedDeRham

end Crystalline

end
