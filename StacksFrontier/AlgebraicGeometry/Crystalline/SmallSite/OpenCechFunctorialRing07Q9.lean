module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.EnvelopeCosimplicialComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Comparison07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechSystem07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PresentationMorphism07Q9

/-!
# The ring maps `D(n) → D'(n)` of a morphism of presentations over `f : X' ⟶ X`

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, and a morphism of schemes `f : X' ⟶ X` with `W' = f⁻¹(W)` affine.  The
situation `X'/S` over the same divided power base is
`Crystalline.GlobalCrystallineSituation.SmallSite.overSituation`.  The restriction
`f^♯ : Γ(W, ⊤) → Γ(W', ⊤)` and the identity of `Γ(V, ⊤)` form a morphism of the affine
situations `(Γ(V, ⊤), Γ(W, ⊤))` and `(Γ(V, ⊤), Γ(W', ⊤))`, and a ring map `r : P → P'` of
polynomial presentations of `Γ(W, ⊤)` and `Γ(W', ⊤)` compatible with `f^♯` induces maps of the
completed divided power envelopes `D(n) → D'(n)` of the tensor power presentations, and of their
finite levels `D(n)/(p)^{N + e + N'} → D'(n)/(p)^{N' + e}`.

This file builds those ring maps and proves that they extend the tensor powers of `r`, are over
`Γ(V, ⊤)`, are compatible with `f^♯` on the quotients by the divided power ideals, and commute
with the cosimplicial structure maps and with the level drops.

## Main definitions

* `openAffineSituationHom07Q9` — the morphism of affine situations induced by `f`.
* `envelopeRingMap07Q9` — the divided power morphism `D(n) ⟶ D'(n)`.
* `levelRingMap07Q9` — the induced map of finite levels, with the shift `N'` of the cutoff.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

/-- The structure morphism of the restriction to a pair of opens, followed by the inclusion of
the open of the base, is the inclusion of the open of `X` followed by the structure morphism. -/
theorem sourceToBase_restrict_comp_ι (S : GlobalCrystallineSituation.{u}) (V : S.S.scheme.Opens)
    (W : S.X.Opens) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) :
    sourceToBase (restrict S V W hVW) ≫ (restrictSι S V W hVW).hom =
      restrictXι S V W hVW ≫ sourceToBase S := by
  simp only [sourceToBase, Category.assoc]
  rw [← DividedPowerScheme.closedFiberMap_comp_closedFiberι (restrictSι S V W hVW),
    reassoc_of% restrict_changeBase_condition' S V W hVW]

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {X' : Scheme.{u}} (f : X' ⟶ S.X)

include hVW in
/-- The preimage of `W` maps into `V` in the situation `X'/S`. -/
theorem preimage_le_overSituation07Q9 :
    f ⁻¹ᵁ W ≤ sourceToBase (overSituation S f) ⁻¹ᵁ V := fun _ hx ↦ hVW hx

/-- The restriction `f⁻¹(W) ⟶ W` of `f`, as a morphism of the thickened spaces of the two
restricted situations. -/
def restrictMap07Q9 : (restrict (overSituation S f) V (f ⁻¹ᵁ W)
    (preimage_le_overSituation07Q9 S hVW f)).X ⟶ (restrict S V W hVW).X :=
  f ∣_ W

/-- The restriction of `f` commutes with the inclusions of the two opens. -/
theorem restrictMap07Q9_comp_restrictXι :
    restrictMap07Q9 S hVW f ≫ restrictXι S V W hVW =
      restrictXι (overSituation S f) V (f ⁻¹ᵁ W) (preimage_le_overSituation07Q9 S hVW f) ≫ f :=
  morphismRestrict_ι f W

/-- The structure morphism of the restricted situation `(p, S|_V, f⁻¹(W))` of `X'/S` factors
through the restriction of `f`. -/
theorem sourceToBase_restrict_overSituation07Q9 :
    sourceToBase (restrict (overSituation S f) V (f ⁻¹ᵁ W)
        (preimage_le_overSituation07Q9 S hVW f)) =
      restrictMap07Q9 S hVW f ≫ sourceToBase (restrict S V W hVW) := by
  have := isOpenImmersion_restrictSι_hom S V W hVW
  refine (cancel_mono (restrictSι S V W hVW).hom).mp ?_
  have h₁ := sourceToBase_restrict_comp_ι (overSituation S f) V (f ⁻¹ᵁ W)
    (preimage_le_overSituation07Q9 S hVW f)
  have h₂ := sourceToBase_restrict_comp_ι S V W hVW
  have key : restrictXι (overSituation S f) V (f ⁻¹ᵁ W) (preimage_le_overSituation07Q9 S hVW f) ≫
        (f ≫ sourceToBase S) =
      (restrictMap07Q9 S hVW f ≫ sourceToBase (restrict S V W hVW)) ≫
        (restrictSι S V W hVW).hom := by
    rw [Category.assoc, h₂, ← Category.assoc (restrictMap07Q9 S hVW f),
      restrictMap07Q9_comp_restrictXι, Category.assoc]
  refine h₁.trans (Eq.trans ?_ key)
  simp only [sourceToBase, Category.assoc]

variable (hW₂ : IsAffineOpen (f ⁻¹ᵁ W))

/-- The affine situation `(Γ(V, ⊤), Γ(f⁻¹(W), ⊤))` of `X'/S`. -/
abbrev openAffineSituation₂07Q9 : AffineCrystallineSituation.{u, u} :=
  openAffineSituation07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)

/-- **The morphism of affine situations induced by `f`**: the identity of `Γ(V, ⊤)` and the
restriction `f^♯ : Γ(W, ⊤) → Γ(f⁻¹(W), ⊤)`. -/
def openAffineSituationHom07Q9 :
    AffineCrystallineSituation.Hom (openAffineSituation07Q9 S hW hVW)
      (openAffineSituation₂07Q9 S hVW f hW₂) where
  base := DividedPowers.DPMorphism.id _
  target := (restrictMap07Q9 S hVW f).appTop.hom
  commutes := by
    change (restrictMap07Q9 S hVW f).appTop.hom.comp
        (sourceToBase (restrict S V W hVW)).appTop.hom =
      (sourceToBase (restrict (overSituation S f) V (f ⁻¹ᵁ W)
        (preimage_le_overSituation07Q9 S hVW f))).appTop.hom
    rw [sourceToBase_restrict_overSituation07Q9, Scheme.Hom.comp_appTop]
    rfl

variable {ι κ : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hrC : ∀ b, r (MvPolynomial.C b) = MvPolynomial.C b)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

/-- The divided power morphism of the uncompleted envelopes in tensor degree `n`. -/
abbrev envelopeMap07Q9 (n : ℕ) :=
  tensorPowerEnvelopeMapOver (openAffineSituationHom07Q9 S hW hVW f hW₂) g g₂ r hrC hr n

/-- **The divided power morphism `D(n) ⟶ D'(n)` of the completed envelopes**, on the transparent
realisation `Crystalline.completedTensorPowerDividedPowerRing`: the `p`-adic completion of the
morphism of uncompleted envelopes. -/
def completedEnvelopeMap07Q9 (n : ℕ) :
    completedTensorPowerDividedPowerRing (openAffineSituation07Q9 S hW hVW) g hg n ⟶
      completedTensorPowerDividedPowerRing (openAffineSituation₂07Q9 S hVW f hW₂) g₂ hg₂ n :=
  DividedPowers.DPMorphism.mk' (adicCompletionRingMap_isDPMorphism _ _ S.p
    (completedTensorPowerDifferential _ g hg n).1 (completedTensorPowerDifferential _ g₂ hg₂ n).1
    (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr n))

/-- The completed map is the completion of the uncompleted one. -/
theorem completedEnvelopeMap07Q9_toRingHom (n : ℕ) :
    (completedEnvelopeMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n).toRingHom =
      adicCompletionRingMap (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr n).toRingHom
        (map_pAdicIdeal_le S.p _) := rfl

/-- **The divided power morphism `D(n) ⟶ D'(n)`**, on the rings of the objects
`Crystalline.tensorPowerEnvelopeThickening` of `Cris^∧` from which the two systems are built. -/
def envelopeRingMap07Q9 (n : ℕ) :
    (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW) g hg n).thickening.ring ⟶
      (tensorPowerEnvelopeThickening (openAffineSituation₂07Q9 S hVW f hW₂) g₂ hg₂
        n).thickening.ring :=
  DividedPowerRing.dpMorphismCongr (tensorPowerEnvelopeThickening_ring_eq _ g hg n)
    (tensorPowerEnvelopeThickening_ring_eq _ g₂ hg₂ n)
    (completedEnvelopeMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n)

/-- `envelopeRingMap07Q9` read through the identifications with the transparent realisations. -/
theorem ringEquiv_envelopeRingMap07Q9 (n : ℕ)
    (x : (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW) g hg
      n).thickening.ring) :
    tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ n
        (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n x) =
      adicCompletionRingMap (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr n).toRingHom
        (map_pAdicIdeal_le S.p _) (tensorPowerEnvelopeThickeningRingEquiv _ g hg n x) :=
  DividedPowerRing.ringEquivOfEq_dpMorphismCongr _ _ _ x

/-- **`D(n) ⟶ D'(n)` extends the tensor power of `r`** on the image of the presentation
algebra. -/
theorem envelopeRingMap07Q9_presentationMap (n : ℕ)
    (q : MvPolynomial (Fin (n + 1) × ι) (openAffineSituation07Q9 S hW hVW).A) :
    envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n
        ((tensorPowerEnvelopeThickening _ g hg n).presentationMap q) =
      (tensorPowerEnvelopeThickening _ g₂ hg₂ n).presentationMap
        (tensorPowerRingHom (openAffineSituationHom07Q9 S hW hVW f hW₂) r n q) := by
  apply (tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ n).injective
  rw [ringEquiv_envelopeRingMap07Q9, tensorPowerEnvelopeThickeningRingEquiv_presentationMap,
    tensorPowerEnvelopeThickeningRingEquiv_presentationMap]
  simp only [tensorPowerEnvelopeMap, toPAdicCompletedDividedPowerEnvelope, RingHom.comp_apply,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact (adicCompletionRingMap_of _ _ _).trans (congrArg _ (tensorPowerEnvelopeMapOver_polynomial
    (openAffineSituationHom07Q9 S hW hVW f hW₂) g g₂ r hrC hr n q))

/-- **`D(n) ⟶ D'(n)` is over `Γ(V, ⊤)`.** -/
theorem envelopeRingMap07Q9_fromBase (n : ℕ) (a : (openAffineSituation07Q9 S hW hVW).A) :
    envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n
        ((tensorPowerEnvelopeThickening _ g hg n).thickening.fromBase a) =
      (tensorPowerEnvelopeThickening _ g₂ hg₂ n).thickening.fromBase a :=
  (congrArg (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n)
      (CompletedEnvelopeThickening.presentationMap_C _ _ _
        (tensorPowerEnvelopeThickening _ g hg n) a).symm).trans
    ((envelopeRingMap07Q9_presentationMap S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n _).trans
      ((congrArg (tensorPowerEnvelopeThickening _ g₂ hg₂ n).presentationMap
        (tensorPowerRingHom_C (openAffineSituationHom07Q9 S hW hVW f hW₂) r n a)).trans
        (CompletedEnvelopeThickening.presentationMap_C _ _ _
          (tensorPowerEnvelopeThickening _ g₂ hg₂ n) a)))

/-- **`D(n) ⟶ D'(n)` is compatible with `f^♯` on the quotients by the divided power ideals.** -/
theorem envelopeRingMap07Q9_toQuotient (n : ℕ) (c : (openAffineSituation07Q9 S hW hVW).C) :
    DividedPowerRing.quotientRingHom (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n)
        ((tensorPowerEnvelopeThickening _ g hg n).thickening.toQuotient c) =
      (tensorPowerEnvelopeThickening _ g₂ hg₂ n).thickening.toQuotient
        ((restrictMap07Q9 S hVW f).appTop.hom c) := by
  obtain ⟨q, rfl⟩ := tensorPowerPresentation_surjective _ g hg n c
  rw [CompletedEnvelopeThickening.toQuotient_apply, DividedPowerRing.quotientRingHom_mk,
    envelopeRingMap07Q9_presentationMap, ← CompletedEnvelopeThickening.toQuotient_apply]
  exact congrArg _ (RingHom.congr_fun (tensorPowerRingHom_comp_presentation
    (openAffineSituationHom07Q9 S hW hVW f hW₂) g g₂ r hrC hr n) q)

/-- **`D(n) ⟶ D'(n)` commutes with the cosimplicial structure maps of `D(•)` and `D'(•)`.** -/
theorem envelopeRingMap07Q9_comp_map {n m : SimplexCategory} (φ : n ⟶ m) :
    ((envelopeCosimplicial _ g hg).map φ).hom ≫
        envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr m.len =
      envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n.len ≫
        ((envelopeCosimplicial _ g₂ hg₂).map φ).hom := by
  apply DividedPowers.DPMorphism.ext
  funext x
  apply (tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ m.len).injective
  have h := tensorPowerEnvelopeMapOver_comp_envelopeReindex
    (openAffineSituationHom07Q9 S hW hVW f hW₂) g g₂ r hrC hr φ
  have hcomp : (adicCompletionRingMap
          (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr m.len).toRingHom
          (map_pAdicIdeal_le S.p _)).comp
        (adicCompletionRingMap (envelopeReindex _ g φ).1.toRingHom (map_pAdicIdeal_le S.p _)) =
      (adicCompletionRingMap (envelopeReindex _ g₂ φ).1.toRingHom (map_pAdicIdeal_le S.p _)).comp
        (adicCompletionRingMap (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr n.len).toRingHom
          (map_pAdicIdeal_le S.p _)) := by
    have h' : (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr m.len).toRingHom.comp
          (envelopeReindex _ g φ).1.toRingHom =
        (envelopeReindex _ g₂ φ).1.toRingHom.comp
          (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr n.len).toRingHom := by
      ext y
      exact congrArg (fun q : DividedPowers.DPMorphism _ _ ↦ q y) h
    rw [← adicCompletionRingMap_comp, ← adicCompletionRingMap_comp, h']
  have e1 := ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr m.len
    (((envelopeCosimplicial _ g hg).map φ).hom.toRingHom x)
  have e2 := tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map _ g hg φ x
  have e3 := ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n.len x
  have e4 := tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map _ g₂ hg₂ φ
    (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n.len x)
  change tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ m.len
      (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr m.len
        (((envelopeCosimplicial _ g hg).map φ).hom.toRingHom x)) =
    tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ m.len
      (((envelopeCosimplicial _ g₂ hg₂).map φ).hom.toRingHom
        (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n.len x))
  rw [e1, e2, e4, e3]
  exact RingHom.congr_fun hcomp _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
