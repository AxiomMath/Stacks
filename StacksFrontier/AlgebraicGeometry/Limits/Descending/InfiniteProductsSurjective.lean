module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity of an infinite product of schemes over a base

The structure morphism of the product over a scheme `S` of an arbitrary family of surjective
affine morphisms is again surjective. The product is the categorical product of the objects
`Over.mk (f i)` in `Over S`; its existence comes from the affineness hypotheses via
`AlgebraicGeometry.hasProduct_of_isAffineHom`.

## Main results

* `AlgebraicGeometry.surjective_product_hom`: the structure morphism of the product in `Over S`
  of a family of surjective affine morphisms is surjective.

## Implementation notes

Surjectivity is checked one point `s` of `S` at a time, by base changing the whole family to
the spectrum of the residue field at `s`. The base changed product is the limit of its finite
subproducts; those are affine, quasi-compact and nonempty, so the limit is nonempty by
`AlgebraicGeometry.Scheme.nonempty_of_isLimit`, and any of its points maps to `s`.

## References

* [Stacks Project, Tag 0CNJ](https://stacks.math.columbia.edu/tag/0CNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

universe u v

namespace AlgebraicGeometry

/-- The structure morphism of an object of `Over K` isomorphic to one with surjective structure
morphism is surjective. -/
private theorem surjective_hom_of_iso {K : Scheme.{u}} {X Y : Over K} (e : X ≅ Y)
    [Surjective Y.hom] : Surjective X.hom := by
  have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- The structure morphism of the product in `Over K` of a finite family of surjective
morphisms is surjective. -/
private theorem finite_over_product_surjective {K : Scheme.{u}} {α : Type v} [Finite α]
    (Y : α → Over K) [HasFiniteProducts (Over K)]
    (hY : ∀ a, Surjective (Y a).hom) : Surjective (∏ᶜ Y).hom := by
  classical
  have := Fintype.ofFinite α
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (Y : α → Over K), (∀ a, Surjective (Y a).hom) →
      Surjective (∏ᶜ Y).hom) ?_ ?_ ?_ α Y hY
  · intro α β _ e ih Z hZ
    have : HasProduct (fun a : α => Z (e a)) :=
      hasProduct_of_equiv_of_iso Z (fun a => Z (e a)) e (fun _ => Iso.refl _)
    let e' : (∏ᶜ fun a : α => Z (e a)) ≅ ∏ᶜ Z := Pi.whiskerEquiv e fun _ => Iso.refl _
    have := ih (fun a => Z (e a)) (fun a => hZ (e a))
    exact surjective_hom_of_iso e'.symm
  · intro Y hY
    have hP : IsTerminal (∏ᶜ Y) := IsTerminal.ofUniqueHom
      (fun X => Pi.lift fun a => isEmptyElim a)
      (by intro X f; apply Pi.hom_ext; intro a; exact isEmptyElim a)
    let e : (∏ᶜ Y) ≅ ⊤_ (Over K) := hP.uniqueUpToIso terminalIsTerminal
    let eT : (⊤_ (Over K)) ≅ Over.mk (𝟙 K) := terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal
    have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
    have : IsIso eT.hom.left := (Over.forget K).map_isIso eT.hom
    have het : eT.hom.left = (⊤_ (Over K)).hom := by simpa using eT.hom.w
    have : IsIso (⊤_ (Over K)).hom := het ▸ inferInstance
    exact surjective_hom_of_iso e
  · intro α _ ih Y hY
    have : HasProduct (fun a : α => Y (some a)) := inferInstance
    let R : Over K := ∏ᶜ (fun a : α => Y (some a))
    let e := overOptionProductIso (K := K) (α := α) Y
    have hR : Surjective R.hom := ih (fun a => Y (some a)) (fun a => hY (some a))
    have : Surjective (Y none).hom := hY none
    have hproj : Surjective (prod.fst (X := Y none) (Y := R)).left := by
      rw [← Over.prodLeftIsoPullback_hom_fst]
      infer_instance
    have hB : Surjective (Y none ⨯ R).hom := by
      rw [← (prod.fst (X := Y none) (Y := R)).w]
      infer_instance
    exact surjective_hom_of_iso e

/-- **Stacks Project, Tag 0CNJ.** The structure morphism of the product over `S` of surjective
affine morphisms is surjective. -/
@[stacks 0CNJ]
theorem surjective_product_hom {I : Type u} (S : Scheme.{u})
    (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)]
    [∀ i, Surjective (f i)] :
    letI := hasProduct_of_isAffineHom S T f
    Surjective (∏ᶜ (fun i ↦ Over.mk (f i))).hom := by
  classical
  have := hasProduct_of_isAffineHom S T f
  rw [surjective_iff]
  intro s
  let K := Spec (S.residueField s)
  let q : K ⟶ S := S.fromSpecResidueField s
  let X : I → Scheme := fun i => pullback (f i) q
  let g : ∀ i, X i ⟶ K := fun i => pullback.snd (f i) q
  let h : ∀ i, X i ⟶ T i := fun i => pullback.fst (f i) q
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) q :=
    ⟨fun pb hf => isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
  have hsurj (i : I) : Surjective (g i) := by
    dsimp only [g, X]
    infer_instance
  have haff (i : I) : IsAffineHom (g i) := by
    dsimp only [g, X]
    exact MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom (f i))
  have : ∀ i, IsAffineHom (g i) := haff
  have : ∀ i, Surjective (g i) := hsurj
  have := hasProduct_of_isAffineHom K X g
  let D := liftToFinsetObj (Discrete.functor (fun i => Over.mk (g i)))
  let D' := D ⋙ Over.forget K
  let c' : Cone D' := (Over.forget K).mapCone
    (finiteSubproductsCone (fun i => Over.mk (g i)))
  have hc' : IsLimit c' :=
    isLimitOfPreserves (Over.forget K) (finiteSubproductsConeIsLimit (fun i => Over.mk (g i)))
  have stage_surjective (J : (Finset (Discrete I))ᵒᵖ) : Surjective (D.obj J).hom := by
    simpa [D, liftToFinsetObj] using
      finite_over_product_surjective (fun x : J.unop => Over.mk (g x.1.as))
        (fun x => hsurj x.1.as)
  have stage_affine (J : (Finset (Discrete I))ᵒᵖ) : IsAffine (D'.obj J) := by
    have : IsAffineHom (D.obj J).hom := by
      simpa [D, liftToFinsetObj] using
        isAffineHom_over_finiteProduct (fun x : J.unop => Over.mk (g x.1.as))
          (fun x => haff x.1.as)
    exact isAffine_of_isAffineHom (D.obj J).hom
  have hne (J : (Finset (Discrete I))ᵒᵖ) : Nonempty (D'.obj J) := by
    have : Surjective (D.obj J).hom := stage_surjective J
    obtain ⟨x, _⟩ := ((D.obj J).hom).surjective
      (IsLocalRing.closedPoint (S.residueField s))
    exact ⟨x⟩
  have hcpt (J : (Finset (Discrete I))ᵒᵖ) : CompactSpace (D'.obj J) := by
    have : IsAffine (D'.obj J) := stage_affine J
    infer_instance
  have hmap {J J' : (Finset (Discrete I))ᵒᵖ} (a : J ⟶ J') : IsAffineHom (D'.map a) := by
    have : IsAffine (D'.obj J) := stage_affine J
    have : IsAffine (D'.obj J') := stage_affine J'
    infer_instance
  have : ∀ J, Nonempty (D'.obj J) := hne
  have : ∀ J, CompactSpace (D'.obj J) := hcpt
  have : ∀ {J J'} (a : J ⟶ J'), IsAffineHom (D'.map a) := hmap
  obtain ⟨p⟩ := Scheme.nonempty_of_isLimit D' c' hc'
  let Q := ∏ᶜ (fun i ↦ Over.mk (f i))
  let P := ∏ᶜ (fun i ↦ Over.mk (g i))
  let r : Over.mk (P.hom ≫ q) ⟶ Q := Pi.lift fun i =>
    Over.homMk ((Pi.π (fun i : I => Over.mk (g i)) i).left ≫ h i) (by
      calc
        ((Pi.π (fun i : I => Over.mk (g i)) i).left ≫ h i) ≫ f i =
            (Pi.π (fun i : I => Over.mk (g i)) i).left ≫ (h i ≫ f i) := by
              rw [Category.assoc]
        _ = (Pi.π (fun i : I => Over.mk (g i)) i).left ≫ (g i ≫ q) := by
              rw [pullback.condition]
        _ = ((Pi.π (fun i : I => Over.mk (g i)) i).left ≫ g i) ≫ q := by
              rw [← Category.assoc]
        _ = P.hom ≫ q := by
              simpa [g, P] using congrArg (fun k : P.left ⟶ K => k ≫ q)
                (Pi.π (fun i : I => Over.mk (g i)) i).w)
  let pP : P.left := by simpa [c', P] using p
  refine ⟨r.left pP, ?_⟩
  calc
    Q.hom (r.left pP) = (r.left ≫ Q.hom) pP := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (P.hom ≫ q) pP := by
      simp
    _ = q (P.hom pP) := Scheme.Hom.comp_apply _ _ _
    _ = s := by
      simpa [Subsingleton.elim (P.hom pP) (IsLocalRing.closedPoint (S.residueField s)), q, K] using
        (S.fromSpecResidueField_apply s (IsLocalRing.closedPoint (S.residueField s)))

end AlgebraicGeometry

end
