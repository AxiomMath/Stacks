module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftBaseNaturality

/-!
# The arrow `Inf(Def_X × Def_Y) ⟶ Der_k(𝒪_Y, f_*𝒪_X)` of Stacks 0E3V is `k`-linear

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. The arrow `b` of the six-term exact
sequence of [Stacks Project, Tag 0E3V] sends a pair of infinitesimal automorphisms of the trivial
first-order deformations `X'` and `Y'` to the derivation by which conjugating the trivial lift
`f'` by the pair displaces it. At the chosen re-based first-order pushforwards it is
`Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangentCross`, a bare function
out of `Inf(Def_X) × Inf(Def_Y)`. This file proves that it is `k`-linear for the vector-space
structure `Deformation.naturalLocalizedTangentModule` of [Stacks Project, Tag 06JV] on the source
and `Deformation.Examples.schemeMorphismDerivationsModule` on the target, and packages it as a
linear map, `Deformation.Examples.schemeMorphismConjugationArrowLinear`.

## The two halves

**Additivity.** Addition on `Inf` is composition of infinitesimal automorphisms
(`Deformation.Examples.localizedTangentEquivSelfMapsCross_add`), and conjugating by a composite
pair is conjugating twice. Translating a lift by a derivation commutes with conjugating it
(`Deformation.Examples.globalLiftsOverBaseAutPairConj_vadd`): an infinitesimal automorphism acts
as the identity on the conormal sheaf of the special fibre, so this is the naturality of the
action of [Stacks Project, Tag 0CK2] in the thickening
(`Stacks.Thickenings.derivationActionGlobal_comp_of_correspond`). So the derivation attached to a
pair displaces *every* lift where the pair does
(`Deformation.Examples.globalLiftsOverBaseDerivationVAdd_conjDerivation_eq`), and additivity is
formal.

**Homogeneity.** The scalar action on `Inf` is transport along the coordinate scaling `ε ↦ cε`
([Stacks Project, Tag 06JV] (1)), which on the self-maps of the re-based pushforward is the
conjugation relation `α_{c • t} ∘ σ_c = σ_c ∘ α_t`
(`Deformation.Examples.localizedTangentEquivSelfMapsCross_smul_comp`). Pushing a lift forward
along the scaling therefore carries conjugation by `t` to conjugation by `c • t`; and it carries
translation by `θ` to translation by `c • θ`, which is the base-naturality of the action of
[Stacks Project, Tag 0CK2] at the scaling
(`Deformation.Examples.liftActionTransport_crossScaling`). No case distinction on `c` is needed:
the pushforward exists along every arrow, invertible or not.

## Main results

* `Deformation.Examples.schemeMorphismConjugationArrowLinear`: **the arrow `b` as a `k`-linear
  map**, with `Deformation.Examples.schemeMorphismConjugationArrowLinear_apply` identifying it with
  `Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangentCross`.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

/-! ### The group law and the scalar action on the self-maps of the re-based pushforward -/

section Cross

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {Z : Over (Spec (CommRingCat.of k))}
  (hp : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
  (hrs : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
  {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
  (P : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀)

/-- The self-map attached to a tangent vector is the transported automorphism. -/
theorem localizedTangentEquivSelfMapsCross_val (a : localizedAutomorphismFunctorTangent P) :
    (localizedTangentEquivSelfMapsCross hp P a).1 =
      (P.transportAut (dualNumbersUnderIsoCross x₀).hom
        (localizedTangentEquivKernel P a).1).hom.val.map := rfl

/-- **Addition on the `Inf` term is composition of self-maps of the re-based pushforward.** -/
theorem localizedTangentEquivSelfMapsCross_add :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ a b : localizedAutomorphismFunctorTangent P,
      (localizedTangentEquivSelfMapsCross hp P (a + b)).1 =
        (localizedTangentEquivSelfMapsCross hp P a).1 ≫
          (localizedTangentEquivSelfMapsCross hp P b).1 := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro a b
  rw [localizedTangentEquivSelfMapsCross_val, localizedTangentEquivSelfMapsCross_val,
    localizedTangentEquivSelfMapsCross_val, (naturalLocalizedTangentModule_spec P hrs).1 a b]
  exact congrArg (fun α : Aut (P.obj (squareZeroCrossUnder.{u, u, u}
      ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
      (FGModuleCat.of k (ULift.{u} k)))) => α.hom.val.map)
    ((P.transportAutHom (dualNumbersUnderIsoCross x₀).hom).map_mul _ _)

/-- The coordinate scaling commutes with the comparison of the two square-zero extensions. -/
theorem tangentScaling_comp_dualNumbersUnderIsoCross (c : k) :
    tangentScaling (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) (x := x₀) c ≫
        (dualNumbersUnderIsoCross x₀).hom =
      (dualNumbersUnderIsoCross x₀).hom ≫ squareZeroCrossUnderMap.{u, u, u}
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
        (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))) := by
  ext : 1
  exact squareZeroCross_naturality.{u, u, u} _
    (FGModuleCat.ofHom (c • LinearMap.id : ULift.{u} k →ₗ[k] ULift.{u} k))

/-- **The scalar action on the `Inf` term, on the self-maps of the re-based pushforward**: the
self-map attached to `c • a` is conjugate to the one attached to `a` across the coordinate
scaling `σ_c`, `α_{c • a} ∘ σ_c = σ_c ∘ α_a`. -/
theorem localizedTangentEquivSelfMapsCross_smul_comp :
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∀ (c : k) (a : localizedAutomorphismFunctorTangent P),
      (localizedTangentEquivSelfMapsCross hp P (c • a)).1 ≫ (crossScaling P c).map =
        (crossScaling P c).map ≫ (localizedTangentEquivSelfMapsCross hp P a).1 := by
  let := naturalLocalizedTangentAddCommGroup P hrs
  let := naturalLocalizedTangentModule P hrs
  intro c a
  rw [localizedTangentEquivSelfMapsCross_val, localizedTangentEquivSelfMapsCross_val]
  have hs : (localizedTangentEquivKernel P (c • a)).1 =
      P.transportAut (tangentScaling c) (localizedTangentEquivKernel P a).1 :=
    (naturalLocalizedTangentModule_spec P hrs).2 c a
  rw [hs, ← P.transportAut_comp, tangentScaling_comp_dualNumbersUnderIsoCross,
    P.transportAut_comp]
  have h := congrArg SchemeDeformationCategory.Hom.map
    (P.map_transportHom (squareZeroCrossUnderMap.{u, u, u}
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
        (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))))
      (P.transportAut (dualNumbersUnderIsoCross x₀).hom (localizedTangentEquivKernel P a).1))
  exact h

end Cross

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### An infinitesimal automorphism is the identity on the conormal sheaf -/

/-- **A self-map of the total space of a deformation over the base and fixing the special fibre
induces the identity on the conormal sheaf of the special fibre.** By
[Stacks Project, Tag 04FJ] (`Stacks.Thickenings.derivationActionGlobalEquivOfBase` in the
self-map case) it is a modified self-map `u ⬝ 𝟙`, and those act trivially on the conormal sheaf
(`Stacks.Thickenings.isConormalMapOver_derivationActionGlobal_self`). -/
theorem isConormalMapOver_selfMap {Z : Over (Spec (CommRingCat.of k))}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) Z)
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥) {σ : P.scheme ⟶ P.scheme}
    (h₁ : σ ≫ P.toBase = P.toBase) (h₂ : P.specialMap ≫ σ = P.specialMap) :
    Stacks.Thickenings.IsConormalMapOver (ker_specialMap_pow_two_eq_bot P hm)
      (ker_specialMap_pow_two_eq_bot P hm) h₂ (𝟙 _) := by
  have hsq := ker_specialMap_pow_two_eq_bot P hm
  have comm : P.specialMap ≫ (𝟙 P.scheme : P.scheme ⟶ P.scheme) =
      (𝟙 Z.left : Z.left ⟶ Z.left) ≫ P.specialMap := by
    rw [Category.comp_id, Category.id_comp]
  have ci : P.specialMap ≫ P.toBase = ((𝟙 Z.left : Z.left ⟶ Z.left) ≫ Z.hom) ≫
      residueSpecMap P.base := by
    rw [Category.id_comp]
    exact P.specialCartesian.w
  obtain ⟨θ, hθ⟩ := (Stacks.Thickenings.derivationActionGlobalEquivOfBase hsq P.specialCartesian
    ci comm (Category.id_comp _)).surjective ⟨σ, h₁, by rw [h₂, Category.id_comp]⟩
  have hσ := (Stacks.Thickenings.derivationActionGlobalEquivOfBase_apply hsq P.specialCartesian
    ci comm (Category.id_comp _) θ).symm.trans (congrArg Subtype.val hθ)
  subst hσ
  exact Stacks.Thickenings.isConormalMapOver_derivationActionGlobal_self hsq _ comm h₂

/-! ### Translating a lift commutes with conjugating it -/

section Commute

variable {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  {e : Q.base ⟶ P.base} [IsIso e] (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥)

/-- **Translating a lift by an element of the acting group of [Stacks Project, Tag 0CK2] commutes
with conjugating it by a pair of infinitesimal automorphisms of the endpoints.** -/
theorem globalLiftsOverBaseAutPairConj_vadd (g : globalLiftsOverBaseAutPair pX pY P Q e)
    (ℓ₀ : globalLiftsOverBase f P Q e)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules P.specialMap)
    (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseAutPairConj f pX pY g (globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ) =
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ (globalLiftsOverBaseAutPairConj f pX pY g ℓ) := by
  let := g.2.1
  let := g.2.2.1
  have hsq := ker_specialMap_pow_two_eq_bot P hm
  have hw : P.specialMap ≫ CategoryTheory.inv g.1.1 = P.specialMap :=
    (IsIso.comp_inv_eq _).mpr g.2.2.2.2.1.symm
  have hv : Q.specialMap ≫ CategoryTheory.inv g.1.2 = Q.specialMap :=
    (IsIso.comp_inv_eq _).mpr g.2.2.2.2.2.2.symm
  have hcomp : ∀ m : globalLiftsOverBase f P Q e,
      (globalLiftsOverBaseAutPairConj f pX pY g m).1 ≫ CategoryTheory.inv g.1.2 =
        CategoryTheory.inv g.1.1 ≫ m.1 := fun m => by
    rw [globalLiftsOverBaseAutPairConj_val]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have key : (globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ
        (globalLiftsOverBaseAutPairConj f pX pY g ℓ)).1 ≫ CategoryTheory.inv g.1.2 =
      CategoryTheory.inv g.1.1 ≫ (globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ).1 := by
    rw [globalLiftsOverBaseVAdd_val, globalLiftsOverBaseVAdd_val]
    exact Stacks.Thickenings.derivationActionGlobal_comp_of_correspond hsq hsq hw hv
      (Stacks.Thickenings.correspond_of_isConormalMapOver hsq hsq hw hv
        (isConormalMapOver_selfMap P hm
          ((IsIso.inv_comp_eq _).mpr ((comp_deformationAmbientToBase_iff P e g.1.1).mp
            g.2.2.2.1).symm) hw) fun A U h y => by
          rw [Scheme.Modules.Hom.id_app, AddCommGrpCat.id_apply])
      ℓ.2.2 (globalLiftsOverBaseAutPairConj f pX pY g ℓ).2.2 (hcomp ℓ)
  exact Subtype.ext (by rw [← cancel_mono (CategoryTheory.inv g.1.2), key, hcomp])

/-- Translation by the named action is injective in the translating element. -/
theorem globalLiftsOverBaseVAdd_left_injective (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    Function.Injective fun θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules P.specialMap =>
      globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ θ ℓ := by
  intro θ η h
  exact add_right_cancel ((globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).injective h)

variable (eC : Stacks.Thickenings.conormalModules P.specialMap ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))

/-- **The derivation attached to a pair displaces every lift where the pair does.** The arrow `b`
is defined by its effect on the base lift `ℓ₀`; since translating commutes with conjugating
(`Deformation.Examples.globalLiftsOverBaseAutPairConj_vadd`), it has the same effect on every
lift. -/
theorem globalLiftsOverBaseDerivationVAdd_conjDerivation_eq (ℓ₀ : globalLiftsOverBase f P Q e)
    (g : globalLiftsOverBaseAutPair pX pY P Q e) (ℓ : globalLiftsOverBase f P Q e) :
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
        (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ g) ℓ =
      globalLiftsOverBaseAutPairConj f pX pY g ℓ := by
  obtain ⟨κ, rfl⟩ : ∃ κ, globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ κ ℓ₀ = ℓ :=
    ⟨(globalLiftsOverBaseDerivationEquiv f pX pY hf hm ℓ₀).symm ℓ, by
      rw [globalLiftsOverBaseVAdd_base, Equiv.apply_symm_apply]⟩
  rw [globalLiftsOverBaseDerivationVAdd, ← globalLiftsOverBaseVAdd_add, add_comm,
    globalLiftsOverBaseVAdd_add, globalLiftsOverBaseAutPairConj_vadd f pX pY hf hm]
  congr 1
  exact globalLiftsOverBaseDerivationVAdd_conjDerivation f pX pY hf eC hm ℓ₀ g

/-- Translation by the third term is injective in the translating derivation. -/
theorem globalLiftsOverBaseDerivationVAdd_left_injective (ℓ₀ ℓ : globalLiftsOverBase f P Q e) :
    Function.Injective fun D : schemeMorphismDerivations f pY =>
      globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ D ℓ :=
  fun _ _ h => (schemeMorphismDerivationsEquivHom f pY P.specialMap eC).injective
    (globalLiftsOverBaseVAdd_left_injective f pX pY hf hm ℓ₀ ℓ h)

end Commute

/-! ### The linear map -/

section Linear

/-- The `k`-linear identification of the third term with the acting group is the additive one. -/
theorem schemeMorphismDerivationsLinearEquivHom_apply {X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i]
    (e : Stacks.Thickenings.conormalModules i ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (D : schemeMorphismDerivations f pY) :
    schemeMorphismDerivationsLinearEquivHom f pY i e D =
      schemeMorphismDerivationsEquivHom f pY i e D :=
  rfl

variable {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
    y₀)
  (hpX : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hpY : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  (eC : Stacks.Thickenings.conormalModules (firstOrderPushforwardCross QX).specialMap ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  (hm : IsLocalRing.maximalIdeal (firstOrderPushforwardCross QX).base ^ 2 = ⊥)
  (ℓ₀ : globalLiftsOverBase f (firstOrderPushforwardCross QX) (firstOrderPushforwardCross QY)
    (eqToHom ((firstOrderPushforwardCross_base QY).trans
      (firstOrderPushforwardCross_base QX).symm)))

/-- **The arrow `b` is additive.** -/
theorem globalLiftsOverBaseConjDerivationLocalizedTangentCross_add
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    letI := naturalLocalizedTangentAddCommGroup QX hrsX
    letI := naturalLocalizedTangentAddCommGroup QY hrsY
    ∀ t t' : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY,
      globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀
          (t + t') =
        globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀
            t +
          globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀
            t' := by
  let := naturalLocalizedTangentAddCommGroup QX hrsX
  let := naturalLocalizedTangentModule QX hrsX
  let := naturalLocalizedTangentAddCommGroup QY hrsY
  let := naturalLocalizedTangentModule QY hrsY
  intro t t'
  let G := localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY
    (eqToHom ((firstOrderPushforwardCross_base QY).trans
      (firstOrderPushforwardCross_base QX).symm))
  have hconj : globalLiftsOverBaseAutPairConj f pX pY (G (t + t')) ℓ₀ =
      globalLiftsOverBaseAutPairConj f pX pY (G t')
        (globalLiftsOverBaseAutPairConj f pX pY (G t) ℓ₀) := by
    let := (G t).2.1
    let := (G t).2.2.1
    let := (G t').2.1
    let := (G t').2.2.1
    let := (G (t + t')).2.1
    refine Subtype.ext ?_
    rw [globalLiftsOverBaseAutPairConj_val, globalLiftsOverBaseAutPairConj_val,
      globalLiftsOverBaseAutPairConj_val]
    have h₁ : (G (t + t')).1.1 = (G t).1.1 ≫ (G t').1.1 :=
      localizedTangentEquivSelfMapsCross_add hpX hrsX QX t.1 t'.1
    have h₂ : (G (t + t')).1.2 = (G t).1.2 ≫ (G t').1.2 :=
      localizedTangentEquivSelfMapsCross_add hpY hrsY QY t.2 t'.2
    have hinv : CategoryTheory.inv (G (t + t')).1.1 =
        CategoryTheory.inv (G t').1.1 ≫ CategoryTheory.inv (G t).1.1 := by
      exact IsIso.inv_eq_of_hom_inv_id (by rw [h₁]; simp)
    rw [hinv, h₂]
    simp only [Category.assoc]
  refine (add_comm _ _).symm.trans ?_ |>.symm
  refine globalLiftsOverBaseDerivationVAdd_left_injective f pX pY hf hm eC ℓ₀ ℓ₀ ?_
  show globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ _ ℓ₀ =
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀ _ ℓ₀
  rw [globalLiftsOverBaseDerivationVAdd_add]
  show globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
      (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ (G t'))
      (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
        (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ (G t)) ℓ₀) =
    globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
      (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ (G (t + t'))) ℓ₀
  rw [globalLiftsOverBaseDerivationVAdd_conjDerivation,
    globalLiftsOverBaseDerivationVAdd_conjDerivation_eq,
    globalLiftsOverBaseDerivationVAdd_conjDerivation, hconj]

/-- **Pushing a lift forward along the coordinate scaling carries conjugation by `t` to
conjugation by `c • t`.** -/
theorem globalLiftsOverBasePushforward_crossScaling_conj
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    letI := naturalLocalizedTangentAddCommGroup QX hrsX
    letI := naturalLocalizedTangentModule QX hrsX
    letI := naturalLocalizedTangentAddCommGroup QY hrsY
    letI := naturalLocalizedTangentModule QY hrsY
    ∀ (c : k) (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY)
      (ℓ : globalLiftsOverBase f (firstOrderPushforwardCross QX) (firstOrderPushforwardCross QY)
        (eqToHom ((firstOrderPushforwardCross_base QY).trans
          (firstOrderPushforwardCross_base QX).symm))),
      globalLiftsOverBasePushforward f pX pY hf (crossScaling QX c) (crossScaling QY c)
          (crossScaling_base_comp pX pY QX QY c)
          (globalLiftsOverBaseAutPairConj f pX pY
            (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY _ t) ℓ) =
        globalLiftsOverBaseAutPairConj f pX pY
          (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY _ (c • t))
          (globalLiftsOverBasePushforward f pX pY hf (crossScaling QX c) (crossScaling QY c)
            (crossScaling_base_comp pX pY QX QY c) ℓ) := by
  let := naturalLocalizedTangentAddCommGroup QX hrsX
  let := naturalLocalizedTangentModule QX hrsX
  let := naturalLocalizedTangentAddCommGroup QY hrsY
  let := naturalLocalizedTangentModule QY hrsY
  intro c t ℓ
  let G := localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY
    (eqToHom ((firstOrderPushforwardCross_base QY).trans
      (firstOrderPushforwardCross_base QX).symm))
  let := (G t).2.1
  let := (G (c • t)).2.1
  have hα : (G (c • t)).1.1 ≫ (crossScaling QX c).map = (crossScaling QX c).map ≫ (G t).1.1 :=
    localizedTangentEquivSelfMapsCross_smul_comp hpX hrsX QX c t.1
  have hβ : (G (c • t)).1.2 ≫ (crossScaling QY c).map = (crossScaling QY c).map ≫ (G t).1.2 :=
    localizedTangentEquivSelfMapsCross_smul_comp hpY hrsY QY c t.2
  have hinv : CategoryTheory.inv (G (c • t)).1.1 ≫ (crossScaling QX c).map =
      (crossScaling QX c).map ≫ CategoryTheory.inv (G t).1.1 := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hα, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  refine (eq_globalLiftsOverBasePushforward f pX pY hf _ _ _ _ _ ?_).symm
  show (CategoryTheory.inv (G (c • t)).1.1 ≫ _ ≫ (G (c • t)).1.2) ≫ (crossScaling QY c).map =
    (crossScaling QX c).map ≫ CategoryTheory.inv (G t).1.1 ≫ ℓ.1 ≫ (G t).1.2
  rw [Category.assoc, Category.assoc, hβ, ← Category.assoc _ (crossScaling QY c).map,
    globalLiftsOverBasePushforward_fac, ← Category.assoc, ← Category.assoc, hinv]
  simp only [Category.assoc]

/-- **The arrow `b` is `k`-homogeneous.** -/
theorem globalLiftsOverBaseConjDerivationLocalizedTangentCross_smul
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    letI := naturalLocalizedTangentAddCommGroup QX hrsX
    letI := naturalLocalizedTangentModule QX hrsX
    letI := naturalLocalizedTangentAddCommGroup QY hrsY
    letI := naturalLocalizedTangentModule QY hrsY
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    ∀ (c : k) (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY),
      globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀
          (c • t) =
        c • globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm
          ℓ₀ t := by
  let := naturalLocalizedTangentAddCommGroup QX hrsX
  let := naturalLocalizedTangentModule QX hrsX
  let := naturalLocalizedTangentAddCommGroup QY hrsY
  let := naturalLocalizedTangentModule QY hrsY
  let := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  let : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
  intro c t
  let G := localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY
    (eqToHom ((firstOrderPushforwardCross_base QY).trans
      (firstOrderPushforwardCross_base QX).symm))
  let π := globalLiftsOverBasePushforward f pX pY hf (crossScaling QX c) (crossScaling QY c)
    (crossScaling_base_comp pX pY QX QY c)
  let E' := schemeMorphismDerivationsEquivHom f pY (firstOrderPushforwardCross QX).specialMap eC
  have hlin : ∀ D : schemeMorphismDerivations f pY, E' (c • D) = c • E' D := fun D =>
    (schemeMorphismDerivationsLinearEquivHom f pY (firstOrderPushforwardCross QX).specialMap
      eC).map_smul c D
  refine globalLiftsOverBaseDerivationVAdd_left_injective f pX pY hf hm eC ℓ₀ (π ℓ₀) ?_
  show globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀
      (globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ (G (c • t))) (π ℓ₀) =
    globalLiftsOverBaseVAdd f pX pY hf hm ℓ₀ (E' (c • globalLiftsOverBaseConjDerivation f pX pY hf
      eC hm ℓ₀ (G t))) (π ℓ₀)
  rw [globalLiftsOverBaseDerivationVAdd_conjDerivation_eq, hlin,
    ← globalLiftsOverBasePushforward_crossScaling_conj f pX pY hf QX QY hpX hpY hrsX hrsY c t ℓ₀,
    ← globalLiftsOverBaseDerivationVAdd_conjDerivation f pX pY hf eC hm ℓ₀ (G t),
    globalLiftsOverBaseDerivationVAdd,
    globalLiftsOverBasePushforward_vadd f pX pY hf _ _ _ hm hm ℓ₀ _ ℓ₀ ℓ₀ ℓ₀,
    liftActionTransport_crossScaling f pX pY hf QX QY c hm ℓ₀]

/-- **Stacks 0E3V, the arrow `b : Inf(Def_X × Def_Y) ⟶ Der_k(𝒪_Y, f_*𝒪_X)` as a `k`-linear map.**
At the chosen re-based first-order pushforwards `X'` and `Y'` of the two endpoints and a lift
`f'` of `f` to them, the arrow sending a pair of infinitesimal automorphisms of `X'` and `Y'` to
the derivation by which conjugating `f'` by the pair displaces it is `k`-linear, for the
vector-space structure of [Stacks Project, Tag 06JV] on the source and the `k`-structure of
`Deformation.Examples.schemeMorphismDerivationsModule` on the third term. Its underlying function
is `Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangentCross`
(`Deformation.Examples.schemeMorphismConjugationArrowLinear_apply`). -/
def schemeMorphismConjugationArrowLinear
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    letI := naturalLocalizedTangentAddCommGroup QX hrsX
    letI := naturalLocalizedTangentModule QX hrsX
    letI := naturalLocalizedTangentAddCommGroup QY hrsY
    letI := naturalLocalizedTangentModule QY hrsY
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) →ₗ[k]
      schemeMorphismDerivations f pY :=
  letI := naturalLocalizedTangentAddCommGroup QX hrsX
  letI := naturalLocalizedTangentModule QX hrsX
  letI := naturalLocalizedTangentAddCommGroup QY hrsY
  letI := naturalLocalizedTangentModule QY hrsY
  letI := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  { toFun := globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC
      hm ℓ₀
    map_add' := globalLiftsOverBaseConjDerivationLocalizedTangentCross_add f pX pY hf QX QY hpX
      hpY eC hm ℓ₀ hrsX hrsY
    map_smul' := globalLiftsOverBaseConjDerivationLocalizedTangentCross_smul f pX pY hf QX QY hpX
      hpY eC hm ℓ₀ hrsX hrsY }

/-- The linear arrow `b` is the bare arrow
`Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangentCross`. -/
@[simp]
theorem schemeMorphismConjugationArrowLinear_apply
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    schemeMorphismConjugationArrowLinear f pX pY hf QX QY hpX hpY eC hm ℓ₀ hrsX hrsY t =
      globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀ t :=
  rfl

/-- The underlying function of the linear arrow `b`, as an equation of functions. -/
theorem coe_schemeMorphismConjugationArrowLinear
    (hrsX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hrsY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    ⇑(schemeMorphismConjugationArrowLinear f pX pY hf QX QY hpX hpY eC hm ℓ₀ hrsX hrsY) =
      globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀ :=
  rfl

end Linear

end Deformation.Examples

end
