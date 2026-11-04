module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.SourceBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassScale
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjF1Functor

/-!
# The morphism of Tag 01O9 under a change of the target

Let `f : X ⟶ S` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, with the
open `U(ψ)` and the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O9].  This file
records how `U(ψ)` and `r_{ℒ,ψ}` change when the target `(S, 𝒜)` is changed while `ψ` is kept:

* **along an isomorphism of graded algebras** `Φ : 𝒜₁ ≅ 𝒜₂` on `S`, reading a map
  `ψ : f^*𝒜₂ ⟶ ⨁ ℒ^{⊗ d}` as the map `ψ ∘ f^*Φ` out of `f^*𝒜₁`: the open is unchanged and the
  morphism is followed by the induced isomorphism `Proj_S(𝒜₁) ≅ Proj_S(𝒜₂)`
  (`…globalMorphism_algebraTransport`);
* **along a base change** `g : S' ⟶ S`, reading a map `ψ' : f'^*(g^*𝒜) ⟶ ⨁ ℒ^{⊗ d}` over
  `f' : X ⟶ S'` as the map out of `(g ∘ f')^*𝒜` through the identification
  `f'^*(g^*𝒜) = (g ∘ f')^*𝒜` of [Stacks, Tag 01NT]: the open is unchanged and the morphism into
  `Proj_S(𝒜)` is the morphism into `Proj_{S'}(g^*𝒜)` followed by the base-change morphism
  `Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O3] (`…globalMorphism_baseChangeUp`).

Both are proved through clause (2) of Tag 01O9: on the opens where `ψ` is surjective in a
positive degree, `r_{ℒ,ψ}` is the classifying morphism of a quadruple, and the classifying
morphisms of [Stacks, Tag 01NZ] are known to change in exactly these two ways
(`…F.classifyingMorphism_comp_relativeProjCongr`, `…classifyingMorphism_baseChangeUp`).  The
quadruples themselves are carried along by the commutation of the transport and of the base
change with the pullback, the transition to a multiple degree and the rereading of the degree
(`…Twisting.algebraTransport_scale`, `…Twisting.baseChangeUp_pullback`, …).

These are the inputs that clause (3) of [Stacks, Tag 0D2Z] needs for an arbitrary commutative
square, where the target of the morphism moves from the scheme point `f : X ⟶ Y` to another
scheme point `g : Y' ⟶ Y` of the algebraic space `Y`.

## Main results

* `…RelativeProjInvertibleMorphism.coveringOpen_algebraTransport`,
  `…RelativeProjInvertibleMorphism.lift_globalMorphism_algebraTransport`.
* `…RelativeProjInvertibleMorphism.coveringOpen_baseChangeUp`,
  `…RelativeProjInvertibleMorphism.lift_globalMorphism_baseChangeUp`.
* `…RelativeProjInvertibleMorphism.coveringOpen_congrBase`,
  `…RelativeProjInvertibleMorphism.lift_globalMorphism_congrBase`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

/-! ### Commutation of the transport and of the base change with the operations on `ψ` -/

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

section Transport

variable {T X : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  {d : ℤ} {f : T ⟶ X} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- Moving a unital homomorphism across the transport of a degree, after the pullback. -/
@[reassoc]
theorem map_eqToHom_comp_map_app (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) {n m : ℤ}
    (h : n = m) :
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece h)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (Φ.app m) =
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app n) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg B.piece h)) := by
  subst h
  simp

/-- **The transport along a unital homomorphism commutes with the transition to the degree
`a d`.** -/
theorem algebraTransport_scale (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (ψ : Twisting f B d L) (a : ℤ) :
    letI := isInvertible_piece L a
    (algebraTransport Φ ψ).scale a = algebraTransport Φ (ψ.scale a) := by
  let := isInvertible_piece L a
  refine Twisting.ext fun i => ?_
  have h : i * (a * d) = i * a * d := by ring
  change (pullbackFunctor (ringedSpaceHom f)).map
      (eqToHom (congrArg A.piece h)) ≫
      ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * a * d)) ≫ ψ.app (i * a)) ≫
        (powPowIso L a i).hom =
    (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * (a * d))) ≫
      (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg B.piece h)) ≫
        ψ.app (i * a) ≫ (powPowIso L a i).hom
  rw [Category.assoc, map_eqToHom_comp_map_app_assoc Φ h]

/-- **The transport along a unital homomorphism commutes with rereading the degree.** -/
theorem algebraTransport_congrDegree (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (ψ : Twisting f B d L) {e : ℤ} (h : d = e) :
    (algebraTransport Φ ψ).congrDegree h = algebraTransport Φ (ψ.congrDegree h) := by
  refine Twisting.ext fun i => ?_
  have h' : i * e = i * d := by rw [h]
  change (pullbackFunctor (ringedSpaceHom f)).map
      (eqToHom (congrArg A.piece h')) ≫
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ ψ.app i =
    (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * e)) ≫
      (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg B.piece h')) ≫ ψ.app i
  rw [map_eqToHom_comp_map_app_assoc Φ h']

/-- **Transporting along a unital isomorphism and then along its inverse does nothing.** -/
theorem algebraTransport_algebraTransport_unitalHomInverse
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
    (ψ : Twisting f A d L) :
    algebraTransport Φ (algebraTransport (unitalHomInverse Φ hΦ) ψ) = ψ := by
  refine Twisting.ext fun i => ?_
  have := hΦ (i * d)
  change (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫
      (pullbackFunctor (ringedSpaceHom f)).map (inv (Φ.app (i * d))) ≫ ψ.app i = ψ.app i
  rw [← CategoryTheory.Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- A degree of the transport of `ψ` along a unital isomorphism is surjective exactly when the
same degree of `ψ` is. -/
theorem epi_algebraTransport_app_iff (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hΦ : ∀ n : ℤ, IsIso (Φ.app n)) (ψ : Twisting f B d L) (i : ℤ) :
    Epi ((algebraTransport Φ ψ).app i) ↔ Epi (ψ.app i) := by
  have := hΦ (i * d)
  exact epi_comp_iff_of_epi ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d))) (ψ.app i)

end Transport

section BaseChange

variable {S S' T T₂ : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The base change of Tag 01NT commutes with the pullback along a morphism of test schemes**,
for the map `ψ` of a quadruple. -/
theorem baseChangeUp_pullback (χ : Twisting f' (baseAlgebra g A) d L) (k : T₂ ⟶ T) :
    (χ.baseChangeUp g f' A d).pullback k = (χ.pullback k).baseChangeUp g (k ≫ f') A d := by
  refine Twisting.ext fun i => ?_
  simp only [pullback_app, Twisting.pullbackApp, baseChangeUp_app]
  refine Eq.trans (congrArg (fun z => compComparison k (f' ≫ g) (A.piece (i * d)) ≫
    z ≫ laurentPullback k L i)
    (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom k))
      (compComparison f' g (A.piece (i * d))) (χ.app i))) ?_
  refine Eq.trans (congrArg (fun z => compComparison k (f' ≫ g) (A.piece (i * d)) ≫ z)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom k)).map
      (χ.app i) ≫ laurentPullback k L i))
    (compComparison_assoc k f' g (A.piece (i * d))).symm) ?_
  exact Category.assoc _ _ _

/-- **The base change of Tag 01NT commutes with the transition to the degree `a d`.** -/
theorem baseChangeUp_scale (χ : Twisting f' (baseAlgebra g A) d L) (a : ℤ) :
    letI := isInvertible_piece L a
    (χ.baseChangeUp g f' A d).scale a = (χ.scale a).baseChangeUp g f' A (a * d) := by
  let := isInvertible_piece L a
  refine Twisting.ext fun i => ?_
  have h : i * (a * d) = i * a * d := by ring
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ χ.app (i * a) ≫ (powPowIso L a i).hom)
      (Quadruple.compComparison_comp_eqToHom g f' A h).symm).trans (Category.assoc _ _ _))

/-- **The base change of Tag 01NT commutes with rereading the degree.** -/
theorem baseChangeUp_congrDegree (χ : Twisting f' (baseAlgebra g A) d L) {e : ℤ} (h : d = e) :
    (χ.baseChangeUp g f' A d).congrDegree h = (χ.congrDegree h).baseChangeUp g f' A e := by
  refine Twisting.ext fun i => ?_
  have h' : i * e = i * d := by rw [h]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ χ.app i)
      (Quadruple.compComparison_comp_eqToHom g f' A h').symm).trans (Category.assoc _ _ _))

/-- A degree of the base change of `χ` is surjective exactly when the same degree of `χ` is. -/
theorem epi_baseChangeUp_app_iff (χ : Twisting f' (baseAlgebra g A) d L) (i : ℤ) :
    Epi ((χ.baseChangeUp g f' A d).app i) ↔ Epi (χ.app i) := by
  exact epi_comp_iff_of_epi (compComparison f' g (A.piece (i * d))) (χ.app i)

end BaseChange

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Two general facts about the open and the morphism -/

section General

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- `restrictQuadruple` depends on `ψ` only through its value. -/
theorem restrictQuadruple_congr {ψ χ : Twisting f (situationAlgebra A) 1 L} (h : ψ = χ)
    (W : T.Opens) (k : ℕ) [h₁ : Epi ((ψ.pullback W.ι).app (k : ℤ))]
    [h₂ : Epi ((χ.pullback W.ι).app (k : ℤ))] :
    restrictQuadruple ψ W k = restrictQuadruple χ W k := by
  subst h
  rfl

/-- A lift through an open, followed by the inclusion into a larger open, is the lift through the
larger open. -/
theorem liftOfPreimageEqTop_homOfLE {Z W : Scheme.{u}} {U V : Z.Opens} (q : W ⟶ Z)
    (hU : q ⁻¹ᵁ U = ⊤) (hV : q ⁻¹ᵁ V = ⊤) (h : U ≤ V) :
    liftOfPreimageEqTop U q hU ≫ Z.homOfLE h = liftOfPreimageEqTop V q hV := by
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, liftOfPreimageEqTop_ι,
    liftOfPreimageEqTop_ι]

/-- Precomposing the lift through an open with a map `p` gives the lift of `p ≫ q`. -/
private theorem comp_liftOfPreimageEqTop {Z W V : Scheme.{u}} (U : Z.Opens) (q : W ⟶ Z)
    (hq : q ⁻¹ᵁ U = ⊤) (p : V ⟶ W) (h : Set.range (p ≫ q).base ⊆ Set.range U.ι.base) :
    p ≫ liftOfPreimageEqTop U q hq = IsOpenImmersion.lift U.ι (p ≫ q) h := by
  rw [← cancel_mono U.ι, Category.assoc, liftOfPreimageEqTop_ι, IsOpenImmersion.lift_fac]

/-- **Two morphisms out of `U(ψ)` agree after a lift `W ⟶ U(ψ)` as soon as they agree on the
quadruples of clause (2)**: on every open of `W` over which the pullback of `ψ` is surjective in a
positive degree, the lift factors through an open subscheme of `X` on which clause (2) of
Tag 01O9 computes the morphism of `ψ`.  This is the cover argument shared by the comparisons
below. -/
theorem lift_hom_ext (ψ : Twisting f (situationAlgebra A) 1 L) {W Y : Scheme.{u}} (q : W ⟶ T)
    (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤)
    {a b : W ⟶ Y}
    (h : ∀ (V : W.Opens) (k : ℕ) (_ : 0 < k) [Epi ((ψ.pullback (V.ι ≫ q)).app (k : ℤ))],
      V.ι ≫ a = V.ι ≫ b) : a = b := by
  let O : PositiveSection A → W.Opens :=
    fun p => q ⁻¹ᵁ (toGradedPowerMap ψ).openOfPositiveSection p
  have hO : IsOpenCover O := by
    change ⨆ p, O p = ⊤
    rw [← Scheme.Hom.preimage_iSup, ← GradedPowerMap.coveringOpen_eq_iSup]
    exact hq
  refine Scheme.Cover.hom_ext (W.openCoverOfIsOpenCover O hO) _ _ fun p => ?_
  change (O p).ι ≫ _ = (O p).ι ≫ _
  have : Epi ((ψ.pullback ((O p).ι ≫ q)).app ((p.deg + 1 : ℕ) : ℤ)) := by
    refine epi_pullback_app_of_preimage_eq_top ψ _ p ?_
    rw [Scheme.Hom.comp_preimage]
    exact top_unique fun y _ => y.2
  exact h (O p) (p.deg + 1) (Nat.succ_pos p.deg)

end General

/-! ### Change of the target along an isomorphism of graded algebras -/

/-- The inclusion of the open `⊤` is an isomorphism. -/
theorem isIso_top_ι (V : Scheme.{u}) : IsIso (⊤ : V.Opens).ι :=
  ⟨⟨V.topIso.inv, Scheme.ι_toIso_inv V, Scheme.toIso_inv_ι V⟩⟩

section Transport

variable {S T : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (ψ : Twisting f (situationAlgebra A₂) 1 L)

/-- The transport of the quadruple of clause (2) is the quadruple of clause (2) of the
transport. -/
theorem restrictQuadruple_algebraTransport (W : T.Opens) (k : ℕ)
    [Epi (((Twisting.algebraTransport Φ ψ).pullback W.ι).app (k : ℤ))]
    [Epi ((ψ.pullback W.ι).app (k : ℤ))] :
    restrictQuadruple (Twisting.algebraTransport Φ ψ) W k =
      Quadruple.algebraTransport Φ hΦ (restrictQuadruple ψ W k) := by
  let := isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
  have e1 : (Twisting.algebraTransport Φ ψ).pullback W.ι =
      Twisting.algebraTransport Φ (ψ.pullback W.ι) :=
    Twisting.algebraTransport_pullback Φ ψ W.ι
  have e2 : (Twisting.algebraTransport Φ (ψ.pullback W.ι)).scale (k : ℤ) =
      Twisting.algebraTransport Φ ((ψ.pullback W.ι).scale (k : ℤ)) :=
    Twisting.algebraTransport_scale Φ _ _
  have e3 : (Twisting.algebraTransport Φ ((ψ.pullback W.ι).scale (k : ℤ))).congrDegree
        (mul_one (k : ℤ)) =
      Twisting.algebraTransport Φ (((ψ.pullback W.ι).scale (k : ℤ)).congrDegree
        (mul_one (k : ℤ))) :=
    Twisting.algebraTransport_congrDegree Φ _ _
  have e : (((Twisting.algebraTransport Φ ψ).pullback W.ι).scale (k : ℤ)).congrDegree
        (mul_one (k : ℤ)) =
      Twisting.algebraTransport Φ
        (((ψ.pullback W.ι).scale (k : ℤ)).congrDegree (mul_one (k : ℤ))) := by
    rw [e1, e2, e3]
  exact Quadruple.ext rfl fun i => heq_of_eq (congrArg (fun χ => χ.app i) e)

include hΦ in
/-- The pullback of the transport is surjective in a degree exactly when the pullback of `ψ` is. -/
theorem epi_algebraTransport_pullback_iff {W : Scheme.{u}} (q : W ⟶ T) (i : ℤ) :
    Epi (((Twisting.algebraTransport Φ ψ).pullback q).app i) ↔ Epi ((ψ.pullback q).app i) := by
  have e : (Twisting.algebraTransport Φ ψ).pullback q =
      Twisting.algebraTransport Φ (ψ.pullback q) :=
    Twisting.algebraTransport_pullback Φ ψ q
  rw [e]
  exact Twisting.epi_algebraTransport_app_iff Φ hΦ _ i

include hΦ in
/-- **The open `U(ψ)` does not change under an isomorphism of the graded algebra.** -/
theorem coveringOpen_algebraTransport :
    (toGradedPowerMap (Twisting.algebraTransport Φ ψ)).coveringOpen =
      (toGradedPowerMap ψ).coveringOpen := by
  ext x
  simp only [SetLike.mem_coe, mem_coveringOpen_iff_exists_epi,
    epi_algebraTransport_pullback_iff Φ hΦ]

/-- **The morphism of Tag 01O9 under an isomorphism `Φ : 𝒜₁ ≅ 𝒜₂` of graded algebras.**  Reading
`ψ : f^*𝒜₂ ⟶ ⨁ ℒ^{⊗ d}` as the map `ψ ∘ f^*Φ` out of `f^*𝒜₁`, the morphism into `Proj_S(𝒜₁)`
followed by `Proj_S(𝒜₁) ≅ Proj_S(𝒜₂)` is the morphism of `ψ`; stated after a lift `W ⟶ U(ψ)` of
an arbitrary morphism of schemes `q : W ⟶ X`. -/
theorem lift_globalMorphism_algebraTransport {W : Scheme.{u}} (q : W ⟶ T)
    (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q (by rw [coveringOpen_algebraTransport Φ hΦ]; exact hq) ≫
        (toGradedPowerMap (Twisting.algebraTransport Φ ψ)).globalMorphism (relativeProj A₁) ≫
          (relativeProjCongr Φ hΦ).hom =
      liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A₂) := by
  refine lift_hom_ext ψ q hq fun V k hk _ => ?_
  have : Epi (((Twisting.algebraTransport Φ ψ).pullback (V.ι ≫ q)).app (k : ℤ)) :=
    (epi_algebraTransport_pullback_iff Φ hΦ ψ _ _).2 inferInstance
  obtain ⟨h1, e1⟩ := clauseTwo_of_epi_pullback (Twisting.algebraTransport Φ ψ) (V.ι ≫ q) hk
  obtain ⟨h2, e2⟩ := clauseTwo_of_epi_pullback ψ (V.ι ≫ q) hk
  have l1 := comp_liftOfPreimageEqTop _ q
    (by rw [coveringOpen_algebraTransport Φ hΦ]; exact hq) V.ι h1
  have l2 := comp_liftOfPreimageEqTop _ q hq V.ι h2
  have := isIso_top_ι V.toScheme
  rw [reassoc_of% l1, reassoc_of% l2, ← cancel_epi (⊤ : V.toScheme.Opens).ι, reassoc_of% e1, e2,
    F.classifyingMorphism_comp_relativeProjCongr, F.algebraTransport_mk]
  have : Epi ((((Twisting.algebraTransport Φ ψ).pullback (V.ι ≫ q)).pullback
      (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) := Twisting.epi_pullbackApp _ _ _ inferInstance
  have : Epi (((ψ.pullback (V.ι ≫ q)).pullback (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ inferInstance
  have e : (Twisting.algebraTransport Φ ψ).pullback (V.ι ≫ q) =
      Twisting.algebraTransport Φ (ψ.pullback (V.ι ≫ q)) :=
    Twisting.algebraTransport_pullback Φ ψ (V.ι ≫ q)
  have : Epi (((Twisting.algebraTransport Φ (ψ.pullback (V.ι ≫ q))).pullback
      (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) :=
    (epi_algebraTransport_pullback_iff Φ hΦ (ψ.pullback (V.ι ≫ q)) _ _).2 inferInstance
  refine congrArg (F.classifyingMorphism A₂) (congrArg (F.mk _ _) ?_)
  exact (congrArg (Quadruple.algebraTransport (unitalHomInverse Φ hΦ)
      (isIso_unitalHomInverse_app Φ hΦ)) ((restrictQuadruple_congr e ⊤ k).trans
        (restrictQuadruple_algebraTransport Φ hΦ _ ⊤ k))).trans
    (Quadruple.algebraTransport_inverse_algebraTransport Φ hΦ _)

end Transport

/-! ### Change of the target along a base change -/

section BaseChange

variable {S S' T : Scheme.{u}} {B : SheafGradedAlgebra.{u} S} (φ : S' ⟶ S) {f₀ : T ⟶ S'}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (χ : Twisting f₀ (situationAlgebra (B.pullback φ)) 1 L)

/-- The base change of the quadruple of clause (2) is the quadruple of clause (2) of the base
change. -/
theorem restrictQuadruple_baseChangeUp (W : T.Opens) (k : ℕ)
    [h₁ : Epi (((χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback W.ι).app (k : ℤ))]
    [h₂ : Epi ((χ.pullback W.ι).app (k : ℤ))] :
    restrictQuadruple (χ.baseChangeUp φ f₀ (situationAlgebra B) 1) W k =
      (restrictQuadruple χ W k).baseChangeUp φ (W.ι ≫ f₀) (situationAlgebra B) (k : ℤ) := by
  let := isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
  have e1 : (χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback W.ι =
      (χ.pullback W.ι).baseChangeUp φ (W.ι ≫ f₀) (situationAlgebra B) 1 :=
    Twisting.baseChangeUp_pullback φ f₀ (situationAlgebra B) 1 χ W.ι
  have e2 : ((χ.pullback W.ι).baseChangeUp φ (W.ι ≫ f₀) (situationAlgebra B) 1).scale (k : ℤ) =
      ((χ.pullback W.ι).scale (k : ℤ)).baseChangeUp φ (W.ι ≫ f₀) (situationAlgebra B)
        ((k : ℤ) * 1) :=
    Twisting.baseChangeUp_scale φ (W.ι ≫ f₀) (situationAlgebra B) 1 _ _
  have e3 : (((χ.pullback W.ι).scale (k : ℤ)).baseChangeUp φ (W.ι ≫ f₀) (situationAlgebra B)
        ((k : ℤ) * 1)).congrDegree (mul_one (k : ℤ)) =
      (((χ.pullback W.ι).scale (k : ℤ)).congrDegree (mul_one (k : ℤ))).baseChangeUp φ
        (W.ι ≫ f₀) (situationAlgebra B) (k : ℤ) :=
    Twisting.baseChangeUp_congrDegree φ (W.ι ≫ f₀) (situationAlgebra B) _ _ _
  have e : (((χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback W.ι).scale
        (k : ℤ)).congrDegree (mul_one (k : ℤ)) =
      (((χ.pullback W.ι).scale (k : ℤ)).congrDegree (mul_one (k : ℤ))).baseChangeUp φ
        (W.ι ≫ f₀) (situationAlgebra B) (k : ℤ) :=
    (congrArg (fun χ => (χ.scale (k : ℤ)).congrDegree (mul_one (k : ℤ))) e1).trans
      ((congrArg (fun χ => χ.congrDegree (mul_one (k : ℤ))) e2).trans e3)
  exact Quadruple.ext rfl fun i => heq_of_eq (congrArg (fun χ => χ.app i) e)

/-- The pullback of the base change is surjective in a degree exactly when the pullback of `χ`
is. -/
theorem epi_baseChangeUp_pullback_iff {W : Scheme.{u}} (q : W ⟶ T) (i : ℤ) :
    Epi (((χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback q).app i) ↔
      Epi ((χ.pullback q).app i) := by
  have e : (χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback q =
      (χ.pullback q).baseChangeUp φ (q ≫ f₀) (situationAlgebra B) 1 :=
    Twisting.baseChangeUp_pullback φ f₀ (situationAlgebra B) 1 χ q
  rw [e]
  exact Twisting.epi_baseChangeUp_app_iff φ (q ≫ f₀) (situationAlgebra B) 1 _ i

/-- **The open `U(ψ)` does not change under base change of the target.** -/
theorem coveringOpen_baseChangeUp :
    (toGradedPowerMap (χ.baseChangeUp φ f₀ (situationAlgebra B) 1)).coveringOpen =
      (toGradedPowerMap χ).coveringOpen := by
  ext x
  simp only [SetLike.mem_coe, mem_coveringOpen_iff_exists_epi, epi_baseChangeUp_pullback_iff]

/-- **The morphism of Tag 01O9 under base change of the target.**  For `φ : S' ⟶ S` and a map
`χ : f₀^*(φ^*𝒜) ⟶ ⨁ ℒ^{⊗ d}` over `f₀ : X ⟶ S'`, read as a map out of `(φ ∘ f₀)^*𝒜` through the
identification of [Stacks, Tag 01NT], the morphism into `Proj_S(𝒜)` is the morphism into
`Proj_{S'}(φ^*𝒜)` followed by the base-change morphism of [Stacks, Tag 01O3]; stated after a lift
`W ⟶ U(χ)` of an arbitrary morphism of schemes `q : W ⟶ X`. -/
theorem lift_globalMorphism_baseChangeUp {W : Scheme.{u}} (q : W ⟶ T)
    (hq : q ⁻¹ᵁ (toGradedPowerMap χ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap χ).globalMorphism (relativeProj (B.pullback φ))
        ≫ RelativeProjBaseChangeTwist.baseChangeHom B φ =
      liftOfPreimageEqTop _ q (by rw [coveringOpen_baseChangeUp]; exact hq) ≫
        (toGradedPowerMap (χ.baseChangeUp φ f₀ (situationAlgebra B) 1)).globalMorphism
          (relativeProj B) := by
  refine lift_hom_ext χ q hq fun V k hk _ => ?_
  have : Epi (((χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback (V.ι ≫ q)).app
      (k : ℤ)) := (epi_baseChangeUp_pullback_iff φ χ _ _).2 inferInstance
  obtain ⟨h1, e1⟩ := clauseTwo_of_epi_pullback (χ.baseChangeUp φ f₀ (situationAlgebra B) 1)
    (V.ι ≫ q) hk
  obtain ⟨h2, e2⟩ := clauseTwo_of_epi_pullback χ (V.ι ≫ q) hk
  have l1 := comp_liftOfPreimageEqTop _ q
    (by rw [coveringOpen_baseChangeUp]; exact hq) V.ι h1
  have l2 := comp_liftOfPreimageEqTop _ q hq V.ι h2
  have := isIso_top_ι V.toScheme
  rw [reassoc_of% l1, reassoc_of% l2, ← cancel_epi (⊤ : V.toScheme.Opens).ι, reassoc_of% e2, e1,
    ← classifyingMorphism_baseChangeUp]
  have : Epi ((((χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback (V.ι ≫ q)).pullback
      (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) := Twisting.epi_pullbackApp _ _ _ inferInstance
  have : Epi (((χ.pullback (V.ι ≫ q)).pullback (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ inferInstance
  have e : (χ.baseChangeUp φ f₀ (situationAlgebra B) 1).pullback (V.ι ≫ q) =
      (χ.pullback (V.ι ≫ q)).baseChangeUp φ ((V.ι ≫ q) ≫ f₀) (situationAlgebra B) 1 :=
    Twisting.baseChangeUp_pullback φ f₀ (situationAlgebra B) 1 χ (V.ι ≫ q)
  have : Epi ((((χ.pullback (V.ι ≫ q)).baseChangeUp φ ((V.ι ≫ q) ≫ f₀)
      (situationAlgebra B) 1).pullback (⊤ : V.toScheme.Opens).ι).app (k : ℤ)) :=
    (epi_baseChangeUp_pullback_iff φ (χ.pullback (V.ι ≫ q)) _ _).2 inferInstance
  refine congrArg (F.classifyingMorphism B)
    ((F.baseChangeUp_mk φ (situationAlgebra B) _ _ _).trans ?_)
  exact congrArg (F.mk _ _) ((restrictQuadruple_baseChangeUp φ (χ.pullback (V.ι ≫ q)) ⊤ k
    (h₁ := by assumption) (h₂ := by assumption)).symm.trans
    (restrictQuadruple_congr e ⊤ k (h₁ := by assumption) (h₂ := by assumption)).symm)

end BaseChange

/-! ### Rereading the morphism to the base along an equality -/

section CongrBase

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f₁ f₂ : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- Reading `ψ` over an equal morphism to the base does not change the open. -/
theorem coveringOpen_congrBase (h : f₁ = f₂) (ψ : Twisting f₁ (situationAlgebra A) 1 L) :
    (toGradedPowerMap (Twisting.congrBase h ψ)).coveringOpen =
      (toGradedPowerMap ψ).coveringOpen := by
  subst h
  rfl

/-- Reading `ψ` over an equal morphism to the base does not change the morphism. -/
theorem lift_globalMorphism_congrBase (h : f₁ = f₂) (ψ : Twisting f₁ (situationAlgebra A) 1 L)
    {W : Scheme.{u}} (q : W ⟶ T) (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q (by rw [coveringOpen_congrBase]; exact hq) ≫
        (toGradedPowerMap (Twisting.congrBase h ψ)).globalMorphism (relativeProj A) =
      liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  subst h
  rfl

/-- `toGradedPowerMap` depends on `ψ` only through its value. -/
theorem lift_globalMorphism_congr {ψ χ : Twisting f₁ (situationAlgebra A) 1 L} (h : ψ = χ)
    {W : Scheme.{u}} (q : W ⟶ T) (hq : q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q (by rw [← h]; exact hq) ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A) =
      liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  subst h
  rfl

end CongrBase

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
