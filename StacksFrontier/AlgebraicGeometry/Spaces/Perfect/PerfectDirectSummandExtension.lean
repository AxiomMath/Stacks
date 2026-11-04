module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectExtensionStep
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtension

/-!
# A perfect object on a quasi-compact open is a summand of a restricted perfect object

Let `X` be a quasi-compact quasi-separated algebraic space, `W ⊆ X` a quasi-compact open
subspace and `P` a perfect object of `D(𝒪_W)`. Then `P` is a direct summand of `Q|_W` for a
perfect object `Q` of `D(𝒪_X)` (Stacks 09IX).

The proof is the induction of Stacks 09IT on the quasi-compact opens containing `W`. For an
elementary distinguished square `(W₁ ⊆ W₂, f : V ⟶ W₂)` with `V` affine, a perfect `Q₁` on `W₁`
restricts to `W₁ ×_{W₂} V`, which is a quasi-compact open of `V`; the affine lift
(`AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_shift_of_isAffineSpace`) gives a
perfect `B` on `V` restricting to `Q₁ ⊕ Q₁[1]` there, and `Q₁ ⊕ Q₁[1]` and `B` glue to a perfect
`Q₂` on `W₂` (`AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_shift_of_eds`). `P`
is a summand of `Q₁|_W`, hence of `(Q₁ ⊕ Q₁[1])|_W = Q₂|_W`.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_retract_restrict`: Stacks 09IX.

## References

* [Stacks Project, Tag 09IX](https://stacks.math.columbia.edu/tag/09IX)
* [Stacks Project, Tag 09IT](https://stacks.math.columbia.edu/tag/09IT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

attribute [local instance 10000] HasDerivedCategory.standard

variable {B S hS}

/-- The induction statement for Stacks 09IX: there is a perfect object on `D` of whose
restriction to `W` the object `P` is a direct summand. -/
def IsSummandOfPerfectRestriction {X : AlgebraicSpaces B S hS} {W : Subfunctor X.1}
    (hW : IsOpenSubspace B S hS W)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)) (D : Subfunctor X.1) : Prop :=
  ∀ hD : IsOpenSubspace B S hS D,
    ∃ Q : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS D hD).1
        (openSubspaceSpace B S hS D hD).2),
      (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS D hD).1
        (openSubspaceSpace B S hS D hD).2).IsPerfect Q ∧
      ∀ (a : openSubspaceSpace B S hS W hW ⟶ openSubspaceSpace B S hS D hD)
        (ha : IsEtale B S hS a.hom),
        a.hom ≫ D.ι = W.ι →
        ∃ (s : P ⟶ (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj Q)
          (r : (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj Q ⟶ P),
          s ≫ r = 𝟙 P

/-- A retraction of `P` onto an object transfers along an isomorphism. -/
private theorem exists_retract_of_iso {C : Type*} [Category C] {P A B : C} (e : A ≅ B)
    (s : P ⟶ B) (r : B ⟶ P) (h : s ≫ r = 𝟙 P) : ∃ (s' : P ⟶ A) (r' : A ⟶ P), s' ≫ r' = 𝟙 P :=
  ⟨s ≫ e.inv, e.hom ≫ r, by simp [h]⟩

/-- The base case: `P` is a summand of the restriction of a perfect object on `W` itself. -/
theorem isSummandOfPerfectRestriction_self {X : AlgebraicSpaces B S hS} {W : Subfunctor X.1}
    (hW : IsOpenSubspace B S hS W)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P) :
    IsSummandOfPerfectRestriction hW P W := by
  intro hW'
  let Y := openSubspaceSpace B S hS W hW
  have hid : IsEtale B S hS (𝟙 Y : Y ⟶ Y).hom := isEtale_of_isIso B S hS (𝟙 Y.1)
  refine ⟨(etaleModulePullback.{u, u} B S hS (𝟙 Y) hid).mapDerivedCategory.obj P,
    isPerfect_etaleModulePullback_standard B S hS (𝟙 Y) hid P hP, fun a ha hai => ?_⟩
  obtain rfl : a = 𝟙 Y := by
    apply ObjectProperty.hom_ext
    exact (cancel_mono W.ι).1 (hai.trans (Category.id_comp _).symm)
  have : (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS (Iso.refl Y)).functor.Additive :=
    etaleModulePullback_additive B S hS (𝟙 Y) hid
  have : PreservesFiniteLimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS (Iso.refl Y)).functor :=
    preservesFiniteLimits_etaleModulePullback B S hS (𝟙 Y) hid
  have : PreservesFiniteColimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS (Iso.refl Y)).functor :=
    preservesFiniteColimits_etaleModulePullback B S hS (𝟙 Y) hid
  let Φ := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS (Iso.refl Y))
  exact ⟨Φ.unitIso.hom.app P, Φ.unitIso.inv.app P, Φ.unitIso.hom_inv_id_app P⟩

/-- **The inductive step of Stacks 09IX.** Let `(W₁ ⊆ W₂, f : V ⟶ W₂)` be an elementary
distinguished square of quasi-compact opens of `X` containing `W`, with `V` affine. If `P` is a
summand of the restriction of a perfect object on `W₁`, it is one of a perfect object on `W₂`. -/
theorem isSummandOfPerfectRestriction_step (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {W : Subfunctor X.1} (hW : IsOpenSubspace B S hS W)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)) {W₁ W₂ : Subfunctor X.1}
    (hW₁ : IsOpenSubspace B S hS W₁) (hW₂ : IsOpenSubspace B S hS W₂)
    (hW₁qc : IsQuasiCompactSpace B S hS W₁.toFunctor) (hle : W₁ ≤ W₂) (hWW₁ : W ≤ W₁)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor) (hV : IsAffineSpace B S hS V)
    (hsq : IsElementaryDistinguishedSquare B S hS hW₂.1
      (Subfunctor.range (Subfunctor.homOfLe hle)) f)
    (IH : IsSummandOfPerfectRestriction hW P W₁) :
    IsSummandOfPerfectRestriction hW P W₂ := by
  intro hW₂'
  let Y₁ := openSubspaceSpace B S hS W₁ hW₁
  let Y₂ : AlgebraicSpaces B S hS := ⟨W₂.toFunctor, hW₂.1⟩
  let Uo := Subfunctor.range (Subfunctor.homOfLe hle)
  have hsq' : IsElementaryDistinguishedSquare B S hS Y₂.2 Uo f := hsq
  obtain ⟨Q₁, hQ₁, hret⟩ := IH hW₁
  let φU : W₁.toFunctor ≅ Uo.toFunctor := asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))
  let eU : Y₁ ≅ edsOpen B S hS (W := Y₂) hsq' := ObjectProperty.isoMk _ φU
  have hU := isEtale_hom_of_iso B S hS eU.symm
  let Q₁' := (etaleModulePullback.{u, u} B S hS eU.inv hU).mapDerivedCategory.obj Q₁
  have hQ₁' := isPerfect_etaleModulePullback_standard B S hS eU.inv hU Q₁ hQ₁
  let M := (edsRestrictFst B S hS (W := Y₂) hsq').mapDerivedCategory.obj Q₁'
  have hM := isPerfect_etaleModulePullback_standard B S hS (edsFst B S hS (W := Y₂) hsq')
    (isEtale_edsFst B S hS (W := Y₂) hsq')
    Q₁' hQ₁'
  have hW₂qs := isAbsolutelyQuasiSeparated_of_isOpenSubspace B S hS hZ hXqs W₂ hW₂'
  have hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS (W := Y₂) hsq').1 :=
    isQuasiCompactSpace_pullback B S hS hZ Uo.ι f hsq'.isOpenSubspace.1 Y₂.2
      (IsQuasiCompactSpace.of_iso B S hS hW₁qc φU)
      hV.isQuasiCompactSpace hW₂qs
  obtain ⟨Bo, hBo, ⟨e⟩⟩ := exists_isPerfect_restrict_iso_biprod_shift_of_isAffineSpace
    (V := edsEtale B S hS hsq') hV (edsSnd B S hS (W := Y₂) hsq')
    (by
      have := MorphismProperty.relative_isStableUnderBaseChange
        (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
          (BigFppfOver.toScheme B S hS)) (F := yoneda)
      exact MorphismProperty.pullback_snd (P := MorphismProperty.presheaf _) _ _
        hsq'.isOpenSubspace.2) hPqc
    M hM
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    exists_isPerfect_restrict_iso_biprod_shift_of_eds B S hS (W := Y₂) hsq' Q₁' hQ₁' Bo hBo e
  refine ⟨F, hF, fun a ha hai => ?_⟩
  let a₁ : openSubspaceSpace B S hS W hW ⟶ Y₁ := ObjectProperty.homMk (Subfunctor.homOfLe hWW₁)
  have ha₁ : IsEtale B S hS a₁.hom :=
    isEtale_of_comp_mono B S hS (Subfunctor.homOfLe hWW₁) W₁.ι (by
      rw [Subfunctor.homOfLe_ι]
      exact isEtale_of_isOpenImmersion B S hS hW.2)
  obtain ⟨s₁, r₁, h₁⟩ := hret a₁ ha₁ (Subfunctor.homOfLe_ι hWW₁)
  let b := a₁ ≫ eU.hom
  have hb : IsEtale B S hS b.hom := isEtale_comp B S hS ha₁ (isEtale_hom_of_iso B S hS eU)
  have hab : b ≫ edsOpenHom B S hS hsq' = a := by
    apply ObjectProperty.hom_ext
    refine (cancel_mono W₂.ι).1 ?_
    refine Eq.trans ?_ hai.symm
    show Subfunctor.homOfLe hWW₁ ≫ Subfunctor.toRange (Subfunctor.homOfLe hle) ≫ Uo.ι ≫ W₂.ι =
      W.ι
    rw [Subfunctor.toRange_ι_assoc, Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι]
  let G := (etaleModulePullback.{u, u} B S hS b hb).mapDerivedCategory
  let χ : (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj F ≅
      (etaleModulePullback.{u, u} B S hS a₁ ha₁).mapDerivedCategory.obj Q₁ ⊞
        ((etaleModulePullback.{u, u} B S hS a₁ ha₁).mapDerivedCategory.obj Q₁)⟦(1 : ℤ)⟧ :=
    ((derivedEtaleRestrictComp b (edsOpenHom B S hS (W := Y₂) hsq') a hb
      (isEtale_edsOpenHom B S hS (W := Y₂) hsq') ha hab).app F).symm ≪≫ G.mapIso eF ≪≫
      mapBiprodShiftOneIso G Q₁' ≪≫
      biprodShiftOneMapIso ((derivedEtaleRestrictComp b eU.inv a₁ hb hU ha₁ (by simp [b])).app Q₁)
  exact exists_retract_of_iso χ (s₁ ≫ biprod.inl) (biprod.fst ≫ r₁) (by simp [h₁])

/-- **Stacks 09IX.** Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space
over `S`, `W` a quasi-compact open subspace of `X` and `P` a perfect object of `D(𝒪_W)`. Then `P`
is a direct summand of the restriction `Q|_W` of a perfect object `Q` of `D(𝒪_X)`: there are
`s : P ⟶ Q|_W` and `r : Q|_W ⟶ P` with `s ≫ r = 𝟙`.

The induction of Stacks 09IT on the quasi-compact opens containing `W`, with
`AlgebraicGeometry.Space.isSummandOfPerfectRestriction_step` as the inductive step. -/
@[stacks 09IX]
theorem exists_isPerfect_retract_restrict (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (W : Subfunctor X.1)
    (hW : IsOpenSubspace B S hS W) (hWqc : IsQuasiCompactSpace B S hS W.toFunctor)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P) :
    ∃ Q : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect Q ∧
      ∃ (s : P ⟶ (etaleModulePullback.{u, u} B S hS
          (ObjectProperty.homMk W.ι : openSubspaceSpace B S hS W hW ⟶ X)
          (isEtale_of_isOpenImmersion B S hS hW.2)).mapDerivedCategory.obj Q)
        (r : (etaleModulePullback.{u, u} B S hS
          (ObjectProperty.homMk W.ι : openSubspaceSpace B S hS W hW ⟶ X)
          (isEtale_of_isOpenImmersion B S hS hW.2)).mapDerivedCategory.obj Q ⟶ P),
        s ≫ r = 𝟙 P := by
  have htop := isOpenSubspace_top (B := B) (S := S) (hS := hS) X.2
  obtain ⟨Q, hQ, hret⟩ := qcqs_induction_on_enlargement B S hS hZ X hXqc hXqs W hW hWqc
    (IsSummandOfPerfectRestriction hW P) (isSummandOfPerfectRestriction_self hW P hP)
    (fun W₁ W₂ hW₁ hW₂ hW₁qc _ hle hWW₁ _ f hV hsq IH =>
      isSummandOfPerfectRestriction_step hZ hXqs hW P hW₁ hW₂ hW₁qc hle hWW₁ f hV hsq IH) htop
  let φT : (⊤ : Subfunctor X.1).toFunctor ≅ X.1 := asIso (⊤ : Subfunctor X.1).ι
  let eT : openSubspaceSpace B S hS (⊤ : Subfunctor X.1) htop ≅ X := ObjectProperty.isoMk _ φT
  have hT := isEtale_hom_of_iso B S hS eT.symm
  let i : openSubspaceSpace B S hS W hW ⟶ X := ObjectProperty.homMk W.ι
  have hi : IsEtale B S hS i.hom := isEtale_of_isOpenImmersion B S hS hW.2
  let a := i ≫ eT.inv
  have ha : IsEtale B S hS a.hom := isEtale_comp B S hS hi hT
  have hai : a.hom ≫ (⊤ : Subfunctor X.1).ι = W.ι := by
    show W.ι ≫ inv (⊤ : Subfunctor X.1).ι ≫ (⊤ : Subfunctor X.1).ι = W.ι
    simp
  obtain ⟨s, r, h⟩ := hret a ha hai
  let χ := (derivedEtaleRestrictComp i eT.inv a hi hT ha rfl).app Q
  exact ⟨_, isPerfect_etaleModulePullback_standard B S hS eT.inv hT Q hQ,
    exists_retract_of_iso χ s r h⟩

end AlgebraicGeometry.Space

end
