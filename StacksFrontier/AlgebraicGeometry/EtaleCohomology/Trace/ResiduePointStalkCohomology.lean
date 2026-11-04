module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageStalkChainNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPointExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPointRational

/-!
# The stalk at a point with finite residue field inside `H⁰_c(Spec κ̄, i⁻¹ -)`

Let `w` be a point of `W` with finite residue field `κ`, `i : Spec κ ⟶ W` the canonical morphism
and `x₀` the point of `Spec κ`. For a sheaf `M` of `ℤ_ℓ`-modules on `W_étale` the stalk of `M` at
the geometric point at `i(x₀) = w` embeds into `H⁰_c(Spec κ̄, i⁻¹ M)`, naturally in `M`, carrying
the geometric Frobenius at `w` to the Frobenius of `κ`. The embedding is the stalk of the inverse
image at `x₀` (`Stacks.EtaleCohomology.rationalPointStalkPullbackIso`) followed by the embedding of
the stalk into `H⁰_c` of `Stacks.EtaleCohomology.closedPartStalkCompactSupportInput` for `Spec κ`.

## Main definitions

* `Stacks.EtaleCohomology.residuePointStalkEmbedding`: the natural map from the stalk at the
  geometric point at `w` to `H⁰_c(Spec κ̄, i⁻¹ -)`.

## Main results

* `Stacks.EtaleCohomology.injective_residuePointStalkEmbedding_app`: each component of
  `residuePointStalkEmbedding` is injective.
* `Stacks.EtaleCohomology.frobeniusStalk_comp_residuePointStalkEmbedding_app`: the embedding
  carries the geometric Frobenius at `w` to the Frobenius of `κ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Point

variable (κ : Type u) [Field κ]

/-- The point of `Spec κ`. -/
abbrev residuePoint : Spec (.of κ) := default

/-- The point of `Spec κ` is closed. -/
theorem isClosed_residuePoint : IsClosed ({residuePoint κ} : Set (Spec (.of κ))) := by
  rw [Set.eq_univ_of_forall (fun y => Set.mem_singleton_iff.2 (Subsingleton.elim y _))]
  exact isClosed_univ

/-- The residue field at the point of `Spec κ` is finite when `κ` is. -/
instance finite_residueField_residuePoint [Finite κ] :
    Finite ((Spec (.of κ)).residueField (residuePoint κ)) :=
  finite_residueField (𝟙 _) (residuePoint κ) (isClosed_residuePoint κ)

/-- `Spec κ(x₀)` has as many elements as `κ`. -/
theorem natCard_residueField_residuePoint [Fintype κ] :
    Nat.card ((Spec (.of κ)).residueField (residuePoint κ)) = Fintype.card κ :=
  natCard_residueField_of_residueDegree_eq_one (𝟙 _) (residuePoint κ)
    (residueDegree_id_spec κ (residuePoint κ))

end Point

/-! ### The embedding on `Spec κ` -/

section SpecField

variable (ℓ : ℕ) [Fact ℓ.Prime] (κ : Type u) [Field κ] [Fintype κ] (kbar : Type u) [Field kbar]
  [Algebra κ kbar] [IsAlgClosure κ kbar] (p n : ℕ) [Fact p.Prime] [CharP κ p]
  (hcard : Fintype.card κ = p ^ n)

/-- `M ↦ H⁰_c(Spec κ̄, M)` on sheaves of `ℤ_ℓ`-modules on `Spec κ`. -/
abbrev specFieldCohomology : EtaleModules.{u, 0} ℤ_[ℓ] (Spec (.of κ)) ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
  compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _)) kbar 0

/-- `i_* i⁻¹ = 𝟭` for the identity `i` of `Spec κ`. -/
def specFieldClosedPartIso :
    etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ))) ≅ 𝟭 (EtaleModules.{u, 0} ℤ_[ℓ] (Spec (.of κ))) :=
  Functor.isoWhiskerRight (etaleModuleInverseImageIdIso.{u, 0} ℤ_[ℓ] (Spec (.of κ)))
      (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (𝟙 (Spec (.of κ)))) ≪≫
    Functor.leftUnitor _ ≪≫ etaleModuleDirectImageIdIso ℤ_[ℓ] (Spec (.of κ))

/-- There are `dy > 0` with `#κ(x₀) = (p ^ n) ^ dy` and an injective natural map from the stalk
at the geometric point of `Spec κ` to `H⁰_c(Spec κ̄, i_* i⁻¹ -)` carrying the geometric Frobenius
to the `dy`-th power of the Frobenius. -/
theorem exists_specFieldStalk_closedPart :
    ∃ (dy : ℕ) (_ : 0 < dy)
      (_ : Nat.card ((Spec (.of κ)).residueField (residuePoint κ)) = (p ^ n) ^ dy)
      (s : (Scheme.pointSmallEtale
          (geometricPointAt (Spec (.of κ)) (residuePoint κ)).hom).sheafFiber ⟶
        etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ))) ⋙ specFieldCohomology ℓ κ kbar),
      (∀ G, Function.Injective (s.app G).hom) ∧
      ∀ G, (s.app G).hom ∘ₗ (frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) (Spec (.of κ))
          (residuePoint κ) G).hom =
        (((compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _))
          kbar p n hcard 0).app ((etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ)))).obj G)).hom ^
            dy) ∘ₗ (s.app G).hom :=
  closedPartStalkCompactSupportInput (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _)) kbar
    p n hcard (𝟙 (Spec (.of κ))) (residuePoint κ) ⟨residuePoint κ, rfl⟩ ℤ_[ℓ]

/-- **The stalk of a sheaf on `Spec κ` at its geometric point embeds into `H⁰_c(Spec κ̄, -)`**,
naturally in the sheaf. -/
def specFieldStalkEmbedding :
    (Scheme.pointSmallEtale (geometricPointAt (Spec (.of κ)) (residuePoint κ)).hom).sheafFiber ⟶
      specFieldCohomology ℓ κ kbar :=
  (exists_specFieldStalk_closedPart ℓ κ kbar p n hcard).choose_spec.choose_spec.choose_spec.choose ≫
    Functor.whiskerRight (specFieldClosedPartIso ℓ κ).hom (specFieldCohomology ℓ κ kbar)

/-- Each component of `Stacks.EtaleCohomology.specFieldStalkEmbedding` is injective. -/
theorem injective_specFieldStalkEmbedding_app (G : EtaleModules.{u, 0} ℤ_[ℓ] (Spec (.of κ))) :
    Function.Injective ((specFieldStalkEmbedding ℓ κ kbar p n hcard).app G).hom := by
  have h := (exists_specFieldStalk_closedPart ℓ κ kbar p n hcard).choose_spec.choose_spec
    |>.choose_spec.choose_spec.1 G
  have hi : Function.Injective ((specFieldCohomology ℓ κ kbar).map
      ((specFieldClosedPartIso ℓ κ).hom.app G)).hom :=
    (ConcreteCategory.bijective_of_isIso ((specFieldCohomology ℓ κ kbar).map
      ((specFieldClosedPartIso ℓ κ).hom.app G))).1
  exact hi.comp h

/-- A map of stalks carrying the geometric Frobenius to `π^{dy}`, where `#κ(x₀) = (p ^ n)^{dy}`,
carries it to `π`. -/
theorem frobeniusStalk_comp_eq_of_pow (dy : ℕ)
    (hdy : Nat.card ((Spec (.of κ)).residueField (residuePoint κ)) = (p ^ n) ^ dy)
    (s : (Scheme.pointSmallEtale
          (geometricPointAt (Spec (.of κ)) (residuePoint κ)).hom).sheafFiber ⟶
        etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ))) ⋙ specFieldCohomology ℓ κ kbar)
    (G : EtaleModules.{u, 0} ℤ_[ℓ] (Spec (.of κ)))
    (hfr : (s.app G).hom ∘ₗ (frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) (Spec (.of κ))
          (residuePoint κ) G).hom =
        (((compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _))
          kbar p n hcard 0).app ((etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ)))).obj G)).hom ^
            dy) ∘ₗ (s.app G).hom) :
    frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) (Spec (.of κ)) (residuePoint κ) G ≫
        (s ≫ Functor.whiskerRight (specFieldClosedPartIso ℓ κ).hom
          (specFieldCohomology ℓ κ kbar)).app G =
      (s ≫ Functor.whiskerRight (specFieldClosedPartIso ℓ κ).hom
          (specFieldCohomology ℓ κ kbar)).app G ≫
        (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _))
          kbar p n hcard 0).app G := by
  have hone : dy = 1 := by
    rw [natCard_residueField_residuePoint, hcard] at hdy
    have h2 : 2 ≤ p ^ n := hcard ▸ Fintype.one_lt_card
    exact Nat.pow_right_injective h2 (hdy.symm.trans (pow_one _).symm)
  subst hone
  rw [pow_one] at hfr
  have hsq : frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) (Spec (.of κ)) (residuePoint κ) G ≫ s.app G =
      s.app G ≫ (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ)))
        (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0).app
          ((etaleModuleClosedPart ℤ_[ℓ] (𝟙 (Spec (.of κ)))).obj G) :=
    ModuleCat.hom_ext hfr
  exact comm_comp_of_comm hsq ((compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ)))
    (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0).naturality
      ((specFieldClosedPartIso ℓ κ).hom.app G)).symm

/-- **The embedding carries the geometric Frobenius to the Frobenius of `κ`.** -/
theorem frobeniusStalk_comp_specFieldStalkEmbedding_app
    (G : EtaleModules.{u, 0} ℤ_[ℓ] (Spec (.of κ))) :
    frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) (Spec (.of κ)) (residuePoint κ) G ≫
        (specFieldStalkEmbedding ℓ κ kbar p n hcard).app G =
      (specFieldStalkEmbedding ℓ κ kbar p n hcard).app G ≫
        (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ))) (CompactificationOf.ofProper (𝟙 _))
          kbar p n hcard 0).app G :=
  frobeniusStalk_comp_eq_of_pow ℓ κ kbar p n hcard _
    (exists_specFieldStalk_closedPart ℓ κ kbar p n hcard).choose_spec.choose_spec.choose _ G
    ((exists_specFieldStalk_closedPart ℓ κ kbar p n hcard).choose_spec.choose_spec.choose_spec
      |>.choose_spec.2 G)

end SpecField

/-! ### The embedding on `W` -/

section Embedding

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {W : B.Scheme} (w : W.1)
  [Fintype (W.1.residueField w)] (kbar : Type u) [Field kbar]
  [Algebra (W.1.residueField w) kbar] [IsAlgClosure (W.1.residueField w) kbar] (p n : ℕ)
  [Fact p.Prime] [CharP (W.1.residueField w) p] (hcard : Fintype.card (W.1.residueField w) = p ^ n)

/-- The image in `W` of the point of `Spec κ(w)`; it is `w`
(`Stacks.EtaleCohomology.residuePointImage_eq`). -/
abbrev residuePointImage : W.1 :=
  (B.inclusion.map (residueFieldPointHom B w)).base (residuePoint (W.1.residueField w))

/-- The image in `W` of the point of `Spec κ(w)` is `w`. -/
theorem residuePointImage_eq : residuePointImage B w = w :=
  Scheme.fromSpecResidueField_apply _ _

/-- The residue field of `W` at the image of the point of `Spec κ(w)` is finite. -/
instance finite_residueField_residuePointImage :
    Finite (W.1.residueField (residuePointImage B w)) := by
  rw [residuePointImage_eq]
  infer_instance

/-- The rational point `Spec κ(x₀) ⟶ Spec κ(w)` of the point `x₀` of `Spec κ(w)`. -/
abbrev residuePointRational :
    Spec (.of ((Spec (.of (W.1.residueField w))).residueField
      (residuePoint (W.1.residueField w)))) ⟶
      Spec (.of (W.1.residueField w)) :=
  (Spec (.of (W.1.residueField w))).fromSpecResidueField (residuePoint (W.1.residueField w))

/-- The morphism from the geometric point over the rational point `Spec κ(x₀) ⟶ W` to the geometric
point at its image. -/
def residuePointGeometricHom :
    GeometricPoint.Hom (rationalGeometricPoint (AlgebraicClosure
        ((Spec (.of (W.1.residueField w))).residueField (residuePoint (W.1.residueField w))))
        (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w)))
      (geometricPointAt W.1 (residuePointImage B w)) :=
  (rationalGeometricPointMapHom (B.inclusion.map (residueFieldPointHom B w))
    (AlgebraicClosure ((Spec (.of (W.1.residueField w))).residueField
      (residuePoint (W.1.residueField w))))
    (residuePointRational B w)
    (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w))
    rfl).comp (residueClosurePointHom (B.inclusion.map (residueFieldPointHom B w))
      (residuePoint (W.1.residueField w)))

/-- **The stalk at the geometric point at `w` embeds into `H⁰_c(Spec κ̄, i⁻¹ -)`**, naturally in
the sheaf: the stalk of the inverse image at the point of `Spec κ(w)`, then
`Stacks.EtaleCohomology.specFieldStalkEmbedding`. -/
def residuePointStalkEmbedding :
    (Scheme.pointSmallEtale (geometricPointAt W.1 (residuePointImage B w)).hom).sheafFiber
        (A := ModuleCat.{u + 1} ℤ_[ℓ]) ⟶ residuePointCohomology B ℓ w kbar :=
  (GrothendieckTopology.Point.sheafFiberIsoOfIso (A := ModuleCat.{u + 1} ℤ_[ℓ])
      (@asIso _ _ _ _ (smallEtalePointHom W.1 (residuePointGeometricHom B w))
        (smallEtalePointHom_isIso _ _))).hom ≫
    (rationalPointStalkPullbackIso ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w))
      (AlgebraicClosure ((Spec (.of (W.1.residueField w))).residueField
        (residuePoint (W.1.residueField w))))
      (residuePointRational B w)
    (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w))
      rfl).inv ≫
    Functor.whiskerLeft
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w)))
      (specFieldStalkEmbedding ℓ (W.1.residueField w) kbar p n hcard)

/-- Each component of `Stacks.EtaleCohomology.residuePointStalkEmbedding` is injective. -/
theorem injective_residuePointStalkEmbedding_app (M : EtaleModules.{u, 0} ℤ_[ℓ] W.1) :
    Function.Injective ((residuePointStalkEmbedding B ℓ w kbar p n hcard).app M).hom := by
  unfold residuePointStalkEmbedding
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact ((injective_specFieldStalkEmbedding_app ℓ (W.1.residueField w) kbar p n hcard _).comp
    (ConcreteCategory.bijective_of_isIso _).1).comp (ConcreteCategory.bijective_of_isIso _).1

/-- **The embedding carries the geometric Frobenius at `w` to the Frobenius of `κ(w)`.** -/
theorem frobeniusStalk_comp_residuePointStalkEmbedding_app (M : EtaleModules.{u, 0} ℤ_[ℓ] W.1) :
    frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 (residuePointImage B w) M ≫
        (residuePointStalkEmbedding B ℓ w kbar p n hcard).app M =
      (residuePointStalkEmbedding B ℓ w kbar p n hcard).app M ≫
        (residuePointFrobenius B ℓ w kbar p n hcard).app M := by
  let κ₀ := (Spec (.of (W.1.residueField w))).residueField (residuePoint (W.1.residueField w))
  let : Fintype κ₀ := Fintype.ofFinite _
  have hcard₀ : Fintype.card κ₀ = p ^ n := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField_residuePoint, hcard]
  have : CharP κ₀ p := charP_of_injective_ringHom
    (fieldToResidue (𝟙 (Spec (.of (W.1.residueField w)))) (residuePoint _)).hom.injective p
  have : CharP (AlgebraicClosure κ₀) p :=
    charP_of_injective_algebraMap (algebraMap κ₀ (AlgebraicClosure κ₀)).injective p
  have hres : Nat.card (W.1.residueField (residuePointImage B w)) = Fintype.card κ₀ := by
    rw [residuePointImage_eq, Nat.card_eq_fintype_card, hcard, hcard₀]
  have h1 := NatTrans.congr_app (frobeniusStalkFunctor_comm_of_hom_to (ModuleCat.{u + 1} ℤ_[ℓ])
    W.1 (residuePointImage B w) (AlgebraicClosure κ₀) p n hcard₀
    (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w))
    (residuePointGeometricHom B w) hres) M
  let e := (rationalPointStalkPullbackIso ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w))
    (AlgebraicClosure κ₀) (residuePointRational B w)
    (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w)) rfl).app M
  have h2 := comp_inv_eq_inv_comp_of_hom_comm e e _ _
    (geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom ℤ_[ℓ]
      (B.inclusion.map (residueFieldPointHom B w)) (AlgebraicClosure κ₀) (residuePointRational B w)
      (residuePointRational B w ≫ B.inclusion.map (residueFieldPointHom B w)) rfl p n hcard₀ M)
  have h3 := frobeniusStalk_comp_specFieldStalkEmbedding_app ℓ (W.1.residueField w) kbar p n hcard
    ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w))).obj M)
  rw [frobeniusStalk_eq_geometricFrobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ])
    (Spec (.of (W.1.residueField w))) (residuePoint _) p n hcard₀] at h3
  exact comm_comp_of_comm h1.symm (comm_comp_of_comm h2 h3)

end Embedding

end Stacks.EtaleCohomology
