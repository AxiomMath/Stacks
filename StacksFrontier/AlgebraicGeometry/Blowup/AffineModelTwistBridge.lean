module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedDirectSums
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChart

/-!
# The two twisting sheaves of a blowup agree at the affine local model

`AlgebraicGeometry.blowUpTwist I n` is the `n`-th twisting sheaf of the relative `Proj` of the
Rees algebra of a quasi-coherent sheaf of ideals `I ⊆ 𝒪_X`, on `AlgebraicGeometry.blowUp I`;
`Stacks.Blowup.blowUpTwist m n` is the twisting sheaf `𝒪(n)` of `Proj (A[mt])`, on the affine
model `Stacks.Blowup.blowUpSpec m = Proj (reesGrading m)`. Over an affine base the two schemes are
isomorphic over the base, and this isomorphism carries one twisting sheaf onto the other in every
degree. No hypothesis on the ring `A` or on the ideal `m` is needed.

## Main definitions

* `Stacks.Blowup.AffineModel.projIsoBlowUp`: over an affine base, `Proj` of the Rees algebra of
  the ideal of global sections of `I` is `AlgebraicGeometry.blowUp I`.
* `Stacks.Blowup.AffineModel.projIsoBlowUpTwistIso`: the transport of `𝒪_{X'}(n)` to that
  `Proj`, in every degree.
* `Stacks.Blowup.AffineModel.specProjIso` and
  `Stacks.Blowup.AffineModel.specProjTwistIso`: the same two statements for the ideal sheaf
  `Stacks.Blowup.AffineModel.specIdealSheaf m` on `Spec A` defined by an ideal `m ⊆ A`, where the
  affine model is `Stacks.Blowup.blowUpSpec m` and the twist is `Stacks.Blowup.blowUpTwist m n`.

## Main results

* `Stacks.Blowup.AffineModel.projIsoBlowUp_hom_blowUpToBase` and
  `Stacks.Blowup.AffineModel.specProjIso_hom_blowUpToBase`: the two comparisons are
  isomorphisms over the base.
* `Stacks.Blowup.AffineModel.exists_iso_blowUpTwist` and
  `Stacks.Blowup.AffineModel.exists_iso_blowUpTwist_of_ideal_eq`: an isomorphism of the affine
  model with the blowup over the base, carrying `AlgebraicGeometry.blowUpTwist` onto
  `Stacks.Blowup.blowUpTwist` in every degree.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open Stacks.RelativeProj Stacks.RelativeProj.Situation Stacks.ProjTwistComparison

universe u

namespace Stacks.Blowup.AffineModel

/-! ### The blowup of an affine scheme -/

section AffineBase

variable {X : Scheme.{u}} [IsAffine X] (J : X.IdealSheafData) (n : ℤ)

/-- The whole space of an affine scheme, as an affine open. -/
abbrev wholeSpace (X : Scheme.{u}) [IsAffine X] : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩

/-- The chart of the blowup of an affine scheme over its whole space is an isomorphism. -/
instance isIso_relativeProjChart_wholeSpace :
    IsIso (relativeProjChart (AlgebraicGeometry.reesSituation J) (wholeSpace X)) :=
  haveI : IsIso ((wholeSpace X).1.ι) := inferInstanceAs (IsIso (Scheme.topIso X).hom)
  (relativeProjChart_isPullback (AlgebraicGeometry.reesSituation J)
    (wholeSpace X)).isIso_fst_of_isIso

/-- **Over an affine base the blowup is `Proj` of the Rees algebra of the ideal of global
sections of the centre.** -/
def projIsoBlowUp :
    AlgebraicGeometry.Proj (reesGrading (J.ideal (wholeSpace X))) ≅ AlgebraicGeometry.blowUp J :=
  ((AlgebraicGeometry.reesDataIso J).projIso (wholeSpace X)).symm ≪≫
    asIso (relativeProjChart (AlgebraicGeometry.reesSituation J) (wholeSpace X))

/-- The comparison `Stacks.Blowup.AffineModel.projIsoBlowUp` is the chart of
`Stacks.Blowup.blowUp` over the whole space followed by the inverse of
`AlgebraicGeometry.blowUpIso`. -/
theorem projIsoBlowUp_hom_eq :
    (projIsoBlowUp J).hom =
      Stacks.Blowup.blowUpChart J (wholeSpace X) ≫ (AlgebraicGeometry.blowUpIso J).inv := by
  rw [Iso.eq_comp_inv]
  change (((AlgebraicGeometry.reesDataIso J).projIso (wholeSpace X)).inv ≫
    relativeProjChart (AlgebraicGeometry.reesSituation J) (wholeSpace X)) ≫
      (AlgebraicGeometry.blowUpIso J).hom = _
  rw [Category.assoc, AlgebraicGeometry.relativeProjChart_blowUpIso_hom, Iso.inv_hom_id_assoc]

/-- **The comparison is an isomorphism over the base**: it carries the structure morphism of the
affine model to the blowup morphism. -/
theorem projIsoBlowUp_hom_blowUpToBase :
    (projIsoBlowUp J).hom ≫ AlgebraicGeometry.blowUpToBase J =
      Stacks.Blowup.toSpec (J.ideal (wholeSpace X)) ≫
        (Stacks.RelativeProj.isAffineOpen (wholeSpace X)).isoSpec.inv ≫
          (wholeSpace X).1.ι := by
  rw [projIsoBlowUp_hom_eq, Category.assoc,
    (AlgebraicGeometry.blowUpIso J).inv_comp_eq.2
      (AlgebraicGeometry.blowUpIso_hom_blowUpToBase J).symm,
    Stacks.Blowup.blowUpChart_blowUpToBase]
  exact Category.assoc _ _ _

/-- The twist comparison of the two graded rings over the whole space is invertible. -/
theorem isIso_twistMap_reesDataIso_hom :
    IsIso (twistMap ((AlgebraicGeometry.reesDataIso J).hom (wholeSpace X))
      ((AlgebraicGeometry.reesDataIso J).irrelevant_le_hom (wholeSpace X)) n) :=
  isIso_twistMap_of_comp_eq_id _ _ n ((AlgebraicGeometry.reesDataIso J).inv (wholeSpace X))
    ((AlgebraicGeometry.reesDataIso J).hom_comp_inv (wholeSpace X))
    ((AlgebraicGeometry.reesDataIso J).inv_comp_hom (wholeSpace X))

/-- **The twisting sheaf of the blowup of an affine scheme, read on `Proj` of the Rees algebra of
the ideal of global sections of the centre**: `d^* 𝒪_{X'}(n) ≅ 𝒪(n)` for `d` the comparison
`Stacks.Blowup.AffineModel.projIsoBlowUp`, in every degree. The right-hand side is
`Stacks.Blowup.blowUpTwist (J.ideal ⊤) n`. -/
def projIsoBlowUpTwistIso :
    (Scheme.Modules.pullback (projIsoBlowUp J).hom).obj (AlgebraicGeometry.blowUpTwist J n)
      ≅ ProjectiveSpectrum.Proj.twistingSheaf (reesGrading (J.ideal (wholeSpace X))) n :=
  haveI := isIso_twistMap_reesDataIso_hom J n
  Scheme.Modules.pullbackIsoOfRestrictIso
      (relativeProjChart (AlgebraicGeometry.reesSituation J) (wholeSpace X))
      (AlgebraicGeometry.blowUpTwistChartIso J n (wholeSpace X))
      (AlgebraicGeometry.Proj.map ((AlgebraicGeometry.reesDataIso J).hom (wholeSpace X))
        ((AlgebraicGeometry.reesDataIso J).irrelevant_le_hom (wholeSpace X))) rfl ≪≫
    asIso (twistMap ((AlgebraicGeometry.reesDataIso J).hom (wholeSpace X))
      ((AlgebraicGeometry.reesDataIso J).irrelevant_le_hom (wholeSpace X)) n)

/-- **The two blowup twists agree over an affine base**, at a named ideal of global sections: the
affine model `Proj (Γ(X)[Lt])` is the blowup of `X` in `J`, over `X`, and that isomorphism
carries `AlgebraicGeometry.blowUpTwist` onto `Stacks.Blowup.blowUpTwist` in every degree. -/
theorem exists_iso_blowUpTwist_of_ideal_eq (L : Ideal ↥Γ(X, (wholeSpace X).1))
    (hL : J.ideal (wholeSpace X) = L) :
    ∃ d : Stacks.Blowup.blowUpSpec L ≅ AlgebraicGeometry.blowUp J,
      d.hom ≫ AlgebraicGeometry.blowUpToBase J =
          Stacks.Blowup.toSpec L ≫
            (Stacks.RelativeProj.isAffineOpen (wholeSpace X)).isoSpec.inv ≫
              (wholeSpace X).1.ι ∧
        ∀ q : ℤ, Nonempty ((Scheme.Modules.pullback d.hom).obj
          (AlgebraicGeometry.blowUpTwist J q) ≅ Stacks.Blowup.blowUpTwist L q) := by
  subst hL
  exact ⟨projIsoBlowUp J, projIsoBlowUp_hom_blowUpToBase J,
    fun q => ⟨projIsoBlowUpTwistIso J q⟩⟩

end AffineBase

/-! ### The affine local model -/

section Affine

variable {A : Type u} [CommRing A] (m : Ideal A) (n : ℤ)

/-- The counit followed by the unit of `Γ(Spec A, ⊤) ≅ A` is the identity ring map. -/
private theorem hom_comp_inv_ΓSpecIso :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom =
      RingHom.id A :=
  congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id

/-- The unit followed by the counit of `Γ(Spec A, ⊤) ≅ A` is the identity ring map. -/
private theorem inv_comp_hom_ΓSpecIso :
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
      RingHom.id _ :=
  congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

/-- The quasi-coherent sheaf of ideals on `Spec A` defined by an ideal `m ⊆ A`. -/
def specIdealSheaf : (Spec (CommRingCat.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom m)

/-- Its ideal of global sections is the transport of `m` along the counit `Γ(Spec A, ⊤) ≅ A`. -/
theorem ideal_specIdealSheaf :
    (specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A))) =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom m :=
  Stacks.Blowup.ideal_ofIdealTop_top _

/-- The counit carries that ideal of global sections back to `m`. -/
theorem map_ideal_specIdealSheaf :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A)))) = m := by
  rw [ideal_specIdealSheaf, Ideal.map_map,
    hom_comp_inv_ΓSpecIso,
    Ideal.map_id]

/-- The Rees algebra of the ideal of global sections, transported to the Rees algebra of `m`
along the counit `Γ(Spec A, ⊤) ≅ A`. -/
def specReesHom :
    reesGrading ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A)))) →+*ᵍ
      reesGrading m :=
  Stacks.Blowup.reesGradedHom (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _ m
    (map_ideal_specIdealSheaf m)

/-- The transport in the other direction, along the unit `A ≅ Γ(Spec A, ⊤)`. -/
def specReesInv :
    reesGrading m →+*ᵍ
      reesGrading ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A)))) :=
  Stacks.Blowup.reesGradedHom (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom m _
    (ideal_specIdealSheaf m).symm

/-- The two transports are inverse. -/
theorem specReesHom_comp_specReesInv :
    (specReesHom m).comp (specReesInv m) = GradedRingHom.id (reesGrading m) :=
  Stacks.Blowup.reesGradedHom_comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom m _
    (ideal_specIdealSheaf m).symm (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (map_ideal_specIdealSheaf m)
    (hom_comp_inv_ΓSpecIso)

/-- The two transports are inverse in the other order. -/
theorem specReesInv_comp_specReesHom :
    (specReesInv m).comp (specReesHom m) =
      GradedRingHom.id
        (reesGrading ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A))))) :=
  Stacks.Blowup.reesGradedHom_comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _ m
    (map_ideal_specIdealSheaf m) (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ideal_specIdealSheaf m).symm
    (inv_comp_hom_ΓSpecIso)

/-- The irrelevant ideal of the Rees algebra of `m` is contained in the image of the irrelevant
ideal under the transport `Stacks.Blowup.AffineModel.specReesHom m`. -/
theorem irrelevant_le_specReesHom :
    (reesGrading m)₊ ≤
      ((reesGrading ((specIdealSheaf m).ideal
        (wholeSpace (Spec (CommRingCat.of A)))))₊).map (specReesHom m) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
    (Stacks.Blowup.surjective_reesGradedHom (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _ m
      (map_ideal_specIdealSheaf m) (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (ideal_specIdealSheaf m).symm
      (hom_comp_inv_ΓSpecIso))

/-- `Proj` of the transport of the Rees algebra is an isomorphism of affine models. -/
theorem isIso_projMap_specReesHom :
    IsIso (AlgebraicGeometry.Proj.map (specReesHom m) (irrelevant_le_specReesHom m)) :=
  Stacks.Blowup.isIso_map_reesGradedHom (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _ m
    (map_ideal_specIdealSheaf m) (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ideal_specIdealSheaf m).symm
    (inv_comp_hom_ΓSpecIso)
    (hom_comp_inv_ΓSpecIso)

/-- **The affine blowup of `m ⊆ A` is the blowup of `Spec A` in the sheaf of ideals `m`
defines.** -/
def specProjIso :
    AlgebraicGeometry.Proj (reesGrading m) ≅ AlgebraicGeometry.blowUp (specIdealSheaf m) :=
  haveI := isIso_projMap_specReesHom m
  asIso (AlgebraicGeometry.Proj.map (specReesHom m) (irrelevant_le_specReesHom m)) ≪≫
    projIsoBlowUp (specIdealSheaf m)

/-- The comparison of affine models is the transport of the Rees algebra followed by the
comparison over the affine base. -/
theorem specProjIso_hom :
    (specProjIso m).hom =
      AlgebraicGeometry.Proj.map (specReesHom m) (irrelevant_le_specReesHom m) ≫
        (projIsoBlowUp (specIdealSheaf m)).hom :=
  rfl

/-- **The comparison of affine models is an isomorphism over `Spec A`.** -/
theorem specProjIso_hom_blowUpToBase :
    (specProjIso m).hom ≫ AlgebraicGeometry.blowUpToBase (specIdealSheaf m) =
      Stacks.Blowup.toSpec m := by
  obtain ⟨t, ht⟩ : ∃ t : AlgebraicGeometry.Proj (reesGrading m) ⟶ Spec (CommRingCat.of A),
      t = Stacks.Blowup.toSpec m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : AlgebraicGeometry.Proj (reesGrading
        ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A))))) ⟶
        Spec (CommRingCat.of
          ↥Γ(Spec (CommRingCat.of A), (wholeSpace (Spec (CommRingCat.of A))).1)),
      s = Stacks.Blowup.toSpec
        ((specIdealSheaf m).ideal (wholeSpace (Spec (CommRingCat.of A)))) := ⟨_, rfl⟩
  have hκ : (Stacks.RelativeProj.isAffineOpen
        (wholeSpace (Spec (CommRingCat.of A)))).isoSpec.inv ≫
      (wholeSpace (Spec (CommRingCat.of A))).1.ι =
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    change (isAffineOpen_top (Spec (CommRingCat.of A))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hw : (projIsoBlowUp (specIdealSheaf m)).hom ≫
      AlgebraicGeometry.blowUpToBase (specIdealSheaf m) =
        s ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    rw [projIsoBlowUp_hom_blowUpToBase, hκ, hs]
    rfl
  have hθ : AlgebraicGeometry.Proj.map (specReesHom m) (irrelevant_le_specReesHom m) ≫ s =
      t ≫ Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) := by
    rw [hs, ht]
    exact Stacks.Blowup.map_reesGradedHom_comp_toSpec _ _ _ (map_ideal_specIdealSheaf m) _
  rw [← ht, specProjIso_hom, Category.assoc, hw, ← Category.assoc, hθ, Category.assoc,
    ← Spec.map_comp, CommRingCat.ofHom_hom,
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id, Spec.map_id, Category.comp_id]

/-- The twist comparison of the transport of the Rees algebra is invertible. -/
theorem isIso_twistMap_specReesHom :
    IsIso (twistMap (specReesHom m) (irrelevant_le_specReesHom m) n) :=
  isIso_twistMap_of_comp_eq_id _ _ n (specReesInv m) (specReesHom_comp_specReesInv m)
    (specReesInv_comp_specReesHom m)

/-- **The twisting sheaf of the blowup of `Spec A` in `m`, read on the affine model**:
`d^* 𝒪_{X'}(n) ≅ 𝒪(n)` for `d` the comparison `Stacks.Blowup.AffineModel.specProjIso`, in every
degree. The right-hand side is `Stacks.Blowup.blowUpTwist m n`. -/
def specProjTwistIso :
    (Scheme.Modules.pullback (specProjIso m).hom).obj
        (AlgebraicGeometry.blowUpTwist (specIdealSheaf m) n)
      ≅ ProjectiveSpectrum.Proj.twistingSheaf (reesGrading m) n :=
  haveI := isIso_twistMap_specReesHom m n
  (Scheme.Modules.pullbackCongr (specProjIso_hom m)).app
      (AlgebraicGeometry.blowUpTwist (specIdealSheaf m) n) ≪≫
    ((Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Proj.map (specReesHom m) (irrelevant_le_specReesHom m))
        (projIsoBlowUp (specIdealSheaf m)).hom).app
      (AlgebraicGeometry.blowUpTwist (specIdealSheaf m) n)).symm ≪≫
    (Scheme.Modules.pullback
        (AlgebraicGeometry.Proj.map (specReesHom m)
          (irrelevant_le_specReesHom m))).mapIso
      (projIsoBlowUpTwistIso (specIdealSheaf m) n) ≪≫
    asIso (twistMap (specReesHom m) (irrelevant_le_specReesHom m) n)

/-- **The two blowup twists agree at the affine local model.** The affine model
`Proj (A[mt])` is the blowup of `Spec A` in the sheaf of ideals `m` defines, over `Spec A`, and
that isomorphism carries `AlgebraicGeometry.blowUpTwist` onto `Stacks.Blowup.blowUpTwist` in
every degree. -/
theorem exists_iso_blowUpTwist :
    ∃ d : Stacks.Blowup.blowUpSpec m ≅ AlgebraicGeometry.blowUp (specIdealSheaf m),
      d.hom ≫ AlgebraicGeometry.blowUpToBase (specIdealSheaf m) = Stacks.Blowup.toSpec m ∧
        ∀ n : ℤ, Nonempty ((Scheme.Modules.pullback d.hom).obj
          (AlgebraicGeometry.blowUpTwist (specIdealSheaf m) n) ≅
            Stacks.Blowup.blowUpTwist m n) :=
  ⟨specProjIso m, specProjIso_hom_blowUpToBase m, fun n => ⟨specProjTwistIso m n⟩⟩

end Affine

end Stacks.Blowup.AffineModel

end
