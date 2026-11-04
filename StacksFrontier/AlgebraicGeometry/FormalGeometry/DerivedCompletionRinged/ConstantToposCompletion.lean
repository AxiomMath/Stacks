module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantPushforwardCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCompletionTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion along a morphism of topoi, with constant Noetherian coefficients

Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and `f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi, read
as the morphism of ringed topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` of
`MorphismOfTopoi.constantRingedToposHom`. Write `D_comp(𝒞, Λ)` for the full subcategory of
`D(𝒞, Λ)` of the objects derived complete along `IΛ̲`. [Stacks, Tag 099N] asserts:

1. `Rf_*` sends `D_comp(𝒟, Λ)` into `D_comp(𝒞, Λ)`;
2. the resulting functor `Rf_* : D_comp(𝒟, Λ) ⥤ D_comp(𝒞, Λ)` has a left adjoint `Lf^*_comp`,
   namely `Lf^*` followed by derived completion;
3. `Rf_*` commutes with derived completion;
4. for `K` in `D_comp(𝒟, Λ)`, `Rf_*K = R lim Rf_*(K ⊗^𝐋_Λ (Λ/Iⁿ)̲)`;
5. for `M` in `D_comp(𝒞, Λ)`, `Lf^*_comp M = R lim Lf^*(M ⊗^𝐋_Λ (Λ/Iⁿ)̲)`.

## Main definitions

* `MorphismOfTopoi.constantDerivedCompletePushforward`: `Rf_* : D_comp(𝒟, Λ) ⥤ D_comp(𝒞, Λ)`.
* `MorphismOfTopoi.constantDerivedCompletePullback`: `Lf^*_comp : D_comp(𝒞, Λ) ⥤ D_comp(𝒟, Λ)`,
  `Lf^*` followed by derived completion.
* `MorphismOfTopoi.constantDerivedCompletePullbackPushforwardAdjunction`: **part (2)**.

## Main results

* `MorphismOfTopoi.isDerivedComplete_constantDerivedPushforward`: **part (1)**.
* `MorphismOfTopoi.isIso_derivedCompletionComparisonApp_constantDerivedPushforward`: **part (3)**,
  the canonical comparison `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible.
* `MorphismOfTopoi.isDerivedLimit_constantAdicTower_constantDerivedPushforward`: **part (4)**.
* `MorphismOfTopoi.isDerivedLimit_constantAdicTower_constantDerivedCompletePullback`:
  **part (5)**.

## Implementation notes

The proof is the source's. For parts (1) and (3), proved as
`MorphismOfTopoi.isDerivedComplete_constantDerivedPushforward` and
`MorphismOfTopoi.isIso_derivedCompletionComparisonApp_constantDerivedPushforward`, the source's
appeal to [Stacks, Tag 099K] and [Stacks, Tag 0A0G] is replaced by the computation of both sides
with [Stacks, Tag 099M]: the towers `n ↦ Rf_*K ⊗^𝐋 (Λ/Iⁿ)̲` and
`n ↦ Rf_*(K ⊗^𝐋 (Λ/Iⁿ)̲)` are pro-isomorphic, through the Koszul complexes and the projection
formula of [Stacks, Tag 0944] at strictly perfect complexes. Part (2) is the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] restricted along the reflection onto `D_comp(𝒟, Λ)`, which
exists by [Stacks, Tag 099F] because `IΛ̲` is of finite type. Part (4) is [Stacks, Tag 099M]
followed by [Stacks, Tag 0A07]; part (5) is [Stacks, Tag 099M] on `𝒟` together with
[Stacks, Tag 07A4] and the pro-isomorphism between `n ↦ Lf^*(Λ/Iⁿ)̲` and `n ↦ (Λ/Iⁿ)̲`.

The derived limit `R lim` is recorded by `CategoryTheory.Pretriangulated.IsDerivedLimit`, being
determined only up to non-unique isomorphism, and "commutes with derived completion" in part (3) is
the invertibility of the comparison map characterized by the universal property of derived
completion,
`AlgebraicGeometry.RingedSite.derivedCompletionUnit_comp_derivedCompletionComparisonApp`. The
source states part (5) for `M` derived complete; the proof gives it for every `M` in `D(𝒞, Λ)`, and
it is stated for `M` in `D_comp(𝒞, Λ)`, where `Lf^*_comp` is defined.

## References

* [Stacks Project, Tag 099N](https://stacks.math.columbia.edu/tag/099N)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 099K](https://stacks.math.columbia.edu/tag/099K)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry

universe u

namespace MorphismOfTopoi

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D} (Λ : Type u) [CommRing Λ]
  [IsNoetherianRing Λ] (I : Ideal Λ) (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))

/-- The inclusion of `D_comp(𝒟, Λ)`, the objects of `D(𝒟, Λ)` derived complete along `IΛ̲`, into
`D(𝒟, Λ)` is a right adjoint. -/
instance isRightAdjoint_ι_isDerivedComplete_constant :
    (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u}
      (RingedTopos.constant K Λ).toRingedSite
        (RingedSite.constantIdealSheaf K Λ I))).IsRightAdjoint :=
  RingedSite.isRightAdjoint_ι_isDerivedComplete (RingedSite.constant K Λ)
    (RingedSite.constantIdealSheaf K Λ I)

/-- **`Rf_* : D_comp(𝒟, Λ) ⥤ D_comp(𝒞, Λ)`**, the derived direct image restricted to the
derived-complete objects, which it preserves by part (1) of [Stacks, Tag 099N]. -/
def constantDerivedCompletePushforward :
    ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u}
        (RingedTopos.constant K Λ).toRingedSite (RingedSite.constantIdealSheaf K Λ I)) ⥤
      ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u}
        (RingedTopos.constant J Λ).toRingedSite (RingedSite.constantIdealSheaf J Λ I)) :=
  RingedToposHom.derivedCompletePushforwardOfPreserves (constantRingedToposHom Λ f) _ _
    fun E => isDerivedComplete_constantDerivedPushforward Λ f I E.1 E.2

/-- **`Lf^*_comp : D_comp(𝒞, Λ) ⥤ D_comp(𝒟, Λ)`**: the derived pullback `Lf^*` followed by
derived completion along `IΛ̲`. -/
def constantDerivedCompletePullback :
    ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u}
        (RingedTopos.constant J Λ).toRingedSite (RingedSite.constantIdealSheaf J Λ I)) ⥤
      ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u}
        (RingedTopos.constant K Λ).toRingedSite (RingedSite.constantIdealSheaf K Λ I)) :=
  RingedToposHom.derivedCompletePullback (constantRingedToposHom Λ f) _ _

/-- `Lf^*_comp`, read in `D(𝒟, Λ)`, is `Lf^*` followed by the derived completion functor. -/
theorem constantDerivedCompletePullback_comp_ι :
    constantDerivedCompletePullback Λ I f ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ constantDerivedPullback Λ f ⋙
        RingedSite.derivedCompletion (RingedSite.constant K Λ)
          (RingedSite.constantIdealSheaf K Λ I) :=
  rfl

/-- **[Stacks, Tag 099N], part (2).** Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and
`f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi. The functor `Rf_* : D_comp(𝒟, Λ) ⥤ D_comp(𝒞, Λ)` has
a left adjoint `Lf^*_comp : D_comp(𝒞, Λ) ⥤ D_comp(𝒟, Λ)`, which is `Lf^*` followed by derived
completion (`MorphismOfTopoi.constantDerivedCompletePullback_comp_ι`). -/
@[stacks 099N "(2)"]
def constantDerivedCompletePullbackPushforwardAdjunction :
    constantDerivedCompletePullback Λ I f ⊣ constantDerivedCompletePushforward Λ I f :=
  RingedToposHom.derivedCompletePullbackAdjunctionOfPreserves (constantRingedToposHom Λ f) _ _ _

/-- **[Stacks, Tag 099N], part (3).** Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and
`f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi. `Rf_*` commutes with derived completion: the canonical
comparison `(Rf_*K)^∧ ⟶ Rf_*(K^∧)`, natural in `K` in `D(𝒟, Λ)`, is an isomorphism. -/
@[stacks 099N "(3)"]
theorem isIso_derivedCompletionComparison_constantDerivedPushforward :
    IsIso (RingedSite.derivedCompletionComparison (RingedSite.constantIdealSheaf K Λ I)
      (RingedSite.constantIdealSheaf J Λ I) (constantDerivedPushforward Λ f)
      (fun E hE => isDerivedComplete_constantDerivedPushforward Λ f I E hE)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (isIso_derivedCompletionComparisonApp_constantDerivedPushforward Λ f I)

/-- **[Stacks, Tag 099N], part (4).** Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and
`f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi. For `K` in `D_comp(𝒟, Λ)`,
`Rf_*K = R lim Rf_*(K ⊗^𝐋_Λ (Λ/Iⁿ)̲)`: `Rf_*K` is a derived limit of the tower
`n ↦ Rf_*(K ⊗^𝐋_Λ (Λ/Iⁿ)̲)`. -/
@[stacks 099N "(4)"]
theorem isDerivedLimit_constantAdicTower_constantDerivedPushforward
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)))
    (hE : RingedSite.IsDerivedComplete.{u, u, u, u} (RingedSite.constant K Λ)
      (RingedSite.constantIdealSheaf K Λ I) E) :
    IsDerivedLimit (RingedSite.constantAdicTower K Λ I E ⋙ constantDerivedPushforward Λ f)
      ((constantDerivedPushforward Λ f).obj E) :=
  isDerivedLimit_map_constantDerivedPushforward Λ f _ E
    ((RingedSite.isDerivedComplete_iff_isDerivedLimit_constantAdicTower K Λ I E).1 hE)

/-- **[Stacks, Tag 07A4] with the first variable fixed**: `Lf^*(M ⊗^𝐋 -) ≅ Lf^*M ⊗^𝐋 Lf^*(-)`,
naturally in the second variable. -/
def constantDerivedPullbackTensorIso
    (M : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant J Λ).O))) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (RingedTopos.constant J Λ).O).obj M ⋙ constantDerivedPullback Λ f ≅
      constantDerivedPullback Λ f ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (RingedTopos.constant K Λ).O).obj ((constantDerivedPullback Λ f).obj M) :=
  NatIso.ofComponents
    (fun P => (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (constantRingedToposHom Λ f)).app (M, P))
    (fun {P P'} φ => by
      simpa using (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
        (constantRingedToposHom Λ f)).hom.naturality ((𝟙 M, φ) : ((M, P) : _ × _) ⟶ (M, P')))

/-- **[Stacks, Tag 099N], part (5).** Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and
`f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi. For `M` in `D_comp(𝒞, Λ)`,
`Lf^*_comp M = R lim Lf^*(M ⊗^𝐋_Λ (Λ/Iⁿ)̲)`: `Lf^*_comp M` is a derived limit of the tower
`n ↦ Lf^*(M ⊗^𝐋_Λ (Λ/Iⁿ)̲)`. -/
@[stacks 099N "(5)"]
theorem isDerivedLimit_constantAdicTower_constantDerivedCompletePullback
    (M : ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u}
      (RingedTopos.constant J Λ).toRingedSite (RingedSite.constantIdealSheaf J Λ I))) :
    IsDerivedLimit (RingedSite.constantAdicTower J Λ I M.1 ⋙ constantDerivedPullback Λ f)
      ((constantDerivedCompletePullback Λ I f).obj M).1 := by
  let AC := Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor J Λ ⋙
    DerivedCategory.singleFunctor _ 0
  let AD := Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor K Λ ⋙
    DerivedCategory.singleFunctor _ 0
  let L := constantDerivedPullback Λ f
  let SC := (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedSite.constant J Λ)).obj M.1
  let OC := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (RingedTopos.constant J Λ).O).obj M.1
  let SD := (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedSite.constant K Λ)).obj
    (L.obj M.1)
  let OD := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (RingedTopos.constant K Λ).O).obj (L.obj M.1)
  obtain ⟨p⟩ := nonempty_proIso_constantAdicTower_derivedPullback Λ f I
  let e₁ : AC ⋙ SC ⋙ L ≅ AC ⋙ OC ⋙ L :=
    Functor.isoWhiskerLeft AC (Functor.isoWhiskerRight
      ((RingedSite.derivedTensorFunctorIso (RingedSite.constant J Λ)).app M.1) L)
  let e₂ : AC ⋙ OC ⋙ L ≅ (AC ⋙ L) ⋙ OD :=
    Functor.isoWhiskerLeft AC (constantDerivedPullbackTensorIso Λ f M.1) ≪≫
      (Functor.associator _ _ _).symm
  let e₃ : AD ⋙ OD ≅ AD ⋙ SD :=
    Functor.isoWhiskerLeft AD ((RingedSite.derivedTensorFunctorIso
      (RingedSite.constant K Λ)).app (L.obj M.1)).symm
  let q : InverseSequence.ProIso (AC ⋙ SC ⋙ L) (AD ⋙ SD) :=
    (((InverseSequence.ProIso.ofNatIso e₁).trans (InverseSequence.ProIso.ofNatIso e₂)).trans
      (p.whiskerRight OD)).trans (InverseSequence.ProIso.ofNatIso e₃)
  obtain ⟨N, hN⟩ := exists_isDerivedLimit (AC ⋙ SC ⋙ L)
  obtain ⟨e⟩ := Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ N _ hN
    (RingedSite.isDerivedLimit_constantAdicTower_derivedCompletion K Λ I (L.obj M.1)) q
  exact (RingedSite.isDerivedLimit_iff_of_iso e.symm).2 hN

end MorphismOfTopoi

end
