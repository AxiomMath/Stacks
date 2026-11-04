module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensorQCoh
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution

/-!
# The Fourier–Mukai transform of a Chow datum contains the closed immersion `U ⟶ V`

Let `p : T ⟶ X`, `q : T ⟶ P`, `iZ : Z ⟶ T`, `U ⊆ X` and `V ⊆ P` be a Chow datum as in
`AlgebraicGeometry.chowDatum_derivedPushforward_tensor_restrict_iso` ([Stacks, Tag 0CSK]):
`b = iZ ≫ p` is an isomorphism over `U`, `c = iZ ≫ q` is a closed immersion over `V` and
`b ⁻¹ᵁ U = c ⁻¹ᵁ V`. Write `j : q ⁻¹ᵁ V ⟶ T` for the open immersion, `W = iZ ⁻¹ᵁ (q ⁻¹ᵁ V)` and
`i = iZ ∣_ (q ⁻¹ᵁ V) : W ⟶ q ⁻¹ᵁ V`.

Suppose `E'` is an object of `D(𝒪_T)` such that `Ri_*𝒪_W` is a *retract* of `Lj^*E'`. Then for
every `K ∈ D_QCoh(𝒪_X)`

`R(c ∘ (b|_U)⁻¹)_*(K|_U)` is a retract of `Rq_*(Lp^*K ⊗^𝐋 E')|_V`.

## Main results

* `AlgebraicGeometry.CoherentConverse.chowDatumTailIso`:
  `Rq|_*(Ri_*(Li^*L)) ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)` for `L = Lj^*Lp^*K`.
* `AlgebraicGeometry.CoherentConverse.closedProjectionIso`: the projection formula
  `M ⊗^𝐋 Ri_*𝒪_W ≅ Ri_*(Li^*M)` for `i` quasi-compact and quasi-separated and `M ∈ D_QCoh`.
* `AlgebraicGeometry.CoherentConverse.nonempty_retract_chowDatum`: the retract.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.CoherentConverse

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow

/-- **The projection formula at a quasi-compact quasi-separated morphism, against the structure
sheaf.** For `i : W ⟶ Y` quasi-compact and quasi-separated and `M ∈ D_QCoh(𝒪_Y)`,
`M ⊗^𝐋 Ri_*𝒪_W ≅ Ri_*(Li^*M)`: [Stacks, Tag 08EU] at `E = 𝒪_W[0]`, preceded by the commutativity
constraint and followed by the left unit constraint of [Stacks, Tag 0FPT]. -/
def closedProjectionIso {W Y : Scheme.{u}} (i : W ⟶ Y) [QuasiCompact i] [QuasiSeparated i]
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hM : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) M) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj M).obj
        ((derivedPushforward (ofScheme i)).obj (structureSheafSingle W)) ≅
      (derivedPushforward (ofScheme i)).obj ((derivedPullback (ofScheme i)).obj M) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).braidingIso
      (RingedSpace.ringedSite Y.toRingedSpace) M _ ≪≫
    @asIso _ _ _ _ (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap (ofScheme i)
        (structureSheafSingle W) M)
      (Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh i _ M
        (Stacks.AlgebraicGeometry.AffinePullbackPushforwardTensor.isDQCoh_singleUnit W) hM) ≪≫
    (derivedPushforward (ofScheme i)).mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).leftUnitIso
        (RingedSpace.ringedSite W.toRingedSpace) _)

variable {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) (U : X.Opens) (V : P.Opens)
  (hb : IsIso ((iZ ≫ p) ∣_ U)) (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V)
  (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- With `i = iZ ∣_ (q ⁻¹ᵁ V)`, `j = (q ⁻¹ᵁ V).ι` and `L = Lj^*Lp^*K`, the isomorphism
`Rq|_*(Ri_*(Li^*L)) ≅ R(c ∘ (b|_U)⁻¹)_*(K|_U)` composed of the composition isomorphisms of
[Stacks, Tag 0D5S] and [Stacks, Tag 0D5T], the two factorization identities of the graph, and the
inverse of the derived adjunction unit along `b|_U`. -/
def chowDatumTailIso :
    (derivedPushforward (ofScheme (q ∣_ V))).obj
      ((derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
        ((derivedPullback (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
          ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj
            ((derivedPullback (ofScheme p)).obj K)))) ≅
      (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).obj
        ((derivedPullback (ofScheme U.ι)).obj K) :=
  haveI := isIso_chowDatumGraphIso p q iZ U V hb hW
  have hG1 : chowDatumGraphIso p q iZ U V hW ≫ chowDatumMorphism p q iZ U V hb hW =
      (iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V) :=
    chowDatumGraphIso_comp_chowDatumMorphism p q iZ U V hb hW
  have hG2 : chowDatumGraphIso p q iZ U V hW ≫ U.ι =
      (iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p :=
    chowDatumGraphIso_comp_ι p q iZ U V hW
  have hG1' : ofScheme (chowDatumGraphIso p q iZ U V hW) ≫
      ofScheme (chowDatumMorphism p q iZ U V hb hW) =
      ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V)) :=
    congrArg (fun m : (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ V.toScheme => ofScheme m) hG1
  have hG2' : ofScheme (chowDatumGraphIso p q iZ U V hW) ≫ ofScheme U.ι =
      ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p) :=
    congrArg (fun m : (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ X => ofScheme m) hG2
  have hfg : ofScheme (chowDatumGraphIso p q iZ U V hW) ≫
      ofScheme (inv (chowDatumGraphIso p q iZ U V hW)) =
      𝟙 (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme.toRingedSpace :=
    congrArg (fun m : (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme => ofScheme m)
      (IsIso.hom_inv_id (chowDatumGraphIso p q iZ U V hW))
  have hgf : ofScheme (inv (chowDatumGraphIso p q iZ U V hW)) ≫
      ofScheme (chowDatumGraphIso p q iZ U V hW) = 𝟙 U.toScheme.toRingedSpace :=
    congrArg (fun m : U.toScheme ⟶ U.toScheme => ofScheme m)
      (IsIso.inv_hom_id (chowDatumGraphIso p q iZ U V hW))
  (derivedPushforwardFactorIso (ofScheme (iZ ∣_ (q ⁻¹ᵁ V))) (ofScheme (q ∣_ V))
      (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V))) rfl).app _ ≪≫
    (derivedPushforward (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V)))).mapIso
      ((derivedPullback (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).mapIso
          ((derivedPullbackFactorIso (ofScheme (q ⁻¹ᵁ V).ι) (ofScheme p)
            (ofScheme ((q ⁻¹ᵁ V).ι ≫ p)) rfl).app K) ≪≫
        (derivedPullbackFactorIso (ofScheme (iZ ∣_ (q ⁻¹ᵁ V))) (ofScheme ((q ⁻¹ᵁ V).ι ≫ p))
          (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p)) rfl).app K ≪≫
        ((derivedPullbackFactorIso (ofScheme (chowDatumGraphIso p q iZ U V hW)) (ofScheme U.ι)
          (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ⁻¹ᵁ V).ι ≫ p)) hG2').app K).symm) ≪≫
    ((derivedPushforwardFactorIso (ofScheme (chowDatumGraphIso p q iZ U V hW))
      (ofScheme (chowDatumMorphism p q iZ U V hb hW))
      (ofScheme ((iZ ∣_ (q ⁻¹ᵁ V)) ≫ (q ∣_ V))) hG1').app
        ((derivedPullback (ofScheme (chowDatumGraphIso p q iZ U V hW))).obj
          ((derivedPullback (ofScheme U.ι)).obj K))).symm ≪≫
    (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).mapIso
      (derivedUnitIsoOfInverse (ofScheme (chowDatumGraphIso p q iZ U V hW))
        (ofScheme (inv (chowDatumGraphIso p q iZ U V hW))) hfg hgf
        ((derivedPullback (ofScheme U.ι)).obj K)).symm

/-- **The Fourier–Mukai transform of a Chow datum contains the closed immersion `U ⟶ V`.** If
`Ri_*𝒪_W` is a retract of `Lj^*E'`, then for `K ∈ D_QCoh(𝒪_X)` the complex
`R(c ∘ (b|_U)⁻¹)_*(K|_U)` is a retract of `Rq_*(Lp^*K ⊗^𝐋 E')|_V`. -/
theorem nonempty_retract_chowDatum [IsClosedImmersion iZ]
    (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing T.toRingedSpace)))
    (ρ : Retract ((derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
        (structureSheafSingle (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme))
      ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj E'))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) K) :
    Nonempty (Retract
      ((derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).obj
        ((derivedPullback (ofScheme U.ι)).obj K))
      ((derivedPullback (ofScheme V.ι)).obj ((derivedPushforward (ofScheme q)).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor T.sheaf).obj
          ((derivedPullback (ofScheme p)).obj K)).obj E')))) := by
  have : IsClosedImmersion (iZ ∣_ (q ⁻¹ᵁ V)) := IsZariskiLocalAtTarget.restrict ‹_› _
  let L := (derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj ((derivedPullback (ofScheme p)).obj K)
  have hL : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing (q ⁻¹ᵁ V).toScheme.toRingedSpace)
      L :=
    Stacks.Cohomology.ProjectionFormulaQCohLocalization.isDQCoh_derivedPullback _ _
      (Stacks.Cohomology.ProjectionFormulaQCohLocalization.isDQCoh_derivedPullback _ _ hK)
  let F := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (q ⁻¹ᵁ V).toScheme.sheaf).obj L ⋙ derivedPushforward (ofScheme (q ∣_ V))
  let e1 : F.obj ((derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
        (structureSheafSingle (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme)) ≅
      (derivedPushforward (ofScheme (chowDatumMorphism p q iZ U V hb hW))).obj
        ((derivedPullback (ofScheme U.ι)).obj K) :=
    (derivedPushforward (ofScheme (q ∣_ V))).mapIso
      (closedProjectionIso (iZ ∣_ (q ⁻¹ᵁ V)) L hL) ≪≫ chowDatumTailIso p q iZ U V hb hW K
  let e2 : (derivedPullback (ofScheme V.ι)).obj ((derivedPushforward (ofScheme q)).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor T.sheaf).obj
          ((derivedPullback (ofScheme p)).obj K)).obj E')) ≅
      F.obj ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj E') :=
    (derivedPushforwardRestrictOpenIso q V).app _ ≪≫
      (derivedPushforward (ofScheme (q ∣_ V))).mapIso
        ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
          (ofScheme (q ⁻¹ᵁ V).ι)).app ((derivedPullback (ofScheme p)).obj K, E'))
  exact ⟨(Retract.ofIso e1.symm).trans ((ρ.map F).trans (Retract.ofIso e2.symm))⟩

end AlgebraicGeometry.CoherentConverse

end
