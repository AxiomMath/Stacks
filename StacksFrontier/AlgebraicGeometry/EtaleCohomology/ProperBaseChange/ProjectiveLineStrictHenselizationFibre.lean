module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineGeometricFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationBaseChangeReduction

/-!
# The base change of `ℙ¹` to a strict henselization and the geometric fibre

Let `X' ⟶ T` be a base change of `ℙ¹_S ⟶ S` along `g : T ⟶ S`, let `t` be a geometric point of
`T`, and let `X'^{sh} = X' ×_T Spec(𝒪^{sh}_{T,t})`. For an abelian sheaf `G` on `ℙ¹_S` killed by
a prime `ℓ`, the cohomology of `G` restricted to `X'^{sh}` vanishes in degree `q` exactly when the
cohomology of `G` restricted to the geometric fibre `ℙ¹_S ×_S Spec Ω` at the geometric point
`g ∘ t` of `S` does, granted [Stacks, Tag 0A5H] and [Stacks, Tag 0A5E].

The scheme `X'^{sh}` is `ℙ¹` over the strictly henselian local ring `𝒪^{sh}_{T,t}`, so the second
paragraph of the proof of [Stacks, Tag 095T]
(`Stacks.EtaleCohomology.subsingleton_H_projectiveLine_iff_geometricFibre`) applies, and the
scalar extension of its closed fibre to `Ω` is, by pasting cartesian squares, the geometric fibre
of `ℙ¹_S` at `g ∘ t`. Only isomorphisms of schemes over `ℙ¹_S` intervene.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_strictHenselization_iff_geometricFibre`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] structureSheafStalkToGeometricField_isLocalHom
attribute [local instance] strictHenselizationResidueAlgebra

variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

variable {S T X' : Scheme.{u}} (g : T ⟶ S) (g' : X' ⟶ ProjectiveSpace 1 S) (f' : X' ⟶ T)
  (sq : IsPullback g' f' (ProjectiveSpace 1 S ↘ S) g) (B : BigEtaleSite.{u}) (hT : B.Contains T)
  (t : GeometricPoint T)

/-- The projective line over the strict henselization, mapped to `ℙ¹_S`. -/
abbrev projectiveLineStrictHenselizationToBase :
    ProjectiveSpace 1 (strictHenselization B T hT t) ⟶ ProjectiveSpace 1 S :=
  (ProjectiveSpace.baseChangeIso 1 (strictHenselizationToBase B T hT t ≫ g)).inv ≫
    pullback.fst _ _

omit [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- `ℙ¹` over the strict henselization is the base change of `ℙ¹_S`. -/
theorem isPullback_projectiveLineStrictHenselizationToBase :
    IsPullback (projectiveLineStrictHenselizationToBase g B hT t)
      (ProjectiveSpace 1 (strictHenselization B T hT t) ↘ strictHenselization B T hT t)
      (ProjectiveSpace 1 S ↘ S) (strictHenselizationToBase B T hT t ≫ g) := by
  set e := ProjectiveSpace.baseChangeIso 1 (strictHenselizationToBase B T hT t ≫ g)
  have w₂ : e.inv ≫ pullback.snd _ _ =
      ProjectiveSpace 1 (strictHenselization B T hT t) ↘ strictHenselization B T hT t := by
    rw [← ProjectiveSpace.baseChangeIso_hom_over, Iso.inv_hom_id_assoc]
  refine IsPullback.of_iso_pullback ⟨?_⟩ e.symm rfl w₂
  show (e.inv ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, w₂]

include sq in
/-- **The base change of `ℙ¹_S` to the strict henselization of `T` at `t` versus the geometric
fibre of `ℙ¹_S` at `g ∘ t`.** For an abelian sheaf `G` on `ℙ¹_S` killed by a prime `ℓ`, the
cohomology in degree `q` of `G` restricted to `X' ×_T Spec(𝒪^{sh}_{T,t})` vanishes exactly when
the cohomology of `G` restricted to `ℙ¹_S ×_S Spec Ω` does, granted [Stacks, Tag 0A5H] (`h0A5H`)
and [Stacks, Tag 0A5E] (`h0A5E`) in the forms of their developments. -/
theorem subsingleton_H_strictHenselization_iff_geometricFibre {ℓ : ℕ}
    (h0A5H : ∀ (A : Type u) [CommRing A] [HenselianLocalRing A]
      (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
        (ProjectiveSpace 1 (Spec (.of A))).smallEtaleTopology ℓ)), Injective J →
      ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (closedFibreInclusion A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)))).obj
          ((SheafOfModules.toSheaf _).obj J)) q))
    (h0A5E : ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k]
      [IsSepClosed k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      (_ : topologicalKrullDim X ≤ 1) (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (_ : Stacks.Torsion.torsionSheafProperty.{u + 1} (smallEtaleTopology X) F) (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' f) F q))
    (hℓ : ℓ.Prime) (G : Sheaf (ProjectiveSpace 1 S).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : (ℓ : ℤ) • 𝟙 G = 0) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (strictHenselizationBaseChangeToSource B hT f' t ≫ g')).obj G) q) ↔
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (pullback.fst (ProjectiveSpace 1 S ↘ S) (t.hom ≫ g))).obj G) q) := by
  have := etaleLocalRing_strictHenselian B T hT t
  set O := ↥(etaleLocalRing B T hT t)
  set c := projectiveLineStrictHenselizationToBase g B hT t
  have s₃ := isPullback_projectiveLineStrictHenselizationToBase g B hT t
  -- `X'^{sh}` is `ℙ¹` over the strict henselization
  have sa : IsPullback (strictHenselizationBaseChangeToSource B hT f' t ≫ g')
      (strictHenselizationBaseChangeToStrictHenselization B hT f' t)
      (ProjectiveSpace 1 S ↘ S) (strictHenselizationToBase B T hT t ≫ g) :=
    (IsPullback.of_hasPullback f' (strictHenselizationToBase B T hT t)).paste_horiz sq
  have h₁ := subsingleton_H_inverseImage_iff_of_isIso G q _ c (sa.isoIsPullback _ _ s₃).hom
    (sa.isoIsPullback_hom_fst _ _ s₃).symm
  -- the geometric fibre comparison over the strictly henselian local ring
  have hG' : (ℓ : ℤ) • 𝟙 ((etaleAbelianInverseImage.{u, 0} c).obj G) = 0 :=
    zsmul_id_inverseImage_eq_zero c (ℓ : ℤ) hG
  have h₂ := subsingleton_H_projectiveLine_iff_geometricFibre O t.residueField
    (h0A5H O) (fun f _ hdim F hF q ↦ h0A5E (IsLocalRing.ResidueField O) t.residueField f hdim F
      hF q) hℓ c G hG' q
  -- the scalar extension of the closed fibre is the geometric fibre at `g ∘ t`
  set π := ProjectiveSpace 1 (Spec (.of O)) ↘ Spec (.of O)
  have s₁ := IsPullback.of_hasPullback (closedFibreProjection O π)
    (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField O) t.residueField)))
  have s₂ := isPullback_closedFibre O π
  have hbot : (Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField O) t.residueField)) ≫ residueFieldPoint O) ≫
      (strictHenselizationToBase B T hT t ≫ g) = t.hom ≫ g := by
    rw [← geometricPointToStrictHenselization_eq, ← Category.assoc,
      geometricPointToStrictHenselization_comp]
  have sb : IsPullback ((pullback.fst (closedFibreProjection O π)
        (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField O) t.residueField))) ≫
          closedFibreInclusion O π) ≫ c)
      (pullback.snd (closedFibreProjection O π)
        (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField O) t.residueField))))
      (ProjectiveSpace 1 S ↘ S) (t.hom ≫ g) := by
    convert (s₁.paste_horiz s₂).paste_horiz s₃ using 1
    exact hbot.symm
  have h₃ := subsingleton_H_inverseImage_iff_of_isIso G q _ _
    (sb.isoIsPullback _ _ (IsPullback.of_hasPullback (ProjectiveSpace 1 S ↘ S) (t.hom ≫ g))).hom
    (by rw [IsPullback.isoIsPullback_hom_fst, Category.assoc])
  exact h₁.trans (h₂.trans h₃)

end Stacks.EtaleCohomology

end
