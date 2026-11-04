module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace

/-!
# Pulling back `ρ^*y ≫ τ` along a base change of projective bundles

Let `b : P' ⟶ P` be a morphism over `m : Y' ⟶ Y` (`b ≫ ρ = ρ' ≫ m`) carrying a quotient
`τ : ρ^*F ⟶ L` to a quotient `τ' : ρ'^*F' ⟶ L'` along `F' ≅ m^*F` and `b^*L ≅ L'`, in the form of
Stacks 01O3 (`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec`). For `y : M ⟶ F` and
`y' : M' ⟶ F'` compatible along `M' ≅ m^*M`, and `f : T ⟶ P'`, the pullback along `f ≫ b` of
`ρ^*y ≫ τ` is the pullback along `f` of `ρ'^*y' ≫ τ'`, up to an isomorphism of sources and an
isomorphism of targets which does not depend on `y`. These are pure manipulations of the
comparisons of iterated pullbacks of modules on schemes.

## Main results

* `Stacks.RelativeProj.exists_pullback_comp_map_eq_of_baseChange`.
* `Stacks.RelativeProj.exists_pullback_map_comp_overQuotientMap_eq`: the same with the pulled-back
  quotient written as `TautologicalDatum.overQuotientMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {T P P' Y Y' : Scheme.{u}} (f : T ⟶ P') (b : P' ⟶ P) {ρ : P ⟶ Y} {ρ' : P' ⟶ Y'}
  {ms : Y' ⟶ Y} (hw : b ≫ ρ = ρ' ≫ ms) {F M : Y.Modules} {F' M' : Y'.Modules}
  (θF : F' ≅ (Scheme.Modules.pullback ms).obj F) (θM : M' ≅ (Scheme.Modules.pullback ms).obj M)
  {L : P.Modules} {L' : P'.Modules} (τ : (Scheme.Modules.pullback ρ).obj F ⟶ L)
  (τ' : (Scheme.Modules.pullback ρ').obj F' ⟶ L') (tw : (Scheme.Modules.pullback b).obj L ≅ L')
  (hspec : (Scheme.Modules.pullback b).map τ ≫ tw.hom =
    (Scheme.Modules.pullbackComp b ρ).hom.app F ≫ (Scheme.Modules.pullbackCongr hw).hom.app F ≫
      (Scheme.Modules.pullbackComp ρ' ms).inv.app F ≫ (Scheme.Modules.pullback ρ').map θF.inv ≫ τ')
  (y : M ⟶ F) (y' : M' ⟶ F') (hy : y' ≫ θF.hom = θM.hom ≫ (Scheme.Modules.pullback ms).map y)

include hspec hy in
/-- **The pullback along `f ≫ b` of `ρ^*y ≫ τ` is the pullback along `f` of `ρ'^*y' ≫ τ'`**, up to
an isomorphism of sources and the isomorphism of targets `f^*L' ≅ f^*b^*L ≅ (f ≫ b)^*L`. -/
theorem exists_pullback_comp_map_eq_of_baseChange :
    ∃ Src : (Scheme.Modules.pullback (f ≫ b)).obj ((Scheme.Modules.pullback ρ).obj M) ≅
        (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback ρ').obj M'),
      (Scheme.Modules.pullback (f ≫ b)).map ((Scheme.Modules.pullback ρ).map y ≫ τ) =
        Src.hom ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ').map y' ≫ τ') ≫
          ((Scheme.Modules.pullback f).mapIso tw.symm ≪≫
            (Scheme.Modules.pullbackComp f b).app L).hom := by
  -- the composite comparison `b^*ρ^* ≅ ρ'^*m^*`
  let Ψ : ∀ N : Y.Modules, (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback ρ).obj N) ≅
      (Scheme.Modules.pullback ρ').obj ((Scheme.Modules.pullback ms).obj N) := fun N =>
    (Scheme.Modules.pullbackComp b ρ).app N ≪≫ (Scheme.Modules.pullbackCongr hw).app N ≪≫
      ((Scheme.Modules.pullbackComp ρ' ms).app N).symm
  have hΨ : ∀ {N N' : Y.Modules} (z : N ⟶ N'),
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback ρ).map z) ≫ (Ψ N').hom =
        (Ψ N).hom ≫ (Scheme.Modules.pullback ρ').map ((Scheme.Modules.pullback ms).map z) := by
    intro N N' z
    have n₁ := (Scheme.Modules.pullbackComp b ρ).hom.naturality z
    have n₂ := (Scheme.Modules.pullbackCongr hw).hom.naturality z
    have n₃ := (Scheme.Modules.pullbackComp ρ' ms).inv.naturality z
    simp only [Functor.comp_map] at n₁ n₂ n₃
    simp only [Ψ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
    rw [reassoc_of% n₁, reassoc_of% n₂, n₃]
    simp only [Category.assoc]
  have hb : (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback ρ).map y ≫ τ) =
      (Ψ M).hom ≫ (Scheme.Modules.pullback ρ').map θM.inv ≫
        ((Scheme.Modules.pullback ρ').map y' ≫ τ') ≫ tw.inv := by
    have hy' : (Scheme.Modules.pullback ms).map y ≫ θF.inv = θM.inv ≫ y' := by
      rw [Iso.comp_inv_eq, Category.assoc, hy, Iso.inv_hom_id_assoc]
    have hτ := (Iso.eq_comp_inv tw).2 hspec
    have h1 := hΨ y
    simp only [Ψ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] at h1 ⊢
    rw [Functor.map_comp, hτ]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← Functor.map_comp_assoc (Scheme.Modules.pullback ρ'), hy',
      Functor.map_comp_assoc]
  refine ⟨((Scheme.Modules.pullbackComp f b).app _).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (Ψ M ≪≫ (Scheme.Modules.pullback ρ').mapIso θM.symm), ?_⟩
  have nat' := (NatIso.naturality_1 (Scheme.Modules.pullbackComp f b)
    ((Scheme.Modules.pullback ρ).map y ≫ τ)).symm
  rw [nat', Functor.comp_map, hb]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Iso.symm_hom]

/-- **The pulled-back quotient of a morphism `f` into `𝐏(F)`, composed with `g^*y`, is the pullback
along `f` of `π^*y ≫ τ`**, up to the comparison `g^*M ≅ f^*π^*M`. -/
theorem pullback_map_comp_overQuotientMap_eq {Z T : Scheme.{u}} {F M : Z.Modules}
    [F.IsQuasicoherent] (D : TautologicalDatum Z F) (y : M ⟶ F) (f : T ⟶ projectiveBundle Z F)
    {g : T ⟶ Z} (hg : f ≫ projectiveBundleToBase Z F = g) :
    (Scheme.Modules.pullback g).map y ≫ D.overQuotientMap f hg =
      ((Scheme.Modules.pullbackCongr hg).symm.app M ≪≫
        ((Scheme.Modules.pullbackComp f (projectiveBundleToBase Z F)).app M).symm).hom ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback (projectiveBundleToBase Z F)).map y ≫ D.univ) := by
  have n₁ := (Scheme.Modules.pullbackCongr hg).inv.naturality y
  have n₂ := (Scheme.Modules.pullbackComp f (projectiveBundleToBase Z F)).inv.naturality y
  simp only [Functor.comp_map] at n₁ n₂
  rw [TautologicalDatum.overQuotientMap, reassoc_of% n₁, reassoc_of% n₂, Functor.map_comp]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]

end Stacks.RelativeProj

end
