module

public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3
public import StacksFrontier.AlgebraicGeometry.Descent.NonvanishingSectionNearFibre
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreSectionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing

/-!
# Triviality near a fibre: the trivial-faces case of Tag 0BF2

Let `p : P ⟶ S` and the `i k ≫ p : X k ⟶ S` (`k` in a finite type) be flat, proper and of finite
presentation with `𝒪_T ≅ p_{T,*}𝒪` after every base change, let `ℒ` be invertible on `P` with
every `(i k)^*ℒ` trivial, and let `s ∈ S` be a point over whose fibre `P_s` the module `ℒ` is
trivial and for which `H¹(P_s, 𝒪) ⟶ ⊕_k H¹(X_{k,s}, 𝒪)` is injective. Then `ℒ` is trivial over
`P ×_S U` for an open neighbourhood `U` of `s`. This is
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2) in the case where every `ℒ_i` is
trivial (so that the intersection of the loci `Z_i` is all of `S`).

The proof is the source's. Shrink `S` to an affine open neighbourhood `j : Spec R ⟶ S` of `s`.
The cohomological half (`exists_unit_hom_modulePullback_ne_zero_of_injective_H1`, in the namespace
`AlgebraicGeometry.MinimalComplexFunctoriality`) produces `σ : 𝒪_{P_R} ⟶ ℒ|_{P_R}` whose pullback
to `P_s` is nonzero. As `ℒ|_{P_s}` is trivial and `Γ(P_s, 𝒪) = κ(s)` is a field, that pullback is
a nowhere vanishing section of the fibre, so `σ` vanishes at no point of `P_R` over `s`
([Stacks, Tag 0H78]), and the topological argument
(`AlgebraicGeometry.SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus`)
trivializes `ℒ` over `P_R ×_R U'` for an open `U' ∋ s`, that is over `P ×_S j(U')`.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_injective_H1`: the
  statement above.
* `exists_isTrivial_modulePullback_fst_ι_of_injective_H1_of_isPullback` (same namespace):
  the same at a point with values in an arbitrary field, with the fibres given by pullback
  squares; this is the form used by the general case of Tag 0BF2, after a base change.
* `AlgebraicGeometry.SheafOfModules.mem_nonvanishingLocus_of_modulePullback_map_ne_zero`: a
  morphism `𝒪_P ⟶ ℒ` with nonzero pullback to a scheme `F` on which `ℒ` is trivial and whose ring
  of functions is a field vanishes at no point of the image of `F`.
* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_fst_ι_image`: a trivialization over
  `P_W ×_W U'` for an open immersion `j : W ⟶ S` and an open `U' ⊆ W` is one over `P ×_S j(U')`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.GlobalKunneth (sectionsOverBase baseRing sectionsPullbackMap)
open AlgebraicGeometry.ProperFlatBaseChange

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Triviality over an open of an open neighbourhood is triviality over its image.** For an open
immersion `j : W ⟶ S`, an open `U' ⊆ W` and a module `L` on `P` over `p : P ⟶ S`, if the pullback
of `L` to `P_W = P ×_S W` is trivial over `P_W ×_W U'`, then `L` is trivial over `P ×_S j(U')`. -/
theorem isTrivial_modulePullback_fst_ι_image {S P W : Scheme.{u}} (p : P ⟶ S) (j : W ⟶ S)
    [IsOpenImmersion j] (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (U' : W.Opens)
    (h : IsTrivial (pullback (pullback.snd p j) U'.ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.snd p j) U'.ι).IsSheaf)
      ((modulePullback (pullback.fst (pullback.snd p j) U'.ι).toLRSHom.toShHom).obj
        ((modulePullback (pullback.fst p j).toLRSHom.toShHom).obj L))) :
    IsTrivial (pullback p (j ''ᵁ U').ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p (j ''ᵁ U').ι).IsSheaf)
      ((modulePullback (pullback.fst p (j ''ᵁ U').ι).toLRSHom.toShHom).obj L) := by
  let U := j ''ᵁ U'
  have hr : Set.range U.ι ⊆ Set.range (U'.ι ≫ j) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    rfl
  let g : U.toScheme ⟶ U'.toScheme := IsOpenImmersion.lift (U'.ι ≫ j) U.ι hr
  have hg : g ≫ U'.ι ≫ j = U.ι := IsOpenImmersion.lift_fac _ _ _
  let a₁ : pullback p U.ι ⟶ pullback p j :=
    pullback.lift (pullback.fst p U.ι) (pullback.snd p U.ι ≫ g ≫ U'.ι) (by
      rw [pullback.condition]
      simp only [Category.assoc, hg])
  let a : pullback p U.ι ⟶ pullback (pullback.snd p j) U'.ι :=
    pullback.lift a₁ (pullback.snd p U.ι ≫ g) (by rw [pullback.lift_snd, Category.assoc])
  have hcomp : a ≫ pullback.fst (pullback.snd p j) U'.ι ≫ pullback.fst p j =
      pullback.fst p U.ι := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have h' : Nonempty ((modulePullback ((pullback.fst (pullback.snd p j) U'.ι).toLRSHom.toShHom ≫
      (pullback.fst p j).toLRSHom.toShHom)).obj L ≅
        _root_.SheafOfModules.unit (structureSheafRing
          (pullback (pullback.snd p j) U'.ι).toRingedSpace)) :=
    ⟨(RingedSpaceModuleAdjunction.modulePullbackComp _ _).app L ≪≫ h.some⟩
  have hc : a.toLRSHom.toShHom ≫ ((pullback.fst (pullback.snd p j) U'.ι).toLRSHom.toShHom ≫
      (pullback.fst p j).toLRSHom.toShHom) = (pullback.fst p U.ι).toLRSHom.toShHom := by
    rw [← hcomp]
    rfl
  exact isTrivial_modulePullback_of_comp _ _ _ hc h'

/-! ### Nowhere vanishing sections of a trivial fibre -/

section Nonvanishing

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- The global section of `φ : 𝒪_X ⟶ M` is the image under `φ` of the unit section over `⊤`. -/
private theorem unitHomEquiv_eval_top {X : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (φ : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M) :
    (M.unitHomEquiv φ).eval (op ⊤) =
      (φ.val.app (op ⊤)).hom (Stacks.SheafOfModules.unitSection X ⊤) := by
  have := Stacks.SheafOfModules.unitHomEquiv_symm_app_unitSection M (M.unitHomEquiv φ) ⊤
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- **A section trivialized onto a unit vanishes nowhere.** If `e : M ≅ 𝒪_X` and the image under
`e` of the global section of `φ : 𝒪_X ⟶ M` is a unit of `Γ(X, 𝒪_X)`, then that section lies outside
`𝔪_x M_x` at every point `x`. -/
theorem mem_nonvanishingLocus_of_isUnit {X : RingedSpace.{u, u}}
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    {M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (e : M ≅ _root_.SheafOfModules.unit (structureSheafRing X))
    (φ : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M)
    (hu : IsUnit (show X.presheaf.obj (op ⊤) from (e.hom.val.app (op ⊤)).hom ((φ.val.app (op ⊤)).hom
      (Stacks.SheafOfModules.unitSection X ⊤)))) (x : X.carrier) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus M (M.unitHomEquiv φ) := by
  show grpGerm X M.val x ⊤ (Opens.mem_top x) ((M.unitHomEquiv φ).eval (op ⊤)) ∉ _
  rw [unitHomEquiv_eval_top, Stacks.SheafOfModules.mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.SheafOfModules.stalkLinearEquiv X e x),
    Stacks.SheafOfModules.stalkLinearEquiv_germ,
    Stacks.SheafOfModules.mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.SheafOfModules.unitStalkLinearEquiv X x).symm,
    Stacks.SheafOfModules.unitStalkLinearEquiv_symm_grpGerm]
  intro hm
  have hm' : ringGerm X x ⊤ (Opens.mem_top x) (show X.presheaf.obj (op ⊤) from
      (e.hom.val.app (op ⊤)).hom ((φ.val.app (op ⊤)).hom (Stacks.SheafOfModules.unitSection X ⊤))) ∈
        IsLocalRing.maximalIdeal (ringStalk X x) :=
    Submodule.smul_le.2 (fun a ha b _ => Ideal.mul_mem_right b _ ha) hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm' (hu.map (ringGerm X x ⊤ (Opens.mem_top x)))

/-- A morphism `𝒪_X ⟶ M` that kills the unit section over `X` is zero: a morphism out of `𝒪_X`
is determined by its global section. -/
theorem eq_zero_of_app_top_unitSection_eq_zero {X : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (φ : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M)
    (h : (φ.val.app (op ⊤)).hom (Stacks.SheafOfModules.unitSection X ⊤) = 0) : φ = 0 := by
  rw [← M.unitHomEquiv.symm_apply_apply φ]
  have hs : M.unitHomEquiv φ = 0 := by
    apply Subtype.ext
    funext U
    have hU := (M.unitHomEquiv φ).property (homOfLE (le_top : U.unop ≤ ⊤)).op
    have htop : (M.unitHomEquiv φ).eval (op ⊤) = 0 := (unitHomEquiv_eval_top φ).trans h
    show (M.unitHomEquiv φ).val U = 0
    rw [← hU]
    show (M.val.map _).hom ((M.unitHomEquiv φ).eval (op ⊤)) = 0
    rw [htop, map_zero]
  rw [hs]
  apply M.unitHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  rw [_root_.SheafOfModules.unitHomEquiv_apply_coe]
  rfl

/-- **The pulled-back section of a morphism `𝒪_X ⟶ ℒ`.** The pullback along `f` of the global
section of `σ : 𝒪_X ⟶ ℒ` takes over `⊤` the value at the unit section of `f^*σ`, read through
`f^*𝒪_X ≅ 𝒪_Y`. -/
theorem modulePullbackSection_eval_top_unitHomEquiv {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (σ : _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace) ⟶ L) :
    (Stacks.SheafOfModules.modulePullbackSection f L (L.unitHomEquiv σ)).eval (op ⊤) =
      (((Stacks.PullbackAlgebra.pullbackUnitIso f.toShHom).inv ≫
        (modulePullback f.toShHom).map σ).val.app (op ⊤)).hom
          (Stacks.SheafOfModules.unitSection Y.toRingedSpace ⊤) := by
  refine (Stacks.SheafOfModules.modulePullbackSection_eval_top f L (L.unitHomEquiv σ)).trans ?_
  have h := Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f.toShHom (op ⊤)
    (Stacks.SheafOfModules.unitSection X.toRingedSpace ⊤)
  have h2 : Stacks.RingedSpace.pullbackUnit f.toShHom _ (op ⊤)
      (Stacks.SheafOfModules.unitSection X.toRingedSpace ⊤) =
      ((Stacks.PullbackAlgebra.pullbackUnitIso f.toShHom).inv.val.app (op ⊤)).hom
        (Stacks.SheafOfModules.unitSection Y.toRingedSpace ⊤) := by
    calc _ = (((Stacks.PullbackAlgebra.pullbackUnitIso f.toShHom).hom ≫
            (Stacks.PullbackAlgebra.pullbackUnitIso f.toShHom).inv).val.app (op ⊤)).hom
          (Stacks.RingedSpace.pullbackUnit f.toShHom _ (op ⊤)
            (Stacks.SheafOfModules.unitSection X.toRingedSpace ⊤)) := by
          rw [Iso.hom_inv_id]
          rfl
      _ = ((Stacks.PullbackAlgebra.pullbackUnitIso f.toShHom).inv.val.app (op ⊤)).hom
          (Stacks.RingedSpace.sharp f.toShHom (op ⊤)
            (Stacks.SheafOfModules.unitSection X.toRingedSpace ⊤)) := by
          rw [← h]
          rfl
      _ = _ := by
          congr 1
          exact Stacks.PullbackTensorCoherence.sharp_one f.toShHom (op ⊤)
  refine (Stacks.RingedSpace.pullbackUnit_naturality f.toShHom σ (op ⊤)
    (Stacks.SheafOfModules.unitSection X.toRingedSpace ⊤)).symm.trans ?_
  rw [h2]
  rfl

/-- **A morphism with nonzero pullback to a trivial fibre vanishes nowhere on that fibre.** Let
`tF : F ⟶ P` with `𝒪_{Spec K} ⟶ ps_*𝒪_F` an isomorphism for some `ps : F ⟶ Spec K` and a field
`K` (so that `Γ(F, 𝒪_F)` is a field), and let `tF^*ℒ` be trivial. If `σ : 𝒪_P ⟶ ℒ` has nonzero
pullback to `F`, then its global section is nonvanishing at every point of the image of `tF`: the
pulled-back section corresponds, through `tF^*ℒ ≅ 𝒪_F`, to a nonzero, hence invertible, element of
`Γ(F, 𝒪_F)`, and nonvanishing pulls back ([Stacks, Tag 0H78]). -/
theorem mem_nonvanishingLocus_of_modulePullback_map_ne_zero {K : Type u} [Field K]
    {P F : Scheme.{u}} (tF : F ⟶ P)
    (ps : F ⟶ Spec (CommRingCat.of K)) (hFO : IsIso (structureSheafHom ps.toLRSHom.toShHom))
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hFtriv : IsTrivial F.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) F.IsSheaf)
      ((modulePullback tF.toLRSHom.toShHom).obj L))
    (σ : _root_.SheafOfModules.unit (structureSheafRing P.toRingedSpace) ⟶ L)
    (hσ : (modulePullback tF.toLRSHom.toShHom).map σ ≠ 0) (z : F) :
    tF.base z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := P.toRingedSpace) L
      (L.unitHomEquiv σ) := by
  have _ : ∀ x : P.toRingedSpace.carrier, IsLocalRing (ringStalk P.toRingedSpace x) :=
    P.isLocalRing
  have _ : ∀ x : F.toRingedSpace.carrier, IsLocalRing (ringStalk F.toRingedSpace x) :=
    F.isLocalRing
  suffices hz : z ∈ tF.toLRSHom.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
      (X := P.toRingedSpace) L (L.unitHomEquiv σ) from hz
  rw [Stacks.SheafOfModules.preimage_nonvanishingLocus tF.toLRSHom L (L.unitHomEquiv σ)]
  let M := (modulePullback tF.toLRSHom.toShHom).obj L
  let φ : _root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace) ⟶ M :=
    (Stacks.PullbackAlgebra.pullbackUnitIso tF.toLRSHom.toShHom).inv ≫
      (modulePullback tF.toLRSHom.toShHom).map σ
  have heq : Stacks.SheafOfModules.nonvanishingLocus (X := F.toRingedSpace) M
      (Stacks.SheafOfModules.modulePullbackSection tF.toLRSHom L (L.unitHomEquiv σ)) =
      Stacks.SheafOfModules.nonvanishingLocus (X := F.toRingedSpace) M (M.unitHomEquiv φ) := by
    unfold Stacks.SheafOfModules.nonvanishingLocus
    rw [modulePullbackSection_eval_top_unitHomEquiv]
    rfl
  rw [heq]
  let e : M ≅ _root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace) := hFtriv.some
  refine mem_nonvanishingLocus_of_isUnit e φ ?_ z
  have hne : φ ≫ e.hom ≠ 0 := fun h =>
    hσ (MinimalComplexFunctoriality.eq_zero_of_inv_comp_comp_hom_eq_zero
      (Stacks.PullbackAlgebra.pullbackUnitIso tF.toLRSHom.toShHom) _ e h)
  have hg0 : (show F.presheaf.obj (op ⊤) from (e.hom.val.app (op ⊤)).hom ((φ.val.app (op ⊤)).hom
      (Stacks.SheafOfModules.unitSection F.toRingedSpace ⊤))) ≠ 0 := fun h =>
    hne (eq_zero_of_app_top_unitSection_eq_zero (φ ≫ e.hom) h)
  have hb := (@MinimalComplexFunctoriality.bijective_structureSheafHom_app _ _ ps.toLRSHom.toShHom
    hFO (op ⊤)).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  obtain ⟨k, hk⟩ := hb.2 (show F.presheaf.obj (op ⊤) from (e.hom.val.app (op ⊤)).hom
    ((φ.val.app (op ⊤)).hom (Stacks.SheafOfModules.unitSection F.toRingedSpace ⊤)))
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hg0
    rw [← hk, Function.comp_apply, map_zero, map_zero]
    rfl
  have hu := (Ne.isUnit hk0).map
    (((structureSheafHom ps.toLRSHom.toShHom).hom.app (op ⊤)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  rw [RingHom.comp_apply] at hu
  exact hk ▸ hu

end Nonvanishing

/-! ### The trivial-faces case of Tag 0BF2 -/

/-- The pullback of a trivial pullback along `a ≫ b = c` is trivial when taken in two steps. -/
private theorem isTrivial_modulePullback_modulePullback_of_comp {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) (c : A ⟶ C) (hc : a ≫ b = c)
    {M : _root_.SheafOfModules.{u} (structureSheafRing C.toRingedSpace)}
    (hM : IsTrivial A.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) A.IsSheaf)
      ((modulePullback c.toLRSHom.toShHom).obj M)) :
    IsTrivial A.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) A.IsSheaf)
      ((modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M)) := by
  subst hc
  exact ⟨((modulePullbackComp a.toLRSHom.toShHom b.toLRSHom.toShHom).app M).symm ≪≫ hM.some⟩

/-- A pullback square over `t = t₀ ≫ j` is a pullback square over `t₀` of the base change of its
right side along `j`. -/
private theorem isPullback_pullbackLift_of_comp_eq {A B C D W : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {f : B ⟶ D} {t : C ⟶ D} (h : IsPullback a b f t) (j : W ⟶ D) {t₀ : C ⟶ W}
    (ht : t₀ ≫ j = t) :
    IsPullback (pullback.lift a (b ≫ t₀) (by rw [h.w, Category.assoc, ht])) b
      (pullback.snd f j) t₀ := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
  rw [pullback.lift_fst, ht]
  exact h

/-- The base change of `i` along `j` followed by the projection to `W` is the projection. -/
private theorem pullback_map_comp_snd {X P S W : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S) (j : W ⟶ S) :
    pullback.map (i ≫ p) j p j i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd p j =
      pullback.snd (i ≫ p) j := by
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

/-- The base change of `i` along `j` followed by the projection to `P` is `i` after the
projection. -/
private theorem pullback_map_comp_fst {X P S W : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S) (j : W ⟶ S) :
    pullback.map (i ≫ p) j p j i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst p j =
      pullback.fst (i ≫ p) j ≫ i := by
  simp only [pullback.map, pullback.lift_fst]

/-- A face `tX` of a fibre square over `t = t₀ ≫ j` base-changes to a face of the fibre square over
`t₀` of the base change of `p` along `j`. -/
private theorem exists_isPullback_pullbackMap_of_isPullback {X P S F FX W C : Scheme.{u}}
    {i : X ⟶ P} {p : P ⟶ S} {t : C ⟶ S} {tX : FX ⟶ X} {isk : FX ⟶ F} {ps : F ⟶ C} {tF : F ⟶ P}
    (hX : IsPullback tX (isk ≫ ps) (i ≫ p) t) (hXF : tX ≫ i = isk ≫ tF) (j : W ⟶ S)
    {t₀ : C ⟶ W} (ht : t₀ ≫ j = t) (hF : tF ≫ p = ps ≫ t) :
    ∃ tX' : FX ⟶ pullback (i ≫ p) j,
      IsPullback tX' (isk ≫ ps)
        (pullback.map (i ≫ p) j p j i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd p j) t₀ ∧
      tX' ≫ pullback.map (i ≫ p) j p j i (𝟙 _) (𝟙 _) (by simp) (by simp) =
        isk ≫ pullback.lift tF (ps ≫ t₀) (by rw [hF, Category.assoc, ht]) := by
  refine ⟨pullback.lift tX ((isk ≫ ps) ≫ t₀) (by simp only [hX.w, Category.assoc, ht]), ?_, ?_⟩
  · rw [pullback_map_comp_snd]
    exact isPullback_pullbackLift_of_comp_eq hX j ht
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hXF
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]

/-- For a fibre `F` of `p` over a field-valued point `t` factored through `P ×_S W`, every point
of `P ×_S W` over a point `w` of `W` lying under the image of `t` comes from `F`. -/
private theorem exists_eq_of_isPullback_of_snd_eq {K : Type u} [Field K] {S P F W : Scheme.{u}}
    {p : P ⟶ S} {t : Spec (CommRingCat.of K) ⟶ S} {tF : F ⟶ P} {ps : F ⟶ Spec (CommRingCat.of K)}
    (hF : IsPullback tF ps p t) (j : W ⟶ S) [IsOpenImmersion j] {tF' : F ⟶ pullback p j}
    (htF' : tF' ≫ pullback.fst p j = tF) {w : W} (hw : j w = t (IsLocalRing.closedPoint K))
    {x : ↥(pullback p j)} (hx : pullback.snd p j x = w) : ∃ z, tF' z = x := by
  have hpx : p (pullback.fst p j x) = t (IsLocalRing.closedPoint K) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hx, hw]
  obtain ⟨z₀, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpx
  refine ⟨hF.isoPullback.inv z₀, (pullback.fst p j).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, htF', ← hz, ← Scheme.Hom.comp_apply,
    IsPullback.isoPullback_inv_fst]

/-- A morphism `𝒪 ⟶ ℒ|_{P ×_S W}`, for an open immersion `j : W ⟶ S`, with nonzero pullback to a
trivial fibre of `p` over a field-valued point `t` trivializes `ℒ` over `P ×_S U` for an open `U`
containing the image of `t`. -/
private theorem exists_isTrivial_modulePullback_fst_ι_of_modulePullback_map_ne_zero {K : Type u}
    [Field K] {S P F W : Scheme.{u}} (p : P ⟶ S) [IsProper p] {t : Spec (CommRingCat.of K) ⟶ S}
    {tF : F ⟶ P} (ps : F ⟶ Spec (CommRingCat.of K)) (hF : IsPullback tF ps p t)
    (hFO : IsIso (structureSheafHom ps.toLRSHom.toShHom)) (j : W ⟶ S) [IsOpenImmersion j]
    {w : W} (hw : j w = t (IsLocalRing.closedPoint K))
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    [IsInvertible (pullback p j).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback p j).IsSheaf)
      ((modulePullback (pullback.fst p j).toLRSHom.toShHom).obj L)]
    (tF' : F ⟶ pullback p j) (htF' : tF' ≫ pullback.fst p j = tF)
    (hFtriv : IsTrivial F.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) F.IsSheaf)
      ((modulePullback tF'.toLRSHom.toShHom).obj
        ((modulePullback (pullback.fst p j).toLRSHom.toShHom).obj L)))
    (σ : _root_.SheafOfModules.unit (structureSheafRing (pullback p j).toRingedSpace) ⟶
      (modulePullback (pullback.fst p j).toLRSHom.toShHom).obj L)
    (hσ : (modulePullback tF'.toLRSHom.toShHom).map σ ≠ 0) :
    ∃ U : S.Opens, Set.range t ⊆ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L) := by
  obtain ⟨U', hwU', hU'⟩ := exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus
    (pullback.snd p j) _ (pullback.snd p j).isClosedMap (SheafOfModules.unitHomEquiv _ σ) w
      fun x hx => by
      obtain ⟨z, rfl⟩ := exists_eq_of_isPullback_of_snd_eq hF j htF' hw hx
      exact mem_nonvanishingLocus_of_modulePullback_map_ne_zero tF' ps hFO _ hFtriv σ hσ z
  refine ⟨j ''ᵁ U', ?_, isTrivial_modulePullback_fst_ι_image p j L U' hU'⟩
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
  exact ⟨w, hwU', hw⟩

/-- **[Stacks, Tag 0BF2] when every `ℒ_i` is trivial, at a field-valued point.** Let
`p : P ⟶ S` and the `i k ≫ p : X k ⟶ S` (`k` in a finite type) be flat, proper and of finite
presentation, and let `ℒ` be invertible on `P` with every `(i k)^*ℒ` trivial. Let
`t : Spec K ⟶ S` be a point with values in a field, `F` the fibre of `p` over `t` and `FX k` the
fibre of `i k ≫ p` over `t`, given as pullback squares, with `𝒪_{Spec K} ⟶ ps_*𝒪_F` and every
`𝒪_{Spec K} ⟶ (isk k ≫ ps)_*𝒪_{FX k}` isomorphisms. If `ℒ` is trivial on `F` and
`H¹(F, 𝒪) ⟶ ⊕_k H¹(FX k, 𝒪)` is injective, then `ℒ` is trivial over `P ×_S U` for an open `U`
containing the image of `t`.

This is `exists_isTrivial_modulePullback_fst_ι_of_injective_H1` with the fibre presented by
arbitrary pullback squares over an arbitrary field-valued point, which is the form in which the
general case of Tag 0BF2 applies it after a base change. -/
theorem exists_isTrivial_modulePullback_fst_ι_of_injective_H1_of_isPullback
    {S P : Scheme.{u}} (p : P ⟶ S) [Flat p] [IsProper p] (hpfp : FinitePresentation p)
    {ι : Type u} [Finite ι] (X : ι → Scheme.{u}) (i : ∀ k, X k ⟶ P)
    (hflat : ∀ k, Flat (i k ≫ p)) (hprop : ∀ k, IsProper (i k ≫ p))
    (hfp : ∀ k, FinitePresentation (i k ≫ p))
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    [IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L]
    (htriv : ∀ k, IsTrivial (X k).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (X k).IsSheaf)
      ((modulePullback (i k).toLRSHom.toShHom).obj L))
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
    {F : Scheme.{u}} (tF : F ⟶ P) (ps : F ⟶ Spec (CommRingCat.of K))
    (hF : IsPullback tF ps p t)
    (hFO : IsIso (structureSheafHom ps.toLRSHom.toShHom))
    (hFtriv : IsTrivial F.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) F.IsSheaf)
      ((modulePullback tF.toLRSHom.toShHom).obj L))
    (FX : ι → Scheme.{u}) (isk : ∀ k, FX k ⟶ F) (tX : ∀ k, FX k ⟶ X k)
    (hX : ∀ k, IsPullback (tX k) (isk k ≫ ps) (i k ≫ p) t)
    (hXF : ∀ k, tX k ≫ i k = isk k ≫ tF)
    (hXO : ∀ k, IsIso (structureSheafHom (isk k ≫ ps).toLRSHom.toShHom))
    (hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace)) 1).obj
        ((sectionsOverBase ps.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap ps.toLRSHom.toShHom (isk k).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (structureSheafRing F.toRingedSpace)))))).hom c = 0) →
        c = 0) :
    ∃ U : S.Opens, Set.range t ⊆ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L) := by
  classical
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨R, j, hj, w, hw⟩ := S.exists_Spec_apply_eq (t pt)
  have hr : Set.range t ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x pt]
    exact ⟨w, hw⟩
  let χ : R ⟶ CommRingCat.of K := Spec.preimage (IsOpenImmersion.lift j t hr)
  have ht : Spec.map χ ≫ j = t := by
    simp only [χ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have := hpfp.1
  have := hpfp.2.1
  have := hpfp.2.2
  let pW := pullback.snd p j
  let q := pullback.fst p j
  let XW : ι → Scheme.{u} := fun k => pullback (i k ≫ p) j
  let iW : ∀ k, XW k ⟶ pullback p j := fun k =>
    pullback.map (i k ≫ p) j p j (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hiW : ∀ k, iW k ≫ pW = pullback.snd (i k ≫ p) j := fun k => pullback_map_comp_snd (i k) p j
  have hiWq : ∀ k, iW k ≫ q = pullback.fst (i k ≫ p) j ≫ i k := fun k =>
    pullback_map_comp_fst (i k) p j
  let tF' : F ⟶ pullback p j := pullback.lift tF (ps ≫ Spec.map χ)
    (by rw [hF.w, Category.assoc, ht])
  have htF' : tF' ≫ q = tF := pullback.lift_fst _ _ _
  choose tX' hX' hXF' using fun k =>
    exists_isPullback_pullbackMap_of_isPullback (hX k) (hXF k) j ht hF.w
  have hfpW : ∀ k, FinitePresentation (iW k ≫ pW) := fun k => by
    have := (hfp k).1
    have := (hfp k).2.1
    have := (hfp k).2.2
    rw [hiW]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let LW := (modulePullback q.toLRSHom.toShHom).obj L
  have : IsInvertible (pullback p j).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback p j).IsSheaf)
      LW := Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ L ‹_›
  have hFtriv' := isTrivial_modulePullback_modulePullback_of_comp tF' q tF htF' hFtriv
  obtain ⟨σ, hσ⟩ :=
    MinimalComplexFunctoriality.exists_unit_hom_modulePullback_ne_zero_of_injective_H1 χ pW
      ⟨inferInstance, inferInstance, inferInstance⟩ XW iW (fun k => hiW k ▸ inferInstance)
      (fun k => hiW k ▸ inferInstance) hfpW LW
      (fun k => isTrivial_modulePullback_modulePullback_of_comp (iW k) q _ rfl
        (isTrivial_modulePullback_scheme_of_comp _ _ _ (hiWq k).symm (htriv k)))
      tF' ps (isPullback_pullbackLift_of_comp_eq hF j ht) hFO
      hFtriv' FX isk tX' hX' hXF' hXO hinj
  exact exists_isTrivial_modulePullback_fst_ι_of_modulePullback_map_ne_zero p ps hF hFO j hw L
    tF' htF' hFtriv' σ hσ

/-- **[Stacks, Tag 0BF2] when every `ℒ_i` is trivial.** Let `p : P ⟶ S` and the
`i k ≫ p : X k ⟶ S` (`k` in a finite type) be flat, proper and of finite presentation, with
`𝒪_T ⟶ p_{T,*}𝒪` and `𝒪_T ⟶ (i k ≫ p)_{T,*}𝒪` isomorphisms after every base change `T ⟶ S`;
let `ℒ` be invertible on `P` with every `(i k)^*ℒ` trivial, and let `s ∈ S` be such that `ℒ` is
trivial on the fibre `P_s` and `H¹(P_s, 𝒪) ⟶ ⊕_k H¹(X_{k,s}, 𝒪)` is injective. Then `ℒ` is
trivial over `P ×_S U` for an open neighbourhood `U` of `s`.

`H¹(P_s, 𝒪)` is the degree-`1` cohomology of the `κ(s)`-linear derived global sections of
`𝒪_{P_s}`, and the `k`-th component of the map is
`Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap` along the base change `X_{k,s} ⟶ P_s` of
`i k`. -/
theorem exists_isTrivial_modulePullback_fst_ι_of_injective_H1
    {S P : Scheme.{u}} (p : P ⟶ S) [Flat p] [IsProper p] (_hpfp : FinitePresentation p)
    (_hpO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd p a).toLRSHom.toShHom))
    {ι : Type u} [Finite ι] (X : ι → Scheme.{u}) (i : ∀ k, X k ⟶ P)
    (_hflat : ∀ k, Flat (i k ≫ p)) (_hprop : ∀ k, IsProper (i k ≫ p))
    (_hfp : ∀ k, FinitePresentation (i k ≫ p))
    (_hO : ∀ k {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd (i k ≫ p) a).toLRSHom.toShHom))
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    [IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L]
    (_htriv : ∀ k, IsTrivial (X k).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (X k).IsSheaf)
      ((modulePullback (i k).toLRSHom.toShHom).obj L))
    (s : S)
    (_hfiber : IsTrivial (pullback p (S.fromSpecResidueField s)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p (S.fromSpecResidueField s)).IsSheaf)
      ((modulePullback (pullback.fst p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj L))
    (_hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (S.residueField s)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (structureSheafRing
              (pullback p (S.fromSpecResidueField s)).toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap (pullback.snd p (S.fromSpecResidueField s)).toLRSHom.toShHom
            (pullback.map (i k ≫ p) (S.fromSpecResidueField s) p (S.fromSpecResidueField s)
              (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (structureSheafRing
                (pullback p (S.fromSpecResidueField s)).toRingedSpace)))))).hom c = 0) →
        c = 0) :
    ∃ U : S.Opens, s ∈ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L) := by
  let e := S.fromSpecResidueField s
  let isk : ∀ k, pullback (i k ≫ p) e ⟶ pullback p e := fun k =>
    pullback.map (i k ≫ p) e p e (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hisk : ∀ k, isk k ≫ pullback.snd p e = pullback.snd (i k ≫ p) e := fun k =>
    pullback_map_comp_snd (i k) p e
  have hX : ∀ k, IsPullback (pullback.fst (i k ≫ p) e) (isk k ≫ pullback.snd p e)
      (i k ≫ p) e := fun k => by
    rw [hisk]
    exact IsPullback.of_hasPullback _ _
  have hXF : ∀ k, pullback.fst (i k ≫ p) e ≫ i k = isk k ≫ pullback.fst p e := fun k =>
    (pullback_map_comp_fst (i k) p e).symm
  have hXO : ∀ k, IsIso (structureSheafHom (isk k ≫ pullback.snd p e).toLRSHom.toShHom) :=
    fun k => by
      rw [hisk]
      exact _hO k e
  obtain ⟨U, hU, hL⟩ := exists_isTrivial_modulePullback_fst_ι_of_injective_H1_of_isPullback p
    _hpfp X i _hflat _hprop _hfp L _htriv e (pullback.fst p e) (pullback.snd p e)
    (IsPullback.of_hasPullback p e) (_hpO e) _hfiber (fun k => pullback (i k ≫ p) e) isk
    (fun k => pullback.fst (i k ≫ p) e) hX hXF hXO _hinj
  refine ⟨U, hU ?_, hL⟩
  show s ∈ Set.range (S.fromSpecResidueField s)
  rw [Scheme.range_fromSpecResidueField]
  exact Set.mem_singleton s

end AlgebraicGeometry.SheafOfModules

end
