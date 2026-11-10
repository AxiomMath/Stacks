module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Capture
public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.Sectionwise

/-!
# Eventual injectivity of the system of quotients on sections over an affine open

For the directed system of quotients `Sym(ℱᵢ)/ℐ` mapping to a quasi-coherent algebra `𝒜` on a
quasi-compact quasi-separated scheme `X`: over an affine open of `X`, two sections of a member of
the system with the same image in `𝒜` already agree in a later member.

## Main results

* `Stacks.SymQuotientSystem.quotIncl_right_app` and
  `Stacks.SymQuotientSystem.surjective_quotIncl_right_app`: the surjection
  `Sym(ℱᵢ) ⟶ Sym(ℱᵢ)/ℐ` on sections over an open is the map on sections of the closed immersion
  `𝐙(ℐ) ⟶ 𝐕(ℱᵢ)`, and it is surjective over an affine open.
* `Stacks.SymQuotientSystem.quotIncl_comp_systemMap`: enlarging the ideal is compatible with the
  two surjections out of `Sym(ℱᵢ)`.
* `Stacks.SymQuotientSystem.exists_map_eq_of_coconeApp_eq`: two sections of a member of the
  system over an affine open with the same image in `𝒜` agree in a later member.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.SymQuotientAlgebra

universe u

namespace Stacks.SymQuotientSystem

variable {X : Scheme.{u}}

/-! ### Restriction along an equality of opens -/

/-- A ring map with a left inverse in `CommRingCat` is injective. -/
private theorem injective_of_comp_eq_id {A B : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ A)
    (h : f ≫ g = 𝟙 A) : Function.Injective f.hom :=
  Function.LeftInverse.injective (g := g.hom) fun r => by
    simpa using ConcreteCategory.congr_hom h r

/-- Restriction of sections along an inclusion of opens `W ≤ V` with `V ≤ W` is injective. -/
theorem injective_presheaf_map {Z : Scheme.{u}} {V W : Z.Opens} (hle : W ≤ V) (hle' : V ≤ W) :
    Function.Injective (Z.presheaf.map (homOfLE hle).op).hom :=
  injective_of_comp_eq_id _ (Z.presheaf.map (homOfLE hle').op)
    ((Z.presheaf.map_comp _ _).symm.trans
      ((congrArg Z.presheaf.map
        (Subsingleton.elim ((homOfLE hle).op ≫ (homOfLE hle').op) (𝟙 (op V)))).trans
          (Z.presheaf.map_id (op V))))

/-! ### Sections of the surjection onto a quotient -/

/-- **The surjection `Sym(ℱ) ⟶ Sym(ℱ)/ℐ` on sections over an open of `X`** is the map on
sections of the closed immersion `𝐙(ℐ) ⟶ 𝐕(ℱ)` over the preimage of that open. -/
theorem quotIncl_right_app (E : SheafOfModules.{u} X.ringCatSheaf) [E.IsQuasicoherent]
    (J : (Scheme.Modules.vectorBundle X E).IdealSheafData) (U : X.Opens) :
    (pushforwardAlgebraMap (quotIncl E J)).right.hom.app (op U) =
      J.subschemeι.app (Scheme.Modules.vectorBundleToBase X E ⁻¹ᵁ U) := by
  rw [pushforwardAlgebraMap_app (quotIncl E J) U (preimage_le_preimage_preimage _ _)]
  exact Scheme.Hom.appLE_eq_app _

/-- **The surjection `Sym(ℱ) ⟶ Sym(ℱ)/ℐ` is surjective on sections over an affine open.** -/
theorem surjective_quotIncl_right_app (E : SheafOfModules.{u} X.ringCatSheaf)
    [E.IsQuasicoherent] (J : (Scheme.Modules.vectorBundle X E).IdealSheafData) (U : X.Opens)
    (hU : IsAffineOpen U) :
    Function.Surjective ((pushforwardAlgebraMap (quotIncl E J)).right.hom.app (op U)).hom := by
  have := Scheme.Modules.isAffineHom_vectorBundleToBase X E
  have hV : IsAffineOpen (Scheme.Modules.vectorBundleToBase X E ⁻¹ᵁ U) := hU.preimage _
  have hs := Scheme.Hom.app_surjective J.subschemeι
    (Scheme.Modules.vectorBundleToBase X E ⁻¹ᵁ U) hV
  intro z
  obtain ⟨w, hw⟩ := hs z
  refine ⟨w, Eq.trans ?_ hw⟩
  exact congrArg (fun k => (CommRingCat.Hom.hom k) w) (quotIncl_right_app E J U)

/-- **Enlarging the ideal is compatible with the two surjections out of `Sym(ℱ)`**: at a fixed
stage of the system of modules, the surjection onto the smaller quotient followed by the
transition morphism is the surjection onto the larger quotient. -/
theorem quotIncl_comp_systemMap {E : SheafOfModules.{u} X.ringCatSheaf} [E.IsQuasicoherent]
    {J J' : (Scheme.Modules.vectorBundle X E).IdealSheafData} (g : E ⟶ E) (hg : g = 𝟙 E)
    (h : J ≤ J'.map (Scheme.Modules.vectorBundleMap X g).left) :
    pushforwardAlgebraMap (quotIncl E J) ≫ symQuotientAlgebraMap E E g J J' h =
      pushforwardAlgebraMap (quotIncl E J') := by
  refine (pushforwardAlgebraMap_comp (symQuotientOverMap E E g J J' h)
    (quotIncl E J)).symm.trans (congrArg (fun t => pushforwardAlgebraMap t) ?_)
  refine Over.OverMorphism.ext ?_
  change (symQuotientOverMap E E g J J' h).left ≫ J.subschemeι = J'.subschemeι
  refine (symQuotientOverMap_left_subschemeι E E g J J' h).trans ?_
  subst hg
  rw [Scheme.Modules.vectorBundleMap_id, Over.id_left]
  exact Category.comp_id _


/-- An isomorphism of algebra sheaves is injective on sections over an open. -/
theorem injective_iso_right_app {A B : X.QuasicoherentAlgebra} (e : A ≅ B) (U : X.Opens) :
    Function.Injective (e.hom.right.hom.app (op U)).hom :=
  injective_of_comp_eq_id _ (e.inv.right.hom.app (op U))
    (congrArg (fun k : A ⟶ A => k.right.hom.app (op U)) e.hom_inv_id)

/-! ### Eventual injectivity -/

variable (𝒜 : X.QuasicoherentAlgebra) [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent 𝒜]
  {I : Type u} [PartialOrder I] {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  [∀ i, (D.obj i).IsQuasicoherent]
  (φ : D ⟶ (Functor.const I).obj
    (Scheme.QuasicoherentAlgebra.underlyingModule 𝒜 : SheafOfModules.{u} X.ringCatSheaf))

/-- The two lifts of two sections of a quotient with the same image in `𝒜` have the same image
under the projection to the vector bundle. -/
theorem pushforwardAlgebraMap_proj_eq (U : X.Opens) (a : Index (proj 𝒜 φ))
    (x y : ((system (proj 𝒜 φ)).obj a).right.obj.obj (op U))
    (hxy : ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom x =
      ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom y)
    (x' y' : (pushforwardAlgebra
      (Scheme.Modules.vectorBundleOver X (F := D.obj a.idx)).hom).right.obj.obj (op U))
    (hx' : ((pushforwardAlgebraMap
      (quotIncl (D.obj a.idx) a.ideal)).right.hom.app (op U)).hom x' = x)
    (hy' : ((pushforwardAlgebraMap
      (quotIncl (D.obj a.idx) a.ideal)).right.hom.app (op U)).hom y' = y) :
    ((pushforwardAlgebraMap (proj 𝒜 φ a.idx)).right.hom.app (op U)).hom x' =
      ((pushforwardAlgebraMap (proj 𝒜 φ a.idx)).right.hom.app (op U)).hom y' := by
  have hmor : pushforwardAlgebraMap (quotIncl (D.obj a.idx) a.ideal) ≫
      coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a =
      pushforwardAlgebraMap (proj 𝒜 φ a.idx) ≫ (relativeSpecOverIso 𝒜).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (relativeSpecOverIso 𝒜).hom)
        (quotIncl_comp_quotientAlgebraLift (D.obj a.idx) a.ideal (proj 𝒜 φ a.idx) a.le_ker))
  have hev : ∀ z, ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom
        (((pushforwardAlgebraMap (quotIncl (D.obj a.idx) a.ideal)).right.hom.app (op U)).hom z) =
      ((relativeSpecOverIso 𝒜).hom.right.hom.app (op U)).hom
        (((pushforwardAlgebraMap (proj 𝒜 φ a.idx)).right.hom.app (op U)).hom z) :=
    fun z => congrArg (fun k => (k.right.hom.app (op U)).hom z) hmor
  refine injective_iso_right_app (relativeSpecOverIso 𝒜) U ?_
  refine (hev x').symm.trans (Eq.trans ?_ (hev y'))
  exact (congrArg (fun z =>
      ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom z)
    hx').trans (hxy.trans (congrArg (fun z =>
      ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom z)
    hy').symm)

/-- Two sections of `Sym(ℱᵢ)` over an open `U` of `X` with the same image under the map on
pushed-forward structure sheaves induced by `pᵢ` have the same image under the map on sections of
`pᵢ` over the preimage of `U` in `𝐕(ℱᵢ)`. -/
theorem app_eq_of_pushforwardAlgebraMap_proj_eq (U : X.Opens) (i : I)
    (x' y' : (pushforwardAlgebra
      (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom).right.obj.obj (op U))
    (hproj : ((pushforwardAlgebraMap (proj 𝒜 φ i)).right.hom.app (op U)).hom x' =
      ((pushforwardAlgebraMap (proj 𝒜 φ i)).right.hom.app (op U)).hom y') :
    ((proj 𝒜 φ i).left.app (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom x' =
      ((proj 𝒜 φ i).left.app (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom y' := by
  have hle := preimage_le_preimage_preimage (proj 𝒜 φ i) U
  have hpre : (proj 𝒜 φ i).left ⁻¹ᵁ
      (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U) =
      (relativeSpecOver 𝒜).hom ⁻¹ᵁ U :=
    congrArg (fun f => f ⁻¹ᵁ U) (Over.w (proj 𝒜 φ i))
  have hpfa := pushforwardAlgebraMap_app (proj 𝒜 φ i) U hle
  refine injective_presheaf_map hle hpre.le ?_
  exact (congrArg (fun k => (CommRingCat.Hom.hom k) x') hpfa).symm.trans
    (hproj.trans (congrArg (fun k => (CommRingCat.Hom.hom k) y') hpfa))

/-- **The difference of two sections of `Sym(ℱᵢ)` with the same image under `pᵢ` lies in a finite
type sheaf of ideals below the kernel of `pᵢ`**, over a quasi-compact quasi-separated `X` and an
open whose preimage in `𝐕(ℱᵢ)` is affine. -/
theorem exists_isFiniteType_le_sub_mem [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (U : X.Opens)
    (i : I) (hV : IsAffineOpen (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U))
    (x' y' : (pushforwardAlgebra
      (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom).right.obj.obj (op U))
    (happ : ((proj 𝒜 φ i).left.app
        (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom x' =
      ((proj 𝒜 φ i).left.app
        (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom y') :
    ∃ K : (Scheme.Modules.vectorBundle X (D.obj i)).IdealSheafData, K.IsFiniteType ∧
      K ≤ (proj 𝒜 φ i).left.ker ∧ x' - y' ∈ K.ideal
        ⟨Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U, hV⟩ := by
  have hqcp := quasiCompact_proj_left 𝒜 φ i
  have hmem : x' - y' ∈ (proj 𝒜 φ i).left.ker.ideal
      ⟨Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U, hV⟩ := by
    rw [Scheme.Hom.ker_apply]
    refine RingHom.mem_ker.mpr ((map_sub _ x' y').trans ?_)
    exact (congrArg (fun z => z - ((proj 𝒜 φ i).left.app
      (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom y') happ).trans (sub_self _)
  have hcs : CompactSpace ↥(Scheme.Modules.vectorBundleOver X (F := D.obj i)).left :=
    compactSpace_vectorBundle (D.obj i)
  have hqs : QuasiSeparatedSpace ↥(Scheme.Modules.vectorBundleOver X (F := D.obj i)).left :=
    quasiSeparatedSpace_vectorBundle (D.obj i)
  exact Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_mem ((proj 𝒜 φ i).left.ker)
    ⟨Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U, hV⟩ (x' - y') hmem

/-- **Two sections of `Sym(ℱᵢ)` whose difference lies in `ℐ ⊔ 𝒦` have the same image in
`Sym(ℱᵢ)/(ℐ ⊔ 𝒦)`.** -/
theorem quotIncl_app_eq_of_sub_mem (U : X.Opens) (i : I)
    (hV : IsAffineOpen (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U))
    (J : (Scheme.Modules.vectorBundle X (D.obj i)).IdealSheafData)
    (x' y' : (pushforwardAlgebra
      (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom).right.obj.obj (op U))
    (hmemb : x' - y' ∈ J.ideal
      ⟨Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U, hV⟩) :
    ((pushforwardAlgebraMap (quotIncl (D.obj i) J)).right.hom.app (op U)).hom x' =
      ((pushforwardAlgebraMap (quotIncl (D.obj i) J)).right.hom.app (op U)).hom y' := by
  have hk := Scheme.Hom.ker_apply J.subschemeι
    ⟨Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U, hV⟩
  rw [Scheme.IdealSheafData.ker_subschemeι] at hk
  have hz : (J.subschemeι.app
      (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom (x' - y') = 0 :=
    RingHom.mem_ker.mp (hk ▸ hmemb)
  have hz' : (J.subschemeι.app
        (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom x' =
      (J.subschemeι.app
        (Scheme.Modules.vectorBundleToBase X (D.obj i) ⁻¹ᵁ U)).hom y' :=
    sub_eq_zero.mp ((map_sub _ x' y').symm.trans hz)
  have e1 := quotIncl_right_app (D.obj i) J U
  exact (congrArg (fun k => (CommRingCat.Hom.hom k) x') e1).trans
    (hz'.trans (congrArg (fun k => (CommRingCat.Hom.hom k) y') e1).symm)

/-- **Eventual injectivity of the system on sections over an affine open.** Two sections of
`Sym(ℱᵢ)/ℐ` over an affine open of a quasi-compact quasi-separated `X` with the same image in
`𝒜` already agree in `Sym(ℱᵢ)/(ℐ ⊔ 𝒦)` for a finite type `𝒦` below the kernel of
`pᵢ : Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)`. -/
theorem exists_map_eq_of_coconeApp_eq [CompactSpace ↥X] [QuasiSeparatedSpace ↥X]
    (U : X.Opens) (hU : IsAffineOpen U) (a : Index (proj 𝒜 φ))
    (x y : ((system (proj 𝒜 φ)).obj a).right.obj.obj (op U))
    (hxy : ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom x =
      ((coconeApp (proj 𝒜 φ) 𝒜 (relativeSpecOverIso 𝒜) a).right.hom.app (op U)).hom y) :
    ∃ (b : Index (proj 𝒜 φ)) (h : a ≤ b),
      (((system (proj 𝒜 φ)).map (homOfLE h)).right.hom.app (op U)).hom x =
        (((system (proj 𝒜 φ)).map (homOfLE h)).right.hom.app (op U)).hom y := by
  have haff := Scheme.Modules.isAffineHom_vectorBundleToBase X (D.obj a.idx)
  have hV : IsAffineOpen (Scheme.Modules.vectorBundleToBase X (D.obj a.idx) ⁻¹ᵁ U) :=
    hU.preimage _
  obtain ⟨x', hx'⟩ := surjective_quotIncl_right_app (D.obj a.idx) a.ideal U hU x
  obtain ⟨y', hy'⟩ := surjective_quotIncl_right_app (D.obj a.idx) a.ideal U hU y
  obtain ⟨K, hKft, hKle, hKmem⟩ := exists_isFiniteType_le_sub_mem 𝒜 φ U a.idx hV x' y'
    (app_eq_of_pushforwardAlgebraMap_proj_eq 𝒜 φ U a.idx x' y'
      (pushforwardAlgebraMap_proj_eq 𝒜 φ U a x y hxy x' y' hx' hy'))
  have hab : a ≤ (⟨a.idx, a.ideal ⊔ K, a.isFiniteType.sup hKft,
      sup_le a.le_ker hKle⟩ : Index (proj 𝒜 φ)) :=
    Index.le_mk (proj 𝒜 φ) le_rfl (by rw [map_vectorBundleMap_refl]; exact le_sup_left)
  refine ⟨_, hab, ?_⟩
  have hbidx : a.idx ≤ (⟨a.idx, a.ideal ⊔ K, a.isFiniteType.sup hKft,
      sup_le a.le_ker hKle⟩ : Index (proj 𝒜 φ)).idx :=
    IndexLe.idx (proj 𝒜 φ) (leOfHom (homOfLE hab))
  have hbideal : a.ideal ≤ ((⟨a.idx, a.ideal ⊔ K, a.isFiniteType.sup hKft,
      sup_le a.le_ker hKle⟩ : Index (proj 𝒜 φ)).ideal).map
        (Scheme.Modules.vectorBundleMap X (D.map (homOfLE hbidx))).left :=
    IndexLe.ideal (proj 𝒜 φ) (leOfHom (homOfLE hab))
  have hgid := (congrArg D.map (Subsingleton.elim (homOfLE hbidx) (𝟙 a.idx))).trans
    (D.map_id a.idx)
  have hsys := quotIncl_comp_systemMap (D.map (homOfLE hbidx)) hgid hbideal
  have hev2 : ∀ z, (((system (proj 𝒜 φ)).map (homOfLE hab)).right.hom.app (op U)).hom
        (((pushforwardAlgebraMap (quotIncl (D.obj a.idx) a.ideal)).right.hom.app (op U)).hom z) =
      ((pushforwardAlgebraMap
        (quotIncl (D.obj a.idx) (a.ideal ⊔ K))).right.hom.app (op U)).hom z :=
    fun z => congrArg (fun k => (k.right.hom.app (op U)).hom z) hsys
  have hbig := quotIncl_app_eq_of_sub_mem U a.idx hV (a.ideal ⊔ K) x' y'
    (Scheme.IdealSheafData.le_def.mp le_sup_right _ hKmem)
  refine Eq.trans (congrArg (fun z =>
    (((system (proj 𝒜 φ)).map (homOfLE hab)).right.hom.app (op U)).hom z) hx'.symm) ?_
  refine Eq.trans ((hev2 x').trans (hbig.trans (hev2 y').symm)) ?_
  exact congrArg (fun z =>
    (((system (proj 𝒜 φ)).map (homOfLE hab)).right.hom.app (op U)).hom z) hy'

end Stacks.SymQuotientSystem

end
