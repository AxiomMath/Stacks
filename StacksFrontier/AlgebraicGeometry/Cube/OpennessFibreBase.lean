module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessSetup
public import StacksFrontier.AlgebraicGeometry.Cube.GlueTrivial
public import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit

/-!
# The fibre of the openness step of the theorem of the cube: the objects

In the notation of `StacksFrontier.AlgebraicGeometry.Cube.OpennessSetup`, let `L` be a
quasi-coherent module on `Q = (X ×_k Y) ×_k Spec R` and let `𝔭` be a prime of `R` over which `L`
is trivial on the fibre. This file proves the degree-zero input of the openness step of the
theorem of the cube ([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)): after base
change to `κ(𝔭)`, a degree-zero cocycle of the Čech complex `C` of `L` whose restriction to the
face `X_R` vanishes is zero.

## Main results

* `Stacks.Cech.cochainBaseChange_square`: the comparison of Čech cochains around a commutative
  square of schemes, read through `pullbackComp` and `pullbackCongr`.
* `Stacks.Cech.exists_global_of_cechD_eq_zero`: a Čech `0`-cocycle is a global section.
* `Stacks.Cech.eq_zero_of_pullbackSections_eq_zero`: a nonzero global section of a trivial
  module on a proper geometrically integral scheme pulls back to a nonzero section along any
  morphism from a nonempty scheme.
* `AlgebraicGeometry.Cube.Openness.h0_fibre`: the degree-zero statement above.

## Implementation notes

The base change of `C` to `κ(𝔭)` is the Čech complex of the fibre `Q_κ`
(`Stacks.Cech.cechBaseChangeData`, which needs `L` quasi-coherent and the opens `W s` affine).
The base change of the face map `ΦX` is compared with the face map of the fibre through
`Stacks.Cech.cochainBaseChange_square`, applied to the square `j_{X,κ} ≫ g_Q = g_X ≫ j_X`; only
a map, not an isomorphism, is needed out of the base change of the face complex, so the face
opens need not be affine. On the fibre a `0`-cocycle is a global section of a trivial module on
a proper geometrically integral scheme over `κ(𝔭)`, hence a constant multiple of the
trivializing section (Stacks Tag 0BUG, part (8)), and a nonzero multiple restricts to a nonzero
section on the nonempty face.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace Stacks.Cech

/-- The comparison on Čech cochains along two equal morphisms agrees, once the two pullback
modules are identified by `AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem cochainBaseChange_congr {X X' : Scheme.{u}} {h h' : X' ⟶ X} (e : h = h') (F : X.Modules)
    {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens) (hU : ∀ i, U' i = h ⁻¹ᵁ U i)
    (hU' : ∀ i, U' i = h' ⁻¹ᵁ U i) (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    cochainMap U' ((Scheme.Modules.pullbackCongr e).hom.app F).mapPresheaf p
        (cochainBaseChange h U U' (Equiv.refl I) F hU p s) =
      cochainBaseChange h' U U' (Equiv.refl I) F hU' p s := by
  subst e
  funext i
  simp [Scheme.Modules.pullbackCongr]

/-- **The comparison on Čech cochains around a commutative square.** For `h' ≫ g = gZ ≫ h`,
comparing along `g` and then `h'` is comparing along `h` and then `gZ`, once the two pullback
modules are identified through `pullbackComp` and `pullbackCongr`. -/
theorem cochainBaseChange_square {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (h : Z ⟶ X)
    (gZ : Z' ⟶ Z) (h' : Z' ⟶ X') (hcomm : h' ≫ g = gZ ≫ h) (F : X.Modules) {I : Type u}
    (U : I → X.Opens) (U' : I → X'.Opens) (hU' : ∀ i, U' i = g ⁻¹ᵁ U i)
    (UZ : I → Z.Opens) (hUZ : ∀ i, UZ i = h ⁻¹ᵁ U i) (UZ' : I → Z'.Opens)
    (hUZ' : ∀ i, UZ' i = gZ ⁻¹ᵁ UZ i) (hUZ'' : ∀ i, UZ' i = h' ⁻¹ᵁ U' i) (p : ℕ)
    (s : CechCochains.Cochain U F.presheaf p) :
    cochainMap UZ' ((Scheme.Modules.pullbackComp h' g).hom.app F ≫
        (Scheme.Modules.pullbackCongr hcomm).hom.app F ≫
          (Scheme.Modules.pullbackComp gZ h).inv.app F).mapPresheaf p
        (cochainBaseChange h' U' UZ' (Equiv.refl I) ((Scheme.Modules.pullback g).obj F) hUZ'' p
          (cochainBaseChange g U U' (Equiv.refl I) F hU' p s)) =
      cochainBaseChange gZ UZ UZ' (Equiv.refl I) ((Scheme.Modules.pullback h).obj F) hUZ' p
        (cochainBaseChange h U UZ (Equiv.refl I) F hUZ p s) := by
  funext i
  have e1 := congrFun (cochainBaseChange_comp g h' F U U' UZ' hU' hUZ'' p s) i
  have e2 := congrFun (cochainBaseChange_comp h gZ F U UZ UZ' hUZ hUZ' p s) i
  have e3 := congrFun (cochainBaseChange_congr hcomm F U UZ'
    (preimage_trans g h' U U' UZ' hU' hUZ'') (preimage_trans h gZ U UZ UZ' hUZ hUZ') p s) i
  simp only [cochainMap_apply, Scheme.Modules.mapPresheaf_app] at e1 e2 e3 ⊢
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, e1, e3, ← e2, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  rfl

/-- The intersection over a constant one-element tuple is the open itself. -/
theorem inter_const {Y : TopCat} {ι : Type*} (U : ι → Opens Y) (s : ι) :
    CechCochains.inter U (fun _ : Fin 1 => s) = U s := by
  simp [CechCochains.inter]

/-- Every point lies in some member of an open cover. -/
private theorem exists_mem_of_iSup_eq_top {Y : TopCat} {ι : Type*} {U : ι → Opens Y}
    (h : ⨆ i, U i = ⊤) (y : Y) : ∃ i, y ∈ U i :=
  Opens.mem_iSup.mp (by rw [h]; trivial)

/-- The global sections of a nonempty scheme form a nontrivial ring. -/
theorem nontrivial_sections_of_nonempty {Z : Scheme.{u}} [Nonempty Z] (W : Z.Opens)
    (hW : W = ⊤) : Nontrivial Γ(Z, W) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  exact (Z.presheaf.germ W z (hW ▸ trivial)).hom.domain_nontrivial

open Stacks.SchemeCohomology RingedSpaceModuleAdjunction in
/-- If a section `σ` of a module `M'` isomorphic to the structure sheaf is sent to a unit by the
isomorphism, then `σ` trivializes `M'` over every open. -/
theorem bijective_smul_resL_of_isUnit {Z : Scheme.{u}}
    (M' : SheafOfModules.{u} (structureSheafRing (ringedSpace Z)))
    (θ₀ : M' ≅ SheafOfModules.unit (structureSheafRing (ringedSpace Z)))
    (σ : M'.val.obj (Opposite.op ⊤))
    (ht : IsUnit (show Γ(Z, ⊤) from θ₀.hom.val.app (Opposite.op ⊤) σ))
    (V' : Z.Opens) (hV' : V' ≤ ⊤) :
    Function.Bijective
      fun c : Z.presheaf.obj (Opposite.op V') => c • AlgebraicGeometry.Cube.resL M' hV' σ := by
  have hbij : Function.Bijective (θ₀.hom.val.app (Opposite.op V')) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (Stacks.SheafOfModules.isIso_val_app_of_iso θ₀ (Opposite.op V'))
  refine (Function.Bijective.of_comp_iff' hbij _).mp ?_
  have hcomp : (θ₀.hom.val.app (Opposite.op V') ∘
      fun c : Z.presheaf.obj (Opposite.op V') => c • AlgebraicGeometry.Cube.resL M' hV' σ) =
      fun c => c * Z.presheaf.map (homOfLE hV').op (θ₀.hom.val.app (Opposite.op ⊤) σ) := by
    funext c
    simp only [Function.comp_apply]
    rw [(θ₀.hom.val.app (Opposite.op V')).hom.map_smul]
    congr 1
    exact PresheafOfModules.naturality_apply θ₀.hom.val _ σ
  rw [hcomp]
  exact IsUnit.isUnit_iff_mulRight_bijective.mp (ht.map _)

open Stacks.SchemeCohomology RingedSpaceModuleAdjunction in
/-- **A nonzero global section of a trivial module on a proper geometrically integral scheme
pulls back to a nonzero section along any morphism from a nonempty scheme.** The section is a
constant multiple of the trivializing section, the constants being the field `K` (Tag 0BUG), so
a nonzero one trivializes the module, and the pullback of a trivializing section is a unit by
`AlgebraicGeometry.Cube.isUnit_ev`. -/
theorem eq_zero_of_pullbackSections_eq_zero {K : Type u} [Field K] {Z Z' : Scheme.{u}}
    (q : Z ⟶ Spec (.of K)) [IsProper q] [GeometricallyIntegral q] (j : Z' ⟶ Z) [Nonempty Z']
    (M : Z.Modules) (θ : M ≅ SheafOfModules.unit _) (σ : Γ(M, ⊤))
    (hσ : pullbackSections j M ⊤ σ = 0) : σ = 0 := by
  by_contra hne
  let M' : SheafOfModules.{u} (structureSheafRing (ringedSpace Z)) := M
  let θ₀ : M' ≅ SheafOfModules.unit (structureSheafRing (ringedSpace Z)) := θ
  let θ' : (modulePullback (hom j)).obj M' ≅
      SheafOfModules.unit (structureSheafRing (ringedSpace Z')) :=
    (modulePullback (hom j)).mapIso θ₀ ≪≫ modulePullbackUnitIso (hom j)
  let t : Γ(Z, ⊤) := θ₀.hom.val.app (Opposite.op ⊤) σ
  have ht : t ≠ 0 := by
    intro h0
    apply hne
    have := congrArg (θ₀.inv.val.app (Opposite.op ⊤)) h0
    simp only [t] at this
    exact (Stacks.SheafOfModules.inv_val_app_hom_val_app θ₀ _ _).symm.trans
      (this.trans (map_zero _))
  have hiso := isIso_globalSections_of_geometricallyIntegral K q
  have hfield : IsField Γ(Z, ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (asIso ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop)).commRingCatIsoToRingEquiv.toMulEquiv.symm
  let _ := hfield.toField
  have hev := AlgebraicGeometry.Cube.isUnit_ev M' j θ' ⊤ σ
    (bijective_smul_resL_of_isUnit M' θ₀ σ (isUnit_iff_ne_zero.mpr ht))
  have h0 : AlgebraicGeometry.Cube.ev M' j θ' ⊤ σ = 0 := by
    unfold AlgebraicGeometry.Cube.ev
    rw [show Stacks.PullbackUnitGenerators.pullbackUnitSection (hom j) M' (Opposite.op ⊤) σ = 0
      from hσ]
    exact map_zero (θ'.hom.val.app (Opposite.op (j ⁻¹ᵁ ⊤))).hom
  rw [h0] at hev
  have : Nontrivial Γ(Z', j ⁻¹ᵁ ⊤) := nontrivial_sections_of_nonempty _ (by simp)
  exact not_isUnit_zero hev

/-- **Degree zero on the fibre.** Let `M` be a trivial module on a proper geometrically integral
scheme `Z` over a field, `U` an open cover of `Z` and `j : Z' ⟶ Z` a morphism from a nonempty
scheme. A global section of `M` whose restrictions to the members of `U` pull back to zero along
`j` is zero. -/
theorem eq_zero_of_cochainBaseChange_restr_eq_zero {K : Type u} [Field K]
    {Z Z' : Scheme.{u}} (q : Z ⟶ Spec (.of K)) [IsProper q] [GeometricallyIntegral q]
    (j : Z' ⟶ Z) [Nonempty Z'] (M : Z.Modules) (θ : M ≅ SheafOfModules.unit _) {ι : Type u}
    (U : ι → Z.Opens) (hU : ⨆ i, U i = ⊤) (V : ι → Z'.Opens) (hV : ∀ i, V i = j ⁻¹ᵁ U i)
    (σ : Γ(M, ⊤))
    (hface : cochainBaseChange j U V (Equiv.refl ι) M hV 0
      (fun _ => CechCochains.restr M.presheaf le_top σ) = 0) : σ = 0 := by
  refine eq_zero_of_pullbackSections_eq_zero q j M θ σ ?_
  let F : TopCat.Sheaf Ab.{u} Z' :=
    ⟨((Scheme.Modules.pullback j).obj M).presheaf, ((Scheme.Modules.pullback j).obj M).isSheaf⟩
  refine F.eq_of_locally_eq' (fun s : ι => V s) (j ⁻¹ᵁ ⊤)
    (fun s => homOfLE ((hV s).le.trans (j.preimage_mono le_top))) ?_ _ 0 fun s => ?_
  · intro x _
    obtain ⟨s, hs⟩ := exists_mem_of_iSup_eq_top hU (j x)
    exact Opens.mem_iSup.mpr ⟨s, (hV s).symm ▸ hs⟩
  · have hle : V s ≤ CechCochains.inter V (fun _ : Fin 1 => s) := (inter_const V s).ge
    have hle' : CechCochains.inter V (fun _ : Fin 1 => s) ≤
        j ⁻¹ᵁ CechCochains.inter U (fun _ : Fin 1 => s) :=
      (inter_eq_preimage j U V (Equiv.refl ι) hV _).le
    have h2 := congrArg (CechCochains.restr _ hle) (congrFun hface fun _ => s)
    rw [CechCochains.Cochain.zero_apply, map_zero] at h2
    change CechCochains.restr _ hle (CechCochains.restr _ hle'
      (pullbackSections j M _ (CechCochains.restr M.presheaf le_top σ))) = 0 at h2
    rw [CechCochains.restr_restr, pullbackSections_restr j M le_top
      ((hle.trans hle').trans (j.preimage_mono le_top)) (hle.trans hle') σ] at h2
    exact h2.trans (map_zero _).symm

end Stacks.Cech

namespace AlgebraicGeometry.Cube.Openness

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
  (R : Type u) [CommRing R] [Algebra k R]

omit [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g] in
/-- The members of the product family of opens are affine. -/
theorem isAffineOpen_W {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
    (hUXa : ∀ a, IsAffineOpen (UX a)) (hUYa : ∀ b, IsAffineOpen (UY b)) (s : I × J) :
    IsAffineOpen (W f g R UX UY s) := by
  have : IsAffine (UX s.1).toScheme := hUXa s.1
  have : IsAffine (UY s.2).toScheme := hUYa s.2
  have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top _
  have : IsAffineHom (pullback.fst (pullback.fst f g ≫ f) (φR R)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (pullback.fst f g ≫ f) (φR R)).flip inferInstance
  exact (isAffineOpen_inf_preimage f g (U := UX s.1) (V := UY s.2) (S₀ := ⊤) le_top
    le_top).preimage _

omit [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g] in
/-- The product family of opens covers `Q`. -/
theorem iSup_W_eq_top {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
    (hUX : ⊤ = ⨆ a, UX a) (hUY : ⊤ = ⨆ b, UY b) : ⨆ s, W f g R UX UY s = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  let p₀ := pullback.fst (pullback.fst f g ≫ f) (φR R) p
  obtain ⟨a, ha⟩ := Stacks.Cech.exists_mem_of_iSup_eq_top hUX.symm (pullback.fst f g p₀)
  obtain ⟨b, hb⟩ := Stacks.Cech.exists_mem_of_iSup_eq_top hUY.symm (pullback.snd f g p₀)
  exact Opens.mem_iSup.mpr ⟨(a, b), ha, hb⟩

end AlgebraicGeometry.Cube.Openness

namespace AlgebraicGeometry.Cube.Openness

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R] (𝔭 : Ideal R) [𝔭.IsPrime]

/-- The point `Spec κ(𝔭) ⟶ Spec R`. -/
abbrev σR : Spec (.of 𝔭.ResidueField) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.ResidueField))

/-- The fibre `Q_κ` of `Q` over `𝔭`. -/
abbrev Qκ : Scheme.{u} := pullback (qR f g R) (σR R 𝔭)

/-- The projection `Q_κ ⟶ Q`. -/
abbrev gQ : Qκ f g R 𝔭 ⟶ Q f g R := pullback.fst _ _

/-- The structure morphism `Q_κ ⟶ Spec κ`. -/
abbrev qκ : Qκ f g R 𝔭 ⟶ Spec (.of 𝔭.ResidueField) := pullback.snd _ _

/-- The fibre of `X_R` over `𝔭`. -/
abbrev XRκ : Scheme.{u} := pullback (qX f R) (σR R 𝔭)

/-- The projection `X_{R,κ} ⟶ X_R`. -/
abbrev gX : XRκ f R 𝔭 ⟶ XR f R := pullback.fst _ _

/-- The structure morphism `X_{R,κ} ⟶ Spec κ`. -/
abbrev qXκ : XRκ f R 𝔭 ⟶ Spec (.of 𝔭.ResidueField) := pullback.snd _ _

/-- The face of the fibre, `X_{R,κ} ⟶ Q_κ`. -/
def jXκ : XRκ f R 𝔭 ⟶ Qκ f g R 𝔭 :=
  pullback.map _ _ _ _ (jX f g y hy R) (𝟙 _) (𝟙 _)
    (by rw [jX_qR, Category.comp_id]) (by simp)

/-- The face of the fibre lies over `Spec κ`. -/
theorem jXκ_qκ : jXκ f g y hy R 𝔭 ≫ qκ f g R 𝔭 = qXκ f R 𝔭 := by
  rw [jXκ, pullback.lift_snd, Category.comp_id]

/-- The face of the fibre is the base change of the face. -/
theorem jXκ_gQ : jXκ f g y hy R 𝔭 ≫ gQ f g R 𝔭 = gX f R 𝔭 ≫ jX f g y hy R := by
  rw [jXκ, pullback.lift_fst]

end AlgebraicGeometry.Cube.Openness

namespace AlgebraicGeometry.Cube.Openness

open Stacks.Cech

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R]
  {I J : Type u} [Finite I] [Finite J] (UX : I → X.Opens) (UY : J → Y.Opens)
  (hUXa : ∀ a, IsAffineOpen (UX a)) (hUYa : ∀ b, IsAffineOpen (UY b))
  (hUX : (⊤ : X.Opens) = ⨆ a, UX a) (hUY : (⊤ : Y.Opens) = ⨆ b, UY b)
  (L : (Q f g R).Modules) [L.IsQuasicoherent]
  (𝔮 : Ideal R) [𝔮.IsPrime]

/-- The cover of the fibre `Q_κ`. -/
abbrev Wκ (s : I × J) : (Qκ f g R 𝔮).Opens := gQ f g R 𝔮 ⁻¹ᵁ W f g R UX UY s

/-- The cover of the face of the fibre. -/
abbrev Vκ (s : I × J) : (XRκ f R 𝔮).Opens := gX f R 𝔮 ⁻¹ᵁ (jX f g y hy R ⁻¹ᵁ W f g R UX UY s)

omit [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
  [Finite I] [Finite J] in
/-- The cover of the face of the fibre is the preimage of the cover of the fibre. -/
theorem Vκ_eq (s : I × J) :
    Vκ f g y hy R UX UY 𝔮 s = jXκ f g y hy R 𝔮 ⁻¹ᵁ Wκ f g R UX UY 𝔮 s := by
  rw [← Scheme.Hom.comp_preimage, jXκ_gQ]
  rfl

end AlgebraicGeometry.Cube.Openness

end

end
