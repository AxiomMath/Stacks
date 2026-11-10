module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessFibreBase
public import StacksFrontier.AlgebraicGeometry.Cube.KunnethOneCocycle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# Degree one on the fibre of the openness step of the theorem of the cube

Let `X` and `Y` be schemes over a field `k`, let `R` be a `k`-algebra with a prime `𝔮` and
residue field `κ`, and let `Q = X_R ×_R Y_R` with fibre `Q_κ` over `𝔮`. The fibre `Q_κ` is the
fibre product `X_{R,κ} ×_κ Y_{R,κ}`, and its faces through `κ`-points are the faces of that fibre
product. A Čech `1`-cocycle of a trivial module on a product of proper geometrically integral
schemes whose pullbacks to the two faces are coboundaries is a coboundary, and base change to the
fibre commutes with restriction to a face.

## Main results

* `CategoryTheory.Limits.isPullback_map_of_isPullback`: the base change of a fibre product is
  the fibre product of the base changes.
* `AlgebraicGeometry.Cube.Openness.isPullback_Qκ`: `Q_κ = X_{R,κ} ×_κ Y_{R,κ}`, and
  `jXκ_eq_faceX`, `jYκ_eq_faceY`: the faces of the fibre are the faces of that fibre product.
* `AlgebraicGeometry.Cube.Openness.exists_cechD_eq_of_faces`: the Künneth lemma
  `AlgebraicGeometry.Cube.exists_coboundary_of_faces` read through a trivialization of the
  module.
* `Stacks.Cech.extendScalars_face_square` and `Stacks.Cech.exists_face_coboundary`: base change
  to the fibre commutes with restriction to a face, so a face coboundary after base change is a
  face coboundary on the fibre.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe v u

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **Base change of a fibre product.** If `P = A ×_S B` and `S' ⟶ S`, then the base change
`P ×_S S'` is `(A ×_S S') ×_{S'} (B ×_S S')`, through the base changes of the projections. -/
theorem isPullback_map_of_isPullback {A B P S S' : C} {a : A ⟶ S} {b : B ⟶ S}
    {pA : P ⟶ A} {pB : P ⟶ B} (hsq : IsPullback pA pB a b) (c : P ⟶ S) (hc : pA ≫ a = c)
    (σ : S' ⟶ S) :
    IsPullback (pullback.map c σ a σ pA (𝟙 _) (𝟙 _) (by simp [hc]) (by simp))
      (pullback.map c σ b σ pB (𝟙 _) (𝟙 _) (by simp [← hc, hsq.w]) (by simp))
      (pullback.snd a σ) (pullback.snd b σ) := by
  set pA' := pullback.map c σ a σ pA (𝟙 _) (𝟙 _) (by simp [hc]) (by simp)
  set pB' := pullback.map c σ b σ pB (𝟙 _) (𝟙 _) (by simp [← hc, hsq.w]) (by simp)
  have hA₁ : pA' ≫ pullback.fst a σ = pullback.fst c σ ≫ pA := pullback.lift_fst _ _ _
  have hA₂ : pA' ≫ pullback.snd a σ = pullback.snd c σ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hB₁ : pB' ≫ pullback.fst b σ = pullback.fst c σ ≫ pB := pullback.lift_fst _ _ _
  have hB₂ : pB' ≫ pullback.snd b σ = pullback.snd c σ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hleft : IsPullback pA' (pullback.fst c σ) (pullback.fst a σ) pA := by
    refine IsPullback.of_right (h₁₂ := pullback.snd a σ) (h₂₂ := a) (v₁₃ := σ) ?_ hA₁
      (IsPullback.of_hasPullback a σ).flip
    rw [hA₂, hc]
    exact (IsPullback.of_hasPullback c σ).flip
  refine (IsPullback.of_right (h₁₂ := pullback.fst b σ) (h₂₂ := σ) (v₁₃ := b) ?_
    (by rw [hB₂, hA₂]) (IsPullback.of_hasPullback b σ)).flip
  rw [hB₁, ← pullback.condition]
  exact hleft.flip.paste_horiz hsq.flip

end CategoryTheory.Limits

namespace Stacks.Cech

section FaceComparison

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' Z Z' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (fZ : Z ⟶ Spec (.of A)) (fZ' : Z' ⟶ Spec (.of A')) (gZ : Z' ⟶ Z)
  (hsqZ : IsPullback gZ fZ' fZ (Spec.map (CommRingCat.ofHom φ)))
  (h : Z ⟶ X) (hh : h ≫ f = fZ) (h' : Z' ⟶ X') (hh' : h' ≫ f' = fZ')
  (hcomm : h' ≫ g = gZ ≫ h) (F : X.Modules) {I : Type u} (U : I → X.Opens)
  (UZ' : I → Z'.Opens) (hUZ' : ∀ s, UZ' s = h' ⁻¹ᵁ (g ⁻¹ᵁ U s))

/-- The base-change comparison out of the extension of scalars of the Čech complex of a face. -/
noncomputable def faceBaseChange (p : ℕ) :
    (ModuleCat.extendScalars φ).obj
        ((alternatingCechModuleComplex fZ (fun s => h ⁻¹ᵁ U s)
          ((Scheme.Modules.pullback h).obj F)).X p) ⟶
      alternatingCechModuleObj fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F)) p :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (alternatingCechModuleObj fZ'
      (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F)) p))
      (alternatingCochainBaseChangeₗ gZ (fun s => h ⁻¹ᵁ U s) (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        (Equiv.refl _) ((Scheme.Modules.pullback h).obj F) (fun _ => rfl) φ fZ fZ'
        (fun V => baseRingHom_comp_app φ fZ fZ' gZ hsqZ V) p))

/-- On a pure tensor `1 ⊗ m`, the face comparison is the base change of cochains applied to `m`. -/
theorem faceBaseChange_one_tmul (p : ℕ)
    (m : (alternatingCechModuleComplex fZ (fun s => h ⁻¹ᵁ U s)
      ((Scheme.Modules.pullback h).obj F)).X p) :
    (faceBaseChange φ fZ fZ' gZ hsqZ h F U p).hom ((1 : A') ⊗ₜ[A, φ] m) =
      alternatingCochainBaseChangeₗ gZ (fun s => h ⁻¹ᵁ U s) (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        (Equiv.refl _) ((Scheme.Modules.pullback h).obj F) (fun _ => rfl) φ fZ fZ'
        (fun V => baseRingHom_comp_app φ fZ fZ' gZ hsqZ V) p m :=
  one_smul (M := A') (α := alternatingCechModuleObj fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
    ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F)) p) _

/-- The face comparison commutes with the Čech differentials. -/
theorem faceBaseChange_d (p : ℕ)
    (w : (ModuleCat.extendScalars φ).obj
        ((alternatingCechModuleComplex fZ (fun s => h ⁻¹ᵁ U s)
          ((Scheme.Modules.pullback h).obj F)).X p)) :
    (faceBaseChange φ fZ fZ' gZ hsqZ h F U (p + 1)).hom
        (((ModuleCat.extendScalars φ).map ((alternatingCechModuleComplex fZ
          (fun s => h ⁻¹ᵁ U s) ((Scheme.Modules.pullback h).obj F)).d p (p + 1))).hom w) =
      (alternatingCechModuleDiff fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F)) p).hom
        ((faceBaseChange φ fZ fZ' gZ hsqZ h F U p).hom w) := by
  have key : (ModuleCat.extendScalars φ).map ((alternatingCechModuleComplex fZ
        (fun s => h ⁻¹ᵁ U s) ((Scheme.Modules.pullback h).obj F)).d p (p + 1)) ≫
        faceBaseChange φ fZ fZ' gZ hsqZ h F U (p + 1) =
      faceBaseChange φ fZ fZ' gZ hsqZ h F U p ≫
        alternatingCechModuleDiff fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
          ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F)) p := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
    refine Eq.trans ?_ (CategoryTheory.comp_apply _ _ _).symm
    refine Eq.trans (congrArg (faceBaseChange φ fZ fZ' gZ hsqZ h F U (p + 1)).hom
      (ModuleCat.ExtendScalars.map_tmul φ _ (1 : A') m)) ?_
    refine Eq.trans (faceBaseChange_one_tmul φ fZ fZ' gZ hsqZ h F U (p + 1) _) ?_
    refine Eq.trans ?_ (congrArg _ (faceBaseChange_one_tmul φ fZ fZ' gZ hsqZ h F U p m)).symm
    rw [alternatingCechModuleComplex_d]
    exact Subtype.ext
      (cochainBaseChange_cechD gZ _ _ (Equiv.refl _) _ (fun _ => rfl) p m.1).symm
  exact congrArg (fun k => k.hom w) key

include hcomm in
/-- The two preimages of an open `U s` under the commuting square agree. -/
theorem preimage_face_eq (s : I) : gZ ⁻¹ᵁ (h ⁻¹ᵁ U s) = h' ⁻¹ᵁ (g ⁻¹ᵁ U s) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcomm]

/-- The identification of the two pullbacks of `F` to the base-changed face. -/
noncomputable def faceModuleIso :
    (Scheme.Modules.pullback h').obj ((Scheme.Modules.pullback g).obj F) ≅
      (Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback h).obj F) :=
  (Scheme.Modules.pullbackComp h' g).app F ≪≫ (Scheme.Modules.pullbackCongr hcomm).app F ≪≫
    ((Scheme.Modules.pullbackComp gZ h).app F).symm

/-- **Base change commutes with restriction to a face.** -/
theorem extendScalars_face_square [IsSeparated f] [F.IsQuasicoherent] [Finite I]
    (hUaff : ∀ s, IsAffineOpen (U s)) (p : ℕ) :
    (ModuleCat.extendScalars φ).map
        ((alternatingCechModuleComplexPullbackMap f fZ h hh U (fun s => h ⁻¹ᵁ U s)
          (fun _ => rfl) F).f p) ≫ faceBaseChange φ fZ fZ' gZ hsqZ h F U p =
      (cechBaseChangeData φ f f' g hsq F U hUaff (fun s => g ⁻¹ᵁ U s) (Equiv.refl _)
          (fun _ => rfl)).alternatingIso.hom.f p ≫
        (alternatingCechModuleComplexPullbackMap f' fZ' h' hh' (fun s => g ⁻¹ᵁ U s)
          (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s)) (preimage_face_eq g gZ h h' hcomm U)
          ((Scheme.Modules.pullback g).obj F)).f p ≫
        (alternatingCechModuleComplexMapIso fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
          (faceModuleIso g gZ h h' hcomm F)).hom.f p := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  have hD := alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U (fun s => g ⁻¹ᵁ U s)
    (Equiv.refl _) F (fun _ => rfl) φ f f' (fun V => baseRingHom_comp_app φ f f' g hsq V) hsq
    hUaff p m
  refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
  refine Eq.trans ?_ (CategoryTheory.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg ((alternatingCechModuleComplexPullbackMap f' fZ' h' hh'
    (fun s => g ⁻¹ᵁ U s) (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s)) (preimage_face_eq g gZ h h' hcomm U)
    ((Scheme.Modules.pullback g).obj F)).f p ≫
      (alternatingCechModuleComplexMapIso fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        (faceModuleIso g gZ h h' hcomm F)).hom.f p).hom hD).symm
  refine Eq.trans (congrArg (faceBaseChange φ fZ fZ' gZ hsqZ h F U p).hom
    (ModuleCat.ExtendScalars.map_tmul φ _ (1 : A') m)) ?_
  refine Eq.trans (faceBaseChange_one_tmul φ fZ fZ' gZ hsqZ h F U p _) ?_
  exact Subtype.ext (cochainBaseChange_square g h gZ h' hcomm F U (fun s => g ⁻¹ᵁ U s)
    (fun _ => rfl) (fun s => h ⁻¹ᵁ U s) (fun _ => rfl) (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
    (fun _ => rfl) (preimage_face_eq g gZ h h' hcomm U) p m.1).symm

include hsqZ in
/-- **A face coboundary after base change is a face coboundary on the base-changed face.** -/
theorem exists_face_coboundary [IsSeparated f] [F.IsQuasicoherent] [Finite I]
    (hUaff : ∀ s, IsAffineOpen (U s))
    (c : (ModuleCat.extendScalars φ).obj ((alternatingCechModuleComplex f U F).X 1))
    (eZ : (ModuleCat.extendScalars φ).obj
      ((alternatingCechModuleComplex fZ (fun s => h ⁻¹ᵁ U s)
        ((Scheme.Modules.pullback h).obj F)).X 0))
    (hc : ((ModuleCat.extendScalars φ).map
        ((alternatingCechModuleComplexPullbackMap f fZ h hh U (fun s => h ⁻¹ᵁ U s)
          (fun _ => rfl) F).f 1)).hom c =
      ((ModuleCat.extendScalars φ).map ((alternatingCechModuleComplex fZ (fun s => h ⁻¹ᵁ U s)
        ((Scheme.Modules.pullback h).obj F)).d 0 1)).hom eZ) :
    ∃ e' : (alternatingCechModuleComplex fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        ((Scheme.Modules.pullback h').obj ((Scheme.Modules.pullback g).obj F))).X 0,
      ((alternatingCechModuleComplexPullbackMap f' fZ' h' hh' (fun s => g ⁻¹ᵁ U s)
          (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s)) (preimage_face_eq g gZ h h' hcomm U)
          ((Scheme.Modules.pullback g).obj F)).f 1).hom
        (((cechBaseChangeData φ f f' g hsq F U hUaff (fun s => g ⁻¹ᵁ U s) (Equiv.refl _)
          (fun _ => rfl)).alternatingIso.hom.f 1).hom c) =
      ((alternatingCechModuleComplex fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
        ((Scheme.Modules.pullback h').obj ((Scheme.Modules.pullback g).obj F))).d 0 1).hom e' := by
  let Tiso := alternatingCechModuleComplexMapIso fZ' (fun s => gZ ⁻¹ᵁ (h ⁻¹ᵁ U s))
    (faceModuleIso g gZ h h' hcomm F)
  refine ⟨(Tiso.inv.f 0).hom ((faceBaseChange φ fZ fZ' gZ hsqZ h F U 0).hom eZ), ?_⟩
  have h1 := congrArg (fun k => k.hom c)
    (extendScalars_face_square φ f f' g hsq fZ fZ' gZ hsqZ h hh h' hh' hcomm F U hUaff 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [hc, faceBaseChange_d φ fZ fZ' gZ hsqZ h F U 0 eZ] at h1
  have h3 := congrArg (Tiso.inv.f 1).hom h1
  have hcomm' := congrArg (fun k => k.hom ((faceBaseChange φ fZ fZ' gZ hsqZ h F U 0).hom eZ))
    (Tiso.inv.comm 0 1)
  simp only [ModuleCat.hom_comp] at hcomm'
  refine Eq.trans ?_ (h3.symm.trans ?_)
  · change _ = ((Tiso.hom.f 1 ≫ Tiso.inv.f 1).hom _)
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  · exact hcomm'.symm.trans rfl

end FaceComparison

end Stacks.Cech

namespace AlgebraicGeometry.Cube.Openness

open Stacks.Cech Stacks.SchemeCohomology RingedSpaceModuleAdjunction

/-- The trivialization of the pullback of a trivialized module. -/
noncomputable def pullbackTriv {Z Z' : Scheme.{u}} (j : Z' ⟶ Z) (M : Z.Modules)
    (θ : M ≅ SheafOfModules.unit _) :
    (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit Z'.ringCatSheaf :=
  (Scheme.Modules.pullback j).mapIso θ ≪≫ Stacks.PullbackAlgebra.pullbackUnitIso (hom j)

/-- **The pullback of a section, read through the trivializations, is the pullback of the
function.** -/
theorem pullbackTriv_pullbackSections {Z Z' : Scheme.{u}} (j : Z' ⟶ Z) (M : Z.Modules)
    (θ : M ≅ SheafOfModules.unit _) (V : Z.Opens) (m : Γ(M, V)) :
    (pullbackTriv j M θ).hom.val.app (Opposite.op (j ⁻¹ᵁ V)) (pullbackSections j M V m) =
      j.app V (θ.hom.val.app (Opposite.op V) m) :=
  (congrArg ((Stacks.PullbackAlgebra.pullbackUnitIso (hom j)).hom.val.app _)
    (Stacks.RingedSpace.pullbackUnit_naturality (hom j) θ.hom (Opposite.op V) m)).trans
    (Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit (hom j) (Opposite.op V)
      (θ.hom.val.app (Opposite.op V) m))

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem app_restr {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) {A B : Z.Opens} (h : B ≤ A)
    (m : Γ(M, A)) :
    φ.val.app (Opposite.op B) (CechCochains.restr M.presheaf h m) =
      CechCochains.restr N.presheaf h (φ.val.app (Opposite.op A) m) :=
  PresheafOfModules.naturality_apply φ.val _ m

/-- A `K`-rational point lands in some member of an open cover. -/
theorem exists_range_subset {K : Type u} [Field K] {T : Scheme.{u}} (x : Spec (.of K) ⟶ T)
    {ι : Type*} (U : ι → T.Opens) (hU : (⊤ : T.Opens) = ⨆ i, U i) :
    ∃ i, Set.range x ⊆ U i := by
  have : x (IsLocalRing.closedPoint K) ∈ ⨆ i, U i := hU ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp this
  refine ⟨i, ?_⟩
  rintro _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]

/-- The Čech differential at a tuple is the alternating sum of restrictions of the faces. -/
private theorem cechD_apply_eq_sum {Z : Scheme.{u}} (M : Z.Modules) {ι : Type u} (U : ι → Z.Opens)
    {n : ℕ} (z : CechCochains.Cochain U M.presheaf n) (i : Fin (n + 2) → ι) :
    CechCochains.cechD U M.presheaf n z i = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr M.presheaf (CechCochains.inter_le_omit U i j) (z (i ∘ j.succAbove)) :=
  rfl

/-- The face of a Čech cochain omitting `j` restricts to the cochain at any equal tuple. -/
private theorem restr_inter_le_omit_eq {Z : Scheme.{u}} (M : Z.Modules) {ι : Type u}
    (U : ι → Z.Opens) {n : ℕ} (z : CechCochains.Cochain U M.presheaf n) (i : Fin (n + 2) → ι)
    (j : Fin (n + 2)) (i' : Fin (n + 1) → ι) (hi : ∀ k, i (j.succAbove k) = i' k)
    (h : CechCochains.inter U i ≤ CechCochains.inter U i') :
    CechCochains.restr M.presheaf (CechCochains.inter_le_omit U i j) (z (i ∘ j.succAbove)) =
      CechCochains.restr M.presheaf h (z i') :=
  restr_cochain_congr U M z (funext hi) _ h

/-- The Čech differential of a `0`-cochain at a pair. -/
theorem cechD_zero_apply {Z : Scheme.{u}} (M : Z.Modules) {ι : Type u} (U : ι → Z.Opens)
    (z : CechCochains.Cochain U M.presheaf 0) (i : Fin 2 → ι)
    (h₁ : CechCochains.inter U i ≤ CechCochains.inter U (fun _ : Fin 1 => i 1))
    (h₀ : CechCochains.inter U i ≤ CechCochains.inter U (fun _ : Fin 1 => i 0)) :
    CechCochains.cechD U M.presheaf 0 z i =
      CechCochains.restr M.presheaf h₁ (z fun _ => i 1) -
        CechCochains.restr M.presheaf h₀ (z fun _ => i 0) := by
  rw [cechD_apply_eq_sum, Fin.sum_univ_two, restr_inter_le_omit_eq M U z i 0 _ (fun k => by
    fin_cases k; rfl) h₁, restr_inter_le_omit_eq M U z i 1 _ (fun k => by fin_cases k; rfl) h₀]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg]

/-- The Čech differential of a `1`-cochain at a triple. -/
theorem cechD_one_apply {Z : Scheme.{u}} (M : Z.Modules) {ι : Type u} (U : ι → Z.Opens)
    (z : CechCochains.Cochain U M.presheaf 1) (i : Fin 3 → ι)
    (h₀ : CechCochains.inter U i ≤ CechCochains.inter U ![i 1, i 2])
    (h₁ : CechCochains.inter U i ≤ CechCochains.inter U ![i 0, i 2])
    (h₂ : CechCochains.inter U i ≤ CechCochains.inter U ![i 0, i 1]) :
    CechCochains.cechD U M.presheaf 1 z i =
      CechCochains.restr M.presheaf h₀ (z ![i 1, i 2]) -
        CechCochains.restr M.presheaf h₁ (z ![i 0, i 2]) +
          CechCochains.restr M.presheaf h₂ (z ![i 0, i 1]) := by
  rw [cechD_apply_eq_sum, Fin.sum_univ_three,
    restr_inter_le_omit_eq M U z i 0 _ (fun k => by fin_cases k <;> rfl) h₀,
    restr_inter_le_omit_eq M U z i 1 _ (fun k => by fin_cases k <;> rfl) h₁,
    restr_inter_le_omit_eq M U z i 2 _ (fun k => by fin_cases k <;> rfl) h₂]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two,
    ← sub_eq_add_neg]
  norm_num

/-- Restriction in the structure sheaf, read as a sheaf of modules, is restriction of
functions. -/
theorem restr_unit {Z : Scheme.{u}} {A B : Z.Opens} (h : B ≤ A) (x : Γ(Z, A)) :
    CechCochains.restr (Scheme.Modules.presheaf (SheafOfModules.unit Z.ringCatSheaf)) h x =
      res h x := rfl

/-- The intersection of a pair of members of a family of opens. -/
theorem inter_pair_eq {Z : Scheme.{u}} {ι : Type u} (W : ι → Z.Opens) (s t : ι) :
    CechCochains.inter W ![s, t] = W s ⊓ W t := by
  simp only [CechCochains.inter]
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · refine le_iInf fun k => ?_
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

/-- The intersection of a triple of members of a family of opens. -/
theorem inter_triple_eq {Z : Scheme.{u}} {ι : Type u} (W : ι → Z.Opens) (s t r : ι) :
    CechCochains.inter W ![s, t, r] = W s ⊓ W t ⊓ W r := by
  simp only [CechCochains.inter]
  apply le_antisymm
  · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  · refine le_iInf fun k => ?_
    fin_cases k
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right

/-- **A cocycle read through a trivialization.** A Čech `1`-cocycle of a trivialized module,
read as functions on the pairwise intersections, satisfies the cocycle identity. -/
theorem res_app_cocycle_of_cechD_eq_zero {Z : Scheme.{u}} {ι : Type u} (W : ι → Z.Opens)
    (M : Z.Modules) (θ : M ≅ SheafOfModules.unit _) (c : CechCochains.Cochain W M.presheaf 1)
    (hc : CechCochains.cechD W M.presheaf 1 c = 0) (s t r : ι) :
    res (B := W s ⊓ W t ⊓ W r) inf_le_left
        (res (inter_pair_eq W s t).ge (θ.hom.val.app (Opposite.op _) (c ![s, t]))) +
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (res (inter_pair_eq W t r).ge (θ.hom.val.app (Opposite.op _) (c ![t, r]))) =
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (res (inter_pair_eq W s r).ge (θ.hom.val.app (Opposite.op _) (c ![s, r]))) := by
  let Θ : ∀ V : Z.Opens, Γ(M, V) → Γ(Z, V) := fun V m => θ.hom.val.app (Opposite.op V) m
  have hΘadd : ∀ V (m m' : Γ(M, V)), Θ V (m + m') = Θ V m + Θ V m' := fun V m m' =>
    map_add (θ.hom.val.app (Opposite.op V)).hom m m'
  have hΘsub : ∀ V (m m' : Γ(M, V)), Θ V (m - m') = Θ V m - Θ V m' := fun V m m' =>
    map_sub (θ.hom.val.app (Opposite.op V)).hom m m'
  have hΘzero : ∀ V, Θ V 0 = 0 := fun V => map_zero (θ.hom.val.app (Opposite.op V)).hom
  have hΘres : ∀ {A B : Z.Opens} (h : B ≤ A) (m : Γ(M, A)),
      Θ B (CechCochains.restr M.presheaf h m) = res h (Θ A m) := fun h m =>
    app_restr θ.hom h m
  have hWWW := inter_triple_eq W s t r
  have h := congrFun hc ![s, t, r]
  rw [CechCochains.Cochain.zero_apply, cechD_one_apply M W c ![s, t, r]
    (hWWW.le.trans ((inter_pair_eq W t r).ge.trans'
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
    (hWWW.le.trans ((inter_pair_eq W s r).ge.trans'
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)))
    (hWWW.le.trans ((inter_pair_eq W s t).ge.trans' inf_le_left))] at h
  have h2 := congrArg (fun m => res hWWW.ge (Θ _ m)) h
  simp only [hΘadd, hΘsub, hΘzero, hΘres, res_res, map_add, map_sub, map_zero] at h2
  change res _ (res _ (Θ _ (c ![s, t]))) + res _ (res _ (Θ _ (c ![t, r]))) =
    res _ (res _ (Θ _ (c ![s, r])))
  simp only [res_res]
  have h3 : res ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
          (inter_pair_eq W t r).ge) (Θ (CechCochains.inter W ![t, r]) (c ![t, r])) -
      res ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans (inter_pair_eq W s r).ge)
        (Θ (CechCochains.inter W ![s, r]) (c ![s, r])) +
      res (inf_le_left.trans (inter_pair_eq W s t).ge)
        (Θ (CechCochains.inter W ![s, t]) (c ![s, t])) = 0 := h2
  linear_combination h3

/-- **A face coboundary read through a trivialization.** If the base change along `j` of a Čech
`1`-cochain `c` of a trivialized module is a coboundary, then the pulled-back functions of `c`
on opens `O k` lying over the members `W' (s k)` are a coboundary. -/
theorem exists_res_app_eq_sub_of_cochainBaseChange {Z Q : Scheme.{u}} (j : Z ⟶ Q)
    {ι : Type u} (W' : ι → Q.Opens) (VZ : ι → Z.Opens) (hVZ : ∀ s, VZ s = j ⁻¹ᵁ W' s)
    (M : Q.Modules) (θ : M ≅ SheafOfModules.unit _) (c : CechCochains.Cochain W' M.presheaf 1)
    (eZ : CechCochains.Cochain VZ ((Scheme.Modules.pullback j).obj M).presheaf 0)
    (hZ : cochainBaseChange j W' VZ (Equiv.refl _) M hVZ 1 c =
      CechCochains.cechD VZ ((Scheme.Modules.pullback j).obj M).presheaf 0 eZ)
    {κ : Type*} (s : κ → ι) (O : κ → Z.Opens) (hO : ∀ k, O k ≤ VZ (s k)) :
    ∃ e : ∀ k, Γ(Z, O k), ∀ k k', ∀ h : O k ⊓ O k' ≤ j ⁻¹ᵁ CechCochains.inter W' ![s k, s k'],
      res h (j.app _ (θ.hom.val.app (Opposite.op _) (c ![s k, s k']))) =
        res inf_le_right (e k') - res inf_le_left (e k) := by
  let Ψ := pullbackTriv j M θ
  have hUle : ∀ k, O k ≤ CechCochains.inter VZ (fun _ => s k) := fun k => by
    rw [inter_const]
    exact hO k
  refine ⟨fun k => res (hUle k) (Ψ.hom.val.app _ (eZ fun _ => s k)), fun k k' hO' => ?_⟩
  have hle : O k ⊓ O k' ≤ CechCochains.inter VZ ![s k, s k'] :=
    (inf_le_inf (hO k) (hO k')).trans (inter_pair_eq VZ _ _).ge
  have h := congrFun hZ ![s k, s k']
  rw [cechD_zero_apply _ VZ eZ ![s k, s k'] (le_iInf fun _ => iInf_le _ 1)
    (le_iInf fun _ => iInf_le _ 0)] at h
  have hΨres : ∀ {A B : Z.Opens} (h : B ≤ A) (m : Γ((Scheme.Modules.pullback j).obj M, A)),
      Ψ.hom.val.app (Opposite.op B) (CechCochains.restr _ h m) =
        res h (Ψ.hom.val.app (Opposite.op A) m) := fun h m => app_restr Ψ.hom h m
  have hΨsub : ∀ V' (m m' : Γ((Scheme.Modules.pullback j).obj M, V')),
      Ψ.hom.val.app (Opposite.op V') (m - m') =
        Ψ.hom.val.app (Opposite.op V') m - Ψ.hom.val.app (Opposite.op V') m' := fun V' m m' =>
    map_sub (Ψ.hom.val.app (Opposite.op V')).hom m m'
  rw [← pullbackTriv_pullbackSections j M θ, ← hΨres hO']
  have hcb : cochainBaseChange j W' VZ (Equiv.refl _) M hVZ 1 c ![s k, s k'] =
      CechCochains.restr _ (inter_eq_preimage _ W' VZ (Equiv.refl _) hVZ ![s k, s k']).le
        (pullbackSections j M _ (c ![s k, s k'])) := rfl
  rw [show CechCochains.restr _ hO' (pullbackSections j M _ (c ![s k, s k'])) =
      CechCochains.restr _ hle
        (cochainBaseChange j W' VZ (Equiv.refl _) M hVZ 1 c ![s k, s k']) by
      rw [hcb, CechCochains.restr_restr]
      rfl, h, map_sub, hΨsub]
  congr 1 <;>
  · refine (app_restr Ψ.hom hle _).trans ?_
    refine (congrArg (res hle) (app_restr Ψ.hom _ _)).trans ?_
    exact (res_res _ _ _).trans (res_res _ _ _).symm

/-- **A face coboundary through `appLE`.** If the base change along `j` of a Čech `1`-cochain
`c` of a trivialized module is a coboundary, then the images under `j.appLE` of the functions of
`c` on the pairwise intersections of the `W' (s k)` are a coboundary on the opens `O k`. -/
theorem exists_appLE_eq_sub_of_cochainBaseChange {Z Q : Scheme.{u}} (j : Z ⟶ Q)
    {ι : Type u} (W' : ι → Q.Opens) (VZ : ι → Z.Opens) (hVZ : ∀ s, VZ s = j ⁻¹ᵁ W' s)
    (M : Q.Modules) (θ : M ≅ SheafOfModules.unit _) (c : CechCochains.Cochain W' M.presheaf 1)
    (eZ : CechCochains.Cochain VZ ((Scheme.Modules.pullback j).obj M).presheaf 0)
    (hZ : cochainBaseChange j W' VZ (Equiv.refl _) M hVZ 1 c =
      CechCochains.cechD VZ ((Scheme.Modules.pullback j).obj M).presheaf 0 eZ)
    {κ : Type*} (s : κ → ι) (O : κ → Z.Opens) (hO : ∀ k, O k ≤ VZ (s k))
    (hle : ∀ k k', O k ⊓ O k' ≤ j ⁻¹ᵁ (W' (s k) ⊓ W' (s k'))) :
    ∃ e : ∀ k, Γ(Z, O k), ∀ k k',
      (j.appLE _ (O k ⊓ O k') (hle k k')).hom
          (res (inter_pair_eq W' (s k) (s k')).ge
            (θ.hom.val.app (Opposite.op _) (c ![s k, s k']))) =
        res inf_le_right (e k') - res inf_le_left (e k) := by
  obtain ⟨e, he⟩ := exists_res_app_eq_sub_of_cochainBaseChange j W' VZ hVZ M θ c eZ hZ s O hO
  refine ⟨e, fun k k' => Eq.trans ?_ (he k k' (by
    rw [inter_pair_eq]
    exact hle k k'))⟩
  change (Q.presheaf.map (homOfLE (inter_pair_eq W' (s k) (s k')).ge).op ≫
    j.appLE _ (O k ⊓ O k') (hle k k')).hom (θ.hom.val.app (Opposite.op _) (c ![s k, s k'])) = _
  rw [Scheme.Hom.map_appLE]
  rfl

/-- **A coboundary read through a trivialization.** A Čech `1`-cochain of a trivialized module
whose functions on the pairwise intersections are a coboundary is a coboundary. -/
theorem exists_cechD_eq_of_res_app_eq_sub {Z : Scheme.{u}} {ι : Type u} (W : ι → Z.Opens)
    (M : Z.Modules) (θ : M ≅ SheafOfModules.unit _) (c : CechCochains.Cochain W M.presheaf 1)
    (e : ∀ s, Γ(Z, W s))
    (he : ∀ s t, res (inter_pair_eq W s t).ge (θ.hom.val.app (Opposite.op _) (c ![s, t])) =
      res inf_le_right (e t) - res inf_le_left (e s)) :
    ∃ c' : CechCochains.Cochain W M.presheaf 0, CechCochains.cechD W M.presheaf 0 c' = c := by
  let Θ : ∀ V : Z.Opens, Γ(M, V) → Γ(Z, V) := fun V m => θ.hom.val.app (Opposite.op V) m
  have hΘsub : ∀ V (m m' : Γ(M, V)), Θ V (m - m') = Θ V m - Θ V m' := fun V m m' =>
    map_sub (θ.hom.val.app (Opposite.op V)).hom m m'
  have hΘres : ∀ {A B : Z.Opens} (h : B ≤ A) (m : Γ(M, A)),
      Θ B (CechCochains.restr M.presheaf h m) = res h (Θ A m) := fun h m =>
    app_restr θ.hom h m
  have hΘinj : ∀ V' (m m' : Γ(M, V')), Θ V' m = Θ V' m' → m = m' := fun V' m m' h =>
    (Stacks.SheafOfModules.inv_val_app_hom_val_app θ _ m).symm.trans
      ((congrArg (θ.inv.val.app (Opposite.op V')) h).trans
        (Stacks.SheafOfModules.inv_val_app_hom_val_app θ _ m'))
  let Θinv : ∀ V : Z.Opens, Γ(Z, V) → Γ(M, V) := fun V x' => θ.inv.val.app (Opposite.op V) x'
  have hinv : ∀ V' (x' : Γ(Z, V')), Θ V' (Θinv V' x') = x' :=
    fun V' x' => Stacks.SheafOfModules.hom_val_app_inv_val_app θ _ x'
  have hle0 : ∀ i : Fin 1 → ι, CechCochains.inter W i ≤ W (i 0) := fun i => iInf_le _ 0
  let c₀ : CechCochains.Cochain W M.presheaf 0 := fun i => Θinv _ (res (hle0 i) (e (i 0)))
  refine ⟨c₀, funext fun i => ?_⟩
  obtain ⟨s, t, rfl⟩ : ∃ s t, i = ![s, t] :=
    ⟨i 0, i 1, funext fun k => by fin_cases k <;> rfl⟩
  apply hΘinj
  have h₁ : CechCochains.inter W ![s, t] ≤ CechCochains.inter W (fun _ : Fin 1 => t) :=
    le_iInf fun _ => iInf_le (fun k => W (![s, t] k)) 1
  have h₀ : CechCochains.inter W ![s, t] ≤ CechCochains.inter W (fun _ : Fin 1 => s) :=
    le_iInf fun _ => iInf_le (fun k => W (![s, t] k)) 0
  rw [cechD_zero_apply M W c₀ ![s, t] h₁ h₀, hΘsub]
  change Θ _ (CechCochains.restr M.presheaf h₁ (c₀ fun _ => t)) -
    Θ _ (CechCochains.restr M.presheaf h₀ (c₀ fun _ => s)) = _
  rw [hΘres h₁, hΘres h₀]
  simp only [c₀]
  rw [hinv, hinv, res_res, res_res]
  refine res_injective_of_eq (inter_pair_eq W s t).ge (inter_pair_eq W s t) ?_
  have hsub : ∀ {A B : Z.Opens} (h : B ≤ A) (u v : Γ(Z, A)), res h (u - v) = res h u - res h v :=
    fun h u v => map_sub (Z.presheaf.map (homOfLE h).op).hom u v
  rw [hsub, res_res, res_res]
  exact (he s t).symm

/-- **Degree one on a product of proper geometrically integral schemes.** Let `Q = X ×_K Y`
with `X`, `Y` proper and geometrically integral over a field `K`, with `K`-points `x`, `y`, and
let `M` be a trivial module on `Q`. A Čech `1`-cocycle of `M` on the cover by boxes of finite
affine covers, whose pullbacks to the two faces through `y` and through `x` are coboundaries, is a
coboundary. This is the Künneth lemma `AlgebraicGeometry.Cube.exists_coboundary_of_faces` read
through the trivialization. -/
theorem exists_cechD_eq_of_faces {K : Type u} [Field K] {X Y Q : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    {pX : Q ⟶ X} {pY : Q ⟶ Y} (hsq : IsPullback pX pY f g)
    (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    {I J : Type u} [Finite I] [Finite J] (U : I → X.Opens) (V : J → Y.Opens)
    (hUa : ∀ a, IsAffineOpen (U a)) (hVa : ∀ b, IsAffineOpen (V b))
    (hU : (⊤ : X.Opens) = ⨆ a, U a) (hV : (⊤ : Y.Opens) = ⨆ b, V b)
    (W' : I × J → Q.Opens) (hW' : ∀ s, W' s = Cube.W pX pY U V s)
    (M : Q.Modules) (θ : M ≅ SheafOfModules.unit _)
    (jX : X ⟶ Q) (hjX : jX = faceX hsq y hy) (VX : I × J → X.Opens)
    (hVX : ∀ s, VX s = jX ⁻¹ᵁ W' s)
    (jY : Y ⟶ Q) (hjY : jY = faceY hsq x hx) (VY : I × J → Y.Opens)
    (hVY : ∀ s, VY s = jY ⁻¹ᵁ W' s)
    (c : CechCochains.Cochain W' M.presheaf 1) (hc : CechCochains.cechD W' M.presheaf 1 c = 0)
    (eX : CechCochains.Cochain VX ((Scheme.Modules.pullback jX).obj M).presheaf 0)
    (hX : cochainBaseChange jX W' VX (Equiv.refl _) M hVX 1 c =
      CechCochains.cechD VX ((Scheme.Modules.pullback jX).obj M).presheaf 0 eX)
    (eY : CechCochains.Cochain VY ((Scheme.Modules.pullback jY).obj M).presheaf 0)
    (hY : cochainBaseChange jY W' VY (Equiv.refl _) M hVY 1 c =
      CechCochains.cechD VY ((Scheme.Modules.pullback jY).obj M).presheaf 0 eY) :
    ∃ c' : CechCochains.Cochain W' M.presheaf 0, CechCochains.cechD W' M.presheaf 0 c' = c := by
  obtain rfl : W' = Cube.W pX pY U V := funext hW'
  subst hjX hjY
  let cs : ∀ s t : I × J, Γ(Q, Cube.W pX pY U V s ⊓ Cube.W pX pY U V t) := fun s t =>
    res (inter_pair_eq _ s t).ge (θ.hom.val.app (Opposite.op _) (c ![s, t]))
  obtain ⟨a₀, hxa⟩ := exists_range_subset x U hU
  obtain ⟨b₀, hyb⟩ := exists_range_subset y V hV
  have hXK := exists_appLE_eq_sub_of_cochainBaseChange (faceX hsq y hy) _ VX hVX M θ c eX hX
    (fun a => (a, b₀)) U (fun a => by
      rw [hVX]
      exact le_faceX_preimage hsq y hy hyb) (le_faceX_preimage_W hsq hy U V hyb)
  have hYK := exists_appLE_eq_sub_of_cochainBaseChange (faceY hsq x hx) _ VY hVY M θ c eY hY
    (fun b => (a₀, b)) V (fun b => by
      rw [hVY]
      exact le_faceY_preimage hsq x hx hxa) (le_faceY_preimage_W hsq hx U V hxa)
  obtain ⟨e, he⟩ := exists_coboundary_of_faces hsq x hx y hy U V hUa hVa hU hV a₀ hxa b₀ hyb
    cs (res_app_cocycle_of_cechD_eq_zero _ M θ c hc) hXK hYK
  exact exists_cechD_eq_of_res_app_eq_sub _ M θ c e he

section Fibre

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R] (𝔮 : Ideal R) [𝔮.IsPrime]

/-- `Q = X_R ×_R Y_R`. -/
theorem isPullback_Q : IsPullback
    (pullback.map (pullback.fst f g ≫ f) (φR R) f (φR R) (pullback.fst f g) (𝟙 _) (𝟙 _)
      (by simp) (by simp))
    (pullback.map (pullback.fst f g ≫ f) (φR R) g (φR R) (pullback.snd f g) (𝟙 _) (𝟙 _)
      (by simp [pullback.condition]) (by simp))
    (qX f R) (qY g R) :=
  isPullback_map_of_isPullback (IsPullback.of_hasPullback f g) _ rfl (φR R)

/-- The projection `Q ⟶ X_R`. -/
noncomputable abbrev prX : Q f g R ⟶ XR f R :=
  pullback.map (pullback.fst f g ≫ f) (φR R) f (φR R) (pullback.fst f g) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The projection `Q ⟶ Y_R`. -/
noncomputable abbrev prY : Q f g R ⟶ YR g R :=
  pullback.map (pullback.fst f g ≫ f) (φR R) g (φR R) (pullback.snd f g) (𝟙 _) (𝟙 _)
    (by simp [pullback.condition]) (by simp)

/-- The projection `Q ⟶ X_R` lies over `Spec R`. -/
theorem prX_qX : prX f g R ≫ qX f R = qR f g R :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The projection `Q ⟶ Y_R` lies over `Spec R`. -/
theorem prY_qY : prY f g R ≫ qY g R = qR f g R :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The fibre of `Y_R` over `𝔮`. -/
abbrev YRκ : Scheme.{u} := pullback (qY g R) (σR R 𝔮)

/-- The projection `Y_{R,κ} ⟶ Y_R`. -/
abbrev gY : YRκ g R 𝔮 ⟶ YR g R := pullback.fst _ _

/-- The structure morphism `Y_{R,κ} ⟶ Spec κ`. -/
abbrev qYκ : YRκ g R 𝔮 ⟶ Spec (.of 𝔮.ResidueField) := pullback.snd _ _

/-- The face of the fibre, `Y_{R,κ} ⟶ Q_κ`. -/
noncomputable def jYκ : YRκ g R 𝔮 ⟶ Qκ f g R 𝔮 :=
  pullback.map _ _ _ _ (jY f g x hx R) (𝟙 _) (𝟙 _)
    (by rw [jY_qR, Category.comp_id]) (by simp)

/-- The face `Y_{R,κ} ⟶ Q_κ` lies over `Spec κ`. -/
theorem jYκ_qκ : jYκ f g x hx R 𝔮 ≫ qκ f g R 𝔮 = qYκ g R 𝔮 := by
  rw [jYκ, pullback.lift_snd, Category.comp_id]

/-- The face `Y_{R,κ} ⟶ Q_κ` is the base change of the face `Y_R ⟶ Q`. -/
theorem jYκ_gQ : jYκ f g x hx R 𝔮 ≫ gQ f g R 𝔮 = gY g R 𝔮 ≫ jY f g x hx R := by
  rw [jYκ, pullback.lift_fst]

/-- The projection `Q_κ ⟶ X_{R,κ}`. -/
noncomputable abbrev pXκ : Qκ f g R 𝔮 ⟶ XRκ f R 𝔮 :=
  pullback.map (qR f g R) (σR R 𝔮) (qX f R) (σR R 𝔮) (prX f g R) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The projection `Q_κ ⟶ Y_{R,κ}`. -/
noncomputable abbrev pYκ : Qκ f g R 𝔮 ⟶ YRκ g R 𝔮 :=
  pullback.map (qR f g R) (σR R 𝔮) (qY g R) (σR R 𝔮) (prY f g R) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- **`Q_κ = X_{R,κ} ×_κ Y_{R,κ}`.** -/
theorem isPullback_Qκ : IsPullback (pXκ f g R 𝔮) (pYκ f g R 𝔮) (qXκ f R 𝔮) (qYκ g R 𝔮) :=
  isPullback_map_of_isPullback (isPullback_Q f g R) (qR f g R) (prX_qX f g R) (σR R 𝔮)

/-- The `R`-point of `Y_R` through `y`. -/
noncomputable def yR : Spec (.of R) ⟶ YR g R :=
  pullback.lift (φR R ≫ y) (𝟙 _) (by rw [Category.assoc, hy, Category.comp_id, Category.id_comp])

/-- The `κ`-point of `Y_{R,κ}` through `y`. -/
noncomputable def yκ : Spec (.of 𝔮.ResidueField) ⟶ YRκ g R 𝔮 :=
  pullback.lift (σR R 𝔮 ≫ yR g y hy R) (𝟙 _) (by
    rw [Category.assoc, yR, pullback.lift_snd, Category.comp_id, Category.id_comp])

/-- The point `y_κ` is a section of `Y_{R,κ} ⟶ Spec κ`. -/
theorem yκ_qYκ : yκ g y hy R 𝔮 ≫ qYκ g R 𝔮 = 𝟙 _ := by rw [yκ, pullback.lift_snd]

/-- The `R`-point of `X_R` through `x`. -/
noncomputable def xR : Spec (.of R) ⟶ XR f R :=
  pullback.lift (φR R ≫ x) (𝟙 _) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])

/-- The `κ`-point of `X_{R,κ}` through `x`. -/
noncomputable def xκ : Spec (.of 𝔮.ResidueField) ⟶ XRκ f R 𝔮 :=
  pullback.lift (σR R 𝔮 ≫ xR f x hx R) (𝟙 _) (by
    rw [Category.assoc, xR, pullback.lift_snd, Category.comp_id, Category.id_comp])

/-- The point `x_κ` is a section of `X_{R,κ} ⟶ Spec κ`. -/
theorem xκ_qXκ : xκ f x hx R 𝔮 ≫ qXκ f R 𝔮 = 𝟙 _ := by rw [xκ, pullback.lift_snd]

/-- The face `X_R ⟶ Q` is a section of the projection `Q ⟶ X_R`. -/
theorem jX_prX : jX f g y hy R ≫ prX f g R = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, prX, pullback.lift_fst, jX, ← Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, prX_qX, jX_qR, Category.id_comp]

/-- The face `X_R ⟶ Q` followed by `Q ⟶ Y_R` is `X_R ⟶ Spec R` followed by `y_R`. -/
theorem jX_prY : jX f g y hy R ≫ prY f g R = qX f R ≫ yR g y hy R := by
  apply pullback.hom_ext
  · rw [Category.assoc, prY, pullback.lift_fst, jX, ← Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_snd, Category.assoc, yR, pullback.lift_fst,
      ← Category.assoc, ← Category.assoc, pullback.condition]
  · rw [Category.assoc, prY_qY, jX_qR, Category.assoc, yR, pullback.lift_snd,
      Category.comp_id]

/-- The face `Y_R ⟶ Q` is a section of the projection `Q ⟶ Y_R`. -/
theorem jY_prY : jY f g x hx R ≫ prY f g R = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, prY, pullback.lift_fst, jY, ← Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, prY_qY, jY_qR, Category.id_comp]

/-- The face `Y_R ⟶ Q` followed by `Q ⟶ X_R` is `Y_R ⟶ Spec R` followed by `x_R`. -/
theorem jY_prX : jY f g x hx R ≫ prX f g R = qY g R ≫ xR f x hx R := by
  apply pullback.hom_ext
  · rw [Category.assoc, prX, pullback.lift_fst, jY, ← Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_fst, Category.assoc, xR, pullback.lift_fst,
      ← Category.assoc, ← Category.assoc, pullback.condition]
  · rw [Category.assoc, prX_qX, jY_qR, Category.assoc, xR, pullback.lift_snd,
      Category.comp_id]

/-- The face of the fibre through `y` is the face of the fibre product through `y_κ`. -/
theorem jXκ_eq_faceX : jXκ f g y hy R 𝔮 =
    faceX (isPullback_Qκ f g R 𝔮) (yκ g y hy R 𝔮) (yκ_qYκ g y hy R 𝔮) := by
  apply (isPullback_Qκ f g R 𝔮).hom_ext
  · rw [faceX_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, pXκ, pullback.lift_fst, ← Category.assoc, jXκ_gQ, Category.assoc,
        jX_prX, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pXκ, pullback.lift_snd, Category.comp_id, jXκ_qκ, Category.id_comp]
  · rw [faceX_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, pYκ, pullback.lift_fst, ← Category.assoc, jXκ_gQ, Category.assoc,
        jX_prY, Category.assoc, yκ, pullback.lift_fst, ← Category.assoc, ← Category.assoc,
        pullback.condition]
    · rw [Category.assoc, pYκ, pullback.lift_snd, Category.comp_id, jXκ_qκ, Category.assoc, yκ,
        pullback.lift_snd, Category.comp_id]

/-- The face of the fibre through `x` is the face of the fibre product through `x_κ`. -/
theorem jYκ_eq_faceY : jYκ f g x hx R 𝔮 =
    faceY (isPullback_Qκ f g R 𝔮) (xκ f x hx R 𝔮) (xκ_qXκ f x hx R 𝔮) := by
  apply (isPullback_Qκ f g R 𝔮).hom_ext
  · rw [faceY_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, pXκ, pullback.lift_fst, ← Category.assoc, jYκ_gQ, Category.assoc,
        jY_prX, Category.assoc, xκ, pullback.lift_fst, ← Category.assoc, ← Category.assoc,
        pullback.condition]
    · rw [Category.assoc, pXκ, pullback.lift_snd, Category.comp_id, jYκ_qκ, Category.assoc, xκ,
        pullback.lift_snd, Category.comp_id]
  · rw [faceY_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, pYκ, pullback.lift_fst, ← Category.assoc, jYκ_gQ, Category.assoc,
        jY_prY, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pYκ, pullback.lift_snd, Category.comp_id, jYκ_qκ, Category.id_comp]

end Fibre

section Cover

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (R : Type u) [CommRing R] [Algebra k R] (𝔮 : Ideal R) [𝔮.IsPrime]
  {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)

/-- The cover of `X_{R,κ}` induced by `UX`. -/
abbrev UXκ (a : I) : (XRκ f R 𝔮).Opens := gX f R 𝔮 ⁻¹ᵁ (pullback.fst f (φR R) ⁻¹ᵁ UX a)

/-- The cover of `Y_{R,κ}` induced by `UY`. -/
abbrev UYκ (b : J) : (YRκ g R 𝔮).Opens := gY g R 𝔮 ⁻¹ᵁ (pullback.fst g (φR R) ⁻¹ᵁ UY b)

/-- The composite `Q_κ ⟶ X_{R,κ} ⟶ X_R ⟶ X` equals `Q_κ ⟶ Q ⟶ X ×_k Y ⟶ X`. -/
theorem pXκ_comp : pXκ f g R 𝔮 ≫ gX f R 𝔮 ≫ pullback.fst f (φR R) =
    gQ f g R 𝔮 ≫ pullback.fst (pullback.fst f g ≫ f) (φR R) ≫ pullback.fst f g := by
  rw [← Category.assoc, pXκ, pullback.lift_fst, Category.assoc, prX, pullback.lift_fst]

/-- The composite `Q_κ ⟶ Y_{R,κ} ⟶ Y_R ⟶ Y` equals `Q_κ ⟶ Q ⟶ X ×_k Y ⟶ Y`. -/
theorem pYκ_comp : pYκ f g R 𝔮 ≫ gY g R 𝔮 ≫ pullback.fst g (φR R) =
    gQ f g R 𝔮 ≫ pullback.fst (pullback.fst f g ≫ f) (φR R) ≫ pullback.snd f g := by
  rw [← Category.assoc, pYκ, pullback.lift_fst, Category.assoc, prY, pullback.lift_fst]

/-- The preimage in `Q_κ` of the product open `W s` of `Q` is the product open of the induced
covers of `X_{R,κ}` and `Y_{R,κ}`. -/
theorem Wκ_eq_W (s : I × J) :
    gQ f g R 𝔮 ⁻¹ᵁ W f g R UX UY s =
      Cube.W (pXκ f g R 𝔮) (pYκ f g R 𝔮) (UXκ f R 𝔮 UX) (UYκ g R 𝔮 UY) s := by
  ext p
  simp only [W, Cube.W, Cube.box, Scheme.Hom.preimage_inf, TopologicalSpace.Opens.coe_inf,
    Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.mem_preimage]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  simp only [pXκ_comp, pYκ_comp]

/-- If every `UX a` is affine, so is every `UXκ a`. -/
theorem isAffineOpen_UXκ (hUXa : ∀ a, IsAffineOpen (UX a)) (a : I) :
    IsAffineOpen (UXκ f R 𝔮 UX a) := by
  have : IsAffineHom (pullback.fst f (φR R)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (φR R)).flip inferInstance
  have : IsAffineHom (gX f R 𝔮) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (qX f R) (σR R 𝔮)).flip inferInstance
  exact ((hUXa a).preimage _).preimage _

/-- If every `UY b` is affine, so is every `UYκ b`. -/
theorem isAffineOpen_UYκ (hUYa : ∀ b, IsAffineOpen (UY b)) (b : J) :
    IsAffineOpen (UYκ g R 𝔮 UY b) :=
  isAffineOpen_UXκ g R 𝔮 UY hUYa b

/-- If the `UX a` cover `X`, the `UXκ a` cover `X_{R,κ}`. -/
theorem iSup_UXκ (hUX : (⊤ : X.Opens) = ⨆ a, UX a) :
    (⊤ : (XRκ f R 𝔮).Opens) = ⨆ a, UXκ f R 𝔮 UX a := by
  refine (eq_top_iff.mpr fun p _ => ?_).symm
  have : pullback.fst f (φR R) (gX f R 𝔮 p) ∈ ⨆ a, UX a := hUX ▸ trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp this
  exact Opens.mem_iSup.mpr ⟨a, ha⟩

/-- If the `UY b` cover `Y`, the `UYκ b` cover `Y_{R,κ}`. -/
theorem iSup_UYκ (hUY : (⊤ : Y.Opens) = ⨆ b, UY b) :
    (⊤ : (YRκ g R 𝔮).Opens) = ⨆ b, UYκ g R 𝔮 UY b :=
  iSup_UXκ g R 𝔮 UY hUY

end Cover

end AlgebraicGeometry.Cube.Openness

end

end
