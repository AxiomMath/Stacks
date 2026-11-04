module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechBasisMap
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocalQuasiIso

/-!
# The sections of `basisMap` over an affine étale scheme

Let `S` be affine, `f : X ⟶ S`, `U` a finite family of opens of `X` with affine finite
intersections, and `T ⟶ S` an affine étale `S`-scheme. On the sections over `T`, the morphism
`Stacks.ArtinSchreier.basisMap` given by cocycles `zᵢ` is, up to isomorphism, the extension of
scalars along `Γ(S) ⟶ Γ(T)` of `Stacks.ArtinSchreier.moduleBasisMap`.

## Main results

* `Stacks.ArtinSchreier.quasiIsoAt_sections_basisMap`: the sections of `basisMap` over `T` are a
  quasi-isomorphism in degree `q` when `moduleBasisMap` is and `Γ(S) ⟶ Γ(T)` is flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.ArtinSchreier

section Generic

/-- A finite sum of morphisms of additive groups, evaluated at `b`, is the sum of the values. -/
theorem addCommGrpCat_sum_apply {M N : AddCommGrpCat.{u + 1}} {κ : Type*} (s : Finset κ)
    (g : κ → (M ⟶ N)) (b : M) : (∑ i ∈ s, g i) b = ∑ i ∈ s, g i b :=
  map_sum (AddMonoidHom.mk' (fun g : M ⟶ N => g b) (fun _ _ => rfl)) g s

/-- `ULift.down` of a finite sum is the sum of the `ULift.down`s. -/
theorem ulift_down_sum {M : Type*} [AddCommMonoid M] {κ : Type*} (s : Finset κ)
    (g : κ → ULift.{u + 1} M) : (∑ i ∈ s, g i).down = ∑ i ∈ s, (g i).down :=
  map_sum (AddEquiv.ulift (α := M)) g s

/-- The component at `V` of a finite sum of morphisms of sheaves, evaluated at `b`, is the sum of
the values of the components. -/
theorem sheafHom_sum_app {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {κ : Type*} (s : Finset κ) (g : κ → (F ⟶ G)) (V : S.Etaleᵒᵖ) (b : F.obj.obj V) :
    (∑ i ∈ s, g i).hom.app V b = ∑ i ∈ s, (g i).hom.app V b :=
  map_sum (AddMonoidHom.mk' (fun g : F ⟶ G => g.hom.app V b) (fun _ _ => rfl)) g s

end Generic

variable {X S : Scheme.{u}} (f : X ⟶ S) {T : Scheme.{u}} (t : T ⟶ S) {ι : Type} [Finite ι]
  (U : ι → X.Opens) [IsAffine S] [IsAffine T]
  (hU : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffineOpen (inter U x))

/-- The components of the base-change isomorphism of Čech complexes. -/
theorem cechFibreBaseChangeIso_hom_f_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    (cechFibreBaseChangeIso f t U hU).hom.f n ≫ π U (fibreSectionsPresheaf f t) n x =
      (ModuleCat.extendScalars.{u, u, u} t.appTop.hom).map (π U (baseSectionsPresheaf f) n x) ≫
        (fibreBaseChange f t).app (op (inter U x)) := by
  have : (ModuleCat.extendScalars.{u, u, u} t.appTop.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} t.appTop.hom).left_adjoint_additive
  show ((mapCechIso (ModuleCat.extendScalars.{u, u, u} t.appTop.hom) U
      (baseSectionsPresheaf f)).hom.f n ≫ ((cechComplexFunctor U).map (fibreBaseChange f t)).f n) ≫
    π U (fibreSectionsPresheaf f t) n x = _
  rw [Category.assoc, Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π,
    ← Category.assoc, mapCechIso_hom_f_comp_π]

variable {r q : ℕ} (z : Fin r → (baseCech f U).X q)

/-- The basis vector `1 ⊗ eᵢ` of `Γ(T) ⊗_{Γ(S)} Γ(S)^r`. -/
abbrev oneTmulBasis (r : ℕ) (i : Fin r) :
    (ModuleCat.extendScalars.{u, u, u} t.appTop.hom).obj (ModuleCat.of Γ(S, ⊤) (Fin r → Γ(S, ⊤))) :=
  (1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤), t.appTop.hom] (Pi.single i (1 : Γ(S, ⊤)) : Fin r → Γ(S, ⊤))

/-- `b ↦ ∑ᵢ bᵢ (1 ⊗ eᵢ)`, the inverse of the identification `Γ(T) ⊗_{Γ(S)} Γ(S)^r ≅ Γ(T)^r`. -/
theorem baseChangeTermEquiv_symm_apply (b : Fin r → Γ(T, ⊤)) :
    (Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv t.appTop.hom r).symm b =
      ∑ i, b i • oneTmulBasis t r i := by
  rw [LinearEquiv.symm_apply_eq, map_sum]
  refine (funext fun k => ?_ : _ = _).symm
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]
  have h : ∀ i, (Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv t.appTop.hom r)
      (oneTmulBasis t r i) = Pi.single i 1 := fun i => by
    let := t.appTop.hom.toAlgebra
    refine (Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv_tmul t.appTop.hom r 1 _).trans ?_
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  simp only [h, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne' hj, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]

/-- The sections of `𝐆_a^r` over `T` are the base change of `Γ(S)^r`. -/
def freeSectionsIso (V' : S.Etale) (r : ℕ) :
    (freeAdditiveSheaf S r).obj.obj (op V') ≅
      (moduleCoefficients Γ(V'.left, ⊤)).obj
        ((ModuleCat.extendScalars.{u, u, u} V'.hom.appTop.hom).obj
          (ModuleCat.of Γ(S, ⊤) (Fin r → Γ(S, ⊤)))) :=
  AddEquiv.toAddCommGrpIso
    { toFun := fun b => ULift.up
        ((Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv V'.hom.appTop.hom r).symm b.down)
      invFun := fun w => ULift.up
        ((Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv V'.hom.appTop.hom r) w.down)
      left_inv := fun _ => ULift.ext _ _ (LinearEquiv.apply_symm_apply _ _)
      right_inv := fun _ => ULift.ext _ _ (LinearEquiv.symm_apply_apply _ _)
      map_add' := fun b b' => ULift.ext _ _ (map_add _ b.down b'.down) }

/-- The sections over `V'` of the presheaf `V ↦ f_*(ι_{V,*} 𝐆_{a,V})` are the `Γ(V')`-modules
`Γ((V' ×_S X) ×_X V)`. -/
def directImageSectionsIso (V' : S.Etale) :
    openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f ⋙ etaleSections S V' ≅
      fibreSectionsPresheaf f V'.hom ⋙ moduleCoefficients.{u} Γ(V'.left, ⊤) :=
  (sectionsModulePresheafIso (pullback.snd V'.hom f) (pullback.fst V'.hom f)).symm

/-- The component of `basisMapDeg` at the index `x` is `∑ᵢ prᵢ ≫ multMap cᵢ`, where `prᵢ` is the
`i`-th projection of `𝐆_a^r` and `cᵢ` the `x`-component of `zᵢ`. -/
theorem basisMapDeg_comp_π (x : Fin (q + 1) → ι) :
    basisMapDeg f U z ≫ π U _ q x =
      ∑ i, freeAdditiveProj S r i ≫
        multMap f (inter U x) (π U (baseSectionsPresheaf f) q x (z i)) := by
  rw [basisMapDeg, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, cochainMult_comp_π]
  rfl

/-- On sections over `V'`, the component of `basisMapDeg` at the index `x` sends `b` to
`∑ᵢ multFun cᵢ (bᵢ)`, where `cᵢ` is the `x`-component of `zᵢ`. -/
theorem basisMapDeg_comp_π_app (x : Fin (q + 1) → ι) (V' : S.Etale)
    (b : (freeAdditiveSheaf S r).obj.obj (op V')) :
    ((basisMapDeg f U z ≫ π U _ q x).hom.app (op V') b).down =
      ∑ i, multFun f (inter U x) (π U (baseSectionsPresheaf f) q x (z i)) V'.hom (b.down i) :=
  (congrArg (fun g => (g.hom.app (op V') b).down) (basisMapDeg_comp_π f U z x)).trans
    ((congrArg ULift.down (sheafHom_sum_app _ _ (op V') b)).trans
      (ulift_down_sum
        (M := ↑((pullback (pullback.snd V'.hom f) (inter U x).ι).presheaf.obj (op ⊤))) _ _))

/-- The base change along `Γ(S) ⟶ Γ(T)` of the component of `moduleBasisMapDeg` at the index `x`,
followed by `fibreBaseChange`, sends the element of `Γ(T) ⊗_{Γ(S)} Γ(S)^r` corresponding to
`b ∈ Γ(T)^r` to `∑ᵢ multFun cᵢ (bᵢ)`, where `cᵢ` is the `x`-component of `zᵢ`. -/
theorem moduleBasisMapDeg_comp_π_fibreBaseChange_apply (x : Fin (q + 1) → ι)
    (b : Fin r → Γ(T, ⊤)) :
    ((ModuleCat.extendScalars.{u, u, u} t.appTop.hom).map
        (moduleBasisMapDeg f U z ≫ π U (baseSectionsPresheaf f) q x) ≫
          (fibreBaseChange f t).app (op (inter U x)))
        ((Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv t.appTop.hom r).symm b) =
      ∑ i, multFun f (inter U x) (π U (baseSectionsPresheaf f) q x (z i)) t (b i) := by
  rw [baseChangeTermEquiv_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  show b i • (fibreBaseChange f t).app (op (inter U x))
    ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤), t.appTop.hom]
      (π U (baseSectionsPresheaf f) q x (moduleBasisMapDeg f U z
        (Pi.single i (1 : Γ(S, ⊤)) : Fin r → Γ(S, ⊤))))) = _
  rw [moduleBasisMapDeg_single, fibreBaseChange_app_one_tmul]
  rfl

/-- **In degree `q`, the sections of `basisMap` over an affine étale `V'` are the base change of
`moduleBasisMap`.** -/
theorem sections_basisMapDeg_comp (V' : S.Etale) [IsAffine ((𝟭 Scheme.{u}).obj V'.left)] :
    (etaleSections S V').map (basisMapDeg f U z) ≫
      (mapCechIso (etaleSections S V') U
        (openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f)).hom.f q ≫
        ((cechComplexFunctor U).map (directImageSectionsIso f V').hom).f q =
    (freeSectionsIso V' r).hom ≫
      (moduleCoefficients Γ(V'.left, ⊤)).map
        ((ModuleCat.extendScalars.{u, u, u} V'.hom.appTop.hom).map (moduleBasisMapDeg f U z) ≫
          (cechFibreBaseChangeIso f V'.hom U hU).hom.f q) ≫
        (mapCechIso (moduleCoefficients Γ(V'.left, ⊤)) U
          (fibreSectionsPresheaf f V'.hom)).hom.f q := by
  refine hom_ext U _ fun x => ?_
  have h1 := Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π U
    (directImageSectionsIso f V').hom q x
  have h2 := mapCechIso_hom_f_comp_π (etaleSections S V') U
    (openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f) q x
  have h3 := mapCechIso_hom_f_comp_π (moduleCoefficients Γ(V'.left, ⊤)) U
    (fibreSectionsPresheaf f V'.hom) q x
  have h4 := cechFibreBaseChangeIso_hom_f_comp_π f V'.hom U hU q x
  have eL : (etaleSections S V').map (basisMapDeg f U z) ≫
      (mapCechIso (etaleSections S V') U
        (openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f)).hom.f q ≫
        ((cechComplexFunctor U).map (directImageSectionsIso f V').hom).f q ≫ π U _ q x =
      (etaleSections S V').map (basisMapDeg f U z ≫ π U _ q x) ≫
        (directImageSectionsIso f V').hom.app (op (inter U x)) :=
    (congrArg ((etaleSections S V').map (basisMapDeg f U z) ≫ ·)
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (directImageSectionsIso f V').hom.app (op (inter U x))) h2)))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (directImageSectionsIso f V').hom.app (op (inter U x)))
          ((etaleSections S V').map_comp _ _).symm))
  have eR : (freeSectionsIso V' r).hom ≫
      (moduleCoefficients Γ(V'.left, ⊤)).map
        ((ModuleCat.extendScalars.{u, u, u} V'.hom.appTop.hom).map (moduleBasisMapDeg f U z) ≫
          (cechFibreBaseChangeIso f V'.hom U hU).hom.f q) ≫
        (mapCechIso (moduleCoefficients Γ(V'.left, ⊤)) U (fibreSectionsPresheaf f V'.hom)).hom.f q ≫
          π U _ q x =
      (freeSectionsIso V' r).hom ≫ (moduleCoefficients Γ(V'.left, ⊤)).map
        ((ModuleCat.extendScalars.{u, u, u} V'.hom.appTop.hom).map
          (moduleBasisMapDeg f U z ≫ π U (baseSectionsPresheaf f) q x) ≫
            (fibreBaseChange f V'.hom).app (op (inter U x))) := by
    congr 1
    rw [h3, ← Functor.map_comp, Category.assoc, h4, ← Category.assoc, ← Functor.map_comp]
  refine eL.trans (Eq.trans ?_ eR.symm)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext _ _ ?_)
  exact (basisMapDeg_comp_π_app f U z x V' b).trans
    (moduleBasisMapDeg_comp_π_fibreBaseChange_apply f V'.hom U z x b.down).symm

open Stacks.QuasiIsoFromSingle in
include hU in
/-- **Over an affine étale `S`-scheme `V'` with `Γ(S) ⟶ Γ(V')` flat, the sections of `basisMap`
are a quasi-isomorphism in degree `q`** when `moduleBasisMap` is. -/
theorem quasiIsoAt_sections_basisMap (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)
    (V' : S.Etale) [IsAffine ((𝟭 Scheme.{u}).obj V'.left)] (hflat : V'.hom.appTop.hom.Flat)
    (hT : QuasiIsoAt (moduleBasisMap f U z hz) q) :
    QuasiIsoAt (((etaleSections S V').mapHomologicalComplex _).map (basisMap f U z hz)) q := by
  let E := ModuleCat.extendScalars.{u, u, u} V'.hom.appTop.hom
  let MC := moduleCoefficients Γ(V'.left, ⊤)
  have : E.Additive := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).left_adjoint_additive
  have : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have : PreservesFiniteColimits E :=
    ModuleCat.extendScalars_preservesFiniteColimits.{u, u, u} V'.hom.appTop.hom
  have : E.PreservesHomology := Functor.preservesHomologyOfExact E
  have : MC.PreservesHomology := Functor.preservesHomologyOfExact MC
  have h1 : QuasiIsoAt ((E.mapHomologicalComplex _).map (moduleBasisMap f U z hz)) q :=
    HomologicalComplex.quasiIsoAt_map_of_preservesHomology _ E q
  have h2 : QuasiIsoAt ((MC.mapHomologicalComplex _).map
      ((E.mapHomologicalComplex _).map (moduleBasisMap f U z hz) ≫
        (cechFibreBaseChangeIso f V'.hom U hU).hom) ≫
      (mapCechIso MC U (fibreSectionsPresheaf f V'.hom)).hom) q := by
    have := HomologicalComplex.quasiIsoAt_map_of_preservesHomology
      ((E.mapHomologicalComplex _).map (moduleBasisMap f U z hz) ≫
        (cechFibreBaseChangeIso f V'.hom U hU).hom) MC q
    infer_instance
  have hMD : ∀ k, (ComplexShape.up ℕ).Rel q k →
      moduleBasisMapDeg f U z ≫ (baseCech f U).d q k = 0 := fun k hk => by
    obtain rfl : q + 1 = k := hk
    exact moduleBasisMapDeg_comp_d f U z hz
  have e2 := map_map_mkHomFromSingle_comp (moduleBasisMapDeg f U z) hMD E MC
    (cechFibreBaseChangeIso f V'.hom U hU).hom
    (mapCechIso MC U (fibreSectionsPresheaf f V'.hom)).hom
  have h2' := (congrArg (fun g => QuasiIsoAt g q) e2).mp h2
  have h3 := (quasiIsoAt_iff_comp_left _ _ q).1 ((quasiIsoAt_iff_comp_left _ _ q).1 h2')
  let eS := etaleSections S V'
  let iT := mapCechIso eS U (openDirectImagePresheaf X ⋙ etaleAbelianDirectImage.{u, 0} f) ≪≫
    (cechComplexFunctor U).mapIso (directImageSectionsIso f V')
  have hbMD : ∀ k, (ComplexShape.up ℕ).Rel q k →
      basisMapDeg f U z ≫ (directImageCech f U).d q k = 0 := fun k hk => by
    obtain rfl : q + 1 = k := hk
    exact basisMapDeg_comp_d f U z hz
  have hpf : ∀ k, (ComplexShape.up ℕ).Rel q k →
      eS.map (basisMapDeg f U z) ≫ ((eS.mapHomologicalComplex _).obj (directImageCech f U)).d q k =
        0 := fun k hk => by
    rw [Functor.mapHomologicalComplex_obj_d, ← eS.map_comp, hbMD k hk, eS.map_zero]
  have eq1 : (eS.mapHomologicalComplex _).map (basisMap f U z hz) =
      (HomologicalComplex.singleMapHomologicalComplex eS _ q).hom.app _ ≫
        HomologicalComplex.mkHomFromSingle (eS.map (basisMapDeg f U z)) hpf :=
    map_mkHomFromSingle (basisMapDeg f U z) hbMD eS
  have eq2 := mkHomFromSingle_comp (eS.map (basisMapDeg f U z)) hpf iT.hom
  have eq3 : eS.map (basisMapDeg f U z) ≫ iT.hom.f q = (freeSectionsIso V' r).hom ≫
      ((MC.map (E.map (moduleBasisMapDeg f U z) ≫ (cechFibreBaseChangeIso f V'.hom U hU).hom.f q) ≫
        (mapCechIso MC U (fibreSectionsPresheaf f V'.hom)).hom.f q)) :=
    sections_basisMapDeg_comp f U hU z V'
  have eq4 := single_map_comp_mkHomFromSingle
    ((MC.map (E.map (moduleBasisMapDeg f U z) ≫ (cechFibreBaseChangeIso f V'.hom U hU).hom.f q) ≫
        (mapCechIso MC U (fibreSectionsPresheaf f V'.hom)).hom.f q))
    (fun k hk => map_map_comp_d_eq_zero (moduleBasisMapDeg f U z) hMD E MC _ _ k hk)
    (freeSectionsIso V' r).hom
  have hmk : ∀ {A' : AddCommGrpCat.{u + 1}} {L' : CochainComplex AddCommGrpCat.{u + 1} ℕ}
      (φ₁ φ₂ : A' ⟶ L'.X q) (h : φ₁ = φ₂) (pf₁ pf₂),
      HomologicalComplex.mkHomFromSingle φ₁ pf₁ = HomologicalComplex.mkHomFromSingle φ₂ pf₂ := by
    rintro _ _ _ _ rfl _ _; rfl
  have h4 := (quasiIsoAt_iff_comp_left
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) q).map (freeSectionsIso V' r).hom) _ q).2 h3
  have h4a := (congrArg (fun g => QuasiIsoAt g q) eq4).mp h4
  have h4b := (congrArg (fun g => QuasiIsoAt g q) (hmk _ _ eq3.symm _ (fun k hk => by
      rw [Category.assoc, iT.hom.comm, ← Category.assoc, hpf k hk, zero_comp]))).mp h4a
  have h4 := (congrArg (fun g => QuasiIsoAt g q) eq2).mpr h4b
  have h5 := (quasiIsoAt_iff_comp_right _ iT.hom q).1 h4
  have h6 := (quasiIsoAt_iff_comp_left
    ((HomologicalComplex.singleMapHomologicalComplex eS _ q).hom.app _) _ q).2 h5
  exact (congrArg (fun g => QuasiIsoAt g q) eq1).mpr h6

/-- **The affine étale `S`-schemes cover every étale `S`-scheme.** -/
theorem coversByProperty_isAffine (S : Scheme.{u}) :
    Stacks.Sites.CoversByProperty (fun V : S.Etale => IsAffine ((𝟭 Scheme.{u}).obj V.left))
      S.smallEtaleTopology := by
  intro W
  let C := W.left.affineCover
  let Z : C.I₀ → S.Etale := fun i => Scheme.Etale.mk (C.f i ≫ W.hom)
  let a : ∀ i, Z i ⟶ W := fun i => MorphismProperty.Over.homMk (C.f i) rfl
  have hcov : Sieve.ofArrows Z a ∈ S.smallEtaleTopology W := by
    refine (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 (Set.eq_univ_of_forall fun x => ?_)
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  refine S.smallEtaleTopology.superset_covering ?_ hcov
  rintro V b ⟨_, g, _, ⟨i⟩, rfl⟩
  refine ⟨Z i, g, a i, ?_, rfl⟩
  show IsAffine (C.X i)
  infer_instance

include hU in
/-- **The cocycles `zᵢ` exhibit `𝐆_a^r[-q]` as quasi-isomorphic in degree `q` to the Čech complex
of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})`**, for `S` affine, a finite family of opens with affine finite
intersections, and cocycles whose classes form a basis of the degree-`q` Čech cohomology of
`V ↦ Γ((S ×_S X) ×_X V)` over `Γ(S)`. -/
theorem quasiIsoAt_basisMap (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)
    (hT : QuasiIsoAt (moduleBasisMap f U z hz) q) :
    QuasiIsoAt (basisMap f U z hz) q :=
  Stacks.Sites.quasiIsoAt_of_quasiIsoAt_sections (coversByProperty_isAffine S)
    (basisMap f U z hz) q fun W hW => by
      have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := hW
      have : IsAffine W.left := hW
      have : IsAffine ((Functor.fromPUnit S).obj W.right) := ‹IsAffine S›
      exact quasiIsoAt_sections_basisMap f U hU z hz W
        (HasRingHomProperty.appTop (P := @Flat) W.hom inferInstance) hT

end Stacks.ArtinSchreier

end
