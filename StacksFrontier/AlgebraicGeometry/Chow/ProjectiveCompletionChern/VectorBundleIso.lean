module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapSections
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The morphism `C ⟶ 𝐕(𝒞)` and its rings of functions

The morphism of modules `𝒞 ⟶ (C ⟶ X)_* 𝒪_C`, `m ↦ m / T`, corresponds by the universal property of
`𝐕(𝒞) = Spec_X(Sym^*(𝒞))` to a morphism `C ⟶ 𝐕(𝒞)` over `X`. Over an affine open `V` of `X` it acts
on functions by a ring map `Sym_R(M) ⟶ Γ(C ∩ π⁻¹V)` sending `m` to `m / T`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.toVectorBundle`: the morphism `C ⟶ 𝐕(𝒞)` over `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- A finite locally free `𝒪_X`-module `𝒞` is quasi-coherent. -/
instance isQuasicoherent_C : 𝒞.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

/-- **The morphism `C ⟶ 𝐕(𝒞)` over `X`** classified by `m ↦ m / T`. -/
def toVectorBundle :
    Over.mk (openToBase 𝒞) ⟶ Scheme.Modules.vectorBundleOver X (F := 𝒞) :=
  (Scheme.Modules.vectorBundleHomEquiv 𝒞 (Over.mk (openToBase 𝒞))).symm (nu 𝒞 r)

/-- Under the universal property of `𝐕(𝒞)`, the morphism `toVectorBundle` corresponds to `nu`,
the module map `m ↦ m / T`. -/
theorem vectorBundleHomEquiv_toVectorBundle :
    Scheme.Modules.vectorBundleHomEquiv 𝒞 (Over.mk (openToBase 𝒞)) (toVectorBundle 𝒞 r) =
      nu 𝒞 r :=
  Equiv.apply_symm_apply _ _

/-- The ring map `Γ(V, Sym(𝒞)) ⟶ Γ(C ∩ π⁻¹V)` induced by `C ⟶ 𝐕(𝒞)`. -/
def toVectorBundleRing (V : X.Opens) :
    (Scheme.Modules.symmetricAlgebraSheaf X 𝒞).right.obj.obj (op V) ⟶
      Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) :=
  haveI := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  ((Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv ≫
    pushforwardAlgebraMap (toVectorBundle 𝒞 r)).right.hom.app (op V)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- The comparison of the two ungraded realizations of `Sym(𝒞)` on a homogeneous local section. -/
theorem symmetricAlgebraSheafComparison_hom_ungradedAlgebraSheafIncl (V : X.Opens) (n : ℤ)
    (x : ((Scheme.Modules.symmetricAlgebra X 𝒞).piece n).val.obj (op V)) :
    (((Scheme.Modules.symmetricAlgebraSheafComparison 𝒞).hom.right.hom.app (op V)).hom
        (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X _ _ n V x)) =
      (Scheme.Modules.symmetricAlgebra X 𝒞).ungradedIncl n x :=
  congrArg (fun φ : (Scheme.Modules.symmetricAlgebra X 𝒞).toPresheafGradedAlgebra.totalPresheaf ⟶
      ((Scheme.Modules.symmetricAlgebra X 𝒞).toPresheafGradedAlgebra.totalSheaf
        (Opens.grothendieckTopology (X : TopCat))).obj =>
        ConcreteCategory.hom (φ.app (op V))
          ((Scheme.Modules.symmetricAlgebra X 𝒞).toPresheafGradedAlgebra.incl n x))
    (Stacks.RelativeSpec.ungradedRingUnit_comp_ringSheafIsoUngradedSheaf_inv X
      (Scheme.Modules.symmetricAlgebra X 𝒞) (Scheme.Modules.symmetricAlgebra_mul_comm X 𝒞))

/-- **`C ⟶ 𝐕(𝒞)` on the generators**: the section `m` of `𝒞`, read in `Γ(V, Sym(𝒞))`, goes to
`m / T`. -/
theorem toVectorBundleRing_ungradedIncl (V : X.Opens) (m : Γ(𝒞, V)) :
    toVectorBundleRing 𝒞 r V ((Scheme.Modules.symmetricAlgebra X 𝒞).ungradedIncl 1
        (((Scheme.Modules.symmetricAlgebraGen X 𝒞).val.app (op V)) m)) =
      Scheme.Modules.Hom.app (nu 𝒞 r) V m := by
  have h3 := congrArg (fun φ => (SheafOfModules.Hom.val φ).app (op V) m)
    ((Scheme.Modules.vectorBundleHomEquiv_apply 𝒞 (Over.mk (openToBase 𝒞))
      (toVectorBundle 𝒞 r)).symm.trans (vectorBundleHomEquiv_toVectorBundle 𝒞 r))
  refine Eq.trans ?_ h3
  change _ = ((((Scheme.Modules.symmetricAlgebraSheafComparison 𝒞).hom ≫
    (Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv ≫
      pushforwardAlgebraMap (toVectorBundle 𝒞 r)).right.hom.app (op V)).hom
    (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X _ _ 1 V
      (((Scheme.Modules.symmetricAlgebraGen X 𝒞).val.app (op V)) m)))
  rw [← symmetricAlgebraSheafComparison_hom_ungradedAlgebraSheafIncl]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- The structure map of `f_* 𝒪` is the pullback of functions. -/
theorem pushforwardAlgebra_hom_app {Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens) (c : Γ(X, V)) :
    ((pushforwardAlgebra f).hom.hom.app (op V)).hom c = f.app V c := rfl

/-- `toVectorBundleRing` is the pullback of functions along `toVectorBundle`, precomposed with
the identification of `Sym(𝒞)` with the pushforward of the functions on `𝐕(𝒞)`. -/
theorem toVectorBundleRing_apply (V : X.Opens)
    (x : (Scheme.Modules.symmetricAlgebraSheaf X 𝒞).right.obj.obj (op V)) :
    haveI := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
    toVectorBundleRing 𝒞 r V x =
      ((pushforwardAlgebraMap (toVectorBundle 𝒞 r)).right.hom.app (op V)).hom
        (((Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv.right.hom.app (op V)).hom x) :=
  rfl

/-- **`C ⟶ 𝐕(𝒞)` is a morphism over `X`**, read on functions: the structure map of `Sym(𝒞)` goes to
the pullback of functions along `C ⟶ X`. -/
theorem toVectorBundleRing_structure (V : X.Opens) (c : Γ(X, V)) :
    toVectorBundleRing 𝒞 r V
        (((Scheme.Modules.symmetricAlgebraSheaf X 𝒞).hom.hom.app (op V)).hom c) =
      (openToBase 𝒞).app V c := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  rw [toVectorBundleRing_apply]
  have h1 : ((Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv.right.hom.app (op V)).hom
      (((Scheme.Modules.symmetricAlgebraSheaf X 𝒞).hom.hom.app (op V)).hom c) =
      (Scheme.Modules.vectorBundleToBase X 𝒞).app V c :=
    congrArg (fun φ : X.sheaf ⟶
        (pushforwardAlgebra (Scheme.Modules.vectorBundleToBase X 𝒞)).right =>
      (φ.hom.app (op V)).hom c) (Under.w (Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)).inv)
  rw [h1, pushforwardAlgebraMap_app (toVectorBundle 𝒞 r) V
    (preimage_le_preimage_preimage (toVectorBundle 𝒞 r) V)]
  have hw : (toVectorBundle 𝒞 r).left ≫ Scheme.Modules.vectorBundleToBase X 𝒞 = openToBase 𝒞 :=
    Over.w (toVectorBundle 𝒞 r)
  have h3 : ((toVectorBundle 𝒞 r).left ≫ Scheme.Modules.vectorBundleToBase X 𝒞).appLE V
      (openToBase 𝒞 ⁻¹ᵁ V) (preimage_le_preimage_preimage (toVectorBundle 𝒞 r) V) =
      (openToBase 𝒞).app V := by
    rw [← Scheme.Hom.appLE_eq_app]
    congr 1
  exact congrArg (fun φ => φ c) ((Scheme.Hom.comp_appLE (toVectorBundle 𝒞 r).left
    (Scheme.Modules.vectorBundleToBase X 𝒞) V (openToBase 𝒞 ⁻¹ᵁ V)
    (preimage_le_preimage_preimage (toVectorBundle 𝒞 r) V)).symm.trans h3)

/-! ### Over an affine open with `𝒞` free -/

section Affine

variable {V : X.Opens} (hV : IsAffineOpen V)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- The image in the projective completion of `C ∩ π⁻¹V` is the open `openW 𝒞 hV`. -/
theorem image_preimage_openToBase_eq :
    (openT 𝒞).ι ''ᵁ (openToBase 𝒞 ⁻¹ᵁ V) = openW 𝒞 hV := by
  rw [openW_eq]
  refine (Scheme.Hom.image_preimage_eq_opensRange_inf (openT 𝒞).ι (proj 𝒞 ⁻¹ᵁ V)).trans ?_
  rw [Scheme.Opens.opensRange_ι]

/-- **On `W`, the function `m / T` is the coordinate `y_m`.** -/
theorem divT_eq_coordY (m : Γ(𝒞, V)) :
    divT 𝒞 r V m = (space 𝒞).presheaf.map
      (homOfLE (image_preimage_openToBase_eq 𝒞 hV).le).op (coordY 𝒞 hV m) := by
  refine (eq_divT 𝒞 r ?_).symm
  set sT := ((twistData 𝒞).ψ 1).val.app (op V)
    ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
      ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞)))
  have hψ : (twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op (psiInl 𝒞 V m) =
      coordY 𝒞 hV m • (twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op sT :=
    psi_restrict_openW 𝒞 hV m
  have hT : (twist 𝒞).presheaf.map (homOfLE (le_top : openW 𝒞 hV ≤ ⊤)).op (coordT 𝒞) =
      (twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op sT :=
    coordT_restrict_openW 𝒞 hV
  have hc : ∀ {A B C : (space 𝒞).Opens} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      (twist 𝒞).presheaf.map (homOfLE hAC).op =
        (twist 𝒞).presheaf.map (homOfLE hBC).op ≫ (twist 𝒞).presheaf.map (homOfLE hAB).op := by
    intros
    rw [← Functor.map_comp]
    rfl
  rw [hc (image_preimage_openToBase_eq 𝒞 hV).le le_top le_top,
    hc (image_preimage_openToBase_eq 𝒞 hV).le (openW_le 𝒞 hV) (image_preimage_le_proj 𝒞 V),
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hT, hψ,
    Scheme.Modules.map_smul]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- The functions on `W` are the functions on `C ∩ π⁻¹V`, read on the open subscheme `C`. -/
def kappa : Γ(space 𝒞, openW 𝒞 hV) ≃+* Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) :=
  ((space 𝒞).presheaf.mapIso
      (eqToIso (image_preimage_openToBase_eq 𝒞 hV)).op).commRingCatIsoToRingEquiv.trans
    ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ V)).commRingCatIsoToRingEquiv

/-- `kappa` sends the coordinate `y_m` on `W` to the function `m / T` on `C ∩ π⁻¹V`. -/
theorem kappa_coordY (m : Γ(𝒞, V)) :
    kappa 𝒞 hV (coordY 𝒞 hV m) = Scheme.Modules.Hom.app (nu 𝒞 r) V m := by
  rw [nu_app, divT_eq_coordY 𝒞 r hV]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- `kappa` sends the pullback to `W` of a function `c` on `V` to the pullback of `c` along
`C ⟶ X`. -/
theorem kappa_proj_app (c : Γ(X, V)) :
    kappa 𝒞 hV ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ((proj 𝒞).app V c)) =
      (openToBase 𝒞).app V c := by
  have h1 : kappa 𝒞 hV ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op
      ((proj 𝒞).app V c)) =
      ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ V)).hom (resC 𝒞 V ((proj 𝒞).app V c)) := by
    change ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ V)).hom
      ((space 𝒞).presheaf.map (eqToHom (image_preimage_openToBase_eq 𝒞 hV)).op
        ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ((proj 𝒞).app V c))) = _
    refine congrArg (fun z => ((openT 𝒞).ι.appIso (openToBase 𝒞 ⁻¹ᵁ V)).hom z) ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [h1, appIso_hom_resC, Scheme.Hom.comp_app]
  rfl

/-- The ring map `Sym_R(M) ⟶ Γ(C ∩ π⁻¹V)` induced by `C ⟶ 𝐕(𝒞)`. -/
def theta : SymmetricAlgebra Γ(X, V) Γ(𝒞, V) →+* Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) :=
  (toVectorBundleRing 𝒞 r V).hom.comp (Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV).toRingHom

/-- `theta` sends a generator `m` of `Sym_R(M)` to `kappa` of the coordinate `y_m`. -/
theorem theta_ι (m : Γ(𝒞, V)) :
    theta 𝒞 r hV (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m) = kappa 𝒞 hV (coordY 𝒞 hV m) := by
  rw [kappa_coordY 𝒞 r hV, theta, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl]
  exact toVectorBundleRing_ungradedIncl 𝒞 r V m

/-- `theta` sends a scalar `c ∈ R` to `kappa` of the pullback of `c` to `W`. -/
theorem theta_algebraMap (c : Γ(X, V)) :
    theta 𝒞 r hV (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) c) =
      kappa 𝒞 hV ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ((proj 𝒞).app V c)) := by
  rw [kappa_proj_app, theta, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap]
  exact toVectorBundleRing_structure 𝒞 r V c

/-- **`C ⟶ 𝐕(𝒞)` is an isomorphism over `V` on functions**: `theta` is inverse to the
identification `Γ(C ∩ π⁻¹V) ≅ Γ(W) ≅ Sym_R(M)`. -/
theorem coordRingEquiv_kappa_symm_theta (a : SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) :
    coordRingEquiv 𝒞 hV ((kappa 𝒞 hV).symm (theta 𝒞 r hV a)) = a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap c =>
    rw [theta_algebraMap, RingEquiv.symm_apply_apply, coordRingEquiv_proj_app]
  | ι m =>
    rw [theta_ι, RingEquiv.symm_apply_apply, coordRingEquiv_coordY]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The ring map `theta : Sym_R(M) ⟶ Γ(C ∩ π⁻¹V)` is bijective. -/
theorem bijective_theta : Function.Bijective (theta 𝒞 r hV) := by
  have hfun : (theta 𝒞 r hV : SymmetricAlgebra Γ(X, V) Γ(𝒞, V) → _) =
      kappa 𝒞 hV ∘ (coordRingEquiv 𝒞 hV).symm := funext fun a => by
    rw [Function.comp_apply, ← (RingEquiv.eq_symm_apply _).2
      (coordRingEquiv_kappa_symm_theta 𝒞 r hV a), RingEquiv.apply_symm_apply]
  rw [hfun]
  exact (kappa 𝒞 hV).bijective.comp (coordRingEquiv 𝒞 hV).symm.bijective

/-- `C ⟶ 𝐕(𝒞)` is bijective on functions over an affine open `V` of `X`. -/
theorem bijective_toVectorBundleRing (hV : IsAffineOpen V) :
    Function.Bijective (toVectorBundleRing 𝒞 r V) := by
  have hfun : (toVectorBundleRing 𝒞 r V : _ → _) = theta 𝒞 r hV ∘
      (Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV).symm := by
    funext x
    change _ = toVectorBundleRing 𝒞 r V
      ((Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV)
        ((Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV).symm x))
    rw [RingEquiv.apply_symm_apply]
  rw [hfun]
  exact (bijective_theta 𝒞 r hV).comp
    (Stacks.SymAlgSections.symSectionsRingEquiv 𝒞 hV).symm.bijective

end Affine

/-- **`C ⟶ 𝐕(𝒞)` is bijective on functions over every affine open `V` of `X`.** -/
theorem bijective_toVectorBundle_appLE {V : X.Opens} (hV : IsAffineOpen V)
    (hle : openToBase 𝒞 ⁻¹ᵁ V ≤
      (toVectorBundle 𝒞 r).left ⁻¹ᵁ (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V)) :
    Function.Bijective ((toVectorBundle 𝒞 r).left.appLE
      (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) (openToBase 𝒞 ⁻¹ᵁ V) hle) := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  set e := Scheme.Modules.vectorBundlePushforwardIso X (F := 𝒞)
  have hinv1 : ∀ x, (e.hom.right.hom.app (op V)).hom ((e.inv.right.hom.app (op V)).hom x) = x :=
    fun x => congrArg (fun φ => (φ.right.hom.app (op V)).hom x) e.inv_hom_id
  have hinv2 : ∀ x, (e.inv.right.hom.app (op V)).hom ((e.hom.right.hom.app (op V)).hom x) = x :=
    fun x => congrArg (fun φ => (φ.right.hom.app (op V)).hom x) e.hom_inv_id
  have hfun2 : ((toVectorBundle 𝒞 r).left.appLE
      (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) (openToBase 𝒞 ⁻¹ᵁ V) hle : _ → _) =
      (toVectorBundleRing 𝒞 r V) ∘ (e.hom.right.hom.app (op V)).hom := by
    funext x
    refine Eq.trans ?_ (toVectorBundleRing_apply 𝒞 r V _).symm
    refine Eq.trans ?_ (congrArg ((pushforwardAlgebraMap (toVectorBundle 𝒞 r)).right.hom.app
      (op V)).hom (hinv2 x).symm)
    exact congrArg (fun φ : Γ(Scheme.Modules.vectorBundle X 𝒞,
        Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) ⟶ Γ((openT 𝒞).toScheme, openToBase 𝒞 ⁻¹ᵁ V) =>
        φ.hom x) (pushforwardAlgebraMap_app (toVectorBundle 𝒞 r) V hle).symm
  rw [hfun2]
  exact (bijective_toVectorBundleRing 𝒞 r hV).comp
    ⟨Function.LeftInverse.injective hinv2, Function.RightInverse.surjective hinv1⟩

/-- The preimage under `C ⟶ 𝐕(𝒞)` of the part of `𝐕(𝒞)` over `V` is `C ∩ π⁻¹V`. -/
theorem preimage_toVectorBundle (V : X.Opens) :
    (toVectorBundle 𝒞 r).left ⁻¹ᵁ (Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V) =
      openToBase 𝒞 ⁻¹ᵁ V :=
  congrArg (· ⁻¹ᵁ V) (Over.w (toVectorBundle 𝒞 r))

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] in
/-- A morphism of affine schemes inducing an isomorphism on global sections is an
isomorphism. -/
theorem isIso_of_isAffine_of_isIso_appTop {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsAffine Y]
    [IsAffine Z] [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine f)).mpr (inferInstanceAs (IsIso (Spec.map f.appTop)))

/-- **`C = {T ≠ 0}` is the vector bundle `𝐕(𝒞) = Spec_X(Sym^*(𝒞))`**: the morphism `C ⟶ 𝐕(𝒞)`
over `X` given by `m ↦ m / T` is an isomorphism. -/
instance isIso_toVectorBundle : IsIso (toVectorBundle 𝒞 r).left := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := 𝒞)
  let U : X.affineOpens → (Scheme.Modules.vectorBundle X 𝒞).Opens := fun V =>
    Scheme.Modules.vectorBundleToBase X 𝒞 ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨V, hV, hzV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (U := (⊤ : X.Opens)) (x := Scheme.Modules.vectorBundleToBase X 𝒞 z) trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hzV⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre := preimage_toVectorBundle 𝒞 r V.1
  have hiso : IsIso ((toVectorBundle 𝒞 r).left.appLE (U V) (openToBase 𝒞 ⁻¹ᵁ V.1) hpre.ge) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toVectorBundle_appLE 𝒞 r V.2 hpre.ge)
  have happ : ((toVectorBundle 𝒞 r).left ∣_ U V).appTop =
      (toVectorBundle 𝒞 r).left.appLE ((U V).ι ''ᵁ ⊤)
        (((toVectorBundle 𝒞 r).left ⁻¹ᵁ U V).ι ''ᵁ ⊤)
        (image_morphismRestrict_preimage (toVectorBundle 𝒞 r).left (U V) ⊤).le :=
    morphismRestrict_app' _ _ ⊤
  have : IsIso ((toVectorBundle 𝒞 r).left ∣_ U V).appTop := by
    rw [happ]
    exact (Scheme.Hom.appLE_congr _ _ (Scheme.Opens.ι_image_top _)
      ((Scheme.Opens.ι_image_top _).trans hpre) (IsIso ·)).2 hiso
  have : IsAffine (U V).toScheme :=
    Scheme.Modules.isAffineOpen_preimage_vectorBundleToBase X 𝒞 V
  have h₁ : IsAffineOpen (openToBase 𝒞 ⁻¹ᵁ V.1) := by
    rw [← (openT 𝒞).ι.isAffineOpen_iff_of_isOpenImmersion, image_preimage_openToBase_eq 𝒞 V.2]
    exact isAffineOpen_openW 𝒞 V.2
  have : IsAffine ((toVectorBundle 𝒞 r).left ⁻¹ᵁ U V).toScheme := hpre ▸ h₁
  exact isIso_of_isAffine_of_isIso_appTop _

end Stacks.Chow.ProjectiveCompletion
