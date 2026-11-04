module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf

/-!
# Restriction to an open containing the support

Let `O, O'` be opens of a scheme `X` covering it, and let `Q` be a sheaf of modules restricting
to zero on `O'`. Then restriction to `O` is a bijection `Hom(P, Q) → Hom(P|_O, Q|_O)` for every
`P`. For a coherent adic system along an ideal sheaf `J` every term is killed by a power of `J`,
hence restricts to zero off the support of `J`; so restriction of coherent adic systems to an
open containing the support of `J` is fully faithful.

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_restrictFunctor_map_of_isZero_restrict`: the
  bijection above.
* `Stacks.Algebraization.isZero_restrict_of_idealPowerMultiple_eq_bot`: a module killed by
  `J ^ n` restricts to zero on every open disjoint from the support of `J`.
* `Stacks.Algebraization.bijective_whiskerRight_restrict_coherentAdicSystems`: restriction of
  coherent adic systems along `J` to an open containing the support of `J` is bijective on
  morphisms.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace AlgebraicGeometry.Scheme.Modules

/-- The image of the preimage of `T` under the inclusion of `O` is `O ⊓ T`. -/
private theorem image_preimage_ι_eq_inf {X : Scheme.{u}} (O T : X.Opens) :
    O.ι ''ᵁ O.ι ⁻¹ᵁ T = O ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- The sections of `Q` over an open `V ≤ O'` vanish when the restriction of `Q` to `O'` is
zero. -/
theorem eq_zero_of_isZero_restrict {X : Scheme.{u}} (O' : X.Opens) (Q : X.Modules)
    (hQ : IsZero (Q.restrict O'.ι)) {V : X.Opens} (hV : V ≤ O') (s : Γ(Q, V)) : s = 0 := by
  have hV' : O'.ι ''ᵁ (O'.ι ⁻¹ᵁ V) = V := by
    rw [image_preimage_ι_eq_inf]
    exact inf_eq_right.mpr hV
  let t : Γ(Q.restrict O'.ι, O'.ι ⁻¹ᵁ V) :=
    Q.presheaf.map (eqToHom hV').op s
  have ht : t = 0 := by
    have h := congrArg (fun φ : Q.restrict O'.ι ⟶ Q.restrict O'.ι => φ.app (O'.ι ⁻¹ᵁ V) t)
      (hQ.eq_of_src (𝟙 _) 0)
    simpa using h
  have : s = Q.presheaf.map (eqToHom hV'.symm).op t := by
    simp only [t, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  rw [this, ht]
  exact map_zero (Q.presheaf.map (eqToHom hV'.symm).op).hom

/-- **Morphisms into a module supported in an open are determined by their restriction.** If
`O ⊔ O' = X` and `Q` restricts to zero on `O'`, then restriction to `O` is a bijection
`Hom(P, Q) → Hom(P|_O, Q|_O)`. -/
theorem bijective_restrictFunctor_map_of_isZero_restrict {X : Scheme.{u}} (O O' : X.Opens)
    (hcov : O ⊔ O' = ⊤) (P Q : X.Modules) (hQ : IsZero (Q.restrict O'.ι)) :
    Function.Bijective (fun f : P ⟶ Q => (Scheme.Modules.restrictFunctor O.ι).map f) := by
  have hunit : IsIso ((restrictAdjunction O.ι).unit.app Q) := by
    rw [Hom.isIso_iff_isIso_app]
    intro T
    rw [restrictAdjunction_unit_app_app]
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
    let A : X.Opens := O.ι ''ᵁ O.ι ⁻¹ᵁ T
    let B : X.Opens := O' ⊓ T
    have hAT : A ≤ T := O.ι.image_preimage_le T
    have hBT : B ≤ T := inf_le_right
    have hA : A = O ⊓ T := image_preimage_ι_eq_inf O T
    have hcover : T ≤ A ⊔ B := by
      intro x hx
      have : x ∈ O ⊔ O' := hcov ▸ trivial
      rcases (Opens.mem_sup.mp this) with h | h
      · exact Opens.mem_sup.mpr (Or.inl (hA ▸ ⟨h, hx⟩))
      · exact Opens.mem_sup.mpr (Or.inr ⟨h, hx⟩)
    have hB : ∀ {V : X.Opens}, V ≤ B → ∀ s t : Γ(Q, V), s = t := fun hV s t =>
      (eq_zero_of_isZero_restrict O' Q hQ (hV.trans inf_le_left) s).trans
        (eq_zero_of_isZero_restrict O' Q hQ (hV.trans inf_le_left) t).symm
    let F : TopCat.Sheaf Ab.{u} X := ⟨Q.presheaf, Q.isSheaf⟩
    constructor
    · rw [injective_iff_map_eq_zero]
      intro s hs
      refine F.eq_of_locally_eq₂ (homOfLE hAT) (homOfLE hBT) hcover s 0 ?_ ?_
      · exact hs.trans (map_zero _).symm
      · exact hB le_rfl _ _
    · intro t₀
      let t : ToType (F.1.obj (op A)) := t₀
      let C : Bool → X.Opens := fun i => Bool.rec B A i
      let d : ∀ i, ToType (F.1.obj (op (C i))) := fun i =>
        Bool.rec (motive := fun i => ToType (F.1.obj (op (C i)))) 0 t i
      have hd : TopCat.Presheaf.IsCompatible F.1 C d := by
        intro i j
        cases i <;> cases j
        · exact hB inf_le_left _ _
        · exact hB inf_le_left _ _
        · exact hB inf_le_right _ _
        · exact congrArg (fun φ : op A ⟶ op (A ⊓ A) => F.1.map φ t) (Subsingleton.elim _ _)
      obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' C T
        (fun i => Bool.rec (motive := fun i => C i ⟶ T) (homOfLE hBT) (homOfLE hAT) i)
        (fun x hx => by
          rcases Opens.mem_sup.mp (hcover hx) with h | h
          · exact Opens.mem_iSup.mpr ⟨true, h⟩
          · exact Opens.mem_iSup.mpr ⟨false, h⟩) d hd
      exact ⟨g, hg true⟩
  have hfun : (fun f : P ⟶ Q => (Scheme.Modules.restrictFunctor O.ι).map f) =
      ((restrictAdjunction O.ι).homEquiv P (Q.restrict O.ι)).symm ∘
        ((Iso.refl P).homCongr (asIso ((restrictAdjunction O.ι).unit.app Q))) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv, asIso_hom,
      Category.id_comp]
    rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
    exact ((restrictAdjunction O.ι).unit.naturality f).symm
  rw [hfun]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

/-- A module all of whose sections over opens below `O'` vanish restricts to zero on `O'`. -/
theorem isZero_restrict_of_eq_zero {X : Scheme.{u}} (O' : X.Opens) (Q : X.Modules)
    (h : ∀ (V : X.Opens), V ≤ O' → ∀ s : Γ(Q, V), s = 0) : IsZero (Q.restrict O'.ι) := by
  refine IsZero.of_iso ?_ (Iso.refl _)
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  have hW : O'.ι ''ᵁ W ≤ O' := fun y ⟨w, _, hw⟩ => hw ▸ w.2
  exact (h _ hW _).trans (h _ hW _).symm

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Algebraization

open AlgebraicGeometry

/-- The zero subsheaf of `M` is the zero submodule over every open. -/
theorem bot_obj_schemeModules {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ) :
    (⊥ : M.Submodule).obj U = ⊥ :=
  SheafOfModules.Submodule.bot_obj M U

/-- An ideal sheaf is the unit ideal over an affine open disjoint from its support. -/
theorem ideal_eq_top_of_disjoint_support {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (hU : Disjoint (U.1 : Set X) J.support) : J.ideal U = ⊤ := by
  by_contra hne
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top] at hne
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hx : U.2.fromSpec p ∈ X.zeroLocus (U := U.1) (J.ideal U) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus]; exact ⟨p, hp, rfl⟩
  have hsupp : U.2.fromSpec p ∈ (J.support : Set X) ∩ U.1 := by
    rw [Scheme.IdealSheafData.coe_support_inter]; exact hx
  exact Set.disjoint_left.mp hU hsupp.2 hsupp.1

/-- **A module killed by a power of `J` vanishes off the support of `J`.** If `J ^ n Q = 0`, then
`Q` restricts to zero on every open disjoint from the support of `J`. -/
theorem isZero_restrict_of_idealPowerMultiple_eq_bot {X : Scheme.{u}} (J : X.IdealSheafData)
    (n : ℕ) (Q : X.Modules) (h : idealPowerMultiple J n Q = ⊥) (O' : X.Opens)
    (hO' : Disjoint (O' : Set X) J.support) : IsZero (Q.restrict O'.ι) := by
  have haff : ∀ U : X.affineOpens, U.1 ≤ O' → ∀ s : Γ(Q, U.1), s = 0 := by
    intro U hUO s
    have hle := (idealPowerMultiple_le_iff J n Q ⊥).mp h.le U
    rw [bot_obj_schemeModules] at hle
    have htop : J.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(Q, U)) = ⊤ := by
      rw [ideal_eq_top_of_disjoint_support J U (hO'.mono_left hUO), Ideal.top_pow,
        Submodule.top_smul]
    have hs : s ∈ J.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(Q, U)) := by
      rw [htop]; exact Submodule.mem_top
    exact hle hs
  refine Scheme.Modules.isZero_restrict_of_eq_zero O' Q fun V hV s => ?_
  let F : TopCat.Sheaf Ab.{u} X := ⟨Q.presheaf, Q.isSheaf⟩
  refine F.eq_of_locally_eq' (fun U : {U : X.affineOpens // U.1 ≤ V} => U.1.1) V
    (fun U => homOfLE U.2) (fun x hx => ?_) s 0 fun U => ?_
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  · exact (haff U.1 (U.2.trans hV) _).trans (haff U.1 (U.2.trans hV) _).symm

/-- **Restriction of coherent adic systems to an open containing the support is fully
faithful.** For coherent adic systems `P` and `Q` along `J` and an open `O` containing the
support of `J`, restriction to `O` is a bijection between morphisms `P ⟶ Q` and natural
transformations between the restricted systems. -/
theorem bijective_whiskerRight_restrict_coherentAdicSystems {X : Scheme.{u}}
    [IsLocallyNoetherian X] (J : X.IdealSheafData) (O : X.Opens)
    (hO : (J.support : Set X) ⊆ O) (P Q : Stacks.Coherent.CoherentAdicSystems J) :
    Function.Bijective (fun φ : P ⟶ Q =>
      Functor.whiskerRight φ.hom (Scheme.Modules.restrictFunctor O.ι)) := by
  let O' : X.Opens := ⟨(J.support : Set X)ᶜ, J.support.isClosed.isOpen_compl⟩
  have hcov : O ⊔ O' = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    by_cases hx : x ∈ (J.support : Set X)
    · exact Opens.mem_sup.mpr (Or.inl (hO hx))
    · exact Opens.mem_sup.mpr (Or.inr hx)
  have hdisj : Disjoint (O' : Set X) J.support := disjoint_compl_left
  let R := Scheme.Modules.restrictFunctor O.ι
  have bij' : ∀ (Y : X.Modules) (m : ℕᵒᵖ), Function.Bijective
      (fun f : Y ⟶ Q.obj.obj m => R.map f) := fun Y m =>
    Scheme.Modules.bijective_restrictFunctor_map_of_isZero_restrict O O' hcov _ _
      (isZero_restrict_of_idealPowerMultiple_eq_bot J (m.unop + 1) (Q.obj.obj m)
        (Q.property.2.1 m.unop) O' hdisj)
  have bij := fun m => bij' (P.obj.obj m) m
  constructor
  · intro φ ψ h
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun m => (bij m).1 ?_))
    exact congrArg (fun θ : P.obj ⋙ R ⟶ Q.obj ⋙ R => θ.app m) h
  · intro θ
    choose f hf using fun m : ℕᵒᵖ => (bij m).2 (θ.app m)
    have hnat : ∀ ⦃m m' : ℕᵒᵖ⦄ (g : m ⟶ m'), P.obj.map g ≫ f m' = f m ≫ Q.obj.map g := by
      intro m m' g
      apply (bij' (P.obj.obj m) m').1
      simp only [Functor.map_comp]
      rw [show R.map (f m') = θ.app m' from hf m', show R.map (f m) = θ.app m from hf m]
      exact θ.naturality g
    refine ⟨ObjectProperty.homMk ⟨f, hnat⟩, ?_⟩
    ext m : 2
    exact hf m

end Stacks.Algebraization

end
