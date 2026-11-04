module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AffineFractionClassTarget

/-!
# The affine description of the fraction class map: clause 3 of Tag 0G7R

Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` be a finite nonempty family and let `M` be an
`A`-module.  This file proves that the target comparison
`Stacks.Perfect.AffineFractionClass.targetComparison`, from
`Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})` to `Γ(Spec A, Coker(lastDif))`, is an isomorphism, and
deduces clause 3 of Tag 0G7R: together with the source isomorphism
`M/(f₁,…,f_c)M ≅ Γ(Spec A, Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~))`, it identifies the global
sections of the map of Tag 0G7Q with `Cech.supportedFraction`.

## Main definitions

* `Stacks.Perfect.AffineFractionClass.targetEquiv`: the target comparison, as an isomorphism
  `Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c}) ≅ Γ(Spec A, Coker(lastDif))`.
* `Stacks.Perfect.AffineFractionClass.cokernelTildeIso`: for a map of quasi-coherent
  `𝒪_{Spec A}`-modules, the comparison of its cokernel with the associated sheaf of the cokernel
  of the map it induces on global sections.
* `Stacks.Perfect.AffineFractionClass.fromTildeΓL` and `isoTopL`: the counit and the unit of the
  tilde–global-sections adjunction, in the `moduleSpecΓFunctor` spelling of their source resp.
  target.

## Main results

* `Stacks.Perfect.AffineFractionClass.bijective_targetComparison`: **the target comparison is
  bijective.**
* `Stacks.Perfect.AffineFractionClass.supportedFraction_eq_conj`: **clause 3 of Tag 0G7R.**  The
  global sections of Tag 0G7Q's map `supportedFractionClass` for `X = Spec A` and `ℱ = M~`,
  conjugated by the source isomorphism `affineSourceEquiv` and the target isomorphism
  `targetEquiv`, *are* the map `Cech.supportedFraction` by which the example describes them.
* `Stacks.Perfect.AffineFractionClass.surjective_Γ_cokernelπ` and `ker_Γ_cokernelπ`: **global
  sections are right exact on quasi-coherent modules over an affine scheme** — the projection to
  the cokernel is surjective on global sections and its kernel there is the range.
* `Stacks.Perfect.AffineFractionClass.isQuasicoherent_prodTerm` and `isQuasicoherent_term`: the
  terms of the sheaf-level extended alternating Čech complex of `M~` are quasi-coherent.
* `Stacks.Perfect.AffineFractionClass.bijective_topTransfer`: the comparison on the top Čech
  term is bijective, both sides being `M_{f₁⋯f_c}`.
* `Stacks.Perfect.AffineFractionClass.range_Γ_lastDif_le`: the image of the last differential on
  global sections is carried by `topTransfer` from the algebraic boundaries.
* `Stacks.Perfect.AffineFractionClass.Γ_supportedFractionClass_int_two_ne_zero`: **non-degeneracy**
  at the named inhabitant `A = ℤ`, `f = ![2]`, `M = ℤ`, where the identification is the nonzero
  map `ℤ/2 ⟶ ℤ[1/2]/ℤ`.

## Implementation notes

The proof is right exactness of `Γ(Spec A, -)` on quasi-coherent modules, from the exactness of
`M ↦ M~`.  The sheaf-level Čech terms are quasi-coherent: each `restrictedModule` is the direct
image, along the inclusion of a principal open (`inter_eq_basicOpen`), of the restriction of
`M~`; that inclusion is an affine morphism, so Tag 02KG applies.

## References

* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.SupportedFraction Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AffineFractionClass

variable {R : CommRingCat.{u}} {d : ℕ}

/-! ### The principal-open intersections are principal opens -/

/-- The principal open of a product is contained in the principal open of each factor. -/
public theorem basicOpen_prod_le (f : Fin (d + 1) → R) (s : Finset (Fin (d + 1)))
    {i : Fin (d + 1)} (hi : i ∈ s) :
    PrimeSpectrum.basicOpen (∏ j ∈ s, f j) ≤ PrimeSpectrum.basicOpen (f i) := by
  rw [← Finset.mul_prod_erase s f hi, PrimeSpectrum.basicOpen_mul]
  exact inf_le_left

/-- The principal-open intersection belonging to an increasing tuple of indices is exactly the
principal open of the product of the equations it inverts. -/
public theorem inter_eq_basicOpen (f : Fin (d + 1) → R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) (s : Finset (Fin (d + 1)))
    (hs : ∀ j : Fin (d + 1), j ∈ s ↔ ∃ k, q.1 k = j) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 =
      PrimeSpectrum.basicOpen (∏ j ∈ s, f j) := by
  refine le_antisymm (inter_le_basicOpen_prod f q s fun j hj => (hs j).1 hj) ?_
  refine le_iInf fun k => le_inf le_top ?_
  exact (basicOpen_prod_le f s ((hs (q.1 k)).2 ⟨k, rfl⟩)).trans
    (le_of_eq (AlgebraicGeometry.basicOpen_eq_of_affine (f (q.1 k))).symm)

/-- The intersection of all the principal opens is the principal open of the product of all the
equations. -/
public theorem interTop_eq (f : Fin (d + 1) → R) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1 =
      PrimeSpectrum.basicOpen (∏ j ∈ (Finset.univ : Finset (Fin (d + 1))), f j) :=
  inter_eq_basicOpen f (topIndex d) Finset.univ fun j => ⟨fun _ => ⟨j, rfl⟩, fun _ => by simp⟩

/-- The principal-open intersection of the tuple omitting `i` is the principal open of the
product of all the equations except `f i`. -/
public theorem interFace_eq {e : ℕ} (f : Fin (e + 2) → R) (i : Fin (e + 2)) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (faceIndex e i).1 =
      PrimeSpectrum.basicOpen (∏ j ∈ (Finset.univ : Finset (Fin (e + 2))).erase i, f j) := by
  classical
  refine inter_eq_basicOpen f (faceIndex e i) _ fun j => ⟨fun hj => ?_, fun hj => ?_⟩
  · exact Fin.exists_succAbove_eq (Finset.ne_of_mem_erase hj)
  · obtain ⟨k, rfl⟩ := hj
    exact Finset.mem_erase.2 ⟨i.succAbove_ne k, Finset.mem_univ _⟩

/-! ### The comparison out of a localization is an isomorphism -/

/-- On an open equal to the principal open of `g`, the canonical map from the module to its
sections is a localization at the powers of `g`. -/
public theorem isLocalizedModule_toOpenL (M : ModuleCat.{u} R) (g : R) {V : (Spec R).Opens}
    (hVeq : V = PrimeSpectrum.basicOpen g) :
    IsLocalizedModule (Submonoid.powers g) (toOpenL M V) := by
  subst hVeq
  exact inferInstanceAs
    (IsLocalizedModule (Submonoid.powers g) (tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom)

/-- **The comparison out of a localization is bijective** when the open is exactly the principal
open of the product of the inverted equations: both sides are then localizations of `M` at the
powers of that product. -/
public theorem bijective_awayLift (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) {V : (Spec R).Opens}
    (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (hVeq : V = PrimeSpectrum.basicOpen (∏ j ∈ s, f j)) :
    Function.Bijective (awayLift f M s hV) := by
  have : IsLocalizedModule (Cech.cechSub f s) (toOpenL M V) :=
    isLocalizedModule_toOpenL M (∏ j ∈ s, f j) hVeq
  have hiso : awayLift f M s hV =
      (IsLocalizedModule.iso (Cech.cechSub f s) (toOpenL M V)).toLinearMap :=
    awayLift_unique f M s hV _ fun m => by
      rw [LinearEquiv.coe_coe, LocalizedModule.mkLinearMap_apply, IsLocalizedModule.iso_mk_one]
  rw [hiso]
  exact (IsLocalizedModule.iso (Cech.cechSub f s) (toOpenL M V)).bijective

/-! ### The comparison on the top Čech term is an isomorphism -/

/-- Restriction to the same open is the identity. -/
public theorem resL_self (F : (Spec R).Modules) {V : (Spec R).Opens} (h : V ≤ V) (x : Γ(F, V)) :
    resL F h x = x := by
  rw [resL_apply, Subsingleton.elim (homOfLE h) (𝟙 V)]
  simp

/-- A section placed in one component of a cochain is read back from that component. -/
private theorem secIso_atIndexL_self (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1)) :
    secIso (specFun f) (tilde M) p ⊤ (atIndexL f M p q y) q = y := by
  rw [secIso_atIndexL, dif_pos rfl, resL_self]

/-- **Putting a section in the unique top component is bijective.**  In the top degree there is
only one increasing tuple, so a cochain is its single component. -/
public theorem secIso_atIndexL_top (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1)) :
    secIso (specFun f) (tilde M) d ⊤ (atIndexL f M d (topIndex d) y) (topIndex d) = y :=
  secIso_atIndexL_self f M _ y

/-- In the top degree a cochain is recovered from its single component. -/
public theorem atIndexL_top_secIso (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (z : Γ(prodTerm (specFun f) (tilde M) d, ⊤)) :
    atIndexL f M d (topIndex d) (secIso (specFun f) (tilde M) d ⊤ z (topIndex d)) = z := by
  refine (secIso (specFun f) (tilde M) d ⊤).injective (funext fun q => ?_)
  obtain rfl := topIndex_unique q
  exact secIso_atIndexL_self f M _ _

/-- In the top degree, putting a section in the unique component is bijective. -/
public theorem bijective_atIndexL_top (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Function.Bijective (atIndexL f M d (topIndex d)) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun z => secIso (specFun f) (tilde M) d ⊤ z (topIndex d),
      secIso_atIndexL_top f M, atIndexL_top_secIso f M⟩

/-- **The top Čech term is a single localization.**  There is only one `(d+1)`-element subset of
`Fin (d + 1)`, so the inclusion of its summand is bijective. -/
public theorem bijective_lofTop (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Function.Bijective (DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
      (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩) := by
  classical
  constructor
  · intro x y hxy
    simpa using congrArg (DirectSum.component R {w : Finset (Fin (d + 1)) // w.card = d + 1}
      (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩) hxy
  · intro z
    refine ⟨DirectSum.component R {w : Finset (Fin (d + 1)) // w.card = d + 1}
      (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩ z, ?_⟩
    refine DirectSum.ext_component R fun i => ?_
    obtain rfl := Cech.eq_topIndex i
    simp

/-- **`topTransfer` is bijective.**  Both sides are `M_{f₁⋯f_c}`: the source because the top Čech
term has a single summand, the target because the top principal intersection is the principal
open of the product of the equations and the sections of `M~` there are that localization. -/
public theorem bijective_topTransfer (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Function.Bijective (topTransfer f M) := by
  have hb : Function.Bijective ((atIndexL f M d (topIndex d) : _ → _) ∘
      (awayLift f M Finset.univ (interTop_le f Finset.univ))) :=
    (bijective_atIndexL_top f M).comp
      (bijective_awayLift f M Finset.univ (interTop_le f Finset.univ) (interTop_eq f))
  have hcomp : ∀ x : Cech.cechMod f (M : Type u) Finset.univ,
      topTransfer f M (DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
        (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩ x) =
      atIndexL f M d (topIndex d) (awayLift f M Finset.univ (interTop_le f Finset.univ) x) :=
    fun x => topTransfer_lof_of_card f M Finset.univ (Finset.card_fin _) x
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := (bijective_lofTop f M).surjective a
    obtain ⟨b', rfl⟩ := (bijective_lofTop f M).surjective b
    rw [hcomp, hcomp] at hab
    exact congrArg _ (hb.injective hab)
  · intro z
    obtain ⟨x, hx⟩ := hb.surjective z
    exact ⟨DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
      (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩ x,
      (hcomp x).trans hx⟩

/-! ### The terms of the sheaf-level complex are quasi-coherent -/

/-- The principal-open intersection of `equationsOpen` is the one `CechCochains.inter` writes
over the whole space. -/
public theorem equationsOpen_eq_inter (f : Fin (d + 1) → R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    equationsOpen (specFun f) p q =
      CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 :=
  iInf_congr fun _ => (top_inf_eq _).symm

/-- Every principal-open intersection is a principal open, so its inclusion is affine. -/
public instance isAffineHom_equationsOpen (f : Fin (d + 1) → R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    IsAffineHom (equationsOpen (specFun f) p q).ι := by
  classical
  have h : equationsOpen (specFun f) p q =
      (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv
        (∏ j ∈ Finset.image q.1 Finset.univ, f j)) := by
    rw [equationsOpen_eq_inter,
      inter_eq_basicOpen f q (Finset.image q.1 Finset.univ) (fun j => by simp),
      AlgebraicGeometry.basicOpen_eq_of_affine]
  rw [h]
  infer_instance

/-- **Each term of the sheaf-level Čech complex is quasi-coherent.**  It is the direct image,
along the affine inclusion of a principal open, of the restriction of `M~`. -/
public instance isQuasicoherent_restrictedModule (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    {p : ℕ} (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    (restrictedModule (specFun f) (tilde M) p q).IsQuasicoherent := by
  have : ((Scheme.Modules.pullback (equationsOpen (specFun f) p q).ι).obj
      (tilde M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
        (equationsOpen (specFun f) p q).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (equationsOpen (specFun f) p q).ι).app
        (tilde M)) inferInstance
  exact Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom _ _

/-- A finite product of quasi-coherent modules on an affine scheme is quasi-coherent: `M ↦ M~`
is additive, hence preserves finite products. -/
public theorem isQuasicoherent_pi {ι : Type} [Finite ι] (P : ι → (Spec R).Modules)
    [∀ i, (P i).IsQuasicoherent] : (∏ᶜ P).IsQuasicoherent := by
  have : Fintype ι := Fintype.ofFinite ι
  have e₁ : (tilde.functor R).obj (∏ᶜ fun i => (moduleSpecΓFunctor (R := R)).obj (P i)) ≅
      ∏ᶜ fun i => (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj (P i)) :=
    PreservesProduct.iso (tilde.functor R) _
  have hiso : ∀ i, IsIso (Scheme.Modules.fromTildeΓ (P i)) := fun i =>
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (P i)
  have e₂ : (∏ᶜ fun i => (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj (P i))) ≅
      ∏ᶜ P :=
    Pi.mapIso fun i => @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (P i)) (hiso i)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso (e₁ ≪≫ e₂)
    inferInstance

/-- **The sheaf-level Čech terms are quasi-coherent.** -/
public instance isQuasicoherent_prodTerm (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ) :
    (prodTerm (specFun f) (tilde M) p).IsQuasicoherent :=
  isQuasicoherent_pi _

/-- **The source of the last differential is quasi-coherent.** -/
public instance isQuasicoherent_term (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (n : ℕ) :
    (term (specFun f) (tilde M) n).IsQuasicoherent := by
  cases n with
  | zero => exact inferInstanceAs ((tilde M).IsQuasicoherent)
  | succ p => exact inferInstanceAs ((prodTerm (specFun f) (tilde M) p).IsQuasicoherent)

/-! ### Global sections are right exact on quasi-coherent modules -/

/-- The kernel of the projection to a cokernel of modules is the range. -/
public theorem ker_cokernelπ_eq_range {A B : ModuleCat.{u} R} (ψ : A ⟶ B) :
    LinearMap.ker (cokernel.π ψ).hom = LinearMap.range ψ.hom := by
  refine le_antisymm (fun b hb => ?_) ?_
  · have hiso := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom ψ
    have happ : ((ModuleCat.cokernelIsoRangeQuotient ψ).hom).hom ((cokernel.π ψ).hom b) =
        (LinearMap.range ψ.hom).mkQ b :=
      congrArg (fun χ : B ⟶ ModuleCat.of R (B ⧸ LinearMap.range ψ.hom) => χ.hom b) hiso
    rw [show (cokernel.π ψ).hom b = 0 from hb, map_zero] at happ
    exact (Submodule.Quotient.mk_eq_zero _).1 happ.symm
  · rintro _ ⟨a, rfl⟩
    exact congrArg (fun χ : A ⟶ cokernel ψ => χ.hom a) (cokernel.condition ψ)

/-- The counit of the tilde–global-sections adjunction, with its source written through
`moduleSpecΓFunctor`. -/
public def fromTildeΓL (Q : (Spec R).Modules) :
    tilde ((moduleSpecΓFunctor (R := R)).obj Q) ⟶ Q :=
  Scheme.Modules.fromTildeΓ Q

/-- The unit of the tilde–global-sections adjunction, with its target written through
`moduleSpecΓFunctor`. -/
public def isoTopL (N : ModuleCat.{u} R) : N ≅ (moduleSpecΓFunctor (R := R)).obj (tilde N) :=
  tilde.isoTop N

/-- Naturality of `fromTildeΓL`. -/
public theorem fromTildeΓL_naturality {P Q : (Spec R).Modules} (φ : P ⟶ Q) :
    tilde.map ((moduleSpecΓFunctor (R := R)).map φ) ≫ fromTildeΓL Q = fromTildeΓL P ≫ φ :=
  Scheme.Modules.fromTildeΓNatTrans.naturality φ

/-- The triangle identity of the tilde–global-sections adjunction, in the spelling of
`fromTildeΓL` and `isoTopL`. -/
public theorem isoTopL_comp_Γ_fromTildeΓL (Q : (Spec R).Modules) :
    (isoTopL ((moduleSpecΓFunctor (R := R)).obj Q)).hom ≫
      (moduleSpecΓFunctor (R := R)).map (fromTildeΓL Q) = 𝟙 _ :=
  (tilde.adjunction (R := R)).right_triangle_components Q

/-- Naturality of `isoTopL`. -/
public theorem isoTopL_comp_Γ_tilde_map {A B : ModuleCat.{u} R} (h : A ⟶ B) :
    (isoTopL A).hom ≫ (moduleSpecΓFunctor (R := R)).map (tilde.map h) =
      h ≫ (isoTopL B).hom :=
  tilde.toOpen_map_app h ⊤

/-- The counit `fromTildeΓL` is invertible on each sheaf-level Čech term. -/
public theorem isIso_fromTildeΓL_prodTerm (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ) :
    IsIso (fromTildeΓL (prodTerm (specFun f) (tilde M) p)) :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _

/-- The counit `fromTildeΓL` is invertible on the source of the last differential. -/
public theorem isIso_fromTildeΓL_term (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (n : ℕ) :
    IsIso (fromTildeΓL (term (specFun f) (tilde M) n)) :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _

section RightExact

variable {P Q : (Spec R).Modules} (φ : P ⟶ Q)
  [IsIso (fromTildeΓL P)] [IsIso (fromTildeΓL Q)]

/-- The cokernel of the associated sheaf of the map on global sections, compared with the
cokernel of the map. -/
public def cokernelTildeIsoAux :
    cokernel (tilde.map ((moduleSpecΓFunctor (R := R)).map φ)) ≅ cokernel φ :=
  cokernel.mapIso (tilde.map ((moduleSpecΓFunctor (R := R)).map φ)) φ
    (asIso (fromTildeΓL P)) (asIso (fromTildeΓL Q)) (fromTildeΓL_naturality φ)

/-- The projection to the cokernel, followed by `cokernelTildeIsoAux`. -/
public theorem π_comp_cokernelTildeIsoAux_hom :
    cokernel.π (tilde.map ((moduleSpecΓFunctor (R := R)).map φ)) ≫ (cokernelTildeIsoAux φ).hom =
      fromTildeΓL Q ≫ cokernel.π φ :=
  cokernel.π_desc _ _ _

/-- **The cokernel is the associated sheaf of the cokernel on global sections.** -/
public def cokernelTildeIso :
    cokernel φ ≅ tilde (cokernel ((moduleSpecΓFunctor (R := R)).map φ)) :=
  (cokernelTildeIsoAux φ).symm ≪≫ tildeCokernelIso ((moduleSpecΓFunctor (R := R)).map φ)

/-- Through `cokernelTildeIso`, the projection to the cokernel is `tilde` of the projection to
the cokernel on global sections. -/
public theorem π_comp_cokernelTildeIso_hom :
    fromTildeΓL Q ≫ cokernel.π φ ≫ (cokernelTildeIso φ).hom =
      tilde.map (cokernel.π ((moduleSpecΓFunctor (R := R)).map φ)) := by
  have h1 : fromTildeΓL Q ≫ cokernel.π φ ≫ (cokernelTildeIsoAux φ).inv =
      cokernel.π (tilde.map ((moduleSpecΓFunctor (R := R)).map φ)) := by
    rw [← Category.assoc, ← π_comp_cokernelTildeIsoAux_hom φ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : fromTildeΓL Q ≫ cokernel.π φ ≫ (cokernelTildeIso φ).hom =
      (fromTildeΓL Q ≫ cokernel.π φ ≫ (cokernelTildeIsoAux φ).inv) ≫
        (tildeCokernelIso ((moduleSpecΓFunctor (R := R)).map φ)).hom := by
    simp only [cokernelTildeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [h2, h1, π_comp_tildeCokernelIso_hom]

/-- **Global sections read off the cokernel.**  Through `cokernelTildeIso`, the projection to the
cokernel becomes, on global sections, the projection to the cokernel of the map induced on
global sections. -/
public theorem Γπ_comp_cokernelTildeIso :
    (moduleSpecΓFunctor (R := R)).map (cokernel.π φ) ≫
        (moduleSpecΓFunctor (R := R)).map (cokernelTildeIso φ).hom =
      cokernel.π ((moduleSpecΓFunctor (R := R)).map φ) ≫
        (isoTopL (cokernel ((moduleSpecΓFunctor (R := R)).map φ))).hom := by
  have h3 : (isoTopL ((moduleSpecΓFunctor (R := R)).obj Q)).hom ≫
      (moduleSpecΓFunctor (R := R)).map
        (fromTildeΓL Q ≫ cokernel.π φ ≫ (cokernelTildeIso φ).hom) =
      cokernel.π ((moduleSpecΓFunctor (R := R)).map φ) ≫
        (isoTopL (cokernel ((moduleSpecΓFunctor (R := R)).map φ))).hom := by
    rw [π_comp_cokernelTildeIso_hom, isoTopL_comp_Γ_tilde_map]
  rwa [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    isoTopL_comp_Γ_fromTildeΓL, Category.id_comp] at h3

/-- `Γπ_comp_cokernelTildeIso`, evaluated at a global section. -/
public theorem cokernelTildeIso_Γπ_apply (b : (moduleSpecΓFunctor (R := R)).obj Q) :
    ((moduleSpecΓFunctor (R := R)).map (cokernelTildeIso φ).hom).hom
        (((moduleSpecΓFunctor (R := R)).map (cokernel.π φ)).hom b) =
      (isoTopL (cokernel ((moduleSpecΓFunctor (R := R)).map φ))).hom
        ((cokernel.π ((moduleSpecΓFunctor (R := R)).map φ)).hom b) := by
  have h := congrArg (fun g : (moduleSpecΓFunctor (R := R)).obj Q ⟶ _ => g.hom b)
    (Γπ_comp_cokernelTildeIso φ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Both isomorphisms in `Γπ_comp_cokernelTildeIso` are bijective on global sections. -/
private theorem bijective_cokernelTildeIso_Γ :
    Function.Bijective ((moduleSpecΓFunctor (R := R)).map (cokernelTildeIso φ).hom).hom ∧
      Function.Bijective
        ((isoTopL (cokernel ((moduleSpecΓFunctor (R := R)).map φ))).hom).hom :=
  ⟨ConcreteCategory.bijective_of_isIso _, ConcreteCategory.bijective_of_isIso _⟩

/-- **Right exactness, first half.**  The projection to the cokernel is surjective on global
sections. -/
public theorem surjective_Γ_cokernelπ :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map (cokernel.π φ)).hom := by
  obtain ⟨hT, hI⟩ := bijective_cokernelTildeIso_Γ φ
  have hπ : Function.Surjective (cokernel.π ((moduleSpecΓFunctor (R := R)).map φ)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  intro z
  obtain ⟨c, hc⟩ := hI.surjective
    (((moduleSpecΓFunctor (R := R)).map (cokernelTildeIso φ).hom).hom z)
  obtain ⟨b, rfl⟩ := hπ c
  exact ⟨b, hT.injective ((cokernelTildeIso_Γπ_apply φ b).trans hc)⟩

/-- **Right exactness, second half.**  On global sections, the kernel of the projection to the
cokernel is the range. -/
public theorem ker_Γ_cokernelπ :
    LinearMap.ker ((moduleSpecΓFunctor (R := R)).map (cokernel.π φ)).hom =
      LinearMap.range ((moduleSpecΓFunctor (R := R)).map φ).hom := by
  obtain ⟨hT, hI⟩ := bijective_cokernelTildeIso_Γ φ
  ext b
  rw [LinearMap.mem_ker, ← ker_cokernelπ_eq_range ((moduleSpecΓFunctor (R := R)).map φ),
    LinearMap.mem_ker]
  refine ⟨fun hb => hI.injective ?_, fun hb => hT.injective ?_⟩
  · rw [← cokernelTildeIso_Γπ_apply φ b, hb, map_zero, map_zero]
  · rw [cokernelTildeIso_Γπ_apply φ b, hb, map_zero, map_zero]

end RightExact

/-! ### The image of the last differential is the image of the algebraic boundaries -/

/-- Equal top indices give equal summands. -/
private theorem lof_congr (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    {t t' : {w : Finset (Fin (d + 1)) // w.card = d + 1}} (h : t = t')
    {s : Finset (Fin (d + 1))} (hst : s ⊆ t.1) (hst' : s ⊆ t'.1)
    (x : Cech.cechMod f (M : Type u) s) :
    DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
        (fun w => Cech.cechMod f (M : Type u) w.1) t (Cech.cechι f (M : Type u) hst x) =
      DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
        (fun w => Cech.cechMod f (M : Type u) w.1) t' (Cech.cechι f (M : Type u) hst' x) := by
  subst h; rfl

/-- A power of `-1` multiplied by itself is `1`. -/
private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨n, rfl⟩

private theorem cechSign_mul_self (s : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    Cech.cechSign s i * Cech.cechSign s i = 1 :=
  neg_one_pow_mul_self _

/-- **A fraction whose denominator omits one index is, up to sign, a boundary.** -/
public theorem lof_univ_mem_range_cechD (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) (hs : s.card = d) (hsub : s ⊆ Finset.univ)
    (x : Cech.cechMod f (M : Type u) s) :
    DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
        (fun w => Cech.cechMod f (M : Type u) w.1) ⟨Finset.univ, Finset.card_fin _⟩
        (Cech.cechι f (M : Type u) hsub x) ∈
      LinearMap.range (Cech.cechD f (M : Type u) d) := by
  classical
  have hcompl : sᶜ.card = 1 := by rw [Finset.card_compl, hs]; simp
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcompl
  have hmem : i₀ ∈ sᶜ := by rw [hi₀]; exact Finset.mem_singleton_self i₀
  have hins : insert i₀ s = Finset.univ := by
    have hse : s = Finset.univ.erase i₀ := by
      rw [← Finset.compl_singleton, ← hi₀, compl_compl]
    rw [hse, Finset.insert_erase (Finset.mem_univ i₀)]
  refine ⟨Cech.cechSign s i₀ • DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d}
    (fun w => Cech.cechMod f (M : Type u) w.1) ⟨s, hs⟩ x, ?_⟩
  rw [map_zsmul, Cech.cechD_lof,
    Finset.sum_eq_single_of_mem (⟨i₀, hmem⟩ : {w // w ∈ sᶜ}) (Finset.mem_attach _ _)
      (fun j _ hj => absurd (Subtype.ext (Finset.mem_singleton.1 (hi₀ ▸ j.2))) hj),
    smul_smul, cechSign_mul_self, one_smul]
  exact lof_congr f M (Subtype.ext hins) _ hsub x

/-- **The image under `topTransfer` of a fraction whose denominator omits an index is a
boundary.** -/
public theorem atIndexL_awayLift_mem_map (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) (hs : s.card = d) (x : Cech.cechMod f (M : Type u) s) :
    atIndexL f M d (topIndex d) (awayLift f M s (interTop_le f s) x) ∈
      Submodule.map (topTransfer f M) (LinearMap.range (Cech.cechD f (M : Type u) d)) := by
  refine ⟨_, lof_univ_mem_range_cechD f M s hs (Finset.subset_univ s) x, ?_⟩
  rw [topTransfer_lof_of_card f M Finset.univ (Finset.card_fin _),
    awayLift_cechι f M (Finset.subset_univ s) (interTop_le f s) (interTop_le f Finset.univ) x]

/-- Summation of ordered cochains is componentwise. -/
private theorem ordCochain_sum_apply {ι : Type*} {p : ℕ} {F : (Spec R).Modules}
    {U : Fin (d + 1) → (Spec R).Opens} (s : Finset ι)
    (g : ι → CechCochains.OrdCochain U (Scheme.Modules.presheaf F) p)
    (t : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    (∑ i ∈ s, g i) t = ∑ i ∈ s, g i t := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, CechCochains.OrdCochain.add_apply, ih]

/-- A submodule of the degree-`p` sections containing every single-component cochain is
everything. -/
public theorem mem_of_atIndexL (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (N : Submodule R ((moduleSpecΓFunctor (R := R)).obj (prodTerm (specFun f) (tilde M) p)))
    (hN : ∀ (q : CechCochains.OrdIndex (I := Fin (d + 1)) p)
      (y : Γ(tilde M, CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1)),
      (atIndexL f M p q y :
        (moduleSpecΓFunctor (R := R)).obj (prodTerm (specFun f) (tilde M) p)) ∈ N)
    (w : (moduleSpecΓFunctor (R := R)).obj (prodTerm (specFun f) (tilde M) p)) : w ∈ N := by
  classical
  have : Fintype (CechCochains.OrdIndex (I := Fin (d + 1)) p) := Fintype.ofFinite _
  have hsum : ∑ q : CechCochains.OrdIndex (I := Fin (d + 1)) p,
      atIndexL f M p q (secIso (specFun f) (tilde M) p ⊤ w q) = w := by
    refine (secIso (specFun f) (tilde M) p ⊤).injective (funext fun t => ?_)
    rw [map_sum, ordCochain_sum_apply,
      Finset.sum_eq_single_of_mem t (Finset.mem_univ t)
        (fun q _ hq => by rw [secIso_atIndexL, dif_neg fun h => hq h.symm]),
      secIso_atIndexL_self]
  rw [← hsum]
  exact Submodule.sum_mem _ fun q _ => hN q _

/-- A cochain supported in a tuple which is not a face is killed by the last differential. -/
public theorem difSucc_atIndexL_of_not_face {e : ℕ} (f : Fin (e + 2) → R) (M : ModuleCat.{u} R)
    (q : CechCochains.OrdIndex (I := Fin (e + 2)) e)
    (hq : ∀ i : Fin (e + 2), faceIndex e i ≠ q)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1)) :
    (difSucc (specFun f) (tilde M) e).app ⊤ (atIndexL f M e q y) = 0 := by
  refine (secIso (specFun f) (tilde M) (e + 1) ⊤).injective (funext fun t => ?_)
  obtain rfl := topIndex_unique t
  have hidx : ∀ j : Fin (e + 2),
      (⟨(topIndex (e + 1)).1 ∘ j.succAbove,
        CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩ :
          CechCochains.OrdIndex (I := Fin (e + 2)) e) = faceIndex e j := fun _ => rfl
  rw [map_zero, CechCochains.OrdCochain.zero_apply, secIso_difSucc, ordD_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [secIso_atIndexL, dif_neg (fun h => hq j ((hidx j).symm.trans h)), map_zero, smul_zero]

/-- **The image of the last differential on global sections is the image under `topTransfer` of
the algebraic boundaries.** -/
public theorem range_Γ_lastDif_le (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    LinearMap.range
        ((moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom) ≤
      Submodule.map (topTransfer f M) (LinearMap.range (Cech.cechD f (M : Type u) d)) := by
  classical
  rintro _ ⟨w, rfl⟩
  cases d with
  | zero =>
      have hprod : (∏ j ∈ (∅ : Finset (Fin 1)), f j) = 1 := by simp
      have htopeq : (⊤ : (Spec R).Opens) =
          PrimeSpectrum.basicOpen (∏ j ∈ (∅ : Finset (Fin 1)), f j) := by
        rw [hprod, PrimeSpectrum.basicOpen_one]
        rfl
      have htop : (⊤ : (Spec R).Opens) ≤
          PrimeSpectrum.basicOpen (∏ j ∈ (∅ : Finset (Fin 1)), f j) := le_of_eq htopeq
      obtain ⟨x, rfl⟩ := (bijective_awayLift f M ∅ htop htopeq).surjective w
      have hval : (moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom
            (awayLift f M ∅ htop x) =
          atIndexL f M 0 (topIndex 0) (awayLift f M ∅ (interTop_le f ∅) x) :=
        lastDif_preimage_zero f M ∅ htop x
      rw [hval]
      exact atIndexL_awayLift_mem_map f M ∅ Finset.card_empty x
  | succ e =>
      refine mem_of_atIndexL f M e
        (Submodule.comap ((moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom)
          (Submodule.map (topTransfer f M) (LinearMap.range (Cech.cechD f (M : Type u) (e + 1)))))
        (fun q y => ?_) w
      show (moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom
          (atIndexL f M e q y) ∈
        Submodule.map (topTransfer f M) (LinearMap.range (Cech.cechD f (M : Type u) (e + 1)))
      by_cases hface : ∃ i : Fin (e + 2), faceIndex e i = q
      · obtain ⟨i, rfl⟩ := hface
        have hfaceLe : CechCochains.inter
            (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
              (faceIndex e i).1 ≤
            PrimeSpectrum.basicOpen (∏ j ∈ (Finset.univ : Finset (Fin (e + 2))).erase i, f j) :=
          le_of_eq (interFace_eq f i)
        obtain ⟨x, rfl⟩ :=
          (bijective_awayLift f M ((Finset.univ : Finset (Fin (e + 2))).erase i) hfaceLe
            (interFace_eq f i)).surjective y
        have hkey := lastDif_preimage_succ f M ((Finset.univ : Finset (Fin (e + 2))).erase i) i
          hfaceLe x
        have hsm : (moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom
              (atIndexL f M e (faceIndex e i)
                (awayLift f M ((Finset.univ : Finset (Fin (e + 2))).erase i) hfaceLe x)) =
            ((-1 : ℤ) ^ (i : ℕ)) • atIndexL f M (e + 1) (topIndex (e + 1))
              (awayLift f M ((Finset.univ : Finset (Fin (e + 2))).erase i)
                (interTop_le f _) x) := by
          show (difSucc (specFun f) (tilde M) e).app ⊤ _ = _
          rw [← hkey, map_zsmul, map_zsmul, smul_smul, neg_one_pow_mul_self,
            one_smul]
        rw [hsm]
        exact zsmul_mem (atIndexL_awayLift_mem_map f M _
          (by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega) x) _
      · have hzero : (moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom
            (atIndexL f M e q y) = 0 :=
          difSucc_atIndexL_of_not_face f M q (fun i hi => hface ⟨i, hi⟩) y
        rw [hzero]
        exact Submodule.zero_mem _

/-! ### The target comparison is an isomorphism -/

/-- **The target comparison is bijective.** -/
public theorem bijective_targetComparison (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Function.Bijective (targetComparison f M) := by
  have := isIso_fromTildeΓL_term f M d
  have := isIso_fromTildeΓL_prodTerm f M d
  have hsurj : Function.Surjective (piL f M) :=
    surjective_Γ_cokernelπ (lastDif (specFun f) (tilde M))
  have hker : LinearMap.ker (piL f M) =
      LinearMap.range ((moduleSpecΓFunctor.map (lastDif (specFun f) (tilde M))).hom) :=
    ker_Γ_cokernelπ (lastDif (specFun f) (tilde M))
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have h0 : piL f M (topTransfer f M x) = 0 := hz
    have hmem : topTransfer f M x ∈
        Submodule.map (topTransfer f M) (LinearMap.range (Cech.cechD f (M : Type u) d)) :=
      range_Γ_lastDif_le f M (hker ▸ h0)
    obtain ⟨y, hy, hxy⟩ := hmem
    have hxy' : x = y := (bijective_topTransfer f M).injective hxy.symm
    exact (Submodule.Quotient.mk_eq_zero _).2 (hxy' ▸ hy)
  · intro v
    obtain ⟨b, rfl⟩ := hsurj v
    obtain ⟨x, rfl⟩ := (bijective_topTransfer f M).surjective b
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The target comparison, as an isomorphism.** -/
public def targetEquiv (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    (Cech.cechTerm f (M : Type u) (d + 1) ⧸
        LinearMap.range (Cech.cechD f (M : Type u) d)) ≃ₗ[R]
      moduleSpecΓFunctor.obj (cokernel (lastDif (specFun f) (tilde M))) :=
  LinearEquiv.ofBijective (targetComparison f M) (bijective_targetComparison f M)

/-- `targetEquiv` sends the class of the top fraction of `m` to the class of the image of `m`
under the fraction map. -/
public theorem targetEquiv_mk (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (m : M) :
    targetEquiv f M (Submodule.Quotient.mk (Cech.topFraction f (M : Type u) m)) =
      (cokernel.π (lastDif (specFun f) (tilde M))).app ⊤
        ((fractionHom (specFun f) (tilde M) d).app ⊤ ((tilde.isoTop M).hom m)) :=
  targetComparison_mk f M m

/-- **Clause 3 of Tag 0G7R.**  Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` be a finite
nonempty family and let `M` be an `A`-module.  The map `c_{f₁,…,f_c}` of Tag 0G7Q for
`X = Spec A` and `ℱ = M~`, in the cokernel-to-cokernel presentation
`Coker((f₁,…,f_c) : ℱ^{⊕c} ⟶ ℱ) ⟶ Coker(lastDif)` of
`Stacks.Perfect.SupportedFraction.supportedFractionClass`, read on global sections through the
two canonical isomorphisms

`M/(f₁,…,f_c)M ≅ Γ(Spec A, Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~))`  (`affineSourceEquiv`) and
`Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c}) ≅ Γ(Spec A, Coker(lastDif))`  (`targetEquiv`),

**is** the map `Cech.supportedFraction` by which the example describes it.  Both comparisons are
isomorphisms (`bijective_affineSourceComparison` and `bijective_targetComparison`). -/
@[stacks 0G7R "the description itself: Γ(Spec A, -) of Tag 0G7Q's map c_{f₁,…,f_c} for ℱ = M~, \
  conjugated by the two canonical isomorphisms affineSourceEquiv and targetEquiv, IS the map \
  Cech.supportedFraction of Tag 0G7R"]
public theorem supportedFraction_eq_conj (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Cech.supportedFraction f (M : Type u) =
      (targetEquiv f M).symm.toLinearMap ∘ₗ
        ((moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom ∘ₗ
          (affineSourceEquiv f M).toLinearMap) := by
  refine LinearMap.ext fun z => ?_
  have h := LinearMap.congr_fun (supportedFraction_eq_targetComparison f M) z
  show Cech.supportedFraction f (M : Type u) z =
    (targetEquiv f M).symm
      ((moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom
        (affineSourceEquiv f M z))
  rw [show affineSourceEquiv f M z = affineSourceComparison f M z from rfl]
  rw [show (moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom
      (affineSourceComparison f M z) =
      targetComparison f M (Cech.supportedFraction f (M : Type u) z) from h]
  exact ((targetEquiv f M).symm_apply_apply _).symm

/-- **Tag 0G7R.**  Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` and let `M` be an
`A`-module.  Take `X = Spec A` and `ℱ = M~`.  Then the map `c_{f₁,…,f_c}` of Tag 0G7Q, read on
global sections through the two canonical `A`-linear isomorphisms

`M/(f₁,…,f_c)M ≅ Γ(Spec A, Coker((f₁,…,f_c) : ℱ^{⊕c} ⟶ ℱ))`  (`affineSourceEquiv`) and
`Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c}) ≅ Γ(Spec A, Coker(lastDif))`  (`targetEquiv`),

is the map `M/(f₁,…,f_c)M ⟶ Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})` carrying the class of
`s ∈ M` to the class of the fraction `s/(f₁⋯f_c)`.

This is the example's description, source and target modules, map and formula together, in one
statement, for a nonempty family; the empty family is
`Stacks.Perfect.AffineFractionClassEmpty.targetIsoEmpty_inv_Γ_quotientClassMap_sourceIsoEmpty`.
The classes of sections exhaust `M/(f₁,…,f_c)M`, so the formula below determines the
conjugated map; the map-level equality is `supportedFraction_eq_conj` and the formula alone is
`Cech.supportedFraction_mk`.

The ring and the module are taken in a *single* universe, as `tilde` requires, whereas
`Cech.supportedFraction` itself is stated for a ring and a module in independent universes.
That is a restriction of spelling only: a ring and a module in independent
universes are moved into a common universe by `ULift`. -/
@[stacks 0G7R "the example in one statement: for X = Spec A and ℱ = M~, Tag 0G7Q's map \
c_{f₁,…,f_c} on global sections, conjugated by the canonical isomorphisms affineSourceEquiv and \
targetEquiv, sends the class of s ∈ M to the class of the fraction s/(f₁⋯f_c) in Coker(⨁ᵢ \
M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})"]
public theorem targetEquiv_symm_Γ_supportedFractionClass_affineSourceEquiv_mk
    (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M) :
    (targetEquiv f M).symm
        ((moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom
          (affineSourceEquiv f M (Submodule.Quotient.mk s))) =
      Submodule.Quotient.mk
        (DirectSum.lof R {t : Finset (Fin (d + 1)) // t.card = d + 1}
          (fun t => Cech.cechMod f (M : Type u) t.1) ⟨Finset.univ, Finset.card_fin _⟩
          (LocalizedModule.mk s ⟨∏ i, f i, Submonoid.mem_powers _⟩)) :=
  (LinearMap.congr_fun (supportedFraction_eq_conj f M)
      (Submodule.Quotient.mk s)).symm.trans
    (Cech.supportedFraction_mk f (M : Type u) s)

/-! ### Non-degeneracy -/

/-- For `A = ℤ`, `f = ![2]` and `M = ℤ`, as a `CommRingCat` and a `ModuleCat`, the map
`Cech.supportedFraction` from `ℤ/2` to `ℤ[1/2]/ℤ` is not zero. -/
public theorem supportedFraction_intCat_two_ne_zero :
    Cech.supportedFraction ![(2 : (CommRingCat.of ℤ))]
      ((ModuleCat.of ℤ ℤ : ModuleCat (CommRingCat.of ℤ)) : Type) ≠ 0 :=
  supportedFraction_ne_zero _ (by norm_num) (by simp [Int.isUnit_iff])

/-- **The identification of Tag 0G7R is not an identification of zero maps.**  Whenever
`Cech.supportedFraction` is not zero, neither are the global sections of Tag 0G7Q's map read
through the source isomorphism: by `supportedFraction_eq_conj` the two differ by the
isomorphism `targetEquiv`. -/
public theorem Γ_supportedFractionClass_ne_zero (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (h : Cech.supportedFraction f (M : Type u) ≠ 0) :
    (moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom ∘ₗ
        (affineSourceEquiv f M).toLinearMap ≠ 0 := by
  intro h0
  exact h (by rw [supportedFraction_eq_conj f M, h0, LinearMap.comp_zero])

/-- **The identification of Tag 0G7R is not degenerate at a named inhabitant.**  For `A = ℤ`,
`f = ![2]`, `M = ℤ` — source `ℤ/2`, target `ℤ[1/2]/ℤ` — the global sections of Tag 0G7Q's map,
read through the source isomorphism, are not zero. -/
public theorem Γ_supportedFractionClass_int_two_ne_zero :
    (moduleSpecΓFunctor.map (supportedFractionClass (specFun ![(2 : (CommRingCat.of ℤ))])
          (tilde (ModuleCat.of ℤ ℤ : ModuleCat (CommRingCat.of ℤ))))).hom ∘ₗ
        (affineSourceEquiv ![(2 : (CommRingCat.of ℤ))]
          (ModuleCat.of ℤ ℤ : ModuleCat (CommRingCat.of ℤ))).toLinearMap ≠ 0 :=
  Γ_supportedFractionClass_ne_zero ![(2 : (CommRingCat.of ℤ))]
    (ModuleCat.of ℤ ℤ : ModuleCat (CommRingCat.of ℤ)) supportedFraction_intCat_two_ne_zero

end Stacks.Perfect.AffineFractionClass

end
