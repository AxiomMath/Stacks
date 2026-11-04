module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LocalLerayHirsch
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackEvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackScalars
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray--Hirsch theorem for de Rham cohomology

Let `f : X ⟶ Y` be a smooth proper morphism of schemes over `S`, and let `ξ_i ∈ H^{n_i}_{dR}(X/S)`
be classes whose images in `H^*_{dR}(X_y/y)` form a `κ(y)`-basis for every `y ∈ Y`. This file
proves Proposition 0FMR of the Stacks project: the morphism
`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` is an isomorphism in `D(Y, g⁻¹𝒪_S)`, and
`(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is an isomorphism `⨁_i H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S)`.

The proof is the one of the source. Being an isomorphism is checked on the cohomology over the
members of a basis of `Y`, the affine opens `V` mapping into an affine open `W ⊆ S`
(`Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen`). Over
such a `V` the formation of `ξ̃` commutes with restriction to `f⁻¹V ⟶ V` over `W`
(`bijective_homology_lerayHirschMorphism_of_restrict`), the fibre hypothesis passes to the
restriction (`exists_basis_fibreClassOverS_restrict`), and over an affine base the statement is
Lemma 0FUM (`bijective_cohomologyFunctor_lerayHirschMorphism`).

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_lerayHirschMorphism`: Proposition 0FMR, the derived
  statement.
* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_deRhamCohomologyCup`: Proposition 0FMR, the
  statement on de Rham cohomology.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The map on base scalars of a commutative square is compatible with the maps from the global
sections of the bases. -/
theorem globalRingHom_inverseImageBaseMap_inverseImageGlobalSections {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) (a : Γ(S, ⊤)) :
    (Stacks.Cohomology.LerayCupPairing.globalRingHom (inverseImageBaseMap g' f' f g w)).hom
        ((Scheme.Hom.inverseImageGlobalSections f).hom a) =
      (Scheme.Hom.inverseImageGlobalSections f').hom (g.appTop a) :=
  congrArg (fun F => (Stacks.Cohomology.LerayCupPairing.globalRingHom F).hom a)
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g w)

/-! ### The fibres of the restriction to an open of the base -/

section Fibre

variable {V : Y.Opens} {W : S.Opens} (hVW : V ≤ g ⁻¹ᵁ W) (y : V)
  (φ : (f ∣_ V).fiber y ⟶ f.fiber (V.ι y)) [IsIso φ]
  (e : Y.residueField (V.ι y) ⟶ (V : Scheme).residueField y) [IsIso e]
  (hw : φ ≫ f.fiberToSpecResidueField (V.ι y) =
    (f ∣_ V).fiberToSpecResidueField y ≫ Spec.map e)
  (h₁ : φ ≫ f.fiberι (V.ι y) = (f ∣_ V).fiberι y ≫ (f ⁻¹ᵁ V).ι)
  (h₂ : Spec.map e ≫ Y.fromSpecResidueField (V.ι y) = (V : Scheme).fromSpecResidueField y ≫ V.ι)

/-- The pullback of fibre de Rham cohomology along the identification of the fibres. -/
abbrev fibreTransport (m : ℤ) :
    ↥(fibreDeRhamModule f (V.ι y) m) →+ ↥(fibreDeRhamModule (f ∣_ V) y m) :=
  deRhamPullbackSquare φ ((f ∣_ V).fiberToSpecResidueField y) (f.fiberToSpecResidueField (V.ι y))
    (Spec.map e) hw m

include h₁ h₂ in
/-- The transport carries the fibre class of `ξ` to the fibre class of its restriction. -/
theorem fibreTransport_fibreClassOverS (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    fibreTransport f y φ e hw m (fibreClassOverS f g (V.ι y) m ξ) =
      fibreClassOverS (f ∣_ V) (g.resLE W V hVW) y m (restrictClass f g V W hVW m ξ) := by
  have c₁ := deRhamPullbackSquare_comp (f.fiberι (V.ι y)) (f.fiberToSpecResidueField (V.ι y))
    (f ≫ g) (Y.fromSpecResidueField (V.ι y) ≫ g) (fiberι_comp_comp f g (V.ι y)) φ
    ((f ∣_ V).fiberToSpecResidueField y) (Spec.map e) hw
    (by rw [Category.assoc, fiberι_comp_comp f g (V.ι y), ← Category.assoc, hw, Category.assoc]) m ξ
  have c₂ := deRhamPullbackSquare_comp (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι
    (restrict_w f g V W hVW) ((f ∣_ V).fiberι y) ((f ∣_ V).fiberToSpecResidueField y)
    ((V : Scheme).fromSpecResidueField y ≫ g.resLE W V hVW)
    (fiberι_comp_comp (f ∣_ V) (g.resLE W V hVW) y)
    (by rw [Category.assoc, restrict_w f g V W hVW, ← Category.assoc,
      fiberι_comp_comp (f ∣_ V) (g.resLE W V hVW) y, Category.assoc]) m ξ
  refine c₁.trans (Eq.trans ?_ c₂.symm)
  refine deRhamPullbackSquare_congr (f' := (f ∣_ V).fiberToSpecResidueField y) (f := f ≫ g)
    h₁ ?_ _ _ m ξ
  rw [← Category.assoc, h₂, Category.assoc, restrictBase_w g V W hVW, Category.assoc]

/-- The transport is semilinear along `κ(y) ≅ κ_V(y)`. -/
theorem fibreTransport_smul (m : ℤ) (c : Y.residueField (V.ι y))
    (x : ↥(fibreDeRhamModule f (V.ι y) m)) :
    fibreTransport f y φ e hw m (c • x) = e.hom c • fibreTransport f y φ e hw m x := by
  have h := deRhamPullbackSquare_smul φ ((f ∣_ V).fiberToSpecResidueField y)
    (f.fiberToSpecResidueField (V.ι y)) (Spec.map e) hw m
    ((Scheme.Hom.inverseImageGlobalSections (f.fiberToSpecResidueField (V.ι y))).hom
      ((Scheme.ΓSpecIso (Y.residueField (V.ι y))).inv.hom c)) x
  have h' := globalRingHom_inverseImageBaseMap_inverseImageGlobalSections φ
    ((f ∣_ V).fiberToSpecResidueField y) (f.fiberToSpecResidueField (V.ι y)) (Spec.map e) hw
    ((Scheme.ΓSpecIso (Y.residueField (V.ι y))).inv.hom c)
  have hΓ : (Spec.map e).appTop.hom ((Scheme.ΓSpecIso (Y.residueField (V.ι y))).inv.hom c) =
      (Scheme.ΓSpecIso ((V : Scheme).residueField y)).inv.hom (e.hom c) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality e) c).symm
  exact h.trans (congrArg (fun r => r • (show ↑(SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras ((f ∣_ V).fiberToSpecResidueField y))
        (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras ((f ∣_ V).fiberToSpecResidueField y))) m) from
      fibreTransport f y φ e hw m x))
    (h'.trans (congrArg (Scheme.Hom.inverseImageGlobalSections
      ((f ∣_ V).fiberToSpecResidueField y)).hom hΓ)))

/-- The transport is bijective: the identifications of the fibres and of the residue fields are
isomorphisms. -/
theorem bijective_fibreTransport (m : ℤ) : Function.Bijective (fibreTransport f y φ e hw m) := by
  have hw' : inv φ ≫ (f ∣_ V).fiberToSpecResidueField y =
      f.fiberToSpecResidueField (V.ι y) ≫ inv (Spec.map e) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hL : ∀ z, deRhamPullbackSquare (inv φ) (f.fiberToSpecResidueField (V.ι y))
      ((f ∣_ V).fiberToSpecResidueField y) (inv (Spec.map e)) hw' m
        (fibreTransport f y φ e hw m z) =
      deRhamPullbackSquare (𝟙 _) (f.fiberToSpecResidueField (V.ι y))
        (f.fiberToSpecResidueField (V.ι y)) (𝟙 _) (by simp) m z := fun z =>
    (deRhamPullbackSquare_comp φ ((f ∣_ V).fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (V.ι y)) (Spec.map e) hw (inv φ)
      (f.fiberToSpecResidueField (V.ι y))
      (inv (Spec.map e)) hw' (by rw [IsIso.inv_hom_id, IsIso.inv_hom_id, Category.id_comp,
        Category.comp_id]) m z).trans
      (deRhamPullbackSquare_congr (f' := f.fiberToSpecResidueField (V.ι y))
        (f := f.fiberToSpecResidueField (V.ι y)) (IsIso.inv_hom_id φ)
        (IsIso.inv_hom_id (Spec.map e)) _ _ m z)
  have hR : ∀ z, fibreTransport f y φ e hw m (deRhamPullbackSquare (inv φ)
      (f.fiberToSpecResidueField (V.ι y)) ((f ∣_ V).fiberToSpecResidueField y) (inv (Spec.map e))
        hw' m z) =
      deRhamPullbackSquare (𝟙 _) ((f ∣_ V).fiberToSpecResidueField y)
        ((f ∣_ V).fiberToSpecResidueField y) (𝟙 _) (by simp) m z := fun z =>
    (deRhamPullbackSquare_comp (inv φ) (f.fiberToSpecResidueField (V.ι y))
      ((f ∣_ V).fiberToSpecResidueField y) (inv (Spec.map e)) hw' φ
      ((f ∣_ V).fiberToSpecResidueField y) (Spec.map e) hw (by rw [IsIso.hom_inv_id,
        IsIso.hom_inv_id, Category.id_comp, Category.comp_id]) m z).trans
      (deRhamPullbackSquare_congr (f' := (f ∣_ V).fiberToSpecResidueField y)
        (f := (f ∣_ V).fiberToSpecResidueField y) (IsIso.hom_inv_id φ)
        (IsIso.hom_inv_id (Spec.map e)) _ _ m z)
  have bL := bijective_deRhamPullbackSquare_of_isIso (𝟙 _) (f.fiberToSpecResidueField (V.ι y))
    (f.fiberToSpecResidueField (V.ι y)) (by simp) m
  have bR := bijective_deRhamPullbackSquare_of_isIso (𝟙 _) ((f ∣_ V).fiberToSpecResidueField y)
    ((f ∣_ V).fiberToSpecResidueField y) (by simp) m
  refine ⟨fun a b hab => bL.1 ((hL a).symm.trans ((congrArg _ hab).trans (hL b))), fun z => ?_⟩
  obtain ⟨z', hz'⟩ := bR.2 z
  exact ⟨_, (hR z').trans hz'⟩

include φ e hw h₁ h₂ in
/-- **The fibre hypothesis of the Leray--Hirsch theorem passes to the restriction to an open of the
base**: a basis of `⨁_m H^m_{dR}(X_y/κ(y))` given by fibre classes transports to one of
`⨁_m H^m_{dR}((f⁻¹V)_y/κ_V(y))` given by the fibre classes of the restricted classes. -/
theorem exists_basis_fibreClassOverS_restrict {r : ℕ} (n : Fin r → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    (hb : ∃ b : Module.Basis (Fin r) (Y.residueField (V.ι y))
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f (V.ι y) m)),
      ∀ i, b i = DirectSum.lof (Y.residueField (V.ι y)) ℤ
        (fun m : ℤ => ↥(fibreDeRhamModule f (V.ι y) m))
        (n i : ℤ) (fibreClassOverS f g (V.ι y) (n i : ℤ) (ξ i))) :
    ∃ b : Module.Basis (Fin r) ((V : Scheme).residueField y)
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule (f ∣_ V) y m)),
      ∀ i, b i = DirectSum.lof ((V : Scheme).residueField y) ℤ
        (fun m : ℤ => ↥(fibreDeRhamModule (f ∣_ V) y m)) (n i : ℤ)
        (fibreClassOverS (f ∣_ V) (g.resLE W V hVW) y (n i : ℤ)
          (restrictClass f g V W hVW (n i : ℤ) (ξ i))) := by
  classical
  obtain ⟨b, hb⟩ := hb
  let E := DFinsupp.mapRange.addEquiv (β₁ := fun m : ℤ => ↥(fibreDeRhamModule f (V.ι y) m))
    (β₂ := fun m : ℤ => ↥(fibreDeRhamModule (f ∣_ V) y m))
    fun m => AddEquiv.ofBijective (fibreTransport f y φ e hw m)
      (bijective_fibreTransport f y φ e hw m)
  have hE : ∀ x m, E x m = fibreTransport f y φ e hw m (x m) := fun _ _ => rfl
  have hEsmul : ∀ (c : Y.residueField (V.ι y)) x, E (c • x) = e.hom c • E x := by
    intro c x
    ext m
    rw [hE, DFinsupp.smul_apply, DFinsupp.smul_apply, hE]
    exact fibreTransport_smul f y φ e hw m c (x m)
  have hEsum : ∀ (c : Fin r → Y.residueField (V.ι y)),
      E (∑ i, c i • b i) = ∑ i, e.hom (c i) • E (b i) := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hEsmul (c i) (b i)
  have he : ∀ c, e.hom ((inv e).hom c) = c := fun c =>
    ConcreteCategory.congr_hom (IsIso.inv_hom_id e) c
  have hli : LinearIndependent ((V : Scheme).residueField y) fun i => E (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h0 : E (∑ i, (inv e).hom (c i) • b i) = E 0 := by
      rw [hEsum, map_zero]
      simpa only [he] using hc
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ (E.injective h0) i
    rw [← he (c i), this, map_zero]
  have hsp : ⊤ ≤ Submodule.span ((V : Scheme).residueField y) (Set.range fun i => E (b i)) := by
    intro z _
    obtain ⟨x, rfl⟩ := E.surjective z
    rw [← b.sum_repr x, hEsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, fun i => ?_⟩
  rw [Module.Basis.mk_apply, hb i]
  ext m
  rw [hE, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  rcases eq_or_ne m (n i : ℤ) with rfl | hm
  · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    exact fibreTransport_fibreClassOverS f g hVW y φ e hw h₁ h₂ _ (ξ i)
  · rw [DirectSum.of_eq_of_ne _ _ _ hm, DirectSum.of_eq_of_ne _ _ _ hm, map_zero]

end Fibre

/-- **Stacks Project, Proposition 0FMR, the derived statement.** For a smooth proper morphism
`f : X ⟶ Y` over `S` and classes `ξ_i ∈ H^{n_i}_{dR}(X/S)` whose images in `H^*_{dR}(X_y/y)` form a
basis over `κ(y)` for every point `y ∈ Y`, the morphism
`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` is an isomorphism in
`D(Y, (Y ⟶ S)^{-1}𝒪_S)`. -/
@[stacks 0FMR "first assertion: for f smooth proper over S and classes ξ_i ∈ H^{n_i}_dR(X/S) whose \
images in H^*_dR(X_y/y) form a κ(y)-basis for all y ∈ Y, the map ξ~ = ⊕ ξ~_i[-n_i] : \
⊕ Ω_{Y/S}[-n_i] → Rf_*Ω_{X/S} is an isomorphism in D(Y, (Y → S)^{-1}O_S)"]
theorem isIso_lerayHirschMorphism [Smooth f] [IsProper f] {r : ℕ} (n : Fin r → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    (hb : ∀ y : Y, ∃ b : Module.Basis (Fin r) (Y.residueField y)
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
      ∀ i, b i = DirectSum.lof (Y.residueField y) ℤ (fun m : ℤ => ↥(fibreDeRhamModule f y m))
        (n i : ℤ) (fibreClassOverS f g y (n i : ℤ) (ξ i))) :
    IsIso (lerayHirschMorphism f g n ξ) := by
  refine Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen
    (Z := inverseImageBase g) (Scheme.Hom.isBasis_affine_le_preimage_affine g)
    (lerayHirschMorphism f g n ξ) ?_
  rintro (V : Y.Opens) ⟨hV, W, hW, hVW⟩ k
  have : IsAffine V := hV
  have : IsAffine W := hW
  have : IsProper (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsProper f› V
  refine bijective_homology_lerayHirschMorphism_of_restrict f g V W hVW n ξ (fun k => ?_) k
  refine bijective_cohomologyFunctor_lerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n _
    (fun y => ?_) k
  have hpb :=
    isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f V).flip y
  have : IsIso (Spec.map (V.ι.residueFieldMap y)) := inferInstance
  exact @exists_basis_fibreClassOverS_restrict _ _ _ f g _ _ hVW y _ hpb.isIso_fst_of_isIso
    (V.ι.residueFieldMap y) inferInstance hpb.w (pullback.lift_fst _ _ _)
    (V.ι.SpecMap_residueFieldMap_fromSpecResidueField y) _ n ξ (hb (V.ι y))

/-- **Stacks Project, Proposition 0FMR, the statement on de Rham cohomology.** For a smooth proper
morphism `f : X ⟶ Y` over `S` and classes `ξ_i ∈ H^{n_i}_{dR}(X/S)` whose images in
`H^*_{dR}(X_y/y)` form a basis over `κ(y)` for every point `y ∈ Y`, the map
`⨁_i H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S), (a_i) ↦ ∑ ξ_i ∪ f^*a_i` is an isomorphism: in every degree `k`
the map `⨁_i H^{k - n_i}_{dR}(Y/S) ⟶ H^k_{dR}(X/S)` is bijective. -/
@[stacks 0FMR "second assertion: under the same hypotheses the map ⊕_i H^*_dR(Y/S) → H^*_dR(X/S), \
(a_1, ..., a_N) ↦ Σ ξ_i ∪ f^*a_i, is an isomorphism (in every degree k, from ⊕_i H^{k-n_i}_dR(Y/S))"]
theorem bijective_sum_deRhamCohomologyCup [Smooth f] [IsProper f] {r : ℕ} (n : Fin r → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    (hb : ∀ y : Y, ∃ b : Module.Basis (Fin r) (Y.residueField y)
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
      ∀ i, b i = DirectSum.lof (Y.residueField y) ℤ (fun m : ℤ => ↥(fibreDeRhamModule f y m))
        (n i : ℤ) (fibreClassOverS f g y (n i : ℤ) (ξ i))) (k : ℤ) :
    Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule f g (k - n i) (a i)))) :=
  have := isIso_lerayHirschMorphism f g n ξ hb
  bijective_sum_deRhamCohomologyCup_of_isIso f g n ξ k

end AlgebraicGeometry.DeRhamLerayHirsch
