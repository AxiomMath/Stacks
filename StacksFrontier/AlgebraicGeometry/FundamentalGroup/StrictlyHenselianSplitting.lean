module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.RingTheory.Henselian.FiniteEtale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers of a strictly henselian local scheme split, and their sections extend

Let `R` be a henselian local ring whose residue field is separably closed — a *strictly*
henselian local ring. Every finite étale `R`-algebra is then a finite product of copies of `R`,
so every finite étale cover of `Spec R` is a finite disjoint union of copies of `Spec R`. A
morphism from a connected scheme to such a disjoint union lands in a single summand, and the
summands are sections of the cover; consequently a section of a finite étale cover of `Spec R`
over any connected scheme sitting over `Spec R` is the restriction of a section over `Spec R`
itself.

The splitting comes from Stacks 04GK, which is available here as the instance
`CommAlgCat.FiniteEtale.isEquivalence_baseChange_residueField`: base change along `R → κ` is an
equivalence onto finite étale `κ`-algebras, and over a separably closed field every finite étale
algebra is `Fin n → κ` (`Algebra.IsFiniteSplit`). Transporting the splitting of
`Fin n → κ` back through the equivalence splits the `R`-algebra.

## Main results

* `AlgebraicGeometry.isSepClosed_residueField_of_maximalIdeal`
  — the two conventional residue fields of a local ring, `IsLocalRing.ResidueField` and
  `(IsLocalRing.maximalIdeal R).ResidueField`, have the same separable closedness.
* `AlgebraicGeometry.exists_algEquiv_pi_of_henselian_of_isSepClosed`
  — a finite étale algebra over a strictly henselian local ring is a finite product of copies of
  the ring.
* `AlgebraicGeometry.exists_iso_pi_of_henselian_of_isSepClosed`
  — a finite étale cover of a strictly henselian local affine scheme is a finite disjoint union
  of copies of the base, compatibly with the structure morphism.
* `AlgebraicGeometry.exists_factor_sigma_of_connectedSpace`
  — a morphism from a connected scheme into a coproduct of schemes factors through one summand.
* `AlgebraicGeometry.exists_section_of_henselian_of_isSepClosed`
  — **a section of a finite étale cover over a connected scheme over `Spec R` extends to a
  section over `Spec R`**, for `R` strictly henselian local.

## Implementation notes

This file is an input to Stacks 0BLQ and carries no `@[stacks]` attribute; that tag is proved in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrum`, at
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum`, and the note at the
end of these implementation notes records how the results below enter that proof.

Strict henselization is not mentioned in any statement. What the arguments use is the pair of
hypotheses `[HenselianLocalRing R]` and `[IsSepClosed (IsLocalRing.ResidueField R)]`, which is
what "strictly henselian" means and which is strictly weaker than being presented as a strict
henselization of something: `Stacks.StrictHenselization.IsStrictHenselization A κsep Ash` yields
exactly these two for `Ash` (its fields `henselian` and `sepClosed`, the latter through
`isSepClosed_residueField_of_maximalIdeal` because the structure records separable closedness of
`(maximalIdeal Ash).ResidueField`). Keeping the hypotheses in this form means the results apply
to any strictly henselian local ring, not only to a chosen strict henselization.

The index type of the splitting is `ULift.{u} (Fin n)` rather than `Fin n`, because
`AlgebraicGeometry.sigmaSpec` needs the index type in the scheme universe.

**How Stacks 0BLQ uses this file.** 0BLQ says that for a local ring `A` whose strict
henselization has connected punctured spectrum, restriction along
`Spec A ∖ {closed point} ↪ Spec A` is fully faithful on finite étale covers. Faithfulness is
Stacks 0BQE, at `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_isDominant`. Fullness is
where the results below are used, in two further steps:

1. descend a section from the strict henselization. The section over the punctured spectrum of
   `A` pulls back to a section over the punctured spectrum of `Ash`, which is connected by
   hypothesis, so `exists_section_of_henselian_of_isSepClosed` extends it over `Spec Ash`; the
   extension then descends along `Spec Ash → Spec A`, which is an effective epimorphism by
   Mathlib's `AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine` because
   `A → Ash` is faithfully flat. The flatness of `A → Ash` comes from property (2) of
   `Stacks.StrictHenselization.IsStrictHenselization`, the field `isFilteredColimitEtale`, which
   presents `Ash` as a filtered colimit of étale `A`-algebras; a filtered colimit of étale
   algebras is flat (`CommAlgCat.flat_of_ind_etale`), and the resulting bridge is
   `Stacks.StrictHenselization.IsStrictHenselization.flat`.
2. turn the extended section into a morphism of covers, through the finite étale *internal Hom*
   of Stacks 0BL7: a morphism `Y|U ⟶ Z|U` over `U` is a section of `Hom_X(Y, Z) ⟶ X` over `U`,
   and 0BL7 says that Hom-scheme is itself finite étale. That tag is
   `Stacks.FundamentalGroup.exists_finiteEtale_internalHom`.

## References

* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 04GK](https://stacks.math.columbia.edu/tag/04GK)
* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Separable closedness transfers along a ring equivalence of fields. -/
private theorem isSepClosed_of_ringEquiv
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed L] : IsSepClosed K := by
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic L K := ⟨fun x =>
    (show x = algebraMap L K (e x) by simp [RingHom.algebraMap_toAlgebra]) ▸
      isAlgebraic_algebraMap _⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := L) (E := K)

/-- The two conventional residue fields of a local ring — `IsLocalRing.ResidueField R`, the
quotient by the maximal ideal, and `(IsLocalRing.maximalIdeal R).ResidueField`, the residue field
of the maximal ideal as an ideal — agree up to a canonical isomorphism, so separable closedness
of the second gives separable closedness of the first. -/
theorem isSepClosed_residueField_of_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R]
    [IsSepClosed (maximalIdeal R).ResidueField] :
    IsSepClosed (ResidueField R) := by
  let f := algebraMap R (maximalIdeal R).ResidueField
  let g : ResidueField R →+* (maximalIdeal R).ResidueField :=
    Ideal.Quotient.lift (maximalIdeal R) f fun a ha => by
      rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
  have hg : Function.Bijective g := by
    refine ⟨g.injective, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) y
    exact ⟨residue R x, rfl⟩
  exact isSepClosed_of_ringEquiv (RingEquiv.ofBijective g hg)

/-- **Finite étale algebras over a strictly henselian local ring split.** For a henselian local
ring `R` with separably closed residue field, every finite étale `R`-algebra is isomorphic to
`Fin n → R` for some `n`.

Base change along `R → κ` is an equivalence onto the finite étale `κ`-algebras (Stacks 04GK), and
over the separably closed `κ` every finite étale algebra is `Fin n → κ`; the equivalence is full
and faithful, so the isomorphism `κ ⊗ S ≅ Fin n → κ = κ ⊗ (Fin n → R)` comes from an isomorphism
`S ≅ Fin n → R`. -/
@[ega "IV 18.3.3" "more general", ega "IV 18.8.1" "(a)⇒(b)"]
theorem exists_algEquiv_pi_of_henselian_of_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] :
    ∃ n : ℕ, Nonempty (S ≃ₐ[R] (Fin n → R)) := by
  classical
  let k := ResidueField R
  let B := CommAlgCat.FiniteEtale.of R S
  let F := CommAlgCat.FiniteEtale.baseChange R k
  let C := F.obj B
  let : Algebra.IsFiniteSplit k C.obj := inferInstance
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k C.obj
  let D := CommAlgCat.FiniteEtale.of R (Fin n → R)
  let e' : TensorProduct R k (Fin n → R) ≃ₐ[k] (Fin n → k) :=
    (Algebra.TensorProduct.piRight R k k (fun _ : Fin n => R)).trans
      (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R k k)
  let φ : C ≅ F.obj D := CommAlgCat.FiniteEtale.isoMk (e.trans e'.symm)
  let : F.Full := inferInstance
  let : F.Faithful := inferInstance
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let ψ : B.obj ≅ D.obj := (CommAlgCat.finiteEtale R).ι.mapIso (hF.isoEquiv.symm φ)
  exact ⟨n, ⟨CommAlgCat.algEquivOfIso ψ⟩⟩

/-- **Finite étale covers of a strictly henselian local affine scheme are split.** A finite étale
cover of `Spec R`, for `R` henselian local with separably closed residue field, is isomorphic
over `Spec R` to the spectrum of `ULift (Fin n) → R`, which is the disjoint union of `n` copies
of `Spec R`. -/
@[ega "IV 18.8.1" "(a)⇒(b)", sga "3 VIIB 2.5" "special case"]
theorem exists_iso_pi_of_henselian_of_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (Y : FiniteEtaleOver (Spec (.of R))) :
    ∃ n : ℕ, ∃ e : Y.left ≅ Spec (.of (ULift.{u} (Fin n) → R)),
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ULift.{u} (Fin n) → R))) = Y.hom := by
  let : IsFinite Y.hom := Y.prop.1
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of R))).obj Y.right) := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  let : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let : Etale Y.hom := Y.prop.2
  let φ : CommRingCat.of R ⟶ CommRingCat.of Γ(Y.left, ⊤) :=
    Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let : Algebra R Γ(Y.left, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite R Γ(Y.left, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    apply (IsFinite.SpecMap_iff φ).mp
    rw [Spec.map_preimage]
    infer_instance
  have heta : Algebra.Etale R Γ(Y.left, ⊤) := by
    rw [← RingHom.etale_algebraMap]
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    infer_instance
  obtain ⟨n, ⟨e₀⟩⟩ := exists_algEquiv_pi_of_henselian_of_isSepClosed R Γ(Y.left, ⊤)
  let e := e₀.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin n => R) Equiv.ulift.symm)
  let i : CommRingCat.of Γ(Y.left, ⊤) ≅
      CommRingCat.of (ULift.{u} (Fin n) → R) :=
    e.toRingEquiv.toCommRingCatIso
  let f := Spec.map i.hom
  let ξ := Y.left.isoSpec ≪≫ (asIso f).symm
  refine ⟨n, ξ, ?_⟩
  apply (cancel_epi Y.left.isoSpec.inv).mp
  dsimp [ξ]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hf : inv f = Spec.map i.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    change Spec.map i.hom ≫ Spec.map i.inv = 𝟙 _
    rw [← Spec.map_comp]
    simp
  rw [hf, ← Spec.map_comp, ← Spec.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)]
  refine Spec.map_inj.mpr (CommRingCat.hom_ext ?_)
  ext r
  change e.symm ((algebraMap R (ULift.{u} (Fin n) → R)) r) =
    (algebraMap R Γ(Y.left, ⊤)) r
  exact e.symm.commutes r

/-- **A morphism from a connected scheme into a coproduct factors through one summand.** The
index of the summand is constant on the source because the index map is continuous into a
discrete space, and the image then lies in the range of one open immersion. -/
theorem exists_factor_sigma_of_connectedSpace
    {ι : Type u} [TopologicalSpace ι] [DiscreteTopology ι] [Small.{u} ι]
    (g : ι → Scheme.{u}) (X : Scheme.{u}) [ConnectedSpace X]
    (f : X ⟶ ∐ g) :
    ∃ i, ∃ t : X ⟶ g i, t ≫ CategoryTheory.Limits.Sigma.ι g i = f := by
  let q : X → ι := fun x => ((sigmaMk g).symm (f x)).1
  have hq : Continuous q := (continuous_sigma fun _ => continuous_const).comp
    ((sigmaMk g).symm.continuous.comp f.continuous)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let i := q x
  have hrange : Set.range f ⊆ Set.range (CategoryTheory.Limits.Sigma.ι g i) := by
    rintro y ⟨z, rfl⟩
    rcases h : (sigmaMk g).symm (f z) with ⟨j, w⟩
    have hj : j = i := by
      have hqz : q z = j := by simp [q, h]
      exact hqz.symm.trans (PreconnectedSpace.constant inferInstance hq)
    have hzw : (sigmaMk g) ⟨j, w⟩ = f z := by
      simpa [h] using (sigmaMk g).apply_symm_apply (f z)
    subst j
    refine ⟨w, ?_⟩
    simpa [sigmaMk_mk] using hzw
  exact ⟨i, IsOpenImmersion.lift _ f hrange, IsOpenImmersion.lift_fac _ f hrange⟩

/-- A section of a split finite cover over a connected scheme is the restriction of one of the
`n` canonical sections over the base. -/
theorem exists_section_of_split
    (R : Type u) [CommRing R] (n : ℕ)
    (U : Scheme.{u}) [ConnectedSpace U]
    (j : U ⟶ Spec (.of R))
    (s : U ⟶ Spec (.of (ULift.{u} (Fin n) → R)))
    (hs : s ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (ULift.{u} (Fin n) → R))) = j) :
    ∃ t : Spec (.of R) ⟶ Spec (.of (ULift.{u} (Fin n) → R)),
      t ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ULift.{u} (Fin n) → R))) = 𝟙 _ ∧
      j ≫ t = s := by
  classical
  let I := ULift.{u} (Fin n)
  let g : I → Scheme.{u} := fun _ => Spec (.of R)
  let c := sigmaSpec (fun _ : I => CommRingCat.of R)
  obtain ⟨i, w, hw⟩ := exists_factor_sigma_of_connectedSpace g U (s ≫ inv c)
  let t : Spec (.of R) ⟶ Spec (.of (I → R)) :=
    CategoryTheory.Limits.Sigma.ι g i ≫ c
  have ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R (I → R))) = 𝟙 _ := by
    dsimp [t, c]
    rw [ι_sigmaSpec, ← Spec.map_comp]
    have hring : CommRingCat.ofHom (algebraMap R (I → R)) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i) = 𝟙 _ := by
      apply CommRingCat.hom_ext
      ext r
      simp
    rw [hring]
    simp
  have hws : w ≫ t = s := by
    dsimp [t]
    rw [← Category.assoc, hw]
    dsimp [c]
    simp
  have hwj : w = j := by
    rw [← Category.comp_id w, ← ht, ← Category.assoc, hws, hs]
  exact ⟨t, ht, hwj ▸ hws⟩

/-- **Sections of a finite étale cover extend from a connected scheme over a strictly henselian
local ring.** Let `R` be a henselian local ring with separably closed residue field, let
`Y ⟶ Spec R` be finite étale, let `U` be a connected scheme with a morphism `j : U ⟶ Spec R`,
and let `s : U ⟶ Y` be a section of `Y` over `j`. Then `s` is the restriction along `j` of a
section `t : Spec R ⟶ Y` of `Y ⟶ Spec R`.

The cover is a disjoint union of `n` copies of `Spec R`
(`exists_iso_pi_of_henselian_of_isSepClosed`), `s` lands in one copy
(`exists_factor_sigma_of_connectedSpace`), and that copy is a section over the whole base. -/
@[ega "IV 18.5.12" "Necessity",
  ega "IV 18.8.1" "(a)⇒(c), special case",
  sga "3 X 4.5" "special case",
  sga "3 XI 1.11" "special case",
  sga "7 XV 1.1.2" "special case"]
theorem exists_section_of_henselian_of_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (Y : FiniteEtaleOver (Spec (.of R)))
    (U : Scheme.{u}) [ConnectedSpace U]
    (j : U ⟶ Spec (.of R)) (s : U ⟶ Y.left)
    (hs : s ≫ Y.hom = j) :
    ∃ t : Spec (.of R) ⟶ Y.left, t ≫ Y.hom = 𝟙 _ ∧ j ≫ t = s := by
  obtain ⟨n, e, he⟩ := exists_iso_pi_of_henselian_of_isSepClosed R Y
  let p := Spec.map (CommRingCat.ofHom
    (algebraMap R (ULift.{u} (Fin n) → R)))
  have hsp : (s ≫ e.hom) ≫ p = j := by
    rw [Category.assoc, he, hs]
  obtain ⟨t, ht, hst⟩ := exists_section_of_split R n U j (s ≫ e.hom) hsp
  have hep : e.inv ≫ Y.hom = p := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨t ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, hep]
    exact ht
  · rw [← Category.assoc, hst, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry

end
