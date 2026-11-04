module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociatedFieldExtension

/-!
# Weakly associated points and henselizations

For a quasi-coherent sheaf on a scheme, weak association at a point can be detected on its
stalk, on the base change of that stalk to a henselization of the stalk, or on its base change
to a strict henselization.

Two of the three implications are the flat-extension statement that for a flat local extension
`R → S` carrying the maximal ideal to the maximal ideal, weak association of `𝔪_R` to `M`
implies weak association of `𝔪_S` to `S ⊗[R] M`. The remaining one descends weak association
from a strict henselization: the henselization is an ind-étale colimit, so a witnessing element
already lives over some étale `R`-algebra `A`, and weak association there is transported back to
`R` by the étale case of Stacks 38.5.5.

## Main results

* `AlgebraicGeometry.weaklyAssociated_tfae_henselization` gives the four equivalent descriptions
  of a weakly associated point.

## Implementation notes

The henselization and strict henselization are represented by arbitrary rings satisfying
`IsLocalRing.IsHenselization`; the latter is distinguished by a chosen separable closure of the
residue field. The four entries of `List.TFAE` are the four numbered conditions in the source.
The stalk base changes use Mathlib's scalar-extension model `Rh ⊗[R] M`.

The colimit bookkeeping needs not that the colimit of a filtered diagram of algebras is the union
of the images of its structure maps — which is true of the chosen colimit — but that *any* colimit
cocone has that property. That is `CommAlgCat.exists_app_eq`, established from the universal
property alone, and `exists_tensor_rep_of_colimit` lifts it to a tensor product by induction on
the tensor.

## References

* [Stacks Project, Tag 0CTU](https://stacks.math.columbia.edu/tag/0CTU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

namespace AlgebraicGeometry

open scoped TensorProduct

/-- For a flat local extension carrying the maximal ideal onto the maximal ideal, weak
association of the maximal ideal is inherited by the base change. -/
private theorem weaklyAssociated_maximal_tensor_of_flat
    {R S M : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M]
    (hmax : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (h : IsWeaklyAssociatedPrime R M (maximalIdeal R)) :
    IsWeaklyAssociatedPrime S (S ⊗[R] M) (maximalIdeal S) := by
  change WeaklyAssociated (maximalIdeal R) M at h
  obtain ⟨m, hm⟩ :=
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := R) (N := M)).mp h
  have hrad : (Ideal.torsionOf R M m).radical = maximalIdeal R := by
    simpa [annihilatorOfElem_semiring, Ideal.annihilator_span_singleton_eq_torsionOf] using hm
  refine (weaklyAssociated_maximalIdeal_iff_exists_radical_eq
    (S := S) (N := S ⊗[R] M)).mpr ⟨(1 : S) ⊗ₜ[R] m, ?_⟩
  rw [annihilatorOfElem_semiring, Ideal.annihilator_span_singleton_eq_torsionOf,
    ← ann_extension_eq_ann_baseChange_elem]
  refine le_antisymm ?_ ?_
  · calc
      (Ideal.map (algebraMap R S) (Ideal.torsionOf R M m)).radical ≤
          (Ideal.map (algebraMap R S) (maximalIdeal R)).radical :=
        Ideal.radical_mono (Ideal.map_mono
          ((Ideal.le_radical : Ideal.torsionOf R M m ≤ _).trans (le_of_eq hrad)))
      _ = maximalIdeal S := by rw [hmax, (maximalIdeal.isMaximal S).isPrime.radical]
  · calc
      maximalIdeal S = Ideal.map (algebraMap R S) (maximalIdeal R) := hmax.symm
      _ = Ideal.map (algebraMap R S) (Ideal.torsionOf R M m).radical := by rw [hrad]
      _ ≤ (Ideal.map (algebraMap R S) (Ideal.torsionOf R M m)).radical :=
        Ideal.map_radical_le (algebraMap R S)

/-- Weak association transfers along a ring isomorphism acting on a fixed module. -/
private theorem weaklyAssociatedPrime_map_of_ringEquiv
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Module S M] (e : R ≃+* S)
    (hsmul : ∀ (r : R) (m : M), (e r : S) • m = r • m) {p : Ideal R}
    (h : IsWeaklyAssociatedPrime R M p) :
    IsWeaklyAssociatedPrime S M (p.map e) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  let I := (S ∙ m).annihilator
  have hI : (R ∙ m).annihilator = I.comap e := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, Ideal.mem_comap, I]
    rw [hsmul]
  obtain ⟨q, hq, hqp⟩ : p ∈ Ideal.comap e '' I.minimalPrimes :=
    (Ideal.comap_minimalPrimes_eq_of_surjective (f := (e : R →+* S)) e.surjective I) ▸
      (by simpa [hI, I] using hm : p ∈ (I.comap e).minimalPrimes)
  show p.map e ∈ I.minimalPrimes
  rwa [← hqp, Ideal.map_comap_of_surjective e e.surjective q]

/-- The prime of `Γ(Spec R, ⊤)` corresponding to a point of `Spec R` is the image of the prime. -/
private theorem primeIdealOf_top_asIdeal {R : Type u} [CommRing R] (y : PrimeSpectrum R) :
    ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨y, Set.mem_univ _⟩).asIdeal =
      y.asIdeal.map (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv := by
  rw [IsAffineOpen.primeIdealOf, (isAffineOpen_top (Spec (.of R))).isoSpec_hom,
    Scheme.Opens.toSpecΓ_top]
  show ((Spec (.of R)).isoSpec.hom y).asIdeal = _
  rw [Scheme.isoSpec_Spec_hom]
  exact Ideal.comap_symm (f := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv)

/-- Every element of `A ⊗[R] M` for `A` a filtered colimit of `R`-algebras comes from one of
the stages. -/
private theorem exists_tensor_rep_of_colimit {R : Type u} [CommRing R]
    {J : Type w} [Category J] [IsFiltered J] {F : J ⥤ CommAlgCat.{w} R}
    (c : Cocone F) (hc : IsColimit c) {M : Type v} [AddCommGroup M] [Module R M]
    (z : (c.pt : Type w) ⊗[R] M) :
    ∃ j : J, ∃ z' : (F.obj j : Type w) ⊗[R] M,
      LinearMap.rTensor M ((c.ι.app j).hom.toLinearMap) z' = z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
      exact ⟨j, 0, by simp⟩
  | tmul a m =>
      obtain ⟨j, a', ha'⟩ := CommAlgCat.exists_app_eq hc a
      exact ⟨j, a' ⊗ₜ[R] m, by simp [ha']⟩
  | add x y hx hy =>
      obtain ⟨i, x', hx'⟩ := hx
      obtain ⟨j, y', hy'⟩ := hy
      let k := IsFiltered.max i j
      let fi : i ⟶ k := IsFiltered.leftToMax i j
      let fj : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, LinearMap.rTensor M (F.map fi).hom.toLinearMap x' +
        LinearMap.rTensor M (F.map fj).hom.toLinearMap y', ?_⟩
      rw [map_add]
      show (LinearMap.rTensor M ((c.ι.app k).hom.toLinearMap) ∘ₗ
          LinearMap.rTensor M (F.map fi).hom.toLinearMap) x' +
        (LinearMap.rTensor M ((c.ι.app k).hom.toLinearMap) ∘ₗ
          LinearMap.rTensor M (F.map fj).hom.toLinearMap) y' = _
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
      have hι : ∀ {l} (g : l ⟶ k), ((c.ι.app k).hom.toLinearMap).comp
          (F.map g).hom.toLinearMap = (c.ι.app l).hom.toLinearMap := fun g => by
        ext a
        exact ConcreteCategory.congr_hom (c.w g) a
      rw [hι fi, hι fj, hx', hy']

/-- **Stacks Project, Tag 0CTU.** A point is weakly associated to a quasi-coherent sheaf if and
only if the maximal ideal of its stalk is weakly associated to the stalk module; equivalently,
the corresponding maximal ideal remains weakly associated after extension to a henselization or
a strict henselization. -/
@[stacks 0CTU]
theorem weaklyAssociated_tfae_henselization
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (x : X)
    {Rh Rsh : Type u}
    [CommRing Rh] [IsLocalRing Rh] [Algebra (X.presheaf.stalk x) Rh]
    [IsHenselization (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra (X.presheaf.stalk x) Rsh]
    [Algebra (ResidueField (X.presheaf.stalk x)) (ResidueField Rsh)]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) (ResidueField Rsh)]
    [IsHenselization (X.presheaf.stalk x) (ResidueField Rsh) Rsh] :
    let F' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
    let M := ↑(TopCat.Presheaf.stalk F'.presheaf x)
    letI : Module (X.presheaf.stalk x) M := inferInstance
    List.TFAE
      [Stacks.Divisors.IsWeaklyAssociatedPoint F x,
       IsWeaklyAssociatedPrime (X.presheaf.stalk x) M
         (maximalIdeal (X.presheaf.stalk x)),
       IsWeaklyAssociatedPrime Rh (TensorProduct (X.presheaf.stalk x) Rh M)
         (maximalIdeal Rh),
       IsWeaklyAssociatedPrime Rsh (TensorProduct (X.presheaf.stalk x) Rsh M)
         (maximalIdeal Rsh)] := by
  classical
  let F' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let M := ↑(TopCat.Presheaf.stalk F'.presheaf x)
  let : Module (X.presheaf.stalk x) M := inferInstance
  dsimp only
  tfae_have 1 → 2 := id
  tfae_have 2 → 3 := by
    intro h
    have : Module.Flat (X.presheaf.stalk x) Rh :=
      IsLocalRing.IsHenselization.flat
        (R := X.presheaf.stalk x) (L := ResidueField (X.presheaf.stalk x)) (Rh := Rh)
    exact weaklyAssociated_maximal_tensor_of_flat
      (R := X.presheaf.stalk x) (S := Rh) (M := M)
      (IsLocalRing.IsHenselization.map_maximalIdeal
        (R := X.presheaf.stalk x) (L := ResidueField (X.presheaf.stalk x)) (Rh := Rh)) h
  tfae_have 3 → 4 := by
    intro h
    let R := X.presheaf.stalk x
    let κ := ResidueField R
    let κsh := ResidueField Rsh
    obtain ⟨eRh, heRh⟩ :=
      IsLocalRing.IsHenselization.exists_residueFieldEquiv (R := R) (L := κ) (Rh := Rh)
    obtain ⟨eSh, heSh⟩ :=
      IsLocalRing.IsHenselization.exists_residueFieldEquiv (R := R) (L := κsh) (Rh := Rsh)
    let : Algebra κ κsh := inferInstance
    let : Algebra R κsh := ((algebraMap κ κsh).comp (residue R)).toAlgebra
    have : IsScalarTower R κ κsh :=
      IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
    let p : Rh →ₐ[R] κsh :=
      { toRingHom := (algebraMap κ κsh).comp (eRh.symm.toRingHom.comp (residue Rh))
        commutes' := by
          intro r
          show algebraMap κ κsh (eRh.symm (residue Rh (algebraMap R Rh r))) =
            algebraMap R κsh r
          rw [← heRh r, eRh.symm_apply_apply]
          exact (IsScalarTower.algebraMap_apply R κ κsh r).symm }
    let p' : Rsh →ₐ[R] κsh :=
      { toRingHom := eSh.symm.toRingHom.comp (residue Rsh)
        commutes' := by
          intro r
          show eSh.symm (residue Rsh (algebraMap R Rsh r)) = algebraMap R κsh r
          rw [← heSh r, eSh.symm_apply_apply]
          exact (IsScalarTower.algebraMap_apply R κ κsh r).symm }
    have : HenselianLocalRing Rsh :=
      IsLocalRing.IsHenselization.henselian (R := R) (L := κsh) (Rh := Rsh)
    obtain ⟨f, hf, -⟩ :=
      HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale
        (IsLocalRing.IsHenselization.ind_etale_of_universe_le (R := R) (L := κ) (Rh := Rh))
        p p' (eSh.symm.surjective.comp residue_surjective)
    let : Algebra Rh Rsh := f.toRingHom.toAlgebra
    have : IsScalarTower R Rh Rsh :=
      IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
    have : Module.Flat R Rsh :=
      IsLocalRing.IsHenselization.flat (R := R) (L := κsh) (Rh := Rsh)
    have : Module.Flat Rh Rsh :=
      CommAlgCat.flat_of_ind_etale_restrictScalars
        (IsLocalRing.IsHenselization.ind_etale_of_universe_le (R := R) (L := κ) (Rh := Rh))
    have hmax : Ideal.map (algebraMap Rh Rsh) (maximalIdeal Rh) = maximalIdeal Rsh := by
      rw [← IsLocalRing.IsHenselization.map_maximalIdeal (R := R) (L := κ) (Rh := Rh),
        Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh Rsh,
        IsLocalRing.IsHenselization.map_maximalIdeal (R := R) (L := κsh) (Rh := Rsh)]
    exact (LinearEquiv.isWeaklyAssociatedPrime_iff
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rh Rsh Rsh M) _).mp
      (weaklyAssociated_maximal_tensor_of_flat (R := Rh) (S := Rsh) (M := Rh ⊗[R] M) hmax h)
  tfae_have 4 → 1 := by
    intro h
    let R := X.presheaf.stalk x
    let S := Rsh
    obtain ⟨z, hz⟩ := h
    obtain ⟨J, _, hJ, pres, hpres⟩ :=
      IsLocalRing.IsHenselization.ind_etale_of_universe_le
        (R := R) (L := ResidueField S) (Rh := S)
    obtain ⟨j, zA, hzA⟩ := exists_tensor_rep_of_colimit pres.cocone pres.isColimit z
    let A := (pres.diag.obj j : Type u)
    have : Algebra.Etale R A := hpres j
    let φ : A →ₐ[R] S := (pres.ι.app j).hom
    let : Algebra A S := φ.toRingHom.toAlgebra
    have : IsScalarTower R A S :=
      IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
    have : Module.Flat R S :=
      IsLocalRing.IsHenselization.flat (R := R) (L := ResidueField S) (Rh := S)
    have hAind : (CommAlgCat.etale R).ind (CommAlgCat.of R A) :=
      (CategoryTheory.ObjectProperty.le_ind (CommAlgCat.etale R))
        (CommAlgCat.of R A) (hpres j)
    have : Module.Flat A S := CommAlgCat.flat_of_ind_etale_restrictScalars hAind
    have hzA' : LinearMap.rTensor M (IsScalarTower.toAlgHom R A S).toLinearMap zA = z := hzA
    have hz' : (maximalIdeal S) ∈ (S ∙ LinearMap.rTensor M
        (IsScalarTower.toAlgHom R A S).toLinearMap zA).annihilator.minimalPrimes := by
      rwa [hzA']
    have hAweak := IsWeaklyAssociatedPrime.comap_of_flat_rTensor
      (R := R) (M := M) (T := A) (S := S) zA hz'
    let pA := (maximalIdeal S).comap (algebraMap A S)
    have hpA : pA.IsPrime := by
      show ((maximalIdeal S).comap (algebraMap A S)).IsPrime
      exact inferInstance
    let f : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
    have : Etale f := HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := R) (S := A)).2 (hpres j))
    let y : PrimeSpectrum A := ⟨pA, hpA⟩
    let G : (Spec (.of R)).Modules :=
      (tilde.functor (CommRingCat.of R)).obj (ModuleCat.of R M)
    let N : ModuleCat (CommRingCat.of A) :=
      (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R M)
    let ePB := (pullbackTildeIso (CommRingCat.of R) (CommRingCat.of A)
      (CommRingCat.ofHom (algebraMap R A))).app (ModuleCat.of R M)
    have ePB' : ((Scheme.Modules.pullback f).obj G) ≅ (tilde.functor (CommRingCat.of A)).obj N := by
      simpa [f, G, N, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
        ModuleCat.RestrictScalars.obj', ModuleCat.of] using ePB
    let eΓ := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).app N ≪≫
      asIso ((moduleSpecΓFunctor (R := CommRingCat.of A)).map ePB'.inv)
    let H := (Scheme.Modules.pullback f).obj G
    have : H.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (.of A)).ringCatSheaf).prop_of_iso
        ePB'.symm inferInstance
    let eN : (A ⊗[R] M) ≃ₗ[A] (↑N) := by
      let T := (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)
      let : Module A T := inferInstance
      have : IsScalarTower R A T :=
        IsScalarTower.of_algebraMap_smul (A := A) (M := ↑T) (fun _ _ => rfl)
      show (A ⊗[R] M) ≃ₗ[A] (TensorProduct R T M)
      exact TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (R := A) (M := A)) (LinearEquiv.refl (R := R) (M := M))
    have hAweak' : IsWeaklyAssociatedPrime A (↑N) pA := by
      simpa [pA] using (LinearEquiv.isWeaklyAssociatedPrime_iff eN _).mp hAweak
    let Q := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj H
    let : Module A Γ(H, ⊤) := Q.isModule
    have hsections : IsWeaklyAssociatedPrime A Γ(H, ⊤) pA :=
      (LinearEquiv.isWeaklyAssociatedPrime_iff eΓ.toLinearEquiv _).mp hAweak'
    let ρ : A ≃+* Γ(Spec (.of A), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    let : Module Γ(Spec (.of A), ⊤) Γ(H, ⊤) := (H.val.obj (.op ⊤)).isModule
    have hsectionsB : IsWeaklyAssociatedPrime Γ(Spec (.of A), ⊤) Γ(H, ⊤) (pA.map ρ) :=
      weaklyAssociatedPrime_map_of_ringEquiv (M := Γ(H, ⊤)) ρ (by intro a m; rfl) hsections
    have hpointA : Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback f).obj G) y := by
      let hU : IsAffineOpen (⊤ : (Spec (.of A)).Opens) := isAffineOpen_top (Spec (.of A))
      have hyU : y ∈ (⊤ : (Spec (.of A)).Opens) := Set.mem_univ _
      have hsections' : IsWeaklyAssociatedPrime Γ(Spec (.of A), ⊤) Γ(H, ⊤)
          (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
        have hp := primeIdealOf_top_asIdeal y
        simpa [hp] using hsectionsB
      exact (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint H ⊤ hU y hyU).mp hsections'
    have hpointR := (isWeaklyAssociatedPoint_pullback_iff_of_etale f G y).mp hpointA
    have : IsLocalHom (algebraMap R S) :=
      IsLocalRing.IsHenselization.isLocalHom (R := R) (L := ResidueField S) (Rh := S)
    have hmaxR : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
      maximalIdeal_comap (algebraMap R S)
    let xR : PrimeSpectrum R := ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
    have hbase : f.base y = xR := by
      apply PrimeSpectrum.ext
      show pA.comap (algebraMap R A) = maximalIdeal R
      dsimp [pA]
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hmaxR
    rw [hbase] at hpointR
    have hRglobal := (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      G ⊤ (isAffineOpen_top (Spec (.of R))) xR (Set.mem_univ _)).mpr hpointR
    let ρR : R ≃+* Γ(Spec (.of R), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
    let eTop := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app (ModuleCat.of R M)
    have hM : IsWeaklyAssociatedPrime R M (maximalIdeal R) := by
      have h := weaklyAssociatedPrime_map_of_ringEquiv (M := Γ(G, ⊤)) ρR.symm
        (by
          intro b m
          rw [Scheme.Modules.smul_Spec_def (M := G) (U := ⊤)]
          congr 1
          show ((Spec (.of R)).presheaf.map (𝟙 (Opposite.op ⊤))) _ = b
          rw [CategoryTheory.Functor.map_id_apply]
          show ρR (ρR.symm b) = b
          exact ρR.apply_symm_apply b) hRglobal
      have hpR : ((isAffineOpen_top (Spec (.of R))).primeIdealOf
          ⟨xR, Set.mem_univ _⟩).asIdeal = (maximalIdeal R).map ρR :=
        primeIdealOf_top_asIdeal xR
      have h' : IsWeaklyAssociatedPrime R (Γ(G, ⊤)) (maximalIdeal R) := by
        rw [hpR] at h
        have hIdeal : (Ideal.map ρR.symm ((maximalIdeal R).map ρR)) = maximalIdeal R := by
          rw [← Ideal.comap_symm (f := ρR)]
          exact Ideal.map_comap_of_surjective _ ρR.symm.surjective _
        simpa only [hIdeal] using h
      exact (LinearEquiv.isWeaklyAssociatedPrime_iff eTop.symm.toLinearEquiv _).mp h'
    exact hM
  tfae_finish

end AlgebraicGeometry

end
