module

public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
import StacksFrontier.RingTheory.Henselian.QuasiFinite
import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization

/-!
# The strict henselization as a base change of the henselization

Let `R → S` be a ring map and let `q` be a prime of `S` lying over the prime `p` of `R` such that
`κ(p) → κ(q)` is an isomorphism. For a common separable algebraic closure `κ^sep` of the two
residue fields, the strict henselization of `S_q` is the base change of the strict henselization
of `R_p` along the map of henselizations `(R_p)^h → (S_q)^h`:
`(S_q)^{sh} = (S_q)^h ⊗_{(R_p)^h} (R_p)^{sh}`.

## Main results

* `HenselianLocalRing.of_ringEquiv`: a ring isomorphic to a henselian local ring is henselian.
* `HenselianLocalRing.of_isIntegral`: a local ring integral over a henselian local ring is
  henselian.
* `IsLocalRing.IsHenselization.exists_algEquiv_tensorProduct_strictHenselization`: Stacks 0C2Z.

## Implementation notes

Henselizations and strict henselizations are instances of `IsLocalRing.IsHenselization`, with
residue field extension `κ` and `κ^sep` respectively; the identifications of `κ^sep` with the
residue fields of the two strict henselizations are part of the data. The equality of the source
is an isomorphism of `(S_q)^h`-algebras which is compatible with the canonical map
`(R_p)^{sh} → (S_q)^{sh}` over `(R_p)^h` inducing the identity of `κ^sep`, whose existence is part
of the statement.

*Universes.* `IsLocalRing.IsHenselization R L Rh` places `R`, `L` and `Rh` in independent
universes, the filtered colimit presenting `Rh` being taken on `ULift Rh` in the universe ambient
to `R` and `Rh`. The lifting lemma `existsUnique_lift_of_ind_etale` and the uniqueness lemma
`exists_algEquiv_of_residueFieldEquiv` below are therefore stated in independent universes too;
they are reduced to their equal-universe forms by restricting scalars along
`ULift.ringEquiv` (`Stacks.Henselization.Shared.ind_etale_restrictScalars`). The same device
carries `isIntegral_strictHenselization`: the union of finite étale extensions of Lemma 0BSL, which
is what makes `(R_p)^{sh}` integral over `(R_p)^h`, is a directed limit built in one universe, so
it is applied to `R_p` and `(R_p)^h` pushed into their common ambient universe. Consequently no
universe identification remains: all seven carriers of Stacks 0C2Z are independent.

One pitfall is worth recording, since it is invisible in the statement. In
`isIntegral_strictHenselization`, integrality of the union over `ULift (R_p)^h` must be established
*before* the `Algebra (R_p)^h U` structure is introduced. That structure supplies a second, non
definitionally equal route to `Algebra (ULift (R_p)^h) U`, and once both are in scope the
`IsScalarTower (ULift (R_p)^h) (ULift (R_p)^h) U` side condition of `IsIntegral.map` can no longer
be synthesized.

## References

* [StacksProject 0C2Z](https://stacks.math.columbia.edu/tag/0C2Z)
-/

@[expose] public section

open IsLocalRing Stacks.Henselization.Shared

universe u v w x y z t

section

variable {R : Type u} {A : Type u} {B : Type v} [CommRing R] [CommRing A] [CommRing B]
  [IsLocalRing A] [HenselianLocalRing B] [Algebra R A] [Algebra R B]

/-- Lemma 08HR for a local ind-étale algebra in the universe of the base ring: a map `φ` of
residue fields compatible with the structure maps lifts to exactly one algebra map. -/
private theorem existsUnique_lift_of_ind_etale_aux
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R A))
    (φ : ResidueField A →+* ResidueField B)
    (hφ : ∀ r, φ (residue A (algebraMap R A r)) = residue B (algebraMap R B r)) :
    ∃! f : A →ₐ[R] B, ∀ a, residue B (f a) = φ (residue A a) := by
  refine (existsUnique_congr fun f => ?_).mp
    (HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale hind
      { toRingHom := φ.comp (residue A), commutes' := hφ }
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective)
  exact AlgHom.ext_iff.trans (forall_congr' fun _ => Iff.rfl)

end

/-- An isomorphism of local rings acts on residue classes through the underlying isomorphism. -/
private theorem mapEquiv_residue {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (a : A) :
    ResidueField.mapEquiv e (residue A a) = residue B (e a) :=
  ResidueField.map_residue (e : A →+* B) a

/-- **Lemma 08HR for a local ind-étale algebra**, in independent universes. A map `φ` of residue
fields compatible with the structure maps lifts to exactly one algebra map. The ind-étale
hypothesis is the one carried by `IsLocalRing.IsHenselization`, a filtered colimit presentation of
`ULift A` in the universe ambient to `R` and `A`; both the base ring and the colimit are pushed
into that universe along `ULift.ringEquiv`. -/
private theorem existsUnique_lift_of_ind_etale {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [IsLocalRing A] [HenselianLocalRing B]
    [Algebra R A] [Algebra R B]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v} (CommAlgCat.of R (ULift.{u} A)))
    (φ : ResidueField A →+* ResidueField B)
    (hφ : ∀ r, φ (residue A (algebraMap R A r)) = residue B (algebraMap R B r)) :
    ∃! f : A →ₐ[R] B, ∀ a, residue B (f a) = φ (residue A a) := by
  let eR : ULift.{v} R ≃+* R := ULift.ringEquiv
  let eA : ULift.{u} A ≃+* A := ULift.ringEquiv
  let : IsLocalRing (ULift.{u} A) := eA.symm.isLocalRing
  let : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ((algebraMap R (ULift.{u} A)).comp eR.toRingHom).toAlgebra
  let : Algebra (ULift.{v} R) B := ((algebraMap R B).comp eR.toRingHom).toAlgebra
  let φ' : ResidueField (ULift.{u} A) →+* ResidueField B :=
    φ.comp (ResidueField.mapEquiv eA).toRingHom
  have hres (a : ULift.{u} A) : φ' (residue _ a) = φ (residue A (eA a)) :=
    congrArg φ (mapEquiv_residue eA a)
  obtain ⟨f', hf', huniq⟩ := existsUnique_lift_of_ind_etale_aux
    (ind_etale_restrictScalars eR (CommAlgCat.of R (ULift.{u} A)) hind) φ' fun r => by
      rw [hres]
      exact hφ r.down
  refine ⟨{ toRingHom := (f' : ULift.{u} A →+* B).comp eA.symm.toRingHom
            commutes' := fun r => f'.commutes (ULift.up r) },
    fun a => (hf' (eA.symm a)).trans ((hres (eA.symm a)).trans (by rw [eA.apply_symm_apply])),
    fun g hg => ?_⟩
  have heq : ({ toRingHom := (g : A →+* B).comp eA.toRingHom
                commutes' := fun r => g.commutes r.down } : ULift.{u} A →ₐ[ULift.{v} R] B) = f' :=
    huniq _ fun a => (hg (eA a)).trans (hres a).symm
  exact AlgHom.ext fun a => AlgHom.congr_fun heq (eA.symm a)

/-- An endomorphism of a henselian ind-étale local algebra inducing the identity on the residue
field is the identity. -/
private theorem algHom_eq_id_of_residue {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [HenselianLocalRing A] [Algebra R A]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v} (CommAlgCat.of R (ULift.{u} A)))
    (f : A →ₐ[R] A) (hf : ∀ a, residue A (f a) = residue A a) : f = AlgHom.id R A := by
  obtain ⟨_, -, hu⟩ := existsUnique_lift_of_ind_etale hind (RingHom.id _) fun _ => rfl
  exact (hu f hf).trans (hu _ fun _ => rfl).symm

/-- **Uniqueness of the henselization in independent universes** (Lemma 08HT). Two henselian
ind-étale `R`-algebras whose residue fields are identified with a common field `K`, compatibly with
the structure maps from `R`, are isomorphic over `R` by an isomorphism inducing the identity
of `K`. -/
theorem IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv
    {R : Type u} {A : Type v} {B : Type w}
    {K : Type x} [CommRing R] [CommRing A] [CommRing B] [Field K] [HenselianLocalRing A]
    [HenselianLocalRing B] [Algebra R A] [Algebra R B]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v} (CommAlgCat.of R (ULift.{u} A)))
    (hB : (CommAlgCat.etale.{max u w} R).ind.{max u w} (CommAlgCat.of R (ULift.{u} B)))
    (eA : K ≃+* ResidueField A) (eB : K ≃+* ResidueField B)
    (he : ∀ r, eA.symm (residue A (algebraMap R A r)) = eB.symm (residue B (algebraMap R B r))) :
    ∃ e : A ≃ₐ[R] B, ∀ a, eB.symm (residue B (e a)) = eA.symm (residue A a) := by
  obtain ⟨f, hf, -⟩ := existsUnique_lift_of_ind_etale hA (eA.symm.trans eB).toRingHom fun r => by
    show eB (eA.symm (residue A (algebraMap R A r))) = _
    rw [he, eB.apply_symm_apply]
  obtain ⟨g, hg, -⟩ := existsUnique_lift_of_ind_etale hB (eB.symm.trans eA).toRingHom fun r => by
    show eA (eB.symm (residue B (algebraMap R B r))) = _
    rw [← he, eA.apply_symm_apply]
  have hfg : f.comp g = AlgHom.id R B :=
    algHom_eq_id_of_residue hB _ fun b => by
      simp only [AlgHom.comp_apply, hf, hg, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.trans_apply, eA.symm_apply_apply, eB.apply_symm_apply]
  have hgf : g.comp f = AlgHom.id R A :=
    algHom_eq_id_of_residue hA _ fun a => by
      simp only [AlgHom.comp_apply, hf, hg, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.trans_apply, eB.symm_apply_apply, eA.apply_symm_apply]
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, fun a => ?_⟩
  show eB.symm (residue B (f a)) = _
  rw [hf]
  exact eB.symm_apply_apply _

/-- **Uniqueness of the henselization in independent universes** (Lemma 08HT), under the name
this file used before the statement was made available to the modules that import it. -/
private alias exists_algEquiv_of_residueFieldEquiv := IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv

/-- The subalgebra generated by the coefficients of a polynomial contains them. -/
private theorem coeff_mem_adjoin {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (g : Polynomial B) {s : Set B} (hs : ∀ n ∈ g.support, g.coeff n ∈ s) (n : ℕ) :
    g.coeff n ∈ Algebra.adjoin A s := by
  by_cases hn : n ∈ g.support
  · exact Algebra.subset_adjoin (hs n hn)
  · rw [Polynomial.notMem_support_iff.mp hn]
    exact zero_mem _

/-- **A ring isomorphic to a henselian local ring is henselian local.** A simple-root problem is
transported along the isomorphism, which is local since it is bijective. -/
theorem HenselianLocalRing.of_ringEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [HenselianLocalRing A] (e : A ≃+* B) : HenselianLocalRing B := by
  have : IsLocalRing B := e.isLocalRing
  set φ : B →+* A := (e.symm : B →+* A) with hφ
  have hφe (x : B) : φ x = e.symm x := rfl
  have hu (x : B) : IsUnit (φ x) ↔ IsUnit x :=
    ⟨fun h => by simpa [hφe] using h.map (e : A →+* B), fun h => h.map φ⟩
  have hm (x : B) : φ x ∈ maximalIdeal A ↔ x ∈ maximalIdeal B := by
    simp only [mem_maximalIdeal, mem_nonunits_iff, hu]
  have heval (p : Polynomial B) (x : B) : (p.map φ).eval (φ x) = φ (p.eval x) :=
    Polynomial.eval_map_apply _ _
  have hinv (a : A) : φ (e a) = a := e.symm_apply_apply a
  refine ⟨fun f hf a₀ ha₀ hd => ?_⟩
  have h₀ : (f.map φ).eval (φ a₀) ∈ maximalIdeal A := by
    rw [heval]
    exact (hm _).mpr ha₀
  have h₁ : IsUnit ((f.map φ).derivative.eval (φ a₀)) := by
    rw [Polynomial.derivative_map, heval]
    exact (hu _).mpr hd
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian (f.map φ) (hf.map _) (φ a₀) h₀ h₁
  refine ⟨e a, ?_, (hm _).mp ?_⟩
  · have hz : φ (f.eval (e a)) = 0 := by rw [← heval, hinv]; exact ha
    show Polynomial.eval (e a) f = 0
    exact e.symm.injective (by simpa [hφe] using hz)
  · rw [map_sub, hinv]
    exact ha'

/-- Integrality transports along a compatible pair of isomorphisms of the base ring and of the
algebra. -/
private theorem Algebra.isIntegral_of_ringEquiv {R R' S S' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R S] [Algebra R' S'] [Algebra.IsIntegral R S]
    (f : R' ≃+* R) (g : S ≃+* S')
    (h : (algebraMap R' S').comp (f.symm : R →+* R') = (g : S →+* S').comp (algebraMap R S)) :
    Algebra.IsIntegral R' S' :=
  ⟨fun x => by
    obtain ⟨P, hP, hPx⟩ := Algebra.IsIntegral.isIntegral (R := R) (g.symm x)
    refine ⟨P.map (f.symm : R →+* R'), hP.map _, ?_⟩
    have hgx : (g : S →+* S') (g.symm x) = x := g.apply_symm_apply x
    have hev := Polynomial.hom_eval₂ P (algebraMap R S) (g : S →+* S') (g.symm x)
    rw [hgx] at hev
    rw [Polynomial.eval₂_map, h, ← hev, hPx, map_zero]⟩

/-- A local ring integral over a henselian local ring in the same universe is henselian: a
simple-root problem for a monic polynomial `g` over `B` involves finitely many elements of `B`, and
the subalgebra `S` they generate is finite over `A` and local, since `B` is integral over it, hence
henselian by Lemma 04GH, and a root of `g` in `S` solves the problem in `B`. -/
private theorem henselianLocalRing_of_isIntegral_aux {A B : Type u} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    HenselianLocalRing B := by
  refine { is_henselian := fun g hg a₀ hga₀ ⟨d, hd⟩ => ?_ }
  classical
  let S : Subalgebra A B :=
    Algebra.adjoin A ((g.support.image g.coeff ∪ {a₀, (↑d⁻¹ : B)} : Finset B) : Set B)
  have : Module.Finite A S := Algebra.finite_adjoin_of_finite_of_isIntegral (Finset.finite_toSet _)
    fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top A
  have : IsLocalRing S := RingHom.domain_isLocalRing (algebraMap S B)
  have : HenselianLocalRing S :=
    ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u} A).2.1 S
      inferInstance).1
  have : IsLocalHom (algebraMap S B) := ((local_hom_TFAE _).out 5 1 rfl rfl).mp
    (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)))
  have hcoeffs : (↑g.coeffs : Set B) ⊆ S.toSubring := fun b hb => by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hb
    exact coeff_mem_adjoin g
      (fun n hn => Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hn))) n
  let p : Polynomial S := g.toSubring S.toSubring hcoeffs
  have hpmap : p.map (algebraMap S B) = g := g.map_toSubring S.toSubring hcoeffs
  have hev (q : Polynomial S) (x : S) :
      algebraMap S B (q.eval x) = (q.map (algebraMap S B)).eval (algebraMap S B x) :=
    (Polynomial.eval_map_apply _ _).symm
  let aS : S := ⟨a₀, Algebra.subset_adjoin (by simp)⟩
  have haS : algebraMap S B aS = a₀ := rfl
  have hd' : algebraMap S B (p.derivative.eval aS) = d := by
    rw [hev, ← Polynomial.derivative_map, hpmap, haS, hd]
  have hpa : p.eval aS ∈ maximalIdeal S := (mem_maximalIdeal _).mpr fun hu =>
    (mem_maximalIdeal _).mp hga₀ (by rw [← hpmap, ← haS, ← hev]; exact hu.map _)
  obtain ⟨zz, hz, hza⟩ := HenselianLocalRing.is_henselian p
    (Polynomial.monic_of_injective Subtype.val_injective (hpmap ▸ hg)) aS hpa
    (isUnit_of_map_unit (algebraMap S B) _ (hd' ▸ d.isUnit))
  refine ⟨zz, ?_, map_nonunit (algebraMap S B) _ hza⟩
  have h := hev p zz
  rw [hz, map_zero, hpmap] at h
  exact h.symm

/-- **A local ring integral over a henselian local ring is henselian.** The two rings are pushed
into their common ambient universe along `ULift.ringEquiv`, where the subalgebra generated by a
simple-root problem is finite over the base and hence henselian by Lemma 04GH. -/
theorem HenselianLocalRing.of_isIntegral {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    HenselianLocalRing B := by
  let eA : ULift.{v} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{u} B ≃+* B := ULift.ringEquiv
  let : HenselianLocalRing (ULift.{v} A) := HenselianLocalRing.of_ringEquiv eA.symm
  let : IsLocalRing (ULift.{u} B) := eB.symm.isLocalRing
  let : Algebra (ULift.{v} A) (ULift.{u} B) :=
    (eB.symm.toRingHom.comp ((algebraMap A B).comp eA.toRingHom)).toAlgebra
  have : Algebra.IsIntegral (ULift.{v} A) (ULift.{u} B) :=
    Algebra.isIntegral_of_ringEquiv eA eB.symm (RingHom.ext fun _ => rfl)
  have : HenselianLocalRing (ULift.{u} B) :=
    henselianLocalRing_of_isIntegral_aux (A := ULift.{v} A)
  exact HenselianLocalRing.of_ringEquiv eB

namespace IsLocalRing.IsHenselization

variable {R : Type u} [CommRing R] [IsLocalRing R] {H : Type x} [CommRing H] [IsLocalRing H]
  [Algebra R H]

/-- An algebra map out of a local `R`-algebra whose maximal ideal is generated by that of `R`, to a
local `R`-algebra with local structure map, is local. -/
private theorem isLocalHom_algHom_of_map_eq {A : Type x} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A) (f : A →ₐ[R] B) :
    IsLocalHom f.toRingHom := by
  have hm' : (maximalIdeal A).map f.toRingHom ≤ maximalIdeal B := by
    rw [← hm, Ideal.map_map, AlgHom.toRingHom_eq_coe, f.comp_algebraMap]
    exact Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap (algebraMap R B)).ge
  exact ((local_hom_TFAE f.toRingHom).out 4 1).mp fun a ha => hm' (Ideal.mem_map_of_mem _ ha)

/-- An algebra map out of a henselization of `R` to a local `R`-algebra with local structure map is
local, since the maximal ideal of the henselization is generated by that of `R`. -/
private theorem isLocalHom_algHom {L : Type w} [Field L] [Algebra (ResidueField R) L]
    [IsHenselization R L H] {B : Type v} [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalHom (algebraMap R B)] (f : H →ₐ[R] B) : IsLocalHom f.toRingHom :=
  isLocalHom_algHom_of_map_eq (map_maximalIdeal (R := R) (L := L)) f

/-- Two algebra maps out of a henselization of `R` into a henselian local `R`-algebra with local
structure map coincide. -/
@[ega "IV 18.6.6" "(ii)"]
private theorem algHom_ext [IsHenselization R (ResidueField R) H] {B : Type v} [CommRing B]
    [HenselianLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)] (f g : H →ₐ[R] B) :
    f = g := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := R) (L := ResidueField R) (Rh := H)
  have := isLocalHom_algHom (L := ResidueField R) f
  have := isLocalHom_algHom (L := ResidueField R) g
  have hres (f : H →ₐ[R] B) [IsLocalHom f.toRingHom] (a : H) :
      residue B (f a) = ResidueField.map f.toRingHom (residue H a) :=
    (ResidueField.map_residue _ a).symm
  obtain ⟨_, -, hu⟩ := existsUnique_lift_of_ind_etale
    (ind_etale (R := R) (L := ResidueField R) (Rh := H))
    (ResidueField.map f.toRingHom) fun r => by rw [← hres, f.commutes]
  refine (hu f (hres f)).trans (hu g fun a => ?_).symm
  obtain ⟨r, hr⟩ := residue_surjective (e.symm (residue H a))
  have h : residue H (algebraMap R H r) = residue H a := by
    rw [← he r, Algebra.algebraMap_self, RingHom.id_apply, hr, RingEquiv.apply_symm_apply]
  rw [hres g, ← h, ← hres g, ← hres f, f.commutes, g.commutes]

/-- An `R`-algebra map into a henselian local `R`-algebra with local structure map, from an
`R`-algebra `X` which is also an `H`-algebra, is determined on `H` by the structure maps. -/
private theorem algHom_apply_algebraMap [IsHenselization R (ResidueField R) H] {X : Type y}
    {Y : Type v} [CommRing X] [CommRing Y] [HenselianLocalRing Y] [Algebra R X] [Algebra R Y]
    [Algebra H X] [Algebra H Y] [IsScalarTower R H X] [IsScalarTower R H Y]
    [IsLocalHom (algebraMap R Y)] (f : X →ₐ[R] Y) (a : H) :
    f (algebraMap H X a) = algebraMap H Y a :=
  AlgHom.congr_fun
    (algHom_ext (f.comp (IsScalarTower.toAlgHom R H X)) (IsScalarTower.toAlgHom R H Y)) a

end IsLocalRing.IsHenselization

namespace IsLocalRing.IsHenselization

variable {R : Type u} [CommRing R] [IsLocalRing R] (Rh : Type x) [CommRing Rh] [IsLocalRing Rh]
  [Algebra R Rh] [IsHenselization R (ResidueField R) Rh]

/-- **A strict henselization is integral over the henselization.** By Lemma 0BSL a strict
henselization of `R` is a union of finite extensions of `Rh`, and by Lemma 08HT any two strict
henselizations are isomorphic over `Rh`. Lemma 0BSL builds its union in one universe, so it is
applied to `R` and `Rh` pushed into their common ambient universe and to the canonical separable
closure there; the resulting strict henselization is then compared with `Rsh` over `R`, where the
two ind-étale presentations are free to live in their own universes. -/
private theorem isIntegral_strictHenselization {K : Type w} [Field K]
    [Algebra (ResidueField R) K] [IsSepClosure (ResidueField R) K] (Rsh : Type z) [CommRing Rsh]
    [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]
    [IsHenselization R K Rsh] : Algebra.IsIntegral Rh Rsh := by
  have := henselian (R := R) (L := ResidueField R) (Rh := Rh)
  have := henselian (R := R) (L := K) (Rh := Rsh)
  have := isLocalHom (R := R) (L := K) (Rh := Rsh)
  obtain ⟨e₀, he₀⟩ := exists_residueFieldEquiv (R := R) (L := ResidueField R) (Rh := Rh)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at he₀
  obtain ⟨eK, heK⟩ := exists_residueFieldEquiv (R := R) (L := K) (Rh := Rsh)
  let eR : ULift.{x} R ≃+* R := ULift.ringEquiv
  let eRh : ULift.{u} Rh ≃+* Rh := ULift.ringEquiv
  let : IsLocalRing (ULift.{x} R) := eR.symm.isLocalRing
  let : IsLocalRing (ULift.{u} Rh) := eRh.symm.isLocalRing
  let : Algebra (ULift.{x} R) (ULift.{u} Rh) :=
    ((algebraMap R (ULift.{u} Rh)).comp eR.toRingHom).toAlgebra
  let mR : ResidueField (ULift.{x} R) ≃+* ResidueField R := ResidueField.mapEquiv eR
  let mRh : ResidueField (ULift.{u} Rh) ≃+* ResidueField Rh := ResidueField.mapEquiv eRh
  have hmR (y : ULift.{x} R) : mR (residue _ y) = residue R (eR y) := mapEquiv_residue eR y
  have hmRh (y : ULift.{u} Rh) : mRh (residue _ y) = residue Rh (eRh y) := mapEquiv_residue eRh y
  let : IsHenselization (ULift.{x} R) (ResidueField (ULift.{x} R)) (ULift.{u} Rh) :=
    IsHenselization.of_ind_etale (HenselianLocalRing.of_ringEquiv eRh.symm)
      (ind_etale_restrictScalars eR (CommAlgCat.of R (ULift.{u} Rh))
        (ind_etale (R := R) (L := ResidueField R) (Rh := Rh)))
      ⟨(mR.trans e₀).trans mRh.symm, fun y => by
        rw [Algebra.algebraMap_self, RingHom.id_apply]
        apply mRh.injective
        show mRh (mRh.symm (e₀ (mR (residue _ y)))) = _
        rw [mRh.apply_symm_apply, hmR, hmRh, he₀]
        rfl⟩
  obtain ⟨e, -, -, U, _, _, _, _, _, A, -, ι, -, -, -, -, -, -, hcover, hU, -, -, hUR⟩ :=
    exists_strictHenselization_iUnion_finiteEtale.{max u x, max u x} (ULift.{x} R) (ULift.{u} Rh)
      (SeparableClosure (ResidueField (ULift.{x} R)))
  -- Integrality of `U` over `ULift Rh` is recorded *here*, while the only `ULift Rh`-algebra
  -- structure on `U` is the one just obtained. The `Algebra Rh U` introduced on the next line
  -- creates a second, non-definitionally-equal route to `Algebra (ULift Rh) U`, after which
  -- `IsIntegral.map`'s `IsScalarTower (ULift Rh) (ULift Rh) U` can no longer be synthesized.
  have hintU : Algebra.IsIntegral (ULift.{u} Rh) U := ⟨fun y => by
    obtain ⟨L, a, ha⟩ := hcover y
    simpa [ha] using (Algebra.IsIntegral.isIntegral a).map (ι L)⟩
  let : Algebra R U := ((algebraMap (ULift.{x} R) U).comp eR.symm.toRingHom).toAlgebra
  let : Algebra Rh U := ((algebraMap (ULift.{u} Rh) U).comp eRh.symm.toRingHom).toAlgebra
  have : IsScalarTower R Rh U := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap (ULift.{x} R) U (eR.symm r) = _
    rw [IsScalarTower.algebraMap_apply (ULift.{x} R) (ULift.{u} Rh) U]
    rfl
  let : Algebra (ResidueField (ULift.{x} R)) K :=
    ((algebraMap (ResidueField R) K).comp mR.toRingHom).toAlgebra
  have : IsSepClosure (ResidueField (ULift.{x} R)) K :=
    ⟨IsSepClosure.sep_closed (ResidueField R) (K := K),
      Algebra.IsSeparable.of_equiv_equiv mR.symm (RingEquiv.refl K) (by
        ext a
        simp [RingHom.algebraMap_toAlgebra])⟩
  let σ : SeparableClosure (ResidueField (ULift.{x} R)) ≃ₐ[ResidueField (ULift.{x} R)] K :=
    IsSepClosure.equiv _ _ _
  obtain ⟨eU, heU⟩ := exists_residueFieldEquiv (R := ULift.{x} R)
    (L := SeparableClosure (ResidueField (ULift.{x} R))) (Rh := U) (self := hUR)
  have hbase (r : R) : algebraMap (ResidueField (ULift.{x} R)) K (residue _ (eR.symm r))
      = algebraMap (ResidueField R) K (residue R r) := by
    show algebraMap (ResidueField R) K (mR (residue _ (eR.symm r))) = _
    rw [hmR]
    rfl
  obtain ⟨E, -⟩ := IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv
    ((CommAlgCat.etale R).ind.prop_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} U ≃ₐ[R] U).symm)
      (ind_etale_restrictScalars eR.symm (CommAlgCat.of (ULift.{x} R) U)
        (ind_etale_of_universe_le (R := ULift.{x} R)
          (L := SeparableClosure (ResidueField (ULift.{x} R))) (Rh := U))))
    (ind_etale (R := R) (L := K) (Rh := Rsh)) eU (σ.toRingEquiv.trans eK) fun r => by
      have h₁ : residue U (algebraMap R U r) = eU (algebraMap
          (ResidueField (ULift.{x} R)) (SeparableClosure (ResidueField (ULift.{x} R)))
          (residue _ (eR.symm r))) := (heU (eR.symm r)).symm
      rw [h₁, ← heK r, RingEquiv.symm_apply_apply, RingEquiv.symm_trans_apply,
        RingEquiv.symm_apply_apply, ← hbase]
      -- `σ` is a `κ(ULift R)`-algebra equivalence, so its inverse undoes the structure map;
      -- the goal is stated through `σ.toRingEquiv.symm`, hence the explicit term.
      exact (σ.symm.commutes _).symm
  let E' : U ≃ₐ[Rh] Rsh :=
    { E.toRingEquiv with commutes' := fun a => algHom_apply_algebraMap E.toAlgHom a }
  have := hintU
  have : Algebra.IsIntegral Rh U :=
    Algebra.isIntegral_of_ringEquiv eRh.symm (RingEquiv.refl U) (RingHom.ext fun _ => rfl)
  exact Algebra.isIntegral_of_ringEquiv (RingEquiv.refl Rh) E'.toRingEquiv
    (RingHom.ext fun a => (E'.commutes a).symm)

end IsLocalRing.IsHenselization

open scoped TensorProduct

section TensorProduct

variable (A : Type x) (B : Type y) (C : Type z) [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing C] [Algebra A B] [Algebra A C]

/-- The closed fibre of `B ⊗[A] C` over `B` is the residue field of `C`, when `A → B` induces an
isomorphism of residue fields and `𝔪_A C = 𝔪_C`. -/
private theorem exists_quotient_tensorProduct_equiv [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (hres : Function.Bijective (ResidueField.map (algebraMap A B)))
    (hm : (maximalIdeal A).map (algebraMap A C) = maximalIdeal C) :
    Nonempty (((B ⊗[A] C) ⧸ (maximalIdeal B).map (algebraMap B (B ⊗[A] C))) ≃+*
      ResidueField C) := by
  let eAB : ResidueField A ≃ₐ[A] ResidueField B :=
    { RingEquiv.ofBijective (ResidueField.map (algebraMap A B)) hres with
      commutes' := fun a => ResidueField.map_residue (algebraMap A B) a }
  exact ⟨(Algebra.TensorProduct.quotIdealMapEquivQuotTensor (B ⊗[A] C)
    (maximalIdeal B)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B (ResidueField B) (ResidueField B)
      C).toRingEquiv.trans
    ((Algebra.TensorProduct.congr eAB.symm (AlgEquiv.refl (R := A) (A₁ := C))).toRingEquiv.trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal A)).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq hm))))⟩

/-- If `B` is henselian, `A → B` induces an isomorphism of residue fields, `C` is integral over `A`
and `𝔪_A C = 𝔪_C`, then `B ⊗[A] C` is a henselian local ring with maximal ideal `𝔪_B (B ⊗[A] C)`:
its closed fibre over `B` is a field, and it is integral over `B`. -/
private theorem henselianLocalRing_tensorProduct [HenselianLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A C]
    (hres : Function.Bijective (ResidueField.map (algebraMap A B)))
    (hm : (maximalIdeal A).map (algebraMap A C) = maximalIdeal C) :
    ∃ _ : HenselianLocalRing (B ⊗[A] C),
      (maximalIdeal B).map (algebraMap B (B ⊗[A] C)) = maximalIdeal (B ⊗[A] C) := by
  let I : Ideal (B ⊗[A] C) := (maximalIdeal B).map (algebraMap B (B ⊗[A] C))
  obtain ⟨E⟩ := exists_quotient_tensorProduct_equiv A B C hres hm
  have hI : I.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr
    (E.toMulEquiv.isField (Field.toIsField (ResidueField C)))
  have : IsLocalRing (B ⊗[A] C) := .of_unique_max_ideal ⟨I, hI, fun J hJ =>
    (hI.eq_of_le hJ.ne_top (Ideal.map_le_iff_le_comap.mpr
      (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J)).ge)).symm⟩
  exact ⟨HenselianLocalRing.of_isIntegral (A := B), eq_maximalIdeal hI⟩

end TensorProduct

namespace IsLocalRing.IsHenselization

section BaseChange

variable {Rp : Type u} [CommRing Rp] [IsLocalRing Rp] {Sq : Type v} [CommRing Sq] [IsLocalRing Sq]
  [Algebra Rp Sq] [IsLocalHom (algebraMap Rp Sq)]
  {ksep : Type w} [Field ksep] [Algebra (ResidueField Rp) ksep] [Algebra (ResidueField Sq) ksep]
  {Rh : Type x} [CommRing Rh] [IsLocalRing Rh] [Algebra Rp Rh]
  [IsHenselization Rp (ResidueField Rp) Rh]
  {Sh : Type y} [CommRing Sh] [IsLocalRing Sh] [Algebra Sq Sh]
  [IsHenselization Sq (ResidueField Sq) Sh] [Algebra Rp Sh] [Algebra Rh Sh]
  [IsScalarTower Rp Rh Sh] [IsScalarTower Rp Sq Sh]
  {Rsh : Type z} [CommRing Rsh] [IsLocalRing Rsh] [Algebra Rp Rsh] [Algebra Rh Rsh]
  [IsScalarTower Rp Rh Rsh] [IsHenselization Rp ksep Rsh]
  {Ssh : Type t} [CommRing Ssh] [IsLocalRing Ssh] [Algebra Sq Ssh] [Algebra Sh Ssh]
  [Algebra Rp Ssh] [Algebra Rh Ssh] [IsScalarTower Sq Sh Ssh] [IsScalarTower Rp Sq Ssh]
  [IsScalarTower Rp Rh Ssh] [IsScalarTower Rh Sh Ssh] [IsHenselization Sq ksep Ssh]

/-- The map `(R_p)^{sh} → (S_q)^{sh}` over `(R_p)^h` inducing `eSsh ∘ eRsh⁻¹` on residue
fields. -/
private theorem exists_strictHenselization_algHom
    (hksep : ∀ a, algebraMap (ResidueField Sq) ksep (ResidueField.map (algebraMap Rp Sq) a) =
      algebraMap (ResidueField Rp) ksep a)
    (eRsh : ksep ≃+* ResidueField Rsh) (heRsh : ∀ a, eRsh (algebraMap (ResidueField Rp) ksep
      (residue Rp a)) = residue Rsh (algebraMap Rp Rsh a))
    (eSsh : ksep ≃+* ResidueField Ssh) (heSsh : ∀ b, eSsh (algebraMap (ResidueField Sq) ksep
      (residue Sq b)) = residue Ssh (algebraMap Sq Ssh b)) :
    ∃ g : Rsh →ₐ[Rh] Ssh, ∀ a, residue Ssh (g a) = (eRsh.symm.trans eSsh) (residue Rsh a) := by
  have := henselian (R := Sq) (L := ksep) (Rh := Ssh)
  have := isLocalHom (R := Sq) (L := ksep) (Rh := Ssh)
  have : IsLocalHom (algebraMap Rp Ssh) := by
    rw [IsScalarTower.algebraMap_eq Rp Sq Ssh]; infer_instance
  obtain ⟨g₀, hg₀, -⟩ := existsUnique_lift_of_ind_etale
    (ind_etale (R := Rp) (L := ksep) (Rh := Rsh))
    (eRsh.symm.trans eSsh).toRingHom fun r => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply, ← heRsh,
        RingEquiv.symm_apply_apply, IsScalarTower.algebraMap_apply Rp Sq Ssh, ← heSsh,
        ← ResidueField.map_residue, hksep]
  exact ⟨{ g₀.toRingHom with commutes' := fun a => algHom_apply_algebraMap g₀ a }, hg₀⟩

omit [IsHenselization Rp (ResidueField Rp) Rh] in
/-- The map of henselizations `(R_p)^h → (S_q)^h` induces an isomorphism of residue fields when
`R_p → S_q` does. -/
private theorem bijective_residueField_map_henselization [IsLocalHom (algebraMap Rh Sh)]
    (hres : Function.Bijective (ResidueField.map (algebraMap Rp Sq))) :
    Function.Bijective (ResidueField.map (algebraMap Rh Sh)) := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  obtain ⟨eS, heS⟩ := exists_residueFieldEquiv (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  obtain ⟨c, hc⟩ := hres.2 (eS.symm b)
  obtain ⟨r, rfl⟩ := residue_surjective c
  refine ⟨residue Rh (algebraMap Rp Rh r), ?_⟩
  rw [ResidueField.map_residue, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply Rp Sq Sh, ← heS, Algebra.algebraMap_self, RingHom.id_apply,
    ← ResidueField.map_residue, hc, RingEquiv.apply_symm_apply]

/-- `(R_p)^{sh}` is integral over `(R_p)^h` and its maximal ideal is generated by that of
`(R_p)^h`. -/
private theorem isIntegral_and_map_maximalIdeal [IsSepClosure (ResidueField Rp) ksep] :
    Algebra.IsIntegral Rh Rsh ∧
      (maximalIdeal Rh).map (algebraMap Rh Rsh) = maximalIdeal Rsh := by
  obtain ⟨_, _, hsep, -⟩ := exists_residueFieldAlgebra (R := Rp) (L := ksep) (Rh := Rsh)
  have := hsep inferInstance
  refine ⟨isIntegral_strictHenselization (R := Rp) Rh Rsh (K := ResidueField Rsh), ?_⟩
  rw [← map_maximalIdeal (R := Rp) (L := ResidueField Rp), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, map_maximalIdeal (L := ksep)]

variable [HenselianLocalRing (Sh ⊗[Rh] Rsh)]

variable (Sh) in
/-- The map `Sh ⊗[Rh] Rsh → Ssh` induced by `g : Rsh → Ssh`. -/
private noncomputable abbrev tensorLift (g : Rsh →ₐ[Rh] Ssh) : Sh ⊗[Rh] Rsh →ₐ[Sh] Ssh :=
  AlgHom.liftEquiv Rh Sh Rsh Ssh g

omit [IsLocalRing Rh] [IsHenselization Rp (ResidueField Rp) Rh] [IsLocalRing Sh]
  [IsHenselization Sq (ResidueField Sq) Sh] [IsLocalRing Rsh] [IsHenselization Rp ksep Rsh]
  [IsLocalRing Ssh] [IsHenselization Sq ksep Ssh] [HenselianLocalRing (Sh ⊗[Rh] Rsh)] in
/-- `tensorLift Sh g` restricts to `g` on `Rsh`. -/
private theorem tensorLift_includeRight (g : Rsh →ₐ[Rh] Ssh) (a : Rsh) :
    tensorLift Sh g (Algebra.TensorProduct.includeRight a) = g a := by
  simp [tensorLift]

omit [IsLocalRing Rh] [IsLocalRing Rsh] in
/-- The map `Sh ⊗[Rh] Rsh → Ssh` induced by `g` is local. -/
private theorem isLocalHom_tensorLift [IsLocalHom (algebraMap Sh Ssh)]
    (hmT : (maximalIdeal Sh).map (algebraMap Sh (Sh ⊗[Rh] Rsh)) = maximalIdeal (Sh ⊗[Rh] Rsh))
    (g : Rsh →ₐ[Rh] Ssh) : IsLocalHom (tensorLift Sh g).toRingHom :=
  isLocalHom_algHom_of_map_eq hmT _

include Sq ksep in
omit [Algebra Rp Sq] [IsLocalHom (algebraMap Rp Sq)] [IsLocalRing Rh]
  [IsHenselization Rp (ResidueField Rp) Rh] [IsScalarTower Rp Sq Sh] [IsScalarTower Rp Sq Ssh] in
/-- **The tensor product is the strict henselization.** If `Sh ⊗[Rh] Rsh` is henselian local
with maximal ideal generated by that of `Sh`, and `g : Rsh → Ssh` induces an isomorphism `φ` on
residue fields, then the map `Sh ⊗[Rh] Rsh → Ssh` induced by `g` is an isomorphism. Its inverse
is the lift of the inverse of the residue field isomorphism along the ind-étale `Sq → Ssh`. -/
private theorem exists_algEquiv_of_residue_eq [IsLocalHom (algebraMap Rp Sh)]
    [IsLocalHom (algebraMap Sh Ssh)]
    (hmT : (maximalIdeal Sh).map (algebraMap Sh (Sh ⊗[Rh] Rsh)) = maximalIdeal (Sh ⊗[Rh] Rsh))
    (φ : ResidueField Rsh ≃+* ResidueField Ssh) (g : Rsh →ₐ[Rh] Ssh)
    (hg : ∀ a, residue Ssh (g a) = φ (residue Rsh a)) :
    ∃ e : Ssh ≃ₐ[Sh] Sh ⊗[Rh] Rsh, ∀ a, e (g a) = Algebra.TensorProduct.includeRight a := by
  have : IsScalarTower Rp Sh Ssh := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply Rp Rh Ssh, IsScalarTower.algebraMap_apply Rh Sh Ssh,
      ← IsScalarTower.algebraMap_apply Rp Rh Sh]
  let F := tensorLift Sh g
  have := isLocalHom_tensorLift hmT g
  have hres (a : Sh ⊗[Rh] Rsh) : ResidueField.map F.toRingHom (residue _ a) = residue Ssh (F a) :=
    ResidueField.map_residue _ a
  let eF : ResidueField (Sh ⊗[Rh] Rsh) ≃+* ResidueField Ssh :=
    RingEquiv.ofBijective _ ⟨RingHom.injective _, fun b => by
      obtain ⟨a, ha⟩ := residue_surjective (φ.symm b)
      exact ⟨residue _ (Algebra.TensorProduct.includeRight a), by
        rw [hres, tensorLift_includeRight, hg, ha, φ.apply_symm_apply]⟩⟩
  have heF (a : Sh ⊗[Rh] Rsh) : eF (residue _ a) = residue Ssh (F a) := hres a
  have : IsLocalHom (algebraMap Sh (Sh ⊗[Rh] Rsh)) :=
    ((local_hom_TFAE _).out 4 1).mp fun a ha => hmT ▸ Ideal.mem_map_of_mem _ ha
  have := henselian (R := Sq) (L := ksep) (Rh := Ssh)
  have := isLocalHom (R := Sq) (L := ksep) (Rh := Ssh)
  have := isLocalHom (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  have : IsLocalHom (algebraMap Sq (Sh ⊗[Rh] Rsh)) := by
    rw [IsScalarTower.algebraMap_eq Sq Sh]; infer_instance
  have : IsLocalHom (algebraMap Rp (Sh ⊗[Rh] Rsh)) := by
    rw [IsScalarTower.algebraMap_eq Rp Sh]; infer_instance
  obtain ⟨i₀, hres₀, -⟩ := existsUnique_lift_of_ind_etale
    (ind_etale (R := Sq) (L := ksep) (Rh := Ssh))
    eF.symm.toRingHom fun b => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, heF,
        IsScalarTower.algebraMap_apply Sq Sh (Sh ⊗[Rh] Rsh) b, F.commutes,
        ← IsScalarTower.algebraMap_apply Sq Sh Ssh b]
  let i : Ssh →ₐ[Sh] Sh ⊗[Rh] Rsh :=
    { i₀.toRingHom with commutes' := fun b => algHom_apply_algebraMap i₀ b }
  have hi (a : Ssh) : eF (residue _ (i a)) = residue Ssh a := by
    rw [show residue _ (i a) = eF.symm (residue Ssh a) from hres₀ a, RingEquiv.apply_symm_apply]
  have hFi : F.comp i = AlgHom.id Sh Ssh :=
    AlgHom.ext fun a => AlgHom.congr_fun (algHom_eq_id_of_residue
      (ind_etale (R := Sq) (L := ksep) (Rh := Ssh)) ((F.comp i).restrictScalars Sq)
      fun a => by rw [AlgHom.restrictScalars_apply, AlgHom.comp_apply, ← heF, hi]) a
  let j : Rsh →ₐ[Rp] Sh ⊗[Rh] Rsh := (Algebra.TensorProduct.includeRight).restrictScalars Rp
  have := isLocalHom_algHom (L := ksep) j
  have hig (a : Rsh) : i (g a) = Algebra.TensorProduct.includeRight a := by
    obtain ⟨_, -, hu⟩ := existsUnique_lift_of_ind_etale
      (ind_etale (R := Rp) (L := ksep) (Rh := Rsh))
      (ResidueField.map j.toRingHom) fun r => by
        rw [ResidueField.map_residue, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, j.commutes]
    refine AlgHom.congr_fun ((hu ((i.restrictScalars Rp).comp (g.restrictScalars Rp))
      fun a => ?_).trans (hu j fun a => (ResidueField.map_residue _ a).symm).symm) a
    rw [ResidueField.map_residue, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      AlgHom.restrictScalars_apply, ← eF.injective.eq_iff, hi, heF]
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.restrictScalars_apply,
      tensorLift_includeRight]
  refine ⟨AlgEquiv.ofAlgHom i F ((AlgHom.liftEquiv Rh Sh Rsh _).symm.injective ?_) hFi, hig⟩
  ext a
  exact (congrArg i (tensorLift_includeRight (Sh := Sh) g a)).trans (hig a)

omit [HenselianLocalRing (Sh ⊗[Rh] Rsh)] in
/-- **Stacks 0C2Z for local rings.** Let `Rp → Sq` be a local map of local rings inducing an
isomorphism of residue fields, and let `κ^sep` be a common separable algebraic closure of them.
Then there is a local map `Rsh → Ssh` over `Rh` inducing the identity of `κ^sep`, and it identifies
`Ssh` with `Sh ⊗[Rh] Rsh`. -/
theorem exists_algEquiv_tensorProduct_strictHenselization [IsSepClosure (ResidueField Rp) ksep]
    (hres : Function.Bijective (ResidueField.map (algebraMap Rp Sq)))
    (hksep : ∀ a, algebraMap (ResidueField Sq) ksep (ResidueField.map (algebraMap Rp Sq) a) =
      algebraMap (ResidueField Rp) ksep a)
    (eRsh : ksep ≃+* ResidueField Rsh) (heRsh : ∀ a, eRsh (algebraMap (ResidueField Rp) ksep
      (residue Rp a)) = residue Rsh (algebraMap Rp Rsh a))
    (eSsh : ksep ≃+* ResidueField Ssh) (heSsh : ∀ b, eSsh (algebraMap (ResidueField Sq) ksep
      (residue Sq b)) = residue Ssh (algebraMap Sq Ssh b)) :
    ∃ g : Rsh →ₐ[Rh] Ssh, IsLocalHom g ∧
      (∀ a, eSsh.symm (residue Ssh (g a)) = eRsh.symm (residue Rsh a)) ∧
      ∃ e : Ssh ≃ₐ[Sh] Sh ⊗[Rh] Rsh, ∀ a, e (g a) = Algebra.TensorProduct.includeRight a := by
  have := isLocalHom (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  have : IsLocalHom (algebraMap Rp Sh) := by
    rw [IsScalarTower.algebraMap_eq Rp Sq Sh]; infer_instance
  have : IsLocalHom (algebraMap Rh Sh) :=
    isLocalHom_algHom (L := ResidueField Rp) (IsScalarTower.toAlgHom Rp Rh Sh)
  have := henselian (R := Sq) (L := ResidueField Sq) (Rh := Sh)
  have : IsLocalHom (algebraMap Sh Ssh) :=
    have := isLocalHom (R := Sq) (L := ksep) (Rh := Ssh)
    isLocalHom_algHom (L := ResidueField Sq) (IsScalarTower.toAlgHom Sq Sh Ssh)
  obtain ⟨g, hg⟩ := exists_strictHenselization_algHom (Rh := Rh) (Sq := Sq) hksep eRsh heRsh eSsh
    heSsh
  obtain ⟨_, hm⟩ :=
    isIntegral_and_map_maximalIdeal (Rp := Rp) (Rh := Rh) (Rsh := Rsh) (ksep := ksep)
  obtain ⟨_, hmT⟩ := henselianLocalRing_tensorProduct Rh Sh Rsh
    (bijective_residueField_map_henselization hres) hm
  exact ⟨g, ⟨(isLocalHom_of_residue_eq g.toRingHom (eRsh.symm.trans eSsh).toRingHom
    hg).map_nonunit⟩, fun a => by simp [hg],
    exists_algEquiv_of_residue_eq (Rp := Rp) (Sq := Sq) (ksep := ksep) hmT _ g hg⟩

end BaseChange

end IsLocalRing.IsHenselization

open IsLocalRing.IsHenselization in
/-- **The strict henselization as a base change of the henselization** (Stacks 0C2Z). Let
`R → S` be a ring map and let `q` be a prime of `S` lying over the prime `p` of `R` such that
`κ(p) → κ(q)` is an isomorphism, and let `κ^sep` be a separable algebraic closure of
`κ(p) = κ(q)`. Let `(R_p)^h → (S_q)^h` be henselizations over `R_p → S_q` and let `(R_p)^{sh}`,
`(S_q)^{sh}` be strict henselizations with respect to `κ^sep`. Then the local map
`(R_p)^{sh} → (S_q)^{sh}` over `(R_p)^h` inducing the identity of `κ^sep` identifies
`(S_q)^{sh}` with `(S_q)^h ⊗_{(R_p)^h} (R_p)^{sh}`. -/
@[stacks 0C2Z "The equality of the source is an isomorphism of `(S_q)^h`-algebras
`Ssh ≃ₐ[Sh] Sh ⊗[Rh] Rsh` compatible with the local map `Rsh → Ssh` over `Rh` inducing the identity
of `κ^sep` (via `eRsh`, `eSsh`), which is part of the statement. Henselizations and strict
henselizations are `IsHenselization` with residue field `κ` and `κ^sep`. All seven carriers — `R`,
`S`, `κ^sep`, `(R_p)^h`, `(S_q)^h`, `(R_p)^{sh}`, `(S_q)^{sh}` — lie in mutually independent
universes."]
theorem IsLocalRing.IsHenselization.exists_algEquiv_tensorProduct_strictHenselization_atPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (hres : Function.Bijective
      (ResidueField.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))
    (ksep : Type w) [Field ksep] [Algebra (ResidueField (Localization.AtPrime p)) ksep]
    [Algebra (ResidueField (Localization.AtPrime q)) ksep]
    [IsSepClosure (ResidueField (Localization.AtPrime p)) ksep]
    [IsSepClosure (ResidueField (Localization.AtPrime q)) ksep]
    (hksep : ∀ a, algebraMap (ResidueField (Localization.AtPrime q)) ksep
      (ResidueField.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) a) =
        algebraMap (ResidueField (Localization.AtPrime p)) ksep a)
    (Rh : Type x) [CommRing Rh] [IsLocalRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselization (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)) Rh]
    (Sh : Type y) [CommRing Sh] [IsLocalRing Sh] [Algebra (Localization.AtPrime q) Sh]
    [IsHenselization (Localization.AtPrime q) (ResidueField (Localization.AtPrime q)) Sh]
    [Algebra (Localization.AtPrime p) Sh] [Algebra Rh Sh]
    [IsScalarTower (Localization.AtPrime p) Rh Sh]
    [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sh]
    [IsLocalHom (algebraMap Rh Sh)]
    (Rsh : Type z) [CommRing Rsh] [IsLocalRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [Algebra Rh Rsh] [IsScalarTower (Localization.AtPrime p) Rh Rsh]
    [IsHenselization (Localization.AtPrime p) ksep Rsh]
    (Ssh : Type t) [CommRing Ssh] [IsLocalRing Ssh] [Algebra (Localization.AtPrime q) Ssh]
    [Algebra Sh Ssh] [Algebra (Localization.AtPrime p) Ssh] [Algebra Rh Ssh]
    [IsScalarTower (Localization.AtPrime q) Sh Ssh]
    [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh]
    [IsScalarTower (Localization.AtPrime p) Rh Ssh] [IsScalarTower Rh Sh Ssh]
    [IsHenselization (Localization.AtPrime q) ksep Ssh]
    (eRsh : ksep ≃+* ResidueField Rsh)
    (heRsh : ∀ a, eRsh (algebraMap (ResidueField (Localization.AtPrime p)) ksep
      (residue (Localization.AtPrime p) a)) =
        residue Rsh (algebraMap (Localization.AtPrime p) Rsh a))
    (eSsh : ksep ≃+* ResidueField Ssh)
    (heSsh : ∀ b, eSsh (algebraMap (ResidueField (Localization.AtPrime q)) ksep
      (residue (Localization.AtPrime q) b)) =
        residue Ssh (algebraMap (Localization.AtPrime q) Ssh b)) :
    ∃ g : Rsh →ₐ[Rh] Ssh, IsLocalHom g ∧
      (∀ a, eSsh.symm (residue Ssh (g a)) = eRsh.symm (residue Rsh a)) ∧
      ∃ e : Ssh ≃ₐ[Sh] Sh ⊗[Rh] Rsh, ∀ a, e (g a) = Algebra.TensorProduct.includeRight a :=
  exists_algEquiv_tensorProduct_strictHenselization hres hksep eRsh heRsh eSsh heSsh
