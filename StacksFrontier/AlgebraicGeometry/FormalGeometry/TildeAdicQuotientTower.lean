module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientRestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# The adic quotient tower of `M̃` on an open of an affine scheme is the tower of `M̃ / Iⁿ M̃`

Let `A` be a commutative ring, `I` and `𝔞` ideals of `A`, and put `X = Spec(A)` and
`U = X ∖ V(𝔞)`. Let `M` be an `A`-module and let `ℱ = M̃|_U` be the restriction to `U` of the
module sheaf attached to `M`. This file identifies the tower

`n ↦ ℱ / Iⁿ ℱ`     with     `n ↦ (M / Iⁿ M)~|_U`

as an isomorphism of inverse systems, compatibly with the quotient projections out of `ℱ` and
hence with every transition map.

This is the module tower the four-term sequence of local cohomology is fed with: its sections on
`U` are the right-hand side of the comparison of Stacks 0DXQ, and each term is the restriction of
the sheaf attached to an honest `A`-module, which is what makes the local-cohomology computation
of `Γ(U, ·)` available term by term.

Two ingredients combine. On `Spec(A)` the associated-sheaf functor turns the module surjection
`M ⟶ M / Iⁿ M`, whose kernel is `Iⁿ M`, into the sheaf quotient of `M̃` by the `n`-th power of
`I · 𝒪_X`: that is `Stacks.Algebraization.tildeQuotientIso`. Restriction along the open immersion
`U ⟶ X` then commutes with the whole tower, by
`Stacks.Algebraization.adicQuotientRestrictOpenTowerIso`, which is the naturality in `n` of
`Stacks.Algebraization.restrictIdealPowerQuotientIso` — the term-by-term statement that
restriction commutes with the subsheaf `Iⁿ M̃` and with its cokernel, already available from
`Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap`. That restriction carries `I · 𝒪_X`
to `I · 𝒪_U` by `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap`.

## Main definitions

* `Stacks.Algebraization.tildeIdealSheaf` — the quasi-coherent ideal sheaf `I · 𝒪` on `Spec R`.
* `Stacks.Algebraization.tildeQuotientIso` — a surjection of `R`-modules with kernel `Iⁿ M`
  becomes, after `~`, the sheaf quotient of `M̃` by the `n`-th ideal-power multiple.
* `Stacks.Algebraization.tildeAdicQuotientTowerIso` — on `Spec R`, the tower `n ↦ M̃ / Iⁿ M̃` is
  the tower `n ↦ (M / Iⁿ M)~`.
* `Stacks.Algebraization.quotientSystemNearVanishingTildeObjIso` — the tower
  `n ↦ (M̃|_U) / Iⁿ (M̃|_U)` is the tower `n ↦ (M / Iⁿ M)~|_U`.
* `Stacks.Algebraization.quotientSystemNearVanishingTowerIso` — the same for a module on `U`
  presented as `M̃|_U`.

## Main results

* `Stacks.Algebraization.tilde_idealPowerMultiple_eq_bot` — if `Iⁿ` annihilates `M` then
  `Iⁿ M̃ = 0`.
* `Stacks.Algebraization.π_comp_tildeAdicQuotientIso_hom`,
  `Stacks.Algebraization.π_comp_quotientSystemNearVanishingTildeObjIso_hom_app` and
  `Stacks.Algebraization.π_comp_quotientSystemNearVanishingTowerIso_hom_app` — all three
  comparisons respect the quotient projections, which is what pins them down: two quotients of
  one module are isomorphic over it exactly when they are quotients by the same subsheaf.
* `Stacks.Algebraization.exists_finiteModule_quotientSystemNearVanishing_iso` — over a Noetherian
  ring, for a *coherent* module `ℱ` on `U` there is a finite `A`-module `M` with
  `ℱ / Iⁿ ℱ ≅ (M / Iⁿ M)~|_U` as towers.

## Implementation notes

`M` is an `R`-module while the ideal sheaf `I · 𝒪_{Spec R}` and the submodule `Iⁿ M̃` are stated
with the ring `Γ(Spec R, ⊤)` of global functions. The two scalar actions on the global sections
of a module on `Spec R` agree through `AlgebraicGeometry.Scheme.ΓSpecIso`, by
`AlgebraicGeometry.Scheme.Modules.smul_Spec_def`, which is a `rfl`; the two lemmas
`Stacks.Algebraization.mem_map_smul_top` and
`Stacks.Algebraization.map_smul_top_eq_bot_of_eq_bot` are the two directions of that translation
that the proofs below need, stated as a membership and as a vanishing rather than as an
inequality of submodules, because submodules over the two rings cannot be compared with `≤`.

`Stacks.Coherent.affineTildeQuotientIso` is the same statement as
`Stacks.Algebraization.tildeQuotientIso` for `Stacks.Coherent.affineTilde` — the quasi-inverse of
global sections on an arbitrary affine scheme — rather than for
`AlgebraicGeometry.tilde.functor`. It is not usable here: its module lives over `Γ(X, ⊤)`, while
`Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde` and the local cohomology of
chapter 51 present everything over the ring itself. The proof below is the same argument carried
out with `AlgebraicGeometry.tilde.adjunction` and its unit
`AlgebraicGeometry.tilde.isoTop`, so no comparison of the two associated-sheaf functors is
needed.

The isomorphism is built from the universal property on both sides rather than as a map with an
inverse: the descent of `M̃ ⟶ (M / Iⁿ M)~` through the quotient projection exists because `Iⁿ`
annihilates `(M / Iⁿ M)~`, the descent in the other direction exists because the quotient
projection kills `Iⁿ M̃` and `~` is a left adjoint, and the two composites are identities because
both projections are epimorphisms.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.LocalCohomology

/-! ### The two scalar actions on global sections of a module on `Spec R` -/

variable {R : CommRingCat.{u}}

/-- The `R`-action on the global sections of a module on `Spec R` is the action of the ring
`Γ(Spec R, ⊤)` of global functions through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
public lemma smul_top_eq_ΓSpecIso_smul (N : (Spec R).Modules) (r : R)
    (x : Γ(N, (⊤ : (Spec R).Opens))) :
    r • x = (Scheme.ΓSpecIso R).inv r • x := by
  rw [AlgebraicGeometry.Scheme.Modules.smul_Spec_def,
    show (Opens.leTop (⊤ : (Spec R).Opens)).op = 𝟙 (op (⊤ : (Spec R).Opens)) from
      Subsingleton.elim _ _, (Spec R).presheaf.map_id]
  rfl

/-- A global section in `I • Γ(N, ⊤)` for the `R`-action lies in `(I · Γ(Spec R, ⊤)) • Γ(N, ⊤)`
for the action of the global functions. -/
public lemma mem_map_smul_top (N : (Spec R).Modules) (I : Ideal R)
    {x : Γ(N, (⊤ : (Spec R).Opens))}
    (hx : x ∈ I • (⊤ : Submodule R Γ(N, (⊤ : (Spec R).Opens)))) :
    x ∈ (I.map (Scheme.ΓSpecIso R).inv.hom) •
      (⊤ : Submodule Γ(Spec R, ⊤) Γ(N, (⊤ : (Spec R).Opens))) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) fun _ _ => Submodule.add_mem _
  rw [smul_top_eq_ΓSpecIso_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

/-- If `I` annihilates the global sections of a module on `Spec R` for the `R`-action, then its
extension to the global functions annihilates them for that ring's action. -/
public lemma map_smul_top_eq_bot_of_eq_bot (N : (Spec R).Modules) (I : Ideal R)
    (h : I • (⊤ : Submodule R Γ(N, (⊤ : (Spec R).Opens))) = ⊥) :
    (I.map (Scheme.ΓSpecIso R).inv.hom) •
        (⊤ : Submodule Γ(Spec R, ⊤) Γ(N, (⊤ : (Spec R).Opens))) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun b hb x _ => ?_) bot_le
  have hsurj : Function.Surjective (Scheme.ΓSpecIso R).inv.hom :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hb
  rw [Submodule.mem_bot]
  have hx : a • x ∈ I • (⊤ : Submodule R Γ(N, (⊤ : (Spec R).Opens))) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rw [h, Submodule.mem_bot] at hx
  rw [← smul_top_eq_ΓSpecIso_smul]
  exact hx

/-! ### The ideal sheaf generated by an ideal of the base ring -/

/-- The quasi-coherent ideal sheaf `I · 𝒪` on `Spec R` generated by an ideal `I` of `R`. -/
public abbrev tildeIdealSheaf (R : CommRingCat.{u}) (I : Ideal R) : (Spec R).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom)

/-- **`~` carries annihilation to the vanishing of the ideal-power multiple.** If `Iⁿ`
annihilates `N` then the subsheaf `(I · 𝒪)ⁿ Ñ` of `Ñ` is zero. -/
public lemma tilde_idealPowerMultiple_eq_bot (I : Ideal R) (n : ℕ) (N : ModuleCat.{u} R)
    (h : I ^ n • (⊤ : Submodule R N) = ⊥) :
    idealPowerMultiple (tildeIdealSheaf R I) n ((tilde.functor R).obj N) = ⊥ := by
  apply affine_idealPowerMultiple_eq_bot
  rw [← Ideal.map_pow]
  apply map_smul_top_eq_bot_of_eq_bot
  let e := (tilde.isoTop N).toLinearEquiv
  have h2 := map_smul_top_local (I ^ n) e.toLinearMap e.surjective
  rw [h, Submodule.map_bot] at h2
  exact h2.symm

/-! ### The associated sheaf of a quotient by a power of an ideal -/

/-- **A surjection with ideal-power kernel becomes a sheaf quotient.** For a surjection
`p : M ⟶ N` of `R`-modules with `ker p = Iⁿ M`, the map `p̃ : M̃ ⟶ Ñ` exhibits `Ñ` as the quotient
of `M̃` by the `n`-th power of the ideal sheaf `I · 𝒪` on `Spec R`, compatibly with the quotient
projection. -/
public noncomputable def tildeQuotientIso (I : Ideal R) (n : ℕ) {M N : ModuleCat.{u} R}
    (p : M ⟶ N) (hp : Function.Surjective p.hom)
    (hk : LinearMap.ker p.hom = I ^ n • (⊤ : Submodule R M)) :
    { e : idealPowerQuotient (tildeIdealSheaf R I) n ((tilde.functor R).obj M) ≅
        (tilde.functor R).obj N //
      cokernel.π (C := (Spec R).Modules)
          (idealPowerMultiple (tildeIdealSheaf R I) n ((tilde.functor R).obj M)).ι ≫ e.hom =
        (tilde.functor R).map p } := by
  let J : Ideal Γ(Spec R, ⊤) := I.map (Scheme.ΓSpecIso R).inv.hom
  let 𝒥 : (Spec R).IdealSheafData := Scheme.IdealSheafData.ofIdealTop J
  let L := tilde.functor R
  let adj := tilde.adjunction (R := R)
  let P := idealPowerMultiple 𝒥 n (L.obj M)
  let Q : (Spec R).Modules := cokernel (C := (Spec R).Modules) P.ι
  let π : L.obj M ⟶ Q := cokernel.π (C := (Spec R).Modules) P.ι
  have hN : I ^ n • (⊤ : Submodule R N) = ⊥ := by
    rw [← map_smul_top_local (I ^ n) p.hom hp, ← hk]
    rw [← Submodule.comap_bot, Submodule.map_comap_eq]
    simp
  have hbot : idealPowerMultiple 𝒥 n (L.obj N) = ⊥ :=
    tilde_idealPowerMultiple_eq_bot I n N hN
  let d : Q ⟶ L.obj N := idealPowerQuotientDesc 𝒥 n (L.map p) hbot
  have hd : π ≫ d = L.map p := idealPowerQuotientDesc_π 𝒥 n (L.map p) hbot
  let k : M ⟶ moduleSpecΓFunctor.obj Q := adj.homEquiv M Q π
  have hgen : J ^ n • (⊤ : Submodule Γ(Spec R, ⊤) Γ(L.obj M, (⊤ : (Spec R).Opens))) ≤
      P.toSubmodule.obj (op (⊤ : (Spec R).Opens)) := by
    have hh := (idealPowerMultiple_le_iff 𝒥 n (L.obj M) P).mp le_rfl
      ⟨⊤, isAffineOpen_top (Spec R)⟩
    rw [show 𝒥.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ = J from
      ofIdealTop_ideal_top (Spec R) J] at hh
    exact hh
  have hker : LinearMap.ker p.hom ≤ LinearMap.ker k.hom := by
    rw [hk]
    intro x hx
    let e := (tilde.isoTop M).toLinearEquiv
    have hex : e x ∈ I ^ n • (⊤ : Submodule R Γ(L.obj M, (⊤ : (Spec R).Opens))) := by
      have hh := Submodule.mem_map_of_mem (f := e.toLinearMap) hx
      rwa [map_smul_top_local (I ^ n) e.toLinearMap e.surjective] at hh
    have hex2 : e x ∈ J ^ n • (⊤ : Submodule Γ(Spec R, ⊤)
        Γ(L.obj M, (⊤ : (Spec R).Opens))) := by
      have hpow : (I ^ n).map (Scheme.ΓSpecIso R).inv.hom = J ^ n :=
        Ideal.map_pow _ I n
      exact hpow ▸ mem_map_smul_top (L.obj M) (I ^ n) hex
    have w := cokernel.condition (C := (Spec R).Modules) P.ι
    exact congrArg (fun f => f.val.app (op (⊤ : (Spec R).Opens)) ⟨e x, hgen hex2⟩) w
  let k' := (exists_desc_of_ker_le p k hp hker).choose
  have hk' : p ≫ k' = k := (exists_desc_of_ker_le p k hp hker).choose_spec
  let d' : L.obj N ⟶ Q := (adj.homEquiv N Q).symm k'
  have hd' : L.map p ≫ d' = π := by
    apply (adj.homEquiv M Q).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hk'
  have hpepi : Epi p := (ModuleCat.epi_iff_surjective _).mpr hp
  have hLepi : Epi (L.map p) := inferInstance
  have h1 : d ≫ d' = 𝟙 Q := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hd, hd', Category.comp_id]
  have h2 : d' ≫ d = 𝟙 (L.obj N) := by
    apply (cancel_epi (L.map p)).mp
    rw [← Category.assoc, hd', hd, Category.comp_id]
  exact ⟨⟨d, d', h1, h2⟩, hd⟩

/-! ### The tower of ideal-power quotients of `M̃` on `Spec R` -/

/-- **The levelwise identification on `Spec R`.** The quotient of `M̃` by the `n`-th power of
`I · 𝒪` is the sheaf attached to `M / Iⁿ M`. -/
public noncomputable def tildeAdicQuotientIso (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (adicQuotientSystem (tildeIdealSheaf R I) ((tilde.functor R).obj M)).obj ⟨n⟩ ≅
      (tilde.functor R).obj ((idealPowerQuotientTower I M).obj ⟨n⟩) :=
  (tildeQuotientIso I n (ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule R M))))
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)).1

/-- The levelwise identification respects the quotient projections. -/
@[reassoc]
public lemma π_comp_tildeAdicQuotientIso_hom (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    cokernel.π (C := (Spec R).Modules)
        (idealPowerMultiple (tildeIdealSheaf R I) n ((tilde.functor R).obj M)).ι ≫
      (tildeAdicQuotientIso I M n).hom =
      (tilde.functor R).map ((idealPowerQuotientCone I M).π.app ⟨n⟩) :=
  (tildeQuotientIso I n _ (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)).2

/-- The naturality square of `Stacks.Algebraization.tildeAdicQuotientIso`. Both legs compose
with the quotient projection at the smaller index to the sheaf map of the projection
`M ⟶ M / Iʲ M`. -/
public theorem tildeAdicQuotientIso_naturality (I : Ideal R) (M : ModuleCat.{u} R)
    {i j : ℕᵒᵖ} (g : i ⟶ j) :
    (adicQuotientSystem (tildeIdealSheaf R I) ((tilde.functor R).obj M)).map g ≫
        (tildeAdicQuotientIso I M j.unop).hom =
      (tildeAdicQuotientIso I M i.unop).hom ≫
        (tilde.functor R).map ((idealPowerQuotientTower I M).map g) := by
  apply (cancel_epi (cokernel.π (C := (Spec R).Modules)
    (idealPowerMultiple (tildeIdealSheaf R I) i.unop ((tilde.functor R).obj M)).ι)).mp
  have hleft : cokernel.π (C := (Spec R).Modules)
      (idealPowerMultiple (tildeIdealSheaf R I) i.unop ((tilde.functor R).obj M)).ι ≫
      ((adicQuotientSystem (tildeIdealSheaf R I) ((tilde.functor R).obj M)).map g ≫
        (tildeAdicQuotientIso I M j.unop).hom) =
      (tilde.functor R).map ((idealPowerQuotientCone I M).π.app j) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun q => q ≫ (tildeAdicQuotientIso I M j.unop).hom)
      (quotientMapOfLE_π (idealPowerMultiple_antitone (tildeIdealSheaf R I)
        ((tilde.functor R).obj M) (leOfHom g.unop)))) ?_
    exact π_comp_tildeAdicQuotientIso_hom I M j.unop
  have hright : cokernel.π (C := (Spec R).Modules)
      (idealPowerMultiple (tildeIdealSheaf R I) i.unop ((tilde.functor R).obj M)).ι ≫
      ((tildeAdicQuotientIso I M i.unop).hom ≫
        (tilde.functor R).map ((idealPowerQuotientTower I M).map g)) =
      (tilde.functor R).map ((idealPowerQuotientCone I M).π.app j) :=
    (π_comp_tildeAdicQuotientIso_hom_assoc I M i.unop
        ((tilde.functor R).map ((idealPowerQuotientTower I M).map g))).trans
      (((tilde.functor R).map_comp _ _).symm.trans
        (congrArg (tilde.functor R).map ((idealPowerQuotientCone I M).w g)))
  exact hleft.trans hright.symm

/-- **The tower of ideal-power quotients of `M̃` on `Spec R`.** The tower `n ↦ M̃ / (I · 𝒪)ⁿ M̃` is
the tower `n ↦ (M / Iⁿ M)~`, compatibly with every transition map. -/
public noncomputable def tildeAdicQuotientTowerIso (I : Ideal R) (M : ModuleCat.{u} R) :
    adicQuotientSystem (tildeIdealSheaf R I) ((tilde.functor R).obj M) ≅
      idealPowerQuotientTower I M ⋙ tilde.functor R :=
  NatIso.ofComponents (fun n => tildeAdicQuotientIso I M n.unop)
    (fun g => tildeAdicQuotientIso_naturality I M g)

/-- The tower identification acts levelwise as `Stacks.Algebraization.tildeAdicQuotientIso`. -/
public lemma tildeAdicQuotientTowerIso_hom_app (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕᵒᵖ) :
    (tildeAdicQuotientTowerIso I M).hom.app n = (tildeAdicQuotientIso I M n.unop).hom :=
  rfl

/-! ### The tower on the complement of a zero locus -/

/-- The ideal sheaf `I · 𝒪_U` on `U = Spec(A) ∖ V(𝔞)` is the restriction of the ideal sheaf
`I · 𝒪_X` on `X = Spec(A)`. -/
public lemma idealSheafNearVanishing_eq_comap (A : Type u) [CommRing A] (I a : Ideal A) :
    idealSheafNearVanishing A I a =
      (tildeIdealSheaf (CommRingCat.of A) I).comap (complementZeroLocus A a).ι :=
  Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap A I _

/-- **The adic quotient tower of `M̃|_U`.** For `U = Spec(A) ∖ V(𝔞)` and an `A`-module `M`, the
tower `n ↦ (M̃|_U) / Iⁿ (M̃|_U)` is the tower `n ↦ (M / Iⁿ M)~|_U`, compatibly with every
transition map. -/
public noncomputable def quotientSystemNearVanishingTildeObjIso (A : Type u) [CommRing A]
    (I a : Ideal A) (M : ModuleCat.{u} A) :
    quotientSystemNearVanishing A I a
        (((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A a).ι) ≅
      (idealPowerQuotientTower I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι :=
  adicQuotientRestrictOpenTowerIso (complementZeroLocus A a).ι
    (tildeIdealSheaf (CommRingCat.of A) I) ((tilde.functor (CommRingCat.of A)).obj M)
    (idealSheafNearVanishing_eq_comap A I a)
    (tildeAdicQuotientTowerIso (R := CommRingCat.of A) I M)

/-- **The tower identification respects the quotient projections.** The projection of `M̃|_U` onto
its `n`-th adic quotient is, under the identification, the restriction to `U` of the sheaf map of
the module projection `M ⟶ M / Iⁿ M`. -/
public lemma π_comp_quotientSystemNearVanishingTildeObjIso_hom_app (A : Type u) [CommRing A]
    (I a : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    cokernel.π (C := (complementZeroLocus A a : Scheme).Modules)
        (idealPowerMultiple (idealSheafNearVanishing A I a) n
          (((tilde.functor (CommRingCat.of A)).obj M).restrict
            (complementZeroLocus A a).ι)).ι ≫
      (quotientSystemNearVanishingTildeObjIso A I a M).hom.app ⟨n⟩ =
      (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        ((tilde.functor (CommRingCat.of A)).map
          ((idealPowerQuotientCone I M).π.app ⟨n⟩)) :=
  (π_comp_adicQuotientRestrictOpenTowerIso_hom_app (complementZeroLocus A a).ι
      (tildeIdealSheaf (CommRingCat.of A) I) ((tilde.functor (CommRingCat.of A)).obj M)
      (idealSheafNearVanishing_eq_comap A I a)
      (tildeAdicQuotientTowerIso (R := CommRingCat.of A) I M) n).trans
    (congrArg (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
      (π_comp_tildeAdicQuotientIso_hom (R := CommRingCat.of A) I M n))

/-- **The adic quotient tower of a module on `U` presented as `M̃|_U`.** -/
public noncomputable def quotientSystemNearVanishingTowerIso (A : Type u) [CommRing A]
    (I a : Ideal A) (F : (complementZeroLocus A a : Scheme).Modules) (M : ModuleCat.{u} A)
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A a).ι) :
    quotientSystemNearVanishing A I a F ≅
      (idealPowerQuotientTower I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι :=
  adicQuotientRestrictOpenTowerIsoOfIso (complementZeroLocus A a).ι
    (tildeIdealSheaf (CommRingCat.of A) I) ((tilde.functor (CommRingCat.of A)).obj M)
    (idealSheafNearVanishing_eq_comap A I a)
    (tildeAdicQuotientTowerIso (R := CommRingCat.of A) I M) e

/-- The identification for a presented module respects the quotient projections. -/
public lemma π_comp_quotientSystemNearVanishingTowerIso_hom_app (A : Type u) [CommRing A]
    (I a : Ideal A) (F : (complementZeroLocus A a : Scheme).Modules) (M : ModuleCat.{u} A)
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A a).ι) (n : ℕ) :
    cokernel.π (C := (complementZeroLocus A a : Scheme).Modules)
        (idealPowerMultiple (idealSheafNearVanishing A I a) n F).ι ≫
      (quotientSystemNearVanishingTowerIso A I a F M e).hom.app ⟨n⟩ =
      e.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        ((tilde.functor (CommRingCat.of A)).map
          ((idealPowerQuotientCone I M).π.app ⟨n⟩)) :=
  (π_comp_adicQuotientRestrictOpenTowerIsoOfIso_hom_app (complementZeroLocus A a).ι
      (tildeIdealSheaf (CommRingCat.of A) I) ((tilde.functor (CommRingCat.of A)).obj M)
      (idealSheafNearVanishing_eq_comap A I a)
      (tildeAdicQuotientTowerIso (R := CommRingCat.of A) I M) e n).trans
    (congrArg (fun q => e.hom ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map q)
      (π_comp_tildeAdicQuotientIso_hom (R := CommRingCat.of A) I M n))

/-- **The adic quotient tower of a coherent module on `U = Spec(A) ∖ V(𝔞)`.** Over a Noetherian
ring, for a coherent module `ℱ` on `U` there is a finite `A`-module `M` with
`ℱ / Iⁿ ℱ ≅ (M / Iⁿ M)~|_U` as inverse systems.

The module is the one of Stacks 0BK0 (1), by
`Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`. -/
public theorem exists_finiteModule_quotientSystemNearVanishing_iso (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent] :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      Nonempty (quotientSystemNearVanishing A I a F ≅
        (idealPowerQuotientTower I M ⋙ tilde.functor (CommRingCat.of A)) ⋙
          Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι) := by
  obtain ⟨M, hMfin, ⟨e⟩⟩ := exists_finiteModule_iso_restrict_tilde A a F
  exact ⟨M, hMfin, ⟨quotientSystemNearVanishingTowerIso A I a F M e⟩⟩

end Stacks.Algebraization

end
