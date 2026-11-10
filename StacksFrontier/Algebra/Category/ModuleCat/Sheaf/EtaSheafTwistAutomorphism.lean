module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComplex

/-!
# Automorphisms of the décalage induced by automorphisms of the twisted terms

Let `X` be a ringed space, `I ⊆ 𝒪_X` an invertible ideal sheaf and `F^•` a cochain complex of
`I`-torsion-free `𝒪_X`-modules.  The degree-`n` term of the décalage `η_I F^•` is the fibre
product of the cospan

`I^{⊗ n} ⊗ F^n ⟶ I^{⊗ n} ⊗ F^{n+1} ⟵ I^{⊗ (n+1)} ⊗ F^{n+1}`

formed by the twisted differential and the inclusion of consecutive ideal powers.  An automorphism
of each of these cospans — automorphisms of the three twisted terms commuting with the two maps —
induces an automorphism of the fibre product, and these assemble into an automorphism of the
complex `η_I F^•`.

The point of the construction is the uniqueness statement that comes with it: two maps of
complexes into `η_I F^•` whose two projections differ by such a family of automorphisms differ by
the induced automorphism of `η_I F^•`.  This is how two comparison maps into a décalage, built
from two different identifications of the twisted terms, are shown to agree up to an
automorphism, without ever comparing the identifications themselves.

## Main definitions

* `Stacks.IdealTorsion.Eta.EtaTwist`: a family of automorphisms of the cospans defining the terms
  of `η_I F^•`.
* `Stacks.IdealTorsion.Eta.EtaTwist.iso`: the induced automorphism of the complex `η_I F^•`.

## Main results

* `Stacks.IdealTorsion.Eta.EtaTwist.iso_hom_f_fst` and `iso_hom_f_snd`: the induced automorphism
  acts on the two projections by the given automorphisms.
* `Stacks.IdealTorsion.Eta.EtaTwist.eq_comp_iso_hom`: **two maps into `η_I F^•` whose projections
  differ by a twist differ by the induced automorphism.**

## Implementation notes

As in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafCohomology.lean`, the degree-`n` term
of `η_I F^•` is a fibre product that is not unfolded at instance transparency, so every square is
proved at the `etaTerm` spelling, through `Stacks.IdealTorsion.Eta.etaDifferentialData`, and
crossed to `η_I F^•` by `Stacks.IdealTorsion.Eta.etaObj_d_eq`.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u})

variable (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)))
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property I]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))) ℤ)

/-- **A twist of the cospans defining the décalage.**  For every degree `n`, automorphisms of the
twisted terms `I^{⊗ n} ⊗ F^n` and `I^{⊗ n} ⊗ F^{n+1}` commuting with the twisted differential,
such that the automorphism of `I^{⊗ n} ⊗ F^{n+1}` and that of `I^{⊗ (n+1)} ⊗ F^{n+1}` (the
degree-`(n + 1)` one of the first family) commute with the inclusion of consecutive ideal
powers. -/
structure EtaTwist where
  /-- The automorphism of `I^{⊗ n} ⊗ F^n`. -/
  cur : ∀ n : ℤ, idealPowerTerm X I n (F.X n) ≅ idealPowerTerm X I n (F.X n)
  /-- The automorphism of `I^{⊗ n} ⊗ F^{n+1}`. -/
  nxt : ∀ n : ℤ, idealPowerTerm X I n (F.X (n + 1)) ≅ idealPowerTerm X I n (F.X (n + 1))
  /-- The automorphisms commute with the twisted differential. -/
  map_comm : ∀ n : ℤ, idealPowerMap X I n (F.d n (n + 1)) ≫ (nxt n).hom =
    (cur n).hom ≫ idealPowerMap X I n (F.d n (n + 1))
  /-- The automorphisms commute with the inclusion of consecutive ideal powers. -/
  incl_comm : ∀ n : ℤ, idealPowerIncl X I ι n (F.X (n + 1)) ≫ (nxt n).hom =
    (cur (n + 1)).hom ≫ idealPowerIncl X I ι n (F.X (n + 1))

namespace EtaTwist

variable {X I ι F}

/-- The inverse twist. -/
def symm (θ : EtaTwist X I ι F) : EtaTwist X I ι F where
  cur n := (θ.cur n).symm
  nxt n := (θ.nxt n).symm
  map_comm n := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← θ.map_comm n,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  incl_comm n := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← θ.incl_comm n,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The map induced by a twist on the degree-`n` term of the décalage. -/
noncomputable def termHom (θ : EtaTwist X I ι F) (n : ℤ) :
    etaTerm X I ι F n ⟶ etaTerm X I ι F n :=
  pullback.map _ _ _ _ (θ.cur n).hom (θ.cur (n + 1)).hom (θ.nxt n).hom
    (θ.map_comm n) (θ.incl_comm n)

/-- The map induced by a twist acts on the first projection by the degree-`n` automorphism. -/
theorem termHom_fst (θ : EtaTwist X I ι F) (n : ℤ) :
    θ.termHom n ≫ etaFst X I ι F n = etaFst X I ι F n ≫ (θ.cur n).hom :=
  pullback.lift_fst _ _ _

/-- The map induced by a twist acts on the second projection by the degree-`(n + 1)`
automorphism. -/
theorem termHom_snd (θ : EtaTwist X I ι F) (n : ℤ) :
    θ.termHom n ≫ etaSnd X I ι F n = etaSnd X I ι F n ≫ (θ.cur (n + 1)).hom :=
  pullback.lift_snd _ _ _

/-- The map induced by a twist, followed by that of the inverse twist, is the identity. -/
theorem termHom_symm_termHom (θ : EtaTwist X I ι F) (n : ℤ) :
    θ.termHom n ≫ θ.symm.termHom n = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, termHom_fst, ← Category.assoc, termHom_fst, Category.assoc]
    change etaFst X I ι F n ≫ (θ.cur n).hom ≫ (θ.cur n).inv = _
    rw [Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, termHom_snd, ← Category.assoc, termHom_snd, Category.assoc]
    change etaSnd X I ι F n ≫ (θ.cur (n + 1)).hom ≫ (θ.cur (n + 1)).inv = _
    rw [Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- The inverse of the inverse twist is the original twist. -/
theorem symm_symm (θ : EtaTwist X I ι F) : θ.symm.symm = θ := by
  cases θ
  rfl

variable [Mono ι] (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))

/-- The induced maps on terms commute with the differential of the décalage, at the `etaTerm`
spelling.  On the first projection both sides are the second projection followed by the
degree-`(n + 1)` automorphism; on the second projection both vanish. -/
theorem termHom_comm (θ : EtaTwist X I ι F) (n : ℤ) :
    θ.termHom n ≫ (etaDifferentialData X I ι F hF).d n =
      (etaDifferentialData X I ι F hF).d n ≫ θ.termHom (n + 1) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, (etaDifferentialData X I ι F hF).d_fst n, termHom_snd,
      Category.assoc]
    change _ = (etaDifferentialData X I ι F hF).d n ≫
      (θ.termHom (n + 1) ≫ etaFst X I ι F (n + 1))
    rw [termHom_fst, ← Category.assoc, (etaDifferentialData X I ι F hF).d_fst n]
  · rw [Category.assoc]
    change θ.termHom n ≫ ((etaDifferentialData X I ι F hF).d n ≫ etaSnd X I ι F (n + 1)) =
      (etaDifferentialData X I ι F hF).d n ≫ (θ.termHom (n + 1) ≫ etaSnd X I ι F (n + 1))
    rw [etaDifferentialData_d_comp_etaSnd X I ι F hF n, comp_zero, termHom_snd,
      ← Category.assoc, etaDifferentialData_d_comp_etaSnd X I ι F hF n, zero_comp]

/-- The map of complexes induced by a twist. -/
noncomputable def hom (θ : EtaTwist X I ι F) : etaObj X I ι F hF ⟶ etaObj X I ι F hF where
  f n := θ.termHom n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [etaObj_d_eq]
    exact θ.termHom_comm hF i

/-- The degree-`n` component of the map of complexes induced by a twist is `termHom θ n`. -/
theorem hom_f (θ : EtaTwist X I ι F) (n : ℤ) : (θ.hom hF).f n = θ.termHom n := rfl

/-- **The automorphism of the décalage induced by a twist.** -/
noncomputable def iso (θ : EtaTwist X I ι F) : etaObj X I ι F hF ≅ etaObj X I ι F hF where
  hom := θ.hom hF
  inv := θ.symm.hom hF
  hom_inv_id := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    exact θ.termHom_symm_termHom n
  inv_hom_id := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    have h := θ.symm.termHom_symm_termHom n
    rw [symm_symm] at h
    exact h

/-- The induced automorphism acts on the first projection by the given automorphism. -/
theorem iso_hom_f_fst (θ : EtaTwist X I ι F) (n : ℤ) :
    (θ.iso hF).hom.f n ≫ etaFst X I ι F n = etaFst X I ι F n ≫ (θ.cur n).hom :=
  θ.termHom_fst n

/-- The induced automorphism acts on the second projection by the given automorphism in the next
degree. -/
theorem iso_hom_f_snd (θ : EtaTwist X I ι F) (n : ℤ) :
    (θ.iso hF).hom.f n ≫ etaSnd X I ι F n = etaSnd X I ι F n ≫ (θ.cur (n + 1)).hom :=
  θ.termHom_snd n

/-- **Two maps into the décalage whose projections differ by a twist differ by the induced
automorphism.**  A map into `η_I F^•` is determined by its two projections in every degree, and
the induced automorphism acts on the projections by the twist. -/
theorem eq_comp_iso_hom (θ : EtaTwist X I ι F)
    {S : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))) ℤ}
    (a b : S ⟶ etaObj X I ι F hF)
    (hfst : ∀ n : ℤ, a.f n ≫ etaFst X I ι F n = b.f n ≫ etaFst X I ι F n ≫ (θ.cur n).hom)
    (hsnd : ∀ n : ℤ,
      a.f n ≫ etaSnd X I ι F n = b.f n ≫ etaSnd X I ι F n ≫ (θ.cur (n + 1)).hom) :
    a = b ≫ (θ.iso hF).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f]
  refine pullback.hom_ext ?_ ?_
  · change a.f n ≫ etaFst X I ι F n = (b.f n ≫ θ.termHom n) ≫ etaFst X I ι F n
    exact (hfst n).trans ((congrArg (fun k => b.f n ≫ k) (θ.termHom_fst n).symm).trans
      (Category.assoc _ _ _).symm)
  · change a.f n ≫ etaSnd X I ι F n = (b.f n ≫ θ.termHom n) ≫ etaSnd X I ι F n
    exact (hsnd n).trans ((congrArg (fun k => b.f n ≫ k) (θ.termHom_snd n).symm).trans
      (Category.assoc _ _ _).symm)

end EtaTwist

end Stacks.IdealTorsion.Eta

end
