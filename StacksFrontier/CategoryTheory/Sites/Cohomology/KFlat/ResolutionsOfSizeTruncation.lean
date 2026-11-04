module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize

/-!
# The sequential flat resolution of a complex, with the truncation at each stage

`Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize` presents the resolution
of Stacks 06YS as the colimit of a sequence of bounded above complexes of flat `O`-modules. In
its construction the `n`-th complex of the sequence resolves the truncation `τ_{≤ n}` of the
complex. This file records that fact as well.

## Main results

* `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize_truncLE`: the
  sequential resolution, with a quasi-isomorphism from the `n`-th stage to `τ_{≤ n}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.KFlatResolution

noncomputable section

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- **The resolution of Stacks 06YS as a sequential colimit, stage by stage.** Every complex of
`O`-modules receives a termwise surjective quasi-isomorphism from the colimit of a sequence of
bounded above complexes of flat `O`-modules, the `n`-th of which resolves the truncation
`τ_{≤ n}` of the complex. -/
theorem exists_resolution_colimit_ofSize_truncLE
    (G : CochainComplex (ModOfSize.{v, u, w} R) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (ModOfSize.{v, u, w} R) ℤ) (f : colimit D ⟶ G),
      (∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b) ∧
      (∀ (n : ℕ) (i : ℤ),
        AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
          ((D.obj n).X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) ∧
      (∀ n : ℕ, ∃ q : D.obj n ⟶ G.truncLE (n : ℤ), QuasiIso q) := by
  have := hasColimitsOfShape_nat_ofSize R
  have := hasExactColimitsOfShape_nat_ofSize R
  let P : ObjectProperty (ModOfSize.{v, u, w} R) := fun X ↦
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) X
  let _ : P.ContainsZero := Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize R
  have hsum : ∀ X Y, P X → P Y → P (X ⊞ Y) :=
    Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize R
  have hcover : ∀ X, ∃ (Y : _) (_ : P Y) (p : Y ⟶ X), Epi p := by
    intro X
    obtain ⟨N, p, hN, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize R X
    exact ⟨N, hN, p, hp⟩
  obtain ⟨Q, q, g, hq, hepi, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover G
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n ↦ q n ≫ G.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ G := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ G.ιTruncLE (n : ℤ) := hc.fac s
  refine ⟨D, α, fun n ↦ ⟨(n : ℤ), hle n⟩, hflat,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα,
    fun i ↦ ?_, fun n ↦ ⟨q n, hq n⟩⟩
  have hlt : i < ((i.toNat + 1 : ℕ) : ℤ) := by omega
  have h1 : Epi ((q (i.toNat + 1)).f i) := hepi (i.toNat + 1) i
  have h2 : Epi ((G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    G.epi_ιTruncLE_f_of_lt _ i hlt
  have hfac : (c.ι.app (i.toNat + 1)).f i ≫ α.f i
      = (q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i :=
    congrArg (fun φ ↦ φ.f i) (hα (i.toNat + 1))
  have h3 : Epi ((q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    @epi_comp _ _ _ _ _ _ h1 _ h2
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ h3 hfac

end

end Stacks.SheafOfModules.KFlatResolution

end
