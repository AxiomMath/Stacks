module

public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ProjectiveExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic

namespace Stacks.SectionsToProjectiveSpace.C1573
end Stacks.SectionsToProjectiveSpace.C1573

/-!
# A morphism to projective space is given by sections on a dense open

Let `Y` be a scheme with finitely many irreducible components and `φ : Y ⟶ ℙⁿ_ℤ` a morphism.
Then there is a dense open `U ⊆ Y` and regular functions `s₀, …, sₙ` on `U`, spanning the unit
ideal, such that `φ` restricted to `U` is the morphism attached to them.

The open `U` is a disjoint union of opens `O_C`, one for each irreducible component `C`: the
part of `C` lying in the preimage of a standard chart containing the image of the generic point
of `C` and off all the other components. On `O_C` the morphism is given by the pulled back
ratios of that chart
(`Stacks.SectionsToProjectiveSpace.C1573.exists_eq_toProjectiveSpaceAtUniverse`), and these glue
over the disjoint union.

## Main results

* `Stacks.SectionsToProjectiveSpace.C1573.exists_dense_eq_toProjectiveSpaceAtUniverse`: the
  statement above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SectionsToProjectiveSpace

open _root_.Stacks.SectionsToProjectiveSpace.C1573
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/-- The standard charts cover projective space. -/
theorem C1573.iSup_chartOpen_eq_top : (⨆ j : Fin (n + 1), chartOpen.{u} j) = ⊤ :=
  Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n

/-- A set containing the generic point of every irreducible component is dense. -/
theorem C1573.dense_of_genericPoint_mem {X : Type*} [TopologicalSpace X] [QuasiSober X]
    {U : Set X} (hU : ∀ C (hC : C ∈ irreducibleComponents X), hC.1.genericPoint ∈ U) :
    Dense U := by
  refine dense_iff_closure_eq.mpr (Set.eq_univ_iff_forall.mpr fun x => ?_)
  have hx := mem_irreducibleComponent (x := x)
  have hC := irreducibleComponent_mem_irreducibleComponents x
  rw [← (isClosed_of_mem_irreducibleComponents _ hC).closure_eq,
    ← hC.1.isGenericPoint_genericPoint_closure.def] at hx
  exact closure_mono (Set.singleton_subset_iff.mpr (hU _ hC)) hx

/-- Sections over pairwise disjoint opens `O C`, the `j C`-th of which is `1` on `O C`, glue to
sections over `⨆ C, O C` spanning the unit ideal. -/
theorem C1573.exists_glue_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type u} {m : ℕ}
    (O : ι → Y.Opens) (hdisj : ∀ C D, C ≠ D → O C ⊓ O D = ⊥)
    (r : ∀ C, Fin m → Γ((O C).toScheme, ⊤)) (j : ι → Fin m) (hrj : ∀ C, r C (j C) = 1) :
    ∃ s : Fin m → Γ(Y, ⨆ C, O C),
      (∀ C l, (Y.homOfLE (le_iSup O C)).appTop ((⨆ C, O C).topIso.inv (s l)) = r C l) ∧
        Ideal.span (Set.range fun l => (⨆ C, O C).topIso.inv (s l)) = ⊤ := by
  have hcompat (sf : ∀ C, Γ(Y, O C)) : TopCat.Presheaf.IsCompatible Y.sheaf.1 O sf := by
    intro C D
    by_cases hCD : C = D
    · subst hCD
      rfl
    · exact @Subsingleton.elim _ (CommRingCat.subsingleton_of_isTerminal
        (Y.sheaf.isTerminalOfEqEmpty (hdisj C D hCD))) _ _
  let glue : (∀ C, Γ(Y, O C)) → Γ(Y, ⨆ C, O C) := fun sf =>
    (Y.sheaf.existsUnique_gluing O sf (hcompat sf)).exists.choose
  have hglue (sf : ∀ C, Γ(Y, O C)) (C : ι) :
      Y.presheaf.map (homOfLE (le_iSup O C)).op (glue sf) = sf C :=
    (Y.sheaf.existsUnique_gluing O sf (hcompat sf)).exists.choose_spec C
  let s : Fin m → Γ(Y, ⨆ C, O C) := fun l => glue fun C => (O C).topIso.hom (r C l)
  let a : Fin m → Γ(Y, ⨆ C, O C) := fun l => glue fun C => if l = j C then 1 else 0
  have hsum : ∑ l, a l * s l = 1 := by
    refine Y.sheaf.eq_of_locally_eq O _ _ fun C => ?_
    have e : Opens.leSupr O C = homOfLE (le_iSup O C) := rfl
    show Y.presheaf.map (Opens.leSupr O C).op _ = Y.presheaf.map (Opens.leSupr O C).op _
    rw [e, map_one, map_sum]
    simp only [map_mul, a, s, hglue]
    rw [Finset.sum_eq_single (j C)]
    · rw [ite_eq_left rfl, one_mul, hrj, map_one]
    · exact fun l _ hl => by rw [ite_eq_right hl, zero_mul]
    · exact absurd (Finset.mem_univ _)
  refine ⟨s, fun C l => ?_, Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one⟩
  · rw [Stacks.ProjectiveExtension.C1573.homOfLE_appTop_topIso_inv, hglue, Iso.hom_inv_id_apply]
  · have h1 : (1 : Γ((⨆ C, O C).toScheme, ⊤)) =
        ∑ l, (⨆ C, O C).topIso.inv (a l) * (⨆ C, O C).topIso.inv (s l) := by
      rw [← map_one (⨆ C, O C).topIso.inv.hom, ← hsum, map_sum]
      simp only [map_mul]
    rw [h1]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)

/-- **A morphism to projective space is given by sections on a dense open.** For a scheme `Y`
with finitely many irreducible components and `φ : Y ⟶ ℙⁿ_ℤ` there are a dense open `U ⊆ Y` and
sections `s₀, …, sₙ ∈ Γ(Y, U)` spanning the unit ideal with `U.ι ≫ φ` the morphism attached to
them. -/
theorem C1573.exists_dense_eq_toProjectiveSpaceAtUniverse {Y : Scheme.{u}}
    [Finite (irreducibleComponents Y)] (φ : Y ⟶ projectiveSpaceAtUniverse.{u} n) :
    ∃ (U : Y.Opens) (s : Fin (n + 1) → Γ(Y, U))
      (hs : Ideal.span (Set.range fun l => U.topIso.inv (s l)) = ⊤),
      Dense (U : Set Y) ∧
        U.ι ≫ φ = toProjectiveSpaceAtUniverse (fun l => U.topIso.inv (s l)) hs := by
  classical
  set ι := irreducibleComponents Y
  have hclosed : ∀ C : ι, IsClosed (C : Set Y) := fun C =>
    isClosed_of_mem_irreducibleComponents _ C.2
  let η : ι → Y := fun C => (C.2.1).genericPoint
  have hη : ∀ C : ι, closure {η C} = (C : Set Y) := fun C =>
    C.2.1.isGenericPoint_genericPoint_closure.def.trans (hclosed C).closure_eq
  have hchart (C : ι) : ∃ j, φ.base (η C) ∈ chartOpen.{u} j :=
    Opens.mem_iSup.mp (by rw [iSup_chartOpen_eq_top]; trivial)
  choose j hj using hchart
  let others : ι → Set Y := fun C => ⋃ D ∈ ({C}ᶜ : Set ι), (D : Set Y)
  have hothers : ∀ C : ι, IsClosed (others C) := fun C =>
    (Set.toFinite _).isClosed_biUnion fun D _ => hclosed D
  let O : ι → Y.Opens := fun C =>
    φ ⁻¹ᵁ chartOpen.{u} (j C) ⊓ ⟨(others C)ᶜ, (hothers C).isOpen_compl⟩
  have hnot (C D : ι) (hDC : D ≠ C) (x : Y) (hxD : x ∈ (D : Set Y)) : x ∉ O C := fun hx =>
    hx.2 (Set.mem_biUnion hDC hxD)
  have hOC : ∀ C : ι, ∀ x ∈ O C, x ∈ (C : Set Y) := fun C x hx => by
    by_contra h
    exact hnot C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
      (fun hDC => h (hDC ▸ mem_irreducibleComponent)) x mem_irreducibleComponent hx
  have hdisj : ∀ C D : ι, C ≠ D → O C ⊓ O D = ⊥ := fun C D hCD =>
    eq_bot_iff.mpr fun x hx => hnot C D hCD.symm x (hOC D x hx.2) hx.1
  have hηO (C : ι) : η C ∈ O C := ⟨hj C, fun hmem => by
    obtain ⟨D, hD, hηD⟩ := Set.mem_iUnion₂.mp hmem
    have hCD : (C : Set Y) ⊆ D :=
      (hη C).ge.trans (closure_minimal (Set.singleton_subset_iff.mpr hηD) (hclosed D))
    exact hD (Subtype.ext (le_antisymm hCD (C.2.2 D.2.1 hCD)).symm)⟩
  have hloc : ∀ C : ι, ∃ (r : Fin (n + 1) → Γ((O C).toScheme, ⊤))
      (hr : Ideal.span (Set.range r) = ⊤), r (j C) = 1 ∧
        (O C).ι ≫ φ = toProjectiveSpaceAtUniverse r hr := fun C =>
    exists_eq_toProjectiveSpaceAtUniverse _ (j C) (by rintro _ ⟨x, rfl⟩; exact x.2.1)
  choose r hr hrj hrφ using hloc
  set U : Y.Opens := ⨆ C, O C
  obtain ⟨s, hs_res, hs⟩ := exists_glue_of_pairwise_disjoint O hdisj r j hrj
  have hle : ∀ C : ι, O C ≤ U := le_iSup O
  refine ⟨U, s, hs, dense_of_genericPoint_mem fun D hD => hle ⟨D, hD⟩ (hηO ⟨D, hD⟩), ?_⟩
  let 𝒰 : U.toScheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun C => (O C).toScheme)
    (fun C => Y.homOfLE (hle C)) (fun x => by
      obtain ⟨C, hC⟩ := (Opens.mem_iSup).mp x.2
      exact ⟨C, ⟨x.1, hC⟩, Subtype.ext (by simp)⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun C => ?_
  show Y.homOfLE (hle C) ≫ U.ι ≫ φ = Y.homOfLE (hle C) ≫ _
  rw [Scheme.homOfLE_ι_assoc, hrφ C,
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality (Y.homOfLE (hle C)) _ hs
      (span_range_comp _ _ hs)]
  exact toProjectiveSpaceAtUniverse_congr (funext fun l => (hs_res C l).symm) _ _

end Stacks.SectionsToProjectiveSpace

end
