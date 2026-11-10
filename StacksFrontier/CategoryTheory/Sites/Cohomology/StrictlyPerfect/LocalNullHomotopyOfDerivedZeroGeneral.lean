module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalNullHomotopyOfDerivedZero
import StacksCore.Tactic.StacksAttribute

/-!
# Local null-homotopy of a map which vanishes in the derived category, at general universes

Stacks 08FR (2) with the objects of the site, its morphisms and the sections of the structure
sheaf at independent universes: `RingedSite.{u, v, w}` with the sections of the modules in the
ring universe `w`, which is what pairing it with Stacks 08FR (1)
(`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`) asks for.

The form in `LocalNullHomotopyOfDerivedZero` is pinned to `RingedSite.{u, u, 0}` because it reads
the diagonal-universe Stacks 08FP (1), `exists_coveringSieve_homotopy_zero_of_acyclic`; the form
here reads the universe-general `exists_coveringSieve_homotopy_zero_of_acyclic_general` instead.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero_general`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w d

namespace AlgebraicGeometry.RingedSite

section GeneralUniverses

variable (X : RingedSite.{u, v, w}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d}
  (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **Stacks 08FR (2)**, with the objects of the site, its morphisms and the sections of the
structure sheaf at independent universes. This is the general form of
`exists_coveringSieve_homotopy_zero_of_derived_zero` above, which is pinned to
`RingedSite.{u, u, 0}`.

The statement and the proof are the pinned ones: a map `α : E ⟶ F` of complexes of
`O|_U`-modules with `E` strictly perfect whose image in `D(O|_U)` is zero becomes
null-homotopic after restriction along each arrow of some covering sieve of `U`. Only the engine
beneath changes name — Stacks 08FP (1) is read as
`exists_coveringSieve_homotopy_zero_of_acyclic_general`, where the pinned form reads
`exists_coveringSieve_homotopy_zero_of_acyclic`.

This is the form that pairs with Stacks 08FR (1),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, whose module sections live in
the ring universe `w`. -/
@[sga "6 I 4.1" "special case"]
theorem exists_coveringSieve_homotopy_zero_of_derived_zero_general
    {E F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) (α : E ⟶ F)
    (hα : DerivedCategory.Q.map α = 0) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0) := by
  let M := SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
  let q := HomotopyCategory.quotient M (ComplexShape.up ℤ)
  have hα₀ : DerivedCategory.Qh.map (q.map α) = 0 := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso M).hom.app F)).1
    rw [DerivedCategory.quotientCompQhIso_hom_naturality]
    simp [hα]
  obtain ⟨Z, s, hs, hαs⟩ := (MorphismProperty.map_eq_iff_postcomp
    (L := DerivedCategory.Qh) (W := HomotopyCategory.quasiIso M (ComplexShape.up ℤ))
    (q.map α) 0).1 (by rw [hα₀, Functor.map_zero])
  obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t, rfl⟩ := q.map_surjective s
  let T := (CochainComplex.mappingCone.triangleh t).invRotate
  -- The cone of the quasi-isomorphism `t` is acyclic: the cone sits in a distinguished triangle
  -- of the homotopy category whose other two vertices are the source and target of `t`, and the
  -- quasi-isomorphisms of the homotopy category are the maps whose cone is acyclic.
  have hcone : QuasiIso t → (CochainComplex.mappingCone t).Acyclic := by
    rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact (ObjectProperty.trW_iff_of_distinguished _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished t)).1
  -- A shift of an acyclic complex is acyclic, the shift functor identifying the cohomology of
  -- `K⟦a⟧` in degree `i` with that of `K` in degree `i + a`.
  have hsh : ((CochainComplex.mappingCone t)⟦(-1 : ℤ)⟧).Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    simpa [CochainComplex] using
      (IsZero.of_iso
        (hcone ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).1 hs) (i + (-1))).isZero_homology
        ((CochainComplex.ShiftSequence.shiftIso M (-1) i (i + (-1)) (add_comm (-1) i)).app
          (CochainComplex.mappingCone t)))
  have hC' : (T.obj₁.as).Acyclic := by
    change (((q.obj (CochainComplex.mappingCone t))⟦(-1 : ℤ)⟧).as).Acyclic
    rw [HomotopyCategory.shift_quotient_obj]
    exact hsh
  obtain ⟨β₀, hβ₀⟩ := Triangle.coyoneda_exact₂ T
    (inv_rot_of_distTriang _ (HomotopyCategory.mappingCone_triangleh_distinguished t)) (q.map α)
    (by
      change q.map α ≫ (CochainComplex.mappingCone.triangleh t).mor₁ = 0
      exact (by simpa using hαs : q.map α ≫ q.map t = 0))
  obtain ⟨β, hβ⟩ := q.map_surjective β₀
  obtain ⟨j, hj⟩ := q.map_surjective T.mor₁
  have hfactor : Homotopy α (β ≫ j) :=
    HomotopyCategory.homotopyOfEq _ _ (show q.map α = q.map β ≫ q.map j by
      rw [hβ, hj]
      exact hβ₀)
  obtain ⟨S, hS, hnull⟩ :=
    exists_coveringSieve_homotopy_zero_of_acyclic_general (X := X) (U := U) (α := β) hE hC'
  refine ⟨S, hS, fun f hf ↦ ?_⟩
  obtain ⟨hβf⟩ := hnull f hf
  let R :=
    SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk f)
  let RV := R.mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨(R.mapHomotopy hfactor).trans ((Homotopy.ofEq (RV.map_comp β j)).trans
    ((hβf.compRight (RV.map j)).trans (Homotopy.ofEq (by exact zero_comp))))⟩

end GeneralUniverses

end AlgebraicGeometry.RingedSite

end
