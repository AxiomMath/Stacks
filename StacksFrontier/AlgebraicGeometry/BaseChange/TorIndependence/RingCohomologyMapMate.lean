module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareTransport
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnit

/-!
# The comparison of Stacks 065Z as a base change map

For a commutative square of commutative rings `f : R → A`, `g : R → R'`, `h : A → A'`,
`i : R' → A'` with common composite `c : R → A'`, derived extension of scalars along the four
edges and derived restriction of scalars along `f` and `i` form a square of adjunctions, with the
two composites identified with derived extension of scalars along `c` by the composition
isomorphisms. The comparison `K|_R ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'}` of Stacks 065Z is its base change
map `Stacks.CategoryTheory.BaseChange.map`.

## Main definitions

* `RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq`: the composition isomorphism
  `D_f ⋙ D_h ≅ D_c` of the chosen models, for `h ∘ f = c`.

## Main results

* `RingTheory.TorIndependence.isIso_squareDerivedComparison_comp_iff`,
  `RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_iff_forall_cohomology`:
  invertibility of the comparison followed by `φ`, read on cohomology.

* `RingTheory.TorIndependence.ringHomSquareComparison_app_eq_map`
* `RingTheory.TorIndependence.squareDerivedComparison_app_eq_map`: the same for a square of
  algebras.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section RingHom

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- The composition isomorphism `D_f ⋙ D_h ≅ D_c` of the chosen models of derived extension of
scalars, along an equality `h ∘ f = c` of ring homomorphisms. -/
abbrev totalDerivedExtensionScalarsCompOfEq (f : R →+* A) (h : A →+* A') (c : R →+* A')
    (hc : h.comp f = c) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h).functor ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} c).functor :=
  StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, u + 1, u + 1, u + 1} f h
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).comparison
    c hc

/-- The composition isomorphism of the chosen models, read against the comparisons: it is induced
by the degreewise composition isomorphism of extension of scalars, cast along `h ∘ f = c`. -/
theorem totalDerivedExtensionScalarsCompOfEq_hom_app_comparison (f : R →+* A) (h : A →+* A')
    (c : R →+* A') (hc : h.comp f = c) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalarsCompOfEq f h c hc).hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          c).comparison.app P =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h).functor.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            f).comparison.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h).comparison.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (extendScalarsCompInvOfEq.{u, u, u, u} f h c hc) (ComplexShape.up ℤ)).app P) :=
  (StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison.{u, u, u,
    u, u + 1, u + 1, u + 1} f h _ _ _ _ c hc P).trans
    (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq.{u, u, u, u} f h _ _ _ _
      c hc P)

/-- **The comparison of Stacks 065Z is the base change map** of the square of derived
extension/restriction adjunctions along `f` and `i`, with the composites identified with derived
extension of scalars along `c` by the composition isomorphisms. -/
theorem ringHomSquareComparison_app_eq_map (f : R →+* A) (g : R →+* R') (h : A →+* A')
    (i : R' →+* A') (c : R →+* A') (h1 : h.comp f = c) (h2 : i.comp g = c)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ringHomSquareComparison f g h i (h1.trans h2.symm)).app K =
      Stacks.CategoryTheory.BaseChange.map (totalDerivedExtensionScalarsAdjunction f)
        (totalDerivedExtensionScalarsAdjunction i) (totalDerivedExtensionScalarsCompOfEq g i c h2)
        (totalDerivedExtensionScalarsCompOfEq f h c h1) K := by
  let Tf := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  let Ti := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} i
  let Tc := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} c
  let adjf := totalDerivedExtensionScalarsAdjunction f
  let adji := totalDerivedExtensionScalarsAdjunction i
  let eg := totalDerivedExtensionScalarsCompOfEq g i c h2
  let ef := totalDerivedExtensionScalarsCompOfEq f h c h1
  let τ := ringHomSquareComparison f g h i (h1.trans h2.symm)
  let Ri := (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
  have : (ModuleCat.extendScalars.{u, u, u} g).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} g).isLeftAdjoint
  have : (ModuleCat.extendScalars.{u, u, u} h).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} h).isLeftAdjoint
  have := Tf.isLeftDerived
  have := Tg.isLeftDerived
  have := Th.isLeftDerived
  have := Ti.isLeftDerived
  -- the 2-cell of the comparison: the mate of `τ`
  have hτ : mateEquiv adjf adji ((mateEquiv adjf adji).symm τ) = τ := Equiv.apply_symm_apply _ _
  let α : Tg.functor ⋙ Ti.functor ⟶ Tf.functor ⋙ Th.functor :=
    (mateEquiv adjf adji).symm τ
  have hM : ∀ N, Tg.functor.map (adjf.unit.app N) ≫ τ.app (Tf.functor.obj N) =
      adji.unit.app (Tg.functor.obj N) ≫ Ri.map (α.app N) := fun N => by
    have := unit_mateEquiv adjf adji ((mateEquiv adjf adji).symm τ) N
    rwa [hτ] at this
  have hα : α = eg.hom ≫ ef.inv := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) fun X => ?_
    obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
    have : IsIso (DerivedCategory.Q.map p) := Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) p hp
    rw [← cancel_epi ((Tg.functor ⋙ Ti.functor).map (DerivedCategory.Q.map p)), α.naturality,
      (eg.hom ≫ ef.inv).naturality]
    refine congrArg (· ≫ _) ?_
    let QP := DerivedCategory.Q.obj P
    let ccg := StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u}
      g i Tg.functor Tg.comparison Ti.functor Ti.comparison c h2
    let ccf := StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u}
      f h Tf.functor Tf.comparison Th.functor Th.comparison c h1
    have hU : adji.unit.app (Tg.functor.obj QP) ≫ Ri.map (ccg.app P) =
        Tg.functor.map (adjf.unit.app QP) ≫ τ.app (Tf.functor.obj QP) ≫ Ri.map (ccf.app P) :=
      @unit_comp_compComparisonOfEq.{u, u, u, u} R A R' A' _ _ _ _ _ _ _ _ f g h i _ _ c h1 h2
        Tg.functor Th.functor Tg.comparison Th.comparison Tg.isLeftDerived Th.isLeftDerived
        Tf.functor Tf.comparison Ti.functor Ti.comparison Tf.isLeftDerived Ti.isLeftDerived P
    have h3 : ccg.app P = α.app QP ≫ ccf.app P := by
      apply (adji.homEquiv _ _).injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Ri.map_comp, hU,
        reassoc_of% hM QP]
    have hg : eg.hom.app QP ≫ Tc.comparison.app P = ccg.app P :=
      StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison.{u, u, u,
        u, u + 1, u + 1, u + 1} g i Tg.functor Tg.comparison Ti.functor Ti.comparison c h2 P
    have hf : ef.hom.app QP ≫ Tc.comparison.app P = ccf.app P :=
      StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison.{u, u, u,
        u, u + 1, u + 1, u + 1} f h Tf.functor Tf.comparison Th.functor Th.comparison c h1 P
    have : IsIso (Tc.comparison.app P) := Tc.comparison_isIso_of_kFlat P hP
    rw [← cancel_mono (ef.hom.app QP ≫ Tc.comparison.app P), hf, ← h3, ← hg]
    simp only [NatTrans.comp_app, Category.assoc]
    rw [← hf, Iso.inv_hom_id_app_assoc]
  refine Stacks.CategoryTheory.BaseChange.app_eq_map_of_unit adjf adji eg ef τ (fun N => ?_) K
  rw [hM N, hα]
  rfl

end RingHom

section Algebra

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- **The comparison of Stacks 065Z for a square of algebras is the base change map** of the
square of derived extension/restriction adjunctions along `R → A` and `R' → A'`, the composites
being identified with derived extension of scalars along `R → A'`. -/
theorem squareDerivedComparison_app_eq_map (K : DerivedCategory (ModuleCat.{u} A)) :
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K =
      Stacks.CategoryTheory.BaseChange.map
        (totalDerivedExtensionScalarsAdjunction (algebraMap R A))
        (totalDerivedExtensionScalarsAdjunction (algebraMap R' A'))
        (totalDerivedExtensionScalarsCompOfEq (algebraMap R R') (algebraMap R' A')
          (algebraMap R A') (IsScalarTower.algebraMap_eq R R' A').symm)
        (totalDerivedExtensionScalarsCompOfEq (algebraMap R A) (algebraMap A A')
          (algebraMap R A') (IsScalarTower.algebraMap_eq R A A').symm) K :=
  ringHomSquareComparison_app_eq_map (algebraMap R A) (algebraMap R R') (algebraMap A A')
    (algebraMap R' A') (algebraMap R A') (IsScalarTower.algebraMap_eq R A A').symm
    (IsScalarTower.algebraMap_eq R R' A').symm K


/-- **The comparison of Stacks 065Z followed by `φ` is invertible exactly when it is on every
cohomology module.** -/
theorem isIso_squareDerivedComparison_comp_iff (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    IsIso ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ) ↔
      ∀ n, IsIso (cohomologyComparisonMap (R := R) (R' := R') K K' φ n) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ⟨fun h => ?_, fun h => ?_⟩
  · unfold cohomologyComparisonMap
    infer_instance
  · unfold cohomologyComparisonMap at h
    exact IsIso.of_isIso_comp_right _
      (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app K')


/-- `RingTheory.TorIndependence.isIso_squareDerivedComparison_comp_iff` for a commutative square
of ring homomorphisms, with the algebra structures they define. -/
theorem isIso_ringHomSquareComparison_comp_iff_forall_cohomology {R A R' A' : Type u}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] (f : R →+* A) (g : R →+* R')
    (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj K ⟶ K') :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := h.toAlgebra
    letI := i.toAlgebra
    letI := (i.comp g).toAlgebra
    haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' sq.symm
    haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' rfl
    IsIso ((ringHomSquareComparison f g h i sq).app K ≫
        (ModuleCat.restrictScalars i).mapDerivedCategory.map φ) ↔
      ∀ n, IsIso (cohomologyComparisonMap (R := R) (R' := R') K K' φ n) :=
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp g).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' sq.symm
  haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' rfl
  isIso_squareDerivedComparison_comp_iff (R := R) (A := A) (R' := R') (A' := A') K K' φ

end Algebra

end RingTheory.TorIndependence

end
