module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyBaseFieldTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologySmoothCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveBaseFieldLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationGeometricCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# `H²_c` of a lisse sheaf with trivial geometric monodromy on a curve

Let `U` be a smooth geometrically connected curve over a finite field `k` with `q` elements, `k̄`
an algebraic closure, `x̄` a geometric point and `Q` a finite `ℤ/m`-module with a continuous action
of `π₁(U, x̄)` on which `π₁(U_k̄)` acts trivially, `m` invertible in `k̄`. Then `ℱ_Q = f⁻¹ ℱ_{Q₀}`
for the descended module `Q₀` over `π₁(Spec k)` (`Stacks.EtaleCohomology.lisseBaseFieldModule`),
`H²_c(U_k̄, ℱ_Q) = H²(V̄_k̄, q⁻¹ℱ_{Q₀})` for the smooth projective compactification `V̄` of `U`,
and once `ℱ_{Q₀}` is identified over `k̄` with the constant sheaf `Q`, compatibly with the twists
and the action `B` of the geometric Frobenius `φ`, `H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist`).

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist`:
  `H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ` for `Q` with trivial geometric monodromy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x))
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include hcard in
/-- **`H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`**, for `Q` with trivial geometric monodromy, given
the identification over `k̄` of the descended sheaf `ℱ_{Q₀}` on `Spec k` with the constant sheaf
`Q`, carrying its Frobenius twist to the action of `φ` followed by the twist of `Q`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist
    (hm : IsUnit (m : kbar)) (hgi : GeometricallyIrreducible f) (φ : EtaleFundamentalGroup U.1 x)
    (u₀ : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
          (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ))) [IsIso u₀]
    (h₀ : u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
            (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)) =
      (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
              (Q.obj.obj.obj.ρ φ))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀) :
    ∃ θ : (compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+ Q.obj.obj.obj.V,
      ∀ t, θ (((compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod m)).obj Q)).hom t) =
        (p ^ q : ℕ) • (Q.obj.obj.obj.ρ φ).hom (θ t) := by
  have : Finite Q.obj.obj.obj.V := (moduleCat_isFG_iff_finite (ZMod m) _).1 Q.property
  let F₀ := (lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
    (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)
  let T := compactSupportSheafCohomology (ZMod m) f j kbar 2
  let π := compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2
  obtain ⟨α₁⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_baseField_iso B U k f x hs
    (ZMod m) Q hQ
  obtain ⟨C⟩ := nonempty_coverCompactification k f j.toBase j.immersion
    (CompactificationOf.immersion_toBase j) (𝟙 U.1)
  have hjq : C.j ≫ C.q = f :=
    (C.j_comp_q f (CompactificationOf.immersion_toBase j)).trans (Category.id_comp f)
  have : GeometricallyIrreducible (C.j ≫ C.q) := by rw [hjq]; exact hgi
  have := C.isCurve_fieldBaseChange kbar inferInstance
  have := C.smooth_fieldBaseChange kbar
  have := C.isProper_fieldBaseChange kbar
  let α₂ : (etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀) ≅
      (etaleModuleInverseImage.{u, 0} (ZMod m) f).obj F₀ :=
    (etaleModuleInverseImageRestrictionIso (ZMod m) C.j).symm.app _ ≪≫
      (etaleModuleInverseImageCompIso (ZMod m) C.j C.q).symm.app F₀ ≪≫
      eqToIso (congrArg (fun g => (etaleModuleInverseImage.{u, 0} (ZMod m) g).obj F₀) hjq)
  obtain ⟨e₃, he₃⟩ := exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification
    f j kbar m p q hcard C ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀)
  obtain ⟨e₄, he₄⟩ := exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist C.q
    kbar m p q hcard hm F₀ Q.obj.obj.obj.V (Q.obj.obj.obj.ρ φ) u₀ h₀
  let ι := α₂ ≪≫ α₁
  let e₁ : T.obj ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+
      T.obj ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀)) :=
    (T.mapIso ι).symm.toLinearEquiv.toAddEquiv
  refine ⟨(e₁.trans e₃.toAddEquiv).trans e₄, fun t => ?_⟩
  have hnat : e₁ ((π.app _).hom t) = (π.app _).hom (e₁ t) :=
    congrArg (fun φ => φ.hom t) (π.naturality ι.inv).symm
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  rw [hnat]
  exact (congrArg e₄ (he₃ (e₁ t))).trans (he₄ _)

end Stacks.EtaleCohomology

end
