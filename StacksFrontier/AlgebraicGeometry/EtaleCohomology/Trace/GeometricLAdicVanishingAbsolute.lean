module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Vanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingInputs
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The absolute form of Tag 095U over a separably closed field, for sheaves of `ℤ/m`-modules

The vanishing step of [Stacks, Tag 03V2] uses [Stacks, Tag 095U] in its absolute form: for a
scheme `Y` proper over a separably closed field `K` with `dim Y ≤ n` and a sheaf `G` of
`ℤ/m`-modules on `Y_étale`, `Hᵠ(Y, G) = 0` for `q > 2n`, where the cohomology is computed as
`Hᵠ(RΓ(Spec K, Rg_* G))` for the structure morphism `g`
(`Stacks.EtaleCohomology.ProperSeparablyClosedVanishingStatement`). This file derives that form
from Tag 095U, and Tag 095U from the two inputs of its proof.

The steps are these.

* **The absolute abelian form from the relative one.** By the Leray spectral sequence of `g`
  (`LerayVanishing.subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage`),
  `Hᵠ(Y, F)` vanishes once `H^{q-p}(Spec K, R^p g_* F)` does for every `p ≤ q`. For `p > 2n` the
  sheaf `R^p g_* F` is zero by Tag 095U: the only fibre of `g` is `Y`. For `p ≤ 2n < q` the degree
  `q - p` is positive, and global sections over a separably closed field are an equivalence
  (`Stacks.EtaleCohomology.isEquivalence_globalSections_of_isSepClosed`), hence exact, so they
  have no higher derived functors.
* **The module form from the abelian form.** `RΓ(Spec K, Rg_* G) ≅ RΓ(Y, G)` because
  `Γ(Spec K, g_* -) = Γ(Y, -)` and `g_*` preserves injectives; the cohomology of a sheaf of
  `ℤ/m`-modules computed with injective sheaves of modules is `Ext` out of the constant sheaf,
  which is the cohomology `Sheaf.H` of the underlying abelian sheaf
  (`Stacks.EtaleCohomology.extConstantAddEquivSheafH`); and that abelian sheaf is torsion,
  being killed by `m`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_of_properDirectImageVanishingStatement`: the
  absolute abelian form, from Tag 095U.
* `Stacks.EtaleCohomology.ProperSeparablyClosedSheafHVanishingStatement`: the absolute abelian
  form, as a statement.
* `Stacks.EtaleCohomology.isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH`:
  `Hᵠ(RΓ(S, Rg_* G))` vanishes when `Hᵠ` of the underlying abelian sheaf of `G` does.
* `Stacks.EtaleCohomology.properSeparablyClosedVanishingStatement_of_sheafH`: the module form,
  from the absolute abelian form.
* `properSeparablyClosedVanishingStatement_of_properDirectImageVanishingStatement`:
  the module form, from Tag 095U.
* `Stacks.EtaleCohomology.properDirectImageVanishingStatement_of_curve`: Tag 095U from the proper
  base change theorem and the vanishing above degree `2` on proper curves over algebraically
  closed fields, the two inputs of its proof.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The fibres of a morphism to the spectrum of a field have the dimension of the source: the
spectrum of a field is a point, so the fibre over it is homeomorphic to the whole source. -/
theorem topologicalKrullDim_fiber_of_spec_field (K : Type u) [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (y : Spec (.of K)) :
    topologicalKrullDim (g.fiber y) = topologicalKrullDim Y := by
  have : Subsingleton (Spec (.of K)) := by
    change Subsingleton (PrimeSpectrum K)
    exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField K)
  have huniv : (g : Y → Spec (.of K)) ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim _ _
  rw [IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo y).isHomeomorph]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    ((Homeomorph.setCongr huniv).trans (Homeomorph.Set.univ Y)).isHomeomorph)

/-- **Étale cohomology over a separably closed field vanishes in positive degrees**: global
sections on the small étale site of `Spec K` are an equivalence, hence exact. -/
@[sga "4 VIII 2.4"]
theorem subsingleton_sheafH_spec_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u + 1} F p) := by
  have := isEquivalence_globalSections_of_isSepClosed K AddCommGrpCat.{u + 1}
  have : (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    Stacks.Cohomology.GlobalSections.additive_Γ.{0, u, u + 1} _
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
  exact Functor.isZero_rightDerived_of_exact _ F p hp

/-- **The absolute form of [Stacks, Tag 095U] over a separably closed field, from Tag 095U.**
Let `Y` be proper over a separably closed field `K` with `dim Y ≤ n`, and `F` a torsion abelian
sheaf on `Y_étale`. Then `Hᵠ(Y, F) = 0` for `q > 2n`, granted Tag 095U
(`ProperDirectImageVanishingStatement`): by the Leray spectral sequence of `Y ⟶ Spec K`, whose
only fibre is `Y`, and the vanishing of the cohomology of `Spec K` in positive degrees. -/
theorem subsingleton_sheafH_of_properDirectImageVanishingStatement
    (h095U : ProperDirectImageVanishingStatement.{u}) (K : Type u) [Field K] [IsSepClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g] (n : ℕ)
    (hY : topologicalKrullDim Y ≤ n) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F) (q : ℕ) (hq : 2 * n < q) :
    Subsingleton (Sheaf.H.{u + 1} F q) := by
  have hfib : ∀ y : Spec (.of K), topologicalKrullDim (g.fiber y) ≤ n := fun y ↦
    (topologicalKrullDim_fiber_of_spec_field K g y).le.trans hY
  refine LerayVanishing.subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage.{u, 0}
    g F q fun p hp ↦ ?_
  by_cases hpn : 2 * n < p
  · exact Sheaf.subsingleton_H_of_isZero
      (h095U g n hfib F hF p (by exact_mod_cast hpn)) (q - p)
  · exact subsingleton_sheafH_spec_of_isSepClosed K _ (q - p) (by omega)

/-- **The cohomology of a sheaf of `Λ`-modules over the spectrum of a separably closed field,
pushed forward from `Y`, is the cohomology on `Y`**: `RΓ(Spec K, Rg_* G) ≅ RΓ(Y, G)`, since
`Γ(Spec K, g_* -) = Γ(Y, -)` and `g_*` preserves injective objects. -/
def derivedDirectImageSectionsIsoDerivedGlobalSections (Λ : Type) [Ring Λ] {Y S : Scheme.{u}}
    (g : Y ⟶ S) (G : EtaleModules.{u, 0} Λ Y) :
    derivedDirectImageSections g Λ G ≅
      DerivedCategory.Plus.ι.obj ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
  DerivedCategory.Plus.ι.mapIso ((rightDerivedFunctorPlusCompIsoOfIso
    (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
    (etaleModuleGlobalSections.{u, 0} Λ Y) (etaleModuleGlobalSectionsDirectImageIso g Λ)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)).symm

/-- The underlying abelian sheaf of a sheaf of `ℤ/m`-modules is torsion: it is killed by `m`. -/
theorem torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod {Y : Scheme.{u}} (m : ℕ)
    [NeZero m] (G : EtaleModules.{u, 0} (ZMod m) Y) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((etaleModuleUnderlyingAbelian Y (ZMod m)).obj G) := by
  intro U x
  refine ⟨⊤, (Y.smallEtaleTopology).top_mem U, fun V f _ ↦ ⟨m, Nat.pos_of_ne_zero (NeZero.ne m),
    ?_⟩⟩
  change m • (G.obj.map f.op x : G.obj.obj (Opposite.op V)) = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul]

/-- **The absolute case of [Stacks, Tag 095U] over a separably closed field, for torsion abelian
sheaves, as a statement**: for every scheme `Y` proper over a separably closed field with
`dim Y ≤ n` and every torsion abelian sheaf `F` on `Y_étale`, `Hᵠ(Y, F) = 0` for `q > 2n`. -/
def ProperSeparablyClosedSheafHVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsSepClosed K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K))
    [IsProper g] (n : ℕ), topologicalKrullDim Y ≤ n →
    ∀ F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F →
      ∀ q : ℕ, 2 * n < q → Subsingleton (Sheaf.H.{u + 1} F q)

/-- **The absolute abelian form of [Stacks, Tag 095U] over a separably closed field, from
Tag 095U.** -/
theorem properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
    (h095U : ProperDirectImageVanishingStatement.{u}) :
    ProperSeparablyClosedSheafHVanishingStatement.{u} :=
  fun K _ _ _ g _ n hY F hF q hq ↦
    subsingleton_sheafH_of_properDirectImageVanishingStatement h095U K g n hY F hF q hq

/-- **The cohomology `Hᵠ(RΓ(S, Rg_* G))` of a sheaf of `Λ`-modules vanishes as soon as the
cohomology of its underlying abelian sheaf does**: `RΓ(S, Rg_* G) ≅ RΓ(Y, G)`, and the cohomology
of `G` computed with injective sheaves of modules is `Ext` out of the constant sheaf, which is the
cohomology `Sheaf.H` of the underlying abelian sheaf. -/
theorem isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (Λ : Type) [CommRing Λ]
    {Y S : Scheme.{u}} (g : Y ⟶ S) (G : EtaleModules.{u, 0} Λ Y) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Y Λ).obj G) q)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ)).obj
      (derivedDirectImageSections g Λ G)) := by
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (derivedDirectImageSectionsIsoDerivedGlobalSections Λ g G))
  change IsZero (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (q : ℤ)).obj G)
  have e := (etaleModuleRightDerivedPlusIsoExt Λ Y G q).addCommGroupIsoToAddEquiv.trans
    (extConstantAddEquivSheafH Y G q)
  have : Subsingleton (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus
      (q : ℤ)).obj G) := e.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- **The module form of the absolute case of [Stacks, Tag 095U], from the abelian form.**
`ProperSeparablyClosedSheafHVanishingStatement` implies `ProperSeparablyClosedVanishingStatement`:
`Hᵠ(RΓ(Spec K, Rg_* G)) = 0` for `q > 2n` and every sheaf `G` of `ℤ/m`-modules, `m ≠ 0`, since the
underlying abelian sheaf of `G` is torsion. -/
theorem properSeparablyClosedVanishingStatement_of_sheafH
    (h : ProperSeparablyClosedSheafHVanishingStatement.{u}) :
    ProperSeparablyClosedVanishingStatement.{u} := by
  intro K _ _ Y g _ n hY m _ G q hq
  lift q to ℕ using by omega
  exact isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH (ZMod m) g G q
    (h K g n hY _ (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod m G) q
      (by exact_mod_cast hq))

/-- **The module form of the absolute case of [Stacks, Tag 095U], from Tag 095U.** -/
theorem properSeparablyClosedVanishingStatement_of_properDirectImageVanishingStatement
    (h095U : ProperDirectImageVanishingStatement.{u}) :
    ProperSeparablyClosedVanishingStatement.{u} :=
  properSeparablyClosedVanishingStatement_of_sheafH
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement h095U)

/-- **[Stacks, Tag 095U] from the two inputs of its proof**: the proper base change theorem for
every proper morphism (`h095T`, the conclusion of [Stacks, Tag 095T]) and the vanishing
`H^q(C, G) = 0` for `q > 2` on every proper scheme `C` of dimension at most one over an
algebraically closed field (`hcurve`, the clause of [Stacks, Tag 03SC] the proof uses). This is
`isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve_univ`
at the coefficient universe of `ProperDirectImageVanishingStatement`. -/
theorem properDirectImageVanishingStatement_of_curve
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, 0} p)
    (hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
          letI := IsGrothendieckAbelian.hasExt.{u + 1}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          Subsingleton (Sheaf.H.{u + 1} G q)) :
    ProperDirectImageVanishingStatement.{u} := by
  intro X Y f _ n hn F hF i hi
  exact isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve_univ.{u, 0}
    h095T hcurve f n hn F hF i (by exact_mod_cast hi)

end Stacks.EtaleCohomology

end
