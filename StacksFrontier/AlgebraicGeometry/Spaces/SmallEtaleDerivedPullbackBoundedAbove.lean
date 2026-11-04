module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionFactsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The derived pullback along a morphism of algebraic spaces is right t-exact

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  If the cohomology sheaves
of `E ∈ D(𝒪_Y)` vanish in degrees `> n`, so do those of `Lf^*E`: the derived pullback preserves
`D^{≤ n}`.

`E` is represented by a complex of flat `𝒪_Y`-modules which vanishes strictly above `n` (flat
modules cover every module, Stacks 03EW, and a bounded above complex is resolved by a bounded
above complex of terms from a covering class); such a complex is K-flat with flat terms
(Stacks 06YQ), so it computes the derived pullback (Stacks 06YY), and its degreewise pullback still
vanishes strictly above `n`.

The universes are those of the small étale ringed topos of an algebraic space — its objects one
universe above its sections — which is why the bounded above flat representative is produced
here at free universes rather than read off
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE`, which needs
the sections universe to dominate the site.

## Main results

* `AlgebraicGeometry.Space.exists_flat_isStrictlyLE_iso`: a bounded above flat representative.
* `AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_obj_of_isLE`: `Lf^*` preserves
  `D^{≤ n}`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback_map_approximation`: `Lf^*` carries a
  morphism inducing isomorphisms on cohomology in degrees `> m` and an epimorphism in degree `m`
  to one with the same property.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A bounded above object of `D(𝒪_Y)` has a bounded above flat representative.** -/
theorem exists_flat_isStrictlyLE_iso {Y : AlgebraicSpaces B S hS}
    (E : DerivedCategory (toposModules B S hS Y)) (n : ℤ) [E.IsLE n] :
    ∃ G : CochainComplex (toposModules B S hS Y) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallEtaleRingedTopos B S hS Y).O) (G.X i)) ∧
      G.IsStrictlyLE n ∧ Nonempty (DerivedCategory.Q.obj G ≅ E) := by
  classical
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E n
  let Pflat : ObjectProperty (toposModules B S hS Y) := fun F =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) F
  have : Pflat.ContainsZero :=
    ⟨⟨0, isZero_zero _, Stacks.SheafOfModules.KFlatOfSize.isFlat_of_isZero_ofSize _
      (isZero_zero _)⟩⟩
  have hcover : ∀ F : toposModules B S hS Y,
      ∃ (G : toposModules B S hS Y) (_ : Pflat G) (g : G ⟶ F), Epi g := fun F =>
    let ⟨G, g, hG, hg⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize
      (smallEtaleRingedTopos B S hS Y).O F
    ⟨G, hG, g, hg⟩
  obtain ⟨P, g, -, hg, hPflat, hPLE⟩ := (CochainComplex.exists_quasiIso_prop Pflat hcover n).1 M
  exact ⟨P, hPflat, hPLE, ⟨asIso (DerivedCategory.Q.map g) ≪≫ eM.symm⟩⟩

/-- A bounded above complex of flat modules on the small étale site of an algebraic space is
K-flat with flat terms (Stacks 06YQ). -/
theorem isKFlat_of_isStrictlyLE {Y : AlgebraicSpaces B S hS}
    (G : CochainComplex (toposModules B S hS Y) ℤ) (n : ℤ) [G.IsStrictlyLE n]
    (hG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (G.X i)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y) ((HomotopyCategory.quotient _ _).obj G) :=
  ⟨CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ G n
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize _)
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize _) fun q =>
      Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize _ _ (hG q) q, hG⟩

/-- **The derived pullback along a morphism of algebraic spaces preserves `D^{≤ n}`.** -/
theorem isLE_smallEtaleDerivedModulePullback_obj_of_isLE {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : DerivedCategory (toposModules B S hS Y)) (n : ℤ) [E.IsLE n] :
    ((smallEtaleDerivedModulePullback B S hS f).obj E).IsLE n := by
  obtain ⟨G, hG, hGLE, ⟨e⟩⟩ := exists_flat_isStrictlyLE_iso E n
  have hK := isKFlat_of_isStrictlyLE G n hG
  have := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f _ hK
  have hpLE : CochainComplex.IsStrictlyLE
      (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G) n :=
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).map_isZero
        (G.isZero_of_isStrictlyLE n i hi)
  have e' : (smallEtaleDerivedModulePullback B S hS f).obj E ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) :=
    (smallEtaleDerivedModulePullback B S hS f).mapIso
        (((DerivedCategory.quotientCompQhIso (toposModules B S hS Y)).app G) ≪≫ e).symm ≪≫
      asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.quotient _ _).obj G)) ≪≫
      DerivedCategory.Qh.mapIso
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
          |>.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app G) ≪≫
      (DerivedCategory.quotientCompQhIso (toposModules B S hS X)).app _
  exact DerivedCategory.TStructure.t.isLE_of_iso e'.symm n

/-- The canonical comparison `Lf^* ⟶ f^*` along a morphism of algebraic spaces is compatible with
the shifts. -/
instance commShift_smallEtaleDerivedModulePullbackComparison {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : NatTrans.CommShift (smallEtaleDerivedModulePullbackComparison B S hS f) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedModulePullbackComparison B S hS f) (smallEtaleModuleQuasiIso B S hS Y) ℤ

/-- **The derived pullback carries an approximation in degrees `> m` to one.**  If
`α : P ⟶ E` induces isomorphisms on cohomology in every degree `> m` and an epimorphism in
degree `m`, so does `Lf^*α`: the derived pullback is triangulated and preserves `D^{≤ n}`. -/
theorem smallEtaleDerivedModulePullback_map_approximation {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {P E : DerivedCategory (toposModules B S hS Y)} (α : P ⟶ E) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS Y) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS Y) m).map α)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS X) i).map
        ((smallEtaleDerivedModulePullback B S hS f).map α))) ∧
      Epi ((DerivedCategory.homologyFunctor (toposModules B S hS X) m).map
        ((smallEtaleDerivedModulePullback B S hS f).map α)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE
    (smallEtaleDerivedModulePullback B S hS f)
    (fun K n _ => isLE_smallEtaleDerivedModulePullback_obj_of_isLE f K n) α m hiso hepi

end AlgebraicGeometry.Space

end
