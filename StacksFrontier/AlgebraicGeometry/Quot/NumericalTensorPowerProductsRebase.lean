module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackRebase
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImagePerfect
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsCongr
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackSourceIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.DerivedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.Perfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackAlongIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreEulerPullback


/-!
# The numerical invariants of Stacks 0DNE along the change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a separated morphism of finite
presentation of algebraic spaces over `W`, with perfect objects `E_1, …, E_r` of `D(𝒪_X)`.  Over
`S` there is the standing datum `Λ_h f : Λ_h X ⟶ Λ_h Y` with the perfect objects `Φ E_j`.  For an
object `(T, 𝓕)` of `Coh_{X/Y}` and its transported object of `Coh_{Λ_h X/Λ_h Y}`, the objects `K_n`
correspond: `K_n ≅ Ψ(Lσ^* K'_n)` for `σ : Λ_h T ≅ T`, the derived direct image along the
(non-representable) projection `X_T ⟶ T` commuting with the change of base scheme.  The
`K'_n` being perfect (Stacks 0A1P), the derived-fibre Euler characteristics correspond under the
bijection of points of Stacks 03I5, so `Coh^P_{X/Y}` is the inverse image of
`Coh^P_{Λ_h X/Λ_h Y}` and open-and-closedness descends; the `K'_n` are perfect by
`AlgebraicGeometry.Space.NumericalSituation.isPerfect_numericalDirectImage`.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.rebaseObjects`: the perfect objects `Φ E_j`.
* `AlgebraicGeometry.Space.NumericalSituation.numericalTensorRebaseIso`,
  `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImageRebaseIso`: the comparisons of
  the objects `E^{⊗ n}_T ⊗^𝐋 𝓕` and `K_n`.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.numericalEuler_rebase`: the functions `χ_n` agree.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_rebase_iff`: `Coh^P_{X/Y}` is
  the inverse image of `Coh^P_{Λ_h X/Λ_h Y}`.
* `AlgebraicGeometry.Space.NumericalSituation.isOpenAndClosedCondition_of_rebase`:
  open-and-closedness of `Coh^P` descends along the change of base scheme.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) (D : CoherentSituation B W hW)

/-- **Derived direct image along the inverse of an isomorphism is derived pullback**:
`R(ι⁻¹)_* ≅ Lι^*`, both being right adjoints of `L(ι⁻¹)^*`. -/
def derivedModulePushforwardInvIsoPullbackOfIso {X X' : AlgebraicSpaces B S hS} (ι : X ≅ X') :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    letI := isGrothendieckAbelian_modules B S hS X'.1 X'.2
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS ι.inv) :
      DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) ≅
      smallEtaleDerivedModulePullback B S hS ι.hom :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  letI := isGrothendieckAbelian_modules B S hS X'.1 X'.2
  (smallEtaleDerivedModulePushforwardIso B S hS ι.inv).symm ≪≫
    (smallEtaleDerivedAdjunction B S hS ι.inv).rightAdjointUniq
      (smallEtaleDerivedModulePullbackEquivalenceOfIso ι.symm).toAdjunction

namespace NumericalSituation

open CoherentSituation

variable (hf : IsSeparated B W hW D.f.hom) {r : ℕ}
  (E : Fin r → @DerivedCategory (Modules.{u, u} B W hW D.X.1 D.X.2) _ _
    (HasDerivedCategory.standard _))
  (hE : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B W hW D.X.1 D.X.2)
    (smallEtaleRingedSite B W hW D.X.1 D.X.2).IsPerfect (E j))
  (P : (Fin r → ℤ) → ℤ)

/-- The perfect objects `Φ E_j` on `Λ_h X`. -/
abbrev rebaseObjects : Fin r → @DerivedCategory (Modules.{u, u} B S hS (D.relocalize h).X.1
    (D.relocalize h).X.2) _ _ (HasDerivedCategory.standard _) :=
  fun j => (rebaseDerivedExtension B W S hW hS h D.X.2
    (relocalizeSpaceSE B W S hW hS h D.X).2).obj (E j)

include hE in
/-- The objects `Φ E_j` are perfect. -/
theorem isPerfect_rebaseObjects (j : Fin r) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (D.relocalize h).X.1 (D.relocalize h).X.2)
    (smallEtaleRingedSite B S hS (D.relocalize h).X.1 (D.relocalize h).X.2).IsPerfect
      (rebaseObjects h D E j) :=
  isPerfect_rebaseDerivedExtension_obj B W S hW hS h D.X.2 (relocalizeSpaceSE B W S hW hS h D.X).2
    (E j) (hE j)

/-- The projection `X_T ⟶ X` of the base change along a test scheme is representable. -/
theorem relativelyRepresentable_baseChangeProjection (T : SchemesOver D.Y) :
    yoneda.relativelyRepresentable (baseChangeProjection D.f T).hom :=
  MorphismProperty.of_isPullback
    (IsPullback.map (ObjectProperty.ι _) (isPullback_baseChangeSpace D.f T)).flip
    (Functor.relativelyRepresentable.diag_iff.mp D.Y.2.diagonal_representable T.hom.hom)

/-- **The objects `(E^{⊗ n})_T ⊗^𝐋 𝓕` along the change of base scheme**: restricting to `X_T` the
derived pullback along `Λ_h (X_T) ≅ (Λ_h X)_T` of the object for the transported object and the
perfect objects `Φ E_j` gives the object for `(T, 𝓕)` and the `E_j`. -/
def numericalTensorRebaseIso (A : CoherentObject D) (n : Fin r → ℤ) :
    (rebaseDerived B W S hW hS h (D.space A.T).2
        (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2).obj
      ((smallEtaleDerivedModulePullback B S hS (D.relocalizeSpaceIso h A.T).hom).obj
        ((ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
          (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).numericalTensor
            (D.relocalizeObject h A) n)) ≅
      (ofDerivedTensorPowerProducts hf E hE P).numericalTensor A n := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW (D.space A.T).1 (D.space A.T).2)
  let ι := D.relocalizeSpaceIso h A.T
  let p := baseChangeProjection D.f A.T
  let EF := (D.relocalizeModules h A.T).functor.obj A.F
  let TP' := derivedTensorPowerProduct B S hS _ _ (rebaseObjects h D E) n
  let Ψ := rebaseDerived B W S hW hS h (D.space A.T).2
    (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2
  let e1 : (smallEtaleDerivedModulePullback B S hS ι.hom).obj
        ((smallEtaleDerivedModulePullback B S hS
          (baseChangeProjection (D.relocalize h).f (D.relocalizeTest h A.T))).obj TP') ≅
      (smallEtaleDerivedModulePullback B S hS (relocalizeHomSE B W S hW hS h p)).obj TP' :=
    (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _ ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (D.relocalizeSpaceIso_hom_projection h A.T)).app _
  let e2 := smallEtaleDerivedModulePullbackSingleInvIsoOfIso ι EF
  let e3 := ((smallEtaleDerivedPullbackTensorIso ι.hom).app (_, _)) ≪≫
    ((smallEtaleDerivedTensor B S hS _).mapIso e1).app _ ≪≫
    ((smallEtaleDerivedTensor B S hS _).obj _).mapIso e2
  let e4 := (rebaseDerivedPullbackIso B W S hW hS h p
    (relativelyRepresentable_baseChangeProjection D A.T)).app TP'
  let e5 : (rebaseDerived B W S hW hS h D.X.2 (relocalizeSpaceSE B W S hW hS h D.X).2).obj TP' ≅
      derivedTensorPowerProduct B W hW _ _ E n :=
    rebaseDerivedTensorPowerProductIso B W S hW hS h D.X.2
        (relocalizeSpaceSE B W S hW hS h D.X).2 _ n ≪≫
      derivedTensorPowerProductCongrIso (fun j =>
        (rebaseDerivedExtensionCompIso B W S hW hS h D.X.2
          (relocalizeSpaceSE B W S hW hS h D.X).2).app (E j)) n
  let e6 := rebaseDerivedSingleIso B W S hW hS h (D.space A.T).2
      (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2 EF ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((D.relocalizeModules h A.T).unitIso.app A.F).symm
  exact Ψ.mapIso e3 ≪≫ rebaseDerivedTensorIso B W S hW hS h (D.space A.T).2
      (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2 _ _ ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B W hW (D.space A.T).1 (D.space A.T).2)).mapIso
      (e4 ≪≫ (smallEtaleDerivedModulePullback B W hW p).mapIso e5)).app _ ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B W hW (D.space A.T).1 (D.space A.T).2)).obj _).mapIso e6

/-- The projection `Λ_h (X_T) ⟶ Λ_h T` is the composite of the comparison
`Λ_h (X_T) ≅ (Λ_h X)_T`, the projection `(Λ_h X)_T ⟶ T` and `T ≅ Λ_h T`. -/
theorem rebaseHom_projection_eq (T : SchemesOver D.Y) :
    relocalizeHomSE B W S hW hS h (D.projection T) = (D.relocalizeSpaceIso h T).hom ≫
      ((D.relocalize h).projection (D.relocalizeTest h T) ≫
        (relocalizeSchemeSpaceIso h T.left).inv) := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact (D.relocalizeSpaceIso_hom_inclusion h T).symm

/-- **`K_n` along the change of base scheme**: the object `K_n` of `(T, 𝓕)` for the `E_j` is the
restriction to `T` of the pullback along `Λ_h T ≅ T` of the object `K_n` of the transported object
for the perfect objects `Φ E_j`. -/
def numericalDirectImageRebaseIso (A : CoherentObject D) (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf E hE P).numericalDirectImage A n ≅
      (rebaseDerived B W S hW hS h (testSpace A).2
          (relocalizeSpaceSE B W S hW hS h (testSpace A)).2).obj
        ((smallEtaleDerivedModulePullback B S hS (relocalizeSchemeSpaceIso h A.T.left).hom).obj
          ((ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
            (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).numericalDirectImage
              (D.relocalizeObject h A) n)) := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW (D.space A.T).1 (D.space A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW (testSpace A).1 (testSpace A).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
    (relocalizeSpaceSE B W S hW hS h (D.space A.T)).1
    (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
    (relocalizeSpaceSE B W S hW hS h (testSpace A)).1
    (relocalizeSpaceSE B W S hW hS h (testSpace A)).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
    ((D.relocalize h).space (D.relocalizeTest h A.T)).1
    ((D.relocalize h).space (D.relocalizeTest h A.T)).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
    ((schemeSpaceFunctor B S hS).obj (D.relocalizeTest h A.T).left).1
    ((schemeSpaceFunctor B S hS).obj (D.relocalizeTest h A.T).left).2)
  letI := isGrothendieckAbelian_modules B W hW (D.space A.T).1 (D.space A.T).2
  letI := isGrothendieckAbelian_modules B S hS (relocalizeSpaceSE B W S hW hS h (D.space A.T)).1
    (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2
  letI := isGrothendieckAbelian_modules B S hS ((D.relocalize h).space (D.relocalizeTest h A.T)).1
    ((D.relocalize h).space (D.relocalizeTest h A.T)).2
  letI := isGrothendieckAbelian_modules B S hS
    ((schemeSpaceFunctor B S hS).obj (D.relocalizeTest h A.T).left).1
    ((schemeSpaceFunctor B S hS).obj (D.relocalizeTest h A.T).left).2
  let ι := D.relocalizeSpaceIso h A.T
  let σ := relocalizeSchemeSpaceIso h A.T.left
  let M' := (ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
    (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).numericalTensor
      (D.relocalizeObject h A) n
  let Ψ := rebaseDerived B W S hW hS h (testSpace A).2
    (relocalizeSpaceSE B W S hW hS h (testSpace A)).2
  let e1 := (Stacks.DerivedFunctor.totalRightDerived
    (modulePushforward B W hW (D.projection A.T))).mapIso
      (numericalTensorRebaseIso h D hf E hE P A n).symm
  let e2 := ((rebaseDerivedDirectImageIso B W S hW hS h (D.projection A.T)).app
    ((smallEtaleDerivedModulePullback B S hS ι.hom).obj M')).symm
  let e3 := (eqToIso (congrArg (fun k => haveI := modulePushforward_additive B S hS k
      (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS k) : DerivedCategory (Modules.{u, u} B S hS
        (relocalizeSpaceSE B W S hW hS h (D.space A.T)).1
          (relocalizeSpaceSE B W S hW hS h (D.space A.T)).2) ⥤
          DerivedCategory (Modules.{u, u} B S hS (relocalizeSpaceSE B W S hW hS h (testSpace A)).1
            (relocalizeSpaceSE B W S hW hS h (testSpace A)).2)))
      (rebaseHom_projection_eq h D A.T))).app _ ≪≫
    derivedModulePushforwardCompPullbackIsoOfIso ι _ M' ≪≫
    (derivedModulePushforwardCompIso B S hS _ σ.inv).app M' ≪≫
    (derivedModulePushforwardInvIsoPullbackOfIso σ).app _
  exact e1 ≪≫ e2 ≪≫ Ψ.mapIso e3

/-- **The numerical invariants along the change of base scheme**: if the object `K_n` of the
transported object is perfect, the function `χ_n` of `(T, 𝓕)` at a point `t` of `T` is the
function `χ_n` of the transported object at the corresponding point. -/
theorem numericalEuler_rebase (A : CoherentObject D) (n : Fin r → ℤ)
    (hK : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (testSpace (D.relocalizeObject h A)).1 (testSpace (D.relocalizeObject h A)).2)
      (smallEtaleRingedSite B S hS _ (testSpace (D.relocalizeObject h A)).2).IsPerfect
        ((ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
          (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).numericalDirectImage
            (D.relocalizeObject h A) n))
    (x : points B W hW (testSpace A).1) :
    (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A n x =
      (ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
        (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).numericalEuler
          (D.relocalizeObject h A) n
        (pointsMap B S hS _ (relocalizeSchemeSpaceIso h A.T.left).hom.hom
          (pointsRelocalize B W S hW hS h _ x)) := by
  have hK' := (isPerfect_smallEtaleDerivedModulePullback_hom_iff B S hS
    (relocalizeSchemeSpaceIso h A.T.left) _).2 hK
  exact (congrFun (derivedFibreEuler_congr (testSpace A)
    (numericalDirectImageRebaseIso h D hf E hE P A n)) x).trans
    ((derivedFibreEuler_rebaseDerived B W S hW hS h (testSpace A) _ hK' x).trans
      (derivedFibreEuler_derivedPullback_of_isPerfect (relocalizeSchemeSpaceIso h A.T.left).hom _
        hK _))

/-- The bijection of points `|T| ≅ |Λ_h T|` of a test scheme read over `W` and over `S`. -/
theorem bijective_pointsMap_rebaseSchemeSpaceIso_pointsRelocalize (U : BigFppfOver B W hW) :
    Function.Bijective (pointsMap B S hS _ (relocalizeSchemeSpaceIso h U).hom.hom ∘
      pointsRelocalize B W S hW hS h _) := by
  refine Function.Bijective.comp ?_ (pointsRelocalize_bijective B W S hW hS h _)
  refine Function.bijective_iff_has_inverse.2
    ⟨pointsMap B S hS _ (relocalizeSchemeSpaceIso h U).inv.hom, fun y => ?_, fun y => ?_⟩
  · rw [← Function.comp_apply (f := pointsMap B S hS _ _), ← pointsMap_comp]
    change pointsMap B S hS _
      ((relocalizeSchemeSpaceIso h U).hom ≫ (relocalizeSchemeSpaceIso h U).inv).hom y = y
    rw [Iso.hom_inv_id]
    exact congrFun (pointsMap_id B S hS _) y
  · rw [← Function.comp_apply (f := pointsMap B S hS _ _), ← pointsMap_comp]
    change pointsMap B S hS _
      ((relocalizeSchemeSpaceIso h U).inv ≫ (relocalizeSchemeSpaceIso h U).hom).hom y = y
    rw [Iso.inv_hom_id]
    exact congrFun (pointsMap_id B S hS _) y

/-- **`Coh^P_{X/Y}` is the inverse image of `Coh^P_{Λ_h X/Λ_h Y}`** along the change of base
scheme. -/
theorem hasNumericalInvariants_rebase_iff (A : CoherentObject D) :
    (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants A ↔
      (ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
        (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).HasNumericalInvariants
          (D.relocalizeObject h A) := by
  have hφ := bijective_pointsMap_rebaseSchemeSpaceIso_pointsRelocalize h A.T.left
  have hK := fun n => (ofDerivedTensorPowerProducts (D := D.relocalize h)
    (D.isSeparated_relocalize h hf) (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE)
      P).isPerfect_numericalDirectImage (D.relocalizeObject h A) n
  refine forall_congr' fun n => ⟨fun H t' => ?_, fun H t => ?_⟩
  · obtain ⟨t, rfl⟩ := hφ.2 t'
    exact (numericalEuler_rebase h D hf E hE P A n (hK n) t).symm.trans (H t)
  · exact (numericalEuler_rebase h D hf E hE P A n (hK n) t).trans (H _)

/-- **Open-and-closedness of `Coh^P` descends along the change of base scheme.** -/
theorem isOpenAndClosedCondition_of_rebase
    (h' : IsOpenAndClosedCondition (D.relocalize h)
      (ofDerivedTensorPowerProducts (D := D.relocalize h) (D.isSeparated_relocalize h hf)
        (rebaseObjects h D E) (isPerfect_rebaseObjects h D E hE) P).HasNumericalInvariants) :
    IsOpenAndClosedCondition D (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants :=
  IsOpenAndClosedCondition.of_rebase h h' (hasNumericalInvariants_rebase_iff h D hf E hE P)

end NumericalSituation

end AlgebraicGeometry.Space

end
