module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Glueing
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Approximation by perfect complexes on quasi-compact quasi-separated schemes

If `X = U ∪ V` with `U` quasi-compact, `V` affine and `U ∩ V` quasi-compact, and approximation by
perfect complexes holds on `U`, then it holds on `X`. Consequently approximation by perfect
complexes holds on every quasi-compact quasi-separated scheme.

## Main results

* `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_of_sup_affine`:
  approximation by perfect complexes passes from `U` to `X = U ∪ V` when `V` is affine and `U`
  and `U ∩ V` are quasi-compact.
* `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes`: approximation by
  perfect complexes holds on every quasi-compact quasi-separated scheme.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe w u

namespace AlgebraicGeometry

/-- For a distinguished triangle in any model of the derived category, if the cohomology stalks of
the outer vertices vanish off `T`, so do those of the middle vertex. -/
theorem isZero_stalk_homology_obj₂_of_distinguished {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{w} (_root_.SheafOfModules.{u} O)] (T : Set X)
    (S : Triangle (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (hS : S ∈ distTriang (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (h₁ : ∀ (i : ℤ) (x : X), x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
          S.obj₁).val.presheaf) x))
    (h₃ : ∀ (i : ℤ) (x : X), x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
          S.obj₃).val.presheaf) x))
    (i : ℤ) (x : X) (hx : x ∉ T) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
        S.obj₂).val.presheaf) x) := by
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O x]
  exact ((DerivedCategory.HomologySequence.exact₂ S hS i).map
    (SheafOfModules.stalkFunctor O x)).isZero_of_both_isZero
      ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₁ i x hx))
      ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₃ i x hx))

/-- For a distinguished triangle in any model of the derived category, if the cohomology stalks of
the first vertex vanish off `T` and those of the second vanish off `T` in all degrees `≥ b`, then
those of the third vanish off `T` in all degrees `≥ b`. -/
theorem isZero_stalk_homology_obj₃_of_distinguished_anyModel {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{w} (_root_.SheafOfModules.{u} O)] (T : Set X) (b : ℤ)
    (S : Triangle (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (hS : S ∈ distTriang (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (h₁ : ∀ (i : ℤ) (x : X), x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
          S.obj₁).val.presheaf) x))
    (h₂ : ∀ i : ℤ, b ≤ i → ∀ x : X, x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
          S.obj₂).val.presheaf) x))
    (i : ℤ) (hi : b ≤ i) (x : X) (hx : x ∉ T) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
        S.obj₃).val.presheaf) x) := by
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O x]
  exact ((DerivedCategory.HomologySequence.exact₃ S hS i (i + 1) rfl).map
    (SheafOfModules.stalkFunctor O x)).isZero_of_both_isZero
      ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₂ i hi x hx))
      ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₁ (i + 1) x hx))

end AlgebraicGeometry

namespace AlgebraicGeometry.PerfectApproximation

open Stacks.Duality.OpenImmersion

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-! ### Restriction to opens -/

/-- Isomorphic objects of `D(𝒪_Y)` have isomorphic stalks of cohomology sheaves. -/
def stalkHomologyMapIso {Y : Scheme.{u}} {K L : DerivedCategory Y.Modules} (e : K ≅ L) (i : ℤ)
    (x : Y) :
    TopCat.Presheaf.stalk (X := Y)
        (((DerivedCategory.homologyFunctor Y.Modules i).obj K).val.presheaf) x ≅
      TopCat.Presheaf.stalk (X := Y)
        (((DerivedCategory.homologyFunctor Y.Modules i).obj L).val.presheaf) x :=
  (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((DerivedCategory.homologyFunctor Y.Modules i).mapIso e)

/-- A cohomology sheaf vanishing on an open has vanishing stalks at the points of that open. -/
theorem isZero_stalk_homology_of_isZero_homology_derivedRestrict {X : Scheme.{u}}
    (O : X.Opens) (F : DerivedCategory X.Modules) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor O.toScheme.Modules i).obj
      ((derivedRestrict O.ι).obj F))) {x : X} (hx : x ∈ O) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x) :=
  ((isZero_homology_iff_forall_isZero_stalk _ i).1 h ⟨x, hx⟩).of_iso
    (stalkHomologyDerivedRestrictIso O.ι F i ⟨x, hx⟩).symm

/-- Restriction to an open preserves `m`-pseudo-coherence, at the locally small model of
`D(𝒪_X)`. -/
theorem isPseudoCoherentFrom_derivedRestrict {X : Scheme.{u}} (O : X.Opens)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) :
    RingedSpace.IsPseudoCoherentFrom (X := O.toScheme.toRingedSpace)
      ((derivedRestrict O.ι).obj E) m := by
  let K := (DerivedCategory.Q (C := X.Modules)).objPreimage E
  let eK : (DerivedCategory.Q (C := X.Modules)).obj K ≅ E :=
    (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso E
  have hK : RingedSpace.IsPseudoCoherentComplexFrom (X := X.toRingedSpace) K m :=
    RingedSpace.isPseudoCoherentComplexFrom_of_iso E m hE K eK
  have h₁ : RingedSpace.IsPseudoCoherentFrom (X := O.toScheme.toRingedSpace)
      ((DerivedCategory.Q (C := O.toScheme.Modules)).obj (RingedSpace.restrictComplex K O)) m :=
    ⟨_, RingedSpace.isPseudoCoherentComplexFrom_restrictComplex K m hK O,
      ⟨Iso.refl ((DerivedCategory.Q (C := O.toScheme.Modules)).obj
        (RingedSpace.restrictComplex K O))⟩⟩
  let e : (DerivedCategory.Q (C := O.toScheme.Modules)).obj (RingedSpace.restrictComplex K O) ≅
      (derivedRestrict O.ι).obj E :=
    (DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
        (Stacks.Duality.CompactPerfect.restrictModulesComplexIso O K) ≪≫
      (Stacks.Duality.CompactPerfect.derivedRestrictQIso O.ι K).symm ≪≫
        (derivedRestrict O.ι).mapIso eK
  exact @RingedSpace.IsPseudoCoherentFrom.ofIso O.toScheme.toRingedSpace
    (Scheme.Modules.hasDerivedCategory O.toScheme) _ _ m h₁ e

/-- A morphism of `D(𝒪_Y)` approximates from `m` when its restrictions to the members of an open
cover by two opens do. -/
theorem approximatesFrom_of_derivedRestrict_two {Y A B : Scheme.{u}} (jA : A ⟶ Y) (jB : B ⟶ Y)
    [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y)) {g E : DerivedCategory Y.Modules}
    (γ : g ⟶ E) (m : ℤ)
    (hA : DerivedCategory.ApproximatesFrom ((derivedRestrict jA).map γ) m)
    (hB : DerivedCategory.ApproximatesFrom ((derivedRestrict jB).map γ) m) :
    DerivedCategory.ApproximatesFrom γ m := by
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle γ
  refine (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ _ hT m).2 fun i hi => ?_
  refine isZero_homology_of_isZero_homology_derivedRestrict_two jA jB hcov C i ?_ ?_
  · exact (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ _
      ((derivedRestrict jA).map_distinguished _ hT) m).1 hA i hi
  · exact (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ _
      ((derivedRestrict jB).map_distinguished _ hT) m).1 hB i hi

/-- Approximation by perfect complexes is carried along an isomorphism of schemes, in the encoding
of `AlgebraicGeometry.HasApproximationByPerfectComplexes`. -/
theorem hasApproximationByPerfectComplexes_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : HasApproximationByPerfectComplexes Y) : HasApproximationByPerfectComplexes X :=
  (approximationByPerfectComplexes_iff X).1
    (approximationByPerfectComplexes_of_iso e ((approximationByPerfectComplexes_iff Y).2 h))

end AlgebraicGeometry.PerfectApproximation

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

namespace AlgebraicGeometry.PerfectApproximation

open Stacks.Duality.OpenImmersion

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- Approximation for `(T, E, m)` at the locally small model. -/
private abbrev Approx (X : Scheme.{u}) (T : Set X) (E : DerivedCategory X.Modules) (m : ℤ) :
    Prop :=
  ∃ P : DerivedCategory X.Modules,
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P ∧
      (∀ (i : ℤ) (x : X), x ∉ T → IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj P).val.presheaf) x)) ∧
      ∃ α : P ⟶ E, DerivedCategory.ApproximatesFrom α m

private theorem exists_ι_eq_of_sup_eq_top {X : Scheme.{u}} {A B : X.Opens} (h : A ⊔ B = ⊤)
    (y : X) : (∃ x, A.ι x = y) ∨ (∃ x, B.ι x = y) := by
  rcases (h ▸ trivial : y ∈ A ⊔ B) with hy | hy
  exacts [Or.inl ⟨⟨y, hy⟩, rfl⟩, Or.inr ⟨⟨y, hy⟩, rfl⟩]

/-- On a cover by two opens, an approximation `α : P ⟶ F|_A` from a perfect `P` vanishing on the
overlap extends to a perfect `g` vanishing on `B` and an approximation `g ⟶ F`, if `F|_B` has
vanishing cohomology from degree `m` on. -/
private theorem exists_isPerfect_extension_approximatesFrom {Y A B C : Scheme.{u}}
    (jA : A ⟶ Y) (jB : B ⟶ Y) (iA : C ⟶ A) (iB : C ⟶ B) [IsOpenImmersion jA]
    [IsOpenImmersion jB] [IsOpenImmersion iA] [IsOpenImmersion iB] (hsq : IsPullback iA iB jA jB)
    (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y)) (P : DerivedCategory A.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := A.toRingedSpace) P)
    (hp : IsZero ((derivedRestrict iA).obj P)) (F : DerivedCategory Y.Modules) (m : ℤ)
    (α : P ⟶ (derivedRestrict jA).obj F) (hα : DerivedCategory.ApproximatesFrom α m)
    (hFB : ∀ i : ℤ, m ≤ i → IsZero ((DerivedCategory.homologyFunctor B.Modules i).obj
      ((derivedRestrict jB).obj F))) :
    ∃ (g : DerivedCategory Y.Modules) (_ : (derivedRestrict jA).obj g ≅ P) (γ : g ⟶ F),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) g ∧
        IsZero ((derivedRestrict jB).obj g) ∧ DerivedCategory.ApproximatesFrom γ m := by
  obtain ⟨g, eg, γ, hgB, hγ⟩ :=
    exists_extension_of_isZero_derivedRestrict jA jB iA iB hsq hcov P hp F α
  refine ⟨g, eg, γ, isPerfect_of_isPerfect_derivedRestrict_two jA jB hcov g
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso eg.symm hP)
      (AlgebraicGeometry.RingedSpace.isPerfect_of_isZero hgB), hgB, ?_⟩
  refine approximatesFrom_of_derivedRestrict_two jA jB hcov γ m ?_ ?_
  · rw [hγ]
    exact (DerivedCategory.approximatesFrom_iso_comp_iff eg α m).2 hα
  · exact DerivedCategory.approximatesFrom_of_isZero _ m
      (fun i _ => (DerivedCategory.homologyFunctor _ i).map_isZero hgB) hFB

/-- An approximation on `V` vanishing on `W` extends to `X = V ∪ W` when the cohomology of the
object vanishes on `W` from degree `m` on. -/
private theorem approx_of_approx_restrict {X : Scheme.{u}} (W V : X.Opens) (hWV : W ⊔ V = ⊤)
    (T : Set X) (hTW : ∀ x : X, x ∉ T → x ∈ W) (F : DerivedCategory X.Modules) (m : ℤ)
    (hFW : ∀ i : ℤ, m ≤ i → IsZero ((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj
      ((derivedRestrict W.ι).obj F)))
    (P : DerivedCategory V.toScheme.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := V.toScheme.toRingedSpace) P)
    (hPW : ∀ (i : ℤ) (x : V.toScheme), x.1 ∈ W → IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor V.toScheme.Modules i).obj P).val.presheaf) x))
    (α : P ⟶ (derivedRestrict V.ι).obj F) (hα : DerivedCategory.ApproximatesFrom α m) :
    Approx X T F m := by
  let iA := X.homOfLE (inf_le_left : V ⊓ W ≤ V)
  let iB := X.homOfLE (inf_le_right : V ⊓ W ≤ W)
  have hsq : IsPullback iA iB V.ι W.ι := isPullback_opens_inf V W
  have hcov : ∀ y : X, (∃ x, V.ι x = y) ∨ (∃ x, W.ι x = y) :=
    exists_ι_eq_of_sup_eq_top (by rwa [sup_comm])
  have hp : IsZero ((derivedRestrict iA).obj P) :=
    isZero_derivedRestrict_of_isZero_stalk iA P fun i x =>
      hPW i (iA x) ((X.homOfLE_apply _ x : (iA x).1 = x.1) ▸ x.2.2)
  obtain ⟨g, -, γ, hg, hgW, hγ⟩ := exists_isPerfect_extension_approximatesFrom V.ι W.ι iA iB hsq
    hcov P hP hp F m α hα hFW
  exact ⟨g, hg, fun i x hx => isZero_stalk_of_isZero_derivedRestrict W.ι g hgW i ⟨x, hTW x hx⟩,
    γ, hγ⟩

/-- Extension of an approximation from `U` to `U ∪ V'` by zero on `V'`, for `V'` disjoint from
`T`, when the cohomology of the object vanishes off `T` from degree `t` on. -/
private theorem exists_extension_approximatesFrom {X : Scheme.{u}} (U Vt : X.Opens) (T : Set X)
    (hVt : ∀ x : X, x ∈ Vt → x ∉ T) (F : DerivedCategory X.Modules) (t : ℤ)
    (hF : ∀ (i : ℤ) (x : X), t ≤ i → x ∉ T → IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) P)
    (hPT : ∀ (i : ℤ) (x : U.toScheme), x.1 ∉ T → IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj P).val.presheaf) x))
    (a : P ⟶ (derivedRestrict U.ι).obj F) (ha : DerivedCategory.ApproximatesFrom a t) :
    ∃ (A : DerivedCategory (U ⊔ Vt).toScheme.Modules)
      (γ : A ⟶ (derivedRestrict (U ⊔ Vt).ι).obj F),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (U ⊔ Vt).toScheme.toRingedSpace) A ∧
        (∀ (i : ℤ) (x : (U ⊔ Vt).toScheme), x.1 ∉ T → IsZero (TopCat.Presheaf.stalk
          (((DerivedCategory.homologyFunctor (U ⊔ Vt).toScheme.Modules i).obj A).val.presheaf)
            x)) ∧
        DerivedCategory.ApproximatesFrom γ t := by
  let W := U ⊔ Vt
  let jA := X.homOfLE (le_sup_left : U ≤ W)
  let jB := X.homOfLE (le_sup_right : Vt ≤ W)
  let iA := X.homOfLE (inf_le_left : U ⊓ Vt ≤ U)
  let iB := X.homOfLE (inf_le_right : U ⊓ Vt ≤ Vt)
  have hsq : IsPullback iA iB jA jB := isPullback_opens_inf_le le_sup_left le_sup_right
  have hcov : ∀ y : W.toScheme, (∃ x, jA x = y) ∨ (∃ x, jB x = y) := by
    intro y
    rcases y.2 with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, Subtype.ext (X.homOfLE_apply _ _)⟩
    · exact Or.inr ⟨⟨y.1, h⟩, Subtype.ext (X.homOfLE_apply _ _)⟩
  let θ : derivedRestrict U.ι ≅ derivedRestrict W.ι ⋙ derivedRestrict jA :=
    derivedRestrictCongr (X.homOfLE_ι (le_sup_left : U ≤ W)).symm ≪≫
      derivedRestrictCompIso jA W.ι
  let FW := (derivedRestrict W.ι).obj F
  have hp : IsZero ((derivedRestrict iA).obj P) :=
    isZero_derivedRestrict_of_isZero_stalk iA P fun i x =>
      hPT i (iA x) ((X.homOfLE_apply _ x : (iA x).1 = x.1) ▸ hVt _ x.2.2)
  have hFB : ∀ i : ℤ, t ≤ i → IsZero ((DerivedCategory.homologyFunctor Vt.toScheme.Modules i).obj
      ((derivedRestrict jB).obj FW)) := by
    intro i hi
    refine (isZero_homology_iff_forall_isZero_stalk _ i).2 fun y => ?_
    refine IsZero.of_iso ?_ (stalkHomologyDerivedRestrictIso jB FW i y ≪≫
      stalkHomologyDerivedRestrictIso W.ι F i (jB y))
    refine hF i _ hi (hVt _ ?_)
    have h : W.ι (jB y) = y.1 := X.homOfLE_apply _ y
    exact h ▸ y.2
  obtain ⟨A, eA, γ, hA, hAB, hγ⟩ := exists_isPerfect_extension_approximatesFrom jA jB iA iB hsq
    hcov P hP hp FW t (a ≫ θ.hom.app F)
    ((DerivedCategory.approximatesFrom_comp_iso_iff a (θ.app F) t).2 ha) hFB
  refine ⟨A, γ, hA, fun i x hx => ?_, hγ⟩
  rcases hcov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact (hPT i y ((X.homOfLE_apply _ y : (jA y).1 = y.1) ▸ hx)).of_iso
      ((stalkHomologyDerivedRestrictIso jA A i y).symm ≪≫ stalkHomologyMapIso eA i y)
  · exact isZero_stalk_of_isZero_derivedRestrict jB A hAB i y

/-- Given an approximation `γ : A ⟶ F|_W` from the top degree `t` of `F|_W`, there is a perfect
object `R` supported on `T` with a morphism `R ⟶ F` whose cone has vanishing cohomology on `W`
from degree `t` on. -/
private theorem exists_isPerfect_cone {X : Scheme.{u}} (W V : X.Opens) (hWV : W ⊔ V = ⊤)
    (hV : IsAffineOpen V) (hWVc : IsCompact ((W : Set X) ∩ V)) (T : Set X)
    (hTW : ∀ x : X, x ∉ T → x ∈ W) (F : DerivedCategory X.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent)
    (t : ℤ) (hFW : ∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor
      W.toScheme.Modules i).obj ((derivedRestrict W.ι).obj F)))
    (A : DerivedCategory W.toScheme.Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toScheme.toRingedSpace) A)
    (hAT : ∀ (i : ℤ) (x : W.toScheme), x.1 ∉ T → IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj A).val.presheaf) x))
    (γ : A ⟶ (derivedRestrict W.ι).obj F) (hγ : DerivedCategory.ApproximatesFrom γ t) :
    ∃ (R : DerivedCategory X.Modules) (φ : R ⟶ F),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) R ∧
        (∀ (i : ℤ) (x : X), x ∉ T → IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj R).val.presheaf) x)) ∧
        ∀ (F' : DerivedCategory X.Modules) (v : F ⟶ F') (w : F' ⟶ R⟦(1 : ℤ)⟧),
          Triangle.mk φ v w ∈ distTriang (DerivedCategory X.Modules) → ∀ i : ℤ, t ≤ i →
            IsZero ((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj
              ((derivedRestrict W.ι).obj F')) := by
  obtain ⟨R, f, φ, hR, hφ⟩ := exists_isPerfect_glueing W V hWV hV hWVc F hqc A hA γ
  refine ⟨R, φ, hR, fun i x hx => ?_, fun F' v w hT i hi => ?_⟩
  · have hxW := hTW x hx
    refine IsZero.of_iso ?_ ((stalkHomologyDerivedRestrictIso W.ι R i ⟨x, hxW⟩).symm ≪≫
      stalkHomologyMapIso f i ⟨x, hxW⟩)
    exact isZero_stalk_homology_biprod_shift W.toScheme.ringCatSheaf A A ⟨x, hxW⟩
      (fun j => hAT j _ hx) (fun j => hAT j _ hx) i
  · have hA' : ∀ j : ℤ, t < j →
        IsZero ((DerivedCategory.homologyFunctor W.toScheme.Modules j).obj A) := fun j hj =>
      have := hγ.1 j hj
      (hFW j hj).of_iso (asIso ((DerivedCategory.homologyFunctor _ j).map γ))
    have hepi : Epi ((DerivedCategory.homologyFunctor W.toScheme.Modules t).map
        ((derivedRestrict W.ι).map φ)) := by
      rw [hφ, Functor.map_comp, Functor.map_comp]
      have := hγ.2
      infer_instance
    refine DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top _
      ((derivedRestrict W.ι).map_distinguished _ hT) t (fun j hj => ?_) hFW hepi i hi
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ j).mapIso f)
    refine IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hA' j hj, ?_⟩)
      ((DerivedCategory.homologyFunctor _ j).mapBiprod _ _)
    exact (DerivedCategory.isZero_homology_shift_iff A j).2 (hA' (j + 1) (by omega))

/-- Let `X = U ∪ V` be an open cover with `U` quasi-compact, `V` affine and `U ∩ V`
quasi-compact. If approximation by perfect complexes holds on `U`, then it holds on `X`. -/
@[stacks 08ER]
theorem hasApproximationByPerfectComplexes_of_sup_affine {X : Scheme.{u}} (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hUVc : IsCompact ((U : Set X) ∩ V)) (h : HasApproximationByPerfectComplexes U.toScheme) :
    HasApproximationByPerfectComplexes X := by
  rw [hasApproximationByPerfectComplexes_iff_locallySmall] at h ⊢
  intro T hT hTc
  obtain ⟨rU, hrU⟩ := h (U.ι.base ⁻¹' T) (hT.preimage U.ι.isOpenEmbedding.continuous)
    (by rw [← Set.preimage_compl]; exact hTc.preimage_of_isOpenEmbedding U.ι.isOpenEmbedding)
  have : IsAffine V.toScheme := hV
  let T' : Set V.toScheme := V.ι.base ⁻¹' (T ∩ (U : Set X)ᶜ)
  have hT' : IsClosed T' :=
    (hT.inter U.isOpen.isClosed_compl).preimage V.ι.isOpenEmbedding.continuous
  have hT'c : IsRetrocompact T'ᶜ := by
    have hc : T'ᶜ = V.ι.base ⁻¹' Tᶜ ∪ ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme) := by
      ext x
      simp only [T', Set.mem_compl_iff, Set.mem_preimage, Set.mem_inter_iff, not_and_or,
        not_not, Set.mem_union, TopologicalSpace.Opens.map_coe, SetLike.mem_coe]
    rw [hc]
    refine (hTc.preimage_of_isOpenEmbedding V.ι.isOpenEmbedding).union ?_
    refine IsCompact.isRetrocompact ?_ (V.ι ⁻¹ᵁ U).isOpen
    rw [V.ι.isOpenEmbedding.isEmbedding.isCompact_iff, ← Scheme.Hom.coe_image,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    simpa [Set.inter_comm] using hUVc
  obtain ⟨rV, hrV⟩ := (hasApproximationByPerfectComplexes_iff_locallySmall V.toScheme).1
    (hasApproximationByPerfectComplexes_of_isAffine V.toScheme) T' hT' hT'c
  set sU := max rU 0 with hsU
  set sV := max rV 0 with hsV
  have hrU0 : rU ≤ sU := le_max_left _ _
  have hsU0 : 0 ≤ sU := le_max_right _ _
  have hrV0 : rV ≤ sV := le_max_left _ _
  have hsV0 : 0 ≤ sV := le_max_right _ _
  refine ⟨sU + sV, fun E m hqc hpc hsupp => ?_⟩
  let Vt : X.Opens := V ⊓ ⟨Tᶜ, hT.isOpen_compl⟩
  let W : X.Opens := U ⊔ Vt
  have hVt : ∀ x : X, x ∈ Vt → x ∉ T := fun x hx => hx.2
  have hTW : ∀ x : X, x ∉ T → x ∈ W := by
    intro x hx
    have hx' : x ∈ U ⊔ V := hUV ▸ (trivial : x ∈ (⊤ : X.Opens))
    rcases hx' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hx⟩
  have hWV : W ⊔ V = ⊤ := by
    rw [eq_top_iff, ← hUV]
    exact sup_le_sup_right le_sup_left V
  have hVtc : IsCompact (Tᶜ ∩ (V : Set X)) := hTc hV.isCompact V.isOpen
  have hWc : IsCompact (W : Set X) := by
    refine hU.union ?_
    have : ((Vt : X.Opens) : Set X) = Tᶜ ∩ (V : Set X) := Set.inter_comm _ _
    rw [this]
    exact hVtc
  have hWVc : IsCompact ((W : Set X) ∩ V) := by
    have : (W : Set X) ∩ V = ((U : Set X) ∩ V) ∪ (Tᶜ ∩ (V : Set X)) := by
      ext x
      simp only [W, Vt, TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_inf,
        TopologicalSpace.Opens.coe_mk, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        SetLike.mem_coe]
      tauto
    exact this ▸ hUVc.union hVtc
  have key : ∀ n : ℕ, ∀ F : DerivedCategory X.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent) →
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) F (m - (sU + sV)) →
      (∀ (i : ℤ) (x : X), m - (sU + sV) ≤ i → x ∉ T →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x)) →
      (∀ i : ℤ, m - sV + n ≤ i → IsZero ((DerivedCategory.homologyFunctor
        W.toScheme.Modules i).obj ((derivedRestrict W.ι).obj F))) →
      Approx X T F m := by
    intro n
    induction n with
    | zero =>
      intro F hqc hpc hsupp hvan
      obtain ⟨P, hP, hPT, α, hα⟩ := hrV ((derivedRestrict V.ι).obj F) m
        (fun i => derivedCategoryB_derivedRestrict V.ι F hqc i)
        (isPseudoCoherentFrom_derivedRestrict V F (m - rV) (hpc.mono (by omega)))
        (fun i x hi hx => by
          refine IsZero.of_iso ?_ (stalkHomologyDerivedRestrictIso V.ι F i x)
          by_cases hxT : V.ι.base x ∈ T
          · exact isZero_stalk_homology_of_isZero_homology_derivedRestrict W F i
              (hvan i (by omega)) (Or.inl (not_not.1 fun hxU => hx ⟨hxT, hxU⟩))
          · exact hsupp i _ (by omega) hxT)
      refine approx_of_approx_restrict W V hWV T hTW F m (fun i hi => hvan i (by omega)) P hP
        (fun i x hx => hPT i x fun hxT' => ?_) α hα
      rcases hx with hxU | hxVt
      · exact hxT'.2 hxU
      · exact hxVt.2 hxT'.1
    | succ n ih =>
      intro F hqc hpc hsupp hvan
      obtain ⟨P, hP, hPT, a, ha⟩ := hrU ((derivedRestrict U.ι).obj F) (m - sV + n)
        (fun i => derivedCategoryB_derivedRestrict U.ι F hqc i)
        (isPseudoCoherentFrom_derivedRestrict U F (m - sV + n - rU) (hpc.mono (by omega)))
        (fun i x hi hx => (hsupp i (U.ι.base x) (by omega) hx).of_iso
          (stalkHomologyDerivedRestrictIso U.ι F i x))
      obtain ⟨A, γ, hA, hAT, hγ⟩ := exists_extension_approximatesFrom U Vt T hVt F (m - sV + n)
        (fun i x hi hx => hsupp i x (by omega) hx) P hP (fun i x hx => hPT i x hx) a ha
      obtain ⟨R, φ, hR, hRT, hcone⟩ := exists_isPerfect_cone W V hWV hV hWVc T hTW F hqc
        (m - sV + n) (fun i hi => hvan i (by push_cast; omega)) A hA hAT γ hγ
      obtain ⟨F', v, w, hT₃⟩ := distinguished_cocone_triangle φ
      have hRpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) R :=
        RingedSpace.IsPerfect.isPseudoCoherent hR
      have hRqc : ∀ i : ℤ,
          ((DerivedCategory.homologyFunctor X.Modules i).obj R).IsQuasicoherent :=
        isQuasicoherentDerived_of_isPseudoCoherent X R hRpc
      have hF'qc : ∀ i : ℤ,
          ((DerivedCategory.homologyFunctor X.Modules i).obj F').IsQuasicoherent :=
        (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ext_of_isTriangulatedClosed₃ _ hT₃
            hRqc hqc
      have hF'pc : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) F' (m - (sU + sV)) :=
        RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished (m - (sU + sV)) _ hT₃
          (by obtain ⟨K, hK, e⟩ := hRpc; exact ⟨K, hK _, e⟩) hpc
      obtain ⟨R', hR', hR'T, α', hα'⟩ := ih F' hF'qc hF'pc
        (fun i x hi hx => isZero_stalk_homology_obj₃_of_distinguished_anyModel X.ringCatSheaf T
          (m - (sU + sV)) _ hT₃ hRT (fun j hj y hy => hsupp j y hj hy) i hi x hx)
        (fun i hi => hcone F' v w hT₃ i hi)
      obtain ⟨R'', u', v', hT'', ψ, hψ⟩ :=
        DerivedCategory.exists_approximatesFrom_of_triangle _ hT₃ m α' hα'
      exact ⟨R'', Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished _
          hT'' hR hR',
        fun i x hx => AlgebraicGeometry.isZero_stalk_homology_obj₂_of_distinguished X.ringCatSheaf
          T _ hT'' hRT hR'T i x hx, ψ, hψ⟩
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWc
  obtain ⟨b, hb⟩ := RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom
    (X := W.toScheme.toRingedSpace) ((derivedRestrict W.ι).obj E) (m - (sU + sV))
    (isPseudoCoherentFrom_derivedRestrict W E (m - (sU + sV)) hpc)
  have hn := Int.self_le_toNat (b - (m - sV))
  exact key (b - (m - sV)).toNat E hqc hpc hsupp fun i hi => hb i (by omega)

/-- Approximation by perfect complexes holds on every quasi-compact and quasi-separated scheme. -/
@[stacks 08ES]
theorem hasApproximationByPerfectComplexes (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : HasApproximationByPerfectComplexes X := by
  refine hasApproximationByPerfectComplexes_of_iso X.topIso.symm
    (Stacks.AlgebraicGeometry.InductionPrinciple.induction_top
      (fun W : X.Opens => HasApproximationByPerfectComplexes W.toScheme)
      (fun W hW => by
        have : IsAffine W.toScheme := hW
        exact hasApproximationByPerfectComplexes_of_isAffine W.toScheme)
      (fun U V hU hV hPU _ _ => ?_))
  let S := U ⊔ V
  have himage : ∀ O : X.Opens, O ≤ S → S.ι ''ᵁ (S.ι ⁻¹ᵁ O) = O := fun O hO => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hO
  have hcompact : ∀ O : X.Opens, IsCompact (O : Set X) → O ≤ S →
      IsCompact ((S.ι ⁻¹ᵁ O : S.toScheme.Opens) : Set S.toScheme) := fun O hO hOS => by
    rw [S.ι.isOpenEmbedding.isEmbedding.isCompact_iff, ← Scheme.Hom.coe_image, himage O hOS]
    exact hO
  have : IsAffine V.toScheme := hV
  have hV' : IsAffineOpen (S.ι ⁻¹ᵁ V) :=
    IsAffine.of_isIso (S.ι.isoImage (S.ι ⁻¹ᵁ V) ≪≫ X.isoOfEq (himage V le_sup_right)).hom
  refine hasApproximationByPerfectComplexes_of_sup_affine (S.ι ⁻¹ᵁ U) (S.ι ⁻¹ᵁ V) ?_
    (hcompact U hU le_sup_left) hV' ?_
    (hasApproximationByPerfectComplexes_of_iso
      (S.ι.isoImage (S.ι ⁻¹ᵁ U) ≪≫ X.isoOfEq (himage U le_sup_left)) hPU)
  · exact eq_top_iff.2 fun y _ => y.2
  · exact hcompact (U ⊓ V) (hU.inter_of_isOpen hV.isCompact U.isOpen V.isOpen)
      (inf_le_left.trans le_sup_left)

end AlgebraicGeometry.PerfectApproximation

end
