module

public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.TwistSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement

/-!
# Relative flatness of the twists on a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra. If the homogeneous piece `A_n`
is a flat `𝒪_S`-module for all sufficiently large `n`, then every twist `𝒪_X(t)` on the relative
projective spectrum `X = Proj_S(A)` is flat over `S`.

Flatness of a quasi-coherent module over the target is a condition on affine opens upstairs and
downstairs (`AlgebraicGeometry.isFlatOver_tfae`). The affine opens used here are the standard
opens `D₊(f)` of the charts: the chart over an affine open `U` of the base is the absolute
`Proj (A(U))`, the twists restrict on it to the absolute twists, and the sections of the absolute
twist over `D₊(f)` are flat over `Γ(S, U)` by
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.flat_twistSections`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFlat.isFlatOver_twist`: every twist of a relative `Proj` is
  flat over the base under eventual flatness of the homogeneous pieces. This is the second
  assertion of Stacks tag 0D4C.

## Implementation notes

The twists are taken as a parameter: `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is
the structure Tag 01NR produces, and the statement is made for an arbitrary term of it. That is
this development's convention for every other result about the twists, and it is the general
form — the assertion about a particular glued family of twists is the instantiation of this one
at that family.

The quantification is not vacuous. Tag 01NR's existence assertion is discharged, for every
quasi-coherent graded `𝒪_S`-algebra and with no hypothesis beyond the algebra itself, by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`
(`GluedTwistAlgebra/Assemble.lean`, `@[stacks 01NR]`), so the twists of Tag 0D4C's statement do
exist and this result applies to them.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFlat

/-- **Flatness of sections transported along an identification of a restricted module with a
module on an open immersion's source.** If `e` identifies the restriction of `F` along the open
immersion `j` with `T`, then the sections of `F` over the image of an open `V` are the sections of
`T` over `V`, and the comparison is linear for the two base-ring actions provided those actions
agree under the identification of the rings of functions. -/
public theorem flat_sections_of_moduleIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (T : Y.Modules) (e : F.restrict j ≅ T)
    (V : Y.Opens) {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, V)) (ψ : R →+* Γ(X, j ''ᵁ V))
    (hρ : (j.appIso V).hom.hom.comp ψ = ρ)
    (hflat : letI : Module R Γ(T, V) := Module.compHom _ ρ
      Module.Flat R Γ(T, V)) :
    letI : Module R Γ(F, j ''ᵁ V) := Module.compHom _ ψ
    Module.Flat R Γ(F, j ''ᵁ V) := by
  let _ : Module R Γ(T, V) := Module.compHom _ ρ
  let _ : Module R Γ(F, j ''ᵁ V) := Module.compHom _ ψ
  let q : Γ(T, V) →ₗ[R] Γ(F, j ''ᵁ V) :=
    { toFun := fun x => (F.restrictAppIso j V).hom (e.inv.app V x)
      map_add' := by intros; simp
      map_smul' := by
        intro r x
        change (F.restrictAppIso j V).hom (e.inv.app V (ρ r • x)) =
          ψ r • (F.restrictAppIso j V).hom (e.inv.app V x)
        rw [Scheme.Modules.Hom.app_smul]
        have he : (j.appIso V).inv (ρ r) = ψ r := by
          rw [← hρ]
          exact ConcreteCategory.congr_hom (j.appIso V).hom_inv_id (ψ r)
        change (j.appIso V).inv (ρ r) •
          (F.restrictAppIso j V).hom (e.inv.app V x) = _
        rw [he] }
  have hbij : Function.Bijective q := by
    change Function.Bijective fun x => (F.restrictAppIso j V).hom (e.inv.app V x)
    refine Function.Bijective.comp (ConcreteCategory.bijective_of_isIso _) ?_
    have : IsIso (e.inv.app V) := by
      change IsIso ((Scheme.Modules.toPresheaf Y ⋙
        (CategoryTheory.evaluation _ _).obj (Opposite.op V)).map e.inv)
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (e.inv.app V)
  exact (Module.Flat.equiv_iff (LinearEquiv.ofBijective q hbij)).mp hflat

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- **The structure morphism of a relative `Proj`, read on sections over a standard affine open of
a chart.** It is the composite of the structure map `Γ(S, U) → A(U)_0 → A(U)_(f)` with the
identification of `A(U)_(f)` with the functions on `D₊(f)`. -/
public theorem chart_appLE (U : S.Opens) (hU : IsAffineOpen U) {d : ℕ}
    {f : A.sectionRing U} (hf : f ∈ A.grading U d) (hd : 0 < d)
    (h : Proj.basicOpen (A.grading U) f ≤
      ((relativeProj A).chart U hU ≫ (relativeProj A).toBase) ⁻¹ᵁ U) :
    letI := A.sectionRingAlgebra U
    ((relativeProj A).chart U hU ≫ (relativeProj A).toBase).appLE U
        (Proj.basicOpen (A.grading U) f) h =
      CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers f)).comp
          (GradedRing.toGradeZero (A.grading U) (A.strHom_mem U))) ≫
        Proj.awayToSection (A.grading U) f := by
  let _ := A.sectionRingAlgebra U
  rw [A.toGradeZero_eq U]
  have hdef : projInclusionToOpen A U hU =
      Proj.toSpecZero (A.grading U) ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U))) ≫
        hU.isoSpec.inv := rfl
  have hV := Proj.isAffineOpen_basicOpen (A.grading U) f hf hd
  have ht : (Proj.basicOpen (A.grading U) f).ι ≫ Proj.toSpecZero (A.grading U) =
      Proj.basicOpenToSpec (A.grading U) f ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero (A.grading U) f hf hd]
    simp [Proj.awayι, ← Proj.basicOpenIsoSpec_hom (A.grading U) f hf hd]
  apply Spec.map_injective
  apply (cancel_mono hU.fromSpec).mp
  apply (cancel_epi hV.isoSpec.hom).mp
  rw [← Category.assoc, hV.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
    ← hU.isoSpec_hom, hU.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι,
    ((relativeProj A).chart_isPullback U hU).w, hdef]
  simp only [Spec.map_comp, CommRingCat.ofHom_comp, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι]
  rw [reassoc_of% ht]
  simp only [Proj.basicOpenToSpec, Category.assoc]

include A in
/-- **Relative flatness of the twists on a relative projective spectrum.**

If the homogeneous piece `A_n` of a quasi-coherent graded `𝒪_S`-algebra is a flat `𝒪_S`-module for
every sufficiently large `n`, then every homogeneous piece of the glued graded algebra of twists on
the relative projective spectrum of `A` is flat over the base.

The twist data is a parameter, so this is the general form of the assertion, of which the
statement for any particular glued family of twists is an instance — in particular for the
canonical one, `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which Tag
01NR supplies unconditionally.

The criterion used is the affine-open-covering criterion of `AlgebraicGeometry.isFlatOver_tfae`,
with the affine opens of the base downstairs and, over each of them, the images under the chart of
the standard opens of the absolute `Proj` at homogeneous elements of positive degree. -/
@[stacks 0D4C "relative flatness of the twists"]
public theorem isFlatOver_twist (D : TwistData A) (t : ℤ)
    (hflat : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ))) :
    IsFlatOver (relativeProj A).toBase.toLRSHom.toShHom (D.algebra.piece t) := by
  classical
  obtain ⟨N, hN⟩ := hflat
  let p := (relativeProj A).toBase
  let F : (relativeProj A).scheme.Modules := D.algebra.piece t
  let _ : F.IsQuasicoherent := D.isQuasicoherent t
  refine ((isFlatOver_tfae p F).out 4 1).mp ?_
  refine ⟨S.affineOpens, Subtype.val,
    TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top S), fun U => U.2, ?_⟩
  intro U
  let j := (relativeProj A).chart U.1 U.2
  let _ : IsOpenImmersion j := isOpenImmersion_chart (relativeProj A) U.1 U.2
  let V : (Σ m : ℕ+, A.grading U.1 (m : ℕ)) → (AlgebraicGeometry.Proj (A.grading U.1)).Opens :=
    fun i => Proj.basicOpen (A.grading U.1) (i.2 : A.sectionRing U.1)
  have hV : (⨆ i, V i) = ⊤ := Proj.iSup_basicOpen_homogeneous_eq_top (A.grading U.1)
  have hcover : (⨆ i, j ''ᵁ V i) = p ⁻¹ᵁ U.1 := by
    rw [← j.image_iSup, hV]
    exact chart_image_top (relativeProj A) U.1 U.2
  refine ⟨_, fun i => j ''ᵁ V i, hcover, fun i => ?_, fun i => ?_⟩
  · exact j.isAffineOpen_iff_of_isOpenImmersion.mpr
      (Proj.isAffineOpen_basicOpen (A.grading U.1) _ i.2.2 i.1.2)
  · let T : (AlgebraicGeometry.Proj (A.grading U.1)).Modules :=
      twistingSheaf (A.grading U.1) t
    let _ := A.sectionRingAlgebra U.1
    let φ := (HomogeneousLocalization.fromZeroRingHom (A.grading U.1)
      (Submonoid.powers (i.2 : A.sectionRing U.1))).comp
        (GradedRing.toGradeZero (A.grading U.1) (A.strHom_mem U.1))
    have hUV : j ''ᵁ V i ≤ p ⁻¹ᵁ U.1 := (le_iSup _ i).trans hcover.le
    refine flat_sections_of_moduleIso j F T (D.chartData.chartIso U.1 U.2 t) (V i)
      ((Proj.awayToSection (A.grading U.1) (i.2 : A.sectionRing U.1)).hom.comp φ)
      (p.appLE U.1 (j ''ᵁ V i) hUV).hom ?_ ?_
    · change (p.appLE U.1 (j ''ᵁ V i) hUV ≫ (j.appIso (V i)).hom).hom = _
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      exact congrArg CommRingCat.Hom.hom
        (chart_appLE A U.1 U.2 i.2.2 i.1.2 _)
    · exact A.flat_twistSections U.1 N hN U.2 i.1.2 i.2.2 t

end Stacks.AlgebraicGeometry.RelativeProjFlat

end
