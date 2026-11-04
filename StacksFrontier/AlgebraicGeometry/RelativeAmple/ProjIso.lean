module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.DirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.GradedDirectImage
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.GluedComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Statement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A universally closed morphism with a relatively ample module is a relative `Proj`: Tag 0C6J

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module ample relative to `f`
([Stacks, Tag 01VH]); `f` is then quasi-compact (part of the definition) and quasi-separated
(`Stacks.RelativeAmple.IsRelativelyAmple.quasiSeparated`, from [Stacks, Tag 01VI]). Let
`𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` be the quasi-coherent graded `𝒪_S`-algebra
`Stacks.RelativeAmple.directImageAlgebra f L` and `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` the adjunction
map, the datum `Stacks.RelativeAmple.directImagePowerMap f L` of [Stacks, Tag 01O8]. This file
proves

* clause (5) of [Stacks, Tag 01VJ], the assertion `U(ψ) = X`, for this `𝒜` and this `ψ`
  (`coveringOpen_directImagePowerMap`), so that the morphism `r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` of
  [Stacks, Tag 01O9] is a morphism `r : X ⟶ Proj_S(𝒜)` over `S`
  (`relativeAmpleProjHom`, `relativeAmpleProjHom_toBase`) — the canonical morphism of
  [Stacks, Tag 01VJ];
* **[Stacks, Tag 0C6J]**: if moreover `f` is universally closed, `r` is an isomorphism
  (`isIso_relativeAmpleProjHom`).

## The route

Being an isomorphism is local on the target, and `Proj_S(𝒜)` is covered by the preimages of the
affine opens `V` of `S`, each of which is the chart `Proj 𝒜(V)` of [Stacks, Tag 01NQ]. Over such a
`V` the morphism `r` is, by clause (3) of [Stacks, Tag 01O9], the morphism of [Stacks, Tag 01NK]
for the graded map `𝒜(V) ⟶ Γ_*(f⁻¹V, L|_{f⁻¹V})` induced by `ψ`
(`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.affineDatum`). For the
adjunction map `ψ` that graded map is an isomorphism of graded rings: the sections of `f_* L^{⊗ d}`
over `V` are the sections of `L^{⊗ d}` over `f⁻¹V` (`sectionRingEquiv`, `affineDatum_eq_comap`).
So, up to that isomorphism, `r` over `V` is the canonical morphism `f⁻¹V ⟶ Proj Γ_*(f⁻¹V, L)` of
[Stacks, Tag 01PZ] (`Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued`), for the
module `L|_{f⁻¹V}`, which is ample by the definition of relative ampleness. The source's argument
for that morphism — an open immersion with dense image by [Stacks, Tag 01Q1], with closed image
by [Stacks, Tag 01W6] since `f⁻¹V ⟶ V` is universally closed and `Proj` is separated — is
`Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple`, and it makes `r` an
isomorphism over every affine open of `S` (`isIso_glued_affineDatum`), hence an isomorphism
(`isIso_globalMorphism`). The same affine comparison gives `U(ψ) = X`: over `V` the open `U(ψ)`
is the union of the nonvanishing opens of the homogeneous sections of positive degree of
`Γ_*(f⁻¹V, L)`, which is all of `f⁻¹V` because `L|_{f⁻¹V}` is ample.

## References

* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul
  (restrictPowSection restrictPowSectionHom)

universe u

namespace Stacks.RelativeAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

section QCQS

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  [QuasiCompact f] [QuasiSeparated f]

section Affine

variable (V : S.Opens)

/-- The restriction of `L` to `f⁻¹(V)`. -/
abbrev restrictedModule : (f ⁻¹ᵁ V).toScheme.Modules :=
  (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L

/-- **The degreewise comparison** `Γ(V, f_* L^{⊗ n}) ⟶ Γ_*(f⁻¹V, L|_{f⁻¹V})_n`: a section of
`L^{⊗ n}` over `f⁻¹V`, read as a global section of `(L|_{f⁻¹V})^{⊗ n}` on the open subscheme
`f⁻¹V`, and then as a morphism out of the monoidal unit. It is the degree-`n` component of the
graded map `𝒜(V) ⟶ Γ_*(f⁻¹V, L|_{f⁻¹V})` that the adjunction map induces over `V`. -/
def sectionPieceHom (n : ℕ) :
    (directImageAlgebra f L).sectionPieces V n →+ powSections (restrictedModule f L V) n :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv _
      (natTensorPow (restrictedModule f L V) n)).symm.toAddMonoidHom.comp
    ((restrictPowSectionHom L (f ⁻¹ᵁ V) n).comp ((directImagePowerMap f L).valueHom n V))

/-- The degreewise comparison, read on global sections. -/
theorem globalSection_sectionPieceHom (n : ℕ) (a : (directImageAlgebra f L).sectionPieces V n) :
    globalSection _ _ (sectionPieceHom f L V n a)
      = restrictPowSection L (f ⁻¹ᵁ V) n ((directImagePowerMap f L).value n V a) :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv _ _).apply_symm_apply _

/-- An isomorphism of modules is bijective on sections over any open. -/
private theorem bijective_hom_app {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) (W : Z.Opens) :
    Function.Bijective (fun a : Γ(A, W) => e.hom.app W a) :=
  Function.bijective_iff_has_inverse.2 ⟨fun b => e.inv.app W b,
    fun x => Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e.symm W x,
    fun y => Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e W y⟩

omit [QuasiCompact f] [QuasiSeparated f] in
/-- Reading a section of `L^{⊗ n}` over an open `U` as a global section of `(L|_U)^{⊗ n}` is a
bijection. -/
theorem bijective_restrictPowSection (n : ℕ) :
    Function.Bijective (restrictPowSection L (f ⁻¹ᵁ V) n) := by
  have h : (restrictPowSection L (f ⁻¹ᵁ V) n) = fun x =>
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictNatTensorPowIso L
        (f ⁻¹ᵁ V) n).hom.app ⊤
        (Stacks.NonvanishingLocusRestrict.restrictSection (f ⁻¹ᵁ V) (natTensorPow L n) x) :=
    funext (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq L _ n)
  rw [h]
  refine Function.Bijective.comp (g := fun y =>
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictNatTensorPowIso L
        (f ⁻¹ᵁ V) n).hom.app ⊤ y)
    (f := fun x => Stacks.NonvanishingLocusRestrict.restrictSection (f ⁻¹ᵁ V) (natTensorPow L n) x)
    (bijective_hom_app _ ⊤) ?_
  exact ⟨fun x y hxy => by
      rw [← Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection _ _ x,
        ← Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection _ _ y]
      exact congrArg _ hxy,
      fun y => ⟨_,
        Stacks.NonvanishingLocusRestrict.restrictSection_sectionOfRestrictGlobalSection _ _ y⟩⟩

/-- The comparison of the two spellings of the tensor powers is bijective on sections. -/
theorem bijective_powCompare_inv_app (n : ℕ) (W : X.Opens) :
    Function.Bijective (fun a : Γ(tensorPowerModule X L n, W) => (powCompare L n).inv.app W a) :=
  bijective_hom_app (powCompare L n).symm W

/-- **The degreewise comparison is bijective.** -/
theorem bijective_sectionPieceHom (n : ℕ) : Function.Bijective (sectionPieceHom f L V n) :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv _ _).symm.bijective.comp
    ((bijective_restrictPowSection f L V n).comp (bijective_powCompare_inv_app L n (f ⁻¹ᵁ V)))

/-- **The degreewise comparison is multiplicative**: the product in `𝒜(V)` goes to the product
in `Γ_*(f⁻¹V, L|_{f⁻¹V})`. -/
theorem sectionPieceHom_mul (n m : ℕ) (a : (directImageAlgebra f L).sectionPieces V n)
    (b : (directImageAlgebra f L).sectionPieces V m) :
    sectionPieceHom f L V (n + m) (((directImageAlgebra f L).mul (n : ℤ) (m : ℤ)).app V a b)
      = mul (sectionPieceHom f L V n a) (sectionPieceHom f L V m b) := by
  apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv _ _).injective
  show globalSection _ _ (sectionPieceHom f L V (n + m) _)
    = globalSection _ _ (mul (sectionPieceHom f L V n a) (sectionPieceHom f L V m b))
  rw [← Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_globalSection,
    globalSection_sectionPieceHom, globalSection_sectionPieceHom, globalSection_sectionPieceHom]
  exact (congrArg (restrictPowSection L (f ⁻¹ᵁ V) (n + m))
      ((directImagePowerMap f L).value_mul n m V a b)).trans
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_localMulSections
      L (f ⁻¹ᵁ V) n m _ _)

/-- The degreewise comparison, as an additive equivalence. -/
def sectionPieceEquiv (n : ℕ) :
    (directImageAlgebra f L).sectionPieces V n ≃+ powSections (restrictedModule f L V) n :=
  AddEquiv.ofBijective (sectionPieceHom f L V n) (bijective_sectionPieceHom f L V n)

/-- The degreewise equivalence is the degreewise comparison. -/
theorem sectionPieceEquiv_apply (n : ℕ) (a : (directImageAlgebra f L).sectionPieces V n) :
    sectionPieceEquiv f L V n a = sectionPieceHom f L V n a := rfl

/-- The additive equivalence `𝒜(V) ≃ Γ_*(f⁻¹V, L|_{f⁻¹V})` of graded rings of sections, degree by
degree. -/
def sectionRingAddEquiv :
    (directImageAlgebra f L).sectionRing V ≃+ sectionRing (restrictedModule f L V) where
  toFun := DirectSum.map fun n => (sectionPieceEquiv f L V n).toAddMonoidHom
  invFun := DirectSum.map fun n => (sectionPieceEquiv f L V n).symm.toAddMonoidHom
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n a => simp [DirectSum.map_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n a => simp [DirectSum.map_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_add' := map_add _

/-- The additive equivalence on a homogeneous element. -/
theorem sectionRingAddEquiv_of (n : ℕ) (a : (directImageAlgebra f L).sectionPieces V n) :
    sectionRingAddEquiv f L V (DirectSum.of _ n a)
      = DirectSum.of _ n (sectionPieceHom f L V n a) :=
  DirectSum.map_of _ n a

/-- **The ring isomorphism `𝒜(V) ≅ Γ_*(f⁻¹V, L|_{f⁻¹V})`.** -/
def sectionRingEquiv :
    (directImageAlgebra f L).sectionRing V ≃+* sectionRing (restrictedModule f L V) where
  toEquiv := (sectionRingAddEquiv f L V).toEquiv
  map_add' := (sectionRingAddEquiv f L V).map_add'
  map_mul' x y := by
    change sectionRingAddEquiv f L V (x * y)
      = sectionRingAddEquiv f L V x * sectionRingAddEquiv f L V y
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | of n a =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
      | of m b =>
        rw [DirectSum.of_mul_of, sectionRingAddEquiv_of, sectionRingAddEquiv_of,
          sectionRingAddEquiv_of, ← Stacks.SectionRingChartMap.of_mul_eq]
        exact congrArg _ (sectionPieceHom_mul f L V n m a b)

/-- The ring isomorphism on a homogeneous element. -/
theorem sectionRingEquiv_of (n : ℕ) (a : (directImageAlgebra f L).sectionPieces V n) :
    sectionRingEquiv f L V (DirectSum.of _ n a) = DirectSum.of _ n (sectionPieceHom f L V n a) :=
  sectionRingAddEquiv_of f L V n a

/-- **The ring isomorphism `𝒜(V) ≅ Γ_*(f⁻¹V, L|_{f⁻¹V})`, as a homomorphism of graded rings.** -/
def sectionGradedHom :
    (directImageAlgebra f L).grading V →+*ᵍ grading (restrictedModule f L V) where
  toRingHom := (sectionRingEquiv f L V).toRingHom
  map_mem := by
    rintro i x ⟨a, rfl⟩
    exact ⟨sectionPieceHom f L V i a, (sectionRingEquiv_of f L V i a).symm⟩

/-- The inverse of `sectionGradedHom`, as a homomorphism of graded rings. -/
def sectionGradedHomInv :
    grading (restrictedModule f L V) →+*ᵍ (directImageAlgebra f L).grading V where
  toRingHom := (sectionRingEquiv f L V).symm.toRingHom
  map_mem := by
    rintro i y ⟨b, rfl⟩
    refine ⟨(sectionPieceEquiv f L V i).symm b, ?_⟩
    change _ = (sectionRingEquiv f L V).symm _
    rw [RingEquiv.eq_symm_apply, sectionRingEquiv_of, ← sectionPieceEquiv_apply,
      AddEquiv.apply_symm_apply]

/-- `sectionGradedHomInv` is a left inverse of `sectionGradedHom`. -/
theorem sectionGradedHomInv_comp :
    (sectionGradedHomInv f L V).comp (sectionGradedHom f L V) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (sectionRingEquiv f L V).symm_apply_apply x

/-- `sectionGradedHomInv` is a right inverse of `sectionGradedHom`. -/
theorem sectionGradedHom_comp :
    (sectionGradedHom f L V).comp (sectionGradedHomInv f L V) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (sectionRingEquiv f L V).apply_symm_apply x

/-- **The datum of [Stacks, Tag 01NK] that the adjunction map induces over `V` is the identity of
`Γ_*(f⁻¹V, L|_{f⁻¹V})` pulled back along `sectionGradedHom`.** -/
theorem affineDatum_eq_comap :
    (directImagePowerMap f L).affineDatum V
      = Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (sectionGradedHom f L V)
          (Stacks.SectionRingGluedComparison.canonicalSections (restrictedModule f L V)) := by
  refine Stacks.SectionRingGluedComparison.gradedSections_ext ?_
  rintro n ⟨_, a, rfl⟩
  show restrictPowSection L (f ⁻¹ᵁ V) n ((directImagePowerMap f L).value n V
      ((DirectSum.of _ n a : (directImageAlgebra f L).sectionRing V) n))
    = globalSection _ _ ((sectionRingEquiv f L V (DirectSum.of _ n a)) n)
  rw [sectionRingEquiv_of, DirectSum.of_eq_same, DirectSum.of_eq_same,
    globalSection_sectionPieceHom]

end Affine

section Ample

variable {f L}

omit [QuasiCompact f] [QuasiSeparated f] in
/-- For `L` ample relative to `f`, its restriction to the preimage of an affine open is ample:
the definition [Stacks, Tag 01VH]. -/
theorem isAmple_restrictedModule (hL : IsRelativelyAmple f L) {V : S.Opens} (hV : IsAffineOpen V) :
    Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme (restrictedModule f L V) :=
  hL.isAmple_preimage f L V hV

/-- For `L` ample relative to `f`, the covering open of the datum induced over an affine `V` is
all of `f⁻¹V`. -/
theorem coveringOpen_affineDatum_eq_top (hL : IsRelativelyAmple f L) {V : S.Opens}
    (hV : IsAffineOpen V) : ((directImagePowerMap f L).affineDatum V).coveringOpen = ⊤ :=
  (congrArg (fun ψ => ψ.coveringOpen) (affineDatum_eq_comap f L V)).trans
    ((Stacks.SectionRingGluedComparison.coveringOpen_comap_of_comp_eq_id _ _
      (sectionGradedHom_comp f L V)
      (Stacks.SectionRingGluedComparison.canonicalSections (restrictedModule f L V))).trans
      (Stacks.SectionRingGluedComparison.coveringOpen_canonicalSections_eq_top _
        (isAmple_restrictedModule hL hV)))

/-- **[Stacks, Tag 01VJ] (5), `U(ψ) = X`**, for `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` and `ψ` the adjunction
map: the open `U(ψ)` of [Stacks, Tag 01O8] is all of `X` when `L` is ample relative to `f`. -/
theorem coveringOpen_directImagePowerMap (hL : IsRelativelyAmple f L) :
    (directImagePowerMap f L).coveringOpen = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  have h2 := (directImagePowerMap f L).coveringOpen_affineDatum V
  rw [coveringOpen_affineDatum_eq_top hL hV] at h2
  have hx' : (⟨x, hxV⟩ : (f ⁻¹ᵁ V).toScheme) ∈
      (f ⁻¹ᵁ V).ι ⁻¹ᵁ (directImagePowerMap f L).coveringOpenOver V := h2 ▸ trivial
  exact (directImagePowerMap f L).coveringOpenOver_le_coveringOpen hV hx'

/-- **Over an affine open `V` of the base, `r_{L, ψ}` is an isomorphism**, for `f` universally
closed and `L` ample relative to `f`: the morphism of [Stacks, Tag 01NK] for the induced datum is
an isomorphism. -/
theorem isIso_glued_affineDatum [UniversallyClosed f] (hL : IsRelativelyAmple f L)
    {V : S.Opens} (hV : IsAffineOpen V) :
    IsIso ((directImagePowerMap f L).affineDatum V).glued := by
  have : UniversallyClosed (f ⁻¹ᵁ V).toScheme.toSpecΓ := by
    have : IsAffine V.toScheme := hV
    exact Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ (f ∣_ V)
  have : IsIso
      (Stacks.SectionRingGluedComparison.canonicalSections (restrictedModule f L V)).glued :=
    Stacks.SectionRingGluedComparison.isIso_glued_canonicalSections _
      (isAmple_restrictedModule hL hV) this
  have h := Stacks.SectionRingGluedComparison.isIso_glued_comap _ _
    (sectionGradedHomInv_comp f L V) (sectionGradedHom_comp f L V)
    (Stacks.SectionRingGluedComparison.canonicalSections (restrictedModule f L V))
  exact affineDatum_eq_comap f L V ▸ h

/-- **`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` is an isomorphism**, for `f` universally closed and `L` ample
relative to `f`. Being an isomorphism is local on the target; over the preimage of an affine open
`V` of `S` the morphism is `isIso_glued_affineDatum` followed by the chart of
[Stacks, Tag 01NQ] at `V`, an isomorphism onto that preimage. -/
theorem isIso_globalMorphism [UniversallyClosed f] (hL : IsRelativelyAmple f L) :
    IsIso ((directImagePowerMap f L).globalMorphism (relativeProj (directImageAlgebra f L))) := by
  let P := directImagePowerMap f L
  let rp := relativeProj (directImageAlgebra f L)
  have hU : (⨆ V : S.affineOpens, rp.toBase ⁻¹ᵁ (V : S.Opens)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top S,
      Scheme.Hom.preimage_top]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hU
    fun V => ?_
  show IsIso (P.globalMorphism rp ∣_ rp.toBase ⁻¹ᵁ V.1)
  have hRW : P.globalMorphism rp ⁻¹ᵁ (rp.toBase ⁻¹ᵁ V.1) = P.toBase ⁻¹ᵁ V.1 := by
    rw [← Scheme.Hom.comp_preimage, P.globalMorphism_comp_toBase rp]
  let c : AlgebraicGeometry.Proj ((directImageAlgebra f L).grading V.1)
      ≅ (rp.toBase ⁻¹ᵁ V.1).toScheme :=
    (rp.chart_isPullback V.1 V.2).isoPullback ≪≫ pullbackRestrictIsoRestrict rp.toBase V.1
  have hc : c.hom ≫ (rp.toBase ⁻¹ᵁ V.1).ι = rp.chart V.1 V.2 := by
    simp only [c, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      IsPullback.isoPullback_hom_fst]
  have := isIso_glued_affineDatum hL V.2
  have hg : P.globalMorphism rp ∣_ (rp.toBase ⁻¹ᵁ V.1)
      = (P.coveringOpen.toScheme.isoOfEq hRW).hom ≫ (P.toBaseIso V.1 V.2).hom ≫
        (P.datumIso V.1).inv ≫ (P.affineDatum V.1).glued ≫ c.hom := by
    rw [← cancel_mono (rp.toBase ⁻¹ᵁ V.1).ι, morphismRestrict_ι]
    simp only [Category.assoc, hc]
    show _ = (P.coveringOpen.toScheme.isoOfEq hRW).hom ≫ P.piece rp V
    rw [← P.ι_globalMorphism rp V, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  rw [hg]
  infer_instance

end Ample

/-- **The canonical morphism `r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` of [Stacks, Tag 01VJ]**, for
`L` ample relative to a quasi-compact quasi-separated `f`: the morphism
`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O9] for the adjunction map `ψ`, read on `X`
through `U(ψ) = X` (`coveringOpen_directImagePowerMap`). -/
@[ega "II 4.6.3"]
def relativeAmpleProjHom (hL : IsRelativelyAmple f L) :
    X ⟶ (relativeProj (directImageAlgebra f L)).scheme :=
  X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImagePowerMap hL).symm).hom ≫
    (directImagePowerMap f L).globalMorphism (relativeProj (directImageAlgebra f L))

/-- **`r` is a morphism over `S`**: `r` followed by the structure morphism of `Proj_S(𝒜)` is
`f`. -/
theorem relativeAmpleProjHom_toBase (hL : IsRelativelyAmple f L) :
    relativeAmpleProjHom f L hL ≫ (relativeProj (directImageAlgebra f L)).toBase = f := by
  rw [relativeAmpleProjHom, Category.assoc, Category.assoc,
    (directImagePowerMap f L).globalMorphism_comp_toBase, GradedPowerMap.toBase,
    ← Category.assoc (X.isoOfEq _).hom, Scheme.isoOfEq_hom_ι, ← Category.assoc,
    Scheme.toIso_inv_ι, Category.id_comp]

end QCQS

/-- **[Stacks, Tag 0C6J].** Let `f : X ⟶ S` be a universally closed morphism of schemes and `L` an
invertible `𝒪_X`-module ample relative to `f`. Then the canonical morphism
`r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` of [Stacks, Tag 01VJ] is an isomorphism.

Here `⨁_{d ≥ 0} f_* L^{⊗ d}` is `directImageAlgebra f L`, the relative `Proj` is that of
[Stacks, Tag 01NQ], and `r` is `relativeAmpleProjHom f L hL`, the morphism `r_{L, ψ}` of
[Stacks, Tag 01O9] for the adjunction map `ψ` on its source `U(ψ) = X`. The quasi-compactness and
quasi-separatedness of `f` that the algebra needs are part of, resp. a consequence of, relative
ampleness ([Stacks, Tags 01VH, 01VI]); they are not hypotheses. -/
@[stacks 0C6J]
theorem isIso_relativeAmpleProjHom {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : IsRelativelyAmple f L) :
    haveI := hL.quasiCompact
    haveI := hL.quasiSeparated
    IsIso (relativeAmpleProjHom f L hL) := by
  have := hL.quasiCompact
  have := hL.quasiSeparated
  have := isIso_globalMorphism hL
  rw [relativeAmpleProjHom]
  infer_instance

end Stacks.RelativeAmple

end
