module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.SourceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointTwists

/-!
# The morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` of algebraic spaces, from a graded map `ψ`

[Stacks, Tag 0D2Z] fixes a scheme `S`, an algebraic space `Y` over `S`, a quasi-coherent graded
`𝒪_Y`-algebra `𝒜` with relative Proj `π : Proj_Y(𝒜) ⟶ Y`, a morphism `f : X ⟶ Y`, an invertible
`𝒪_X`-module `ℒ` and a homomorphism of graded `𝒪_X`-algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`.  On
the open subspace `U(ψ) ⊆ X` where `f^*𝒜_d ⟶ ℒ^{⊗ d}` is surjective for some `d ≥ 1` it produces
a morphism of algebraic spaces over `Y`, `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`, and a map of graded
algebras `θ : r^*(⨁ 𝒪(d)) ⟶ ⨁ ℒ^{⊗ d}|_{U(ψ)}`, characterized by three properties.  The proof is
"omitted"; its hint reduces everything to the scheme case [Stacks, Tag 01O9] by describing
`U(ψ)` as a subfunctor of `X` and attaching to each test scheme of it the morphism into
`Proj_Y(𝒜)` given by the construction of the relative Proj.

This file carries that out with `ψ` an actual homomorphism of graded algebras
(`…RelativeProjQcohSheaf.Twisting`), nothing about it carried as data.  `Proj_Y(𝒜)` is presented,
as everywhere in this library, by its base changes `T ×_Y Proj_Y(𝒜) = Proj_T(t^*𝒜)` to the scheme
points `t : T ⟶ Y` (`AlgebraicGeometry.Space.RelativeProjPoints`, the second assertion of
[Stacks, Tag 084B]).  `X` is a scheme object of the site and `f : X ⟶ Y` a point of `Y`, so that
`f^*𝒜` is the algebra `d.algebra X f` of the presentation and `ψ` is a graded map out of it.

* `U(ψ)` is the open subspace `AlgebraicGeometry.Space.subspaceOfOpens` of `X` cut out by the
  open `U(ψ)` of [Stacks, Tag 01O8] (`AlgebraicGeometry.Space.isOpenSubspace_subspaceOfOpens`),
  which is the union of the loci where `ψ_d` is surjective, `d ≥ 1`
  (`…RelativeProjInvertibleMorphism.mem_coveringOpen_iff_exists_epi`).
* `r_{ℒ,ψ}` sends a test scheme `ρ : T ⟶ X` of `U(ψ)` to the point of `Proj_Y(𝒜)` which
  `X ×_Y Proj_Y(𝒜) = Proj_X(f^*𝒜)` attaches to `T ⟶ U(ψ) ⟶ Proj_X(f^*𝒜)`, the second arrow being
  the morphism of [Stacks, Tag 01O9].

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.invertibleMorphism`: **`r_{ℒ,ψ}`**.
* `AlgebraicGeometry.Space.RelativeProjPoints.quadruplePoint`: the morphism `W ⟶ Proj_Y(𝒜)`
  which the construction of the relative Proj attaches to the quadruple
  `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`.

## Main results

* `…invertibleMorphism_comp_π`: `r_{ℒ,ψ}` is a morphism over `Y`.
* `…mem_subspaceOfOpens_of_epi`: **clause (2)(a)**.
* `…locusFactor_invertibleMorphism_of_epi`: **clause (2)(b)**.
* `…eq_invertibleMorphism`: `r_{ℒ,ψ}` is the only morphism over `Y` with clause (2)(b).
* `…invertibleTheta_clauseOne`: **`θ` and clause (1)**, after base change to the scheme point
  `f`, where the twists of `Proj_Y(𝒜)` are those of `Proj_X(f^*𝒜)`
  (`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistAlgebra`, by definition the algebra of
  `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra (d.algebra X f)`).
* `…invertibleMorphism_baseChange`, with `…RelativeProjInvertibleMorphism.coveringOpen_pullback`:
  **clause (3)** for the open and the morphism, for the squares in which `Y' ⟶ Y` is the point `f`.

## Implementation notes

**Why `X` is a scheme.**  `f^*𝒜`, `ℒ` and `ψ` on an algebraic space `X` cannot be written in this
library: the presentation of `𝒜` gives its restriction to each scheme point separately, with no
comparison between the restrictions to two points.  The source itself states clauses (2) and (3)
for schemes over `X`, and every scheme over `Y` is such a point.

**Clause (1) for `V ⟶ Y`, clause (3) for an arbitrary `Y' ⟶ Y`.**  The source states clause (1)
for `V ⟶ Y` étale, and clause (3) for an arbitrary scheme `Y'` over `Y`; both compare the
restriction of `𝒜` to two different scheme points of `Y`.  This file states them at the point `f`
itself (clause (1) on the opens of `X`, clause (3) for `Y' = X`).  The general statements, which
read that comparison off the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`), are
`AlgebraicGeometry.Space.RelativeProjSituation.clauseOne`, `…clauseThree_coveringOpen`,
`…clauseThree_morphism` and `…clauseThree_theta`, and the whole lemma is
`AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z`, in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleBaseChange.lean`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.GluedTwistAlgebra (twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space.RelativeProjPoints

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π) {X : BigFppfOver B S hS} {f : yoneda.obj X ⟶ Y}
    {L : ((BigFppfOver.toScheme B S hS).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X)) (situationAlgebra (d.algebra X f)) 1 L)

/-- A test scheme lying in `U(ψ)` has preimage `U(ψ)` equal to the whole test scheme. -/
private theorem preimage_coveringOpen_eq_top_of_mem {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (BigFppfOver.toScheme B S hS).map ρ ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen = ⊤ :=
  top_unique fun y _ => (mem_subspaceOfOpens_iff B S hS X _ ρ).1 hρ y

/-- The factorisation through `U(ψ)` of a test scheme of the locus. -/
abbrev locusLift {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ (toGradedPowerMap ψ).coveringOpen.toScheme :=
  liftOfPreimageEqTop _ _ (top_unique fun y _ => (mem_subspaceOfOpens_iff B S hS X _ ρ).1 hρ y)

/-- The factorisation through `U(ψ)` is a factorisation of the underlying morphism of schemes. -/
@[reassoc (attr := simp)]
theorem locusLift_ι {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    d.locusLift ψ ρ hρ ≫ (toGradedPowerMap ψ).coveringOpen.ι
      = (BigFppfOver.toScheme B S hS).map ρ :=
  liftOfPreimageEqTop_ι _ _ _

/-- The composite `T ⟶ U(ψ) ⟶ Proj_X(f^*𝒜)` is a morphism over the test scheme's point of `X`. -/
theorem locusLift_globalMorphism_toBase {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (d.locusLift ψ ρ hρ ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
        ≫ (relativeProj (d.algebra X f)).toBase = (BigFppfOver.toScheme B S hS).map ρ := by
  rw [Category.assoc, GradedPowerMap.globalMorphism_comp_toBase, GradedPowerMap.toBase,
    locusLift_ι_assoc]
  exact Category.comp_id _

/-- **The value of `r_{ℒ,ψ}` at a test scheme `ρ : T ⟶ X` of `U(ψ)`**: the `T`-point of `P` over
`f ∘ ρ` which the identification `T ×_Y P = Proj_T(ρ^*f^*𝒜)` of [Stacks, Tag 084B] attaches to the
composite `T ⟶ U(ψ) ⟶ Proj_X(f^*𝒜)` of [Stacks, Tag 01O9]. -/
def invertiblePoint {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    {u : yoneda.obj T ⟶ Proj // u ≫ π = yoneda.map ρ ≫ f} :=
  (d.pointEquivProjOver X f ρ).symm
    ⟨d.locusLift ψ ρ hρ ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)),
      d.locusLift_globalMorphism_toBase ψ ρ hρ⟩

/-- The scheme morphism attached to the value of `r_{ℒ,ψ}` is `T ⟶ U(ψ) ⟶ Proj_X(f^*𝒜)`. -/
theorem pointEquivProjOver_invertiblePoint {T : BigFppfOver B S hS} (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (d.pointEquivProjOver X f ρ (d.invertiblePoint ψ ρ hρ)).1
      = d.locusLift ψ ρ hρ ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)) :=
  congrArg Subtype.val ((d.pointEquivProjOver X f ρ).apply_symm_apply _)

/-- The points restrict along morphisms of test schemes. -/
theorem map_comp_invertiblePoint {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (ρ : T ⟶ X)
    (hρ : ρ ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    yoneda.map g ≫ (d.invertiblePoint ψ ρ hρ).1
      = (d.invertiblePoint ψ (g ≫ ρ) ((subspaceOfOpens B S hS X
        (toGradedPowerMap ψ).coveringOpen).map g.op hρ)).1 := by
  have hn := d.pointEquivProjOver_natural X f ρ g (d.invertiblePoint ψ ρ hρ)
  rw [d.pointEquivProjOver_invertiblePoint ψ ρ hρ] at hn
  have hl : (BigFppfOver.toScheme B S hS).map g ≫ d.locusLift ψ ρ hρ
      = d.locusLift ψ (g ≫ ρ) ((subspaceOfOpens B S hS X
        (toGradedPowerMap ψ).coveringOpen).map g.op hρ) := by
    rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι, Category.assoc,
      locusLift_ι, locusLift_ι, Functor.map_comp]
  have key : (⟨yoneda.map g ≫ (d.invertiblePoint ψ ρ hρ).1, by
      rw [Category.assoc, (d.invertiblePoint ψ ρ hρ).2, ← Category.assoc,
        ← Functor.map_comp]⟩ : {u : yoneda.obj T' ⟶ Proj // u ≫ π = yoneda.map (g ≫ ρ) ≫ f})
      = d.invertiblePoint ψ (g ≫ ρ) ((subspaceOfOpens B S hS X
        (toGradedPowerMap ψ).coveringOpen).map g.op hρ) := by
    refine (Equiv.eq_symm_apply _).2 (Subtype.ext ?_)
    rw [hn, ← Category.assoc, hl]
  exact congrArg Subtype.val key

/-- **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`, the morphism of [Stacks, Tag 0D2Z]**, as the transformation of
functors the source's proof builds: on a test scheme `ρ : T ⟶ X` of `U(ψ)` it is
`invertiblePoint`, and its naturality is the naturality of the identification
`X ×_Y Proj_Y(𝒜) = Proj_X(f^*𝒜)`. -/
@[stacks 0D2Z "variant: the morphism r_{L,psi} : U(psi) -> Proj_Y(A) for a presentation of \
Proj_Y(A) by its base changes to the scheme points of Y; \
the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
def invertibleMorphism :
    (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).toFunctor ⟶ Proj where
  app U := ↾fun a => yonedaEquiv (d.invertiblePoint ψ a.1 a.2).1
  naturality U V h := by
    ext a
    refine Eq.trans ?_ (yonedaEquiv_naturality' (d.invertiblePoint ψ a.1 a.2).1 h).symm
    exact congrArg yonedaEquiv (d.map_comp_invertiblePoint ψ h.unop a.1 a.2).symm

/-- **`r_{ℒ,ψ}` is a morphism over `Y`**, as [Stacks, Tag 0D2Z] asserts: `π ∘ r_{ℒ,ψ}` is the
restriction of `f` to `U(ψ)`. -/
@[stacks 0D2Z "variant: r_{L,psi} lies over Y, for a presentation of Proj_Y(A) by its base \
changes to the scheme points of Y; \
the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem invertibleMorphism_comp_π :
    d.invertibleMorphism ψ ≫ π
      = (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).ι ≫ f := by
  ext U a
  obtain ⟨ρ, hρ⟩ := a
  change π.app U (yonedaEquiv (d.invertiblePoint ψ ρ hρ).1) = f.app U ρ
  rw [← yonedaEquiv_comp, (d.invertiblePoint ψ ρ hρ).2, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- The factorisation through `U(ψ) ⊆ X` of a test scheme `W ⟶ X` lying in `U(ψ)`. -/
abbrev locusFactor {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W)) :
    yoneda.obj W ⟶ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).toFunctor :=
  yonedaEquiv.symm ⟨w, hw⟩

/-- The factorisation is a factorisation of `W ⟶ X` through `U(ψ) ⊆ X`. -/
theorem locusFactor_ι {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W)) :
    d.locusFactor ψ w hw ≫ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).ι
      = yoneda.map w :=
  (yonedaEquiv_symm_naturality_right W _ _).trans
    (yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map w).symm)

/-- The factorisation is natural in the test scheme. -/
theorem locusFactor_comp {W W' : BigFppfOver B S hS} (g : W' ⟶ W) (w : W ⟶ X)
    (hw : w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W))
    (hgw : g ≫ w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W')) :
    d.locusFactor ψ (g ≫ w) hgw = yoneda.map g ≫ d.locusFactor ψ w hw :=
  (yonedaEquiv_symm_naturality_left g
    (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).toFunctor ⟨w, hw⟩).symm

/-- On a test scheme of `U(ψ)`, `r_{ℒ,ψ}` is its value `invertiblePoint`. -/
theorem locusFactor_invertibleMorphism {W : BigFppfOver B S hS} (w : W ⟶ X)
    (hw : w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W)) :
    d.locusFactor ψ w hw ≫ d.invertibleMorphism ψ = (d.invertiblePoint ψ w hw).1 :=
  (yonedaEquiv_symm_naturality_right W (d.invertibleMorphism ψ) _).trans
    (yonedaEquiv.symm_apply_apply _)

/-- **Clause (2)(a) of [Stacks, Tag 0D2Z].**  For `k ≥ 1` and a scheme `w : W ⟶ X` such that
`ψ|_W : (f ∘ w)^*𝒜_k ⟶ (w^*ℒ)^{⊗ k}` is surjective, `w` factors through `U(ψ)`. -/
@[stacks 0D2Z "variant: clause (2)(a), for a presentation of Proj_Y(A) by its base changes to \
the scheme points of Y; the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem mem_subspaceOfOpens_of_epi {W : BigFppfOver B S hS} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))] :
    w ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op W) := by
  refine (mem_subspaceOfOpens_iff B S hS X _ w).2 fun y => ?_
  have h := preimage_coveringOpen_eq_top_of_epi ψ ((BigFppfOver.toScheme B S hS).map w) hk
  have hy : y ∈ (BigFppfOver.toScheme B S hS).map w ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
    rw [h]; trivial
  exact hy

/-- **The morphism `W ⟶ Proj_Y(𝒜)` that the construction of the relative Proj attaches to the
quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`**: the class of that quadruple in the functor `F` of
[Stacks, Tag 01NX] for `f^*𝒜`, represented by `Proj_X(f^*𝒜)` ([Stacks, Tag 01NZ]), read in `P`
through the identification `X ×_Y P = Proj_X(f^*𝒜)` of [Stacks, Tag 084B]. -/
def quadruplePoint {W : BigFppfOver B S hS} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))] :
    yoneda.obj W ⟶ Proj :=
  ((d.pointEquivProjOver X f w).symm
    ⟨(Scheme.topIso _).inv ≫ F.classifyingMorphism (d.algebra X f)
        (F.mk ((⊤ : ((BigFppfOver.toScheme B S hS).obj W).Opens).ι ≫
            (BigFppfOver.toScheme B S hS).map w ≫ 𝟙 _) (by exact_mod_cast hk)
          (haveI : Epi (((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).pullback
              (⊤ : ((BigFppfOver.toScheme B S hS).obj W).Opens).ι).app (k : ℤ)) :=
            Twisting.epi_pullbackApp _ _ _ inferInstance
           restrictQuadruple (ψ.pullback ((BigFppfOver.toScheme B S hS).map w)) ⊤ k)), by
      obtain ⟨h, e⟩ := clauseTwo_of_epi_pullback ψ ((BigFppfOver.toScheme B S hS).map w) hk
      rw [← e, Scheme.toIso_inv_ι_assoc, Category.assoc,
        GradedPowerMap.globalMorphism_comp_toBase, GradedPowerMap.toBase,
        IsOpenImmersion.lift_fac_assoc]
      exact Category.comp_id _⟩).1

/-- **Clause (2)(b) of [Stacks, Tag 0D2Z].**  For `k ≥ 1` and a scheme `w : W ⟶ X` such that
`ψ|_W` is surjective in degree `k`, the composite of the factorisation `W ⟶ U(ψ)` with
`r_{ℒ,ψ}` is the morphism `W ⟶ Proj_Y(𝒜)` which the construction of the relative Proj attaches to
the quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`. -/
@[stacks 0D2Z "variant: clause (2)(b), for a presentation of Proj_Y(A) by \
its base changes to the scheme points of Y; \
the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem locusFactor_invertibleMorphism_of_epi {W : BigFppfOver B S hS} (w : W ⟶ X) {k : ℕ}
    (hk : 0 < k) [Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))] :
    d.locusFactor ψ w (d.mem_subspaceOfOpens_of_epi ψ w hk) ≫ d.invertibleMorphism ψ
      = d.quadruplePoint ψ w hk := by
  rw [locusFactor_invertibleMorphism]
  obtain ⟨h, e⟩ := clauseTwo_of_epi_pullback ψ ((BigFppfOver.toScheme B S hS).map w) hk
  refine congrArg (fun z => ((d.pointEquivProjOver X f w).symm z).1) (Subtype.ext ?_)
  refine Eq.trans ?_ (congrArg (fun z => (Scheme.topIso _).inv ≫ z) e)
  rw [Scheme.toIso_inv_ι_assoc]
  rfl

/-- **`r_{ℒ,ψ}` is characterized by clause (2)**: a morphism `U(ψ) ⟶ Proj_Y(𝒜)` over `Y` which, on
every test scheme `W ⟶ X` over which `ψ` is surjective in some positive degree, is the morphism
attached to the quadruple of clause (2)(b), is `r_{ℒ,ψ}`. -/
@[stacks 0D2Z "variant: the characterization of r_{L,psi} by clause (2)(b), for a presentation \
of Proj_Y(A) by its base changes to the scheme points of Y; \
the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem eq_invertibleMorphism
    (Φ : (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).toFunctor ⟶ Proj)
    (hΦπ : Φ ≫ π = (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).ι ≫ f)
    (hΦ : ∀ {W : BigFppfOver B S hS} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
      [Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))],
      d.locusFactor ψ w (d.mem_subspaceOfOpens_of_epi ψ w hk) ≫ Φ = d.quadruplePoint ψ w hk) :
    Φ = d.invertibleMorphism ψ := by
  ext ⟨T⟩ ⟨ρ, hρ⟩
  have hover : (d.locusFactor ψ ρ hρ ≫ Φ) ≫ π = yoneda.map ρ ≫ f := by
    rw [Category.assoc, hΦπ, ← Category.assoc, locusFactor_ι]
  suffices key : (⟨d.locusFactor ψ ρ hρ ≫ Φ, hover⟩ :
      {u : yoneda.obj T ⟶ Proj // u ≫ π = yoneda.map ρ ≫ f}) = d.invertiblePoint ψ ρ hρ by
    have h1 := congrArg yonedaEquiv (congrArg Subtype.val key)
    rw [yonedaEquiv_comp] at h1
    exact (congrArg (Φ.app (op T)) (yonedaEquiv.apply_symm_apply _).symm).trans h1
  refine (d.pointEquivProjOver X f ρ).injective (Subtype.ext ?_)
  let O : PositiveSection (d.algebra X f) → ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    fun p => (BigFppfOver.toScheme B S hS).map ρ ⁻¹ᵁ (toGradedPowerMap ψ).openOfPositiveSection p
  have hO : IsOpenCover O := by
    change ⨆ p, O p = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    exact d.preimage_coveringOpen_eq_top_of_mem ψ ρ hρ
  refine Scheme.Cover.hom_ext
    (((BigFppfOver.toScheme B S hS).obj T).openCoverOfIsOpenCover O hO) _ _
    fun (p : PositiveSection (d.algebra X f)) => ?_
  change (O p).ι ≫ _ = (O p).ι ≫ _
  let Tp := openSiteObject B S hS T (O p)
  let ιp : Tp ⟶ T := openSiteObjectHom B S hS T (O p)
  have hιp : (BigFppfOver.toScheme B S hS).map ιp = (O p).ι := map_openSiteObjectHom B S hS T (O p)
  have hepi : Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map (ιp ≫ ρ))).app
      ((p.deg + 1 : ℕ) : ℤ)) := by
    refine epi_pullback_app_of_preimage_eq_top ψ _ p ?_
    rw [Functor.map_comp, hιp]
    exact top_unique fun y _ => y.2
  have hfac : d.locusFactor ψ (ιp ≫ ρ) (d.mem_subspaceOfOpens_of_epi ψ _ (Nat.succ_pos p.deg))
      = yoneda.map ιp ≫ d.locusFactor ψ ρ hρ :=
    d.locusFactor_comp ψ ιp ρ hρ _
  have e := (hΦ (ιp ≫ ρ) (Nat.succ_pos p.deg)).trans
    (d.locusFactor_invertibleMorphism_of_epi ψ (ιp ≫ ρ) (Nat.succ_pos p.deg)).symm
  rw [hfac, Category.assoc, Category.assoc, locusFactor_invertibleMorphism] at e
  have n1 := d.pointEquivProjOver_natural X f ρ ιp ⟨d.locusFactor ψ ρ hρ ≫ Φ, hover⟩
  have n2 := d.pointEquivProjOver_natural X f ρ ιp (d.invertiblePoint ψ ρ hρ)
  rw [← hιp]
  refine n1.symm.trans (Eq.trans ?_ n2)
  exact congrArg (fun u => (d.pointEquivProjOver X f (ιp ≫ ρ) u).1) (Subtype.ext e)

/-- A test scheme `t : T ⟶ X'` whose composite with `g' : X' ⟶ X` lies in `U(ψ)` lies in
`U(g'^*ψ) = g'^{-1}(U(ψ))`. -/
theorem preimage_coveringOpen_pullback_eq_top {X' T : BigFppfOver B S hS} (g' : X' ⟶ X)
    (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ
      (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).coveringOpen = ⊤ := by
  rw [coveringOpen_pullback, ← Scheme.Hom.comp_preimage, ← Functor.map_comp]
  exact d.preimage_coveringOpen_eq_top_of_mem ψ _ ht

/-- **Clause (3) of [Stacks, Tag 0D2Z], for the morphism, when `Y' ⟶ Y` is the point `f`.**
Consider the square with `Y' = X`, `g = f : Y' ⟶ Y`, a scheme `g' : X' ⟶ X` and `f' = g'`, so that
`𝒜' = f^*𝒜`, `ℒ' = g'^*ℒ` and `ψ' = g'^*ψ`.  Then `U(ψ') = g'^{-1}(U(ψ))`
(`…RelativeProjInvertibleMorphism.coveringOpen_pullback`), and `r_{ℒ',ψ'}` of
[Stacks, Tag 01O9] agrees with the base change of `r_{ℒ,ψ}` through
`Proj_X(f^*𝒜) = X ×_Y Proj_Y(𝒜)`: on every test scheme `t : T ⟶ X'` of `U(ψ')`, the point
`(f' ∘ t, r_{ℒ,ψ}(g' ∘ t))` of `X ×_Y Proj_Y(𝒜)` is `r_{ℒ',ψ'} ∘ t`. -/
@[stacks 0D2Z "variant: clause (3) for the morphism, for the squares in which \
Y' -> Y is the scheme point f : X -> Y; \
the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem invertibleMorphism_baseChange {X' T : BigFppfOver B S hS} (g' : X' ⟶ X) (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS X (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (d.pointEquivProjOver X f (t ≫ g')
        ⟨d.locusFactor ψ (t ≫ g') ht ≫ d.invertibleMorphism ψ, by
          rw [Category.assoc, invertibleMorphism_comp_π, ← Category.assoc, locusFactor_ι]⟩).1
      = liftOfPreimageEqTop _ _ (d.preimage_coveringOpen_pullback_eq_top ψ g' t ht)
        ≫ (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).globalMorphism
          (relativeProj (d.algebra X f)) := by
  refine (congrArg (fun z => (d.pointEquivProjOver X f (t ≫ g') z).1)
    (Subtype.ext (d.locusFactor_invertibleMorphism ψ _ ht))).trans ?_
  rw [pointEquivProjOver_invertiblePoint, ← coveringOpenPullback_globalMorphism,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι, locusLift_ι, Category.assoc,
    coveringOpenPullback_ι, liftOfPreimageEqTop_ι_assoc, Functor.map_comp]

/-- **`θ` and clause (1) of [Stacks, Tag 0D2Z], after base change to the scheme point
`f : X ⟶ Y`.**  The twists of `Proj_Y(𝒜)` are given at the scheme points of `Y`
([Stacks, Tag 084D]); at `f` they are the twists of `Proj_X(f^*𝒜)`, so
`r^*(⨁ 𝒪(d))` is the inverse image along `U(ψ) ⟶ Proj_X(f^*𝒜)` of those twists, and `θ` is the
map of [Stacks, Tag 01O9].  It preserves the unit and is multiplicative, and for every open `V`
of `X`, `d ≥ 0` and `a ∈ (f^*𝒜)_d(V)` it carries the inverse image of `ψ_P(a)` to the restriction
of `ψ(a)` to `U(ψ) ∩ V`: the square of clause (1). -/
@[stacks 0D2Z "variant: theta and clause (1) after base change to the scheme point \
f : X -> Y, for the opens of X; the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem invertibleTheta_clauseOne :
    SheafOfModules.sectionsMap (((toGradedPowerMap ψ).theta).app 0)
        (Stacks.Conormal.gradedPullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
          (twistDataOfGradedAlgebra (d.algebra X f)).algebra).one
      = (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn L
          (toGradedPowerMap ψ).coveringOpen).one
    ∧ (∀ (n e : ℕ) (U : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
        (x : ((Stacks.Conormal.gradedPullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
          (twistDataOfGradedAlgebra (d.algebra X f)).algebra).piece (n : ℤ)).val.obj (op U))
        (y : ((Stacks.Conormal.gradedPullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
          (twistDataOfGradedAlgebra (d.algebra X f)).algebra).piece (e : ℤ)).val.obj (op U)),
        (((toGradedPowerMap ψ).theta.app ((n : ℤ) + (e : ℤ))).val.app (op U)
            (((Stacks.Conormal.gradedPullback
              ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
              (twistDataOfGradedAlgebra (d.algebra X f)).algebra).mul n e).app (op U) x y))
          = ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn L
              (toGradedPowerMap ψ).coveringOpen).mul n e).app (op U)
              (((toGradedPowerMap ψ).theta.app n).val.app (op U) x)
              (((toGradedPowerMap ψ).theta.app e).val.app (op U) y))
    ∧ (∀ (V : ((BigFppfOver.toScheme B S hS).obj X).Opens) (n : ℕ)
        (a : Γ((d.algebra X f).piece (n : ℤ), V)),
        ((Stacks.AmpleProjectiveImmersion.tensorPowerModule _ L (n : ℤ)).restrict
            (toGradedPowerMap ψ).coveringOpen.ι).presheaf.map
            (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V)).op
            (((toGradedPowerMap ψ).theta.app n).val.app
              (op ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)) ⁻¹ᵁ
                ((relativeProj (d.algebra X f)).toBase ⁻¹ᵁ V)))
              (Stacks.RingedSpace.pullbackUnit
                ((toGradedPowerMap ψ).globalMorphism
                  (relativeProj (d.algebra X f))).toLRSHom.toShHom
                ((twistDataOfGradedAlgebra (d.algebra X f)).algebra.piece (n : ℤ))
                (op ((relativeProj (d.algebra X f)).toBase ⁻¹ᵁ V))
                (((twistDataOfGradedAlgebra (d.algebra X f)).ψ n).app V a)))
          = (Stacks.AmpleProjectiveImmersion.tensorPowerModule _ L (n : ℤ)).presheaf.map
              (homOfLE ((toGradedPowerMap ψ).coveringOpen.ι.image_preimage_le
                (𝟙 ((BigFppfOver.toScheme B S hS).obj X) ⁻¹ᵁ V))).op
              ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L n).hom.app
                (𝟙 ((BigFppfOver.toScheme B S hS).obj X) ⁻¹ᵁ V)
                ((toGradedPowerMap ψ).value n V a))) :=
  ⟨(toGradedPowerMap ψ).theta_map_one,
    fun n e U x y => (toGradedPowerMap ψ).theta.map_mul n e (op U) x y,
    fun V n a => (toGradedPowerMap ψ).theta_clauseOne V n a⟩

end AlgebraicGeometry.Space.RelativeProjPoints

end
