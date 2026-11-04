module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ModuleChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSquare

/-!
# Stacks 0D2Z for a morphism of algebraic spaces `f : X ⟶ Y`

[Stacks, Tag 0D2Z] fixes a scheme `S`, an algebraic space `Y` over `S`, a quasi-coherent graded
`𝒪_Y`-algebra `𝒜` with relative Proj `π : Proj_Y(𝒜) ⟶ Y`, a morphism of algebraic spaces
`f : X ⟶ Y`, an invertible `𝒪_X`-module `ℒ` and a homomorphism of graded `𝒪_X`-algebras
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`.  On the open subspace `U(ψ) ⊆ X` of [Stacks, Tag 0D2Y],

  `|U(ψ)| = ⋃_{d ≥ 1} {locus where f^*𝒜_d ⟶ ℒ^{⊗ d} is surjective}`,

it produces a canonical morphism of algebraic spaces `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` over `Y`,
characterized by clause (2) of the tag and compatible with base change, clause (3).

This file does this with `X` an **algebraic space**, on the relative Proj that the library
constructs (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`, Situation 0849,
Stacks 084A/084B).  The scheme case is
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleMorphismPoints.lean`; the space case is
reduced to it exactly as the source's hint reduces everything to Tag 01O9: a morphism of algebraic
spaces out of `U(ψ)` is a transformation of functors on the big fppf site, so it is given by its
values on the scheme points of `U(ψ)`, and at a scheme point `x : T ⟶ X` the value is the morphism
`r_{x^*ℒ, x^*ψ}` of Tag 01O9 for the restriction of `(ℒ, ψ)` to `T`.  The naturality of these
values is clause (3) of the scheme case for the square `T' ⟶ T`
(`…invertibleMorphism_baseChange_square`), together with the invariance of Tag 01O9 under an
isomorphism of the invertible module
(`…RelativeProjInvertibleMorphism.lift_globalMorphism_congrModule`).

## How `(ℒ, ψ)` on the algebraic space `X` is given

As everywhere in the relative Proj of an algebraic space in this library, sheaves on `X` are
presented by their restrictions to the scheme points of `X` together with the comparisons between
those restrictions: the graded algebra `𝒜` on `Y` enters through its restrictions `y^*𝒜` and the
comparisons `(y ∘ τ)^*𝒜 ≅ τ^*(y^*𝒜)` of the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`), and so `f^*𝒜` restricted to
a scheme point `x` of `X` is `(f ∘ x)^*𝒜`.  The pair `(ℒ, ψ)` is presented the same way
(`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`): for every scheme
point `x : T ⟶ X` the restriction `x^*ℒ`, an invertible module on `T`, and the restriction
`x^*ψ : (f ∘ x)^*𝒜 ⟶ ⨁ (x^*ℒ)^{⊗ d}`, a homomorphism of graded algebras; for every morphism
`τ : T' ⟶ T` of test schemes the identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`, under which
`(x ∘ τ)^*ψ` is the pullback `τ^*(x^*ψ)` read through the comparison of the restricted algebras.
This is the description of a quasi-coherent module on `X` by the quasi-coherent modules it induces
on the big site of `X`; no cocycle condition on the identifications is imposed, which only makes
the statements below more general.

## Main definitions

* `…InvertibleTwistingRestriction.locusOpen`: the open that `U(ψ)` cuts on a scheme point of `X`,
  the open `U(x^*ψ)` of Tag 01O8; an abbreviation of
  `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.coveringOpen`.
* `…InvertibleTwistingRestriction.locus`: **the open subspace `U(ψ) ⊆ X`**, cut out by its set of
  points (Stacks 03BZ, `AlgebraicGeometry.Space.openSubspaceOfPoints`).  It is irreducible, and
  reached through `…isOpenSubspace_locus`, `…mem_locus_iff` and `…preimage_locus`.
* `…InvertibleTwistingRestriction.invertibleMorphism`: **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`**.
* `…InvertibleTwistingRestriction.quadruplePoint`: the morphism `W ⟶ Proj_Y(𝒜)` that the
  construction of the relative Proj attaches to the quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`.

## Main results

* `…isOpenSubspace_locus`, `…mem_locus_iff`, `…preimage_locus`, `…mem_locusOpen_iff_exists_epi`:
  `U(ψ)` is an open subspace, a scheme point lies in it exactly when `U(x^*ψ)` is everything, its
  preimage along a scheme point is `U(x^*ψ)`, and its points are those near which some
  `ψ_d`, `d ≥ 1`, is surjective.
* `…invertibleMorphism_comp_π`: `r_{ℒ,ψ}` lies over `Y`.
* `…mem_locus_of_epi`, `…factor_invertibleMorphism_of_epi`: **clause (2)(a) and (2)(b)**.
* `…invertibleMorphism_baseChange_square`: **clause (3)** for the open and the morphism, for an
  arbitrary commutative square with `X'`, `Y'` schemes.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

universe u m

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace AlgebraicGeometry.Space.GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Z : BigFppfOver B S hS} {f : yoneda.obj Z ⟶ X}
    {L : ((BigFppfOver.toScheme B S hS).obj Z).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj Z))
      (situationAlgebra ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) 1 L)
    {X' Y' : BigFppfOver B S hS} (g : yoneda.obj Y' ⟶ X) (f' : X' ⟶ Y') (g' : X' ⟶ Z)
    (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f)

/-- **A component of the pullback `ψ'` of `ψ` to a commutative square is surjective exactly when
the same component of `(g')^*ψ` is**: the comparisons through which `ψ'` is read are
isomorphisms. -/
theorem epi_squareTwisting_app_iff (i : ℤ) :
    Epi ((ρ.squareTwisting hc hX ψ g f' g' hsq).app i) ↔
      Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map g')).app i) := by
  unfold squareTwisting squareTwistingAtPoint squarePullbackDown
  refine (Twisting.epi_congrBase_app_iff _ _ i).trans ?_
  refine (Twisting.epi_baseChangeUp_app_iff _ _ _ _ _ i).trans ?_
  refine (Twisting.epi_algebraTransport_app_iff _ (isIso_unitalHomInverse_app _ _) _ i).trans ?_
  refine (Twisting.epi_algebraTransport_app_iff _ (ρ.isIso_restrict_app _ _ _ _) _ i).trans ?_
  refine (Twisting.epi_baseChangeDown_app_iff _ _ _ i).trans ?_
  exact Twisting.epi_congrBase_app_iff _ _ i

end AlgebraicGeometry.Space.GradedAlgebraRestriction

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} (f : X ⟶ s.space.1)

/-- The square `T' = T' ⟶ T` over the identity: `𝟙 ≫ ((x ∘ τ) ≫ f) = τ ≫ (x ≫ f)`. -/
theorem yoneda_map_id_comp_assoc {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) :
    yoneda.map (𝟙 T') ≫ ((yoneda.map τ ≫ x) ≫ f) = yoneda.map τ ≫ (x ≫ f) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]

/-- **An invertible module `ℒ` on `X` and a homomorphism of graded algebras
`ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}`, given by their restrictions to the scheme points of `X`.**

For a scheme point `x : T ⟶ X`: the restriction `x^*ℒ` (`line`), invertible, and the
restriction `x^*ψ : (f ∘ x)^*𝒜 ⟶ ⨁_d (x^*ℒ)^{⊗ d}` (`twisting`), a homomorphism of graded
algebras out of the restriction of `𝒜` to the scheme point `f ∘ x` of `Y`; for a morphism
`τ : T' ⟶ T` of test schemes, the identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` (`lineIso`), under which
`(x ∘ τ)^*ψ` is the pullback of `x^*ψ` along `τ` (`twisting_map`), read through the comparison
`(f ∘ x ∘ τ)^*𝒜 ≅ τ^*((f ∘ x)^*𝒜)` of the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting` for the square with
`f' = 𝟙`). -/
structure InvertibleTwistingRestriction where
  /-- The restriction `x^*ℒ` of `ℒ` to a scheme point `x : T ⟶ X`. -/
  line (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X) :
    ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Modules
  /-- `ℒ` is invertible. -/
  [isInvertible (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X) :
    Stacks.Ample.IsInvertibleModule _ (line T x)]
  /-- The restriction `x^*ψ : (f ∘ x)^*𝒜 ⟶ ⨁_d (x^*ℒ)^{⊗ d}` of `ψ`. -/
  twisting (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X) :
    Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
      (situationAlgebra (s.relativeProjPoints.algebra T (x ≫ f))) 1 (line T x)
  /-- The identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`. -/
  lineIso {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) :
    (pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ))).obj
      (line T x) ≅ line T' (yoneda.map τ ≫ x)
  /-- `(x ∘ τ)^*ψ` is the pullback of `x^*ψ` along `τ`. -/
  twisting_map {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) :
    twisting T' (yoneda.map τ ≫ x) =
      (Twisting.congrBase (CategoryTheory.Functor.map_id _ T')
        (s.quadrupleRestriction.squareTwisting s.shrink.contains_relativeProj_pointAlgebra
          s.shrink.space.property.isSheaf (twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
          (yoneda_map_id_comp_assoc s f τ x))).congrModule
        (lineIso τ x)

namespace InvertibleTwistingRestriction

attribute [instance] InvertibleTwistingRestriction.isInvertible

variable {s f} (R : s.InvertibleTwistingRestriction f)

/-! ### The open subspace `U(ψ)` -/

/-- **The open that `U(ψ)` cuts on a scheme point `x : T ⟶ X`**: the open `U(x^*ψ)` of
[Stacks, Tag 01O8] for the restriction of `ψ` to `T`, that is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.coveringOpen` of the
restriction, of which this is an abbreviation. -/
abbrev locusOpen (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X) :
    ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens :=
  (toGradedPowerMap (R.twisting T x)).coveringOpen

/-- **Formation of `U(ψ)` commutes with pullback** ([Stacks, Tag 0D2Y]): the open cut on the
scheme point `x ∘ τ` is the preimage along `τ` of the open cut on `x`. -/
theorem locusOpen_map {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) :
    R.locusOpen T' (yoneda.map τ ≫ x) =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map τ ⁻¹ᵁ R.locusOpen T x :=
  (congrArg (fun χ => (toGradedPowerMap χ).coveringOpen) (R.twisting_map τ x)).trans
    ((coveringOpen_congrModule _ _).trans ((coveringOpen_congrBase _ _).trans
      (s.quadrupleRestriction.coveringOpen_squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra
        s.shrink.space.property.isSheaf (R.twisting T x) _ (𝟙 T') τ _)))

/-- **`|U(ψ)|` is the union of the loci where some `ψ_d`, `d ≥ 1`, is surjective**: on a scheme
point `x : T ⟶ X`, a point of `T` lies in `U(ψ)` exactly when it has an open neighbourhood over
which a positive-degree component of `x^*ψ` is surjective. -/
theorem mem_locusOpen_iff_exists_epi (T : BigFppfOver s.site s.base s.containsBase)
    (x : yoneda.obj T ⟶ X) (y : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T) :
    y ∈ R.locusOpen T x ↔
      ∃ (V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) (k : ℕ),
        0 < k ∧ y ∈ V ∧ Epi (((R.twisting T x).pullback V.ι).app (k : ℤ)) :=
  mem_coveringOpen_iff_exists_epi (R.twisting T x) y

/-- An open of the spectrum of a field containing a point is everything. -/
theorem eq_top_of_mem_fieldPoint
    (p : FieldValuedPoint s.site s.base s.containsBase X)
    (O : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj p.siteObject).Opens)
    {y : (BigFppfOver.toScheme s.site s.base s.containsBase).obj p.siteObject} (hy : y ∈ O) :
    O = ⊤ := by
  have : Subsingleton ((BigFppfOver.toScheme s.site s.base s.containsBase).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  exact top_unique fun z _ => by rwa [Subsingleton.elim z y]

/-- A field-valued point of `X` lies in `U(ψ)`: the open that `U(ψ)` cuts on it is everything. -/
def FieldPointMem (p : FieldValuedPoint s.site s.base s.containsBase X) : Prop :=
  R.locusOpen p.siteObject (yonedaEquiv.symm p.value) = ⊤

/-- The preimage of an open under a morphism out of the spectrum of a field is everything exactly
when the image of the closed point lies in the open. -/
private theorem preimage_eq_top_iff_closedPoint_mem
    (p : FieldValuedPoint s.site s.base s.containsBase X) {Z : Scheme.{u}}
    (φ : (BigFppfOver.toScheme s.site s.base s.containsBase).obj p.siteObject ⟶ Z) (O : Z.Opens) :
    φ ⁻¹ᵁ O = ⊤ ↔ φ (IsLocalRing.closedPoint p.carrier) ∈ O :=
  ⟨fun h => show _ ∈ φ ⁻¹ᵁ O by rw [h]; trivial, fun h => eq_top_of_mem_fieldPoint p _ h⟩

/-- Membership in `U(ψ)` passes along a domination of field-valued points. -/
theorem fieldPointMem_iff_of_dominates {p r : FieldValuedPoint s.site s.base s.containsBase X}
    (h : FieldValuedPoint.Dominates s.site s.base s.containsBase X r p) :
    R.FieldPointMem r ↔ R.FieldPointMem p := by
  obtain ⟨φ, hφ⟩ := h
  have hr : (yonedaEquiv.symm r.value : yoneda.obj r.siteObject ⟶ X) =
      yoneda.map φ ≫ yonedaEquiv.symm p.value := by
    rw [← hφ, yonedaEquiv_symm_map]
    rfl
  unfold FieldPointMem
  rw [hr, R.locusOpen_map]
  exact (preimage_eq_top_iff_closedPoint_mem r _ _).trans
    ⟨eq_top_of_mem_fieldPoint p _, fun h => by simp [h]⟩

/-- Membership in `U(ψ)` depends only on the point of `X` a field-valued point represents. -/
theorem fieldPointMem_iff_of_class_eq {p q : FieldValuedPoint s.site s.base s.containsBase X}
    (h : p.class s.site s.base s.containsBase X = q.class s.site s.base s.containsBase X) :
    R.FieldPointMem p ↔ R.FieldPointMem q := by
  obtain ⟨r, hrp, hrq⟩ :=
    (FieldValuedPoint.class_eq_class_iff s.site s.base s.containsBase X p q).1 h
  exact (R.fieldPointMem_iff_of_dominates hrp).symm.trans (R.fieldPointMem_iff_of_dominates hrq)

/-- **The set `|U(ψ)|` of points of `X`.** -/
def locusPoints : Set (points s.site s.base s.containsBase X) :=
  {w | ∃ p : FieldValuedPoint s.site s.base s.containsBase X,
    p.class s.site s.base s.containsBase X = w ∧ R.FieldPointMem p}

/-- The class of a field-valued point `p` of `X` lies in `|U(ψ)|` exactly when `p` lies in
`U(ψ)`. -/
theorem class_mem_locusPoints_iff (p : FieldValuedPoint s.site s.base s.containsBase X) :
    p.class s.site s.base s.containsBase X ∈ R.locusPoints ↔ R.FieldPointMem p :=
  ⟨fun ⟨_, hq, hm⟩ => (R.fieldPointMem_iff_of_class_eq hq).1 hm, fun h => ⟨p, rfl, h⟩⟩

/-- A field-valued point of a scheme point `q : A ⟶ X` lies in `U(ψ)` exactly when its scheme
point lies in the open `U(ψ)` cuts on `A`. -/
theorem fieldPointMem_map_iff {A : BigFppfOver s.site s.base s.containsBase}
    (q : yoneda.obj A ⟶ X) (p : FieldValuedPoint s.site s.base s.containsBase (yoneda.obj A)) :
    R.FieldPointMem (FieldValuedPoint.map s.site s.base s.containsBase _ q p) ↔
      schemePoint s.site s.base s.containsBase A p ∈ R.locusOpen A q := by
  have h : (yonedaEquiv.symm (q.app (op p.siteObject) p.value) :
      yoneda.obj p.siteObject ⟶ X) = yoneda.map p.value ≫ q :=
    yonedaEquiv.symm_apply_eq.2 (by rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map])
  show R.locusOpen p.siteObject (yonedaEquiv.symm (q.app (op p.siteObject) p.value)) = ⊤ ↔ _
  rw [h, R.locusOpen_map]
  exact preimage_eq_top_iff_closedPoint_mem p _ _

/-- **`|U(ψ)|` is open.** -/
theorem isOpen_locusPoints :
    @IsOpen _ (pointTopology s.site s.base s.containsBase X) R.locusPoints := by
  rw [isOpen_pointTopology_iff]
  intro A q
  refine ⟨R.locusOpen A q, (R.locusOpen A q).isOpen, fun p => ?_⟩
  rw [Set.mem_preimage, pointsMap_class, class_mem_locusPoints_iff, fieldPointMem_map_iff]
  rfl

/-- **The open subspace `U(ψ) ⊆ X` of [Stacks, Tag 0D2Y]**: the subfunctor of `X` cut out by the
open set of points `|U(ψ)|` (Stacks 03BZ). -/
def locus : Subfunctor X :=
  openSubspaceOfPoints s.site s.base s.containsBase X R.locusPoints

/-- **`U(ψ)` is an open subspace of the algebraic space `X`.**  Its points are those near which
some `f^*𝒜_d ⟶ ℒ^{⊗ d}`, `d ≥ 1`, is surjective (`…mem_locusOpen_iff_exists_epi`), and its
preimage along a scheme point `x` is `U(x^*ψ)` (`…preimage_locus`). -/
@[stacks 0D2Z "the source U(psi) of r_{L,psi}, for an algebraic space X, is an open subspace of \
X"]
theorem isOpenSubspace_locus (hX : IsAlgebraicSpace s.site s.base s.containsBase X) :
    IsOpenSubspace s.site s.base s.containsBase R.locus :=
  isOpenSubspace_openSubspaceOfPoints s.site s.base s.containsBase hX _ R.isOpen_locusPoints

/-- **A scheme point `x : T ⟶ X` factors through `U(ψ)` exactly when the open `U(x^*ψ)` that
`U(ψ)` cuts on `T` is everything.** -/
theorem mem_locus_iff {T : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj T ⟶ X) :
    yonedaEquiv x ∈ R.locus.obj (op T) ↔ R.locusOpen T x = ⊤ := by
  rw [locus, mem_openSubspaceOfPoints_iff, Equiv.symm_apply_apply]
  constructor
  · intro h
    refine top_unique fun y _ => ?_
    obtain ⟨p, rfl⟩ := exists_fieldValuedPoint_schemePoint_eq s.site s.base s.containsBase T y
    have hp := h ⟨p.class s.site s.base s.containsBase _, rfl⟩
    rwa [pointsMap_class, class_mem_locusPoints_iff, fieldPointMem_map_iff] at hp
  · rintro h _ ⟨w, rfl⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep w
    show FieldValuedPoint.class _ _ _ _ _ ∈ R.locusPoints
    rw [class_mem_locusPoints_iff, fieldPointMem_map_iff, h]
    trivial

/-- Membership of a section of `X` in `U(ψ)`, read on the corresponding scheme point. -/
theorem locusOpen_eq_top_of_mem {T : BigFppfOver s.site s.base s.containsBase}
    {a : X.obj (op T)} (ha : a ∈ R.locus.obj (op T)) :
    R.locusOpen T (yonedaEquiv.symm a) = ⊤ :=
  (R.mem_locus_iff _).1 (by rwa [Equiv.apply_symm_apply])

/-- **The preimage of `U(ψ)` along a scheme point `x : T ⟶ X` is the open subscheme `U(x^*ψ)` of
`T`**: `U(ψ) ×_X T = U(x^*ψ)`. -/
theorem preimage_locus (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X) :
    R.locus.preimage x = subspaceOfOpens s.site s.base s.containsBase T (R.locusOpen T x) := by
  rw [locus, preimage_openSubspaceOfPoints', subspaceOfOpens]
  congr 1
  ext w
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  show FieldValuedPoint.class _ _ _ _ _ ∈ R.locusPoints ↔ schemePoint _ _ _ T p ∈ R.locusOpen T x
  rw [class_mem_locusPoints_iff, fieldPointMem_map_iff]

attribute [irreducible] locus

/-! ### The morphism `r_{ℒ,ψ}` -/

/-- A test scheme `τ : T' ⟶ T` lies in `U(x^*ψ)` as soon as the open `U(ψ)` cuts on `x ∘ τ` is
everything. -/
theorem mem_subspaceOfOpens_of_locusOpen {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X) (h : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤) :
    τ ∈ (subspaceOfOpens s.site s.base s.containsBase T
      (toGradedPowerMap (R.twisting T x)).coveringOpen).obj (op T') := by
  refine (mem_subspaceOfOpens_iff s.site s.base s.containsBase T _ τ).2 fun y => ?_
  have hy : y ∈ R.locusOpen T' (yoneda.map τ ≫ x) := by rw [h]; trivial
  rw [R.locusOpen_map] at hy
  exact hy

omit R in
/-- If `O` is the top open of `Z`, then its preimage under `q : Y ⟶ Z` is the top open of `Y`. -/
theorem preimage_eq_top_of_eq_top {Y Z : Scheme.{u}} (q : Y ⟶ Z) {O : Z.Opens} (h : O = ⊤) :
    q ⁻¹ᵁ O = ⊤ :=
  top_unique fun y _ => by
    have hy : q y ∈ O := by rw [h]; trivial
    exact hy

/-- The open that `U(ψ)` cuts on `T` along `𝟙 T ≫ x` is the one it cuts along `x`. -/
theorem locusOpen_id_comp {T : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj T ⟶ X) :
    R.locusOpen T (yoneda.map (𝟙 T) ≫ x) = R.locusOpen T x := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The value of `r_{ℒ,ψ}` at a scheme point `x : T ⟶ U(ψ)`**: the `T`-point of `Proj_Y(𝒜)`
over `f ∘ x` attached, through `T ×_Y Proj_Y(𝒜) = Proj_T((f ∘ x)^*𝒜)` (Stacks 084B), to the
morphism `T = U(x^*ψ) ⟶ Proj_T((f ∘ x)^*𝒜)` of [Stacks, Tag 01O9] for the restriction `x^*ψ`. -/
def point {T : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj T ⟶ X)
    (hx : R.locusOpen T x = ⊤) :
    {u : yoneda.obj T ⟶ s.relativeProjFunctor //
      u ≫ s.relativeProjπ = yoneda.map (𝟙 T) ≫ (x ≫ f)} :=
  s.relativeProjPoints.invertiblePoint (R.twisting T x) (𝟙 T)
    (R.mem_subspaceOfOpens_of_locusOpen (𝟙 T) x ((R.locusOpen_id_comp x).trans hx))

/-- The value of `r_{ℒ,ψ}` at a scheme point depends only on the point, not on the proof that
it lies in `U(ψ)`. -/
theorem point_congr {T : BigFppfOver s.site s.base s.containsBase} {x x' : yoneda.obj T ⟶ X}
    (h : x = x') (hx : R.locusOpen T x = ⊤) (hx' : R.locusOpen T x' = ⊤) :
    (R.point x hx).1 = (R.point x' hx').1 := by
  subst h
  rfl

omit R in
/-- The point of `Proj_Y(𝒜)` attached to `ψ` along `w : T' ⟶ T` depends only on `w`, not on
the proof that `w` lies in `U(ψ)`. -/
theorem invertiblePoint_congr {T T' : BigFppfOver s.site s.base s.containsBase}
    {g : yoneda.obj T ⟶ s.space.1}
    {L : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
      (situationAlgebra (s.relativeProjPoints.algebra T g)) 1 L) {w w' : T' ⟶ T} (h : w = w')
    (hw : w ∈ (subspaceOfOpens s.site s.base s.containsBase T
      (toGradedPowerMap ψ).coveringOpen).obj (op T'))
    (hw' : w' ∈ (subspaceOfOpens s.site s.base s.containsBase T
      (toGradedPowerMap ψ).coveringOpen).obj (op T')) :
    (s.relativeProjPoints.invertiblePoint ψ w hw).1 =
      (s.relativeProjPoints.invertiblePoint ψ w' hw').1 := by
  subst h
  rfl

omit R in
/-- The morphism `T ⟶ Proj_Y(𝒜)` given by `pointEquivProjOver` depends only on `r` and `u`,
not on the proof that `u` lies over `r ≫ z`. -/
theorem pointEquivProjOver_val_congr {Z T : BigFppfOver s.site s.base s.containsBase}
    (z : yoneda.obj Z ⟶ s.space.1) {r r' : T ⟶ Z} (h : r = r')
    {u u' : yoneda.obj T ⟶ s.relativeProjFunctor} (hu : u = u')
    (p : u ≫ s.relativeProjπ = yoneda.map r ≫ z) (p' : u' ≫ s.relativeProjπ = yoneda.map r' ≫ z) :
    (s.relativeProjPoints.pointEquivProjOver Z z r ⟨u, p⟩).1 =
      (s.relativeProjPoints.pointEquivProjOver Z z r' ⟨u', p'⟩).1 := by
  subst h
  subst hu
  rfl

/-- **The value of `r_{ℒ,ψ}` at `x ∘ τ` is the value at `τ` of the morphism of Tag 01O9 for
`x^*ψ`**, for any scheme point `x : T ⟶ X` and any `τ : T' ⟶ T` with `x ∘ τ` in `U(ψ)`.  This is
clause (3) of the scheme case for the square `T' ⟶ T` over `f ∘ x`, read through the
identifications of the restriction datum. -/
theorem point_map {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) (h : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤) :
    (R.point (yoneda.map τ ≫ x) h).1 =
      (s.relativeProjPoints.invertiblePoint (R.twisting T x) τ
        (R.mem_subspaceOfOpens_of_locusOpen τ x h)).1 := by
  have hτ := R.mem_subspaceOfOpens_of_locusOpen τ x h
  have ht : 𝟙 T' ≫ τ ∈ (subspaceOfOpens s.site s.base s.containsBase T
      (toGradedPowerMap (R.twisting T x)).coveringOpen).obj (op T') := by
    rw [Category.id_comp]; exact hτ
  have key := (s.invertibleMorphism_baseChange_square (R.twisting T x)
    ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x)).2 (𝟙 T') ht
  have hu : s.relativeProjPoints.locusFactor (R.twisting T x) (𝟙 T' ≫ τ) ht ≫
        s.relativeProjPoints.invertibleMorphism (R.twisting T x) =
      (s.relativeProjPoints.invertiblePoint (R.twisting T x) τ hτ).1 :=
    (s.relativeProjPoints.locusFactor_invertibleMorphism (R.twisting T x) _ ht).trans
      (invertiblePoint_congr (R.twisting T x) (Category.id_comp τ) ht hτ)
  have hover : (s.relativeProjPoints.invertiblePoint (R.twisting T x) τ hτ).1 ≫
      s.relativeProjπ = yoneda.map (𝟙 T') ≫ ((yoneda.map τ ≫ x) ≫ f) := by
    rw [(s.relativeProjPoints.invertiblePoint (R.twisting T x) τ hτ).2,
      yoneda_map_id_comp_assoc s f τ x]
  have e1 : (s.relativeProjPoints.pointEquivProjOver T' ((yoneda.map τ ≫ x) ≫ f) (𝟙 T')
      ⟨(s.relativeProjPoints.invertiblePoint (R.twisting T x) τ hτ).1, hover⟩).1 =
        liftOfPreimageEqTop _ ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T'))
            (s.quadrupleRestriction.preimage_coveringOpen_squareTwisting_eq_top
              s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
              (R.twisting T x) _ (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x) (𝟙 T') ht) ≫
          (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
            s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting
              T x)
              ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x))).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))) :=
    (pointEquivProjOver_val_congr _ (Category.comp_id (𝟙 T')).symm hu.symm _ _).trans key
  have e2 := s.relativeProjPoints.pointEquivProjOver_invertiblePoint
    (R.twisting T' (yoneda.map τ ≫ x)) (𝟙 T')
    (R.mem_subspaceOfOpens_of_locusOpen (𝟙 T') (yoneda.map τ ≫ x)
      ((R.locusOpen_id_comp _).trans h))
  have hc1 :=
    (congrArg (fun χ => (toGradedPowerMap χ).coveringOpen) (R.twisting_map τ x)).symm.trans h
  have hc2 := (coveringOpen_congrModule _ _).symm.trans hc1
  have hc3 := (coveringOpen_congrBase _ _).symm.trans hc2
  have e3 := (lift_globalMorphism_congr (R.twisting_map τ x)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T'))
      (preimage_eq_top_of_eq_top _ h)).symm.trans
    ((lift_globalMorphism_congrModule _ (R.lineIso τ x)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T'))
      (preimage_eq_top_of_eq_top _ hc2)).trans
      (lift_globalMorphism_congrBase _ _
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T'))
      (preimage_eq_top_of_eq_top _ hc3)))
  have := (s.relativeProjPoints.pointEquivProjOver T' ((yoneda.map τ ≫ x) ≫ f) (𝟙 T')).injective
    (Subtype.ext (e2.trans (e3.trans e1.symm)))
  exact congrArg Subtype.val this

/-- The values of `r_{ℒ,ψ}` are natural in the test scheme. -/
theorem map_comp_point {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) (hx : R.locusOpen T x = ⊤) (x' : yoneda.obj T' ⟶ X)
    (hx' : R.locusOpen T' x' = ⊤) (hxx' : x' = yoneda.map τ ≫ x) :
    yoneda.map τ ≫ (R.point x hx).1 = (R.point x' hx').1 := by
  subst hxx'
  refine ((s.relativeProjPoints.map_comp_invertiblePoint (R.twisting T x) τ (𝟙 T) _).trans
    (invertiblePoint_congr (R.twisting T x) (Category.comp_id τ) _
      (R.mem_subspaceOfOpens_of_locusOpen τ x hx'))).trans (R.point_map τ x hx').symm

/-- **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`, the morphism of [Stacks, Tag 0D2Z], for a morphism of
algebraic spaces `f : X ⟶ Y`**, as the transformation of functors on the big fppf site that the
source's proof builds: its value on a scheme point `x : T ⟶ U(ψ)` is the morphism of
[Stacks, Tag 01O9] for the restriction `x^*ψ` (`point`), read in `Proj_Y(𝒜)` through
`T ×_Y Proj_Y(𝒜) = Proj_T((f ∘ x)^*𝒜)`; its naturality is clause (3) of the scheme case. -/
@[stacks 0D2Z "the canonical morphism r_{L,psi} : U(psi) -> Proj_Y(A) for a morphism of \
algebraic spaces f : X -> Y, an invertible O_X-module L and a homomorphism of graded algebras \
psi : f^*A -> (+)_d L^d, given on X by their restrictions to the scheme points of X; U(psi) is \
the open subspace of the algebraic space X of Tag 0D2Y and Proj_Y(A) the relative Proj of \
Tag 084A/084B"]
def invertibleMorphism : R.locus.toFunctor ⟶ s.relativeProjFunctor where
  app U := ↾fun a => yonedaEquiv (R.point (yonedaEquiv.symm a.1) (R.locusOpen_eq_top_of_mem a.2)).1
  naturality U V h := by
    ext a
    refine Eq.trans ?_ (yonedaEquiv_naturality'
      (R.point (yonedaEquiv.symm a.1) (R.locusOpen_eq_top_of_mem a.2)).1 h).symm
    exact congrArg yonedaEquiv (R.map_comp_point h.unop _ _ _ _
      (yonedaEquiv_symm_map h a.1)).symm

/-- **`r_{ℒ,ψ}` is a morphism over `Y`**: `π ∘ r_{ℒ,ψ}` is the restriction of `f` to `U(ψ)`. -/
@[stacks 0D2Z "r_{L,psi} is a morphism of algebraic spaces over Y, for a morphism of algebraic \
spaces f : X -> Y"]
theorem invertibleMorphism_comp_π :
    R.invertibleMorphism ≫ s.relativeProjπ = R.locus.ι ≫ f := by
  ext U a
  show s.relativeProjπ.app U
    (yonedaEquiv (R.point (yonedaEquiv.symm a.1) (R.locusOpen_eq_top_of_mem a.2)).1) = f.app U a.1
  rw [← yonedaEquiv_comp, (R.point _ _).2, CategoryTheory.Functor.map_id, Category.id_comp,
    yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The factorisation through `U(ψ) ⊆ X` of a scheme point `w : W ⟶ X` lying in `U(ψ)`. -/
def factor {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X)
    (hw : yonedaEquiv w ∈ R.locus.obj (op W)) : yoneda.obj W ⟶ R.locus.toFunctor :=
  yonedaEquiv.symm ⟨yonedaEquiv w, hw⟩

/-- The factorisation is a factorisation of `w` through the inclusion `U(ψ) ⊆ X`. -/
theorem factor_ι {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X)
    (hw : yonedaEquiv w ∈ R.locus.obj (op W)) : R.factor w hw ≫ R.locus.ι = w :=
  (yonedaEquiv_symm_naturality_right W R.locus.ι
    (⟨yonedaEquiv w, hw⟩ : R.locus.toFunctor.obj (op W))).trans (yonedaEquiv.symm_apply_apply w)

/-- On a scheme point of `U(ψ)`, `r_{ℒ,ψ}` is its value `point`. -/
theorem factor_invertibleMorphism {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) (hw : yonedaEquiv w ∈ R.locus.obj (op W)) :
    R.factor w hw ≫ R.invertibleMorphism = (R.point w ((R.mem_locus_iff w).1 hw)).1 :=
  (yonedaEquiv_symm_naturality_right W R.invertibleMorphism
    (⟨yonedaEquiv w, hw⟩ : R.locus.toFunctor.obj (op W))).trans
    ((yonedaEquiv.symm_apply_apply _).trans (R.point_congr (Equiv.symm_apply_apply _ _) _ _))

/-- **Clause (2)(a) of [Stacks, Tag 0D2Z].**  For `k ≥ 1` and a scheme `w : W ⟶ X` such that
`ψ|_W : (f ∘ w)^*𝒜_k ⟶ (w^*ℒ)^{⊗ k}` is surjective, `w` factors through `U(ψ)`. -/
@[stacks 0D2Z "clause (2)(a), for a morphism of algebraic spaces f : X -> Y: a scheme W -> X \
over which psi is surjective in some degree d >= 1 factors through the open subspace U(psi) of \
the algebraic space X"]
theorem mem_locus_of_epi {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X)
    {k : ℕ} (hk : 0 < k) [hw : Epi ((R.twisting W w).app (k : ℤ))] :
    yonedaEquiv w ∈ R.locus.obj (op W) := by
  have : Epi (((R.twisting W w).pullback (𝟙 _)).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ hw
  exact (R.mem_locus_iff w).2 (preimage_coveringOpen_eq_top_of_epi (R.twisting W w) (𝟙 _) hk)

/-- **The morphism `W ⟶ Proj_Y(𝒜)` that the construction of the relative Proj attaches to the
quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`**, for a scheme `w : W ⟶ X` over which `ψ` is surjective
in degree `k ≥ 1`: the class of that quadruple in the functor of [Stacks, Tag 01NX] for
`(f ∘ w)^*𝒜`, read in `Proj_Y(𝒜)` through `W ×_Y Proj_Y(𝒜) = Proj_W((f ∘ w)^*𝒜)`. -/
def quadruplePoint {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X)
    {k : ℕ} (hk : 0 < k) [hw : Epi ((R.twisting W w).app (k : ℤ))] :
    yoneda.obj W ⟶ s.relativeProjFunctor :=
  haveI : Epi (((R.twisting W w).pullback
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 W))).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ hw
  s.relativeProjPoints.quadruplePoint (R.twisting W w) (𝟙 W) hk

/-- **Clause (2)(b) of [Stacks, Tag 0D2Z].**  For `k ≥ 1` and a scheme `w : W ⟶ X` such that
`ψ|_W` is surjective in degree `k`, the composite of the factorisation `W ⟶ U(ψ)` with
`r_{ℒ,ψ}` is the morphism `W ⟶ Proj_Y(𝒜)` which the construction of the relative Proj attaches to
the quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`. -/
@[stacks 0D2Z "clause (2)(b), for a morphism of algebraic spaces f : X -> Y: for a scheme \
W -> X over which psi is surjective in degree k >= 1, W -> U(psi) -> Proj_Y(A) is the morphism \
the construction of the relative Proj attaches to the quadruple (k, W -> Y, L^k|_W, psi|_W)"]
theorem factor_invertibleMorphism_of_epi {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) {k : ℕ} (hk : 0 < k) [hw : Epi ((R.twisting W w).app (k : ℤ))] :
    R.factor w (R.mem_locus_of_epi w hk) ≫ R.invertibleMorphism = R.quadruplePoint w hk := by
  have : Epi (((R.twisting W w).pullback
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 W))).app (k : ℤ)) :=
    Twisting.epi_pullbackApp _ _ _ hw
  rw [factor_invertibleMorphism, point, ← s.relativeProjPoints.locusFactor_invertibleMorphism]
  exact s.relativeProjPoints.locusFactor_invertibleMorphism_of_epi (R.twisting W w) (𝟙 W) hk

/-- **A component of `(x ∘ τ)^*ψ` is surjective exactly when the same component of the
pullback `τ^*(x^*ψ)` is.** -/
theorem epi_twisting_map_iff {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X) (i : ℤ) :
    Epi ((R.twisting T' (yoneda.map τ ≫ x)).app i) ↔
      Epi (((R.twisting T x).pullback
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).app i) := by
  rw [R.twisting_map τ x]
  refine (Twisting.epi_congrModule_app_iff _ _ i).trans ?_
  refine (Twisting.epi_congrBase_app_iff _ _ i).trans ?_
  exact s.quadrupleRestriction.epi_squareTwisting_app_iff
    s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T x) _
    (𝟙 T') τ _ i

/-- The factorisation through `U(ψ)` is natural in the scheme point. -/
theorem factor_comp {W W' : BigFppfOver s.site s.base s.containsBase} (g : W' ⟶ W)
    (w : yoneda.obj W ⟶ X) (hw : yonedaEquiv w ∈ R.locus.obj (op W))
    (hgw : yonedaEquiv (yoneda.map g ≫ w) ∈ R.locus.obj (op W')) :
    R.factor (yoneda.map g ≫ w) hgw = yoneda.map g ≫ R.factor w hw := by
  refine Eq.trans ?_ (yonedaEquiv_symm_naturality_left g R.locus.toFunctor
    (⟨yonedaEquiv w, hw⟩ : R.locus.toFunctor.obj (op W))).symm
  exact congrArg yonedaEquiv.symm (Subtype.ext (yonedaEquiv_naturality' w g.op).symm)

/-- **`r_{ℒ,ψ}` is characterized by clause (2)**: a morphism `U(ψ) ⟶ Proj_Y(𝒜)` over `Y` which,
on every scheme `W ⟶ X` over which `ψ` is surjective in some positive degree, is the morphism
attached to the quadruple of clause (2)(b), is `r_{ℒ,ψ}`. -/
@[stacks 0D2Z "r_{L,psi} is characterized by property (2), for a morphism of algebraic spaces \
f : X -> Y: it is the only morphism U(psi) -> Proj_Y(A) over Y with clause (2)(b)"]
theorem eq_invertibleMorphism (Φ : R.locus.toFunctor ⟶ s.relativeProjFunctor)
    (hΦπ : Φ ≫ s.relativeProjπ = R.locus.ι ≫ f)
    (hΦ : ∀ {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X) {k : ℕ}
      (hk : 0 < k) [Epi ((R.twisting W w).app (k : ℤ))],
      R.factor w (R.mem_locus_of_epi w hk) ≫ Φ = R.quadruplePoint w hk) :
    Φ = R.invertibleMorphism := by
  ext ⟨T⟩ ⟨a, ha⟩
  set x : yoneda.obj T ⟶ X := yonedaEquiv.symm a
  have hx : yonedaEquiv x ∈ R.locus.obj (op T) := by
    show yonedaEquiv (yonedaEquiv.symm a) ∈ _
    rwa [Equiv.apply_symm_apply]
  have hsub : (⟨yonedaEquiv x, hx⟩ : R.locus.toFunctor.obj (op T)) = ⟨a, ha⟩ :=
    Subtype.ext (Equiv.apply_symm_apply _ _)
  have hval : ∀ Ψ : R.locus.toFunctor ⟶ s.relativeProjFunctor,
      Ψ.app (op T) ⟨a, ha⟩ = yonedaEquiv (R.factor x hx ≫ Ψ) := fun Ψ =>
    (congrArg (Ψ.app (op T)) hsub).symm.trans ((yonedaEquiv.apply_symm_apply _).symm.trans
      (congrArg yonedaEquiv (yonedaEquiv_symm_naturality_right T Ψ _).symm))
  suffices key : R.factor x hx ≫ Φ = R.factor x hx ≫ R.invertibleMorphism by
    exact (hval Φ).trans ((congrArg yonedaEquiv key).trans (hval R.invertibleMorphism).symm)
  have hover : ∀ Ψ : R.locus.toFunctor ⟶ s.relativeProjFunctor,
      Ψ ≫ s.relativeProjπ = R.locus.ι ≫ f →
        (R.factor x hx ≫ Ψ) ≫ s.relativeProjπ = yoneda.map (𝟙 T) ≫ (x ≫ f) := fun Ψ hΨ => by
    rw [Category.assoc, hΨ, ← Category.assoc, factor_ι, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hxtop : R.locusOpen T x = ⊤ := (R.mem_locus_iff x).1 hx
  refine congrArg Subtype.val
    ((s.relativeProjPoints.pointEquivProjOver T (x ≫ f) (𝟙 T)).injective
      (a₁ := ⟨_, hover Φ hΦπ⟩) (a₂ := ⟨_, hover _ R.invertibleMorphism_comp_π⟩) (Subtype.ext ?_))
  let O : PositiveSection (s.relativeProjPoints.algebra T (x ≫ f)) →
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens :=
    fun p => (toGradedPowerMap (R.twisting T x)).openOfPositiveSection p
  have hO : IsOpenCover O := by
    show ⨆ p, O p = ⊤
    rwa [← GradedPowerMap.coveringOpen_eq_iSup]
  refine Scheme.Cover.hom_ext
    (((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).openCoverOfIsOpenCover O hO) _ _
    fun (p : PositiveSection (s.relativeProjPoints.algebra T (x ≫ f))) => ?_
  show (O p).ι ≫ _ = (O p).ι ≫ _
  let Tp := openSiteObject s.site s.base s.containsBase T (O p)
  let ιp : Tp ⟶ T := openSiteObjectHom s.site s.base s.containsBase T (O p)
  have hιp : (BigFppfOver.toScheme s.site s.base s.containsBase).map ιp = (O p).ι :=
    map_openSiteObjectHom s.site s.base s.containsBase T (O p)
  have hepi : Epi ((R.twisting Tp (yoneda.map ιp ≫ x)).app ((p.deg + 1 : ℕ) : ℤ)) := by
    refine (R.epi_twisting_map_iff ιp x _).2 ?_
    refine epi_pullback_app_of_preimage_eq_top (R.twisting T x) _ p ?_
    rw [hιp]
    exact top_unique fun y _ => y.2
  have hmem := R.mem_locus_of_epi (yoneda.map ιp ≫ x) (Nat.succ_pos p.deg)
  have hfac := R.factor_comp ιp x hx hmem
  have e := (hΦ (yoneda.map ιp ≫ x) (Nat.succ_pos p.deg)).trans
    (R.factor_invertibleMorphism_of_epi (yoneda.map ιp ≫ x) (Nat.succ_pos p.deg)).symm
  rw [hfac, Category.assoc, Category.assoc] at e
  have n1 := s.relativeProjPoints.pointEquivProjOver_natural T (x ≫ f) (𝟙 T) ιp
    ⟨R.factor x hx ≫ Φ, hover Φ hΦπ⟩
  have n2 := s.relativeProjPoints.pointEquivProjOver_natural T (x ≫ f) (𝟙 T) ιp
    ⟨R.factor x hx ≫ R.invertibleMorphism, hover _ R.invertibleMorphism_comp_π⟩
  rw [← hιp]
  refine n1.symm.trans (Eq.trans ?_ n2)
  exact pointEquivProjOver_val_congr _ rfl e _ _

/-! ### Clause (3) -/

/-- The square `g ∘ f' = f ∘ g'`, read over the identity of `X'`. -/
theorem square_id {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X)
    (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f) :
    yoneda.map f' ≫ g = yoneda.map (𝟙 X') ≫ (g' ≫ f) := by
  rw [hsq, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The pullback `ψ' : (f')^*(g^*𝒜) ⟶ ⨁_d ((g')^*ℒ)^{⊗ d}` of `ψ` to a commutative square**
`g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes: the restriction `(g')^*ψ` of `ψ` to the scheme point
`g'` of `X`, read over `f' : X' ⟶ Y'` as a map out of the restriction `g^*𝒜` of `𝒜` to the
scheme point `g` of `Y`, through the comparisons of the restriction datum
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting` for the square
`X' = X' ⟶ Y'`). -/
def squarePsi {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X)
    (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f) :
    Twisting ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
      (situationAlgebra (s.relativeProjPoints.algebra Y' g)) 1
      ((pullbackFunctor (ringedSpaceHom
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 X')))).obj (R.line X' g')) :=
  s.quadrupleRestriction.squareTwisting s.shrink.contains_relativeProj_pointAlgebra
    s.shrink.space.property.isSheaf (R.twisting X' g') g f' (𝟙 X') (square_id g' f' g hsq)

omit R in
/-- The preimage of an open of `X'` under the identity morphism of `X'` is that open. -/
theorem preimage_map_id (X' : BigFppfOver s.site s.base s.containsBase)
    (O : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').Opens) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 X') ⁻¹ᵁ O = O := by
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **Clause (3) of [Stacks, Tag 0D2Z], the open: `U(ψ') = (g')^{-1}(U(ψ))`.**  For a commutative
square `g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes, the open `U(ψ')` of Tag 01O9 for the pullback
`ψ'` is the open that `U(ψ)` cuts on the scheme point `g'`, and the preimage of the open
subspace `U(ψ) ⊆ X` along `g'` is the open subscheme `U(ψ')` of `X'`. -/
theorem coveringOpen_squarePsi {X' Y' : BigFppfOver s.site s.base s.containsBase}
    (g' : yoneda.obj X' ⟶ X) (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1)
    (hsq : yoneda.map f' ≫ g = g' ≫ f) :
    (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen = R.locusOpen X' g' :=
  (s.quadrupleRestriction.coveringOpen_squareTwisting s.shrink.contains_relativeProj_pointAlgebra
    s.shrink.space.property.isSheaf (R.twisting X' g') g f' (𝟙 X') (square_id g' f' g hsq)).trans
    (preimage_map_id X' _)

/-- A test scheme `t : T ⟶ X'` with `g' ∘ t` in `U(ψ)` lies in `U(ψ')`. -/
theorem preimage_coveringOpen_squarePsi_eq_top {X' Y' T : BigFppfOver s.site s.base s.containsBase}
    (g' : yoneda.obj X' ⟶ X) (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1)
    (hsq : yoneda.map f' ≫ g = g' ≫ f) (t : T ⟶ X')
    (ht : yonedaEquiv (yoneda.map t ≫ g') ∈ R.locus.obj (op T)) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map t ⁻¹ᵁ
      (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen = ⊤ := by
  rw [R.coveringOpen_squarePsi, ← R.locusOpen_map]
  exact (R.mem_locus_iff _).1 ht

/-- The composite `T ⟶ U(ψ) ⟶ Proj_Y(𝒜)` of a test scheme `t : T ⟶ X'` with `g' ∘ t` in `U(ψ)`
lies over `g ∘ f' ∘ t`. -/
theorem factor_invertibleMorphism_comp_π {X' Y' T : BigFppfOver s.site s.base s.containsBase}
    (g' : yoneda.obj X' ⟶ X) (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1)
    (hsq : yoneda.map f' ≫ g = g' ≫ f) (t : T ⟶ X')
    (ht : yonedaEquiv (yoneda.map t ≫ g') ∈ R.locus.obj (op T)) :
    (R.factor (yoneda.map t ≫ g') ht ≫ R.invertibleMorphism) ≫ s.relativeProjπ =
      yoneda.map (t ≫ f') ≫ g := by
  rw [Category.assoc, invertibleMorphism_comp_π, ← Category.assoc, factor_ι, Category.assoc,
    ← hsq, CategoryTheory.Functor.map_comp, Category.assoc]

/-- **Clause (3) of [Stacks, Tag 0D2Z], for a morphism of algebraic spaces `f : X ⟶ Y`.**
Consider a commutative square `g ∘ f' = f ∘ g'` with `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
`g : Y' ⟶ Y` and `X'`, `Y'` schemes, `𝒜' = g^*𝒜`, `ℒ' = (g')^*ℒ`, and let `ψ'` be the pullback
of `ψ` (`squarePsi`).  Then

* `U(ψ') = (g')^{-1}(U(ψ))`: the preimage of the open subspace `U(ψ) ⊆ X` along `g'` is the open
  subscheme `U(ψ')` of `X'` of [Stacks, Tag 01O9]; and
* `r_{ψ',ℒ'} : U(ψ') ⟶ Proj_{Y'}(𝒜')` of [Stacks, Tag 01O9] agrees with the base change of
  `r_{ψ,ℒ}` through the identification `Proj_{Y'}(𝒜') = Y' ×_Y Proj_Y(𝒜)` of Stacks 084B: for
  every test scheme `t : T ⟶ X'` of `U(ψ')`, the `T`-point of `Y' ×_Y Proj_Y(𝒜)` with components
  `f' ∘ t` and `r_{ψ,ℒ} ∘ g' ∘ t` is, in `Proj_{Y'}(𝒜')`, the composite
  `T ⟶ U(ψ') ⟶ Proj_{Y'}(𝒜')`. -/
@[stacks 0D2Z "clause (3), the open and the morphism, for a morphism of algebraic spaces \
f : X -> Y and an ARBITRARY commutative square g o f' = f o g' with X', Y' schemes: with psi' the \
pullback of psi, U(psi') = (g')^{-1}(U(psi)) as open subspaces, and r_{psi',L'} : \
U(psi') -> Proj_{Y'}(g^*A) of Tag 01O9 is the base change of r_{L,psi} through the \
identification Proj_{Y'}(g^*A) = Y' x_Y Proj_Y(A) of Tag 084B, tested on every scheme \
T -> U(psi')"]
theorem invertibleMorphism_baseChange_square {X' Y' : BigFppfOver s.site s.base s.containsBase}
    (g' : yoneda.obj X' ⟶ X) (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1)
    (hsq : yoneda.map f' ≫ g = g' ≫ f) :
    R.locus.preimage g' = subspaceOfOpens s.site s.base s.containsBase X'
        (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen ∧
    ∀ {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
      (ht : yonedaEquiv (yoneda.map t ≫ g') ∈ R.locus.obj (op T)),
      (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
          ⟨R.factor (yoneda.map t ≫ g') ht ≫ R.invertibleMorphism,
            R.factor_invertibleMorphism_comp_π g' f' g hsq t ht⟩).1 =
        liftOfPreimageEqTop _ ((BigFppfOver.toScheme s.site s.base s.containsBase).map t)
            (R.preimage_coveringOpen_squarePsi_eq_top g' f' g hsq t ht) ≫
          (toGradedPowerMap (R.squarePsi g' f' g hsq)).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra Y' g)) := by
  refine ⟨(R.preimage_locus X' g').trans
    (congrArg (subspaceOfOpens s.site s.base s.containsBase X') (R.coveringOpen_squarePsi g' f' g
      hsq).symm), fun {T} t ht => ?_⟩
  have htop : R.locusOpen T (yoneda.map t ≫ g') = ⊤ := (R.mem_locus_iff _).1 ht
  have hτ := R.mem_subspaceOfOpens_of_locusOpen t g' htop
  have ht' : t ≫ 𝟙 X' ∈ (subspaceOfOpens s.site s.base s.containsBase X'
      (toGradedPowerMap (R.twisting X' g')).coveringOpen).obj (op T) := by
    rw [Category.comp_id]; exact hτ
  have key := (s.invertibleMorphism_baseChange_square (R.twisting X' g') g f' (𝟙 X')
    (square_id g' f' g hsq)).2 t ht'
  have hu : R.factor (yoneda.map t ≫ g') ht ≫ R.invertibleMorphism =
      s.relativeProjPoints.locusFactor (R.twisting X' g') (t ≫ 𝟙 X') ht' ≫
        s.relativeProjPoints.invertibleMorphism (R.twisting X' g') :=
    ((R.factor_invertibleMorphism _ ht).trans ((R.point_map t g' htop).trans
      (invertiblePoint_congr (R.twisting X' g') (Category.comp_id t).symm hτ ht'))).trans
      (s.relativeProjPoints.locusFactor_invertibleMorphism (R.twisting X' g') _ ht').symm
  exact (pointEquivProjOver_val_congr _ rfl hu _ _).trans key

end InvertibleTwistingRestriction

end AlgebraicGeometry.Space.RelativeProjSituation

end
