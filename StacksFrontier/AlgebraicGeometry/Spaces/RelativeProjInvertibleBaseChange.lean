module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.BaseDescent
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.BaseDescentTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleThetaBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison

/-!
# Stacks Tag 0D2Z: clause (1) for `V ⟶ Y` and clause (3) for an arbitrary scheme `Y' ⟶ Y`

In Situation 0849 let `Y` be the algebraic space, `𝒜` the quasi-coherent graded `𝒪_Y`-algebra and
`P = Proj_Y(𝒜)` its relative homogeneous spectrum of [Stacks, Tag 084B]
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`).  For a scheme `X` over `Y`,
an invertible `ℒ` on `X` and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}`, the open `U(ψ)` and the morphism
`r_{ℒ,ψ} : U(ψ) ⟶ P` are those of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleMorphismPoints.lean`.

Clause (3) of [Stacks, Tag 0D2Z] considers a commutative square `g ∘ f' = f ∘ g'` with `X'` and
`Y'` schemes, `𝒜' = g^*𝒜`, `ℒ' = g'^*ℒ` and `ψ'` the pullback of `ψ`, a map
`f'^*𝒜' ⟶ ⨁_d ℒ'^{⊗ d}`.  Here `ψ'` is `clauseThreeTwisting`: `g'^*ψ`, read through the
identifications `f'^*(g^*𝒜) ≅ (g ∘ f')^*𝒜 = (f ∘ g')^*𝒜 ≅ g'^*(f^*𝒜)` of the restriction datum of
Stacks 084A (`AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`).  This file
proves:

* `clauseThree_coveringOpen`: `U(ψ') = g'^{-1}(U(ψ))`;
* `clauseThree_morphism`: `r_{ℒ',ψ'}` of [Stacks, Tag 01O9] agrees with the base change of
  `r_{ℒ,ψ}` through the identification `Proj_{Y'}(𝒜') = Y' ×_Y P` of Stacks 084B: on every test
  scheme `t : T ⟶ U(ψ')`, the point `(f' ∘ t, r_{ℒ,ψ} ∘ g' ∘ t)` of `Y' ×_Y P` is
  `r_{ℒ',ψ'} ∘ t`;
* `clauseThree_theta`: `θ'` is the pullback of `θ` along `U(ψ') ⟶ U(ψ)`, through the
  identifications of the twists of `Proj_{Y'}(𝒜')` and `Proj_X(f^*𝒜)` over `X'`;
* `clauseOne`: clause (1) for every scheme `v : V ⟶ Y` (in particular every étale one), on every
  scheme `W` over `V ×_Y X`;
* `tag0D2Z`: the whole lemma.

The proof reads both `ψ'` and `g'^*ψ` over `X'` itself
(`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.baseDescent`), where they become the
same map `(g ∘ f')^*𝒜 ⟶ ⨁_d ℒ'^{⊗ d}`; the morphism of Tag 01O9 is compatible with that change of
base (`…globalMorphism_baseDescent`), and the two identifications of Stacks 084B over `Y'` and
over `X` are compatible with further base change to `X'` (`pointEquivProjOver_comp`).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (baseChangeHom)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp (pullbackGradedAlgebraCompIso
  pullbackGradedAlgebraCongrIso)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open GradedPowerMap (twD Otw psiU)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable (s : RelativeProjSituation.{u, m})

/-! ### The identifications of Stacks 084B under further base change -/

/-- **The identification `T ×_Y P = Proj_T(t^*𝒜)` of Stacks 084B is compatible with further base
change**, on points: a point of `P` over `h' ≫ h` read through the identification at `z` is the
point read through the identification at `z ∘ h`, followed by the comparison morphism of the third
assertion of Stacks 084B. -/
theorem pointEquivOver_comp {Z Z' T : BigFppfOver s.site s.base s.containsBase}
    (z : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) (h' : T ⟶ Z')
    (ξ : {u : yoneda.obj T ⟶ s.relativeProjFunctor //
      u ≫ s.relativeProjπ = yoneda.map (h' ≫ h) ≫ z}) :
    (s.relativeProjPoints.pointEquivOver Z z (h' ≫ h) ξ).1 =
      (s.relativeProjPoints.pointEquivOver Z' (yoneda.map h ≫ z) h'
          ⟨ξ.1, by rw [ξ.2, Functor.map_comp, Category.assoc]⟩).1 ≫
        s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra z h := by
  set σ := s.relativeProjPoints.pointEquivOver Z' (yoneda.map h ≫ z) h'
    ⟨ξ.1, by rw [ξ.2, Functor.map_comp, Category.assoc]⟩
  have hw : (σ.1 ≫ s.quadrupleRestriction.projComparison
      s.shrink.contains_relativeProj_pointAlgebra z h) ≫ s.relativeProjPoints.fibreHom Z z =
        h' ≫ h :=
    (Category.assoc _ _ _).trans ((congrArg (σ.1 ≫ ·) (s.isPullback_projComparison z h).1.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) σ.2)))
  have key : s.relativeProjPoints.pointEquivOver Z z (h' ≫ h) ξ = ⟨_, hw⟩ := by
    refine (Equiv.apply_eq_iff_eq_symm_apply _).2 (Subtype.ext ?_)
    exact ((congrArg (· ≫ s.relativeProjPoints.fibreToSpace Z z)
      (Functor.map_comp yoneda σ.1 (s.quadrupleRestriction.projComparison
        s.shrink.contains_relativeProj_pointAlgebra z h))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (yoneda.map σ.1 ≫ ·) (s.isPullback_projComparison z h).2.1).trans
          (s.relativeProjPoints.map_pointEquivOver Z' _ h' _)))).symm
  exact congrArg Subtype.val key

/-- **`pointEquivOver_comp` on the relative homogeneous spectra**, at a point `v` equal to
`z ∘ h`: the comparison morphism is the identification of the restricted algebras followed by
the base-change morphism of Tag 01O3. -/
theorem pointEquivProjOver_comp {Z Z' T : BigFppfOver s.site s.base s.containsBase}
    (z : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) (v : yoneda.obj Z' ⟶ s.space.1)
    (hv : yoneda.map h ≫ z = v) (h' : T ⟶ Z')
    (ξ : {u : yoneda.obj T ⟶ s.relativeProjFunctor //
      u ≫ s.relativeProjπ = yoneda.map (h' ≫ h) ≫ z}) :
    (s.relativeProjPoints.pointEquivProjOver Z z (h' ≫ h) ξ).1 =
      (s.relativeProjPoints.pointEquivProjOver Z' v h'
          ⟨ξ.1, by rw [ξ.2, ← hv, Functor.map_comp, Category.assoc]⟩).1 ≫
        (relativeProjCongr (A₁ := s.shrink.pointAlgebra Z' v)
          (A₂ := (s.shrink.pointAlgebra Z z).pullback
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))
          (s.quadrupleRestriction.restrict h z v hv)
          (s.quadrupleRestriction.isIso_restrict_app h z v hv)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra Z z)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h) := by
  subst hv
  have e1 := congrArg (fun k => (BigFppfOver.toScheme s.site s.base s.containsBase).map k)
    (s.pointEquivOver_comp z h h' ξ)
  have e2 := (s.isPullback_projComparison z h).2.2
  exact ((Category.comp_id _).trans (e1.trans ((Functor.map_comp _ _ _).trans
    (congrArg (_ ≫ ·) e2)))).trans (congrArg (· ≫ _) (Category.comp_id _).symm)

/-- **`Proj_{Z'}(v^*𝒜) = Z' ×_Z Proj_Z(z^*𝒜)`** at a point `v` equal to `z ∘ h`, through the
identification of the restricted algebras and the base-change morphism of Tag 01O3. -/
theorem isPullback_restrictProj {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (z : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) (v : yoneda.obj Z' ⟶ s.space.1)
    (hv : yoneda.map h ≫ z = v) :
    IsPullback
      ((relativeProjCongr (A₁ := s.shrink.pointAlgebra Z' v)
          (A₂ := (s.shrink.pointAlgebra Z z).pullback
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))
          (s.quadrupleRestriction.restrict h z v hv)
          (s.quadrupleRestriction.isIso_restrict_app h z v hv)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra Z z)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))
      (relativeProj (s.shrink.pointAlgebra Z' v)).toBase
      (relativeProj (s.shrink.pointAlgebra Z z)).toBase
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h) := by
  subst hv
  have e := (s.quadrupleRestriction.isPullback_baseChangeHom_restrictProjIso
    s.shrink.contains_relativeProj_pointAlgebra z h)
  exact e.2 ▸ e.1

/-! ### The pulled-back map `ψ'` of clause (3) -/

section ClauseThree

variable {s} {X : BigFppfOver s.site s.base s.containsBase} {f : yoneda.obj X ⟶ s.space.1}
  {L : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X).Modules}
  [Stacks.Ample.IsInvertibleModule _ L]
  (ψ : Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X))
    (situationAlgebra (s.relativeProjPoints.algebra X f)) 1 L)
  {Y' X' : BigFppfOver s.site s.base s.containsBase} (g : yoneda.obj Y' ⟶ s.space.1)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f)

/-- **The map `ψ'` of clause (3) of [Stacks, Tag 0D2Z]**: for a commutative square
`g ∘ f' = f ∘ g'` with `X'` and `Y'` schemes, the pullback `g'^*ψ` of `ψ`, read as a map
`f'^*(g^*𝒜) ⟶ ⨁_d (g'^*ℒ)^{⊗ d}` over `f' : X' ⟶ Y'` through the identifications
`g'^*(f^*𝒜) ≅ (f ∘ g')^*𝒜 = (g ∘ f')^*𝒜 ≅ f'^*(g^*𝒜)` of the restriction datum of Stacks 084A. -/
def clauseThreeTwisting :
    Twisting ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
      (situationAlgebra (s.relativeProjPoints.algebra Y' g)) 1
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme s.site s.base
        s.containsBase).map g'))).obj L) :=
  baseAscent (A := s.relativeProjPoints.algebra Y' g)
    (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
    (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
    (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl)
    (baseDescent (A := s.relativeProjPoints.algebra X f)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
      (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
      (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))

/-- `ψ'` and `g'^*ψ`, read over `X'`, are the same map `(g ∘ f')^*𝒜 ⟶ ⨁_d (g'^*ℒ)^{⊗ d}`. -/
theorem baseDescent_clauseThreeTwisting :
    baseDescent (A := s.relativeProjPoints.algebra Y' g)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
        (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
        (clauseThreeTwisting ψ g f' g' hsq) =
      baseDescent (A := s.relativeProjPoints.algebra X f)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
        (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
        (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')) :=
  baseDescent_baseAscent _ _ _ _

/-- **Clause (3) of [Stacks, Tag 0D2Z], for the open: `U(ψ') = g'^{-1}(U(ψ))`.** -/
theorem clauseThree_coveringOpen :
    (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map g' ⁻¹ᵁ
        (toGradedPowerMap ψ).coveringOpen :=
  (coveringOpen_baseDescent _ _ (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl) _).symm.trans
    ((congrArg (fun χ => (toGradedPowerMap χ).coveringOpen)
      (baseDescent_clauseThreeTwisting ψ g f' g' hsq)).trans
      ((coveringOpen_baseDescent _ _
        (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm) _).trans
        (coveringOpen_pullback ψ _)))

/-- A test scheme `t : T ⟶ X'` whose composite with `g'` lies in `U(ψ)` lies in `U(ψ')`. -/
theorem preimage_clauseThree_coveringOpen_eq_top {T : BigFppfOver s.site s.base s.containsBase}
    (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens s.site s.base s.containsBase X
      (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map t ⁻¹ᵁ
      (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen = ⊤ := by
  rw [clauseThree_coveringOpen, ← Scheme.Hom.comp_preimage, ← Functor.map_comp]
  exact top_unique fun y _ => (mem_subspaceOfOpens_iff _ _ _ X _ _).1 ht y

/-- The point `r_{ℒ,ψ} ∘ w` of `P` over a test scheme `w : T ⟶ U(ψ)` lies over `f ∘ w`. -/
private theorem locusFactor_invertibleMorphism_comp_π_eq
    {T : BigFppfOver s.site s.base s.containsBase} (w : T ⟶ X)
    (hw : w ∈ (subspaceOfOpens s.site s.base s.containsBase X
      (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (s.relativeProjPoints.locusFactor ψ w hw ≫ s.relativeProjPoints.invertibleMorphism ψ)
        ≫ s.relativeProjπ = yoneda.map w ≫ f := by
  rw [Category.assoc, RelativeProjPoints.invertibleMorphism_comp_π, ← Category.assoc,
    RelativeProjPoints.locusFactor_ι]

include hsq in
/-- The point `(f' ∘ t, r_{ℒ,ψ} ∘ g' ∘ t)` of `Y' ×_Y P` lies over `g`. -/
theorem locusFactor_invertibleMorphism_comp_π {T : BigFppfOver s.site s.base s.containsBase}
    (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens s.site s.base s.containsBase X
      (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (s.relativeProjPoints.locusFactor ψ (t ≫ g') ht ≫ s.relativeProjPoints.invertibleMorphism ψ)
        ≫ s.relativeProjπ = yoneda.map (t ≫ f') ≫ g := by
  rw [locusFactor_invertibleMorphism_comp_π_eq, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hsq]

/-- **Clause (3) of [Stacks, Tag 0D2Z], for the morphism.**  `r_{ℒ',ψ'} : U(ψ') ⟶ Proj_{Y'}(𝒜')`
of [Stacks, Tag 01O9] agrees with the base change of `r_{ℒ,ψ}` through the identification
`Proj_{Y'}(𝒜') = Y' ×_Y Proj_Y(𝒜)` of Stacks 084B: on every test scheme `t : T ⟶ X'` of
`U(ψ') = g'^{-1}(U(ψ))`, the point `(f' ∘ t, r_{ℒ,ψ} ∘ g' ∘ t)` of `Y' ×_Y P` is
`r_{ℒ',ψ'} ∘ t`. -/
theorem clauseThree_morphism {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens s.site s.base s.containsBase X
      (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
        ⟨s.relativeProjPoints.locusFactor ψ (t ≫ g') ht ≫ s.relativeProjPoints.invertibleMorphism ψ,
          locusFactor_invertibleMorphism_comp_π ψ g f' g' hsq t ht⟩).1 =
      liftOfPreimageEqTop _ _ (preimage_clauseThree_coveringOpen_eq_top ψ g f' g' hsq t ht) ≫
        (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).globalMorphism
          (relativeProj (s.relativeProjPoints.algebra Y' g)) := by
  set u := s.relativeProjPoints.locusFactor ψ (t ≫ g') ht ≫
    s.relativeProjPoints.invertibleMorphism ψ
  set C :=
    baseDescent (A := s.relativeProjPoints.algebra X f)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
    (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
    (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
  have hu : u ≫ s.relativeProjπ = yoneda.map t ≫ (yoneda.map f' ≫ g) := by
    rw [locusFactor_invertibleMorphism_comp_π ψ g f' g' hsq t ht, Functor.map_comp,
      Category.assoc]
  set σ := (s.relativeProjPoints.pointEquivProjOver X' (yoneda.map f' ≫ g) t ⟨u, hu⟩).1
  -- the identification over `Y'`, and the one over `X`, both through `X'`
  have hY := s.pointEquivProjOver_comp g f' (yoneda.map f' ≫ g) rfl t
    ⟨u, locusFactor_invertibleMorphism_comp_π ψ g f' g' hsq t ht⟩
  have huX : u ≫ s.relativeProjπ = yoneda.map (t ≫ g') ≫ f :=
    locusFactor_invertibleMorphism_comp_π_eq ψ (t ≫ g') ht
  have hX := s.pointEquivProjOver_comp f g' (yoneda.map f' ≫ g) hsq.symm t ⟨u, huX⟩
  have hB := s.relativeProjPoints.invertibleMorphism_baseChange ψ g' t ht
  obtain ⟨hleX, hCX⟩ := globalMorphism_of_eq_baseDescent _ _
    (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
    (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')) C rfl
  obtain ⟨hleY, hCY⟩ := globalMorphism_of_eq_baseDescent _ _
    (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl)
    (clauseThreeTwisting ψ g f' g' hsq) C (baseDescent_clauseThreeTwisting ψ g f' g' hsq)
  set lX := liftOfPreimageEqTop _ _
    (s.relativeProjPoints.preimage_coveringOpen_pullback_eq_top ψ g' t ht)
  set lY := liftOfPreimageEqTop _ _ (preimage_clauseThree_coveringOpen_eq_top ψ g f' g' hsq t ht)
  set rC := (toGradedPowerMap C).globalMorphism
    (relativeProj (s.relativeProjPoints.algebra X' (yoneda.map f' ≫ g)))
  -- `σ` is the lift of `t` through `U(C)` followed by `r_C`, by the cartesian square over `X`
  have hσ : σ = lX ≫ ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE hleX ≫
      rC := by
    refine (s.isPullback_restrictProj f g' _ hsq.symm).hom_ext ?_ ?_
    · refine hX.symm.trans (hB.trans ?_)
      exact (congrArg (lX ≫ ·) hCX.symm).trans
        ((congrArg (lX ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
    · have e1 := GradedPowerMap.globalMorphism_comp_toBase (toGradedPowerMap C)
        (relativeProj (s.relativeProjPoints.algebra X' (yoneda.map f' ≫ g)))
      refine (s.relativeProjPoints.pointEquivProjOver X' (yoneda.map f' ≫ g) t ⟨u, hu⟩).2.trans ?_
      refine (liftOfPreimageEqTop_ι _ _
        (s.relativeProjPoints.preimage_coveringOpen_pullback_eq_top ψ g' t ht)).symm.trans ?_
      refine (congrArg (lX ≫ ·) (Scheme.homOfLE_ι _ hleX).symm).trans ?_
      refine (congrArg (fun k => lX ≫ _ ≫ k) ((Category.comp_id _).symm.trans e1.symm)).trans ?_
      exact (congrArg (lX ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
  have hl : lX ≫ ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE hleX =
      lY ≫ ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE hleY :=
    (cancel_mono (toGradedPowerMap C).coveringOpen.ι).1
      ((Category.assoc _ _ _).trans ((congrArg (lX ≫ ·) (Scheme.homOfLE_ι _ hleX)).trans
        ((liftOfPreimageEqTop_ι _ _
          (s.relativeProjPoints.preimage_coveringOpen_pullback_eq_top ψ g' t ht)).trans
          ((liftOfPreimageEqTop_ι _ _
            (preimage_clauseThree_coveringOpen_eq_top ψ g f' g' hsq t ht)).symm.trans
            ((congrArg (lY ≫ ·) (Scheme.homOfLE_ι _ hleY)).symm.trans
              (Category.assoc _ _ _).symm)))))
  refine hY.trans ?_
  refine (congrArg (· ≫ _) hσ).trans ?_
  refine (congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ rC) hl).trans (Category.assoc _ _ _)))).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (lY ≫ ·) (Category.assoc _ _ _))).trans
    (congrArg (lY ≫ ·) hCY)

/-! ### `θ'` is the pullback of `θ` -/

/-- `U(ψ') ⊆ U(g'^*ψ)`: both are `g'^{-1}(U(ψ))`. -/
theorem clauseThree_coveringOpen_le :
    (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen ≤
      (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        g'))).coveringOpen :=
  ((clauseThree_coveringOpen ψ g f' g' hsq).trans (coveringOpen_pullback ψ _).symm).le

/-- **The restriction `j : U(ψ') ⟶ U(ψ)` of `g'`.** -/
abbrev clauseThreeRestrict :
    (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen.toScheme ⟶
      (toGradedPowerMap ψ).coveringOpen.toScheme :=
  ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
      (clauseThree_coveringOpen_le ψ g f' g' hsq) ≫
    coveringOpenPullback ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')

/-- The two identifications of `U(ψ')` and of `U(g'^*ψ)` with the open `U(ψ↓)` of `X'` agree. -/
theorem clauseThree_descentIncl_comp :
    ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq) ≫
      descentIncl (A := s.relativeProjPoints.algebra X f)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
        (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
        (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
        (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
        (baseDescent (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))) rfl =
      descentIncl (A := s.relativeProjPoints.algebra Y' g)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
        (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
        (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl)
        (clauseThreeTwisting ψ g f' g' hsq)
        (baseDescent (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
        (baseDescent_clauseThreeTwisting ψ g f' g' hsq) :=
  Scheme.homOfLE_homOfLE _ _ _

/-- **`j^*r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ≅ r_{ℒ',ψ'}^*(⨁_d 𝒪'(d))`**, the canonical identification through
which clause (3) compares `θ'` with `θ`: the pseudofunctoriality of the inverse image along
`j = (U(ψ') ⊆ U(g'^*ψ)) ≫ (U(g'^*ψ) ⟶ U(ψ))`, the identification of `[Stacks, Tag 01O9]` for
`g'^*ψ` (`…thetaSourceIso`), and the comparisons of the twists of `Proj_X(f^*𝒜)` and of
`Proj_{Y'}(g^*𝒜)` with those of `Proj_{X'}((g ∘ f')^*𝒜)` along the morphisms of Stacks 084B (3)
(`…thetaDescentSourceIso`, built from the `θ` of Tag 01O3). -/
def clauseThreeSourceIso :
    Stacks.Conormal.gradedPullback (clauseThreeRestrict ψ g f' g' hsq)
        (Stacks.Conormal.gradedPullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj (s.relativeProjPoints.algebra X f)))
          (twD (s.relativeProjPoints.algebra X f)).algebra) ≅
      Stacks.Conormal.gradedPullback
        ((toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).globalMorphism
          (relativeProj (s.relativeProjPoints.algebra Y' g)))
        (twD (s.relativeProjPoints.algebra Y' g)).algebra :=
  (pullbackGradedAlgebraCompIso
      (Stacks.Conormal.gradedPullback
        ((toGradedPowerMap ψ).globalMorphism (relativeProj (s.relativeProjPoints.algebra X f)))
        (twD (s.relativeProjPoints.algebra X f)).algebra)
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq))
      (coveringOpenPullback ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))).symm ≪≫
    pullbackGradedAlgebraMapIso
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq)).toLRSHom.toShHom
      (thetaSourceIso ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')) ≪≫
    pullbackGradedAlgebraMapIso
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq)).toLRSHom.toShHom
      (thetaDescentSourceIso (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
          rfl).symm ≪≫
    pullbackGradedAlgebraCompIso
      (Stacks.Conormal.gradedPullback
        ((toGradedPowerMap
            (baseDescent (A := s.relativeProjPoints.algebra X f)
              (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
              (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
              (ψ.pullback
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).globalMorphism
          (relativeProj (s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))))
        (twD (s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))).algebra)
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq))
      (descentIncl (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
          rfl) ≪≫
    pullbackGradedAlgebraCongrIso
        (Stacks.Conormal.gradedPullback
          ((toGradedPowerMap
              (baseDescent (A := s.relativeProjPoints.algebra X f)
                (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
                (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
                (ψ.pullback
                  ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).globalMorphism
            (relativeProj (s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))))
          (twD (s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))).algebra)
        (clauseThree_descentIncl_comp ψ g f' g' hsq) ≪≫
    thetaDescentSourceIso (A := s.relativeProjPoints.algebra Y' g)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
      (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
      (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl) (clauseThreeTwisting ψ g f' g' hsq)
      (baseDescent (A := s.relativeProjPoints.algebra X f)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
        (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
        (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
      (baseDescent_clauseThreeTwisting ψ g f' g' hsq)

/-- **`j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (g'^*ℒ)^{⊗ d}|_{U(ψ')}`**, the identification of the
targets of `j^*θ` and `θ'`: the restriction of the tensor powers along `j`, read through the
inverse image (`…thetaTargetIso`, `…thetaDescentTargetIso`). -/
def clauseThreeTargetIso :
    Stacks.Conormal.gradedPullback (clauseThreeRestrict ψ g f' g' hsq)
        (laurentOn (toGradedPowerMap ψ).L (toGradedPowerMap ψ).coveringOpen) ≅
      laurentOn (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).L
        (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen :=
  (pullbackGradedAlgebraCompIso (laurentOn (toGradedPowerMap ψ).L (toGradedPowerMap ψ).coveringOpen)
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq))
      (coveringOpenPullback ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))).symm ≪≫
    pullbackGradedAlgebraMapIso
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq)).toLRSHom.toShHom
      (thetaTargetIso ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')) ≪≫
    pullbackGradedAlgebraMapIso
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq)).toLRSHom.toShHom
      (thetaDescentTargetIso (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
          rfl).symm ≪≫
    pullbackGradedAlgebraCompIso
      (laurentOn
        (toGradedPowerMap
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).L
        (toGradedPowerMap
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).coveringOpen)
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj X').homOfLE
        (clauseThree_coveringOpen_le ψ g f' g' hsq))
      (descentIncl (A := s.relativeProjPoints.algebra X f)
          (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
          (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
          (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
          (baseDescent (A := s.relativeProjPoints.algebra X f)
            (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
          rfl) ≪≫
    pullbackGradedAlgebraCongrIso
        (laurentOn
          (toGradedPowerMap
            (baseDescent (A := s.relativeProjPoints.algebra X f)
              (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
              (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
              (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).L
          (toGradedPowerMap
            (baseDescent (A := s.relativeProjPoints.algebra X f)
              (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
              (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
              (ψ.pullback
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))).coveringOpen)
        (clauseThree_descentIncl_comp ψ g f' g' hsq) ≪≫
    thetaDescentTargetIso (A := s.relativeProjPoints.algebra Y' g)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
      (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
      (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl) (clauseThreeTwisting ψ g f' g' hsq)
      (baseDescent (A := s.relativeProjPoints.algebra X f)
        (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
        (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
        (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
      (baseDescent_clauseThreeTwisting ψ g f' g' hsq)


/-- **The last assertion of clause (3) of [Stacks, Tag 0D2Z]: `θ'` is the pullback of `θ`.**
For the square `g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes, the map
`θ' : r_{ℒ',ψ'}^*(⨁_d 𝒪_{Proj_{Y'}(𝒜')}(d)) ⟶ ⨁_d ℒ'^{⊗ d}|_{U(ψ')}` of [Stacks, Tag 01O9] for `ψ'`
is the inverse image `j^*θ` of `θ : r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` along the
restriction `j : U(ψ') ⟶ U(ψ)` of `g'`, read through the canonical identifications
`clauseThreeSourceIso` and `clauseThreeTargetIso` of the sources and the targets. -/
theorem clauseThree_theta :
    (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).theta =
      (clauseThreeSourceIso ψ g f' g' hsq).inv ≫
        pullbackGradedAlgebraMap (clauseThreeRestrict ψ g f' g' hsq).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫
        (clauseThreeTargetIso ψ g f' g' hsq).hom := by
  have h1 := theta_pullback ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
  have h2 :=
    theta_baseDescent (A := s.relativeProjPoints.algebra X f)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
    (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
    (s.quadrupleRestriction.isIso_restrict_app g' f _ hsq.symm)
    (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))
    (baseDescent (A := s.relativeProjPoints.algebra X f)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
      (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
      (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g'))) rfl
  have h3 :=
    theta_baseDescent (A := s.relativeProjPoints.algebra Y' g)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map f')
    (s.quadrupleRestriction.restrict f' g (yoneda.map f' ≫ g) rfl)
    (s.quadrupleRestriction.isIso_restrict_app f' g _ rfl) (clauseThreeTwisting ψ g f' g' hsq)
    (baseDescent (A := s.relativeProjPoints.algebra X f)
      (A₁ := s.shrink.pointAlgebra X' (yoneda.map f' ≫ g))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
      (s.quadrupleRestriction.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
      (ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')))
    (baseDescent_clauseThreeTwisting ψ g f' g' hsq)
  have h12 := (Iso.eq_comp_inv _).2 ((Iso.inv_comp_eq _).1 (h2.symm.trans h1))
  refine h3.trans ?_
  refine (congrArg (fun t => _ ≫ t ≫ _) (pullbackGradedAlgebraMap_congr_eq _
    (clauseThree_descentIncl_comp ψ g f' g' hsq))).trans ?_
  refine (congrArg (fun t => _ ≫ (_ ≫ t ≫ _) ≫ _) (pullbackGradedAlgebraMap_comp_eq _ _ _)).trans ?_
  refine (congrArg (fun t => _ ≫ (_ ≫ (_ ≫ pullbackGradedAlgebraMap _ t ≫ _) ≫ _) ≫ _) h12).trans ?_
  refine (congrArg (fun t => _ ≫ (_ ≫ (_ ≫ t ≫ _) ≫ _) ≫ _)
    (pullbackGradedAlgebraMap_comp_pullback_iso _ _ _ _ _ _ _)).trans ?_
  unfold clauseThreeSourceIso clauseThreeTargetIso
  exact iso_chain_conj _ _ _ _ _ _ _ _ _ _ _ _ _

end ClauseThree

/-! ### Clause (1) for an arbitrary scheme `V ⟶ Y`, and the whole tag -/

section Tag

variable {s} {X : BigFppfOver s.site s.base s.containsBase} {f : yoneda.obj X ⟶ s.space.1}
  {L : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X).Modules}
  [Stacks.Ample.IsInvertibleModule _ L]
  (ψ : Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X))
      (situationAlgebra (s.relativeProjPoints.algebra X f)) 1 L)

/-- **Clause (1) of [Stacks, Tag 0D2Z]**, for a scheme `v : V ⟶ Y` and a scheme `W` over
`V ×_Y X` (`p : W ⟶ V`, `q : W ⟶ X`, `v ∘ p = f ∘ q`), so that `U(ψ') = q^{-1}(U(ψ))` is the part
of `W` over `V ×_Y U(ψ)` and `r_{ℒ',ψ'} : U(ψ') ⟶ Proj_V(v^*𝒜) = V ×_Y Proj_Y(𝒜)` is the base
change of `r_{ℒ,ψ}` (`clauseThree_morphism`).  For `d ≥ 0` and a section `a` of `v^*𝒜_d` over an
open `O` of `V` (for `V ⟶ Y` étale and `O = V` these are the sections `𝒜_d(V)` of `𝒜`), the map `θ`
— pulled back to `U(ψ')` through the canonical identifications of clause (3) — carries the inverse
image of `ψ_{Proj}(a) ∈ Γ(O ×_Y Proj_Y(𝒜), 𝒪(d))` to the restriction of
`ψ(a) ∈ Γ(O ×_Y X, ℒ^{⊗ d})`: the square of clause (1) commutes. -/
theorem clauseOne {V W : BigFppfOver s.site s.base s.containsBase} (v : yoneda.obj V ⟶ s.space.1)
    (p : W ⟶ V) (q : W ⟶ X) (hpq : yoneda.map p ≫ v = yoneda.map q ≫ f)
    (O : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V).Opens) (n : ℕ)
    (a : Γ((s.relativeProjPoints.algebra V v).piece (n : ℤ), O)) :
    ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).powK n).presheaf.map
        (eqToHom ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).toBase_preimage_eq O)).op
      ((((clauseThreeSourceIso ψ v p q hpq).inv ≫
          pullbackGradedAlgebraMap (clauseThreeRestrict ψ v p q hpq).toLRSHom.toShHom
            (toGradedPowerMap ψ).theta ≫
          (clauseThreeTargetIso ψ v p q hpq).hom).app n).val.app
        (op
            ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra V v)) ⁻¹ᵁ
          ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O)))
        (pullbackUnit ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra V v))).toLRSHom.toShHom
          (Otw (s.relativeProjPoints.algebra V v) n)
              (op ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O))
              (psiU (s.relativeProjPoints.algebra V v) n O a))) =
      (tensorPowerModule ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)
          (toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).L n).presheaf.map
          (homOfLE
              ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).coveringOpen.ι.image_preimage_le
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map p ⁻¹ᵁ O))).op
        ((powCompare (toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).L n).hom.app
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map p ⁻¹ᵁ O)
          (valueSec (clauseThreeTwisting ψ v p q hpq) n O a)) := by
  have h := (toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).theta_clauseOne O n a
  rw [toGradedPowerMap_value (clauseThreeTwisting ψ v p q hpq) n O a] at h
  refine (congrArg
      (fun θ₀ => ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).powK n).presheaf.map
      (eqToHom ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).toBase_preimage_eq O)).op
      ((θ₀.app n).val.app
        (op
            ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra V v)) ⁻¹ᵁ
          ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O)))
        (pullbackUnit ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra V v))).toLRSHom.toShHom
          (Otw (s.relativeProjPoints.algebra V v) n)
              (op ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O))
              (psiU (s.relativeProjPoints.algebra V v) n O a))))
      (clauseThree_theta ψ v p q hpq).symm).trans h

/-- **[Stacks, Tag 0D2Z].**  In Situation 0849 let `Y` be the algebraic space `s.space`, `𝒜` the
quasi-coherent graded `𝒪_Y`-algebra `s.algebra` and `π : Proj_Y(𝒜) ⟶ Y` its relative homogeneous
spectrum of Stacks 084B (`s.relativeProjFunctor`, `s.relativeProjπ`).  Let `f : X ⟶ Y` with `X` a
scheme, `ℒ` invertible on `X` and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, and
let `U(ψ) ⊆ X` be the open subspace of [Stacks, Tag 0D2Y].  Then `ψ` induces the morphism
`r_{ℒ,ψ} = s.relativeProjPoints.invertibleMorphism ψ : U(ψ) ⟶ Proj_Y(𝒜)` and the map of graded
algebras `θ = (toGradedPowerMap ψ).theta : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` (the twists of
`Proj_Y(𝒜)` read at the scheme point `f`, where they are those of `Proj_X(f^*𝒜)`, Stacks 084D (3)),
such that:

1. `r_{ℒ,ψ}` is a morphism over `Y`, and `θ` preserves the unit and the products;
2. **clause (1)**: for every scheme `v : V ⟶ Y` (in particular every `V ⟶ Y` étale), every scheme
   `W` over `V ×_Y X`, every open `O` of `V`, `d ≥ 0` and section `a` of `v^*𝒜_d` over `O`, the
   pullback of `θ` to `V ×_Y U(ψ)` carries the inverse image of `ψ_{Proj}(a)` to the restriction of
   `ψ(a)` (`clauseOne`);
3. **clause (2)(a)**: a scheme `W ⟶ X` over which `ψ` is surjective in some degree `k ≥ 1`
   factors through `U(ψ)`;
4. **clause (2)(b)**: the composite `W ⟶ U(ψ) ⟶ Proj_Y(𝒜)` is the point of `Proj_Y(𝒜)` which the
   construction of the relative Proj attaches to the quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`;
5. **the characterization**: `r_{ℒ,ψ}` is the only morphism over `Y` with clause (2)(b);
6. **clause (3)**: for every commutative square `g ∘ f' = f ∘ g'` with `X'` and `Y'` schemes,
   with `ψ' = clauseThreeTwisting ψ g f' g' hsq` the pullback of `ψ`:
   `U(ψ') = g'^{-1}(U(ψ))`; `r_{ℒ',ψ'}` is the base change of `r_{ℒ,ψ}` through
   `Proj_{Y'}(g^*𝒜) = Y' ×_Y Proj_Y(𝒜)`; and `θ'` is the pullback of `θ` along
   `j : U(ψ') ⟶ U(ψ)`. -/
@[stacks 0D2Z "variant: X a scheme; the whole lemma, in Situation 0849 with Proj_Y(A) the relative Proj of Stacks 084B \
and X a scheme over the algebraic space Y: the morphism r_{L,psi} : U(psi) -> Proj_Y(A) over Y; \
theta : r^*((+)_d O(d)) -> (+)_d L^d|_{U(psi)} a unital multiplicative map; clause (1) for every \
scheme V -> Y (in particular every etale one) and every scheme over V x_Y X; clauses (2)(a) and \
(2)(b) for every scheme W -> X and every degree d >= 1; the characterization of r_{L,psi} by \
(2)(b); and clause (3) for every square with X', Y' schemes and Y' -> Y arbitrary: \
U(psi') = (g')^{-1}(U(psi)), r_{L',psi'} is the base change of r_{L,psi} through \
Proj_{Y'}(A') = Y' x_Y Proj_Y(A), and theta' is the pullback of theta"]
theorem tag0D2Z :
    s.relativeProjPoints.invertibleMorphism ψ ≫ s.relativeProjπ =
        (subspaceOfOpens s.site s.base s.containsBase X (toGradedPowerMap ψ).coveringOpen).ι ≫ f ∧
    SheafOfModules.sectionsMap (((toGradedPowerMap ψ).theta).app 0)
        (Stacks.Conormal.gradedPullback
            ((toGradedPowerMap ψ).globalMorphism (relativeProj (s.relativeProjPoints.algebra X f)))
            (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
              (s.relativeProjPoints.algebra X f)).algebra).one =
      (laurentOn L (toGradedPowerMap ψ).coveringOpen).one ∧
    (∀ (n e : ℕ) (U : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
        (x :
            ((Stacks.Conormal.gradedPullback
                ((toGradedPowerMap ψ).globalMorphism
                  (relativeProj (s.relativeProjPoints.algebra X f)))
                (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
                  (s.relativeProjPoints.algebra X f)).algebra).piece
              (n : ℤ)).val.obj
            (op U))
        (y :
            ((Stacks.Conormal.gradedPullback
                ((toGradedPowerMap ψ).globalMorphism
                  (relativeProj (s.relativeProjPoints.algebra X f)))
                (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
                  (s.relativeProjPoints.algebra X f)).algebra).piece
              (e : ℤ)).val.obj
            (op U)),
        (((toGradedPowerMap ψ).theta.app ((n : ℤ) + (e : ℤ))).val.app (op U)
            (((Stacks.Conormal.gradedPullback
                    ((toGradedPowerMap ψ).globalMorphism
                      (relativeProj (s.relativeProjPoints.algebra X f)))
                    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
                      (s.relativeProjPoints.algebra X f)).algebra).mul
                  n e).app
                (op U) x y)) =
          ((laurentOn L (toGradedPowerMap ψ).coveringOpen).mul n e).app (op U)
            (((toGradedPowerMap ψ).theta.app n).val.app (op U) x)
            (((toGradedPowerMap ψ).theta.app e).val.app (op U) y)) ∧
    (∀ {V W : BigFppfOver s.site s.base s.containsBase} (v : yoneda.obj V ⟶ s.space.1) (p : W ⟶ V)
        (q : W ⟶ X)
        (hpq : yoneda.map p ≫ v = yoneda.map q ≫ f)
        (O : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V).Opens) (n : ℕ)
        (a : Γ((s.relativeProjPoints.algebra V v).piece (n : ℤ), O)),
      ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).powK n).presheaf.map
          (eqToHom ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).toBase_preimage_eq O)).op
        ((((clauseThreeSourceIso ψ v p q hpq).inv ≫
            pullbackGradedAlgebraMap (clauseThreeRestrict ψ v p q hpq).toLRSHom.toShHom
              (toGradedPowerMap ψ).theta ≫
            (clauseThreeTargetIso ψ v p q hpq).hom).app n).val.app
          (op
              ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
                (relativeProj (s.relativeProjPoints.algebra V v)) ⁻¹ᵁ
            ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O)))
          (pullbackUnit ((toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra V v))).toLRSHom.toShHom
            (Otw (s.relativeProjPoints.algebra V v) n)
                (op ((relativeProj (s.relativeProjPoints.algebra V v)).toBase ⁻¹ᵁ O))
                (psiU (s.relativeProjPoints.algebra V v) n O a))) =
        (tensorPowerModule ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)
            (toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).L n).presheaf.map
            (homOfLE
                ((toGradedPowerMap
                  (clauseThreeTwisting ψ v p q hpq)).coveringOpen.ι.image_preimage_le
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map p ⁻¹ᵁ O))).op
          ((powCompare (toGradedPowerMap (clauseThreeTwisting ψ v p q hpq)).L n).hom.app
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map p ⁻¹ᵁ O)
            (valueSec (clauseThreeTwisting ψ v p q hpq) n O a))) ∧
    (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : W ⟶ X) {k : ℕ} (_ : 0 < k)
        [Epi
              ((ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map w)).app
                (k : ℤ))],
            w ∈
            (subspaceOfOpens s.site s.base s.containsBase X (toGradedPowerMap ψ).coveringOpen).obj
              (op W)) ∧
    (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
        [Epi
            ((ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map w)).app (k : ℤ))],
        s.relativeProjPoints.locusFactor ψ w
            (s.relativeProjPoints.mem_subspaceOfOpens_of_epi ψ w hk) ≫
            s.relativeProjPoints.invertibleMorphism ψ =
                s.relativeProjPoints.quadruplePoint ψ w hk) ∧
    (∀ Φ :
        (subspaceOfOpens s.site s.base s.containsBase X
            (toGradedPowerMap ψ).coveringOpen).toFunctor ⟶
          s.relativeProjFunctor,
      Φ ≫ s.relativeProjπ =
      (subspaceOfOpens s.site s.base s.containsBase X (toGradedPowerMap ψ).coveringOpen).ι ≫ f →
      (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
        [Epi
            ((ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map w)).app (k : ℤ))],
        s.relativeProjPoints.locusFactor ψ w
          (s.relativeProjPoints.mem_subspaceOfOpens_of_epi ψ w hk) ≫
          Φ = s.relativeProjPoints.quadruplePoint ψ w hk) →
      Φ = s.relativeProjPoints.invertibleMorphism ψ) ∧
    (∀ {Y' X' : BigFppfOver s.site s.base s.containsBase} (g : yoneda.obj Y' ⟶ s.space.1)
        (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f),
      (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).coveringOpen =
          (BigFppfOver.toScheme s.site s.base s.containsBase).map g' ⁻¹ᵁ
          (toGradedPowerMap ψ).coveringOpen ∧
      (∀ {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
        (ht : t ≫ g' ∈
          (subspaceOfOpens s.site s.base s.containsBase X (toGradedPowerMap ψ).coveringOpen).obj
            (op T)),
        (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
            ⟨s.relativeProjPoints.locusFactor ψ (t ≫ g') ht ≫
              s.relativeProjPoints.invertibleMorphism ψ,
              locusFactor_invertibleMorphism_comp_π ψ g f' g' hsq t ht⟩).1 =
          liftOfPreimageEqTop _ _ (preimage_clauseThree_coveringOpen_eq_top ψ g f' g' hsq t ht) ≫
            (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra Y' g))) ∧
      (toGradedPowerMap (clauseThreeTwisting ψ g f' g' hsq)).theta =
        (clauseThreeSourceIso ψ g f' g' hsq).inv ≫
          pullbackGradedAlgebraMap (clauseThreeRestrict ψ g f' g' hsq).toLRSHom.toShHom
            (toGradedPowerMap ψ).theta ≫
          (clauseThreeTargetIso ψ g f' g' hsq).hom) :=
  ⟨s.relativeProjPoints.invertibleMorphism_comp_π ψ,
    (s.relativeProjPoints.invertibleTheta_clauseOne ψ).1,
    (s.relativeProjPoints.invertibleTheta_clauseOne ψ).2.1,
    fun v p q hpq O n a => clauseOne ψ v p q hpq O n a,
    fun w _ hk _ => s.relativeProjPoints.mem_subspaceOfOpens_of_epi ψ w hk,
    fun w _ hk _ => s.relativeProjPoints.locusFactor_invertibleMorphism_of_epi ψ w hk,
    fun Φ hΦπ hΦ => s.relativeProjPoints.eq_invertibleMorphism ψ Φ hΦπ hΦ,
    fun g f' g' hsq => ⟨clauseThree_coveringOpen ψ g f' g' hsq,
      fun t ht => clauseThree_morphism ψ g f' g' hsq t ht, clauseThree_theta ψ g f' g' hsq⟩⟩

end Tag

end AlgebraicGeometry.Space.RelativeProjSituation
