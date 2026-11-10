module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleMorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace

/-!
# Clause (2)(b) of Stacks 0D2Z on the constructed relative Proj

[Stacks, Tag 0D2Z] attaches to a morphism `f : X ⟶ Y` towards an algebraic space `Y` carrying a
quasi-coherent graded algebra `𝒜`, an invertible `𝒪_X`-module `ℒ` and a homomorphism of graded
algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` a morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`. Its clause (2)(b)
says: for `d ≥ 1` and a scheme `W ⟶ X` over which `ψ|_W : f^*𝒜_d|_W ⟶ ℒ^{⊗ d}|_W` is surjective,
the composite `W ⟶ U(ψ) ⟶ Proj_Y(𝒜)` *agrees with the morphism `W ⟶ Proj_Y(𝒜)` which exists by
the construction of `Proj_Y(𝒜)`* (Definition 084C): the point of the functor `F` of
quadruples of Stacks 084A given by the quadruple `(d, W ⟶ Y, ℒ^{⊗ d}|_W, ψ^{(d)}|_W)`.

`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleMorphismPoints.lean` builds
`r_{ℒ,ψ}` for any presentation of `Proj_Y(𝒜)` by its base changes to the scheme points of `Y`
(`AlgebraicGeometry.Space.RelativeProjPoints`), and there clause (2)(b) can only name the
morphism attached to the quadruple through the presentation at the point `f`
(`AlgebraicGeometry.Space.RelativeProjPoints.quadruplePoint`). This file states the clause on the
relative Proj that the library constructs, the functor of quadruples
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor` of Situation 0849 with its
presentation `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`
(Stacks 084B), where "the morphism which exists by the construction" has its literal meaning: a
morphism `W ⟶ Proj_Y(𝒜)` is a point of `F(W)`, and the point of `r_{ℒ,ψ}` at `W` is the class of
the quadruple of clause (2)(b).

The quadruple `(d, W ⟶ Y, ℒ^{⊗ d}|_W, ψ^{(d)}|_W)` is a quadruple for the restriction `w^*(f^*𝒜)`
of the algebra at the point `f` to `W`; a point of `F(W)` over `f ∘ w` is a class of quadruples
for the restriction `(f ∘ w)^*𝒜`. The two algebras are identified by the comparison of the
restriction datum of the situation
(`AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`), and the passage from one
to the other is `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreOfF`, the inverse of the
comparison by which Stacks 084B identifies `Z ×_X F` with the functor of quadruples of `g^*𝒜`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.clauseTwoClass`: the class over `W`
  of the quadruple `(k, W ⟶ X, ℒ^{⊗ k}|_W, ψ^{(k)}|_W)` of clause (2) of Tag 01O9.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpaceEquiv_invertibleMorphism_val`:
  the statement below for the functor of quadruples of an arbitrary restriction datum of a
  family of quasi-coherent graded algebras.
* `AlgebraicGeometry.Space.RelativeProjSituation.quadrupleSpaceEquiv_invertibleMorphism_val`:
  **clause (2)(b) on the constructed relative Proj**, for an arbitrary scheme `W ⟶ X`: the point
  of `F(W)` given by `W ⟶ U(ψ) ⟶ Proj_Y(𝒜)` records, at every quasi-compact `v : W' ⟶ W`, the
  class of the pullback along `v` of the quadruple of clause (2)(b).
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctorEquivF_invertibleMorphism`:
  the same for a quasi-compact `W`, where `F(W)` is the set of classes of quadruples itself.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
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

/-! ### The quadruple of clause (2)(b) of Tag 01O9, as a class over the test scheme -/

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L)

/-- The class of the quadruple `(k, q ≫ f, (q^*ℒ)^{⊗ k}, ψ^{(k)}|_W)` of clause (2) of Tag 01O9
over the open `⊤` of `W`, for a morphism `q : W ⟶ T` over which `ψ` is surjective in degree `k`. -/
def clauseTwoTopClass {W : Scheme.{u}} (q : W ⟶ T) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback q).app (k : ℤ))] :
    F (situationAlgebra A) (⊤ : W.Opens).toScheme :=
  F.mk ((⊤ : W.Opens).ι ≫ q ≫ f) (by exact_mod_cast hk)
    (haveI : Epi (((ψ.pullback q).pullback (⊤ : W.Opens).ι).app (k : ℤ)) :=
      Twisting.epi_pullbackApp _ _ _ inferInstance
     restrictQuadruple (ψ.pullback q) ⊤ k)

/-- **The quadruple of clause (2) of Tag 01O9 as a class over `W`**: for a morphism
`q : W ⟶ T` over which `ψ` is surjective in degree `k ≥ 1`, the class over `W` of the quadruple
`(k, q ≫ f, (q^*ℒ)^{⊗ k}, ψ^{(k)}|_W)`. -/
def clauseTwoClass {W : Scheme.{u}} (q : W ⟶ T) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback q).app (k : ℤ))] : F (situationAlgebra A) W :=
  F.pullback W.topIso.inv (clauseTwoTopClass ψ q hk)

/-- The class of clause (2) lies over `q ≫ f`. -/
theorem clauseTwoClass_fst {W : Scheme.{u}} (q : W ⟶ T) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback q).app (k : ℤ))] : (clauseTwoClass ψ q hk).1 = q ≫ f := by
  change W.topIso.inv ≫ (⊤ : W.Opens).ι ≫ q ≫ f = _
  rw [Scheme.toIso_inv_ι_assoc]

/-- The pullback along `g : W' ⟶ W` of the class of clause (2) lies over `g ≫ q ≫ f`. -/
theorem pullback_clauseTwoClass_fst {W W' : Scheme.{u}} (g : W' ⟶ W) (q : W ⟶ T) {k : ℕ}
    (hk : 0 < k) [Epi ((ψ.pullback q).app (k : ℤ))] :
    (F.pullback g (clauseTwoClass ψ q hk)).1 = g ≫ q ≫ f :=
  congrArg (g ≫ ·) (clauseTwoClass_fst ψ q hk)

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

/-! ### The section of `X ×_Y P` behind `quadruplePoint`, for any presentation -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π) {X : BigFppfOver B S hS} {f : yoneda.obj X ⟶ Y}
    {L : ((BigFppfOver.toScheme B S hS).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X)) (situationAlgebra (d.algebra X f)) 1 L)

/-- The point `quadruplePoint` of clause (2)(b) comes from a section of `X ×_Y P` over `w` whose
scheme morphism is the morphism `W ⟶ Proj_X(f^*𝒜)` classifying the quadruple of clause (2)(b). -/
theorem exists_quadruplePoint_eq {W : BigFppfOver B S hS} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))] :
    ∃ s' : W ⟶ d.fibre X f, s' ≫ d.fibreHom X f = w ∧
      (BigFppfOver.toScheme B S hS).map s' ≫ (d.fibreIso X f).hom =
        (Scheme.topIso _).inv ≫ F.classifyingMorphism (d.algebra X f)
          (clauseTwoTopClass ψ ((BigFppfOver.toScheme B S hS).map w) hk) ∧
      yoneda.map s' ≫ d.fibreToSpace X f = d.quadruplePoint ψ w hk := by
  obtain ⟨z, hz1, hz2⟩ : ∃ z, d.quadruplePoint ψ w hk = ((d.pointEquivProjOver X f w).symm z).1 ∧
      z.1 = (Scheme.topIso _).inv ≫ F.classifyingMorphism (d.algebra X f)
        (clauseTwoTopClass ψ ((BigFppfOver.toScheme B S hS).map w) hk) := ⟨_, rfl, rfl⟩
  exact ⟨(d.pointEquivOver X f w ((d.pointEquivProjOver X f w).symm z)).1,
    (d.pointEquivOver X f w ((d.pointEquivProjOver X f w).symm z)).2,
    (d.pointEquivProjOver_apply X f w ((d.pointEquivProjOver X f w).symm z)).symm.trans
      ((congrArg Subtype.val ((d.pointEquivProjOver X f w).apply_symm_apply z)).trans hz2),
    (d.map_pointEquivOver X f w ((d.pointEquivProjOver X f w).symm z)).trans hz1.symm⟩

end RelativeProjPoints

/-! ### Clause (2)(b) on the functor of quadruples of a restriction datum -/

namespace GradedAlgebraRestriction

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

/-- **Clause (2)(b) of Stacks 0D2Z on the functor of quadruples of a restriction datum.**  The
point of `F(W)` given by `W ⟶ U(ψ) ⟶ F` records, at every quasi-compact `v : W' ⟶ W`, the class of
the pullback along `v` of the quadruple `(k, w, (w^*ℒ)^{⊗ k}, ψ^{(k)}|_W)`, transported from
`(w ∘ v)^*(f^*𝒜)` to `(f ∘ w ∘ v)^*𝒜` along the comparison of the restriction datum. -/
theorem quadrupleSpaceEquiv_invertibleMorphism_val
    {W : BigFppfOver B S hS} (w : W ⟶ Z) {k : ℕ} (hk : 0 < k)
    [hε : Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))]
    (W' : BigFppfOver B S hS) (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W'))
    (v : W' ⟶ W) :
    (ρ.quadrupleSpaceEquiv hc hX W
        (yonedaEquiv ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ w
          ((ρ.quadrupleRelativeProjPoints hc hX).mem_subspaceOfOpens_of_epi ψ w hk) ≫
            (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ))).val W' hW' v =
      ⟨yoneda.map (v ≫ w) ≫ f,
        ρ.fibreOfF f (v ≫ w) (yoneda.map (v ≫ w) ≫ f) rfl
          (F.pullback ((BigFppfOver.toScheme B S hS).map v)
            (clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk))
          ((pullback_clauseTwoClass_fst ψ _ _ hk).trans
            ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Functor.map_comp _ _ _).symm))⟩ := by
  rw [RelativeProjPoints.locusFactor_invertibleMorphism_of_epi _ ψ w hk]
  obtain ⟨s', hs'2, hs'3, hs'1⟩ : ∃ s' : W ⟶ projObj Â f (hc Z f),
      s' ≫ projHom Â f (hc Z f) = w ∧
      (BigFppfOver.toScheme B S hS).map s' = (Scheme.topIso _).inv ≫
        F.classifyingMorphism ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)
          (clauseTwoTopClass ψ ((BigFppfOver.toScheme B S hS).map w) hk) ∧
      yoneda.map s' ≫ ρ.projToQuadrupleSpace hc hX f =
        (ρ.quadrupleRelativeProjPoints hc hX).quadruplePoint ψ w hk := by
    obtain ⟨s', h2, h3, h1⟩ :=
      (ρ.quadrupleRelativeProjPoints hc hX).exists_quadruplePoint_eq ψ w hk
    exact ⟨s', h2, (Category.comp_id _).symm.trans h3, h1⟩
  rw [← hs'1, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hpt : ρ.quadrupleSpaceEquiv hc hX W ((ρ.projToQuadrupleSpace hc hX f).app (op W) s') =
      ρ.limPointEquiv hX W (ρ.projPoint f (hc Z f) s') := by
    change ρ.quadrupleSpaceEquiv hc hX W (ρ.relativeProjFunctorEquivQuadruple hc hX W
      ((ρ.projToFunctor hc f).app (op W) s')) = _
    rw [quadrupleSpaceEquiv_relativeProjFunctorEquivQuadruple,
      relativeProjFunctorEquiv_projToFunctor]
  rw [hpt]
  have hval : ((relativeProjRepresentableByFunctorUnconditional (Â Z f)).homEquiv
      ((BigFppfOver.toScheme B S hS).map s')).val _ hW' ((BigFppfOver.toScheme B S hS).map v) =
        F.pullback ((BigFppfOver.toScheme B S hS).map v)
          (clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk) := by
    refine (congrArg (fun m => ((relativeProjRepresentableByFunctorUnconditional (Â Z f)).homEquiv
      m).val _ hW' ((BigFppfOver.toScheme B S hS).map v)) hs'3).trans ?_
    refine (congrArg (fun y => Scheme.QcExtension.val y _ hW' ((BigFppfOver.toScheme B S hS).map v))
      (Functor.RepresentableBy.homEquiv_comp _ _ _)).trans ?_
    refine (congrArg (fun y => (Scheme.QcExtension.pullback _ (Scheme.topIso _).inv y).val _ hW'
      ((BigFppfOver.toScheme B S hS).map v)) (homEquiv_classifyingMorphism _ _)).trans ?_
    exact F.pullback_comp _ _ _
  refine Sigma.ext ?_ ?_
  · change yoneda.map v ≫ yoneda.map (s' ≫ projHom Â f (hc Z f)) ≫ f = _
    simp only [hs'2, Functor.map_comp, Category.assoc]
  · exact ρ.fibreOfF_heq f rfl rfl (homEquiv_val_fst _ _ _ _ _)
      ((pullback_clauseTwoClass_fst ψ _ _ hk).trans
        ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Functor.map_comp _ _ _).symm))
      (by rw [hs'2]) (by simp only [hs'2, Functor.map_comp, Category.assoc]) hval

/-- **Clause (2)(b) of Stacks 0D2Z on the functor of quadruples of a restriction datum, for a
quasi-compact `W`**, where the value of the functor is the set of classes of quadruples. -/
theorem quadrupleSpaceEquivF_invertibleMorphism
    {W : BigFppfOver B S hS} (w : W ⟶ Z) {k : ℕ} (hk : 0 < k)
    [hε : Epi ((ψ.pullback ((BigFppfOver.toScheme B S hS).map w)).app (k : ℤ))]
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) :
    ρ.quadrupleSpaceEquivF hc hX W hW
        (yonedaEquiv ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ w
          ((ρ.quadrupleRelativeProjPoints hc hX).mem_subspaceOfOpens_of_epi ψ w hk) ≫
            (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ)) =
      ⟨yoneda.map w ≫ f,
        ρ.fibreOfF f w (yoneda.map w ≫ f) rfl
          (clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk)
          ((clauseTwoClass_fst ψ _ hk).trans (Category.comp_id _))⟩ := by
  change (ρ.quadrupleSpaceEquiv hc hX W _).val W hW (𝟙 W) = _
  rw [ρ.quadrupleSpaceEquiv_invertibleMorphism_val hc hX ψ w hk W hW (𝟙 W)]
  have key : ∀ (t : W ⟶ Z) (_ : t = w)
      (ζ : F ((GradedAlgebraPoints.ofQuasicoherentFamily Â).algebra Z f)
        ((BigFppfOver.toScheme B S hS).obj W))
      (_ : ζ = clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk)
      (h1 : ζ.1 = (BigFppfOver.toScheme B S hS).map t)
      (h2 : (clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk).1 =
        (BigFppfOver.toScheme B S hS).map w),
      (⟨yoneda.map t ≫ f, ρ.fibreOfF f t (yoneda.map t ≫ f) rfl ζ h1⟩ :
          (GradedAlgebraPoints.ofQuasicoherentFamily Â).F W) =
        ⟨yoneda.map w ≫ f, ρ.fibreOfF f w (yoneda.map w ≫ f) rfl
          (clauseTwoClass ψ ((BigFppfOver.toScheme B S hS).map w) hk) h2⟩ := by
    rintro t rfl ζ rfl h1 h2
    rfl
  exact key _ (Category.id_comp w) _
    ((congrArg (fun g => F.pullback g _) (CategoryTheory.Functor.map_id _ _)).trans
      (F.pullback_id _)) _ _

end GradedAlgebraRestriction

/-! ### Clause (2)(b) on the relative Proj of Situation 0849 -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) {X : BigFppfOver s.site s.base s.containsBase}
    {f : yoneda.obj X ⟶ s.space.1}
    {L : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X))
      (situationAlgebra (s.relativeProjPoints.algebra X f)) 1 L)

/-- **Clause (2)(b) of Stacks 0D2Z on the constructed relative Proj, for an arbitrary scheme
`W ⟶ X`.**

Let `F = Proj_Y(𝒜)` be the functor of quadruples of Stacks 084A of Situation 0849, constructed as
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`, and let
`r_{ℒ,ψ} : U(ψ) ⟶ F` be the morphism of Stacks 0D2Z for a homomorphism of graded algebras
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` on a scheme `f : X ⟶ Y`. For `k ≥ 1` and a scheme `w : W ⟶ X`
over which `ψ|_W` is surjective in degree `k`, the composite `W ⟶ U(ψ) ⟶ F` is the morphism given
by the construction of `F`: the point of `F(W)` it defines records, at every quasi-compact test
object `v : W' ⟶ W`, the point of `F(W')` over `f ∘ w ∘ v` given by the class of the pullback
along `v` of the quadruple `(k, w, (w^*ℒ)^{⊗ k}, ψ^{(k)}|_W)`, transported from the algebra
`(w ∘ v)^*(f^*𝒜)` to the algebra `(f ∘ w ∘ v)^*𝒜` along the comparison of the restriction datum
of the situation. -/
@[stacks 0D2Z "variant: clause (2)(b) read on the functor of \
quadruples of Tag 084A at every quasi-compact W' -> W; the tag is \
AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem quadrupleSpaceEquiv_invertibleMorphism_val
    {W : BigFppfOver s.site s.base s.containsBase} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map w)).app (k : ℤ))]
    (W' : BigFppfOver s.site s.base s.containsBase)
    (hW' : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W'))
    (v : W' ⟶ W) :
    (s.quadrupleRestriction.quadrupleSpaceEquiv s.shrink.contains_relativeProj_pointAlgebra
        s.space.property.isSheaf W
        (yonedaEquiv (s.relativeProjPoints.locusFactor ψ w
          (s.relativeProjPoints.mem_subspaceOfOpens_of_epi ψ w hk) ≫
            s.relativeProjPoints.invertibleMorphism ψ))).val W' hW' v =
      ⟨yoneda.map (v ≫ w) ≫ f,
        s.quadrupleRestriction.fibreOfF f (v ≫ w) (yoneda.map (v ≫ w) ≫ f) rfl
          (F.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map v)
            (clauseTwoClass ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map w) hk))
          ((pullback_clauseTwoClass_fst ψ _ _ hk).trans
            ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Functor.map_comp _ _ _).symm))⟩ :=
  s.quadrupleRestriction.quadrupleSpaceEquiv_invertibleMorphism_val
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf ψ w hk
    (hε := by assumption) W' hW' v

/-- **Clause (2)(b) of Stacks 0D2Z on the constructed relative Proj, for a quasi-compact scheme
`W ⟶ X`.** There the value `F(W)` of the functor of quadruples is the set of classes of quadruples
over `W` (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctorEquivF`), and the
point of `W ⟶ U(ψ) ⟶ Proj_Y(𝒜)` is the class of the quadruple
`(k, w, (w^*ℒ)^{⊗ k}, ψ^{(k)}|_W)`, transported from `w^*(f^*𝒜)` to `(f ∘ w)^*𝒜` along the
comparison of the restriction datum. -/
theorem relativeProjFunctorEquivF_invertibleMorphism
    {W : BigFppfOver s.site s.base s.containsBase} (w : W ⟶ X) {k : ℕ} (hk : 0 < k)
    [Epi ((ψ.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map w)).app (k : ℤ))]
    (hW : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)) :
    s.relativeProjFunctorEquivF W hW
        (yonedaEquiv (s.relativeProjPoints.locusFactor ψ w
          (s.relativeProjPoints.mem_subspaceOfOpens_of_epi ψ w hk) ≫
            s.relativeProjPoints.invertibleMorphism ψ)) =
      ⟨yoneda.map w ≫ f,
        s.quadrupleRestriction.fibreOfF f w (yoneda.map w ≫ f) rfl
          (clauseTwoClass ψ ((BigFppfOver.toScheme s.site s.base s.containsBase).map w) hk)
          ((clauseTwoClass_fst ψ _ hk).trans (Category.comp_id _))⟩ :=
  s.quadrupleRestriction.quadrupleSpaceEquivF_invertibleMorphism
    s.shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf ψ w hk
    (hε := by assumption) hW

end RelativeProjSituation

end AlgebraicGeometry.Space

end
