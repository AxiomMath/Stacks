module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TargetChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaSquareAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleMorphismQuadruple

/-!
# Clause (3) of Stacks 0D2Z for an arbitrary commutative square

[Stacks, Tag 0D2Z] attaches to a morphism `f : X ⟶ Y` towards an algebraic space `Y` carrying a
quasi-coherent graded algebra `𝒜`, an invertible `𝒪_X`-module `ℒ` and a homomorphism of graded
algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` the open `U(ψ) ⊆ X` and a morphism
`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` over `Y`.  Its clause (3) reads:

> Consider a commutative diagram
> ```
>  X' --g'--> X
>  |f'        |f
>  v          v
>  Y' --g---> Y
> ```
> where `X'` and `Y'` are schemes, set `𝒜' = g^*𝒜` and `ℒ' = (g')^*ℒ` and denote
> `ψ' : (f')^*𝒜 ⟶ ⨁_{d ≥ 0} (ℒ')^{⊗ d}` the pullback of `ψ`.  Let `U(ψ')`, `r_{ψ',ℒ'}` and `θ'` be
> the open, morphism and homomorphism constructed in Constructions, Lemma 01O9.  Then
> `U(ψ') = (g')^{-1}(U(ψ))` and `r_{ψ',ℒ'}` agrees with the base change of `r_{ψ,ℒ}` via the
> isomorphism `Proj_{Y'}(𝒜') = Y' ×_Y Proj_Y(𝒜)` of Lemma 085C.  Moreover, `θ'` is the pullback
> of `θ`.

This file proves the three assertions for an **arbitrary** such square, on the relative Proj
that the library constructs (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`,
Situation 0849), with `X` a scheme as in the rest of the 0D2Z development.

## The pullback `ψ'`

`ψ'` is a map out of `(f')^*𝒜' = (f')^*(g^*𝒜)`: in the library a
`…RelativeProjQcohSheaf.Twisting (f') (g^*𝒜) 1 ℒ'`, to which [Stacks, Tag 01O9] over the base
`Y'` applies.  It is the inverse image `(g')^*ψ : (g')^*(f^*𝒜) ⟶ ⨁ (ℒ')^{⊗ d}` read through the
canonical identifications

  `(f')^*(g^*𝒜) ≅ (g ∘ f')^*𝒜 = (f ∘ g')^*𝒜 ≅ (g')^*(f^*𝒜)`

of the restriction datum of the situation (`…GradedAlgebraRestriction.restrict`, the comparison
`(f ∘ τ)^*𝒜 ≅ τ^*(f^*𝒜)` of Stacks 084A), together with the identification
`(f')^*(𝒜') ⟶ ⨁ ⋯` over `f'` ↔ `(f')^*(𝒜')` over the identity of `X'` of [Stacks, Tag 01NT]:
`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting`.

## The proof

The identification `Proj_{Y'}(g^*𝒜) = Y' ×_Y Proj_Y(𝒜)` is the second assertion of Stacks 084B
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`, through which Stacks 085C is
proved for scheme points), and "agrees with the base change of `r_{ψ,ℒ}`" means: for every test
scheme `t : T ⟶ X'` of `U(ψ')`, the `T`-point of `Y' ×_Y Proj_Y(𝒜)` with components `f' ∘ t` and
`r_{ψ,ℒ} ∘ g' ∘ t` is, read in `Proj_{Y'}(g^*𝒜)`, the composite `T ⟶ U(ψ') ⟶ Proj_{Y'}(g^*𝒜)`.

Both scheme points `g ∘ f'` and `f ∘ g'` of `Y` are the same point `e` of `X'`, and the third
assertion of Stacks 084B (`…isPullback_projComparison`) identifies the base changes of
`Proj_Y(𝒜)` to `X'` along the two ways round the square with `Proj_{X'}(e^*𝒜)`, through the
comparison `Proj_{X'}(e^*𝒜) ≅ Proj_{X'}(h^*(z^*𝒜)) ⟶ Proj_Z(z^*𝒜)` for `(h, z) = (f', g)` and
`(g', f)` (`…pointEquivProjOver_comp_eq`, `…eq_pointEquivProjOver_of_comp_eq`).  On the side of
the morphisms, `r_{ψ',ℒ'}` and `r_{ψ,ℒ} ∘ g'` are compared with the morphism of [Stacks, Tag 01O9]
for `ψ` read over `X'` itself, by the behaviour of Tag 01O9 under a change of the target
(`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/TargetChange.lean`) and under base
change of the source (`…coveringOpenPullback_globalMorphism`).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.coveringOpen_squareTwisting`:
  **`U(ψ') = (g')^{-1}(U(ψ))`**.
* `AlgebraicGeometry.Space.RelativeProjSituation.invertibleMorphism_baseChange_square`:
  **`r_{ψ',ℒ'}` is the base change of `r_{ψ,ℒ}`** through `Proj_{Y'}(g^*𝒜) = Y' ×_Y Proj_Y(𝒜)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.invertibleTheta_baseChange_square`:
  **`θ'` is the pullback of `θ`**: `θ' = j^*θ` for the restriction `j : U(ψ') ⟶ U(ψ)` of `g'`,
  through the identifications `…GradedAlgebraRestriction.squareThetaSourceIso` and
  `…GradedAlgebraRestriction.squareThetaTargetIso`.
* `AlgebraicGeometry.Space.RelativeProjPoints.invertibleTheta_unique`: at the scheme point `f`,
  **`θ` is characterized by clause (1)** (the uniqueness half of `…invertibleTheta_clauseOne`).

## The map `θ'`

Both `θ'` and `j^*θ` are compared with the map `θ` of [Stacks, Tag 01O9] for `ψ` read over `X'`
itself at the point `e = g ∘ f' = f ∘ g'` (`…squareTwistingAtPoint`, over `Proj_{X'}(e^*𝒜)`):
`ψ'` is the change of the target of that map along `f'`, and changing its target along `g'`
gives back `(g')^*ψ` (`…squareTargetChangeZ_eq`).  The comparison of `θ` under a change of the
target (`…RelativeProjInvertibleMorphism.theta_changeTarget`), used twice, and under base change
of the source (`…RelativeProjInvertibleMorphism.theta_pullback`), are assembled by
`…RelativeProjInvertibleMorphism.eq_squareChainIso`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.AlgebraicGeometry.GluedTwistAlgebra (twistDataOfGradedAlgebra)

universe u m

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

variable {T X : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  {d : ℤ} {f : T ⟶ X} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **Transporting along a unital isomorphism and then along its inverse does nothing**, the
other composite of `…Twisting.algebraTransport_algebraTransport_unitalHomInverse`. -/
theorem algebraTransport_unitalHomInverse_algebraTransport
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
    (ψ : Twisting f B d L) :
    algebraTransport (unitalHomInverse Φ hΦ) (algebraTransport Φ ψ) = ψ := by
  refine Twisting.ext fun i => ?_
  have := hΦ (i * d)
  show (pullbackFunctor (ringedSpaceHom f)).map (inv (Φ.app (i * d))) ≫
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ ψ.app i = ψ.app i
  rw [← CategoryTheory.Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)

/-! ### The fibre identifications of Stacks 084B at two scheme points -/

/-- **The fibre identification at a restricted point, through the comparison of Stacks 084B.**
For `h : Z' ⟶ Z`, a scheme point `z` of `X` and a `T`-point `u` of `F` over `(z ∘ h) ∘ r`, the
`T`-point of `Proj_Z(z^*𝒜)` over `h ∘ r` attached to `u` is the one of `Proj_{Z'}((z ∘ h)^*𝒜)`
over `r` followed by the comparison morphism. -/
theorem pointEquivProjOver_comp {Z Z' T : BigFppfOver B S hS} (h : Z' ⟶ Z)
    (z : yoneda.obj Z ⟶ X) (r : T ⟶ Z') (u : yoneda.obj T ⟶ ρ.quadrupleSpace hc hX)
    (hu : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map r ≫ (yoneda.map h ≫ z))
    (hu' : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (r ≫ h) ≫ z) :
    ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z z (r ≫ h) ⟨u, hu'⟩).1 =
      ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' (yoneda.map h ≫ z) r
          ⟨u, hu⟩).1 ≫
        (BigFppfOver.toScheme B S hS).map (ρ.projComparison hc z h) := by
  let s := (ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver Z' (yoneda.map h ≫ z) r ⟨u, hu⟩
  have hw : ρ.projComparison hc z h ≫ projHom Â z (hc Z z) =
      projHom Â (yoneda.map h ≫ z) (hc Z' _) ≫ h :=
    (ρ.isPullback_projComparison hc z h).1.w
  have hs : (s.1 ≫ ρ.projComparison hc z h) ≫
      (ρ.quadrupleRelativeProjPoints hc hX).fibreHom Z z = r ≫ h :=
    (Category.assoc _ _ _).trans ((congrArg (s.1 ≫ ·) hw).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) s.2)))
  have hval : u = yoneda.map (s.1 ≫ ρ.projComparison hc z h) ≫
      ρ.projToQuadrupleSpace hc hX z :=
    ((ρ.quadrupleRelativeProjPoints hc hX).map_pointEquivOver Z' (yoneda.map h ≫ z) r
      ⟨u, hu⟩).symm.trans
      ((congrArg (yoneda.map s.1 ≫ ·) (ρ.projToQuadrupleSpace_comp hc hX z h).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ ρ.projToQuadrupleSpace hc hX z) (yoneda.map_comp _ _).symm)))
  have key : (ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver Z z (r ≫ h) ⟨u, hu'⟩ =
      ⟨s.1 ≫ ρ.projComparison hc z h, hs⟩ :=
    (Equiv.eq_symm_apply _).1 (Subtype.ext hval)
  refine (congrArg (fun w => (BigFppfOver.toScheme B S hS).map w.1 ≫ 𝟙 _) key).trans ?_
  exact (Category.comp_id _).trans ((CategoryTheory.Functor.map_comp _ _ _).trans
    (congrArg (· ≫ _) (Category.comp_id _).symm))

/-- **The fibre identification at a restricted point, through the canonical morphism.**  The
same statement with the comparison written as the identification
`Proj_{Z'}(z'^*𝒜) ≅ Proj_{Z'}(h^*(z^*𝒜))` of the restriction datum followed by the base-change
morphism of Tag 01O3, for an arbitrary spelling `z'` of the point `z ∘ h`. -/
theorem pointEquivProjOver_comp_eq {Z Z' T : BigFppfOver B S hS} (h : Z' ⟶ Z)
    (z : yoneda.obj Z ⟶ X) (z' : yoneda.obj Z' ⟶ X) (hz : yoneda.map h ≫ z = z') (r : T ⟶ Z')
    (u : yoneda.obj T ⟶ ρ.quadrupleSpace hc hX)
    (hu : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map r ≫ z')
    (hu' : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (r ≫ h) ≫ z) :
    ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z z (r ≫ h) ⟨u, hu'⟩).1 =
      ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' z' r ⟨u, hu⟩).1 ≫
        (relativeProjCongr (A₁ := Â Z' z')
          (A₂ := (Â Z z).pullback ((BigFppfOver.toScheme B S hS).map h))
          (ρ.restrict h z z' hz) (ρ.isIso_restrict_app h z z' hz)).hom ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z z)
            ((BigFppfOver.toScheme B S hS).map h) := by
  subst hz
  rw [ρ.pointEquivProjOver_comp hc hX h z r u hu hu', ρ.toScheme_map_projComparison hc z h]
  rfl

/-- **A section over the restricted point is determined by its image.**  A `T`-point `m` of
`Proj_{Z'}(z'^*𝒜)` over `r` whose image in `Proj_Z(z^*𝒜)` is the point attached to `u` is the
point attached to `u`. -/
theorem eq_pointEquivProjOver_of_comp_eq {Z Z' T : BigFppfOver B S hS} (h : Z' ⟶ Z)
    (z : yoneda.obj Z ⟶ X) (z' : yoneda.obj Z' ⟶ X) (hz : yoneda.map h ≫ z = z') (r : T ⟶ Z')
    (u : yoneda.obj T ⟶ ρ.quadrupleSpace hc hX)
    (hu : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map r ≫ z')
    (hu' : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (r ≫ h) ≫ z)
    (m : (BigFppfOver.toScheme B S hS).obj T ⟶ (relativeProj (Â Z' z')).scheme)
    (hm : m ≫ (relativeProj (Â Z' z')).toBase = (BigFppfOver.toScheme B S hS).map r)
    (he : m ≫ (relativeProjCongr (A₁ := Â Z' z')
          (A₂ := (Â Z z).pullback ((BigFppfOver.toScheme B S hS).map h))
          (ρ.restrict h z z' hz) (ρ.isIso_restrict_app h z z' hz)).hom ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z z)
            ((BigFppfOver.toScheme B S hS).map h) =
      ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z z (r ≫ h) ⟨u, hu'⟩).1) :
    m = ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' z' r ⟨u, hu⟩).1 := by
  let v := ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' z' r).symm ⟨m, hm⟩
  have hv : ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' z' r v).1 = m :=
    congrArg Subtype.val (((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z' z'
      r).apply_symm_apply _)
  have hv' : v.1 ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (r ≫ h) ≫ z := by
    rw [v.2, ← hz, CategoryTheory.Functor.map_comp, Category.assoc]
  have key := ρ.pointEquivProjOver_comp_eq hc hX h z z' hz r v.1 v.2 hv'
  have key' := key.trans ((congrArg (fun w => w ≫ _) hv).trans he)
  have h1 : (⟨v.1, hv'⟩ : {w : yoneda.obj T ⟶ ρ.quadrupleSpace hc hX //
      w ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (r ≫ h) ≫ z}) = ⟨u, hu'⟩ :=
    ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z z (r ≫ h)).injective
      (Subtype.ext key')
  have h2 : v = ⟨u, hu⟩ := Subtype.ext (show v.1 = u from congrArg Subtype.val h1)
  rw [← hv, h2]

/-! ### The pullback `ψ'` of `ψ` to a commutative square -/

variable {Z : BigFppfOver B S hS} {f : yoneda.obj Z ⟶ X}
    {L : ((BigFppfOver.toScheme B S hS).obj Z).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj Z))
      (situationAlgebra ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) 1 L)
    {X' Y' : BigFppfOver B S hS} (g : yoneda.obj Y' ⟶ X) (f' : X' ⟶ Y') (g' : X' ⟶ Z)
    (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f)

/-- `(g')^*ψ`, read over the identity of `X'` as a map out of `(g')^*(f^*𝒜)` (Tag 01NT). -/
def squarePullbackDown :
    Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X'))
      (baseAlgebra ((BigFppfOver.toScheme B S hS).map g') (situationAlgebra (Â Z f))) 1
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map g'))).obj L) :=
  Twisting.baseChangeDown ((BigFppfOver.toScheme B S hS).map g')
    (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Z f)) 1
    (Twisting.congrBase (comp_id_eq_id_comp g') (ψ.pullback ((BigFppfOver.toScheme B S hS).map g')))

/-- **`(g')^*ψ` as a map out of the restriction of `𝒜` to the point `g ∘ f' = f ∘ g'` of `X'`.**
It is `squarePullbackDown` transported along the comparison `(f ∘ g')^*𝒜 ≅ (g')^*(f^*𝒜)` of the
restriction datum. -/
def squareTwistingAtPoint :
    Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X'))
      (situationAlgebra (Â X' (yoneda.map f' ≫ g))) 1
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map g'))).obj L) :=
  Twisting.algebraTransport (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
    (ρ.squarePullbackDown hc hX ψ g')

/-- **The pullback `ψ' : (f')^*(g^*𝒜) ⟶ ⨁_d ((g')^*ℒ)^{⊗ d}` of `ψ` to the square of clause (3)
of Stacks 0D2Z**, as a map over `f' : X' ⟶ Y'` for the restriction `g^*𝒜` of `𝒜` to the scheme
point `g`: the inverse image `(g')^*ψ` read through
`(f')^*(g^*𝒜) ≅ (g ∘ f')^*𝒜 = (f ∘ g')^*𝒜 ≅ (g')^*(f^*𝒜)` (the comparisons of the restriction
datum) and through the identification of Tag 01NT between maps over `f'` and over the identity
of `X'`. -/
def squareTwisting :
    Twisting ((BigFppfOver.toScheme B S hS).map f') (situationAlgebra (Â Y' g)) 1
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map g'))).obj L) :=
  Twisting.congrBase (Category.id_comp _)
    (Twisting.baseChangeUp ((BigFppfOver.toScheme B S hS).map f')
      (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Y' g)) 1
      (Twisting.algebraTransport
        (unitalHomInverse (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
          (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl))
        (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)))

/-- If `t ⁻¹ᵁ V = ⊤` and `U = V`, then `t ⁻¹ᵁ U = ⊤`. -/
private theorem preimage_eq_top_of_eq {P Q : Scheme.{u}} (t : P ⟶ Q) {U V : Q.Opens} (h : U = V)
    (hV : t ⁻¹ᵁ V = ⊤) : t ⁻¹ᵁ U = ⊤ :=
  h ▸ hV

/-- Changing the base of `squarePullbackDown` along `g'` gives back `(g')^*ψ`. -/
private theorem baseChangeUp_squarePullbackDown :
    Twisting.baseChangeUp ((BigFppfOver.toScheme B S hS).map g')
      (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Z f)) 1
      (ρ.squarePullbackDown hc hX ψ g') =
    Twisting.congrBase (comp_id_eq_id_comp g')
      (ψ.pullback ((BigFppfOver.toScheme B S hS).map g')) :=
  (Twisting.baseChangeEquiv ((BigFppfOver.toScheme B S hS).map g')
    (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Z f)) 1).right_inv _

/-! ### The open: `U(ψ') = (g')^{-1}(U(ψ))` -/

/-- The open of `squarePullbackDown` is `U((g')^*ψ)`. -/
theorem coveringOpen_squarePullbackDown :
    (toGradedPowerMap (A := (Â Z f).pullback ((BigFppfOver.toScheme B S hS).map g'))
        (ρ.squarePullbackDown hc hX ψ g')).coveringOpen =
      (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).coveringOpen := by
  refine (coveringOpen_baseChangeUp (B := Â Z f) ((BigFppfOver.toScheme B S hS).map g')
    (ρ.squarePullbackDown hc hX ψ g')).symm.trans ?_
  refine (congrArg (fun χ => (toGradedPowerMap χ).coveringOpen)
    (ρ.baseChangeUp_squarePullbackDown hc hX ψ g')).trans ?_
  exact coveringOpen_congrBase _ _

/-- The open of `squareTwistingAtPoint` is `U((g')^*ψ)`. -/
theorem coveringOpen_squareTwistingAtPoint :
    (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).coveringOpen =
      (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).coveringOpen :=
  (coveringOpen_algebraTransport (A₁ := Â X' (yoneda.map f' ≫ g))
    (A₂ := (Â Z f).pullback ((BigFppfOver.toScheme B S hS).map g'))
    (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
    (ρ.isIso_restrict_app g' f _ hsq.symm) (ρ.squarePullbackDown hc hX ψ g')).trans
    (ρ.coveringOpen_squarePullbackDown hc hX ψ g')

/-- **`U(ψ') = (g')^{-1}(U(ψ))`**, the first assertion of clause (3) of Stacks 0D2Z, for the
functor of quadruples of a restriction datum. -/
theorem coveringOpen_squareTwisting :
    (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen =
      (BigFppfOver.toScheme B S hS).map g' ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
  refine (coveringOpen_congrBase _ _).trans ?_
  refine (coveringOpen_baseChangeUp (B := Â Y' g) ((BigFppfOver.toScheme B S hS).map f') _).trans
    ?_
  refine (coveringOpen_algebraTransport
    (A₁ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f'))
    (A₂ := Â X' (yoneda.map f' ≫ g)) _ (isIso_unitalHomInverse_app _ _) _).trans ?_
  refine (ρ.coveringOpen_squareTwistingAtPoint hc hX ψ g f' g' hsq).trans ?_
  exact coveringOpen_pullback ψ _

/-! ### The morphism -/

/-- **The morphism of `squareTwistingAtPoint`, followed by the comparison at `f`, is `r_{ℒ,ψ}`
restricted along `g'`.** -/
theorem lift_globalMorphism_squareTwistingAtPoint {T : BigFppfOver B S hS} (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS Z (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t)
        ((congrArg (fun U => (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ U)
          (ρ.coveringOpen_squareTwistingAtPoint hc hX ψ g f' g' hsq)).trans
          ((ρ.quadrupleRelativeProjPoints hc hX).preimage_coveringOpen_pullback_eq_top ψ g' t
            ht)) ≫
        (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).globalMorphism
          (relativeProj (Â X' (yoneda.map f' ≫ g))) ≫
        (relativeProjCongr (A₁ := Â X' (yoneda.map f' ≫ g))
          (A₂ := (Â Z f).pullback ((BigFppfOver.toScheme B S hS).map g'))
          (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (ρ.isIso_restrict_app g' f _ hsq.symm)).hom ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Z f)
          ((BigFppfOver.toScheme B S hS).map g') =
      (ρ.quadrupleRelativeProjPoints hc hX).locusLift ψ (t ≫ g') ht ≫
        (toGradedPowerMap ψ).globalMorphism
          (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) := by
  have hU : ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ
    (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).coveringOpen
      = ⊤ := (ρ.quadrupleRelativeProjPoints hc hX).preimage_coveringOpen_pullback_eq_top ψ g' t ht
  have hbcd : ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ (toGradedPowerMap (A := (Â Z f).pullback
      ((BigFppfOver.toScheme B S hS).map g')) (ρ.squarePullbackDown hc hX ψ g')).coveringOpen = ⊤ :=
    preimage_eq_top_of_eq _ (ρ.coveringOpen_squarePullbackDown hc hX ψ g') hU
  -- the transport along the comparison at `f`
  have s1 := lift_globalMorphism_algebraTransport (A₁ := Â X' (yoneda.map f' ≫ g))
    (A₂ := (Â Z f).pullback ((BigFppfOver.toScheme B S hS).map g'))
    (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
    (ρ.isIso_restrict_app g' f _ hsq.symm) (ρ.squarePullbackDown hc hX ψ g')
    ((BigFppfOver.toScheme B S hS).map t) hbcd
  -- the base change along `g'`
  have s2 := lift_globalMorphism_baseChangeUp (B := Â Z f) ((BigFppfOver.toScheme B S hS).map g')
    (ρ.squarePullbackDown hc hX ψ g') ((BigFppfOver.toScheme B S hS).map t) hbcd
  have s3 := lift_globalMorphism_congr (ρ.baseChangeUp_squarePullbackDown hc hX ψ g')
    ((BigFppfOver.toScheme B S hS).map t)
    (preimage_eq_top_of_eq _ (coveringOpen_baseChangeUp (B := Â Z f)
      ((BigFppfOver.toScheme B S hS).map g') (ρ.squarePullbackDown hc hX ψ g')) hbcd)
  have s4 := lift_globalMorphism_congrBase (comp_id_eq_id_comp g')
    (ψ.pullback ((BigFppfOver.toScheme B S hS).map g')) ((BigFppfOver.toScheme B S hS).map t) hU
  -- the base change of the source along `g'`
  have s5 : liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t) hU ≫
      (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).globalMorphism
        (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) =
      (ρ.quadrupleRelativeProjPoints hc hX).locusLift ψ (t ≫ g') ht ≫
        (toGradedPowerMap ψ).globalMorphism
          (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) := by
    rw [← coveringOpenPullback_globalMorphism, ← Category.assoc]
    congr 1
    rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι, RelativeProjPoints.locusLift_ι,
      Category.assoc, coveringOpenPullback_ι, liftOfPreimageEqTop_ι_assoc,
      CategoryTheory.Functor.map_comp]
  have s1' := eq_whisker s1 (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
    (Â Z f) ((BigFppfOver.toScheme B S hS).map g'))
  simp only [Category.assoc] at s1'
  exact s1'.trans (s2.trans (s3.symm.trans (s4.trans s5)))

/-- **The morphism of `ψ'`, read through the comparison at `g`, is the morphism of
`squareTwistingAtPoint`.** -/
theorem lift_globalMorphism_squareTwisting {T : BigFppfOver B S hS} (t : T ⟶ X')
    (ht : (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ
      (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t) ht ≫
        (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).globalMorphism
          (relativeProj (Â X' (yoneda.map f' ≫ g))) ≫
        (relativeProjCongr (A₁ := Â X' (yoneda.map f' ≫ g))
          (A₂ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f'))
          (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
          (ρ.isIso_restrict_app f' g _ rfl)).hom ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Y' g)
          ((BigFppfOver.toScheme B S hS).map f') =
      liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t)
          ((congrArg (fun U => (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ U)
            ((ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).trans
              (ρ.coveringOpen_squareTwistingAtPoint hc hX ψ g f' g' hsq
                |>.trans (coveringOpen_pullback ψ _)).symm)).trans ht) ≫
        (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
          (relativeProj (Â Y' g)) := by
  let R1 := ρ.restrict f' g (yoneda.map f' ≫ g) rfl
  let χY := Twisting.algebraTransport
    (unitalHomInverse R1 (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl))
    (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)
  have hχ : ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ (toGradedPowerMap (A := (Â Y' g).pullback
      ((BigFppfOver.toScheme B S hS).map f')) χY).coveringOpen = ⊤ :=
    preimage_eq_top_of_eq _ (coveringOpen_algebraTransport
      (A₁ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f'))
      (A₂ := Â X' (yoneda.map f' ≫ g)) _ (isIso_unitalHomInverse_app _ _) _) ht
  have hinv := Twisting.algebraTransport_algebraTransport_unitalHomInverse R1
    (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
    (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)
  -- the transport along the comparison at `g`
  have s1 := lift_globalMorphism_algebraTransport (A₁ := Â X' (yoneda.map f' ≫ g))
    (A₂ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f')) R1
    (ρ.isIso_restrict_app f' g _ rfl) χY ((BigFppfOver.toScheme B S hS).map t) hχ
  have s0 := lift_globalMorphism_congr hinv ((BigFppfOver.toScheme B S hS).map t)
    (preimage_eq_top_of_eq _ (coveringOpen_algebraTransport
      (A₁ := Â X' (yoneda.map f' ≫ g))
      (A₂ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f')) R1
      (ρ.isIso_restrict_app f' g _ rfl) χY) hχ)
  -- the base change along `f'`
  have s2 := lift_globalMorphism_baseChangeUp (B := Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
    χY ((BigFppfOver.toScheme B S hS).map t) hχ
  have s3 := lift_globalMorphism_congrBase (Category.id_comp _)
    (Twisting.baseChangeUp ((BigFppfOver.toScheme B S hS).map f')
      (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Y' g)) 1 χY)
    ((BigFppfOver.toScheme B S hS).map t)
    (preimage_eq_top_of_eq _ (coveringOpen_baseChangeUp (B := Â Y' g)
      ((BigFppfOver.toScheme B S hS).map f') χY) hχ)
  have s1' := eq_whisker s1 (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
    (Â Y' g) ((BigFppfOver.toScheme B S hS).map f'))
  simp only [Category.assoc] at s1'
  have s0' := eq_whisker s0 ((relativeProjCongr (A₁ := Â X' (yoneda.map f' ≫ g))
          (A₂ := (Â Y' g).pullback ((BigFppfOver.toScheme B S hS).map f')) R1
          (ρ.isIso_restrict_app f' g _ rfl)).hom ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (Â Y' g)
          ((BigFppfOver.toScheme B S hS).map f'))
  simp only [Category.assoc] at s0'
  exact s0'.trans (s1'.trans (s2.trans s3.symm))

include hsq in
/-- The point `r_{ℒ,ψ} ∘ g' ∘ t` of `F` lies over `g ∘ f' ∘ t`. -/
theorem locusFactor_invertibleMorphism_comp_π {T : BigFppfOver B S hS} (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS Z (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ (t ≫ g') ht ≫
        (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ) ≫ ρ.quadrupleSpaceπ hc hX =
      yoneda.map (t ≫ f') ≫ g := by
  rw [Category.assoc, RelativeProjPoints.invertibleMorphism_comp_π, ← Category.assoc,
    RelativeProjPoints.locusFactor_ι, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hsq]

/-- A test scheme of `U(ψ)` through `g'` is a test scheme of `U(ψ')`. -/
theorem preimage_coveringOpen_squareTwisting_eq_top {T : BigFppfOver B S hS} (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS Z (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ
      (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen = ⊤ :=
  preimage_eq_top_of_eq _ ((ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).trans
      (coveringOpen_pullback ψ _).symm)
    ((ρ.quadrupleRelativeProjPoints hc hX).preimage_coveringOpen_pullback_eq_top ψ g' t ht)

/-- **Clause (3) of Stacks 0D2Z for the morphism, for an arbitrary commutative square, on the
functor of quadruples of a restriction datum.**  For every test scheme `t : T ⟶ X'` of
`U(ψ') = (g')^{-1}(U(ψ))`, the `T`-point of `Y' ×_Y F` with components `f' ∘ t` and
`r_{ℒ,ψ} ∘ g' ∘ t`, read in `Proj_{Y'}(g^*𝒜)` through the identification of Stacks 084B, is
`T ⟶ U(ψ') ⟶ Proj_{Y'}(g^*𝒜)`, the second arrow being `r_{ℒ',ψ'}` of Tag 01O9. -/
theorem invertibleMorphism_baseChange_square {T : BigFppfOver B S hS} (t : T ⟶ X')
    (ht : t ≫ g' ∈ (subspaceOfOpens B S hS Z (toGradedPowerMap ψ).coveringOpen).obj (op T)) :
    ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Y' g (t ≫ f')
        ⟨(ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ (t ≫ g') ht ≫
          (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ,
          ρ.locusFactor_invertibleMorphism_comp_π hc hX ψ g f' g' hsq t ht⟩).1 =
      liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t)
          (ρ.preimage_coveringOpen_squareTwisting_eq_top hc hX ψ g f' g' hsq t ht) ≫
        (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
          (relativeProj (Â Y' g)) := by
  have hu1 : ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ (t ≫ g') ht ≫
        (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ) ≫ ρ.quadrupleSpaceπ hc hX =
      yoneda.map t ≫ (yoneda.map f' ≫ g) := by
    rw [ρ.locusFactor_invertibleMorphism_comp_π hc hX ψ g f' g' hsq t ht,
      CategoryTheory.Functor.map_comp, Category.assoc]
  have hu2 : ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ (t ≫ g') ht ≫
        (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ) ≫ ρ.quadrupleSpaceπ hc hX =
      yoneda.map (t ≫ g') ≫ f := by
    rw [Category.assoc, RelativeProjPoints.invertibleMorphism_comp_π, ← Category.assoc,
      RelativeProjPoints.locusFactor_ι]
  have ht'' : (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ
      (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).coveringOpen = ⊤ :=
    preimage_eq_top_of_eq _ (ρ.coveringOpen_squareTwistingAtPoint hc hX ψ g f' g' hsq)
      ((ρ.quadrupleRelativeProjPoints hc hX).preimage_coveringOpen_pullback_eq_top ψ g' t ht)
  -- the point of `Proj_{Y'}` through the point of `Proj_{X'}` at `g ∘ f'`
  have sA := ρ.pointEquivProjOver_comp_eq hc hX f' g (yoneda.map f' ≫ g) rfl t _ hu1
    (ρ.locusFactor_invertibleMorphism_comp_π hc hX ψ g f' g' hsq t ht)
  -- the point of `Proj_{X'}` at `g ∘ f' = f ∘ g'` is the morphism of `squareTwistingAtPoint`
  have hm : (liftOfPreimageEqTop _ ((BigFppfOver.toScheme B S hS).map t) ht'' ≫
      (toGradedPowerMap (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).globalMorphism
        (relativeProj (Â X' (yoneda.map f' ≫ g)))) ≫
      (relativeProj (Â X' (yoneda.map f' ≫ g))).toBase = (BigFppfOver.toScheme B S hS).map t := by
    rw [Category.assoc, GradedPowerMap.globalMorphism_comp_toBase, GradedPowerMap.toBase,
      liftOfPreimageEqTop_ι_assoc]
    exact Category.comp_id _
  have hpt : (ρ.quadrupleRelativeProjPoints hc hX).locusLift ψ (t ≫ g') ht ≫
      (toGradedPowerMap ψ).globalMorphism
        (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) =
      ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z f (t ≫ g')
        ⟨(ρ.quadrupleRelativeProjPoints hc hX).locusFactor ψ (t ≫ g') ht ≫
          (ρ.quadrupleRelativeProjPoints hc hX).invertibleMorphism ψ, hu2⟩).1 :=
    ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver_invertiblePoint ψ (t ≫ g')
      ht).symm.trans
      (congrArg (fun w => ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivProjOver Z f
        (t ≫ g') w).1)
        (Subtype.ext ((ρ.quadrupleRelativeProjPoints hc hX).locusFactor_invertibleMorphism ψ
          (t ≫ g') ht).symm))
  have he := (Category.assoc _ _ _).trans
    ((ρ.lift_globalMorphism_squareTwistingAtPoint hc hX ψ g f' g' hsq t ht).trans hpt)
  have sB := ρ.eq_pointEquivProjOver_of_comp_eq hc hX g' f (yoneda.map f' ≫ g) hsq.symm t _ hu1
    hu2 _ hm he
  -- the morphism of `ψ'`
  have sC := ρ.lift_globalMorphism_squareTwisting hc hX ψ g f' g' hsq t ht''
  refine sA.trans ?_
  refine (congrArg (fun w => w ≫ _) sB.symm).trans ?_
  exact (Category.assoc _ _ _).trans sC

/-! ### The map `θ`: `θ'` is the pullback of `θ` -/

/-- `ψ'` is the change of the target along `f'` of `squareTwistingAtPoint`, read over
`𝟙 ≫ f' = f'`. -/
theorem squareTwisting_eq_congrBase :
    ρ.squareTwisting hc hX ψ g f' g' hsq =
      Twisting.congrBase (Category.id_comp _)
        (changeTarget (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
          (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
          (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
          (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)) :=
  rfl

/-- `squareTwistingAtPoint` read back over `g'` by the change of the target along `g'`. -/
abbrev squareTargetChangeZ :
    Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X') ≫ (BigFppfOver.toScheme B S hS).map g')
      (situationAlgebra (Â Z f)) 1
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map g'))).obj L) :=
  changeTarget (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
    (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm)
    (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)

/-- **Changing the target of `squareTwistingAtPoint` back along `g'` gives `(g')^*ψ`.** -/
theorem squareTargetChangeZ_eq :
    ρ.squareTargetChangeZ hc hX ψ g f' g' hsq =
      Twisting.congrBase (comp_id_eq_id_comp g')
        (ψ.pullback ((BigFppfOver.toScheme B S hS).map g')) := by
  show Twisting.baseChangeUp ((BigFppfOver.toScheme B S hS).map g')
      (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Z f)) 1
      (Twisting.algebraTransport (unitalHomInverse (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (ρ.isIso_restrict_app g' f _ hsq.symm))
        (Twisting.algebraTransport (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
          (ρ.squarePullbackDown hc hX ψ g'))) = _
  refine (congrArg (Twisting.baseChangeUp ((BigFppfOver.toScheme B S hS).map g')
    (𝟙 ((BigFppfOver.toScheme B S hS).obj X')) (situationAlgebra (Â Z f)) 1)
    (Twisting.algebraTransport_unitalHomInverse_algebraTransport _ _ _)).trans ?_
  exact ρ.baseChangeUp_squarePullbackDown hc hX ψ g'

/-- `U(ψ') = U(squareTargetChangeZ)`: both are `U(squareTwistingAtPoint)`. -/
theorem coveringOpen_squareTwisting_eq_targetChangeZ :
    (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen =
      (toGradedPowerMap (ρ.squareTargetChangeZ hc hX ψ g f' g' hsq)).coveringOpen :=
  (coveringOpen_changeTarget_of_eq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
      (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
      (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
      (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
      (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq)).trans
    (coveringOpen_changeTarget (Â Z f) _ _ _ _).symm

/-- The two ways from `U(ψ')` to `U(squareTwistingAtPoint)` agree. -/
theorem squareTheta_hk :
    Scheme.homOfLE ((BigFppfOver.toScheme B S hS).obj X')
        (ρ.coveringOpen_squareTwisting_eq_targetChangeZ hc hX ψ g f' g' hsq).le ≫
      Scheme.homOfLE ((BigFppfOver.toScheme B S hS).obj X')
        (coveringOpen_changeTarget (Â Z f) _ _ _ (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)).le =
    Scheme.homOfLE ((BigFppfOver.toScheme B S hS).obj X')
        (coveringOpen_changeTarget_of_eq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
          (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
          (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
          (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
          (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq)).le :=
  Scheme.homOfLE_homOfLE _ _ _

/-- The restriction of `g'` to `U(ψ') ⟶ U(ψ)`, through `U(squareTargetChangeZ)`. -/
theorem squareTheta_hj :
    Scheme.homOfLE ((BigFppfOver.toScheme B S hS).obj X')
        (ρ.coveringOpen_squareTwisting_eq_targetChangeZ hc hX ψ g f' g' hsq).le ≫
      coveringOpenPullbackOfEq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
        (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq) =
    Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
      (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
      (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le := by
  rw [← cancel_mono (toGradedPowerMap ψ).coveringOpen.ι]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Scheme.Hom.resLE_comp_ι _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Scheme.homOfLE_ι _ _)).trans ?_
  exact (Scheme.Hom.resLE_comp_ι _ _).symm

/-- **`j^*r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ≅ r_{ℒ',ψ'}^*(⨁_d 𝒪(d))`** for the restriction `j : U(ψ') ⟶ U(ψ)` of
`g'`.  Both sides are identified with the inverse image of the twists of the relative Proj
`Proj_{X'}(e^*𝒜)` at the point `e = g ∘ f' = f ∘ g'` of `X'` along the morphism `r` of
`squareTwistingAtPoint`: through the comparisons of twists along
`Proj_{X'}(e^*𝒜) ⟶ Proj_{Y'}(g^*𝒜)` and along `Proj_{X'}(e^*𝒜) ⟶ Proj_X(f^*𝒜)` of Stacks 084B (3)
(`…thetaChangeSourceIsoOfEq`,
`…thetaChangeSourceIso`), the pseudofunctoriality of the inverse image (`…thetaSourceIsoOfEq`)
and the congruences along the equalities of the morphisms (`…squareChainIso`). -/
def squareThetaSourceIso :
    Stacks.Conormal.gradedPullback
        (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
          (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
          (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)
        (Stacks.Conormal.gradedPullback ((toGradedPowerMap ψ).globalMorphism
          (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)))
          (GradedPowerMap.twD ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)).algebra) ≅
      Stacks.Conormal.gradedPullback ((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g'
          hsq)).globalMorphism (relativeProj (Â Y' g))) (GradedPowerMap.twD (Â Y' g)).algebra :=
  squareChainIso (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
    (thetaChangeSourceIsoOfEq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
      (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
      (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
      (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
      (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq))
    (thetaChangeSourceIso (Â Z f) _ _ _ (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq))
    (thetaSourceIsoOfEq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
      (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq))

/-- **`j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (ℒ')^{⊗ d}|_{U(ψ')}`** for the restriction
`j : U(ψ') ⟶ U(ψ)` of `g'`: the identification `thetaTargetIso` of the pullback along `g'`
(`…thetaTargetIsoOfEq`) and the identifications `…laurentOnHomOfLEIso` along the equal opens,
assembled as `squareThetaSourceIso` is. -/
def squareThetaTargetIso :
    Stacks.Conormal.gradedPullback
        (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
          (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
          (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)
        (laurentOn L (toGradedPowerMap ψ).coveringOpen) ≅
      laurentOn ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map g'))).obj L)
        (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen :=
  squareChainIso (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
    (laurentOnHomOfLEIso _ _) (laurentOnHomOfLEIso _ _)
    (thetaTargetIsoOfEq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
      (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq))

/-- **`θ'` is the pullback of `θ`, for an arbitrary commutative square** (the last assertion of
clause (3) of Stacks 0D2Z, on the functor of quadruples of a restriction datum): `θ'` is
`j^*θ` for the restriction `j : U(ψ') ⟶ U(ψ)` of `g'`, through `squareThetaSourceIso` and
`squareThetaTargetIso`. -/
theorem theta_baseChange_square :
    (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).theta =
      (ρ.squareThetaSourceIso hc hX ψ g f' g' hsq).inv ≫
        pullbackGradedAlgebraMap
          (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
            (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
            (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫
        (ρ.squareThetaTargetIso hc hX ψ g f' g' hsq).hom :=
  eq_squareChainIso (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
    (theta_changeTarget_of_eq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
      (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
      (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
      (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
      (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq))
    (theta_changeTarget (Â Z f) _ _ _ (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq))
    (theta_pullback_of_eq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
      (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq))

end GradedAlgebraRestriction

/-! ### Clause (3) on the relative Proj of Situation 0849 -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) {X : BigFppfOver s.site s.base s.containsBase}
    {f : yoneda.obj X ⟶ s.space.1}
    {L : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj X))
      (situationAlgebra (s.relativeProjPoints.algebra X f)) 1 L)
    {X' Y' : BigFppfOver s.site s.base s.containsBase} (g : yoneda.obj Y' ⟶ s.space.1)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f)

/-- **Clause (3) of Stacks 0D2Z, for the open and the morphism, for an arbitrary commutative
square, on the constructed relative Proj.**

Let `F = Proj_Y(𝒜)` be the relative Proj of Situation 0849, constructed as the functor of
quadruples of Stacks 084A (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`),
`f : X ⟶ Y` a scheme point of the algebraic space `Y`, `ℒ` an invertible `𝒪_X`-module,
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` a homomorphism of graded algebras and
`r_{ℒ,ψ} : U(ψ) ⟶ F` the morphism of Stacks 0D2Z.  Consider a commutative square
`g ∘ f' = f ∘ g'` with `f' : X' ⟶ Y'`, `g' : X' ⟶ X` and `g : Y' ⟶ Y`, `X'` and `Y'` schemes; put
`𝒜' = g^*𝒜`, `ℒ' = (g')^*ℒ` and let `ψ' : (f')^*𝒜' ⟶ ⨁_d (ℒ')^{⊗ d}` be the pullback of `ψ`
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting`).  Then

* `U(ψ') = (g')^{-1}(U(ψ))`, `U(ψ')` being the open of Tag 01O9 for `ψ'` over `Y'`; and
* `r_{ψ',ℒ'} : U(ψ') ⟶ Proj_{Y'}(𝒜')` of Tag 01O9 agrees with the base change of `r_{ψ,ℒ}`
  through the identification `Proj_{Y'}(𝒜') = Y' ×_Y F` of Stacks 084B: for every test scheme
  `t : T ⟶ X'` of `U(ψ')`, the `T`-point of `Y' ×_Y F` with components `f' ∘ t` and
  `r_{ψ,ℒ} ∘ g' ∘ t` is, in `Proj_{Y'}(𝒜')`, the composite `T ⟶ U(ψ') ⟶ Proj_{Y'}(𝒜')`. -/
@[stacks 0D2Z "clause (3), the open and the morphism, at a scheme point f : X -> Y of the base \
(X a scheme), for an ARBITRARY commutative square \
g o f' = f o g' with X', Y' schemes, on the relative Proj constructed as the functor of \
quadruples of Tag 084A: with psi' the pullback of psi to (f')^*(g^*A) (through the comparisons \
(f')^*(g^*A) = (g o f')^*A = (f o g')^*A = (g')^*(f^*A)), U(psi') = (g')^{-1}(U(psi)), and \
r_{psi',L'} : U(psi') -> Proj_{Y'}(g^*A) of Tag 01O9 is the base change of r_{psi,L} through the \
identification Proj_{Y'}(g^*A) = Y' x_Y Proj_Y(A) of Tag 084B, tested on every scheme T -> U(psi')"]
theorem invertibleMorphism_baseChange_square :
    (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          ψ g f' g' hsq)).coveringOpen =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map g' ⁻¹ᵁ
        (toGradedPowerMap ψ).coveringOpen ∧
    ∀ {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
      (ht : t ≫ g' ∈ (subspaceOfOpens s.site s.base s.containsBase X
        (toGradedPowerMap ψ).coveringOpen).obj (op T)),
      (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
          ⟨s.relativeProjPoints.locusFactor ψ (t ≫ g') ht ≫
            s.relativeProjPoints.invertibleMorphism ψ,
            s.quadrupleRestriction.locusFactor_invertibleMorphism_comp_π
              s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf ψ g f' g'
                hsq t
              ht⟩).1 =
        liftOfPreimageEqTop _ ((BigFppfOver.toScheme s.site s.base s.containsBase).map t)
            (s.quadrupleRestriction.preimage_coveringOpen_squareTwisting_eq_top
              s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf ψ g f' g'
                hsq t
              ht) ≫
          (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
            s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf ψ g f' g'
              hsq)).globalMorphism (relativeProj (s.relativeProjPoints.algebra Y' g)) :=
  ⟨s.quadrupleRestriction.coveringOpen_squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf ψ g f' g' hsq,
    fun t ht => s.quadrupleRestriction.invertibleMorphism_baseChange_square
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf ψ g f' g' hsq t
        ht⟩

/-- **The last assertion of clause (3) of Stacks 0D2Z, `θ'` is the pullback of `θ`, for an
arbitrary commutative square, on the constructed relative Proj.**

In the situation of `invertibleMorphism_baseChange_square` (a commutative square
`g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes, `𝒜' = g^*𝒜`, `ℒ' = (g')^*ℒ` and `ψ'` the pullback of
`ψ`), let `θ : r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` and
`θ' : r_{ℒ',ψ'}^*(⨁_d 𝒪(d)) ⟶ ⨁_d (ℒ')^{⊗ d}|_{U(ψ')}` be the homomorphisms of graded algebras of
Tag 01O9, for `ψ` at the point `f` and for `ψ'` over `Y'`.  Then `θ'` is the inverse image `j^*θ`
of `θ` along the restriction `j : U(ψ') = (g')^{-1}(U(ψ)) ⟶ U(ψ)` of `g'`, read through the
canonical identifications of sheaves of graded algebras
`j^*r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ≅ r_{ℒ',ψ'}^*(⨁_d 𝒪(d))`
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareThetaSourceIso`: pseudofunctoriality of
the inverse image and the comparison of the twists of Tag 01NR along the morphisms of relative
Proj's over the point `g ∘ f' = f ∘ g'` of `X'`, Stacks 084B (3)) and
`j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (ℒ')^{⊗ d}|_{U(ψ')}`
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareThetaTargetIso`). -/
@[stacks 0D2Z "clause (3), theta: at a scheme point f : X -> Y of the base (X a scheme), for an \
ARBITRARY commutative square g o f' = f o g' with X', \
Y' schemes, on the relative Proj constructed as the functor of quadruples of Tag 084A, the map \
theta' : r'^*((+)_d O(d)) -> (+)_d (L')^d|_{U(psi')} of Tag 01O9 for the pullback psi' of psi is \
the pullback j^*theta of theta along the restriction j : U(psi') -> U(psi) of g', through the \
canonical isomorphisms of graded algebras j^*r^*((+)_d O(d)) = r'^*((+)_d O(d)) and \
j^*((+)_d L^d|_{U(psi)}) = (+)_d (L')^d|_{U(psi')}"]
theorem invertibleTheta_baseChange_square :
    (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          ψ g f' g' hsq)).theta =
      (s.quadrupleRestriction.squareThetaSourceIso s.shrink.contains_relativeProj_pointAlgebra
          s.shrink.space.property.isSheaf ψ g f' g' hsq).inv ≫
        pullbackGradedAlgebraMap
          (Scheme.Hom.resLE ((BigFppfOver.toScheme s.site s.base s.containsBase).map g')
            (toGradedPowerMap ψ).coveringOpen
            (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
              s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
              ψ g f' g' hsq)).coveringOpen
            (s.quadrupleRestriction.coveringOpen_squareTwisting
              s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
              ψ g f' g' hsq).le).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫
        (s.quadrupleRestriction.squareThetaTargetIso s.shrink.contains_relativeProj_pointAlgebra
          s.shrink.space.property.isSheaf ψ g f' g' hsq).hom :=
  s.quadrupleRestriction.theta_baseChange_square s.shrink.contains_relativeProj_pointAlgebra
    s.shrink.space.property.isSheaf ψ g f' g' hsq

end RelativeProjSituation

/-! ### `θ` is characterized by clause (1) -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π) {X : BigFppfOver B S hS} {f : yoneda.obj X ⟶ Y}
    {L : ((BigFppfOver.toScheme B S hS).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X)) (situationAlgebra (d.algebra X f)) 1 L)

/-- **`θ` is characterized by clause (1) of [Stacks, Tag 0D2Z], after base change to the scheme
point `f : X ⟶ Y`.**  With the twists of `Proj_Y(𝒜)` at `f` those of `Proj_X(f^*𝒜)`, as in
`invertibleTheta_clauseOne`: a homomorphism of graded algebras
`θ' : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` which, for every open `V` of `X`, `d ≥ 0` and
`a ∈ (f^*𝒜)_d(V)`, carries the inverse image of `ψ_P(a)` to the restriction of `ψ(a)` to
`U(ψ) ∩ V` is `θ`. -/
@[stacks 0D2Z "theta is characterized by clause (1), at the scheme point f : X -> Y: a \
homomorphism of graded algebras theta' : r^*((+)_d O(d)) -> (+)_d L^d|_{U(psi)} which for every \
open V of X, d >= 0 and a in (f^*A)_d(V) carries the pullback of psi_P(a) to the restriction of \
psi(a) is theta"]
theorem invertibleTheta_unique
    (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback
        ((toGradedPowerMap ψ).globalMorphism (relativeProj (d.algebra X f)))
        (twistDataOfGradedAlgebra (d.algebra X f)).algebra)
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn L
        (toGradedPowerMap ψ).coveringOpen))
    (h : ∀ (V : ((BigFppfOver.toScheme B S hS).obj X).Opens) (n : ℕ)
        (a : Γ((d.algebra X f).piece (n : ℤ), V)),
        ((Stacks.AmpleProjectiveImmersion.tensorPowerModule _ L (n : ℤ)).restrict
            (toGradedPowerMap ψ).coveringOpen.ι).presheaf.map
            (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V)).op
            ((θ'.app n).val.app
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
                ((toGradedPowerMap ψ).value n V a))) :
    θ' = (toGradedPowerMap ψ).theta :=
  (toGradedPowerMap ψ).eq_theta_of_clauseOne h

end RelativeProjPoints

end AlgebraicGeometry.Space

end
