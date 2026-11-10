module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent

/-!
# An étale chart of the source whose image factors through a chart of the target

Let `g : X' ⟶ X` be a morphism of algebraic spaces. There is an étale chart `v : V ⟶ X'` which
is surjective (it alone is an étale covering of `X'`) and whose composite with `g` factors as
`V ⟶ U ⟶ X` through an étale chart `u : U ⟶ X`.

Consequently a morphism of `𝒪_{X'}`-modules is determined by its inverse images along the étale
charts `v` of `X'` for which `v ≫ g` factors through an étale chart of `X`.

## Main results

* `AlgebraicGeometry.Space.exists_chart_factorization_isEtaleCovering`: the chart `v`.
* `AlgebraicGeometry.Space.hom_ext_of_chart_factorization`: the extensionality principle.

## References

* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A surjective étale chart of `X'` whose composite with `g : X' ⟶ X` factors through an étale
chart of `X`.** -/
theorem exists_chart_factorization_isEtaleCovering {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) :
    ∃ (V : SmallEtale B S hS X'.1) (U : SmallEtale B S hS X.1)
      (h : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj U),
      V.1.hom ≫ g.hom = yoneda.map h ≫ U.1.hom ∧
      IsEtaleCovering B S hS
        (fun _ : PUnit.{u + 1} => yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V))
        (fun _ => V.1.hom) := by
  have : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
  obtain ⟨T, a, ha_surj, ha_et⟩ := X.2.exists_atlas
  have : HasPullback g.hom a := HasLimitsOfShape.has_limit _
  have hpb := isEtaleCovering_pullback B S hS g.hom X'.2 _ _
    (isEtaleCovering_atlas.{u, u} B S hS X.2 ha_surj ha_et)
  have hP := hpb.source_isAlgebraicSpace PUnit.unit
  obtain ⟨T', b, hb_surj, hb_et⟩ := hP.exists_atlas
  have hcomp := isEtaleCovering_comp B S hS (fun _ : PUnit.{u + 1} => PUnit.{u + 1}) _ _ _
    (fun _ _ => b) hpb (fun _ => isEtaleCovering_atlas.{u, u} B S hS hP hb_surj hb_et)
  have hcomp' := IsEtaleCovering.reindex B S hS hcomp
    (σ := fun _ : PUnit.{u + 1} => (⟨PUnit.unit, PUnit.unit⟩ : (_ : PUnit.{u + 1}) × PUnit.{u + 1}))
    (fun _ => ⟨PUnit.unit, rfl⟩)
  refine ⟨⟨CostructuredArrow.mk (b ≫ pullback.fst g.hom a),
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 (hcomp'.etale PUnit.unit)⟩,
    ⟨CostructuredArrow.mk a, ha_et⟩, Yoneda.fullyFaithful.preimage (b ≫ pullback.snd g.hom a),
    ?_, hcomp'⟩
  change (b ≫ pullback.fst g.hom a) ≫ g.hom =
    yoneda.map (Yoneda.fullyFaithful.preimage (b ≫ pullback.snd g.hom a)) ≫ a
  rw [Yoneda.fullyFaithful.map_preimage, Category.assoc, Category.assoc, pullback.condition]

/-- **A morphism of `𝒪_{X'}`-modules is determined by its inverse images along the étale charts
`v` of `X'` whose composite with `g : X' ⟶ X` factors through an étale chart of `X`.** -/
theorem hom_ext_of_chart_factorization {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    {M N : Modules.{u, u} B S hS X'.1 X'.2} {a b : M ⟶ N}
    (H : ∀ (V : SmallEtale B S hS X'.1) (U : SmallEtale B S hS X.1)
      (h : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj U),
      V.1.hom ≫ g.hom = yoneda.map h ≫ U.1.hom →
      (modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V) (X := X')
        V.1.hom)).map a =
      (modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V) (X := X')
        V.1.hom)).map b) :
    a = b := by
  obtain ⟨V, U, h, hvh, hcov⟩ := exists_chart_factorization_isEtaleCovering g
  exact QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : PUnit.{u + 1} => yonedaSpace B S hS ((SmallEtale.toOver B S hS X'.1).obj V))
    (fun _ => pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V) (X := X') V.1.hom) hcov a b
    (fun _ => H V U h hvh)

end AlgebraicGeometry.Space

end
