module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteSectionPullbackTransfer

/-!
# Sections over the geometric fibre come from étale neighbourhoods, given proper base change

Let `B` be a big étale site, `f : X ⟶ Y` a proper morphism of its underlying category, `ȳ` a
geometric point of `Y` whose spectrum lies in `B`, `X_ȳ` the geometric fibre and
`p : X_ȳ ⟶ X` its projection. For an abelian sheaf `F` on the bounded small étale site of `X`,
every global section of `p⁻¹F` over `X_ȳ` is the pullback, along `X_ȳ ⟶ X_V`, of a section of `F`
over `X_V = X ×_Y V` for some étale neighbourhood `(V, v̄)` of `ȳ`.

This is the surjectivity half of the proper base change theorem for `H⁰`
([Stacks, Tag 095T](https://stacks.math.columbia.edu/tag/095T)), which enters the description of
the stalks of `f_!` ([Stacks, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)). It is
derived here from the same statement for sheaves of sets on Mathlib's model of the small étale
site, carried as the hypothesis `hM`, through the comparison of the two presentations of the small
étale site, `AlgebraicGeometry.SmallEtale.exists_sectionPullback_transfer`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_geometricFibreRestriction_eq_of_isProper_of_sets` — the
  statement above, given `hM`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.obj)
  (hy : B.Contains y.source)

/-- **Sections over the geometric fibre of a proper morphism come from étale neighbourhoods,
granted the statement for sheaves of sets on Mathlib's small étale site.** Let `f : X ⟶ Y` be
proper, `ȳ` a geometric point of `Y` and `p : X_ȳ ⟶ X` the projection of the geometric fibre.
Assume `hM`: for every sheaf of sets `H` on Mathlib's small étale site of `X`, every global
section of `p⁻¹H` is, for some étale neighbourhood `(V, v̄)` of `ȳ`, the pullback of a section of
`H` over `X_V` along `X_ȳ ⟶ X_V`. Then every global section of `p⁻¹F`, for an abelian sheaf `F`
on the bounded small étale site of `X`, is `geometricFibreRestriction` of a section of `F` over
some `X_V`.

The hypothesis `hM` is the proper base change theorem in degree zero for Mathlib's model of the
small étale site (Stacks 095T); it is not discharged here. -/
theorem exists_geometricFibreRestriction_eq_of_isProper_of_sets
    [IsProper (B.inclusion.map f)]
    (hM : ∀ (H : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (max (u + 1) v)))
      (t : ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v}
          (B.inclusion.map (geometricFibreProj B f y hy))).obj H).obj.obj
            (op (Scheme.Etale.mk (𝟙 (geometricFibreObj B f y hy).obj)))),
      ∃ (N : (geometricPointFiber B Y.obj Y.property y).Elements)
        (s : H.obj.obj (op ((toEtaleSite B X.obj X.property).obj
          ((smallEtaleBaseChange B f).obj N.1)))),
        ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v}
            (B.inclusion.map (geometricFibreProj B f y hy))).obj H).obj.map
          (Stacks.EtaleCohomology.smallEtaleBaseChangeLift
            (B.inclusion.map (geometricFibreProj B f y hy))
            ((toEtaleSite B X.obj X.property).obj ((smallEtaleBaseChange B f).obj N.1))
            (B.inclusion.map ((geometricFibreLift B f y hy N).hom.left ≫
              baseChangeObjProjection B (geometricFibreProj B f y hy)
                ((smallEtaleBaseChange B f).obj N.1)))
            (baseChangeLift_condition B (geometricFibreProj B f y hy)
              ((smallEtaleBaseChange B f).obj N.1) (geometricFibreLift B f y hy N))).op
          (Stacks.EtaleCohomology.smallEtaleSectionPullback.{u, v}
            (B.inclusion.map (geometricFibreProj B f y hy)) H _ s) = t)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (t : geometricFibreSections B f y hy F) :
    ∃ (N : (geometricPointFiber B Y.obj Y.property y).Elements)
      (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj N.1))),
      geometricFibreRestriction B f y hy F N s = t := by
  obtain ⟨H, eX, eP, hcomp⟩ :=
    exists_sectionPullback_transfer.{v, u} B (geometricFibreProj B f y hy) F
  obtain ⟨N, s', hs'⟩ := hM H (eP t)
  refine ⟨N, (eX _).symm s', eP.injective ?_⟩
  refine (hcomp ((smallEtaleBaseChange B f).obj N.1) (geometricFibreLift B f y hy N)
    ((eX _).symm s')).trans ?_
  rw [Equiv.apply_symm_apply]
  exact hs'

end AlgebraicGeometry.SmallEtale

end
