module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverTopologyInstances

/-!
# Higher cohomology of `Gₐ` and of its restrictions over affine objects of the big fppf site

On the big fppf site of a scheme `S`, the positive-degree cohomology of `Gₐ` over an object with
affine underlying scheme vanishes: `Gₐ` is the associated sheaf of the structure sheaf of `S`, so
this is the affine vanishing of the cohomology of an associated quasi-coherent sheaf.

The vanishing survives restriction along a continuous functor `v` from the slice of the big fppf
category over an object `X` to the big fppf site of `S`, as soon as `v` preserves fibre products
and equalizers and sends objects with affine underlying scheme to objects with affine underlying
scheme. This is the Leray collapse along `v`: the higher direct images of the sheaf vanish,
because every object of the slice over `X` is covered by objects with affine underlying scheme,
over whose images the higher cohomology vanishes; so cohomology over an object `T` of the
restriction is cohomology over `v T`, which vanishes when `T` has affine underlying scheme.

Two such functors are `Over.map f` along the structure morphism `f : X → S` of an object of the
site (the restriction to the localized site), and `Over.map f ⋙ Over.pullback z ⋙ Over.map z`
for `z : Z → S`, which sends `T` to `T ×_S Z` and whose restriction of `Gₐ` is the sheaf
`T ↦ Γ(T ×_S Z, 𝒪)`, provided `X ×_S Z → X` is a closed immersion.

## Main results

* `AlgebraicGeometry.BigFppfOver.isZero_H'_additiveGroupSheaf_of_isAffine`: `H^q(A, Gₐ) = 0`
  for `q > 0` and `A` with affine underlying scheme.
* `AlgebraicGeometry.BigFppfOver.isZero_H'_sheafPushforwardContinuous_of_isAffine`: the same
  vanishing for the restriction of a sheaf acyclic over affine objects along such a functor `v`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

-- A localized big site is essentially small at the universe of its morphisms, so these two
-- supply its `Ext` universe and enough injectives.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u})

/-- Abelian presheaves on the slice `B.topology.over X` of a big fppf site over one of its objects
can be sheafified: this is the localized fppf site of the underlying scheme of `X`, spelled as a
localization of the site's topology. -/
theorem hasSheafify_topology_over (X : B.Schemes) :
    HasSheafify (B.topology.over X) AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (BigFppfOver.topology B (B.inclusion.obj X) X.2) AddCommGrpCat.{u})

attribute [local instance] hasSheafify_topology_over

/-- **`H^q(A, Gₐ) = 0` for `q > 0` over an object `A` of the big fppf site of `S` with affine
underlying scheme.** `Gₐ` is the associated sheaf of the structure sheaf of `S`
(`AlgebraicGeometry.overAdditiveGroupSheafIsoAssociatedSheaf`), whose positive-degree cohomology
over affine objects vanishes (`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`). -/
theorem isZero_H'_additiveGroupSheaf_of_isAffine {S : Scheme.{u}} (hS : B.Contains S)
    (A : BigFppfOver B S hS) (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (q : ℕ) (hq : 0 < q) :
    IsZero (Sheaf.H' (BigFppfOver.additiveGroupSheaf S B hS) q A) :=
  letI : HasSheafify (overTopology .fppf B S hS) AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u})
  letI : HasExt.{u} (Sheaf (overTopology .fppf B S hS) AddCommGrpCat.{u}) :=
    inferInstanceAs (HasExt.{u} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}))
  (isZero_sheafCohomology_succ_overAffine S (Scheme.unitModule S) .fppf B hS A hA q hq).of_iso
    (((Sheaf.cohomologyPresheafFunctor _ q).mapIso
      (overAdditiveGroupSheafIsoAssociatedSheaf S .fppf B hS)).app (op A)).symm

/-- **Restriction along a functor preserving affineness keeps the affine vanishing.** Let `v` be
a continuous functor from the slice over an object `X` of the big fppf site to the big fppf site
of `S`, preserving fibre products and equalizers and sending objects with affine underlying
scheme to objects with affine underlying scheme, and let `G` be an abelian sheaf on the big fppf
site of `S` whose positive-degree cohomology vanishes over every object with affine underlying
scheme. Then the positive-degree cohomology of the restriction of `G` along `v` vanishes over
every object with affine underlying scheme.

This is the Leray collapse `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` along
`v`: its higher direct images vanish by
`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, the
objects with affine underlying scheme covering every object of the slice
(`bigAffineFppfInclusion_isDenseSubsite`). -/
theorem isZero_H'_sheafPushforwardContinuous_of_isAffine {S : Scheme.{u}} (hS : B.Contains S)
    (X : B.Schemes) (G : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (hG : ∀ A : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj A) →
      ∀ q, 0 < q → IsZero (Sheaf.H' G q A))
    (v : Over X ⥤ BigFppfOver B S hS)
    [v.IsContinuous (B.topology.over X) (BigFppfOver.topology B S hS)]
    [PreservesLimitsOfShape WalkingCospan v] [PreservesLimitsOfShape WalkingParallelPair v]
    (hv : ∀ W : Over X, IsAffine (B.inclusion.obj W.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (v.obj W)))
    (T : Over X) (hT : IsAffine (B.inclusion.obj T.left)) (q : ℕ) (hq : 0 < q) :
    IsZero (Sheaf.H' ((v.sheafPushforwardContinuous AddCommGrpCat.{u}
      (B.topology.over X) (BigFppfOver.topology B S hS)).obj G) q T) := by
  let J := B.topology.over X
  let K := BigFppfOver.topology B S hS
  let : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasEqualizers (Over X) := hasEqualizers_of_hasPullbacks_and_binary_products
  let := fun P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u} =>
    Stacks.Cohomology.BiggerSite.hasPointwiseLeftKanExtension_op v P
  let : (v.sheafPushforwardContinuous AddCommGrpCat.{u} J K).PreservesInjectiveObjects :=
    Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous J K v
  let : (v.sheafPushforwardContinuous AddCommGrpCat.{u} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hvan : ∀ j, 1 ≤ j → j ≤ q →
      IsZero (((v.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived j).obj G) := by
    intro j hj _
    refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
      v j G (fun V => ?_)
    refine ⟨fun W _ => IsAffine (B.inclusion.obj W.left), ?_, fun W g hg => ?_⟩
    · have : (BigAffineFppf.inclusion B (B.inclusion.obj X) X.2).IsCoverDense
          (BigFppfOver.topology B (B.inclusion.obj X) X.2) :=
        Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B (B.inclusion.obj X) X.2) _ _
      have hc : Sieve.coverByImage (BigAffineFppf.inclusion B (B.inclusion.obj X) X.2) V ∈
          BigFppfOver.topology B (B.inclusion.obj X) X.2 V :=
        Functor.IsCoverDense.is_cover (G := BigAffineFppf.inclusion B (B.inclusion.obj X) X.2)
          (K := BigFppfOver.topology B (B.inclusion.obj X) X.2) V
      refine J.superset_covering ?_ hc
      rintro W g ⟨s⟩
      exact ⟨_, s.lift, s.map, s.obj.property, s.fac⟩
    · exact (hG _ (hv W hg) j hj).of_iso
        (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
          K G j (v.obj W)).symm
  exact (hG _ (hv T hT) q hq).of_iso
    (Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso J K v G T q hvan)

end AlgebraicGeometry.BigFppfOver

end
