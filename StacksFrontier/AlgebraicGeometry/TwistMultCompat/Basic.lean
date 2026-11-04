module

public import StacksFrontier.AlgebraicGeometry.TwistMultCompat.Generic

/-!
# Tag 01NO: the canonical twist isomorphisms commute with multiplication

Tag 01NO's fourth assertion says that for an inclusion `U ⊆ V` of affine opens of the base of a
quasi-coherent graded algebra, the canonical isomorphisms on the twists of the induced morphism
of projective spectra are compatible with the multiplication maps
`𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` of Tag 01MU. The mathematics is Tag 01MY's
`Stacks.AlgebraicGeometry.ProjMapCard.projMapData_preserves_products`; everything between the two
is a transport along the five structural isomorphisms of the inverse image that Tag 01NO's
comparison wraps Tag 01MY's twist map in.

## Main results

* `Stacks.AlgebraicGeometry.TwistMultCompat.projInclusionTwistMap_preserves_products`: **the
  comparison maps on the twists commute with the multiplication maps**, for every pair of twist
  indices and every inclusion of affine opens of the base, with no hypothesis beyond that
  situation.
* `Stacks.AlgebraicGeometry.TwistMultCompat.projInclusionTwistIso_preserves_products`: **Tag
  01NO, multiplication compatibility of twist isomorphisms.** The same, with the comparison read
  as the `hom` of `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, which is
  the shape the tagged statement has.
* `Stacks.AlgebraicGeometry.TwistMultCompat.twistMultiplication_comp_twistComposite`: the same
  identity with the comparison written out as its six factors — the statement the transport
  produces, and the one the two above are obtained from by three applications of
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq`.

## How the kernel-cost obstruction is avoided

The transport *runs*, but identifying the transported composite directly with the **named**
comparison does not: `exact` against the whole equation
with the goal rewritten by `projInclusionTwistMap_eq` reports `maximum recursion
depth`, peeling the multiplication and the tensor map off with `congrArg` gets two of three
through and times out on the third, and `congr 1` is refused by the kernel. None of that is a
missing mathematical input.

What avoids it is running the transport **at the level of variables**, in
`Stacks.AlgebraicGeometry.TwistMultCompat.Generic`, where no `Proj`, no twisting sheaf and no
graded ring occurs. The six-factor statement below is then obtained from
`Stacks.AlgebraicGeometry.TwistMultCompat.transport_six` by *instantiation* — the elaborator
substitutes the concrete morphisms for the variables and the kernel checks that two written-out
composites of the same length are the same term — and the passage to the named comparison is
three applications of `projInclusionTwistMap_eq`, one per twist index, each of them a
`congrArg` whose motive is a single `≫`. No conversion at these types is requested anywhere, and no
compiler option is raised; the file builds in seconds.

Two spellings have to agree for this to work. They are recorded on the declarations they belong to in the companion file: the module
argument of a component of `AlgebraicGeometry.Scheme.Modules.pullbackComp` must be *the same
term* in the naturality square and in the monoidal coherence, since converting one spelling
against the other is a deterministic `whnf` timeout; and both morphism arguments of
`CategoryTheory.Functor.map_comp` must be written out rather than inferred, since with the middle
term free the elaborator may choose it by reducing the inverse image functor and the resulting
`isDefEq` exhausts the budget.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjMapCard Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.TwistMultTransport
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistMultCompat

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  TopCat.Presheaf.IsSheaf

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n m : ℤ)

/-- Equal pairs of comparison maps give equal tensor-then-multiply composites. -/
private theorem tensorMap_comp_twistMultiplicationMap_congr
    {a a' : (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
      (twistingSheaf (A.grading V) n) ⟶ twistingSheaf (A.grading U) n}
    {b b' : (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
      (twistingSheaf (A.grading V) m) ⟶ twistingSheaf (A.grading U) m}
    (ha : a = a') (hb : b = b') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.presheaf,
            (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m))
          ((a, b) : (_, _) ⟶ (_, _))) ≫ twistMultiplicationMap (A.grading U) n m =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.presheaf,
            (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m))
          ((a', b') : (_, _) ⟶ (_, _))) ≫ twistMultiplicationMap (A.grading U) n m := by
  subst ha hb
  rfl

/-- **The comparison maps on the twists commute with the multiplication maps.**

`Stacks.AlgebraicGeometry.TwistMultCompat.transport_six`, instantiated at the concrete data: the
factorisation `projInclusionTopSection ≫ projMapData.hom = projInclusionMap` of Tag 01NO's
morphism, the retraction `projInclusionTopSection ≫ mapDomain.ι = 𝟙` of the inclusion of Tag
01MY's open domain, Tag 01MU's multiplication maps at the two ends, and Tag 01MY's twist maps as
the comparison family. The multiplication identity those satisfy is
`Stacks.AlgebraicGeometry.TwistMultTransport.bundle_mult_twistMap`, i.e. Tag 01MY's
`projMapData_preserves_products` with its leading Tag 01CD comparison cancelled.

The six factors are never written down here. `Stacks.AlgebraicGeometry.ProjInclusionTwist`'s
`comp_congr` replaces, in one step, both the pulled-back multiplication by its definition and the
named comparison by its six factors — so the composite appears only in the *type* of an
intermediate `Eq.trans`, obtained by substituting the concrete morphisms into `transport_six`,
and never in a motive the elaborator has to build or in a statement it has to check. Writing it
out instead — in a theorem whose statement carries all three chains — is a deterministic
`isDefEq` timeout. -/
public theorem projInclusionTwistMap_preserves_products :
    pullbackTwistMultiplication (A.grading V) (projInclusionMap A U V h hU hV) n m ≫
        ProjInclusionTwist.projInclusionTwistMap A U V h hU hV (n + m) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m))
          (((ProjInclusionTwist.projInclusionTwistMap A U V h hU hV n),
            (ProjInclusionTwist.projInclusionTwistMap A U V h hU hV m)) :
              (_, _) ⟶ (_, _))) ≫
        twistMultiplicationMap (A.grading U) n m :=
  ((comp_congr
        (pullbackTwistMultiplication_eq (A.grading V) (projInclusionMap A U V h hU hV) n m)
        (ProjInclusionTwist.projInclusionTwistMap_eq A U V h hU hV (n + m))).trans
      (transport_six (projInclusionTopSection A U V h hU hV)
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι
        (projInclusionTopSection_ι A U V h hU hV)
        (projInclusionMap_eq_comp A U V h hU hV)
        (twistMultiplicationMap (A.grading V) n m)
        (twistMultiplicationMap (A.grading U) n m)
        ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n)
        ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap m)
        ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap (n + m))
        (bundle_mult_twistMap A U V h n m))).trans
    (tensorMap_comp_twistMultiplicationMap_congr A U V h hU hV n m
      (ProjInclusionTwist.projInclusionTwistMap_eq A U V h hU hV n).symm
      (ProjInclusionTwist.projInclusionTwistMap_eq A U V h hU hV m).symm)

/-- **Tag 01NO, multiplication compatibility of twist isomorphisms.** For an inclusion `U ⊆ V` of
affine opens of the base of a quasi-coherent graded algebra and any two twist indices `n, m : ℤ`,
the canonical isomorphisms on the twists of the induced morphism of projective spectra are
compatible with the multiplication maps of Tag 01MU: the pulled-back multiplication followed by
the comparison on the `(n + m)`-th twist is the tensor product of the comparisons on the `n`-th
and the `m`-th twists followed by the multiplication map downstairs.

The hypotheses are exactly those of the tagged statement: a quasi-coherent graded algebra on a scheme, two affine
opens, an inclusion between them, and two unrestricted twist indices. -/
@[stacks 01NO "multiplication compatibility of twist isomorphisms"]
public theorem projInclusionTwistIso_preserves_products :
    pullbackTwistMultiplication (A.grading V) (projInclusionMap A U V h hU hV) n m ≫
        (projInclusionTwistIso A U V h hU hV (n + m)).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m))
          (((projInclusionTwistIso A U V h hU hV n).hom,
            (projInclusionTwistIso A U V h hU hV m).hom) : (_, _) ⟶ (_, _))) ≫
        twistMultiplicationMap (A.grading U) n m :=
  ((comp_congr
        (Eq.refl (pullbackTwistMultiplication (A.grading V)
          (projInclusionMap A U V h hU hV) n m))
        (projInclusionTwistIso_hom A U V h hU hV (n + m))).trans
      (projInclusionTwistMap_preserves_products A U V h hU hV n m)).trans
    (tensorMap_comp_twistMultiplicationMap_congr A U V h hU hV n m
      (projInclusionTwistIso_hom A U V h hU hV n).symm
      (projInclusionTwistIso_hom A U V h hU hV m).symm)

/-! ### Faithfulness to the statement of Tag 01NO

The statement of Tag 01NO writes its fourth assertion over the canonical twist isomorphism,
which is `CategoryTheory.asIso` of the comparison map applied to
`projInclusionTwistMap_isIso` — the assertion whose library form,
`Stacks.AlgebraicGeometry.ProjInclusionTwist.isIso_projInclusionTwistMap`, carries Tag 01NO's
`canonical twist isomorphisms` label. The `example` below is that statement with that spelling
restored and in its own binder order, so that the tagged theorem above is checkably the
assertion of Tag 01NO and not a neighbour of it. -/

example (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (n m : ℤ) :
    pullbackTwistMultiplication (A.grading V) (projInclusionMap A U V h hU hV) n m ≫
        (@asIso _ _ _ _ _ (isIso_projInclusionTwistMap A U V h hU hV (n + m))).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U)).toRingedSpace)).IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m))
          (((@asIso _ _ _ _ _ (isIso_projInclusionTwistMap A U V h hU hV n)).hom,
            (@asIso _ _ _ _ _ (isIso_projInclusionTwistMap A U V h hU hV m)).hom) :
              (_, _) ⟶ (_, _))) ≫
        twistMultiplicationMap (A.grading U) n m :=
  ((comp_congr
        (Eq.refl (pullbackTwistMultiplication (A.grading V)
          (projInclusionMap A U V h hU hV) n m))
        (@asIso_hom _ _ _ _ (ProjInclusionTwist.projInclusionTwistMap A U V h hU hV (n + m))
          (isIso_projInclusionTwistMap A U V h hU hV (n + m)))).trans
      (projInclusionTwistMap_preserves_products A U V h hU hV n m)).trans
    (comp_congr
      (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.presheaf,
            (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
            (twistingSheaf (A.grading V) n),
            (Scheme.Modules.pullback (projInclusionMap A U V h hU hV)).obj
              (twistingSheaf (A.grading V) m)))
          (Y := (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m)))
        (Prod.ext (@asIso_hom _ _ _ _ (ProjInclusionTwist.projInclusionTwistMap A U V h hU hV n)
          (isIso_projInclusionTwistMap A U V h hU hV n)).symm
          (@asIso_hom _ _ _ _ (ProjInclusionTwist.projInclusionTwistMap A U V h hU hV m)
            (isIso_projInclusionTwistMap A U V h hU hV m)).symm))
      (Eq.refl (twistMultiplicationMap (A.grading U) n m)))

end Stacks.AlgebraicGeometry.TwistMultCompat

end
