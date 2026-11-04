module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Psi

/-!
# Tag 01NR's `ψ` in adjoint form, read along a factorization

For a quasi-coherent graded algebra `A` on a scheme `Y` with relative homogeneous spectrum
`π : Proj_Y(A) ⟶ Y`, and a morphism `ι : X ⟶ Proj_Y(A)` with `f = ι ≫ π`, the
homomorphism-of-sections map `ψ : A_n ⟶ π_*𝒪(n)` of Stacks 01NR transposes along `π^* ⊣ π_*` and
pulls back along `ι` to a morphism `f^*A_n ⟶ ι^*𝒪(n)`
(`AlgebraicGeometry.Space.pullbackAdjointPsi`). In Situation 0849 this is, on the scheme of a base
change `V ×_X P = Proj_V(v^*𝒜)`, the morphism
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHom` of the atlas, written at free
variables (`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`).

## Main definitions

* `AlgebraicGeometry.Space.pullbackAdjointOfComp`: the adjoint `f^*A ⟶ ι^*O` of `ψ : A ⟶ p_* O`
  along a factorization `f = ι ≫ p`.
* `AlgebraicGeometry.Space.pullbackAdjointPsi`: the case of Tag 01NR's `ψ`.
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToBase`: the structure morphism
  `V ×_X P ⟶ V` on schemes.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`: Tag 01NR's `ψ` on the
  scheme of `V ×_X P` in adjoint form, as `AlgebraicGeometry.Space.pullbackAdjointPsi` at the
  point.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartHomOfAdjoint`: `ψ` on the atlas, built
  from `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-- **The adjoint of `ψ : A ⟶ p_* O` read along a factorization `f = ι ≫ p`**: the transpose
`p^*A ⟶ O` of `ψ` along `p^* ⊣ p_*`, pulled back along `ι`, read through `f^*A ≅ ι^*p^*A`. -/
def pullbackAdjointOfComp {X P Y : Scheme.{u}} (ι : X ⟶ P) (p : P ⟶ Y) (f : X ⟶ Y)
    (hf : f = ι ≫ p) {A : Y.Modules} {O : P.Modules}
    (ψ : A ⟶ (Scheme.Modules.pushforward p).obj O) :
    (Scheme.Modules.pullback f).obj A ⟶ (Scheme.Modules.pullback ι).obj O :=
  (Scheme.Modules.pullbackCongr hf).hom.app A ≫ (Scheme.Modules.pullbackComp ι p).inv.app A ≫
    (Scheme.Modules.pullback ι).map
      (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm ψ)

open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra) in
/-- **Tag 01NR's `ψ` in adjoint form, read along a factorization**: for a quasi-coherent graded
algebra `A` on `Y`, a morphism `ι : X ⟶ Proj_Y(A)` and `f = ι ≫ π` with `π : Proj_Y(A) ⟶ Y` the
structure morphism, the morphism `f^*A_n ⟶ ι^*𝒪(n)`
(`AlgebraicGeometry.Space.pullbackAdjointOfComp` of the homogeneous-section map `ψ`). -/
def pullbackAdjointPsi {X Y : Scheme.{u}} (A : SheafGradedAlgebra Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase)
    (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback ι).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)) :=
  pullbackAdjointOfComp ι (relativeProj A).toBase f hf
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n)

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The structure morphism `V ×_X P ⟶ V` on schemes, with the scheme of `V` read as the base of
the relative homogeneous spectrum `Proj_V(v^*𝒜)` (the spelling of Situation 0849 shrunk to the
universe `u`, `AlgebraicGeometry.Space.RelativeProjSituation.shrink`). -/
def fibreToBase (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
      (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj V :=
  (BigFppfOver.toScheme s.site s.base s.containsBase).map (s.relativeProjPoints.fibreHom V v)

/-- The structure morphism `V ×_X P ⟶ V` on schemes is the structure morphism of `Proj_V(v^*𝒜)`,
read through `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
theorem fibreToBase_eq (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    s.fibreToBase V v = s.toRelativeProj V v ≫ (relativeProj (s.shrink.pointAlgebra V v)).toBase :=
  s.toScheme_map_fibreHom V v

/-- **Tag 01NR's `ψ` on the scheme of `V ×_X P`, in adjoint form, at free variables**:
`AlgebraicGeometry.Space.pullbackAdjointPsi` at the point `v`, the transpose
`π_V^*(v^*𝒜)_n ⟶ 𝒪(n)` of the homogeneous-section map `(v^*𝒜)_n ⟶ π_{V*}𝒪(n)`. -/
def psiChartSchemeHomOfAdjoint (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℕ) :
    (Scheme.Modules.pullback (s.fibreToBase V v)).obj ((s.shrink.pointAlgebra V v).piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback (s.toRelativeProj V v)).obj
        ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)).piece (n : ℤ)) :=
  pullbackAdjointPsi (s.shrink.pointAlgebra V v) (s.toRelativeProj V v) (s.fibreToBase V v)
    (s.fibreToBase_eq V v) n

/-- **`ψ` on the atlas in degree `n`**, with Tag 01NR's `ψ` in the form
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`: the identification
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso` followed by the module attached
to `ψ` in adjoint form. -/
def psiChartHomOfAdjoint
    (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property) (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).obj
        (s.psiSourceQcoh (n : ℤ)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
          (s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))).obj :=
  (s.psiChartSourceIso Px (n : ℤ)).hom ≫
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.map
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (n : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))).hom

end RelativeProjSituation

end AlgebraicGeometry.Space

end
