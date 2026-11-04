module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistExists
public import StacksFrontier.AlgebraicGeometry.ProjMapCard.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication

/-!
# Tag 07ZG: the graded-algebra clause of `θ`, written down

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, `U(ψ) ⊆ Proj_S(B)` the
open it induces a morphism on, `r_ψ : U(ψ) ⟶ Proj_S(A)` that morphism and `θ_n` the comparison map
on the `n`-th twist built in `StacksFrontier/AlgebraicGeometry/Morphism/TwistExists.lean`. Tag 07ZG
states `θ` not as a family of degreewise maps but as a map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras

`r_ψ^*(⨁_d 𝒪_{Proj_S(A)}(d)) ⟶ ⨁_d 𝒪_{U(ψ)}(d)`,

and the clause the degreewise family does not carry is that it respects the products. **This file
writes that clause down as a Lean statement and reduces it.** It is proved in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulProof.lean`, which discharges the hypothesis of
the second reduction below; `θ` is assembled as a homomorphism of sheaves of graded algebras, and
the tag registered, in `StacksFrontier/AlgebraicGeometry/Morphism/TwistAlgebra.lean`.

The clause is a square, not a structure, because the relative graded algebra already exists:
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.gluedTwistAlgebra` is a sheaf of `ℤ`-graded algebras on
the relative `Proj` whose `piece n` is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A n`,
and `relativeTwistMul` below is its product morphism out of the tensor product sheaf. What has to
be proved is

`r_ψ^*𝒪(m) ⊗ r_ψ^*𝒪(n) ⟶ r_ψ^*𝒪(m+n) --θ_{m+n}--> ι^*𝒪(m+n)` equals
`r_ψ^*𝒪(m) ⊗ r_ψ^*𝒪(n) --θ_m ⊗ θ_n--> ι^*𝒪(m) ⊗ ι^*𝒪(n) ⟶ ι^*𝒪(m+n)`,

both pulled-back products formed with the Tag 01CD comparison, which is `pullbackRelativeTwistMul`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMul`: the product of the relative twists —
  the multiplication of the glued graded algebra of Tag 01NR, as a morphism out of the tensor
  product sheaf.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.pullbackRelativeTwistMul`: that product pulled back along
  a morphism into the relative `Proj`, formed with the Tag 01CD comparison. This is the relative
  analogue of `Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`, and the two
  sides of the clause are composites of it.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.IsMultiplicativeOnSections`: **the clause reduced to local
  sections.** The statement that `θ_{m+n}` carries the pullback-unit image of a product of two
  sections of the relative twists to the product of the images — the relative analogue of
  `Stacks.AlgebraicGeometry.ProjMapCard.twistPushforwardMap_twistMultiplicationMap`, which is the
  shape in which the absolute clause's content was proved.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul_of_sections`: **the section-level
  statement implies the clause.** The Tag 01CD comparison is invertible, so it can be cancelled off
  the source; a morphism out of a pullback of a tensor product is determined by its adjoint
  transpose on the sheafification-unit images of pure tensors
  (`Stacks.AlgebraicGeometry.ProjMapCard.pullbackTensor_hom_ext`); and on such an image each side
  is computed outright.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul_of_forall_chart` and
  `relativeTwistMap_mul_of_forall_chart_pullback`: **the clause is local on the pieces of `U(ψ)`**,
  in the two spellings of a restriction. This is
  `Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.hom_ext_of_chartImage` at the two sides of the
  square.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.comparison_comp_pullbackRelativeTwistMul`,
  `relativeTwistMap_mul_lhs_pullbackUnit` and `relativeTwistMap_mul_rhs_pullbackUnit`: the three
  computations the first reduction is assembled from.

## Which reduction was used, and no `stacks` attribute is attached here

**The clause is proved**, in `StacksFrontier/AlgebraicGeometry/Morphism/TwistMulProof.lean`:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul`. Nothing in *this* file carries the
project tag, because the tag belongs on the declaration that states the whole of Tag 07ZG, which
is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeProjMapTriple` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistAlgebra.lean`.

Of the two reductions below it is the chart one,
`relativeTwistMap_mul_of_forall_chart_pullback`, that was used. **The section reduction was not**:
no term of type `IsMultiplicativeOnSections` is constructed anywhere, and
`relativeTwistMap_mul_of_sections` is unused by the proof. It is kept because it records the shape
in which the *absolute* clause's content was proved and is the form a future direct argument on
sections would take.

One observation from the earlier notes survives and is worth keeping. The route "the locality
argument of `StacksFrontier/AlgebraicGeometry/Morphism/TwistEventual.lean` carries the absolute
statement across" does **not** apply. That argument works because being an epimorphism and being an
isomorphism are *properties* stable under conjugation by isomorphisms, so `relativeTwistMap_chart`
together with `relativeTwistChart_eq` suffices and no section is ever looked at. Multiplicativity
is an *equation*, and conjugating an equation by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and `chartTargetIso` requires those
isomorphisms to be moved past the tensor products and the multiplications — which is a
computation. That computation is
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulLeg.lean`'s `leg_mul`, run at the level of
variables and instantiated at the two legs.

Neither a bridge of `Stacks.PullbackCompMonoidal.comparison_tensor` to the spelling used here nor a
tensor analogue of `chartSourceIso` is needed. `comparison_tensor` is not used at all;
the structural compatibilities actually used are
`Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp_hom`,
`Stacks.AlgebraicGeometry.TwistMultCompat.comparison_tensorSheafMap_nat` and
`Stacks.AlgebraicGeometry.TwistMultTransport.pullbackCongr_rfl_hom_app`, all already available at the
scheme spelling, and no tensor analogue of `chartSourceIso` exists or is wanted — the tensor
products are moved by the *generic* lemmas of `TwistMulLeg`, where the chart isomorphisms do not
occur.

## Implementation notes

`relativeTwistMap_mul_of_sections` is assembled from three separately-stated computations rather
than proved in one `refine` chain: stated as one declaration, with the section-level hypothesis
written out inline, it reports `(deterministic) timeout at whnf, maximum number of heartbeats
(200000) has been reached` at the declaration header, and the heartbeat limit cannot be raised in
this library. The hypothesis is therefore a `def ... : Prop`, elaborated once, and the two sides of
the square are computed by `relativeTwistMap_mul_lhs_pullbackUnit` and
`relativeTwistMap_mul_rhs_pullbackUnit`. This is the discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/GluedTwistAlgebra/Assemble.lean` record for the same reason.

The computations are chains of `Eq.trans` and `congrArg`: `AlgebraicGeometry.Scheme.Modules` is a
`def`, so a `rw` whose motive abstracts over a section of a tensor product fails its motive check
even where both sides print identically. This is the device
`StacksFrontier/AlgebraicGeometry/ProjMapCard/Multiplication.lean` already uses, and the absolute
clause's proof is the model for the whole first reduction.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}}

/-- **The product of the relative twists.** The multiplication of the glued graded algebra of Tag
01NR on the relative projective spectrum of `A`, whose homogeneous pieces are the relative twists,
read as a morphism out of the tensor product sheaf rather than as a bilinear map on local
sections. -/
public abbrev relativeTwistMul (A : SheafGradedAlgebra S) (m n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
        (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩).obj ((relativeTwist A m))).obj
        ((relativeTwist A n))) ⟶
      relativeTwist A (m + n) :=
  SheafOfModules.GradedAlgebra.mulSheaf
    (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra m n

/-- **The product of the relative twists, pulled back along a morphism into the relative
`Proj`**: `f^*𝒪(m) ⊗ f^*𝒪(n) ⟶ f^*𝒪(m+n)`, the inverse of the Tag 01CD comparison between the
pullback of a tensor product and the tensor product of the pullbacks, followed by the pullback of
the product. The relative analogue of
`Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`; the comparison is invertible
unconditionally, which is what makes the definition possible. -/
public def pullbackRelativeTwistMul (A : SheafGradedAlgebra S) {W : Scheme.{u}}
    (f : W ⟶ (relativeProj A).scheme) (m n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((W.toRingedSpace)).presheaf,
        ((W.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj
        (relativeTwist A m)))).obj (((Scheme.Modules.pullback f).obj (relativeTwist A n)))) ⟶
      (Scheme.Modules.pullback f).obj (relativeTwist A (m + n)) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app
      (relativeTwist A m, relativeTwist A n) ≫
    (Scheme.Modules.pullback f).map (relativeTwistMul A m n)

/-- The forward direction of the Tag 01CD comparison is the one the pulled-back product inverts:
`pullbackRelativeTwistMul` composed on the left with the comparison is the pullback of the
product. -/
public theorem comparison_comp_pullbackRelativeTwistMul (A : SheafGradedAlgebra S)
    {W : Scheme.{u}} (f : W ⟶ (relativeProj A).scheme) (m n : ℤ) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
          (relativeTwist A m, relativeTwist A n) ≫
        pullbackRelativeTwistMul A f m n =
      (Scheme.Modules.pullback f).map (relativeTwistMul A m n) :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun k => k ≫ (Scheme.Modules.pullback f).map (relativeTwistMul A m n))
        (Iso.hom_inv_id_app
          (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom)
          (relativeTwist A m, relativeTwist A n)))
      (Category.id_comp _))

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- **The graded-algebra clause of Tag 07ZG is local on the pieces of `U(ψ)`.** If the two sides of
the square have equal restrictions to the piece of `U(ψ)` over every affine open of the base, they
are equal.

The pieces cover `U(ψ)`, so a morphism of sheaves of modules on `U(ψ)` is determined by its
restrictions to them; this is that separation statement, `hom_ext_of_chartImage`, at the two sides
of the square. This is the restriction spelling; it is the inverse-image spelling,
`relativeTwistMap_mul_of_forall_chart_pullback`, whose hypothesis
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulProof.lean` discharges. -/
public theorem relativeTwistMap_mul_of_forall_chart (m n : ℤ)
    (h : ∀ U : AffineOpen S,
      (Scheme.Modules.restrictFunctor (pieceIncl ψ U)).map
          (pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n)) =
        (Scheme.Modules.restrictFunctor (pieceIncl ψ U)).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
              ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
              (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
            pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n)) :
    pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
          ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
        pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n :=
  Tag07ZGTwistLocality.hom_ext_of_chartImage ψ h

/-- **The graded-algebra clause of Tag 07ZG, reduced to local sections.** For every open `V` of
`Proj_S(A)` and sections `s`, `t` of the `m`-th and `n`-th relative twists over `V`, the map
`θ_{m+n}` carries the pullback-unit image of the product of `s` and `t` to the pulled-back product
of the images of the pullback-unit images of `s` and of `t`.

The source of the square has no usable sections — it is a tensor product of two pullbacks — and
this is what replaces them: it is the relative analogue of
`Stacks.AlgebraicGeometry.ProjMapCard.twistPushforwardMap_twistMultiplicationMap`, the shape in
which the absolute clause's mathematical content was proved. `relativeTwistMap_mul_of_sections`
derives the clause from it; **no term of this type is constructed anywhere**, and the clause is
proved instead through the chart reduction — see the note above on which reduction was used. -/
public def IsMultiplicativeOnSections (m n : ℤ) : Prop :=
  ∀ (V : (relativeProj A).scheme.Opens)
    (s : (relativeTwist A m).val.obj (op V)) (t : (relativeTwist A n).val.obj (op V)),
    Hom.app (relativeTwistMap ψ (m + n)).val (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A (m + n)) (op V)
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.mul m n).app (op V) s t)) =
      Hom.app (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n).val
          (op (relativeMapHom ψ ⁻¹ᵁ V))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf
            (ψ.relativeMapDomain.toScheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
            (ψ.relativeMapDomain.toScheme.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj
            (O := (ψ.relativeMapDomain.toScheme.toRingedSpace).presheaf)
            (((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B m))).val
            (((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n))).val))
          (op (relativeMapHom ψ ⁻¹ᵁ V))
          (Hom.app (relativeTwistMap ψ m).val (op (relativeMapHom ψ ⁻¹ᵁ V))
              (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A m) (op V) s) ⊗ₜ
            Hom.app (relativeTwistMap ψ n).val (op (relativeMapHom ψ ⁻¹ᵁ V))
              (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A n) (op V) t)))

/-- **The left-hand side of the square on the pullback-unit image of a pure tensor.** Pushing the
pullback-unit map through the pullback of the product (`pullbackUnit_naturality`) and computing the
product on the sheafification-unit image of a pure tensor
(`SheafOfModules.GradedAlgebra.mulSheaf_unit`) leaves `θ_{m+n}` applied to the pullback-unit image
of the product of the two sections. -/
public theorem relativeTwistMap_mul_lhs_pullbackUnit (m n : ℤ) (V : (relativeProj A).scheme.Opens)
    (s : (relativeTwist A m).val.obj (op V)) (t : (relativeTwist A n).val.obj (op V)) :
    Hom.app ((Scheme.Modules.pullback (relativeMapHom ψ)).map (relativeTwistMul A m n) ≫
          relativeTwistMap ψ (m + n)).val (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
              (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩))).obj
            (relativeTwist A m, relativeTwist A n)) (op V)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf ((relativeProj A).scheme.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf
              ((relativeProj A).scheme.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := ((relativeProj A).scheme.toRingedSpace).presheaf)
              ((relativeTwist A m)).val ((relativeTwist A n)).val)) (op V) (s ⊗ₜ t))) =
      Hom.app (relativeTwistMap ψ (m + n)).val (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A (m + n)) (op V)
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.mul m n).app (op V) s t)) :=
  Eq.trans
    (congrArg (Hom.app (relativeTwistMap ψ (m + n)).val (op (relativeMapHom ψ ⁻¹ᵁ V)))
      (pullbackUnit_naturality (relativeMapHom ψ).toLRSHom.toShHom (relativeTwistMul A m n)
        (op V) (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf ((relativeProj A).scheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
            ((relativeProj A).scheme.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := ((relativeProj A).scheme.toRingedSpace).presheaf)
            ((relativeTwist A m)).val ((relativeTwist A n)).val)) (op V) (s ⊗ₜ t))))
    (congrArg (fun z => Hom.app (relativeTwistMap ψ (m + n)).val
        (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A (m + n)) (op V) z))
      (SheafOfModules.GradedAlgebra.mulSheaf_unit
        (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra m n (op V) s t))

/-- **The right-hand side of the square on the pullback-unit image of a pure tensor.** The Tag 01CD
comparison carries the pullback-unit image of a pure tensor to the pure tensor of the pullback-unit
images (`comparison_pullbackUnit_tensorSheafUnit`), and the tensor product of `θ_m` and `θ_n`
carries that to the pure tensor of their values (`tensorSheaf_map_unit_tmul`). -/
public theorem relativeTwistMap_mul_rhs_pullbackUnit (m n : ℤ) (V : (relativeProj A).scheme.Opens)
    (s : (relativeTwist A m).val.obj (op V)) (t : (relativeTwist A n).val.obj (op V)) :
    Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
            (relativeMapHom ψ).toLRSHom.toShHom).hom.app
              (relativeTwist A m, relativeTwist A n) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
              ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
              (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
            pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n).val
        (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
              (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩))).obj
            (relativeTwist A m, relativeTwist A n)) (op V)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf ((relativeProj A).scheme.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf
              ((relativeProj A).scheme.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := ((relativeProj A).scheme.toRingedSpace).presheaf)
              ((relativeTwist A m)).val ((relativeTwist A n)).val)) (op V) (s ⊗ₜ t))) =
      Hom.app (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n).val
          (op (relativeMapHom ψ ⁻¹ᵁ V))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf
            (ψ.relativeMapDomain.toScheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
            (ψ.relativeMapDomain.toScheme.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj
            (O := (ψ.relativeMapDomain.toScheme.toRingedSpace).presheaf)
            (((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B m))).val
            (((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n))).val))
          (op (relativeMapHom ψ ⁻¹ᵁ V))
          (Hom.app (relativeTwistMap ψ m).val (op (relativeMapHom ψ ⁻¹ᵁ V))
              (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A m) (op V) s) ⊗ₜ
            Hom.app (relativeTwistMap ψ n).val (op (relativeMapHom ψ ⁻¹ᵁ V))
              (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A n) (op V) t))) :=
  Eq.trans
    (congrArg (fun z => Hom.app (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n).val
        (op (relativeMapHom ψ ⁻¹ᵁ V))
        (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
            ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
            (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _)))).val
          (op (relativeMapHom ψ ⁻¹ᵁ V)) z))
      (comparison_pullbackUnit_tensorSheafUnit (relativeMapHom ψ).toLRSHom.toShHom
        (relativeTwist A m) (relativeTwist A n) V s t))
    (congrArg (Hom.app (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n).val
        (op (relativeMapHom ψ ⁻¹ᵁ V)))
      (tensorSheaf_map_unit_tmul ψ.relativeMapDomain.toScheme.toRingedSpace
        (relativeTwistMap ψ m) (relativeTwistMap ψ n) (op (relativeMapHom ψ ⁻¹ᵁ V))
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A m) (op V) s)
        (pullbackUnit (relativeMapHom ψ).toLRSHom.toShHom (relativeTwist A n) (op V) t)))

/-- **The section-level statement implies the graded-algebra clause of Tag 07ZG.** The Tag 01CD
comparison is invertible, so it cancels off the source of the square and leaves the pullback of the
product followed by `θ_{m+n}`; a morphism out of a pullback of a tensor product is determined by
its adjoint transpose on the sheafification-unit images of pure tensors of sections of the base
(`pullbackTensor_hom_ext`); and on such an image the two sides are the two computations above.

This is the relative analogue of the proof of
`Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication`, with the one
step that carries mathematical content left as the hypothesis. -/
public theorem relativeTwistMap_mul_of_sections (m n : ℤ) (h : IsMultiplicativeOnSections ψ m n) :
    pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
          ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
        pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n := by
  refine (cancel_epi ((Stacks.PullbackTensorIso.pullbackTensorIso
    (relativeMapHom ψ).toLRSHom.toShHom).hom.app
      (relativeTwist A m, relativeTwist A n))).mp ?_
  refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun k => k ≫ relativeTwistMap ψ (m + n))
      (comparison_comp_pullbackRelativeTwistMul A (relativeMapHom ψ) m n))) ?_
  refine pullbackTensor_hom_ext (relativeMapHom ψ).toLRSHom.toShHom
    (relativeTwist A m) (relativeTwist A n) _ _ fun V s t => ?_
  exact (relativeTwistMap_mul_lhs_pullbackUnit ψ m n V s t).trans
    ((h V s t).trans (relativeTwistMap_mul_rhs_pullbackUnit ψ m n V s t).symm)

/-- **The graded-algebra clause of Tag 07ZG is local on the pieces of `U(ψ)`, with the restrictions
read as inverse images.** `relativeTwistMap_mul_of_forall_chart` with the restriction functor
traded for the pullback by `restrictFunctor_map_eq_of_pullback_map_eq`; this is the spelling in
which `relativeTwistMap_chart` describes `θ_n` over a piece, hence the spelling the transport of
the absolute clause is written in. Its hypothesis is discharged by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chart_pullback_mul` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulProof.lean`, and this is the reduction Tag 07ZG's
graded-algebra clause is proved through. -/
public theorem relativeTwistMap_mul_of_forall_chart_pullback (m n : ℤ)
    (h : ∀ U : S.affineOpens,
      (Scheme.Modules.pullback (pieceIncl ψ U)).map
          (pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n)) =
        (Scheme.Modules.pullback (pieceIncl ψ U)).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
              ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
              (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
            pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n)) :
    pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
          ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
        pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n :=
  relativeTwistMap_mul_of_forall_chart ψ m n fun U =>
    restrictFunctor_map_eq_of_pullback_map_eq (pieceIncl ψ U) (h U)

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
