module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair

/-!
# The homomorphism of stalk rings of a pullback, on germs

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, let `Φ` be a point of `C` and
let `Ψ` be a point of `D` whose stalk functor on sheaves of sets is the inverse image along `f`
followed by the stalk functor of `Φ`.  The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings along which
Stacks 05V5 extends scalars, `Stacks.Sheaves.StalkPullback.stalkRingMap`, is built from the
comparison of stalk functors on sheaves of *sets* and is therefore opaque on germs until that
comparison is unwound.  This file unwinds it: the germ at a lift of `Ψ` of a section of `𝒪'`
goes to the germ obtained by transporting it through the comparison of stalk functors and
through the fibre at `Φ` of the inverse-image form `f⁻¹𝒪' ⟶ 𝒪` of the structure map, read back
into the `CommRingCat`-valued stalk of `𝒪`.

## Main results

* `Stacks.commRingPresheafFiberIso_hom_toPresheafFiber`: the comparison of the `RingCat`-valued
  stalk of the presheaf of rings underlying a presheaf of commutative rings with its
  `CommRingCat`-valued stalk carries a germ to the germ of the same section.
* `Stacks.Sheaves.StalkPullback.commRingStalkEquiv_toPresheafFiber`: the isomorphism
  `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings on a germ.
* `Stacks.Sheaves.StalkPullback.stalkRingMap_toPresheafFiber`: the homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ`
  on a germ.

## Implementation notes

The three comparisons that `Stacks.Sheaves.StalkPullback.stalkRingMap` is composed of each carry
germs to germs, so the computation is a chain of three germ identities: the `RingCat`-versus-
`CommRingCat` comparison at either end, which is
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app`; the
comparison of Stacks 05V1 between the stalk of a sheaf of rings and the stalk of its underlying
sheaf of sets, which is `Stacks.Sheaves.StalkTransport.ringStalkComparison_ringGerm`; and the
stalk of the structure map, which is
`Stacks.Sheaves.StalkPullback.fSharpStalk_commRingPresheafFiberIso_ringStalkComparison`.

What is left on the right-hand side is the transport of the germ through the comparison of
stalk functors on sheaves of sets.  That transport is not computable in this generality — it is
the datum `e` — so the formula is stated with it in place; at a concrete morphism of ringed
topoi it is what a chartwise computation evaluates.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.StalkTransport

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

noncomputable section

universe w v u v' u' t

namespace Stacks

/-- **The two readings of the stalk of a presheaf of commutative rings agree on germs.**  The
comparison of the `RingCat`-valued stalk of the presheaf of rings underlying `O` with the
`CommRingCat`-valued stalk of `O` carries the germ at a neighbourhood of the point of a section
of `O` to the germ of the same section. -/
theorem commRingPresheafFiberIso_hom_toPresheafFiber {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
    (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) (u : Φ.fiber.obj U) (s : O.obj (op U)) :
    (commRingPresheafFiberIso Φ O).hom.hom
        (Φ.toPresheafFiber U u (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) s) =
      Φ.toPresheafFiber U u O s :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (F := forget₂ CommRingCat.{w} RingCat.{w}) U u O) s

end Stacks

namespace Stacks.Sheaves.StalkPullback

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings, on a germ.**  It carries the germ at a
lift `v` of `Ψ` of a section of `𝒪'` to the germ of the same section read through the comparison
of stalk functors on sheaves of sets. -/
theorem commRingStalkEquiv_toPresheafFiber (V : Y.C) (v : Ψ.fiber.obj V)
    (s : Y.O.obj.obj (op V)) :
    commRingStalkEquiv f Φ Ψ e (Ψ.toPresheafFiber V v Y.O.obj s) =
      (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).hom.hom
        (ringStalkComparison Φ (inverseImageStructureRing f)
          (e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (Ψ.toPresheafFiber V v
              (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj s))) := by
  have hA : (Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv
        (ringStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (Ψ.toPresheafFiber V v
            (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj s)) =
      Ψ.toPresheafFiber V v Y.O.obj s := by
    refine Eq.trans (congrArg
      (fun z => (Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv z)
      (ringStalkComparison_ringGerm Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V v s)) ?_
    exact Stacks.commRingPresheafFiberIso_hom_toPresheafFiber Ψ Y.O.obj V v s
  refine Eq.trans (congrArg (fun z =>
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).hom.hom
      (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e z))
    ((RingEquiv.symm_apply_eq _).2 hA.symm)) ?_
  exact congrArg (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).hom.hom
    (stalkRingMap_ringStalkComparison f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings, on a germ.**  It carries the germ at a lift
`v` of `Ψ` of a section of `𝒪'` to the germ obtained by transporting that germ through the
comparison of stalk functors on sheaves of sets and through the fibre at `Φ` of the
inverse-image form `f⁻¹𝒪' ⟶ 𝒪` of the structure map of `f`. -/
theorem stalkRingMap_toPresheafFiber (V : Y.C) (v : Ψ.fiber.obj V) (s : Y.O.obj.obj (op V)) :
    stalkRingMap f Φ Ψ e (Ψ.toPresheafFiber V v Y.O.obj s) =
      (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
        (ringStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((Φ.sheafFiber (A := Type w)).map
              ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage)
            (e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (Ψ.toPresheafFiber V v
                (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj s)))) := by
  refine Eq.trans (congrArg (fSharpStalk f Φ)
    (commRingStalkEquiv_toPresheafFiber f Φ Ψ e V v s)) ?_
  exact fSharpStalk_commRingPresheafFiberIso_ringStalkComparison f Φ _

end Stacks.Sheaves.StalkPullback

end

end
