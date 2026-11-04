module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAugmentationFormula
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtStalkOverQuotient
public import StacksFrontier.LinearAlgebra.ExteriorPower.HomBaseChangeOnWedges
public import StacksFrontier.RingTheory.Koszul.ContractionDualOnABasis

/-!
# The stalk pairing of the self-Ext algebra against the contraction classes

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. This file pairs
the two halves of the local computation of Stacks 0BQY against one another at a stalk.

The cocycle half says that the composition product of `i` degree-one coordinate-contraction
classes is the class of the `i`-fold iterated contraction. The stalk half says that the iterated
contraction at a stalk is the duality pairing against the wedge of the corresponding coordinate
projections. What is proved here is that the identification of the stalk of a piece of the
self-Ext algebra with `O_x`-linear maps out of an exterior power carries the germ of the
iterated-contraction class to exactly that pairing.

## Main results

* `Stacks.RegularSequence.KoszulChainData.modStalkEquivOfIso_homologyPieceIsoExt_germ`: the germ of
  a class of the self-Ext algebra, written in the shape that
  `Stacks.RegularSequence.KoszulChainData.extStalkEquiv_germ` consumes.

## Implementation notes

**Transports are moved by `refine`/`Eq.trans`, not by `rw`.** The indexing of the Koszul cochain
complex is `(asCochain K.chain).X n = K.chain.X (-n)`, so the degree-`n` term of the chain complex
and the degree-`-n` term of the cochain complex are the same object definitionally and not
syntactically. `rw` matches at `instances` transparency and will not unfold `asCochain`, so a
rewrite whose pattern mentions one spelling fails against a goal carrying the other; `refine` and
`Eq.trans` elaborate at default transparency and do not.

The same applies to the two spellings of the sheaf of rings. An exterior power `A.exteriorPower m`
is a module over `CategoryTheory.Sheaf.toRingCat` of `Rc`, while
`AlgebraicGeometry.RingedSite.internalHomSheaf` of `ringedSite Rc` is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf` of its structure sheaf. The two are definitionally equal,
but `Stacks.SheafOfModules.Tensor.ringSheaf` is an ordinary definition, so a goal mentioning both
is not type-correct at `implicit` transparency and `rw` declines to rewrite in it; the second
`Stacks.SheafOfModules.modStalkEquivOfIso_germ` below is therefore applied by `Eq.trans`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.SheafOfModules.SheafHomStalk Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The germ of a class of the self-Ext algebra, in the shape the stalk identification
consumes.** `Stacks.RegularSequence.KoszulChainData.extStalkEquiv_germ` evaluates `extStalkEquiv`
on an element of the Ext stalk presented as the inverse image of the germ of a local homomorphism
out of an exterior power. The germ of a local section of a piece of the self-Ext algebra is such an
element, the homomorphism being its image under
`Stacks.RegularSequence.KoszulChainData.homIso` read through the identification of the degree-`m`
term of the Koszul complex with the `m`-th exterior power.

This is `homIso_eq` on germs: the two identifications of the piece — up to the Ext sheaf and then
down to the internal Hom sheaf — compose to `homIso`. -/
theorem modStalkEquivOfIso_homologyPieceIsoExt_germ (m : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (c : (commVal (Rc := Rc)
      ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ))).obj (op U)) :
    modStalkEquivOfIso Rc (homologyPieceIsoExt Rc K ((m : ℕ) : ℤ)) x
        (germAt ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ)) U x hx c) =
      (modStalkEquivOfIso Rc (extIsoInternalHomExteriorPower Rc K m) x).symm
        (germAt (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m)
            (quotient Rc (φ := φ))) U x hx
          ((eqToHom (congrArg
              (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M (quotient Rc (φ := φ)))
              (K.chain_X ((m : ℕ) : ℤ)))).val.app (op U)
            ((homIso Rc K ((m : ℕ) : ℤ)).hom.val.app (op U) c))) := by
  rw [LinearEquiv.eq_symm_apply, modStalkEquivOfIso_germ]
  refine Eq.trans
    (modStalkEquivOfIso_germ Rc (extIsoInternalHomExteriorPower Rc K m) x U hx _) ?_
  refine congrArg (germAt _ U x hx) ?_
  refine Eq.trans ?_ (congrArg
    (fun t => (eqToHom (congrArg
        (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M (quotient Rc (φ := φ)))
        (K.chain_X ((m : ℕ) : ℤ)))).val.app (op U) t)
    (congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
      ((_root_.SheafOfModules.Hom.val g).app (op U))))
      (congrArg Iso.hom (homIso_eq Rc K ((m : ℕ) : ℤ)))) c))
  rfl

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The stalk identification of a piece of the self-Ext algebra, on a germ and a basis wedge.**
The germ at `x` of a local section `c` of the degree-`m` piece is carried to the `O_x`-linear map
which, on the basis wedge indexed by `v`, takes the value obtained by applying the homomorphism
`homIso c` to the corresponding basis section of the exterior power.

This is `modStalkEquivOfIso_homologyPieceIsoExt_germ` followed by
`Stacks.RegularSequence.KoszulChainData.extStalkEquiv_germ`, with the transport of the source
argument moved by `AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_source_app`. -/
theorem homologyPieceStalkEquiv_germ (m : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (c : (commVal (Rc := Rc)
      ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ))).obj (op U))
    (v : Fin m → Fin r) :
    homologyPieceStalkEquiv Rc K m x
        (germAt ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ)) U x hx c)
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) m fun k => Pi.single (v k) 1) =
      germAt (quotient Rc (φ := φ)) U x hx
        (((homIso Rc K ((m : ℕ) : ℤ)).hom.val.app (op U) c).app (op (Over.mk (𝟙 U)))
          (eqToHom (congrArg
            (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk (𝟙 U))))
            (K.chain_X ((m : ℕ) : ℤ)).symm) (exteriorBasisSection A U m v))) := by
  refine Eq.trans (congrArg
    (fun z => extStalkEquiv Rc K m x z
      (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) m fun k => Pi.single (v k) 1))
    (modStalkEquivOfIso_homologyPieceIsoExt_germ Rc K m x U hx c)) ?_
  refine Eq.trans (extStalkEquiv_germ Rc K m x U hx _ v) ?_
  refine congrArg (germAt (quotient Rc (φ := φ)) U x hx) ?_
  exact AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_source_app (ringedSite Rc)
    (quotient Rc (φ := φ)) (K.chain_X ((m : ℕ) : ℤ)) _ U _ (op (Over.mk (𝟙 U)))
    (exteriorBasisSection A U m v)

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The stalk identification on the germ of the iterated-contraction class, at a basis wedge.**
Combining `homologyPieceStalkEquiv_germ` with
`Stacks.RegularSequence.KoszulChainData.homIso_app_apply_iteratedContractionClassOn`: the value is
the germ of the augmentation applied to the iterated contraction of the basis section. Everything
on the right is a section of the Koszul complex and its augmentation; no Ext sheaf, no cohomology
class and no internal Hom complex remain. -/
theorem homologyPieceStalkEquiv_germ_iteratedContractionClassOn (m : ℕ)
    (j : Fin (m + 1) → ULift.{u} (Fin r)) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (v : Fin (m + 1) → Fin r) :
    homologyPieceStalkEquiv Rc K (m + 1) x
        (germAt ((homologyGradedAlgebra Rc (cochain Rc K)).piece (((m + 1 : ℕ) : ℕ) : ℤ)) U x hx
          (iteratedContractionClassOn Rc K m j (op U)))
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) (m + 1)
          fun k => Pi.single (v k) 1) =
      germAt (quotient Rc (φ := φ)) U x hx
        (eqToHom (congrArg
            (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk (𝟙 U))))
            (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
                (quotient Rc (φ := φ))).X (((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))
                = quotient Rc (φ := φ) from by rw [sub_self]; rfl))
          (((augSingle Rc K).f
                (((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))).val.app (op U)
            ((K.tupleCoordKoszulDOf (m + 1) (fun k => j k.rev)
                (show -(((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) + ((m + 1 : ℕ) : ℤ)
                  = -(-((m + 1 : ℕ) : ℤ)) by push_cast; ring)).val.app (op U)
              (eqToHom (congrArg
                  (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk (𝟙 U))))
                  (congrArg K.chain.X (neg_neg ((m + 1 : ℕ) : ℤ))).symm)
                (eqToHom (congrArg
                  (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk (𝟙 U))))
                  (K.chain_X (((m + 1 : ℕ) : ℕ) : ℤ)).symm)
                  (exteriorBasisSection A U (m + 1) v)))))) := by
  refine Eq.trans (homologyPieceStalkEquiv_germ Rc K (m + 1) x U hx
    (iteratedContractionClassOn Rc K m j (op U)) v) ?_
  exact congrArg (germAt (quotient Rc (φ := φ)) U x hx)
    (homIso_app_apply_iteratedContractionClassOn Rc K m j U U (𝟙 U) _)

end Stacks.RegularSequence.KoszulChainData

end
