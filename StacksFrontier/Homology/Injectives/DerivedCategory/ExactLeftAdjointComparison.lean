module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel

/-!
# Comparing composites of right derived functors through their exact left adjoints

Consider a square of abelian categories and additive functors

```
𝒬_Y --ι_Y--> ℳ_Y
 |            |
q^*          p^*
 v            v
𝒬_X --ι_X--> ℳ_X
```

commuting up to an isomorphism `q^* ⋙ ι_X ≅ ι_Y ⋙ p^*`, in which all four functors are exact and
each has a right adjoint: `ι_X ⊣ C_X`, `ι_Y ⊣ C_Y`, `p^* ⊣ p_*` and `q^* ⊣ q_*`.  Then, at
arbitrary chosen models of the four derived categories, the two composites of total right derived
functors `Rp_* ⋙ RC_Y` and `RC_X ⋙ Rq_*` are isomorphic.

The argument is that of [Stacks, Tag 08GZ].  An exact functor induces a functor of derived
categories with no derivation, and that functor is left adjoint to the total right derived
functor of its right adjoint by [Stacks, Tag 09T5]
(`Stacks.DerivedModel.adjunctionOfExact`).  So both composites are right adjoint to a composite
of induced functors `D(𝒬_Y) ⥤ D(ℳ_X)`; the two composites of induced functors agree because the
square commutes already before deriving, and a right adjoint is unique up to a canonical
isomorphism.

## Main results

* `Stacks.DerivedModel.rightDerivedCompIsoOfExactLeftAdjoints`: the isomorphism
  `Rp_* ⋙ RC_Y ≅ RC_X ⋙ Rq_*`.

## References

* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedModel

variable {MX MY QCX QCY : Type*} [Category* MX] [Category* MY] [Category* QCX] [Category* QCY]
  [Abelian MX] [Abelian MY] [Abelian QCX] [Abelian QCY]
  [HasDerivedCategory MX] [HasDerivedCategory MY] [HasDerivedCategory QCX] [HasDerivedCategory QCY]
  [IsGrothendieckAbelian MX] [IsGrothendieckAbelian MY] [IsGrothendieckAbelian QCX]
  {ιX : QCX ⥤ MX} [ιX.Additive] [PreservesFiniteLimits ιX] [PreservesFiniteColimits ιX]
  {ιY : QCY ⥤ MY} [ιY.Additive] [PreservesFiniteLimits ιY] [PreservesFiniteColimits ιY]
  {pb : MY ⥤ MX} [pb.Additive] [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {qpb : QCY ⥤ QCX} [qpb.Additive] [PreservesFiniteLimits qpb] [PreservesFiniteColimits qpb]
  {CX : MX ⥤ QCX} [CX.Additive] {CY : MY ⥤ QCY} [CY.Additive]
  {pf : MX ⥤ MY} [pf.Additive] {qpf : QCX ⥤ QCY} [qpf.Additive]

/-- **Comparing composites of right derived functors through their exact left adjoints.**  Let
`q^* ⋙ ι_X ≅ ι_Y ⋙ p^*` be a square of exact functors of abelian categories, with right adjoints
`ι_X ⊣ C_X`, `ι_Y ⊣ C_Y`, `p^* ⊣ p_*`, `q^* ⊣ q_*`, the categories `ℳ_X`, `ℳ_Y`, `𝒬_X` being
Grothendieck abelian.  Then for arbitrary models of the four derived categories and arbitrary
total right derived functors `Rp_*`, `RC_X`, `RC_Y`, `Rq_*` relative to them, there is a natural
isomorphism `Rp_* ⋙ RC_Y ≅ RC_X ⋙ Rq_*`.

Both sides are right adjoint to the same functor `D(𝒬_Y) ⥤ D(ℳ_X)`: by
`Stacks.DerivedModel.adjunctionOfExact` the functors induced by `ι_Y` and `p^*` are left adjoint
to `RC_Y` and `Rp_*`, and those induced by `q^*` and `ι_X` to `Rq_*` and `RC_X`; the two
composite left adjoints agree, as both are induced by the two sides of the commutative square. -/
def rightDerivedCompIsoOfExactLeftAdjoints (e : qpb ⋙ ιX ≅ ιY ⋙ pb)
    (adjX : ιX ⊣ CX) (adjY : ιY ⊣ CY) (adjf : pb ⊣ pf) (adjq : qpb ⊣ qpf)
    (QMX : CochainComplex MX ℤ ⥤ DerivedCategory MX)
    [QMX.IsLocalization (HomologicalComplex.quasiIso MX (ComplexShape.up ℤ))]
    (QMY : CochainComplex MY ℤ ⥤ DerivedCategory MY)
    [QMY.IsLocalization (HomologicalComplex.quasiIso MY (ComplexShape.up ℤ))]
    (QX : CochainComplex QCX ℤ ⥤ DerivedCategory QCX)
    [QX.IsLocalization (HomologicalComplex.quasiIso QCX (ComplexShape.up ℤ))]
    (QY : CochainComplex QCY ℤ ⥤ DerivedCategory QCY)
    [QY.IsLocalization (HomologicalComplex.quasiIso QCY (ComplexShape.up ℤ))]
    (Rf : DerivedCategory MX ⥤ DerivedCategory MY)
    (RfUnit : pf.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QMY ⟶ QMX ⋙ Rf)
    [Rf.IsRightDerivedFunctor RfUnit (HomologicalComplex.quasiIso MX (ComplexShape.up ℤ))]
    (RQX : DerivedCategory MX ⥤ DerivedCategory QCX)
    (RQXUnit : CX.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QX ⟶ QMX ⋙ RQX)
    [RQX.IsRightDerivedFunctor RQXUnit (HomologicalComplex.quasiIso MX (ComplexShape.up ℤ))]
    (RQY : DerivedCategory MY ⥤ DerivedCategory QCY)
    (RQYUnit : CY.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶ QMY ⋙ RQY)
    [RQY.IsRightDerivedFunctor RQYUnit (HomologicalComplex.quasiIso MY (ComplexShape.up ℤ))]
    (Φ : DerivedCategory QCX ⥤ DerivedCategory QCY)
    (ΦUnit : qpf.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶ QX ⋙ Φ)
    [Φ.IsRightDerivedFunctor ΦUnit (HomologicalComplex.quasiIso QCX (ComplexShape.up ℤ))] :
    Rf ⋙ RQY ≅ RQX ⋙ Φ := by
  let adjRQX := adjunctionOfExact ιX QMX QX adjX RQX RQXUnit
  let adjRQY := adjunctionOfExact ιY QMY QY adjY RQY RQYUnit
  let adjRf := adjunctionOfExact pb QMX QMY adjf Rf RfUnit
  let adjPhi := adjunctionOfExact qpb QX QY adjq Φ ΦUnit
  let c := ComplexShape.up ℤ
  let QtXall := homotopyLocalization QMX
  let L1 := derivedFunctorOfExact ιY QMY QY ⋙ derivedFunctorOfExact pb QMX QMY
  let L2 := derivedFunctorOfExact qpb QX QY ⋙ derivedFunctorOfExact ιX QMX QX
  let H1 := (ιY.mapHomotopyCategory c ⋙ pb.mapHomotopyCategory c) ⋙ QtXall
  let H2 := (qpb.mapHomotopyCategory c ⋙ ιX.mapHomotopyCategory c) ⋙ QtXall
  let h1 : homotopyLocalization QY ⋙ L1 ≅ H1 :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedFunctorOfExactFac ιY QMY QY) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedFunctorOfExactFac pb QMX QMY) ≪≫
      (Functor.associator _ _ _).symm
  let h2 : homotopyLocalization QY ⋙ L2 ≅ H2 :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedFunctorOfExactFac qpb QX QY) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedFunctorOfExactFac ιX QMX QX) ≪≫
      (Functor.associator _ _ _).symm
  let eBase : H2 ≅ H1 :=
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e c) QtXall ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (ιY ⋙ pb)) c).symm
        QtXall
  let W := HomotopyCategory.quasiIso QCY c
  letI : Localization.Lifting (homotopyLocalization QY) W H1 L1 := ⟨h1⟩
  letI : Localization.Lifting (homotopyLocalization QY) W H2 L2 := ⟨h2⟩
  let eLeft : L2 ≅ L1 := Localization.liftNatIso (homotopyLocalization QY) W H2 H1 L2 L1 eBase
  exact (adjRQY.comp adjRf).rightAdjointUniq ((adjPhi.comp adjRQX).ofNatIsoLeft eLeft)

end Stacks.DerivedModel

end
