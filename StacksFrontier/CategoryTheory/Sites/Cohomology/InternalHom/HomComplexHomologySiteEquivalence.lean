module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence

/-!
# The cohomology sheaves of an internal Hom complex are invariant under an equivalence of sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `e : C ≌ D`, `φ`, `ψ` be an equivalence of
ringed sites in the sense of
`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`. The transport `φ_*` of sheaves of
modules is an equivalence, hence exact, so it commutes with the cohomology of a complex, and it
carries the internal Hom complex to the internal Hom complex of the transports. Composing the
two:

`φ_* Hⁿ(SheafHom(K, M)) ≅ Hⁿ(SheafHom(φ_* K, φ_* M))`.

This is the statement of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/HomComplexHomologySliceRestriction.lean`
with an arbitrary equivalence of ringed sites in place of restriction to a slice site. As
there, these are the *pieces* of the graded algebra that the composition product is built on —
the cohomology sheaves of the internal Hom complex itself, not the Ext sheaves of the derived
internal Hom.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso`: the comparison above.
* `AlgebraicGeometry.RingedSite.sheafHomCyclesSiteEquivMap`: the same comparison with cycles in
  place of cohomology.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso_hom`: the comparison written out as
  the composite of the two isomorphisms it is built from.
* `AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso_natural`: it is natural in both
  variables, which is what makes it *the* comparison rather than an unspecified isomorphism of
  the two sheaves.
* `AlgebraicGeometry.RingedSite.map_homologyπ_sheafHomHomologySiteEquivIso` and its form on
  local sections `AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso_hom_app_homologyπ`:
  **the comparison carries the class of a cocycle to the class of the corresponding cocycle.**
  Without this an isomorphism of cohomology sheaves says nothing about any particular section of
  either.
* `AlgebraicGeometry.RingedSite.sheafHomCyclesSiteEquivMap_iCycles` and
  `AlgebraicGeometry.RingedSite.sheafHomCyclesSiteEquivMap_iCycles_app`: that comparison on
  cycles, read inside the complex, where it is the chain-level transport.

## Implementation notes

Nothing here is proved twice. Exactness of the transport is
`AlgebraicGeometry.RingedSite.pushforward_preservesFiniteLimits` together with
`AlgebraicGeometry.RingedSite.pushforward_preservesFiniteColimits`, both of which come from the
transport being the functor of `AlgebraicGeometry.RingedSite.modulesEquiv`; that an exact
additive functor commutes with the cohomology of a complex is
`Stacks.Homology.exactHomologyIso`; and the comparison of the internal Hom complexes is
`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`. The naturality statement is the
naturality of each of those two in turn, so it is an identity of composites and not a
computation.

The exactness is supplied as a local instance rather than found by synthesis, for the reason
recorded in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SheafHomSiteEquivalence.lean`: the
witness needs `ψ`, `H₁` and `H₂`, which typeclass synthesis cannot recover from a statement
mentioning only `φ`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The cohomology sheaves of an internal Hom complex are invariant under an equivalence of
ringed sites.** For complexes `K`, `M` of `O_D`-modules and an integer `n`, transporting the
cohomology sheaf `Hⁿ(SheafHom(K, M))` along the equivalence gives the cohomology sheaf
`Hⁿ(SheafHom(φ_* K, φ_* M))` of the internal Hom complex of the transports.

It is `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso` under the degree-`n` cohomology
functor, preceded by the comparison which identifies the transport of a cohomology sheaf with
the cohomology sheaf of the transport, the transport being exact. -/
def sheafHomHomologySiteEquivIso
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (SheafOfModules.pushforward.{u} φ).obj ((sheafHomComplex X K M).obj.homology n) ≅
      (sheafHomComplex Y ((pushComplex eqv φ).obj K)
        ((pushComplex eqv φ).obj M)).obj.homology n :=
  ((Stacks.Homology.exactHomologyIso (SheafOfModules.pushforward.{u} φ) n).app
      (sheafHomComplex X K M).obj).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M)

/-- The comparison, spelled out: the inverse of the exactness comparison for the transport,
followed by the degree-`n` cohomology of the chain-level transport. -/
theorem sheafHomHomologySiteEquivIso_hom
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K M n).hom =
      (Stacks.Homology.exactHomologyIso (SheafOfModules.pushforward.{u} φ) n).inv.app
          (sheafHomComplex X K M).obj ≫
        HomologicalComplex.homologyMap (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M).hom n :=
  rfl

/-- **The comparison is natural in both variables.** Transporting the map of cohomology sheaves
induced by `f : K' ⟶ K` and `g : M ⟶ M'` gives the map induced by the transports of `f` and
`g`. -/
theorem sheafHomHomologySiteEquivIso_natural
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K' ⟶ K) (g : M ⟶ M') (n : ℤ) :
    (SheafOfModules.pushforward.{u} φ).map
          (HomologicalComplex.homologyMap (homMap X f g) n) ≫
        (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K' M' n).hom =
      (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K M n).hom ≫
        HomologicalComplex.homologyMap
          (homMap Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g)) n := by
  have hnat : (SheafOfModules.pushforward.{u} φ).map
          (HomologicalComplex.homologyMap (homMap X f g) n) ≫
        (Stacks.Homology.exactHomologyIso (SheafOfModules.pushforward.{u} φ) n).inv.app
            (sheafHomComplex X K' M').obj =
      (Stacks.Homology.exactHomologyIso (SheafOfModules.pushforward.{u} φ) n).inv.app
            (sheafHomComplex X K M).obj ≫
        HomologicalComplex.homologyMap ((pushComplex eqv φ).map (homMap X f g)) n :=
    (Stacks.Homology.exactHomologyIso (SheafOfModules.pushforward.{u} φ) n).inv.naturality
      (homMap X f g)
  rw [sheafHomHomologySiteEquivIso_hom, sheafHomHomologySiteEquivIso_hom, ← Category.assoc,
    hnat, Category.assoc, Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, siteEquivSheafHomComplexIso_natural eqv φ ψ H₁ H₂ f g]

/-! ### The comparison on a class of a cocycle

The comparison is an isomorphism of cohomology sheaves and so says nothing on its own about a
*section* of one of them. What a consumer computing with local sections needs is the value of
the comparison on the class of a cocycle, and that is what follows. -/

/-- **The cycles of an internal Hom complex are invariant under an equivalence of ringed
sites.** The comparison is built exactly as
`AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso`, with cycles in place of cohomology:
the exactness comparison of the transport on the degree-`n` short complex, followed by the
degree-`n` cycles of the chain-level transport. -/
def sheafHomCyclesSiteEquivMap
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (SheafOfModules.pushforward.{u} φ).obj ((sheafHomComplex X K M).obj.cycles n) ⟶
      (sheafHomComplex Y ((pushComplex eqv φ).obj K)
        ((pushComplex eqv φ).obj M)).obj.cycles n :=
  (((sheafHomComplex X K M).obj.sc n).mapCyclesIso (SheafOfModules.pushforward.{u} φ)).inv ≫
    HomologicalComplex.cyclesMap (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M).hom n

/-- **The comparison on cycles, read inside the complex.** A cocycle and the cocycle it is
carried to have the same image in the complex, up to the chain-level transport. -/
theorem sheafHomCyclesSiteEquivMap_iCycles
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    sheafHomCyclesSiteEquivMap eqv φ ψ H₁ H₂ K M n ≫
        (sheafHomComplex Y ((pushComplex eqv φ).obj K)
          ((pushComplex eqv φ).obj M)).obj.iCycles n =
      (SheafOfModules.pushforward.{u} φ).map ((sheafHomComplex X K M).obj.iCycles n) ≫
        (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M).hom.f n := by
  have hi : (((sheafHomComplex X K M).obj.sc n).mapCyclesIso
          (SheafOfModules.pushforward.{u} φ)).inv ≫
        ((pushComplex eqv φ).obj (sheafHomComplex X K M).obj).iCycles n =
      (SheafOfModules.pushforward.{u} φ).map ((sheafHomComplex X K M).obj.iCycles n) :=
    (Iso.inv_comp_eq _).2
      (ShortComplex.mapCyclesIso_hom_iCycles ((sheafHomComplex X K M).obj.sc n)
        (SheafOfModules.pushforward.{u} φ)).symm
  erw [sheafHomCyclesSiteEquivMap, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, hi]

/-- **The comparison of cohomology sheaves carries the class of a cocycle to the class of the
corresponding cocycle.** This is the compatibility of
`AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso` with
`HomologicalComplex.homologyπ`, which neither factor of that comparison had. -/
theorem map_homologyπ_sheafHomHomologySiteEquivIso
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (SheafOfModules.pushforward.{u} φ).map ((sheafHomComplex X K M).obj.homologyπ n) ≫
        (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K M n).hom =
      sheafHomCyclesSiteEquivMap eqv φ ψ H₁ H₂ K M n ≫
        (sheafHomComplex Y ((pushComplex eqv φ).obj K)
          ((pushComplex eqv φ).obj M)).obj.homologyπ n := by
  rw [sheafHomHomologySiteEquivIso_hom, ← Category.assoc,
    Stacks.Homology.map_homologyπ_exactHomologyIso_inv_app]
  erw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  exact (Category.assoc _ _ _).symm

/-- **The comparison on a class of a cocycle, on local sections.** For an object `V` of `C` and
a degree-`n` cocycle `x` of `SheafHom(K, M)` over `e(V)`, the comparison sends the class of `x`
to the class of the cocycle `x` is carried to. -/
theorem sheafHomHomologySiteEquivIso_hom_app_homologyπ
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (V : Y.C)
    (x : ((sheafHomComplex X K M).obj.cycles n).val.obj (op (eqv.functor.obj V))) :
    ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K M n).hom.val.app (op V))
        (((sheafHomComplex X K M).obj.homologyπ n).val.app (op (eqv.functor.obj V)) x) =
      ((sheafHomComplex Y ((pushComplex eqv φ).obj K)
            ((pushComplex eqv φ).obj M)).obj.homologyπ n).val.app (op V)
        ((sheafHomCyclesSiteEquivMap eqv φ ψ H₁ H₂ K M n).val.app (op V) x) :=
  congrArg (fun z => (SheafOfModules.Hom.val z).app (op V) x)
    (map_homologyπ_sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ K M n)

/-- **The comparison on cycles, read inside the complex, on local sections.** -/
theorem sheafHomCyclesSiteEquivMap_iCycles_app
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (V : Y.C)
    (x : ((sheafHomComplex X K M).obj.cycles n).val.obj (op (eqv.functor.obj V))) :
    (((sheafHomComplex Y ((pushComplex eqv φ).obj K)
            ((pushComplex eqv φ).obj M)).obj.iCycles n).val.app (op V))
        ((sheafHomCyclesSiteEquivMap eqv φ ψ H₁ H₂ K M n).val.app (op V) x) =
      ((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M).hom.f n).val.app (op V)
        (((sheafHomComplex X K M).obj.iCycles n).val.app (op (eqv.functor.obj V)) x) :=
  congrArg (fun z => (SheafOfModules.Hom.val z).app (op V) x)
    (sheafHomCyclesSiteEquivMap_iCycles eqv φ ψ H₁ H₂ K M n)

end AlgebraicGeometry.RingedSite

end
