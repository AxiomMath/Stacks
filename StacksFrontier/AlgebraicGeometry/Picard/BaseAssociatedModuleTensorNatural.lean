module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransport
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitePicardComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# The tensor comparison of the associated-module functor is natural

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` is Stacks 03EL at the morphism of
ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, packaged as the object-level tensor comparison
`Stacks.SheafOfModules.Picard.TensorIso` of the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks
03DU (4).  That packaging asks for no naturality, and the transport of Picard groups in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean` uses none.  The transport of
*tensor powers* is only natural in the invertible module when the tensor comparison is
(`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural`), and this file discharges that
datum for this comparison, at every one of the five topologies and with no hypothesis on `S`.

It holds because the comparison is assembled from natural transformations and from nothing else:
`Stacks.SheafOfModules.pullbackTensorIso` is Stacks 03EL for the pullback of modules along an
arbitrary morphism of ringed topoi, *as a natural isomorphism of bifunctors*, and
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` identifies that pullback
with `𝓕 ↦ 𝓕^a`, *as a natural isomorphism of functors*.  The square to prove is therefore the
horizontal paste of three squares: naturality of the second isomorphism's inverse, naturality of
the first, and naturality of the second again in each of the two arguments.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.basePullbackModules` and
  `AlgebraicGeometry.BigFppfOver.basePullbackTensorIso`: the pullback of sheaves of modules along
  the morphism of ringed topoi attached to `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` and Stacks 03EL for
  it, named so that the three squares below can be written down.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso_hom`: the comparison read as the
  composite of its three constituents, by `rfl`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso_naturality`: **the naturality
  square of the comparison**, at the bifunctor spelling of the two tensor products.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`: **the tensor comparison
  of `𝓕 ↦ 𝓕^a` is natural**, in the packaging
  `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` that the transport of tensor
  powers consumes.

## Implementation notes

The three constituents also assemble into a single natural isomorphism of bifunctors, whiskering
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` on the left and the product
of two copies of it on the right, and the square below is then the naturality of that one natural
transformation.  That is **not** how it is proved here: identifying the component of such a
whiskered composite with `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorBifunctorIso`
is a `whnf` problem that does not finish inside the heartbeat budget, for the reason recorded in
the implementation notes of `StacksFrontier/AlgebraicGeometry/Picard/BaseSitePicardComparison.lean`
— checking a composite isomorphism of sheaves of modules against an independently declared type
is expensive.  Pasting the three squares by hand costs three `have`s and no `whnf` of that kind.

Once `baseAssociatedModuleTensorIso_hom` has replaced both comparisons by their three
constituents, the square is assembled by a chain of `Eq.trans`, `congrArg` and
`CategoryTheory.Category.assoc` **as terms**, not by `rw` or `simp`.  The composites to
reassociate straddle three categories of sheaves of modules whose ring sheaves are spelled
differently — the one of the associated-module functor, the one of the pullback of modules, and
the one of `AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor` — so a single composite
carries two `CategoryTheory.Category` instances that agree only at default transparency.
`CategoryTheory.Category.assoc` wants one instance for both of its compositions, which is a match
`rw` and `simp` will not make; a term, whose placeholders are solved by `isDefEq` at default
transparency, does.

The source and target of every `CategoryTheory.Functor.map` of a tensor bifunctor are given
explicitly as `X :=` and `Y :=`.  Left to be inferred they are metavariables, and the elaborator
then tries to unfold a tensor product sheaf against one, which does not terminate inside the
budget.

Only the last statement, `baseAssociatedModuleTensorIso'_natural`, crosses from the bifunctor
spelling of the two tensor products — `Stacks.SheafOfModules.Tensor.sheafTensor` read on pairs
through `CategoryTheory.Functor.uncurry`, the one Stacks 03EL is stated with — to the curried
spelling `((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).obj N` of Tag 01CA that
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` is written at.  The two are the same
sheaf of modules by `rfl`, as `AlgebraicGeometry.BigFppfOver.tensorSheafBifunctorZariski_obj` and
`AlgebraicGeometry.BigFppfOver.tensorSheafBifunctorBase_obj` record, and the crossing is one
application of the square above.

No `@[stacks]` attribute is claimed: Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso`, and this module only records that the instance of it
used for the big sites is natural.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback of sheaves of modules along the morphism of ringed topoi attached to
`((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, which
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` identifies with the
associated-module functor of Stacks 03DU (4). -/
public abbrev basePullbackModules (τ : SiteKind) :=
  pullbackModules.{u, u, u, u + 1, u, u} (baseRingedToposModulesHom B S hS τ)

/-- Stacks 03EL for that pullback of modules: a natural isomorphism of bifunctors. -/
public abbrev basePullbackTensorIso (τ : SiteKind) :=
  Stacks.SheafOfModules.pullbackTensorIso (baseRingedToposModulesHom B S hS τ)

/-- **The comparison of Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, read as the composite of
its three constituents**: the inverse of the identification of `𝓕 ↦ 𝓕^a` with the pullback of
modules, Stacks 03EL for that pullback, and the identification again in each argument. -/
public theorem baseAssociatedModuleTensorIso_hom (τ : SiteKind) (M N : S.Modules) :
    (baseAssociatedModuleTensorBifunctorIso B S hS τ M N).hom =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
          ((tensorSheafBifunctorZariski S).obj (M, N)) ≫
        (basePullbackTensorIso B S hS τ).hom.app (M, N) ≫
          (tensorSheafBifunctorBase B S hS τ).map
            (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
            (Y := ((baseAssociatedModule B S hS τ).obj M,
              (baseAssociatedModule B S hS τ).obj N))
            ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M,
              (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N) := rfl

/-- **The naturality square of Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`**, at the bifunctor
spelling of the two tensor products: the associated module of a tensor product is the tensor
product of the associated modules, *naturally* in both arguments. -/
public theorem baseAssociatedModuleTensorIso_naturality (τ : SiteKind)
    {M N M' N' : S.Modules} (e : M ≅ M') (f : N ≅ N') :
    (baseAssociatedModule B S hS τ).map ((tensorSheafBifunctorZariski S).map
          (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)) ≫
        (baseAssociatedModuleTensorBifunctorIso B S hS τ M' N').hom =
      (baseAssociatedModuleTensorBifunctorIso B S hS τ M N).hom ≫
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N))
          (Y := ((baseAssociatedModule B S hS τ).obj M', (baseAssociatedModule B S hS τ).obj N'))
          ((baseAssociatedModule B S hS τ).map e.hom,
            (baseAssociatedModule B S hS τ).map f.hom) := by
  -- Paste the squares of the three constituents: `h1` is naturality of the inverse of
  -- `pullbackModulesIsoBaseAssociatedModule`, `h2` is naturality of `pullbackTensorIso`, and `h3`
  -- is naturality of `pullbackModulesIsoBaseAssociatedModule` in each of the two arguments,
  -- carried inside the tensor bifunctor by its functoriality.
  have h1 : (baseAssociatedModule B S hS τ).map ((tensorSheafBifunctorZariski S).map
          (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)) ≫
        (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
          ((tensorSheafBifunctorZariski S).obj (M', N')) =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
          ((tensorSheafBifunctorZariski S).obj (M, N)) ≫
        (basePullbackModules B S hS τ).map ((tensorSheafBifunctorZariski S).map
          (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)) :=
    (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.naturality _
  have h2 : (basePullbackModules B S hS τ).map ((tensorSheafBifunctorZariski S).map
          (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)) ≫
        (basePullbackTensorIso B S hS τ).hom.app (M', N') =
      (basePullbackTensorIso B S hS τ).hom.app (M, N) ≫
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
          (Y := ((basePullbackModules B S hS τ).obj M', (basePullbackModules B S hS τ).obj N'))
          ((basePullbackModules B S hS τ).map e.hom,
            (basePullbackModules B S hS τ).map f.hom) :=
    (basePullbackTensorIso B S hS τ).hom.naturality (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)
  have h3 : (tensorSheafBifunctorBase B S hS τ).map
          (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
          (Y := ((basePullbackModules B S hS τ).obj M', (basePullbackModules B S hS τ).obj N'))
          ((basePullbackModules B S hS τ).map e.hom,
            (basePullbackModules B S hS τ).map f.hom) ≫
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((basePullbackModules B S hS τ).obj M', (basePullbackModules B S hS τ).obj N'))
          (Y := ((baseAssociatedModule B S hS τ).obj M',
            (baseAssociatedModule B S hS τ).obj N'))
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M',
            (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N') =
      (tensorSheafBifunctorBase B S hS τ).map
          (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
          (Y := ((baseAssociatedModule B S hS τ).obj M,
            (baseAssociatedModule B S hS τ).obj N))
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M,
            (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N) ≫
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N))
          (Y := ((baseAssociatedModule B S hS τ).obj M',
            (baseAssociatedModule B S hS τ).obj N'))
          ((baseAssociatedModule B S hS τ).map e.hom,
            (baseAssociatedModule B S hS τ).map f.hom) := by
    rw [← (tensorSheafBifunctorBase B S hS τ).map_comp,
      ← (tensorSheafBifunctorBase B S hS τ).map_comp]
    refine congrArg (fun z => (tensorSheafBifunctorBase B S hS τ).map
      (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
      (Y := ((baseAssociatedModule B S hS τ).obj M',
        (baseAssociatedModule B S hS τ).obj N')) z) ?_
    change ((basePullbackModules B S hS τ).map e.hom ≫
            (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M',
          (basePullbackModules B S hS τ).map f.hom ≫
            (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N') = _
    rw [(pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.naturality e.hom,
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.naturality f.hom]
    rfl
  have mid : ((baseAssociatedModule B S hS τ).map ((tensorSheafBifunctorZariski S).map
            (X := (M, N)) (Y := (M', N')) (e.hom, f.hom)) ≫
          (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
            ((tensorSheafBifunctorZariski S).obj (M', N'))) ≫
        (basePullbackTensorIso B S hS τ).hom.app (M', N') =
      ((pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
            ((tensorSheafBifunctorZariski S).obj (M, N)) ≫
          (basePullbackTensorIso B S hS τ).hom.app (M, N)) ≫
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
          (Y := ((basePullbackModules B S hS τ).obj M', (basePullbackModules B S hS τ).obj N'))
          ((basePullbackModules B S hS τ).map e.hom,
            (basePullbackModules B S hS τ).map f.hom) :=
    Eq.trans (congrArg (fun z => z ≫ _) h1) (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun z => _ ≫ z) h2) (Category.assoc _ _ _).symm))
  rw [baseAssociatedModuleTensorIso_hom, baseAssociatedModuleTensorIso_hom]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) mid) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) h3) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫ _) (Category.assoc _ _ _)

/-- **The object-level tensor comparison of `𝓕 ↦ 𝓕^a` is natural in both arguments**, at every one
of the five topologies and with no hypothesis on `S`.  This discharges the extra datum that
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_naturality` asks for, for the
functor the comparison of Picard groups of
`StacksFrontier/AlgebraicGeometry/Picard/BaseSitePicardComparison.lean` is built from. -/
public theorem baseAssociatedModuleTensorIso'_natural (τ : SiteKind) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) :=
  fun M N M' N' e f => by
    have hz : (Stacks.SheafOfModules.Invertible.tensorProductIso S.presheaf
          (zariskiStructureIsSheaf S) e f).hom =
        (tensorSheafBifunctorZariski S).map (X := (M, N)) (Y := (M', N')) (e.hom, f.hom) :=
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩ e.hom f.hom).symm
    have hb : (Stacks.SheafOfModules.Invertible.tensorProductIso
          (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
          ((baseAssociatedModule B S hS τ).mapIso e)
          ((baseAssociatedModule B S hS τ).mapIso f)).hom =
        (tensorSheafBifunctorBase B S hS τ).map
          (X := ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N))
          (Y := ((baseAssociatedModule B S hS τ).obj M', (baseAssociatedModule B S hS τ).obj N'))
          ((baseAssociatedModule B S hS τ).map e.hom,
            (baseAssociatedModule B S hS τ).map f.hom) :=
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat)
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩
        ((baseAssociatedModule B S hS τ).map e.hom)
        ((baseAssociatedModule B S hS τ).map f.hom)).symm
    exact (congrArg (fun z => (baseAssociatedModule B S hS τ).map z ≫
          (baseAssociatedModuleTensorIso' B S hS τ M' N').hom) hz).trans
      ((baseAssociatedModuleTensorIso_naturality B S hS τ e f).trans
        (congrArg (fun z => (baseAssociatedModuleTensorIso' B S hS τ M N).hom ≫ z) hb.symm))

end AlgebraicGeometry.BigFppfOver

end
