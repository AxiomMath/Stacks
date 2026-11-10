module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Leray
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# Cohomology is unchanged by pushforward along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes. Then `H ⁱ(X, F) ≅ H ⁱ(S, f_* F)` for every
quasi-coherent `𝒪_X`-module `F`, **naturally in `F`**. This is [Stacks, Tag 089W].

The source writes an equality of cohomology groups; the content recorded here is that the
identification is a natural isomorphism of functors on the category of quasi-coherent modules,
not an unrelated choice of isomorphism for each module.

[Stacks, Tag 01F4] part (1) (`Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages`)
already gives the isomorphism for a single module whose higher direct images vanish, and
[Stacks, Tag 01XC] (`Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward`) supplies
that vanishing for a quasi-coherent module along an affine morphism. What that composition does
*not* give is naturality: the isomorphism of part (1) is assembled at a fixed module,
and one of its three factors is the inverse of a component of the unit of `R f_*`, which is
invertible only at an `f_*`-acyclic module.

So the collapse is rebuilt here one level up, as a natural transformation that happens to be
invertible on the quasi-coherent modules:

* `singlePushforwardUnit` is the natural transformation `(f_* F)[0] ⟶ R f_*(F[0])`, assembled from
  the unit of `R f_*` and the two pinned isomorphisms identifying `F[0]` in the derived category
  with its image from the homotopy category. It is a natural transformation of functors
  `Mod(𝒪_X) ⥤ D⁺(Mod(𝒪_S))`, and `isIso_singlePushforwardUnit_app` says that its component at
  `F` is invertible exactly when `F` is `f_*`-acyclic — that component *is* the unit of `R f_*`
  at `F[0]`, up to two isomorphisms.
* `derivedPlusPushforwardNatTrans` whiskers it against
  `Stacks.LeraySections.rightDerivedFunctorPlusCompIso`, the functor-level isomorphism
  `R Γ(X, -) ≅ R f_* ⋙ R Γ(S, -)`, to get a natural transformation
  `f_* ⋙ R ᵖΓ(S, -) ⟶ R ᵖΓ(X, -)` of functors `Mod(𝒪_X) ⥤ Ab`.
* `cohomologyPushforwardIso` restricts that to the quasi-coherent modules, where every component
  is invertible, and reindexes `ℤ` to `ℕ` with `Stacks.DerivedIndexing.rightDerivedIso`.

## Main definitions

* `Stacks.AffineCohomologyPushforward.singlePushforwardUnit`: the natural transformation
  `f_*(-)[0] ⟶ R f_*((-)[0])`.
* `Stacks.AffineCohomologyPushforward.derivedPlusPushforwardNatTrans`: the comparison
  `f_* ⋙ R ᵖΓ(S, -) ⟶ R ᵖΓ(X, -)`, natural in the module.
* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso`: the natural isomorphism
  `H ⁱ(X, -) ≅ H ⁱ(S, f_*(-))` on quasi-coherent modules, which is the strengthening of
  [Stacks, Tag 089W] to a natural isomorphism.
* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`: its component at a single
  quasi-coherent module, `H ⁱ(X, F) ≅ H ⁱ(S, f_* F)`.
* `Stacks.AffineCohomologyPushforward.cohomologyIsoPushforwardOfAffine`: **[Stacks, Tag 089W]**
  exactly as the source states it, and by the route the source takes — [Stacks, Tag 01XC] into
  [Stacks, Tag 01F4] part (1).

## Main results

* `Stacks.AffineCohomologyPushforward.isIso_singlePushforwardUnit_app`: the component of
  `singlePushforwardUnit` at an `f_*`-acyclic module is invertible.
* `Stacks.AffineCohomologyPushforward.isIso_derivedPlusPushforwardNatTrans_app`: hence so is the
  component of the comparison of derived global sections.
* `Stacks.AffineCohomologyPushforward.isIso_schemeDerivedPlusNatTrans_app`: and so, for an affine
  morphism, is its component at every quasi-coherent module.

No stacks attribute is attached: the covering set is reported rather than written.

## Implementation notes

**What is and is not pinned.** `singlePushforwardUnit` is built from the unit of `R f_*` and two
isomorphisms that are themselves pinned, so `cohomologyPushforwardIso` involves no choices. It is
nevertheless not *characterized by an equation* here: no lemma computes its degree-zero component
against the two canonical maps `Γ ⟶ R ⁰Γ`, and no lemma computes it through a chosen comparison of
a pushed-forward injective resolution with an injective resolution of the pushforward. Those two
normalizations are not formalized here.

**Why part (1) is not simply whiskered.**
`Stacks.LeraySections.derivedPushforwardSingleIso` has exactly the right type at each module, but
it takes the acyclicity hypothesis as an *argument* and inverts a unit component inside its own
body, so there is no natural transformation of which it is the family of components. The middle
factor of `singlePushforwardUnit` is the same unit component, and the surrounding two factors are
the same two pinned isomorphisms, so `cohomologyPushforwardIso` agrees with part (1) at
every quasi-coherent module; that agreement is not asserted as a lemma here, because asserting it
would require re-deriving `derivedPushforwardSingleIso`'s definitional unfolding in this file.

**Associativity of functor composition.** Every whiskering below meets its neighbour at an object
presented with a different bracketing of `⋙`. These are definitionally equal — `Functor.comp`
reduces to the same `obj`/`map` fields either way — so the compositions are written in term mode
and no `Functor.associator` appears. `Functor.rightDerivedPlus` is a semireducible `def` sitting in
the type of these composites, so `rw`/`simp` cannot see through it and the proofs that the
components are invertible go through `dsimp only` on the definitions, or through `change` to the
reduced composite, followed by instance search — never through rewriting.

**Universes.** Everything runs at a single universe `u`, as
`Stacks.LeraySections.rightDerivedFunctorPlusCompIso` does; `(R := X.ringCatSheaf)` is written out
in the statement of `cohomologyPushforwardIso` because `SheafOfModules.isQuasicoherent` otherwise
fails to elaborate at a universe that matches.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AffineCohomologyPushforward

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The unit of `RG` (Mathlib's `rightDerivedFunctorPlusUnith`, whose definition is not exposed)
is invertible at `K` exactly when the unit of `Functor.totalRightDerived` is: both are units of
right derived functors of the same functor. -/
private lemma isIso_rightDerivedFunctorPlusUnith_app_iff {D : Type*} {E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D]
    [HasDerivedCategory E] (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) ↔
      IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app K) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)) K]
  exact (isIso_comp_right_iff _ _).symm

/-! ### The comparison, over a morphism of ringed spaces -/

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The natural transformation `(f_* F)[0] ⟶ R f_*(F[0])`.** Its middle factor is the unit of
`R f_*` at the image of `F[0]` from the bounded below homotopy category; the two outer factors are
the pinned identifications of that image with `F[0]` in the derived category
(`CategoryTheory.Functor.singleFunctorPlusIsoCompQh`) and of `f_*` applied to it with `(f_* F)[0]`
(`CategoryTheory.Functor.mapSingleFunctorCompQhIso`). -/
def singlePushforwardUnit :
    modulePushforward f ⋙
        DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0 ⟶
      DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
        (modulePushforward f).rightDerivedFunctorPlus :=
  (Functor.mapSingleFunctorCompQhIso (modulePushforward f)).inv ≫
    Functor.whiskerLeft
      (HomotopyCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0)
      (modulePushforward f).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (Functor.singleFunctorPlusIsoCompQh (A := SheafOfModules.{u}
      (structureSheafRing X)) 0).inv (modulePushforward f).rightDerivedFunctorPlus

/-- **The component of `singlePushforwardUnit` at an `f_*`-acyclic module is invertible.** Right
acyclicity *is* invertibility of the middle factor, and the two outer factors are components of
isomorphisms. -/
theorem isIso_singlePushforwardUnit_app {F : SheafOfModules.{u} (structureSheafRing X)}
    (hF : (modulePushforward f).rightAcyclic F) :
    IsIso ((singlePushforwardUnit f).app F) := by
  have hu : IsIso ((modulePushforward f).rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
      F)) :=
    (isIso_rightDerivedFunctorPlusUnith_app_iff _ _).2 hF
  dsimp only [singlePushforwardUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- **The comparison of derived global sections, `R ᵖΓ(S, f_* -) ⟶ R ᵖΓ(X, -)`.**
`Stacks.LeraySections.rightDerivedFunctorPlusCompIso` is already an isomorphism of functors on the
bounded below derived category, `R Γ(X, -) ≅ R f_* ⋙ R Γ(S, -)`; the only thing left to compare is
`(f_* F)[0]` with `R f_*(F[0])`, which is `singlePushforwardUnit`. -/
def derivedPlusPushforwardNatTrans (p : ℤ) :
    modulePushforward f ⋙ (secF (structureSheafRing Y) ⊤).rightDerivedPlus p ⟶
      (secF (structureSheafRing X) ⊤).rightDerivedPlus p :=
  Functor.whiskerRight (singlePushforwardUnit f)
      ((secF (structureSheafRing Y) (⊤ : Opens Y.carrier)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p) ≫
    Functor.whiskerLeft
        (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0)
      (Functor.whiskerRight (Stacks.LeraySections.rightDerivedFunctorPlusCompIso f).inv
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p))

/-- **The component of the comparison at an `f_*`-acyclic module is invertible.** Both factors
are: the first is a functor applied to `isIso_singlePushforwardUnit_app`, the second a functor
applied to a component of an isomorphism. -/
theorem isIso_derivedPlusPushforwardNatTrans_app (p : ℤ)
    {F : SheafOfModules.{u} (structureSheafRing X)} (hF : (modulePushforward f).rightAcyclic F) :
    IsIso ((derivedPlusPushforwardNatTrans f p).app F) := by
  have hσ : IsIso ((singlePushforwardUnit f).app F) := isIso_singlePushforwardUnit_app f hF
  change IsIso
    (((secF (structureSheafRing Y) (⊤ : Opens Y.carrier)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
          ((singlePushforwardUnit f).app F) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
        ((Stacks.LeraySections.rightDerivedFunctorPlusCompIso f).inv.app
          ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            F)))
  infer_instance

end RingedSpaces

/-! ### The natural isomorphism on quasi-coherent modules over a morphism of schemes -/

section Schemes


variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The comparison of derived global sections along a morphism of schemes. Every identification
needed to read the ringed-space transformation at a morphism of schemes is `rfl`, by
`Stacks.SchemeCohomology.ringSheaf_ringedSpace` and
`Stacks.SchemeCohomology.modulePushforward_hom`. -/
def schemeDerivedPlusNatTrans (p : ℤ) :
    Scheme.Modules.pushforward f ⋙ (secF S.ringCatSheaf ⊤).rightDerivedPlus p ⟶
      (secF X.ringCatSheaf ⊤).rightDerivedPlus p :=
  derivedPlusPushforwardNatTrans (Stacks.SchemeCohomology.hom f) p

/-- **The comparison is invertible at a quasi-coherent module when `f` is affine.** This is
[Stacks, Tag 01XC] in the shape `Stacks.AffineHigherDirectImage.rightAcyclic_pushforward`. -/
theorem isIso_schemeDerivedPlusNatTrans_app [IsAffineHom f] (p : ℤ) (F : X.Modules)
    [F.IsQuasicoherent] : IsIso ((schemeDerivedPlusNatTrans f p).app F) :=
  isIso_derivedPlusPushforwardNatTrans_app (Stacks.SchemeCohomology.hom f) p
    (Stacks.AffineHigherDirectImage.rightAcyclic_pushforward f F)

/-- The comparison of derived global sections, restricted to the quasi-coherent modules. -/
def quasicoherentDerivedPlusNatTrans (p : ℤ) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        Scheme.Modules.pushforward f ⋙ (secF S.ringCatSheaf ⊤).rightDerivedPlus p ⟶
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        (secF X.ringCatSheaf ⊤).rightDerivedPlus p :=
  Functor.whiskerLeft _ (schemeDerivedPlusNatTrans f p)

/-- Every component of the restricted comparison is invertible. Declared as an instance so that
`CategoryTheory.NatIso.isIso_of_isIso_app` can find it. -/
instance isIso_quasicoherentDerivedPlusNatTrans_app [IsAffineHom f] (p : ℤ)
    (G : (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory) :
    IsIso ((quasicoherentDerivedPlusNatTrans f p).app G) :=
  isIso_schemeDerivedPlusNatTrans_app f p G.obj

/-- The comparison restricted to the quasi-coherent modules, where it is a natural isomorphism. -/
def quasicoherentDerivedPlusNatIso [IsAffineHom f] (p : ℤ) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        Scheme.Modules.pushforward f ⋙ (secF S.ringCatSheaf ⊤).rightDerivedPlus p ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        (secF X.ringCatSheaf ⊤).rightDerivedPlus p := by
  haveI := NatIso.isIso_of_isIso_app (quasicoherentDerivedPlusNatTrans f p)
  exact asIso (quasicoherentDerivedPlusNatTrans f p)

/-- **[Stacks, Tag 089W].** For an affine morphism of schemes `f : X ⟶ S`, cohomology of a
quasi-coherent module is canonically isomorphic to cohomology of its pushforward, *naturally in
the module*: this is an isomorphism of functors on the category of quasi-coherent
`𝒪_X`-modules, not a choice of isomorphism for each one. -/
@[stacks 089W "the natural isomorphism",
  ega "II 5.2.3",
  ega "III 1.3.4" "g to a point",
  ega "III 1.3.3"]
def cohomologyPushforwardIso [IsAffineHom f] (i : ℕ) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        Hfunctor X.ringCatSheaf ⊤ i ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        Scheme.Modules.pushforward f ⋙ Hfunctor S.ringCatSheaf ⊤ i :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (R := X.ringCatSheaf)))
      (Stacks.DerivedIndexing.rightDerivedIso (secF X.ringCatSheaf (⊤ : Opens X.carrier)) i) ≪≫
    (quasicoherentDerivedPlusNatIso f (i : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent
        (R := X.ringCatSheaf)))
      (Functor.isoWhiskerLeft (Scheme.Modules.pushforward f)
        (Stacks.DerivedIndexing.rightDerivedIso
          (secF S.ringCatSheaf (⊤ : Opens S.carrier)) i).symm)

/-- The component of the natural isomorphism of [Stacks, Tag 089W] at a quasi-coherent module:
`H ⁱ(X, F) ≅ H ⁱ(S, f_* F)`. -/
def cohomologyPushforwardIsoApp [IsAffineHom f] (i : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] :
    Hgroup X.ringCatSheaf ⊤ i F ≅
      Hgroup S.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F) :=
  (cohomologyPushforwardIso f i).app ⟨F, inferInstance⟩

/-- **[Stacks, Tag 089W] exactly as the source states it**, and by the route the source takes:
`H ⁱ(X, F) = H ⁱ(S, f_* F)` for `f` affine and `F` quasi-coherent, in every degree `i ≥ 0`. The
proof is the source's — [Stacks, Tag 01XC] feeds the vanishing hypothesis of [Stacks, Tag 01F4]
part (1), here in the scheme form
`Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages`.

This is a *second* construction of the isomorphism of `cohomologyPushforwardIsoApp`, assembled out
of part (1) rather than rebuilt; no lemma identifies the two, which is why the natural
one is built from scratch above. -/
def cohomologyIsoPushforwardOfAffine [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent]
    (i : ℕ) :
    Hgroup X.ringCatSheaf ⊤ i F ≅
      Hgroup S.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F) :=
  Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages f
    (fun q hq ↦ Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward f F q hq) i

end Schemes

end Stacks.AffineCohomologyPushforward

end
