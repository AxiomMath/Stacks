module

public import Mathlib.CategoryTheory.Monoidal.Tor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorsorsAndColimits.KFlatResolution
public import StacksFrontier.Homology.Tor.ChangeOfRingsSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion

/-!
# The stalk of a Tor sheaf is the Tor module of the stalks

Let `X` be a scheme and let `ℱ`, `𝒢` be `𝒪_X`-modules. The stalk at a point `x` of the Tor sheaf
`Tor_p^{𝒪_X}(ℱ, 𝒢)` is the Tor module `Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)` of the two stalks over the
local ring. This is the second clause of Lemma 43.14.2 and the "basic fact we will use
frequently" with which Section 43.14 opens.

The proof is the one the source indicates, in three steps. Choose K-flat resolutions `P → ℱ` and
`Q → 𝒢`; then `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the `(-p)`-th cohomology of `Tot(P ⊗_{𝒪_X} Q)`, so its
stalk is the `(-p)`-th homology of the complex of stalks of that total complex. The stalk functor
carries the total tensor complex to the total tensor complex of the stalks, and carries a K-flat
complex to a K-flat complex — the two halves of the stalk criterion for K-flatness, Tag 06YB.
Finally a K-flat resolution computes `Tor` over a ring, so contracting `Q_x` against the K-flat
`P_x` leaves `Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`.

## Main definitions

* `AlgebraicGeometry.TorFormula.flatRes` and `AlgebraicGeometry.TorFormula.flatResHom` — the
  chosen K-flat resolution of a module placed in degree `0`, and its augmentation.
* `AlgebraicGeometry.TorFormula.stalkFlatResHom` — the augmentation of the stalked resolution
  onto the stalk of the module.

## Main results

* `AlgebraicGeometry.TorFormula.torSheafStalkIso` — **Tag 0AZT, the stalk clause.**
* `AlgebraicGeometry.TorFormula.torSheafStalkStep₁` and
  `AlgebraicGeometry.TorFormula.torSheafStalkStep₂` — the two halves it is composed from.

## Implementation notes

The resolutions are the library's *chosen* ones, `Stacks.Cohomology.kFlatResolution`, rather than
witnesses extracted from an existence statement: the result is data, so a resolution picked by
`Classical.choose` at each use would not be well defined.

The ring of scalars is the `RingCat`-valued stalk
`TopCat.Presheaf.stalk (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj x`, which is the ring
that `AlgebraicGeometry.Scheme.Modules.stalkFunctor` takes its modules over. It is the local ring
`𝒪_{X, x}` of the source, in the spelling the stalk functor produces; the `CommRingCat`-valued
stalk `X.presheaf.stalk x` is the same ring in the other spelling, and a comparison between the
two is still owed by anything that wants to read this result against
`Ideal.localIntersectionMultiplicity`, which is phrased over the latter.

`MonoidalCategory` and `MonoidalPreadditive` for the stalk module category are supplied
explicitly in each statement. They are not found by instance search: `ModuleCat` is indexed by a
`Ring` instance, the stalk carries two defeq but differently spelled ones — the `RingCat` one and
the one derived from `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` — and search runs at a
transparency where that difference is invisible. For the same reason several instance arguments
below are passed positionally, pinned with `inferInstanceAs`, rather than left to search; `exact`
and function application then unify the two spellings at default transparency.

The result is built as two declarations composed in a third rather than as one chain, so that no
declaration has to elaborate another's interior.

### Clause (4) of Tag 0AZT is not carried

Lemma 43.14.2 also asserts that `Tor_p^{𝒪_X}(ℱ, 𝒢)` vanishes for `p > dim X` on a nonsingular
variety. That is not proved here. With the stalk comparison below it reduces to the vanishing of
`Tor_p` over a regular local ring of dimension at most `dim X`, since a sheaf is zero exactly
when all its stalks are.

## References

* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- The chosen K-flat resolution of an `𝒪_X`-module placed in degree `0`. -/
def flatRes (X : Scheme.{u}) (F : X.Modules) : CochainComplex X.Modules ℤ :=
  letI : HasWeakSheafify (schemeRingedSite X).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
  letI : (schemeRingedSite X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u})
  Stacks.Cohomology.kFlatResolution (schemeRingedSite X)
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)

/-- The augmentation of the chosen K-flat resolution onto the module it resolves. -/
def flatResHom (X : Scheme.{u}) (F : X.Modules) :
    flatRes X F ⟶ (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F :=
  letI : HasWeakSheafify (schemeRingedSite X).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
  letI : (schemeRingedSite X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u})
  Stacks.Cohomology.kFlatResolutionHom (schemeRingedSite X)
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)

/-- The chosen resolution is K-flat. -/
theorem flatRes_kFlat (X : Scheme.{u}) (F : X.Modules) :
    Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf (flatRes X F) :=
  let : HasWeakSheafify (schemeRingedSite X).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
  let : (schemeRingedSite X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u})
  Stacks.Cohomology.kFlatResolution_kFlat (schemeRingedSite X) _

/-- The augmentation of the chosen resolution is a quasi-isomorphism. -/
instance flatResHom_quasiIso (X : Scheme.{u}) (F : X.Modules) : QuasiIso (flatResHom X F) :=
  letI : HasWeakSheafify (schemeRingedSite X).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
  letI : (schemeRingedSite X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u})
  Stacks.Cohomology.kFlatResolutionHom_quasiIso (schemeRingedSite X) _

/-- In the derived category the chosen resolution is the module placed in degree `0`. -/
def flatResIso (X : Scheme.{u}) (F : X.Modules) :
    (DerivedCategory.Q.obj (flatRes X F) : DerivedCategory X.Modules) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
  haveI : IsIso (DerivedCategory.Q.map (flatResHom X F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := X.Modules) (flatResHom X F)).2 inferInstance
  asIso (DerivedCategory.Q.map (flatResHom X F)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm

/-- The augmentation of the stalked resolution onto the stalk of the module: the complex of
stalks of the chosen resolution resolves `ℱ_x`. -/
def stalkFlatResHom (X : Scheme.{u}) (x : X) (F : X.Modules) :
    AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x (flatRes X F) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((Scheme.Modules.stalkFunctor X x).obj F) :=
  ((Scheme.Modules.stalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (flatResHom X F) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.stalkFunctor X x)
      (ComplexShape.up ℤ) 0).app F).hom

/-- The stalked augmentation is a quasi-isomorphism: the stalk functor is exact, and the second
factor is an isomorphism. -/
instance stalkFlatResHom_quasiIso (X : Scheme.{u}) (x : X) (F : X.Modules) :
    QuasiIso (stalkFlatResHom X x F) :=
  @quasiIso_comp _ _ _ _ _ _ _ _
    (((Scheme.Modules.stalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (flatResHom X F))
    (((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.stalkFunctor X x)
      (ComplexShape.up ℤ) 0).app F).hom) _ _ _
    (@HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _
      (flatResHom X F) (Scheme.Modules.stalkFunctor X x)
      (inferInstanceAs ((Scheme.Modules.stalkFunctor X x).Additive))
      (inferInstanceAs ((Scheme.Modules.stalkFunctor X x).PreservesHomology)) _ _ _ _
      inferInstance)
    (@quasiIso_of_isIso _ _ _ _ _ _ _
      (((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.stalkFunctor X x)
        (ComplexShape.up ℤ) 0).app F).hom)
      (inferInstanceAs (IsIso (((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.stalkFunctor X x) (ComplexShape.up ℤ) 0).app F).hom))) _ _)

/-- The stalk of `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the `(-p)`-th homology of the complex of stalks of the
total tensor complex of the two chosen K-flat resolutions. -/
def torSheafStalkStep₁ (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) (x : X) :
    (Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p) ≅
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
        (Stacks.Duality.totalTensorComplex (flatRes X F) (flatRes X G))).homology (-(p : ℤ)) :=
  stalkTorSheafIso X F G p x (flatRes X F) (flatRes X G)
    (flatRes_kFlat X F) (flatRes_kFlat X G) (flatResIso X F) (flatResIso X G)

/-- That homology is `Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`: the stalk of a total tensor complex is the
total tensor complex of the stalks, the stalk of a K-flat complex is K-flat, and a K-flat
resolution computes `Tor` over a ring. -/
def torSheafStalkStep₂ (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) (x : X) :
    letI : MonoidalCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
      Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat X.sheaf x
    letI : MonoidalPreadditive (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
      Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat X.sheaf x
    (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
        (Stacks.Duality.totalTensorComplex (flatRes X F) (flatRes X G))).homology (-(p : ℤ)) ≅
      ((Tor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) p).obj
          ((Scheme.Modules.stalkFunctor X x).obj F)).obj
        ((Scheme.Modules.stalkFunctor X x).obj G) := by
  letI := StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  have hPx : CochainComplex.KFlat
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x (flatRes X F)) :=
    (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise X.sheaf
      (flatRes X F)).mp (flatRes_kFlat X F) x
  exact HomologicalComplex.homologyMapIso
      (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso X.sheaf x
        (flatRes X F) (flatRes X G)) (-(p : ℤ)) ≪≫
    @CochainComplex.Tor.ChangeOfRingsSpectralSequence.mapBifunctorHomologyTorIso
      _ _ _ _ _ _ (stalkFlatResHom X x F)
      (inferInstanceAs (QuasiIso (stalkFlatResHom X x F))) hPx (stalkFlatResHom X x G)
      (inferInstanceAs (QuasiIso (stalkFlatResHom X x G))) p

/-- **Stacks 0AZT: the stalk of a Tor sheaf is the Tor module of the stalks.** For `𝒪_X`-modules
`ℱ` and `𝒢` on a scheme `X` and a point `x`, the stalk at `x` of `Tor_p^{𝒪_X}(ℱ, 𝒢)` is
`Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`. No hypothesis on `X`, `ℱ` or `𝒢` is needed. -/
@[stacks 0AZT "the stalk clause: the stalk at `x` of `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the Tor module \
`Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)` of the two stalks over the local ring, with no hypothesis on the \
scheme or the two modules. The local ring is the `RingCat`-valued stalk of the structure sheaf, \
which is the ring the stalk functor takes its modules over. The coherence and support clauses \
are `isCoherent_torSheaf_of_isRegular` and `supp_torSheaf_subset_inter`; the vanishing clause \
for `p > dim X` is NOT carried, see the module docstring."]
def torSheafStalkIso (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) (x : X) :
    letI : MonoidalCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
      Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat X.sheaf x
    letI : MonoidalPreadditive (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) :=
      Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat X.sheaf x
    (Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p) ≅
      ((Tor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x)) p).obj
          ((Scheme.Modules.stalkFunctor X x).obj F)).obj
        ((Scheme.Modules.stalkFunctor X x).obj G) :=
  torSheafStalkStep₁ X F G p x ≪≫ torSheafStalkStep₂ X F G p x

end AlgebraicGeometry.TorFormula

end
