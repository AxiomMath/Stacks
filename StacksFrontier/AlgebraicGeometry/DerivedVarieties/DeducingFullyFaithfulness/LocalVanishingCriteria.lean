module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraper
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraperCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DiagonalFibreVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOfTheRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedStalk
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CaseIKernelVanishing

/-!
# Local vanishing of a perfect complex from Ext groups with the residue-field skyscraper

Let `X` be a scheme, `x ∈ X` a closed point, `𝒪_x` the skyscraper sheaf at `x` with value the
residue field `κ(x)`, and `K` a perfect object of `D(𝒪_X)`. This file proves [Stacks, Tag 0G03]:
each of the following vanishing conditions forces cohomology to vanish on an open neighbourhood
of `x`.

1. (`X` regular of finite type over a field) `Ext^i_X(𝒪_x, K) = 0` gives `H^{i - d_x}(K)|_U = 0`,
   `d_x = dim 𝒪_{X,x}`;
2. (same) `Hom_X(𝒪_x, K[i]) = 0` for all `i` gives `K|_U = 0`;
3. `Ext^i_X(K, 𝒪_x) = 0` gives `H^i(K^∨)|_U = 0`;
4. `Hom_X(K, 𝒪_x[i]) = 0` for all `i` gives `K|_U = 0`;
5. `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x) = 0` gives `H^i(K)|_U = 0`;
6. `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x) = 0` for all `i` gives `K|_U = 0`.

## Main results

* `exists_mem_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper`:
  part (1).
* `exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper`:
  part (2).
* `exists_mem_isZero_stalkHomology_derivedDual_of_subsingleton_hom_to_residueFieldSkyscraper`:
  part (3).
* `exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_to_residueFieldSkyscraper`:
  part (4).
* `exists_mem_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor`:
  part (5).
* `exists_mem_forall_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor`:
  part (6).

## Implementation notes

The proof is the source's. Everything is reduced to part (5), which is
`AlgebraicGeometry.exists_mem_isZero_stalkHomology_of_derivedTensor_residueField` (the derived
stalk form, from [Stacks, Tag 068U]) once `H^i(X, K ⊗^𝐋 𝒪_x)` is identified with
`H^i((K ⊗^𝐋 𝒪_x)_x)`. That identification holds because `K ⊗^𝐋 𝒪_x` has its cohomology
sheaves supported on the closed point `x`
(`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right`), and
for such a complex derived global sections are the derived stalk
(`Stacks.Cohomology.SupportedComplexes.homologyIsoDerivedStalk`), after the two readings of
`RΓ(X, -)` are matched by `AlgebraicGeometry.isZero_homology_derivedModuleGlobalSections_iff`.

* Part (1) is [Stacks, Tag 0G02] at `F = F' = 𝒪_x`
  (`AlgebraicGeometry.exists_ringKrullDim_eq_and_homAddEquiv_homologyDerivedTensor`), whose inputs
  — `𝒪_x` coherent and supported at `x`, and `κ(x)` Matlis dual to itself — are
  `AlgebraicGeometry.isCoherent_residueFieldSkyscraperSheaf`,
  `AlgebraicGeometry.supp_residueFieldSkyscraperSheaf_subset` and
  `AlgebraicGeometry.isMatlisDualPair_stalk_residueFieldSkyscraperSheaf`. It turns
  `Ext^i(𝒪_x, K)` into `H^0(X, K[i] ⊗^𝐋 𝒪_x[-d_x])`, and the shifts are moved out of the
  tensor product by `AlgebraicGeometry.derivedTensorShiftShiftIso`.
* Part (2) is part (1) in every degree; only the finitely many degrees inside the cohomological
  bounds of `K` need a neighbourhood.
* Part (3) is `Ext^i(K, 𝒪_x) = H^0(X, 𝒪_x[i] ⊗^𝐋 K^∨)` ([Stacks, Tags 08DQ and 08JJ], in the form
  `AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual`) followed by part (5)
  for the perfect complex `K^∨` (`Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace`).
* Part (4) is `exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper`
  (the [Stacks, Tag 0GWZ] argument, stated there for bounded complexes with coherent cohomology)
  at a perfect `K`, which has bounded coherent cohomology by
  `Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect` ([Stacks, Tag 0FXU]).
  That statement is phrased with `AlgebraicGeometry.residueFieldSkyscraper`, the construction of
  the skyscraper at `x` with value `κ(x) = X.residueField x` by sheafifying the skyscraper
  presheaf, and part (4) is stated with it; parts (1)–(3), (5) and (6) use
  `AlgebraicGeometry.residueFieldSkyscraperSheaf`, the skyscraper sheaf at `x` whose value is the
  residue field of the stalk ring, which is the one the derived-stalk form of part (5) is stated
  with.

"`H^j(L)|_U = 0`" is read as the vanishing of the stalk of the cohomology sheaf `H^j(L)` at every
point of `U`; "`K` is zero on `U`" as that vanishing in every degree. `H^i(X, -)` is the cohomology
of `Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` of the ringed site of opens, and
the derived tensor product is that of the ringed site of opens — the two in which
[Stacks, Tag 0G02] is stated. Parts (3)–(6) hold for every Noetherian scheme, which contains the
source's regular schemes of finite type over a field; part (4) holds for every point.

## References

* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedSectionsLeray in
/-- **Hypercohomology of a complex supported at a closed point is its derived stalk there.**
For `L` in `D(𝒪_X)` with cohomology sheaves supported on the closed point `x`, the vanishing of
`H^n(X, L)` forces the vanishing of `H^n(L_x)`. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_globalSections (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (L : DerivedCategory X.Modules)
    (hL : CohomologySupportedOn X.ringCatSheaf ({x} : Set X) L) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj L))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) n).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj L)) := by
  have inst : (derivedSectionsOverOpen X.toRingedSpace ⊤).IsRightDerivedFunctor
      (derivedSectionsOverOpenUnit X.toRingedSpace ⊤)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := inferInstance
  have h1 := (@isZero_homology_derivedModuleGlobalSections_iff X
    (derivedSectionsOverOpen X.toRingedSpace ⊤) (derivedSectionsOverOpenUnit X.toRingedSpace ⊤)
    inst L n).mp h
  have h2 := h1.of_iso (Stacks.Cohomology.SupportedComplexes.homologyIsoDerivedStalk
    X.toRingedSpace x hx L hL n).symm
  have h3 := h2.of_iso (((ModuleCat.restrictScalars
    (Stacks.Cohomology.SupportedComplexes.structureSheafGermTop X.toRingedSpace
      x)).mapDerivedCategoryHomologyIso n).app
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj L)).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr ((ModuleCat.isZero_iff_subsingleton
    (R := (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))).mp h3)

/-- **The shifted form**: for `L` supported on the closed point `x`, the vanishing of
`H^0(X, L[n])` forces the vanishing of `H^n(L_x)`. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_globalSections_shift (X : Scheme.{u})
    (x : X) (hx : IsClosed ({x} : Set X)) (L : DerivedCategory X.Modules)
    (hL : CohomologySupportedOn X.ringCatSheaf ({x} : Set X) L) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (L⟦n⟧)))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) n).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj L)) := by
  let : (SheafOfModules.stalkFunctor X.ringCatSheaf x).Additive :=
    SheafOfModules.stalkFunctor_additive X.ringCatSheaf x
  let : Limits.PreservesFiniteLimits (SheafOfModules.stalkFunctor X.ringCatSheaf x) :=
    SheafOfModules.stalkFunctor_preservesFiniteLimits X.ringCatSheaf x
  let : Limits.PreservesColimits (SheafOfModules.stalkFunctor X.ringCatSheaf x) :=
    SheafOfModules.stalkFunctor_preservesColimits X.ringCatSheaf x
  have h0 := isZero_homology_derivedStalk_of_isZero_homology_globalSections X x hx (L⟦n⟧)
    (cohomologySupportedOn_shift X.ringCatSheaf _ n L hL) 0 h
  exact h0.of_iso (((DerivedCategory.homologyFunctor _ 0).shiftIso n 0 n (by omega)).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      (((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.commShiftIso n).app
        L).symm)

/-- A bifunctor compatible with shifts in each variable separately commutes with shifts in both
variables at once: `F(A[a], B[b]) ≅ F(A, B)[a + b]`. -/
def bifunctorShiftShiftIso {C : Type*} [Category* C] [HasShift C ℤ] (F : C ⥤ C ⥤ C)
    (A B : C) (a b : ℤ) [(F.obj (A⟦a⟧)).CommShift ℤ] [(F.flip.obj B).CommShift ℤ] :
    (F.obj (A⟦a⟧)).obj (B⟦b⟧) ≅ ((F.obj A).obj B)⟦a + b⟧ :=
  ((F.obj (A⟦a⟧)).commShiftIso b).app B ≪≫
    (shiftFunctor C b).mapIso (((F.flip.obj B).commShiftIso a).app A) ≪≫
    (shiftFunctorAdd' C a b (a + b) rfl).symm.app _

/-- The derived tensor product of the ringed site of opens commutes with shifts in both
variables: `A[a] ⊗^𝐋 B[b] ≅ (A ⊗^𝐋 B)[a + b]`. -/
def derivedTensorShiftShiftIso (X : Scheme.{u}) (A B : DerivedCategory X.Modules) (a b : ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (A⟦a⟧)).obj (B⟦b⟧) ≅
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj A).obj B)⟦a + b⟧ :=
  @bifunctorShiftShiftIso _ _ _ _ A B a b
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).commShift_right (A⟦a⟧))
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).commShift_left B)

section Tensor

/-- The derived tensor product `K ⊗^𝐋_{𝒪_X} 𝒪_x`, formed with the derived tensor product of the
ringed site of opens of `X` in which [Stacks, Tag 0G02] is stated. -/
abbrev derivedTensorSkyscraper (X : Scheme.{u}) (x : X) (K : DerivedCategory X.Modules) :
    DerivedCategory X.Modules :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor
    (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (residueFieldSkyscraperSheaf X x))

/-- The two derived tensor products of `K` with the skyscraper `𝒪_x` agree. -/
def derivedTensorSkyscraperIso (X : Scheme.{u}) (x : X) (K : DerivedCategory X.Modules) :
    derivedTensorSkyscraper X x K ≅ derivedTensorResidueFieldSkyscraper X x K :=
  RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) K
    ((DerivedCategory.singleFunctor X.Modules 0).obj (residueFieldSkyscraperSheaf X x))

/-- `K ⊗^𝐋_{𝒪_X} 𝒪_x` has its cohomology sheaves supported on the closed point `x`. -/
theorem cohomologySupportedOn_derivedTensorResidueFieldSkyscraper (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (K : DerivedCategory X.Modules) :
    CohomologySupportedOn X.ringCatSheaf ({x} : Set X)
      (derivedTensorResidueFieldSkyscraper X x K) := by
  have hO := SheafOfModules.cohomologySupportedOn_singleFunctor_skyscraperObj X.ringCatSheaf x
    (residueFieldStalkModule X x)
  rw [hx.closure_eq] at hO
  exact Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right
    X.sheaf ({x} : Set X) K _ hO

/-- An isomorphism `L ≅ L'` transfers the vanishing of `H^n(X, L)` to that of `H^n(X, L')`. -/
private theorem isZero_homology_globalSections_of_iso (X : Scheme.{u})
    {L L' : DerivedCategory X.Modules} (e : L ≅ L') (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj L))) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj L')) :=
  h.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
    ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
      (Stacks.SheafOfModules.ringedSite X.sheaf)).mapIso e)).symm

/-- **The vanishing of `H^i(X, K ⊗^𝐋 𝒪_x)` is the vanishing of `H^i(K_x ⊗^𝐋 κ(x))`.** -/
theorem isZero_homology_derivedStalk_derivedTensorResidueFieldSkyscraper (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (K : DerivedCategory X.Modules) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (derivedTensorSkyscraper X x K)))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) i).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
          (derivedTensorResidueFieldSkyscraper X x K))) := by
  exact isZero_homology_derivedStalk_of_isZero_homology_globalSections X x hx _
    (cohomologySupportedOn_derivedTensorResidueFieldSkyscraper X x hx K) i
    (isZero_homology_globalSections_of_iso X (derivedTensorSkyscraperIso X x K) i h)

/-- **[Stacks, Tag 0G03] part (5), global form.** Let `X` be a Noetherian scheme, `x` a closed
point of `X`, `𝒪_x` the skyscraper at `x` with value `κ(x)` and `K` a perfect object of
`D(𝒪_X)`. If `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x) = 0`, then `H^i(K)` vanishes on an open neighbourhood
of `x`. -/
@[stacks 0G03 "part (5), for X a Noetherian scheme (which every scheme of finite type over a \
field is), x a closed point and K perfect: H^i(X, -) is the cohomology of the derived global \
sections of the ringed site of opens, and H^i(K)|_U = 0 is read as the vanishing of the stalk of \
H^i(K) at every point of U"]
theorem exists_mem_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor
    (X : Scheme.{u}) [IsNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (derivedTensorSkyscraper X x K)))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
  exists_mem_isZero_stalkHomology_of_derivedTensor_residueField X x K hK i
    (isZero_homology_derivedStalk_derivedTensorResidueFieldSkyscraper X x hx K i h)

/-- **[Stacks, Tag 0G03] part (6), global form.** In the situation of part (5), if
`H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x) = 0` for all `i`, then `K` is zero on an open neighbourhood of `x`. -/
@[stacks 0G03 "part (6), for X a Noetherian scheme (which every scheme of finite type over a \
field is), x a closed point and K perfect: if H^i(X, K ⊗^L 𝒪_x) = 0 for all i then every \
cohomology sheaf of K has vanishing stalk at every point of an open neighbourhood of x"]
theorem exists_mem_forall_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor
    (X : Scheme.{u}) [IsNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (derivedTensorSkyscraper X x K)))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
  exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField X x K hK fun i =>
    isZero_homology_derivedStalk_derivedTensorResidueFieldSkyscraper X x hx K i (h i)

/-- If `H^0(X, K[a] ⊗^𝐋 𝒪_x[b]) = 0` then `H^{a+b}(K_x ⊗^𝐋 κ(x)) = 0`. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_globalSections_derivedTensor_shift
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) (K : DerivedCategory X.Modules)
    (a b : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor
            (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (K⟦a⟧)).obj
              (((DerivedCategory.singleFunctor X.Modules 0).obj
                (residueFieldSkyscraperSheaf X x))⟦b⟧))))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) (a + b)).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
          (derivedTensorResidueFieldSkyscraper X x K))) := by
  exact isZero_homology_derivedStalk_of_isZero_homology_globalSections_shift X x hx _
    (cohomologySupportedOn_derivedTensorResidueFieldSkyscraper X x hx K) (a + b)
    (isZero_homology_globalSections_of_iso X (derivedTensorShiftShiftIso X K _ a b ≪≫
      (shiftFunctor _ (a + b)).mapIso (derivedTensorSkyscraperIso X x K)) 0 h)

end Tensor

/-- A regular scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_isRegular_of_finiteType (k : Type u) [Field k] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact sX] (hX : IsRegular X) : IsNoetherian X := by
  have : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  exact {}

/-- **[Stacks, Tag 0G03] part (1).** Let `k` be a field, `X` a regular scheme of finite type
over `k`, `x ∈ X` a closed point, `𝒪_x` the skyscraper at `x` with value `κ(x)`, `d` the
dimension of `𝒪_{X,x}`, and `K` a perfect object of `D(𝒪_X)`. If `Ext^i_X(𝒪_x, K) = 0`, then
`H^{i - d}(K)` vanishes on an open neighbourhood of `x`. -/
@[stacks 0G03 "part (1), at the source's hypotheses: k a field, X a regular scheme of finite \
type over k, x a closed point, 𝒪_x the skyscraper at x with value κ(x), K perfect.  \
Ext^i_X(𝒪_x, K) is Hom_{D(𝒪_X)}(𝒪_x, K[i]); d_x = dim 𝒪_{X,x} is the natural number d with \
ringKrullDim 𝒪_{X,x} = d, produced by the conclusion; H^{i-d_x}(K)|_U = 0 is read as the vanishing \
of the stalk of H^{i-d_x}(K) at every point of U"]
theorem exists_mem_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper
    (k : Type u) [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : IsRegular X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (i : ℤ)
    (h : Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj
      (residueFieldSkyscraperSheaf X x) ⟶ K⟦i⟧)) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = d ∧
      ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
        IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
          ((DerivedCategory.homologyFunctor X.Modules (i - d)).obj K)) := by
  have : IsNoetherian X := isNoetherian_of_isRegular_of_finiteType k X sX hX
  have := isCoherent_residueFieldSkyscraperSheaf X x hx
  obtain ⟨d, hd, e, -⟩ := exists_ringKrullDim_eq_and_homAddEquiv_homologyDerivedTensor k X sX
    hX x hx (residueFieldSkyscraperSheaf X x) (residueFieldSkyscraperSheaf X x)
    (supp_residueFieldSkyscraperSheaf_subset X x hx)
    (supp_residueFieldSkyscraperSheaf_subset X x hx)
    (isMatlisDualPair_stalk_residueFieldSkyscraperSheaf X x)
  refine ⟨d, hd, ?_⟩
  have hz := AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((e (K⟦i⟧)).symm.injective.subsingleton)
  exact exists_mem_isZero_stalkHomology_of_derivedTensor_residueField X x K hK (i + -(d : ℤ))
    (isZero_homology_derivedStalk_of_isZero_homology_globalSections_derivedTensor_shift X x hx K
      i (-(d : ℤ)) hz)

/-- **Degreewise local vanishing of a perfect complex is local vanishing.** If every
cohomology sheaf of a perfect `K` on a Noetherian scheme vanishes near `x`, then all of them
vanish on one common neighbourhood of `x`: only the finitely many degrees inside the
cohomological bounds of `K` need a neighbourhood, and their intersection is open. -/
theorem exists_mem_forall_isZero_stalkHomology_of_forall_exists (X : Scheme.{u}) [IsNoetherian X]
    (x : X) (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
  classical
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK).1
  have hout : ∀ i : ℤ, (i < a ∨ b < i) → ∀ y : X,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := fun i hi y =>
    Functor.map_isZero (SheafOfModules.stalkFunctor X.ringCatSheaf y) (hi.elim (ha i) (hb i))
  choose V hxV hV using h
  refine ⟨⟨⋂ i ∈ (Finset.Icc a b : Finset ℤ), (V i : Set X.carrier),
    isOpen_biInter_finset fun i _ => (V i).isOpen⟩, Set.mem_biInter fun i _ => hxV i, ?_⟩
  intro y hy i
  by_cases hi : a ≤ i ∧ i ≤ b
  · exact hV i y (Set.mem_iInter₂.1 hy i (Finset.mem_Icc.2 hi))
  · exact hout i (by omega) y

/-- **[Stacks, Tag 0G03] part (2).** Let `k` be a field, `X` a regular scheme of finite type
over `k`, `x ∈ X` a closed point, `𝒪_x` the skyscraper at `x` with value `κ(x)` and `K` a perfect
object of `D(𝒪_X)`. If `Hom_X(𝒪_x, K[i]) = 0` for all `i ∈ ℤ`, then `K` is zero on an open
neighbourhood of `x`. -/
@[stacks 0G03 "part (2), at the source's hypotheses: k a field, X a regular scheme of finite \
type over k, x a closed point, K perfect; if Hom_{D(𝒪_X)}(𝒪_x, K[i]) = 0 for all i then every \
cohomology sheaf of K has vanishing stalk at every point of an open neighbourhood of x"]
theorem exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper
    (k : Type u) [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : IsRegular X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj
      (residueFieldSkyscraperSheaf X x) ⟶ K⟦i⟧)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
  have : IsNoetherian X := isNoetherian_of_isRegular_of_finiteType k X sX hX
  obtain ⟨d, hd, -⟩ :=
    exists_mem_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper
      k X sX hX x hx K hK 0 (h 0)
  refine exists_mem_forall_isZero_stalkHomology_of_forall_exists X x K hK fun j => ?_
  obtain ⟨d', hd', hU⟩ :=
    exists_mem_isZero_stalkHomology_of_subsingleton_hom_from_residueFieldSkyscraper
      k X sX hX x hx K hK (j + d) (h (j + d))
  obtain rfl : d' = d := by exact_mod_cast hd'.symm.trans hd
  simpa using hU

/-- The derived tensor product of the ringed site of opens of a scheme is symmetric. -/
def schemeDerivedTensorSymmIso (X : Scheme.{u}) (A B : DerivedCategory X.Modules) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj A).obj B ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj B).obj A :=
  @Iso.trans (DerivedCategory X.Modules) inferInstance _ _ _
    (RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) A B)
    (@Iso.trans (DerivedCategory X.Modules) inferInstance _ _ _ (derivedTensorSymmIso X.sheaf A B)
      (@Iso.symm (DerivedCategory X.Modules) inferInstance _ _
        (RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) B A)))

/-- The target of an additive equivalence out of a subsingleton is a subsingleton. The additive
structures are implicit rather than instance arguments, so that they are read off the given
equivalence instead of being synthesized again. -/
theorem subsingleton_of_addEquiv {A B : Type*} {iA : Add A} {iB : Add B}
    (e : @AddEquiv A B iA iB) (h : Subsingleton A) : Subsingleton B :=
  @Function.Injective.subsingleton _ _ _ e.symm.injective h

/-- **Morphisms out of a perfect complex are global sections of the dual tensor product**, in
the direction used below: if `Hom(K, M) = 0` then `H^0(X, M ⊗^𝐋 K^∨) = 0`. This is
[Stacks, Tag 08JJ] at a perfect object, in the form
`AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual`. -/
theorem isZero_homology_derivedTensor_derivedDual_of_subsingleton_hom (X : Scheme.{u})
    (K M : DerivedCategory X.Modules) (hK : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect K)
    (h : Subsingleton (K ⟶ M)) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor
            (Stacks.SheafOfModules.ringedSite X.sheaf)).obj M).obj
              (Stacks.SheafOfModules.derivedDual X.sheaf K)))) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (subsingleton_of_addEquiv
    (RingedSite.homAddEquivHomologyDerivedTensorOfDual (Stacks.SheafOfModules.ringedSite X.sheaf)
      K (Stacks.SheafOfModules.derivedDual X.sheaf K) hK (Iso.refl _) M) h)

/-- **[Stacks, Tag 0G03] part (3).** Let `X` be a Noetherian scheme, `x ∈ X` a closed point,
`𝒪_x` the skyscraper at `x` with value `κ(x)` and `K` a perfect object of `D(𝒪_X)`, with dual
`K^∨ = R𝓗om(K, 𝒪_X)`. If `Ext^i_X(K, 𝒪_x) = 0`, then `H^i(K^∨)` vanishes on an open
neighbourhood of `x`. -/
@[stacks 0G03 "part (3), for X a Noetherian scheme (which every scheme of finite type over a \
field is), x a closed point and K perfect: Ext^i_X(K, 𝒪_x) is Hom_{D(𝒪_X)}(K, 𝒪_x[i]), K^∨ is \
R𝓗om(K, 𝒪_X), and H^i(K^∨)|_U = 0 is read as the vanishing of the stalk of H^i(K^∨) at every \
point of U"]
theorem exists_mem_isZero_stalkHomology_derivedDual_of_subsingleton_hom_to_residueFieldSkyscraper
    (X : Scheme.{u}) [IsNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (i : ℤ)
    (h : Subsingleton (K ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
      (residueFieldSkyscraperSheaf X x))⟦i⟧)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          (Stacks.SheafOfModules.derivedDual X.sheaf K))) := by
  have hK' : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect K :=
    (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace K).1 hK
  have hKd : RingedSpace.IsPerfect (X := X.toRingedSpace)
      (Stacks.SheafOfModules.derivedDual X.sheaf K) :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace K hK
  have hz := isZero_homology_derivedTensor_derivedDual_of_subsingleton_hom X K
    (((DerivedCategory.singleFunctor X.Modules 0).obj (residueFieldSkyscraperSheaf X x))⟦i⟧) hK' h
  have hz' := isZero_homology_globalSections_of_iso X
    (schemeDerivedTensorSymmIso X _ _ ≪≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (Stacks.SheafOfModules.ringedSite X.sheaf)).mapIso
          ((shiftFunctorZero (DerivedCategory X.Modules) ℤ).app
            (Stacks.SheafOfModules.derivedDual X.sheaf K))).symm.app _) 0 hz
  have hstalk := isZero_homology_derivedStalk_of_isZero_homology_globalSections_derivedTensor_shift
    X x hx (Stacks.SheafOfModules.derivedDual X.sheaf K) 0 i hz'
  rw [zero_add] at hstalk
  exact exists_mem_isZero_stalkHomology_of_derivedTensor_residueField X x _ hKd i hstalk

/-- **[Stacks, Tag 0G03] part (4).** Let `X` be a Noetherian scheme, `x ∈ X` a point, `𝒪_x`
the skyscraper at `x` with value `κ(x)` and `K` a perfect object of `D(𝒪_X)`. If
`Hom_X(K, 𝒪_x[i]) = 0` for all `i ∈ ℤ`, then `K` is zero on an open neighbourhood of `x`. -/
@[stacks 0G03 "part (4), for X a Noetherian scheme (which every scheme of finite type over a \
field is), x any point and K perfect: if Hom_{D(𝒪_X)}(K, 𝒪_x[i]) = 0 for all i then every \
cohomology sheaf of K has vanishing stalk at every point of an open neighbourhood of x"]
theorem exists_mem_forall_isZero_stalkHomology_of_subsingleton_hom_to_residueFieldSkyscraper
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton (K ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
      (residueFieldSkyscraper X x))⟦i⟧)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (OXModule.stalk ((DerivedCategory.homologyFunctor X.Modules i).obj K) y) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hcoh⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  let KB : DerivedCategory.Bounded X.Modules :=
    ⟨K, ⟨⟨a, (DerivedCategory.isGE_iff K a).2 ha⟩, ⟨b, (DerivedCategory.isLE_iff K b).2 hb⟩⟩⟩
  refine exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper X x KB hcoh
    fun i => ?_
  exact @Function.Injective.subsingleton _ _ _
    (Iso.homCongr (Iso.refl K) (((DerivedCategory.singleFunctors X.Modules).shiftIso
      (-i) i 0 (by omega)).app (residueFieldSkyscraper X x))).symm.injective (h (-i))

end AlgebraicGeometry

end
