module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.Algebra.Homology.HomBicomplexExt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Duality on a Cohen–Macaulay curve

Let `X` be a proper scheme over a field `k` which is Cohen–Macaulay and equidimensional of
dimension one, let `ω_X^• = f^×(𝒪_{Spec k})` be the dualizing complex and `ω_X = H^{-1}(ω_X^•)`
the dualizing sheaf of [Stacks, Tag 0BS2]. This file proves [Stacks, Tag 0BS3]:

1. `ω_X` is a dualizing module on `X`
   (`Stacks.Duality.isDualizingModuleOf_dualizingSheafOverField`);
2. `ω_X` is a coherent Cohen–Macaulay module whose support is `X`
   (`Stacks.Duality.dualizingSheafOverField_isCoherent_isCohenMacaulay_supp_eq_univ`);
3. there are functorial isomorphisms `Ext^i_X(K, ω_X[1]) = Hom_k(H^{-i}(X, K), k)` compatible with
   shifts for `K ∈ D_QCoh(𝒪_X)` (`Stacks.Duality.exists_extDualityShiftOne`);
4. there are functorial isomorphisms `Ext^{1 + i}(ℱ, ω_X) = Hom_k(H^{-i}(X, ℱ), k)` for
   quasi-coherent `ℱ` (`Stacks.Duality.exists_extSuccDuality`).

Everything rests on `ω_X^• ≅ ω_X[1]`
(`Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay`), proved in
`…/Curves/VanishingResults/CohenMacaulayDualizingComplex.lean` from the Cohen–Macaulay hypothesis
through [Stacks, Tag 0AWT], as in the source, and on the dualizing character of `ω_X^•`
(`Stacks.Duality.isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one`).
Clauses (3) and (4) are clause (4) of [Stacks, Tag 0BS2]
(`Stacks.Duality.extDualityAddEquiv`, natural by `Stacks.Duality.extDualityAddEquiv_naturality`,
compatible with the shift by `Stacks.Duality.extDualityAddEquiv_shift`) transported along that
isomorphism.

## Main definitions

* `Stacks.Duality.dualizingSheafShiftOne` — `ω_X[1]`.
* `Stacks.Duality.extDualityShiftOneAddEquiv` — `Ext^i_X(K, ω_X[1]) ≃+ Hom_k(H^{-i}(X, K), k)`.
* `Stacks.Duality.homDualityShiftOneAddEquiv` — `Hom(K, ω_X[1]) ≃+ Hom_k(H^0(X, K), k)`.
* `Stacks.Duality.extSuccDualityAddEquiv` — `Ext^{1+i}_X(ℱ, ω_X) ≃+ Hom_k(H^{-i}(X, ℱ), k)`.

## References

* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomBicomplex (postcompAddEquiv)

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **`ω_X[1]`**: the dualizing sheaf `ω_X = H^{-1}(ω_X^•)` placed in degree `-1`. -/
abbrev dualizingSheafShiftOne : DerivedCategory X.Modules :=
  ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))⟦(1 : ℤ)⟧

/-! ### Clauses (1) and (2) -/

/-- **[Stacks, Tag 0BS3], clause (1).** Let `X` be a proper scheme over a field `k` which is
Cohen–Macaulay and equidimensional of dimension one. Then `ω_X = H^{-1}(ω_X^•)` is a dualizing
module on `X` in the sense of [Stacks, Section 0AWH]: `ω_X^• = f^×(𝒪_{Spec k})` is a dualizing
complex, `-1` is the least degree in which it has nonzero cohomology, and `ω_X` is that
cohomology sheaf. -/
@[stacks 0BS3 "(1)"]
theorem isDualizingModuleOf_dualizingSheafOverField
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingModuleOf (dualizingSheafOverField f) (dualizingComplexOverField f).obj (-1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one f hdim.le,
    fun hz => ?_, fun i hi =>
      isZero_homology_dualizingComplexOverField_of_isCohenMacaulay f hcm hequi hdim i (by omega),
    rfl⟩
  have h1 : 1 ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds X) := by
    rw [← topologicalKrullDim, hdim]
  obtain ⟨-, B, -⟩ := Order.one_le_krullDim_iff.mp h1
  obtain ⟨x, -⟩ := B.isIrreducible.nonempty
  have hω := nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay f hcm hequi hdim x
  have hsz : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (dualizingSheafOverField f)) := Functor.map_isZero _ hz
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hsz
  exact not_nontrivial_iff_subsingleton.mpr hsub hω

/-- **[Stacks, Tag 0BS3], clause (2).** Let `X` be a proper scheme over a field `k` which is
Cohen–Macaulay and equidimensional of dimension one. Then `ω_X = H^{-1}(ω_X^•)` is a coherent
Cohen–Macaulay `𝒪_X`-module ([Stacks, Tag 0343]) whose support is `X`. -/
@[stacks 0BS3 "(2)"]
theorem dualizingSheafOverField_isCoherent_isCohenMacaulay_supp_eq_univ
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    _root_.SheafOfModules.IsCoherent (dualizingSheafOverField f) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X (dualizingSheafOverField f) ∧
      _root_.SheafOfModules.supp (dualizingSheafOverField f) = Set.univ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hK := isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one f hdim.le
  refine ⟨isCoherent_homology_of_isDualizingComplex hK (-1),
    sheafIsCohenMacaulay_homology_of_concentrated _ hK (-1) fun i hi =>
      isZero_homology_dualizingComplexOverField_of_isCohenMacaulay f hcm hequi hdim i hi, ?_⟩
  refine Set.eq_univ_of_forall fun x => ?_
  exact @exists_ne _
    (nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay f hcm hequi hdim x) 0

/-! ### Clause (3) -/

/-- **`Ext^i_X(K, ω_X[1]) ≃+ Hom_k(H^{-i}(X, K), k)`** for `K ∈ D_QCoh(𝒪_X)`: clause (4) of
[Stacks, Tag 0BS2] transported along `ω_X[1] ≅ ω_X^•`. -/
def extDualityShiftOneAddEquiv
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    DerivedCategory.Ext K.obj (dualizingSheafShiftOne f) i ≃+
      (derivedCohomologyOverField f K.obj (-i) ⟶ ModuleCat.of k k) :=
  (postcompAddEquiv ((shiftFunctor (DerivedCategory X.Modules) i).mapIso
    (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim))).trans
      (extDualityAddEquiv f K i)

/-- `extDualityShiftOneAddEquiv` sends `α : Ext^i(K, ω_X[1])` to the image under
`extDualityAddEquiv` of `α` composed with the `i`-th shift of `ω_X[1] ≅ ω_X^•`. -/
theorem extDualityShiftOneAddEquiv_apply
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (dualizingSheafShiftOne f) i) :
    extDualityShiftOneAddEquiv f hcm hequi hdim K i α =
      extDualityAddEquiv f K i (show K.obj ⟶ _ from (show K.obj ⟶ _ from α) ≫
        (shiftFunctor (DerivedCategory X.Modules) i).map
          (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).hom) := rfl

/-- **`Hom(K, ω_X[1]) ≃+ Hom_k(H^0(X, K), k)`** for `K ∈ D_QCoh(𝒪_X)`: the degree-zero duality
of [Stacks, Tag 0BS2] transported along `ω_X[1] ≅ ω_X^•`. -/
def homDualityShiftOneAddEquiv
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ dualizingSheafShiftOne f) ≃+
      (derivedCohomologyOverField f K.obj 0 ⟶ ModuleCat.of k k) :=
  (postcompAddEquiv (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim)).trans
    (dualityAddEquivZero f K)

/-- **Naturality in `K`** of `Stacks.Duality.extDualityShiftOneAddEquiv`. -/
theorem extDualityShiftOneAddEquiv_naturality
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K L : quasiCoherentDerivedCategory X) (i : ℤ)
    (g : K.obj ⟶ L.obj) (α : DerivedCategory.Ext L.obj (dualizingSheafShiftOne f) i) :
    extDualityShiftOneAddEquiv f hcm hequi hdim K i (g ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((derivedGlobalSectionsOver f).map g) ≫
        extDualityShiftOneAddEquiv f hcm hequi hdim L i α := by
  rw [extDualityShiftOneAddEquiv_apply, extDualityShiftOneAddEquiv_apply,
    ← extDualityAddEquiv_naturality]
  refine congrArg _ ?_
  exact Category.assoc _ _ _

/-- **Naturality in `K`** of `Stacks.Duality.homDualityShiftOneAddEquiv`. -/
theorem homDualityShiftOneAddEquiv_naturality
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K L : quasiCoherentDerivedCategory X)
    (g : K.obj ⟶ L.obj) (β : L.obj ⟶ dualizingSheafShiftOne f) :
    homDualityShiftOneAddEquiv f hcm hequi hdim K (g ≫ β) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver f).map g) ≫
        homDualityShiftOneAddEquiv f hcm hequi hdim L β := by
  show dualityAddEquivZero f K ((g ≫ β) ≫ _) = _ ≫ dualityAddEquivZero f L (β ≫ _)
  rw [← dualityAddEquivZero_naturality, Category.assoc]

/-- **Compatibility with the shift** of `Stacks.Duality.extDualityShiftOneAddEquiv`: the
degree-`i` identification at `K` is the degree-zero identification
`Stacks.Duality.homDualityShiftOneAddEquiv` at `K⟦-i⟧`, read through the shift adjunction
`Ext^i_X(K, ω_X[1]) = Hom(K⟦-i⟧, ω_X[1])` on the left and the shift comparison
`H^{-i}(X, K) = H^0(X, K⟦-i⟧)` on the right. -/
theorem extDualityShiftOneAddEquiv_shift
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (dualizingSheafShiftOne f) i) :
    extDualityShiftOneAddEquiv f hcm hequi hdim K i α =
      (derivedCohomologyShiftIso f K.obj (-i)).inv ≫
        homDualityShiftOneAddEquiv f hcm hequi hdim (shiftQuasiCoherent K (-i))
          (((shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).toAdjunction.homEquiv
            K.obj (dualizingSheafShiftOne f)).symm α) := by
  rw [extDualityShiftOneAddEquiv_apply, extDualityAddEquiv_shift]
  show _ = (derivedCohomologyShiftIso f K.obj (-i)).inv ≫
    dualityAddEquivZero f (shiftQuasiCoherent K (-i))
      (_ ≫ (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).hom)
  refine congrArg (fun z => (derivedCohomologyShiftIso f K.obj (-i)).inv ≫ z) ?_
  refine congrArg (dualityAddEquivZero f (shiftQuasiCoherent K (-i))) ?_
  show ((shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).toAdjunction.homEquiv
      K.obj (dualizingComplexOverField f).obj).symm (α ≫ (shiftFunctor _ i).map _) = _
  exact Adjunction.homEquiv_naturality_right_symm
    (shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).toAdjunction
    (show K.obj ⟶ _ from α) (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).hom

/-- **[Stacks, Tag 0BS3], clause (3).** Let `X` be a proper scheme over a field `k` which is
Cohen–Macaulay and equidimensional of dimension one, and `ω_X = H^{-1}(ω_X^•)`. There are
isomorphisms

  `Ext^i_X(K, ω_X[1]) = Hom_k(H^{-i}(X, K), k)`

for `K ∈ D_QCoh(𝒪_X)` and `i ∈ ℤ`, functorial in `K` and compatible with shifts: they come from
isomorphisms `Hom(K, ω_X[1]) = Hom_k(H^0(X, K), k)`, functorial in `K`, by reading
`Ext^i_X(K, ω_X[1])` as `Hom(K⟦-i⟧, ω_X[1])` (the shift adjunction) and `H^{-i}(X, K)` as
`H^0(X, K⟦-i⟧)`. -/
@[stacks 0BS3 "(3)"]
theorem exists_extDualityShiftOne
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    ∃ (e : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
        DerivedCategory.Ext K.obj (dualizingSheafShiftOne f) i ≃+
          (derivedCohomologyOverField f K.obj (-i) ⟶ ModuleCat.of k k))
      (e₀ : ∀ K : quasiCoherentDerivedCategory X,
        (K.obj ⟶ dualizingSheafShiftOne f) ≃+
          (derivedCohomologyOverField f K.obj 0 ⟶ ModuleCat.of k k)),
      (∀ (K L : quasiCoherentDerivedCategory X) (i : ℤ) (g : K.obj ⟶ L.obj)
          (α : DerivedCategory.Ext L.obj (dualizingSheafShiftOne f) i),
        e K i (g ≫ α) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
            ((derivedGlobalSectionsOver f).map g) ≫ e L i α) ∧
      (∀ (K L : quasiCoherentDerivedCategory X) (g : K.obj ⟶ L.obj)
          (β : L.obj ⟶ dualizingSheafShiftOne f),
        e₀ K (g ≫ β) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
            ((derivedGlobalSectionsOver f).map g) ≫ e₀ L β) ∧
      (∀ (K : quasiCoherentDerivedCategory X) (i : ℤ)
          (α : DerivedCategory.Ext K.obj (dualizingSheafShiftOne f) i),
        e K i α = (derivedCohomologyShiftIso f K.obj (-i)).inv ≫
          e₀ (shiftQuasiCoherent K (-i))
            (((shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).toAdjunction.homEquiv
              K.obj (dualizingSheafShiftOne f)).symm α)) :=
  ⟨extDualityShiftOneAddEquiv f hcm hequi hdim, homDualityShiftOneAddEquiv f hcm hequi hdim,
    extDualityShiftOneAddEquiv_naturality f hcm hequi hdim,
    homDualityShiftOneAddEquiv_naturality f hcm hequi hdim,
    extDualityShiftOneAddEquiv_shift f hcm hequi hdim⟩

/-! ### Clause (4) -/

/-- `Ext^{1+i}(ℱ, ω_X) = Ext^i(ℱ, ω_X[1])`: the shift `⟦1 + i⟧` is the shift `⟦1⟧` followed by
the shift `⟦i⟧`. -/
def extSuccAddEquivExtShift (F : X.Modules) (i : ℤ) :
    DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f)) (1 + i) ≃+
      DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        (dualizingSheafShiftOne f) i :=
  postcompAddEquiv ((shiftFunctorAdd' (DerivedCategory X.Modules) 1 i (1 + i) rfl).app
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f)))

/-- **`Ext^{1+i}_X(ℱ, ω_X) ≃+ Hom_k(H^{-i}(X, ℱ), k)`** for a quasi-coherent `ℱ`. -/
def extSuccDualityAddEquiv
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℤ) :
    DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f)) (1 + i) ≃+
      (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) (-i) ⟶
        ModuleCat.of k k) :=
  (extSuccAddEquivExtShift f F i).trans
    (extDualityShiftOneAddEquiv f hcm hequi hdim (singleQuasiCoherent F hF 0) i)

/-- **Naturality in `ℱ`** of `Stacks.Duality.extSuccDualityAddEquiv`. -/
theorem extSuccDualityAddEquiv_naturality
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (F G : X.Modules) (hF : F.IsQuasicoherent)
    (hG : G.IsQuasicoherent) (i : ℤ) (u : F ⟶ G)
    (α : DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj G)
        ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f)) (1 + i)) :
    extSuccDualityAddEquiv f hcm hequi hdim F hF i
        ((DerivedCategory.singleFunctor X.Modules 0).map u ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((derivedGlobalSectionsOver f).map ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫
        extSuccDualityAddEquiv f hcm hequi hdim G hG i α := by
  have h := extDualityShiftOneAddEquiv_naturality f hcm hequi hdim (singleQuasiCoherent F hF 0)
    (singleQuasiCoherent G hG 0) i ((DerivedCategory.singleFunctor X.Modules 0).map u)
    (extSuccAddEquivExtShift f G i α)
  refine Eq.trans ?_ h
  refine congrArg (extDualityShiftOneAddEquiv f hcm hequi hdim (singleQuasiCoherent F hF 0) i) ?_
  exact Category.assoc (obj := DerivedCategory X.Modules) _ _ _

/-- **[Stacks, Tag 0BS3], clause (4).** Let `X` be a proper scheme over a field `k` which is
Cohen–Macaulay and equidimensional of dimension one, and `ω_X = H^{-1}(ω_X^•)`. There are
isomorphisms

  `Ext^{1 + i}_X(ℱ, ω_X) = Hom_k(H^{-i}(X, ℱ), k)`

for quasi-coherent `ℱ` on `X` and `i ∈ ℤ`, functorial in `ℱ`. -/
@[stacks 0BS3 "(4)"]
theorem exists_extSuccDuality
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    ∃ e : ∀ (F : X.Modules) (_ : F.IsQuasicoherent) (i : ℤ),
        DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj F)
            ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))
            (1 + i) ≃+
          (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) (-i) ⟶
            ModuleCat.of k k),
      ∀ (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (i : ℤ) (u : F ⟶ G)
        (α : DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj G)
          ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f)) (1 + i)),
        e F hF i ((DerivedCategory.singleFunctor X.Modules 0).map u ≫ α) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
              ((derivedGlobalSectionsOver f).map
                ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫
            e G hG i α :=
  ⟨extSuccDualityAddEquiv f hcm hequi hdim, extSuccDualityAddEquiv_naturality f hcm hequi hdim⟩

end Stacks.Duality

end
