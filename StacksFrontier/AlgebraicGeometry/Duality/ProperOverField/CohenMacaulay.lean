module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality for a proper Cohen--Macaulay scheme over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, which is
Cohen--Macaulay and equidimensional of dimension `d`. Let `ω_X^• = a(𝒪_{Spec k})` be its
dualizing complex and `ω_X = H^{-d}(ω_X^•)` its dualizing module, as in [Stacks, Tag 0FVV]
(`Stacks.Duality.relativeDualizingComplex`, `Stacks.Duality.relativeDualizingModule`).
[Stacks, Tag 0FVZ] says:

1. `ω_X` is a dualizing module on `X` in the sense of [Stacks, Section 0AWH];
2. `ω_X` is a coherent Cohen--Macaulay module whose support is `X`;
3. there are functorial isomorphisms `Ext^i_X(K, ω_X[d]) = Hom_k(H^{-i}(X, K), k)`, compatible with
   shifts and distinguished triangles, for `K ∈ D_QCoh(𝒪_X)`;
4. there are functorial isomorphisms `Ext^{d - i}(F, ω_X) = Hom_k(H^i(X, F), k)` for `F`
   quasi-coherent.

## Main results

* `Stacks.Duality.isZero_homology_relativeDualizingComplex_of_ne_of_isProper` — the cohomology of
  `ω_X^•` is concentrated in degree `-d`.
* `Stacks.Duality.relativeDualizingComplexIsoShiftOfIsProper` — `ω_X^• ≅ ω_X[d]`.
* `Stacks.Duality.isDualizingModuleOf_relativeDualizingModule_of_isProper` — part (1).
* `Stacks.Duality.relativeDualizingModule_isCoherent_cohenMacaulay_supp_of_isProper` — part (2).
* `Stacks.Duality.dualityEquivShiftOfIsProper` and its companions — part (3).
* `Stacks.Duality.dualizingModuleExtEquivOfIsProper` and its naturality — part (4).

## Implementation notes

The proof is the source's. Since `X` is equidimensional, every irreducible component has
dimension `d = dim X`, so by part (2) of [Stacks, Tag 0FVV] the support of `ω_X = H^{-d}(ω_X^•)`
is all of `X`. Since `X` is Cohen--Macaulay, at every point `x` the stalks of the cohomology
sheaves of `ω_X^•` are concentrated in a single degree ([Stacks, Tag 0AWT], clause (2),
`Stacks.Duality.isCohenMacaulayLocalRing_stalk_iff_stalkwise`); that degree is `-d` because the
stalk of `H^{-d}(ω_X^•)` at `x` is nonzero. Hence `H^i(ω_X^•) = 0` for `i ≠ -d` and
`ω_X^• = ω_X[d]`. Part (1) is then the definition of a dualizing module
(`Stacks.Duality.IsDualizingModuleOf`), part (2) is [Stacks, Tag 0AWT]'s Cohen--Macaulayness of
the concentrated cohomology sheaf (`Stacks.Duality.sheafIsCohenMacaulay_homology_of_concentrated`)
with coherence from [Stacks, Tag 0FVV], and parts (3) and (4) are part (5) of [Stacks, Tag 0FVV]
(`Stacks.Duality.dualityEquiv`) transported along `ω_X^• ≅ ω_X[d]`, using
`Ext^{d-i}(F, ω_X) = Ext^{-i}(F[0], ω_X[d])` and `H^{-(-i)}(X, F[0]) = H^i(X, F)` for part (4).

`ω_X[d]` is written literally as `((DerivedCategory.singleFunctor X.Modules 0).obj ω_X)⟦d⟧`, and
`Ext^{d-i}(F, ω_X)` is `CategoryTheory.Abelian.zExt F ω_X (d - i)`, the `ℤ`-graded `Ext` of
[Stacks, Tag 06XQ]. "Equidimensional of dimension `d`" is `TopologicalSpace.Equidimensional X`
([Stacks, Tag 0058]) together with `topologicalKrullDim X = d`. The derived categories are those of
[Stacks, Tag 0FVV] in the base, at which `ω_X^•` is defined.

## References

* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Section 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open StacksDraft.DerivedHom.HomModuleBaseChange (postcompLinearEquiv)

universe u

/-- **On an equidimensional space every irreducible component has the dimension of the space.**
The dimension of a space is the supremum of the dimensions of its irreducible components, and on
an equidimensional space these are all equal. -/
@[ega "0 14.1.3"]
theorem TopologicalSpace.Equidimensional.topologicalKrullDim_eq_of_mem_irreducibleComponents
    {T : Type*} [TopologicalSpace T] (h : TopologicalSpace.Equidimensional T) {C : Set T}
    (hC : C ∈ irreducibleComponents T) :
    topologicalKrullDim C = topologicalKrullDim T := by
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents T]
  exact le_antisymm (le_iSup₂_of_le C hC le_rfl) (iSup₂_le fun W hW => (h W hW C hC).le)

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- The relative dualizing module `ω_X = H^{-dim X}(ω_X^•)` of `f : X ⟶ Spec k`. -/
local notation "ωM" =>
  relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- On an equidimensional proper scheme over a field the dualizing module `ω_X` has full support:
by part (2) of [Stacks, Tag 0FVV] its support is the union of the irreducible components of
dimension `dim X`, which are all of them. -/
theorem supp_relativeDualizingModule_eq_univ_of_isProper
    (hequi : TopologicalSpace.Equidimensional X) :
    _root_.SheafOfModules.supp ωM = Set.univ := by
  rw [(relativeDualizingModule_of_isProper f).2.2]
  have : {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} =
      irreducibleComponents X :=
    Set.sep_eq_self_iff_mem_true.mpr fun C hC =>
      hequi.topologicalKrullDim_eq_of_mem_irreducibleComponents hC
  rw [this, sUnion_irreducibleComponents]

/-- The stalks of `ω_X` are nontrivial when `X` is equidimensional, since `ω_X` has full support. -/
private theorem nontrivial_stalk_relativeDualizingModule
    (hequi : TopologicalSpace.Equidimensional X) (y : X) : Nontrivial ((ωM).presheaf.stalk y) :=
  (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mp
    (supp_relativeDualizingModule_eq_univ_of_isProper f hequi ▸ Set.mem_univ y)

/-- On a Cohen--Macaulay equidimensional proper scheme over a field the cohomology sheaves of
`ω_X^•` vanish outside degree `-dim X`: at every point the stalks are concentrated in one degree
([Stacks, Tag 0AWT], clause (2)), and that degree is `-dim X` because `ω_X = H^{-dim X}(ω_X^•)` has
full support. -/
theorem isZero_homology_relativeDualizingComplex_of_ne_of_isProper
    (hCM : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (j : ℤ) (hj : j ≠ -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj (ωX).obj) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  have hK := isDualizingComplex_relativeDualizingComplex_of_isProper f
  refine (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
    X.ringCatSheaf _).mpr fun y => ModuleCat.isZero_iff_subsingleton.mpr ?_
  obtain ⟨-, hCMx⟩ := ((AlgebraicGeometry.isCohenMacaulay_tfae_stalk X).out 1 2).mp hCM
  obtain ⟨_, hy⟩ := hCMx y
  obtain ⟨n, hn⟩ := (isCohenMacaulayLocalRing_stalk_iff_stalkwise _ hK y).mp hy
  have hnt := nontrivial_stalk_relativeDualizingModule f hequi y
  have hn0 : n = -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ) := by
    by_contra hne
    exact not_subsingleton_iff_nontrivial.mpr hnt (hn _ (Ne.symm hne))
  subst hn0
  exact hn j hj

/-- `-dim X = -d` for `X` of dimension `d`, in the form in which `ω_X = H^{-dim X}(ω_X^•)` is
defined. -/
theorem neg_toNat_getD_topologicalKrullDim_eq {d : ℕ} (hd : topologicalKrullDim X = d) :
    -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ) = -(d : ℤ) := by
  rw [hd]
  rfl

/-- **`ω_X^• = ω_X[d]`.** On a proper scheme over a field which is Cohen--Macaulay and
equidimensional of dimension `d`, the dualizing complex `ω_X^•` is the dualizing module `ω_X`
placed in degree `-d`, i.e. shifted by `d`. -/
def relativeDualizingComplexIsoShiftOfIsProper (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d) :
    (ωX).obj ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧ :=
  have hn := neg_toNat_getD_topologicalKrullDim_eq (X := X) hd
  have hz : ∀ j : ℤ, j ≠ -(d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj (ωX).obj) := fun j hj =>
    isZero_homology_relativeDualizingComplex_of_ne_of_isProper f hCM hequi j (hn ▸ hj)
  haveI : (ωX).obj.IsGE (-(d : ℤ)) :=
    (DerivedCategory.isGE_iff _ _).2 fun j hj => hz j (by omega)
  haveI : (ωX).obj.IsLE (-(d : ℤ)) :=
    (DerivedCategory.isLE_iff _ _).2 fun j hj => hz j (by omega)
  have hex := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ωX).obj (-(d : ℤ))
  let e : (ωX).obj ≅ (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).obj hex.choose :=
    hex.choose_spec.some
  let eH : ωM ≅ hex.choose :=
    eqToIso (congrArg (fun n => (DerivedCategory.homologyFunctor X.Modules n).obj (ωX).obj) hn) ≪≫
      (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-(d : ℤ))).app _
  e ≪≫ (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).mapIso eH.symm ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (d : ℤ) (-(d : ℤ)) 0
      (by omega)).symm.app ωM

/-- **[Stacks, Tag 0FVZ], part (1).** Let `X` be a proper scheme over a field `k` which is
Cohen--Macaulay and equidimensional of dimension `d`. The module `ω_X` of [Stacks, Tag 0FVV] is a
dualizing module on `X` in the sense of [Stacks, Section 0AWH]: `ω_X^•` is a dualizing complex,
`-d` is the least degree in which it has nonzero cohomology, and `ω_X = H^{-d}(ω_X^•)`. -/
@[stacks 0FVZ "part (1): ω_X is a dualizing module on X (Section 0AWH)"]
theorem isDualizingModuleOf_relativeDualizingModule_of_isProper
    (hCM : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (d : ℕ) (hd : topologicalKrullDim X = d) :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingModuleOf ωM (ωX).obj (-(d : ℤ)) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  have hn := neg_toNat_getD_topologicalKrullDim_eq (X := X) hd
  have hne : (Set.univ : Set X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.univ_eq_empty_iff] at h
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty X).mpr h] at hd
    exact WithBot.bot_ne_coe hd
  obtain ⟨y, -⟩ := hne
  refine ⟨isDualizingComplex_relativeDualizingComplex_of_isProper f, ?_, ?_, ?_⟩
  · intro hz
    have hnt := nontrivial_stalk_relativeDualizingModule f hequi y
    have hz' : IsZero ωM := by
      change IsZero ((DerivedCategory.homologyFunctor X.Modules _).obj (ωX).obj)
      rw [hn]
      exact hz
    have := ModuleCat.isZero_iff_subsingleton.mp
      (((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
        X.ringCatSheaf _).mp hz') y)
    exact not_subsingleton_iff_nontrivial.mpr hnt this
  · intro j hj
    exact isZero_homology_relativeDualizingComplex_of_ne_of_isProper f hCM hequi j
      (by rw [hn]; omega)
  · change (DerivedCategory.homologyFunctor X.Modules _).obj (ωX).obj = _
    rw [hn]

/-- **[Stacks, Tag 0FVZ], part (2).** Let `X` be a proper scheme over a field `k` which is
Cohen--Macaulay and equidimensional of dimension `d`. The module `ω_X` of [Stacks, Tag 0FVV] is a
coherent Cohen--Macaulay `𝒪_X`-module whose support is `X`. -/
@[stacks 0FVZ "part (2): ω_X is a coherent Cohen-Macaulay module whose support is X"]
theorem relativeDualizingModule_isCoherent_cohenMacaulay_supp_of_isProper
    (hCM : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X) :
    (ωM).IsCoherent ∧ AlgebraicGeometry.SheafIsCohenMacaulay X ωM ∧
      _root_.SheafOfModules.supp ωM = Set.univ := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨(relativeDualizingModule_of_isProper f).1, ?_,
    supp_relativeDualizingModule_eq_univ_of_isProper f hequi⟩
  exact sheafIsCohenMacaulay_homology_of_concentrated (ωX).obj
    (isDualizingComplex_relativeDualizingComplex_of_isProper f) _
    (isZero_homology_relativeDualizingComplex_of_ne_of_isProper f hCM hequi)

/-! ### Part (3): duality against `ω_X[d]` -/

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)` on `D(𝒪_X)`, with values in `k`-vector spaces; its shift sequence
is `H^n(X, -) = H^n ∘ RΓ(X, -)`. -/
local notation "HX" => derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- **[Stacks, Tag 0FVZ], part (3), the isomorphisms.** Let `X` be a proper scheme over a field `k`
which is Cohen--Macaulay and equidimensional of dimension `d`. For `K` in `D_QCoh(𝒪_X)` and every
`i` there is a `k`-linear isomorphism `Ext^i_X(K, ω_X[d]) ≅ Hom_k(H^{-i}(X, K), k)`. It is part (5)
of [Stacks, Tag 0FVV] (`Stacks.Duality.dualityEquiv`) read through `ω_X^• ≅ ω_X[d]`
(`Stacks.Duality.relativeDualizingComplexIsoShiftOfIsProper`); it is natural in `K`
(`Stacks.Duality.dualityEquivShiftOfIsProper_comp`) and compatible with shifts and distinguished
triangles (`Stacks.Duality.dualityEquivShiftOfIsProper_shiftedHomComp`,
`Stacks.Duality.dualityEquivShiftOfIsProper_shift`,
`Stacks.Duality.dualityEquivShiftOfIsProper_triangle`). -/
@[stacks 0FVZ "part (3): the isomorphisms Ext^i_X(K, ω_X[d]) = Hom_k(H^{-i}(X, K), k)"]
def dualityEquivShiftOfIsProper (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    letI := Scheme.linearOver f
    DerivedCategory.Ext K.obj (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i
      ≃ₗ[k] ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj K.obj) →ₗ[k] k) :=
  letI := Scheme.linearOver f
  postcompLinearEquiv k K.obj ((shiftFunctor (DerivedCategory X.Modules) i).mapIso
      (relativeDualizingComplexIsoShiftOfIsProper f hCM hequi d hd).symm) ≪≫ₗ
    dualityEquiv f K i

/-- The isomorphism of part (3) is that of part (5) of [Stacks, Tag 0FVV] after composing with
`ω_X[d] ≅ ω_X^•`. -/
theorem dualityEquivShiftOfIsProper_apply (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquivShiftOfIsProper f hCM hequi d hd K i α x =
      dualityEquiv f K i (α ≫ (shiftFunctor (DerivedCategory X.Modules) i).map
        (relativeDualizingComplexIsoShiftOfIsProper f hCM hequi d hd).inv) x := by
  rfl

/-- **[Stacks, Tag 0FVZ], part (3), functoriality.** The isomorphisms of part (3) are natural in
`K`: for `g : K ⟶ L` and `α ∈ Ext^i_X(L, ω_X[d])`, the linear form attached to `g ≫ α` is the one
attached to `α` precomposed with `H^{-i}(X, g)`. -/
@[stacks 0FVZ "part (3): the isomorphisms are functorial in K"]
theorem dualityEquivShiftOfIsProper_comp (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (K L : quasiCoherentDerivedCategory X) (i : ℤ) (g : K.obj ⟶ L.obj)
    (α : DerivedCategory.Ext L.obj
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquivShiftOfIsProper f hCM hequi d hd K i (g ≫ α) x =
      dualityEquivShiftOfIsProper f hCM hequi d hd L i α
        ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
          ((derivedGlobalSectionsOver f).map g) x) := by
  exact (congrArg (fun a => dualityEquiv f K i a x) (Category.assoc _ _ _)).trans
    (dualityEquiv_comp f K L i g _ x)

/-- Composition with `ω_X[d] ≅ ω_X^•` commutes with precomposition by a shifted morphism. -/
theorem shiftedHomComp_comp_shift_map {L K Y Z : DerivedCategory X.Modules} {i j c : ℤ}
    (β : DerivedCategory.Ext L K j) (α : DerivedCategory.Ext K Y i) (h : i + j = c)
    (e : Y ⟶ Z) :
    (β.comp α h) ≫ (shiftFunctor (DerivedCategory X.Modules) c).map e =
      β.comp (α ≫ (shiftFunctor (DerivedCategory X.Modules) i).map e) h := by
  rw [← ShiftedHom.comp_mk₀ (β.comp α h) (0 : ℤ) rfl e, ← ShiftedHom.comp_mk₀ α (0 : ℤ) rfl e,
    ShiftedHom.comp_assoc β α _ h (zero_add i) (by omega)]

/-- **[Stacks, Tag 0FVZ], part (3), compatibility with shifted morphisms.** For
`β ∈ Ext^j_X(L, K)` and `α ∈ Ext^i_X(K, ω_X[d])`, the linear form on `H^{-(i+j)}(X, L)` attached to
`β.comp α ∈ Ext^{i+j}_X(L, ω_X[d])` is the one attached to `α` precomposed with the map
`H^{-(i+j)}(X, L) ⟶ H^{-i}(X, K)` induced by `β`. This contains the compatibility with shifts
(`Stacks.Duality.dualityEquivShiftOfIsProper_shift`) and with distinguished triangles
(`Stacks.Duality.dualityEquivShiftOfIsProper_triangle`). -/
@[stacks 0FVZ "part (3): compatibility with shifts and distinguished triangles"]
theorem dualityEquivShiftOfIsProper_shiftedHomComp (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (K L : quasiCoherentDerivedCategory X) {i j c : ℤ}
    (β : DerivedCategory.Ext L.obj K.obj j)
    (α : DerivedCategory.Ext K.obj
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i)
    (h : i + j = c)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-c)).obj
      ((derivedGlobalSectionsOver f).obj L.obj)) :
    letI := Scheme.linearOver f
    dualityEquivShiftOfIsProper f hCM hequi d hd L c (β.comp α h) x =
      dualityEquivShiftOfIsProper f hCM hequi d hd K i α
        ((HX).shiftMap β (-c) (-i) (by omega) x) := by
  exact (congrArg (fun a => dualityEquiv f L c a x) (shiftedHomComp_comp_shift_map β α h _)).trans
    (dualityEquiv_shiftedHomComp f K L β _ h x)

/-- **[Stacks, Tag 0FVZ], part (3), compatibility with shifts.** Under
`Ext^{i+n}_X(K⟦n⟧, ω_X[d]) = Ext^i_X(K, ω_X[d])` (composition with the identity of `K⟦n⟧`) and
`H^{-(i+n)}(X, K⟦n⟧) ≅ H^{-i}(X, K)`, the isomorphisms of `K⟦n⟧` and of `K` agree. -/
@[stacks 0FVZ "part (3): compatibility with shifts"]
theorem dualityEquivShiftOfIsProper_shift (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (K : quasiCoherentDerivedCategory X) (i n : ℤ)
    (α : DerivedCategory.Ext K.obj
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + n))).obj
      ((derivedGlobalSectionsOver f).obj (K.obj⟦n⟧))) :
    letI := Scheme.linearOver f
    dualityEquivShiftOfIsProper f hCM hequi d hd
        ⟨K.obj⟦n⟧, ObjectProperty.le_shift _ n K.obj K.property⟩ (i + n)
        (ShiftedHom.comp (𝟙 (K.obj⟦n⟧)) α rfl) x =
      dualityEquivShiftOfIsProper f hCM hequi d hd K i α
        (((HX).shiftIso n (-(i + n)) (-i) (by omega)).hom.app K.obj x) := by
  rw [dualityEquivShiftOfIsProper_shiftedHomComp f hCM hequi d hd K _ _ α rfl,
    Functor.shiftMap_id]

/-- **[Stacks, Tag 0FVZ], part (3), compatibility with distinguished triangles.** For a triangle
`K ⟶ L ⟶ M ⟶ K⟦1⟧` in `D_QCoh(𝒪_X)`, the isomorphisms intertwine composition with its third
morphism, `Ext^i_X(K, ω_X[d]) ⟶ Ext^{i+1}_X(M, ω_X[d])`, and the connecting morphism
`H^{-(i+1)}(X, M) ⟶ H^{-i}(X, K)` of the long exact cohomology sequence. -/
@[stacks 0FVZ "part (3): compatibility with distinguished triangles"]
theorem dualityEquivShiftOfIsProper_triangle (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (T : Pretriangulated.Triangle (DerivedCategory X.Modules))
    (h₁ : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₁)
    (h₃ : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₃)
    (i : ℤ)
    (α : DerivedCategory.Ext T.obj₁
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωM)⟦(d : ℤ)⟧) i)
    (x : (DerivedCategory.homologyFunctor (ModuleCat k) (-(i + 1))).obj
      ((derivedGlobalSectionsOver f).obj T.obj₃)) :
    letI := Scheme.linearOver f
    dualityEquivShiftOfIsProper f hCM hequi d hd ⟨T.obj₃, h₃⟩ (i + 1)
        (ShiftedHom.comp (T.mor₃ : DerivedCategory.Ext T.obj₃ T.obj₁ 1) α rfl) x =
      dualityEquivShiftOfIsProper f hCM hequi d hd ⟨T.obj₁, h₁⟩ i α
        ((HX).homologySequenceδ T (-(i + 1)) (-i) (by omega) x) := by
  rw [dualityEquivShiftOfIsProper_shiftedHomComp f hCM hequi d hd ⟨T.obj₁, h₁⟩ ⟨T.obj₃, h₃⟩ _ α
    rfl]
  rfl

/-! ### Part (4): `Ext^{d-i}(F, ω_X) = Hom_k(H^i(X, F), k)` -/

/-- **[Stacks, Tag 0FVZ], part (4).** Let `X` be a proper scheme over a field `k` which is
Cohen--Macaulay and equidimensional of dimension `d`. For `F` a quasi-coherent `𝒪_X`-module there
are `k`-linear isomorphisms `Ext^{d-i}_X(F, ω_X) ≅ Hom_k(H^i(X, F), k)`, natural in `F`
(`Stacks.Duality.dualizingModuleExtEquivOfIsProper_comp`). It is part (3) for `K = F[0]` in degree
`-i`, through `Ext^{d-i}(F[0], ω_X[0]) = Ext^{-i}(F[0], ω_X[d])` and
`H^{-(-i)}(X, F[0]) = H^i(X, F)`. -/
@[stacks 0FVZ "part (4): Ext^{d-i}(F, ω_X) = Hom_k(H^i(X, F), k) for F quasi-coherent"]
def dualizingModuleExtEquivOfIsProper (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    letI := Scheme.linearOver f
    Abelian.zExt F ωM ((d : ℤ) - i) ≃ₗ[k] (cohomologyOverField k f F i →ₗ[k] k) :=
  letI := Scheme.linearOver f
  postcompLinearEquiv k ((DerivedCategory.singleFunctor X.Modules 0).obj F)
      ((shiftFunctorAdd' (DerivedCategory X.Modules) (d : ℤ) (-(i : ℤ)) ((d : ℤ) - i)
        (by omega)).app ((DerivedCategory.singleFunctor X.Modules 0).obj ωM)) ≪≫ₗ
    dualityEquivShiftOfIsProper f hCM hequi d hd (singleQuasiCoherentDegreeZero F) (-(i : ℤ)) ≪≫ₗ
    LinearEquiv.arrowCongr ((hypercohomologyNegNegIso f i).app F).toLinearEquiv
      (LinearEquiv.refl k k)

/-- **[Stacks, Tag 0FVZ], part (4), functoriality.** The isomorphisms of part (4) are natural in
the quasi-coherent module `F`: for `φ : F ⟶ G` and `α ∈ Ext^{d-i}_X(G, ω_X)`, the linear form
attached to `φ ≫ α` is the one attached to `α` precomposed with `H^i(X, φ)`. -/
@[stacks 0FVZ "part (4): the isomorphisms are functorial in F"]
theorem dualizingModuleExtEquivOfIsProper_comp (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (i : ℕ)
    (α : Abelian.zExt G ωM ((d : ℤ) - i)) (x : cohomologyOverField k f F i) :
    letI := Scheme.linearOver f
    dualizingModuleExtEquivOfIsProper f hCM hequi d hd F i
        ((DerivedCategory.singleFunctor X.Modules 0).map φ ≫ α) x =
      dualizingModuleExtEquivOfIsProper f hCM hequi d hd G i α
        ((cohomologyOverFieldFunctor k f i).map φ x) := by
  let := Scheme.linearOver f
  have h₂ := congrArg (fun y ↦ y.hom x) ((hypercohomologyNegNegIso f i).inv.naturality φ)
  exact (congrArg (fun a => dualityEquivShiftOfIsProper f hCM hequi d hd
      (singleQuasiCoherentDegreeZero F) (-(i : ℤ)) a
        (((hypercohomologyNegNegIso f i).app F).inv x)) (Category.assoc _ _ _)).trans
    ((dualityEquivShiftOfIsProper_comp f hCM hequi d hd (singleQuasiCoherentDegreeZero F)
      (singleQuasiCoherentDegreeZero G) _ ((DerivedCategory.singleFunctor X.Modules 0).map φ) _
        _).trans (congrArg _ h₂.symm))

end Stacks.Duality

end
