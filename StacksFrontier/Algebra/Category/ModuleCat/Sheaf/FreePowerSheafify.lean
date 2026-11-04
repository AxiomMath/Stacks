module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerFree
public import StacksFrontier.LinearAlgebra.SymmetricPower.MonomialBasis

/-!
# The symmetric and exterior powers of a finite free sheaf of modules are free

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `ι` a finite type.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerFree` settles the *sectionwise* half of the
free case of Stacks Tag 00DN: over each object `V` separately, the sections
`Symⁿ_{O♯(V)}((free ι)(V))` and `⋀ⁿ_{O♯(V)}((free ι)(V))` are free `O♯(V)`-modules of finite rank,
on the degree-`n` multidegrees `{d : ι →₀ ℕ | d.degree = n}` and on the `n`-element subsets
`Set.powersetCard ι n` respectively. The *sheaf-level* assertion
`Symⁿ (free ι) ≅ free {d | d.degree = n}` needs those isomorphisms to be **natural in `V`**.

This file proves the naturality and draws the sheaf-level conclusion. The free case of Stacks Tag
01CK clause (6) — the symmetric and exterior powers of a free sheaf of modules of finite rank are
free of finite rank — is `Stacks.SheafOfModules.symmetricPowerFreeIso` and
`exteriorPowerFreeIso`, with `symmetricPowerFreeIsoOfIso` and `exteriorPowerFreeIsoOfIso` for a
sheaf of modules merely isomorphic to a finite free one and
`exists_finite_nonempty_iso_free_symmetricPower`, `exists_finite_nonempty_iso_free_exteriorPower`
asserting the existence of such an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.symPowFreeEquiv` and `extPowFreeEquiv`: the sections of the sectionwise
  symmetric (respectively exterior) power of `free ι` over an object, identified with the sections
  of the free sheaf of modules on the monomial index, by matching the two bases.
* `Stacks.SheafOfModules.symPowFreeIso` and `extPowFreeIso`: **those identifications as
  isomorphisms of presheaves of modules**.
* `Stacks.SheafOfModules.symmetricPowerFreeIso` and `exteriorPowerFreeIso`: **the sheaf-level
  isomorphisms** `Symⁿ (free ι) ≅ free {d | d.degree = n}` and
  `⋀ⁿ (free ι) ≅ free (Set.powersetCard ι n)`, for an arbitrary package of algebras in the sense
  of Section 17.21 over `free ι`.
* `Stacks.SheafOfModules.symmetricPowerFreeIsoOfIso` and `exteriorPowerFreeIsoOfIso`: the same
  for a package over a sheaf of modules isomorphic to `free ι`.

## Main results

* `Finsupp.exists_prod_fin_eq_prod`: **a multidegree of total degree `n` can be enumerated by
  `Fin n` once and for all**, before any family of factors is given.
* `SymPow.exists_prod_ι_eq_coe_basisSymmetricPower_uniform`: the monomial formula for
  `SymPow.basisSymmetricPower` with the enumeration chosen before the module, so that one tuple of
  indices computes the basis vector over two different rings.
* `Stacks.SheafOfModules.freeCoordBasis_map`: the basis of the sections of a finite free sheaf of
  modules is natural.
* `Stacks.SheafOfModules.basisSymPowSections_map` and `basisExtPowSections_map`: **the monomial
  bases of the sectionwise symmetric and exterior powers of a finite free sheaf of modules are
  natural.**
* `Stacks.SheafOfModules.exists_finite_nonempty_iso_free_symmetricPower` and
  `exists_finite_nonempty_iso_free_exteriorPower`: every symmetric or exterior power of a sheaf of
  modules isomorphic to a finite free one is free of finite rank.

## Implementation notes

**`SheafOfModules.valPresheaf J G` is interchangeable with `G.val`.** The sheaf-level
isomorphisms compose `SheafOfModules.symmetricPowerSheafifyIso` with the sheafification of
`symPowFreeIso` and with `SheafOfModules.sheafifyValIso`, and the first two are stated at
`PresheafOfModules.symPow n (valPresheaf J G)` while the middle one is stated at
`PresheafOfModules.symPow n G.val`. Those agree at default transparency —
`PresheafOfModules.restrictScalars` along an identity changes only the spelling of the scalar
action — which is the same fact that lets `SheafOfModules.symPowCmp` be passed to
`PresheafOfModules.sheafificationHomEquiv`. No bridge isomorphism is needed and none is built.

**The index type is `Type u`, the module universe.** `SheafOfModules.free` is only defined for an
index in the module universe, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf` records the same constraint: the
coproduct `∐ (fun _ : ι => unit O)` lands in `SheafOfModules.{max w u}` for `ι : Type w`, and the
free form is ill-typed rather than merely hard. Nothing here is narrowed relative to
`FreePowerFree`, whose site universes `u₁`, `v` are independent of the ring-and-module universe.

**The index is finite.** The whole argument runs through `Stacks.SheafOfModules.freeCoordBasis`,
which exists only for a finite index because `(free ι)(V)` is computed by `freeCoord_bijective`
from the coproduct being a product.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.GradedAlgebra (ringSheafOfIsSheaf)

universe w'

namespace Finsupp

/-- The degree-`n` multidegrees in finitely many variables form a finite type. -/
instance instFiniteDegreeEq {κ : Type*} [Finite κ] (n : ℕ) :
    Finite {d : κ →₀ ℕ | d.degree = n} :=
  (Finsupp.finite_of_degree_eq n).to_subtype

/-- **A multidegree of total degree `n` can be enumerated by `Fin n`, independently of what is
being multiplied.** The enumeration is the list underlying `Finsupp.toMultiset d`, in which each
index occurs with its multiplicity; because the tuple `σ` is produced before any family `v` is
given, the same tuple computes the monomial `∏ i, v i ^ d i` for every `v` at once. -/
theorem exists_prod_fin_eq_prod {κ : Type*} (n : ℕ) (d : {d : κ →₀ ℕ | d.degree = n}) :
    ∃ σ : Fin n → κ, ∀ {A : Type w'} [CommMonoid A] (v : κ → A),
      ∏ i : Fin n, v (σ i) = (d : κ →₀ ℕ).prod fun i e => v i ^ e := by
  have hlen : (d : κ →₀ ℕ).toMultiset.toList.length = n := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact d.2
  refine ⟨fun i => (d : κ →₀ ℕ).toMultiset.toList[(i.cast hlen.symm :
    Fin (d : κ →₀ ℕ).toMultiset.toList.length).1], ?_⟩
  intro A _ v
  rw [Fin.prod_congr' (fun i : Fin (d : κ →₀ ℕ).toMultiset.toList.length =>
      v (d : κ →₀ ℕ).toMultiset.toList[i.1]) hlen.symm, ← Fin.prod_ofFn,
    List.ofFn_getElem_eq_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Finsupp.prod_map_toMultiset]

end Finsupp

namespace SymPow

/-- **The monomial formula for the basis of a symmetric power, with the enumeration of the
multidegree chosen before the module.** One tuple of indices `σ` computes the basis vector at `d`
for every ring, module and basis. -/
theorem exists_prod_ι_eq_coe_basisSymmetricPower_uniform {κ : Type*} (n : ℕ)
    (d : {d : κ →₀ ℕ | d.degree = n}) :
    ∃ σ : Fin n → κ, ∀ {R : Type w'} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M]
      (b : Module.Basis κ R M), ∏ i : Fin n, SymmetricAlgebra.ι R M (b (σ i)) =
        ((basisSymmetricPower b n d : symmetricPower n R M) : SymmetricAlgebra R M) := by
  obtain ⟨σ, hσ⟩ := Finsupp.exists_prod_fin_eq_prod n d
  refine ⟨σ, ?_⟩
  intro R _ M _ _ b
  rw [hσ fun k => SymmetricAlgebra.ι R M (b k), coe_basisSymmetricPower_apply]
  rfl

end SymPow

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{u}}
  (hO : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat RingCat))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The coordinates of the `i`-th vector of `Stacks.SheafOfModules.freeCoordBasis` are the
Kronecker delta at `i`. -/
theorem freeCoord_freeCoordBasis {ι : Type u} [DecidableEq ι] [Finite ι] (V : Cᵒᵖ) (i : ι) :
    freeCoord (S := ringSheafOfIsSheaf hO) V (freeCoordBasis hO V i) = Pi.single i 1 := by
  rw [freeCoordBasis, Module.Basis.map_apply, ← freeCoordLinearEquiv_apply hO V,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply]

/-- **The basis of the sections of a finite free sheaf of modules is natural.** The restriction
map carries the `i`-th basis vector over `V` to the `i`-th basis vector over `W`. -/
theorem freeCoordBasis_map {ι : Type u} [DecidableEq ι] [Finite ι] {V W : Cᵒᵖ} (m : V ⟶ W)
    (i : ι) :
    (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.map m
        (freeCoordBasis hO V i) = freeCoordBasis hO W i := by
  refine (freeCoord_bijective (S := ringSheafOfIsSheaf hO) W).1 ?_
  rw [freeCoord_freeCoordBasis hO W i]
  funext j
  rw [freeCoord_map, freeCoord_freeCoordBasis hO V i]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- **The monomial basis of the sectionwise symmetric power of a finite free sheaf of modules is
natural.** The restriction map carries the monomial basis vector at a multidegree `d` over `V` to
the one over `W`. -/
theorem basisSymPowSections_map {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ) {V W : Cᵒᵖ}
    (m : V ⟶ W) (d : {d : ι →₀ ℕ | d.degree = n}) :
    (PresheafOfModules.symPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).map m
      (basisSymPowSections hO n V d) = basisSymPowSections hO n W d := by
  obtain ⟨σ, hσ⟩ := SymPow.exists_prod_ι_eq_coe_basisSymmetricPower_uniform n d
  have hb : ∀ X : Cᵒᵖ, (↑(PresheafOfModules.symPowSections n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val X
          (basisSymPowSections hO n X d)) :
      SymmetricAlgebra (ToType ((ringSheafOfIsSheaf hO).obj.obj X))
        (ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj X))) =
      ∏ i : Fin n, SymmetricAlgebra.ι _ _ (freeCoordBasis hO X (σ i)) := by
    intro X
    rw [basisSymPowSections, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, ← hσ]
  refine (PresheafOfModules.symPowSections n _ W).injective (Subtype.ext ?_)
  rw [PresheafOfModules.symPowSections_map_prod_ι n _ m (fun i => freeCoordBasis hO V (σ i)) _
    (hb V), hb W]
  exact Finset.prod_congr rfl fun i _ => by rw [freeCoordBasis_map]

/-- **The basis of the sectionwise exterior power of a finite free sheaf of modules is natural.**
The exterior analogue of `Stacks.SheafOfModules.basisSymPowSections_map`. -/
theorem basisExtPowSections_map {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ) {V W : Cᵒᵖ}
    (m : V ⟶ W) (s : Set.powersetCard ι n) :
    (PresheafOfModules.extPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).map m
      (basisExtPowSections hO n V s) = basisExtPowSections hO n W s := by
  have hb : ∀ X : Cᵒᵖ, (↑(PresheafOfModules.extPowSections n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val X
          (basisExtPowSections hO n X s)) :
      ExteriorAlgebra (ToType ((ringSheafOfIsSheaf hO).obj.obj X))
        (ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val.obj X))) =
      ExteriorAlgebra.ιMulti _ n
        fun i => freeCoordBasis hO X (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
    intro X
    rw [basisExtPowSections, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe]
    rfl
  refine (PresheafOfModules.extPowSections n _ W).injective (Subtype.ext ?_)
  rw [PresheafOfModules.extPowSections_map, hb V, ExteriorAlgebra.mapₛₗ_ιMulti, hb W]
  exact congrArg (fun g : Fin n → ToType ((_root_.SheafOfModules.free
      (R := ringSheafOfIsSheaf hO) ι).val.obj W) => ExteriorAlgebra.ιMulti _ n g)
    (funext fun i => by rw [PresheafOfModules.restrictₛₗ_apply, freeCoordBasis_map])

/-! ### The presheaf-level isomorphisms -/

/-- The sections of the sectionwise symmetric power of a finite free sheaf of modules over an
object, identified with the sections of the free sheaf of modules on the degree-`n` multidegrees,
by matching the two bases. -/
noncomputable def symPowFreeEquiv {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    ToType ((PresheafOfModules.symPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V) ≃ₗ[
      ToType ((ringSheafOfIsSheaf hO).obj.obj V)]
      ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO)
        {d : ι →₀ ℕ | d.degree = n}).val.obj V) :=
  (basisSymPowSections hO n V).equiv (freeCoordBasis hO V) (Equiv.refl _)

/-- **The presheaf of sectionwise symmetric powers of a finite free sheaf of modules is the free
presheaf of modules on the degree-`n` multidegrees.** This is
`Stacks.SheafOfModules.symPowFreeEquiv` promoted to an isomorphism of presheaves of modules. -/
noncomputable def symPowFreeIso {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ) :
    PresheafOfModules.symPow n (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val ≅
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO)
        {d : ι →₀ ℕ | d.degree = n}).val :=
  PresheafOfModules.isoMk (fun V => (symPowFreeEquiv hO n V).toModuleIso) fun {V W} m =>
    ModuleCat.hom_ext ((basisSymPowSections hO n V).ext fun d => by
      change symPowFreeEquiv hO n W ((PresheafOfModules.symPow n
          (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).map m
            (basisSymPowSections hO n V d)) =
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO)
          {d : ι →₀ ℕ | d.degree = n}).val.map m
            (symPowFreeEquiv hO n V (basisSymPowSections hO n V d))
      rw [basisSymPowSections_map, symPowFreeEquiv, symPowFreeEquiv, Module.Basis.equiv_apply,
        Module.Basis.equiv_apply, freeCoordBasis_map])

/-- The sections of the sectionwise exterior power of a finite free sheaf of modules over an
object, identified with the sections of the free sheaf of modules on the `n`-element subsets of
the index type, by matching the two bases. -/
noncomputable def extPowFreeEquiv {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ) (V : Cᵒᵖ) :
    ToType ((PresheafOfModules.extPow n
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).obj V) ≃ₗ[
      ToType ((ringSheafOfIsSheaf hO).obj.obj V)]
      ToType ((_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO)
        (Set.powersetCard ι n)).val.obj V) :=
  (basisExtPowSections hO n V).equiv (freeCoordBasis hO V) (Equiv.refl _)

/-- **The presheaf of sectionwise exterior powers of a finite free sheaf of modules is the free
presheaf of modules on the `n`-element subsets of the index type.** The exterior counterpart of
`Stacks.SheafOfModules.symPowFreeIso`. -/
noncomputable def extPowFreeIso {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ) :
    PresheafOfModules.extPow n (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val ≅
      (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) (Set.powersetCard ι n)).val :=
  PresheafOfModules.isoMk (fun V => (extPowFreeEquiv hO n V).toModuleIso) fun {V W} m =>
    ModuleCat.hom_ext ((basisExtPowSections hO n V).ext fun s => by
      change extPowFreeEquiv hO n W ((PresheafOfModules.extPow n
          (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO) ι).val).map m
            (basisExtPowSections hO n V s)) =
        (_root_.SheafOfModules.free (R := ringSheafOfIsSheaf hO)
          (Set.powersetCard ι n)).val.map m
            (extPowFreeEquiv hO n V (basisExtPowSections hO n V s))
      rw [basisExtPowSections_map, extPowFreeEquiv, extPowFreeEquiv, Module.Basis.equiv_apply,
        Module.Basis.equiv_apply, freeCoordBasis_map])

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

/-! ### The sheaf-level statement -/

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **The degree-`n` symmetric power of a finite free sheaf of modules is free on the degree-`n`
multidegrees.** -/
noncomputable def symmetricPowerFreeIso {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι)) :
    A.symmetricPower n ≅ _root_.SheafOfModules.free
      (R := CategoryTheory.Sheaf.toRingCat J Osharp) {d : ι →₀ ℕ | d.degree = n} :=
  (_root_.SheafOfModules.symmetricPowerSheafifyIso J A n).trans
    (((PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).mapIso
        (symPowFreeIso (CategoryTheory.Sheaf.toRingCat J Osharp).property n)).trans
      (_root_.SheafOfModules.sheafifyValIso J _))

/-- **The degree-`n` exterior power of a finite free sheaf of modules is free on the `n`-element
subsets of the index type.** -/
noncomputable def exteriorPowerFreeIso {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι)) :
    A.exteriorPower n ≅ _root_.SheafOfModules.free
      (R := CategoryTheory.Sheaf.toRingCat J Osharp) (Set.powersetCard ι n) :=
  (_root_.SheafOfModules.exteriorPowerSheafifyIso J A n).trans
    (((PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).mapIso
        (extPowFreeIso (CategoryTheory.Sheaf.toRingCat J Osharp).property n)).trans
      (_root_.SheafOfModules.sheafifyValIso J _))

variable {F : _root_.SheafOfModules.{u} (CategoryTheory.Sheaf.toRingCat J Osharp)}

/-- `Stacks.SheafOfModules.symmetricPowerFreeIso` for a sheaf of modules merely *isomorphic* to a
finite free one. -/
noncomputable def symmetricPowerFreeIsoOfIso {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    (e : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι) :
    A.symmetricPower n ≅ _root_.SheafOfModules.free
      (R := CategoryTheory.Sheaf.toRingCat J Osharp) {d : ι →₀ ℕ | d.degree = n} :=
  symmetricPowerFreeIso J n (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J e A)

/-- `Stacks.SheafOfModules.exteriorPowerFreeIso` for a sheaf of modules merely *isomorphic* to a
finite free one. -/
noncomputable def exteriorPowerFreeIsoOfIso {ι : Type u} [LinearOrder ι] [Finite ι] (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    (e : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι) :
    A.exteriorPower n ≅ _root_.SheafOfModules.free
      (R := CategoryTheory.Sheaf.toRingCat J Osharp) (Set.powersetCard ι n) :=
  exteriorPowerFreeIso J n (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso J e A)

/-- **Every symmetric power of a sheaf of modules isomorphic to a finite free one is free of
finite rank.** -/
theorem exists_finite_nonempty_iso_free_symmetricPower (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (ι : Type u) [Finite ι]
    (e : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι) :
    ∃ K : Type u, Finite K ∧ Nonempty (A.symmetricPower n ≅
      _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) K) := by
  classical
  exact ⟨{d : ι →₀ ℕ | d.degree = n}, inferInstance,
    ⟨symmetricPowerFreeIsoOfIso J n A e⟩⟩

/-- **Every exterior power of a sheaf of modules isomorphic to a finite free one is free of
finite rank.** -/
theorem exists_finite_nonempty_iso_free_exteriorPower (n : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (ι : Type u) [Finite ι]
    (e : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) ι) :
    ∃ K : Type u, Finite K ∧ Nonempty (A.exteriorPower n ≅
      _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) K) := by
  let _ : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨Set.powersetCard ι n, inferInstance, ⟨exteriorPowerFreeIsoOfIso J n A e⟩⟩

end Stacks.SheafOfModules

end
