module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulExteriorBasis
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a presheaf of modules with a natural basis, and the stalk of a finite free sheaf

Let `X` be a topological space, `R` a presheaf of commutative rings on it and `M` a presheaf of
`R`-modules. Suppose that for every open set `U` the sections `M(U)` carry a basis indexed by a
fixed finite type `κ`, and that the basis is *natural*: restriction carries the `k`-th basis
vector over `U` to the `k`-th basis vector over `V ≤ U`. Then the stalk `M_x` is free on `κ` over
the stalk `R_x`, with the germs of the basis sections as basis. This file proves that and draws
two consequences.

The first is the stalk of a finite free sheaf of modules: `(O♯^ι)_x ≅ (ι → O_x)`, with the germ
of the `k`-th tautological section going to the `k`-th standard basis vector. The sectionwise
basis is `Stacks.SheafOfModules.freeCoordBasis` and its naturality is
`Stacks.SheafOfModules.freeCoordBasis_map`; what is added here is the passage to the filtered
colimit, which those results do not perform.

The second is the coordinate form of Stacks Tag 01CH in degree `n` for a finite free sheaf of
modules: the stalk of `⋀ⁿ(O♯ʳ)` is `⋀ⁿ_{O_x}((O_x)ʳ)`, and the germ of a scalar times an ordered
exterior product of tautological generators is the corresponding multiple of the wedge of
standard basis vectors, with the scalar replaced by its germ. This is the comparison the Koszul
complex of a sequence of global sections (Stacks Tag 062K) is compared to at a point.

## Main definitions

* `Stacks.SheafOfModules.germAddHom` and `resAddHom`: the germ and restriction maps on sections
  of a presheaf of modules, bundled as additive maps out of `M.obj (op U)`.
* `Stacks.SheafOfModules.toStalkOfBasis` and `stalkEquivOfBasis`: the comparison
  `(κ → R_x) ⟶ M_x` taking the `k`-th standard basis vector to the germ of the `k`-th basis
  section, and that comparison as a linear equivalence.
* `Stacks.SheafOfModules.freeSheafBasis`: the natural family of bases of the sections of a finite
  free sheaf of modules, one over each open set.
* `Stacks.SheafOfModules.freeStalkEquiv`: the stalk of a finite free sheaf of modules as
  `ι → O_x`, and `koszulFreeStalkEquiv` the same with the `ULift` wrapper on the index removed.
* `Stacks.SheafOfModules.exteriorKoszulStalkEquiv`: the stalk of the degree-`n` exterior power of
  `O♯ʳ` as `⋀ⁿ_{O_x}((O_x)ʳ)`.

## Main results

* `Stacks.SheafOfModules.toStalkOfBasis_germ`: **the comparison formula** — the germ of a section
  is the comparison applied to the germs of its coordinates.
* `Stacks.SheafOfModules.stalkEquivOfBasis_single` and
  `stalkEquivOfBasis_symm_germAddHom_smul`: the comparison is pinned down by its values on the
  standard basis, and on germs of scalar multiples of basis sections.
* `Stacks.SheafOfModules.freeSheafBasis_apply`: the `k`-th basis vector of the sections of a
  finite free sheaf of modules is the `k`-th tautological section.
* `Stacks.SheafOfModules.freeStalkEquiv_single` and `koszulFreeStalkEquiv_germ_freeSection`: the
  germ of the `k`-th tautological section is the `k`-th standard basis vector of `ι → O_x`.
* `Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_smul_exteriorBasisSection`: **the
  characterizing germ formula** for the degree-`n` exterior power of a finite free sheaf of
  modules.
* `Stacks.SheafOfModules.isZero_exteriorPiece_of_neg`, with its tensor and symmetric
  counterparts: the three graded algebras of Section 17.21 are zero objects in negative degrees.

## Implementation notes

* The single universe `u` carrying the space, the sections of the structure sheaf and the
  sections of every module is forced by `TopCat.Presheaf.stalk`, exactly as in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk`: a `CommRingCat.{u}`-valued presheaf
  on `X` has stalks only for `X : TopCat.{u}`. Nothing is narrowed. The site universes of the
  final section, which mentions no stalk, are independent.
* The natural-basis hypotheses are taken as explicit arguments — a family of bases and an
  equation — rather than bundled into a structure, so the results apply to any presheaf of
  modules satisfying the description and no structure declared here can collide with one declared
  elsewhere. This is the convention `KoszulStalk` already uses for its presentation data.
* The index type is `Fintype` rather than `Finite` because `toStalkOfBasis` is defined as a finite
  sum of coordinate projections, so the enumeration is data in the definition and not only in a
  proof. `DecidableEq` appears only on the statements that mention `Pi.single`.
* Germ and restriction are bundled as `AddMonoidHom`s (`germAddHom`, `resAddHom`) for the reason
  recorded in `KoszulStalk`: `M.obj (op U)` and `M.presheaf.obj (op U)` are the same group with
  `AddCommMonoid` instances that `rw` will not interchange, so `map_sum` fails on a sum formed at
  the wrong spelling. `germAddHom` is only additive — the scalars act through different rings on
  source and target — so `germAddHom_smul` is used explicitly and never `map_smul`.
* Injectivity is where finiteness of `κ` is really used: finitely many coordinates can be
  realized over a single neighbourhood, obtained as an `iInf` of opens (`Opens.coe_iInf` needs
  the index finite). The coefficients are then killed one at a time by
  `Fintype.linearIndependent_iff`.
* `exteriorKoszulStalkEquiv` is *not* built from a sectionwise identification of `⋀ⁿ(O♯ʳ)(U)`
  with `⋀ⁿ_{O(U)}(O(U)ʳ)`. It is `SheafOfModules.TensorExteriorSymmetricAlgebras.`
  `exteriorPowerStalkEquiv` — Tag 01CH in degree `n`, already an isomorphism — composed with the
  exterior power of `koszulFreeStalkEquiv`. A sectionwise identification would require the
  comparison morphism of Tag 01CG to be invertible *before* sheafification, which is true for a
  finite free sheaf but is not proved anywhere in this development; going through 01CH avoids the
  question entirely.
* The exterior products of tautological generators are
  `Stacks.RegularSequence.exteriorBasisSection`, the left-handed ordered products of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulExteriorBasis`, and the germ formula
  reduces to that file's `exteriorPowerStalkEquiv_germ_exteriorBasisSection`. The subtype form
  `exteriorPower.ιMulti` is used for the wedge; the ungraded form `ExteriorAlgebra.ιMulti` is its
  coercion by `exteriorPower.ιMulti_apply_coe`.
* No `@[stacks]` attribute. The free-sheaf statements are not assertions of any tag — Tag 01CK
  clause (6) is the *locally* free assertion and `FreePowerSheafify` already declines the tag for
  the globally free case — and the exterior germ formula is Tag 01CH in degree `n` specialized to
  a free sheaf, the tag itself being carried by `SheafOfModules.exteriorAlgebra_stalk` in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open SheafOfModules.GradedAlgebra (ringSheafOfIsSheaf)

universe u

namespace Stacks.SheafOfModules

section StalkBasis

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The germ at `x` of a section of a presheaf of modules, as an additive map out of
`M.obj (op U)`. -/
noncomputable def germAddHom {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) :
    ↑(M.obj (op U)) →+ ↑(TopCat.Presheaf.stalk M.presheaf x) where
  toFun s := TopCat.Presheaf.germ M.presheaf U x hx s
  map_zero' := map_zero _
  map_add' a c := map_add _ a c

/-- Restriction of a section of a presheaf of modules, as an additive map. -/
noncomputable def resAddHom {U V : Opens ↥X} (h : V ≤ U) :
    ↑(M.obj (op U)) →+ ↑(M.obj (op V)) where
  toFun s := M.map (homOfLE h).op s
  map_zero' := map_zero _
  map_add' a c := map_add _ a c

/-- `germAddHom M U hx` sends a section to its germ at `x`. -/
theorem germAddHom_apply {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (s : ↑(M.obj (op U))) :
    germAddHom M U hx s = TopCat.Presheaf.germ M.presheaf U x hx s := rfl

/-- `resAddHom M h` sends a section over `U` to its restriction to `V`. -/
theorem resAddHom_apply {U V : Opens ↥X} (h : V ≤ U) (s : ↑(M.obj (op U))) :
    resAddHom M h s = M.map (homOfLE h).op s := rfl

/-- The germ of `a • s` is the germ of `a` acting on the germ of `s`. -/
theorem germAddHom_smul {x : ↥X} (U : Opens ↥X) (hx : x ∈ U)
    (a : ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op U))) (s : ↑(M.obj (op U))) :
    germAddHom M U hx (a • s) = R.germ U x hx a • germAddHom M U hx s :=
  PresheafOfModules.germ_smul M x U hx a s

/-- The restriction of `a • s` is the restriction of `a` acting on the restriction of `s`. -/
theorem resAddHom_smul {U V : Opens ↥X} (h : V ≤ U)
    (a : ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op U))) (s : ↑(M.obj (op U))) :
    resAddHom M h (a • s) = (R ⋙ forget₂ CommRingCat RingCat).map (homOfLE h).op a •
      resAddHom M h s :=
  PresheafOfModules.map_smul M (homOfLE h).op a s

/-- The germ at `x` of the restriction of a section to `V` is the germ of the section itself. -/
theorem germAddHom_resAddHom {x : ↥X} {U V : Opens ↥X} (h : V ≤ U) (hx : x ∈ V)
    (s : ↑(M.obj (op U))) :
    germAddHom M V hx (resAddHom M h s) = germAddHom M U (h hx) s :=
  TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) x hx s

variable {κ : Type u} [Fintype κ]
  (β : ∀ U : Opens ↥X, Module.Basis κ ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op U))
    ↑(M.obj (op U)))

/-- The comparison from coordinate families over the stalk ring to the stalk of `M`: the
`O_x`-linear map sending the `k`-th standard basis vector to the germ of the `k`-th basis
section. -/
noncomputable def toStalkOfBasis (x : ↥X) :
    (κ → ↑(TopCat.Presheaf.stalk R x)) →ₗ[↑(TopCat.Presheaf.stalk R x)]
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  ∑ k : κ, (LinearMap.toSpanSingleton ↑(TopCat.Presheaf.stalk R x) _
    (germAddHom M (⊤ : Opens ↥X) (Set.mem_univ x) (β ⊤ k))).comp (LinearMap.proj k)

/-- `toStalkOfBasis M β x v` is the sum over `k` of `v k` times the germ of the `k`-th basis
section. -/
theorem toStalkOfBasis_apply (x : ↥X) (v : κ → ↑(TopCat.Presheaf.stalk R x)) :
    toStalkOfBasis M β x v =
      ∑ k : κ, v k • germAddHom M (⊤ : Opens ↥X) (Set.mem_univ x) (β ⊤ k) := by
  rw [toStalkOfBasis, LinearMap.sum_apply]
  rfl

variable (hβ : ∀ {U V : Opens ↥X} (h : V ≤ U) (k : κ), resAddHom M h (β U k) = β V k)

include hβ

omit [Fintype κ] in
/-- The germ of a basis section does not depend on the open set it is read over. -/
theorem germAddHom_basis {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (k : κ) :
    germAddHom M U hx (β U k) = germAddHom M (⊤ : Opens ↥X) (Set.mem_univ x) (β ⊤ k) := by
  rw [← hβ (le_top : U ≤ ⊤) k, germAddHom_resAddHom]

/-- **The comparison formula.** The germ of a section is the comparison applied to the germs of
its coordinates. -/
theorem toStalkOfBasis_germ {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (s : ↑(M.obj (op U))) :
    toStalkOfBasis M β x (fun k => R.germ U x hx ((β U).repr s k)) = germAddHom M U hx s := by
  rw [toStalkOfBasis_apply]
  conv_rhs => rw [← (β U).sum_repr s]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [germAddHom_smul, germAddHom_basis M β hβ U hx k]

/-- The comparison `toStalkOfBasis M β x` is surjective. -/
theorem toStalkOfBasis_surjective (x : ↥X) : Function.Surjective (toStalkOfBasis M β x) := by
  intro m
  obtain ⟨U, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  exact ⟨_, (toStalkOfBasis_germ M β hβ U hx s).trans hs⟩

/-- The comparison `toStalkOfBasis M β x` is injective. -/
theorem toStalkOfBasis_injective (x : ↥X) : Function.Injective (toStalkOfBasis M β x) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  classical
  choose W hW a ha using fun k : κ => TopCat.Presheaf.exists_germ_eq R (v k)
  have hmem : x ∈ (⨅ k, W k : Opens ↥X) := by
    simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact hW
  set V : Opens ↥X := ⨅ k, W k with hV
  set c : κ → ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op V)) :=
    fun k => R.map (homOfLE (iInf_le _ k)).op (a k) with hc
  have hcg : ∀ k : κ, R.germ V x hmem (c k) = v k := by
    intro k
    rw [hc]
    exact (R.germ_res_apply (homOfLE (iInf_le W k)) x hmem (a k)).trans (ha k)
  have h1 : germAddHom M V hmem (∑ k : κ, c k • β V k) =
      ∑ k : κ, v k • germAddHom M (⊤ : Opens ↥X) (Set.mem_univ x) (β ⊤ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [germAddHom_smul, hcg k, germAddHom_basis M β hβ V hmem k]
  have hs : germAddHom M V hmem (∑ k : κ, c k • β V k) = 0 := by
    rw [h1, ← toStalkOfBasis_apply]; exact hv
  obtain ⟨W', hxW', iW'V, _, hW'⟩ :=
    TopCat.Presheaf.germ_eq M.presheaf x hmem hmem (∑ k : κ, c k • β V k) 0
      (by rw [map_zero]; exact hs)
  have hle : W' ≤ V := leOfHom iW'V
  have hres : resAddHom M hle (∑ k : κ, c k • β V k) = 0 := by
    rw [resAddHom_apply, show (homOfLE hle : W' ⟶ V) = iW'V from Subsingleton.elim _ _,
      show (M.map iW'V.op) (∑ k : κ, c k • β V k) =
        (M.presheaf.map iW'V.op) (∑ k : κ, c k • β V k) from rfl, hW']
    exact map_zero _
  have hzero : ∑ k : κ, (R ⋙ forget₂ CommRingCat RingCat).map (homOfLE hle).op (c k) •
      β W' k = 0 := by
    refine Eq.trans (Eq.symm (Eq.trans (map_sum (resAddHom M hle) _ _)
      (Finset.sum_congr rfl fun k _ => ?_))) hres
    exact (resAddHom_smul M hle (c k) (β V k)).trans
      (congrArg _ (hβ hle k))
  have hcoef := fun k => Fintype.linearIndependent_iff.1 (β W').linearIndependent
    (fun k => (R ⋙ forget₂ CommRingCat RingCat).map (homOfLE hle).op (c k)) hzero k
  funext k
  rw [← hcg k, ← TopCat.Presheaf.germ_res_apply R (homOfLE hle) x hxW' (c k),
    show R.map (homOfLE hle).op (c k) = 0 from hcoef k, map_zero]
  rfl

/-- **The stalk of a presheaf of modules with a natural finite basis is free on the germs of the
basis sections.** -/
@[ega "II 6.5.3" "partial"]
noncomputable def stalkEquivOfBasis (x : ↥X) :
    (κ → ↑(TopCat.Presheaf.stalk R x)) ≃ₗ[↑(TopCat.Presheaf.stalk R x)]
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  LinearEquiv.ofBijective (toStalkOfBasis M β x)
    ⟨toStalkOfBasis_injective M β hβ x, toStalkOfBasis_surjective M β hβ x⟩

/-- The linear equivalence `stalkEquivOfBasis M β hβ x` agrees with `toStalkOfBasis M β x`. -/
theorem stalkEquivOfBasis_apply (x : ↥X) (v : κ → ↑(TopCat.Presheaf.stalk R x)) :
    stalkEquivOfBasis M β hβ x v = toStalkOfBasis M β x v := rfl

/-- The `k`-th standard basis vector goes to the germ of the `k`-th basis section over any open
set containing `x`. -/
theorem stalkEquivOfBasis_single [DecidableEq κ] {x : ↥X} (U : Opens ↥X) (hx : x ∈ U)
    (k : κ) :
    stalkEquivOfBasis M β hβ x (Pi.single k 1) = germAddHom M U hx (β U k) := by
  rw [stalkEquivOfBasis_apply, toStalkOfBasis_apply, germAddHom_basis M β hβ U hx k,
    Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]),
    Pi.single_eq_same, one_smul]

/-- **The characterizing formula.** The germ of a scalar multiple of a basis section is the
corresponding multiple of the standard basis vector over the stalk. -/
theorem stalkEquivOfBasis_symm_germAddHom_smul [DecidableEq κ] {x : ↥X} (U : Opens ↥X)
    (hx : x ∈ U)
    (a : ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op U))) (k : κ) :
    (stalkEquivOfBasis M β hβ x).symm (germAddHom M U hx (a • β U k)) =
      R.germ U x hx a • Pi.single k 1 := by
  rw [LinearEquiv.symm_apply_eq, germAddHom_smul,
    ← stalkEquivOfBasis_single M β hβ U hx k, ← map_smul (stalkEquivOfBasis M β hβ x)]

end StalkBasis

/-! ### The stalk of a finite free sheaf of modules -/

section FreeStalk

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The `k`-th tautological section of a free sheaf of modules is the section whose coordinate
family is the Kronecker delta at `k`. -/
theorem freeSection_eval_eq_freeMk (V : (Opens ↥X)ᵒᵖ) (k : ι) :
    (_root_.SheafOfModules.freeSection
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) k).eval V =
      freeMk (S := toRingCat (Opens.grothendieckTopology ↥X) Osharp) V (Pi.single k 1) := by
  have hexp : freeMk (S := toRingCat (Opens.grothendieckTopology ↥X) Osharp) V
        (Pi.single k 1) =
      ∑ i : ι, (_root_.SheafOfModules.ιFree
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) i).val.app V
          (toUnit V ((Pi.single k 1 :
            ι → ↑((toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj V)) i)) := rfl
  rw [hexp, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; exact map_zero _), Pi.single_eq_same]
  exact freeSection_eval k V

/-- The natural family of bases of the sections of a finite free sheaf of modules, one over each
open set. -/
noncomputable def freeSheafBasis (U : Opens ↥X) :
    Module.Basis ι ↑((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      ↑((_root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) ι).val.obj (op U)) :=
  freeCoordBasis (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property (op U)

/-- The `k`-th vector of `Stacks.SheafOfModules.freeSheafBasis` is the `k`-th tautological
section. -/
theorem freeSheafBasis_apply (U : Opens ↥X) (k : ι) :
    freeSheafBasis (Osharp := Osharp) U k =
      (_root_.SheafOfModules.freeSection
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) k).eval (op U) := by
  have h1 : freeSheafBasis (Osharp := Osharp) U k =
      freeCoordBasis (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property (op U) k := rfl
  rw [h1]
  refine (freeCoord_bijective
    (S := toRingCat (Opens.grothendieckTopology ↥X) Osharp) (op U)).1 ?_
  rw [freeCoord_freeCoordBasis, freeSection_eval_eq_freeMk, freeCoord_freeMk]

/-- `Stacks.SheafOfModules.freeSheafBasis` is natural: restriction carries the `k`-th basis
vector to the `k`-th basis vector. -/
theorem freeSheafBasis_natural {U V : Opens ↥X} (h : V ≤ U) (k : ι) :
    resAddHom (_root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) ι).val h
        (freeSheafBasis (Osharp := Osharp) U k) =
      freeSheafBasis V k :=
  freeCoordBasis_map (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property
    (homOfLE h).op k

/-- **The stalk of a finite free sheaf of modules is free on the index type over the stalk of
the structure sheaf**, the basis being the germs of the tautological sections. -/
noncomputable def freeStalkEquiv (x : ↥X) :
    (ι → ↑(TopCat.Presheaf.stalk Osharp.obj x)) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (_root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) ι).val.presheaf x) :=
  stalkEquivOfBasis _ freeSheafBasis freeSheafBasis_natural x

/-- **The characterizing formula for the stalk of a finite free sheaf of modules**: the standard
basis vector at `k` corresponds to the germ of the `k`-th tautological section. -/
@[ega "0 5.5.5"]
theorem freeStalkEquiv_single {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (k : ι) :
    freeStalkEquiv (Osharp := Osharp) (ι := ι) x (Pi.single k 1) =
      TopCat.Presheaf.germ (_root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) ι).val.presheaf U x hx
        ((_root_.SheafOfModules.freeSection
          (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) k).eval (op U)) :=
  (stalkEquivOfBasis_single _ freeSheafBasis freeSheafBasis_natural U hx k).trans
    (congrArg (germAddHom _ U hx) (freeSheafBasis_apply (Osharp := Osharp) U k))

/-- The inverse form of `Stacks.SheafOfModules.freeStalkEquiv_single`. -/
theorem freeStalkEquiv_symm_germ_freeSection {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (k : ι) :
    (freeStalkEquiv (Osharp := Osharp) (ι := ι) x).symm
        (TopCat.Presheaf.germ (_root_.SheafOfModules.free
          (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) ι).val.presheaf U x hx
          ((_root_.SheafOfModules.freeSection
            (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp) k).eval (op U))) =
      Pi.single k 1 :=
  (LinearEquiv.symm_apply_eq _).2 (freeStalkEquiv_single U hx k).symm

end FreeStalk


/-! ### The stalk of an exterior power of a finite free sheaf of modules, in coordinates -/

section ExteriorFree

open Stacks.RegularSequence

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}

/-- **The stalk of `O♯ʳ` is `(O_x)ʳ`**, with the germ of the `k`-th tautological section going
to the `k`-th standard basis vector. This is `Stacks.SheafOfModules.freeStalkEquiv` with the
`ULift` wrapper on the index removed. -/
noncomputable def koszulFreeStalkEquiv (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (koszulFreeSheaf Osharp r).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)) :=
  (freeStalkEquiv (Osharp := Osharp) (ι := ULift.{u} (Fin r)) x).symm ≪≫ₗ
    LinearEquiv.funCongrLeft ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk Osharp.obj x) (Equiv.ulift (α := Fin r)).symm

/-- The germ of the `k`-th tautological section of `O♯ʳ` is the `k`-th standard basis vector. -/
theorem koszulFreeStalkEquiv_germ_freeSection {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (k : Fin r) :
    koszulFreeStalkEquiv (Osharp := Osharp) (r := r) x
        (TopCat.Presheaf.germ (koszulFreeSheaf Osharp r).val.presheaf U x hx
          ((_root_.SheafOfModules.freeSection
            (R := toRingCat (Opens.grothendieckTopology ↥X) Osharp)
            (ULift.up k)).eval (op U))) =
      Pi.single k 1 := by
  rw [koszulFreeStalkEquiv, LinearEquiv.trans_apply,
    freeStalkEquiv_symm_germ_freeSection U hx (ULift.up k), LinearEquiv.funCongrLeft_apply]
  funext j
  by_cases h : j = k
  · subst h
    rw [Pi.single_eq_same]
    exact Pi.single_eq_same _ _
  · rw [Pi.single_eq_of_ne h]
    exact Pi.single_eq_of_ne (fun hj => h (ULift.up_injective hj)) _

variable (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
  (Opens.grothendieckTopology ↥X) (koszulFreeSheaf Osharp r))

/-- **The stalk of the degree-`n` exterior power of `O♯ʳ` is `⋀ⁿ_{O_x}((O_x)ʳ)`**: Tag 01CH in
degree `n` for a finite free sheaf of modules, with the stalk of `O♯ʳ` written in coordinates
by `Stacks.SheafOfModules.koszulFreeStalkEquiv`. -/
noncomputable def exteriorKoszulStalkEquiv (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n
        (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)) :=
  (A.exteriorPowerStalkEquiv n x) ≪≫ₗ exteriorPowerCongr n (koszulFreeStalkEquiv x)

/-- The germ of an exterior product of tautological generators is the wedge of the standard
basis vectors with the same indices. -/
theorem exteriorKoszulStalkEquiv_germ_exteriorBasisSection (n : ℕ) {x : ↥X} (U : Opens ↥X)
    (hx : x ∈ U) (i : Fin n → Fin r) :
    exteriorKoszulStalkEquiv A n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
          (exteriorBasisSection A U n i)) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun j => Pi.single (i j) 1 := by
  have hc : ∀ v : Fin n → ↑(TopCat.Presheaf.stalk (koszulFreeSheaf Osharp r).val.presheaf x),
      exteriorPowerCongr n (koszulFreeStalkEquiv (Osharp := Osharp) (r := r) x)
          (exteriorPower.ιMulti
            ↑(TopCat.Presheaf.stalk Osharp.obj x) n v) =
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
          fun j => koszulFreeStalkEquiv x (v j) :=
    fun v => exteriorPower.map_apply_ιMulti _ v
  rw [exteriorKoszulStalkEquiv, LinearEquiv.trans_apply,
    exteriorPowerStalkEquiv_germ_exteriorBasisSection A n x U hx i, hc]
  exact congrArg (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n)
    (funext fun j => koszulFreeStalkEquiv_germ_freeSection U hx (i j))

/-- **The characterizing germ formula for the Koszul comparison.** The germ of a scalar times an
ordered exterior product of tautological generators is the corresponding multiple of the wedge
of standard basis vectors over the stalk, with the scalar replaced by its germ. This includes
the unit in degree zero and the individual generators in degree one. -/
theorem exteriorKoszulStalkEquiv_germ_smul_exteriorBasisSection (n : ℕ) {x : ↥X}
    (U : Opens ↥X) (hx : x ∈ U) (a : ↑(Osharp.obj.obj (op U))) (i : Fin n → Fin r) :
    exteriorKoszulStalkEquiv A n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
          (a • exteriorBasisSection A U n i)) =
      TopCat.Presheaf.germ Osharp.obj U x hx a • exteriorPower.ιMulti
        ↑(TopCat.Presheaf.stalk Osharp.obj x) n fun j => Pi.single (i j) 1 := by
  rw [show TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
        (a • exteriorBasisSection A U n i) =
      germAddHom (A.exteriorPower n).val U hx (a • exteriorBasisSection A U n i) from rfl,
    germAddHom_smul, map_smul,
    show germAddHom (A.exteriorPower n).val U hx (exteriorBasisSection A U n i) =
      TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
        (exteriorBasisSection A U n i) from rfl,
    exteriorKoszulStalkEquiv_germ_exteriorBasisSection A n U hx i]

end ExteriorFree

/-! ### Vanishing of an exterior algebra in negative degrees -/

section NegativeDegrees

universe v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (toRingCat J Osharp)}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- A sheaf of modules all of whose sections vanish is a zero object. -/
theorem isZero_of_forall_section_eq_zero {M : _root_.SheafOfModules.{u} (toRingCat J Osharp)}
    (h : ∀ (U : Cᵒᵖ) (y : M.val.obj U), y = 0) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h U y

/-- **The exterior algebra of a sheaf of modules is a zero object in every negative degree.** -/
theorem isZero_exteriorPiece_of_neg
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) {n : ℤ} (hn : n < 0) :
    IsZero (A.exterior.piece n) :=
  isZero_of_forall_section_eq_zero fun U y => A.exteriorPiece_eq_zero_of_neg n hn U y

/-- The tensor-algebra counterpart of
`Stacks.SheafOfModules.isZero_exteriorPiece_of_neg`. -/
theorem isZero_tensorPiece_of_neg
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) {n : ℤ} (hn : n < 0) :
    IsZero (A.tensor.piece n) :=
  isZero_of_forall_section_eq_zero fun U y => A.tensorPiece_eq_zero_of_neg n hn U y

/-- The symmetric-algebra counterpart of
`Stacks.SheafOfModules.isZero_exteriorPiece_of_neg`. -/
theorem isZero_symmetricPiece_of_neg
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) {n : ℤ} (hn : n < 0) :
    IsZero (A.symmetric.piece n) :=
  isZero_of_forall_section_eq_zero fun U y => A.symmetricPiece_eq_zero_of_neg n hn U y

end NegativeDegrees

end Stacks.SheafOfModules

end
