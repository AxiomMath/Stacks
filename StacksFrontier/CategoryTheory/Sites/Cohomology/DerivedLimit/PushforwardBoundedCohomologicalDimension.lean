module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.EventuallyConstantDerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded cohomological dimension of a derived direct image

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi, let `A ⊂ Mod(O)` and
`A' ⊂ Mod(O')` be weak Serre subcategories, and let `N` be an integer such that

* `C, O, A` and `C', O', A'` both satisfy the standing hypothesis of the Olsson--Laszlo
  situation of Stacks 0D6R,
* `Rᵖf_*F` lies in `A'` for every `p ≥ 0` and every `F` of `A`, and
* `Rᵖf_*F = 0` for every `p > N` and every `F` of `A`.

Then for every `K` of `D_A(O)`:

* `Rf_*K` lies in `D_{A'}(O')`, and
* the canonical map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` is an isomorphism for `j ≥ N - n`.

This is Stacks 0D6U, a version of [Laszlo--Olsson, six-I, Lemma 2.1.10] with slightly changed
hypotheses, and the content of this file.

## The argument

By Stacks 0D6S the object `K` is a derived limit of its tower of truncations `τ_{≥ -n}K` from
below, and `Rf_*` carries that presented derived limit to a presented derived limit of the
tower `Rf_*(τ_{≥ -n}K)`, being a triangulated right adjoint (Stacks 0A07, whose adjunction is
the one of Stacks 07A6). Each stage of the pushed-forward tower is bounded below with
cohomology in `A'`, by the vanishing of `Rᵖf_*` above `N` and the hypothesis that `Rᵖf_*`
carries `A` into `A'`. The fibre of a transition map `τ_{≥ -(k+1)}K ⟶ τ_{≥ -k}K` has
cohomology in `A` concentrated in a single degree `-(k+1)`, so its image lies in degrees
`≤ -(k+1) + N`; hence the cohomology towers `(Hʲ(Rf_*(τ_{≥ -n}K)))` are eventually constant,
and Stacks 0D6T for the target situation identifies the cohomology of the derived limit with
their eventual values. Comparing with the stabilising stage gives both conclusions.

## Main results

* `Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_derivedPushforward_obj` (Stacks 0D6U,
  part (a)): `Rf_*` carries `D_A(O)` into `D_{A'}(O')`.
* `Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ` (Stacks 0D6U,
  part (b)): the truncation comparison is an isomorphism on `Hʲ` for `j ≥ N - n`.

Along the way:

* `Stacks.Cohomology.OlssonLaszlo.truncGETower_presentation`: the presented derived limit of
  the truncation tower of an object of `D_A(O)`, with the canonical map to it invertible.
* `Stacks.Cohomology.OlssonLaszlo.exists_presented_derivedLimit_map`: a triangulated right
  adjoint carries a presented derived limit to a presented derived limit.
* `Stacks.Cohomology.OlssonLaszlo.isLE_derivedPushforward_singleFunctor_obj`: `Rf_*` has
  cohomological dimension `N` over `A`.
* The generic bounded-below mapping criterion shows that `Rf_*` carries
  `D⁺_A(O)` into `D⁺_{A'}(O')`.

## Implementation notes

The morphism of ringed topoi is an `AlgebraicGeometry.RingedToposSiteHom` together with the
assertion that its underlying functor is a morphism of sites. That assertion is not an extra
hypothesis: it is what makes the pair a morphism of ringed topoi in the source's sense, and it
is what supplies the adjunction `Lf^* ⊣ Rf_*` on which Stacks 0A07 rests; the same convention
is used for Stacks 0A07 itself. The three universes of both ringed topoi are collapsed to one,
as they are for that adjunction.

The standing hypotheses of the two Olsson--Laszlo situations are taken as loose data — a class
of objects, a cofinal system of coverings of each of them and an integer bound — rather than as
two `Stacks.Cohomology.OlssonLaszloSituation` arguments, because the situation bundles its own
site and sheaf of rings, which here must be those of `X` and of `Y`. The two situations are
assembled from that data internally, so the hypotheses are the fields of Stacks 0D6R verbatim.

`Rᵖf_*F` is read as `Hᵖ(Rf_*(F[0]))`, the `p`-th cohomology of the unbounded derived direct
image of `F` placed in degree zero; this is the higher direct image of Stacks 072W. Writing it
this way rather than as `Functor.rightDerivedPlus` of degreewise direct image keeps every
statement about one and the same functor, the unbounded `Rf_*` of Stacks 07A5, and so needs no
comparison between the bounded below and the unbounded derived functor.

A derived limit is supplied by its defining distinguished triangle together with the
compatibility of the structural map with the projections, rather than by an existence
predicate, so that the comparison maps appearing in the conclusions are the canonical ones.

## References

* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.OlssonLaszlo

universe v u wRing wModule w

attribute [local instance] HasDerivedCategory.standard

/-! ### Truncation from below and weak Serre membership -/

/- `homologyMap_truncGEπ_isIso` stood here: the same statement, with the same proof, as
`DerivedCategory.isIso_homologyMap_truncGEπ_app` in
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean:98`, which this module
imports. The uses below name that one. -/

/-- Truncation from below preserves membership in the derived subcategory attached to a class
of objects closed under isomorphisms and containing the zero objects, in particular to a weak
Serre class. -/
theorem derivedCategoryB_truncGE_mem
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (K : DerivedCategory C) (hK : DerivedCategoryB.derivedCategoryB P K)
    (n : ℤ) :
    DerivedCategoryB.derivedCategoryB P
      ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  intro i
  by_cases hi : n ≤ i
  · have hmap := DerivedCategory.isIso_homologyMap_truncGEπ_app n i hi K
    let _ : IsIso ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncGEπ n).app K)) := hmap
    let e : (DerivedCategory.homologyFunctor C i).obj K ≅
        (DerivedCategory.homologyFunctor C i).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K) :=
      asIso ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncGEπ n).app K))
    exact P.prop_of_iso e (hK i)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) := by
      let _ : ((DerivedCategory.TStructure.t.truncGE n).obj K).IsGE n := inferInstance
      exact DerivedCategory.isZero_of_isGE _ n i (by omega)
    exact P.prop_of_isZero hz

/-- Every stage of the tower of truncations from below of an object of `D_A` is bounded below
and has all its cohomology in `A`. -/
theorem truncGETower_obj_mem_plus
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (K : DerivedCategory C) (hK : DerivedCategoryB.derivedCategoryB P K)
    (n : ℕ) :
    DerivedCategoryB.derivedCategoryBPlus P
      ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K) := by
  refine ⟨?_, derivedCategoryB_truncGE_mem P K hK (-(n : ℤ))⟩
  refine ⟨-(n : ℤ), ?_⟩
  intro i hi
  let _ : ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ)) :=
    inferInstance
  exact DerivedCategory.isZero_of_isGE _ (-(n : ℤ)) i hi

/-- An inverse system indexed by `ℕ` whose transition maps out of every stage past `n₀` are
isomorphisms is eventually constant at `n₀`. -/
theorem isEventuallyConstantTo_of_isIso_succ
    {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    F.IsEventuallyConstantTo (.op n₀) := by
  have hmap (m : ℕ) (hm : n₀ ≤ m) :
      IsIso (F.map (homOfLE hm).op) := by
    induction m, hm using Nat.le_induction with
    | base =>
        rw [show (homOfLE (le_refl n₀)).op = 𝟙 (Opposite.op n₀) from Subsingleton.elim _ _,
          F.map_id]
        infer_instance
    | succ m hm ih =>
        let _ := ih
        let _ := h m hm
        rw [show (homOfLE (Nat.le_succ_of_le hm)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op from Subsingleton.elim _ _,
          F.map_comp]
        infer_instance
  intro m f
  have hi := hmap m.unop (leOfHom f.unop)
  convert hi using 1
  exact congrArg F.map (Subsingleton.elim _ _)

/-! ### The presented derived limit of the truncation tower -/

attribute [local implicit_reducible] Stacks.DerivedLimit.truncGETower

/-- In the Olsson--Laszlo situation, the tower of truncations from below of an object of
`D_A(O)` has a derived limit, presented by its defining distinguished triangle, and the
canonical map from the object to that derived limit is an isomorphism. -/
@[stacks 0D6S "the conclusion with the derived limit, its defining distinguished triangle and \
the canonical map of Remark 0H72 constructed: for `K` in `D_A(O)` (hK) the truncation tower has \
a product and a presented derived limit, and the canonical map to it is an isomorphism"]
theorem truncGETower_presentation
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) :
    ∃ (_hprod : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{wModule} S.O))
      (c : K ⟶ L)
      (p : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩) (n + 1) ≫
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).map
          (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} S.O)) ∧
      (∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) ∧ IsIso c := by
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K
  have hGE (n : ℕ) : (tower.obj ⟨n⟩).IsGE (-(n : ℤ)) := by
    show ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE _
    infer_instance
  let _ : HasLimitsOfShape (Discrete ℕ) (SheafOfModules.{wModule} S.O) :=
    SheafOfModules.hasLimitsOfShape.{wModule} (R := S.O) (Discrete ℕ)
  let _ : HasProductsOfShape ℕ (SheafOfModules.{wModule} S.O) := inferInstance
  obtain ⟨hprod, L, p, δ, hT⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE tower
    (fun n ↦ ⟨-(n : ℤ), hGE n⟩)
  let _ := hprod
  let q : K ⟶ ∏ᶜ fun n : ℕ ↦ tower.obj ⟨n⟩ :=
    Pi.lift (fun n ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
  let diff := Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) (n + 1) ≫
        tower.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk p diff δ
  have hmap (n : ℕ) : tower.map (homOfLE (Nat.le_succ n)).op =
      (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K :=
    Stacks.DerivedLimit.truncGETower_map_homOfLE_succ _ K n
  have hq (n : ℕ) : q ≫ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K :=
    Pi.lift_π _ n
  have hzero : q ≫ T.mor₂ = 0 := by
    show q ≫ diff = 0
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub, hq n,
      ← Category.assoc, hq (n + 1), hmap, zero_comp]
    exact sub_eq_zero_of_eq
      (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) K).symm
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT q hzero
  change q = c ≫ p at hc
  have hIso : IsIso c := isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB
    S K hK L p ⟨δ, hT⟩ c (fun n ↦ by
      rw [← Category.assoc, ← hc]
      exact Pi.lift_π _ n)
  refine ⟨hprod, L, c, p, δ, hT, ?_, hIso⟩
  intro n
  rw [← Category.assoc, ← hc]
  exact Pi.lift_π _ n

/-- Transfer weak Serre membership from the eventual cohomology of an inverse system to a
presented derived limit of that system. -/
theorem derivedCategoryB_of_presented_derivedLimit
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (T : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{wModule} S.O))
    (hT : ∀ n : ℕ, DerivedCategoryB.derivedCategoryBPlus S.A (T.obj ⟨n⟩))
    (L : DerivedCategory (SheafOfModules.{wModule} S.O))
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫
            T.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} S.O)))
    (ℋ : ℤ → SheafOfModules.{wModule} S.O)
    (e : ∀ j : ℤ, Stacks.InverseSystem.EventuallyConstantValue
      (T ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j) (ℋ j))
    (hℋ : ∀ j : ℤ, S.A (ℋ j)) :
    DerivedCategoryB.derivedCategoryB S.A L := by
  rcases hL with ⟨δ, hTriangle⟩
  intro j
  let c := cohomologyToEventuallyConstantValue S T L p j (ℋ j) (e j)
  have hc : IsIso c := isIso_cohomologyToEventuallyConstantValue
    S T hT L p ⟨δ, hTriangle⟩ ℋ e j
  let _ : IsIso c := hc
  exact S.A.prop_of_iso (asIso c).symm (hℋ j)

/-! ### Images of presented derived limits under a triangulated right adjoint -/

/-- A triangulated right adjoint carries a presented derived limit of an inverse system,
together with a compatible family of maps into the system, to a presented derived limit of the
image system with the compatible family of image maps. -/
theorem exists_presented_derivedLimit_map
    {C D : Type*} [Category C] [Category D] {K : C}
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (R : C ⥤ D) [R.IsRightAdjoint] [R.CommShift ℤ] [R.IsTriangulated]
    (tower : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ => tower.obj ⟨n⟩]
    (L : C) (p : L ⟶ ∏ᶜ fun n : ℕ => tower.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => tower.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk p (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => tower.obj ⟨n⟩) (n + 1) ≫
          tower.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang C)
    (c : K ⟶ L)
    (κ : ∀ n : ℕ, K ⟶ tower.obj ⟨n⟩)
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n =
      κ n) :
    ∃ (_hprod : HasProduct fun n : ℕ => R.obj (tower.obj ⟨n⟩))
      (p' : R.obj L ⟶ ∏ᶜ fun n : ℕ => R.obj (tower.obj ⟨n⟩))
      (δ' : (∏ᶜ fun n : ℕ => R.obj (tower.obj ⟨n⟩)) ⟶ R.obj L⟦(1 : ℤ)⟧),
      Triangle.mk p' (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) n -
          Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) (n + 1) ≫
            R.map (tower.map (homOfLE (Nat.le_succ n)).op)) δ' ∈ distTriang D ∧
      ∀ n : ℕ, R.map c ≫ p' ≫
        Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) n = R.map (κ n) := by
  let G : Discrete ℕ ⥤ C := Discrete.functor fun n : ℕ => tower.obj ⟨n⟩
  let _ : PreservesLimitsOfShape (Discrete ℕ) R :=
    (Adjunction.ofIsRightAdjoint R).rightAdjoint_preservesLimits.preservesLimitsOfShape
  let _ : PreservesLimit G R := inferInstance
  let G' : Discrete ℕ ⥤ D := Discrete.functor fun n : ℕ => R.obj (tower.obj ⟨n⟩)
  let η : G ⋙ R ≅ G' := Discrete.natIso fun _ => Iso.refl _
  let cone : Cone (G ⋙ R) := R.mapCone (Fan.mk
    (∏ᶜ fun n : ℕ => tower.obj ⟨n⟩) (Pi.π (fun n : ℕ => tower.obj ⟨n⟩)))
  let d : Cone G' := Fan.mk (R.obj (∏ᶜ fun n : ℕ => tower.obj ⟨n⟩))
    (fun n => R.map (Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n))
  let w : (Cone.postcompose η.hom).obj cone ≅ d :=
    Cone.ext (Iso.refl _) (by intro j; cases j; simp [cone, d, η])
  have hd : IsLimit d := (IsLimit.equivOfNatIsoOfIso η cone d w)
    (isLimitOfPreserves R (productIsProduct (fun n : ℕ => tower.obj ⟨n⟩)))
  let _ : HasProduct (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) :=
    HasLimit.mk ⟨d, hd⟩
  let e : R.obj (∏ᶜ fun n : ℕ => tower.obj ⟨n⟩) ≅
      ∏ᶜ fun n : ℕ => R.obj (tower.obj ⟨n⟩) :=
    hd.conePointUniqueUpToIso (productIsProduct _)
  have eπ (n : ℕ) : e.hom ≫
      Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) n =
        R.map (Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp hd (productIsProduct _) (Discrete.mk n)
  let diff := Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) n -
      Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) (n + 1) ≫
        R.map (tower.map (homOfLE (Nat.le_succ n)).op)
  let T := Triangle.mk p
    (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => tower.obj ⟨n⟩) (n + 1) ≫
        tower.map (homOfLE (Nat.le_succ n)).op) δ
  have hm : R.map T.mor₂ ≫ e.hom = e.hom ≫ diff := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, eπ n, ← Functor.map_comp]
    show R.map (Pi.lift (fun n : ℕ =>
      Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => tower.obj ⟨n⟩) (n + 1) ≫
          tower.map (homOfLE (Nat.le_succ n)).op) ≫
      Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n) = _
    simp only [Pi.lift_π]
    rw [Functor.map_sub]
    simp only [Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.map_comp, Category.assoc,
      limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.comp_sub, eπ, sub_right_inj, diff]
    rw [← eπ (n + 1), Category.assoc]
  let p' := R.map p ≫ e.hom
  let δ' := e.inv ≫ R.map δ ≫ (R.commShiftIso (1 : ℤ)).hom.app L
  let T' := Triangle.mk p' diff δ'
  have hIso : R.mapTriangle.obj T ≅ T' := by
    refine Triangle.isoMk _ _ (Iso.refl _) e e ?_ ?_ ?_
    · simp [T', p', T, Functor.mapTriangle]
    · exact hm
    · simp [T', δ', T, Functor.mapTriangle]
  have hT' : T' ∈ distTriang D :=
    isomorphic_distinguished _ (R.map_distinguished T htriangle) _ hIso.symm
  have hcompat (n : ℕ) : R.map c ≫ p' ≫
      Pi.π (fun n : ℕ => R.obj (tower.obj ⟨n⟩)) n = R.map (κ n) := by
    dsimp [p']
    calc
      _ = R.map c ≫ R.map p ≫ R.map
          (Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n) := by
            rw [Category.assoc, eπ n]
      _ = R.map (c ≫ p ≫ Pi.π (fun n : ℕ => tower.obj ⟨n⟩) n) := by
            rw [← Functor.map_comp, ← Functor.map_comp]
      _ = R.map (κ n) := by rw [hc n]
  exact ⟨inferInstance, p', δ', hT', hcompat⟩

/-! ### The Olsson--Laszlo situations attached to a morphism of ringed topoi -/

section Topoi

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [hA : A.IsWeakSerreClass] [hA' : A'.IsWeakSerreClass]
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝒰.X i) p F))
  (N : ℤ)
  (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), A F →
    A' ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
  (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
    ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
        ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))

/-- The Olsson--Laszlo situation on the source of a morphism of ringed topoi. -/
private noncomputable def sourceSituation :
    Stacks.Cohomology.OlssonLaszloSituation.{w, w, w, w} where
  C := X.C
  J := X.J
  O := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  A := A
  B := B
  basis_cover := basisCover
  degreeBound := degreeBound
  coverings := coverings
  vanishing := vanishing

/-- The Olsson--Laszlo situation on the target of a morphism of ringed topoi. -/
private noncomputable def targetSituation :
    Stacks.Cohomology.OlssonLaszloSituation.{w, w, w, w} where
  C := Y.C
  J := Y.J
  O := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  A := A'
  B := B'
  basis_cover := basisCover'
  degreeBound := degreeBound'
  coverings := coverings'
  vanishing := vanishing'


attribute [local implicit_reducible] sourceSituation targetSituation

open Stacks.InverseSystem

/-- The canonical map from a truncation from above is an isomorphism on cohomology in the
degrees that truncation retains. -/
private theorem homologyMap_truncLTι_isIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (b i : ℤ) (hi : i < b) (K : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLTι b).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj K
  have hT : T ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLTGE_distinguished b K
  have hzero : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃) := by
    let : T.obj₃.IsGE b := inferInstance
    exact DerivedCategory.isZero_of_isGE _ b i (by omega)
  have hzeroPrev : IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj T.obj₃) := by
    let : T.obj₃.IsGE b := inferInstance
    exact DerivedCategory.isZero_of_isGE _ b (i - 1) (by omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
      (hzero.eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      (hzeroPrev.eq_of_src _ _)
  show IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁)
  exact isIso_of_mono_of_epi _

/-- An exact functor of derived categories that carries an object placed in degree zero into
degrees `≤ d` carries it, placed in degree `n`, into degrees `≤ n + d`. -/
theorem isLE_map_singleFunctor_obj_of_isLE_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : DerivedCategory C ⥤ DerivedCategory D) [R.CommShift ℤ] (M : C) (d : ℤ)
    (hM : (R.obj ((DerivedCategory.singleFunctor C 0).obj M)).IsLE d) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor C n).obj M)).IsLE (n + d) := by
  have := hM
  have hs : ((R.obj ((DerivedCategory.singleFunctor C 0).obj M))⟦-n⟧).IsLE (n + d) :=
    DerivedCategory.TStructure.t.isLE_shift
      (R.obj ((DerivedCategory.singleFunctor C 0).obj M)) d (-n) (n + d) (by omega)
  have hs' : DerivedCategory.TStructure.t.IsLE
      ((R ⋙ shiftFunctor (DerivedCategory D) (-n)).obj
        ((DerivedCategory.singleFunctor C 0).obj M)) (n + d) := hs
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((R.commShiftIso (-n)).app ((DerivedCategory.singleFunctor C 0).obj M)).symm ≪≫
      R.mapIso (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by omega)).app M))
    (n + d)

/-- **An exact functor of cohomological dimension `N` over a class `P` carries a bounded
object with cohomology in `P` into bounded degrees.** If `R` sends every object of `P` placed
in degree `n` into degrees `≤ n + N`, then it sends an object living in degrees `[a, b]` with
all cohomology in `P` into degrees `≤ b + N`. The class `P` need only be closed under
isomorphisms and contain the zero objects; a weak Serre class is one. -/
theorem isLE_map_obj_of_bounded
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : DerivedCategory C ⥤ DerivedCategory D) [R.CommShift ℤ] [R.IsTriangulated]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (N : ℤ)
    (hsingle : ∀ (M : C) (n : ℤ), P M →
      (R.obj ((DerivedCategory.singleFunctor C n).obj M)).IsLE (n + N))
    (m : ℕ) (E : DerivedCategory C)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj E))
    (a b : ℤ) (ha : E.IsGE a) (hb : E.IsLE b) (hab : b - a = (m : ℤ)) :
    (R.obj E).IsLE (b + N) := by
  induction m using Nat.strong_induction_on generalizing E a b with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        have hab' : a = b := by omega
        subst a
        let : E.IsGE b := ha
        let : E.IsLE b := hb
        obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E b
        let eH : (DerivedCategory.homologyFunctor C b).obj E ≅ M :=
          (DerivedCategory.homologyFunctor C b).mapIso e ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app M
        have hM : P M := P.prop_of_iso eH (hE b)
        have hs := hsingle M b hM
        exact DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e).symm (b + N)
      · let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj E
        let : E.IsGE a := ha
        let : E.IsLE b := hb
        have hT : T ∈ distTriang (DerivedCategory C) :=
          DerivedCategory.TStructure.t.triangleLTGE_distinguished b E
        have hleftGE : T.obj₁.IsGE a := by
          show ((DerivedCategory.TStructure.t.truncLT b).obj E).IsGE a
          infer_instance
        have hleftLE : T.obj₁.IsLE (b - 1) := by
          show ((DerivedCategory.TStructure.t.truncLT b).obj E).IsLE (b - 1)
          infer_instance
        have hleftE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T.obj₁) := by
          intro i
          by_cases hi : i < b
          · have hIso := homologyMap_truncLTι_isIso b i hi E
            let : IsIso ((DerivedCategory.homologyFunctor C i).map
                ((DerivedCategory.TStructure.t.truncLTι b).app E)) := hIso
            exact P.prop_of_iso (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncLTι b).app E)) hIso).symm (hE i)
          · let : T.obj₁.IsLE (b - 1) := hleftLE
            exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ (b - 1) i (by omega))
        have hleft := ih (m - 1) (by omega) T.obj₁ hleftE a (b - 1) hleftGE hleftLE (by omega)
        have hrightGE : T.obj₃.IsGE b := by
          show ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b
          infer_instance
        have hrightLE : T.obj₃.IsLE b := by
          show ((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b
          infer_instance
        let : T.obj₃.IsGE b := hrightGE
        let : T.obj₃.IsLE b := hrightLE
        obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
        have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app b b le_rfl E
        let : IsIso ((DerivedCategory.homologyFunctor C b).map
            ((DerivedCategory.TStructure.t.truncGEπ b).app E)) := hπ
        have hEb : P ((DerivedCategory.homologyFunctor C b).obj T.obj₃) :=
          P.prop_of_iso (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor C b).map
            ((DerivedCategory.TStructure.t.truncGEπ b).app E)) hπ) (hE b)
        let eH : (DerivedCategory.homologyFunctor C b).obj T.obj₃ ≅ M :=
          (DerivedCategory.homologyFunctor C b).mapIso e ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app M
        have hM : P M := P.prop_of_iso eH hEb
        have hs := hsingle M b hM
        have hright : (R.obj T.obj₃).IsLE (b + N) :=
          DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e).symm (b + N)
        let RT := R.mapTriangle.obj T
        have hRT : RT ∈ distTriang (DerivedCategory D) := R.map_distinguished T hT
        have hleftRT : RT.obj₁.IsLE (b - 1 + N) := by
          show (R.obj T.obj₁).IsLE (b - 1 + N)
          exact hleft
        let : RT.obj₁.IsLE (b - 1 + N) := hleftRT
        have hleft' : RT.obj₁.IsLE (b + N) :=
          DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + N) (b + N) (by omega)
        exact DerivedCategory.TStructure.t.isLE₂ RT hRT (b + N) hleft' hright

/-- **The transition maps of the image of the truncation tower are cohomology isomorphisms in
high degrees.** For an exact functor `R` of cohomological dimension `N` over `P` and an object
`K` of `D_P`, the map `R(τ_{≥ -(k+1)}K) ⟶ R(τ_{≥ -k}K)` is an isomorphism on `H^j` for
`j ≥ N - k`. The class `P` need only be closed under isomorphisms and contain the zero objects;
a weak Serre class is one. -/
theorem isIso_homologyMap_map_truncGETower_succ
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : DerivedCategory C ⥤ DerivedCategory D) [R.CommShift ℤ] [R.IsTriangulated]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (N : ℤ)
    (hsingle : ∀ (M : C) (n : ℤ), P M →
      (R.obj ((DerivedCategory.singleFunctor C n).obj M)).IsLE (n + N))
    (K : DerivedCategory C) (hK : DerivedCategoryB.derivedCategoryB P K)
    (k : ℕ) (j : ℤ) (hj : N - (k : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor D j).map
      (R.map ((Stacks.DerivedLimit.truncGETower C K).map (homOfLE (Nat.le_succ k)).op))) := by
  let a : ℤ := -((k + 1 : ℕ) : ℤ)
  let b : ℤ := -(k : ℤ)
  have hab : a + 1 = b := by dsimp only [a, b]; omega
  let E := (DerivedCategory.TStructure.t.truncGE a).obj K
  have hE : DerivedCategoryB.derivedCategoryB P E := derivedCategoryB_truncGE_mem P K hK a
  let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj E
  have hT : T ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLTGE_distinguished b E
  have hleftGE : T.obj₁.IsGE a := by
    show ((DerivedCategory.TStructure.t.truncLT b).obj E).IsGE a
    let : E.IsGE a := inferInstance
    infer_instance
  have hleftLE : T.obj₁.IsLE a := by
    show ((DerivedCategory.TStructure.t.truncLT b).obj E).IsLE a
    rw [← hab]
    infer_instance
  have hleftP : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T.obj₁) := by
    intro i
    by_cases hi : i < b
    · by_cases hia : i = a
      · subst i
        have hι := homologyMap_truncLTι_isIso b a (by omega) E
        let : IsIso ((DerivedCategory.homologyFunctor C a).map
            ((DerivedCategory.TStructure.t.truncLTι b).app E)) := hι
        have eι : (DerivedCategory.homologyFunctor C a).obj E ≅
            (DerivedCategory.homologyFunctor C a).obj T.obj₁ :=
          (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor C a).map
            ((DerivedCategory.TStructure.t.truncLTι b).app E)) hι).symm
        exact P.prop_of_iso eι (hE a)
      · let : T.obj₁.IsGE a := hleftGE
        exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ a i (by omega))
    · let : T.obj₁.IsLE a := hleftLE
      exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ a i (by omega))
  have hleftBound : (R.obj T.obj₁).IsLE (a + N) :=
    isLE_map_obj_of_bounded R P N hsingle 0 T.obj₁ hleftP a a hleftGE hleftLE (by omega)
  let RT := R.mapTriangle.obj T
  have hRT : RT ∈ distTriang (DerivedCategory D) := R.map_distinguished T hT
  have hzero (i : ℤ) (hi : a + N < i) :
      IsZero ((DerivedCategory.homologyFunctor D i).obj (R.obj T.obj₁)) := by
    let : (R.obj T.obj₁).IsLE (a + N) := hleftBound
    exact DerivedCategory.isZero_of_isLE _ (a + N) i hi
  have hja : a + N < j := by dsimp only [a]; omega
  have hmono : Mono ((DerivedCategory.homologyFunctor D j).map RT.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff RT hRT j).2
      ((hzero j hja).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor D j).map RT.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff RT hRT j (j + 1) (by omega)).2
      ((hzero (j + 1) (by omega)).eq_of_tgt _ _)
  let : Mono ((DerivedCategory.homologyFunctor D j).map RT.mor₂) := hmono
  let : Epi ((DerivedCategory.homologyFunctor D j).map RT.mor₂) := hepi
  have hπ' : IsIso ((DerivedCategory.homologyFunctor D j).map RT.mor₂) :=
    isIso_of_mono_of_epi _
  have hπ : IsIso ((DerivedCategory.homologyFunctor D j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
    show IsIso ((DerivedCategory.homologyFunctor D j).map RT.mor₂)
    exact hπ'
  let τ := (DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app K
  let γ := (DerivedCategory.TStructure.t.truncGE b).map
    ((DerivedCategory.TStructure.t.truncGEπ a).app K)
  have hγ : IsIso γ :=
    DerivedCategory.TStructure.t.isIso_truncGE_map_truncGEπ_app b a (by omega) K
  let : IsIso γ := hγ
  have hfac : τ ≫ γ = (DerivedCategory.TStructure.t.truncGEπ b).app E := by
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext (n := a)
    dsimp only [τ, γ]
    calc
      (DerivedCategory.TStructure.t.truncGEπ a).app K ≫
          ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app K ≫
            (DerivedCategory.TStructure.t.truncGE b).map
              ((DerivedCategory.TStructure.t.truncGEπ a).app K)) =
        ((DerivedCategory.TStructure.t.truncGEπ a).app K ≫
          (DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app K) ≫
            (DerivedCategory.TStructure.t.truncGE b).map
              ((DerivedCategory.TStructure.t.truncGEπ a).app K) := by
                simp
      _ = (DerivedCategory.TStructure.t.truncGEπ b).app K ≫
          (DerivedCategory.TStructure.t.truncGE b).map
            ((DerivedCategory.TStructure.t.truncGEπ a).app K) := by
              rw [DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app]
      _ = (DerivedCategory.TStructure.t.truncGEπ a).app K ≫
          (DerivedCategory.TStructure.t.truncGEπ b).app E :=
            DerivedCategory.TStructure.t.truncGEπ_naturality b
              ((DerivedCategory.TStructure.t.truncGEπ a).app K)
  have hτ : τ = (DerivedCategory.TStructure.t.truncGEπ b).app E ≫ inv γ := by
    calc
      τ = τ ≫ γ ≫ inv γ := by simp
      _ = _ := by simpa [Category.assoc] using congrArg (fun g ↦ g ≫ inv γ) hfac
  have htransition : (Stacks.DerivedLimit.truncGETower C K).map
      (homOfLE (Nat.le_succ k)).op = τ := by
    dsimp only [τ, a, b]
    rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  have hγ' : IsIso ((DerivedCategory.homologyFunctor D j).map (R.map (inv γ))) := by
    infer_instance
  have hτIso : IsIso ((DerivedCategory.homologyFunctor D j).map (R.map τ)) := by
    rw [hτ, R.map_comp, CategoryTheory.Functor.map_comp]
    exact IsIso.comp_isIso' hπ hγ'
  rw [htransition]
  exact hτIso

/-! ### The derived direct image in the Olsson--Laszlo situation -/

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- The instances exhibiting the derived direct image as an exact functor commuting with the
shift. -/
private theorem isTriangulated_derivedPushforward :
    (derivedPushforward f).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardTopos
    (derivedPushforward f) (derivedPushforwardUnit f)

omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] hA in
include hmos hvanishImage in
/-- **The derived direct image of a module of `A` placed in degree zero lives in degrees
`≤ N`**, which is the hypothesis that `R^pf_*` vanishes above `N` read in the derived
category. -/
private theorem isLE_derivedPushforward_singleFunctor_zero
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : A M) :
    ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)).IsLE N := by
  have hGE : ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)).IsGE 0 :=
    (by
      let := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
        (pullbackInvertsQuasiIso_isKFlat f hmos))
      let : (derivedPullback f).IsTriangulated :=
        Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
          (pullbackInvertsQuasiIso_isKFlat f hmos)
      exact Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction f
        (derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
          pullbackInvertsQuasiIso_isKFlat f hmos)
        (isLE_derivedPullback_obj_of_isMorphismOfSites f hmos) _ 0 inferInstance)
  have := hGE
  rw [DerivedCategory.isLE_iff]
  intro p hp
  by_cases hp0 : 0 ≤ p
  · obtain ⟨pn, rfl⟩ : ∃ pn : ℕ, (pn : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp0⟩
    exact hvanishImage pn (by exact_mod_cast hp) M hM
  · exact DerivedCategory.isZero_of_isGE _ 0 p (by omega)

omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] hA in
include hmos hvanishImage in
/-- **The derived direct image has cohomological dimension `N` over `A`**: it sends a module of
`A` placed in any degree `n` into cohomological degrees `≤ n + N`. -/
theorem isLE_derivedPushforward_singleFunctor_obj
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : A M) (n : ℤ) :
    ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj M)).IsLE
        (n + N) := by
  have _ := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
        (pullbackInvertsQuasiIso_isKFlat f hmos))
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  exact isLE_map_singleFunctor_obj_of_isLE_zero (derivedPushforward f) M N
    (isLE_derivedPushforward_singleFunctor_zero f hmos A N hvanishImage M hM) n

omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
include hmos hvanishImage hA in
/-- **Stacks 0D6U, the stabilisation of the pushed-forward truncation tower.** The transition
map `Rf_*(τ_{≥ -(k+1)}K) ⟶ Rf_*(τ_{≥ -k}K)` is an isomorphism on `H^j` for `j ≥ N - k`. -/
theorem isIso_homology_derivedPushforward_truncGETower_succ
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) (k : ℕ) (j : ℤ)
    (hj : N - (k : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward f).map
        ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
          (homOfLE (Nat.le_succ k)).op))) := by
  have _ := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
        (pullbackInvertsQuasiIso_isKFlat f hmos))
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated := isTriangulated_derivedPushforward f
  exact isIso_homologyMap_map_truncGETower_succ (derivedPushforward f) A N
    (fun M n hM ↦ isLE_derivedPushforward_singleFunctor_obj f hmos A N hvanishImage M hM n)
    K hK k j hj

/-- On each homology group, the pushed-forward truncation tower is eventually constant from stage
`max 0 (N - i)` on. -/
private theorem isEventuallyConstantTo_homology_derivedPushforward_truncGETower
    {X Y : RingedTopos.{w, w, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposSiteHom X Y)
    (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [A.IsWeakSerreClass] (N : ℤ)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
          ((derivedPushforward f).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) (i : ℤ) :
    ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
        derivedPushforward f) ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i).IsEventuallyConstantTo
      (.op (max 0 (Int.toNat (N - i)))) := by
  apply isEventuallyConstantTo_of_isIso_succ
  intro k hk
  exact isIso_homology_derivedPushforward_truncGETower_succ f hmos A N hvanishImage K hK k i (by
    have h1 : N - i ≤ (Int.toNat (N - i) : ℤ) := Int.self_le_toNat _
    have h2 : ((max 0 (Int.toNat (N - i)) : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    simp only [Nat.cast_max] at h2
    omega)

/-- Every stage of the pushed-forward truncation tower of an object of `D_A` lies in `D⁺_{A'}`. -/
private theorem derivedCategoryBPlus_derivedPushforward_truncGETower
    {X Y : RingedTopos.{w, w, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposSiteHom X Y)
    (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      A F → A' ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
        ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) (k : ℕ) :
    DerivedCategoryB.derivedCategoryBPlus A'
      ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
        derivedPushforward f).obj ⟨k⟩) := by
  have _ := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat f hmos))
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated := isTriangulated_derivedPushforward f
  have hGE (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (n : ℤ) (hK : K.IsGE n) : ((derivedPushforward f).obj K).IsGE n := by
    let : (derivedPullback f).IsTriangulated :=
      Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
        (pullbackInvertsQuasiIso_isKFlat f hmos)
    exact Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction f
      (derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
        pullbackInvertsQuasiIso_isKFlat f hmos)
      (isLE_derivedPullback_obj_of_isMorphismOfSites f hmos) K n hK
  have sourceProperty := truncGETower_obj_mem_plus A K hK k
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1 sourceProperty.1
  refine DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE (derivedPushforward f) A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A') hGE _ a ha fun q ↦ ?_
  have := hGE ((DerivedCategory.singleFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
      ((Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨k⟩))) 0
    inferInstance
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨0, this⟩, fun pp ↦ ?_⟩
  by_cases hp0 : 0 ≤ pp
  · obtain ⟨pn, rfl⟩ : ∃ pn : ℕ, (pn : ℤ) = pp := ⟨pp.toNat, Int.toNat_of_nonneg hp0⟩
    exact himage pn _ (sourceProperty.2 q)
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') _
      (DerivedCategory.isZero_of_isGE _ 0 pp (by omega))

include hA hA' basisCover vanishing basisCover' vanishing' himage hvanishImage hmos in
/-- **Stacks Project, Tag 0D6U, part (a).** Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism
of ringed topoi and let `A`, `A'` be weak Serre subcategories of `Mod(O)`, `Mod(O')` for which
both sites satisfy the Olsson--Laszlo hypothesis, `Rᵖf_*` carries `A` into `A'`, and
`Rᵖf_*F = 0` for `p > N` and `F` in `A`. Then `Rf_*` carries `D_A(O)` into `D_{A'}(O')`. -/
@[stacks 0D6U "part (a)"]
theorem derivedCategoryB_derivedPushforward_obj
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A' ((derivedPushforward f).obj K) := by
  let S := sourceSituation A B basisCover degreeBound coverings vanishing
  let S' := targetSituation A' B' basisCover' degreeBound' coverings' vanishing'
  obtain ⟨hprod, L, c, p, δ, htriangle, hc, hcIso⟩ :=
    truncGETower_presentation S K hK
  let tower := Stacks.DerivedLimit.truncGETower
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K
  have _ := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
        (pullbackInvertsQuasiIso_isKFlat f hmos))
  have hadj : derivedPullback f ⊣ derivedPushforward f :=
    derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
      pullbackInvertsQuasiIso_isKFlat f hmos
  have _ : (derivedPushforward f).IsRightAdjoint := hadj.isRightAdjoint
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated := isTriangulated_derivedPushforward f
  let towerR := tower ⋙ derivedPushforward f
  have hT : ∀ k : ℕ, DerivedCategoryB.derivedCategoryBPlus A' (towerR.obj ⟨k⟩) :=
    derivedCategoryBPlus_derivedPushforward_truncGETower f A A' hmos himage K hK
  let : HasProduct fun k : ℕ ↦ tower.obj ⟨k⟩ := hprod
  obtain ⟨hprod', p', δ', htriangle', hcompat⟩ :=
    exists_presented_derivedLimit_map (derivedPushforward f) tower L p δ htriangle c
      (fun k ↦ (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K) hc
  let : HasProduct fun k : ℕ ↦ towerR.obj ⟨k⟩ := hprod'
  let idx : ℤ → ℕ := fun i ↦ max 0 (Int.toNat (N - i))
  let ℋ : ℤ → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) := fun i ↦
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i).obj
      (towerR.obj ⟨idx i⟩)
  have heventual : ∀ i : ℤ, EventuallyConstantValue
      (towerR ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i) (ℋ i) := fun i ↦
    ⟨idx i, isEventuallyConstantTo_homology_derivedPushforward_truncGETower f A N hmos
      hvanishImage K hK i, Iso.refl _⟩
  have hℋ : ∀ i : ℤ, A' (ℋ i) := fun i ↦ (hT (idx i)).2 i
  have hlimit : DerivedCategoryB.derivedCategoryB A' ((derivedPushforward f).obj L) :=
    derivedCategoryB_of_presented_derivedLimit S' towerR hT _ p' ⟨δ', htriangle'⟩ ℋ heventual hℋ
  let : IsIso c := hcIso
  intro j
  exact A'.prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).mapIso
      ((derivedPushforward f).mapIso (asIso c)).symm) (hlimit j)

include hA hA' basisCover vanishing basisCover' vanishing' himage hvanishImage hmos in
/-- **Stacks Project, Tag 0D6U, part (b).** In the situation of part (a), the canonical map
`Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` induced by the truncation `K ⟶ τ_{≥ -n}K` is an isomorphism
for every `j ≥ N - n`. -/
@[stacks 0D6U "part (b)"]
theorem isIso_homology_derivedPushforward_truncGEπ
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  let S := sourceSituation A B basisCover degreeBound coverings vanishing
  let S' := targetSituation A' B' basisCover' degreeBound' coverings' vanishing'
  obtain ⟨hprod, L, c, p, δ, htriangle, hc, hcIso⟩ :=
    truncGETower_presentation S K hK
  let tower := Stacks.DerivedLimit.truncGETower
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K
  have _ := (pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
        (pullbackInvertsQuasiIso_isKFlat f hmos))
  have hadj : derivedPullback f ⊣ derivedPushforward f :=
    derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
      pullbackInvertsQuasiIso_isKFlat f hmos
  have _ : (derivedPushforward f).IsRightAdjoint := hadj.isRightAdjoint
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated := isTriangulated_derivedPushforward f
  let Rf := derivedPushforward f
  let towerR := tower ⋙ Rf
  have hT : ∀ k : ℕ, DerivedCategoryB.derivedCategoryBPlus A' (towerR.obj ⟨k⟩) :=
    derivedCategoryBPlus_derivedPushforward_truncGETower f A A' hmos himage K hK
  let : HasProduct fun k : ℕ ↦ tower.obj ⟨k⟩ := hprod
  obtain ⟨hprod', p', δ', htriangle', hcompat⟩ :=
    exists_presented_derivedLimit_map Rf tower L p δ htriangle c
      (fun k ↦ (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K) hc
  let : HasProduct fun k : ℕ ↦ towerR.obj ⟨k⟩ := hprod'
  let idx : ℤ → ℕ := fun i ↦ max 0 (Int.toNat (N - i))
  let ℋ : ℤ → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) := fun i ↦
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i).obj
      (towerR.obj ⟨idx i⟩)
  let heventual : ∀ i : ℤ, EventuallyConstantValue
      (towerR ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i) (ℋ i) := fun i ↦
    ⟨idx i, isEventuallyConstantTo_homology_derivedPushforward_truncGETower f A N hmos
      hvanishImage K hK i, Iso.refl _⟩
  have hidxle : idx j ≤ n := by
    have : (Int.toNat (N - j) : ℤ) ≤ (n : ℤ) := by
      have := Int.toNat_le.2 (show N - j ≤ (n : ℤ) by omega)
      exact_mod_cast this
    simp only [idx]
    omega
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j
  let κ : ∀ k : ℕ, K ⟶ tower.obj ⟨k⟩ := fun k ↦
    (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K
  let d := Stacks.Cohomology.cohomologyToEventuallyConstantValue S' towerR (Rf.obj L) p' j
    (ℋ j) (heventual j)
  have hd : IsIso d := Stacks.Cohomology.isIso_cohomologyToEventuallyConstantValue
    S' towerR hT (Rf.obj L) p' ⟨δ', htriangle'⟩ ℋ heventual j
  have hcompatIdx := hcompat (idx j)
  have hidxComp : H.map (Rf.map c) ≫ d =
      H.map (Rf.map (κ (idx j))) ≫ (heventual j).iso.hom := by
    show H.map (Rf.map c) ≫
      (H.map (p' ≫ Pi.π (fun k : ℕ ↦ Rf.obj (tower.obj ⟨k⟩)) (idx j)) ≫
        (heventual j).iso.hom) = _
    rw [← CategoryTheory.Functor.map_comp_assoc]
    exact congrArg (fun g ↦ H.map g ≫ (heventual j).iso.hom) hcompatIdx
  let : IsIso c := hcIso
  have hidxMap : IsIso (H.map (Rf.map (κ (idx j)))) := by
    have hcMap : IsIso (H.map (Rf.map c)) := by infer_instance
    let : IsIso (H.map (Rf.map c)) := hcMap
    let : IsIso d := hd
    have hcomp : IsIso (H.map (Rf.map c) ≫ d) := by infer_instance
    rw [hidxComp] at hcomp
    exact IsIso.of_isIso_comp_right _ (heventual j).iso.hom
  have htransition : IsIso ((towerR ⋙ H).map (homOfLE hidxle).op) :=
    (heventual j).isEventuallyConstant.isIso_map (homOfLE hidxle).op (𝟙 _)
  have hπfactor : κ n ≫ tower.map (homOfLE hidxle).op = κ (idx j) := by
    let π : (Functor.const ℕᵒᵖ).obj K ⟶ tower := NatTrans.ofOpSequence κ (by
      intro k
      show 𝟙 K ≫ κ k = κ (k + 1) ≫ tower.map (homOfLE (Nat.le_succ k)).op
      rw [Category.id_comp]
      dsimp only [κ, tower]
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) K).symm)
    exact (π.naturality (homOfLE hidxle).op).symm.trans (Category.id_comp _)
  have htargetComp : H.map (Rf.map (κ n)) ≫
      H.map (Rf.map (tower.map (homOfLE hidxle).op)) =
        H.map (Rf.map (κ (idx j))) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hπfactor]
  have htarget : IsIso (H.map (Rf.map (κ n))) := by
    have hcomp : IsIso (H.map (Rf.map (κ n)) ≫
        H.map (Rf.map (tower.map (homOfLE hidxle).op))) := by
      rw [htargetComp]
      exact hidxMap
    have htrans : IsIso (H.map (Rf.map (tower.map (homOfLE hidxle).op))) := by
      change IsIso ((towerR ⋙ H).map (homOfLE hidxle).op) at htransition
      exact htransition
    let := hcomp
    let := htrans
    exact IsIso.of_isIso_comp_right
      (H.map (Rf.map (κ n)))
      (H.map (Rf.map (tower.map (homOfLE hidxle).op)))
  exact htarget

end Topoi

end Stacks.Cohomology.OlssonLaszlo

end
