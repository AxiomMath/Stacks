module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeEdgeVanishing
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.Divisors.ClosedSubschemeDimensionDrop
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineHigherDirectImageSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.MorphismReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparatedSupportVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.DirectImageGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `cd(X) ≤ 2 dim X` for a separated scheme of finite type over a separably closed field

Let `k` be a separably closed field and `X` a separated scheme of finite type over `k` with
`dim X ≤ n`. Then `H^q(X, 𝓕) = 0` for `q > 2n` and every torsion abelian sheaf `𝓕` on `X_ét`
(SGA 4, Exposé X, Corollaire 4.3). For affine `X` the sharper bound `cd(X) ≤ dim X` is
[Stacks, Tag 0F0V] together with `cd(k) = 0`.

## The proof

Induction on `n`. If `X` is affine, Tag 0F0V applies. Otherwise let `U ⊆ X` be a dense affine
open (`AlgebraicGeometry.exists_finite_dense_affine_open_cover`) and `Z = X ∖ U` with its
reduced structure; `Z` is nowhere dense, so `dim Z ≤ n - 1`, and `j : U ⟶ X` is affine because
`X` is separated. The sequences `0 → j_!j^{-1}𝓕 → 𝓕 → i_*i^{-1}𝓕 → 0` (Tag 095L), for `𝓕` and for
`j_*j^{-1}𝓕`, and the induction hypothesis on `Z` reduce to `H^q(X, j_*𝓖) = 0` for `q > 2n`,
where `𝓖 = j^{-1}𝓕`. By the bottom edge of the Leray spectral sequence of `j`
(`AlgebraicGeometry.subsingleton_sheafH_etaleAbelianDirectImage_obj_of_subsingleton`) this follows
from

* `H^q(U, 𝓖) = 0` for `q > n`: Tag 0F0V on the affine `U`, with `cd(k) = 0`;
* `H^s(X, R^pj_*𝓖) = 0` for `p ≥ 1` and `s > 2(n - p)`: by Tag 0F0X the support of `R^pj_*𝓖`
  lies in the set `E_{n-p}` of points of transcendence degree at most `n - p` (and `R^pj_*𝓖 = 0`
  for `p > n`), and the induction hypothesis in dimension `n - p`, in its support form
  `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_separatedBound`, applies.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_etaleAbelianDirectImage_obj_of_subsingleton`: the
  Leray edge vanishing for a direct image on small étale sites.
* `AlgebraicGeometry.isEtaleCohomologyBound_of_isAffine_of_isSepClosed`: `cd(X) ≤ dim X` for
  affine `X` of finite type over a separably closed field.
* `AlgebraicGeometry.isEtaleCohomologyBound_two_mul_of_isSepClosed`: **`cd(X) ≤ 2 dim X`**.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* SGA 4, Exposé X, Corollaire 4.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **The bottom edge of the Leray spectral sequence, as a vanishing criterion.** For a morphism
`j : U ⟶ X` and an abelian sheaf `𝓖` on `U_ét`, `H^n(X, j_*𝓖) = 0` as soon as `H^n(U, 𝓖) = 0`
and `H^s(X, R^pj_*𝓖) = 0` whenever `p ≥ 1` and `p + s + 1 = n`. -/
theorem subsingleton_sheafH_etaleAbelianDirectImage_obj_of_subsingleton {U X : Scheme.{u}}
    (j : U ⟶ X) (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h₀ : Subsingleton (Sheaf.H.{u + 1, u + 1} G n))
    (h : ∀ p s : ℕ, 1 ≤ p → p + s + 1 = n → Subsingleton (Sheaf.H.{u + 1, u + 1}
      (((etaleAbelianDirectImage.{u, u + 1} j).rightDerived p).obj G) s)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} j).obj G) n) := by
  have : (etaleAbelianDirectImage.{u, u + 1} j).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} j)
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
    at h₀ ⊢
  exact Stacks.CompositeDegreeVanishing.isZero_rightDerived_obj_of_isZero_comp_of_isZero
    (etaleAbelianDirectImage.{u, u + 1} j) (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    G n (h₀.of_iso ((Functor.rightDerivedIsoOfNatIso
      (etaleAbelianDirectImageCompΓIso.{u, u + 1} j) n).app G)) fun p s hp hps =>
        (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}
          _ _ _).1 (h p s hp hps)

/-- **`cd(X) ≤ dim X` for an affine scheme of finite type over a separably closed field**
(Stacks 0F0V with `cd(k) = 0`): if `dim X ≤ n` then `H^q(X, 𝓕) = 0` for `q > n` and every
torsion abelian sheaf `𝓕` on `X_ét`. -/
@[sga "4 IX 5.7" "more general", sga "4 X 5.2" "special case", sga "4 XIV 3.2"]
theorem isEtaleCohomologyBound_of_isAffine_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsAffine X] (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) :
    Scheme.IsEtaleCohomologyBound X (n : ℕ∞) := by
  intro F hF q hq
  have h : Scheme.etaleCohomologicalDimension X ≤ n :=
    (Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le k X p n hX).trans
      ((add_le_add le_rfl (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k)).trans
        (by simp))
  exact Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension X F hF q (h.trans_lt hq)

/-- A space whose Krull dimension `d` satisfies `d + 1 ≤ 0` is empty. -/
theorem isEmpty_of_topologicalKrullDim_add_one_le_zero {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T + 1 ≤ 0) : IsEmpty T := by
  rw [← topologicalKrullDim_eq_bot_iff_isEmpty]
  induction hd : topologicalKrullDim T using WithBot.recBotCoe with
  | bot => rfl
  | coe e =>
    rw [hd] at h
    exfalso
    have : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by
      simpa using h
    simpa using WithBot.coe_le_coe.mp this

/-- For an affine `f : X ⟶ Y` over `K` and a torsion sheaf `𝓕` supported on points of
transcendence degree at most `a`, `R^qf_*𝓕` is supported on points of transcendence degree at
most `a - q`. -/
theorem smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset_trdegLESet
    (K : Type u) [Field K] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of K)) (gY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType gX] [LocallyOfFiniteType gY] (f : X ⟶ Y) [IsAffineHom f]
    (hfg : f ≫ gY = gX) (a : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a) (q : ℕ) :
    smallEtaleSupport (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F) ⊆
      Scheme.trdegLESet K gY (a - q) := by
  intro y hy
  have hy' := smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset K gX gY f hfg a F hF
    hsupp q hy
  simp only [Set.mem_setOf_eq] at hy'
  simp only [Scheme.trdegLESet, Set.mem_setOf_eq]
  set t := (let : Algebra K (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ gY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.trdeg K (Y.residueField y)) with ht
  obtain ⟨e, he⟩ := Cardinal.lt_aleph0.1
    ((le_self_add.trans hy').trans_lt Cardinal.natCast_lt_aleph0 : t < Cardinal.aleph0)
  rw [he] at hy' ⊢
  have : e + q ≤ a := by exact_mod_cast hy'
  exact_mod_cast (by omega : e ≤ a - q)

/-- **The Leray step.** Let `p : X ⟶ Spec k` be separated, quasi-compact and locally of finite
type over a separably closed field, `j : U ⟶ X` affine, quasi-separated and locally of finite
type, with `U` affine of dimension at most `m`, and suppose `cd(Z) ≤ 2d` for every such `Z` of
dimension `d < m`; then `H^q(X, j_*𝓖) = 0` for `q > 2m` and every torsion abelian sheaf `𝓖` on
`U_ét`. -/
theorem subsingleton_sheafH_etaleAbelianDirectImage_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] {U X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    [IsSeparated p] [CompactSpace X] (j : U ⟶ X) [IsAffineHom j] [QuasiSeparated j]
    [LocallyOfFiniteType j] [IsAffine U] (m : ℕ)
    (ih : ∀ d < m, ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [IsSeparated g] [CompactSpace Z], topologicalKrullDim Z ≤ d →
        Scheme.IsEtaleCohomologyBound Z ((2 * d : ℕ) : ℕ∞))
    (hU : topologicalKrullDim U ≤ m) (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty U.smallEtaleTopology G) (q : ℕ) (hq : 2 * m < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} j).obj G) q) := by
  have hsuppG : smallEtaleSupport G ⊆ Scheme.trdegLESet k (j ≫ p) m := by
    rw [Scheme.trdegLESet_eq_univ_of_topologicalKrullDim_le k (j ≫ p) hU]
    exact Set.subset_univ _
  refine subsingleton_sheafH_etaleAbelianDirectImage_obj_of_subsingleton j G q
    (isEtaleCohomologyBound_of_isAffine_of_isSepClosed k U (j ≫ p) m hU G hG q
      (by exact_mod_cast (by omega : m < q))) fun p' s hp' hps => ?_
  by_cases hlt : m < p'
  · exact Sheaf.subsingleton_H_of_isZero
      (isZero_rightDerived_etaleAbelianDirectImage_of_lt k (j ≫ p) p j rfl m G hG hsuppG p' hlt) s
  · exact subsingleton_H_of_smallEtaleSupport_subset_of_separatedBound k p (m - p')
      ((2 * (m - p') : ℕ) : ℕ∞) (fun Z g _ _ _ hZ => ih (m - p') (by omega) Z g hZ) _
      (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{u + 1} j p' G hG)
      (smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset_trdegLESet k (j ≫ p) p j rfl
        m G hG hsuppG p') s (by exact_mod_cast (by omega : 2 * (m - p') < s))

/-- **Reduction to the open part.** Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` an open
immersion onto its complement. If `H^q(X, i_*i^{-1}𝓕)`, `H^{q-1}(X, i_*i^{-1}j_*j^{-1}𝓕)` and
`H^q(X, j_*j^{-1}𝓕)` vanish, with `q > 0`, then so does `H^q(X, 𝓕)`. -/
theorem subsingleton_sheafH_of_subsingleton_openClosed {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q)
    (hZ : Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj
      ((etaleAbelianInverseImage.{u, u + 1} i).obj F)) q))
    (hZ' : Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj
      ((etaleAbelianInverseImage.{u, u + 1} i).obj ((etaleAbelianDirectImage.{u, u + 1} j).obj
        ((etaleRestriction.{u, u + 1} j).obj F)))) (q - 1)))
    (hU : Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} j).obj
      ((etaleRestriction.{u, u + 1} j).obj F)) q)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  let G := (etaleRestriction.{u, u + 1} j).obj F
  let F' := (etaleAbelianDirectImage.{u, u + 1} j).obj G
  obtain ⟨_, hS₁⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, u + 1} i j hij F
  obtain ⟨_, hS₂⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, u + 1} i j hij F'
  have eG : (etaleRestriction.{u, u + 1} j).obj F' ≅ G :=
    (etaleRestriction.{u, u + 1} j).mapIso
        (((etaleRestrictionAbelianDirectImageAdj.{u, u + 1} j).rightAdjointUniq
          (etaleDirectImageAdj.{u, u + 1} j)).app G) ≪≫
      asIso ((etaleDirectImageAdj.{u, u + 1} j).counit.app G)
  have : (extensionByZero.{u, u + 1} j).Additive :=
    (extensionByZeroAdj.{u, u + 1} j).left_adjoint_additive
  have hjF : Subsingleton (Sheaf.H.{u + 1, u + 1} ((extensionByZero.{u, u + 1} j).obj G) q) := by
    have h₁ := Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact hS₂ (q - 1) q (by omega)
      hU hZ'
    rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
      at h₁ ⊢
    exact h₁.of_iso (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).mapIso
      ((extensionByZero.{u, u + 1} j).mapIso eG.symm))
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS₁ x (hZ.elim _ _)
  rw [← ha, hjF.elim a 0, Abelian.Ext.zero_comp]

/-- For an integral morphism `i : Z ⟶ X` with `cd(Z) ≤ c`, `H^s(X, i_*i^{-1}𝓐) = 0` for `s > c`
and every torsion abelian sheaf `𝓐` on `X_ét`. -/
theorem subsingleton_sheafH_etaleAbelianDirectImage_inverseImage_of_isEtaleCohomologyBound
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsIntegralHom i] {c : ℕ∞}
    (hZ : Scheme.IsEtaleCohomologyBound Z c) (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology A) (s : ℕ) (hs : c < s) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj
      ((etaleAbelianInverseImage.{u, u + 1} i).obj A)) s) :=
  (Equiv.ofBijective _
    (etaleCohomologyDirectImageMap_bijective.{u, u + 1, u + 1} i _ s)).subsingleton_congr.2
    (hZ _ (torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} i A hA) s hs)

/-- An affine open `U` of `X` whose complement is the image of a map from an empty scheme is all
of `X`, so `X` is affine. -/
theorem isAffine_of_range_eq_compl {Z X : Scheme.{u}} [IsEmpty Z] (i : Z ⟶ X) (U : X.Opens)
    (hU : IsAffineOpen U) (hrange : Set.range i.base = (U : Set X)ᶜ) : IsAffine X := by
  have hUtop : U = ⊤ := eq_top_iff.2 fun y _ => by
    by_contra hy
    obtain ⟨z, -⟩ : y ∈ Set.range i.base := hrange ▸ hy
    exact isEmptyElim z
  subst hUtop
  have : IsAffine (⊤ : X.Opens).toScheme := hU
  exact IsAffine.of_isIso X.topIso.inv

/-- **`cd(X) ≤ 2 dim X`** (SGA 4, Exposé X, Corollaire 4.3). Let `k` be a separably closed field
and `X` a separated, quasi-compact scheme locally of finite type over `k` with `dim X ≤ n`. Then
`H^q(X, 𝓕) = 0` for `q > 2n` and every torsion abelian sheaf `𝓕` on `X_ét`. -/
@[sga "4 IX 5.7" "degree > 2 vanishing"]
theorem isEtaleCohomologyBound_two_mul_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (n : ℕ) : ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
      [CompactSpace X], topologicalKrullDim X ≤ n →
        Scheme.IsEtaleCohomologyBound X ((2 * n : ℕ) : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X p _ _ _ hX F hF q hq
  have hq' : 2 * n < q := by exact_mod_cast hq
  by_cases hA : IsAffine X
  · exact isEtaleCohomologyBound_of_isAffine_of_isSepClosed k X p n hX F hF q
      (by exact_mod_cast (by omega : n < q))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  obtain ⟨Fc, U₀, hAff, hcov, hle, hdense⟩ := exists_finite_dense_affine_open_cover (X := X)
  obtain ⟨x⟩ : Nonempty X := not_isEmpty_iff.1 fun _ => hA isAffine_of_isEmpty
  obtain ⟨U, hUF, -⟩ := hcov x
  let W : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal W
  let i : J.subscheme ⟶ X := J.subschemeι
  have hrange : Set.range i.base = (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hWnd : IsNowhereDense ((U : Set X)ᶜ) := by
    rw [U.isOpen.isClosed_compl.isNowhereDense_iff, interior_compl,
      (hdense.mono (hle U hUF)).closure_eq, Set.compl_univ]
  have hZdim : topologicalKrullDim J.subscheme + 1 ≤ n := by
    rw [Stacks.Divisors.topologicalKrullDim_eq_range_of_isClosedImmersion i, hrange]
    exact (hWnd.topologicalKrullDim_add_one_le U.isOpen.isClosed_compl).trans hX
  rcases n with _ | m
  · have := isEmpty_of_topologicalKrullDim_add_one_le_zero (T := J.subscheme)
      (by exact_mod_cast hZdim)
    exact (hA (isAffine_of_range_eq_compl i U (hAff U hUF) hrange)).elim
  have : CompactSpace J.subscheme := (IsClosedImmersion.isClosedEmbedding i).compactSpace
  have hZm : topologicalKrullDim J.subscheme ≤ m := by
    rw [Stacks.Divisors.topologicalKrullDim_eq_range_of_isClosedImmersion i, hrange]
    exact hWnd.topologicalKrullDim_le_of_le_natCast_succ U.isOpen.isClosed_compl m hX
  have hZ := ih m (by omega) J.subscheme (i ≫ p) hZm
  have hij : Set.range U.ι.base = (Set.range i.base)ᶜ := by
    rw [hrange, compl_compl]
    exact Scheme.Opens.range_ι U
  have : IsAffine U.toScheme := hAff U hUF
  have : IsAffineHom U.ι :=
    MorphismProperty.of_postcomp @IsAffineHom (W' := @IsSeparated) U.ι p ‹_›
      (isAffineHom_of_isAffine _)
  have hG := Scheme.Hom.torsionSheafProperty_etaleRestriction U.ι F hF
  exact subsingleton_sheafH_of_subsingleton_openClosed i U.ι hij F q (by omega)
    (subsingleton_sheafH_etaleAbelianDirectImage_inverseImage_of_isEtaleCohomologyBound i hZ F hF
      q (by exact_mod_cast (by omega : 2 * m < q)))
    (subsingleton_sheafH_etaleAbelianDirectImage_inverseImage_of_isEtaleCohomologyBound i hZ _
      (torsionSheafProperty_smallEtaleDirectImageAb.{u + 1} U.ι _ hG) (q - 1)
      (by exact_mod_cast (by omega : 2 * m < q - 1)))
    (subsingleton_sheafH_etaleAbelianDirectImage_of_isSepClosed k p U.ι (m + 1) ih
      (U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hX) _ hG q hq')

end AlgebraicGeometry

end
