module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksCore.Tactic.StacksAttribute

/-!
# The Čech sequence of a covering and the extension by zero of the structure sheaf

Let `R` be a sheaf of rings on a site `C`, let `U : C` and let `{U_i → U}_{i ∈ I}` be a
covering family of `U` whose pairwise fibre products `U_i ×_U U_j` exist. **Stacks 0934**
asserts that the sequence

`⊕_{i, j} j_{U_i ×_U U_j!} O_{U_i ×_U U_j} ⟶ ⊕_i j_{U_i!} O_{U_i} ⟶ j_{U!} O_U ⟶ 0`

of sheaves of `R`-modules is exact, the left-hand map being the difference of the two
restrictions. This file proves it, and deduces the **middle exactness half of Stacks 0G1W**:
for a quasi-compact `U` the covering may be cut down to a finite subfamily first.

## Main definitions

* `Stacks.SheafOfModules.cechRelationsMap`: the difference of the two restriction maps
  `⊕_{i, j} j_{U_i ×_U U_j!} O_{U_i ×_U U_j} ⟶ ⊕_i j_{U_i!} O_{U_i}`.
* `Stacks.SheafOfModules.cechShortComplex`: the two maps of the displayed sequence, packaged
  as a `ShortComplex`.

## Main results

* `Stacks.SheafOfModules.extensionByZeroUnitMap_comp`: functoriality of `j_{U!} O_U` in `U`
  is compatible with composition.
* `Stacks.SheafOfModules.exists_hom_of_cechRelationsMap_comp_eq_zero`: a morphism out of
  `⊕_i j_{U_i!} O_{U_i}` killing the Čech relations factors through `j_{U!} O_U`. This is the
  sheaf axiom for the target, read through Stacks 0G1V.
* `Stacks.SheafOfModules.isColimitCokernelCoforkCechShortComplex`: `⊕_i j_{U_i!} O_{U_i} ⟶
  j_{U!} O_U` is a cokernel of `cechRelationsMap`.
* `Stacks.SheafOfModules.cechShortComplex_exact` and
  `Stacks.SheafOfModules.epi_cechShortComplex_g`: **Stacks Project, Tag 0934**, the two
  exactness assertions of the displayed sequence.
* `Stacks.SheafOfModules.exists_finite_restrictIndex_cechShortComplex_exact`: **Stacks
  Project, Tag 0G1W**, the middle exactness half.

## Implementation notes

**The argument is Stacks' own, run through the cokernel universal property rather than
through Tag 05AA.** Stacks applies `Hom(-, F)` to the displayed sequence, observes that the
result is the sheaf axiom for `F` by Tag 0G1V, and concludes by Homology Lemma 05AA (a
sequence is exact with surjective right-hand map exactly when `Hom(-, F)` is exact for every
`F`). Both directions of 05AA are available here as
`CategoryTheory.ShortComplex.exact_iff_homRight`, but the *forward* implication is all that
is used, and for that the statement "`⊕_i j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` is a cokernel of
`cechRelationsMap`" is literally the sheaf axiom for every target at once: the universal
property quantifies over the targets exactly as 05AA's criterion does. So the cokernel is
constructed directly, and `ShortComplex.exact_of_g_is_cokernel` turns it into exactness. This
avoids transporting the `preadditiveYoneda` short complexes of abelian groups, which is where
05AA itself needs a transparency option.

**No quasi-compactness and no distinguished collection of objects.** Tag 0934 holds for an
arbitrary covering family of an arbitrary object; the only hypothesis beyond the covering
condition is the existence of the pairwise fibre products, which Stacks assumes implicitly by
writing them down. Quasi-compactness enters only in the last result of the file, where it
supplies a finite subfamily which is still a covering — and that extraction is already
available as `Stacks.SheafOfModules.QuasiCompact.exists_finite_restrictIndex_sieve₀_mem`.

**Why the compatible family is taken in the `Arrows.Compatible` form.** Mathlib's
`CategoryTheory.Presieve.Arrows.PullbackCompatible` is the form that mentions the canonical
fibre products, and is the closer match to the statement of Tag 0934; but it is stated under
an instance `(Presieve.ofArrows X π).HasPairwisePullbacks`, so using it would mean producing
a *presieve-level* pullback instance from the family-level one and then relying on proof
irrelevance to identify the two resulting fibre products. The general
`CategoryTheory.Presieve.Arrows.Compatible` form carries no instance at all, and the step
from the fibre-product form to it is three lines: factor the competing pair through the fibre
product and use `extensionByZeroUnitMap_comp`.

**Index universes.** `CategoryTheory.GrothendieckTopology.IsQuasiCompactObject` quantifies
over covering families indexed by `Type (max u₁ v₁)`, so that is the index universe of the
covering families here, and `𝒰.I₀ × 𝒰.I₀` lies in it; the coproducts therefore exist in
`SheafOfModules.{max u₁ v₁ w t} R`. The module universe `max u₁ v₁ w t` is the one
`Stacks.SheafOfModules.extensionByZeroUnit` is constructed at.

The two `local instance`s below are a fifth copy of a derivation that `ExtensionByZeroUnit.lean`,
`ExtensionByZeroQuasiCompact.lean`, `ExtensionByZeroUnitULift.lean` and
`FiniteExtensionByZeroPresentation.lean` also carry privately; a public declaration of another
module cannot refer to a `private` one. If they are ever made public, all five copies should
cite them.

## References

* [Stacks Project, Tag 0934](https://stacks.math.columbia.edu/tag/0934)
* [Stacks Project, Tag 0G1W](https://stacks.math.columbia.edu/tag/0G1W)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 05AA](https://stacks.math.columbia.edu/tag/05AA)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u₁ v₁ w t

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-! ### Functoriality of the extension by zero in the object -/

section Functoriality

variable (R : Sheaf J RingCat.{w})

/-- The section of `j_{U!} O_U` over `V` corresponding to `j_{V!} O_V ⟶ j_{U!} O_U` under
Stacks 0G1V is the restriction along `f` of the one corresponding to the identity. -/
lemma extensionByZeroUnitHomEquiv_map_self {V U : C} (f : V ⟶ U) :
    extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R V (extensionByZeroUnit.{u₁, v₁, w, t} R U)
        (extensionByZeroUnitMap.{u₁, v₁, w, t} R f) =
      (extensionByZeroUnit.{u₁, v₁, w, t} R U).val.map f.op
        (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U
          (extensionByZeroUnit.{u₁, v₁, w, t} R U) (𝟙 _)) := by
  rw [← extensionByZeroUnitHomEquiv_map, Category.comp_id]

/-- **Functoriality of `j_{U!} O_U` in `U` is compatible with composition.** -/
lemma extensionByZeroUnitMap_comp {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    extensionByZeroUnitMap.{u₁, v₁, w, t} R (g ≫ f) =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R g ≫
        extensionByZeroUnitMap.{u₁, v₁, w, t} R f := by
  refine (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R W
    (extensionByZeroUnit.{u₁, v₁, w, t} R U)).injective ?_
  rw [extensionByZeroUnitHomEquiv_map_self, extensionByZeroUnitHomEquiv_map,
    extensionByZeroUnitHomEquiv_map_self, op_comp, PresheafOfModules.map_comp_apply]

end Functoriality

/-! ### The Čech sequence of a covering family -/

section Cech

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

variable (R : Sheaf J RingCat.{w}) {U : C} (𝒰 : PreZeroHypercover.{max u₁ v₁} U)
  [hpb : ∀ i j, HasPullback (𝒰.f i) (𝒰.f j)]

/-- **The Čech relations of a covering family.** The difference of the two restriction maps
`⊕_{i, j} j_{U_i ×_U U_j!} O_{U_i ×_U U_j} ⟶ ⊕_i j_{U_i!} O_{U_i}`. -/
noncomputable def cechRelationsMap :
    (∐ fun p : 𝒰.I₀ × 𝒰.I₀ =>
        extensionByZeroUnit.{u₁, v₁, w, t} R (pullback (𝒰.f p.1) (𝒰.f p.2))) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i) :=
  Sigma.desc fun p ↦
    extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.fst (𝒰.f p.1) (𝒰.f p.2)) ≫
        Sigma.ι (fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) p.1 -
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.snd (𝒰.f p.1) (𝒰.f p.2)) ≫
        Sigma.ι (fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) p.2

/-- The component of `cechRelationsMap` at the summand indexed by `p = (i, j)` is the difference
of the restrictions along the two projections of `U_i ×_U U_j`. -/
@[reassoc]
lemma ι_comp_cechRelationsMap (p : 𝒰.I₀ × 𝒰.I₀) :
    Sigma.ι (fun q : 𝒰.I₀ × 𝒰.I₀ ↦
          extensionByZeroUnit.{u₁, v₁, w, t} R (pullback (𝒰.f q.1) (𝒰.f q.2))) p ≫
        cechRelationsMap.{u₁, v₁, w, t} R 𝒰 =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.fst (𝒰.f p.1) (𝒰.f p.2)) ≫
          Sigma.ι (fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) p.1 -
        extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.snd (𝒰.f p.1) (𝒰.f p.2)) ≫
          Sigma.ι (fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) p.2 :=
  Sigma.ι_comp_desc _ _

/-- The Čech relations are relations: they are killed by the map to `j_{U!} O_U`. -/
lemma cechRelationsMap_comp_sigmaDesc :
    cechRelationsMap.{u₁, v₁, w, t} R 𝒰 ≫
        (Sigma.desc fun i ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i)) = 0 := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [comp_zero, ι_comp_cechRelationsMap_assoc, Preadditive.sub_comp, Category.assoc,
    Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, ← extensionByZeroUnitMap_comp,
    ← extensionByZeroUnitMap_comp, pullback.condition, sub_self]

/-- **The Čech sequence of a covering family**, as a short complex
`⊕_{i, j} j_{U_i ×_U U_j!} O_{U_i ×_U U_j} ⟶ ⊕_i j_{U_i!} O_{U_i} ⟶ j_{U!} O_U`. -/
noncomputable def cechShortComplex : ShortComplex (SheafOfModules.{max u₁ v₁ w t} R) :=
  ShortComplex.mk (cechRelationsMap.{u₁, v₁, w, t} R 𝒰)
    (Sigma.desc fun i ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i))
    (cechRelationsMap_comp_sigmaDesc.{u₁, v₁, w, t} R 𝒰)

/-- The second map of `cechShortComplex` is the sum of the maps `j_{U_i!} O_{U_i} ⟶ j_{U!} O_U`. -/
@[simp]
lemma cechShortComplex_g :
    (cechShortComplex.{u₁, v₁, w, t} R 𝒰).g =
      Sigma.desc fun i ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i) := rfl

/-- The first map of `cechShortComplex` is `cechRelationsMap`. -/
@[simp]
lemma cechShortComplex_f :
    (cechShortComplex.{u₁, v₁, w, t} R 𝒰).f = cechRelationsMap.{u₁, v₁, w, t} R 𝒰 := rfl

/-! ### The sheaf axiom as the cokernel property -/

/-- A morphism out of `⊕_i j_{U_i!} O_{U_i}` which kills the Čech relations takes the same
value on the two restrictions of any pair of competing arrows, not only on the canonical
fibre-product projections: factor the competing pair through the fibre product. -/
lemma comp_eq_of_cechRelationsMap_comp_eq_zero {N : SheafOfModules.{max u₁ v₁ w t} R}
    (φ : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) ⟶ N)
    (hφ : cechRelationsMap.{u₁, v₁, w, t} R 𝒰 ≫ φ = 0) {Z : C} {i j : 𝒰.I₀}
    (gi : Z ⟶ 𝒰.X i) (gj : Z ⟶ 𝒰.X j) (hg : gi ≫ 𝒰.f i = gj ≫ 𝒰.f j) :
    extensionByZeroUnitMap.{u₁, v₁, w, t} R gi ≫
        Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i')) i ≫ φ =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R gj ≫
        Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i')) j ≫ φ := by
  have hp : extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.fst (𝒰.f i) (𝒰.f j)) ≫
        Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i')) i ≫ φ =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.snd (𝒰.f i) (𝒰.f j)) ≫
        Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i')) j ≫ φ := by
    have h := Sigma.ι (fun q : 𝒰.I₀ × 𝒰.I₀ ↦
      extensionByZeroUnit.{u₁, v₁, w, t} R (pullback (𝒰.f q.1) (𝒰.f q.2))) (i, j) ≫= hφ
    rw [comp_zero, ι_comp_cechRelationsMap_assoc, Preadditive.sub_comp, Category.assoc,
      Category.assoc, sub_eq_zero] at h
    exact h
  have e : ∀ {V : C} (a : pullback (𝒰.f i) (𝒰.f j) ⟶ V) (g : Z ⟶ V),
      pullback.lift gi gj hg ≫ a = g → extensionByZeroUnitMap.{u₁, v₁, w, t} R g =
        extensionByZeroUnitMap.{u₁, v₁, w, t} R (pullback.lift gi gj hg) ≫
          extensionByZeroUnitMap.{u₁, v₁, w, t} R a := by
    rintro V a g rfl
    rw [extensionByZeroUnitMap_comp]
  rw [e _ gi (pullback.lift_fst _ _ _), e _ gj (pullback.lift_snd _ _ _), Category.assoc,
    Category.assoc, hp]

/-- **The sheaf axiom, read through Stacks 0G1V.** A morphism `φ : ⊕_i j_{U_i!} O_{U_i} ⟶ N`
which kills the Čech relations of a *covering* family factors through `j_{U!} O_U`.

Under Stacks 0G1V the restrictions of `φ` to the summands are sections of `N` over the `U_i`;
killing the Čech relations says that they agree on the fibre products, i.e. that they form a
compatible family, and the factorisation is their amalgamation. -/
theorem exists_hom_of_cechRelationsMap_comp_eq_zero (h𝒰 : 𝒰.sieve₀ ∈ J U)
    {N : SheafOfModules.{max u₁ v₁ w t} R}
    (φ : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i)) ⟶ N)
    (hφ : cechRelationsMap.{u₁, v₁, w, t} R 𝒰 ≫ φ = 0) :
    ∃ ψ : extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ N,
      (Sigma.desc fun i ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i)) ≫ ψ = φ := by
  have hP : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{max u₁ v₁ w t}) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget AddCommGrpCat.{max u₁ v₁ w t})).obj ⟨_, N.isSheaf⟩).2
  have hsf := (Presieve.isSheafFor_iff_generate
    (P := N.val.presheaf ⋙ forget AddCommGrpCat.{max u₁ v₁ w t})
    (Presieve.ofArrows 𝒰.X 𝒰.f)).2 (hP _ h𝒰)
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  obtain ⟨s, hs, -⟩ := hsf
    (fun i ↦ extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒰.X i) N
      (Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (𝒰.X i')) i ≫ φ))
    (fun i j Z gi gj hg ↦ by
      refine ((extensionByZeroUnitHomEquiv_map.{u₁, v₁, w, t} R gi N _).symm.trans ?_).trans
        (extensionByZeroUnitHomEquiv_map.{u₁, v₁, w, t} R gj N _)
      exact congrArg (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R Z N)
        (comp_eq_of_cechRelationsMap_comp_eq_zero.{u₁, v₁, w, t} R 𝒰 φ hφ gi gj hg))
  refine ⟨(extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N).symm s,
    Sigma.hom_ext _ _ fun i ↦ ?_⟩
  rw [Sigma.ι_comp_desc_assoc]
  refine (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒰.X i) N).injective ?_
  rw [extensionByZeroUnitHomEquiv_map]
  exact (congrArg (fun x ↦ N.val.map (𝒰.f i).op x)
    (Equiv.apply_symm_apply (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N) s)).trans (hs i)

/-- **`⊕_i j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` is a cokernel of the Čech relations map.** This is
the full content of Stacks 0934: the universal property says both that the sequence is exact
in the middle and that the right-hand map is an epimorphism. -/
noncomputable def isColimitCokernelCoforkCechShortComplex (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    IsColimit (CokernelCofork.ofπ (cechShortComplex.{u₁, v₁, w, t} R 𝒰).g
      (cechShortComplex.{u₁, v₁, w, t} R 𝒰).zero) :=
  haveI : Epi (cechShortComplex.{u₁, v₁, w, t} R 𝒰).g :=
    epi_sigmaDesc_extensionByZeroUnitMap.{u₁, v₁, w, t} R 𝒰 h𝒰
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk ↦
    ⟨(exists_hom_of_cechRelationsMap_comp_eq_zero.{u₁, v₁, w, t} R 𝒰 h𝒰 k hk).choose,
      (exists_hom_of_cechRelationsMap_comp_eq_zero.{u₁, v₁, w, t} R 𝒰 h𝒰 k hk).choose_spec⟩

/-- **Stacks Project, Tag 0934**, exactness in the middle. For a covering family
`{U_i → U}` with existing pairwise fibre products, the Čech sequence
`⊕_{i, j} j_{U_i ×_U U_j!} O_{U_i ×_U U_j} ⟶ ⊕_i j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` is exact at
`⊕_i j_{U_i!} O_{U_i}`. -/
@[stacks 0934 "exactness in the middle, i.e. the relations among the generators
  `j_{U_i!} O_{U_i}` of `j_{U!} O_U` are generated by the fibre products"]
theorem cechShortComplex_exact (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    (cechShortComplex.{u₁, v₁, w, t} R 𝒰).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkCechShortComplex.{u₁, v₁, w, t} R 𝒰 h𝒰)

/-- **Stacks Project, Tag 0934**, exactness at `j_{U!} O_U`. This is
`Stacks.SheafOfModules.epi_sigmaDesc_extensionByZeroUnitMap` — the surjectivity half of
Stacks 0G1W, which needs neither the fibre products nor quasi-compactness — read off the
Čech short complex. -/
@[stacks 0934 "exactness at `j_{U!} O_U`, i.e. the right-hand map is an epimorphism"]
theorem epi_cechShortComplex_g (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    Epi (cechShortComplex.{u₁, v₁, w, t} R 𝒰).g :=
  epi_sigmaDesc_extensionByZeroUnitMap.{u₁, v₁, w, t} R 𝒰 h𝒰

end Cech

/-! ### Stacks 0G1W, the middle exactness half -/

section QuasiCompactCech

variable (R : Sheaf J RingCat.{w}) {U : C}

/-- **Stacks Project, Tag 0G1W**, the middle exactness half. If `U` is a quasi-compact object
and `{U_i → U}_{i ∈ I}` is a covering family whose pairwise fibre products exist, then there
is a finite subset `I' ⊆ I` for which the Čech sequence of the subfamily `{U_i → U}_{i ∈ I'}`
is exact in the middle as well as at `j_{U!} O_U`.

Quasi-compactness is used only through
`Stacks.SheafOfModules.QuasiCompact.exists_finite_restrictIndex_sieve₀_mem`: a covering family
of a quasi-compact object has a finite subfamily which is *still a covering*, and Stacks 0934
applies to that subfamily directly. -/
@[stacks 0G1W "the middle exactness: a finite subfamily of a covering of a quasi-compact
  object already has exact Čech sequence"]
theorem exists_finite_restrictIndex_cechShortComplex_exact
    (hU : J.IsQuasiCompactObject U) (𝒰 : PreZeroHypercover.{max u₁ v₁} U)
    (h𝒰 : 𝒰.sieve₀ ∈ J U) [hpb𝒰 : ∀ i j, HasPullback (𝒰.f i) (𝒰.f j)] :
    ∃ T : Set 𝒰.I₀, T.Finite ∧
      (cechShortComplex.{u₁, v₁, w, t} R (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀))
          (hpb := fun _ _ ↦ hpb𝒰 _ _)).Exact ∧
        Epi (cechShortComplex.{u₁, v₁, w, t} R (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀))
          (hpb := fun _ _ ↦ hpb𝒰 _ _)).g := by
  obtain ⟨T, hTfin, hTcov⟩ :=
    QuasiCompact.exists_finite_restrictIndex_sieve₀_mem hU 𝒰 h𝒰
  exact ⟨T, hTfin,
    cechShortComplex_exact.{u₁, v₁, w, t} R (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀))
      (hpb := fun _ _ ↦ hpb𝒰 _ _) hTcov,
    epi_cechShortComplex_g.{u₁, v₁, w, t} R (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀))
      (hpb := fun _ _ ↦ hpb𝒰 _ _) hTcov⟩

end QuasiCompactCech

end Stacks.SheafOfModules

end
