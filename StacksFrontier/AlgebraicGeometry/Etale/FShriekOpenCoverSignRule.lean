module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverFiberPoints

/-!
# The Čech sign rule on the stalks of the complex of an open covering

Let `f : X ⟶ Y` be locally quasi-finite in a big étale site, let `U : I → Opens X` be a family of
open subschemes, let `F` be an abelian sheaf on the small étale site of `X` and let `s` be a
geometric point of `Y`. Suppose the stalk at `s` of the degree-`n` term of the Čech complex of
Stacks 0F5H is identified with the coproduct `∐_{x, σ} F_x` over the pairs of a point `x` of the
geometric fibre of `f` over `s` and an `n`-tuple `σ` of indices of opens containing `x`, in such a
way that the summand of `(x, σ)` goes into the summand of the intersection `X_σ` by a map whose
composite with the covariance map `(f_{σ,!} F|_{X_σ})_s ⟶ (f_!F)_s` of Stacks 0F6S depends only on
`x`. Then the stalk of the differential obeys the Čech sign rule

`ι_{x,σ} ≫ d = ∑_k (-1)^k ι_{x, σ ∘ δ_k}`,

the alternating sum over the ways of deleting one index from the tuple.

This is the second input of
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkDecomposition`, so
together with such a decomposition it gives the exactness of the complex of Stacks 0F5H.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechObjTermι` — the inclusion of the summand of a
  tuple of indices into the degree-`n` term of the Čech complex of a fixed sheaf.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechObjTermAug` — the augmentation of the
  degree-`n` term onto the degree-zero term `f_!F`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechObjTermMap` — the reindexing map of the terms.

## Main results

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_d_succ_succ` — above degree one the
  differential is the alternating sum of the reindexing maps deleting one index.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.ι_comp_sheafFiber_cechComplexObj_d` — the Čech
  sign rule on the stalk at a geometric point of the base.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkCoefficients` — the
  Čech complex of a covering is acyclic once such a summandwise stalk decomposition is given.

## Implementation notes

Only one property of the summand maps is used, and it is used on two tuples at a time: the
composite with the covariance map of the intersection is the same for a tuple and for the tuple
with one index deleted. Since the covariance map is a monomorphism on every stalk by Stacks 0F6S
part (4), this already pins down the effect of the Čech face map on the summands, so no
description of the comparison isomorphism `AlgebraicGeometry.SmallEtale.openShriekCompIso` on
stalks is needed, exactly as at the level of sheaves.

The alternating signs are those of Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex`, whose
`k`-th face is the reindexing along `Fin.succAbove k`, which deletes the `k`-th entry of a tuple;
the sign rule asserted here is therefore the one the complex has, with no reindexing of the sum.
In degree zero the term of the complex is `f_!F` rather than a direct sum and the summand
inclusion is the covariance map itself, which is why `cechObjTermι` and `cechObjTermAug` are
defined by cases on the degree, and why the sign rule is proved separately in the lowest degree,
where the differential is the augmentation rather than an alternating sum.

The terms of the complex of a fixed sheaf are the values of the terms of the complex of functors,
and the maps between them are the values of the maps of functors; they are nevertheless named
here, because an isomorphism with the coproduct model is stated in terms of the complex of the
sheaf, and a statement mixing the two descriptions of one term is beyond the reach of `rewrite`.

## References

* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u v

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

section Terms

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The covariance map `f_{t,!}(F|_{X_t}) ⟶ f_!F` of Stacks 0F6S, viewed as a map into the
degree-zero term of the Čech complex of `F`. -/
public def cechObjTermCov {n : ℕ} (t : Fin n → I) :
    (openShriekPushforward.{u, v} B (openSchemeι B (coverOpen B U t)) f).obj F ⟶
      (cechComplexObj.{u, v} B f U F).X 0 :=
  (openCovarianceShriekMap.{u, v} B (openSchemeι B (coverOpen B U t)) f).app F

/-- The inclusion of the summand of a tuple of indices into the degree-`n` term of the Čech
complex of `F`: in positive degree the inclusion of a summand of the direct sum, and in degree
zero, where the term of the complex is `f_!F`, the covariance map of the intersection. -/
public def cechObjTermι (n : ℕ) (t : Fin n → I) :
    (openShriekPushforward.{u, v} B (openSchemeι B (coverOpen B U t)) f).obj F ⟶
      (cechComplexObj.{u, v} B f U F).X n :=
  match n with
  | 0 => cechObjTermCov.{u, v} B f U F t
  | m + 1 => (Sigma.ι (cechFamily.{u, v} B f U (m + 1)) t).app F

/-- The augmentation of the degree-`n` term of the Čech complex of `F` onto its degree-zero term
`f_!F`: the sum of the covariance maps in positive degree, and the identity in degree zero. -/
public def cechObjTermAug (n : ℕ) :
    (cechComplexObj.{u, v} B f U F).X n ⟶ (cechComplexObj.{u, v} B f U F).X 0 :=
  match n with
  | 0 => 𝟙 _
  | m + 1 => (cechAugMap.{u, v} B f U (m + 1)).app F

/-- The map of terms of the Čech complex of `F` induced by a reindexing of tuples of indices: on
the summand of a tuple it is the Čech face map into the summand of the reindexed tuple. -/
public def cechObjTermMap {m n : ℕ} (g : Fin (n + 1) → Fin (m + 1)) :
    (cechComplexObj.{u, v} B f U F).X (m + 1) ⟶ (cechComplexObj.{u, v} B f U F).X (n + 1) :=
  (cechMap.{u, v} B f U g).app F

/-- In degree zero the summand inclusion is the covariance map of the intersection. -/
public theorem cechObjTermι_zero (t : Fin 0 → I) :
    cechObjTermι.{u, v} B f U F 0 t = cechObjTermCov.{u, v} B f U F t :=
  rfl

/-- In positive degree the summand inclusion is the inclusion of a summand of the direct sum. -/
public theorem cechObjTermι_succ (n : ℕ) (t : Fin (n + 1) → I) :
    cechObjTermι.{u, v} B f U F (n + 1) t =
      (Sigma.ι (cechFamily.{u, v} B f U (n + 1)) t).app F :=
  rfl

/-- The summand inclusion of a tuple, followed by the augmentation, is the covariance map of the
intersection cut out by that tuple. -/
public theorem cechObjTermι_comp_cechObjTermAug (n : ℕ) (t : Fin n → I) :
    cechObjTermι.{u, v} B f U F n t ≫ cechObjTermAug.{u, v} B f U F n =
      cechObjTermCov.{u, v} B f U F t := by
  cases n with
  | zero => exact Category.comp_id _
  | succ m => exact congrArg (fun α => NatTrans.app α F) (ι_comp_cechAugMap.{u, v} B f U t)

/-- The summand inclusions are compatible with the reindexing maps: on the summand of a tuple, a
reindexing is the Čech face map of the corresponding inclusion of intersections followed by the
summand inclusion of the reindexed tuple. -/
public theorem cechObjTermι_comp_cechObjTermMap {m n : ℕ} (t : Fin (m + 1) → I)
    (g : Fin (n + 1) → Fin (m + 1)) :
    cechObjTermι.{u, v} B f U F (m + 1) t ≫ cechObjTermMap.{u, v} B f U F g =
      (shriekLE.{u, v} B f (coverOpen_le_comp B U t g)).app F ≫
        cechObjTermι.{u, v} B f U F (n + 1) (t ∘ g) :=
  congrArg (fun α => NatTrans.app α F) (ι_comp_cechMap.{u, v} B f U g t)

/-- The last differential of the Čech complex of `F` is the augmentation. -/
public theorem cechComplexObj_d_one_zero :
    (cechComplexObj.{u, v} B f U F).d 1 0 = cechObjTermAug.{u, v} B f U F 1 :=
  rfl

/-- Above degree one the differential of the Čech complex of `F` is the alternating sum of the
reindexing maps deleting one index from a tuple: the Čech sign rule. -/
public theorem cechComplexObj_d_succ_succ (n : ℕ) :
    (cechComplexObj.{u, v} B f U F).d (n + 1 + 1) (n + 1) =
      ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ (i : ℕ) •
        cechObjTermMap.{u, v} B f U F i.succAbove := by
  have h₁ : (cechComplex.{u, v} B f U).d (n + 1 + 1) (n + 1) =
      ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ (i : ℕ) • cechMap.{u, v} B f U i.succAbove :=
    (cechComplex_d_succ_succ.{u, v} B f U n).trans
      (alternatingFaceMapComplex_cechSimplicial_d.{u, v} B f U n)
  exact (congrArg (·.app F) h₁).trans (by
    rw [NatTrans.app_sum]
    exact Finset.sum_congr rfl fun i _ => NatTrans.app_zsmul F _ _)

end Terms

section SignRule

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- **The Čech sign rule on stalks.** Let the stalk at `s` of the degree-`n` term of the Čech
complex be identified with the coproduct of the stalks of `F` over the pairs of a point `x` of the
geometric fibre of `f` over `s` and an `n`-tuple of indices of opens containing it, in such a way
that each summand map factors through the summand of the intersection cut out by the tuple by a
map `c` whose composite with the covariance map of that intersection is a map `δ x` depending only
on `x`. Then the stalk of the differential takes the summand of a tuple to the alternating sum,
with the signs of the alternating-face-map complex, of the summands of the tuples obtained by
deleting one index. -/
public theorem ι_comp_sheafFiber_cechComplexObj_d (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (e : ∀ n : ℕ,
      (∐ fun t : Σ x : GeometricFiberPoint B f s,
            Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) ≅
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X n))
    (δ : ∀ x : GeometricFiberPoint B f s,
      fiberPointStalk.{u, v} B f s F x ⟶
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj ((fShriekFunctor.{u, v} B f).obj F))
    (c : ∀ (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      fiberPointStalk.{u, v} B f s F x ⟶
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj
          ((openShriekPushforward.{u, v} B
            (openSchemeι B (coverOpen B U fun k => (q k).1)) f).obj F))
    (hc : ∀ (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      c n x q ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B
            (openSchemeι B (coverOpen B U fun k => (q k).1)) f).app F) = δ x)
    (he : ∀ (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
            Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) ⟨x, q⟩ ≫ (e n).hom =
        c n x q ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          (cechObjTermι.{u, v} B f U F n fun k => (q k).1))
    (n : ℕ) (t : Σ x : GeometricFiberPoint B f s,
      Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x) :
    Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
          Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x =>
        fiberPointStalk.{u, v} B f s F t.1) t ≫ (e (n + 1)).hom ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((cechComplexObj.{u, v} B f U F).d (n + 1) n) =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        (Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
              Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
            fiberPointStalk.{u, v} B f s F t.1) ⟨t.1, t.2 ∘ k.succAbove⟩ ≫ (e n).hom) := by
  have hadd := additive_etaleStalkSheafFiber.{u, v} B Y.obj Y.property s
  have hface : ∀ (m p : ℕ) (x : GeometricFiberPoint B f s)
      (q : Fin (m + 1) → fiberPointCoverIndex.{u, v} B f U s x) (g : Fin (p + 1) → Fin (m + 1)),
      c (m + 1) x q ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((shriekLE.{u, v} B f (coverOpen_le_comp B U (fun k => (q k).1) g)).app F) =
        c (p + 1) x (q ∘ g) := by
    intro m p x q g
    have hmono := mono_sheafFiber_openCovarianceShriekMap_app.{u, v} B
      (openSchemeι B (coverOpen B U ((fun k => (q k).1) ∘ g))) f F s
    refine (cancel_mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map
        ((openCovarianceShriekMap.{u, v} B
          (openSchemeι B (coverOpen B U ((fun k => (q k).1) ∘ g))) f).app F))).1 ?_
    rw [Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app,
      shriekLE_comp_openCovarianceShriekMap]
    exact (hc _ x _).trans (hc _ x _).symm
  obtain ⟨x, q⟩ := t
  cases n with
  | zero =>
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rw [cechComplexObj_d_one_zero, ← Category.assoc, he (0 + 1) x q, Category.assoc,
      ← Functor.map_comp, cechObjTermι_comp_cechObjTermAug,
      he 0 x (q ∘ (0 : Fin 1).succAbove)]
    exact (hc _ x _).trans (hc _ x _).symm
  | succ m =>
    rw [cechComplexObj_d_succ_succ, Functor.map_sum]
    simp only [Functor.map_zsmul, Preadditive.comp_sum, Preadditive.comp_zsmul]
    refine Finset.sum_congr rfl fun k _ => congrArg (fun z => (-1 : ℤ) ^ (k : ℕ) • z) ?_
    rw [← Category.assoc, he (m + 1 + 1) x q, Category.assoc, ← Functor.map_comp,
      cechObjTermι_comp_cechObjTermMap, Functor.map_comp, ← Category.assoc,
      hface (m + 1) m x q k.succAbove]
    exact (he (m + 1) x (q ∘ k.succAbove)).symm

/-- **Stacks 0F5H, exactness.** The Čech complex of an open covering is acyclic once, at every
geometric point `s` of `Y`, the stalk of its degree-`n` term is identified with the coproduct of
the stalks of `F` over the pairs of a point `x` of the geometric fibre and an `n`-tuple of indices
of opens containing it, summandwise through the summand of the intersection cut out by the tuple
and compatibly with the covariance maps of those intersections. -/
public theorem cechComplexObj_acyclic_of_stalkCoefficients (hU : (⨆ i, U i) = ⊤)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (e : ∀ (s : GeometricPoint Y.obj) (n : ℕ),
      (∐ fun t : Σ x : GeometricFiberPoint B f s,
            Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) ≅
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X n))
    (δ : ∀ (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s),
      fiberPointStalk.{u, v} B f s F x ⟶
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj ((fShriekFunctor.{u, v} B f).obj F))
    (c : ∀ (s : GeometricPoint Y.obj) (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      fiberPointStalk.{u, v} B f s F x ⟶
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj
          ((openShriekPushforward.{u, v} B
            (openSchemeι B (coverOpen B U fun k => (q k).1)) f).obj F))
    (hc : ∀ (s : GeometricPoint Y.obj) (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      c s n x q ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B
            (openSchemeι B (coverOpen B U fun k => (q k).1)) f).app F) = δ s x)
    (he : ∀ (s : GeometricPoint Y.obj) (n : ℕ) (x : GeometricFiberPoint B f s)
        (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x),
      Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
            Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) ⟨x, q⟩ ≫ (e s n).hom =
        c s n x q ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          (cechObjTermι.{u, v} B f U F n fun k => (q k).1)) :
    (cechComplexObj.{u, v} B f U F).Acyclic :=
  cechComplexObj_acyclic_of_stalkDecomposition.{u, v} B f U hU F e fun s n t =>
    ι_comp_sheafFiber_cechComplexObj_d.{u, v} B f U s F (e s) (δ s) (c s) (hc s) (he s) n t

end SignRule

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
