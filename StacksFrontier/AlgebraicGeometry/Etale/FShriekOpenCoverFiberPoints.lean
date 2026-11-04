module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkAcyclicityCriterion

/-!
# The geometric fibre over an open covering, and the Čech face map on stalks

Let `f : X ⟶ Y` be a morphism of a big étale site, let `s` be a geometric point of `Y`, and let
`U : I → Opens X` be a family of open subschemes of `X`. The geometric fibre of `j_V ≫ f` over
`s`, for `V` an open subscheme of `X`, is the part of the geometric fibre of `f` whose underlying
point lies in `V`; combining this over the intersections `X_{i₀…i_p}` identifies the index set of
the degree-`p` Čech stalk,

`Σ_{t : Fin (p+1) → I} (fibre of f over s inside X_t)  ≃  Σ_{x in the fibre} (Fin (p+1) → I_x)`,

where `I_x = {i : I | x ∈ X_i}`. The right-hand side is the indexing of the acyclicity criterion
`AlgebraicTopology.SimplexCoproductAcyclicity.acyclic_of_simplexCoproduct`, and the index types
`I_x` are nonempty exactly because the family covers `X`, which is where the covering hypothesis
enters: the complex itself exists for an arbitrary family of opens.

This reduces the exactness of the Čech resolution of Stacks 0F5H to the two inputs of that
criterion — the degreewise identification of the stalks with the coproduct model, and the Čech
sign rule for the differential — and the reduction is recorded as
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkDecomposition`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.openSchemeFiberPointEquiv` — the geometric fibre
  of `j_V ≫ f` is the part of the geometric fibre of `f` lying in `V`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverTupleSwapEquiv` — a tuple of indices with a
  fibre point in the corresponding intersection is a fibre point with a tuple of its indices.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverFiberTupleEquiv` — the reindexing of the
  degree-`p` Čech index set by the geometric fibre.

## Main results

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.openFiberPoint_mem` — a point of the geometric
  fibre of `j_V ≫ f` has image in `V`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.exists_openFiberPoint_of_mem_opens` — conversely a
  point of the geometric fibre of `f` lying in `V` comes from one of `j_V ≫ f`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.mem_coverOpen_iff` — a point lies in the
  intersection `X_{i₀…i_p}` exactly when it lies in each `X_{i_k}`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.nonempty_coverIndex` — if the family covers `X`
  then every point lies in some member.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.sheafFiber_map_shriekLE_app_eq` — the stalk of the
  Čech face map is determined by cancelling the stalk of the covariance map.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkDecomposition` —
  the Čech complex of a covering is acyclic once its stalks are identified with the coproduct
  model carrying the Čech sign rule.

## Implementation notes

The source of a geometric point is the spectrum of a field, so its underlying space is a
subsingleton: a morphism out of it has a one-point image, and lifting it through the open
immersion `V.ι` is `AlgebraicGeometry.IsOpenImmersion.lift` applied to that single point. This is
why no scheme-theoretic hypothesis beyond openness is needed, and why the two directions assemble
into a bijection rather than only an injection.

An arbitrary infimum of opens is the interior of the intersection, so the description of
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverOpen` as the set-theoretic intersection uses
that the index type `Fin n` of a tuple is finite.

The stalk of the Čech face map needs no description of the comparison isomorphism
`AlgebraicGeometry.SmallEtale.openShriekCompIso` on stalks. As at the level of sheaves, where
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.shriekLE_trans` cancels a monomorphism rather than
proving a pentagon identity, the face map is pinned down by its composite with the covariance map
of the larger open, which is a monomorphism on every stalk by Stacks 0F6S part (4).

## References

* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

section FiberPoints

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)

/-- A point of an open subscheme has its image in that open. -/
private theorem opensPoint_mem (W : (B.inclusion.obj X).Opens) (p : (W.toScheme : Type u)) :
    W.ι.base p ∈ W := p.2

/-- A point of the geometric fibre of `j_V ≫ f` over `s` has underlying point of `X` in `V`. -/
public theorem openFiberPoint_mem (V : (B.inclusion.obj X).Opens)
    (x : GeometricFiberPoint B (openSchemeι B V ≫ f) s) :
    (openFiberPoint B (openSchemeι B V) f s x).1.base default ∈ V :=
  opensPoint_mem B V _

/-- A point of the geometric fibre of `f` over `s` whose underlying point of `X` lies in `V`
comes from a point of the geometric fibre of `j_V ≫ f`: the geometric point lifts through the
open immersion, its source having a single point. -/
public theorem exists_openFiberPoint_of_mem_opens (V : (B.inclusion.obj X).Opens)
    (y : GeometricFiberPoint B f s) (hy : y.1.base default ∈ V) :
    ∃ x, openFiberPoint B (openSchemeι B V) f s x = y := by
  have hr : Set.range y.1.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default]
  let g : s.source ⟶ V.toScheme := IsOpenImmersion.lift V.ι y.1 hr
  have hfac : g ≫ V.ι = y.1 := IsOpenImmersion.lift_fac _ _ hr
  refine ⟨⟨g, ?_⟩, Subtype.ext hfac⟩
  change g ≫ V.ι ≫ B.inclusion.map f = s.hom
  rw [← Category.assoc, hfac]
  exact y.2

/-- The geometric fibre of `j_V ≫ f` over `s` is the part of the geometric fibre of `f` whose
underlying point of `X` lies in the open subscheme `V`. -/
public def openSchemeFiberPointEquiv (V : (B.inclusion.obj X).Opens) :
    GeometricFiberPoint B (openSchemeι B V ≫ f) s ≃
      {y : GeometricFiberPoint B f s // y.1.base default ∈ V} :=
  Equiv.ofBijective
    (fun x => ⟨openFiberPoint B (openSchemeι B V) f s x, openFiberPoint_mem B f s V x⟩)
    ⟨fun _ _ h =>
      openFiberPoint_injective B (openSchemeι B V) f s (congrArg Subtype.val h),
      fun y => (exists_openFiberPoint_of_mem_opens B f s V y.1 y.2).imp
        fun _ hx => Subtype.ext hx⟩

end FiberPoints

section Reindex

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- A point lies in the intersection `X_{i₀…i_p}` cut out by a tuple of indices exactly when it
lies in each of the opens of the tuple. -/
public theorem mem_coverOpen_iff {n : ℕ} (t : Fin n → I) (p : B.inclusion.obj X) :
    p ∈ coverOpen B U t ↔ ∀ k, p ∈ U (t k) := by
  change p ∈ ((⨅ k, U (t k) : (B.inclusion.obj X).Opens) : Set _) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter

/-- If the family of opens covers `X` then every point of `X` lies in one of its members, so the
index type of the opens containing a point is nonempty. -/
public theorem nonempty_coverIndex (hU : (⨆ i, U i) = ⊤) (p : B.inclusion.obj X) :
    Nonempty {i : I // p ∈ U i} :=
  let ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU ▸ trivial : p ∈ ⨆ i, U i)
  ⟨⟨i, hi⟩⟩

/-- A tuple of indices together with a point of the fibre inside the corresponding intersection
is the same as a point of the fibre together with a tuple of indices of opens containing it. -/
public def coverTupleSwapEquiv (n : ℕ) :
    (Σ t : Fin n → I,
        {y : GeometricFiberPoint B f s // y.1.base default ∈ coverOpen B U t}) ≃
      Σ y : GeometricFiberPoint B f s, Fin n → {i : I // y.1.base default ∈ U i} where
  toFun a := ⟨a.2.1, fun k => ⟨a.1 k, (mem_coverOpen_iff B U a.1 _).1 a.2.2 k⟩⟩
  invFun a := ⟨fun k => (a.2 k).1,
    ⟨a.1, (mem_coverOpen_iff B U _ _).2 fun k => (a.2 k).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The reindexing of the degree-`p` Čech stalk.** The pairs consisting of a tuple of `n`
indices and a point of the geometric fibre of `f_{i₀…i_{n-1}}` over `s` are the pairs consisting
of a point `x` of the geometric fibre of `f` and a tuple of `n` indices of opens containing it. -/
public def coverFiberTupleEquiv (n : ℕ) :
    (Σ t : Fin n → I, GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s) ≃
      Σ y : GeometricFiberPoint B f s, Fin n → {i : I // y.1.base default ∈ U i} :=
  (Equiv.sigmaCongrRight fun t =>
      openSchemeFiberPointEquiv B f s (coverOpen B U t)).trans
    (coverTupleSwapEquiv.{u, v} B f s U n)

end Reindex

section FaceMapOnStalks

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The Čech face map is determined on stalks by the covariance maps.** A map of stalks which
composes with the covariance map of the larger open to the covariance map of the smaller one is
the stalk of the Čech face map, the former covariance map being a monomorphism on stalks. -/
public theorem sheafFiber_map_shriekLE_app_eq {V W : (B.inclusion.obj X).Opens} (h : V ≤ W)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj)
    (φ : ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((openShriekPushforward.{u, v} B (openSchemeι B V) f).obj F) ⟶
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((openShriekPushforward.{u, v} B (openSchemeι B W) f).obj F))
    (hφ : φ ≫ ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B (openSchemeι B W) f).app F) =
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B (openSchemeι B V) f).app F)) :
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map ((shriekLE.{u, v} B f h).app F) = φ := by
  have hmono := mono_sheafFiber_openCovarianceShriekMap_app.{u, v} B (openSchemeι B W) f F s
  refine (cancel_mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) v})).map
      ((openCovarianceShriekMap.{u, v} B (openSchemeι B W) f).app F))).1 ?_
  rw [hφ, ← Functor.map_comp]
  exact congrArg _
    (NatTrans.congr_app (shriekLE_comp_openCovarianceShriekMap.{u, v} B f h) F)

end FaceMapOnStalks

section Assembly

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- The indices of the opens of the covering which contain a given point of the geometric
fibre of `f` over a geometric point of `Y`. -/
public abbrev fiberPointCoverIndex (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s) : Type (max (u + 1) v) :=
  {i : I // x.1.base default ∈ U i}

/-- The degree-`n` summand of the coproduct model of the stalk of the Čech complex: the stalk of
the sheaf at the geometric point of `X` underlying a point of the geometric fibre. -/
public abbrev fiberPointStalk (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f s) : AddCommGrpCat.{max (u + 1) v} :=
  AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)

/-- **Stacks 0F5H, exactness, reduced to the stalk decomposition.** Given, at every geometric
point of `Y`, an identification of the stalk of the Čech complex with the coproduct model indexed
by the geometric fibre carrying the Čech sign rule, the Čech complex of a covering is acyclic. -/
public theorem cechComplexObj_acyclic_of_stalkDecomposition (hU : (⨆ i, U i) = ⊤)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (e : ∀ (s : GeometricPoint Y.obj) (n : ℕ),
      (∐ fun t : Σ x : GeometricFiberPoint B f s,
            Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) ≅
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X n))
    (hd : ∀ (s : GeometricPoint Y.obj) (n : ℕ)
        (t : Σ x : GeometricFiberPoint B f s,
          Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x),
      Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
            Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x =>
          fiberPointStalk.{u, v} B f s F t.1) t ≫ (e s (n + 1)).hom ≫
          ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
            ((cechComplexObj.{u, v} B f U F).d (n + 1) n) =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
          (Sigma.ι (fun t : Σ x : GeometricFiberPoint B f s,
                Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
              fiberPointStalk.{u, v} B f s F t.1) ⟨t.1, t.2 ∘ k.succAbove⟩ ≫
            (e s n).hom)) :
    (cechComplexObj.{u, v} B f U F).Acyclic := by
  refine acyclic_of_etaleStalk_exact.{u, v} B Y.obj Y.property _ fun s i => ?_
  have hadd := additive_etaleStalkSheafFiber.{u, v} B Y.obj Y.property s
  have hne : ∀ x : GeometricFiberPoint B f s,
      Nonempty (fiberPointCoverIndex.{u, v} B f U s x) :=
    fun x => nonempty_coverIndex.{u, v} B U hU _
  exact AlgebraicTopology.SimplexCoproductAcyclicity.acyclic_of_simplexCoproduct
    (fiberPointCoverIndex.{u, v} B f U s) (fiberPointStalk.{u, v} B f s F)
    ((((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).mapHomologicalComplex _).obj
      (cechComplexObj.{u, v} B f U F)) (e s) (hd s) i

end Assembly

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
