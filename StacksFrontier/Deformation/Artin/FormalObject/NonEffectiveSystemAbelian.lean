module

public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleLimitTorsion
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleQuotientStackClass

/-!
# A non-effective system of objects of `[Spec(k)/A]` (Stacks 0CXX)

Let `k` be an algebraically closed field which is not the algebraic closure of a finite field and
let `A` be an abelian variety over `k` of dimension at least one. This file proves Stacks 0CXX:
there are an inverse system of `k`-algebras `R_n`, with surjective transition maps whose kernels
are locally nilpotent, and a system `(ξ_n)` of objects of `𝒳 = [Spec(k)/A]` over the spectra of
the `R_n` which is not effective in the sense of Stacks 0CXT. As printed, Stacks 0CXX has no
condition on the dimension of `A`, and it fails for the zero abelian variety `A = Spec k`, over
which `[Spec(k)/A]` is the final stack and every system is effective (`errata.md`, entry of
2026-10-28, "0CXX, the zero abelian variety"); the statement here carries the correction
`1 ≤ dim A`.

The system is that of the discussion before Stacks 0CXX, run over the function field
`K = k(A)` of `A` instead of over `k`:

* `R_n = K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)`, the thickenings of the triangle over `K`, regarded
  as `k`-algebras (`Deformation.Artin.powQuotientDiagram`); its limit is the completion
  `K[x, y]^∧` (`Deformation.Artin.isLimitAdicCompletionCone`);
* `ξ_n` is the object of `𝒳` over `Spec R_n` glued from trivial torsors along the generic point
  `η : Spec K ⟶ A` (`Deformation.Artin.triangleSystem`);
* the class of `ξ_0` in `H¹_fppf(Spec R_0, A)` has infinite order, because `η` is not a torsion
  point when `dim A ≥ 1`
  (`Deformation.Artin.not_isOfFinAddOrder_quotientStackTrivialActionClass_triangleObject`, through
  Stacks 0AEN);
* every object of `𝒳` over `Spec K[x, y]^∧` has a class of finite order, since `K[x, y]^∧` is a
  two dimensional regular Noetherian domain (Stacks 0AF9 and 0AFA,
  `isOfFinAddOrder_quotientStackTrivialActionClass_of_iso_spec_triangleCompletion` in the
  namespace `AlgebraicGeometry.Space.GroupAlgebraicSpace`).

A morphism of `𝒳` from `ξ_0` to an object over the limit would make the first class the
restriction of the second, so the system is not effective
(`Deformation.Artin.not_isEffectiveSystem_of_not_isOfFinAddOrder_of_addMonoidHom`).

The source glues along a non-torsion point of `A(k)`, whose existence it does not prove (for
countable `k` it is a theorem of Frey and Jarden, recorded in `errata.md`, entry of 2026-10-28 on
0AFB). The lemma asks for some inverse system of `k`-algebras, not a specific one, and over `K`
the generic point is a non-torsion point whose existence is elementary; this is why the
hypothesis that `k` is not the algebraic closure of a finite field is not used. It is kept so
that the statement has the hypotheses of the source.

## Main definitions

* `Deformation.Artin.abelianVarietyClassifyingStack`: the stack `[Spec(k)/A]`, the quotient
  stack of the trivial action on `Spec k` of the group algebraic space of `A`.
* `Deformation.Artin.triangleLimitSite` and `Deformation.Artin.triangleLimitCocone`: the
  spectrum of `K[x, y]^∧` as an object of the big fppf site of `Spec k`, and the cocone of the
  thickenings with that vertex.

## Main results

* `Deformation.Artin.contains_left_of_isAbelianVariety`,
  `Deformation.Artin.contains_spec_triangleLevel` and
  `Deformation.Artin.contains_spec_triangleCompletion`: `A`, the thickenings over `K` and the
  spectrum of `K[x, y]^∧` lie in every big fppf site containing `Spec k`.
* `Deformation.Artin.not_isEffectiveSystem_quotientStack_of_not_isOfFinAddOrder`: the torsion
  comparison for the first cohomology class of `[S/G]`.
* `Deformation.Artin.exists_nonEffectiveSystem_quotientStack_abelianVariety`: **Stacks 0CXX**.
* `Deformation.Artin.not_isStronglyFormallyEffective_quotientStack_abelianVariety`: `[Spec(k)/A]`
  does not satisfy strong formal effectiveness.

## Implementation notes

Sheafification, `Ext`-groups and local bijectivity on the localized big fppf sites, and
sheafification, `Ext`-groups and enough injectives on the big fppf site of each object, are
instance arguments, as everywhere in the library for the big fppf site (see
`AlgebraicGeometry.Space.fppfH1_isAddTorsion`, Stacks 0AFA, and
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_dim_two`, Stacks 0AF9): the site
has objects one universe above its morphisms and coefficients, and Mathlib provides none of them
for such a site. The site itself is any big fppf site containing `Spec k`; `A`, the thickenings and
the limit lie in it automatically.

## References

* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Space
open scoped CategoryTheory.MonObj

universe w u

namespace Deformation.Artin

section Size

variable {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})

/-- An abelian variety over `k` lies in every big fppf site containing `Spec k`: it is of finite
type over `k` and quasi-compact. -/
theorem contains_left_of_isAbelianVariety (hk : 𝒞.Contains (Spec (.of k)))
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A] : 𝒞.Contains A.left :=
  (Scheme.size_le_of_locallyOfFiniteType A.hom).trans_lt hk

variable (K : Type u) [Field K]

/-- The thickenings of the triangle over a field `K` lie in every big fppf site containing
`Spec K`: they are of finite type over `K`. -/
theorem contains_spec_triangleLevel (hK : 𝒞.Contains (Spec (.of K))) (n : ℕ) :
    𝒞.Contains (Spec (.of (triangleLevel K n))) :=
  Scheme.size_Spec_lt_of_finiteType 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit K _ hK

/-- The cardinality of the completion `K[x, y]^∧` is at most `max ℵ₀ #K ^ ℵ₀`: an element is a
sequence of residues of polynomials. -/
theorem mk_triangleCompletion_le :
    Cardinal.mk (triangleCompletion K) ≤ max Cardinal.aleph0 (Cardinal.mk K) ^ Cardinal.aleph0 := by
  have hinj : Function.Injective (fun (x : triangleCompletion K) (n : ℕ) =>
      Function.surjInv (Submodule.Quotient.mk_surjective _) (x.1 n)) := fun x y h =>
    Subtype.ext (funext fun n => Function.injective_surjInv _ (congrFun h n))
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
  refine Cardinal.power_le_power_right (MvPolynomial.cardinalMk_le_max_lift.trans ?_)
  rw [Cardinal.lift_uzero]
  have h2 : Cardinal.lift.{u} (Cardinal.mk (Fin 2)) ≤ Cardinal.aleph0 := by
    exact Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
  exact sup_le (sup_le le_sup_right (h2.trans le_sup_left)) le_sup_left

/-- The completion `K[x, y]^∧` lies in every big fppf site containing `Spec K`. -/
theorem contains_spec_triangleCompletion (hK : 𝒞.Contains (Spec (.of K))) :
    𝒞.Contains (Spec (.of (triangleCompletion K))) :=
  Scheme.size_Spec_lt_of_mk_le 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit _ hK
    ((mk_triangleCompletion_le K).trans_eq (by rw [Scheme.size_Spec]))

end Size

/-! ### The torsion comparison for the first cohomology class of `[S/G]` -/

section ClassComparison

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  (G : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS))
  [G.IsCommutative]
  [∀ U : BigFppfOver 𝒞 S hS, HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 S hS,
    ((BigFppfOver.topology 𝒞 S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback

/-- **A system of objects of `[S/G]` is not effective** over a base cocone when the first
cohomology class (`AlgebraicGeometry.Space.quotientStackTrivialActionClass`) of one of its
objects has infinite order while every object over the vertex of the cocone has a class of finite
order: the class is compatible with pullback (`quotientStackTrivialActionClass_map`). -/
theorem not_isEffectiveSystem_quotientStack_of_not_isOfFinAddOrder {J : Type*} [Category* J]
    (ξ : J ⥤ (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X
      (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).obj)
    (c : Cocone (ξ ⋙ (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩
      G.obj.X (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p)) (j : J)
    (htors : ∀ x, (Stack.quotientStackOfAction ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩
      G.obj.X (𝟙_ (Over (baseS 𝒞 S hS))) G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p.obj x =
        c.pt → IsOfFinAddOrder (quotientStackTrivialActionClass.{w} G x))
    (hfree : ¬ IsOfFinAddOrder (quotientStackTrivialActionClass.{w} G (ξ.obj j))) :
    ¬ IsEffectiveSystem (Stack.quotientStackOfAction
      ⟨baseS 𝒞 S hS, isAlgebraicSpace_baseS 𝒞 S hS⟩ G.obj.X (𝟙_ (Over (baseS 𝒞 S hS)))
        G.property (isAlgebraicSpace_baseS 𝒞 S hS)).p ξ c :=
  not_isEffectiveSystem_of_not_isOfFinAddOrder_of_addMonoidHom _ _
    (quotientStackTrivialActionClass.{w} G)
    (fun _ => Stacks.Cohomology.Torsors.overMapH1Restrict _ _ _ 1)
    (quotientStackTrivialActionClass_map G) ξ c j htors hfree

end ClassComparison

/-! ### The class of `ξ_0`, for the group algebraic space of `A` -/

section Free

variable {k : Type u} [Field k] {𝒞 : BigFppfSite.{u}} {hk : 𝒞.Contains (Spec (.of k))}
  {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A] (hA : 𝒞.Contains A.left)
  (hRA : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel A.left.functionField n))))
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Deformation.Artin.not_isOfFinAddOrder_quotientStackTrivialActionClass_triangleObject`, for
the group algebraic space `GroupAlgebraicSpace.ofGroupScheme A hA` of `A`, which is
`Deformation.Artin.siteGroupSpace A hA`. -/
theorem not_isOfFinAddOrder_quotientStackTrivialActionClass_ofGroupScheme_triangleObject
    [Infinite k] (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    letI := functionFieldAlgebra A
    ¬ IsOfFinAddOrder (quotientStackTrivialActionClass.{w}
      (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA)
      (triangleObject A.left.functionField 𝒞 hk hRA hA (genericPointOverField A) 0).1) :=
  not_isOfFinAddOrder_quotientStackTrivialActionClass_triangleObject hA hRA hdim

/-- **The system `ξ_0 ⟶ ξ_1 ⟶ ⋯` is not effective** over a base cocone over every object of
whose vertex the class of an object of `[Spec(k)/A]` has finite order: the class of `ξ_0` has
infinite order. -/
theorem not_isEffectiveSystem_triangleSystem
    [Infinite k] (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    letI := functionFieldAlgebra A
    ∀ (c : Cocone (triangleSystem A.left.functionField 𝒞 hk hRA hA (genericPointOverField A) ⋙
        (Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).property
          (isAlgebraicSpace_baseS 𝒞 _ hk)).p)),
      (∀ x, (Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).property
          (isAlgebraicSpace_baseS 𝒞 _ hk)).p.obj x = c.pt →
        IsOfFinAddOrder (quotientStackTrivialActionClass.{w}
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA) x)) →
      ¬ IsEffectiveSystem (Stack.quotientStackOfAction
          ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
          (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A hA).property
          (isAlgebraicSpace_baseS 𝒞 _ hk)).p
        (triangleSystem A.left.functionField 𝒞 hk hRA hA (genericPointOverField A)) c :=
  fun c htors => not_isEffectiveSystem_quotientStack_of_not_isOfFinAddOrder _ _ c 0 htors
    (not_isOfFinAddOrder_quotientStackTrivialActionClass_ofGroupScheme_triangleObject hA hRA hdim)

end Free

/-! ### The spectrum of the limit as an object of the site, and the base cocone -/

section Limit

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] {𝒞 : BigFppfSite.{u}}
  {hk : 𝒞.Contains (Spec (.of k))} (hR : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel K n))))
  (hL : 𝒞.Contains (Spec (.of (triangleCompletion K))))

/-- The spectra `Spec R_n` of the levels of an inverse system of `k`-algebras, as a functor
`ℕ ⥤ Scheme`. -/
abbrev specSystem (R : ℕᵒᵖ ⥤ CommAlgCat.{u} k) : ℕ ⥤ Scheme.{u} :=
  (R ⋙ forget₂ (CommAlgCat.{u} k) CommRingCat.{u}).rightOp ⋙ Scheme.Spec

/-- The scheme of the `n`-th level of `Deformation.Artin.triangleSiteSystem` is `Spec R_n`, for
`R_n` the `n`-th level of the inverse system of thickenings of the triangle over `K`, regarded as
`k`-algebras; this is the identity, natural in `n`. -/
def triangleSiteSystemSpecHom :
    triangleSiteSystem K 𝒞 hk hR ⋙ BigFppfOver.toScheme 𝒞 _ hk ⟶
      specSystem (powQuotientDiagram k (triangleIdeal K)) :=
  NatTrans.ofSequence (fun n => 𝟙 (Spec (.of (triangleLevel K n)))) (fun n =>
    (Category.comp_id _).trans (Eq.trans (by
      rw [Functor.comp_map, triangleSiteSystem_map_succ]
      rfl) (Category.id_comp _).symm))

/-- The scheme map underlying a transition map of `Deformation.Artin.triangleSiteSystem` is the
map of spectra of the corresponding transition map of the thickenings, as `k`-algebras. -/
theorem toScheme_map_triangleSiteSystem_map {i j : ℕ} (g : i ⟶ j) :
    (BigFppfOver.toScheme 𝒞 _ hk).map ((triangleSiteSystem K 𝒞 hk hR).map g) =
      Scheme.Spec.map (CommRingCat.ofHom
        ((powQuotientDiagram k (triangleIdeal K)).map g.op).hom.toRingHom).op :=
  (Category.comp_id _).symm.trans
    (((triangleSiteSystemSpecHom (k := k) K hR).naturality g).trans (Category.id_comp _))

variable (k) in
/-- The spectrum of the completion `K[x, y]^∧` as an object of the big fppf site of `Spec k`. -/
def triangleLimitSite : BigFppfOver 𝒞 (Spec (.of k)) hk :=
  BigFppfOver.mk 𝒞 _ hk hL (specOverField k K (triangleCompletion K)).hom

/-- The closed immersion `X_n ⟶ Spec K[x, y]^∧` in the big fppf site, induced by the leg of the
limit cone at `n`. -/
def triangleLimitSiteι (n : ℕ) : triangleSite K 𝒞 hk hR n ⟶ triangleLimitSite k K hL :=
  BigFppfOver.homMk 𝒞 _ hk hL _
    (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ (triangleIdeal K) (n + 1)).toRingHom)) (by
    change _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      show (AdicCompletion.evalₐ (triangleIdeal K) (n + 1)).toRingHom.comp
          (algebraMap K (triangleCompletion K)) = algebraMap K (triangleLevel K n) from
        RingHom.ext ((AdicCompletion.evalₐ (triangleIdeal K) (n + 1)).restrictScalars K).commutes])

/-- The cocone of the system of thickenings with vertex `Spec K[x, y]^∧`. -/
def triangleLimitCocone : Cocone (triangleSiteSystem K 𝒞 hk hR) where
  pt := triangleLimitSite k K hL
  «ι» := NatTrans.ofSequence (fun n => triangleLimitSiteι K hR hL n) (fun n => by
    refine Eq.trans ?_ (Category.comp_id _).symm
    apply (BigFppfOver.toScheme 𝒞 _ hk).map_injective
    refine ((BigFppfOver.toScheme 𝒞 _ hk).map_comp _ _).trans ?_
    refine (congrArg (· ≫ _)
      (toScheme_map_triangleSiteSystem_map K hR (homOfLE (Nat.le_succ n)))).trans ?_
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    exact CommRingCat.hom_ext (RingHom.ext fun x => congrArg (fun φ => CommAlgCat.Hom.hom φ x)
      ((adicCompletionCone k (triangleIdeal K)).w (homOfLE (Nat.le_succ n)).op)))

end Limit

/-! ### The classifying stack of an abelian variety and its non-effective system -/

section Stack

open GroupAlgebraicSpace
  (isOfFinAddOrder_quotientStackTrivialActionClass_of_iso_spec_triangleCompletion)

variable {k : Type u} [Field k] (𝒞 : BigFppfSite.{u}) (hk : 𝒞.Contains (Spec (.of k)))
  (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]

/-- **The classifying stack `[Spec(k)/A]`** of an abelian variety `A` over `k`, over the big fppf
site of `Spec k`: the quotient stack (Stacks 044Q) of the trivial action on `Spec k` of the group
algebraic space of `A` (Stacks 043I). -/
abbrev abelianVarietyClassifyingStack :=
  Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
    (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A
      (contains_left_of_isAbelianVariety 𝒞 hk A)).obj.X
    (𝟙_ (Over (baseS 𝒞 _ hk)))
    (GroupAlgebraicSpace.ofGroupScheme (hS := hk) A
      (contains_left_of_isAbelianVariety 𝒞 hk A)).property
    (isAlgebraicSpace_baseS 𝒞 _ hk)

variable [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u})]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 _ hk).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u})]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u})]

/-- **Stacks Project, Tag 0CXX.** Let `k` be an algebraically closed field which is not the
algebraic closure of a finite field, let `A` be an abelian variety over `k` with `1 ≤ dim A`, and
let `𝒳 = [Spec(k)/A]` over the big fppf site of `Spec k`. There are an inverse system `R` of
`k`-algebras with a limit cone `cS`, whose transition maps are surjective with locally nilpotent
kernels, and a system `ξ` of objects of `𝒳` lying over the spectra of the levels of `R` (through
the isomorphisms `f`, compatible with the transition maps), together with the cocone `c` of the
base it maps to, whose vertex is the spectrum of the limit (through `fL`, compatible with the legs
and with the structure morphism to `Spec k`), such that `ξ` is not effective over `c` in the sense
of Tag 0CXT.

The condition `1 ≤ dim A` is not in the source, whose statement fails for the zero abelian
variety (`errata.md`, entry of 2026-10-28). The system is the one of the discussion before the
lemma, over the function field `K = k(A)`: `R_n = K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)` and `ξ_n`
glued along the generic point of `A`. The hypothesis on `k` is not used; it is the source's. -/
@[stacks 0CXX "with the condition 1 ≤ dim A, which the source omits: as printed the lemma fails \
for the zero abelian variety (errata.md, 2026-10-28). The system is the source's construction \
over the function field k(A), glued along the generic point of A."]
theorem exists_nonEffectiveSystem_quotientStack_abelianVariety [IsAlgClosed k]
    (_hkinf : ∀ F : Subfield k, Finite F → ¬ Algebra.IsAlgebraic F k)
    (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    ∃ (R : ℕᵒᵖ ⥤ CommAlgCat.{u} k) (cS : Cone R)
      (ξ : ℕ ⥤ (abelianVarietyClassifyingStack 𝒞 hk A).obj)
      (c : Cocone (ξ ⋙ (abelianVarietyClassifyingStack 𝒞 hk A).p))
      (f : ∀ n : ℕ, (schemeOverField k 𝒞 hk).obj
        ((ξ ⋙ (abelianVarietyClassifyingStack 𝒞 hk A).p).obj n) ≅ Spec (.of (R.obj (.op n))))
      (fL : (schemeOverField k 𝒞 hk).obj c.pt ≅ Spec (.of cS.pt)),
      Nonempty (IsLimit cS) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j), Function.Surjective (R.map g).hom) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j),
        (RingHom.ker (R.map g).hom.toRingHom).LocallyNilpotent) ∧
      (∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k 𝒞 hk).map
          ((ξ ⋙ (abelianVarietyClassifyingStack 𝒞 hk A).p).map g) ≫ (f j).hom =
        (f i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map g.op).hom.toRingHom).op) ∧
      (∀ n : ℕ, (schemeOverField k 𝒞 hk).map (c.ι.app n) ≫ fL.hom =
        (f n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cS.π.app (.op n)).hom.toRingHom).op) ∧
      (fL.inv ≫ 𝒞.inclusion.map c.pt.hom =
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cS.pt)).op) ∧
      ¬ IsEffectiveSystem (abelianVarietyClassifyingStack 𝒞 hk A).p ξ c :=
  letI := functionFieldAlgebra A
  by
    have hA := contains_left_of_isAbelianVariety 𝒞 hk A
    have hK : 𝒞.Contains (Spec (.of A.left.functionField)) :=
      BigFppfSite.contains_spec_functionField 𝒞 hA
    have hR := contains_spec_triangleLevel 𝒞 A.left.functionField hK
    have hL := contains_spec_triangleCompletion 𝒞 A.left.functionField hK
    let ξ := triangleSystem A.left.functionField 𝒞 hk hR hA (genericPointOverField A)
    let e := triangleSystemProjectionIso A.left.functionField 𝒞 hk hR hA (genericPointOverField A)
    let cL := triangleLimitCocone A.left.functionField (hk := hk) hR hL
    refine ⟨powQuotientDiagram k (triangleIdeal A.left.functionField),
      adicCompletionCone k (triangleIdeal A.left.functionField), ξ,
      ⟨cL.pt, e.hom ≫ cL.ι⟩,
      fun n => (schemeOverField k 𝒞 hk).mapIso (e.app n), Iso.refl _,
      ⟨isLimitAdicCompletionCone k _⟩, surjective_powQuotientDiagram_map k _,
      locallyNilpotent_ker_powQuotientDiagram_map k _, fun {i j} g => ?_, fun n => ?_, ?_, ?_⟩
    · change (schemeOverField k 𝒞 hk).map _ ≫ (schemeOverField k 𝒞 hk).map (e.hom.app j) =
        (schemeOverField k 𝒞 hk).map (e.hom.app i) ≫ _
      refine ((schemeOverField k 𝒞 hk).map_comp _ _).symm.trans ?_
      refine (congrArg (schemeOverField k 𝒞 hk).map (e.hom.naturality g)).trans ?_
      refine ((schemeOverField k 𝒞 hk).map_comp _ _).trans ?_
      exact congrArg (_ ≫ ·) (toScheme_map_triangleSiteSystem_map _ hR g)
    · exact (Category.comp_id _).trans ((Functor.map_comp _ _ _).trans rfl)
    · refine (Category.id_comp _).trans ?_
      refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
      exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k A.left.functionField
        (triangleCompletion A.left.functionField)).symm
    · exact not_isEffectiveSystem_triangleSystem hA hR hdim _ fun x hx =>
        isOfFinAddOrder_quotientStackTrivialActionClass_of_iso_spec_triangleCompletion
          A hA A.left.functionField x (eqToIso (congrArg (BigFppfOver.objScheme 𝒞 _ hk) hx))

/-- **`[Spec(k)/A]` does not satisfy strong formal effectiveness** (Tag 0CXT), for `k` an
algebraically closed field which is not the algebraic closure of a finite field and `A` an
abelian variety over `k` with `1 ≤ dim A`: the conclusion of
`Deformation.Artin.exists_nonEffectiveSystem_quotientStack_abelianVariety` fed back to
`Deformation.Artin.IsStronglyFormallyEffective`, with the identity of `Spec k` as chart. -/
theorem not_isStronglyFormallyEffective_quotientStack_abelianVariety [IsAlgClosed k]
    (hkinf : ∀ F : Subfield k, Finite F → ¬ Algebra.IsAlgebraic F k)
    (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    ¬ IsStronglyFormallyEffective 𝒞 (Spec (CommRingCat.of k)) hk
      (abelianVarietyClassifyingStack 𝒞 hk A).p
      (Stack.isFiberedInGroupoids_quotientStack _) := by
  obtain ⟨R, cS, ξ, c, f, fL, ⟨hlim⟩, hsurj, hnil, h1, h2, h3, hne⟩ :=
    exists_nonEffectiveSystem_quotientStack_abelianVariety.{w} 𝒞 hk A hkinf hdim
  intro hSFE
  exact hne (hSFE k (𝟙 (Spec (CommRingCat.of k))) R cS hlim hsurj hnil ξ c f fL
    (fun g => h1 g) h2 (h3.trans (Category.comp_id _).symm))

end Stack

end Deformation.Artin

end
