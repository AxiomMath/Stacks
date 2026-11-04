module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# The stalk of the sheaf associated to a graded module

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ` and let `M` be a
`ℤ`-graded `S`-module with grading `𝒨`. At a point `x` of `Proj(S)`, corresponding to a
homogeneous prime `p` not containing the irrelevant ideal, the stalk of the associated sheaf
`M̃` is canonically the degree-zero part `M₍p₎` of the localization of `M` at `p`.

The identification is `S₍p₎`-linear for the canonical identification
`AlgebraicGeometry.Proj.stalkIso'` of the stalk of the structure sheaf with `S₍p₎`, and it
sends the germ of a section to the value of that section at `x`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt`: the degree-zero
  part of the localization of `M` at the homogeneous prime of a point of `Proj(S)`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk`: the stalk
  of `M̃`, formed as a colimit over the open neighbourhoods of the point.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafGerm`: the germ at
  the point of a section of `M̃` over an open neighbourhood.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv`: the
  canonical additive identification of the stalk with `M₍p₎`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkLinearEquiv`:
  the same identification, as a linear equivalence over the structure-sheaf stalk.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv_germ`:
  the identification sends the germ of a section to the value of the section at the point.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv_germ_smul`:
  the identification is compatible with the action of germs of the structure sheaf.

## Implementation notes

The source states the identification as an equality of modules. The degree-zero part is the
`S₍p₎`-submodule of `LocalizedModule p.primeCompl M` spanned by the fractions `m / s` with
`m` and `s` homogeneous of the same degree.

The stalk is formed directly as a colimit of the underlying presheaf of abelian groups
rather than through `TopCat.Presheaf.stalk` on the presheaf of modules: the latter ties the
universe of the space to the universe of the target category, whereas the associated sheaf is
a `SheafOfModules.{max u v}` over a space in `Type u`. Surjectivity of the evaluation map
uses that every element of the degree-zero part is an integer combination of fractions
`m / s`, each of which is the value at `x` of a section over the standard open `D₊(sf)` for a
homogeneous `f` of positive degree outside `p`; injectivity uses that two germs with the same
value at `x` agree on a smaller standard open.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- The homogeneous ideal of a point of `Proj(S)` is prime as an ideal of `S`. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The homogeneous degree-zero part of the localization of `M` at a point of `Proj(S)`:
the `S₍p₎`-submodule spanned by the fractions `m / s` with `m` and `s` homogeneous of the
same degree. -/
noncomputable def degreeZeroModuleAt (x : ProjectiveSpectrum.top 𝒮) :
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    Submodule (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) := by
  letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  exact Submodule.span (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    {z | ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
      m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s}

/-- The stalk of the associated module sheaf at a point, formed as a colimit of the
underlying presheaf of abelian groups so that the universe of the module is independent of
the universe of the space. -/
noncomputable def associatedModuleSheafStalk (x : ProjectiveSpectrum.top 𝒮) :
    AddCommGrpCat.{max u v} :=
  CategoryTheory.Limits.colimit
    ((OpenNhds.inclusion x).op ⋙ (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf)

/-- The germ at `x` of a section of the associated module sheaf over an open neighbourhood
of `x`. -/
noncomputable def associatedModuleSheafGerm
    (x : ProjectiveSpectrum.top 𝒮) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (hx : x ∈ U) (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    associatedModuleSheafStalk 𝒮 𝒨 x :=
  CategoryTheory.Limits.colimit.ι
    ((OpenNhds.inclusion x).op ⋙ (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf)
    (op ⟨U, hx⟩) s

/-- Evaluation at `x` of the sections over the open neighbourhoods of `x`, as a cocone with
vertex the degree-zero part of the localization at `x`. The local-fraction condition is
exactly what puts the value at `x` into the degree-zero part. -/
noncomputable def associatedModuleSheafStalkEvalCocone
    (x : ProjectiveSpectrum.top 𝒮) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf) := by
  letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  refine {
    pt := AddCommGrpCat.of (degreeZeroModuleAt 𝒮 𝒨 x)
    ι := {
      app := fun U => AddCommGrpCat.ofHom {
        toFun := fun a => ⟨a.1 ⟨x, U.unop.2⟩, by
          have ha : (ProjectiveSpectrum.Proj.locallyModuleFraction 𝒮 𝒨).pred a.1 := a.property
          obtain ⟨V, hxV, iV, d, m, s, hm, hs, hn, hval⟩ := ha ⟨x, U.unop.2⟩
          have heval : a.1 ⟨x, U.unop.2⟩ =
              LocalizedModule.mk m ⟨s, hn ⟨x, hxV⟩⟩ := by
            simpa using hval ⟨x, hxV⟩
          rw [heval]
          exact Submodule.subset_span ⟨d, m, ⟨s, hn ⟨x, hxV⟩⟩, hm, hs, rfl⟩⟩
        map_zero' := rfl
        map_add' _ _ := rfl
      }
      naturality := by
        intro i j f
        ext a
        rfl
    }
  }

/-- Evaluation at `x`, as an additive map out of the stalk. -/
noncomputable def associatedModuleSheafStalkEval
    (x : ProjectiveSpectrum.top 𝒮) :
    associatedModuleSheafStalk 𝒮 𝒨 x →+ degreeZeroModuleAt 𝒮 𝒨 x :=
  (Limits.colimit.desc
    ((OpenNhds.inclusion x).op ⋙ (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf)
    (associatedModuleSheafStalkEvalCocone 𝒮 𝒨 x)).hom

omit [Decomposition 𝒨] in
/-- Evaluation of a germ is the value of a representing section at the point. -/
theorem associatedModuleSheafStalkEval_germ
    (x : ProjectiveSpectrum.top 𝒮) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (hx : x ∈ U) (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    ((associatedModuleSheafStalkEval 𝒮 𝒨 x
      (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) : degreeZeroModuleAt 𝒮 𝒨 x) :
      ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) =
      ((ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv 𝒮 𝒨 U).toFun s).1 ⟨x, hx⟩ := by
  have h := congrArg (fun f => f s)
    (Limits.colimit.ι_desc (associatedModuleSheafStalkEvalCocone 𝒮 𝒨 x) (op ⟨U, hx⟩))
  change associatedModuleSheafStalkEval 𝒮 𝒨 x
      (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) = _ at h
  exact congrArg Subtype.val h

omit [Decomposition 𝒨] in
/-- Every element of the stalk is the germ of a section over some open neighbourhood: the
colimit computing the stalk is filtered, so its underlying type is the quotient of the
disjoint union of the section groups. -/
theorem associatedModuleSheafStalk_exists_germ
    (x : ProjectiveSpectrum.top 𝒮) (z : associatedModuleSheafStalk 𝒮 𝒨 x) :
    ∃ (U : Opens (ProjectiveSpectrum.top 𝒮)) (hx : x ∈ U)
      (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)),
      associatedModuleSheafGerm 𝒮 𝒨 x U hx s = z := by
  let F := (OpenNhds.inclusion x).op ⋙
    (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf
  let c := AddCommGrpCat.FilteredColimits.colimitCocone F
  let hc := AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit F
  let eHom : Limits.colimit F ⟶ c.pt := Limits.colimit.desc F c
  let invHom : c.pt ⟶ Limits.colimit F := hc.desc (Limits.colimit.cocone F)
  have hcomp : eHom ≫ invHom = 𝟙 (Limits.colimit F) := by
    apply Limits.colimit.hom_ext
    intro j
    calc
      Limits.colimit.ι F j ≫ eHom ≫ invHom = c.ι.app j ≫ invHom := by
        rw [← Category.assoc, Limits.colimit.ι_desc]
      _ = (Limits.colimit.cocone F).ι.app j := hc.fac (Limits.colimit.cocone F) j
      _ = Limits.colimit.ι F j := rfl
  let F' := F ⋙ forget₂ AddCommGrpCat AddGrpCat ⋙ forget₂ AddGrpCat AddMonCat
  let hzM : AddMonCat.FilteredColimits.M F' := eHom z
  obtain ⟨i, s, hs⟩ := AddMonCat.FilteredColimits.M.mk_surjective F' hzM
  have hleft : Function.LeftInverse invHom.hom eHom.hom := by
    intro y
    simpa using congrArg (fun f => f y) hcomp
  have hz : Limits.colimit.ι F i s = z := by
    apply hleft.injective
    calc
      eHom (Limits.colimit.ι F i s) = c.ι.app i s := by
        show (Limits.colimit.ι F i ≫ eHom) s = c.ι.app i s
        rw [Limits.colimit.ι_desc]
      _ = eHom z := hs
  cases i with
  | op i =>
    obtain ⟨U, hx⟩ := i
    exact ⟨U, hx, s,
      by simpa [F, associatedModuleSheafStalk, associatedModuleSheafGerm] using hz⟩

omit [Decomposition 𝒨] in
/-- The germ of a restriction of a section is the germ of the section. -/
theorem associatedModuleSheafGerm_res (x : ProjectiveSpectrum.top 𝒮)
    {U V : Opens (ProjectiveSpectrum.top 𝒮)} (i : V ⟶ U) (hx : x ∈ V)
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    associatedModuleSheafGerm 𝒮 𝒨 x V hx
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf.map i.op s) =
      associatedModuleSheafGerm 𝒮 𝒨 x U (i.le hx) s :=
  Limits.colimit.w_apply ((OpenNhds.inclusion x).op ⋙
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf)
    (homOfLE i.le : (⟨V, hx⟩ : OpenNhds x) ⟶ ⟨U, i.le hx⟩).op s

omit [Decomposition 𝒨] in
/-- Two sections with the same value at `x` have the same germ at `x`: their homogeneous
fractions are proportional near `x`, hence the sections agree on a smaller standard open. -/
theorem associatedModuleSheafGerm_eq_of_apply_eq (x : ProjectiveSpectrum.top 𝒮)
    {U V : Opens (ProjectiveSpectrum.top 𝒮)} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U))
    (t : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op V))
    (hpoint : s.1 ⟨x, hxU⟩ = t.1 ⟨x, hxV⟩) :
    associatedModuleSheafGerm 𝒮 𝒨 x U hxU s = associatedModuleSheafGerm 𝒮 𝒨 x V hxV t := by
  let F := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf
  have Hs : (ProjectiveSpectrum.Proj.locallyModuleFraction 𝒮 𝒨).pred s.1 := s.property
  have Ht : (ProjectiveSpectrum.Proj.locallyModuleFraction 𝒮 𝒨).pred t.1 := t.property
  obtain ⟨Us, hxs, is, ds, ms, ss, hms, hss, hns, hvs⟩ := Hs ⟨x, hxU⟩
  obtain ⟨Ut, hxt, it, dt, mt, st, hmt, hst, hnt, hvt⟩ := Ht ⟨x, hxV⟩
  have hvsx : s.1 ⟨x, hxU⟩ = LocalizedModule.mk ms ⟨ss, hns ⟨x, hxs⟩⟩ := by
    simpa using hvs ⟨x, hxs⟩
  have hvtpoint := hvt ⟨x, hxt⟩
  have hp : t.1 (it ⟨x, hxt⟩) = t.1 ⟨x, hxV⟩ := rfl
  have hfrac := by
    simpa only [hvsx, ← hp, hvtpoint] using hpoint
  obtain ⟨q, hcross⟩ := LocalizedModule.mk_eq.mp hfrac
  let W := Us ⊓ Ut ⊓ ProjectiveSpectrum.basicOpen 𝒮 (q : S)
  have hxW : x ∈ W :=
    ⟨⟨hxs, hxt⟩, (ProjectiveSpectrum.mem_basicOpen 𝒮 (q : S) x).2 q.2⟩
  let iWs : W ⟶ Us := homOfLE (show W ≤ Us from inf_le_left.trans inf_le_left)
  let iWt : W ⟶ Ut := homOfLE (show W ≤ Ut from inf_le_left.trans inf_le_right)
  let iWU : W ⟶ U := iWs ≫ is
  let iWV : W ⟶ V := iWt ≫ it
  have hrestr : F.map iWU.op s = F.map iWV.op t := by
    apply Subtype.ext
    funext y
    show s.1 (iWU y) = t.1 (iWV y)
    have hvsy : s.1 (iWU y) = LocalizedModule.mk ms ⟨ss, hns (iWs y)⟩ := by
      simpa [iWU, iWs] using hvs (iWs y)
    have hvty : t.1 (iWV y) = LocalizedModule.mk mt ⟨st, hnt (iWt y)⟩ := by
      simpa [iWV, iWt] using hvt (iWt y)
    rw [hvsy, hvty]
    exact LocalizedModule.mk_eq.mpr
      ⟨⟨(q : S), (ProjectiveSpectrum.mem_basicOpen 𝒮 (q : S) y.1).1 y.2.2⟩, hcross⟩
  calc
    associatedModuleSheafGerm 𝒮 𝒨 x U hxU s =
        associatedModuleSheafGerm 𝒮 𝒨 x W hxW (F.map iWU.op s) :=
      (associatedModuleSheafGerm_res 𝒮 𝒨 x iWU hxW s).symm
    _ = associatedModuleSheafGerm 𝒮 𝒨 x W hxW (F.map iWV.op t) :=
      congrArg (associatedModuleSheafGerm 𝒮 𝒨 x W hxW) hrestr
    _ = associatedModuleSheafGerm 𝒮 𝒨 x V hxV t :=
      associatedModuleSheafGerm_res 𝒮 𝒨 x iWV hxW t

omit [Decomposition 𝒨] in
/-- Evaluation at the point is injective on the stalk: two sections with the same value at
`x` have proportional homogeneous fractions near `x`, hence agree on a smaller standard
open. -/
theorem associatedModuleSheafStalkEval_injective
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Injective (associatedModuleSheafStalkEval 𝒮 𝒨 x) := by
  intro a b hab
  obtain ⟨U, hxU, s, rfl⟩ := associatedModuleSheafStalk_exists_germ 𝒮 𝒨 x a
  obtain ⟨V, hxV, t, rfl⟩ := associatedModuleSheafStalk_exists_germ 𝒮 𝒨 x b
  refine associatedModuleSheafGerm_eq_of_apply_eq 𝒮 𝒨 x hxU hxV s t ?_
  have heval :
      (((associatedModuleSheafStalkEval 𝒮 𝒨 x)
        (associatedModuleSheafGerm 𝒮 𝒨 x U hxU s) : degreeZeroModuleAt 𝒮 𝒨 x) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) =
      (((associatedModuleSheafStalkEval 𝒮 𝒨 x)
        (associatedModuleSheafGerm 𝒮 𝒨 x V hxV t) : degreeZeroModuleAt 𝒮 𝒨 x) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    congrArg Subtype.val hab
  rwa [associatedModuleSheafStalkEval_germ 𝒮 𝒨 x U hxU s,
    associatedModuleSheafStalkEval_germ 𝒮 𝒨 x V hxV t] at heval

/-- Multiplying a homogeneous element of degree `d` by a homogeneous ring element of degree `i`
gives a homogeneous element of degree `i + d`, with degrees as natural numbers. -/
private theorem smul_mem_graded_natCast {S M σ τ : Type*} [SetLike σ S] [SetLike τ M] [SMul S M]
    {𝒮 : ℕ → σ} {𝒨 : ℤ → τ} [SetLike.GradedSMul 𝒮 𝒨] {i d : ℕ} {a : S} {m : M}
    (ha : a ∈ 𝒮 i) (hm : m ∈ 𝒨 (d : ℤ)) : a • m ∈ 𝒨 ((i + d : ℕ) : ℤ) := by
  simpa only [Nat.cast_add] using
    (show a • m ∈ 𝒨 ((i : ℤ) + d) from SetLike.GradedSMul.smul_mem ha hm)

omit [Decomposition 𝒨] [AddSubgroupClass τ M] in
/-- The additive subgroup generated by the fractions `m / s`, with `m` and `s` homogeneous of
the same degree, is stable under the action of `S₍p₎`. -/
theorem smul_mem_closure_homogeneousFractions (x : ProjectiveSpectrum.top 𝒮)
    (r : HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x}
    (hz : z ∈ AddSubgroup.closure
      {z | ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
        m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s}) :
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    r • z ∈ AddSubgroup.closure
      {z | ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
        m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s} := by
  let : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨d, m, s, hm, hs, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective r
    have hnum := smul_mem_graded_natCast c.num.2 hm
    have hden : (c.den : S) * (s : S) ∈ 𝒮 (c.deg + d) :=
      SetLike.mul_mem_graded c.den.2 hs
    have hcden : (c.den : S) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := c.den_mem
    have hmul : HomogeneousLocalization.mk c • LocalizedModule.mk m s =
        LocalizedModule.mk ((c.num : S) • m)
          ⟨(c.den : S) * (s : S),
            x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hcden s.2⟩ := by
      show HomogeneousLocalization.val (HomogeneousLocalization.mk c) •
          LocalizedModule.mk m s = _
      rw [HomogeneousLocalization.val_mk]
      exact LocalizedModule.mk_smul_mk _ _ _ _
    exact AddSubgroup.subset_closure ⟨c.deg + d, (c.num : S) • m,
      ⟨(c.den : S) * (s : S),
        x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hcden s.2⟩,
      hnum, hden, hmul⟩
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
    simpa only [smul_add] using add_mem ih₁ ih₂
  | neg z hz ih => simpa only [smul_neg] using neg_mem ih

omit [Decomposition 𝒨] in
/-- A fraction `m / s`, with `m` and `s` homogeneous of the same degree `d`, is the value at
`x` of a germ: that of the section `fm / sf` over `D₊(sf)`, for `f` homogeneous of positive
degree outside the prime of `x`. -/
theorem exists_associatedModuleSheafStalkEval_eq_mk (x : ProjectiveSpectrum.top 𝒮)
    {d : ℕ} {m : M} {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hm : m ∈ 𝒨 (d : ℤ)) (hs : (s : S) ∈ 𝒮 d) :
    ∃ a, ((associatedModuleSheafStalkEval 𝒮 𝒨 x a : degreeZeroModuleAt 𝒮 𝒨 x) :
      ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) = LocalizedModule.mk m s := by
  obtain ⟨e, he, f, hf, hfx⟩ : ∃ (e : ℕ) (_ : 0 < e) (f : S), f ∈ 𝒮 e ∧
      f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒮).mpr h)
  let g : S := (s : S) * f
  have hg : g ∈ 𝒮 (d + e) := SetLike.mul_mem_graded hs hf
  have hgm : f • m ∈ 𝒨 ((d + e : ℕ) : ℤ) := by
    simpa only [add_comm] using smul_mem_graded_natCast hf hm
  have hxg : x ∈ ProjectiveSpectrum.basicOpen 𝒮 g :=
    (ProjectiveSpectrum.mem_basicOpen 𝒮 g x).2
      (x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem s.2 hfx)
  let aFun : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 g,
      ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 y.1 :=
    fun y => LocalizedModule.mk (f • m) ⟨g, y.2⟩
  have haFun : (ProjectiveSpectrum.Proj.locallyModuleFraction 𝒮 𝒨).pred aFun := fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒮 g, y.2, 𝟙 _, d + e, f • m, g, hgm, hg, fun z => z.2,
      fun _ => rfl⟩
  let a : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (.op (ProjectiveSpectrum.basicOpen 𝒮 g)) :=
    ⟨aFun, haFun⟩
  refine ⟨associatedModuleSheafGerm 𝒮 𝒨 x (ProjectiveSpectrum.basicOpen 𝒮 g) hxg a, ?_⟩
  rw [associatedModuleSheafStalkEval_germ 𝒮 𝒨 x
    (ProjectiveSpectrum.basicOpen 𝒮 g) hxg a]
  show aFun ⟨x, hxg⟩ = _
  exact LocalizedModule.mk_eq.mpr ⟨1, by simp only [smul_smul, Submonoid.smul_def, g]⟩

omit [Decomposition 𝒨] in
/-- Evaluation at the point is surjective onto the degree-zero part: a fraction `m / s` with
`m` and `s` homogeneous of degree `d` is the value at `x` of the section `fm / sf` over
`D₊(sf)`, for `f` homogeneous of positive degree outside the prime of `x`. -/
theorem associatedModuleSheafStalkEval_surjective
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Surjective (associatedModuleSheafStalkEval 𝒮 𝒨 x) := by
  let : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  let H : AddSubgroup (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    AddSubgroup.closure {z | ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
      m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s}
  let P : Submodule (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) := {
    carrier := H
    zero_mem' := H.zero_mem
    add_mem' := H.add_mem
    smul_mem' := fun r _ hz => smul_mem_closure_homogeneousFractions 𝒮 𝒨 x r hz
  }
  have hle : degreeZeroModuleAt 𝒮 𝒨 x ≤ P :=
    Submodule.span_le.2 fun _ hz => AddSubgroup.subset_closure hz
  have hHsurj : ∀ z : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x, z ∈ H →
      ∃ a, associatedModuleSheafStalkEval 𝒮 𝒨 x a = z := by
    intro z hzP
    induction hzP using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨d, m, s, hm, hs, rfl⟩ := hz
      exact exists_associatedModuleSheafStalkEval_eq_mk 𝒮 𝒨 x hm hs
    | zero => exact ⟨0, by simp⟩
    | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
      obtain ⟨a, ha⟩ := ih₁
      obtain ⟨b, hb⟩ := ih₂
      exact ⟨a + b, by simp [ha, hb]⟩
    | neg z hz ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨-a, by simp [ha]⟩
  intro z
  obtain ⟨a, ha⟩ := hHsurj z (hle z.property)
  exact ⟨a, Subtype.ext ha⟩

/-- The canonical identification of the stalk of the sheaf associated to `M` with the
degree-zero localization of `M` at a point of `Proj(S)`. -/
@[ega "II 2.5.5"]
noncomputable def associatedModuleSheafStalkEquiv
    (x : ProjectiveSpectrum.top 𝒮) :
    (associatedModuleSheafStalk 𝒮 𝒨 x) ≃+
      degreeZeroModuleAt 𝒮 𝒨 x :=
  AddEquiv.ofBijective (associatedModuleSheafStalkEval 𝒮 𝒨 x)
    ⟨associatedModuleSheafStalkEval_injective 𝒮 𝒨 x,
      associatedModuleSheafStalkEval_surjective 𝒮 𝒨 x⟩

/-- The action of the structure-sheaf stalk on the stalk of the associated module sheaf,
transported from the degree-zero prime localization of the module. -/
noncomputable instance associatedModuleSheafStalkModule
    (x : ProjectiveSpectrum.top 𝒮) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
      (associatedModuleSheafStalk 𝒮 𝒨 x) := by
  letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (associatedModuleSheafStalk 𝒮 𝒨 x) :=
    (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).module _
  exact Module.compHom _ (Proj.stalkIso' 𝒮 x).toRingHom

/-- The canonical `S₍p₎`-linear identification of the stalk of `M̃` with the degree-zero
localization at `p`, taken through the structure-sheaf stalk isomorphism. -/
noncomputable def associatedModuleSheafStalkLinearEquiv
    (x : ProjectiveSpectrum.top 𝒮) :
    letI : Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
        (degreeZeroModuleAt 𝒮 𝒨 x) :=
      Module.compHom _ (Proj.stalkIso' 𝒮 x).toRingHom
    (associatedModuleSheafStalk 𝒮 𝒨 x) ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
      degreeZeroModuleAt 𝒮 𝒨 x := by
  letI : Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
      (degreeZeroModuleAt 𝒮 𝒨 x) :=
    Module.compHom _ (Proj.stalkIso' 𝒮 x).toRingHom
  exact { associatedModuleSheafStalkEquiv 𝒮 𝒨 x with
    map_smul' := by
      intro r m
      simp only [RingHom.id_apply]
      change (associatedModuleSheafStalkEquiv 𝒮 𝒨 x)
        ((associatedModuleSheafStalkEquiv 𝒮 𝒨 x).symm
          ((Proj.stalkIso' 𝒮 x r) • (associatedModuleSheafStalkEquiv 𝒮 𝒨 x m))) =
        (Proj.stalkIso' 𝒮 x r) • (associatedModuleSheafStalkEquiv 𝒮 𝒨 x m)
      simp }

omit [Decomposition 𝒨] in
/-- The stalk identification sends a germ to the value of its section at the point. -/
theorem associatedModuleSheafStalkEquiv_germ
    (x : ProjectiveSpectrum.top 𝒮) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (hx : x ∈ U) (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    (((associatedModuleSheafStalkEquiv 𝒮 𝒨 x).toFun
      (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) :
        degreeZeroModuleAt 𝒮 𝒨 x) : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) =
      ((ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv 𝒮 𝒨 U).toFun s).1 ⟨x, hx⟩ :=
  associatedModuleSheafStalkEval_germ 𝒮 𝒨 x U hx s

omit [Decomposition 𝒨] in
/-- The stalk identification respects scalar multiplication by germs of sections of the
structure sheaf, through the canonical ring-stalk identification. -/
theorem associatedModuleSheafStalkEquiv_germ_smul
    (x : ProjectiveSpectrum.top 𝒮) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (hx : x ∈ U)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U))
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    associatedModuleSheafStalkEquiv 𝒮 𝒨 x
      (associatedModuleSheafGerm 𝒮 𝒨 x U hx (r • s)) =
      (Proj.stalkIso' 𝒮 x
          ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.germ U x hx r)) •
        associatedModuleSheafStalkEquiv 𝒮 𝒨 x
          (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) := by
  let : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  apply Subtype.ext
  show (((associatedModuleSheafStalkEquiv 𝒮 𝒨 x).toFun
      (associatedModuleSheafGerm 𝒮 𝒨 x U hx (r • s)) :
        degreeZeroModuleAt 𝒮 𝒨 x) : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) =
    ((Proj.stalkIso' 𝒮 x
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.germ U x hx r)) •
      ((associatedModuleSheafStalkEquiv 𝒮 𝒨 x).toFun
        (associatedModuleSheafGerm 𝒮 𝒨 x U hx s) :
          degreeZeroModuleAt 𝒮 𝒨 x) : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x)
  rw [associatedModuleSheafStalkEquiv_germ 𝒮 𝒨 x U hx (r • s),
    associatedModuleSheafStalkEquiv_germ 𝒮 𝒨 x U hx s,
    Proj.stalkIso'_germ]
  rfl

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections
