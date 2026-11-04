module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion

/-!
# Approximating morphisms out of an inverse limit by morphisms out of a stage

Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces
over a scheme `S` with affine transition morphisms, small enough for the site, and let `c` be
a limit cone for it whose vertex is again an algebraic space. For a morphism `φ : V ⟶ Z` of
algebraic spaces over `S` which is locally of finite presentation, Stacks 0CP4 says that the
comparison square

```
colim_i Mor(D_i, V) ⟶ Mor(c.pt, V)
        |                   |
        v                   v
colim_i Mor(D_i, Z) ⟶ Mor(c.pt, Z)
```

is cartesian. This file records two consequences of that cartesian square: a morphism `c.pt ⟶ V`
whose composite with `φ` is defined over a stage is itself defined over a stage, and two morphisms
out of a stage which agree over the limit and over `Z` agree after a single transition morphism.
Both are also stated with the cardinality bounds on the index replaced by
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` or by `AlgebraicGeometry.Space.IsSiteSmall`.

For a stage `i` of a preorder, the slice `CategoryTheory.Over (Opposite.op i)` of its opposite has
at most as many objects as the preorder, and all of its morphism types are subsingletons.

## Main results

* `AlgebraicGeometry.cardinal_mk_over_op_le`: a slice of the opposite of a preorder has at most
  as many objects as the preorder.
* `AlgebraicGeometry.cardinal_mk_hom_over_op_lt`: the morphism types of such a slice are below
  the cofinality of the size cutoff of the site.
* `AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving`: a morphism out of the
  limit whose composite with `φ` is defined over a stage is defined over a stage.
* `AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving`: two morphisms out of a
  stage which agree over the limit and over `Z` agree after one transition morphism.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry

/-! ### The slice of the opposite of a preorder -/

section SliceOfPreorder

variable {I : Type u} [Preorder I]

/-- The slice `Over (op i)` of the opposite of a preorder `I` has at most `#I` objects. -/
theorem cardinal_mk_over_op_le (i : I) : #(Over (op i)) ≤ #I := by
  refine Cardinal.mk_le_of_injective (f := fun j : Over (op i) ↦ j.left.unop) ?_
  intro A A' h
  obtain ⟨a, ⟨u⟩, f⟩ := A
  obtain ⟨a', ⟨u'⟩, f'⟩ := A'
  cases u
  cases u'
  obtain rfl : a = a' := Opposite.unop_injective h
  obtain rfl : f = f' := Subsingleton.elim _ _
  rfl

end SliceOfPreorder

/-- The morphism types of the slice `Over (op i)` of the opposite of a preorder have cardinality
below the cofinality of the size cutoff of the big fppf site `B`. -/
theorem cardinal_mk_hom_over_op_lt (B : BigFppfSite.{u}) {I : Type u} [Preorder I] (i : I)
    (j k : Over (op i)) : #(j ⟶ k) < B.cutoff.ord.cof :=
  have : Subsingleton (j ⟶ k) :=
    ⟨fun _ _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _)⟩
  (Cardinal.le_one_iff_subsingleton.2 this).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

namespace Space

/-! ### Descending a morphism out of the limit -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- If the comparison square of `φ` is cartesian, a morphism out of the limit whose composite with
`φ` is defined over a stage is defined over a stage. -/
private theorem exists_stage_map_of_isPullback
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : V ⟶ Z)
    (hp : IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj V ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj V ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight (yoneda.map φ) uliftFunctor.{u + 1, u + 1})))
      (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map φ).app (op c.pt)))
      (colimit.desc (D.op ⋙ yoneda.obj Z ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj Z ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op)))
    (g : c.pt ⟶ V) (i : J) (b : D.obj i ⟶ Z) (hsq : g ≫ φ = c.π.app i ≫ b) :
    ∃ (j : J) (t : D.obj j ⟶ V) (k : J) (a : k ⟶ j) (a' : k ⟶ i),
      c.π.app k ≫ D.map a ≫ t = g ∧ (D.map a ≫ t) ≫ φ = D.map a' ≫ b := by
  let U := uliftFunctor.{u + 1, u + 1}
  let F := yoneda.obj V ⋙ U
  let G := yoneda.obj Z ⋙ U
  let α := Functor.whiskerLeft D.op (Functor.whiskerRight (yoneda.map φ) U)
  let y : colimit (D.op ⋙ G) := colimit.ι (D.op ⋙ G) (op i) ⟨b⟩
  have hw : U.map ((yoneda.map φ).app (op c.pt)) ⟨g⟩ =
      colimit.desc (D.op ⋙ G) (G.mapCocone c.op) y := by
    show ULift.up (g ≫ φ) = (colimit.ι (D.op ⋙ G) (op i) ≫
      colimit.desc (D.op ⋙ G) (G.mapCocone c.op)) ⟨b⟩
    rw [colimit.ι_desc]
    exact congrArg ULift.up hsq
  obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback hp ⟨g⟩ y hw
  obtain ⟨j', t', ht⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (D.op ⋙ F)) z
  have hcol : colimit.ι (D.op ⋙ G) j' (α.app j' t') = colimit.ι (D.op ⋙ G) (op i) ⟨b⟩ :=
    calc colimit.ι (D.op ⋙ G) j' (α.app j' t')
        = colimMap α (colimit.ι (D.op ⋙ F) j' t') := (colimit.ι_map_apply α j' t').symm
      _ = colimMap α z := congrArg (colimMap α) ht
      _ = y := hz₂
      _ = colimit.ι (D.op ⋙ G) (op i) ⟨b⟩ := rfl
  have hlimRep : colimit.desc (D.op ⋙ F) (F.mapCocone c.op)
      (colimit.ι (D.op ⋙ F) j' t') = ⟨g⟩ :=
    (congrArg (colimit.desc (D.op ⋙ F) (F.mapCocone c.op)) ht).trans hz₁
  change (colimit.ι (D.op ⋙ F) j' ≫
    colimit.desc (D.op ⋙ F) (F.mapCocone c.op)) t' = ⟨g⟩ at hlimRep
  rw [colimit.ι_desc] at hlimRep
  change ULift.up (c.π.app j'.unop ≫ t'.down) = ULift.up g at hlimRep
  have hlim : c.π.app j'.unop ≫ t'.down = g := congrArg ULift.down hlimRep
  obtain ⟨k', fa, fa', heq⟩ := (Types.FilteredColimit.colimit_eq_iff (D.op ⋙ G)).mp hcol
  refine ⟨j'.unop, t'.down, k'.unop, fa.unop, fa'.unop, ?_, ?_⟩
  · rwa [← Category.assoc, c.w fa.unop]
  · change ULift.up (D.map fa.unop ≫ t'.down ≫ φ) = ULift.up (D.map fa'.unop ≫ b) at heq
    exact congrArg ULift.down heq

/-- If the comparison square of `φ` is cartesian, two morphisms out of a stage which agree over
the limit and over `Z` agree after a single transition morphism. -/
private theorem exists_stage_eq_of_isPullback
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : V ⟶ Z)
    (hp : IsPullback
      (colimit.desc (D.op ⋙ yoneda.obj V ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj V ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight (yoneda.map φ) uliftFunctor.{u + 1, u + 1})))
      (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map φ).app (op c.pt)))
      (colimit.desc (D.op ⋙ yoneda.obj Z ⋙ uliftFunctor.{u + 1, u + 1})
        ((yoneda.obj Z ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op)))
    (i : J) (r s : D.obj i ⟶ V) (hlim : c.π.app i ≫ r = c.π.app i ≫ s)
    (hbase : r ≫ φ = s ≫ φ) :
    ∃ (k : J) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s := by
  let U := uliftFunctor.{u + 1, u + 1}
  let F := yoneda.obj V ⋙ U
  let G := yoneda.obj Z ⋙ U
  let α := Functor.whiskerLeft D.op (Functor.whiskerRight (yoneda.map φ) U)
  have heq : colimit.ι (D.op ⋙ F) (op i) ⟨r⟩ = colimit.ι (D.op ⋙ F) (op i) ⟨s⟩ := by
    refine Types.ext_of_isPullback hp ?_ ?_
    · show (colimit.ι (D.op ⋙ F) (op i) ≫
          colimit.desc (D.op ⋙ F) (F.mapCocone c.op)) ⟨r⟩ =
        (colimit.ι (D.op ⋙ F) (op i) ≫
          colimit.desc (D.op ⋙ F) (F.mapCocone c.op)) ⟨s⟩
      rw [colimit.ι_desc]
      exact congrArg ULift.up hlim
    · show colimMap α (colimit.ι (D.op ⋙ F) (op i) ⟨r⟩) =
        colimMap α (colimit.ι (D.op ⋙ F) (op i) ⟨s⟩)
      calc colimMap α (colimit.ι (D.op ⋙ F) (op i) ⟨r⟩)
          = colimit.ι (D.op ⋙ G) (op i) (α.app (op i) ⟨r⟩) :=
            colimit.ι_map_apply α (op i) ⟨r⟩
        _ = colimit.ι (D.op ⋙ G) (op i) (α.app (op i) ⟨s⟩) :=
            congrArg (colimit.ι (D.op ⋙ G) (op i)) (congrArg ULift.up hbase)
        _ = colimMap α (colimit.ι (D.op ⋙ F) (op i) ⟨s⟩) :=
            (colimit.ι_map_apply α (op i) ⟨s⟩).symm
  obtain ⟨k, a, hka⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (D.op ⋙ F)) ⟨r⟩ ⟨s⟩).mp heq
  exact ⟨k.unop, a.unop, congrArg ULift.down hka⟩

/-- A morphism `g` out of the inverse limit of a cofiltered system of quasi-compact and
quasi-separated algebraic spaces with affine transition morphisms, into the source of a morphism
`φ` which is locally of finite presentation, is defined over a stage as soon as its composite with
`φ` is: if `g ≫ φ` is the restriction of a morphism `b` out of the stage `i`, then some stage `j`
carries a morphism `t` whose restriction to the limit is `g` and which, after a further transition
morphism, lies over `b`. -/
theorem exists_stage_map_of_relativelyLimitPreserving
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hSize : #J < B.cutoff.ord.cof) (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (g : c.pt ⟶ V) (i : J) (b : D.obj i ⟶ Z) (hsq : g ≫ φ = c.π.app i ≫ b) :
    ∃ (j : J) (t : D.obj j ⟶ V) (k : J) (a : k ⟶ j) (a' : k ⟶ i),
      c.π.app k ≫ D.map a ≫ t = g ∧ (D.map a ≫ t) ≫ φ = D.map a' ≫ b :=
  exists_stage_map_of_isPullback B S hS D c φ
    (qcqsLimitSquare_of_isLocallyOfFinitePresentation B S hS hZ φ hV hZ' hφ
      J D c hSize hHomSize hDalg hDqc hDqs hDaff hc hc') g i b hsq

/-- Two morphisms out of a stage of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, into the source of a morphism `φ` which is
locally of finite presentation, agree after a single transition morphism as soon as they agree over
the limit and after composing with `φ`. -/
theorem exists_stage_eq_of_relativelyLimitPreserving
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hSize : #J < B.cutoff.ord.cof) (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (i : J) (r s : D.obj i ⟶ V) (hlim : c.π.app i ≫ r = c.π.app i ≫ s)
    (hbase : r ≫ φ = s ≫ φ) :
    ∃ (k : J) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s :=
  exists_stage_eq_of_isPullback B S hS D c φ
    (qcqsLimitSquare_of_isLocallyOfFinitePresentation B S hS hZ φ hV hZ' hφ
      J D c hSize hHomSize hDalg hDqc hDqs hDaff hc hc') i r s hlim hbase

/-! ### Systems satisfying the convention of the site, or small for the site -/

/-- A morphism `g` out of the inverse limit of a cofiltered system satisfying
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, into the source of a morphism `φ` which is
locally of finite presentation, is defined over a stage as soon as its composite with `φ` is: if
`g ≫ φ` is the restriction of a morphism `b` out of the stage `i`, then some stage `j` carries a
morphism `t` whose restriction to the limit is `g` and which, after a further transition morphism,
lies over `b`. -/
theorem exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (_hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (g : c.pt ⟶ V) (i : J) (b : D.obj i ⟶ Z) (hsq : g ≫ φ = c.π.app i ≫ b) :
    ∃ (j : J) (t : D.obj j ⟶ V) (k : J) (a : k ⟶ j) (a' : k ⟶ i),
      c.π.app k ≫ D.map a ≫ t = g ∧ (D.map a ≫ t) ≫ φ = D.map a' ≫ b :=
  exists_stage_map_of_isPullback B S hS D c φ
    (isPullback_qcqsLimitSquare_of_isLocallyOfFinitePresentation B S hS hZ φ hV hZ' hφ
      D c hconv hDalg hDqc hDqs hDaff hc) g i b hsq

/-- A morphism `g` out of the inverse limit of a cofiltered system, small for the site, of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms, into the
source of a morphism `φ` which is locally of finite presentation, is defined over a stage as soon
as its composite with `φ` is: if `g ≫ φ` is the restriction of a morphism `b` out of the stage `i`,
then some stage `j` carries a morphism `t` whose restriction to the limit is `g` and which, after a
further transition morphism, lies over `b`. -/
theorem exists_stage_map_of_relativelyLimitPreserving_of_isSiteSmall
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hb : IsSiteSmall B S hS D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (g : c.pt ⟶ V) (i : J) (b : D.obj i ⟶ Z) (hsq : g ≫ φ = c.π.app i ≫ b) :
    ∃ (j : J) (t : D.obj j ⟶ V) (k : J) (a : k ⟶ j) (a' : k ⟶ i),
      c.π.app k ≫ D.map a ≫ t = g ∧ (D.map a ≫ t) ≫ φ = D.map a' ≫ b :=
  exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ D c hc
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hDalg hDqc hDqs hDaff hc' hV hZ' φ hφ g i
        b hsq

/-- Two morphisms out of a stage of a cofiltered system satisfying
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, into the source of a morphism `φ` which is
locally of finite presentation, agree after a single transition morphism as soon as they agree over
the limit and after composing with `φ`. -/
theorem exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (_hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (i : J) (r s : D.obj i ⟶ V) (hlim : c.π.app i ≫ r = c.π.app i ≫ s)
    (hbase : r ≫ φ = s ≫ φ) :
    ∃ (k : J) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s :=
  exists_stage_eq_of_isPullback B S hS D c φ
    (isPullback_qcqsLimitSquare_of_isLocallyOfFinitePresentation B S hS hZ φ hV hZ' hφ
      D c hconv hDalg hDqc hDqs hDaff hc) i r s hlim hbase

/-- Two morphisms out of a stage of a cofiltered system, small for the site, of quasi-compact and
quasi-separated algebraic spaces with affine transition morphisms, into the source of a morphism
`φ` which is locally of finite presentation, agree after a single transition morphism as soon as
they agree over the limit and after composing with `φ`. -/
theorem exists_stage_eq_of_relativelyLimitPreserving_of_isSiteSmall
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hb : IsSiteSmall B S hS D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (i : J) (r s : D.obj i ⟶ V) (hlim : c.π.app i ≫ r = c.π.app i ≫ s)
    (hbase : r ≫ φ = s ≫ φ) :
    ∃ (k : J) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s :=
  exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ D c hc
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hDalg hDqc hDqs hDaff hc' hV hZ' φ hφ i r
        s hlim hbase

end Space

end AlgebraicGeometry

end
