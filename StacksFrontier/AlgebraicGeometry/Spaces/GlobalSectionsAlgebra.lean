module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.RingTheory.LocalRing.IdempotentElem

/-!
# Global functions of an algebraic space: the base algebra, and the componentwise splitting

The global regular functions of a presheaf `F` on the big fppf site of `S` are the compatible
families of functions on its étale charts, that is the sections of the structure presheaf of
the small étale site.  Two structures on them are built here, both of them ingredients of
Tag 0DMY.

First, when the base is the spectrum of a ring `A` they form an `A`-algebra: a scalar `a` is
sent to the family of its pullbacks along the structure morphisms of the charts, which is a
compatible family because every morphism of charts is a morphism over the base.

Second, once the points of `F` carry a topology, the global functions map to the product,
over the connected components of the point space, of the functions on those charts whose
whole image lies in one component.  When each component is open — so that each chart splits
as a disjoint union of the parts lying over each component — this map is a bijection, and the
product decomposition of Tag 0DMY follows from it.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctions` is the ring of global regular functions, the
  sections of the structure presheaf of the small étale site.
* `AlgebraicGeometry.Space.baseToGlobalFunctions` is the canonical ring homomorphism from the
  base ring to the global functions, and
  `AlgebraicGeometry.Space.globalFunctionsAlgebra` the algebra structure it induces.
* `AlgebraicGeometry.Space.chartOpenRestriction` restricts an étale chart to an open
  subscheme of its source.
* `AlgebraicGeometry.Space.componentChart` is the full subsite of charts lying over one
  connected component, `AlgebraicGeometry.Space.componentFunctions` its ring of functions,
  and `AlgebraicGeometry.Space.globalFunctionsRestriction` the simultaneous restriction of
  global functions to all of them.
* `AlgebraicGeometry.Space.ComponentwiseArtinianFactorization` is the decomposition asserted
  by Tag 0DMY, with the equivalence pinned to be that restriction.
* `AlgebraicGeometry.Space.sectionSupport` is the set of points at which a global function
  does not vanish.

## Main results

* `AlgebraicGeometry.Space.baseToGlobalFunctions_val_apply` computes the value of a scalar at
  a chart: it is the pullback of the constant along the chart's structure morphism.
* `AlgebraicGeometry.Space.bijective_globalFunctionsRestriction_of_cover`: restriction to the
  components is bijective as soon as the components cut each chart into disjoint opens.
* `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization`: the componentwise
  Artinian factorization exists for an algebraic space over a field with finitely many
  connected components and an Artinian ring of global functions.
* `CategoryTheory.Functor.bijective_pi_sectionsPrecomp`: sections of a presheaf of types are
  the product of the sections over a locally cofinal family of full subcategories.
* `AlgebraicGeometry.Scheme.bijective_pi_appTop_of_disjoint_cover`: global sections of a
  scheme are the product of the sections over a pairwise disjoint open cover.
* `AlgebraicGeometry.Space.mem_sectionSupport_iff`: the support of a global function, the set
  of points where it does not vanish, is detected on any one chart through that point.
* `AlgebraicGeometry.Space.componentRestriction_eq_zero_or_one`: an idempotent global
  function restricts to `0` or to `1` on each connected component.
* `IsLocalRing.of_isArtinianRing_of_forall_isIdempotentElem`: an Artinian ring with only the
  trivial idempotents is local.

## Implementation notes

The ring structure is `RingCat.sectionsSubring` transported to the commutative setting, as
there is no unconditional `CommRing` instance on the sections of a functor into
`CommRingCat`: Mathlib's `CommRingCat.limitCommRing` is stated only under a smallness
hypothesis on the sections, which fails here because the small étale site of a `Scheme.{u}`
lives in `Type (u + 1)`.

`AlgebraicGeometry.Space.baseToGlobalFunctions` has the same body as
`AlgebraicGeometry.Space.baseRingHom`, but not the same type, and neither subsumes the other.
`baseRingHom` lands in `Stacks.Cohomology.SiteModules.GlobalSectionRing` of the ring sheaf of
the small étale *ringed* site, so it takes the algebraicity hypothesis on `F` that building
that ringed site needs; the global functions themselves need no such hypothesis, and the
algebra structure is wanted on them for an arbitrary presheaf.  The two carriers are the same
subring of `∀ U, Γ(U, 𝒪_U)` whenever both are defined, so the homomorphisms agree, but
stating that needs the ringed site in scope and is therefore not done here.

The topology on the points is an instance argument of everything that mentions connected
components, rather than a fixed choice.  The results that genuinely need the topology of
Tag 03BX are confined to the sections where `AlgebraicGeometry.Space.pointTopology` — the
constructive one, which needs no algebraicity hypothesis — is a local instance.  So the
decomposition applies to any topology on the points for which the components are open.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace IsLocalRing

/-- An Artinian ring whose only idempotents are `0` and `1` is local. -/
theorem of_isArtinianRing_of_forall_isIdempotentElem (R : Type*) [CommRing R] [Nontrivial R]
    [IsArtinianRing R] (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing R := by
  classical
  obtain ⟨p, hp⟩ := Ideal.exists_maximal R
  have : p.IsPrime := hp.isPrime
  refine IsLocalRing.of_unique_max_ideal ⟨p, hp, fun q hq => ?_⟩
  by_contra hne
  obtain ⟨e, hnotp, he, hother⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne p
  rcases h e he with hzero | hone
  · exact hnotp (hzero ▸ p.zero_mem)
  · exact hq.ne_top (q.eq_top_iff_one.mpr (hone ▸ hother q hq.isPrime hne))

end IsLocalRing

namespace CategoryTheory.Functor

/-- Sections of a presheaf of types are the product of the sections of its restrictions to a
family of full subcategories, provided the family is *locally cofinal* in the following
sense: every object `U` carries, for each index `i`, a morphism `v U i : V U i ⟶ U` out of an
object with property `P i` through which every morphism into `U` from an object with property
`P i` factors, and the sections over `U` are freely determined by their restrictions along
the `v U i`. -/
theorem bijective_pi_sectionsPrecomp {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*) {I : Type*}
    (P : I → ObjectProperty C) (V : C → I → C) (v : ∀ U i, V U i ⟶ U)
    (hV : ∀ U i, P i (V U i))
    (hfac : ∀ {U W} i, P i W → ∀ g : W ⟶ U, ∃ l : W ⟶ V U i, l ≫ v U i = g)
    (hbij : ∀ U, Function.Bijective
      (fun s : F.obj (op U) => fun i => F.map (v U i).op s)) :
    Function.Bijective (fun s : F.sections => fun i => (P i).ι.op.sectionsPrecomp s) := by
  classical
  constructor
  · intro s t h
    apply Subtype.ext
    funext U
    apply (hbij U.unop).injective
    funext i
    have hi := congrArg (fun z => (z i).val (op ⟨V U.unop i, hV U.unop i⟩)) h
    exact (s.property (v U.unop i).op).trans (hi.trans (t.property (v U.unop i).op).symm)
  · intro s
    let t (U : Cᵒᵖ) : F.obj U :=
      ((hbij U.unop).surjective
        (fun i => (s i).val (op ⟨V U.unop i, hV U.unop i⟩))).choose
    have ht (U : C) (i : I) :
        F.map (v U i).op (t (op U)) = (s i).val (op ⟨V U i, hV U i⟩) :=
      congrFun ((hbij U).surjective _).choose_spec i
    have hn {U W : C} (i : I) (hW : P i W) (g : W ⟶ U) :
        F.map g.op (t (op U)) = (s i).val (op ⟨W, hW⟩) := by
      obtain ⟨l, hl⟩ := hfac i hW g
      rw [← hl, op_comp, F.map_comp, types_comp_apply, ht]
      exact (s i).property ((P i).homMk (X := ⟨W, hW⟩) (Y := ⟨V U i, hV U i⟩) l).op
    refine ⟨⟨t, ?_⟩, ?_⟩
    · intro U W g
      apply (hbij W.unop).injective
      funext i
      show F.map (v W.unop i).op (F.map g (t U)) = _
      rw [← types_comp_apply, ← F.map_comp]
      exact (hn i (hV W.unop i) (v W.unop i ≫ g.unop)).trans (ht W.unop i).symm
    · funext i
      apply Subtype.ext
      funext U
      show t (op U.unop.obj) = _
      simpa using hn i U.unop.property (𝟙 U.unop.obj)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- Restricting a section of the structure sheaf along `f` and then along `g` is restricting
it along any `h` with the same endpoints. -/
theorem presheaf_map_map_apply (X : Scheme.{u}) {U V W : X.Opens}
    (f : (op U : (X.Opens)ᵒᵖ) ⟶ op V) (g : (op V : (X.Opens)ᵒᵖ) ⟶ op W)
    (h : (op U : (X.Opens)ᵒᵖ) ⟶ op W) (s : Γ(X, U)) :
    X.presheaf.map g (X.presheaf.map f s) = X.presheaf.map h s := by
  have he : X.presheaf.map f ≫ X.presheaf.map g = X.presheaf.map h := by
    rw [← X.presheaf.map_comp]; congr 1
  exact ConcreteCategory.congr_hom he s

/-- Global sections of a scheme are the product of the sections over the members of a
pairwise disjoint open cover. -/
theorem bijective_pi_appTop_of_disjoint_cover (X : Scheme.{u}) {I : Type*} (V : I → X.Opens)
    (hd : Pairwise fun i j => Disjoint (V i) (V j)) (hc : iSup V = ⊤) :
    Function.Bijective (fun s : Γ(X, ⊤) => fun i => (V i).ι.appTop s) := by
  have hcomp (t : ∀ i, Γ(X, V i)) : TopCat.Presheaf.IsCompatible X.presheaf V t := by
    intro i j
    rcases eq_or_ne i j with rfl | h
    · rfl
    · have : Subsingleton Γ(X, V i ⊓ V j) := by rw [(hd h).eq_bot]; infer_instance
      exact Subsingleton.elim _ _
  have hr (s : Γ(X, ⊤)) (i : I) :
      (V i).topIso.hom ((V i).ι.appTop s) =
        X.presheaf.map (homOfLE (show V i ≤ ⊤ from le_top)).op s :=
    presheaf_map_map_apply X (homOfLE (show (V i).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
      (eqToHom (V i).ι_image_top.symm).op _ s
  constructor
  · intro s t h
    apply X.sheaf.eq_of_locally_eq' V ⊤ (fun _ => homOfLE le_top) hc.ge
    intro i
    exact (hr s i).symm.trans
      ((congrArg (fun a => (V i).topIso.hom a) (congrFun h i)).trans (hr t i))
  · intro t
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V ⊤
      (fun _ => homOfLE le_top) hc.ge (fun i => (V i).topIso.hom (t i)) (hcomp _)
    exact ⟨s, funext fun i =>
      (ConcreteCategory.bijective_of_isIso (V i).topIso.hom).injective ((hr s i).trans (hs i))⟩

/-- For an idempotent global function `e`, the basic open of `1 - e` is the complement of the
basic open of `e`. -/
theorem mem_basicOpen_one_sub_of_isIdempotentElem (Y : Scheme.{u}) (e : Γ(Y, ⊤))
    (he : IsIdempotentElem e) (x : Y) :
    x ∈ Y.basicOpen (1 - e) ↔ x ∉ Y.basicOpen e := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
  rcases IsLocalRing.isIdempotentElem_eq_zero_or_one
    (he.map (Y.presheaf.germ ⊤ x trivial).hom) with h | h <;> simp [h]

/-- An idempotent global function with full basic open is `1`, and one with empty basic open
is `0`. -/
theorem isIdempotentElem_eq_of_basicOpen (Y : Scheme.{u}) (e : Γ(Y, ⊤))
    (he : IsIdempotentElem e) :
    ((∀ x : Y, x ∈ Y.basicOpen e) → e = 1) ∧ ((∀ x : Y, x ∉ Y.basicOpen e) → e = 0) := by
  constructor
  · intro h
    apply TopCat.Presheaf.section_ext ⟨Y.presheaf, Y.sheaf.2⟩
    intro x hx
    rw [map_one]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit
      ((Y.mem_basicOpen_top e x).mp (h x))).mp
      (he.map (Y.presheaf.germ ⊤ x hx).hom)
  · intro h
    apply TopCat.Presheaf.section_ext ⟨Y.presheaf, Y.sheaf.2⟩
    intro x hx
    rw [map_zero]
    exact (IsLocalRing.isIdempotentElem_eq_zero_or_one
      (he.map (Y.presheaf.germ ⊤ x hx).hom)).resolve_right
        fun h1 => h x ((Y.mem_basicOpen_top e x).mpr (h1 ▸ isUnit_one))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

section Presheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The ring of global regular functions of a presheaf on the big fppf site of `S`: the
compatible families of regular functions on its étale charts. -/
abbrev globalFunctions : Type (u + 1) :=
  (structurePresheaf B S hS F ⋙ forget CommRingCat).sections

/-- Pointwise ring operations on compatible families of regular functions. -/
noncomputable instance globalFunctionsCommRing : CommRing (globalFunctions B S hS F) :=
  @Subring.toCommRing
    (∀ U, (structurePresheaf B S hS F).obj U) _
    (RingCat.sectionsSubring
      (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat))

end Presheaf

section Base

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)

/-- The canonical ring homomorphism from the base ring to the global regular functions of a
presheaf over `Spec A`: a scalar is sent to the family of its pullbacks along the structure
morphisms of the étale charts. -/
noncomputable def baseToGlobalFunctions :
    A →+* globalFunctions B (Spec (.of A)) hA X where
  toFun a := ⟨fun U =>
    (((Scheme.ΓSpecIso (.of A)).inv ≫
      Scheme.Γ.map ((B.inclusion.map
        ((SmallEtale.toOver B (Spec (.of A)) hA X).obj U.unop).hom).op)).hom a),
    by
      intro U V g
      let T := SmallEtale.toOver B (Spec (.of A)) hA X
      have hw :
          B.inclusion.map (T.map g.unop).left ≫
              B.inclusion.map (T.obj U.unop).hom =
            B.inclusion.map (T.obj V.unop).hom := by
        simpa only [← Functor.map_comp] using
          congrArg B.inclusion.map (Over.w (T.map g.unop))
      change (((Scheme.ΓSpecIso (.of A)).inv ≫
        (B.inclusion.map (T.obj U.unop).hom).appTop ≫
        (B.inclusion.map (T.map g.unop).left).appTop).hom a) =
        (((Scheme.ΓSpecIso (.of A)).inv ≫
          (B.inclusion.map (T.obj V.unop).hom).appTop).hom a)
      rw [← Scheme.Hom.comp_appTop, hw]⟩
  map_one' := Subtype.ext <| funext fun _ => RingHom.map_one _
  map_mul' a b := Subtype.ext <| funext fun _ => RingHom.map_mul _ a b
  map_zero' := Subtype.ext <| funext fun _ => RingHom.map_zero _
  map_add' a b := Subtype.ext <| funext fun _ => RingHom.map_add _ a b

/-- The value of a constant at an étale chart is its pullback along the structure morphism of
that chart. -/
theorem baseToGlobalFunctions_val_apply (a : A) (U : (SmallEtale B (Spec (.of A)) hA X)ᵒᵖ) :
    (baseToGlobalFunctions A B hA X a).val U =
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        Scheme.Γ.map (B.inclusion.map
          (((SmallEtale.toOver B (Spec (.of A)) hA X).obj U.unop).hom)).op) a :=
  rfl

/-- The canonical algebra structure on the global regular functions of a presheaf over
`Spec A`. -/
noncomputable instance globalFunctionsAlgebra :
    Algebra A (globalFunctions B (Spec (.of A)) hA X) :=
  (baseToGlobalFunctions A B hA X).toAlgebra

/-- The algebra map of `AlgebraicGeometry.Space.globalFunctionsAlgebra` is
`AlgebraicGeometry.Space.baseToGlobalFunctions`. -/
theorem algebraMap_globalFunctions :
    algebraMap A (globalFunctions B (Spec (.of A)) hA X) = baseToGlobalFunctions A B hA X :=
  rfl

end Base

/-! ### Restricting an étale chart to an open subscheme of its source -/

section Charts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- An étale chart of `F` restricted to an open subscheme of its source. -/
noncomputable def chartOpenRestriction (U : SmallEtale B S hS F)
    (V : ((BigFppfOver.toScheme B S hS).obj U.1.left).Opens) : SmallEtale B S hS F := by
  let hV : B.Contains V.toScheme :=
    Scheme.size_lt_of_isOpenImmersion V.ι U.1.left.left.property
  let i : B.obj hV ⟶ U.1.left.left :=
    B.inclusion.preimage (X := B.obj hV) (Y := U.1.left.left) V.ι
  let W : BigFppfOver B S hS := Over.mk (i ≫ U.1.left.hom)
  let g : W ⟶ U.1.left := Over.homMk i (by simp [W])
  refine ⟨CostructuredArrow.mk (yoneda.map g ≫ U.1.hom), ?_⟩
  refine etale_comp_of_scheme B S hS g U.1.hom ?_ U.2
  have hgi : (BigFppfOver.toScheme B S hS).map g = V.ι := B.inclusion.map_preimage _
  rw [hgi]
  infer_instance

/-- The inclusion of a chart restricted to an open subscheme into the chart. -/
noncomputable def chartOpenRestrictionHom (U : SmallEtale B S hS F)
    (V : ((BigFppfOver.toScheme B S hS).obj U.1.left).Opens) :
    chartOpenRestriction B S hS F U V ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (B.inclusion.preimage V.ι)) (by rfl))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.chartOpenRestrictionHom` is
the inclusion of the open subscheme. -/
theorem chartOpenRestrictionHom_toScheme (U : SmallEtale B S hS F)
    (V : ((BigFppfOver.toScheme B S hS).obj U.1.left).Opens) :
    (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
      (chartOpenRestrictionHom B S hS F U V) = V.ι :=
  B.inclusion.map_preimage _

/-- A morphism of étale charts does not move the point of the presheaf that a point of the
source chart represents. -/
theorem pointsMap_chart_hom {U W : SmallEtale B S hS F} (g : W ⟶ U)
    (p : points B S hS (yoneda.obj W.obj.left)) :
    pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
        (pointsMap B S hS (yoneda.obj W.obj.left) (yoneda.map g.hom.left) p) =
      pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom p := by
  have h : yoneda.map g.hom.left ≫ U.obj.hom = W.obj.hom := by simp
  rw [← h, pointsMap_comp]
  rfl

/-- A morphism of étale charts whose image lies in an open subscheme of the target factors
through the restriction of the target to that subscheme. -/
theorem chartOpenRestriction_fac {U W : SmallEtale B S hS F}
    (V : ((BigFppfOver.toScheme B S hS).obj U.1.left).Opens) (g : W ⟶ U)
    (hg : Set.range ((BigFppfOver.toScheme B S hS).map g.hom.left) ⊆ (V : Set _)) :
    ∃ l : W ⟶ chartOpenRestriction B S hS F U V,
      l ≫ chartOpenRestrictionHom B S hS F U V = g := by
  let l := IsOpenImmersion.lift V.ι ((BigFppfOver.toScheme B S hS).map g.hom.left)
    (by rw [Scheme.Opens.range_ι]; exact hg)
  have hl : l ≫ V.ι = (BigFppfOver.toScheme B S hS).map g.hom.left :=
    IsOpenImmersion.lift_fac _ _ _
  let W' := chartOpenRestriction B S hS F U V
  let lB : W.obj.left.left ⟶ W'.obj.left.left :=
    B.inclusion.preimage (X := W.obj.left.left) (Y := W'.obj.left.left) l
  let vB := (chartOpenRestrictionHom B S hS F U V).hom.left.left
  have hlB : lB ≫ vB = g.hom.left.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    have h1 : B.inclusion.map lB = l := B.inclusion.map_preimage _
    have h2 : B.inclusion.map vB = V.ι := chartOpenRestrictionHom_toScheme B S hS F U V
    rw [h1, h2]
    exact hl
  let lO : W.obj.left ⟶ W'.obj.left := Over.homMk lB (by
    show lB ≫ (vB ≫ U.obj.left.hom) = W.obj.left.hom
    rw [← Category.assoc, hlB]
    exact g.hom.left.w)
  have hlO : lO ≫ (chartOpenRestrictionHom B S hS F U V).hom.left = g.hom.left :=
    Over.OverMorphism.ext hlB
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk lO (by
    show yoneda.map lO ≫ (yoneda.map _ ≫ U.obj.hom) = W.obj.hom
    have hh := congrArg (fun t => yoneda.map t ≫ U.obj.hom) hlO
    exact hh.trans (by simp))), ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hlO)⟩

/-- Two points of two étale charts of `F` representing the same point of `F` are the images
of a single point of a common chart. -/
theorem exists_common_chart (U V : SmallEtale B S hS F)
    (p : points B S hS (yoneda.obj U.obj.left))
    (q : points B S hS (yoneda.obj V.obj.left))
    (hpq : pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p =
      pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom q) :
    ∃ (W : SmallEtale B S hS F) (a : W ⟶ U) (b : W ⟶ V)
      (r : points B S hS (yoneda.obj W.obj.left)),
      pointsMap B S hS (yoneda.obj W.obj.left) (yoneda.map a.hom.left) r = p ∧
      pointsMap B S hS (yoneda.obj W.obj.left) (yoneda.map b.hom.left) r = q := by
  have sq : IsPullback (yoneda.map (U.property.rep.fst' V.obj.hom))
      (yoneda.map (U.property.rep.snd V.obj.hom)) U.obj.hom V.obj.hom :=
    U.property.rep.isPullback' V.obj.hom
  have hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (U.property.rep.snd V.obj.hom) :=
    U.property.property V.obj.hom _ _ sq
  refine ⟨⟨CostructuredArrow.mk (yoneda.map (U.property.rep.snd V.obj.hom) ≫ V.obj.hom),
      etale_comp_of_scheme B S hS _ V.obj.hom hb V.property⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk (U.property.rep.fst' V.obj.hom) sq.w),
    ObjectProperty.homMk (CostructuredArrow.homMk (U.property.rep.snd V.obj.hom) rfl), ?_⟩
  exact exists_points_of_isPullback B S hS sq p q hpq

/-- Whether a point of a chart lies in the basic open of a global function does not depend on
the chart it is read on. -/
theorem basicOpen_section_map (s : globalFunctions B S hS F)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (p : points B S hS (yoneda.obj V.obj.left)) :
    pointsToScheme B S hS U.obj.left
          (pointsMap B S hS (yoneda.obj V.obj.left) (yoneda.map g.hom.left) p) ∈
        ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (s.val (op U)) ↔
      pointsToScheme B S hS V.obj.left p ∈
        ((BigFppfOver.toScheme B S hS).obj V.obj.left).basicOpen (s.val (op V)) := by
  rw [pointsToScheme_pointsMap_yoneda]
  obtain ⟨r, hr⟩ : ∃ r : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤),
      r = s.val (op U) := ⟨s.val (op U), rfl⟩
  have hs : ((BigFppfOver.toScheme B S hS).map g.hom.left).appTop r = s.val (op V) := by
    rw [hr]; exact s.property g.op
  rw [← hr, ← hs]
  exact Iff.of_eq (congrArg
    (fun W : ((BigFppfOver.toScheme B S hS).obj V.obj.left).Opens =>
      pointsToScheme B S hS V.obj.left p ∈ W)
    (Scheme.preimage_basicOpen_top ((BigFppfOver.toScheme B S hS).map g.hom.left) r))

/-- The *support* of a global function: the points of `F` at which it does not vanish, read
on any étale chart. -/
def sectionSupport (s : globalFunctions B S hS F) : Set (points B S hS F) :=
  {x | ∃ (U : SmallEtale B S hS F) (p : points B S hS (yoneda.obj U.obj.left)),
    pointsToScheme B S hS U.obj.left p ∈
        ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (s.val (op U)) ∧
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p = x}

/-- The value of an idempotent global function on a chart is idempotent. -/
private theorem isIdempotentElem_val (s : globalFunctions B S hS F) (hs : IsIdempotentElem s)
    (U : SmallEtale B S hS F) : IsIdempotentElem (s.val (op U)) :=
  congrArg (fun t : globalFunctions B S hS F => t.val (op U)) hs.eq

/-- The support of a global function is detected on any single chart. -/
theorem mem_sectionSupport_iff (s : globalFunctions B S hS F) (U : SmallEtale B S hS F)
    (p : points B S hS (yoneda.obj U.obj.left)) :
    pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p ∈ sectionSupport B S hS F s ↔
      pointsToScheme B S hS U.obj.left p ∈
        ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (s.val (op U)) := by
  constructor
  · rintro ⟨V, q, hq, he⟩
    obtain ⟨W, a, b, r, hr, hr'⟩ := exists_common_chart B S hS F U V p q he.symm
    rw [← hr]
    exact (basicOpen_section_map B S hS F s a r).mpr
      ((basicOpen_section_map B S hS F s b r).mp (hr' ▸ hq))
  · exact fun hp => ⟨U, p, hp, rfl⟩

end Charts

/-! ### Restriction of global functions to the charts of a connected component -/

section Components

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [TopologicalSpace (points B S hS F)]

/-- The set of points belonging to a connected component of the point space.  For any
representative `x` of `c` this is `connectedComponent x`. -/
def connectedComponentCarrier (c : ConnectedComponents (points B S hS F)) :
    Set (points B S hS F) :=
  ConnectedComponents.mk ⁻¹' {c}

/-- A connected component of the point space is a connected subset. -/
theorem isConnected_connectedComponentCarrier (c : ConnectedComponents (points B S hS F)) :
    IsConnected (connectedComponentCarrier B S hS F c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  show IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- Étale charts whose entire image on points lies in a specified connected component. -/
def componentChartProperty (c : ConnectedComponents (points B S hS F)) :
    ObjectProperty (SmallEtale B S hS F) :=
  fun U => Set.range (pointsMap B S hS (yoneda.obj U.1.left) U.1.hom) ⊆
    connectedComponentCarrier B S hS F c

/-- The full subcategory of the small étale site cut out by the charts lying in one
connected component. -/
abbrev componentChart (c : ConnectedComponents (points B S hS F)) :=
  (componentChartProperty B S hS F c).FullSubcategory

/-- The factor of the global functions indexed by a connected component: the compatible
families of regular functions on the étale charts lying in that component. -/
abbrev componentFunctions (c : ConnectedComponents (points B S hS F)) : Type (u + 1) :=
  (((componentChartProperty B S hS F c).ι.op ⋙ structurePresheaf B S hS F) ⋙
    forget CommRingCat).sections

/-- Pointwise ring operations on compatible families of regular functions on the charts of
a connected component. -/
noncomputable instance componentFunctionsCommRing
    (c : ConnectedComponents (points B S hS F)) :
    CommRing (componentFunctions B S hS F c) :=
  @Subring.toCommRing
    (∀ j, ((componentChartProperty B S hS F c).ι.op ⋙ structurePresheaf B S hS F).obj j) _
    (RingCat.sectionsSubring
      (((componentChartProperty B S hS F c).ι.op ⋙ structurePresheaf B S hS F) ⋙
        forget₂ CommRingCat RingCat))

/-- Simultaneous restriction of global functions to the charts of every connected
component. -/
noncomputable def globalFunctionsRestriction :
    globalFunctions B S hS F →+*
      (∀ c : ConnectedComponents (points B S hS F), componentFunctions B S hS F c) where
  toFun s c := (componentChartProperty B S hS F c).ι.op.sectionsPrecomp s
  map_one' := by funext c; ext U; rfl
  map_mul' s t := by funext c; ext U; rfl
  map_zero' := by funext c; ext U; rfl
  map_add' s t := by funext c; ext U; rfl

/-- Restriction of global functions to the charts of a single connected component. -/
noncomputable def componentRestriction (c : ConnectedComponents (points B S hS F)) :
    globalFunctions B S hS F →+* componentFunctions B S hS F c :=
  (Pi.evalRingHom _ c).comp (globalFunctionsRestriction B S hS F)

/-- The restriction of a chart to an open cutting out a connected component lies in it. -/
private theorem componentChartProperty_chartOpenRestriction (U : SmallEtale B S hS F)
    (c : ConnectedComponents (points B S hS F))
    (V : ((BigFppfOver.toScheme B S hS).obj U.obj.left).Opens)
    (hV : ∀ p : FieldValuedPoint B S hS (yoneda.obj U.obj.left),
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
          (p.class B S hS (yoneda.obj U.obj.left)) ∈ connectedComponentCarrier B S hS F c ↔
        schemePoint B S hS U.obj.left p ∈ V) :
    componentChartProperty B S hS F c (chartOpenRestriction B S hS F U V) := by
  rintro _ ⟨p, rfl⟩
  induction p using Quot.inductionOn with | h p =>
    rw [← pointsMap_chart_hom B S hS F (chartOpenRestrictionHom B S hS F U V)]
    apply (hV (p.map B S hS _ (yoneda.map (chartOpenRestrictionHom B S hS F U V).hom.left))).mpr
    rw [schemePoint_map_yoneda]
    show ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
      (chartOpenRestrictionHom B S hS F U V)) _ ∈ V
    rw [chartOpenRestrictionHom_toScheme]
    exact (schemePoint B S hS (chartOpenRestriction B S hS F U V).obj.left p).property

/-- **The componentwise decomposition of global functions.**  Suppose that for every étale
chart `U` and every connected component `c` an open subscheme `V U c` of `U` has been chosen
which is exactly the part of `U` lying over `c`, and that for each `U` these opens are
pairwise disjoint and cover `U`.  Then simultaneous restriction to the components is a
bijection from global functions onto the product of the componentwise factors. -/
theorem bijective_globalFunctionsRestriction_of_cover
    (V : (U : SmallEtale B S hS F) → ConnectedComponents (points B S hS F) →
      ((BigFppfOver.toScheme B S hS).obj U.obj.left).Opens)
    (hVspec : ∀ (U : SmallEtale B S hS F) (c : ConnectedComponents (points B S hS F))
      (p : FieldValuedPoint B S hS (yoneda.obj U.obj.left)),
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
          (p.class B S hS (yoneda.obj U.obj.left)) ∈
            connectedComponentCarrier B S hS F c ↔
        schemePoint B S hS U.obj.left p ∈ V U c)
    (hc : ∀ U, iSup (V U) = ⊤)
    (hd : ∀ U, Pairwise fun c d => Disjoint (V U c) (V U d)) :
    Function.Bijective (globalFunctionsRestriction B S hS F) := by
  let W U c := chartOpenRestriction B S hS F U (V U c)
  let v U c := chartOpenRestrictionHom B S hS F U (V U c)
  have hW U c : componentChartProperty B S hS F c (W U c) :=
    componentChartProperty_chartOpenRestriction B S hS F U c _ (hVspec U c)
  apply Functor.bijective_pi_sectionsPrecomp
    (structurePresheaf B S hS F ⋙ forget CommRingCat)
    (componentChartProperty B S hS F) W v hW
  · intro U T c hT g
    apply chartOpenRestriction_fac
    rintro _ ⟨x, rfl⟩
    obtain ⟨p, rfl⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS T.obj.left x
    have hp := hT ⟨p.class B S hS _, rfl⟩
    rw [← pointsMap_chart_hom B S hS F g] at hp
    have hm := (hVspec U c (p.map B S hS _ (yoneda.map g.hom.left))).mp hp
    rwa [schemePoint_map_yoneda] at hm
  · intro U
    have h := Scheme.bijective_pi_appTop_of_disjoint_cover
      ((BigFppfOver.toScheme B S hS).obj U.obj.left) (V U) (hd U) (hc U)
    show Function.Bijective
      (fun s : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) => fun c =>
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (v U c)).appTop s)
    simp only [v, chartOpenRestrictionHom_toScheme]
    exact h

end Components

section ComponentsOverBase

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    [TopologicalSpace (points B (Spec (.of A)) hA X)]

/-- The base-ring algebra structure on a componentwise factor, induced from the one on
global functions by restriction. -/
@[instance_reducible]
noncomputable def componentFunctionsAlgebra
    (c : ConnectedComponents (points B (Spec (.of A)) hA X)) :
    Algebra A (componentFunctions B (Spec (.of A)) hA X c) :=
  ((componentRestriction B (Spec (.of A)) hA X c).comp
    (baseToGlobalFunctions A B hA X)).toAlgebra

/-- Simultaneous restriction of global functions to the connected components, as a
homomorphism of base-ring algebras. -/
noncomputable def globalFunctionsRestrictionAlgHom :
    letI (c : ConnectedComponents (points B (Spec (.of A)) hA X)) :
        Algebra A (componentFunctions B (Spec (.of A)) hA X c) :=
      componentFunctionsAlgebra A B hA X c
    globalFunctions B (Spec (.of A)) hA X →ₐ[A]
      (∀ c : ConnectedComponents (points B (Spec (.of A)) hA X),
        componentFunctions B (Spec (.of A)) hA X c) :=
  letI (c : ConnectedComponents (points B (Spec (.of A)) hA X)) :
      Algebra A (componentFunctions B (Spec (.of A)) hA X c) :=
    componentFunctionsAlgebra A B hA X c
  ⟨globalFunctionsRestriction B (Spec (.of A)) hA X, fun _ => funext fun _ => rfl⟩

end ComponentsOverBase

/-- The componentwise Artinian factorization of the global functions of an algebraic space
over a field, with the equivalence fixed to be simultaneous restriction to the connected
components. -/
structure ComponentwiseArtinianFactorization (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    [TopologicalSpace (points B (Spec (.of k)) hS X)] where
  /-- Each connected component is an open subset of the point space. -/
  isOpen_component : ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
    IsOpen (connectedComponentCarrier B (Spec (.of k)) hS X c)
  /-- Each factor is an Artinian ring. -/
  isArtinian : ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
    IsArtinianRing (componentFunctions B (Spec (.of k)) hS X c)
  /-- Each factor is a local ring. -/
  isLocal : ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
    IsLocalRing (componentFunctions B (Spec (.of k)) hS X c)
  /-- The base-field algebra structure on each factor. -/
  factorAlgebra : ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
    Algebra k (componentFunctions B (Spec (.of k)) hS X c)
  /-- Global functions are the product of the factors. -/
  equivalence :
    letI (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
        Algebra k (componentFunctions B (Spec (.of k)) hS X c) := factorAlgebra c
    globalFunctions B (Spec (.of k)) hS X ≃ₐ[k]
      (∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X c)
  /-- The equivalence is simultaneous restriction to the components. -/
  equivalence_apply :
    letI (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
        Algebra k (componentFunctions B (Spec (.of k)) hS X c) := factorAlgebra c
    ∀ (s : globalFunctions B (Spec (.of k)) hS X)
      (c : ConnectedComponents (points B (Spec (.of k)) hS X)),
      equivalence s c =
        (componentChartProperty B (Spec (.of k)) hS X c).ι.op.sectionsPrecomp s

/-! ### The point topology enters -/

section PointTopology

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Every point of an algebraic space comes from a point of one of its étale charts. -/
theorem exists_chart_point (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    ∃ (U : SmallEtale B S hS F) (p : points B S hS (yoneda.obj U.obj.left)),
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p = x := by
  obtain ⟨U, f, hs, he⟩ := hF.exists_atlas
  obtain ⟨p, hp⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U f).mp hs x
  exact ⟨⟨CostructuredArrow.mk f, he⟩, p, hp⟩

/-- An open set of points, read on an étale chart, is cut out by an open subscheme of that
chart. -/
theorem exists_opens_chart_of_isOpen (U : SmallEtale B S hS F) (W : Set (points B S hS F))
    (hW : IsOpen W) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj U.obj.left).Opens,
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U.obj.left),
        pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
            (p.class B S hS (yoneda.obj U.obj.left)) ∈ W ↔
          schemePoint B S hS U.obj.left p ∈ V := by
  obtain ⟨V, hV, hiff⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS U.obj.left _).mp
    ((continuous_pointsMap B S hS U.obj.hom).isOpen_preimage W hW)
  exact ⟨⟨V, hV⟩, hiff⟩

/-- For an algebraic space `F` and an open connected component `c` of its points, the ring of
functions on the étale charts lying over `c` is nontrivial. -/
theorem nontrivial_componentFunctions (hF : IsAlgebraicSpace B S hS F)
    (c : ConnectedComponents (points B S hS F))
    (hc : IsOpen (connectedComponentCarrier B S hS F c)) :
    Nontrivial (componentFunctions B S hS F c) := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS F hF x
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  obtain ⟨V, hV⟩ := exists_opens_chart_of_isOpen B S hS F U _ hc
  have hxV : schemePoint B S hS U.obj.left p ∈ V :=
    (hV p).mp (by change ConnectedComponents.mk _ = c; rw [hp]; exact hx)
  have hW := componentChartProperty_chartOpenRestriction B S hS F U c V hV
  let y : V.toScheme := ⟨schemePoint B S hS U.obj.left p, hxV⟩
  refine nontrivial_of_ne (0 : componentFunctions B S hS F c) 1 fun h => ?_
  have hh : (0 : Γ(V.toScheme, ⊤)) = 1 :=
    congrArg (fun s : componentFunctions B S hS F c =>
      s.val (op ⟨chartOpenRestriction B S hS F U V, hW⟩)) h
  have hhh := congrArg (fun z => (V.toScheme.presheaf.germ ⊤ y trivial).hom z) hh
  rw [map_zero, map_one] at hhh
  exact zero_ne_one hhh

/-- Each connected component of a space with finitely many connected components is open. -/
theorem isOpen_connectedComponentCarrier
    [Finite (ConnectedComponents (points B S hS F))]
    (c : ConnectedComponents (points B S hS F)) :
    IsOpen (connectedComponentCarrier B S hS F c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  show IsOpen (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact (TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents x).2

/-- The support of a global function is open. -/
theorem isOpen_sectionSupport (s : globalFunctions B S hS F) :
    IsOpen (sectionSupport B S hS F s) := by
  have he : sectionSupport B S hS F s =
      ⋃ U : SmallEtale B S hS F,
        pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ''
          (pointsToScheme B S hS U.obj.left ⁻¹'
            (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen
              (s.val (op U)) : Set _)) := by
    ext x
    simp only [sectionSupport, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image,
      Set.mem_preimage]
    rfl
  rw [he]
  refine isOpen_iUnion fun U =>
    isOpenMap_pointsMap_of_presheafEtale B S hS U.obj.hom U.property _ ?_
  exact (isOpen_yoneda_iff_isSchemeOpen B S hS U.obj.left _).mpr
    ⟨_, (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (s.val (op U))).isOpen,
      fun _ => Iff.rfl⟩

/-- The support of an *idempotent* global function is clopen. -/
theorem isClopen_sectionSupport (hF : IsAlgebraicSpace B S hS F)
    (s : globalFunctions B S hS F) (hs : IsIdempotentElem s) :
    IsClopen (sectionSupport B S hS F s) := by
  have hc : (sectionSupport B S hS F s)ᶜ = sectionSupport B S hS F (1 - s) := by
    ext x
    obtain ⟨U, p, rfl⟩ := exists_chart_point B S hS F hF x
    rw [Set.mem_compl_iff, mem_sectionSupport_iff, mem_sectionSupport_iff]
    exact (Scheme.mem_basicOpen_one_sub_of_isIdempotentElem _ _
      (isIdempotentElem_val B S hS F s hs U) _).symm
  exact ⟨isOpen_compl_iff.mp (hc ▸ isOpen_sectionSupport B S hS F (1 - s)),
    isOpen_sectionSupport B S hS F s⟩

/-- An idempotent global function restricts to `0` or to `1` on each connected component. -/
theorem componentRestriction_eq_zero_or_one (hF : IsAlgebraicSpace B S hS F)
    (s : globalFunctions B S hS F) (hs : IsIdempotentElem s)
    (c : ConnectedComponents (points B S hS F)) :
    componentRestriction B S hS F c s = 0 ∨ componentRestriction B S hS F c s = 1 := by
  have hcl := isClopen_sectionSupport B S hS F hF s hs
  by_cases h : (connectedComponentCarrier B S hS F c ∩ sectionSupport B S hS F s).Nonempty
  · right
    have hh := (isConnected_connectedComponentCarrier B S hS F
      c).isPreconnected.subset_isClopen hcl h
    apply Subtype.ext
    funext U
    refine (Scheme.isIdempotentElem_eq_of_basicOpen _ _
      (isIdempotentElem_val B S hS F s hs U.unop.obj)).1 fun x => ?_
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS U.unop.obj.obj.left x
    exact (mem_sectionSupport_iff B S hS F s U.unop.obj p).mp (hh (U.unop.property ⟨p, rfl⟩))
  · left
    apply Subtype.ext
    funext U
    refine (Scheme.isIdempotentElem_eq_of_basicOpen _ _
      (isIdempotentElem_val B S hS F s hs U.unop.obj)).2 fun x hx => ?_
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS U.unop.obj.obj.left x
    exact h ⟨_, U.unop.property ⟨p, rfl⟩,
      (mem_sectionSupport_iff B S hS F s U.unop.obj p).mpr hx⟩

end PointTopology

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-! ### The componentwise factorization -/

section Factorization

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)

/-- The global functions of an algebraic space over a field, with finitely many connected
components and an Artinian ring of global functions, split as the product of the rings of
functions on the charts of each connected component, each factor Artinian and local, and the
splitting is simultaneous restriction. -/
theorem nonempty_componentwiseArtinianFactorization
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    [Finite (ConnectedComponents (points B (Spec (.of k)) hS X))]
    (hart : IsArtinianRing (globalFunctions B (Spec (.of k)) hS X)) :
    Nonempty (ComponentwiseArtinianFactorization k B hS X) := by
  classical
  have hopen := isOpen_connectedComponentCarrier B (Spec (.of k)) hS X
  let V (U : SmallEtale B (Spec (.of k)) hS X)
      (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj U.obj.left).Opens :=
    (exists_opens_chart_of_isOpen B (Spec (.of k)) hS X U _ (hopen c)).choose
  have hVspec : ∀ (U : SmallEtale B (Spec (.of k)) hS X)
      (c : ConnectedComponents (points B (Spec (.of k)) hS X))
      (p : FieldValuedPoint B (Spec (.of k)) hS (yoneda.obj U.obj.left)),
      pointsMap B (Spec (.of k)) hS (yoneda.obj U.obj.left) U.obj.hom
          (p.class B (Spec (.of k)) hS (yoneda.obj U.obj.left)) ∈
            connectedComponentCarrier B (Spec (.of k)) hS X c ↔
        schemePoint B (Spec (.of k)) hS U.obj.left p ∈ V U c :=
    fun U c => (exists_opens_chart_of_isOpen B (Spec (.of k)) hS X U _ (hopen c)).choose_spec
  have hVcover : ∀ U, iSup (V U) = ⊤ := by
    intro U
    apply TopologicalSpace.Opens.ext
    ext x
    obtain ⟨p, rfl⟩ :=
      exists_fieldValuedPoint_schemePoint_eq B (Spec (.of k)) hS U.obj.left x
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact ⟨ConnectedComponents.mk (pointsMap B (Spec (.of k)) hS
      (yoneda.obj U.obj.left) U.obj.hom
      (p.class B (Spec (.of k)) hS (yoneda.obj U.obj.left))),
      (hVspec U _ p).mp rfl⟩
  have hVdisjoint : ∀ U, Pairwise fun c d => Disjoint (V U c) (V U d) := by
    intro U c d hcd
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxc, hxd⟩
    obtain ⟨p, rfl⟩ :=
      exists_fieldValuedPoint_schemePoint_eq B (Spec (.of k)) hS U.obj.left x
    exact hcd (((hVspec U c p).mpr hxc).symm.trans ((hVspec U d p).mpr hxd))
  have hρ : Function.Bijective (globalFunctionsRestriction B (Spec (.of k)) hS X) :=
    bijective_globalFunctionsRestriction_of_cover B (Spec (.of k)) hS X V hVspec
      hVcover hVdisjoint
  let E := RingEquiv.ofBijective (globalFunctionsRestriction B (Spec (.of k)) hS X) hρ
  have hA : ∀ c, IsArtinianRing (componentFunctions B (Spec (.of k)) hS X c) := by
    intro c
    refine Function.Surjective.isArtinianRing
      (f := componentRestriction B (Spec (.of k)) hS X c) fun a => ?_
    obtain ⟨s, hs⟩ := hρ.surjective (Pi.single c a)
    exact ⟨s, (congrFun hs c).trans (Pi.single_eq_same c a)⟩
  have hL : ∀ c, IsLocalRing (componentFunctions B (Spec (.of k)) hS X c) := by
    intro c
    have := hA c
    have := nontrivial_componentFunctions B (Spec (.of k)) hS X hX c (hopen c)
    refine IsLocalRing.of_isArtinianRing_of_forall_isIdempotentElem _ fun e he => ?_
    let t : ∀ d, componentFunctions B (Spec (.of k)) hS X d := Pi.single c e
    have ht : IsIdempotentElem t := by
      show t * t = t
      funext d
      by_cases h : d = c
      · subst d
        simpa [t] using he.eq
      · simp [t, h]
    have hte : componentRestriction B (Spec (.of k)) hS X c (E.symm t) = e :=
      (congrFun (E.apply_symm_apply t) c).trans (Pi.single_eq_same c e)
    simpa only [hte] using componentRestriction_eq_zero_or_one B (Spec (.of k)) hS X hX
      (E.symm t) (ht.map E.symm) c
  let inst : ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
      Algebra k (componentFunctions B (Spec (.of k)) hS X c) :=
    fun c => componentFunctionsAlgebra k B hS X c
  exact ⟨{ isOpen_component := hopen
           isArtinian := hA
           isLocal := hL
           factorAlgebra := inst
           equivalence := AlgEquiv.ofBijective (globalFunctionsRestrictionAlgHom k B hS X) hρ
           equivalence_apply := fun _ _ => rfl }⟩

end Factorization

end AlgebraicGeometry.Space

end
