module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesFibreProduct

/-!
# The functor of quadruples of Stacks 084A as a limit over the quasi-compact opens

In Situation 0849 the source defines the functor `F` of quadruples on a quasi-compact test scheme
as the union `F(T)` of the classes of quadruples — in this library
`AlgebraicGeometry.Space.GradedAlgebraPoints.F` — and on an arbitrary test scheme `T` as the
limit `F(T) = lim_{V ⊆ T quasi-compact open} F(V)`.  This file constructs that limit literally,
for any presheaf `Φ` on the big fppf site, as
`AlgebraicGeometry.Space.SiteQcExtension`, and applies it to the functor of quadruples
`AlgebraicGeometry.Space.GradedAlgebraRestriction.functor` of a restriction datum `ρ`: the
presheaf `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleFunctor` is **the functor of
Stacks 084A**, the union `GradedAlgebraPoints.F` on every quasi-compact test object
(`AlgebraicGeometry.Space.SiteQcExtension.equivObj`) and the limit of those unions in general.

It then compares it with the presheaf `AlgebraicGeometry.Space.GradedAlgebraRestriction.limFunctor`
on which the comparison with the relative homogeneous spectrum was carried out, whose points
record the glued point of `X` together with a family of points of the fibres.  When `X` is a sheaf
for the fppf topology — in Situation 0849 it is an algebraic space — the two agree
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.limPointEquiv`): the points of `X` underlying
a compatible family of points of `F` over the quasi-compact test objects glue, because the
quasi-compact opens of a test object cover it.

## Main definitions

* `AlgebraicGeometry.Space.SiteQcExtension`: the limit of a presheaf over the test objects with
  quasi-compact scheme mapping to a given one.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleFunctor`: the functor of quadruples
  of Stacks 084A.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.limPointIso`: its identification with
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.limFunctor` for a sheaf `X`.

## Main results

* `AlgebraicGeometry.Space.sieve_compactOpens_mem`: the quasi-compact opens of a test object
  generate a covering sieve.
* `AlgebraicGeometry.Space.existsUnique_glue_compactSpace`: a family of points of a sheaf over
  all the test objects with quasi-compact scheme mapping to `T`, compatible with restriction,
  glues to a unique point over `T`.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The limit over the quasi-compact test objects -/

/-- **The limit of a presheaf over the quasi-compact test objects over `T`**: a family of
elements of `Φ(W)`, one for each morphism `w : W ⟶ T` out of a test object with quasi-compact
scheme, compatible with restriction.  Restricted to the quasi-compact opens of `T` this is the
limit `lim_{V ⊆ T quasi-compact open} Φ(V)`; indexing by all quasi-compact test objects over `T`
makes the functoriality in `T` a reindexing. -/
structure SiteQcExtension (Φ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v) (T : BigFppfOver B S hS) where
  /-- The element recorded at `w : W ⟶ T`. -/
  val (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T) : Φ.obj (op W)
  /-- The recorded elements are compatible with restriction. -/
  compat (W W' : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) (h : W' ⟶ W) (w : W ⟶ T) :
    Φ.map h.op (val W hW w) = val W' hW' (h ≫ w)

namespace SiteQcExtension

variable {Φ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}

/-- Two elements of the limit are equal if they record the same element at every `w : W ⟶ T`. -/
@[ext] theorem ext {T : BigFppfOver B S hS} {s s' : SiteQcExtension Φ T}
    (h : ∀ W hW w, s.val W hW w = s'.val W hW w) : s = s' := by
  obtain ⟨v, c⟩ := s
  obtain ⟨v', c'⟩ := s'
  obtain rfl : v = v' := funext fun W => funext fun hW => funext fun w => h W hW w
  rfl

/-- Reindexing along a morphism of test objects. -/
def pullback {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (s : SiteQcExtension Φ T) :
    SiteQcExtension Φ T' where
  val W hW w := s.val W hW (w ≫ τ)
  compat W W' hW hW' h w := s.compat W W' hW hW' h (w ≫ τ)

/-- **The limit as a presheaf on the big fppf site.** -/
def functor (Φ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)
    where
  obj T := SiteQcExtension Φ T.unop
  map τ := TypeCat.ofHom (pullback τ.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The element recorded at `w` by the reindexing of `s` along `τ` is the element recorded by `s`
at `w ≫ τ.unop`. -/
@[simp] theorem functor_map_val {T T' : (BigFppfOver B S hS)ᵒᵖ} (τ : T ⟶ T')
    (s : SiteQcExtension Φ T.unop) (W : BigFppfOver B S hS)
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T'.unop) :
    ((functor Φ).map τ s).val W hW w = s.val W hW (w ≫ τ.unop) := rfl

/-- **On a test object with quasi-compact scheme the limit is the value of the presheaf**: the
identity is a terminal object of the index. -/
def equivObj (T : BigFppfOver B S hS) (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    SiteQcExtension Φ T ≃ Φ.obj (op T) where
  toFun s := s.val T hT (𝟙 T)
  invFun x :=
    { val := fun _ _ w => Φ.map w.op x
      compat := fun _ _ _ _ h w => by rw [op_comp, Functor.map_comp_apply] }
  left_inv s := by
    ext W hW w
    exact s.compat T W hT hW w (𝟙 T)
  right_inv x := by
    change Φ.map (𝟙 T).op x = x
    rw [op_id, Functor.map_id_apply]

end SiteQcExtension

/-! ### The quasi-compact opens of a test object cover it -/

/-- The open subscheme of a quasi-compact open is quasi-compact. -/
theorem compactSpace_opensObject (Y : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj Y).CompactOpens) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (opensObject B S hS Y V.1)) :=
  isCompact_iff_compactSpace.mp V.2

/-- **The quasi-compact opens of a test object generate a covering sieve** of the big fppf site:
they are open immersions and every point lies in an affine, hence quasi-compact, open. -/
theorem sieve_compactOpens_mem (Y : BigFppfOver B S hS) :
    Sieve.ofArrows (fun V : ((BigFppfOver.toScheme B S hS).obj Y).CompactOpens =>
        opensObject B S hS Y V.1) (fun V => opensObjectι B S hS Y V.1) ∈
      BigFppfOver.topology B S hS Y := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
    (fun V => inferInstanceAs (AlgebraicGeometry.IsOpenImmersion V.1.ι)) fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj Y).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  refine ⟨⟨(U : ((BigFppfOver.toScheme B S hS).obj Y).Opens), hU.isCompact⟩, ?_⟩
  show x ∈ Set.range (Scheme.Opens.ι (U : ((BigFppfOver.toScheme B S hS).obj Y).Opens)).base
  rw [Scheme.Opens.range_ι]
  exact hxU

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)

include hX in
/-- **A point of a sheaf over a test object is determined by its restrictions to the
quasi-compact opens.** -/
theorem eq_of_compactOpens {Y : BigFppfOver B S hS} {a b : yoneda.obj Y ⟶ X}
    (h : ∀ V : ((BigFppfOver.toScheme B S hS).obj Y).CompactOpens,
      yoneda.map (opensObjectι B S hS Y V.1) ≫ a = yoneda.map (opensObjectι B S hS Y V.1) ≫ b) :
    a = b := by
  apply yonedaEquiv.injective
  refine (((isSheaf_iff_isSheaf_of_type _ X).mp hX) _
    (sieve_compactOpens_mem Y)).isSeparatedFor.ext fun Z f hf => ?_
  obtain ⟨_, k, _, ⟨V⟩, rfl⟩ := hf
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, Functor.map_comp, Category.assoc,
    Category.assoc, h V]

include hX in
/-- The restrictions of a compatible family of points of a sheaf over the quasi-compact test
objects over `T` agree on a common refinement. -/
theorem map_comp_eq_of_comp_eq {T : BigFppfOver B S hS}
    (p : ∀ (W : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj W) →
      (W ⟶ T) → (yoneda.obj W ⟶ X))
    (hp : ∀ (W W' : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
      (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) (h : W' ⟶ W) (w : W ⟶ T),
      p W' hW' (h ≫ w) = yoneda.map h ≫ p W hW w)
    {Z W W' : BigFppfOver B S hS} (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) {w : W ⟶ T} {w' : W' ⟶ T}
    {g : Z ⟶ W} {g' : Z ⟶ W'} (hg : g ≫ w = g' ≫ w') :
    yoneda.map g ≫ p W hW w = yoneda.map g' ≫ p W' hW' w' := by
  refine eq_of_compactOpens hX fun U => ?_
  have hU := compactSpace_opensObject Z U
  simpa only [Functor.map_comp, Category.assoc] using
    (hp _ _ _ hU (opensObjectι B S hS Z U.1 ≫ g) w).symm.trans <|
      (congrArg (p _ hU) (by rw [Category.assoc, Category.assoc, hg])).trans
        (hp _ _ _ hU (opensObjectι B S hS Z U.1 ≫ g') w')

/-- A point over `T` which restricts to a compatible family on the quasi-compact opens of `T`
restricts to it on every quasi-compact test object over `T`. -/
theorem map_comp_eq_of_forall_compactOpens {T : BigFppfOver B S hS}
    (p : ∀ (W : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj W) →
      (W ⟶ T) → (yoneda.obj W ⟶ X))
    (hp : ∀ (W W' : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
      (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) (h : W' ⟶ W) (w : W ⟶ T),
      p W' hW' (h ≫ w) = yoneda.map h ≫ p W hW w)
    (t : yoneda.obj T ⟶ X)
    (ht : ∀ V : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens,
      yoneda.map (opensObjectι B S hS T V.1) ≫ t =
        p _ (compactSpace_opensObject T V) (opensObjectι B S hS T V.1))
    (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T) : yoneda.map w ≫ t = p W hW w := by
  let c := Scheme.compactOpenFactorization hW ((BigFppfOver.toScheme B S hS).map w)
  have hc := compactSpace_opensObject T ⟨c.opens, c.isCompact_opens⟩
  have hι : yoneda.map (opensObjectι B S hS T c.opens) ≫ t =
      p _ hc (opensObjectι B S hS T c.opens) := ht ⟨c.opens, c.isCompact_opens⟩
  calc yoneda.map w ≫ t
      = yoneda.map (GradedAlgebraRestriction.factorHom w c ≫ opensObjectι B S hS T c.opens) ≫
          t := by
        rw [GradedAlgebraRestriction.factorHom_ι]
    _ = yoneda.map (GradedAlgebraRestriction.factorHom w c) ≫
        p _ hc (opensObjectι B S hS T c.opens) := by rw [Functor.map_comp, Category.assoc, hι]
    _ = p W hW (GradedAlgebraRestriction.factorHom w c ≫ opensObjectι B S hS T c.opens) :=
        (hp _ _ hc hW _ _).symm
    _ = p W hW w := congrArg (p W hW) (GradedAlgebraRestriction.factorHom_ι w c)

include hX in
/-- **A compatible family of points of a sheaf over the quasi-compact test objects over `T` glues
to a unique point over `T`.** -/
theorem existsUnique_glue_compactSpace {T : BigFppfOver B S hS}
    (p : ∀ (W : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj W) →
      (W ⟶ T) → (yoneda.obj W ⟶ X))
    (hp : ∀ (W W' : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
      (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) (h : W' ⟶ W) (w : W ⟶ T),
      p W' hW' (h ≫ w) = yoneda.map h ≫ p W hW w) :
    ∃! f : yoneda.obj T ⟶ X, ∀ (W : BigFppfOver B S hS)
      (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T),
      yoneda.map w ≫ f = p W hW w := by
  have hs := ((isSheaf_iff_isSheaf_of_type _ X).mp hX) _ (sieve_compactOpens_mem T)
  rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hs
  obtain ⟨t, ht, -⟩ := hs (fun V => yonedaEquiv (p _ (compactSpace_opensObject T V)
      (opensObjectι B S hS T V.1))) fun V V' Z gi gj hg => by
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    congr 1
    exact map_comp_eq_of_comp_eq hX p hp _ _ hg
  have hfac := map_comp_eq_of_forall_compactOpens p hp (yonedaEquiv.symm t) fun V =>
    yonedaEquiv.injective (by rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]; exact ht V)
  refine ⟨yonedaEquiv.symm t, hfac, fun f hf => eq_of_compactOpens hX fun V => ?_⟩
  rw [hf _ (compactSpace_opensObject T V), hfac _ (compactSpace_opensObject T V)]

/-! ### The functor of quadruples of Stacks 084A -/

namespace GradedAlgebraRestriction

variable {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

/-- **Stacks 084A: the functor of quadruples**, on every test object `T` the limit over the
quasi-compact test objects `W ⟶ T` of the unions `F(W)` of the classes of quadruples
(`AlgebraicGeometry.Space.GradedAlgebraPoints.F`). On a quasi-compact `T` its value is `F(T)`
itself, by `AlgebraicGeometry.Space.SiteQcExtension.equivObj`. -/
abbrev quadrupleFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  SiteQcExtension.functor ρ.functor

/-- A point of the limit with its glued point, as a point of the functor of quadruples. -/
def limPointToQc {T : BigFppfOver B S hS} (ξ : LimPoint ρ T) : SiteQcExtension ρ.functor T where
  val W hW w := ⟨yoneda.map w ≫ ξ.point, ξ.val W hW w⟩
  compat W W' hW hW' h w := Sigma.ext rfl (heq_of_eq (ξ.compat W W' hW hW' h w))

include hX in
/-- The points of `X` underlying a point of the functor of quadruples glue. -/
theorem existsUnique_point {T : BigFppfOver B S hS} (s : SiteQcExtension ρ.functor T) :
    ∃! f : yoneda.obj T ⟶ X, ∀ (W : BigFppfOver B S hS)
      (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T),
      yoneda.map w ≫ f = GradedAlgebraPoints.F.point r (s.val W hW w) :=
  existsUnique_glue_compactSpace hX (fun W hW w => GradedAlgebraPoints.F.point r (s.val W hW w))
    fun W W' hW hW' h w => (congrArg (GradedAlgebraPoints.F.point r)
      (s.compat W W' hW hW' h w)).symm

/-- The point of `X` underlying a point of the functor of quadruples. -/
def qcPoint {T : BigFppfOver B S hS} (s : SiteQcExtension ρ.functor T) : yoneda.obj T ⟶ X :=
  (ρ.existsUnique_point hX s).choose

/-- The restriction of `ρ.qcPoint hX s` along `w : W ⟶ T` is the point of `X` underlying the
element that `s` records at `w`. -/
theorem map_comp_qcPoint {T : BigFppfOver B S hS} (s : SiteQcExtension ρ.functor T)
    (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T) :
    yoneda.map w ≫ ρ.qcPoint hX s = GradedAlgebraPoints.F.point r (s.val W hW w) :=
  (ρ.existsUnique_point hX s).choose_spec.1 W hW w

/-- A point of the functor of quadruples, as a point of the limit with its glued point. -/
def qcToLimPoint {T : BigFppfOver B S hS} (s : SiteQcExtension ρ.functor T) : LimPoint ρ T where
  point := ρ.qcPoint hX s
  val W hW w := cast (congrArg (GradedAlgebraPoints.F.fibre r W)
    (ρ.map_comp_qcPoint hX s W hW w).symm) (s.val W hW w : r.F W).2
  compat W W' hW hW' h w := by
    have e1 := GradedAlgebraPoints.F.mk_cast r W (ρ.map_comp_qcPoint hX s W hW w).symm
      (s.val W hW w : r.F W).2
    have e2 := GradedAlgebraPoints.F.mk_cast r W' (ρ.map_comp_qcPoint hX s W' hW' (h ≫ w)).symm
      (s.val W' hW' (h ≫ w) : r.F W').2
    have key := (congrArg (ρ.FRestrict h) e1).trans ((s.compat W W' hW hW' h w).trans e2.symm)
    exact eq_of_heq (Sigma.mk.inj key).2

/-- **For a sheaf `X` the two presentations of the functor of quadruples agree**: a point of the
limit of the unions over the quasi-compact test objects is the same as a point of `X` together
with a compatible family of points of the fibres over its restrictions. -/
def limPointEquiv (T : BigFppfOver B S hS) : LimPoint ρ T ≃ SiteQcExtension ρ.functor T where
  toFun := ρ.limPointToQc
  invFun := ρ.qcToLimPoint hX
  left_inv ξ := by
    have hp : ρ.qcPoint hX (ρ.limPointToQc ξ) = ξ.point :=
      ((ρ.existsUnique_point hX (ρ.limPointToQc ξ)).unique
        (ρ.map_comp_qcPoint hX _) fun _ _ _ => rfl)
    exact LimPoint.ext' hp fun W hW w => cast_heq _ _
  right_inv s := by
    ext W hW w
    exact GradedAlgebraPoints.F.mk_cast r W (ρ.map_comp_qcPoint hX s W hW w).symm _

/-- The identification `limPointEquiv` commutes with restriction along `τ : T' ⟶ T`: it sends
`ξ.restrict τ` to the reindexing along `τ` of the image of `ξ`. -/
theorem limPointEquiv_restrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : LimPoint ρ T) :
    ρ.limPointEquiv hX T' (ξ.restrict τ) = (ρ.limPointEquiv hX T ξ).pullback τ := rfl

/-- **The two presentations of the functor of quadruples are isomorphic presheaves**, for a sheaf
`X`. -/
def limPointIso : ρ.limFunctor ≅ ρ.quadrupleFunctor :=
  NatIso.ofComponents (fun T => (ρ.limPointEquiv hX T.unop).toIso) fun _ => rfl

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
