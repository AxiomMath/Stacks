module

public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Rigidity of morphisms out of an affine dominant cofiltered limit, at a free index universe

Mathlib's `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` — the
injective half of (1) ⇒ (3) of Stacks 01ZC — is stated for an index category at the scheme
universe. `StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean` frees that
coupling at the cost of `CategoryTheory.InitiallySmall.{u}` on the index, which is a genuine
cofinality restriction.

This file frees it with **no** hypothesis relating the index universe to the scheme universe, for
a system that is affine over a fixed base and whose limit projections are quasi-compact and
scheme-theoretically dominant. Such a system has a `u`-small subsystem with the same limit, by
`AlgebraicGeometry.exists_small_limit_of_affine_of_dominant`, and Mathlib's statement applies to
that subsystem.

## Main results

* `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_over`,
  for a system of schemes in an overcategory.
* `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant`, the
  same for a system of schemes with a natural family of affine morphisms to a fixed base. This is
  the form consumers want: it does not ask them to build a functor into an overcategory.

## Implementation notes

The base `S` over which the system is affine and the base `T` over which the target is of finite
type are kept distinct: in the application to Stacks 0CNR they are, respectively, the base change
of the model of the source's good diagram to the common stage and the stage of the target's good
diagram.

The two designated indices are absorbed by seeding
`AlgebraicGeometry.exists_small_limit_of_affine_of_dominant` with a common upper bound for them,
so that a single index of the small subsystem dominates both. No initiality or cofinality of the
small subsystem is used — only that its limit agrees.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC), the injective half of
  (1) ⇒ (3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **Stacks 01ZC, injective half, for an affine dominant system at a free index universe.**
Let `D` be an inverse system of schemes affine over `S`, indexed by the opposite of a directed
preorder `I` at a universe independent of the scheme universe, with quasi-compact
scheme-theoretically dominant limit projections and quasi-compact stages, and let `g : W ⟶ T` be
locally of finite type. Two morphisms into `W` from stages of the system, compatible with a
natural family of morphisms to `T` and agreeing after the limit projections, agree after a
transition of the system.

This is Mathlib's `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`
with the index universes freed and *no* smallness hypothesis on the index. -/
public theorem Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_over
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffineHom (D.obj i).hom] [IsAffineHom c.pt.hom]
    [∀ i, QuasiCompact (c.π.app i).left]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i).left]
    [∀ i, CompactSpace (D.obj i).left]
    {T W : Scheme.{u}} (τ : D ⋙ Over.forget S ⟶ (Functor.const Iᵒᵖ).obj T)
    (g : W ⟶ T) [LocallyOfFiniteType g]
    {i : I} (p : (D.obj (op i)).left ⟶ W) (hp : τ.app (op i) = p ≫ g)
    {j : I} (q : (D.obj (op j)).left ⟶ W) (hq : τ.app (op j) = q ≫ g)
    (hpq : (c.π.app (op i)).left ≫ p = (c.π.app (op j)).left ≫ q) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      (D.map (homOfLE hik).op).left ≫ p = (D.map (homOfLE hjk).op).left ≫ q := by
  classical
  obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
  obtain ⟨J, hJ, hne, hd, e, a, ha, ⟨hlim⟩⟩ :=
    exists_small_limit_of_affine_of_dominant (α := PUnit.{u + 1}) (fun _ => l) D c hc
  let := hJ
  let := hne
  let := hd
  let E := e.monotone.functor.op
  let A : Jᵒᵖ ⥤ Scheme.{u} := (E ⋙ D) ⋙ Over.forget S
  let c' : Cone A := (Over.forget S).mapCone (c.whisker E)
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget S) hlim
  have hAff : ∀ {x y : Jᵒᵖ} (b : x ⟶ y), IsAffineHom (A.map b) := by
    intro x y b
    change IsAffineHom ((D.map (E.map b)).left)
    have : IsAffineHom ((D.map (E.map b)).left ≫ (D.obj (E.obj y)).hom) := by
      rw [(D.map (E.map b)).w]
      infer_instance
    exact IsAffineHom.of_comp _ (D.obj (E.obj y)).hom
  have hCpt : ∀ x : Jᵒᵖ, CompactSpace (A.obj x) := fun x =>
    inferInstanceAs (CompactSpace (D.obj (E.obj x)).left)
  let τ' : A ⟶ (Functor.const Jᵒᵖ).obj T :=
    { app x := τ.app (E.obj x)
      naturality := fun x y b => τ.naturality (E.map b) }
  -- The seeded index of the small subsystem dominates both designated indices.
  have hel : e (a PUnit.unit) = l := congrFun ha PUnit.unit
  have hik₀ : i ≤ e (a PUnit.unit) := hel ▸ hil
  have hjk₀ : j ≤ e (a PUnit.unit) := hel ▸ hjl
  have hτ' {n : I} (r : (D.obj (op n)).left ⟶ W) (hr : τ.app (op n) = r ≫ g)
      (hm : n ≤ e (a PUnit.unit)) :
      τ'.app (op (a PUnit.unit)) = ((D.map (homOfLE hm).op).left ≫ r) ≫ g := by
    have h := τ.naturality ((homOfLE hm).op)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Functor.comp_map,
      Over.forget_map] at h
    rw [Category.assoc, ← hr]
    exact h.symm
  have hcw {n m : I} (hm : n ≤ m) :
      (c.π.app (op m)).left ≫ (D.map (homOfLE hm).op).left = (c.π.app (op n)).left :=
    congrArg (fun h : c.pt ⟶ D.obj (op n) => h.left) (c.w ((homOfLE hm).op))
  obtain ⟨m, him, hjm, hm⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    A τ' g c' hc'
    (i := op (a PUnit.unit)) ((D.map (homOfLE hik₀).op).left ≫ p)
    (hτ' p hp hik₀)
    (j := op (a PUnit.unit)) ((D.map (homOfLE hjk₀).op).left ≫ q)
    (hτ' q hq hjk₀)
    (by
      rw [show c'.π.app (op (a PUnit.unit)) = (c.π.app (op (e (a PUnit.unit)))).left from rfl,
        ← Category.assoc, ← Category.assoc, hcw hik₀, hcw hjk₀, hpq])
  refine ⟨e (unop m), hik₀.trans (e.monotone (leOfHom him.unop)),
    hjk₀.trans (e.monotone (leOfHom hjm.unop)), ?_⟩
  have hh {n : I} (hn : n ≤ e (a PUnit.unit)) {x : Jᵒᵖ} (r : x ⟶ op (a PUnit.unit)) :
      D.map (homOfLE (hn.trans (e.monotone (leOfHom r.unop)))).op =
        D.map (E.map r) ≫ D.map (homOfLE hn).op := by
    rw [← D.map_comp]
    rfl
  rw [hh hik₀ him, hh hjk₀ hjm]
  simpa only [Over.comp_left, Category.assoc, A, Functor.comp_map, Over.forget_map] using hm

attribute [local instance] IsCofiltered.isConnected in
/-- **Stacks 01ZC, injective half, for an affine dominant system at a free index universe.**
The same statement as
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_over`
for a system of plain schemes together with a natural family `ρ` of affine morphisms to a fixed
base `S`, compatible with an affine morphism `ρc` out of the limit vertex.

Every condition on the system is an explicit hypothesis rather than an instance argument, since
at a consumer the system is typically a whiskered diagram and instance search does not reduce
through `CategoryTheory.Limits.Cone.whisker`. -/
public theorem Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (ρ : D ⟶ (Functor.const Iᵒᵖ).obj S) (ρc : c.pt ⟶ S)
    (hρc : ∀ x, c.π.app x ≫ ρ.app x = ρc)
    (hAff : ∀ x, IsAffineHom (ρ.app x)) (hAffc : IsAffineHom ρc)
    (hqc : ∀ x, QuasiCompact (c.π.app x))
    (hdom : ∀ x, IsSchemeTheoreticallyDominant (c.π.app x))
    (hcpt : ∀ x, CompactSpace (D.obj x))
    {T W : Scheme.{u}} (τ : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (g : W ⟶ T) (hg : LocallyOfFiniteType g)
    {i : I} (p : D.obj (op i) ⟶ W) (hp : τ.app (op i) = p ≫ g)
    {j : I} (q : D.obj (op j) ⟶ W) (hq : τ.app (op j) = q ≫ g)
    (hpq : c.π.app (op i) ≫ p = c.π.app (op j) ≫ q) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      D.map (homOfLE hik).op ≫ p = D.map (homOfLE hjk).op ≫ q := by
  classical
  let := hg
  let D' : Iᵒᵖ ⥤ Over S :=
    { obj x := Over.mk (ρ.app x)
      map {x y} a := Over.homMk (D.map a) (by simp)
      map_id x := Over.OverMorphism.ext (by simp)
      map_comp a b := Over.OverMorphism.ext (by simp) }
  let c' : Cone D' :=
    { pt := Over.mk ρc
      π :=
        { app x := Over.homMk (c.π.app x) (hρc x)
          naturality := fun x y a => Over.OverMorphism.ext (c.w a).symm } }
  have hc' : IsLimit c' := isLimitOfReflects (Over.forget S) hc
  have h₁ : ∀ x, IsAffineHom (D'.obj x).hom := hAff
  have h₂ : IsAffineHom c'.pt.hom := hAffc
  have h₃ : ∀ x, QuasiCompact (c'.π.app x).left := hqc
  have h₄ : ∀ x, IsSchemeTheoreticallyDominant (c'.π.app x).left := hdom
  have h₅ : ∀ x, CompactSpace (D'.obj x).left := hcpt
  let τ' : D' ⋙ Over.forget S ⟶ (Functor.const Iᵒᵖ).obj T :=
    { app x := τ.app x
      naturality := fun x y a => τ.naturality a }
  exact Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_over D' c' hc' τ' g
    (i := i) p hp (j := j) q hq hpq

end AlgebraicGeometry

end
