module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductRefined

/-!
# The clopen decomposition along a coproduct of sheaves, in an arbitrary value universe

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 02WO** and **Stacks 0F15** say
that a section of a coproduct `P = ∐ᵢ Fᵢ` of sheaves over an object `W` of the big fppf site of
`S` decomposes `W` into pairwise disjoint open subobjects `W' i` covering `W`, the restriction
of the section to `W' i` coming from `Fᵢ`, and each `W' i` being universal with that property.
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` proves this for sheaves
with values in `Type u`, the value universe of the site. This file carries it over to the value
universe `max w u` with `w` independent of `u`, which is the generality in which a formal
algebraic space — a sheaf of `Type (u + 1)` — lives, and in which the coproducts occurring in
that theory are formed.

## Main results

* `AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan_ulift`:
  **Stacks 02WO** and **Stacks 0F15** for sheaves with values in `Type (max w u)`.
* `AlgebraicGeometry.Sheaf.injective_app_cofan_inj_ulift`,
  `AlgebraicGeometry.Sheaf.mono_hom_cofan_inj_bigFppfOver_ulift`,
  `AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver_ulift` and
  `AlgebraicGeometry.Sheaf.isEmpty_toScheme_of_eq_of_ne_ulift`: the legs are injective on
  sections, hence monomorphisms of presheaves and of sheaves, and distinct legs have disjoint
  images -- the disjointness half of **Stacks 02WO**, in the same value universe.

## Implementation notes

The decomposition machinery is not rebuilt one universe up: the sheaves involved are assumed
pointwise `u`-small, hence are universe lifts of sheaves of `Type u`
(`AlgebraicGeometry.Space.shrinkCompUliftFunctorIso`), and the statement is transported along
that lift. The smallness hypothesis is what an affine formal algebraic space supplies, through
the set-theoretic condition of Stacks 0AIS
(`AlgebraicGeometry.FormalSpace.small_of_satisfiesSetTheoreticCondition`); it is not a
cardinality argument about the site, whose cutoff is only a strong limit of uncountable
cofinality.

The shrink-and-descend step is not done here: it is
`AlgebraicGeometry.Space.exists_shrink_isColimit_cofan_of_small`, which also supplies the one thing
that is not automatic -- that the shrunk family still has the shrunk coproduct for its coproduct,
the category of sheaves of `Type u` on this site not being known to have coproducts at all.
Smallness of the coproduct is not a hypothesis either: it follows there from smallness of the
members and `u`-smallness of the index type.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 02WO in an arbitrary value universe -/

/-- **Stacks 02WO and Stacks 0F15 for sheaves with values in a universe `max w u` independent of
the universe `u` of the schemes.** A section `x` of a coproduct `P = ∐ᵢ Fᵢ` of pointwise
`u`-small sheaves over an object `W` of the big fppf site of `S`, the index type being
`u`-small, decomposes `W` into a family of pairwise disjoint open subobjects `W' i`, covering
`W`, such that `x` restricted to `W' i` comes from `Fᵢ`; and each `W' i` is universal with that
property.

This is `AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` with the value
universe of the sheaves decoupled from the universe of the morphisms of the site. The
decomposition machinery is not rebuilt: the sheaves are universe lifts of sheaves of `Type u`,
the coproduct cocone descends to those by
`AlgebraicGeometry.Space.exists_shrink_isColimit_cofan_of_small`, and the conclusion, which speaks
of objects of the site and of sections, transports back along the lift. -/
@[stacks 02WO "in an arbitrary value universe, for pointwise `u`-small sheaves and a `u`-small \
index type; the smallness hypotheses are absent from \
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`, which is the same \
statement in the value universe of the site", stacks 0F15 "in an arbitrary value universe"]
theorem Sheaf.exists_clopen_decomposition_of_isColimit_cofan_ulift {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hF : ∀ i, FunctorToTypes.Small.{u} (F i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (W : BigFppfOver B S hS) (x : P.obj.obj (op W)) :
    ∃ (W' : I → BigFppfOver B S hS) (p : ∀ i, W' i ⟶ W),
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ i, ∃ z : (F i).obj.obj (op (W' i)),
        (ι i).hom.app (op (W' i)) z = P.obj.map (p i).op x) ∧
      (∀ i i', i ≠ i' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (W' i))
        (y' : (BigFppfOver.toScheme B S hS).obj (W' i')),
        (BigFppfOver.toScheme B S hS).map (p i) y ≠
          (BigFppfOver.toScheme B S hS).map (p i') y') ∧
      (∀ w : (BigFppfOver.toScheme B S hS).obj W,
        ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ (i : I) (T : BigFppfOver B S hS) (t : T ⟶ W),
        (∃ z : (F i).obj.obj (op T), (ι i).hom.app (op T) z = P.obj.map t.op x) →
        ∃ t' : T ⟶ W' i, t' ≫ p i = t) := by
  classical
  obtain ⟨F₀, P₀, ι₀, eF, eP, ⟨hcolim⟩, hup, hdown⟩ :=
    Space.exists_shrink_isColimit_cofan_of_small B S hS hF ι hP
  let x₀ : P₀.obj.obj (op W) := (eP.inv.app (op W) x).down
  have hx₀ : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W),
      eP.hom.app (op T) (ULift.up (P₀.obj.map t.op x₀)) = P.obj.map t.op x := by
    intro T t
    calc eP.hom.app (op T) (ULift.up (P₀.obj.map t.op x₀))
        = eP.hom.app (op T)
            ((P₀.obj ⋙ uliftFunctor.{w}).map t.op (eP.inv.app (op W) x)) := rfl
      _ = P.obj.map t.op (eP.hom.app (op W) (eP.inv.app (op W) x)) :=
          NatTrans.naturality_apply eP.hom t.op (eP.inv.app (op W) x)
      _ = P.obj.map t.op x := by simp
  have hx₀' : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W),
      (eP.inv.app (op T) (P.obj.map t.op x)).down = P₀.obj.map t.op x₀ := by
    intro T t
    rw [NatTrans.naturality_apply eP.inv t.op x]
    rfl
  obtain ⟨W', p, hoi, hsec, hdisj, hcov, huniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι₀ hcolim W x₀
  refine ⟨W', p, hoi, fun i => ?_, hdisj, hcov, fun i T t hz => ?_⟩
  · obtain ⟨z₀, hz₀⟩ := hsec i
    refine ⟨(eF i).hom.app (op (W' i)) (ULift.up z₀), ?_⟩
    rw [hup i (op (W' i)) z₀, hz₀]
    exact hx₀ (W' i) (p i)
  · obtain ⟨z, hz⟩ := hz
    refine huniv i T t ⟨((eF i).inv.app (op T) z).down, ?_⟩
    rw [hdown i (op T) z, hz, hx₀' T t]

/-! ### Disjointness of a coproduct of sheaves in an arbitrary value universe -/

/-- **The legs of a coproduct cocone of pointwise `u`-small sheaves on the big fppf site of `S`
are injective on sections**, for a value universe independent of the universe of the objects of
the site.

This is `AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver` combined with
`CategoryTheory.Sheaf.injective_app_of_mono`, transported along the universe lift: the clopen
classifier that makes the legs monomorphisms is a sheaf in the value universe of the site only,
so the statement is read on the shrunk cofan and brought back up. -/
theorem Sheaf.injective_app_cofan_inj_ulift {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hF : ∀ i, FunctorToTypes.Small.{u} (F i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) (T : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((ι i₀).hom.app T) := by
  classical
  obtain ⟨F₀, P₀, ι₀, eF, eP, ⟨hcolim⟩, -, hdown⟩ :=
    Space.exists_shrink_isColimit_cofan_of_small B S hS hF ι hP
  have _ : Mono (ι₀ i₀) := Sheaf.mono_cofan_inj_bigFppfOver ι₀ hcolim i₀
  have h₀ : Function.Injective ((ι₀ i₀).hom.app T) :=
    CategoryTheory.Sheaf.injective_app_of_mono (ι₀ i₀) T.unop
  have hinv : Function.Injective ((eF i₀).inv.app T) :=
    ((isIso_iff_bijective ((eF i₀).inv.app T)).1 inferInstance).1
  intro a b hab
  refine hinv (ULift.ext _ _ ?_)
  refine h₀ ?_
  rw [hdown i₀ T a, hdown i₀ T b, hab]

/-- **The legs of a coproduct cocone of pointwise `u`-small sheaves on the big fppf site of `S`
are monomorphisms of presheaves**, for a value universe independent of the universe of the
objects of the site. This is the form in which a monomorphism is cancelled out of a pullback
square, by `CategoryTheory.MorphismProperty.relative_of_comp_mono`, the pullbacks of the theory
of algebraic spaces being formed in the presheaf category. -/
theorem Sheaf.mono_hom_cofan_inj_bigFppfOver_ulift {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hF : ∀ i, FunctorToTypes.Small.{u} (F i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) : Mono (ι i₀).hom :=
  (NatTrans.mono_iff_mono_app _).2 fun T =>
    (CategoryTheory.mono_iff_injective ((ι i₀).hom.app T)).2
      (Sheaf.injective_app_cofan_inj_ulift B S hS hF ι hP i₀ T)

/-- **The legs of a coproduct cocone of pointwise `u`-small sheaves on the big fppf site of `S`
are monomorphisms**, for a value universe independent of the universe of the objects of the
site. This is `AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver` with the value universe of
the sheaves decoupled from the universe of the morphisms of the site. -/
theorem Sheaf.mono_cofan_inj_bigFppfOver_ulift {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hF : ∀ i, FunctorToTypes.Small.{u} (F i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) : Mono (ι i₀) :=
  CategoryTheory.Sheaf.mono_of_injective (ι i₀) fun T =>
    Sheaf.injective_app_cofan_inj_ulift B S hS hF ι hP i₀ T

/-- **Distinct legs of a coproduct cocone of pointwise `u`-small sheaves on the big fppf site of
`S` have disjoint images**, for a value universe independent of the universe of the objects of
the site: an object of the site carrying sections of two different members of the family with the
same image in the coproduct has no points.

This is `AlgebraicGeometry.Sheaf.isEmpty_toScheme_of_eq_of_ne` with the value universe of the
sheaves decoupled from the universe of the morphisms of the site, and is the disjointness half
of Stacks 02WO there. -/
@[stacks 02WO "disjointness of the legs, in an arbitrary value universe"]
theorem Sheaf.isEmpty_toScheme_of_eq_of_ne_ulift {I : Type v} [Small.{u} I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hF : ∀ i, FunctorToTypes.Small.{u} (F i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) {i j : I} (hij : i ≠ j) {W : BigFppfOver B S hS}
    (x : (F i).obj.obj (op W)) (y : (F j).obj.obj (op W))
    (h : (ι i).hom.app (op W) x = (ι j).hom.app (op W) y) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj W) := by
  classical
  obtain ⟨F₀, P₀, ι₀, eF, eP, ⟨hcolim⟩, -, hdown⟩ :=
    Space.exists_shrink_isColimit_cofan_of_small B S hS hF ι hP
  refine Sheaf.isEmpty_toScheme_of_eq_of_ne ι₀ hcolim hij
    ((eF i).inv.app (op W) x).down ((eF j).inv.app (op W) y).down ?_
  rw [hdown i (op W) x, hdown j (op W) y, h]

end AlgebraicGeometry

end
