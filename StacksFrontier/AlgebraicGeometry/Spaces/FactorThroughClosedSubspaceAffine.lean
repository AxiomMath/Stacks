module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace

/-!
# Factoring through a closed subspace, tested on affine charts only

`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le` states Stacks 03MB with its
vanishing condition read on *every* étale scheme chart of `X`, and with the *ideal sheaf* of
the closed immersion `Z ×_X U ⟶ U` on the right-hand side.  On a non-affine chart the ideal
sheaf is genuinely more information than its ideal of global sections, so that form of the
criterion cannot be restated with `AlgebraicGeometry.Space.definingIdealAt` without losing
content, and the notes of that file say so.

Restricting the charts to the *affine* ones removes the difficulty: over an affine base an
ideal sheaf of a closed immersion is recovered from its global sections
(`AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine`), so the condition becomes an
inclusion of ideals of rings of regular functions.  This file proves the criterion in that
form.  Its vanishing half is already
`AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`, which holds on an arbitrary
chart; what is proved here is the converse, whose hypothesis is now weaker than the one the
unrestricted criterion assumes, since it says nothing about non-affine charts.

The missing step is purely one of coverings.  The reverse direction of
`exists_comp_eq_iff_forall_ker_le` checks membership in `Z` after the surjective étale base
change of a *single* chart supplied by `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`,
which is an arbitrary scheme.  Here the chart is taken from
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas` instead: it is a disjoint
union of affine charts `W i`, each of which is an object of the big fppf category over `S`
sitting in the chart by an open immersion, and each of which is itself an étale chart of `X`.
The base change of a point of `X` by that chart is then covered by the preimages of the `W i`,
and over each of those the point factors through an affine chart, where
`AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le` applies.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Scheme.exists_mem_range_of_coproductIso`: a family of morphisms into a
  scheme identified with the coproduct inclusions of its sources is jointly surjective.
* `AlgebraicGeometry.BigFppfOver.exists_openCover_lift_of_isOpenImmersion`: **the covering
  step.** Given a jointly surjective family of open immersions `j i : W i ⟶ U` of the big
  fppf category over `S` and a morphism `φ : P ⟶ U`, the object `P` has an open covering by
  objects `Q i` of the category, indexed by the same type, such that `Q i ⟶ P` composed with
  `φ` factors through `j i`.
* `AlgebraicGeometry.Space.map_op_app_eq_app_comp`: restricting a point of a presheaf coming
  from a represented chart is precomposition in the site.
* `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le` is **Stacks
  03MB** with the vanishing condition quantified over the affine étale charts only, and
  written with `AlgebraicGeometry.Space.definingIdealAt`.

## Implementation notes

No `@[stacks 03MB]` attribute is added.  The factorization criterion of Tag 03MB, with the
vanishing of `h^*𝓘 ⟶ 𝒪_Y` as its right-hand side, is part of
`AlgebraicGeometry.Space.closedImmersion_quasicoherentIdeal_correspondence`
(`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionIdealCorrespondence.lean`), which is
proved from the theorem here.

The `Q i` of the covering step are the preimages under `φ` of the images of the `j i`, taken
as open subschemes of the scheme underlying `P`.  No cardinal arithmetic is involved and no
regularity of the site's cutoff is used: an open subscheme of an object of the site is again
an object of the site by `AlgebraicGeometry.BigFppfSite.contains_coe_opens`, and the covering
sieve it generates is a covering sieve of the fppf topology by
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`, whose index type is
unrestricted.  The two morphisms out of `Q i` are produced from the underlying morphisms of
schemes — the open immersion of the preimage, and Mathlib's
`AlgebraicGeometry.IsOpenImmersion.lift` — by
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`.

Several steps are written with `congrArg` and explicit associativity rather than `rw`.  The
underlying scheme of `Q i` is definitionally the open subscheme but not syntactically equal to
it, and the base change object of a relatively representable morphism depends on the morphism
being based changed, so the motive of a rewrite in either position fails to typecheck.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Joint surjectivity of a family presenting a coproduct -/

/-- A family of morphisms `g i : Y i ⟶ T` of schemes which, under an isomorphism of `T` with
the coproduct of the `Y i`, becomes the family of coproduct inclusions is jointly surjective:
every point of `T` is in the image of some `g i`. -/
theorem Scheme.exists_mem_range_of_coproductIso {I : Type u} (Y : I → Scheme.{u})
    (T : Scheme.{u}) (e : (∐ Y) ≅ T) (g : ∀ i, Y i ⟶ T)
    (hg : ∀ i, Sigma.ι Y i ≫ e.hom = g i) (x : T) :
    ∃ i, x ∈ Set.range (g i) := by
  rcases hiz : (sigmaMk Y).symm (e.inv.base x) with ⟨i, z⟩
  refine ⟨i, z, ?_⟩
  have hz : Sigma.ι Y i z = e.inv.base x := by
    rw [← sigmaMk_mk Y i z, ← hiz, Homeomorph.apply_symm_apply]
  rw [← hg i, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering a base change by the members of an open covering -/

/-- **An open covering of an object of the big fppf category over `S` pulls back to an open
covering of any object over it, compatibly with lifts.** Let `j i : W i ⟶ U` be a family of
morphisms of the big fppf category over `S` whose underlying morphisms of schemes are open
immersions covering `U`, and let `φ : P ⟶ U`. Then there are objects `Q i` of the category,
indexed by the same type, open immersions `π i : Q i ⟶ P` generating a covering sieve of `P`,
and morphisms `ψ i : Q i ⟶ W i` with `ψ i ≫ j i = π i ≫ φ`.

The `Q i` are the preimages `φ ⁻¹ᵁ (j i).opensRange` as open subschemes of the scheme under
`P`; the `ψ i` are the universal property of the open immersion `j i`. -/
theorem BigFppfOver.exists_openCover_lift_of_isOpenImmersion
    {I : Type v} {W : I → BigFppfOver B S hS} {U P : BigFppfOver B S hS}
    (j : ∀ i, W i ⟶ U)
    (hj : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)))
    (φ : P ⟶ U) :
    ∃ (Q : I → BigFppfOver B S hS) (π : ∀ i, Q i ⟶ P) (ψ : ∀ i, Q i ⟶ W i),
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π i))) ∧
        Sieve.ofArrows Q π ∈ BigFppfOver.topology B S hS P ∧
        ∀ i, ψ i ≫ j i = π i ≫ φ := by
  have := hj
  set Vo : I → ((BigFppfOver.toScheme B S hS).obj P).Opens := fun i =>
    (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map (j i)).opensRange with hVo
  set Q : I → BigFppfOver B S hS := fun i =>
    BigFppfOver.mk B S hS (B.contains_coe_opens P.left.2 (Vo i))
      ((Vo i).ι ≫ B.inclusion.map P.hom) with hQ
  have hw : ∀ {A A' : BigFppfOver B S hS} (m : A ⟶ A'),
      (BigFppfOver.toScheme B S hS).map m ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom :=
    fun m => (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w m))
  have hπ : ∀ i, ∃ p : Q i ⟶ P, (BigFppfOver.toScheme B S hS).map p = (Vo i).ι := fun i =>
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := Q i) (Y := P) (Vo i).ι rfl
  choose π hπmap using hπ
  have hrange : ∀ i, Set.range ((Vo i).ι ≫ (BigFppfOver.toScheme B S hS).map φ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    rintro i _ ⟨y, rfl⟩
    exact y.2
  set χ : ∀ i, (↑(Vo i) : Scheme.{u}) ⟶ (BigFppfOver.toScheme B S hS).obj (W i) := fun i =>
    IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map (j i))
      ((Vo i).ι ≫ (BigFppfOver.toScheme B S hS).map φ) (hrange i) with hχ
  have hfac : ∀ i, χ i ≫ (BigFppfOver.toScheme B S hS).map (j i) =
      (Vo i).ι ≫ (BigFppfOver.toScheme B S hS).map φ := fun i =>
    IsOpenImmersion.lift_fac _ _ (hrange i)
  have hqw : ∀ i, χ i ≫ B.inclusion.map (W i).hom =
      (Vo i).ι ≫ B.inclusion.map P.hom := fun i => by
    rw [← hw (j i), ← Category.assoc, hfac i, Category.assoc, hw φ]
  have hψ : ∀ i, ∃ q : Q i ⟶ W i, (BigFppfOver.toScheme B S hS).map q = χ i := fun i =>
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := Q i) (Y := W i) (χ i) (hqw i)
  choose ψ hψmap using hψ
  have hπimm : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π i)) := fun i => by
    rw [hπmap i]
    exact (inferInstance : IsOpenImmersion (Vo i).ι)
  refine ⟨Q, π, ψ, hπimm, ?_, fun i => ?_⟩
  · refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π hπimm fun x => ?_
    obtain ⟨i, hi⟩ := hcov ((BigFppfOver.toScheme B S hS).map φ x)
    refine ⟨i, ?_⟩
    have hrng : Set.range ((BigFppfOver.toScheme B S hS).map (π i)) =
        (↑(Vo i) : Set ((BigFppfOver.toScheme B S hS).obj P)) := by
      rw [hπmap i]
      exact Scheme.Opens.range_ι (Vo i)
    rw [hrng]
    exact hi
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact (congrArg (fun m => m ≫ (BigFppfOver.toScheme B S hS).map (j i)) (hψmap i)).trans
      ((hfac i).trans
        (congrArg (fun m => m ≫ (BigFppfOver.toScheme B S hS).map φ) (hπmap i)).symm)

namespace Space

/-! ### Stacks 03MB on affine charts -/

/-- Restricting a point of a presheaf which comes from a scheme chart along a morphism of the
big fppf category over `S` is precomposition with that morphism in the site. -/
theorem map_op_app_eq_app_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c a V : BigFppfOver B S hS} (g : yoneda.obj c ⟶ F) (m : V ⟶ a) (k : a ⟶ c) :
    F.map m.op (g.app (op a) k) = g.app (op V) (m ≫ k) := by
  rw [← g.naturality_apply (f := m.op) (x := k)]
  rfl

/-- **Stacks 03MB, with the vanishing condition read on the affine charts only.** A morphism
`h : Y ⟶ X` of algebraic spaces over `S` factors through a closed subspace `Z ⊆ X` exactly
when, for every *affine* étale scheme chart `U` of `X` and every point of `Y` over an object
`a` of the site whose image in `X` factors through `U` by `k : a ⟶ U`, the defining ideal
`AlgebraicGeometry.Space.definingIdealAt` of `Z` at `U` is killed by pullback of regular
functions along `k`.

The condition is weaker than the one of
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le`, which quantifies over every chart
and asks for an inclusion of ideal *sheaves*: on an affine chart the two agree by
`AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine`, and on a non-affine chart nothing is
assumed here at all.  The vanishing half is
`AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`, which holds on an arbitrary
chart.  The converse replaces the atlas of
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` by the disjoint union of affine charts of
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas` and covers the base change
of a point of `X` by the affine summands, using
`AlgebraicGeometry.BigFppfOver.exists_openCover_lift_of_isOpenImmersion`. -/
theorem exists_comp_eq_iff_forall_isAffine_definingIdealAt_le
    (X Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (h : Y ⟶ X) :
    (∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = h) ↔
      ∀ (U : SmallEtale B S hS X.1),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        ∀ (a : BigFppfOver B S hS) (k : a ⟶ U.1.left) (y : yoneda.obj a ⟶ Y.1),
          yoneda.map k ≫ U.1.hom = y ≫ h.hom →
            definingIdealAt B S hS X Z (op U) ≤
              RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom := by
  refine ⟨fun ⟨g, hg⟩ U _ a k y hy =>
    definingIdealAt_le_ker_of_comp_eq B S hS X Y Z h g hg U k y hy, fun hker => ?_⟩
  have hrange : Subfunctor.range h.hom ≤ Z.1 := by
    rintro T _ ⟨x₀, rfl⟩
    obtain ⟨UX, f, I, W, jj, e, hfS, hfE, hWaff, hje, hjimm, hjetale, -⟩ :=
      IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X.1 X.2
    have hjcov : ∀ x : (BigFppfOver.toScheme B S hS).obj UX,
        ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (jj i)) :=
      Scheme.exists_mem_range_of_coproductIso _ _ e _ hje
    set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm (h.hom.app T x₀) with hτ
    have hτ' : τ = yonedaEquiv.symm x₀ ≫ h.hom := by
      rw [hτ]
      exact yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply])
    refine mem_obj_of_surjective_etale B S hS X.2.isSheaf Z.1 Z.2.1.isSheaf
      (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
    have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ := by
      rw [hfE.rep.map_fst' τ]
      exact hfE.rep.w τ
    have hval : X.1.map (hfE.rep.snd τ).op (h.hom.app T x₀) =
        f.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
      rw [← yonedaEquiv_yoneda_map_comp B S hS f (hfE.rep.fst' τ), hw,
        ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
    rw [hval]
    obtain ⟨Q, π, ψ, hπimm, hsieve, hcomm⟩ :=
      BigFppfOver.exists_openCover_lift_of_isOpenImmersion B S hS jj hjimm hjcov
        (hfE.rep.fst' τ)
    refine mem_obj_of_sieve_le B S hS X.2.isSheaf Z.1 Z.2.1.isSheaf _ _ hsieve ?_
    rintro V m ⟨_, l, p, ⟨i⟩, rfl⟩
    set Uaff : SmallEtale B S hS X.1 :=
      ⟨CostructuredArrow.mk (yoneda.map (jj i) ≫ f), hjetale i⟩
    have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj Uaff.1.left) := hWaff i
    have hkey : (l ≫ π i) ≫ hfE.rep.fst' τ = (l ≫ ψ i) ≫ jj i := by
      rw [Category.assoc, ← hcomm i, Category.assoc]
    rw [map_op_app_eq_app_comp, hkey]
    show Uaff.1.hom.app (op V) (l ≫ ψ i) ∈ Z.1.obj (op V)
    rw [mem_obj_iff_definingIdealAt_le]
    refine hker Uaff haff V (l ≫ ψ i)
      (yoneda.map (l ≫ π i) ≫ yoneda.map (hfE.rep.snd τ) ≫ yonedaEquiv.symm x₀) ?_
    have h1 : yoneda.map (l ≫ ψ i) ≫ Uaff.1.hom =
        yoneda.map (l ≫ π i) ≫ yoneda.map (hfE.rep.snd τ) ≫ τ := by
      rw [show Uaff.1.hom = yoneda.map (jj i) ≫ f from rfl, ← Category.assoc,
        ← Functor.map_comp, ← hkey, Functor.map_comp, Category.assoc, hw]
    refine h1.trans ((congrArg (fun t : yoneda.obj T.unop ⟶ X.1 =>
        yoneda.map (l ≫ π i) ≫ yoneda.map (hfE.rep.snd τ) ≫ t) hτ').trans ?_)
    simp only [Category.assoc]
  refine ⟨ObjectProperty.homMk (Subfunctor.lift h.hom hrange), ?_⟩
  apply ObjectProperty.hom_ext
  exact Subfunctor.lift_ι h.hom hrange

end Space

end AlgebraicGeometry

end
