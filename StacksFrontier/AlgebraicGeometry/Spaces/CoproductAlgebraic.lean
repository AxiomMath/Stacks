module

public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition

/-!
# A coproduct of algebraic spaces is an algebraic space

Let `G` be a coproduct, in the category of sheaves of sets on the big fppf site over a scheme
`S`, of a family of algebraic spaces `F i` over `S`, and suppose that chosen surjective étale
scheme atlases `f i : yoneda.obj (U i) ⟶ F i` have a coproduct `V` *inside the site*. This file
proves Stacks 02WQ: `G` is again an algebraic space over `S`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_section_of_disjoint_openCover`: sections of a sheaf
  glue along a family of pairwise disjoint open subobjects covering the base, with no
  compatibility hypothesis.
* `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_size_le`: a family of objects of the site
  indexed by a type of the working universe and of uniformly bounded size has a disjoint union
  inside the site.
* `AlgebraicGeometry.BigFppfOver.exists_factor_of_range_le` and
  `AlgebraicGeometry.BigFppfOver.hom_ext_of_openCover`: a morphism of the site whose image lies
  in an open subobject factors through it, and a morphism of the site is determined by its
  restrictions to an open cover of its source.
* `AlgebraicGeometry.isPullback_yoneda_map_of_isColimit_cofan`: `U i₀` is the fibre product of
  the coproduct `V` of the atlases with the `i₀`-th member `F i₀` over `G`.
* `AlgebraicGeometry.exists_isPullback_of_isColimit_cofan`: the fibre product of two
  representable presheaves over `G` is representable by an object of the site.
* `AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`: the diagonal of `G` is
  representable.
* `AlgebraicGeometry.presheaf_inverseImage_of_isColimit_cofan`: the glued chart
  `yoneda.obj V ⟶ G` inherits from the `f i` any property of scheme morphisms which is Zariski
  local at the target.
* `AlgebraicGeometry.isAlgebraicSpace_coproduct` is Stacks 02WQ.

## Implementation notes

The geometric input is Stacks 02WO in the form proved in
`StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition`: a section of `G` over an object
`W` of the site decomposes `W` into pairwise disjoint open subobjects `W' i` covering `W`, over
which the section comes from `F i`, each universal with that property. Both clauses of
Stacks 025Y are then checked piece by piece.

For the diagonal, representability is reduced by
`CategoryTheory.Functor.relativelyRepresentable.diag_of_map_from_obj` to representability of
every morphism `yoneda.obj a ⟶ G`, that is, to representability of the fibre product of two
sections `g` over `a` and `k` over `c`. Decomposing `a` and `c` splits that fibre product into
the fibre products `R i` of the `i`-th pieces over `F i`, which are representable because the
diagonal of `F i` is, and the `R i` have to be assembled into a single object of the site. This
is where the *size* cutoff of the site enters, and it is the delicate
step: `AlgebraicGeometry.Scheme.size_sigmaObj_lt` bounds a coproduct only for a countable
index type, while the pieces are indexed by a set of disjoint opens of `a`, which can be
uncountable. What makes it work is that each `R i ⟶ a ⨯ c` is a *monomorphism*, being a base
change of the diagonal of `F i`, together with the uniform bound
`AlgebraicGeometry.Scheme.size_le_of_mono`, whose right-hand side `max (2 ^ #Y) (size Y)` does
not mention the source; `AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit`
puts that bound below the cutoff because the cutoff is a strong prelimit. Only the pieces with
a point contribute, and these inject into the points of `a`, which bounds the index type; the
assembly is then `AlgebraicGeometry.schemeSize_coproduct_le`, which carries *no* cofinality
hypothesis. In particular `AlgebraicGeometry.isRepresentable_of_zariskiCover`, whose cofinality
hypothesis `#ι < B.cutoff.ord.cof` would not be available here, is not used.

Monomorphy of `R i ⟶ a ⨯ c` is first established in the site and then transported to schemes.
That direction is not automatic for a full subcategory — a morphism can be a monomorphism in
the site without being one in all of `Scheme` — but it does follow from preservation of fibre
products, which is `CategoryTheory.preserves_mono_of_preservesLimit`: being a monomorphism is the
condition that the two projections of the fibre square with itself agree.

For the atlas, the glued morphism `v : yoneda.obj V ⟶ G` of Stacks 02WO is representable as
soon as the diagonal is, so no further size argument is needed; what has to be checked is that
each represented base change of `v` is surjective and étale. This is done Zariski-locally on
the test object, using the decomposition again: over the `i`-th piece the base change of `v`
*is* a base change of `f i`, because `U i` is the fibre of `V` over `F i`. That last statement,
`AlgebraicGeometry.isPullback_yoneda_map_of_isColimit_cofan`, is the only place where the
coproduct `V` is used, and its proof is where disjointness of the legs `ι i` of the sheaf cofan
is consumed: a morphism `T ⟶ V` whose image in `G` comes from `F i₀` has image inside `U i₀`,
because the part of `T` over any other `U k` would carry sections of two different members with
the same image in `G`, hence have no points.

Surjectivity and étaleness are both handled by the single statement
`AlgebraicGeometry.presheaf_inverseImage_of_isColimit_cofan`, parameterized by a property of
scheme morphisms which is Zariski local at the target. For `AlgebraicGeometry.Etale` the
instance has to be supplied by hand, as
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`, since typeclass inference
does not unify it with the goal.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe w v₁ u₁ v u

namespace AlgebraicGeometry

section Pieces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Glueing along a disjoint open cover of an object of the site -/

/-- A morphism of the site whose image in schemes is an open immersion is a monomorphism. -/
private theorem mono_of_isOpenImmersion_map {X Y : BigFppfOver B S hS} (p : X ⟶ Y)
    (hp : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p)) : Mono p :=
  have := hp
  (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)

/-- A map out of a representable presheaf is determined by its value at the identity. -/
private theorem app_eq_map_app_id {a : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : yoneda.obj a ⟶ P) {T : BigFppfOver B S hS}
    (s : T ⟶ a) : m.app (op T) s = P.map s.op (m.app (op a) (𝟙 a)) := by
  simpa using NatTrans.naturality_apply m s.op (𝟙 a)

/-- Representable presheaves are sheaves of types for the topology of the site. -/
private theorem isSheaf_yoneda_obj_type (X : BigFppfOver B S hS) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS X)

/-- The legs of a colimit cofan of sheaves are injective on sections over every object. -/
private theorem injective_app_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) (i : I) (T : BigFppfOver B S hS) :
    Function.Injective ((ι i).hom.app (op T)) :=
  have := Sheaf.mono_cofan_inj_bigFppfOver ι hG i
  CategoryTheory.Sheaf.injective_app_of_mono (ι i) T

/-- If a section `x` restricts along `p` to the image of a section `z` of a member, then every
restriction of `x` along `e ≫ p` is the image of the corresponding restriction of `z`. -/
private theorem map_comp_section_eq {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G) (i : I)
    {a A T : BigFppfOver B S hS} {x : G.obj.obj (op a)} {z : (F i).obj.obj (op A)} (p : A ⟶ a)
    (hz : (ι i).hom.app (op A) z = G.obj.map p.op x) (e : T ⟶ A) :
    G.obj.map (e ≫ p).op x = (ι i).hom.app (op T) ((F i).obj.map e.op z) := by
  rw [op_comp, Functor.map_comp_apply, ← hz,
    ← NatTrans.naturality_apply (ι i).hom e.op z]

/-- **Sections of a sheaf glue along a family of pairwise disjoint open subobjects covering
the base.** No compatibility hypothesis is needed: two members of the family meet only in an
object with no points, over which every sheaf takes a one-element value. -/
theorem BigFppfOver.exists_section_of_disjoint_openCover
    {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : Presieve.IsSheaf (BigFppfOver.topology B S hS) H)
    {K : Type w} {T : BigFppfOver B S hS} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hdisj : ∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (W k))
      (y' : (BigFppfOver.toScheme B S hS).obj (W k')),
      (BigFppfOver.toScheme B S hS).map (p k) y ≠
        (BigFppfOver.toScheme B S hS).map (p k') y')
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (σ : ∀ k, H.obj (op (W k))) :
    ∃ τ : H.obj (op T), ∀ k, H.map (p k).op τ = σ k := by
  classical
  have hindep : ∀ (T' : BigFppfOver B S hS) (k k' : K) (h : T' ⟶ W k) (h' : T' ⟶ W k'),
      h ≫ p k = h' ≫ p k' → H.map h.op (σ k) = H.map h'.op (σ k') := by
    intro T' k k' h h' hcomp
    by_cases hkk' : k = k'
    · subst hkk'
      have := mono_of_isOpenImmersion_map (p k) (hoi k)
      rw [(cancel_mono (p k)).1 hcomp]
    · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj T') := by
        refine ⟨fun y => ?_⟩
        have h1 := congrArg
          (fun m : (BigFppfOver.toScheme B S hS).obj T' ⟶
            (BigFppfOver.toScheme B S hS).obj T => m y)
          (congrArg (BigFppfOver.toScheme B S hS).map hcomp)
        simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h1
        exact hdisj k k' hkk' _ _ h1
      exact (hH.subsingleton_obj_of_bot_mem _
        (BigFppfOver.bot_mem_topology T' hempty)).elim _ _
  have hcovT : Sieve.ofArrows W p ∈ BigFppfOver.topology B S hS T :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hoi hcov
  have hchoice : ∀ (T' : BigFppfOver B S hS) (g : T' ⟶ T), (Sieve.ofArrows W p).arrows g →
      ∃ y : H.obj (op T'), ∀ (k : K) (h : T' ⟶ W k), h ≫ p k = g →
        y = H.map h.op (σ k) := by
    rintro T' g ⟨Z, h, e, ⟨k⟩, hcomp⟩
    exact ⟨H.map h.op (σ k), fun k' h' hh' => hindep T' k k' h h' (hcomp.trans hh'.symm)⟩
  choose yy hyy using hchoice
  set fam : Presieve.FamilyOfElements H (Sieve.ofArrows W p).arrows :=
    fun T' g hg => yy T' g hg with hfamdef
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T' T'' g u hg
    obtain ⟨Z, h, e, ⟨k⟩, hcomp⟩ := id hg
    simp only [hfamdef]
    rw [hyy T' g hg k h hcomp,
      hyy T'' (u ≫ g) ((Sieve.ofArrows W p).downward_closed hg u) k (u ≫ h)
        (by rw [Category.assoc, hcomp]),
      ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨τ, hτ, -⟩ := hH _ hcovT fam hcompat
  refine ⟨τ, fun k => ?_⟩
  refine (hτ (p k) ⟨W k, 𝟙 (W k), p k, ⟨k⟩, Category.id_comp _⟩).trans ?_
  simp only [hfamdef]
  exact (hyy (W k) (p k) _ k (𝟙 (W k)) (Category.id_comp _)).trans (by simp)

/-! ### Coproducts of bounded families in the site -/

/-- **A family of objects of the big fppf site over `S`, indexed by a type of the working
universe and of uniformly bounded size, has a disjoint union inside the site.**

The disjoint union of the underlying schemes carries the structure morphism assembled from
those of the members, and its size is bounded by `AlgebraicGeometry.schemeSize_coproduct_le`,
so it is an object of the site. The members sit inside it as pairwise disjoint open
subobjects which cover it. -/
theorem BigFppfOver.exists_coproduct_of_size_le (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {K : Type u} (R : K → BigFppfOver B S hS) {μ : Cardinal.{u}}
    (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hsize : ∀ k, ((BigFppfOver.toScheme B S hS).obj (R k)).size ≤ μ) :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k, R k ⟶ Z),
      (∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c k))) ∧
      (∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (R k))
        (y' : (BigFppfOver.toScheme B S hS).obj (R k')),
        (BigFppfOver.toScheme B S hS).map (c k) y ≠
          (BigFppfOver.toScheme B S hS).map (c k') y') ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj Z,
        ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c k))) := by
  set Y : K → Scheme.{u} := fun k => (BigFppfOver.toScheme B S hS).obj (R k) with hYdef
  have hZsize : (∐ Y).size < B.cutoff :=
    (schemeSize_coproduct_le Y μ hℵ hK hsize).trans_lt hμ
  set τ : (∐ Y) ⟶ S := Sigma.desc fun k => B.inclusion.map (R k).hom with hτdef
  set Z : BigFppfOver B S hS := Over.mk (B.inclusion.preimage
    (X := B.obj hZsize) (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hZsize) ⟶ B.inclusion.obj (B.obj hS) from τ)) with hZdef
  have hZhom : B.inclusion.map Z.hom = τ := B.inclusion.map_preimage _
  have hc : ∀ k, ∃ ψ : R k ⟶ Z, (BigFppfOver.toScheme B S hS).map ψ = Sigma.ι Y k := by
    intro k
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := R k) (Y := Z) (Sigma.ι Y k) ?_
    rw [hZhom, hτdef, Sigma.ι_desc]
  choose c hcmap using hc
  refine ⟨Z, c, fun k => ?_, fun k k' hkk' y y' => ?_, fun z => ?_⟩
  · rw [hcmap k]
    infer_instance
  · rw [hcmap k, hcmap k']
    intro hy
    exact hkk' (congrArg Sigma.fst ((sigmaι_eq_iff Y k k' y y').1 hy))
  · obtain ⟨k, hk⟩ :=
      ((Scheme.presieve₀_mem_precoverage_iff _).1 (sigmaOpenCover Y).mem₀).1 z
    refine ⟨k, ?_⟩
    rw [hcmap k, ← sigmaOpenCover_f Y k]
    exact hk

/-! ### Factoring through an open subobject of the site -/

/-- A morphism of the big fppf site over `S` whose image lies in the image of an open
immersion of the site factors through that open immersion, uniquely. -/
theorem BigFppfOver.exists_factor_of_range_le {U V T : BigFppfOver B S hS} (i : U ⟶ V)
    (hi : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)) (g : T ⟶ V)
    (hr : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map i)) :
    ∃ l : T ⟶ U, l ≫ i = g := by
  have := hi
  have hw : ∀ {X Y : BigFppfOver B S hS} (m : X ⟶ Y),
      (BigFppfOver.toScheme B S hS).map m ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom := by
    intro X Y m
    have h := congrArg B.inclusion.map (Over.w m)
    rwa [B.inclusion.map_comp] at h
  have hφ := IsOpenImmersion.lift_fac ((BigFppfOver.toScheme B S hS).map i)
    ((BigFppfOver.toScheme B S hS).map g) hr
  obtain ⟨ψ, hψ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := T) (Y := U)
    (IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map g) hr)
    (by rw [← hw i, ← Category.assoc, hφ, hw g])
  refine ⟨ψ, (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  rw [Functor.map_comp, hψ, hφ]

/-- Two morphisms of the big fppf site over `S` out of an object which agree on a jointly
surjective family of open subobjects of the source are equal: the family generates a
covering sieve, and the presheaf represented by the target is a sheaf. -/
theorem BigFppfOver.hom_ext_of_openCover {T X : BigFppfOver B S hS} {K : Type w}
    {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    {h₁ h₂ : T ⟶ X} (h : ∀ k, p k ≫ h₁ = p k ≫ h₂) : h₁ = h₂ := by
  refine ((isSheaf_yoneda_obj_type X _
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hoi hcov)).isSeparatedFor).ext ?_
  rintro T' e ⟨Z, l, e', ⟨k⟩, hcomp⟩
  show e ≫ h₁ = e ≫ h₂
  rw [← hcomp, Category.assoc, Category.assoc, h k]

/-! ### The chart of a coproduct of sheaves is a fibre product -/

/-- **A member of a coproduct of objects of the site is the fibre product of the coproduct
with the corresponding member of a coproduct of sheaves.**

Let `G` be a coproduct of the sheaves `F i`, presented by a colimit cofan with legs `ι i`,
let `V` be a coproduct of the objects `U i` *inside the site*, and let `v : yoneda.obj V ⟶ G`
be a morphism restricting to given charts `f i : yoneda.obj (U i) ⟶ F i` on the members.
Then the resulting square is Cartesian: `U i₀` is the fibre of `V` over the `i₀`-th member.

The content is surjectivity: a morphism `s : T ⟶ V` whose image in `G` comes from the
`i₀`-th member factors through `U i₀`. Every point of `T` lies over some member `U k`, and
the part of `T` over `U k` carries a section of `F k` and a section of `F i₀` with the same
image in `G`, so it has no points unless `k = i₀`
(`AlgebraicGeometry.Sheaf.isEmpty_toScheme_of_eq_of_ne`); hence the image of `s` lies in the
image of `U i₀`, and `s` factors through it. That the factorisation is carried to the given
section of `F i₀` is injectivity of `ι i₀` on sections. -/
theorem isPullback_yoneda_map_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS}
    {j : ∀ i, U i ⟶ V} (hV : IsColimit (Cofan.mk V j))
    {f : ∀ i, yoneda.obj (U i) ⟶ (F i).obj} {v : yoneda.obj V ⟶ G.obj}
    (hfac : ∀ i, yoneda.map (j i) ≫ v = f i ≫ (ι i).hom) (i₀ : I) :
    IsPullback (yoneda.map (j i₀)) (f i₀) v (ι i₀).hom := by
  classical
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  have happ : ∀ (i : I) (T' : BigFppfOver B S hS) (l : T' ⟶ U i),
      v.app (op T') (l ≫ j i) = (ι i).hom.app (op T') ((f i).app (op T') l) :=
    fun i T' l => congrArg (fun m : yoneda.obj (U i) ⟶ G.obj => m.app (op T') l) (hfac i)
  -- the image of a morphism into `V` which comes from the `i₀`-th member lies in `U i₀`
  have hrange : ∀ (T : BigFppfOver B S hS) (s : T ⟶ V) (ξ : (F i₀).obj.obj (op T)),
      v.app (op T) s = (ι i₀).hom.app (op T) ξ →
      Set.range ((BigFppfOver.toScheme B S hS).map s) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (j i₀)) := by
    rintro T s ξ hs _ ⟨t, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, (BigFppfOver.toScheme B S hS).map s t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (j k)) :=
      Set.mem_iUnion.1 ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ _)
    obtain ⟨T', q, hq, hqr, -⟩ := exists_restrict_bigFppfOver T
      ((BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (j k)).opensRange)
    obtain ⟨y, hy⟩ : t ∈ Set.range ((BigFppfOver.toScheme B S hS).map q) := by
      rw [hqr]
      exact hk
    have hqs : Set.range ((BigFppfOver.toScheme B S hS).map (q ≫ s)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (j k)) := by
      rintro _ ⟨z, rfl⟩
      have hz : (BigFppfOver.toScheme B S hS).map q z ∈
          ((BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ
            ((BigFppfOver.toScheme B S hS).map (j k)).opensRange : Set _) := by
        rw [← hqr]
        exact ⟨z, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hz
    obtain ⟨l, hl⟩ := BigFppfOver.exists_factor_of_range_le (j k) (hoi k) (q ≫ s) hqs
    have h₁ : v.app (op T') ((yoneda.obj V).map q.op s)
        = (ι k).hom.app (op T') ((f k).app (op T') l) :=
      (congrArg (v.app (op T'))
        (show (yoneda.obj V).map q.op s = l ≫ j k from hl.symm)).trans (happ k T' l)
    have h₂ : v.app (op T') ((yoneda.obj V).map q.op s)
        = (ι i₀).hom.app (op T') ((F i₀).obj.map q.op ξ) := by
      rw [NatTrans.naturality_apply v q.op s, hs,
        ← NatTrans.naturality_apply (ι i₀).hom q.op ξ]
    by_cases hki₀ : k = i₀
    · subst hki₀
      refine ⟨(BigFppfOver.toScheme B S hS).map l y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hl, Functor.map_comp,
        Scheme.Hom.comp_apply, hy]
    · exact ((Sheaf.isEmpty_toScheme_of_eq_of_ne ι hG hki₀ _ _
        (h₁.symm.trans h₂)).false y).elim
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  obtain ⟨T⟩ := X
  refine (Limits.Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact congrArg (fun m : yoneda.obj (U i₀) ⟶ G.obj => m.app (op T)) (hfac i₀)
  · rintro h₁ h₂ ⟨he, -⟩
    have := mono_of_isOpenImmersion_map (j i₀) (hoi i₀)
    exact (cancel_mono (j i₀)).1 he
  · intro s ξ hsξ
    obtain ⟨h, hh⟩ := BigFppfOver.exists_factor_of_range_le (j i₀) (hoi i₀) s
      (hrange T s ξ hsξ)
    exact ⟨h, hh, injective_app_of_isColimit_cofan ι hG i₀ T
      ((happ i₀ T h).symm.trans ((congrArg (v.app (op T)) hh).trans hsξ))⟩

/-! ### Fibre products over a coproduct of algebraic spaces -/

/-- **The fibre product of two representable presheaves over a coproduct of algebraic spaces
is representable.**

Let `G` be a coproduct of the sheaves `F i`, each with representable diagonal, and let
`g : yoneda.obj a ⟶ G` and `k : yoneda.obj c ⟶ G` be two sections. Decomposing `a` and `c`
along the coproduct (`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`)
splits the fibre product into the fibre products `R i` of the `i`-th pieces over `F i`, which
are representable because the diagonal of `F i` is. The pieces are glued into a single object
of the site: each `R i ⟶ a ⨯ c` is a monomorphism, so
`AlgebraicGeometry.Scheme.size_le_of_mono` bounds all the `R i` by one cardinal below the
cutoff, and only the finitely many — in general, at most `#a` many — pieces with a point
contribute, so `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_size_le` applies.

That the resulting object really is the fibre product is checked on each object of the site.
Injectivity and surjectivity both reduce to the pieces, by the universal property of the
decomposition and the glueing of
`AlgebraicGeometry.BigFppfOver.exists_section_of_disjoint_openCover`. -/
theorem exists_isPullback_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (hd : ∀ i, yoneda.relativelyRepresentable (diag (F i).obj))
    {a c : BigFppfOver B S hS} (g : yoneda.obj a ⟶ G.obj) (k : yoneda.obj c ⟶ G.obj) :
    ∃ (Z : BigFppfOver B S hS) (πa : Z ⟶ a) (πc : Z ⟶ c),
      IsPullback (yoneda.map πa) (yoneda.map πc) g k := by
  classical
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hGsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  -- the two sections
  set x := g.app (op a) (𝟙 a) with hxdef
  set y := k.app (op c) (𝟙 c) with hydef
  -- decompose the two bases along the coproduct
  obtain ⟨A, pa, hAoi, hAsec, hAdisj, hAcov, hAuniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG a x
  obtain ⟨Cc, pc, hCoi, hCsec, hCdisj, hCcov, hCuniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG c y
  choose za hza using hAsec
  choose zc hzc using hCsec
  have hpamono : ∀ i, Mono (pa i) := fun i => mono_of_isOpenImmersion_map (pa i) (hAoi i)
  have hpcmono : ∀ i, Mono (pc i) := fun i => mono_of_isOpenImmersion_map (pc i) (hCoi i)
  -- the pieces of the decomposition as charts of the members
  set ga : ∀ i, yoneda.obj (A i) ⟶ (F i).obj := fun i => yonedaEquiv.symm (za i) with hgadef
  set gc : ∀ i, yoneda.obj (Cc i) ⟶ (F i).obj := fun i => yonedaEquiv.symm (zc i) with hgcdef
  have hgaapp : ∀ (i : I) (T : BigFppfOver B S hS) (α : T ⟶ A i),
      (ga i).app (op T) α = (F i).obj.map α.op (za i) := fun i T α =>
    yonedaEquiv_symm_app_apply (za i) (op T) α
  have hgcapp : ∀ (i : I) (T : BigFppfOver B S hS) (γ : T ⟶ Cc i),
      (gc i).app (op T) γ = (F i).obj.map γ.op (zc i) := fun i T γ =>
    yonedaEquiv_symm_app_apply (zc i) (op T) γ
  -- the fibre products of the pieces
  have hrep : ∀ i, ∃ (R : BigFppfOver B S hS) (qa : R ⟶ A i) (qc : R ⟶ Cc i),
      IsPullback (yoneda.map qc) (yoneda.map qa) (gc i) (ga i) := by
    intro i
    obtain ⟨R, snd, fst, hpb⟩ :=
      Functor.relativelyRepresentable.of_diag (hd i) (gc i) (ga i)
    obtain ⟨qc, rfl⟩ := yoneda.map_surjective fst
    exact ⟨R, snd, qc, hpb⟩
  choose R qa qc hRpb using hrep
  have hRw : ∀ i, (F i).obj.map (qc i).op (zc i) = (F i).obj.map (qa i).op (za i) := by
    intro i
    have h := congrArg
      (fun m : yoneda.obj (R i) ⟶ (F i).obj => m.app (op (R i)) (𝟙 (R i))) (hRpb i).w
    simpa [hgaapp, hgcapp] using h
  -- each piece is a subobject of the product of the two bases
  have hQmono : ∀ i, Mono (Limits.prod.lift (qa i ≫ pa i) (qc i ≫ pc i) : R i ⟶ a ⨯ c) := by
    intro i
    refine ⟨fun {T} g₁ g₂ e => ?_⟩
    have e₁ : g₁ ≫ qa i = g₂ ≫ qa i := by
      have h := congrArg (fun m : T ⟶ a ⨯ c => m ≫ Limits.prod.fst) e
      simp only [Category.assoc, Limits.prod.lift_fst] at h
      have := hpamono i
      exact (cancel_mono (pa i)).1 (by simpa using h)
    have e₂ : g₁ ≫ qc i = g₂ ≫ qc i := by
      have h := congrArg (fun m : T ⟶ a ⨯ c => m ≫ Limits.prod.snd) e
      simp only [Category.assoc, Limits.prod.lift_snd] at h
      have := hpcmono i
      exact (cancel_mono (pc i)).1 (by simpa using h)
    refine yoneda.map_injective ((hRpb i).hom_ext ?_ ?_)
    · rw [← Functor.map_comp, ← Functor.map_comp, e₂]
    · rw [← Functor.map_comp, ← Functor.map_comp, e₁]
  -- the index type of the pieces with a point, shrunk into the working universe
  have hJinj : Function.Injective
      (fun n : {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))} =>
        (BigFppfOver.toScheme B S hS).map (pa n.1) n.2.some) := by
    intro n m hnm
    refine Subtype.ext ?_
    by_contra hne
    exact hAdisj n.1 m.1 hne _ _ hnm
  have hJsmall : Small.{u} {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))} :=
    small_of_injective hJinj
  set K : Type u := Shrink.{u} {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))}
    with hKdef
  set ix : K → I := fun n => ((equivShrink _).symm n).1 with hixdef
  have hixinj : Function.Injective ix := fun n m h =>
    (equivShrink _).symm.injective (Subtype.ext h)
  have hKcard : #K ≤ #(↥((BigFppfOver.toScheme B S hS).obj a)) :=
    Cardinal.mk_le_of_injective (hJinj.comp (equivShrink _).symm.injective)
  -- the uniform size bound
  set μ : Cardinal.{u} :=
    max (max (2 ^ #(↥((BigFppfOver.toScheme B S hS).obj a)))
        ((BigFppfOver.toScheme B S hS).obj a).size)
      (max (2 ^ #(↥((BigFppfOver.toScheme B S hS).obj (a ⨯ c))))
        ((BigFppfOver.toScheme B S hS).obj (a ⨯ c)).size) with hμdef
  have hμlt : μ < B.cutoff :=
    max_lt
      (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
        a.left.property)
      (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
        (a ⨯ c).left.property)
  have hμℵ : ℵ₀ ≤ μ :=
    le_max_of_le_left (le_max_of_le_right (Scheme.aleph0_le_size _))
  have hμK : #K ≤ μ :=
    hKcard.trans ((Cardinal.cantor _).le.trans (le_max_of_le_left (le_max_left _ _)))
  have hμR : ∀ n : K, ((BigFppfOver.toScheme B S hS).obj (R (ix n))).size ≤ μ := by
    intro n
    have := hQmono (ix n)
    have hm : Mono ((BigFppfOver.toScheme B S hS).map
        (Limits.prod.lift (qa (ix n) ≫ pa (ix n)) (qc (ix n) ≫ pc (ix n)))) :=
      preserves_mono_of_preservesLimit (BigFppfOver.toScheme B S hS) _
    exact (Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map
      (Limits.prod.lift (qa (ix n) ≫ pa (ix n)) (qc (ix n) ≫ pc (ix n))))).trans
      (le_max_right _ _)
  -- the disjoint union of the pieces
  obtain ⟨Z, cc, hccoi, hccdisj, hcccov⟩ :=
    BigFppfOver.exists_coproduct_of_size_le B S hS (fun n : K => R (ix n)) hμℵ hμlt hμK hμR
  -- the two projections, glued from the pieces
  obtain ⟨πa, hπa⟩ := BigFppfOver.exists_section_of_disjoint_openCover
    (isSheaf_yoneda_obj_type a) cc hccoi hccdisj hcccov fun n => qa (ix n) ≫ pa (ix n)
  obtain ⟨πc, hπc⟩ := BigFppfOver.exists_section_of_disjoint_openCover
    (isSheaf_yoneda_obj_type c) cc hccoi hccdisj hcccov fun n => qc (ix n) ≫ pc (ix n)
  have hπa' : ∀ n : K, cc n ≫ πa = qa (ix n) ≫ pa (ix n) := hπa
  have hπc' : ∀ n : K, cc n ≫ πc = qc (ix n) ≫ pc (ix n) := hπc
  refine ⟨Z, πa, πc, ?_⟩
  -- a morphism into `Z` lying over the `n`-th piece of `a` factors through the `n`-th piece
  have hfactor : ∀ (T : BigFppfOver B S hS) (h : T ⟶ Z) (n : K),
      Set.range ((BigFppfOver.toScheme B S hS).map ((h ≫ πa))) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (pa (ix n))) →
      ∃ β : T ⟶ R (ix n), β ≫ cc n = h := by
    intro T h n hr
    refine BigFppfOver.exists_factor_of_range_le (cc n) (hccoi n) h ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨m, w, hw⟩ := hcccov ((BigFppfOver.toScheme B S hS).map h z)
    obtain ⟨v, hv⟩ := hr ⟨z, rfl⟩
    have k₁ : (BigFppfOver.toScheme B S hS).map (h ≫ πa) z
        = (BigFppfOver.toScheme B S hS).map (pa (ix m))
            ((BigFppfOver.toScheme B S hS).map (qa (ix m)) w) := by
      rw [Functor.map_comp, Scheme.Hom.comp_apply, ← hw, ← Scheme.Hom.comp_apply,
        ← Functor.map_comp, hπa' m, Functor.map_comp, Scheme.Hom.comp_apply]
    have hmn : m = n := by
      by_contra hne
      exact hAdisj (ix m) (ix n) (fun he => hne (hixinj he)) _ _ (k₁.symm.trans hv.symm)
    exact hmn ▸ ⟨w, hw⟩
  -- the covering sieve of `Z` by the pieces
  have hZcov : Sieve.ofArrows (fun n : K => R (ix n)) cc ∈ BigFppfOver.topology B S hS Z :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS cc hccoi hcccov
  -- the two projections pull `x` and `y` back to the same section of `G` over `Z`
  have hsec : G.obj.map πa.op x = G.obj.map πc.op y := by
    refine ((hGsheaf _ hZcov).isSeparatedFor).ext ?_
    rintro T' e ⟨W', l, e', ⟨n⟩, hcomp⟩
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← hcomp,
      Category.assoc, Category.assoc, hπa' n, hπc' n]
    rw [← Category.assoc, ← Category.assoc, map_comp_section_eq ι (ix n) _ (hza (ix n)),
      map_comp_section_eq ι (ix n) _ (hzc (ix n)), op_comp, Functor.map_comp_apply, op_comp,
      Functor.map_comp_apply, hRw (ix n)]
  have hwglob : yoneda.map πa ≫ g = yoneda.map πc ≫ k := by
    refine yonedaEquiv.injective ?_
    show g.app (op Z) (𝟙 Z ≫ πa) = k.app (op Z) (𝟙 Z ≫ πc)
    rw [Category.id_comp, Category.id_comp, app_eq_map_app_id g, app_eq_map_app_id k, hsec]
  -- every object of the site over `a` and `c` is covered by pieces of the fibre product
  have hdecomp : ∀ (T : BigFppfOver B S hS) (sT : T ⟶ a) (tT : T ⟶ c),
      G.obj.map sT.op x = G.obj.map tT.op y →
      ∃ (D : K → BigFppfOver B S hS) (pd : ∀ n, D n ⟶ T) (ρ : ∀ n, D n ⟶ R (ix n)),
        (∀ n, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (pd n))) ∧
        (∀ n n', n ≠ n' → ∀ (yy : (BigFppfOver.toScheme B S hS).obj (D n))
          (yy' : (BigFppfOver.toScheme B S hS).obj (D n')),
          (BigFppfOver.toScheme B S hS).map (pd n) yy ≠
            (BigFppfOver.toScheme B S hS).map (pd n') yy') ∧
        (∀ t : (BigFppfOver.toScheme B S hS).obj T,
          ∃ n, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pd n))) ∧
        (∀ n, ρ n ≫ qa (ix n) ≫ pa (ix n) = pd n ≫ sT) ∧
        (∀ n, ρ n ≫ qc (ix n) ≫ pc (ix n) = pd n ≫ tT) := by
    intro T sT tT hst
    obtain ⟨D, pd, hDoi, hDsec, hDdisj, hDcov, hDuniv⟩ :=
      Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG T (G.obj.map sT.op x)
    choose zd hzd using hDsec
    have hαex : ∀ i, ∃ α : D i ⟶ A i, α ≫ pa i = pd i ≫ sT := by
      intro i
      refine hAuniv i (D i) (pd i ≫ sT) ⟨zd i, ?_⟩
      rw [hzd i, ← Functor.map_comp_apply, ← op_comp]
    have hγex : ∀ i, ∃ γ : D i ⟶ Cc i, γ ≫ pc i = pd i ≫ tT := by
      intro i
      refine hCuniv i (D i) (pd i ≫ tT) ⟨zd i, ?_⟩
      rw [hzd i, hst, ← Functor.map_comp_apply, ← op_comp]
    choose α hα using hαex
    choose γ hγ using hγex
    have hzda : ∀ i, (F i).obj.map (α i).op (za i) = zd i := by
      intro i
      refine injective_app_of_isColimit_cofan ι hG i (D i) ?_
      rw [NatTrans.naturality_apply (ι i).hom (α i).op (za i), hza i,
        ← Functor.map_comp_apply, ← op_comp, hα i, hzd i, ← Functor.map_comp_apply, ← op_comp]
    have hzdc : ∀ i, (F i).obj.map (γ i).op (zc i) = zd i := by
      intro i
      refine injective_app_of_isColimit_cofan ι hG i (D i) ?_
      rw [NatTrans.naturality_apply (ι i).hom (γ i).op (zc i), hzc i,
        ← Functor.map_comp_apply, ← op_comp, hγ i, hzd i, hst, ← Functor.map_comp_apply,
        ← op_comp]
    have hρex : ∀ i, ∃ ρ : D i ⟶ R i, ρ ≫ qa i = α i ∧ ρ ≫ qc i = γ i := by
      intro i
      have hwi : yoneda.map (γ i) ≫ gc i = yoneda.map (α i) ≫ ga i := by
        refine yonedaEquiv.injective ?_
        show (gc i).app (op (D i)) (𝟙 (D i) ≫ γ i)
          = (ga i).app (op (D i)) (𝟙 (D i) ≫ α i)
        rw [Category.id_comp, Category.id_comp, hgaapp, hgcapp, hzda i, hzdc i]
      refine ⟨yoneda.preimage ((hRpb i).lift (yoneda.map (γ i)) (yoneda.map (α i)) hwi),
        yoneda.map_injective ?_, yoneda.map_injective ?_⟩
      · rw [Functor.map_comp, yoneda.map_preimage]
        exact (hRpb i).lift_snd _ _ hwi
      · rw [Functor.map_comp, yoneda.map_preimage]
        exact (hRpb i).lift_fst _ _ hwi
    choose ρ hρa hρc using hρex
    have hDcovK : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        ∃ n : K, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pd (ix n))) := by
      intro t
      obtain ⟨i, w, hw⟩ := hDcov t
      have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj (A i)) :=
        ⟨(BigFppfOver.toScheme B S hS).map (α i) w⟩
      refine ⟨equivShrink {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))}
        ⟨i, hne⟩, ?_⟩
      have hixe : ix (equivShrink
          {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))} ⟨i, hne⟩) = i := by
        rw [hixdef]
        exact congrArg Subtype.val ((equivShrink
          {i : I // Nonempty ((BigFppfOver.toScheme B S hS).obj (A i))}).symm_apply_apply
            ⟨i, hne⟩)
      rw [hixe]
      exact ⟨w, hw⟩
    refine ⟨fun n => D (ix n), fun n => pd (ix n), fun n => ρ (ix n),
      fun n => hDoi (ix n), fun n n' hnn' => hDdisj (ix n) (ix n')
        (fun he => hnn' (hixinj he)), hDcovK, fun n => ?_, fun n => ?_⟩
    · rw [← Category.assoc, hρa (ix n), hα (ix n)]
    · rw [← Category.assoc, hρc (ix n), hγ (ix n)]
  -- injectivity of the pair of projections
  have hinj : ∀ (T : BigFppfOver B S hS) (h₁ h₂ : T ⟶ Z),
      h₁ ≫ πa = h₂ ≫ πa → h₁ ≫ πc = h₂ ≫ πc → h₁ = h₂ := by
    intro T h₁ h₂ e₁ e₂
    obtain ⟨D, pd, ρ, hDoi, hDdisj, hDcov, hρa, hρc⟩ :=
      hdecomp T (h₁ ≫ πa) (h₁ ≫ πc) (by
        rw [op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply, hsec])
    refine BigFppfOver.hom_ext_of_openCover pd hDoi hDcov fun n => ?_
    have hr₁ : Set.range ((BigFppfOver.toScheme B S hS).map ((pd n ≫ h₁) ≫ πa)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (pa (ix n))) := by
      have he : (pd n ≫ h₁) ≫ πa = (ρ n ≫ qa (ix n)) ≫ pa (ix n) := by
        rw [Category.assoc, ← hρa n, Category.assoc]
      rw [he]
      rintro _ ⟨z, rfl⟩
      exact ⟨(BigFppfOver.toScheme B S hS).map (ρ n ≫ qa (ix n)) z, by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]⟩
    have hr₂ : Set.range ((BigFppfOver.toScheme B S hS).map ((pd n ≫ h₂) ≫ πa)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (pa (ix n))) := by
      rw [show (pd n ≫ h₂) ≫ πa = (pd n ≫ h₁) ≫ πa by
        rw [Category.assoc, Category.assoc, e₁]]
      exact hr₁
    obtain ⟨β₁, hβ₁⟩ := hfactor (D n) (pd n ≫ h₁) n hr₁
    obtain ⟨β₂, hβ₂⟩ := hfactor (D n) (pd n ≫ h₂) n hr₂
    have hca : ∀ (β : D n ⟶ R (ix n)) (hh : T ⟶ Z), β ≫ cc n = pd n ≫ hh →
        (β ≫ qa (ix n)) ≫ pa (ix n) = (pd n ≫ hh) ≫ πa := by
      intro β hh hβ
      rw [Category.assoc, ← hπa' n, ← Category.assoc, hβ]
    have hcc' : ∀ (β : D n ⟶ R (ix n)) (hh : T ⟶ Z), β ≫ cc n = pd n ≫ hh →
        (β ≫ qc (ix n)) ≫ pc (ix n) = (pd n ≫ hh) ≫ πc := by
      intro β hh hβ
      rw [Category.assoc, ← hπc' n, ← Category.assoc, hβ]
    have ea : β₁ ≫ qa (ix n) = β₂ ≫ qa (ix n) := by
      have := hpamono (ix n)
      refine (cancel_mono (pa (ix n))).1 ?_
      rw [hca β₁ h₁ hβ₁, hca β₂ h₂ hβ₂, Category.assoc, Category.assoc, e₁]
    have ec : β₁ ≫ qc (ix n) = β₂ ≫ qc (ix n) := by
      have := hpcmono (ix n)
      refine (cancel_mono (pc (ix n))).1 ?_
      rw [hcc' β₁ h₁ hβ₁, hcc' β₂ h₂ hβ₂, Category.assoc, Category.assoc, e₂]
    have hβ : β₁ = β₂ := yoneda.map_injective ((hRpb (ix n)).hom_ext
      (by rw [← Functor.map_comp, ← Functor.map_comp, ec])
      (by rw [← Functor.map_comp, ← Functor.map_comp, ea]))
    rw [← hβ₁, ← hβ₂, hβ]
  -- surjectivity of the pair of projections
  have hsurj : ∀ (T : BigFppfOver B S hS) (sT : T ⟶ a) (tT : T ⟶ c),
      g.app (op T) sT = k.app (op T) tT →
      ∃ h : T ⟶ Z, h ≫ πa = sT ∧ h ≫ πc = tT := by
    intro T sT tT hst
    obtain ⟨D, pd, ρ, hDoi, hDdisj, hDcov, hρa, hρc⟩ :=
      hdecomp T sT tT (by rw [← app_eq_map_app_id g, ← app_eq_map_app_id k]; exact hst)
    obtain ⟨h, hh⟩ := BigFppfOver.exists_section_of_disjoint_openCover
      (isSheaf_yoneda_obj_type Z) pd hDoi hDdisj hDcov fun n => ρ n ≫ cc n
    have hh' : ∀ n, pd n ≫ h = ρ n ≫ cc n := hh
    refine ⟨h, BigFppfOver.hom_ext_of_openCover pd hDoi hDcov fun n => ?_,
      BigFppfOver.hom_ext_of_openCover pd hDoi hDcov fun n => ?_⟩
    · calc pd n ≫ h ≫ πa = (pd n ≫ h) ≫ πa := (Category.assoc _ _ _).symm
        _ = (ρ n ≫ cc n) ≫ πa := by rw [hh' n]
        _ = ρ n ≫ qa (ix n) ≫ pa (ix n) := by rw [Category.assoc, hπa' n]
        _ = pd n ≫ sT := hρa n
    · calc pd n ≫ h ≫ πc = (pd n ≫ h) ≫ πc := (Category.assoc _ _ _).symm
        _ = (ρ n ≫ cc n) ≫ πc := by rw [hh' n]
        _ = ρ n ≫ qc (ix n) ≫ pc (ix n) := by rw [Category.assoc, hπc' n]
        _ = pd n ≫ tT := hρc n
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  obtain ⟨T⟩ := X
  refine (Limits.Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact congrArg (fun m : yoneda.obj Z ⟶ G.obj => m.app (op T)) hwglob
  · rintro h₁ h₂ ⟨e₁, e₂⟩
    exact hinj T h₁ h₂ e₁ e₂
  · intro sT tT hst
    exact hsurj T sT tT hst

/-! ### The diagonal and the atlas of a coproduct -/

/-- **The diagonal of a coproduct of algebraic spaces is representable.**

By `CategoryTheory.Functor.relativelyRepresentable.diag_of_map_from_obj` this is the same as
representability of every morphism from a representable presheaf, which is
`AlgebraicGeometry.exists_isPullback_of_isColimit_cofan`. -/
theorem relativelyRepresentable_diag_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (hd : ∀ i, yoneda.relativelyRepresentable (diag (F i).obj)) :
    yoneda.relativelyRepresentable (diag G.obj) := by
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine Functor.relativelyRepresentable.diag_of_map_from_obj fun a g c kk => ?_
  obtain ⟨Z, πa, πc, hpb⟩ := exists_isPullback_of_isColimit_cofan ι hG hd g kk
  exact ⟨Z, πc, yoneda.map πa, hpb⟩

/-- **The glued chart of a coproduct of algebraic spaces inherits a Zariski-local property
of its members.**

The chart `v` is representable because the diagonal of the coproduct is
(`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`), so it is enough to
check the property on one represented base change at a time. Such a base change is checked
after restricting to the pieces of the decomposition of the test object: over the `i`-th
piece the base change of `v` agrees with a base change of the `i`-th chart `f i`, because
`U i` is the fibre of `V` over the `i`-th member
(`AlgebraicGeometry.isPullback_yoneda_map_of_isColimit_cofan`). -/
theorem presheaf_inverseImage_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (hd : ∀ i, yoneda.relativelyRepresentable (diag (F i).obj))
    {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V}
    (hV : IsColimit (Cofan.mk V j))
    {f : ∀ i, yoneda.obj (U i) ⟶ (F i).obj} {v : yoneda.obj V ⟶ G.obj}
    (hfac : ∀ i, yoneda.map (j i) ≫ v = f i ≫ (ι i).hom)
    {P₀ : MorphismProperty Scheme.{u}} (hloc : IsZariskiLocalAtTarget P₀)
    (hf : ∀ i, (P₀.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (f i)) :
    (P₀.inverseImage (BigFppfOver.toScheme B S hS)).presheaf v := by
  classical
  have hri : (P₀.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hLP := isPullback_yoneda_map_of_isColimit_cofan ι hG hV hfac
  have hvrep : yoneda.relativelyRepresentable v :=
    have _ : HasBinaryProducts (BigFppfOver B S hS) :=
      hasBinaryProducts_of_hasTerminal_and_pullbacks _
    Functor.relativelyRepresentable.of_diag
      (relativelyRepresentable_diag_of_isColimit_cofan ι hG hd) v
  refine MorphismProperty.relative_of_snd hvrep fun c kk => ?_
  set y := kk.app (op c) (𝟙 c) with hydef
  obtain ⟨A, pa, hAoi, hAsec, hAdisj, hAcov, hAuniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG c y
  choose za hza using hAsec
  set ga : ∀ i, yoneda.obj (A i) ⟶ (F i).obj := fun i => yonedaEquiv.symm (za i) with hgadef
  have hgaapp : ∀ (i : I) (T : BigFppfOver B S hS) (α : T ⟶ A i),
      (ga i).app (op T) α = (F i).obj.map α.op (za i) := fun i T α =>
    yonedaEquiv_symm_app_apply (za i) (op T) α
  have hgaι : ∀ i, yoneda.map (pa i) ≫ kk = ga i ≫ (ι i).hom := by
    intro i
    refine yonedaEquiv.injective ?_
    show kk.app (op (A i)) (𝟙 (A i) ≫ pa i)
      = (ι i).hom.app (op (A i)) ((ga i).app (op (A i)) (𝟙 (A i)))
    rw [Category.id_comp, app_eq_map_app_id kk, hgaapp]
    simp only [op_id, CategoryTheory.Functor.map_id_apply]
    exact (hza i).symm
  show P₀ ((BigFppfOver.toScheme B S hS).map (hvrep.snd kk))
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Scheme.zariskiPrecoverage)
    (R := Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (A i))
      (fun i => (BigFppfOver.toScheme B S hS).map (pa i))) ?_ ?_
  · rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hAcov, hAoi⟩
  · intro U' gg hpb hR
    obtain ⟨i⟩ := hR
    have hsitepb : IsPullback (yoneda.map (Limits.pullback.fst (hvrep.snd kk) (pa i)))
        (yoneda.map (Limits.pullback.snd (hvrep.snd kk) (pa i)))
        (yoneda.map (hvrep.snd kk)) (yoneda.map (pa i)) :=
      (IsPullback.of_hasPullback (hvrep.snd kk) (pa i)).map yoneda
    have hcomp := hsitepb.paste_horiz (hvrep.isPullback kk)
    rw [hgaι i] at hcomp
    have hw : (yoneda.map (Limits.pullback.fst (hvrep.snd kk) (pa i)) ≫ hvrep.fst kk) ≫ v
        = (yoneda.map (Limits.pullback.snd (hvrep.snd kk) (pa i)) ≫ ga i) ≫ (ι i).hom :=
      hcomp.w.trans (Category.assoc _ _ _).symm
    have hsq : IsPullback ((hLP i).lift _ _ hw)
        (yoneda.map (Limits.pullback.snd (hvrep.snd kk) (pa i))) (f i) (ga i) :=
      IsPullback.of_right (by rw [(hLP i).lift_fst]; exact hcomp)
        ((hLP i).lift_snd _ _ hw) (hLP i)
    have hps : P₀ ((BigFppfOver.toScheme B S hS).map
        (Limits.pullback.snd (hvrep.snd kk) (pa i))) :=
      (hf i).property (ga i) _ _ hsq
    rw [← PreservesPullback.iso_hom_snd (BigFppfOver.toScheme B S hS) (hvrep.snd kk)
      (pa i)] at hps
    exact (MorphismProperty.cancel_left_of_respectsIso P₀ _ _).1 hps

end Pieces

/-! ### Stacks 02WQ -/

/-- **Stacks 02WQ.** A coproduct of algebraic spaces over `S` is an algebraic space over `S`,
provided the chosen surjective étale scheme atlases of the members have a coproduct inside the
big fppf site over `S`.

The sheaf condition is part of the data. The diagonal is representable by
`AlgebraicGeometry.relativelyRepresentable_diag_of_isColimit_cofan`, and the coproduct `V` of
the atlases, with the morphism to the coproduct sheaf glued by
`AlgebraicGeometry.exists_hom_yoneda_of_isColimit_cofan`, is a surjective étale atlas by
`AlgebraicGeometry.presheaf_inverseImage_of_isColimit_cofan`. -/
@[stacks 02WQ]
theorem isAlgebraicSpace_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v}
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (U : I → BigFppfOver B S hS)
    (f : ∀ i, yoneda.obj (U i) ⟶ F i)
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (V : BigFppfOver B S hS)
    (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk V j)) :
    IsAlgebraicSpace B S hS G.obj := by
  obtain ⟨v, hfac⟩ := exists_hom_yoneda_of_isColimit_cofan ι f hV
  refine ⟨G.property, relativelyRepresentable_diag_of_isColimit_cofan ι hG
    fun i => (hF i).diagonal_representable, V, v, ?_, ?_⟩
  · exact presheaf_inverseImage_of_isColimit_cofan ι hG
      (fun i => (hF i).diagonal_representable) hV hfac inferInstance hsurj
  · exact presheaf_inverseImage_of_isColimit_cofan ι hG
      (fun i => (hF i).diagonal_representable) hV hfac
      (HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale) (Q := RingHom.Etale)) hetale

end AlgebraicGeometry

end
