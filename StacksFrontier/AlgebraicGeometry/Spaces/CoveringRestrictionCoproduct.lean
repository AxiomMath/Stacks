module

public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.InlineBootstrapForm

/-!
# The restriction of a sheaf to a coproduct of objects of the site, and Stacks 04SK

Let `F` be an fppf sheaf of sets on the big fppf site of a scheme `S` and let `V` be a
coproduct, *inside the site*, of a family `U i` of objects of the site. The restriction
`yoneda.obj V ⨯ F` of `F` to `V` is then a coproduct of the restrictions
`yoneda.obj (U i) ⨯ F` in the category of fppf sheaves. This file proves that, and deduces
Stacks 04SK — a presheaf which is a sheaf and whose restrictions to the members of a covering
of the base, together with their coproduct, are algebraic spaces is an algebraic space — from
the bootstrap theorem Stacks 04S6, condition (3).

## Main results

* `AlgebraicGeometry.isIso_hom_desc_of_decomposition`: a cofan of sheaves whose legs are
  injective on sections, pairwise disjoint in the sense that two sections of different
  members with the same image live over an object with no points, and jointly decompose every
  section of the target over a disjoint open cover, is a coproduct: the morphism to it from a
  sheaf coproduct of the same family is an isomorphism of presheaves.
* `AlgebraicGeometry.exists_iso_prod_yoneda_obj_of_isColimit_cofan`: a sheaf coproduct of the
  restrictions `yoneda.obj (U i) ⨯ F` is isomorphic to the restriction `yoneda.obj V ⨯ F` to
  a coproduct `V` of the `U i` in the site, compatibly with the coproduct injections. This is
  the identification with which the proof of Stacks 04SK opens: the morphism
  `∐ᵢ (h_{U i} × F) ⟶ F` *is* the base change of `V ⟶ S` along `F ⟶ S`.
* `AlgebraicGeometry.SpacesDescent.surjective_inf_flat_inf_locallyOfFinitePresentation_desc`:
  the morphism out of a coproduct in the site induced by a flat, locally finitely presented,
  jointly surjective family is surjective, flat and locally of finite presentation.
* `AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_atlas_size_le`: the refinement step
  shared by Stacks 04SK and Stacks 04U0 — if the restrictions of the members `F_i` to affine
  opens of the members have étale atlases of bounded size, then `F` is an algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_of_isCovering` is Stacks 04SK.

## Implementation notes

Both halves of the coproduct comparison are checked on sections, the category of sheaves of
sets being a full subcategory of presheaves, where a morphism is an isomorphism as soon as
every component is bijective. Surjectivity on sections glues the local lifts along the
decomposition with `AlgebraicGeometry.BigFppfOver.exists_section_of_disjoint_openCover`;
injectivity decomposes a section of the coproduct twice with
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`, the second
decomposition being carried by the pieces of the first, and discards the pieces with the
wrong index because they have no points.

The decomposition needed for the restriction `yoneda.obj V ⨯ F` is geometric: a section over
`T` is a pair of a morphism `T ⟶ V` and a section of `F` over `T`, and the pieces are the
preimages in `T` of the members `U i`, which are pairwise disjoint open subobjects covering
`T` because the members of a colimit cofan in the site are
(`AlgebraicGeometry.isOpenImmersion_toScheme_map_cofan`,
`AlgebraicGeometry.ne_toScheme_map_cofan`, `AlgebraicGeometry.iUnion_range_toScheme_map_cofan`).

The source's chart for Stacks 04SK is `∐ F_i ⟶ F`, the base change of `∐ S_i ⟶ S`. The
disjoint union `∐ S_i` need not be an object of the site, so the proof uses a refinement of the
covering instead. It has one affine open of a member over each point of `S`, so its disjoint
union is an object of the site by the size bounds of Stacks 04T7 and Stacks 000Q
(`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt`). The base change of
`F` to that disjoint union is an algebraic space by Stacks 02WQ
(`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`). The atlases it needs come from an
atlas of `∐ F_i`, split along the coproduct, and this is where hypothesis (3) of the source is
used. The coproduct `∐ F_i` itself is given as data together with its universal property,
because the index type of the covering is of the next universe.

The instance of the bootstrap theorem Stacks 04S6 which the proof of Stacks 04SK consumes is
condition (3) for a scheme-representable chart. It is
`AlgebraicGeometry.Space.isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap` applied to
condition (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

## References

* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe w u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two sections of a binary product of presheaves over the same object agree as soon as
their two components do. -/
private lemma prod_section_ext {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} {z z' : (P ⨯ Q).obj (op T)}
    (h₁ : (prod.fst : P ⨯ Q ⟶ P).app (op T) z = (prod.fst : P ⨯ Q ⟶ P).app (op T) z')
    (h₂ : (prod.snd : P ⨯ Q ⟶ Q).app (op T) z = (prod.snd : P ⨯ Q ⟶ Q).app (op T) z') :
    z = z' := by
  refine yonedaEquiv.symm.injective (prod.hom_ext ?_ ?_) <;> refine yonedaEquiv.injective ?_ <;>
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Two sections of a sheaf over an object of the big fppf site of `S` which agree on a
jointly surjective family of open subobjects are equal. -/
private lemma section_ext_of_openCover {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : Presieve.IsSheaf (BigFppfOver.topology B S hS) H) {K : Type w}
    {T : BigFppfOver B S hS} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    {τ₁ τ₂ : H.obj (op T)} (h : ∀ k, H.map (p k).op τ₁ = H.map (p k).op τ₂) : τ₁ = τ₂ := by
  refine ((hH _ (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hoi
    hcov)).isSeparatedFor).ext ?_
  rintro T' g ⟨Z, l, e, ⟨k⟩, hcomp⟩
  rw [← hcomp]
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  rw [h k]

/-- The morphism of presheaves underlying the morphism out of a colimit cofan of sheaves
restricts along each leg to the corresponding leg of the target cofan. -/
private theorem hom_comp_hom_desc_cofan {I : Type w}
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} (κ : ∀ i, Fi i ⟶ X) (i : I) :
    (ι i).hom ≫ (hG.desc (Cofan.mk X κ)).hom = (κ i).hom := by
  have h := hG.fac (Cofan.mk X κ) ⟨i⟩
  simp only [Cofan.mk_ι_app] at h
  exact Sheaf.hom_ext_iff.mp h

/-- A morphism out of a coproduct of sheaves is injective on sections as soon as its
restrictions `κ i` to the members are injective on sections and two sections of different
members with the same image can only live over an object with no points. -/
private theorem injective_hom_app_of_isColimit_cofan {I : Type w}
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} {ι : ∀ i, Fi i ⟶ G}
    (hG : IsColimit (Cofan.mk G ι))
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} {κ : ∀ i, Fi i ⟶ X} {θ : G ⟶ X}
    (hfac : ∀ i, (ι i).hom ≫ θ.hom = (κ i).hom)
    (hinj : ∀ (i : I) (T : BigFppfOver B S hS),
      Function.Injective ((κ i).hom.app (op T)))
    (hdisj : ∀ (i i' : I), i ≠ i' → ∀ (T : BigFppfOver B S hS)
      (a : (Fi i).obj.obj (op T)) (b : (Fi i').obj.obj (op T)),
      (κ i).hom.app (op T) a = (κ i').hom.app (op T) b →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T))
    (T : BigFppfOver B S hS) : Function.Injective (θ.hom.app (op T)) := by
  have hGs : Presieve.IsSheaf (BigFppfOver.topology B S hS) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hκθ : ∀ (i : I) (T : BigFppfOver B S hS) (a : (Fi i).obj.obj (op T)),
      θ.hom.app (op T) ((ι i).hom.app (op T) a) = (κ i).hom.app (op T) a := fun i T a => by
    simpa using congrArg (fun m : (Fi i).obj ⟶ X.obj => m.app (op T) a) (hfac i)
  intro τ₁ τ₂ hτ
  obtain ⟨W, p, hoi, hz, -, hcov, -⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG T τ₁
  refine section_ext_of_openCover hGs p hoi hcov fun i => ?_
  obtain ⟨zi, hzi⟩ := hz i
  obtain ⟨Y, q, hqoi, hw, -, hqcov, -⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hG (W i)
      (G.obj.map (p i).op τ₂)
  refine section_ext_of_openCover hGs q hqoi hqcov fun k => ?_
  have key : θ.hom.app (op (Y k)) (G.obj.map (q k).op (G.obj.map (p i).op τ₁))
      = θ.hom.app (op (Y k)) (G.obj.map (q k).op (G.obj.map (p i).op τ₂)) := by
    simp only [NatTrans.naturality_apply, hτ]
  obtain ⟨wk, hwk⟩ := hw k
  rcases eq_or_ne k i with rfl | hki
  · have hA : G.obj.map (q k).op (G.obj.map (p k).op τ₁)
        = (ι k).hom.app (op (Y k)) ((Fi k).obj.map (q k).op zi) := by
      rw [← hzi]
      exact (NatTrans.naturality_apply (ι k).hom (q k).op zi).symm
    rw [hA, ← hwk]
    refine congrArg ((ι k).hom.app (op (Y k))) (hinj k (Y k) ?_)
    rw [← hκθ k (Y k) ((Fi k).obj.map (q k).op zi), ← hκθ k (Y k) wk, ← hA, hwk]
    exact key
  · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj (Y k)) := by
      refine hdisj k i hki (Y k) wk ((Fi i).obj.map (q k).op zi) ?_
      have hR : (ι i).hom.app (op (Y k)) ((Fi i).obj.map (q k).op zi)
          = G.obj.map (q k).op (G.obj.map (p i).op τ₁) := by
        rw [NatTrans.naturality_apply, hzi]
      rw [← hκθ k (Y k) wk, ← hκθ i (Y k) ((Fi i).obj.map (q k).op zi), hwk, hR]
      exact key.symm
    exact (hGs.subsingleton_obj_of_bot_mem _
      (BigFppfOver.bot_mem_topology (Y k) hempty)).elim _ _

/-- **A cofan of sheaves which decomposes every section locally is a coproduct.**

Let `G` be a coproduct of the sheaves `Fi` on the big fppf site of `S`, presented by a
colimit cofan with legs `ι i`, and let `κ i : Fi i ⟶ X` be another cofan on the same family.
Suppose that each `κ i` is injective on sections, that two sections of different members with
the same image in `X` can only live over an object with no points, and that every section of
`X` over an object `T` of the site becomes a section of `Fi i` after restriction to the
`i`-th member of a family of pairwise disjoint open subobjects covering `T`. Then the induced
morphism `G ⟶ X` is an isomorphism of presheaves.

Surjectivity on sections is the gluing of the local lifts, which is possible because `G` is a
sheaf and the pieces are disjoint; injectivity decomposes a section of `G` twice, the second
decomposition being carried by the pieces of the first, and uses the disjointness hypothesis
to discard the pieces with the wrong index. -/
theorem isIso_hom_desc_of_decomposition {I : Type w}
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} (κ : ∀ i, Fi i ⟶ X)
    (hinj : ∀ (i : I) (T : BigFppfOver B S hS),
      Function.Injective ((κ i).hom.app (op T)))
    (hdisj : ∀ (i i' : I), i ≠ i' → ∀ (T : BigFppfOver B S hS)
      (a : (Fi i).obj.obj (op T)) (b : (Fi i').obj.obj (op T)),
      (κ i).hom.app (op T) a = (κ i').hom.app (op T) b →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T))
    (hdecomp : ∀ (T : BigFppfOver B S hS) (y : X.obj.obj (op T)),
      ∃ (W : I → BigFppfOver B S hS) (p : ∀ i, W i ⟶ T),
        (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))) ∧
        (∀ i i', i ≠ i' → ∀ (y₁ : (BigFppfOver.toScheme B S hS).obj (W i))
          (y₂ : (BigFppfOver.toScheme B S hS).obj (W i')),
          (BigFppfOver.toScheme B S hS).map (p i) y₁ ≠
            (BigFppfOver.toScheme B S hS).map (p i') y₂) ∧
        (∀ t : (BigFppfOver.toScheme B S hS).obj T,
          ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p i))) ∧
        (∀ i, ∃ z : (Fi i).obj.obj (op (W i)),
          (κ i).hom.app (op (W i)) z = X.obj.map (p i).op y)) :
    IsIso (hG.desc (Cofan.mk X κ)).hom := by
  classical
  set θ : G ⟶ X := hG.desc (Cofan.mk X κ)
  have hfac : ∀ i, (ι i).hom ≫ θ.hom = (κ i).hom := hom_comp_hom_desc_cofan ι hG κ
  have hGs : Presieve.IsSheaf (BigFppfOver.topology B S hS) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hXs : Presieve.IsSheaf (BigFppfOver.topology B S hS) X.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 X.property
  have hsurj : ∀ (T : BigFppfOver B S hS),
      Function.Surjective (θ.hom.app (op T)) := by
    intro T y
    obtain ⟨W, p, hoi, hpdisj, hcov, hlift⟩ := hdecomp T y
    choose z hz using hlift
    obtain ⟨τ, hτ⟩ := BigFppfOver.exists_section_of_disjoint_openCover hGs p hoi hpdisj hcov
      fun i => (ι i).hom.app (op (W i)) (z i)
    refine ⟨τ, section_ext_of_openCover hXs p hoi hcov fun i => ?_⟩
    rw [← NatTrans.naturality_apply θ.hom (p i).op τ, hτ i,
      ← types_comp_apply ((ι i).hom.app (op (W i))) (θ.hom.app (op (W i))),
      ← NatTrans.comp_app, hfac i, hz i]
  have : ∀ Z : (BigFppfOver B S hS)ᵒᵖ, IsIso (θ.hom.app Z) := by
    intro Z
    obtain ⟨T⟩ := Z
    exact (isIso_iff_bijective _).2
      ⟨injective_hom_app_of_isColimit_cofan hG hfac hinj hdisj T, hsurj T⟩
  exact NatIso.isIso_of_isIso_app θ.hom

/-- The first component of the image of a section of `yoneda.obj U ⨯ F` under
`prod.map (yoneda.map f) (𝟙 F)` is its first component composed with `f`. -/
private theorem fst_app_prod_map_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T : BigFppfOver B S hS}
    (z : (yoneda.obj U ⨯ F).obj (op T)) :
    (prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T)
        ((prod.map (yoneda.map f) (𝟙 F)).app (op T) z)
      = (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U).app (op T) z ≫ f :=
  calc (prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T)
        ((prod.map (yoneda.map f) (𝟙 F)).app (op T) z)
      = (prod.map (yoneda.map f) (𝟙 F) ≫ prod.fst).app (op T) z := rfl
    _ = (prod.fst ≫ yoneda.map f).app (op T) z := by rw [prod.map_fst (yoneda.map f) (𝟙 F)]
    _ = (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U).app (op T) z ≫ f := rfl

/-- The second component of the image of a section of `yoneda.obj U ⨯ F` under
`prod.map (yoneda.map f) (𝟙 F)` is its second component. -/
private theorem snd_app_prod_map_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T : BigFppfOver B S hS}
    (z : (yoneda.obj U ⨯ F).obj (op T)) :
    (prod.snd : yoneda.obj V ⨯ F ⟶ F).app (op T)
        ((prod.map (yoneda.map f) (𝟙 F)).app (op T) z)
      = (prod.snd : yoneda.obj U ⨯ F ⟶ F).app (op T) z :=
  calc (prod.snd : yoneda.obj V ⨯ F ⟶ F).app (op T)
        ((prod.map (yoneda.map f) (𝟙 F)).app (op T) z)
      = (prod.map (yoneda.map f) (𝟙 F) ≫ prod.snd).app (op T) z := rfl
    _ = (prod.snd ≫ 𝟙 F).app (op T) z := by rw [prod.map_snd (yoneda.map f) (𝟙 F)]
    _ = (prod.snd : yoneda.obj U ⨯ F ⟶ F).app (op T) z := by rw [Category.comp_id]

/-- A morphism of the big fppf site of `S` whose image lies in the image of an open
immersion `j` factors through `j`. -/
private theorem exists_hom_comp_eq_of_range_subset {U V W : BigFppfOver B S hS} (j : U ⟶ V)
    [IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] (f : W ⟶ V)
    (h : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ c : W ⟶ U, c ≫ j = f := by
  have hφ : IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map f) h ≫ (BigFppfOver.toScheme B S hS).map j
      = (BigFppfOver.toScheme B S hS).map f :=
    IsOpenImmersion.lift_fac _ _ _
  have e : ∀ {A : BigFppfOver B S hS} (g : A ⟶ V),
      B.inclusion.map A.hom = (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map V.hom :=
    fun g => by
      simp only [Functor.comp_map, ← Functor.map_comp]
      exact congrArg B.inclusion.map (Over.w g).symm
  have hcompat : IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map f) h ≫ B.inclusion.map U.hom
      = B.inclusion.map W.hom := by
    rw [e j, e f, ← Category.assoc, hφ]
  obtain ⟨c, hcmap⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hcompat
  refine ⟨c, (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  rw [Functor.map_comp, hcmap, IsOpenImmersion.lift_fac]

/-- Every point of a coproduct in the big fppf site of `S` lies in the image of some member. -/
private theorem exists_mem_range_of_isColimit_cofan {I : Type w}
    {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V}
    (hV : IsColimit (Cofan.mk V j)) (x : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)) :=
  Set.mem_iUnion.1 ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ _)

/-- Let `V` be a coproduct of the family `U i` inside the big fppf site of `S`. A section of
`yoneda.obj V ⨯ F` over `T` becomes, on the `i`-th member of a family of pairwise disjoint open
subobjects covering `T`, the image of a section of `yoneda.obj (U i) ⨯ F`. -/
private theorem exists_decomposition_prod_yoneda_obj_of_isColimit_cofan {I : Type w}
    {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V}
    (hV : IsColimit (Cofan.mk V j)) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver B S hS) (y : (yoneda.obj V ⨯ F).obj (op T)) :
    ∃ (W : I → BigFppfOver B S hS) (p : ∀ i, W i ⟶ T),
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ i i', i ≠ i' → ∀ (y₁ : (BigFppfOver.toScheme B S hS).obj (W i))
        (y₂ : (BigFppfOver.toScheme B S hS).obj (W i')),
        (BigFppfOver.toScheme B S hS).map (p i) y₁ ≠
          (BigFppfOver.toScheme B S hS).map (p i') y₂) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ i, ∃ z : (yoneda.obj (U i) ⨯ F).obj (op (W i)),
        (prod.map (yoneda.map (j i)) (𝟙 F)).app (op (W i)) z
          = (yoneda.obj V ⨯ F).map (p i).op y) := by
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  set s : T ⟶ V := (prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T) y with hsdef
  set x : F.obj (op T) := (prod.snd : yoneda.obj V ⨯ F ⟶ F).app (op T) y
  have hopenpre : ∀ i, IsOpen (((BigFppfOver.toScheme B S hS).map s) ⁻¹'
      (Set.range ((BigFppfOver.toScheme B S hS).map (j i)))) := by
    intro i
    have := hoi i
    refine IsOpen.preimage ((BigFppfOver.toScheme B S hS).map s).continuous ?_
    have h := ((BigFppfOver.toScheme B S hS).map (j i)).opensRange.isOpen
    rwa [Scheme.Hom.coe_opensRange] at h
  choose W p hpoi hprange hpuniv using fun i =>
    exists_restrict_bigFppfOver T ⟨_, hopenpre i⟩
  have hmem : ∀ i w, (BigFppfOver.toScheme B S hS).map s ((BigFppfOver.toScheme B S hS).map (p i) w)
      ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := fun i w => by
    have : (BigFppfOver.toScheme B S hS).map (p i) w ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (p i)) := ⟨w, rfl⟩
    rwa [hprange i] at this
  have hps : ∀ i, Set.range ((BigFppfOver.toScheme B S hS).map (p i ≫ s)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    rintro i _ ⟨w, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hmem i w
  have hc : ∀ i, ∃ c : W i ⟶ U i, c ≫ j i = p i ≫ s := fun i =>
    have := hoi i
    exists_hom_comp_eq_of_range_subset (j i) (p i ≫ s) (hps i)
  choose c hcfac using hc
  refine ⟨W, p, hpoi, ?_, ?_, fun i => ?_⟩
  · intro i i' hii' y₁ y₂ heq
    obtain ⟨z₁, hz₁⟩ := hmem i y₁
    obtain ⟨z₂, hz₂⟩ := hmem i' y₂
    refine ne_toScheme_map_cofan hV hii' z₁ z₂ ?_
    rw [hz₁, hz₂, heq]
  · intro t
    obtain ⟨i, hi⟩ := exists_mem_range_of_isColimit_cofan hV
      ((BigFppfOver.toScheme B S hS).map s t)
    exact ⟨i, by rwa [hprange i]⟩
  refine ⟨yonedaEquiv (prod.lift (yoneda.map (c i))
    (yonedaEquiv.symm (F.map (p i).op x))), prod_section_ext ?_ ?_⟩
  · rw [fst_app_prod_map_yoneda_map, ← yonedaEquiv_comp, prod.lift_fst, yonedaEquiv_yoneda_map,
      hcfac i,
      NatTrans.naturality_apply (prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V) (p i).op y,
      ← hsdef]
    exact rfl
  · rw [snd_app_prod_map_yoneda_map, ← yonedaEquiv_comp, prod.lift_snd, Equiv.apply_symm_apply,
      NatTrans.naturality_apply (prod.snd : yoneda.obj V ⨯ F ⟶ F) (p i).op y]

/-- **The restriction of a sheaf to a coproduct of objects of the site is the coproduct of its
restrictions.**

Let `V` be a coproduct of the family `U i` *inside* the big fppf site of `S`, let `F` be an
fppf sheaf of sets on that site, and let `G` be a sheaf coproduct of the restrictions
`yoneda.obj (U i) ⨯ F` of `F` to the members. Then `G` is isomorphic to the restriction
`yoneda.obj V ⨯ F` of `F` to `V`, compatibly with the coproduct injections.

This is the identification with which the proof of Stacks 04SK opens: for a covering
`{S i → S}` of the base with coproduct `V`, the morphism `∐ᵢ (h_{S i} × F) ⟶ F` *is* the
projection `h_V × F ⟶ F`, that is, the base change of `V ⟶ S` along `F ⟶ S`.

The isomorphism comes from `AlgebraicGeometry.isIso_hom_desc_of_decomposition`: a section of
`h_V × F` over `T` is a pair of a morphism `T ⟶ V` and a section of `F`, and the preimages in
`T` of the members `U i` are pairwise disjoint open subobjects covering `T` over which the
morphism to `V` factors through a single member. -/
theorem exists_iso_prod_yoneda_obj_of_isColimit_cofan {I : Type w}
    {U : I → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V}
    (hV : IsColimit (Cofan.mk V j)) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFi : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj (U i) ⨯ F))
    (hVF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj V ⨯ F))
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, (⟨yoneda.obj (U i) ⨯ F, hFi i⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι)) :
    ∃ e : G.obj ≅ yoneda.obj V ⨯ F,
      ∀ i, (ι i).hom ≫ e.hom = prod.map (yoneda.map (j i)) (𝟙 F) := by
  classical
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  have hjmono : ∀ i, Mono (j i) := fun i =>
    have := hoi i
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  set κ : ∀ i, (⟨yoneda.obj (U i) ⨯ F, hFi i⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨yoneda.obj V ⨯ F, hVF⟩ := fun i =>
    ObjectProperty.homMk (prod.map (yoneda.map (j i)) (𝟙 F))
  -- the two components of the image of a section under `κ i`
  have hκfst : ∀ (i : I) (T : BigFppfOver B S hS)
      (z : (yoneda.obj (U i) ⨯ F).obj (op T)),
      (prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T) ((κ i).hom.app (op T) z)
        = (prod.fst : yoneda.obj (U i) ⨯ F ⟶ yoneda.obj (U i)).app (op T) z ≫ j i :=
    fun i _ z => fst_app_prod_map_yoneda_map (j i) F z
  have hκsnd : ∀ (i : I) (T : BigFppfOver B S hS)
      (z : (yoneda.obj (U i) ⨯ F).obj (op T)),
      (prod.snd : yoneda.obj V ⨯ F ⟶ F).app (op T) ((κ i).hom.app (op T) z)
        = (prod.snd : yoneda.obj (U i) ⨯ F ⟶ F).app (op T) z :=
    fun i _ z => snd_app_prod_map_yoneda_map (j i) F z
  have hinj : ∀ (i : I) (T : BigFppfOver B S hS),
      Function.Injective ((κ i).hom.app (op T)) := by
    intro i T z z' h
    refine prod_section_ext ?_ ?_
    · have h₁ := congrArg ((prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T)) h
      rw [hκfst, hκfst] at h₁
      have := hjmono i
      exact (cancel_mono (j i)).1 h₁
    · have h₂ := congrArg ((prod.snd : yoneda.obj V ⨯ F ⟶ F).app (op T)) h
      rwa [hκsnd, hκsnd] at h₂
  have hdisj : ∀ (i i' : I), i ≠ i' → ∀ (T : BigFppfOver B S hS)
      (a : (yoneda.obj (U i) ⨯ F).obj (op T)) (b : (yoneda.obj (U i') ⨯ F).obj (op T)),
      (κ i).hom.app (op T) a = (κ i').hom.app (op T) b →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T) := by
    intro i i' hii' T a b h
    have h₁ := congrArg ((prod.fst : yoneda.obj V ⨯ F ⟶ yoneda.obj V).app (op T)) h
    rw [hκfst, hκfst] at h₁
    refine ⟨fun t => ?_⟩
    refine ne_toScheme_map_cofan hV hii'
      ((BigFppfOver.toScheme B S hS).map
        ((prod.fst : yoneda.obj (U i) ⨯ F ⟶ yoneda.obj (U i)).app (op T) a) t)
      ((BigFppfOver.toScheme B S hS).map
        ((prod.fst : yoneda.obj (U i') ⨯ F ⟶ yoneda.obj (U i')).app (op T) b) t) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, h₁]
  have hiso := isIso_hom_desc_of_decomposition ι hcoprod κ hinj hdisj
    (exists_decomposition_prod_yoneda_obj_of_isColimit_cofan hV F)
  exact ⟨asIso (hcoprod.desc (Cofan.mk (⟨yoneda.obj V ⨯ F, hVF⟩ :
    Sheaf (BigFppfOver.topology B S hS) (Type u)) κ)).hom,
    hom_comp_hom_desc_cofan ι hcoprod κ⟩

/-! ### Stacks 04SK -/

namespace SpacesDescent

/-- The morphism out of a coproduct in the big fppf site of `S` induced by a family of morphisms
which are flat, locally of finite presentation and jointly surjective is itself surjective, flat
and locally of finite presentation: flatness and local finite presentation are local on the
source, and the summands form an open cover of the coproduct. -/
theorem surjective_inf_flat_inf_locallyOfFinitePresentation_desc {K : Type u}
    {W : K → BigFppfOver B S hS} {Z U : BigFppfOver B S hS} {c : ∀ k, W k ⟶ Z}
    (hZ : IsColimit (Cofan.mk Z c)) (g : ∀ k, W k ⟶ U)
    (hflat : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (g k)))
    (hlfp : ∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k))) :
    (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hZ g)) := by
  have hoi : ∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c k)) := fun k =>
    isOpenImmersion_toScheme_map_cofan hZ k
  have hcmap : ∀ k, (BigFppfOver.toScheme B S hS).map (c k) ≫
      (BigFppfOver.toScheme B S hS).map (Cofan.IsColimit.desc hZ g) =
        (BigFppfOver.toScheme B S hS).map (g k) := by
    intro k
    rw [← Functor.map_comp]
    exact congrArg _ (Cofan.IsColimit.fac hZ g k)
  have hcovZ : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ k y, (BigFppfOver.toScheme B S hS).map (c k) y = x := fun x =>
    exists_mem_range_of_isColimit_cofan hZ x
  have _hflatloc : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  have _hlfploc : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  let 𝒰 : Scheme.OpenCover.{u} ((BigFppfOver.toScheme B S hS).obj Z) :=
    Scheme.Cover.mkOfCovers K (fun k => (BigFppfOver.toScheme B S hS).obj (W k))
      (fun k => (BigFppfOver.toScheme B S hS).map (c k)) hcovZ fun k => hoi k
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · constructor
    intro x
    obtain ⟨k, w, hw⟩ := hsurj x
    refine ⟨(BigFppfOver.toScheme B S hS).map (c k) w, ?_⟩
    rwa [← Scheme.Hom.comp_apply, hcmap k]
  · exact IsZariskiLocalAtSource.of_openCover 𝒰 fun k => hcmap k ▸ hflat k
  · exact IsZariskiLocalAtSource.of_openCover 𝒰 fun k => hcmap k ▸ hlfp k

end SpacesDescent

/-- The members of a covering of the base of the big fppf site of `S` are jointly surjective,
flat and locally of finite presentation. -/
private theorem exists_mem_range_and_fppf_of_isCovering
    {E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)))}
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩) :
    (∀ x, ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (E.f i))) ∧
      ∀ i, (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        ((BigFppfOver.toScheme B S hS).map (E.f i)) := by
  have hfp := B.isFppfCovering_of_isCovering hE
  rw [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map] at hfp
  rwa [show (((PreZeroHypercover.map (BigFppfOver.forget B S hS) E).map
      (schemeBelowInclusion B.cutoff)).presieve₀) =
      Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (E.X i))
        (fun i => (BigFppfOver.toScheme B S hS).map (E.f i)) from rfl,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfp

/-- An affine object of the big fppf site of `S` with an open immersion `j` into an object
which is locally of finite presentation over `Y` has size at most that of `Y`. -/
private theorem size_le_of_isAffine_of_isOpenImmersion {W X Y : BigFppfOver B S hS} (j : W ⟶ X)
    (f : X ⟶ Y) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f)] :
    ((BigFppfOver.toScheme B S hS).obj W).size ≤ ((BigFppfOver.toScheme B S hS).obj Y).size := by
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (j ≫ f)) := by
    rw [Functor.map_comp]
    infer_instance
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := inferInstance
  exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (j ≫ f))

/-- A covering of the base of the big fppf site of `S` is refined by a family indexed by the
points of `S`: over each point, an affine open `W s` of a member of the covering, whose map to
the base is flat, locally of finite presentation and of size at most that of `S`, these maps
being jointly surjective. -/
private theorem exists_affine_refinement_of_isCovering
    {E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)))}
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩) :
    ∃ (i₀ : (BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS))) → E.I₀)
      (W : (BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS))) → BigFppfOver B S hS)
      (j : ∀ s, W s ⟶ E.X (i₀ s)),
      (∀ s, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j s))) ∧
      (∀ s, IsAffine ((BigFppfOver.toScheme B S hS).obj (W s))) ∧
      (∀ s, Flat ((BigFppfOver.toScheme B S hS).map (j s ≫ E.f (i₀ s)))) ∧
      (∀ s, LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map (j s ≫ E.f (i₀ s)))) ∧
      (∀ s, ((BigFppfOver.toScheme B S hS).obj (W s)).size ≤
        ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))).size) ∧
      ∀ x, ∃ s, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j s ≫ E.f (i₀ s))) := by
  obtain ⟨hcov, hfl⟩ := exists_mem_range_and_fppf_of_isCovering hE
  have hpt : ∀ s : (BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS))), ∃ (i : E.I₀)
      (O : ((BigFppfOver.toScheme B S hS).obj (E.X i)).Opens)
      (y : (BigFppfOver.toScheme B S hS).obj (E.X i)),
      IsAffineOpen O ∧ y ∈ O ∧ (BigFppfOver.toScheme B S hS).map (E.f i) y = s := by
    intro s
    obtain ⟨i, y, hy⟩ := hcov s
    obtain ⟨O, hO, hyO, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      ((BigFppfOver.toScheme B S hS).obj (E.X i)).isBasis_affineOpens)
      (show y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj (E.X i)).Opens) from trivial)
    exact ⟨i, O, y, hO, hyO, hy⟩
  choose i₀ O y₀ hOaff hyO hy₀ using hpt
  choose W j hjoi hjrange _ using fun s => exists_restrict_bigFppfOver (E.X (i₀ s)) (O s)
  have hWaff : ∀ s, IsAffine ((BigFppfOver.toScheme B S hS).obj (W s)) := fun s => by
    have := hjoi s
    have h : IsAffineOpen ((BigFppfOver.toScheme B S hS).map (j s)).opensRange := by
      rw [show ((BigFppfOver.toScheme B S hS).map (j s)).opensRange = O s from
        TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, hjrange s])]
      exact hOaff s
    rw [← Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion] at h
    have : IsAffine (⊤ : ((BigFppfOver.toScheme B S hS).obj (W s)).Opens).toScheme := h
    exact IsAffine.of_isIso (Scheme.topIso _).inv
  have hlfp : ∀ s, LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (j s ≫ E.f (i₀ s))) := fun s => by
    have := hjoi s
    have := (hfl (i₀ s)).2
    rw [Functor.map_comp]
    infer_instance
  refine ⟨i₀, W, j, hjoi, hWaff, fun s => ?_, hlfp, fun s => ?_, fun x => ?_⟩
  · have := hjoi s
    have := (hfl (i₀ s)).1
    rw [Functor.map_comp]
    infer_instance
  · have := hWaff s
    have := hjoi s
    have := (hfl (i₀ s)).2
    exact size_le_of_isAffine_of_isOpenImmersion (j s) (E.f (i₀ s))
  · obtain ⟨w, hw⟩ : y₀ x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j x)) := by
      rw [hjrange x]
      exact hyO x
    refine ⟨x, w, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hw]
    exact hy₀ x

/-- Let `Z` be a coproduct in the big fppf site of `S` of objects `W s`, each mapping by `j s`
to a member of a covering of the base, and let `v : Z ⟶ S` restrict to these maps. If the
restrictions of the members `F_i` of a sheaf `F` along the `j s` have étale atlases of size at
most `μ`, then the base change of `F` along `v`, which is the coproduct of these restrictions,
is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_of_isColimit_cofan
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)))}
    (hFi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F))
    {K : Type u} {i₀ : K → E.I₀} {W : K → BigFppfOver B S hS} (j : ∀ s, W s ⟶ E.X (i₀ s))
    {Z : BigFppfOver B S hS} {c : ∀ s, W s ⟶ Z} (hZ : IsColimit (Cofan.mk Z c))
    {v : Z ⟶ Over.mk (𝟙 (B.obj hS))} (hcv : ∀ s, c s ≫ v = j s ≫ E.f (i₀ s))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hatlas : ∀ s, ∃ (Y : BigFppfOver B S hS)
      (b : yoneda.obj Y ⟶ pullback
        (prod.fst : yoneda.obj (E.X (i₀ s)) ⨯ F ⟶ yoneda.obj (E.X (i₀ s))) (yoneda.map (j s))),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      ((BigFppfOver.toScheme B S hS).obj Y).size ≤ μ) :
    IsAlgebraicSpace B S hS
      (pullback ((Space.isTerminal_yoneda_obj_base B S hS).from F) (yoneda.map v)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let π : F ⟶ yoneda.obj T₀ := (Space.isTerminal_yoneda_obj_base B S hS).from F
  let X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun s =>
    pullback (prod.fst : yoneda.obj (E.X (i₀ s)) ⨯ F ⟶ yoneda.obj (E.X (i₀ s)))
      (yoneda.map (j s))
  have hX : ∀ s, IsAlgebraicSpace B S hS (X s) := fun s =>
    isAlgebraicSpace_of_relativelyRepresentable B S hS (pullback.fst _ _)
      ((Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
        (IsPullback.of_hasPullback _ _).flip (Functor.relativelyRepresentable.map yoneda (j s)))
      (hFi (i₀ s))
  let ζ : ∀ s, X s ⟶ F := fun s => pullback.fst _ _ ≫ prod.snd
  let q : ∀ s, X s ⟶ yoneda.obj (W s) := fun s => pullback.snd _ _
  have hsq : ∀ s, IsPullback (ζ s) (q s) π (yoneda.map (j s ≫ E.f (i₀ s))) := fun s => by
    have hf : Over.mkIdTerminal.from (E.X (i₀ s)) = E.f (i₀ s) := Over.mkIdTerminal.hom_ext _ _
    have hB := (Space.isPullback_prod_fst_snd_yoneda_obj (E.X (i₀ s)) F).flip
    rw [hf] at hB
    simpa only [← Functor.map_comp] using (IsPullback.of_hasPullback
      (prod.fst : yoneda.obj (E.X (i₀ s)) ⨯ F ⟶ yoneda.obj (E.X (i₀ s)))
      (yoneda.map (j s))).paste_horiz hB
  choose Yat b hbsurj hbet hYsize using hatlas
  obtain ⟨hZs⟩ := nonempty_isColimit_cofan_toScheme (B := B) (S := S) (hS := hS) hZ
  let pp : ∀ s, X s ⟶ pullback π (yoneda.map v) := fun s =>
    pullback.lift (ζ s) (q s ≫ yoneda.map (c s)) (by
      rw [Category.assoc (q s), ← Functor.map_comp, hcv]
      exact (hsq s).w)
  have hpb : ∀ s, IsPullback (pp s) (q s) (pullback.snd π (yoneda.map v)) (yoneda.map (c s)) := by
    intro s
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π _)
    rw [pullback.lift_fst, ← Functor.map_comp, hcv]
    exact hsq s
  let Gsh : Sheaf J (Type u) := ⟨pullback π (yoneda.map v),
    Presheaf.isSheaf_pullback _ π (yoneda.map v) hF (isAlgebraicSpace_yoneda B S hS Z).isSheaf
      (isAlgebraicSpace_yoneda B S hS T₀).isSheaf⟩
  exact isAlgebraicSpace_coproduct_of_size_le B S hS X hX Gsh
    (fun s => (⟨pp s⟩ : (⟨X s, (hX s).isSheaf⟩ : Sheaf J (Type u)) ⟶ Gsh))
    (Space.nonempty_isColimit_cofanMk_of_isPullback B S hS
      (fun s => J.yoneda.map (c s)) (Space.isColimit_yoneda_of_isColimit_toScheme B S hS W Z c hZs)
      (⟨pullback.snd π (yoneda.map v)⟩ : Gsh ⟶ J.yoneda.obj Z)
      (fun s => (⟨pp s⟩ : (⟨X s, (hX s).isSheaf⟩ : Sheaf J (Type u)) ⟶ Gsh))
      (fun s => (⟨q s⟩ : (⟨X s, (hX s).isSheaf⟩ : Sheaf J (Type u)) ⟶ J.yoneda.obj (W s)))
      (fun s => IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u)) (hpb s))).some
    Yat b hbsurj hbet (Equiv.refl _) hℵ hμ hK hYsize

/-- **The refinement step of Stacks 04SK and Stacks 04U0.** Let `F` be a sheaf on the big fppf
site of `S` and let `{S i → S}` be a covering family of the base whose restrictions
`F_i = h_{S i} × F` are algebraic spaces. Suppose that, for a cardinal `κ` below the cutoff of
the site, the restriction of `F_i` to every affine open `W` of a member `S i` has a surjective
étale atlas of size at most `κ`. Then `F` is an algebraic space.

This is the common part of the proofs of Stacks 04SK and Stacks 04U0. The source's chart is
`∐ F_i ⟶ F`, the base change of `∐ S_i ⟶ S`, and the disjoint union `∐ S_i` need not be an
object of the site; so the covering is refined first. For every point `s` of `S` choose a member
`S_{i s}` with a point over `s` and an affine open `W s` of it through that point. Each `W s` has
size at most `size (S)` (Stacks 04T7), and there are at most `2 ^ size (S)` of them, so their
disjoint union `Z` is an object of the site, and `Z ⟶ S` is surjective, flat and locally of
finite presentation. The restriction `h_{W s} × F` is the base change of `F_{i s}` along
`W s ⟶ S_{i s}`, and it has an atlas of size at most `κ` by hypothesis; so the base change
`F ×_S Z`, which is the coproduct of these restrictions, is an algebraic space by Stacks 02WQ
(`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`). Its projection to `F` is the base
change of `Z ⟶ S`, so it is representable, surjective, flat and locally of finite presentation,
and Stacks 04S6, condition (3), concludes. -/
theorem isAlgebraicSpace_of_isCovering_of_atlas_size_le
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS))))
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩)
    (hFi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F))
    {κ : Cardinal.{u}} (hκ : κ < B.cutoff)
    (hatlas : ∀ (i : E.I₀) (W : BigFppfOver B S hS) (j : W ⟶ E.X i),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) →
      ∃ (Y : BigFppfOver B S hS)
        (b : yoneda.obj Y ⟶ pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i))
          (yoneda.map j)),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
        ((BigFppfOver.toScheme B S hS).obj Y).size ≤ κ) :
    IsAlgebraicSpace B S hS F := by
  classical
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) := by
    have h₁ : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.inf
    exact MorphismProperty.IsStableUnderBaseChange.inf
      (P := (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}))
  obtain ⟨i₀, W, j, hjoi, hWaff, hgflat, hglfp, hWsize, hgsurj⟩ :=
    exists_affine_refinement_of_isCovering hE
  let g : ∀ s, W s ⟶ T₀ := fun s => j s ≫ E.f (i₀ s)
  -- the size bounds
  set μ : Cardinal.{u} := 2 ^ max ((BigFppfOver.toScheme B S hS).obj T₀).size κ
  have hle : ∀ c : Cardinal.{u},
      c ≤ max ((BigFppfOver.toScheme B S hS).obj T₀).size κ → c ≤ μ :=
    fun c hc => hc.trans (Cardinal.cantor _).le
  have hℵ : ℵ₀ ≤ μ := hle _ ((Scheme.aleph0_le_size _).trans (le_max_left _ _))
  have hμ : μ < B.cutoff :=
    B.cutoff_isStrongPrelimit (max_lt T₀.left.property hκ)
  have hK : #((BigFppfOver.toScheme B S hS).obj T₀ : Type u) ≤ μ :=
    (Scheme.mk_le_two_pow_size _).trans
      (Cardinal.power_le_power_left two_ne_zero (le_max_left _ _))
  -- the disjoint union of the `W s` in the site, and the base change of `F` to it
  obtain ⟨Z, c, ⟨hZ⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS W
    ((schemeSize_coproduct_le _ μ hℵ hK fun s =>
      hle _ ((hWsize s).trans (le_max_left _ _))).trans_lt hμ)
  let v : Z ⟶ T₀ := Cofan.IsColimit.desc hZ g
  let π : F ⟶ yoneda.obj T₀ := (Space.isTerminal_yoneda_obj_base B S hS).from F
  have hGalg : IsAlgebraicSpace B S hS (pullback π (yoneda.map v)) :=
    isAlgebraicSpace_pullback_of_isColimit_cofan hF hFi j hZ (v := v)
      (fun s => Cofan.IsColimit.fac hZ g s) hℵ hμ hK fun s =>
        let ⟨Y, b, hb₁, hb₂, hb₃⟩ := hatlas (i₀ s) (W s) (j s) (hWaff s) (hjoi s)
        ⟨Y, b, hb₁, hb₂, hle _ (hb₃.trans (le_max_right _ _))⟩
  -- the chart `F ×_S Z ⟶ F`, and Stacks 04S6
  have hsqv := (IsPullback.of_hasPullback π (yoneda.map v)).flip
  exact Space.isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap B S hS
    (Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS
      (Space.bootstrap04S6QuotientSheaf B S hS)) F hF _ hGalg
    (pullback.fst π (yoneda.map v))
    ((Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback hsqv
      (Functor.relativelyRepresentable.map yoneda v))
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsqv
      (Space.presheaf_yoneda_map_of_inverseImage B S hS hPbc v
        (SpacesDescent.surjective_inf_flat_inf_locallyOfFinitePresentation_desc hZ g
          hgflat hglfp hgsurj)))


/-- **Stacks 04SK**.

Let `F` be a presheaf of sets on the big fppf site of `S` and let `{S i → S}` be a covering
family of the base. Assume

1. `F` is a sheaf (`hF`);
2. each restriction `F_i = h_{S i} × F` is an algebraic space (`hFi`);
3. the coproduct `∐ F_i` is an algebraic space: `G`, presented by the colimit cofan `hcoprod`
   with legs `ι`, is a coproduct of the `F_i` in sheaves, and it is an algebraic space (`hG`).

Then `F` is an algebraic space.

The coproduct in (3) is given as data because the index type of the covering is of the next
universe, so a coproduct of the `F_i` need not exist in sheaves of `Type u`; any two coproducts
are isomorphic, so this is the source's hypothesis.

The source's proof applies Stacks 04S6 to `∐ F_i ⟶ F`, the base change of `∐ S_i ⟶ S`. Inside
the site this chart is built from a refinement of the covering of size bounded by `S`, which is
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_atlas_size_le`; what that lemma asks for is
a bounded étale atlas of the restriction of each `F_i` to an affine open `W` of `S_i`, and
hypothesis (3) is exactly what supplies it. An étale atlas `U` of `∐ F_i` splits along the
coproduct into étale atlases `U_i` of the `F_i`, which are open in `U`
(`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`). The restriction of
`F_i` to `W` is the base change of `F_i` along `W ⟶ S_i`, so `W ×_{S_i} U_i` is an étale atlas
of it, of size at most `max (size S) (size U)`.

The last step is Stacks 04S6, condition (3), for a chart representable by objects of the site:
a sheaf which receives a representable, surjective, flat, locally finitely presented morphism
from an algebraic space is an algebraic space. -/
@[stacks 04SK]
theorem isAlgebraicSpace_of_isCovering
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS))))
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩)
    (hFi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F))
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i : E.I₀, (⟨yoneda.obj (E.X i) ⨯ F, (hFi i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι))
    (hG : IsAlgebraicSpace B S hS G.obj) :
    IsAlgebraicSpace B S hS F := by
  classical
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  -- the members of the covering are locally of finite presentation over the base
  obtain ⟨-, hfl⟩ := exists_mem_range_and_fppf_of_isCovering hE
  -- an étale atlas of the coproduct, split along the coproduct into atlases of the members
  obtain ⟨U, f, hfsurj, hfet⟩ := hG.exists_atlas
  obtain ⟨Up, p, hpoi, hpsec, -, -, hpuniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hcoprod U (yonedaEquiv f)
  choose z hz using hpsec
  let a : ∀ i, yoneda.obj (Up i) ⟶ yoneda.obj (E.X i) ⨯ F := fun i => yonedaEquiv.symm (z i)
  have ha : ∀ i, IsPullback (yoneda.map (p i)) (a i) f (ι i).hom := fun i => by
    simpa only [Equiv.symm_apply_apply] using
      isPullback_yoneda_clopen_piece ι hcoprod (p i) (hpoi i) (yonedaEquiv f) (z i) (hz i)
        (hpuniv i)
  have _ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  let σ : ∀ i, Up i ⟶ E.X i := fun i => yoneda.preimage (a i ≫ prod.fst)
  have hσ : ∀ i, yoneda.map (σ i) = a i ≫ prod.fst := fun i => yoneda.map_preimage _
  have hUpsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (Up i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj U).size := fun i =>
    have := hpoi i
    Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))
  -- the atlas of the restriction to an affine open `W` of a member is the base change of `U_i`
  refine isAlgebraicSpace_of_isCovering_of_atlas_size_le hF E hE hFi
    (max_lt T₀.left.property U.left.property) (fun i W j hWaff hjoi => ?_)
  let b : yoneda.obj (Limits.pullback j (σ i)) ⟶
      pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i)) (yoneda.map j) :=
    pullback.lift (yoneda.map (pullback.snd j (σ i)) ≫ a i)
      (yoneda.map (pullback.fst j (σ i))) (by
        rw [Category.assoc, ← hσ, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hb : IsPullback (yoneda.map (pullback.snd j (σ i))) b (a i)
      (pullback.fst _ _ : pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i))
        (yoneda.map j) ⟶ _) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
    simp only [b, pullback.lift_snd, ← hσ]
    exact (IsPullback.of_hasPullback j (σ i)).flip.map yoneda
  have hWsize : ((BigFppfOver.toScheme B S hS).obj W).size ≤
      ((BigFppfOver.toScheme B S hS).obj T₀).size := by
    have := (hfl i).2
    exact size_le_of_isAffine_of_isOpenImmersion j (E.f i)
  exact ⟨Limits.pullback j (σ i), b,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hb
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback (ha i) hfsurj),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hb
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback (ha i) hfet),
    (Space.size_pullback_le B S hS j (σ i)).trans (max_le_max hWsize (hUpsize i))⟩

end AlgebraicGeometry

end
