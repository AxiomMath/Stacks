module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Limits.CofanSummandIso
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# A morphism out of a coproduct of representables is representable by objects of the site

Let `S` be a scheme contained in a big fppf site `B`, let `W` be an object of the big fppf site
of `S` which is the coproduct of a family `V` of objects of that site, and let
`q : W ⟶ X` be a morphism of fppf sheaves of `Type (u + 1)` out of the representable sheaf of
`W`. If the restriction of `q` to every summand is representable by objects of the site, and if
at every scheme-valued point of `X` the objects representing those restrictions carry one common
size bound below the cutoff, then `q` itself is representable by objects of the site.

The base change of `q` along a point of `X` is computed summand by summand: a coproduct of
sheaves of sets is a universal colimit, so the base change of the coproduct decomposition of
`W` is a coproduct decomposition of that base change, and each of its members is the object of
the site representing the base change of the corresponding restriction. The uniform size bound
puts the coproduct of those objects back inside the site, and the representable sheaf of that
coproduct is the coproduct of their representable sheaves, so it is the base change.

The size bound is the hypothesis that cannot be dropped, and it is where the set-theoretic
content of **Stacks 0AIS** enters: the index type of the coproduct decomposition of `W` carries
no bound against the cofinality of the cutoff, so the coproduct of the representing objects is
inside the site only because all of them are bounded by one cardinal.

## Main results

* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isColimitCofan_of_size_le`: the
  criterion.
* `AlgebraicGeometry.FormalSpace.mono_prodLift_pullback_of_relativelyRepresentable`: the
  representing object of a base change sits inside the product of the site by a monomorphism.
* `AlgebraicGeometry.FormalSpace.exists_size_bound_of_relativelyRepresentable`: the uniform
  bound the criterion asks for, for a family of morphisms out of subobjects of one object of
  the site.
* `CategoryTheory.relativelyRepresentable_uliftYoneda_iff`: relative representability along the
  sheaf-valued universe-lifted Yoneda embedding is relative representability of the underlying
  morphism of presheaves along the presheaf-valued one. This is what carries the criterion over
  to the presheaf formulation in which the algebraic-space condition is stated.

## Implementation notes

The statement is in the category of sheaves rather than of presheaves, because the coproduct
decomposition `W = ∐ V i` holds for the *sheaf* represented by `W` and not for the presheaf: it
is the fppf descent statement
`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`, whose colimit is taken
among sheaves. Fibre products of sheaves are computed as fibre products of presheaves, so the
conclusion transports to the presheaf statement along
`CategoryTheory.GrothendieckTopology.uliftYonedaCompSheafToPresheaf`.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The members of a cofan may be replaced by isomorphic objects without disturbing the
colimit property. -/
private def isColimitCofanCompIso {D : Type*} [Category* D] {ι : Type*}
    {F G : ι → D} {P : D} (f : ∀ i, F i ⟶ P) (hf : IsColimit (Cofan.mk P f))
    (e : ∀ i, G i ≅ F i) : IsColimit (Cofan.mk P fun i => (e i).hom ≫ f i) :=
  Cofan.isColimitCompIso f hf e

/-- **A morphism out of a coproduct of representables is representable by objects of the
site.** Let `W` be an object of the big fppf site of `S` whose representable sheaf is the
coproduct of those of a family `V` indexed by a type of `Type u`, and let `q` be a morphism of
fppf sheaves of `Type (u + 1)` out of it. If every restriction of `q` to a summand is
representable by objects of the site, and if at every scheme-valued point of the target the
objects of the site representing those restrictions are of size at most one cardinal below the
cutoff which also bounds the index type, then `q` is representable by objects of the site.

The base change along a point decomposes as the coproduct of the base changes of the
restrictions, coproducts of sheaves of sets being universal colimits, and the uniform bound
puts that coproduct back inside the site. -/
theorem relativelyRepresentable_of_isColimitCofan_of_size_le
    {ι : Type u} (V : ι → BigFppfOver B S hS) {W : BigFppfOver B S hS} (j : ∀ i, V i ⟶ W)
    (hcofan : IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W)
      fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i)))
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X)
    (hrep : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i) ≫ q))
    (hbound : ∀ (T : BigFppfOver B S hS)
        (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X),
      ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ #ι ≤ μ ∧
        ∀ i, ((BigFppfOver.toScheme B S hS).obj ((hrep i).pullback ξ)).size ≤ μ) :
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable q := by
  intro T ξ
  obtain ⟨μ, hμ, hιμ, hZμ⟩ := hbound T ξ
  -- the base change of `q` along `ξ`, and its decomposition along the coproduct
  have hApb : IsPullback (pullback.fst q ξ) (pullback.snd q ξ) q ξ :=
    IsPullback.of_hasPullback q ξ
  have hpaste : ∀ i, IsPullback
      (pullback.snd ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))
        (pullback.fst q ξ) ≫ pullback.snd q ξ)
      (pullback.fst ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))
        (pullback.fst q ξ)) ξ
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i) ≫ q) := fun i =>
    (IsPullback.of_hasPullback
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))
      (pullback.fst q ξ)).flip.paste_horiz hApb.flip
  -- each member of the decomposition is the representing object of the site
  have he : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj ((hrep i).pullback ξ) ≅
      pullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))
        (pullback.fst q ξ) := fun i =>
    ((hrep i).isPullback ξ).flip.isoIsPullback _ _ (hpaste i)
  -- the coproduct of the representing objects is again an object of the site
  obtain ⟨V', j', -, -, -, -, ⟨hcofanV'⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS
      (fun i => (hrep i).pullback ξ) hμ hιμ hZμ
  have eA : pullback q ξ ≅ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V' :=
    (Cofan.isColimitCompIso
      (fun i => pullback.snd ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))
        (pullback.fst q ξ))
      (Sheaf.isColimitCofanMkPullback (BigFppfOver.topology B S hS)
        (fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i)) hcofan
        (pullback.fst q ξ)) he).coconePointUniqueUpToIso hcofanV'
  refine ⟨V', (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.preimage
      (eA.inv ≫ pullback.snd q ξ), eA.inv ≫ pullback.fst q ξ, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ eA.symm rfl
    ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_preimage _).symm
  rw [(BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_preimage, Category.assoc,
    Category.assoc, hApb.w]

/-! ### The uniform size bound -/

/-- **The representing object of a base change sits inside the product of the site by a
monomorphism.** Let `a : U₀ ⟶ X` be a morphism of fppf sheaves out of the representable sheaf
of an object of the site which is representable by objects of the site, let `ξ : T ⟶ X` be a
scheme-valued point of its target and let `k : U₀ ⟶ W` be a monomorphism of the site. Then the
object of the site representing the base change of `a` along `ξ` maps monomorphically to the
product `W ⨯ T`.

Two morphisms into the representing object which agree after both projections agree, which is
the universal property of the base change read inside the site; the first projection is
recovered from its composite with `k` because `k` is a monomorphism. -/
theorem mono_prodLift_pullback_of_relativelyRepresentable
    [HasBinaryProducts (BigFppfOver B S hS)]
    {U₀ W : BigFppfOver B S hS} {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {a : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U₀ ⟶ X}
    (hrep : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable a)
    {T : BigFppfOver B S hS}
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X)
    (k : U₀ ⟶ W) [Mono k] :
    Mono (prod.lift (hrep.fst' ξ ≫ k) (hrep.snd ξ)) :=
  ⟨fun _ _ h => hrep.hom_ext' ((cancel_mono k).mp (by simpa using h =≫ prod.fst))
    (by simpa using h =≫ prod.snd)⟩

/-- **The representing object of a base change is bounded by the product of the site.** The
monomorphism of `AlgebraicGeometry.FormalSpace.mono_prodLift_pullback_of_relativelyRepresentable`
is a monomorphism of schemes, the forgetful functor to schemes preserving fibre products, and
a monomorphism of schemes bounds the size of its source by
`AlgebraicGeometry.Scheme.size_le_of_mono`.

The bound does not mention the source of `a`, so it is uniform over a family of morphisms out
of subobjects of one object `W` of the site. That is what makes it usable for the coproduct
criterion above. -/
theorem size_pullback_le_of_relativelyRepresentable
    [HasBinaryProducts (BigFppfOver B S hS)]
    {U₀ W : BigFppfOver B S hS} {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {a : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U₀ ⟶ X}
    (hrep : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable a)
    {T : BigFppfOver B S hS}
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X)
    (k : U₀ ⟶ W) [Mono k] :
    ((BigFppfOver.toScheme B S hS).obj (hrep.pullback ξ)).size ≤
      max (2 ^ #((BigFppfOver.toScheme B S hS).obj (W ⨯ T)))
        (((BigFppfOver.toScheme B S hS).obj (W ⨯ T)).size) := by
  have := mono_prodLift_pullback_of_relativelyRepresentable B S hS hrep ξ k
  exact Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map
    (prod.lift (hrep.fst' ξ ≫ k) (hrep.snd ξ)))

/-- **The uniform bound the coproduct criterion asks for.** For a family of morphisms of fppf
sheaves out of subobjects `V i ⟶ W` of one object `W` of the site, each representable by
objects of the site, the representing objects of all their base changes along one scheme-valued
point `ξ : T ⟶ X` are bounded by a single cardinal below the cutoff, which also bounds the
index type as soon as that is of cardinality below the cutoff.

Both `2 ^ #(W ⨯ T)` and `size (W ⨯ T)` are below the cutoff, which is a strong prelimit
containing the size of every object of the site. -/
theorem exists_size_bound_of_relativelyRepresentable
    [HasBinaryProducts (BigFppfOver B S hS)]
    {ι : Type u} (hι : #ι < B.cutoff)
    {V : ι → BigFppfOver B S hS} {W : BigFppfOver B S hS}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {a : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (V i) ⟶ X}
    (hrep : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable (a i))
    {T : BigFppfOver B S hS}
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X)
    (k : ∀ i, V i ⟶ W) (hk : ∀ i, Mono (k i)) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ #ι ≤ μ ∧
      ∀ i, ((BigFppfOver.toScheme B S hS).obj ((hrep i).pullback ξ)).size ≤ μ := by
  have hWT : ((BigFppfOver.toScheme B S hS).obj (W ⨯ T)).size < B.cutoff :=
    (W ⨯ T).left.property
  have hpts : #((BigFppfOver.toScheme B S hS).obj (W ⨯ T)) < B.cutoff :=
    (mk_scheme_le_two_power_size _).trans_lt (B.cutoff_isStrongPrelimit hWT)
  refine ⟨max (max (2 ^ #((BigFppfOver.toScheme B S hS).obj (W ⨯ T)))
    (((BigFppfOver.toScheme B S hS).obj (W ⨯ T)).size)) #ι,
    max_lt (max_lt (B.cutoff_isStrongPrelimit hpts) hWT) hι, le_max_right _ _, fun i => ?_⟩
  have := hk i
  exact (size_pullback_le_of_relativelyRepresentable B S hS (hrep i) ξ (k i)).trans
    (le_max_left _ _)

/-! ### Passing between the sheaf-valued and the presheaf-valued Yoneda embedding -/

/-- Relative representability only depends on the embedding functor up to isomorphism.

A `private` declaration of this name, statement and content also exists in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SchemeAtlas.lean`. -/
theorem relativelyRepresentable_of_natIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : D} (f : X ⟶ Y)
    (hf : F.relativelyRepresentable f) : G.relativelyRepresentable f := by
  intro a g
  obtain ⟨b, s, p, hp⟩ := hf ((e.app a).hom ≫ g)
  refine ⟨b, s, (e.app b).inv ≫ p, ?_⟩
  apply hp.of_iso (e.app b) (Iso.refl _) (e.app a) (Iso.refl _) <;> simp

/-- **Relative representability is the same condition for the sheaf-valued and for the
presheaf-valued universe-lifted Yoneda embedding.** A morphism of fppf sheaves of `Type (u + 1)`
is representable by objects of the site along
`CategoryTheory.GrothendieckTopology.uliftYoneda` exactly when the underlying morphism of
presheaves is representable by objects of the site along `CategoryTheory.uliftYoneda`.

Fibre products of sheaves are fibre products of the underlying presheaves and the forgetful
functor is fully faithful, which is
`AlgebraicGeometry.Space.relativelyRepresentable_comp_map_iff`; the two embeddings are then
identified by `CategoryTheory.GrothendieckTopology.uliftYonedaCompSheafToPresheaf`.

The algebraic-space condition of `AlgebraicGeometry.Space.IsAlgebraicSpaceULift` is stated for
presheaves, while the coproduct decomposition which the criterion above consumes holds for
sheaves; this is what passes between the two. -/
theorem relativelyRepresentable_uliftYoneda_iff
    {F G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : F ⟶ G) :
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable f ↔
      uliftYoneda.{u + 1}.relativelyRepresentable
        ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map f) := by
  rw [← Space.relativelyRepresentable_comp_map_iff
    ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1})
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) f]
  exact ⟨relativelyRepresentable_of_natIso
      (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.{u + 1} _,
    relativelyRepresentable_of_natIso
      (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.{u + 1}.symm _⟩

/-! ### The chart of a bounded family -/

/-- The identification of the sheaf-valued universe-lifted Yoneda embedding, read as a
presheaf, with the presheaf-valued one. -/
private abbrev glIso :
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} ⋙
      sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅ uliftYoneda.{u + 1} :=
  (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.{u + 1}

/-- **The scheme atlas of a bounded family, with its representability.** A family of morphisms
of fppf sheaves out of objects of the site, each representable by objects of the site, whose
index type and whose members are bounded by one cardinal below the cutoff, descends to a
morphism out of a single object of the site — the coproduct of the family, which the bound puts
inside the site — and that morphism is again representable by objects of the site.

The coproduct injections are open immersions covering the coproduct, so the morphism out of it
is an atlas as soon as the members are; representability of it is
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isColimitCofan_of_size_le`, whose
uniform size bound is
`AlgebraicGeometry.FormalSpace.exists_size_bound_of_relativelyRepresentable`. -/
theorem exists_chart_of_size_le
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type u} (V : I → BigFppfOver B S hS)
    (g : ∀ i, uliftYoneda.{u + 1}.obj (V i) ⟶ X.obj)
    (hg : ∀ i, uliftYoneda.{u + 1}.relativelyRepresentable (g i))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hI : #I ≤ μ)
    (hV : ∀ i, ((BigFppfOver.toScheme B S hS).obj (V i)).size ≤ μ) :
    ∃ (W : BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
      (q : uliftYoneda.{u + 1}.obj W ⟶ X.obj),
      (∀ i, uliftYoneda.{u + 1}.map (k i) ≫ q = g i) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i))) ∧
      (∀ w : (BigFppfOver.toScheme B S hS).obj W,
        ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i))) ∧
      uliftYoneda.{u + 1}.relativelyRepresentable q := by
  classical
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨W, k, hopen, hcov, -, -, ⟨hcofan⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS V hμ hI hV
  have hmono : ∀ i, Mono (k i) := fun i =>
    have := hopen i
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  -- the family, read in the category of sheaves
  let gsh : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (V i) ⟶ X := fun i =>
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).preimage
      ((glIso B S hS).hom.app (V i) ≫ g i)
  have hgshmap : ∀ i, (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map (gsh i)
      = (glIso B S hS).hom.app (V i) ≫ g i := fun i =>
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map_preimage _
  -- the glued morphism of sheaves, and its representability
  let qsh := Cofan.IsColimit.desc hcofan gsh
  have hfac : ∀ i,
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (k i) ≫ qsh = gsh i :=
    Cofan.IsColimit.fac hcofan gsh
  have hfacrep : ∀ i,
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable
        ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (k i) ≫ qsh) := by
    intro i
    rw [hfac i, relativelyRepresentable_uliftYoneda_iff, hgshmap i]
    exact (uliftYoneda.{u + 1}.relativelyRepresentable).comp_mem _ _
      (Functor.relativelyRepresentable.of_isIso _ _) (hg i)
  refine ⟨W, k, (glIso B S hS).inv.app W ≫
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map qsh, ?_, hopen, hcov, ?_⟩
  · intro i
    rw [← Category.assoc, (glIso B S hS).inv.naturality (k i), Category.assoc,
      Functor.comp_map, ← Functor.map_comp, hfac i, hgshmap i, Iso.inv_hom_id_app_assoc]
  · exact (uliftYoneda.{u + 1}.relativelyRepresentable).comp_mem _ _
      (Functor.relativelyRepresentable.of_isIso _ _)
      ((relativelyRepresentable_uliftYoneda_iff B S hS qsh).mp
        (relativelyRepresentable_of_isColimitCofan_of_size_le B S hS V k hcofan qsh hfacrep
          fun T ξ => exists_size_bound_of_relativelyRepresentable B S hS (hI.trans_lt hμ)
            hfacrep ξ k hmono))

end AlgebraicGeometry.FormalSpace

end
