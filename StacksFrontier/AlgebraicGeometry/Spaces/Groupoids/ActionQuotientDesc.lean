module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FppfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientTorsor

/-!
# The morphism out of the quotient of a site object by a group action

Let a group `G` act on an object `V` of a big fppf site over a scheme `S`, and let `X` be a
sheaf on that site. A morphism `h_V ⟶ X` which is **invariant** under the action — unchanged
by precomposition with every automorphism of `V` realizing a group element — descends to a
morphism `V/G ⟶ X` out of the quotient sheaf, uniquely so.

This is the construction the induced morphism `U_p ⟶ X` of [Stacks, Tag 0728] is an instance
of: the space `W_p` of [Stacks, Tag 0726] lies over `X`, so the structure morphism
`h_{W_p} ⟶ X` is invariant under the action of `S_{p+1}` permuting the factors, that action
being an action *over* `X`.

## Main definitions

* `AlgebraicGeometry.Space.actionQuotientDesc` is the descended morphism `V/G ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.sieve_ofArrows_siteActionRelationInclusion_mem_topology`: the `G`
  copies of `V` inside the scheme of arrows of the graph relation cover it.
* `AlgebraicGeometry.Space.yoneda_map_siteActionRelationSource_comp_eq`: an invariant morphism
  to a sheaf coequalizes the source and the target of the graph relation.
* `AlgebraicGeometry.Space.actionProjection_comp_actionQuotientDesc` and
  `AlgebraicGeometry.Space.actionQuotientDesc_unique` are the universal property: the
  descended morphism restricts to the given one along the projection, and is the only morphism
  which does.

## Implementation notes

The coequalizing hypothesis `Stacks.Groupoids.quotientSheafDesc` asks for is an equation
between maps out of the restricted functor of points of the *relation* object, and that object
is a `G`-indexed coproduct, which Yoneda does not break into summands. The equation is
therefore not reduced to summands directly: it is first transported, along
`AlgebraicGeometry.Space.pointsYonedaIso` and its naturality
`AlgebraicGeometry.Space.pointsYonedaIso_hom_comp`, into an equation between maps out of the
presheaf *represented* by the relation object inside the site, where it becomes an equation
between two sections of the sheaf `X`; the `G` copies of `V` cover the relation object, so
`X` being separated for that covering family reduces it to one equation per group element, and
there the source map is the identity and the target map is the automorphism realizing the
element. No `CategoryTheory.Limits.IsColimit` statement about the coproduct in the site is
needed, and no coproduct index hypothesis beyond `Small.{u} G`: that the copies cover is read
off from the Zariski covering of the underlying coproduct of schemes through
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`.

The statements here need only the size hypothesis `hR` placing the relation object in the
site; freeness of the action plays no role. The module is nevertheless seated above
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FreeActionQuotientTorsor.lean`, which is where
`AlgebraicGeometry.Space.siteActionRelationInclusion_comp_target` — the one input identifying
the target map on a summand with the automorphism of the site — is proved.

`StacksFrontier/AlgebraicGeometry/Spaces/Decent/FiniteSchemeFiltration.lean` carries `private`
copies of the covering statement and of the coequalizing statement
(`actionRelationSite_ofArrows_mem_topology`, `yoneda_comp_siteActionRelation_eq`), proved for
a `Shrink.{u} G`-indexed reindexing of the same family and used there only to descend along an
fppf quotient. Those are subsumed by the public statements here and could be retired onto
them.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (V : BigFppfOver B S hS)
  (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)

/-! ### The copies of `V` cover the scheme of arrows of the graph relation -/

omit [Group G] in
/-- The summand inclusion of the relation scheme, read on underlying schemes: the coproduct
inclusion followed by the comparison of the coproduct in the slice over `S` with the
coproduct of the underlying schemes. -/
theorem toScheme_map_siteActionRelationInclusion (g : G) :
    (BigFppfOver.toScheme B S hS).map (siteActionRelationInclusion G B hS V hR g) =
      Sigma.ι (fun _ : G ↦ (underlyingOver B hS V).left) g ≫
        (actionRelationUnderlyingIso (underlyingOver B hS V) G).inv := by
  rw [actionRelationUnderlyingIso_inv_ι]
  rfl

omit [Group G] in
/-- Every summand inclusion of the relation scheme of a group action is an open immersion on
underlying schemes. -/
theorem isOpenImmersion_toScheme_map_siteActionRelationInclusion (g : G) :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (siteActionRelationInclusion G B hS V hR g)) := by
  rw [toScheme_map_siteActionRelationInclusion]
  have h1 : AlgebraicGeometry.IsOpenImmersion
      (Sigma.ι (fun _ : G ↦ (underlyingOver B hS V).left) g) :=
    inferInstance
  have h2 : AlgebraicGeometry.IsOpenImmersion
      (actionRelationUnderlyingIso (underlyingOver B hS V) G).inv :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  exact @AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _ h1 h2

omit [Group G] in
/-- **The `G` copies of `V` inside the scheme of arrows of the graph relation of a group action
cover it.** They are a Zariski covering of the underlying coproduct of schemes, and a Zariski
covering is an fppf covering. -/
theorem sieve_ofArrows_siteActionRelationInclusion_mem_topology :
    Sieve.ofArrows (fun _ : G ↦ V) (siteActionRelationInclusion G B hS V hR) ∈
      BigFppfOver.topology B S hS (siteActionRelationScheme G B hS V hR) := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
    (fun g ↦ isOpenImmersion_toScheme_map_siteActionRelationInclusion G B S hS V hR g)
    (fun x ↦ ?_)
  obtain ⟨g, y, hy⟩ := AlgebraicGeometry.exists_sigmaι_eq
    (fun _ : G ↦ (underlyingOver B hS V).left)
    ((actionRelationUnderlyingIso (underlyingOver B hS V) G).hom.base x)
  have hcancel : (actionRelationUnderlyingIso (underlyingOver B hS V) G).inv.base
      ((actionRelationUnderlyingIso (underlyingOver B hS V) G).hom.base x) = x :=
    congrArg (fun k : (actionRelationScheme (underlyingOver B hS V) G).left ⟶
        (actionRelationScheme (underlyingOver B hS V) G).left ↦ k.base x)
      (actionRelationUnderlyingIso (underlyingOver B hS V) G).hom_inv_id
  have hbase : ((BigFppfOver.toScheme B S hS).map
      (siteActionRelationInclusion G B hS V hR g)).base y = x := by
    have hrw : ((BigFppfOver.toScheme B S hS).map
        (siteActionRelationInclusion G B hS V hR g)).base y =
        (actionRelationUnderlyingIso (underlyingOver B hS V) G).inv.base
          ((Sigma.ι (fun _ : G ↦ (underlyingOver B hS V).left) g).base y) := by
      rw [toScheme_map_siteActionRelationInclusion]
      rfl
    rw [hrw, hy]
    exact hcancel
  exact ⟨g, y, hbase⟩

/-! ### An invariant morphism to a sheaf coequalizes the graph relation -/

variable (a : G →* Aut (underlyingOver B hS V))

omit [Group G] in
/-- The source map of the graph relation of a group action, read under the inclusion of the
site into the schemes over `S`. -/
theorem post_map_siteActionRelationSource :
    (Over.post (X := B.obj hS) B.inclusion).map (siteActionRelationSource G B hS V hR) =
      actionRelationSource (underlyingOver B hS V) G := by
  ext
  rfl

/-- The target map of the graph relation of a group action, read under the inclusion of the
site into the schemes over `S`. -/
theorem post_map_siteActionRelationTarget :
    (Over.post (X := B.obj hS) B.inclusion).map (siteActionRelationTarget G B hS V hR a) =
      actionRelationTarget (underlyingOver B hS V) G a := by
  ext
  rfl

/-- **A morphism to a sheaf which is invariant under a group action coequalizes the source and
the target of the graph relation of the action.**

The two composites are sections of the sheaf over the relation object; the `G` copies of `V`
cover it, and on the copy indexed by `g` the source map is the identity while the target map
is the automorphism of the site realizing `g`, which the morphism is assumed to absorb. -/
theorem yoneda_map_siteActionRelationSource_comp_eq
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f) :
    yoneda.map (siteActionRelationSource G B hS V hR) ≫ f =
      yoneda.map (siteActionRelationTarget G B hS V hR a) ≫ f := by
  have hsf : Presieve.IsSheafFor X
      (Presieve.ofArrows (fun _ : G ↦ V) (siteActionRelationInclusion G B hS V hR)) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (hX.isSheafFor _
        (sieve_ofArrows_siteActionRelationInclusion_mem_topology G B S hS V hR))
  apply yonedaEquiv.injective
  refine hsf.isSeparatedFor.ext ?_
  rintro Z m ⟨g⟩
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality,
    ← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply,
    ← op_comp, ← op_comp, siteActionRelationInclusion_comp_source,
    siteActionRelationInclusion_comp_target, op_id,
    CategoryTheory.Functor.map_id_apply, yonedaEquiv_naturality, hf]

/-! ### The descended morphism out of the quotient -/

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

include hR in
omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The coequalizing hypothesis `Stacks.Groupoids.quotientSheafDesc` asks of an invariant
morphism to a sheaf, read on the restricted functors of points of the graph relation. -/
theorem sourceMap_actionRelation_comp_pointsYonedaIso_hom_comp
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
          (actionRelation (underlyingOver B hS V) G a) ≫
        ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f) =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
          (actionRelation (underlyingOver B hS V) G a) ≫
        ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f) := by
  have hsrc := pointsYonedaIso_hom_comp (Over.post (X := B.obj hS) B.inclusion)
    (siteActionRelationSource G B hS V hR)
  have htgt := pointsYonedaIso_hom_comp (Over.post (X := B.obj hS) B.inclusion)
    (siteActionRelationTarget G B hS V hR a)
  simp only [post_map_siteActionRelationSource, post_map_siteActionRelationTarget] at hsrc htgt
  change (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (actionRelation (underlyingOver B hS V) G a).source) ≫
      ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f) =
    (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (actionRelation (underlyingOver B hS V) G a).target) ≫
      ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f)
  rw [show (actionRelation (underlyingOver B hS V) G a).source =
      actionRelationSource (underlyingOver B hS V) G from prod.lift_snd _ _,
    show (actionRelation (underlyingOver B hS V) G a).target =
      actionRelationTarget (underlyingOver B hS V) G a from prod.lift_fst _ _,
    ← Category.assoc, ← Category.assoc]
  erw [hsrc, htgt, Category.assoc, Category.assoc,
    yoneda_map_siteActionRelationSource_comp_eq G B S hS V hR a hX f hf]

/-- The comparison isomorphism carries the projection onto the quotient to the canonical
projection of the restricted functor of points onto the quotient sheaf. -/
theorem pointsYonedaIso_hom_comp_actionProjection :
    (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫
        actionProjection G B hS V a =
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion)
        (actionRelation (underlyingOver B hS V) G a) :=
  Iso.hom_inv_id_assoc _ _

include hR in
/-- **The morphism `V/G ⟶ X` induced by an invariant morphism `h_V ⟶ X` to a sheaf.** This is
descent out of the quotient sheaf of the graph relation of the action, whose coequalizing
hypothesis invariance supplies. -/
def actionQuotientDesc {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f) :
    actionQuotient G B hS V a ⟶ X :=
  (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (actionRelation (underlyingOver B hS V) G a)
    ⟨X, hX⟩ ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f)
    (sourceMap_actionRelation_comp_pointsYonedaIso_hom_comp
      G B S hS V hR a hX f hf)).hom

include hR in
/-- The descended morphism restricts to the given one along the canonical projection of the
restricted functor of points onto the quotient sheaf. -/
theorem toQuotientSheaf_comp_actionQuotientDesc
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f) :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (actionRelation (underlyingOver B hS V) G a) ≫
        actionQuotientDesc G B S hS V hR a hX f hf =
      (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f :=
  Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (actionRelation (underlyingOver B hS V) G a) ⟨X, hX⟩
    ((pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f)
    (sourceMap_actionRelation_comp_pointsYonedaIso_hom_comp G B S hS V hR a hX f hf)

include hR in
/-- **The morphism induced on the quotient restricts to the given one along the projection.**
-/
theorem actionProjection_comp_actionQuotientDesc
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f) :
    actionProjection G B hS V a ≫ actionQuotientDesc G B S hS V hR a hX f hf = f := by
  refine (cancel_epi
    (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom).1 ?_
  rw [← Category.assoc, pointsYonedaIso_hom_comp_actionProjection G B S hS V a,
    toQuotientSheaf_comp_actionQuotientDesc G B S hS V hR a hX f hf]

include hR in
/-- **Descent along the projection onto the quotient is unique.** -/
theorem actionQuotientDesc_unique
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : yoneda.obj V ⟶ X)
    (hf : ∀ g : G, yoneda.map (siteActionHom G B hS V a g) ≫ f = f)
    (d : actionQuotient G B hS V a ⟶ X)
    (hd : actionProjection G B hS V a ≫ d = f) :
    d = actionQuotientDesc G B S hS V hR a hX f hf := by
  have hpd : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (actionRelation (underlyingOver B hS V) G a) ≫ d =
      (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) V).hom ≫ f := by
    rw [← pointsYonedaIso_hom_comp_actionProjection G B S hS V a, Category.assoc, hd]
  exact congrArg (fun z : Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (actionRelation (underlyingOver B hS V) G a) ⟶ ⟨X, hX⟩ ↦ z.hom)
    (Stacks.Groupoids.quotientSheafDesc_unique (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) (actionRelation (underlyingOver B hS V) G a)
      ⟨X, hX⟩ _
      (sourceMap_actionRelation_comp_pointsYonedaIso_hom_comp G B S hS V hR a hX f hf)
      ⟨d⟩ hpd)

end AlgebraicGeometry.Space

end
