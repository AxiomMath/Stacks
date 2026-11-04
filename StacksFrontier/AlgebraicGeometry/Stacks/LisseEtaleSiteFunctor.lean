module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition

/-!
# A smooth morphism of algebraic stacks restricts to the lisse-étale sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks over a scheme `S` in a big fppf site
`B`. An object of `𝒳` is *smooth* when the 1-morphism it names under the 2-Yoneda lemma, out of
the big fppf site of the scheme it lies over, is smooth; the smooth objects form the lisse-étale
site of **Stacks 0787**. Because smoothness of 1-morphisms is stable under composition
(**Stacks 075V**), `f` carries smooth objects of `𝒳` to smooth objects of `𝒴`, hence restricts to
a functor of the two lisse-étale sites, and that restriction is continuous and cocontinuous.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.siteFunctor`: the restriction of a smooth 1-morphism to the
  lisse-étale sites, together with the equality of composites that specifies it.

## Main results

* `AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_homFunctor_associatedTopology`: the
  underlying functor of a 1-morphism of algebraic stacks is continuous and cocontinuous for the
  topologies the two stacks inherit from any topology on the schemes of the big site.
* `AlgebraicGeometry.Stack.LisseEtale.smoothObject_map`: a smooth 1-morphism carries smooth
  objects to smooth objects.
* `AlgebraicGeometry.Stack.LisseEtale.siteFunctor_isContinuous` and
  `AlgebraicGeometry.Stack.LisseEtale.siteFunctor_isCocontinuous`: the restriction is continuous
  and cocontinuous — **Stacks 07AT** (1), first assertion.

## Implementation notes

The file is the lisse-étale twin of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfSiteFunctor.lean` and reuses that file's generic
machinery rather than repeating it: the invariance of the smooth-diagram criterion of
**Stacks 06FM** under a 2-isomorphism and under an identification of the source
(`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso` and
`...hasPropertyOnSomeSmoothDiagram_of_eqToHom_comp`), the 2-Yoneda comparison
`AlgebraicGeometry.Stack.objectMorphismComp_twoIso`, and the two descent lemmas
`CategoryTheory.Functor.isContinuous_of_comp_fullyFaithful` and
`...isCocontinuous_of_comp_fullyFaithful`, all of which are stated for an arbitrary morphism
property, an arbitrary 1-morphism, respectively an arbitrary fully faithful functor.

The object-level step is the only mathematical content. Smoothness of an object `x` of `𝒳` is
smoothness of the 1-morphism `x : U → 𝒳` for `U` the scheme `x` lies over, and **Stacks 075V**
gives smoothness of `U → 𝒳 → 𝒴`; that composite is the 1-morphism `f x : U → 𝒴` only after the
equality `p_𝒴 (f x) = U` supplied by `f` being strictly over the site, and only up to a
2-isomorphism.

Continuity and cocontinuity are then formal, over the *étale* site of each stack rather than the
fppf one: the restriction composed with the inclusion of the smooth objects of `𝒴` is the
inclusion of those of `𝒳` followed by the underlying functor of `f`, which is continuous and
cocontinuous for the inherited étale topologies by **Stacks 06NW**, and the inclusions are
continuous and cocontinuous by **Stacks 0788** (1). Both properties descend along the inclusion of
`𝒴`, which is fully faithful. Because the ambient topology here is the étale one and not the fppf
one, `AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_homFunctor_associatedTopology` is
stated for an arbitrary topology `τ` on the schemes of `B`; it subsumes the fppf form
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_and_isCocontinuous_homFunctor`, which is not
reusable as it stands.

The second assertion of **Stacks 07AT** (1), the two identifications `f'_*(g')⁻¹ = g⁻¹f_*` and
`g'_!(f')⁻¹ = f⁻¹g_!` of the induced morphisms of topoi, is not proved here; the tag records only
the site functor and its two continuity properties.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The underlying functor of a 1-morphism of algebraic stacks over `S` is continuous and
cocontinuous for the sites the two stacks inherit from a topology `τ` on the schemes of the big
site: it is a 1-morphism of fibred categories strictly over the big fppf category of `S`, so
**Stacks 06NW** applies to the topologies of **Stacks 06TP**. -/
theorem isContinuous_and_isCocontinuous_homFunctor_associatedTopology (f : 𝒳 ⟶ 𝒴)
    (τ : GrothendieckTopology B.Schemes) :
    f.hom.hom.toFunctor.IsContinuous
        (associatedTopology B S hS 𝒳.val.val.p τ)
        (associatedTopology B S hS 𝒴.val.val.p τ) ∧
      f.hom.hom.toFunctor.IsCocontinuous
        (associatedTopology B S hS 𝒳.val.val.p τ)
        (associatedTopology B S hS 𝒴.val.val.p τ) := by
  have _ : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have _ : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  exact (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w)
    |>.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))

namespace LisseEtale

/-- **A smooth 1-morphism carries smooth objects to smooth objects.** The 2-Yoneda 1-morphism of
`f x` is, up to a 2-isomorphism and the identification of its source, the composite of the one of
`x` with `f`; both are smooth, and smoothness of 1-morphisms is stable under composition by
**Stacks 075V**. -/
theorem smoothObject_map (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f)
    (x : LisseEtale.{u, w} B S hS 𝒳) :
    smoothObject.{u, w} B S hS 𝒴
      (f.hom.hom.toFunctor.obj ((inclusion.{u, w} B S hS 𝒳).obj x)) := by
  let y : 𝒳.val.val.obj := (inclusion.{u, w} B S hS 𝒳).obj x
  let gx : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y) ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl))
  have hcomp : AlgebraicStacks.IsSmooth B S hS (gx ≫ f) :=
    AlgebraicStacks.isSmooth_comp B S hS gx f x.property hf
  have hbase : 𝒴.val.val.p.obj (f.hom.hom.toFunctor.obj y) = 𝒳.val.val.p.obj y :=
    Functor.congr_obj f.hom.hom.w y
  have hj := hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
    (fun _ _ g => Space.IsSmooth B S hS g)
    (objectMorphismComp_twoIso B S hS f y) hcomp
  exact hasPropertyOnSomeSmoothDiagram_of_eqToHom_comp B S hS
    (fun _ _ g => Space.IsSmooth B S hS g)
    (congrArg (schemeFibredCategory B S hS) hbase.symm)
    (objectMorphism B S hS 𝒴.val
      (Functor.Fiber.mk (a := f.hom.hom.toFunctor.obj y) rfl)) hj

/-- **Stacks 07AT** (1), the site functor. A smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` restricts to a functor between the lisse-étale sites, specified by the property that its
composite with the inclusion of the smooth objects of `𝒴` is the inclusion of those of `𝒳`
followed by the underlying functor of `f`.

The restriction exists because `f` carries smooth objects to smooth objects
(`AlgebraicGeometry.Stack.LisseEtale.smoothObject_map`), and that equality of composites is what
says its action on objects and arrows is the action of `f`. -/
@[stacks 07AT "the functor of lisse-etale sites along a smooth 1-morphism"]
def siteFunctor (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    {F : LisseEtale.{u, w} B S hS 𝒳 ⥤ LisseEtale.{u, w} B S hS 𝒴 //
      F ⋙ inclusion.{u, w} B S hS 𝒴 =
        inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor} :=
  ⟨ObjectProperty.lift _ (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor)
      (smoothObject_map B S hS f hf),
    CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by simp [ObjectProperty.lift]⟩

/-- **Stacks 07AT** (1), continuity. The restriction of a smooth 1-morphism to the lisse-étale
sites is continuous: its composite with the inclusion of `𝒴` is, and continuity descends along
that inclusion, which is fully faithful and cocontinuous by **Stacks 0788** (1). -/
@[stacks 07AT "that functor is continuous, in the smooth case"]
theorem siteFunctor_isContinuous (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    (siteFunctor.{u, w} B S hS f hf).1.IsContinuous
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) := by
  have := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).1
  have := isContinuous_inclusion_topology'.{u, w} B S hS 𝒳
  have := isCocontinuous_inclusion_topology'.{u, w} B S hS 𝒴
  have : ((siteFunctor.{u, w} B S hS f hf).1 ⋙ inclusion.{u, w} B S hS 𝒴).IsContinuous
      (topology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) := by
    rw [(siteFunctor.{u, w} B S hS f hf).2]
    exact Functor.isContinuous_comp _ _ _
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) _
  exact Functor.isContinuous_of_comp_fullyFaithful _ (inclusion.{u, w} B S hS 𝒴) _ _
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))

/-- **Stacks 07AT** (1), cocontinuity. The same descent, with the roles of continuity and
cocontinuity of the inclusion exchanged. -/
@[stacks 07AT "that functor is cocontinuous, in the smooth case"]
theorem siteFunctor_isCocontinuous (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    (siteFunctor.{u, w} B S hS f hf).1.IsCocontinuous
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) := by
  have := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  have := isCocontinuous_inclusion_topology'.{u, w} B S hS 𝒳
  have := isContinuous_inclusion_topology'.{u, w} B S hS 𝒴
  have : ((siteFunctor.{u, w} B S hS f hf).1 ⋙ inclusion.{u, w} B S hS 𝒴).IsCocontinuous
      (topology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) := by
    rw [(siteFunctor.{u, w} B S hS f hf).2]
    exact isCocontinuous_comp _ _ _
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
  exact Functor.isCocontinuous_of_comp_fullyFaithful _ (inclusion.{u, w} B S hS 𝒴) _ _
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))

end LisseEtale

end AlgebraicGeometry.Stack

end
