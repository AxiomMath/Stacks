module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.MonoToZeroDimensionalLocalSpectra
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence

/-!
# A monomorphism into an algebraic stack covered by the spectrum of a field (Stacks 06MQ)

**Stacks 06MQ.** Let `f : 𝒵' ⟶ 𝒵` be a monomorphism of algebraic stacks over `S` and assume that
`𝒵` admits a 1-morphism from the algebraic stack of the spectrum of a field which is locally of
finite presentation, surjective and flat. Then either `𝒵'` has no points, or `f` is an
equivalence.

The proof is the source's. Assume `|𝒵'|` is nonempty and write `Spec k ⟶ 𝒵` for the given cover,
with `T` the object of the big fppf site of `S` presenting `Spec k`. Surjectivity of the cover and
**Stacks 04XH** put a point on the 2-fibre product `𝒵' ×_𝒵 Spec k`. That 2-fibre product is
representable by an algebraic space, because `f` is representable by algebraic spaces, and the
structural morphism of a representing space is a monomorphism of algebraic spaces over `S`, because
`f` is a monomorphism; its target is the representable algebraic space of `T`, whose underlying
scheme is the spectrum of a field. So **Stacks 06MG** leaves two possibilities, and the point just
produced excludes the one where the representing space has no points: the structural morphism is an
isomorphism.

An isomorphism has a section over every object of the slice site at `T`, and a section of the
representing space is the same thing as an object of the 2-fibre product; so for every object `a`
of that slice site the image of `a` under the cover is isomorphic, vertically over the base, to the
image under `f` of an object of `𝒵'`. This is the source's "`Spec k ⟶ 𝒵` factors through `𝒵'`",
stated for every base change of the tautological object rather than only for the object itself.

Full faithfulness of `f` is **Stacks 05UK** (the implication (1) ⟹ (2) of **Stacks 04ZZ**). For
essential surjectivity, **Stacks 07AN** covers any object `x` of any fibre of `𝒵` by a covering
sieve along each member `k : V ⟶ U` of which `x` is reached by a morphism out of the image of an
object of the slice site at `T`; composing with the factorisation above replaces that image by the
image under `f` of an object of `𝒵'` over `V`, and a morphism to `x` over `k` out of an object over
`V` is strongly cartesian in a category fibred in groupoids, so that object is *the* base change of
`x` along `k`. That is exactly local essential surjectivity on fibres, and **Stacks 046N** turns
it, for a fully faithful 1-morphism of stacks, into an equivalence over the site.

## Main results

* `AlgebraicGeometry.Stack.isEmpty_points_or_isEquivalenceOver_of_isMonomorphism`:
  **Stacks 06MQ**, and
  `AlgebraicGeometry.Stack.isEquivalenceOver_of_isMonomorphism_of_fieldSpectrumCover`, its
  nonempty case with the cover spelled out.
* `AlgebraicGeometry.Stack.exists_vertical_iso_of_section_baseChange`: a section of an algebraic
  space representing a base change of `f` names an object of `𝒵'` whose image is vertically
  isomorphic to the given object of `𝒵`, and
  `AlgebraicGeometry.Stack.nonempty_points_of_sliceTwoFibreProductObject` goes back the other way,
  from an object of the base change over a field object to a point of the representing space.
* `AlgebraicGeometry.Stack.exists_sliceTwoFibreProductObject`: the comparison between the 2-fibre
  product of `f` with the stack of `T` and the 2-fibre product of `f` with the slice site at `T`,
  on objects.
* `AlgebraicGeometry.Stack.nonempty_section_of_isIso_algebraicSpaceMap`: an isomorphism of
  algebraic spaces over `S` out of the relocalisation of a space over `T` has a section over every
  object of the slice site at `T`.
* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_of_forall_vertical_iso`: the local essential
  surjectivity on fibres that **Stacks 046N** consumes, from the factorisation of the cover
  through `𝒵'`.

## Implementation notes

The conclusion is the strong one: `CategoryTheory.Functor.IsEquivalenceOver`, an equivalence in
the 2-category of fibred categories over the site — a quasi-inverse which is again strictly a
1-morphism over the site, with vertical unit and counit. This is what **Stacks 046N**
(`CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`) produces, and it is
strictly stronger than the underlying functor being an equivalence of categories. It is data,
hence the `Nonempty`.

Emptiness of `𝒵'` is `IsEmpty (AlgebraicGeometry.Stack.AlgebraicStacks.points B S hS 𝒵')`, the
point set of **Stacks 04XG**; this is how emptiness of an algebraic stack is spelled elsewhere in
the library, for instance in `StacksFrontier.AlgebraicGeometry.Stacks.Dimension`.

The hypothesis on `𝒵` is condition (2) of **Stacks 06MP**, i.e.
`AlgebraicGeometry.Stack.HasLocallyOfFinitePresentationFlatFieldSpectrumCover`, rather than a
field, a site object and an isomorphism spelled out: that abbreviation already packages exactly
the data the source asks for, and the source reaches Stacks 06MQ from Stacks 06MP.

Two different 2-fibre products of `f` appear and have to be compared. **Stacks 04XH** is available
for the 2-fibre product of the cospan `(f, Spec k ⟶ 𝒵)` in the 2-category of algebraic stacks,
whose objects are based over the big fppf site of `S`; the monomorphism condition of
**Stacks 04ZW** instead quantifies over 2-fibre products of `f` with a 1-morphism *out of the slice
site at an object*, whose objects are based over that slice site. The two are related by
`CategoryTheory.Over.iteratedSliceEquiv`, and
`AlgebraicGeometry.Stack.exists_sliceTwoFibreProductObject` carries an object across. Only the
direction from the algebraic-stack 2-fibre product to the slice one is needed, and only on
objects, so no equivalence of categories is built.

Both `CategoryTheory.Functor.IsStack` hypotheses of Stacks 046N come from
`AlgebraicGeometry.Stack.isStack_of_isAlgebraicStack`, and the monomorphism hypothesis of
Stacks 05UK is the second conjunct of **Stacks 04ZW** after
`AlgebraicGeometry.Space.mono_hom_iff_mono` (**Stacks 042M**) has turned a monomorphism of the
category of algebraic spaces over `S` into a monomorphism of the underlying presheaves.

## References

* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The unit of the iterated-slice equivalence is vertical.** For an object `V` of a slice
`(𝒞/T)` the comparison of `V` with its round trip through `𝒞/T.left` lies over the identity of the
underlying object of `V`: the round trip replaces the structure morphism of `V.left` by the
composite that `CategoryTheory.Over.w` says it is. -/
private theorem isHomLift_iteratedSliceUnitIso_inv {C : Type u} [Category.{w} C] {X : C}
    (T : Over X) (V : Over T) :
    (Over.forget T).IsHomLift (𝟙 V.left)
      (((Over.iteratedSliceEquiv T).unitIso.app V).symm.hom) := by
  cases V with
  | mk W _ a =>
    have hdom : (Over.forget T).obj
        (((Over.iteratedSliceEquiv T).functor ⋙
          (Over.iteratedSliceEquiv T).inverse).obj (Over.mk a)) = W := by
      change Over.mk (a.left ≫ T.hom) = W
      exact congrArg Over.mk (Over.w a)
    refine IsHomLift.of_fac' (Over.forget T) (𝟙 W) _ hdom rfl ?_
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.id_comp]
    rw [Over.eqToHom_left]
    simp only [Over.forget, Over.iteratedSliceEquiv, Over.iteratedSliceForward,
      Over.iteratedSliceBackward, Over.mk_left, Functor.id_obj, Functor.comp_obj, Over.mk_hom,
      Comma.fst_obj, Iso.symm_hom, Iso.app_inv, eqToHom_refl, Over.id_left, Category.comp_id]
    rfl

/-- **The image of the iterated-slice unit under a 1-morphism `p` lies over an identity.** -/
private theorem isHomLift_homFunctor_iteratedSliceUnitIso_hom
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (T : BigFppfOver B S hS)
    (p : schemeStack.{u, w} B S hS T ⟶ 𝒵) (V : Over T) :
    𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj V))
      (((CatFiberedInGroupoids.homFunctor p.hom).mapIso
        ((Over.iteratedSliceEquiv T).unitIso.app V)).hom) := by
  have : (schemeStack.{u, w} B S hS T).val.val.p.IsHomLift (𝟙 ((Over.forget T).obj V))
      (((Over.iteratedSliceEquiv T).unitIso.app V).hom) := by
    have : (Over.forget T).IsHomLift (𝟙 ((Over.forget T).obj V))
        (((Over.iteratedSliceEquiv T).unitIso.app V).symm.hom) :=
      isHomLift_iteratedSliceUnitIso_inv T V
    exact IsHomLift.lift_id_inv (Over.forget T) _ ((Over.iteratedSliceEquiv T).unitIso.app V).symm
  exact p.hom.hom.preserves_isHomLift _ _

/-- **A section of an algebraic space representing a base change of `f` names an object of the
source.** Let `f : 𝒵' ⟶ 𝒵` be a 1-morphism of algebraic stacks over `S`, let `T` be an object of
the big fppf site of `S` and let `y` be a 1-morphism from the slice site at `T` into `𝒵`. If the
presheaf `G` on that slice site represents the 2-fibre product `(Sch/T) ×_𝒵 𝒵'`, then a section of
`G` over an object `a` of the slice site gives an object of `𝒵'` whose image under `f` is
isomorphic to `y a` by an isomorphism vertical over the base of `a`.

This is one half of the 2-Yoneda dictionary between sections of the representing space and objects
of the 2-fibre product; the object is the image of the canonical object attached to the section
under the backward 1-morphism of the representing equivalence. -/
theorem exists_vertical_iso_of_section_baseChange
    {𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵' ⟶ 𝒵) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒵.val.val.obj)
    (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒵'.val.val.p 𝒵.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : BigFppfOver B T.left.1 T.left.2) (s : G.obj (op a)) :
    ∃ (x : 𝒵'.val.val.obj) (i : y.obj a ≅ (CatFiberedInGroupoids.homFunctor f.hom).obj x),
      𝒵.val.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) i.hom := by
  let z : (presheafOfCategories (G ⋙ typeToCat)).obj := ⟨a, ⟨s⟩⟩
  let q := e.inv.functor.obj z
  have hqa : q.x = a := Functor.congr_obj e.inv.w z
  refine ⟨q.y, y.mapIso (eqToIso hqa.symm) ≪≫ q.iso, ?_⟩
  have hbase : q.base = (Over.map T.hom).obj a := by rw [← hqa]; exact q.hx.symm
  have : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) q.iso.hom :=
    hbase ▸ q.vertical
  change 𝒵.val.val.p.IsHomLift _ (y.map (eqToHom hqa.symm) ≫ q.iso.hom)
  rw [eqToHom_map]
  infer_instance

/-- **An object of a base change of `f` based over a field object gives a point of the representing
algebraic space.** In the situation of
`AlgebraicGeometry.Stack.exists_vertical_iso_of_section_baseChange`, an object of the 2-fibre
product `(Sch/T) ×_𝒵 𝒵'` whose base is a field object of the big fppf site of `S` names a section
of the representing presheaf there, and a section over a field object is a field-valued point of
**Stacks 03BU** of the algebraic space over `S` obtained by relocalising. -/
theorem nonempty_points_of_sliceTwoFibreProductObject
    {𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵' ⟶ 𝒵) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒵.val.val.obj)
    (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B T.left.1 T.left.2 G)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒵'.val.val.p 𝒵.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (A : TwoFibreProductOver (Over.map T.hom) 𝒵'.val.val.p 𝒵.val.val.p y
      (CatFiberedInGroupoids.homFunctor f.hom))
    (hfield : IsFieldObject B S hS A.base) :
    Nonempty (Space.points B S hS
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨G, hG⟩).1.left) := by
  have hfieldW : IsFieldObject B S hS ((Over.map T.hom).obj A.x) := A.hx ▸ hfield
  obtain ⟨q, -, -⟩ := exists_fieldValuedPoint_of_isFieldObject B S hS _ _ hfieldW
    (((spacesOverSmallerBaseFunctorForgetIso B T.left.1 S T.left.2 hS T.hom).inv.app
      ⟨G, hG⟩).app _ ⟨⟨A.x.hom, PresheafOfCategories.sectionOfObj e A rfl⟩, rfl⟩)
  exact ⟨q.class B S hS _⟩

/-- **An object of the 2-fibre product of `f` with the stack of `T` gives one of the 2-fibre
product of `f` with the slice site at `T`.** The two 2-fibre products differ by
`CategoryTheory.Over.iteratedSliceEquiv`: the first is based over the big fppf site of `S` and its
`T`-component is an object of `Sch/T`, the second is based over the slice site at `T` and its
`T`-component is an object of `Sch/T.left`. The comparison isomorphism of the two images in `𝒵` is
the unit of that equivalence, which is vertical by
`AlgebraicGeometry.Stack.isHomLift_iteratedSliceUnitIso_inv`.

The base is unchanged, which is what the consumer needs: it is where the field-object hypothesis of
`AlgebraicGeometry.Stack.nonempty_points_of_sliceTwoFibreProductObject` lives. -/
theorem exists_sliceTwoFibreProductObject
    {𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵' ⟶ 𝒵) (T : BigFppfOver B S hS)
    (p : schemeStack.{u, w} B S hS T ⟶ 𝒵)
    (q : TwoFibreProductOver 𝒵'.val.val.p (schemeStack.{u, w} B S hS T).val.val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor p.hom)) :
    ∃ A : TwoFibreProductOver (Over.map T.hom) 𝒵'.val.val.p 𝒵.val.val.p
      (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom)
      (CatFiberedInGroupoids.homFunctor f.hom),
      A.base = q.base := by
  have hbase : (Over.forget T).obj q.y = q.base := q.hy
  have hfirst : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj q.y))
      (((CatFiberedInGroupoids.homFunctor p.hom).mapIso
        ((Over.iteratedSliceEquiv T).unitIso.app q.y).symm).hom) := by
    have := isHomLift_homFunctor_iteratedSliceUnitIso_hom B S hS T p q.y
    exact IsHomLift.lift_id_inv 𝒵.val.val.p _ ((CatFiberedInGroupoids.homFunctor p.hom).mapIso
      ((Over.iteratedSliceEquiv T).unitIso.app q.y))
  have hsecond : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj q.y)) q.iso.inv := by
    have : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj q.y)) q.iso.hom := by
      rw [hbase]
      exact q.vertical
    exact IsHomLift.lift_id_inv 𝒵.val.val.p _ q.iso
  refine ⟨{ base := (Over.forget T).obj q.y
            x := (Over.iteratedSliceEquiv T).functor.obj q.y
            y := q.x
            hx := congrArg Over.mk (Over.w q.y.hom)
            hy := q.hx.trans hbase.symm
            iso := (CatFiberedInGroupoids.homFunctor p.hom).mapIso
              ((Over.iteratedSliceEquiv T).unitIso.app q.y).symm ≪≫ q.iso.symm
            vertical := ?_ }, hbase⟩
  exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒵.val.val.p ((Over.forget T).obj q.y) _ _ _ _ _
    hfirst hsecond

/-- **An isomorphic structural morphism has a section over every object of the slice site.** Let
`G` be an algebraic space over `T` and suppose the structural morphism to the representable
algebraic space of `T` of the relocalisation of `G` to `S` is an isomorphism. Then `G` has a
section over every object of the slice site at `T`: the inverse isomorphism applied to the
canonical factorisation of that object is a section of the relocalisation, and
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_left` reads off that its factorisation
component is the structure morphism of the object itself. -/
theorem nonempty_section_of_isIso_algebraicSpaceMap (T : BigFppfOver B S hS)
    (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B T.left.1 T.left.2 G)
    (hiso : IsIso (algebraicSpaceMap B S hS T
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨G, hG⟩)).hom)
    (a : BigFppfOver B T.left.1 T.left.2) : Nonempty (G.obj (op a)) := by
  have := hiso
  let A : AlgebraicSpaces B T.left.1 T.left.2 := ⟨G, hG⟩
  let Fy := (spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj A
  let W : BigFppfOver B S hS := (Over.map T.hom).obj a
  let v : (yoneda.obj (Over.mk T.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u).obj (op W) :=
    Over.homMk a.hom rfl
  let s : Fy.1.left.obj (op W) := (inv (algebraicSpaceMap B S hS T Fy).hom).app (op W) v
  have hs : Fy.1.hom.app (op W) s = v :=
    congrFun (congrArg (fun k => k.app (op W))
      (IsIso.inv_hom_id (algebraicSpaceMap B S hS T Fy).hom)) v
  let t := ((spacesOverSmallerBaseFunctorForgetIso B T.left.1 S T.left.2 hS T.hom).hom.app A).app
    (op W) s
  have ht : t.1.1 = a.hom := by
    rw [← spacesOverSmallerBaseFunctor_hom_app_left B T.left.1 S T.left.2 hS T.hom A (op W) s, hs]
    rfl
  have ht2 := t.1.2
  rw [ht] at ht2
  exact ⟨ht2⟩

/-- **Local essential surjectivity on fibres from a factorisation of the cover.** Let
`f : 𝒵' ⟶ 𝒵` be a 1-morphism of algebraic stacks over `S` and let `p : Sch/T ⟶ 𝒵` be flat, locally
of finite presentation and surjective. If every base change of the tautological object of `Sch/T`
has image under `p` vertically isomorphic to the image under `f` of an object of `𝒵'`, then `f` is
locally essentially surjective on fibres for the big fppf topology.

**Stacks 07AN** supplies, for an object `x` of the fibre of `𝒵` over `U`, a covering sieve of `U`
along each member `k : V ⟶ U` of which there is an object `x₀` of `Sch/T` and a morphism
`p x₀ ⟶ x` over `k`. The hypothesis replaces `p x₀` by `f x'` for an object `x'` of `𝒵'`, and the
resulting morphism `f x' ⟶ x` over `k` is strongly cartesian because `𝒵` is fibred in groupoids,
hence identifies `f x'` with the chosen base change of `x` along `k` inside the fibre over `V`. -/
theorem locallyEssSurjOnFibers_of_forall_vertical_iso
    {𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵' ⟶ 𝒵) (T : BigFppfOver B S hS)
    (p : schemeStack.{u, w} B S hS T ⟶ 𝒵)
    (hlift : ∀ a : BigFppfOver B T.left.1 T.left.2,
      ∃ (x : 𝒵'.val.val.obj)
        (i : (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom).obj a ≅
          (CatFiberedInGroupoids.homFunctor f.hom).obj x),
        𝒵.val.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) i.hom)
    (hflat : AlgebraicStacks.IsFlat B S hS p)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS p)
    (hsurj : IsSurjective B S hS p) :
    Functor.LocallyEssSurjOnFibers 𝒵.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (BigFppfOver.topology B S hS) := by
  have hfib : 𝒵.val.val.p.IsFibered := 𝒵.val.isFiberedInGroupoids.isFibered
  have hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒵)) =
      ⋃ _ : Unit, Set.range (AlgebraicStacks.pointsMap B S hS p) := by
    rw [Set.iUnion_const, hsurj.range_eq]
  intro U x
  obtain ⟨R, hR, hRlift⟩ := exists_fppfCovering_fibre_lift_of_family B S hS
    (𝒳 := fun _ : Unit => schemeStack.{u, w} B S hS T) (𝒴 := 𝒵)
    (fun _ => p) (fun _ => hflat) (fun _ => hlfp) hjs U x
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨-, x₀, α, hα⟩ := hRlift hk
  have hαl : 𝒵.val.val.p.IsHomLift k α := hα
  obtain ⟨x', i, hi⟩ := hlift ((Over.iteratedSliceEquiv T).functor.obj x₀)
  have hax : (Over.map T.hom).obj ((Over.iteratedSliceEquiv T).functor.obj x₀) =
      (Over.forget T).obj x₀ := congrArg Over.mk (Over.w x₀.hom)
  have hi' : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj x₀)) i.hom := by
    rw [← hax]; exact hi
  let j : (CatFiberedInGroupoids.homFunctor p.hom).obj x₀ ≅
      (CatFiberedInGroupoids.homFunctor f.hom).obj x' :=
    (CatFiberedInGroupoids.homFunctor p.hom).mapIso
      ((Over.iteratedSliceEquiv T).unitIso.app x₀) ≪≫ i
  have hj : 𝒵.val.val.p.IsHomLift (𝟙 ((Over.forget T).obj x₀)) j.hom :=
    @IsHomLift.comp_of_lift_id _ _ _ _ 𝒵.val.val.p ((Over.forget T).obj x₀) _ _ _ _ _
      (isHomLift_homFunctor_iteratedSliceUnitIso_hom B S hS T p x₀) hi'
  have hx₀V : (Over.forget T).obj x₀ = V :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p p.hom) x₀).symm.trans
      (IsHomLift.domain_eq 𝒵.val.val.p k α)
  have hjV : 𝒵.val.val.p.IsHomLift (𝟙 V) j.hom := by rw [← hx₀V]; exact hj
  have hjinv : 𝒵.val.val.p.IsHomLift (𝟙 V) j.inv := by
    have := hjV
    exact IsHomLift.lift_id_inv 𝒵.val.val.p V j
  have hβ : 𝒵.val.val.p.IsHomLift k (j.inv ≫ α) := by
    have := hjinv
    have := hαl
    exact IsHomLift.comp_lift_id_left 𝒵.val.val.p k α j.inv
  have hx' : 𝒵'.val.val.p.obj x' = V :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f.hom) x').symm.trans
      (IsHomLift.domain_eq 𝒵.val.val.p k (j.inv ≫ α))
  have := hβ
  have : 𝒵.val.val.p.IsStronglyCartesian k (j.inv ≫ α) :=
    𝒵.val.isFiberedInGroupoids.isStronglyCartesian_homLift k (j.inv ≫ α)
  have hcart : 𝒵.val.val.p.IsCartesian k (j.inv ≫ α) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian 𝒵.val.val.p k _
  exact ⟨Functor.Fiber.mk hx', ⟨Functor.fiberIsoOfCartesian k (j.inv ≫ α)
    (Functor.IsPreFibered.pullbackMap x.2 k) hcart
    (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 k)⟩⟩

/-- **The content of Stacks 06MQ: a nonempty monomorphism into a stack covered by the spectrum of
a field is an equivalence.** This is
`AlgebraicGeometry.Stack.isEmpty_points_or_isEquivalenceOver_of_isMonomorphism` with the cover
spelled out and the nonempty alternative already chosen.

**Stacks 04XH** puts a point on the 2-fibre product of `f` with the cover; the cover's source is
the spectrum of a field, so **Stacks 06MG** makes the structural morphism of an algebraic space
representing that 2-fibre product an isomorphism rather than a morphism out of a space with no
points. Its sections then factor the cover through `𝒵'` after every base change, `f` is fully
faithful by **Stacks 05UK**, and **Stacks 07AN** together with the factorisation gives local
essential surjectivity on fibres, which **Stacks 046N** upgrades to an equivalence. -/
theorem isEquivalenceOver_of_isMonomorphism_of_fieldSpectrumCover
    {𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵' ⟶ 𝒵)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f)
    (T : BigFppfOver B S hS) (kf : Type u) [Field kf]
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of kf))
    (p : schemeStack.{u, w} B S hS T ⟶ 𝒵)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS p)
    (hsurj : IsSurjective B S hS p) (hflat : AlgebraicStacks.IsFlat B S hS p)
    (hne' : Nonempty (AlgebraicStacks.points B S hS 𝒵')) :
    Nonempty (Functor.IsEquivalenceOver 𝒵'.val.val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)) := by
  classical
  obtain ⟨z'⟩ := hne'
  -- The 1-morphism `p` read on the slice site at `T`, and an algebraic space representing the
  -- 2-fibre product of `f` with it.
  have hy : (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom) ⋙
      𝒵.val.val.p = Over.map T.hom :=
    calc (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom) ⋙ 𝒵.val.val.p
        = T.iteratedSliceBackward ⋙
            (CatFiberedInGroupoids.homFunctor p.hom ⋙ 𝒵.val.val.p) := Functor.assoc _ _ _
      _ = T.iteratedSliceBackward ⋙ (schemeStack.{u, w} B S hS T).val.val.p :=
          congrArg (T.iteratedSliceBackward ⋙ ·)
            (CatFiberedInGroupoids.homFunctor_comp_p p.hom)
      _ = Over.map T.hom := Over.iteratedSliceBackward_forget T
  obtain ⟨G, hG, ⟨e⟩⟩ := hf.1 T (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom)
    hy
  let Fy := (spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨G, hG⟩
  have : Mono (algebraicSpaceMap B S hS T Fy).hom :=
    (Space.mono_hom_iff_mono B S hS _).2 (hf.2 T _ hy G hG ⟨e⟩)
  -- The 2-fibre product is nonempty, by Stacks 04XH.
  obtain ⟨t, ht⟩ := hsurj (AlgebraicStacks.pointsMap B S hS f z')
  obtain ⟨r, -, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f p)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f p) z' t ht.symm
  obtain ⟨qpt, -⟩ := Quotient.exists_rep r
  have hover : qpt.obj.base = qpt.base := qpt.over
  have hfieldbase : IsFieldObject B S hS qpt.obj.base :=
    ⟨qpt.carrier, qpt.field,
      ⟨eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hover) ≪≫ qpt.isSpec⟩⟩
  obtain ⟨A, hA⟩ := exists_sliceTwoFibreProductObject B S hS f T p qpt.obj
  have hne : Nonempty (Space.points B S hS Fy.1.left) :=
    nonempty_points_of_sliceTwoFibreProductObject B S hS f T _ G hG e A (hA ▸ hfieldbase)
  -- Stacks 06MG: the structural morphism is an isomorphism.
  have hiso : IsIso (algebraicSpaceMap B S hS T Fy).hom :=
    (Space.isEmpty_points_or_isIso_of_mono_to_spec_field B S hS Fy.property
      (algebraicSpaceMap B S hS T Fy).hom (Over.mk T.hom) (Iso.refl _) kf eT).resolve_left
      fun h => absurd hne (not_nonempty_iff.2 h)
  -- The cover factors through `𝒵'` after every base change.
  have hlift : ∀ a : BigFppfOver B T.left.1 T.left.2,
      ∃ (x : 𝒵'.val.val.obj)
        (i : (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor p.hom).obj a ≅
          (CatFiberedInGroupoids.homFunctor f.hom).obj x),
        𝒵.val.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) i.hom := fun a =>
    (nonempty_section_of_isIso_algebraicSpaceMap B S hS T G hG hiso a).elim
      (exists_vertical_iso_of_section_baseChange B S hS f T _ G e a)
  -- Full faithfulness is Stacks 05UK, and Stacks 046N concludes.
  obtain ⟨_, _⟩ := full_and_faithful_homFunctor_of_mono_representingMaps B S hS f.hom
    hf.1 fun U z hz H hH he => (Space.mono_hom_iff_mono B S hS _).2 (hf.2 U z hz H hH he)
  exact (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers
    (isStack_of_isAlgebraicStack.{u, w} B S hS 𝒵'.property)
    (isStack_of_isAlgebraicStack.{u, w} B S hS 𝒵.property)
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids 𝒵.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom))).2
    (locallyEssSurjOnFibers_of_forall_vertical_iso B S hS f T p hlift hflat hlfp hsurj)

/-- **Stacks 06MQ.** Let `f : 𝒵' ⟶ 𝒵` be a monomorphism of algebraic stacks over `S` and assume
that `𝒵` admits a 1-morphism from the algebraic stack of the spectrum of a field which is locally
of finite presentation, surjective and flat (condition (2) of **Stacks 06MP**). Then either `𝒵'`
has no points, or `f` is an equivalence over the big fppf site of `S`.

The nonempty case is
`AlgebraicGeometry.Stack.isEquivalenceOver_of_isMonomorphism_of_fieldSpectrumCover`. -/
@[stacks 06MQ]
theorem isEmpty_points_or_isEquivalenceOver_of_isMonomorphism
    (𝒵' 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵' ⟶ 𝒵)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f)
    (hcov : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵) :
    IsEmpty (AlgebraicStacks.points B S hS 𝒵') ∨
      Nonempty (Functor.IsEquivalenceOver 𝒵'.val.val.p 𝒵.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)) := by
  rcases isEmpty_or_nonempty (AlgebraicStacks.points B S hS 𝒵') with hempty | hne'
  · exact Or.inl hempty
  obtain ⟨F, p, hlfp, hsurj, hflat⟩ := hcov
  exact Or.inr (isEquivalenceOver_of_isMonomorphism_of_fieldSpectrumCover.{u, w} B S hS f hf
    F.base F.carrier F.isSpec p hlfp hsurj hflat hne')

end AlgebraicGeometry.Stack

end
