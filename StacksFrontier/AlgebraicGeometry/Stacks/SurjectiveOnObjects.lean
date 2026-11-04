module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Morphisms surjective on objects (Stacks 06D4, 06D5, 06D6)

Let `S` be a scheme contained in a big fppf site `B`. A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories
fibred in groupoids over the big fppf site of `S` is *surjective on objects* when every object
of `𝒴` over the spectrum of a field `k` is, after passing to a field extension `K/k`, the image
of an object of `𝒳`. Stacks 06D5 is that this is preserved by base change: the second
projection of the 2-fibre product `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` is surjective on objects as soon as `p` is,
and Stacks 06D6 is that it is preserved by composition.

## Main definitions

* `AlgebraicGeometry.Stack.IsFieldObject`: an object of the site whose underlying scheme is the
  spectrum of a field.
* `AlgebraicGeometry.Stack.IsSurjectiveOnObjects`: **Stacks 06D4**, surjectivity on objects.

## Main results

* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_twoFibreProductSnd`: **Stacks 06D5**.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_comp`: **Stacks 06D6**.

## Implementation notes

The source asks for an isomorphism `p(x) ≅ y|_{Spec K}` with the restriction of `y` along the
field extension. This is expressed instead as a morphism `α : p(x) ⟶ y` lying over the morphism
`Spec K ⟶ Spec k` of the site; in a category fibred in groupoids every such morphism is strongly
cartesian, so the two formulations agree, and the restriction of `y` — a choice — does not have
to be recorded. Field objects are recognised up to isomorphism of the underlying scheme, since
the site's objects are schemes over `S` and not spectra on the nose.

Surjectivity on objects is stated for bare functors to the site rather than for a 1-morphism of
`CategoryTheory.CatFiberedInGroupoids`, because the two categories and their projections are all
that the condition mentions; the universes of the two total categories are therefore free of
each other and of the site.

The 2-fibre product is the canonical one of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, whose apex is the 2-fibre product
over the site of Stacks 0040, and the base change of `p` by `q` is that square's second
projection. The proof is the one of the source: pull `z` back along the field extension produced
by surjectivity of `p` over the image of `z`, and use that both the pullback map and the
morphism `α` are strongly cartesian over the same morphism of the site to identify their sources
by `CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso`. That isomorphism is vertical,
so the quadruple it forms is an object of the 2-fibre product, and the pullback map is the
required lift. Stacks 06D6 is formal: the two field extensions compose, and the lift is the
image of the first one's under the second 1-morphism followed by the second one's, which lies
over the composite because the second 1-morphism is strictly over the site.

## References

* [Stacks Project, Tag 06D5](https://stacks.math.columbia.edu/tag/06D5)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u uX uY uZ vX vY vZ v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the big fppf site over `S` whose underlying scheme is the spectrum of a
field. -/
def IsFieldObject (U : BigFppfOver B S hS) : Prop :=
  ∃ (k : Type u) (hk : Field k),
    letI : Field k := hk
    Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k))

/-- **Stacks 06D4.** A 1-morphism of categories over the big fppf site of `S` is *surjective on
objects* when every object over the spectrum of a field acquires a lift after passing to a field
extension. -/
def IsSurjectiveOnObjects
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) (F : X ⥤ Y) : Prop :=
  ∀ (U : BigFppfOver B S hS), IsFieldObject B S hS U →
    ∀ (y : Y), pY.obj y = U →
      ∃ (V : BigFppfOver B S hS),
        IsFieldObject B S hS V ∧
          ∃ (f : V ⟶ U) (x : X), pX.obj x = V ∧
            ∃ α : F.obj x ⟶ y, pY.IsHomLift f α

/-- **Stacks 06D5.** Surjectivity on objects is preserved by base change: if `p : 𝒳 ⟶ 𝒴` is
surjective on objects then so is the second projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of its base change along
any `q : 𝒵 ⟶ 𝒴`. -/
@[stacks 06D5]
theorem isSurjectiveOnObjects_twoFibreProductSnd
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    (h : IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)) :
    IsSurjectiveOnObjects B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare p q).pt.val.p 𝒵.val.p
      (CatFiberedInGroupoids.homFunctor
        (CatFiberedInGroupoids.twoFibreProductSquare p q).snd) := by
  intro U hU z hz
  have hzq : 𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor q).obj z) = U :=
    (BasedFunctor.w_obj q.hom z).trans hz
  obtain ⟨V, hV, f, x, hx, α, hα⟩ :=
    h U hU ((CatFiberedInGroupoids.homFunctor q).obj z) hzq
  let : 𝒵.val.p.IsFiberedInGroupoids := 𝒵.isFiberedInGroupoids
  let : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let z' : 𝒵.val.obj := Functor.IsPreFibered.pullbackObj hz f
  let b : z' ⟶ z := Functor.IsPreFibered.pullbackMap hz f
  let : 𝒴.val.p.IsHomLift f ((CatFiberedInGroupoids.homFunctor q).map b) :=
    BasedFunctor.preserves_isHomLift q.hom f b
  let : 𝒴.val.p.IsStronglyCartesian f ((CatFiberedInGroupoids.homFunctor q).map b) :=
    CatFiberedInGroupoids.isStronglyCartesian_map q f b
  let : 𝒴.val.p.IsHomLift f α := hα
  let : 𝒴.val.p.IsStronglyCartesian f α :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift f α
  have hbase : f = (Iso.refl V).hom ≫ f := by simp
  have hevertical : 𝒴.val.p.IsHomLift (𝟙 V)
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒴.val.p hbase
        ((CatFiberedInGroupoids.homFunctor q).map b) α).hom := by
    show 𝒴.val.p.IsHomLift (Iso.refl V).hom _
    infer_instance
  let W : TwoFibreProductOver 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q) :=
    { base := V, x := x, y := z', hx := hx
      hy := Functor.IsPreFibered.pullbackObj_proj hz f
      iso := Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒴.val.p hbase
        ((CatFiberedInGroupoids.homFunctor q).map b) α
      vertical := hevertical }
  refine ⟨V, hV, f, W, rfl, b, ?_⟩
  show 𝒵.val.p.IsHomLift f b
  infer_instance

/-- **Stacks 06D6.** A composite of two 1-morphisms surjective on objects is surjective on
objects: compose the two field extensions. -/
@[stacks 06D6]
theorem isSurjectiveOnObjects_comp
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {Z : Type uZ} [Category.{vZ} Z]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS) (F : X ⥤ Y) (G : Y ⥤ Z) (hG : G ⋙ pZ = pY)
    (hFsurj : IsSurjectiveOnObjects B S hS pX pY F)
    (hGsurj : IsSurjectiveOnObjects B S hS pY pZ G) :
    IsSurjectiveOnObjects B S hS pX pZ (F ⋙ G) := by
  intro U hU z hz
  obtain ⟨W, hW, g, y, hy, β, hβ⟩ := hGsurj U hU z hz
  obtain ⟨V, hV, f, x, hx, α, hα⟩ := hFsurj W hW y hy
  let : pY.IsHomLift f α := hα
  let : pZ.IsHomLift f (G.map α) := Functor.isHomLift_map_of_comp_eq hG f α
  let : pZ.IsHomLift g β := hβ
  exact ⟨V, hV, f ≫ g, x, hx, G.map α ≫ β, inferInstance⟩

end AlgebraicGeometry.Stack

end
