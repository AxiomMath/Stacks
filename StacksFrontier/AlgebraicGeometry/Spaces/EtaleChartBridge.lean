module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal

/-!
# From represented base changes to étale charts

A property of morphisms of algebraic spaces over `S` can be expressed in two ways: by asking
that every represented base change of the morphism has a property `P` of scheme morphisms, as
`AlgebraicGeometry.Space.IsClosedImmersion` does, or by asking that `P` holds for the morphism
of schemes underlying every commuting square of étale charts, as
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` does. This file proves that the first form
implies the second, which is the implication of Stacks 03MJ carried as the hypothesis
`AlgebraicGeometry.Space.PresheafImpliesHoldsOnEveryEtaleChart`, and discharges that hypothesis
for the two properties the comparison of fibre products of Stacks 03KN needs.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.etale_of_comp_etale_chart` is the cancellation step: a morphism of
  the site which factors one étale chart of a presheaf through another is étale.
* `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp` is the
  implication of Stacks 03MJ, for a property of scheme morphisms which is preserved when an
  étale morphism is composed in front of it, and
  `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_le` is the same for a
  property which is stable under composition and holds for the étale morphisms.
* `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType` and
  `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite` discharge
  the hypothesis for being locally of finite type and for being locally of finite type and
  locally quasi-finite.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc'` and
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc'` are the two remaining assertions of
  part (1) of Stacks 03KN, now unconditional.

## Implementation notes

Let `φ : G ⟶ H` be a morphism of presheaves every represented base change of which has `P`, and
let `a : h_U ⟶ G` and `b : h_V ⟶ H` be étale charts sitting over `h : U ⟶ V`. Representability
of `φ` turns `b` into a represented base change: it gives an object `W` of the site, a morphism
`p : W ⟶ V` with `P` and a chart `c : h_W ⟶ G` fitting in a pullback square. The chart square
then factors `h` as `l ≫ p` for a unique `l : U ⟶ W`, by the universal property of that square,
and the whole content of the implication is that `l` is étale.

That is the cancellation step. It is available at the level of schemes as
`CategoryTheory.MorphismProperty.HasOfPostcompProperty`, which Mathlib has for étale morphisms,
but `l` is only given as a morphism between two étale charts of `G`, and étaleness of a chart is
a statement about all of its represented base changes rather than about a single scheme
morphism. The step that transports it is the pullback of `a` along `c`: étaleness of the chart
`a` makes its second projection étale, étaleness of the chart `c` makes its first projection
étale, and the factorisation of `a` through `c` provides a section of that first projection
whose composite with the second projection is `l`. Cancellation applies to the section, because
the first projection is étale and the composite is an identity, and `l` is then a composite of
two étale morphisms of schemes.

The hypothesis on `P` is exactly what the last composition needs: `P` must survive composition
with an étale morphism in front. Some such hypothesis is necessary, since for `P` the
isomorphisms the implication is false — an identity has all of its represented base changes
isomorphisms, while a non-surjective étale chart of its source is a chart square whose
underlying scheme morphism is not an isomorphism. Both properties Stacks 03KN needs satisfy it,
being stable under composition and holding for the étale morphisms; local quasi-finiteness of an
étale morphism is `AlgebraicGeometry.locallyQuasiFinite_of_etale`.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cancellation between two étale charts -/

/-- A morphism `l : U ⟶ W` of the site which factors an étale chart `a : h_U ⟶ G` of a presheaf
through an étale chart `c : h_W ⟶ G` of the same presheaf is étale. -/
theorem etale_of_comp_etale_chart {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U W : BigFppfOver B S hS} {a : yoneda.obj U ⟶ G} {c : yoneda.obj W ⟶ G} {l : U ⟶ W}
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hl : yoneda.map l ≫ c = a) :
    Etale ((BigFppfOver.toScheme B S hS).map l) := by
  have hi : yoneda.map (𝟙 U) ≫ a = yoneda.map l ≫ c := by simp [hl]
  have hsecond : Etale ((BigFppfOver.toScheme B S hS).map (ha.rep.snd c)) := ha.property_snd c
  have hfirst : Etale ((BigFppfOver.toScheme B S hS).map (ha.rep.fst' c)) :=
    hc.property a (yoneda.map (ha.rep.snd c)) (ha.rep.fst' c) (ha.rep.isPullback' c).flip
  have hsection : Etale ((BigFppfOver.toScheme B S hS).map
      (ha.rep.lift' (g := c) (𝟙 U) l hi)) := by
    refine MorphismProperty.of_postcomp (@Etale.{u} : MorphismProperty Scheme.{u}) _
      ((BigFppfOver.toScheme B S hS).map (ha.rep.fst' c)) hfirst ?_
    rw [← Functor.map_comp, ha.rep.lift'_fst (g := c) (𝟙 U) l hi, CategoryTheory.Functor.map_id]
    infer_instance
  rw [← ha.rep.lift'_snd (g := c) (𝟙 U) l hi, Functor.map_comp]
  infer_instance

/-! ### The implication of Stacks 03MJ -/

/-- **Stacks 03MJ, condition (1) from the represented base changes.** A property `P` of scheme
morphisms which survives composition with an étale morphism in front of it holds on every étale
chart of a morphism of presheaves all of whose represented base changes have `P`. -/
@[stacks 03MJ "condition (1) from the represented base changes"]
theorem presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y Z : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ Z), Etale i → P p → P (i ≫ p)) :
    PresheafImpliesHoldsOnEveryEtaleChart B S hS P := by
  intro G H φ hφ U V a b h ha hb hcomm
  have hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hφ.rep.fst b) :=
    presheaf_of_isPullback B S hS (hφ.rep.isPullback b).flip hb
  have hi : a ≫ φ = yoneda.map h ≫ b := hcomm.symm
  have hl : Etale ((BigFppfOver.toScheme B S hS).map (hφ.rep.lift (g := b) a h hi)) :=
    etale_of_comp_etale_chart B S hS ha hc (hφ.rep.lift_fst (g := b) a h hi)
  rw [← hφ.rep.lift_snd (g := b) a h hi, Functor.map_comp]
  exact hP _ _ hl (hφ.property_snd b)

/-- **Stacks 03MJ, condition (1) from the represented base changes.** A property `P` of scheme
morphisms which is stable under composition and holds for the étale morphisms holds on every
étale chart of a morphism of presheaves all of whose represented base changes have `P`. -/
theorem presheafImpliesHoldsOnEveryEtaleChart_of_etale_le (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition]
    (hle : (@Etale.{u} : MorphismProperty Scheme.{u}) ≤ P) :
    PresheafImpliesHoldsOnEveryEtaleChart B S hS P :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS P
    fun i p hi hp => P.comp_mem i p (hle _ _ _ hi) hp

/-- Being locally of finite type passes from the represented base changes of a morphism of
algebraic spaces over `S` to its étale charts. -/
theorem presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType :
    PresheafImpliesHoldsOnEveryEtaleChart B S hS
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_le B S hS _ fun _ _ f hf => by
    have : Etale f := hf
    infer_instance

/-- Being locally of finite type and locally quasi-finite passes from the represented base
changes of a morphism of algebraic spaces over `S` to its étale charts. -/
theorem presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite :
    PresheafImpliesHoldsOnEveryEtaleChart B S hS
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _ fun i p hi hp => by
    have : Etale i := hi
    have : LocallyOfFiniteType p := hp.1
    have : LocallyQuasiFinite p := hp.2
    have : LocallyQuasiFinite i := (locallyQuasiFinite_of_etale i).2
    exact ⟨inferInstance, inferInstance⟩

/-! ### The two remaining assertions of Stacks 03KN -/

variable {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally of finite type in
the sense of Stacks 03XF. This is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc` with its hypothesis discharged. -/
@[stacks 03KN "part (1): locally of finite type"]
theorem isLocallyOfFiniteType_mapDesc' (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyOfFiniteType B S hS (pullback.mapDesc f g h) :=
  isLocallyOfFiniteType_mapDesc B S hS
    (presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS) f g h hZ

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally quasi-finite in
the sense of Stacks 03XJ. This is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc` with its hypothesis discharged. -/
@[stacks 03KN "part (1): locally quasi-finite"]
theorem isLocallyQuasiFinite_mapDesc' (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyQuasiFinite B S hS (pullback.mapDesc f g h) :=
  isLocallyQuasiFinite_mapDesc B S hS
    (presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite B S hS) f g h hZ

end AlgebraicGeometry.Space

end
