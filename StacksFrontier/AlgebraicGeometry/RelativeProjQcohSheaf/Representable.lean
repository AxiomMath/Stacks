module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# Relative Proj as a functor: representability of `F_d` by a scheme

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and fix an integer `d`.
Section 01NS attaches to `d` the functor `F_d` whose value on a test scheme `T` is the set of
strict equivalence classes of quadruples `(d, f : T → S, L, ψ)`, and **Tag 01NV** says that
`F_d` is representable by a scheme.

The source's proof has four steps: (1) `F_d` is a Zariski sheaf; (2) for an affine open cover
`S = ⋃ U_i` one considers the subfunctors `F_{d,i} ⊆ F_d` of those pairs whose morphism to `S`
factors through `U_i`; (3) each `F_{d,i}` is representable, by Tag 01NU, the affine case; (4) the
`F_{d,i}` are open subfunctors covering `F_d`, so Schemes, Lemma 26.15.4 (Tag 01JJ) applies and
`F_d` is representable.

This file states the tag with steps (1), (2) and (3) **carried as explicit named hypotheses**
and proves step (4). Nothing is weakened.

## What is carried, and why

The functor `F_d` itself is **not** carried: it is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor`, whose action on a morphism of test
schemes is the pullback of a quadruple and whose two functor laws are proved in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`. The statements below come in
two forms: one concluding about `Fd.functor`, and one concluding about a functor
`Fd.functorOfModel` transported from the carried sheaf, which is what the statements said before
the functor laws were available.

* `G` and `model`: a `Type u`-valued Zariski sheaf on `Sch` whose sections over a test scheme
  are in bijection with `F_d(T)`. Two things are carried by this. The source's **step (1)**, the
  Zariski sheaf property of `F_d`, of which only the *separatedness* half is proved — it is
  `...RelativeProjQcohSheaf.ZariskiSeparated.Fd.isSeparated_functor`, unconditional, so a
  compatible family of classes on a Zariski covering has **at most** one amalgamation; that it has
  one is what is still missing. (Glueing
  invertible modules along an open cover is *not* what is missing for it:
  `Stacks.SheafOfModules.ModulesGlueData.glued` glues a family of modules given on the members
  of a family of open immersions with a cocycle of comparisons, and
  `Stacks.SheafOfModules.UnitTransitionCocycle.isInvertible_glue` shows the result is invertible.
  Nor is the cocycle condition on the overlaps what is missing: the witness of
  `Quadruple.StrictlyEquivalent` is unique, by
  `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_witness_unique`, so the comparisons on
  the overlaps compose on the triple overlaps, which is
  `...RelativeProjQcohSheaf.Quadruple.eq_trans_of_witness` and is that cocycle condition. What is
  missing is the glueing construction itself: assembling the glued invertible module and a glued
  `ψ` into a quadruple over the whole test scheme whose restrictions are strictly equivalent to
  the given ones.) And **smallness**, because Mathlib's form
  of Tag 01JJ is stated for `Type u`-valued sheaves while `Fd A d T` lives in `Type (u + 1)`, a
  quadruple recording an invertible module. The restriction maps of `F_d` are *not* carried; for
  the statements about `Fd.functor` the hypothesis `naturality` asks only that `G`'s restriction
  maps agree with the pullback of a quadruple through the bijections.
* `base_naturality`, in the `functorOfModel` form: that the carried restriction maps are
  compatible with the projection to `Hom(-, S)`, that is, that the morphism `T' ⟶ S` of a
  restricted class is the restricted morphism. In the `Fd.functor` form this is not a hypothesis;
  it follows from `naturality` and `Fd.pullback_fst`.
* `c`, `hc` and `hcover`: the representing schemes of the affine-local subfunctors, as a jointly
  surjective family of relatively representable open immersions into `G`. This carries steps
  (2) and (3), that is, **Tag 01NU** in the shape those charts want. Tag 01NU *itself* is proved:
  `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean` represents
  `Fd.functor` over an affine base by the open `U_d` of Equation 27.12.0.1, and
  `...RelativeProjQcohSheaf.Fd.chartRelativeEquiv` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartFdRepresentation.lean` carries that
  to the open `U_d ⊓ f⁻¹(U)` of a relative homogeneous spectrum, naturally in the test scheme.
  The passage from those chart-wise representations to the family `c`, `hc`, `hcover` into one
  model — the identification of the subfunctor `F_{d,i}` of `F_d` with `F_d` of the restricted
  algebra, the relative representability of each `c i` by an open immersion, and their joint
  local surjectivity — is carried out in
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineOpenCharts.lean`, for Situation
  01NN and `d ≥ 1`; the binders stay here because these statements are more general than the
  tag, for an arbitrary graded algebra and an arbitrary integer `d`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functorOfModel`: the functor `F_d`
  presented through the carried sheaf: its value on `T` is the set `F_d(T)` of Section 01NS and
  its action on a morphism is transported from the sheaf rather than being the pullback of a
  quadruple.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base`:
  **the functor `F_d` is representable by a scheme over `S`, conditionally on the above.** There
  are a scheme `Y`, a morphism `p : Y ⟶ S` and a representation of `Fd.functor` by `Y` under
  which the morphism `T ⟶ Y` attached to a class in `F_d(T)`, composed with `p`, is the morphism
  `T ⟶ S` that class records. So `Y` represents `F_d` as a functor to schemes over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.isRepresentable_functor`: the same in the
  bare form, `(Fd.functor …).IsRepresentable`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.exists_representableBy_over_base` and
  `...Fd.isRepresentable_functorOfModel`: **Tag 01NV, conditionally**, for the transported
  functor `functorOfModel`.

Beyond Mathlib's Tag 01JJ the proof contributes the passage from the small sheaf `G` to the
functor on the sets `F_d(T)`, and the structure morphism: `p` is read off the universal element
of `F_d(Y)`, and the compatibility for *every* class is then forced, since every class is the
restriction of the universal element along the morphism representing it.

## Implementation notes

`Fd.functorOfModel` is given by transport along the carried bijections, so that its value on a
test scheme is the set `F_d(T)` itself, up to `rfl` (`Fd.functorOfModel_obj`), rather than an
abstract set isomorphic to it. Its action is `Fd.functorOfModel_map`, also by `rfl`, and the two
functor laws are the laws for `G` conjugated by the bijections.

Representability is `CategoryTheory.Functor.RepresentableBy`, which compares `(T ⟶ Y)` with
`F.obj (op T)` through an `Equiv` and therefore applies to a `Type (u + 1)`-valued functor on
`Scheme.{u}` as well as to a `Type u`-valued one. Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`, on the other hand, delivers a
representation of the `Type u`-valued sheaf only, which is why the comparison is carried out by
hand rather than by `CategoryTheory.Functor.RepresentableBy.ofIso`: that transport is stated for
two functors valued in one universe.

## Not done here

Nothing here produces the Zariski sheaf `G`, and nothing here assembles the charts. Of the two
things `G` carries, the sheaf property of `F_d` is proved only in its separatedness half
(`...RelativeProjQcohSheaf.ZariskiSeparated.Fd.isSeparated_functor`; what
`CategoryTheory.Presieve.IsSeparated.isSheaf` still wants is the existence of an amalgamation),
and the smallness of its values is not established *in this file* — `F_d(T)` records an
invertible module and so lives in `Type (u + 1)`, and the hypothesis `model` is already the
weakest form of smallness there is, an `Equiv` with a `Type u` set, so no `ULift` can remove it.
It is established downstream, unconditionally, as `...RelativeProjQcohSheaf.Fd.small` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleSmall.lean`. Hence `c`, `hc`,
`hcover` and the pair `G`, `model` all remain hypotheses here. What is no longer carried is the
functoriality of `F_d`.

Three things about those hypotheses *are* now settled, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SmallModel`, and they are what to read
before adding to the list above. The smallness is a **consequence** of the conclusion
(`...SmallModel.Fd.small_of_representableBy`: a representation gives a bijection of `F_d(T)` with
a `Type u` set of morphisms), so it is not an artefact of going through Tag 01JJ and no spelling
of the tag avoids it; it is **not independent of `c`, `hc`, `hcover`** either, being local on the
test scheme by the separatedness proved in `...ZariskiSeparated` and hence a consequence of Tag
01NU (`...SmallModel.Fd.small_of_cover`, `...SmallModel.Fd.small_of_baseCover`); and the
compatibility hypotheses `naturality` and `base_naturality` are **not needed at all** once the
model is taken to be the canonical `T ↦ Shrink (F_d(T))`, for which the compatibility is the
theorem `...SmallModel.Fd.smallPresheaf_naturality`. So
`...SmallModel.Fd.exists_representableBy_functor_of_isSheaf` and
`...SmallModel.Fd.isRepresentable_functor_of_isSheaf` state this tag carrying only the smallness
of the sets `F_d(T)`, the Zariski sheaf property of `F_d` itself, and Tag 01NU.
The uniqueness of the representing scheme up to isomorphism over `S`, formal from the
representation, is not stated.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  (G : Sheaf Scheme.zariskiTopology.{u} (Type u))
  (model : ∀ T : Scheme.{u}, G.obj.obj (op T) ≃ Fd A d T)

/-- **Stacks Project, Section 01NS, the functor `F_d`.** Given a `Type u`-valued Zariski sheaf
`G` on `Sch` whose sections over a test scheme are in bijection with the set `F_d(T)` of strict
equivalence classes of quadruples, the functor on schemes whose value on `T` *is* `F_d(T)` and
whose action on morphisms is transported from `G`.

What this repository does not have is the *sheaf* `G` and the bijections, and the reason is
**not** that `F_d` is only a family of sets: the pullback of a quadruple along a morphism of test
schemes is constructed in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback`, descends to
`...RelativeProjQcohSheaf.UnionPullback.Fd.pullback`, and makes `F_d` a functor already, namely
`...RelativeProjQcohSheaf.UnionFunctor.Fd.functor`. The reason is **smallness**: `F_d(T)` lives
in `Type (u + 1)` while a `Type u`-valued sheaf on `Sch` lives in `Type u`, and a bijection
`G(T) ≃ F_d(T)` across those universes *is* the assertion that `F_d(T)` is essentially small.
That is a theorem to be proved, not a spelling to be fixed, and it is not proved here; so a
functor that is to be compared with a `Type u`-valued sheaf has to be presented through such a
model. Which theorem it is, is settled in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SmallModel`: the smallness is local on the
test scheme and follows from Tag 01NU (`...SmallModel.Fd.small_of_baseCover`), and once it is
granted the model needs no choosing and no compatibility hypothesis —
`...SmallModel.Fd.smallPresheaf` is the canonical one. -/
def Fd.functorOfModel : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := Fd A d T.unop
  map {T T'} k :=
    TypeCat.ofHom fun ξ => model T'.unop (G.obj.map k ((model T.unop).symm ξ))
  map_id T := by ext ξ; simp
  map_comp {T T' T''} k k' := by ext ξ; simp

/-- The value of the functor on a test scheme is the set `F_d(T)` itself. -/
theorem Fd.functorOfModel_obj (T : Scheme.{u}) :
    (Fd.functorOfModel A d G model).obj (op T) = Fd A d T := rfl

/-- The action of the functor on a morphism of test schemes, transported from the sheaf. -/
theorem Fd.functorOfModel_map {T' T : Scheme.{u}} (k : T' ⟶ T) (ξ : Fd A d T) :
    (Fd.functorOfModel A d G model).map k.op ξ = model T' (G.obj.map k.op ((model T).symm ξ)) :=
  rfl

/-- Tag 01JJ applied to a model `m` of a functor `F` with a projection `π` to `Hom(-, S)`: `F` is
representable by a scheme over `S`, given the charts. -/
private theorem exists_representableBy_of_charts {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)}
    (π : ∀ T : Scheme.{u}, F.obj (op T) → (T ⟶ S))
    (m : ∀ T : Scheme.{u}, G.obj.obj (op T) ≃ F.obj (op T))
    (hnat : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      m T' (G.obj.map k.op x) = F.map k.op (m T x))
    (base_naturality : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      π T' (m T' (G.obj.map k.op x)) = k ≫ π T (m T x))
    {ι : Type u} {X : ι → Scheme.{u}} (c : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : F.RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : F.obj (op T)), e.homEquiv.symm ξ ≫ p = π T ξ := by
  have := hcover
  have r : G.obj.RepresentableBy (Scheme.LocalRepresentability.glueData hc).glued :=
    Scheme.LocalRepresentability.representableBy hc
  refine ⟨_, π _ (m _ (r.homEquiv (𝟙 _))),
    { homEquiv := fun {T} => r.homEquiv.trans (m T)
      homEquiv_comp := fun k g => by
        simp only [Equiv.trans_apply, r.homEquiv_comp, hnat] }, fun T ξ => ?_⟩
  have hk : ξ = m T (G.obj.map ((r.homEquiv.trans (m T)).symm ξ).op (r.homEquiv (𝟙 _))) := by
    rw [← r.homEquiv_comp, Category.comp_id]
    exact (Equiv.apply_symm_apply (r.homEquiv.trans (m T)) ξ).symm
  exact (congrArg (π T) hk).trans
    (base_naturality ((r.homEquiv.trans (m T)).symm ξ) (r.homEquiv (𝟙 _))) |>.symm

/-- **Stacks Project, Tag 01NV, conditionally.** The functor `F_d` of Section 01NS is
representable by a scheme over `S`: there are a scheme `Y`, a morphism `p : Y ⟶ S` and a
representation of `F_d` by `Y` under which the morphism `T ⟶ Y` representing a class
`ξ ∈ F_d(T)`, composed with `p`, is the morphism `T ⟶ S` recorded by `ξ`.

Three inputs of the source's proof are not available in this repository and are carried as
explicit named hypotheses.

* `G` and `model`, through which the functor is presented: a `Type u`-valued Zariski sheaf on
  `Sch` naturally in bijection with the family of sets `F_d(T)`. This is the source's step (1),
  the Zariski sheaf property, together with the restriction maps of `F_d` — the pullback of a
  quadruple is not constructed here — and with the smallness that Tag 01JJ needs.
* `base_naturality`: the compatibility of those restriction maps with the projection to
  `Hom(-, S)`.
* `c`, with `hc` and `hcover`: a jointly surjective family of relatively representable open
  immersions into `G`, that is, the representing schemes of the affine-local subfunctors
  `F_{d,i}`. This is the source's steps (2) and (3), namely **Tag 01NU**, which is not proved
  here; the tag is `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`.

What is proved is the source's step (4) together with the passage from the small sheaf to the
functor on the sets `F_d(T)` and the construction of the structure morphism: `p` is the morphism
to `S` recorded by the universal element of `F_d(Y)`, and the compatibility of the
representation with the projections follows from naturality. -/
-- [Stacks, Tag 01NV] is registered unconditionally on
-- AffineOpenCharts.Fd.isRepresentable_functor_of_pos; this statement is the conditional form and
-- carries its hypotheses, so it no longer claims the tag. Its content is unchanged.
theorem Fd.exists_representableBy_over_base
    (base_naturality : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      (model T' (G.obj.map k.op x)).1 = k ≫ (model T x).1)
    {ι : Type u} {X : ι → Scheme.{u}} (c : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : (Fd.functorOfModel A d G model).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1 := by
  exact exists_representableBy_of_charts G (F := Fd.functorOfModel A d G model) (fun _ ξ => ξ.1)
    model (fun k x => congrArg (model _) (congrArg _ (Equiv.symm_apply_apply _ _).symm))
    base_naturality c hc hcover

/-- **Stacks Project, Tag 01NV, conditionally, in the bare form.** The functor `F_d` of Section
01NS is representable.

This is `Fd.exists_representableBy_over_base` forgetting the structure morphism to `S`; see
there for what is carried and what is proved. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Same carried hypotheses see the clause string there: the Zariski sheaf model carrying step
--   (1), the smallness and the restriction maps this statement uses, and the affine-local charts
--   carrying Tag 01NU. Fd.isRepresentable_functor is the same conclusion for Fd.functor, whose
--   restriction maps are the pullback of a quadruple and are not carried
theorem Fd.isRepresentable_functorOfModel
    (base_naturality : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      (model T' (G.obj.map k.op x)).1 = k ≫ (model T x).1)
    {ι : Type u} {X : ι → Scheme.{u}} (c : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    (Fd.functorOfModel A d G model).IsRepresentable := by
  obtain ⟨Y, _, e, _⟩ :=
    Fd.exists_representableBy_over_base A d G model base_naturality c hc hcover
  exact ⟨Y, ⟨e⟩⟩

/-! ### The same statements for the genuine functor `F_d`

`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor` is the functor `F_d` built from the
pullback of a quadruple, with both functor laws proved. The two statements below conclude
representability of *that* functor, so the restriction maps of `F_d` are no longer carried: the
sheaf `G` is asked only to be a `Type u`-valued Zariski-sheaf **model** of it, and the
compatibility of its restriction maps with those of `F_d` is the hypothesis `naturality` — a
property of the carried bijections, not a further datum. `base_naturality` disappears as well,
being `Fd.pullback_fst` composed with `naturality`.
-/

/-- **The functor `F_d` is representable by a scheme over `S`, given a small Zariski-sheaf model
of it and the affine-local charts.** This is `Fd.exists_representableBy_over_base` with the
transported functor `Fd.functorOfModel` replaced by the genuine functor `Fd.functor`, whose action
on morphisms is the pullback of a quadruple.

What `G` and `model` carry here is therefore only the **Zariski sheaf property** of `F_d` (the
source's step (1)) and the **smallness** of the sets `F_d(T)`, which Mathlib's form of Tag 01JJ
needs because it is stated for `Type u`-valued sheaves while `F_d(T)` lives in `Type (u + 1)`.
The restriction maps of `F_d` are not carried; `naturality` only requires that `G`'s restriction
maps be the pullback of a quadruple read through the bijections.

The family `c`, `hc`, `hcover` still carries the source's steps (2) and (3), that is
**Tag 01NU**; for Situation 01NN and `d ≥ 1` it is supplied by
`...RelativeProjQcohSheaf.Fd.affineOpenChart` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineOpenCharts.lean`. -/
theorem Fd.exists_representableBy_functor_over_base
    (naturality : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      model T' (G.obj.map k.op x) = Fd.pullback k (model T x))
    {ι : Type u} {X : ι → Scheme.{u}} (c : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : (Fd.functor A d).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1 := by
  refine exists_representableBy_of_charts G (F := Fd.functor A d) (fun _ ξ => ξ.1) model
    (fun k x => naturality k x) (fun k x => ?_) c hc hcover
  exact (congrArg (fun ξ : Fd A d _ => ξ.1) (naturality k x)).trans (Fd.pullback_fst k _)

/-- **The functor `F_d` is representable, in the bare form.** This is
`Fd.exists_representableBy_functor_over_base` forgetting the structure morphism to `S`; see there
for what is carried. -/
theorem Fd.isRepresentable_functor
    (naturality : ∀ {T' T : Scheme.{u}} (k : T' ⟶ T) (x : G.obj.obj (op T)),
      model T' (G.obj.map k.op x) = Fd.pullback k (model T x))
    {ι : Type u} {X : ι → Scheme.{u}} (c : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    (Fd.functor A d).IsRepresentable := by
  obtain ⟨Y, _, e, _⟩ :=
    Fd.exists_representableBy_functor_over_base A d G model naturality c hc hcover
  exact ⟨Y, ⟨e⟩⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
