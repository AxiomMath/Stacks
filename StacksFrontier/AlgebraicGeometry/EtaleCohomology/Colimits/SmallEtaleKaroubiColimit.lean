module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSystemDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# The colimit presentation of a system of abelian étale sheaves, as a Karoubi colimit

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes with a cone `c`, write `X = c.pt`, and let
`F` be a system of abelian sheaves on the small étale sites of the levels in the sense of
[Stacks, Tag 0EZL]. The sheaf `𝒢` on the small étale site of `X` that [Stacks, Tag 09YQ] speaks
of is `colim_i f_i^{-1}F_i`, which this development carries as the predicate
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` — a universal property
rather than a `CategoryTheory.Limits.IsColimit`, because the assignment `i ↦ f_i^{-1}F_i` is
**not a functor**: [Stacks, Tag 0EZL] imposes only the cocycle condition on a system, so the
diagram map of an identity transition is merely an idempotent
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem`) and not the identity.

This file removes that obstruction, at no cost in generality, by passing to the **Karoubi
envelope**. A non-unital diagram of the above shape is exactly a functor

`i ↦ (f_i^{-1}F_i, e_i)` from `I` to `Karoubi (Sheaf X.smallEtaleTopology AddCommGrpCat)`,

because in the Karoubi envelope the identity of the object `(L, e)` *is* `e`, and the two
one-sided absorption laws of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem_comp_systemDiagramMap` say
precisely that each diagram map is a morphism there. Moreover a compatible family of maps to a
sheaf `H` is exactly a cocone with vertex the image of `H`, so `IsColimitPresentation` becomes an
honest `IsColimit`.

Three things follow that the predicate alone does not give, and that the dévissage of
[Stacks, Tag 09YQ] needs:

* **existence** — every system has a colimit presentation, because the Karoubi envelope of the
  sheaf category has colimits (the sheaf category is abelian, hence idempotent complete, so the
  Karoubi envelope is equivalent to it);
* **exactness on the left** — a levelwise monomorphism of systems induces a monomorphism of the
  presenting sheaves, by the Grothendieck axiom AB5 for the sheaf category, since `I` is directed
  and therefore filtered; and
* a **uniqueness** statement for the induced maps, which is `IsColimit.uniq`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemKaroubiDiagram` — the functor
  `I ⥤ Karoubi (Sheaf X.smallEtaleTopology AddCommGrpCat)` attached to a system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemKaroubiCocone` — the cocone on it
  attached to a compatible family.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemKaroubiDiagramMap` — the morphism of
  functors attached to a morphism of systems.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_systemKaroubiCocone` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_of_isColimit` — **a
  colimit presentation is the same thing as a colimit of the Karoubi diagram.**
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_isColimitPresentation` — **every
  system has a colimit presentation**, as soon as the index is small in the coefficient universe.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.mono_of_pointwise_mono` — **a levelwise
  monomorphism of systems induces a monomorphism on the presenting sheaves.**

## Implementation notes

**Why a Karoubi colimit is not a weakening.** `IsColimitPresentation F 𝒢 ι` asks that every
compatible family factor uniquely through `ι`. Factoring through the legs of
`systemKaroubiCocone` is the same condition: the two directions are
`isColimit_systemKaroubiCocone` and `isColimitPresentation_of_isColimit`, and neither adds a
hypothesis. In particular nothing here imposes the identity law on the system; the identity law
is exactly what the Karoubi envelope supplies for free.

**The index direction.** For `a : i ⟶ j` in `Iᵒᵖ` the diagram map goes `f_j^{-1}F_j ⟶ f_i^{-1}F_i`,
so the diagram is a functor on `I` and not on `Iᵒᵖ`; the object at `i : I` is the one at
`Opposite.op i`. `Opposite.op (Opposite.unop i) = i` holds by definitional unfolding, which is
what lets the legs of a cocone be read as a family indexed by `Iᵒᵖ`.

**The universe hypotheses.** `exists_isColimitPresentation` needs `Small.{u + 1} I`, which is
what makes colimits of shape `I` exist in abelian sheaves with coefficients in
`AddCommGrpCat.{u + 1}` (`AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology`);
`mono_of_pointwise_mono` needs `UnivLE.{v, u + 1}`, which turns the Grothendieck-abelian AB5 of
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse` — stated at the
coefficient universe — into AB5 at the universe of the index. Neither is a hypothesis on the
*mathematics*: a system whose colimit does not exist has no presentation to speak of, and in the
setting of Stacks 09YQ the index is a directed set of the same size as the schemes.

**No instances are exported.** The colimit, filtered-colimit and AB5 instances for the sheaf
category and for its Karoubi envelope are introduced with `letI` inside the proofs that need
them, never registered. The coefficient universe of the sheaf category is not determined by the
arguments, so a global instance makes the unifier stick; this is the rule of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Sheafification/SmallEtaleColimits.lean`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-! ### The diagram in the Karoubi envelope -/

/-- **The diagram of a system in the Karoubi envelope of the sheaf category on the limit.** At
`i : I` the object is the formal direct factor of `f_i^{-1}F_i` cut out by the idempotent
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem` of the identity transition,
and the map of `i ⟶ j` is the diagram map of the opposite transition. This *is* a functor: the
identity law, which the system itself does not satisfy, holds in the Karoubi envelope because the
identity of `(L, e)` there is `e`. -/
def systemKaroubiDiagram (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) :
    I ⥤ Karoubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) where
  obj i :=
    { X := (etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).obj
        (F.obj (Opposite.op i))
      p := systemDiagramIdem F (Opposite.op i)
      idem := systemDiagramIdem_idem F (Opposite.op i) }
  map {i j} α :=
    { f := systemDiagramMap F α.op
      comm := by
        rw [systemDiagramMap_comp_systemDiagramIdem, systemDiagramIdem_comp_systemDiagramMap] }
  map_id i := rfl
  map_comp {i j k} α β := Karoubi.hom_ext _ _ (systemDiagramMap_comp F β.op α.op)

/-- The underlying sheaf of the Karoubi diagram at `i` is the inverse image of
`F.obj (Opposite.op i)` along `conePi c (Opposite.op i)`. -/
@[simp]
theorem systemKaroubiDiagram_obj_X (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (i : I) :
    ((systemKaroubiDiagram (c := c) F).obj i).X =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).obj
        (F.obj (Opposite.op i)) :=
  rfl

/-- The idempotent of the Karoubi diagram at `i` is `systemDiagramIdem F (Opposite.op i)`. -/
@[simp]
theorem systemKaroubiDiagram_obj_p (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (i : I) :
    ((systemKaroubiDiagram (c := c) F).obj i).p = systemDiagramIdem F (Opposite.op i) :=
  rfl

/-- The underlying map of the Karoubi diagram on `α : i ⟶ j` is `systemDiagramMap F α.op`. -/
@[simp]
theorem systemKaroubiDiagram_map_f (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : I}
    (α : i ⟶ j) : ((systemKaroubiDiagram (c := c) F).map α).f = systemDiagramMap F α.op :=
  rfl

/-- **The leg of a cocone on the Karoubi diagram**, read as a map out of the inverse image
`f_i^{-1}F_i` and indexed by `Iᵒᵖ` — the shape
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` asks for. The body is the
underlying map of the leg; what the ascription does is write the source as
`(etaleAbelianInverseImage (conePi c i)).obj (F.obj i)` rather than as the `X` field of the
Karoubi object at `Opposite.unop i`, which is the same sheaf but not the same expression. -/
def karoubiCoconeLeg (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (t : Cocone (systemKaroubiDiagram (c := c) F)) (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ t.pt.X :=
  (t.ι.app i.unop).f

/-- The leg of a cocone, at a level written as `Opposite.op i`, is the underlying map of the
cocone's component at `i`. -/
theorem karoubiCoconeLeg_op (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (t : Cocone (systemKaroubiDiagram (c := c) F)) (i : I) :
    karoubiCoconeLeg F t (Opposite.op i) = (t.ι.app i).f :=
  rfl

/-- **The legs of any cocone on the Karoubi diagram form a compatible family.** -/
theorem isCompatibleFamily_cocone_ι (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (t : Cocone (systemKaroubiDiagram (c := c) F)) :
    IsCompatibleFamily F t.pt.X (karoubiCoconeLeg F t) := by
  rw [isCompatibleFamily_iff_systemDiagramMap]
  intro i j a
  have hn := congrArg Karoubi.Hom.f (t.ι.naturality a.unop)
  simp only [Karoubi.comp_f, systemKaroubiDiagram_map_f, Functor.const_obj_map,
    Karoubi.id_f] at hn
  exact hn.trans (Karoubi.comp_p (t.ι.app j.unop))

/-- **The cocone on the Karoubi diagram attached to a compatible family.** Its vertex is the
image of the target sheaf under the embedding into the Karoubi envelope, and its legs are the
maps of the family; the Karoubi side condition on a leg is the compatibility of the family with
the identity transition of its level. -/
def systemKaroubiCocone (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H)
    (hτ : IsCompatibleFamily F H τ) : Cocone (systemKaroubiDiagram (c := c) F) where
  pt := (toKaroubi _).obj H
  ι :=
    { app := fun i => by
        refine { f := τ (Opposite.op i), comm := ?_ }
        change systemDiagramIdem F (Opposite.op i) ≫ τ (Opposite.op i) ≫ 𝟙 H = τ (Opposite.op i)
        rw [Category.comp_id]
        exact (isCompatibleFamily_iff_systemDiagramMap F H τ).mp hτ (𝟙 (Opposite.op i))
      naturality := fun i j α => by
        refine Karoubi.hom_ext _ _ ?_
        change systemDiagramMap F α.op ≫ τ (Opposite.op j) = τ (Opposite.op i) ≫ 𝟙 H
        rw [Category.comp_id]
        exact (isCompatibleFamily_iff_systemDiagramMap F H τ).mp hτ α.op }

/-- The vertex of `systemKaroubiCocone F H τ hτ` is the image of `H` in the Karoubi envelope. -/
@[simp]
theorem systemKaroubiCocone_pt (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H)
    (hτ : IsCompatibleFamily F H τ) :
    (systemKaroubiCocone F H τ hτ).pt = (toKaroubi _).obj H :=
  rfl

/-- The underlying map of the leg of `systemKaroubiCocone F H τ hτ` at `i` is
`τ (Opposite.op i)`. -/
theorem systemKaroubiCocone_ι_app_f (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H)
    (hτ : IsCompatibleFamily F H τ) (i : I) :
    ((systemKaroubiCocone F H τ hτ).ι.app i).f = τ (Opposite.op i) :=
  rfl

/-! ### A colimit presentation is a colimit of the Karoubi diagram -/

/-- **A colimit presentation makes the Karoubi cocone a colimit cocone.** -/
def isColimit_systemKaroubiCocone {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (h : IsColimitPresentation F 𝒢 ι) :
    IsColimit (systemKaroubiCocone F 𝒢 ι h.compatible) where
  desc t := by
    refine { f := h.desc (isCompatibleFamily_cocone_ι F t), comm := ?_ }
    change 𝟙 𝒢 ≫ h.desc (isCompatibleFamily_cocone_ι F t) ≫ t.pt.p =
      h.desc (isCompatibleFamily_cocone_ι F t)
    rw [Category.id_comp]
    refine h.hom_ext fun i => ?_
    rw [← Category.assoc, h.desc_fac (isCompatibleFamily_cocone_ι F t) i]
    exact Karoubi.comp_p (t.ι.app i.unop)
  fac t i := by
    refine Karoubi.hom_ext _ _ ?_
    change ι (Opposite.op i) ≫ h.desc (isCompatibleFamily_cocone_ι F t) = (t.ι.app i).f
    exact h.desc_fac (isCompatibleFamily_cocone_ι F t) (Opposite.op i)
  uniq t m hm := by
    refine Karoubi.hom_ext _ _ ?_
    refine h.hom_ext fun i => ?_
    change ι i ≫ m.f = ι i ≫ h.desc (isCompatibleFamily_cocone_ι F t)
    rw [h.desc_fac (isCompatibleFamily_cocone_ι F t) i]
    exact congrArg Karoubi.Hom.f (hm i.unop)

/-- **A colimit of the Karoubi diagram is a colimit presentation.** -/
theorem isColimitPresentation_of_isColimit {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (hι : IsCompatibleFamily F 𝒢 ι) (h : IsColimit (systemKaroubiCocone F 𝒢 ι hι)) :
    IsColimitPresentation F 𝒢 ι where
  compatible := hι
  existsUnique_desc H τ hτ := by
    refine ⟨show 𝒢 ⟶ H from (h.desc (systemKaroubiCocone F H τ hτ)).f, fun i => ?_,
      fun y hy => ?_⟩
    · have hfac := congrArg Karoubi.Hom.f (h.fac (systemKaroubiCocone F H τ hτ) i.unop)
      rwa [Karoubi.comp_f] at hfac
    · have hy' : ∀ i : I, (systemKaroubiCocone F 𝒢 ι hι).ι.app i ≫
          (show (systemKaroubiCocone F 𝒢 ι hι).pt ⟶ (systemKaroubiCocone F H τ hτ).pt from
            { f := y, comm := by
                show 𝟙 𝒢 ≫ y ≫ 𝟙 H = y
                rw [Category.id_comp, Category.comp_id] }) =
            (systemKaroubiCocone F H τ hτ).ι.app i := by
        intro i
        refine Karoubi.hom_ext _ _ ?_
        show ι (Opposite.op i) ≫ y = τ (Opposite.op i)
        exact hy (Opposite.op i)
      exact congrArg Karoubi.Hom.f (h.uniq (systemKaroubiCocone F H τ hτ) _ hy')

/-! ### Existence of a colimit presentation -/

/-- **Every system of abelian étale sheaves on the levels has a colimit presentation on the
limit**, as soon as the index is small in the coefficient universe.

The Karoubi envelope of the sheaf category is equivalent to it — the sheaf category is abelian
and therefore idempotent complete — so it has colimits of shape `I`; the colimit of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemKaroubiDiagram` is isomorphic to the
image of a sheaf, and transporting the colimit cocone to that image exhibits the presentation
through
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_of_isColimit`. -/
theorem exists_isColimitPresentation [Small.{u + 1} I]
    (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) :
    ∃ (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
      (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢),
      IsColimitPresentation F 𝒢 ι := by
  let : HasColimitsOfShape I (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :=
    hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} c.pt I
  let : HasColimitsOfShape I
      (Karoubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})) :=
    Adjunction.hasColimitsOfShape_of_equivalence (toKaroubiEquivalence _).inverse
  let t : Cocone (systemKaroubiDiagram (c := c) F) := colimit.cocone _
  let e := (toKaroubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})).objObjPreimageIso
    t.pt
  refine ⟨(toKaroubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})).objPreimage t.pt,
    fun i => karoubiCoconeLeg F t i ≫ e.inv.f, ?_⟩
  exact isColimitPresentation_of_isColimit
    (IsCompatibleFamily.comp (isCompatibleFamily_cocone_ι F t) e.inv.f)
    (IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext e.symm fun i => Karoubi.hom_ext _ _ rfl))

/-! ### A levelwise monomorphism induces a monomorphism of the presenting sheaves -/

/-- **The morphism of Karoubi diagrams attached to a morphism of systems.** Its component is the
inverse image of the level map followed by the idempotent of the target, which is what makes it a
morphism of formal direct factors. -/
def systemKaroubiDiagramMap {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i) :
    systemKaroubiDiagram (c := c) F ⟶ systemKaroubiDiagram (c := c) G where
  app i :=
    { f := (etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).map
        (φ (Opposite.op i)) ≫ systemDiagramIdem G (Opposite.op i)
      comm := systemDiagramIdem_comp_map_comp_systemDiagramIdem φ hφ (Opposite.op i) }
  naturality {i j} α :=
    Karoubi.hom_ext _ _ (systemDiagramMap_comp_map_comp_systemDiagramIdem φ hφ α.op)

/-- The underlying map of the component of `systemKaroubiDiagramMap φ hφ` at `i` is the inverse
image of `φ (Opposite.op i)` followed by the idempotent `systemDiagramIdem G (Opposite.op i)`. -/
theorem systemKaroubiDiagramMap_app_f {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i) (i : I) :
    ((systemKaroubiDiagramMap (c := c) φ hφ).app i).f =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).map (φ (Opposite.op i)) ≫
        systemDiagramIdem G (Opposite.op i) :=
  rfl

/-- **A criterion for a morphism of the Karoubi envelope of a preadditive category to be a
monomorphism.** If the underlying map is `m ≫ Q.p` for an `m` commuting with the two idempotents
and monomorphic, then the Karoubi morphism is a monomorphism: a map into `P` absorbs `P.p`, so a
map killed by `m ≫ Q.p` is already killed by `m`.

Nothing of the kind holds for `m ≫ Q.p` in the underlying category — `Q.p` is an idempotent and
not a monomorphism — which is why the criterion is stated for the Karoubi morphism. -/
theorem mono_karoubi_of_mono_comp_p {C : Type*} [Category* C] [Preadditive C] {P Q : Karoubi C}
    (m : P.X ⟶ Q.X) (hm : P.p ≫ m = m ≫ Q.p) (hmono : Mono m) (f : P ⟶ Q)
    (hf : f.f = m ≫ Q.p) : Mono f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z g hg
  rw [Karoubi.hom_eq_zero_iff] at hg ⊢
  rw [Karoubi.comp_f, hf] at hg
  refine (Preadditive.mono_iff_cancel_zero m).mp hmono _ _ ?_
  rwa [← Karoubi.comp_p g, Category.assoc, hm]

/-- **A levelwise monomorphism of systems induces a monomorphism of the presenting sheaves.**

This is the Grothendieck axiom AB5 for abelian sheaves on the small étale site of the limit: the
index `I` is a directed preorder, hence filtered, so a monomorphism of filtered diagrams in the
Karoubi envelope has monomorphic colimit, and the fully faithful embedding of the sheaf category
into its Karoubi envelope reflects monomorphisms.

It is the left exactness of the passage to the limit sheaf, and it is what turns the levelwise
short exact sequences of the dévissage of [Stacks, Tag 09YQ] into a short exact sequence on the
limit. -/
theorem mono_of_pointwise_mono [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {𝒢F 𝒢G : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ιF : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢F}
    {ιG : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (G.obj i) ⟶ 𝒢G}
    (hF : IsColimitPresentation F 𝒢F ιF) (hG : IsColimitPresentation G 𝒢G ιG)
    (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i)
    (hmono : ∀ i : Iᵒᵖ, Mono (φ i)) (χ : 𝒢F ⟶ 𝒢G)
    (hχ : ∀ i : Iᵒᵖ, ιF i ≫ χ =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) ≫ ιG i) :
    Mono χ := by
  let := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse c.pt
  let : HasFilteredColimitsOfSize.{v, v}
      (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :=
    ⟨fun J _ _ => hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} c.pt J⟩
  let : AB5OfSize.{v, v} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :=
    AB5OfSize_of_univLE.{v, v, u + 1, u + 1} _
  let : HasFilteredColimitsOfSize.{v, v}
      (Karoubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})) :=
    ⟨fun J _ _ => Adjunction.hasColimitsOfShape_of_equivalence (toKaroubiEquivalence _).inverse⟩
  let : AB5OfSize.{v, v} (Karoubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})) :=
    ⟨fun J _ _ => HasExactColimitsOfShape.of_codomain_equivalence J (toKaroubiEquivalence _)⟩
  have hstable := MorphismProperty.IsStableUnderFilteredColimits.isStableUnderColimitsOfShape
    (W := MorphismProperty.monomorphisms
      (Karoubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}))) I
  have hpt : ∀ i : I, Mono ((systemKaroubiDiagramMap (c := c) φ hφ).app i) := by
    intro i
    have : Mono (φ (Opposite.op i)) := hmono (Opposite.op i)
    refine mono_karoubi_of_mono_comp_p
      ((etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).map (φ (Opposite.op i)))
      (systemDiagramIdem_naturality φ hφ (Opposite.op i)) (Functor.map_mono _ _) _ ?_
    rw [systemKaroubiDiagramMap_app_f, systemKaroubiDiagram_obj_p]
    rfl
  have := hpt
  have hcomm : ∀ i : I, (systemKaroubiCocone F 𝒢F ιF hF.compatible).ι.app i ≫
      (toKaroubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})).map χ =
      (systemKaroubiDiagramMap (c := c) φ hφ).app i ≫
        (systemKaroubiCocone G 𝒢G ιG hG.compatible).ι.app i := by
    intro i
    refine Karoubi.hom_ext _ _ ?_
    show ιF (Opposite.op i) ≫ χ =
      ((etaleAbelianInverseImage.{u, u + 1} (conePi c (Opposite.op i))).map (φ (Opposite.op i)) ≫
        systemDiagramIdem G (Opposite.op i)) ≫ ιG (Opposite.op i)
    rw [hχ (Opposite.op i), Category.assoc,
      IsCompatibleFamily.systemDiagramIdem_comp hG.compatible (Opposite.op i)]
  exact (toKaroubi (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})).mono_of_mono_map
    (hstable.condition _ _ _ _ (isColimit_systemKaroubiCocone hF)
      (isColimit_systemKaroubiCocone hG) (systemKaroubiDiagramMap φ hφ) hpt _ hcomm)

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
