module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.Deformation.Artin.ChangeOfField
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# The change-of-field functor is an equivalence under (RS)

This file proves the second assertion of Tag 07WX: the canonical functor
`(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` built in
`StacksFrontier/Deformation/Artin/ChangeOfField.lean` is an equivalence as soon as `𝒳` satisfies
the Rim–Schlessinger condition (RS).

## Main definitions

* `Deformation.Artin.OverIsArtinianLocal` and `Deformation.Artin.OverIsFiniteType` — the two
  conditions cutting out the objects (RS) quantifies over, for a scheme over `S` rather than
  for an object of a chosen big fppf site.
* `Deformation.Artin.SatisfiesRSOver` — condition (RS) for a category fibred in groupoids over
  the category `Over S` of all schemes over `S`, in the shape `Deformation.Artin.SatisfiesRS`
  (Tag 07WP) has over the site.

## Main results

* `Deformation.Artin.changeOfFieldFunctor_isEquivalence` — the canonical functor of Tag 07WX is
  an equivalence when `𝒳` satisfies (RS).
* `Deformation.Artin.changeOfFieldFunctor_faithful`,
  `Deformation.Artin.changeOfFieldFunctor_full` and
  `Deformation.Artin.changeOfFieldFunctor_essSurj` are its three constituents.

## Implementation notes

The ambient base category of Tag 07WX, as formalized in
`StacksFrontier/Deformation/Artin/ChangeOfField.lean`, is the category `Over S` of all schemes over
`S`, so condition (RS) is needed in that shape. `Deformation.Artin.SatisfiesRS` (Tag 07WP) is
stated for a category fibred in groupoids over a chosen big fppf site, and transporting the
change-of-field construction to the site would require placing `Spec A` in the chosen site.
`Deformation.Artin.SatisfiesRSOver` is therefore the same condition over `Over S`: for every
pushout square of affine, local Artinian, finite-type schemes over `S` along a closed immersion,
the comparison `Deformation.Artin.fiberSquareComparison` from the fibre over the fourth corner
to the two-fibre product of the fibres over the other three corners is an equivalence. It is
stated with respect to the same choice of pullbacks the functor itself is built from, since the
condition does not depend on that choice.

The square (RS) is applied to is essentially the one already built in
`StacksFrontier/Deformation/Artin/ChangeOfField.lean`: its corners are `Spec l`, `Spec C`,
`Spec k` and `Spec (C ×_l k)`, its legs are `Deformation.Artin.restrictionResidueMap`,
`q.map η`, `Deformation.Artin.changeOfFieldBaseMap` and `Deformation.Artin.residueBaseMap`, and
it is a pushout along a closed immersion by Tag 0ET0 applied to the fibre-product square of
rings of the comparison functor of Tag 07W8, the residue map `C ⟶ l` being surjective. The three
constituents of the equivalence then read:

* faithfulness is the uniqueness half, that an arrow out of an object over `Spec (C ×_l k)` is
  determined by its restrictions to `Spec C` and to `Spec k`;
* fullness is the existence half for arrows;
* essential surjectivity is the gluing of a deformation over `C` with `x₀` along `x_{l,0}`.

### No unrestricted `@[stacks 07WX]`

One restriction is recorded in the attribute string of
`Deformation.Artin.changeOfFieldFunctor_isEquivalence`: the hypothesis is that `𝒳` is fibred in
groupoids over the category of *all* `S`-schemes, whereas the source asks only that `𝒳` be
fibred in groupoids over the big fppf site `(Sch/S)_{fppf}`. This is the same restriction the
construction of the functor carries in
`StacksFrontier/Deformation/Artin/ChangeOfField.lean`. Consequently (RS) is used here in the
matching form `Deformation.Artin.SatisfiesRSOver` rather than in the site form
`Deformation.Artin.SatisfiesRS` of Tag 07WP; the two are independent definitions and no
implication between them is proved here.

This restriction is not a deferred step, and a bridge between the two forms of (RS) would not
remove it. A category fibred in groupoids over the big fppf site presents itself over the
category of all `S`-schemes as the composite `p ⋙ Over.post B.inclusion`, and that composite is
never fibred in groupoids over `Over S`, nor does it admit a choice of pullbacks there:
`Deformation.Artin.not_isFiberedInGroupoids_comp_post` and
`Deformation.Artin.not_nonempty_choiceOfPullbacks_comp_post`, in
`StacksFrontier/Deformation/Artin/ChangeOfField/SiteFibrednessObstruction.lean`, prove both
negations from the cutoff cardinal of the site. The two fibredness hypotheses are therefore
incomparable rather than one being weaker than the other, the hypotheses of the theorem below
cannot be instantiated at a site-presented category at all, and a statement of the form "site
hypotheses imply the change-of-field functor is an equivalence" obtained that way would be
vacuous. Carrying Tag 07WX to the site needs the construction re-derived over the site.

It is so re-derived, in `StacksFrontier/Deformation/Artin/ChangeOfField/SiteRestriction.lean`:
`Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence` is the second assertion of Tag 07WX
for a category fibred in groupoids over the big fppf site, under (RS) in the site form
`Deformation.Artin.SatisfiesRS` of Tag 07WP, with no choice of pullbacks over `Over S` assumed.
The theorem below is the same statement over the category of all `S`-schemes.

The finite-type hypotheses on the two residue-field points are explicit hypotheses rather than a
restriction: the source has them standing, `k` being of finite type over `S` and `l/k` finite.

## References

* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Deformation.Artin

/-! ### Lifting and gluing through the comparison of a square of fibres -/

section FiberSquare

open CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type*} [Category C] {Y : Type*} [Category Y]
variable (q : Y ⥤ C) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (w : f ≫ i = g ≫ j)

/-- The comparison isomorphism between the pullback functors along two equal morphisms is
compatible with the two chosen cartesian lifts. -/
private theorem pullbackFunctorEqToIso_app_fac (f' g' : U ⟶ V) (h : f' = g') (x : q.Fiber V) :
    Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor h)).app x).hom ≫
      c.map g' x = c.map f' x := by
  cases h
  exact Category.id_comp _

/-- The isomorphism carried by the value of the comparison functor identifies the two composite
cartesian lifts of a commutative square in the base. -/
private theorem fiberSquareComparison_iso_fac (x : q.Fiber Z) :
    Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j w).obj x).iso.hom ≫
      c.map g (c.obj j x) ≫ c.map j x = c.map f (c.obj i x) ≫ c.map i x := by
  change Fiber.fiberInclusion.map (((c.objCompIso f i x).symm ≪≫
    (eqToIso (congrArg c.pullbackFunctor w)).app x ≪≫ c.objCompIso g j x).hom) ≫ _ = _
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [c.objCompIso_hom_fac, pullbackFunctorEqToIso_app_fac q c _ _ w]
  rw [← c.objCompIso_hom_fac f i x]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  change (𝟙 _ ≫ _) ≫ _ = _
  simp only [Category.id_comp]

/-- When `q` is fibred in groupoids, two lifts of one arrow with domains in the same fibre differ
by an isomorphism of that fibre. -/
private theorem exists_fiberIso_fac (hq : q.IsFiberedInGroupoids) (b : U ⟶ V) {a : Y}
    {z z' : q.Fiber U} (φ : z.1 ⟶ a) (φ' : z'.1 ⟶ a) [q.IsHomLift b φ] [q.IsHomLift b φ'] :
    ∃ e : z ≅ z', Fiber.fiberInclusion.map e.hom ≫ φ' = φ ∧
      Fiber.fiberInclusion.map e.inv ≫ φ = φ' :=
  have hc := (hq.isStronglyCartesian_homLift b φ).isCartesian_of_isStronglyCartesian
  have hc' := (hq.isStronglyCartesian_homLift b φ').isCartesian_of_isStronglyCartesian
  ⟨_, fiberIsoOfCartesian_hom_fac b φ φ' hc hc', fiberIsoOfCartesian_inv_fac b φ φ' hc hc'⟩

/-- When the comparison of a square is faithful, a morphism of the fibre over the fourth
corner is determined by its two chosen restrictions. -/
private theorem fiberSquareComparison_hom_ext
    [(fiberSquareComparison q c f g i j w).Faithful]
    {s t : q.Fiber Z} {α β : s ⟶ t}
    (hi : c.map i s ≫ Fiber.fiberInclusion.map α =
      c.map i s ≫ Fiber.fiberInclusion.map β)
    (hj : c.map j s ≫ Fiber.fiberInclusion.map α =
      c.map j s ≫ Fiber.fiberInclusion.map β) : α = β := by
  apply (fiberSquareComparison q c f g i j w).map_injective
  apply CategoricalPullback.hom_ext
  · change c.homMap i α = c.homMap i β
    apply fiber_hom_ext_of_cartesian i (c.map i t) inferInstance
    simpa only [c.homMap_fac] using hi
  · change c.homMap j α = c.homMap j β
    apply fiber_hom_ext_of_cartesian j (c.map j t) inferInstance
    simpa only [c.homMap_fac] using hj

/-- When the comparison of a square is full, a compatible pair of morphisms of the two chosen
restrictions comes from a morphism of the fibre over the fourth corner. -/
private theorem fiberSquareComparison_hom_exists
    [(fiberSquareComparison q c f g i j w).Full]
    {s t : q.Fiber Z} (α : c.obj i s ⟶ c.obj i t) (β : c.obj j s ⟶ c.obj j t)
    (h : (c.pullbackFunctor f).map α ≫
        ((fiberSquareComparison q c f g i j w).obj t).iso.hom =
      ((fiberSquareComparison q c f g i j w).obj s).iso.hom ≫
        (c.pullbackFunctor g).map β) :
    ∃ γ : s ⟶ t,
      c.map i s ≫ Fiber.fiberInclusion.map γ =
          Fiber.fiberInclusion.map α ≫ c.map i t ∧
        c.map j s ≫ Fiber.fiberInclusion.map γ =
          Fiber.fiberInclusion.map β ≫ c.map j t := by
  let m : (fiberSquareComparison q c f g i j w).obj s ⟶
      (fiberSquareComparison q c f g i j w).obj t := ⟨α, β, h⟩
  let γ := (fiberSquareComparison q c f g i j w).preimage m
  have hm := (fiberSquareComparison q c f g i j w).map_preimage m
  have hi : c.homMap i γ = α := congrArg CategoricalPullback.Hom.fst hm
  have hj : c.homMap j γ = β := congrArg CategoricalPullback.Hom.snd hm
  refine ⟨γ, ?_, ?_⟩
  · rw [← hi, c.homMap_fac]
  · rw [← hj, c.homMap_fac]

/-- **Where (RS) enters, the gluing step.** When the comparison of a square is essentially
surjective, a pair of arrows out of an object of the fibre over the first corner can be
completed to a commutative square of arrows into an object of the fibre over the fourth
corner. -/
private theorem fiberSquareComparison_glue
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).EssSurj]
    (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    [q.IsHomLift f α] [q.IsHomLift g β] :
    ∃ (t : q.Fiber Z) (γ : y.val ⟶ t.val) (δ : z.val ⟶ t.val),
      q.IsHomLift i γ ∧ q.IsHomLift j δ ∧ α ≫ γ = β ≫ δ := by
  obtain ⟨eV, heV, -⟩ := exists_fiberIso_fac q hq f (c.map f y) α
  obtain ⟨eW, heW, -⟩ := exists_fiberIso_fac q hq g β (c.map g z)
  let d : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) :=
    ⟨y, z, eV ≪≫ eW⟩
  obtain ⟨t, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (fiberSquareComparison q c f g i j w) d
  have hidV : q.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map e.inv.fst) := e.inv.fst.property
  have hidW : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map e.inv.snd) := e.inv.snd.property
  have hγ : q.IsHomLift i (Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t) :=
    CategoryTheory.IsHomLift.comp_lift_id_left' q V
      (Fiber.fiberInclusion.map e.inv.fst) i (c.map i t)
  have hδ : q.IsHomLift j (Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t) :=
    CategoryTheory.IsHomLift.comp_lift_id_left' q W
      (Fiber.fiberInclusion.map e.inv.snd) j (c.map j t)
  refine ⟨t, Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t,
    Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t, hγ, hδ, ?_⟩
  have hw := congrArg (fun m : c.obj f y ⟶ c.obj g (c.obj j t) =>
      Fiber.fiberInclusion.map m ≫ c.map g (c.obj j t) ≫ c.map j t) e.inv.w
  simp only [Functor.ChoiceOfPullbacks.pullbackFunctor_map, Functor.map_comp,
    Category.assoc, fiberSquareComparison_iso_fac] at hw
  have hi : Fiber.fiberInclusion.map (c.homMap f e.inv.fst) ≫
      c.map f (c.obj i t) ≫ c.map i t =
      c.map f y ≫ Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t := by
    have hfac := congrArg (fun m => m ≫ c.map i t) (c.homMap_fac f e.inv.fst)
    simp only [Category.assoc] at hfac
    exact hfac
  have hj : Fiber.fiberInclusion.map (c.homMap g e.inv.snd) ≫
      c.map g (c.obj j t) ≫ c.map j t =
      c.map g z ≫ Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t := by
    have hfac := congrArg (fun m => m ≫ c.map j t) (c.homMap_fac g e.inv.snd)
    simp only [Category.assoc] at hfac
    exact hfac
  rw [hi, hj] at hw
  apply (cancel_epi (Fiber.fiberInclusion.map eV.hom)).mp
  calc
    Fiber.fiberInclusion.map eV.hom ≫ α ≫
          Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t =
        c.map f y ≫ Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t := by
      rw [← Category.assoc, heV]
    _ = Fiber.fiberInclusion.map d.iso.hom ≫
          c.map g z ≫ Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t := hw
    _ = Fiber.fiberInclusion.map eV.hom ≫ β ≫
          Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t := by
      change Fiber.fiberInclusion.map (eV.hom ≫ eW.hom) ≫ _ = _
      rw [Functor.map_comp, Category.assoc,
        ← Category.assoc (Fiber.fiberInclusion.map eW.hom), heW]

/-- When the comparison of a square is faithful, a morphism of the fibre over the fourth corner
is determined by its composites with one arrow from the fibre over the second corner and one
arrow from the fibre over the third corner. -/
private theorem fiberSquareComparison_hom_ext_of_lifts
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).Faithful]
    {s t : q.Fiber Z} (y : q.Fiber V) (z : q.Fiber W)
    (r : y.val ⟶ s.val) (s₂ : z.val ⟶ s.val)
    [q.IsHomLift i r] [q.IsHomLift j s₂]
    {α β : s ⟶ t}
    (hi : r ≫ Fiber.fiberInclusion.map α = r ≫ Fiber.fiberInclusion.map β)
    (hj : s₂ ≫ Fiber.fiberInclusion.map α = s₂ ≫ Fiber.fiberInclusion.map β) : α = β := by
  obtain ⟨eV, hfV, -⟩ := exists_fiberIso_fac q hq i (c.map i s) r
  obtain ⟨eW, hfW, -⟩ := exists_fiberIso_fac q hq j (c.map j s) s₂
  refine fiberSquareComparison_hom_ext q c f g i j w ?_ ?_
  · rw [← hfV, Category.assoc, Category.assoc, hi]
  · rw [← hfW, Category.assoc, Category.assoc, hj]

/-- When the comparison of a square is full, a compatible pair of arrows out of the two chosen
restrictions of an object of the fibre over the fourth corner factors through a morphism of
that fibre. -/
private theorem fiberSquareComparison_desc
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).Full]
    {s t : q.Fiber Z} (r : (c.obj i s).val ⟶ t.val) (s₂ : (c.obj j s).val ⟶ t.val)
    [q.IsHomLift i r] [q.IsHomLift j s₂]
    (h : c.map f (c.obj i s) ≫ r =
      Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j w).obj s).iso.hom ≫
        c.map g (c.obj j s) ≫ s₂) :
    ∃ γ : s ⟶ t, c.map i s ≫ Fiber.fiberInclusion.map γ = r ∧
      c.map j s ≫ Fiber.fiberInclusion.map γ = s₂ := by
  obtain ⟨eα, hα, -⟩ := exists_fiberIso_fac q hq i r (c.map i t)
  obtain ⟨eβ, hβ, -⟩ := exists_fiberIso_fac q hq j s₂ (c.map j t)
  obtain ⟨γ, hγi, hγj⟩ := fiberSquareComparison_hom_exists q c f g i j w eα.hom eβ.hom (by
    apply fiber_hom_ext_of_cartesian (g ≫ j) (c.map g (c.obj j t) ≫ c.map j t)
      (hq.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
    simp only [Functor.ChoiceOfPullbacks.pullbackFunctor_map, Functor.map_comp,
      Category.assoc, fiberSquareComparison_iso_fac]
    calc
      Fiber.fiberInclusion.map (c.homMap f eα.hom) ≫
          c.map f (c.obj i t) ≫ c.map i t = c.map f (c.obj i s) ≫ r := by
        rw [← Category.assoc, c.homMap_fac, Category.assoc, hα]
      _ = _ := h
      _ = _ := by
        rw [← hβ, ← Category.assoc (c.map g (c.obj j s)), ← c.homMap_fac]
        simp only [Category.assoc])
  exact ⟨γ, hγi.trans hα, hγj.trans hβ⟩

/-- **Where (RS) enters, the extension step.** When the comparison of a square is full, a pair
of arrows into an object of the fibre over the fourth corner compatible with a pair of arrows
out of the fibre over the first corner extends along a second such compatible pair. -/
private theorem fiberSquareComparison_pointed_hom_exists
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).Full]
    {s t : q.Fiber Z} (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    (r : y.val ⟶ s.val) (s₂ : z.val ⟶ s.val)
    (r' : y.val ⟶ t.val) (s₂' : z.val ⟶ t.val)
    [q.IsHomLift f α] [q.IsHomLift g β]
    [q.IsHomLift i r] [q.IsHomLift j s₂]
    [q.IsHomLift i r'] [q.IsHomLift j s₂']
    (ha : α ≫ r = β ≫ s₂) (hb : α ≫ r' = β ≫ s₂') :
    ∃ γ : s ⟶ t, r ≫ Fiber.fiberInclusion.map γ = r' ∧
      s₂ ≫ Fiber.fiberInclusion.map γ = s₂' := by
  have hsr : q.IsStronglyCartesian i r := hq.isStronglyCartesian_homLift i r
  have hss : q.IsStronglyCartesian j s₂ := hq.isStronglyCartesian_homLift j s₂
  obtain ⟨eV, heV, -⟩ := exists_fiberIso_fac q hq i (c.map i s) r
  obtain ⟨eW, heW, -⟩ := exists_fiberIso_fac q hq j (c.map j s) s₂
  obtain ⟨e, he, -⟩ :=
    exists_fiberIso_fac q hq (f ≫ i) (c.map f (c.obj i s) ≫ c.map i s) (α ≫ r)
  have hα : Fiber.fiberInclusion.map e.hom ≫ α =
      c.map f (c.obj i s) ≫ Fiber.fiberInclusion.map eV.hom := by
    refine Functor.IsStronglyCartesian.ext q i r f ?_
    simpa only [Category.assoc, heV] using he
  have hβ : Fiber.fiberInclusion.map e.hom ≫ β =
      Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j w).obj s).iso.hom ≫
        c.map g (c.obj j s) ≫ Fiber.fiberInclusion.map eW.hom := by
    refine Functor.IsStronglyCartesian.ext q j s₂ g ?_
    simp only [Category.assoc, heW, fiberSquareComparison_iso_fac]
    rw [← ha]
    exact he
  obtain ⟨γ, hi, hj⟩ := fiberSquareComparison_desc q c f g i j w hq
    (Fiber.fiberInclusion.map eV.hom ≫ r') (Fiber.fiberInclusion.map eW.hom ≫ s₂') (by
      rw [← Category.assoc, ← hα]
      rw [← Category.assoc (c.map g (c.obj j s)),
        ← Category.assoc (Fiber.fiberInclusion.map
          ((fiberSquareComparison q c f g i j w).obj s).iso.hom), ← hβ]
      simpa only [Category.assoc] using
        congrArg (fun m => Fiber.fiberInclusion.map e.hom ≫ m) hb)
  refine ⟨γ, ?_, ?_⟩
  · apply (cancel_epi (Fiber.fiberInclusion.map eV.hom)).mp
    simpa only [← Category.assoc, heV] using hi
  · apply (cancel_epi (Fiber.fiberInclusion.map eW.hom)).mp
    simpa only [← Category.assoc, heW] using hj

/-- **Where (RS) enters, the uniqueness step.** When the comparison of a square is faithful, an
arrow out of an object of the fibre over the fourth corner is determined by its composites with
one arrow from the fibre over the second corner and one arrow from the fibre over the third
corner. -/
private theorem fiberSquareComparison_arrow_ext
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).Faithful]
    {s : q.Fiber Z} {b : Y} (h : Z ⟶ q.obj b)
    (y : q.Fiber V) (z : q.Fiber W)
    (r : y.val ⟶ s.val) (s₂ : z.val ⟶ s.val)
    [q.IsHomLift i r] [q.IsHomLift j s₂]
    {α β : s.val ⟶ b} [q.IsHomLift h α] [q.IsHomLift h β]
    (hi : r ≫ α = r ≫ β) (hj : s₂ ≫ α = s₂ ≫ β) : α = β := by
  let b₀ : q.Fiber (q.obj b) := ⟨b, rfl⟩
  have hsl : q.IsStronglyCartesian h (c.map h b₀) :=
    hq.isStronglyCartesian_homLift h (c.map h b₀)
  obtain ⟨eα, hα, -⟩ := exists_fiberIso_fac q hq h α (c.map h b₀)
  obtain ⟨eβ, hβ, -⟩ := exists_fiberIso_fac q hq h β (c.map h b₀)
  have he : eα.hom = eβ.hom := by
    refine fiberSquareComparison_hom_ext_of_lifts q c f g i j w hq y z r s₂ ?_ ?_
    · refine Functor.IsStronglyCartesian.ext q h (c.map h b₀) i ?_
      simpa only [Category.assoc, hα, hβ] using hi
    · refine Functor.IsStronglyCartesian.ext q h (c.map h b₀) j ?_
      simpa only [Category.assoc, hα, hβ] using hj
  rw [← hα, ← hβ, he]

/-- **Where (RS) enters, the existence step.** When the comparison of a square is full, a
compatible pair of arrows out of the fibres over the second and third corners factors through an
arrow out of an object of the fibre over the fourth corner. -/
private theorem fiberSquareComparison_pointed_arrow_exists
    (hq : q.IsFiberedInGroupoids)
    [(fiberSquareComparison q c f g i j w).Full]
    {s : q.Fiber Z} {b : Y} (h : Z ⟶ q.obj b)
    (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    (r : y.val ⟶ s.val) (s₂ : z.val ⟶ s.val)
    (r' : y.val ⟶ b) (s₂' : z.val ⟶ b)
    [q.IsHomLift f α] [q.IsHomLift g β]
    [q.IsHomLift i r] [q.IsHomLift j s₂]
    [q.IsHomLift (i ≫ h) r'] [q.IsHomLift (j ≫ h) s₂']
    (ha : α ≫ r = β ≫ s₂) (hb : α ≫ r' = β ≫ s₂') :
    ∃ γ : s.val ⟶ b, q.IsHomLift h γ ∧ r ≫ γ = r' ∧ s₂ ≫ γ = s₂' := by
  let b₀ : q.Fiber (q.obj b) := ⟨b, rfl⟩
  have hsl : q.IsStronglyCartesian h (c.map h b₀) :=
    hq.isStronglyCartesian_homLift h (c.map h b₀)
  let r₀ := Functor.IsStronglyCartesian.map q h (c.map h b₀) (g := i) rfl r'
  let s₀ := Functor.IsStronglyCartesian.map q h (c.map h b₀) (g := j) rfl s₂'
  have hr : r₀ ≫ c.map h b₀ = r' := Functor.IsStronglyCartesian.fac q h (c.map h b₀) rfl r'
  have hs : s₀ ≫ c.map h b₀ = s₂' := Functor.IsStronglyCartesian.fac q h (c.map h b₀) rfl s₂'
  have hb' : α ≫ r₀ = β ≫ s₀ := by
    have hlift : q.IsHomLift (f ≫ i) (β ≫ s₀) := w.symm ▸ inferInstance
    refine Functor.IsStronglyCartesian.ext q h (c.map h b₀) (f ≫ i) ?_
    simpa only [Category.assoc, hr, hs] using hb
  obtain ⟨γ, hγi, hγj⟩ := fiberSquareComparison_pointed_hom_exists q c f g i j w hq
    x y z α β r s₂ r₀ s₀ ha hb'
  have hid : q.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map γ) := γ.property
  refine ⟨Fiber.fiberInclusion.map γ ≫ c.map h b₀, ?_, ?_, ?_⟩
  · exact CategoryTheory.IsHomLift.comp_lift_id_left' q Z
      (Fiber.fiberInclusion.map γ) h (c.map h b₀)
  · rw [← Category.assoc, hγi, hr]
  · rw [← Category.assoc, hγj, hs]

end FiberSquare

/-! ### Condition (RS) over the category of all schemes over `S` -/

section RSOver

universe u v w

variable {S : Scheme.{u}}

/-- An object of `Over S` whose domain is the spectrum of a local Artinian ring. This is the
condition `Deformation.Artin.IsArtinianLocal` of Tag 07WP, read for a scheme over `S` rather
than for an object of a chosen big fppf site. -/
public abbrev OverIsArtinianLocal (X : Over S) : Prop :=
  IsAffine X.left ∧ IsLocalRing Γ(X.left, ⊤) ∧ IsArtinianRing Γ(X.left, ⊤)

/-- An object of `Over S` which is of finite type over `S`. This is the condition
`Deformation.Artin.IsFiniteTypeOver` of Tag 07WP, read for a scheme over `S`. -/
public abbrev OverIsFiniteType (X : Over S) : Prop :=
  LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom

/-- **Condition (RS)**, for a category fibred in groupoids over the category `Over S` of all
schemes over `S`: for every pushout square of finite-type local Artinian schemes over `S` along
a closed immersion, restriction from the fibre over the pushout identifies that fibre with the
two-fibre product of the fibres over the other three corners.

This is `Deformation.Artin.SatisfiesRS` (Tag 07WP) with the chosen big fppf site replaced by
`Over S`, which is the ambient base category the change-of-field functor of Tag 07WX is built
over. The condition is stated for a given choice of pullbacks, on which it does not depend. -/
public abbrev SatisfiesRSOver {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (c : q.ChoiceOfPullbacks) : Prop :=
  ∀ {U U' V V' : Over S} (i : U ⟶ U') (j : U ⟶ V) (i' : U' ⟶ V') (j' : V ⟶ V')
      (hw : i ≫ i' = j ≫ j'),
    OverIsArtinianLocal U → OverIsArtinianLocal U' →
      OverIsArtinianLocal V → OverIsArtinianLocal V' →
      OverIsFiniteType U → OverIsFiniteType U' →
      OverIsFiniteType V → OverIsFiniteType V' →
    IsClosedImmersion i.left →
      IsPushout i.left j.left i'.left j'.left →
        (fiberSquareComparison q c j i j' i' hw.symm).IsEquivalence

/-- The spectrum of a local Artinian ring, with any structure map to `S`, is one of the objects
condition (RS) quantifies over. -/
theorem overIsArtinianLocal_spec (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (b : Spec (CommRingCat.of R) ⟶ S) :
    OverIsArtinianLocal (Over.mk b) := by
  change IsAffine (Spec (CommRingCat.of R)) ∧ IsLocalRing Γ(Spec (CommRingCat.of R), ⊤) ∧
    IsArtinianRing Γ(Spec (CommRingCat.of R), ⊤)
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.isLocalRing
  · exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.isArtinianRing

/-- The residue map of an object of `𝒞_{Λ,κ}` is a map of `Λ`-algebras. -/
private theorem residueMap_comp_algebraMap_aux {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ κ) :
    (residueMap A).comp (algebraMap Λ A) = algebraMap Λ κ := by
  ext a
  change A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A a)) = algebraMap Λ κ a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply Λ A (ResidueField A) a]
  exact A.residueEquiv.commutes a

/-- Finite type of the chosen residue-field point transfers to the spectrum of any Artinian
local algebra with that residue field. -/
theorem spec_finiteType_of_residueField_point {Λ κ : Type u} [CommRing Λ] [Field κ]
    [Algebra Λ κ] (A : ArtinianLocalAlgCat.{u, u, u} Λ κ) (iΛ : Spec (.of Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  let f : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let g : Spec (.of κ) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ
  let eSpec := Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso A.residueEquiv.symm.toRingEquiv).op
  have hring : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom (residueMap A) =
      CommRingCat.ofHom (algebraMap Λ κ) := by
    rw [← CommRingCat.ofHom_comp, residueMap_comp_algebraMap_aux]
  have hbase : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ f = g := by
    simp only [f, g, ← Category.assoc, ← Spec.map_comp, hring]
  have hfactor : eSpec.hom ≫ Spec.map (CommRingCat.ofHom (residueMap A)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    dsimp [eSpec]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change A.residueEquiv.symm (A.residueEquiv (IsLocalRing.residue A a)) = _
    exact A.residueEquiv.symm_apply_apply _
  have hcanonical : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f =
      eSpec.hom ≫ g := by
    rw [← hfactor, Category.assoc, hbase]
  have hg : LocallyOfFiniteType g := hfinite
  have hgc : QuasiCompact g := hqc
  have hresFinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := by
    rw [hcanonical]
    infer_instance
  have hresQC : QuasiCompact
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := by
    rw [hcanonical]
    infer_instance
  exact (AlgebraicGeometry.finiteType_iff_residueField_comp_finiteType S A f).2
    ⟨hresFinite, hresQC⟩

end RSOver

/-! ### The pushout square attached to a change of residue field -/

section Square

universe u v w

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} (iΛ : Spec (.of T.Λ) ⟶ S)

/-- The residue map of an object of `𝒞_{Λ,κ}` is a map of `Λ`-algebras. -/
theorem residueMap_comp_algebraMap_self {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ κ) :
    (residueMap A).comp (algebraMap Λ A) = algebraMap Λ κ :=
  residueMap_comp_algebraMap_aux A

/-- The structure map of `Spec κ` factors through the structure map of `Spec A`. -/
theorem specMap_residueMap_comp_self {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ κ) (iΛ' : Spec (.of Λ) ⟶ S) :
    Spec.map (CommRingCat.ofHom (residueMap A)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ') =
      Spec.map (CommRingCat.ofHom (algebraMap Λ κ)) ≫ iΛ' := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    residueMap_comp_algebraMap_self]

/-- The structure map of `Spec l` factors through the structure map of `Spec k`. -/
theorem specMap_fieldExtension_comp :
    Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ := by
  have h : (algebraMap T.k T.l).comp (algebraMap T.Λ T.k) = algebraMap T.Λ T.l :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply T.Λ T.k T.l a).symm
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The arrow `Spec l ⟶ Spec k` of `Over S` given by the finite extension `l/k`. -/
def specFieldExtensionMap :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (specMap_fieldExtension_comp T iΛ)

/-- The underlying morphism of `specFieldExtensionMap` is `Spec` of `algebraMap k l`. -/
@[simp]
theorem specFieldExtensionMap_left :
    (specFieldExtensionMap T iΛ).left =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) := rfl

/-- The arrow `Spec l ⟶ Spec C` of `Over S` given by the residue map of an object of
`𝒞_{Λ,l}`; the arrow `Deformation.Artin.restrictionResidueMap` is this one, read out of the
image of the distinguished point. -/
def specResidueFieldMap (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)))
    (specMap_residueMap_comp T iΛ C)

/-- The underlying morphism of `specResidueFieldMap` is `Spec` of the residue map of `C`. -/
@[simp]
theorem specResidueFieldMap_left (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    (specResidueFieldMap T iΛ C).left =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)) := rfl

/-- The arrow `Spec k ⟶ Spec A` of `Over S` given by the residue map of an object of
`𝒞_{Λ,k}`. -/
def specResidueBaseMap (A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (residueMap A)))
    (specMap_residueMap_comp_self A iΛ)

/-- The underlying morphism of `specResidueBaseMap` is `Spec` of the residue map of `A`. -/
@[simp]
theorem specResidueBaseMap_left (A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k) :
    (specResidueBaseMap T iΛ A).left =
      Spec.map (CommRingCat.ofHom (residueMap A)) := rfl

/-- The arrow `Spec C ⟶ Spec A` of `Over S` attached to an identification of `A` with the
comparison algebra `C ×_l k`; the arrow
`Deformation.Artin.changeOfFieldRestrictionBaseMap` is this one,
read into the image of the deformed point. -/
def changeOfFieldBaseMap {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)))
    (specMap_changeOfFieldMap_comp T iΛ e)

/-- The underlying morphism of `changeOfFieldBaseMap` is `Spec` of `changeOfFieldMap`. -/
@[simp]
theorem changeOfFieldBaseMap_left {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (changeOfFieldBaseMap T iΛ e).left =
      Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)) := rfl

/-- The square of spectra of `l`, `C`, `k` and `A` attached to a change of field commutes in
`Over S`. -/
theorem specResidueFieldMap_comp_changeOfFieldBaseMap
    {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    specResidueFieldMap T iΛ C ≫ changeOfFieldBaseMap T iΛ e =
      specFieldExtensionMap T iΛ ≫ specResidueBaseMap T iΛ A := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, specResidueFieldMap_left, changeOfFieldBaseMap_left,
    specFieldExtensionMap_left, specResidueBaseMap_left]
  exact (specMap_changeOfFieldMap_square T A e).symm

/-! #### The square is a pushout along a closed immersion -/

/-- An isomorphism of `𝒞_{Λ,κ}` as an isomorphism of the underlying rings. -/
def isoRingEquiv {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ κ} (e : A ⟶ B) [IsIso e] : A ≃+* B where
  toFun := e.hom
  invFun := (inv e).hom
  left_inv a := congrArg (fun z : A ⟶ A => z.hom a) (IsIso.hom_inv_id e)
  right_inv b := congrArg (fun z : B ⟶ B => z.hom b) (IsIso.inv_hom_id e)
  map_mul' x y := map_mul e.hom x y
  map_add' x y := map_add e.hom x y

/-- The residue map of `A` computes the second coordinate of the comparison algebra. -/
theorem residueMap_eq_pullbackSnd {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) (a : A) :
    residueMap A a =
      (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.2 :=
  (e.residue_comm a).symm.trans ((Deformation.comparisonFunctor T).residue_snd C (e.hom a))

/-- An identification of `A` with the comparison algebra `C ×_l k` identifies the square of
rings `l`, `C`, `k`, `A` with a fibre product. -/
theorem comparisonRing_isPullback {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) [IsIso e] :
    IsPullback (CommRingCat.ofHom (residueMap A))
      (CommRingCat.ofHom (changeOfFieldMap T e))
      (CommRingCat.ofHom (algebraMap T.k T.l))
      (CommRingCat.ofHom (Deformation.residueMap T C)) := by
  let φ : A ≃+* RingHom.pullback (Deformation.residueMap T C) (algebraMap T.k T.l) :=
    (isoRingEquiv e).trans ((Deformation.comparisonFunctor T).pullbackEquiv C)
  have h := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom (Deformation.residueMap T C))
    (CommRingCat.ofHom (algebraMap T.k T.l)))
  refine (h.of_iso φ.toCommRingCatIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (Category.comp_id _) (Category.comp_id _)).flip
  · ext x
    exact (congrArg (fun z => z.val.1) (φ.apply_symm_apply x)).symm
  · ext x
    exact ((residueMap_eq_pullbackSnd T e (φ.symm x)).trans
      (congrArg (fun z => z.val.2) (φ.apply_symm_apply x))).symm

/-- The residue map of an object of `𝒞_{Λ,l}` is surjective. -/
theorem residueMap_surjective (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    Function.Surjective (Deformation.residueMap T C) :=
  C.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := C))

/-- The leg `Spec l ⟶ Spec C` of the change-of-field square is a closed immersion. -/
theorem specResidueFieldMap_isClosedImmersion (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    IsClosedImmersion (specResidueFieldMap T iΛ C).left := by
  rw [specResidueFieldMap_left]
  exact IsClosedImmersion.spec_of_surjective _ (residueMap_surjective T C)

/-- **Stacks Project, Tag 0ET0 applied to a change of residue field.** The square of spectra of
`l`, `C`, `k` and `A ≅ C ×_l k` is a pushout of schemes, because the residue map `C ⟶ l` is
surjective. -/
theorem specChangeOfField_isPushout {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) [IsIso e] :
    IsPushout (specResidueFieldMap T iΛ C).left (specFieldExtensionMap T iΛ).left
      (changeOfFieldBaseMap T iΛ e).left (specResidueBaseMap T iΛ A).left := by
  rw [specResidueFieldMap_left, specFieldExtensionMap_left, changeOfFieldBaseMap_left,
    specResidueBaseMap_left]
  exact Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (comparisonRing_isPullback T e) (residueMap_surjective T C)

/-! #### The base maps of a morphism of deformations of `x₀` -/

/-- The structure map of `Spec B` factors through a morphism `A ⟶ B` of `𝒞_{Λ,κ}`. -/
theorem specMap_hom_comp_self {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ κ} (h : A ⟶ B) (iΛ' : Spec (.of Λ) ⟶ S) :
    Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ') =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ' := by
  have hcomm : h.hom.toRingHom.comp (algebraMap Λ A) = algebraMap Λ B :=
    RingHom.ext h.hom.commutes
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm]

/-- The spectrum of a morphism of `𝒞_{Λ,k}`, as an arrow of `Over S`. -/
def algebraBaseMapSelf {A B : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} (h : A ⟶ B) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ B)) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom h.hom.toRingHom)) (specMap_hom_comp_self h iΛ)

/-- The underlying morphism of `algebraBaseMapSelf` is `Spec` of the given algebra map. -/
@[simp]
theorem algebraBaseMapSelf_left {A B : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} (h : A ⟶ B) :
    (algebraBaseMapSelf T iΛ h).left =
      Spec.map (CommRingCat.ofHom h.hom.toRingHom) := rfl

/-- The distinguished arrow from `Spec k` is compatible with change of the base algebra. -/
@[reassoc]
theorem specResidueBaseMap_comp {A B : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} (h : A ⟶ B) :
    specResidueBaseMap T iΛ B ≫ algebraBaseMapSelf T iΛ h = specResidueBaseMap T iΛ A := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, algebraBaseMapSelf_left, specResidueBaseMap_left,
    specResidueBaseMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change B.residueEquiv (IsLocalRing.residue B (h.hom a)) =
    A.residueEquiv (IsLocalRing.residue A a)
  exact h.residue_comm a

/-- The naturality square of the change-of-field base maps, in `Over S`. -/
@[reassoc]
theorem changeOfFieldBaseMap_naturality
    {A A' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C)
    (e' : A' ⟶ (Deformation.comparisonFunctor T).functor.obj C')
    (g : A ⟶ A') (h : C ⟶ C')
    (hcomm : g ≫ e' = e ≫ (Deformation.comparisonFunctor T).functor.map h) :
    changeOfFieldBaseMap T iΛ e' ≫ algebraBaseMapSelf T iΛ g =
      algebraBaseMap T iΛ h ≫ changeOfFieldBaseMap T iΛ e := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, changeOfFieldBaseMap_left, algebraBaseMapSelf_left,
    algebraBaseMap_left, changeOfFieldBaseMap_left]
  exact specMap_changeOfFieldMap_naturality T e e' g h hcomm

/-- The change-of-field map is natural in the identification of the base algebra. -/
theorem changeOfFieldMap_comp_hom {A A' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l} (g : A ⟶ A')
    (e' : A' ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    changeOfFieldMap T (g ≫ e') = (changeOfFieldMap T e').comp g.hom.toRingHom := by
  rw [changeOfFieldMap_naturality T (g ≫ e') e' g (𝟙 C)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id])]
  exact RingHom.ext fun _ => rfl

end Square

/-! ### The three constituents of the equivalence -/

section Equivalence

universe u v w

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} (iΛ : Spec (.of T.Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
variable {x₀ xₗ : X}
variable {hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)}
variable (hxₗ : q.obj xₗ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable {η : xₗ ⟶ x₀}
variable (hη : eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map η).left ≫
  eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
variable (c : q.ChoiceOfPullbacks)

/-- Reading off an equality of morphisms from an equality of their conjugates. -/
theorem eq_of_conj_eq {C : Type*} [Category C] {W W' Z Z' : C}
    (hW : W' = W) (hZ : Z' = Z) {f g : W ⟶ Z}
    (h : eqToHom hW ≫ f ≫ eqToHom hZ.symm = eqToHom hW ≫ g ≫ eqToHom hZ.symm) : f = g := by
  subst hW
  subst hZ
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- An arrow whose base morphism, conjugated by the identifications of its endpoints, is the
underlying morphism of `f` lies over `f`. -/
private theorem isHomLift_of_left_conj {R R' : Over S} (f : R ⟶ R') {A B : X} (φ : A ⟶ B)
    (hA : q.obj A = R) (hB : q.obj B = R')
    (h : eqToHom (congrArg Over.left hA).symm ≫ (q.map φ).left ≫
      eqToHom (congrArg Over.left hB) = f.left) : q.IsHomLift f φ := by
  refine CategoryTheory.IsHomLift.of_fac' q _ _ hA hB ?_
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
  exact eq_of_eqToHom_conj (congrArg Over.left hA) (congrArg Over.left hB) h

include hη in
/-- The arrow `x_{l,0} ⟶ x₀` lies over the leg `Spec l ⟶ Spec k` of the change-of-field
square. -/
theorem eta_isHomLift : q.IsHomLift (specFieldExtensionMap T iΛ) η :=
  isHomLift_of_left_conj _ η hxₗ hx₀ hη

/-- The arrow of a deformation of `x₀` lies over the leg `Spec k ⟶ Spec A`. -/
theorem deformationObject_arrow_isHomLift (d : DeformationObject iΛ q x₀ hx₀) :
    q.IsHomLift (specResidueBaseMap T iΛ d.algebra) d.arrow :=
  isHomLift_of_left_conj _ _ hx₀ d.base d.arrow_base

/-- The arrow of a deformation of `x_{l,0}` lies over the leg `Spec l ⟶ Spec C`. -/
theorem deformationObject_arrow_isHomLift_l (ee : DeformationObject iΛ q xₗ hxₗ) :
    q.IsHomLift (specResidueFieldMap T iΛ ee.algebra) ee.arrow :=
  isHomLift_of_left_conj _ _ hxₗ ee.base ee.arrow_base

/-- The reversed arrow of a morphism of deformations of `x₀` lies over the spectrum of its
arrow of `𝒞_{Λ,k}`. -/
theorem deformationMorphism_arrow_isHomLift {a b : DeformationObject iΛ q x₀ hx₀}
    (m : DeformationMorphism iΛ q x₀ hx₀ a b) :
    q.IsHomLift (algebraBaseMapSelf T iΛ m.ringHom ≫ eqToHom a.base.symm) m.arrow := by
  refine CategoryTheory.IsHomLift.of_fac' q _ _ b.base rfl ?_
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
    Over.eqToHom_left, algebraBaseMapSelf_left,
    eq_of_eqToHom_conj (congrArg Over.left b.base) (congrArg Over.left a.base) m.arrow_base]
  simp only [eqToHom_refl, Category.comp_id]

/-- The arrow of a deformation of `x₀` lies over the leg `Spec k ⟶ Spec A`, read into the
image of the deformed point. -/
theorem deformationObject_arrow_isHomLift' (d : DeformationObject iΛ q x₀ hx₀) :
    q.IsHomLift (specResidueBaseMap T iΛ d.algebra ≫ eqToHom d.base.symm) d.arrow := by
  have hlift := deformationObject_arrow_isHomLift T iΛ d
  refine CategoryTheory.IsHomLift.of_fac' q _ _ hx₀ rfl ?_
  rw [CategoryTheory.IsHomLift.fac' q (specResidueBaseMap T iΛ d.algebra) d.arrow]
  simp only [eqToHom_refl, Category.comp_id]

/-- The reversed arrow of a morphism of deformations of `x_{l,0}` lies over the spectrum of its
arrow of `𝒞_{Λ,l}`. -/
theorem deformationMorphism_arrow_isHomLift_l {a b : DeformationObject iΛ q xₗ hxₗ}
    (m : DeformationMorphism iΛ q xₗ hxₗ a b) :
    q.IsHomLift (algebraBaseMap T iΛ m.ringHom) m.arrow :=
  isHomLift_of_left_conj _ _ b.base a.base m.arrow_base

/-- The restricting arrow of a deformation lies over the leg `Spec C ⟶ Spec A`. -/
theorem changeOfFieldRestriction_isHomLift (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.IsHomLift (changeOfFieldBaseMap T iΛ e) (changeOfFieldRestriction T iΛ c d e) := by
  refine CategoryTheory.IsHomLift.of_fac' q _ _
    (restrictionFiberObj T iΛ c d e).property d.base ?_
  rw [changeOfFieldRestriction_map]
  rfl

variable (D : PredeformationConstruction iΛ q x₀ hx₀)
variable (E : PredeformationConstruction iΛ q xₗ hxₗ)

/-- The category structure on the carrier of `D`. -/
local instance : Category.{max u w} D.carrier := D.category
/-- The category structure on the carrier of `E`. -/
local instance : Category.{max u w} E.carrier := E.category

/-- The identification of the base of a deformation with a comparison algebra, unfolded. -/
theorem changeOfFieldIso_eq (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    changeOfFieldIso T iΛ D a =
      eqToHom (D.object_projection a.fst).symm ≫ a.iso.hom := rfl

/-- The identification of the base of a deformation with a comparison algebra is an
isomorphism. -/
instance isIso_changeOfFieldIso (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    IsIso (changeOfFieldIso T iΛ D a) := by
  rw [changeOfFieldIso_eq]
  infer_instance

/-- **Where (RS) enters.** Condition (RS), applied to the change-of-field square of `l`, `C`,
`k` and `A ≅ C ×_l k`: that square is a pushout along a closed immersion of finite-type local
Artinian schemes over `S`, so the comparison of fibres is an equivalence. -/
theorem changeOfFieldSquare_comparison_isEquivalence
    (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) [IsIso e] :
    (fiberSquareComparison q c (specFieldExtensionMap T iΛ) (specResidueFieldMap T iΛ C)
      (specResidueBaseMap T iΛ A) (changeOfFieldBaseMap T iΛ e)
      (specResidueFieldMap_comp_changeOfFieldBaseMap T iΛ e).symm).IsEquivalence := by
  refine hRS (specResidueFieldMap T iΛ C) (specFieldExtensionMap T iΛ)
    (changeOfFieldBaseMap T iΛ e) (specResidueBaseMap T iΛ A)
    (specResidueFieldMap_comp_changeOfFieldBaseMap T iΛ e)
    (overIsArtinianLocal_spec T.l _) (overIsArtinianLocal_spec (C : Type u) _)
    (overIsArtinianLocal_spec T.k _) (overIsArtinianLocal_spec (A : Type u) _)
    ⟨hfinL, hqcL⟩ (spec_finiteType_of_residueField_point C iΛ hfinL hqcL)
    ⟨hfinK, hqcK⟩ (spec_finiteType_of_residueField_point A iΛ hfinK hqcK)
    (specResidueFieldMap_isClosedImmersion T iΛ C) (specChangeOfField_isPushout T iΛ e)

/-! #### Faithfulness -/

include hη in
/-- **Where (RS) enters, uniqueness.** The canonical functor of Tag 07WX is faithful when `𝒳`
satisfies (RS): the reversed arrow of a morphism of the change-of-fields category is determined
by its restrictions to `Spec C` and to `Spec k`. -/
public theorem changeOfFieldFunctor_faithful
    (hq : q.IsFiberedInGroupoids) (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    (changeOfFieldFunctor T iΛ hxₗ hη c D E).Faithful := by
  constructor
  intro a b f g hfg
  have h1 := changeOfFieldFunctor_morphisms T iΛ hxₗ hη c D E f
  have h2 := changeOfFieldFunctor_morphisms T iΛ hxₗ hη c D E g
  rw [hfg] at h1
  have ht := h1.symm.trans h2
  have hoa : (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a)).algebra = a.snd :=
    congrArg (fun z : DeformationObject iΛ q xₗ hxₗ => z.algebra)
      (changeOfFieldFunctor_objects T iΛ hxₗ hη c D E a)
  have hob : (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj b)).algebra = b.snd :=
    congrArg (fun z : DeformationObject iΛ q xₗ hxₗ => z.algebra)
      (changeOfFieldFunctor_objects T iΛ hxₗ hη c D E b)
  have hpa : (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a)).point =
      (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).val :=
    congrArg (fun z : DeformationObject iΛ q xₗ hxₗ => z.point)
      (changeOfFieldFunctor_objects T iΛ hxₗ hη c D E a)
  have hpb : (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj b)).point =
      (restrictionFiberObj T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)).val :=
    congrArg (fun z : DeformationObject iΛ q xₗ hxₗ => z.point)
      (changeOfFieldFunctor_objects T iΛ hxₗ hη c D E b)
  have hsnd : f.snd = g.snd := by
    have hr := congrArg
      (fun z : DeformationMorphism iΛ q xₗ hxₗ
        (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a))
        (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj b)) => z.ringHom) ht
    rw [transportDeformationMorphism_ringHom, transportDeformationMorphism_ringHom,
      changeOfFieldDeformationMorphism_ringHom, changeOfFieldDeformationMorphism_ringHom] at hr
    exact eq_of_conj_eq hoa hob hr
  have harr : changeOfFieldMorphismArrow T iΛ c D f =
      changeOfFieldMorphismArrow T iΛ c D g := by
    have hr := congrArg
      (fun z : DeformationMorphism iΛ q xₗ hxₗ
        (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a))
        (E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj b)) => z.arrow) ht
    rw [transportDeformationMorphism_arrow, transportDeformationMorphism_arrow,
      changeOfFieldDeformationMorphism_arrow, changeOfFieldDeformationMorphism_arrow] at hr
    exact eq_of_conj_eq hpb hpa hr
  have hring : (D.morphisms a.fst b.fst f.fst).ringHom =
      (D.morphisms a.fst b.fst g.fst).ringHom := by
    have hf := changeOfFieldIso_naturality T iΛ D f
    have hg := changeOfFieldIso_naturality T iΛ D g
    rw [hsnd] at hf
    exact (cancel_mono (changeOfFieldIso T iΛ D b)).mp (hf.trans hg.symm)
  have harrow : (D.morphisms a.fst b.fst f.fst).arrow =
      (D.morphisms a.fst b.fst g.fst).arrow := by
    have hEq := changeOfFieldSquare_comparison_isEquivalence T iΛ c hRS hfinK hqcK hfinL hqcL
      (changeOfFieldIso T iΛ D b)
    have hr : q.IsHomLift (specResidueBaseMap T iΛ (D.objects b.fst).algebra)
        (D.objects b.fst).arrow := deformationObject_arrow_isHomLift T iΛ (D.objects b.fst)
    have hs : q.IsHomLift (changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b))
        (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)) :=
      changeOfFieldRestriction_isHomLift T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)
    have hα : q.IsHomLift (algebraBaseMapSelf T iΛ (D.morphisms a.fst b.fst f.fst).ringHom ≫
        eqToHom (D.objects a.fst).base.symm) (D.morphisms a.fst b.fst f.fst).arrow :=
      deformationMorphism_arrow_isHomLift T iΛ (D.morphisms a.fst b.fst f.fst)
    have hβ : q.IsHomLift (algebraBaseMapSelf T iΛ (D.morphisms a.fst b.fst f.fst).ringHom ≫
        eqToHom (D.objects a.fst).base.symm) (D.morphisms a.fst b.fst g.fst).arrow := by
      rw [hring]
      exact deformationMorphism_arrow_isHomLift T iΛ (D.morphisms a.fst b.fst g.fst)
    refine fiberSquareComparison_arrow_ext q c (specFieldExtensionMap T iΛ)
      (specResidueFieldMap T iΛ b.snd)
      (specResidueBaseMap T iΛ (D.objects b.fst).algebra)
      (changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b))
      (specResidueFieldMap_comp_changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b)).symm
      hq (s := ⟨(D.objects b.fst).point, (D.objects b.fst).base⟩)
      (algebraBaseMapSelf T iΛ (D.morphisms a.fst b.fst f.fst).ringHom ≫
        eqToHom (D.objects a.fst).base.symm)
      ⟨x₀, hx₀⟩
      (restrictionFiberObj T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b))
      (D.objects b.fst).arrow
      (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)) ?_ ?_
    · rw [(D.morphisms a.fst b.fst f.fst).triangle, (D.morphisms a.fst b.fst g.fst).triangle]
    · rw [← changeOfFieldMorphismArrow_fac T iΛ c D f, ← changeOfFieldMorphismArrow_fac T iΛ c D g,
        harr]
  exact CategoricalPullback.hom_ext ((D.morphisms a.fst b.fst).injective
    (DeformationMorphism.ext_of_components (hr := hring) (ha := harrow))) hsnd

/-! #### Fullness -/

include hη in
/-- **Where (RS) enters, existence.** The canonical functor of Tag 07WX is full when `𝒳`
satisfies (RS): a morphism of the restricted deformations is glued from its two restrictions to
a reversed arrow over the comparison algebra. -/
public theorem changeOfFieldFunctor_full
    (hq : q.IsFiberedInGroupoids) (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    (changeOfFieldFunctor T iΛ hxₗ hη c D E).Full := by
  constructor
  intro a b m
  have hoa := changeOfFieldFunctor_objects T iΛ hxₗ hη c D E a
  have hob := changeOfFieldFunctor_objects T iΛ hxₗ hη c D E b
  set M' := transportDeformationMorphism hoa.symm hob.symm
    (E.morphisms _ _ m)
  set fsnd : a.snd ⟶ b.snd := M'.ringHom
  set ρ : (D.objects a.fst).algebra ⟶ (D.objects b.fst).algebra :=
    changeOfFieldIso T iΛ D a ≫ (Deformation.comparisonFunctor T).functor.map fsnd ≫
      inv (changeOfFieldIso T iΛ D b) with hρdef
  have hρ : ρ ≫ changeOfFieldIso T iΛ D b =
      changeOfFieldIso T iΛ D a ≫ (Deformation.comparisonFunctor T).functor.map fsnd := by
    simp only [hρdef, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hEq := changeOfFieldSquare_comparison_isEquivalence T iΛ c hRS hfinK hqcK hfinL hqcL
    (changeOfFieldIso T iΛ D b)
  have hηlift : q.IsHomLift (specFieldExtensionMap T iΛ) η := eta_isHomLift T iΛ (hx₀ := hx₀) hxₗ hη
  have hβ : q.IsHomLift (specResidueFieldMap T iΛ b.snd)
      (changeOfFieldArrow T iΛ hxₗ hη c (D.objects b.fst) (changeOfFieldIso T iΛ D b)) :=
    deformationObject_arrow_isHomLift_l T iΛ hxₗ
      (restrictionDeformation T iΛ hxₗ hη c (D.objects b.fst) (changeOfFieldIso T iΛ D b))
  have hr : q.IsHomLift (specResidueBaseMap T iΛ (D.objects b.fst).algebra)
      (D.objects b.fst).arrow := deformationObject_arrow_isHomLift T iΛ (D.objects b.fst)
  have hs : q.IsHomLift (changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b))
      (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)) :=
    changeOfFieldRestriction_isHomLift T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)
  have hr' : q.IsHomLift (specResidueBaseMap T iΛ (D.objects b.fst).algebra ≫
      (algebraBaseMapSelf T iΛ ρ ≫ eqToHom (D.objects a.fst).base.symm))
      (D.objects a.fst).arrow := by
    rw [← Category.assoc, specResidueBaseMap_comp]
    exact deformationObject_arrow_isHomLift' T iΛ (D.objects a.fst)
  have hs' : q.IsHomLift (changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b) ≫
      (algebraBaseMapSelf T iΛ ρ ≫ eqToHom (D.objects a.fst).base.symm))
      (M'.arrow ≫ changeOfFieldRestriction T iΛ c (D.objects a.fst)
        (changeOfFieldIso T iΛ D a)) := by
    rw [← Category.assoc, changeOfFieldBaseMap_naturality T iΛ (changeOfFieldIso T iΛ D a)
      (changeOfFieldIso T iΛ D b) ρ fsnd hρ, Category.assoc]
    have h₁ : q.IsHomLift (algebraBaseMap T iΛ fsnd) M'.arrow :=
      deformationMorphism_arrow_isHomLift_l T iΛ hxₗ M'
    have h₂ : q.IsHomLift (changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst)
        (changeOfFieldIso T iΛ D a))
        (changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)) :=
      (changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
        (changeOfFieldIso T iΛ D a)).toIsHomLift
    exact CategoryTheory.IsHomLift.comp q (algebraBaseMap T iΛ fsnd)
      (changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst) (changeOfFieldIso T iΛ D a)) M'.arrow
      (changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
  have htri : changeOfFieldArrow T iΛ hxₗ hη c (D.objects b.fst)
        (changeOfFieldIso T iΛ D b) ≫ M'.arrow =
      changeOfFieldArrow T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a) := by
    have h := M'.triangle
    rwa [restrictionDeformation_arrow, restrictionDeformation_arrow] at h
  obtain ⟨γ, hγ, hγ₁, hγ₂⟩ := fiberSquareComparison_pointed_arrow_exists q c
    (specFieldExtensionMap T iΛ) (specResidueFieldMap T iΛ b.snd)
    (specResidueBaseMap T iΛ (D.objects b.fst).algebra)
    (changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b))
    (specResidueFieldMap_comp_changeOfFieldBaseMap T iΛ (changeOfFieldIso T iΛ D b)).symm
    hq (s := ⟨(D.objects b.fst).point, (D.objects b.fst).base⟩)
    (algebraBaseMapSelf T iΛ ρ ≫ eqToHom (D.objects a.fst).base.symm)
    ⟨xₗ, hxₗ⟩ ⟨x₀, hx₀⟩
    (restrictionFiberObj T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b))
    η (changeOfFieldArrow T iΛ hxₗ hη c (D.objects b.fst) (changeOfFieldIso T iΛ D b))
    (D.objects b.fst).arrow
    (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b))
    (D.objects a.fst).arrow
    (M'.arrow ≫ changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
    (changeOfFieldArrow_fac T iΛ hxₗ hη c (D.objects b.fst)
      (changeOfFieldIso T iΛ D b)).symm
    (by rw [← Category.assoc, htri,
      changeOfFieldArrow_fac T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a)])
  set mD : DeformationMorphism iΛ q x₀ hx₀ (D.objects a.fst) (D.objects b.fst) :=
    { ringHom := ρ
      arrow := γ
      triangle := hγ₁
      arrow_base := by
        rw [CategoryTheory.IsHomLift.fac' q (algebraBaseMapSelf T iΛ ρ ≫
          eqToHom (D.objects a.fst).base.symm) γ]
        simp only [Over.comp_left, Over.eqToHom_left, algebraBaseMapSelf_left, Category.assoc,
          eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp,
          eqToHom_trans_assoc] }
  set ffst : a.fst ⟶ b.fst := (D.morphisms a.fst b.fst).symm mD
  have hffst : D.morphisms a.fst b.fst ffst = mD :=
    (D.morphisms a.fst b.fst).apply_symm_apply mD
  have hw : D.projection.map ffst ≫ b.iso.hom =
      a.iso.hom ≫ (Deformation.comparisonFunctor T).functor.map fsnd := by
    have hmp : ρ = eqToHom (D.object_projection a.fst).symm ≫
        D.projection.map ffst ≫ eqToHom (D.object_projection b.fst) := by
      have h := D.morphism_projection ffst
      rw [hffst] at h
      exact h.symm
    rw [hmp, changeOfFieldIso_eq, changeOfFieldIso_eq] at hρ
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hρ
    exact (cancel_epi (eqToHom (D.object_projection a.fst).symm)).mp hρ
  set f : a ⟶ b := ⟨ffst, fsnd, hw⟩
  refine ⟨f, (E.morphisms _ _).injective ?_⟩
  rw [changeOfFieldFunctor_morphisms]
  have hM : transportDeformationMorphism hoa hob M' = E.morphisms _ _ m :=
    transportDeformationMorphism_symm hoa.symm hob.symm (E.morphisms _ _ m)
  rw [← hM]
  refine congrArg (fun z => transportDeformationMorphism hoa hob z) ?_
  refine DeformationMorphism.ext_of_components (hr := rfl) (ha := ?_)
  rw [changeOfFieldDeformationMorphism_arrow]
  have h₁ : q.IsHomLift (algebraBaseMap T iΛ fsnd)
      (changeOfFieldMorphismArrow T iΛ c D f) := by
    refine CategoryTheory.IsHomLift.of_fac' q _ _
      (restrictionFiberObj T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)).property
      (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).property
      (changeOfFieldMorphismArrow_map T iΛ c D f)
  have h₂ : q.IsHomLift (algebraBaseMap T iΛ fsnd) M'.arrow :=
    deformationMorphism_arrow_isHomLift_l T iΛ hxₗ M'
  have h₃ := changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
    (changeOfFieldIso T iΛ D a)
  refine Functor.IsStronglyCartesian.ext q
    (changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst) (changeOfFieldIso T iΛ D a))
    (changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
    (algebraBaseMap T iΛ fsnd) ?_
  rw [changeOfFieldMorphismArrow_fac]
  change _ ≫ (D.morphisms a.fst b.fst ffst).arrow = _
  rw [hffst, ← hγ₂]

/-! #### Essential surjectivity -/

/-- Postcomposing the base morphism of a lift with an equality of objects again gives a
lift. -/
theorem isHomLift_comp_eqToHom {A B : X} {R R' R'' : Over S} (f : R ⟶ R') (φ : A ⟶ B)
    (hf : q.IsHomLift f φ) (h : R' = R'') (hB : q.obj B = R'') :
    q.IsHomLift (f ≫ eqToHom h) φ := by
  have := hf
  refine CategoryTheory.IsHomLift.of_fac' q _ _
    (CategoryTheory.IsHomLift.domain_eq q f φ) hB ?_
  rw [CategoryTheory.IsHomLift.fac' q f φ]
  subst h
  simp only [eqToHom_refl, Category.comp_id]

include hη in
/-- **Where (RS) enters, gluing.** A deformation of `x_{l,0}` over `C` is the restriction of a
deformation of `x₀` over the comparison algebra `C ×_l k`: condition (RS) glues it with `x₀`
along `x_{l,0}`. -/
theorem exists_deformation_glue
    (hq : q.IsFiberedInGroupoids) (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (ee : DeformationObject iΛ q xₗ hxₗ) :
    ∃ (d : DeformationObject iΛ q x₀ hx₀)
      (hA : d.algebra = (Deformation.comparisonFunctor T).functor.obj ee.algebra)
      (δ : ee.point ⟶ d.point),
      q.IsHomLift (changeOfFieldRestrictionBaseMap T iΛ d (eqToHom hA)) δ ∧
        ee.arrow ≫ δ = η ≫ d.arrow := by
  have hEq := changeOfFieldSquare_comparison_isEquivalence T iΛ c hRS hfinK hqcK hfinL hqcL
    (𝟙 ((Deformation.comparisonFunctor T).functor.obj ee.algebra))
  have hηlift : q.IsHomLift (specFieldExtensionMap T iΛ) η :=
    eta_isHomLift T iΛ (hx₀ := hx₀) hxₗ hη
  have hβ : q.IsHomLift (specResidueFieldMap T iΛ ee.algebra) ee.arrow :=
    deformationObject_arrow_isHomLift_l T iΛ hxₗ ee
  obtain ⟨s, γ, δ, hγ, hδ, hglue⟩ := fiberSquareComparison_glue q c
    (specFieldExtensionMap T iΛ) (specResidueFieldMap T iΛ ee.algebra)
    (specResidueBaseMap T iΛ ((Deformation.comparisonFunctor T).functor.obj ee.algebra))
    (changeOfFieldBaseMap T iΛ
      (𝟙 ((Deformation.comparisonFunctor T).functor.obj ee.algebra)))
    (specResidueFieldMap_comp_changeOfFieldBaseMap T iΛ
      (𝟙 ((Deformation.comparisonFunctor T).functor.obj ee.algebra))).symm
    hq ⟨xₗ, hxₗ⟩ ⟨x₀, hx₀⟩ ⟨ee.point, ee.base⟩ η ee.arrow
  refine ⟨{ algebra := (Deformation.comparisonFunctor T).functor.obj ee.algebra
            point := s.val
            arrow := γ
            base := s.property
            arrow_base := ?_ }, rfl, δ, ?_, hglue.symm⟩
  · have := hγ
    rw [CategoryTheory.IsHomLift.fac' q
      (specResidueBaseMap T iΛ ((Deformation.comparisonFunctor T).functor.obj ee.algebra)) γ]
    simp only [Over.comp_left, Over.eqToHom_left, specResidueBaseMap_left, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans, Category.comp_id]
  · exact isHomLift_comp_eqToHom _ δ hδ s.property.symm rfl

/-- Reading off that a conjugated morphism is an identity. -/
theorem conj_eq_id_of_eq {C : Type*} [Category C] {W Z Y : C}
    (hW : W = Y) (hZ : Z = Y) {f : W ⟶ Z}
    (h : f = eqToHom hW ≫ eqToHom hZ.symm) :
    eqToHom hW.symm ≫ f ≫ eqToHom hZ = 𝟙 Y := by
  subst hW
  subst hZ
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- The reversed arrow underlying a morphism of a fibre of `q` lies over the identity of the
base object of that fibre. -/
theorem fiberHom_arrow_base {Zobj : Over S} {s t : q.Fiber Zobj} (m : s ⟶ t) :
    eqToHom (congrArg Over.left s.property).symm ≫ (q.map m.1).left ≫
        eqToHom (congrArg Over.left t.property) = 𝟙 Zobj.left := by
  have := m.property
  have hfac : q.map m.1 = eqToHom s.property ≫ eqToHom t.property.symm := by
    rw [CategoryTheory.IsHomLift.fac' q (𝟙 Zobj) m.1]
    simp only [Category.id_comp]
  have hfacleft : (q.map m.1).left =
      eqToHom (congrArg Over.left s.property) ≫
        eqToHom (congrArg Over.left t.property).symm := by
    rw [hfac, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
  exact conj_eq_id_of_eq _ _ hfacleft

/-- The spectrum of the identity of an object of `𝒞_{Λ,l}` is the identity. -/
theorem specMap_id_ringHom (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.Hom.hom (𝟙 C)).toRingHom) =
      𝟙 (Spec (CommRingCat.of (C : Type u))) := by
  change Spec.map (CommRingCat.ofHom (RingHom.id C)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- Postcomposing a lift with a morphism of a fibre again gives a lift of the same base
morphism. -/
theorem isHomLift_comp_fiberHom {Zobj : Over S} {A : X} {s t : q.Fiber Zobj}
    {R : Over S} (f : R ⟶ Zobj) (φ : A ⟶ s.val) (hφ : q.IsHomLift f φ) (m : s ⟶ t) :
    q.IsHomLift f (φ ≫ m.1) := by
  have := hφ
  have := m.property
  exact CategoryTheory.IsHomLift.comp_lift_id_right' q f φ Zobj m.1

include hη in
/-- A deformation of `x_{l,0}` mapping to a deformation of `x₀` over the base map of a change
of field, compatibly with the two distinguished arrows, is isomorphic to the restriction of
that deformation: the restricting arrow and the given arrow are two cartesian lifts of one and
the same arrow of `Over S`. -/
theorem exists_isIso_restrictionDeformation
    (hq : q.IsFiberedInGroupoids) (d : DeformationObject iΛ q x₀ hx₀)
    (ee : DeformationObject iΛ q xₗ hxₗ)
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj ee.algebra)
    (δ : ee.point ⟶ d.point) (hδ : q.IsHomLift (changeOfFieldRestrictionBaseMap T iΛ d e) δ)
    (hcomm : ee.arrow ≫ δ = η ≫ d.arrow) :
    ∃ (mm : DeformationMorphism iΛ q xₗ hxₗ
        (restrictionDeformation T iΛ hxₗ hη c d e) ee)
      (nn : DeformationMorphism iΛ q xₗ hxₗ ee
        (restrictionDeformation T iΛ hxₗ hη c d e)),
      mm.ringHom ≫ nn.ringHom = 𝟙 ee.algebra ∧
        nn.ringHom ≫ mm.ringHom = 𝟙 ee.algebra ∧
        nn.arrow ≫ mm.arrow = 𝟙 (restrictionFiberObj T iΛ c d e).val ∧
        mm.arrow ≫ nn.arrow = 𝟙 ee.point := by
  have := hδ
  have := hq.isStronglyCartesian_homLift (changeOfFieldRestrictionBaseMap T iΛ d e) δ
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  let zz : q.Fiber (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ ee.algebra)) ≫ iΛ) : Over S) :=
    ⟨ee.point, ee.base⟩
  obtain ⟨eiso, hνR, hν'δ⟩ := exists_fiberIso_fac q hq (changeOfFieldRestrictionBaseMap T iΛ d e)
    (z := zz) (z' := restrictionFiberObj T iΛ c d e) δ (changeOfFieldRestriction T iΛ c d e)
  change eiso.hom.1 ≫ _ = _ at hνR
  change eiso.inv.1 ≫ _ = _ at hν'δ
  have hν : q.IsHomLift (𝟙 (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ ee.algebra)) ≫ iΛ) : Over S))
      (eiso.hom.1) := eiso.hom.property
  have hν' : q.IsHomLift (𝟙 (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ ee.algebra)) ≫ iΛ) : Over S))
      (eiso.inv.1) := eiso.inv.property
  have harr : q.IsHomLift (specResidueFieldMap T iΛ ee.algebra)
      (changeOfFieldArrow T iΛ hxₗ hη c d e) :=
    deformationObject_arrow_isHomLift_l T iΛ hxₗ (restrictionDeformation T iΛ hxₗ hη c d e)
  have hee : q.IsHomLift (specResidueFieldMap T iΛ ee.algebra) ee.arrow :=
    deformationObject_arrow_isHomLift_l T iΛ hxₗ ee
  refine ⟨{ ringHom := 𝟙 ee.algebra
            arrow := eiso.hom.1
            triangle := ?_
            arrow_base := ?_ },
          { ringHom := 𝟙 ee.algebra
            arrow := eiso.inv.1
            triangle := ?_
            arrow_base := ?_ }, Category.comp_id _, Category.comp_id _, ?_, ?_⟩
  · rw [restrictionDeformation_arrow]
    have : q.IsHomLift (specResidueFieldMap T iΛ ee.algebra)
        (ee.arrow ≫ eiso.hom.1) :=
      isHomLift_comp_fiberHom (specResidueFieldMap T iΛ ee.algebra) ee.arrow hee eiso.hom
    refine Functor.IsStronglyCartesian.ext q (changeOfFieldRestrictionBaseMap T iΛ d e)
      (changeOfFieldRestriction T iΛ c d e) (specResidueFieldMap T iΛ ee.algebra) ?_
    rw [Category.assoc, hνR, hcomm, changeOfFieldArrow_fac]
  · exact (fiberHom_arrow_base eiso.hom).trans (specMap_id_ringHom T ee.algebra).symm
  · rw [restrictionDeformation_arrow]
    have : q.IsHomLift (specResidueFieldMap T iΛ ee.algebra)
        (changeOfFieldArrow T iΛ hxₗ hη c d e ≫
          eiso.inv.1) :=
      isHomLift_comp_fiberHom (specResidueFieldMap T iΛ ee.algebra)
        (changeOfFieldArrow T iΛ hxₗ hη c d e) harr eiso.inv
    refine Functor.IsStronglyCartesian.ext q (changeOfFieldRestrictionBaseMap T iΛ d e) δ
      (specResidueFieldMap T iΛ ee.algebra) ?_
    rw [Category.assoc, hν'δ, changeOfFieldArrow_fac, hcomm]
  · exact (fiberHom_arrow_base eiso.inv).trans (specMap_id_ringHom T ee.algebra).symm
  · exact congrArg (fun z : restrictionFiberObj T iΛ c d e ⟶
      restrictionFiberObj T iΛ c d e => z.1) eiso.inv_hom_id
  · exact congrArg (fun z : zz ⟶ zz => z.1) eiso.hom_inv_id

include hη in
/-- **Where (RS) enters, essential surjectivity.** The canonical functor of Tag 07WX is
essentially surjective when `𝒳` satisfies (RS). -/
public theorem changeOfFieldFunctor_essSurj
    (hq : q.IsFiberedInGroupoids) (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    (changeOfFieldFunctor T iΛ hxₗ hη c D E).EssSurj := by
  constructor
  intro t
  obtain ⟨d, hA, δ, hδ, hglue⟩ := exists_deformation_glue T iΛ hxₗ hη c hq hRS
    hfinK hqcK hfinL hqcL (E.objects t)
  obtain ⟨a₀, ha₀⟩ := D.objects.surjective d
  subst ha₀
  let a : Deformation.ChangeOfFieldsCategory T D.projection :=
    ⟨a₀, (E.objects t).algebra, eqToIso ((D.object_projection a₀).trans hA)⟩
  have hcfi : changeOfFieldIso T iΛ D a = eqToHom hA := by
    rw [changeOfFieldIso_eq]
    change eqToHom (D.object_projection a₀).symm ≫
      eqToHom ((D.object_projection a₀).trans hA) = _
    rw [eqToHom_trans]
  rw [← hcfi] at hδ
  obtain ⟨mm, nn, h₁, h₂, h₃, h₄⟩ := exists_isIso_restrictionDeformation T iΛ hxₗ hη c hq
    (D.objects a.fst) (E.objects t) (changeOfFieldIso T iΛ D a) δ hδ hglue
  have hoa : E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a) =
      restrictionDeformation T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a) :=
    changeOfFieldFunctor_objects T iΛ hxₗ hη c D E a
  have h₁' : ∀ {Y : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
      (v : (E.objects t).algebra ⟶ Y), mm.ringHom ≫ nn.ringHom ≫ v = v := by
    intro Y v
    rw [← Category.assoc, h₁]
    exact Category.id_comp v
  have h₃' : ∀ {y : X}
      (v : (restrictionFiberObj T iΛ c (D.objects a.fst)
        (changeOfFieldIso T iΛ D a)).val ⟶ y), nn.arrow ≫ mm.arrow ≫ v = v := by
    intro y v
    rw [← Category.assoc, h₃]
    exact Category.id_comp v
  refine ⟨a, ⟨⟨(E.morphisms _ _).symm
      (transportDeformationMorphism hoa rfl mm),
    (E.morphisms _ _).symm (transportDeformationMorphism rfl hoa nn), ?_, ?_⟩⟩⟩
  · refine (E.morphisms _ _).injective (DeformationMorphism.ext_of_components (hr := ?_) (ha := ?_))
    · rw [predeformationMorphism_ringHom_comp, predeformationMorphism_ringHom_id,
        (E.morphisms _ _).apply_symm_apply, (E.morphisms _ _).apply_symm_apply,
        transportDeformationMorphism_ringHom, transportDeformationMorphism_ringHom]
      simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        h₁', eqToHom_trans]
    · rw [E.reversed_composition, E.reversed_identity,
        (E.morphisms _ _).apply_symm_apply, (E.morphisms _ _).apply_symm_apply,
        transportDeformationMorphism_arrow, transportDeformationMorphism_arrow]
      simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        h₃', eqToHom_trans]
  · refine (E.morphisms _ _).injective (DeformationMorphism.ext_of_components (hr := ?_) (ha := ?_))
    · rw [predeformationMorphism_ringHom_comp, predeformationMorphism_ringHom_id,
        (E.morphisms _ _).apply_symm_apply, (E.morphisms _ _).apply_symm_apply,
        transportDeformationMorphism_ringHom, transportDeformationMorphism_ringHom]
      simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        h₂, eqToHom_trans_assoc]
    · rw [E.reversed_composition, E.reversed_identity,
        (E.morphisms _ _).apply_symm_apply, (E.morphisms _ _).apply_symm_apply,
        transportDeformationMorphism_arrow, transportDeformationMorphism_arrow]
      simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        h₄, eqToHom_trans_assoc]

/-! #### The equivalence -/

include hη in
/-- **Stacks Project, Tag 07WX.** The canonical functor
`(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` of Tag 07WX is an equivalence when `𝒳` satisfies the
Rim–Schlessinger condition (RS). -/
@[stacks 07WX "the functor is an equivalence under (RS); the ambient base category is the \
category of all S-schemes rather than the big fppf site, and (RS) is taken in the matching \
form over that category"]
public theorem changeOfFieldFunctor_isEquivalence
    (hq : q.IsFiberedInGroupoids) (hRS : SatisfiesRSOver q c)
    (hfinK : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hqcK : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hfinL : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hqcL : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    (changeOfFieldFunctor T iΛ hxₗ hη c D E).IsEquivalence where
  faithful := changeOfFieldFunctor_faithful T iΛ hxₗ hη c D E hq hRS hfinK hqcK hfinL hqcL
  full := changeOfFieldFunctor_full T iΛ hxₗ hη c D E hq hRS hfinK hqcK hfinL hqcL
  essSurj := changeOfFieldFunctor_essSurj T iΛ hxₗ hη c D E hq hRS hfinK hqcK hfinL hqcL

end Equivalence

end Deformation.Artin

end
