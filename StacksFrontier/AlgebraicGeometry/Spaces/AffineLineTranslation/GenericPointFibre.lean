module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic

/-!
# The generic point of the quotient of the affine line by the integer translations

Let `k` be a field of characteristic zero, let `X = 𝔸¹_k/ℤ` be the fppf sheaf quotient of the
affine line by the translation action of the integers, and let
`γ : Spec k(x) ⟶ X` be the image in `X` of the generic point of the line. This file computes
the self-fibre-product of `γ` and deduces that `γ` is not a monomorphism, which are the first
two assertions of Stacks 02Z7.

The engine is the identification of `Spec k(x) ×_{γ, X, γ} Spec k(x)` with the disjoint union
of one copy of `Spec k(x)` for every integer: the kernel pair of the projection
`𝔸¹_k ⟶ 𝔸¹_k/ℤ` is the graph relation of the action on the line, and that relation restricts
along the monomorphism `Spec k(x) ⟶ 𝔸¹_k` to the graph relation of the translation action of
the integers on `Spec k(x)`. Since the two projections of that relation differ — translation
by one is not the identity of `Spec k(x)` — `γ` cannot be a monomorphism.

## Main definitions

* `AlgebraicGeometry.AffineLineTranslation.genericPointTranslationAction` is the action of the
  integers on the generic point `Spec k(x)` by translating the indeterminate.
* `AlgebraicGeometry.AffineLineTranslation.genericQuotientMorphism` is the morphism
  `γ : Spec k(x) ⟶ 𝔸¹_k/ℤ`.

## Main results

* `AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields.of_equivariant`: condition
  `(*)` of Stacks 02Z2 descends along an equivariant morphism, because the residue field map
  of a morphism of schemes is a homomorphism of fields and hence injective. This is how the
  freeness of the translation action on `Spec k(x)` is read off from its freeness on `𝔸¹_k`.
* `AlgebraicGeometry.Space.actionRelation_rel_comp` and
  `AlgebraicGeometry.Space.actionRelation_rel_of_rel_comp`: the graph relation of a group
  action restricts along an equivariant monomorphism. The second direction decomposes the
  source into the clopen pieces lying over the summands of the relation scheme, using that a
  coproduct of schemes is a universal colimit.
* `Stacks.Groupoids.toQuotientSheaf_app_eq_iff_rel` is the kernel pair of the projection onto
  a quotient sheaf, read on arbitrary points of the presented `S`-scheme rather than on the
  chart.
* `AlgebraicGeometry.AffineLineTranslation.isPullback_genericQuotientMorphism` is the second
  assertion of Stacks 02Z7: `Spec k(x) ×_{γ, X, γ} Spec k(x) = ∐_{n ∈ ℤ} Spec k(x)`.
* `AlgebraicGeometry.AffineLineTranslation.not_mono_genericQuotientMorphism` is the first
  assertion of Stacks 02Z7: `γ` is not a monomorphism.

## Implementation notes

The fibre product is taken in the category of presheaves of types on the big fppf site over
`Spec k`, where it exists without any representability input, and the copies of `Spec k(x)`
are presented by `Stacks.Groupoids.points`, the functor of points of a `k`-scheme restricted
to the site. So no size hypothesis on the disjoint union is needed; only the first assertion,
which exhibits a nonidentity automorphism of a specific object of the site, asks that
`Spec k(x)` itself belong to the site.

The affine line appears throughout as
`AlgebraicGeometry.AffineLineTranslation.lineOver`, the `k`-scheme underlying the object of
the site which represents it, rather than as
`AlgebraicGeometry.AffineLineInvolution.affineLine`. The two are definitionally equal, but the
quotient-sheaf machinery states the quotient in the former spelling, and the graph relation is
a morphism into a binary product, whose instance argument blocks the conversion.

The third assertion of Stacks 02Z7 — that `γ` factors through no monomorphism from the
spectrum of a field — is
`AlgebraicGeometry.AffineLineTranslation.not_exists_mono_factorisation_genericQuotientPoint`
in `StacksFrontier/AlgebraicGeometry/Spaces/AffineLineTranslationNotDecent.lean`, beside the
statement of Stacks 03ID which it implies.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v w

namespace Stacks.Groupoids

/-- The canonical projection onto the quotient sheaf of a pre-relation identifies two points
which the pre-relation relates. This is
`Stacks.Groupoids.quotientChart_app_eq_of_rel` for points of the presented `S`-scheme which
need not come from the site. -/
theorem toQuotientSheaf_app_eq_of_rel {S : AlgebraicGeometry.Scheme.{u}} {C : Type v}
    [Category.{w} C] (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R U : Over S} (j : PreRelation R U) {T : C} {x y : F.obj T ⟶ U} (h : j.Rel x y) :
    (toQuotientSheaf J F j).app (op T) x = (toQuotientSheaf J F j).app (op T) y := by
  obtain ⟨r, hx, hy⟩ := h
  rw [← hx, ← hy]
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (sourceMap_toQuotientSheaf J F j) (op T)) r).symm

/-- **The kernel pair of the projection onto a quotient sheaf.** Two points of the presented
`S`-scheme of an object of the site have the same image in the quotient sheaf exactly when
they are related. This is `Stacks.Groupoids.quotientChart_app_eq_iff_rel` read on the
projection itself rather than on the chart, using that a fully faithful presenting functor
makes every morphism between presented objects come from the site. -/
theorem toQuotientSheaf_app_eq_iff_rel {S : AlgebraicGeometry.Scheme.{u}} {C : Type v}
    [Category.{u} C] (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    [J.WEqualsLocallyBijective (Type u)] (F : C ⥤ Over S) [F.Full] [F.Faithful]
    {R : Over S} {X : C} (j : PreRelation R (F.obj X)) [Mono j]
    (hj : IsPreEquivalenceRelation j) (hR : Presheaf.IsSheaf J (points F R))
    (hX : Presheaf.IsSheaf J (points F (F.obj X))) {T : C} (x y : F.obj T ⟶ F.obj X) :
    (toQuotientSheaf J F j).app (op T) x = (toQuotientSheaf J F j).app (op T) y ↔
      j.Rel x y := by
  have hx : F.map (F.preimage x) = x := F.map_preimage x
  have hy : F.map (F.preimage y) = y := F.map_preimage y
  refine ⟨fun h ↦ ?_, toQuotientSheaf_app_eq_of_rel J F j⟩
  have h' : (quotientChart J F X j).app (op T) (F.preimage x) =
      (quotientChart J F X j).app (op T) (F.preimage y) := by
    rwa [quotientChart_app, quotientChart_app, hx, hy]
  have hrel := (quotientChart_app_eq_iff_rel J F X j hj hR hX
    (F.preimage x) (F.preimage y)).1 h'
  rwa [hx, hy] at hrel

/-- The relation induced by a pre-relation on points is stable under restriction. -/
theorem rel_comp_left {S : AlgebraicGeometry.Scheme.{u}} {R U : Over S}
    (j : PreRelation R U) {T T' : Over S} (f : T' ⟶ T) {x y : T ⟶ U} (h : j.Rel x y) :
    j.Rel (f ≫ x) (f ≫ y) := by
  obtain ⟨r, hx, hy⟩ := h
  exact ⟨f ≫ r, by rw [Category.assoc, hx], by rw [Category.assoc, hy]⟩

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}}

/-- The freeness condition of Stacks 02Z2 descends along an equivariant morphism: if the
group acts nontrivially on the residue field at every fixed point of `U`, and `U'` carries a
compatible action together with an equivariant morphism to `U`, then the same holds on `U'`.
The residue field map of the equivariant morphism is a homomorphism of fields, hence
injective, so it detects the triviality of the action upstairs. -/
theorem ActsNontriviallyOnFixedResidueFields.of_equivariant {U U' : Over S} {G : Type v}
    [Group G] (a : G →* Aut U) (b : G →* Aut U') (m : U' ⟶ U)
    (hm : ∀ g : G, (b g).hom ≫ m = m ≫ (a g).hom)
    (ha : ActsNontriviallyOnFixedResidueFields U G a) :
    ActsNontriviallyOnFixedResidueFields U' G b := by
  intro g x hx hne hres
  have hmg : (b g).hom.left ≫ m.left = m.left ≫ (a g).hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, hm g]
  have he : ((b g).hom.left ≫ m.left).base x = (m.left ≫ (a g).hom.left).base x := by
    rw [hmg]
  have hpt : (a g).hom.left.base (m.left.base x) = m.left.base x :=
    he.symm.trans (congrArg m.left.base hx)
  refine ha g (m.left.base x) hpt hne ?_
  have hmono : Mono (m.left.residueFieldMap x) :=
    ConcreteCategory.mono_of_injective _ (m.left.residueFieldMap x).hom.injective
  have hcongr := Scheme.Hom.residueFieldMap_congr hmg x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp, hres,
    Scheme.Hom.residueFieldMap_congr' (f := m.left) hx] at hcongr
  have hcongr' : ((U.left.residueFieldCongr he).hom ≫
        (a g).hom.left.residueFieldMap (m.left.base x)) ≫ m.left.residueFieldMap x =
      (U.left.residueFieldCongr (congrArg m.left.base hx)).hom ≫
        m.left.residueFieldMap x :=
    (Category.assoc _ _ _).trans hcongr.symm
  have hcancel := (cancel_mono (m.left.residueFieldMap x)).mp hcongr'
  refine (cancel_epi (U.left.residueFieldCongr he).hom).mp ?_
  exact hcancel.trans (Scheme.residueFieldCongr_trans_hom U.left he hpt).symm

/-- The target map of the graph relation of a group action is the target of its pre-relation. -/
private theorem actionRelation_target {U : Over S} {G : Type v} [Group G] [Small.{u} G]
    (a : G →* Aut U) :
    (actionRelation U G a).target = actionRelationTarget U G a :=
  prod.lift_fst _ _

/-- The source map of the graph relation of a group action is the source of its pre-relation. -/
private theorem actionRelation_source {U : Over S} {G : Type v} [Group G] [Small.{u} G]
    (a : G →* Aut U) :
    (actionRelation U G a).source = actionRelationSource U G :=
  prod.lift_snd _ _

/-- An equivariant morphism carries the graph relation of the action upstairs into the graph
relation of the action downstairs: the two maps of the relation on `U'`, followed by the
morphism, are related. -/
theorem actionRelation_rel_comp {U U' : Over S} {G : Type v} [Group G] [Small.{u} G]
    (a : G →* Aut U) (b : G →* Aut U') (m : U' ⟶ U)
    (hm : ∀ g : G, (b g).hom ≫ m = m ≫ (a g).hom) :
    (actionRelation U G a).Rel (actionRelationTarget U' G b ≫ m)
      (actionRelationSource U' G ≫ m) := by
  refine ⟨Sigma.desc (fun g : G ↦ m ≫ Sigma.ι (fun _ : G ↦ U) g), ?_, ?_⟩
  · rw [actionRelation_target]
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    simp only [actionRelationTarget, Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc]
    rw [hm g]
  · rw [actionRelation_source]
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    simp only [actionRelationSource, Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc,
      Category.comp_id, Category.id_comp]

/-- **The graph relation of a group action restricts along an equivariant monomorphism.**
Two points of `U'` whose images in `U` are related by the graph relation of the action on
`U` are already related by the graph relation of the action on `U'`.

The witness upstairs is a morphism into the disjoint union of copies of `U` indexed by the
group; it decomposes the source into the clopen pieces lying over the summands, and on the
piece indexed by `g` the two points differ by the action of `g` because the monomorphism
intertwines the two actions. -/
theorem actionRelation_rel_of_rel_comp {U U' : Over S} {G : Type v} [Group G] [Small.{u} G]
    (a : G →* Aut U) (b : G →* Aut U') (m : U' ⟶ U) [Mono m]
    (hm : ∀ g : G, (b g).hom ≫ m = m ≫ (a g).hom)
    {W : Over S} {x y : W ⟶ U'}
    (h : (actionRelation U G a).Rel (x ≫ m) (y ≫ m)) :
    (actionRelation U' G b).Rel x y := by
  obtain ⟨r, hrt, hrs⟩ := h
  rw [actionRelation_target] at hrt
  rw [actionRelation_source] at hrs
  set Y : G → Over S := fun _ ↦ U with hY
  set c : Cofan Y := Cofan.mk (∐ Y) (Sigma.ι Y) with hc
  have hu : IsUniversalColimit c := isUniversalColimit_sigmaCofanOver Y
  have huι : ∀ g : G, c.inj g ≫ 𝟙 (∐ Y) = Sigma.ι Y g := fun g ↦ Category.comp_id _
  set e : (∐ fun g : G ↦ pullback r (Sigma.ι Y g)) ≅ pullback r (𝟙 (∐ Y)) :=
    coproductPullbackIso Y (Sigma.ι Y) c hu (𝟙 (∐ Y)) huι r with he
  set ε : (∐ fun g : G ↦ pullback r (Sigma.ι Y g)) ≅ W :=
    e ≪≫ (pullbackRightIdIso r).symm with hε
  have hεhom : ∀ g : G, Sigma.ι (fun g : G ↦ pullback r (Sigma.ι Y g)) g ≫ ε.hom =
      pullback.fst r (Sigma.ι Y g) := by
    intro g
    have h1 : ε.hom = e.hom ≫ pullback.fst r (𝟙 (∐ Y)) := by
      rw [hε, Iso.trans_hom, Iso.symm_hom, pullbackRightIdIso_inv]
    rw [h1, ← Category.assoc, Category.assoc]
    exact coproductPullbackIso_ι_fst Y (Sigma.ι Y) c hu (𝟙 (∐ Y)) huι r g
  -- On the piece indexed by `g` the two points differ by the action of `g`.
  have hpiece : ∀ g : G, pullback.fst r (Sigma.ι Y g) ≫ y ≫ (b g).hom =
      pullback.fst r (Sigma.ι Y g) ≫ x := by
    intro g
    refine (cancel_mono m).mp ?_
    have hcond : pullback.fst r (Sigma.ι Y g) ≫ r =
        pullback.snd r (Sigma.ι Y g) ≫ Sigma.ι Y g := pullback.condition
    have hsrc : pullback.fst r (Sigma.ι Y g) ≫ y ≫ m = pullback.snd r (Sigma.ι Y g) := by
      rw [← hrs, ← Category.assoc, hcond, Category.assoc]
      show pullback.snd r (Sigma.ι Y g) ≫ Sigma.ι Y g ≫
        Sigma.desc (fun _ : G ↦ 𝟙 U) = _
      rw [Sigma.ι_desc, Category.comp_id]
    have htgt : pullback.fst r (Sigma.ι Y g) ≫ x ≫ m =
        pullback.snd r (Sigma.ι Y g) ≫ (a g).hom := by
      rw [← hrt, ← Category.assoc, hcond, Category.assoc]
      show pullback.snd r (Sigma.ι Y g) ≫ Sigma.ι Y g ≫
        Sigma.desc (fun h : G ↦ (a h).hom) = _
      rw [Sigma.ι_desc]
    simp only [Category.assoc, hm g, reassoc_of% hsrc, htgt]
  refine ⟨ε.inv ≫ Sigma.desc (fun g : G ↦ pullback.fst r (Sigma.ι Y g) ≫ y ≫
    Sigma.ι (fun _ : G ↦ U') g), ?_, ?_⟩
  · rw [actionRelation_target, Category.assoc]
    refine (Iso.inv_comp_eq ε).mpr ?_
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Category.assoc]
    show pullback.fst r (Sigma.ι Y g) ≫ y ≫ Sigma.ι (fun _ : G ↦ U') g ≫
      Sigma.desc (fun h : G ↦ (b h).hom) = _
    rw [Sigma.ι_desc,
      ← Category.assoc (Sigma.ι (fun g : G ↦ pullback r (Sigma.ι Y g)) g) ε.hom x,
      hεhom g, hpiece g]
  · rw [actionRelation_source, Category.assoc]
    refine (Iso.inv_comp_eq ε).mpr ?_
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Category.assoc]
    show pullback.fst r (Sigma.ι Y g) ≫ y ≫ Sigma.ι (fun _ : G ↦ U') g ≫
      Sigma.desc (fun _ : G ↦ 𝟙 U') = _
    rw [Sigma.ι_desc, Category.comp_id,
      ← Category.assoc (Sigma.ι (fun g : G ↦ pullback r (Sigma.ι Y g)) g) ε.hom y,
      hεhom g]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.AffineLineTranslation

open AffineLineInvolution

variable (k : Type u) [Field k]

/-! ### The integer translations of the generic point -/

/-- Translating the indeterminate by a sum of integers is translating by one and then the
other. -/
theorem genericPointTranslationIso_add (p q : ℤ) :
    genericPointTranslationIso k (p + q) =
      (genericPointTranslationIso k q).trans (genericPointTranslationIso k p) := by
  refine Iso.ext (Over.OverMorphism.ext ?_)
  show (genericPointTranslationIso k (p + q)).hom.left =
    ((genericPointTranslationIso k q).hom ≫ (genericPointTranslationIso k p).hom).left
  rw [Over.comp_left, genericPointTranslationIso_left, genericPointTranslationIso_left,
    genericPointTranslationIso_left, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  ext z
  show RatFunc.laurent (((p + q : ℤ) : k)) z =
    (RatFunc.laurent ((q : ℤ) : k)) ((RatFunc.laurent ((p : ℤ) : k)) z)
  rw [RatFunc.laurent_laurent, show ((q : ℤ) : k) + ((p : ℤ) : k) = ((p + q : ℤ) : k) by
    push_cast; ring]

/-- The integers act on the generic point of the affine line over `k` by translating the
indeterminate. -/
def genericPointTranslationAction : Multiplicative ℤ →* Aut (genericPointOver k) :=
  MonoidHom.mk' (fun n ↦ genericPointTranslationIso k n.toAdd) fun p q ↦
    genericPointTranslationIso_add k p.toAdd q.toAdd

/-- The element `g` acts on the generic point by translation by `g.toAdd`. -/
@[simp]
theorem genericPointTranslationAction_apply (g : Multiplicative ℤ) :
    genericPointTranslationAction k g = genericPointTranslationIso k g.toAdd :=
  congrFun (MonoidHom.mk'_apply _ _) g

/-- The generic point map is a monomorphism of `k`-schemes. -/
instance mono_genericPointMap : Mono (genericPointMap k) := by
  have hleft : Mono (genericPointMap k).left := genericPointMap_mono k
  constructor
  intro X f g h
  exact Over.OverMorphism.ext
    ((cancel_mono (genericPointMap k).left).mp (congrArg Over.Hom.left h))

/-- The generic point map intertwines the translation action on the generic point with the
translation action on the affine line. -/
theorem genericPointMap_equivariant (g : Multiplicative ℤ) :
    (genericPointTranslationAction k g).hom ≫ genericPointMap k =
      genericPointMap k ≫ (translationAction k g).hom := by
  rw [genericPointTranslationAction_apply]
  exact genericPointMap_translation k g.toAdd

/-- In characteristic zero no nonzero integer translation of the indeterminate fixes the
generic point of the affine line together with the field of rational functions: the
corresponding statement for the affine line transports along the generic point map. -/
theorem genericPointTranslationAction_residueFieldFaithful [CharZero k] :
    Space.ActsNontriviallyOnFixedResidueFields (genericPointOver k) (Multiplicative ℤ)
      (genericPointTranslationAction k) :=
  Space.ActsNontriviallyOnFixedResidueFields.of_equivariant (translationAction k)
    (genericPointTranslationAction k) (genericPointMap k) (genericPointMap_equivariant k)
    (translationAction_residueFieldFaithful k)

/-- The graph relation of the integer translation action on the affine line over a field of
characteristic zero is an étale equivalence relation: in characteristic zero no nonidentity
translation fixes a point of the line together with the residue field there. -/
instance isEtaleEquivalenceRelation_translationActionRelation (k : Type u) [Field k]
    [CharZero k] :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k)) :=
  Space.actionRelation_isEtaleEquivalenceRelation _ _ _
    (translationAction_residueFieldFaithful k)

/-- The graph relation of the integer translation action on the generic point is an étale
equivalence relation. -/
instance isEtaleEquivalenceRelation_genericPointTranslationActionRelation [CharZero k] :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.actionRelation (genericPointOver k) (Multiplicative ℤ)
        (genericPointTranslationAction k)) :=
  Space.actionRelation_isEtaleEquivalenceRelation _ _ _
    (genericPointTranslationAction_residueFieldFaithful k)

/-! ### The generic point as a point of the quotient -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- The functor presenting a big fppf site over `Spec k` as a site of `k`-schemes. -/
abbrev siteOver : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) :=
  Over.post B.inclusion

/-- The affine line over `k`, spelled as the `k`-scheme underlying the object of the site
which represents it. This is the spelling in which the quotient-sheaf machinery states the
quotient `𝔸¹_k/ℤ`, so it is the one used throughout this section. -/
abbrev lineOver (hU : B.Contains (affineLine k).left) : Over (Spec (.of k)) :=
  Space.underlyingOver B hS (siteAffineLine k B hS hU)

/-- The graph relation of the integer translation action on the affine line over `k`. -/
abbrev translationActionRelation (hU : B.Contains (affineLine k).left) :
    PreRelation (Space.actionRelationScheme (lineOver k B hS hU) (Multiplicative ℤ))
      (lineOver k B hS hU) :=
  Space.actionRelation (lineOver k B hS hU) (Multiplicative ℤ) (translationAction k)

/-- The generic point of the affine line over `k`, in the spelling of
`AlgebraicGeometry.AffineLineTranslation.lineOver`. -/
abbrev genericPointMapOver (hU : B.Contains (affineLine k).left) :
    genericPointOver k ⟶ lineOver k B hS hU := genericPointMap k

/-- The generic point map, viewed as a morphism into `lineOver`, is a monomorphism. -/
instance mono_genericPointMapOver (hU : B.Contains (affineLine k).left) :
    Mono (genericPointMapOver k B hS hU) := mono_genericPointMap k

/-- In characteristic zero, the graph relation of the integer translation action on the affine
line over `k` is an étale equivalence relation. -/
instance isEtaleEquivalenceRelation_translationActionRelationOver [CharZero k]
    (hU : B.Contains (affineLine k).left) :
    IsEtaleEquivalenceRelation (translationActionRelation k B hS hU) :=
  Space.actionRelation_isEtaleEquivalenceRelation _ _ _
    (translationAction_residueFieldFaithful k)

/-- The generic point of the affine line over `k`, as a morphism `γ : Spec k(x) ⟶ X = 𝔸¹_k/ℤ`
of fppf sheaves over `Spec k`: the generic point of the line followed by the projection onto
the quotient. -/
@[stacks 02Z7 "the generic point of the quotient"]
def genericQuotientMorphism (hU : B.Contains (affineLine k).left) :
    points (siteOver k B hS) (genericPointOver k) ⟶ translationQuotient k B hS hU :=
  (siteOver k B hS).op.whiskerLeft (yoneda.map (genericPointMapOver k B hS hU)) ≫
    toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS) (siteOver k B hS)
      (translationActionRelation k B hS hU)

/-- The morphism `genericQuotientMorphism` sends a `T`-point `x` of the generic point to the
class in the quotient of the composite of `x` with the generic point map. -/
theorem genericQuotientMorphism_app (hU : B.Contains (affineLine k).left)
    (T : BigFppfOver B (Spec (.of k)) hS)
    (x : (siteOver k B hS).obj T ⟶ genericPointOver k) :
    (genericQuotientMorphism k B hS hU).app (op T) x =
      (toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hS) (siteOver k B hS)
        (translationActionRelation k B hS hU)).app (op T)
          (x ≫ genericPointMapOver k B hS hU) := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The map of points induced by a morphism `f : Y ⟶ Z` of `k`-schemes sends a `T`-point `x`
of `Y` to `x ≫ f`. -/
theorem pointsMap_app {Y Z : Over (Spec (.of k))} (f : Y ⟶ Z)
    (T : BigFppfOver B (Spec (.of k)) hS) (x : (siteOver k B hS).obj T ⟶ Y) :
    ((siteOver k B hS).op.whiskerLeft (yoneda.map f)).app (op T) x = x ≫ f := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The two projections of the graph relation of the translation action on the generic point
become related by the graph relation of the translation action on the affine line once
composed with the generic point map. -/
theorem rel_comp_genericPointMapOver (hU : B.Contains (affineLine k).left)
    {T : Over (Spec (.of k))}
    (A : T ⟶ Space.actionRelationScheme (genericPointOver k) (Multiplicative ℤ)) :
    (translationActionRelation k B hS hU).Rel
      ((A ≫ Space.actionRelationTarget (genericPointOver k) (Multiplicative ℤ)
        (genericPointTranslationAction k)) ≫ genericPointMapOver k B hS hU)
      ((A ≫ Space.actionRelationSource (genericPointOver k) (Multiplicative ℤ)) ≫
        genericPointMapOver k B hS hU) := by
  simpa only [Category.assoc] using rel_comp_left _ A
    (Space.actionRelation_rel_comp (U := lineOver k B hS hU) (translationAction k)
      (genericPointTranslationAction k) (genericPointMapOver k B hS hU)
      (genericPointMap_equivariant k))

/-- **Stacks 02Z7, the self-fibre-product of the generic point.** The fibre product
`Spec k(x) ×_{γ, X, γ} Spec k(x)` over `X = 𝔸¹_k/ℤ` is the disjoint union of one copy of
`Spec k(x)` for every integer: it is the graph relation of the translation action of `ℤ` on
`Spec k(x)`, whose two projections send the summand indexed by `n` to the translate of the
generic point by `n` and to the generic point itself.

The kernel pair of the projection `𝔸¹_k ⟶ 𝔸¹_k/ℤ` is the graph relation of the action on the
line — this is Stacks 0265 in the form
`Stacks.Groupoids.quotientChart_app_eq_iff_rel` — and that relation restricts along the
monomorphism `Spec k(x) ⟶ 𝔸¹_k` to the graph relation of the action on `Spec k(x)`. -/
@[stacks 02Z7 "the self-fibre-product of the generic point"]
theorem isPullback_genericQuotientMorphism [CharZero k]
    (hU : B.Contains (affineLine k).left) :
    IsPullback
      ((siteOver k B hS).op.whiskerLeft (yoneda.map
        (Space.actionRelationTarget (genericPointOver k) (Multiplicative ℤ)
          (genericPointTranslationAction k))))
      ((siteOver k B hS).op.whiskerLeft (yoneda.map
        (Space.actionRelationSource (genericPointOver k) (Multiplicative ℤ))))
      (genericQuotientMorphism k B hS hU) (genericQuotientMorphism k B hS hU) := by
  classical
  have : (siteOver k B hS).Full :=
    inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  have : (siteOver k B hS).Faithful :=
    inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  have : Mono (translationActionRelation k B hS hU) :=
    mono_of_isEtaleEquivalenceRelation _
  have : Mono (Space.actionRelation (genericPointOver k) (Multiplicative ℤ)
      (genericPointTranslationAction k)) := mono_of_isEtaleEquivalenceRelation _
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  obtain ⟨T⟩ := T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine ConcreteCategory.hom_ext _ _ fun A ↦ ?_
    simp only [types_comp_apply, pointsMap_app, genericQuotientMorphism_app]
    exact toQuotientSheaf_app_eq_of_rel _ _ _ (rel_comp_genericPointMapOver k B hS hU A)
  · rintro A A' ⟨h₁, h₂⟩
    refine PreRelation.ext_of_target_of_source
      (Space.actionRelation (genericPointOver k) (Multiplicative ℤ)
        (genericPointTranslationAction k)) ?_ ?_
    · rw [Space.actionRelation_target]
      simpa only [pointsMap_app] using h₁
    · rw [Space.actionRelation_source]
      simpa only [pointsMap_app] using h₂
  · intro x₂ x₃ h
    have hiff := toQuotientSheaf_app_eq_iff_rel
      (BigFppfOver.topology B (Spec (.of k)) hS) (siteOver k B hS)
      (X := siteAffineLine k B hS hU) (translationActionRelation k B hS hU)
      (isPreEquivalenceRelation_of_isEtaleEquivalenceRelation _)
      (isSheaf_points B (Spec (.of k)) hS _) (isSheaf_points B (Spec (.of k)) hS _)
      (x₂ ≫ genericPointMapOver k B hS hU) (x₃ ≫ genericPointMapOver k B hS hU)
    have hrelm := hiff.1 (by simpa only [genericQuotientMorphism_app] using h)
    obtain ⟨r, hr₁, hr₂⟩ := Space.actionRelation_rel_of_rel_comp (U := lineOver k B hS hU)
      (translationAction k) (genericPointTranslationAction k) (genericPointMapOver k B hS hU)
      (genericPointMap_equivariant k) hrelm
    rw [Space.actionRelation_target] at hr₁
    rw [Space.actionRelation_source] at hr₂
    exact ⟨r, by simpa only [pointsMap_app] using hr₁,
      by simpa only [pointsMap_app] using hr₂⟩

/-- Translating the indeterminate of `k(x)` by one is not the identity automorphism of the
generic point: the indeterminate goes to `x + 1`. -/
theorem genericPointTranslationAction_one_ne_one :
    (genericPointTranslationAction k (Multiplicative.ofAdd (1 : ℤ))).hom ≠
      𝟙 (genericPointOver k) := by
  intro h
  have h' : (genericPointTranslationIso k 1).hom = 𝟙 (genericPointOver k) := by
    rw [← h, genericPointTranslationAction_apply]
    rfl
  have hleft : Spec.map (CommRingCat.ofHom (RatFunc.laurent (((1 : ℤ) : k))).toRingHom) =
      Spec.map (𝟙 (CommRingCat.of (RatFunc k))) := by
    rw [Spec.map_id, ← genericPointTranslationIso_left]
    simpa using congrArg Over.Hom.left h'
  have hring := congrArg
    (fun φ : CommRingCat.of (RatFunc k) ⟶ CommRingCat.of (RatFunc k) ↦ φ.hom RatFunc.X)
    (Spec.map_inj.mp hleft)
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply] at hring
  rw [show ((RatFunc.laurent (((1 : ℤ) : k))).toRingHom RatFunc.X) = RatFunc.X + 1 by
    simp] at hring
  simp at hring

/-- **Stacks 02Z7, part 1.** The generic point `γ : Spec k(x) ⟶ 𝔸¹_k/ℤ` is *not* a
monomorphism: translating the indeterminate by one is a nonidentity automorphism of
`Spec k(x)` which `γ` does not separate, because the translation is identified with the
identity in the quotient. It is the summand indexed by `1` of the self-fibre-product computed
in `AlgebraicGeometry.AffineLineTranslation.isPullback_genericQuotientMorphism` on which the
two projections differ. -/
@[stacks 02Z7 "gamma is not a monomorphism"]
theorem not_mono_genericQuotientMorphism [CharZero k]
    (hU : B.Contains (affineLine k).left) (hG : B.Contains (Spec (.of (RatFunc k)))) :
    ¬ Mono (genericQuotientMorphism k B hS hU) := by
  intro hmono
  set GP : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨(genericPointOver k).hom⟩ : B.obj hG ⟶ B.obj hS)
  have hrelone := rel_comp_genericPointMapOver k B hS hU
    (Sigma.ι (fun _ : Multiplicative ℤ ↦ genericPointOver k) (Multiplicative.ofAdd (1 : ℤ)))
  simp only [Space.actionRelationTarget, Space.actionRelationSource, Sigma.ι_desc] at hrelone
  let pt₁ : (points (siteOver k B hS) (genericPointOver k)).obj (op GP) :=
    (genericPointTranslationAction k (Multiplicative.ofAdd (1 : ℤ))).hom
  let pt₂ : (points (siteOver k B hS) (genericPointOver k)).obj (op GP) :=
    𝟙 (genericPointOver k)
  have hvalue : (genericQuotientMorphism k B hS hU).app (op GP) pt₁ =
      (genericQuotientMorphism k B hS hU).app (op GP) pt₂ :=
    (genericQuotientMorphism_app k B hS hU GP pt₁).trans
      ((toQuotientSheaf_app_eq_of_rel _ _ _ hrelone).trans
        (genericQuotientMorphism_app k B hS hU GP pt₂).symm)
  have hcomp : yonedaEquiv.symm pt₁ ≫ genericQuotientMorphism k B hS hU =
      yonedaEquiv.symm pt₂ ≫ genericQuotientMorphism k B hS hU := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hvalue
  exact genericPointTranslationAction_one_ne_one k
    (yonedaEquiv.symm.injective ((cancel_mono _).mp hcomp))

end AlgebraicGeometry.AffineLineTranslation

end
