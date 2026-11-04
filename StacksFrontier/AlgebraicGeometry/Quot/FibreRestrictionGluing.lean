module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperPushoutGluing

/-!
# Restriction across a pushout is an equivalence once objects glue

Let
```
T  ⟶ T'
↓     ↓
S  ⟶ S'
```
be a commutative square of schemes of the big fppf site and let `R` be a family of properties of
the slices of algebraic spaces over these schemes, stable under base change. This file gives a
criterion, in terms of pushouts and pullbacks of algebraic spaces only, for the canonical
restriction functor `AlgebraicGeometry.Space.fibrePushoutRestriction` from the fibre over `S'` to
the compatible pairs over `S` and `T'` to be an equivalence:

* every object `W` of the fibre over `S'` is the pushout, as an algebraic space, of its base
  changes `W_S ⟵ W_T ⟶ W_{T'}` to the three other corners; and
* every compatible pair `(V, U', φ)` over `S` and `T'` is glued by some object `P` of the fibre
  over `S'`: there are cartesian squares exhibiting `V` as `P ×_{S'} S` and `U'` as
  `P ×_{S'} T'`, through which `φ` becomes the identity of `P ×_{S'} T`.

The first condition makes restriction fully faithful, the second makes it essentially
surjective. This is the bookkeeping that turns the gluing statements of Stacks 07W3 — the
counit `G(F(W')) ⟶ W'` is an isomorphism for flat `W'`, and a glued triple `G(V, U', φ)` is
recovered by base change and is flat and locally of finite presentation when its pieces are —
into the equivalence of fibre categories `AlgebraicGeometry.Space.FlatLfpPushoutRS` that the
statement of Stacks 0D1J is reduced to.

## Main results

* `AlgebraicGeometry.Space.fibreRestriction_faithful_of_isPushout` and
  `AlgebraicGeometry.Space.fibreRestriction_full_of_isPushout`: restriction is fully faithful
  when every object over `S'` is the pushout of its base changes.
* `AlgebraicGeometry.Space.fibreRestriction_essSurj_of_glue`: restriction is essentially
  surjective when every compatible pair is glued by an object over `S'`.
* `AlgebraicGeometry.Space.fibreRestriction_isEquivalence_of_isPushout_of_glue`: the two
  together.

## References

* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}

/-- The left component of a base change of a morphism of the slice, followed by the projection
to the source of the base change, is the projection followed by the morphism. -/
theorem pullback_map_left_fst {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V)
    {Z W : Over (schemeSpace V)} (k : Z ⟶ W) :
    ((Over.pullback (schemeSpaceMap a)).map k).left ≫ pullback.fst W.hom (schemeSpaceMap a) =
      pullback.fst Z.hom (schemeSpaceMap a) ≫ k.left :=
  pullback.lift_fst _ _ _

variable (R : ∀ U : BigFppfOver B S₀ hS₀, ObjectProperty (Over (schemeSpace U)))
  (hR : FibreStable R)
variable {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
  (hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g)

/-- The map from the restriction `W_T = (W ×_{S'} S) ×_S T` of an object `W` over `S'` to its
restriction `W_{T'} = W ×_{S'} T'`, through the canonical identification of the two routes
to `T`. -/
abbrev overlapToT' (W : Over (schemeSpace S')) :
    pullback (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) ⟶
      pullback W.hom (schemeSpaceMap g) :=
  ((sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
    (schemeSpaceMap h) hc W).hom).left ≫
      pullback.fst (pullback.snd W.hom (schemeSpaceMap g)) (schemeSpaceMap i)

/-- The square of base changes of an object `W` over `S'` commutes. -/
theorem overlapToT'_fst (W : Over (schemeSpace S')) :
    overlapToT' i f g h hc W ≫ pullback.fst W.hom (schemeSpaceMap g) =
      pullback.fst (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
        pullback.fst W.hom (schemeSpaceMap h) := by
  simpa only [overlapToT', Category.assoc] using
    sliceOverlapIso_hom_left_comp_fst (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
      (schemeSpaceMap h) hc W

/-- The hypothesis of full faithfulness: every object of the fibre over `S'` is the pushout of
its base changes to `S`, `T` and `T'`. -/
abbrev IsPushoutOfRestrictions : Prop :=
  ∀ W : (R S').FullSubcategory,
    IsPushout (overlapToT' i f g h hc W.obj)
      (pullback.fst (pullback.snd W.obj.hom (schemeSpaceMap h)) (schemeSpaceMap f))
      (pullback.fst W.obj.hom (schemeSpaceMap g)) (pullback.fst W.obj.hom (schemeSpaceMap h))

/-- Restriction is faithful when every object over `S'` is the pushout of its restrictions. -/
theorem fibreRestriction_faithful_of_isPushout
    (hpo : IsPushoutOfRestrictions R i f g h hc) :
    (fibrePushoutRestriction R hR i f g h hc).Faithful := by
  constructor
  intro W₁ W₂ φ ψ hφψ
  apply (R S').ι.map_injective
  show φ.hom = ψ.hom
  apply Over.OverMorphism.ext
  have hS : ((Over.pullback (schemeSpaceMap h)).map φ.hom).left =
      ((Over.pullback (schemeSpaceMap h)).map ψ.hom).left :=
    congrArg (fun k => k.hom.left) (congrArg CategoricalPullback.Hom.fst hφψ)
  have hT : ((Over.pullback (schemeSpaceMap g)).map φ.hom).left =
      ((Over.pullback (schemeSpaceMap g)).map ψ.hom).left :=
    congrArg (fun k => k.hom.left) (congrArg CategoricalPullback.Hom.snd hφψ)
  apply (hpo W₁).hom_ext
  · rw [← pullback_map_left_fst g φ.hom, ← pullback_map_left_fst g ψ.hom, hT]
  · rw [← pullback_map_left_fst h φ.hom, ← pullback_map_left_fst h ψ.hom, hS]

/-- Two morphisms of restrictions to `S` and to `T'` that agree on the overlap `T` satisfy the
compatibility square of the pushout of restrictions. -/
theorem overlapToT'_comp_left {W₁ W₂ : Over (schemeSpace S')}
    (a : (Over.pullback (schemeSpaceMap h)).obj W₁ ⟶ (Over.pullback (schemeSpaceMap h)).obj W₂)
    (b : (Over.pullback (schemeSpaceMap g)).obj W₁ ⟶ (Over.pullback (schemeSpaceMap g)).obj W₂)
    (hab : (Over.pullback (schemeSpaceMap f)).map a ≫
        (sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₂).hom =
      (sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₁).hom ≫ (Over.pullback (schemeSpaceMap i)).map b) :
    overlapToT' i f g h hc W₁ ≫ b.left =
      ((Over.pullback (schemeSpaceMap f)).map a).left ≫ overlapToT' i f g h hc W₂ := by
  have h1 : ((Over.pullback (schemeSpaceMap i)).map b).left ≫
        pullback.fst (pullback.snd W₂.hom (schemeSpaceMap g)) (schemeSpaceMap i) =
      pullback.fst (pullback.snd W₁.hom (schemeSpaceMap g)) (schemeSpaceMap i) ≫ b.left :=
    pullback_map_left_fst i b
  have hw : ((Over.pullback (schemeSpaceMap f)).map a).left ≫
        ((sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₂).hom).left =
      ((sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₁).hom).left ≫ ((Over.pullback (schemeSpaceMap i)).map b).left :=
    by simpa only [Over.comp_left] using congrArg (fun q => q.left) hab
  dsimp only [overlapToT']
  rw [Category.assoc, ← h1, ← Category.assoc, ← hw, Category.assoc]

/-- A morphism of base changes is the base change of `m` once it is compatible with `m` along the
first projections. -/
private theorem pullback_map_eq_of_fst {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V)
    {W₁ W₂ : Over (schemeSpace V)} (m : W₁ ⟶ W₂)
    (c : (Over.pullback (schemeSpaceMap a)).obj W₁ ⟶ (Over.pullback (schemeSpaceMap a)).obj W₂)
    (hc : pullback.fst W₁.hom (schemeSpaceMap a) ≫ m.left =
      c.left ≫ pullback.fst W₂.hom (schemeSpaceMap a)) :
    (Over.pullback (schemeSpaceMap a)).map m = c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback_map_left_fst a m).trans hc
  · exact (Over.w _).trans (Over.w c).symm

/-- A pair of morphisms of restrictions to `S` and to `T'` agreeing on the overlap `T` comes
from a morphism over `S'`, when the source is the pushout of its restrictions. -/
theorem exists_eq_pullback_map_of_isPushout {W₁ W₂ : Over (schemeSpace S')}
    (hpo : IsPushout (overlapToT' i f g h hc W₁)
      (pullback.fst (pullback.snd W₁.hom (schemeSpaceMap h)) (schemeSpaceMap f))
      (pullback.fst W₁.hom (schemeSpaceMap g)) (pullback.fst W₁.hom (schemeSpaceMap h)))
    (a : (Over.pullback (schemeSpaceMap h)).obj W₁ ⟶ (Over.pullback (schemeSpaceMap h)).obj W₂)
    (b : (Over.pullback (schemeSpaceMap g)).obj W₁ ⟶ (Over.pullback (schemeSpaceMap g)).obj W₂)
    (hab : (Over.pullback (schemeSpaceMap f)).map a ≫
        (sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₂).hom =
      (sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W₁).hom ≫ (Over.pullback (schemeSpaceMap i)).map b) :
    ∃ m : W₁ ⟶ W₂, (Over.pullback (schemeSpaceMap h)).map m = a ∧
      (Over.pullback (schemeSpaceMap g)).map m = b := by
  have ha : a.left ≫ pullback.snd W₂.hom (schemeSpaceMap h) =
      pullback.snd W₁.hom (schemeSpaceMap h) := Over.w a
  have hb : b.left ≫ pullback.snd W₂.hom (schemeSpaceMap g) =
      pullback.snd W₁.hom (schemeSpaceMap g) := Over.w b
  have hfa : ((Over.pullback (schemeSpaceMap f)).map a).left ≫
        pullback.fst (pullback.snd W₂.hom (schemeSpaceMap h)) (schemeSpaceMap f) =
      pullback.fst (pullback.snd W₁.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫ a.left :=
    pullback_map_left_fst f a
  have hcond : overlapToT' i f g h hc W₁ ≫ (b.left ≫ pullback.fst W₂.hom (schemeSpaceMap g)) =
      pullback.fst (pullback.snd W₁.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
        (a.left ≫ pullback.fst W₂.hom (schemeSpaceMap h)) := by
    rw [← Category.assoc, overlapToT'_comp_left i f g h hc a b hab, Category.assoc,
      overlapToT'_fst, ← Category.assoc, hfa, Category.assoc]
  have hm : hpo.desc _ _ hcond ≫ W₂.hom = W₁.hom := by
    apply hpo.hom_ext
    · rw [hpo.inl_desc_assoc, Category.assoc, pullback.condition, ← Category.assoc, hb,
        pullback.condition]
    · rw [hpo.inr_desc_assoc, Category.assoc, pullback.condition, ← Category.assoc, ha,
        pullback.condition]
  exact ⟨Over.homMk (hpo.desc _ _ hcond) hm,
    pullback_map_eq_of_fst h _ _ (hpo.inr_desc _ _ hcond),
    pullback_map_eq_of_fst g _ _ (hpo.inl_desc _ _ hcond)⟩

/-- Restriction is full when every object over `S'` is the pushout of its restrictions. -/
theorem fibreRestriction_full_of_isPushout
    (hpo : IsPushoutOfRestrictions R i f g h hc) :
    (fibrePushoutRestriction R hR i f g h hc).Full := by
  constructor
  intro W₁ W₂ k
  obtain ⟨m, hmS, hmT⟩ := exists_eq_pullback_map_of_isPushout i f g h hc (hpo W₁)
    k.fst.hom k.snd.hom (congrArg (fun q => q.hom) k.w)
  refine ⟨(R S').homMk m, ?_⟩
  apply CategoricalPullback.hom_ext
  · exact (R S).ι.map_injective hmS
  · exact (R T').ι.map_injective hmT

/-! ### Essential surjectivity -/

/-- An object over `U` exhibited as the base change of an object `W` over `V` by a cartesian
square is isomorphic, in the slice over `U`, to the base change of `W`. -/
def pullbackIsoOfIsPullback {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V)
    {W : Over (schemeSpace V)} {X : Over (schemeSpace U)} {j : X.left ⟶ W.left}
    (hX : IsPullback j X.hom W.hom (schemeSpaceMap a)) :
    (Over.pullback (schemeSpaceMap a)).obj W ≅ X :=
  Over.isoMk hX.isoPullback.symm hX.isoPullback_inv_snd

/-- **Gluing a compatible pair.** Let `V` be over `S`, `U'` over `T'` and
`φ : V ×_S T ⟶ U' ×_{T'} T` a morphism over `T`. If `W` over `S'` comes with cartesian squares
exhibiting `V` as `W ×_{S'} S` and `U'` as `W ×_{S'} T'`, and the two maps `V ×_S T ⟶ W` agree
through `φ`, then the resulting identifications of the restrictions of `W` with `V` and `U'`
are compatible with `φ` and the canonical identification of the two restrictions of `W` to
`T`. -/
theorem pullbackIsoOfIsPullback_compat {V : Over (schemeSpace S)} {U' : Over (schemeSpace T')}
    (φ : (Over.pullback (schemeSpaceMap f)).obj V ⟶ (Over.pullback (schemeSpaceMap i)).obj U')
    {W : Over (schemeSpace S')} {jV : V.left ⟶ W.left} {jU : U'.left ⟶ W.left}
    (hV : IsPullback jV V.hom W.hom (schemeSpaceMap h))
    (hU : IsPullback jU U'.hom W.hom (schemeSpaceMap g))
    (hcomm : φ.left ≫ pullback.fst U'.hom (schemeSpaceMap i) ≫ jU =
      pullback.fst V.hom (schemeSpaceMap f) ≫ jV) :
    (Over.pullback (schemeSpaceMap f)).map (pullbackIsoOfIsPullback h hV).hom ≫ φ =
      (sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
          (schemeSpaceMap h) hc W).hom ≫
        (Over.pullback (schemeSpaceMap i)).map (pullbackIsoOfIsPullback g hU).hom := by
  let A := ((Over.pullback (schemeSpaceMap f)).map (pullbackIsoOfIsPullback h hV).hom).left
  let Bl := ((Over.pullback (schemeSpaceMap i)).map (pullbackIsoOfIsPullback g hU).hom).left
  let Sl := ((sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
    (schemeSpaceMap h) hc W).hom).left
  have F4 : A ≫ pullback.fst V.hom (schemeSpaceMap f) =
      pullback.fst (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
        hV.isoPullback.inv :=
    pullback_map_left_fst f (pullbackIsoOfIsPullback h hV).hom
  have F5 : Bl ≫ pullback.fst U'.hom (schemeSpaceMap i) =
      pullback.fst (pullback.snd W.hom (schemeSpaceMap g)) (schemeSpaceMap i) ≫
        hU.isoPullback.inv :=
    pullback_map_left_fst i (pullbackIsoOfIsPullback g hU).hom
  have F6 : φ.left ≫ pullback.snd U'.hom (schemeSpaceMap i) =
      pullback.snd V.hom (schemeSpaceMap f) := Over.w φ
  have F7 : A ≫ pullback.snd V.hom (schemeSpaceMap f) =
      pullback.snd (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) :=
    Over.w ((Over.pullback (schemeSpaceMap f)).map (pullbackIsoOfIsPullback h hV).hom)
  have F8 : Sl ≫ pullback.snd (pullback.snd W.hom (schemeSpaceMap g)) (schemeSpaceMap i) =
      pullback.snd (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) :=
    sliceOverlapIso_hom_left_comp_snd _ _ _ _ hc W
  have F9 : Bl ≫ pullback.snd U'.hom (schemeSpaceMap i) =
      pullback.snd (pullback.snd W.hom (schemeSpaceMap g)) (schemeSpaceMap i) :=
    Over.w ((Over.pullback (schemeSpaceMap i)).map (pullbackIsoOfIsPullback g hU).hom)
  have F10 : Sl ≫ pullback.fst (pullback.snd W.hom (schemeSpaceMap g)) (schemeSpaceMap i) ≫
        pullback.fst W.hom (schemeSpaceMap g) =
      pullback.fst (pullback.snd W.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
        pullback.fst W.hom (schemeSpaceMap h) := by
    simpa only [overlapToT', Category.assoc] using overlapToT'_fst i f g h hc W
  apply Over.OverMorphism.ext
  show A ≫ φ.left = Sl ≫ Bl
  apply pullback.hom_ext
  · apply hU.hom_ext
    · simp only [Category.assoc]
      rw [hcomm, reassoc_of% F4, hV.isoPullback_inv_fst, reassoc_of% F5,
        hU.isoPullback_inv_fst, F10]
    · simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% F6, reassoc_of% F7, reassoc_of% F9,
        reassoc_of% F8]
  · simp only [Category.assoc]
    rw [F6, F7, F9, F8]

/-- The hypothesis of essential surjectivity: every compatible pair `(V, U', φ)` of the fibres
over `S` and `T'` is glued by an object `W` of the fibre over `S'`, i.e. there are cartesian
squares exhibiting `V` as `W ×_{S'} S` and `U'` as `W ×_{S'} T'` through which the two maps
`V ×_S T ⟶ W` agree via `φ`. -/
abbrev GluesCompatiblePairs : Prop :=
  ∀ P : CategoricalPullback (fibreBaseChange R hR f) (fibreBaseChange R hR i),
    ∃ (W : (R S').FullSubcategory) (jV : P.fst.obj.left ⟶ W.obj.left)
      (jU : P.snd.obj.left ⟶ W.obj.left),
      IsPullback jV P.fst.obj.hom W.obj.hom (schemeSpaceMap h) ∧
      IsPullback jU P.snd.obj.hom W.obj.hom (schemeSpaceMap g) ∧
      P.iso.hom.hom.left ≫ pullback.fst P.snd.obj.hom (schemeSpaceMap i) ≫ jU =
        pullback.fst P.fst.obj.hom (schemeSpaceMap f) ≫ jV

/-- Restriction is essentially surjective when every compatible pair is glued by an object over
`S'`. -/
theorem fibreRestriction_essSurj_of_glue (hglue : GluesCompatiblePairs R hR i f g h) :
    (fibrePushoutRestriction R hR i f g h hc).EssSurj := by
  constructor
  intro P
  obtain ⟨W, jV, jU, hV, hU, hcomm⟩ := hglue P
  refine ⟨W, ⟨CategoricalPullback.mkIso ((R S).isoMk (pullbackIsoOfIsPullback h hV))
    ((R T').isoMk (pullbackIsoOfIsPullback g hU)) ?_⟩⟩
  exact (R T).ι.map_injective (pullbackIsoOfIsPullback_compat i f g h hc P.iso.hom.hom hV hU hcomm)

/-- **Restriction across a pushout square is an equivalence once objects glue.** If every
object of the fibre over `S'` is the pushout of its restrictions to `S`, `T` and `T'`, and
every compatible pair over `S` and `T'` is glued by an object of the fibre over `S'`, then the
canonical restriction functor is an equivalence. -/
theorem fibreRestriction_isEquivalence_of_isPushout_of_glue
    (hpo : IsPushoutOfRestrictions R i f g h hc) (hglue : GluesCompatiblePairs R hR i f g h) :
    (fibrePushoutRestriction R hR i f g h hc).IsEquivalence := by
  have := fibreRestriction_faithful_of_isPushout R hR i f g h hc hpo
  have := fibreRestriction_full_of_isPushout R hR i f g h hc hpo
  have := fibreRestriction_essSurj_of_glue R hR i f g h hc hglue
  exact { }

end AlgebraicGeometry.Space
