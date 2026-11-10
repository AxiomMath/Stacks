module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationUniqueLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplementRange
public import StacksFrontier.CategoryTheory.Sites.JointCoverDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pushforward of a modification along a separated étale morphism

Let `f : V ⟶ W` be a morphism of algebraic spaces over a scheme `S` and let `h : Y ⟶ V` be an
algebraic space over `V`. The proof of Stacks 0BGY constructs the presheaf on the big fppf site
of `S` whose sections over a test object `T` are the pairs `(w, y)` consisting of a morphism
`w : T ⟶ W` and a morphism `y : T ×_{w, W} V ⟶ Y` **over `V`**. It is the dependent product, or
pushforward, of `Y` along `f`, and the source shows that it is the algebraic space whose base
change along `f` is `Y` and which is unchanged away from the closed subspace over which `f` is an
isomorphism.

Those pairs are the pairs of Stacks 05Y1 for the relative morphism functor `Mor_W(V, Y)` of
Stacks 05Y2, cut down by the condition that the second component lie over `V`; so the
pushforward is a subfunctor of `Mor_W(V, Y)`, and its restriction maps, its projection to `W`
and the identification of its sections come for free from that functor.

## Main definitions

* `AlgebraicGeometry.Space.excisionSubfunctor`: the subfunctor of `Mor_W(V, Y)` of the pairs
  whose second component lies over `V`.
* `AlgebraicGeometry.Space.excisionPushforward` and
  `AlgebraicGeometry.Space.excisionProjection`: that subfunctor read as a presheaf, with its
  projection to `W`.
* `AlgebraicGeometry.Space.excisionSections`: the sections of the pushforward over a test
  object, as pairs.
* `AlgebraicGeometry.Space.diagSection`: the diagonal section `A ⟶ A ×_W V` of a morphism
  `v : A ⟶ V`, along which the second component of a pair is evaluated.
* `AlgebraicGeometry.Space.diagonalCoverObj` and
  `AlgebraicGeometry.Space.diagonalCoverHom`: the decomposition `V ×_W V = Δ(V) ⊔ C` of a
  separated étale morphism, read as a two-member family indexed by `Bool`.

## Main results

* `AlgebraicGeometry.Space.excisionProjection_app`: the projection reads off the first
  component of a pair.
* `AlgebraicGeometry.Space.excisionSections_map`: the restriction maps are base change of
  pairs.
* `AlgebraicGeometry.Space.isSheaf_excisionPushforward`: the pushforward is an fppf sheaf.
* `AlgebraicGeometry.Space.existsUnique_excision_app_of_mem`: over a section of `W` which lies
  in an open subspace away from which `Y` is unchanged, the pushforward has exactly one
  section. This is the statement that the pushforward is unchanged away from that subspace.
* `AlgebraicGeometry.Space.isIso_pullback_snd_excisionProjection`: the base change of the
  pushforward to such an open subspace is an isomorphism.
* `AlgebraicGeometry.Space.exists_excision_morphism_of_diagSection` and
  `AlgebraicGeometry.Space.excision_morphism_unique_of_diagSection`: for `f` separated and
  étale, restriction to the diagonal is a bijection from the morphisms `A ×_W V ⟶ Y` over `V`
  to the morphisms `A ⟶ Y` over `V`.
* `AlgebraicGeometry.Space.exists_iso_pullback_excisionProjection`: the base change of the
  pushforward along `f` is `Y`, compatibly with the two morphisms to `V`.
* `AlgebraicGeometry.Space.sheafify_iSup_range_pullback_fst_eq_top` and
  `AlgebraicGeometry.Space.sheafify_iSup_range_yoneda_map_eq_top`: a jointly covering family
  stays jointly covering after base change, and a covering sieve of an object of the site is a
  jointly covering family of the presheaf it represents.

## Implementation notes

The condition cutting out the subfunctor is stability of `y ≫ h = pullback.snd` under base
change of pairs, which is `CategoryTheory.Limits.pullback.map_snd`; nothing else about the
relative morphism functor is used to form the subfunctor.

The uniqueness statement is `AlgebraicGeometry.Space.existsUnique_lift_of_isIso_pullback_snd`
applied to `h`: the projection `T ×_W V ⟶ V` factors through the preimage of the open subspace,
because its composite with `f` is the projection to `T` followed by a morphism which factors
through that subspace.

The sheaf property is `CategoryTheory.Subfunctor.isSheaf_iff` over the sheaf `Mor_W(V, Y)` of
Stacks 05Y3: the condition cutting out the subfunctor is an equality of two morphisms
`T ×_W V ⟶ V`, and `V` is a sheaf, so it suffices that the comparison maps of the base changes
along a covering sieve be jointly covering. That is the base change along `T ×_W V ⟶ T` of the
statement that a covering sieve covers the presheaf it generates.

The identification of the base change along `f` goes through the *universal* pair, the morphism
`Y ×_W V ⟶ Y` over `V` restricting to the identity on the diagonal. Restricting it along the
morphisms `yoneda.obj T' ⟶ Y` which name the sections of `Y` produces the inverse morphism
`Y ⟶ (pushforward) ×_W V` with no further work: its naturality is
`AlgebraicGeometry.Space.RelativeMorphism.restrict_comp`. Only its bijectivity on sections needs
the decomposition `V ×_W V = Δ(V) ⊔ C` of
`AlgebraicGeometry.Space.exists_subfunctor_sheafify_sup_range_diagonal_eq_top`, base changed
along `v : A ⟶ V`; over the diagonal piece a morphism to `Y` is the datum wanted, and over `C`
it is the unique lift of its image in `V`, because `C` lies over the open complement of `T`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ModificationExcisionPushforward
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ModificationExcisionPushforward
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)
  (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y)
  (hW : IsAlgebraicSpace B S hS W)

/-- **Lying over `V` is stable under restriction of pairs.** The second component of a
restricted pair is the comparison map of the two base changes followed by the second component
of the original pair, and that comparison map carries the projection to `V` to the projection
to `V`. -/
theorem restrict_morphism_comp_eq {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : T' ⟶ T)
    (p : RelativeMorphism B S hS V Y W f (h ≫ f) T)
    (hp : p.morphism ≫ h = pullback.snd p.base f) :
    (RelativeMorphism.restrict t p).morphism ≫ h =
      pullback.snd (RelativeMorphism.restrict t p).base f := by
  have key : (pullback.map (t ≫ p.base) f p.base f t (𝟙 V) (𝟙 W) (by simp) (by simp) ≫
      p.morphism) ≫ h = pullback.snd (t ≫ p.base) f := by
    rw [Category.assoc, hp, pullback.map_snd, Category.comp_id]
  exact key

/-- Lying over `V` transfers along an equality of pairs. -/
private theorem morphism_comp_eq_of_eq {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q r : RelativeMorphism B S hS V Y W f (h ≫ f) T} (e : q = r)
    (hr : r.morphism ≫ h = pullback.snd r.base f) :
    q.morphism ≫ h = pullback.snd q.base f :=
  e ▸ hr

/-- An algebraic space is a sheaf of types for the topology of the big fppf site. -/
private theorem isSheaf_of_isAlgebraicSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
  (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf

/-! ### Jointly covering families -/

section Covering

variable {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A jointly covering family stays jointly covering after an arbitrary base change.** If the
subfunctor of `X` generated by the images of a family sheafifies to the whole of `X`, then for
every `g : P ⟶ X` the subfunctor of `P` generated by the images of the first projections of the
fibre products `P ×_X A i` sheafifies to the whole of `P`.

A section of `P` whose image in `X` lifts to a member of the family lifts to the corresponding
fibre product, the lift being `CategoryTheory.Limits.pullback.lift` of the two morphisms out of
the representable presheaf named by the two sections. -/
@[sga "3 IV 4.2.3" "special case"]
theorem sheafify_iSup_range_pullback_fst_eq_top {I : Type*}
    {A : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : ∀ i, A i ⟶ X)
    (ht : (⨆ i, Subfunctor.range (t i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (g : P ⟶ X) :
    (⨆ i, Subfunctor.range (pullback.fst g (t i))).sheafify
      (BigFppfOver.topology B S hS) = ⊤ := by
  refine top_le_iff.1 ?_
  intro A' p _
  have hcov : (⨆ i, Subfunctor.range (t i)).sieveOfSection (g.app A' p) ∈
      BigFppfOver.topology B S hS A'.unop := by
    have hmem : g.app A' p ∈ ((⨆ i, Subfunctor.range (t i)).sheafify
        (BigFppfOver.topology B S hS)).obj A' := by
      rw [ht]; trivial
    exact hmem
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcov
  intro Z k hk
  have hk' : X.map k.op (g.app A' p) ∈ (⨆ i, Subfunctor.range (t i)).obj (op Z) := hk
  rw [Subfunctor.iSup_obj] at hk'
  obtain ⟨i, c, hc⟩ := Set.mem_iUnion.1 hk'
  have hw : yonedaEquiv.symm (P.map k.op p) ≫ g = yonedaEquiv.symm c ≫ t i := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hc,
      NatTrans.naturality_apply]
  have hmem : P.map k.op p ∈ (⨆ i, Subfunctor.range (pullback.fst g (t i))).obj (op Z) := by
    rw [Subfunctor.iSup_obj]
    refine Set.mem_iUnion.mpr ⟨i, yonedaEquiv (pullback.lift _ _ hw), ?_⟩
    rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  exact hmem

/-- **A covering sieve of an object of the site is a jointly covering family of the presheaf it
represents.** The sieve of arrows along which a prescribed section of `yoneda.obj U` restricts
into the image of a member is the base change of the given covering sieve along that section,
hence covering. -/
theorem sheafify_iSup_range_yoneda_map_eq_top (U : BigFppfOver B S hS) (R : Sieve U)
    (hR : R ∈ BigFppfOver.topology B S hS U) :
    (⨆ i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g},
        Subfunctor.range (yoneda.map i.2.1)).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  refine top_le_iff.1 ?_
  intro A' s _
  have hcov : R.pullback s ∈ BigFppfOver.topology B S hS A'.unop :=
    (BigFppfOver.topology B S hS).pullback_stable s hR
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcov
  intro Z k hk
  have hmem : (yoneda.obj U).map k.op s ∈
      (⨆ i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g},
        Subfunctor.range (yoneda.map i.2.1)).obj (op Z) := by
    rw [Subfunctor.iSup_obj]
    refine Set.mem_iUnion.mpr ⟨⟨Z, ⟨k ≫ s, hk⟩⟩, 𝟙 Z, ?_⟩
    simp
  exact hmem

end Covering

/-- The pairs of Stacks 05Y1 for `Mor_W(V, Y)` whose second component lies over `V` and not
merely over `W`. -/
def excisionSubfunctor : Subfunctor (relativeHom B S hS V Y W f (h ≫ f) hV hY hW) where
  obj T := {p |
    (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T.unop p).morphism ≫ h =
      pullback.snd (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T.unop p).base f}
  map := by
    intro U U' i p hp
    have hp' : (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW U.unop p).morphism ≫ h =
        pullback.snd (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW U.unop p).base f := hp
    have key : ∀ q : RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj U'.unop),
        q = RelativeMorphism.restrict (yoneda.map i.unop)
          (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW U.unop p) →
        q.morphism ≫ h = pullback.snd q.base f := by
      rintro q rfl
      exact restrict_morphism_comp_eq B S hS f h (yoneda.map i.unop) _ hp'
    exact key _ (relativeHomSections_map B S hS V Y W f (h ≫ f) hV hY hW i.unop p)

/-- The pushforward of `Y` along `f`: the presheaf whose sections over a test object `T` are the
pairs consisting of a morphism `T ⟶ W` and a morphism `T ×_W V ⟶ Y` over `V`. -/
def excisionPushforward : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (excisionSubfunctor B S hS f h hV hY hW).toFunctor

/-- The projection of the pushforward to `W`, reading off the first component of a pair. -/
def excisionProjection : excisionPushforward B S hS f h hV hY hW ⟶ W :=
  (excisionSubfunctor B S hS f h hV hY hW).ι ≫
    relativeHomProjection B S hS V Y W f (h ≫ f) hV hY hW

/-- The sections of the pushforward over a test object, as pairs of Stacks 05Y1 which lie
over `V`. -/
def excisionSections (T : BigFppfOver B S hS)
    (p : (excisionPushforward B S hS f h hV hY hW).obj (op T)) :
    RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj T) :=
  relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T p.1

/-- A section of the pushforward lies over `V`. -/
theorem excisionSections_comp (T : BigFppfOver B S hS)
    (p : (excisionPushforward B S hS f h hV hY hW).obj (op T)) :
    (excisionSections B S hS f h hV hY hW T p).morphism ≫ h =
      pullback.snd (excisionSections B S hS f h hV hY hW T p).base f :=
  p.2

/-- The projection of the pushforward reads off the first component of a pair. -/
theorem excisionProjection_app (T : BigFppfOver B S hS)
    (p : (excisionPushforward B S hS f h hV hY hW).obj (op T)) :
    (excisionProjection B S hS f h hV hY hW).app (op T) p =
      yonedaEquiv (excisionSections B S hS f h hV hY hW T p).base :=
  rfl

/-- The restriction maps of the pushforward are base change of pairs. -/
theorem excisionSections_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : (excisionPushforward B S hS f h hV hY hW).obj (op T)) :
    excisionSections B S hS f h hV hY hW T'
        ((excisionPushforward B S hS f h hV hY hW).map g.op p) =
      RelativeMorphism.restrict (yoneda.map g)
        (excisionSections B S hS f h hV hY hW T p) :=
  relativeHomSections_map B S hS V Y W f (h ≫ f) hV hY hW g p.1

/-- Two sections of the pushforward over a test object with the same underlying pair agree. -/
theorem excision_obj_ext (T : BigFppfOver B S hS)
    (p q : (excisionPushforward B S hS f h hV hY hW).obj (op T))
    (hpq : excisionSections B S hS f h hV hY hW T p =
      excisionSections B S hS f h hV hY hW T q) : p = q :=
  Subtype.ext ((relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T).injective hpq)

/-! ### The pushforward is a sheaf -/

/-- **A pair which lies over `V` locally lies over `V`.** The two morphisms
`T ×_W V ⟶ V` to be compared agree after composing with the comparison maps of the base changes
along the arrows of a covering sieve, and those comparison maps are jointly covering because a
covering sieve is a jointly covering family of the representable presheaf and joint covering
survives base change along `T ×_W V ⟶ T`. -/
theorem morphism_comp_eq_of_forall
    (hVsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) V) (U : BigFppfOver B S hS)
    (q : RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj U)) (R : Sieve U)
    (hR : R ∈ BigFppfOver.topology B S hS U)
    (hloc : ∀ ⦃Z : BigFppfOver B S hS⦄ (g : Z ⟶ U), R.arrows g →
      (RelativeMorphism.restrict (yoneda.map g) q).morphism ≫ h =
        pullback.snd (RelativeMorphism.restrict (yoneda.map g) q).base f) :
    q.morphism ≫ h = pullback.snd q.base f := by
  have hcov₀ := sheafify_iSup_range_yoneda_map_eq_top B S hS U R hR
  have hcov₁ := sheafify_iSup_range_pullback_fst_eq_top B S hS
    (fun i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g} => yoneda.map i.2.1)
    hcov₀ (pullback.fst q.base f)
  have hle : (⨆ i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g},
        Subfunctor.range (pullback.fst (pullback.fst q.base f) (yoneda.map i.2.1))) ≤
      ⨆ i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g},
        Subfunctor.range (pullback.mapFst (yoneda.map i.2.1) q.base f) := by
    refine iSup_le fun i => ?_
    have hsq := (pullback.isPullback_mapFst (yoneda.map i.2.1) q.base f).flip
    have hu : hsq.lift (pullback.fst (pullback.fst q.base f) (yoneda.map i.2.1))
          (pullback.snd (pullback.fst q.base f) (yoneda.map i.2.1)) pullback.condition ≫
        pullback.mapFst (yoneda.map i.2.1) q.base f =
          pullback.fst (pullback.fst q.base f) (yoneda.map i.2.1) :=
      hsq.lift_fst _ _ _
    rw [← hu]
    exact le_trans (Subfunctor.range_comp_le _ _)
      (le_iSup (fun j : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g} =>
        Subfunctor.range (pullback.mapFst (yoneda.map j.2.1) q.base f)) i)
  have hcov : (⨆ i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g},
      Subfunctor.range (pullback.mapFst (yoneda.map i.2.1) q.base f)).sheafify
        (BigFppfOver.topology B S hS) = ⊤ :=
    top_le_iff.1 (hcov₁.ge.trans (Subfunctor.sheafify_le_sheafify _ hle))
  refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top (BigFppfOver.topology B S hS)
    (fun i : Σ Z : BigFppfOver B S hS, {g : Z ⟶ U // R.arrows g} =>
      pullback.mapFst (yoneda.map i.2.1) q.base f) hcov hVsheaf ?_
  rintro ⟨Z, g, hg⟩
  have hmap : pullback.map (yoneda.map g ≫ q.base) f q.base f (yoneda.map g) (𝟙 V) (𝟙 W)
      (by simp) (by simp) = pullback.mapFst (yoneda.map g) q.base f :=
    pullback.map_id_eq_mapFst _ _ _ _ _
  have h2 : (pullback.mapFst (yoneda.map g) q.base f ≫ q.morphism) ≫ h =
      pullback.snd (yoneda.map g ≫ q.base) f := by
    rw [← hmap]
    exact hloc g hg
  rw [← Category.assoc, h2, pullback.mapFst_snd]

/-- **The pushforward of `Y` along `f` is an fppf sheaf.** The relative morphism functor is a
sheaf by Stacks 05Y3, so by `CategoryTheory.Subfunctor.isSheaf_iff` it is enough that a pair
which lies over `V` after restriction along a covering sieve already lies over `V`. -/
theorem isSheaf_excisionPushforward :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (excisionPushforward B S hS f h hV hY hW) := by
  have hMor : Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (relativeHom B S hS V Y W f (h ≫ f) hV hY hW) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (isSheaf_relativeHom B S hS V Y W f (h ≫ f) hV hY hW)
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf (BigFppfOver.topology B S hS)
    (excisionSubfunctor B S hS f h hV hY hW).toFunctor
  refine (Subfunctor.isSheaf_iff _ hMor).2 ?_
  intro U s hs
  refine morphism_comp_eq_of_forall B S hS f h (isSheaf_of_isAlgebraicSpace B S hS hV) U.unop
    (relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW U.unop s)
    ((excisionSubfunctor B S hS f h hV hY hW).sieveOfSection s) hs ?_
  intro Z g hg
  exact morphism_comp_eq_of_eq B S hS f h
    (relativeHomSections_map B S hS V Y W f (h ≫ f) hV hY hW g s).symm hg

/-! ### The pushforward over the untouched subspace -/

section Untouched

variable {W₀ : Subfunctor W}

/-- The projection `A ×_W V ⟶ V` of a base change along a morphism `a : A ⟶ W` landing in `W₀`
factors through the preimage `f⁻¹W₀`: its composite with `f` is the projection to `A` followed
by `a`. -/
theorem range_pullback_snd_le_preimage {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W)
    (ha : Subfunctor.range a ≤ W₀) :
    Subfunctor.range (pullback.snd a f) ≤ W₀.preimage f := by
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, ← pullback.condition]
  exact le_trans (Subfunctor.range_comp_le _ _) ha

/-- **The second component of a pair over `W₀` exists.** If `Y` is unchanged over `f⁻¹W₀` and
`a : A ⟶ W` lands in `W₀`, the projection `A ×_W V ⟶ V` lifts through `h`. -/
theorem exists_excision_morphism (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W) (ha : Subfunctor.range a ≤ W₀) :
    ∃ y : pullback a f ⟶ Y, y ≫ h = pullback.snd a f :=
  exists_lift_of_isIso_pullback_snd B S hS h hY₀ (pullback.snd a f)
    (Subfunctor.lift (pullback.snd a f) (range_pullback_snd_le_preimage B S hS f a ha)) rfl

/-- **The second component of a pair over `W₀` is unique.** -/
theorem excision_morphism_unique (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W) (ha : Subfunctor.range a ≤ W₀)
    (y₁ y₂ : pullback a f ⟶ Y) (h₁ : y₁ ≫ h = pullback.snd a f)
    (h₂ : y₂ ≫ h = pullback.snd a f) : y₁ = y₂ :=
  lift_eq_of_isIso_pullback_snd B S hS h hY₀
    (Subfunctor.lift (pullback.snd a f) (range_pullback_snd_le_preimage B S hS f a ha))
    y₁ y₂ h₁ h₂

/-- **Two pairs over one section of `W₀` which lie over `V` are equal.** -/
theorem relativeMorphism_ext_of_mem (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ W) (ha : Subfunctor.range a ≤ W₀)
    (q₁ q₂ : RelativeMorphism B S hS V Y W f (h ≫ f) A)
    (hb₁ : q₁.base = a) (hb₂ : q₂.base = a)
    (hm₁ : q₁.morphism ≫ h = pullback.snd q₁.base f)
    (hm₂ : q₂.morphism ≫ h = pullback.snd q₂.base f) : q₁ = q₂ := by
  obtain ⟨b₁, m₁, c₁⟩ := q₁
  obtain ⟨b₂, m₂, c₂⟩ := q₂
  subst hb₁
  subst hb₂
  simp only [RelativeMorphism.mk.injEq, heq_eq_eq, true_and]
  exact excision_morphism_unique B S hS f h hY₀ _ ha m₁ m₂ hm₁ hm₂

/-- **Over a section of `W` lying in `W₀` the pushforward has exactly one section.** This is
the statement that the pushforward of `Y` along `f` is unchanged away from the locus `f`
modifies: the second component of the pair is forced, because `Y` is unchanged over the
preimage of `W₀` and the projection `T ×_W V ⟶ V` lands there. -/
theorem existsUnique_excision_app_of_mem (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι))
    (T : BigFppfOver B S hS) (w : W.obj (op T)) (hw : w ∈ W₀.obj (op T)) :
    ∃! p : (excisionPushforward B S hS f h hV hY hW).obj (op T),
      (excisionProjection B S hS f h hV hY hW).app (op T) p = w := by
  have hrange : Subfunctor.range (yonedaEquiv.symm w) ≤ W₀ := by
    rintro C y ⟨g, rfl⟩
    exact W₀.map g.op hw
  obtain ⟨y, hy⟩ := exists_excision_morphism B S hS f h hY₀ (yonedaEquiv.symm w) hrange
  have hcomm : y ≫ (h ≫ f) = pullback.snd (yonedaEquiv.symm w) f ≫ f := by
    rw [← Category.assoc, hy]
  obtain ⟨s, hs⟩ : ∃ s : (relativeHom B S hS V Y W f (h ≫ f) hV hY hW).obj (op T),
      relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T s =
        (⟨yonedaEquiv.symm w, y, hcomm⟩ :
          RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj T)) :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  have hmem : s ∈ (excisionSubfunctor B S hS f h hV hY hW).obj (op T) :=
    morphism_comp_eq_of_eq B S hS f h hs hy
  obtain ⟨p, hp⟩ : ∃ p : (excisionPushforward B S hS f h hV hY hW).obj (op T),
      excisionSections B S hS f h hV hY hW T p =
        (⟨yonedaEquiv.symm w, y, hcomm⟩ :
          RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj T)) :=
    ⟨⟨s, hmem⟩, hs⟩
  have hbase : (excisionSections B S hS f h hV hY hW T p).base = yonedaEquiv.symm w :=
    congrArg RelativeMorphism.base hp
  refine ⟨p, ?_, ?_⟩
  · change (excisionProjection B S hS f h hV hY hW).app (op T) p = w
    rw [excisionProjection_app, hbase, Equiv.apply_symm_apply]
  · intro p' hp'
    have hp'' : (excisionProjection B S hS f h hV hY hW).app (op T) p' = w := hp'
    refine excision_obj_ext B S hS f h hV hY hW T p' p ?_
    refine relativeMorphism_ext_of_mem B S hS f h hY₀ (yonedaEquiv.symm w) hrange _ _
      ?_ hbase (excisionSections_comp B S hS f h hV hY hW T p')
      (excisionSections_comp B S hS f h hV hY hW T p)
    refine yonedaEquiv.eq_symm_apply.2 ?_
    exact (excisionProjection_app B S hS f h hV hY hW T p').symm.trans hp''

/-- **The base change of the pushforward to `W₀` is an isomorphism**, componentwise: over a
section of `W₀` the sections of the pushforward are a singleton, so pairing with that section
is a bijection. -/
theorem isIso_app_pullback_snd_excisionProjection
    (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι)) (T : BigFppfOver B S hS) :
    IsIso ((pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι).app (op T)) := by
  rw [isIso_iff_bijective]
  have hcond : ∀ c : (pullback (excisionProjection B S hS f h hV hY hW) W₀.ι).obj (op T),
      (excisionProjection B S hS f h hV hY hW).app (op T)
          ((pullback.fst (excisionProjection B S hS f h hV hY hW) W₀.ι).app (op T) c) =
        ((pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι).app (op T) c).1 := by
    intro c
    have h₁ : (pullback.fst (excisionProjection B S hS f h hV hY hW) W₀.ι ≫
          excisionProjection B S hS f h hV hY hW).app (op T) c =
        (pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι ≫ W₀.ι).app (op T) c := by
      rw [pullback.condition]
    rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply] at h₁
    exact h₁
  refine ⟨fun c₁ c₂ hc => ?_, fun w' => ?_⟩
  · refine pullback_obj_ext (excisionProjection B S hS f h hV hY hW) W₀.ι (op T) _ _ ?_ hc
    have hu := (existsUnique_excision_app_of_mem B S hS f h hV hY hW hY₀ T
      ((pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι).app (op T) c₁).1
      ((pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι).app (op T) c₁).2)
    refine hu.unique (hcond c₁) ?_
    rw [hcond c₂, hc]
  · obtain ⟨p, hp, -⟩ :=
      existsUnique_excision_app_of_mem B S hS f h hV hY hW hY₀ T w'.1 w'.2
    obtain ⟨c, -, hc⟩ := exists_pullback_obj B S hS
      (excisionProjection B S hS f h hV hY hW) W₀.ι p w' hp
    exact ⟨c, hc⟩

/-- **The base change of the pushforward to `W₀` is an isomorphism.** -/
theorem isIso_pullback_snd_excisionProjection
    (hY₀ : IsIso (pullback.snd h (W₀.preimage f).ι)) :
    IsIso (pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι) :=
  have : ∀ A, IsIso ((pullback.snd (excisionProjection B S hS f h hV hY hW) W₀.ι).app A) :=
    fun A => isIso_app_pullback_snd_excisionProjection B S hS f h hV hY hW hY₀ A.unop
  NatIso.isIso_of_isIso_app _

end Untouched

/-! ### The diagonal section and the decomposition of `V ×_W V` -/

section Diagonal

/-- The diagonal section `A ⟶ A ×_W V` of a morphism `v : A ⟶ V`: the pair `(𝟙, v)`. -/
def diagSection {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) : A ⟶ pullback (v ≫ f) f :=
  pullback.lift (𝟙 A) v (by rw [Category.id_comp])

/-- The first projection of `diagSection B S hS f v` is the identity of `A`. -/
@[reassoc (attr := simp)]
theorem diagSection_fst {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    diagSection B S hS f v ≫ pullback.fst (v ≫ f) f = 𝟙 A :=
  pullback.lift_fst _ _ _

/-- The second projection of `diagSection B S hS f v` is `v` itself. -/
@[reassoc (attr := simp)]
theorem diagSection_snd {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    diagSection B S hS f v ≫ pullback.snd (v ≫ f) f = v :=
  pullback.lift_snd _ _ _

/-- The two members of the decomposition `V ×_W V = Δ(V) ⊔ C`, as a family indexed by
`Bool`. -/
def diagonalCoverObj (C : Subfunctor (pullback f f)) :
    Bool → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  | false => V
  | true => C.toFunctor

/-- The morphisms of that family to the fibre square `V ×_W V`. -/
def diagonalCoverHom (C : Subfunctor (pullback f f)) :
    ∀ b, diagonalCoverObj B S hS f C b ⟶ pullback f f
  | false => pullback.diagonal f
  | true => C.ι

/-- The subfunctor generated by the two-member family is the join of the range of the diagonal
and the complementary piece. -/
theorem iSup_range_diagonalCoverHom (C : Subfunctor (pullback f f)) :
    (⨆ b, Subfunctor.range (diagonalCoverHom B S hS f C b)) =
      Subfunctor.range (pullback.diagonal f) ⊔ C := by
  rw [iSup_bool_eq]
  change Subfunctor.range C.ι ⊔ Subfunctor.range (pullback.diagonal f) =
    Subfunctor.range (pullback.diagonal f) ⊔ C
  rw [Subfunctor.range_ι, sup_comm]

/-- The base change to `A ×_W V` of the decomposition of `V ×_W V` is jointly covering. -/
theorem sheafify_iSup_range_diagonalCover (C : Subfunctor (pullback f f))
    (hCtop : (Subfunctor.range (pullback.diagonal f) ⊔ C).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    (⨆ b, Subfunctor.range (pullback.fst (pullback.mapFst v f f)
      (diagonalCoverHom B S hS f C b))).sheafify (BigFppfOver.topology B S hS) = ⊤ :=
  sheafify_iSup_range_pullback_fst_eq_top B S hS (diagonalCoverHom B S hS f C)
    (by rw [iSup_range_diagonalCoverHom]; exact hCtop) (pullback.mapFst v f f)

/-- On the diagonal part of `A ×_W V` the projection to `V` is the projection to `A` followed
by `v`. -/
theorem fst_mapFst_diagonal_comp {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
        pullback.fst (v ≫ f) f ≫ v =
      pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
        pullback.snd (v ≫ f) f := by
  rw [← pullback.mapFst_fst v f f, ← pullback.mapFst_snd v f f, ← Category.assoc,
    ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
    pullback.diagonal_fst, pullback.diagonal_snd]

/-- The diagonal part of `A ×_W V` factors through the diagonal section. -/
theorem fst_mapFst_diagonal_fac {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    (pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ pullback.fst (v ≫ f) f) ≫
        diagSection B S hS f v =
      pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, diagSection_fst, Category.comp_id]
  · rw [Category.assoc, diagSection_snd, Category.assoc]
    exact fst_mapFst_diagonal_comp B S hS f v

/-- The diagonal section factors through the diagonal part of `A ×_W V`. -/
theorem exists_comp_fst_mapFst_diagonal {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    ∃ u : A ⟶ pullback (pullback.mapFst v f f) (pullback.diagonal f),
      u ≫ pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) =
        diagSection B S hS f v := by
  have hcond : diagSection B S hS f v ≫ pullback.mapFst v f f = v ≫ pullback.diagonal f := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.mapFst_fst, ← Category.assoc, diagSection_fst,
        Category.id_comp, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.mapFst_snd, diagSection_snd, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]
  exact ⟨pullback.lift _ _ hcond, pullback.lift_fst _ _ _⟩

/-- The complementary part of `A ×_W V` lies over the preimage of the open complement of `T`:
its projection to `V` has composite with `f` factoring through that open subspace. -/
theorem range_fst_mapFst_complement_le (C : Subfunctor (pullback f f)) (T : Subfunctor W)
    (hCsnd : C ≤ (openComplement B S hS T).preimage (pullback.snd f f ≫ f))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) :
    Subfunctor.range (pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f) ≤
      (openComplement B S hS T).preimage f := by
  have hcomp : (pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f) ≫ f =
      pullback.snd (pullback.mapFst v f f) C.ι ≫ C.ι ≫ pullback.snd f f ≫ f := by
    rw [← pullback.mapFst_snd v f f, Category.assoc, ← Category.assoc,
      ← Category.assoc (pullback.fst (pullback.mapFst v f f) C.ι), pullback.condition,
      Category.assoc, Category.assoc]
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, hcomp]
  refine le_trans (Subfunctor.range_comp_le _ _) ?_
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]
  exact hCsnd

/-- A pair whose first component factors as `v ≫ f` has a diagonal section: a morphism
`A ⟶ A ×_W V` whose two components are the identity and `v`. -/
theorem exists_diag_of_base_eq {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V)
    (q : RelativeMorphism B S hS V Y W f (h ≫ f) A) (hb : q.base = v ≫ f) :
    ∃ d : A ⟶ pullback q.base f, d ≫ pullback.fst q.base f = 𝟙 A ∧
      d ≫ pullback.snd q.base f = v :=
  ⟨pullback.lift (𝟙 A) v (by rw [hb, Category.id_comp]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _⟩

/-- **The universal pair, restricted along `t : A ⟶ Y`, recovers `t` along the diagonal.** Here
the universal pair is a morphism `m : Y ×_W V ⟶ Y` over `V` whose restriction to the diagonal is
the identity of `Y`. -/
theorem comp_restrict_morphism (m : pullback (h ≫ f) f ⟶ Y)
    (hmc : m ≫ (h ≫ f) = pullback.snd (h ≫ f) f ≫ f)
    (hmd : diagSection B S hS f h ≫ m = 𝟙 Y)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : A ⟶ Y) (v : A ⟶ V) (hv : t ≫ h = v)
    (d : A ⟶ pullback (t ≫ (h ≫ f)) f)
    (hdf : d ≫ pullback.fst (t ≫ (h ≫ f)) f = 𝟙 A)
    (hds : d ≫ pullback.snd (t ≫ (h ≫ f)) f = v) :
    d ≫ (RelativeMorphism.restrict t
      (⟨h ≫ f, m, hmc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).morphism = t := by
  have hkey : d ≫ pullback.map (t ≫ (h ≫ f)) f (h ≫ f) f t (𝟙 V) (𝟙 W)
      (by simp) (by simp) = t ≫ diagSection B S hS f h := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.map_fst, ← Category.assoc, hdf, Category.id_comp,
        Category.assoc, diagSection_fst, Category.comp_id]
    · rw [Category.assoc, pullback.map_snd, ← Category.assoc, hds, Category.comp_id,
        Category.assoc, diagSection_snd, hv]
  have hgoal : d ≫ (pullback.map (t ≫ (h ≫ f)) f (h ≫ f) f t (𝟙 V) (𝟙 W)
      (by simp) (by simp) ≫ m) = t := by
    rw [← Category.assoc, hkey, Category.assoc, hmd, Category.comp_id]
  exact hgoal

include hV hY hW

/-- **A morphism `A ×_W V ⟶ Y` over `V` is determined by its restriction to the diagonal.**
On the diagonal part of `A ×_W V` the two morphisms agree because that part factors through the
diagonal section; on the complementary part they agree because a morphism to `Y` over the open
complement of `T` is the unique lift of its image in `V`. -/
theorem excision_morphism_unique_of_diagSection (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hT : IsIso (T.fromPreimage f))
    (hY₀ : IsIso (pullback.snd h ((openComplement B S hS T).preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) (m₁ m₂ : pullback (v ≫ f) f ⟶ Y)
    (h₁ : m₁ ≫ h = pullback.snd (v ≫ f) f) (h₂ : m₂ ≫ h = pullback.snd (v ≫ f) f)
    (hd : diagSection B S hS f v ≫ m₁ = diagSection B S hS f v ≫ m₂) : m₁ = m₂ := by
  obtain ⟨C, hCtop, -, hCsnd⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top
    B S hS hV hW f hf hsep T hT
  have hYsheaf := isSheaf_of_isAlgebraicSpace B S hS hY
  refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top (BigFppfOver.topology B S hS)
    (fun b => pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b))
    (sheafify_iSup_range_diagonalCover B S hS f C hCtop v) hYsheaf ?_
  intro b
  cases b with
  | false =>
    change pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ m₁ =
      pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ m₂
    calc pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ m₁
        = ((pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
              pullback.fst (v ≫ f) f) ≫ diagSection B S hS f v) ≫ m₁ := by
          rw [fst_mapFst_diagonal_fac]
      _ = (pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
              pullback.fst (v ≫ f) f) ≫ (diagSection B S hS f v ≫ m₂) := by
          rw [Category.assoc, hd]
      _ = ((pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
              pullback.fst (v ≫ f) f) ≫ diagSection B S hS f v) ≫ m₂ :=
          (Category.assoc _ _ _).symm
      _ = pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ m₂ := by
          rw [fst_mapFst_diagonal_fac]
  | true =>
    change pullback.fst (pullback.mapFst v f f) C.ι ≫ m₁ =
      pullback.fst (pullback.mapFst v f f) C.ι ≫ m₂
    refine lift_eq_of_isIso_pullback_snd B S hS h hY₀
      (Subfunctor.lift _ (range_fst_mapFst_complement_le B S hS f C T hCsnd v)) _ _ ?_ ?_
    · change (pullback.fst (pullback.mapFst v f f) C.ι ≫ m₁) ≫ h =
        pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f
      rw [Category.assoc, h₁]
    · change (pullback.fst (pullback.mapFst v f f) C.ι ≫ m₂) ≫ h =
        pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f
      rw [Category.assoc, h₂]

/-- **A morphism `A ⟶ Y` over `V` extends, uniquely, to a morphism `A ×_W V ⟶ Y` over `V`.**
On the diagonal part of `A ×_W V` the extension is the given morphism, read off the projection
to `A`; on the complementary part it is the unique lift through `h`, available because that part
lies over the open complement of `T`. The two agree wherever they overlap: their images in `V`
coincide, and over the open complement a section of `Y` is determined by its image in `V`. -/
theorem exists_excision_morphism_of_diagSection (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hT : IsIso (T.fromPreimage f))
    (hY₀ : IsIso (pullback.snd h ((openComplement B S hS T).preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V) (y : A ⟶ Y) (hy : y ≫ h = v) :
    ∃ m : pullback (v ≫ f) f ⟶ Y, m ≫ h = pullback.snd (v ≫ f) f ∧
      diagSection B S hS f v ≫ m = y := by
  obtain ⟨C, hCtop, -, hCsnd⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top
    B S hS hV hW f hf hsep T hT
  have hYsheaf := isSheaf_of_isAlgebraicSpace B S hS hY
  have hVsheaf := isSheaf_of_isAlgebraicSpace B S hS hV
  have hCle := range_fst_mapFst_complement_le B S hS f C T hCsnd v
  obtain ⟨mC, hmC⟩ := exists_lift_of_isIso_pullback_snd B S hS h hY₀
    (pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f)
    (Subfunctor.lift _ hCle) rfl
  obtain ⟨φ₀, hφfalse, hφtrue⟩ :
      ∃ φ₀ : ∀ b : Bool,
          pullback (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b) ⟶ Y,
        φ₀ false = pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
            pullback.fst (v ≫ f) f ≫ y ∧ φ₀ true = mC :=
    ⟨fun b => match b with
      | false => pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
          pullback.fst (v ≫ f) f ≫ y
      | true => mC, rfl, rfl⟩
  have hover : ∀ b, φ₀ b ≫ h = pullback.fst (pullback.mapFst v f f)
      (diagonalCoverHom B S hS f C b) ≫ pullback.snd (v ≫ f) f := by
    intro b
    cases b with
    | false =>
      have e : (pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
            pullback.fst (v ≫ f) f ≫ y) ≫ h =
          pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
            pullback.snd (v ≫ f) f := by
        rw [Category.assoc, Category.assoc, hy]
        exact fst_mapFst_diagonal_comp B S hS f v
      exact (congrArg (fun k => k ≫ h) hφfalse).trans e
    | true =>
      change φ₀ true ≫ h =
        pullback.fst (pullback.mapFst v f f) C.ι ≫ pullback.snd (v ≫ f) f
      rw [hφtrue]
      exact hmC
  have hover' : ∀ (yy : (BigFppfOver B S hS)ᵒᵖ) (b : Bool)
      (c : (pullback (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b)).obj yy),
      h.app yy ((φ₀ b).app yy c) = (pullback.snd (v ≫ f) f).app yy
        ((pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b)).app yy c) := by
    intro yy b c
    have e : (φ₀ b ≫ h).app yy c =
        (pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b) ≫
          pullback.snd (v ≫ f) f).app yy c := by rw [hover b]
    rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply] at e
    exact e
  have hmem : ∀ (yy : (BigFppfOver B S hS)ᵒᵖ)
      (c : (pullback (pullback.mapFst v f f) C.ι).obj yy),
      (pullback.snd (v ≫ f) f).app yy
          ((pullback.fst (pullback.mapFst v f f) C.ι).app yy c) ∈
        ((openComplement B S hS T).preimage f).obj yy := fun yy c => hCle yy ⟨c, rfl⟩
  have hconst : ∀ (yy : (BigFppfOver B S hS)ᵒᵖ) (b₁ b₂ : Bool)
      (c₁ : (pullback (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b₁)).obj yy)
      (c₂ : (pullback (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b₂)).obj yy),
      (pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b₁)).app yy c₁ =
          (pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b₂)).app yy c₂ →
        (φ₀ b₁).app yy c₁ = (φ₀ b₂).app yy c₂ := by
    intro yy b₁ b₂ c₁ c₂ hc
    cases b₁ with
    | false =>
      cases b₂ with
      | false =>
        have e : ∀ c : (pullback (pullback.mapFst v f f) (pullback.diagonal f)).obj yy,
            (φ₀ false).app yy c = (pullback.fst (v ≫ f) f ≫ y).app yy
              ((pullback.fst (pullback.mapFst v f f) (pullback.diagonal f)).app yy c) := by
          intro c
          rw [hφfalse]
          exact NatTrans.comp_app_apply _ _ _ _
        exact (e c₁).trans
          ((congrArg ((pullback.fst (v ≫ f) f ≫ y).app yy) hc).trans (e c₂).symm)
      | true =>
        refine eq_of_app_eq_of_mem_of_isIso_pullback_snd B S hS (A := yy.unop) h hY₀ _
          (hmem yy c₂) _ _ ?_ (hover' yy true c₂)
        exact (hover' yy false c₁).trans
          (congrArg ((pullback.snd (v ≫ f) f).app yy) hc)
    | true =>
      cases b₂ with
      | false =>
        refine eq_of_app_eq_of_mem_of_isIso_pullback_snd B S hS (A := yy.unop) h hY₀ _
          (hmem yy c₁) _ _ (hover' yy true c₁) ?_
        exact (hover' yy false c₂).trans
          (congrArg ((pullback.snd (v ≫ f) f).app yy) hc.symm)
      | true =>
        refine eq_of_app_eq_of_mem_of_isIso_pullback_snd B S hS (A := yy.unop) h hY₀ _
          (hmem yy c₁) _ _ (hover' yy true c₁) ?_
        exact (hover' yy true c₂).trans
          (congrArg ((pullback.snd (v ≫ f) f).app yy) hc.symm)
  obtain ⟨m, hm, -⟩ := Presheaf.existsUnique_hom_of_sheafify_iSup_range_eq_top
    (BigFppfOver.topology B S hS)
    (fun b => pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b))
    (sheafify_iSup_range_diagonalCover B S hS f C hCtop v) hYsheaf φ₀ hconst
  refine ⟨m, ?_, ?_⟩
  · refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top (BigFppfOver.topology B S hS)
      (fun b => pullback.fst (pullback.mapFst v f f) (diagonalCoverHom B S hS f C b))
      (sheafify_iSup_range_diagonalCover B S hS f C hCtop v) hVsheaf ?_
    intro b
    rw [← Category.assoc, hm b]
    exact hover b
  · obtain ⟨u, hu⟩ := exists_comp_fst_mapFst_diagonal B S hS f v
    have hmfalse : pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫ m =
        pullback.fst (pullback.mapFst v f f) (pullback.diagonal f) ≫
          pullback.fst (v ≫ f) f ≫ y := (hm false).trans hφfalse
    rw [← hu, Category.assoc, hmfalse, ← Category.assoc u, hu, ← Category.assoc,
      diagSection_fst, Category.id_comp]

/-- **Two pairs over one section of `W` which lie over `V` and agree along the diagonal are
equal.** -/
theorem relativeMorphism_ext_of_diag (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)
    (T : Subfunctor W) (hT : IsIso (T.fromPreimage f))
    (hY₀ : IsIso (pullback.snd h ((openComplement B S hS T).preimage f).ι))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : A ⟶ V)
    (q₁ q₂ : RelativeMorphism B S hS V Y W f (h ≫ f) A)
    (hb₁ : q₁.base = v ≫ f) (hb₂ : q₂.base = v ≫ f)
    (hm₁ : q₁.morphism ≫ h = pullback.snd q₁.base f)
    (hm₂ : q₂.morphism ≫ h = pullback.snd q₂.base f)
    (d₁ : A ⟶ pullback q₁.base f) (d₂ : A ⟶ pullback q₂.base f)
    (hd₁f : d₁ ≫ pullback.fst q₁.base f = 𝟙 A) (hd₁s : d₁ ≫ pullback.snd q₁.base f = v)
    (hd₂f : d₂ ≫ pullback.fst q₂.base f = 𝟙 A) (hd₂s : d₂ ≫ pullback.snd q₂.base f = v)
    (hd : d₁ ≫ q₁.morphism = d₂ ≫ q₂.morphism) : q₁ = q₂ := by
  obtain ⟨b₁, m₁, c₁⟩ := q₁
  obtain ⟨b₂, m₂, c₂⟩ := q₂
  subst hb₁
  subst hb₂
  have he₁ : d₁ = diagSection B S hS f v :=
    pullback.hom_ext (by rw [hd₁f, diagSection_fst]) (by rw [hd₁s, diagSection_snd])
  have he₂ : d₂ = diagSection B S hS f v :=
    pullback.hom_ext (by rw [hd₂f, diagSection_fst]) (by rw [hd₂s, diagSection_snd])
  simp only [RelativeMorphism.mk.injEq, heq_eq_eq, true_and]
  refine excision_morphism_unique_of_diagSection B S hS f h hV hY hW hf hsep T hT hY₀ v
    m₁ m₂ hm₁ hm₂ ?_
  rwa [he₁, he₂] at hd

/-- **The base change of the pushforward along `f` is `Y`.** Over a test object `T'`, a section
of the base change is a morphism `v : T' ⟶ V` together with a pair over `f ∘ v`, that is, a
morphism `T' ×_W V ⟶ Y` over `V`; restricting such a morphism to the diagonal copy of `T'` is a
bijection onto the sections of `Y` over `T'`.

The morphism `Y ⟶ (pushforward) ×_W V` realizing the inverse is built once and for all from the
*universal* pair: the morphism `Y ×_W V ⟶ Y` over `V` whose restriction to the diagonal is the
identity of `Y`. Its restrictions along the morphisms `yoneda.obj T' ⟶ Y` naming the sections of
`Y` are the required pairs, and their compatibility with restriction is the functoriality of
`AlgebraicGeometry.Space.RelativeMorphism.restrict`. -/
theorem exists_iso_pullback_excisionProjection (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hT : IsIso (T.fromPreimage f))
    (hY₀ : IsIso (pullback.snd h ((openComplement B S hS T).preimage f).ι)) :
    ∃ e : pullback (excisionProjection B S hS f h hV hY hW) f ≅ Y,
      e.hom ≫ h = pullback.snd (excisionProjection B S hS f h hV hY hW) f := by
  classical
  -- the universal pair over `Y`
  obtain ⟨mY, hmY, hmYd⟩ := exists_excision_morphism_of_diagSection B S hS f h hV hY hW
    hf hsep T hT hY₀ h (𝟙 Y) (Category.id_comp h)
  have hmYc : mY ≫ (h ≫ f) = pullback.snd (h ≫ f) f ≫ f := by rw [← Category.assoc, hmY]
  -- the section of the pushforward attached to a morphism `yoneda.obj T' ⟶ Y`
  have hsec : ∀ (T' : BigFppfOver B S hS) (t : yoneda.obj T' ⟶ Y),
      ∃ p : (excisionPushforward B S hS f h hV hY hW).obj (op T'),
        excisionSections B S hS f h hV hY hW T' p =
          RelativeMorphism.restrict t (⟨h ≫ f, mY, hmYc⟩ :
            RelativeMorphism B S hS V Y W f (h ≫ f) Y) := by
    intro T' t
    have hmem : ((relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW T').symm
        (RelativeMorphism.restrict t (⟨h ≫ f, mY, hmYc⟩ :
          RelativeMorphism B S hS V Y W f (h ≫ f) Y))) ∈
        (excisionSubfunctor B S hS f h hV hY hW).obj (op T') :=
      morphism_comp_eq_of_eq B S hS f h (Equiv.apply_symm_apply _ _)
        (restrict_morphism_comp_eq B S hS f h t _ hmY)
    exact ⟨⟨_, hmem⟩, Equiv.apply_symm_apply _ _⟩
  choose Pt hPt using hsec
  -- the morphism from `Y` to the pushforward
  obtain ⟨Φ₁, hΦ₁⟩ : ∃ Φ₁ : Y ⟶ excisionPushforward B S hS f h hV hY hW,
      ∀ (D : (BigFppfOver B S hS)ᵒᵖ) (y₀ : Y.obj D),
        Φ₁.app D y₀ = Pt D.unop (yonedaEquiv.symm y₀) := by
    refine ⟨{ app := fun D => ↾fun y₀ => Pt D.unop (yonedaEquiv.symm y₀), naturality := ?_ },
      fun _ _ => rfl⟩
    intro D D' g
    refine TypeCat.homEquiv.injective (funext fun y₀ => ?_)
    simp only [TypeCat.homEquiv_apply, types_comp_apply, TypeCat.ofHom_apply]
    refine excision_obj_ext B S hS f h hV hY hW D'.unop _ _ ?_
    have e1 : excisionSections B S hS f h hV hY hW D'.unop
        ((excisionPushforward B S hS f h hV hY hW).map g
          (Pt D.unop (yonedaEquiv.symm y₀))) =
        RelativeMorphism.restrict (yoneda.map g.unop)
          (excisionSections B S hS f h hV hY hW D.unop
            (Pt D.unop (yonedaEquiv.symm y₀))) :=
      excisionSections_map B S hS f h hV hY hW g.unop _
    rw [hPt, e1, hPt, RelativeMorphism.restrict_comp, yonedaEquiv_symm_map]
  -- it lies over `W`
  have hcond : Φ₁ ≫ excisionProjection B S hS f h hV hY hW = h ≫ f := by
    refine Stacks.Sites.CoverDescent.natTrans_ext fun D y₀ => ?_
    have e2 : (excisionSections B S hS f h hV hY hW D.unop (Φ₁.app D y₀)).base =
        yonedaEquiv.symm y₀ ≫ (h ≫ f) := by
      rw [hΦ₁, hPt]
      exact RelativeMorphism.restrict_base _ _
    calc (Φ₁ ≫ excisionProjection B S hS f h hV hY hW).app D y₀
        = (excisionProjection B S hS f h hV hY hW).app D (Φ₁.app D y₀) :=
          NatTrans.comp_app_apply _ _ _ _
      _ = yonedaEquiv (excisionSections B S hS f h hV hY hW D.unop (Φ₁.app D y₀)).base :=
          excisionProjection_app B S hS f h hV hY hW D.unop _
      _ = yonedaEquiv (yonedaEquiv.symm y₀ ≫ (h ≫ f)) := by rw [e2]
      _ = (h ≫ f).app D y₀ := by
          rw [yonedaEquiv_comp]
          exact congrArg ((h ≫ f).app D) (Equiv.apply_symm_apply _ _)
  -- the two components of the lifted morphism
  have hAppFst : ∀ (D : (BigFppfOver B S hS)ᵒᵖ) (y₀ : Y.obj D),
      (pullback.fst (excisionProjection B S hS f h hV hY hW) f).app D
        ((pullback.lift Φ₁ h hcond).app D y₀) = Φ₁.app D y₀ := by
    intro D y₀
    rw [← NatTrans.comp_app_apply, pullback.lift_fst]
  have hAppSnd : ∀ (D : (BigFppfOver B S hS)ᵒᵖ) (y₀ : Y.obj D),
      (pullback.snd (excisionProjection B S hS f h hV hY hW) f).app D
        ((pullback.lift Φ₁ h hcond).app D y₀) = h.app D y₀ := by
    intro D y₀
    rw [← NatTrans.comp_app_apply, pullback.lift_snd]
  -- restatements of the section-level tools at an arbitrary opposite object
  have hoverApp : ∀ (D : (BigFppfOver B S hS)ᵒᵖ)
      (p : (excisionPushforward B S hS f h hV hY hW).obj D),
      (excisionSections B S hS f h hV hY hW D.unop p).morphism ≫ h =
        pullback.snd (excisionSections B S hS f h hV hY hW D.unop p).base f :=
    fun D p => excisionSections_comp B S hS f h hV hY hW D.unop p
  have hyon : ∀ (G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (D : (BigFppfOver B S hS)ᵒᵖ)
      (φ : G ⟶ F) (x : G.obj D), yonedaEquiv.symm x ≫ φ = yonedaEquiv.symm (φ.app D x) :=
    fun _ _ D φ x => yonedaEquiv_symm_naturality_right D.unop φ x
  -- the transport used to compare two diagonal sections of equal pairs
  have hdiagkey : ∀ (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (v : A ⟶ V)
      (q q' : RelativeMorphism B S hS V Y W f (h ≫ f) A), q = q' →
      ∀ (d : A ⟶ pullback q.base f) (d' : A ⟶ pullback q'.base f),
        d ≫ pullback.fst q.base f = 𝟙 A → d ≫ pullback.snd q.base f = v →
        d' ≫ pullback.fst q'.base f = 𝟙 A → d' ≫ pullback.snd q'.base f = v →
        d ≫ q.morphism = d' ≫ q'.morphism := by
    rintro A v q q' rfl d d' h1 h2 h3 h4
    rw [show d = d' from pullback.hom_ext (by rw [h1, h3]) (by rw [h2, h4])]
  -- injectivity
  have hinj : ∀ D : (BigFppfOver B S hS)ᵒᵖ,
      Function.Injective ((pullback.lift Φ₁ h hcond).app D) := by
    intro D y₁ y₂ hy
    have hv : h.app D y₁ = h.app D y₂ := by rw [← hAppSnd D y₁, ← hAppSnd D y₂, hy]
    have hq : RelativeMorphism.restrict (yonedaEquiv.symm y₁)
          (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y) =
        RelativeMorphism.restrict (yonedaEquiv.symm y₂)
          (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y) := by
      rw [← hPt, ← hPt, ← hΦ₁, ← hΦ₁, ← hAppFst D y₁, ← hAppFst D y₂, hy]
    have hvv : yonedaEquiv.symm y₂ ≫ h = yonedaEquiv.symm y₁ ≫ h := by
      rw [hyon _ _ D h y₁, hyon _ _ D h y₂, hv]
    have hb₁ : (RelativeMorphism.restrict (yonedaEquiv.symm y₁)
        (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).base =
        (yonedaEquiv.symm y₁ ≫ h) ≫ f := by
      change yonedaEquiv.symm y₁ ≫ (h ≫ f) = (yonedaEquiv.symm y₁ ≫ h) ≫ f
      rw [Category.assoc]
    have hb₂ : (RelativeMorphism.restrict (yonedaEquiv.symm y₂)
        (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).base =
        (yonedaEquiv.symm y₁ ≫ h) ≫ f := by
      change yonedaEquiv.symm y₂ ≫ (h ≫ f) = (yonedaEquiv.symm y₁ ≫ h) ≫ f
      rw [← Category.assoc, hvv]
    obtain ⟨d₁, hd₁f, hd₁s⟩ := exists_diag_of_base_eq B S hS f h (yonedaEquiv.symm y₁ ≫ h) _ hb₁
    obtain ⟨d₂, hd₂f, hd₂s⟩ := exists_diag_of_base_eq B S hS f h (yonedaEquiv.symm y₁ ≫ h) _ hb₂
    have e₁ : d₁ ≫ (RelativeMorphism.restrict (yonedaEquiv.symm y₁)
        (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).morphism =
        yonedaEquiv.symm y₁ :=
      comp_restrict_morphism B S hS f h mY hmYc hmYd (yonedaEquiv.symm y₁) _ rfl d₁ hd₁f hd₁s
    have e₂ : d₂ ≫ (RelativeMorphism.restrict (yonedaEquiv.symm y₂)
        (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).morphism =
        yonedaEquiv.symm y₂ :=
      comp_restrict_morphism B S hS f h mY hmYc hmYd (yonedaEquiv.symm y₂) _ hvv d₂ hd₂f hd₂s
    refine yonedaEquiv.symm.injective (e₁.symm.trans ((hdiagkey _ (yonedaEquiv.symm y₁ ≫ h)
      _ _ hq d₁ d₂ hd₁f hd₁s hd₂f hd₂s).trans e₂))
  -- surjectivity
  have hsurj : ∀ D : (BigFppfOver B S hS)ᵒᵖ,
      Function.Surjective ((pullback.lift Φ₁ h hcond).app D) := by
    intro D c
    obtain ⟨p, v₀, hp, hv₀⟩ : ∃ (p : (excisionPushforward B S hS f h hV hY hW).obj D)
        (v₀ : V.obj D),
        (pullback.fst (excisionProjection B S hS f h hV hY hW) f).app D c = p ∧
          (pullback.snd (excisionProjection B S hS f h hV hY hW) f).app D c = v₀ :=
      ⟨_, _, rfl, rfl⟩
    have hπ : (excisionProjection B S hS f h hV hY hW).app D p = f.app D v₀ := by
      have e : (pullback.fst (excisionProjection B S hS f h hV hY hW) f ≫
            excisionProjection B S hS f h hV hY hW).app D c =
          (pullback.snd (excisionProjection B S hS f h hV hY hW) f ≫ f).app D c := by
        rw [pullback.condition]
      rwa [NatTrans.comp_app_apply, NatTrans.comp_app_apply, hp, hv₀] at e
    have hqb : (excisionSections B S hS f h hV hY hW D.unop p).base =
        yonedaEquiv.symm v₀ ≫ f := by
      rw [hyon _ _ D f v₀]
      exact yonedaEquiv.eq_symm_apply.2
        ((excisionProjection_app B S hS f h hV hY hW D.unop p).symm.trans hπ)
    obtain ⟨d, hdf, hds⟩ := exists_diag_of_base_eq B S hS f h (yonedaEquiv.symm v₀) _ hqb
    have ht : (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism) ≫ h =
        yonedaEquiv.symm v₀ := by rw [Category.assoc, hoverApp D p, hds]
    refine ⟨yonedaEquiv (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism), ?_⟩
    have htsymm : yonedaEquiv.symm
        (yonedaEquiv (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism)) =
        d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism :=
      Equiv.symm_apply_apply _ _
    refine pullback_obj_ext (excisionProjection B S hS f h hV hY hW) f D _ c ?_ ?_
    · rw [hAppFst, hΦ₁, hp, htsymm]
      refine excision_obj_ext B S hS f h hV hY hW D.unop _ _ ?_
      rw [hPt]
      have hb₁ : (RelativeMorphism.restrict
          (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism)
          (⟨h ≫ f, mY, hmYc⟩ : RelativeMorphism B S hS V Y W f (h ≫ f) Y)).base =
          yonedaEquiv.symm v₀ ≫ f := by
        change (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism) ≫ (h ≫ f) =
          yonedaEquiv.symm v₀ ≫ f
        rw [← Category.assoc, ht]
      obtain ⟨d₁, hd₁f, hd₁s⟩ :=
        exists_diag_of_base_eq B S hS f h (yonedaEquiv.symm v₀) _ hb₁
      refine relativeMorphism_ext_of_diag B S hS f h hV hY hW hf hsep T hT hY₀
        (yonedaEquiv.symm v₀) _ _ hb₁ hqb
        (restrict_morphism_comp_eq B S hS f h _ _ hmY) (hoverApp D p) d₁ d hd₁f hd₁s hdf hds ?_
      exact comp_restrict_morphism B S hS f h mY hmYc hmYd
        (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism) _ ht d₁ hd₁f hd₁s
    · rw [hAppSnd, hv₀]
      have e1 : yonedaEquiv
          ((d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism) ≫ h) =
          h.app D (yonedaEquiv
            (d ≫ (excisionSections B S hS f h hV hY hW D.unop p).morphism)) :=
        yonedaEquiv_comp _ _
      rw [ht, Equiv.apply_symm_apply] at e1
      exact e1.symm
  -- hence the base change is isomorphic to `Y`
  have : ∀ D, IsIso ((pullback.lift Φ₁ h hcond).app D) := fun D =>
    (isIso_iff_bijective _).2 ⟨hinj D, hsurj D⟩
  have : IsIso (pullback.lift Φ₁ h hcond) := NatIso.isIso_of_isIso_app _
  refine ⟨(asIso (pullback.lift Φ₁ h hcond)).symm, ?_⟩
  change inv (pullback.lift Φ₁ h hcond) ≫ h =
    pullback.snd (excisionProjection B S hS f h hV hY hW) f
  rw [IsIso.inv_comp_eq, pullback.lift_snd]

end Diagonal

end AlgebraicGeometry.Space

end
