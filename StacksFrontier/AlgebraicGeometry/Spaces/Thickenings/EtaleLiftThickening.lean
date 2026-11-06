module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unique lifting into an étale algebraic space across a thickening of arbitrary order

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, and let `T ⊂ T'` be
a thickening of algebraic spaces over `S` of **arbitrary** order. This file proves that a solid
square over `T ⊂ T'` with right-hand side `f` has exactly one dotted arrow: every morphism
`T ⟶ X` over `Y` extends uniquely to `T' ⟶ X` over `Y`.

This is the étale case of Stacks 0611 with the order hypothesis removed. Stacks 0611 itself,
`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening`, holds for a
merely *formally* étale `f` but only at a thickening of order one: its proof instantiates the
order to obtain a square-zero ideal, which is what the definition of formal étaleness, Stacks
049S part (2), tests against. For an actually étale `f` no such instantiation is needed, because
the scheme-level extension of a section across a thickening — Stacks 025H,
`Stacks.Etale.exists_lift_of_surjective_closedImmersion`, together with its uniqueness companion
`Stacks.Etale.hom_ext_of_surjective` — asks only for a closed immersion surjective on points.

## Main results

* `AlgebraicGeometry.Space.Etale.existsUnique_lift_site_of_isThickening`: the chart case. For a
  closed immersion `i : U₀ ⟶ U` of objects of the big fppf site which is surjective on points,
  a morphism `yoneda.obj U₀ ⟶ X` over `Y` extends uniquely to `yoneda.obj U ⟶ X` over `Y`.
* `AlgebraicGeometry.Space.Etale.hom_ext_site_of_isThickening`: the uniqueness half of the
  previous statement, as an extensionality lemma.
* `AlgebraicGeometry.Space.Etale.existsUnique_lift_of_isThickening`: **the étale case of
  Stacks 0611 at a thickening of arbitrary order**, for a thickening of algebraic spaces.

## Implementation notes

**The chart case.** Because `f` is étale it is relatively representable, so its base change
along `b : yoneda.obj U ⟶ Y` is an object `E` of the site with `E ⟶ U` étale as a morphism of
schemes. A morphism `yoneda.obj U ⟶ X` over `b` is then the same datum as a section of
`E ⟶ U`, and a morphism `yoneda.obj U₀ ⟶ X` over `yoneda.map i ≫ b` the same datum as a section
over `U₀`. So the statement is exactly the extension of a section of an étale morphism across a
closed immersion surjective on points, which is Stacks 025H; the extended section is a morphism
of schemes and becomes a morphism of the site by
`AlgebraicGeometry.BigFppfOver.homOfCompEq`, because it is a section. Uniqueness is
`Stacks.Etale.hom_ext_of_surjective`, which needs only the surjectivity.

**From the chart case to a thickening of algebraic spaces.** The descent is the one the proof of
Stacks 0611 performs: a surjective étale atlas `q : yoneda.obj U ⟶ T'` of the ambient space
restricts the thickening to a closed immersion of site objects surjective on points, by
`AlgebraicGeometry.Space.exists_thickening_chart_pullback_subfunctor` — which asks nothing of
the chart, in particular not that it be étale, and nothing of the order; the chart case lifts
the given morphism over the atlas; the lift is invariant under the kernel pair of the atlas, by
the uniqueness half of the chart case applied over the restriction of the thickening to the
kernel pair; and the atlas presents `T'` as the coequalizer of its kernel pair in sheaves of
sets, by Stacks 0262 part (3) in the form
`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`, so the invariant lift descends.
That the descended arrow restricts to the given one on `T` is tested against the epimorphism
`yoneda.obj U₀ ⟶ T`, which is a surjective étale chart of `T`.

## References

* [Stacks Project, Tag 025H](https://stacks.math.columbia.edu/tag/025H)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart case -/

section Site

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

variable (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)

/-- A morphism `yoneda.obj U ⟶ X` lying over `b` is a section of the base change of `f` along
`b`, which is a morphism of the site because that base change is an object of the site. -/
private noncomputable def etaleRepSection {U : BigFppfOver B S hS} {b : yoneda.obj U ⟶ Y}
    (c : yoneda.obj U ⟶ X) (hc : c ≫ f = b) : U ⟶ hf.rep.pullback b :=
  hf.rep.lift c (𝟙 U) (by rw [hc, CategoryTheory.Functor.map_id, Category.id_comp])

private theorem etaleRepSection_fst {U : BigFppfOver B S hS} {b : yoneda.obj U ⟶ Y}
    (c : yoneda.obj U ⟶ X) (hc : c ≫ f = b) :
    yoneda.map (etaleRepSection B S hS hf c hc) ≫ hf.rep.fst b = c :=
  hf.rep.lift_fst _ _ _

private theorem etaleRepSection_snd {U : BigFppfOver B S hS} {b : yoneda.obj U ⟶ Y}
    (c : yoneda.obj U ⟶ X) (hc : c ≫ f = b) :
    etaleRepSection B S hS hf c hc ≫ hf.rep.snd b = 𝟙 U :=
  hf.rep.lift_snd _ _ _

/-- **Uniqueness of a lift into an étale algebraic space across a thickening of site objects.**
Two morphisms `yoneda.obj U ⟶ X` lying over the same morphism to `Y`, which agree after
restriction along a morphism of the site surjective on points, are equal.

Both are sections of the base change of `f` along `b`, which is étale, and
`Stacks.Etale.hom_ext_of_surjective` identifies two sections of an étale morphism agreeing after
a morphism surjective on points. No closed immersion hypothesis is used, and nothing is assumed
about the order of the thickening. -/
theorem Etale.hom_ext_site_of_isThickening (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    {U₀ U : BigFppfOver B S hS} (i : U₀ ⟶ U)
    (hsj : Function.Surjective ((BigFppfOver.toScheme B S hS).map i).base)
    {b : yoneda.obj U ⟶ Y} (c₁ c₂ : yoneda.obj U ⟶ X) (hc₁ : c₁ ≫ f = b) (hc₂ : c₂ ≫ f = b)
    (h : yoneda.map i ≫ c₁ = yoneda.map i ≫ c₂) : c₁ = c₂ := by
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hf.rep.snd b)) :=
    hf.property_snd b
  -- The two sections agree after restriction along `i`, by the universal property of the base
  -- change: they agree over `X` by hypothesis and over `U` because both are sections.
  have hiτ : i ≫ etaleRepSection B S hS hf c₁ hc₁ = i ≫ etaleRepSection B S hS hf c₂ hc₂ := by
    refine hf.rep.hom_ext ?_ ?_
    · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        etaleRepSection_fst B S hS hf c₁ hc₁, etaleRepSection_fst B S hS hf c₂ hc₂, h]
    · rw [Category.assoc, Category.assoc, etaleRepSection_snd B S hS hf c₁ hc₁,
        etaleRepSection_snd B S hS hf c₂ hc₂]
  have hτ : etaleRepSection B S hS hf c₁ hc₁ = etaleRepSection B S hS hf c₂ hc₂ :=
    (BigFppfOver.toScheme B S hS).map_injective
      (Stacks.Etale.hom_ext_of_surjective ((BigFppfOver.toScheme B S hS).map i) hsj
        ((BigFppfOver.toScheme B S hS).map (hf.rep.snd b)) _ _
        (by rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp,
          etaleRepSection_snd B S hS hf c₁ hc₁, etaleRepSection_snd B S hS hf c₂ hc₂])
        (by rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hiτ]))
  calc c₁ = yoneda.map (etaleRepSection B S hS hf c₁ hc₁) ≫ hf.rep.fst b :=
        (etaleRepSection_fst B S hS hf c₁ hc₁).symm
    _ = yoneda.map (etaleRepSection B S hS hf c₂ hc₂) ≫ hf.rep.fst b := by rw [hτ]
    _ = c₂ := etaleRepSection_fst B S hS hf c₂ hc₂

/-- **The chart case of unique lifting into an étale algebraic space across a thickening of
arbitrary order.** Let `i : U₀ ⟶ U` be a closed immersion of objects of the big fppf site over
`S` which is surjective on points, and let `f : X ⟶ Y` be an étale morphism of presheaves on the
site, in the relatively representable sense. Every morphism `yoneda.obj U₀ ⟶ X` lying over a
morphism `b : yoneda.obj U ⟶ Y` extends uniquely to a morphism `yoneda.obj U ⟶ X` over `b`.

Nothing is assumed about the order of the thickening: the extension is Stacks 025H,
`Stacks.Etale.exists_lift_of_surjective_closedImmersion`, which asks only for a closed immersion
surjective on points. -/
@[sga "1 I 5.6" "more general"]
theorem Etale.existsUnique_lift_site_of_isThickening (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    {U₀ U : BigFppfOver B S hS} (i : U₀ ⟶ U)
    (hci : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hsj : Function.Surjective ((BigFppfOver.toScheme B S hS).map i).base)
    (a : yoneda.obj U₀ ⟶ X) (b : yoneda.obj U ⟶ Y)
    (hsq : a ≫ f = yoneda.map i ≫ b) :
    ∃! c : yoneda.obj U ⟶ X, yoneda.map i ≫ c = a ∧ c ≫ f = b := by
  classical
  have := hci
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hf.rep.snd b)) :=
    hf.property_snd b
  -- `a` is a section of the base change of `f` along `b`, over the closed subscheme `U₀`.
  have hg₀fst : yoneda.map (hf.rep.lift a i hsq) ≫ hf.rep.fst b = a := hf.rep.lift_fst _ _ _
  have hg₀snd : hf.rep.lift a i hsq ≫ hf.rep.snd b = i := hf.rep.lift_snd _ _ _
  -- Stacks 025H extends it to a section over `U`.
  obtain ⟨σ, hσ₁, hσ₂⟩ := Stacks.Etale.exists_lift_of_surjective_closedImmersion
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd b))
    (𝟙 ((BigFppfOver.toScheme B S hS).obj U))
    ((BigFppfOver.toScheme B S hS).map i) hsj
    ((BigFppfOver.toScheme B S hS).map (hf.rep.lift a i hsq))
    (by rw [Category.comp_id, ← (BigFppfOver.toScheme B S hS).map_comp, hg₀snd])
  -- A section of a morphism of the site is itself a morphism of the site.
  have hQ : (BigFppfOver.toScheme B S hS).map (hf.rep.snd b) ≫ B.inclusion.map U.hom =
      B.inclusion.map (hf.rep.pullback b).hom := by
    show B.inclusion.map (hf.rep.snd b).left ≫ B.inclusion.map U.hom = _
    rw [← B.inclusion.map_comp, Over.w]
  have hcomp : σ ≫ B.inclusion.map (hf.rep.pullback b).hom = B.inclusion.map U.hom := by
    rw [← hQ, ← Category.assoc, hσ₁, Category.id_comp]
  have hτmap : (BigFppfOver.toScheme B S hS).map (BigFppfOver.homOfCompEq B S hS σ hcomp) = σ :=
    BigFppfOver.toScheme_map_homOfCompEq B S hS σ hcomp
  have hτsnd : BigFppfOver.homOfCompEq B S hS σ hcomp ≫ hf.rep.snd b = 𝟙 U :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [(BigFppfOver.toScheme B S hS).map_comp, hτmap, hσ₁,
        (BigFppfOver.toScheme B S hS).map_id])
  have hτi : i ≫ BigFppfOver.homOfCompEq B S hS σ hcomp = hf.rep.lift a i hsq :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [(BigFppfOver.toScheme B S hS).map_comp, hτmap, hσ₂])
  have hlift : (yoneda.map (BigFppfOver.homOfCompEq B S hS σ hcomp) ≫ hf.rep.fst b) ≫ f = b := by
    rw [Category.assoc, hf.rep.w b, ← Category.assoc, ← Functor.map_comp, hτsnd,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hrestrict : yoneda.map i ≫ yoneda.map (BigFppfOver.homOfCompEq B S hS σ hcomp) ≫
      hf.rep.fst b = a := by
    rw [← Category.assoc, ← Functor.map_comp, hτi, hg₀fst]
  exact ⟨_, ⟨hrestrict, hlift⟩, fun c' hc' ↦
    Etale.hom_ext_site_of_isThickening B S hS hf i hsj c' _ hc'.2 hlift
      (by rw [hc'.1, hrestrict])⟩

end Site

/-- Two morphisms of presheaves out of the underlying presheaf of a sheaf agree if they agree
after precomposition with an epimorphism of sheaves. -/
private theorem eq_of_epi_sheaf_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G H : Sheaf J (Type u)} (e : F ⟶ G) [Epi e] {g h : G.obj ⟶ H.obj}
    (hgh : e.hom ≫ g = e.hom ≫ h) : g = h :=
  Sheaf.hom_ext_iff.1 ((cancel_epi e).1
    (Sheaf.hom_ext hgh : e ≫ (⟨g⟩ : G ⟶ H) = e ≫ (⟨h⟩ : G ⟶ H)))

/-! ### A thickening of algebraic spaces of arbitrary order -/

/-- **The étale case of Stacks 0611, at a thickening of ARBITRARY order.** An étale morphism
`f : X ⟶ Y` of algebraic spaces over `S` admits exactly one dotted arrow in a solid square over
a thickening `T ⊂ T'` of algebraic spaces over `S`. No affineness is assumed of either space of
the thickening, and — unlike
`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening`, which is the
tag for a merely formally étale `f` — no bound on the order of the thickening.

A surjective étale atlas `q` of the ambient space restricts the thickening to a closed immersion
of objects of the site which is surjective on points, by
`AlgebraicGeometry.Space.exists_thickening_chart_pullback_subfunctor`; the chart case
`AlgebraicGeometry.Space.Etale.existsUnique_lift_site_of_isThickening` lifts the given morphism
over the atlas; that lift is invariant under the kernel pair of the atlas, because the
restriction of the thickening to the kernel pair is again a closed immersion surjective on
points and `AlgebraicGeometry.Space.Etale.hom_ext_site_of_isThickening` applies there; and the
atlas presents `T'` as the coequalizer of its kernel pair in sheaves of sets, by Stacks 0262
part (3) in the form `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`, so the
invariant lift descends. Uniqueness is the chart case again, read after the atlas, which is an
epimorphism of sheaves. -/
@[sga "3 XI 1.5" "Étale case"]
theorem Etale.existsUnique_lift_of_isThickening
    {X Y T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (T : Subfunctor T'.obj) (hT : IsThickening B S hS T' T)
    (a : T.toFunctor ⟶ X.obj) (b : T'.obj ⟶ Y.obj) (hsq : a ≫ f.hom = T.ι ≫ b) :
    ∃! c : T'.obj ⟶ X.obj, T.ι ≫ c = a ∧ c ≫ f.hom = b := by
  classical
  -- A surjective étale atlas of the ambient space, and the thickening of site objects that the
  -- given thickening restricts to over it.
  obtain ⟨U, q, hqS, hqE⟩ := T'.property.exists_atlas
  obtain ⟨U₀, i, p, hpb, hthick⟩ := exists_thickening_chart_pullback_subfunctor B S hS hT U q
  have hci : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    hthick.1
  have hsj : Function.Surjective ((BigFppfOver.toScheme B S hS).map i).base := hthick.2
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := Etale.existsUnique_lift_site_of_isThickening B S hS hf i hci hsj
    (p ≫ a) (q ≫ b) (by rw [Category.assoc, hsq, ← Category.assoc, hpb.w, Category.assoc])
  -- The kernel pair of the atlas, and the invariance of the lift under it.
  let rep := T'.property.diagonal_representable.of_diag q
  let R := rep.pullback q
  let s : R ⟶ U := rep.fst' q
  let t : R ⟶ U := rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := rep.isPullback' q
  have hinv : yoneda.map s ≫ c = yoneda.map t ≫ c := by
    obtain ⟨R₀, j, pR, hpbR, hthickR⟩ :=
      exists_thickening_chart_pullback_subfunctor B S hS hT R (yoneda.map s ≫ q)
    have key (v : R ⟶ U) (hv : yoneda.map v ≫ q = yoneda.map s ≫ q) :
        yoneda.map j ≫ yoneda.map v ≫ c = pR ≫ a ∧
          (yoneda.map v ≫ c) ≫ f.hom = (yoneda.map s ≫ q) ≫ b := by
      have hw : pR ≫ T.ι = yoneda.map (j ≫ v) ≫ q := by
        rw [hpbR.w, Functor.map_comp, Category.assoc, hv]
      refine ⟨?_, ?_⟩
      · calc yoneda.map j ≫ yoneda.map v ≫ c = yoneda.map (j ≫ v) ≫ c := by
              rw [Functor.map_comp, Category.assoc]
          _ = (hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ yoneda.map i) ≫ c := by
              rw [hpb.lift_snd]
          _ = hpb.lift pR (yoneda.map (j ≫ v)) hw ≫ p ≫ a := by rw [Category.assoc, hc₁]
          _ = pR ≫ a := by rw [← Category.assoc, hpb.lift_fst]
      · calc (yoneda.map v ≫ c) ≫ f.hom = yoneda.map v ≫ q ≫ b := by
              rw [Category.assoc, hc₂]
          _ = (yoneda.map v ≫ q) ≫ b := by rw [Category.assoc]
          _ = (yoneda.map s ≫ q) ≫ b := by rw [hv]
    exact Etale.hom_ext_site_of_isThickening B S hS hf j hthickR.2 _ _
      (key s rfl).2 (key t hR.w.symm).2 (by rw [(key s rfl).1, (key t hR.w.symm).1])
  -- The atlas presents `T'` as the coequalizer of its kernel pair, so the lift descends.
  let J := BigFppfOver.topology B S hS
  let hcolimit := isCoequalizer_of_surjectiveEtale B S hS q s t hR T'.property hqS hqE
  let hRsh := Classical.choose hcolimit
  have hcolimitU := Classical.choose_spec hcolimit
  let hUsh := Classical.choose hcolimitU
  have hcolimitC := Classical.choose_spec hcolimitU
  let hc := Classical.choice hcolimitC
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let T'F : Sheaf J (Type u) := ⟨T'.obj, T'.property.isSheaf⟩
  let XF : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let YF : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let qf : UF ⟶ T'F := ⟨q⟩
  have hwc : sf ≫ (⟨c⟩ : UF ⟶ XF) = tf ≫ (⟨c⟩ : UF ⟶ XF) := Sheaf.hom_ext hinv
  let cofork : Cofork sf tf := Cofork.ofπ (⟨c⟩ : UF ⟶ XF) hwc
  let dsh := hc.desc cofork
  have hfac : qf ≫ dsh = (⟨c⟩ : UF ⟶ XF) := by
    exact hc.fac cofork WalkingParallelPair.one
  have hqd : q ≫ dsh.hom = c := congrArg (fun φ ↦ φ.hom) hfac
  have hqepi : Epi qf := Cofork.IsColimit.epi hc
  -- The descended arrow solves the original lifting problem.
  have hd₂ : dsh.hom ≫ f.hom = b := by
    refine eq_of_epi_sheaf_hom (H := YF) qf (g := dsh.hom ≫ f.hom) (h := b) ?_
    change q ≫ _ = q ≫ _
    rw [← Category.assoc, hqd, hc₂]
  have hd₁ : T.ι ≫ dsh.hom = a := by
    have hstabS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hstabE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hpS := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqS
    have hpE := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hqE
    let U₀F : Sheaf J (Type u) := ⟨yoneda.obj U₀, BigFppfOver.isSheaf_yoneda_obj B S hS U₀⟩
    let TF : Sheaf J (Type u) := ⟨T.toFunctor, hT.1.1.isSheaf⟩
    let pf : U₀F ⟶ TF := ⟨p⟩
    have _ : Sheaf.IsLocallySurjective pf :=
      isLocallySurjective_of_surjective_etale B S hS p hpS hpE
    have _ : Epi pf := inferInstance
    refine eq_of_epi_sheaf_hom (H := XF) pf (g := T.ι ≫ dsh.hom) (h := a) ?_
    change p ≫ _ = p ≫ _
    rw [reassoc_of% hpb.w, hqd, hc₁]
  refine ⟨dsh.hom, ⟨hd₁, hd₂⟩, fun c' hc' ↦ ?_⟩
  have hqc : q ≫ c' = q ≫ dsh.hom :=
    Etale.hom_ext_site_of_isThickening B S hS hf i hsj (q ≫ c') (q ≫ dsh.hom)
      (by rw [Category.assoc, hc'.2]) (by rw [Category.assoc, hd₂])
      (by rw [← reassoc_of% hpb.w, ← reassoc_of% hpb.w, hc'.1, hd₁])
  exact eq_of_epi_sheaf_hom (H := XF) qf hqc

/-! ### The presheaf form, at a thickening of arbitrary order -/

/-- **Unique extension of morphisms into an étale algebraic space across a thickening of
arbitrary order, at the level of presheaves.** Let `f : X ⟶ Y` be a monomorphism whose range is
a thickening of `Y`, of arbitrary order; let `π : H ⟶ F` be a base change of `f` along a
morphism `v : F ⟶ Y.1` with `F` an algebraic space; and let `w : G ⟶ Y.1` be étale, in the
relatively representable sense, with `G` an algebraic space. Every morphism `H ⟶ G` over `Y`
extends uniquely to a morphism `F ⟶ G` over `Y`.

This is `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isFirstOrderThickening` with the
order hypothesis removed and formal étaleness of `w` strengthened to étaleness, which is what
pays for the removal. The thickening to extend across is the inverse image of
`CategoryTheory.Subfunctor.range f.hom` along `v`, a thickening by Stacks 09ZX
(`AlgebraicGeometry.Space.isThickening_preimage`); the given cartesian square is matched with
the canonical cartesian square of that inverse image
(`CategoryTheory.Subfunctor.isPullback_preimage`) by the comparison isomorphism of two cartesian
squares over one cospan, and the extension is then
`AlgebraicGeometry.Space.Etale.existsUnique_lift_of_isThickening`. -/
@[sga "1 I 5.6" "more general"]
theorem Etale.existsUnique_hom_presheaf_of_isThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1)
    (hw : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (d : H ⟶ G) (hd : d ≫ w = π ≫ v) :
    ∃! α : F ⟶ G, π ≫ α = d ∧ α ≫ w = v := by
  have hinv : inv (Subfunctor.toRange f.hom) ≫ f.hom = (Subfunctor.range f.hom).ι :=
    (cancel_epi (Subfunctor.toRange f.hom)).1 (by
      rw [IsIso.hom_inv_id_assoc]
      exact (Subfunctor.toRange_ι f.hom).symm)
  have hiso : IsPullback (inv (Subfunctor.toRange f.hom)) (Subfunctor.range f.hom).ι f.hom
      (𝟙 Y.1) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hinv⟩
  have hpaste := (Subfunctor.isPullback_preimage v (Subfunctor.range f.hom)).paste_horiz hiso
  rw [Category.comp_id] at hpaste
  obtain ⟨θ, hθiso, hθ⟩ :
      ∃ θ : H ⟶ ((Subfunctor.range f.hom).preimage v).toFunctor,
        IsIso θ ∧ θ ≫ ((Subfunctor.range f.hom).preimage v).ι = π :=
    ⟨(hpb.isoIsPullback _ _ hpaste.flip).hom, inferInstance,
      IsPullback.isoIsPullback_hom_fst _ _ hpb hpaste.flip⟩
  have := hθiso
  have hGp : IsThickening B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)
      ((Subfunctor.range f.hom).preimage v) :=
    isThickening_preimage B S hS (Subfunctor.range f.hom)
      (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y) hT
  have hsq : (inv θ ≫ d) ≫ w = ((Subfunctor.range f.hom).preimage v).ι ≫ v := by
    rw [Category.assoc, hd, ← hθ]
    simp
  obtain ⟨α, ⟨ha1, ha2⟩, hauniq⟩ :=
    Etale.existsUnique_lift_of_isThickening B S hS
      (T' := (⟨F, hF⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk w : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ Y) hw
      ((Subfunctor.range f.hom).preimage v) hGp (inv θ ≫ d) v hsq
  refine ⟨α, ⟨?_, ha2⟩, fun β ⟨hb1, hb2⟩ ↦ hauniq β ⟨?_, hb2⟩⟩
  · rw [← hθ, Category.assoc, ha1, IsIso.hom_inv_id_assoc]
  · rw [← hb1, ← hθ]
    simp

/-- **Two morphisms over `Y` into an étale algebraic space agreeing on a thickening of arbitrary
order are equal.** The uniqueness half of
`AlgebraicGeometry.Space.Etale.existsUnique_hom_presheaf_of_isThickening`, applied to the
restriction of either morphism. -/
theorem Etale.hom_ext_presheaf_of_isThickening
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom))
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : G ⟶ Y.1)
    (hw : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (α β : F ⟶ G) (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  obtain ⟨α₀, -, huniq⟩ := Etale.existsUnique_hom_presheaf_of_isThickening B S hS f hT hF hG
    hpb w hw (π ≫ α) (by rw [Category.assoc, hα])
  rw [huniq α ⟨rfl, hα⟩, huniq β ⟨h.symm, hβ⟩]

end AlgebraicGeometry.Space

end
