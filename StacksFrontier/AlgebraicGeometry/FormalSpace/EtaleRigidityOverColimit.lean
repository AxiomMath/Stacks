module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleLiftDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit

/-!
# Rigidity of a representable étale morphism over a colimit of thickenings

Let `S` be a scheme contained in a big fppf site `B`, let `c` be a colimit cocone over a
diagram `P : I ⥤ BigFppfOver B S hS` of objects of the site whose transition morphisms are
thickenings, and suppose the index `I` has a least element `i₀`. Two morphisms `p : X ⟶ c.pt`
and `q : Z ⟶ c.pt` which are representable and étale and whose base changes to the stage `i₀`
agree are then isomorphic over `c.pt`.

This is the rigidity step of the essential-surjectivity half of **Stacks 0AN8**: the
identification of an affine formal algebraic space étale over `Spf R` with the formal spectrum
of a completed étale algebra is produced at one quotient stage and propagated to the whole
formal spectrum by the uniqueness of étale lifts across the thickenings between stages.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_etale_of_isRepresentableEtale`: a morphism of fppf
  sheaves which is representable by objects of the site and representable étale in the sense of
  Definition 0AIM is étale after every represented base change.
* `AlgebraicGeometry.FormalSpace.existsUnique_relativeEtale_lift_sheaf`: a section of a
  representable étale morphism of fppf sheaves prescribed over a thickening of an object of the
  site extends uniquely.
* `AlgebraicGeometry.FormalSpace.existsUnique_relativeEtale_lift_colimit`: the same for the
  vertex of a colimit cocone over a diagram of thickenings with a least stage: the section is
  prescribed over the least stage.
* `AlgebraicGeometry.FormalSpace.exists_iso_of_isPullback_least_stage`: two representable étale
  morphisms to the vertex of such a cocone with a common base change to the least stage are
  isomorphic over the vertex.

## Implementation notes

The unique-lifting engine is
`AlgebraicGeometry.FormalSpace.existsUnique_siteHom_of_isThickening_of_etale`, the topological
invariance of the étale site for objects of the site, which carries no affineness and no
nilpotency-order hypothesis. The sheaf-level statement is reduced to it by replacing the target
of the lift by the represented base change of the étale morphism along the prescribed morphism
out of the thickened object, which is exactly what relative representability provides.

The colimit statement is the universal property of the colimit applied to the cocone whose legs
are the unique lifts: the lifts are compatible with the transitions because a transition
composed with a lift is again a lift, and uniqueness identifies the two.

For the rigidity statement, each of the two morphisms is replaced by its diagram of base changes
to the stages — the chosen pullbacks of relative representability, made functorial by the
universal property — whose colimit is the source, by universality of the given colimit cocone
applied to that diagram and its first projections. The identification of the two base changes at
the least stage then lifts, in both directions, to morphisms over `c.pt`, and the two composites
are the identity by the uniqueness clause.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Reduction

/-- A represented base change of a morphism of presheaves which is representable by algebraic
spaces and étale in the bootstrap sense of Stacks 03XZ is an étale morphism of the site.

The represented base change is, up to the canonical isomorphism with the chosen fibre product,
a scheme-valued point of that fibre product; the étaleness condition applies to it because the
identity of a representable is relatively étale. -/
theorem etale_toScheme_map_of_hasPropertyULift
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (p : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) p hrep)
    {U V : BigFppfOver B S hS} (a : (uliftYoneda.{u + 1}).obj U ⟶ X) (q : U ⟶ V)
    (b : (uliftYoneda.{u + 1}).obj V ⟶ Y)
    (h : IsPullback a ((uliftYoneda.{u + 1}).map q) p b) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) := by
  let P := Space.etaleOnSite B S hS
  let _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.respectsIso
  let _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let Q := P.relative (uliftYoneda.{u + 1})
  let e := h.flip.isoPullback
  have hid : Q (𝟙 ((uliftYoneda.{u + 1}).obj U)) := by
    apply MorphismProperty.relative.of_exists
    intro W w
    refine ⟨W, w, 𝟙 W, ?_, ?_⟩
    · simpa using (IsPullback.of_id_snd (f := w))
    · change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 W))
      rw [CategoryTheory.Functor.map_id]
      infer_instance
  have he : Q e.hom := by
    simpa using MorphismProperty.RespectsIso.postcomp Q e.hom (𝟙 _) hid
  have hq := het V b U e.hom he
  have hq' : Q ((uliftYoneda.{u + 1}).map q) := by
    change Q (e.hom ≫ pullback.fst b p) at hq
    simpa only [e, IsPullback.isoPullback_hom_fst] using hq
  exact MorphismProperty.of_relative_map (P := P) hq'

/-- Relative representability along the sheafified Yoneda embedding of the big fppf site of `S`
passes to the underlying morphism of presheaves and the universe-lifted Yoneda embedding. This
is `AlgebraicGeometry.FormalSpace.relative_sheafifiedYoneda_iff_uliftYoneda` for the trivial
morphism property, whose relative form is representability alone. -/
theorem relativelyRepresentable_uliftYoneda_of_sheafifiedYoneda
    {X Y : FppfSheaf B S hS} (p : X ⟶ Y)
    (hrep : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable p) :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable p.hom :=
  ((relative_sheafifiedYoneda_iff_uliftYoneda' B S hS ⊤ p).mp
    ⟨hrep, fun _ _ _ _ _ _ ↦ trivial⟩).rep

/-- **A representable étale morphism of fppf sheaves is étale after every represented base
change.** For a morphism which is representable by objects of the site — Stacks 0AKN for a
morphism of affine formal algebraic spaces — the étaleness condition of Definition 0AIM is the
relative morphism property of étaleness along the sheafified Yoneda embedding. -/
theorem relative_etale_of_isRepresentableEtale
    {X Y : FppfSheaf B S hS} (p : X ⟶ Y) (hp : IsRepresentableEtale B S hS p)
    (hrep : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable p) :
    (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) p :=
  (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS (Space.etaleOnSite B S hS) p).mpr
    ⟨relativelyRepresentable_uliftYoneda_of_sheafifiedYoneda B S hS p hrep,
      fun _ _ g fst snd hsq ↦
        etale_toScheme_map_of_hasPropertyULift B S hS p.hom hp.1 hp.2 fst snd g hsq⟩

/-- **A morphism of fppf sheaves which is representable by objects of the site and étale after
every represented base change is representable étale in the sense of Definition 0AIM.** This is
the converse of `AlgebraicGeometry.FormalSpace.relative_etale_of_isRepresentableEtale`, and it
is where the étaleness condition of Definition 0AIM is *produced* rather than consumed.

Both clauses of Definition 0AIM come out of the relative property. Representability by
algebraic spaces does because the relative property supplies, for every scheme-valued point of
the target, an object of the site representing the base change, and the universe-lifted Yoneda
presheaf of an object of the site is an algebraic space over `S`. The étaleness clause does
because the relative property is stable under base change, so the projection of each represented
base change has it, and the relative property is stable under composition, which is what
`AlgebraicGeometry.Space.IsEtaleULift` of that projection asks for. -/
theorem isRepresentableEtale_of_relative_etale' {X Y : FppfSheaf B S hS} (p : X ⟶ Y)
    (hp : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) p) :
    IsRepresentableEtale B S hS p := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  have hrel : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) p.hom :=
    (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS (Space.etaleOnSite B S hS) p).mp hp
  refine ⟨fun U ξ ↦ ?_, fun U ξ ↦ ?_⟩
  · obtain ⟨W, ρ, w, hpb⟩ := hrel.rep ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hpb.flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W)
  · exact fun _ φ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback ξ p.hom).flip hrel)

end Reduction

section Lifting

/-- **A section of a representable étale morphism of fppf sheaves prescribed over a thickening
extends uniquely.** Let `q : Z ⟶ Y` be representable by objects of the site and étale after
every represented base change, let `i : U₀ ⟶ U` be a morphism of the site which is a thickening
on underlying schemes, and let `a : U₀ ⟶ Z` lie over `b : U ⟶ Y`. Then `a` extends uniquely to
a morphism `U ⟶ Z` over `b`.

Replacing `Z` by the represented base change `Z ×_Y U`, which relative representability
provides and over which `q` becomes an étale morphism of the site, turns this into the
topological invariance of the étale site,
`AlgebraicGeometry.FormalSpace.existsUnique_siteHom_of_isThickening_of_etale`. -/
theorem existsUnique_relativeEtale_lift_sheaf {Z Y : FppfSheaf B S hS} (q : Z ⟶ Y)
    (hqEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q)
    {U₀ U : BigFppfOver B S hS} (i : U₀ ⟶ U)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U₀ ⟶ Z)
    (b : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y)
    (h : a ≫ q = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫ b) :
    ∃! l : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Z,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i ≫ l = a ∧ l ≫ q = b := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda J
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let r := hqEt.rep.snd b
  let d := hqEt.rep.fst b
  have hp : IsPullback d (F.map r) q b := hqEt.rep.isPullback b
  have hret : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r) :=
    hqEt.property b d r hp
  let a' : U₀ ⟶ hqEt.rep.pullback b := hqEt.rep.lift a i h
  have ha' : F.map a' ≫ d = a := hqEt.rep.lift_fst _ _ _
  have ha'r : a' ≫ r = i := hqEt.rep.lift_snd _ _ _
  obtain ⟨t, ht, hu⟩ := existsUnique_siteHom_of_isThickening_of_etale B S hS i hi
    (v := 𝟙 U) (w := r) hret a' (by rwa [Category.comp_id])
  refine ⟨F.map t ≫ d, ⟨?_, ?_⟩, ?_⟩
  · rw [← F.map_comp_assoc, ht.1, ha']
  · rw [Category.assoc, hp.w, ← F.map_comp_assoc, ht.2, F.map_id, Category.id_comp]
  · rintro m ⟨hm₁, hm₂⟩
    let m' : U ⟶ hqEt.rep.pullback b :=
      hqEt.rep.lift m (𝟙 U) (by rw [hm₂, F.map_id, Category.id_comp])
    have hm' : F.map m' ≫ d = m := hqEt.rep.lift_fst _ _ _
    have hm'r : m' ≫ r = 𝟙 U := hqEt.rep.lift_snd _ _ _
    have him : i ≫ m' = a' := by
      refine hqEt.rep.hom_ext ?_ ?_
      · rw [F.map_comp, Category.assoc, hm', hm₁, ha']
      · rw [Category.assoc, hm'r, Category.comp_id, ha'r]
    rw [← hm', hu m' ⟨him, hm'r⟩]

/-- **A section of a representable étale morphism of fppf sheaves prescribed over the least
stage of a colimit of thickenings extends uniquely to the colimit.** Let `c` be a colimit
cocone over a diagram `P : I ⥤ BigFppfOver B S hS` whose transition morphisms are thickenings,
with `i₀` least in `I`, and let `q : Z ⟶ Y` be representable and étale after every represented
base change. A morphism `a : P i₀ ⟶ Z` over `p : c.pt ⟶ Y` extends uniquely to `c.pt ⟶ Z`.

The extension along each transition `P i₀ ⟶ P i` is the unique one of
`AlgebraicGeometry.FormalSpace.existsUnique_relativeEtale_lift_sheaf`; uniqueness makes the
extensions a cocone, and the universal property of the colimit assembles them. -/
theorem existsUnique_relativeEtale_lift_colimit
    {I : Type w} [Preorder I] (i₀ : I) (h₀ : ∀ i, i₀ ≤ i)
    (P : I ⥤ BigFppfOver B S hS)
    (htrans : ∀ (i j : I) (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (P.map g)))
    (c : Cocone (P ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hc : IsColimit c) {Z Y : FppfSheaf B S hS} (q : Z ⟶ Y)
    (hqEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q)
    (p : c.pt ⟶ Y)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (P.obj i₀) ⟶ Z)
    (ha : a ≫ q = c.ι.app i₀ ≫ p) :
    ∃! l : c.pt ⟶ Z, c.ι.app i₀ ≫ l = a ∧ l ≫ q = p := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have cw : ∀ {i j : I} (g : i ⟶ j), F.map (P.map g) ≫ c.ι.app j = c.ι.app i :=
    fun g ↦ c.w g
  have hlift : ∀ i : I, ∃! l : F.obj (P.obj i) ⟶ Z,
      F.map (P.map (homOfLE (h₀ i))) ≫ l = a ∧ l ≫ q = c.ι.app i ≫ p := fun i ↦
    existsUnique_relativeEtale_lift_sheaf B S hS q hqEt (P.map (homOfLE (h₀ i)))
      (htrans _ _ _) a (c.ι.app i ≫ p) (by rwa [← Category.assoc, cw])
  choose l hl hu using hlift
  let d : Cocone (P ⋙ F) :=
    { pt := Z
      ι :=
      { app := l
        naturality := fun i j g ↦ by
          change F.map (P.map g) ≫ l j = l i ≫ 𝟙 Z
          rw [Category.comp_id]
          refine hu i _ ⟨?_, ?_⟩
          · rw [← F.map_comp_assoc, ← P.map_comp,
              show homOfLE (h₀ i) ≫ g = homOfLE (h₀ j) from Subsingleton.elim _ _, (hl j).1]
          · rw [Category.assoc, (hl j).2, ← Category.assoc, cw g] } }
  have hli : l i₀ = a := by
    simpa only [show homOfLE (h₀ i₀) = 𝟙 i₀ from Subsingleton.elim _ _, P.map_id, F.map_id,
      Category.id_comp] using (hl i₀).1
  refine ⟨hc.desc d, ⟨(hc.fac d i₀).trans hli, ?_⟩, ?_⟩
  · refine hc.hom_ext fun i ↦ ?_
    rw [← Category.assoc, hc.fac]
    exact (hl i).2
  · rintro m ⟨hm₁, hm₂⟩
    refine hc.hom_ext fun i ↦ ?_
    rw [hc.fac]
    refine hu i _ ⟨?_, ?_⟩
    · rw [← Category.assoc, cw, hm₁]
    · rw [Category.assoc, hm₂]

end Lifting

section Rigidity

/-- A square whose left side is the base change of `p` along `ci` and whose right side is the base
change of `p` along `cj`, commuting over the cartesian squares, is cartesian. -/
private theorem isPullback_of_isPullback_of_comp_eq {C : Type*} [Category C]
    {X Z Aᵢ Aⱼ Tᵢ Tⱼ : C} {p : X ⟶ Z} {xᵢ : Aᵢ ⟶ X} {xⱼ : Aⱼ ⟶ X} {sᵢ : Aᵢ ⟶ Tᵢ}
    {sⱼ : Aⱼ ⟶ Tⱼ} {cᵢ : Tᵢ ⟶ Z} {cⱼ : Tⱼ ⟶ Z} {m : Aᵢ ⟶ Aⱼ} {g : Tᵢ ⟶ Tⱼ}
    (hᵢ : IsPullback xᵢ sᵢ p cᵢ) (hⱼ : IsPullback xⱼ sⱼ p cⱼ) (hm : m ≫ xⱼ = xᵢ)
    (hms : m ≫ sⱼ = sᵢ ≫ g) (hg : g ≫ cⱼ = cᵢ) : IsPullback m sᵢ sⱼ g :=
  IsPullback.of_right (by rwa [hm, hg]) hms hⱼ

/-- A morphism of the site whose image under the sheafified Yoneda embedding is a base change of
the image of a thickening is a thickening. -/
private theorem isThickening_of_isPullback_sheafifiedYoneda {U U' V V' : BigFppfOver B S hS}
    {f : U ⟶ U'} {u : U ⟶ V} {u' : U' ⟶ V'} {g : V ⟶ V'}
    (h : IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u')
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g))
    (hg : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map g)) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map f) := by
  have := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  let : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_relative_map
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (P := MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip
      (MorphismProperty.relative_map hg))

/-- The diagram of represented base changes of a relatively representable morphism to the
vertex of a cocone, together with its colimit and its cartesian squares.

The stages are the chosen pullbacks of relative representability and the transitions are the
unique morphisms over them; that the source is their colimit is the universality of the given
colimit cocone, applied to this diagram and the first projections. -/
theorem exists_stage_presentation_of_relativelyRepresentable
    {I : Type w} [Preorder I] (P₀ : I ⥤ BigFppfOver B S hS)
    (htrans : ∀ (i j : I) (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (P₀.map g)))
    (c : Cocone (P₀ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hc : IsUniversalColimit c) {X : FppfSheaf B S hS} (p : X ⟶ c.pt)
    (hp : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable p) :
    ∃ (P : I ⥤ BigFppfOver B S hS)
      (a : P ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⟶
        (Functor.const I).obj X) (r : P ⟶ P₀),
      (∀ (i j : I) (g : i ⟶ j), Stacks.Thickenings.IsThickening
        ((BigFppfOver.toScheme B S hS).map (P.map g))) ∧
      Nonempty (IsColimit (Cocone.mk X a)) ∧
      ∀ i, IsPullback (a.app i)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (r.app i)) p (c.ι.app i) := by
  have := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  have cw : ∀ {i j : I} (g : i ⟶ j),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (P₀.map g) ≫ c.ι.app j =
        c.ι.app i := fun g ↦ c.w g
  have hs : ∀ i : I, IsPullback (hp.fst (c.ι.app i))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (hp.snd (c.ι.app i))) p
      (c.ι.app i) := fun i ↦ hp.isPullback (c.ι.app i)
  let m : ∀ {i j : I}, (i ⟶ j) → (hp.pullback (c.ι.app i) ⟶ hp.pullback (c.ι.app j)) :=
    fun {i j} g ↦ hp.lift (hp.fst (c.ι.app i)) (hp.snd (c.ι.app i) ≫ P₀.map g) (by
      rw [Functor.map_comp, Category.assoc, cw g]
      exact (hs i).w)
  have hm₁ : ∀ {i j : I} (g : i ⟶ j),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (m g) ≫
        hp.fst (c.ι.app j) = hp.fst (c.ι.app i) := fun g ↦ hp.lift_fst _ _ _
  have hm₂ : ∀ {i j : I} (g : i ⟶ j),
      m g ≫ hp.snd (c.ι.app j) = hp.snd (c.ι.app i) ≫ P₀.map g := fun g ↦ hp.lift_snd _ _ _
  let P : I ⥤ BigFppfOver B S hS :=
    { obj := fun i ↦ hp.pullback (c.ι.app i)
      map := m
      map_id := fun i ↦ hp.hom_ext (by rw [hm₁, CategoryTheory.Functor.map_id, Category.id_comp])
        (by rw [hm₂, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
      map_comp := fun g g' ↦ hp.hom_ext
        (by rw [hm₁, CategoryTheory.Functor.map_comp, Category.assoc, hm₁, hm₁])
        (by rw [hm₂, Category.assoc, hm₂, ← Category.assoc, hm₂, Category.assoc,
          CategoryTheory.Functor.map_comp]) }
  let a : P ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⟶
      (Functor.const I).obj X :=
    { app := fun i ↦ hp.fst (c.ι.app i)
      naturality := fun i j g ↦ (hm₁ g).trans (Category.comp_id _).symm }
  let r : P ⟶ P₀ := { app := fun i ↦ hp.snd (c.ι.app i), naturality := fun i j g ↦ hm₂ g }
  have hbigpb : ∀ {i j : I} (g : i ⟶ j),
      IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (m g))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (hp.snd (c.ι.app i)))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (hp.snd (c.ι.app j)))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (P₀.map g)) := fun g ↦
    isPullback_of_isPullback_of_comp_eq (hs _) (hs _) (hm₁ g)
      (by rw [← CategoryTheory.Functor.map_comp, hm₂ g, CategoryTheory.Functor.map_comp]) (cw g)
  exact ⟨P, a, r, fun i j g ↦ isThickening_of_isPullback_sheafifiedYoneda B S hS (hbigpb g)
    (htrans i j g), ⟨(hc (Cocone.mk X a)
      (Functor.whiskerRight r (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) p
      (NatTrans.ext (funext fun j ↦ (hs j).w.symm)) (fun {i j} g ↦ hbigpb g) hs).some⟩, hs⟩

/-- **Two representable étale morphisms to the vertex of a colimit of thickenings with a common
base change to the least stage are isomorphic over the vertex.** This is the rigidity step of
the essential-surjectivity half of Stacks 0AN8.

Each morphism is replaced by its diagram of represented base changes to the stages, whose
colimit is its source; the given isomorphism at the least stage then extends, in both
directions, to a morphism over `c.pt` by
`AlgebraicGeometry.FormalSpace.existsUnique_relativeEtale_lift_colimit`, and the uniqueness
clause identifies both composites with the identity. -/
theorem exists_iso_of_isPullback_least_stage
    {I : Type w} [Preorder I] (i₀ : I) (h₀ : ∀ i, i₀ ≤ i)
    (P₀ : I ⥤ BigFppfOver B S hS)
    (htrans : ∀ (i j : I) (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (P₀.map g)))
    (c : Cocone (P₀ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hc : IsUniversalColimit c) {X Z : FppfSheaf B S hS} (p : X ⟶ c.pt) (q : Z ⟶ c.pt)
    (hpEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) p)
    (hqEt : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q)
    {N : FppfSheaf B S hS}
    {n₀ : N ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (P₀.obj i₀)}
    {nX : N ⟶ X} {nZ : N ⟶ Z}
    (hX : IsPullback nX n₀ p (c.ι.app i₀)) (hZ : IsPullback nZ n₀ q (c.ι.app i₀)) :
    ∃ t : X ≅ Z, p = t.hom ≫ q := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨P, a, r, hPt, ⟨hcP⟩, hpbP⟩ :=
    exists_stage_presentation_of_relativelyRepresentable B S hS P₀ htrans c hc p hpEt.rep
  obtain ⟨Q, b, s, hQt, ⟨hcQ⟩, hpbQ⟩ :=
    exists_stage_presentation_of_relativelyRepresentable B S hS P₀ htrans c hc q hqEt.rep
  let ε₁ : N ≅ F.obj (P.obj i₀) := hX.isoIsPullback _ _ (hpbP i₀)
  let ε₂ : N ≅ F.obj (Q.obj i₀) := hZ.isoIsPullback _ _ (hpbQ i₀)
  have hε₁ : ε₁.hom ≫ F.map (r.app i₀) = n₀ := hX.isoIsPullback_hom_snd _ _ (hpbP i₀)
  have hε₂ : ε₂.hom ≫ F.map (s.app i₀) = n₀ := hZ.isoIsPullback_hom_snd _ _ (hpbQ i₀)
  let e₀ : F.obj (P.obj i₀) ≅ F.obj (Q.obj i₀) := ε₁.symm ≪≫ ε₂
  have he₀ : e₀.hom ≫ F.map (s.app i₀) = F.map (r.app i₀) := by
    change (ε₁.inv ≫ ε₂.hom) ≫ F.map (s.app i₀) = _
    rw [Category.assoc, hε₂, ← hε₁, ← Category.assoc, ε₁.inv_hom_id, Category.id_comp]
  have hab : (e₀.hom ≫ b.app i₀) ≫ q = a.app i₀ ≫ p := by
    rw [Category.assoc, (hpbQ i₀).w, ← Category.assoc, he₀, (hpbP i₀).w]
  have hba : (e₀.inv ≫ a.app i₀) ≫ p = b.app i₀ ≫ q := by
    rw [Category.assoc, ← hab, Category.assoc, e₀.inv_hom_id_assoc]
  obtain ⟨m, hm, -⟩ := existsUnique_relativeEtale_lift_colimit B S hS i₀ h₀ P hPt
    (Cocone.mk X a) hcP q hqEt p (e₀.hom ≫ b.app i₀) hab
  obtain ⟨n, hn, -⟩ := existsUnique_relativeEtale_lift_colimit B S hS i₀ h₀ Q hQt
    (Cocone.mk Z b) hcQ p hpEt q (e₀.inv ≫ a.app i₀) hba
  have hpuniq := existsUnique_relativeEtale_lift_colimit B S hS i₀ h₀ P hPt
    (Cocone.mk X a) hcP p hpEt p (a.app i₀) rfl
  have hquniq := existsUnique_relativeEtale_lift_colimit B S hS i₀ h₀ Q hQt
    (Cocone.mk Z b) hcQ q hqEt q (b.app i₀) rfl
  have hmn : m ≫ n = 𝟙 X := hpuniq.unique
    ⟨by
      change a.app i₀ ≫ m ≫ n = a.app i₀
      rw [← Category.assoc, hm.1, Category.assoc, hn.1, e₀.hom_inv_id_assoc],
      by rw [Category.assoc, hn.2, hm.2]⟩
    ⟨Category.comp_id _, Category.id_comp _⟩
  have hnm : n ≫ m = 𝟙 Z := hquniq.unique
    ⟨by
      change b.app i₀ ≫ n ≫ m = b.app i₀
      rw [← Category.assoc, hn.1, Category.assoc, hm.1, e₀.inv_hom_id_assoc],
      by rw [Category.assoc, hm.2, hn.2]⟩
    ⟨Category.comp_id _, Category.id_comp _⟩
  exact ⟨⟨m, n, hmn, hnm⟩, hm.2.symm⟩

end Rigidity

end AlgebraicGeometry.FormalSpace

end
