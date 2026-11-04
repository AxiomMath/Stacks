module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Functoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# The stagewise 2-fibre product of a cospan of diagrams of categories

Let `α : 𝒳 ⟶ 𝒴` and `γ : 𝒵 ⟶ 𝒴` be morphisms of diagrams of categories indexed by a category
`J`. Taking the 2-fibre product of `α.app j` and `γ.app j` for each `j` gives a new diagram
`j ↦ 𝒳ⱼ ×_{𝒴ⱼ} 𝒵ⱼ`, and this file constructs it: the transitions are the functoriality of the
2-fibre product of Stacks 02XA applied to the naturality squares of `α` and `γ`, and the two
functoriality laws are proved.

This diagram is the source of the comparison
`colim (𝒳ⱼ ×_{𝒴ⱼ} 𝒵ⱼ) ⥤ (colim 𝒳ⱼ) ×_{colim 𝒴ⱼ} (colim 𝒵ⱼ)`
whose full faithfulness — "filtered colimits of categories commute with 2-fibre products", the
statement the proof of Stacks 0CMT uses with the details omitted — is *not* proved here.

## Main definitions

* `CategoryTheory.Cat.twoFibreProductMap`: the transition functor of the stagewise 2-fibre
  product.
* `CategoryTheory.Cat.twoFibreProductDiagram`: the stagewise 2-fibre product as a diagram.

## Main results

* `CategoryTheory.Cat.categoricalPullback_obj_ext`: objects of a 2-fibre product of categories
  agree as soon as their components and structural isomorphisms do.
* `CategoryTheory.Cat.categoricalPullback_map_comp_map`: two stacked 2-commutative diagrams
  between cospans induce on 2-fibre products the functor of the stacked diagram.
* `CategoryTheory.Cat.categoricalPullback_map_comp_asSmallMap`: the special case of that in which
  the second diagram is a universe lift, which is how a comparison out of a split fibre becomes
  natural for the stagewise 2-fibre product of the *lifted* diagrams.
* `CategoryTheory.Cat.twoFibreProductMap_id` and
  `CategoryTheory.Cat.twoFibreProductMap_comp`: the functoriality laws.

## Implementation notes

The objects of a 2-fibre product of categories carry an isomorphism as part of their data, so
an equality of such objects is not componentwise: `categoricalPullback_obj_ext` reduces it to the
two component equalities together with the compatibility of the structural isomorphisms under the
resulting transports. Those transports accumulate as chains of `eqToHom`, whose endpoints are
only definitionally — not syntactically — equal, so `eqToHom_trans` does not fire on them;
`eqToHom_chain₃` collapses such a chain in one step, with its endpoint equalities taken as
arguments so that unification rather than syntactic matching lines them up, and
`eq_eqToHom_conj` strips a conjugating pair of them from a goal.

`CategoryTheory.AsSmall` is a definition rather than an abbreviation for `ULift`, so `simp` does
not see the two universe lifts cancel through the `ULift` projection; `asSmall_down_obj_up_obj`
and `asSmall_up_map_down` supply that.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 02X9](https://stacks.math.columbia.edu/tag/02X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t v w

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down

/-- Two objects of a 2-fibre product of categories agree as soon as their two components do and
their structural isomorphisms are identified by the resulting transports. -/
lemma categoricalPullback_obj_ext {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q : CategoricalPullback F G}
    (h₁ : P.fst = Q.fst) (h₂ : P.snd = Q.snd)
    (h₃ : P.iso.hom = eqToHom (congrArg F.obj h₁) ≫ Q.iso.hom ≫
      eqToHom (congrArg G.obj h₂).symm) : P = Q := by
  obtain ⟨p₁, p₂, pe⟩ := P
  obtain ⟨q₁, q₂, qe⟩ := Q
  cases h₁
  cases h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h₃
  simpa using Iso.ext h₃

/-- The naturality square of a morphism of diagrams of categories, read on underlying
functors. -/
lemma naturality_toFunctor {J : Type v} [Category.{w} J] {U V : J ⥤ Cat.{t, t}} (β : U ⟶ V)
    {j k : J} (s : j ⟶ k) :
    (U.map s).toFunctor ⋙ (β.app k).toFunctor =
      (β.app j).toFunctor ⋙ (V.map s).toFunctor := by
  rw [← Cat.Hom.comp_toFunctor, ← Cat.Hom.comp_toFunctor, β.naturality s]

section Diagram

variable {J : Type v} [Category.{w} J]
  {X Y Z : J ⥤ Cat.{t, t}} (α : X ⟶ Y) (γ : Z ⟶ Y)

/-- The transition functor of the stagewise 2-fibre product diagram: it is the functoriality of
the 2-fibre product (Stacks 02XA) applied to the naturality squares of `α` and `γ`. -/
def twoFibreProductMap {j k : J} (s : j ⟶ k) :
    CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor ⥤
      CategoricalPullback (α.app k).toFunctor (γ.app k).toFunctor :=
  CategoricalPullback.map (α.app j).toFunctor (γ.app j).toFunctor
    (X.map s).toFunctor (Z.map s).toFunctor (Y.map s).toFunctor
    (α.app k).toFunctor (γ.app k).toFunctor
    (eqToIso (naturality_toFunctor γ s))
    (eqToIso (naturality_toFunctor α s).symm)

/-- The first component of the image of an object under `twoFibreProductMap α γ s` is the image
of its first component under `X.map s`. -/
@[simp]
lemma twoFibreProductMap_obj_fst {j k : J} (s : j ⟶ k)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductMap α γ s).obj P).fst = (X.map s).toFunctor.obj P.fst := rfl

/-- The second component of the image of an object under `twoFibreProductMap α γ s` is the image
of its second component under `Z.map s`. -/
@[simp]
lemma twoFibreProductMap_obj_snd {j k : J} (s : j ⟶ k)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductMap α γ s).obj P).snd = (Z.map s).toFunctor.obj P.snd := rfl

/-- The first component of the image of a morphism under `twoFibreProductMap α γ s` is the image
of its first component under `X.map s`. -/
@[simp]
lemma twoFibreProductMap_map_fst {j k : J} (s : j ⟶ k)
    {P Q : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor} (f : P ⟶ Q) :
    ((twoFibreProductMap α γ s).map f).fst = (X.map s).toFunctor.map f.fst := rfl

/-- The second component of the image of a morphism under `twoFibreProductMap α γ s` is the
image of its second component under `Z.map s`. -/
@[simp]
lemma twoFibreProductMap_map_snd {j k : J} (s : j ⟶ k)
    {P Q : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor} (f : P ⟶ Q) :
    ((twoFibreProductMap α γ s).map f).snd = (Z.map s).toFunctor.map f.snd := rfl

/-- The `iso` field of the image of an object under `twoFibreProductMap α γ s` is the image of
its `iso` field under `Y.map s`, conjugated by the naturality 2-cells of `α` and `γ`. -/
lemma twoFibreProductMap_obj_iso_hom {j k : J} (s : j ⟶ k)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductMap α γ s).obj P).iso.hom =
      (eqToIso (naturality_toFunctor α s).symm).inv.app P.fst ≫
        (Y.map s).toFunctor.map P.iso.hom ≫
          (eqToIso (naturality_toFunctor γ s)).inv.app P.snd := rfl

/-- The `iso` field of the transition functor of the stagewise 2-fibre product, with its two
2-cells written as transports. -/
lemma twoFibreProductMap_obj_iso_hom' {j k : J} (s : j ⟶ k)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductMap α γ s).obj P).iso.hom =
      eqToHom (Functor.congr_obj (naturality_toFunctor α s) P.fst) ≫
        (Y.map s).toFunctor.map P.iso.hom ≫
          eqToHom (Functor.congr_obj (naturality_toFunctor γ s) P.snd).symm := by
  rw [twoFibreProductMap_obj_iso_hom]
  simp only [CategoryTheory.eqToIso.inv]
  rw [CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_app]

/-- A chain of three transports on either side of a morphism is the single transport. -/
lemma eqToHom_chain₃ {C : Type*} [Category C] {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : C}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (p₃ : a₃ = a₄) (f : a₄ ⟶ b₁)
    (q₁ : b₁ = b₂) (q₂ : b₂ = b₃) (q₃ : b₃ = b₄) (p : a₁ = a₄) (q : b₁ = b₄) :
    eqToHom p₁ ≫ eqToHom p₂ ≫ eqToHom p₃ ≫ f ≫ eqToHom q₁ ≫ eqToHom q₂ ≫ eqToHom q₃ =
      eqToHom p ≫ f ≫ eqToHom q := by
  cases p₁; cases p₂; cases p₃; cases q₁; cases q₂; cases q₃; simp

/-- The first component of a transport between objects of a 2-fibre product. -/
lemma categoricalPullback_eqToHom_fst {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q : CategoricalPullback F G} (h : P = Q) :
    (eqToHom h).fst = eqToHom (congrArg CategoricalPullback.fst h) := by
  cases h; rfl

/-- The second component of a transport between objects of a 2-fibre product. -/
lemma categoricalPullback_eqToHom_snd {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q : CategoricalPullback F G} (h : P = Q) :
    (eqToHom h).snd = eqToHom (congrArg CategoricalPullback.snd h) := by
  cases h; rfl

/-- **Vertical composition of `CategoryTheory.Limits.CategoricalPullback.map`.** Two stacked
2-commutative diagrams between cospans induce on 2-fibre products the functor of the stacked
diagram, whose 2-cells are the pasted ones. This is the identity that lets a comparison out of a
2-fibre product be transported along a further change of cospan -- for instance along a universe
lift -- without recomputing it. -/
lemma categoricalPullback_map_comp_map {𝒜₁ ℬ₁ 𝒞₁ 𝒜₂ ℬ₂ 𝒞₂ 𝒜₃ ℬ₃ 𝒞₃ : Type*}
    [Category 𝒜₁] [Category ℬ₁] [Category 𝒞₁] [Category 𝒜₂] [Category ℬ₂] [Category 𝒞₂]
    [Category 𝒜₃] [Category ℬ₃] [Category 𝒞₃]
    (H : 𝒜₁ ⥤ 𝒞₁) (Iv : ℬ₁ ⥤ 𝒞₁)
    (L : 𝒜₁ ⥤ 𝒜₂) (K : ℬ₁ ⥤ ℬ₂) (M : 𝒞₁ ⥤ 𝒞₂) (F : 𝒜₂ ⥤ 𝒞₂) (G : ℬ₂ ⥤ 𝒞₂)
    (a : K ⋙ G ≅ Iv ⋙ M) (b : H ⋙ M ≅ L ⋙ F)
    (L' : 𝒜₂ ⥤ 𝒜₃) (K' : ℬ₂ ⥤ ℬ₃) (M' : 𝒞₂ ⥤ 𝒞₃) (F' : 𝒜₃ ⥤ 𝒞₃) (G' : ℬ₃ ⥤ 𝒞₃)
    (a' : K' ⋙ G' ≅ G ⋙ M') (b' : F ⋙ M' ≅ L' ⋙ F') :
    CategoricalPullback.map H Iv L K M F G a b ⋙
        CategoricalPullback.map F G L' K' M' F' G' a' b' =
      CategoricalPullback.map H Iv (L ⋙ L') (K ⋙ K') (M ⋙ M') F' G'
        (Functor.isoWhiskerLeft K a' ≪≫ Functor.isoWhiskerRight a M')
        (Functor.isoWhiskerRight b M' ≪≫ Functor.isoWhiskerLeft L b') := by
  refine CategoryTheory.Functor.ext
    (fun P => categoricalPullback_obj_ext rfl rfl ?_) (fun P Q f => ?_)
  · simp
    exact (Category.id_comp _).symm
  · refine CategoricalPullback.Hom.ext ?_ ?_
    · simp [categoricalPullback_eqToHom_fst]
      exact (Category.id_comp _).symm
    · simp [categoricalPullback_eqToHom_snd]
      exact (Category.id_comp _).symm

/-- The two universe lifts cancel on objects. `CategoryTheory.AsSmall` is a definition rather
than an abbreviation for `ULift`, so `simp` cannot see this through the projection. -/
@[simp]
lemma asSmall_down_obj_up_obj {C : Type*} [Category C] (X : C) :
    AsSmall.down.obj (AsSmall.up.{t}.obj X) = X := rfl

/-- The two universe lifts cancel on morphisms. -/
@[simp]
lemma asSmall_up_map_down {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    (AsSmall.up.{t}.map f).down = f := rfl

/-- A morphism equals its conjugate by two transports as soon as the two are heterogeneously
equal. The transports are taken as arguments, so this applies wherever the endpoints agree only
definitionally -- which is the case for every transport produced by
`CategoryTheory.Functor.ext` out of a comparison that is natural on the nose. -/
lemma eq_eqToHom_conj {C : Type*} [Category C] {a a' b b' : C} (h₁ : a = a') (h₂ : b' = b)
    (f : a ⟶ b) (g : a' ⟶ b') (hfg : HEq f g) : f = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by
  cases h₁
  cases h₂
  simpa using hfg

/-- **The universe lift of a change of cospan, read on 2-fibre products.** Changing the cospan by
`(RX, RZ, RY)` and then lifting universes is the same as lifting universes and then changing the
cospan by the lifts of `(RX, RZ, RY)`. Every 2-cell here is a transport, so the two composites
agree on the nose; this is the identity that makes a comparison out of a split fibre natural for
the *stagewise* 2-fibre product of the lifted diagrams rather than only for the unlifted one. -/
lemma categoricalPullback_map_comp_asSmallMap {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : Type*}
    [Category X₁] [Category Z₁] [Category Y₁] [Category X₂] [Category Z₂] [Category Y₂]
    (H₁ : X₁ ⥤ Y₁) (I₁ : Z₁ ⥤ Y₁) (H₂ : X₂ ⥤ Y₂) (I₂ : Z₂ ⥤ Y₂)
    (RX : X₁ ⥤ X₂) (RZ : Z₁ ⥤ Z₂) (RY : Y₁ ⥤ Y₂)
    (hq : RZ ⋙ I₂ = I₁ ⋙ RY) (hp : RX ⋙ H₂ = H₁ ⋙ RY) :
    CategoricalPullback.map H₁ I₁ RX RZ RY H₂ I₂ (eqToIso hq) (eqToIso hp.symm) ⋙
        CategoricalPullback.map H₂ I₂ AsSmall.up.{t} AsSmall.up.{t} AsSmall.up.{t}
          (AsSmall.down ⋙ H₂ ⋙ AsSmall.up) (AsSmall.down ⋙ I₂ ⋙ AsSmall.up)
          (eqToIso rfl) (eqToIso rfl) =
      CategoricalPullback.map H₁ I₁ AsSmall.up.{t} AsSmall.up.{t} AsSmall.up.{t}
          (AsSmall.down ⋙ H₁ ⋙ AsSmall.up) (AsSmall.down ⋙ I₁ ⋙ AsSmall.up)
          (eqToIso rfl) (eqToIso rfl) ⋙
        CategoricalPullback.map (AsSmall.down ⋙ H₁ ⋙ AsSmall.up)
          (AsSmall.down ⋙ I₁ ⋙ AsSmall.up)
          (AsSmall.down ⋙ RX ⋙ AsSmall.up) (AsSmall.down ⋙ RZ ⋙ AsSmall.up)
          (AsSmall.down ⋙ RY ⋙ AsSmall.up)
          (AsSmall.down ⋙ H₂ ⋙ AsSmall.up) (AsSmall.down ⋙ I₂ ⋙ AsSmall.up)
          (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up.{t}) hq))
          (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up.{t}) hp.symm)) := by
  refine CategoryTheory.Functor.ext
    (fun P => categoricalPullback_obj_ext rfl rfl ?_) (fun P Q f => ?_)
  · refine eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
    simp [eqToHom_map]
  · refine CategoricalPullback.Hom.ext ?_ ?_ <;>
    · simp only [Functor.comp_map, CategoricalPullback.comp_fst, CategoricalPullback.comp_snd,
        CategoricalPullback.map_map_fst, CategoricalPullback.map_map_snd,
        categoricalPullback_eqToHom_fst, categoricalPullback_eqToHom_snd]
      exact eq_eqToHom_conj _ _ _ _ HEq.rfl

/-- The universe lift `CategoryTheory.AsSmall.up` is an equivalence. Mathlib records the
equivalence `CategoryTheory.AsSmall.equiv` but not this instance for its functor, and instance
synthesis does not read the equivalence backwards. -/
instance isEquivalence_asSmall_up {C : Type*} [Category C] :
    (AsSmall.up : C ⥤ AsSmall.{t} C).IsEquivalence :=
  AsSmall.equiv.isEquivalence_functor

/-- The inverse universe lift `CategoryTheory.AsSmall.down` is an equivalence. -/
instance isEquivalence_asSmall_down {C : Type*} [Category C] :
    (AsSmall.down : AsSmall.{t} C ⥤ C).IsEquivalence :=
  AsSmall.equiv.isEquivalence_inverse

/-- **The universe lift of a 2-fibre product of categories is an equivalence.** Both legs of the
cospan are lifted by `CategoryTheory.AsSmall.up`, which is an equivalence, so Stacks 02XB (3)
applies. -/
instance isEquivalence_categoricalPullback_asSmallMap {X₁ Z₁ Y₁ : Type*}
    [Category X₁] [Category Z₁] [Category Y₁] (H : X₁ ⥤ Y₁) (I : Z₁ ⥤ Y₁) :
    (CategoricalPullback.map H I AsSmall.up.{t} AsSmall.up.{t} AsSmall.up.{t}
      (AsSmall.down ⋙ H ⋙ AsSmall.up) (AsSmall.down ⋙ I ⋙ AsSmall.up)
      (eqToIso rfl) (eqToIso rfl)).IsEquivalence :=
  induced_isEquivalence_of_isEquivalence (H := H) (I := I)
    (F := AsSmall.down ⋙ H ⋙ AsSmall.up) (G := AsSmall.down ⋙ I ⋙ AsSmall.up)
    AsSmall.up AsSmall.up AsSmall.up (eqToIso rfl) (eqToIso rfl)

/-- The transition functor of the stagewise 2-fibre product at an identity is the identity. -/
lemma twoFibreProductMap_id (j : J) : twoFibreProductMap α γ (𝟙 j) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun P => ?_) (fun P Q f => ?_)
  · refine categoricalPullback_obj_ext
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor (X.map_id j)) P.fst)
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor (Z.map_id j)) P.snd) ?_
    rw [twoFibreProductMap_obj_iso_hom',
      Functor.congr_hom (congrArg Cat.Hom.toFunctor (Y.map_id j)) P.iso.hom]
    simp
  · apply CategoricalPullback.hom_ext
    · rw [twoFibreProductMap_map_fst,
        Functor.congr_hom (congrArg Cat.Hom.toFunctor (X.map_id j)) f.fst]
      simp [categoricalPullback_eqToHom_fst]
    · rw [twoFibreProductMap_map_snd,
        Functor.congr_hom (congrArg Cat.Hom.toFunctor (Z.map_id j)) f.snd]
      simp [categoricalPullback_eqToHom_snd]

/-- The transition functors of the stagewise 2-fibre product compose. -/
lemma twoFibreProductMap_comp {j k l : J} (s : j ⟶ k) (s' : k ⟶ l) :
    twoFibreProductMap α γ (s ≫ s') =
      twoFibreProductMap α γ s ⋙ twoFibreProductMap α γ s' := by
  refine CategoryTheory.Functor.ext (fun P => ?_) (fun P Q f => ?_)
  · refine categoricalPullback_obj_ext
      (show ((twoFibreProductMap α γ (s ≫ s')).obj P).fst =
          ((twoFibreProductMap α γ s ⋙ twoFibreProductMap α γ s').obj P).fst from
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (X.map_comp s s')) P.fst)
      (show ((twoFibreProductMap α γ (s ≫ s')).obj P).snd =
          ((twoFibreProductMap α γ s ⋙ twoFibreProductMap α γ s').obj P).snd from
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (Z.map_comp s s')) P.snd) ?_
    rw [twoFibreProductMap_obj_iso_hom',
      Functor.congr_hom (congrArg Cat.Hom.toFunctor (Y.map_comp s s')) P.iso.hom]
    show _ = eqToHom _ ≫ ((twoFibreProductMap α γ s').obj
      ((twoFibreProductMap α γ s).obj P)).iso.hom ≫ eqToHom _
    rw [twoFibreProductMap_obj_iso_hom', twoFibreProductMap_obj_iso_hom']
    simp only [Functor.comp_obj, Hom.comp_toFunctor, Functor.comp_map, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc, twoFibreProductMap_obj_fst, twoFibreProductMap_obj_snd,
      Functor.map_comp, CategoryTheory.eqToHom_map]
    exact (eqToHom_chain₃ ..).symm
  · apply CategoricalPullback.hom_ext
    · rw [twoFibreProductMap_map_fst,
        Functor.congr_hom (congrArg Cat.Hom.toFunctor (X.map_comp s s')) f.fst]
      simp [CategoricalPullback.comp_fst, categoricalPullback_eqToHom_fst]
    · rw [twoFibreProductMap_map_snd,
        Functor.congr_hom (congrArg Cat.Hom.toFunctor (Z.map_comp s s')) f.snd]
      simp [CategoricalPullback.comp_snd, categoricalPullback_eqToHom_snd]

/-- **The stagewise 2-fibre product of a cospan of diagrams of categories.** Its value at `j` is
the explicit 2-fibre product `𝒳ⱼ ×_{𝒴ⱼ} 𝒵ⱼ` and its transitions are the functoriality of the
2-fibre product applied to the naturality squares of `α` and `γ`. -/
def twoFibreProductDiagram : J ⥤ Cat.{t, t} where
  obj j := Cat.of (CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor)
  map s := (twoFibreProductMap α γ s).toCatHom
  map_id j := Cat.Hom.ext (twoFibreProductMap_id α γ j)
  map_comp s s' := Cat.Hom.ext (twoFibreProductMap_comp α γ s s')

/-- The value of `twoFibreProductDiagram α γ` at `j` is the 2-fibre product of `α.app j` and
`γ.app j`. -/
@[simp]
lemma twoFibreProductDiagram_obj (j : J) :
    (twoFibreProductDiagram α γ).obj j =
      Cat.of (CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) := rfl

/-- The transition functor of `twoFibreProductDiagram α γ` along `s` is
`twoFibreProductMap α γ s`. -/
@[simp]
lemma twoFibreProductDiagram_map {j k : J} (s : j ⟶ k) :
    (twoFibreProductDiagram α γ).map s = (twoFibreProductMap α γ s).toCatHom := rfl

end Diagram

end CategoryTheory.Cat

end
