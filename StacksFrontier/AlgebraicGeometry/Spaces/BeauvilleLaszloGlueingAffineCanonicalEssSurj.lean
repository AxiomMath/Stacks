module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalRestriction

/-!
# Essential surjectivity of the Beauville--Laszlo glueing functor (Stacks 0F9Q)

This file inverts the glueing functor of Stacks 0F9N on affine glueable algebraic spaces. The
dictionary it runs on is: how to read a pushout square of rings off a base-change identification
of objects of the site, and how the canonical base-change isomorphisms of
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso` act on the identity section. Given
a cartesian glueing triple with three affine components, those turn the triple into a pair of
pushout squares of rings, `BeauvilleLaszlo.glueingSubalgebra_spec` gives the glued ring, and its
spectrum is the algebraic space the triple comes from.

## Main results

* `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_essSurj`: the glueing functor is
  essentially surjective on affine glueable algebraic spaces. With faithfulness and fullness, this
  is Stacks 0F9Q.
* `BeauvilleLaszlo.Space.exists_isPushout_of_pullbackIso`: an identification of the base change
  of `Spec A` with `Spec A₂` over `Spec R₂` is the canonical identification attached to a
  pushout square of rings, and the ring map completing the square is read off from it.
* `BeauvilleLaszlo.Space.relocalizeRestrictSpecOverIso_section_left`: transporting the identity
  section of `Spec A₃` back through two successive base-change isomorphisms gives the morphism
  of schemes `Spec (ψ ≫ χ)`, where `ψ` and `χ` are the two ring maps of the two pushout
  squares.
* `BeauvilleLaszlo.Space.exists_isPushout_section_of_iso`: the same statement with the
  identification as an *argument*, so that a consumer keeps its own local isomorphism and never
  mentions `AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso` at all. This is the
  form the glueing triple's two structure isomorphisms are fed to.
* `BeauvilleLaszlo.Space.section_comp`: two base-change identifications compose on the identity
  section, stated for arbitrary isomorphisms.
* `BeauvilleLaszlo.Space.square_of_section_left`: two chains of base-change isomorphisms
  identifying a double restriction with a representable presheaf agree up to a comparison
  isomorphism of the two double restrictions, as soon as the two chains agree on the identity
  section.
* `BeauvilleLaszlo.Space.squareBaseChangeIso_hom_app` and
  `BeauvilleLaszlo.Space.squareBaseChangeIso_section_left`: the comparison isomorphism of the
  two iterated base changes of a commutative square is the canonical cast, and so does not
  change the underlying morphism of a section. Together these are everything the outer square
  of a cartesian glueing triple needs to know about it.

## Implementation notes

Everything here is deliberately stated for the *representable* presheaves `yoneda.obj T` of the
big fppf category, since the content of Stacks 0F9Q on affine objects is a statement about ring
maps: a morphism of presheaves out of a representable is a section, a section is a morphism of
the site, and a morphism of the site between spectra is a ring map
(`AlgebraicGeometry.BigFppfOver.specOverHomEquiv`).

Morphisms of presheaves are compared by evaluating them on the identity section and reading off
the underlying morphism of schemes; `BeauvilleLaszlo.Space.yoneda_hom_ext` and
`BeauvilleLaszlo.Space.left_congr` are the two book-keeping steps of that reduction, and
`BeauvilleLaszlo.Space.eqToHom_yoneda_app_left` records that a cast between the sections over
two equal objects of the slice does not change the underlying morphism.

`BeauvilleLaszlo.Space.square_of_section_left` keeps the two chains of base-change
isomorphisms, and the comparison isomorphism of the two double restrictions, as variables, and
asks for its hypothesis as a bare equality of two sections; and
`BeauvilleLaszlo.Space.exists_isPushout_section_of_iso` hands the identification back as data
rather than naming it. That is not stylistic. The
canonical base-change isomorphism
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso` unfolds through
`CategoryTheory.IsPullback.isoPullback` and `CategoryTheory.Limits.pullback.lift` to the fibre
product cone of schemes, and a cast `eqToHom h` between two iterated restrictions along
`AlgebraicGeometry.Spec.map`s makes the kernel attempt a K-reduction — that is, a definitional
comparison of the two restrictions, hence of two composites of `Spec.map`s. Either one makes
the kernel give up: the same statement with the cast replaced by an abstract morphism, or with
the isomorphisms replaced by variables, is checked in about a second. Marking a copy of the
isomorphism irreducible does not help, since reducibility attributes guide the elaborator and
the kernel ignores them, so the only remedy is to keep such terms out of the comparisons
altogether. That is what the shape of these statements does: every consumer obtains its
isomorphisms as local hypotheses and compares only those.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ v₁

namespace BeauvilleLaszlo.Space

open AlgebraicGeometry.BigFppfOver

/-- **Reading a pushout square of rings off a base-change identification.** If the base change
of `Spec A` over `Spec R` along `Spec R₂ ⟶ Spec R` is identified with `Spec A₂` over `Spec R₂`,
then the identification is the canonical one
(`AlgebraicGeometry.BigFppfOver.pullbackSpecOverIso`) for a pushout square of rings completing
`φ` and `ρ`. -/
private theorem exists_isPushout_of_pullbackIso (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂)
    (e : (Over.pullback (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
          (specOver B hX hA φ) ≅ specOver B hX₂ hA₂ φ₂) :
    ∃ (ψ : A ⟶ A₂) (hpo : IsPushout φ ρ ψ φ₂),
      pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo = e := by
  let i : B.obj hA₂ ≅ pullback (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) :=
    { hom := e.inv.left
      inv := e.hom.left
      hom_inv_id := by
        have := e.inv_hom_id
        exact congrArg CommaMorphism.left this
      inv_hom_id := by
        have := e.hom_inv_id
        exact congrArg CommaMorphism.left this }
  have hsnd : i.hom ≫ pullback.snd
      (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) =
      (ObjectProperty.homMk (Spec.map φ₂) : B.obj hA₂ ⟶ B.obj hX₂) := Over.w e.inv
  set u : Spec A₂ ⟶ Spec A := B.inclusion.map (i.hom ≫ pullback.fst
      (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)) with hu
  have hfst : i.hom ≫ pullback.fst
      (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) =
      (ObjectProperty.homMk (Spec.map (Spec.preimage u)) : B.obj hA₂ ⟶ B.obj hA) := by
    apply ObjectProperty.hom_ext
    rw [Spec.map_preimage]
    rfl
  have hcomm : CommSq
      (ObjectProperty.homMk (Spec.map (Spec.preimage u)) : B.obj hA₂ ⟶ B.obj hA)
      (ObjectProperty.homMk (Spec.map φ₂) : B.obj hA₂ ⟶ B.obj hX₂)
      (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) := by
    refine ⟨?_⟩
    rw [← hfst, ← hsnd, Category.assoc, Category.assoc, pullback.condition]
  have hpb : IsPullback
      (ObjectProperty.homMk (Spec.map (Spec.preimage u)) : B.obj hA₂ ⟶ B.obj hA)
      (ObjectProperty.homMk (Spec.map φ₂) : B.obj hA₂ ⟶ B.obj hX₂)
      (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) :=
    IsPullback.of_iso_pullback hcomm i hfst hsnd
  have hpb2 : IsPullback (Spec.map (Spec.preimage u)) (Spec.map φ₂) (Spec.map φ)
      (Spec.map ρ) := hpb.map B.inclusion
  have hpo : IsPushout φ ρ (Spec.preimage u) φ₂ :=
    IsPullback.op_iff.mp (IsPullback.of_map_of_faithful Scheme.Spec hpb2.flip)
  refine ⟨Spec.preimage u, hpo, Iso.ext (Over.OverMorphism.ext ?_)⟩
  rw [pullbackSpecOverIso_hom_left]
  have hio : (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ (Spec.preimage u) hpo).isoPullback.hom =
      i.hom :=
    pullback.hom_ext ((IsPullback.isoPullback_hom_fst _).trans hfst.symm)
      ((IsPullback.isoPullback_hom_snd _).trans hsnd.symm)
  exact congrArg Iso.inv (Iso.ext hio :
    (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ (Spec.preimage u) hpo).isoPullback = i)


/-- Three composable casts compose to a cast. The composite's proof is an argument, so that the
statement applies whatever that proof happens to be. -/
private theorem eqToHom_comp_eqToHom₃ {C : Type u₁} [Category.{v₁} C] {A A' A'' A''' : C}
    (p : A = A') (q : A' = A'') (r : A'' = A''') (h : A = A''') :
    (eqToHom p ≫ eqToHom q) ≫ eqToHom r = eqToHom h := by
  subst p
  subst q
  subst r
  simp

/-- A one-sided inverse of a cast is the opposite cast. -/
private theorem eq_eqToHom_symm {C : Type u₁} [Category.{v₁} C] {A A' : C} (h : A = A')
    (f : A' ⟶ A) (hf : eqToHom h ≫ f = 𝟙 A) : f = eqToHom h.symm := by
  subst h
  simpa using hf

/-- **Reading the compatibility square of a glueing triple off the compatibility of two
base-change chains.** The two say the same thing, but one is written with the triple's own
structure arrow `tR.hom` and the other with the composite `tR.inv ≫ m.hom` through which that
arrow enters the two chains; passing between them is cancelling the isomorphism `m` on the
right and then `tR` on the left.

Every morphism here is a variable: the two sides of the comparison this discharges are typed
through `BeauvilleLaszlo.Space.baseChange` on one side and
`CategoryTheory.OverShriek.relocalizeRestrict` on the other, two spellings of the same functor,
and a rewrite by associativity across the mixture has an ill-typed motive. With the morphisms
abstract there is no mixture to cross. -/
private theorem comp_eq_of_comp_iso_eq {C : Type u₁} [Category.{v₁} C]
    {X A Nl M Wp X' A' Nr : C}
    (p : X ⟶ Nl) (u : X ⟶ A) (cu : A ⟶ Nl) (tl : Nl ⟶ M)
    (s : X ⟶ X') (q : X' ⟶ Nr) (v : X' ⟶ A') (cv : A' ⟶ Nr)
    (tR : M ≅ Nr) (m : M ≅ Wp) (hp : p = u ≫ cu) (hq : q = v ≫ cv)
    (key : u ≫ cu ≫ tl ≫ m.hom = s ≫ v ≫ cv ≫ tR.inv ≫ m.hom) :
    p ≫ tl ≫ tR.hom = s ≫ q := by
  have h : u ≫ cu ≫ tl = s ≫ v ≫ cv ≫ tR.inv :=
    (Iso.cancel_iso_hom_right _ _ m).mp (by simpa using key)
  rw [hp, hq]
  simp [reassoc_of% h]

/-- Congruence for the underlying morphism of a morphism of a slice category. -/
private theorem left_congr {C : Type u₁} [Category.{v₁} C] {X : C} {V W : Over X}
    {x y : W ⟶ V} (hxy : x = y) : x.left = y.left :=
  congrArg (fun z : W ⟶ V => z.left) hxy

/-- Congruence for the underlying morphism of the value of a map of sections. -/
private theorem app_left_congr {C : Type u₁} [Category.{v₁} C] {X : C} {V W : Over X}
    {E : Type v₁} {f g : E ⟶ (W ⟶ V)} (hfg : f = g) (x : E) :
    (f x : W ⟶ V).left = (g x : W ⟶ V).left := by
  rw [hfg]

/-- A cast between the sections of a representable presheaf at two equal objects of the slice
does not change the underlying morphism. -/
private theorem eqToHom_yoneda_app_left {C : Type u₁} [Category.{v₁} C] {X : C} (V : Over X)
    {U : C} {p₁ p₂ : U ⟶ X} (hW : p₁ = p₂)
    (hp : (yoneda.obj V).obj (Opposite.op (Over.mk p₁)) =
      (yoneda.obj V).obj (Opposite.op (Over.mk p₂)))
    (t : Over.mk p₁ ⟶ V) : ((eqToHom hp) t).left = t.left := by
  subst hW
  rfl

/-- Two morphisms out of a representable presheaf agreeing on the identity section are
equal. -/
private theorem yoneda_hom_ext {C : Type u₁} [Category.{v₁} C] {X : C} {F : Cᵒᵖ ⥤ Type v₁}
    (a b : yoneda.obj X ⟶ F)
    (hab : a.app (Opposite.op X) (𝟙 X) = b.app (Opposite.op X) (𝟙 X)) : a = b := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_apply, yonedaEquiv_apply]
  exact hab

/-- **Restriction along a composite depends only on the composite.** -/
private theorem relocalizeRestrict_iter_eq (B : BigFppfSite.{u})
    {S M₁ M₂ T : Scheme.{u}} (hS : B.Contains S) (hM₁ : B.Contains M₁)
    (hM₂ : B.Contains M₂) (hT : B.Contains T)
    (a₁ : B.obj hS ⟶ B.obj hM₁) (b₁ : B.obj hM₁ ⟶ B.obj hT)
    (a₂ : B.obj hS ⟶ B.obj hM₂) (b₂ : B.obj hM₂ ⟶ B.obj hT)
    (hbase : a₁ ≫ b₁ = a₂ ≫ b₂) (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizeRestrict a₁).obj ((OverShriek.relocalizeRestrict b₁).obj F) =
      (OverShriek.relocalizeRestrict a₂).obj ((OverShriek.relocalizeRestrict b₂).obj F) := by
  change (Over.map a₁ ⋙ Over.map b₁).op ⋙ F = (Over.map a₂ ⋙ Over.map b₂).op ⋙ F
  rw [← Over.mapComp_eq, ← Over.mapComp_eq, hbase]

/-- The effect on a section of the cast identifying two iterated restrictions along morphisms
with equal composite: it does not change the underlying morphism of schemes. The morphism of
presheaves preceding the cast is kept abstract, so that no large term has to be unfolded. -/
private theorem comp_eqToHom_iter_app_left (B : BigFppfSite.{u})
    {S M₁ M₂ T : Scheme.{u}} (hS : B.Contains S) (hM₁ : B.Contains M₁)
    (hM₂ : B.Contains M₂) (hT : B.Contains T)
    (a₁ : B.obj hS ⟶ B.obj hM₁) (b₁ : B.obj hM₁ ⟶ B.obj hT)
    (a₂ : B.obj hS ⟶ B.obj hM₂) (b₂ : B.obj hM₂ ⟶ B.obj hT)
    (V : BigFppfOver B T hT) (W : BigFppfOver B S hS)
    (hW : (W.hom ≫ a₁) ≫ b₁ = (W.hom ≫ a₂) ≫ b₂)
    (h : (OverShriek.relocalizeRestrict a₁).obj
          ((OverShriek.relocalizeRestrict b₁).obj (yoneda.obj V)) =
        (OverShriek.relocalizeRestrict a₂).obj
          ((OverShriek.relocalizeRestrict b₂).obj (yoneda.obj V)))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (a : F ⟶ (OverShriek.relocalizeRestrict a₁).obj
      ((OverShriek.relocalizeRestrict b₁).obj (yoneda.obj V)))
    (t : F.obj (Opposite.op W)) :
    (((a ≫ eqToHom h).app (Opposite.op W)) t).left = ((a.app (Opposite.op W)) t).left := by
  rw [NatTrans.comp_app_apply, eqToHom_app]
  exact eqToHom_yoneda_app_left V hW _ _

/-- **The ring map underlying a single base-change identification.** Transporting the identity
section of `Spec A₂` back through the canonical base-change isomorphism attached to a pushout
square of rings gives the morphism of schemes `Spec.map ψ`. -/
private theorem relocalizeRestrictSpecOverIso_section_one (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    B.inclusion.map
      (((relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv.app
        (Opposite.op (specOver B hX₂ hA₂ φ₂))) (𝟙 (specOver B hX₂ hA₂ φ₂))).left =
      Spec.map ψ := by
  have hinv : (relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv =
      yoneda.map (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv ≫
        (OverShriek.restrictYonedaIso
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)
          (specOver B hX hA φ)).hom := rfl
  rw [hinv]
  simp only [NatTrans.comp_app_apply, yoneda_map_app, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk, Category.id_comp]
  rw [OverShriek.restrictYonedaIso_hom_app_left]
  exact (B.inclusion.map_comp _ _).trans
    (toScheme_map_pullbackSpecOverIso_inv_fst B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo)


/-- **Reading a pushout square of rings off an arbitrary base-change identification.** Any
identification of the restriction of `Spec A` with `Spec A₂` over `Spec R₂` is the canonical
one, so it comes with a ring map `ψ` completing `φ` and `ρ` to a pushout square, and it carries
the identity section of `Spec A₂` to `Spec.map ψ`.

The identification is an argument rather than a result, so that a consumer works with its own
local isomorphism throughout and never mentions
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso`. -/
private theorem exists_isPushout_section_of_iso (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂)
    (K : (OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
          (yoneda.obj (specOver B hX hA φ)) ≅ yoneda.obj (specOver B hX₂ hA₂ φ₂)) :
    ∃ ψ : A ⟶ A₂, IsPushout φ ρ ψ φ₂ ∧
      B.inclusion.map ((K.inv.app (Opposite.op (specOver B hX₂ hA₂ φ₂)))
        (𝟙 (specOver B hX₂ hA₂ φ₂))).left = Spec.map ψ := by
  obtain ⟨ψ, hpo, hpso⟩ := exists_isPushout_of_pullbackIso B hX hA hX₂ hA₂ φ ρ φ₂
    (yoneda.preimageIso ((OverShriek.restrictYonedaIso
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)
      (specOver B hX hA φ)) ≪≫ K))
  refine ⟨ψ, hpo, ?_⟩
  have hmap : yoneda.mapIso (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo) =
      (OverShriek.restrictYonedaIso
        (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)
        (specOver B hX hA φ)) ≪≫ K := by
    rw [hpso]
    exact Iso.ext (yoneda.map_preimage _)
  have hK : relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo = K := by
    apply Iso.ext
    change ((OverShriek.restrictYonedaIso
        (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)
        (specOver B hX hA φ)).symm ≪≫
      yoneda.mapIso (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo)).hom = K.hom
    rw [hmap]
    simp
  rw [← hK]
  exact relocalizeRestrictSpecOverIso_section_one B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo



/-- **Existence form of `BeauvilleLaszlo.Space.relocalizeRestrictSpecOverIso_section_one`.**
A pushout square of rings yields a base-change identification, as data, together with the
morphism of schemes it induces on the identity section. -/
private theorem exists_relocIso_section_one (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    ∃ I : (OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
        (yoneda.obj (specOver B hX hA φ)) ≅ yoneda.obj (specOver B hX₂ hA₂ φ₂),
      B.inclusion.map ((I.inv.app (Opposite.op (specOver B hX₂ hA₂ φ₂)))
        (𝟙 (specOver B hX₂ hA₂ φ₂))).left = Spec.map ψ :=
  ⟨relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo,
    relocalizeRestrictSpecOverIso_section_one B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo⟩

/-- **Composing two base-change identifications on the identity section.** All four presheaves
are variables here, which is what keeps the comparison cheap. -/
private theorem section_comp (B : BigFppfSite.{u})
    {S M T : Scheme.{u}} (hS : B.Contains S) (hM : B.Contains M) (hT : B.Contains T)
    (a : B.obj hS ⟶ B.obj hM) (b : B.obj hM ⟶ B.obj hT)
    (V : BigFppfOver B T hT) (V₁ : BigFppfOver B M hM) (W : BigFppfOver B S hS)
    (I : (OverShriek.relocalizeRestrict b).obj (yoneda.obj V) ≅ yoneda.obj V₁)
    (J : (OverShriek.relocalizeRestrict a).obj (yoneda.obj V₁) ≅ yoneda.obj W) :
    B.inclusion.map (((J.inv ≫ (OverShriek.relocalizeRestrict a).map I.inv).app
          (Opposite.op W)) (𝟙 W)).left =
      B.inclusion.map ((J.inv.app (Opposite.op W)) (𝟙 W)).left ≫
        B.inclusion.map ((I.inv.app (Opposite.op V₁)) (𝟙 V₁)).left := by
  have hnat := NatTrans.naturality_apply I.inv
    (Quiver.Hom.op ((J.inv.app (Opposite.op W)) (𝟙 W))) (𝟙 V₁)
  simp only [NatTrans.comp_app_apply, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    Functor.op_obj, Opposite.unop_op, yoneda_obj_map, Quiver.Hom.unop_op,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, Category.comp_id] at hnat ⊢
  have hobj : ∀ (t : (Over.map a).obj W ⟶ V₁)
      (x : ((OverShriek.relocalizeRestrict b).obj (yoneda.obj V)).obj (Opposite.op V₁)),
      (((OverShriek.relocalizeRestrict b).obj (yoneda.obj V)).map (Quiver.Hom.op t)) x =
        (Over.map b).map t ≫ x := fun _ _ => rfl
  rw [hnat, hobj]
  simp only [Over.comp_left, Over.map_map_left, Functor.map_comp]

/-- **The ring map underlying an iterated base-change identification.** Transporting the
identity section of `Spec A₃` back through the two canonical base-change isomorphisms of
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso` for the pushout squares `P` and
`Q` yields the morphism of schemes `Spec (ψ ≫ χ)`. -/
private theorem relocalizeRestrictSpecOverIso_section_left (B : BigFppfSite.{u})
    {R A R₂ A₂ R₃ A₃ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (hX₃ : B.Contains (Spec R₃)) (hA₃ : B.Contains (Spec A₃))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (σ : R₂ ⟶ R₃) (φ₂ : R₂ ⟶ A₂) (φ₃ : R₃ ⟶ A₃)
    (ψ : A ⟶ A₂) (χ : A₂ ⟶ A₃)
    (P : IsPushout φ ρ ψ φ₂) (Q : IsPushout φ₂ σ χ φ₃) :
    B.inclusion.map
      (((relocalizeRestrictSpecOverIso B hX₂ hA₂ hX₃ hA₃ φ₂ σ φ₃ χ Q).inv ≫
            (OverShriek.relocalizeRestrict
              (ObjectProperty.homMk (Spec.map σ) : B.obj hX₃ ⟶ B.obj hX₂)).map
            (relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ P).inv).app
          (Opposite.op (specOver B hX₃ hA₃ φ₃)) (𝟙 (specOver B hX₃ hA₃ φ₃))).left =
      Spec.map (ψ ≫ χ) := by
  rw [section_comp, relocalizeRestrictSpecOverIso_section_one B hX hA hX₂ hA₂ φ ρ φ₂ ψ P,
    relocalizeRestrictSpecOverIso_section_one B hX₂ hA₂ hX₃ hA₃ φ₂ σ φ₃ χ Q, Spec.map_comp]
  rfl


/-- **Existence form of `BeauvilleLaszlo.Space.relocalizeRestrictSpecOverIso_section_left`.**
The two base-change isomorphisms are returned as data, so that a consumer obtains them as
local hypotheses and never mentions
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso` itself. -/
private theorem exists_relocIso_pair (B : BigFppfSite.{u})
    {R A R₂ A₂ R₃ A₃ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (hX₃ : B.Contains (Spec R₃)) (hA₃ : B.Contains (Spec A₃))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (σ : R₂ ⟶ R₃) (φ₂ : R₂ ⟶ A₂) (φ₃ : R₃ ⟶ A₃)
    (ψ : A ⟶ A₂) (χ : A₂ ⟶ A₃)
    (P : IsPushout φ ρ ψ φ₂) (Q : IsPushout φ₂ σ χ φ₃) :
    ∃ (I : (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
            (yoneda.obj (specOver B hX hA φ)) ≅ yoneda.obj (specOver B hX₂ hA₂ φ₂))
      (J : (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map σ) : B.obj hX₃ ⟶ B.obj hX₂)).obj
            (yoneda.obj (specOver B hX₂ hA₂ φ₂)) ≅ yoneda.obj (specOver B hX₃ hA₃ φ₃)),
      (BigFppfOver.toScheme B (Spec R) hX).map
          ((J.inv ≫ (OverShriek.relocalizeRestrict
              (ObjectProperty.homMk (Spec.map σ) : B.obj hX₃ ⟶ B.obj hX₂)).map I.inv).app
            (Opposite.op (specOver B hX₃ hA₃ φ₃)) (𝟙 (specOver B hX₃ hA₃ φ₃))) =
        Spec.map (ψ ≫ χ) :=
  ⟨relocalizeRestrictSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ P,
    relocalizeRestrictSpecOverIso B hX₂ hA₂ hX₃ hA₃ φ₂ σ φ₃ χ Q,
    relocalizeRestrictSpecOverIso_section_left B hX hA hX₂ hA₂ hX₃ hA₃ φ ρ σ φ₂ φ₃ ψ χ P Q⟩


/-- **The comparison isomorphism of the two iterated base changes of a commutative square is
the canonical cast.** Stated and proved with the four morphisms of the square as variables: the
cast's two sides are definitionally comparable only through the morphisms of the square, so
with those abstract the comparison is immediate, where with `AlgebraicGeometry.Spec.map`s
substituted it is not. -/
private theorem squareBaseChangeIso_hom_app (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') (Y : AlgebraicSpaces B X hX)
    (h : (baseChange B U' U hU' hU gU).obj ((baseChange B U X hU hX jU).obj Y) =
      (baseChange B U' X' hU' hX' gX').obj ((baseChange B X' X hX' hX jX').obj Y)) :
    (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y =
      eqToHom h := by
  have e1 := baseChangeIterToDirectIso_hom_app_eqToHom B U' U X hU' hU hX gU jU Y
  have e2 : (baseChangeIterToDirectIso B U' X' X hU' hX' hX gX' jX').inv.app Y =
      eqToHom (by rfl) := rfl
  unfold squareBaseChangeIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app, e1, e2,
    eqToHom_app, Functor.comp_obj]
  exact eqToHom_comp_eqToHom₃ _ _ _ h


/-- **The comparison isomorphism of the square does not change the underlying morphism of a
section.** Again with the four morphisms of the square as variables. This is the only fact about
`BeauvilleLaszlo.Space.squareBaseChangeIso` that the outer square of a glueing triple needs. -/
private theorem squareBaseChangeIso_section_left (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (T : BigFppfOver B X hX) (W : BigFppfOver B U' hU')
    (u : yoneda.obj W ⟶ (OverShriek.relocalizeRestrict gX').obj
      ((OverShriek.relocalizeRestrict jX').obj (yoneda.obj T))) :
    B.inclusion.map (((u ≫ ((squareBaseChangeIso B U' U X' X hU' hU hX' hX
              gU gX' jU jX' hcomm).inv.app (schemeSpace T)).hom).app
          (Opposite.op W)) (𝟙 W)).left =
      B.inclusion.map ((u.app (Opposite.op W)) (𝟙 W)).left := by
  have hobj : (baseChange B U' U hU' hU gU).obj ((baseChange B U X hU hX jU).obj
        (schemeSpace T)) =
      (baseChange B U' X' hU' hX' gX').obj ((baseChange B X' X hX' hX jX').obj
        (schemeSpace T)) :=
    congrArg (fun k => (baseChange B U' X hU' hX k).obj (schemeSpace T)) hcomm
  have hinv : (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).inv.app
      (schemeSpace T) = eqToHom hobj.symm := by
    refine eq_eqToHom_symm hobj _ ?_
    rw [← squareBaseChangeIso_hom_app B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
      (schemeSpace T) hobj]
    exact (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX'
      hcomm).hom_inv_id_app (schemeSpace T)
  rw [hinv, fullSubcategory_eqToHom_hom hobj.symm]
  exact congrArg (fun t => B.inclusion.map t)
    (comp_eqToHom_iter_app_left B hU' hX' hU hX gX' jX' gU jU T W
      (by rw [Category.assoc, Category.assoc, hcomm])
      (relocalizeRestrict_iter_eq B hU' hX' hU hX gX' jX' gU jU hcomm.symm (yoneda.obj T))
      _ u (𝟙 W))

/-- **Two base-change identifications of a double restriction agree.** Suppose a presheaf
`yoneda.obj V` over `T` is identified, by two chains of base-change isomorphisms through
intermediate bases `M₁` and `M₂`, with `yoneda.obj W` over `S`; suppose a comparison
isomorphism `c` of the two double restrictions does not change the underlying morphism of a
section over `W`, and suppose the two chains carry the identity section of `W` to the same
morphism of schemes. Then the two chains agree up to `c`. -/
private theorem square_of_section_left (B : BigFppfSite.{u})
    {S M₁ M₂ T : Scheme.{u}} (hS : B.Contains S) (hM₁ : B.Contains M₁)
    (hM₂ : B.Contains M₂) (hT : B.Contains T)
    (a₁ : B.obj hS ⟶ B.obj hM₁) (b₁ : B.obj hM₁ ⟶ B.obj hT)
    (a₂ : B.obj hS ⟶ B.obj hM₂) (b₂ : B.obj hM₂ ⟶ B.obj hT)
    (V : BigFppfOver B T hT) (W : BigFppfOver B S hS)
    {G₁ : (BigFppfOver B M₁ hM₁)ᵒᵖ ⥤ Type u} {G₂ : (BigFppfOver B M₂ hM₂)ᵒᵖ ⥤ Type u}
    (I₁ : (OverShriek.relocalizeRestrict b₁).obj (yoneda.obj V) ≅ G₁)
    (I₂ : (OverShriek.relocalizeRestrict b₂).obj (yoneda.obj V) ≅ G₂)
    (I₃ : (OverShriek.relocalizeRestrict a₁).obj G₁ ≅ yoneda.obj W)
    (I₄ : (OverShriek.relocalizeRestrict a₂).obj G₂ ≅ yoneda.obj W)
    (c : (OverShriek.relocalizeRestrict a₁).obj
          ((OverShriek.relocalizeRestrict b₁).obj (yoneda.obj V)) ≅
      (OverShriek.relocalizeRestrict a₂).obj
          ((OverShriek.relocalizeRestrict b₂).obj (yoneda.obj V)))
    (hsec : ((I₃.inv ≫ (OverShriek.relocalizeRestrict a₁).map I₁.inv).app
          (Opposite.op W)) (𝟙 W) =
      (((I₄.inv ≫ (OverShriek.relocalizeRestrict a₂).map I₂.inv) ≫ c.inv).app
          (Opposite.op W)) (𝟙 W)) :
    (OverShriek.relocalizeRestrict a₁).map I₁.hom ≫ I₃.hom =
      c.hom ≫ ((OverShriek.relocalizeRestrict a₂).map I₂.hom ≫ I₄.hom) := by
  refine (Iso.inv_eq_inv
    ((OverShriek.relocalizeRestrict a₁).mapIso I₁ ≪≫ I₃)
    (c ≪≫ ((OverShriek.relocalizeRestrict a₂).mapIso I₂ ≪≫ I₄))).mp ?_
  change I₃.inv ≫ (OverShriek.relocalizeRestrict a₁).map I₁.inv =
    (I₄.inv ≫ (OverShriek.relocalizeRestrict a₂).map I₂.inv) ≫ c.inv
  exact yoneda_hom_ext _ _ hsec




/-- **A cartesian glueing triple identified with the triple of an algebraic space.** Given
identifications of the `U`- and `X'`-components of a cartesian triple `Z` with the two base
changes of `Y`, compatible with the glueing isomorphism of `Z` in the sense of `hsq`, the
canonical triple of `Y` is isomorphic to `Z`. The middle component of the isomorphism is forced:
the inner square of the triple of `Y` has the identity as its structure arrow, so it *defines*
the middle component as the conjugate of the `U`-component.

Stated with the four morphisms of the square as variables, so that no definitional comparison
here meets a term built from `AlgebraicGeometry.Spec.map`. -/
private noncomputable def glueingTripleIso (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    (eU : (baseChange B U X hU hX jU).obj Y ≅
      (overU B U' U X' hU' hU hX' gU gX').obj Z)
    (eX' : (baseChange B X' X hX' hX jX').obj Y ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj Z)
    (hsq : haveI : IsIso Z.obj.left.hom := Z.property.1
      (baseChange B U' U hU' hU gU).map eU.hom ≫ inv Z.obj.left.hom ≫ Z.obj.hom =
        (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y ≫
          (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (canonicalGlueingDataFunctor B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).obj Y ≅ Z := by
  haveI : IsIso Z.obj.left.hom := Z.property.1
  refine ObjectProperty.isoMk _ (Comma.isoMk (Comma.isoMk
    ((baseChange B U' U hU' hU gU).mapIso eU ≪≫ (asIso Z.obj.left.hom).symm) eU ?_) eX' ?_)
  · simp [canonicalGlueingDataFunctor, canonicalGlueingTriple]
  · exact hsq




/-- The comparison isomorphism of the two iterated base changes of a commutative square, read
on presheaves. -/
private noncomputable def squareBaseChangeIsoObj (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') (Y : AlgebraicSpaces B X hX) :
    ((baseChange B U' U hU' hU gU).obj ((baseChange B U X hU hX jU).obj Y)).obj ≅
      ((baseChange B U' X' hU' hX' gX').obj ((baseChange B X' X hX' hX jX').obj Y)).obj where
  hom := ((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y).hom
  inv := ((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).inv.app Y).hom
  hom_inv_id := congrArg (fun m => m.hom)
    ((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom_inv_id_app Y)
  inv_hom_id := congrArg (fun m => m.hom)
    ((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).inv_hom_id_app Y)


/-- **`BeauvilleLaszlo.Space.glueingTripleIso` with its data read on the underlying
presheaves.** The two component identifications and the compatibility square are asked for as
morphisms of presheaves rather than of algebraic spaces, which is how a consumer has them: it
builds them out of base-change identifications of representables.

The translation is a `rfl`, but a `rfl` between the `BeauvilleLaszlo.Space.baseChange` and the
`CategoryTheory.OverShriek.relocalizeRestrict` spelling of a double restriction, and performing
it where the four morphisms of the square are composites of `AlgebraicGeometry.Spec.map`s costs
the consumer its whole heartbeat budget and then defeats the kernel. Here the four are
variables and it is immediate. -/
private noncomputable def glueingTripleIsoOfPresheafIso (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    (eU : ((baseChange B U X hU hX jU).obj Y).obj ≅
      ((overU B U' U X' hU' hU hX' gU gX').obj Z).obj)
    (eX' : ((baseChange B X' X hX' hX jX').obj Y).obj ≅
      ((overX' B U' U X' hU' hU hX' gU gX').obj Z).obj)
    (hsq : haveI : IsIso Z.obj.left.hom := Z.property.1
      (OverShriek.relocalizeRestrict gU).map eU.hom ≫
          (inv Z.obj.left.hom).hom ≫ Z.obj.hom.hom =
        (squareBaseChangeIsoObj B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm Y).hom ≫
          (OverShriek.relocalizeRestrict gX').map eX'.hom) :
    (canonicalGlueingDataFunctor B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).obj Y ≅ Z :=
  glueingTripleIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm Y Z
    (ObjectProperty.isoMk _ eU) (ObjectProperty.isoMk _ eX')
    (by
      have : IsIso Z.obj.left.hom := Z.property.1
      exact ObjectProperty.hom_ext _ hsq)

/-- **The hypothesis of `BeauvilleLaszlo.Space.square_of_section_left`, reduced to an equality
of morphisms of schemes.** The two chains of base-change identifications agree on the identity
section as soon as the two composites of the morphisms of schemes they are built from agree;
the comparison isomorphism of the two double restrictions contributes nothing, by
`BeauvilleLaszlo.Space.squareBaseChangeIso_section_left`.

Stated with the four morphisms of the square, the four presheaf identifications, the four
objects of the slices and the comparison isomorphism all as variables, so that it is this
statement and not the consumer's that pays for the comparison of the two spellings of a double
restriction. The comparison isomorphism comes with its defining equation rather than written
out, so that the consumer's goal and this conclusion agree on the nose: matching them up to
that one unfolding instead is what defeats the kernel. -/
private theorem section_square_of_section_comp (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
    (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (V : BigFppfOver B X hX) (V₁ : BigFppfOver B U hU) (V₂ : BigFppfOver B X' hX')
    (W : BigFppfOver B U' hU')
    (I₁ : (OverShriek.relocalizeRestrict jU).obj (yoneda.obj V) ≅ yoneda.obj V₁)
    (I₂ : (OverShriek.relocalizeRestrict jX').obj (yoneda.obj V) ≅ yoneda.obj V₂)
    (K₁ : (OverShriek.relocalizeRestrict gU).obj (yoneda.obj V₁) ≅ yoneda.obj W)
    (K₂ : (OverShriek.relocalizeRestrict gX').obj (yoneda.obj V₂) ≅ yoneda.obj W)
    (c : (OverShriek.relocalizeRestrict gU).obj
          ((OverShriek.relocalizeRestrict jU).obj (yoneda.obj V)) ≅
        (OverShriek.relocalizeRestrict gX').obj
          ((OverShriek.relocalizeRestrict jX').obj (yoneda.obj V)))
    (hc : c = squareBaseChangeIsoObj B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
      (schemeSpace V))
    (hchain : B.inclusion.map ((K₁.inv.app (Opposite.op W)) (𝟙 W)).left ≫
          B.inclusion.map ((I₁.inv.app (Opposite.op V₁)) (𝟙 V₁)).left =
        B.inclusion.map ((K₂.inv.app (Opposite.op W)) (𝟙 W)).left ≫
          B.inclusion.map ((I₂.inv.app (Opposite.op V₂)) (𝟙 V₂)).left) :
    ((K₁.inv ≫ (OverShriek.relocalizeRestrict gU).map I₁.inv).app (Opposite.op W)) (𝟙 W) =
      (((K₂.inv ≫ (OverShriek.relocalizeRestrict gX').map I₂.inv) ≫ c.inv).app
        (Opposite.op W)) (𝟙 W) := by
  subst hc
  refine Over.OverMorphism.ext (B.inclusion.map_injective (Eq.trans ?_
    (squareBaseChangeIso_section_left B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm V W
      (K₂.inv ≫ (OverShriek.relocalizeRestrict gX').map I₂.inv)).symm))
  rw [section_comp B hU' hU hX gU jU V V₁ W I₁ K₁,
    section_comp B hU' hX' hX gX' jX' V V₂ W I₂ K₂]
  exact hchain

/-- **Glueability of a ring is glueability of the global sections of its spectrum.** The
`R`-module structure that `AlgebraicGeometry.Space.IsGlueableGlobalSections` puts on
`Γ(Spec A, ⊤)` is the one transported from `A` along `AlgebraicGeometry.Scheme.ΓSpecIso`, by
that isomorphism's naturality, so the two glueability statements correspond. -/
private theorem isGlueableGlobalSections_specOver {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) [Algebra R ↥A]
    (αA : CommRingCat.of R ⟶ A) (hαA : αA.hom = algebraMap R ↥A)
    (h : letI : Algebra R R' := g.toAlgebra
      BeauvilleLaszlo.IsGlueableFor (S := R') ↥A f) :
    AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX
      (BigFppfOver.specOver B hX hA αA) := by
  -- `let`, not `have`: the statement of
  -- `AlgebraicGeometry.Space.IsGlueableGlobalSections` carries these two instances in its own
  -- body, so the goal only matches while they are transparent here.
  let : Algebra R R' := g.toAlgebra
  let : Algebra R ↥Γ(Spec A, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map αA).appTop).hom).toAlgebra
  have hnat := Scheme.ΓSpecIso_inv_naturality αA
  have hcomm : ∀ r : R, algebraMap R ↥Γ(Spec A, ⊤) r =
      ((Scheme.ΓSpecIso A).inv).hom (algebraMap R ↥A r) := fun r => by
    rw [← hαA]
    exact (congrArg (fun m : CommRingCat.of R ⟶ Γ(Spec A, ⊤) => m.hom r) hnat).symm
  exact (BeauvilleLaszlo.isGlueableFor_linearEquiv_iff
    ({ (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv with
        commutes' := fun r => (hcomm r).symm } : ↥A ≃ₐ[R] ↥Γ(Spec A, ⊤)).toLinearEquiv f).mp h

/-- **Essential surjectivity of the Beauville--Laszlo glueing functor on affine glueable
algebraic spaces**, the remaining clause of Stacks 0F9Q. -/
public theorem canonicalAffineGlueableRestriction_essSurj {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).EssSurj := by
  constructor
  intro Z
  obtain ⟨TU, hTUaff, ⟨iU⟩⟩ := Z.property.1
  obtain ⟨TM, hTMaff, ⟨iM⟩⟩ := Z.property.2.1
  obtain ⟨TX', hTX'aff, ⟨iX'⟩⟩ := Z.property.2.2
  obtain ⟨A₁, hA₁, φ₁, ⟨kU⟩⟩ := BigFppfOver.exists_specOver B hU TU hTUaff
  obtain ⟨A'', hA'', μ, ⟨kM⟩⟩ := BigFppfOver.exists_specOver B hU' TM hTMaff
  obtain ⟨A', hA', φ', ⟨kX'⟩⟩ := BigFppfOver.exists_specOver B hX' TX' hTX'aff
  have : IsIso Z.obj.obj.left.hom := Z.obj.property.1
  have : IsIso Z.obj.obj.hom := Z.obj.property.2
  obtain ⟨cU, hcU⟩ : ∃ c : ((overU B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).obj Z.obj).obj ≅ yoneda.obj (specOver B hU hA₁ φ₁),
      c = iU ≪≫ yoneda.mapIso kU := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ : ∃ c : ((overU' B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).obj Z.obj).obj ≅ yoneda.obj (specOver B hU' hA'' μ),
      c = iM ≪≫ yoneda.mapIso kM := ⟨_, rfl⟩
  obtain ⟨cX', hcX'⟩ : ∃ c : ((overX' B _ _ _ hU' hU hX' (canGU g f B hU' hU)
      (canGX' g f B hU' hX')).obj Z.obj).obj ≅ yoneda.obj (specOver B hX' hA' φ'),
      c = iX' ≪≫ yoneda.mapIso kX' := ⟨_, rfl⟩
  obtain ⟨θL, hθL⟩ : ∃ t : ((overU' B _ _ _ hU' hU hX' (canGU g f B hU' hU)
        (canGX' g f B hU' hX')).obj Z.obj).obj ≅
      (OverShriek.relocalizeRestrict (canGU g f B hU' hU)).obj
        (((overU B _ _ _ hU' hU hX' (canGU g f B hU' hU)
          (canGX' g f B hU' hX')).obj Z.obj).obj),
      t = (ObjectProperty.ι _).mapIso (asIso Z.obj.obj.left.hom) := ⟨_, rfl⟩
  obtain ⟨θR, hθR⟩ : ∃ t : ((overU' B _ _ _ hU' hU hX' (canGU g f B hU' hU)
        (canGX' g f B hU' hX')).obj Z.obj).obj ≅
      (OverShriek.relocalizeRestrict (canGX' g f B hU' hX')).obj
        (((overX' B _ _ _ hU' hU hX' (canGU g f B hU' hU)
          (canGX' g f B hU' hX')).obj Z.obj).obj),
      t = (ObjectProperty.ι _).mapIso (asIso Z.obj.obj.hom) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K : (OverShriek.relocalizeRestrict (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (Localization.awayMap g f))) :
        B.obj hU' ⟶ B.obj hU)).obj (yoneda.obj (specOver B hU hA₁ φ₁)) ≅
      yoneda.obj (specOver B hU' hA'' μ),
      K = (OverShriek.relocalizeRestrict (canGU g f B hU' hU)).mapIso cU.symm ≪≫
        θL.symm ≪≫ cM := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K : (OverShriek.relocalizeRestrict (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))) :
        B.obj hU' ⟶ B.obj hX')).obj (yoneda.obj (specOver B hX' hA' φ')) ≅
      yoneda.obj (specOver B hU' hA'' μ),
      K = (OverShriek.relocalizeRestrict (canGX' g f B hU' hX')).mapIso cX'.symm ≪≫
        θR.symm ≪≫ cM := ⟨_, rfl⟩
  obtain ⟨ψ₁, P₃, hs₃⟩ := exists_isPushout_section_of_iso B hU hA₁ hU' hA'' φ₁
    (CommRingCat.ofHom (Localization.awayMap g f)) μ K₁
  obtain ⟨ψ₂, P₄, hs₄⟩ := exists_isPushout_section_of_iso B hX' hA' hU' hA'' φ'
    (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f)))) μ K₂
  have hbase : (CommRingCat.ofHom (algebraMap R (Localization.Away f))) ≫
      (CommRingCat.ofHom (Localization.awayMap g f)) =
      (CommRingCat.ofHom g) ≫
        (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f)))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    have h := B.inclusion.congr_map hcomm
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hw₃ : ∀ x, ψ₁.hom (φ₁.hom x) =
      μ.hom ((CommRingCat.ofHom (Localization.awayMap g f)).hom x) := fun x =>
    congrArg (fun m : CommRingCat.of (Localization.Away f) ⟶ A'' => m.hom x) P₃.w
  have hw₄ : ∀ x, ψ₂.hom (φ'.hom x) =
      μ.hom ((CommRingCat.ofHom (algebraMap R' (Localization.Away (g f)))).hom x) := fun x =>
    congrArg (fun m : CommRingCat.of R' ⟶ A'' => m.hom x) P₄.w
  have hwb : ∀ x : R, (CommRingCat.ofHom (Localization.awayMap g f)).hom
        ((CommRingCat.ofHom (algebraMap R (Localization.Away f))).hom x) =
      (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f)))).hom
        ((CommRingCat.ofHom g).hom x) := fun x =>
    congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of (Localization.Away (g f)) => m.hom x)
      hbase
  let : Algebra R R' := g.toAlgebra
  let : Algebra (Localization.Away f) ↥A₁ := φ₁.hom.toAlgebra
  let : Algebra R ↥A₁ := ((algebraMap (Localization.Away f) ↥A₁).comp
    (algebraMap R (Localization.Away f))).toAlgebra
  have : IsScalarTower R (Localization.Away f) ↥A₁ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R' ↥A' := φ'.hom.toAlgebra
  let : Algebra R ↥A' := ((algebraMap R' ↥A').comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' ↥A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (Localization.Away f) (Localization.Away (g f)) :=
    (Localization.awayMap g f).toAlgebra
  have : IsScalarTower R (Localization.Away f) (Localization.Away (g f)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsScalarTower.algebraMap_apply R R' (Localization.Away (g f)) x).trans (hwb x).symm
  let : Algebra (Localization.Away (g f)) ↥A'' := μ.hom.toAlgebra
  let : Algebra ↥A₁ ↥A'' := ψ₁.hom.toAlgebra
  let : Algebra ↥A' ↥A'' := ψ₂.hom.toAlgebra
  let : Algebra R' ↥A'' := ((algebraMap ↥A' ↥A'').comp (algebraMap R' ↥A')).toAlgebra
  have : IsScalarTower R' ↥A' ↥A'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R' (Localization.Away (g f)) ↥A'' :=
    IsScalarTower.of_algebraMap_eq hw₄
  let : Algebra R ↥A'' := ((algebraMap R' ↥A'').comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' ↥A'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R ↥A' ↥A'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (Localization.Away f) ↥A'' :=
    ((algebraMap ↥A₁ ↥A'').comp (algebraMap (Localization.Away f) ↥A₁)).toAlgebra
  have : IsScalarTower (Localization.Away f) ↥A₁ ↥A'' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (Localization.Away f) (Localization.Away (g f)) ↥A'' :=
    IsScalarTower.of_algebraMap_eq hw₃
  have : IsScalarTower R (Localization.Away (g f)) ↥A'' :=
    IsScalarTower.of_algebraMap_eq fun x => hw₄ (g x)
  have : IsScalarTower R (Localization.Away f) ↥A'' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (hw₄ (g x)).trans (((congrArg μ.hom (hwb x)).symm).trans (hw₃ _).symm)
  have : IsScalarTower R ↥A₁ ↥A'' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (hw₄ (g x)).trans (((congrArg μ.hom (hwb x)).symm).trans (hw₃ _).symm)
  have : Algebra.IsPushout (Localization.Away f) (Localization.Away (g f)) ↥A₁ ↥A'' :=
    CommRingCat.isPushout_iff_isPushout.mp P₃.flip
  have : Algebra.IsPushout R' (Localization.Away (g f)) ↥A' ↥A'' :=
    CommRingCat.isPushout_iff_isPushout.mp P₄.flip
  have hsub : Algebra.algebraMapSubmonoid ↥A' (Submonoid.powers (g f)) =
      Submonoid.powers (algebraMap R ↥A' f) := by
    change (Submonoid.powers (g f)).map (algebraMap R' ↥A') = _
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (IsScalarTower.algebraMap_apply R R' ↥A' f).symm
  have : IsLocalization.Away (algebraMap R ↥A' f) ↥A'' := by
    have h := (Algebra.isLocalization_iff_isPushout (Submonoid.powers (g f))
      (Localization.Away (g f)) (T := ↥A') (B := ↥A'')).mpr
      (Algebra.IsPushout.symm inferInstance)
    rwa [hsub] at h
  have hsub' : Algebra.algebraMapSubmonoid R' (Submonoid.powers f) =
      Submonoid.powers (g f) := by
    change (Submonoid.powers f).map (algebraMap R R') = _
    rw [Submonoid.map_powers]
    rfl
  have : Algebra.IsPushout R (Localization.Away f) R' (Localization.Away (g f)) := by
    refine Algebra.IsPushout.symm ((Algebra.isLocalization_iff_isPushout
      (Submonoid.powers f) (Localization.Away f) (T := R')
      (B := Localization.Away (g f))).mp ?_)
    rw [hsub']
    infer_instance
  have : Algebra.IsPushout R R' ↥A₁ ↥A'' :=
    Algebra.IsPushout.symm ((Algebra.IsPushout.comp_iff (R := R) (S := Localization.Away f)
      (T := ↥A₁) (R' := R') (S' := Localization.Away (g f)) (T' := ↥A'')).mpr
      (Algebra.IsPushout.symm inferInstance))
  obtain ⟨hAglue, hApo₁, hAloc, hApo₂⟩ := BeauvilleLaszlo.glueingSubalgebra_spec
    (R := R) (S := R') f hglue.1 hglue.2 (A' := ↥A') (A₁ := ↥A₁) (A'' := ↥A'')
  have hAcont : B.Contains (Spec (CommRingCat.of
      ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A''))) :=
    AlgebraicGeometry.BigFppfSite.contains_spec_of_injective B
      (AlgebraicGeometry.BigFppfSite.contains_spec_prod B hA' hA₁)
      (BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'').val.toRingHom
      fun _ _ h => Subtype.ext h
  have := hApo₁.symm
  have := hApo₂.symm
  obtain ⟨I₁, hI₁⟩ := exists_relocIso_section_one B hX hAcont hU hA₁ _ _ φ₁ _
    (CommRingCat.isPushout_of_isPushout R
      ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'') (Localization.Away f) ↥A₁)
  obtain ⟨I₂, hI₂⟩ := exists_relocIso_section_one B hX hAcont hX' hA' _ _ φ' _
    (CommRingCat.isPushout_of_isPushout R
      ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'') R' ↥A')
  refine ⟨⟨schemeSpace (BigFppfOver.specOver B hX hAcont (CommRingCat.ofHom
      (algebraMap R ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'')))), ?_, ?_⟩, ⟨?_⟩⟩
  · exact AlgebraicGeometry.Space.isAffineSpace_yoneda B _ hX _ inferInstance
  · exact isGlueableAlgebraicSpace_schemeSpace g f B hX hglue _ inferInstance
      (isGlueableGlobalSections_specOver g f B hX _ hAcont _ rfl
        ((BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact
          ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'') f).mpr hAglue))
  · refine ObjectProperty.isoMk _ (glueingTripleIsoOfPresheafIso B _ _ _ _ hU' hU hX' hX
      (canGU g f B hU' hU) (canGX' g f B hU' hX') (canJU f B hU hX) (canJX' g B hX' hX) hcomm
      _ Z.obj ?_ ?_ ?_)
    -- The two component identifications are given against the hole's own type, so that the
    -- elaborator never has to guess the two objects of the subcategory: inferring them from a
    -- type ascription on `CategoryTheory.ObjectProperty.isoMk` instead costs a minute of
    -- heartbeats here, which is most of this declaration's budget.
    · exact I₁ ≪≫ cU.symm
    · exact I₂ ≪≫ cX'.symm
    have key := square_of_section_left B hU' hU hX' hX (canGU g f B hU' hU)
      (canJU f B hU hX) (canGX' g f B hU' hX') (canJX' g B hX' hX)
      (BigFppfOver.specOver B hX hAcont (CommRingCat.ofHom
        (algebraMap R ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A''))))
      (BigFppfOver.specOver B hU' hA'' μ) I₁ I₂ K₁ K₂
      (squareBaseChangeIsoObj B _ _ _ _ hU' hU hX' hX (canGU g f B hU' hU)
        (canGX' g f B hU' hX') (canJU f B hU hX) (canJX' g B hX' hX) hcomm
        (schemeSpace (BigFppfOver.specOver B hX hAcont (CommRingCat.ofHom
          (algebraMap R ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'')))))) ?_
    · have e1 : (inv Z.obj.obj.left.hom).hom = θL.inv := by rw [hθL]; rfl
      have e2 : Z.obj.obj.hom.hom = θR.hom := by rw [hθR]; rfl
      rw [hK₁, hK₂] at key
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at key
      rw [e1, e2]
      exact comp_eq_of_comp_iso_eq _ _ _ _ _ _ _ _ θR cM
        ((OverShriek.relocalizeRestrict (canGU g f B hU' hU)).map_comp I₁.hom cU.inv)
        ((OverShriek.relocalizeRestrict (canGX' g f B hU' hX')).map_comp I₂.hom cX'.inv) key
    · have hglueeq : CommRingCat.ofHom
            (algebraMap ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'') ↥A₁) ≫ ψ₁ =
          CommRingCat.ofHom
            (algebraMap ↥(BeauvilleLaszlo.glueingSubalgebra R ↥A' ↥A₁ ↥A'') ↥A') ≫ ψ₂ := by
        ext x
        exact ((BeauvilleLaszlo.mem_glueingSubalgebra R ↥A' ↥A₁ ↥A'').mp x.2).symm
      refine section_square_of_section_comp B _ _ _ _ hU' hU hX' hX (canGU g f B hU' hU)
        (canGX' g f B hU' hX') (canJU f B hU hX) (canJX' g B hX' hX) hcomm _ _ _ _
        I₁ I₂ K₁ K₂ _ rfl ?_
      simp only [hs₃, hs₄, hI₁, hI₂]
      exact ((Spec.map_comp _ _).symm.trans (congrArg Spec.map hglueeq)).trans
        (Spec.map_comp _ _)

end BeauvilleLaszlo.Space

end
