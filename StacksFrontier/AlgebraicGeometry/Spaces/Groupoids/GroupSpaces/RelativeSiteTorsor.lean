module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfSheafTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceTorsorActions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsors over an arbitrary object of the big fppf site, and torsors on the localized site

Let `U` be an object of the big fppf site of `S`, let `G` be a group object of the category of
presheaves over the representable presheaf of `U` and let `X` be an object acted on by it.
This file compares that action with a torsor on the localized site `(Sch/U)_fppf`, the way
Stacks 04TZ compares an action over the terminal presheaf with a torsor on the big site
itself.

The comparison is needed because the two renderings of a torsor in this development do not
otherwise meet. Effective descent for torsors under a sheaf of groups is available on the
localized sites (Stacks 04UK), while the hypotheses and the conclusion of Stacks 04U1 are
stated for actions of group objects over a base which is not the terminal presheaf; the
existing comparison hardwires the base to be terminal, so its ingredients are of no use over
`U`.

## Main definitions

* `AlgebraicGeometry.Space.sliceSection`: the presheaf on `(Sch/U)_fppf` of sections of an
  object over the representable presheaf of `U`, that is the *fibre* of its underlying
  presheaf over the tautological section.
* `AlgebraicGeometry.Space.sliceSectionEquiv`: those sections are the morphisms into the
  object from the presentation of the test object of the localized site.
* `AlgebraicGeometry.Space.sliceSheafOfGroups` and
  `AlgebraicGeometry.Space.slicePseudoTorsor`: the sheaf of groups and the pseudo-torsor on
  `(Sch/U)_fppf` attached to a group object over `U` and to a pseudo-torsor action of it.
* `AlgebraicGeometry.Space.IsRelativeSiteTorsor`: the condition that the sections of the
  acted-on object form a torsor on the localized site under the sections of the group object,
  with both presheaves identified and both actions agreeing.

## Main results

* `AlgebraicGeometry.Space.isSheaf_sliceSection`: the fibre of the underlying presheaf of an
  object over the representable presheaf of `U` over the tautological section is a sheaf on
  the localized site. This is *not* the restriction of the presheaf to the localized site, so
  the glueing of restrictions does not give it; what gives it is the fibre criterion of
  Stacks 00Y1 together with the sheaf condition on the representable presheaf of `U`, that is
  subcanonicality of the fppf topology, which here is a projection of
  `AlgebraicGeometry.IsAlgebraicSpace`.
* `AlgebraicGeometry.Space.isTorsor_slicePseudoTorsor`: a pseudo-torsor trivialized by an fppf
  covering of the representable presheaf of `U` gives a *torsor* on the localized site, that
  is a locally nonempty one.
* `AlgebraicGeometry.Space.isTorsor_slicePseudoTorsor_of_isLocallySurjective`: the same
  conclusion from local surjectivity of the structure morphism, which is the form the torsor
  condition takes in Stacks 04UL, and which therefore covers the acting group of a torsor over
  a section of an arbitrary base sheaf.
* `AlgebraicGeometry.Space.isRelativeSiteTorsor_of_isFppfTorsor`: **the relative form of
  Stacks 04TZ in the direction from algebraic spaces to the site**, at an arbitrary object `U`
  of the big fppf site rather than only at a terminal one.
* `AlgebraicGeometry.Space.isPseudoTorsor_of_relativeSiteTorsorData`: the converse direction
  for the pseudo-torsor condition.
* `AlgebraicGeometry.Space.exists_isFppfCovering_trivializing_of_isTorsor`: the converse
  direction for the trivializing covering, which recovers an fppf covering of the
  representable presheaf of `U` after which the acted-on object has a section.
* `AlgebraicGeometry.Space.isFppfTorsor_iff_isRelativeSiteTorsor`: **the relative form of
  Stacks 04TZ**, the biconditional between being an fppf torsor of algebraic spaces over the
  representable presheaf of an arbitrary object `U` of the big fppf site and being a torsor on
  the localized site `(Sch/U)_fppf`.
* `AlgebraicGeometry.Space.isRelativeSiteTorsor_of_isSheafTorsor`: an object of the category
  `𝒢/ℬ-Torsors` of Stacks 04UL is a torsor on the localized site; the sheaf condition on the
  acting group, which `AlgebraicGeometry.Space.SheafTorsors` omits, comes from the sheaf
  conditions on `ℬ` and on `𝒢`.
* `AlgebraicGeometry.Space.isPseudoTorsor_overYonedaObj` and
  `AlgebraicGeometry.Space.isLocallySurjective_overYonedaObj`: a torsor on the localized site
  manufactures an action of group objects over the representable presheaf of `U` which is a
  pseudo-torsor with locally surjective structure morphism, by
  `PseudoTorsor.overYonedaModObj`.

## Implementation notes

The sections of an object `F` over the representable presheaf of `U` over a test object
`(V, a)` of the localized site are the sections of the underlying presheaf of `F` over `V`
whose image in the representable presheaf is `a`; equivalently they are the morphisms
`Over.mk (yoneda.map a) ⟶ F` of the slice, which is how the group structure and the action on
them are obtained from the group object and the action. That identification is
`AlgebraicGeometry.Space.sliceSectionEquiv`, and it is natural in the test object by the Yoneda
lemma.

Local nonemptiness on the localized site is obtained from local triviality of the action, not
from the pseudo-torsor condition: a section of the base over a test object factors through a
member of the trivializing fppf covering only after a further covering sieve of the test
object, which is `AlgebraicGeometry.Space.exists_sieve_lift_of_isFppfCovering`, and the section
of the restriction over that member is carried back by composition.

## References

* [Stacks Project, Tag 04TZ](https://stacks.math.columbia.edu/tag/04TZ)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {U : BigFppfOver 𝒞 S hS}

/-! ### The sections of an object over the representable presheaf of `U` -/

/-- The presheaf on the localized site `(Sch/U)_fppf` of sections of an object over the
representable presheaf of `U`: its sections over a test object `(V, a)` are the sections of
the underlying presheaf over `V` whose image in the representable presheaf of `U` is `a`. -/
abbrev sliceSection (F : Over (yoneda.obj U)) : (Over U)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj U)) F.hom

variable (𝒞 S hS) in
/-- **The fibre over the tautological section is a sheaf on the localized site.** A compatible
family of sections of the fibre amalgamates in the restriction of the underlying presheaf to
the localized site, and the amalgamation lies in the fibre because the representable presheaf
of `U` is separated for the fppf topology. -/
theorem isSheaf_sliceSection (F : Over (yoneda.obj U))
    (hF : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) F.left) :
    Presheaf.IsSheaf ((BigFppfOver.topology 𝒞 S hS).over U) (sliceSection F) := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine OverShriek.isSheaf_fiber _ _ ?_ ?_
  · exact (isSheaf_iff_isSheaf_of_type _ _).1
      (((BigFppfOver.topology 𝒞 S hS).overPullback (Type u) U).obj ⟨F.left, hF⟩).property
  · exact ((isSheaf_iff_isSheaf_of_type _ _).1
      (((BigFppfOver.topology 𝒞 S hS).overPullback (Type u) U).obj
        ⟨yoneda.obj U, (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf⟩).property).isSeparated

/-- A test object of the localized site, presented as an object over the representable
presheaf of `U`. -/
abbrev sliceOver (W : Over U) : Over (yoneda.obj U) :=
  Over.mk (yoneda.map W.hom)

/-- **The sections of an object over the representable presheaf of `U` are the morphisms into
it.** Over a test object `(V, a)` of the localized site they are the morphisms of the slice
from `Over.mk (yoneda.map a)`, by the Yoneda lemma. -/
def sliceSectionEquiv (F : Over (yoneda.obj U)) (W : Over U) :
    (sliceOver W ⟶ F) ≃ (sliceSection F).obj (op W) where
  toFun φ := ⟨yonedaEquiv φ.left, by
    rw [← yonedaEquiv_comp, Over.w φ]
    exact yonedaEquiv_yoneda_map W.hom⟩
  invFun s := Over.homMk (yonedaEquiv.symm s.1) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact s.2.trans (yonedaEquiv_yoneda_map W.hom).symm)
  left_inv φ := Over.OverMorphism.ext (yonedaEquiv.symm_apply_apply φ.left)
  right_inv s := Subtype.ext (yonedaEquiv.apply_symm_apply s.1)

/-- The morphism of the slice over the representable presheaf of `U` relating the
presentations of two test objects of the localized site along a morphism between them. -/
def sliceRestrict {W W' : Over U} (g : W' ⟶ W) : sliceOver W' ⟶ sliceOver W :=
  Over.homMk (yoneda.map g.left) (by
    change yoneda.map g.left ≫ yoneda.map W.hom = yoneda.map W'.hom
    rw [← Functor.map_comp, Over.w g])

/-- Restricting a section along a morphism of the localized site corresponds, under
`AlgebraicGeometry.Space.sliceSectionEquiv`, to precomposing the morphism it represents. -/
theorem sliceSectionEquiv_map (F : Over (yoneda.obj U)) {W W' : (Over U)ᵒᵖ} (g : W ⟶ W')
    (φ : sliceOver W.unop ⟶ F) :
    (sliceSection F).map g (sliceSectionEquiv F W.unop φ) =
      sliceSectionEquiv F W'.unop (sliceRestrict g.unop ≫ φ) := by
  apply Subtype.ext
  simp only [sliceSectionEquiv]
  exact yonedaEquiv_naturality φ.left g.unop.left

/-! ### The sheaf of groups and the pseudo-torsor on the localized site -/

/-- The sheaf of groups on the localized site `(Sch/U)_fppf` of sections of a group object
over the representable presheaf of `U`: its sections over a test object form a group because
they are the morphisms into a group object. -/
def sliceSheafOfGroups (G : Over (yoneda.obj U)) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left) :
    SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U) where
  presheaf := sliceSection G
  isSheaf := isSheaf_sliceSection 𝒞 S hS G hG
  group W := Equiv.group (sliceSectionEquiv G W.unop).symm
  map_mul := by
    intro W W' g g₁ g₂
    rw [Equiv.mul_def (sliceSectionEquiv G W.unop).symm g₁ g₂]
    simp only [Equiv.symm_symm]
    rw [sliceSectionEquiv_map]
    have hres : ∀ a : (sliceSection G).obj W,
        (sliceSection G).map g a = sliceSectionEquiv G W'.unop
          (sliceRestrict g.unop ≫ (sliceSectionEquiv G W.unop).symm a) := by
      intro a
      simpa only [Equiv.apply_symm_apply] using
        sliceSectionEquiv_map G g ((sliceSectionEquiv G W.unop).symm a)
    rw [hres g₁, hres g₂, Equiv.mul_def (sliceSectionEquiv G W'.unop).symm]
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
    exact congrArg _ (MonObj.comp_mul _ _ _)

/-- The unit of the group of sections of a group object over the representable presheaf of
`U` is the identity morphism of the presentation of the test object. -/
theorem sliceSheafOfGroups_one (G : Over (yoneda.obj U)) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left) (W : (Over U)ᵒᵖ) :
    (1 : (sliceSheafOfGroups G hG).presheaf.obj W) = sliceSectionEquiv G W.unop 1 :=
  rfl

/-- The group law on the sections of a group object over the representable presheaf of `U` is
the one transported from the morphisms into it. -/
theorem sliceSheafOfGroups_mul (G : Over (yoneda.obj U)) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left) (W : (Over U)ᵒᵖ)
    (g h : (sliceSheafOfGroups G hG).presheaf.obj W) :
    g * h = sliceSectionEquiv G W.unop
      ((sliceSectionEquiv G W.unop).symm g * (sliceSectionEquiv G W.unop).symm h) :=
  rfl

/-- The action of the sections of a group object over the representable presheaf of `U` on the
sections of an object it acts on, over a test object of the localized site. -/
def sliceAction (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X] (W : Over U)
    (g : (sliceSection G).obj (op W)) (x : (sliceSection X).obj (op W)) :
    (sliceSection X).obj (op W) :=
  sliceSectionEquiv X W
    ((sliceSectionEquiv G W).symm g • (sliceSectionEquiv X W).symm x)

/-- The action on sections is the action in the slice, read through the identification of
sections with morphisms. -/
@[simp]
theorem sliceAction_apply (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X] (W : Over U)
    (g : sliceOver W ⟶ G) (x : sliceOver W ⟶ X) :
    sliceAction G X W (sliceSectionEquiv G W g) (sliceSectionEquiv X W x) =
      sliceSectionEquiv X W (g • x) := by
  simp only [sliceAction, Equiv.symm_apply_apply]

/-- A pseudo-torsor action of group objects over the representable presheaf of `U`, viewed as
a pseudo-torsor of sheaves on the localized site `(Sch/U)_fppf` under the sheaf of groups of
sections. -/
def slicePseudoTorsor (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X.left)
    (hp : IsPseudoTorsor G X) :
    PseudoTorsor.{u} (sliceSheafOfGroups G hG) where
  presheaf := sliceSection X
  isSheaf := isSheaf_sliceSection 𝒞 S hS X hX
  act W g x := sliceAction G X W.unop g x
  one_act := by
    intro W s
    obtain ⟨b, rfl⟩ := (sliceSectionEquiv X W.unop).surjective s
    rw [sliceSheafOfGroups_one, sliceAction_apply, one_smul]
  mul_act := by
    intro W g h s
    rw [sliceSheafOfGroups_mul]
    obtain ⟨a, rfl⟩ := (sliceSectionEquiv G W.unop).surjective g
    obtain ⟨c, rfl⟩ := (sliceSectionEquiv G W.unop).surjective h
    obtain ⟨b, rfl⟩ := (sliceSectionEquiv X W.unop).surjective s
    simp only [Equiv.symm_apply_apply, sliceAction_apply, mul_smul]
  naturality := by
    intro W W' f g x
    obtain ⟨a, rfl⟩ := (sliceSectionEquiv G W.unop).surjective g
    obtain ⟨b, rfl⟩ := (sliceSectionEquiv X W.unop).surjective x
    change (sliceSection X).map f (sliceAction G X W.unop
        (sliceSectionEquiv G W.unop a) (sliceSectionEquiv X W.unop b)) =
      sliceAction G X W'.unop ((sliceSection G).map f (sliceSectionEquiv G W.unop a))
        ((sliceSection X).map f (sliceSectionEquiv X W.unop b))
    rw [sliceAction_apply, sliceSectionEquiv_map, sliceSectionEquiv_map,
      sliceSectionEquiv_map, sliceAction_apply, ModObj.comp_smul]
  simplyTransitive := by
    intro W _ s t
    obtain ⟨x, rfl⟩ := (sliceSectionEquiv X W.unop).surjective s
    obtain ⟨y, rfl⟩ := (sliceSectionEquiv X W.unop).surjective t
    obtain ⟨g, hg, huniq⟩ := (isPseudoTorsor_iff_points 𝒞 S hS (yoneda.obj U) G X).1 hp
      W.unop.left (yoneda.map W.unop.hom) x y
    refine ⟨sliceSectionEquiv G W.unop g, ?_, ?_⟩
    · change sliceAction G X W.unop (sliceSectionEquiv G W.unop g)
        (sliceSectionEquiv X W.unop x) = sliceSectionEquiv X W.unop y
      rw [sliceAction_apply, hg]
    · intro g' hg'
      obtain ⟨a, rfl⟩ := (sliceSectionEquiv G W.unop).surjective g'
      replace hg' : sliceAction G X W.unop (sliceSectionEquiv G W.unop a)
          (sliceSectionEquiv X W.unop x) = sliceSectionEquiv X W.unop y := hg'
      rw [sliceAction_apply] at hg'
      exact congrArg _ (huniq a ((sliceSectionEquiv X W.unop).injective hg'))

/-! ### Local nonemptiness from local triviality -/

variable (𝒞 S hS) in
/-- **Local triviality becomes local nonemptiness.** A pseudo-torsor whose structure morphism
has sections after an fppf covering of the representable presheaf of `U` gives a torsor on the
localized site: over a test object the tautological section factors through a member of the
covering after a covering sieve
(`AlgebraicGeometry.Space.exists_sieve_lift_of_isFppfCovering`), and the section over that
member composes with the factorization to a section over the member of the sieve. -/
theorem isTorsor_slicePseudoTorsor (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X.left)
    (hp : IsPseudoTorsor G X) {I : Type (u + 1)}
    (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ yoneda.obj U)
    (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (hsec : ∀ i, Nonempty (𝟙_ (Over (Bᵢ i)) ⟶ (Over.pullback (f i)).obj X)) :
    (slicePseudoTorsor G X hG hX hp).IsTorsor := by
  intro W
  obtain ⟨R, hR, hlift⟩ := exists_sieve_lift_of_isFppfCovering 𝒞 S hS Bᵢ f hcov W.left
    (yoneda.map W.hom)
  refine ⟨(Sieve.overEquiv W).symm R,
    (BigFppfOver.topology 𝒞 S hS).overEquiv_symm_mem_over W R hR, ?_⟩
  intro W' k hk
  obtain ⟨i, c', hc'⟩ := hlift k.left hk
  obtain ⟨t, ht⟩ := (nonempty_unitHom_pullback_iff (f i) X).1 (hsec i)
  refine ⟨⟨yonedaEquiv (c' ≫ t), ?_⟩⟩
  rw [← yonedaEquiv_comp, Category.assoc, ht, hc', ← Functor.map_comp, Over.w k]
  exact yonedaEquiv_yoneda_map W'.hom

variable (𝒞 S hS) in
/-- **Local surjectivity becomes local nonemptiness.** This is the same conclusion as
`AlgebraicGeometry.Space.isTorsor_slicePseudoTorsor` from the hypothesis in which Stacks 04UL
packages it: the structure morphism to the representable presheaf of `U` is locally
surjective. The sieve of arrows along which the tautological section lifts is a covering sieve
of the test object, and a lift along one of them is a section of the fibre over the restricted
tautological section.

In particular this applies to the acting group `U ×_{b, ℬ} 𝒢` of a torsor over a section `b`
of an arbitrary base sheaf `ℬ`, whose underlying object over the representable presheaf of `U`
is a group object exactly as here. -/
theorem isTorsor_slicePseudoTorsor_of_isLocallySurjective (G X : Over (yoneda.obj U))
    [GrpObj G] [ModObj G X]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.left)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X.left)
    (hp : IsPseudoTorsor G X)
    (hls : Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) X.hom) :
    (slicePseudoTorsor G X hG hX hp).IsTorsor := by
  intro W
  refine ⟨(Sieve.overEquiv W).symm (Presheaf.imageSieve X.hom W.hom),
    (BigFppfOver.topology 𝒞 S hS).overEquiv_symm_mem_over W _ (hls.imageSieve_mem W.hom), ?_⟩
  rintro W' k ⟨s, hs⟩
  exact ⟨⟨s, hs.trans (Over.w k)⟩⟩

/-! ### The relative form of Stacks 04TZ -/

variable (𝒞 S hS) in
/-- An action of group objects over the representable presheaf of `U` is a *torsor on the
localized site* when the sections of the acted-on object form a torsor in the sense of
Stacks 03AH on `(Sch/U)_fppf` under the sheaf of groups of sections of the group object, the
two sheaves being identified with the presheaves of sections and the two actions agreeing over
every test object. -/
def IsRelativeSiteTorsor (U : BigFppfOver 𝒞 S hS) (G X : Over (yoneda.obj U)) [GrpObj G]
    [ModObj G X] : Prop :=
  ∃ (H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U))
    (F : PseudoTorsor.{u} H) (eG : H.presheaf ≅ sliceSection G)
    (eX : F.presheaf ≅ sliceSection X), F.IsTorsor ∧
      ∀ (W : Over U) (g : H.presheaf.obj (op W)) (x : F.presheaf.obj (op W)),
        eX.hom.app (op W) (F.act (op W) g x) =
          sliceAction G X W (eG.hom.app (op W) g) (eX.hom.app (op W) x)

variable (𝒞 S hS) in
/-- **The relative form of Stacks 04TZ, from algebraic spaces to the site.** An fppf torsor of
algebraic spaces over the representable presheaf of an arbitrary object `U` of the big fppf
site is a torsor on the localized site `(Sch/U)_fppf`: its sections form a pseudo-torsor
(`AlgebraicGeometry.Space.slicePseudoTorsor`), which is locally nonempty by
`AlgebraicGeometry.Space.isTorsor_slicePseudoTorsor`. -/
theorem isRelativeSiteTorsor_of_isFppfTorsor (hU : IsAlgebraicSpace 𝒞 S hS (yoneda.obj U))
    (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (h : IsFppfTorsor 𝒞 S hS (yoneda.obj U) hU G X hG hX) :
    IsRelativeSiteTorsor 𝒞 S hS U G X := by
  obtain ⟨hp, I, Bᵢ, f, _, hcov, hsec⟩ := h
  exact ⟨sliceSheafOfGroups G hG.isSheaf,
    slicePseudoTorsor G X hG.isSheaf hX.isSheaf hp, Iso.refl _, Iso.refl _,
    isTorsor_slicePseudoTorsor 𝒞 S hS G X hG.isSheaf hX.isSheaf hp Bᵢ f hcov hsec,
    fun _ _ _ => rfl⟩

variable (𝒞 S hS) in
/-- **The relative form of Stacks 04TZ, the pseudo-torsor half of the converse.** A torsor on
the localized site whose sheaf of groups and whose underlying sheaf are the presheaves of
sections of a group object and of an object it acts on, compatibly with the actions, arises
from a pseudo-torsor action.

Over a test object of the localized site the action on sections is simply transitive, and the
points of the acted-on object over the presentation of that test object are exactly those
sections (`AlgebraicGeometry.Space.sliceSectionEquiv`), so the pointwise criterion
`AlgebraicGeometry.Space.isPseudoTorsor_iff_points` applies. -/
@[sga "3 III 0.1" "(i) ⇒ (ii)"]
theorem isPseudoTorsor_of_relativeSiteTorsorData (G X : Over (yoneda.obj U)) [GrpObj G]
    [ModObj G X]
    (H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U))
    (F : PseudoTorsor.{u} H) (eG : H.presheaf ≅ sliceSection G)
    (eX : F.presheaf ≅ sliceSection X)
    (hact : ∀ (W : Over U) (g : H.presheaf.obj (op W)) (x : F.presheaf.obj (op W)),
      eX.hom.app (op W) (F.act (op W) g x) =
        sliceAction G X W (eG.hom.app (op W) g) (eX.hom.app (op W) x)) :
    IsPseudoTorsor G X := by
  refine (isPseudoTorsor_iff_points 𝒞 S hS (yoneda.obj U) G X).2 fun T b x y => ?_
  obtain ⟨a, rfl⟩ : ∃ a : T ⟶ U, yoneda.map a = b :=
    ⟨yonedaEquiv b, yonedaEquiv.injective (yonedaEquiv_yoneda_map _)⟩
  let W : Over U := Over.mk a
  have hinv : ∀ z, eX.hom.app (op W) (eX.inv.app (op W) z) = z := fun z => by simp
  obtain ⟨gF, hgy, huniq⟩ := F.simplyTransitive (op W)
    ⟨eX.inv.app (op W) (sliceSectionEquiv X W x)⟩
    (eX.inv.app (op W) (sliceSectionEquiv X W x))
    (eX.inv.app (op W) (sliceSectionEquiv X W y))
  refine ⟨(sliceSectionEquiv G W).symm (eG.hom.app (op W) gF), ?_, ?_⟩
  · apply (sliceSectionEquiv X W).injective
    have h := hact W gF (eX.inv.app (op W) (sliceSectionEquiv X W x))
    rw [hgy, hinv, hinv] at h
    rw [h]
    simp only [sliceAction, Equiv.symm_apply_apply]
  · intro g' hg'
    have hGinv : eG.hom.app (op W) (eG.inv.app (op W) (sliceSectionEquiv G W g')) =
        sliceSectionEquiv G W g' := by simp
    have h := hact W (eG.inv.app (op W) (sliceSectionEquiv G W g'))
      (eX.inv.app (op W) (sliceSectionEquiv X W x))
    rw [hinv, hGinv] at h
    have hval : eX.hom.app (op W) (F.act (op W) (eG.inv.app (op W)
        (sliceSectionEquiv G W g')) (eX.inv.app (op W) (sliceSectionEquiv X W x))) =
        eX.hom.app (op W) (eX.inv.app (op W) (sliceSectionEquiv X W y)) := by
      rw [h, sliceAction_apply, hg', hinv]
    rw [Equiv.eq_symm_apply, ← hGinv, huniq _ ((eX.app (op W)).toEquiv.injective hval)]

variable (𝒞 S hS) in
/-- **The relative form of Stacks 04TZ, the trivializing covering of the converse.** A torsor
on the localized site whose underlying sheaf is the presheaf of sections of an object over the
representable presheaf of `U` makes that object have a section after an fppf covering of the
representable presheaf.

The terminal object `(U, 𝟙 U)` of the localized site carries a covering sieve over which the
torsor has sections; a chosen covering family of the big fppf site refining that sieve
(`AlgebraicGeometry.BigFppfOver.exists_isCovering_of_mem_topology`) becomes an fppf covering of
algebraic spaces under Yoneda, by `AlgebraicGeometry.Space.isFppfCovering_yoneda_map`; and the
section over a member of the family is, through `AlgebraicGeometry.Space.sliceSectionEquiv`, a
factorization of that member through the structure morphism. -/
@[sga "3 IV 5.1.5" "(i) ⇒ (ii)"]
theorem exists_isFppfCovering_trivializing_of_isTorsor (X : Over (yoneda.obj U))
    {H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U)}
    (F : PseudoTorsor.{u} H) (eX : F.presheaf ≅ sliceSection X) (hFT : F.IsTorsor) :
    ∃ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
      (f : ∀ i, Bᵢ i ⟶ yoneda.obj U), (∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) ∧
        IsFppfCovering 𝒞 S hS Bᵢ f ∧
          ∀ i, Nonempty (𝟙_ (Over (Bᵢ i)) ⟶ (Over.pullback (f i)).obj X) := by
  obtain ⟨R, hR, hRloc⟩ := hFT (Over.mk (𝟙 U))
  obtain ⟨E, hE, hET⟩ := BigFppfOver.exists_isCovering_of_mem_topology 𝒞 S hS
    (((BigFppfOver.topology 𝒞 S hS).mem_over_iff R).1 hR)
  have hgeom :=
    BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering 𝒞 hE
  refine ⟨E.I₀, fun i => yoneda.obj (E.X i), fun i => yoneda.map (E.f i),
    fun i => isAlgebraicSpace_yoneda 𝒞 S hS (E.X i),
    isFppfCovering_yoneda_map 𝒞 S hS E.X E.f (fun i => (hgeom.2 i).1)
      (fun i => (hgeom.2 i).2) (fun x => hgeom.1 x), fun i => ?_⟩
  have hqi : R (Over.homMk (E.f i) (Category.comp_id _) :
      (Over.mk (E.f i) : Over U) ⟶ Over.mk (𝟙 U)) := by
    rw [← (Sieve.overEquiv (Over.mk (𝟙 U) : Over U)).symm_apply_apply R]
    exact hET i
  obtain ⟨s⟩ := hRloc hqi
  exact (nonempty_unitHom_pullback_iff (yoneda.map (E.f i)) X).2
    ⟨_, Over.w ((sliceSectionEquiv X (Over.mk (E.f i))).symm
      (eX.hom.app (op (Over.mk (E.f i))) s))⟩

variable (𝒞 S hS) in
/-- **The relative form of Stacks 04TZ, from the site to algebraic spaces.** A torsor on the
localized site `(Sch/U)_fppf` whose sheaf of groups and whose underlying sheaf are the
presheaves of sections of a group object and of an object it acts on, compatibly with the
actions, comes from an fppf torsor of algebraic spaces over the representable presheaf of `U`:
the action is a pseudo-torsor by
`AlgebraicGeometry.Space.isPseudoTorsor_of_relativeSiteTorsorData` and it is trivialized by an
fppf covering by `AlgebraicGeometry.Space.exists_isFppfCovering_trivializing_of_isTorsor`. -/
theorem isFppfTorsor_of_isRelativeSiteTorsor (hU : IsAlgebraicSpace 𝒞 S hS (yoneda.obj U))
    (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (h : IsRelativeSiteTorsor 𝒞 S hS U G X) :
    IsFppfTorsor 𝒞 S hS (yoneda.obj U) hU G X hG hX := by
  obtain ⟨H, F, eG, eX, hFT, hact⟩ := h
  exact ⟨isPseudoTorsor_of_relativeSiteTorsorData 𝒞 S hS G X H F eG eX hact,
    exists_isFppfCovering_trivializing_of_isTorsor 𝒞 S hS X F eX hFT⟩

variable (𝒞 S hS) in
/-- **Stacks 04TZ over an arbitrary object of the big fppf site.** An action of a group object
over the representable presheaf of an object `U` of the big fppf site of `S` on an object over
that presheaf is an fppf torsor exactly when it is a torsor on the localized site
`(Sch/U)_fppf`. For `U` a terminal object of the site this is the comparison
`AlgebraicGeometry.Space.isFppfTorsor_iff_siteTorsor` over the big site itself.

Untagged: the `@[stacks 04TZ]` attribute sits on that comparison, which is the source's
statement over `S` and the site `(Sch/S)_fppf` it names, as with the other relative forms of
04TZ in this file. -/
theorem isFppfTorsor_iff_isRelativeSiteTorsor (hU : IsAlgebraicSpace 𝒞 S hS (yoneda.obj U))
    (G X : Over (yoneda.obj U)) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    IsFppfTorsor 𝒞 S hS (yoneda.obj U) hU G X hG hX ↔ IsRelativeSiteTorsor 𝒞 S hS U G X :=
  ⟨isRelativeSiteTorsor_of_isFppfTorsor 𝒞 S hS hU G X hG hX,
    isFppfTorsor_of_isRelativeSiteTorsor 𝒞 S hS hU G X hG hX⟩

/-! ### A torsor for a group object over a base sheaf -/

variable (𝒞 S hS) in
/-- **A torsor over a section of a base sheaf is a torsor on the localized site.** An object of
the category `𝒢/ℬ-Torsors` of Stacks 04UL over the section `b` of `ℬ` is a torsor on the
localized site `(Sch/U)_fppf` under the sections of the acting group `U ×_{b, ℬ} 𝒢`.

The two conditions `AlgebraicGeometry.Space.IsSheafTorsor` carries beyond the pseudo-torsor
condition are exactly what the passage asks for: the acted-on object is a sheaf, and its
structure morphism is locally surjective, which is local nonemptiness by
`AlgebraicGeometry.Space.isTorsor_slicePseudoTorsor_of_isLocallySurjective`. The one condition
`AlgebraicGeometry.Space.SheafTorsors` deliberately omits, that the acting group be a sheaf, is
supplied here from the sheaf conditions on `ℬ` and on `𝒢`, because that group is the fibre
product `U ×_{b, ℬ} 𝒢` and a fibre product of sheaves over a sheaf is a sheaf
(`CategoryTheory.Presheaf.isSheaf_pullback`). -/
theorem isRelativeSiteTorsor_of_isSheafTorsor {ℬ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (G : Grp (Over ℬ)) (b : yoneda.obj U ⟶ ℬ) (F : Over (yoneda.obj U))
    (act : ModObj (sheafPullbackGroup G U b).X F)
    (hℬ : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) ℬ)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.X.left)
    (hT : IsSheafTorsor G U b F act) :
    @IsRelativeSiteTorsor 𝒞 S hS U (sheafPullbackGroup G U b).X F _ act := by
  have hGb : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS)
      (sheafPullbackGroup G U b).X.left :=
    Presheaf.isSheaf_pullback _ G.X.hom b hG (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf hℬ
  exact ⟨sliceSheafOfGroups _ hGb, slicePseudoTorsor _ F hGb hT.1 hT.2.1, Iso.refl _,
    Iso.refl _,
    isTorsor_slicePseudoTorsor_of_isLocallySurjective 𝒞 S hS _ F hGb hT.1 hT.2.1 hT.2.2,
    fun _ _ _ => rfl⟩

/-! ### The action manufactured from a torsor on the localized site -/

variable (𝒞 S hS) in
/-- A torsor on the localized site manufactures an action of group objects over the
representable presheaf of `U` whose shear map is an isomorphism, that is a pseudo-torsor
action. The action morphism itself is `PseudoTorsor.overYonedaModObj`. -/
@[sga "3 III 0.1" "(i) ⇒ (ii)"]
theorem isPseudoTorsor_overYonedaObj
    {H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U)}
    (F : PseudoTorsor.{u} H) :
    IsPseudoTorsor (F.overYonedaGrp (J := BigFppfOver.topology 𝒞 S hS))
      (F.overYonedaObj (J := BigFppfOver.topology 𝒞 S hS)) :=
  F.isIso_leftSMul_overYoneda (J := BigFppfOver.topology 𝒞 S hS)

variable (𝒞 S hS) in
/-- The acted-on object manufactured from a torsor on the localized site has a locally
surjective structure morphism to the representable presheaf of `U`, which is the local
existence of sections asked for by Stacks 04UL. -/
theorem isLocallySurjective_overYonedaObj
    {H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U)}
    (F : PseudoTorsor.{u} H) (hF : F.IsTorsor) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS)
      (F.overYonedaObj (J := BigFppfOver.topology 𝒞 S hS)).hom :=
  F.isLocallySurjective_overYonedaObj_hom (J := BigFppfOver.topology 𝒞 S hS) hF

variable (𝒞 S hS) in
/-- The acted-on object manufactured from a torsor on the localized site is a sheaf: the
representable presheaf of `U` is one, by subcanonicality of the fppf topology. -/
theorem isSheaf_overYonedaObj
    {H : SheafOfGroups.{u} (C := Over U) ((BigFppfOver.topology 𝒞 S hS).over U)}
    (F : PseudoTorsor.{u} H) :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS)
      (F.overYonedaObj (J := BigFppfOver.topology 𝒞 S hS)).left :=
  F.isSheaf_overYonedaObj (J := BigFppfOver.topology 𝒞 S hS)
    (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf

end AlgebraicGeometry.Space

end
