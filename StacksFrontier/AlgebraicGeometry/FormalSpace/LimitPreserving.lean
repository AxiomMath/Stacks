module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.JointlySurjectiveFamily
import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective

/-!
# Formal algebraic spaces with finitely presented stages are limit preserving

Let `S` be a scheme contained in a big fppf site `B`. This file proves that a formal algebraic
space `X` over `S` is limit preserving in the sense of Stacks 049J as soon as it has an atlas as in
Definition 0AIM whose members `Uₖ` have "finitely presented stages": any two morphisms from an
affine object of the site into `Uₖ` factor through one object `Z` of the site, locally of finite
presentation over `S`, by way of a section of `Uₖ` over `Z` which is a monomorphism on affine
objects. For an affine formal algebraic space `colim Spec(A/J)` these are the thickening stages
`Spec(A/J)` (Stacks 0AIA), which are of finite presentation over `S` in the Noetherian situation
of Stacks 0GHC.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.structureMorphisms`: the structure morphisms to `S` of the
  stages of a diagram in the big fppf site of `S`.
* `AlgebraicGeometry.FormalSpace.HasFinitelyPresentedStages`: any two morphisms from an affine
  object factor through one stage locally of finite presentation over `S` which is a
  monomorphism on affine objects.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_comp_eq_of_isLimit`,
  `AlgebraicGeometry.BigFppfOver.exists_map_comp_eq_of_isLimit` and
  `AlgebraicGeometry.BigFppfOver.exists_comp_eq_map_of_isLimit`: for a cofiltered limit of affine
  objects of the big fppf site of `S`, a morphism from the limit to an object locally of finite
  presentation over `S` factors through a stage, two morphisms from a stage to an object locally
  of finite type over `S` agreeing on the limit agree at a later stage, and the same existence
  holds relative to a stage.
* `AlgebraicGeometry.FormalSpace.limitPreserving_of_hasFinitelyPresentedStages`: a sheaf with
  finitely presented stages is limit preserving.
* `AlgebraicGeometry.FormalSpace.exists_lift_of_isEtale_of_isAffineFormalAlgebraicSpace`: lifts
  along an étale chart out of an affine formal algebraic space descend through limits of affines.
* `AlgebraicGeometry.FormalSpace.limitPreserving_of_atlas` and
  `AlgebraicGeometry.FormalSpace.limitPreserving_of_hasAffineEtaleAtlasWithProperty`: a sheaf
  with an atlas as in Definition 0AIM by affine formal algebraic spaces with finitely presented
  stages is limit preserving.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 049O](https://stacks.math.columbia.edu/tag/049O)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BigFppfOver

variable {B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ BigFppfOver B S hS}
  {c : Cone D}

/-- The structure morphisms to `S` of the stages of a diagram in the big fppf site of `S`, as a
cone over the constant diagram on `S`. -/
def structureMorphisms (D : I ⥤ BigFppfOver B S hS) :
    D ⋙ BigFppfOver.toScheme B S hS ⟶ (Functor.const I).obj S where
  app i := B.inclusion.map (D.obj i).hom
  naturality i j g := by
    simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map, Functor.const_obj_map,
      Category.comp_id]
    rw [← Over.w (D.map g)]
    rfl

/-- A morphism of schemes between objects of the big fppf site lying over `S` comes from a morphism
of the site. -/
private theorem exists_map_eq_of_comp_eq {X Y : BigFppfOver B S hS}
    (u : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hu : u ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) :
    ∃ a : X ⟶ Y, (BigFppfOver.toScheme B S hS).map a = u :=
  ⟨Over.homMk (ObjectProperty.homMk u)
    (B.inclusion.map_injective (by rw [Functor.map_comp]; exact hu)), rfl⟩

/-- Let `V = lim Vᵢ` be a cofiltered limit of affine objects of the big fppf site of `S` and let
`Z` be an object locally of finite presentation over `S`. Every morphism `V ⟶ Z` factors through
some stage `Vᵢ`. -/
theorem exists_comp_eq_of_isLimit (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    {Z : BigFppfOver B S hS} (hZ : LocallyOfFinitePresentation (B.inclusion.map Z.hom))
    (a : c.pt ⟶ Z) : ∃ (i : I) (aᵢ : D.obj i ⟶ Z), c.π.app i ≫ aᵢ = a := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ i, IsAffine ((D ⋙ T).obj i) := hD
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom ((D ⋙ T).map g) := fun _ ↦ inferInstance
  have : ∀ i, CompactSpace ((D ⋙ T).obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ T).obj i) := fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation (B.inclusion.map Z.hom) := hZ
  obtain ⟨i, g, hg, hgf⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D ⋙ T)
    (structureMorphisms D) (B.inclusion.map Z.hom) (T.mapCone c) hc (T.map a) (by
      ext i
      change B.inclusion.map (c.π.app i).left ≫ B.inclusion.map (D.obj i).hom =
        B.inclusion.map a.left ≫ B.inclusion.map Z.hom
      rw [← Functor.map_comp, ← Functor.map_comp, Over.w, Over.w]
      rfl)
  obtain ⟨aᵢ, rfl⟩ := exists_map_eq_of_comp_eq g hgf
  exact ⟨i, aᵢ, T.map_injective hg⟩

/-- Let `V = lim Vᵢ` be a cofiltered limit of affine objects of the big fppf site of `S` and let
`Z` be an object locally of finite type over `S`. Two morphisms `Vᵢ ⟶ Z` with the same
restriction to `V` agree at a later stage. -/
theorem exists_map_comp_eq_of_isLimit (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    {Z : BigFppfOver B S hS} (hZ : LocallyOfFiniteType (B.inclusion.map Z.hom)) {i : I}
    (a b : D.obj i ⟶ Z) (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (j : I) (g : j ⟶ i), D.map g ≫ a = D.map g ≫ b := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ i, IsAffine ((D ⋙ T).obj i) := hD
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom ((D ⋙ T).map g) := fun _ ↦ inferInstance
  have : ∀ i, CompactSpace ((D ⋙ T).obj i) := fun _ ↦ inferInstance
  have : LocallyOfFiniteType (B.inclusion.map Z.hom) := hZ
  obtain ⟨j, g, hg⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (D ⋙ T)
    (structureMorphisms D) (B.inclusion.map Z.hom) (T.mapCone c) hc (T.map a) (T.map b)
    (by change B.inclusion.map (D.obj i).hom = B.inclusion.map a.left ≫ B.inclusion.map Z.hom
        rw [← Functor.map_comp, Over.w])
    (by change B.inclusion.map (D.obj i).hom = B.inclusion.map b.left ≫ B.inclusion.map Z.hom
        rw [← Functor.map_comp, Over.w])
    (by simpa only [Functor.mapCone_π_app, ← T.map_comp] using congrArg T.map hab)
  exact ⟨j, g, T.map_injective (by rw [T.map_comp, T.map_comp]; exact hg)⟩

/-- Let `V = lim Vᵢ` be a cofiltered limit of affine objects of the big fppf site of `S` and let
`p : E ⟶ Vᵢ` be a morphism of the site locally of finite presentation. Every section `V ⟶ E` of
`p` over `V` is the restriction of a morphism `Vⱼ ⟶ E` lying over the transition morphism
`Vⱼ ⟶ Vᵢ`, for some later stage `Vⱼ`. -/
theorem exists_comp_eq_map_of_isLimit (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    {i : I} {E : BigFppfOver B S hS} (p : E ⟶ D.obj i)
    (hp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p))
    (σ : c.pt ⟶ E) (hσ : σ ≫ p = c.π.app i) :
    ∃ (j : I) (g : j ⟶ i) (σⱼ : D.obj j ⟶ E), c.π.app j ≫ σⱼ = σ ∧ σⱼ ≫ p = D.map g := by
  let T := BigFppfOver.toScheme B S hS
  let q : Over i ⥤ I := Over.forget i
  let D' := q ⋙ D ⋙ T
  let c' := (T.mapCone c).whisker q
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv q (T.mapCone c)).symm hc
  have : ∀ j, IsAffine (D'.obj j) := fun j ↦ hD j.left
  have : ∀ {j k : Over i} (g : j ⟶ k), IsAffineHom (D'.map g) := fun _ ↦ inferInstance
  have : ∀ j, CompactSpace (D'.obj j) := fun _ ↦ inferInstance
  have : ∀ j, QuasiSeparatedSpace (D'.obj j) := fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation (T.map p) := hp
  let t : D' ⟶ (Functor.const (Over i)).obj (T.obj (D.obj i)) :=
    { app j := T.map (D.map j.hom)
      naturality j k g := by
        simp only [D', q, Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj,
          Functor.comp_map, Over.forget_map, Functor.const_obj_map, Category.comp_id,
          ← T.map_comp, ← D.map_comp, Over.w] }
  obtain ⟨j, u, hu, hup⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t
    (T.map p) c' hc' (T.map σ) (by
      ext j
      change T.map (c.π.app j.left) ≫ T.map (D.map j.hom) = T.map σ ≫ T.map p
      rw [← T.map_comp, ← T.map_comp, c.w, hσ])
  have hu' : u ≫ B.inclusion.map E.hom = B.inclusion.map (D.obj j.left).hom := by
    rw [← Over.w p, B.inclusion.map_comp, ← Category.assoc]
    change (u ≫ T.map p) ≫ _ = _
    rw [hup]
    change B.inclusion.map (D.map j.hom).left ≫ B.inclusion.map (D.obj i).hom = _
    rw [← B.inclusion.map_comp, Over.w]
  obtain ⟨σⱼ, rfl⟩ := exists_map_eq_of_comp_eq u hu'
  exact ⟨j.left, j.hom, σⱼ, T.map_injective hu, T.map_injective hup⟩

end BigFppfOver

namespace FormalSpace

/-- An fppf sheaf `X` on the big fppf site of `S` *has finitely presented stages* when any two
sections of `X` over an affine object `T` are pulled back, along two morphisms `T ⟶ Z`, from one
section `y` of `X` over an object `Z` locally of finite presentation over `S`, where `y` is a
monomorphism on affine objects: two morphisms from an affine object to `Z` pulling `y` back to
the same section are equal. -/
abbrev HasFinitelyPresentedStages (X : FppfSheaf B S hS) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ t₁ t₂ : X.obj.obj (op T), ∃ (Z : BigFppfOver B S hS) (y : X.obj.obj (op Z)),
      LocallyOfFinitePresentation (B.inclusion.map Z.hom) ∧
      (∀ ⦃T' : BigFppfOver B S hS⦄ (a b : T' ⟶ Z),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
          X.obj.map a.op y = X.obj.map b.op y → a = b) ∧
      ∃ z₁ z₂ : T ⟶ Z, X.obj.map z₁.op y = t₁ ∧ X.obj.map z₂.op y = t₂

/-- A sheaf with finitely presented stages is limit preserving in the sense of Stacks 049J. -/
theorem limitPreserving_of_hasFinitelyPresentedStages {X : FppfSheaf B S hS}
    (hX : HasFinitelyPresentedStages B S hS X) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X.obj := by
  intro I _ _ D c hc hD hC
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq _ D c ?_ ?_
  · intro x
    obtain ⟨Z, y, hZ, -, z₁, -, hz₁, -⟩ := hX c.pt hC x x
    obtain ⟨i, a, ha⟩ := BigFppfOver.exists_comp_eq_of_isLimit hc hD hZ z₁
    refine ⟨i, X.obj.map a.op y, ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, ha, hz₁]
  · intro i x₁ x₂ hx
    obtain ⟨Z, y, hZ, hinj, z₁, z₂, rfl, rfl⟩ := hX (D.obj i) (hD i) x₁ x₂
    have hZ' : LocallyOfFiniteType (B.inclusion.map Z.hom) := by
      have := hZ
      infer_instance
    obtain ⟨j, g, hg⟩ := BigFppfOver.exists_map_comp_eq_of_isLimit hc hD hZ' z₁ z₂
      (hinj _ _ hC (by simpa only [← Functor.map_comp_apply, ← op_comp] using hx))
    refine ⟨j, g, ?_⟩
    simp only [← Functor.map_comp_apply, ← op_comp, hg]

/-- Let `u : U ⟶ X` be a morphism of fppf sheaves out of an affine formal algebraic
space which is representable by algebraic spaces and étale, let `V = lim Vₖ` be a cofiltered
limit of affine objects of the site, and let `s` be a section of `X` over a stage `Vₖ`. Every
lift through `u` of the restriction of `s` to `V` is the restriction of a lift through `u` of the
restriction of `s` to some later stage. -/
theorem exists_lift_of_isEtale_of_isAffineFormalAlgebraicSpace {X U : FppfSheaf B S hS}
    (u : U ⟶ X) (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS u.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) u.hom hrep)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj k))) (k : I)
    (x : U.obj.obj (op c.pt)) (s : X.obj.obj (op (D.obj k)))
    (hx : u.hom.app _ x = X.obj.map (c.π.app k).op s) :
    ∃ (l : I) (g : l ⟶ k) (y : U.obj.obj (op (D.obj l))),
      U.obj.map (c.π.app l).op y = x ∧ u.hom.app _ y = X.obj.map (D.map g).op s := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : (fppfYoneda B S hS).Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : (fppfYoneda B S hS).Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let Y := fppfYoneda B S hS
  let cX : Y.obj (D.obj k) ⟶ X := (Sheaf.sectionEquiv J).symm s
  obtain ⟨E, p, q, sq, hpe, -⟩ := exists_isPullback_etale_isSeparated_of_chart B S hS u hU hrep
    het cX
  let ξ : Y.obj c.pt ⟶ U := (Sheaf.sectionEquiv J).symm x
  have hcomm : ξ ≫ u = Y.map (c.π.app k) ≫ cX := by
    apply (Sheaf.sectionEquiv J).injective
    rw [Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact hx
  let σ : c.pt ⟶ E := Y.preimage (sq.lift ξ (Y.map (c.π.app k)) hcomm)
  have hσp : σ ≫ p = c.π.app k := Y.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  have hσq : Y.map σ ≫ q = ξ := by
    rw [Functor.map_preimage, IsPullback.lift_fst]
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) := by
    have := hpe
    infer_instance
  obtain ⟨l, g, σl, hσl, hσlp⟩ := BigFppfOver.exists_comp_eq_map_of_isLimit hc hD p this σ hσp
  refine ⟨l, g, Sheaf.sectionEquiv J (Y.map σl ≫ q), ?_, ?_⟩
  · rw [← Sheaf.sectionEquiv_map_comp, ← Category.assoc, ← Functor.map_comp, hσl, hσq,
      Equiv.apply_symm_apply]
  · rw [← Sheaf.sectionEquiv_comp, Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp,
      hσlp, Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]

/-- Let `X` be an fppf sheaf on the big fppf site of `S` with a family of morphisms
`uₖ : Uₖ ⟶ X` as in Definition 0AIM: each `Uₖ` an affine formal algebraic space, each `uₖ`
representable by algebraic spaces and étale, and `∐ Uₖ ⟶ X` a surjection of sheaves. If every
`Uₖ` has finitely presented stages, then `X` is limit preserving in the sense of Stacks 049J. -/
theorem limitPreserving_of_atlas {X : FppfSheaf B S hS} {K : Type (u + 1)}
    (U : K → FppfSheaf B S hS) (f : ∀ k, U k ⟶ X)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (U k))
    (het : ∀ k, ∃ hfk : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f k).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f k).hom hfk)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    (hst : ∀ k, HasFinitelyPresentedStages B S hS (U k)) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X.obj := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine limitPreserving_of_jointlyLocallySurjective.{u, u + 1, u, u} B S hS X.property
    (fun k ↦ (f k).hom) (fun V s ↦ Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc f hsurj s)
    (fun k ↦ limitPreserving_of_hasFinitelyPresentedStages B S hS (hst k)) ?_
  intro i j _ _ _ D c hc hD _ k x x' hx
  obtain ⟨hrep, hetale⟩ := het i
  exact exists_lift_of_isEtale_of_isAffineFormalAlgebraicSpace B S hS (f i) (haff i) hrep hetale
    hc hD k x _ hx

/-- A formal algebraic space with an affine étale atlas, as in condition (2) of Stacks 0AKX, by
affine formal algebraic spaces with finitely presented stages is limit preserving. -/
theorem limitPreserving_of_hasAffineEtaleAtlasWithProperty {X : FppfSheaf B S hS}
    (hX : HasAffineEtaleAtlasWithProperty B S hS X (HasFinitelyPresentedStages B S hS)) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X.obj := by
  obtain ⟨K, U, f, haff, het, hsurj, hst⟩ := hX
  exact limitPreserving_of_atlas B S hS U f haff het hsurj hst

end FormalSpace

end AlgebraicGeometry

end
