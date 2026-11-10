module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GaloisBaseChangeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# A decent algebraic space of finite type over a field with enough affines over the closure

Let `k` be a field with algebraic closure `k̄` and let `X` be an algebraic space over `k`.
Suppose `X` is decent and locally of finite type over `k`, the base change `X_{k̄}` is a
scheme, and every finite set of `k̄`-rational points of `X_{k̄}` is contained in an affine
open.  Then `X` is a scheme.

Being a scheme is `CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the
space, and the base change `X_{k̄}` is the restriction of `X` to the big fppf site over
`Spec k̄`, namely `CategoryTheory.OverShriek.relocalizeRestrict` along the morphism
`Spec k̄ ⟶ Spec k` of the site.  A `k̄`-rational point of `X_{k̄}` is a section of that
restriction over the terminal object `Spec k̄` of its own site, and an affine open is
presented by an open immersion into `X_{k̄}` out of an affine object of the site.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isAlgClosure_finite_rationalPoints_isAffine`:
  **Stacks 0B88.**

## Implementation notes

The argument is organised around the schematic locus
`AlgebraicGeometry.Space.schematicLocus` of Stacks 03JH.  Since `X` is decent and locally of
finite type over a field, its point space is a Jacobson space (Stacks 0BA6 together with
Stacks 0BA3), so the schematic locus is everything as soon as it contains every closed point;
that reduction is `isRepresentable_of_closedPoints_schematic` below, using Stacks 03KE in the
case `(θ)` through `isRepresentable_of_open_representable_neighborhoods`.

For a closed point `x` of `|X|`, Stacks 0AHB produces a closed immersion `Spec l ⟶ X`
representing `x`, and `Spec l ⟶ Spec k` is then finite (Stacks 03XG, the Hilbert
Nullstellensatz through `AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`).
Base changing to `k̄` turns `Spec l` into a finite scheme over an algebraically closed field,
hence a finite disjoint union of `k̄`-rational points, and hypothesis (3) produces an affine
open `W ⊆ X_{k̄}` through which that finite scheme factors — this is
`exists_affine_factor_of_finite_over_algebraicallyClosed`.

Rather than descend `W` to a finite subextension and quotient by a Galois group, the proof
exploits that `Spec k̄ ⟶ Spec k` is an affine, flat, surjective — hence fpqc — covering, and
that the projection `π : X_{k̄} ⟶ X`, being a base change of it, is universally closed and
quasi-compact.  Closedness of `π` converts the fibrewise statement into a quasi-compact open
neighbourhood `N` of `x` in `X` whose base change to `k̄` lands inside `W`, which makes
`N_{k̄} ⟶ Spec k̄` quasi-affine; Stacks 0423 (quasi-affineness is fpqc local on the target,
`AlgebraicGeometry.Space.isLocalAtTarget_isQuasiAffineHom_fpqc`) descends that to `N`, and a
quasi-affine algebraic space over an affine base is a scheme by Stacks 03WM.  Hence `N` lies
in the schematic locus and so does `x`.

## References

* [Stacks Project, Tag 0B88](https://stacks.math.columbia.edu/tag/0B88)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Generic facts about relocalization along a morphism of a category -/

section Relocalize

universe v

variable {C : Type u} [Category.{v} C] {S S' : C}

/-- The lower-shriek extension along `g : S ⟶ S'` of a presheaf represented by `U` over `S`
is represented by the image of `U` under `Over.map g`. -/
private def relocalizeYonedaRepresentableBy (g : S ⟶ S') (U : Over S) :
    ((OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj U)).RepresentableBy
      ((Over.map g).obj U) where
  homEquiv {T} := {
    toFun := fun f => ⟨⟨f.left ≫ U.hom, Over.homMk f.left rfl⟩, by
      change (f.left ≫ U.hom) ≫ g = T.hom
      simpa only [Over.map_obj_hom, Category.assoc] using f.w⟩
    invFun := fun s => Over.homMk s.1.2.left (by
      change s.1.2.left ≫ (U.hom ≫ g) = T.hom
      rw [← Category.assoc, s.1.2.w]
      exact s.2)
    left_inv := fun f => by ext; rfl
    right_inv := fun ⟨⟨a, b⟩, ha⟩ => by
      apply Subtype.ext
      let e : Over.mk (b.left ≫ U.hom) ⟶ Over.mk a :=
        Over.homMk (𝟙 T.left) (by
          change 𝟙 T.left ≫ a = b.left ≫ U.hom
          simpa only [Category.id_comp, Over.mk_hom] using b.w.symm)
      have he : e ≫ b = (Over.homMk b.left rfl : Over.mk (b.left ≫ U.hom) ⟶ U) := by
        ext; simp [e]
      have hh := OverShriek.sigmaMk_eq_self (yoneda.obj U) b e rfl
      change (⟨b.left ≫ U.hom, e ≫ b⟩ : Σ χ, (yoneda.obj U).obj (op (Over.mk χ))) = _ at hh
      rwa [he] at hh
  }
  homEquiv_comp {T T'} f h := by
    apply Subtype.ext
    let e : Over.mk ((f.left ≫ h.left) ≫ U.hom) ⟶ U :=
      Over.homMk (f.left ≫ h.left) rfl
    let e' : Over.mk (f.left ≫ (h.left ≫ U.hom)) ⟶ U :=
      (Over.homMk f.left rfl : Over.mk (f.left ≫ (h.left ≫ U.hom)) ⟶
        Over.mk (h.left ≫ U.hom)) ≫
      (Over.homMk h.left rfl : Over.mk (h.left ≫ U.hom) ⟶ U)
    have hh := OverShriek.sigmaMk_eq (yoneda.obj U) (𝟙 U) e e' rfl
    change (⟨(f.left ≫ h.left) ≫ U.hom, e ≫ 𝟙 U⟩ :
      Σ χ : T.left ⟶ S, (yoneda.obj U).obj (op (Over.mk χ))) =
      ⟨f.left ≫ (h.left ≫ U.hom), e' ≫ 𝟙 U⟩ at hh
    change (⟨(f.left ≫ h.left) ≫ U.hom, e⟩ :
      Σ χ : T.left ⟶ S, (yoneda.obj U).obj (op (Over.mk χ))) =
      ⟨f.left ≫ (h.left ≫ U.hom), e'⟩
    simpa only [Category.comp_id] using hh

/-- The projection of the lower-shriek extension of a restriction onto the presheaf
represented by `g` itself. -/
private def relocalizeProjection (g : S ⟶ S') (F : (Over S')ᵒᵖ ⥤ Type v) :
    (OverShriek.relocalizePresheafFunctor g).obj
      ((OverShriek.relocalizeRestrict g).obj F) ⟶ yoneda.obj (Over.mk g) where
  app T := ↾fun s => Over.homMk s.1.1 s.2
  naturality T T' f := by ext s; rfl

/-- Two sections of a binary product of presheaves agree when both projections do. -/
private theorem product_obj_ext {D : Type*} [Category.{v} D]
    {F G : Dᵒᵖ ⥤ Type v} {T : Dᵒᵖ} {s t : (F ⨯ G).obj T}
    (h₁ : (prod.fst : F ⨯ G ⟶ F).app T s = (prod.fst : F ⨯ G ⟶ F).app T t)
    (h₂ : (prod.snd : F ⨯ G ⟶ G).app T s = (prod.snd : F ⨯ G ⟶ G).app T t) : s = t := by
  refine yonedaEquiv.symm.injective (prod.hom_ext ?_ ?_) <;> apply yonedaEquiv.injective
  · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h₁
  · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h₂

/-- The lower-shriek extension of the restriction of `F` along `g` is the product of `F` with
the presheaf represented by `g`. -/
private def relocalizeRestrictProductIso
    (g : S ⟶ S') (F : (Over S')ᵒᵖ ⥤ Type v) :
    (OverShriek.relocalizePresheafFunctor g).obj
        ((OverShriek.relocalizeRestrict g).obj F) ≅ yoneda.obj (Over.mk g) ⨯ F := by
  let L := (OverShriek.relocalizePresheafFunctor g).obj
    ((OverShriek.relocalizeRestrict g).obj F)
  let a : L ⟶ yoneda.obj (Over.mk g) := relocalizeProjection g F
  let b : L ⟶ F := OverShriek.relocalizeOfRestricted g (𝟙 _)
  let c := prod.lift a b
  have hc₁ (T) (s : L.obj T) :
      (prod.fst : yoneda.obj (Over.mk g) ⨯ F ⟶ yoneda.obj (Over.mk g)).app T (c.app T s) =
        a.app T s :=
    congrArg (fun f : L ⟶ yoneda.obj (Over.mk g) => f.app T s) (prod.lift_fst a b)
  have hc₂ (T) (s : L.obj T) :
      (prod.snd : yoneda.obj (Over.mk g) ⨯ F ⟶ F).app T (c.app T s) = b.app T s :=
    congrArg (fun f : L ⟶ F => f.app T s) (prod.lift_snd a b)
  have hc (T) : Function.Bijective (c.app T) := by
    constructor
    · rintro ⟨⟨σ, x⟩, hσ⟩ ⟨⟨τ, y⟩, hτ⟩ h
      have h₁ := congrArg (fun z =>
        (prod.fst : yoneda.obj (Over.mk g) ⨯ F ⟶ yoneda.obj (Over.mk g)).app T z) h
      have h₁ := (hc₁ T ⟨⟨σ, x⟩, hσ⟩).symm.trans (h₁.trans (hc₁ T ⟨⟨τ, y⟩, hτ⟩))
      have he : σ = τ := congrArg Over.Hom.left h₁
      subst τ
      have h₂ := congrArg (fun z =>
        (prod.snd : yoneda.obj (Over.mk g) ⨯ F ⟶ F).app T z) h
      have h₂ := (hc₂ T ⟨⟨σ, x⟩, hσ⟩).symm.trans (h₂.trans (hc₂ T ⟨⟨σ, y⟩, hτ⟩))
      change σ ≫ g = T.unop.hom at hσ
      let e : T.unop ⟶ Over.mk (σ ≫ g) := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (σ ≫ g) = T.unop.hom
        simpa using hσ)
      have : IsIso e := by
        have : IsIso e.left := by change IsIso (𝟙 _); infer_instance
        let : IsIso ((Over.forget S').map e) := inferInstanceAs (IsIso e.left)
        exact isIso_of_reflects_iso e (Over.forget S')
      change F.map e.op x = F.map e.op y at h₂
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq
        ((ConcreteCategory.bijective_of_isIso (F.map e.op)).1 h₂)))
    · intro z
      let q : T.unop ⟶ Over.mk g :=
        (prod.fst : yoneda.obj (Over.mk g) ⨯ F ⟶ yoneda.obj (Over.mk g)).app T z
      let e : Over.mk (q.left ≫ g) ⟶ T.unop := Over.homMk (𝟙 _) (by simpa using q.w.symm)
      let s : L.obj T := ⟨⟨q.left,
        F.map e.op ((prod.snd : yoneda.obj (Over.mk g) ⨯ F ⟶ F).app T z)⟩, q.w⟩
      refine ⟨s, product_obj_ext ?_ ?_⟩
      · rw [hc₁]
        apply Over.OverMorphism.ext
        rfl
      · rw [hc₂]
        change F.map _ (F.map e.op
          ((prod.snd : yoneda.obj (Over.mk g) ⨯ F ⟶ F).app T z)) = _
        rw [← F.map_comp_apply, ← op_comp]
        have hid : (Over.homMk (𝟙 T.unop.left) (by simpa using q.w) :
            T.unop ⟶ Over.mk (q.left ≫ g)) ≫ e = 𝟙 T.unop := by ext; simp [e]
        rw [hid, op_id, F.map_id]
        rfl
  have : ∀ T, IsIso (c.app T) := fun T => (ConcreteCategory.isIso_iff_bijective _).mpr (hc T)
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact asIso c

private theorem representableBy_toIso_hom_app
    {D : Type u} [Category.{v} D] {F : Dᵒᵖ ⥤ Type v} {U T : D}
    (e : F.RepresentableBy U) (f : T ⟶ U) :
    e.toIso.hom.app (op T) f = e.homEquiv f := rfl

private theorem relocalizeYoneda_projection
    (g : S ⟶ S') (U : Over S) (F : (Over S')ᵒᵖ ⥤ Type v)
    (j : yoneda.obj U ⟶ (OverShriek.relocalizeRestrict g).obj F) :
    (relocalizeYonedaRepresentableBy g U).toIso.hom ≫
      (OverShriek.relocalizePresheafFunctor g).map j ≫ relocalizeProjection g F =
      yoneda.map (Over.homMk U.hom rfl : (Over.map g).obj U ⟶ Over.mk g) := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [yonedaEquiv_apply, representableBy_toIso_hom_app]
  change (relocalizeProjection g F).app (op ((Over.map g).obj U))
    (((OverShriek.relocalizePresheafFunctor g).map j).app (op ((Over.map g).obj U))
      ⟨⟨𝟙 U.left ≫ U.hom, Over.homMk (𝟙 U.left) rfl⟩, _⟩) = _
  exact Over.OverMorphism.ext (Category.id_comp _)

private theorem relocalizeYoneda_counit
    (g : S ⟶ S') (U : Over S) (F : (Over S')ᵒᵖ ⥤ Type v)
    (j : yoneda.obj U ⟶ (OverShriek.relocalizeRestrict g).obj F) :
    (relocalizeYonedaRepresentableBy g U).toIso.hom ≫
      (OverShriek.relocalizePresheafFunctor g).map j ≫
        OverShriek.relocalizeOfRestricted g
          (𝟙 ((OverShriek.relocalizeRestrict g).obj F)) =
      yonedaEquiv.symm (show F.obj (op ((Over.map g).obj U)) from j.app (op U) (𝟙 U)) := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [yonedaEquiv_apply, representableBy_toIso_hom_app]
  change (OverShriek.relocalizeOfRestricted g (𝟙 _)).app (op ((Over.map g).obj U))
    (((OverShriek.relocalizePresheafFunctor g).map j).app (op ((Over.map g).obj U))
      ⟨⟨𝟙 U.left ≫ U.hom, Over.homMk (𝟙 U.left) rfl⟩, _⟩) = _
  let e : U ⟶ Over.mk (𝟙 U.left ≫ U.hom) := Over.homMk (𝟙 U.left) (by simp)
  let e' : Over.mk (𝟙 U.left ≫ U.hom) ⟶ U := Over.homMk (𝟙 U.left) rfl
  change F.map ((Over.map g).map e).op (j.app _ e') = j.app _ (𝟙 U)
  have hn := (j.naturality_apply e.op e').symm
  change F.map ((Over.map g).map e).op (j.app _ e') = j.app _ (e ≫ e') at hn
  have he : e ≫ e' = 𝟙 U := by ext; simp [e, e']
  rwa [he] at hn

private theorem relocalizeYoneda_naturality
    (g : S ⟶ S') {U V : Over S} (f : U ⟶ V) :
    yoneda.map ((Over.map g).map f) ≫ (relocalizeYonedaRepresentableBy g V).toIso.hom =
      (relocalizeYonedaRepresentableBy g U).toIso.hom ≫
        (OverShriek.relocalizePresheafFunctor g).map (yoneda.map f) := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [yonedaEquiv_apply, representableBy_toIso_hom_app, representableBy_toIso_hom_app]
  change ⟨⟨f.left ≫ V.hom, Over.homMk f.left rfl⟩, _⟩ =
    ((OverShriek.relocalizePresheafFunctor g).map (yoneda.map f)).app
      (op ((Over.map g).obj U))
      ⟨⟨𝟙 U.left ≫ U.hom, Over.homMk (𝟙 U.left) rfl⟩, _⟩
  apply Subtype.ext
  have h := OverShriek.sigmaMk_eq (yoneda.obj V) (𝟙 V)
    (Over.homMk f.left rfl : Over.mk (f.left ≫ V.hom) ⟶ V)
    ((Over.homMk (𝟙 U.left) rfl : Over.mk (𝟙 U.left ≫ U.hom) ⟶ U) ≫ f)
    (by simp)
  change (⟨f.left ≫ V.hom, (Over.homMk f.left rfl : Over.mk (f.left ≫ V.hom) ⟶ V) ≫ 𝟙 V⟩ :
      Σ χ, (yoneda.obj V).obj (op (Over.mk χ))) =
    ⟨𝟙 U.left ≫ U.hom,
      ((Over.homMk (𝟙 U.left) rfl : Over.mk (𝟙 U.left ≫ U.hom) ⟶ U) ≫ f) ≫ 𝟙 V⟩ at h
  change (⟨f.left ≫ V.hom, (Over.homMk f.left rfl : Over.mk (f.left ≫ V.hom) ⟶ V)⟩ :
      Σ χ, (yoneda.obj V).obj (op (Over.mk χ))) =
    ⟨𝟙 U.left ≫ U.hom,
      (Over.homMk (𝟙 U.left) rfl : Over.mk (𝟙 U.left ≫ U.hom) ⟶ U) ≫ f⟩
  simpa only [Category.comp_id] using h

end Relocalize

/-! ### Properties of morphisms under relocalization and base change -/

attribute [local instance] pointTopology

private alias schemeProperty_inverseImage_stable :=
  AlgebraicGeometry.Space.inverseImage_stableUnderBaseChange

private theorem relativeProperty_relocalize
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : F ⟶ G)
    (hi : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf i) :
    (P.inverseImage (BigFppfOver.toScheme B S' hS')).presheaf
      ((OverShriek.relocalizePresheafFunctor g).map i) :=
  have _ : (P.inverseImage (BigFppfOver.toScheme B S' hS')).RespectsIso :=
    (schemeProperty_inverseImage_stable B S' hS' P).respectsIso
  OverShriek.presheaf_map_relocalize g (fun _ hk => hk) hi

private theorem relativeProperty_baseChange_projection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P (B.inclusion.map U.hom)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (prod.snd : yoneda.obj U ⨯ X ⟶ X) := by
  let T := BigFppfOver.toScheme B S hS
  let Q := P.inverseImage T
  have _ : Q.IsStableUnderBaseChange := schemeProperty_inverseImage_stable B S hS P
  let V : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let g : U ⟶ V := Over.homMk U.hom (by change U.hom ≫ 𝟙 _ = U.hom; simp)
  have hg : Q g := hP
  have hrep := MorphismProperty.relative_map (F := yoneda) (P := Q) hg
  have hV : IsTerminal (yoneda.obj V) :=
    IsTerminal.isTerminalObj yoneda V Over.mkIdTerminal
  have hpb : IsPullback (prod.fst : yoneda.obj U ⨯ X ⟶ yoneda.obj U)
      prod.snd (yoneda.map g) (hV.from X) := by
    convert IsPullback.of_is_product' (prodIsProd (yoneda.obj U) X) hV using 1
    exact hV.hom_ext _ _
  have _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hrep

/-! ### Elementary facts about the point maps -/

private theorem closedMap_of_relative_universallyClosed
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.UniversallyClosed.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsClosedMorphism B S hS f := by
  have hc := (presheaf_universallyClosed_iff B S hS hF hG hf.1).mp hf G hG (𝟙 G)
  have hH := isAlgebraicSpace_pullback B S hS (𝟙 G) f hG hF hG
  apply IsClosedMap.of_comp_surjective
    (pointsMap_surjective_of_isIso B S hS (pullback.snd (𝟙 G) f))
    (continuous_pointsMap B S hS (pullback.snd (𝟙 G) f))
  rw [← pointsMap_comp]
  simpa only [← pullback.condition, Category.comp_id] using hc

private theorem compactSpace_of_quasiCompact_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (hU : IsQuasiCompactSpace B S hS (yoneda.obj U)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨V, a, hV, ha, _⟩ := hU
  let f : V ⟶ U := yoneda.preimage a
  have hf : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map f) := by
    have hp : IsPullback (𝟙 (yoneda.obj V)) (yoneda.map f) a (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp [f]⟩
    exact ha.2 (𝟙 _) (𝟙 _) f hp
  let := hV
  exact ⟨by
    rw [← Set.image_univ_of_surjective (AlgebraicGeometry.Surjective.surj
      (f := (BigFppfOver.toScheme B S hS).map f))]
    exact isCompact_univ.image ((BigFppfOver.toScheme B S hS).map f).continuous⟩

private theorem fpqcCovering_of_affine_flat_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U V : BigFppfOver B S hS) (g : U ⟶ V)
    (hgAffine : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g))
    (hgFlat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map g))
    (hgSurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map g)) :
    IsFpqcCovering B S hS (fun _ : PUnit.{1} => yoneda.map g) := by
  let T := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsAffineHom.{u}) T) :=
    schemeProperty_inverseImage_stable B S hS _
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Flat.{u}) T) :=
    schemeProperty_inverseImage_stable B S hS _
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u}) T) :=
    schemeProperty_inverseImage_stable B S hS _
  have ha := MorphismProperty.relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsAffineHom.{u}) T) hgAffine
  have hf := MorphismProperty.relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.Flat.{u}) T) hgFlat
  have hs := MorphismProperty.relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u}) T) hgSurj
  refine ⟨fun _ => isFlat_yoneda_map B S hS g hgFlat, fun Z h => ?_⟩
  let W := ha.1.pullback h
  let q : W ⟶ A.obj Z := ha.1.snd h
  have hqa : AlgebraicGeometry.IsAffineHom (T.map q) := ha.property_snd h
  let : IsAffine (T.obj (A.obj Z)) := Z.property
  have hW : IsAffine (T.obj W) := isAffine_of_isAffineHom (T.map q)
  let W' : BigAffineFppf B S hS := ⟨W, hW⟩
  let q' : W' ⟶ Z := ObjectProperty.homMk q
  refine ⟨PreZeroHypercover.singleton q', inferInstance, ?_,
    fun _ => ⟨PUnit.unit, ha.1.fst h, (ha.1.isPullback h).w⟩⟩
  have : AlgebraicGeometry.Flat (T.map q) := hf.2 h (ha.1.fst h) q (ha.1.isPullback h)
  have : AlgebraicGeometry.Surjective (T.map q) :=
    hs.2 h (ha.1.fst h) q (ha.1.isPullback h)
  simpa [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton,
    BigAffineFppf.toScheme, A, T, q'] using (T.map q).singleton_mem_fpqcPrecoverage

/-! ### A quasi-compact open neighbourhood inside a prescribed open -/

/-- The points of an open subspace form an open subset of the points of the ambient space. -/
private theorem isOpen_range_pointsMap_of_isOpenSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  rw [← openSubspacesOrderIso_apply B S hS X hX ⟨V, hV⟩]
  exact (openSubspacesOrderIso B S hS X hX ⟨V, hV⟩).2

private theorem exists_quasiCompact_openSubspace_within
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (O : Set (points B S hS X))
    (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ V : Subfunctor X,
      IsOpenSubspace B S hS V ∧ IsQuasiCompactSpace B S hS V.toFunctor ∧
        ∃ v : points B S hS V.toFunctor,
          pointsMap B S hS V.toFunctor V.ι v = x ∧
            Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆ O := by
  obtain ⟨U, hU⟩ :=
    (hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp (hO.mem_nhds hxO)
  have hUopen : IsOpen U := hU.1.1
  have hUcompact : IsCompact U := hU.1.2.1
  have hxU : x ∈ U := hU.1.2.2
  let e := openSubspacesOrderIso B S hS X hX
  let W := e.symm ⟨U, hUopen⟩
  let V : Subfunctor X := W.1
  have hV : IsOpenSubspace B S hS V := W.2
  have hVrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = U := by
    have happly := openSubspacesOrderIso_apply B S hS X hX ⟨V, hV⟩
    have hinv : e ⟨V, hV⟩ = ⟨U, hUopen⟩ := by
      dsimp only [V, W]
      exact e.apply_symm_apply ⟨U, hUopen⟩
    exact happly.symm.trans
      (congrArg (fun O : TopologicalSpace.Opens (points B S hS X) => O.carrier) hinv)
  have hVcompact : CompactSpace (points B S hS V.toFunctor) := by
    have hImm : IsImmersion B S hS V.ι :=
      MorphismProperty.relative_monotone (fun _ _ f hf => by
        let : AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map f) := hf
        exact inferInstanceAs (AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map f)))
        V.ι hV.2
    have hEmb : Topology.IsEmbedding (pointsMap B S hS V.toFunctor V.ι) :=
      isEmbedding_pointsMap_of_isImmersion B S hS hX V.ι hImm
    have hImageCompact : IsCompact (pointsMap B S hS V.toFunctor V.ι '' Set.univ) := by
      rwa [Set.image_univ, hVrange]
    exact ⟨hEmb.isCompact_iff.mpr hImageCompact⟩
  have hVqc : IsQuasiCompactSpace B S hS V.toFunctor :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS V.toFunctor hV.1).2 hVcompact
  obtain ⟨v, hv⟩ : x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := hVrange ▸ hxU
  exact ⟨V, hV, hVqc, v, hv, hVrange ▸ hU.2⟩

/-! ### Representability from a quasi-affine fpqc base change -/

private theorem isRepresentable_of_quasiAffine_fpqc_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : U ⟶ V) (hcover : IsFpqcCovering B S hS (fun _ : PUnit.{1} => yoneda.map g))
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ yoneda.obj V) (a : H ⟶ F) (b : H ⟶ yoneda.obj U)
    (sq : IsPullback a b f (yoneda.map g))
    (hb : IsQuasiAffineHom B S hS b) : F.IsRepresentable := by
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let H' : AlgebraicSpaces B S hS := ⟨H, hH⟩
  let U' : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let f' : F' ⟶ V' := ObjectProperty.homMk f
  let g' : U' ⟶ V' := ObjectProperty.homMk (yoneda.map g)
  let a' : H' ⟶ F' := ObjectProperty.homMk a
  let b' : H' ⟶ U' := ObjectProperty.homMk b
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ t => IsQuasiAffineHom B S hS t.hom
  let hloc : P.IsLocalAtTarget (Topology.precoverage.{u, 0} .fpqc B S hS) :=
    isLocalAtTarget_isQuasiAffineHom_fpqc.{0, u} B S hS
  have _ : P.RespectsIso := hloc.toRespects
  have sq' : IsPullback a' b' f' g' :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (IsAlgebraicSpace B S hS)) sq
  have hmem : Presieve.ofArrows (fun _ : PUnit.{1} => U') (fun _ => g') ∈
      Topology.precoverage.{u, 0} .fpqc B S hS V' :=
    ⟨PUnit.{1}, (fun _ => U'), (fun _ => g'), rfl, V'.property,
      (fun _ => U'.property), hcover⟩
  have hf' : P f' := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := P) (K := Topology.precoverage.{u, 0} .fpqc B S hS) hmem
    rintro _ _ _ ⟨j⟩
    apply (P.cancel_left_of_respectsIso sq'.isoPullback.hom _).mp
    rw [sq'.isoPullback_hom_snd]
    exact hb
  obtain ⟨W, _, ⟨e⟩⟩ := hf' ⟨V, hV⟩ (𝟙 _)
  have _ : IsIso (pullback.snd (𝟙 (yoneda.obj V)) f) := inferInstance
  exact isRepresentable_of_natIso (yoneda.obj W)
    (e ≪≫ asIso (pullback.snd (𝟙 (yoneda.obj V)) f))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
private theorem quasiAffine_of_open_factor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F)
    (U V : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : yoneda.obj U ⟶ G) (hi : IsOpenImmersion B S hS i)
    (a : F ⟶ G) (ha : IsOpenImmersion B S hS a)
    (d : F ⟶ yoneda.obj U) (hd : d ≫ i = a)
    (b : F ⟶ yoneda.obj V) : IsQuasiAffineHom B S hS b := by
  let := mono_of_presheaf_isOpenImmersion hi
  have sq : IsPullback d (𝟙 F) i a := IsPullback.of_vert_isIso_mono ⟨by simpa using hd⟩
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hdopen : IsOpenImmersion B S hS d :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip ha
  let W := hdopen.1.pullback (𝟙 (yoneda.obj U))
  have _ : IsIso (hdopen.1.fst (𝟙 (yoneda.obj U))) :=
    (hdopen.1.isPullback (𝟙 (yoneda.obj U))).isIso_fst_of_isIso
  let e : yoneda.obj W ≅ F := asIso (hdopen.1.fst (𝟙 (yoneda.obj U)))
  have _ : F.IsRepresentable := isRepresentable_of_natIso _ e
  let r : W ⟶ U := hdopen.1.snd (𝟙 _)
  let T := BigFppfOver.toScheme B S hS
  have _ : AlgebraicGeometry.IsOpenImmersion (T.map r) := hdopen.property_snd (𝟙 _)
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj W) := by
    obtain ⟨A, q, hA, hs, he⟩ := hqc
    refine ⟨A, q ≫ e.inv, hA, (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u}) T)
      |>.cancel_right_of_respectsIso q e.inv).mpr hs, fun C t ht => ?_⟩
    simpa only [Category.assoc] using
      (MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u}) T)
        |>.cancel_right_of_respectsIso (t ≫ q) e.inv).mpr (he C t ht)
  let : CompactSpace (T.obj W) := compactSpace_of_quasiCompact_yoneda B S hS W hWqc
  let : IsAffine (T.obj U) := hU
  let : Scheme.IsQuasiAffine (T.obj W) := Scheme.IsQuasiAffine.of_isImmersion (T.map r)
  let t : W ⟶ V := yoneda.preimage (e.hom ≫ b)
  let : IsAffine (T.obj V) := hV
  have ht : AlgebraicGeometry.IsQuasiAffineHom (T.map t) := by
    refine ⟨fun O hO => ?_⟩
    have : CompactSpace ((T.map t) ⁻¹ᵁ O).toScheme :=
      isCompact_iff_compactSpace.mp ((T.map t).isCompact_preimage hO.isCompact)
    exact Scheme.IsQuasiAffine.of_isImmersion ((T.map t) ⁻¹ᵁ O).ι
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsQuasiAffineHom.{u}) T) :=
    schemeProperty_inverseImage_stable B S hS _
  have hr := MorphismProperty.relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsQuasiAffineHom.{u}) T) ht
  have hbrel : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsQuasiAffineHom.{u}) T).presheaf b := by
    apply (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsQuasiAffineHom.{u}) T)
      |>.cancel_left_of_respectsIso e.hom b).mp
    simpa only [t, yoneda.map_preimage] using hr
  exact ((isQuasiAffineHom_tfae_of_isAlgebraicSpace hF
    (isAlgebraicSpace_yoneda B S hS V) b).out 1 2).mp hbrel

private theorem exists_quasiAffine_baseChange_neighborhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (π : Y ⟶ X) (hπclosed : IsClosedMorphism B S hS π)
    (hπqc : IsQuasiCompact B S hS π)
    (U V : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : yoneda.obj U ⟶ Y) (hi : IsOpenImmersion B S hS i)
    (b : Y ⟶ yoneda.obj V) (x : points B S hS X)
    (hfiber : ∀ y, pointsMap B S hS Y π y = x →
      y ∈ Set.range (pointsMap B S hS (yoneda.obj U) i)) :
    ∃ N : Subfunctor X, IsOpenSubspace B S hS N ∧
      (∃ n, pointsMap B S hS N.toFunctor N.ι n = x) ∧
      IsQuasiAffineHom B S hS (pullback.snd N.ι π ≫ b) := by
  classical
  let R := Subfunctor.range i
  have hR := isOpenSubspace_range_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_yoneda B S hS U) i hi
  let r := Set.range (pointsMap B S hS R.toFunctor R.ι)
  have hr : IsOpen r := isOpen_range_pointsMap_of_isOpenSubspace B S hS hY R hR
  let O := (pointsMap B S hS Y π '' rᶜ)ᶜ
  have hO : IsOpen O := (hπclosed rᶜ hr.isClosed_compl).isOpen_compl
  have hxO : x ∈ O := by
    rintro ⟨y, hy, hyx⟩
    obtain ⟨z, rfl⟩ := hfiber y hyx
    apply hy
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange i) z, ?_⟩
    change (pointsMap B S hS _ R.ι ∘ pointsMap B S hS _ (Subfunctor.toRange i)) z = _
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  obtain ⟨N, hN, hNqc, n, hn, hNO⟩ :=
    exists_quasiCompact_openSubspace_within B S hS hX x O hO hxO
  let H := pullback N.ι π
  have hH := isAlgebraicSpace_pullback B S hS N.ι π hN.1 hY hX
  let a : H ⟶ Y := pullback.snd N.ι π
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have ha : IsOpenImmersion B S hS a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback N.ι π) hN.2
  have hpoints : Set.range (pointsMap B S hS H a) ⊆ r := by
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have ht := hNO (Set.mem_range_self (pointsMap B S hS H (pullback.fst N.ι π) z))
    apply ht
    refine ⟨pointsMap B S hS H a z, hz, ?_⟩
    change (pointsMap B S hS Y π ∘ pointsMap B S hS H a) z =
      (pointsMap B S hS N.toFunctor N.ι ∘ pointsMap B S hS H (pullback.fst N.ι π)) z
    rw [← pointsMap_comp, ← pointsMap_comp]
    exact congrArg (fun f => pointsMap B S hS H f z) pullback.condition.symm
  obtain ⟨d, hd⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hY hH R hR a).mpr hpoints
  let := mono_of_presheaf_isOpenImmersion hi
  let d' : H ⟶ yoneda.obj U := d ≫ inv (Subfunctor.toRange i)
  have hd' : d' ≫ i = a := by
    dsimp only [d']
    calc
      (d ≫ inv (Subfunctor.toRange i)) ≫ i =
          (d ≫ inv (Subfunctor.toRange i)) ≫ (Subfunctor.toRange i ≫ R.ι) := by
        rw [Subfunctor.toRange_ι]
      _ = d ≫ R.ι := by simp
      _ = a := hd
  exact ⟨N, hN, ⟨n, hn⟩, quasiAffine_of_open_factor B S hS hH
    (hπqc N.toFunctor hN.1 hNqc N.ι) U V hU hV i hi a ha d' hd' (a ≫ b)⟩

/-! ### Finiteness of a closed field-valued point over the ground field -/

private theorem locallyOfFiniteType_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  have _ : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fppf
  exact (holdsOnEveryEtaleChart_iff_relative B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    hX hY f hf.1).mpr <| MorphismProperty.relative_monotone (fun _ _ g hg => by
    let : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map g) := hg
    change AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)
    infer_instance) f hf

private theorem locallyOfFiniteType_yonedaMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : IsLocallyOfFiniteType B S hS (yoneda.map f)) :
    AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  have _ : P.IsStableUnderBaseChange := schemeProperty_inverseImage_stable B S hS _
  have hid (W : BigFppfOver B S hS) : P.presheaf (𝟙 (yoneda.obj W)) := by
    have hW : P (𝟙 W) := by
      change AlgebraicGeometry.Etale (T.map (𝟙 W))
      rw [T.map_id]
      infer_instance
    simpa only [yoneda.map_id] using MorphismProperty.relative_map (F := yoneda) hW
  exact hf U V (𝟙 _) (𝟙 _) f (hid U) (hid V) (by simp)

private theorem isFinite_toBase_of_closedImmersion_fieldRepresentative
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : IsLocallyOfFiniteType B (Spec (.of k)) hk f)
    (p : FieldValuedPoint B (Spec (.of k)) hk X)
    (hp : IsClosedImmersion B (Spec (.of k)) hk
      (fieldMorphism B (Spec (.of k)) hk X p)) :
    AlgebraicGeometry.IsFinite p.toBase := by
  let U := p.siteObject B (Spec (.of k)) hk X
  let V : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  have hU := isAlgebraicSpace_yoneda B (Spec (.of k)) hk U
  have hV := isAlgebraicSpace_yoneda B (Spec (.of k)) hk V
  have hpft := locallyOfFiniteType_of_isClosedImmersion B (Spec (.of k)) hk
    hU hX (fieldMorphism B (Spec (.of k)) hk X p) hp
  have hcomp := isLocallyOfFiniteType_comp B (Spec (.of k)) hk hU hX hV
    (fieldMorphism B (Spec (.of k)) hk X p) f hpft hf
  let q : U ⟶ V := Over.homMk U.hom (by change U.hom ≫ 𝟙 _ = U.hom; simp)
  have hterminal : IsTerminal (yoneda.obj V) :=
    IsTerminal.isTerminalObj yoneda V Over.mkIdTerminal
  have hq : fieldMorphism B (Spec (.of k)) hk X p ≫ f = yoneda.map q :=
    hterminal.hom_ext _ _
  rw [hq] at hcomp
  exact AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr
    (locallyOfFiniteType_yonedaMap B (Spec (.of k)) hk q hcomp)

/-! ### Representability from representable open neighbourhoods -/

private theorem isRepresentable_of_open_representable_neighborhoods
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hlocal : ∀ x : points B S hS X,
      ∃ V : Subfunctor X, IsOpenSubspace B S hS V ∧
        (∃ z : points B S hS V.toFunctor, pointsMap B S hS V.toFunctor V.ι z = x) ∧
        V.toFunctor.IsRepresentable) :
    X.IsRepresentable := by
  classical
  obtain ⟨U, a, ha, _⟩ := hX.exists_atlas
  have hasurj :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp ha
  have _ : Small.{u} (points B S hS X) :=
    small_of_surjective (hasurj.comp (pointsEquivScheme B S hS U).symm.surjective)
  let I := Shrink.{u} (points B S hS X)
  let pointOf (i : I) : points B S hS X := (equivShrink _).symm i
  let V : I → Subfunctor X := fun i => (hlocal (pointOf i)).choose
  have hdata (i : I) := (hlocal (pointOf i)).choose_spec
  have hV (y : I) : IsOpenSubspace B S hS (V y) := (hdata y).1
  have hz' (y : I) : ∃ z : points B S hS (V y).toFunctor,
      pointsMap B S hS (V y).toFunctor (V y).ι z = pointOf y := (hdata y).2.1
  let z (y : I) := (hz' y).choose
  have hz (y : I) :
      pointsMap B S hS (V y).toFunctor (V y).ι (z y) = pointOf y := (hz' y).choose_spec
  refine isRepresentable_of_isZariskiCover B S hS X hX I V
    ((isZariskiCover_iff_iUnion_points B S hS X hX I V hV).2
      (Set.eq_univ_of_forall fun x => ?_)) fun y => (hdata y).2.2
  let i : I := equivShrink _ x
  exact Set.mem_iUnion.mpr ⟨i, z i, by simpa [i, pointOf] using hz i⟩

/-! ### The point space is Jacobson, so closed points suffice -/

@[ega "IV 10.7.1" "partial", sga "4 VIII 3.13" "Example in a)"]
private theorem jacobsonSpace_points_of_locallyOfFiniteType
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hdecent : IsDecentSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hfinite : IsLocallyOfFiniteType B (Spec (.of k)) hk f) :
    JacobsonSpace (points B (Spec (.of k)) hk X) := by
  have _ : ObjectProperty.IsLocal (fun T : Scheme.{u} => JacobsonSpace T)
      Scheme.etalePrecoverage :=
    ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage
  let U : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let Y := yoneda.obj U
  have hY : IsAlgebraicSpace B (Spec (.of k)) hk Y :=
    isAlgebraicSpace_yoneda B (Spec (.of k)) hk U
  let T := BigFppfOver.toScheme B (Spec (.of k)) hk
  have hJacY : HasEtaleLocalProperty B (Spec (.of k)) hk Y
      (fun T : Scheme.{u} => JacobsonSpace T) := by
    have hUJac : JacobsonSpace (T.obj U) := inferInstanceAs (JacobsonSpace (Spec (.of k)))
    refine ⟨U, 𝟙 Y, ?_, ?_, hUJac⟩ <;>
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, fun _ _ _ _ snd hpb => ?_⟩ <;>
      have hmap : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso <;>
      let : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd <;>
      let : IsIso (T.map snd) := Functor.map_isIso T snd
    · change AlgebraicGeometry.Surjective (T.map snd)
      infer_instance
    · change AlgebraicGeometry.Etale (T.map snd)
      infer_instance
  exact (exists_jacobson_atlas_iff_jacobsonSpace_points B (Spec (.of k)) hk hX hdecent).mp
    (exists_jacobson_atlas_of_isLocallyOfFiniteType B (Spec (.of k)) hk hY hX f hfinite hJacY)

private theorem isRepresentable_of_closedPoints_schematic
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hdecent : IsDecentSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hfinite : IsLocallyOfFiniteType B (Spec (.of k)) hk f)
    (hclosed : ∀ x : points B (Spec (.of k)) hk X,
      IsClosed ({x} : Set (points B (Spec (.of k)) hk X)) →
      x ∈ Set.range (pointsMap B (Spec (.of k)) hk
        (schematicLocus B (Spec (.of k)) hk X).toFunctor
        (schematicLocus B (Spec (.of k)) hk X).ι)) :
    X.IsRepresentable := by
  classical
  let : JacobsonSpace (points B (Spec (.of k)) hk X) :=
    jacobsonSpace_points_of_locallyOfFiniteType B k hk X hX hdecent f hfinite
  let L := schematicLocus B (Spec (.of k)) hk X
  have hL := (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    B (Spec (.of k)) hk hX).1
  let r := Set.range (pointsMap B (Spec (.of k)) hk L.toFunctor L.ι)
  have hrOpen : IsOpen r := isOpen_range_pointsMap_of_isOpenSubspace B (Spec (.of k)) hk hX L hL
  let C := rᶜ
  have hCclosed : IsClosed C := hrOpen.isClosed_compl
  have hCempty : C = ∅ := by
    by_contra hn
    obtain ⟨x, hxC, hxclosed⟩ := nonempty_inter_closedPoints
      (X := points B (Spec (.of k)) hk X)
      (Set.nonempty_iff_ne_empty.mpr hn) hCclosed.isLocallyClosed
    exact hxC (hclosed x (by simpa using hxclosed))
  have hrange : ∀ x : points B (Spec (.of k)) hk X, x ∈ r :=
    Set.eq_univ_iff_forall.mp (Set.compl_empty_iff.mp hCempty)
  have hLrep := (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    B (Spec (.of k)) hk hX).2
  exact isRepresentable_of_open_representable_neighborhoods B (Spec (.of k)) hk X hX
    fun x => ⟨L, hL, hrange x, hLrep⟩

/-! ### Hypothesis (3) applied to a finite scheme over the algebraic closure -/

private theorem exists_affine_factor_of_finite_over_algebraicallyClosed
    (K : Type u) [Field K] [IsAlgClosed K]
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (haffine : ∀ s : Finset (F.obj (op (Over.mk (𝟙 (B.obj hK))))),
      ∃ (U : BigFppfOver B (Spec (.of K)) hK) (i : yoneda.obj U ⟶ F),
        IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) ∧
        IsOpenImmersion B (Spec (.of K)) hK i ∧
        ∀ x ∈ s, x ∈ Set.range (i.app (op (Over.mk (𝟙 (B.obj hK))))))
    (A : BigFppfOver B (Spec (.of K)) hK)
    (hA : AlgebraicGeometry.IsFinite (B.inclusion.map A.hom)) (j : yoneda.obj A ⟶ F) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK) (i : yoneda.obj U ⟶ F),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) ∧
      IsOpenImmersion B (Spec (.of K)) hK i ∧
      ∃ q : A ⟶ U, yoneda.map q ≫ i = j := by
  classical
  let T := BigFppfOver.toScheme B (Spec (.of K)) hK
  let V : BigFppfOver B (Spec (.of K)) hK := Over.mk (𝟙 (B.obj hK))
  let a : T.obj A ⟶ Spec (.of K) := B.inclusion.map A.hom
  let : AlgebraicGeometry.IsFinite a := hA
  let : IsLocallyArtinian (T.obj A) := IsLocallyArtinian.of_locallyQuasiFinite a
  let : CompactSpace (T.obj A) := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace a
  let : IsArtinianScheme (T.obj A) := ⟨⟩
  let : Fintype (T.obj A) := Fintype.ofFinite _
  let : T1Space A.left.1 := inferInstanceAs (T1Space (T.obj A))
  let ρ (x : T.obj A) : V ⟶ A := Over.homMk
    (ObjectProperty.homMk (AlgebraicGeometry.pointOfClosedPoint a x isClosed_singleton)) (by
      apply ObjectProperty.hom_ext
      exact AlgebraicGeometry.pointOfClosedPoint_comp a x isClosed_singleton)
  let s := Finset.univ.image (fun x : T.obj A => j.app (op V) (ρ x))
  obtain ⟨U, i, hU, hi, hs⟩ := haffine s
  let P := hi.1.pullback j
  let b : P ⟶ A := hi.1.snd j
  let c : yoneda.obj P ⟶ yoneda.obj U := hi.1.fst j
  have sq : IsPullback c (yoneda.map b) i j := hi.1.isPullback j
  have hb : AlgebraicGeometry.IsOpenImmersion (T.map b) := hi.property_snd j
  have hbSurj : AlgebraicGeometry.Surjective (T.map b) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, ht⟩ := hs (j.app (op V) (ρ x)) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    have hcomm : yoneda.map t ≫ i = yoneda.map (ρ x) ≫ j :=
      yonedaEquiv.injective (by simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using ht)
    let l : V ⟶ P := yoneda.preimage (sq.lift (yoneda.map t) (yoneda.map (ρ x)) hcomm)
    have hl : l ≫ b = ρ x := by
      apply yoneda.map_injective
      rw [Functor.map_comp, yoneda.map_preimage]
      exact sq.lift_snd _ _ _
    refine ⟨T.map l (IsLocalRing.closedPoint K), ?_⟩
    change (T.map l ≫ T.map b) _ = x
    rw [← T.map_comp, hl]
    exact AlgebraicGeometry.pointOfClosedPoint_apply a x isClosed_singleton _
  let : IsIso (T.map b) :=
    (AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective (T.map b)).mpr ⟨hb, hbSurj⟩
  let : IsIso b := isIso_of_reflects_iso b T
  refine ⟨U, i, hU, hi, inv b ≫ yoneda.preimage c, ?_⟩
  rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, sq.w]
  simp

/-! ### Stacks 0B88 -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the big fppf site
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_DecentFiniteTypeScheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for binary products of presheaves on the big fppf site
local instance (priority := high) hasBinaryProducts_presheaf_DecentFiniteTypeScheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- **Stacks 0B88.** Let `k` be a field with algebraic closure `K = k̄` and let `X` be an
algebraic space over `k`.  Assume

1. `X` is decent and locally of finite type over `k`,
2. `X_{k̄}` is a scheme, and
3. any finite set of `k̄`-rational points of `X_{k̄}` is contained in an affine.

Then `X` is a scheme.

Hypotheses (1) and (3) are present and not weakened: `hdecent` together with `hfinite` is
hypothesis (1), and `haffine` is hypothesis (3).  Hypothesis (2) is not needed by the proof
below and is omitted, so the statement is stronger than the source's.

`X_{k̄}` is the restriction of `X` to the big fppf site over `Spec k̄` along the morphism
`g : Spec k̄ ⟶ Spec k` of the site, a `k̄`-rational point of it is a section over the terminal
object `Spec k̄` of that site, and an affine open is presented by an open immersion out of an
affine object, as in the library's form of Tag 0BA1. The structure morphism of `X` over `Spec k`
is given explicitly as `f`, the base `Spec k` being terminal in its own big fppf site.

Being decent and locally of finite type over a field, `|X|` is a Jacobson space (Tag 0BA6 and
Tag 0BA3), so it is enough to put every closed point of `|X|` in the schematic locus of
Tag 03JH, and then Tag 03KE in the case `(θ)` finishes.  A closed point is represented by a
closed immersion `Spec l ⟶ X` (Tag 0AHB) with `l/k` finite (Tag 03XG and the Hilbert
Nullstellensatz), so `Spec l ×_X X_{k̄}` is a finite scheme over an algebraically closed field
and hypothesis (3) gives an affine open of `X_{k̄}` through which it factors.  The projection
`π : X_{k̄} ⟶ X` is a base change of the affine, flat, surjective morphism
`Spec k̄ ⟶ Spec k`, hence universally closed and quasi-compact, and closedness converts the
fibrewise containment into a quasi-compact open neighbourhood `N` of the point whose base
change to `k̄` is quasi-affine over `Spec k̄`.  Tag 0423 descends quasi-affineness along that
fpqc covering and Tag 03WM makes `N` a scheme, so the point is in the schematic locus. -/
@[stacks 0B88 "hypotheses (1) and (3) of the source; (2) is not needed"]
theorem isRepresentable_of_isAlgClosure_finite_rationalPoints_isAffine
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hdecent : IsDecentSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hfinite : IsLocallyOfFiniteType B (Spec (.of k)) hk f)
    (haffine :
      let Xbase := (OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          B.obj hK ⟶ B.obj hk)).obj X
      ∀ s : Finset (Xbase.obj (op (Over.mk (𝟙 (B.obj hK))))),
        ∃ (U : BigFppfOver B (Spec (.of K)) hK) (i : yoneda.obj U ⟶ Xbase),
          IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) ∧
          IsOpenImmersion B (Spec (.of K)) hK i ∧
          ∀ x ∈ s, x ∈ Set.range (i.app (op (Over.mk (𝟙 (B.obj hK)))))) :
    X.IsRepresentable := by
  classical
  apply isRepresentable_of_closedPoints_schematic B k hk X hX hdecent f hfinite
  intro x hx
  obtain ⟨p, hp, hpclosed⟩ :=
    exists_fieldValuedPoint_isClosedImmersion B (Spec (.of k)) hk hX hdecent x hx
  have hpfinite := isFinite_toBase_of_closedImmersion_fieldRepresentative
    B k hk X hX f hfinite p hpclosed
  let g : B.obj hK ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let P := p.siteObject B (Spec (.of k)) hk X
  let A : BigFppfOver B (Spec (.of K)) hK := Over.mk (pullback.snd P.hom g)
  let q : (Over.map g).obj A ⟶ P := Over.homMk (pullback.fst P.hom g) pullback.condition
  let j : yoneda.obj A ⟶ (OverShriek.relocalizeRestrict g).obj X :=
    yonedaEquiv.symm (X.map q.op p.value)
  have hA : AlgebraicGeometry.IsFinite (B.inclusion.map A.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback P.hom g).map B.inclusion)
      (show AlgebraicGeometry.IsFinite (B.inclusion.map P.hom) from hpfinite)
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨W, i, hWaffine, hi, w, hw⟩ :=
    exists_affine_factor_of_finite_over_algebraicallyClosed K B hK
      ((OverShriek.relocalizeRestrict g).obj X) haffine A hA j
  let Xbase := (OverShriek.relocalizeRestrict g).obj X
  have hXbase := isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k))
    hK hk g X hX
  let L := OverShriek.relocalizePresheafFunctor g
  let Y := L.obj Xbase
  have hY := isAlgebraicSpace_viewOver B (Spec (.of K)) (Spec (.of k)) hK hk g Xbase hXbase
  let π : Y ⟶ X := OverShriek.relocalizeOfRestricted g (𝟙 Xbase)
  let V : BigFppfOver B (Spec (.of k)) hk := Over.mk g
  let T : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let g₀ : V ⟶ T := Over.homMk g (by change g ≫ 𝟙 _ = g; simp)
  let b : Y ⟶ yoneda.obj V := relocalizeProjection g X
  let eY := relocalizeRestrictProductIso g X
  have hπ : eY.hom ≫ prod.snd = π := prod.lift_snd _ _
  have hb : eY.hom ≫ prod.fst = b := prod.lift_fst _ _
  have hgIntegral : AlgebraicGeometry.IsIntegralHom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [AlgebraicGeometry.IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hπrel (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (hP : P (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
      (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf π := by
    have _ : (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).RespectsIso :=
      (schemeProperty_inverseImage_stable B (Spec (.of k)) hk P).respectsIso
    rw [← hπ]
    exact (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk))
      |>.cancel_left_of_respectsIso eY.hom _).mpr <|
      relativeProperty_baseChange_projection B (Spec (.of k)) hk V X P hP
  have hπuc := hπrel (@AlgebraicGeometry.UniversallyClosed.{u}) inferInstance
  have hπqc : IsQuasiCompact B (Spec (.of k)) hk π :=
    (presheaf_quasiCompact_iff_isQuasiCompact B (Spec (.of k)) hk hπuc.1).mp
      (hπrel (@AlgebraicGeometry.QuasiCompact.{u}) inferInstance)
  have hterminal : IsTerminal (yoneda.obj T) :=
    IsTerminal.isTerminalObj yoneda T Over.mkIdTerminal
  have sqY : IsPullback π b f (yoneda.map g₀) := by
    have hs : IsPullback (prod.snd : yoneda.obj V ⨯ X ⟶ X) prod.fst f (yoneda.map g₀) := by
      convert (IsPullback.of_is_product' (prodIsProd (yoneda.obj V) X) hterminal).flip using 1 <;>
        exact hterminal.hom_ext _ _
    exact hs.of_iso' eY (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using hπ) (by simpa using hb) (by simp) (by simp)
  let U := (Over.map g).obj W
  let i' : yoneda.obj U ⟶ Y :=
    (relocalizeYonedaRepresentableBy g W).toIso.hom ≫ L.map i
  have hi' : IsOpenImmersion B (Spec (.of k)) hk i' :=
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B (Spec (.of k)) hk))
      |>.cancel_left_of_respectsIso
        (relocalizeYonedaRepresentableBy g W).toIso.hom _).mpr <|
      relativeProperty_relocalize B (Spec (.of K)) (Spec (.of k)) hK hk g
        (@AlgebraicGeometry.IsOpenImmersion.{u}) i hi
  have hfiber : ∀ y, pointsMap B (Spec (.of k)) hk Y π y = x →
      y ∈ Set.range (pointsMap B (Spec (.of k)) hk (yoneda.obj U) i') := by
    let A' := (Over.map g).obj A
    let a₀ : A' ⟶ V := Over.homMk A.hom rfl
    let p₀ : P ⟶ T := Over.homMk P.hom (by change P.hom ≫ 𝟙 _ = P.hom; simp)
    let pmap := fieldMorphism B (Spec (.of k)) hk X p
    let j' : yoneda.obj A' ⟶ Y := (relocalizeYonedaRepresentableBy g A).toIso.hom ≫ L.map j
    have hjb : j' ≫ b = yoneda.map a₀ := relocalizeYoneda_projection g A X j
    have hjπ : j' ≫ π = yoneda.map q ≫ pmap := by
      rw [show j' ≫ π = yonedaEquiv.symm (show X.obj (op A') from j.app (op A) (𝟙 A)) from
        relocalizeYoneda_counit g A X j]
      apply yonedaEquiv.injective
      simp [j, pmap, fieldMorphism, ← yonedaEquiv_naturality]
    have sqA : IsPullback q a₀ p₀ g₀ :=
      IsPullback.of_map_of_faithful (Over.forget (B.obj hk))
        (IsPullback.of_hasPullback P.hom g)
    have sq' : IsPullback j' (yoneda.map q) π pmap := by
      have hs : IsPullback (j' ≫ b) (yoneda.map q) (yoneda.map g₀) (pmap ≫ f) := by
        rw [hjb, hterminal.hom_ext (pmap ≫ f) (yoneda.map p₀)]
        exact (sqA.map yoneda).flip
      exact hs.of_right hjπ sqY.flip
    have hfactor : yoneda.map ((Over.map g).map w) ≫ i' = j' := by
      dsimp only [i', j']
      rw [← Category.assoc, relocalizeYoneda_naturality, Category.assoc, ← L.map_comp, hw]
    let Aalg : AlgebraicSpaces B (Spec (.of k)) hk :=
      ⟨yoneda.obj A', isAlgebraicSpace_yoneda B (Spec (.of k)) hk A'⟩
    let Palg : AlgebraicSpaces B (Spec (.of k)) hk :=
      ⟨yoneda.obj P, isAlgebraicSpace_yoneda B (Spec (.of k)) hk P⟩
    let Yalg : AlgebraicSpaces B (Spec (.of k)) hk := ⟨Y, hY⟩
    let Xalg : AlgebraicSpaces B (Spec (.of k)) hk := ⟨X, hX⟩
    have sqalg : IsPullback (ObjectProperty.homMk j' : Aalg ⟶ Yalg)
        (ObjectProperty.homMk (yoneda.map q) : Aalg ⟶ Palg)
        (ObjectProperty.homMk π : Yalg ⟶ Xalg)
        (ObjectProperty.homMk pmap : Palg ⟶ Xalg) :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι (IsAlgebraicSpace B (Spec (.of k)) hk)) sq'
    let pp : FieldValuedPoint B (Spec (.of k)) hk (yoneda.obj P) := { p with value := 𝟙 P }
    have hpp : pointsMap B (Spec (.of k)) hk (yoneda.obj P) pmap
        (pp.class B (Spec (.of k)) hk (yoneda.obj P)) = x := by
      have hm : FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj P) pmap pp = p := by
        change { p with value := pmap.app (op P) (𝟙 P) } = p
        have heval : pmap.app (op P) (𝟙 P) = p.value := by
          change X.map (𝟙 P).op p.value = p.value
          rw [op_id, X.map_id]
          rfl
        rw [heval]
      change (FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj P) pmap pp).class
        B (Spec (.of k)) hk X = x
      rwa [hm]
    intro y hy
    obtain ⟨zz, hzz, -⟩ := exists_point_of_isPullback B (Spec (.of k)) hk
      sqalg y (pp.class B (Spec (.of k)) hk (yoneda.obj P)) (hy.trans hpp.symm)
    refine ⟨pointsMap B (Spec (.of k)) hk (yoneda.obj A')
      (yoneda.map ((Over.map g).map w)) zz, ?_⟩
    change (pointsMap B (Spec (.of k)) hk (yoneda.obj U) i' ∘
      pointsMap B (Spec (.of k)) hk (yoneda.obj A')
        (yoneda.map ((Over.map g).map w))) zz = y
    rwa [← pointsMap_comp, hfactor]
  obtain ⟨N, hN, ⟨n, hn⟩, hNbase⟩ :=
    exists_quasiAffine_baseChange_neighborhood B (Spec (.of k)) hk hX hY π
      (closedMap_of_relative_universallyClosed B (Spec (.of k)) hk hY hX π hπuc)
      hπqc U V hWaffine (by change IsAffine (Spec (.of K)); infer_instance)
      i' hi' b x hfiber
  have hgflat : AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g₀) := by
    change AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hgsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g₀) := by
    change AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [AlgebraicGeometry.surjective_iff]
    exact Function.surjective_to_subsingleton _
  have hNrep : N.toFunctor.IsRepresentable :=
    isRepresentable_of_quasiAffine_fpqc_baseChange B (Spec (.of k)) hk V T
      (by change IsAffine (Spec (.of k)); infer_instance) g₀
      (fpqcCovering_of_affine_flat_surjective B (Spec (.of k)) hk V T g₀
        (by
          change AlgebraicGeometry.IsAffineHom
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          infer_instance)
        hgflat hgsurj)
      hN.1 (isAlgebraicSpace_pullback B (Spec (.of k)) hk N.ι π hN.1 hY hX)
      (N.ι ≫ f) (pullback.fst N.ι π) (pullback.snd N.ι π ≫ b)
      ((IsPullback.of_hasPullback N.ι π).flip.paste_horiz sqY.flip).flip hNbase
  let l := le_schematicLocus B (Spec (.of k)) hk X N hN hNrep
  refine ⟨pointsMap B (Spec (.of k)) hk N.toFunctor (Subfunctor.homOfLe l) n, ?_⟩
  change (pointsMap B (Spec (.of k)) hk _ _ ∘
    pointsMap B (Spec (.of k)) hk N.toFunctor (Subfunctor.homOfLe l)) n = x
  rwa [← pointsMap_comp, Subfunctor.homOfLe_ι]

end AlgebraicGeometry.Space

end
