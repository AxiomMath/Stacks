module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension.ResidueFieldPoint
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# The change-of-residue-field square: auxiliary lemmas

Auxiliary results for the change-of-residue-field step in the proof of
`Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt` (Stacks 07XG): an equivalence
of categories cofibred in groupoids over Artinian local algebras is smooth, maps between
predeformation categories are determined by their images in schemes, `eqToHom` bookkeeping for
casts along equalities of Artinian local algebras, and the base compatibility of the route around
the change-of-residue-field square that restricts the slice first.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

-- `CategoryTheory.Functor.Fiber` is a plain `def`, so a term whose type mentions the underlying
-- object of a fibre -- such as the chosen cartesian lift `c.map f x`, whose source is
-- `(c.obj f x).1` where `(c.sliceFunctor x).obj f` is expected -- is not type-correct at
-- `implicit` transparency. Making it implicit-reducible here is what
-- `StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf` does for the same reason.
attribute [local implicit_reducible]
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.BasedFunctor.comp
  Deformation.changeOfFieldsBasedFunctor

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)

variable (x : X)
variable {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
variable (iΛ : Spec (.of Λ) ⟶ S) (uₗ₀ : Over (p.obj x))
variable (huₗ₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))

attribute [local instance] PredeformationConstruction.category

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  InducedPredeformationFunctor.toBasedFunctor

private theorem fiberwise_preimage_of_cofibered
    {C : Type*} [Category C] {𝓕 : BasedCategory C} {𝓖 : BasedCategory C}
    (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.EssSurj]
    (h𝓕 : Deformation.IsCofiberedInGroupoids 𝓕.p) (y : 𝓖.obj) :
    ∃ (x : 𝓕.obj) (e : φ.obj x ≅ y),
      𝓖.p.IsHomLift (𝟙 (𝓖.p.obj y)) e.hom := by
  let x₀ := φ.toFunctor.objPreimage y
  let e₀ := φ.toFunctor.objObjPreimageIso y
  let c : 𝓕.p.obj x₀ ≅ 𝓖.p.obj y :=
    eqToIso (φ.w_obj x₀).symm ≪≫ 𝓖.p.mapIso e₀
  obtain ⟨z, hz, β, hβ⟩ := h𝓕.exists_iso_lift (z := Opposite.op x₀) c.symm.op
  let x := z.unop
  let b : x ≅ x₀ := β.unop
  have hx : 𝓕.p.obj x = 𝓖.p.obj y := by
    simpa using congrArg Opposite.unop hz
  have hb : 𝓕.p.map b.hom = eqToHom hx ≫ c.inv := by
    have h := IsHomLift.fac' 𝓕.p.op c.symm.op.hom β.hom
    simpa [b, Functor.op_map] using congrArg (fun f => f.unop) h
  let e : φ.obj x ≅ y := φ.toFunctor.mapIso b ≪≫ e₀
  refine ⟨x, e, IsHomLift.of_fac' 𝓖.p _ e.hom ((φ.w_obj x).trans hx) rfl ?_⟩
  let : 𝓖.p.IsHomLift (𝓕.p.map b.hom) (φ.map b.hom) :=
    BasedFunctor.preserves_isHomLift φ _ _
  have hm : 𝓖.p.map (φ.map b.hom) = eqToHom (φ.w_obj x) ≫
      𝓕.p.map b.hom ≫ eqToHom (φ.w_obj x₀).symm :=
    IsHomLift.fac' 𝓖.p (𝓕.p.map b.hom) (φ.map b.hom)
  dsimp [e]
  rw [𝓖.p.map_comp, hm, hb]
  simp [c, Category.assoc]

theorem isSmooth_of_equivalence
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat Λ k)}
    {𝓖 : BasedCategory (Deformation.ArtinianLocalAlgCat Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.IsEquivalence]
    (h𝓕 : Deformation.IsCofiberedInGroupoids 𝓕.p) : Deformation.IsSmooth φ := by
  intro B A f _ y x g hg
  let := hg
  obtain ⟨x', e, he⟩ := fiberwise_preimage_of_cofibered φ h𝓕 y
  let := he
  have hy : 𝓖.p.obj y = B := IsHomLift.domain_eq 𝓖.p f g
  have hcomp : 𝓖.p.IsHomLift f (e.hom ≫ g) := by
    rw [hy] at he
    let := he
    exact IsHomLift.comp_lift_id_left 𝓖.p f g e.hom
  let h := φ.toFunctor.preimage (e.hom ≫ g)
  have hh : φ.map h = e.hom ≫ g := φ.toFunctor.map_preimage _
  refine ⟨x', h, e.hom, ?_, hy ▸ he, hh⟩
  apply (BasedFunctor.isHomLift_iff φ f h).mp
  rw [hh]
  exact hcomp

theorem unique_lift_post
    {C D E : Type*} [Category C] [Category D] [Category E]
    (p : C ⥤ D) (hp : p.IsFiberedInGroupoids) (J : D ⥤ E) [J.Full] [J.Faithful]
    {a b c : C} (f : a ⟶ c) (g : b ⟶ c)
    (h : (p ⋙ J).obj b ⟶ (p ⋙ J).obj a)
    (w : h ≫ (p ⋙ J).map f = (p ⋙ J).map g) :
    ∃! t : b ⟶ a, (p ⋙ J).map t = h ∧ t ≫ f = g := by
  obtain ⟨t, ⟨ht, htf⟩, hu⟩ := hp.unique_lift f g (J.preimage h)
    (J.map_injective (by simpa using w))
  refine ⟨t, ⟨by simp [Functor.comp_map, ht], htf⟩, ?_⟩
  intro t' ht'
  exact hu t' ⟨J.map_injective (by simpa using ht'.1), ht'.2⟩

theorem deformation_arrow_map_eq
    {Y : Type*} [Category Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (a b : DeformationObject i q y₀ hy₀)
    (hA : a.algebra = b.algebra) (e : q.obj b.point = q.obj a.point) :
    q.map b.arrow ≫ eqToHom e = q.map a.arrow := by
  apply Over.OverMorphism.ext
  rcases a with ⟨A, a, α, ha, hα⟩
  rcases b with ⟨D, b, β, hb, hβ⟩
  dsimp at hA e ⊢
  subst D
  rw [← hα] at hβ
  simpa [Over.comp_left, Over.eqToHom_left, Category.assoc] using
    congrArg (fun f => eqToHom (congrArg Over.left hy₀) ≫ f ≫
      eqToHom (congrArg Over.left ha).symm) hβ

theorem predeformation_map_eq_of_projection_eq
    {Y : Type*} [Category Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : PredeformationConstruction i q y₀ hy₀)
    {a b : C.carrier} (f g : a ⟶ b) (h : C.projection.map f = C.projection.map g) :
    q.map (C.morphisms a b f).arrow = q.map (C.morphisms a b g).arrow := by
  have hr : (C.morphisms a b f).ringHom = (C.morphisms a b g).ringHom := by
    rw [← C.morphism_projection f, ← C.morphism_projection g, h]
  apply Over.OverMorphism.ext
  have hf := (C.morphisms a b f).arrow_base
  have hg := (C.morphisms a b g).arrow_base
  rw [hr, ← hg] at hf
  simpa [Category.assoc] using congrArg (fun k =>
    eqToHom (congrArg Over.left (C.objects b).base) ≫ k ≫
      eqToHom (congrArg Over.left (C.objects a).base).symm) hf

/-- Transport an equality of composites along the casts appearing on either side and append a
common tail. Stating this separately keeps the `eqToHom` bookkeeping out of proofs whose terms
are only type-correct after unfolding the predeformation constructions. -/
theorem comp_eqToHom_tail_eq {𝒞 : Type*} [Category 𝒞]
    {V W Y₀ Y Y' Y'' Z : 𝒞} {f : V ⟶ W} {f' : W ⟶ Y₀} {e : Y₀ = Y} {e' : Y₀ = Y'}
    {m : V ⟶ Y''} {e'' : Y'' = Y} {e''' : Y'' = Y'} {k : Y' ⟶ Z}
    (hu : f ≫ f' ≫ eqToHom e = m ≫ eqToHom e'') :
    f ≫ f' ≫ eqToHom e' ≫ k = m ≫ eqToHom e''' ≫ k := by
  subst e'
  subst e''
  subst e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hu ⊢
  rw [← hu, Category.assoc]

private theorem specMap_eqToHom
    {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} R k} (e : A = D) :
    Spec.map (CommRingCat.ofHom (eqToHom e).hom.toRingHom) =
      eqToHom (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k =>
        Spec (.of A)) e).symm := by
  cases e
  show Spec.map (𝟙 _) = 𝟙 _
  simp

/-- Precomposing a ring map with the cast along an equality of Artinian local algebras becomes,
on `Spec`, postcomposition with the corresponding `eqToHom`. -/
theorem specMap_comp_eqToHom
    {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} R k} (e : A = D)
    {V : Type u} [CommRing V] (f : (D : Type u) →+* V) :
    Spec.map (CommRingCat.ofHom (f.comp (eqToHom e).hom.toRingHom)) =
      Spec.map (CommRingCat.ofHom f) ≫
        eqToHom (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k =>
          Spec (.of A)) e).symm := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_eqToHom]

private theorem specMap_cast_codomain
    {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} R k}
    (e : D = A) (V : CommRingCat.{u}) (f : V →+* A) :
    Spec.map (CommRingCat.ofHom (e.symm ▸ f)) =
      eqToHom (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k =>
        Spec (.of A)) e) ≫ Spec.map (CommRingCat.ofHom f) := by
  cases e
  simp

theorem restriction_base_changed_algebra
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
    (i : Spec (.of T.Λ) ⟶ S) (x₀ xₗ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ i))
    (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ i))
    (η : xₗ ⟶ x₀) (E : Site.ChangeOfFieldFunctor T i B hS p x₀ xₗ hx₀ hxₗ η)
    (a : Deformation.ChangeOfFieldsCategory T
      (predeformationCategory i (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (h : (p ⋙ Over.post B.inclusion).obj
      ((predeformationCategory i (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
        (E.toFunctor.obj a)).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ i)) :
    eqToHom (congrArg Over.left h).symm ≫
      ((p ⋙ Over.post B.inclusion).map (E.restriction a)).left ≫
      eqToHom (congrArg Over.left
        ((predeformationCategory i (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).base) =
      Spec.map (CommRingCat.ofHom (Site.deformationProjection T i B hS p x₀ hx₀ a)) := by
  have he := E.restriction_base a
  rw [specMap_cast_codomain (E.algebra_eq a)
    (.of ((predeformationCategory i (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra)
    (Site.deformationProjection T i B hS p x₀ hx₀ a)] at he
  simpa [Category.assoc] using congrArg (fun f =>
    eqToHom (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l =>
      Spec (.of A)) (E.algebra_eq a)).symm ≫ f) he

/-- The structure morphism to `x` of the object obtained by restricting the slice first and then
mapping to `𝒳`, read off over the base of the `k`-level deformation. One half of the
base-compatibility input of `basedIso_changeOfFieldFunctor`. -/
theorem basedIso_changeOfFieldFunctor_baseSource
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) (iT : Spec (.of T.Λ) ⟶ S)
    (c : p.ChoiceOfPullbacks)
    (uκ uₗ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (huₗ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (δ : uₗ ⟶ uκ)
    (hxₗ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (Gₗ : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ huₗ)
    (Es : Site.ChangeOfFieldFunctor T iT B hS (Over.forget (p.obj x)) uκ uₗ huκ huₗ δ)
    (a : Deformation.ChangeOfFieldsCategory T
      (predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection)
    (bH : (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iT (p ⋙ Over.post B.inclusion)
            ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxₗ).objects
          (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT)) :
    eqToHom (congrArg Over.left bH).symm ≫
      ((p ⋙ Over.post B.inclusion).map
        (eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
          c.map ((predeformationCategory iT
              (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).objects
            (Es.toFunctor.obj a)).point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left =
    Spec.map (CommRingCat.ofHom (Site.deformationProjection T iT B hS
      (Over.forget (p.obj x)) uκ huκ a)) ≫
      eqToHom (congrArg Over.left ((predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects a.fst).base).symm ≫
      ((Over.post B.inclusion).map ((predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects
          a.fst).point.hom).left := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let Ds := predeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ
  let Dt := predeformationCategory iT q (F.obj uₗ) hxₗ
  let d := Ds.objects (Es.toFunctor.obj a)
  have bd : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj d.point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT) :=
    d.base.trans (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l =>
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iT)) (Es.algebra_eq a))
  have hs := restriction_base_changed_algebra B S hS (Over.forget (p.obj x))
    T iT uκ uₗ huκ huₗ δ Es a bd
  have hdmap := IsHomLift.fac' p d.point.hom
    (c.map d.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))
  have hw : ((Over.post B.inclusion).map (Es.restriction a).left).left ≫
      ((Over.post B.inclusion).map
        ((predeformationCategory iT
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects
            a.fst).point.hom).left =
      ((Over.post B.inclusion).map d.point.hom).left :=
    congrArg (fun f => ((Over.post B.inclusion).map f).left) (Es.restriction a).w
  rw [← hs]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hvH : (q.map (eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
        c.map d.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left =
      (q.map (eqToHom (show (Dt.objects (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).point =
          (c.obj d.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))).1 from
        Gₗ.object_point (Es.toFunctor.obj a)))).left ≫
      (q.map (c.map d.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left := by
    rw [← Over.comp_left, ← q.map_comp]
  rw [hvH]
  dsimp only [q, Functor.comp_map]
  rw [eqToHom_map, hdmap]
  simp only [Functor.map_comp, Over.comp_left, Over.eqToHom_left, eqToHom_map,
    eqToHom_trans_assoc, eqToHom_refl, Category.comp_id]
  exact congrArg (fun f => eqToHom (congrArg Over.left bd).symm ≫ f) hw.symm

end Deformation.Artin

end
