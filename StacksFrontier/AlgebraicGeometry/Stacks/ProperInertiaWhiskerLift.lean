module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.CategoryTheory.DottedArrows.TwoYoneda
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase

/-!
# Lifting a 2-endomorphism along the generic point, from a proper inertia

Let `𝒴` be an algebraic stack over a scheme `S` of a big fppf site, let `R` be a valuation ring
whose spectrum and whose fraction field's spectrum are objects `W` and `V` of the site, let
`inc : V ⟶ W` be the inclusion of the generic point and let `y : 𝒞/W ⟶ 𝒴` be a 1-morphism. If
the inertia projection `π : I_𝒴 ⟶ 𝒴` is proper in the sense of Properties of Stacks, Section
04XB, then every 2-endomorphism of `y ∘ j`, where `j : 𝒞/V ⟶ 𝒞/W` is the restriction along
`inc`, is the left whiskering `j ◁ δ` of a 2-endomorphism `δ` of `y`.

## Main results

* `AlgebraicGeometry.Stack.exists_lift_of_isProper` and
  `AlgebraicGeometry.Stack.exists_section_of_isProper`: the valuative criterion of properness
  for a morphism of algebraic spaces, read against site objects merely isomorphic to the spectra
  of a valuation ring and of its fraction field, and in relocalised form.
* `AlgebraicGeometry.Stack.exists_extension_in_represented_fiber`: a point of the base change
  of a proper 1-morphism representable by algebraic spaces, taken over the generic point,
  extends over the whole spectrum.
* `AlgebraicGeometry.Stack.exists_whiskerLeft_of_isProper_inertiaProjection`: the lifting of
  2-endomorphisms described above.

## Implementation notes

Properness is taken in the relative sense of Stacks 04XB, `AlgebraicGeometry.Stack.IsProper`,
rather than the absolute sense of Stacks 0CL5: the inertia projection of an algebraic stack is
representable by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack`).

The facts about vertical morphisms take their `IsHomLift` hypotheses explicitly rather than as
instances.

## References

* [Stacks Project, Tag 0CLD](https://stacks.math.columbia.edu/tag/0CLD)
* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor

namespace AlgebraicGeometry.Stack

universe u w u₁ v₁ u₂ v₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting along a proper morphism of algebraic spaces -/

/-- **The valuative criterion of properness, read against a pair of site objects merely
isomorphic to the spectra of a valuation ring and of its fraction field.** -/
theorem exists_lift_of_isProper {U V : BigFppfOver B S hS} (j : V ⟶ U)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of R))
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of (FractionRing R)))
    (hj : (BigFppfOver.toScheme B S hS).map j =
      eV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ eU.inv)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (p : X ⟶ Y) (hp : Space.IsProper B S hS p)
    (x : yoneda.obj V ⟶ X) (y : yoneda.obj U ⟶ Y)
    (hxy : x ≫ p = yoneda.map j ≫ y) :
    ∃ l : yoneda.obj U ⟶ X, yoneda.map j ≫ l = x ∧ l ≫ p = y := by
  have hcont : ∀ (T : BigFppfOver B S hS) (A : CommRingCat.{u}),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec A) → B.Contains (Spec A) := fun T A e => by
    change (Spec A).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact T.left.property
  have hR := hcont U _ eU
  have hK := hcont V _ eV
  let base := eU.inv ≫ U.hom.hom
  let R₀ := siteObject B S hS hR base
  let K₀ := siteObject B S hS hK
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ base)
  let iR : R₀ ≅ U := Over.isoMk
    (ObjectProperty.isoMk _ eU.symm) (by apply ObjectProperty.hom_ext; rfl)
  have hinc : eV.inv ≫ j.left.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ eU.inv := by
    change j.left.hom = _ at hj
    simp [hj]
  let iK : K₀ ≅ V := Over.isoMk
    (ObjectProperty.isoMk _ eV.symm) (by
      apply ObjectProperty.hom_ext
      show eV.inv ≫ V.hom.hom = _
      have h := congrArg (fun k => k.hom) (Over.w j)
      change j.left.hom ≫ U.hom.hom = V.hom.hom at h
      rw [← h, ← Category.assoc, hinc]
      rfl)
  let j₀ : K₀ ⟶ R₀ := Over.homMk
    (ObjectProperty.homMk (Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have hj₀ : iK.hom ≫ j = j₀ ≫ iR.hom := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hinc
  let q : Space.ValuativeSquare p :=
    { R := R
      K := FractionRing R
      ring_mem := hR
      field_mem := hK
      base := base
      generic := yoneda.map iK.hom ≫ x
      special := yoneda.map iR.hom ≫ y
      comm := by
        show (yoneda.map iK.hom ≫ x) ≫ p =
          yoneda.map j₀ ≫ yoneda.map iR.hom ≫ y
        rw [Category.assoc, hxy, ← Category.assoc, ← yoneda.map_comp, hj₀,
          yoneda.map_comp, Category.assoc] }
  obtain ⟨⟨l⟩, -⟩ :=
    (Space.isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated hX hY p
      hp.2.1 (Space.isQuasiSeparated_of_isSeparated B S hS hp.1)).mp hp q
  refine ⟨yoneda.map iR.inv ≫ l.map, ?_, ?_⟩
  · apply (cancel_epi (yoneda.map iK.hom)).mp
    rw [← Category.assoc, ← yoneda.map_comp, hj₀, yoneda.map_comp]
    have hl := l.generic_comm
    change yoneda.map j₀ ≫ l.map = yoneda.map iK.hom ≫ x at hl
    simpa only [Category.assoc, ← yoneda.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using hl
  · rw [Category.assoc, l.special_comm]
    show yoneda.map iR.inv ≫ yoneda.map iR.hom ≫ y = y
    simp [← yoneda.map_comp_assoc]

/-- **The relocalised form of `AlgebraicGeometry.Stack.exists_lift_of_isProper`.** If the algebraic
space `F` over the slice at `U` represents a proper morphism over `U`, and `F` has a section over
the object `Over.mk j.left` of that slice, then that section extends to a section over the unit
object, provided `U` is the spectrum of a valuation ring, `V` the spectrum of its fraction field
and `j` the inclusion of the generic point. -/
theorem exists_section_of_isProper {U V : BigFppfOver B S hS} (j : V ⟶ U)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of R))
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of (FractionRing R)))
    (hj : (BigFppfOver.toScheme B S hS).map j =
      eV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ eU.inv)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hp : Space.IsProper B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (s : F.obj (.op (Over.mk j.left))) :
    ∃ t : F.obj (.op (Over.mk (𝟙 U.left))),
      F.map (Over.homMk j.left (Category.comp_id _) :
        Over.mk j.left ⟶ Over.mk (𝟙 U.left)).op t = s := by
  let A : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩
  let G := spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom
  let i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app A
  let p := (algebraicSpaceMap B S hS U (G.obj A)).hom
  let s₀ : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (.op V) := ⟨⟨j.left, s⟩, j.w⟩
  let x : yoneda.obj V ⟶ (G.obj A).1.left := yonedaEquiv.symm (i.inv.app _ s₀)
  have hx : x ≫ p = yoneda.map j := by
    apply yonedaEquiv.injective
    show p.app (.op V) ((G.obj A).1.left.map (𝟙 V).op (i.inv.app (.op V) s₀)) = j
    rw [op_id, CategoryTheory.Functor.map_id]
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS
      U.hom A (.op V) s₀
  obtain ⟨l, hl, hlp⟩ := exists_lift_of_isProper B S hS j R eU eV hj (G.obj A).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) p hp x (𝟙 _) (by simpa using hx)
  let t₀ := i.hom.app (.op U) (yonedaEquiv l)
  have ht : (Over.homMk t₀.1.1 t₀.2 : U ⟶ U) = 𝟙 _ := by
    have ht := spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS
      U.hom A (.op U) t₀
    have hp' := congrArg (fun η => η.app (.op U) (𝟙 U)) hlp
    dsimp at hp'
    change p.app (.op U) (i.inv.app (.op U) t₀) = _ at ht
    simp only [t₀, Iso.hom_inv_id_app_apply] at ht
    exact ht.symm.trans hp'
  have htbase : t₀.1.1 = 𝟙 U.left := congrArg (fun k => k.left) ht
  have hext : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).map j.op t₀ = s₀ := by
    have hl' := congrArg (fun η => η.app (.op V) (𝟙 V)) hl
    change l.app (.op V) (𝟙 V ≫ j) = x.app (.op V) (𝟙 V) at hl'
    rw [Category.id_comp] at hl'
    dsimp only [t₀]
    rw [← NatTrans.naturality_apply]
    show i.hom.app (.op V) ((G.obj A).1.left.map j.op (l.app (.op U) (𝟙 U))) = s₀
    rw [← l.naturality_apply]
    show i.hom.app (.op V) (l.app (.op V) (j ≫ 𝟙 U)) = s₀
    rw [Category.comp_id, hl']
    show i.hom.app (.op V) ((G.obj A).1.left.map (𝟙 V).op (i.inv.app (.op V) s₀)) = s₀
    rw [op_id, CategoryTheory.Functor.map_id]
    exact i.inv_hom_id_app_apply _ s₀
  clear_value t₀
  obtain ⟨⟨ψ, t⟩, hψ⟩ := t₀
  dsimp only at htbase
  subst htbase
  refine ⟨t, ?_⟩
  have hh := congrArg (fun z => z.1) hext
  change (⟨j.left ≫ 𝟙 U.left,
    F.map (Over.homMk j.left rfl :
      Over.mk (j.left ≫ 𝟙 U.left) ⟶ Over.mk (𝟙 U.left)).op t⟩ :
      Σ χ : V.left ⟶ U.left, F.obj (.op (Over.mk χ))) = ⟨j.left, s⟩ at hh
  have hkey := OverShriek.sigmaMk_eq F t
    (Over.homMk j.left rfl : Over.mk (j.left ≫ 𝟙 U.left) ⟶ Over.mk (𝟙 U.left))
    (Over.homMk j.left (Category.comp_id _) : Over.mk j.left ⟶ Over.mk (𝟙 U.left)) rfl
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp (hkey.symm.trans hh)
  exact eq_of_heq h2

/-! ### Extending a point of a base change -/

/-- Transporting a section of a presheaf along two composable `eqToHom`s is transporting it along
their composite. -/
theorem map_op_eqToHom_comp {C : Type u₁} [Category.{v₁} C] (F : Cᵒᵖ ⥤ Type u₂)
    {a b c : C} (h₁ : a = b) (h₂ : b = c) (x : F.obj (Opposite.op c)) :
    F.map (eqToHom h₁).op (F.map (eqToHom h₂).op x) = F.map (eqToHom (h₁.trans h₂)).op x := by
  subst h₁
  subst h₂
  simp

/-- Transporting a section of a presheaf along an `eqToHom` of a self-equality does nothing. -/
theorem map_op_eqToHom_self {C : Type u₁} [Category.{v₁} C] (F : Cᵒᵖ ⥤ Type u₂)
    {a : C} (h : a = a) (x : F.obj (Opposite.op a)) : F.map (eqToHom h).op x = x := by
  rw [show h = rfl from rfl]
  simp

/-- **A section of a representing presheaf extending a given one produces a morphism of the
represented fibred category over the given morphism of the base.** -/
theorem exists_extension_of_presheaf_section
    {C : Type (u + 1)} [Category.{u} C] {Z : Type (u + 1)} [Category.{u} Z]
    (p : Z ⥤ C) (F : Cᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : Z) {T : C} (j : p.obj z ⟶ T) (t : F.obj (Opposite.op T))
    (ht : F.map j.op t =
      F.map (eqToHom (Functor.congr_obj e.hom.w z).symm).op (e.hom.functor.obj z).fiber.as) :
    ∃ (z' : Z) (_ : z ⟶ z'), p.obj z' = T := by
  let zF : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨T, Discrete.mk t⟩
  let τ : e.hom.functor.obj z ⟶ zF :=
    { base := eqToHom (Functor.congr_obj e.hom.w z) ≫ j
      fiber := eqToHom (by
        apply Discrete.ext
        show (e.hom.functor.obj z).fiber.as =
          F.map (eqToHom (Functor.congr_obj e.hom.w z) ≫ j).op t
        rw [op_comp, F.map_comp, types_comp_apply, ht]
        exact ((map_op_eqToHom_comp F _ _ _).trans
          (map_op_eqToHom_self F _ (e.hom.functor.obj z).fiber.as)).symm) }
  have hτ : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift j τ :=
    IsHomLift.of_fac' _ j τ (Functor.congr_obj e.hom.w z) rfl (by
      show _ ≫ j = _ ≫ j ≫ 𝟙 T
      simp)
  have hmap : p.IsHomLift j (e.inv.functor.map τ) :=
    Functor.isHomLift_map_of_comp_eq e.inv.w j τ
  have hu := e.isHomLift_unitIso_hom_app z
  have hlift : p.IsHomLift j (e.unitIso.hom.app z ≫ e.inv.functor.map τ) :=
    IsHomLift.comp_lift_id_left p j (e.inv.functor.map τ) (e.unitIso.hom.app z)
  exact ⟨e.inv.functor.obj zF, e.unitIso.hom.app z ≫ e.inv.functor.map τ,
    IsHomLift.codomain_eq p j (e.unitIso.hom.app z ≫ e.inv.functor.map τ)⟩

/-- **A point of a base change over the generic point of the spectrum of a valuation ring extends
over the whole spectrum, when the 1-morphism is proper and representable by algebraic spaces.**

That is, a point `q` of the base change along `y` lying over the generic point admits a morphism
`q ⟶ q'` to a point `q'` lying over the unit object. -/
theorem exists_extension_in_represented_fiber
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (g : 𝒜 ⟶ ℬ)
    (hg : IsProper B S hS g) (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    {W V : BigFppfOver B S hS} (inc : V ⟶ W)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (eW : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (.of R))
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of (FractionRing R)))
    (hinc : (BigFppfOver.toScheme B S hS).map inc =
      eV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ eW.inv)
    (y : BigFppfOver B W.left.1 W.left.2 ⥤ ℬ.val.obj)
    (hy : y ⋙ ℬ.val.p = Over.map W.hom)
    (q : TwoFibreProductOver (Over.map W.hom) 𝒜.val.p ℬ.val.p y g.hom.toFunctor)
    (hq : q.x = Over.mk inc.left) :
    ∃ (q' : TwoFibreProductOver (Over.map W.hom) 𝒜.val.p ℬ.val.p y g.hom.toFunctor)
      (_ : q ⟶ q'), q'.x = Over.mk (𝟙 W.left) := by
  obtain ⟨qb, qx, qy, qhx, qhy, qiso, qvert⟩ := q
  dsimp only at hq
  subst hq
  obtain ⟨F, hF, ⟨e⟩⟩ := hrep W y hy
  obtain ⟨t, ht⟩ := exists_section_of_isProper B S hS inc R eW eV hinc F hF
    (hg W y hy F hF ⟨e⟩)
    (F.map (eqToHom (Functor.congr_obj e.hom.w
      ⟨qb, Over.mk inc.left, qy, qhx, qhy, qiso, qvert⟩).symm).op
      (e.hom.functor.obj ⟨qb, Over.mk inc.left, qy, qhx, qhy, qiso, qvert⟩).fiber.as)
  exact exists_extension_of_presheaf_section _ F e _ _ t ht

/-! ### Lifting a 2-endomorphism along the generic point -/

section Vertical

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {𝒮 : Type u₂} [Category.{v₂} 𝒮] (p : 𝒜 ⥤ 𝒮) {T : 𝒮}

/-- A morphism lying over an identity has source lying over the same object. -/
theorem obj_eq_of_isHomLift_id {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 T) φ) :
    p.obj a = T :=
  have := h
  IsHomLift.domain_eq p (𝟙 T) φ

/-- A vertical endomorphism of an object of a category over `𝒮` is sent to an identity. -/
theorem map_eq_id_of_isHomLift_id {a : 𝒜} (φ : a ⟶ a) (h : p.IsHomLift (𝟙 T) φ) :
    p.map φ = 𝟙 (p.obj a) := by
  have := h
  obtain rfl : p.obj a = T := IsHomLift.domain_eq p (𝟙 T) φ
  exact (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj a)) φ).symm

/-- An endomorphism sent to an identity lies over the identity of the object below it. -/
theorem isHomLift_id_of_map_eq_id {a : 𝒜} (φ : a ⟶ a) (hφ : p.map φ = 𝟙 (p.obj a))
    (ha : p.obj a = T) : p.IsHomLift (𝟙 T) φ := by
  subst ha
  rw [← hφ]
  infer_instance

/-- The inverse of an isomorphism lying over an identity lies over that identity. -/
theorem isHomLift_id_inv {a b : 𝒜} (i : a ≅ b) (h : p.IsHomLift (𝟙 T) i.hom) :
    p.IsHomLift (𝟙 T) i.inv := by
  have := h
  have hiso := IsHomLift.lift_id_inv_isIso p T i.hom
  rwa [show CategoryTheory.inv i.hom = i.inv from by simp] at hiso

/-- A composite of two morphisms lying over one identity lies over it. -/
theorem isHomLift_comp_id {a b c : 𝒜} (φ : a ⟶ b) (ψ : b ⟶ c)
    (hφ : p.IsHomLift (𝟙 T) φ) (hψ : p.IsHomLift (𝟙 T) ψ) : p.IsHomLift (𝟙 T) (φ ≫ ψ) :=
  have := hφ
  have := hψ
  IsHomLift.comp_of_lift_id p T φ ψ

end Vertical

/-- **Every 2-endomorphism of `y ∘ j` is the left whiskering of a 2-endomorphism of `y`**, when
the inertia projection `I_𝒴 ⟶ 𝒴` is proper and `j` is the inclusion of the generic point of the
spectrum of a valuation ring. -/
theorem exists_whiskerLeft_of_isProper_inertiaProjection
    {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (hI : IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴).hom)
    {W V : BigFppfOver B S hS} (inc : V ⟶ W)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (eW : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (.of R))
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of (FractionRing R)))
    (hinc : (BigFppfOver.toScheme B S hS).map inc =
      eV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ eW.inv)
    {j : schemeFibredCategory B S hS V ⟶ schemeFibredCategory B S hS W}
    (hj : j.hom.toFunctor = Over.map inc)
    (y : schemeFibredCategory B S hS W ⟶ 𝒴.1)
    (τ : (j ≫ y) ⟶ (j ≫ y)) :
    ∃ δ : y ⟶ y, j ◁ δ = τ := by
  classical
  let π := (inertiaProjectionAlgebraicStacks B S hS 𝒴).hom
  have hrep : IsRepresentableByAlgebraicSpaces B S hS π.hom :=
    isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒴.val 𝒴.property
  let back := Over.iteratedSliceBackward W
  let V₀ : (schemeFibredCategory B S hS V).val.obj := Over.mk (𝟙 V)
  have hjobj : j.hom.obj V₀ = Over.mk inc := by
    rw [show j.hom.toFunctor = Over.map inc from hj]
    show Over.mk (𝟙 V ≫ inc) = Over.mk inc
    rw [Category.id_comp]
  let yf := back ⋙ y.hom.toFunctor
  have hyf : yf ⋙ 𝒴.val.val.p = Over.map W.hom :=
    (congrArg (fun k => back ⋙ k) y.hom.w).trans (Over.iteratedSliceBackward_forget W)
  have hτ : 𝒴.val.val.p.IsHomLift (𝟙 V) (τ.hom.toNatTrans.app V₀) := τ.hom.isHomLift' V₀
  have hτiso : IsIso (τ.hom.toNatTrans.app V₀) :=
    Functor.isIso_of_fiber_isGroupoid (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid V)
      (τ.hom.toNatTrans.app V₀) hτ
  let τAut : Aut (y.hom.obj (j.hom.obj V₀)) := @asIso _ _ _ _ (τ.hom.toNatTrans.app V₀) hτiso
  let A : RelativeInertia 𝒴.val.val.p :=
    { obj := y.hom.obj (j.hom.obj V₀)
      auto := τAut
      cond := map_eq_id_of_isHomLift_id 𝒴.val.val.p (τ.hom.toNatTrans.app V₀) hτ }
  have hA : 𝒴.val.val.p.obj A.obj = V :=
    obj_eq_of_isHomLift_id 𝒴.val.val.p (τ.hom.toNatTrans.app V₀) hτ
  have hgx : (Over.map W.hom).obj (Over.mk inc.left) = V := by
    show Over.mk (inc.left ≫ W.hom) = V
    rw [Over.w inc]
    rfl
  let c₀ : back.obj (Over.mk inc.left) ≅ Over.mk inc :=
    Over.isoMk (Over.isoMk (Iso.refl V.left) (by
          show 𝟙 V.left ≫ V.hom = inc.left ≫ W.hom
          rw [Category.id_comp]
          exact (Over.w inc).symm)) (by
        apply Over.OverMorphism.ext
        show 𝟙 V.left ≫ inc.left = inc.left
        rw [Category.id_comp])
  let c : back.obj (Over.mk inc.left) ≅ j.hom.obj V₀ := c₀ ≪≫ eqToIso hjobj.symm
  have hc₀ : (schemeFibredCategory B S hS W).val.p.IsHomLift (𝟙 V) c₀.hom := by
    show (Over.forget W).IsHomLift (𝟙 V) c₀.hom
    refine IsHomLift.of_fac' _ _ _ hgx rfl ?_
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [c₀, back, Over.iteratedSliceBackward]
    rfl
  have h₁ : (schemeFibredCategory B S hS W).val.p.IsHomLift (𝟙 V) (eqToHom hjobj.symm) :=
    IsHomLift.eqToHom_domain_lift_id hjobj.symm rfl
  have hc : (schemeFibredCategory B S hS W).val.p.IsHomLift (𝟙 V) c.hom :=
    isHomLift_comp_id (schemeFibredCategory B S hS W).val.p c₀.hom (eqToHom hjobj.symm) hc₀ h₁
  have hc' : 𝒴.val.val.p.IsHomLift (𝟙 V) (y.hom.map c.hom) :=
    Functor.isHomLift_map_of_comp_eq y.hom.w (𝟙 V) c.hom
  let q : TwoFibreProductOver (Over.map W.hom) (inertia B S hS 𝒴.val).val.p 𝒴.val.val.p yf
      π.hom.toFunctor :=
    { base := V
      x := Over.mk inc.left
      y := A
      hx := hgx
      hy := hA
      iso := y.hom.toFunctor.mapIso c
      vertical := hc' }
  obtain ⟨q', θ, hv⟩ := exists_extension_in_represented_fiber B S hS π hI hrep
    inc R eW eV hinc yf hyf q rfl
  obtain ⟨qb, qx, qy, qhx, qhy, qiso, qvert⟩ := q'
  subst hv
  have hqb : W = qb := by
    change Over.mk (𝟙 W.left ≫ W.hom) = qb at qhx
    rw [Category.id_comp] at qhx
    exact (show Over.mk W.hom = W by cases W; rfl).symm.trans qhx
  subst hqb
  let T₀ : Over W := Over.mk (𝟙 W)
  let e : T₀ ≅ back.obj (Over.mk (𝟙 W.left)) :=
    Over.isoMk (Over.isoMk (Iso.refl W.left)
        (by simp [back, Over.iteratedSliceBackward, T₀])) (by
      apply Over.OverMorphism.ext
      simp [back, Over.iteratedSliceBackward, T₀]
      rfl)
  have he : (schemeFibredCategory B S hS W).val.p.IsHomLift (𝟙 W) e.hom := by
    show (Over.forget W).IsHomLift (𝟙 W) e.hom
    refine IsHomLift.of_fac' _ _ _ rfl ?_ ?_
    · show Over.mk (𝟙 W.left ≫ W.hom) = W
      rw [Category.id_comp]
      cases W
      rfl
    · apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      simp [e, T₀, back, Over.iteratedSliceBackward]
      rfl
  have hqv : 𝒴.val.val.p.IsHomLift (𝟙 W) qiso.hom := qvert
  have hqvinv : 𝒴.val.val.p.IsHomLift (𝟙 W) qiso.inv :=
    isHomLift_id_inv 𝒴.val.val.p qiso hqv
  let au : π.hom.obj qy ⟶ π.hom.obj qy := qy.auto.hom
  have hauto : 𝒴.val.val.p.IsHomLift (𝟙 W) au :=
    isHomLift_id_of_map_eq_id 𝒴.val.val.p au qy.cond qhy
  let E : y.hom.obj T₀ ≅ yf.obj (Over.mk (𝟙 W.left)) := y.hom.toFunctor.mapIso e
  have hE : 𝒴.val.val.p.IsHomLift (𝟙 W) E.hom :=
    Functor.isHomLift_map_of_comp_eq y.hom.w (𝟙 W) e.hom
  have hEinv : 𝒴.val.val.p.IsHomLift (𝟙 W) E.inv := isHomLift_id_inv 𝒴.val.val.p E hE
  have hδ₀ : 𝒴.val.val.p.IsHomLift (𝟙 W)
      (E.hom ≫ qiso.hom ≫ au ≫ qiso.inv ≫ E.inv) :=
    isHomLift_comp_id 𝒴.val.val.p _ _ hE
      (isHomLift_comp_id 𝒴.val.val.p _ _ hqv
        (isHomLift_comp_id 𝒴.val.val.p _ _ hauto
          (isHomLift_comp_id 𝒴.val.val.p _ _ hqvinv hEinv)))
  have ht : (Over.mkIdTerminal.from (j.hom.obj V₀) : j.hom.obj V₀ ⟶ T₀) ≫ e.hom =
      c.inv ≫ back.map θ.a :=
    (Iso.eq_comp_inv e).mp (Over.mkIdTerminal.hom_ext _ _)
  let cH : yf.obj (Over.mk inc.left) ⟶ y.hom.obj (j.hom.obj V₀) := y.hom.toFunctor.map c.hom
  let cI : y.hom.obj (j.hom.obj V₀) ⟶ yf.obj (Over.mk inc.left) := y.hom.toFunctor.map c.inv
  let aQ : yf.obj (Over.mk inc.left) ⟶ yf.obj (Over.mk (𝟙 W.left)) :=
    y.hom.toFunctor.map (back.map θ.a)
  let t : y.hom.obj (j.hom.obj V₀) ⟶ y.hom.obj T₀ :=
    y.hom.toFunctor.map (Over.mkIdTerminal.from (j.hom.obj V₀))
  let b : y.hom.obj (j.hom.obj V₀) ⟶ π.hom.obj qy := θ.b.hom
  let τ₀ : y.hom.obj (j.hom.obj V₀) ⟶ y.hom.obj (j.hom.obj V₀) := τ.hom.toNatTrans.app V₀
  have hDtDe : t ≫ E.hom = cI ≫ aQ :=
    ((y.hom.toFunctor.map_comp _ e.hom).symm.trans
      (congrArg y.hom.toFunctor.map ht)).trans
        (y.hom.toFunctor.map_comp c.inv (back.map θ.a))
  have hcc : cI ≫ cH = 𝟙 _ :=
    ((y.hom.toFunctor.map_comp c.inv c.hom).symm.trans
      (congrArg y.hom.toFunctor.map c.inv_hom_id)).trans (y.hom.toFunctor.map_id _)
  have hw : aQ ≫ qiso.hom = cH ≫ b := θ.w
  have hbcomm : b ≫ au = τ₀ ≫ b := θ.b.comm
  have hb : cI ≫ aQ ≫ qiso.hom = b := by rw [hw, reassoc_of% hcc]
  have hbt : b ≫ qiso.inv ≫ E.inv = t := by
    rw [← hb]
    simp [← reassoc_of% hDtDe]
  refine CatFiberedInGroupoids.exists_whiskerLeft_of_unitHom inc hj τ
    (E.hom ≫ qiso.hom ≫ au ≫ qiso.inv ≫ E.inv) hδ₀ (Eq.symm ?_)
  show t ≫ E.hom ≫ qiso.hom ≫ au ≫ qiso.inv ≫ E.inv = τ₀ ≫ t
  rw [← hbt]
  simp [reassoc_of% hbcomm]

end AlgebraicGeometry.Stack

end
