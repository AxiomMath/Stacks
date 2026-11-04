module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Morphisms constant on the fibres of a contraction

Let `f : X ⟶ Y` be a morphism of schemes which is a closed surjection and for which
`𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, that is, `f` is an isomorphism on the sections over every
open of `Y`. Then `f` is an epimorphism of schemes, and a morphism
`g : X ⟶ Z` factors (uniquely) through `f` as soon as it is constant on the fibres of `f`.
Consequently two such morphisms out of `X` with the same fibres differ by a unique isomorphism.

This is how a contraction is determined by the set of points it identifies: a morphism of
schemes is a continuous map together with a map of sheaves of rings, and both descend along
`f`, the first because a closed surjection is a quotient map and the second because
`𝒪_Y = f_*𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.descOfConstantOnFibres`: the factorization of `g` through `f`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fac_descOfConstantOnFibres`: `f ≫ descOfConstantOnFibres = g`.
* `AlgebraicGeometry.Scheme.Hom.ext_of_comp_eq_comp`: `f` is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_comp_eq_of_constantOnFibres`: unique factorization.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_iso_of_fibres_eq`: two such morphisms with the same
  fibres differ by a unique isomorphism.

## Implementation notes

The descended map of sheaves on an open `U` of `Z` is `g` on sections over `U` followed by the
inverse of `f` on sections over the preimage of `U` in `Y`. Locality on stalks is inherited
from `g`: at `y = f x` the stalk map of `g` at `x` is the stalk map of the descended morphism at
`y` followed by the local stalk map of `f` at `x`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z)

/-- Two restriction maps of the structure sheaf composing to a map from an open to itself
compose to the identity. -/
theorem presheaf_map_comp_presheaf_map_eq_id {T : Scheme.{u}} {A B : T.Opens} (a : op A ⟶ op B)
    (b : op B ⟶ op A) : T.presheaf.map a ≫ T.presheaf.map b = 𝟙 _ := by
  rw [← Functor.map_comp]
  exact (congrArg T.presheaf.map (Subsingleton.elim _ _)).trans (T.presheaf.map_id _)

/-- Precomposing a round trip of restriction maps of the structure sheaf changes nothing. -/
private theorem comp_presheaf_map_comp_presheaf_map {T : Scheme.{u}} {A B : T.Opens}
    {W : CommRingCat.{u}} (k : W ⟶ T.presheaf.obj (op A)) (a : op A ⟶ op B) (b : op B ⟶ op A) :
    k ≫ T.presheaf.map a ≫ T.presheaf.map b = k :=
  (congrArg (k ≫ ·) (presheaf_map_comp_presheaf_map_eq_id a b)).trans (Category.comp_id _)

section Desc

variable (hf : IsClosedMap f.base) [Surjective f]
  (hg : ∀ x x' : X, f.base x = f.base x' → g.base x = g.base x')

/-- The continuous map through which a map constant on the fibres of a closed surjection
factors. -/
def descBaseOfConstantOnFibres : Y.toPresheafedSpace.carrier ⟶ Z.toPresheafedSpace.carrier :=
  TopCat.ofHom ((hf.isQuotientMap f.base.hom.continuous f.surjective).lift g.base.hom
    fun _ _ h ↦ hg _ _ h)

/-- The descended continuous map composed with `f` is the underlying map of `g`. -/
theorem fac_descBaseOfConstantOnFibres : f.base ≫ descBaseOfConstantOnFibres f g hf hg = g.base :=
  TopCat.hom_ext (Topology.IsQuotientMap.lift_comp _ _ _)

/-- The preimage of an open along the descended map, pulled back to `X`, is its preimage
along `g`. -/
theorem preimage_descBaseOfConstantOnFibres (U : Z.Opens) :
    f ⁻¹ᵁ (Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U = g ⁻¹ᵁ U :=
  congrArg (fun φ ↦ (Opens.map φ).obj U) (fac_descBaseOfConstantOnFibres f g hf hg)

variable (hiso : ∀ U : Y.Opens, IsIso (f.app U))

/-- The descended map on sections over an open of `Z`. -/
def descAppOfConstantOnFibres (U : Z.Opens) :
    Γ(Z, U) ⟶ Γ(Y, (Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U) :=
  haveI := hiso ((Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U)
  g.app U ≫ X.presheaf.map (eqToHom (preimage_descBaseOfConstantOnFibres f g hf hg U)).op ≫
    inv (f.app _)

/-- The descended map on sections over `U` followed by `f` on sections is `g` on sections over
`U`, up to the identification of the preimages of `U` in `X`. -/
@[reassoc]
theorem descAppOfConstantOnFibres_comp_app (U : Z.Opens) :
    descAppOfConstantOnFibres f g hf hg hiso U ≫ f.app _ =
      g.app U ≫ X.presheaf.map (eqToHom (preimage_descBaseOfConstantOnFibres f g hf hg U)).op := by
  have := hiso ((Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U)
  simp [descAppOfConstantOnFibres]

/-- The descended map of structure sheaves. -/
def descCOfConstantOnFibres :
    Z.presheaf ⟶ (descBaseOfConstantOnFibres f g hf hg) _* Y.presheaf where
  app U := descAppOfConstantOnFibres f g hf hg hiso U.unop
  naturality U U' i := by
    have := hiso ((Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U'.unop)
    change Z.presheaf.map i ≫ descAppOfConstantOnFibres f g hf hg hiso U'.unop =
      descAppOfConstantOnFibres f g hf hg hiso U.unop ≫
        Y.presheaf.map ((Opens.map (descBaseOfConstantOnFibres f g hf hg)).map i.unop).op
    rw [← cancel_mono (f.app ((Opens.map (descBaseOfConstantOnFibres f g hf hg)).obj U'.unop)),
      Category.assoc, descAppOfConstantOnFibres_comp_app, Category.assoc, f.naturality,
      descAppOfConstantOnFibres_comp_app_assoc, g.naturality_assoc]
    refine congrArg (g.app U.unop ≫ ·) ?_
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The descended morphism of presheafed spaces. -/
def descPshHomOfConstantOnFibres : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace where
  base := descBaseOfConstantOnFibres f g hf hg
  c := descCOfConstantOnFibres f g hf hg hiso

/-- The descended morphism of presheafed spaces composed with `f` is `g`. -/
theorem toPshHom_comp_descPshHomOfConstantOnFibres :
    f.toPshHom ≫ descPshHomOfConstantOnFibres f g hf hg hiso = g.toPshHom := by
  refine PresheafedSpace.Hom.ext _ _ (fac_descBaseOfConstantOnFibres f g hf hg) ?_
  refine NatTrans.ext (funext fun U ↦ ?_)
  show descAppOfConstantOnFibres f g hf hg hiso U.unop ≫ f.app _ ≫ X.presheaf.map _ =
    g.app U.unop
  rw [descAppOfConstantOnFibres_comp_app_assoc]
  exact comp_presheaf_map_comp_presheaf_map _ _ _

/-- The stalk maps of the descended morphism of presheafed spaces are local. -/
theorem isLocalHom_stalkMap_descPshHomOfConstantOnFibres (y : Y) :
    IsLocalHom ((descPshHomOfConstantOnFibres f g hf hg hiso).stalkMap y).hom := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have key : ∀ φ : X.toPresheafedSpace ⟶ Z.toPresheafedSpace, φ = g.toPshHom →
      IsLocalHom (φ.stalkMap x).hom := by
    rintro φ rfl
    exact g.prop x
  have h := key _ (toPshHom_comp_descPshHomOfConstantOnFibres f g hf hg hiso)
  have hc :=
    PresheafedSpace.stalkMap.comp f.toPshHom (descPshHomOfConstantOnFibres f g hf hg hiso) x
  have h' : IsLocalHom ((f.toPshHom.stalkMap x).hom.comp
      ((descPshHomOfConstantOnFibres f g hf hg hiso).stalkMap (f.base x)).hom) := by
    rw [← CommRingCat.hom_comp, ← hc]
    exact h
  exact isLocalHom_of_comp _ (f.toPshHom.stalkMap x).hom

/-- **Descent along a contraction.** If `f` is a closed surjection with `𝒪_Y ≅ f_*𝒪_X` and `g`
is constant on the fibres of `f`, the morphism `Y ⟶ Z` through which `g` factors. -/
def descOfConstantOnFibres : Y ⟶ Z where
  __ := descPshHomOfConstantOnFibres f g hf hg hiso
  prop := isLocalHom_stalkMap_descPshHomOfConstantOnFibres f g hf hg hiso

/-- The descended morphism of schemes composed with `f` is `g`. -/
theorem fac_descOfConstantOnFibres : f ≫ descOfConstantOnFibres f g hf hg hiso = g := by
  refine Scheme.Hom.ext (fac_descBaseOfConstantOnFibres f g hf hg) fun U ↦ ?_
  show (descAppOfConstantOnFibres f g hf hg hiso U ≫ f.app _) ≫ _ = _
  rw [descAppOfConstantOnFibres_comp_app]
  exact (Category.assoc _ _ _).trans (comp_presheaf_map_comp_presheaf_map _ _ _)

end Desc

/-- A surjective morphism which is an isomorphism on all sections is an epimorphism. -/
theorem ext_of_comp_eq_comp [Surjective f] (hiso : ∀ U : Y.Opens, IsIso (f.app U))
    {h₁ h₂ : Y ⟶ Z} (e : f ≫ h₁ = f ≫ h₂) : h₁ = h₂ := by
  have hbase : h₁.base = h₂.base := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact congrArg (fun φ : X ⟶ Z ↦ φ.base x) e
  refine Scheme.Hom.ext hbase fun U ↦ ?_
  have := hiso (h₂ ⁻¹ᵁ U)
  have e' := Scheme.Hom.congr_app e U
  simp only [Scheme.Hom.comp_app] at e'
  rw [← cancel_mono (f.app (h₂ ⁻¹ᵁ U)), Category.assoc, f.naturality, reassoc_of% e']
  exact comp_presheaf_map_comp_presheaf_map (h₂.app U ≫ f.app (h₂ ⁻¹ᵁ U)) _ _

/-- **Unique factorization through a contraction.** Let `f` be a closed surjection which is an
isomorphism on all sections. A morphism constant on the fibres of `f` factors uniquely
through `f`. -/
theorem existsUnique_comp_eq_of_constantOnFibres (hf : IsClosedMap f.base) [Surjective f]
    (hiso : ∀ U : Y.Opens, IsIso (f.app U))
    (hg : ∀ x x' : X, f.base x = f.base x' → g.base x = g.base x') :
    ∃! h : Y ⟶ Z, f ≫ h = g :=
  ⟨descOfConstantOnFibres f g hf hg hiso, fac_descOfConstantOnFibres f g hf hg hiso,
    fun _ hh ↦ ext_of_comp_eq_comp f hiso
      (hh.trans (fac_descOfConstantOnFibres f g hf hg hiso).symm)⟩

/-- **Two contractions with the same fibres are uniquely isomorphic.** Let `f₁ : X ⟶ Y₁` and
`f₂ : X ⟶ Y₂` be closed surjections which are isomorphisms on all sections. If they identify
the same pairs of points of `X`, there is a unique isomorphism `e : Y₁ ≅ Y₂` with
`f₁ ≫ e.hom = f₂`. -/
theorem existsUnique_iso_of_fibres_eq {Y₁ Y₂ : Scheme.{u}} (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂)
    (hf₁ : IsClosedMap f₁.base) (hf₂ : IsClosedMap f₂.base) [Surjective f₁] [Surjective f₂]
    (hiso₁ : ∀ U : Y₁.Opens, IsIso (f₁.app U)) (hiso₂ : ∀ U : Y₂.Opens, IsIso (f₂.app U))
    (hfib : ∀ x x' : X, f₁.base x = f₁.base x' ↔ f₂.base x = f₂.base x') :
    ∃! e : Y₁ ≅ Y₂, f₁ ≫ e.hom = f₂ := by
  let a := descOfConstantOnFibres f₁ f₂ hf₁ (fun x x' ↦ (hfib x x').1) hiso₁
  let b := descOfConstantOnFibres f₂ f₁ hf₂ (fun x x' ↦ (hfib x x').2) hiso₂
  have ha : f₁ ≫ a = f₂ := fac_descOfConstantOnFibres _ _ _ _ _
  have hb : f₂ ≫ b = f₁ := fac_descOfConstantOnFibres _ _ _ _ _
  refine ⟨⟨a, b, ?_, ?_⟩, ha, fun e he ↦ Iso.ext (ext_of_comp_eq_comp f₁ hiso₁ (he.trans ha.symm))⟩
  · exact ext_of_comp_eq_comp f₁ hiso₁ (by rw [reassoc_of% ha, hb, Category.comp_id])
  · exact ext_of_comp_eq_comp f₂ hiso₂ (by rw [reassoc_of% hb, ha, Category.comp_id])

end AlgebraicGeometry.Scheme.Hom
