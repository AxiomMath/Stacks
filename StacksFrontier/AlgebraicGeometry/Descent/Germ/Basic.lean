module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Germs of schemes

A germ of a scheme is a scheme together with a distinguished point of its underlying
topological space. A morphism of germs is represented by a morphism defined on an open
neighbourhood of the distinguished source point which carries that point to the distinguished
target point; two representatives are identified when their restrictions agree on a smaller
open neighbourhood. Germs compose by restricting the first representative to the inverse
image of the domain of the second.

## Main definitions

* `AlgebraicGeometry.GermOfScheme` is a scheme equipped with a point.
* `AlgebraicGeometry.MorphismOfGerms.Representative` is a morphism defined on an open
  neighbourhood and preserving the distinguished point.
* `AlgebraicGeometry.MorphismOfGerms` is the quotient of such representatives by agreement
  near the distinguished point.
* `AlgebraicGeometry.MorphismOfGerms.comp` is composition of morphisms of germs.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.mk_eq_mk_iff` characterizes equality of represented
  morphisms by agreement on an open neighbourhood.
* `AlgebraicGeometry.MorphismOfGerms.lift` and `AlgebraicGeometry.MorphismOfGerms.inductionOn`
  give the quotient elimination principles used by constructions on morphisms of germs.
* `AlgebraicGeometry.MorphismOfGerms.comp_mk` computes the composite on representatives.

## Implementation notes

The pair in the source is represented by a dependent structure, so that the type of the
distinguished point records its scheme. Agreement is expressed after restricting both
morphisms to one common open neighbourhood; this relation is made into a setoid directly, so
the quotient has exactly the equivalence relation specified in the source. The domain of a
composite representative is the image in the original source scheme of the inverse image of
the second representative's domain, and the quotient lift is justified by restricting
representatives to the neighbourhoods on which they agree.

## References

* [Stacks Project, Tag 04QR](https://stacks.math.columbia.edu/tag/04QR)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A germ of a scheme is a scheme together with a distinguished point. -/
@[stacks 04QR "germ_of_scheme"]
structure GermOfScheme where
  /-- The scheme underlying the germ. -/
  scheme : Scheme.{u}
  /-- The distinguished point of the germ. -/
  point : scheme

namespace MorphismOfGerms

/-- A representative of a morphism of germs from `X` to `S`: a morphism from an open
neighbourhood of the distinguished point of `X` to the underlying scheme of `S`, carrying the
distinguished point to that of `S`. -/
structure Representative (X S : GermOfScheme.{u}) where
  /-- The open neighbourhood on which the representative is defined. -/
  source : X.scheme.Opens
  /-- The distinguished source point belongs to the domain. -/
  mem_source : X.point ∈ source
  /-- The morphism defined on the open neighbourhood. -/
  hom : source.toScheme ⟶ S.scheme
  /-- The morphism carries the distinguished source point to the distinguished target
  point. -/
  map_point : hom ⟨X.point, mem_source⟩ = S.point

/-- Two representatives agree near the distinguished source point when they agree after
restriction to some common open neighbourhood of that point. -/
def Representative.AgreeNear {X S : GermOfScheme.{u}} (f g : Representative X S) : Prop :=
  ∃ (U : X.scheme.Opens) (_hxU : X.point ∈ U)
      (hUf : U ≤ f.source) (hUg : U ≤ g.source),
    X.scheme.homOfLE hUf ≫ f.hom = X.scheme.homOfLE hUg ≫ g.hom

/-- Agreement near the distinguished point is an equivalence relation. -/
noncomputable def representativeSetoid (X S : GermOfScheme.{u}) :
    Setoid (Representative X S) where
  r := Representative.AgreeNear
  iseqv := {
    refl f := ⟨f.source, f.mem_source, le_rfl, le_rfl, rfl⟩
    symm := fun ⟨U, hxU, hUf, hUg, hfg⟩ ↦ ⟨U, hxU, hUg, hUf, hfg.symm⟩
    trans := by
      rintro f g h ⟨U, hxU, hUf, hUg, hfg⟩ ⟨V, hxV, hVg, hVh, hgh⟩
      refine ⟨U ⊓ V, ⟨hxU, hxV⟩, inf_le_left.trans hUf, inf_le_right.trans hVh, ?_⟩
      calc
        X.scheme.homOfLE (inf_le_left.trans hUf) ≫ f.hom =
            X.scheme.homOfLE inf_le_left ≫ (X.scheme.homOfLE hUf ≫ f.hom) := by simp
        _ = X.scheme.homOfLE inf_le_left ≫ (X.scheme.homOfLE hUg ≫ g.hom) := by rw [hfg]
        _ = X.scheme.homOfLE (inf_le_right.trans hVg) ≫ g.hom := by simp
        _ = X.scheme.homOfLE inf_le_right ≫ (X.scheme.homOfLE hVg ≫ g.hom) := by simp
        _ = X.scheme.homOfLE inf_le_right ≫ (X.scheme.homOfLE hVh ≫ h.hom) := by rw [hgh]
        _ = X.scheme.homOfLE (inf_le_right.trans hVh) ≫ h.hom := by simp }

end MorphismOfGerms

/-- A morphism of germs of schemes is a representative defined on an open neighbourhood of the
distinguished source point, modulo agreement on a possibly smaller such neighbourhood. -/
@[stacks 04QR "morphism_of_germs"]
noncomputable def MorphismOfGerms (X S : GermOfScheme.{u}) : Type u :=
  Quotient (MorphismOfGerms.representativeSetoid X S)

namespace MorphismOfGerms

/-- The morphism of germs represented by a neighbourhood morphism. -/
noncomputable def mk {X S : GermOfScheme.{u}} (f : Representative X S) :
    MorphismOfGerms X S :=
  Quotient.mk _ f

/-- Define a function on morphisms of germs from a function on representatives which is
invariant under agreement near the distinguished point. -/
noncomputable def lift {X S : GermOfScheme.{u}} {α : Sort*} (F : Representative X S → α)
    (hF : ∀ f g, f.AgreeNear g → F f = F g) : MorphismOfGerms X S → α :=
  Quotient.lift F hF

/-- Quotient lifting evaluates on a representative as the original function. -/
@[simp]
theorem lift_mk {X S : GermOfScheme.{u}} {α : Sort*} (F : Representative X S → α)
    (hF : ∀ f g, f.AgreeNear g → F f = F g) (f : Representative X S) :
    lift F hF (mk f) = F f :=
  rfl

/-- To prove a property of every morphism of germs, it suffices to prove it for the morphism
represented by each neighbourhood morphism. -/
protected theorem inductionOn {X S : GermOfScheme.{u}}
    {motive : MorphismOfGerms X S → Prop} (f : MorphismOfGerms X S)
    (h : ∀ g : Representative X S, motive (mk g)) : motive f :=
  Quotient.inductionOn f h

/-- Every morphism of germs has a representative on an open neighbourhood. -/
theorem exists_rep {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) :
    ∃ g : Representative X S, mk g = f :=
  Quotient.exists_rep f

/-- Two representatives determine the same morphism of germs exactly when they agree on some
open neighbourhood of the distinguished source point. -/
theorem mk_eq_mk_iff {X S : GermOfScheme.{u}} {f g : Representative X S} :
    mk f = mk g ↔ f.AgreeNear g :=
  Quotient.eq

/-- Restrict a representative to a smaller open neighbourhood of the distinguished source
point. -/
noncomputable def restrictRepresentative {X Y : GermOfScheme.{u}} (f : Representative X Y)
    (U : X.scheme.Opens) (hxU : X.point ∈ U) (hU : U ≤ f.source) : Representative X Y where
  source := U
  mem_source := hxU
  hom := X.scheme.homOfLE hU ≫ f.hom
  map_point := by
    change f.hom (X.scheme.homOfLE hU ⟨X.point, hxU⟩) = Y.point
    rw [show X.scheme.homOfLE hU ⟨X.point, hxU⟩ =
      ⟨X.point, f.mem_source⟩ from Subtype.ext (by simp)]
    exact f.map_point

/-- Compose two representatives after restricting the first representative to the inverse
image of the domain of the second. -/
noncomputable def compRepresentative {X Y Z : GermOfScheme.{u}} (f : Representative X Y)
    (g : Representative Y Z) : Representative X Z where
  source := f.source.ι ''ᵁ f.hom ⁻¹ᵁ g.source
  mem_source := by
    refine ⟨⟨X.point, f.mem_source⟩, ?_, rfl⟩
    change f.hom ⟨X.point, f.mem_source⟩ ∈ g.source
    simpa only [f.map_point] using g.mem_source
  hom := (f.source.ι.isoImage _).inv ≫ f.hom ∣_ g.source ≫ g.hom
  map_point := by
    change g.hom ((f.hom ∣_ g.source)
      ((f.source.ι.isoImage _).inv ⟨X.point, _⟩)) = Z.point
    calc
      _ = g.hom ⟨Y.point, g.mem_source⟩ := by
        apply congrArg (fun p : g.source.toScheme ↦ g.hom p)
        apply Subtype.ext
        change g.source.ι ((f.hom ∣_ g.source)
          ((f.source.ι.isoImage _).inv ⟨X.point, _⟩)) = Y.point
        rw [← f.map_point, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
        change (((f.source.ι.isoImage _).inv ≫
          (f.hom ⁻¹ᵁ g.source).ι ≫ f.hom) ⟨X.point, _⟩) = _
        rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
        change f.hom (X.scheme.homOfLE _ ⟨X.point, _⟩) =
          f.hom ⟨X.point, f.mem_source⟩
        apply congrArg (fun p : f.source.toScheme ↦ f.hom p)
        apply Subtype.ext
        simp
      _ = Z.point := g.map_point

/-- Two representatives with the same domain and compatible morphisms are equal. -/
theorem representative_ext_of_source_hom {X Y : GermOfScheme.{u}}
    {f g : Representative X Y} (hsource : f.source = g.source)
    (hhom : f.hom = (X.scheme.isoOfEq hsource).hom ≫ g.hom) : f = g := by
  cases f
  cases g
  cases hsource
  simp only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp] at hhom
  cases hhom
  rfl

/-- Equal representatives have morphisms identified along the equality of their domains. -/
theorem representative_hom_eq_of_eq {X Y : GermOfScheme.{u}}
    {f g : Representative X Y} (h : f = g) :
    f.hom = (X.scheme.isoOfEq (congrArg
      (fun r : Representative X Y ↦ r.source) h)).hom ≫ g.hom := by
  subst g
  simp

/-- Restrictions of two representatives to a common neighbourhood coincide when the restricted
morphisms agree. -/
private theorem restrictRepresentative_eq_of_hom_eq {X Y : GermOfScheme.{u}}
    {f g : Representative X Y} {U : X.scheme.Opens} (hxU : X.point ∈ U) (hUf : U ≤ f.source)
    (hUg : U ≤ g.source)
    (h : X.scheme.homOfLE hUf ≫ f.hom = X.scheme.homOfLE hUg ≫ g.hom) :
    restrictRepresentative f U hxU hUf = restrictRepresentative g U hxU hUg :=
  representative_ext_of_source_hom rfl
    (by simpa [restrictRepresentative, Scheme.isoOfEq_rfl] using h)

/-- Composing a restricted representative agrees with restricting the composite. -/
theorem compRepresentative_restrict_left {X Y Z : GermOfScheme.{u}}
    (f : Representative X Y) (U : X.scheme.Opens) (hxU : X.point ∈ U) (hU : U ≤ f.source)
    (g : Representative Y Z) :
    compRepresentative (restrictRepresentative f U hxU hU) g =
      restrictRepresentative (compRepresentative f g)
        (compRepresentative (restrictRepresentative f U hxU hU) g).source
        (compRepresentative (restrictRepresentative f U hxU hU) g).mem_source
        (by
          change U.ι ''ᵁ ((X.scheme.homOfLE hU ≫ f.hom) ⁻¹ᵁ g.source) ≤ _
          rw [Scheme.Hom.comp_preimage]
          exact X.scheme.ι_image_homOfLE_le_ι_image hU _ ) := by
  refine representative_ext_of_source_hom rfl ?_
  simp [compRepresentative, restrictRepresentative, morphismRestrict_comp,
    isoImage_ι_inv_morphismRestrict_homOfLE_assoc]

/-- Composing with a restricted representative agrees with restricting the composite. -/
theorem compRepresentative_restrict_right {X Y Z : GermOfScheme.{u}}
    (f : Representative X Y) (g : Representative Y Z) (V : Y.scheme.Opens)
    (hyV : Y.point ∈ V) (hV : V ≤ g.source) :
    compRepresentative f (restrictRepresentative g V hyV hV) =
      restrictRepresentative (compRepresentative f g) (f.source.ι ''ᵁ (f.hom ⁻¹ᵁ V))
        (by
          refine ⟨⟨X.point, f.mem_source⟩, ?_, rfl⟩
          change f.hom ⟨X.point, f.mem_source⟩ ∈ V
          simpa only [f.map_point] using hyV)
        (f.source.ι.image_mono (f.hom.preimage_mono hV)) := by
  apply representative_ext_of_source_hom
  · simp [compRepresentative, restrictRepresentative, Scheme.isoOfEq_rfl,
      ← f.source.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV]
  · rfl

/-- Representatives whose restrictions to neighbourhoods coincide agree near the
distinguished point. -/
theorem agreeNear_of_restrict_eq {X Y : GermOfScheme.{u}} (f g : Representative X Y)
    (U V : X.scheme.Opens) (hxU : X.point ∈ U) (hxV : X.point ∈ V)
    (hUf : U ≤ f.source) (hVg : V ≤ g.source)
    (h : restrictRepresentative f U hxU hUf =
      restrictRepresentative g V hxV hVg) : f.AgreeNear g := by
  have hUV : U = V := congrArg (fun r : Representative X Y ↦ r.source) h
  have hh := representative_hom_eq_of_eq h
  subst V
  exact ⟨U, hxU, hUf, hVg, by simpa [restrictRepresentative, Scheme.isoOfEq_rfl] using hh⟩

/-- Composition of representatives respects agreement near the distinguished points. -/
theorem compRepresentative_agreeNear {X Y Z : GermOfScheme.{u}}
    (f₁ f₂ : Representative X Y) (hf : f₁.AgreeNear f₂)
    (g₁ g₂ : Representative Y Z) (hg : g₁.AgreeNear g₂) :
    (compRepresentative f₁ g₁).AgreeNear (compRepresentative f₂ g₂) := by
  obtain ⟨U, hxU, hUf₁, hUf₂, hf⟩ := hf
  obtain ⟨V, hyV, hVg₁, hVg₂, hg⟩ := hg
  have ef := restrictRepresentative_eq_of_hom_eq hxU hUf₁ hUf₂ hf
  have eg := restrictRepresentative_eq_of_hom_eq hyV hVg₁ hVg₂ hg
  have hleft' : (compRepresentative f₁ g₁).AgreeNear
      (compRepresentative f₂ g₁) :=
    agreeNear_of_restrict_eq _ _ _ _ _ _ _ _
      ((compRepresentative_restrict_left f₁ U hxU hUf₁ g₁).symm.trans
        ((congrArg (fun f ↦ compRepresentative f g₁) ef).trans
          (compRepresentative_restrict_left f₂ U hxU hUf₂ g₁)))
  have hright' : (compRepresentative f₂ g₁).AgreeNear
      (compRepresentative f₂ g₂) :=
    agreeNear_of_restrict_eq _ _ _ _ _ _ _ _ (by
      simpa only [compRepresentative_restrict_right] using
        congrArg (fun g ↦ compRepresentative f₂ g) eg)
  exact (representativeSetoid X Z).iseqv.trans hleft' hright'

/-- Composition of morphisms of germs, obtained by composing representatives after restricting
the first one to the inverse image of the domain of the second. -/
@[stacks 04QR "composition_of_germs", implicit_reducible]
noncomputable def comp {X Y Z : GermOfScheme.{u}} :
    MorphismOfGerms X Y → MorphismOfGerms Y Z → MorphismOfGerms X Z :=
  Quotient.lift₂ (fun f g ↦ mk (compRepresentative f g))
    (fun f₁ g₁ f₂ g₂ hf hg ↦
      mk_eq_mk_iff.mpr (compRepresentative_agreeNear f₁ f₂ hf g₁ g₂ hg))

/-- Composition is represented by the composite of representatives on the inverse image
neighbourhood. -/
@[simp]
theorem comp_mk {X Y Z : GermOfScheme.{u}} (f : Representative X Y) (g : Representative Y Z) :
    comp (mk f) (mk g) = mk (compRepresentative f g) :=
  rfl

end MorphismOfGerms

end AlgebraicGeometry
