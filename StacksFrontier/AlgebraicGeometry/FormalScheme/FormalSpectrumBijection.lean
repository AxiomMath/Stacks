module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumMapLTRS
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of formal spectra and continuous ring maps

A continuous homomorphism `φ : A → B` of pre-admissible topological rings is recovered from the
morphism `Spf φ : Spf B → Spf A` of locally topologically ringed spaces it induces: the map that
`Spf φ` induces on global sections is `φ` read through the canonical maps
`A → Γ(Spf A, 𝒪_{Spf A})` and `B → Γ(Spf B, 𝒪_{Spf B})`. When `B` is separated and linearly
topologized the second of those maps is injective, so `φ ↦ Spf φ` is injective.

## Main definitions

* `AlgebraicGeometry.ltrsGlobalSectionsMap`: the map a morphism of locally topologically ringed
  spaces induces on global sections.
* `AlgebraicGeometry.spfPresheafObjIsoOn`: the sections of `𝒪_{Spf A} = lim 𝒪_λ` over an open set
  are the limit of the sections of the `𝒪_λ` there.
* `AlgebraicGeometry.spfMapGammaHom` and `AlgebraicGeometry.spfComponentGammaMap`: the maps on
  global sections induced by `Spf φ` and by its component `𝒪^A_I → (Spf φ)_* 𝒪^B_J`.
* `AlgebraicGeometry.spfLTRSMap`: the map sending a continuous ring homomorphism `A → B` to the
  morphism `Spf B → Spf A` of locally topologically ringed spaces it induces.

## Main results

* `AlgebraicGeometry.spfPresheafOn_obj_hom_ext`: two maps into the sections of `𝒪_{Spf A}` over an
  open set agree as soon as they agree in every term `𝒪_λ` of the inverse system.
* `AlgebraicGeometry.spfGammaHom_comp_spfProjection_app_top`: the canonical map
  `A → Γ(Spf A, 𝒪_{Spf A})` followed by the projection onto the global sections of `𝒪_λ` is the
  component `A → A/I_λ ≅ Γ(Spec (A/I_λ), 𝒪)` of the canonical map.
* `AlgebraicGeometry.spfGammaHom_comp_spfMapGammaHom`: the canonical maps into global sections
  turn `Spf φ` back into `φ`.
* `AlgebraicGeometry.injective_spfGammaHom`: for a separated, linearly topologized,
  pre-admissible ring the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` is injective.
* `AlgebraicGeometry.injective_spfLTRSMap` is one half of Stacks 0AHZ: the map taking a
  continuous ring homomorphism `A → B` to the induced morphism of formal spectra is injective.
* `AlgebraicGeometry.isUnit_germ_spfGammaHomOn_iff`: an element of `A` lies outside an open prime
  `x` exactly when its image in the local ring of `𝒪_{Spf A}` at `x` is invertible. The point `x`
  is therefore read off from that local ring together with the canonical map into global
  sections, just as a point of `Spec R` is read off from `R → 𝒪_{Spec R, x}`.
* `AlgebraicGeometry.notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn` and
  `AlgebraicGeometry.base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn`: the image of a point under a
  morphism `X → Spf A` of locally topologically ringed spaces is recovered from the map that
  morphism induces on global sections, so two such morphisms that agree on global sections have
  the same underlying continuous map. This is the base-map half of the identification of Stacks
  0AHZ.

## Implementation notes

The canonical map `A → Γ(Spf A, 𝒪_{Spf A})` is injective under separatedness alone: its
component at an ideal of definition `I_λ` is the quotient map `A → A/I_λ`, and in a separated
linearly topologized pre-admissible ring the ideals of definition intersect in zero, which is
`TopologicalRing.eq_zero_of_mem_isIdealOfDefinition`. Surjectivity — equivalently, the source's
identification `Γ(Spf A, 𝒪_{Spf A}) = A` — is where completeness of `A` would enter, through
`TopologicalRing.exists_ringEquiv_idealOfDefinitionLimit`; it is not used here.

Only the base-map half of the identification of Stacks 0AHZ is proved below, and the
identification itself cannot be stated in this module. Reading a continuous homomorphism
`A → B` off a morphism `Spf B → Spf A` needs the inverse of `B → Γ(Spf B, 𝒪_{Spf B})`, which is
`AlgebraicGeometry.spfGammaEquiv` in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso` — a module that
imports this one. Recovering the comparison map of sheaves as well would need, in addition, that
a map out of `𝒪_{Spf A} = lim 𝒪_λ` into a pseudo-discrete sheaf on a quasi-compact space factor
through a single term `𝒪_λ`, which is not available yet.

Three of the definitions below record a map that already exists, with its source and target
spelled as rings of sections of `𝒪_{Spf A}` and of the `𝒪_λ` over the whole space. They are not
cosmetic. The comparison map of a morphism of presheafed spaces has as its target the sections
over the *preimage* of an open set, which for the whole space is only definitionally the whole
space; and the sections of `𝒪_{Spf A}` over an open set are the sections of a limit, not visibly
a limit of sections. Without the one spelling of each object that these names fix, the map on
global sections is not even a function of the morphism alone.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-- The map a morphism of locally topologically ringed spaces induces on global sections: the
component of its comparison map at the whole space. -/
def ltrsGlobalSectionsMap {X Y : LTRS.{u}} (g : X ⟶ Y) :
    Y.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤) :=
  g.toHom.c.app (op ⊤)

/-! ### The components of the canonical map into global sections -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The sections of `lim 𝒪_λ`, the structure presheaf of the formal spectrum taken along a weak
ideal system `P`, over an open set are the limit of the sections of the `𝒪_λ` over that set,
limits of presheaves being computed objectwise. -/
noncomputable def spfPresheafObjIsoOn (P : Ideal A → Prop) [IsWeakIdealSystem A P]
    (U : Opens (spfSpace A)) :
    (spfPresheafOn A P).obj (op U) ≅ limit ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
      (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) :=
  limitObjIsoLimitCompEvaluation (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) (op U)

/-- The sections of `𝒪_{Spf A} = lim 𝒪_λ` over an open set are the limit of the sections of the
`𝒪_λ` over that set, limits of presheaves being computed objectwise.

The ideals-of-definition case of `spfPresheafObjIsoOn`. -/
@[reducible] noncomputable def spfPresheafObjIso (U : Opens (spfSpace A)) :
    (spfPresheaf A).obj (op U) ≅ limit ((spfDiagram A ⋙ pseudoDiscreteFunctor) ⋙
      (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) :=
  spfPresheafObjIsoOn (A := A) (P := IsIdealOfDefinition) (U := U)

/-- Under the identification of the sections with a limit, the projection onto the `λ`-th factor
is the projection onto `𝒪_λ`. -/
theorem spfPresheafObjIsoOn_hom_π (U : Opens (spfSpace A)) (I : SpfIndex A P) :
    (spfPresheafObjIsoOn A P U).hom ≫ limit.π ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) I
      = (spfProjectionOn A I).app (op U) :=
  limitObjIsoLimitCompEvaluation_hom_π (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) I (op U)

/-- Under the identification of the sections of `𝒪_{Spf A}` with a limit, the projection onto
the `λ`-th factor is the projection of `𝒪_{Spf A}` onto `𝒪_λ`.

The ideals-of-definition case of `spfPresheafObjIsoOn_hom_π`. -/
theorem spfPresheafObjIso_hom_π (U : Opens (spfSpace A)) (I : IdealsOfDefinition A) :
    (spfPresheafObjIso A U).hom ≫ limit.π ((spfDiagram A ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) I
      = (spfProjection A I).app (op U) :=
  spfPresheafObjIsoOn_hom_π (A := A) (P := IsIdealOfDefinition) (U := U) (I := I)

/-- The inverse identification of the sections with a limit, followed by the projection onto
`𝒪_λ`, is the projection onto the `λ`-th factor. -/
theorem spfPresheafObjIsoOn_inv_spfProjectionOn_app (U : Opens (spfSpace A))
    (I : SpfIndex A P) :
    (spfPresheafObjIsoOn A P U).inv ≫ (spfProjectionOn A I).app (op U)
      = limit.π ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
          (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) I :=
  limitObjIsoLimitCompEvaluation_inv_π_app (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) I (op U)

/-- The inverse identification of the sections of `𝒪_{Spf A}` with a limit, followed by the
projection of `𝒪_{Spf A}` onto `𝒪_λ`, is the projection onto the `λ`-th factor.

The ideals-of-definition case of `spfPresheafObjIsoOn_inv_spfProjectionOn_app`. -/
theorem spfPresheafObjIso_inv_spfProjection_app (U : Opens (spfSpace A))
    (I : IdealsOfDefinition A) :
    (spfPresheafObjIso A U).inv ≫ (spfProjection A I).app (op U)
      = limit.π ((spfDiagram A ⋙ pseudoDiscreteFunctor) ⋙
          (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op U)) I :=
  spfPresheafObjIsoOn_inv_spfProjectionOn_app (A := A) (P := IsIdealOfDefinition) (U := U) (I := I)

/-- Two maps into the sections of `lim 𝒪_λ` over an open set agree as soon as their images in
every term `𝒪_λ` of the inverse system agree. -/
theorem spfPresheafOn_obj_hom_ext {R : TopCommRingCat.{u}} {U : Opens (spfSpace A)}
    {f g : R ⟶ (spfPresheafOn A P).obj (op U)}
    (h : ∀ I : SpfIndex A P,
      f ≫ (spfProjectionOn A I).app (op U) = g ≫ (spfProjectionOn A I).app (op U)) :
    f = g := by
  refine (cancel_mono (spfPresheafObjIsoOn A P U).hom).1 (limit.hom_ext fun I => ?_)
  rw [Category.assoc, Category.assoc, spfPresheafObjIsoOn_hom_π]
  exact h I

/-- Two maps into the sections of `𝒪_{Spf A} = lim 𝒪_λ` over an open set agree as soon as their
images in every term `𝒪_λ` of the inverse system agree.

The ideals-of-definition case of `spfPresheafOn_obj_hom_ext`. -/
theorem spfPresheaf_obj_hom_ext {R : TopCommRingCat.{u}} {U : Opens (spfSpace A)}
    {f g : R ⟶ (spfPresheaf A).obj (op U)}
    (h : ∀ I : IdealsOfDefinition A,
      f ≫ (spfProjection A I).app (op U) = g ≫ (spfProjection A I).app (op U)) :
    f = g :=
  spfPresheafOn_obj_hom_ext (A := A) (P := IsIdealOfDefinition) (R := R) (U := U) (f := f) (g := g)
    (h := h)

/-- The canonical map `A → Γ(lim 𝒪_λ)` followed by the projection onto the global sections of the
term `𝒪_λ` is the component `A → A/I_λ ≅ Γ(Spec (A/I_λ), 𝒪)` of the canonical map. -/
theorem spfGammaHomOn_comp_spfProjection_app_top (I : SpfIndex A P) :
    spfGammaHomOn A P ≫ (spfProjectionOn A I).app (op ⊤) = spfGammaComponentOn A I := by
  show limit.lift ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op ⊤)) (spfGammaConeOn A P)
      ≫ (spfPresheafObjIsoOn A P ⊤).inv ≫ (spfProjectionOn A I).app (op ⊤)
    = spfGammaComponentOn A I
  rw [spfPresheafObjIsoOn_inv_spfProjectionOn_app]
  exact limit.lift_π (spfGammaConeOn A P) I

/-- The canonical map `A → Γ(Spf A, 𝒪_{Spf A})` followed by the projection onto the global
sections of the term `𝒪_λ` is the component `A → A/I_λ ≅ Γ(Spec (A/I_λ), 𝒪)` of the canonical
map. -/
theorem spfGammaHom_comp_spfProjection_app_top (I : IdealsOfDefinition A) :
    spfGammaHom A ≫ (spfProjection A I).app (op ⊤) = spfGammaComponent A I :=
  spfGammaHomOn_comp_spfProjection_app_top A I

/-- If a local homomorphism sends `x` to `y`, then `x` is a unit exactly when `y` is. -/
private theorem isUnit_iff_of_map_eq {R S F : Type*} [Monoid R] [Monoid S] [FunLike F R S]
    [MonoidHomClass F R S] (f : F) [IsLocalHom f] {x : R} {y : S} (h : f x = y) :
    IsUnit x ↔ IsUnit y :=
  h ▸ (isUnit_map_iff f x).symm

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The component of the canonical map at a member `I` of the family, followed by the
identification of `Γ(Spec (A/I), 𝒪)` with `A/I`, is the quotient map `A → A/I`. -/
theorem spfGammaComponentHomOn_comp_ΓSpecIso_hom (I : SpfIndex A P) :
    spfGammaComponentHomOn A I ≫ (Scheme.ΓSpecIso (spfQuotientOn A I)).hom
      = CommRingCat.ofHom (Ideal.Quotient.mk I.1) := by
  rw [spfGammaComponentHomOn, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [IsTopologicalRing A] in
/-- The component of the canonical map at an ideal of definition `I`, followed by the
identification of `Γ(Spec (A/I), 𝒪)` with `A/I`, is the quotient map `A → A/I`.

The ideals-of-definition case of `spfGammaComponentHomOn_comp_ΓSpecIso_hom`. -/
theorem spfGammaComponentHom_comp_ΓSpecIso_hom (I : IdealsOfDefinition A) :
    spfGammaComponentHom A I ≫ (Scheme.ΓSpecIso (spfQuotient A I)).hom
      = CommRingCat.ofHom (Ideal.Quotient.mk I.1) :=
  spfGammaComponentHomOn_comp_ΓSpecIso_hom (A := A) (P := IsIdealOfDefinition) (I := I)

variable (P) in
/-- **For a separated ring the canonical map into the global sections of the formal spectrum
taken along a fundamental system of ideals is injective.** Its component at a member `I` of the
system is the quotient map `A → A/I`, and the members of a fundamental system of ideals of a
separated ring intersect in zero. Completeness of `A`, which is what makes the map surjective as
well, is not needed.

Both the ideals of definition of an admissible ring and the weak ideals of definition of a weakly
admissible one are such a system, so this covers the injectivity half of Stacks 0AHY and of its
counterpart in McQuillan's setting. -/
theorem injective_spfGammaHomOn [T2Space A] (h : IsFundamentalIdealSystem A P) :
    Function.Injective (spfGammaHomOn A P).1 := by
  intro a b hab
  refine sub_eq_zero.mp (h.eq_zero_of_forall_mem fun I hI => ?_)
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp ?_
  have key : ∀ c : A, (Scheme.ΓSpecIso (spfQuotientOn A ⟨I, hI⟩)).hom.hom
      (((spfProjectionOn A ⟨I, hI⟩).app (op ⊤)).1 ((spfGammaHomOn A P).1 c))
      = Ideal.Quotient.mk I c := by
    intro c
    have h1 : ((spfProjectionOn A ⟨I, hI⟩).app (op ⊤)).1 ((spfGammaHomOn A P).1 c)
        = (spfGammaComponentOn A ⟨I, hI⟩).1 c :=
      congrArg (fun k : TopCommRingCat.of A ⟶
          (pseudoDiscrete (spfComponentOn A ⟨I, hI⟩)).obj (op ⊤) => k.1 c)
        (spfGammaHomOn_comp_spfProjection_app_top A ⟨I, hI⟩)
    rw [h1]
    exact congrArg (fun k : CommRingCat.of A ⟶ spfQuotientOn A ⟨I, hI⟩ => k.hom c)
      (spfGammaComponentHomOn_comp_ΓSpecIso_hom A ⟨I, hI⟩)
  rw [← key a, ← key b, hab]

/-- For a separated, linearly topologized, pre-admissible topological ring the canonical map
`A → Γ(Spf A, 𝒪_{Spf A})` is injective. -/
theorem injective_spfGammaHom [IsLinearTopology A A] [T2Space A] (hA : IsPreAdmissible A) :
    Function.Injective (spfGammaHom A).1 :=
  injective_spfGammaHomOn A IsIdealOfDefinition
    (isFundamentalIdealSystem_isIdealOfDefinition hA)

/-- **The counterpart of the injectivity half of Stacks 0AHY in McQuillan's setting**: for a
weakly admissible topological ring the canonical map `A → Γ(Spfw A, 𝒪)` into the global sections
of the formal spectrum taken along the *weak* ideals of definition is injective. -/
theorem injective_spfwGammaHom [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    Function.Injective (spfGammaHomOn A IsWeakIdealOfDefinition).1 :=
  have := hA.2.2
  injective_spfGammaHomOn A IsWeakIdealOfDefinition
    (isFundamentalIdealSystem_isWeakIdealOfDefinition hA)

end

/-! ### The formal spectrum of a continuous ring map recovers the map -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {φ : A →+* B} (hφ : Continuous φ)

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- The component of the canonical map of `A` at an ideal of definition `I`, followed by the map
on global sections induced by `Spec (B/J) → Spec (A/I)`, is `φ` followed by the component of the
canonical map of `B` at `J`: both are `A → B → B/J ≅ Γ(Spec (B/J), 𝒪)`, because `A → A/I → B/J`
is `A → B → B/J`. -/
theorem spfGammaComponentHom_comp_appTop (J : IdealsOfDefinition B) (I : IdealsOfDefinition A)
    (hI : I.1 ≤ Ideal.comap φ J.1) :
    spfGammaComponentHom A I
        ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI)))
      = CommRingCat.ofHom φ ≫ spfGammaComponentHom B J := by
  have key : (Scheme.ΓSpecIso (spfQuotientOn A I)).inv
        ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI)))
      = CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI)
        ≫ (Scheme.ΓSpecIso (spfQuotientOn B J)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hmk : CommRingCat.ofHom (Ideal.Quotient.mk I.1)
        ≫ CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI)
      = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J.1) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (RingHom.ext fun _ => rfl)
  rw [spfGammaComponentHom, spfGammaComponentHom, spfGammaComponentHomOn, spfGammaComponentHomOn,
    Category.assoc, key, ← Category.assoc, hmk, Category.assoc]

variable (hA : IsPreAdmissible A)

/-- The map on global sections induced by the component `𝒪^A_I → (Spf φ)_* 𝒪^B_J` of `Spf φ`. -/
noncomputable def spfComponentGammaMap (J : IdealsOfDefinition B) (I : IdealsOfDefinition A)
    (hI : I.1 ≤ Ideal.comap φ J.1) :
    (pseudoDiscrete (spfComponent A I)).obj (op ⊤)
      ⟶ (pseudoDiscrete (spfComponent B J)).obj (op ⊤) :=
  ((spfComponentSpaceMapPseudoDiscrete A B hφ hA J I hI).c).app (op ⊤)

/-- The component of the canonical map of `A` at `I`, followed by the map on global sections of
the component `𝒪^A_I → (Spf φ)_* 𝒪^B_J` of `Spf φ`, is `φ` followed by the component of the
canonical map of `B` at `J`. -/
theorem spfGammaComponent_comp_spfComponentGammaMap (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) :
    spfGammaComponent A I ≫ spfComponentGammaMap A B hφ hA J I hI
      = (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫ spfGammaComponent B J :=
  Subtype.ext (congrArg CommRingCat.Hom.hom (spfGammaComponentHom_comp_appTop A B J I hI))

variable (I₀ : IdealsOfDefinition A)

/-- The map `Spf φ` induces on global sections, as a morphism
`Γ(Spf A, 𝒪_{Spf A}) → Γ(Spf B, 𝒪_{Spf B})` of topological rings. -/
noncomputable def spfMapGammaHom :
    (spfPresheaf A).obj (op ⊤) ⟶ (spfPresheaf B).obj (op ⊤) :=
  (spfMapC A B hφ I₀ hA).app (op ⊤)

/-- The map `Spf φ` induces on global sections, followed by the projection onto the global
sections of the term `𝒪^B_J`, is the projection onto the global sections of
`𝒪^A_{I₀ ⊓ φ⁻¹(J)}` followed by the induced map of those terms. -/
theorem spfMapGammaHom_comp_spfProjection_app_top (J : IdealsOfDefinition B) :
    spfMapGammaHom A B hφ hA I₀ ≫ (spfProjection B J).app (op ⊤)
      = (spfProjection A (spfPullbackIdeal A B hφ I₀ J)).app (op ⊤)
        ≫ spfComponentGammaMap A B hφ hA J (spfPullbackIdeal A B hφ I₀ J)
            (spfPullbackIdeal_le A B hφ I₀ J) :=
  congrFun (congrArg NatTrans.app (spfMapC_comp_spfProjection A B hφ hA I₀ J)) (op ⊤)

/-- The map `Spf φ` induces on global sections is `φ`, read through the canonical maps
`A → Γ(Spf A, 𝒪_{Spf A})` and `B → Γ(Spf B, 𝒪_{Spf B})`. This is the square that the
identification of Stacks 0AHZ fills: the two sides agree in each term `𝒪_λ` of the inverse
systems, where the assertion is that `A → A/(I₀ ⊓ φ⁻¹(J)) → B/J` is `A → B → B/J`. -/
theorem spfGammaHom_comp_spfMapGammaHom :
    spfGammaHom A ≫ spfMapGammaHom A B hφ hA I₀
      = (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫ spfGammaHom B := by
  refine spfPresheafOn_obj_hom_ext B fun J => ?_
  rw [Category.assoc, Category.assoc, spfMapGammaHom_comp_spfProjection_app_top,
    spfGammaHom_comp_spfProjection_app_top B J, ← Category.assoc,
    spfGammaHom_comp_spfProjection_app_top A (spfPullbackIdeal A B hφ I₀ J)]
  exact spfGammaComponent_comp_spfComponentGammaMap A B hφ hA J
    (spfPullbackIdeal A B hφ I₀ J) (spfPullbackIdeal_le A B hφ I₀ J)

end

/-! ### Injectivity of `φ ↦ Spf φ` -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (hA : IsPreAdmissible A) (I₀ : IdealsOfDefinition A) (hB : IsPreAdmissible B)

/-- `Spf` on morphisms as a map of sets: a continuous ring homomorphism `A → B`, which is exactly
a morphism `A ⟶ B` of topological rings, goes to the morphism `Spf B → Spf A` of locally
topologically ringed spaces that it induces. -/
@[sga "3 VIIB 1.1" "Spf(φ)"]
noncomputable def spfLTRSMap (f : TopCommRingCat.of A ⟶ TopCommRingCat.of B) :
    spfLTRS B hB ⟶ spfLTRS A hA :=
  spfMapLTRS A B (φ := f.1) f.2 hA I₀ hB

/-- The morphism of `LTRS` attached to a continuous ring homomorphism is
`AlgebraicGeometry.spfMapLTRS`. -/
@[simp]
theorem spfLTRSMap_apply {φ : A →+* B} (hφ : Continuous φ) :
    spfLTRSMap A B hA I₀ hB ⟨φ, hφ⟩ = spfMapLTRS A B hφ hA I₀ hB := rfl

/-- The map on global sections of the morphism of `LTRS` attached to a continuous ring
homomorphism is `AlgebraicGeometry.spfMapGammaHom`. -/
theorem ltrsGlobalSectionsMap_spfLTRSMap (f : TopCommRingCat.of A ⟶ TopCommRingCat.of B) :
    ltrsGlobalSectionsMap (spfLTRSMap A B hA I₀ hB f) = spfMapGammaHom A B f.2 hA I₀ := rfl

/-- **Stacks 0AHZ**, injectivity of the comparison map. In the identification
`Mor_{LTRS}((Spf B, 𝒪_{Spf B}), (Spf A, 𝒪_{Spf A})) = Hom_cont(A, B)` the map from continuous
ring homomorphisms to morphisms of formal spectra is injective as soon as `B` is separated and
linearly topologized: a morphism determines the map it induces on global sections, that map is
the homomorphism read through the canonical maps into global sections, and the canonical map of
`B` is injective. -/
@[stacks 0AHZ "injectivity of the comparison map Hom_cont(A, B) → Mor_LTRS(Spf B, Spf A)",
  ega "I 10.4.6" "Affine case X = Spf B", sga "3 VIIB 1.1" "partial"]
theorem injective_spfLTRSMap [IsLinearTopology B B] [T2Space B] :
    Function.Injective (spfLTRSMap A B hA I₀ hB) := by
  intro f g hfg
  refine Subtype.ext (RingHom.ext fun a => ?_)
  have hΓ : spfMapGammaHom A B f.2 hA I₀ = spfMapGammaHom A B g.2 hA I₀ := by
    rw [← ltrsGlobalSectionsMap_spfLTRSMap, ← ltrsGlobalSectionsMap_spfLTRSMap]
    exact congrArg (fun m : spfLTRS B hB ⟶ spfLTRS A hA => ltrsGlobalSectionsMap m) hfg
  have hf : spfGammaHom A ≫ spfMapGammaHom A B f.2 hA I₀ = f ≫ spfGammaHom B :=
    spfGammaHom_comp_spfMapGammaHom A B f.2 hA I₀
  have hg : spfGammaHom A ≫ spfMapGammaHom A B g.2 hA I₀ = g ≫ spfGammaHom B :=
    spfGammaHom_comp_spfMapGammaHom A B g.2 hA I₀
  have hkey : f ≫ spfGammaHom B = g ≫ spfGammaHom B := by rw [← hf, ← hg, hΓ]
  exact injective_spfGammaHom B hB
    (congrArg (fun k : TopCommRingCat.of A ⟶ (spfPresheaf B).obj (op ⊤) => k.1 a) hkey)

end

/-! ### Points of a formal spectrum are recovered from its local rings -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The global section of `𝒪_λ` attached to `a : A` is invertible at an open prime `x` exactly
when `a ∉ x`: the stalk of `𝒪_λ` at `x` is the local ring of `Spec (A/I_λ)` at the prime
corresponding to `x`, and there the image of `a` is invertible exactly outside that prime. -/
theorem isUnit_germ_spfGammaComponentHomOn_iff (I : SpfIndex A P) (x : spfSpace A)
    (a : A) :
    IsUnit ((spfComponentOn A I).germ ⊤ x trivial ((spfGammaComponentHomOn A I).hom a))
      ↔ a ∉ x.1.asIdeal := by
  obtain ⟨q, rfl⟩ := surjective_spfOfQuotientOn A I x
  set s : (spfComponentOn A I).obj (op ⊤) := (spfGammaComponentHomOn A I).hom a
  have hpush : IsLocalHom ((Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
      (spfOfQuotientOn A I) q).hom := inferInstance
  have hgerm : ((Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
        (spfOfQuotientOn A I) q)
        ((spfComponentOn A I).germ ⊤ (spfOfQuotientOn A I q) trivial s)
      = (Spec (spfQuotientOn A I)).presheaf.germ ⊤ q trivial s :=
    congrArg
      (fun k : (spfComponentOn A I).obj (op ⊤) ⟶ (Spec (spfQuotientOn A I)).presheaf.stalk q => k s)
      (TopCat.Presheaf.stalkPushforward_germ CommRingCat.{u} (spfOfQuotientOn A I)
        (Spec (spfQuotientOn A I)).presheaf ⊤ q trivial)
  refine (isUnit_iff_of_map_eq _ hgerm).trans ?_
  rw [← Scheme.mem_basicOpen_top, basicOpen_eq_of_affine']
  have hΓ : (Scheme.ΓSpecIso (spfQuotientOn A I)).hom s = Ideal.Quotient.mk I.1 a :=
    congrArg (fun k : CommRingCat.of A ⟶ spfQuotientOn A I => k.hom a)
      (spfGammaComponentHomOn_comp_ΓSpecIso_hom A I)
  rw [hΓ]
  exact Iff.rfl

/-- The global section of `𝒪_λ` attached to `a : A` is invertible at an open prime `x` exactly
when `a ∉ x`: the stalk of `𝒪_λ` at `x` is the local ring of `Spec (A/I_λ)` at the prime
corresponding to `x`, and there the image of `a` is invertible exactly outside that prime.

The ideals-of-definition case of `isUnit_germ_spfGammaComponentHomOn_iff`. -/
theorem isUnit_germ_spfGammaComponentHom_iff (I : IdealsOfDefinition A) (x : spfSpace A)
    (a : A) :
    IsUnit ((spfComponent A I).germ ⊤ x trivial ((spfGammaComponentHom A I).hom a))
      ↔ a ∉ x.1.asIdeal :=
  isUnit_germ_spfGammaComponentHomOn_iff (A := A) (P := IsIdealOfDefinition) (I := I) (x := x)
    (a := a)

/-- The global section of `𝒪` attached to `a : A` is invertible at an open prime `x` exactly
when `a ∉ x`. The point `x` of the formal spectrum is therefore read off from the local ring of
`𝒪` at `x` together with the canonical map `A → Γ(𝒪)`, exactly as a point of `Spec R` is read
off from `R → 𝒪_{Spec R, x}`. One term `I₀` of the inverse system is enough: the question is
already decided in the local ring of `Spec (A/I₀)`. -/
theorem isUnit_germ_spfGammaHomOn_iff (I₀ : SpfIndex A P) (x : spfSpace A) (a : A) :
    IsUnit ((spfPresheafOn A P).germ ⊤ x trivial ((spfGammaHomOn A P).1 a)) ↔ a ∉ x.1.asIdeal := by
  set I : SpfIndex A P := I₀
  have hθ : IsLocalHom ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map
      (spfProjectionOn A I)).1 := isLocalHom_spfProjectionOn_stalk A I x
  have hproj : ((spfProjectionOn A I).app (op ⊤)).1 ((spfGammaHomOn A P).1 a)
      = (spfGammaComponentHomOn A I).hom a :=
    congrArg (fun k : TopCommRingCat.of A ⟶ (pseudoDiscrete (spfComponentOn A I)).obj (op ⊤) =>
      k.1 a) (spfGammaHomOn_comp_spfProjection_app_top A I)
  have hstalk : ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map (spfProjectionOn A I))
        ((spfPresheafOn A P).germ ⊤ x trivial ((spfGammaHomOn A P).1 a))
      = (pseudoDiscrete (spfComponentOn A I)).germ ⊤ x trivial
          ((spfGammaComponentHomOn A I).hom a) := by
    rw [← hproj]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply (C := TopCommRingCat.{u}) ⊤ x trivial
      (spfProjectionOn A I) ((spfGammaHomOn A P).1 a)
  have hpd : ∀ t : ((pseudoDiscrete (spfComponentOn A I)).obj (op ⊤)).α,
      IsUnit ((pseudoDiscrete (spfComponentOn A I)).germ ⊤ x trivial t)
        ↔ IsUnit ((spfComponentOn A I).germ ⊤ x trivial t) := fun t =>
    isUnit_iff_of_map_eq (pseudoDiscreteStalkIso (spfComponentOn A I) x).hom.hom
      (congrArg (fun k : (spfComponentOn A I).obj (op ⊤) ⟶ (spfComponentOn A I).stalk x => k t)
        (germ_pseudoDiscreteStalkIso_hom (spfComponentOn A I) x ⊤ trivial))
  have hup := isUnit_iff_of_map_eq
    ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map (spfProjectionOn A I)).1 hstalk
  rw [← isUnit_germ_spfGammaComponentHomOn_iff A I x a]
  exact hup.trans (hpd ((spfGammaComponentHomOn A I).hom a))

/-- The global section of `𝒪_{Spf A}` attached to `a : A` is invertible at an open prime `x`
exactly when `a ∉ x`. The point `x` of `Spf A` is therefore read off from the local ring of
`𝒪_{Spf A}` at `x` together with the canonical map `A → Γ(Spf A, 𝒪_{Spf A})`, exactly as a point
of `Spec R` is read off from `R → 𝒪_{Spec R, x}`.

The ideals-of-definition case of `isUnit_germ_spfGammaHomOn_iff`. -/
theorem isUnit_germ_spfGammaHom_iff (hA : IsPreAdmissible A) (x : spfSpace A) (a : A) :
    IsUnit ((spfPresheaf A).germ ⊤ x trivial ((spfGammaHom A).1 a)) ↔ a ∉ x.1.asIdeal :=
  isUnit_germ_spfGammaHomOn_iff (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (x := x) (a := a)

end

/-! ### A morphism into a formal spectrum has its base map determined on global sections -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (hA : IsPreAdmissible A)
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]
  {I₀ : SpfIndex A P}

/-- The image under a morphism `g : X → Spf A` of locally topologically ringed spaces of a point
`y` of `X` is recovered from the map `g` induces on global sections: the open prime `g(y)`
consists of exactly those `a : A` whose image in the local ring of `X` at `y`, taken along
`A → Γ(Spf A, 𝒪_{Spf A}) → Γ(X, 𝒪_X) → 𝒪_{X, y}`, is not invertible. -/
theorem notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn {X : LTRS.{u}} (g : X ⟶ spfLTRSOn A P I₀)
    (y : X) (a : A) :
    a ∉ (g.toHom.base y).1.asIdeal
      ↔ IsUnit (X.presheaf.germ ⊤ y trivial
          ((ltrsGlobalSectionsMap g).1 ((spfGammaHomOn A P).1 a))) := by
  have hgerm : g.toHom.stalkMap y
        ((spfPresheafOn A P).germ ⊤ (g.toHom.base y) trivial ((spfGammaHomOn A P).1 a))
      = X.presheaf.germ ⊤ y trivial ((ltrsGlobalSectionsMap g).1 ((spfGammaHomOn A P).1 a)) :=
    PresheafedSpace.stalkMap_germ_apply g.toHom ⊤ y trivial ((spfGammaHomOn A P).1 a)
  rw [← isUnit_germ_spfGammaHomOn_iff A I₀ (g.toHom.base y) a]
  exact isUnit_iff_of_map_eq (g.toHom.stalkMap y).1 hgerm

/-- The image under a morphism `g : X → Spf A` of locally topologically ringed spaces of a point
`y` of `X` is recovered from the map `g` induces on global sections: the open prime `g(y)`
consists of exactly those `a : A` whose image in the local ring of `X` at `y`, taken along
`A → Γ(Spf A, 𝒪_{Spf A}) → Γ(X, 𝒪_X) → 𝒪_{X, y}`, is not invertible.

The ideals-of-definition case of `notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn`. -/
theorem notMem_base_asIdeal_iff_isUnit_germ {X : LTRS.{u}} (g : X ⟶ spfLTRS A hA) (y : X)
    (a : A) :
    a ∉ (g.toHom.base y).1.asIdeal
      ↔ IsUnit (X.presheaf.germ ⊤ y trivial
          ((ltrsGlobalSectionsMap g).1 ((spfGammaHom A).1 a))) :=
  notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn (A := A) (P := IsIdealOfDefinition) (X := X)
    (g := g) (y := y) (a := a) (I₀ := preAdmissibleSpfIndex A hA)

/-- **Extensionality on base maps for morphisms into a formal spectrum.** Two morphisms
`X → Spf A` of locally topologically ringed spaces that induce the same map on global sections
have the same underlying continuous map. This is the half of the identification of Stacks 0AHZ
that needs of the inverse system only that it have a term, and no hypothesis on `X` at all: the
point `g(y)` is determined by which elements of `A` become invertible in the local ring of `X`
at `y`, and that datum is part of the map on global sections. -/
theorem base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn {X : LTRS.{u}} {g h : X ⟶ spfLTRSOn A P I₀}
    (hgh : ltrsGlobalSectionsMap g = ltrsGlobalSectionsMap h) :
    g.toHom.base = h.toHom.base := by
  refine TopCat.hom_ext (ContinuousMap.ext fun y => Subtype.ext (PrimeSpectrum.ext
    (Ideal.ext fun a => not_iff_not.1 ?_)))
  rw [notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn A g y a,
    notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn A h y a, hgh]

/-- **Extensionality on base maps for morphisms into a formal spectrum.** Two morphisms
`X → Spf A` of locally topologically ringed spaces that induce the same map on global sections
have the same underlying continuous map. This is the half of the identification of Stacks 0AHZ
that needs no hypothesis on `A` beyond pre-admissibility, and no hypothesis on `X` at all: the
point `g(y)` is determined by which elements of `A` become invertible in the local ring of `X`
at `y`, and that datum is part of the map on global sections.

The ideals-of-definition case of `base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn`. -/
theorem base_eq_of_ltrsGlobalSectionsMap_eq {X : LTRS.{u}} {g h : X ⟶ spfLTRS A hA}
    (hgh : ltrsGlobalSectionsMap g = ltrsGlobalSectionsMap h) :
    g.toHom.base = h.toHom.base :=
  base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn (A := A) (P := IsIdealOfDefinition) (X := X)
    (g := g) (h := h) (hgh := hgh) (I₀ := preAdmissibleSpfIndex A hA)

end

end AlgebraicGeometry
