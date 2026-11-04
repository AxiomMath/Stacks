module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField

/-!
# The residue field of the henselian local ring of a decent algebraic space

The residue field of the henselian local ring of a decent algebraic space at a point is the
residue field of the space at that point: the field of the chosen monomorphism from a field
spectrum representing the point.

## Main definitions

* `AlgebraicGeometry.Space.fieldValuedPointHom`: the homomorphism of fields whose spectrum is a
  given morphism of the site objects of two field-valued points.

## Main results

* `AlgebraicGeometry.Space.exists_ringEquiv_residueField_neighborhood`: the residue field of an
  elementary étale neighborhood at its distinguished point is the residue field of the space,
  by an isomorphism over the space.
* `AlgebraicGeometry.Space.exists_residueFieldEquiv_residueField`: the residue field of the
  henselian local ring at a point is the residue field of the space at that point, through an
  isomorphism compatible with a given elementary étale neighborhood.
* `AlgebraicGeometry.Space.existsUnique_residueFieldEquiv_residueField`: the residue field of the
  henselian local ring at a point is the residue field of the space at that point, by the unique
  isomorphism compatible with every elementary étale neighborhood.
* `AlgebraicGeometry.Space.nonempty_residueFieldEquiv_residueField`: the residue field of the
  henselian local ring at a point is isomorphic to the residue field of the space at that point.

## References

* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The homomorphism of fields whose spectrum is a given morphism of the site objects of two
field-valued points. -/
def fieldValuedPointHom (p q : FieldValuedPoint B S hS X)
    (g : p.siteObject B S hS X ⟶ q.siteObject B S hS X) : q.carrier →+* p.carrier :=
  ((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom

/-- The spectrum of the homomorphism underlying a morphism of site objects is that morphism. -/
theorem spec_fieldValuedPointHom (p q : FieldValuedPoint B S hS X)
    (g : p.siteObject B S hS X ⟶ q.siteObject B S hS X) :
    Spec.map (CommRingCat.ofHom (fieldValuedPointHom B S hS X p q g)) =
      B.inclusion.map g.left := by
  dsimp [fieldValuedPointHom]
  simp

/-- The homomorphism underlying a composite of morphisms of site objects is the composite, in
the other order, of the homomorphisms they underlie. -/
theorem fieldValuedPointHom_comp (p q r : FieldValuedPoint B S hS X)
    (g : p.siteObject B S hS X ⟶ q.siteObject B S hS X)
    (h : q.siteObject B S hS X ⟶ r.siteObject B S hS X) :
    fieldValuedPointHom B S hS X p r (g ≫ h) =
      (fieldValuedPointHom B S hS X p q g).comp (fieldValuedPointHom B S hS X q r h) := by
  have hof : CommRingCat.ofHom ((fieldValuedPointHom B S hS X p q g).comp
      (fieldValuedPointHom B S hS X q r h)) =
      CommRingCat.ofHom (fieldValuedPointHom B S hS X q r h) ≫
        CommRingCat.ofHom (fieldValuedPointHom B S hS X p q g) := rfl
  have key : CommRingCat.ofHom (fieldValuedPointHom B S hS X p r (g ≫ h)) =
      CommRingCat.ofHom ((fieldValuedPointHom B S hS X p q g).comp
        (fieldValuedPointHom B S hS X q r h)) := by
    apply Spec.map_injective
    rw [spec_fieldValuedPointHom, hof, Spec.map_comp, spec_fieldValuedPointHom,
      spec_fieldValuedPointHom]
    simp
  exact congrArg CommRingCat.Hom.hom key

variable (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)

/-! ### The residue-field points of a refinement of elementary étale neighborhoods -/

/-- The homomorphism of fields underlying the morphism of residue-field points induced by a
morphism of elementary étale neighborhoods is the homomorphism of residue fields induced by the
underlying morphism of schemes. -/
theorem fieldValuedPointHom_neighborhoodResidueFieldMap
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
        (neighborhoodFieldPoint B S hS X hX x U)
        (neighborhoodResidueFieldMap B S hS X hX x f) =
      ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
        f.hom.left.1.residueFieldMap V.point).hom := by
  have h₁ := spec_fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
    (neighborhoodFieldPoint B S hS X hX x U) (neighborhoodResidueFieldMap B S hS X hX x f)
  have h₂ : B.inclusion.map
        (Over.Hom.left (neighborhoodResidueFieldMap B S hS X hX x f)) =
      Spec.map ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
        f.hom.left.1.residueFieldMap V.point) := rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective (h₁.trans h₂))

/-- The homomorphism of residue fields induced by a morphism of elementary étale neighborhoods
carries the class of a germ to the class of its image in the stalk of the finer
neighborhood. -/
theorem residue_fieldValuedPointHom_neighborhoodResidueFieldMap
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    (r : U.scheme.left.1.presheaf.stalk U.point) :
    fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
        (neighborhoodFieldPoint B S hS X hX x U)
        (neighborhoodResidueFieldMap B S hS X hX x f) (IsLocalRing.residue _ r) =
      IsLocalRing.residue _ ((neighborhoodStalkMap B S hS X hX x f).hom r) := by
  have hcat : U.scheme.left.1.residue U.point ≫
        ((U.scheme.left.1.residueFieldCongr f.map_point).inv ≫
          f.hom.left.1.residueFieldMap V.point) =
      neighborhoodStalkMap B S hS X hX x f ≫ V.scheme.left.1.residue V.point := by
    rw [Scheme.residueFieldCongr_inv, ← Category.assoc, Scheme.residue_residueFieldCongr,
      Category.assoc, Scheme.residue_residueFieldMap, neighborhoodStalkMap, Category.assoc]
  rw [fieldValuedPointHom_neighborhoodResidueFieldMap B S hS X hX x f]
  exact ConcreteCategory.congr_hom hcat r

/-- The morphism of residue-field points induced by a morphism of elementary étale
neighborhoods lies over the algebraic space. -/
theorem fieldMorphism_neighborhoodResidueFieldMap
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫
        fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
      fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x V) := by
  have h₁ := congrArg
    (fun k : yoneda.obj ((neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X) ⟶ X ↦
      yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫ k)
    (neighborhoodFieldPoint_morphism B S hS X hX x U)
  have h₂ : yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) ≫
        (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
          U.toSpace) =
      yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
        V.toSpace := by
    rw [← Category.assoc, ← Functor.map_comp, neighborhoodResidueFieldMap_comp,
      Functor.map_comp, Category.assoc, f.over]
  exact h₁.trans (h₂.trans (neighborhoodFieldPoint_morphism B S hS X hX x V).symm)

/-! ### The residue field of the henselian local ring -/

/-- The morphism from the residue-field point of a neighborhood to the space is a monomorphism. -/
private theorem mono_fieldMorphism_neighborhoodFieldPoint
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    Mono (fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U)) := by
  rw [fieldMorphism, neighborhoodFieldPoint_morphism]
  exact U.mono_residueField

/-- The residue field of an elementary étale neighborhood at its distinguished point is the
residue field of the decent algebraic space at the point it lies over, by the unique
isomorphism over the space. -/
theorem exists_ringEquiv_residueField_neighborhood (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (eκ : (neighborhoodFieldPoint B S hS X hX x U).carrier ≃+*
        residueField B S hS X hDecent x)
      (g : (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X ⟶
        (neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X),
      fieldValuedPointHom B S hS X _ _ g = eκ.toRingHom ∧
        yoneda.map g ≫ fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
          residueFieldMorphism B S hS X hDecent x := by
  set p := (residueFieldRepresentative B S hS X hDecent x).1 with hp
  set q := neighborhoodFieldPoint B S hS X hX x U with hq
  have hmp : Mono (yonedaEquiv.symm p.value) :=
    (residueFieldRepresentative B S hS X hDecent x).2.2
  have hmq : Mono (yonedaEquiv.symm q.value) :=
    mono_fieldMorphism_neighborhoodFieldPoint B S hS X hX x U
  have hcls : p.class B S hS X = q.class B S hS X :=
    ((residueFieldRepresentative B S hS X hDecent x).2.1).trans
      (neighborhoodFieldPoint_class B S hS X hX x U).symm
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS X hX p q hcls
  have hover : yoneda.map e.hom ≫ fieldMorphism B S hS X q =
      residueFieldMorphism B S hS X hDecent x := by
    show yoneda.map e.hom ≫ yonedaEquiv.symm q.value = yonedaEquiv.symm p.value
    rw [yonedaEquiv_symm_naturality_left e.hom X q.value, he]
  have hleftIso : IsIso (B.inclusion.map e.hom.left) := by
    have h₁ : IsIso ((Over.forget (B.obj hS)).map e.hom) := inferInstance
    have h₂ : IsIso e.hom.left := h₁
    infer_instance
  have hspec := spec_fieldValuedPointHom B S hS X p q e.hom
  rw [← hspec] at hleftIso
  have hop : IsIso (Scheme.Spec.map
      (CommRingCat.ofHom (fieldValuedPointHom B S hS X p q e.hom)).op) := by
    simpa [Scheme.Spec] using hleftIso
  have hiso : IsIso (CommRingCat.ofHom (fieldValuedPointHom B S hS X p q e.hom)) :=
    (isIso_op_iff _).mp
      ((Functor.FullyFaithful.ofFullyFaithful Scheme.Spec).isIso_of_isIso_map _)
  exact ⟨(asIso (CommRingCat.ofHom
    (fieldValuedPointHom B S hS X p q e.hom))).commRingCatIsoToRingEquiv, e.hom, rfl, hover⟩

/-- The residue field of the henselian local ring of a decent algebraic space at a point is the
residue field of the space at that point, through an isomorphism compatible with the canonical
homomorphism out of the stalk of a given elementary étale neighborhood. -/
@[stacks 0EN0 "the residue field of the henselian local ring is the residue field of the space.
Both fields are determined only up to canonical isomorphism, so the identification is
existential, pinned by the isomorphism `eκ` of the neighborhood residue field with the residue
field of the space lying over the space (the morphism `g`) and by compatibility with the
canonical homomorphism out of the neighborhood stalk. No hypothesis is carried: cofilteredness of
the elementary étale neighborhoods comes from Stacks 0BGV, nonemptiness from the given
neighborhood"]
theorem exists_residueFieldEquiv_residueField (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    ∃ (eκ : (neighborhoodFieldPoint B S hS X hX x U).carrier ≃+*
        residueField B S hS X hDecent x)
      (g : (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X ⟶
        (neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X)
      (e : residueField B S hS X hDecent x ≃+*
        IsLocalRing.ResidueField (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))),
      fieldValuedPointHom B S hS X _ _ g = eκ.toRingHom ∧
        yoneda.map g ≫ fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
          residueFieldMorphism B S hS X hDecent x ∧
        ∀ r : U.scheme.left.1.presheaf.stalk U.point,
          e (eκ (IsLocalRing.residue _ r)) =
            IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent U r) := by
  let _ := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  obtain ⟨eκ, g, hg, hover⟩ :=
    exists_ringEquiv_residueField_neighborhood B S hS X hX x hDecent U
  obtain ⟨e₁, he₁⟩ :=
    exists_residueFieldEquiv_henselianLocalRing B S hS X hX x hDecent U
  exact ⟨eκ, g, eκ.symm.trans e₁, hg, hover,
    fun r ↦ (congrArg e₁ (eκ.symm_apply_apply _)).trans (he₁ r)⟩

/-- The residue field of the henselian local ring of a decent algebraic space at a point is the
residue field of the space at that point: there is exactly one isomorphism
between them compatible with every elementary étale neighborhood of the point, namely the one
carrying the class of the image of a germ `r` of the neighborhood to the value at `r` of the
homomorphism of residue fields lying over the space. -/
@[stacks 0EN0 "the residue field of the henselian local ring is the residue field of the space,
by the canonical isomorphism: the unique one compatible, for every elementary étale neighborhood,
with the canonical homomorphism out of its stalk and the homomorphism of residue fields over the
space. No neighborhood is assumed; one exists by Stacks 0BBP"]
theorem existsUnique_residueFieldEquiv_residueField (hDecent : IsDecentSpace B S hS X) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    ∃! e : IsLocalRing.ResidueField
        (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) ≃+*
          residueField B S hS X hDecent x,
      ∀ (U : ElementaryEtaleNeighborhood B S hS X hX x)
        (g : (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X ⟶
          (neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X),
        yoneda.map g ≫ fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
            residueFieldMorphism B S hS X hDecent x →
        ∀ r : U.scheme.left.1.presheaf.stalk U.point,
          e (IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent U r)) =
            fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
              (neighborhoodFieldPoint B S hS X hX x U) g (IsLocalRing.residue _ r) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  choose eU heU using fun U : ElementaryEtaleNeighborhood B S hS X hX x ↦
    exists_residueFieldEquiv_henselianLocalRing B S hS X hX x hDecent U
  choose eκ gov hgov hover using fun U : ElementaryEtaleNeighborhood B S hS X hX x ↦
    exists_ringEquiv_residueField_neighborhood B S hS X hX x hDecent U
  have hsurj : ∀ (U : ElementaryEtaleNeighborhood B S hS X hX x)
      (y : IsLocalRing.ResidueField
        (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))),
      ∃ r : U.scheme.left.1.presheaf.stalk U.point,
        IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent U r) = y := by
    intro U y
    obtain ⟨t, rfl⟩ := (eU U).surjective y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
    exact ⟨r, (heU U r).symm⟩
  have hgeq : ∀ (U : ElementaryEtaleNeighborhood B S hS X hX x)
      (g : (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X ⟶
        (neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X),
      yoneda.map g ≫ fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
          residueFieldMorphism B S hS X hDecent x →
      g = gov U := by
    intro U g hg
    have := mono_fieldMorphism_neighborhoodFieldPoint B S hS X hX x U
    exact yoneda.map_injective ((cancel_mono
      (fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U))).1
      (hg.trans (hover U).symm))
  have hgovtrans : ∀ {V U : ElementaryEtaleNeighborhood B S hS X hX x}
      (h : (neighborhoodFieldPoint B S hS X hX x V).siteObject B S hS X ⟶
        (neighborhoodFieldPoint B S hS X hX x U).siteObject B S hS X),
      yoneda.map h ≫ fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
          fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x V) →
      fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
          (neighborhoodFieldPoint B S hS X hX x U) (gov U) =
        (fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
            (neighborhoodFieldPoint B S hS X hX x V) (gov V)).comp
          (fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
            (neighborhoodFieldPoint B S hS X hX x U) h) := by
    intro V U h hh
    have hcomp : yoneda.map (gov V ≫ h) ≫
        fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX x U) =
        residueFieldMorphism B S hS X hDecent x := by
      rw [Functor.map_comp, Category.assoc, hh]
      exact hover V
    rw [← hgeq U (gov V ≫ h) hcomp, fieldValuedPointHom_comp]
  have hgovtrans' : ∀ {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U),
      fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
          (neighborhoodFieldPoint B S hS X hX x U) (gov U) =
        (fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
            (neighborhoodFieldPoint B S hS X hX x V) (gov V)).comp
          (fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
            (neighborhoodFieldPoint B S hS X hX x U)
            (neighborhoodResidueFieldMap B S hS X hX x f)) :=
    fun {V U} f ↦ hgovtrans (neighborhoodResidueFieldMap B S hS X hX x f)
      (fieldMorphism_neighborhoodResidueFieldMap B S hS X hX x f)
  have heUtrans : ∀ {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
      (t : (neighborhoodFieldPoint B S hS X hX x U).carrier),
      eU U t = eU V (fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
        (neighborhoodFieldPoint B S hS X hX x U)
        (neighborhoodResidueFieldMap B S hS X hX x f) t) := by
    intro V U f t
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
    have hnat : stalkToHenselianLocalRing B S hS X hX x hDecent V
          ((neighborhoodStalkMap B S hS X hX x f).hom r) =
        stalkToHenselianLocalRing B S hS X hX x hDecent U r :=
      congrArg (fun φ : U.scheme.left.1.presheaf.stalk U.point →+*
          (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) ↦ φ r)
        (stalkToHenselianLocalRing_naturality B S hS X hX x hDecent f)
    calc eU U (IsLocalRing.residue _ r)
        = IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent U r) :=
          heU U r
      _ = IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX x hDecent V
            ((neighborhoodStalkMap B S hS X hX x f).hom r)) :=
          congrArg (IsLocalRing.residue _) hnat.symm
      _ = eU V (IsLocalRing.residue _ ((neighborhoodStalkMap B S hS X hX x f).hom r)) :=
          (heU V _).symm
      _ = eU V (fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
            (neighborhoodFieldPoint B S hS X hX x U)
            (neighborhoodResidueFieldMap B S hS X hX x f) (IsLocalRing.residue _ r)) :=
          congrArg (eU V)
            (residue_fieldValuedPointHom_neighborhoodResidueFieldMap B S hS X hX x f r).symm
  obtain ⟨U₀, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hDecent x
  have : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX x) :=
    ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX x ⟨U₀⟩
  have hbase : ∀ t : (neighborhoodFieldPoint B S hS X hX x U₀).carrier,
      (eU U₀).symm.trans (eκ U₀) (eU U₀ t) =
        fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
          (neighborhoodFieldPoint B S hS X hX x U₀) (gov U₀) t := by
    intro t
    rw [hgov U₀]
    exact congrArg (eκ U₀) ((eU U₀).symm_apply_apply t)
  have hstep : ∀ {V W : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ W),
      (∀ t : (neighborhoodFieldPoint B S hS X hX x V).carrier,
          (eU U₀).symm.trans (eκ U₀) (eU V t) =
            fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
              (neighborhoodFieldPoint B S hS X hX x V) (gov V) t) ↔
        ∀ t : (neighborhoodFieldPoint B S hS X hX x W).carrier,
          (eU U₀).symm.trans (eκ U₀) (eU W t) =
            fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
              (neighborhoodFieldPoint B S hS X hX x W) (gov W) t := by
    intro V W f
    have hρ := fun t ↦ DFunLike.congr_fun (hgovtrans' f) t
    refine ⟨fun hV t ↦ ?_, fun hW t ↦ ?_⟩
    · rw [heUtrans f t, hV]
      exact (hρ t).symm
    · have hsurjρ : Function.Surjective
          (fieldValuedPointHom B S hS X (neighborhoodFieldPoint B S hS X hX x V)
            (neighborhoodFieldPoint B S hS X hX x W)
            (neighborhoodResidueFieldMap B S hS X hX x f)) := by
        intro s
        refine ⟨(eκ W).symm ((eκ V) s), ?_⟩
        have h₁ := hρ ((eκ W).symm ((eκ V) s))
        rw [hgov W, hgov V] at h₁
        exact (eκ V).injective (h₁.symm.trans ((eκ W).apply_symm_apply _))
      obtain ⟨z, rfl⟩ := hsurjρ t
      rw [← heUtrans f z, hW z]
      exact hρ z
  have hall : ∀ W : ElementaryEtaleNeighborhood B S hS X hX x,
      ∀ t : (neighborhoodFieldPoint B S hS X hX x W).carrier,
        (eU U₀).symm.trans (eκ U₀) (eU W t) =
          fieldValuedPointHom B S hS X (residueFieldRepresentative B S hS X hDecent x).1
            (neighborhoodFieldPoint B S hS X hX x W) (gov W) t := fun W ↦
    (hstep (IsCofiltered.minToLeft W U₀)).1
      ((hstep (IsCofiltered.minToRight W U₀)).2 hbase)
  refine ⟨(eU U₀).symm.trans (eκ U₀), ?_, ?_⟩
  · intro W g hg r
    rw [hgeq W g hg, ← heU W r]
    exact hall W (IsLocalRing.residue _ r)
  · intro e he
    refine RingEquiv.ext fun y ↦ ?_
    obtain ⟨r, rfl⟩ := hsurj U₀ y
    rw [he U₀ (gov U₀) (hover U₀) r, ← heU U₀ r]
    exact (hall U₀ (IsLocalRing.residue _ r)).symm

/-- The residue field of the henselian local ring of a decent algebraic space at a point is
isomorphic to the residue field of the space at that point. -/
theorem nonempty_residueFieldEquiv_residueField (hDecent : IsDecentSpace B S hS X) :
    letI := henselianLocalRing_isLocalRing B S hS X hX x hDecent
    Nonempty (IsLocalRing.ResidueField
        (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) ≃+*
      residueField B S hS X hDecent x) := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hDecent
  exact ⟨(existsUnique_residueFieldEquiv_residueField B S hS X hX x hDecent).exists.choose⟩

end AlgebraicGeometry.Space

end
