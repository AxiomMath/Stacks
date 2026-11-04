module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Square
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of complexes associated to a square on a ringed site

For a commutative square `E ⟶ Y`, `Z ⟶ X` in a site carrying a sheaf of rings, signed
restriction of sections gives a two-step chain `I(X) ⟶ I(Z) ⊞ I(Y) ⟶ I(E)` whose composite
vanishes.  The zero null-homotopy for that vanishing therefore produces a canonical map from
`I(X)` to the mapping cocone of the second step.

## Main definitions

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsSystem` is the contravariant system of
  section functors of the site, which is the input the general engine below runs on.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.General.firstMap`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.General.secondMap` and
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.General.cSquare` are the two signed maps and the
  canonical map, for an arbitrary contravariant system of additive section functors.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.firstMap` is the map `I(X) ⟶ I(Z) ⊞ I(Y)` assembled
  from the two
  restrictions out of `X`.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.secondMap` is the signed map `I(Z) ⊞ I(Y) ⟶ I(E)`,
  with the minus sign on
  the restriction from `Y`.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare` is the canonical map `I(X) ⟶ C(β)[-1]`
  built from `firstMap` and
  the zero null-homotopy of `firstMap ≫ secondMap`.

## Main results

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.firstMap_comp_secondMap` is the vanishing of the
  two-step composite.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction_id`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction_comp` and their degreewise
  forms say that restriction of sections is contravariantly functorial.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare_natural` is the naturality of `cSquare` in
  the complex.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare_arrow_iso_of_isKInjective` shows that the
  arrow obtained in the
  derived category of abelian groups does not depend on the choice of K-injective
  representative of a derived object.

## Implementation notes

`CategoryTheory.Square` numbers the four corners `E, Y, Z, X` as `X₁, X₂, X₃, X₄`, so the
square's factorization `sq.fac` is the equality of the two composites `X₄ ⟶ X₁`.  Mathlib's
`CochainComplex.mappingCocone β` is `C(β)[-1]`.

The construction is stated in the `General` namespace for an arbitrary contravariant system
`S : ιᵒᵖ ⥤ (A ⥤ B)` of additive section functors between abelian categories, and a square of
objects of `ι`; the per-corner sections are `S.obj (op U)`, restriction is `S.map f.op`, and
contravariant functoriality of restriction is `S.map_id` and `S.map_comp`.  The site-theoretic
statements are that engine instantiated at `sectionsSystem`, the system of sections functors of
the site, so that nothing about sheaves of modules enters the construction itself.

The sheaf of rings is taken as a `Sheaf J RingCat` rather than extracted from a bundled
ringed site whose structure sheaf is commutative: nothing in these three constructions uses
commutativity, and the commutative case is recovered by instantiating the ring sheaf at the
`RingCat`-valued sheaf underlying the structure sheaf.  The module universe is independent
of the site and ring universes.

Independence of the K-injective representative is reduced to the triangulated five lemma:
`MappingCoconeAux.mapArrowHom_eq_coneMap` identifies the induced map of mapping cocones
with the shift of Mathlib's `CochainComplex.mappingCone.map`, which is the third component
of a morphism of the distinguished cone triangles, and the other two components are
inverted by the localization functor because a homotopy equivalence is carried to a
homotopy equivalence by the degreewise section functors and by binary biproducts.

## References

* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}

/-- Sections over `U`, regarded as abelian groups. -/
noncomputable abbrev sections (R : Sheaf J RingCat.{r}) (U : C) :
    SheafOfModules.{v} R ⥤ AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{v}).obj (op U)

/-- Restriction of sections along a morphism of the site. -/
noncomputable def sectionsRestriction (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :
    sections.{u, v} R V ⟶ sections.{u, v} R U :=
  Functor.whiskerLeft (SheafOfModules.toSheaf R)
    ((sheafSections J AddCommGrpCat.{v}).map f.op)

/-- Sections over an object form an additive functor on sheaves of abelian groups. -/
theorem sheafSections_obj_additive (U : C) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op U)).Additive where
  map_add := by intros; rfl

attribute [local instance] sheafSections_obj_additive

/-- Sections over an object form an additive functor on sheaves of modules. -/
instance sections_additive (R : Sheaf J RingCat.{r}) (U : C) :
    (sections.{u, v} R U).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf R ⋙
    (sheafSections J AddCommGrpCat.{v}).obj (op U)).Additive)

/-- The sections of the site, as a contravariant system of additive functors on sheaves of
modules: over the object `U` it is `sections R U`, and along `f : U ⟶ V` it is restriction. -/
noncomputable abbrev sectionsSystem (R : Sheaf J RingCat.{r}) :
    Cᵒᵖ ⥤ (SheafOfModules.{v} R ⥤ AddCommGrpCat.{v}) where
  obj X := sections R X.unop
  map f := sectionsRestriction R f.unop
  map_id X := by
    have h : sectionsRestriction R (𝟙 X.unop) = 𝟙 (sections R X.unop) := by
      dsimp [sectionsRestriction]
      rw [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id']
    exact h
  map_comp f g := by
    have h : sectionsRestriction R (g.unop ≫ f.unop) =
        sectionsRestriction R f.unop ≫ sectionsRestriction R g.unop := by
      dsimp [sectionsRestriction]
      rw [Functor.map_comp, Functor.whiskerLeft_comp]
    exact h

/-- Every functor of the system of sections is additive. -/
instance sectionsSystem_obj_additive (R : Sheaf J RingCat.{r}) (X : Cᵒᵖ) :
    ((sectionsSystem.{u, v} R).obj X).Additive :=
  sections_additive R X.unop

end Stacks.MayerVietoris.CanonicalMapOfComplexes

namespace MappingCoconeAux

open HomologicalComplex CochainComplex CochainComplex.HomComplex

section

variable {C : Type u} [Category.{w} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  [DecidableRel c.Rel] {F G F' G' : HomologicalComplex C c} {φ : F ⟶ G} {φ' : F' ⟶ G'}
  [HasHomotopyCofiber φ] [HasHomotopyCofiber φ']
  (Hc : ∀ (j : ι), ∃ i, c.Rel i j) (α : Arrow.mk φ ⟶ Arrow.mk φ')

open homotopyCofiber in
/-- The induced map of homotopy cofibers is compatible with the first projections. -/
theorem mapArrowHom_f_fstX (j k : ι) (hjk : c.Rel j k) :
    (mapArrowHom φ φ' Hc α).f j ≫ fstX φ' j k hjk = fstX φ j k hjk ≫ α.left.f k := by
  rw [mapArrowHom, desc_f _ _ _ _ _ hjk]
  simp [inrCompHomotopy_hom _ _ _ _ hjk]

open homotopyCofiber in
/-- The induced map of homotopy cofibers is compatible with the second projections. -/
theorem mapArrowHom_f_sndX (j : ι) :
    (mapArrowHom φ φ' Hc α).f j ≫ sndX φ' j = sndX φ j ≫ α.right.f j := by
  rw [mapArrowHom]
  by_cases hj : c.Rel j (c.next j)
  · rw [desc_f _ _ _ _ _ hj]
    simp [inrCompHomotopy_hom _ _ _ _ hj]
  · rw [desc_f' _ _ _ _ hj]
    simp

end

section

variable {C : Type u} [Category.{w} C] [Preadditive C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
  [HasHomotopyCofiber φ]

/-- The first projection of a mapping cocone, in terms of the mapping cone. -/
theorem cocone_fst_f (p : ℤ) :
    (mappingCocone.fst φ).f p = (mappingCone.fst φ).1.v (p + -1) p (by omega) := by
  simp [mappingCocone.fst,
    Cochain.leftShift_v (n := 1) _ (-1) 0 (by omega) p p (add_zero p) (p + -1) (by omega)]
  rfl

/-- The second projection of a mapping cocone, in terms of the mapping cone. -/
theorem cocone_snd_v (p : ℤ) :
    (mappingCocone.snd φ).v p (p + -1) rfl =
      (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) :=
  (Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by omega) p (p + -1) rfl (p + -1)
    (by omega)).trans (by simp [Int.negOnePow_even 2 ⟨1, rfl⟩])

/-- The first projection of a mapping cone is the first projection of the homotopy cofiber. -/
theorem fst_v_eq (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone.fst φ).1.v i j hij =
      homotopyCofiber.fstX φ i j (ComplexShape.up_mk _ _ hij) := rfl

/-- The second projection of a mapping cone is the second projection of the homotopy cofiber. -/
theorem snd_v_eq (i : ℤ) :
    (mappingCone.snd φ).v i i (add_zero i) = homotopyCofiber.sndX φ i := by
  rw [mappingCone.snd]
  exact Cochain.ofHoms_v _ i

/-- Maps into a mapping cocone are determined by their two components. -/
theorem hom_ext {M : CochainComplex C ℤ} {f g : M ⟶ mappingCocone φ}
    (h₁ : ∀ p, f.f p ≫ (mappingCocone.fst φ).f p = g.f p ≫ (mappingCocone.fst φ).f p)
    (h₂ : ∀ p, f.f p ≫ (mappingCocone.snd φ).v p (p + -1) rfl =
      g.f p ≫ (mappingCocone.snd φ).v p (p + -1) rfl) :
    f = g := by
  ext p
  have key : ∀ (x : M.X p ⟶ (mappingCocone φ).X p),
      x = (x ≫ (mappingCocone.fst φ).f p) ≫ (mappingCocone.inl φ).v p p (add_zero p) +
        (x ≫ (mappingCocone.snd φ).v p (p + -1) rfl) ≫
          (mappingCocone.inr φ).1.v (p + -1) p (by omega) := fun x => by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      mappingCocone.id_X φ p (p + -1) rfl, Category.comp_id]
  rw [key (f.f p), key (g.f p), h₁ p, h₂ p]

end

section

open HomologicalComplex CochainComplex

variable {V : Type*} [Category V] [Preadditive V] [Limits.HasBinaryBiproducts V]
  {W : Type*} [Category W] [Preadditive W] (F : V ⥤ W) [F.Additive]

/-- An additive functor inverts the biproduct of two maps as soon as it inverts each of
them: the inverse is assembled from the two projections and inclusions. -/
theorem isIso_map_biprod_map {A B A' B' : V} (u : A ⟶ A') (v : B ⟶ B')
    [IsIso (F.map u)] [IsIso (F.map v)] :
    IsIso (F.map (Limits.biprod.map u v)) := by
  refine ⟨F.map (Limits.biprod.fst : A' ⊞ B' ⟶ A') ≫ inv (F.map u) ≫
      F.map (Limits.biprod.inl : A ⟶ A ⊞ B) +
    F.map (Limits.biprod.snd : A' ⊞ B' ⟶ B') ≫ inv (F.map v) ≫
      F.map (Limits.biprod.inr : B ⟶ A ⊞ B), ?_, ?_⟩
  · have h₁ : F.map (Limits.biprod.map u v) ≫ F.map (Limits.biprod.fst : A' ⊞ B' ⟶ A') =
        F.map (Limits.biprod.fst : A ⊞ B ⟶ A) ≫ F.map u := by
      rw [← F.map_comp, ← F.map_comp, Limits.biprod.map_fst]
    have h₂ : F.map (Limits.biprod.map u v) ≫ F.map (Limits.biprod.snd : A' ⊞ B' ⟶ B') =
        F.map (Limits.biprod.snd : A ⊞ B ⟶ B) ≫ F.map v := by
      rw [← F.map_comp, ← F.map_comp, Limits.biprod.map_snd]
    simp only [Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂, IsIso.hom_inv_id_assoc]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, Limits.biprod.total, F.map_id]
  · have h₁ : F.map (Limits.biprod.inl : A ⟶ A ⊞ B) ≫ F.map (Limits.biprod.map u v) =
        F.map u ≫ F.map (Limits.biprod.inl : A' ⟶ A' ⊞ B') := by
      rw [← F.map_comp, ← F.map_comp, Limits.biprod.inl_map]
    have h₂ : F.map (Limits.biprod.inr : B ⟶ A ⊞ B) ≫ F.map (Limits.biprod.map u v) =
        F.map v ≫ F.map (Limits.biprod.inr : B' ⟶ A' ⊞ B') := by
      rw [← F.map_comp, ← F.map_comp, Limits.biprod.inr_map]
    simp only [Preadditive.add_comp, Category.assoc, h₁, h₂, IsIso.inv_hom_id_assoc]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, Limits.biprod.total, F.map_id]

end

section

open HomologicalComplex CochainComplex

variable {C : Type u} [Category.{w} C] [Preadditive C] [Limits.HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The map of mapping cones induced by a commutative square is compatible with the
first projections. -/
theorem coneMap_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫ (mappingCone.fst φ₂).1.v p q hpq =
      (mappingCone.fst φ₁).1.v p q hpq ≫ a.f q := by
  simp [mappingCone.ext_from_iff _ q p hpq, mappingCone.map]

/-- The map of mapping cones induced by a commutative square is compatible with the
second projections. -/
theorem coneMap_f_snd_v (p : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫ (mappingCone.snd φ₂).v p p (add_zero p) =
      (mappingCone.snd φ₁).v p p (add_zero p) ≫ b.f p := by
  simp [mappingCone.ext_from_iff _ (p + 1) p rfl, mappingCone.map]

/-- The first-projection compatibility of `mappingCone.map`, in homotopy-cofiber form. -/
theorem coneMap_f_fstX (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫
        homotopyCofiber.fstX φ₂ p q (ComplexShape.up_mk _ _ hpq) =
      homotopyCofiber.fstX φ₁ p q (ComplexShape.up_mk _ _ hpq) ≫ a.f q :=
  coneMap_f_fst_v φ₁ φ₂ a b comm p q hpq

/-- The second-projection compatibility of `mappingCone.map`, in homotopy-cofiber form. -/
theorem coneMap_f_sndX (p : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫ homotopyCofiber.sndX φ₂ p =
      homotopyCofiber.sndX φ₁ p ≫ b.f p := by
  rw [← snd_v_eq, ← snd_v_eq]
  exact coneMap_f_snd_v φ₁ φ₂ a b comm p

/-- The homotopy-cofiber map induced by a morphism of arrows is the map of mapping cones
induced by the underlying commutative square. -/
theorem mapArrowHom_eq_coneMap (Hc : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j)
    (α : Arrow.mk φ₁ ⟶ Arrow.mk φ₂) :
    homotopyCofiber.mapArrowHom φ₁ φ₂ Hc α =
      mappingCone.map φ₁ φ₂ α.left α.right α.w.symm := by
  ext p
  refine homotopyCofiber.ext_to_X φ₂ p (p + 1) (ComplexShape.up_mk _ _ rfl) ?_ ?_
  · exact (mapArrowHom_f_fstX Hc α p (p + 1) (ComplexShape.up_mk _ _ rfl)).trans
      (coneMap_f_fstX φ₁ φ₂ α.left α.right _ p (p + 1) rfl).symm
  · exact (mapArrowHom_f_sndX Hc α p).trans
      (coneMap_f_sndX φ₁ φ₂ α.left α.right _ p).symm

end

section

open HomologicalComplex

variable {A : Type u} [Category.{w} A] [Abelian A] [HasDerivedCategory A]

/-- Two K-injective complexes whose images in the derived category are isomorphic are
homotopy equivalent: morphisms into a K-injective complex are computed by `Qh`, so the
derived isomorphism and its inverse both lift, uniquely, to homotopy classes. -/
theorem nonempty_homotopyEquiv_of_derivedIso (I I' : CochainComplex A ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj I') :
    Nonempty (HomotopyEquiv I I') := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) I').surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app I ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso A).inv.app I')
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective g
  have hQf : DerivedCategory.Q.map f = e.hom := by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := A) f
    rw [hg, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
    exact ((cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app I)).mp h).symm
  have : IsIso (DerivedCategory.Q.map f) := by rw [hQf]; infer_instance
  have hq : QuasiIso f := by rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  obtain ⟨he, -⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp hq
  exact ⟨he⟩

end
end MappingCoconeAux

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes.General

open MappingCoconeAux

section Chain

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Preadditive A]
  {B : Type*} [Category* B] [Preadditive B] [HasBinaryBiproducts B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive]

/-- Degreewise sections over an object of the indexing category. -/
noncomputable abbrev complexFunctor (U : ι) : CochainComplex A ℤ ⥤ CochainComplex B ℤ :=
  (S.obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise restriction along a morphism of the indexing category. -/
noncomputable def restrictionComplex {U V : ι} (f : U ⟶ V) :
    complexFunctor S V ⟶ complexFunctor S U :=
  NatTrans.mapHomologicalComplex (S.map f.op) (ComplexShape.up ℤ)

omit [HasBinaryBiproducts B] in
/-- Degreewise restriction along an identity is the identity. -/
theorem restrictionComplex_id (U : ι) :
    restrictionComplex S (𝟙 U) = 𝟙 (complexFunctor S U) := by
  have h : S.map (𝟙 U).op = 𝟙 (S.obj (op U)) := S.map_id (op U)
  rw [restrictionComplex, h, NatTrans.mapHomologicalComplex_id]

omit [HasBinaryBiproducts B] in
/-- Degreewise restriction is contravariantly functorial. -/
theorem restrictionComplex_comp {U V W : ι} (f : U ⟶ V) (g : V ⟶ W) :
    restrictionComplex S (f ≫ g) = restrictionComplex S g ≫ restrictionComplex S f := by
  have h : S.map (f ≫ g).op = S.map g.op ≫ S.map f.op := S.map_comp g.op f.op
  rw [restrictionComplex, h, NatTrans.mapHomologicalComplex_comp]
  rfl

variable (sq : Square ι)

/-- The map `I(X₄) ⟶ I(X₃) ⊞ I(X₂)`. -/
noncomputable def firstMap (I : CochainComplex A ℤ) :
    (complexFunctor S sq.X₄).obj I ⟶
      (complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I :=
  biprod.lift ((restrictionComplex S sq.f₃₄).app I) ((restrictionComplex S sq.f₂₄).app I)

/-- The signed map `I(X₃) ⊞ I(X₂) ⟶ I(X₁)`. -/
noncomputable def secondMap (I : CochainComplex A ℤ) :
    (complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I ⟶
      (complexFunctor S sq.X₁).obj I :=
  biprod.desc ((restrictionComplex S sq.f₁₃).app I) (-((restrictionComplex S sq.f₁₂).app I))

/-- Signed restriction maps compose to zero. -/
theorem firstMap_comp_secondMap (I : CochainComplex A ℤ) :
    firstMap S sq I ≫ secondMap S sq I = 0 := by
  dsimp [firstMap, secondMap]
  rw [biprod.lift_desc, Preadditive.comp_neg, add_neg_eq_zero]
  have key : restrictionComplex S sq.f₃₄ ≫ restrictionComplex S sq.f₁₃ =
      restrictionComplex S sq.f₂₄ ≫ restrictionComplex S sq.f₁₂ := by
    rw [← restrictionComplex_comp, ← restrictionComplex_comp, sq.fac]
  exact congrArg (fun α : complexFunctor S sq.X₄ ⟶ complexFunctor S sq.X₁ => α.app I) key

/-- The canonical map `I(X₄) ⟶ C(β)[-1]`, using the zero null-homotopy. -/
noncomputable def cSquare (I : CochainComplex A ℤ) :
    (complexFunctor S sq.X₄).obj I ⟶ CochainComplex.mappingCocone (secondMap S sq I) :=
  CochainComplex.mappingCocone.lift (secondMap S sq I) (firstMap S sq I) 0
    (by simp [firstMap_comp_secondMap S sq I])

/-- The morphism of signed restriction arrows induced by a chain map. -/
noncomputable def secondMapArrowMap {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    Arrow.mk (secondMap S sq I) ⟶ Arrow.mk (secondMap S sq I') :=
  Arrow.homMk'
    (biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f))
    ((complexFunctor S sq.X₁).map f) (by
      apply biprod.hom_ext'
      · simp [secondMap, NatTrans.naturality]
      · simp [secondMap, NatTrans.naturality])

/-- The induced map of mapping cocones. -/
noncomputable def mappingCoconeMap {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    CochainComplex.mappingCocone (secondMap S sq I) ⟶
      CochainComplex.mappingCocone (secondMap S sq I') :=
  (shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom (secondMap S sq I) (secondMap S sq I')
      (fun j ↦ ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩) (secondMapArrowMap S sq f))

/-- The induced map of mapping cocones is compatible with the first projections. -/
theorem mappingCoconeMap_f_fst_f {I I' : CochainComplex A ℤ} (f : I ⟶ I') (p : ℤ) :
    (mappingCoconeMap S sq f).f p ≫
        (CochainComplex.mappingCocone.fst (secondMap S sq I')).f p =
      (CochainComplex.mappingCocone.fst (secondMap S sq I)).f p ≫
        (biprod.map ((complexFunctor S sq.X₃).map f)
          ((complexFunctor S sq.X₂).map f)).f p := by
  simp only [cocone_fst_f, fst_v_eq, mappingCoconeMap]
  exact mapArrowHom_f_fstX _ _ _ _ _

/-- The induced map of mapping cocones is compatible with the second projections. -/
theorem mappingCoconeMap_f_snd_v {I I' : CochainComplex A ℤ} (f : I ⟶ I') (p : ℤ) :
    (mappingCoconeMap S sq f).f p ≫
        (CochainComplex.mappingCocone.snd (secondMap S sq I')).v p (p + -1) rfl =
      (CochainComplex.mappingCocone.snd (secondMap S sq I)).v p (p + -1) rfl ≫
        ((complexFunctor S sq.X₁).map f).f (p + -1) := by
  simp only [cocone_snd_v, snd_v_eq, mappingCoconeMap]
  exact mapArrowHom_f_sndX _ _ _

/-- The first map is natural in the complex. -/
theorem firstMap_natural {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (complexFunctor S sq.X₄).map f ≫ firstMap S sq I' =
      firstMap S sq I ≫ biprod.map ((complexFunctor S sq.X₃).map f)
        ((complexFunctor S sq.X₂).map f) := by
  apply biprod.hom_ext <;>
    simp [firstMap, restrictionComplex, NatTrans.naturality]

/-- The chain-level canonical maps commute with chain maps. -/
theorem cSquare_natural {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (complexFunctor S sq.X₄).map f ≫ cSquare S sq I' =
      cSquare S sq I ≫ mappingCoconeMap S sq f := by
  refine hom_ext _ (fun p => ?_) (fun p => ?_)
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      cSquare, CochainComplex.mappingCocone.lift_f_fst_f, mappingCoconeMap_f_fst_f,
      ← Category.assoc, cSquare, CochainComplex.mappingCocone.lift_f_fst_f]
    exact congrArg (fun z => HomologicalComplex.Hom.f z p) (firstMap_natural S sq f)
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      cSquare, CochainComplex.mappingCocone.lift_f_snd_v, mappingCoconeMap_f_snd_v,
      ← Category.assoc, cSquare, CochainComplex.mappingCocone.lift_f_snd_v]
    simp

end Chain

section Derived

open HomologicalComplex

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- Changing a K-injective representative gives an isomorphic arrow in the derived category of
the value category.

Two K-injective representatives of the same derived object are homotopy equivalent, and
the chain-level canonical map is natural; the induced map of mapping cocones is inverted
by the localization functor because it is the third component of a morphism of
distinguished triangles whose other two components are inverted. -/
theorem cSquare_arrow_iso_of_isKInjective (K : DerivedCategory A) (I I' : CochainComplex A ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ K) (e' : DerivedCategory.Q.obj I' ≅ K) :
    Nonempty (Arrow.mk (DerivedCategory.Q.map (cSquare S sq I)) ≅
      Arrow.mk (DerivedCategory.Q.map (cSquare S sq I'))) := by
  obtain ⟨he⟩ := nonempty_homotopyEquiv_of_derivedIso I I' (e.trans e'.symm)
  have hsec : ∀ U : ι, IsIso (DerivedCategory.Q.map ((complexFunctor S U).map he.hom)) := by
    intro U
    have : QuasiIso ((complexFunctor S U).map he.hom) := by
      rw [← HomologicalComplex.mem_quasiIso_iff]
      exact homotopyEquivalences_le_quasiIso _ _ _ ⟨(S.obj (op U)).mapHomotopyEquiv he, rfl⟩
    infer_instance
  have h₃ := hsec sq.X₃
  have h₂ := hsec sq.X₂
  have hbip : IsIso (DerivedCategory.Q.map (biprod.map ((complexFunctor S sq.X₃).map he.hom)
      ((complexFunctor S sq.X₂).map he.hom))) :=
    isIso_map_biprod_map DerivedCategory.Q _ _
  have hcone : QuasiIso (CochainComplex.mappingCone.map _ _ _ _
      (secondMapArrowMap S sq he.hom).w.symm) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap _ _ _ _ (secondMapArrowMap S sq he.hom).w.symm))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) hbip (hsec sq.X₁)
  have hcocone : IsIso (DerivedCategory.Q.map (mappingCoconeMap S sq he.hom)) := by
    have : QuasiIso (mappingCoconeMap S sq he.hom) := by
      rw [mappingCoconeMap, mapArrowHom_eq_coneMap]
      exact (CochainComplex.quasiIso_shift_iff _ _).2 hcone
    infer_instance
  have h₄ := hsec sq.X₄
  refine ⟨Arrow.isoMk (asIso (DerivedCategory.Q.map ((complexFunctor S sq.X₄).map he.hom)))
    (asIso (DerivedCategory.Q.map (mappingCoconeMap S sq he.hom))) ?_⟩
  dsimp
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, cSquare_natural]

end Derived

end Stacks.MayerVietoris.CanonicalMapOfComplexes.General

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes

open MappingCoconeAux

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}

/-- Degreewise sections of a complex of module sheaves. -/
noncomputable abbrev sectionsComplex (R : Sheaf J RingCat.{r}) (U : C) :
    CochainComplex (SheafOfModules.{v} R) ℤ ⥤ CochainComplex AddCommGrpCat.{v} ℤ :=
  General.complexFunctor (sectionsSystem R) U

/-- Restriction along an identity is the identity. -/
theorem sectionsRestriction_id (R : Sheaf J RingCat.{r}) (U : C) :
    sectionsRestriction.{u, v} R (𝟙 U) = 𝟙 (sections R U) :=
  (sectionsSystem.{u, v} R).map_id (op U)

/-- Restriction is contravariantly functorial. -/
theorem sectionsRestriction_comp (R : Sheaf J RingCat.{r}) {U V W : C} (f : U ⟶ V)
    (g : V ⟶ W) :
    sectionsRestriction.{u, v} R (f ≫ g) =
      sectionsRestriction R g ≫ sectionsRestriction R f :=
  (sectionsSystem.{u, v} R).map_comp g.op f.op

/-- Degreewise restriction of sections.  An `abbrev`, so that the general engine's lemmas and
the structure fields spelled with `General.restrictionComplex` match this spelling by `rw`. -/
noncomputable abbrev sectionsRestrictionComplex (R : Sheaf J RingCat.{r}) {U V : C}
    (f : U ⟶ V) :
    sectionsComplex.{u, v} R V ⟶ sectionsComplex.{u, v} R U :=
  General.restrictionComplex (sectionsSystem R) f

/-- Degreewise restriction along an identity is the identity. -/
theorem sectionsRestrictionComplex_id (R : Sheaf J RingCat.{r}) (U : C) :
    sectionsRestrictionComplex.{u, v} R (𝟙 U) = 𝟙 (sectionsComplex R U) :=
  General.restrictionComplex_id (sectionsSystem R) U

/-- Degreewise restriction is contravariantly functorial. -/
theorem sectionsRestrictionComplex_comp (R : Sheaf J RingCat.{r}) {U V W : C} (f : U ⟶ V)
    (g : V ⟶ W) :
    sectionsRestrictionComplex.{u, v} R (f ≫ g) =
      sectionsRestrictionComplex R g ≫ sectionsRestrictionComplex R f :=
  General.restrictionComplex_comp (sectionsSystem R) f g

variable {R : Sheaf J RingCat.{r}} (sq : Square C)

/-- The map `I(X) ⟶ I(Z) ⊞ I(Y)`. -/
@[stacks 0F16 "the map alpha"]
noncomputable def firstMap (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    (sectionsComplex R sq.X₄).obj I ⟶
      (sectionsComplex R sq.X₃).obj I ⊞ (sectionsComplex R sq.X₂).obj I :=
  General.firstMap (sectionsSystem R) sq I

/-- The signed map `I(Z) ⊞ I(Y) ⟶ I(E)`. -/
@[stacks 0F16 "the map beta"]
noncomputable def secondMap (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    (sectionsComplex R sq.X₃).obj I ⊞ (sectionsComplex R sq.X₂).obj I ⟶
      (sectionsComplex R sq.X₁).obj I :=
  General.secondMap (sectionsSystem R) sq I

/-- The canonical map `I(X) ⟶ C(β)[-1]`, using the zero null-homotopy. -/
@[stacks 0F16 "the canonical map of complexes"]
noncomputable def cSquare (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    (sectionsComplex R sq.X₄).obj I ⟶ CochainComplex.mappingCocone (secondMap sq I) :=
  General.cSquare (sectionsSystem R) sq I

/-- Signed restriction maps compose to zero. -/
@[stacks 0F16 "the relation beta composed with alpha is zero"]
theorem firstMap_comp_secondMap (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    firstMap sq I ≫ secondMap sq I = 0 :=
  General.firstMap_comp_secondMap (sectionsSystem R) sq I

/-- The morphism of signed restriction arrows induced by a chain map.  Spelled as an explicit
`Arrow.homMk'` of the two degreewise maps, with its commutativity taken from the general
engine, so that the components are visible to `simp`. -/
noncomputable def secondMapArrowMap
    {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    Arrow.mk (secondMap sq I) ⟶ Arrow.mk (secondMap sq I') :=
  Arrow.homMk'
    (biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f))
    ((sectionsComplex R sq.X₁).map f)
    (by exact (General.secondMapArrowMap (sectionsSystem R) sq f).w)

/-- The induced map of mapping cocones. -/
noncomputable def mappingCoconeMap
    {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    CochainComplex.mappingCocone (secondMap sq I) ⟶
      CochainComplex.mappingCocone (secondMap sq I') :=
  General.mappingCoconeMap (sectionsSystem R) sq f

/-- The induced map of mapping cocones is compatible with the first projections. -/
theorem mappingCoconeMap_f_fst_f {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I')
    (p : ℤ) :
    (mappingCoconeMap sq f).f p ≫
        (CochainComplex.mappingCocone.fst (secondMap sq I')).f p =
      (CochainComplex.mappingCocone.fst (secondMap sq I)).f p ≫
        (biprod.map ((sectionsComplex R sq.X₃).map f)
          ((sectionsComplex R sq.X₂).map f)).f p :=
  General.mappingCoconeMap_f_fst_f (sectionsSystem R) sq f p

/-- The induced map of mapping cocones is compatible with the second projections. -/
theorem mappingCoconeMap_f_snd_v {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I')
    (p : ℤ) :
    (mappingCoconeMap sq f).f p ≫
        (CochainComplex.mappingCocone.snd (secondMap sq I')).v p (p + -1) rfl =
      (CochainComplex.mappingCocone.snd (secondMap sq I)).v p (p + -1) rfl ≫
        ((sectionsComplex R sq.X₁).map f).f (p + -1) :=
  General.mappingCoconeMap_f_snd_v (sectionsSystem R) sq f p

/-- The first map is natural in the complex of module sheaves. -/
theorem firstMap_natural {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (sectionsComplex R sq.X₄).map f ≫ firstMap sq I' =
      firstMap sq I ≫ biprod.map ((sectionsComplex R sq.X₃).map f)
        ((sectionsComplex R sq.X₂).map f) :=
  General.firstMap_natural (sectionsSystem R) sq f

/-- The chain-level canonical maps commute with chain maps. -/
@[stacks 0F16 "functoriality on complexes"]
theorem cSquare_natural {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (sectionsComplex R sq.X₄).map f ≫ cSquare sq I' =
      cSquare sq I ≫ mappingCoconeMap sq f :=
  General.cSquare_natural (sectionsSystem R) sq f

section

open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard sheafSections_obj_additive

variable [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Changing a K-injective representative gives an isomorphic arrow in `D(Ab)`.

Two K-injective representatives of the same derived object are homotopy equivalent, and
the chain-level canonical map is natural; the induced map of mapping cocones is inverted
by the localization functor because it is the third component of a morphism of
distinguished triangles whose other two components are inverted. -/
@[stacks 0F16 "independence of the K-injective representative"]
theorem cSquare_arrow_iso_of_isKInjective
    (K : DerivedCategory (SheafOfModules.{v} R))
    (I I' : CochainComplex (SheafOfModules.{v} R) ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (_ : DerivedCategory.Q.obj I ≅ K) (_ : DerivedCategory.Q.obj I' ≅ K) :
    Nonempty (Arrow.mk (DerivedCategory.Q.map (cSquare sq I)) ≅
      Arrow.mk (DerivedCategory.Q.map (cSquare sq I'))) := by
  rename_i e e'
  exact General.cSquare_arrow_iso_of_isKInjective (sectionsSystem R) sq K I I' e e'

end

end Stacks.MayerVietoris.CanonicalMapOfComplexes

end
