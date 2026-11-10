module

public import Mathlib.AlgebraicGeometry.Spec
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Denominators
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeSeminormalization

/-!
# Relative seminormalization and localization

For a dominant morphism of affine spectra, relative seminormalization commutes with localization
on the base.

## Main results

* `AlgebraicGeometry.mem_relativeSeminormalization_localization_iff` characterizes the localized
  relative seminormalization as the localization of the original relative seminormalization.

## Implementation notes

The equality of the two subalgebras is expressed elementwise in an arbitrary pair of localization
rings, and the right-hand side is the usual fraction description of the localization of the
original subalgebra. The dominance hypothesis for the localized map is an explicit argument,
because it is an argument of the chosen relative seminormalization.

Both inclusions go through the square-cube criterion
`AlgebraicGeometry.universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube`. For
the inclusion of the localization into the localized seminormalization, the localized base map is
a base change of the original one along a localization, so it stays a universal homeomorphism and
keeps its residue fields, and maximality of the localized seminormalization applies. For the
reverse inclusion, an element of the localized seminormalization sits in a square-cube tower over
the localization; `IsLocalization.exists_numerator_not_mem_of_localization` clears denominators in
the resulting membership conditions, producing a numerator which the original seminormalization
must already contain.

## References

* [Stacks Project, Tag 0H3M](https://stacks.math.columbia.edu/tag/0H3M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry


private theorem adjoin_square_cube_isUniversalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (E : Subalgebra A B) (y : B) (hy2 : y ^ 2 ∈ E) (hy3 : y ^ 3 ∈ E) :
    let X := Algebra.adjoin E ({y} : Set B)
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap E X)).op) ∧
      (∀ x, IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap E X)).op).residueFieldMap x)) := by
  let X := Algebra.adjoin E ({y} : Set B)
  have hinj : Function.Injective (algebraMap E X) :=
    fun _ _ hab => Subtype.ext (congrArg (fun z : X => (z : B)) hab)
  apply (universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube
    hinj).2
  intro F
  let b : Fin 1 → X := fun _ => ⟨y, Algebra.subset_adjoin (by simp)⟩
  have hrange : Set.range b = (Subtype.val : X → B) ⁻¹' ({y} : Set B) := by
    ext z
    simp [b, Subtype.ext_iff]
  have htop : Algebra.adjoin E (Set.range b) = ⊤ := by
    rw [hrange]
    exact Algebra.adjoin_adjoin_coe_preimage
  refine ⟨1, b, ?_, ?_⟩
  · rw [htop]
    exact Set.subset_univ _
  · intro i
    fin_cases i
    constructor
    · rw [show (b 0) ^ 2 = algebraMap E X ⟨y ^ 2, hy2⟩ from Subtype.ext rfl]
      exact (Algebra.adjoin E _).algebraMap_mem ⟨y ^ 2, hy2⟩
    · rw [show (b 0) ^ 3 = algebraMap E X ⟨y ^ 3, hy3⟩ from Subtype.ext rfl]
      exact (Algebra.adjoin E _).algebraMap_mem ⟨y ^ 3, hy3⟩

private theorem special_element_mem_relativeSeminormalization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (y : B) (hy2 : y ^ 2 ∈ relativeSeminormalization A B hdom)
    (hy3 : y ^ 3 ∈ relativeSeminormalization A B hdom) :
    y ∈ relativeSeminormalization A B hdom := by
  let C := relativeSeminormalization A B hdom
  let X := Algebra.adjoin C ({y} : Set B)
  let fAX : A →+* X := (algebraMap C X).comp (algebraMap A C)
  let : Algebra A X := fAX.toAlgebra
  have hCX := adjoin_square_cube_isUniversalHomeomorphism C y hy2 hy3
  have hAC : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) :=
    relativeSeminormalization_universalHomeomorphism A B hdom
  have : MorphismProperty.IsStableUnderComposition (@UniversalHomeomorphism.{u}) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition
  have hcomp := MorphismProperty.comp_mem (@UniversalHomeomorphism.{u})
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap C X)).op)
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) hCX.1 hAC
  have hmap :
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap C X)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op =
      Scheme.Spec.map (CommRingCat.ofHom fAX).op := by
    rw [← Scheme.Spec.map_comp]
    congr 1
  rw [hmap] at hcomp
  have hresComp : ∀ x, IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom fAX).op).residueFieldMap x) := by
    intro x
    let fCX := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C X)).op
    rw [← hmap, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      (relativeSeminormalization_residueFieldMap_isIso A B hdom (fCX x)) (hCX.2 x)
  let g : X →ₐ[A] B :=
    { toRingHom := X.val.toRingHom
      commutes' := by
        intro a
        change X.val (fAX a) = algebraMap A B a
        simp [fAX] }
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom fAX).op) := hcomp
  exact map_mem_relativeSeminormalization A B hdom g hresComp
    ⟨y, Algebra.subset_adjoin (by simp)⟩

private theorem residueFieldMap_isIso_of_stalkMap_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsIso (f.stalkMap x)) : IsIso (f.residueFieldMap x) := by
  change IsIso (CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom))
  let e := asIso (f.stalkMap x)
  let er := RingEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
  have hmap : IsLocalRing.ResidueField.map (f.stalkMap x).hom =
      (IsLocalRing.ResidueField.mapEquiv er).toRingHom := RingHom.ext fun _ => rfl
  rw [hmap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (IsLocalRing.ResidueField.mapEquiv er).bijective

private theorem localized_stalkMap_isIso
    {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    (S : Submonoid A) [IsLocalization S T]
    (x : Scheme.Spec.obj (Opposite.op (CommRingCat.of T))) :
    IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A T)).op).stalkMap x) := by
  let e : T ≃ₐ[A] Localization S := IsLocalization.algEquiv S T (Localization S)
  let i := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let qT := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A T)).op
  let qL := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (Localization S))).op
  have hring : e.toRingEquiv.toCommRingCatIso.inv.hom.comp
      (algebraMap A (Localization S)) = algebraMap A T := by
    ext a
    apply e.injective
    simp [e.commutes]
  have hmap : i.inv ≫ qL = qT := by
    change Scheme.Spec.map (e.toRingEquiv.toCommRingCatIso.inv.op) ≫
      Scheme.Spec.map ((CommRingCat.ofHom (algebraMap A (Localization S))).op) =
      Scheme.Spec.map ((CommRingCat.ofHom (algebraMap A T)).op)
    rw [← Scheme.Spec.map_comp]
    exact congrArg Scheme.Spec.map
      (congrArg Quiver.Hom.op (CommRingCat.hom_ext_iff.mpr hring))
  have hcomp : IsIso ((i.inv ≫ qL).stalkMap x) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso'
      (AlgebraicGeometry.isIso_specMap_stalkMap_localization
        (CommRingCat.of A) S (i.inv x)) inferInstance
  change IsIso (qT.stalkMap x)
  rw [← hmap]
  exact hcomp

private theorem localized_residueFieldMap_isIso
    {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    (S : Submonoid A) [IsLocalization S T]
    (x : Scheme.Spec.obj (Opposite.op (CommRingCat.of T))) :
    IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A T)).op).residueFieldMap x) :=
  residueFieldMap_isIso_of_stalkMap_isIso _ x (localized_stalkMap_isIso S x)

/-- Membership in the range of a ring map is transported along a compatible ring equivalence. -/
private theorem mem_range_equiv_iff
    {R P Q : Type u} [CommRing R] [CommRing P] [CommRing Q]
    (e : P ≃+* Q) (f : R →+* P) (g : R →+* Q) (h : e.toRingHom.comp f = g) (y : P) :
    e y ∈ Set.range g ↔ y ∈ Set.range f := by
  subst h
  exact ⟨fun ⟨z, hz⟩ => ⟨z, e.injective hz⟩, fun ⟨z, hz⟩ => ⟨z, congrArg e hz⟩⟩

/-- Localizing a submonoid of `A` in a subalgebra of `B` lands in its localization in `B`. -/
private theorem map_le_comap_subalgebra_val
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) (E : Subalgebra A B) :
    S.map (algebraMap A E) ≤ Submonoid.comap (E.val : E →+* B) (S.map (algebraMap A B)) := by
  intro z hz
  obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hz
  exact Submonoid.mem_map_of_mem (algebraMap A B) hs

private noncomputable def localizedBaseMap
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (S : Submonoid A) (Aₛ : Type u) [CommRing Aₛ] [Algebra A Aₛ]
    [IsLocalization S Aₛ] :
    Aₛ →+* Localization (S.map (algebraMap A C)) :=
  IsLocalization.map (Localization (S.map (algebraMap A C)))
    (algebraMap A C) S.le_comap_map

private noncomputable def localizedSubalgebraRingMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) (E : Subalgebra A B) (Bₛ : Type u)
    [CommRing Bₛ] [Algebra B Bₛ]
    [IsLocalization (S.map (algebraMap A B)) Bₛ] :
    Localization (S.map (algebraMap A E)) →+* Bₛ := by
  exact IsLocalization.map (M := S.map (algebraMap A E))
    (S := Localization (S.map (algebraMap A E))) (T := S.map (algebraMap A B)) Bₛ
    (E.val : E →+* B) (map_le_comap_subalgebra_val S E)

private theorem localized_square_cube_numerator_contradiction
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) (E : Subalgebra A B)
    (x : Localization (S.map (algebraMap A B)))
    (hx : x ∉ Set.range (localizedSubalgebraRingMap S E
      (Localization (S.map (algebraMap A B)))))
    (h2 : x ^ 2 ∈ Set.range (localizedSubalgebraRingMap S E
      (Localization (S.map (algebraMap A B)))))
    (h3 : x ^ 3 ∈ Set.range (localizedSubalgebraRingMap S E
      (Localization (S.map (algebraMap A B)))))
    (hspecial : ∀ y : B, y ^ 2 ∈ E → y ^ 3 ∈ E → y ∈ E) : False := by
  let T := S.map (algebraMap A E)
  let SB := S.map (algebraMap A B)
  let RE := Localization (T.map E.toSubring.subtype)
  have hmon : T.map E.toSubring.subtype = SB := by
    ext z
    change (∃ t ∈ T, E.toSubring.subtype t = z) ↔
      ∃ s ∈ S, algebraMap A B s = z
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, (E.val.commutes s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨algebraMap A E s, ⟨s, hs, rfl⟩, E.val.commutes s⟩
  have : IsLocalization SB RE := by
    rw [← hmon]
    infer_instance
  let e : Localization SB ≃ₐ[B] RE := IsLocalization.algEquiv SB (Localization SB) RE
  let cE : Localization T →+* RE :=
    IsLocalization.map (M := T) (S := Localization T) (T := T.map E.toSubring.subtype)
      RE E.toSubring.subtype T.le_comap_map
  have hcomp : e.toRingEquiv.toRingHom.comp
      (localizedSubalgebraRingMap S E (Localization SB)) = cE := by
    apply IsLocalization.ringHom_ext T
    ext a
    have hleft : localizedSubalgebraRingMap S E (Localization SB)
        (algebraMap E (Localization T) a) = algebraMap B (Localization SB) ((a : E) : B) := by
      simp [localizedSubalgebraRingMap, T, SB, IsLocalization.map_eq]
    have hright : cE (algebraMap E (Localization T) a) = algebraMap B RE ((a : E) : B) := by
      change cE (algebraMap E (Localization T) a) = algebraMap B RE (E.val a)
      exact IsLocalization.map_eq T.le_comap_map (a : E)
    change e (localizedSubalgebraRingMap S E (Localization SB)
        (algebraMap E (Localization T) a)) = cE (algebraMap E (Localization T) a)
    rw [hleft, e.commutes, hright]
  have hrange := mem_range_equiv_iff e.toRingEquiv _ _ hcomp
  have hx' : e x ∉ Set.range cE := fun h => hx ((hrange x).1 h)
  have h2' : (e x) ^ 2 ∈ Set.range cE := by
    rw [← map_pow]
    exact (hrange _).2 h2
  have h3' : (e x) ^ 3 ∈ Set.range cE := by
    rw [← map_pow]
    exact (hrange _).2 h3
  let b : Fin 3 → B := fun i => if i.val = 1 ∨ i.val = 2 then 1 else 0
  have hbx : ∀ i, algebraMap B RE (b i) * (e x) ^ (i.val + 1) ∈ Set.range cE := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [b]⟩
    · simpa [b] using h2'
    · simpa [b] using h3'
  obtain ⟨t, y, hxy, hyNot, hy⟩ :=
    IsLocalization.exists_numerator_not_mem_of_localization E.toSubring T b (e x) hx' hbx
  have hy2 : y ^ 2 ∈ E := by simpa [b] using hy ⟨1, by decide⟩
  have hy3 : y ^ 3 ∈ E := by simpa [b] using hy ⟨2, by decide⟩
  exact hyNot (hspecial y hy2 hy3)

private theorem localized_relativeSeminormalization_range_square_cube_closed
    {A B Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Bₛ] [Algebra A B]
    (S : Submonoid A) [Algebra B Bₛ]
    [IsLocalization (S.map (algebraMap A B)) Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (x : Bₛ)
    (h2 : x ^ 2 ∈ Set.range (localizedSubalgebraRingMap S
      (relativeSeminormalization A B hdom) Bₛ))
    (h3 : x ^ 3 ∈ Set.range (localizedSubalgebraRingMap S
      (relativeSeminormalization A B hdom) Bₛ)) :
    x ∈ Set.range (localizedSubalgebraRingMap S
      (relativeSeminormalization A B hdom) Bₛ) := by
  let E := relativeSeminormalization A B hdom
  let SB := S.map (algebraMap A B)
  let BLoc := Localization SB
  let e : Bₛ ≃ₐ[B] BLoc := IsLocalization.algEquiv SB Bₛ BLoc
  have hcomp : e.toRingEquiv.toRingHom.comp
      (localizedSubalgebraRingMap S E Bₛ) =
        localizedSubalgebraRingMap S E BLoc := by
    apply IsLocalization.ringHom_ext (S.map (algebraMap A E))
    ext c
    simp [localizedSubalgebraRingMap, SB, BLoc, IsLocalization.map_eq, e.commutes]
  by_contra hx
  have hrange := mem_range_equiv_iff e.toRingEquiv _ _ hcomp
  have hx' : e x ∉ Set.range (localizedSubalgebraRingMap S E BLoc) :=
    fun h => hx ((hrange x).1 h)
  have h2' : (e x) ^ 2 ∈ Set.range (localizedSubalgebraRingMap S E BLoc) := by
    rw [← map_pow]
    exact (hrange _).2 h2
  have h3' : (e x) ^ 3 ∈ Set.range (localizedSubalgebraRingMap S E BLoc) := by
    rw [← map_pow]
    exact (hrange _).2 h3
  exact localized_square_cube_numerator_contradiction S E (e x) hx' h2' h3'
    (special_element_mem_relativeSeminormalization hdom)

private theorem localizedBaseMap_universalHomeomorphism
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (S : Submonoid A) (Aₛ : Type u) [CommRing Aₛ] [Algebra A Aₛ]
    [IsLocalization S Aₛ]
    (hAC : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    let f := localizedBaseMap S Aₛ
    let _ : Algebra Aₛ (Localization (S.map (algebraMap A C))) := f.toAlgebra
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op) := by
  let f : Aₛ →+* Localization (S.map (algebraMap A C)) :=
    localizedBaseMap S Aₛ
  let : Algebra Aₛ (Localization (S.map (algebraMap A C))) := f.toAlgebra
  have hcomp : f.comp (algebraMap A Aₛ) =
      (algebraMap C (Localization (S.map (algebraMap A C)))).comp
        (algebraMap A C) := by
    simp [f, localizedBaseMap, IsLocalization.map_comp]
  have : IsScalarTower A Aₛ (Localization (S.map (algebraMap A C))) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid C S)
      (Localization (S.map (algebraMap A C))) := by
    change IsLocalization (S.map (algebraMap A C)) _
    infer_instance
  have hp : Algebra.IsPushout A C Aₛ (Localization (S.map (algebraMap A C))) :=
    Algebra.isPushout_of_isLocalization S Aₛ C
      (Localization (S.map (algebraMap A C)))
  have hsq : IsPullback
      (Scheme.Spec.map (CommRingCat.ofHom
        (algebraMap C (Localization (S.map (algebraMap A C))))).op)
      (Scheme.Spec.map (CommRingCat.ofHom f).op)
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A Aₛ)).op) := by
    apply isPullback_SpecMap_of_isPushout
    exact CommRingCat.isPushout_of_isPushout A C Aₛ
      (Localization (S.map (algebraMap A C)))
  exact (universalHomeomorphism_iff _).mpr
    (MorphismProperty.of_isPullback hsq hAC.universally_isHomeomorph)

private theorem localizedBaseMap_residueFieldMap_isIso
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (S : Submonoid A) (Aₛ : Type u) [CommRing Aₛ] [Algebra A Aₛ]
    [IsLocalization S Aₛ]
    (hres : ∀ x, IsIso ((Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap A C)).op).residueFieldMap x)) :
    let f := localizedBaseMap S Aₛ
    let _ : Algebra Aₛ (Localization (S.map (algebraMap A C))) := f.toAlgebra
    ∀ x, IsIso ((Scheme.Spec.map (CommRingCat.ofHom f).op).residueFieldMap x) := by
  let f : Aₛ →+* Localization (S.map (algebraMap A C)) :=
    localizedBaseMap S Aₛ
  let : Algebra Aₛ (Localization (S.map (algebraMap A C))) := f.toAlgebra
  let qC := Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap C (Localization (S.map (algebraMap A C))))).op
  let qA := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A Aₛ)).op
  let q := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  let g := Scheme.Spec.map (CommRingCat.ofHom f).op
  have hcomp : f.comp (algebraMap A Aₛ) =
      (algebraMap C (Localization (S.map (algebraMap A C)))).comp
        (algebraMap A C) := by
    simp [f, localizedBaseMap, IsLocalization.map_comp]
  have hcat : CommRingCat.ofHom (algebraMap A C) ≫
      CommRingCat.ofHom (algebraMap C (Localization (S.map (algebraMap A C)))) =
        CommRingCat.ofHom (algebraMap A Aₛ) ≫ CommRingCat.ofHom f :=
    CommRingCat.hom_ext_iff.mpr hcomp.symm
  have hmap : qC ≫ q = g ≫ qA := by
    rw [← Scheme.Spec.map_comp, ← Scheme.Spec.map_comp]
    exact congrArg Scheme.Spec.map (congrArg Quiver.Hom.op hcat)
  change (∀ x, IsIso ((Scheme.Spec.map (CommRingCat.ofHom f).op).residueFieldMap x))
  intro x
  have hleft : IsIso ((qC ≫ q).residueFieldMap x) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hres (qC x))
      (localized_residueFieldMap_isIso (A := C)
        (T := Localization (S.map (algebraMap A C))) (S.map (algebraMap A C)) x)
  have hcancel : ∀ {h : _ ⟶ _}, g ≫ qA = h → IsIso (h.residueFieldMap x) →
      IsIso (g.residueFieldMap x) := by
    rintro h rfl hh
    rw [Scheme.residueFieldMap_comp] at hh
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (localized_residueFieldMap_isIso (A := A) (T := Aₛ) S (g x)) hh
  exact hcancel hmap.symm hleft

private theorem universalHomeomorphism_cancel_right
    (A R D : Type u) [CommRing A] [CommRing R] [CommRing D]
    (f : A →+* R) (g : R →+* D)
    (hf : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op))
    (hcomp : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (g.comp f)).op)) :
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom g).op) := by
  let F := Scheme.Spec.map (CommRingCat.ofHom f).op
  let G := Scheme.Spec.map (CommRingCat.ofHom g).op
  let H := Scheme.Spec.map (CommRingCat.ofHom (g.comp f)).op
  have hGF : G ≫ F = H := by
    change Scheme.Spec.map (CommRingCat.ofHom g).op ≫
      Scheme.Spec.map (CommRingCat.ofHom f).op = _
    rw [← Scheme.Spec.map_comp]
    congr 1
  let : Algebra A R := f.toAlgebra
  let : Algebra R D := g.toAlgebra
  let : Algebra A D := (g.comp f).toAlgebra
  obtain ⟨hIcomp, hinjH, hsurjH⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective H).mp hcomp
  have hIG : IsIntegralHom G :=
    IsIntegralHom.SpecMap_iff.mpr fun x => RingHom.IsIntegralElem.of_comp (f := f) (g := g)
      ((IsIntegralHom.SpecMap_iff.mp hIcomp) x)
  have : UniversallyInjective F :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective F).mp hf).2.1
  have hfields := ((tfae_universallyInjective H).out 1 2).mp hinjH
  have hfieldsG : ∀ (K : Type u) [Field K],
      Function.Injective (fun φ : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶
        Scheme.Spec.obj (Opposite.op (CommRingCat.of D)) => φ ≫ G) := by
    intro K hK φ ψ hφψ
    apply hfields K
    change φ ≫ H = ψ ≫ H
    rw [← hGF]
    change φ ≫ G = ψ ≫ G at hφψ
    simpa [Category.assoc] using congrArg (fun q => q ≫ F) hφψ
  have : UniversallyInjective G :=
    ((tfae_universallyInjective G).out 1 2).mpr hfieldsG
  have hsurjG : Surjective G := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hsurjH.surj (F x)
    refine ⟨y, Scheme.Hom.injective F ?_⟩
    rw [← hGF] at hy
    change F (G y) = F x at hy
    exact hy
  exact
    (universalHomeomorphism_iff_integral_universallyInjective_surjective G).mpr
      ⟨hIG, inferInstance, hsurjG⟩

private theorem localized_subalgebra_range_iff_fraction
    {A B Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Bₛ] [Algebra A B]
    (S : Submonoid A) (E : Subalgebra A B) [Algebra B Bₛ]
    [IsLocalization (S.map (algebraMap A B)) Bₛ]
    (x : Bₛ) :
    x ∈ Set.range (localizedSubalgebraRingMap S E Bₛ) ↔
      ∃ b : B, b ∈ E ∧ ∃ s : S,
        x = IsLocalization.mk' Bₛ b
          ⟨algebraMap A B s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩ := by
  let SC := S.map (algebraMap A E)
  let SB := S.map (algebraMap A B)
  let f := localizedSubalgebraRingMap S E Bₛ
  have hSC := map_le_comap_subalgebra_val S E
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨b, t, ht⟩ := IsLocalization.exists_mk'_eq SC z
    obtain ⟨s, hs, hts⟩ := Submonoid.mem_map.mp t.2
    refine ⟨b, b.2, ⟨s, hs⟩, ?_⟩
    have hden : (E.val t.1 : B) = algebraMap A B s := by
      rw [← hts]
      simp
    calc
      x = f z := hz.symm
      _ = f (IsLocalization.mk' (Localization SC) b t) := by rw [ht]
      _ = IsLocalization.mk' Bₛ (b : B)
          ⟨algebraMap A B s, Submonoid.mem_map.mpr ⟨s, hs, rfl⟩⟩ := by
            change (IsLocalization.map (M := SC) (S := Localization SC)
              (T := SB) Bₛ E.val hSC)
              (IsLocalization.mk' (Localization SC) b t) = _
            rw [IsLocalization.map_mk']
            congr 1
            exact Subtype.ext hden
  · rintro ⟨b, hb, s, rfl⟩
    refine ⟨IsLocalization.mk' (Localization SC) ⟨b, hb⟩
      ⟨algebraMap A E s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩, ?_⟩
    change (IsLocalization.map (M := SC) (S := Localization SC)
      (T := SB) Bₛ E.val hSC)
      (IsLocalization.mk' (Localization SC) ⟨b, hb⟩
        ⟨algebraMap A E s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩) = _
    rw [IsLocalization.map_mk']
    congr 1

/-- An element of the relative seminormalization after localization is exactly a fraction whose
numerator belongs to the original relative seminormalization. -/
@[stacks 0H3M]
public theorem mem_relativeSeminormalization_localization_iff
    (A B Aₛ Bₛ : Type u) [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [Algebra A B] (S : Submonoid A)
    [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (S.map (algebraMap A B)) Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ]
    [Algebra Aₛ Bₛ] [IsScalarTower A Aₛ Bₛ]
    (hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hdomₛ : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ)).op))
    (x : Bₛ) :
    x ∈ relativeSeminormalization Aₛ Bₛ hdomₛ ↔
      ∃ (b : B), b ∈ relativeSeminormalization A B hdom ∧
        ∃ s : S, x = IsLocalization.mk' Bₛ b
          ⟨algebraMap A B s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩ :=
  by
  let E := relativeSeminormalization A B hdom
  let CLoc := Localization (S.map (algebraMap A E))
  let f : Aₛ →+* CLoc := localizedBaseMap S Aₛ
  let cB : CLoc →+* Bₛ := localizedSubalgebraRingMap S E Bₛ
  let : Algebra Aₛ CLoc := f.toAlgebra
  have hfc : f.comp (algebraMap A Aₛ) =
      (algebraMap E CLoc).comp (algebraMap A E) := by
    simpa [f, localizedBaseMap] using
      (IsLocalization.map_comp (M := S) (g := algebraMap A E)
        (hy := S.le_comap_map))
  have hbase0 : (cB.comp f).comp (algebraMap A Aₛ) =
      (algebraMap Aₛ Bₛ).comp (algebraMap A Aₛ) := by
    ext a
    calc
      cB (f (algebraMap A Aₛ a)) =
          cB (algebraMap E CLoc (algebraMap A E a)) :=
            congrArg cB (DFunLike.congr_fun hfc a)
      _ = algebraMap B Bₛ (algebraMap A B a) := by
        simp [cB, localizedSubalgebraRingMap, IsLocalization.map_eq]
      _ = algebraMap A Bₛ a :=
        (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B Bₛ) a).symm
      _ = algebraMap Aₛ Bₛ (algebraMap A Aₛ a) :=
        DFunLike.congr_fun (IsScalarTower.algebraMap_eq A Aₛ Bₛ) a
  have hbase : cB.comp f = algebraMap Aₛ Bₛ := IsLocalization.ringHom_ext S hbase0
  let g : CLoc →ₐ[Aₛ] Bₛ :=
    { toRingHom := cB
      commutes' := fun a => DFunLike.congr_fun hbase a }
  have hLoc : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op) := by
    simpa [f] using localizedBaseMap_universalHomeomorphism S Aₛ
      (relativeSeminormalization_universalHomeomorphism A B hdom)
  have hLocRes : ∀ z, IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom f).op).residueFieldMap z) := by
    simpa [f] using localizedBaseMap_residueFieldMap_isIso S Aₛ
      (relativeSeminormalization_residueFieldMap_isIso A B hdom)
  let D := relativeSeminormalization Aₛ Bₛ hdomₛ
  let qLoc := Scheme.Spec.map (CommRingCat.ofHom f).op
  let qD := Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ D)).op
  let : UniversalHomeomorphism qLoc := hLoc
  have hmax : ∀ z : CLoc, cB z ∈ D :=
    map_mem_relativeSeminormalization Aₛ Bₛ hdomₛ g hLocRes
  have hmon : (S.map (algebraMap A E)).map E.val = S.map (algebraMap A B) := by
    ext z
    simp [Submonoid.mem_map]
  let : IsLocalization ((S.map (algebraMap A E)).map E.val) Bₛ := by
    rw [hmon]
    infer_instance
  have hcB : Function.Injective cB := by
    let SC := S.map (algebraMap A E)
    let fEB : E →+* B := E.val.toRingHom
    have hSC := map_le_comap_subalgebra_val S E
    change Function.Injective (IsLocalization.map Bₛ fEB hSC)
    have htargetLoc : IsLocalization (SC.map fEB) Bₛ := by
      change IsLocalization ((S.map (algebraMap A E)).map E.val) Bₛ
      rw [hmon]
      infer_instance
    exact @IsLocalization.map_injective_of_injective
      E _ SC CLoc _ _ B _ inferInstance fEB Bₛ _ _ Subtype.val_injective htargetLoc
  let gD : CLoc →+* D := RingHom.codRestrict cB D hmax
  let : Algebra CLoc D := gD.toAlgebra
  have hCDbase : gD.comp f = algebraMap Aₛ D := by
    ext a
    change cB (f a) = algebraMap Aₛ Bₛ a
    exact DFunLike.congr_fun hbase a
  let : IsScalarTower Aₛ CLoc D :=
    IsScalarTower.of_algebraMap_eq' hCDbase.symm
  have hcat : CommRingCat.ofHom f ≫ CommRingCat.ofHom gD =
      CommRingCat.ofHom (algebraMap Aₛ D) := CommRingCat.hom_ext_iff.mpr hCDbase
  have hmap :
      Scheme.Spec.map (CommRingCat.ofHom gD).op ≫ qLoc = qD := by
    change Scheme.Spec.map (CommRingCat.ofHom gD).op ≫
      Scheme.Spec.map (CommRingCat.ofHom f).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₛ D)).op
    rw [← Scheme.Spec.map_comp]
    exact congrArg Scheme.Spec.map (congrArg Quiver.Hom.op hcat)
  have hcompUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (gD.comp f)).op) := by
    rw [hCDbase]
    exact relativeSeminormalization_universalHomeomorphism Aₛ Bₛ hdomₛ
  have hCDUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom gD).op) :=
    universalHomeomorphism_cancel_right Aₛ CLoc D f gD hLoc hcompUH
  have hDRes :=
    relativeSeminormalization_residueFieldMap_isIso Aₛ Bₛ hdomₛ
  have hCDRes : ∀ z, IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom gD).op).residueFieldMap z) := by
    intro z
    let qCD := Scheme.Spec.map (CommRingCat.ofHom gD).op
    have hqLoc := hLocRes (qCD z)
    let η := (Scheme.residueFieldCongr (congrArg (fun k => k z) hmap)).hom
    have hcongr : qLoc.residueFieldMap (qCD z) ≫ qCD.residueFieldMap z =
        η ≫ qD.residueFieldMap z := by
      rw [← Scheme.residueFieldMap_comp qCD qLoc z]
      rw [Scheme.Hom.residueFieldMap_congr hmap z]
    have hright : IsIso (η ≫ qD.residueFieldMap z) :=
      IsIso.comp_isIso' (inferInstance : IsIso η) (hDRes z)
    have hleft : IsIso (qLoc.residueFieldMap (qCD z) ≫ qCD.residueFieldMap z) := by
      rw [hcongr]
      exact hright
    let : IsIso (qLoc.residueFieldMap (qCD z)) := hqLoc
    let : IsIso (qLoc.residueFieldMap (qCD z) ≫ qCD.residueFieldMap z) := hleft
    exact IsIso.of_isIso_comp_left (qLoc.residueFieldMap (qCD z))
      (qCD.residueFieldMap z)
  have hcB' : Function.Injective (algebraMap CLoc D) := by
    change Function.Injective gD
    intro x y hxy
    apply hcB
    exact congrArg D.val hxy
  have hfinite :=
    (universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube
      hcB').mp ⟨hCDUH, hCDRes⟩
  let : Algebra CLoc Bₛ := cB.toAlgebra
  let j : D →ₐ[CLoc] Bₛ :=
    { toRingHom := D.val.toRingHom
      commutes' := by
        intro z
        change ((gD z : D) : Bₛ) = cB z
        rfl }
  let P : Subalgebra CLoc D :=
    Subalgebra.comap j (⊥ : Subalgebra CLoc Bₛ)
  have hseq_mem : ∀ (n : ℕ) (b : Fin n → D)
      (hstep : ∀ i : Fin n, b i ^ 2 ∈ Algebra.adjoin CLoc
        (Set.range (fun k : Fin i => b (Fin.castLE i.isLt.le k))) ∧
        b i ^ 3 ∈ Algebra.adjoin CLoc
        (Set.range (fun k : Fin i => b (Fin.castLE i.isLt.le k))))
      (i : Fin n), b i ∈ P := by
    intro n b hstep
    have hnum : ∀ k : ℕ, ∀ hk : k < n, b ⟨k, hk⟩ ∈ P := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          let i : Fin n := ⟨k, hk⟩
          have hpre : Algebra.adjoin CLoc
              (Set.range (fun t : Fin i => b (Fin.castLE i.isLt.le t))) ≤ P := by
            rw [Algebra.adjoin_le_iff]
            rintro z ⟨t, rfl⟩
            let jt : Fin n := Fin.castLE i.isLt.le t
            have hjk : jt.val < k := by simp [jt, i]
            have hjn : jt.val < n := lt_trans hjk hk
            have hprev := ih jt.val hjk hjn
            have hidx : Fin.castLE i.isLt.le t = (⟨jt.val, hjn⟩ : Fin n) := by
              apply Fin.ext
              rfl
            have hprev' := hprev
            rw [← hidx] at hprev'
            change b jt ∈ P
            exact hprev'
          have h2 := hpre (hstep i).1
          have h3 := hpre (hstep i).2
          have h2' : j (b i) ^ 2 ∈ (⊥ : Subalgebra CLoc Bₛ) := by
            change j (b i ^ 2) ∈ (⊥ : Subalgebra CLoc Bₛ) at h2
            simpa [map_pow] using h2
          have h3' : j (b i) ^ 3 ∈ (⊥ : Subalgebra CLoc Bₛ) := by
            change j (b i ^ 3) ∈ (⊥ : Subalgebra CLoc Bₛ) at h3
            simpa [map_pow] using h3
          have hr2 : (j (b i)) ^ 2 ∈ Set.range cB := by
            change (j (b i)) ^ 2 ∈ Set.range (algebraMap CLoc Bₛ)
            exact Algebra.mem_bot.mp h2'
          have hr3 : (j (b i)) ^ 3 ∈ Set.range cB := by
            change (j (b i)) ^ 3 ∈ Set.range (algebraMap CLoc Bₛ)
            exact Algebra.mem_bot.mp h3'
          have hmem := localized_relativeSeminormalization_range_square_cube_closed
            S (Bₛ := Bₛ) hdom (j (b i)) hr2 hr3
          change b i ∈ P at *
          exact Algebra.mem_bot.mpr hmem
    intro i
    simpa using hnum i.val i.isLt
  have hrev : ∀ y : Bₛ, y ∈ D → y ∈ Set.range cB := by
    intro y hy
    let d : D := ⟨y, hy⟩
    obtain ⟨n, b, hsubset, hstep⟩ := hfinite ({d} : Finset D)
    have hgen := hseq_mem n b hstep
    have hpre : Algebra.adjoin CLoc (Set.range b) ≤ P := by
      rw [Algebra.adjoin_le_iff]
      rintro z ⟨i, rfl⟩
      exact hgen i
    have hdP : d ∈ P := hpre (hsubset (by simp))
    have hdbot : j d ∈ (⊥ : Subalgebra CLoc Bₛ) := hdP
    change y ∈ Set.range cB
    change j d ∈ Set.range (algebraMap CLoc Bₛ)
    exact Algebra.mem_bot.mp hdbot
  have heq : x ∈ D ↔ x ∈ Set.range cB :=
    ⟨hrev x, by rintro ⟨z, rfl⟩; exact hmax z⟩
  exact heq.trans (localized_subalgebra_range_iff_fraction S E x)

end AlgebraicGeometry

end
