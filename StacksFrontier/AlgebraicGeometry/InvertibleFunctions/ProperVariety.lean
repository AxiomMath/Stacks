module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Invertible functions on an open subscheme of a proper variety

Stacks Tag 04L4 says that for `k` an algebraically closed field, `Xbar` a proper variety over `k`
and `X ⊆ Xbar` a *normal* open subscheme, the group `𝒪^*(X)/k^*` is finitely generated.

The divisor-theoretic heart of the argument is
`AlgebraicGeometry.fg_units_quotient_of_constant_globalUnits`
(`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/Basic.lean`), which proves the conclusion
for an open of a normal integral Noetherian scheme all of whose invertible global functions are
constants. This file supplies the two things that turn that into the tag.

* The hypothesis on the global units holds for *any* proper variety over an algebraically closed
  field, and needs no cohomology: Mathlib's `AlgebraicGeometry.isField_of_universallyClosed` and
  `AlgebraicGeometry.finite_appTop_of_universallyClosed` make `Γ(Xbar, ⊤)` a field finite over
  `k`, and a finite extension of an algebraically closed field is trivial. This is the content of
  Tag 04L2 (4) that Tag 04L4 uses, obtained here directly rather than through Tag 0BUG.
* The passage from an open *subscheme* given by an open immersion `j : X ⟶ Z` to the open
  `j ''ᵁ ⊤` of `Z`, through the isomorphism `AlgebraicGeometry.Scheme.Hom.appIso` on sections.

What remains for Tag 04L4 is the reduction to a *normal* proper variety, which is Tag 0BXR: the
normalization `ν : Xbar^ν ⟶ Xbar` is finite with `Xbar^ν` a normal variety, and `ν` restricts to
an isomorphism over the normal open `X`. It appears below as the hypothesis `hmodel` of
`AlgebraicGeometry.fg_units_quotient_of_exists_normal_model`, which is in all other respects
exactly the statement of the tag.

## Main results

* `AlgebraicGeometry.surjective_appTop_of_isAlgClosed`: the global functions on a proper variety
  over an algebraically closed field are the constants.
* `AlgebraicGeometry.forall_units_mem_range_of_isAlgClosed`: hence so are the invertible global
  functions.
* `AlgebraicGeometry.fg_units_quotient_of_isOpenImmersion_into_normal_properVariety`: Tag 04L4 for
  an open subscheme of a *normal* proper variety.
* `AlgebraicGeometry.fg_units_quotient_of_exists_normal_model`: Tag 04L4 with the reduction to the
  normal case (Tag 0BXR) as a hypothesis.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Stacks Tag 04L2 (4) for an algebraically closed base field.** The ring of global functions
on a proper variety over an algebraically closed field is the base field: by
`AlgebraicGeometry.isField_of_universallyClosed` it is a field, by
`AlgebraicGeometry.finite_appTop_of_universallyClosed` it is finite over `k`, and a finite -- hence
integral -- extension of an algebraically closed field is trivial. -/
theorem surjective_appTop_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperVariety k f] :
    Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
  let : Module.Finite k Γ(X, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k f).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))
  have : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).surjective

/-- Every invertible global function on a proper variety over an algebraically closed field is a
constant, coming from a unit of the base field. -/
theorem forall_units_mem_range_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProperVariety k f] (s : Γ(X, ⊤)ˣ) :
    s ∈ (Units.map (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range := by
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
  obtain ⟨c, hc⟩ := surjective_appTop_of_isAlgClosed k f (s : Γ(X, ⊤))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact s.ne_zero (by simpa using hc.symm)
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩

/-- Tag 04L4 for an open of a normal proper variety, phrased with the open as a member of
`AlgebraicGeometry.Scheme.Opens`. -/
theorem fg_units_quotient_opens_of_normal_properVariety (k : Type u) [Field k] [IsAlgClosed k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsProperVariety k g]
    (hnorm : ∀ V : Z.affineOpens, IsIntegrallyClosed Γ(Z, V.1))
    (V : Z.Opens) (hV : (V : Set Z).Nonempty) :
    Group.FG (Γ(Z, V)ˣ ⧸ (Units.map
      ((Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toMonoidHom).range) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType g
  have hgen : genericPoint Z ∈ V :=
    (genericPoint_spec (α := Z)).mem_open_set_iff V.isOpen |>.mpr (by simpa using hV)
  exact fg_units_quotient_of_constant_globalUnits hnorm _
    (forall_units_mem_range_of_isAlgClosed k g) hgen

/-- The restriction to the image of an open immersion, followed by the induced isomorphism on
sections, is the map on global sections. -/
private theorem map_le_top_comp_appIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Z.presheaf.map (homOfLE (le_top : (j ''ᵁ (⊤ : X.Opens)) ≤ ⊤)).op ≫ (j.appIso ⊤).hom
      = j.appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, Scheme.Hom.appTop]
  convert Category.comp_id (j.app ⊤) using 2
  rw [Subsingleton.elim (homOfLE (le_top.trans (Scheme.Hom.preimage_top j).ge))
    (𝟙 (⊤ : X.Opens))]
  simp

/-- **Stacks Tag 04L4 for a normal proper variety.** Let `k` be an algebraically closed field, let
`Z` be a proper variety over `k` whose rings of sections on affine opens are integrally closed,
and let `j : X ⟶ Z` be an open immersion. Then the invertible functions on `X` modulo the
constants form a finitely generated group.

This is the tag for the case where the ambient proper variety is already normal; the general case
reduces to it by Tag 0BXR. -/
theorem fg_units_quotient_of_isOpenImmersion_into_normal_properVariety
    (k : Type u) [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsProperVariety k g]
    (hnorm : ∀ V : Z.affineOpens, IsIntegrallyClosed Γ(Z, V.1))
    (j : X ⟶ Z) [IsOpenImmersion j] :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appTop).hom).toMonoidHom).range) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · -- an empty source has only the trivial unit group
    have h1 : Subsingleton (Γ(X, ⊤)ˣ) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    have : Finite (Γ(X, ⊤)ˣ) := @Finite.of_subsingleton _ h1
    infer_instance
  set V : Z.Opens := j ''ᵁ ⊤ with hVdef
  have hV : (V : Set Z).Nonempty :=
    ⟨j.base (Classical.arbitrary X), ⟨Classical.arbitrary X, trivial, rfl⟩⟩
  have hFG := fg_units_quotient_opens_of_normal_properVariety k g hnorm V hV
  set φZ : k →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom with hφZ
  set ψ : k →+* Γ(Z, V) :=
    (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp φZ with hψ
  set φX : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appTop).hom with hφX
  let ε : Γ(Z, V) ≃+* Γ(X, ⊤) := (j.appIso ⊤).commRingCatIsoToRingEquiv
  have hkey : ∀ c : k, ε (ψ c) = φX c := by
    intro c
    have h := map_le_top_comp_appIso j
    have h2 : ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appTop)
        = ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ j.appTop := by
      rw [Scheme.Hom.comp_appTop, Category.assoc]
    change ((j.appIso ⊤).hom.hom) (((Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) (φZ c)) = _
    rw [hφX, h2]
    change _ = j.appTop.hom (φZ c)
    rw [← h]
    rfl
  have hle : (Units.map ψ.toMonoidHom).range ≤
      ((Units.map φX.toMonoidHom).range).comap (Units.mapEquiv ε.toMulEquiv).toMonoidHom := by
    rintro u ⟨c, rfl⟩
    exact ⟨c, Units.ext (hkey c).symm⟩
  refine Group.fg_of_surjective (f := QuotientGroup.map _ _
    (Units.mapEquiv ε.toMulEquiv).toMonoidHom hle) ?_
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨QuotientGroup.mk ((Units.mapEquiv ε.toMulEquiv).symm u), ?_⟩
  rw [QuotientGroup.map_mk]
  congr 1
  ext
  simp

/-- **Stacks Tag 04L4, modulo Tag 0BXR.** Let `k` be an algebraically closed field, let `Xbar` be
a proper variety over `k` and let `X` be a normal open subscheme of it. If `X` is also an open
subscheme of some *normal* proper variety over `k`, compatibly with the structure morphisms, then
the invertible functions on `X` modulo the constants form a finitely generated group.

The hypothesis `hmodel` is what Tag 0BXR provides, with `Z` the normalization of `Xbar`: it is
finite over `Xbar`, hence proper over `k`, it is a normal variety, and it restricts to an
isomorphism over the normal open `X`. Everything else in this statement is the tag. -/
theorem fg_units_quotient_of_exists_normal_model (k : Type u) [Field k] [IsAlgClosed k]
    {X Xbar : Scheme.{u}} (f : Xbar ⟶ Spec (.of k)) [IsProperVariety k f]
    (i : X ⟶ Xbar) [IsOpenImmersion i] [IsNormal X]
    (hmodel : ∃ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) (_ : IsProperVariety k g)
      (_ : ∀ V : Z.affineOpens, IsIntegrallyClosed Γ(Z, V.1)) (j : X ⟶ Z)
      (_ : IsOpenImmersion j), j ≫ g = i ≫ f) :
    letI φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map φ.toMonoidHom).range) := by
  obtain ⟨Z, g, _, hnorm, j, _, hcomm⟩ := hmodel
  have h := fg_units_quotient_of_isOpenImmersion_into_normal_properVariety k g hnorm j
  rw [hcomm] at h
  exact h

end AlgebraicGeometry

end
