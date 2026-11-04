module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Roofs of quasi-isomorphisms

Two cochain complexes `K` and `L` in an abelian category are joined by a *roof of
quasi-isomorphisms* when there is a complex `G` and quasi-isomorphisms `K ⟶ G ⟵ L`. This is a
condition on complexes alone: it mentions no derived category, and so it can be stated, assumed
and transported without choosing a model of `D(C)`. In every model of the derived category it is
the same as an isomorphism `Q(K) ≅ Q(L)` (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`), since
every morphism of the derived category is a left fraction (`DerivedCategory.left_fac`).

## Main definitions

* `CochainComplex.QuasiIsoRoof`: a left fraction for the quasi-isomorphisms (Mathlib's
  `CategoryTheory.MorphismProperty.LeftFraction`) whose numerator is a quasi-isomorphism too.

## Main results

* `CochainComplex.quasiIsoRoof_iff`: a roof is a pair of quasi-isomorphisms into a common
  complex.
* `CochainComplex.QuasiIsoRoof.of_quasiIso`, `.of_iso`, `.symm`, `.precomp`, `.precomp_right`,
  `.precomp_right_iso` and `.map`: a quasi-isomorphism or an isomorphism gives a roof, roofs are
  symmetric, can be precomposed with quasi-isomorphisms on either side, in particular with an
  isomorphism on the second leg, and are carried along exact functors.
* `CochainComplex.quasiIsoRoof_iff_nonempty_iso`: in any model of the derived category, a roof
  between `K` and `L` exists exactly when `Q(K) ≅ Q(L)`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂ w

namespace CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- A **roof of quasi-isomorphisms** `K ⟶ G ⟵ L`: a left fraction for the quasi-isomorphisms
(Mathlib's `MorphismProperty.LeftFraction`) whose numerator is also a quasi-isomorphism. It is
model-free; in every model of `D(C)` it is an isomorphism `Q K ≅ Q L`
(`quasiIsoRoof_iff_nonempty_iso`). -/
def QuasiIsoRoof (K L : CochainComplex C ℤ) : Prop :=
  ∃ φ : (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).LeftFraction K L, QuasiIso φ.f

/-- A roof of quasi-isomorphisms between `K` and `L` is a complex `G` together with
quasi-isomorphisms `K ⟶ G` and `L ⟶ G`. -/
theorem quasiIsoRoof_iff {K L : CochainComplex C ℤ} :
    QuasiIsoRoof K L ↔
      ∃ (G : CochainComplex C ℤ) (f : K ⟶ G) (s : L ⟶ G), QuasiIso f ∧ QuasiIso s :=
  ⟨fun ⟨φ, hf⟩ => ⟨φ.Y', φ.f, φ.s, hf, φ.hs⟩, fun ⟨_, f, s, hf, hs⟩ => ⟨⟨f, s, hs⟩, hf⟩⟩

namespace QuasiIsoRoof

/-- A quasi-isomorphism `K ⟶ L` is a roof, with the identity of `L` as its second leg. -/
theorem of_quasiIso {K L : CochainComplex C ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIsoRoof K L :=
  ⟨MorphismProperty.LeftFraction.ofHom _ f, hf⟩

/-- An isomorphism of complexes is a roof. -/
theorem of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) : QuasiIsoRoof K L :=
  of_quasiIso e.hom (quasiIso_of_isIso e.hom)

/-- A roof read backwards is a roof: both of its legs are quasi-isomorphisms. -/
theorem symm {K L : CochainComplex C ℤ} (h : QuasiIsoRoof K L) : QuasiIsoRoof L K := by
  obtain ⟨φ, hf⟩ := h
  exact ⟨⟨φ.s, φ.f, hf⟩, φ.hs⟩

/-- A roof out of `K` precomposed with a quasi-isomorphism `K' ⟶ K` is a roof out of `K'`. -/
theorem precomp {K K' L : CochainComplex C ℤ} (k : K' ⟶ K) (hk : QuasiIso k)
    (h : QuasiIsoRoof K L) : QuasiIsoRoof K' L := by
  obtain ⟨φ, hf⟩ := h
  exact ⟨⟨k ≫ φ.f, φ.s, φ.hs⟩, quasiIso_comp _ _ (hφ := hk) (hφ' := hf)⟩

/-- A roof into `L` precomposed with a quasi-isomorphism `L' ⟶ L` on its second leg is a roof
into `L'`. -/
theorem precomp_right {K L L' : CochainComplex C ℤ} (l : L' ⟶ L) (hl : QuasiIso l)
    (h : QuasiIsoRoof K L) : QuasiIsoRoof K L' :=
  (h.symm.precomp l hl).symm

/-- A roof into `L` precomposed with an isomorphism `L' ≅ L` on its second leg is a roof into
`L'`. -/
theorem precomp_right_iso {K L L' : CochainComplex C ℤ} (e : L' ≅ L) (h : QuasiIsoRoof K L) :
    QuasiIsoRoof K L' :=
  h.precomp_right e.hom (quasiIso_of_isIso e.hom)

/-- An exact functor carries a roof of quasi-isomorphisms to a roof of quasi-isomorphisms between
the images of the complexes. -/
theorem map {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] {K L : CochainComplex C ℤ} (h : QuasiIsoRoof K L) :
    QuasiIsoRoof ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  obtain ⟨φ, hf⟩ := h
  have : QuasiIso φ.s := φ.hs
  exact ⟨⟨(F.mapHomologicalComplex _).map φ.f, (F.mapHomologicalComplex _).map φ.s,
    HomologicalComplex.quasiIso_map_of_preservesHomology φ.s F⟩,
    HomologicalComplex.quasiIso_map_of_preservesHomology φ.f F⟩

end QuasiIsoRoof

/-- **The bridge to every model of the derived category.** Two complexes are joined by a roof of
quasi-isomorphisms exactly when their images in the derived category are isomorphic.

A roof gives `Q(f) ≫ Q(s)⁻¹`. Conversely an isomorphism `e : Q(K) ≅ Q(L)` is a left fraction
`Q(γ) ≫ Q(s)⁻¹` (`DerivedCategory.left_fac`); `s` is a quasi-isomorphism, and so is `γ`, since
`Q(γ) = e ≫ Q(s)` is an isomorphism. -/
theorem quasiIsoRoof_iff_nonempty_iso [HasDerivedCategory.{w} C] (K L : CochainComplex C ℤ) :
    QuasiIsoRoof K L ↔ Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) := by
  constructor
  · rintro ⟨φ, hf⟩
    have : QuasiIso φ.s := φ.hs
    exact ⟨asIso (DerivedCategory.Q.map φ.f) ≪≫ (asIso (DerivedCategory.Q.map φ.s)).symm⟩
  · rintro ⟨e⟩
    obtain ⟨G, γ, s, hs, fac⟩ := DerivedCategory.left_fac e.hom
    have hγ : DerivedCategory.Q.map γ = e.hom ≫ DerivedCategory.Q.map s := by simp [fac]
    have : IsIso (DerivedCategory.Q.map γ) := by rw [hγ]; infer_instance
    exact quasiIsoRoof_iff.2 ⟨G, γ, s, (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := γ)).1 this,
      (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs⟩

end CochainComplex
