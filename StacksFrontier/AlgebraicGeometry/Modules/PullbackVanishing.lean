module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Vanishing of a homomorphism of modules and of its inverse images

A homomorphism of sheaves of modules on a scheme is zero as soon as it is zero on the members of
an open cover, and inverse image along a morphism detects or preserves this vanishing in the
expected ways.

## Main results

* `AlgebraicGeometry.Scheme.Modules.hom_eq_zero_of_app_eq_zero_of_iSup_eq_top` and
  `AlgebraicGeometry.Scheme.Modules.hom_eq_zero_of_pullback_ι_map_eq_zero`: vanishing is local on
  an open cover, in the sectionwise and in the inverse-image formulation.
* `AlgebraicGeometry.Scheme.Modules.pullback_comp_map_eq_zero_iff` and
  `AlgebraicGeometry.Scheme.Modules.pullback_map_eq_zero_of_comp`: inverse image along a
  composition.
* `AlgebraicGeometry.Scheme.Modules.pullback_map_eq_zero_iff_of_isIso`: inverse image along an
  isomorphism neither creates nor destroys vanishing.
* `AlgebraicGeometry.Scheme.Modules.pullback_ι_map_eq_zero_of_fromSpec`: on an affine open it
  suffices to test vanishing on the spectrum of the ring of sections.

## Implementation notes

Inverse image along a morphism of schemes is only pseudofunctorial, so a statement about
`Scheme.Modules.pullback (f ≫ g)` must be mediated by `Scheme.Modules.pullbackComp`; the
comparison is an isomorphism, which is why vanishing transports along it in both directions.
Faithfulness of inverse image along an isomorphism is obtained from the same comparison together
with `Scheme.Modules.pullbackCongr` and `Scheme.Modules.pullbackId`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X Y Z : Scheme.{u}}

/-! ### Locality of vanishing -/

/-- **Vanishing of a homomorphism of modules is local.**  A homomorphism of sheaves of modules
which kills every section over every open subset contained in some member of an open cover is
zero. -/
theorem hom_eq_zero_of_app_eq_zero_of_iSup_eq_top {M N : X.Modules} {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (φ : M ⟶ N)
    (hlocal : ∀ i (V : X.Opens), V ≤ U i → ∀ x, φ.app V x = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  set W : ι → X.Opens := fun i => V ⊓ U i with hWdef
  have hW : iSup W = V := by
    calc iSup W = V ⊓ iSup U := by simp [hWdef, inf_iSup_eq]
      _ = V := by simp [hU]
  set P := N.presheaf with hP
  set y : P.obj (op (iSup W)) := P.map (eqToHom hW).op (φ.app V x) with hy
  have hz := (Scheme.Modules.isSheaf N).isSeparated (iSup W)
    (Sieve.generate (TopCat.Presheaf.presieveOfCovering W))
    (TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology W) y 0 ?_
  · have hzMap : (P.map (eqToHom hW).op).hom (φ.app V x) = (P.map (eqToHom hW).op).hom 0 := by
      simpa [hy, hP] using hz
    exact (ConcreteCategory.bijective_of_isIso (P.map (eqToHom hW).op)).injective hzMap
  · intro T f hf
    obtain ⟨A, h, g, hg, hcomp⟩ := hf
    obtain ⟨i, hAi⟩ := hg
    subst A
    rw [show g = homOfLE (le_iSup W i) from Subsingleton.elim _ _] at hcomp
    have hres : P.map (homOfLE (le_iSup W i)).op y = 0 := by
      have hmapEq : P.map (eqToHom hW).op ≫ P.map (homOfLE (le_iSup W i)).op =
          P.map (homOfLE (inf_le_left : W i ≤ V)).op := by
        rw [← Functor.map_comp, ← op_comp,
          show homOfLE (le_iSup W i) ≫ eqToHom hW = homOfLE (inf_le_left : W i ≤ V) from
            Subsingleton.elim _ _]
      have hnat : (N.presheaf.map (homOfLE (inf_le_left : W i ≤ V)).op).hom (φ.app V x) =
          φ.app (W i) ((M.presheaf.map (homOfLE (inf_le_left : W i ≤ V)).op).hom x) := by
        simpa using
          (congrArg (fun q => q x)
            (φ.mapPresheaf.naturality (homOfLE (inf_le_left : W i ≤ V)).op)).symm
      change (P.map (eqToHom hW).op ≫ P.map (homOfLE (le_iSup W i)).op).hom (φ.app V x) = 0
      rw [hmapEq, hnat]
      exact hlocal i (W i) inf_le_right _
    rw [show f.op = (homOfLE (le_iSup W i)).op ≫ h.op by rw [← op_comp, hcomp], Functor.map_comp]
    change (N.presheaf.map h.op).hom ((N.presheaf.map (homOfLE (le_iSup W i)).op).hom y) =
      (N.presheaf.map h.op).hom ((N.presheaf.map (homOfLE (le_iSup W i)).op).hom 0)
    rw [hres]
    simp

/-- **Vanishing of a homomorphism of modules is local, in inverse-image form.**  A homomorphism
of sheaves of modules whose inverse image along the inclusion of each member of an open cover is
zero is itself zero. -/
theorem hom_eq_zero_of_pullback_ι_map_eq_zero {M N : X.Modules} {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (φ : M ⟶ N)
    (hlocal : ∀ i, (Scheme.Modules.pullback (U i).ι).map φ = 0) : φ = 0 := by
  apply hom_eq_zero_of_app_eq_zero_of_iSup_eq_top U hU φ
  intro i V hV x
  set f := (U i).ι with hf
  have hRestr : (Scheme.Modules.restrictFunctor f).map φ = 0 := by
    rw [← Preadditive.IsIso.comp_right_eq_zero
        (g := (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N),
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality φ, hlocal i, Limits.comp_zero]
  have hV' : f ''ᵁ (f ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hV
  have hcomp := congrArg (fun g => g.app (f ⁻¹ᵁ V)) hRestr
  change φ.app (f ''ᵁ (f ⁻¹ᵁ V)) = 0 at hcomp
  rw [hV'] at hcomp
  exact congrArg (fun q => q x) hcomp

/-! ### Inverse image along a composition -/

/-- **Vanishing of an inverse image along a composition.**  The inverse image of a homomorphism
of modules along a composition is zero exactly when the iterated inverse image is. -/
theorem pullback_comp_map_eq_zero_iff (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback (f ≫ g)).map φ = 0 ↔
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) = 0 := by
  rw [← Preadditive.IsIso.comp_left_eq_zero (f := (Scheme.Modules.pullbackComp f g).hom.app M),
    ← (Scheme.Modules.pullbackComp f g).hom.naturality φ, Preadditive.IsIso.comp_right_eq_zero,
    Functor.comp_map]

/-- **An inverse image which already vanishes still vanishes after a further inverse image.** -/
theorem pullback_map_eq_zero_of_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N)
    (h : (Scheme.Modules.pullback g).map φ = 0) :
    (Scheme.Modules.pullback (f ≫ g)).map φ = 0 :=
  (pullback_comp_map_eq_zero_iff f g φ).2 (by rw [h]; simp)

/-! ### Inverse image along an isomorphism -/

/-- Inverse image of sheaves of modules along an isomorphism of schemes is faithful. -/
instance faithful_pullback_of_isIso (f : X ⟶ Y) [IsIso f] :
    (Scheme.Modules.pullback f).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.pullback (inv f))
    (Scheme.Modules.pullbackComp (inv f) f ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId Y)

/-- **Inverse image along an isomorphism detects vanishing.** -/
theorem pullback_map_eq_zero_iff_of_isIso (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map φ = 0 ↔ φ = 0 :=
  ⟨fun h => (Scheme.Modules.pullback f).map_injective (by simpa using h), fun h => by
    rw [h]; simp⟩

/-- **On an affine open it suffices to test vanishing on the spectrum of its ring of sections.**
If the inverse image of a homomorphism of modules along `IsAffineOpen.fromSpec` is zero, then so
is its inverse image along the inclusion of the affine open. -/
theorem pullback_ι_map_eq_zero_of_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {M N : X.Modules}
    (φ : M ⟶ N) (h : (Scheme.Modules.pullback hU.fromSpec).map φ = 0) :
    (Scheme.Modules.pullback U.ι).map φ = 0 := by
  have h' : (Scheme.Modules.pullback (hU.isoSpec.inv ≫ U.ι)).map φ = 0 := by
    rw [IsAffineOpen.isoSpec_inv_ι hU]; exact h
  exact (pullback_map_eq_zero_iff_of_isIso hU.isoSpec.inv _).1
    ((pullback_comp_map_eq_zero_iff hU.isoSpec.inv U.ι φ).1 h')

end AlgebraicGeometry.Scheme.Modules

end
