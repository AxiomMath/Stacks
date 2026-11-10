module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingImmersion
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The centre of an étale chart is cut out by a regular sequence

On an étale chart `g : U ⟶ 𝐀^{m+n}_R` of a closed immersion `i : Z ⟶ X` of schemes smooth over
`S` (`Stacks.DeRham.BlowupEtaleChart`), the pullbacks of the last `n` coordinates `y₁, …, y_n`
lie in the ideal of `Z`, and on every affine open inside `U` they form a weakly regular sequence:
they do in the polynomial ring, and `g` is flat.  So `Ext^k(i_*𝒢|_V, ℰ|_V) = 0` for `k < n`, for
every `𝒪_Z`-module `𝒢`, every affine open `V ⊆ U` and every `𝒪_X`-module `ℰ` free on `V`
([Stacks, Tag 0G5I], in the affine case).  This is the local input of the uniqueness half of
[Stacks, Tag 0G5J].

## Main results

* `MvPolynomial.isWeaklyRegular_ofFn_X_inr`: the last `n` variables of `R[x₁, …, x_m, y₁, …, y_n]`
  form a weakly regular sequence.
* `Stacks.DeRham.BlowupEtaleChart.subsingleton_ext_restrict_pushforward`: the vanishing of `Ext`
  above, on an affine open inside a chart.

## References

* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace MvPolynomial

/-- **The last `n` variables of `R[x₁, …, x_m, y₁, …, y_n]` form a weakly regular sequence**, with
no hypothesis on `R`. -/
@[sga "6 VII 1.2" "partial"]
theorem isWeaklyRegular_ofFn_X_inr (R : Type u) [CommRing R] (m n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin m ⊕ Fin n) R)
      (List.ofFn fun j : Fin n => (X (Sum.inr j) : MvPolynomial (Fin m ⊕ Fin n) R)) := by
  cases n with
  | zero => exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  | succ n =>
    let e : MvPolynomial (Fin m ⊕ Fin (n + 1)) R ≃+*
        MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m) R) :=
      ((renameEquiv R (Equiv.sumComm (Fin m) (Fin (n + 1)))).trans
        (sumAlgEquiv R (Fin (n + 1)) (Fin m))).toRingEquiv
    have he : ∀ j : Fin (n + 1), e (X (Sum.inr j)) = X j := fun j => by
      simp [e, sumAlgEquiv_X_inl]
    have h := isWeaklyRegular_ofFn_X (R := MvPolynomial (Fin m) R) n
    have h' := Stacks.AlgebraicGeometry.isWeaklyRegular_map_of_flat e.symm.toRingHom
      (RingHom.Flat.of_bijective e.symm.bijective) h
    simpa [List.map_ofFn, Function.comp_def, ← he] using h'

end MvPolynomial

namespace Stacks.DeRham.BlowupEtaleChart

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X} (c : BlowupEtaleChart f i)

/-- The `j`-th of the last `n` coordinates `y_j`, pulled back to an open `V ⊆ U` of a chart. -/
noncomputable abbrev coordinateSection {V : X.Opens} (hVU : V ≤ c.U) (j : Fin c.n) :
    Γ(V.toScheme, ⊤) :=
  (X.homOfLE hVU ≫ c.g).appTop
    (Stacks.MoreMorphisms.gammaEquiv c.R c.m c.n (MvPolynomial.X (Sum.inr j)))

/-- **On an affine open inside a chart the coordinates `y_j` form a weakly regular sequence.** -/
theorem isWeaklyRegular_coordinateSection {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ c.U) :
    RingTheory.Sequence.IsWeaklyRegular Γ(V.toScheme, ⊤)
      (List.ofFn (c.coordinateSection hVU)) := by
  have : IsAffine V.toScheme := hV
  have hflat : (X.homOfLE hVU ≫ c.g).appTop.hom.Flat :=
    HasRingHomProperty.appTop (P := @Flat) _ inferInstance
  have h := Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat
    ((X.homOfLE hVU ≫ c.g).appTop.hom.comp
      (Stacks.MoreMorphisms.gammaEquiv c.R c.m c.n).toRingHom)
    ((RingHom.Flat.of_bijective
      (Stacks.MoreMorphisms.gammaEquiv c.R c.m c.n).bijective).comp hflat) _
    (MvPolynomial.isWeaklyRegular_ofFn_X_inr c.R c.m c.n)
  exact h

end Stacks.DeRham.BlowupEtaleChart


namespace Stacks.DeRham.BlowupEtaleChart

open Stacks.AlgebraicGeometry.RegularIdealSheaf
variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X} (c : BlowupEtaleChart f i)

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

/-- The coordinate subspace kills the last `n` coordinates. -/
theorem coordinateEmbedding_appTop_X_inr (R : Type u) [CommRing R] (m n : ℕ) (j : Fin n) :
    (Stacks.MoreMorphisms.coordinateEmbedding R m n).appTop
      (Stacks.MoreMorphisms.gammaEquiv R m n (MvPolynomial.X (Sum.inr j))) = 0 := by
  have h := Stacks.MoreMorphisms.gammaEquiv_coordinateEmbedding_appTop R m n
    (Stacks.MoreMorphisms.gammaEquiv R m n (MvPolynomial.X (Sum.inr j)))
  rw [RingEquiv.symm_apply_apply] at h
  have h0 : Stacks.MoreMorphisms.coordinateProjection R m n (MvPolynomial.X (Sum.inr j)) = 0 := by
    simp [Stacks.MoreMorphisms.coordinateProjection]
  rw [h0] at h
  exact (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R))).commRingCatIsoToRingEquiv.injective
    (h.trans (map_zero _).symm)

/-- **The coordinates `y_j` vanish on the centre.**  On an open `V` inside a chart, the pullback
of `y_j` lies in the ideal of `Z`: its image in `Γ(Z, i⁻¹V)` is zero. -/
theorem coordinateSection_mem_definingIdealOfHom [IsClosedImmersion i] {V : X.Opens}
    (hVU : V ≤ c.U) (j : Fin c.n) :
    V.topIso.hom (c.coordinateSection hVU j) ∈ (definingIdealOfHom i).obj (op V) := by
  change (i.app V).hom (V.topIso.hom (c.coordinateSection hVU j)) = 0
  have hres : (i ∣_ V) ≫ X.homOfLE hVU =
      Z.homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ c.U from fun x hx => hVU hx) ≫ (i ∣_ c.U) := by
    rw [← cancel_mono c.U.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have key : (i ∣_ V).appTop (c.coordinateSection hVU j) = 0 := by
    have h1 : ((i ∣_ V) ≫ X.homOfLE hVU ≫ c.g).appTop
        (Stacks.MoreMorphisms.gammaEquiv c.R c.m c.n (MvPolynomial.X (Sum.inr j))) = 0 := by
      rw [← Category.assoc, hres, Category.assoc, ← c.centreMap_comm, ← Category.assoc,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateEmbedding_appTop_X_inr,
        map_zero]
    simpa only [coordinateSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h1
  rw [morphismRestrict_appTop] at key
  simp only at key
  have key' : (i.app (V.ι ''ᵁ ⊤)).hom (c.coordinateSection hVU j) = 0 := by
    refine (Z.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage i V ⊤)).op
      ).commRingCatIsoToRingEquiv.injective ?_
    rw [map_zero]
    exact key
  have hnat := Scheme.Hom.naturality i (eqToHom V.ι_image_top.symm).op
  have := congrArg (fun φ => φ.hom (c.coordinateSection hVU j)) hnat
  simp only [CommRingCat.hom_comp] at this
  have e : V.topIso.hom = X.presheaf.map (eqToHom V.ι_image_top.symm).op := rfl
  rw [e]
  refine this.trans ?_
  change (Z.presheaf.map _).hom ((i.app (V.ι ''ᵁ ⊤)).hom (c.coordinateSection hVU j)) = 0
  rw [key', map_zero]

attribute [local instance] HasDerivedCategory.standard HasExt.standard

/-- **[Stacks, Tag 0G5I] on an affine open of a chart.**  Let `V ⊆ U` be an affine open inside a
chart of codimension `n`, let `𝒢` be an `𝒪_Z`-module and let `ℰ` be an `𝒪_X`-module which is free
on `V`.  Then `Ext^k(i_*𝒢|_V, ℰ|_V) = 0` for `k < n`: the coordinates `y₁, …, y_n` form a weakly
regular sequence on `V` killing `i_*𝒢`. -/
theorem subsingleton_ext_restrict_pushforward [IsClosedImmersion i] {V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ c.U) (G : Z.Modules) (E : X.Modules) (ι : Type u)
    (e : E.restrict V.ι ≅ SheafOfModules.free.{u} ι) (k : ℕ) (hk : k < c.n) :
    Subsingleton (Abelian.Ext (((Scheme.Modules.pushforward i).obj G).restrict V.ι)
      (E.restrict V.ι) k) := by
  have : IsAffine V.toScheme := hV
  refine Stacks.RegularSequence.subsingleton_ext_of_isAffine_of_iso_free _ _ ι e
    (List.ofFn (c.coordinateSection hVU)) ?_ (c.isWeaklyRegular_coordinateSection hV hVU) k
    (by simpa using hk)
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  have h := globalSmulCenter_restrict_pushforward_eq_zero i G V _
    (c.coordinateSection_mem_definingIdealOfHom hVU j)
  rwa [Iso.hom_inv_id_apply] at h

end Stacks.DeRham.BlowupEtaleChart

end
