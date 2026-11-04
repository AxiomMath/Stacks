module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtIdealPowerRestrict
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictFunctorOpensRange
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIso

/-!
# The `Ext`-colimit statement of Stacks 0G2H in `RestrictionLifting` form

Let `X` be a scheme, `𝓘` a quasi-coherent sheaf of ideals, `V` an open disjoint from the support
of `𝓘`, and `𝓖`, `𝓕` two `𝒪_X`-modules. The core case of [Stacks, Tag 0G2H] is the bijectivity
of

`colim_n Ext^i_X(𝓘^n𝓖, 𝓕) ⟶ Ext^i_V(𝓖|_V, 𝓕|_V)`

and for `i = 0` it is proved in
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtIdealPowerRestrict`, in
terms of the canonical map
`Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict`, whose source is indexed by
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul` and whose transitions are the
inclusions `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap`.

The dévissage uses that statement through
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange`, whose two hypotheses are
stated for a bare inverse sequence `S : ℕᵒᵖ ⥤ X.Modules` in terms of
`CategoryTheory.Abelian.Ext.mapExactFunctor` and the transitions `tr S`, and the sequence it is
applied to is `Stacks.Duality.idealPowerSystem 𝓘 𝓖`, the sequence `n ↦ 𝓘^n𝓖` of
[Stacks, Tag 0G4R].

This file identifies the two forms. The objects agree on the nose
(`Stacks.Duality.idealPowerSystem_obj`) and so do the transitions
(`Stacks.AlgebraicGeometry.IdealPowerColimit.tr_idealPowerSystem_eq`); what has to be unwound is
the comparison `(𝓘^n𝓖)|_V ≅ 𝓖|_V` that `extIdealPowRestrict` composes with and the
`RestrictionLifting` hypotheses do not, which is a cancellation of two
`CategoryTheory.Abelian.Ext.mk₀`'s.

The comparison is stated for an arbitrary degree `i`; the degree-zero instance
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem_degreeZero` is
unconditional, and is the case `p = q` of the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.tr_idealPowerSystem_eq`: the transitions of
  `Stacks.Duality.idealPowerSystem` are the inclusions of the ideal-power filtration.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mapExactFunctor_eq_of_surjective`: the
  `hlift` hypothesis, from surjectivity of
  `Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict` in degree `i`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_comp_eq_of_injective`: the `heq`
  hypothesis, from its injectivity in degree `i`.
* `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem`: **the core case of
  [Stacks, Tag 0G2H] in degree `i`, in `RestrictionLifting` form, from the `Ext`-colimit
  statement in degree `i`.**
* `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem_degreeZero`: its
  unconditional degree-zero instance.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open InverseSequence
open Stacks.AlgebraicGeometry.IdealPower

universe w u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The ideal-power inverse sequence and the filtration inclusions -/

/-- **The transitions of the inverse sequence `n ↦ 𝓘^n𝓖` are the inclusions of the ideal-power
filtration.** `Stacks.Duality.idealPowerSystem` is assembled from its successive inclusions, so
this is `Stacks.Duality.tr_idealPowerSystem` read through
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap`, the two being the same inclusion
of submodules. -/
public theorem tr_idealPowerSystem_eq (I : X.IdealSheafData) (G : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    tr (Stacks.Duality.idealPowerSystem I G) h = idealPowSmulMap I G h :=
  Stacks.Duality.tr_idealPowerSystem I G h

/-! ### Unwinding the comparison `(𝓘^n𝓖)|_V ≅ 𝓖|_V` -/

section Splice

variable (I : X.IdealSheafData) (V : X.Opens)
  (hV : Disjoint (V : Set X) (I.support : Set X))

/-- `Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict` written out: the
restriction of the class, precomposed with the comparison `𝓖|_V ≅ (𝓘^n𝓖)|_V`. -/
public theorem extIdealPowRestrict_eq_mk₀_comp [HasExt.{w} X.Modules]
    [HasExt.{w} V.toScheme.Modules] {G F : X.Modules} {i n : ℕ}
    (ξ : Ext.{w} (idealPowSmul I n G) F i) :
    extIdealPowRestrict.{w, w} I V hV ξ =
      (Ext.mk₀ (restrictIdealPowSmulIso I V hV n G).inv).comp
        (ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι)) (zero_add i) :=
  rfl

/-- The surjectivity half of the core case of [Stacks, Tag 0G2H], restated at a stage past a
given one: a class on `V` with source `(𝓘^n𝓖)|_V` is, up to the comparison
`restrictIdealPowSmulIso` and past some stage `m ≥ n`, the restriction of a class on `X`.

This is the `hlift` hypothesis of
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange` with the transition map
of the inverse sequence written as the filtration inclusion `idealPowSmulMap`. The comparison is
unwound by `restrict_idealPowSmulMap_comp_hom`, and the stage is pushed past `n` by
`extIdealPowRestrict_mk₀_comp`. -/
public theorem exists_mapExactFunctor_eq_of_surjective' [HasExt.{w} X.Modules]
    [HasExt.{w} V.toScheme.Modules] {G F : X.Modules} {i : ℕ}
    (hsurj : ∀ η : Ext.{w} ((Scheme.Modules.restrictFunctor V.ι).obj G)
        ((Scheme.Modules.restrictFunctor V.ι).obj F) i,
      ∃ (n : ℕ) (ξ : Ext.{w} (idealPowSmul I n G) F i),
        extIdealPowRestrict.{w, w} I V hV ξ = η)
    (n : ℕ) (η : Ext.{w} ((Scheme.Modules.restrictFunctor V.ι).obj (idealPowSmul I n G))
      ((Scheme.Modules.restrictFunctor V.ι).obj F) i) :
    ∃ (m : ℕ) (h : n ≤ m) (ξ : Ext.{w} (idealPowSmul I m G) F i),
      ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) =
        (Ext.mk₀ ((Scheme.Modules.restrictFunctor V.ι).map (idealPowSmulMap I G h))).comp η
          (zero_add i) := by
  obtain ⟨k, ξ, hξ⟩ :=
    hsurj ((Ext.mk₀ (restrictIdealPowSmulIso I V hV n G).inv).comp η (zero_add i))
  refine ⟨max k n, le_max_right k n,
    (Ext.mk₀ (idealPowSmulMap I G (le_max_left k n))).comp ξ (zero_add i), ?_⟩
  have h1 := (extIdealPowRestrict_mk₀_comp I V hV (le_max_left k n) ξ).trans hξ
  rw [extIdealPowRestrict_eq_mk₀_comp] at h1
  have h2 := congrArg (fun z : Ext.{w} ((Scheme.Modules.restrictFunctor V.ι).obj G)
      ((Scheme.Modules.restrictFunctor V.ι).obj F) i =>
    (Ext.mk₀ (restrictIdealPowSmulIso I V hV (max k n) G).hom).comp z (zero_add i)) h1
  simp only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp] at h2
  rw [(Iso.eq_comp_inv _).mpr (restrict_idealPowSmulMap_comp_hom I V hV (le_max_right k n) G)]
  simpa only [Ext.mk₀_comp_mk₀_assoc] using h2

/-- The injectivity half of the core case of [Stacks, Tag 0G2H], restated for a pair of classes:
two classes in `Ext^i_X(𝓘^n𝓖, 𝓕)` with the same restriction to `V` agree on `𝓘^{n+N}𝓖` for some
`N`.

This is the `heq` hypothesis of
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange` with the transition map of
the inverse sequence written as the filtration inclusion `idealPowSmulMap`. It is the hypothesis
applied to the difference of the two classes, which is legitimate because
`CategoryTheory.Abelian.Ext.mapExactFunctor` and Yoneda composition are both additive. -/
public theorem exists_mk₀_comp_eq_of_injective' [HasExt.{w} X.Modules]
    [HasExt.{w} V.toScheme.Modules] {G F : X.Modules} {i : ℕ}
    (hinj : ∀ (n : ℕ) (ζ : Ext.{w} (idealPowSmul I n G) F i),
      extIdealPowRestrict.{w, w} I V hV ζ = 0 →
      ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ζ (zero_add i) = 0)
    (n : ℕ) (ξ ξ' : Ext.{w} (idealPowSmul I n G) F i)
    (hξ : ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) =
      ξ'.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι)) :
    ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ξ (zero_add i) =
      (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ξ' (zero_add i) := by
  have hmap : (ξ - ξ').mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) =
      ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) -
        ξ'.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) :=
    map_sub ((Scheme.Modules.restrictFunctor V.ι).mapExtAddHom (idealPowSmul I n G) F i) ξ ξ'
  rw [hξ, sub_self] at hmap
  obtain ⟨N, hN⟩ :=
    hinj n (ξ - ξ') (by rw [extIdealPowRestrict_eq_mk₀_comp, hmap, Ext.comp_zero])
  refine ⟨N, ?_⟩
  have hsplit : (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp (ξ - ξ')
        (zero_add i) =
      (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ξ (zero_add i) -
        (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ξ' (zero_add i) := by
    rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, ← sub_eq_add_neg]
  rw [hsplit] at hN
  exact sub_eq_zero.mp hN

/-- **The `hlift` hypothesis of
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange` for the inverse sequence
`Stacks.Duality.idealPowerSystem 𝓘 𝓖`.** The objects of that sequence are the `𝓘^n𝓖` on the nose
and its transitions are the filtration inclusions
(`Stacks.AlgebraicGeometry.IdealPowerColimit.tr_idealPowerSystem_eq`), so this is
`exists_mapExactFunctor_eq_of_surjective'` read through those two identifications. -/
public theorem exists_mapExactFunctor_eq_of_surjective [HasExt.{w} X.Modules]
    [HasExt.{w} V.toScheme.Modules] {G F : X.Modules} {i : ℕ}
    (hsurj : ∀ η : Ext.{w} ((Scheme.Modules.restrictFunctor V.ι).obj G)
        ((Scheme.Modules.restrictFunctor V.ι).obj F) i,
      ∃ (n : ℕ) (ξ : Ext.{w} (idealPowSmul I n G) F i),
        extIdealPowRestrict.{w, w} I V hV ξ = η)
    (n : ℕ) (η : Ext.{w} ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Stacks.Duality.idealPowerSystem I G).obj (op n)))
      ((Scheme.Modules.restrictFunctor V.ι).obj F) i) :
    ∃ (m : ℕ) (h : n ≤ m)
      (ξ : Ext.{w} ((Stacks.Duality.idealPowerSystem I G).obj (op m)) F i),
      ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) =
        (Ext.mk₀ ((Scheme.Modules.restrictFunctor V.ι).map
          (tr (Stacks.Duality.idealPowerSystem I G) h))).comp η (zero_add i) := by
  obtain ⟨m, h, ξ, hξ⟩ := exists_mapExactFunctor_eq_of_surjective' I V hV hsurj n η
  refine ⟨m, h, ?_⟩
  rw [tr_idealPowerSystem_eq]
  exact ⟨ξ, hξ⟩

/-- **The `heq` hypothesis of
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange` for the inverse sequence
`Stacks.Duality.idealPowerSystem 𝓘 𝓖`**, from `exists_mk₀_comp_eq_of_injective'` and the
identification of the transitions with the filtration inclusions. -/
public theorem exists_mk₀_comp_eq_of_injective [HasExt.{w} X.Modules]
    [HasExt.{w} V.toScheme.Modules] {G F : X.Modules} {i : ℕ}
    (hinj : ∀ (n : ℕ) (ζ : Ext.{w} (idealPowSmul I n G) F i),
      extIdealPowRestrict.{w, w} I V hV ζ = 0 →
      ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ζ (zero_add i) = 0)
    (n : ℕ) (ξ ξ' : Ext.{w} ((Stacks.Duality.idealPowerSystem I G).obj (op n)) F i)
    (hξ : ξ.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) =
      ξ'.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι)) :
    ∃ (m : ℕ) (h : n ≤ m),
      (Ext.mk₀ (tr (Stacks.Duality.idealPowerSystem I G) h)).comp ξ (zero_add i) =
        (Ext.mk₀ (tr (Stacks.Duality.idealPowerSystem I G) h)).comp ξ' (zero_add i) := by
  obtain ⟨N, hN⟩ := exists_mk₀_comp_eq_of_injective' I V hV hinj n ξ ξ' hξ
  refine ⟨n + N, Nat.le_add_right n N, ?_⟩
  rw [tr_idealPowerSystem_eq]
  exact hN

end Splice

end Stacks.AlgebraicGeometry.IdealPowerColimit

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.IdealPowerColimit

variable {U X : Scheme.{u}}

/-- **The core case of [Stacks, Tag 0G2H] in degree `i`, in `RestrictionLifting` form.**
Let `j : U ⟶ X` be an open immersion whose image is disjoint from the support of the
quasi-coherent sheaf of ideals `𝓘`. If the canonical map
`colim_n Ext^i_X(𝓘^n𝓖, 𝓕) ⟶ Ext^i_{j(U)}(𝓖|, 𝓕|)` of
`Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict` is surjective and injective in
the stagewise sense of `hsurj` and `hinj`, then the system `(𝓘^n𝓖)` placed in degree `p`
satisfies the identification of the tag against `𝓕` placed in degree `q`, for `q + i = p`.

This is the hypothesis `hext` of
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree`, hence — through
it — the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`. -/
public lemma restrictionLifting_singleFunctor_idealPowerSystem (j : U ⟶ X)
    [IsOpenImmersion j] [HasExt.{w} X.Modules] [HasExt.{w} j.opensRange.toScheme.Modules]
    (I : X.IdealSheafData) (hj : Disjoint (j.opensRange : Set X) (I.support : Set X))
    (G F : X.Modules) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p)
    (hsurj : ∀ η : Ext.{w} ((Scheme.Modules.restrictFunctor j.opensRange.ι).obj G)
        ((Scheme.Modules.restrictFunctor j.opensRange.ι).obj F) i,
      ∃ (n : ℕ) (ξ : Ext.{w} (idealPowSmul I n G) F i),
        extIdealPowRestrict.{w, w} I j.opensRange hj ξ = η)
    (hinj : ∀ (n : ℕ) (ζ : Ext.{w} (idealPowSmul I n G) F i),
      extIdealPowRestrict.{w, w} I j.opensRange hj ζ = 0 →
      ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ζ (zero_add i) = 0) :
    RestrictionLifting
      (Stacks.Duality.idealPowerSystem I G ⋙ DerivedCategory.singleFunctor X.Modules p)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory
      ((DerivedCategory.singleFunctor X.Modules q).obj F) :=
  restrictionLifting_singleFunctor_of_ext_opensRange j
    (Stacks.Duality.idealPowerSystem I G) F p q i hi
    (exists_mapExactFunctor_eq_of_surjective I j.opensRange hj hsurj)
    (exists_mk₀_comp_eq_of_injective I j.opensRange hj hinj)

/-- **The core case of [Stacks, Tag 0G2H] in degree `0`.** The degree-zero instance of
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem`, whose two hypotheses are
the first display of [Stacks, Tag 01YB]: `hsurj` is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq` and `hinj` is
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero`
in degree `0`. It is the case `p = q` of the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`, and is unconditional. -/
public lemma restrictionLifting_singleFunctor_idealPowerSystem_degreeZero [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [HasExt.{w} X.Modules]
    [HasExt.{w} j.opensRange.toScheme.Modules] (I : X.IdealSheafData)
    (hj : j.opensRange = I.support.compl) (G F : X.Modules) [G.IsCoherent]
    [F.IsQuasicoherent] (p : ℤ) :
    RestrictionLifting
      (Stacks.Duality.idealPowerSystem I G ⋙ DerivedCategory.singleFunctor X.Modules p)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory
      ((DerivedCategory.singleFunctor X.Modules p).obj F) :=
  restrictionLifting_singleFunctor_idealPowerSystem j I
    (disjoint_support_of_eq_supportCompl hj) G F p p 0 (by simp)
    (fun η => exists_extIdealPowRestrict_eq.{w, w} I j.opensRange hj G F η)
    (fun _ ζ hζ =>
      exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero.{w, w} I j.opensRange hj ζ hζ)

end AlgebraicGeometry

end
