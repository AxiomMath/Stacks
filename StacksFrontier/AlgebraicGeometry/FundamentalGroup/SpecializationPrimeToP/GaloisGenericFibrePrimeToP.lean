module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationPrimeToP.DiscreteValuationRingReduction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.GaloisGenericFibreDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverAutSubgroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization maps are surjective and prime-to-`p` isomorphisms

This file completes [Stacks, Tag 0C0R]. What the library already had was the reduction of the tag
to one geometric statement, the hypothesis `Hgal` of
`surjective_and_exists_continuousMulEquiv_primeToP_of_forall_isDiscreteValuationRing`:
over a strictly henselian discrete valuation ring `R` whose residue field is algebraically closed
of characteristic `p`, every Galois object of `FÉt_{Z_η̄}` whose automorphism group has order
prime to `p` — `η̄` the geometric generic point of `Spec R`, `h : Z ⟶ Spec R` smooth proper with
geometrically connected fibres — is the base change along `Z_η̄ ⟶ Z` of a finite étale cover of
`Z`. That statement is proved here, and the tag is attached to the composition.

The route is the one the residue-characteristic-zero sibling [Stacks, Tag 0C0Q] takes
(`AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre`), with one
hypothesis exchanged for another. That route rests on [Stacks, Tag 0EYJ]
(`AlgebraicGeometry.FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian`),
whose hypothesis on the Galois group is that its order be *invertible in the residue fields* of
the base. In residue characteristic zero that is automatic, and it is the only thing residue
characteristic zero was used for. In residue characteristic `p` the hypothesis that the order of
the group is prime to `p` gives exactly the same invertibility
(`AlgebraicGeometry.isUnit_natCast_of_not_dvd_ringChar_specResidueField`). So the whole of the
geometric half transfers:

* the cover descends from `Z_η̄` to a Galois cover of a finite stage `K(t) ×_K Z_K` carrying a
  `K(t)`-rational point over a section of `h`, by
  `AlgebraicGeometry.exists_galoisCover_stage_model_of_isGalois`, which mentions no
  characteristic at all and is reused unchanged;
* the order of the group of that stage cover is the order of `Aut` of the original cover, because
  both are the degree of the cover and degrees are unchanged by base change
  (`AlgebraicGeometry.card_aut_eq_card_of_baseChange_finiteEtaleGaloisCover`); this is the
  dictionary which turns the tag's hypothesis on `Aut` of the cover of `Z_η̄` into the hypothesis
  [Stacks, Tag 0EYJ] consumes;
* with `L = K(t)` and `B'` the integral closure of `R` in `L`, the stage `Z_L` is the generic
  fibre of `Z_{B'} ⟶ Spec B'`, [Stacks, Tag 0EYJ] extends the cover over `Z_{B'}`, and
  `R ⟶ B'` is residually trivial, so the extension descends to `Z` by [Stacks, Tag 0A48].

Two differences from the residue-characteristic-zero argument are worth recording.

* The residue extension `κ(R) ⊂ κ(B')` is still trivial, because `κ(R)` is algebraically closed
  and the extension is algebraic
  (`Stacks.Henselian.bijective_residueField_map_integralClosure`, which assumes nothing about
  characteristic, finiteness or separability). So the descent of the extended cover from `Z_{B'}`
  to `Z` is unaffected.
* The finite subextension `L = K(t)` of `k̄/K` need *not* be separable in characteristic `p`. So
  the integral closure is taken through the package
  `Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_integralClosure`, which is
  unconditional, rather than through its separable refinement: `B'` is a strictly henselian
  discrete valuation ring with fraction field `L`, which is all that is needed, a discrete
  valuation ring being Noetherian. Module-finiteness of `B'` over `R` is not used.

## Main results

* `AlgebraicGeometry.isUnit_natCast_of_not_dvd_ringChar_specResidueField` — a natural number not
  divisible by the residue characteristic of a local ring is a unit in that ring.
* `AlgebraicGeometry.card_aut_eq_card_of_baseChange_finiteEtaleGaloisCover` — a Galois object
  which is the base change of a Galois cover with group `G` has automorphism group of order
  `|G|`.
* `AlgebraicGeometry.exists_finiteEtale_model_of_galoisCover_stage_of_isUnit` — a Galois cover of
  a finite stage whose order is invertible in the base, with a rational point over a section,
  extends and descends to the family.
* `AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre_of_not_dvd` — the
  residual geometric input of [Stacks, Tag 0C0R].
* `AlgebraicGeometry.surjective_and_exists_continuousMulEquiv_primeToP` —
  [Stacks, Tag 0C0R].

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0C0P](https://stacks.math.columbia.edu/tag/0C0P)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0C0R](https://stacks.math.columbia.edu/tag/0C0R)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory IsLocalRing
open Stacks.FundamentalGroup

universe v u

namespace AlgebraicGeometry

/-! ### Invertibility from the residue characteristic -/

/-- **A natural number not divisible by the residue characteristic of a local ring is a unit in
that ring.** Here the residue characteristic is read off the scheme-theoretic residue field of
`Spec R` at the closed point, which is the form in which [Stacks, Tag 0C0R] carries it. If `n`
were a nonunit it would lie in the maximal ideal, so its image in `R ⧸ m` would vanish, hence so
would its image in the residue field of the closed point — the two being joined by a ring
homomorphism through `Ideal.ResidueField` and
`AlgebraicGeometry.Scheme.Spec.residueFieldIso` — and the characteristic of that field would
divide `n`.

In residue characteristic zero this is nonvanishing of `n`; the point of the statement is that in
residue characteristic `p` it is exactly the prime-to-`p` condition of [Stacks, Tag 0C0R]. It is
the variant of `Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar` which asks for
non-divisibility rather than coprimality, so that no primality of `p` is needed, and which reads
the residue characteristic on the spectrum. -/
@[ega "0 21.1.3" "special case", sga "4 IX 3.0" "special case"]
theorem isUnit_natCast_of_not_dvd_ringChar_specResidueField {R : Type u} [CommRing R]
    [IsLocalRing R] {n p : ℕ}
    (hp : ringChar ((Spec (.of R)).residueField (closedPoint R)) = p) (hdvd : ¬ p ∣ n) :
    IsUnit (n : R) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hzero : ((n : R) : R ⧸ IsLocalRing.maximalIdeal R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_natCast] at hzero
  have h0 : (Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).inv.hom.comp
        (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
          ((IsLocalRing.maximalIdeal R).ResidueField))
        ((n : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    rw [hzero, map_zero]
  rw [map_natCast] at h0
  exact hdvd (hp ▸ (ringChar.spec _ n).mp h0)

/-! ### The order of the automorphism group is unchanged by base change -/

/-- **A Galois object which is a base change of a Galois cover with group `G` has `|G|`
automorphisms.** Let `ρ : T ⟶ S` be a morphism of connected schemes, let `V` be a finite étale
Galois cover of `S` with group `G`, and let `A` be a Galois object of `FÉt_T` isomorphic to the
base change of `V` along `ρ`. Then `Aut A` and `G` have the same order.

Both orders are the degree of the cover: the automorphism group of a Galois object acts simply
transitively on a geometric fibre
(`AlgebraicGeometry.EtaleFundamentalGroup.card_aut_eq_card_fiber_of_isGalois`), so has order the
size of that fibre; the fibres of a base change are the fibres of the original cover
(`AlgebraicGeometry.finiteEtaleFiberProjectionEquiv`); and the group of a Galois cover is its own
automorphism group (`AlgebraicGeometry.FiniteEtaleGaloisCover.autMulEquiv`).

This is the dictionary which lets the prime-to-`p` hypothesis of [Stacks, Tag 0C0R], stated on
`Aut` of a cover of the geometric generic fibre, be used as the invertibility hypothesis of
[Stacks, Tag 0EYJ], stated on the group of a Galois cover of a stage. -/
theorem card_aut_eq_card_of_baseChange_finiteEtaleGaloisCover {T S : Scheme.{u}}
    [ConnectedSpace T] [ConnectedSpace S] (ρ : T ⟶ S) {G : Type v} [Group G] [Finite G]
    (V : FiniteEtaleGaloisCover S G) (A : FiniteEtaleOver T) [IsGalois A]
    (e : (finiteEtaleBaseChange ρ).obj V.obj ≅ A) :
    Nat.card (Aut A) = Nat.card G := by
  obtain ⟨t⟩ := ConnectedSpace.toNonempty (α := ↥T)
  let x : GeometricPoint T := T.algClosedPoint t
  calc Nat.card (Aut A)
      = Nat.card ((finiteEtaleFiberFunctor x).obj A) :=
        EtaleFundamentalGroup.card_aut_eq_card_fiber_of_isGalois x A
    _ = Nat.card ((finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange ρ).obj V.obj)) :=
        Nat.card_congr ((finiteEtaleFiberFunctor x).mapIso e).toEquiv.symm
    _ = Nat.card ((finiteEtaleFiberFunctor (x.map ρ)).obj V.obj) :=
        Nat.card_congr (finiteEtaleFiberProjectionEquiv ρ x V.obj)
    _ = Nat.card (Aut V.obj) :=
        (EtaleFundamentalGroup.card_aut_eq_card_fiber_of_isGalois (x.map ρ) V.obj).symm
    _ = Nat.card G := (Nat.card_congr V.autMulEquiv.toEquiv).symm

/-! ### From a Galois cover of a finite stage of invertible order to a cover of the family -/

/-- **The section-induced rational point of the generic fibre of `Y_B ⟶ Spec B` is the image of a
rational point of the stage `Spec L ×_{Spec K} Y_K` lying over the section**, across an
isomorphism `m` of the stage with that generic fibre compatible with the maps to `Y` and to
`Spec L`. Both sides are compared after composing with the two legs of the cartesian square
`AlgebraicGeometry.isPullback_fiberι_genericPoint_comp`. -/
private theorem genericFiberSection_eq_comp_isoIsPullback {R K L B : Type u} [CommRing R]
    [CommRing K] [Field L] [CommRing B] [IsDomain B] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ h = 𝟙 _)
    (i : Spec ((Spec (.of B)).residueField (genericPoint (Spec (.of B)))) ⟶ Spec (.of L))
    [IsIso i]
    (hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap B L))
      = (Spec (.of B)).fromSpecResidueField (genericPoint (Spec (.of B))))
    (m : pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≅
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiber
        (genericPoint (Spec (.of B))))
    (hm₁ : m.hom ≫ (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiberι
          (genericPoint (Spec (.of B))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hm₂ : m.hom ≫ (pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R B)))).fiberToSpecResidueField (genericPoint (Spec (.of B))) ≫ i
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    {W : Scheme.{u}} (v : W ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (z : Spec (.of L) ⟶ W)
    (hz₁ : z ≫ v ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = 𝟙 _)
    (hz₂ : z ≫ v ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) :
    genericFiberSection (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ σ) (𝟙 _) (by
        rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _) = i ≫ (z ≫ v) ≫ m.hom := by
  refine (isPullback_fiberι_genericPoint_comp h i hi).hom_ext ?_ ?_
  · rw [← Category.assoc, genericFiberSection_fiberι, Category.assoc, pullback.lift_fst]
    simp only [Category.assoc, hm₁, hz₂]
    rw [reassoc_of% specMap_algebraMap_comp_of_isScalarTower R K L,
      ← reassoc_of% specMap_algebraMap_comp_of_isScalarTower R B L, reassoc_of% hi]
  · rw [← Category.assoc, genericFiberSection_fiberToSpecResidueField, Category.id_comp]
    simp only [Category.assoc, hm₂, hz₁, Category.comp_id]

/-- **A finite étale cover transported along an isomorphism and extended across a base change
which is an equivalence is itself a base change.** If `V` over `S` is carried by `m : S ≅ F` to
a cover of `F` which is the base change along `ι : F ⟶ Y'` of a cover `W` of `Y'`, and base
change along `g : Y' ⟶ Y` is an equivalence, then `V` is the base change along
`m ≫ ι ≫ g` of a finite étale cover of `Y`. -/
private theorem exists_finiteEtaleBaseChange_iso_of_iso_of_isEquivalence {Y Y' F S : Scheme.{u}}
    (g : Y' ⟶ Y) [(finiteEtaleBaseChange g).IsEquivalence] (ι : F ⟶ Y') (m : S ≅ F)
    {f : S ⟶ Y} (hf : m.hom ≫ ι ≫ g = f) {V : FiniteEtaleOver S} {W : FiniteEtaleOver Y'}
    (ε : (finiteEtaleBaseChange ι).obj W ≅ (finiteEtaleBaseChange m.inv).obj V) :
    ∃ C : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange f).obj C ≅ V) := by
  refine ⟨(finiteEtaleBaseChange g).objPreimage W, ?_⟩
  obtain ⟨ε₂⟩ := nonempty_iso_finiteEtaleBaseChange_comp m.hom ι _ rfl
    (((finiteEtaleBaseChangeComp m.hom m.inv (𝟙 _) m.hom_inv_id.symm).app V).symm ≪≫
      finiteEtaleBaseChangeId.app V) ε
  exact nonempty_iso_finiteEtaleBaseChange_comp _ g f (by rw [← hf, Category.assoc]) ε₂
    ((finiteEtaleBaseChange g).objObjPreimageIso W)

/-- **A Galois cover of `Y_L` whose order is invertible in the base, with a rational point over a
section, extends and descends to `Y` through any residually trivial henselian discrete valuation
ring with fraction field `L`.** Let `B` be a henselian discrete valuation ring over the henselian
local ring `R`, with fraction field `L`, such that `R ⟶ B` is local and bijective on residue
fields. The stage `Spec L ×_{Spec K} Y_K` is the generic fibre of `Y_B ⟶ Spec B`
(`AlgebraicGeometry.isPullback_fiberι_genericPoint_comp`), on which the section induces the given
rational point (`AlgebraicGeometry.genericFiberSection_eq_comp_isoIsPullback`); so
[Stacks, Tag 0EYJ] extends `V` over `Y_B`, and the extension descends to `Y` by
[Stacks, Tag 0A48]
(`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField`).
-/
private theorem exists_finiteEtale_model_of_galoisCover_stage_of_isFractionRing
    (R K L B : Type u)
    [CommRing R] [HenselianLocalRing R] [CommRing K] [Field L] [Algebra R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)] [Algebra B L]
    [IsScalarTower R B L] [IsFractionRing B L]
    (hres : Function.Bijective (ResidueField.map (algebraMap R B)))
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h] [GeometricallyConnected h]
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ h = 𝟙 _) (G : Type v) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : R))
    (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) G)
    (z : Spec (.of L) ⟶ V.obj.left)
    (hz₁ : z ≫ V.obj.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = 𝟙 _)
    (hz₂ : z ≫ V.obj.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) :
    ∃ C : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj C ≅ V.obj) := by
  have : IsNormal (Spec (.of B)) := isNormal_spec_of_isDiscreteValuationRing B
  -- the section of the base change to `Spec B`
  let σ' : Spec (.of B) ⟶ pullback h (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ σ) (𝟙 _) (by
      rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσ' : σ' ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B))) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  -- the stage `Y_L` is the generic fibre of `Y_B ⟶ Spec B`
  obtain ⟨i, _, hi⟩ := exists_isIso_comp_specMap_eq_fromSpecResidueField (A := B) L
  have Hstage := AlgebraicExtensionLimit.isPullback_pullback_comp h
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  rw [specMap_algebraMap_comp_of_isScalarTower R K L] at Hstage
  have Hfib := isPullback_fiberι_genericPoint_comp h i hi
  let m := Hstage.isoIsPullback _ _ Hfib
  -- the two section-induced rational points agree across the comparison isomorphism
  have hsec : genericFiberSection _ σ' hσ' = i ≫ (z ≫ V.obj.hom) ≫ m.hom :=
    genericFiberSection_eq_comp_isoIsPullback h σ hσ i hi m
      (Hstage.isoIsPullback_hom_fst _ _ Hfib) (Hstage.isoIsPullback_hom_snd _ _ Hfib)
      V.obj.hom z hz₁ hz₂
  -- the Galois cover transported to the generic fibre, with its rational point
  have : ConnectedSpace ↥V.obj.left := V.connected
  let Z := V.baseChange m.inv (connectedSpace_left_finiteEtaleBaseChange_of_isIso m.inv V.obj)
  let zZ : Spec ((Spec (.of B)).residueField (genericPoint (Spec (.of B)))) ⟶ Z.obj.left :=
    pullback.lift (i ≫ z) (genericFiberSection _ σ' hσ') (by
      rw [Iso.eq_comp_inv, hsec]
      simp only [Category.assoc])
  -- Tag 0EYJ: the cover of the generic fibre extends over `Spec B`, the order of `G` being
  -- invertible on `Spec B` as it is already invertible in `R`
  obtain ⟨Y₀, ε, -⟩ :=
    FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))) σ' hσ' G
      (isUnit_natCast_specResidueField_of_isUnit
        (by simpa only [map_natCast] using hG.map (algebraMap R B))) Z zZ
      (pullback.lift_snd _ _ _)
  -- the extension descends from `Y_B` to `Y`
  have := isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField R B hres h
  exact exists_finiteEtaleBaseChange_iso_of_iso_of_isEquivalence _ _ m
    (Hstage.isoIsPullback_hom_fst _ _ Hfib) (V := V.obj) ε

/-- **A Galois cover of `Y_L` whose order is invertible in the base, with a rational point over a
section, extends and descends to `Y`.** Let `R` be a strictly henselian discrete valuation ring
with algebraically closed residue field, let `K` be its fraction field and `L` a finite extension
of `K`, let `h : Y ⟶ Spec R` be smooth and proper with geometrically connected fibres and `σ` a
section of `h`, and let `V` be a finite étale Galois cover of `Spec L ×_{Spec K} Y_K` with finite
group `G` whose order is a unit in `R`, carrying an `L`-rational point over the section. Then `V`
is the base change along `Spec L ×_{Spec K} Y_K ⟶ Y` of a finite étale cover of `Y`.

Write `B' = ` the integral closure of `R` in `L`. It is again a strictly henselian discrete
valuation ring with fraction field `L`
(`Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_integralClosure`), so `Spec B'` is
integral, normal and Noetherian. The scheme `Spec L ×_{Spec K} Y_K` is the generic fibre of
`Y_{B'} ⟶ Spec B'` (`AlgebraicGeometry.isPullback_fiberι_genericPoint_comp`), the section induces
the same rational point on both presentations, and the order of `G` is invertible on `Spec B'`
because it is already invertible in `R` and `R` maps to `B'`. So
[Stacks, Tag 0EYJ] extends `V` over `Y_{B'}`, and `R ⟶ B'` induces a bijection on residue fields,
so that extension descends to `Y`
(`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField`,
[Stacks, Tag 0A48]).

This is `AlgebraicGeometry.exists_finiteEtale_model_of_galoisCover_stage` with its residue
characteristic zero hypothesis replaced by the invertibility of `|G|` which was all that
hypothesis delivered; in residue characteristic `p` that invertibility comes from `|G|` being
prime to `p`
(`AlgebraicGeometry.isUnit_natCast_of_not_dvd_ringChar_specResidueField`). Separability of `L/K`
is not available here, so the integral closure is taken through the unconditional package;
module-finiteness over `R` is not needed.

The two hypotheses on the rational point are the two components of the single equation saying it
lies over the section: `hz₁` says it lies over the given `L`-point of the base and `hz₂` that its
image in `Y` is the section. -/
theorem exists_finiteEtale_model_of_galoisCover_stage_of_isUnit (R K L : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [StrictlyHenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h] [GeometricallyConnected h]
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ h = 𝟙 _) (G : Type v) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : R))
    (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) G)
    (z : Spec (.of L) ⟶ V.obj.left)
    (hz₁ : z ≫ V.obj.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = 𝟙 _)
    (hz₂ : z ≫ V.obj.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) :
    ∃ C : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj C ≅ V.obj) := by
  -- the integral closure of `R` in `L`, with no separability available
  obtain ⟨_, _, _, _⟩ :=
    Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_integralClosure R K L
  exact exists_finiteEtale_model_of_galoisCover_stage_of_isFractionRing R K L
    ↥(integralClosure R L) (Stacks.Henselian.bijective_residueField_map_integralClosure R L) h σ hσ
    G hG V z hz₁ hz₂

/-! ### The residual geometric input of Tag 0C0R -/

/-- **Every Galois cover of order prime to `p` of the geometric generic fibre of a smooth proper
family over a strictly henselian discrete valuation ring of residue characteristic `p` is a base
change.** Let `R` be a strictly henselian discrete valuation ring whose residue field is
algebraically closed of characteristic `p`, let `h : Y ⟶ Spec R` be smooth and proper with
geometrically connected fibres, and let `η` be a geometric point of `Spec R` lying over the
generic point. Then every finite étale cover of the geometric generic fibre `Y_η̄` which is a
Galois object of `FÉt_{Y_η̄}` with `¬ p ∣ |Aut A|` is isomorphic to the base change along
`Y_η̄ ⟶ Y` of a finite étale cover of `Y`.

This is the last paragraph of the proof of [Stacks, Tag 0C0R]. With `K = Frac R` and `kbar` the
algebraic closure of `K` inside the residue field of `η`
(`AlgebraicGeometry.exists_ringHom_algebraicClosure_of_liesOver_genericPoint`), the cover descends
to a Galois cover of a finite stage `Spec K(t) ×_{Spec K} Y_K` carrying a `K(t)`-rational point
over a section of `h` (`AlgebraicGeometry.exists_galoisCover_stage_model_of_isGalois`, the section
itself being `AlgebraicGeometry.exists_section_of_smooth_of_strictlyHenselian`); the group of that
stage cover has the order of `Aut A`
(`AlgebraicGeometry.card_aut_eq_card_of_baseChange_finiteEtaleGaloisCover`), hence prime to `p`;
and the stage cover extends over the integral closure of `R` in `K(t)` and descends to `Y`
(`AlgebraicGeometry.exists_finiteEtale_model_of_galoisCover_stage_of_isUnit`, the invertibility
coming from `AlgebraicGeometry.isUnit_natCast_of_not_dvd_ringChar_specResidueField`).

Compared with the residue-characteristic-zero statement
`AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre`, the first half —
the descent to a finite stage — is reused verbatim, and only the extension over the integral
closure changes, the prime-to-`p` condition replacing characteristic zero as the source of the
invertibility that [Stacks, Tag 0EYJ] asks for. -/
theorem exists_finiteEtale_model_of_isGalois_geometricGenericFibre_of_not_dvd (R : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [StrictlyHenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h]
    [Smooth h] [GeometricallyConnected h] (η : GeometricPoint (Spec (.of R)))
    (A : FiniteEtaleOver (fiberOverGeometricPoint h η)) {p : ℕ}
    (hchar : ringChar ((Spec (.of R)).residueField (closedPoint R)) = p)
    (hη : η.hom default = genericPoint (Spec (.of R))) [IsGalois A]
    (hcard : ¬ p ∣ Nat.card (Aut A)) :
    ∃ B : FiniteEtaleOver Y,
      Nonempty ((finiteEtaleBaseChange (pullback.fst h η.hom)).obj B ≅ A) := by
  obtain ⟨σR, hσR⟩ :=
    exists_section_of_smooth_of_strictlyHenselian R h (h.surjective (closedPoint R))
  obtain ⟨χ, hχ⟩ := exists_ringHom_algebraicClosure_of_liesOver_genericPoint η.hom hη
  obtain ⟨G, hGgrp, hGfin, t, V, z, ρ, hz₁, hz₂, ⟨εA⟩, hρ⟩ :=
    exists_galoisCover_stage_model_of_isGalois (FractionRing R)
      (AlgebraicClosure (FractionRing R)) h σR hσR χ η.hom hχ A
  let := hGgrp
  let := hGfin
  -- the group of the stage cover has the order of `Aut A`, hence is prime to `p`
  have hstageconn : ConnectedSpace
      ↥(pullback (AlgebraicExtensionLimit.stageHom (FractionRing R)
          (AlgebraicClosure (FractionRing R)) t)
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) :=
    AlgebraicExtensionLimit.connectedSpace_pullback_stageHom (FractionRing R)
      (AlgebraicClosure (FractionRing R)) _ t
  have hGcard : ¬ p ∣ Nat.card G := by
    rwa [← card_aut_eq_card_of_baseChange_finiteEtaleGaloisCover ρ V A εA]
  -- the stage is a finite extension of the fraction field
  let : Field ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    (AlgebraicExtensionLimit.isField_adjoin (FractionRing R)
      (AlgebraicClosure (FractionRing R)) t).toField
  have : FiniteDimensional (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    AlgebraicExtensionLimit.finiteDimensional_adjoin (FractionRing R)
      (AlgebraicClosure (FractionRing R)) t
  let : Algebra R ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    ((algebraMap (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R))))).comp
        (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨C, ⟨εC⟩⟩ := exists_finiteEtale_model_of_galoisCover_stage_of_isUnit R (FractionRing R)
    ↥(Algebra.adjoin (FractionRing R) (t : Set (AlgebraicClosure (FractionRing R))))
    h σR hσR G (isUnit_natCast_of_not_dvd_ringChar_specResidueField hchar hGcard) V z hz₁ hz₂
  exact ⟨C, nonempty_iso_finiteEtaleBaseChange_comp ρ _ (pullback.fst h η.hom) hρ.symm εA εC⟩

/-! ### Tag 0C0R -/

/-- **[Stacks, Tag 0C0R].** Let `f : X ⟶ S` be a smooth proper morphism with geometrically
connected fibres, let `s' ⇝ s` be a specialization of points of `S` realized by a specialization
map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and let `p` be the characteristic of `κ(s)`. Then `sp` is
surjective and induces an isomorphism `π'₁(X_{s̄'}) ≅ π'₁(X_{s̄})` of the maximal prime-to-`p`
quotients, commuting with the projections.

Surjectivity is [Stacks, Tag 0C0P]. The isomorphism of the maximal prime-to-`p` quotients is
reduced by
`surjective_and_exists_continuousMulEquiv_primeToP_of_forall_isDiscreteValuationRing`
to the descent of the Galois covers of order prime to `p` of a geometric generic fibre over a
strictly henselian discrete valuation ring with algebraically closed residue field of
characteristic `p`, which is
`AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre_of_not_dvd`. -/
@[stacks 0C0R "the whole statement, under the source's hypotheses only: `f` smooth and proper \
with geometrically connected fibres (`IsProper f`, `Smooth f`, `GeometricallyConnected f`), a \
specialization of points of `S` realized by a specialization map `sp` (`hsp`), and `p` the \
characteristic of `κ(s)` (`hchar`). Both of the source's conclusions are stated and proved: `sp` \
is surjective, and the induced map of the maximal prime-to-`p` quotients is an isomorphism of \
topological groups commuting with the projections, which is the source's isomorphism \
`π'₁(X_{s̄'}) ≅ π'₁(X_{s̄})`.", sga "1 X 3.8" "more general", sga "1 X 3.9"]
theorem surjective_and_exists_continuousMulEquiv_primeToP {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = p) :
    Function.Surjective sp ∧
      ∃ e : PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x') ≃ₜ*
          PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        ∀ g, e (primeToPMk p _ g) = primeToPMk p _ (sp g) := by
  refine surjective_and_exists_continuousMulEquiv_primeToP_of_forall_isDiscreteValuationRing f
    s' s p x' x sp hsp hchar ?_
  intro R _ _ _ _ _ Z hZ _ _ _ η A hcharR hη _ hAcard
  exact exists_finiteEtale_model_of_isGalois_geometricGenericFibre_of_not_dvd R hZ η A hcharR hη
    hAcard

end AlgebraicGeometry

end
