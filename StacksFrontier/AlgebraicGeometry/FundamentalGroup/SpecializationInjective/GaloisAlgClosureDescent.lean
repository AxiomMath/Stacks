module

public import StacksFrontier.CategoryTheory.Galois.ObjectEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleAlgClosedEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap

/-!
# Galois covers of a fibre over an algebraically closed extension descend

Let `f : X ⟶ S` be proper, let `g : Spec k̄ ⟶ S` be a point with algebraically closed residue
field and let `w : Spec Ω ⟶ S` factor through `g` along an extension `k̄ ⊆ Ω` of algebraically
closed fields. Then every Galois object of `FÉt_{X_Ω}` is the base change of a Galois object of
`FÉt_{X_{k̄}}`, by [Stacks, Tag 0A49] for the proper scheme `X_{k̄}` over `k̄`.

This is the first step of the descent of a Galois cover of a *geometric* generic fibre to a
generic fibre: a geometric point of `S` lying over a point `s` factors through the spectrum of an
algebraic closure of `κ(s)` inside its own residue field, and the step replaces the algebraically
closed field of the geometric point, which can be enormous, by that algebraic closure — a field
over which the limit arguments for an algebraic extension apply.

The map `X_Ω ⟶ X_{k̄}` is taken as data, characterized by its two projections, because the callers
present it in different shapes (`AlgebraicGeometry.pullbackBaseChangeMap` for a factorization of
the base, `AlgebraicGeometry.fiberOverGeometricPointMap` for a geometric point); both satisfy the
two equations by `pullback.lift_fst` and `pullback.lift_snd`.

The transport of the Galois condition across the equivalence of [Stacks, Tag 0A49] is
`CategoryTheory.PreGaloisCategory.isGalois_obj_of_isEquivalence`.

## Main results

* `AlgebraicGeometry.eq_pullbackLeftPullbackSndIso_inv_comp_fst` — a map of base changes over a
  factorization of the base morphism is the pasting isomorphism followed by a projection.
* `AlgebraicGeometry.nonempty_iso_finiteEtaleBaseChange_comp` — two base-change isomorphisms
  along the legs of a factorization compose into one along the composite.
* `AlgebraicGeometry.exists_isGalois_essImage_of_isEquivalence` — a Galois object has a *Galois*
  model when base change is an equivalence.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isAlgClosed_base` —
  [Stacks, Tag 0A49] in the shape of a map between two base changes of one proper morphism.
* `AlgebraicGeometry.exists_isGalois_model_of_isAlgClosed_base` — the descent itself.
* `AlgebraicGeometry.injective_specPreimage_of_liesOver_genericPoint` and
  `AlgebraicGeometry.exists_ringHom_fractionRing_of_liesOver_genericPoint` — a geometric point of
  the spectrum of a domain lying over the generic point has residue field an extension of the
  fraction field, which is how the factorization the descent consumes is produced.

## References

* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

/-! ### Maps between base changes -/

/-- The projection to the base change along the second leg of a factorization. -/
theorem pullbackBaseChangeMap_fst {X S T U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ S)
    (c : T ⟶ U) (hc : c ≫ h = g) :
    pullbackBaseChangeMap f g h c hc ≫ pullback.fst f h = pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- The second projection of a map of base changes is the second projection followed by the
morphism of bases. -/
theorem pullbackBaseChangeMap_snd {X S T U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ S)
    (c : T ⟶ U) (hc : c ≫ h = g) :
    pullbackBaseChangeMap f g h c hc ≫ pullback.snd f h = pullback.snd f g ≫ c :=
  pullback.lift_snd _ _ _

/-- **A map of base changes over a factorization of the base is the pasting isomorphism followed
by a projection.** For `f : X ⟶ S` and a factorization `c ≫ g` of the base morphism, the map
`X_T ⟶ X_U` determined by the two projections identifies `X_T` with `(X_U) ×_U T` and projects. -/
theorem eq_pullbackLeftPullbackSndIso_inv_comp_fst {X S U T : Scheme.{u}} (f : X ⟶ S)
    (g : U ⟶ S) (c : T ⟶ U) (m : pullback f (c ≫ g) ⟶ pullback f g)
    (h₁ : m ≫ pullback.fst f g = pullback.fst f (c ≫ g))
    (h₂ : m ≫ pullback.snd f g = pullback.snd f (c ≫ g) ≫ c) :
    m = (pullbackLeftPullbackSndIso f g c).inv ≫ pullback.fst (pullback.snd f g) c := by
  refine pullback.hom_ext ?_ ?_
  · rw [h₁, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  · rw [h₂, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]

/-- **Base-change isomorphisms compose along a factorization.** If a cover `C` of `U` pulls back
to `B` along `q` and `B` pulls back to `A` along `p`, then `C` pulls back to `A` along `p ≫ q`. -/
theorem nonempty_iso_finiteEtaleBaseChange_comp {S T U : Scheme.{u}} (p : S ⟶ T) (q : T ⟶ U)
    (pq : S ⟶ U) (hpq : pq = p ≫ q) {A : FiniteEtaleOver S} {B : FiniteEtaleOver T}
    {C : FiniteEtaleOver U} (e₁ : (finiteEtaleBaseChange p).obj B ≅ A)
    (e₂ : (finiteEtaleBaseChange q).obj C ≅ B) :
    Nonempty ((finiteEtaleBaseChange pq).obj C ≅ A) :=
  ⟨(finiteEtaleBaseChangeComp p q pq hpq).app C ≪≫
    (finiteEtaleBaseChange p).mapIso e₂ ≪≫ e₁⟩

/-! ### A Galois model across an equivalence -/

/-- **A Galois object has a Galois model when base change is an equivalence.** The inverse of the
equivalence is itself an equivalence, so it carries the Galois object to a Galois object by
`CategoryTheory.PreGaloisCategory.isGalois_obj_of_isEquivalence`, and the counit identifies the
base change of that model with the original cover. -/
theorem exists_isGalois_essImage_of_isEquivalence {S T : Scheme.{u}} [ConnectedSpace ↥S]
    [ConnectedSpace ↥T] (q : T ⟶ S) (hq : (finiteEtaleBaseChange q).IsEquivalence)
    (A : FiniteEtaleOver T) [IsGalois A] :
    ∃ B : FiniteEtaleOver S, IsGalois B ∧
      Nonempty ((finiteEtaleBaseChange q).obj B ≅ A) := by
  have := hq
  refine ⟨(finiteEtaleBaseChange q).inv.obj A,
    isGalois_obj_of_isEquivalence (finiteEtaleBaseChange q).inv A, ?_⟩
  exact ⟨(finiteEtaleBaseChange q).asEquivalence.counitIso.app A⟩

/-! ### Tag 0A49 between two base changes -/

/-- **[Stacks, Tag 0A49] as a statement about two base changes of one proper morphism.** Let
`f : X ⟶ S` be proper and let `w : Spec Ω ⟶ S` factor as `Spec Ω ⟶ Spec k̄ ⟶ S` along an
extension of algebraically closed fields. Then base change along any `m : X_Ω ⟶ X_{k̄}` with the
two projections of the canonical map is an equivalence on finite étale covers.

The map `m` is, by `AlgebraicGeometry.eq_pullbackLeftPullbackSndIso_inv_comp_fst`, an isomorphism
followed by the projection `(X_{k̄})_Ω ⟶ X_{k̄}`, and `X_{k̄}` is proper over `k̄`, so
[Stacks, Tag 0A49] applies to it. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isAlgClosed_base
    {kbar Omega : Type u} [Field kbar] [Field Omega] [Algebra kbar Omega]
    [IsAlgClosed kbar] [IsAlgClosed Omega] {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (g : Spec (.of kbar) ⟶ S) (w : Spec (.of Omega) ⟶ S)
    (hw : Spec.map (CommRingCat.ofHom (algebraMap kbar Omega)) ≫ g = w)
    (m : pullback f w ⟶ pullback f g)
    (h₁ : m ≫ pullback.fst f g = pullback.fst f w)
    (h₂ : m ≫ pullback.snd f g
      = pullback.snd f w ≫ Spec.map (CommRingCat.ofHom (algebraMap kbar Omega))) :
    (finiteEtaleBaseChange m).IsEquivalence := by
  subst hw
  rw [eq_pullbackLeftPullbackSndIso_inv_comp_fst f g _ m h₁ h₂]
  exact isEquivalence_finiteEtaleBaseChange_isIso_comp _ _
    (isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed (pullback.snd f g))

/-! ### The descent -/

/-- **A Galois cover of `X_Ω` is the base change of a Galois cover of `X_{k̄}`.** Let `f : X ⟶ S`
be proper, let `g : Spec k̄ ⟶ S` have algebraically closed residue field, and let
`w : Spec Ω ⟶ S` factor through `g` along `k̄ ⊆ Ω` with `Ω` algebraically closed. If `X_{k̄}` and
`X_Ω` are connected, then every Galois object `A` of `FÉt_{X_Ω}` is the base change of a Galois
object of `FÉt_{X_{k̄}}` along the canonical `X_Ω ⟶ X_{k̄}`. -/
theorem exists_isGalois_model_of_isAlgClosed_base
    {kbar Omega : Type u} [Field kbar] [Field Omega] [Algebra kbar Omega]
    [IsAlgClosed kbar] [IsAlgClosed Omega] {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (g : Spec (.of kbar) ⟶ S) (w : Spec (.of Omega) ⟶ S)
    (hw : Spec.map (CommRingCat.ofHom (algebraMap kbar Omega)) ≫ g = w)
    [ConnectedSpace ↥(pullback f g)] [ConnectedSpace ↥(pullback f w)]
    (m : pullback f w ⟶ pullback f g)
    (h₁ : m ≫ pullback.fst f g = pullback.fst f w)
    (h₂ : m ≫ pullback.snd f g
      = pullback.snd f w ≫ Spec.map (CommRingCat.ofHom (algebraMap kbar Omega)))
    (A : FiniteEtaleOver (pullback f w)) [IsGalois A] :
    ∃ B : FiniteEtaleOver (pullback f g), IsGalois B ∧
      Nonempty ((finiteEtaleBaseChange m).obj B ≅ A) :=
  exists_isGalois_essImage_of_isEquivalence m
    (isEquivalence_finiteEtaleBaseChange_of_isAlgClosed_base f g w hw m h₁ h₂) A

/-! ### A geometric point over the generic point of an affine integral base -/

/-- **A morphism from the spectrum of a field hitting the generic point of the spectrum of a
domain is injective on rings.** The image of the unique point of `Spec Ω` is the prime ideal
`ker φ` of the corresponding ring map `φ`, and the generic point of the spectrum of a domain is
the zero ideal, so `ker φ = 0`. -/
theorem injective_specPreimage_of_liesOver_genericPoint {R : Type u} [CommRing R] [IsDomain R]
    {Omega : Type u} [Field Omega] (w : Spec (.of Omega) ⟶ Spec (.of R))
    (hw : w default = genericPoint (Spec (.of R))) :
    Function.Injective (Spec.preimage w).hom := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
  have hw' : w.base default = genericPoint (Spec (.of R)) := hw
  have h1 : (Spec.map (Spec.preimage w)).base default = (⊥ : PrimeSpectrum R) := by
    rw [Spec.map_preimage, hw', genericPoint_eq_bot_of_affine]
  have hd : (default : ↥(Spec (CommRingCat.of Omega))) = (⊥ : PrimeSpectrum Omega) :=
    Subsingleton.elim _ _
  rw [hd] at h1
  have h2 : PrimeSpectrum.comap (Spec.preimage w).hom (⊥ : PrimeSpectrum Omega)
      = (⊥ : PrimeSpectrum R) := h1
  have hc := congrArg PrimeSpectrum.asIdeal h2
  simp only [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot] at hc
  exact hc

/-- **The residue field of a geometric point over the generic point of the spectrum of a domain
is an extension of the fraction field.** The underlying ring map is injective by
`AlgebraicGeometry.injective_specPreimage_of_liesOver_genericPoint`, so it extends over the
localization at the nonzerodivisors. -/
theorem exists_ringHom_fractionRing_of_liesOver_genericPoint {R : Type u} [CommRing R]
    [IsDomain R] {Omega : Type u} [Field Omega] (w : Spec (.of Omega) ⟶ Spec (.of R))
    (hw : w default = genericPoint (Spec (.of R))) :
    ∃ ψ : FractionRing R →+* Omega,
      ψ.comp (algebraMap R (FractionRing R)) = (Spec.preimage w).hom := by
  have hinj := injective_specPreimage_of_liesOver_genericPoint w hw
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a ↦ IsFractionRing.lift_algebraMap hinj a⟩

end AlgebraicGeometry

end
