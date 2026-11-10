module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A resolution of a model of a smooth curve is again a model

Let `R` be a discrete valuation ring with fraction field `K`, let `C` be a smooth curve over `K`
and let `X ⟶ Spec R` be a model of `C`. If `Y ⟶ X` is a resolution of singularities, then the
composite `Y ⟶ Spec R` is again a model of `C`.

The content is the identification of the generic fibre. Writing `X_K` for the generic fibre of
the model, the generic fibre of `Y ⟶ Spec R` is the preimage `Y ×_X X_K`, and the projection
`Y ×_X X_K ⟶ X_K` is proper and birational onto the smooth — hence normal, one-dimensional —
curve `X_K ≅ C`. Such a projection is an isomorphism, which transports the given identification
`C ≅ X_K` to an identification of `C` with the generic fibre of `Y`. Flatness of `Y ⟶ Spec R`
then comes from dominance: over a discrete valuation ring a torsion-free module is flat, and the
local rings of an integral scheme dominating `Spec R` are torsion-free.

## Main results

* `AlgebraicGeometry.isModel_comp_of_isResolution` — a resolution of a model of a smooth curve
  is a model of that curve.

## Implementation notes

Models carry a chosen identification with their generic fibre, so the conclusion is existential:
it produces an identification of the curve with the generic fibre of the resolution.

The private lemma `isFinite_of_isProper_of_isBirational_of_topologicalKrullDim_le_one` stands in
for the finiteness criterion of [Stacks Project, Tag 0AB7]; delete it when that tag lands. It
states only the instance consumed here, with the target assumed normal of dimension at most one
rather than merely of stalk dimension at most one, and it concludes global finiteness rather
than finiteness over a neighbourhood of each point.

## References

* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 0C2U](https://stacks.math.columbia.edu/tag/0C2U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Finiteness

/-- A birational morphism of integral schemes sends the generic point to the generic point. -/
private theorem map_genericPoint_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (hf : IsBirational f) : f (genericPoint X) = genericPoint Y := by
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
    hf.bijOn.1 (show genericPoint X ∈ genericPoints X by simp [genericPoints_eq_singleton])

/-- A Noetherian local domain of Krull dimension at most one which is integrally closed in its
field of fractions is a valuation ring. -/
private theorem valuationRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : ringKrullDim A ≤ 1) : ValuationRing A := by
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hA
  have h : IsIntegrallyClosed A ∧
      ∀ P : Ideal A, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal A :=
    ⟨‹IsIntegrallyClosed A›,
      fun _ hP hP' => IsLocalRing.eq_maximalIdeal (hP'.isMaximal_of_ne_bot hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 4 2).mp h

/-- The map of local rings induced by a birational morphism of integral schemes is an isomorphism
at every point, provided the target is normal of dimension at most one.

The local ring `A` of the target below the point is a valuation ring of the function field `K`,
because it is an integrally closed Noetherian local domain of dimension at most one with `K` as
its field of fractions. The local ring of the source maps to `K` as well, compatibly, so the
local subring of `K` it cuts out dominates the one cut out by `A`; valuation subrings are maximal
for domination, so the two agree. -/
private theorem isIso_stalkMap_of_isBirational_of_isNormal {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f)
    (hY : topologicalKrullDim Y ≤ (1 : ℕ)) (x : X) : IsIso (f.stalkMap x) := by
  have hηX : genericPoint X ∈ genericPoints X := by simp [genericPoints_eq_singleton]
  have hη : f (genericPoint X) = genericPoint Y := map_genericPoint_of_isBirational f hf
  have hspec : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hspecY : genericPoint Y ⤳ f x := (genericPoint_spec Y).specializes (Set.mem_univ _)
  have : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := IsNormal.stalk_normal (f x)
  have : ValuationRing (Y.presheaf.stalk (f x)) :=
    valuationRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _
      ((ringKrullDim_stalk_le_topologicalKrullDim (f x)).trans hY)
  have he : IsIso (f.stalkMap (genericPoint X)) := hf.isIso_stalkMap _ hηX
  let c : Y.presheaf.stalk (f (genericPoint X)) ⟶ Y.functionField :=
    Y.presheaf.stalkSpecializes (specializes_of_eq hη.symm)
  have : IsIso c := inferInstanceAs (IsIso (Y.presheaf.stalkCongr (Inseparable.of_eq hη)).hom)
  let g : X.presheaf.stalk x ⟶ Y.functionField :=
    X.presheaf.stalkSpecializes hspec ≫ inv (f.stalkMap (genericPoint X)) ≫ c
  have hginj : Function.Injective g.hom := by
    have h₁ : Function.Injective (X.presheaf.stalkSpecializes hspec).hom := by
      have : (X.presheaf.stalkSpecializes hspec).hom =
          algebraMap (X.presheaf.stalk x) X.functionField :=
        (RingHom.algebraMap_toAlgebra _).symm
      rw [this]
      exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    have h₂ : Function.Injective (inv (f.stalkMap (genericPoint X)) ≫ c).hom :=
      (ConcreteCategory.bijective_of_isIso _).1
    exact h₂.comp h₁
  have hcomm : g.hom.comp (f.stalkMap x).hom =
      algebraMap (Y.presheaf.stalk (f x)) Y.functionField := by
    have hnat := Scheme.Hom.stalkSpecializes_stalkMap f (genericPoint X) x hspec
    have hsq : f.stalkMap x ≫ g = Y.presheaf.stalkSpecializes hspecY := by
      rw [show f.stalkMap x ≫ g =
        (f.stalkMap x ≫ X.presheaf.stalkSpecializes hspec) ≫
          inv (f.stalkMap (genericPoint X)) ≫ c by simp [g, Category.assoc],
        ← hnat, Category.assoc, IsIso.hom_inv_id_assoc,
        TopCat.Presheaf.stalkSpecializes_comp]
    rw [← CommRingCat.hom_comp, hsq,
      ← RingHom.algebraMap_toAlgebra (Y.presheaf.stalkSpecializes hspecY).hom]
  have hbij := bijective_rangeRestrict_comp_of_valuationRing (K := Y.functionField)
    (f.stalkMap x).hom g.hom hcomm
  have hrange : Function.Bijective g.hom.rangeRestrict :=
    ⟨fun a b hab => hginj (congrArg Subtype.val hab), g.hom.rangeRestrict_surjective⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff' hrange (f.stalkMap x).hom).mp hbij

/-- A proper birational morphism of integral schemes onto a normal scheme of dimension at most
one is finite.

This stands in for the finiteness criterion of [Stacks Project, Tag 0AB7]; delete it when that
tag lands. -/
private theorem isFinite_of_isProper_of_isBirational_of_topologicalKrullDim_le_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : X ⟶ Y) [IsProper f] (hf : IsBirational f)
    (hY : topologicalKrullDim Y ≤ (1 : ℕ)) : IsFinite f := by
  have : LocallyQuasiFinite f := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine le_antisymm le_top fun x _ => ?_
    rw [Scheme.Hom.mem_quasiFiniteLocus]
    have := isIso_stalkMap_of_isBirational_of_isNormal f hf hY x
    exact RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end Finiteness

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDiscreteValuationRing R] in
/-- The map `Spec K ⟶ Spec R` sends the generic point to the generic point. -/
private theorem genericPoint_specMap_algebraMap :
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (genericPoint (Spec (.of K))) = genericPoint (Spec (.of R)) := by
  apply PrimeSpectrum.ext
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  change Ideal.comap (algebraMap R K) (⊥ : Ideal K) = ⊥
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact map_eq_zero_iff _ (IsFractionRing.injective R K)

/-- A morphism from an integral scheme to the spectrum of a discrete valuation ring which sends
the generic point to the generic point is flat: the local rings of the source are torsion-free
over the local rings of `Spec R`, which are principal. -/
private theorem flat_of_genericPoint_map {Z : Scheme.{u}} (q : Z ⟶ Spec (.of R)) [IsIntegral Z]
    (hη : q (genericPoint Z) = genericPoint (Spec (.of R))) : Flat q := by
  have hdom : IsDominant q :=
    ((tfae_isDominant_of_isIntegral q).out 2 1).mp hη
  have hstalk : ∀ z : Z, Function.Injective (q.stalkMap z) :=
    ((tfae_isDominant_of_isIntegral q).out 1 6).mp hdom
  rw [Flat.iff_flat_stalkMap]
  intro z
  let A := (Spec (.of R)).presheaf.stalk (q z)
  let B := Z.presheaf.stalk z
  let φ : A →+* B := (q.stalkMap z).hom
  let p := (q z).asIdeal
  have : p.IsPrime := (q z).isPrime
  let L := Localization.AtPrime p
  let e : A ≃+* L :=
    (AlgebraicGeometry.Spec.stalkIso (.of R) (q z)).commRingCatIsoToRingEquiv
  have : IsNoetherianRing R := inferInstance
  have : IsDedekindDomain R :=
    ((IsDiscreteValuationRing.TFAE R (IsDiscreteValuationRing.not_isField R)).out 1 3).mp
      (show IsDiscreteValuationRing R from inferInstance)
  have : IsPrincipalIdealRing L := by
    by_cases hp : p = ⊥
    · have : Field L := IsField.toField <| by
        have : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L p
        rw [IsLocalRing.isField_iff_maximalIdeal_eq]
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        simp [hp]
      infer_instance
    · have : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L p
      have : IsDiscreteValuationRing L :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp L
      infer_instance
  have : IsPrincipalIdealRing A := by
    refine ⟨fun I => ?_⟩
    have hI : (I.map e.toRingHom).IsPrincipal := inferInstance
    have hI' : ((I.map e.toRingHom).map e.symm.toRingHom).IsPrincipal := inferInstance
    have hmap : (I.map e.toRingHom).map e.symm.toRingHom = I := by
      rw [Ideal.map_map]
      simp
    rw [hmap] at hI'
    exact hI'
  let ψ : L →+* B := φ.comp e.symm.toRingHom
  let : Algebra L B := ψ.toAlgebra
  have htf : Module.IsTorsionFree L B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    have hφ : Function.Injective φ := hstalk z
    intro a b hab
    apply e.symm.injective
    exact hφ hab
  have hflat : Module.Flat L B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    exact htf
  have hψ : ψ.Flat := hflat
  have he : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  change φ.Flat
  rw [show φ = ψ.comp e.toRingHom by ext a; simp [ψ]]
  exact RingHom.Flat.comp he hψ

/-- The structure morphism of a model sends the generic point of the total space to the generic
point of `Spec R`, because the generic fibre is a dense open subscheme. -/
private theorem model_genericPoint_map {C X : Scheme.{u}} [IsIntegral C] (p : X ⟶ Spec (.of R))
    [IsIntegral X] (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    p (genericPoint X) = genericPoint (Spec (.of R)) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let P := pullback p i
  let a := pullback.fst p i
  have : IsIntegral P := IsIntegral.of_isIso eX.hom
  have : IsOpenImmersion i := Stacks.Models.genericFiberSpec_isOpenImmersion
  have : IsOpenImmersion a := inferInstance
  have hne : (a.opensRange : Set X).Nonempty := by
    obtain ⟨z⟩ := (inferInstance : Nonempty P)
    exact ⟨a z, ⟨z, rfl⟩⟩
  have hdense : Dense (a.opensRange : Set X) :=
    (preirreducibleSpace_iff_open_dense X).mp inferInstance a.opensRange.2 hne
  have ha : IsDominant a := by
    rw [isDominant_iff, denseRange_iff_closure_range]
    change Dense (Set.range a) at hdense
    exact dense_iff_closure_eq.mp hdense
  have hηa : a (genericPoint P) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral a).out 1 2).mp ha
  have hcommη : p (a (genericPoint P)) = i (pullback.snd p i (genericPoint P)) :=
    congrArg (fun g : P ⟶ Spec (.of R) => g (genericPoint P))
      (pullback.condition : a ≫ p = pullback.snd p i ≫ i)
  have hηsnd : pullback.snd p i (genericPoint P) = genericPoint (Spec (.of K)) :=
    Subsingleton.elim _ _
  rwa [hηa, hηsnd, genericPoint_specMap_algebraMap] at hcommη

/-- **Stacks Project, Tag 0C2U.** A resolution of singularities of a model of a smooth curve is
again a model of that curve. -/
@[stacks 0C2U "resolution_is_model"]
theorem isModel_comp_of_isResolution {C X Y : Scheme.{u}} (c : C ⟶ Spec (.of K)) [Smooth c]
    [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : Stacks.Models.IsModel c p eX) (f : Y ⟶ X) (hf : IsResolution f) :
    ∃ eY : C ≅ pullback (f ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      Stacks.Models.IsModel c (f ≫ p) eY := by
  have hbir := hf.1.1
  have : IsProper f := hf.1.2.1
  have : IsIntegral Y := hf.1.2.2
  let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let PX := pullback p i
  let PY := pullback (f ≫ p) i
  let a := pullback.fst p i
  let b := pullback.fst (f ≫ p) i
  let Q := pullback f a
  let θ := pullbackRightPullbackFstIso p i f
  have : IsOpenImmersion i := Stacks.Models.genericFiberSpec_isOpenImmersion
  have : IsOpenImmersion a := inferInstance
  have : IsOpenImmersion b := inferInstance
  have hηX : p (genericPoint X) = genericPoint (Spec (.of R)) := model_genericPoint_map p eX
  have hηY : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isBirational f hbir
  have hηf : (f ≫ p) (genericPoint Y) = genericPoint (Spec (.of R)) := by
    rw [Scheme.Hom.comp_apply, hηY, hηX]
  have hηrange : (f ≫ p) (genericPoint Y) ∈ i.opensRange := by
    rw [hηf, ← genericPoint_specMap_algebraMap (R := R) (K := K)]
    exact ⟨genericPoint (Spec (.of K)), rfl⟩
  obtain ⟨z, -⟩ : genericPoint Y ∈ b.opensRange := by
    rwa [Scheme.Hom.opensRange_pullbackFst]
  have : Nonempty PY := ⟨z⟩
  have : IsIntegral C := inferInstance
  have : IsIntegral PX := IsIntegral.of_isIso eX.hom
  have : IsOpenImmersion (pullback.fst f a) := inferInstance
  have : Nonempty Q := Nonempty.map θ.inv inferInstance
  have : IsIntegral Q := isIntegral_of_isOpenImmersion (pullback.fst f a)
  have hnormalC : IsNormal C := isNormal_of_isRegular C (isRegular_of_smooth_over_field c)
  have hnormalPX : IsNormal PX := by
    rw [isNormal_iff_stalk_normal]
    intro x
    obtain ⟨w, hw⟩ := (TopCat.homeoOfIso (asIso eX.hom.base)).surjective x
    subst x
    have : IsIso (eX.hom.stalkMap w) := inferInstance
    let er := (asIso (eX.hom.stalkMap w)).commRingCatIsoToRingEquiv
    have hIC : IsIntegrallyClosed (C.presheaf.stalk w) := id (hnormalC.stalk_normal w)
    have hIC' : IsIntegrallyClosed (PX.presheaf.stalk (eX.hom w)) :=
      IsIntegrallyClosed.of_equiv er.symm
    exact ⟨inferInstance, id hIC'⟩
  have hdimPX : topologicalKrullDim PX ≤ (1 : ℕ) := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (TopCat.homeoOfIso (asIso eX.hom.base)).isHomeomorph,
      IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)]
    norm_num
  let q := pullback.snd f a
  have hηα : (pullback.fst f a) (genericPoint Q) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion (pullback.fst f a)
  have hηj : a (genericPoint PX) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion a
  have hpt : a (q (genericPoint Q)) = f ((pullback.fst f a) (genericPoint Q)) :=
    congrArg (fun g : Q ⟶ X => g (genericPoint Q))
      (pullback.condition (f := f) (g := a)).symm
  have hηq : q (genericPoint Q) = genericPoint PX := by
    apply a.isOpenEmbedding.injective
    calc
      a (q (genericPoint Q)) = f ((pullback.fst f a) (genericPoint Q)) := hpt
      _ = genericPoint X := by rw [hηα, hηY]
      _ = a (genericPoint PX) := hηj.symm
  have hstalkq : IsIso (q.stalkMap (genericPoint Q)) := by
    let H := Scheme.stalkMapIsoOfIsPullback
      (IsPullback.of_isLimit (pullback.isLimit f a)) (genericPoint Q)
    have : IsIso (f.stalkMap ((pullback.fst f a) (genericPoint Q))) := by
      rw [hηα]
      exact hbir.isIso_stalkMap _ (by rw [genericPoints_eq_singleton]; simp)
    let u := H.hom.left
    let v := H.hom.right
    have : IsIso u := inferInstance
    have : IsIso v := inferInstance
    have hW : u ≫ q.stalkMap (genericPoint Q) =
        f.stalkMap ((pullback.fst f a) (genericPoint Q)) ≫ v := by
      simpa only [u, v, q, pullback.cone, PullbackCone.fst_limit_cone,
        PullbackCone.snd_limit_cone, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using H.hom.w
    have : IsIso (u ≫ q.stalkMap (genericPoint Q)) := by
      rw [hW]
      infer_instance
    exact IsIso.of_isIso_comp_left (f := u) _
  have hbirq : IsBirational q := by
    apply isBirational_of_bijOn_of_isIso_stalkMap
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      exact Set.bijOn_singleton.mpr hηq
    · intro x hx
      rw [genericPoints_eq_singleton] at hx
      subst x
      exact hstalkq
  have : IsLocallyNoetherian (Spec (.of K)) := inferInstance
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : IsLocallyNoetherian PX := isLocallyNoetherian_of_isOpenImmersion eX.inv
  have : IsNormal PX := hnormalPX
  have : IsFinite q :=
    isFinite_of_isProper_of_isBirational_of_topologicalKrullDim_le_one q hbirq hdimPX
  have : IsIso q := isIso_of_isIntegralHom_of_isBirational_of_isNormal q hbirq
  let eY : C ≅ PY := eX ≪≫ (asIso q).symm ≪≫ θ
  refine ⟨eY, flat_of_genericPoint_map (f ≫ p) hηf, ?_, ?_, ?_⟩
  · have : LocallyOfFiniteType p := hX.2.1
    infer_instance
  · have : QuasiCompact p := hX.2.2.1
    infer_instance
  · change eY.hom ≫ pullback.snd (f ≫ p) i = c
    have hc : eX.hom ≫ pullback.snd p i = c := hX.2.2.2
    simp [eY, θ, q, Category.assoc, pullbackRightPullbackFstIso_hom_snd, hc]

end AlgebraicGeometry
