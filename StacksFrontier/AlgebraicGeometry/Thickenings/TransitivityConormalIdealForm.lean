module

public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSequenceIdealForm
public import StacksFrontier.AlgebraicGeometry.Thickenings.TransitivityConormalShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of a local complete intersection, in the form of ideal sheaves

Let `Z --i--→ Y --p--→ X` be morphisms of schemes, let `Z ⊂ A` be a universal first-order
thickening of `Z` over `X` and `Y ⊂ B` one of `Y` over `X`, with inclusions `j_Z`, `j_Y`, and
let `q : A ⟶ B` be a morphism over `X` restricting to `i`.  Let `F` be the fibre product
`Y ×_B A`, with inclusion `j_F : F ⟶ A`, and let `k : W ⟶ F` be a morphism together with an
isomorphism `u : W ≅ Z` carrying `k` to the copy of `Z` inside `F`.  If `i` is a local complete
intersection morphism then the sequence of `𝒪_W`-modules

```
  k^*j_F^*q^*𝓘_Y ⟶ k^*j_F^*𝓘_Z ⟶ k^*𝓘_W
```

pulled back along `k` from the maps of ideal sheaves of the two squares, is short exact.

This is the short exactness of the conormal sequence of [Stacks Project, Tag 06BA] (see also
[Stacks Project, Tag 06AE]) in the form of ideal sheaves, for an arbitrary presentation of the
data: the ambient `F` is any fibre product, not the chosen one, and the copy `W` of `Z` is any
scheme isomorphic to it over `F`.

## Main results

* `Stacks.Thickenings.shortExact_transitivityIdealForm`: for a local complete intersection
  morphism `i`, the sequence above is short exact.

## References

* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.ClosedImmersion Stacks.Immersion

universe u

namespace Stacks.Thickenings

/-- **The map of ideal sheaves of a square of schemes with invertible vertical maps is an
isomorphism.** -/
theorem isIso_idealSheafMap_of_isIso {Z Z' W W' : Scheme.{u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f : Z ⟶ W} {k : Z' ⟶ W'} [IsIso f] [IsIso k] (comm : i ≫ k = f ≫ j) :
    IsIso (idealSheafMap (toShHom_square comm)) := by
  have hι : Mono (idealSheafι i.toLRSHom.toShHom) := inferInstanceAs (Mono (kernel.ι _))
  have heq : idealSheafMap (toShHom_square comm) =
      (modulePullback k.toLRSHom.toShHom).map
          (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
            (asIso f) j).inv ≫
        (Stacks.Conormal.pullbackIdealSheafIsoOfEq i k ((asIso f).hom ≫ j) comm).hom := by
    refine (cancel_mono (idealSheafι i.toLRSHom.toShHom)).mp ?_
    refine (idealSheafMap_comp_ι _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·)
      (Stacks.Conormal.pullbackIdealSheafIsoOfEq_hom_comp_ι i k ((asIso f).hom ≫ j) comm).symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine congrArg (· ≫ _) ?_
    refine Eq.trans ?_ (Functor.map_comp _ _ _)
    exact congrArg _
      (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_inv_comp_ι
        (asIso f) j).symm
  rw [heq]
  infer_instance

section Canonical

variable {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ X)
  (tZ : UniversalFirstOrderThickening (i ≫ p)) (tY : UniversalFirstOrderThickening p)

/-- **Stacks 06BA in the form of ideal sheaves, at the chosen fibre product.**  For a local
complete intersection morphism `i`, the pullback along the inclusion of `Z` into
`Y ×_{Y'} Z'` of the sequence `pr^*h^*𝓘_Y ⟶ pr^*𝓘_Z ⟶ 𝓘_{Z/Y ×_{Y'} Z'}` of ideal sheaves is
short exact, `h : Z' ⟶ Y'` being the morphism of thickenings and `pr` the projection to `Z'`. -/
@[sga "6 VIII 2.6" "partial"]
theorem shortExact_transitivityIdealForm_canonical (hi : IsLocalCompleteIntersectionMorphism i) :
    ∃ h : (modulePullback (relativeInclusion i p tZ tY).toLRSHom.toShHom).map
          ((modulePullback
              (pullback.snd tY.inclusion (transitivityMap i p tZ tY)).toLRSHom.toShHom).map
            (idealSheafMap (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm))) ≫
        (modulePullback (relativeInclusion i p tZ tY).toLRSHom.toShHom).map
          (idealSheafMap (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w)) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have h06 := transitivityConormalShortComplex_shortExact i p tZ tY hi
  have hS : ∃ h : transitivityConormalLeftMap i p tZ tY ≫
      transitivityConormalRightMap i p tZ tY = 0,
      (ShortComplex.mk _ _ h).ShortExact := ⟨_, h06⟩
  refine (shortExact_conormalSequence_iff_idealForm (relativeInclusion i p tZ tY).toLRSHom.toShHom
    tZ.inclusion.toLRSHom.toShHom tY.inclusion.toLRSHom.toShHom
    (pullback.snd tY.inclusion (transitivityMap i p tZ tY)).toLRSHom.toShHom
    (transitivityMap i p tZ tY).toLRSHom.toShHom (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom
    i.toLRSHom.toShHom
    (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w)
    (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm)).mp ?_
  refine (CategoryTheory.ShortComplex.exists_shortExact_mk_iff_of_isIso₃ _ _ _ _
    ((modulePullback i.toLRSHom.toShHom).map (conormalSheafSelfIso tY.inclusion).inv ≫
      (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.app
        ((modulePullback i.toLRSHom.toShHom).obj
          (conormalSheaf tY.inclusion.toLRSHom.toShHom)))
    ((conormalSheafSelfIso tZ.inclusion).inv ≫
      (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.app
        (conormalSheaf tZ.inclusion.toLRSHom.toShHom))
    (conormalSheafSelfIso (relativeInclusion i p tZ tY)).inv ?_ ?_).mp hS
  · have hn := (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.naturality
      (conormalSheafMap (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm))
    have hL : transitivityConormalLeftMap i p tZ tY =
        (modulePullback i.toLRSHom.toShHom).map (conormalSheafSelfIso tY.inclusion).inv ≫
          conormalSheafMap (toShHom_square (inclusion_comp_transitivityMap i p tZ tY).symm) ≫
            (conormalSheafSelfIso tZ.inclusion).hom := rfl
    refine (congrArg (· ≫ _) hL).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)))).trans ?_
    refine (congrArg (_ ≫ ·) hn).trans ?_
    exact (Category.assoc _ _ _).symm
  · have hn := (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.naturality
      (conormalSheafSelfIso tZ.inclusion).inv
    have hR : transitivityConormalRightMap i p tZ tY =
        (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.app _ ≫
          (modulePullback (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).map
            (conormalSheafSelfIso tZ.inclusion).inv ≫
          conormalSheafMap (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w) ≫
            (conormalSheafSelfIso (relativeInclusion i p tZ tY)).hom := rfl
    refine (congrArg (· ≫ _) hR).trans ?_
    have h1 : (conormalSheafMap
          (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w) ≫
          (conormalSheafSelfIso (relativeInclusion i p tZ tY)).hom) ≫
        (conormalSheafSelfIso (relativeInclusion i p tZ tY)).inv =
        conormalSheafMap (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w) :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
        (Category.comp_id _))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ _) hn.symm

end Canonical

section General

variable {Z Y X A B F W : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ X) (jZ : Z ⟶ A) (jY : Y ⟶ B)
  (pA : A ⟶ X) (pB : B ⟶ X) (q : A ⟶ B) (jF : F ⟶ A) (ρ : F ⟶ Y) (k : W ⟶ F) (u : W ⟶ Z)

/-- **Stacks 06BA in the form of ideal sheaves.**  Let `Z ⊂ A` be a universal first-order
thickening of `Z` over `X` and `Y ⊂ B` one of `Y` over `X`, `q : A ⟶ B` a morphism over `X`
restricting to `i`, `F` a fibre product `Y ×_B A` with inclusion `j_F` and `k : W ⟶ F` a
morphism with an isomorphism `u : W ⟶ Z` carrying it to the copy of `Z` inside `F`.  If `i` is a
local complete intersection morphism, the pullback along `k` of the sequence
`j_F^*q^*𝓘_Y ⟶ j_F^*𝓘_Z ⟶ 𝓘_W` of ideal sheaves is short exact. -/
@[sga "6 VIII 2.6" "partial"]
theorem shortExact_transitivityIdealForm
    (hZ : IsUniversalFirstOrderThickening (i ≫ p) jZ pA)
    (hY : IsUniversalFirstOrderThickening p jY pB) (hq : jZ ≫ q = i ≫ jY) (hqb : q ≫ pB = pA)
    (hF : IsPullback ρ jF jY q) [IsIso u] (hk : k ≫ jF = u ≫ jZ) (hkρ : k ≫ ρ = u ≫ i)
    (hi : IsLocalCompleteIntersectionMorphism i) :
    ∃ h : (modulePullback k.toLRSHom.toShHom).map
          ((modulePullback jF.toLRSHom.toShHom).map (idealSheafMap (toShHom_square hq))) ≫
        (modulePullback k.toLRSHom.toShHom).map (idealSheafMap (toShHom_square hk)) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have hT : q = transitivityMap i p ⟨A, jZ, pA, hZ⟩ ⟨B, jY, pB, hY⟩ :=
    universalFirstOrderThickeningMap_unique ⟨A, jZ, pA, hZ⟩ ⟨B, jY, pB, hY⟩ i (𝟙 X)
      (transitivity_comm i p) q hq (by rw [hqb, Category.comp_id])
  subst hT
  set tZ : UniversalFirstOrderThickening (i ≫ p) := ⟨A, jZ, pA, hZ⟩
  set tY : UniversalFirstOrderThickening p := ⟨B, jY, pB, hY⟩
  have hex := exactFunctor_modulePullback_of_isFlat u.toLRSHom.toShHom
    (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom u)
  have hcan := CategoryTheory.ShortComplex.exists_shortExact_mk_map
    (modulePullback u.toLRSHom.toShHom) _ _
    (shortExact_transitivityIdealForm_canonical i p tZ tY hi)
  have hv₁ : hF.isoPullback.hom ≫ pullback.snd jY (transitivityMap i p tZ tY) = jF :=
    hF.isoPullback_hom_snd
  have hv₂ : hF.isoPullback.hom ≫ pullback.fst jY (transitivityMap i p tZ tY) = ρ :=
    hF.isoPullback_hom_fst
  have hkv : k ≫ hF.isoPullback.hom = u ≫ relativeInclusion i p tZ tY := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₂, hkρ, Category.assoc]
      exact congrArg (u ≫ ·) (relativeInclusion_comp_fst i p tZ tY).symm
    · rw [Category.assoc, hv₁, hk, Category.assoc]
      exact congrArg (u ≫ ·) (relativeInclusion_comp_snd i p tZ tY).symm
  have hψ := isIso_idealSheafMap_of_isIso hkv
  set e := hF.isoPullback.hom.toLRSHom.toShHom
  set s := (pullback.snd jY (transitivityMap i p tZ tY)).toLRSHom.toShHom
  set r := (relativeInclusion i p tZ tY).toLRSHom.toShHom
  have hvs : e ≫ s = jF.toLRSHom.toShHom := congrArg (fun g : F ⟶ A => g.toLRSHom.toShHom) hv₁
  have hkv' : u.toLRSHom.toShHom ≫ r = k.toLRSHom.toShHom ≫ e :=
    congrArg (fun g : W ⟶ _ => g.toLRSHom.toShHom) hkv.symm
  refine (CategoryTheory.ShortComplex.exists_shortExact_mk_iff_of_replacement
    (D := modulePullback u.toLRSHom.toShHom) (I := modulePullback r) (K₀ := modulePullback e)
    (idealSheafMap (toShHom_square hq))
    (idealSheafMap (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w))
    (idealSheafMap (toShHom_square hk)) (idealSheafMap (toShHom_square hkv))
    (fun N => (modulePullbackComp e s).inv.app N ≫
      (eqToHom (congrArg (fun g => modulePullback g) hvs)).app N)
    (fun N => @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (NatIso.isIso_app_of_isIso _ N))
    (fun f => by
      have h1 := (modulePullbackComp e s).inv.naturality f
      have h2 := (eqToHom (congrArg (fun g => modulePullback g) hvs)).naturality f
      simp only [Functor.comp_map] at h1
      rw [reassoc_of% h1, h2, Category.assoc])
    (fun N => (modulePullbackComp u.toLRSHom.toShHom r).inv.app N ≫
      (eqToHom (congrArg (fun g => modulePullback g) hkv')).app N ≫
      (modulePullbackComp k.toLRSHom.toShHom e).hom.app N)
    (fun N => @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ N) inferInstance))
    (fun f => by
      have h1 := (modulePullbackComp u.toLRSHom.toShHom r).inv.naturality f
      have h2 := (eqToHom (congrArg (fun g => modulePullback g) hkv')).naturality f
      have h3 := (modulePullbackComp k.toLRSHom.toShHom e).hom.naturality f
      simp only [Functor.comp_map] at h1 h3
      rw [reassoc_of% h1, reassoc_of% h2, h3, Category.assoc, Category.assoc])
    ?_).mp hcan
  have c : k.toLRSHom.toShHom ≫ e ≫ s =
      (u.toLRSHom.toShHom ≫ (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom) ≫ jZ.toLRSHom.toShHom := by
    rw [← Category.assoc, toShHom_square hkv, Category.assoc,
      toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w, Category.assoc]
  have hc := idealSheafMap_comp (toShHom_square hkv)
    (toShHom_square (isPullback_relativeInclusion_inclusion i p tZ tY).w) c
  have hcg := idealSheafMap_congr hvs c (toShHom_square hk)
  refine ((Iso.inv_hom_id_app_assoc (modulePullbackComp e s) _ _).symm.trans
    (congrArg (_ ≫ ·) hc.symm)).trans ?_
  exact (congrArg (_ ≫ ·) hcg).trans (Category.assoc _ _ _).symm

end General

end Stacks.Thickenings

end
