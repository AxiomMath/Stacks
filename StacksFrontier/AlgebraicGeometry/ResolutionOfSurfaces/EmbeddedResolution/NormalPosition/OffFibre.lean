module

public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform

/-!
# Blowing up a closed point: the picture off the exceptional fibre

Let `p` be a closed point of a scheme `W` and let `b : W' → W` be the blowup of `W` at the
reduced point `p`. Away from the exceptional fibre `b⁻¹(p)` the morphism `b` is an isomorphism,
so nothing local changes there: the local rings of `W'` are those of `W`, the strict transform
of a closed subscheme agrees with its total transform, and local intersection numbers of strict
transforms are those of the original subschemes.

## Main definitions

* `Stacks.ResolutionOfSurfaces.localIntersectionColength`: the length of the local ring at a
  point of the scheme-theoretic intersection of two closed subschemes, as a natural number.

## Main results

* `Stacks.ResolutionOfSurfaces.stalk_transformIdeal_of_ne`: off the exceptional fibre the
  ideal of the strict transform is the image of the ideal of the original subscheme.
* `Stacks.ResolutionOfSurfaces.localIntersectionColength_transformIdeal_of_ne`: off the
  exceptional fibre the local intersection colength of two strict transforms is that of the
  original subschemes.
* `Stacks.ResolutionOfSurfaces.stalk_exceptionalIdeal_of_ne`: off the exceptional fibre the
  exceptional divisor is invisible.

## Implementation notes

The strict transform of `Z ⊆ W` is built in the base change `P = Z ×_W W'` as the kernel ideal of
the inclusion of the open `V ⊆ P` lying off the inverse image of `p`, and
`AlgebraicGeometry.transformIdeal` is the kernel of the composite closed immersion into `W'`. At
a point of `V` the stalk of that kernel ideal vanishes, so the strict transform and `P` have the
same local ring there, and the stalk of `transformIdeal` agrees with the stalk of the kernel of
the projection `P → W'`, which is the inverse image ideal of `Z`.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Local rings off the exceptional fibre -/

/-- The reduced closed point `p` is the support of its own ideal sheaf. -/
public theorem coe_support_centerIdeal {W : Scheme.{u}} (p : W) (hp : IsClosed ({p} : Set W)) :
    ((centerIdeal p hp).support : Set W) = {p} := by
  simp only [centerIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk]

/-- Off the range of a closed immersion the stalk of its kernel ideal sheaf is the unit
ideal. -/
private theorem stalk_ker_eq_top_of_notMem_range {X C : Scheme.{u}} (f : C ⟶ X)
    [IsClosedImmersion f] (x : X) (hx : x ∉ Set.range f) :
    IdealSheafData.stalk f.ker x = ⊤ := by
  rw [IdealSheafData.stalk_eq_top_iff_not_mem_support]
  change x ∉ (f.ker.support : Set X)
  rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]
  exact hx

/-- Composing a ring map with an injective one does not change its kernel. -/
private theorem ker_comp_eq_of_injective {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hψ : Function.Injective ψ.hom) : RingHom.ker (φ ≫ ψ).hom = RingHom.ker φ.hom := by
  rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hψ]

/-- **Off the exceptional fibre the strict transform is the total transform, stalkwise.** At a
point `q` of the blowup at a closed point `p` with `b q ≠ p`, the stalk of the ideal of the
strict transform of `I` is the image of the stalk of `I` at `b q`. -/
public theorem stalk_transformIdeal_of_ne {W : Scheme.{u}} (I : W.IdealSheafData) (p : W)
    (hp : IsClosed ({p} : Set W)) (q : blowUp (centerIdeal p hp))
    (hq : blowUpToBase (centerIdeal p hp) q ≠ p) :
    IdealSheafData.stalk (transformIdeal I p hp) q =
      Ideal.map ((blowUpToBase (centerIdeal p hp)).stalkMap q).hom
        (IdealSheafData.stalk I (blowUpToBase (centerIdeal p hp) q)) := by
  have hcomap : I.comap (blowUpToBase (centerIdeal p hp)) =
      (pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp))).ker := by
    change (pullback.fst (blowUpToBase (centerIdeal p hp)) I.subschemeι).ker = _
    rw [← pullbackSymmetry_hom_comp_fst, Scheme.Hom.ker_comp_of_isIso]
  rw [← IdealSheafData.stalk_comap, hcomap]
  change IdealSheafData.stalk ((strictTransformCenterIdeal I p hp).subschemeι ≫
      pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp))).ker q = _
  have hpt : ∀ y, I.subschemeι (pullback.fst I.subschemeι (blowUpToBase (centerIdeal p hp)) y) =
      blowUpToBase (centerIdeal p hp)
        (pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp)) y) := fun y =>
    congrArg (fun k => k.base y)
      (pullback.condition (f := I.subschemeι) (g := blowUpToBase (centerIdeal p hp)))
  by_cases hq' : q ∈ Set.range (pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp)))
  · obtain ⟨y, rfl⟩ := hq'
    set V : (pullback I.subschemeι (blowUpToBase (centerIdeal p hp))).Opens :=
      (pullback.fst I.subschemeι (blowUpToBase (centerIdeal p hp)) ≫ I.subschemeι) ⁻¹ᵁ
        (centerIdeal p hp).support.compl with hV
    have hyV : y ∈ V := by
      change I.subschemeι (pullback.fst I.subschemeι (blowUpToBase (centerIdeal p hp)) y) ∉
        ((centerIdeal p hp).support : Set W)
      rw [coe_support_centerIdeal p hp, Set.mem_singleton_iff, hpt]
      exact hq
    have hbot : IdealSheafData.stalk (strictTransformCenterIdeal I p hp) y = ⊥ := by
      obtain ⟨v, rfl⟩ : ∃ v : (V : Scheme.{u}), V.ι v = y := ⟨⟨y, hyV⟩, rfl⟩
      have h0 : (strictTransformCenterIdeal I p hp).comap V.ι = ⊥ := by
        rw [strictTransformCenterIdeal_eq_ker]
        exact Stacks.Coherent.comap_ker_self_eq_bot _
      have h1 := IdealSheafData.stalk_comap (strictTransformCenterIdeal I p hp) V.ι v
      rw [h0, stalk_bot] at h1
      have : IsIso (V.ι.stalkMap v) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 v
      exact (Ideal.map_eq_bot_iff_of_injective
        (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective).mp h1.symm
    have hymem : y ∈ Set.range (strictTransformCenterIdeal I p hp).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      by_contra h
      have h' := (IdealSheafData.stalk_eq_top_iff_not_mem_support _ y).mpr h
      rw [hbot] at h'
      exact bot_ne_top h'
    obtain ⟨z, rfl⟩ := hymem
    have e3 := IdealSheafData.stalk_ker_of_isClosedImmersion
      (strictTransformCenterIdeal I p hp).subschemeι z
    rw [Scheme.IdealSheafData.ker_subschemeι, hbot] at e3
    refine (IdealSheafData.stalk_ker_of_isClosedImmersion
      ((strictTransformCenterIdeal I p hp).subschemeι ≫
        pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp))) z).trans ?_
    refine Eq.trans ?_ (IdealSheafData.stalk_ker_of_isClosedImmersion
      (pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp)))
      ((strictTransformCenterIdeal I p hp).subschemeι z)).symm
    rw [Scheme.Hom.stalkMap_comp]
    exact ker_comp_eq_of_injective _ _ ((RingHom.injective_iff_ker_eq_bot _).mpr e3.symm)
  · have hq2 : q ∉ Set.range ((strictTransformCenterIdeal I p hp).subschemeι ≫
        pullback.snd I.subschemeι (blowUpToBase (centerIdeal p hp))) :=
      fun ⟨z, hz⟩ => hq' ⟨_, hz⟩
    rw [stalk_ker_eq_top_of_notMem_range _ _ hq2, stalk_ker_eq_top_of_notMem_range _ _ hq']

/-! ### Local intersection colengths -/

/-- The colength at `x` of the scheme-theoretic intersection of two closed subschemes. -/
public def localIntersectionColength {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) : ℕ :=
  (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
    (IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x))).toNat

/-- The local intersection colength is symmetric in the two closed subschemes. -/
public theorem localIntersectionColength_comm {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    localIntersectionColength I J x = localIntersectionColength J I x := by
  unfold localIntersectionColength
  rw [sup_comm]

/-- The local intersection colength vanishes at a point lying off one of the two closed
subschemes. -/
public theorem localIntersectionColength_eq_zero_of_notMem {X : Scheme.{u}}
    (I J : X.IdealSheafData) (x : X) (h : x ∉ I.support ∨ x ∉ J.support) :
    localIntersectionColength I J x = 0 := by
  have htop : IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x = ⊤ := by
    rcases h with h | h
    · rw [(IdealSheafData.stalk_eq_top_iff_not_mem_support I x).mpr h, top_sup_eq]
    · rw [(IdealSheafData.stalk_eq_top_iff_not_mem_support J x).mpr h, sup_top_eq]
  unfold localIntersectionColength
  rw [htop]
  have : Subsingleton (X.presheaf.stalk x ⧸ (⊤ : Ideal (X.presheaf.stalk x))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Module.length_eq_zero]
  rfl

/-- At a point of the intersection, the local intersection colength is the length of the local
ring of the scheme-theoretic intersection. -/
public theorem localIntersectionColength_eq_intersectionLength {X : Scheme.{u}}
    (I J : X.IdealSheafData) (x : X) (hx : x ∈ (I ⊔ J).support) :
    localIntersectionColength I J x = intersectionLength I J x hx :=
  (intersectionLength_eq_colength I J x hx).symm

/-- **Off the exceptional fibre local intersection colengths of strict transforms are
unchanged.** -/
public theorem localIntersectionColength_transformIdeal_of_ne {W : Scheme.{u}}
    (I J : W.IdealSheafData) (p : W) (hp : IsClosed ({p} : Set W))
    (q : blowUp (centerIdeal p hp)) (hq : blowUpToBase (centerIdeal p hp) q ≠ p) :
    localIntersectionColength (transformIdeal I p hp) (transformIdeal J p hp) q =
      localIntersectionColength I J (blowUpToBase (centerIdeal p hp) q) := by
  have := isIso_stalkMap_blowUpToBase_of_ne (centerIdeal p hp) p (coe_support_centerIdeal p hp) q hq
  let e := (asIso ((blowUpToBase (centerIdeal p hp)).stalkMap q)).commRingCatIsoToRingEquiv
  have hker : RingHom.ker ((blowUpToBase (centerIdeal p hp)).stalkMap q).hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp e.injective
  unfold localIntersectionColength
  rw [stalk_transformIdeal_of_ne I p hp q hq, stalk_transformIdeal_of_ne J p hp q hq,
    ← Ideal.map_sup]
  have h := length_quotient_sup_ker ((blowUpToBase (centerIdeal p hp)).stalkMap q).hom
    e.surjective (IdealSheafData.stalk I (blowUpToBase (centerIdeal p hp) q) ⊔
      IdealSheafData.stalk J (blowUpToBase (centerIdeal p hp) q))
  rw [hker, bot_sup_eq] at h
  rw [← h]

/-- **Off the exceptional fibre the exceptional divisor is invisible**: its ideal has unit
stalk there. -/
public theorem stalk_exceptionalIdeal_of_ne {W : Scheme.{u}} (p : W)
    (hp : IsClosed ({p} : Set W)) (q : blowUp (centerIdeal p hp))
    (hq : blowUpToBase (centerIdeal p hp) q ≠ p) :
    IdealSheafData.stalk (exceptionalIdeal (centerIdeal p hp)) q = ⊤ :=
  (IdealSheafData.stalk_eq_top_iff_not_mem_support _ q).mpr fun h =>
    hq ((mem_exceptionalIdeal_support_iff p hp q).mp h)

/-- Off the exceptional fibre no closed subscheme meets the exceptional divisor. -/
public theorem localIntersectionColength_exceptionalIdeal_of_ne {W : Scheme.{u}} (p : W)
    (hp : IsClosed ({p} : Set W)) (A : (blowUp (centerIdeal p hp)).IdealSheafData)
    (q : blowUp (centerIdeal p hp)) (hq : blowUpToBase (centerIdeal p hp) q ≠ p) :
    localIntersectionColength A (exceptionalIdeal (centerIdeal p hp)) q = 0 :=
  localIntersectionColength_eq_zero_of_notMem _ _ q <| Or.inr fun h =>
    hq ((mem_exceptionalIdeal_support_iff p hp q).mp h)

end Stacks.ResolutionOfSurfaces

end
