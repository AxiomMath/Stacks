module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveFunctor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ReducedInvariance
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SymmetricSquarePlane
public import StacksCore.Tactic.StacksAttribute

/-!
# The functor of effective relative cycles is not representable

Let `S` be a locally Noetherian scheme and let `f : X ⟶ S` be locally of finite type. Stacks
Remark 0H5Y asks whether the functor `S' ↦ z^eff(X'/S', r)`, `X' = S' ×_S X`, on schemes locally
of finite type over `S` is representable, and answers that it cannot be, because
`z(X'/S', r) = z(X'_red/S'_red, r)`; the counter example is left to the reader. This file makes the
counter example: for a finite purely inseparable extension `K/k` of degree `> 1`, `S = Spec k` and
`X = Spec K`, the functor is not representable. Together with the characteristic `2` example of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SymmetricSquarePlane` this shows that the
functor is not representable in general.

## Main results

* `Stacks.Chow.effectiveRelativeCyclesMap_injective` — the map of the functor along a morphism
  surjective on points is injective; in particular along `S'_red ⟶ S'`.
* `Stacks.Chow.not_isRepresentable_effectiveRelativeCyclesFunctor_specFieldExt` — the counter
  example over an imperfect field.
* `Stacks.Chow.exists_not_isRepresentable_effectiveRelativeCyclesFunctor` — the functor is not
  representable for some `f : X ⟶ S` as in the remark.

## Implementation notes

The argument is the one the remark points at. Suppose `M` represents the functor and let
`ξ ∈ z^eff(X ×_S X / X, 0)` be the cycle of the diagonal of `X = Spec K`. The two pullbacks of the
corresponding morphism `X ⟶ M` to `D = X ×_S X` agree after restriction to `D_red`, the two
projections `D_red ⟶ X` being equal (`K/k` has at most one `k`-embedding into a reduced ring),
and base change of relative cycles to `D_red` is injective; so the morphism `X ⟶ M` coequalizes
the two projections and descends along the effective epimorphism `Spec K ⟶ Spec k`. The cycle `ξ`
would then be the base change of a cycle on `X/S`, which is impossible: `ξ` is a single
`K`-rational point of `X ×_S X` with coefficient one, while base change along `K/k` multiplies the
coefficient of such a point by `[K : k]`
(`Stacks.Chow.finrank_dvd_of_baseChangeFamilyOfIsPullback_eq_single`).

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Lemma 0H5G](https://stacks.math.columbia.edu/tag/0H5G)
* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

/-! ### Maps of the functor along surjections are injective -/

section Injective

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ)

/-- Base change of effective relative cycles along a morphism surjective on points is injective
(Tag 0H4X, part (1)). -/
theorem effectiveRelativeCyclesMap_injective {T₁ T₂ : LocallyOfFiniteTypeOver S} (h : T₂ ⟶ T₁)
    (hs : Function.Surjective h.hom.left) :
    Function.Injective (effectiveRelativeCyclesMap f r h) := by
  intro α β hαβ
  have h1 := congrArg (fun γ : ↥(effectiveRelativeCycles (pullback.snd f T₂.obj.hom) r) =>
    γ.1.1) hαβ
  simp only [effectiveRelativeCyclesMap_coe] at h1
  rw [baseChangeFamilyOfIsPullback_eq_iff] at h1
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  obtain ⟨t, rfl⟩ := hs s
  exact h1 t

end Injective

/-! ### A purely inseparable extension of the base field -/

section PurelyInseparable

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The morphism `Spec K ⟶ Spec k` attached to an extension of fields. -/
abbrev specFieldExt : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- A purely inseparable extension of fields is an epimorphism onto reduced schemes: two
morphisms from a reduced scheme to `Spec K` which agree after `Spec K ⟶ Spec k` agree. -/
theorem eq_of_comp_specFieldExt_eq [IsPurelyInseparable k K] {Z : Scheme.{u}} [IsReduced Z]
    (g₁ g₂ : Z ⟶ Spec (.of K)) (h : g₁ ≫ specFieldExt k K = g₂ ≫ specFieldExt k K) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k K))
  have key : ∀ g : Z ⟶ Spec (.of K),
      ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.comp (algebraMap k K) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ specFieldExt k K).appTop).hom := by
    intro g
    have h2 : CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv =
        (Scheme.ΓSpecIso (.of k)).inv ≫ (specFieldExt k K).appTop := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← h2]
    rfl
  have hinj := IsPurelyInseparable.injective_comp_algebraMap k K Γ(Z, ⊤)
    (show ((Scheme.ΓSpecIso (.of K)).inv ≫ g₁.appTop).hom.comp (algebraMap k K) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ g₂.appTop).hom.comp (algebraMap k K) by
      rw [key, key, h])
  have h3 : (Scheme.ΓSpecIso (.of K)).inv ≫ g₁.appTop =
      (Scheme.ΓSpecIso (.of K)).inv ≫ g₂.appTop := CommRingCat.hom_ext hinj
  exact (cancel_epi _).mp h3

variable [FiniteDimensional k K]

/-- For a finite extension `K / k`, the morphism `Spec K ⟶ Spec k` is locally of finite type. -/
instance locallyOfFiniteType_specFieldExt : LocallyOfFiniteType (specFieldExt k K) :=
  haveI := Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field (k := k) (A := K)
  Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank _ (Module.finrank k K)

/-- `Spec k`, as a scheme locally of finite type over itself. -/
abbrev baseObj : LocallyOfFiniteTypeOver (Spec (.of k)) := objOf (𝟙 (Spec (.of k)))

/-- `Spec K`, as a scheme locally of finite type over `Spec k`. -/
abbrev extObj : LocallyOfFiniteTypeOver (Spec (.of k)) := objOf (specFieldExt k K)

/-- `Spec K ×_k Spec K`, as a scheme locally of finite type over `Spec k`. -/
def pairObj : LocallyOfFiniteTypeOver (Spec (.of k)) :=
  ⟨Over.mk (pullback.fst (specFieldExt k K) (specFieldExt k K) ≫ specFieldExt k K),
    inferInstanceAs (LocallyOfFiniteType (pullback.fst (specFieldExt k K) (specFieldExt k K) ≫
      specFieldExt k K))⟩

/-- The reduction of `Spec K ×_k Spec K`, as a scheme locally of finite type over `Spec k`. -/
def pairRedObj : LocallyOfFiniteTypeOver (Spec (.of k)) :=
  ⟨Over.mk ((pullback (specFieldExt k K) (specFieldExt k K)).reductionι ≫
      pullback.fst (specFieldExt k K) (specFieldExt k K) ≫ specFieldExt k K),
    inferInstanceAs (LocallyOfFiniteType ((pullback (specFieldExt k K)
      (specFieldExt k K)).reductionι ≫ pullback.fst (specFieldExt k K) (specFieldExt k K) ≫
        specFieldExt k K))⟩

/-- `Spec K ⟶ Spec k` as a morphism over `Spec k`. -/
def extToBase : extObj k K ⟶ baseObj k :=
  ObjectProperty.homMk (Over.homMk (specFieldExt k K) (Category.comp_id _))

/-- The first projection `Spec K ×_k Spec K ⟶ Spec K`. -/
def pairFst : pairObj k K ⟶ extObj k K :=
  ObjectProperty.homMk (Over.homMk (pullback.fst (specFieldExt k K) (specFieldExt k K)) rfl)

/-- The second projection `Spec K ×_k Spec K ⟶ Spec K`. -/
def pairSnd : pairObj k K ⟶ extObj k K :=
  ObjectProperty.homMk (Over.homMk (pullback.snd (specFieldExt k K) (specFieldExt k K))
    pullback.condition.symm)

/-- The reduction morphism of `Spec K ×_k Spec K`. -/
def pairRedι : pairRedObj k K ⟶ pairObj k K :=
  ObjectProperty.homMk (Over.homMk (pullback (specFieldExt k K) (specFieldExt k K)).reductionι
    rfl)

/-- `Spec K ⟶ Spec k` is surjective, both spectra being single points. -/
instance surjective_specFieldExt : Surjective (specFieldExt k K) :=
  ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- `Spec K ⟶ Spec k` is flat. -/
instance flat_specFieldExt : Flat (specFieldExt k K) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))

/-- The two projections `Spec K ×_k Spec K ⟶ Spec K` agree on the reduction: there is at most
one `k`-algebra map from a purely inseparable extension to a reduced ring. -/
theorem pairRedι_comp_pairFst [IsPurelyInseparable k K] :
    pairRedι k K ≫ pairFst k K = pairRedι k K ≫ pairSnd k K := by
  ext : 2
  change (pullback (specFieldExt k K) (specFieldExt k K)).reductionι ≫ pullback.fst _ _ =
    (pullback (specFieldExt k K) (specFieldExt k K)).reductionι ≫ pullback.snd _ _
  exact eq_of_comp_specFieldExt_eq k K _ _ (by simp only [Category.assoc, pullback.condition])

/-- A morphism which is an isomorphism induces a surjection on every residue field. -/
theorem surjective_residueFieldMap_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [hg : IsIso g]
    (x : X) : Function.Surjective (g.residueFieldMap x) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2

/-- The diagonal composed with the top edge of the square relating `Spec K ×_k Spec K` to
`Spec K ×_k Spec k` is an isomorphism. -/
theorem isIso_graphSection_comp_overBaseChangeMap :
    IsIso (graphSection (specFieldExt k K) (𝟙 (Over.mk (specFieldExt k K))) ≫
      overBaseChangeMap (specFieldExt k K) (extToBase k K).hom) := by
  have h : (graphSection (specFieldExt k K) (𝟙 (Over.mk (specFieldExt k K))) ≫
      overBaseChangeMap (specFieldExt k K) (extToBase k K).hom) ≫
      pullback.fst (specFieldExt k K) (baseObj k).obj.hom = 𝟙 _ := by
    simp only [overBaseChangeMap, graphSection, Category.assoc, pullback.lift_fst]
    rfl
  have : IsIso ((graphSection (specFieldExt k K) (𝟙 (Over.mk (specFieldExt k K))) ≫
      overBaseChangeMap (specFieldExt k K) (extToBase k K).hom) ≫
      pullback.fst (specFieldExt k K) (baseObj k).obj.hom) := by rw [h]; infer_instance
  have : IsIso (pullback.fst (specFieldExt k K) (baseObj k).obj.hom) :=
    inferInstanceAs (IsIso (pullback.fst (specFieldExt k K) (𝟙 (Spec (.of k)))))
  exact IsIso.of_isIso_comp_right _ (pullback.fst (specFieldExt k K) (baseObj k).obj.hom)

/-- **Stacks Project, Remark 0H5Y.** Let `k` be a field and let `K/k` be a finite purely
inseparable extension of degree `> 1`, so that `S = Spec k` is Noetherian and
`f : X = Spec K ⟶ S` is finite. The functor `S' ↦ z^eff(X'/S', 0)`, `X' = S' ×_S X`, on schemes
locally of finite type over `S` is not representable.

This is the reason the source gives, made into a counter example: relative cycles do not see
nilpotents. If `M` represented the functor, the diagonal cycle `ξ ∈ z^eff(X_K/Spec K, 0)` would
be a morphism `Spec K ⟶ M` whose two pullbacks to `Spec K ×_k Spec K` agree, because they agree
on the reduction and base change to the reduction is injective; as `Spec K ⟶ Spec k` is an
effective epimorphism, `ξ` would come from `z^eff(X/S, 0)`. But the cycle `ξ` is one rational
point with coefficient one, while every base change of a cycle along `K/k` has coefficients
divisible by `[K : k]` at such a point. -/
@[stacks 0H5Y "the functor S' ↦ z^eff(X'/S', r) is not representable, the counter example the \
remark leaves to the reader, built from z(X'/S', r) = z(X'_red/S'_red, r)"]
theorem not_isRepresentable_effectiveRelativeCyclesFunctor_specFieldExt
    [IsPurelyInseparable k K] (hK : Module.finrank k K ≠ 1) :
    ¬ (effectiveRelativeCyclesFunctor (specFieldExt k K) 0).IsRepresentable := by
  classical
  rintro ⟨M, ⟨R⟩⟩
  set F := effectiveRelativeCyclesFunctor (specFieldExt k K) 0
  set ξ := diagonalRelativeCycle (specFieldExt k K)
  set φ := R.homEquiv.symm ξ
  -- the two pullbacks of `ξ` to `Spec K ×_k Spec K` agree
  have hpr : pairFst k K ≫ φ = pairSnd k K ≫ φ := by
    apply R.homEquiv.injective
    rw [R.homEquiv_comp, R.homEquiv_comp, Equiv.apply_symm_apply]
    apply effectiveRelativeCyclesMap_injective (specFieldExt k K) 0 (pairRedι k K)
      (pullback (specFieldExt k K) (specFieldExt k K)).surjective_reductionι
    change (effectiveRelativeCyclesMap _ 0 (pairRedι k K) ∘
        effectiveRelativeCyclesMap _ 0 (pairFst k K)) ξ =
      (effectiveRelativeCyclesMap _ 0 (pairRedι k K) ∘
        effectiveRelativeCyclesMap _ 0 (pairSnd k K)) ξ
    rw [← effectiveRelativeCyclesMap_comp, ← effectiveRelativeCyclesMap_comp,
      pairRedι_comp_pairFst]
  -- so `φ` descends along the effective epimorphism `Spec K ⟶ Spec k`
  have : IsRegularEpi (specFieldExt k K) := isRegularEpi_of_flat_of_surjective_of_isAffine _
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Spec (.of K) ⟶ M.obj.left, φ₀ = φ.hom.left := ⟨_, rfl⟩
  have h3 : pullback.fst (specFieldExt k K) (specFieldExt k K) ≫ φ₀ =
      pullback.snd (specFieldExt k K) (specFieldExt k K) ≫ φ₀ := by
    rw [hφ₀]
    exact congrArg (fun m : pairObj k K ⟶ M => m.hom.left) hpr
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (.of K)),
      g₁ ≫ specFieldExt k K = g₂ ≫ specFieldExt k K → g₁ ≫ φ₀ = g₂ ≫ φ₀ := by
    intro Z g₁ g₂ hg
    calc g₁ ≫ φ₀
        = pullback.lift g₁ g₂ hg ≫ (pullback.fst (specFieldExt k K) (specFieldExt k K) ≫
            φ₀) := by rw [← Category.assoc, pullback.lift_fst]
      _ = pullback.lift g₁ g₂ hg ≫ (pullback.snd (specFieldExt k K) (specFieldExt k K) ≫
            φ₀) := by rw [h3]
      _ = g₂ ≫ φ₀ := by rw [← Category.assoc, pullback.lift_snd]
  let ψ₀ : Spec (.of k) ⟶ M.obj.left := EffectiveEpi.desc (specFieldExt k K) φ₀ hdesc
  have hfac : specFieldExt k K ≫ ψ₀ = φ₀ := EffectiveEpi.fac _ _ _
  have hw : ψ₀ ≫ M.obj.hom = 𝟙 _ := by
    rw [← cancel_epi (specFieldExt k K), ← Category.assoc, hfac, hφ₀]
    exact (Over.w φ.hom).trans (Category.comp_id _).symm
  let ψ : baseObj k ⟶ M := ObjectProperty.homMk (Over.homMk ψ₀ hw)
  have hψ : extToBase k K ≫ ψ = φ := by
    ext : 2
    exact hfac.trans hφ₀
  -- hence `ξ` is a base change from `Spec k`
  set c := R.homEquiv ψ
  have hc : F.map (extToBase k K).op c = ξ := by
    rw [← R.homEquiv_comp, hψ, Equiv.apply_symm_apply]
  have hcfam := congrArg (fun γ : F.obj (op (extObj k K)) => γ.1.1) hc
  simp only [F, effectiveRelativeCyclesFunctor_map_coe] at hcfam
  -- the point of `Spec K` and the point of the diagonal over it
  let t : Spec (.of K) := Nonempty.some inferInstance
  set σ := graphSection (specFieldExt k K) (𝟙 (Over.mk (specFieldExt k K)))
  obtain ⟨Q, hQ⟩ : σ t ∈ Set.range ((pullback.snd (specFieldExt k K)
      (extObj k K).obj.hom).fiberι t) := by
    rw [Scheme.Hom.range_fiberι]
    change (σ ≫ pullback.snd _ _) t = t
    rw [graphSection_snd]
    rfl
  have hfinrank : let := ((extToBase k K).hom.left.residueFieldMap t).hom.toAlgebra
      Module.finrank ((baseObj k).obj.left.residueField ((extToBase k K).hom.left t))
        ((extObj k K).obj.left.residueField t) = Module.finrank k K :=
    finrank_residueFieldMap_specMap k K t
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  have hdvd := finrank_dvd_of_baseChangeFamilyOfIsPullback_eq_single
    (pullback.snd (specFieldExt k K) (baseObj k).obj.hom)
    (isPullback_overBaseChange (specFieldExt k K) (extToBase k K).hom) t c.1.1 Q 1
    (hfin := by
      let := ((extToBase k K).hom.left.residueFieldMap t).hom.toAlgebra
      exact Module.finite_of_finrank_pos (hfinrank ▸ hpos))
    (residueDegree_restrictedFiberMap_eq_one_of_section _ _ _ _ _ t σ
      (@surjective_residueFieldMap_of_isIso _ _ _
        (isIso_graphSection_comp_overBaseChangeMap k K) t) Q hQ)
    (by
      intro x
      rw [hcfam]
      refine (familyAssociatedToClosedSubscheme_apply_of_section _ σ
        (graphSection_snd (specFieldExt k K) _) t x).trans ?_
      congr 1
      exact propext ⟨fun h => (Scheme.Hom.fiberι _ t).isEmbedding.injective (h.trans hQ.symm),
        fun h => h ▸ hQ⟩)
  have hd : ((Module.finrank k K : ℕ) : ℤ) ∣ 1 := hfinrank ▸ hdvd
  exact hK (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd)

end PurelyInseparable

/-- **Stacks Project, Remark 0H5Y.** The functor `S' ↦ z^eff(X'/S', r)`, `X' = S' ×_S X`, on
schemes locally of finite type over `S` is not representable in general: there are a locally
Noetherian scheme `S`, a morphism `f : X ⟶ S` locally of finite type and an `r ≥ 0` for which it is
not representable. One may take `S = Spec 𝔽₂`, `X = A²` and `r = 0`
(`Stacks.Chow.SymPlane.not_isRepresentable`). -/
@[stacks 0H5Y "the functor S' ↦ z^eff(X'/S', r) cannot be representable in general"]
theorem exists_not_isRepresentable_effectiveRelativeCyclesFunctor :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S) (_ : LocallyOfFiniteType f) (_ : IsLocallyNoetherian S)
      (r : ℕ), ¬ (effectiveRelativeCyclesFunctor f r).IsRepresentable :=
  ⟨_, _, SymPlane.planeHom (ULift.{u} (ZMod 2)), inferInstance, inferInstance, 0,
    SymPlane.not_isRepresentable _⟩

end Stacks.Chow

end
