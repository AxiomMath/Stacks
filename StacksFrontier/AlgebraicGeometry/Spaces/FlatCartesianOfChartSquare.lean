module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Flatness and cartesianness of a square of closed subspaces from one square of charts

Let
```
X --⊆--→ X'
|f       |g
↓        ↓
Y --⊆--→ Y'
```
be a commutative square of algebraic spaces over a scheme `S` whose horizontal arrows are
inclusions of closed subspaces. Suppose given a surjective étale chart `a' : U' → X'`, an étale
chart `b' : V' → Y'` and `α : U' → V'` over `g`, together with the closed subschemes
`j : U₀ → U'` and `k : V₀ → V'` cut out by `X` and `Y` and a morphism `f₀ : U₀ → V₀`, such that
`α` is flat and the square `(j, f₀, α, k)` of schemes is cartesian. Then `g` is flat and the
square of algebraic spaces is cartesian, `X = Y ×_{Y'} X'`.

## Main results

* `AlgebraicGeometry.Space.isFlat_and_isPullback_of_chartSquare`: `g` is flat and
  `X = Y ×_{Y'} X'`.

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (X : ClosedSubspaces B S hS X'.1)
    (Y : ClosedSubspaces B S hS Y'.1) (g : X' ⟶ Y')
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))

/-- **Flatness and cartesianness from one square of charts.** For a commutative square of
closed subspaces `(X ⊆ X') → (Y ⊆ Y')` over `g`, a surjective étale chart `a' : U' → X'`, an
étale chart `b' : V' → Y'`, `α : U' → V'` over `g`, the closed subschemes `U₀ ⊆ U'` and
`V₀ ⊆ V'` cut out by `X` and `Y`, and `f₀ : U₀ → V₀`, if `α` is flat and the square of schemes
`(j, f₀, α, k)` is cartesian, then `g` is flat and `X = Y ×_{Y'} X'`. -/
theorem isFlat_and_isPullback_of_chartSquare
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    {U' V' U₀ V₀ : BigFppfOver B S hS} (a' : yoneda.obj U' ⟶ X'.1)
    (b' : yoneda.obj V' ⟶ Y'.1) (α : U' ⟶ V') (j : U₀ ⟶ U') (k : V₀ ⟶ V') (f₀ : U₀ ⟶ V₀)
    (p : yoneda.obj U₀ ⟶ X.1.toFunctor) (q : yoneda.obj V₀ ⟶ Y.1.toFunctor)
    (ha'S : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a')
    (ha'E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a')
    (hb'E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b')
    (hα : a' ≫ g.hom = yoneda.map α ≫ b')
    (hpU : IsPullback p (yoneda.map j) X.1.ι a') (hpV : IsPullback q (yoneda.map k) Y.1.ι b')
    (hflatα : Flat ((BigFppfOver.toScheme B S hS).map α))
    (hpb : IsPullback ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map f₀) ((BigFppfOver.toScheme B S hS).map α)
      ((BigFppfOver.toScheme B S hS).map k)) :
    IsFlat B S hS g.hom ∧
      IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y) := by
  refine ⟨(holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
    isEtaleLocalOnSourceAndTarget_flat X'.2 Y'.2 g.hom).2
      ⟨U', V', a', b', α, ha'E, hb'E, ha'S, hα.symm, hflatα⟩, ?_⟩
  have hpbB : IsPullback j f₀ α k := by
    have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hpb
  have h1 : X.1.ι ≫ g.hom = f.hom ≫ Y.1.ι := congrArg (fun m => m.hom) hsq
  have hle : X.1 ≤ Y.1.preimage g.hom := fun T x hx => by
    show g.hom.app T x ∈ Y.1.obj T
    rw [show g.hom.app T x = (f.hom.app T ⟨x, hx⟩).1 from
      ConcreteCategory.congr_hom (congr_app h1 T) ⟨x, hx⟩]
    exact (f.hom.app T ⟨x, hx⟩).2
  let φ := Subfunctor.homOfLe hle
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ := by
    have ha'loc := isLocallySurjective_of_surjective_etale B S hS a' ha'S ha'E
    refine ⟨fun {T} s => (BigFppfOver.topology B S hS).superset_covering ?_
      (ha'loc.imageSieve_mem s.1)⟩
    rintro T' e ⟨u, hu⟩
    have hgu : (b'.app (Opposite.op T') (u ≫ α)) ∈ Y.1.obj (Opposite.op T') := by
      have h2 := ConcreteCategory.congr_hom (congr_app hα (Opposite.op T')) u
      change g.hom.app _ (a'.app _ u) = b'.app _ (u ≫ α) at h2
      rw [← h2, hu]
      exact ((Y.1.preimage g.hom).toFunctor.map e.op s).2
    obtain ⟨v, -, hv⟩ := Types.exists_of_isPullback
      (hpV.map ((evaluation _ _).obj (Opposite.op T')))
      (⟨b'.app (Opposite.op T') (u ≫ α), hgu⟩ : Y.1.toFunctor.obj (Opposite.op T'))
      (u ≫ α) rfl
    change v ≫ k = u ≫ α at hv
    let w : T' ⟶ U₀ := hpbB.lift u v hv.symm
    refine ⟨p.app (Opposite.op T') w, Subtype.ext ?_⟩
    have h3 := ConcreteCategory.congr_hom (congr_app hpU.w (Opposite.op T')) w
    change (p.app (Opposite.op T') w).1 = a'.app (Opposite.op T') (w ≫ j) at h3
    show (p.app (Opposite.op T') w).1 = X'.1.map e.op s.1
    rw [h3, hpbB.lift_fst]
    exact hu
  have hiso : IsIso φ := by
    let J := BigFppfOver.topology B S hS
    have hF : Presheaf.IsSheaf J X.1.toFunctor := X.2.1.isSheaf
    have hG : Presheaf.IsSheaf J (Y.1.preimage g.hom).toFunctor :=
      (isClosedSubspace_preimage B S hS g.hom Y.1 Y'.2 X'.2 Y.2).1.isSheaf
    let ψ : (⟨_, hF⟩ : Sheaf J (Type u)) ⟶ ⟨_, hG⟩ := ObjectProperty.homMk φ
    have hi : Sheaf.IsLocallyInjective ψ :=
      Presheaf.isLocallyInjective_of_injective J φ fun T x y hxy =>
        Subtype.ext (congrArg (fun z : (Y.1.preimage g.hom).toFunctor.obj T => z.1) hxy)
    have _ : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨hi, hloc⟩
    exact (sheafToPresheaf J (Type u)).map_isIso ψ
  have hpre0 := Subfunctor.isPullback_preimage g.hom Y.1
  have hpre := hpre0.flip
  have hcart : IsPullback X.1.ι f.hom g.hom Y.1.ι := by
    refine hpre.of_iso (asIso φ).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
          simp only [φ, Subfunctor.homOfLe_ι]) ?_
      (by simp) (by simp)
    simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv]
    rw [IsIso.eq_inv_comp, ← cancel_mono Y.1.ι, Category.assoc,
      hpre0.w, ← Category.assoc]
    simp only [φ, Subfunctor.homOfLe_ι]
    exact h1
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) hcart

end AlgebraicGeometry.Space

end
