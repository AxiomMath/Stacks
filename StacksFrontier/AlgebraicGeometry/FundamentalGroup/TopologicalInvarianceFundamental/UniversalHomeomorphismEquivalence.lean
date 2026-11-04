module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.CoverEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite étale covers are invariant under universal homeomorphisms

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Base change along `f` is an
equivalence `FÉt_Y ⥤ FÉt_X`, `V ↦ V ×_Y X`; consequently, for connected `X` and `Y`, the induced
map `π₁(X, x) → π₁(Y, f ∘ x)` of étale fundamental groups is an isomorphism.

## Main results

* `AlgebraicGeometry.isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism` — an étale
  morphism `V ⟶ Y` whose base change along a universal homeomorphism `X ⟶ Y` is finite is
  itself finite.
* `AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism` — base
  change along a universal homeomorphism is an equivalence of categories of finite étale covers.
* `AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism` — for connected
  `X` and `Y`, the induced continuous homomorphism of étale fundamental groups is an isomorphism
  of topological groups.
* `AlgebraicGeometry.etaleFundamentalGroupMap_bijective_of_universalHomeomorphism` — in
  particular the induced map of étale fundamental groups is bijective.
* `AlgebraicGeometry.finiteEtaleBaseChange_pullbackFst_specMap_algebraMap_isEquivalence` — the
  case of the base change `Y_K ⟶ Y` along a purely inseparable field extension `K/k`.

## Implementation notes

The source proves essential surjectivity by descending a finite étale cover of `X` along `X/Y`,
the descent datum coming from the fact that the diagonal of `f` is a thickening. Here the
equivalence of small étale sites along `f`, `Stacks.Etale.etalePullback_isEquivalence`
(Stacks 04DZ), is available, so it remains to see that an étale `V ⟶ Y` is finite once
`V ×_Y X ⟶ X` is. The projection `V ×_Y X ⟶ V` is surjective and universally closed, being a
base change of `f`, and `V ×_Y X ⟶ Y` is finite; hence `V ⟶ Y` is quasi-compact, universally
closed and separated, so proper, and an étale proper morphism is finite by Zariski's main theorem
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). This is the source's omitted
finiteness argument, whose hint is that `U ⟶ V` is surjective and `U ⟶ Y` is integral.

The isomorphism of fundamental groups is
`AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange` (Stacks 0BQA)
applied to this equivalence, so it is the canonical map
`AlgebraicGeometry.etaleFundamentalGroupMap`.

## References

* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Finiteness descends along a universal homeomorphism for étale morphisms.** Let
`f : X ⟶ Y` be a universal homeomorphism and `g : V ⟶ Y` étale. If the base change
`V ×_Y X ⟶ X` is finite then `g` is finite: `g` is quasi-compact, universally closed and
separated because `V ×_Y X ⟶ V` is surjective and universally closed with finite composite to
`Y`, and a proper étale morphism is finite. -/
theorem isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism {V : Scheme.{u}}
    (f : X ⟶ Y) [UniversalHomeomorphism f] (g : V ⟶ Y) [Etale g]
    [IsFinite (pullback.snd g f)] : IsFinite g := by
  obtain ⟨_, _, _⟩ := (universalHomeomorphism_iff_integral_universallyInjective_surjective
    f).mp inferInstance
  have hcomp : IsIntegralHom (pullback.fst g f ≫ g) := by
    rw [pullback.condition]
    infer_instance
  have _ : QuasiCompact g := quasiCompact_of_comp_of_surjective (pullback.fst g f) g
  have _ : UniversallyClosed g := UniversallyClosed.of_comp_surjective (pullback.fst g f) g
  have _ : IsSeparated g := by
    let A : Over Y := Over.mk (pullback.fst g f ≫ g)
    let φ : A ⟶ Over.mk g := Over.homMk (pullback.fst g f) rfl
    have : Surjective φ.left := inferInstanceAs (Surjective (pullback.fst g f))
    have : UniversallyClosed φ.left := inferInstanceAs (UniversallyClosed (pullback.fst g f))
    have : IsSeparated A.hom := inferInstanceAs (IsSeparated (pullback.fst g f ≫ g))
    exact isSeparated_of_surjective_universallyClosed φ
  have _ : IsProper g := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- **Topological invariance of finite étale covers.** Let `f : X ⟶ Y` be a universal
homeomorphism of schemes. Then base change `FÉt_Y ⥤ FÉt_X`, `V ↦ V ×_Y X`, is an equivalence of
categories.

Base change along `f` is an equivalence of small étale sites (Stacks 04DZ), and an étale
`V ⟶ Y` is finite exactly when `V ×_Y X ⟶ X` is, by
`AlgebraicGeometry.isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism`; so the
equivalence restricts to the finite étale covers. -/
@[stacks 0BQN "the equivalence `FÉt_Y ⥤ FÉt_X`",
  ega "IV 18.1.2" "special case",
  sga "1 IX 1.7" "partial",
  sga "1 IX 4.10" "special case",
  sga "1 IX 6.8" "special case",
  sga "4½ Th_finitude 2.7" "partial"]
theorem finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (finiteEtaleBaseChange f).IsEquivalence := by
  obtain ⟨_, _, _⟩ := (universalHomeomorphism_iff_integral_universallyInjective_surjective
    f).mp inferInstance
  let _ : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  let _ : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let E : Y.Etale ⥤ X.Etale := MorphismProperty.Over.pullback (@Etale) ⊤ f
  have _ : E.IsEquivalence := Stacks.Etale.etalePullback_isEquivalence f
  let F := finiteEtaleBaseChange f
  let G := finiteEtaleToEtale X
  let G' := finiteEtaleToEtale Y
  have hobj : ∀ A : FiniteEtaleOver Y, G.obj (F.obj A) = E.obj (G'.obj A) := fun _ ↦ rfl
  have hmap : ∀ {A B : FiniteEtaleOver Y} (φ : A ⟶ B),
      G.map (F.map φ) = E.map (G'.map φ) := fun _ ↦ rfl
  have hGff := finiteEtaleToEtaleFullyFaithful X
  have hG'ff := finiteEtaleToEtaleFullyFaithful Y
  have _ : G.Faithful := hGff.faithful
  have _ : G'.Faithful := hG'ff.faithful
  have hfaithful : F.Faithful :=
    ⟨fun {_ _} φ ψ h ↦ G'.map_injective (E.map_injective (by rw [← hmap φ, ← hmap ψ, h]))⟩
  have hfull : F.Full := by
    refine Functor.Full.mk ?_
    intro A B φ
    refine ⟨hG'ff.preimage (E.preimage (G.map φ)), G.map_injective ?_⟩
    rw [hmap, hG'ff.map_preimage]
    exact E.map_preimage _
  have hess : F.EssSurj := by
    refine ⟨fun A ↦ ?_⟩
    obtain ⟨B, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := E) (G.obj A)
    have _ : IsIso e.hom.left :=
      ⟨e.inv.left, congrArg (fun k ↦ k.left) e.hom_inv_id, congrArg (fun k ↦ k.left) e.inv_hom_id⟩
    have _ : IsFinite (G.obj A).hom := A.prop.1
    have _ : IsFinite (E.obj B).hom := by
      rw [← MorphismProperty.Over.w e.hom]
      infer_instance
    have _ : Etale B.hom := B.prop
    have _ : IsFinite (pullback.snd B.hom f) := ‹IsFinite (E.obj B).hom›
    let B' : FiniteEtaleOver Y := MorphismProperty.Over.mk ⊤ B.hom
      ⟨isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism f B.hom, B.prop⟩
    have eB : G'.obj B' ≅ B := MorphismProperty.Over.isoMk (Iso.refl B.left) (Category.id_comp _)
    exact ⟨B', ⟨hGff.preimageIso (eqToIso (hobj B') ≪≫ E.mapIso eB ≪≫ e)⟩⟩
  exact Functor.IsEquivalence.mk hfaithful hfull hess

/-- **Topological invariance of the étale fundamental group.** Let `f : X ⟶ Y` be a universal
homeomorphism of connected schemes and `x` a geometric point of `X`. Then the induced continuous
homomorphism `AlgebraicGeometry.etaleFundamentalGroupMap f x : π₁(X, x) → π₁(Y, f ∘ x)` is an
isomorphism of topological groups. -/
@[stacks 0BQN "the isomorphism of fundamental groups"]
def fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] [ConnectedSpace X] [ConnectedSpace Y] (x : GeometricPoint X) :
    { e : EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup Y (x.map f) //
      ∀ σ : EtaleFundamentalGroup X x, e σ = etaleFundamentalGroupMap f x σ } :=
  fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange f
    (finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism f) x

/-- For a universal homeomorphism `f : X ⟶ Y` of connected schemes and a geometric point `x` of
`X`, the induced map `π₁(X, x) → π₁(Y, f ∘ x)` of étale fundamental groups is bijective. -/
theorem etaleFundamentalGroupMap_bijective_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] [ConnectedSpace X] [ConnectedSpace Y] (x : GeometricPoint X) :
    Function.Bijective (etaleFundamentalGroupMap f x) := by
  obtain ⟨e, he⟩ := fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism f x
  have : (etaleFundamentalGroupMap f x : EtaleFundamentalGroup X x →
      EtaleFundamentalGroup Y (x.map f)) = e := funext fun σ ↦ (he σ).symm
  rw [this]
  exact e.bijective

/-- **Finite étale covers are invariant under a purely inseparable extension of the base
field.** Let `K/k` be a purely inseparable extension of fields and `g : Y ⟶ Spec k` a scheme
over `k`. Then base change along the projection `Y_K = Y ×_{Spec k} Spec K ⟶ Y` is an
equivalence `FÉt_Y ⥤ FÉt_{Y_K}`: the projection is a base change of the universal
homeomorphism `Spec K ⟶ Spec k`. -/
@[sga "1 IX 6.8" "special case"]
theorem finiteEtaleBaseChange_pullbackFst_specMap_algebraMap_isEquivalence (k K : Type u)
    [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] (g : Y ⟶ Spec (.of k)) :
    (finiteEtaleBaseChange
      (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence :=
  have : UniversalHomeomorphism
      (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(MorphismProperty.universally_isStableUnderBaseChange
        (topologically @IsHomeomorph)).of_isPullback (IsPullback.of_hasPullback g _).flip
      (universalHomeomorphism_specMap_algebraMap k K).universally_isHomeomorph⟩
  finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism _

end AlgebraicGeometry

end
