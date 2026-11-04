module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Properness of the support gives universal purity

A finite type quasi-coherent module whose support is proper over the base is universally pure
relative to that base; in particular this holds for every such module on a scheme which is itself
proper over the base, and so a proper scheme is universally pure over its base.

All three statements come from one observation. An impurity requires the closure of its chosen
point to miss the fibre over the specialized point; but the specialized point lies in the image
of that closure, and if that image is closed then it also contains the point it specializes to,
which produces a point of the closure in the forbidden fibre. The image is closed in both cases:
for a proper morphism because the base change of the structure morphism is closed, and for a
module with proper support because the closure of the chosen point is contained in the support of
the pulled-back module, which is the base change of a closed subscheme proper over the base.

## Main results

* `AlgebraicGeometry.relativeAssassin_subset_supp`: the relative assassin is contained in the
  support.
* `AlgebraicGeometry.isUniversallyPureAlong_of_moduleIso` and
  `AlgebraicGeometry.isUniversallyPureAlong_iff_of_moduleIso`: universal purity along a fibre only
  depends on the isomorphism class of the module.
* `AlgebraicGeometry.isUniversallyPureRelative_of_support_isProperOver`,
  `AlgebraicGeometry.isUniversallyPureRelative_of_isProper` and
  `AlgebraicGeometry.isSchemeUniversallyPureRelative_of_isProper` are the three parts of the
  source.

## Implementation notes

Properness is Mathlib's `AlgebraicGeometry.IsProper`, which supplies both finiteness conditions
on the morphism: local finite type is one of its parents, and quasi-compactness follows from
universal closedness.

Properness of a closed subset over the base is `AlgebraicGeometry.IsProperOver`, which is
properness of the structure morphism of the reduced induced closed subscheme. Since the argument
below only uses the underlying closed set of that subscheme, no closed subscheme structure
adapted to the module — such as the one cut out by its annihilator — is needed.

## References

* [Stacks Project, Tag 05K3](https://stacks.math.columbia.edu/tag/05K3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The relative assassin of a finite type module is contained in its support: an associated
point of the restriction to a fibre lies in the support of that restriction, which is the inverse
image of the support. -/
theorem relativeAssassin_subset_supp {X S : Scheme.{u}} (g : X ⟶ S) (M : X.Modules)
    [M.IsFiniteType] :
    Stacks.Divisors.relativeAssassin g M ⊆ SheafOfModules.supp M := by
  intro x hx
  rw [Stacks.Divisors.mem_relativeAssassin] at hx
  obtain ⟨t, y, hy, hxy⟩ := hx
  have := associatedPoints_subset_support _ hy
  rw [Stacks.Modules.supp_pullback] at this
  exact hxy ▸ this

/-- An impurity diagram whose chosen point has a closure with closed image in the test scheme is
not an impurity: the image then contains the specialized point of the test scheme, so the closure
of the chosen point meets the fibre over it. -/
private lemma not_isImpurity_of_isClosed_image_closure (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) (h : IsClosed (D.toT.base '' closure {D.xi})) : ¬ IsImpurity P D := by
  rintro ⟨-, hDisjoint⟩
  obtain ⟨y, hyclose, hybase⟩ :=
    D.specializes.mem_closed h ⟨D.xi, subset_closure rfl, D.xi_liesOver⟩
  have hmeet : y ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) := by
    refine ⟨hyclose, ?_⟩
    rw [D.toT.range_fiberι]
    exact hybase
  rwa [hDisjoint] at hmeet

/-- Universal purity along a fibre is unchanged by replacing the module by an isomorphic one. -/
theorem isUniversallyPureAlong_of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F G : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent] (e : F ≅ G) (s : S) :
    IsUniversallyPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) →
      IsUniversallyPureAlong
        ({ S := S, X := X, f := f, F := G, s := s } : PrePureSituation.{u}) := by
  intro h D hD
  refine h { D with } ⟨?_, hD.2⟩
  show D.xi ∈ Stacks.Divisors.relativeAssassin D.toT ((Scheme.Modules.pullback D.toX).obj F)
  rw [relativeAssassin_eq_of_moduleIso D.toT ((Scheme.Modules.pullback D.toX).mapIso e)]
  exact hD.1

/-- Universal purity along a fibre only depends on the isomorphism class of the module. -/
theorem isUniversallyPureAlong_iff_of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F G : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent] (e : F ≅ G) (s : S) :
    IsUniversallyPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) ↔
      IsUniversallyPureAlong
        ({ S := S, X := X, f := f, F := G, s := s } : PrePureSituation.{u}) :=
  ⟨isUniversallyPureAlong_of_moduleIso f F G e s,
    isUniversallyPureAlong_of_moduleIso f G F e.symm s⟩

/-- **Stacks Project, Tag 05K3, part (1).** A finite type quasi-coherent module whose support is
proper over the base is universally pure relative to that base. -/
@[stacks 05K3 "part (1)"]
theorem isUniversallyPureRelative_of_support_isProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hF : IsProperOver f (⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ : Closeds X)) :
    IsUniversallyPureRelative f F := by
  intro s D hImp
  have hFT : (D.pulledBack _).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType D.toX.toLRSHom.toShHom F
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ : Closeds X)
  have hProper : IsProper (J.subschemeι ≫ f) := hF
  let w : pullback J.subschemeι D.toX ⟶ D.X_T := pullback.snd J.subschemeι D.toX
  have hrange : Set.range w = D.toX ⁻¹' SheafOfModules.supp F := by
    rw [Scheme.Pullback.range_snd, J.range_subschemeι]
    exact congrArg _ (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have : UniversallyClosed (w ≫ D.toT) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback J.subschemeι D.toX).paste_vert D.isPullback) inferInstance
  have hsub : closure ({D.xi} : Set D.X_T) ⊆ Set.range w := by
    rw [hrange]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_)
      ((SheafOfModules.isClosed_supp F).preimage D.toX.continuous)
    rw [← Stacks.Modules.supp_pullback D.toX F]
    exact relativeAssassin_subset_supp D.toT _ hImp.1
  have himg : (w ≫ D.toT).base '' (w.base ⁻¹' closure ({D.xi} : Set D.X_T)) =
      D.toT.base '' closure ({D.xi} : Set D.X_T) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro t ⟨z, hz, rfl⟩
      exact ⟨w.base z, hz, rfl⟩
    · rintro t ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := hsub hx
      exact ⟨z, hx, rfl⟩
  exact not_isImpurity_of_isClosed_image_closure _ D
    (himg ▸ (w ≫ D.toT).isClosedMap _ (isClosed_closure.preimage w.continuous)) hImp

/-- **Stacks Project, Tag 05K3, part (2).** A finite type quasi-coherent module on a scheme which
is proper over the base is universally pure relative to that base. -/
@[stacks 05K3 "part (2)"]
theorem isUniversallyPureRelative_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    IsUniversallyPureRelative f F := by
  intro s D
  refine not_isImpurity_of_isClosed_image_closure _ D ?_
  have : UniversallyClosed D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  exact D.toT.isClosedMap _ isClosed_closure

/-- **Stacks Project, Tag 05K3, part (3).** A proper scheme is universally pure over its base. -/
@[stacks 05K3 "part (3)"]
theorem isSchemeUniversallyPureRelative_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    @IsUniversallyPureRelative.{u} X S f _ _ (SheafOfModules.unit.{u} X.ringCatSheaf)
      (structureSheaf_isFiniteType X)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X) :=
  have : (SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType := structureSheaf_isFiniteType X
  isUniversallyPureRelative_of_isProper f (SheafOfModules.unit.{u} X.ringCatSheaf)

end AlgebraicGeometry

end
