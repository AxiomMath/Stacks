module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectHomotopyGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalNullHomotopyOverSlices
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local lifting through a cohomological isomorphism

Let `X` be a ringed space, let `α : ℰ ⟶ ℱ` be a morphism of complexes of `𝒪_X`-modules with `ℰ`
strictly perfect and `ℰ^j = 0` for `j < a`, and let `f : 𝒢 ⟶ ℱ` be a morphism which is an
isomorphism on cohomology in every degree above `a` and an epimorphism on cohomology in degree
`a`. Then every point of `X` has an open neighbourhood over which `α` factors through `f` up to
homotopy (Stacks 08C8).

## Main results

* `AlgebraicGeometry.RingedSpace.isZero_homology_mappingCone` says that the mapping cone of `f`
  has vanishing cohomology in every degree at least `a`.
* `AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy` is Stacks 08C8.

## Implementation notes

The source proof is the one in the Stacks Project: the mapping cone `C(f)` has vanishing
cohomology in degrees at least `a`, so Stacks 08C7 applies to the composite
`α ≫ inr f : ℰ ⟶ C(f)` and makes it null-homotopic over an open neighbourhood `U` of the given
point; the distinguished triangle `𝒢 ⟶ ℱ ⟶ C(f)` over `U` then produces the lift `β` in the
homotopy category, and a representative of it in the category of complexes satisfies the
conclusion up to homotopy.

The vanishing of the cohomology of `C(f)` is read off from the long exact cohomology sequence of
the distinguished triangle `triangleh f` in the homotopy category, for which the shifted homology
functor is homological: the `i`-th term vanishes exactly when `H^i(f)` is epi and `H^{i+1}(f)` is
mono, which is what the hypotheses on `f` give in degrees at least `a`. The passage between
`HomotopyCategory.homologyFunctor` and `HomologicalComplex.homologyFunctor` is
`HomotopyCategory.homologyFunctorFactors`.

Restriction to an open subset is taken in the slice idiom, `SheafOfModules.overFunctor`, which is
the idiom of Stacks 08C6 and 08C7
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StrictlyPerfectHomotopyGlobal.lean`); no bridge to
`AlgebraicGeometry.RingedSpace.restrictModules` is needed here, since the only input from below
is Stacks 08C7 and the only output is consumed by Stacks 08C9 in the same idiom.

Universes: the statement is at `AlgebraicGeometry.RingedSpace.{u, u}` with `𝒪_X`-modules in
universe `u`, which is the generality in which `StrictlyPerfect.OXMod` and
`StrictlyPerfect.IsStrictlyPerfect` are defined; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`.

## References

* [The Stacks Project, Lemma 20.46.6 (08C8)](https://stacks.math.columbia.edu/tag/08C8)
* [The Stacks Project, Lemma 20.46.5 (08C7)](https://stacks.math.columbia.edu/tag/08C7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect

open SheafOfModules (overFunctor)

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- The mapping cone of a morphism `f : 𝒢 ⟶ ℱ` of complexes of `𝒪_X`-modules which is an
isomorphism on cohomology in every degree above `a` and an epimorphism on cohomology in degree
`a` has vanishing cohomology in every degree at least `a`.

The `i`-th term of the long exact cohomology sequence of the distinguished triangle
`𝒢 ⟶ ℱ ⟶ C(f)` vanishes exactly when `H^i(f)` is an epimorphism and `H^{i+1}(f)` is a
monomorphism, and for `i ≥ a` both hold: the first by hypothesis when `i = a` and because
`H^i(f)` is then an isomorphism when `i > a`, the second because `i + 1 > a`. -/
public theorem isZero_homology_mappingCone
    {F G : CochainComplex (OXMod.{u, u} X) ℤ} (f : G ⟶ F) (a : ℤ)
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ i : ℤ, a ≤ i → IsZero ((CochainComplex.mappingCone f).homology i) := by
  intro i hi
  set H := HomotopyCategory.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) 0 with hH
  set T := CochainComplex.mappingCone.triangleh f with hT'
  have hT : T ∈ distTriang (HomotopyCategory (OXMod.{u, u} X) (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished f
  -- Conjugating by isomorphisms preserves being an epimorphism, resp. a monomorphism. The
  -- isomorphisms are taken as `Iso`s so that `Iso.isIso_hom` and `Iso.isIso_inv` supply the
  -- instances at the use site.
  have hconjEpi : ∀ {A A' B' B : OXMod.{u, u} X} (eu : A ≅ A') (g : A' ⟶ B') (ev : B ≅ B'),
      Epi g → Epi (eu.hom ≫ g ≫ ev.inv) := by
    intro A A' B' B eu g ev hg
    have := hg
    infer_instance
  have hconjMono : ∀ {A A' B' B : OXMod.{u, u} X} (eu : A ≅ A') (g : A' ⟶ B') (ev : B ≅ B'),
      Mono g → Mono (eu.hom ≫ g ≫ ev.inv) := by
    intro A A' B' B eu g ev hg
    have := hg
    infer_instance
  -- The shifted homology functor applied to `T.mor₁ = Q.map f` is, up to the canonical
  -- isomorphism `HomotopyCategory.homologyFunctorFactors`, the map `H^n(f)`.
  have hmap (n : ℤ) :
      (H.shift n).map T.mor₁ =
        ((HomotopyCategory.homologyFunctorFactors (OXMod.{u, u} X)
            (ComplexShape.up ℤ) n).app G).hom ≫ HomologicalComplex.homologyMap f n ≫
          ((HomotopyCategory.homologyFunctorFactors (OXMod.{u, u} X)
            (ComplexShape.up ℤ) n).app F).inv := by
    change (HomotopyCategory.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) n).map
      ((HomotopyCategory.quotient (OXMod.{u, u} X) (ComplexShape.up ℤ)).map f) = _
    simp only [Functor.comp_obj, Iso.app_hom, Iso.app_inv]
    exact (NatIso.naturality_2
      (HomotopyCategory.homologyFunctorFactors (OXMod.{u, u} X) (ComplexShape.up ℤ) n) f).symm
  have hepi : Epi ((H.shift i).map T.mor₁) := by
    have : Epi (HomologicalComplex.homologyMap f i) := by
      rcases lt_or_eq_of_le hi with h | h
      · have := hf_gt i h
        infer_instance
      · subst i; exact hf_a
    rw [hmap i]
    exact hconjEpi _ _ _ this
  have hmono : Mono ((H.shift (i + 1)).map T.mor₁) := by
    have := hf_gt (i + 1) (by omega)
    rw [hmap (i + 1)]
    exact hconjMono _ _ _ (IsIso.mono_of_iso (HomologicalComplex.homologyMap f (i + 1)))
  have hz : IsZero ((H.shift i).obj T.obj₃) :=
    (H.homologySequence_exact₃ T hT i (i + 1) rfl).isZero_X₂_iff.mpr
      ⟨(H.homologySequence_epi_shift_map_mor₁_iff T hT i).1 hepi,
        (H.homologySequence_mono_shift_map_mor₁_iff T hT i (i + 1) rfl).1 hmono⟩
  have hz' : IsZero ((HomotopyCategory.homologyFunctor (OXMod.{u, u} X) (ComplexShape.up ℤ) i).obj
      ((HomotopyCategory.quotient (OXMod.{u, u} X)
        (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone f))) := hz
  simpa only [HomologicalComplex.homology, HomologicalComplex.homologyFunctor_obj] using
    ((HomotopyCategory.homologyFunctorFactors (OXMod.{u, u} X) (ComplexShape.up ℤ) i).app
      (CochainComplex.mappingCone f)).isZero_iff.mp hz'

/-- **Stacks 08C8.** Let `X` be a ringed space, let `α : ℰ ⟶ ℱ` be a morphism of complexes of
`𝒪_X`-modules with `ℰ` strictly perfect and `ℰ^j = 0` for `j < a`, and let `f : 𝒢 ⟶ ℱ` be a
morphism of complexes of `𝒪_X`-modules which is an isomorphism on cohomology in every degree
above `a` and an epimorphism on cohomology in degree `a`. Then every point of `X` has an open
neighbourhood `U` carrying a morphism `β : ℰ|_U ⟶ 𝒢|_U` with `β ≫ f|_U` homotopic to `α|_U`.

The mapping cone `C(f)` has vanishing cohomology in degrees at least `a`
(`AlgebraicGeometry.RingedSpace.isZero_homology_mappingCone`), so Stacks 08C7 makes the
composite `α ≫ inr f` null-homotopic over some open neighbourhood `U` of the given point. Hence
`α|_U` composed with the second map of the distinguished triangle `𝒢|_U ⟶ ℱ|_U ⟶ C(f|_U)` is
zero in the homotopy category over `U`, and `Triangle.coyoneda_exact₂` factors it through
`f|_U`; any representative `β` of that factorization satisfies the conclusion. -/
@[stacks 08C8, sga "6 I 4.2" "ringed space case"]
public theorem exists_local_lift_homotopy
    {E F G : CochainComplex (OXMod.{u, u} X) ℤ} (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect E) (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ⟶
          ((overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G,
        Nonempty (Homotopy
          (β ≫ ((overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)
          (((overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)) := by
  intro x
  obtain ⟨U, hx, hzero⟩ := exists_local_homotopy_zero_of_isZero_homology
    (α ≫ CochainComplex.mappingCone.inr f) a hE hEa
    (isZero_homology_mappingCone f a hf_gt hf_a) x
  set R := overFunctor (structureSheafOfRings X) U with hR
  set RHC := R.mapHomologicalComplex (ComplexShape.up ℤ) with hRHC
  set Q := HomotopyCategory.quotient (SheafOfModules.{u} ((structureSheafOfRings X).over U))
    (ComplexShape.up ℤ) with hQ
  -- The cone of `f|_U` is the restriction of the cone of `f`, so the composite of `α|_U` with
  -- the second map of the distinguished triangle over `U` vanishes in the homotopy category.
  have hcomp : Q.map (RHC.map α) ≫ Q.map (CochainComplex.mappingCone.inr (RHC.map f)) = 0 := by
    have hnull : Q.map (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) = 0 := by
      rw [← Functor.map_comp]
      exact (HomotopyCategory.quotient_map_eq_zero_iff _).2 hzero
    have hchain : RHC.map α ≫ CochainComplex.mappingCone.inr (RHC.map f) =
        (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso f R).hom := by
      rw [Category.assoc, CochainComplex.mappingCone.map_inr]
    rw [← Functor.map_comp, hchain, Functor.map_comp, hnull, zero_comp]
  obtain ⟨βq, hβq⟩ := Triangle.coyoneda_exact₂ _
    (HomotopyCategory.mappingCone_triangleh_distinguished (RHC.map f)) (Q.map (RHC.map α)) hcomp
  obtain ⟨β, hβ⟩ := Q.map_surjective βq
  change RHC.obj E ⟶ RHC.obj G at β
  have hβmap : Q.map β ≫ Q.map (RHC.map f) = Q.map (RHC.map α) :=
    (congrArg (· ≫ Q.map (RHC.map f)) hβ).trans hβq.symm
  have hdiff : Q.map (β ≫ RHC.map f - RHC.map α) = 0 := by
    rw [Functor.map_sub, Functor.map_comp]
    exact sub_eq_zero.mpr hβmap
  obtain ⟨h⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1 hdiff
  exact ⟨U, hx, β, ⟨Homotopy.equivSubZero.symm h⟩⟩

end AlgebraicGeometry.RingedSpace

end
