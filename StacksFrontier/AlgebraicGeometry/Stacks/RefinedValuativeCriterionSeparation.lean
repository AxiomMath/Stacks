module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated

/-!
# The refined valuative criterion of separation for algebraic stacks (Stacks 0E95)

Stacks 0E95 deduces separatedness of a quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` locally of finite
type over a locally Noetherian `𝒴` from the uniqueness part of the valuative criterion, tested
only on valuative diagrams over discrete valuation rings whose generic point factors through a
1-morphism of finite type `h : 𝒰 ⟶ 𝒳` with dense image.

This file proves Stacks 0E95 assuming the statement of Stacks 0CQM.

## Main results

* `ValuativeCriterion.DiscreteUniquenessAlong.discreteExistenceAlong_relativeDiagonal`: uniqueness
  along `h` for `f` gives existence along `h` for `Δ_f`, over the given valuation ring (Stacks
  0E8L).
* `ValuativeCriterion.DiscreteUniquenessAlong.relativeDiagonal`: uniqueness along `h` for `f` gives
  uniqueness along `h` for `Δ_f` (Stacks 0E8L).
* `AlgebraicStacks.isSeparated_of_discreteUniquenessAlong_of_isSeparated_relativeDiagonal`: Stacks
  0E95 when `Δ_f` is separated.
* `AlgebraicStacks.isSeparated_of_denseRange_of_discreteUniquenessAlong`: Stacks 0E95 from the
  statement of Stacks 0CQM.

## References

* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

namespace ValuativeCriterion

/-- The valuative diagram for `f` underlying one for `Δ_f`, with special point the first
projection of `y` followed by `f`. -/
private abbrev diagonalBaseDiagram {f : 𝒳 ⟶ 𝒴}
    (D : ValuativeDiagram B S hS 𝒳 (AlgebraicStacks.twoFibreProduct B S hS f f)
      (AlgebraicStacks.relativeDiagonal B S hS f)) : ValuativeDiagram B S hS 𝒳 𝒴 f :=
  { D with
    y := (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom
    γ := diagonalWitness B S hS D }

/-- **Uniqueness along `h` for `f` gives existence along `h` for the relative diagonal**, with no
extension of the valuation ring at all. -/
theorem DiscreteUniquenessAlong.discreteExistenceAlong_relativeDiagonal {h : 𝒰 ⟶ 𝒳}
    {f : 𝒳 ⟶ 𝒴} (hf : DiscreteUniquenessAlong B S hS h f) :
    DiscreteExistenceAlong B S hS h (AlgebraicStacks.relativeDiagonal B S hS f) := by
  intro q hq u hu
  have hfrac : (algebraMap q.R q.K).comp (RingHom.id q.R)
      = (RingHom.id q.K).comp (algebraMap q.R q.K) := by
    rw [RingHom.comp_id, RingHom.id_comp]
  let e := dominatingExtensionOfRingMaps B q q.R q.K (RingHom.id q.R) (RingHom.id q.K)
    (isLocalHom_id q.R) hfrac q.ring_mem q.field_mem
  refine ⟨e, ?_⟩
  let D := ValuativeSquare.toValuativeDiagram B S hS
    (ValuativeSquare.ofDominatingExtension B S hS q e)
  obtain ⟨m⟩ := (hf (diagonalBaseDiagram B S hS D) hq (e.k ≫ u) (by
        show e.k ≫ q.x = _
        rw [hu]
        rfl)).2
    (diagonalDottedArrowFst B S hS D) (diagonalDottedArrowSnd B S hS D)
  obtain ⟨d, _⟩ := Quotient.exists_rep ((diagonalDottedArrowClassesEquiv B S hS D).symm m.hom)
  exact ⟨d⟩

/-- **Uniqueness along `h` for `f` gives uniqueness along `h` for the relative diagonal.** -/
theorem DiscreteUniquenessAlong.relativeDiagonal {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hf : DiscreteUniquenessAlong B S hS h f) :
    DiscreteUniquenessAlong B S hS h (AlgebraicStacks.relativeDiagonal B S hS f) := by
  intro D hD u hu
  refine ⟨isSetoidCategory_dottedArrow_relativeDiagonal B S hS D, fun a b => ?_⟩
  obtain ⟨hiso, hendo⟩ := (hf (diagonalBaseDiagram B S hS D) hD u hu).1
  have hsub : ∀ m₁ m₂ : diagonalDottedArrowFst B S hS D ⟶ diagonalDottedArrowSnd B S hS D,
      m₁ = m₂ := fun m₁ m₂ => by
    have := hiso m₂
    have := hendo _ (m₁ ≫ inv m₂)
    exact ((IsIso.comp_inv_eq m₂).1 this).trans (Category.id_comp m₂)
  exact Quotient.exact ((diagonalDottedArrowClassesEquiv B S hS D).injective (hsub _ _))

end ValuativeCriterion

namespace AlgebraicStacks

/-- **The relative diagonal of a 1-morphism locally of finite type is locally of finite
type.** -/
theorem isLocallyOfFiniteType_relativeDiagonal_of_isLocallyOfFiniteType (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (relativeDiagonal B S hS f) :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf)

/-- **The 2-fibre product `𝒳 ×_𝒴 𝒳` of a 1-morphism locally of finite type over a locally
Noetherian algebraic stack is locally Noetherian.** -/
theorem isLocallyNoetherian_twoFibreProduct (f : 𝒳 ⟶ 𝒴) (hf : IsLocallyOfFiniteType B S hS f)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴) :
    HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (twoFibreProduct B S hS f f) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS ((twoFibreProductSquare B S hS f f).fst ≫ f)
    (isLocallyOfFiniteType_comp B S hS _ f
      (isLocallyOfFiniteType_baseChange B S hS f f (twoFibreProductSquare B S hS f f)
        (isTwoFibreProduct_twoFibreProductSquare B S hS f f) hf) hf) h𝒴

/-- **Stacks 0E95 when the relative diagonal is separated.** Let
`f : 𝒳 ⟶ 𝒴` be locally of finite type over a locally Noetherian `𝒴`, with quasi-compact relative
diagonal, and let `h : 𝒰 ⟶ 𝒳` be of finite type with dense image. If `Δ_f` is separated and `f`
satisfies the discrete uniqueness part of the valuative criterion along `h`, then `f` is separated.
`h0CQM` is the statement of Stacks 0CQM. -/
theorem isSeparated_of_discreteUniquenessAlong_of_isSeparated_relativeDiagonal
    (h0CQM : ∀ (𝒰' 𝒳' 𝒴' : AlgebraicStacks.{u, w} B S hS) (h' : 𝒰' ⟶ 𝒳') (f' : 𝒳' ⟶ 𝒴'),
      HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴' →
      IsFiniteType B S hS f' → IsFiniteType B S hS h' → IsSeparated B S hS f' →
      @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS h')) →
      ValuativeCriterion.DiscreteExistenceAlong B S hS h' f' → IsProper B S hS f')
    (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hqc : Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hΔ : IsSeparated B S hS (relativeDiagonal B S hS f))
    (huniq : ValuativeCriterion.DiscreteUniquenessAlong B S hS h f) :
    IsSeparated B S hS f := by
  have hrep := Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hP := h0CQM 𝒰 𝒳 (twoFibreProduct B S hS f f) h (relativeDiagonal B S hS f)
    (isLocallyNoetherian_twoFibreProduct B S hS f hf h𝒴)
    ⟨isLocallyOfFiniteType_relativeDiagonal_of_isLocallyOfFiniteType B S hS f hf,
      (isQuasiCompact_iff_baseChange_quasiCompact B S hS (relativeDiagonal B S hS f) hrep).1 hqc⟩
    hh hΔ hdense
    (ValuativeCriterion.DiscreteUniquenessAlong.discreteExistenceAlong_relativeDiagonal B S hS
      huniq)
  exact (isProper_iff_isProper_hom B S hS (relativeDiagonal B S hS f) hrep).1 hP

/-- **Stacks 0E95, from the statement of Stacks 0CQM.** Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` be
1-morphisms of algebraic stacks over `S`, with `𝒴` locally Noetherian, `f` locally of finite type
and quasi-separated, `h` of finite type, and the image of `|h|` dense in `|𝒳|`. If for every
valuative diagram for `f` over a discrete valuation ring whose generic point factors through `h`
the category of dotted arrows is empty or a setoid with exactly one isomorphism class, then `f` is
separated. `h0CQM` is the statement of Stacks 0CQM. -/
theorem isSeparated_of_denseRange_of_discreteUniquenessAlong
    (h0CQM : ∀ (𝒰' 𝒳' 𝒴' : AlgebraicStacks.{u, w} B S hS) (h' : 𝒰' ⟶ 𝒳') (f' : 𝒳' ⟶ 𝒴'),
      HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴' →
      IsFiniteType B S hS f' → IsFiniteType B S hS h' → IsSeparated B S hS f' →
      @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS h')) →
      ValuativeCriterion.DiscreteExistenceAlong B S hS h' f' → IsProper B S hS f')
    (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (huniq : ValuativeCriterion.DiscreteUniquenessAlong B S hS h f) :
    IsSeparated B S hS f := by
  set δ := relativeDiagonal B S hS f
  have hrep : IsRepresentableByAlgebraicSpaces B S hS δ.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hrep₂ : IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonal B S hS δ).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS δ
  have hqc₂ : Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val (twoFibreProduct B S hS f f).val
        δ.hom) :=
    (Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS δ hrep).2 hqs.2
  have hqsΔ : IsQuasiSeparated B S hS δ :=
    (isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS δ hrep).2 hqc₂
  have hsep₂ : IsSeparated B S hS (relativeDiagonal B S hS δ) :=
    ((Stack.isSeparated_relativeDiagonal_tfae B S hS (relativeDiagonal B S hS δ) hrep₂).out 3 1).2
      (Stack.isSeparated_relativeDiagonal_of_isSetoidCategory_dottedArrow B S hS δ hqsΔ.2
        fun D => isSetoidCategory_dottedArrow_relativeDiagonal B S hS D)
  have hsepΔ : IsSeparated B S hS δ :=
    isSeparated_of_discreteUniquenessAlong_of_isSeparated_relativeDiagonal B S hS h0CQM h δ
      (isLocallyNoetherian_twoFibreProduct B S hS f hf h𝒴)
      (isLocallyOfFiniteType_relativeDiagonal_of_isLocallyOfFiniteType B S hS f hf) hqc₂ hh
      hdense hsep₂ (ValuativeCriterion.DiscreteUniquenessAlong.relativeDiagonal B S hS huniq)
  exact isSeparated_of_discreteUniquenessAlong_of_isSeparated_relativeDiagonal B S hS h0CQM h f
    h𝒴 hf hqs.1 hh hdense hsepΔ huniq

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
