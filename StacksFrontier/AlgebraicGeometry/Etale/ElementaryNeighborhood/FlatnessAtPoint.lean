module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood

/-!
# Flatness at a point spreads after an elementary étale base change

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type, and let `x : X` be a point at which `F` is flat over `S`. Stacks Tag 05KT produces an
elementary étale neighbourhood `(S', s')` of `(S, f x)` and an open subscheme
`V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the unique point over `x` on which the pullback of `F` is
flat over `Spec 𝒪_{S', s'}`.

This is Stacks Tag 05I5 with the finite presentation hypothesis on `f` weakened to finite type,
at the cost of dropping the finite presentation conclusion on the pullback of `F`.

## Main results

* `AlgebraicGeometry.ElementaryEtaleFlatness.exists_elementaryEtaleNeighborhood_open_flat` is
  **Stacks Tag 05KT**.

## Implementation notes

The statement follows from `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFlatOver`, which
states Tag 05KT with the unique point over `x` recorded as the singleton fibre of
`pullback.fst`.

The local scheme at the distinguished point of the étale neighbourhood is represented by
`Spec (S'.presheaf.stalk s')` with structure map `S'.fromSpecStalk s'`, and the open subscheme by
an open subset of the categorical pullback. The point over `x` and its uniqueness are part of the
produced data.

The affine base change assertion of Stacks Tag 02KG enters as
`AlgebraicGeometry.affinePushforwardBaseChangeIso`, which reads
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` as an
isomorphism.

## References

* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ElementaryEtaleFlatness

open AlgebraicGeometry

universe u

/-- The affine base-change isomorphism `g^* f_* F ≅ f'_* (g')^* F` of Stacks Tag 02KG, under the
name used by the consumers of this file: this is
`AlgebraicGeometry.affinePushforwardBaseChangeIso`. -/
def affineBaseChangeIso {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hw : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  affinePushforwardBaseChangeIso hw F

/-- **Stacks Project, Tag 05KT.** Flatness at a point of a finite type quasi-coherent module
spreads to an open neighbourhood after base change to the local scheme of a suitable
elementary étale neighbourhood of the image point. -/
@[stacks 05KT]
theorem exists_elementaryEtaleNeighborhood_open_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X)
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let g := U.scheme.fromSpecStalk U.point ≫ U.toBase
      let P : Scheme.{u} := pullback f g
      ∃ (z : P) (_ : pullback.fst f g z = x)
      (_ : ∀ z' : P, pullback.fst f g z' = x → z' = z) (V : P.Opens),
      z ∈ V ∧
        AlgebraicGeometry.IsFlatOver
          (((V.ι : V.toScheme ⟶ P) ≫ pullback.snd f g).toLRSHom.toShHom)
          ((Scheme.Modules.pullback
            ((V.ι : V.toScheme ⟶ P) ≫ pullback.fst f g)).obj F) :=
  by
    obtain ⟨U, hU, V, v, hfiber, hflat⟩ :=
      AlgebraicGeometry.existsElementaryEtaleNeighborhoodFlatOver f F x hF
    refine ⟨U, hU, V.ι v, ?_, ?_, V, v.2, hflat⟩
    · have hmem : (V.ι v : ↥(pullback f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase))) ∈
            pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} := by
        rw [hfiber]
        exact Set.mem_singleton _
      exact hmem
    · intro z' hz'
      have hmem : z' ∈
          pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} := hz'
      rw [hfiber] at hmem
      exact hmem


end AlgebraicGeometry.ElementaryEtaleFlatness

end
