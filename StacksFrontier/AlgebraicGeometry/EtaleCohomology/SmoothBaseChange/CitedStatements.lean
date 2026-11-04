module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover

/-!
# The cited statements of the smooth base change theorem

The second proof of the smooth base change theorem (Stacks, Theorem 0EYU) cites results that are
not theorems of this library. The theorems built on the proof take each of them as one named
argument, and the propositions below are those arguments.
Each one is the statement of the cited result as the source gives it, or the parts of it that
the proof uses.

* `FlatReducedFibresBaseChange` — **Stacks 0EYS**.
* `EtaleLocalHigherBaseChange` — **Stacks 0EZR**, part (3).
* `HigherBaseChangePaste` — **Stacks 0EZS**, the statement for abelian sheaves.
* `FirstFailureNormalization` — **Stacks 0F08**.
* `AffineCurveCohomologyVanishing` and `CurveCohomologyAlgClosedInvariance` — **Stacks 03SC**,
  parts (2) and (6).
* `GaloisCoversExtendFromGenericFiber` — **Stacks 0EZJ**, discharged by
  `AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber`.

## Implementation notes

The source's second proof cites Lemma 0A5E for the identification
`H^1(X_L, ℤ/dℤ) = H^1(X_K, ℤ/dℤ)` of a smooth affine curve over an algebraically closed field `L`
with its base change to an algebraically closed extension `K`. Lemma 0A5E needs a proper curve,
and the curve here is affine. The identification is part (6) of Theorem 03SC, because
`ℤ/dℤ` is torsion prime to the characteristic, and that is what is used.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **The statement of Stacks 0EYS.** In a cartesian square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
whose left vertical morphism `f` is flat, locally of finite presentation and has geometrically
reduced fibres, the base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism for every sheaf of
sets `F` on the small étale site of `T`, that is, the base change transformation of sheaves of
sets is a natural isomorphism. The sheaves take values in `Type (max (u + 1) v)`. -/
def FlatReducedFibresBaseChangeAt.{v} : Prop :=
  ∀ ⦃X S Y T : Scheme.{u}⦄ (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f],
    IsIso (smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm)

/-- **The statement of Stacks 0EYS** for sheaves of sets in `Type (u + 1)`, the form the proof of
the smooth base change theorem uses: `FlatReducedFibresBaseChangeAt` at `v = 0`. -/
def FlatReducedFibresBaseChange : Prop :=
  FlatReducedFibresBaseChangeAt.{u, 0}

/-- **The statement of Stacks 0EZR, part (3).** In a cartesian square of schemes with an étale
covering `{Uᵢ → X}` such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and with
the induced cartesian squares `Uᵢ ← Uᵢ ×_X Y`, `Vᵢ ← Vᵢ ×_S T` (the data
`Stacks.EtaleCohomology.EtaleLocalBaseChangeData`, whose sheaf is the abelian sheaf `F`): if for
every `i` the base change map `fᵢ⁻¹ R^q g_{i,*} F|ᵢ ⟶ R^q h_{i,*} eᵢ⁻¹ F|ᵢ` is an isomorphism,
then so is `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`. -/
def EtaleLocalHigherBaseChange : Prop :=
  ∀ (D : EtaleLocalBaseChangeData.{u, u} Ab.{u + 1}) (q : ℕ),
    (∀ i : D.I, IsIso ((higherBaseChangeMapAb (D.f_i i) (D.g_i i) (D.h_i i) (D.e_i i)
        (D.local_cartesian i).w q).app ((smallEtalePullbackAb (D.toT_i i)).obj D.F))) →
      IsIso ((higherBaseChangeMapAb D.f D.g D.h D.e D.cartesian.w q).app D.F)

/-- **The statement of Stacks 0EZS for abelian sheaves.** For a tower of two commutative squares
```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```
an abelian sheaf `F` on the small étale site of `X₀` and a degree `q`, if the base change maps
`u₁⁻¹ R^q g₀_* F ⟶ R^q g₁_* v₁⁻¹ F` and `u₂⁻¹ R^q g₁_* v₁⁻¹F ⟶ R^q g₂_* v₂⁻¹ v₁⁻¹ F` are
isomorphisms, then so is the base change map of the outer rectangle. The source states it for a
tower of cartesian squares; it holds for commutative ones. -/
def HigherBaseChangePaste : Prop :=
  ∀ ⦃X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}⦄ (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
    (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}),
    IsIso ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F) →
    IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F)) →
    IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F)

/-- **The statement of Stacks 0F08.** For a morphism of schemes `f : X ⟶ S` and an integer `n`,
if `BC(f, n, q)` holds and `BC(f, n, q + 1)` does not, then there are a diagram of two cartesian
squares over an affine integral normal `S'` with algebraically closed function field, an
algebraically closed field `K` with `Spec K ⟶ S'` dominant, and a divisor `d` of `n` such that
`R^{q+1} h_*(ℤ/dℤ)` is nonzero (`Stacks.EtaleCohomology.FirstFailureDiagram.NormalFailureDiagram`).
The source's `q ≥ 1` with `BC(f, n, q - 1)` is written here as `q + 1` with `BC(f, n, q)`. -/
def FirstFailureNormalization : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) (n : ℤ) (q : ℕ),
    BaseChangeHolds f n (q : ℤ) → ¬ BaseChangeHolds f n ((q : ℤ) + 1) →
      FirstFailureDiagram.NormalFailureDiagram f n (q + 1)

/-- **The statement of Stacks 03SC, part (2).** If `k` is an algebraically closed field, `X` is a
separated scheme of finite type over `k` of dimension at most one, and `F` is a torsion abelian
sheaf on `X_étale`, then `H^q_ét(X, F) = 0` for `q > 1` if `X` is affine. -/
def AffineCurveCohomologyVanishing : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π],
    topologicalKrullDim X ≤ 1 → IsAffine X →
    ∀ [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
      (F : Sheaf X.smallEtaleTopology Ab.{u + 1}),
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
        ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{u + 1} F q)

/-- **The statement of Stacks 03SC, part (6).** If `k` is an algebraically closed field, `X` is a
separated scheme of finite type over `k` of dimension at most one, and `F` is an abelian sheaf on
`X_étale` which is torsion prime to the characteristic of `k`, then for every extension `k'/k` of
algebraically closed fields the restriction `H^q_ét(X, F) ⟶ H^q_ét(X_{k'}, F|_{X_{k'}})` is an
isomorphism.

Torsion prime to the characteristic is asked of the sections: each is annihilated by a positive
integer prime to the characteristic of `k`. -/
def CurveCohomologyAlgClosedInvariance : Prop :=
  ∀ (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    ⦃X : Scheme.{u}⦄ (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π], topologicalKrullDim X ≤ 1 →
    ∀ [HasExt.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
      [HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology
        (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) Ab.{u + 1})]
      (F : Sheaf X.smallEtaleTopology Ab.{u + 1}),
      (∀ (U : X.Etale) (a : F.obj.obj (Opposite.op U)), ∃ n : ℕ, 0 < n ∧
          (ringChar k = 0 ∨ n.Coprime (ringChar k)) ∧ n • a = 0) →
        ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q)

/-- **The statement of Stacks 0EZJ**, as `AlgebraicGeometry.FiniteEtaleGaloisCover` phrases
Galois covers. Let `S` be a quasi-compact and quasi-separated integral normal scheme with generic
point `η`, let `f : X ⟶ S` be a quasi-compact and quasi-separated smooth morphism with
geometrically connected fibres and `σ` a section of `f`. Let `Z ⟶ X_η` be a finite étale Galois
cover with group `G` of order invertible on `S` such that `Z` has a `κ(η)`-rational point mapping
to `σ(η)`. Then there is a finite étale Galois cover `Y ⟶ X` with group `G` whose restriction to
`X_η` is `Z`. -/
def GaloisCoversExtendFromGenericFiber : Prop :=
  ∀ ⦃S X : Scheme.{u}⦄ (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type u) [Group G] [Finite G]
    (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).hom ≫
        e.hom = e.hom ≫ (Z.action g).hom

end Stacks.EtaleCohomology.SmoothBaseChange

end
