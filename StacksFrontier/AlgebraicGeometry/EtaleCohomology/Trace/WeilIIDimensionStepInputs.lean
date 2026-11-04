module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The inputs of the induction step of Weil II

The step `S(n) → S(n + 1)` of the induction on the dimension in the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) fibres an open `U`
of a scheme of dimension `n + 1` over `𝔸ⁿ` with fibres of dimension `≤ 1`, and compares the
cohomology of `U` with that of the higher direct images with compact support `Rʳ g_! G` on the
base through the Leray spectral sequence. This file states the results this step consumes, each
as one proposition:

* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageFamily`: an assignment `R g j G r` of an
  ℓ-adic sheaf on `W` to a morphism `g : U ⟶ W` with a compactification `j`, an ℓ-adic sheaf `G`
  on `U` and `r : ℕ` (the role of `Rʳ g_! G`);
* `Stacks.EtaleCohomology.LAdicSheaf.LerayWeightInput`: the weight bounds on the cohomology of
  the `Rʳ g_! G` give the weight bound on the cohomology of `G` (Leray);
* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageStalkInput`: the Frobenius at a closed
  point `w` of `W` on the stalk of `Rʳ g_! G` has the characteristic polynomial of the Frobenius
  of `κ(w)` on `Hʳ_c` of the fibre (proper base change, Tag 0F7L);
* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageLisseLocusInput`: the `Rʳ g_! G` are lisse
  over a nonempty open of the base (Tag 0GL0);
* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageRealizableInput`: for `g` affine and smooth
  of relative dimension one, the `Rʳ g_! G` are `ι`-realizable over a nonempty open of `W`;
* `Stacks.EtaleCohomology.LAdicSheaf.FiniteCompactSupportCohomologyInput`: finiteness of
  compactly supported cohomology in every dimension (Tag 03V3);
* `Stacks.EtaleCohomology.LAdicSheaf.CompactSupportCompactificationIndependenceInput`: the
  Frobenius on `Hⁱ_c` does not depend on the compactification (Tag 0F7I).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageFamily` and the propositions above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open scoped AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **A family of higher direct images with compact support**: to a separated morphism of finite
type `g : U ⟶ W` of noetherian schemes, a compactification `j` of `g`, an ℓ-adic sheaf `G` on `U`
and `r : ℕ`, an ℓ-adic sheaf `R g j G r` on `W`, in the role of `Rʳ g_! G`. The properties of
`Rʳ g_!` used in the induction step of Weil II are stated for such a family. -/
abbrev LAdicSheaf.HigherDirectImageFamily : Type (u + 2) :=
  ∀ {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)],
    CompactificationOf (Over.mk (B.inclusion.map g)) → LAdicSheaf.{u, u + 1} B U ℓ → ℕ →
      LAdicSheaf.{u, u + 1} B W ℓ

variable {B ℓ}

/-- **The Leray weight implication** (Weil II 3.3; Leray spectral sequence of `Rg_!`, Tag 0F7J):
for `g : U ⟶ W` over a finite field `k` with `q = p ^ m` elements and an ℓ-adic sheaf `G` on `U`,
if for every `r` the eigenvalues of the geometric Frobenius on `Hⁱ_c(W_k̄, Rʳ g_! G ⊗ ℚ_ℓ)` have
weights `≤ b + r + i` along `ι`, then for some compactification of `U` the eigenvalues on
`Hⁱ_c(U_k̄, G ⊗ ℚ_ℓ)` have weights `≤ b + i`. -/
def LAdicSheaf.LerayWeightInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (ι : ℚ_[ℓ] →+* ℂ) (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1]
      (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
      [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
      (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
      (G : LAdicSheaf.{u, u + 1} B U ℓ) (b : ℤ),
      (∀ (r : ℕ) (jW : CompactificationOf (Over.mk fW)) (i : ℤ) [FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B W ℓ fW jW kbar
            (R g jg G r) i)],
        IsCharpolyNormMixedOfWeightLE (p ^ q) ι (b + r + i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B W ℓ fW jW kbar p q hcard
            (R g jg G r) i).hom) →
      ∃ jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)), ∀ (i : ℤ)
        [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          (B.inclusion.map g ≫ fW) jU kbar G i)],
        IsCharpolyNormMixedOfWeightLE (p ^ q) ι (b + i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map g ≫ fW)
            jU kbar p q hcard G i).hom

/-- **The stalks of `Rʳ g_! G` at closed points** (proper base change, Tag 0F7L, with the
Frobenius): at a closed point `w` of `W`, of degree over a finite field `k`, the characteristic
polynomial of the geometric Frobenius on `(Rʳ g_! G)_w̄ ⊗ ℚ_ℓ` is that of the geometric Frobenius
of the finite field `κ(w)` on `Hʳ_c` of the fibre `U_w = U ×_W Spec κ(w)` over `κ(w)` with
coefficients in `G|_{U_w} ⊗ ℚ_ℓ`, for one compactification of `U_w` over `κ(w)` serving every
`G` and every `r`. -/
def LAdicSheaf.HigherDirectImageStalkInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1]
    (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
    (w : closedPoints W.1) (hB : B.Contains ((B.inclusion.map g).fiber w.1))
    [IsNoetherian ((B.inclusion.map g).fiber w.1)]
    [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w.1)]
    [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w.1)]
    [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w.1)]
    [Fintype (W.1.residueField w.1)] (kbar : Type u) [Field kbar]
    [Algebra (W.1.residueField w.1) kbar] [IsAlgClosure (W.1.residueField w.1) kbar] (p n : ℕ)
    [Fact p.Prime] [CharP (W.1.residueField w.1) p]
    (hcard : Fintype.card (W.1.residueField w.1) = p ^ n),
    ∃ jw : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w.1)),
      ∀ (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
          (k := W.1.residueField w.1) B (B.obj ((B.inclusion.map g).fiber w.1) hB) ℓ
          ((B.inclusion.map g).fiberToSpecResidueField w.1) jw kbar
          (LAdicSheaf.inverseImage
            (ObjectProperty.homMk ((B.inclusion.map g).fiberι w.1) :
              B.obj ((B.inclusion.map g).fiber w.1) hB ⟶ U) G) r)],
        (LAdicSheaf.rationalStalkFrobenius B W ℓ (R g jg G r) w.1
            (finite_residueField fW w.1 w.2)).charpoly =
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
            (k := W.1.residueField w.1) B (B.obj ((B.inclusion.map g).fiber w.1) hB) ℓ
            ((B.inclusion.map g).fiberToSpecResidueField w.1) jw kbar p n hcard
            (LAdicSheaf.inverseImage
              (ObjectProperty.homMk ((B.inclusion.map g).fiberι w.1) :
                B.obj ((B.inclusion.map g).fiber w.1) hB ⟶ U) G) r).hom.charpoly

/-- **The lisse locus of the `Rʳ g_! G`** (Tag 0GL0 and its ℓ-adic form): for `g : U ⟶ W` with
`W` nonempty and reduced and `G` lisse, there is a nonempty open `V ⊆ W` such that over every open
`V' ⊆ V`, with `g' : U' ⟶ V'` the base change of `g`, every `Rʳ g'_! (G|_{U'})` is lisse. -/
def LAdicSheaf.HigherDirectImageLisseLocusInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) :
    Prop :=
  ∀ (U W : B.Scheme) [IsNoetherian U.1] [IsNoetherian W.1] [IsReduced W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (G : LAdicSheaf.{u, u + 1} B U ℓ), G.IsLisse →
    Nonempty W.1 → ∃ (V : B.Scheme) (jV : V ⟶ W), IsOpenImmersion (B.inclusion.map jV) ∧
      Nonempty V.1 ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] (jV' : V' ⟶ V)
        (jU : U' ⟶ U) (g' : U' ⟶ V') [LocallyOfFiniteType (B.inclusion.map g')]
        [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')]
        (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
        IsOpenImmersion (B.inclusion.map jV') →
        IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
          (B.inclusion.map (jV' ≫ jV)) →
        ∀ r : ℕ, (R g' jg' (LAdicSheaf.inverseImage jU G) r).IsLisse

/-- **Realizability of the `Rʳ g_! G` for families of smooth affine curves** (Weil II 1.5,
Kedlaya §6): let `g : U ⟶ W` be affine and smooth of relative dimension one, over a finite field
`k` with `p ^ n` elements, `ℓ ≠ p`, with `W` reduced and irreducible and `U` nonempty, and let
`G` be lisse, pointwise `ι`-mixed of weights `≤ w` and `ι`-realizable on `U`. There is a nonempty
open `V ⊆ W` such that over every open `V' ⊆ V`, with `g' : U' ⟶ V'` the base change of `g`, every
`Rʳ g'_! (G|_{U'})` is `ι`-realizable (a property of the Frobenius at the closed points of `V'`,
which does not depend on the structure morphism `fV'` of `V'`). -/
def LAdicSheaf.HigherDirectImageRealizableInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) :
    Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (q : ℕ) (ι : ℚ_[ℓ] →+* ℂ) (U W : B.Scheme)
    [IsNoetherian U.1] [IsNoetherian W.1] [IsReduced W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] [SmoothOfRelativeDimension 1 (B.inclusion.map g)]
    [IsAffineHom (B.inclusion.map g)]
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
    (G : LAdicSheaf.{u, u + 1} B U ℓ) (w : ℤ), G.IsLisse →
    LAdicSheaf.IsPointwiseMixedOfWeightLE B U ℓ (B.inclusion.map g ≫ fW) G q ι w →
    LAdicSheaf.IsIotaRealizable B U ℓ (B.inclusion.map g ≫ fW) G ι →
    IrreducibleSpace W.1 → Nonempty U.1 →
    ∃ (V : B.Scheme) (jV : V ⟶ W), IsOpenImmersion (B.inclusion.map jV) ∧
      Nonempty V.1 ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] (jV' : V' ⟶ V)
        (jU : U' ⟶ U) (g' : U' ⟶ V') [LocallyOfFiniteType (B.inclusion.map g')]
        [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')]
        (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
        IsOpenImmersion (B.inclusion.map jV') →
        IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
          (B.inclusion.map (jV' ≫ jV)) →
        ∀ (fV' : V'.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV'] (r : ℕ),
          LAdicSheaf.IsIotaRealizable B V' ℓ fV' (R g' jg' (LAdicSheaf.inverseImage jU G) r) ι

variable (B ℓ)

/-- **Finiteness of compactly supported ℓ-adic cohomology in every dimension** (Tag 03V3): every
scheme separated of finite type over a finite field has finite compactly supported cohomology at
the finite levels and finite dimensional rational compactly supported cohomology. -/
def LAdicSheaf.FiniteCompactSupportCohomologyInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ q →
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f],
      LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar X f

/-- **Independence of the compactification** (Tag 0F7I, with the Frobenius): the characteristic
polynomial of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not depend on the
compactification of `X` used to define it. -/
def LAdicSheaf.CompactSupportCompactificationIndependenceInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
      [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar F i)]
      [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar F i)],
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₁ kbar p q hcard F
        i).hom.charpoly =
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₂ kbar p q hcard F
          i).hom.charpoly

end Stacks.EtaleCohomology
