module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.UniformDegreeBound
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsoOverBase
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality

/-!
# The isomorphisms of two polarized families over an affine base are corepresentable

Let `a = (X_a ⟶ V, ℒ_a)` and `b = (X_b ⟶ V, ℒ_b)` be polarized families over a common affine base
`V` of the big fppf site. For a pair of polarized families `x`, `y` over a common affine test base
`T`, with morphisms `x ⟶ a`, `y ⟶ b` over the same `T ⟶ V`, the isomorphisms `x ≅ y` over the
identity of `T` are in natural bijection with the ring homomorphisms `H ⟶ Γ(T, 𝒪_T)` over
`Γ(V, 𝒪_V)`, for a single ring `H` of cardinality at most `max ℵ₀ #Γ(V, 𝒪_V)`
(`AlgebraicGeometry.PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection`).
This is the affine core of the representability of the diagonal of `𝒫olarized`
([Stacks, Tag 0D42]).

The ring `H` is the Isom algebra (`Stacks.GradedIsomScheme.isomAlgebra`) of the global sections
data of the truncated section algebras `𝒪_V ⊕ ⨁_{d ≥ d₀} (f_b)_* ℒ_b^{⊗ d}` and
`𝒪_V ⊕ ⨁_{d ≥ d₀} (f_a)_* ℒ_a^{⊗ d}`, at a cut `d₀` at which [Stacks, Tag 0D4F] applies to both
families (`AlgebraicGeometry.PolarizedFamily.IsomCorepresentationSetup`): the pieces of degree
`≥ d₀` are then finite locally free, hence their global sections finite projective over the
affine base, and their formation commutes with base change. The bijection on a test datum is the
composite of

1. isomorphisms over the identity of `T` as polarized isomorphisms over `T`
   (`AlgebraicGeometry.PolarizedFamily.isoOverBaseEquiv`);
2. polarized isomorphisms over the affine `T` as isomorphisms of the global sections data of the
   truncated section algebras of `x` and `y`, which is the hypothesis
   `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`;
3. conjugation by the base change isomorphisms of the global sections data along `T ⟶ V`
   (`Stacks.AlgebraicGeometry.SectionRingBaseChange.baseChangeDatumIso`);
4. the corepresentation `Stacks.GradedIsomScheme.isomEquiv` of isomorphisms of base changes.

Naturality in the test datum is the cocycle property of pulling back sections along pasted squares
(`Stacks.AlgebraicGeometry.SectionRingBaseChange.globalSectionPull_comp`) together with the
naturality of `isomEquiv` in the algebra
(`Stacks.GradedIsomScheme.isomEquiv_comp_hom_app_one_tmul`).

## Main definitions

* `Stacks.GradedIsomScheme.GradedMulDatum.Iso.symm`, `Iso.trans`, `Iso.congr`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.globalSectionPull`: pulling global sections of
  the truncated section algebras back along a commutative square.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.baseChangeDatumIso`: over affine bases, the
  global sections data commute with base change.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection.isoEquiv`: the
  bijection supplied by the hypothesis.
* `AlgebraicGeometry.PolarizedFamily.isoOverBaseEquiv`.
* `AlgebraicGeometry.PolarizedFamily.IsomCorepresentationSetup`: a common cut for `a` and `b`;
  `IsomCorepresentationSetup.isomRing`, the corepresenting ring, and
  `IsomCorepresentationSetup.isoEquiv`, the bijection on one test datum.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.finite_projective_globalDatum_piece`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.baseChangeDatumHom_restrict`.
* `AlgebraicGeometry.PolarizedFamily.IsomCorepresentationSetup.nonempty`.
* `AlgebraicGeometry.PolarizedFamily.IsomCorepresentationSetup.isoEquiv_restrict`: naturality.
* `AlgebraicGeometry.PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection`.

## Implementation notes

The base of `y` (respectively `b`) is only propositionally equal to that of `x` (respectively
`a`), so the structure morphisms of `y` and `b` are read into the base of `x` and `a` through
`AlgebraicGeometry.PolarizedFamily.toBaseOfEq`; with this, all squares in play are commutative
squares of schemes over the same bases and the machinery of
`StacksDraft.AlgebraicGeometry.SectionRingBaseChange` applies verbatim. The algebra structure of
`Γ(T, 𝒪_T)` over `Γ(V, 𝒪_V)` is the one of `Scheme.Hom.appLE` on the whole of `T`, as in
`Stacks.AlgebraicGeometry.SectionRingBaseChange.isBaseChange_tailMapLinearTop`; it agrees with
`Scheme.Hom.appTop` (`appLE_top_eq_appTop`), which is the form of the statement.

The vanishing of the higher direct images is obtained from
`Stacks.AlgebraicGeometry.ProjectiveDeformation.uniformHighTwistVanishing` and passed on, without
being restated, to the cohomology and base change results; the setup structure records only its
consequences.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Stacks.Sites (top_le_preimage_top)
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.GradedIsomScheme

universe u

namespace Stacks.GradedIsomScheme

namespace GradedMulDatum

variable {R : Type u} [CommRing R]

namespace Iso

variable {M N P : GradedMulDatum R}

/-- The inverse of an isomorphism of graded multiplication data. -/
def symm (I : Iso M N) : Iso N M where
  hom := I.inv
  inv := I.hom
  hom_inv := I.inv_hom
  inv_hom := I.hom_inv

/-- The composite of two isomorphisms of graded multiplication data (`I` first). -/
def trans (I : Iso M N) (J : Iso N P) : Iso M P where
  hom := J.hom.comp I.hom
  inv := I.inv.comp J.inv
  hom_inv n x := by simp [J.hom_inv, I.hom_inv]
  inv_hom n y := by simp [I.inv_hom, J.inv_hom]

/-- The forward homomorphism of the inverse is the inverse homomorphism. -/
@[simp]
theorem symm_hom (I : Iso M N) : I.symm.hom = I.inv := rfl

/-- The inverse homomorphism of the inverse is the forward homomorphism. -/
@[simp]
theorem symm_inv (I : Iso M N) : I.symm.inv = I.hom := rfl

/-- The forward homomorphism of a composite, in each degree. -/
@[simp]
theorem trans_hom_app (I : Iso M N) (J : Iso N P) (n : ℕ) (x : M.piece n) :
    (I.trans J).hom.app n x = J.hom.app n (I.hom.app n x) := rfl

/-- The inverse homomorphism of a composite, in each degree. -/
@[simp]
theorem trans_inv_app (I : Iso M N) (J : Iso N P) (n : ℕ) (x : P.piece n) :
    (I.trans J).inv.app n x = I.inv.app n (J.inv.app n x) := rfl

variable {M' N' : GradedMulDatum R}

/-- **Conjugation of isomorphisms**: isomorphisms `M ≅ N` correspond to isomorphisms `M' ≅ N'`
through `M' ≅ M` and `N' ≅ N`. -/
def congr (e₁ : Iso M' M) (e₂ : Iso N' N) : Iso M N ≃ Iso M' N' where
  toFun I := e₁.trans (I.trans e₂.symm)
  invFun J := e₁.symm.trans (J.trans e₂)
  left_inv I := Iso.ext (by ext n x; simp [e₁.inv_hom, e₂.inv_hom])
  right_inv J := Iso.ext (by ext n x; simp [e₁.hom_inv, e₂.hom_inv])

/-- The forward homomorphism of a conjugated isomorphism, in each degree. -/
@[simp]
theorem congr_apply_hom_app (e₁ : Iso M' M) (e₂ : Iso N' N) (I : Iso M N) (n : ℕ)
    (x : M'.piece n) :
    (congr e₁ e₂ I).hom.app n x = e₂.inv.app n (I.hom.app n (e₁.hom.app n x)) := rfl

end Iso

end GradedMulDatum

open GradedMulDatum

variable {R : Type u} [CommRing R] {M N : GradedMulDatum R}
  [∀ n, Module.Finite R (M.piece n)] [∀ n, Module.Projective R (M.piece n)]
  [∀ n, Module.Finite R (N.piece n)] [∀ n, Module.Projective R (N.piece n)]

/-- **Naturality of `isomEquiv` in the algebra**: the isomorphism classified by `f ∘ φ` is the base
change along `f` of the isomorphism classified by `φ`, read on the elements `1 ⊗ m`. -/
theorem isomEquiv_comp_hom_app_one_tmul {C C' : Type u} [CommRing C] [Algebra R C]
    [CommRing C'] [Algebra R C'] (f : C →ₐ[R] C') (φ : isomAlgebra M N →ₐ[R] C) (n : ℕ)
    (m : M.piece n) :
    (isomEquiv M N C' (f.comp φ)).hom.app n (1 ⊗ₜ m) =
      f.toLinearMap.rTensor (N.piece n) ((isomEquiv M N C φ).hom.app n (1 ⊗ₜ m)) := by
  refine (isoOfAlgHom_hom_app_one_tmul (f.comp φ) n m).trans ?_
  refine Eq.trans ?_ (congrArg _ (isoOfAlgHom_hom_app_one_tmul φ n m).symm)
  rw [AlgHom.comp_assoc, pushData_comp]
  rfl

end Stacks.GradedIsomScheme

namespace AlgHom

/-- Algebra homomorphisms `A →ₐ[R] C` are the ring homomorphisms `A →+* C` under `R`. -/
def equivRingHomUnder (R A C : Type*) [CommRing R] [CommRing A] [CommRing C] [Algebra R A]
    [Algebra R C] :
    (A →ₐ[R] C) ≃ {f : A →+* C // f.comp (algebraMap R A) = algebraMap R C} where
  toFun φ := ⟨φ.toRingHom, φ.comp_algebraMap⟩
  invFun f := { f.1 with commutes' := fun r => RingHom.congr_fun f.2 r }
  left_inv _ := AlgHom.ext fun _ => rfl
  right_inv _ := Subtype.ext (RingHom.ext fun _ => rfl)

/-- The ring homomorphism underlying an algebra homomorphism. -/
@[simp]
theorem equivRingHomUnder_apply_coe {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (φ : A →ₐ[R] C) :
    (equivRingHomUnder R A C φ).1 = φ.toRingHom := rfl

end AlgHom

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

open Stacks.AlgebraicGeometry.SectionAlgebra

/-- The global sections over the whole of the target of a morphism of schemes, read through
`appLE`. -/
theorem appLE_top_eq_appTop {T' T : Scheme.{u}} (h : T' ⟶ T) :
    h.appLE ⊤ ⊤ (top_le_preimage_top h) = h.appTop :=
  Scheme.Hom.appLE_eq_app h

section Square

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  (w : q ≫ g = g' ≫ h) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M') (e : ℕ) (he : 0 < e)

/-- **Pulling global sections back along a commutative square**, in each degree of the truncated
section algebras `𝒪 ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}` and `𝒪 ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n}`: the map of
functions in degree `0`, the pullback of sections along `q` followed by `ε` in degrees `≥ e`. -/
def globalSectionPull (n : ℕ) :
    (tailAlgebra g M e he).globalDatum.piece n →+ (tailAlgebra g' M' e he).globalDatum.piece n :=
  tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom
    (squarePieceMap q g g' h w M M' ε ⊤ ⊤ (top_le_preimage_top h)) n

/-- The pullback of global sections is semilinear over the map of global functions. -/
theorem globalSectionPull_smul (n : ℕ) (r : Γ(T, ⊤))
    (x : (tailAlgebra g M e he).globalDatum.piece n) :
    globalSectionPull q g g' h w M M' ε e he n (r • x) =
      h.appLE ⊤ ⊤ (top_le_preimage_top h) r • globalSectionPull q g g' h w M M' ε e he n x :=
  tailMapApp_smul q g g' h w M M' ε e he ⊤ (top_le_preimage_top h) n r x

/-- The pullback of global sections is multiplicative. -/
theorem globalSectionPull_mul (i j : ℕ) (a : (tailAlgebra g M e he).globalDatum.piece i)
    (b : (tailAlgebra g M e he).globalDatum.piece j) :
    globalSectionPull q g g' h w M M' ε e he (i + j)
        ((tailAlgebra g M e he).globalDatum.mul i j a b) =
      (tailAlgebra g' M' e he).globalDatum.mul i j (globalSectionPull q g g' h w M M' ε e he i a)
        (globalSectionPull q g g' h w M M' ε e he j b) :=
  tailMapApp_mul
    (fun n r x => squarePieceMap_smul q g g' h w M M' ε ⊤ ⊤ (top_le_preimage_top h) n r x)
    (fun n m _ _ x y => squarePieceMap_mul q g g' h w M M' ε ⊤ ⊤ (top_le_preimage_top h) n m x y)
    (i : ℤ) (j : ℤ) a b

/-- The pullback of global sections preserves the unit. -/
theorem globalSectionPull_one :
    globalSectionPull q g g' h w M M' ε e he 0 (tailAlgebra g M e he).globalDatum.one =
      (tailAlgebra g' M' e he).globalDatum.one :=
  tailMapApp_one

/-- **The pullback of global sections along a square, extended to the base change**, in degree
`n`: the `Γ(T', 𝒪)`-linear map `Γ(T', 𝒪) ⊗_{Γ(T, 𝒪)} Γ(𝒜_n) ⟶ Γ(𝒜'_n)`, `Γ(T', 𝒪)` being a
`Γ(T, 𝒪)`-algebra through `h`. -/
def baseChangeDatumApp (n : ℕ) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    ((tailAlgebra g M e he).globalDatum.baseChange Γ(T', ⊤)).piece n →ₗ[Γ(T', ⊤)]
      (tailAlgebra g' M' e he).globalDatum.piece n :=
  letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    Module.compHom _ (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom
  haveI : IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (tailMapLinearTop q g g' h w M M' ε e he (top_le_preimage_top h) n).liftBaseChange Γ(T', ⊤)

/-- The base-changed pullback of sections on a pure tensor `c ⊗ x` is `c` times the pullback
of `x`. -/
theorem baseChangeDatumApp_tmul (n : ℕ) (c : Γ(T', ⊤))
    (x : (tailAlgebra g M e he).globalDatum.piece n) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    baseChangeDatumApp q g g' h w M M' ε e he n (c ⊗ₜ x) =
      c • globalSectionPull q g g' h w M M' ε e he n x :=
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  let : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    Module.compHom _ (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom
  have : IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange_tmul (A := Γ(T', ⊤))
    (tailMapLinearTop q g g' h w M M' ε e he (top_le_preimage_top h) n) c x

/-- **The pullback of global sections along a square, extended to the base change**: the
homomorphism of graded multiplication data `Γ(T', 𝒪) ⊗_{Γ(T, 𝒪)} Γ(𝒜) ⟶ Γ(𝒜')` over `Γ(T', 𝒪)`,
`Γ(T', 𝒪)` being a `Γ(T, 𝒪)`-algebra through `h`. -/
def baseChangeDatumHom :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    GradedMulDatum.Hom ((tailAlgebra g M e he).globalDatum.baseChange Γ(T', ⊤))
      (tailAlgebra g' M' e he).globalDatum :=
  letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  { app n := baseChangeDatumApp q g g' h w M M' ε e he n
    app_mul i j a b := by
      induction a using TensorProduct.inductionOn with
      | add a a' ha ha' =>
        rw [LinearMap.map_add₂, map_add, ha, ha', map_add, LinearMap.map_add₂]
      | tmul c x =>
        induction b using TensorProduct.inductionOn with
        | add b b' hb hb' => rw [map_add, map_add, hb, hb', map_add, map_add]
        | tmul c' y =>
          rw [GradedMulDatum.baseChange_mul_tmul, baseChangeDatumApp_tmul,
            baseChangeDatumApp_tmul, baseChangeDatumApp_tmul, LinearMap.map_smul₂,
            LinearMap.map_smul, mul_smul]
          exact congrArg _ (congrArg _
            (globalSectionPull_mul q g g' h w M M' ε e he i j x y))
    app_one := by
      refine (baseChangeDatumApp_tmul q g g' h w M M' ε e he 0 1 _).trans ?_
      rw [one_smul]
      exact globalSectionPull_one q g g' h w M M' ε e he }

/-- The base-change homomorphism on a pure tensor `c ⊗ x` is `c` times the pullback of `x`. -/
theorem baseChangeDatumHom_app_tmul (n : ℕ) (c : Γ(T', ⊤))
    (x : (tailAlgebra g M e he).globalDatum.piece n) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    (baseChangeDatumHom q g g' h w M M' ε e he).app n (c ⊗ₜ x) =
      c • globalSectionPull q g g' h w M M' ε e he n x :=
  baseChangeDatumApp_tmul q g g' h w M M' ε e he n c x

/-- Over affine bases, the base-change homomorphism of global sections data is bijective in every
degree as soon as the transposes `h^* 𝒜_n ⟶ 𝒜'_n` are isomorphisms. -/
theorem bijective_baseChangeDatumHom_app [IsAffine T] [IsAffine T']
    (hiso : ∀ n : ℤ, IsIso ((tailPullbackHom q g g' h w M M' ε e he).app n)) (n : ℕ) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    Function.Bijective ((baseChangeDatumHom q g g' h w M M' ε e he).app n) := by
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  let : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    Module.compHom _ (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom
  have : IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbc :=
    isBaseChange_tailMapLinearTop q g g' h w M M' ε e he (top_le_preimage_top h) n (hiso n)
  change Function.Bijective (⇑((tailMapLinearTop q g g' h w M M' ε e he
    (top_le_preimage_top h) n).liftBaseChange Γ(T', ⊤)))
  have key : ⇑((tailMapLinearTop q g g' h w M M' ε e he (top_le_preimage_top h) n).liftBaseChange
      Γ(T', ⊤)) = ⇑hbc.equiv := by
    funext z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
    | tmul c x =>
      rw [LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul]
  rw [key]
  exact hbc.equiv.bijective

/-- **Over affine bases, global sections data commute with base change**: the isomorphism of
graded multiplication data `Γ(T', 𝒪) ⊗_{Γ(T, 𝒪)} Γ(𝒜) ≅ Γ(𝒜')` given by pulling sections back,
as soon as the transposes `h^* 𝒜_n ⟶ 𝒜'_n` are isomorphisms. -/
def baseChangeDatumIso [IsAffine T] [IsAffine T']
    (hiso : ∀ n : ℤ, IsIso ((tailPullbackHom q g g' h w M M' ε e he).app n)) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    GradedMulDatum.Iso ((tailAlgebra g M e he).globalDatum.baseChange Γ(T', ⊤))
      (tailAlgebra g' M' e he).globalDatum :=
  letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  GradedMulDatum.Iso.ofBijective (baseChangeDatumHom q g g' h w M M' ε e he)
    (bijective_baseChangeDatumHom_app q g g' h w M M' ε e he hiso)

/-- **`globalSectionPull` depends only on the square**: equal morphisms of total spaces and of
bases, with the same comparison of polarizations, give the same pullback of global sections. -/
theorem globalSectionPull_congr {q₁ q₂ : Y' ⟶ Y} {h₁ h₂ : T' ⟶ T} (w₁ : q₁ ≫ g = g' ≫ h₁)
    (w₂ : q₂ ≫ g = g' ≫ h₂) {ε₁ : (Scheme.Modules.pullback q₁).obj M ≅ M'}
    {ε₂ : (Scheme.Modules.pullback q₂).obj M ≅ M'} (hq : q₁ = q₂) (hh : h₁ = h₂) (hε : ε₁ ≍ ε₂)
    (n : ℕ) (x : (tailAlgebra g M e he).globalDatum.piece n) :
    globalSectionPull q₁ g g' h₁ w₁ M M' ε₁ e he n x =
      globalSectionPull q₂ g g' h₂ w₂ M M' ε₂ e he n x := by
  subst hq hh
  cases hε
  rfl

/-- **The pullbacks of global sections compose along pasted squares.** -/
theorem globalSectionPull_comp {Y'' T'' : Scheme.{u}} (q' : Y'' ⟶ Y') (g'' : Y'' ⟶ T'')
    (h' : T'' ⟶ T') (w' : q' ≫ g' = g'' ≫ h') [QuasiCompact g''] [QuasiSeparated g'']
    (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
    (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'') (n : ℕ)
    (x : (tailAlgebra g M e he).globalDatum.piece n) :
    globalSectionPull (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') e he n x =
      globalSectionPull q' g' g'' h' w' M' M'' ε' e he n
        (globalSectionPull q g g' h w M M' ε e he n x) := by
  refine Eq.trans ?_ (tailMapApp_comp _ _ _ _ (n : ℤ) x).symm
  have hρ : ((h' ≫ h).appLE ⊤ ⊤ (top_le_preimage_top (h' ≫ h))).hom =
      (h'.appLE ⊤ ⊤ (top_le_preimage_top h')).hom.comp
        (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have hΦ : squarePieceMap (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') M
        M'' ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') ⊤ ⊤ (top_le_preimage_top (h' ≫ h)) =
      fun m => (squarePieceMap q' g' g'' h' w' M' M'' ε' ⊤ ⊤ (top_le_preimage_top h') m).comp
        (squarePieceMap q g g' h w M M' ε ⊤ ⊤ (top_le_preimage_top h) m) := by
    funext m
    exact AddMonoidHom.ext fun y => sectionPull_comp q q' M M' M'' ε ε' m (g ⁻¹ᵁ ⊤) (g' ⁻¹ᵁ ⊤)
      (g'' ⁻¹ᵁ ⊤)
      (preimage_le_preimage q g g' h w ⊤ ⊤ (top_le_preimage_top h))
      (preimage_le_preimage q' g' g'' h' w' ⊤ ⊤ (top_le_preimage_top h'))
      (preimage_le_preimage (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w')
        ⊤ ⊤ (top_le_preimage_top (h' ≫ h))) y
  exact congrArg₂ (fun ρ Φ => tailMapApp _ _ e e he he le_rfl ⊤ ⊤ ρ Φ (n : ℤ) x) hρ hΦ

/-- **The map of global functions along `h' : T'' ⟶ T'`, as a homomorphism of algebras** over
`Γ(T, 𝒪)`, the two targets being algebras through `h` and through a morphism `h''` equal to
`h' ≫ h`. -/
def restrictAlgHom {T'' : Scheme.{u}} (h' : T'' ⟶ T') (h'' : T'' ⟶ T) (hh : h'' = h' ≫ h) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    letI : Algebra Γ(T, ⊤) Γ(T'', ⊤) := (h''.appLE ⊤ ⊤ (top_le_preimage_top h'')).hom.toAlgebra
    Γ(T', ⊤) →ₐ[Γ(T, ⊤)] Γ(T'', ⊤) :=
  letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(T'', ⊤) := (h''.appLE ⊤ ⊤ (top_le_preimage_top h'')).hom.toAlgebra
  { (h'.appLE ⊤ ⊤ (top_le_preimage_top h')).hom with
    commutes' := fun r => by
      subst hh
      change (h'.appLE ⊤ ⊤ (top_le_preimage_top h')).hom
          ((h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom r) =
        ((h' ≫ h).appLE ⊤ ⊤ (top_le_preimage_top (h' ≫ h))).hom r
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] }

/-- `restrictAlgHom` is the map of global functions. -/
theorem restrictAlgHom_apply {T'' : Scheme.{u}} (h' : T'' ⟶ T') (h'' : T'' ⟶ T)
    (hh : h'' = h' ≫ h) (c : Γ(T', ⊤)) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    letI : Algebra Γ(T, ⊤) Γ(T'', ⊤) := (h''.appLE ⊤ ⊤ (top_le_preimage_top h'')).hom.toAlgebra
    restrictAlgHom h h' h'' hh c = h'.appLE ⊤ ⊤ (top_le_preimage_top h') c := rfl

/-- **The base change isomorphism of global sections data is compatible with restriction**: for
a second square `q' : Y'' ⟶ Y'` over `h' : T'' ⟶ T'`, the base change along the pasted square of
`(Γ(T', 𝒪) → Γ(T'', 𝒪)) ⊗ id` is the pullback of global sections along the second square after the
base change along the first. -/
theorem baseChangeDatumHom_restrict {Y'' T'' : Scheme.{u}} (q' : Y'' ⟶ Y') (g'' : Y'' ⟶ T'')
    (h' : T'' ⟶ T') (w' : q' ≫ g' = g'' ≫ h') [QuasiCompact g''] [QuasiSeparated g'']
    (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
    (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'') (h'' : T'' ⟶ T) (hh : h'' = h' ≫ h)
    (w'' : (q' ≫ q) ≫ g = g'' ≫ h'') (n : ℕ)
    (z : letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
      ((tailAlgebra g M e he).globalDatum.baseChange Γ(T', ⊤)).piece n) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
    letI : Algebra Γ(T, ⊤) Γ(T'', ⊤) := (h''.appLE ⊤ ⊤ (top_le_preimage_top h'')).hom.toAlgebra
    (baseChangeDatumHom (q' ≫ q) g g'' h'' w'' M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') e he).app n
        ((restrictAlgHom h h' h'' hh).toLinearMap.rTensor _ z) =
      globalSectionPull q' g' g'' h' w' M' M'' ε' e he n
        ((baseChangeDatumHom q g g' h w M M' ε e he).app n z) := by
  subst hh
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ (top_le_preimage_top h)).hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(T'', ⊤) :=
    ((h' ≫ h).appLE ⊤ ⊤ (top_le_preimage_top (h' ≫ h))).hom.toAlgebra
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  | tmul c x =>
    rw [LinearMap.rTensor_tmul, baseChangeDatumHom_app_tmul, baseChangeDatumHom_app_tmul,
      globalSectionPull_smul, globalSectionPull_comp q g g' h w M M' ε e he q' g'' h' w' M'' ε']
    rfl

end Square

section Finiteness

variable {Y T : Scheme.{u}} (g : Y ⟶ T) [QuasiCompact g] [QuasiSeparated g]
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (e : ℕ) (he : 0 < e)

/-- **Over an affine base, the global sections data of the truncated section algebra has finite
projective pieces** as soon as the direct images `g_*ℳ^{⊗ n}`, `n ≥ e`, are finite locally free:
the degree `0` piece is `Γ(T, 𝒪)`, the pieces of degree `≥ e` are the global sections of finite
locally free modules over an affine scheme, and the others vanish. -/
theorem finite_projective_globalDatum_piece [IsAffine T]
    (hlf : ∀ n : ℕ, e ≤ n → _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := T.ringCatSheaf) ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)))) (n : ℕ) :
    Module.Finite Γ(T, ⊤) ((tailAlgebra g M e he).globalDatum.piece n) ∧
      Module.Projective Γ(T, ⊤) ((tailAlgebra g M e he).globalDatum.piece n) := by
  by_cases h0 : (n : ℤ) = 0
  · obtain rfl : n = 0 := by exact_mod_cast h0
    have h1 : Module.Free (ToType (T.ringCatSheaf.obj.obj (op ⊤)))
        (ToType ((_root_.SheafOfModules.unit T.ringCatSheaf).val.obj (op ⊤))) :=
      Module.Free.self _
    have h2 : Module.Finite (ToType (T.ringCatSheaf.obj.obj (op ⊤)))
        (ToType ((_root_.SheafOfModules.unit T.ringCatSheaf).val.obj (op ⊤))) :=
      Module.Finite.self _
    exact ⟨h2, @Module.Projective.of_free _ _ _ _ _ h1⟩
  · by_cases hn : (e : ℤ) ≤ (n : ℤ)
    · have := hlf n (by exact_mod_cast hn)
      have := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
        ((Scheme.Modules.pushforward g).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)))
      obtain ⟨h1, h2⟩ :=
        _root_.AlgebraicGeometry.SheafOfModules.module_finite_and_projective_sections
          ((Scheme.Modules.pushforward g).obj
            ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ))) ⟨⊤, isAffineOpen_top T⟩
      let ψ : ((tailAlgebra g M e he).piece (n : ℤ) : T.Modules) ≅
          (Scheme.Modules.pushforward g).obj
            ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)) :=
        eqToIso (tailPiece_eq_piece
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
            (Stacks.RelativeAmple.laurentPowers M)) e he hn)
      let φ := LinearEquiv.ofBijective (Scheme.Modules.sectionsLinearMap ψ.inv ⊤)
        (bijective_iso_hom_app' ψ.symm (op ⊤))
      have : Module.Finite Γ(T, ⊤) Γ((Scheme.Modules.pushforward g).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), ⊤) := h1
      have : Module.Projective Γ(T, ⊤) Γ((Scheme.Modules.pushforward g).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), ⊤) := h2
      exact ⟨Module.Finite.equiv φ, Module.Projective.of_equiv φ⟩
    · have hsub : Subsingleton ((tailAlgebra g M e he).globalDatum.piece n) :=
        ⟨fun x y => (eq_zero_of_tailPiece _ e h0 hn (op ⊤) x).trans
          (eq_zero_of_tailPiece _ e h0 hn (op ⊤) y).symm⟩
      have : Finite ((tailAlgebra g M e he).globalDatum.piece n) := Finite.of_subsingleton
      exact ⟨Module.Finite.of_finite,
        @Module.Projective.of_free _ _ _ _ _ (Module.Free.of_subsingleton _ _)⟩

omit [QuasiCompact g] [QuasiSeparated g] in
/-- The tensor powers of an invertible module are flat over the base of a flat morphism. -/
theorem isFlatOver_laurentPowers_piece [Flat g] (n : ℤ) :
    IsFlatOver g.toLRSHom.toShHom ((Stacks.RelativeAmple.laurentPowers M).piece n) :=
  have := isFiniteLocallyFree_laurentPowers_piece M n
  _root_.AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree
    g ((Stacks.RelativeAmple.laurentPowers M).piece n)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- The tensor powers of an invertible module are supported on a closed subset proper over the
base of a proper morphism (the whole source). -/
theorem exists_isProperOver_laurentPowers_piece [IsProper g]
    (hfp : _root_.AlgebraicGeometry.FinitePresentation g) (n : ℤ) :
    letI : LocallyOfFinitePresentation g := hfp.locallyOfFinitePresentation
    ∃ Z : TopologicalSpace.Closeds Y, IsProperOver g Z ∧
      _root_.SheafOfModules.supp ((Stacks.RelativeAmple.laurentPowers M).piece n) ⊆
        (Z : Set Y) := by
  let _ : LocallyOfFinitePresentation g := hfp.locallyOfFinitePresentation
  refine ⟨⊤, ?_, fun x _ => trivial⟩
  rw [isProperOver_iff_exists_isProper]
  exact ⟨⊥, Scheme.IdealSheafData.support_bot, inferInstance⟩

end Finiteness

end Stacks.AlgebraicGeometry.SectionRingBaseChange

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

open SectionRingBaseChange

namespace PolarizedIsoSectionBijection

variable (hbij : PolarizedIsoSectionBijection.{u}) {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (L : X.Modules) (M : Y.Modules)
  [IsProper f] [Flat f] [QuasiCompact f] [QuasiSeparated f]
  [IsProper g] [Flat g] [QuasiCompact g] [QuasiSeparated g]
  [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M] [IsAffine S]
  (hf : _root_.AlgebraicGeometry.FinitePresentation f)
  (hg : _root_.AlgebraicGeometry.FinitePresentation g)
  (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
  (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- **The bijection between polarized isomorphisms over an affine base and isomorphisms of the
global sections data**, at the cut `d₀`, chosen from `PolarizedIsoSectionBijection`. -/
def isoEquiv :
    PolarizedIsoOver f g L M ≃
      GradedMulDatum.Iso (tailAlgebra g M d₀ hd₀).globalDatum
        (tailAlgebra f L d₀ hd₀).globalDatum :=
  Classical.choose (hbij f g L M hf hg hL hM d₀ hd₀)

/-- The isomorphism of global sections data attached to a polarized isomorphism pulls sections
back along its square over the identity of the base. -/
theorem isoEquiv_hom_app (φ : PolarizedIsoOver f g L M) (n : ℕ)
    (s : (tailAlgebra g M d₀ hd₀).globalDatum.piece n) :
    (isoEquiv hbij f g L M hf hg hL hM d₀ hd₀ φ).hom.app n s =
      globalSectionPull φ.iso.hom g f (𝟙 S) (by rw [φ.comm, Category.comp_id]) M L φ.pol d₀ hd₀
        n s :=
  Classical.choose_spec (hbij f g L M hf hg hL hM d₀ hd₀) φ n s

end PolarizedIsoSectionBijection

end Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace AlgebraicGeometry.PolarizedFamily

open Stacks.AlgebraicGeometry.SectionRingBaseChange Stacks.AlgebraicGeometry.ProjectiveDeformation

variable {B : BigFppfSite.{u}}

attribute [local instance] PolarizedFamily.proper PolarizedFamily.flat PolarizedFamily.invertible

/-- The structure morphism of a polarized family, read into a base scheme equal to its own. -/
def toBaseOfEq (z : PolarizedFamily B) {s : B.Schemes} (h : z.base = s) :
    z.total ⟶ B.inclusion.obj s :=
  z.toBase ≫ B.inclusion.map (eqToHom h)

/-- The transported structure morphism is proper. -/
instance isProper_toBaseOfEq (z : PolarizedFamily B) {s : B.Schemes} (h : z.base = s) :
    IsProper (z.toBaseOfEq h) := by
  unfold toBaseOfEq
  infer_instance

/-- The transported structure morphism is flat. -/
instance flat_toBaseOfEq (z : PolarizedFamily B) {s : B.Schemes} (h : z.base = s) :
    Flat (z.toBaseOfEq h) := by
  unfold toBaseOfEq
  infer_instance

/-- The transported structure morphism is of finite presentation. -/
theorem finitePresentation_toBaseOfEq (z : PolarizedFamily B) {s : B.Schemes}
    (h : z.base = s) : _root_.AlgebraicGeometry.FinitePresentation (z.toBaseOfEq h) := by
  subst h
  simpa [toBaseOfEq] using z.finitePresentation

/-- The polarization is relatively ample for the transported structure morphism. -/
theorem isRelativelyAmple_toBaseOfEq (z : PolarizedFamily B) {s : B.Schemes}
    (h : z.base = s) : Stacks.RelativeAmple.IsRelativelyAmple (z.toBaseOfEq h) z.lineBundle := by
  subst h
  simpa [toBaseOfEq] using z.relativelyAmple

/-- **The square of a morphism of polarized families, read over bases equal to their own**: the
square of `c : x ⟶ y` stays cartesian over any morphism `k` of the new bases corresponding to the
base map of `c`. -/
theorem isPullback_toBaseOfEq {x y : PolarizedFamily B} (c : x ⟶ y) {s t : B.Schemes}
    (hx : x.base = s) (hy : y.base = t) (k : s ⟶ t)
    (hk : c.baseMap ≫ eqToHom hy = eqToHom hx ≫ k) :
    IsPullback c.totalMap (x.toBaseOfEq hx) (y.toBaseOfEq hy) (B.inclusion.map k) := by
  subst hx hy
  obtain rfl : k = c.baseMap := by simpa using hk.symm
  simpa [toBaseOfEq] using c.cartesian

/-- The square of an isomorphism over the identity of the base, over the identity. -/
theorem isPullback_isoOverBase {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (φ : IsoOverBase x y hxy) :
    IsPullback φ.1.totalMap (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) (B.inclusion.map (𝟙 _)) :=
  isPullback_toBaseOfEq φ.1 rfl hxy.symm (𝟙 _) (by simp [φ.2])

/-- The map of total spaces of an isomorphism over the identity of the base is invertible: its
square is cartesian over an isomorphism. -/
instance isIso_totalMap_isoOverBase {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (φ : IsoOverBase x y hxy) : IsIso φ.1.totalMap :=
  (isPullback_isoOverBase φ).isIso_fst_of_isIso

/-- The polarized isomorphism over the base underlying an isomorphism over the identity of the
base. -/
def IsoOverBase.toPolarizedIsoOver {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (φ : IsoOverBase x y hxy) :
    PolarizedIsoOver (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) x.lineBundle y.lineBundle where
  iso := asIso φ.1.totalMap
  comm := by simpa using (isPullback_isoOverBase φ).w
  pol := φ.1.lineBundleIso

/-- The isomorphism over the identity of the base underlying a polarized isomorphism over the
base: its square is cartesian, both horizontal maps being isomorphisms. -/
def ofPolarizedIsoOver {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (P : PolarizedIsoOver (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) x.lineBundle
      y.lineBundle) : IsoOverBase x y hxy :=
  ⟨{ baseMap := eqToHom hxy
     totalMap := P.iso.hom
     cartesian := IsPullback.of_horiz_isIso ⟨by
       have hc := congrArg (· ≫ B.inclusion.map (eqToHom hxy)) P.comm
       simpa [toBaseOfEq] using hc⟩
     lineBundleIso := P.pol }, rfl⟩

/-- **Isomorphisms over the identity of the base are polarized isomorphisms over the base**: a
morphism of polarized families whose base map is the identity has an invertible map of total
spaces (its square is cartesian over an isomorphism), commuting with the structure morphisms. -/
def isoOverBaseEquiv (x y : PolarizedFamily B) (hxy : x.base = y.base) :
    IsoOverBase x y hxy ≃
      PolarizedIsoOver (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) x.lineBundle y.lineBundle where
  toFun φ := φ.toPolarizedIsoOver
  invFun P := ofPolarizedIsoOver P
  left_inv φ := Subtype.ext (Hom.ext φ.2.symm rfl HEq.rfl)
  right_inv _ := PolarizedIsoOver.ext rfl HEq.rfl

/-- `isoOverBaseEquiv` is `IsoOverBase.toPolarizedIsoOver`. -/
theorem isoOverBaseEquiv_apply (x y : PolarizedFamily B) (hxy : x.base = y.base)
    (φ : IsoOverBase x y hxy) : isoOverBaseEquiv x y hxy φ = φ.toPolarizedIsoOver := rfl

/-- Reversing a commutative square of base maps through equalities of bases. -/
theorem comp_eqToHom_symm_eq {C : Type*} [Category C] {s t s' t' : C} (k : s ⟶ t) (k' : s' ⟶ t')
    (h₁ : s = s') (h₂ : t = t') (h : k ≫ eqToHom h₂ = eqToHom h₁ ≫ k') :
    k' ≫ eqToHom h₂.symm = eqToHom h₁.symm ≫ k := by
  subst h₁ h₂
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h ⊢
  exact h.symm

/-- **A uniform degree bound for two polarized families over a common affine base** `V`: a cut
`d₀ > 0` such that, for `z ∈ {a, b}` (read over `V`), the direct images `z_*ℒ_z^{⊗ n}`,
`n ≥ d₀`, are finite locally free and their formation commutes with every cartesian base change
(the transposes `h^* 𝒜_n ⟶ 𝒜'_n` of the truncated section algebras are isomorphisms). -/
structure IsomCorepresentationSetup (a b : PolarizedFamily B) (hab : a.base = b.base) where
  /-- The cut. -/
  degree : ℕ
  /-- The cut is positive. -/
  degree_pos : 0 < degree
  /-- The formation of the truncated section algebras commutes with cartesian base change. -/
  isIso_tailPullbackHom : ∀ (z : PolarizedFamily B) (hz : z.base = a.base), (z = a ∨ z = b) →
    ∀ {T Y : Scheme.{u}} (q : Y ⟶ z.total) (g : Y ⟶ T) (h : T ⟶ B.inclusion.obj a.base)
      [QuasiCompact g] [QuasiSeparated g] (hpb : IsPullback q g (z.toBaseOfEq hz) h)
      (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
      (ε : (Scheme.Modules.pullback q).obj z.lineBundle ≅ M) (n : ℤ),
      IsIso ((tailPullbackHom q (z.toBaseOfEq hz) g h hpb.w z.lineBundle M ε degree
        degree_pos).app n)
  /-- The direct images of the powers of the polarizations are finite locally free. -/
  isFiniteLocallyFree : ∀ (z : PolarizedFamily B) (hz : z.base = a.base), (z = a ∨ z = b) →
    ∀ n : ℕ, degree ≤ n → _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (B.inclusion.obj a.base).ringCatSheaf) ((Scheme.Modules.pushforward
        (z.toBaseOfEq hz)).obj ((Stacks.RelativeAmple.laurentPowers z.lineBundle).piece (n : ℤ)))

namespace IsomCorepresentationSetup

open Stacks.AlgebraicGeometry.VanishingHigherDirectImages
  (isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage)

/-- **A uniform degree bound exists** ([Stacks, Tag 0D4F] (1), (2) and cohomology and base
change): over an affine, hence quasi-compact, base the higher direct images of high powers of the
two polarizations vanish, which makes the direct images finite locally free and their formation
compatible with base change. -/
theorem nonempty (a b : PolarizedFamily B) (hab : a.base = b.base)
    [IsAffine (B.inclusion.obj a.base)] : Nonempty (IsomCorepresentationSetup a b hab) := by
  obtain ⟨da, hda, hva⟩ := uniformHighTwistVanishing a.total _ (a.toBaseOfEq rfl) a.lineBundle
    inferInstance inferInstance (finitePresentation_toBaseOfEq a rfl) inferInstance
    (isRelativelyAmple_toBaseOfEq a rfl)
  obtain ⟨db, hdb, hvb⟩ := uniformHighTwistVanishing b.total _ (b.toBaseOfEq hab.symm)
    b.lineBundle inferInstance inferInstance (finitePresentation_toBaseOfEq b hab.symm)
    inferInstance (isRelativelyAmple_toBaseOfEq b hab.symm)
  let := HasDerivedCategory.standard
  have hv : ∀ (z : PolarizedFamily B) (hz : z.base = a.base), (z = a ∨ z = b) → ∀ k : ℕ,
      max da db ≤ k → ∀ p : ℤ, 0 < p → IsZero (((Scheme.Modules.pushforward
        (z.toBaseOfEq hz)).rightDerivedPlus p).obj
          (Stacks.Ample.tensorPowModule z.total z.lineBundle k)) := by
    rintro z hz (rfl | rfl) k hk p hp
    exacts [hva k (by omega) p hp, hvb k (by omega) p hp]
  refine ⟨⟨max da db, by omega, ?_, ?_⟩⟩
  · rintro z hz hzab T Y q g h _ _ hpb M _ ε n
    refine isIso_tailPullbackHom_app q (z.toBaseOfEq hz) g h hpb.w z.lineBundle M ε _ _
      (fun m hm => ?_) n
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
    exact isIso_baseChangePowHom q (z.toBaseOfEq hz) g h z.lineBundle M ε hpb
      (finitePresentation_toBaseOfEq z hz) (k : ℤ) fun p hp =>
        (hv z hz hzab k (by omega) p hp).of_iso (Functor.mapIso _
          (Stacks.PowerFamilyBridge.tensorPowerModuleIso z.total z.lineBundle (k : ℤ)))
  · rintro z hz hzab n hn
    have := isFinitePresentation_laurentPowers_piece z.lineBundle (n : ℤ)
    exact isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage
      (z.toBaseOfEq hz) (finitePresentation_toBaseOfEq z hz) _
      (isFlatOver_laurentPowers_piece _ _ _)
      (exists_isProperOver_laurentPowers_piece _ _ (finitePresentation_toBaseOfEq z hz) _)
      fun p hp => (hv z hz hzab n hn p hp).of_iso (Functor.mapIso _
        (Stacks.PowerFamilyBridge.tensorPowerModuleIso z.total z.lineBundle (n : ℤ)))

variable {a b : PolarizedFamily B} {hab : a.base = b.base} (S : IsomCorepresentationSetup a b hab)

/-- The global sections datum of the truncated section algebra of `a`, over `Γ(V, 𝒪)`. -/
abbrev datumA : GradedMulDatum Γ(B.inclusion.obj a.base, ⊤) :=
  (tailAlgebra (a.toBaseOfEq rfl) a.lineBundle S.degree S.degree_pos).globalDatum

/-- The global sections datum of the truncated section algebra of `b`, read over `V`. -/
abbrev datumB : GradedMulDatum Γ(B.inclusion.obj a.base, ⊤) :=
  (tailAlgebra (b.toBaseOfEq hab.symm) b.lineBundle S.degree S.degree_pos).globalDatum

variable [IsAffine (B.inclusion.obj a.base)]

/-- The pieces of the global sections datum of `a` are finite over `Γ(V, 𝒪)`. -/
instance finite_datumA (n : ℕ) :
    Module.Finite Γ(B.inclusion.obj a.base, ⊤) (S.datumA.piece n) :=
  (finite_projective_globalDatum_piece _ _ _ _ (S.isFiniteLocallyFree a rfl (Or.inl rfl)) n).1

/-- The pieces of the global sections datum of `a` are projective over `Γ(V, 𝒪)`. -/
instance projective_datumA (n : ℕ) :
    Module.Projective Γ(B.inclusion.obj a.base, ⊤) (S.datumA.piece n) :=
  (finite_projective_globalDatum_piece _ _ _ _ (S.isFiniteLocallyFree a rfl (Or.inl rfl)) n).2

/-- The pieces of the global sections datum of `b` are finite over `Γ(V, 𝒪)`. -/
instance finite_datumB (n : ℕ) :
    Module.Finite Γ(B.inclusion.obj a.base, ⊤) (S.datumB.piece n) :=
  (finite_projective_globalDatum_piece _ _ _ _
    (S.isFiniteLocallyFree b hab.symm (Or.inr rfl)) n).1

/-- The pieces of the global sections datum of `b` are projective over `Γ(V, 𝒪)`. -/
instance projective_datumB (n : ℕ) :
    Module.Projective Γ(B.inclusion.obj a.base, ⊤) (S.datumB.piece n) :=
  (finite_projective_globalDatum_piece _ _ _ _
    (S.isFiniteLocallyFree b hab.symm (Or.inr rfl)) n).2

/-- **The corepresenting algebra**: the Isom algebra of the global sections data of the truncated
section algebras of `b` and `a` over `Γ(V, 𝒪)`. -/
abbrev isomRing : Type u := isomAlgebra S.datumB S.datumA

omit [IsAffine (B.inclusion.obj a.base)] in
/-- The square of a morphism `x ⟶ a`. -/
theorem isPullback_a {x : PolarizedFamily B} (cx : x ⟶ a) :
    IsPullback cx.totalMap (x.toBaseOfEq rfl) (a.toBaseOfEq rfl) (B.inclusion.map cx.baseMap) :=
  isPullback_toBaseOfEq cx rfl rfl cx.baseMap (by simp)

omit [IsAffine (B.inclusion.obj a.base)] in
/-- The square of a morphism `y ⟶ b`, read over the base map of a morphism `x ⟶ a`. -/
theorem isPullback_b {x y : PolarizedFamily B} {hxy : x.base = y.base} {cx : x ⟶ a}
    {cy : y ⟶ b} (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap) :
    IsPullback cy.totalMap (y.toBaseOfEq hxy.symm) (b.toBaseOfEq hab.symm)
      (B.inclusion.map cx.baseMap) :=
  isPullback_toBaseOfEq cy hxy.symm hab.symm cx.baseMap
    (comp_eqToHom_symm_eq cx.baseMap cy.baseMap hxy hab hc)

/-- **The base change isomorphism for `x ⟶ a`** of global sections data, over `Γ(x.base, 𝒪)`. -/
def baseChangeIsoA {x : PolarizedFamily B} (hx : IsAffine (B.inclusion.obj x.base))
    (cx : x ⟶ a) :
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
      ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    GradedMulDatum.Iso (S.datumA.baseChange Γ(B.inclusion.obj x.base, ⊤))
      (tailAlgebra (x.toBaseOfEq rfl) x.lineBundle S.degree S.degree_pos).globalDatum :=
  haveI := hx
  baseChangeDatumIso cx.totalMap (a.toBaseOfEq rfl) (x.toBaseOfEq rfl)
    (B.inclusion.map cx.baseMap) (isPullback_a cx).w a.lineBundle x.lineBundle cx.lineBundleIso
    S.degree S.degree_pos (S.isIso_tailPullbackHom a rfl (Or.inl rfl) cx.totalMap _ _
      (isPullback_a cx) x.lineBundle cx.lineBundleIso)

/-- **The base change isomorphism for `y ⟶ b`** of global sections data, over `Γ(x.base, 𝒪)`. -/
def baseChangeIsoB {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (hx : IsAffine (B.inclusion.obj x.base)) {cx : x ⟶ a} (cy : y ⟶ b)
    (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap) :
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
      ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    GradedMulDatum.Iso (S.datumB.baseChange Γ(B.inclusion.obj x.base, ⊤))
      (tailAlgebra (y.toBaseOfEq hxy.symm) y.lineBundle S.degree S.degree_pos).globalDatum :=
  haveI := hx
  baseChangeDatumIso cy.totalMap (b.toBaseOfEq hab.symm) (y.toBaseOfEq hxy.symm)
    (B.inclusion.map cx.baseMap) (isPullback_b hc).w b.lineBundle y.lineBundle cy.lineBundleIso
    S.degree S.degree_pos (S.isIso_tailPullbackHom b hab.symm (Or.inr rfl) cy.totalMap _ _
      (isPullback_b hc) y.lineBundle cy.lineBundleIso)

variable (hbij : PolarizedIsoSectionBijection.{u})

/-- **The isomorphism of section data attached to an isomorphism over the identity of the base**
of the test families `x`, `y`. -/
def sectionIso {x y : PolarizedFamily B} {hxy : x.base = y.base}
    (hx : IsAffine (B.inclusion.obj x.base)) (φ : IsoOverBase x y hxy) :
    GradedMulDatum.Iso
      (tailAlgebra (y.toBaseOfEq hxy.symm) y.lineBundle S.degree S.degree_pos).globalDatum
      (tailAlgebra (x.toBaseOfEq rfl) x.lineBundle S.degree S.degree_pos).globalDatum :=
  haveI := hx
  hbij.isoEquiv (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) x.lineBundle y.lineBundle
    (finitePresentation_toBaseOfEq x rfl) (finitePresentation_toBaseOfEq y hxy.symm)
    (isRelativelyAmple_toBaseOfEq x rfl) (isRelativelyAmple_toBaseOfEq y hxy.symm) S.degree
    S.degree_pos (isoOverBaseEquiv x y hxy φ)

/-- **The corepresentation on one test datum**: isomorphisms over the identity of the base of
`x`, `y` correspond to ring homomorphisms out of the Isom ring over `Γ(V, 𝒪)`. -/
def isoEquiv (x y : PolarizedFamily B) (hxy : x.base = y.base)
    (hx : IsAffine (B.inclusion.obj x.base)) (cx : x ⟶ a) (cy : y ⟶ b)
    (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap) :
    IsoOverBase x y hxy ≃
      {f : S.isomRing →+* Γ(B.inclusion.obj x.base, ⊤) //
        f.comp (algebraMap Γ(B.inclusion.obj a.base, ⊤) S.isomRing) =
          (B.inclusion.map cx.baseMap).appTop.hom} :=
  letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
    ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
  haveI := hx
  ((isoOverBaseEquiv x y hxy).trans
    (hbij.isoEquiv (x.toBaseOfEq rfl) (y.toBaseOfEq hxy.symm) x.lineBundle y.lineBundle
      (finitePresentation_toBaseOfEq x rfl) (finitePresentation_toBaseOfEq y hxy.symm)
      (isRelativelyAmple_toBaseOfEq x rfl) (isRelativelyAmple_toBaseOfEq y hxy.symm) S.degree
      S.degree_pos)).trans <|
  (GradedMulDatum.Iso.congr (S.baseChangeIsoB hx cy hc) (S.baseChangeIsoA hx cx)).trans <|
  (isomEquiv S.datumB S.datumA Γ(B.inclusion.obj x.base, ⊤)).symm.trans <|
  (AlgHom.equivRingHomUnder _ _ _).trans <| Equiv.subtypeEquivRight fun f => by
    rw [← appLE_top_eq_appTop]
    rfl

/-- The ring homomorphism attached to an isomorphism over the base is the one classified, through
`isomEquiv`, by the conjugate of its isomorphism of section data. -/
theorem isoEquiv_apply_coe (x y : PolarizedFamily B) (hxy : x.base = y.base)
    (hx : IsAffine (B.inclusion.obj x.base)) (cx : x ⟶ a) (cy : y ⟶ b)
    (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap) (φ : IsoOverBase x y hxy) :
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
      ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    (S.isoEquiv hbij x y hxy hx cx cy hc φ).1 =
      ((isomEquiv S.datumB S.datumA Γ(B.inclusion.obj x.base, ⊤)).symm
        (GradedMulDatum.Iso.congr (S.baseChangeIsoB hx cy hc) (S.baseChangeIsoA hx cx)
          (S.sectionIso hbij hx φ))).toRingHom :=
  rfl

omit [IsAffine (B.inclusion.obj a.base)] in
/-- **Naturality of the isomorphisms of section data**: for a morphism of test data
`(rx, ry)` compatible with isomorphisms `φ'`, `φ` over the identity of the bases, pulling sections
back along `ry` and then along `φ'` is pulling them back along `φ` and then along `rx`. -/
theorem sectionIso_hom_app_restrict {x y x' y' : PolarizedFamily B} {hxy : x.base = y.base}
    {hxy' : x'.base = y'.base} (hx : IsAffine (B.inclusion.obj x.base))
    (hx' : IsAffine (B.inclusion.obj x'.base)) (rx : x' ⟶ x) (ry : y' ⟶ y)
    (hr : rx.baseMap ≫ eqToHom hxy = eqToHom hxy' ≫ ry.baseMap) (φ' : IsoOverBase x' y' hxy')
    (φ : IsoOverBase x y hxy) (heq : φ'.1 ≫ ry = rx ≫ φ.1) (n : ℕ)
    (s : (tailAlgebra (y.toBaseOfEq hxy.symm) y.lineBundle S.degree
      S.degree_pos).globalDatum.piece n) :
    (S.sectionIso hbij hx' φ').hom.app n (globalSectionPull ry.totalMap (y.toBaseOfEq hxy.symm)
        (y'.toBaseOfEq hxy'.symm) (B.inclusion.map rx.baseMap)
        (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
          (comp_eqToHom_symm_eq _ _ _ _ hr)).w
        y.lineBundle y'.lineBundle ry.lineBundleIso S.degree S.degree_pos n s) =
      globalSectionPull rx.totalMap (x.toBaseOfEq rfl) (x'.toBaseOfEq rfl)
        (B.inclusion.map rx.baseMap) (isPullback_toBaseOfEq rx rfl rfl rx.baseMap (by simp)).w
        x.lineBundle x'.lineBundle rx.lineBundleIso S.degree S.degree_pos n
        ((S.sectionIso hbij hx φ).hom.app n s) := by
  have := hx
  have := hx'
  have e1 := PolarizedIsoSectionBijection.isoEquiv_hom_app hbij (x'.toBaseOfEq rfl)
    (y'.toBaseOfEq hxy'.symm) x'.lineBundle y'.lineBundle (finitePresentation_toBaseOfEq x' rfl)
    (finitePresentation_toBaseOfEq y' hxy'.symm) (isRelativelyAmple_toBaseOfEq x' rfl)
    (isRelativelyAmple_toBaseOfEq y' hxy'.symm) S.degree S.degree_pos
    (isoOverBaseEquiv x' y' hxy' φ') n
    (globalSectionPull ry.totalMap (y.toBaseOfEq hxy.symm)
        (y'.toBaseOfEq hxy'.symm) (B.inclusion.map rx.baseMap)
        (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
          (comp_eqToHom_symm_eq _ _ _ _ hr)).w
        y.lineBundle y'.lineBundle ry.lineBundleIso S.degree S.degree_pos n s)
  have e2 := PolarizedIsoSectionBijection.isoEquiv_hom_app hbij (x.toBaseOfEq rfl)
    (y.toBaseOfEq hxy.symm) x.lineBundle y.lineBundle (finitePresentation_toBaseOfEq x rfl)
    (finitePresentation_toBaseOfEq y hxy.symm) (isRelativelyAmple_toBaseOfEq x rfl)
    (isRelativelyAmple_toBaseOfEq y hxy.symm) S.degree S.degree_pos
    (isoOverBaseEquiv x y hxy φ) n s
  refine e1.trans (Eq.trans ?_ (congrArg (globalSectionPull rx.totalMap (x.toBaseOfEq rfl)
    (x'.toBaseOfEq rfl) (B.inclusion.map rx.baseMap)
    (isPullback_toBaseOfEq rx rfl rfl rx.baseMap (by simp)).w x.lineBundle x'.lineBundle
    rx.lineBundleIso S.degree S.degree_pos n) e2).symm)
  refine ((globalSectionPull_comp ry.totalMap (y.toBaseOfEq hxy.symm) (y'.toBaseOfEq hxy'.symm)
    (B.inclusion.map rx.baseMap) (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
      (comp_eqToHom_symm_eq _ _ _ _ hr)).w y.lineBundle y'.lineBundle ry.lineBundleIso
    S.degree S.degree_pos φ'.1.totalMap (x'.toBaseOfEq rfl) (𝟙 _)
    ((isoOverBaseEquiv x' y' hxy' φ').comm.trans (Category.comp_id _).symm)
    x'.lineBundle φ'.1.lineBundleIso n s).symm).trans ?_
  refine Eq.trans ?_ (globalSectionPull_comp φ.1.totalMap (y.toBaseOfEq hxy.symm)
    (x.toBaseOfEq rfl) (𝟙 _) ((isoOverBaseEquiv x y hxy φ).comm.trans (Category.comp_id _).symm)
    y.lineBundle x.lineBundle φ.1.lineBundleIso S.degree S.degree_pos rx.totalMap
    (x'.toBaseOfEq rfl) (B.inclusion.map rx.baseMap)
    (isPullback_toBaseOfEq rx rfl rfl rx.baseMap (by simp)).w x'.lineBundle rx.lineBundleIso n s)
  exact globalSectionPull_congr (y.toBaseOfEq hxy.symm) (x'.toBaseOfEq rfl) y.lineBundle
    x'.lineBundle S.degree S.degree_pos _ _ (congrArg Hom.totalMap heq) (by simp)
    (congr_arg_heq (fun χ : x' ⟶ y => χ.lineBundleIso) heq) n s

/-- **The base change isomorphism for `y ⟶ b` is compatible with restriction** along a morphism
`ry : y' ⟶ y` of test families, on the elements `1 ⊗ m`. -/
theorem baseChangeIsoB_hom_app_restrict {x y x' y' : PolarizedFamily B} {hxy : x.base = y.base}
    {hxy' : x'.base = y'.base} (hx : IsAffine (B.inclusion.obj x.base))
    (hx' : IsAffine (B.inclusion.obj x'.base)) {cx : x ⟶ a} (cy : y ⟶ b)
    (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap) {rx : x' ⟶ x} (ry : y' ⟶ y)
    (hr : rx.baseMap ≫ eqToHom hxy = eqToHom hxy' ≫ ry.baseMap)
    (hc' : (rx ≫ cx).baseMap ≫ eqToHom hab = eqToHom hxy' ≫ (ry ≫ cy).baseMap) (n : ℕ)
    (m : S.datumB.piece n) :
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
      ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x'.base, ⊤) :=
      ((B.inclusion.map (rx ≫ cx).baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    (S.baseChangeIsoB hx' (ry ≫ cy) hc').hom.app n (1 ⊗ₜ m) =
      globalSectionPull ry.totalMap (y.toBaseOfEq hxy.symm)
        (y'.toBaseOfEq hxy'.symm) (B.inclusion.map rx.baseMap)
        (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
          (comp_eqToHom_symm_eq _ _ _ _ hr)).w
        y.lineBundle y'.lineBundle ry.lineBundleIso S.degree S.degree_pos n
        ((S.baseChangeIsoB hx cy hc).hom.app n (1 ⊗ₜ m)) := by
  let : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
    ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
  let : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x'.base, ⊤) :=
    ((B.inclusion.map (rx ≫ cx).baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
  refine ((baseChangeDatumHom_app_tmul (ry ≫ cy).totalMap (b.toBaseOfEq hab.symm)
    (y'.toBaseOfEq hxy'.symm) (B.inclusion.map (rx ≫ cx).baseMap) (isPullback_b hc').w
    b.lineBundle y'.lineBundle (ry ≫ cy).lineBundleIso S.degree S.degree_pos n 1 m).trans
      (one_smul _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (globalSectionPull ry.totalMap (y.toBaseOfEq hxy.symm)
        (y'.toBaseOfEq hxy'.symm) (B.inclusion.map rx.baseMap)
        (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
          (comp_eqToHom_symm_eq _ _ _ _ hr)).w
        y.lineBundle y'.lineBundle ry.lineBundleIso S.degree S.degree_pos n)
    ((baseChangeDatumHom_app_tmul cy.totalMap (b.toBaseOfEq hab.symm) (y.toBaseOfEq hxy.symm)
      (B.inclusion.map cx.baseMap) (isPullback_b hc).w b.lineBundle y.lineBundle
      cy.lineBundleIso S.degree S.degree_pos n 1 m).trans (one_smul _ _)).symm)
  refine Eq.trans ?_ (globalSectionPull_comp cy.totalMap (b.toBaseOfEq hab.symm)
    (y.toBaseOfEq hxy.symm) (B.inclusion.map cx.baseMap) (isPullback_b hc).w b.lineBundle
    y.lineBundle cy.lineBundleIso S.degree S.degree_pos ry.totalMap (y'.toBaseOfEq hxy'.symm)
    (B.inclusion.map rx.baseMap) (isPullback_toBaseOfEq ry hxy'.symm hxy.symm rx.baseMap
      (comp_eqToHom_symm_eq _ _ _ _ hr)).w y'.lineBundle ry.lineBundleIso n m)
  exact globalSectionPull_congr (b.toBaseOfEq hab.symm) (y'.toBaseOfEq hxy'.symm) b.lineBundle
    y'.lineBundle S.degree S.degree_pos _ _ rfl (B.inclusion.map_comp _ _) HEq.rfl n m

/-- **The base change isomorphism for `x ⟶ a` is compatible with restriction** along a morphism
`rx : x' ⟶ x` of test families. -/
theorem baseChangeIsoA_hom_app_restrict {x x' : PolarizedFamily B}
    (hx : IsAffine (B.inclusion.obj x.base)) (hx' : IsAffine (B.inclusion.obj x'.base))
    (cx : x ⟶ a) (rx : x' ⟶ x) (n : ℕ)
    (z : letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
        ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
      (S.datumA.baseChange Γ(B.inclusion.obj x.base, ⊤)).piece n) :
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
      ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    letI : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x'.base, ⊤) :=
      ((B.inclusion.map (rx ≫ cx).baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
    (S.baseChangeIsoA hx' (rx ≫ cx)).hom.app n
        ((restrictAlgHom (B.inclusion.map cx.baseMap) (B.inclusion.map rx.baseMap)
          (B.inclusion.map (rx ≫ cx).baseMap) (B.inclusion.map_comp _ _)).toLinearMap.rTensor _
          z) =
      globalSectionPull rx.totalMap (x.toBaseOfEq rfl) (x'.toBaseOfEq rfl)
        (B.inclusion.map rx.baseMap) (isPullback_toBaseOfEq rx rfl rfl rx.baseMap (by simp)).w
        x.lineBundle x'.lineBundle rx.lineBundleIso S.degree S.degree_pos n
        ((S.baseChangeIsoA hx cx).hom.app n z) :=
  baseChangeDatumHom_restrict cx.totalMap (a.toBaseOfEq rfl) (x.toBaseOfEq rfl)
    (B.inclusion.map cx.baseMap) (isPullback_a cx).w a.lineBundle x.lineBundle cx.lineBundleIso
    S.degree S.degree_pos rx.totalMap (x'.toBaseOfEq rfl) (B.inclusion.map rx.baseMap)
    (isPullback_toBaseOfEq rx rfl rfl rx.baseMap (by simp)).w x'.lineBundle rx.lineBundleIso
    (B.inclusion.map (rx ≫ cx).baseMap) (B.inclusion.map_comp _ _) (isPullback_a (rx ≫ cx)).w n z

/-- **Naturality of the corepresentation in the test datum**: restricting along a morphism of
test data `(rx, ry)` corresponds to composing with the map of global functions along the base
map of `rx`. -/
theorem isoEquiv_restrict (x y : PolarizedFamily B) (hxy : x.base = y.base)
    (hx : IsAffine (B.inclusion.obj x.base)) (cx : x ⟶ a) (cy : y ⟶ b)
    (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap)
    (x' y' : PolarizedFamily B) (hxy' : x'.base = y'.base)
    (hx' : IsAffine (B.inclusion.obj x'.base)) (rx : x' ⟶ x) (ry : y' ⟶ y)
    (hr : rx.baseMap ≫ eqToHom hxy = eqToHom hxy' ≫ ry.baseMap)
    (φ' : IsoOverBase x' y' hxy') (φ : IsoOverBase x y hxy) (heq : φ'.1 ≫ ry = rx ≫ φ.1)
    (hc' : (rx ≫ cx).baseMap ≫ eqToHom hab = eqToHom hxy' ≫ (ry ≫ cy).baseMap) :
    (S.isoEquiv hbij x' y' hxy' hx' (rx ≫ cx) (ry ≫ cy) hc' φ').1 =
      (B.inclusion.map rx.baseMap).appTop.hom.comp (S.isoEquiv hbij x y hxy hx cx cy hc φ).1 := by
  let : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x.base, ⊤) :=
    ((B.inclusion.map cx.baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
  let : Algebra Γ(B.inclusion.obj a.base, ⊤) Γ(B.inclusion.obj x'.base, ⊤) :=
    ((B.inclusion.map (rx ≫ cx).baseMap).appLE ⊤ ⊤ (top_le_preimage_top _)).hom.toAlgebra
  let ralg := restrictAlgHom (B.inclusion.map cx.baseMap) (B.inclusion.map rx.baseMap)
    (B.inclusion.map (rx ≫ cx).baseMap) (B.inclusion.map_comp _ _)
  have key : (isomEquiv S.datumB S.datumA Γ(B.inclusion.obj x'.base, ⊤)).symm
      (GradedMulDatum.Iso.congr (S.baseChangeIsoB hx' (ry ≫ cy) hc')
        (S.baseChangeIsoA hx' (rx ≫ cx)) (S.sectionIso hbij hx' φ')) =
      ralg.comp ((isomEquiv S.datumB S.datumA Γ(B.inclusion.obj x.base, ⊤)).symm
        (GradedMulDatum.Iso.congr (S.baseChangeIsoB hx cy hc) (S.baseChangeIsoA hx cx)
          (S.sectionIso hbij hx φ))) := by
    rw [Equiv.symm_apply_eq]
    refine GradedMulDatum.Iso.ext (GradedMulDatum.Hom.baseChange_ext fun n m => ?_)
    rw [isomEquiv_comp_hom_app_one_tmul, Equiv.apply_symm_apply,
      GradedMulDatum.Iso.congr_apply_hom_app, GradedMulDatum.Iso.congr_apply_hom_app]
    have hinj : Function.Injective ((S.baseChangeIsoA hx' (rx ≫ cx)).hom.app n) :=
      fun u v huv => ((S.baseChangeIsoA hx' (rx ≫ cx)).hom_inv n u).symm.trans
        ((congrArg _ huv).trans ((S.baseChangeIsoA hx' (rx ≫ cx)).hom_inv n v))
    apply hinj
    rw [(S.baseChangeIsoA hx' (rx ≫ cx)).inv_hom, S.baseChangeIsoA_hom_app_restrict hx hx' cx rx n,
      (S.baseChangeIsoA hx cx).inv_hom,
      S.baseChangeIsoB_hom_app_restrict hx hx' cy hc ry hr hc' n m]
    exact S.sectionIso_hom_app_restrict hbij hx hx' rx ry hr φ' φ heq n _
  refine ((S.isoEquiv_apply_coe hbij x' y' hxy' hx' (rx ≫ cx) (ry ≫ cy) hc' φ').trans
    ((congrArg AlgHom.toRingHom key).trans ?_)).trans
      (congrArg ((B.inclusion.map rx.baseMap).appTop.hom.comp)
        (S.isoEquiv_apply_coe hbij x y hxy hx cx cy hc φ)).symm
  exact RingHom.ext fun r => congrArg
    (fun k : Γ(B.inclusion.obj x.base, ⊤) ⟶ Γ(B.inclusion.obj x'.base, ⊤) =>
      k.hom (((isomEquiv S.datumB S.datumA Γ(B.inclusion.obj x.base, ⊤)).symm
        (GradedMulDatum.Iso.congr (S.baseChangeIsoB hx cy hc) (S.baseChangeIsoA hx cx)
          (S.sectionIso hbij hx φ))) r)) (appLE_top_eq_appTop (B.inclusion.map rx.baseMap))

end IsomCorepresentationSetup

/-- **The isomorphisms between pullbacks of two polarized families over an affine base are
corepresentable** ([Stacks, Tag 0D42], the affine core of the representability of the diagonal
of `𝒫olarized`), given that polarized isomorphisms over an affine base are the isomorphisms of
the global sections data of the truncated section algebras
(`Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`). The ring `H` is
the Isom algebra of the global sections data of the truncated section algebras of `b` and `a` at a
cut `d₀` for which [Stacks, Tag 0D4F] applies to both families. -/
theorem exists_corepresentation_isoOverBase_of_sectionBijection
    (hbij : Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection.{u})
    (a b : PolarizedFamily B) (hab : a.base = b.base) [IsAffine (B.inclusion.obj a.base)] :
    ∃ (H : Type u) (_ : CommRing H) (ι : Γ(B.inclusion.obj a.base, ⊤) →+* H),
      Cardinal.mk H ≤ max Cardinal.aleph0 (Cardinal.mk Γ(B.inclusion.obj a.base, ⊤)) ∧
      IsIsoOverBaseCorepresented a b hab H ι := by
  obtain ⟨S⟩ := IsomCorepresentationSetup.nonempty a b hab
  exact ⟨S.isomRing, inferInstance, algebraMap _ _,
    (cardinalMk_isomAlgebra_le S.datumB S.datumA).trans (max_comm _ _).le,
    S.isoEquiv hbij, fun x y hxy hx cx cy hc x' y' hxy' hx' rx ry hr φ' φ heq =>
      S.isoEquiv_restrict hbij x y hxy hx cx cy hc x' y' hxy' hx' rx ry hr φ' φ heq _⟩

end AlgebraicGeometry.PolarizedFamily

end
