module

public import StacksFrontier.AlgebraicGeometry.AffineGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackSpecGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackBaseAlgebra
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.SectionPullRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# The quasi-coherent graded algebra on `Spec R` attached to a graded `R`-algebra, and maps out of
its pullbacks

Let `B` be an `ℕ`-graded `R`-algebra with grading `𝒢`. Its associated sheaf `B̃` is a
quasi-coherent graded `𝒪_{Spec R}`-algebra in the sense of Situation 01NN
(`specSheafGradedAlgebra`). For a ring map `f : R ⟶ S`, a quasi-coherent graded
`𝒪_{Spec S}`-algebra `𝒜'` and a homomorphism of graded rings `p : B ⟶ Γ(Spec S, 𝒜')` compatible
with `f`, the adjoint transpose of `B̃ ⟶ (Spec f)_* 𝒜'` is a homomorphism of graded algebras
`(Spec f)^* B̃ ⟶ 𝒜'` (`specGradedHom`); it is an isomorphism in every degree when `p` exhibits
`Γ(Spec S, 𝒜'_d)` as `S ⊗_R B_d` for every `d`.

## Main definitions

* `Stacks.PolarizedAlgebraization.specSheafGradedAlgebra`: `B̃`.
* `Stacks.PolarizedAlgebraization.homogeneousSectionTop`: the global section of `B̃_k` named by a
  homogeneous element of degree `k`.
* `Stacks.PolarizedAlgebraization.globalSectionsHom`: `B ⟶ Γ(Spec R, B̃)`, a bijective
  homomorphism of graded rings.
* `Stacks.PolarizedAlgebraization.chiHom`: `B̃ ⟶ (Spec f)_* 𝒜'`, the homomorphism of graded
  algebras which is `p` on global sections; its degree-`k` piece is the transpose along the tilde
  adjunction of `chiLinear`, `b ↦ p(b)_k`.
* `Stacks.PolarizedAlgebraization.specGradedHom`: `(Spec f)^* B̃ ⟶ 𝒜'`, the adjoint transpose of
  `chiHom`.
* `Stacks.PolarizedAlgebraization.pieceBaseChangeMap`: `S ⊗_R B_k ⟶ Γ(Spec S, 𝒜'_k)`.

## Main results

* `Stacks.PolarizedAlgebraization.specGradedHom_app_unitApp`: `specGradedHom` carries the pullback
  of the section named by `b` to the degree-`k` component of `p b`.
* `Stacks.PolarizedAlgebraization.hom_ext_pullback_piece`: maps out of `(Spec f)^* B̃_k` are
  determined by their values on the pullbacks of the sections named by the elements of `B_k`.
* `Stacks.PolarizedAlgebraization.isIso_specGradedHom_app`: `specGradedHom` is an isomorphism in
  every degree when `S ⊗_R B_k ⟶ Γ(Spec S, 𝒜'_k)` is bijective for every `k`.

## Implementation notes

Multiplicativity of `chiHom` on all local sections is proved on the covering sieve of local
lifts along the comparison `𝒪(U) ⊗_R B_k ⟶ B̃_k` (`chiApp_map_mul`), where it reduces to the
multiplicativity of `p` (`chiApp_mul_pieceCmp`); this is the technique of
`Stacks.SpecGraded.specGradedAlgebra_mul_comm`. Isomorphy of `specGradedHom` goes through the
affine pullback comparison `(Spec f)^* M̃ ≅ (S ⊗_R M)~` of Tag 01I9 and the tilde adjunction:
on a quasi-coherent module over an affine scheme a map out of an associated sheaf is an
isomorphism as soon as its map on global sections is bijective.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.GradedProperCohomology (intExtend)
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.PolarizedAlgebraization

/-- The restriction of a module on `Spec S` from `⊤` to `(Spec f)⁻¹ ⊤ = ⊤` is the identity. -/
theorem map_le_top_preimage_top {R S : CommRingCat.{u}} (f : R ⟶ S) (M : (Spec S).Modules)
    (x : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE (le_top : (Spec.map f) ⁻¹ᵁ ⊤ ≤ ⊤)).op x = x :=
  (congrArg (fun φ : M.presheaf.obj (op ⊤) ⟶ M.presheaf.obj (op ⊤) => φ.hom x)
    (M.presheaf.map_id (op ⊤)) :)

/-- On global sections, `Spec f` carries the section named by `r` to the section named by
`f r`. -/
theorem app_top_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).app ⊤ ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) :=
  (congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- Additive maps out of a tensor product agreeing on pure tensors are equal. -/
private theorem addMonoidHom_ext_tmul {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] (F G : M ⊗[R] N →+ P)
    (h : ∀ (m : M) (n : N), F (m ⊗ₜ[R] n) = G (m ⊗ₜ[R] n)) : F = G := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m n => exact h m n

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒢 : ℕ → Submodule R B) [_root_.GradedAlgebra 𝒢]

include 𝒢

/-- **`B̃`, the quasi-coherent graded `𝒪_{Spec R}`-algebra attached to the graded `R`-algebra
`B`**: its degree-`n` piece is the associated sheaf of `B_n`, and of `0` in negative degrees. -/
def specSheafGradedAlgebra : SheafGradedAlgebra (Spec R) :=
  Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra
    (Stacks.SpecGraded.specGradedAlgebra (intExtend 𝒢))
    (fun i j U a b => Stacks.SpecGraded.specGradedAlgebra_mul_comm (intExtend 𝒢) i j U a b)
    (fun _ hn U x => (ModuleCat.subsingleton_of_isZero
      ((PresheafOfModules.evaluation _ U).map_isZero ((SheafOfModules.forget _).map_isZero
        (Stacks.SpecGraded.isZero_specGradedAlgebra_piece (intExtend 𝒢)
          (Stacks.AlgebraicGeometry.GradedProperCohomology.intExtend_neg 𝒢 hn))))).allEq x 0)
    (fun _ => inferInstance)

/-- The degree-`k` piece of `B̃` is the associated sheaf of `B_k`, on the nose. -/
theorem specSheafGradedAlgebra_piece (k : ℕ) :
    (specSheafGradedAlgebra 𝒢).piece (k : ℤ) = tilde (ModuleCat.of R (𝒢 k)) :=
  rfl

/-- The global section of `B̃_k` named by a homogeneous element of degree `k`. -/
def homogeneousSectionTop {k : ℕ} (b : 𝒢 k) :
    Γ((specSheafGradedAlgebra 𝒢).piece (k : ℤ), ⊤) :=
  (Stacks.SpecGraded.homogeneousSection (intExtend 𝒢) (k := (k : ℤ)) b).eval (op ⊤)

/-- The section named by `b` is the image of `b` under `M ⟶ Γ(Spec R, M̃)`. -/
theorem homogeneousSectionTop_eq {k : ℕ} (b : 𝒢 k) :
    homogeneousSectionTop 𝒢 b = tilde.toOpen (ModuleCat.of R (𝒢 k)) ⊤ b := by
  change (1 : Γ(Spec R, ⊤)) • Stacks.AffineBaseChange.toOpenₗ (ModuleCat.of R (𝒢 k)) ⊤ b = _
  exact one_smul _ _

/-- The section named by a sum is the sum of the sections. -/
theorem homogeneousSectionTop_add {k : ℕ} (b b' : 𝒢 k) :
    homogeneousSectionTop 𝒢 (b + b') = homogeneousSectionTop 𝒢 b + homogeneousSectionTop 𝒢 b' :=
  Stacks.SpecGraded.homogeneousSection_eval_add (intExtend 𝒢) (k := (k : ℤ)) b b' (op ⊤)

/-- The section named by a product is the product of the sections. -/
theorem homogeneousSectionTop_mul {i j : ℕ} (b : 𝒢 i) (b' : 𝒢 j) :
    homogeneousSectionTop 𝒢 (⟨(b : B) * b', SetLike.mul_mem_graded b.2 b'.2⟩ : 𝒢 (i + j)) =
      ((specSheafGradedAlgebra 𝒢).mul (i : ℤ) (j : ℤ)).app ⊤
        (homogeneousSectionTop 𝒢 b) (homogeneousSectionTop 𝒢 b') :=
  (Stacks.SpecGraded.castHom_homogeneousSection_mul (intExtend 𝒢) (i := (i : ℤ)) (j := (j : ℤ))
    (m := ((i + j : ℕ) : ℤ)) rfl b b' ⟨(b : B) * b', SetLike.mul_mem_graded b.2 b'.2⟩ rfl
    (op ⊤)).symm

/-- `B_k ⟶ Γ(Spec R, B̃_k)`, additively. -/
def globalSectionsPiece (k : ℕ) : 𝒢 k →+ (specSheafGradedAlgebra 𝒢).sectionPieces ⊤ k :=
  AddMonoidHom.mk' (fun b => homogeneousSectionTop 𝒢 b) (homogeneousSectionTop_add 𝒢)

/-- `B_k ⟶ Γ(Spec R, B̃_k)` is bijective. -/
theorem bijective_globalSectionsPiece (k : ℕ) :
    Function.Bijective (globalSectionsPiece 𝒢 k) := by
  have h : Function.Bijective (tilde.toOpen (ModuleCat.of R (𝒢 k)) ⊤) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  refine ⟨fun x y hxy => h.1 ?_, fun z => ?_⟩
  · have e : homogeneousSectionTop 𝒢 x = homogeneousSectionTop 𝒢 y := hxy
    rwa [homogeneousSectionTop_eq, homogeneousSectionTop_eq] at e
  · obtain ⟨b, hb⟩ := h.2 z
    exact ⟨b, (homogeneousSectionTop_eq 𝒢 b).trans hb⟩

/-- `⨁ B_k ⟶ Γ(Spec R, B̃)` as a ring homomorphism. -/
def globalSectionsDirectSumHom :
    DirectSum ℕ (fun k => 𝒢 k) →+* (specSheafGradedAlgebra 𝒢).sectionRing ⊤ :=
  DirectSum.toSemiring (fun k => (DirectSum.of _ k).comp (globalSectionsPiece 𝒢 k))
      (by
        refine (congrArg (DirectSum.of ((specSheafGradedAlgebra 𝒢).sectionPieces ⊤) 0) ?_).trans
          (DirectSum.one_def _).symm
        exact congrArg (fun z => z.eval (op ⊤))
          (Stacks.SpecGraded.homogeneousSection_gOne (intExtend 𝒢)))
      (fun {i j} a b => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply]
        rw [DirectSum.of_mul_of]
        exact congrArg (DirectSum.of ((specSheafGradedAlgebra 𝒢).sectionPieces ⊤) (i + j))
          (homogeneousSectionTop_mul 𝒢 a b))

/-- `B ⟶ Γ(Spec R, B̃)` as a ring homomorphism. -/
def globalSectionsRingHom : B →+* (specSheafGradedAlgebra 𝒢).sectionRing ⊤ :=
  (globalSectionsDirectSumHom 𝒢).comp (DirectSum.decomposeRingEquiv 𝒢).toRingHom

/-- `B ⟶ Γ(Spec R, B̃)` sends a homogeneous element of degree `k` to the section it names, in
degree `k`. -/
theorem globalSectionsRingHom_of {k : ℕ} (b : 𝒢 k) :
    globalSectionsRingHom 𝒢 (b : B) =
      DirectSum.of ((specSheafGradedAlgebra 𝒢).sectionPieces ⊤) k (homogeneousSectionTop 𝒢 b) := by
  change globalSectionsDirectSumHom 𝒢 (DirectSum.decompose 𝒢 (b : B)) = _
  rw [DirectSum.decompose_coe, globalSectionsDirectSumHom, DirectSum.toSemiring_of]
  rfl

/-- **`B ⟶ Γ(Spec R, B̃)`**, the homomorphism of graded rings sending a homogeneous `b` to the
global section it names. -/
def globalSectionsHom : 𝒢 →+*ᵍ (specSheafGradedAlgebra 𝒢).grading ⊤ where
  __ := globalSectionsRingHom 𝒢
  map_mem := fun {i x} hx => by
    rw [show x = ((⟨x, hx⟩ : 𝒢 i) : B) from rfl, globalSectionsRingHom_of]
    exact ⟨_, rfl⟩

/-- `globalSectionsHom` sends a homogeneous element of degree `k` to the section it names, in
degree `k`. -/
theorem globalSectionsHom_of {k : ℕ} (b : 𝒢 k) :
    globalSectionsHom 𝒢 (b : B) =
      DirectSum.of ((specSheafGradedAlgebra 𝒢).sectionPieces ⊤) k (homogeneousSectionTop 𝒢 b) :=
  globalSectionsRingHom_of 𝒢 b

/-- `B ⟶ Γ(Spec R, B̃)` is bijective. -/
theorem bijective_globalSectionsHom : Function.Bijective (globalSectionsHom 𝒢) := by
  have hmap : ⇑(globalSectionsDirectSumHom 𝒢) = ⇑(DirectSum.map (globalSectionsPiece 𝒢)) := by
    have : (globalSectionsDirectSumHom 𝒢).toAddMonoidHom = DirectSum.map (globalSectionsPiece 𝒢) :=
      DirectSum.addHom_ext fun k b => by
        rw [DirectSum.map_of]
        change globalSectionsDirectSumHom 𝒢 (DirectSum.of (fun k => 𝒢 k) k b) = _
        rw [globalSectionsDirectSumHom, DirectSum.toSemiring_of]
        rfl
    exact congrArg DFunLike.coe this
  have hb : Function.Bijective (DirectSum.map (globalSectionsPiece 𝒢)) :=
    ⟨(DirectSum.map_injective _).mpr fun k => (bijective_globalSectionsPiece 𝒢 k).1,
      (DirectSum.map_surjective _).mpr fun k => (bijective_globalSectionsPiece 𝒢 k).2⟩
  change Function.Bijective (globalSectionsDirectSumHom 𝒢 ∘ DirectSum.decompose 𝒢)
  rw [hmap]
  exact hb.comp (DirectSum.decomposeRingEquiv 𝒢).bijective

/-- `B ⟶ Γ(Spec R, B̃)` is compatible with the structure maps. -/
theorem globalSectionsHom_algebraMap (r : R) :
    globalSectionsHom 𝒢 (algebraMap R B r) =
      (specSheafGradedAlgebra 𝒢).strHom ⊤ ((Scheme.ΓSpecIso R).inv r) := by
  have e : algebraMap R B r =
      ((r • Stacks.SpecGraded.gOne (intExtend 𝒢) : intExtend 𝒢 ((0 : ℕ) : ℤ)) : B) := by
    rw [Submodule.coe_smul, Algebra.algebraMap_eq_smul_one]
    rfl
  rw [e]
  refine (globalSectionsHom_of 𝒢 (k := 0) _).trans ?_
  rw [SheafGradedAlgebra.strHom_apply]
  exact congrArg (DirectSum.of ((specSheafGradedAlgebra 𝒢).sectionPieces ⊤) 0)
    (Stacks.SpecGraded.homogeneousSection_smul_gOne (intExtend 𝒢) r)

section Chi

variable {S : CommRingCat.{u}} (f : R ⟶ S) (A' : SheafGradedAlgebra (Spec S))

/-- The value of the degree-`k` map `B_k ⟶ Γ(Spec R, (Spec f)_* 𝒜'_k)`: the degree-`k` component
of `p b`. -/
def chiValue (p : 𝒢 →+*ᵍ A'.grading ⊤) (k : ℕ) (b : 𝒢 k) :
    Γ(A'.piece (k : ℤ), (Spec.map f) ⁻¹ᵁ ⊤) :=
  (A'.piece (k : ℤ)).presheaf.map (homOfLE le_top).op ((p (b : B) : A'.sectionRing ⊤) k)

omit [_root_.GradedAlgebra 𝒢] in
/-- `chiValue` is additive. -/
theorem chiValue_add (p : 𝒢 →+*ᵍ A'.grading ⊤) (k : ℕ) (b b' : 𝒢 k) :
    chiValue 𝒢 f A' p k (b + b') = chiValue 𝒢 f A' p k b + chiValue 𝒢 f A' p k b' := by
  simp only [chiValue, Submodule.coe_add, map_add, DirectSum.add_apply]

omit [_root_.GradedAlgebra 𝒢] in
/-- `chiValue` is `R`-linear, `R` acting on the target through `Spec f`. -/
theorem chiValue_smul (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (k : ℕ) (r : R) (b : 𝒢 k) :
    chiValue 𝒢 f A' p k (r • b) =
      (Spec.map f).app ⊤ ((Scheme.ΓSpecIso R).inv r) • chiValue 𝒢 f A' p k b := by
  have e : p ((r • b : 𝒢 k) : B) =
      A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)) * p (b : B) := by
    rw [Submodule.coe_smul, Algebra.smul_def r (b : B), map_mul, hp]
  rw [chiValue, e, SheafGradedAlgebra.strHom_mul_apply, Scheme.Modules.map_smul,
    app_top_ΓSpecIso_inv]
  congr 1

/-- **The degree-`k` map `B_k ⟶ Γ(Spec R, (Spec f)_* 𝒜'_k)`**, `b ↦ p(b)_k`, as a morphism of
`R`-modules. -/
def chiLinear (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (k : ℕ) :
    ModuleCat.of R (𝒢 k) ⟶
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj (A'.piece (k : ℤ))) :=
  ConcreteCategory.ofHom (C := ModuleCat R) (show ModuleCat.of R (𝒢 k) →ₗ[R] (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (Spec.map f)).obj (A'.piece (k : ℤ))) : ModuleCat R) from
    { toFun := chiValue 𝒢 f A' p k
      map_add' := chiValue_add 𝒢 f A' p k
      map_smul' := fun r b => (chiValue_smul 𝒢 f A' p hp k r b).trans rfl })

/-- **The degree-`n` component of `B̃ ⟶ (Spec f)_* 𝒜'`**: the adjoint transpose of `chiLinear` in
degrees `n ≥ 0`, and zero in negative degrees, where `B̃` vanishes. -/
def chiApp (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r))) :
    ∀ n : ℤ, (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
        (specSheafGradedAlgebra 𝒢)).piece n ⟶
      (Stacks.RingedSpace.pushforwardAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')).piece n
  | Int.ofNat k => (tilde.adjunction.homEquiv _ _).symm (chiLinear 𝒢 f A' p hp k)
  | Int.negSucc _ => 0

/-- The degree-`k` component of `chiApp` carries the section of `B̃_k` named by `b` over `U` to
the restriction of `p(b)_k`. -/
theorem chiApp_toOpen (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (k : ℕ) (U : (Spec R).Opens) (b : 𝒢 k) :
    (chiApp 𝒢 f A' p hp (k : ℤ)).val.app (op U) (tilde.toOpen (ModuleCat.of R (𝒢 k)) U b) =
      (A'.piece (k : ℤ)).presheaf.map (homOfLE (le_top : (Spec.map f) ⁻¹ᵁ U ≤ ⊤)).op
        ((p (b : B) : A'.sectionRing ⊤) k) := by
  have h1 := ConcreteCategory.congr_hom (tilde.toOpen_map_app (chiLinear 𝒢 f A' p hp k) U) b
  have h2 := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app
    ((Scheme.Modules.pushforward (Spec.map f)).obj (A'.piece (k : ℤ))) U) (chiValue 𝒢 f A' p k b)
  change (Scheme.Modules.fromTildeΓ _).val.app (op U)
    ((tilde.map (chiLinear 𝒢 f A' p hp k)).val.app (op U)
      (tilde.toOpen (ModuleCat.of R (𝒢 k)) U b)) = _
  refine (congrArg _ h1).trans ?_
  refine h2.trans ?_
  exact (ConcreteCategory.congr_hom ((A'.piece (k : ℤ)).presheaf.map_comp
    (homOfLE (le_top : (Spec.map f) ⁻¹ᵁ ⊤ ≤ ⊤)).op
    (homOfLE ((Spec.map f).preimage_mono (le_top : U ≤ ⊤))).op).symm
    ((p (b : B) : A'.sectionRing ⊤) k) :)

/-- The degree-`k` component of `chiApp` carries the local section `a ⊗ b` of `B̃_k` to
`a • p(b)_k`. -/
theorem chiApp_pieceCmp (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (k : ℕ) (U : (Spec R).Opens) (a : Γ(Spec R, U)) (b : 𝒢 k) :
    (chiApp 𝒢 f A' p hp (k : ℤ)).val.app (op U)
        ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (k : ℤ)).app (op U) (a ⊗ₜ[R] b)) =
      (Spec.map f).app U a • (A'.piece (k : ℤ)).presheaf.map
        (homOfLE (le_top : (Spec.map f) ⁻¹ᵁ U ≤ ⊤)).op ((p (b : B) : A'.sectionRing ⊤) k) := by
  have e : (Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (k : ℤ)).app (op U) (a ⊗ₜ[R] b) =
      a • Stacks.AffineBaseChange.toOpenₗ (ModuleCat.of R (𝒢 k)) U b := rfl
  rw [e]
  refine (((chiApp 𝒢 f A' p hp (k : ℤ)).val.app (op U)).hom.map_smul a _).trans ?_
  exact (congrArg (fun z : Γ(A'.piece (k : ℤ), (Spec.map f) ⁻¹ᵁ U) => (Spec.map f).app U a • z)
    (chiApp_toOpen 𝒢 f A' p hp k U b) :)

omit [_root_.GradedAlgebra 𝒢] in
include 𝒢 in
/-- The degree-`(m + n)` component of a product of homogeneous elements of degrees `m`, `n` under
a homomorphism of graded rings into the sections of `𝒜'` is the product of the components. -/
theorem mul_component (p : 𝒢 →+*ᵍ A'.grading ⊤) {m n : ℕ} (b : 𝒢 m) (b' : 𝒢 n) :
    ((p ((b : B) * b') : A'.sectionRing ⊤) (m + n)) =
      (A'.mul (m : ℤ) (n : ℤ)).app ⊤ ((p (b : B) : A'.sectionRing ⊤) m)
        ((p (b' : B) : A'.sectionRing ⊤) n) := by
  obtain ⟨y, hy⟩ := p.map_mem b.2
  obtain ⟨y', hy'⟩ := p.map_mem b'.2
  replace hy : DirectSum.of (A'.sectionPieces ⊤) m y = p (b : B) := hy
  replace hy' : DirectSum.of (A'.sectionPieces ⊤) n y' = p (b' : B) := hy'
  rw [map_mul, ← hy, ← hy', DirectSum.of_mul_of, DirectSum.of_eq_same, DirectSum.of_eq_same,
    DirectSum.of_eq_same]
  rfl

/-- The degree-`(m + n)` component on the comparison image of a product of base-changed local
sections is the product of the degree-`m` and degree-`n` components. -/
theorem chiApp_mul_pieceCmp (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (m n : ℕ) (Y : (Spec R).Opens)
    (x₀ : Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (m : ℤ)) (y₀ : Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (n : ℤ)) :
    (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y)
        ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) ((m : ℤ) + (n : ℤ))).app (op Y)
          (Stacks.SpecGraded.mulSec (intExtend 𝒢) (op Y) (m : ℤ) (n : ℤ) x₀ y₀)) =
      (A'.mul (m : ℤ) (n : ℤ)).app ((Spec.map f) ⁻¹ᵁ Y)
        ((chiApp 𝒢 f A' p hp (m : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)).app (op Y) x₀))
        ((chiApp 𝒢 f A' p hp (n : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)).app (op Y) y₀)) := by
  -- the left side as an additive function of `x₀`, for a fixed `y`
  let F₁ : (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (n : ℤ)) →
      (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (m : ℤ)) →+
        Γ(A'.piece ((m : ℤ) + (n : ℤ)), (Spec.map f) ⁻¹ᵁ Y) :=
    fun y => ((chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y)).hom.toAddMonoidHom.comp
      (((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) ((m : ℤ) + (n : ℤ))).app
        (op Y)).hom.toAddMonoidHom.comp
        ((Stacks.SpecGraded.mulSec (intExtend 𝒢) (op Y) (m : ℤ) (n : ℤ)).flip y).toAddMonoidHom)
  let F₂ : (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (n : ℤ)) →
      (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (m : ℤ)) →+
        Γ(A'.piece ((m : ℤ) + (n : ℤ)), (Spec.map f) ⁻¹ᵁ Y) :=
    fun y => (AddMonoidHom.flip ((A'.mul (m : ℤ) (n : ℤ)).app ((Spec.map f) ⁻¹ᵁ Y))
        ((chiApp 𝒢 f A' p hp (n : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)).app (op Y) y))).comp
      (((chiApp 𝒢 f A' p hp (m : ℤ)).val.app (op Y)).hom.toAddMonoidHom.comp
        ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)).app (op Y)).hom.toAddMonoidHom)
  -- the right side as an additive function of `y₀`, for a fixed pure tensor `x`
  let G₁ : (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (m : ℤ)) →
      (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (n : ℤ)) →+
        Γ(A'.piece ((m : ℤ) + (n : ℤ)), (Spec.map f) ⁻¹ᵁ Y) :=
    fun x => ((chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y)).hom.toAddMonoidHom.comp
      (((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) ((m : ℤ) + (n : ℤ))).app
        (op Y)).hom.toAddMonoidHom.comp
        (Stacks.SpecGraded.mulSec (intExtend 𝒢) (op Y) (m : ℤ) (n : ℤ) x).toAddMonoidHom)
  let G₂ : (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (m : ℤ)) →
      (Γ(Spec R, Y) ⊗[R] intExtend 𝒢 (n : ℤ)) →+
        Γ(A'.piece ((m : ℤ) + (n : ℤ)), (Spec.map f) ⁻¹ᵁ Y) :=
    fun x => ((A'.mul (m : ℤ) (n : ℤ)).app ((Spec.map f) ⁻¹ᵁ Y)
        ((chiApp 𝒢 f A' p hp (m : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)).app (op Y) x))).comp
      (((chiApp 𝒢 f A' p hp (n : ℤ)).val.app (op Y)).hom.toAddMonoidHom.comp
        ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)).app (op Y)).hom.toAddMonoidHom)
  have key : ∀ (s t : Γ(Spec R, Y)) (b : 𝒢 m) (b' : 𝒢 n),
      G₁ (s ⊗ₜ[R] b) (t ⊗ₜ[R] b') = G₂ (s ⊗ₜ[R] b) (t ⊗ₜ[R] b') := by
    intro s t b b'
    change (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y)
        ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) ((m : ℤ) + (n : ℤ))).app (op Y)
          (Stacks.SpecGraded.mulSec (intExtend 𝒢) (op Y) (m : ℤ) (n : ℤ) (s ⊗ₜ[R] b)
            (t ⊗ₜ[R] b'))) =
      (A'.mul (m : ℤ) (n : ℤ)).app ((Spec.map f) ⁻¹ᵁ Y)
        ((chiApp 𝒢 f A' p hp (m : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)).app (op Y) (s ⊗ₜ[R] b)))
        ((chiApp 𝒢 f A' p hp (n : ℤ)).val.app (op Y)
          ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)).app (op Y) (t ⊗ₜ[R] b')))
    refine (congrArg (fun z => (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y)
      ((Stacks.SpecGraded.pieceCmp (intExtend 𝒢) ((m : ℤ) + (n : ℤ))).app (op Y) z))
      (Stacks.SpecGraded.mulSec_tmul (intExtend 𝒢) (op Y) (m : ℤ) (n : ℤ) s t b b')).trans ?_
    refine (chiApp_pieceCmp 𝒢 f A' p hp (m + n) Y (s * t)
      ⟨(b : B) * b', SetLike.mul_mem_graded b.2 b'.2⟩).trans ?_
    rw [chiApp_pieceCmp 𝒢 f A' p hp m Y s b, chiApp_pieceCmp 𝒢 f A' p hp n Y t b',
      (A'.mul (m : ℤ) (n : ℤ)).map_smul_left, (A'.mul (m : ℤ) (n : ℤ)).map_smul_right,
      ← (A'.mul (m : ℤ) (n : ℤ)).naturality, ← mul_component, map_mul, mul_smul]
    rfl
  have hG : ∀ (s : Γ(Spec R, Y)) (b : 𝒢 m), G₁ (s ⊗ₜ[R] b) = G₂ (s ⊗ₜ[R] b) := fun s b =>
    addMonoidHom_ext_tmul _ _ fun t b' => key s t b b'
  have hF : F₁ y₀ = F₂ y₀ :=
    addMonoidHom_ext_tmul _ _ fun s b => DFunLike.congr_fun (hG s b) y₀
  exact DFunLike.congr_fun hF x₀

/-- The local sections of a negative-degree piece of `B̃` vanish. -/
theorem situationAlgebra_section_eq_zero {n : ℤ} (hn : n < 0) (U : ((Spec R).Opens)ᵒᵖ)
    (x : ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
      (specSheafGradedAlgebra 𝒢)).piece n).val.obj U) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero
      ((PresheafOfModules.evaluation _ U).map_isZero ((SheafOfModules.forget _).map_isZero
        (Stacks.SpecGraded.isZero_specGradedAlgebra_piece (intExtend 𝒢)
          (Stacks.AlgebraicGeometry.GradedProperCohomology.intExtend_neg 𝒢 hn))))).allEq x 0

/-- `chiApp` is multiplicative on local sections. -/
theorem chiApp_map_mul (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
      (specSheafGradedAlgebra 𝒢)).piece i).val.obj U)
    (y : ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
      (specSheafGradedAlgebra 𝒢)).piece j).val.obj U) :
    (chiApp 𝒢 f A' p hp (i + j)).val.app U
        (((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
          (specSheafGradedAlgebra 𝒢)).mul i j).app U x y) =
      ((Stacks.RingedSpace.pushforwardAlgebra
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')).mul i j).app U
        ((chiApp 𝒢 f A' p hp i).val.app U x) ((chiApp 𝒢 f A' p hp j).val.app U y) := by
  obtain ⟨U⟩ := U
  rcases i with m | m
  · rcases j with n | n
    · change (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op U) _ = _
      refine Stacks.eq_of_isSeparated _
        ((Opens.grothendieckTopology ↥(Spec R)).intersection_covering
          (Stacks.cmpSieve_mem (Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)) x)
          (Stacks.cmpSieve_mem (Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)) y)) ?_
      rintro Y g ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
      have hx : PresheafOfModules.Hom.app (Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (m : ℤ)) (op Y)
          x₀ = (Stacks.SpecGraded.pieceSheaf (intExtend 𝒢) (m : ℤ)).val.map g.op x := hx₀
      have hy : PresheafOfModules.Hom.app (Stacks.SpecGraded.pieceCmp (intExtend 𝒢) (n : ℤ)) (op Y)
          y₀ = (Stacks.SpecGraded.pieceSheaf (intExtend 𝒢) (n : ℤ)).val.map g.op y := hy₀
      have hL := (Stacks.SpecGraded.presheafAlgebra (intExtend 𝒢)).ofComparison_mul_restrict
        (Stacks.SpecGraded.pieceSheaf (intExtend 𝒢)) (Stacks.SpecGraded.pieceCmp (intExtend 𝒢))
        (m : ℤ) (n : ℤ) g.op x y x₀ y₀ hx hy
      refine ((PresheafOfModules.naturality_apply
        (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val g.op _).symm.trans ?_)
      refine (congrArg (fun z => (chiApp 𝒢 f A' p hp ((m : ℤ) + (n : ℤ))).val.app (op Y) z)
        hL).trans ?_
      refine (chiApp_mul_pieceCmp 𝒢 f A' p hp m n Y x₀ y₀).trans ?_
      refine Eq.trans ?_ (((Stacks.RingedSpace.pushforwardAlgebra
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')).mul
            (m : ℤ) (n : ℤ)).naturality g.op _ _).symm
      exact congrArg₂ (fun a b => ((Stacks.RingedSpace.pushforwardAlgebra
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')).mul
            (m : ℤ) (n : ℤ)).app (op Y) a b)
        ((congrArg (fun z => (chiApp 𝒢 f A' p hp (m : ℤ)).val.app (op Y) z) hx).trans
          (PresheafOfModules.naturality_apply (chiApp 𝒢 f A' p hp (m : ℤ)).val g.op x))
        ((congrArg (fun z => (chiApp 𝒢 f A' p hp (n : ℤ)).val.app (op Y) z) hy).trans
          (PresheafOfModules.naturality_apply (chiApp 𝒢 f A' p hp (n : ℤ)).val g.op y))
    · obtain rfl := situationAlgebra_section_eq_zero 𝒢 (Int.negSucc_lt_zero n) (op U) y
      rw [map_zero, map_zero, map_zero, map_zero]
  · obtain rfl := situationAlgebra_section_eq_zero 𝒢 (Int.negSucc_lt_zero m) (op U) x
    rw [map_zero, AddMonoidHom.zero_apply, map_zero, map_zero, map_zero, AddMonoidHom.zero_apply]

/-- `chiApp` preserves the unit section. -/
theorem chiApp_map_one (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (U : ((Spec R).Opens)ᵒᵖ) :
    (chiApp 𝒢 f A' p hp 0).val.app U
        ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
          (specSheafGradedAlgebra 𝒢)).one.eval U) =
      (Stacks.RingedSpace.pushforwardAlgebra
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')).one.eval U := by
  obtain ⟨U⟩ := U
  refine (chiApp_pieceCmp 𝒢 f A' p hp 0 U 1 ⟨1, SetLike.GradedOne.one_mem⟩).trans ?_
  have e : ((p ((⟨1, SetLike.GradedOne.one_mem⟩ : 𝒢 0) : B) : A'.sectionRing ⊤) 0) = A'.one ⊤ := by
    change ((p 1 : A'.sectionRing ⊤) 0) = _
    rw [map_one, DirectSum.one_def, DirectSum.of_eq_same]
    rfl
  rw [map_one, one_smul, e]
  exact A'.one_res _

/-- **`B̃ ⟶ (Spec f)_* 𝒜'`**, the homomorphism of graded algebras which is `p` on global
sections. -/
def chiHom (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r))) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra (specSheafGradedAlgebra 𝒢))
      (Stacks.RingedSpace.pushforwardAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra A')) where
  app := chiApp 𝒢 f A' p hp
  map_mul := chiApp_map_mul 𝒢 f A' p hp
  map_one := chiApp_map_one 𝒢 f A' p hp

omit [_root_.GradedAlgebra 𝒢] in
/-- The degree-`k` component of `p (r • b)` is `r • p(b)_k`, `R` acting through `f`. -/
theorem smul_component (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    {k : ℕ} (r : R) (b : 𝒢 k) :
    ((p ((r • b : 𝒢 k) : B) : A'.sectionRing ⊤) k) =
      (Scheme.ΓSpecIso S).inv (f r) • ((p (b : B) : A'.sectionRing ⊤) k) := by
  rw [Submodule.coe_smul, Algebra.smul_def r (b : B), map_mul, hp,
    SheafGradedAlgebra.strHom_mul_apply]

end Chi

variable {S : CommRingCat.{u}} (f : R ⟶ S) (A' : SheafGradedAlgebra (Spec S))
  (p : 𝒢 →+*ᵍ A'.grading ⊤)
  (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))

include f A' p hp

/-- **The homomorphism `(Spec f)^* B̃ ⟶ 𝒜'` attached to `p : B ⟶ Γ(Spec S, 𝒜')`**: the adjoint
transpose of the homomorphism `B̃ ⟶ (Spec f)_* 𝒜'` which is `p` on global sections. -/
def specGradedHom (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r))) :
    SheafGradedAlgebraHom ((specSheafGradedAlgebra 𝒢).pullback (Spec.map f)) A' where
  app n := (Stacks.RingedSpace.transposeUnitalHom
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
    (chiHom 𝒢 f A' p hp)).app n
  app_mul i j U a b := (Stacks.RingedSpace.transposeUnitalHom
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
    (chiHom 𝒢 f A' p hp)).map_mul i j (op U) a b
  app_one U := (Stacks.RingedSpace.transposeUnitalHom
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
    (chiHom 𝒢 f A' p hp)).map_one (op U)

/-- `specGradedHom` carries the pullback of the section named by `b` to the degree-`k` component
of `p b`. -/
theorem specGradedHom_app_unitApp (k : ℕ) (b : 𝒢 k) :
    ((specGradedHom 𝒢 f A' p hp).app (k : ℤ)).app ((Spec.map f) ⁻¹ᵁ ⊤)
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp (Spec.map f)
          ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⊤ (homogeneousSectionTop 𝒢 b)) =
      (A'.piece (k : ℤ)).presheaf.map (homOfLE le_top).op ((p (b : B) : A'.sectionRing ⊤) k) := by
  refine (Stacks.RingedSpace.transposeApp_pullbackUnit
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom (Spec.map f))
    (chiHom 𝒢 f A' p hp) (k : ℤ) ⊤ (homogeneousSectionTop 𝒢 b)).trans ?_
  rw [show homogeneousSectionTop 𝒢 b = _ from homogeneousSectionTop_eq 𝒢 b]
  exact chiApp_toOpen 𝒢 f A' p hp k ⊤ b

omit A' p hp in
/-- **Maps out of `(Spec f)^* B̃_k` are determined by the pullbacks of the sections named by the
elements of `B_k`.** -/
theorem hom_ext_pullback_piece (k : ℕ) {F : (Spec S).Modules}
    (φ₁ φ₂ : (Scheme.Modules.pullback (Spec.map f)).obj
      ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⟶ F)
    (h : ∀ b : 𝒢 k,
      φ₁.app ((Spec.map f) ⁻¹ᵁ ⊤)
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp (Spec.map f)
            ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⊤ (homogeneousSectionTop 𝒢 b)) =
        φ₂.app ((Spec.map f) ⁻¹ᵁ ⊤)
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp (Spec.map f)
            ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⊤ (homogeneousSectionTop 𝒢 b))) :
    φ₁ = φ₂ := by
  have e : ∀ (φ : (Scheme.Modules.pullback (Spec.map f)).obj
      ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⟶ F) (b : 𝒢 k),
      (tilde.adjunction.homEquiv (ModuleCat.of R (𝒢 k)) _
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _ φ)).hom b =
      φ.app ((Spec.map f) ⁻¹ᵁ ⊤)
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp (Spec.map f)
          ((specSheafGradedAlgebra 𝒢).piece (k : ℤ)) ⊤ (homogeneousSectionTop 𝒢 b)) := by
    intro φ b
    rw [homogeneousSectionTop_eq, Adjunction.homEquiv_unit]
    exact (congrArg (fun ψ : (specSheafGradedAlgebra 𝒢).piece (k : ℤ) ⟶
        (Scheme.Modules.pushforward (Spec.map f)).obj F =>
          ψ.app ⊤ (tilde.toOpen (ModuleCat.of R (𝒢 k)) ⊤ b))
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv_unit _ _ φ) :)
  refine ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _).injective ?_
  refine (tilde.adjunction.homEquiv (ModuleCat.of R (𝒢 k)) _).injective ?_
  ext b
  exact (e φ₁ b).trans ((h b).trans (e φ₂ b).symm)

/-- The degree-`k` comparison `S ⊗_R B_k ⟶ Γ(Spec S, 𝒜'_k)`, `s ⊗ b ↦ s • p(b)_k`, additively. -/
def pieceBaseChangeMap (p : 𝒢 →+*ᵍ A'.grading ⊤)
    (hp : ∀ r : R, p (algebraMap R B r) = A'.strHom ⊤ ((Scheme.ΓSpecIso S).inv (f r)))
    (k : ℕ) :
    letI := f.hom.toAlgebra
    S ⊗[R] 𝒢 k →+ Γ(A'.piece (k : ℤ), ⊤) :=
  letI := f.hom.toAlgebra
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s : S => AddMonoidHom.mk' (fun b : 𝒢 k =>
        ((Scheme.ΓSpecIso S).inv s • ((p (b : B) : A'.sectionRing ⊤) k) :
          Γ(A'.piece (k : ℤ), ⊤)))
        (fun b b' => by simp only [Submodule.coe_add, map_add, DirectSum.add_apply, smul_add]))
      (fun s s' => by
        ext b
        simp only [map_add, add_smul, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]))
    (fun r s b => by
      simp only [AddMonoidHom.mk'_apply]
      rw [smul_component 𝒢 f A' p hp, Algebra.smul_def, map_mul, mul_smul]
      exact smul_comm _ _ _)

/-- **`specGradedHom` is an isomorphism in every degree** when, for every `k`, the comparison
`S ⊗_R B_k ⟶ Γ(Spec S, 𝒜'_k)` is bijective. -/
theorem isIso_specGradedHom_app
    (hbij : ∀ k : ℕ, Function.Bijective (pieceBaseChangeMap 𝒢 f A' p hp k)) (k : ℤ) :
    IsIso ((specGradedHom 𝒢 f A' p hp).app k) := by
  rcases k with m | m
  · let M := ModuleCat.of R (𝒢 m)
    let e := (AlgebraicGeometry.pullbackTildeIso R S f).app M
    let ψ : tilde ((ModuleCat.extendScalars f.hom).obj M) ⟶ A'.piece (m : ℤ) :=
      e.inv ≫ (specGradedHom 𝒢 f A' p hp).app (m : ℤ)
    let φ := tilde.adjunction.homEquiv _ _ ψ
    have hφx : ∀ b : 𝒢 m, φ.hom ((1 : S) ⊗ₜ[R, f.hom] b) = ((p (b : B) : A'.sectionRing ⊤) m) := by
      intro b
      have h2 := Stacks.SheafOfModules.inv_val_app_hom_val_app e (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app
          (tilde M)).val.app (op ⊤) (tilde.toOpen M ⊤ b))
      have h3 := specGradedHom_app_unitApp 𝒢 f A' p hp m b
      rw [homogeneousSectionTop_eq, map_le_top_preimage_top] at h3
      change ((specGradedHom 𝒢 f A' p hp).app (m : ℤ)).val.app (op ⊤)
        (e.inv.val.app (op ⊤) (tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
          ((1 : S) ⊗ₜ[R, f.hom] b))) = _
      rw [← AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen R S f M b]
      exact (congrArg (fun z => ((specGradedHom 𝒢 f A' p hp).app (m : ℤ)).val.app (op ⊤) z)
        h2).trans h3
    have heq : ∀ x : (let := f.hom.toAlgebra; S ⊗[R] 𝒢 m),
        φ.hom x = pieceBaseChangeMap 𝒢 f A' p hp m x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        exact (map_add φ.hom x y).trans ((congrArg₂ (· + ·) hx hy).trans
          (map_add (pieceBaseChangeMap 𝒢 f A' p hp m) x y).symm)
      | tmul s b =>
        have e1 := (ModuleCat.ExtendScalars.smul_tmul f.hom (M := M) s 1 b).symm
        rw [mul_one] at e1
        refine (congrArg φ.hom e1).trans ?_
        refine (φ.hom.map_smul s _).trans ?_
        rw [hφx]
        rfl
    have hφ : IsIso φ := by
      rw [ConcreteCategory.isIso_iff_bijective]
      have h := hbij m
      rwa [← show (fun x => φ.hom x) = ⇑(pieceBaseChangeMap 𝒢 f A' p hp m) from funext heq] at h
    have hψ : IsIso ψ := by
      have h : ψ = (tilde.adjunction.homEquiv _ _).symm φ := (Equiv.symm_apply_apply _ _).symm
      rw [h, Adjunction.homEquiv_counit]
      change IsIso (tilde.map φ ≫ Scheme.Modules.fromTildeΓ (A'.piece (m : ℤ)))
      have i1 : IsIso (tilde.map φ) := (tilde.functor S).map_isIso φ
      have : (A'.piece (m : ℤ)).IsQuasicoherent := A'.isQuasicoherent _
      have i2 := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (A'.piece (m : ℤ))
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ e.inv _ _ hψ
  · have h0 : IsZero (A'.piece (Int.negSucc m)) := A'.negative_isZero _ (Int.negSucc_lt_zero m)
    have h1 : IsZero ((specSheafGradedAlgebra 𝒢).piece (Int.negSucc m)) :=
      (specSheafGradedAlgebra 𝒢).negative_isZero _ (Int.negSucc_lt_zero m)
    have h2 : IsZero ((Scheme.Modules.pullback (Spec.map f)).obj
        ((specSheafGradedAlgebra 𝒢).piece (Int.negSucc m))) :=
      (Scheme.Modules.pullback (Spec.map f)).map_isZero h1
    exact ⟨⟨h0.to_ _, h2.eq_of_src _ _, h0.eq_of_src _ _⟩⟩

end Stacks.PolarizedAlgebraization

end
