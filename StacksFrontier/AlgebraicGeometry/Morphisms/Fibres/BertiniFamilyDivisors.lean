module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Families of divisors cut out by a linear system

A finite dimensional space `V` of sections of an invertible module `L` on a scheme `X` over a
field `k` cuts out a family of divisors on `X`. Taking the coordinates with respect to a basis
`v₁, …, v_r` of `V` as parameters, the family is the zero scheme of one *universal section* on
the relative affine space `𝔸^r_X = 𝔸^r_k ×_k X`, and the divisor attached to a vector of
`V ⊗_k k'` is the fibre of that universal divisor over the corresponding `k'`-point of `𝔸^r_k`.
This is the standing situation of the Bertini theorems.

## Main definitions

* `Stacks.Bertini.globalSections` is `Γ(X, L)` as a `k`-vector space, for `X` a scheme over `k`.
* `Stacks.Bertini.FamilyDivisors` is the standing situation: a field, a scheme over it, an
  invertible module, a finite dimensional linear system of its sections, and a basis.
* `Stacks.Bertini.FamilyDivisors.universalSection` is `s_univ = Σᵢ xᵢ ψ(vᵢ)`, a section of
  `pr₂^* L` on `𝔸^r_X`, and `Stacks.Bertini.FamilyDivisors.universalDivisor` is its zero
  scheme `H_univ = Z(s_univ)`.
* `Stacks.Bertini.FamilyDivisors.specializedSection` is `ψ(v) = Σᵢ aᵢ ψ(vᵢ)` on `X_{k'}` and
  `Stacks.Bertini.FamilyDivisors.specializedDivisor` is `H_v = Z(ψ(v))`.
* `Stacks.Bertini.FamilyDivisors.ForGeneral` says that a property of vectors of `V ⊗_k k'`
  holds for general `v`, that is, at every field-valued point of one nonempty open of `𝔸^r_k`.

## Main results

* `Stacks.Bertini.FamilyDivisors.specializedDivisor_eq_comap` is the identity
  `H_v = H_{univ, v}`: the divisor of a vector `v` over a field extension is the fibre of the
  universal divisor over the point of `𝔸^r_k` that `v` determines.

## Implementation notes

Global sections of a sheaf of modules carry no `k`-module structure in Mathlib, so one is
supplied by restricting scalars along the ring map `k → Γ(X, 𝒪_X)` of the structure morphism;
this is `globalSections`, and the carrier of `globalSections k f L` is the carrier of
`Γ(L, ⊤)`, so `FamilyDivisors.sectionOf` needs no transport.

The parameter space is Mathlib's relative affine space `𝔸(ι; X)` for `ι` the basis index set
lifted to the universe of the scheme, which is `𝔸^r_k ×_k X` by
`AlgebraicGeometry.AffineSpace.isPullback_map`. A `k'`-point of `𝔸^r_k` is recorded by its
coordinate tuple `a : Fin r → k'`, which is the same data as the vector `Σᵢ aᵢ ⊗ vᵢ` of
`V ⊗_k k'`; `ForGeneral` quantifies over tuples and states the property of the vector. Its
defining open is a single open of `𝔸^r_k`, not an open chosen for each extension separately.

The fibre `H_{univ, v}` is taken as the scheme-theoretic inverse image
`Scheme.IdealSheafData.comap` along the morphism `X_{k'} → 𝔸^r_X` classifying the point, so
that the fibre identity is an equality of quasi-coherent ideal sheaves on `X_{k'}` rather than
an isomorphism of closed subschemes; `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` turns
it into the cartesian square. The proof is the base change of a zero scheme
([Stacks, Tag 0B6Y]) composed with the invariance of a zero scheme under an isomorphism of the
module carrying the section, which absorbs the comparison `f^* q^* L ≅ (f ≫ q)^* L`.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Bertini

/-- The ring map `k → Γ(X, 𝒪_X)` on global sections induced by the structure morphism of a
scheme over `k`. -/
def baseRingHom (k : Type u) [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    k →+* (X.ringCatSheaf.obj.obj (op ⊤)) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The global sections `Γ(X, L)` of a sheaf of modules on a scheme over `k`, as a
`k`-module: the scalars of the `Γ(X, 𝒪_X)`-module of global sections are restricted along
`baseRingHom`. -/
@[ega "I 2.2.5"]
def globalSections (k : Type u) [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (L : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (baseRingHom k f)).obj (L.val.obj (op ⊤))

/-- **Stacks Project, Tag 0G47.** The standing situation of the Bertini theorems: a field `k`,
a scheme `X` over `k`, an invertible `𝒪_X`-module `L`, a finite dimensional `k`-vector space
`V` with a chosen basis `v₁, …, v_r`, and a `k`-linear map `ψ : V → Γ(X, L)`. -/
@[stacks 0G47 "the standing situation"]
structure FamilyDivisors where
  /-- The base field `k`. -/
  k : Type u
  [isField : Field k]
  /-- The linear system `V`. -/
  V : Type v
  [isAddCommGroup : AddCommGroup V]
  [isModule : Module k V]
  [isFiniteDimensional : FiniteDimensional k V]
  /-- The scheme `X`. -/
  X : Scheme.{u}
  /-- The structure morphism `X → Spec k`. -/
  toBase : X ⟶ Spec (.of k)
  /-- The invertible `𝒪_X`-module `L`. -/
  L : X.Modules
  [isInvertible : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
    X.ringCatSheaf.property L]
  /-- The `k`-linear map `ψ : V → Γ(X, L)` presenting `V` as a linear system of sections. -/
  ψ : V →ₗ[k] globalSections k toBase L
  /-- The chosen basis `v₁, …, v_r` of `V`, where `r = dim V`. -/
  basis : Module.Basis (Fin (Module.finrank k V)) k V

attribute [instance] FamilyDivisors.isField FamilyDivisors.isAddCommGroup
  FamilyDivisors.isModule FamilyDivisors.isFiniteDimensional FamilyDivisors.isInvertible

/-- **A linear combination of pulled-back sections specializes compatibly.** If `f : B ⟶ A`
carries the coefficients `c` to the coefficients `r` and `f ≫ q = p`, then the zero scheme on
`B` of `Σᵢ rᵢ p^* sᵢ` is the inverse image along `f` of the zero scheme on `A` of
`Σᵢ cᵢ q^* sᵢ`. -/
public theorem zeroScheme_sum_smul_comap {Y A B : Scheme.{u}} (L : Y.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (q : A ⟶ Y) (f : B ⟶ A) (p : B ⟶ Y) (hp : f ≫ q = p) {ι : Type*} [Fintype ι]
    (c : ι → Γ(A, ⊤)) (r : ι → Γ(B, ⊤)) (hr : ∀ i, f.appTop (c i) = r i) (s : ι → Γ(L, ⊤)) :
    zeroScheme B ((Scheme.Modules.pullback p).obj L)
        (∑ i, r i • pullbackGlobalSections p L (s i)) =
      (zeroScheme A ((Scheme.Modules.pullback q).obj L)
        (∑ i, c i • pullbackGlobalSections q L (s i))).comap f := by
  subst hp
  have hi : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f q).hom.app L) ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback q).obj L)
        (∑ i, c i • pullbackGlobalSections q L (s i))) =
      ∑ i, r i • pullbackGlobalSections (f ≫ q) L (s i) := by
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
      Scheme.Modules.Hom.app_smul, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp,
      hr]
  rw [← Divisors.zeroScheme_pullback f ((Scheme.Modules.pullback q).obj L)
    (∑ i, c i • pullbackGlobalSections q L (s i))]
  exact (zeroScheme_eq_of_iso
    (L := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback q).obj L))
    (M := (Scheme.Modules.pullback (f ≫ q)).obj L)
    ((Scheme.Modules.pullbackComp f q).app L) hi).symm

namespace FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- The index set `{1, …, r}` of the chosen basis, in the universe of the scheme. -/
abbrev basisIndex : Type u := ULift.{u} (Fin (Module.finrank D.k D.V))

/-- The index set of the chosen basis has `dim V` elements: it is `Fin (dim V)` lifted to the
universe of the scheme. -/
theorem natCard_basisIndex : Nat.card D.basisIndex = Module.finrank D.k D.V := by
  simp

/-- The parameter space `𝔸^r_X = 𝔸^r_k ×_k X` of the family. -/
abbrev parameterSpace : Scheme.{u} := 𝔸(D.basisIndex; D.X)

/-- The projection `pr₂ : 𝔸^r_k ×_k X → X` of the parameter space. -/
abbrev parameterProjection : D.parameterSpace ⟶ D.X := 𝔸(D.basisIndex; D.X) ↘ D.X

/-- The section `ψ(v)` of `L` attached to a vector `v` of the linear system. -/
def sectionOf (v : D.V) : Γ(D.L, ⊤) := D.ψ v

/-- **The universal section** `s_univ = Σᵢ xᵢ ψ(vᵢ)` of `pr₂^* L` on `𝔸^r_k ×_k X`, where
`x₁, …, x_r` are the coordinates of the parameter affine space. -/
@[stacks 0G47 "the universal section"]
def universalSection :
    Γ((Scheme.Modules.pullback D.parameterProjection).obj D.L, ⊤) :=
  ∑ i : Fin (Module.finrank D.k D.V),
    AffineSpace.coord D.X (ULift.up i) •
      pullbackGlobalSections D.parameterProjection D.L (D.sectionOf (D.basis i))

/-- **The universal divisor** `H_univ = Z(s_univ) ⊂ 𝔸^r_k ×_k X`, the zero scheme of the
universal section. -/
@[stacks 0G47 "the universal divisor"]
def universalDivisor : D.parameterSpace.IdealSheafData :=
  zeroScheme D.parameterSpace ((Scheme.Modules.pullback D.parameterProjection).obj D.L)
    D.universalSection

section BaseChange

variable (K : Type u) [Field K] [Algebra D.k K]

/-- The base change `X_{k'} = X ×_k k'` of `X` along a field extension `k'/k`. -/
def baseChange : Scheme.{u} :=
  pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap D.k K)))

/-- The projection `X_{k'} → X` of the base change along a field extension. -/
def baseChangeToX : D.baseChange K ⟶ D.X :=
  pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap D.k K)))

/-- A scalar of the extension field, read as a global function on `X_{k'}` through the
projection `X_{k'} → Spec k'`. -/
def baseChangeScalar (a : K) : Γ(D.baseChange K, ⊤) :=
  (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap D.k K)))).appTop
    ((Scheme.ΓSpecIso (.of K)).inv a)

/-- **The section `ψ(v) = Σᵢ aᵢ ψ(vᵢ)`** of `L|_{X_{k'}}` attached to the vector
`v = Σᵢ aᵢ vᵢ` of `V ⊗_k k'` with coordinate tuple `a` over a field extension `k'/k`. -/
@[stacks 0G47 "the section attached to a vector over an extension field"]
def specializedSection (a : Fin (Module.finrank D.k D.V) → K) :
    Γ((Scheme.Modules.pullback (D.baseChangeToX K)).obj D.L, ⊤) :=
  ∑ i : Fin (Module.finrank D.k D.V),
    D.baseChangeScalar K (a i) •
      pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf (D.basis i))

/-- **The divisor `H_v = Z(ψ(v))`** on `X_{k'}` attached to the vector of `V ⊗_k k'` with
coordinate tuple `a`, as the zero scheme of the section it determines. -/
@[stacks 0G47 "the divisor attached to a vector over an extension field"]
def specializedDivisor (a : Fin (Module.finrank D.k D.V) → K) :
    (D.baseChange K).IdealSheafData :=
  zeroScheme (D.baseChange K) ((Scheme.Modules.pullback (D.baseChangeToX K)).obj D.L)
    (D.specializedSection K a)

/-- The morphism `X_{k'} → 𝔸^r_k ×_k X` over `X` classifying the `k'`-point of `𝔸^r_k` with
coordinate tuple `a`; the fibre of the universal divisor is taken along it. -/
def fibreParameterMap (a : Fin (Module.finrank D.k D.V) → K) :
    D.baseChange K ⟶ D.parameterSpace :=
  AffineSpace.homOfVector (D.baseChangeToX K) (fun i => D.baseChangeScalar K (a i.down))

/-- The classifying morphism of the point with coordinate tuple `a` sends the `i`-th
coordinate function of the parameter space to the `i`-th entry of `a`. -/
theorem fibreParameterMap_appTop_coord (a : Fin (Module.finrank D.k D.V) → K)
    (i : Fin (Module.finrank D.k D.V)) :
    (D.fibreParameterMap K a).appTop (AffineSpace.coord D.X (ULift.up i)) =
      D.baseChangeScalar K (a i) := by
  change (AffineSpace.homOfVector (D.baseChangeToX K)
      (fun j => D.baseChangeScalar K (a j.down))).appTop
        (AffineSpace.coord D.X (ULift.up i)) = D.baseChangeScalar K (a i)
  simpa only [ULift.down_up] using
    AffineSpace.homOfVector_appTop_coord (f := D.baseChangeToX K)
      (v := fun j => D.baseChangeScalar K (a j.down)) (i := ULift.up i)

/-- The classifying morphism of a point of `𝔸^r_k` lies over `X`. -/
theorem fibreParameterMap_comp_parameterProjection (a : Fin (Module.finrank D.k D.V) → K) :
    D.fibreParameterMap K a ≫ D.parameterProjection = D.baseChangeToX K :=
  AffineSpace.homOfVector_over _ _

/-- **`H_v = H_{univ, v}`.** The divisor attached to a vector of `V ⊗_k k'` is the fibre of
the universal divisor over the corresponding `k'`-point of `𝔸^r_k`, as quasi-coherent sheaves
of ideals on `X_{k'}`. -/
@[stacks 0G47 "the fibre of the universal divisor"]
theorem specializedDivisor_eq_comap (a : Fin (Module.finrank D.k D.V) → K) :
    D.specializedDivisor K a = D.universalDivisor.comap (D.fibreParameterMap K a) :=
  zeroScheme_sum_smul_comap D.L D.parameterProjection (D.fibreParameterMap K a)
    (D.baseChangeToX K) (D.fibreParameterMap_comp_parameterProjection K a)
    (fun i => AffineSpace.coord D.X (ULift.up i)) (fun i => D.baseChangeScalar K (a i))
    (D.fibreParameterMap_appTop_coord K a) (fun i => D.sectionOf (D.basis i))

end BaseChange

/-- The `k'`-point of `𝔸^r_k` with coordinate tuple `a`, for `k'/k` a field extension. -/
def parameterPoint {K : Type u} [Field K] [Algebra D.k K]
    (a : Fin (Module.finrank D.k D.V) → K) :
    Spec (.of K) ⟶ 𝔸(D.basisIndex; Spec (.of D.k)) :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap D.k K)))
    (fun i => (Scheme.ΓSpecIso (.of K)).inv (a i.down))

/-- **A property of vectors holds for general `v`** when there is one nonempty open
`U ⊂ 𝔸^r_k` such that `P` holds at every vector of `V ⊗_k k'` whose coordinate tuple gives a
`k'`-point of `U`, for every field extension `k'/k`. -/
@[stacks 0G47 "holding for general vectors"]
def ForGeneral
    (P : ∀ (K : Type u) [Field K] [Algebra D.k K], TensorProduct D.k D.V K → Prop) : Prop :=
  ∃ U : (𝔸(D.basisIndex; Spec (.of D.k))).Opens,
    U.1.Nonempty ∧
      ∀ (K : Type u) [Field K] [Algebra D.k K] (a : Fin (Module.finrank D.k D.V) → K),
        (∀ p : Spec (.of K), D.parameterPoint a p ∈ U) →
          P K (∑ i, TensorProduct.tmul D.k (D.basis i) (a i))

end FamilyDivisors

end Stacks.Bertini

end
