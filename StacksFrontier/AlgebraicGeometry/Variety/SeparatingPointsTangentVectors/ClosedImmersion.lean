module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified
public import StacksCore.Tactic.StacksAttribute

/-!
# A linear system separating points and tangent vectors is very ample

Let `k` be an algebraically closed field, let `X` be a proper `k`-scheme, let `ℒ` be a module on
`X` and let `φ : X ⟶ Y` be a morphism to a separated `k`-scheme carrying a module `ℳ` with
`φ^* ℳ ≅ ℒ`. If the global sections of `ℳ`, transported to `ℒ` along that isomorphism, separate
the closed points of `X` and separate the tangent vectors of `X` over `k`, then `φ` is a closed
immersion. When the target is a projective bundle `𝐏(E)` over `k` and `ℳ` is its degree-one twist
this says that `ℒ` is very ample relative to the structure morphism of `X`.

## Main results

* `AlgebraicGeometry.formallyUnramified_of_separatesTangentVectors`: a family of sections pulled
  back along `φ` which separates tangent vectors makes `φ` formally unramified.
* `AlgebraicGeometry.isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors`: the
  two separation conditions together with properness of `X` over `k` and separatedness of the
  target over `k` make `φ` a closed immersion.
* `AlgebraicGeometry.isClosedImmersion_projectiveSpaceOfModule_of_separates`: the same with
  `Y = 𝐏(W)` the projective space of a nonzero finite-dimensional `k`-vector space `W`, which is
  proper, hence separated, over `k`.
* `AlgebraicGeometry.isRelativelyVeryAmple_of_separatesClosedPoints_of_separatesTangentVectors`:
  with `Y = 𝐏(E)` the projective bundle of a quasi-coherent `k`-module and `ℳ = 𝒪_{𝐏(E)}(1)`, an
  invertible `ℒ` whose system separates points and tangent vectors is very ample relative to the
  structure morphism of `X`.

## Implementation notes

The morphism `φ`, the module `ℳ` on the target, the isomorphism `φ^* ℳ ≅ ℒ` and the family of
sections of `ℳ` inducing the linear system are data here. For `ℒ` invertible and `V` a subspace
of `Γ(X, ℒ)` generating `ℒ` they are the canonical morphism `φ_{ℒ,V} : X ⟶ 𝐏(V)` of
[Stacks, Tag 0FCY] together with `𝒪_{𝐏(V)}(1)` and its degree-one sections; no statement below
produces that morphism, and nothing below uses any property of `ℳ` beyond the existence of the
isomorphism.

Properness of `φ` itself is not assumed: it follows from properness of `X` over `k` and
separatedness of the target over `k`, which for a projective bundle is unconditional. Local
finiteness of type of `φ`, needed for the tangent criterion of [Stacks, Tag 0B2G] and for the
identification of the residue field at a closed point with `k`, likewise follows from properness
of `X` over `k`.

## References

* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Ample Stacks.Tag01VMVeryAmple
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjSeparated (isSeparated_toBase)
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe v u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}

/-- **Separation of tangent vectors makes a morphism formally unramified.** Let `φ : X ⟶ Y` be a
morphism of `k`-schemes with `X` locally of finite type over `k`, let `θ : φ^* ℳ ≅ ℒ` and let `ψ`
be obtained from a family `t` of global sections of `ℳ` by pulling back along `φ` and
transporting along `θ`. If `ψ` separates the tangent vectors of `X` over `k`, then `φ` is
formally unramified. -/
theorem formallyUnramified_of_separatesTangentVectors (f : X ⟶ Y) (p : X ⟶ Spec (.of k))
    (q : Y ⟶ Spec (.of k)) (h : f ≫ q = p) [LocallyOfFiniteType p]
    {M : Y.Modules} {L : X.Modules} (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (htangent : SeparatesTangentVectors p ψ) : FormallyUnramified f := by
  subst h
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ q)
  refine formallyUnramified_of_unramifiedAt_closedPoints f fun x hx => ?_
  have : IsIso (f.residueFieldMap x) := isIso_residueFieldMap_of_isClosed f q x hx
  exact (injective_tangentMap_iff_unramifiedAt_of_locallyOfFiniteType_base f _ q x rfl).mp
    (tangentMap_injective_of_separatesTangentVectors f _ q rfl x hx θ htψ htangent)

/-- **The closed-immersion criterion of [Stacks, Tag 0E8S].** Let `k` be an algebraically closed
field, let `X` be proper over `k`, let `φ : X ⟶ Y` be a morphism of `k`-schemes with `Y`
separated over `k`, let `θ : φ^* ℳ ≅ ℒ` and let `ψ` be obtained from a family `t` of global
sections of `ℳ` by pulling back along `φ` and transporting along `θ`. If `ψ` separates the closed
points of `X` and separates the tangent vectors of `X` over `k`, then `φ` is a closed immersion. -/
theorem isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors (f : X ⟶ Y)
    (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k)) (h : f ≫ q = p) [IsProper p] [IsSeparated q]
    {M : Y.Modules} {L : X.Modules} (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hpoints : SeparatesClosedPoints ψ) (htangent : SeparatesTangentVectors p ψ) :
    IsClosedImmersion f := by
  subst h
  have : IsProper f := IsProper.of_comp f q
  have : FormallyUnramified f :=
    formallyUnramified_of_separatesTangentVectors f _ q rfl θ htψ htangent
  refine isClosedImmersion_of_isProper_of_formallyUnramified f q fun a b ha hb hab => ?_
  exact injective_of_separatesClosedPoints f _ θ htψ hpoints a b ha hb hab

/-- **The closed-immersion criterion of [Stacks, Tag 0E8S] into the projective space of a linear
system.** Let `k` be an algebraically closed field, let `W` be a nonzero finite-dimensional
`k`-vector space, let `X` be proper over `k` and let `φ : X ⟶ 𝐏(W)` be a morphism over `k`
carrying a module `ℳ` with `φ^* ℳ ≅ ℒ`. If the transported family of global sections of `ℳ`
separates the closed points of `X` and separates the tangent vectors of `X` over `k`, then `φ` is
a closed immersion. -/
theorem isClosedImmersion_projectiveSpaceOfModule_of_separates {W : Type u} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] [Nontrivial W] (p : X ⟶ Spec (.of k)) [IsProper p]
    (f : X ⟶ projectiveSpaceOfModule k W)
    (h : f ≫ projectiveSpaceOfModuleToSpec k W = p)
    {M : (projectiveSpaceOfModule k W).Modules} {L : X.Modules}
    (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hpoints : SeparatesClosedPoints ψ) (htangent : SeparatesTangentVectors p ψ) :
    IsClosedImmersion f :=
  isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors f p
    (projectiveSpaceOfModuleToSpec k W) h θ htψ hpoints htangent

/-- **The very-ampleness clause of [Stacks, Tag 0E8S].** Let `k` be an algebraically closed
field, let `X` be proper over `k` through `p`, let `E` be a quasi-coherent `k`-module and let
`i : X ⟶ 𝐏(E)` be a morphism over `k` with `i^* 𝒪_{𝐏(E)}(1) ≅ ℒ` for an invertible `ℒ`. If the
transported family of global sections of `𝒪_{𝐏(E)}(1)` separates the closed points of `X` and
separates the tangent vectors of `X` over `k`, then `ℒ` is very ample relative to `p`. -/
theorem isRelativelyVeryAmple_of_separatesClosedPoints_of_separatesTangentVectors
    {E : (Spec (CommRingCat.of k)).Modules} [E.IsQuasicoherent] (p : X ⟶ Spec (.of k))
    [IsProper p] (i : X ⟶ (relativeProj (symAlgebra E)).scheme)
    (h : i ≫ (relativeProj (symAlgebra E)).toBase = p)
    {L : X.Modules} [IsInvertibleModule X L]
    (θ : (Scheme.Modules.pullback i).obj (twistOne E) ≅ L)
    {V : Type v} {t : V → (twistOne E).val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop i (twistOne E) (t v)) = ψ v)
    (hpoints : SeparatesClosedPoints ψ) (htangent : SeparatesTangentVectors p ψ) :
    IsRelativelyVeryAmple p L := by
  have hsep : IsSeparated (relativeProj (symAlgebra E)).toBase :=
    isSeparated_toBase (symAlgebra E) (relativeProj (symAlgebra E))
  have hci : IsClosedImmersion i :=
    isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors i p
      (relativeProj (symAlgebra E)).toBase h θ htψ hpoints htangent
  exact isRelativelyVeryAmple_of_immersion p L E i inferInstance h θ.symm

end AlgebraicGeometry

end
