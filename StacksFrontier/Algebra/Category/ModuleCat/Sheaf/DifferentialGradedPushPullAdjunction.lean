module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushPullHomogeneous

/-!
# Pull and push for sheaves of differential graded modules: the adjunction

Let `F : C ⥤ D` be a continuous functor of small sites, read as the functor underlying a
morphism of ringed sites `f : (D, K, P) ⟶ (C, J, O)` in the opposite direction, let `A'` be a
sheaf of differential graded algebras on the target, let `A` be a sheaf of differential graded
algebras on the source and let `φ₀ : f⁻¹A' ⟶ A` be a unital homomorphism, equivalently a
homomorphism `φ : A' ⟶ f_*A`. For a right differential graded `A'`-module `M` and a right
differential graded `A`-module `N` the differential graded Hom objects
`Hom_{Mod^dg(A', d)}(M, f_*N)` and `Hom_{Mod^dg(A, d)}(f^*M, N)` agree: in every degree the
homogeneous right-linear maps correspond, by precomposition with the unit of the pullback, and
the correspondence commutes with the differentials of the two Hom complexes. Its degree-zero
closed part is the hom-set adjunction `f^* ⊣ f_*`.

Here `f_*` is the direct image of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean` and `f^*` is
the construction `f^*M = f⁻¹M ⊗_{f⁻¹A'} A` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackConstruction.lean`,
shown to be the pullback in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackAdjunction.lean`.

## Main results

* `Stacks.DifferentialGradedPullbackConstruction.exists_pullbackPushforwardHomEquiv`: the
  identification of the two differential graded Hom objects, in all degrees and compatibly with
  their differentials, together with the hom-set bijection it induces in degree zero.

## Implementation notes

Both halves are already available and are only instantiated here. The degreewise identification
for an abstract pullback datum is
`SheafOfModules.DifferentialGradedModule.PullbackData.homogeneousMapEquiv` of
`DifferentialGradedPushPullHomogeneous.lean`, which also records that it is precomposition with
the unit; the compatibility with the differentials is then `precompCochain_delta` of
`DifferentialGradedPushforward.lean`. What was missing was an *inhabitant* of the pullback
datum, so that the identification is not conditional on one: that is
`Stacks.DifferentialGradedPullbackConstruction.pullbackData`, built from
`f^*M = f⁻¹M ⊗_{f⁻¹A'} A`. Feeding it in is what turns the conditional statements into this
one.

`SheafOfModules.DifferentialGradedModule.HomogeneousMap` is indexed by an
`AlgebraicGeometry.RingedSite`, while the construction of the pullback is stated for a sheaf of
commutative rings on a small site; the two ringed sites `⟨D, K, P⟩` and `⟨C, J, O⟩` are
therefore spelled out at the two occurrences of `HomogeneousMap`, their structure sheaves being
the sheaves of rings the modules are already taken over.

The sum of two homogeneous maps and the differential of one are named by hypotheses rather than
written as operations, the device of `DifferentialGradedTensorHomHomComplex.lean`: the
`AddCommGroup` structure on `SheafOfModules.DifferentialGradedModule.HomogeneousMap` is private
to `DifferentialGradedAxiomA.lean`, and the differential of a homogeneous map is the one of the
Hom complex of cochains. Nothing is restricted by naming them, since both are realized.

**Universes.** The statement below quantifies over
`SheafOfModules.DifferentialGradedModule.{u, u, u}`, the site and module universes identified,
where the source identifies nothing. The restriction is on the *constructed* pullback only:
`SheafOfModules.DifferentialGradedModule.PullbackData.homogeneousMapEquiv`, which is the content
of this tag, holds for an abstract pullback datum with the two sites, their morphism universes
and the two algebras' homogeneous pieces independent, and
`Stacks.DifferentialGradedPullbackConstruction.pullbackObj` is the inhabitant fed to it.

Neither ingredient of that inhabitant is pinned to the site universe: the inverse image takes a
free module universe under `[UnivLE.{u, w}]`, and
`SheafOfModules.RelativeTensor.dgTensorRight` takes the level `max u v z` with `z` free. What
survives is that those are incompatible spellings of one condition, and that spelling this
chain with a `max` costs more heartbeats than the limit.
`DifferentialGradedPullbackAdjunction.lean` records the measurement, the two proofs that time
out, and the change to `Stacks.bilinHom` that would reconcile them.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage
open SheafOfModules.DifferentialGradedModule CochainComplex.HomComplex

universe u

namespace Stacks.DifferentialGradedPullbackConstruction

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]
  {A' : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)}

include radj

/-- **Pull and push for sheaves of differential graded modules**: for the direct image `f_*` and
the pullback `f^*M = f⁻¹M ⊗_{f⁻¹A'} A` along a morphism of small ringed sites, together with a
unital homomorphism `φ₀ : f⁻¹A' ⟶ A`,
`Hom_{Mod^dg(A', d)}(M, f_*N) = Hom_{Mod^dg(A, d)}(f^*M, N)`.

The identification `e` of the two differential graded Hom objects is given in every degree `n`,
it is precomposition with the unit `M ⟶ f^*M` of the pullback — so in particular it is additive
and natural — and it carries the differential of the one Hom complex to the differential of the
other. Its degree-zero closed part is the bijection `e₀` of hom-sets of the adjunction
`f^* ⊣ f_*`, which sends a morphism `g : f^*M ⟶ N` to the unit followed by `g`, read as a
morphism `M ⟶ f_*N`. -/
@[stacks 0FRU]
theorem exists_pullbackPushforwardHomEquiv (φ₀ : inverseImageAlgebra α hO hP A' ⟶ A)
    (hφ₀ : φ₀.IsUnital) :
    ∃ (e : ∀ (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
          (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A) (n : ℤ),
          HomogeneousMap (X := ⟨D, K, Psharp⟩) A (pullbackObj α hO hP φ₀ hφ₀ M) N n ≃
            HomogeneousMap (X := ⟨C, J, Osharp⟩) A' M
              (pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N) n)
        (e₀ : ∀ (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
          (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A),
          (pullbackObj α hO hP φ₀ hφ₀ M ⟶ N) ≃
            (M ⟶ pushforwardObj (semilinearHom α hO hP φ₀ hφ₀) N)),
      (∀ M N n w, (e M N n w).val =
          precompCochain (pullbackUnit α hO hP φ₀ hφ₀ M) w.val) ∧
      (∀ M N n w w' w'', w''.val = w.val + w'.val →
          (e M N n w'').val = (e M N n w).val + (e M N n w').val) ∧
      (∀ M N n w w', w'.val = δ n (n + 1) w.val →
          (e M N (n + 1) w').val = δ n (n + 1) (e M N n w).val) ∧
      (∀ M N g, e₀ M N g = semilinearHomEquiv (semilinearHom α hO hP φ₀ hφ₀) M N
          ((pullbackUnit α hO hP φ₀ hφ₀ M).postcomp g)) := by
  have hval : ∀ (M : SheafOfModules.DifferentialGradedModule.{u, u, u} A')
      (N : SheafOfModules.DifferentialGradedModule.{u, u, u} A) (n : ℤ)
      (w : HomogeneousMap (X := ⟨D, K, Psharp⟩) A (pullbackObj α hO hP φ₀ hφ₀ M) N n),
      (PullbackData.homogeneousMapEquiv (X := ⟨D, K, Psharp⟩) (X' := ⟨C, J, Osharp⟩)
          (semilinearHom α hO hP φ₀ hφ₀) N n (pullbackData α hO hP φ₀ hφ₀) M w).val =
        precompCochain (pullbackUnit α hO hP φ₀ hφ₀ M) w.val :=
    fun M N n w => PullbackData.homogeneousMapEquiv_val (X := ⟨D, K, Psharp⟩)
      (X' := ⟨C, J, Osharp⟩) (semilinearHom α hO hP φ₀ hφ₀) N n
      (pullbackData α hO hP φ₀ hφ₀) M w
  refine ⟨fun M N n => PullbackData.homogeneousMapEquiv (X := ⟨D, K, Psharp⟩)
      (X' := ⟨C, J, Osharp⟩) (semilinearHom α hO hP φ₀ hφ₀) N n
      (pullbackData α hO hP φ₀ hφ₀) M,
    fun M N => pullbackPushforwardHomEquiv (pullbackData α hO hP φ₀ hφ₀) M N,
    hval, fun M N n w w' w'' hw => ?_, fun M N n w w' hw => ?_, fun _ _ _ => rfl⟩
  · beta_reduce
    erw [hval, hw, precompCochain_add, hval M N n w, hval M N n w']
    rfl
  · beta_reduce
    erw [hval, hw, precompCochain_delta _ rfl, hval M N n w]
    rfl

end Stacks.DifferentialGradedPullbackConstruction

end
