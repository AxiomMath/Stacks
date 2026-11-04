module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantModules
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated sheaf of an irrelevant graded module vanishes, in any generation degree

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, let `X = Proj 𝒜`, let `d` be a positive integer and
let `M` be a graded `A`-module whose homogeneous components vanish in all large degrees
divisible by `d`. Then `M̃ = 0`.

This is the half of the kernel identification in the proof of Stacks 0BXF which says that
`M ↦ M̃` kills the irrelevant modules — in the source, "Conversely, assume `M` is irrelevant.
Then `M_{nd}` is zero for `n ≫ 0`. Clearly this implies that `M_{(f_i)} = 0`, whence `M̃ = 0` by
construction." No bound on the generation degrees of `A` is assumed.

## Main results

* `moduleFiber_eq_zero_of_isModuleFraction`: a degree-zero homogeneous fraction of such a module
  is zero in the fiber at each point where its denominator does not vanish.
* `isZero_associatedModuleSheaf_of_gradeEventuallyZero` and
  `isZero_associatedModuleSheafFunctor_obj_of_gradeEventuallyZero`: **the associated sheaf of such
  a module is a zero object**, bare and for the bundled functor.
* `isZero_associatedModuleSheafFunctor_obj_of_isIrrelevant`: **the same for an irrelevant finitely
  generated graded module**, which is the form the proof of Tag 0BXF uses.

## Implementation notes

The vanishing has to be read off the *sections*, not the fibers, and that is the whole point of
this file. `StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/TorsionVanishing.lean` proves
`M̃ = 0` from triviality of every fiber `M_𝔭`, and its hypothesis — the components vanish in
*all* large degrees — is what makes those fibers trivial. Under the weaker hypothesis here the
fibers need not be trivial: for `A = k[x]` with `x` of degree `2`, so that `d = 2`, the shift
`M = A(1)` has `M_{2n} = A_{2n+1} = 0` for every `n`, yet localizing `M` at the complement of
the homogeneous prime `(0)` inverts `x` and leaves a nonzero module. What is true is that each
*degree-zero* homogeneous fraction dies, and a section of `M̃` is by construction locally such a
fraction, so every section is pointwise zero.

Killing a fraction `m / s` with `m` and `s` of the same degree `n` splits on whether `n` is
zero. For `n > 0` the denominator `s` is itself a homogeneous element of positive degree outside
the prime, and
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pow_smul_eq_zero_of_gradeEventuallyZero`
applied to it provides the power of `s` that kills `m`. For `n = 0` there is no such `s`, and a
homogeneous element of positive degree outside the prime is taken instead, which exists by
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_homogeneous_pos_degree_notMem`; the
numerator then has degree `0 = 0 * k`, which is the degree shape that lemma consumes.

That lemma is where the arithmetic of a generation degree `d` greater than one is done: the
numerator of a spanning fraction has degree a multiple of `deg s`, not of `d`, and the exponent
it produces pushes the total degree up to a multiple of `d` with a large quotient.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (ModuleFiber IsModuleFraction locallyModuleFraction moduleSections associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] ProjectiveSpectrum.isPrime

/-- **A degree-zero homogeneous fraction of a module vanishing in large degrees divisible by
`D` is zero in every fiber in which its denominator is invertible.** -/
public theorem moduleFiber_eq_zero_of_isModuleFraction {D : ℕ} (hD : 0 < D)
    {X : GradedModuleCat.{u, v, w} 𝒮} (h : GradeEventuallyZero 𝒮 D X)
    (x : ProjectiveSpectrum.top 𝒮) {n : ℕ} {m : X.carrier} {s : S}
    (hm : m ∈ X.grade (n : ℤ)) (hs : s ∈ 𝒮 n) (hsx : s ∉ x.asHomogeneousIdeal) :
    (LocalizedModule.mk m ⟨s, hsx⟩ : ModuleFiber (M := X.carrier) 𝒮 x) = 0 := by
  obtain ⟨t, htx, hkill⟩ :
      ∃ t : S, t ∈ x.asHomogeneousIdeal.toIdeal.primeCompl ∧ t • m = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨k, hk, g, hg, hgx⟩ := exists_homogeneous_pos_degree_notMem 𝒮 x
      obtain ⟨j, hj⟩ := exists_pow_smul_eq_zero_of_gradeEventuallyZero 𝒮 hD h hk hg
        (n := 0) (x := m) (by simpa using hm)
      exact ⟨g ^ j, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hgx j, hj⟩
    · obtain ⟨j, hj⟩ := exists_pow_smul_eq_zero_of_gradeEventuallyZero 𝒮 hD h hn hs
        (n := 1) (x := m) (by simpa using hm)
      exact ⟨s ^ j, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hsx j, hj⟩
  have hmk : (LocalizedModule.mk m ⟨s, hsx⟩ : ModuleFiber (M := X.carrier) 𝒮 x) =
      LocalizedModule.mk 0 ⟨s, hsx⟩ := by
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨t, htx⟩, ?_⟩
    have hz : t • s • m = 0 := by
      rw [smul_smul, mul_comm, ← smul_smul, hkill, smul_zero]
    rw [smul_zero, smul_zero]
    exact hz
  rw [hmk, LocalizedModule.zero_mk]

/-- Every section of the associated sheaf of such a module is pointwise zero. -/
public theorem moduleSections_apply_eq_zero {D : ℕ} (hD : 0 < D)
    {X : GradedModuleCat.{u, v, w} 𝒮} (h : GradeEventuallyZero 𝒮 D X)
    {U : Opens (ProjectiveSpectrum.top 𝒮)}
    {a : ∀ x : U, ModuleFiber (M := X.carrier) 𝒮 x.1}
    (ha : (locallyModuleFraction 𝒮 X.grade).pred a) (x : U) : a x = 0 := by
  obtain ⟨V, hxV, iV, n, m, s, hm, hs, hns, hav⟩ := ha x
  have hval : a x = LocalizedModule.mk m ⟨s, hns ⟨x.1, hxV⟩⟩ := hav ⟨x.1, hxV⟩
  rw [hval]
  exact moduleFiber_eq_zero_of_isModuleFraction 𝒮 hD h x.1 hm hs (hns ⟨x.1, hxV⟩)

/-- The section groups of the associated sheaf of such a module are trivial. -/
@[ega "II 2.7.2" "more general", ega "II 2.7.3" "(ii)", ega "II 3.4.2" "special case"]
public theorem subsingleton_moduleSections_of_gradeEventuallyZero {D : ℕ} (hD : 0 < D)
    {X : GradedModuleCat.{u, v, w} 𝒮} (h : GradeEventuallyZero 𝒮 D X)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    Subsingleton (moduleSections 𝒮 X.grade U) :=
  ⟨fun a b => Subtype.ext (funext fun x => by
    rw [moduleSections_apply_eq_zero 𝒮 hD h a.2 x, moduleSections_apply_eq_zero 𝒮 hD h b.2 x])⟩

/-- **The associated sheaf of a graded module whose homogeneous components vanish in all large
degrees divisible by `D` is a zero object.** -/
@[ega "II 2.7.2" "more general", ega "II 2.7.3" "(ii)", ega "II 3.4.2" "special case"]
public theorem isZero_associatedModuleSheaf_of_gradeEventuallyZero {D : ℕ} (hD : 0 < D)
    {X : GradedModuleCat.{u, v, w} 𝒮} (h : GradeEventuallyZero 𝒮 D X) :
    Limits.IsZero (associatedModuleSheaf 𝒮 X.grade) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  ext U a : 4
  exact @Subsingleton.elim _
    (subsingleton_moduleSections_of_gradeEventuallyZero 𝒮 hD h U.unop) _ _

/-- The same for the bundled associated-sheaf functor. -/
@[ega "II 2.7.2" "more general", ega "II 2.7.3" "(ii)", ega "II 3.4.2" "special case"]
public theorem isZero_associatedModuleSheafFunctor_obj_of_gradeEventuallyZero {D : ℕ}
    (hD : 0 < D) (X : GradedModuleCat.{u, v, w} 𝒮) (h : GradeEventuallyZero 𝒮 D X) :
    Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj X) :=
  (associatedModuleSheafFunctor_obj 𝒮 X) ▸
    isZero_associatedModuleSheaf_of_gradeEventuallyZero 𝒮 hD h

/-- **Stacks 0BXF, the easy half of the kernel identification, in any generation degree.** The
associated-sheaf functor `M ↦ M̃` sends an irrelevant finitely generated graded module to a zero
object, for every positive `d`. For `d = 1` this is the torsion statement of Tag 0BXD. -/
public theorem isZero_associatedModuleSheafFunctor_obj_of_isIrrelevant {d : ℕ} (hd : 0 < d)
    (X : GradedModuleCat.{u, v, w} 𝒮) [Module.Finite S X.carrier]
    (hirr : IsIrrelevant 𝒮 d X) :
    Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj X) :=
  isZero_associatedModuleSheafFunctor_obj_of_gradeEventuallyZero 𝒮 hd X
    (gradeEventuallyZero_of_isIrrelevant 𝒮 hd hirr)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
