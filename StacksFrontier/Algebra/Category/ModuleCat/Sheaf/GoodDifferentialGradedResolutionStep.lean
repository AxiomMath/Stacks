module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat

/-!
# The inductive step in the construction of a flat resolution

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras and let `P`
be a right differential graded `A`-module. The first proof of Tag 0FSH builds a tower
`P₀ → P₁ → ⋯ → M` whose colimit resolves `M`; this file builds its inductive step, the twisted
extension of `P` by a free module.

The data of the step is a sheaf of graded sets `S` together with a *cycle* of `P` of degree `n`
for every local section of `S` of degree `n` — a family of homogeneous local sections which is
compatible with restriction and closed. Such a family extends to a homomorphism of
**differential** graded modules `A[S] ⟶ P`, which is `SheafOfModules.dgLiftHom`, and the twisted
extension is the cone of that homomorphism: as a graded module it is `P ⊕ A[S][1]`, and its
differential sends a new generator to the cycle chosen for it.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.twistedExtension` is the twisted extension
  `P[S, c]` of `P` by `A[S]` along a family `c` of cycles, with
  `SheafOfModules.DifferentialGradedModule.twistedExtensionInclusion` and
  `SheafOfModules.DifferentialGradedModule.twistedExtensionProjection` its two canonical maps.

## Main results

* `SheafOfModules.DifferentialGradedModule.twistedExtension_isAdmissibleShortExact`:
  **`0 ⟶ P ⟶ P[S, c] ⟶ A[S][1] ⟶ 0` is an admissible short exact sequence.** The twisted
  differential is square-zero and satisfies the Leibniz rule because the chosen sections are
  cycles: that is exactly the statement that `A[S] ⟶ P` is a homomorphism of differential graded
  modules, and the mapping cone of a homomorphism is a differential graded module.
* `SheafOfModules.DifferentialGradedModule.twistedExtension_isGradedFlat` and
  `SheafOfModules.DifferentialGradedModule.twistedExtension_isKFlat`: **the twisted extension of
  a flat and K-flat module is flat and K-flat**, i.e. conditions (1) and (2) of Tag 0FSA
  propagate along the step. These are two out of three along the admissible short exact sequence
  (Tag 0FSC) together with the flatness of `A[S]` (Tag 0FSG) and of its shift.
* `SheafOfModules.DifferentialGradedModule.ConePackage.homologyMap_comp_inclusion_eq_zero`:
  **`Hⁿ(K) → Hⁿ(L) → Hⁿ(C(f))` is zero**, and its specialization
  `SheafOfModules.DifferentialGradedModule.homologyMap_comp_twistedExtensionInclusion_eq_zero`:
  **every class coming from `A[S]` — in particular the class of each chosen cycle — dies in the
  twisted extension.** The hypothesis-feeding form is
  `SheafOfModules.DifferentialGradedModule.comp_homologyMap_twistedExtensionInclusion_eq_zero`,
  which is the shape of the kernel-annihilation hypothesis of
  `SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.exists_comp_d_eq` and its specialization
  `SheafOfModules.DifferentialGradedModule.exists_comp_d_eq_twistedExtension`: **a cycle of
  `A[S]` becomes a boundary in the twisted extension**, the cochain-level form of the same
  statement — its image in `P`, which on the canonical generators is the chosen cycle itself
  (`SheafOfModules.dgLiftHom_generator`), is the differential of a section of `P[S, c]`.

## Implementation notes

**The twisted extension is the cone.** The twisted differential of `P ⊕ A[S]` is not the
direct-sum differential, so it is not the biproduct of differential graded modules; but it *is*
the mapping-cone differential of the homomorphism `A[S] ⟶ P` reading the new generators as
cycles of `P`. So no square-zero law and no Leibniz rule is proved here for the extension
itself: both are already proved for the cone, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedCone.lean`, and the entire
mathematical content of the step is the existence of that homomorphism —
`SheafOfModules.dgLiftHom` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleLift.lean`, where the
cycle condition is used exactly once, to kill the term `d(c(s)) · a` of the Leibniz rule of `P`.
Degreewise the cone of `g : K ⟶ P` is `K^{n+1} ⊕ P^n`, so the free module whose cone is taken is
the one whose generators sit in the degree of the cycle they are sent to, and the third term of
the short exact sequence is its degree-one shift `A[S][1]`, which is `A[S]` with its generators
moved down one degree. This is the indexing of the source's `Pᵢ₊₁ = Pᵢ ⊕ A[Sᵢ₊₁]`, in which a
generator of `Sᵢ₊₁` of degree `n` has as differential a cycle of degree `n + 1`.

**The killing of cohomology needs no hypothesis.** For a general twisted extension of `P` by a
module `Q` the composite `Hⁿ(K) → Hⁿ(P) → Hⁿ(P ⊕ Q)` is killed only after surjectivity of
`Q → K[1]` on cycles; for the cone, where `Q` *is* `K[1]`, the null-homotopy is the canonical
degree `-1` cochain `CochainComplex.mappingCone.inl` and no hypothesis is needed. That is why
`SheafOfModules.DifferentialGradedModule.ConePackage.homologyMap_comp_inclusion_eq_zero` is
stated for an arbitrary cone package.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-! ### The cohomology killed by a cone -/

/-- The composite of `f` with the inclusion into any cone package of `f` is null-homotopic, via the
canonical degree `-1` cochain `CochainComplex.mappingCone.inl`. -/
private theorem ConePackage.nonempty_homotopy_comp_inclusion
    {C' : Type*} [Category C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat}
    {A' : DifferentialGradedAlgebra R'} {K L : DifferentialGradedModule A'} {f : K ⟶ L}
    (Pk : ConePackage f) :
    Nonempty (Homotopy (f.toHomologicalComplex ≫ Pk.inclusion.toHomologicalComplex) 0) := by
  obtain ⟨⟨cplx, mul, hassoc, hone, hleib⟩, incl, proj, hcx, iso, hiso, af, as, hi, hp⟩ := Pk
  dsimp only at hcx hi ⊢
  subst hcx
  rw [show incl.toHomologicalComplex =
    CochainComplex.mappingCone.inr f.toHomologicalComplex from eq_of_heq hi]
  exact ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨CochainComplex.mappingCone.inl f.toHomologicalComplex, by simp⟩⟩

omit [HasWeakSheafify J (Type m)] in
/-- **A class coming from the source of a morphism dies in its cone**: the composite
`Hⁿ(K) → Hⁿ(L) → Hⁿ(C(f))` is zero, for any cone package of `f : K ⟶ L`. No hypothesis is
needed: the null-homotopy of `f` followed by the inclusion is the canonical degree `-1` cochain
`CochainComplex.mappingCone.inl`. -/
theorem ConePackage.homologyMap_comp_inclusion_eq_zero
    {K L : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L} (Pk : ConePackage f) (n : ℤ) :
    HomologicalComplex.homologyMap (f ≫ Pk.inclusion).toHomologicalComplex n = 0 := by
  obtain ⟨ho⟩ := Pk.nonempty_homotopy_comp_inclusion
  exact (ho.homologyMap_eq n).trans (HomologicalComplex.homologyMap_zero _ _ _)

omit [HasWeakSheafify J (Type m)] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{m}] in
/-- **A cycle of `K` becomes a boundary in the cone of `f : K ⟶ L`**, after being carried into
`L` by `f` and included: for a cycle tested by an arbitrary sheaf of modules `Z`, the composite
`Z ⟶ K^{n+1} ⟶ L^{n+1} ⟶ C(f)^{n+1}` is the differential of a section of `C(f)^n`. The
section is the cycle followed by the null-homotopy of `f` composed with the inclusion, whose
degree `-1` component is `CochainComplex.mappingCone.inl`. -/
theorem ConePackage.exists_comp_d_eq {K L : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L}
    (Pk : ConePackage f) (n : ℤ) {Z : SheafOfModules.{m} (toRingCat J Osharp)}
    (x : Z ⟶ K.complex.X (n + 1)) (hx : x ≫ K.complex.d (n + 1) (n + 1 + 1) = 0) :
    ∃ y : Z ⟶ Pk.cone.complex.X n,
      x ≫ f.toHomologicalComplex.f (n + 1) ≫ Pk.inclusion.toHomologicalComplex.f (n + 1) =
        y ≫ Pk.cone.complex.d n (n + 1) := by
  obtain ⟨ho⟩ := Pk.nonempty_homotopy_comp_inclusion
  refine ⟨x ≫ ho.hom (n + 1) n, ?_⟩
  have hcomm := ho.comm (n + 1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    HomologicalComplex.zero_f, add_zero] at hcomm
  rw [← HomologicalComplex.comp_f, hcomm, Preadditive.comp_add, ← Category.assoc x,
    ← Category.assoc x, hx, zero_comp, zero_add]

/-! ### The twisted extension -/

section Extension

variable (S : SheafOfGradedSets.{m} J) (P : DifferentialGradedModule.{t, m, m} A)
  (c : GradedGeneratorFamily S (GradedModule.ofDifferentialGraded P))
  (hc : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
    homSections (P.complex.d n (n + 1)) U (c.app n U s hs) = 0)

/-- **The twisted extension `P[S, c]` of `P` by the free module on `S` along a family `c` of
cycles.** As a graded module it is `P ⊕ A[S][1]`, and its differential is the one of `P` and of
`A[S]` corrected by the map sending a new generator to the cycle chosen for it: that is the
mapping-cone differential of `SheafOfModules.dgLiftHom`, so the construction is the cone of that
homomorphism and needs no square-zero law of its own. -/
noncomputable abbrev twistedExtension : DifferentialGradedModule.{t, m, m} A :=
  cone (dgLiftHom S A P c hc)

/-- **The inclusion of `P` into its twisted extension.** -/
noncomputable abbrev twistedExtensionInclusion : P ⟶ twistedExtension S P c hc :=
  (conePackage (dgLiftHom S A P c hc)).inclusion

/-- **The projection of the twisted extension onto `A[S][1]`**, the free module on `S` with its
generators moved down one degree — the `A[Sᵢ₊₁]` of the source, whose generator of degree `n`
has as differential a cycle of degree `n + 1`. -/
noncomputable abbrev twistedExtensionProjection :
    twistedExtension S P c hc ⟶ shift (freeDGModule S A) :=
  (conePackage (dgLiftHom S A P c hc)).projection

/-- **`0 ⟶ P ⟶ P[S, c] ⟶ A[S][1] ⟶ 0` is an admissible short exact sequence**: it splits after
forgetting the differentials, the twisted extension being degreewise the direct sum of `P` and
of a piece of the free module. This is what propagates goodness, by Tag 0FSC. -/
theorem twistedExtension_isAdmissibleShortExact :
    IsAdmissibleShortExact (twistedExtensionInclusion S P c hc)
      (twistedExtensionProjection S P c hc) :=
  isAdmissibleShortExact_conePackage (dgLiftHom S A P c hc)

/-- **The twisted extension of a module flat as a graded module is flat as a graded module.**
This is condition (1) of Tag 0FSA propagating along the step: two out of three along the
admissible short exact sequence (Tag 0FSC), the third term being the shift of `A[S]`, which is
flat by Tag 0FSG. -/
theorem twistedExtension_isGradedFlat
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P)) :
    RelativeTensor.IsGradedFlat
      (GradedModule.ofDifferentialGraded (twistedExtension S P c hc)) :=
  (twistedExtension_isAdmissibleShortExact S P c hc).isGradedFlat_middle hP
    (isGradedFlat_shift (freeDGModule S A) (freeDGModule_isGradedFlat A S))

/-- **The twisted extension of a K-flat module is K-flat.** This is condition (2) of Tag 0FSA
propagating along the step: two out of three along the admissible short exact sequence (Tag
0FSC), the third term being the shift of `A[S]`, which is K-flat by Tag 0FSG. -/
theorem twistedExtension_isKFlat (hP : RelativeTensor.IsKFlat P) :
    RelativeTensor.IsKFlat (twistedExtension S P c hc) :=
  (twistedExtension_isAdmissibleShortExact S P c hc).isKFlat_middle hP
    (isKFlat_shift (freeDGModule S A) (freeDGModule_isKFlat S A))

/-- **Every cohomology class coming from `A[S]` dies in the twisted extension.** Since the
canonical generators of `A[S]` are closed and are sent to the chosen cycles
(`SheafOfModules.dgLiftHom_generator`), this says in particular that the class of each chosen
cycle becomes a boundary in `P[S, c]` — which is the point of the construction. -/
theorem homologyMap_comp_twistedExtensionInclusion_eq_zero (n : ℤ) :
    HomologicalComplex.homologyMap
      (dgLiftHom S A P c hc ≫ twistedExtensionInclusion S P c hc).toHomologicalComplex n = 0 :=
  (conePackage (dgLiftHom S A P c hc)).homologyMap_comp_inclusion_eq_zero n

/-- **The kernel-annihilation form of the previous result**: a morphism into `Hⁿ(P)` which
factors through `Hⁿ(A[S])` is annihilated by the map to `Hⁿ(P[S, c])`. This is the shape of the
hypothesis `hkill` of
`SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`, for a stage of the tower
whose classes to be killed are the ones carried by the chosen cycles. -/
theorem comp_homologyMap_twistedExtensionInclusion_eq_zero (n : ℤ)
    {Z : SheafOfModules.{m} (toRingCat J Osharp)} (g : Z ⟶ P.complex.homology n)
    (z : Z ⟶ (freeDGModule S A).complex.homology n)
    (hg : g = z ≫ HomologicalComplex.homologyMap (dgLiftHom S A P c hc).toHomologicalComplex n) :
    g ≫ HomologicalComplex.homologyMap
        (twistedExtensionInclusion S P c hc).toHomologicalComplex n = 0 := by
  rw [hg, Category.assoc, ← HomologicalComplex.homologyMap_comp,
    show (dgLiftHom S A P c hc).toHomologicalComplex ≫
        (twistedExtensionInclusion S P c hc).toHomologicalComplex =
      (dgLiftHom S A P c hc ≫ twistedExtensionInclusion S P c hc).toHomologicalComplex from rfl,
    homologyMap_comp_twistedExtensionInclusion_eq_zero S P c hc n, comp_zero]

/-- **Each chosen cycle becomes a boundary in the twisted extension**, for a cycle of `A[S]`
tested by an arbitrary sheaf of modules: its image in `P` under the lift — which on the
canonical generators is the chosen family `c` itself, by
`SheafOfModules.dgLiftHom_generator` — is the differential of a section of `P[S, c]`. This is
the construction's purpose, and the reason the classes of the chosen cycles die. -/
theorem exists_comp_d_eq_twistedExtension (n : ℤ)
    {Z : SheafOfModules.{m} (toRingCat J Osharp)}
    (x : Z ⟶ (freeDGModule S A).complex.X (n + 1))
    (hx : x ≫ (freeDGModule S A).complex.d (n + 1) (n + 1 + 1) = 0) :
    ∃ y : Z ⟶ (twistedExtension S P c hc).complex.X n,
      x ≫ (dgLiftHom S A P c hc).toHomologicalComplex.f (n + 1) ≫
          (twistedExtensionInclusion S P c hc).toHomologicalComplex.f (n + 1) =
        y ≫ (twistedExtension S P c hc).complex.d n (n + 1) :=
  (conePackage (dgLiftHom S A P c hc)).exists_comp_d_eq n x hx

end Extension

end SheafOfModules.DifferentialGradedModule

end
