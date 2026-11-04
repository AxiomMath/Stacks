module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingModuleProperCharts
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedSeparatedNagata
public import StacksFrontier.RingTheory.Dualizing.NormalizedSingleSelfField

/-!
# The dualizing module of a scheme of finite type over a field

Let `X` be a scheme of finite type over a field `k` with structure morphism `f : X ⟶ Spec(k)`,
for the upper shriek functors of Nagata compactifications. Following [Stacks, Tag 0AWJ]:

* `ω_X^•` is the dualizing complex normalized relative to `k[0]`
  (`Stacks.Duality.normalizedDualizingComplex` at `k[0]`, which is a dualizing complex on
  `Spec(k)`); it is a dualizing complex, unique up to unique isomorphism;
* `ω_X = H^{-dim(X)}(ω_X^•)` is the dualizing module of `X`
  (`Stacks.Duality.dualizingModuleOfCompactifications` at the Nagata compactifications);
* if `X` is separated over `k`, then `ω_X^• = f^! 𝒪_{Spec(k)}`, with `f^!` the upper shriek functor
  of [Stacks, Tag 0A9Y] at any compactification of `f`;
* if `X` is proper over `k`, this is a special case of [Stacks, Tag 0AWI]: `ω_X^• = a(𝒪_{Spec(k)})`
  for `a` the right adjoint of `Rf_*`, `ω_X` is the relative dualizing module of that example, and
  `ω_X` is a coherent dualizing module.

## Implementation notes

Equidimensionality of `X`, the standing hypothesis of the example, is not needed for any of these
statements, so it is dropped.

## References

* [Stacks Project, Tag 0AWJ](https://stacks.math.columbia.edu/tag/0AWJ)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [LocallyOfFiniteType p] [QuasiCompact p]

/-- **[Stacks, Tag 0AWJ], the complex `ω_X^•`.** For `X` of finite type over a field `k`, the
dualizing complex `ω_X^•` normalized relative to `k[0]` (`k[0]` being a dualizing complex on
`Spec(k)`) is a dualizing complex, and it is unique up to unique isomorphism: any complex
normalized relative to `k[0]` is isomorphic to it by exactly one isomorphism compatible with
the normalizations. -/
@[stacks 0AWJ "omega_X^bullet, the dualizing complex normalized relative to k[0]"]
theorem isDualizingComplex_normalizedDualizingComplex_of_field :
    haveI := (isFiniteTypeOverNoetherian_of_field p).source_noetherian
    IsDualizingComplex (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
        (derivedStructureSheafPlus (Spec (.of k)))
        (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj.obj ∧
    ∀ 𝒦 : NormalizedOnOpens UpperShriek.nagata (isFiniteTypeOverNoetherian_of_field p)
        (derivedStructureSheafPlus (Spec (.of k))),
      ∃! e : (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex ≅ 𝒦.complex,
        ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
          (UpperShriek.nagata.shriek W.ι
              ((isFiniteTypeOverNoetherian_of_field p).isShriekable_ι W)).mapIso e ≪≫
            𝒦.localIso W hW =
          (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
            (derivedStructureSheafPlus (Spec (.of k)))
            (isDualizingComplex_derivedStructureSheafPlus_of_field k)).localIso W hW :=
  ⟨NormalizedOnOpens.isDualizingComplex_ofCompactifications nagataCompactification
      (isDualizingComplex_derivedStructureSheafPlus_of_field k) _,
    fun 𝒦 => NormalizedOnOpens.existsUnique_iso_ofCompactifications nagataCompactification
      (isDualizingComplex_derivedStructureSheafPlus_of_field k) _ 𝒦⟩

/-- **[Stacks, Tag 0AWJ], the module `ω_X`.** For `X` of finite type over a field `k`, the
dualizing module `ω_X` is `H^{-dim(X)}(ω_X^•)`, the cohomology sheaf in degree minus the dimension
of `X` of the dualizing complex normalized relative to `k[0]`. -/
@[stacks 0AWJ "omega_X = H^{-dim X}(omega_X^bullet)"]
theorem dualizingModuleOfCompactifications_nagata_eq :
    dualizingModuleOfCompactifications nagataCompactification p =
      (DerivedCategory.homologyFunctor X.Modules
        (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj
        (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj.obj :=
  rfl

/-- **[Stacks, Tag 0AWJ], the separated case.** If `X` is separated and of finite type over a
field `k`, then `ω_X^• = f^! 𝒪_{Spec(k)}`, `f : X ⟶ Spec(k)` being the structure morphism and
`f^!` the upper shriek functor of [Stacks, Tag 0A9Y] at any compactification `j` of `f`: there is
exactly one isomorphism `ω_X^• ≅ f^!_j 𝒪_{Spec(k)}` which, followed by the comparison with the
Nagata compactification, carries the normalization of `ω_X^•` on each open `W` separated over `k`
to the canonical `(f^! 𝒪_{Spec(k)})|_W ≅ (W → Spec(k))^! 𝒪_{Spec(k)}`. -/
@[stacks 0AWJ "for X separated over k, omega_X^bullet = f^! O_{Spec k}"]
theorem existsUnique_iso_upperShriekPlus_of_field [IsSeparated p]
    (j : CompactificationOf (Over.mk p)) :
    haveI := isNoetherian_spec_of_field k
    ∃! e : (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
        (derivedStructureSheafPlus (Spec (.of k)))
        (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex ≅
      (upperShriekPlus (ftsHomOf p (isShriekable_of_field p).separatedFiniteType
        (isSeparatedFiniteType_id _) (Category.comp_id p)) j).obj
        (derivedStructureSheafPlus (Spec (.of k))),
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (UpperShriek.nagata.shriek W.ι
            ((isFiniteTypeOverNoetherian_of_field p).isShriekable_ι W)).mapIso
            (e ≪≫ (DominatingCompactification.upperShriekPlusIso (ftsHomOf p
              (isShriekable_of_field p).separatedFiniteType (isSeparatedFiniteType_id _)
              (Category.comp_id p)) j
              (nagataCompactification p (isShriekable_of_field p))).app
              (derivedStructureSheafPlus (Spec (.of k)))) ≪≫
          upperShriekLocalIso UpperShriek.nagata (isFiniteTypeOverNoetherian_of_field p)
            (isShriekable_of_field p) (derivedStructureSheafPlus (Spec (.of k))) hW =
        (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k)).localIso W hW :=
  NormalizedOnOpens.existsUnique_iso_upperShriekPlus_nagata
    (isDualizingComplex_derivedStructureSheafPlus_of_field k) (isShriekable_of_field p) _ j

/-- **[Stacks, Tag 0AWJ], the proper case: `ω_X^• = a(𝒪_{Spec(k)})`.** If `X` is proper over a
field `k`, the dualizing complex normalized relative to `k[0]` is the twisted inverse image
`a(𝒪_{Spec(k)})` of [Stacks, Tag 0A9E], that is, the relative dualizing complex `f^! ω_S^•` of
[Stacks, Tag 0AWI] for `S = Spec(k)` and `ω_S^• = k[0]`. -/
@[stacks 0AWJ "for X proper over k, omega_X^bullet = a(O_{Spec k}), the complex of Example 0AWI"]
def normalizedDualizingComplexIsoRelativeDualizingComplexOfField [IsProper p] :
    haveI := isNoetherian_spec_of_field k
    haveI := (isFiniteTypeOverNoetherian_of_field p).source_noetherian
    (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
        (derivedStructureSheafPlus (Spec (.of k)))
        (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj ≅
      relativeDualizingComplex p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) :=
  have := isNoetherian_spec_of_field k
  have := (isFiniteTypeOverNoetherian_of_field p).source_noetherian
  (ObjectProperty.ι _).mapIso
      (NormalizedOnOpens.existsUnique_iso_shriek_ofCompactifications nagataCompactification
        (isDualizingComplex_derivedStructureSheafPlus_of_field k) (isShriekable_of_field p)
        (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k))).exists.choose ≪≫
    (UpperShriek.shriekOfIsoOfIsProper nagataCompactification p (isShriekable_of_field p)).app
      (derivedStructureSheafPlus (Spec (.of k)))

/-- **[Stacks, Tag 0AWJ], the proper case is a special case of [Stacks, Tag 0AWI].** If `X` is
proper over a field `k`, then `ω_X` is the relative dualizing module of [Stacks, Tag 0AWI] for
`S = Spec(k)` and `ω_S^• = k[0]` (a normalized dualizing complex over the local ring `k`); hence
`ω_X` is coherent and, `X` being nonempty, a dualizing module: `ω_X^•` is a dualizing complex and
`-dim(X)` is the least degree in which it has nonzero cohomology. -/
@[stacks 0AWJ "for X proper over k, this is a special case of Example 0AWI"]
theorem dualizingModuleOfCompactifications_nagata_of_isProper [IsProper p] :
    haveI := isNoetherian_spec_of_field k
    haveI := (isFiniteTypeOverNoetherian_of_field p).source_noetherian
    Nonempty (dualizingModuleOfCompactifications nagataCompactification p ≅
        relativeDualizingModule p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ∧
      (dualizingModuleOfCompactifications nagataCompactification p).IsCoherent ∧
      (Nonempty X → IsDualizingModuleOf
        (dualizingModuleOfCompactifications nagataCompactification p)
        (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj.obj
        (-(natDim X : ℤ))) := by
  have := isNoetherian_spec_of_field k
  have := (isFiniteTypeOverNoetherian_of_field p).source_noetherian
  have hF : IsField Γ(Spec (.of k), ⊤) := MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  let := hF.toField
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) := inferInstance
  have : IsLocalRing Γ(Spec (.of k), ⊤) := inferInstance
  have h0AWI := isDualizingModuleOf_relativeDualizingModule p
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Spec (.of k), ⊤)) 0).obj
      (ModuleCat.of Γ(Spec (.of k), ⊤) Γ(Spec (.of k), ⊤)))
    (Dualizing.isNormalizedDualizingComplex_single_self_of_isField hF)
    (isTildeModelOnAnyModel_unit ⊤ (isAffineOpen_top _))
  let e := normalizedDualizingComplexIsoRelativeDualizingComplexOfField k p
  let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor X.Modules i).obj
      (normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field p)
        (derivedStructureSheafPlus (Spec (.of k)))
        (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj.obj ≅
      (DerivedCategory.homologyFunctor X.Modules i).obj
        (relativeDualizingComplex p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj := fun i =>
    (DerivedCategory.homologyFunctor X.Modules i).mapIso ((ObjectProperty.ι _).mapIso e)
  have hK := (isDualizingComplex_normalizedDualizingComplex_of_field k p).1
  refine ⟨⟨eH _⟩, isCoherent_homology_of_isDualizingComplex hK _, fun hX => ?_⟩
  obtain ⟨-, h⟩ := h0AWI
  have hd := h hX
  exact ⟨hK, fun hz => hd.nonzero (hz.of_iso (eH _).symm),
    fun i hi => (hd.isZero_of_lt i hi).of_iso (eH i), rfl⟩

end Stacks.Duality

end
