module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorIdealPowers
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# The triangles of the `I`-adic filtration in a derived tensor product

Let `(C, J)` be a site, let `Λ` be a commutative ring and let `I ⊆ Λ` be an ideal. The proof of
Stacks Tag 094I runs an induction on `n` along the distinguished triangles

`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`.

This file constructs those triangles. They come from the short exact sequence of `Λ`-modules

`0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0`,

which the constant sheaf functor carries to a short exact sequence of sheaves because it is
exact. A short exact sequence of sheaves placed in degree zero is a distinguished triangle, and
tensoring with `K` is an exact functor of triangulated categories, so its image is again
distinguished.

## Main results

* `Stacks.ConstantSheaf.shortExact_idealPowShortComplex`: the sequence
  `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` of `Λ`-modules is short exact.
* `Stacks.ConstantSheaf.shortExact_map_constantSheaf`: **the constant sheaf functor is exact**,
  in the sense that it carries a short exact sequence of `Λ`-modules to a short exact sequence
  of sheaves of `Λ`-modules.
* `Stacks.ConstantSheaf.exists_distTriang_derivedTensorConstant`: **the triangles of Tag 094I**,
  for a bifunctor `T` exact in its second variable.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_graded`:
  the induction on `n` of
  `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow`
  with its triangle hypothesis replaced by exactness of `T` in the second variable. It still
  assumes the local constancy of the graded pieces, so it is **not** Tag 094I and carries no
  tag; it is what measures the remaining gap.

## Main definitions

* `Stacks.ConstantSheaf.idealPowSuccQuotIncl`: the injection `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹`.
* `Stacks.ConstantSheaf.quotIdealPowSuccProj`: the surjection `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ`.
* `Stacks.ConstantSheaf.idealPowShortComplex`: the two maps as a short complex.

## Implementation notes

`Stacks.ConstantSheaf.idealPowSuccQuot` is `Iⁿ` modulo the submodule of its elements lying in
`Iⁿ⁺¹`, so the map to `Λ/Iⁿ⁺¹` is the one induced by the inclusion of `Iⁿ` in `Λ`, and its
kernel is by construction exactly the submodule divided out. Both the range of that map and the
kernel of `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ` are the image of `Iⁿ` in `Λ/Iⁿ⁺¹`, which is exactness in the middle.

Exactness of the constant sheaf functor is read off its factorization
`constantSheaf = Functor.const Cᵒᵖ ⋙ presheafToSheaf`, which holds by definition. Limits and
colimits of presheaves are computed pointwise, so the first factor preserves both; the second is
left exact and is a left adjoint, so it preserves both as well. Left exactness is already an
instance, `Stacks.ConstantSheaf.constantSheaf_preservesFiniteLimits`; right exactness is
`Stacks.ConstantSheaf.preservesFiniteColimits_constantSheaf` below, and it has to spell the
left-adjoint colimit preservation out rather than call `inferInstance`, which would pick up
`CategoryTheory.presheafToSheaf_preservesFiniteColimits` instead.

**What the triangle needs of `T`, and what it does not.** Only exactness in the second variable
enters — a `CommShift` and an `IsTriangulated` instance for each `T.obj K`. No exactness in the
first variable, no boundedness estimate and no Noetherian hypothesis on `Λ` are used, which is
why this file is stated before any of them.

**Nothing here is tagged 094I.** The triangles were one of the two inputs carried as hypotheses
by
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow`;
the other, the local constancy of the graded pieces, is discharged in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`, where Tag 094I is
registered. See "What is not proved".

## What is not proved

The remaining hypothesis of this file's
`isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_graded`
is that each `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` has locally constant cohomology sheaves of finite type, which the
source obtains from the base change identification
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ = (K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹` together with Tag 094H. Neither of those
inputs is available: Tag 094H is itself not proved in full, and the identification needs a
derived tensor product over `Λ/I` and a change of rings comparison on `D(C, Λ)`, of which only
the case of a ring isomorphism exists here. That hypothesis is nevertheless *proved*, by a
different route, in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`: `Iⁿ/Iⁿ⁺¹` is a
finitely generated `Λ`-module killed by `I`, so iterating the syzygy over `Λ/I` computes each
cohomology sheaf of `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` out of finitely many copies of `K ⊗^L_Λ Λ/I`. That file,
which additionally asks of `T` the boundedness estimate this one does not use, is what carries
the 094I registration.

The bifunctor `T` is still a parameter rather than the derived tensor product of Tag 06YU: that
construction is a bifunctor on `D(SheafOfModules R)` for a sheaf of rings `R`, and no comparison
of that category with `D(Sheaf J (ModuleCat Λ))` exists in this development.

## References

* [Stacks Project, Tag 094I](https://stacks.math.columbia.edu/tag/094I)
* [Stacks Project, Tag 093J](https://stacks.math.columbia.edu/tag/093J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.ConstantSheaf

universe w v u s

/-! ### The short exact sequence `0 → Iⁿ/Iⁿ⁺¹ → Λ/Iⁿ⁺¹ → Λ/Iⁿ → 0` -/

section Modules

variable (Λ : Type s) [CommRing Λ] (I : Ideal Λ) (n : ℕ)

/-- **The injection `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹`**, induced by the inclusion of `Iⁿ` in `Λ`. It is
well defined because an element of `Iⁿ` lying in `Iⁿ⁺¹` has zero image in `Λ/Iⁿ⁺¹`. -/
def idealPowSuccQuotInclHom :
    (↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1))) →ₗ[Λ] (Λ ⧸ I ^ (n + 1)) :=
  Submodule.liftQ _ ((I ^ (n + 1)).mkQ ∘ₗ (I ^ n).subtype) <|
    le_of_eq (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])

/-- **The surjection `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ`** of `Λ`-modules, the canonical quotient map, well defined
because `Iⁿ⁺¹ ⊆ Iⁿ`. -/
def quotIdealPowSuccProjHom : (Λ ⧸ I ^ (n + 1)) →ₗ[Λ] (Λ ⧸ I ^ n) :=
  Submodule.liftQ _ (I ^ n).mkQ <| by
    rw [Submodule.ker_mkQ]
    exact Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The range of `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹` is the image of the submodule `Iⁿ`. -/
theorem range_idealPowSuccQuotInclHom :
    LinearMap.range (idealPowSuccQuotInclHom Λ I n)
      = Submodule.map (I ^ (n + 1)).mkQ (I ^ n) := by
  rw [idealPowSuccQuotInclHom, Submodule.range_liftQ, LinearMap.range_comp,
    Submodule.range_subtype]

/-- The map `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹` is injective: its kernel is exactly the submodule of `Iⁿ` that
was divided out. -/
theorem ker_idealPowSuccQuotInclHom :
    LinearMap.ker (idealPowSuccQuotInclHom Λ I n) = ⊥ :=
  Submodule.ker_liftQ_eq_bot _ _ _
    (le_of_eq (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]))

/-- The kernel of `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ` is the image of the submodule `Iⁿ`. -/
theorem ker_quotIdealPowSuccProjHom :
    LinearMap.ker (quotIdealPowSuccProjHom Λ I n)
      = Submodule.map (I ^ (n + 1)).mkQ (I ^ n) := by
  rw [quotIdealPowSuccProjHom, Submodule.ker_liftQ, Submodule.ker_mkQ]

/-- The map `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ` is surjective, being a quotient map. -/
theorem range_quotIdealPowSuccProjHom :
    LinearMap.range (quotIdealPowSuccProjHom Λ I n) = ⊤ := by
  rw [quotIdealPowSuccProjHom, Submodule.range_liftQ, Submodule.range_mkQ]

/-- **The injection `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹`** as a morphism of `ModuleCat`. -/
def idealPowSuccQuotIncl : idealPowSuccQuot Λ I n ⟶ ModuleCat.of Λ (Λ ⧸ I ^ (n + 1)) :=
  ModuleCat.ofHom (idealPowSuccQuotInclHom Λ I n)

/-- **The surjection `Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ`** as a morphism of `ModuleCat`. -/
def quotIdealPowSuccProj : ModuleCat.of Λ (Λ ⧸ I ^ (n + 1)) ⟶ ModuleCat.of Λ (Λ ⧸ I ^ n) :=
  ModuleCat.ofHom (quotIdealPowSuccProjHom Λ I n)

/-- **The short complex `Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ`** of `Λ`-modules. -/
@[simps]
def idealPowShortComplex : ShortComplex (ModuleCat.{s} Λ) where
  X₁ := idealPowSuccQuot Λ I n
  X₂ := ModuleCat.of Λ (Λ ⧸ I ^ (n + 1))
  X₃ := ModuleCat.of Λ (Λ ⧸ I ^ n)
  f := idealPowSuccQuotIncl Λ I n
  g := quotIdealPowSuccProj Λ I n
  zero := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 y.2

/-- **The sequence `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` is short exact.** The first map is
injective because its kernel is exactly the submodule divided out of `Iⁿ`, the second is
surjective because it is a quotient map, and the range of the first and the kernel of the
second are both the image of `Iⁿ` in `Λ/Iⁿ⁺¹`. -/
theorem shortExact_idealPowShortComplex : (idealPowShortComplex Λ I n).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (idealPowSuccQuotInclHom Λ I n)
      = LinearMap.ker (quotIdealPowSuccProjHom Λ I n)
    rw [range_idealPowSuccQuotInclHom, ker_quotIdealPowSuccProjHom]
  · change Mono (idealPowSuccQuotIncl Λ I n)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (idealPowSuccQuotInclHom Λ I n)
    rw [← LinearMap.ker_eq_bot]
    exact ker_idealPowSuccQuotInclHom Λ I n
  · change Epi (quotIdealPowSuccProj Λ I n)
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (quotIdealPowSuccProjHom Λ I n)
    rw [← LinearMap.range_eq_top]
    exact range_quotIdealPowSuccProjHom Λ I n

end Modules

/-! ### Exactness of the constant sheaf functor -/

section Sheaves

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v w)) [CommRing Λ]

/-- **Sheafification of presheaves of `Λ`-modules preserves colimits of any shape**, being a
left adjoint. Supplied explicitly, as a `PreservesColimitsOfSize.{0,0}` narrowed to the shape
asked for, because `inferInstance` would otherwise select
`CategoryTheory.presheafToSheaf_preservesFiniteColimits`. -/
theorem presheafToSheaf_preservesColimitsOfShape (K : Type) [SmallCategory K] :
    PreservesColimitsOfShape K (presheafToSheaf J (ModuleCat.{max u v w} Λ)) := by
  have h : PreservesColimitsOfSize.{0, 0} (presheafToSheaf J (ModuleCat.{max u v w} Λ)) :=
    (sheafificationAdjunction J (ModuleCat.{max u v w} Λ)).leftAdjoint_preservesColimits
  exact h.preservesColimitsOfShape

/-- **The constant sheaf functor on modules preserves finite colimits.** It is the constant
presheaf functor, which preserves all colimits because colimits of presheaves are computed
pointwise, followed by sheafification, which is a left adjoint.

The companion left exactness is `Stacks.ConstantSheaf.constantSheaf_preservesFiniteLimits`.
Unlike `Stacks.ConstantSheaf.preservesFiniteColimits_constantSheaf_over`, which identifies the
constant sheaf functor on a slice site with the left adjoint of evaluation at the terminal
object `𝟙 V`, this needs no terminal object and so applies to the site `(C, J)` itself. -/
@[sga "4 I 5.8.3" "Clause 1, special case"]
instance preservesFiniteColimits_constantSheaf :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{max u v w} Λ)) := by
  refine ⟨fun K _ _ => ?_⟩
  have hconst : PreservesColimitsOfShape K
    (Functor.const Cᵒᵖ (C := ModuleCat.{max u v w} Λ)) := inferInstance
  exact @comp_preservesColimitsOfShape _ _ _ _ K _ _ _ _ _ hconst
    (presheafToSheaf_preservesColimitsOfShape J Λ K)

/-- **The constant sheaf functor carries a short exact sequence of `Λ`-modules to a short exact
sequence of sheaves of `Λ`-modules**, being exact: the constant presheaf functor preserves all
limits and all colimits, and sheafification is left exact and a left adjoint. -/
theorem shortExact_map_constantSheaf (S : ShortComplex (ModuleCat.{max u v w} Λ))
    (hS : S.ShortExact) :
    (S.map (constantSheaf J (ModuleCat.{max u v w} Λ))).ShortExact :=
  hS.map_of_exact (constantSheaf J (ModuleCat.{max u v w} Λ))

/-- **The constant sheaves of the `I`-adic filtration form a short exact sequence**
`0 ⟶ (Iⁿ/Iⁿ⁺¹)̲ ⟶ (Λ/Iⁿ⁺¹)̲ ⟶ (Λ/Iⁿ)̲ ⟶ 0`. -/
theorem shortExact_map_constantSheaf_idealPowShortComplex (I : Ideal Λ) (n : ℕ) :
    ((idealPowShortComplex Λ I n).map
      (constantSheaf J (ModuleCat.{max u v w} Λ))).ShortExact :=
  shortExact_map_constantSheaf J Λ _ (shortExact_idealPowShortComplex Λ I n)

/-! ### The triangles of Tag 094I -/

end Sheaves

/-- **An exact functor carries the triangle of a short exact sequence to a distinguished
triangle.** This is `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`
followed by `CategoryTheory.Functor.map_distinguished`, stated in the existential form in which
the induction of Tag 094I consumes it.

It is stated for an abstract `F` and an abstract short complex on purpose: instantiating the
three vertices first and only then asking for the triangle makes the elaborator compare the
written out composite functors, which it cannot do inside the heartbeat budget. -/
theorem exists_distTriang_map_singleTriangle {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory.{w} A] (F : DerivedCategory A ⥤ DerivedCategory A) [F.CommShift ℤ]
    [F.IsTriangulated] (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ (f : F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁) ⟶
        F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₂))
      (g : F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₂) ⟶
        F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃))
      (h : F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ⟶
        (F.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory A) :=
  ⟨_, _, _, F.map_distinguished _ hS.singleTriangle_distinguished⟩

section Triangles

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v w)) [CommRing Λ]

attribute [local instance] HasDerivedCategory.standard

/-- **The distinguished triangles of the proof of Stacks Tag 094I.** For a bifunctor `T` on the
derived category of sheaves of `Λ`-modules which is exact in its second variable, and for any
`K` and any `n`, the derived tensor products of `K` with the three terms of the short exact
sequence `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` sit in a distinguished triangle

`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`.

The sequence of constant sheaves placed in degree zero is a distinguished triangle, and
`K ⊗^L_Λ -` is an exact functor of triangulated categories, so it carries that triangle to a
distinguished one. -/
theorem exists_distTriang_derivedTensorConstant
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (I : Ideal Λ) (n : ℕ) :
    ∃ (f : derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n) ⟶
        derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ (n + 1))))
      (g : derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ (n + 1))) ⟶
        derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)))
      (h : derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)) ⟶
        (derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) :=
  exists_distTriang_map_singleTriangle (T.obj K)
    ((idealPowShortComplex Λ I n).map (constantSheaf J (ModuleCat.{max u v w} Λ)))
    (shortExact_map_constantSheaf_idealPowShortComplex J Λ I n)

/-- **The induction on `n` of Tag 094I with its triangle hypothesis discharged.** Let `T` be a
bifunctor on the derived category of sheaves of `Λ`-modules standing for the derived tensor
product over the Noetherian ring `Λ`, exact in its second variable, let `K` be an object of
that derived category and let `I ⊆ Λ` be an ideal. Suppose each `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` has locally
constant cohomology sheaves of finite type. If `K ⊗^L_Λ Λ/I` has locally constant cohomology
sheaves of finite type, then so does `K ⊗^L_Λ Λ/Iⁿ` for every `n ≥ 1`.

This is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow`
with its triangle hypothesis replaced by exactness of `T` in the second variable, the triangles
themselves being supplied by
`Stacks.ConstantSheaf.exists_distTriang_derivedTensorConstant`.

**This is not Tag 094I and carries no tag.** The hypothesis `hgraded` — that the graded pieces
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` have locally constant cohomology sheaves of finite type — is an assumption
the source does not make: there it is derived from the base change identification
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ = (K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹` together with Tag 094H, neither of which is
available here. The hypothesis `hbase` is by contrast the source's own antecedent. What this
declaration records is that the triangles of
`Stacks.ConstantSheaf.exists_distTriang_derivedTensorConstant` do fit the slot the induction
asks for, so that what remains of Tag 094I is exactly `hgraded`.

`hgraded` is discharged, for a `T` which also carries bounds above to their sum and a `K` in
`D^-`, in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`, whose
`..._homology_tensor_quotientIdealPow_of_isLE` is this declaration with `hgraded` supplied.
Tag 094I is registered there. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_graded
    [IsNoetherianRing Λ]
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (I : Ideal Λ)
    (hgraded : ∀ n : ℕ, 1 ≤ n → ∀ i : ℤ,
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          (derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n))))
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)))) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow J Λ T K I
    (fun m _ => exists_distTriang_derivedTensorConstant J Λ T K I m) hgraded hbase n hn

end Triangles

end Stacks.ConstantSheaf

end
