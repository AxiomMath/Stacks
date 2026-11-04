module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Quasicoherent

/-!
# What the affine derived Spec–Γ adjunction transports without the equivalence

Let `R` be a commutative ring. `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is the
adjunction `derivedTilde R ⊣ derivedGlobalSectionsQuasicoherent R` between `D(R)` and
`D_QCoh(𝒪_{Spec R})`, and it holds *unconditionally*; the assertion of [Stacks, Tag 06Z0] that
these two functors are mutually inverse equivalences does not, and is open in this repository.
This file isolates two statements which the adjunction alone — or the adjunction together with a
single invertible counit — already supplies, and which were previously available only under the
full hypothesis `(derivedTilde R).IsEquivalence`.

The first is a transport of *factorisations*. A statement of the form "every morphism out of
`R[0]` into `E` factors through a given morphism `u` of `D(R)`" — the shape of
[Stacks, Tag 08E3], whose conclusion is that every morphism `R[0] ⟶ E` factors through the
canonical map from `R[0]` to a Koszul complex on a power of a sequence — is a statement about
hom-sets of `D(R)`, and the hom-set bijection of an adjunction carries it verbatim to
`D_QCoh(𝒪_{Spec R})`. No full faithfulness and no essential surjectivity are involved: the
adjunction's naturality in its left variable is the whole proof.

The second is *generation*. `𝒪_{Spec R}[0] = derivedTilde R (R[0])` generating
`D_QCoh(𝒪_{Spec R})` is the affine case of [Stacks, Tag 09IS], and
`AlgebraicGeometry.isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit` obtains it by
transporting the generation of `D(R)` by `R[0]` across the equivalence of Tag 06Z0. Only half of
that equivalence is needed, and only pointwise: if the counit of the adjunction is invertible at
the object `Y` in question — that is, if `Y` lies in the essential image of derived
sheafification — then `Y` right orthogonal to the shifts of `𝒪_{Spec R}[0]` forces
`RΓ(Spec R, Y) = 0` by the adjunction, hence `Y ≅ derivedTilde R (RΓ(Spec R, Y)) = 0`. Full
faithfulness, i.e. unbounded affine vanishing ([Stacks, Tag 08D4]), is not used.

## Main results

* `CategoryTheory.Adjunction.exists_comp_map_iff` — for an adjunction `F ⊣ G`, a morphism
  `F X ⟶ E` factors through `F.map u` exactly when its adjunct `X ⟶ G E` factors through `u`.
* `AlgebraicGeometry.exists_factor_derivedTilde_map_iff` — that bijection for derived
  sheafification: **a factorisation statement in `D(R)` transports to `D_QCoh(𝒪_{Spec R})` with
  no hypothesis beyond the adjunction.**
* `AlgebraicGeometry.isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit_of_isIso_counit` —
  **generation of `D_QCoh(𝒪_{Spec R})` by `𝒪_{Spec R}[0]` at an object where the counit is
  invertible**, with no appeal to `(derivedTilde R).IsEquivalence`.

## Implementation notes

No `@[stacks]` attribute appears below. Tag 06Z0 is decomposed into thirteen declarations and the
audit scanner keys on the bare four-character tag, so a single attribute anywhere in this cluster
would render the whole tag formalized; nothing here is one of those thirteen statements in any
case. No attribute for Tag 09IS either: the second result below is the affine case of that tag's
generation half, and still carries a hypothesis.

The derived categories in force are the locally small ones, as everywhere in this cluster;
`CategoryTheory.HasDerivedCategory.standard` is not interchangeable with them, and for the
generation statement that is forced rather than chosen — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration.lean`.

The counit hypothesis is taken at the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction`, the adjunction between the two functors
Tag 06Z0 names, rather than at the counit of the ambient
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` which
`AlgebraicGeometry.essSurj_derivedTilde_of_isIso_counit` uses. The two are identified by
`CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app`; that identification is not
established here and is not needed, since the statement below is phrased entirely in terms of
the restricted adjunction.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Adjunction

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- **Factorisations transport along an adjunction.** Let `F ⊣ G`, let `u : X ⟶ Y` be a morphism
of the source category and let `s : F X ⟶ E`. Then `s` factors through `F.map u` exactly when the
adjunct `s' : X ⟶ G E` of `s` factors through `u`, and the two factors correspond under the same
hom-set bijection.

Both directions are the naturality of the bijection in its left variable,
`CategoryTheory.Adjunction.homEquiv_naturality_left`; nothing is assumed about `F` beyond its
having a right adjoint. -/
theorem exists_comp_map_iff {X Y : C} (u : X ⟶ Y) {E : D} (s : F.obj X ⟶ E) :
    (∃ t : F.obj Y ⟶ E, s = F.map u ≫ t) ↔
      ∃ t' : Y ⟶ G.obj E, adj.homEquiv X E s = u ≫ t' := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨adj.homEquiv Y E t, adj.homEquiv_naturality_left u t⟩
  · rintro ⟨t', ht'⟩
    refine ⟨(adj.homEquiv Y E).symm t', (adj.homEquiv X E).injective ?_⟩
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, ht']

end

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-! ### Factorisations in `D(R)` transport to `D_QCoh(𝒪_{Spec R})` -/

/-- **A factorisation statement in `D(R)` transports to `D_QCoh(𝒪_{Spec R})` along the
adjunction of [Stacks, Tag 06Z0], with no further hypothesis.** A morphism
`s : derivedTilde R M ⟶ E` factors through `derivedTilde R u` for a morphism `u : M ⟶ N` of
`D(R)` exactly when the adjunct of `s`, a morphism `M ⟶ RΓ(Spec R, E)`, factors through `u`.

Taken at `M = R[0]` and `u` the canonical morphism from `R[0]` to a Koszul complex on a power of
a sequence, this is how the conclusion of [Stacks, Tag 08E3] — a statement about the hom-sets of
`D(R)` — becomes a statement about the hom-sets of `D_QCoh(𝒪_{Spec R})`. The equivalence of
Tag 06Z0 is not needed for it; the adjunction, which is unconditional, is enough. -/
theorem exists_factor_derivedTilde_map_iff {M N : DerivedCategory (ModuleCat.{u} R)} (u : M ⟶ N)
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (s : (derivedTilde R).obj M ⟶ E) :
    (∃ t : (derivedTilde R).obj N ⟶ E, s = (derivedTilde R).map u ≫ t) ↔
      ∃ t' : N ⟶ (derivedGlobalSectionsQuasicoherent R).obj E,
        (derivedTildeQuasicoherentAdjunction R).homEquiv M E s = u ≫ t' :=
  (derivedTildeQuasicoherentAdjunction R).exists_comp_map_iff u s

/-! ### Generation of `D_QCoh(𝒪_{Spec R})` from a single invertible counit -/

/-- **The shifts of `derivedTilde R (R[0]) = 𝒪_{Spec R}[0]` detect an object of
`D_QCoh(𝒪_{Spec R})` at which the counit is invertible.** If the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible at `Y` — equivalently, if
`Y` is isomorphic to the derived sheafification of a complex of `R`-modules — and `Y` receives
only zero morphisms from the shifts of `derivedTilde R (R[0])`, then `Y` is zero.

This is the generation half of the affine case of [Stacks, Tag 09IS] with its hypothesis reduced
from the full equivalence of [Stacks, Tag 06Z0] to the essential surjectivity half of it, taken
at the single object `Y`:
`AlgebraicGeometry.isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit` assumes
`(derivedTilde R).IsEquivalence` and transports the generation of `D(R)` by `R[0]` across the
resulting equivalence. In fact the hom-set bijection of the adjunction already carries the
orthogonality hypothesis to `RΓ(Spec R, Y)`, where
`Stacks.Duality.isZero_of_rightOrthogonal_shiftClosure_derivedUnit` applies; the counit is used
once, to carry `RΓ(Spec R, Y) = 0` back to `Y = 0`. Unbounded affine vanishing
([Stacks, Tag 08D4]), which is the other half of Tag 06Z0, is not used. -/
theorem isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit_of_isIso_counit
    (Y : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (hc : IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app Y))
    (hY : ((ofObj fun _ : PUnit.{u + 1} => (derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).shiftClosure ℤ).rightOrthogonal Y) :
    IsZero Y := by
  rw [CategoryTheory.Pretriangulated.rightOrthogonal_shiftClosure_ofObj_iff] at hY
  have h0 : IsZero ((derivedGlobalSectionsQuasicoherent R).obj Y) := by
    refine Stacks.Duality.isZero_of_rightOrthogonal_shiftClosure_derivedUnit R _
      ((CategoryTheory.Pretriangulated.rightOrthogonal_shiftClosure_ofObj_iff _ _).2
        fun i a g => ?_)
    have h1 : ((derivedTilde R).commShiftIso a).inv.app
          (Stacks.Duality.singleGenerator (ModuleCat.of R R) i) ≫
        ((derivedTildeQuasicoherentAdjunction R).homEquiv _ Y).symm g = 0 := hY i a _
    have h2 : ((derivedTildeQuasicoherentAdjunction R).homEquiv _ Y).symm g = 0 := by
      rw [← cancel_epi (((derivedTilde R).commShiftIso a).inv.app
        (Stacks.Duality.singleGenerator (ModuleCat.of R R) i)), comp_zero]
      exact h1
    have h3 := (((derivedTildeQuasicoherentAdjunction R).homEquiv _ Y).apply_symm_apply g).symm
    rw [h2, Adjunction.homAddEquiv_zero] at h3
    exact h3
  have := hc
  exact ((derivedTilde R).map_isZero h0).of_iso
    (asIso ((derivedTildeQuasicoherentAdjunction R).counit.app Y)).symm

end AlgebraicGeometry

end
