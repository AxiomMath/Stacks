module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportStalk
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Regular sections of an invertible module and the associated points of the scheme

Let `X` be a locally Noetherian scheme, let `L` be an invertible `𝒪_X`-module and let
`s ∈ Γ(X, L)`. Then `s` is a regular section — multiplication by `s` is a monomorphism
`𝒪_X ⟶ L` — exactly when `s` does not vanish at any associated point of `X`, that is, when the
germ of `s` at every associated point avoids `𝔪_x L_x`.

## Main results

* `Stacks.Divisors.isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul`: the
  characterization itself.
* `Stacks.Divisors.injective_smul_iff_notMem_maximalIdeal_smul_top`: the algebraic core. Over a
  local ring `R` whose maximal ideal is an associated prime of `R`, multiplication by an element
  `s` of a free rank-one module `M` is injective exactly when `s ∉ 𝔪 M`.
* `Stacks.Divisors.injective_mapFun_iff_notMem_maximalSmul`: the geometric form of the core,
  at an associated point of `X`.
* `Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible`: the stalk of an invertible
  module is free of rank one.

## Implementation notes

Non-vanishing of `s` at `x` is expressed intrinsically, as `s_x ∉ 𝔪_x L_x`
(`Stacks.ModuleStalk.maximalSmul`), rather than through a local trivialization of `L`. This is
the same condition that [Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY) uses to
define the nonvanishing locus of a section.

The two implications use different inputs. For "regular implies non-vanishing" a
monomorphism of sheaves is injective on stalks, so the stalk map `r ↦ r · s_x` is injective, and
the algebraic core turns that into `s_x ∉ 𝔪_x L_x` — this is where the associated-point
hypothesis is used, as it supplies the element of `𝒪_{X,x}` annihilated by exactly `𝔪_x`. For the
converse, [Stacks, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
(`Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints`)
says that a morphism of quasi-coherent modules on a locally Noetherian scheme is a monomorphism
as soon as it is injective on the stalks at the associated points of its source; the source here
is the structure sheaf, whose associated points are by definition those of `X`.

The stalk of `L` carries two equal but not definitionally equal `𝒪_{X,x}`-module structures in
this library. Statements here use `Stacks.ModuleStalk.stalkModule`, which is the one
`Stacks.Divisors.associatedPoints` and Tag 0AVL are phrased over;
`Stacks.NonvanishingPullback.stalkModule_eq_scheme` transports the rank-one freeness of the
stalk of an invertible module, which is proved over the other.

## References

* [Stacks Project, Tag 0AYL](https://stacks.math.columbia.edu/tag/0AYL)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk)
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.Divisors

/-- **The algebraic core of [Stacks, Tag 0AYL].** Let `R` be a local ring whose maximal ideal is
an associated prime of `R` itself, and let `M` be a free `R`-module of rank one. Then
multiplication by `s ∈ M`, as a map `R → M`, is injective exactly when `s ∉ 𝔪 M`.

If `s ∈ 𝔪 M` then, `M` being free of rank one, `s` corresponds to an element of `𝔪`, which
annihilates the element of `R` whose annihilator is exactly `𝔪`; conversely if `s ∉ 𝔪 M` then its
coordinate is a unit, and multiplication by a unit is injective. -/
theorem injective_smul_iff_notMem_maximalIdeal_smul_top
    (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (hm : IsAssociatedPrimeStacks R R (IsLocalRing.maximalIdeal R)) (s : M) :
    Function.Injective (fun r : R ↦ r • s) ↔
      s ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  have hs : s ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔
      e s ∈ IsLocalRing.maximalIdeal R := by
    have he : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).map e.toLinearMap =
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) := by
      rw [Submodule.map_smul'', Submodule.map_top, e.range]
    have h := Submodule.mem_map_equiv
      (p := IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (e := e) (x := e s)
    rw [he, e.symm_apply_apply] at h
    simpa using h.symm
  rw [hs]
  constructor
  · intro hinj hes
    obtain ⟨hprime, t, ht⟩ := hm
    have ht0 : t ≠ 0 := fun h ↦ hprime.ne_top (by rw [← ht]; simp [h])
    refine ht0 (hinj (e.injective ?_))
    rw [e.map_smul]
    rw [← ht] at hes
    simpa [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hes
  · intro hs r₁ r₂ h
    have hu : IsUnit (e s) := by simpa [IsLocalRing.mem_maximalIdeal] using hs
    apply hu.mul_right_cancel
    simpa [smul_eq_mul] using congrArg e h

/-- Transport of the associated-prime property along a linear equivalence. -/
theorem isAssociatedPrimeStacks_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) {p : Ideal R}
    (hp : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R N p := by
  obtain ⟨hp, m, hm⟩ := hp
  refine ⟨hp, e m, ?_⟩
  rw [← hm]
  ext r
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  rw [← e.map_smul, e.map_eq_zero_iff]

variable {X : Scheme.{u}}

/-- The structure sheaf of a scheme, regarded as a module over itself. The associated points of
`X` are by definition the associated points of this module. -/
noncomputable def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The associated points of `X` are the associated points of its structure sheaf, read as a
module over itself. -/
theorem schemeAssociatedPoints_eq (X : Scheme.{u}) :
    schemeAssociatedPoints X = associatedPoints (structureModule X) := rfl

/-- The structure sheaf is quasi-coherent as a module over itself. This is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`, restated at the
`Stacks.Divisors.structureModule` spelling so that instance search finds it. -/
instance isQuasicoherent_structureModule (X : Scheme.{u}) :
    (structureModule X).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X

/-- The unit section of `𝒪_X` over the whole space, read as a global section of the structure
sheaf regarded as a module over itself. -/
noncomputable def unitSectionTop (X : Scheme.{u}) : Γ(structureModule X, ⊤) :=
  (1 : ToType (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))

/-- The stalk at a point of an invertible `𝒪_X`-module is free of rank one over the local ring
of `X` at that point. This is the converse half of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) at a single stalk, transported to
the module structure `Stacks.ModuleStalk.stalkModule`. -/
theorem nonempty_stalk_linearEquiv_of_isInvertible (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) :
    Nonempty (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) := by
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf
      (structureSheafRing X.toRingedSpace).property L).2 ‹_›
  rw [← Stacks.NonvanishingPullback.stalkModule_eq_scheme L x]
  exact Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv X.toRingedSpace L x

/-- The germ at `x` of the unit section of the structure sheaf, read as a section of `𝒪_X`
regarded as a module over itself. -/
noncomputable abbrev unitStalkGerm (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (structureModule X).presheaf x :=
  Stacks.SheafOfModules.unitGerm X.toRingedSpace x

/-- The stalk of `𝒪_X`, regarded as an `𝒪_X`-module, is free of rank one on the germ of the
unit section. -/
theorem bijective_smul_unitStalkGerm (x : X) :
    Function.Bijective fun r : X.presheaf.stalk x => r • unitStalkGerm x := by
  have hb := (Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace x).bijective
  have he : ⇑(Stacks.SheafOfModules.unitStalkLinearEquiv X.toRingedSpace x) =
      fun r : X.presheaf.stalk x => r • unitStalkGerm x := by
    rw [← Stacks.NonvanishingPullback.stalkModule_eq_scheme (structureModule X) x]
    funext r
    simp only [Stacks.SheafOfModules.unitStalkLinearEquiv, LinearEquiv.ofBijective_apply,
      LinearMap.toSpanSingleton_apply, unitStalkGerm]
    rfl
  rw [← he]
  exact hb

/-- The germ of the unit section is a basis of the stalk of `𝒪_X` as a module over itself: the
stalk of the structure sheaf as an `𝒪_X`-module is free of rank one. -/
noncomputable def unitStalkLinearEquiv (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{u}) (structureModule X).presheaf x :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.stalk x) _ (unitStalkGerm x))
    (bijective_smul_unitStalkGerm x)

/-- The isomorphism `unitStalkLinearEquiv x` sends `r` to `r` times the germ of the unit
section. -/
@[simp]
theorem unitStalkLinearEquiv_apply (x : X) (r : X.presheaf.stalk x) :
    unitStalkLinearEquiv x r = r • unitStalkGerm x := rfl

/-- Multiplication by a global section `s` of an `𝒪_X`-module `L`, as a morphism
`𝒪_X ⟶ L` of `𝒪_X`-modules. A section is regular exactly when this is a monomorphism. -/
noncomputable def smulHom (L : X.Modules) (s : L.sections) : structureModule X ⟶ L :=
  L.unitHomEquiv.symm s

/-- Multiplication by `s` sends the unit section to `s`. -/
theorem smulHom_app_one (L : X.Modules) (s : L.sections) :
    (smulHom L s).app ⊤ (unitSectionTop X) = s.eval (op ⊤) := by
  have h := SheafOfModules.unitHomEquiv_apply_coe L (L.unitHomEquiv.symm s) (op ⊤)
  rw [L.unitHomEquiv.apply_symm_apply] at h
  exact h.symm

/-- The stalk at `x` of multiplication by `s` carries the germ of the unit section to the germ
of `s`. -/
theorem mapFun_smulHom_unitStalkGerm (L : X.Modules) (s : L.sections) (x : X) :
    Stacks.ModuleStalk.mapFun (smulHom L s) x (unitStalkGerm x) =
      (L.presheaf.Γgerm x).hom (s.eval (op ⊤)) := by
  have h := Stacks.ModuleStalk.mapFun_Γgerm (smulHom L s) x (unitSectionTop X)
  rw [smulHom_app_one] at h
  exact h

/-- The stalk at `x` of the morphism `𝒪_X ⟶ L` given by multiplication by a global section `s`
of `L`, computed on the basis of the stalk of `𝒪_X` supplied by `unitStalkLinearEquiv`: it is
multiplication of the germ of `s` by a scalar. -/
theorem mapFun_smulHom_unitStalkLinearEquiv (L : X.Modules) (s : L.sections) (x : X)
    (r : X.presheaf.stalk x) :
    Stacks.ModuleStalk.mapFun (smulHom L s) x (unitStalkLinearEquiv x r) =
      r • (L.presheaf.Γgerm x).hom (s.eval (op ⊤)) := by
  rw [unitStalkLinearEquiv_apply, Stacks.ModuleStalk.mapFun_smul,
    mapFun_smulHom_unitStalkGerm]

/-- **The pointwise content of [Stacks, Tag 0AYL].** At an associated point of `X`, the stalk at
`x` of multiplication by a global section `s` of an invertible module `L` is injective exactly
when `s` does not vanish at `x`. -/
theorem injective_mapFun_iff_notMem_maximalSmul (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (x : X) (hx : x ∈ schemeAssociatedPoints X) :
    Function.Injective (Stacks.ModuleStalk.mapFun (smulHom L s) x) ↔
      (L.presheaf.Γgerm x).hom (s.eval (op ⊤)) ∉ Stacks.ModuleStalk.maximalSmul L x := by
  obtain ⟨e⟩ := nonempty_stalk_linearEquiv_of_isInvertible L x
  have hassoc : IsAssociatedPrimeStacks (X.presheaf.stalk x) (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    isAssociatedPrimeStacks_of_linearEquiv (unitStalkLinearEquiv x).symm hx
  have hfun : Stacks.ModuleStalk.mapFun (smulHom L s) x =
      (fun r : X.presheaf.stalk x => r • (L.presheaf.Γgerm x).hom (s.eval (op ⊤))) ∘
        (unitStalkLinearEquiv x).symm := by
    funext r
    rw [Function.comp_apply, ← mapFun_smulHom_unitStalkLinearEquiv L s x,
      LinearEquiv.apply_symm_apply]
  rw [hfun, Function.Injective.of_comp_iff' _ (unitStalkLinearEquiv x).symm.bijective,
    injective_smul_iff_notMem_maximalIdeal_smul_top _ _ e hassoc]
  rfl

/-- **Stacks Project, Tag 0AYL.** Let `X` be a locally Noetherian scheme, `L` an invertible
`𝒪_X`-module and `s ∈ Γ(X, L)`. Then `s` is a regular section if and only if `s` does not vanish
at any associated point of `X`, i.e. its germ at every associated point avoids `𝔪_x L_x`. -/
@[stacks 0AYL]
theorem isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) :
    AlgebraicGeometry.IsRegularSection X.presheaf
        (structureSheafRing X.toRingedSpace).property s ↔
      ∀ x ∈ schemeAssociatedPoints X,
        (L.presheaf.Γgerm x).hom (s.eval (op ⊤)) ∉ Stacks.ModuleStalk.maximalSmul L x := by
  have hLqc : L.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_isInvertible L
  constructor
  · intro hs x hx
    exact (injective_mapFun_iff_notMem_maximalSmul L s x hx).1
      (Stacks.AlgebraicGeometry.EmbeddedPoints.injective_stalkFunctor_map (smulHom L s) hs x)
  · intro hs
    refine Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
      (smulHom L s) fun x => ?_
    by_cases hx : x ∈ schemeAssociatedPoints X
    · exact Or.inl ((injective_mapFun_iff_notMem_maximalSmul L s x hx).2 (hs x hx))
    · exact Or.inr hx

end Stacks.Divisors

end
