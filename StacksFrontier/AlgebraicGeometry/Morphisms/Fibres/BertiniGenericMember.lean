module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFamilyDivisors
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences

/-!
# From the generic member of a linear system to its general members

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]): a finite
dimensional linear system `V` of sections of an invertible module `L` on a scheme `X` over a
field `k`, with a basis `v₁, …, v_r`. The universal divisor `H_univ ⊂ 𝔸^r_k ×_k X` is a scheme
over the parameter space `𝔸^r_k`, and the divisor `H_v` attached to a vector of `V ⊗_k k'` is
its fibre over the corresponding `k'`-point of `𝔸^r_k`.

This module turns a statement about the single *generic* member into a statement about
*general* members, in the precise sense of Tag 0G47: if the fibre of `H_univ → 𝔸^r_k` over the
generic point is geometrically irreducible, then there is one nonempty open `U ⊂ 𝔸^r_k`, over
the base field, such that `H_v` is geometrically irreducible over `k'` for every field
extension `k'/k` and every `k'`-point of `U`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.parameterBase` is the parameter space `𝔸^r_k`.
* `Stacks.Bertini.FamilyDivisors.universalFamily` is `H_univ → 𝔸^r_k`.

## Main results

* `Stacks.Bertini.FamilyDivisors.isPullback_fibreParameterMap` presents the base change
  `X_{k'}` as the fibre product `𝔸^r_X ×_{𝔸^r_k} Spec k'`.
* `Stacks.Bertini.FamilyDivisors.forGeneral_geometricallyIrreducible_of_genericFibre` is the
  passage from the generic member to general members.
* `Stacks.Bertini.FamilyDivisors.noetherianSpace_universalDivisorScheme`: `H_univ` is a
  Noetherian space when `X` is of finite type over `k`.

## Implementation notes

The parameter space of Tag 0G47 is Mathlib's relative affine space `𝔸(ι; X)`, and the
projection to `𝔸^r_k = 𝔸(ι; Spec k)` is `AlgebraicGeometry.AffineSpace.map`, which
`AlgebraicGeometry.AffineSpace.isPullback_map` exhibits as the base change of the structure
morphism `X → Spec k`. Being of finite type and quasi-compact therefore pass from `X → Spec k`
to `𝔸^r_X → 𝔸^r_k`, and from there to `H_univ → 𝔸^r_k` because a closed immersion is of finite
type.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace Stacks.Bertini

/-- The subscheme cut out by the pullback of an ideal sheaf is the fibre product of the
subscheme with the base: `Z(I · 𝒪_X) = X ×_Y Z(I)`. -/
theorem isPullback_subschemeι_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι
      (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f)) f I.subschemeι :=
  IsPullback.of_iso_pullback
    ⟨(Scheme.IdealSheafData.subschemeMap_subschemeι _ _ f (I.le_map_comap f)).symm⟩
    (I.comapIso f) (Scheme.IdealSheafData.comapIso_hom_fst I f)
    (Scheme.IdealSheafData.comapIso_hom_snd I f)

/-- **A base change along a point of a geometrically irreducible open is irreducible.** If the
restriction `f ∣_ V` of `f : X → Y` over an open `V ⊂ Y` is geometrically irreducible, then
every base change of `f` along a `k'`-point of `Y` whose image lies in `V` is irreducible.

The point factors through `V` because `V → Y` is an open immersion, and the base change along
it is then also a base change of `f ∣_ V`, by cancelling the pullback square
`f ⁻¹ᵁ V = X ×_Y V`. -/
theorem irreducibleSpace_of_geometricallyIrreducible_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : GeometricallyIrreducible (f ∣_ V)) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ Y) (hy : ∀ q : Spec (.of K), y q ∈ V) {Z : Scheme.{u}}
    (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)) (h : IsPullback fst snd f y) :
    IrreducibleSpace Z := by
  have hrange : Set.range y.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact hy q
  have hfac : IsOpenImmersion.lift V.ι y hrange ≫ V.ι = y :=
    IsOpenImmersion.lift_fac _ _ _
  rw [← hfac] at h
  exact hV.1 _ _ snd (IsPullback.of_right' h (isPullback_morphismRestrict f V).flip)

namespace FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- The parameter space `𝔸^r_k` of the family, over the base field. -/
abbrev parameterBase : Scheme.{u} := 𝔸(D.basisIndex; Spec (.of D.k))

/-- The projection `𝔸^r_X = 𝔸^r_k ×_k X → 𝔸^r_k` of the parameter space to the parameter
space of the base field. -/
abbrev parameterBaseMap : D.parameterSpace ⟶ D.parameterBase :=
  AffineSpace.map D.basisIndex D.toBase

/-- The universal divisor `H_univ = Z(s_univ)` as a scheme. -/
abbrev universalDivisorScheme : Scheme.{u} := D.universalDivisor.subscheme

/-- **The universal family** `H_univ → 𝔸^r_k`, whose fibre over a `k'`-point of `𝔸^r_k` is the
divisor attached to the corresponding vector of `V ⊗_k k'`. -/
def universalFamily : D.universalDivisorScheme ⟶ D.parameterBase :=
  D.universalDivisor.subschemeι ≫ D.parameterBaseMap

/-- The projection `𝔸^r_X → 𝔸^r_k` is the base change of `X → Spec k`, so it is of finite
type as soon as `X` is. -/
theorem locallyOfFiniteType_parameterBaseMap [LocallyOfFiniteType D.toBase] :
    LocallyOfFiniteType D.parameterBaseMap :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map D.toBase).flip
    (inferInstanceAs (LocallyOfFiniteType D.toBase))

/-- The projection `𝔸^r_X → 𝔸^r_k` is the base change of `X → Spec k`, so it is quasi-compact
as soon as `X → Spec k` is. -/
theorem quasiCompact_parameterBaseMap [QuasiCompact D.toBase] :
    QuasiCompact D.parameterBaseMap :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map D.toBase).flip
    (inferInstanceAs (QuasiCompact D.toBase))

/-- The universal family is of finite type when `X` is of finite type over `k`: it is a closed
immersion followed by the base change of `X → Spec k`. -/
theorem locallyOfFiniteType_universalFamily [LocallyOfFiniteType D.toBase] :
    LocallyOfFiniteType D.universalFamily :=
  have := locallyOfFiniteType_parameterBaseMap D
  MorphismProperty.comp_mem _ _ _ (inferInstance) (inferInstance)

/-- The universal family is quasi-compact when `X → Spec k` is. -/
theorem quasiCompact_universalFamily [QuasiCompact D.toBase] :
    QuasiCompact D.universalFamily :=
  have := quasiCompact_parameterBaseMap D
  MorphismProperty.comp_mem _ _ _ (inferInstance) (inferInstance)

/-- **The parameter space `𝔸^r_k` is a Noetherian scheme**: it is of finite type and
quasi-compact over `Spec k`, and a field is a Noetherian ring. -/
instance isNoetherian_parameterBase : IsNoetherian D.parameterBase :=
  haveI : IsLocallyNoetherian D.parameterBase :=
    LocallyOfFiniteType.isLocallyNoetherian
      (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k))
  haveI : CompactSpace D.parameterBase :=
    QuasiCompact.compactSpace_of_compactSpace
      (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k))
  AlgebraicGeometry.IsNoetherian.mk

/-- **`H_univ` is a Noetherian space** when `X` is of finite type over `k`. The universal family
`H_univ → 𝔸^r_k` is of finite type and quasi-compact
(`Stacks.Bertini.FamilyDivisors.locallyOfFiniteType_universalFamily`,
`Stacks.Bertini.FamilyDivisors.quasiCompact_universalFamily`) and `𝔸^r_k` is a Noetherian
scheme, so `H_univ` is locally Noetherian and compact, hence a Noetherian space.

This is the finiteness hypothesis the dimension count of [Stacks, Tag 0FD6] reads on `H_univ`:
with it an instance, that count needs nothing beyond `X` being of finite type over `k`. -/
instance noetherianSpace_universalDivisorScheme [LocallyOfFiniteType D.toBase]
    [QuasiCompact D.toBase] : NoetherianSpace D.universalDivisorScheme :=
  haveI := D.locallyOfFiniteType_universalFamily
  haveI := D.quasiCompact_universalFamily
  haveI : IsLocallyNoetherian D.universalDivisorScheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.universalFamily
  haveI : CompactSpace D.universalDivisorScheme :=
    QuasiCompact.compactSpace_of_compactSpace D.universalFamily
  haveI : IsNoetherian D.universalDivisorScheme := AlgebraicGeometry.IsNoetherian.mk
  inferInstance

/-- The parameter space `𝔸^r_k` is irreducible: it is the spectrum of a polynomial ring over a
field, which is a domain. -/
theorem irreducibleSpace_parameterBase : IrreducibleSpace D.parameterBase :=
  (Scheme.homeoOfIso (AffineSpace.SpecIso D.basisIndex (.of D.k))).irreducibleSpace_iff.mpr
    (inferInstanceAs (IrreducibleSpace (PrimeSpectrum (MvPolynomial D.basisIndex D.k))))

section BaseChange

variable (K : Type u) [Field K] [Algebra D.k K]

/-- The projection `X_{k'} → Spec k'` of the base change of `X` along a field extension. -/
def baseChangeToSpec : D.baseChange K ⟶ Spec (.of K) :=
  pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap D.k K)))

/-- The base change `X_{k'}` is the fibre product of `X` and `Spec k'` over `Spec k`. -/
theorem isPullback_baseChange :
    IsPullback (D.baseChangeToX K) (D.baseChangeToSpec K) D.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap D.k K))) :=
  IsPullback.of_hasPullback _ _

/-- The `k'`-point of `𝔸^r_k` with coordinate tuple `a` lies over `Spec k'`. -/
theorem parameterPoint_comp_base (a : Fin (Module.finrank D.k D.V) → K) :
    D.parameterPoint a ≫ (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)) =
      Spec.map (CommRingCat.ofHom (algebraMap D.k K)) :=
  AffineSpace.homOfVector_over _ _

/-- The `k'`-point of `𝔸^r_k` with coordinate tuple `a` sends the `i`-th coordinate function to
the `i`-th entry of `a`. -/
theorem parameterPoint_appTop_coord (a : Fin (Module.finrank D.k D.V) → K)
    (i : D.basisIndex) :
    (D.parameterPoint a).appTop (AffineSpace.coord (Spec (.of D.k)) i) =
      (Scheme.ΓSpecIso (.of K)).inv (a i.down) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The square `X_{k'} → 𝔸^r_X`, `X_{k'} → Spec k'`, `𝔸^r_X → 𝔸^r_k`, `Spec k' → 𝔸^r_k`
commutes: the classifying morphism of a `k'`-point of `𝔸^r_k` lies over that point. -/
theorem fibreParameterMap_comp_parameterBaseMap (a : Fin (Module.finrank D.k D.V) → K) :
    D.fibreParameterMap K a ≫ D.parameterBaseMap =
      D.baseChangeToSpec K ≫ D.parameterPoint a := by
  refine AffineSpace.hom_ext ?_ fun i => ?_
  · simp only [Category.assoc]
    rw [AffineSpace.map_over, D.parameterPoint_comp_base K a, ← Category.assoc,
      D.fibreParameterMap_comp_parameterProjection K a]
    exact (D.isPullback_baseChange K).w
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    show (D.fibreParameterMap K a).appTop (D.parameterBaseMap.appTop _) =
      (D.baseChangeToSpec K).appTop ((D.parameterPoint a).appTop _)
    rw [AffineSpace.map_appTop_coord, D.parameterPoint_appTop_coord K a i]
    exact D.fibreParameterMap_appTop_coord K a i.down

/-- **`X_{k'} = 𝔸^r_X ×_{𝔸^r_k} Spec k'`.** The base change of `X` along a field extension is
the fibre of the parameter space over the corresponding `k'`-point of `𝔸^r_k`.

This is the pasting of the square presenting `𝔸^r_X` as `𝔸^r_k ×_k X`
(`AlgebraicGeometry.AffineSpace.isPullback_map`) with the square presenting `X_{k'}` as
`X ×_k Spec k'`. -/
theorem isPullback_fibreParameterMap (a : Fin (Module.finrank D.k D.V) → K) :
    IsPullback (D.fibreParameterMap K a) (D.baseChangeToSpec K)
      D.parameterBaseMap (D.parameterPoint a) := by
  refine IsPullback.of_right (h₁₂ := D.parameterProjection) ?_
    (D.fibreParameterMap_comp_parameterBaseMap K a)
    (AffineSpace.isPullback_map D.toBase).flip
  rw [D.fibreParameterMap_comp_parameterProjection K a, D.parameterPoint_comp_base K a]
  exact D.isPullback_baseChange K

/-- **`H_v` is the fibre of `H_univ` over the point classifying `v`.** The closed subscheme cut
out by the divisor of a vector over a field extension `k'/k` is the fibre product of `H_univ`
and `X_{k'}` over `𝔸^r_X`.

The comparison morphism `H_v → H_univ` is left existentially quantified because the equality
`H_v = H_{univ, v}` of ideal sheaves (`Tag 0G47`) is what identifies the two subschemes, and
rewriting along it changes the type of the morphism. -/
theorem exists_isPullback_specializedDivisor (a : Fin (Module.finrank D.k D.V) → K) :
    ∃ p : (D.specializedDivisor K a).subscheme ⟶ D.universalDivisorScheme,
      IsPullback p (D.specializedDivisor K a).subschemeι
        D.universalDivisor.subschemeι (D.fibreParameterMap K a) := by
  rw [D.specializedDivisor_eq_comap K a]
  exact ⟨_, (isPullback_subschemeι_comap D.universalDivisor (D.fibreParameterMap K a)).flip⟩

/-- **`H_v` is the fibre of the universal family over the `k'`-point classifying `v`.** The
divisor attached to a vector of `V ⊗_k k'`, with its structure morphism to `Spec k'`, is the
base change of the universal family `H_univ → 𝔸^r_k` along that `k'`-point.

This pastes the identification of `H_v` as a fibre over `𝔸^r_X` with the presentation of
`X_{k'}` as `𝔸^r_X ×_{𝔸^r_k} Spec k'`. -/
theorem exists_isPullback_universalFamily (a : Fin (Module.finrank D.k D.V) → K) :
    ∃ p : (D.specializedDivisor K a).subscheme ⟶ D.universalDivisorScheme,
      IsPullback p ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)
        D.universalFamily (D.parameterPoint a) := by
  obtain ⟨p, hp⟩ := D.exists_isPullback_specializedDivisor K a
  exact ⟨p, hp.paste_vert (D.isPullback_fibreParameterMap K a)⟩

/-- A vector of `V ⊗_k k'` has at most one coordinate tuple with respect to the chosen basis:
the basis of `V` stays a basis after base change to `k'`. -/
theorem coordinates_injective (a a' : Fin (Module.finrank D.k D.V) → K)
    (h : ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) =
      ∑ i, TensorProduct.tmul D.k (D.basis i) (a' i)) :
    a = a' := by
  classical
  have key : ∀ (c : Fin (Module.finrank D.k D.V) → K) (j : Fin (Module.finrank D.k D.V)),
      (D.basis.baseChange K).repr
          (TensorProduct.comm D.k D.V K (∑ i, TensorProduct.tmul D.k (D.basis i) (c i))) j =
        c j := by
    intro c j
    rw [map_sum, map_sum]
    simp only [TensorProduct.comm_tmul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self, Finsupp.single_apply,
      ite_smul, one_smul, zero_smul]
    simp
  funext j
  rw [← key a j, h, key a' j]

end BaseChange

/-- **From the generic member of a linear system to its general members.**

Assume `X` is of finite type over `k`. If the fibre of the universal family
`H_univ → 𝔸^r_k` over the generic point `η` of `𝔸^r_k` is geometrically irreducible over the
residue field `κ(η) = k(x₁, …, x_r)`, then for general `v ∈ V ⊗_k k'` the divisor `H_v` is
geometrically irreducible over `k'`, in the precise sense of [Stacks, Tag 0G47]: there is one
nonempty open `U ⊂ 𝔸^r_k`, defined over `k`, such that `H_v` is geometrically irreducible over
`k'` for every field extension `k'/k` and every `k'`-point of `U`.

The open is produced by [Stacks, Tag 0559] applied to `H_univ → 𝔸^r_k`, which is of finite type
and quasi-compact because `X → Spec k` is; and the transfer from a `k'`-point of that open to
the divisor `H_v` is the identification of `H_v` as the fibre of the universal family
(`Stacks.Bertini.FamilyDivisors.exists_isPullback_universalFamily`). -/
theorem forGeneral_geometricallyIrreducible_of_genericFibre
    [LocallyOfFiniteType D.toBase] [QuasiCompact D.toBase] (η : D.parameterBase)
    (hη : IsGenericPoint η Set.univ)
    (hgen : GeometricallyIrreducible (D.universalFamily.fiberToSpecResidueField η)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          GeometricallyIrreducible
            ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  obtain ⟨V, hVne, hV⟩ := geometricallyIrreducibleAfterShrinking D.universalFamily
    (D.irreducibleSpace_parameterBase) (D.locallyOfFiniteType_universalFamily)
    (D.quasiCompact_universalFamily) η hη hgen
  refine ⟨V, Set.nonempty_coe_sort.mp hVne, ?_⟩
  intro K _ _ a hmem a' heq
  obtain rfl := D.coordinates_injective K a a' heq
  obtain ⟨p, hup⟩ := D.exists_isPullback_universalFamily K a
  refine ⟨?_⟩
  intro K₂ _ y₂ Z fst snd hz
  refine irreducibleSpace_of_geometricallyIrreducible_restrict D.universalFamily V hV
    (y₂ ≫ D.parameterPoint a) (fun q => ?_) (fst ≫ p) snd (hz.paste_horiz hup)
  simpa using hmem (y₂ q)

end FamilyDivisors

end Stacks.Bertini

end
