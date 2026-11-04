module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.InjectiveAmplitude
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExtCohomologySheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a coherent complex into one of finite injective dimension

Let `A` be a Noetherian ring and `X = Spec A`. [Stacks, Tag 0A88] says that for `K` in
`D_Coh(A)` — every cohomology module finite, with no boundedness hypothesis whatsoever — and `L`
of finite injective dimension,

`R𝓗om_{𝒪_X}(K̃, L̃) = (R Hom_A(K, L))~`

in `D(𝒪_X)`. This file proves it, for the canonical comparison morphism
`AlgebraicGeometry.affineDerivedTildeHomComparison`.

## Main results

* `AlgebraicGeometry.AffineExt.isZero_cohomologySheaf_of_forall_localizedExt_eq_zero`: a
  cohomology sheaf of `R𝓗om(K̃, L̃)` vanishes as soon as every localized `Ext` module does.
* `AlgebraicGeometry.AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude`: the
  sheaf-side amplitude bound, `R𝓗om(Z̃, L̃)` is `IsLE (b - p)` for `Z` in `D^{≥p}(A)` and `L` of
  injective amplitude in `[a, b]` over a Noetherian `A`.
* `AlgebraicGeometry.isIso_affineDerivedTildeHomComparison_of_finite_homology`: **Tag 0A88**.

## The proof

`K` is not pseudo-coherent: `D_Coh(A)` is not contained in `D^-(A)`, so clause (3)(a) of
[Stacks, Tag 0A6H] — `AlgebraicGeometry.isIso_affineDerivedTildeHomComparison_of_isPseudoCoherent`
— does not apply to `K` itself. What it does apply to is every canonical truncation `τ^{<c}K`,
which is bounded above and still has finite cohomology modules, hence is pseudo-coherent by
[Stacks, Tag 066E]; and `L`, having finite injective dimension, is bounded below.

So fix a degree `n` and cut `K` at `c = b - n + 1`, where `[a, b]` is an injective amplitude
interval for `L`. The canonical truncation triangle `τ^{<c}K ⟶ K ⟶ τ^{≥c}K` is carried by
`R Hom_A(-, L)` and by `R𝓗om_{𝒪_X}((-)~, L̃)` to distinguished triangles
([Stacks, Tag 08I0] on the sheaf side), and the comparison is a morphism between them by
`AlgebraicGeometry.affineDerivedTildeHomComparison_natural_left`. Both error terms —
`R Hom_A(τ^{≥c}K, L)` and `R𝓗om_{𝒪_X}((τ^{≥c}K)~, L̃)` — are `IsLE (n - 1)`, so in degree `n`
the two triangles identify `K` with `τ^{<c}K` on both sides, and the comparison at `τ^{<c}K` is
invertible. Hence the comparison at `K` is invertible in degree `n`; as `n` was arbitrary, it is
invertible.

The two amplitude bounds are not the same statement twice. On the module side it is
`StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude`, read off from a bounded
complex of injectives. **That bound is not inherited by the sheaf side**: the sheafification of
an injective module need not be an injective sheaf, by [Stacks, Tag 0CRZ]. The sheaf-side bound
is proved here instead through part (4) of [Stacks, Tag 0A6H], which computes the `n`-th
cohomology sheaf of `R𝓗om(K̃, L̃)` as the sheaf associated with the presheaf
`D(f) ↦ Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f)`: those `Ext` modules vanish in the range in question
because `L ⊗_A A_f` still has injective amplitude in `[a, b]`, over `A_f`, which is where the
Noetherian hypothesis enters ([Stacks, Tag 0A6I]).

## References

* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A6I](https://stacks.math.columbia.edu/tag/0A6I)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineExt

-- Standard model only: `AlgebraicGeometry.AffineExt.cohomologySheaf`,
--   `AlgebraicGeometry.AffineExt.localizedExt`, `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable (R : CommRingCat.{u})

/-- **A cohomology sheaf of `R𝓗om(K̃, L̃)` with no `Ext` classes over it vanishes.** Part (4) of
[Stacks, Tag 0A6H] exhibits every section of `Hⁿ(R𝓗om(K̃, L̃))` as, locally, the image of a class
in `Ext^n_{R_g}(K ⊗ R_g, L ⊗ R_g)`; if those modules are all zero then every section vanishes
locally, hence vanishes, and a sheaf of modules with no nonzero section is a zero object. -/
theorem isZero_cohomologySheaf_of_forall_localizedExt_eq_zero
    (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : ∀ (g : R) (α : localizedExt R K L g n), α = 0) :
    IsZero (cohomologySheaf R K L n) := by
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ (fun U => ?_)
  refine subsingleton_of_forall_eq 0 (fun s => ?_)
  refine Stacks.SheafOfModules.eq_zero_of_locally_zero' _ s (fun y hy => ?_)
  obtain ⟨W, ⟨g, rfl⟩, hyg, hgV⟩ :=
    (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hy
  obtain ⟨g', h', hyg', α, hα⟩ := extToCohomologySheaf_locally_surjective R K L n g
    (Stacks.SheafOfModules.res _ (homOfLE hgV) s) y hyg
  refine ⟨basicOpen R g', homOfLE h' ≫ homOfLE hgV, hyg', ?_⟩
  rw [h g' α, map_zero] at hα
  exact (Stacks.SheafOfModules.res_res _ (homOfLE hgV) (homOfLE h') s).symm.trans hα.symm

/-- **The sheaf-side amplitude bound.** Over a Noetherian ring `R`, if `Z` has no cohomology
below degree `p` and `L` has injective amplitude in `[a, b]`, then `R𝓗om_{𝒪_{Spec R}}(Z̃, L̃)` has
no cohomology above degree `b - p`.

This is *not* the sheafification of the module-side bound
`StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude`: the sheafification of an
injective module need not be an injective sheaf ([Stacks, Tag 0CRZ]), so `L̃` is not known to
have finite injective dimension as a sheaf. The bound is read instead on the `Ext` presheaf of
part (4) of [Stacks, Tag 0A6H], whose values vanish in this range because `L ⊗_R R_f` has
injective amplitude in `[a, b]` over `R_f` ([Stacks, Tag 0A6I]). -/
theorem isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude [IsNoetherianRing R]
    (Z L : DerivedCategory (ModuleCat.{u} R)) (p a b : ℤ) (hZ : Z.IsGE p)
    (hL : StacksDraft.InjectiveDimension.HasInjectiveAmplitude L a b) :
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tilde.functor R).mapDerivedCategory.obj Z))).obj
      ((tilde.functor R).mapDerivedCategory.obj L)).IsLE (b - p) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine isZero_cohomologySheaf_of_forall_localizedExt_eq_zero R Z L i (fun g α => ?_)
  exact StacksDraft.InjectiveDimension.eq_zero_of_isGE_of_hasInjectiveAmplitude_shift _ _ p a b i
    (CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ Z p hZ)
    (hasInjectiveAmplitude_extD_locMap R L a b g hL) (by omega) α

end AlgebraicGeometry.AffineExt

namespace AlgebraicGeometry

-- Standard model only: `StacksDraft.DerivedHom.derivedHomAdjunction`,
--   `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

/-- Every cohomology module of a canonical truncation `τ^{<c}K` is finite when every cohomology
module of `K` is: below `c` it is a cohomology module of `K`, and at and above `c` it vanishes. -/
private theorem finite_homology_truncLT (R : CommRingCat.{u}) (c : ℤ)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) (i : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((DerivedCategory.TStructure.t.truncLT c).obj K)) := by
  by_cases hi : i < c
  · have := hK i
    exact Module.Finite.equiv
      ((DerivedCategory.truncLTCompHomologyFunctorIso c i hi).app K).toLinearEquiv.symm
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((DerivedCategory.TStructure.t.truncLT c).obj K)) :=
      ModuleCat.subsingleton_of_isZero (DerivedCategory.isZero_of_isLE
        ((DerivedCategory.TStructure.t.truncLT c).obj K) (c - 1) i (by omega))
    infer_instance

/-- **Stacks Tag 0A88.** Let `R` be a Noetherian ring and `X = Spec R`. For `K` an object of
`D_Coh(R)` — all of whose cohomology modules are finite, with no boundedness hypothesis — and `L`
an object of `D(R)` of finite injective dimension, the canonical comparison

`(R Hom_R(K, L))~ ⟶ R𝓗om_{𝒪_X}(K̃, L̃)`

is an isomorphism, which is the asserted equality of the two objects in `D(𝒪_X)`. -/
@[stacks 0A88]
theorem isIso_affineDerivedTildeHomComparison_of_finite_homology (R : CommRingCat.{u})
    [IsNoetherianRing R] (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L) :
    IsIso (affineDerivedTildeHomComparison R K L) := by
  obtain ⟨a, b, hab⟩ := hL
  rw (transparency := .default) [DerivedCategory.isIso_iff]
  intro n
  have hLplus : (DerivedCategory.TStructure.t).plus L :=
    ⟨a, StacksDraft.InjectiveDimension.isGE_of_hasInjectiveAmplitude L a b hab⟩
  set c : ℤ := b - n + 1 with hcdef
  set T := (DerivedCategory.TStructure.t.triangleLTGE c).obj K with hTdef
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) :=
    DerivedCategory.TStructure.t.triangleLTGE_distinguished c K
  -- the comparison at the truncation is invertible: clause (3)(a) of Tag 0A6H
  have hγ : IsIso (affineDerivedTildeHomComparison R T.obj₁ L) := by
    refine isIso_affineDerivedTildeHomComparison_of_isPseudoCoherent R T.obj₁ L ?_ hLplus
    refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      T.obj₁ c (ModuleCat.of R R)).2.1).2 ⟨⟨c - 1, fun i hi =>
        DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) i hi⟩,
      finite_homology_truncLT R c K hK⟩
  -- the truncation triangle, carried to both sides of the comparison
  obtain ⟨δ, hMT⟩ := StacksDraft.DerivedHom.exists_distinguished_derivedHom
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)) L T hT
  obtain ⟨δ', hST⟩ := Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first
    (Spec R).sheaf ((tildeDer R).obj L)
    ((tildeDer R).mapTriangle.obj T)
    ((tildeDer R).map_distinguished T hT)
  -- both error terms vanish in degrees `n` and `n + 1`
  have hc : b - c = n - 1 := by omega
  have hmod : ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
      (op T.obj₃, L)).IsLE (n - 1) :=
    hc ▸ StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)) T.obj₃ L c a b inferInstance hab
  have hmod' : ((tildeDer R).obj
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
        (op T.obj₃, L))).IsLE (n - 1) := by
    have := hmod
    exact Stacks.Homology.isLE_mapDerivedCategory_obj (tilde.functor R) _ (n - 1)
  have hsheaf : (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
      (op ((tildeDer R).obj T.obj₃))).obj
      ((tildeDer R).obj L)).IsLE (n - 1) :=
    hc ▸ AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude R T.obj₃ L
      c a b inferInstance hab
  -- so in degree `n` the two triangles identify `K` with `τ^{<c}K` on both sides
  have h1 : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
      ((tildeDer R).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (X := (op K, L)) (Y := (op T.obj₁, L)) (T.mor₁.op, 𝟙 L)))) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁
      ((tildeDer R).mapTriangle.obj (Triangle.mk
        ((StacksDraft.DerivedHom.derivedHomFunctor
          (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)) L).map T.mor₂.op)
        ((StacksDraft.DerivedHom.derivedHomFunctor
          (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)) L).map T.mor₁.op) δ))
      ((tildeDer R).map_distinguished _ hMT) n (n - 1) hmod' (by omega)
  have h2 : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
      (affineDerivedTildeHomComparison R T.obj₁ L)) := by
    have := hγ
    exact CategoryTheory.Functor.map_isIso _ _
  have h3 : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
        ((tildeDer R).map T.mor₁).op).app
          ((tildeDer R).obj L))) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ (Triangle.mk
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).flip.obj
        ((tildeDer R).obj L)).map
          ((tildeDer R).mapTriangle.obj T).mor₂.op)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).flip.obj
        ((tildeDer R).obj L)).map
          ((tildeDer R).mapTriangle.obj T).mor₁.op) δ')
      hST n (n - 1) hsheaf (by omega)
  -- and the comparison is a morphism of triangles
  have key := congrArg (DerivedCategory.homologyFunctor (Spec R).Modules n).map
    (affineDerivedTildeHomComparison_natural_left R (K := K) (K' := T.obj₁) T.mor₁ L)
  rw (transparency := .default) [Functor.map_comp, Functor.map_comp] at key
  have h12 : IsIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
      ((tildeDer R).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map
          (X := (op K, L)) (Y := (op T.obj₁, L)) (T.mor₁.op, 𝟙 L))) ≫
      (DerivedCategory.homologyFunctor (Spec R).Modules n).map
        (affineDerivedTildeHomComparison R T.obj₁ L)) := IsIso.comp_isIso' h1 h2
  -- the two instance arguments are supplied explicitly: the two spellings of the sheaf category
  -- agree only up to unfolding, so instance synthesis does not see `h3` and `h12`
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ h3 h12 key.symm

end AlgebraicGeometry

end
