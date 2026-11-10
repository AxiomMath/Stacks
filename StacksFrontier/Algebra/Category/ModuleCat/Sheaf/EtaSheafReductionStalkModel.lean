module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReductionStalk

import StacksCore.Tactic.StacksAttribute

/-!
# The décalage half of Tag 0GT9's stalkwise model identification

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  `EtaSheafReductionStalk.lean` reduces Tag 0GT9's
quasi-isomorphism to `Reduction.HasStalkModelComparison`: at every point, *two* isomorphisms
carrying
the stalk of the comparison of Tag 0GT9 to the algebraic comparison of Tag 0F7T — one for the
reduced décalage `η_I F ⊗ O_X/I`, one for the chain-level Bockstein complex — together with the
square they make commute.

This file discharges the first of the two, and records the residue.

## Main results

* `etaModIdealStalkIso`: **the décalage half of the model identification.**  At a generator `f`
  of the stalk ideal `I_x`, the stalk of `η_I F ⊗ O_X/I` is the algebraic `η_f F_x / f η_f F_x`,
  as complexes of `O_{X,x}`-modules.
* `HasStalkBocksteinComparison`: the residue — the Bockstein half of the identification and the
  square, and nothing else.
* `acyclic_reductionComparisonKernel_of_hasStalkBocksteinComparison` and
  `quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinComparison`: granted that residue,
  Tag 0GT9's comparison is a quasi-isomorphism and the kernel complex of
  `EtaSheafReductionQuasiIso.lean` is acyclic.

## Implementation notes

### Where the décalage half comes from

It is not new mathematics: Tag 0GT6 is already formalized, as
`Eta.etaStalkIso` of `EtaSheaf.lean`, and identifies the stalk of the décalage `η_I F` itself
with the algebraic `η_f F_x`.  Tag 0GT9's left-hand side is that complex *reduced modulo the
ideal*, and a reduction is a cokernel, so what has to be added is exactly two things:

* `preservesFiniteColimits_stalkModuleFunctor`: the module-valued stalk functor preserves the
  cokernel.  `EtaSheaf.lean` proves the finite-limits half — the décalage is built from fibre
  products — and this is the other half.  Both come from
  `AlgebraicGeometry.SheafOfModules.stalkFunctor`, restriction of scalars along the comparison
  of the two spellings of the stalk of the structure sheaf being an equivalence.
* `range_stalk_idealPowerIncl_zero`: the stalk of multiplication by the ideal is multiplication
  by `f`.  Both inclusions are read off `Eta.exists_smul_eq_stalk_idealPowerIncl_zero` and
  `Eta.exists_stalk_idealPowerIncl_zero_eq_smul`, which state at the module-valued stalk what
  the step equivalence of `EtaSheaf.lean` already gave: the stalk of
  `I ⊗ M ⟶ M` is `f` times an isomorphism.  They live there and not here because the ambient
  module has two spellings — the tensor sheaf and the first ideal power — and the two are
  interchangeable only inside the module that defines them, the colimit cocone of the
  sheafification not being exposed.

### Why the differential square is five declarations

`maxHeartbeats` is per declaration, and each step of the square spends most of a budget on a
single `isDefEq` between the two spellings of the stalk of a complex; as steps of one chain they
exhaust it together.  The associativity shuffle is `comp_comp_congr`, stated with every object
and morphism a variable for the same reason: one `isDefEq` instead of a dozen keyed matches.

### What this does not do

Nothing here carries `@[stacks 0GT9]`.  Tag 0GT9 asserts that
`Lη_I M ⊗^L O_X/I ⟶ H^•(M/I)` is an isomorphism in `D(O_X)`; everything here is a step of the
*proof* of that.  The tag's own conclusion is proved in Situation 0GT4 in
`EtaSheafReductionDerivedIsoRegular.lean`, as
`Reduction.isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` and
`Reduction.reductionComparisonQIsoOfRegular`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk)

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

/-! ### Variables-only algebra -/

/-- A linear equivalence carries the `f`-multiples onto the `f`-multiples.  Everything is a
variable, so the application below performs one `isDefEq` rather than a keyed match inside the
stalk of a sheaf of modules. -/
private lemma map_range_scalarMap {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : R) (e : M ≃ₗ[R] N) :
    Submodule.map (e : M →ₗ[R] N)
        (LinearMap.range (EtaComplex.scalarMap f M)) =
      LinearMap.range (EtaComplex.scalarMap f N) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨e w, (map_smul e f w).symm⟩
  · rintro y ⟨w, rfl⟩
    exact ⟨f • e.symm w, ⟨e.symm w, rfl⟩, by
      change e (f • e.symm w) = f • w
      rw [map_smul, e.apply_symm_apply]⟩

/-- Postcomposition of a commuting square, with every object and morphism a variable: the one
`isDefEq` the application performs is the matching of the square, rather than a dozen keyed
matches inside the stalk of a complex of sheaves of modules. -/
public lemma comp_comp_congr {C : Type*} [Category C] {W Y V Z T : C}
    {a : W ⟶ Y} {b : Y ⟶ Z} {c : W ⟶ V} {d : V ⟶ Z} (h : a ≫ b = c ≫ d) (g : Z ⟶ T) :
    a ≫ b ≫ g = c ≫ d ≫ g := by
  rw [← Category.assoc, h, Category.assoc]

/-- Rebracketing a composite of three morphisms along two commuting squares, with every object
and morphism a variable. -/
private lemma comp_comp_comp_congr {C : Type*} [Category C] {W Y V Z T U : C}
    {a : W ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ T} {d : Y ⟶ V} {e : V ⟶ T} {g : W ⟶ U} {h : U ⟶ V}
    (h₁ : b ≫ c = d ≫ e) (h₂ : a ≫ d = g ≫ h) : a ≫ b ≫ c = g ≫ h ≫ e := by
  rw [h₁, ← Category.assoc, h₂, Category.assoc]

/-- Composing an isomorphism with its inverse inside a longer composite, with every object and
morphism a variable. -/
private lemma trans_symm_hom_comp {C : Type*} [Category C] {W Y Z T : C}
    (a : W ≅ Y) (e : Z ≅ Y) (q : Y ⟶ T) :
    (a ≪≫ e.symm).hom ≫ e.hom ≫ q = a.hom ≫ q := by
  simp

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The module-valued stalk functor preserves cokernels -/

/-- **The module-valued stalk functor is exact on the right.**  The `RingCat`-valued stalk
functor preserves finite colimits (`AlgebraicGeometry.SheafOfModules.stalkFunctor`), and
restriction of scalars along the comparison of the two spellings of the stalk of the structure
sheaf is an equivalence.

The finite-limits half is already available inside `EtaSheaf.lean`; this is the half that the
reduction modulo the ideal needs, a reduction being a cokernel. -/
public theorem preservesFiniteColimits_stalkModuleFunctor (x : X) :
    PreservesFiniteColimits (stalkModuleFunctor X x) := by
  have h1 : PreservesFiniteColimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x) := inferInstance
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (SemilinearStalk.commStalkRingEquiv X.presheaf x)
  have : PreservesColimitsOfSize.{0, 0} E.inverse :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h1
    (PreservesColimitsOfSize.preservesFiniteColimits E.inverse)

/-! ### Multiplication by the ideal at a stalk is multiplication by the generator -/

/-- **The range of the zeroth ideal-power inclusion at a stalk is the submodule of
`f`-multiples.**  Both inclusions come from `EtaSheaf.lean`, where the two spellings of the
ambient module — the tensor sheaf and the first ideal power — are interchangeable. -/
public theorem range_stalk_idealPowerIncl_zero
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (x : X) (f : ringStalk X x)
    (hf : GeneratesStalkIdeal X ι x f) :
    LinearMap.range ((stalkModuleFunctor X x).map (idealPowerIncl X I ι 0 M)).hom =
      LinearMap.range (EtaComplex.scalarMap f
        ((stalkModuleFunctor X x).obj (idealPowerTerm X I 0 M))) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := exists_smul_eq_stalk_idealPowerIncl_zero X I ι M x f hf z
    exact ⟨w, hw.symm⟩
  · rintro y ⟨w, rfl⟩
    exact exists_stalk_idealPowerIncl_zero_eq_smul X I ι M x f hf w

/-! ### The degreewise model isomorphism -/

/-- The degreewise comparison of Tag 0GT6: in degree `n` the stalk of the décalage is the
degree-`n` term of the algebraic décalage of the stalk complex. -/
private noncomputable def etaTermStalkModelIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).obj (idealPowerTerm X I 0 (etaTerm X I ι F n)) ≅
      (EtaComplex.etaObject f (stalkComplex X x F)).X n :=
  (HomologicalComplex.eval (ModuleCat.{u} (ringStalk X x)) (ComplexShape.up ℤ) n).mapIso
    (etaStalkIso X I ι F hF x f hf)

/-- In degree `n` the comparison of Tag 0GT6 is its own `n`-th component. -/
private lemma etaTermStalkModelIso_hom
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (etaTermStalkModelIso X I ι F hF x f hf n).hom =
      (etaStalkIso X I ι F hF x f hf).hom.f n := rfl

/-- The projection onto the reduction is a map of complexes from the décalage: this is the
naturality of `modIdealMap` read on the differential of the décalage. -/
private lemma cokernel_π_comp_etaModIdealComplex_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) ≫
        (etaModIdealComplex X I ι F hF).d n (n + 1) =
      (etaObj X I ι F hF).d n (n + 1) ≫
        cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F (n + 1))) := by
  rw [etaModIdealComplex_d X I ι F hF n]
  exact cokernel_π_modIdealMap X I ι ((etaObj X I ι F hF).d n (n + 1))

/-- The quotient of the ambient module by the `f`-multiples, transported along Tag 0GT6's
degreewise comparison.  Named rather than inlined, so that the characterisation of
`modIdealStalkTermIso` below can be read off one composite at a time. -/
private noncomputable def modIdealStalkQuotIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    ModuleCat.of (ringStalk X x)
        (((stalkModuleFunctor X x).obj (idealPowerTerm X I 0 (etaTerm X I ι F n))) ⧸
          LinearMap.range ((stalkModuleFunctor X x).map
            (idealPowerIncl X I ι 0 (etaTerm X I ι F n))).hom) ≅
      (EtaComplex.quotientObject f (stalkComplex X x F)).X n :=
  (Submodule.Quotient.equiv _ _ (etaTermStalkModelIso X I ι F hF x f hf n).toLinearEquiv
    (by
      rw [range_stalk_idealPowerIncl_zero X I ι (etaTerm X I ι F n) x f hf]
      exact map_range_scalarMap f
        (etaTermStalkModelIso X I ι F hF x f hf n).toLinearEquiv)).toModuleIso

/-- **The reduction of the décalage modulo the ideal, at a stalk, in degree `n`.**  The stalk
of `(η_I F)^n/I(η_I F)^n` is the degree-`n` term of `η_f F_x / f η_f F_x`.

The stalk functor preserves the defining cokernel, the stalk of multiplication by the ideal is
multiplication by the generator (`range_stalk_idealPowerIncl_zero`), and the ambient modules are
identified by Tag 0GT6. -/
@[no_expose]
private noncomputable def modIdealStalkTermIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).obj (modIdeal X I ι (etaTerm X I ι F n)) ≅
      (EtaComplex.quotientObject f (stalkComplex X x F)).X n :=
  letI := preservesFiniteColimits_stalkModuleFunctor X x
  PreservesCokernel.iso (stalkModuleFunctor X x)
      (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _ ≪≫
      modIdealStalkQuotIso X I ι F hF x f hf n

/-- **The projection onto the reduction is carried to the algebraic quotient projection.**
This is the characterisation of `modIdealStalkTermIso` that the differentials are checked
against: the degreewise comparison is the unique map descending Tag 0GT6's comparison through
the two quotients. -/
private lemma map_cokernel_π_comp_modIdealStalkTermIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
        (modIdealStalkTermIso X I ι F hF x f hf n).hom =
      (etaStalkIso X I ι F hF x f hf).hom.f n ≫
        (EtaComplex.quotientMap f (stalkComplex X x F)).f n := by
  let := preservesFiniteColimits_stalkModuleFunctor X x
  have h3 : ModuleCat.ofHom (LinearMap.range ((stalkModuleFunctor X x).map
          (idealPowerIncl X I ι 0 (etaTerm X I ι F n))).hom).mkQ ≫
        (modIdealStalkQuotIso X I ι F hF x f hf n).hom =
      (etaStalkIso X I ι F hF x f hf).hom.f n ≫
        (EtaComplex.quotientMap f (stalkComplex X x F)).f n :=
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  refine Eq.trans ?_ h3
  rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
      ((stalkModuleFunctor X x).map (idealPowerIncl X I ι 0 (etaTerm X I ι F n))),
    ← PreservesCokernel.π_iso_hom (stalkModuleFunctor X x)
      (idealPowerIncl X I ι 0 (etaTerm X I ι F n))]
  simp only [Category.assoc]
  rfl

/-- **The stalk of the projection onto a successive quotient of the ideal-power filtration is an
epimorphism**: it is the cokernel projection of the stalk of the inclusion, followed by an
isomorphism, the stalk functor preserving the cokernel.

Stated for every twist `n` rather than only for the reduction `n = 0`, because the same fact at
a general `n` is what the graded complexes `F ⊗ I^n/I^{n+1}` need. -/
public lemma epi_map_cokernel_π
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (x : X) (n : ℤ) :
    Epi ((stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n M))) := by
  let := preservesFiniteColimits_stalkModuleFunctor X x
  have hfac : (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n M)) =
      cokernel.π ((stalkModuleFunctor X x).map (idealPowerIncl X I ι n M)) ≫
        (PreservesCokernel.iso (stalkModuleFunctor X x)
          (idealPowerIncl X I ι n M)).inv := by
    rw [← PreservesCokernel.π_iso_hom (stalkModuleFunctor X x) (idealPowerIncl X I ι n M),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]
  exact epi_comp _ _

/-! #### The differential square, one step per declaration

`maxHeartbeats` is per declaration, and each of the three steps below spends most of its budget
on a single `isDefEq` between the two spellings of the stalk of a complex; stated as steps of one
chain inside a single lemma they exhaust it together.
-/

/-- The stalk of the projection onto the reduction is a map of complexes: the differential of
the reduced décalage, read at a stalk. -/
private lemma map_cokernel_π_comp_stalk_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (n : ℤ) :
    (stalkModuleFunctor X x).map
          (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
        ((stalkComplexFunctor X x).obj (etaModIdealComplex X I ι F hF)).d n (n + 1) =
      (stalkComplex X x (etaObj X I ι F hF)).d n (n + 1) ≫
        (stalkModuleFunctor X x).map
          (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F (n + 1)))) := by
  refine Eq.trans ((stalkModuleFunctor X x).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (fun k => (stalkModuleFunctor X x).map k)
    (cokernel_π_comp_etaModIdealComplex_d X I ι F hF n)) ?_
  exact (stalkModuleFunctor X x).map_comp _ _

/-- Step one of the differential square: pass the projection through the degreewise
comparison. -/
private lemma modIdealStalkTermIso_comm_step₁
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).map
          (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
        ((modIdealStalkTermIso X I ι F hF x f hf n).hom ≫
          (EtaComplex.quotientObject f (stalkComplex X x F)).d n (n + 1)) =
      (etaStalkIso X I ι F hF x f hf).hom.f n ≫
        ((EtaComplex.quotientMap f (stalkComplex X x F)).f n ≫
          (EtaComplex.quotientObject f (stalkComplex X x F)).d n (n + 1)) :=
  comp_comp_congr (map_cokernel_π_comp_modIdealStalkTermIso X I ι F hF x f hf n)
    ((EtaComplex.quotientObject f (stalkComplex X x F)).d n (n + 1))

/-- Step two: the algebraic quotient projection and Tag 0GT6's comparison are both maps of
complexes. -/
private lemma modIdealStalkTermIso_comm_step₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (etaStalkIso X I ι F hF x f hf).hom.f n ≫
        ((EtaComplex.quotientMap f (stalkComplex X x F)).f n ≫
          (EtaComplex.quotientObject f (stalkComplex X x F)).d n (n + 1)) =
      (stalkComplex X x (etaObj X I ι F hF)).d n (n + 1) ≫
        ((etaStalkIso X I ι F hF x f hf).hom.f (n + 1) ≫
          (EtaComplex.quotientMap f (stalkComplex X x F)).f (n + 1)) :=
  comp_comp_comp_congr ((EtaComplex.quotientMap f (stalkComplex X x F)).comm n (n + 1))
    ((etaStalkIso X I ι F hF x f hf).hom.comm n (n + 1))

/-- Step three: pass back through the degreewise comparison in degree `n + 1`. -/
private lemma modIdealStalkTermIso_comm_step₃
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkComplex X x (etaObj X I ι F hF)).d n (n + 1) ≫
        ((etaStalkIso X I ι F hF x f hf).hom.f (n + 1) ≫
          (EtaComplex.quotientMap f (stalkComplex X x F)).f (n + 1)) =
      (stalkModuleFunctor X x).map
          (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
        (((stalkComplexFunctor X x).obj (etaModIdealComplex X I ι F hF)).d n (n + 1) ≫
          (modIdealStalkTermIso X I ι F hF x f hf (n + 1)).hom) :=
  comp_comp_comp_congr
    (map_cokernel_π_comp_modIdealStalkTermIso X I ι F hF x f hf (n + 1)).symm
    (map_cokernel_π_comp_stalk_d X I ι F hF x n).symm

/-- The degreewise comparisons commute with the differentials: both sides agree after the
projection from the stalk of the décalage, where the square becomes Tag 0GT6's compatibility
followed by the fact that the algebraic quotient projection is a map of complexes. -/
private lemma modIdealStalkTermIso_comm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (modIdealStalkTermIso X I ι F hF x f hf n).hom ≫
        (EtaComplex.quotientObject f (stalkComplex X x F)).d n (n + 1) =
      ((stalkComplexFunctor X x).obj (etaModIdealComplex X I ι F hF)).d n (n + 1) ≫
        (modIdealStalkTermIso X I ι F hF x f hf (n + 1)).hom := by
  have := epi_map_cokernel_π X I ι (etaTerm X I ι F n) x 0
  refine (cancel_epi ((stalkModuleFunctor X x).map
    (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))))).1 ?_
  exact (modIdealStalkTermIso_comm_step₁ X I ι F hF x f hf n).trans
    ((modIdealStalkTermIso_comm_step₂ X I ι F hF x f hf n).trans
      (modIdealStalkTermIso_comm_step₃ X I ι F hF x f hf n))

/-- **The first of the two model isomorphisms owed by Tag 0GT9.**  At a generator `f` of the
stalk ideal `I_x`, the stalk of the reduced décalage `η_I F ⊗ O_X/I` is the algebraic
`η_f F_x / f η_f F_x`.

It is Tag 0GT6's comparison `Eta.etaStalkIso` of the décalages themselves, pushed through the
two reductions: the stalk functor preserves the cokernel defining the sheaf-level reduction, and
the stalk of multiplication by the ideal is multiplication by `f`. -/
@[no_expose]
public noncomputable def etaModIdealStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) :
    (stalkComplexFunctor X x).obj (etaModIdealComplex X I ι F hF) ≅
      EtaComplex.quotientObject f (stalkComplex X x F) :=
  HomologicalComplex.Hom.isoOfComponents (modIdealStalkTermIso X I ι F hF x f hf)
    (fun n m h => by
      subst h
      exact modIdealStalkTermIso_comm X I ι F hF x f hf n)

/-- **The degreewise characterisation of the décalage half of the model identification.**  The
stalk of the projection onto the reduction, followed by the degree-`n` component of
`etaModIdealStalkIso`, is Tag 0GT6's comparison followed by the algebraic quotient projection.

This is `map_cokernel_π_comp_modIdealStalkTermIso` read on `etaModIdealStalkIso` itself, and it
is the only thing a consumer outside this module can know about that isomorphism's components:
the body of `etaModIdealStalkIso` is not exposed, and the projection onto the reduction is a
stalkwise epimorphism (`epi_map_cokernel_π`), so this equation pins the component down. -/
public theorem map_cokernel_π_comp_etaModIdealStalkIso_hom_f
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
        (etaModIdealStalkIso X I ι F hF x f hf).hom.f n =
      (etaStalkIso X I ι F hF x f hf).hom.f n ≫
        (EtaComplex.quotientMap f (stalkComplex X x F)).f n :=
  map_cokernel_π_comp_modIdealStalkTermIso X I ι F hF x f hf n

/-! ### The Bockstein half of the stalkwise model identification -/

/-- **The stalkwise Bockstein model identification.**  At every
point `x` of `X` there are a generator `f` of the stalk ideal `I_x` which is a nonzerodivisor of
`O_{X,x}` and regular on every term of the stalk complex, and an isomorphism `β` of the stalk of
the chain-level Bockstein complex with the algebraic Bockstein complex of `F_x/f`, carrying the
stalk of the comparison of Tag 0GT9 to the algebraic comparison of Tag 0F7T read through
`etaModIdealStalkIso`.

This is `Reduction.HasStalkModelComparison` with its first datum discharged: the identification
of the stalk of `η_I F ⊗ O_X/I` with the algebraic model is `etaModIdealStalkIso` above, so this
predicate is the Bockstein half of the source's last step — "on stalks this construction matches
the maps built in More on Algebra, Lemma 15.97.6" — and nothing else.  It holds in Situation
0GT4, by `Reduction.hasStalkBocksteinComparison_of_hasStalkBocksteinSquare` applied to
`Reduction.hasStalkBocksteinSquare_of_isLocallyGeneratedByRegular`.

As in `HasStalkModelComparison`, the first four data are not themselves the obligation: on a
space whose structure-sheaf stalks are local rings `exists_stalkGenerator` supplies `f` with its
nonzerodivisor property and `isSMulRegular_stalkComplex` its regularity.  They stay inside the
existential so that the statements consuming this hold in the generality of
`EtaSheafReductionQuasiIso.lean` — condition (2) of Tag 0GT3 alone.

Nothing here is inhabited vacuously: `β` is an isomorphism, not a bare morphism, so no zero map
satisfies the square.

This is reduced one step further in `EtaSheafBocksteinSquare.lean`: `β` need not be asked for as
a morphism of complexes, because the stalk of the comparison of Tag 0GT9 is a degreewise
epimorphism.  `Reduction.HasStalkBocksteinSquare` asks only for the comparison square in each
single degree, against the *named* components `bocksteinChainStalkTermIso`, and
`Reduction.hasStalkBocksteinComparison_of_hasStalkBocksteinSquare` recovers this predicate from
it. -/
public def HasStalkBocksteinComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) : Prop :=
  ∀ x : X, ∃ (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
      (hf : f ∈ nonZeroDivisors (ringStalk X x))
      (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f)
      (β : (stalkComplexFunctor X x).obj (bocksteinChainComplex X I ι F hF) ≅
            EtaPow.Bockstein.bocksteinComplex f hf (stalkComplex X x F) hreg),
      (stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF) ≫ β.hom =
        (etaModIdealStalkIso X I ι F hF x f hgen).hom ≫
          Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg

/-- **The Bockstein model identification gives the full stalkwise model identification.**  The
décalage half is `etaModIdealStalkIso`, composed with the standard identification
`η_f M ⊗ A/fA ≅ η_f M / f η_f M` of Tag 0F7T's development. -/
public theorem hasStalkModelComparison_of_hasStalkBocksteinComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinComparison X I ι F hF) :
    HasStalkModelComparison X I ι F hF := by
  intro x
  obtain ⟨f, hgen, hf, hreg, β, hsq⟩ := h x
  refine ⟨f, hgen, hf, hreg,
    etaModIdealStalkIso X I ι F hF x f hgen ≪≫
      (Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso f hf
        (stalkComplex X x F) hreg).symm, β, hsq.trans ?_⟩
  exact (trans_symm_hom_comp (etaModIdealStalkIso X I ι F hF x f hgen)
    (Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso f hf
      (stalkComplex X x F) hreg)
    (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
      (stalkComplex X x F) hreg)).symm

/-- **Tag 0GT9's quasi-isomorphism, modulo the Bockstein model identification alone.** -/
public theorem quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinComparison X I ι F hF) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) :=
  quasiIso_reductionComparisonChainMap_of_hasStalkModelComparison X I ι F hF
    (hasStalkModelComparison_of_hasStalkBocksteinComparison X I ι F hF h)

/-- **The acyclicity of Tag 0GT9's kernel complex, from the Bockstein model identification
alone.**  This is `EtaSheafReductionQuasiIso.lean`'s chain-level form of the tag, with
`HasStalkBocksteinComparison` the whole of what it rests on. -/
public theorem acyclic_reductionComparisonKernel_of_hasStalkBocksteinComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinComparison X I ι F hF) :
    (reductionComparisonKernel X I ι F hF).Acyclic :=
  acyclic_reductionComparisonKernel_of_hasStalkModelComparison X I ι F hF
    (hasStalkModelComparison_of_hasStalkBocksteinComparison X I ι F hF h)

end Stacks.IdealTorsion.Reduction

end
