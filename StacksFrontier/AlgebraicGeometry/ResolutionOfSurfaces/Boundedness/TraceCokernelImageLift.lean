module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelBaseTrace
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelImage
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelVanishingHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to rational singularities from annihilation of the trace cokernel, through duality

Let `(A, 𝔪, κ)` be a two-dimensional local normal Nagata domain with a normalized dualizing
complex `ω_A^•`, and for a modification `f : X ⟶ Spec(A)` with `X` normal write
`ω_X^• = f^×(ω̃_A^•)` and `N_f = RΓ(X, ω_X^•)`. The trace of [Stacks, Tag 0AWG] over the affine
base (`Stacks.Duality.baseTrace`) is a morphism `N_f ⟶ ω_A^•` of `D(A)`, and on degree `-2`
cohomology it is the trace map `Γ(X, ω_X) ⟶ ω_A` appearing in the hypothesis of
[Stacks, Tag 0B4S]: its source is `Γ(X, ω_X)` by
`AlgebraicGeometry.homologyNegTwoDerivedGlobalSectionsIso` below, and its target is `ω_A` by
`Dualizing.dualizingModule_eq_homologyFunctor_negTwo_obj`, the dualizing module of a
two-dimensional Noetherian local ring being the degree `-2` cohomology of its dualizing complex.

This file proves [Stacks, Tag 0B4S]: if a nonzero `d ∈ A` annihilates the cokernel of that trace
for every normal modification, then reduction to rational singularities is possible for `A`.

## Main results

* `Dualizing.dualizingModule_eq_homologyFunctor_negTwo_obj` — **`ω_A = H^{-2}(ω_A^•)`** over a
  two-dimensional Noetherian local ring, the target of the trace.
* `AlgebraicGeometry.derivedGlobalSectionsIsoShiftSingle` — `RΓ(X, ω_X^•) ≅ RΓ(X, ω_X)[2]` out of
  the normalization `ω_X^• ≅ ω_X[2]`: `RΓ(X, -)` applied to it, with the shift moved out.
* `AlgebraicGeometry.homologyNegTwoDerivedGlobalSectionsIso` — **`H^{-2}(RΓ(X, ω_X^•)) ≅
  Γ(X, ω_X)`**, the previous isomorphism on `H^{-2}` composed with
  `AlgebraicGeometry.homologyShiftTwoSingleIso`.
* `AlgebraicGeometry.surjective_homologyMap_negTwo_derivedGlobalSections` — **`H^{-2}` is
  surjective on `Hom(RΓ(X, 𝒪_X)[2], RΓ(X, ω_X^•))`**, which is what the lifting lemma
  `DerivedCategory.exists_comp_eq_of_surjective_homologyMap` consumes.
* `Dualizing.homologyLinearEquiv_symm_comp` — the corepresentation of `H^j` by the free rank-one
  module in degree `j` is natural in its argument.
* `Stacks.ResolutionOfSurfaces`
  `.isReductionToRationalSingularitiesPossible_of_exists_comp_baseTrace_eq` — [Stacks, Tag 0B4S]
  with its hypothesis read as the factorisation of `d · Hom(A[-2], ω_A^•)` through the trace.
* `Stacks.ResolutionOfSurfaces`
  `.isReductionToRationalSingularitiesPossible_of_smul_baseTraceCokernel_eq_zero` —
  **[Stacks, Tag 0B4S]**, with the hypothesis as the source states it: `d` annihilates the
  cokernel of the trace `Γ(X, ω_X) ⟶ ω_A`.

## The argument

`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_factorisation` is the
tag with Grauert-Riemenschneider ([Stacks, Tag 0AXD]) discharged; what it still asks is that for
every normal modification `f`, every `u : A[-2] ⟶ C_f` which is an isomorphism on `H^{-2}` and
every `q : A[-2] ⟶ ω_A^•`, the morphism `d · q` factor through `u`, where
`C_f = RΓ(X, 𝒪_X)[2]`.

Given the annihilation hypothesis, `d · q` is the trace of a global section of `ω_X`. Indeed
`A[-2]` corepresents `H^{-2}` on `D(A)` (`Dualizing.homologyLinearEquiv`), so `q` *is* an element
of `H^{-2}(ω_A^•) = ω_A`, and `d · q` lies in the image of `H^{-2}(N_f) = Γ(X, ω_X)` under the
trace; corepresentability read backwards turns that element of `H^{-2}(N_f)` into a morphism
`s : A[-2] ⟶ N_f`, and its naturality (`Dualizing.homologyLinearEquiv_symm_comp`) says
`s ≫ baseTrace = d · q`. It therefore suffices to factor `s` through `u` and compose the
factorisation with the trace.

That factorisation is `DerivedCategory.exists_comp_eq_of_surjective_homologyMap`: since `A[-2]`
corepresents `H^{-2}` on *all* of `D(A)`, `A` being projective over itself, a factorisation of `s`
through `u` exists as soon as
`H^{-2} : Hom(C_f, N_f) ⟶ Hom_A(H^{-2}(C_f), H^{-2}(N_f))` is surjective. No t-structure and no
property of `u` beyond `IsIso (H^{-2}(u))` is used.

That surjectivity is where the geometry enters. Both groups are modules of global sections,
`H^{-2}(C_f) = Γ(X, 𝒪_X)` and `H^{-2}(N_f) = Γ(X, ω_X)`, and `Γ(X, 𝒪_X) = A` for a modification
(`AlgebraicGeometry.modificationSecsOverUnitIso`), so an `A`-linear map between them is determined
by the image of the global section `1` and is hence `Γ(X, φ)` for a morphism `φ : 𝒪_X ⟶ ω_X` of
sheaves (`AlgebraicGeometry.exists_comp_secsOver_map_eq`); then `RΓ(X, φ[0])[2]`, read back along
`RΓ(X, ω_X^•) ≅ RΓ(X, ω_X)[2]`, is a morphism with the prescribed `H^{-2}`, by
`AlgebraicGeometry.homologyShiftTwoSingleIso_naturality`.

The normalization `ω_X^• ≅ ω_X[2]` on which `H^{-2}(N_f) ≅ Γ(X, ω_X)` rests is produced, together
with the module `ω_X`, by
`Stacks.ResolutionOfSurfaces.exists_isDualizingModule_isZero_firstCohomology`. So `ω_X` is not a
parameter of the statements below, and the hypothesis on `d` is stated at `H^{-2}` of the trace
rather than at `Γ(X, ω_X)` — those being the same module, by the isomorphism of this file.

## Relation to the other carrier of the tag

The theorem
`isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero` (in the namespace
`Stacks.ResolutionOfSurfaces`) of `Boundedness/TraceCokernelReduction.lean` is the argument of
[Stacks, Tag 0B4S] with the duality of the source's proof supplied as a *parameter*, and does not
carry the tag: its hypothesis
`D` is a `Stacks.ResolutionOfSurfaces.TraceCokernelDuality`, whose fields are the dualizing
modules `ω_X`, their trace maps `Γ(X, ω_X) ⟶ ω_A`, and the presentation of the Matlis dual of
`H¹(X, 𝒪_X)` as a quotient of the cokernel of the trace. The statement below takes none of that:
`ω_X` and its normalization come from [Stacks, Tag 0AXD], the trace is the trace of [Stacks, Tag
0AWG], and the duality is the one of `Boundedness/TraceCokernelVanishingHom.lean`.

## Implementation notes

The derived categories are read at `CategoryTheory.HasDerivedCategory.standard`, the model all the
duality inputs live at, so the three global locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are erased, as in the files this one
extends. Inside that section two `CategoryTheory.CategoryStruct` paths for the sheaves of modules
on a scheme coexist and goals mentioning both are reported not type-correct under implicit
transparency, so every reassociation in
`AlgebraicGeometry.surjective_homologyMap_negTwo_derivedGlobalSections` is supplied as an
explicitly typed term and the steps are composed by `calc`, rather than left to `simp`.

`surjective_homologyMap_negTwo_derivedGlobalSections` writes `RΓ(X, 𝒪_X)[2]` out rather than
naming it `AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift`, so that the component of
`AlgebraicGeometry.homologyShiftTwoSingleIso` at the structure sheaf matches its source without
unfolding; the two are the same term, and the consumer below is stated at the name.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

section Standard

attribute [local instance] HasDerivedCategory.standard

/-! ### The corepresentation of `H^j` by `A[j]` is natural -/

namespace Dualizing

/-- **The corepresentation of `H^j` by the free rank-one module in degree `j` is natural.** For
`g : W ⟶ W'` in `D(A)`, the morphism `A[j] ⟶ W` which `Dualizing.homologyLinearEquiv` attaches to
`x ∈ H^j(W)`, composed with `g`, is the morphism attached to `H^j(g)(x)`.

This is `DerivedCategory.homologyFromSingle_comp` with the identification of `Hom_A(A, -)` with
the identity folded in, as `Dualizing.homologyLinearEquiv` folds it in. -/
theorem homologyLinearEquiv_symm_comp {A : Type u} [CommRing A]
    {W W' : DerivedCategory (ModuleCat.{u} A)} (j : ℤ)
    (s : (DerivedCategory.singleFunctor (ModuleCat.{u} A) j).obj (ModuleCat.of A A) ⟶ W)
    (g : W ⟶ W') :
    (homologyLinearEquiv W' j).symm (s ≫ g) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map g).hom
        ((homologyLinearEquiv W j).symm s) := by
  have key : ∀ (V : DerivedCategory (ModuleCat.{u} A))
      (t : (DerivedCategory.singleFunctor (ModuleCat.{u} A) j).obj (ModuleCat.of A A) ⟶ V),
      (homologyLinearEquiv V j).symm t =
        (DerivedCategory.homologyFromSingle (ModuleCat.of A A) V j t).hom (1 : A) :=
    fun _ _ => rfl
  rw [key, key, DerivedCategory.homologyFromSingle_comp]
  rfl

end Dualizing

/-! ### `ω_A = H^{-2}(ω_A^•)` in dimension two -/

namespace Dualizing

/-- **`ω_A = H^{-2}(ω_A^•)` over a two-dimensional Noetherian local ring.** The dualizing module
`Dualizing.dualizingModule` of an object of `D(A)` is its cohomology in degree `-dim(A)`, so at
`dim(A) = 2` it is the degree `-2` cohomology, which is the reading `ω_A^• = ω_A[2]`.

`Dualizing.localRingDimension` is the Krull dimension of a Noetherian local ring as a natural
number, and `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` is what reconciles it with
`ringKrullDim`, which is where the hypothesis is stated. -/
theorem dualizingModule_eq_homologyFunctor_negTwo_obj {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 2)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    dualizingModule K = (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj K := by
  have hcast : ((localRingDimension A : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
    let : (IsLocalRing.maximalIdeal A : Ideal A).FiniteHeight :=
      Ideal.finiteHeight_of_isNoetherianRing _
    have hh : (IsLocalRing.maximalIdeal A : Ideal A).height ≠ ⊤ :=
      Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    rw [localRingDimension, ENat.natCast_toNat_eq_self.mpr hh]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  rw [hdim, show ((2 : WithBot ℕ∞)) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_num] at hcast
  have h2 : localRingDimension A = 2 := Nat.cast_inj.mp (WithBot.coe_inj.mp hcast)
  have h3 : -(localRingDimension A : ℤ) = (-2 : ℤ) := by omega
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} A)
      (-(localRingDimension A : ℤ))).obj K =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj K
  rw [h3]

end Dualizing

/-! ### `H^{-2}(RΓ(X, ω_X^•)) ≅ Γ(X, ω_X)`, and the surjectivity of `H^{-2}` -/

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`RΓ(X, ω_X^•) ≅ RΓ(X, ω_X)[2]`.** Derived global sections of the normalization
`ω_X^• ≅ ω_X[2]` of [Stacks, Remark 0B4R], with the shift moved out of `RΓ(X, -)` by the
commutation of a triangulated functor with the shift. -/
def derivedGlobalSectionsIsoShiftSingle {K : DerivedCategory X.Modules} {ωX : X.Modules}
    (e : K ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) :
    (derivedGlobalSectionsOver f).obj K ≅
      ((derivedGlobalSectionsOver f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ωX))⟦(2 : ℤ)⟧ :=
  (derivedGlobalSectionsOver f).mapIso e ≪≫
    ((derivedGlobalSectionsOver f).commShiftIso (2 : ℤ)).app _

/-- **`H^{-2}(RΓ(X, ω_X^•)) ≅ Γ(X, ω_X)`.** The source of the trace of [Stacks, Tag 0AWG], read
on degree `-2` cohomology, is the module of global sections of the dualizing module: this is
`AlgebraicGeometry.derivedGlobalSectionsIsoShiftSingle` on `H^{-2}` followed by
`AlgebraicGeometry.homologyShiftTwoSingleIso`. -/
def homologyNegTwoDerivedGlobalSectionsIso {K : DerivedCategory X.Modules} {ωX : X.Modules}
    (e : K ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj
        ((derivedGlobalSectionsOver f).obj K) ≅
      (secsOver f).obj ωX :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).mapIso
      (derivedGlobalSectionsIsoShiftSingle f e) ≪≫
    homologyShiftTwoSingleIso f ωX

/-- **`H^{-2}` is surjective on `Hom(RΓ(X, 𝒪_X)[2], RΓ(X, K))` for `K ≅ ω_X[2]`.** Let
`f : X ⟶ Spec(A)` be a modification of the spectrum of a normal domain and let `K` be an object
of `D(𝒪_X)` isomorphic to `ω_X[2]` for some sheaf of modules `ω_X`. Then every `A`-linear map
`H^{-2}(RΓ(X, 𝒪_X)[2]) ⟶ H^{-2}(RΓ(X, K))` is `H^{-2}` of a morphism of `D(A)`.

Both sides are modules of global sections, by `AlgebraicGeometry.homologyShiftTwoSingleIso` and
`AlgebraicGeometry.homologyNegTwoDerivedGlobalSectionsIso`, and `Γ(X, 𝒪_X) = A` for a
modification (`AlgebraicGeometry.modificationSecsOverUnitIso`), so the map is determined by the
image of the global section `1` and is therefore the global sections of a morphism
`φ : 𝒪_X ⟶ ω_X` of sheaves (`AlgebraicGeometry.exists_comp_secsOver_map_eq`). Then
`RΓ(X, φ[0])[2]`, read back along `RΓ(X, K) ≅ RΓ(X, ω_X)[2]`, is a morphism with the prescribed
`H^{-2}`, by `AlgebraicGeometry.homologyShiftTwoSingleIso_naturality`.

The source is `AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift f`, written out. -/
theorem surjective_homologyMap_negTwo_derivedGlobalSections [IsNormalDomain A]
    (hf : IsModification f) {K : DerivedCategory X.Modules} {ωX : X.Modules}
    (e : K ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) :
    Function.Surjective fun w : ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf)))⟦(2 : ℤ)⟧ ⟶
        (derivedGlobalSectionsOver f).obj K ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map w := by
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2) with hH
  intro α
  set eC := homologyShiftTwoSingleIso f (SheafOfModules.unit X.ringCatSheaf) with hEC
  set eW := homologyShiftTwoSingleIso f ωX with hEW
  set eK := derivedGlobalSectionsIsoShiftSingle f e with hEK
  set ι := (modificationSecsOverUnitIso f hf).inv with hι
  obtain ⟨φ, hφ⟩ := exists_comp_secsOver_map_eq f ωX ι
    (secsOver_map_apply_modificationSecsOverUnitIso_inv_one f hf)
    (ι ≫ eC.inv ≫ α ≫ H.map eK.hom ≫ eW.hom)
  have hφ' : (secsOver f).map φ = eC.inv ≫ α ≫ H.map eK.hom ≫ eW.hom := (cancel_epi ι).mp hφ
  set t := (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (2 : ℤ)).map
      ((derivedGlobalSectionsOver f).map ((DerivedCategory.singleFunctor X.Modules 0).map φ))
    with ht
  have key : H.map t = α ≫ H.map eK.hom := by
    refine (cancel_mono eW.hom).mp ?_
    calc H.map t ≫ eW.hom
        = eC.hom ≫ (secsOver f).map φ := homologyShiftTwoSingleIso_naturality f φ
      _ = eC.hom ≫ eC.inv ≫ α ≫ H.map eK.hom ≫ eW.hom :=
          congrArg (fun r => eC.hom ≫ r) hφ'
      _ = α ≫ H.map eK.hom ≫ eW.hom := eC.hom_inv_id_assoc _
      _ = (α ≫ H.map eK.hom) ≫ eW.hom := (Category.assoc _ _ _).symm
  have final : H.map (t ≫ eK.inv) = α :=
    calc H.map (t ≫ eK.inv)
        = H.map t ≫ H.map eK.inv := H.map_comp _ _
      _ = (α ≫ H.map eK.hom) ≫ H.map eK.inv := congrArg (· ≫ H.map eK.inv) key
      _ = α ≫ H.map eK.hom ≫ H.map eK.inv := Category.assoc _ _ _
      _ = α ≫ H.map (eK.hom ≫ eK.inv) :=
          congrArg (fun r => α ≫ r) (H.map_comp eK.hom eK.inv).symm
      _ = α ≫ H.map (𝟙 _) := congrArg (fun r => α ≫ H.map r) eK.hom_inv_id
      _ = α ≫ 𝟙 _ := congrArg (fun r => α ≫ r) (H.map_id _)
      _ = α := Category.comp_id α
  exact ⟨t ≫ eK.inv, final⟩

end AlgebraicGeometry

/-! ### [Stacks, Tag 0B4S] -/

namespace Stacks.ResolutionOfSurfaces

open Stacks.Duality

variable {A : Type u} [CommRing A]

/-- **[Stacks, Tag 0B4S] with its hypothesis read as a factorisation through the trace.** Let
`(A, 𝔪, κ)` be a local normal Nagata domain of dimension two with a normalized dualizing complex
`ω_A^•`, let `d ∈ A` be nonzero, and suppose that for every modification `f : X ⟶ Spec(A)` with
`X` normal and every morphism `q : A[-2] ⟶ ω_A^•` the morphism `d · q` is of the form
`s ≫ (RΓ(X, ω_X^•) ⟶ ω_A^•)`, the second factor being the trace of [Stacks, Tag 0AWG] over the
affine base (`Stacks.Duality.baseTrace`). Then reduction to rational singularities is possible
for `A`.

`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_factorisation` reduces
the tag to the factorisation of `d · q` through a morphism `u : A[-2] ⟶ RΓ(X, 𝒪_X)[2]` which is
an isomorphism on `H^{-2}`; the given `s` is factored through `u` by
`DerivedCategory.exists_comp_eq_of_surjective_homologyMap`, whose hypothesis is
`AlgebraicGeometry.surjective_homologyMap_negTwo_derivedGlobalSections`, and the factorisation is
then composed with the trace. -/
theorem isReductionToRationalSingularitiesPossible_of_exists_comp_baseTrace_eq
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) (d : A) (hd : d ≠ 0)
    (htrace : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f),
      letI : IsProper f := hf.isProper
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      ∀ q : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶ ωA,
        ∃ s : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶
            (derivedGlobalSectionsOver f).obj
              ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj,
          s ≫ baseTrace f ωA = q ≫ (d • 𝟙 ωA)) :
    IsReductionToRationalSingularitiesPossible A := by
  have : IsNoetherianRing A := ‹IsNagataRing A›.1
  refine isReductionToRationalSingularitiesPossible_of_factorisation A hdim ωA hωA d hd ?_
  intro X _ f hf u hu q
  have : IsProper f := hf.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨ωX, _, ⟨eshift⟩, _⟩ :=
    exists_isDualizingModule_isZero_firstCohomology f ‹IsNagataRing A› hdim hf ωA hωA
  obtain ⟨s, hs⟩ := htrace X f hf q
  obtain ⟨w, hw⟩ := DerivedCategory.exists_comp_eq_of_surjective_homologyMap u hu
    (surjective_homologyMap_negTwo_derivedGlobalSections f hf eshift) s
  refine ⟨w ≫ baseTrace f ωA, ?_⟩
  rwa [← Category.assoc, hw]

/-- Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two with a normalized
dualizing complex `ω_A^•`. If some nonzero `d ∈ A` annihilates the cokernel of the
trace map `Γ(X, ω_X) ⟶ ω_A` for every modification `f : X ⟶ Spec(A)` with `X` normal — `ω_X`
being the dualizing module of `X` normalized relative to `ω_A^•` — then reduction to rational
singularities is possible for `A`: the `A`-module lengths of `H¹(X, 𝒪_X)` admit a common finite
bound over all such `X`.

The trace is the trace of [Stacks, Tag 0AWG] over the affine base
(`Stacks.Duality.baseTrace`) read on degree `-2` cohomology. Its source is `Γ(X, ω_X)` by
`AlgebraicGeometry.homologyNegTwoDerivedGlobalSectionsIso`, and its target is `ω_A` by
`Dualizing.dualizingModule_eq_homologyFunctor_negTwo_obj`: the dualizing module of a
two-dimensional Noetherian local ring is `H^{-2}` of its dualizing complex, which is the source's
own reading `ω_A^• = ω_A[2]`.

Duality turns the annihilation into the factorisation hypothesis of
`isReductionToRationalSingularitiesPossible_of_exists_comp_baseTrace_eq`: `A[-2]` corepresents
`H^{-2}` on `D(A)` (`Dualizing.homologyLinearEquiv`), naturally in its argument
(`Dualizing.homologyLinearEquiv_symm_comp`), so a morphism `q : A[-2] ⟶ ω_A^•` is an element of
`ω_A`, and `d · q` lying in the image of the trace is exactly that factorisation.

The source assumes only that `A` *has* a dualizing complex. Asking for a normalized one costs
nothing: the normalizing shift of [Stacks, Tag 0AX1]
(`Dualizing.exists_isNormalizedDualizingComplex_shift`) produces one from any dualizing complex,
and it is the normalized complex whose `H^{-2}` is the dualizing module `ω_A` that the source's
hypothesis is about. The complex has to be named in the statement because the hypothesis on `d`
mentions it. -/
@[stacks 0B4S "reduction to rational singularities for a two-dimensional local normal Nagata \
domain with a normalized dualizing complex, from a nonzero element annihilating the cokernel of \
the trace map of every normal modification; the trace is Stacks.Duality.baseTrace, the trace of \
Tag 0AWG over the affine base, read on H^{-2}, whose source is the global sections of the \
normalized dualizing module of X by homologyNegTwoDerivedGlobalSectionsIso and whose target is \
the dualizing module of A by dualizingModule_eq_homologyFunctor_negTwo_obj; \
Grauert-Riemenschneider vanishing (Tag 0AXD) is discharged in TraceCokernelVanishingHom.lean \
and the uniform length bound of Tags 0AXJ and 0AXK upstream"]
theorem isReductionToRationalSingularitiesPossible_of_smul_baseTraceCokernel_eq_zero
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) (d : A) (hd : d ≠ 0)
    (hcoker : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f),
      letI : IsProper f := hf.isProper
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      ∀ z : ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj ωA) ⧸
          LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
            (baseTrace f ωA)).hom,
        d • z = 0) :
    IsReductionToRationalSingularitiesPossible A := by
  refine isReductionToRationalSingularitiesPossible_of_exists_comp_baseTrace_eq hdim ωA hωA d hd
    ?_
  intro X _ f hf
  have : IsProper f := hf.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  intro q
  have hmem : d • (Dualizing.homologyLinearEquiv ωA (-2)).symm q ∈
      LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
        (baseTrace f ωA)).hom := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hcoker X f hf (Submodule.Quotient.mk
      ((Dualizing.homologyLinearEquiv ωA (-2)).symm q))]
    rfl
  obtain ⟨y, hy⟩ := hmem
  have hsmul : q ≫ (d • 𝟙 ωA) = d • q := by
    rw [Linear.comp_smul, Category.comp_id]
  refine ⟨Dualizing.homologyLinearEquiv _ (-2) y, ?_⟩
  refine (Dualizing.homologyLinearEquiv ωA (-2)).symm.injective ?_
  rwa [hsmul, Dualizing.homologyLinearEquiv_symm_comp, LinearEquiv.symm_apply_apply, map_smul]

end Stacks.ResolutionOfSurfaces

end Standard

end
