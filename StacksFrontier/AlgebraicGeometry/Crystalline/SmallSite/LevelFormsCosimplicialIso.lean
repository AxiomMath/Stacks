module

public import
  StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsCompositeTwoLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFormsCosimplicialVertical
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitAcyclicity

/-!
# The isomorphism `ε` of [Stacks, Tag 07LF], and the lemma

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, a sheaf `F` of
`𝒪_{X/S}`-modules, a degree `i` and a `p`-adic level `e`.  The degreewise identification

`(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})(T(n)_e)  ≅  L_n ⊗_{D(n)} ⋀^i_{D(n)} Ω_{D(n)}`

is `...SmallSite.levelTensorFormsEquiv`.  **This file proves that it is cosimplicial, assembles it
into the isomorphism `ε` of cosimplicial abelian groups, and with it proves
[Stacks, Tag 07LF].**

The naturality is the abstract square
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` instantiated at the level objects of
`...SmallSite.wholeSpaceSystem`, with the three concrete inputs
`...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality`,
`...SmallSite.levelFormsDPVertical_tmul` and `...SmallSite.levelFormsPsi_tmul_ιMulti`; the
assembly is `Crystalline.cosimplicialModuleForgetUliftIso`, and the passage from the presheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to its sheafification is
`...SmallSite.levelCosimplicialSectionsSheafifyIso`.

## Main definitions

* `...SmallSite.levelCosimplicialFormsPresheafIso` — the isomorphism of cosimplicial abelian
  groups from the level-`e` sections of the **presheaf** `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` onto
  `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`.
* `...SmallSite.levelCosimplicialSectionsFormsIso` — **the isomorphism `ε`**, the same with the
  sheafification on the left.

## Main results

* `...SmallSite.levelTensorFormsCrossingEquiv_naturality` — the cosimplicial naturality of the
  three comparisons of the source's proof at the level objects.
* `...SmallSite.levelTensorFormsEquiv_naturality` — the cosimplicial naturality of the degreewise
  identification.
* `...SmallSite.vanishing07LF` — **[Stacks, Tag 07LF]**: for `X` and `S` affine and a sheaf of
  `𝒪_{X/S}`-modules satisfying the two hypotheses of [Stacks, Tag 07JN], the cohomology groups
  `H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})` vanish for `i > 0`.

## Implementation notes

**The two sides of the square are read at two different levels.**  The level of the third
comparison of the source's proof is the cutoff of the degree's own
`Crystalline.DifferentialsCompletionComparison` plus `N + e`, and that cutoff is a
`Classical.choose` which varies with the cosimplicial degree;
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` is the square that tolerates
this, at the cost of a common level carried as an argument.  The common level
taken here is `c(n) + (c(m) + (N + e))`, so that the unprimed transport is `rfl` and the primed
one is `Nat.add_left_comm`; the two module structures and scalar towers reading the tensor
products there are `...SmallSite.levelSectionsModuleAt` and
`...SmallSite.levelSectionsIsScalarTowerAt`, which exist at **every** level past `N + e`.

**Every instance of the abstract square is supplied positionally**, as
`...SmallSite.levelTensorFormsCrossingEquiv` already supplies one half of them: the module and
scalar-tower structures on the sections are declared at the `(wholeSpaceEnvelopeRing hp).obj n`
spelling of `D(n)` and the square asks for them at `AdicCompletion (p) E(n)`, where a search does
not find them while a definitional check is immediate.

**The instantiation is three declarations and not one, and the assembly four.**  Reading the
right vertical at the spelling of the abstract square — whose module of completed differentials
is `AdicCompletion (p) Ω_{E(n)}` where this chapter writes `Ω_{D(*)}(op (op n))`, inside an
exterior power inside a tensor product — is one heartbeat budget by itself, the application of
the square with its hundred-odd arguments is another, and restating the conclusion at the
chapter's own spelling is a third.  `levelFormsCrossingSquareAux`, `levelFormsCrossingSquare` and
`levelTensorFormsCrossingEquiv_naturality` are those three steps; `levelFormsUliftEquiv`,
`levelCosimplicialFormsPresheaf_map` and `levelFormsUliftEquiv_naturality` play the same role for
the assembly, which otherwise exhausts the recursion depth rather than the heartbeats.  **No
heartbeat and no recursion limit is raised anywhere.**

**The right vertical is the transition map of `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`** and the left one is
the restriction map of the presheaf tensor product conjugated by
`...SmallSite.levelTensorFormsDPEquiv`, so the square proved at the crossing transports to the
full degreewise identification by `LinearEquiv.symm_apply_apply` alone; that is what
`...SmallSite.levelFormsDPVertical` was defined to absorb.

**The assembly keeps the cosimplicial module a variable.**  Substituting
`(CategoryTheory.opOp SimplexCategory).obj n` for `op (op n)` inside `M.obj` does not elaborate at
`M = L_* ⊗ ⋀^i Ω_{D(*)}`; `Crystalline.cosimplicialModuleForgetUliftIso` performs the
substitution once with `M` a variable, which is why this file never has to.  No heartbeat limit
is raised anywhere.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

section Degreewise

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]
variable (F : SheafOfModules.{u} (structureSheaf S)) (i e : ℕ) {n m : SimplexCategory}
  (φ : n ⟶ m)

/-! ### The cosimplicial naturality of the three comparisons -/

/-- The statement of `levelFormsCrossingSquareAux`: the type of
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` at the arguments listed there.  It
is a declaration of its own so that the application is elaborated once for the statement and
once for the proof, each within its own heartbeat budget. -/
abbrev levelFormsCrossingSquareAuxStatement : Prop :=
  type_of% (@_root_.Crystalline.tensorFormsLevelComposite_naturality_of_levels
        (Γ(S.S.scheme, ⊤) : Type u) _
        (wholeSpaceLevelEnvelope hp n.len)
        (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u)
        (wholeSpaceLevelEnvelope hp m.len)
        (Γ((wholeSpaceLevelObj hp e m).obj.thickening.target.scheme, ⊤) : Type u)
        _ _ _ _
        (wholeSpaceLevelEnvelopeAlgebra hp n.len)
        (affineBaseAppLE S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl).hom.toAlgebra
        (wholeSpaceLevelEnvelopeAlgebra hp m.len)
        (affineBaseAppLE S (wholeSpaceLevelObj hp e m).obj (V := ⊤) le_rfl).hom.toAlgebra
        (wholeSpaceLevelEnvelope hp n.len).ideal
        (wholeSpaceLevelEnvelope hp n.len).dividedPowers
        (wholeSpaceLevelEnvelope hp m.len).ideal
        (wholeSpaceLevelEnvelope hp m.len).dividedPowers
        (affineSituation S hp).p
        (wholeSpaceLevelEnvelope_prime_nilpotent hp n.len)
        (wholeSpaceLevelEnvelope_prime_nilpotent hp m.len)
        (wholeSpaceLevelComparison hp n.len) (wholeSpaceLevelComparison hp m.len)
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).1
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).2
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp m.len e).1
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp m.len e).2
        _ (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj)
        _ (crysDividedPowers S (wholeSpaceLevelObj hp e m).obj)
        (wholeSpaceEnvelopeRingLevelAlgEquiv hp n.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
        (ideal_map_of_isDPMorphism_symm
          (B := (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u))
          _ _ (wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
          (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
          (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp n.len e))
        (wholeSpaceEnvelopeRingLevelAlgEquiv hp m.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
        (ideal_map_of_isDPMorphism_symm
          (B := (Γ((wholeSpaceLevelObj hp e m).obj.thickening.target.scheme, ⊤) : Type u))
          _ _ (wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
          (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
          (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp m.len e))
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) _
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) _
        ((wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff +
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
        ((wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff +
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
        ((wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff +
          ((wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff +
            (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)))
        rfl rfl rfl (Nat.add_left_comm _ _ _)
        (levelSectionsModuleTop hp F e n : Type u) _ _
        (levelSectionsModule hp F n e) (levelSectionsModuleAtLevel hp F n e)
        (levelSectionsIsScalarTowerAtLevel hp F n e)
        (levelSectionsModuleAtAdd hp F n e
          (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
        (levelSectionsIsScalarTowerAtAdd hp F n e
          (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
        (levelSectionsModuleAt hp F n e _ ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
        (levelSectionsIsScalarTowerAt hp F n e _
          ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
        (levelSections_smul_eq hp F n e)
        (levelSectionsModuleTop hp F e m : Type u) _ _
        (levelSectionsModule hp F m e) (levelSectionsModuleAtLevel hp F m e)
        (levelSectionsIsScalarTowerAtLevel hp F m e)
        (levelSectionsModuleAtAdd hp F m e
          (wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff)
        (levelSectionsIsScalarTowerAtAdd hp F m e
          (wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff)
        (levelSectionsModuleAt hp F m e _ ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
        (levelSectionsIsScalarTowerAt hp F m e _
          ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
        (levelSections_smul_eq hp F m e)
        (levelEnvelopeReindex hp φ) (levelEnvelopeReindex_isDPMorphism hp φ)
        (crysSectionsRestrictionAlgHom S (levelTransition hp e φ).hom)
        ((levelTransition hp e φ).hom.targetHom.compatible ⊤)
        (wholeSpaceEnvelopeRingLevelAlgEquiv_naturality hp e φ)
        i (levelSectionsRestriction hp F e φ) (levelFormsDPVertical hp F i e φ))

/-- **The abstract square at the level objects, with the right vertical not yet supplied.**

`Crystalline.tensorFormsLevelComposite_naturality_of_levels` applied to everything that does not
mention the right vertical: the four rings, their divided powers, the two comparisons of
[Stacks, Tag 07KK], the two level identifications
`...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv`, the levels, the module structures and scalar
towers on the sections, the reindexing `...SmallSite.levelEnvelopeReindex` of the variables, the
restriction map `...crysSectionsRestrictionAlgHom` on the section rings, the compatibility
`...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality` of the two ring identifications, and
the left vertical `...SmallSite.levelFormsDPVertical`.  What is left is the right vertical, its
value on a tensor of a wedge, and the value of the left one.

It is separated from `levelTensorFormsCrossingEquiv_naturality` below because reading
`...SmallSite.levelFormsPsi` at the spelling of the abstract square — whose module of completed
differentials is `AdicCompletion (p) Ω_{E(n)}` rather than `Ω_{D(*)}(op (op n))`, inside an
exterior power inside a tensor product — is by itself most of a heartbeat budget, and the
application above is the rest of one.  **No heartbeat limit is raised**; the two halves are two
declarations.  **No tag attribute is placed.** -/
theorem levelFormsCrossingSquareAux : levelFormsCrossingSquareAuxStatement hp F i e φ :=
  @_root_.Crystalline.tensorFormsLevelComposite_naturality_of_levels
      (Γ(S.S.scheme, ⊤) : Type u) _
      (wholeSpaceLevelEnvelope hp n.len)
      (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u)
      (wholeSpaceLevelEnvelope hp m.len)
      (Γ((wholeSpaceLevelObj hp e m).obj.thickening.target.scheme, ⊤) : Type u)
      _ _ _ _
      (wholeSpaceLevelEnvelopeAlgebra hp n.len)
      (affineBaseAppLE S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl).hom.toAlgebra
      (wholeSpaceLevelEnvelopeAlgebra hp m.len)
      (affineBaseAppLE S (wholeSpaceLevelObj hp e m).obj (V := ⊤) le_rfl).hom.toAlgebra
      (wholeSpaceLevelEnvelope hp n.len).ideal
      (wholeSpaceLevelEnvelope hp n.len).dividedPowers
      (wholeSpaceLevelEnvelope hp m.len).ideal
      (wholeSpaceLevelEnvelope hp m.len).dividedPowers
      (affineSituation S hp).p
      (wholeSpaceLevelEnvelope_prime_nilpotent hp n.len)
      (wholeSpaceLevelEnvelope_prime_nilpotent hp m.len)
      (wholeSpaceLevelComparison hp n.len) (wholeSpaceLevelComparison hp m.len)
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).1
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).2
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp m.len e).1
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp m.len e).2
      _ (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj)
      _ (crysDividedPowers S (wholeSpaceLevelObj hp e m).obj)
      (wholeSpaceEnvelopeRingLevelAlgEquiv hp n.len e)
      (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
      (ideal_map_of_isDPMorphism_symm
        (B := (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u))
        _ _ (wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp n.len e))
      (wholeSpaceEnvelopeRingLevelAlgEquiv hp m.len e)
      (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
      (ideal_map_of_isDPMorphism_symm
        (B := (Γ((wholeSpaceLevelObj hp e m).obj.thickening.target.scheme, ⊤) : Type u))
        _ _ (wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp m.len e)
        (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp m.len e))
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) _
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) _
      ((wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff +
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
      ((wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff +
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
      ((wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff +
        ((wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff +
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)))
      rfl rfl rfl (Nat.add_left_comm _ _ _)
      (levelSectionsModuleTop hp F e n : Type u) _ _
      (levelSectionsModule hp F n e) (levelSectionsModuleAtLevel hp F n e)
      (levelSectionsIsScalarTowerAtLevel hp F n e)
      (levelSectionsModuleAtAdd hp F n e
        (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
      (levelSectionsIsScalarTowerAtAdd hp F n e
        (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
      (levelSectionsModuleAt hp F n e _ ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
      (levelSectionsIsScalarTowerAt hp F n e _
        ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
      (levelSections_smul_eq hp F n e)
      (levelSectionsModuleTop hp F e m : Type u) _ _
      (levelSectionsModule hp F m e) (levelSectionsModuleAtLevel hp F m e)
      (levelSectionsIsScalarTowerAtLevel hp F m e)
      (levelSectionsModuleAtAdd hp F m e
        (wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff)
      (levelSectionsIsScalarTowerAtAdd hp F m e
        (wholeSpaceLevelComparison hp m.len).quotientSystem.cutoff)
      (levelSectionsModuleAt hp F m e _ ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
      (levelSectionsIsScalarTowerAt hp F m e _
        ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
      (levelSections_smul_eq hp F m e)
      (levelEnvelopeReindex hp φ) (levelEnvelopeReindex_isDPMorphism hp φ)
      (crysSectionsRestrictionAlgHom S (levelTransition hp e φ).hom)
      ((levelTransition hp e φ).hom.targetHom.compatible ⊤)
      (wholeSpaceEnvelopeRingLevelAlgEquiv_naturality hp e φ)
      i (levelSectionsRestriction hp F e φ) (levelFormsDPVertical hp F i e φ)

/-- The statement of `levelFormsCrossingSquare`: the type of `levelFormsCrossingSquareAux` at the
arguments listed there.  It is a declaration of its own for the same reason as
`levelFormsCrossingSquareAuxStatement`. -/
abbrev levelFormsCrossingSquareStatement : Prop :=
  type_of% (levelFormsCrossingSquareAux hp F i e φ
        (levelFormsPsi hp F i e φ) (levelFormsDPVertical_tmul hp F i e φ)
        fun x w ↦ (levelFormsPsi_tmul_ιMulti hp F i e φ x w).trans
          (congrArg
            (fun y : Fin i → ((wholeSpaceEnvelopeDifferentials hp).obj (op (op m)) : Type u) ↦
              levelSectionsRestriction hp F e φ x ⊗ₜ
                exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj m : Type u) i y)
            (funext fun j ↦ levelEnvelopeDifferentialsMap_eq hp φ (w j))))

/-- **The abstract square at the level objects, with every argument supplied.**

```
M(n)_e ⊗ Ωⁱ_{Γ(T(n)_e,𝒪)} ─────▶ L_n ⊗_{D(n)} ⋀ⁱ Ω_{D(n)}
         │ Φ                                │ Ψ
         ▼                                  ▼
M(m)_e ⊗ Ωⁱ_{Γ(T(m)_e,𝒪)} ─────▶ L_m ⊗_{D(m)} ⋀ⁱ Ω_{D(m)}
```

`levelFormsCrossingSquareAux` is the abstract square of
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` at these objects; this supplies its
three remaining arguments.  The right vertical is `...SmallSite.levelFormsPsi`, the transition map
of `L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}`, whose value on a tensor of a wedge is
`...SmallSite.levelFormsPsi_tmul_ιMulti` read against `Crystalline.completionDifferentialsMapₛₗ`
by `...SmallSite.levelEnvelopeDifferentialsMap_eq`; the value of the left vertical on a pure
tensor is `...SmallSite.levelFormsDPVertical_tmul`.

The two sides are read at the levels `c(n) + (N + e)` and `c(m) + (N + e)` of their own
comparisons of [Stacks, Tag 07KK], and the common level of the square is
`c(n) + (c(m) + (N + e))`.  **No tag attribute is placed.** -/
theorem levelFormsCrossingSquare : levelFormsCrossingSquareStatement hp F i e φ :=
  levelFormsCrossingSquareAux hp F i e φ
      (levelFormsPsi hp F i e φ) (levelFormsDPVertical_tmul hp F i e φ)
      fun x w ↦ (levelFormsPsi_tmul_ιMulti hp F i e φ x w).trans
        (congrArg
          (fun y : Fin i → ((wholeSpaceEnvelopeDifferentials hp).obj (op (op m)) : Type u) ↦
            levelSectionsRestriction hp F e φ x ⊗ₜ
              exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj m : Type u) i y)
          (funext fun j ↦ levelEnvelopeDifferentialsMap_eq hp φ (w j)))

/-- **The cosimplicial naturality of `...SmallSite.levelTensorFormsCrossingEquiv`**, at the
spelling of the level objects rather than that of the abstract square.  This is
`levelFormsCrossingSquare` and nothing else; it is a declaration of its own because the two
spellings of the module of completed differentials — `Ω_{D(*)}(op (op n))` and
`AdicCompletion (p) Ω_{E(n)}` — are compared here, inside an exterior power inside a tensor
product.  **No tag attribute is placed.** -/
theorem levelTensorFormsCrossingEquiv_naturality :
    (levelFormsPsi hp F i e φ).comp
        (levelTensorFormsCrossingEquiv hp F i e n).toAddMonoidHom =
      (levelTensorFormsCrossingEquiv hp F i e m).toAddMonoidHom.comp
        (levelFormsDPVertical hp F i e φ) :=
  levelFormsCrossingSquare hp F i e φ

/-- **The cosimplicial naturality of `...SmallSite.levelTensorFormsCrossingEquiv`, on an
element.** -/
theorem levelTensorFormsCrossingEquiv_naturality_apply (z : levelFormsTensorDP hp F i e n) :
    levelFormsPsi hp F i e φ (levelTensorFormsCrossingEquiv hp F i e n z) =
      levelTensorFormsCrossingEquiv hp F i e m (levelFormsDPVertical hp F i e φ z) :=
  DFunLike.congr_fun (levelTensorFormsCrossingEquiv_naturality hp F i e φ) z

/-! ### The cosimplicial naturality of the degreewise identification -/

/-- **The left vertical on the image of the first identification.**  Conjugating back and forth is
the identity, so `...SmallSite.levelFormsDPVertical` applied to the image of `z` under
`...SmallSite.levelTensorFormsDPEquiv` is the image of the restriction of `z`. -/
theorem levelFormsDPVertical_apply (z : levelFormsTensor hp F i e n) :
    levelFormsDPVertical hp F i e φ (levelTensorFormsDPEquiv hp F i e n z) =
      levelTensorFormsDPEquiv hp F i e m (levelFormsTensorRestriction hp F i e φ z) :=
  congrArg
    (fun w ↦ levelTensorFormsDPEquiv hp F i e m (levelFormsTensorRestriction hp F i e φ w))
    ((levelTensorFormsDPEquiv hp F i e n).symm_apply_apply z)

/-- **The cosimplicial naturality of the degreewise identification
`...SmallSite.levelTensorFormsEquiv`.**

The restriction map of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` along the transition `T(m)_e ⟶ T(n)_e` of the
system of [Stacks, Tag 07JN] is carried by the degreewise identification to the transition map of
the cosimplicial module `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`.

This is `levelTensorFormsCrossingEquiv_naturality` conjugated by
`...SmallSite.levelTensorFormsDPEquiv`, which is exactly what
`...SmallSite.levelFormsDPVertical` was defined to absorb.  **No tag attribute is placed.** -/
theorem levelTensorFormsEquiv_naturality (z : levelFormsTensor hp F i e n) :
    levelFormsPsi hp F i e φ (levelTensorFormsEquiv hp F i e n z) =
      levelTensorFormsEquiv hp F i e m (levelFormsTensorRestriction hp F i e φ z) :=
  (levelTensorFormsCrossingEquiv_naturality_apply hp F i e φ
        (levelTensorFormsDPEquiv hp F i e n z)).trans
    (congrArg (fun w ↦ levelTensorFormsCrossingEquiv hp F i e m w)
      (levelFormsDPVertical_apply hp F i e φ z))

/-! ### The isomorphism `ε` -/

/-- **The degreewise identification between the universe lifts.**  The degree `q` of the
cosimplicial abelian group of sections of the presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level
`(q, e)` is the universe lift of `...SmallSite.levelFormsTensor`, and the degree `q` of
`L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}` is the target of `...SmallSite.levelTensorFormsEquiv`; this is that
identification read between the two lifted spellings, so that the assembly below has nothing left
to unfold.  **No tag attribute is placed.** -/
def levelFormsUliftEquiv (q : SimplexCategory) :
    ULift.{u + 1, u} (levelFormsTensor hp F i e q) ≃+
      ULift.{u + 1, u} ((levelFormsCosimplicialModule hp F i e).obj (op (op q)) : Type u) :=
  (AddEquiv.ulift.trans (levelTensorFormsEquiv hp F i e q)).trans AddEquiv.ulift.symm

/-- **The transition map of the level-`e` sections of the presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`** is
the universe lift of `...SmallSite.levelFormsTensorRestriction`, by `rfl`. -/
theorem levelCosimplicialFormsPresheaf_map {q r : SimplexCategory} (ψ : q ⟶ r)
    (x : ULift.{u + 1, u} (levelFormsTensor hp F i e q)) :
    (levelCosimplicialSections (wholeSpaceSystem S hp)
        (tensorDifferentialFormsPresheaf F i) e).map ψ x =
      ULift.up (levelFormsTensorRestriction hp F i e ψ x.down) :=
  rfl

/-- **The cosimplicial naturality of `levelFormsUliftEquiv`**, in the shape
`Crystalline.cosimplicialModuleForgetUliftIso` consumes: the restriction map of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on the left and `Crystalline.cosimplicialModuleTransition` of
`L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}` on the right.  This is `levelTensorFormsEquiv_naturality`, the
transition map of that cosimplicial module being `...SmallSite.levelFormsPsi` by definition. -/
theorem levelFormsUliftEquiv_naturality {q r : SimplexCategory} (ψ : q ⟶ r)
    (x : ULift.{u + 1, u} (levelFormsTensor hp F i e q)) :
    (levelFormsUliftEquiv hp F i e r
        (ULift.up (levelFormsTensorRestriction hp F i e ψ x.down))).down =
      _root_.Crystalline.cosimplicialModuleTransition (levelFormsCosimplicialModule hp F i e) ψ
        (levelFormsUliftEquiv hp F i e q x).down :=
  (levelTensorFormsEquiv_naturality hp F i e ψ x.down).symm

/-- **The isomorphism `ε` for the presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.**

The cosimplicial abelian group of sections of the presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the
level `e` of the system of [Stacks, Tag 07JN] is isomorphic to the underlying cosimplicial abelian
group of `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`, lifted to the universe the sections live in.

This is `Crystalline.cosimplicialModuleForgetUliftIso` on the degreewise
`...SmallSite.levelTensorFormsEquiv` and its naturality
`levelTensorFormsEquiv_naturality`; `AddEquiv.ulift` crosses the universe lift that the
sections of a presheaf of `AddCommGrpCat.{u + 1}` carry.  **No tag attribute is placed.** -/
def levelCosimplicialFormsPresheafIso :
    levelCosimplicialSections (wholeSpaceSystem S hp) (tensorDifferentialFormsPresheaf F i) e ≅
      (_root_.Crystalline.cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
          (levelFormsCosimplicialModule hp F i e) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  _root_.Crystalline.cosimplicialModuleForgetUliftIso (levelFormsCosimplicialModule hp F i e)
    (levelCosimplicialSections (wholeSpaceSystem S hp) (tensorDifferentialFormsPresheaf F i) e)
    (levelFormsUliftEquiv hp F i e) fun ψ x ↦
      (congrArg (fun y ↦ (levelFormsUliftEquiv hp F i e _ y).down)
          (levelCosimplicialFormsPresheaf_map hp F i e ψ x)).trans
        (levelFormsUliftEquiv_naturality hp F i e ψ x)

/-- **The isomorphism `ε` of the source's proof of [Stacks, Tag 07LF].**

For a locally quasi-coherent sheaf `F` of `𝒪_{X/S}`-modules, a degree `i` and a `p`-adic level
`e`, the cosimplicial abelian group `M(•)_e` of sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the
level `e` of the system of [Stacks, Tag 07JN] is isomorphic to the underlying cosimplicial abelian
group of `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`, for `L_*` the cosimplicial `D(*)`-module
`...SmallSite.levelSectionsCosimplicialModule` of the sections of `F`.  The tensor product is
**uncompleted**.

It is `levelCosimplicialFormsPresheafIso` with the first equality of the source's proof —
`...SmallSite.levelCosimplicialSectionsSheafifyIso`, the sheafification unit — composed in.  **No
tag attribute is placed**: this is the input of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso`, not a clause of a tag. -/
def levelCosimplicialSectionsFormsIso (hF : IsLocallyQuasiCoherent F) :
    levelCosimplicialSections (wholeSpaceSystem S hp) (tensorDifferentialFormsSheaf F i).obj e ≅
      (_root_.Crystalline.cosimplicialModuleForget (wholeSpaceEnvelopeRing hp)).obj
          (levelFormsCosimplicialModule hp F i e) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (levelCosimplicialSectionsSheafifyIso hp F hF i e).symm ≪≫
    levelCosimplicialFormsPresheafIso hp F i e

end Degreewise

/-! ### [Stacks, Tag 07LF] -/

/-- **[Stacks, Lemma 60.19.3, Tag 07LF].**  Let `(p, (S, I, γ), X)` be a global crystalline
situation with `X` and `S` affine, and let `F` be a sheaf of `𝒪_{X/S}`-modules on the small
crystalline site which is locally quasi-coherent and whose comparison morphisms along closed
immersions are surjective — the two hypotheses of [Stacks, Tag 07JN].  Then

`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`  for every `i > 0` and every `j ≥ 0`.

The proof is the source's own.  `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso`
reduces the statement to the existence, at every `p`-adic level `e`, of a cosimplicial
`D(*)`-module `L_*` and an isomorphism `M(•)_e ≅ L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}` of cosimplicial
abelian groups with the tensor product **uncompleted**; `L_*` is
`...SmallSite.levelSectionsCosimplicialModule` and the isomorphism is
`...SmallSite.levelCosimplicialSectionsFormsIso`. -/
@[stacks 07LF "the vanishing of the cohomology of F ⊗ Ω^i for i > 0, X and S affine"]
theorem vanishing07LF (S : GlobalCrystallineSituation.{u}) : Vanishing07LF S := by
  intro hX hS
  let := hX
  let := hS
  exact vanishing07LF_of_levelCosimplicialSectionsIso
    (fun F hF _ i _ e ↦ ⟨levelSectionsCosimplicialModule
        (isNilpotent_prime_sections_of_isAffine S) F e,
      ⟨levelCosimplicialSectionsFormsIso (isNilpotent_prime_sections_of_isAffine S) F i e hF⟩⟩)
    hX hS

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
