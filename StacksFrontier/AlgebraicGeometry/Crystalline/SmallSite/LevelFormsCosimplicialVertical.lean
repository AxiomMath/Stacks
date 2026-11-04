module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Acyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFormsNaturalitySquares
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsCosimplicialModule

/-!
# The right-hand input of the cosimplicial naturality of the degreewise identification

`Crystalline.tensorFormsLevelComposite_naturality` of
`ModuleDifferentials/LevelFormsCompositeNaturality.lean` is the abstract square from which the
cosimplicial naturality of `...SmallSite.levelTensorFormsEquiv` is to be deduced, and it has
three concrete inputs at the level objects of `...SmallSite.wholeSpaceSystem`.  Two of them —
`hcomm` and `hPhi` — are `...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality` and
`...SmallSite.levelFormsDPVertical_tmul` of `SmallSite/LevelFormsNaturalitySquares.lean`.  **This
file supplies the third**, the value `hPsi` of the right vertical.

```
M(n)_e ⊗ Ωⁱ_{Γ(T(n)_e,𝒪)} ─────▶ L_n ⊗_{D(n)} ⋀ⁱ Ω_{D(n)}
         │ Φ                                │ Ψ
         ▼                                  ▼
M(m)_e ⊗ Ωⁱ_{Γ(T(m)_e,𝒪)} ─────▶ L_m ⊗_{D(m)} ⋀ⁱ Ω_{D(m)}
```

The right vertical `Ψ` is the transition map of the cosimplicial module
`L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}` along `φ : ⦋n⦌ ⟶ ⦋m⦌`, and `hPsi` says that it carries
`x ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to `(x|_{T(m)_e}) ⊗ ĝ(ω₁) ∧ ⋯ ∧ ĝ(ωᵢ)` for `ĝ` the completed reindexing of
the variables of the envelopes.  **Typing that transition map at the tensor product the abstract
square speaks about is the whole difficulty, and the implementation notes below record how it is
handled.**

## Main definitions

* `...SmallSite.levelFormsCosimplicialModule` — the cosimplicial module
  `L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}` whose degree-`n` term the degreewise identification lands in, named
  once.
* `...SmallSite.levelFormsPsi` — **the right vertical `Ψ`**, the transition map of that
  cosimplicial module, typed at the tensor product
  `Crystalline.tensorFormsLevelComposite` produces.
* `...SmallSite.levelEnvelopeDifferentialsMap` — the transition map of `Ω_{D(*)}`, as an additive
  map between the degrees written `Ω_{D(*)}(op (op n))`.

## Main results

* `...SmallSite.levelEnvelopeReindex_isDPMorphism` — the reindexing of the variables of the
  uncompleted envelopes is a divided power morphism.  This is the hypothesis `hg` of
  `Crystalline.tensorFormsLevelComposite_naturality`.
* `...SmallSite.levelEnvelopeDifferentialsMap_eq` — that transition map is
  `Crystalline.completionDifferentialsMapₛₗ` of the reindexing, by `rfl`.  This is the map `hPsi`
  is stated against in the abstract square.
* `...SmallSite.levelFormsExtPow_map_ιMulti` — the transition map of `⋀ⁱ Ω_{D(*)}` carries a wedge
  to the wedge of the images, by the `transition_mk` field of
  `Crystalline.ExteriorPowerFunctor`.
* `...SmallSite.levelFormsPsi_tmul` — the right vertical on a pure tensor, by `rfl`.
* `...SmallSite.levelFormsPsi_tmul_ιMulti` — **the hypothesis `hPsi`.**

## Implementation notes

**The `CategoryTheory.opOp` reindexing is undone with the cosimplicial module a variable.**
`Crystalline.cosimplicialModuleForget` indexes the degree `n` of its value by
`(opOp SimplexCategory).obj n`, while `...SmallSite.levelTensorFormsCrossingEquiv` and the
abstract square are written at `op (op n)`.  Substituting one index term for the other is `rfl`
on its own, but inside `M.obj` for `M = L_* ⊗ ⋀ⁱ Ω_{D(*)}` the unifier attempts congruence
first, fails, unfolds `M.obj` on both sides and descends through the tensor product into the
exterior-algebra tower with two differently-spelled index and instance terms; it does not
terminate inside the heartbeat budget.  On these very objects, as single-`rfl` goals:
the substitution is immediate at `L_* ⊗ L_*`, at `L_* ⊗ Ω_{D(*)}` and at `⋀ⁱ Ω_{D(*)}` on its
own, and at `L_* ⊗ ⋀ⁱ Ω_{D(*)}` it exhausts the budget — it is the exterior power *under* the
tensor product, and neither factor alone.

`Crystalline.cosimplicialModuleTransition` of `Cosimplicial/Acyclicity.lean` is that substitution
performed once, with the cosimplicial module a *variable*, where the unifier cannot descend into
`M.obj` at all and has to unify the indices — which is the one cheap step.
`...SmallSite.levelFormsPsi` is its instantiation, and its stated type is the tensor product
`Crystalline.tensorFormsLevelComposite` lands in, so the identification is paid for once in that
definition and every later use of `levelFormsPsi` is syntactic.  **No heartbeat limit is raised
anywhere.**

**The `D(n)`-module structure on the renamed sections is declared.**
`...SmallSite.levelSectionsModule` is an instance at the spelling
`F.val.obj (op (T(n)_e))`, and `...SmallSite.levelSectionsModuleTop` — the same type with the
ring of scalars written `Γ(T(n)_e, 𝒪)`, which is the carrier
`...SmallSite.levelTensorFormsCrossingEquiv` is stated over — is a different `DiscrTree` key, so
the instance is invisible there and a pure tensor of a section cannot be written down.
`...SmallSite.levelSectionsModuleTopModule` is the renaming, paid for once as the implementation
notes of `SmallSite/LevelSectionsFormsIso.lean` prescribe for this area.

**The transition map of `Ω_{D(*)}` is named at the `op (op n)` spelling.**
`Crystalline.completionDifferentialsMapₛₗ` lands in
`AdicCompletion (p) Ω_{E(m)}`, over whose scalars written `AdicCompletion (p) E(m)` there is a
module instance; the ring here is spelled `(wholeSpaceEnvelopeRing hp).obj m` instead, where
there is not, so a wedge of its values does not elaborate.
`...SmallSite.levelEnvelopeDifferentialsMap` is the same map with both ends written at the
spelling `⋀ⁱ` is taken over, and `...SmallSite.levelEnvelopeDifferentialsMap_eq` is the bridge.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved.**  The third concrete input of
`Crystalline.tensorFormsLevelComposite_naturality` is supplied; **the square itself is not
assembled here and no isomorphism of cosimplicial objects is constructed.**

What once blocked that assembly was that the abstract square carries a single finite level `k`
for both of its two sides, with `cmp.quotientSystem.cutoff + e = k` on one and
`cmp'.quotientSystem.cutoff + e' = k` on the other, while the cutoff of
`...SmallSite.wholeSpaceLevelComparison` is a `Classical.choose` that depends on the cosimplicial
degree, so no `k` serves every degree at once.  **That is no longer an obstruction.**
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` of
`ModuleDifferentials/LevelFormsCompositeTwoLevels.lean` is the square with the two sides at two
independent levels, over the level independence of
`ModuleDifferentials/CompletionLevelIndependence.lean`; what is left is the instantiation of it
at these objects, and `SmallSite/TensorRestrictionVanishing.lean` records under "What `ε` owes
now" exactly which arguments the three inputs of this file and of
`SmallSite/LevelFormsNaturalitySquares.lean` supply to it.

Nothing is assumed of the sheaf `F`: neither hypothesis (1) nor hypothesis (2) of
[Stacks, Tag 07JN] is used, and no hypothesis beyond `hp` and the two affineness instances that
`...SmallSite.levelTensorFormsEquiv` itself carries is introduced.  Nothing is assumed of `i`
either.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07L1](https://stacks.math.columbia.edu/tag/07L1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]
variable (F : SheafOfModules.{u} (structureSheaf S)) (i e : ℕ) {n m : SimplexCategory}
  (φ : n ⟶ m)

/-! ### The cosimplicial module `L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}` -/

/-- **The cosimplicial `D(*)`-module `L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}`**, the one the hypothesis `hiso`
of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for an isomorphism onto, for
`L_*` the cosimplicial module `...SmallSite.levelSectionsCosimplicialModule` of the sections of
`F` at the `p`-adic level `e`.  The tensor product is the one of
`CategoryTheory.PresheafOfModules` and is **uncompleted**. -/
abbrev levelFormsCosimplicialModule :
    _root_.Crystalline.CosimplicialModule (wholeSpaceEnvelopeRing hp) :=
  levelSectionsCosimplicialModule hp F e ⊗
    (_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
      (wholeSpaceEnvelopeDifferentials hp)

/-- **The sections of `F` over the level `(q, e)` are a `D(q)`-module at the spelling
`...SmallSite.levelSectionsModuleTop` as well.**  `...SmallSite.levelSectionsModule` is declared
at `F.val.obj (op (T(q)_e))`; this is the same instance at the renaming the tensor products of
`...SmallSite.levelTensorFormsCrossingEquiv` are written over.  See the implementation notes. -/
instance levelSectionsModuleTopModule (q : SimplexCategory) :
    Module ((wholeSpaceEnvelopeRing hp).obj q) (levelSectionsModuleTop hp F e q) :=
  levelSectionsModule hp F q e

/-- **The right vertical `Ψ` of the naturality square**: the transition map of
`...SmallSite.levelFormsCosimplicialModule` along `φ`, typed at the tensor product
`Crystalline.tensorFormsLevelComposite` lands in — which is the target of
`...SmallSite.levelTensorFormsCrossingEquiv`.

It is built rather than assumed, which is what
`Crystalline.tensorFormsLevelComposite_naturality` asks for: that statement takes the vertical as
an arbitrary additive map and uses only its value on a tensor of a wedge. -/
def levelFormsPsi :
    TensorProduct ((wholeSpaceEnvelopeRing hp).obj n : Type u)
        (F.val.obj (op (wholeSpaceLevelObj hp e n)) : Type u)
        ↥(⋀[((wholeSpaceEnvelopeRing hp).obj n : Type u)]^i
          ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) →+
      TensorProduct ((wholeSpaceEnvelopeRing hp).obj m : Type u)
        (F.val.obj (op (wholeSpaceLevelObj hp e m)) : Type u)
        ↥(⋀[((wholeSpaceEnvelopeRing hp).obj m : Type u)]^i
          ((wholeSpaceEnvelopeDifferentials hp).obj (op (op m)) : Type u)) :=
  _root_.Crystalline.cosimplicialModuleTransition (levelFormsCosimplicialModule hp F i e) φ

/-! ### The transition map of `Ω_{D(*)}` -/

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The reindexing of the variables of the uncompleted envelopes is a divided power
morphism.**  This is the second component of `Crystalline.envelopeReindex`, and it is the
hypothesis `hg` of `Crystalline.tensorFormsLevelComposite_naturality` at these objects. -/
theorem levelEnvelopeReindex_isDPMorphism :
    DividedPowers.IsDPMorphism (wholeSpaceLevelEnvelope hp n.len).dividedPowers
      (wholeSpaceLevelEnvelope hp m.len).dividedPowers
      (letI := wholeSpaceLevelEnvelopeAlgebra hp n.len
       letI := wholeSpaceLevelEnvelopeAlgebra hp m.len
       (levelEnvelopeReindex hp φ).toRingHom) :=
  (_root_.Crystalline.envelopeReindex (affineSituation S hp)
    (_root_.Crystalline.canonicalPresentation (affineSituation S hp)) φ).1.isDPMorphism

/-- **The transition map `Ω_{D(n)} ⟶ Ω_{D(m)}` of the cosimplicial module `Ω_{D(*)}`**, as an
additive map between the degrees written `Ω_{D(*)}(op (op n))`.  The renaming is what lets a
wedge of its values be written down; see the implementation notes. -/
def levelEnvelopeDifferentialsMap :
    ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u) →+
      ((wholeSpaceEnvelopeDifferentials hp).obj (op (op m)) : Type u) :=
  ((wholeSpaceEnvelopeDifferentials hp).map φ.op.op).hom.toAddMonoidHom

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The transition map of `Ω_{D(*)}` is `Crystalline.completionDifferentialsMapₛₗ` of the
reindexing of the variables.**  Both sides are `Crystalline.adicCompletionMapₛₗ` of the
functoriality `Crystalline.mapDifferentialsOfDPMorphism` of the divided power differentials at
`Crystalline.envelopeReindexAlgHom`, so this holds by `rfl`.  It is what lets the hypothesis
`hPsi` of `Crystalline.tensorFormsLevelComposite_naturality`, which is stated against
`Crystalline.completionDifferentialsMapₛₗ`, be read against the cosimplicial structure map. -/
theorem levelEnvelopeDifferentialsMap_eq
    (y : ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) :
    letI := wholeSpaceLevelEnvelopeAlgebra hp n.len
    letI := wholeSpaceLevelEnvelopeAlgebra hp m.len
    levelEnvelopeDifferentialsMap hp φ y =
      _root_.Crystalline.completionDifferentialsMapₛₗ
        (wholeSpaceLevelEnvelope hp n.len).ideal
        (wholeSpaceLevelEnvelope hp n.len).dividedPowers
        (wholeSpaceLevelEnvelope hp m.len).ideal
        (wholeSpaceLevelEnvelope hp m.len).dividedPowers
        (affineSituation S hp).p (levelEnvelopeReindex hp φ)
        (levelEnvelopeReindex_isDPMorphism hp φ) y :=
  rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The transition map of `⋀ⁱ Ω_{D(*)}` carries a wedge to the wedge of the images.**  This is
the `transition_mk` field of `Crystalline.ExteriorPowerFunctor`, whose `componentIso` is the
identity for `Crystalline.exteriorPowerFunctor`, and `ModuleCat.exteriorPower.mk` is
`exteriorPower.ιMulti`. -/
theorem levelFormsExtPow_map_ιMulti
    (w : Fin i → ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) :
    ((_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
        (wholeSpaceEnvelopeDifferentials hp)).map φ.op.op
        (exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj n : Type u) i w) =
      exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj m : Type u) i
        (fun j ↦ levelEnvelopeDifferentialsMap hp φ (w j)) :=
  (_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).transition_mk
    (wholeSpaceEnvelopeDifferentials hp) φ w

/-! ### The right vertical on a tensor of a wedge -/

/-- **The right vertical on a pure tensor** is the restriction map of `F` tensored with the
transition map of `⋀ⁱ Ω_{D(*)}`.  This is
`CategoryTheory.PresheafOfModules.Monoidal.tensorObj_map_tmul`, read at the renamed carriers, and
it holds by `rfl`. -/
theorem levelFormsPsi_tmul (x : (levelSectionsModuleTop hp F e n : Type u))
    (y : ↥(⋀[((wholeSpaceEnvelopeRing hp).obj n : Type u)]^i
      ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u))) :
    levelFormsPsi hp F i e φ (x ⊗ₜ y) =
      levelSectionsRestriction hp F e φ x ⊗ₜ
        ((_root_.Crystalline.exteriorPowerFunctor (wholeSpaceEnvelopeRing hp) i).functor.obj
          (wholeSpaceEnvelopeDifferentials hp)).map φ.op.op y :=
  rfl

/-- **The hypothesis `hPsi` of `Crystalline.tensorFormsLevelComposite_naturality` at the level
objects of `...SmallSite.wholeSpaceSystem`.**

The right vertical `...SmallSite.levelFormsPsi` — the transition map of
`L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}` — carries a section of `F` over the level `(n, e)` tensored with a
wedge of elements of `Ω_{D(n)}` to the restriction of the section tensored with the wedge of
their images under the transition map of `Ω_{D(*)}`.
`...SmallSite.levelEnvelopeDifferentialsMap_eq` rewrites that transition map as the
`Crystalline.completionDifferentialsMapₛₗ` the abstract square is stated against, and
`Crystalline.tensorExteriorPower_addMonoidHom_ext` is why these values determine the vertical, so
this is the hypothesis and not a weaker statement.

The proof chains `levelFormsPsi_tmul` and `levelFormsExtPow_map_ιMulti`, each as its own
`congrArg`.  **No tag attribute is placed.** -/
theorem levelFormsPsi_tmul_ιMulti (x : (levelSectionsModuleTop hp F e n : Type u))
    (w : Fin i → ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) :
    levelFormsPsi hp F i e φ
        (x ⊗ₜ exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj n : Type u) i w) =
      levelSectionsRestriction hp F e φ x ⊗ₜ
        exteriorPower.ιMulti ((wholeSpaceEnvelopeRing hp).obj m : Type u) i
          (fun j ↦ levelEnvelopeDifferentialsMap hp φ (w j)) :=
  (levelFormsPsi_tmul hp F i e φ x _).trans
    (congrArg (fun z ↦ levelSectionsRestriction hp F e φ x ⊗ₜ z)
      (levelFormsExtPow_map_ιMulti hp i φ w))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
