module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectFormsDPNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsCompositeNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsFormsIso

/-!
# The two left-hand inputs of the cosimplicial naturality of the degreewise identification

`...SmallSite.levelTensorFormsEquiv` of `SmallSite/LevelSectionsFormsIso.lean` is the degreewise
value of the isomorphism `ε` that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for, and
`Crystalline.tensorFormsLevelComposite_naturality` of
`ModuleDifferentials/LevelFormsCompositeNaturality.lean` is the abstract square its cosimplicial
naturality is to be deduced from.  That abstract square has three concrete inputs at the level
objects of `...SmallSite.wholeSpaceSystem`: the compatibility `hcomm` of the two ring
identifications with the cosimplicial transition maps, the value `hPhi` of the left vertical on a
pure tensor, and the value `hPsi` of the right vertical.  **This file supplies the first two.**

```
M(n)_e ⊗ Ωⁱ_{Γ(T(n)_e,𝒪)} ─────▶ L_n ⊗_{D(n)} ⋀ⁱ Ω_{D(n)}
         │ Φ                                │ Ψ
         ▼                                  ▼
M(m)_e ⊗ Ωⁱ_{Γ(T(m)_e,𝒪)} ─────▶ L_m ⊗_{D(m)} ⋀ⁱ Ω_{D(m)}
```

## The compatibility of the ring identifications

`...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv` identifies the section ring of the level
`(n, e)` with the finite level `D(n)/(p)^{N + e}`, and `hcomm` says that the square

```
Γ(T(n)_e, 𝒪) ───▶ D(n)/(p)^{N + e}
     │ u                 │ ĝ
     ▼                   ▼
Γ(T(m)_e, 𝒪) ───▶ D(m)/(p)^{N + e}
```

of `Γ(S, ⊤)`-algebra maps commutes, `u` being the restriction map and `ĝ` the descent
`Crystalline.completedLevelAlgHom` to the level of the `p`-adic completion of the reindexing
`Crystalline.envelopeReindexAlgHom` of the variables of the uncompleted envelopes.  There is no
naturality statement for the algebra isomorphism — only for the ring isomorphism,
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` — and `AlgHom.ext` is what repackages it; the
one thing to check is that the completion of the reindexing *is* the structure map of
`...SmallSite.wholeSpaceEnvelopeRing`, which holds by `rfl` because both sides are
`Crystalline.adicCompletionRingMap` of the same ring map.

## Main definitions

* `...SmallSite.levelTransition` — the transition morphism `T(m)_e ⟶ T(n)_e` of the system of
  [Stacks, Tag 07JN], named once.
* `...SmallSite.levelEnvelopeReindex` — the reindexing `E(n) ⟶ E(m)` of the uncompleted
  envelopes, as a morphism of `Γ(S, ⊤)`-algebras.
* `...SmallSite.levelSectionsRestrictionAlgHom` — the restriction map on the section rings of the
  levels, as a morphism of `Γ(S, ⊤)`-algebras.
* `...SmallSite.levelFormsTensor`, `...SmallSite.levelFormsTensorDP` — the source and the target
  of `...SmallSite.levelTensorFormsDPEquiv`, named so that the pure tensors of the one are
  elaborated at the ring the other is stated over.
* `...SmallSite.levelFormsTensorRestriction`, `...SmallSite.levelSectionsRestriction`,
  `...SmallSite.levelFormsRestriction` — the restriction maps of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, of
  `F` and of `Ω^i_{X/S}` over the transition, as additive maps between the renamed section
  groups.
* `...SmallSite.levelDPFormsMap` — the transition on divided power differential forms at the
  level objects, which is the right-hand side of `hPhi`.
* `...SmallSite.levelFormsDPVertical` — **the left vertical `Φ`**, the restriction map conjugated
  by `...SmallSite.levelTensorFormsDPEquiv`.

## Main results

* `...SmallSite.completedAlgHom_levelEnvelopeReindex_toRingHom` — the completion of the
  reindexing is the structure map of `D(*)`, by `rfl`.
* `...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality` — **the hypothesis `hcomm`.**
* `...SmallSite.levelFormsDPVertical_tmul` — **the hypothesis `hPhi`**: the left vertical carries
  `x ⊗ ω` to `(x|_{T(m)_e}) ⊗ Ωⁱ(u) ω`.

## Implementation notes

**The verticals are conjugated, not assumed.**  `...SmallSite.levelFormsDPVertical` is
`D ∘ R ∘ D⁻¹` for `D` the first identification and `R` the restriction map of the presheaf tensor
product, which is exactly the shape in which the abstract square consumes it; its value on a pure
tensor is computed from `TensorProduct.congr_symm_tmul`, the value of `R` on a pure tensor —
`PresheafOfModules.Monoidal.tensorObj_map_tmul`, which is `rfl` — and
`...affineCrysDifferentialFormsIso_naturality_dp`.

**Every step is a named lemma and every proof is in term mode.**  `rw` and `set` on these terms
pose `isDefEq` problems that do not terminate inside the heartbeat budget even though they
elaborate immediately in a small context; the chains below are built out of `congrArg` and
`Eq.trans` for that reason.

**The three restriction maps are named with the renamed rings in their types.**  The
`PresheafOfModules` restriction map lands in a restriction of scalars, so its codomain carries the
module structure over the ring of the *source*; writing a pure tensor of its values asks for a
module structure at that spelling and the search fails.  `...SmallSite.levelSectionsRestriction`
and `...SmallSite.levelFormsRestriction` are the same two maps with the codomains written at the
rings `...SmallSite.levelTensorFormsDPEquiv` is stated over.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved.**  Two of the three concrete
inputs of `Crystalline.tensorFormsLevelComposite_naturality` are supplied; the third, the value of
the right vertical — the transition map of the cosimplicial module
`L_* ⊗_{D(*)} ⋀ⁱ Ω_{D(*)}` — is **not** supplied here, and no isomorphism of cosimplicial objects
is constructed.  Nothing is assumed of the sheaf `F`: neither hypothesis (1) nor hypothesis (2) of
[Stacks, Tag 07JN] is used, and no hypothesis beyond `hp` and the two affineness instances that
`...SmallSite.levelTensorFormsEquiv` itself carries is introduced.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
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

/-! ### The transition maps -/

/-- **The transition morphism `T(m)_e ⟶ T(n)_e`** of the system of [Stacks, Tag 07JN] along
`φ : ⦋n⦌ ⟶ ⦋m⦌`, named once.  Taking sections reverses the direction, which is what makes the
sections cosimplicial. -/
abbrev levelTransition : wholeSpaceLevelObj hp e m ⟶ wholeSpaceLevelObj hp e n :=
  ((wholeSpaceSystem S hp).map φ.op).app e

/-- **The reindexing `E(n) ⟶ E(m)` of the uncompleted envelopes**, as a morphism of
`Γ(S, ⊤)`-algebras.  This is `Crystalline.envelopeReindexAlgHom` at the situation's own
presentation: it renames the variable `x_c(j)` of the `(n + 1)`-fold tensor power to `x_c(φ(j))`.
Its divided power half is the second field of `Crystalline.envelopeReindex`, and it is the algebra
map `g` of `Crystalline.tensorFormsLevelComposite_naturality` at these objects. -/
abbrev levelEnvelopeReindex :
    letI := wholeSpaceLevelEnvelopeAlgebra hp n.len
    letI := wholeSpaceLevelEnvelopeAlgebra hp m.len
    wholeSpaceLevelEnvelope hp n.len →ₐ[(Γ(S.S.scheme, ⊤) : Type u)]
      wholeSpaceLevelEnvelope hp m.len :=
  _root_.Crystalline.envelopeReindexAlgHom (affineSituation S hp)
    (_root_.Crystalline.canonicalPresentation (affineSituation S hp)) φ

/-- **The restriction map on the section rings of the levels, as a morphism of
`Γ(S, ⊤)`-algebras.**  The underlying ring map is the restriction map of `𝒪_{X/S}` along
`levelTransition`; the commutation with the two structure maps is
`...crysBaseAppLE_fac`.  This is the divided power morphism `u` of
`Crystalline.tensorFormsLevelComposite_naturality` at the level objects. -/
def levelSectionsRestrictionAlgHom :
    letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e n)
    letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e m)
    ((structureSheaf S).obj.obj (op (wholeSpaceLevelObj hp e n)) : Type u) →ₐ[
        (Γ(S.S.scheme, ⊤) : Type u)]
      ((structureSheaf S).obj.obj (op (wholeSpaceLevelObj hp e m)) : Type u) :=
  letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e n)
  letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e m)
  { ((structureSheaf S).obj.map (levelTransition hp e φ).op).hom with
    commutes' := fun a ↦ congrArg (fun q ↦ CommRingCat.Hom.hom q a)
      (crysBaseAppLE_fac S (levelTransition hp e φ).hom).symm }

/-! ### The compatibility of the ring identifications -/

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The `p`-adic completion of the reindexing of the variables is the structure map of
`D(*)`.**  Both sides are `Crystalline.adicCompletionRingMap` of the ring map underlying
`Crystalline.envelopeReindex`, so this holds by `rfl`; it is what lets the naturality of the ring
identification be read against `Crystalline.completedLevelAlgHom`. -/
theorem completedAlgHom_levelEnvelopeReindex_toRingHom :
    letI := wholeSpaceLevelEnvelopeAlgebra hp n.len
    letI := wholeSpaceLevelEnvelopeAlgebra hp m.len
    (_root_.Crystalline.completedAlgHom (affineSituation S hp).p
        (levelEnvelopeReindex hp φ)).toRingHom =
      ((wholeSpaceEnvelopeRing hp).map φ).hom :=
  rfl

/-- **The hypothesis `hcomm` of `Crystalline.tensorFormsLevelComposite_naturality` at the level
objects of `...SmallSite.wholeSpaceSystem`.**

The identification `...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv` of the section ring of the
level `(n, e)` with `D(n)/(p)^{N + e}` carries the restriction map along the transition
`T(m)_e ⟶ T(n)_e` to the descent `Crystalline.completedLevelAlgHom` of the completed reindexing
`D(n) ⟶ D(m)` to that finite level, as an equality of `Γ(S, ⊤)`-algebra maps.

This is `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` — the same statement for the
underlying *ring* isomorphism — through `AlgHom.ext`, together with
`completedAlgHom_levelEnvelopeReindex_toRingHom`.  **No tag attribute is placed.** -/
theorem wholeSpaceEnvelopeRingLevelAlgEquiv_naturality :
    letI := wholeSpaceLevelEnvelopeAlgebra hp n.len
    letI := wholeSpaceLevelEnvelopeAlgebra hp m.len
    letI := levelEnvelopeAlgebra hp n.len
    letI := levelEnvelopeAlgebra hp m.len
    letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e n)
    letI := crysSectionsAlgebra (wholeSpaceLevelObj hp e m)
    (wholeSpaceEnvelopeRingLevelAlgEquiv hp m.len e).toAlgHom.comp
        (levelSectionsRestrictionAlgHom hp e φ) =
      (_root_.Crystalline.completedLevelAlgHom (affineSituation S hp).p
            (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
            (levelEnvelopeReindex hp φ)).comp
        (wholeSpaceEnvelopeRingLevelAlgEquiv hp n.len e).toAlgHom :=
  let := wholeSpaceLevelEnvelopeAlgebra hp n.len
  let := wholeSpaceLevelEnvelopeAlgebra hp m.len
  let := levelEnvelopeAlgebra hp n.len
  let := levelEnvelopeAlgebra hp m.len
  let := crysSectionsAlgebra (wholeSpaceLevelObj hp e n)
  let := crysSectionsAlgebra (wholeSpaceLevelObj hp e m)
  AlgHom.ext fun x ↦
    wholeSpaceEnvelopeRingLevelEquiv_map hp (n := n.len) (m := m.len) φ e x

/-! ### The divided power differential forms at the level objects -/

/-- **The module `Ω^i_{Γ(T(q)_e,𝒪)/Γ(S,⊤),δ(q)}` of divided power differential forms at the level
`(q, e)`**, with the algebra instance supplied positionally as
`...SmallSite.levelTensorFormsDPEquiv` supplies it. -/
abbrev levelDPForms (q : SimplexCategory) :=
  @_root_.Crystalline.dividedPowerDifferentialForms (Γ(S.S.scheme, ⊤) : Type u)
    (Γ((wholeSpaceLevelObj hp e q).obj.thickening.target.scheme, ⊤) : Type u) _ _
    (crysTopAlgebra S (wholeSpaceLevelObj hp e q).obj) _
    (crysDividedPowers S (wholeSpaceLevelObj hp e q).obj) i

/-- **The transition map on divided power differential forms at the level objects**: the
functoriality `Crystalline.mapDifferentialFormsOfDPMorphism` of
`Crystalline.dividedPowerDifferentialForms` at the restriction map on sections.  This is the
right-hand side of the hypothesis `hPhi` of
`Crystalline.tensorFormsLevelComposite_naturality`. -/
abbrev levelDPFormsMap :=
  @_root_.Crystalline.mapDifferentialFormsOfDPMorphism (Γ(S.S.scheme, ⊤) : Type u)
    (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u) _ _
    (crysTopAlgebra S (wholeSpaceLevelObj hp e n).obj) _
    (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj)
    (Γ((wholeSpaceLevelObj hp e m).obj.thickening.target.scheme, ⊤) : Type u) _
    (crysTopAlgebra S (wholeSpaceLevelObj hp e m).obj) _
    (crysDividedPowers S (wholeSpaceLevelObj hp e m).obj)
    (crysSectionsRestrictionAlgHom S (levelTransition hp e φ).hom)
    ((levelTransition hp e φ).hom.targetHom.compatible ⊤) i

/-! ### The restriction maps with the renamed rings -/

/-- **The source of `...SmallSite.levelTensorFormsDPEquiv`**, which is the right-hand side of the
section identification `...SmallSite.levelTensorFormsTop_eq`: the tensor product of the sections
of `F` over the level `(q, e)` with the sections of `Ω^i_{X/S}` there. -/
abbrev levelFormsTensor (q : SimplexCategory) : Type u :=
  TensorProduct Γ((wholeSpaceLevelObj hp e q).obj.thickening.target.scheme, ⊤)
    (levelSectionsModuleTop hp F e q : Type u)
    ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
      (op (wholeSpaceLevelObj hp e q).obj) : Type u)

/-- **The target of `...SmallSite.levelTensorFormsDPEquiv`**: the sections of `F` over the level
`(q, e)` tensored with the divided power differential forms there. -/
abbrev levelFormsTensorDP (q : SimplexCategory) : Type u :=
  TensorProduct Γ((wholeSpaceLevelObj hp e q).obj.thickening.target.scheme, ⊤)
    (levelSectionsModuleTop hp F e q : Type u) (levelDPForms hp i e q)

/-- **The restriction map of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the transition
`T(m)_e ⟶ T(n)_e`**, as an additive map between the two tensor products of
`...SmallSite.levelFormsTensor`. -/
def levelFormsTensorRestriction :
    levelFormsTensor hp F i e n →+ levelFormsTensor hp F i e m :=
  ((tensorDifferentialForms (sheafValComm F) i).map
    (levelTransition hp e φ).op).hom.toAddMonoidHom

/-- **The restriction map of `F` over the transition**, with the ring of scalars of the codomain
written `Γ(T(m)_e, 𝒪)`.  This is the map `phi` on the coefficients that
`Crystalline.tensorFormsLevelComposite_naturality` takes. -/
def levelSectionsRestriction :
    (levelSectionsModuleTop hp F e n : Type u) →+ (levelSectionsModuleTop hp F e m : Type u) :=
  (F.val.map (levelTransition hp e φ).op).hom.toAddMonoidHom

/-- **The restriction map of `Ω^i_{X/S}` over the transition**, with the ring of scalars of the
codomain written `Γ(T(m)_e, 𝒪)`, read on the big crystalline category where
`...affineCrysDifferentialFormsIso` lives. -/
def levelFormsRestriction :
    ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
        (op (wholeSpaceLevelObj hp e n).obj) : Type u) →+
      ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
        (op (wholeSpaceLevelObj hp e m).obj) : Type u) :=
  ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).map
    (levelTransition hp e φ).hom.op).hom.toAddMonoidHom

/-- **The restriction map of the presheaf tensor product on a pure tensor** is the tensor of the
two restriction maps.  This is `PresheafOfModules.Monoidal.tensorObj_map_tmul` with the two
factors read at the renamed rings, and it holds by `rfl`. -/
theorem levelFormsTensorRestriction_tmul (x : (levelSectionsModuleTop hp F e n : Type u))
    (z : ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
      (op (wholeSpaceLevelObj hp e n).obj) : Type u)) :
    levelFormsTensorRestriction hp F i e φ (x ⊗ₜ z) =
      levelSectionsRestriction hp F e φ x ⊗ₜ levelFormsRestriction hp i e φ z := rfl

/-! ### The left vertical and its value on a pure tensor -/

/-- The first identification on a pure tensor: it is the identity on the sections of `F` and
[Stacks, Tag 07J0] on the forms. -/
theorem levelTensorFormsDPEquiv_tmul (q : SimplexCategory)
    (x : (levelSectionsModuleTop hp F e q : Type u))
    (z : ((_root_.Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
      (op (wholeSpaceLevelObj hp e q).obj) : Type u)) :
    levelTensorFormsDPEquiv hp F i e q (x ⊗ₜ z) =
      (x ⊗ₜ affineCrysDifferentialFormsIso S (wholeSpaceLevelObj hp e q).obj (V := ⊤) le_rfl
        (isAffineOpen_top S.S.scheme) i z : levelFormsTensorDP hp F i e q) :=
  TensorProduct.congr_tmul _ _ x z

/-- The inverse of the first identification on a pure tensor. -/
theorem levelTensorFormsDPEquiv_symm_tmul (q : SimplexCategory)
    (x : (levelSectionsModuleTop hp F e q : Type u)) (y : levelDPForms hp i e q) :
    (levelTensorFormsDPEquiv hp F i e q).symm (x ⊗ₜ y) =
      (x ⊗ₜ (affineCrysDifferentialFormsIso S (wholeSpaceLevelObj hp e q).obj (V := ⊤) le_rfl
        (isAffineOpen_top S.S.scheme) i).symm y : levelFormsTensor hp F i e q) :=
  TensorProduct.congr_symm_tmul _ _ x y

/-- **The left vertical `Φ` of the naturality square**, the restriction map of the presheaf tensor
product conjugated by the first identification.  It is built rather than assumed, which is what
`Crystalline.tensorFormsLevelComposite_naturality` asks for: that statement takes the vertical as
an arbitrary additive map and uses only its value on a pure tensor. -/
def levelFormsDPVertical : levelFormsTensorDP hp F i e n →+ levelFormsTensorDP hp F i e m :=
  (levelTensorFormsDPEquiv hp F i e m).toAddEquiv.toAddMonoidHom.comp
    ((levelFormsTensorRestriction hp F i e φ).comp
      (levelTensorFormsDPEquiv hp F i e n).symm.toAddEquiv.toAddMonoidHom)

/-- **[Stacks, Tag 07J0] at the level objects, conjugated**: restricting a divided power
differential form pulled back through the identification and identifying again is the transition
map `...SmallSite.levelDPFormsMap` on divided power differential forms.

This is `...affineCrysDifferentialFormsIso_naturality_dp` at the transition morphism of the
system, followed by `LinearEquiv.apply_symm_apply`. -/
theorem levelFormsRestriction_dp (z : levelDPForms hp i e n) :
    affineCrysDifferentialFormsIso S (wholeSpaceLevelObj hp e m).obj (V := ⊤) le_rfl
        (isAffineOpen_top S.S.scheme) i
        (levelFormsRestriction hp i e φ
          ((affineCrysDifferentialFormsIso S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl
            (isAffineOpen_top S.S.scheme) i).symm z)) =
      levelDPFormsMap hp i e φ z :=
  (affineCrysDifferentialFormsIso_naturality_dp S (levelTransition hp e φ).hom
      (isAffineOpen_top S.S.scheme) i _).trans
    (congrArg (fun w ↦ levelDPFormsMap hp i e φ w) (LinearEquiv.apply_symm_apply _ z))

/-- **The hypothesis `hPhi` of `Crystalline.tensorFormsLevelComposite_naturality` at the level
objects of `...SmallSite.wholeSpaceSystem`.**

The left vertical `...SmallSite.levelFormsDPVertical` carries a pure tensor `x ⊗ ω` of a section
of `F` over the level `(n, e)` with a divided power differential form there to the restriction of
`x` tensored with `...SmallSite.levelDPFormsMap` of `ω`.  Pure tensors span, so this determines
the vertical.

The proof chains `levelTensorFormsDPEquiv_symm_tmul`, `levelFormsTensorRestriction_tmul`,
`levelTensorFormsDPEquiv_tmul` and `levelFormsRestriction_dp`, each as its own `congrArg`.
**No tag attribute is placed.** -/
theorem levelFormsDPVertical_tmul (x : (levelSectionsModuleTop hp F e n : Type u))
    (y : levelDPForms hp i e n) :
    levelFormsDPVertical hp F i e φ (x ⊗ₜ y) =
      levelSectionsRestriction hp F e φ x ⊗ₜ levelDPFormsMap hp i e φ y :=
  ((congrArg (fun w ↦ levelTensorFormsDPEquiv hp F i e m
          (levelFormsTensorRestriction hp F i e φ w))
        (levelTensorFormsDPEquiv_symm_tmul hp F i e n x y)).trans
      ((congrArg (fun w ↦ levelTensorFormsDPEquiv hp F i e m w)
          (levelFormsTensorRestriction_tmul hp F i e φ x _)).trans
        (levelTensorFormsDPEquiv_tmul hp F i e m (levelSectionsRestriction hp F e φ x) _))).trans
    (congrArg (fun w : levelDPForms hp i e m ↦ levelSectionsRestriction hp F e φ x ⊗ₜ w)
      (levelFormsRestriction_dp hp i e φ y))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
