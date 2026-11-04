module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentialForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeDifferentialsLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsComposite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRingAlgEquiv
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsLevelScalars
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsSheafifyIso

/-!
# The degreewise identification `M(n)_e = L_n ⊗_{D(n)} Ω^i_{D(n)}`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, let `F` be a sheaf
of `𝒪_{X/S}`-modules, let `i` be a degree and let `e` be a `p`-adic level.  The isomorphism `ε`
that the hypothesis `hiso` of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks
for is, in cosimplicial degree `n`, an isomorphism

`(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})(T(n)_e)  ≅  L_n ⊗_{D(n)} ⋀^i_{D(n)} Ω_{D(n)}`,

where `L_*` is `...SmallSite.levelSectionsCosimplicialModule`.  **This file constructs that
isomorphism**, as an additive isomorphism of the underlying groups.

Three identifications are made, and the first of them is an equality.

* The **section identification** `levelTensorFormsTop_eq`: the sections of the presheaf tensor
  product over the level object are the honest tensor product of the sections of the two factors,
  over the section ring `Γ(T(n)_e, 𝒪)`.  This holds by `rfl`; what it costs is the renaming of
  the ring of scalars, which is what `levelSectionsModuleTop` and `levelTensorFormsTop` are for
  (see the implementation notes).
* `levelTensorFormsDPEquiv`: the second factor is the module `Ω^i_{Γ(T(n)_e,𝒪)/Γ(S,⊤),δ(n)}` of
  divided power differential forms.  This is `...affineCrysDifferentialFormsIso` —
  [Stacks, Tag 07J0] in every degree — tensored with the identity, the level objects being affine
  by `...SmallSite.isAffine_wholeSpaceSystem_target` and lying over `V = ⊤` on the base.
* `levelTensorFormsCrossingEquiv`: the three comparisons of the source's own proof, which
  `Crystalline.tensorFormsLevelComposite` composes over abstract rings, instantiated here.

## Main definitions

* `...SmallSite.levelTensorFormsEquiv` — **the degreewise isomorphism**, as an `≃+` from the
  sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level `(n, e)` to the degree `n` of
  `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`.
* `...SmallSite.levelSectionsModuleTop`, `...SmallSite.levelTensorFormsTop` — the sections of `F`
  and of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level object, with the ring of scalars written
  `Γ(T(n)_e, 𝒪)`.
* `...SmallSite.wholeSpaceLevelEnvelope` — the **uncompleted** divided power envelope `E(n)` whose
  `p`-adic completion is `D(n)`, with its `Γ(S, ⊤)`-algebra structure
  `...SmallSite.wholeSpaceLevelEnvelopeAlgebra` and the comparison
  `...SmallSite.wholeSpaceLevelComparison` of [Stacks, Tag 07KK] at it.

## Main results

* `...SmallSite.levelTensorFormsTop_eq` — the section identification, by `rfl`.
* `...SmallSite.levelTensorFormsEquiv_apply` — the degreewise isomorphism as its two steps
  applied in turn, which is the form its cosimplicial naturality is to be checked in.

## Implementation notes

**Every obstruction here is a renaming of a ring, and each one is paid for by a definition rather
than inside unification** — the practice the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineObjectDifferentialForms.lean` record for this
area, and the reason `Crystalline.tensorFormsLevelComposite` is stated over abstract rings at all.
Three spellings of the section ring of the level object occur: `Γ(T(n)_e, 𝒪)`, the value
`(structureSheaf S).val.obj` of the structure sheaf, and the value of
`structurePresheaf S ⋙ forget₂ CommRingCat RingCat` which the monoidal structure on presheaves of
modules takes its tensor products over.  They are the same type, and a `Module` or `Algebra`
instance declared at one of them is invisible at the others.  `levelSectionsModuleTop` and
`levelTensorFormsTop` are the renamings onto `Γ(T(n)_e, 𝒪)`, where
`...affineCrysDifferentialFormsIso` lives; their bodies are the terms themselves.

**`Crystalline.tensorFormsLevelComposite` is applied with all of its instance arguments given
explicitly.**  Left to synthesis, none of the five module and scalar-tower instances on the
sections is found: they are declared in `SmallSite/LevelSectionsCosimplicialModule.lean` and
`SmallSite/LevelSectionsLevelScalars.lean` at the `(wholeSpaceEnvelopeRing hp).obj n` spelling of
`D(n)`, and the composite asks for them at `AdicCompletion (p) E(n)`.  Supplying them positionally
asks for a definitional check instead of a search, and that check is immediate.

**The level of the third comparison is `cutoff + (N + e)` and no reindexing is performed.**  The
cutoff of `...SmallSite.wholeSpaceLevelComparison` is a `Classical.choose` and is not comparable
to `Crystalline.uniformLevel`; none of that matters, because the source and target of
`Crystalline.tensorFormsCompletionLevelEquivAt` do not depend on its level — only its ring of
scalars and the instance `[Module (D(n) ⧸ (p)^k) M]` do, and that instance is
`...SmallSite.levelSectionsModuleAtAdd` at `c = cutoff`.  The defining equation is `rfl`.

The exponent is `N + e` and not `e`: the levels of `...SmallSite.wholeSpaceSystem` are
`D(n)/(p)^{N + e}` for the uniform cutoff `N` of `Crystalline.uniformLevel`.

## What is and is not proved

**No tag attribute is placed in this file, and [Stacks, Tag 07LF] is not proved.**  What is
constructed is the degreewise half of the isomorphism `ε` that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for.  **Its cosimplicial
naturality is not proved here**, and no isomorphism of cosimplicial objects is constructed: the
isomorphism built here is one degree at a time, with `n` fixed.  The sheafification half is
`...SmallSite.levelCosimplicialSectionsSheafifyIso` and is not composed in here either.

The sheaf `F` is arbitrary: neither hypothesis (1) nor hypothesis (2) of [Stacks, Tag 07JN] is
used or assumed, and no flatness or finiteness hypothesis appears.  The hypotheses carried are
`hp : IsNilpotent (S.p : Γ(S.X, ⊤))` and the two affineness instances `[IsAffine S.X]` and
`[IsAffine S.S.scheme]`, which `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` already carries.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]
variable (F : SheafOfModules.{u} (structureSheaf S)) (i e : ℕ) (n : SimplexCategory)

/-! ### The level object and its sections -/

/-- **The level `(n, e)` of the cosimplicial system of [Stacks, Tag 07JN]**, named once. -/
abbrev wholeSpaceLevelObj : CrystallineThickening S := ((wholeSpaceSystem S hp).obj (op n)).obj e

/-- **The ambient scheme of the level `(n, e)` is affine**, as an instance, so that
`...affineCrysDifferentialFormsIso` applies at the level objects without the fact having to be
re-introduced at each use.  This is `...SmallSite.isAffine_wholeSpaceSystem_target`, whose
statement is indexed by `n : ℕ`; `⦋n.len⦌` and `n` are the same term by eta for structures. -/
instance isAffine_wholeSpaceLevelObj_target :
    IsAffine (wholeSpaceLevelObj hp e n).obj.thickening.target.scheme :=
  isAffine_wholeSpaceSystem_target hp n.len e

/-- `F` read as a presheaf of modules over the **commutative** structure presheaf, which is the
spelling the monoidal structure of `CategoryTheory.PresheafOfModules` takes its tensor products
over. -/
abbrev sheafValComm :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  F.val

/-- **The sections of `F` over the level `(n, e)`, with the ring of scalars written
`Γ(T(n)_e, 𝒪)`.**  The body is the term itself; see the implementation notes for why the renaming
has to be named. -/
def levelSectionsModuleTop :
    ModuleCat.{u} Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) :=
  (sheafValComm F).obj (op (wholeSpaceLevelObj hp e n))

/-- **The sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level `(n, e)`, with the ring of scalars
written `Γ(T(n)_e, 𝒪)`.** -/
def levelTensorFormsTop :
    ModuleCat.{u} Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) :=
  (tensorDifferentialForms (sheafValComm F) i).obj (op (wholeSpaceLevelObj hp e n))

/-- **The section identification.**  The sections of the presheaf tensor product
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level `(n, e)` are the tensor product, over the section ring
`Γ(T(n)_e, 𝒪)`, of the sections of `F` with the sections of `Ω^i_{X/S}` there.

This is `...SmallSite.tensorDifferentialForms_obj` together with
`...affineCrysDifferentialFormsIso`'s reading of the small-site forms as the big-site ones,
`...smallSite_crysDifferentialForms_obj`; both are `rfl`, and so is this. -/
theorem levelTensorFormsTop_eq :
    (levelTensorFormsTop hp F i e n : Type u) =
      TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
        (levelSectionsModuleTop hp F e n : Type u)
        ((Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
          (op (wholeSpaceLevelObj hp e n).obj) : Type u) :=
  rfl

/-! ### The uncompleted envelope and its comparison -/

/-- **The uncompleted divided power envelope `E(n)`** of the kernel of
`P ⊗_A ⋯ ⊗_A P → Γ(X, ⊤)`, whose `p`-adic completion is the degree `n` of
`...SmallSite.wholeSpaceEnvelopeRing`.  It is the ring the comparison of [Stacks, Tag 07KK] and
the cosimplicial module `Ω_{D(*)}` of [Stacks, Tag 07L1] are built from. -/
abbrev wholeSpaceLevelEnvelope (m : ℕ) :=
  (_root_.Crystalline.tensorPowerEnvelope (affineSituation S hp)
    (_root_.Crystalline.canonicalPresentation (affineSituation S hp)) m).object

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **`p` is nilpotent modulo the divided power ideal of `E(n)`**, so that the completed divided
powers of [Stacks, Tag 07KD] and the comparison of [Stacks, Tag 07KK] exist there.  This is
`Crystalline.polynomialDividedPowerEnvelope_prime_nilpotent`. -/
theorem wholeSpaceLevelEnvelope_prime_nilpotent (m : ℕ) :
    IsNilpotent (Ideal.Quotient.mk (wholeSpaceLevelEnvelope hp m).ideal
      ((affineSituation S hp).p : (wholeSpaceLevelEnvelope hp m))) :=
  _root_.Crystalline.polynomialDividedPowerEnvelope_prime_nilpotent (affineSituation S hp)
    (_root_.Crystalline.tensorPowerPresentation (affineSituation S hp)
      (_root_.Crystalline.canonicalPresentation (affineSituation S hp)) m)

/-- **`E(n)` as a `Γ(S, ⊤)`-algebra**, through its own structure map.  This is the instance the
comparison `...SmallSite.wholeSpaceLevelComparison` carries in its type, and it is supplied here
rather than declared globally for the reason
`...SmallSite.wholeSpaceEnvelopeFromBase` records. -/
abbrev wholeSpaceLevelEnvelopeAlgebra (m : ℕ) :
    Algebra (Γ(S.S.scheme, ⊤) : Type u) (wholeSpaceLevelEnvelope hp m) :=
  (_root_.Crystalline.tensorPowerEnvelope (affineSituation S hp)
    (_root_.Crystalline.canonicalPresentation (affineSituation S hp))
    m).structureMap.toRingHom.toAlgebra

/-- **[Stacks, Tag 07KK] at `E(n)`**: the comparison of the three inverse limits of divided power
differentials, whose cutoff fixes the levels at which the two shapes of `Ω_{D(n)}` agree.  This is
`Crystalline.tensorPowerEnvelopeCompletionComparison`. -/
abbrev wholeSpaceLevelComparison (m : ℕ) :=
  _root_.Crystalline.tensorPowerEnvelopeCompletionComparison (affineSituation S hp)
    (_root_.Crystalline.canonicalPresentation (affineSituation S hp)) m

/-! ### The degreewise isomorphism -/

/-- **The sections of `Ω^i_{X/S}` over the level `(n, e)` are the divided power differential
forms `Ω^i_{Γ(T(n)_e,𝒪)/Γ(S,⊤),δ(n)}`**, after tensoring with the sections of `F`.

This is `...affineCrysDifferentialFormsIso` — [Stacks, Tag 07J0] in every degree — tensored with
the identity on the sections of `F`, both exterior powers being over the one ring
`Γ(T(n)_e, 𝒪)`.  Its two non-affineness hypotheses are discharged once for all the level objects,
as in `...SmallSite.levelCosimplicialSectionsSheafifyIso`: `V = ⊤` on the *base* scheme, affine by
`AlgebraicGeometry.isAffineOpen_top`, and `h = le_rfl` because `Scheme.Hom.preimage_top` is `rfl`;
the affineness of the ambient scheme is `...SmallSite.isAffine_wholeSpaceSystem_target`. -/
def levelTensorFormsDPEquiv :
    TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
        (levelSectionsModuleTop hp F e n : Type u)
        ((Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
          (op (wholeSpaceLevelObj hp e n).obj) : Type u) ≃ₗ[
        Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)]
      TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
        (levelSectionsModuleTop hp F e n : Type u)
        (@dividedPowerDifferentialForms (Γ(S.S.scheme, ⊤) : Type u)
          (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u) _ _
          (affineBaseAppLE S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl).hom.toAlgebra _
          (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj) i) :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    (affineCrysDifferentialFormsIso S (wholeSpaceLevelObj hp e n).obj le_rfl
      (isAffineOpen_top S.S.scheme) i)

/-- **The three comparisons of the source's proof of [Stacks, Tag 07LF], at the level `(n, e)`.**

`M(n)_e ⊗_{Γ(T(n)_e,𝒪)} Ω^i_{Γ(T(n)_e,𝒪)/Γ(S,⊤),δ(n)}  ≃+  L_n ⊗_{D(n)} ⋀^i_{D(n)} Ω_{D(n)}`

This is `Crystalline.tensorFormsLevelComposite` instantiated: the ring identification is
`...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv` with its divided power halves
`...SmallSite.isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv` and `..._symm`, whose
`Crystalline.ideal_map_of_isDPMorphism_symm` supplies the hypothesis that the divided power ideal
is carried *onto* the divided power ideal; the two finite levels are `N + e` and
`cutoff + (N + e)`; and the five module and scalar-tower instances on `M(n)_e` are the ones
`SmallSite/LevelSectionsCosimplicialModule.lean` and
`SmallSite/LevelSectionsLevelScalars.lean` declare.  **No tag attribute is placed.** -/
def levelTensorFormsCrossingEquiv :
    TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
        (levelSectionsModuleTop hp F e n : Type u)
        (@dividedPowerDifferentialForms (Γ(S.S.scheme, ⊤) : Type u)
          (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u) _ _
          (affineBaseAppLE S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl).hom.toAlgebra _
          (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj) i) ≃+
      TensorProduct ((wholeSpaceEnvelopeRing hp).obj n : Type u)
        (F.val.obj (op (wholeSpaceLevelObj hp e n)) : Type u)
        ↥(⋀[((wholeSpaceEnvelopeRing hp).obj n : Type u)]^i
          ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) :=
  @tensorFormsLevelComposite (Γ(S.S.scheme, ⊤) : Type u) (wholeSpaceLevelEnvelope hp n.len)
    (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u) _ _ _
    (wholeSpaceLevelEnvelopeAlgebra hp n.len)
    (affineBaseAppLE S (wholeSpaceLevelObj hp e n).obj (V := ⊤) le_rfl).hom.toAlgebra
    (wholeSpaceLevelEnvelope hp n.len).ideal (wholeSpaceLevelEnvelope hp n.len).dividedPowers
    (affineSituation S hp).p (wholeSpaceLevelEnvelope_prime_nilpotent hp n.len)
    (wholeSpaceLevelComparison hp n.len)
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
    (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).1
    (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n.len e).2
    _ (crysDividedPowers S (wholeSpaceLevelObj hp e n).obj)
    (wholeSpaceEnvelopeRingLevelAlgEquiv hp n.len e)
    (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
    (ideal_map_of_isDPMorphism_symm
      (B := (Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤) : Type u))
      _ _ (wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
      (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n.len e)
      (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp n.len e))
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) _ rfl
    (levelSectionsModuleTop hp F e n : Type u) _ _
    (levelSectionsModule hp F n e) (levelSectionsModuleAtLevel hp F n e)
    (levelSectionsIsScalarTowerAtLevel hp F n e)
    (levelSectionsModuleAtAdd hp F n e (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
    (levelSectionsIsScalarTowerAtAdd hp F n e
      (wholeSpaceLevelComparison hp n.len).quotientSystem.cutoff)
    (levelSections_smul_eq hp F n e) i

/-- **The degreewise identification `M(n)_e = L_n ⊗_{D(n)} Ω^i_{D(n)}`.**

For a sheaf of `𝒪_{X/S}`-modules `F`, a degree `i` and a `p`-adic level `e`, the sections of the
presheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level `(n, e)` of the system of [Stacks, Tag 07JN]
are the degree `n` of `L_* ⊗_{D(*)} ⋀^i Ω_{D(*)}`, for `L_*` the cosimplicial `D(*)`-module
`...SmallSite.levelSectionsCosimplicialModule` of the sections of `F`.

It is `levelTensorFormsDPEquiv` followed by `levelTensorFormsCrossingEquiv`, its source being the
right-hand side of the section identification `levelTensorFormsTop_eq`, which is where the
sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over the level object are to be read.  Additive and not
linear: the crossing of the ring identification is semilinear, source and target being modules
over two different rings.

This is the degreewise half of the isomorphism `ε` that the hypothesis `hiso` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` asks for.  **Its cosimplicial
naturality is not proved here and no isomorphism of cosimplicial objects is constructed; no tag
attribute is placed.** -/
def levelTensorFormsEquiv :
    TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
        (levelSectionsModuleTop hp F e n : Type u)
        ((Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
          (op (wholeSpaceLevelObj hp e n).obj) : Type u) ≃+
      TensorProduct ((wholeSpaceEnvelopeRing hp).obj n : Type u)
        (F.val.obj (op (wholeSpaceLevelObj hp e n)) : Type u)
        ↥(⋀[((wholeSpaceEnvelopeRing hp).obj n : Type u)]^i
          ((wholeSpaceEnvelopeDifferentials hp).obj (op (op n)) : Type u)) :=
  (levelTensorFormsDPEquiv hp F i e n).toAddEquiv.trans
    (levelTensorFormsCrossingEquiv hp F i e n)

/-- **The degreewise identification is the two steps applied in turn.**  This is the form in which
its cosimplicial naturality is to be checked: `Crystalline.tensorFormsLevelComposite_tmul`
computes the second step on a pure tensor, and `Stacks.exteriorPowerCongr_ιMulti` through
`...affineCrysDifferentialFormsIso_ιMulti` computes the first.  **Neither the value of the
composite on a pure tensor nor the naturality is stated here**: the value is a single equation
whose two sides each mention the whole crossing, and checking it is an `isDefEq` problem that does
not terminate inside the heartbeat budget.  The two factors, computed separately, are what a
naturality proof should be built from. -/
theorem levelTensorFormsEquiv_apply
    (z : TensorProduct Γ((wholeSpaceLevelObj hp e n).obj.thickening.target.scheme, ⊤)
      (levelSectionsModuleTop hp F e n : Type u)
      ((Crystalline.GlobalCrystallineSituation.crysDifferentialForms S i).obj
        (op (wholeSpaceLevelObj hp e n).obj) : Type u)) :
    levelTensorFormsEquiv hp F i e n z =
      levelTensorFormsCrossingEquiv hp F i e n (levelTensorFormsDPEquiv hp F i e n z) :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
