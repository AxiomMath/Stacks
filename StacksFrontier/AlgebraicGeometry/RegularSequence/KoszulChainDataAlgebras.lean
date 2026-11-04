module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSectionwiseDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSheafifiedDifferential
public import StacksFrontier.AlgebraicGeometry.RegularSequence.StalkTests

/-!
# The Koszul differential of a sequence of global sections, at the constructed algebra bundle

Let `O♯` be a sheaf of commutative rings on a topological space `X`, let `F = (O♯)ʳ` be the finite
free sheaf of `O♯`-modules on `r` generators and let `φ : F ⟶ O♯` be a morphism of sheaves of
modules. `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulSheafDifferential.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkComplexIso.lean` compute the stalks of the Koszul complex of `φ` from a hypothesis,
`Stacks.RegularSequence.KoszulChainData`: the degree-lowering morphisms of the exterior algebra,
the graded Leibniz rule, the value on a degree-one generator, and the associated `ℤ`-indexed chain
complex.

**This file constructs that term**, for the algebra bundle that is actually constructed,
`Stacks.RegularSequence.koszulAlgebras = SheafOfModules.algebras`. The construction is the
sheafification of the sectionwise one: the exterior algebra of `koszulAlgebras` is, on the nose,
the sheafification of the `ℤ`-extended graded algebra of sectionwise exterior powers
`PresheafOfModules.extPow n (O♯ʳ)`, whose sections are honest exterior powers
`⋀ⁿ_{O(U)}((O♯ʳ)(U))`; over a presheaf the Koszul differential *is* `Koszul.contraction` and each
of the three identities *is* a statement about `CliffordAlgebra.contractLeft`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulSectionwiseDifferential.lean`), and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulSheafifiedDifferential.lean` carries each of
them across the sheafification.

Consequently the stalk comparison of Stacks Tag 063C holds of a named term and not of a
hypothesis: `Stacks.RegularSequence.exists_stalkChainIso_koszulAlgebras`.

## Main definitions

* `Stacks.RegularSequence.koszulDual`: the sectionwise functional of `φ`, i.e. `φ` read on the
  underlying presheaves of modules.
* `Stacks.RegularSequence.koszulChainData`: **the Koszul chain data of `φ` at the constructed
  algebra bundle.**

## Main results

* `Stacks.RegularSequence.koszulD_exteriorGenerator`: the differential sends a degree-one
  generator to its scalar times the exterior unit. This is the one field that is not formal: both
  sides are morphisms out of a sheafification, they agree on the unit-images of local sections,
  and the right triangle identity of the sheafification adjunction is what identifies the
  generator of the constructed bundle with the sectionwise one there.
* `Stacks.RegularSequence.exists_stalkChainIso_koszulAlgebras`: **the stalk comparison for the
  Koszul complex of a sequence of global sections, with no hypothesis.** The stalk at `x` of the
  Koszul complex of sheaves is the ring-level Koszul complex of the germs of the sequence,
  characterized by its value on the germ of a scalar times an ordered exterior product of
  tautological generators.

## Implementation notes

What is forced and what is chosen.

* **Every definitional identification used here is `rfl`, and that is the point.**
  `koszulAlgebras` is `SheafOfModules.algebras`, which is `sheafifiedAlgebras`, which is
  `TensorExteriorSymmetricAlgebras.ofIso` of the inhabitant of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant`; `ofIso` leaves the
  `exterior` field untouched and only composes the generator with the transporting isomorphism.
  So the exterior algebra of `koszulAlgebras` *is*
  `(PresheafOfModules.extPowGradedAlgebra (O♯ʳ).val).extend.sheafify`, and the `d`, `d_mul`,
  `chain`, `chain_X` and `chain_d` fields are the corresponding declarations of
  `KoszulSheafifiedDifferential` with no transport at all. The generator, by contrast, *is*
  composed with `SheafOfModules.sheafifyValIso`, which is why `d_generator` is the one field with
  a proof.
* **`d_generator` is proved as an equality of morphisms, not of sections.** A local section of
  `(O♯ʳ)` is only locally a unit-image, so the identity cannot be checked on unit-images
  directly; what can be is the equality of the two morphisms `O♯ʳ ⟶ ⋀⁰(O♯ʳ)` that the two sides
  are the applications of, after precomposition with `sheafifyValIso`, by
  `PresheafOfModules.sheafification_hom_ext_apply`. Precomposing is also what turns
  `koszulAlgebras.exteriorGenerator` back into the sectionwise generator, by
  `Iso.hom_inv_id_assoc`.
* **The proof is a term-mode `Eq.trans` chain, not a `rw` sequence.** `(P n).obj X`,
  `((toPresheaf R₀).obj (P n)).obj X` and `(extPow n F).obj X` versus
  `(extPowFamily F (n : ℤ)).obj X` are the same types with instances that are not syntactically
  equal, and a rewrite inside a goal mixing them is refused as not type-correct at `implicit`
  transparency. `Eq.trans` and `congrArg` are checked at full transparency. This is the
  obstruction recorded in `KoszulStalkComplexIso` and in `KoszulSheafifiedDifferential`.
* The single universe `u` carrying the space, the sections of `O♯` and the sections of every
  module is forced by `TopCat.Presheaf.stalk`, exactly as in `KoszulStalk`. The universes of
  `KoszulChainData` are written out for the elaboration-order reason recorded in
  `KoszulSheafDifferential`.
* No `@[stacks]` attribute. Stacks Tag 062K asserts the existence *and uniqueness* of the Koszul
  differential and presents it as a differential graded algebra; this file constructs six of the
  fields of that package and proves neither uniqueness, nor graded commutativity, nor the
  differential-graded-algebra presentation, so it is not a covering set for the tag. Tag 063C is a
  statement about regularity of a sequence, which this file does not state either.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open PresheafOfModules

universe u

namespace Stacks.RegularSequence

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}} {r : ℕ}

/-! ### The sectionwise data -/

/-- The presheaf of modules underlying the finite free sheaf `(O♯)ʳ`, over the presheaf of rings
`O♯` rather than over the sheaf of rings. Its sheafification is `(O♯)ʳ` itself, and the graded
algebra of its sectionwise exterior powers is the one whose sheafification is the exterior algebra
of `Stacks.RegularSequence.koszulAlgebras`. -/
noncomputable abbrev koszulValPresheaf (Osharp : Sheaf (Opens.grothendieckTopology ↥X)
    CommRingCat.{u}) (r : ℕ) :
    PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (koszulFreeSheaf Osharp r)

/-- The locally bijective map of presheaves of rings along which the sectionwise exterior algebra
is sheafified: the identity of `O♯`, read in `RingCat`. -/
noncomputable abbrev koszulAlpha :
    (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj :=
  toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)

/-- The `ℤ`-graded algebra of sectionwise exterior powers of `(O♯)ʳ`. Its sheafification is the
exterior algebra of `Stacks.RegularSequence.koszulAlgebras`, on the nose. -/
noncomputable abbrev koszulPreAlgebra :
    Stacks.GradedAlgebra (PresheafOfModules.SectionwiseDual.extPowFamily
      (koszulValPresheaf Osharp r)) :=
  (PresheafOfModules.extPowGradedAlgebra (koszulValPresheaf Osharp r)).extend

/-- The exterior algebra of the constructed bundle is the sheafification of the sectionwise
one. -/
theorem koszulAlgebras_exterior :
    (koszulAlgebras Osharp r).exterior =
      (koszulPreAlgebra (Osharp := Osharp) (r := r)).sheafify
        (koszulAlpha (Osharp := Osharp)) := rfl

/-- The functional of `φ` over an object of the site, retyped at the sections of the underlying
presheaf of modules. -/
noncomputable def koszulDualApp
    (φ : koszulFreeSheaf Osharp r ⟶
      SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (U : (Opens ↥X)ᵒᵖ) :
    Module.Dual ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      ((koszulValPresheaf Osharp r).obj U) :=
  ConcreteCategory.hom (φ.val.app U)

/-- **The sectionwise functional of `φ`**: the morphism `φ` read on the underlying presheaves of
modules. Its compatibility with restriction is the naturality of `φ`. -/
noncomputable def koszulDual
    (φ : koszulFreeSheaf Osharp r ⟶
      SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    PresheafOfModules.SectionwiseDual.{u, u, u, u} (koszulValPresheaf Osharp r) where
  app U := koszulDualApp φ U
  naturality f m := (PresheafOfModules.naturality_apply φ.val f m).symm

variable (φ : koszulFreeSheaf Osharp r ⟶
  SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- **The Koszul differential of `φ` on the exterior algebra of the constructed bundle**: the
sheafification of the sectionwise Koszul differential of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSectionwiseDifferential`. -/
noncomputable def koszulD (n : ℤ) :
    (koszulAlgebras Osharp r).exterior.piece n ⟶
      (koszulAlgebras Osharp r).exterior.piece (n - 1) :=
  (koszulPreAlgebra (Osharp := Osharp) (r := r)).sheafifyD
    (koszulAlpha (Osharp := Osharp)) (koszulDual φ).extKoszulD n

/-! ### The value on a degree-one generator -/

/-- **The Koszul differential of a degree-one generator is its scalar times the exterior unit.**

Both sides are the applications of two morphisms `(O♯)ʳ ⟶ ⋀⁰((O♯)ʳ)`; a local section of
`(O♯)ʳ` is only *locally* the unit-image of a local section of the underlying presheaf, so the
identity is proved as an equality of those morphisms, after precomposition with
`SheafOfModules.sheafifyValIso`, by `PresheafOfModules.sheafification_hom_ext_apply`. The
precomposition is also what turns the generator of the constructed bundle back into the
sectionwise generator, and the right triangle identity of the sheafification adjunction is what
identifies a unit-image with the section it lifts. -/
theorem koszulD_exteriorGenerator (U : (Opens ↥X)ᵒᵖ)
    (e : (koszulFreeSheaf Osharp r).val.obj U) :
    (koszulD φ 1).val.app U ((koszulAlgebras Osharp r).exteriorGenerator.val.app U e) =
      unitScalar φ U e • (koszulAlgebras Osharp r).exterior.one.eval U := by
  have hone : ∀ (V : (Opens ↥X)ᵒᵖ)
      (y : (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj V),
      y • (koszulAlgebras Osharp r).exterior.one.eval V =
        (koszulAlgebras Osharp r).exteriorPieceZeroIsoUnit.inv.val.app V y := fun V y =>
    (koszulAlgebras Osharp r).exteriorPieceZeroIsoUnit_smul_one V _ _
      (iso_hom_val_app_inv_val_app (koszulAlgebras Osharp r).exteriorPieceZeroIsoUnit V y)
  have htri : ∀ (V : (Opens ↥X)ᵒᵖ) (m : (koszulValPresheaf Osharp r).obj V),
      (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X)
          (koszulFreeSheaf Osharp r)).hom.val.app V
        (Hom.app (sheafifyUnit (koszulAlpha (Osharp := Osharp))
          (koszulValPresheaf Osharp r)) V m) = m := fun V m =>
    congrArg (fun k => Hom.app k V m)
      ((PresheafOfModules.sheafificationAdjunction
        (koszulAlpha (Osharp := Osharp))).right_triangle_components (koszulFreeSheaf Osharp r))
  have hgen : ((SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X)
          (koszulFreeSheaf Osharp r)).hom ≫
        (koszulAlgebras Osharp r).exteriorGenerator) =
      SheafOfModules.sectionwiseExteriorAlgebraGen (Opens.grothendieckTopology ↥X)
        (𝟙 Osharp.obj) (koszulValPresheaf Osharp r) :=
    Iso.hom_inv_id_assoc _ _
  have hmor :
      (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X)
          (koszulFreeSheaf Osharp r)).hom ≫
        ((koszulAlgebras Osharp r).exteriorGenerator ≫ koszulD φ 1) =
      (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X)
          (koszulFreeSheaf Osharp r)).hom ≫
        (φ ≫ (koszulAlgebras Osharp r).exteriorPieceZeroIsoUnit.inv) := by
    rw [← Category.assoc, ← Category.assoc]
    refine PresheafOfModules.sheafification_hom_ext_apply
      (koszulAlpha (Osharp := Osharp)) ?_
    intro V m
    have e1 := Stacks.GradedAlgebra.sheafifyGen_unit (koszulAlpha (Osharp := Osharp))
      (koszulPreAlgebra (Osharp := Osharp) (r := r))
      (PresheafOfModules.extPowGen (koszulValPresheaf Osharp r)) V m
    have hL : (((SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X)
              (koszulFreeSheaf Osharp r)).hom ≫
            (koszulAlgebras Osharp r).exteriorGenerator) ≫ koszulD φ 1).val.app V
          (Hom.app (sheafifyUnit (koszulAlpha (Osharp := Osharp))
            (koszulValPresheaf Osharp r)) V m) =
        (koszulDual φ).app V m • (koszulAlgebras Osharp r).exterior.one.eval V := by
      rw [hgen]
      exact ((congrArg (fun z => (koszulD φ 1).val.app V z) e1).trans
          ((Stacks.GradedAlgebra.sheafifyD_unit (koszulAlpha (Osharp := Osharp))
              (koszulPreAlgebra (Osharp := Osharp) (r := r)) (koszulDual φ).extKoszulD 1 V
              (Hom.app (PresheafOfModules.extPowGen (koszulValPresheaf Osharp r)) V m)).trans
            ((congrArg (fun z => Hom.app (sheafifyUnit (koszulAlpha (Osharp := Osharp))
                  (PresheafOfModules.SectionwiseDual.extPowFamily
                    (koszulValPresheaf Osharp r) (1 - 1))) V z)
                ((koszulDual φ).extKoszulD_extPowGen V m)).trans
              (map_smul _ _ _))))
    have hb : (koszulDual φ).app V m = ConcreteCategory.hom (φ.val.app V) m := rfl
    rw [hb] at hL
    refine (hL.trans (hone V _)).trans ?_
    exact (congrArg (fun y =>
      (koszulAlgebras Osharp r).exteriorPieceZeroIsoUnit.inv.val.app V (φ.val.app V y))
        (htri V m)).symm
  have hc := SheafOfModules.hom_congr_app_apply ((cancel_epi _).1 hmor) U e
  exact hc.trans (hone U _).symm

/-- `Stacks.RegularSequence.koszulD_exteriorGenerator` in the shape Stacks Tag 062K states it:
through the degree-zero identification of the tensor algebra and the exterior quotient map. The
two forms differ by `TensorExteriorSymmetricAlgebras.tensorPieceZeroIsoUnit_smul_one` and the
unitality of `tensorToExterior`, exactly as in
`Stacks.RegularSequence.KoszulChainData.d_exteriorGenerator`. -/
theorem koszulD_generator (U : (Opens ↥X)ᵒᵖ) (e : (koszulFreeSheaf Osharp r).val.obj U) :
    (koszulD φ 1).val.app U ((koszulAlgebras Osharp r).exteriorGenerator.val.app U e) =
      ((koszulAlgebras Osharp r).tensorToExterior.app 0).val.app U
        (((koszulAlgebras Osharp r).tensorPieceIso 0).inv.val.app U (φ.val.app U e)) := by
  refine (koszulD_exteriorGenerator φ U e).trans ?_
  have hc : (koszulAlgebras Osharp r).tensorPieceZeroIsoUnit.hom.val.app U
      (((koszulAlgebras Osharp r).tensorPieceIso 0).inv.val.app U (φ.val.app U e)) =
      unitScalar φ U e :=
    iso_hom_val_app_inv_val_app ((koszulAlgebras Osharp r).tensorPieceIso 0) U (φ.val.app U e)
  rw [← (koszulAlgebras Osharp r).tensorPieceZeroIsoUnit_smul_one U _ _ hc, map_smul,
    (koszulAlgebras Osharp r).tensorToExterior.map_one U]

/-! ### The chain data -/

/-- **The Koszul chain data of `φ` at the constructed algebra bundle.** This is the term of
`Stacks.RegularSequence.KoszulChainData` that the stalk computations of Stacks Tag 063C take as a
hypothesis: the degree-lowering morphisms of the exterior algebra of
`Stacks.RegularSequence.koszulAlgebras`, the graded Leibniz rule, the value on a degree-one
generator, and the associated `ℤ`-indexed chain complex, whose degree-`n` term is the degree-`n`
exterior power on the nose. -/
noncomputable def koszulChainData : KoszulChainData.{u, u, u} (koszulAlgebras Osharp r) φ where
  d n := koszulD φ n
  d_mul n m U a b :=
    (koszulPreAlgebra (Osharp := Osharp) (r := r)).sheafifyD_mul
      (koszulAlpha (Osharp := Osharp)) (koszulDual φ).extKoszulD
      (fun n m Y x y => (koszulDual φ).extKoszulD_mul n m Y x y) n m U a b
  d_generator U e := koszulD_generator φ U e
  chain := (koszulPreAlgebra (Osharp := Osharp) (r := r)).sheafifyChain
    (koszulAlpha (Osharp := Osharp)) (koszulDual φ).extKoszulD
    fun n => (koszulDual φ).extKoszulD_comp n
  chain_X _ := rfl
  chain_d n := (koszulPreAlgebra (Osharp := Osharp) (r := r)).sheafifyChain_d
    (koszulAlpha (Osharp := Osharp)) (koszulDual φ).extKoszulD _ n

/-! ### The stalk comparison, unconditionally -/

/-- **The stalk comparison for the Koszul complex of a sequence of global sections.** The stalk at
`x` of the Koszul complex of sheaves of `φ`, built on the constructed exterior algebra of
`(O♯)ʳ`, is isomorphic as a `ℤ`-indexed complex of abelian groups to the zero-extension of the
ring-level Koszul complex `Koszul.seqComplex` of the germs of `f` at `x`, and the isomorphism is
characterized by its value on the germ of a scalar times an ordered exterior product of
tautological generators.

This is `Stacks.RegularSequence.KoszulChainData.exists_stalkChainIso_algebras` with its chain-data
hypothesis discharged by `Stacks.RegularSequence.koszulChainData`. -/
theorem exists_stalkChainIso_koszulAlgebras
    (f : Fin r → ↑(Osharp.obj.obj (op (⊤ : Opens ↥X))))
    (hφ : ∀ k : Fin r,
      ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
        (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k) (x : ↥X) :
    ∃ e : (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj
          (koszulChainData φ).chain) ≅
        ((koszulAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj
          (((Koszul.seqComplex fun k =>
                TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
                  (f k)).extend ComplexShape.embeddingDownNat).restriction
            ComplexShape.embeddingDownIntUpInt),
      ∀ (n : ℕ) (U : Opens ↥X) (hx : x ∈ U) (a : ↑(Osharp.obj.obj (op U)))
          (i : Fin n → Fin r),
        ((Koszul.seqComplex fun k =>
              TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
                (f k)).extendXIso ComplexShape.embeddingDownNat (i := n) rfl).hom
          ((e.hom.f (n : ℤ))
            ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
                ((koszulChainData φ).chain.X ((n : ℕ) : ℤ)).val.presheaf U x hx)
              (((eqToHom ((koszulChainData φ).chain_X ((n : ℕ) : ℤ)).symm).val.app (op U))
                (a • exteriorBasisSection (koszulAlgebras Osharp r) U n i)))) =
          TopCat.Presheaf.germ Osharp.obj U x hx a •
            (⟨ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
                fun j => Pi.single (i j) 1, Koszul.ιMulti_mem n _⟩ :
              ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n
                (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)))) :=
  KoszulChainData.exists_stalkChainIso_algebras (koszulChainData φ) f hφ x

end Stacks.RegularSequence

end
