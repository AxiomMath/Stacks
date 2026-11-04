module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSheafDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkIntegerSupport
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of the Koszul complex of a sequence of global sections

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `f₁, …, f_r` global
sections of `O♯` and `φ : (O♯)ʳ ⟶ O♯` a morphism of sheaves of modules whose value on the `k`-th
tautological generator is `f_k`. Stacks Tag 062K attaches to `φ` a Koszul complex of sheaves of
modules; `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulSheafDifferential.lean` takes that
complex as a hypothesis, `Stacks.RegularSequence.KoszulChainData`, and computes its stalks
degreewise. This file assembles those degreewise computations into **one isomorphism of
`ℤ`-indexed chain complexes of abelian groups**:

`(K.chain)_x ≅ K_•(f₁ₓ, …, f_rₓ)`,

where the left-hand side is the stalk functor of Stacks Tag 01AH applied degreewise to the
Koszul complex of sheaves and the right-hand side is the ring-level Koszul complex
`Koszul.seqComplex` of the sequence of germs, extended by zero to negative degrees and
re-indexed homologically. The isomorphism is pinned down by its value on the germ of a scalar
times an ordered exterior product of tautological generators.

This is the comparison the stalkwise regularity criterion of Stacks Tag 063C rests on: combined
with `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` (Tag 01AG) it turns
acyclicity of the sheaf Koszul complex into acyclicity of the ring-level Koszul complex of the
germs at every point.

## Main definitions

* `Stacks.RegularSequence.stalkAbFunctor`: the stalk functor of Tag 01AH followed by the
  forgetful functor to abelian groups.
* `Stacks.RegularSequence.exteriorKoszulStalkAbIso`: the degreewise comparison of Tag 01CH,
  read as an isomorphism of abelian groups.
* `Stacks.RegularSequence.KoszulChainData.stalkChainXIso`: the degreewise comparison between the
  stalk of the Koszul complex of sheaves and the ring-level Koszul complex of the germs.
* `Stacks.RegularSequence.KoszulChainData.stalkChainIso`: **the comparison of `ℤ`-indexed
  complexes**.

## Main results

* `Stacks.RegularSequence.KoszulChainData.chain_d_eq_dNat`: the differential of the chain complex
  of Tag 062K between consecutive nonnegative degrees, with the degree transports written out.
* `Stacks.RegularSequence.KoszulChainData.stalkChainXIso_comm`: the degreewise comparison
  commutes with the differentials. This is the hypothesis `isoNatToIntAb` asks for, and it is
  exactly the stalk-level differential compatibility of
  `Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin`.
* `Stacks.RegularSequence.KoszulChainData.isZero_stalkChain_X_of_neg`: the stalk complex vanishes
  in negative degrees.
* `Stacks.RegularSequence.KoszulChainData.stalkChainIso_germ_smul_exteriorBasisSection`: **the
  characterizing germ formula.** In degree `n` the comparison sends the germ of
  `a · e_{i₀} ∧ ⋯ ∧ e_{i_{n-1}}` to `a_x · (δ_{i₀} ∧ ⋯ ∧ δ_{i_{n-1}})`, with `a` replaced by its
  germ. This includes the unit in degree zero and the individual generators in degree one.
* `Stacks.RegularSequence.KoszulChainData.exists_stalkChainIso`: the two previous results
  packaged as one existential statement, with the target complex written in the
  `extend`-then-`restriction`-then-`forget₂` spelling and the wedge written as a subtype of the
  exterior algebra.

## Implementation notes

What is forced and what is chosen.

* **The Koszul complex of sheaves is a hypothesis, not a term.** Tag 062K asserts its existence
  and uniqueness and that existence theorem is not available here, so `KoszulChainData` is taken
  as data exactly as in `KoszulSheafDifferential`. Every statement below therefore holds of
  *any* Koszul differential whatsoever, which is strictly stronger than a statement about a
  chosen one.
* **Two scalar rings, and why the comparison is stated over abelian groups.**
  `AlgebraicGeometry.SheafOfModules.stalkFunctor` (which carries Tag 01AH) lands in modules over
  the stalk of the `RingCat`-valued presheaf `O♯ ⋙ forget₂ CommRingCat RingCat`, whereas the
  module structure Mathlib puts on the stalk of a presheaf of modules — hence
  `Stacks.SheafOfModules.exteriorKoszulStalkEquiv` and all of `FreeSheafStalkBasis` — is over the
  stalk of the `CommRingCat`-valued `O♯`. The two stalks are isomorphic and *not* equal, so no
  comparison of stalk *modules* is available without a scalar bridge. Composing with
  `forget₂ _ AddCommGrpCat` deletes the discrepancy: the underlying abelian group is the same
  object on the nose, and `Stacks.RegularSequence.stalkAddHom` is literally the underlying map of
  `stalkFunctor`'s action on morphisms. That is why the comparison is an isomorphism of
  `AddCommGrpCat`-valued complexes and not of `ModuleCat`-valued ones.
* **The two `PreservesZeroMorphisms` instances are a spelling workaround, not duplication.**
  `Functor.mapHomologicalComplex` needs `PreservesZeroMorphisms`, and the instance for
  `stalkFunctor O x` with `O` a variable is *not* found when `O` is the composite
  `toRingCat J O♯`: the discriminant-tree key of the goal is computed after the projection
  `(toRingCat J O♯).obj` has been reduced, so it no longer matches the key of an instance stated
  for a variable `O`. The respelled instance fixes that. This is the same family of obstruction
  that `StalkwiseExactness.lean` records for `TopCat.Sheaf` versus
  `Sheaf (Opens.grothendieckTopology X)`, and the fix is the same: pin the spelling the consumer
  writes. Both instances are `Prop`-valued, so having two is harmless.
* **No `rw` through the two spellings of a section.** `M.obj (op U)` and `M.presheaf.obj (op U)`
  are the same type with `AddCommMonoid` instances that are not syntactically equal, so a goal
  mixing them is not type-correct at `implicit` transparency and `kabstract` refuses with a
  pattern-not-found message. The germ formula below mixes them — as the statement of Tag 063C
  does — so its proof is a chain of `Eq.trans` and `congrArg` rather than a `rw` sequence.
* **The degree transport is carried by `eqToHom (K.chain_X n)`, not erased.** `K.chain.X n` is
  only *propositionally* the degree-`n` exterior power, so the germ formula is stated about a
  section of `K.chain.X n` obtained by transporting an exterior product along that equality. The
  two transports cancel by `Stacks.RegularSequence.iso_hom_val_app_inv_val_app`.
* The single universe `u` carrying the space, the sections of `O♯` and the sections of every
  module is forced by `TopCat.Presheaf.stalk`, exactly as in `KoszulSheafDifferential` and
  `KoszulStalk`. Nothing is narrowed. The `variable` line writes `KoszulChainData.{u, u, u}` for
  the elaboration-order reason recorded in `KoszulSheafDifferential`: in a binder whose earlier
  entries fix the site data only through the explicit bundle argument, the structure's three
  universe metavariables are solved as `0` before the bundle is looked at.
* No `@[stacks]` attribute. Tag 062K asserts existence and uniqueness of the Koszul
  differential, which this file assumes rather than proves; Tag 01AH is carried by
  `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` and Tag 01CH by
  `SheafOfModules.exteriorAlgebra_stalk`. Tag 063C is a statement about regularity of a sequence,
  which this file does not state.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}

/-- The stalk functor on sheaves of modules preserves zero morphisms. It preserves all colimits
(Stacks Tag 01AH), hence the initial object, hence the zero object. -/
instance stalkFunctor_preservesZeroMorphisms
    (O : Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u}) (x : ↥X) :
    (stalkFunctor O x).PreservesZeroMorphisms :=
  have := stalkFunctor_preservesColimits O x
  inferInstance

/-- The previous instance, respelled with the sheaf of rings written as the `RingCat`-valued
image of a sheaf of commutative rings. The respelling is necessary and not duplication: see the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkComplexIso.lean`. -/
instance stalkFunctor_toRingCat_preservesZeroMorphisms
    (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) (x : ↥X) :
    (stalkFunctor (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x).PreservesZeroMorphisms :=
  stalkFunctor_preservesZeroMorphisms _ x

end AlgebraicGeometry.SheafOfModules

namespace Stacks.RegularSequence

open Stacks.SheafOfModules

/-! ### The wedge of standard basis vectors as a subtype of the exterior algebra -/

/-- The exterior power of a wedge of vectors, written as an element of the submodule `⋀ⁿ E` of
the exterior algebra by its defining membership. This is the coercion between the subtype
spelling of a wedge and `exteriorPower.ιMulti`. -/
theorem exteriorPower_ιMulti_eq_mk {R : Type u} [CommRing R] {E : Type*} [AddCommGroup E]
    [Module R E] (n : ℕ) (v : Fin n → E) :
    exteriorPower.ιMulti R n v = ⟨ExteriorAlgebra.ιMulti R n v, Koszul.ιMulti_mem n v⟩ :=
  rfl

/-! ### The stalk of a complex of sheaves of modules, as a complex of abelian groups -/

section StalkComplex

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}

/-- **The stalk at `x`, as a functor to abelian groups**: the stalk functor of Stacks Tag 01AH
followed by the forgetful functor. The composite with `forget₂` is what makes the two scalar
rings on a stalk — that of the `RingCat`-valued presheaf and that of the `CommRingCat`-valued
one — irrelevant. -/
noncomputable abbrev stalkAbFunctor
    (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) (x : ↥X) :
    SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤ AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x ⋙
    forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk (C := RingCat.{u})
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj x)) AddCommGrpCat.{u}

/-- The underlying abelian group of a stalk module of the ring-level Koszul complex. -/
noncomputable abbrev koszulAbFunctor
    (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) (x : ↥X) :
    ModuleCat.{u} ↑(TopCat.Presheaf.stalk Osharp.obj x) ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk Osharp.obj x)) AddCommGrpCat.{u}

variable (A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
  (koszulFreeSheaf Osharp r))

/-- **The degreewise comparison of Stacks Tag 01CH for a finite free sheaf, read over abelian
groups**: the stalk of `⋀ⁿ((O♯)ʳ)` is the degree-`n` term of the ring-level Koszul complex of any
sequence of germs. -/
noncomputable def exteriorKoszulStalkAbIso (x : ↥X)
    (g : Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)) (n : ℕ) :
    (stalkAbFunctor Osharp x).obj (A.exteriorPower n) ≅
      (koszulAbFunctor Osharp x).obj ((Koszul.seqComplex g).X n) :=
  (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x).toAddEquiv.toAddCommGrpIso

end StalkComplex

/-! ### The stalk of the Koszul complex of a sequence of global sections -/

section Free

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}

variable {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r)}

variable {φ : koszulFreeSheaf Osharp r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

namespace KoszulChainData

variable (K : KoszulChainData.{u, u, u} A φ)

/-- **The differential of the chain complex of Stacks Tag 062K between consecutive nonnegative
degrees**, with the two degree transports written out. This is
`Stacks.RegularSequence.KoszulChainData.chain_d_natCast` solved for the differential. -/
theorem chain_d_eq_dNat (n : ℕ) :
    K.chain.d ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ) =
      eqToHom (K.chain_X ((n + 1 : ℕ) : ℤ)) ≫ K.dNat n ≫
        eqToHom (K.chain_X ((n : ℕ) : ℤ)).symm := by
  rw [← K.chain_d_natCast n]
  simp

/-- The same identity after applying the stalk functor, with the transports grouped as an
isomorphism so that they cancel against the degreewise comparison. -/
theorem stalkAbFunctor_map_chain_d (x : ↥X) (n : ℕ) :
    (stalkAbFunctor Osharp x).map (K.chain.d ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ)) =
      ((stalkAbFunctor Osharp x).mapIso (eqToIso (K.chain_X ((n + 1 : ℕ) : ℤ)))).hom ≫
        (stalkAbFunctor Osharp x).map (K.dNat n) ≫
          ((stalkAbFunctor Osharp x).mapIso (eqToIso (K.chain_X ((n : ℕ) : ℤ)))).inv := by
  rw [chain_d_eq_dNat, Functor.map_comp, Functor.map_comp]
  rfl

/-- **The degreewise comparison.** In degree `n` the stalk of the Koszul complex of sheaves is
the degree-`n` term of the ring-level Koszul complex of the sequence of germs: the degree
transport of Tag 062K's chain complex followed by the comparison of Tag 01CH. -/
noncomputable def stalkChainXIso (x : ↥X)
    (g : Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)) (n : ℕ) :
    (stalkAbFunctor Osharp x).obj (K.chain.X ((n : ℕ) : ℤ)) ≅
      (koszulAbFunctor Osharp x).obj ((Koszul.seqComplex g).X n) :=
  (stalkAbFunctor Osharp x).mapIso (eqToIso (K.chain_X ((n : ℕ) : ℤ))) ≪≫
    exteriorKoszulStalkAbIso A x g n

variable (f : Fin r → ↑(Osharp.obj.obj (op (⊤ : Opens ↥X))))
  (hφ : ∀ k : Fin r,
    ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
      (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)

include hφ in
/-- **The comparison of Tag 01CH intertwines the two Koszul differentials at a stalk.** This is
`Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin` read as an equality of morphisms of
abelian groups. -/
theorem exteriorKoszulStalkAbIso_comm (x : ↥X) (n : ℕ) :
    (exteriorKoszulStalkAbIso A x
            (fun k => TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
              (f k)) (n + 1)).hom ≫
        (koszulAbFunctor Osharp x).map ((Koszul.seqComplex fun k =>
          TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
            (f k)).d (n + 1) n) =
      (stalkAbFunctor Osharp x).map (K.dNat n) ≫
        (exteriorKoszulStalkAbIso A x
          (fun k => TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
            (f k)) n).hom := by
  ext m
  rw [Koszul.seqComplex_d]
  exact (exteriorKoszulStalkEquiv_stalkLin K f hφ n x m).symm

include hφ in
/-- **The degreewise comparison commutes with the differentials.** Only the squares between
consecutive nonnegative degrees carry content, and this is that content: the degree transports
of Tag 062K's chain complex cancel and what remains is
`Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin`. -/
theorem stalkChainXIso_comm (x : ↥X) (n : ℕ) :
    (K.stalkChainXIso x (fun k => TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x
            (Opens.mem_top x) (f k)) (n + 1)).hom ≫
        (koszulAbFunctor Osharp x).map ((Koszul.seqComplex fun k =>
          TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
            (f k)).d (n + 1) n) =
      (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj K.chain).d
          ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ) ≫
        (K.stalkChainXIso x (fun k => TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x
          (Opens.mem_top x) (f k)) n).hom := by
  simp only [stalkChainXIso, Iso.trans_hom, Functor.mapHomologicalComplex_obj_d,
    stalkAbFunctor_map_chain_d, Category.assoc, Iso.inv_hom_id_assoc]
  rw [exteriorKoszulStalkAbIso_comm K f hφ x n]

/-- **The stalk of the Koszul complex of sheaves vanishes in negative degrees**, because Tag
062K's chain complex does. -/
theorem isZero_stalkChain_X_of_neg (x : ↥X) (n : ℤ) (hn : n < 0) :
    IsZero ((((stalkAbFunctor Osharp x).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj K.chain).X n) :=
  Functor.map_isZero (stalkAbFunctor Osharp x) (K.isZero_chain_X_of_neg hn)

include hφ in
/-- **The stalk of the Koszul complex of a sequence of global sections is the Koszul complex of
the sequence of germs.** The stalk functor of Stacks Tag 01AH, applied degreewise to the Koszul
complex of sheaves of Stacks Tag 062K, gives a `ℤ`-indexed complex of abelian groups isomorphic
to the ring-level Koszul complex of the germs of `f` at `x`, extended by zero to negative
degrees and re-indexed homologically. -/
noncomputable def stalkChainIso (x : ↥X) :
    (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj K.chain) ≅
      (Stacks.ChainComplexIntBridge.natToIntAbFunctor
          ↑(TopCat.Presheaf.stalk Osharp.obj x)).obj
        (Koszul.seqComplex fun k =>
          TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) :=
  Stacks.ChainComplexIntBridge.isoNatToIntAb _ _
    (K.stalkChainXIso x fun k =>
      TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k))
    (K.stalkChainXIso_comm f hφ x) (K.isZero_stalkChain_X_of_neg x)

include hφ in
/-- In degree `(n : ℤ)`, followed by the degreewise identification of the zero-extension, the
comparison is the degreewise comparison. -/
theorem stalkChainIso_hom_f (x : ↥X) (n : ℕ)
    (m : ↑((stalkAbFunctor Osharp x).obj (K.chain.X ((n : ℕ) : ℤ)))) :
    (Stacks.ChainComplexIntBridge.natToIntAbXIso (Koszul.seqComplex fun k =>
            TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n).hom
        ((K.stalkChainIso f hφ x).hom.f (n : ℤ) m) =
      (K.stalkChainXIso x (fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n).hom m :=
  ConcreteCategory.congr_hom
    (Stacks.ChainComplexIntBridge.natToIntAbXIso_hom_isoNatToIntAb_hom_f
      (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj K.chain)
      (Koszul.seqComplex fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k))
      (K.stalkChainXIso x fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k))
      (K.stalkChainXIso_comm f hφ x) (K.isZero_stalkChain_X_of_neg x) n) m

include hφ in
/-- **The characterizing germ formula.** In degree `n` the comparison sends the germ of a scalar
times an ordered exterior product of tautological generators to the corresponding multiple of
the wedge of standard basis vectors over the stalk ring, with the scalar replaced by its germ.
This includes the unit in degree zero and the individual generators in degree one.

The section the germ is taken of lives in `K.chain.X n`, which is only propositionally the
degree-`n` exterior power, so the exterior product is transported along `K.chain_X n`. -/
theorem stalkChainIso_germ_smul_exteriorBasisSection (x : ↥X) (n : ℕ) (U : Opens ↥X)
    (hx : x ∈ U) (a : ↑(Osharp.obj.obj (op U))) (i : Fin n → Fin r) :
    (Stacks.ChainComplexIntBridge.natToIntAbXIso (Koszul.seqComplex fun k =>
            TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n).hom
        ((K.stalkChainIso f hφ x).hom.f (n : ℤ)
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
              (K.chain.X ((n : ℕ) : ℤ)).val.presheaf U x hx)
            (((eqToHom (K.chain_X ((n : ℕ) : ℤ)).symm).val.app (op U))
              (a • exteriorBasisSection A U n i)))) =
      TopCat.Presheaf.germ Osharp.obj U x hx a •
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
          fun j => Pi.single (i j) 1 := by
  refine Eq.trans (K.stalkChainIso_hom_f f hφ x n _) ?_
  refine Eq.trans ?_
    (Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_smul_exteriorBasisSection A n U hx a i)
  refine Eq.trans
    (congrArg (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x)
      (stalkAddHom_germAddHom (eqToHom (K.chain_X ((n : ℕ) : ℤ))).val U hx
        (((eqToHom (K.chain_X ((n : ℕ) : ℤ)).symm).val.app (op U))
          (a • exteriorBasisSection A U n i)))) ?_
  exact congrArg (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x)
    (congrArg (Stacks.SheafOfModules.germAddHom (A.exteriorPower n).val U hx)
      (iso_hom_val_app_inv_val_app (eqToIso (K.chain_X ((n : ℕ) : ℤ))) (op U) _))

include hφ in
/-- **The stalk comparison for the Koszul complex of a sequence of global sections**, packaged as
one existential statement: an isomorphism of `ℤ`-indexed complexes of abelian groups between the
stalk of the Koszul complex of sheaves and the zero-extension of the ring-level Koszul complex of
the germs, together with the germ formula that characterizes it.

The target complex is written in the `extend`-then-`restriction`-then-`forget₂` spelling and the
wedge as a subtype of the exterior algebra; both are the same objects as in
`Stacks.RegularSequence.KoszulChainData.stalkChainIso` and
`stalkChainIso_germ_smul_exteriorBasisSection`, by `Stacks.ChainComplexIntBridge`
`.natToIntAbFunctor_obj` and `Stacks.RegularSequence.exteriorPower_ιMulti_eq_mk`. -/
theorem exists_stalkChainIso (x : ↥X) :
    ∃ e : (((stalkAbFunctor Osharp x).mapHomologicalComplex (ComplexShape.down ℤ)).obj
          K.chain) ≅
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
                (K.chain.X ((n : ℕ) : ℤ)).val.presheaf U x hx)
              (((eqToHom (K.chain_X ((n : ℕ) : ℤ)).symm).val.app (op U))
                (a • exteriorBasisSection A U n i)))) =
          TopCat.Presheaf.germ Osharp.obj U x hx a •
            (⟨ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
                fun j => Pi.single (i j) 1, Koszul.ιMulti_mem n _⟩ :
              ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n
                (Fin r → ↑(TopCat.Presheaf.stalk Osharp.obj x)))) :=
  ⟨K.stalkChainIso f hφ x, fun n U hx a i =>
    K.stalkChainIso_germ_smul_exteriorBasisSection f hφ x n U hx a i⟩

end KoszulChainData

end Free

end Stacks.RegularSequence

end
