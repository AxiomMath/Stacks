module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit

/-!
# The derived colimit of a system of differential graded modules

Let `(A, d)` be a differential graded algebra and let `M₀ → M₁ → M₂ → ⋯` be a system of right
differential graded `A`-modules. Its derived colimit `hocolim Mₙ` in `D(A, d)` — the third vertex
of a distinguished triangle on the map `1 - f : ⊕ Mₙ ⟶ ⊕ Mₙ` — is represented by the ordinary
colimit `colim Mₙ` of differential graded modules.

The proof is the one of the source, in the form already used for complexes in an abelian
category. Lemma 093W presents the colimit of a system over `ℕ` as the cokernel of `1 - f`, so
`0 → ⊕ Mₙ → ⊕ Mₙ → colim Mₙ → 0` is a short exact sequence of differential graded modules; the
canonical `δ`-functor of Tag 09L0 turns it into a distinguished triangle of `D(A, d)`; and the
image of a direct sum of differential graded modules is a direct sum in `D(A, d)` (Tag 09QI), so
that triangle is the one Definition 090Z asks for.

## Main results

* `DifferentialGradedModule.mono_oneSubShift`: the map `1 - f` of a system over `ℕ` of
  differential graded modules is a monomorphism.
* `DifferentialGradedModule.shortExact_oneSubShift_piMap`: Lemma 093W for differential graded
  modules — `0 → ⊕ Mₙ → ⊕ Mₙ → colim Mₙ → 0` is short exact.
* `DifferentialGradedModule.isHomotopyColimit_toDerivedCategory_obj_colimit`: the derived colimit
  of a system over `ℕ` of differential graded modules is represented by its colimit.

## Implementation notes

*Why `1 - f` has to be shown to be a monomorphism by hand.* The general form of Lemma 093W
(`Stacks.CountableCoproducts.mono_oneSubShift`) deduces it from exactness of colimits over `ℕ`,
which for differential graded modules is not available: the colimits of
`DifferentialGradedModule.differentialGradedModule_hasColimits` are produced abstractly from
coproducts and cokernels, so nothing is known about their elements. Instead the statement is
proved directly, on the concrete direct sum `DifferentialGradedModule.directSumObj`, whose
carrier is the honest direct sum of the carriers: an element killed by `1 - f` has all its
telescope coordinates zero, by induction from the zeroth, hence is zero. Monomorphy transfers
to the chosen coproduct along the comparison isomorphism. The two remaining conditions of a
short exact sequence, surjectivity of `π` and exactness in the middle, are the general ones and
carry no hypothesis.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules live in a single universe `u`; the index type of a direct sum lives there too, so
the system over `ℕ` is reindexed by `ULift ℕ` where a concrete direct sum is needed.

## References

* [Stacks Project, Tag 0CRL](https://stacks.math.columbia.edu/tag/0CRL); the presentation of a
  colimit as a cokernel is [Tag 093W](https://stacks.math.columbia.edu/tag/093W), the canonical
  `δ`-functor is [Tag 09L0](https://stacks.math.columbia.edu/tag/09L0), direct sums in the
  derived category are [Tag 09QI](https://stacks.math.columbia.edu/tag/09QI) and the definition
  of a derived colimit is [Tag 090Z](https://stacks.math.columbia.edu/tag/090Z).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.CountableCoproducts
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Coordinates on a concrete direct sum -/

section Projection

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, u, u} A)

/-- The `j`-th coordinate `⨁ᵢ Nᵢ ⟶ N j` of the concrete direct sum of differential graded
modules. Unlike the coprojections, the coordinates are available only on the concrete model,
where the grading, the action and the differential are all componentwise. -/
def directSumProj (j : ι) : directSumObj N ⟶ N j where
  toFun := DirectSum.component R ι (fun i => (N i).M) j
  map_smul _ _ := rfl
  map_grading _ _ hx := hx j
  map_d := LinearMap.ext fun x => directSumD_apply N x j

/-- The `j`-th coordinate of an element of the concrete direct sum is its `j`-th component. -/
@[simp] theorem directSumProj_toFun_apply (j : ι) (x : ⨁ i, (N i).M) :
    (directSumProj N j).toFun x = x j := rfl

/-- A coprojection followed by a coordinate is the identity on the diagonal and zero off it. -/
theorem directSumInj_comp_directSumProj_self (j : ι) :
    directSumInj N j ≫ directSumProj N j = 𝟙 (N j) := by
  classical
  refine Hom.ext (LinearMap.ext fun y => ?_)
  change DirectSum.component R ι (fun i => (N i).M) j
    (DirectSum.lof R ι (fun i => (N i).M) j y) = y
  rw [DirectSum.component.lof_self]

/-- An element of the concrete direct sum all of whose coordinates vanish is zero. -/
theorem directSum_eq_zero_of_proj (x : (directSumObj N).M)
    (h : ∀ j, (directSumProj N j).toFun x = 0) : x = 0 := by
  refine DirectSum.ext fun j => ?_
  simpa using h j

end Projection

/-! ### The telescope coordinates of a system over `ℕ` -/

section Telescope

variable (F : ℕ ⥤ DifferentialGradedModule.{u, u, u} A)

/-- The reindexing of a system over `ℕ` by `ULift ℕ`, so that its direct sum can be formed
concretely: the index type of `DifferentialGradedModule.directSumObj` lives in the universe of
the algebra. -/
abbrev liftSystem : ULift.{u} ℕ → DifferentialGradedModule A := fun i => F.obj i.down

/-- The concrete direct sum `⨁ₙ Mₙ` of a system over `ℕ`, with the coprojections indexed by `ℕ`,
is a coproduct of the family. -/
def isColimitCofanDirectSum :
    IsColimit (Cofan.mk (directSumObj (liftSystem.{u} F))
      (fun n : ℕ => directSumInj (liftSystem.{u} F) (ULift.up n))) :=
  Cofan.IsColimit.mk _ (fun s => directSumDesc _ (fun i => s.inj i.down))
    (fun s n => directSumInj_comp_directSumDesc _ _ (ULift.up n))
    (fun s m hm => directSum_hom_ext _ fun i => by
      rw [directSumInj_comp_directSumDesc]
      exact hm i.down)

variable [HasCoproduct F.obj]

/-- The comparison of the concrete direct sum of a system over `ℕ` with the chosen coproduct. -/
def directSumCoproductIso : directSumObj (liftSystem.{u} F) ≅ ∐ F.obj :=
  IsColimit.coconePointUniqueUpToIso (isColimitCofanDirectSum F) (colimit.isColimit _)

/-- The comparison carries the `n`-th coprojection of the concrete direct sum to the `n`-th
coprojection of the chosen coproduct. -/
@[reassoc]
theorem directSumInj_comp_directSumCoproductIso_hom (n : ℕ) :
    directSumInj (liftSystem.{u} F) (ULift.up n) ≫ (directSumCoproductIso F).hom =
      Sigma.ι F.obj n :=
  (isColimitCofanDirectSum F).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (Discrete.mk n)

/-- The `n`-th telescope coordinate `⊕ₖ Mₖ ⟶ Mₙ` of a system over `ℕ`: the identity on the
`n`-th summand and zero on the others. -/
def telescopeCoord (n : ℕ) : (∐ F.obj) ⟶ F.obj n :=
  Sigma.desc fun i => if h : i = n then eqToHom (congrArg F.obj h) else 0

/-- The `i`-th coprojection followed by the `n`-th telescope coordinate is the identity when
`i = n` and zero otherwise. -/
theorem ι_telescopeCoord (n i : ℕ) :
    Sigma.ι F.obj i ≫ telescopeCoord F n =
      if h : i = n then eqToHom (congrArg F.obj h) else 0 :=
  Sigma.ι_comp_desc _ _

/-- The comparison carries the `n`-th telescope coordinate to the `n`-th coordinate of the
concrete direct sum. -/
theorem directSumCoproductIso_hom_comp_telescopeCoord (n : ℕ) :
    (directSumCoproductIso F).hom ≫ telescopeCoord F n =
      directSumProj (liftSystem.{u} F) (ULift.up n) := by
  refine directSum_hom_ext (liftSystem.{u} F) fun i => ?_
  rw [← Category.assoc, directSumInj_comp_directSumCoproductIso_hom, ι_telescopeCoord]
  obtain ⟨m⟩ := i
  by_cases h : m = n
  · subst h
    rw [directSumInj_comp_directSumProj_self]
    simp
  · have hne : (ULift.up m : ULift.{u} ℕ) ≠ ULift.up n := fun hh => h (congrArg ULift.down hh)
    have hz : directSumInj (liftSystem.{u} F) (ULift.up m) ≫
        directSumProj (liftSystem.{u} F) (ULift.up n) = 0 := by
      refine Hom.ext (LinearMap.ext fun y => ?_)
      change DirectSum.component R (ULift.{u} ℕ) (fun i => (F.obj i.down).M) (ULift.up n)
        (DirectSum.lof R (ULift.{u} ℕ) (fun i => (F.obj i.down).M) (ULift.up m) y) = 0
      rw [DirectSum.component.of]
      simp [hne]
    rw [hz]
    simp [h]

/-- The zeroth telescope coordinate of `(1 - f) x` is the zeroth telescope coordinate of `x`. -/
theorem oneSubShift_comp_telescopeCoord_zero :
    oneSubShift F ≫ telescopeCoord F 0 = telescopeCoord F 0 := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, ι_oneSubShift, Preadditive.sub_comp, Category.assoc,
    ι_telescopeCoord, ι_telescopeCoord]
  simp

/-- The `(n + 1)`-st telescope coordinate of `(1 - f) x` is `xₙ₊₁ - fₙ xₙ`. -/
theorem oneSubShift_comp_telescopeCoord_succ (n : ℕ) :
    oneSubShift F ≫ telescopeCoord F (n + 1) =
      telescopeCoord F (n + 1) - telescopeCoord F n ≫ F.map (homOfLE (Nat.le_succ n)) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, ι_oneSubShift, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.assoc, ← Category.assoc (Sigma.ι F.obj i), ι_telescopeCoord, ι_telescopeCoord,
    ι_telescopeCoord]
  by_cases hi : i = n
  · subst hi; simp
  · by_cases hi' : i = n + 1
    · subst hi'; simp
    · simp [hi, hi']

/-- An element of the concrete direct sum killed by `1 - f` is zero. -/
theorem eq_zero_of_oneSubShift_eq_zero (y : (directSumObj (liftSystem.{u} F)).M)
    (hy : (oneSubShift F).toFun ((directSumCoproductIso F).hom.toFun y) = 0) : y = 0 := by
  refine directSum_eq_zero_of_proj _ y fun j => ?_
  obtain ⟨n⟩ := j
  have h0 : ∀ k, ((directSumCoproductIso F).hom ≫ oneSubShift F ≫ telescopeCoord F k).toFun y
      = 0 := fun k => by
    rw [Hom.comp_toFun_apply, Hom.comp_toFun_apply, hy, map_zero]
  induction n with
  | zero =>
      have h1 := h0 0
      rw [oneSubShift_comp_telescopeCoord_zero,
        directSumCoproductIso_hom_comp_telescopeCoord] at h1
      exact h1
  | succ n ih =>
      have h1 := h0 (n + 1)
      rw [oneSubShift_comp_telescopeCoord_succ, Preadditive.comp_sub, ← Category.assoc,
        directSumCoproductIso_hom_comp_telescopeCoord,
        directSumCoproductIso_hom_comp_telescopeCoord] at h1
      rw [Hom.hom_sub_toFun, LinearMap.sub_apply, Hom.comp_toFun_apply, ih, map_zero,
        sub_zero] at h1
      exact h1

/-- **The map `1 - f` of a system of differential graded modules is a monomorphism.** -/
theorem mono_oneSubShift : Mono (oneSubShift F) := by
  refine ⟨fun {Z} g h hgh => Hom.ext (LinearMap.ext fun x => ?_)⟩
  have hgh' := LinearMap.congr_fun (congrArg Hom.toFun hgh) x
  rw [Hom.comp_toFun_apply, Hom.comp_toFun_apply] at hgh'
  refine sub_eq_zero.mp ?_
  have hinvhom : ∀ z : (∐ F.obj).M, (directSumCoproductIso F).hom.toFun
      ((directSumCoproductIso F).inv.toFun z) = z := fun z => by
    have := LinearMap.congr_fun
      (congrArg Hom.toFun (directSumCoproductIso F).inv_hom_id) z
    rwa [Hom.comp_toFun_apply] at this
  have hy : (oneSubShift F).toFun ((directSumCoproductIso F).hom.toFun
      ((directSumCoproductIso F).inv.toFun (g.toFun x - h.toFun x))) = 0 := by
    rw [hinvhom, map_sub, hgh', sub_self]
  have hz := eq_zero_of_oneSubShift_eq_zero F _ hy
  rw [← hinvhom (g.toFun x - h.toFun x), hz, map_zero]

end Telescope

/-! ### Lemma 093W for differential graded modules -/

section ShortExact

variable (F : ℕ ⥤ DifferentialGradedModule.{u, u, u} A) [HasCoproduct F.obj] [HasColimit F]

/-- **Lemma 093W for differential graded modules.** For a system `M₀ → M₁ → ⋯` of right
differential graded `A`-modules the sequence
`0 → ⊕ₙ Mₙ --(1 - f)--> ⊕ₙ Mₙ --π--> colim Mₙ → 0` is short exact. -/
@[stacks 093W "differential graded modules"]
theorem shortExact_oneSubShift_piMap :
    ∃ w : oneSubShift F ≫ piMap F = 0,
      (ShortComplex.mk (oneSubShift F) (piMap F) w).ShortExact := by
  refine ⟨comp_oneSubShift_piMap F, ?_⟩
  have := mono_oneSubShift F
  have := epi_piMap F
  exact ⟨Stacks.CountableCoproducts.exact_oneSubShift_piMap F⟩

end ShortExact

/-! ### The derived colimit -/

section DerivedColimit

/-! Two pretriangulated structures on `K(A, d)` are in scope here:
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose distinguished triangles
are the cone triangles, and `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`,
whose distinguished triangles come from admissible short exact sequences. The two classes of
triangles agree only by Tag 09KH, which is not formalized, so the structures are distinct data.
The `δ`-functor of Tag 09L0, `DifferentialGradedModule.canonicalDeltaFunctorStructure`, is built
over the cone-triangle one, so that is the structure the derived colimit below has to be read
in, and it is the one given priority for the statements of this section. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory

/-- `Mod_{(A, d)}` is cocomplete, Tag 09JJ, in the form instance search uses: the hom-sets and
the indexing categories live in the single universe of the chapter's encoding. -/
instance hasColimits_differentialGradedModule (A : DifferentialGradedAlgebra.{u, u} R) :
    HasColimits (DifferentialGradedModule.{u, u, u} A) :=
  differentialGradedModule_hasColimits.{u, u, u} A

/-- `D(A, d)` has countable direct sums: it has all `Type u`-indexed ones (Tag 09QI), and `ℕ` is
in bijection with an index type in that universe. -/
instance hasColimitsOfShape_discrete_nat_derivedCategory
    (A : DifferentialGradedAlgebra.{u, u} R) :
    HasColimitsOfShape (Discrete ℕ) (derivedCategory.{u, u, u} A) :=
  haveI : HasColimitsOfShape (Discrete (ULift.{u} ℕ)) (derivedCategory.{u, u, u} A) :=
    hasCoproducts_derivedCategory A (ULift.{u} ℕ)
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{u, 0}))

/-- Let `(A, d)` be a differential graded algebra and `Mₙ` a system of differential graded
modules. Then the derived colimit `hocolim Mₙ` in `D(A, d)` is represented by the differential
graded module `colim Mₙ`. -/
@[stacks 0CRL]
theorem isHomotopyColimit_toDerivedCategory_obj_colimit
    (A : DifferentialGradedAlgebra.{u, u} R) (F : ℕ ⥤ DifferentialGradedModule.{u, u, u} A) :
    IsHomotopyColimit (F ⋙ toDerivedCategory A) ((toDerivedCategory A).obj (colimit F)) := by
  have : (quasiIsomorphisms.{u, u, u} A).Q.Additive :=
    Localization.functor_additive (quasiIsomorphisms A).Q (quasiIsomorphisms A)
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) (toDerivedCategory A) :=
    derivedCategoryQ_preservesCoproducts A (ULift.{u} ℕ)
  have : PreservesColimitsOfShape (Discrete ℕ) (toDerivedCategory A) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0})) _
  have : HasCoproduct fun n => (toDerivedCategory A).obj (F.obj n) := inferInstance
  obtain ⟨w, hSE⟩ := shortExact_oneSubShift_piMap F
  set e := asIso (sigmaComparison (toDerivedCategory A) F.obj) with he
  refine ⟨e.hom ≫ (toDerivedCategory A).map (piMap F),
    (canonicalDeltaFunctorStructure A).δ hSE ≫
      (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map e.inv, ?_⟩
  refine isomorphic_distinguished _ ((canonicalDeltaFunctorStructure A).distinguished hSE) _
    (Triangle.isoMk _ _ e e (Iso.refl _) ?_ ?_ ?_)
  · exact oneSubShift_comp_sigmaComparison (toDerivedCategory A) F
  · exact Category.comp_id _
  · exact (by rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] :
        ((canonicalDeltaFunctorStructure A).δ hSE ≫
            (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map e.inv) ≫
          (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map e.hom
            = 𝟙 ((toDerivedCategory A).obj (colimit F)) ≫
                (canonicalDeltaFunctorStructure A).δ hSE)

end DerivedColimit

end DifferentialGradedModule

end
