module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedNullHomotopyExtension
public import StacksFrontier.Homology.Injectives.KInjective.AcyclicSubobjects

/-!
# Maps from an acyclic module into a graded injective are null-homotopic

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. Fix a
*set* of nonzero acyclic right differential graded `A`-modules detecting all of them — the
family of Tag 0FST — and a graded injective module `I` such that every morphism into `I` from a
member of that family is null-homotopic. This file proves that then **every** morphism into `I`
from an acyclic right differential graded module is null-homotopic.

This is the substance of the implication (2) ⟹ (1) of Tag 0FSY, and it follows the proof of
Tag 079L.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopic_zero_of_acyclic_of_detectingFamily`: the
  vanishing described above.

## Implementation notes

**The argument.** A *partial null homotopy* of `f : M ⟶ I` is an acyclic differential graded
submodule `S ⊆ M` together with an action-linear cochain of degree `-1` on `S` whose commutator
with the differentials is the restriction of `f`. These are ordered by extension. A chain has an
upper bound: the supremum of the subobjects is their filtered colimit, so it is acyclic and the
cochains glue, which is `exists_actionLinear_colimit`. By Zorn there is a maximal partial null
homotopy. If its subobject `S` were not everything, the cokernel `M / S` would be a nonzero
acyclic module, hence would contain a member of the detecting family; the preimage of that
member in `M` is a strictly larger acyclic submodule, and the null homotopy extends to it by
`exists_actionLinear_delta_extension` — contradicting maximality. So `S` is everything and the
cochain is the required null homotopy.

**Indexing the chain.** A chain is indexed by the *subobjects* occurring in it rather than by
its own elements, because the subobjects of a module form a set in the module universe while
the partial null homotopies do not visibly do so. Two partial null homotopies in a chain with
the same subobject are equal, which is `partialNullHomotopy_eq_of_same_subobject`, so this loses
nothing.

**What is needed of the ambient category.** The supremum of a directed family of subobjects is
its filtered colimit — `CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`
for the Grothendieck abelian category of right differential graded modules, Tag 0FS9 — and
acyclicity passes to that colimit because passing to the underlying cochain complex preserves
it and filtered colimits of sheaves of modules are exact.

## References

* [Stacks Project, Tag 0FSY](https://stacks.math.columbia.edu/tag/0FSY)
* [Stacks Project, Tag 079L](https://stacks.math.columbia.edu/tag/079L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-! ### Passing to the underlying cochain complex -/

omit [HasWeakSheafify X.J (Type max u v w)] in
/-- Taking the degree `n` component of the underlying cochain complex commutes with colimits
of the size of the module universe. -/
theorem toCochainComplex_eval_preservesColimitsOfShape
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (K : Type max u v w) [Category.{max u v w} K] (n : ℤ) :
    PreservesColimitsOfShape K (toCochainComplex.{u, v, max u v w} A ⋙
      HomologicalComplex.eval (SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) n) := by
  have hf : PreservesColimitsOfShape K (forgetToGradedModule.{u, v, max u v w} A) :=
    (forgetToGradedModule_preservesColimitsOfSize.{u, v, max u v w, u, u,
      max u v w, max u v w} A).preservesColimitsOfShape
  have hcol : PreservesColimitsOfShape K
      (GradedModule.pieceFunctor.{u, v, max u v w} A.toGradedAlgebra n) :=
    (GradedModule.pieceFunctor_preservesColimitsOfSize'.{u, v, max u v w, u, u}
      (A := A.toGradedAlgebra) n).preservesColimitsOfShape
  have he : toCochainComplex.{u, v, max u v w} A ⋙
      HomologicalComplex.eval (SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) n =
      forgetToGradedModule.{u, v, max u v w} A ⋙
        GradedModule.pieceFunctor A.toGradedAlgebra n := rfl
  rw [he]
  exact comp_preservesColimitsOfShape _ _

omit [HasWeakSheafify X.J (Type max u v w)] in
/-- Passing to the underlying cochain complex commutes with colimits of the size of the module
universe: forgetting the differential is a left adjoint and taking a homogeneous component
commutes with colimits by Tag 0FR0. -/
theorem toCochainComplex_preservesColimitsOfShape
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (K : Type max u v w) [Category.{max u v w} K] :
    PreservesColimitsOfShape K (toCochainComplex.{u, v, max u v w} A) :=
  (toCochainComplex_preservesColimitsOfSize A).preservesColimitsOfShape

omit [HasWeakSheafify X.J (Type max u v w)] [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The underlying map of complexes of the identity. -/
@[simp] theorem toHomologicalComplex_id
    (M : DifferentialGradedModule.{u, v, max u v w} A) :
    Hom.toHomologicalComplex (𝟙 M) = 𝟙 M.complex := rfl

omit [HasWeakSheafify X.J (Type max u v w)] [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The underlying map of complexes of the zero morphism. -/
@[simp] theorem toHomologicalComplex_zero
    (M N : DifferentialGradedModule.{u, v, max u v w} A) :
    Hom.toHomologicalComplex (0 : M ⟶ N) = 0 := rfl

/-- Passing to the underlying cochain complex is additive. -/
instance toCochainComplex_additive
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (toCochainComplex.{u, v, max u v w} A).Additive where
  map_add := rfl

/-- Passing to the underlying cochain complex preserves finite limits. -/
instance toCochainComplex_preservesFiniteLimits
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesFiniteLimits (toCochainComplex.{u, v, max u v w} A) where
  preservesFiniteLimits K _ _ := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    have hf : PreservesLimitsOfShape K (forgetToGradedModule.{u, v, max u v w} A) :=
      (forgetToGradedModule_preservesLimitsOfSize.{u, v, max u v w, u, u, 0, 0}
        A).preservesLimitsOfShape
    have hcol : PreservesLimitsOfShape K
        (GradedModule.pieceFunctor.{u, v, max u v w} A.toGradedAlgebra n) :=
      (GradedModule.pieceFunctor_preservesFiniteLimits
        (A := A.toGradedAlgebra) n).preservesFiniteLimits K
    have he : toCochainComplex.{u, v, max u v w} A ⋙
        HomologicalComplex.eval (SheafOfModules.{max u v w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n =
        forgetToGradedModule.{u, v, max u v w} A ⋙
          GradedModule.pieceFunctor A.toGradedAlgebra n := rfl
    rw [he]
    exact comp_preservesLimitsOfShape _ _

/-- Passing to the underlying cochain complex preserves finite colimits. -/
instance toCochainComplex_preservesFiniteColimits
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesFiniteColimits (toCochainComplex.{u, v, max u v w} A) where
  preservesFiniteColimits K _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    have hf : PreservesColimitsOfShape K (forgetToGradedModule.{u, v, max u v w} A) :=
      (forgetToGradedModule_preservesColimitsOfSize.{u, v, max u v w, u, u, 0, 0}
        A).preservesColimitsOfShape
    have hcol : PreservesColimitsOfShape K
        (GradedModule.pieceFunctor.{u, v, max u v w} A.toGradedAlgebra n) :=
      ((GradedModule.pieceFunctor_preservesColimitsOfSize'.{u, v, max u v w, u, u}
        (A := A.toGradedAlgebra) n).preservesFiniteColimits).preservesFiniteColimits K
    have he : toCochainComplex.{u, v, max u v w} A ⋙
        HomologicalComplex.eval (SheafOfModules.{max u v w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n =
        forgetToGradedModule.{u, v, max u v w} A ⋙
          GradedModule.pieceFunctor A.toGradedAlgebra n := rfl
    rw [he]
    exact comp_preservesColimitsOfShape _ _

/-! ### Partial null homotopies -/

variable (A)

/-- A partial null homotopy of `f : M ⟶ I`: an acyclic differential graded submodule of `M`
together with an action-linear cochain of degree `-1` on it whose commutator with the
differentials is the restriction of `f`. -/
private structure PartialNullHomotopy (M I : DifferentialGradedModule.{u, v, max u v w} A)
    (f : M ⟶ I) where
  /-- The submodule on which the null homotopy is defined. -/
  S : Subobject M
  /-- The submodule is acyclic. -/
  acyclic : (S : DifferentialGradedModule.{u, v, max u v w} A).complex.Acyclic
  /-- The cochain of degree `-1`. -/
  z : Cochain (S : DifferentialGradedModule.{u, v, max u v w} A).complex I.complex (-1)
  /-- The cochain commutes with the action of the algebra. -/
  linear : IsActionLinear A z
  /-- Its commutator with the differentials is the restriction of `f`. -/
  boundary : δ (-1) 0 z = Cochain.ofHom (S.arrow ≫ f).toHomologicalComplex

variable {A}

private def partialNullHomotopyLE {M I : DifferentialGradedModule.{u, v, max u v w} A}
    {f : M ⟶ I} (a b : PartialNullHomotopy A M I f) : Prop :=
  ∃ h : a.S ≤ b.S,
    (Cochain.ofHom (Subobject.ofLE a.S b.S h).toHomologicalComplex).comp b.z
      (zero_add (-1)) = a.z

private instance partialNullHomotopyPartialOrder
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I} :
    PartialOrder (PartialNullHomotopy A M I f) where
  le := partialNullHomotopyLE
  le_refl a := by
    refine ⟨le_rfl, ?_⟩
    rw [Subobject.ofLE_refl]
    exact Cochain.id_comp a.z
  le_trans a b c hab hbc := by
    obtain ⟨hab, habz⟩ := hab
    obtain ⟨hbc, hbcz⟩ := hbc
    refine ⟨hab.trans hbc, ?_⟩
    change (Cochain.ofHom (Subobject.ofLE a.S c.S (hab.trans hbc)).toHomologicalComplex).comp
      c.z (zero_add (-1)) = a.z
    rw [← Subobject.ofLE_comp_ofLE a.S b.S c.S hab hbc]
    change (Cochain.ofHom ((Subobject.ofLE a.S b.S hab).toHomologicalComplex ≫
      (Subobject.ofLE b.S c.S hbc).toHomologicalComplex)).comp c.z (zero_add (-1)) = a.z
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, hbcz, habz]
  le_antisymm a b hab hba := by
    obtain ⟨hab, habz⟩ := hab
    obtain ⟨hba, -⟩ := hba
    cases a with
    | mk Sa ha za la ba =>
      cases b with
      | mk Sb hb zb lb bb =>
        obtain rfl : Sa = Sb := le_antisymm hab hba
        have hz : za = zb := by
          rw [Subobject.ofLE_refl] at habz
          exact ((Cochain.id_comp zb).symm.trans habz).symm
        cases hz
        rfl

omit [HasWeakSheafify X.J (Type max u v w)] [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
private lemma partialNullHomotopy_le_of_reverse
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I}
    {a b : PartialNullHomotopy A M I f} (habS : a.S ≤ b.S) (hba : b ≤ a) : a ≤ b := by
  obtain ⟨hbaS, hbaz⟩ := hba
  set φ := Subobject.ofLE a.S b.S habS with hφ
  set ψ := Subobject.ofLE b.S a.S hbaS with hψ
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply (cancel_mono a.S.arrow).1
    rw [hφ, hψ, Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow, Category.id_comp]
  refine ⟨habS, ?_⟩
  show (Cochain.ofHom φ.toHomologicalComplex).comp b.z (zero_add (-1)) = a.z
  have hbaz' : (Cochain.ofHom ψ.toHomologicalComplex).comp a.z (zero_add (-1)) = b.z := hbaz
  calc
    (Cochain.ofHom φ.toHomologicalComplex).comp b.z (zero_add (-1)) =
        (Cochain.ofHom φ.toHomologicalComplex).comp
          ((Cochain.ofHom ψ.toHomologicalComplex).comp a.z (zero_add (-1)))
          (zero_add (-1)) := by rw [hbaz']
    _ = (Cochain.ofHom (φ ≫ ψ).toHomologicalComplex).comp a.z (zero_add (-1)) := by
        rw [show ((φ ≫ ψ).toHomologicalComplex) =
          φ.toHomologicalComplex ≫ ψ.toHomologicalComplex from rfl, Cochain.ofHom_comp,
          ← Cochain.comp_assoc_of_first_is_zero_cochain]
    _ = a.z := by
        rw [hφψ]
        exact Cochain.id_comp a.z

omit [HasWeakSheafify X.J (Type max u v w)] [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
private lemma partialNullHomotopy_eq_of_same_subobject
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I}
    {a b : PartialNullHomotopy A M I f} (hS : a.S = b.S) (h : a ≤ b ∨ b ≤ a) : a = b := by
  rcases h with hab | hba
  · exact le_antisymm hab (partialNullHomotopy_le_of_reverse (hS.symm ▸ le_rfl) hab)
  · exact le_antisymm (partialNullHomotopy_le_of_reverse (hS ▸ le_rfl) hba) hba

omit [HasWeakSheafify X.J (Type max u v w)] in
/-- A cochain of degree `-1` on a colimit has commutator `g` with the differentials as soon as
each of its restrictions along the colimit inclusions has commutator the restriction of `g`. -/
theorem delta_eq_ofHom_of_isColimit {J : Type max u v w} [Category.{max u v w} J]
    {D : J ⥤ DifferentialGradedModule.{u, v, max u v w} A} {cc : Cocone D} (hcc : IsColimit cc)
    {I : DifferentialGradedModule.{u, v, max u v w} A} {z : Cochain cc.pt.complex I.complex (-1)}
    {g : cc.pt ⟶ I}
    (h : ∀ j, (Cochain.ofHom (cc.ι.app j).toHomologicalComplex).comp (δ (-1) 0 z)
      (zero_add 0) = Cochain.ofHom (cc.ι.app j ≫ g).toHomologicalComplex) :
    δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : p = q := by omega
  let ev := toCochainComplex.{u, v, max u v w} A ⋙ HomologicalComplex.eval
    (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) p
  have _ : PreservesColimit D ev :=
    (toCochainComplex_eval_preservesColimitsOfShape.{u, v, w} A J p).preservesColimit
  refine (isColimitOfPreserves ev hcc).hom_ext fun j => ?_
  have hh := Cochain.congr_v (h j) p p hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hh
  exact hh.trans (comp_f _ _ p)

omit [HasWeakSheafify X.J (Type max u v w)] [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Precomposing a cochain with commutator `g` by a morphism `φ` gives a cochain with
commutator `φ ≫ g`. -/
theorem delta_ofHom_comp_eq_of_delta_eq {Y Z I : DifferentialGradedModule.{u, v, max u v w} A}
    (φ : Y ⟶ Z) {g : Z ⟶ I} {z : Cochain Z.complex I.complex (-1)}
    (hz : δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex) :
    δ (-1) 0 ((Cochain.ofHom φ.toHomologicalComplex).comp z (zero_add (-1))) =
      Cochain.ofHom (φ ≫ g).toHomologicalComplex := by
  rw [δ_ofHom_comp, hz, ← Cochain.ofHom_comp]
  rfl

/-- Precomposing an action-linear cochain with commutator `g` by `φ` gives an action-linear
cochain with commutator `φ ≫ g`. -/
private lemma exists_actionLinear_delta_ofHom_comp {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {Y Z I : DifferentialGradedModule.{u, v, max u v w} A} (φ : Y ⟶ Z) {g : Z ⟶ I}
    {z : Cochain Z.complex I.complex (-1)} (hz : IsActionLinear A z)
    (hd : δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex) :
    ∃ z' : Cochain Y.complex I.complex (-1),
      IsActionLinear A z' ∧ δ (-1) 0 z' = Cochain.ofHom (φ ≫ g).toHomologicalComplex :=
  ⟨_, actionLinear_comp A _ _ _ (actionLinear_ofHom A φ) hz,
    delta_ofHom_comp_eq_of_delta_eq φ hd⟩

omit [HasWeakSheafify X.J (Type max u v w)] in
/-- The cokernel of a proper subobject has a nonzero underlying complex. -/
theorem not_isZero_cokernel_complex_of_ne_top {M : DifferentialGradedModule.{u, v, max u v w} A}
    {S : Subobject M} (hS : S ≠ ⊤) : ¬ IsZero (cokernel S.arrow).complex := by
  intro h
  have hz : IsZero (cokernel S.arrow) := (IsZero.iff_id_eq_zero _).mpr (Hom.ext fun n => by
    rw [zero_f]
    exact ((HomologicalComplex.eval (SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) n).map_isZero h).eq_of_src _ _)
  have : Epi S.arrow := (Preadditive.epi_iff_isZero_cokernel _).mpr hz
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  exact hS ((Subobject.isIso_arrow_iff_eq_top S).mp inferInstance)

/-! ### Chains have upper bounds -/

private lemma partialNullHomotopy_upperBound_of_monotone
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I} {J : Type max u v w}
    [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (base : J → PartialNullHomotopy A M I f) (hbase : Monotone base) :
    ∃ b : PartialNullHomotopy A M I f, ∀ j, base j ≤ b := by
  let G : J → Subobject M := fun j => (base j).S
  let Ssup : Subobject M := ⨆ j : J, G j
  have hmapLE {i j : J} (g : i ⟶ j) : G i ≤ G j := (hbase (leOfHom g)).1
  let F : J ⥤ MonoOver M :=
    { obj := fun j => MonoOver.mk (G j).arrow
      map := fun {i j} g => MonoOver.homMk (Subobject.ofLE (G i) (G j) (hmapLE g))
        (Subobject.ofLE_arrow _)
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  let cMono : Cocone F :=
    { pt := MonoOver.mk Ssup.arrow
      ι :=
        { app := fun j => MonoOver.homMk (Subobject.ofLE (G j) Ssup (le_iSup G j))
            (Subobject.ofLE_arrow _)
          naturality := fun _ _ _ => Subsingleton.elim _ _ } }
  let cOver := (MonoOver.forget M).mapCocone cMono
  have : Mono cOver.pt.hom := Subobject.arrow_mono Ssup
  have hsup : Subobject.mk cOver.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
    calc Subobject.mk cOver.pt.hom = Ssup := by simp [cOver, cMono, MonoOver.mk_arrow]
      _ = ⨆ j, G j := rfl
      _ = ⨆ j, Subobject.mk (F.obj j).obj.hom := by simp [F, G, MonoOver.mk_arrow]
  have hcColim := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup F cOver hsup
  let D := F ⋙ MonoOver.forget M ⋙ Over.forget M
  let cc := (Over.forget M).mapCocone cOver
  have hcc : IsColimit cc := hcColim
  have hSacyclic : (Ssup : DifferentialGradedModule.{u, v, max u v w} A).complex.Acyclic := by
    have hpres := toCochainComplex_preservesColimitsOfShape.{u, v, w} A J
    exact Stacks.Injectives.acyclic_of_filtered_colimit
      (D ⋙ toCochainComplex.{u, v, max u v w} A)
      ((toCochainComplex.{u, v, max u v w} A).mapCocone cc)
      (isColimitOfPreserves _ hcc) (fun j => (base j).acyclic)
  have hcompat : ∀ ⦃i j⦄ (m : i ⟶ j),
      (Cochain.ofHom (D.map m).toHomologicalComplex).comp (base j).z (zero_add (-1)) =
        (base i).z := fun _ _ m => (hbase (leOfHom m)).2
  obtain ⟨z, hzlin, hzres⟩ := exists_actionLinear_colimit.{u, v, w} A D cc hcc I (-1)
    (fun j => (base j).z) (fun j => (base j).linear) hcompat
  have harrow (j : J) : cc.ι.app j ≫ Ssup.arrow = (G j).arrow :=
    Subobject.ofLE_arrow (le_iSup G j)
  have hboundary : δ (-1) 0 z = Cochain.ofHom (Ssup.arrow ≫ f).toHomologicalComplex :=
    delta_eq_ofHom_of_isColimit hcc fun j => by
      rw [← δ_ofHom_comp, hzres j]
      exact (base j).boundary.trans (congrArg (fun g => Cochain.ofHom (Hom.toHomologicalComplex g))
        ((Category.assoc _ _ f).symm.trans (congrArg (· ≫ f) (harrow j))).symm)
  exact ⟨⟨Ssup, hSacyclic, z, hzlin, hboundary⟩, fun j => ⟨le_iSup G j, hzres j⟩⟩

private lemma partialNullHomotopy_chain_upperBound
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I}
    (c : Set (PartialNullHomotopy A M I f)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ b : PartialNullHomotopy A M I f, ∀ a ∈ c, a ≤ b := by
  classical
  let Rs : Set (Subobject M) := {S | ∃ a, a ∈ c ∧ a.S = S}
  let J₀ := {S : Subobject M // S ∈ Rs}
  let _ : Small.{max u v w} J₀ := inferInstance
  let J := Shrink.{max u v w} J₀
  let e : J₀ ≃ J := equivShrink.{max u v w} J₀
  let SAt : J → Subobject M := fun j => (e.symm j).1
  let base : J → PartialNullHomotopy A M I f := fun j => Classical.choose (e.symm j).2
  have base_mem (j : J) : base j ∈ c := (Classical.choose_spec (e.symm j).2).1
  have base_sub (j : J) : (base j).S = SAt j := (Classical.choose_spec (e.symm j).2).2
  have hbaseLE {i j : J} (hij : SAt i ≤ SAt j) : base i ≤ base j := by
    by_cases heq : base i = base j
    · simp [heq]
    · rcases hc (base_mem i) (base_mem j) heq with h | h
      · exact h
      · refine partialNullHomotopy_le_of_reverse ?_ h
        calc (base i).S = SAt i := base_sub i
          _ ≤ SAt j := hij
          _ = (base j).S := (base_sub j).symm
  have hJne : Nonempty J := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e ⟨x.S, ⟨x, hx, rfl⟩⟩⟩
  have hle {x y : J} (h : base x ≤ base y) : x ≤ y := by
    have hs : SAt x ≤ SAt y := (base_sub x).symm.le.trans (h.1.trans (base_sub y).le)
    have := (equivShrink_le_equivShrink (α := J₀)).mpr hs
    rwa [e.apply_symm_apply, e.apply_symm_apply] at this
  have htot (x y : J) : x ≤ y ∨ y ≤ x := by
    by_cases hxy : x = y
    · exact Or.inl hxy.le
    · have hbase : base x ≠ base y := fun hab => hxy (e.symm.injective (Subtype.ext
        ((base_sub x).symm.trans ((congrArg PartialNullHomotopy.S hab).trans (base_sub y)))))
      exact (hc (base_mem x) (base_mem y) hbase).imp hle hle
  have _ : IsDirected J (· ≤ ·) :=
    ⟨fun x y => (htot x y).elim (fun h => ⟨y, h, le_rfl⟩) (fun h => ⟨x, le_rfl, h⟩)⟩
  have hmono : Monotone base := fun i j hij => hbaseLE
    ((equivShrink_le_equivShrink (α := J₀)).mp (show e (e.symm i) ≤ e (e.symm j) by
      rwa [e.apply_symm_apply, e.apply_symm_apply]))
  obtain ⟨b, hb⟩ := partialNullHomotopy_upperBound_of_monotone base hmono
  refine ⟨b, fun a ha => ?_⟩
  let j : J := e ⟨a.S, ⟨a, ha, rfl⟩⟩
  have hjbase : base j = a := by
    have hj0 : e.symm j = ⟨a.S, ⟨a, ha, rfl⟩⟩ := e.symm_apply_apply _
    have hs : (base j).S = a.S := (base_sub j).trans (congrArg Subtype.val hj0)
    by_cases heq : base j = a
    · exact heq
    · exact partialNullHomotopy_eq_of_same_subobject hs (hc (base_mem j) ha heq)
  exact hjbase ▸ hb j

/-! ### A maximal partial null homotopy is total -/

private lemma partialNullHomotopy_extend {Idx : Type max u v w}
    (Ms : Idx → DifferentialGradedModule.{u, v, max u v w} A)
    (hMs : ∀ s, (Ms s).complex.Acyclic ∧ ¬ IsZero (Ms s).complex)
    (hsmall : ∀ Q : DifferentialGradedModule.{u, v, max u v w} A, Q.complex.Acyclic →
      ¬ IsZero Q.complex → ∃ (s : Idx) (i : Ms s ⟶ Q), Mono i)
    {M I : DifferentialGradedModule.{u, v, max u v w} A} {f : M ⟶ I}
    (hM : M.complex.Acyclic) (hI : GradedInjective I)
    (hv : ∀ (s : Idx) (g : Ms s ⟶ I), ∃ z : Cochain (Ms s).complex I.complex (-1),
      IsActionLinear A z ∧ δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex)
    (P : PartialNullHomotopy A M I f) (htop : P.S ≠ ⊤) :
    ∃ P' : PartialNullHomotopy A M I f, P ≤ P' ∧ P.S < P'.S := by
  classical
  let U := toCochainComplex.{u, v, max u v w} A
  let Q := cokernel P.S.arrow
  let E := ShortComplex.mk P.S.arrow (cokernel.π P.S.arrow) (cokernel.condition _)
  have hE : E.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hQ : Q.complex.Acyclic :=
    Stacks.Injectives.acyclic_right_of_shortExact (E.map U) (hE.map_of_exact U) P.acyclic hM
  obtain ⟨s, k, hk⟩ := hsmall Q hQ (not_isZero_cokernel_complex_of_ne_top htop)
  let T := Subobject.mk k
  let B := (Subobject.pullback (cokernel.π P.S.arrow)).obj T
  obtain ⟨j, hj, hjq, hseq⟩ :=
    Stacks.Injectives.pullbackPreimage_shortExact P.S.arrow T
  let E' := ShortComplex.mk j (Subobject.pullbackπ (cokernel.π P.S.arrow) T) hjq
  have hseq' : E'.ShortExact := hseq
  have hT : (T : DifferentialGradedModule.{u, v, max u v w} A).complex.Acyclic :=
    fun n => ((hMs s).1 n).of_iso (U.mapIso (Subobject.underlyingIso k)).symm
  have hB : (B : DifferentialGradedModule.{u, v, max u v w} A).complex.Acyclic :=
    Stacks.Injectives.acyclic_middle_of_shortExact (E'.map U) (hseq'.map_of_exact U) P.acyclic hT
  have hle : P.S ≤ B := by
    simpa only [Subobject.mk_arrow] using Subobject.mk_le_mk_of_comm j hj
  have hj' : j = Subobject.ofLE P.S B hle :=
    (cancel_mono B.arrow).mp (hj.trans (Subobject.ofLE_arrow _).symm)
  have hstrict : P.S < B := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have : IsIso j := by
      rw [hj']
      exact (inferInstance : IsIso (Subobject.isoOfEq P.S B heq).hom)
    have : Epi E'.g := hseq'.epi_g
    have hzero : E'.g = 0 := by
      apply (cancel_epi j).mp
      show j ≫ Subobject.pullbackπ (cokernel.π P.S.arrow) T = j ≫ 0
      rw [hjq, comp_zero]
    have hz : IsZero (T : DifferentialGradedModule.{u, v, max u v w} A) :=
      IsZero.of_epi_eq_zero _ hzero
    exact (hMs s).2 ((U.map_isZero hz).of_iso (U.mapIso (Subobject.underlyingIso k)).symm)
  have hvT : ∀ g : (T : DifferentialGradedModule.{u, v, max u v w} A) ⟶ I,
      ∃ z : Cochain (T : DifferentialGradedModule.{u, v, max u v w} A).complex I.complex (-1),
        IsActionLinear A z ∧ δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex := by
    intro g
    let ee := Subobject.underlyingIso k
    obtain ⟨z, hz, hd⟩ := hv s (ee.inv ≫ g)
    have := exists_actionLinear_delta_ofHom_comp ee.hom hz hd
    rwa [Iso.hom_inv_id_assoc] at this
  have hd : δ (-1) 0 P.z = Cochain.ofHom (j ≫ (B.arrow ≫ f)).toHomologicalComplex := by
    rw [← Category.assoc, hj]
    exact P.boundary
  obtain ⟨z, hz, hb, hres⟩ := exists_actionLinear_delta_extension.{u, v, max u v w} A E' hseq'
    hI (B.arrow ≫ f) P.z P.linear hd hvT
  exact ⟨⟨B, hB, z, hz, hb⟩, ⟨hle, by simpa only [← hj'] using hres⟩, hstrict⟩

/-! ### The vanishing -/

/-- **Every morphism from an acyclic module into the graded injective is null-homotopic.** Let
`Ms` be a set-indexed family of nonzero acyclic right differential graded modules such that
every nonzero acyclic module receives a monomorphism from a member of the family, and let `I` be
a graded injective module into which every morphism from a member of the family is homotopic to
zero. Then every morphism into `I` from an acyclic right differential graded module is homotopic
to zero. -/
theorem homotopic_zero_of_acyclic_of_detectingFamily {Idx : Type max u v w}
    (Ms : Idx → DifferentialGradedModule.{u, v, max u v w} A)
    (hMs : ∀ s, (Ms s).complex.Acyclic ∧ ¬ IsZero (Ms s).complex)
    (hsmall : ∀ Q : DifferentialGradedModule.{u, v, max u v w} A, Q.complex.Acyclic →
      ¬ IsZero Q.complex → ∃ (s : Idx) (i : Ms s ⟶ Q), Mono i)
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hI : GradedInjective I)
    (hvan : ∀ (s : Idx) (g : Ms s ⟶ I), Homotopic g 0)
    (M : DifferentialGradedModule.{u, v, max u v w} A) (hM : M.complex.Acyclic)
    (f : M ⟶ I) : Homotopic f 0 := by
  classical
  have hbotc : IsZero ((⊥ : Subobject M) :
      DifferentialGradedModule.{u, v, max u v w} A).complex :=
    (toCochainComplex.{u, v, max u v w} A).map_isZero
      (IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero)
  have hacyc : ((⊥ : Subobject M) :
      DifferentialGradedModule.{u, v, max u v w} A).complex.Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (HomologicalComplex.homologyFunctor _ _ n).map_isZero hbotc
  let P₀ : PartialNullHomotopy A M I f :=
    ⟨⊥, hacyc, 0, actionLinear_zero A _ _ _, Cochain.ext _ _ fun p q _ =>
      ((HomologicalComplex.eval (SheafOfModules.{max u v w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) p).map_isZero hbotc).eq_of_src _ _⟩
  have : Nonempty (PartialNullHomotopy A M I f) := ⟨P₀⟩
  obtain ⟨P, hmax⟩ := zorn_le_nonempty (α := PartialNullHomotopy A M I f)
    partialNullHomotopy_chain_upperBound
  have htop : P.S = ⊤ := by
    by_contra htop
    obtain ⟨P', hle, hlt⟩ := partialNullHomotopy_extend Ms hMs hsmall hM hI
      (fun s g => exists_actionLinear_delta_of_homotopic_zero A g (hvan s g)) P htop
    exact (not_le_of_gt hlt) (hmax hle).1
  have : IsIso P.S.arrow := (Subobject.isIso_arrow_iff_eq_top P.S).mpr htop
  obtain ⟨z, hz, hd⟩ := exists_actionLinear_delta_ofHom_comp (inv P.S.arrow) P.linear P.boundary
  exact homotopic_zero_of_actionLinear_delta A f z hz (by simpa using hd)

end SheafOfModules.DifferentialGradedModule

end
