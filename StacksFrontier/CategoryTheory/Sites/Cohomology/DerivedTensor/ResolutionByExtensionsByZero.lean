module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShortComplexDiagramHomology
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.EpiMono
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence

/-!
# Resolutions by sums of extensions by zero on a ringed site

Let `(C, O)` be a ringed site and `G` a cochain complex of `O`-modules. Stacks 077J produces a
compatible system of resolutions of the upper truncations of `G`: an inverse-free ladder of
bounded above complexes `Q_n ⟶ τ_{≤ n+1} G`, each a termwise-epimorphic quasi-isomorphism, whose
terms and whose successive cokernels are direct sums of extensions by zero `j_{U!} O_U` of the
structure sheaves of the slice sites, and whose colimit is quasi-isomorphic to `G`.

The one piece of input beyond the general machinery is that the modules `j_{U!} O_U` *generate*:
every sheaf of `O`-modules is a quotient of a direct sum of them. That is
`exists_epi_from_sum_extensionByZero` below, and it is short, because Stacks 0G1V, in the form
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`, identifies `Hom_O(j_{U!} O_U, M)`
with `M(U)`. Index a direct sum by all pairs `(V, x)` with `x ∈ M(V)`; the component at `(V, x)`
is the morphism corresponding to `x`, and the resulting map is an epimorphism because a morphism
of sheaves of modules is determined by its effect on sections over every object, and every
section occurs as an index.

Given that, the ladder is produced by `CochainComplex.exists_sequence_quasiIso_truncLE` applied
to the class of direct sums of extensions by zero, which is checked to contain zero and to be
closed under binary biproducts; the colimit comparison is a quasi-isomorphism because in each
fixed degree the maps from the truncations are eventually isomorphisms, and filtered colimits of
sheaves of modules are exact.

## Main definitions

* `Stacks.SheafOfModules.IsSumOfExtensionByZeroStructureSheaves`: being isomorphic to a direct
  sum of extensions by zero of the structure sheaves of slice sites.
* `Stacks.SheafOfModules.ResolutionByDirectSumsExtensionsByZero`: the whole compatible ladder,
  with its truncation maps, its quasi-isomorphisms, its termwise epimorphisms, the sum property
  of its terms and of its successive cokernels, and its colimit comparison.

## Main results

* `Stacks.SheafOfModules.exists_epi_from_sum_extensionByZero`: every sheaf of modules is a
  quotient of a direct sum of extensions by zero of the structure sheaves of slices. This is
  Stacks 03EW (3); it is proved here from Stacks 0G1V rather than cited, see the implementation
  notes.
* `Stacks.SheafOfModules.exists_resolutionByDirectSumsExtensionsByZero`: the ladder exists for
  every complex.

## Implementation notes

The first natural-number index corresponds to degree bound one in the source, so that
`system.obj n` resolves `τ_{≤ n+1} G`. The transition between truncations is characterized by
its composition with the canonical map to the original complex, and the colimit comparison by
its composition with each colimit injection; quotients are expressed as epimorphisms.

`exists_epi_from_sum_extensionByZero` is Stacks 03EW part (3) at the ringed-site spelling
`SheafOfModules.pullback (𝟙 (O.over U))` applied to `SheafOfModules.unit`, which is the object
the rest of this file is about. Its content is the adjunction bijection of Stacks 0G1V together
with the choice of index set and the check that a map hit on all sections is epi.

The source's proof is one induction. Here the generation lemma is applied directly rather than
through a comparison of two spellings of `j_{U!} O_U`; with that comparison in place the
construction did not elaborate within the default heartbeat budget.

## References

* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.SheafOfModules


variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-- **Stacks 03EW (3)**, in the form this file needs: every sheaf of modules on a ringed site
receives an epimorphism from a direct sum of extensions by zero of the structure sheaves of the
slices. -/
theorem exists_epi_from_sum_extensionByZero
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (ι : Type u) (U : ι → X.C)
      (p : (∐ fun i : ι =>
        (SheafOfModules.pullback.{u} (F := Over.forget (U i))
          (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))).obj
            (SheafOfModules.unit
              (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))) ⟶ M), Epi p := by
  classical
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let ι : Type u := Σ V : X.C, (M.val.obj (Opposite.op V) : Type u)
  let U : ι → X.C := fun i => i.1
  refine ⟨ι, U, Sigma.desc fun i =>
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J R (U i) M).symm i.2, ⟨?_⟩⟩
  intro N f g h
  have hs (V : X.C) (x : M.val.obj (Opposite.op V)) :
      f.val.app (Opposite.op V) x = g.val.app (Opposite.op V) x := by
    have hh := congrArg (fun k => Sigma.ι
      (fun i : ι => (SheafOfModules.pullback.{u} (F := Over.forget (U i))
        (𝟙 (R.over (U i)))).obj (SheafOfModules.unit (R.over (U i)))) ⟨V, x⟩ ≫ k) h
    simp only [← Category.assoc, Sigma.ι_comp_desc] at hh
    have he := congrArg
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J R V N) hh
    rwa [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply] at he
  apply (SheafOfModules.toSheaf R).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Y
  ext x
  exact hs Y.unop x

private lemma isIso_homologyMap_of_eq_comp_ιTruncLE
    {A : Type v} [Category.{u} A] [Abelian A]
    {K P : CochainComplex A ℤ} {m : ℤ} {φ : P ⟶ K} {f : P ⟶ K.truncLE m} (hf : QuasiIso f)
    (hφ : φ = f ≫ K.ιTruncLE m) {i : ℤ} (hi : i ≤ m) :
    IsIso (HomologicalComplex.homologyMap φ i) := by
  have h₁ := (quasiIso_iff f).1 hf i
  have h₂ := CochainComplex.quasiIsoAt_ιTruncLE K m i hi
  rw [quasiIsoAt_iff_isIso_homologyMap] at h₁ h₂
  rw [hφ, HomologicalComplex.homologyMap_comp]
  exact IsIso.comp_isIso' h₁ h₂

private lemma quasiIso_of_isColimit_of_quasiIso_truncLE_succ
    {A : Type v} [Category.{u} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {K : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ}
    {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (f : ∀ n : ℕ, Q n ⟶ K.truncLE ((n : ℤ) + 1))
    (hf : ∀ n, QuasiIso (f n))
    {c : Cocone (Functor.ofSequence g)} (hc : IsColimit c) (α : c.pt ⟶ K)
    (hα : ∀ n : ℕ, c.ι.app n ≫ α = f n ≫ K.ιTruncLE ((n : ℤ) + 1)) :
    QuasiIso α := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  have hH : PreservesColimitsOfShape ℕ H :=
    Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := A)
      (ComplexShape.up ℤ) i
  have hiso : ∀ n : ℕ, i ≤ (n : ℤ) + 1 → IsIso (H.map (c.ι.app n ≫ α)) :=
    fun n hn => isIso_homologyMap_of_eq_comp_ιTruncLE (hf n) (hα n) hn
  let n₀ := i.toNat
  have hn₀ : i ≤ (n₀ : ℤ) + 1 := by
    have h := Int.self_le_toNat i
    omega
  let v : Cocone (Functor.ofSequence g ⋙ H) := Cocone.mk (H.obj K)
    { app := fun n => H.map (c.ι.app n ≫ α)
      naturality := fun j j' φ => by
        dsimp
        rw [Category.comp_id, ← H.map_comp, ← Category.assoc, c.w φ] }
  have hv₀ : IsIso (v.ι.app n₀) := hiso n₀ hn₀
  have hev : (Functor.ofSequence g ⋙ H).IsEventuallyConstantFrom n₀ := by
    intro j φ
    have : IsIso (v.ι.app j) := hiso j (by
      have := leOfHom φ
      omega)
    exact IsIso.of_isIso_fac_right (v.w φ)
  have hv : IsColimit v := hev.isColimitOfIsIso v
  have hHc : IsColimit (H.mapCocone c) := isColimitOfPreserves H hc
  have heq : H.map α = (hHc.coconePointUniqueUpToIso hv).hom := hHc.hom_ext fun n => by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (H.map_comp _ _).symm
  change IsIso (H.map α)
  rw [heq]
  infer_instance

private noncomputable def truncationTransition
    {A : Type v} [Category.{u} A] [Abelian A]
    (G : CochainComplex A ℤ) (n : ℕ) :
    G.truncLE ((n : ℤ) + 1) ⟶ G.truncLE ((n : ℤ) + 2) :=
  haveI : (G.truncLE ((n : ℤ) + 1)).IsStrictlyLE ((n : ℤ) + 2) :=
    CochainComplex.isStrictlyLE_of_le _ ((n : ℤ) + 1) _ (by omega)
  inv ((G.truncLE ((n : ℤ) + 1)).ιTruncLE ((n : ℤ) + 2)) ≫
    CochainComplex.truncLEMap (G.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2)

private lemma truncationTransition_comp_ιTruncLE
    {A : Type v} [Category.{u} A] [Abelian A]
    (G : CochainComplex A ℤ) (n : ℕ) :
    truncationTransition G n ≫ G.ιTruncLE ((n : ℤ) + 2) = G.ιTruncLE ((n : ℤ) + 1) := by
  dsimp [truncationTransition]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- A direct sum of extensions by zero of the structure sheaves on slices of a site. -/
def IsSumOfExtensionByZeroStructureSheaves
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) : Prop :=
  ∃ (ι : Type u) (U : ι → X.C),
    Nonempty
      ((∐ fun i : ι =>
        (SheafOfModules.pullback.{u}
          (F := Over.forget (U i))
          (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))).obj
            (SheafOfModules.unit (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over (U i)))) ≅ M)

/-- The extension by zero of the structure sheaf of the slice at `U i`. -/
private abbrev extensionByZeroUnit {ι : Type u} (U : ι → X.C) :
    ι → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := fun i =>
  (SheafOfModules.pullback.{u} (F := Over.forget (U i))
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (U i)))).obj
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (U i)))

/-- The zero module is a direct sum of extensions by zero, namely the empty one. -/
theorem isSumOfExtensionByZeroStructureSheaves_containsZero :
    ObjectProperty.ContainsZero (IsSumOfExtensionByZeroStructureSheaves X) := by
  let U₀ : PEmpty.{u + 1} → X.C := fun i => nomatch i
  exact ⟨∐ extensionByZeroUnit X U₀,
    (Stacks.Cohomology.isInitial_coproduct_of_isEmpty _).isZero, PEmpty.{u + 1}, U₀,
    ⟨Iso.refl _⟩⟩

/-- Direct sums of extensions by zero are closed under binary biproducts. -/
theorem isSumOfExtensionByZeroStructureSheaves_biprod
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsSumOfExtensionByZeroStructureSheaves X M)
    (hN : IsSumOfExtensionByZeroStructureSheaves X N) :
    IsSumOfExtensionByZeroStructureSheaves X (M ⊞ N) := by
  obtain ⟨ι, U, ⟨eM⟩⟩ := hM
  obtain ⟨κ, V, ⟨eN⟩⟩ := hN
  let S : Sum ι κ → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := fun
    | Sum.inl i => extensionByZeroUnit X U i
    | Sum.inr j => extensionByZeroUnit X V j
  let e : Discrete.functor S ≅ Discrete.functor (extensionByZeroUnit X (Sum.elim U V)) :=
    Discrete.natIso fun ⟨i⟩ => by cases i <;> exact Iso.refl _
  exact ⟨Sum ι κ, Sum.elim U V, ⟨(HasColimit.isoOfNatIso e).symm ≪≫
    Stacks.Cohomology.coproductSumIso S ≪≫ biprod.mapIso eM eN⟩⟩

/-- Every sheaf of modules receives an epimorphism from a direct sum of extensions by zero. -/
theorem exists_epi_of_isSumOfExtensionByZeroStructureSheaves
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (_ : IsSumOfExtensionByZeroStructureSheaves X N) (p : N ⟶ M), Epi p := by
  obtain ⟨ι, U, p, hp⟩ := exists_epi_from_sum_extensionByZero X M
  exact ⟨_, ⟨ι, U, ⟨Iso.refl _⟩⟩, p, hp⟩

/-- The cokernel of the inclusion of a summand with complement a direct sum of extensions by zero
is a direct sum of extensions by zero. -/
theorem isSumOfExtensionByZeroStructureSheaves_cokernel
    {M N C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {i : M ⟶ N}
    (hC : IsSumOfExtensionByZeroStructureSheaves X C) (e : N ≅ M ⊞ C)
    (he : i ≫ e.hom = biprod.inl) :
    IsSumOfExtensionByZeroStructureSheaves X (cokernel i) := by
  obtain ⟨ι, U, ⟨eC⟩⟩ := hC
  exact ⟨ι, U, ⟨eC ≪≫
    (cokernel.mapIso i biprod.inl (Iso.refl _) e he ≪≫ cokernelBiprodInlIso).symm⟩⟩

/-- A compatible ladder resolving the upper truncations of a complex by sums of
extensions by zero, with its induced comparison from the colimit. -/
structure ResolutionByDirectSumsExtensionsByZero
    (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) where
  /-- The direct system of complexes `Q_n`. -/
  system : ℕ ⥤ CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ
  /-- The map `Q_n ⟶ τ_{≤ n+1} G`. -/
  toTruncation (n : ℕ) : system.obj n ⟶ G.truncLE ((n : ℤ) + 1)
  /-- The map `τ_{≤ n+1} G ⟶ τ_{≤ n+2} G` between successive truncations. -/
  truncationTransition (n : ℕ) :
    G.truncLE ((n : ℤ) + 1) ⟶ G.truncLE ((n : ℤ) + 2)
  /-- The transition between truncations commutes with the maps to `G`. -/
  truncationTransition_ι (n : ℕ) :
    truncationTransition n ≫ G.ιTruncLE ((n : ℤ) + 2) =
      G.ιTruncLE ((n : ℤ) + 1)
  /-- The transition maps of the system are compatible with the maps to the truncations. -/
  square (n : ℕ) :
    system.map (homOfLE (Nat.le_succ n)) ≫ toTruncation (n + 1) =
      toTruncation n ≫ truncationTransition n
  /-- Each map `Q_n ⟶ τ_{≤ n+1} G` is a quasi-isomorphism. -/
  quasiIso (n : ℕ) : QuasiIso (toTruncation n)
  /-- Each map `Q_n ⟶ τ_{≤ n+1} G` is an epimorphism in every degree. -/
  epi_f (n : ℕ) (i : ℤ) : Epi ((toTruncation n).f i)
  /-- Each complex `Q_n` is bounded above. -/
  boundedAbove (n : ℕ) : ∃ a : ℤ, (system.obj n).IsStrictlyLE a
  /-- Every term of every `Q_n` is a direct sum of extensions by zero of structure sheaves. -/
  term_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves X ((system.obj n).X i)
  /-- In every degree, each transition map `Q_n ⟶ Q_{n+1}` is a split monomorphism. -/
  transition_splitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((system.map (homOfLE (Nat.le_succ n))).f i)
  /-- In every degree, the cokernel of each transition map `Q_n ⟶ Q_{n+1}` is a direct sum of
  extensions by zero of structure sheaves. -/
  transition_cokernel_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves X
      (cokernel ((system.map (homOfLE (Nat.le_succ n))).f i))
  /-- The comparison map from the colimit of the system to `G`. -/
  colimitComparison : colimit system ⟶ G
  /-- The comparison map restricts on `Q_n` to the composite `Q_n ⟶ τ_{≤ n+1} G ⟶ G`. -/
  colimitComparison_fac (n : ℕ) :
    colimit.ι system n ≫ colimitComparison =
      toTruncation n ≫ G.ιTruncLE ((n : ℤ) + 1)
  /-- The comparison map from the colimit to `G` is a quasi-isomorphism. -/
  colimit_quasiIso : QuasiIso colimitComparison

private lemma shifted_truncation_ladder
    {A : Type v} [Category.{u} A] [Abelian A]
    {G : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ}
    {f : ∀ n : ℕ, Q n ⟶ G.truncLE ((n : ℕ) : ℤ)}
    {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (hladder : ∀ n : ℕ,
      g n ≫ f (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        f n ≫ G.ιTruncLE ((n : ℕ) : ℤ))
    (n : ℕ) :
    (g (n + 1) ≫ f (n + 1 + 1)) ≫
        G.ιTruncLE (((n + 1 + 1 : ℕ) : ℤ)) =
      f (n + 1) ≫ G.ιTruncLE (((n + 1 : ℕ) : ℤ)) := by
  simpa only [Category.assoc] using hladder (n + 1)

private lemma ofSequence_map_comp_eq_comp_truncationTransition
    {A : Type v} [Category.{u} A] [Abelian A]
    {G : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ}
    (f : ∀ n : ℕ, Q n ⟶ G.truncLE ((n : ℤ) + 1)) (g : ∀ n : ℕ, Q n ⟶ Q (n + 1))
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ G.ιTruncLE (((n + 1 : ℕ) : ℤ) + 1) =
      f n ≫ G.ιTruncLE ((n : ℤ) + 1)) (n : ℕ) :
    (Functor.ofSequence g).map (homOfLE (Nat.le_succ n)) ≫ f (n + 1) =
      f n ≫ truncationTransition G n := by
  apply (cancel_mono (G.ιTruncLE ((n : ℤ) + 2))).1
  have hstep : (Functor.ofSequence g).map (homOfLE (Nat.le_succ n)) ≫ f (n + 1) =
      g n ≫ f (n + 1) := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    rfl
  exact (hstep =≫ _).trans <| (Category.assoc _ _ _).trans <| (hladder n).trans <|
    (f n ≫= truncationTransition_comp_ιTruncLE G n).symm.trans (Category.assoc _ _ _).symm

private lemma exists_colimit_desc_quasiIso
    {A : Type v} [Category.{u} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {G : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ} {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (f : ∀ n : ℕ, Q n ⟶ G.truncLE ((n : ℤ) + 1)) (hf : ∀ n, QuasiIso (f n))
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ G.ιTruncLE (((n + 1 : ℕ) : ℤ) + 1) =
      f n ≫ G.ιTruncLE ((n : ℤ) + 1)) :
    ∃ α : colimit (Functor.ofSequence g) ⟶ G,
      (∀ n : ℕ, colimit.ι (Functor.ofSequence g) n ≫ α = f n ≫ G.ιTruncLE ((n : ℤ) + 1)) ∧
        QuasiIso α := by
  let s : Cocone (Functor.ofSequence g) := Cocone.mk G
    (NatTrans.ofSequence (fun n => f n ≫ G.ιTruncLE ((n : ℤ) + 1)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  exact ⟨colimit.desc _ s, fun n => colimit.ι_desc s n,
    quasiIso_of_isColimit_of_quasiIso_truncLE_succ f hf (colimit.isColimit _) _
      fun n => colimit.ι_desc s n⟩

/-- A complex of modules on a ringed site admits a compatible resolution by direct
sums of extensions by zero, whose colimit is quasi-isomorphic to the complex. -/
@[stacks 077J]
theorem exists_resolutionByDirectSumsExtensionsByZero
    (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    Nonempty (ResolutionByDirectSumsExtensionsByZero X G) := by
  classical
  let A := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let P : ObjectProperty A := IsSumOfExtensionByZeroStructureSheaves X
  have : P.ContainsZero := isSumOfExtensionByZeroStructureSheaves_containsZero X
  obtain ⟨Q, f, g, hq, hepi, hLE, hP, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P
      (fun _ _ => isSumOfExtensionByZeroStructureSheaves_biprod X)
      (exists_epi_of_isSumOfExtensionByZeroStructureSheaves X) G
  let Q' : ℕ → CochainComplex A ℤ := fun n => Q (n + 1)
  let f' : ∀ n : ℕ, Q' n ⟶ G.truncLE ((n : ℤ) + 1) := fun n => f (n + 1)
  let g' : ∀ n : ℕ, Q' n ⟶ Q' (n + 1) := fun n => g (n + 1)
  have hladder' : ∀ n : ℕ, g' n ≫ f' (n + 1) ≫ G.ιTruncLE (((n + 1 : ℕ) : ℤ) + 1) =
      f' n ≫ G.ιTruncLE ((n : ℤ) + 1) := fun n => by
    simpa only [Q', g', f', Category.assoc, Int.natCast_add, Int.natCast_one, add_assoc] using
      shifted_truncation_ladder hladder n
  have := Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  obtain ⟨α, hα, hαq⟩ := exists_colimit_desc_quasiIso f' (fun n => hq (n + 1)) hladder'
  refine ⟨{
    system := Functor.ofSequence g'
    toTruncation := f'
    truncationTransition := truncationTransition G
    truncationTransition_ι := truncationTransition_comp_ιTruncLE G
    square := ofSequence_map_comp_eq_comp_truncationTransition f' g' hladder'
    quasiIso := fun n => hq (n + 1)
    epi_f := fun n i => hepi (n + 1) i
    boundedAbove := fun n => ⟨(n : ℤ) + 2, by
      have : (Q (n + 1)).IsStrictlyLE ((n + 1 : ℕ) : ℤ) := hLE (n + 1)
      exact CochainComplex.isStrictlyLE_of_le (Q (n + 1)) ((n + 1 : ℕ) : ℤ)
        ((n : ℤ) + 2) (by omega)⟩
    term_isSum := fun n i => hP (n + 1) i
    transition_splitMono := ?_
    transition_cokernel_isSum := ?_
    colimitComparison := α
    colimitComparison_fac := hα
    colimit_quasiIso := hαq
  }⟩
  · intro n i
    rw [Functor.ofSequence_map_homOfLE_succ]
    obtain ⟨C, -, e, he⟩ := hsplit (n + 1) i
    refine IsSplitMono.mk' ⟨e.hom ≫ biprod.fst, ?_⟩
    change (g (n + 1)).f i ≫ e.hom ≫ biprod.fst = 𝟙 ((Q (n + 1)).X i)
    rw [← Category.assoc, he]
    simp
  · intro n i
    rw [Functor.ofSequence_map_homOfLE_succ]
    obtain ⟨C, hC, e, he⟩ := hsplit (n + 1) i
    exact isSumOfExtensionByZeroStructureSheaves_cokernel X hC e he

end Stacks.SheafOfModules

end
