module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShortComplexDiagramHomology
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatCover
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Resolutions by sums of extensions by zero on a ringed space

Let `(X, O)` be a ringed space and let `G` be a cochain complex of `O`-modules. Stacks 079T
produces a compatible system of resolutions of the upper truncations of `G`: a ladder of
bounded above complexes `Q_n ⟶ τ_{≤ n+1} G`, each a termwise-epimorphic quasi-isomorphism,
whose terms and whose successive cokernels are direct sums of extensions by zero `j_{U!} O_U`
of the structure sheaves of open subspaces, with transition maps that are termwise split
injective, and whose colimit maps quasi-isomorphically to `G`.

## Main definitions

* `IsSumOfExtensionByZeroStructureSheaves`: being isomorphic to a direct sum of modules
  `j_{U!} O_U`.
* `ResolutionByDirectSumsExtensionsByZero`: the whole ladder, with its truncation maps, its
  quasi-isomorphisms, its termwise epimorphisms, the sum property of its terms and of its
  successive cokernels, and its colimit comparison.

## Main results

* `exists_resolutionByDirectSumsExtensionsByZero`: the ladder exists for every complex.

## Implementation notes

The natural-number index `n` represents the source's index `n + 1`, so that `system.obj n`
resolves `τ_{≤ n+1} G`. The lower row is the canonical truncation system, whose transition is
characterized by compatibility with the canonical inclusions into `G`; the comparison from the
colimit is included in the data together with its values on the colimit injections, which pins
it down as the induced map. "Surjective" is expressed categorically as `Epi`.

The input beyond the general machinery is Stacks 05NI (1),
`Stacks.SheafOfModules.exists_epi_from_coproduct_jShriek_unit`: every sheaf of modules is a
quotient of a direct sum of the `j_{U!} O_U`. Given that, the ladder comes from
`CochainComplex.exists_sequence_quasiIso_truncLE` applied to the class of such direct sums,
which is checked here to contain zero and to be closed under binary biproducts, and the
colimit comparison is a quasi-isomorphism because in each fixed degree the maps from the
truncations are eventually isomorphisms and filtered colimits of sheaves of modules are exact
(Stacks 03DB).

This is the ringed-space form of the statement. The library also carries the ringed-site form,
`Stacks.SheafOfModules.exists_resolutionByDirectSumsExtensionsByZero` (Stacks 077J, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionByExtensionsByZero`), with
the same ladder and the same clauses. The two are not instances of one another as stated: there
the extension by zero is `SheafOfModules.pullback (𝟙 (ringSheaf.over U))` along the slice site
`X.C/U`, here it is `ExtensionByZeroModules.jShriek U O`, the extension by zero along the open
immersion `U → X`, whose source site is `Opens U`. Those two sites are equivalent but not equal,
so deducing one statement from the other needs a transport along that equivalence, which is not
available in the library.

That colimits of shape `ℕ` commute with degreewise homology is cited from
`Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor`, where it is stated once for an
abelian category with exact sequential colimits; Mathlib itself has no such instance.

## References

* [Stacks Project, Tag 079T](https://stacks.math.columbia.edu/tag/079T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Cohomology.SpaceResolutionByExtensionsByZero

variable {X : TopCat.{u}}
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- An `O`-module is a direct sum of extensions by zero `j_{U!} O_U`, for open
subspaces `U` of `X`. -/
def IsSumOfExtensionByZeroStructureSheaves (M : SheafOfModules.{u} O) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X),
    Nonempty
      ((∐ fun i : ι =>
          (ExtensionByZeroModules.jShriek (U i) O).obj
            (SheafOfModules.unit (ExtensionByZeroModules.resRing (U i) O))) ≅ M)

/-- A compatible system of bounded-above resolutions of the canonical truncations of
`G`, with terms and successive cokernels built from sums of extensions by zero. -/
structure ResolutionByDirectSumsExtensionsByZero
    (G : CochainComplex (SheafOfModules.{u} O) ℤ) where
  /-- The direct system of resolving complexes. -/
  system : ℕ ⥤ CochainComplex (SheafOfModules.{u} O) ℤ
  /-- The vertical map from the `n`th resolving complex to `τ_{≤ n+1}G`. -/
  toTruncation (n : ℕ) : system.obj n ⟶ G.truncLE ((n : ℤ) + 1)
  /-- The canonical map `τ_{≤ n+1}G ⟶ τ_{≤ n+2}G`. -/
  truncationTransition (n : ℕ) :
    G.truncLE ((n : ℤ) + 1) ⟶ G.truncLE ((n : ℤ) + 2)
  /-- The truncation transition is the canonical one, as characterized by its composite
  with the inclusion into `G`. -/
  truncationTransition_ι (n : ℕ) :
    truncationTransition n ≫ G.ιTruncLE ((n : ℤ) + 2) =
      G.ιTruncLE ((n : ℤ) + 1)
  /-- The squares between the resolution system and the truncation system commute. -/
  square (n : ℕ) :
    system.map (homOfLE (Nat.le_succ n)) ≫ toTruncation (n + 1) =
      toTruncation n ≫ truncationTransition n
  /-- Every vertical map is a quasi-isomorphism. -/
  quasiIso (n : ℕ) : QuasiIso (toTruncation n)
  /-- Every vertical map is termwise surjective. -/
  epi_f (n : ℕ) (i : ℤ) : Epi ((toTruncation n).f i)
  /-- Each resolving complex is bounded above. -/
  boundedAbove (n : ℕ) : ∃ a : ℤ, (system.obj n).IsStrictlyLE a
  /-- Every term of every resolving complex is a direct sum of modules `j_{U!}O_U`. -/
  term_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves O ((system.obj n).X i)
  /-- Every transition map is a split injection in each degree. -/
  transition_splitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((system.map (homOfLE (Nat.le_succ n))).f i)
  /-- The termwise cokernel of every transition is again a direct sum of modules
  `j_{U!}O_U`. -/
  transition_cokernel_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves O
      (cokernel ((system.map (homOfLE (Nat.le_succ n))).f i))
  /-- The map from the colimit of the resolving complexes to `G`. -/
  colimitComparison : colimit system ⟶ G
  /-- The colimit comparison is induced by the composites through the truncations. -/
  colimitComparison_fac (n : ℕ) :
    colimit.ι system n ≫ colimitComparison =
      toTruncation n ≫ G.ιTruncLE ((n : ℤ) + 1)
  /-- The induced map from the colimit to the original complex is a quasi-isomorphism. -/
  colimit_quasiIso : QuasiIso colimitComparison

private lemma isIso_homologyFunctor_map_comp_ιTruncLE {A : Type*} [Category A] [Abelian A]
    {K Q : CochainComplex A ℤ} {a : ℤ}
    (f : Q ⟶ K.truncLE a) (hf : QuasiIso f) {i : ℤ} (hi : i ≤ a) :
    IsIso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).map
      (f ≫ K.ιTruncLE a)) := by
  have h₁ := (quasiIso_iff f).1 hf i
  have h₂ := CochainComplex.quasiIsoAt_ιTruncLE K a i hi
  rw [quasiIsoAt_iff_isIso_homologyMap] at h₁ h₂
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' h₁ h₂

private lemma quasiIso_colimit_comparison
    {A : Type*} [Category A] [Abelian A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] {K : CochainComplex A ℤ}
    {Q : ℕ → CochainComplex A ℤ} {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (f : ∀ n : ℕ, Q n ⟶ K.truncLE ((n + 1 : ℕ) : ℤ))
    (hf : ∀ n, QuasiIso (f n)) {c : Cocone (Functor.ofSequence g)}
    (hc : IsColimit c) (α : c.pt ⟶ K)
    (hα : ∀ n : ℕ, c.ι.app n ≫ α = f n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)) :
    QuasiIso α := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  set H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := A) (J := ℕ) (ComplexShape.up ℤ) i
  have hiso (n : ℕ) (hi : i ≤ ((n + 1 : ℕ) : ℤ)) : IsIso (H.map (c.ι.app n ≫ α)) := by
    rw [hα n]
    exact isIso_homologyFunctor_map_comp_ιTruncLE (f n) (hf n) hi
  let n₀ : ℕ := i.toNat
  have hn₀le : i ≤ ((n₀ + 1 : ℕ) : ℤ) := by omega
  have hev : (Functor.ofSequence g ⋙ H).IsEventuallyConstantFrom n₀ := by
    intro j φ
    have hj : i ≤ ((j + 1 : ℕ) : ℤ) := by
      have := leOfHom φ
      omega
    have h₁ := hiso j hj
    have h₂ := hiso n₀ hn₀le
    have w : (Functor.ofSequence g ⋙ H).map φ ≫ H.map (c.ι.app j ≫ α) =
        H.map (c.ι.app n₀ ≫ α) := by
      rw [Functor.comp_map, ← H.map_comp, ← Category.assoc, c.w φ]
    exact IsIso.of_isIso_fac_right w
  let u : Cocone (Functor.ofSequence g ⋙ H) :=
    Cocone.mk (H.obj K)
      { app := fun n => H.map (c.ι.app n ≫ α)
        naturality := fun j j' φ => by
          dsimp
          rw [Category.comp_id, ← H.map_comp, ← Category.assoc, c.w φ] }
  have hu₀ : IsIso (u.ι.app n₀) := hiso n₀ hn₀le
  have hu : IsColimit u := hev.isColimitOfIsIso u
  have hHc : IsColimit (H.mapCocone c) := isColimitOfPreserves H hc
  have heq : H.map α = (hHc.coconePointUniqueUpToIso hu).hom := by
    refine hHc.hom_ext fun n => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (H.map_comp _ _).symm
  show IsIso (H.map α)
  rw [heq]
  infer_instance

/-- The canonical map `τ_{≤ n+1} K ⟶ τ_{≤ n+2} K` between canonical truncations. -/
noncomputable def truncLESucc {A : Type*} [Category A] [Abelian A] (K : CochainComplex A ℤ)
    (n : ℕ) :
    K.truncLE ((n + 1 : ℕ) : ℤ) ⟶ K.truncLE ((n + 2 : ℕ) : ℤ) :=
  haveI : (K.truncLE ((n + 1 : ℕ) : ℤ)).IsStrictlyLE ((n + 2 : ℕ) : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ ((n + 1 : ℕ) : ℤ) _ (by omega)
  inv ((K.truncLE ((n + 1 : ℕ) : ℤ)).ιTruncLE ((n + 2 : ℕ) : ℤ)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE ((n + 1 : ℕ) : ℤ)) ((n + 2 : ℕ) : ℤ)

/-- The map `truncLESucc` is compatible with the inclusions into `K`. -/
lemma truncLESucc_ι {A : Type*} [Category A] [Abelian A] (K : CochainComplex A ℤ) (n : ℕ) :
    truncLESucc K n ≫ K.ιTruncLE ((n + 2 : ℕ) : ℤ) = K.ιTruncLE ((n + 1 : ℕ) : ℤ) := by
  dsimp only [truncLESucc]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- A square over the inclusions into `K` commutes over `truncLESucc`. -/
lemma comp_eq_comp_truncLESucc {A : Type*} [Category A] [Abelian A]
    {K Q₁ Q₂ : CochainComplex A ℤ} (n : ℕ) (g : Q₁ ⟶ Q₂)
    (f₁ : Q₁ ⟶ K.truncLE ((n + 1 : ℕ) : ℤ)) (f₂ : Q₂ ⟶ K.truncLE ((n + 2 : ℕ) : ℤ))
    (h : g ≫ f₂ ≫ K.ιTruncLE ((n + 2 : ℕ) : ℤ) = f₁ ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)) :
    g ≫ f₂ = f₁ ≫ truncLESucc K n := by
  have : Mono (K.ιTruncLE ((n + 2 : ℕ) : ℤ)) := by
    apply HomologicalComplex.mono_of_mono_f _
    intro i
    dsimp [CochainComplex.ιTruncLE]
    infer_instance
  apply (cancel_mono (K.ιTruncLE ((n + 2 : ℕ) : ℤ))).1
  rw [Category.assoc, Category.assoc, truncLESucc_ι, h]

/-- A sequence of quasi-isomorphisms onto the truncations `τ_{≤ n+1} K`, compatible with the
inclusions into `K`, induces a quasi-isomorphism from its colimit to `K`. -/
lemma exists_quasiIso_colimit_ofSequence {A : Type*} [Category A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {K : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ} (g : ∀ n : ℕ, Q n ⟶ Q (n + 1))
    (f : ∀ n : ℕ, Q n ⟶ K.truncLE ((n + 1 : ℕ) : ℤ)) (hf : ∀ n, QuasiIso (f n))
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 2 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)) :
    ∃ α : colimit (Functor.ofSequence g) ⟶ K,
      (∀ n : ℕ, colimit.ι (Functor.ofSequence g) n ≫ α =
        f n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)) ∧ QuasiIso α := by
  let s : Cocone (Functor.ofSequence g) := Cocone.mk K
    (NatTrans.ofSequence (fun n => f n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)) fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm)
  exact ⟨colimit.desc _ s, fun n => colimit.ι_desc s n,
    quasiIso_colimit_comparison f hf (colimit.isColimit _) _ fun n => colimit.ι_desc s n⟩

/-- A coproduct indexed by `I ⊕ J` is the biproduct of the coproducts over `I` and over `J`. -/
noncomputable def sigmaSumIsoBiprod {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {I J : Type*} (W : I ⊕ J → C) [HasCoproduct W]
    [HasCoproduct fun i => W (Sum.inl i)] [HasCoproduct fun j => W (Sum.inr j)] :
    ∐ W ≅ (∐ fun i => W (Sum.inl i)) ⊞ ∐ fun j => W (Sum.inr j) where
  hom := Sigma.desc fun
    | .inl i => Sigma.ι (fun i => W (Sum.inl i)) i ≫ biprod.inl
    | .inr j => Sigma.ι (fun j => W (Sum.inr j)) j ≫ biprod.inr
  inv := biprod.desc (Sigma.desc fun i => Sigma.ι W (Sum.inl i))
    (Sigma.desc fun j => Sigma.ι W (Sum.inr j))
  hom_inv_id := Sigma.hom_ext _ _ fun
    | .inl _ => by simp
    | .inr _ => by simp
  inv_hom_id := biprod.hom_ext' _ _ (Sigma.hom_ext _ _ fun _ => by simp)
    (Sigma.hom_ext _ _ fun _ => by simp)

/-- The zero module is a direct sum of extensions by zero, over the empty index type. -/
lemma exists_isZero_isSumOfExtensionByZeroStructureSheaves :
    ∃ Z : SheafOfModules.{u} O, IsZero Z ∧ IsSumOfExtensionByZeroStructureSheaves O Z := by
  let F : PEmpty.{u + 1} → SheafOfModules.{u} O := fun i =>
    (ExtensionByZeroModules.jShriek (PEmpty.elim i : Opens X) O).obj
      (SheafOfModules.unit (ExtensionByZeroModules.resRing (PEmpty.elim i : Opens X) O))
  have (Y : SheafOfModules.{u} O) : Unique ((∐ F) ⟶ Y) :=
    { default := Sigma.desc fun i => i.elim
      uniq := fun _ => Sigma.hom_ext _ _ fun i => i.elim }
  exact ⟨∐ F, (IsInitial.ofUnique _).isZero, PEmpty, PEmpty.elim, ⟨Iso.refl _⟩⟩

/-- A biproduct of direct sums of extensions by zero is again one. -/
lemma IsSumOfExtensionByZeroStructureSheaves.biprod [HasZeroMorphisms (SheafOfModules.{u} O)]
    [HasBinaryBiproducts (SheafOfModules.{u} O)] {M N : SheafOfModules.{u} O}
    (hM : IsSumOfExtensionByZeroStructureSheaves O M)
    (hN : IsSumOfExtensionByZeroStructureSheaves O N) :
    IsSumOfExtensionByZeroStructureSheaves O (M ⊞ N) := by
  obtain ⟨I, U, ⟨eM⟩⟩ := hM
  obtain ⟨J, V, ⟨eN⟩⟩ := hN
  exact ⟨I ⊕ J, Sum.elim U V, ⟨sigmaSumIsoBiprod _ ≪≫ biprod.mapIso eM eN⟩⟩

/-- Every `O`-module is a quotient of a direct sum of extensions by zero. -/
lemma exists_epi_isSumOfExtensionByZeroStructureSheaves (M : SheafOfModules.{u} O) :
    ∃ (N : SheafOfModules.{u} O) (_ : IsSumOfExtensionByZeroStructureSheaves O N)
      (f : N ⟶ M), Epi f := by
  obtain ⟨I, U, f, hf⟩ := Stacks.SheafOfModules.exists_epi_from_coproduct_jShriek_unit O M
  exact ⟨_, ⟨I, U, ⟨Iso.refl _⟩⟩, f, hf⟩

private lemma nonempty_resolution_of_ladder
    [HasExactColimitsOfShape ℕ (SheafOfModules.{u} O)]
    {G : CochainComplex (SheafOfModules.{u} O) ℤ}
    {Q : ℕ → CochainComplex (SheafOfModules.{u} O) ℤ} (f : ∀ n : ℕ, Q n ⟶ G.truncLE n)
    (g : ∀ n : ℕ, Q n ⟶ Q (n + 1)) (hf : ∀ n, QuasiIso (f n))
    (hepi : ∀ (n : ℕ) (i : ℤ), Epi ((f n).f i)) (hle : ∀ n : ℕ, (Q n).IsStrictlyLE n)
    (hQ : ∀ (n : ℕ) (i : ℤ), IsSumOfExtensionByZeroStructureSheaves O ((Q n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), ∃ (C : SheafOfModules.{u} O)
      (_ : IsSumOfExtensionByZeroStructureSheaves O C) (e : (Q (n + 1)).X i ≅ (Q n).X i ⊞ C),
        (g n).f i ≫ e.hom = biprod.inl)
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ G.ιTruncLE ((n : ℕ) : ℤ)) :
    Nonempty (ResolutionByDirectSumsExtensionsByZero O G) := by
  let Q' (n : ℕ) := Q (n + 1)
  let g' (n : ℕ) : Q' n ⟶ Q' (n + 1) := g (n + 1)
  let f' (n : ℕ) : Q' n ⟶ G.truncLE ((n + 1 : ℕ) : ℤ) := f (n + 1)
  have hcomm (n : ℕ) : g' n ≫ f' (n + 1) = f' n ≫ truncLESucc G n :=
    comp_eq_comp_truncLESucc n _ _ _ (hladder (n + 1))
  obtain ⟨α, hfac, hcol⟩ :=
    exists_quasiIso_colimit_ofSequence g' f' (fun n => hf (n + 1)) fun n => hladder (n + 1)
  refine ⟨{
    system := Functor.ofSequence g'
    toTruncation := fun n => by
      show Q' n ⟶ G.truncLE ((n : ℤ) + 1)
      simpa [Nat.cast_add] using f' n
    truncationTransition := fun n => by simpa [Nat.cast_add] using truncLESucc G n
    truncationTransition_ι := fun n => by simpa [Nat.cast_add] using truncLESucc_ι G n
    square := fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      show g' n ≫ f' (n + 1) = f' n ≫ truncLESucc G n
      exact hcomm n
    quasiIso := fun n => by
      show QuasiIso (f' n)
      simpa [f'] using hf (n + 1)
    epi_f := fun n i => by
      show Epi ((f' n).f i)
      simpa [f'] using hepi (n + 1) i
    boundedAbove := fun n => by
      show ∃ a : ℤ, (Q' n).IsStrictlyLE a
      exact ⟨((n + 1 : ℕ) : ℤ), by simpa [Q'] using hle (n + 1)⟩
    term_isSum := fun n i => by
      show IsSumOfExtensionByZeroStructureSheaves O ((Q' n).X i)
      simpa [Q'] using hQ (n + 1) i
    transition_splitMono := fun n i => by
      obtain ⟨C, -, e, he⟩ := hsplit (n + 1) i
      rw [Functor.ofSequence_map_homOfLE_succ]
      show IsSplitMono ((g' n).f i)
      exact ⟨⟨e.hom ≫ biprod.fst, by rw [reassoc_of% he, biprod.inl_fst]⟩⟩
    transition_cokernel_isSum := fun n i => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      obtain ⟨C, ⟨I, U, ⟨ε⟩⟩, e, he⟩ := hsplit (n + 1) i
      exact ⟨I, U, ⟨ε ≪≫ (cokernel.mapIso ((g' n).f i) biprod.inl (Iso.refl _) e he ≪≫
        cokernelBiprodInlIso (X := (Q' n).X i) (Y := C)).symm⟩⟩
    colimitComparison := α
    colimitComparison_fac := hfac
    colimit_quasiIso := hcol }⟩

/-- Every cochain complex `G` of `O`-modules on a ringed space admits a compatible system of
bounded-above resolutions of its canonical truncations `τ_{≤ n+1} G` whose terms and successive
cokernels are direct sums of extensions by zero `j_{U!} O_U`, and whose colimit maps
quasi-isomorphically to `G`. -/
@[stacks 079T]
theorem exists_resolutionByDirectSumsExtensionsByZero
    (G : CochainComplex (SheafOfModules.{u} O) ℤ) :
    Nonempty (ResolutionByDirectSumsExtensionsByZero O G) := by
  classical
  let A := SheafOfModules.{u} O
  let P : ObjectProperty A := fun M => IsSumOfExtensionByZeroStructureSheaves O M
  let : Abelian A := AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules O
  let : CategoryWithHomology A := CategoryTheory.categoryWithHomology_of_abelian
  let : HasZeroObject A := inferInstance
  let : HasZeroMorphisms A := inferInstance
  let : HasZeroObject (CochainComplex A ℤ) := inferInstance
  let : HasZeroMorphisms (CochainComplex A ℤ) := inferInstance
  let : AB5OfSize.{u, u} A := AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules O
  let : HasExactColimitsOfShape (ULiftHom.{u} (ULift.{u} ℕ)) A :=
    (AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules O).ofShape _
  let : HasExactColimitsOfShape ℕ A :=
    HasExactColimitsOfShape.of_domain_equivalence A
      (ULiftHomULiftCategory.equiv ℕ).symm
  let : P.ContainsZero := ⟨exists_isZero_isSumOfExtensionByZeroStructureSheaves O⟩
  obtain ⟨Q, f, g, hf, hepi, hle, hQ, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P
      (fun _ _ => IsSumOfExtensionByZeroStructureSheaves.biprod O)
      (exists_epi_isSumOfExtensionByZeroStructureSheaves O) G
  exact nonempty_resolution_of_ladder O f g hf hepi hle hQ hsplit hladder

end Stacks.Cohomology.SpaceResolutionByExtensionsByZero
