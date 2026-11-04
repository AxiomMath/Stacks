module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleTotalMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded

/-!
# Finite type on affine opens, read on the module of homogeneous sections

`Stacks.Coherent.IsFiniteTypeOnAffine` says that over every affine open `U` the homogeneous
sections of a graded module `M` over a sheaf of graded algebras `𝒜` are generated, as an
additive group in each degree, by the products of finitely many homogeneous sections with the
homogeneous sections of `𝒜`. That is exactly finite generation of the module
`⨁ₙ Mₙ(U)` over the ring `⨁ₘ 𝒜ₘ(U)`, and this file proves the equivalence of the two
statements for a commutative `𝒜`. As a consequence, a graded submodule of a graded module of
finite type is again of finite type as soon as the ring of homogeneous sections of `𝒜` over
each affine open is Noetherian.

## Main results

* `Stacks.Coherent.moduleFinite_total_of_isFiniteTypeOnAffine` and
  `Stacks.Coherent.isFiniteTypeOnAffine_of_forall_moduleFinite` — the two directions of the
  equivalence.
* `Stacks.Coherent.isFiniteTypeOnAffine_of_injective` — a graded module mapping degreewise
  injectively into one of finite type is of finite type, over a sheaf of graded algebras whose
  rings of homogeneous sections over affine opens are Noetherian.
* `Stacks.Coherent.isFiniteTypeOnAffine_ker` — the same for the graded kernel of a homomorphism
  of graded modules.

## References

* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Coherent

open SheafOfModules.GradedModule (totalFun totalFunHom totalLinearMap)

variable {X : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  [A.IsCommutative] (M : SheafOfModules.GradedModule.{u, u, u} A)

/-- The homogeneous sections of a graded module over an affine open, written as a single
module over the ring of homogeneous sections of the algebra. -/
abbrev totalOn (U : X.affineOpens) : Type u := M.toPresheafGradedModule.Total (op U.1)

/-- The set of products of a homogeneous section drawn from `G` with a homogeneous section of
the algebra, in a fixed degree. -/
def generatedSet (U : X.affineOpens)
    (G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1))) (n : ℤ) :
    Set ((M.piece n).val.obj (op U.1)) :=
  { t | ∃ s : Σ d : ℤ, (M.piece d).val.obj (op U.1), s ∈ G ∧
      ∃ (m : ℤ) (a : (A.piece m).val.obj (op U.1)) (h : s.1 + m = n),
        t = h ▸ M.smul s.1 m (op U.1) s.2 a }

/-- The homogeneous sections drawn from `G`, as a subset of the module of all homogeneous
sections. -/
def generatorSet (U : X.affineOpens)
    (G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1))) : Set (totalOn M U) :=
  (fun s => M.toPresheafGradedModule.incl s.1 s.2) '' G

omit [A.IsCommutative] in
/-- A homogeneous section in `G` lies in `generatorSet M U G`. -/
theorem mem_generatorSet (U : X.affineOpens)
    {G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1))}
    {s : Σ n : ℤ, (M.piece n).val.obj (op U.1)} (hs : s ∈ G) :
    M.toPresheafGradedModule.incl s.1 s.2 ∈ generatorSet M U G :=
  ⟨s, hs, rfl⟩

omit [A.IsCommutative] in
/-- `generatorSet M U G` is monotone in `G`. -/
theorem generatorSet_mono (U : X.affineOpens)
    {G G' : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1))} (h : G ⊆ G') :
    generatorSet M U G ⊆ generatorSet M U G' :=
  Set.image_mono h

/-! ### From homogeneous generation to finite generation -/

/-- If `M` is of finite type on affine opens, then over every affine open the module of
homogeneous sections of `M` is finitely generated over the ring of homogeneous sections of the
algebra. -/
theorem moduleFinite_total_of_isFiniteTypeOnAffine (hft : IsFiniteTypeOnAffine M)
    (U : X.affineOpens) :
    Module.Finite (A.toPresheafGradedAlgebra.Total (op U.1)) (totalOn M U) := by
  obtain ⟨G, hG⟩ := hft U
  refine Module.finite_def.mpr
    (Submodule.fg_def.mpr ⟨generatorSet M U (↑G), (G.finite_toSet.image _), top_unique ?_⟩)
  intro t _
  induction t using Stacks.GradedModule.incl_induction with
  | zero => exact Submodule.zero_mem _
  | incl n x =>
    have hsub : AddSubgroup.closure (generatedSet M U (↑G) n) ≤
        AddSubgroup.comap
          (DirectSum.of (fun k => ((M.piece k).val.obj (op U.1) : Type u)) n)
          (Submodule.span (A.toPresheafGradedAlgebra.Total (op U.1))
            (generatorSet M U (↑G))).toAddSubgroup := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro t ⟨s, hsG, m, a, h, rfl⟩
      subst h
      show M.toPresheafGradedModule.incl (s.1 + m) (M.smul s.1 m (op U.1) s.2 a) ∈
        Submodule.span _ _
      have hsm : A.toPresheafGradedAlgebra.incl m a •
            M.toPresheafGradedModule.incl s.1 s.2
          = M.toPresheafGradedModule.incl (s.1 + m) (M.smul s.1 m (op U.1) s.2 a) :=
        Stacks.GradedModule.incl_smul_incl (M := M.toPresheafGradedModule) m s.1 a s.2
      rw [← hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_generatorSet M U hsG))
    exact hsub ((hG n).ge (AddSubgroup.mem_top x))
  | add t t' ht ht' => exact Submodule.add_mem _ (ht trivial) (ht' trivial)

/-! ### From finite generation to homogeneous generation -/

/-- Every section of the module of homogeneous sections lies in the span of finitely many
*homogeneous* sections. -/
theorem exists_finite_mem_span (U : X.affineOpens) (t : totalOn M U) :
    ∃ G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1)), G.Finite ∧
      t ∈ Submodule.span (A.toPresheafGradedAlgebra.Total (op U.1)) (generatorSet M U G) := by
  induction t using Stacks.GradedModule.incl_induction with
  | zero => exact ⟨∅, Set.finite_empty, Submodule.zero_mem _⟩
  | incl n x =>
    exact ⟨{⟨n, x⟩}, Set.finite_singleton _,
      Submodule.subset_span (mem_generatorSet M U (s := ⟨n, x⟩) rfl)⟩
  | add t t' ht ht' =>
    obtain ⟨G, hGfin, hG⟩ := ht
    obtain ⟨G', hG'fin, hG'⟩ := ht'
    exact ⟨G ∪ G', hGfin.union hG'fin, Submodule.add_mem _
      (Submodule.span_mono (generatorSet_mono M U Set.subset_union_left) hG)
      (Submodule.span_mono (generatorSet_mono M U Set.subset_union_right) hG')⟩

/-- A finitely generated module of homogeneous sections is spanned by finitely many
homogeneous sections. -/
theorem exists_homogeneous_span (U : X.affineOpens)
    [Module.Finite (A.toPresheafGradedAlgebra.Total (op U.1)) (totalOn M U)] :
    ∃ G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1)), G.Finite ∧
      Submodule.span (A.toPresheafGradedAlgebra.Total (op U.1))
        (generatorSet M U G) = ⊤ := by
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  choose Gf hGffin hGf using exists_finite_mem_span M U
  refine ⟨⋃ t ∈ S, Gf t, hSfin.biUnion fun t _ => hGffin t, top_unique ?_⟩
  rw [← hS, Submodule.span_le]
  intro t ht
  exact Submodule.span_mono
    (generatorSet_mono M U (Set.subset_biUnion_of_mem (u := Gf) ht)) (hGf t)

/-- The degree-`n` component of a scalar multiple of a homogeneous generator is a sum of
products of that generator with homogeneous sections of the algebra. -/
theorem totalFun_smul_incl_mem (U : X.affineOpens)
    {G : Set (Σ n : ℤ, (M.piece n).val.obj (op U.1))}
    {s : Σ n : ℤ, (M.piece n).val.obj (op U.1)} (hs : s ∈ G)
    (a : A.toPresheafGradedAlgebra.Total (op U.1)) (n : ℤ) :
    totalFun M (op U.1) (a • M.toPresheafGradedModule.incl s.1 s.2) n ∈
      AddSubgroup.closure (generatedSet M U G n) := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_smul]; exact AddSubgroup.zero_mem _
  | incl m b =>
    rw [Stacks.GradedModule.incl_smul_incl]
    rcases eq_or_ne (s.1 + m) n with h | h
    · subst h
      rw [SheafOfModules.GradedModule.totalFun_incl]
      exact AddSubgroup.subset_closure ⟨s, hs, m, b, rfl, rfl⟩
    · rw [SheafOfModules.GradedModule.totalFun_incl_of_ne h]
      exact AddSubgroup.zero_mem _
  | add a a' ha ha' =>
    rw [add_smul, SheafOfModules.GradedModule.totalFun_add]
    exact AddSubgroup.add_mem _ ha ha'

/-- If over every affine open the module of homogeneous sections of `M` is finitely generated
over the ring of homogeneous sections of the algebra, then `M` is of finite type on affine
opens. -/
theorem isFiniteTypeOnAffine_of_forall_moduleFinite
    (h : ∀ U : X.affineOpens,
      Module.Finite (A.toPresheafGradedAlgebra.Total (op U.1)) (totalOn M U)) :
    IsFiniteTypeOnAffine M := by
  classical
  intro U
  have := h U
  obtain ⟨G, hGfin, hG⟩ := exists_homogeneous_span M U
  refine ⟨hGfin.toFinset, fun n => top_unique fun x _ => ?_⟩
  suffices hmem : x ∈ AddSubgroup.closure (generatedSet M U G n) by
    refine AddSubgroup.closure_mono ?_ hmem
    rintro t ⟨s, hs, m, a, hh, rfl⟩
    exact ⟨s, hGfin.mem_toFinset.mpr hs, m, a, hh, rfl⟩
  have hx : M.toPresheafGradedModule.incl n x ∈
      Submodule.span (A.toPresheafGradedAlgebra.Total (op U.1)) (generatorSet M U G) :=
    hG ▸ Submodule.mem_top
  obtain ⟨k, f, g, hc⟩ := Submodule.mem_span_set'.1 hx
  have hxc : x = totalFunHom M (op U.1) n (∑ i, f i • (g i : totalOn M U)) := by
    rw [hc]
    exact (SheafOfModules.GradedModule.totalFun_incl n x).symm
  rw [hxc, map_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨s, hsG, hsi⟩ := (g i).2
  rw [SheafOfModules.GradedModule.totalFunHom_apply, ← hsi]
  exact totalFun_smul_incl_mem M U hsG (f i) n

/-! ### The algebra as a module over itself -/

omit [A.IsCommutative] in
/-- A sheaf of graded algebras, as a graded module over itself, is of finite type on affine
opens. -/
theorem isFiniteTypeOnAffine_regularModule :
    IsFiniteTypeOnAffine (SheafOfModules.GradedModule.regularModule A) := by
  classical
  intro U
  refine ⟨{⟨0, A.one.eval (op U.1)⟩}, fun n => top_unique fun a _ => ?_⟩
  refine AddSubgroup.subset_closure ⟨⟨0, A.one.eval (op U.1)⟩, Finset.mem_singleton_self _,
    n, a, zero_add n, ?_⟩
  exact (Stacks.degCast_eq_of_heq (F := fun k => ((A.piece k).val.obj (op U.1) : Type u))
    (zero_add n) (A.one_mul n (op U.1) a)).symm

/-! ### The Noetherian step -/

/-- A graded module mapping degreewise injectively into one of finite type on affine opens is
of finite type on affine opens, over a sheaf of graded algebras whose rings of homogeneous
sections over affine opens are Noetherian. -/
theorem isFiniteTypeOnAffine_of_injective {N : SheafOfModules.GradedModule.{u, u, u} A}
    (f : M ⟶ N)
    (hinj : ∀ (U : X.affineOpens) (n : ℤ),
      Function.Injective ((f.app n).val.app (op U.1)))
    (hN : IsFiniteTypeOnAffine N)
    (hnoeth : ∀ U : X.affineOpens,
      IsNoetherianRing (A.toPresheafGradedAlgebra.Total (op U.1))) :
    IsFiniteTypeOnAffine M := by
  refine isFiniteTypeOnAffine_of_forall_moduleFinite M fun U => ?_
  have := hnoeth U
  have := moduleFinite_total_of_isFiniteTypeOnAffine N hN U
  have : IsNoetherian (A.toPresheafGradedAlgebra.Total (op U.1)) (totalOn N U) :=
    inferInstance
  exact Module.Finite.of_injective (totalLinearMap f (op U.1))
    (SheafOfModules.GradedModule.injective_totalAddHom f (op U.1) (hinj U))

/-- The graded kernel of a homomorphism of graded modules is of finite type on affine opens
when its source is, over a sheaf of graded algebras whose rings of homogeneous sections over
affine opens are Noetherian. -/
theorem isFiniteTypeOnAffine_ker {Q N : SheafOfModules.GradedModule.{u, u, u} A} (π : Q ⟶ N)
    (hQ : IsFiniteTypeOnAffine Q)
    (hnoeth : ∀ U : X.affineOpens,
      IsNoetherianRing (A.toPresheafGradedAlgebra.Total (op U.1))) :
    IsFiniteTypeOnAffine (SheafOfModules.GradedModule.ker π) :=
  isFiniteTypeOnAffine_of_injective (SheafOfModules.GradedModule.ker π)
    (SheafOfModules.GradedModule.kerι π)
    (fun _ _ _ _ h => Subtype.ext h) hQ hnoeth

end Stacks.Coherent

end
