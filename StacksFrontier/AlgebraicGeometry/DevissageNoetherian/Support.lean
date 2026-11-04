module

public import StacksFrontier.AlgebraicGeometry.DevissageBounded.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType

/-!
# The support of a finite type sheaf of modules is closed

The Noetherian induction of [Stacks, Tag 01YF] runs over the closed subsets of the scheme, with
the support of a coherent module as the quantity that decreases. This file supplies the two
facts about supports that the induction needs and that nothing in this repository had:

* the support of a sheaf of modules **of finite type** is closed, and
* a sheaf of modules with empty support is a zero module.

Neither needs quasi-coherence or a Noetherian hypothesis, and coherence enters only as the
source of finite type. Closedness is stated over an arbitrary sheaf of commutative rings on a
topological space, which is the generality its proof has; the vanishing statement is stated for
a scheme, because `CategoryTheory.Limits.IsZero` needs a `Category` instance on the category of
sheaves of modules and `TopCat.Sheaf` is a `def` that does not unfold during instance search.

## Main results

* `Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp`: the support of a finite type
  sheaf of modules is closed.
* `Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty`: a module on a scheme
  with empty support is zero.
* `Stacks.AlgebraicGeometry.DevissageNoetherian.forall_isClosed_supp` and
  `Stacks.AlgebraicGeometry.DevissageNoetherian.forall_isZero_of_supp_eq_empty`: the two facts
  in the exact shape the Noetherian induction of
  `StacksFrontier/AlgebraicGeometry/DevissageNoetherian/Basic.lean` consumes them.

## Implementation notes

**Closedness is an openness statement about the complement.** If the stalk at `x` vanishes then
the germs at `x` of a finite family of generating sections on a neighbourhood `V` of `x` all
vanish, so each of those sections already vanishes on some smaller neighbourhood; the
intersection of the finitely many neighbourhoods is again open, and at each of its points the
germs of the generating sections are the germs of zero sections, hence zero. Since the germs of
generating sections span the stalk, the stalk vanishes there too. So the complement of the
support contains an open neighbourhood of each of its points.

The spanning statement is `SheafOfModules.span_germ_generators_eq_top` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType`, which this module imports. It
used to be duplicated here because it was `private` there; it is now visible and the copy is
gone.

**Vanishing.** Empty support means every stalk is subsingleton, so by `section_ext` every module
of sections is subsingleton, so the identity of the sheaf of modules agrees with the zero
morphism on every open. `CategoryTheory.Limits.IsZero.iff_id_eq_zero` turns that into `IsZero`.
The route through `CategoryTheory.Sheaf.isZero_iff_stalkFunctor_obj_isZero` is not taken: it is
stated for `CategoryTheory.Sheaf J C`, and `TopCat.Sheaf` is a `def` that does not unfold during
unification — the same obstruction that keeps this statement at the scheme level.

The finite intersection of neighbourhoods is formed as a `Set` and packaged with
`isOpen_iInter_of_finite`, rather than as an infimum in `TopologicalSpace.Opens`: the infimum of
an infinite family of opens is the interior of the intersection, so membership in it is not the
pointwise condition, and the index type here is only known to be `Finite`.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.DevissageNoetherian

/-! ### The germs of generating sections span the stalk -/

/-- **A point at which every generating section has vanishing germ is outside the support.**
The germs of the generating sections span the stalk, so if they all vanish the stalk does. -/
lemma notMem_supp_of_germ_eq_zero {X : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (y : X) (V : Opens X) (hyV : y ∈ V) (gs : (F.over V).GeneratingSections)
    [Finite gs.I]
    (h : ∀ j : gs.I, TopCat.Presheaf.germ F.val.presheaf V y hyV
      ((gs.s j).val (op (Over.mk (𝟙 V)))) = 0) :
    y ∉ SheafOfModules.supp F := by
  let : Module ↑(TopCat.Presheaf.stalk R.obj y)
      ↑(TopCat.Presheaf.stalk F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val y
  have htop := SheafOfModules.span_germ_generators_eq_top R F y V hyV gs
  have hbot : Submodule.span ↑(TopCat.Presheaf.stalk R.obj y)
      (Set.range (fun j : gs.I => TopCat.Presheaf.germ F.val.presheaf V y hyV
        ((gs.s j).val (op (Over.mk (𝟙 V)))))) = ⊥ :=
    Submodule.span_eq_bot.mpr (by rintro z ⟨j, rfl⟩; exact h j)
  rintro ⟨a, ha⟩
  exact ha (Submodule.mem_bot _ |>.mp (hbot ▸ htop ▸ Submodule.mem_top (x := a)))

/-- Sections with the same germ at `x` agree on a smaller neighbourhood of `x`. -/
private theorem exists_map_eq_of_germ_eq {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {V : Opens X} {x : X} (hxV : x ∈ V) (s t : F.obj (op V))
    (h : F.germ V x hxV s = F.germ V x hxV t) :
    ∃ (W : Opens X) (hWV : W ≤ V), x ∈ W ∧ F.map (homOfLE hWV).op s = F.map (homOfLE hWV).op t := by
  obtain ⟨W, hxW, iU, iV, he⟩ := F.germ_eq x hxV hxV s t h
  exact ⟨W, leOfHom iU, hxW, by
    rw [Subsingleton.elim (homOfLE (leOfHom iU)) iU, he, Subsingleton.elim iV iU]⟩

/-- **A finite family of sections with vanishing germs at `x` vanishes on a neighbourhood of
`x`.** The neighbourhoods on which the individual sections vanish are intersected as sets and
repackaged as an open, since the infimum of an infinite family in `TopologicalSpace.Opens` is
the interior of the intersection. -/
lemma exists_isOpen_forall_map_eq_zero {X : TopCat.{u}}
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) {ι : Type u} [Finite ι]
    (V : Opens X) {x : X} (hxV : x ∈ V) (t : ι → F.obj (op V))
    (h : ∀ j, F.germ V x hxV (t j) = 0) :
    ∃ T : Set X, IsOpen T ∧ x ∈ T ∧ T ⊆ (V : Set X) ∧
      ∀ (j : ι) (y : X) (hyV : y ∈ V), y ∈ T → F.germ V y hyV (t j) = 0 := by
  have key : ∀ j : ι, ∃ W : Opens X, x ∈ W ∧ ∃ hWV : W ≤ V,
      F.map (homOfLE hWV).op (t j) = 0 := by
    intro j
    obtain ⟨W, hWV, hxW, he⟩ := exists_map_eq_of_germ_eq F hxV (t j) 0 (by rw [h j, map_zero])
    exact ⟨W, hxW, hWV, by rw [he, map_zero]⟩
  choose W hxW hWV hWz using key
  refine ⟨(V : Set X) ∩ ⋂ j, (W j : Set X),
    V.2.inter (isOpen_iInter_of_finite fun j => (W j).2),
    ⟨hxV, Set.mem_iInter.mpr hxW⟩, Set.inter_subset_left, fun j y hyV hy => ?_⟩
  have hyW : y ∈ W j := Set.mem_iInter.mp hy.2 j
  rw [← TopCat.Presheaf.germ_res_apply F (homOfLE (hWV j)) y hyW (t j), hWz j]
  exact map_zero _

/-- **[Stacks, Tag 056J]: the support of a sheaf of modules of finite type is closed.** Neither
quasi-coherence nor a Noetherian hypothesis nor a scheme structure is used.

If the stalk at `x` vanishes then the germs at `x` of the finitely many generating sections on a
neighbourhood of `x` vanish, so those sections vanish on a smaller neighbourhood, and at every
point of it their germs — which span the stalk there — vanish. -/
theorem isClosed_supp {X : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) [F.IsFiniteType] :
    IsClosed (SheafOfModules.supp F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨U₀, -, ⟨i, ⟨g₀⟩⟩, hxU₀⟩ := σ.coversTop ⊤ x (by trivial)
  have hxV : x ∈ σ.X i := (leOfHom g₀) hxU₀
  have hfin : Finite (σ.generators i).I := (hσ.isFiniteType i).finite
  have hsub : Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
    not_nontrivial_iff_subsingleton.mp fun hnt =>
      hx ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hnt)
  obtain ⟨T, hTopen, hxT, hTV, hTz⟩ := exists_isOpen_forall_map_eq_zero F.val.presheaf (σ.X i) hxV
    (fun j : (σ.generators i).I => ((σ.generators i).s j).val (op (Over.mk (𝟙 (σ.X i)))))
    (fun _ => Subsingleton.elim _ _)
  exact ⟨T, fun y hy => notMem_supp_of_germ_eq_zero R F y (σ.X i) (hTV hy) (σ.generators i)
    (fun j => hTz j y (hTV hy) hy), hTopen, hxT⟩

/-! ### Empty support means zero -/

/-- **A sheaf of modules with empty support is a zero module.** Every stalk being subsingleton
makes every module of sections subsingleton, by `section_ext`, so the identity morphism of the
sheaf of modules is the zero morphism. -/
theorem isZero_of_supp_eq_empty {X : Scheme.{u}} (F : X.Modules)
    (h : SheafOfModules.supp F = ∅) : IsZero F := by
  have hst : ∀ x : X, Subsingleton ↑(TopCat.Presheaf.stalk F.presheaf x) := fun x =>
    not_nontrivial_iff_subsingleton.mp fun hnt => by
      simpa [h] using (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hnt
  have hsec : ∀ U : X.Opens, Subsingleton ↑(Γ(F, U)) := by
    intro U
    refine ⟨fun s t => ?_⟩
    refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf F) (U := op U)
      fun x hx => ?_
    have := hst x
    exact exists_map_eq_of_germ_eq F.presheaf hx s t (Subsingleton.elim _ _)
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  have := hsec U
  rw [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app]
  exact ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _

/-! ### The two facts in the form the Noetherian induction consumes them -/

/-- **The support of a coherent module on a scheme is closed.** Coherence is used only through
finite type. -/
theorem isClosed_supp_of_isCoherent {X : Scheme.{u}} (F : X.Modules) (hF : F.IsCoherent) :
    IsClosed (SheafOfModules.supp F) :=
  have := hF
  have := SheafOfModules.IsCoherent.isFiniteType (M := F)
  isClosed_supp X.sheaf F

/-- **Closedness of the support of every coherent module**, as the hypothesis `hclosed` of
`Stacks.AlgebraicGeometry.DevissageNoetherian.isIdealDevissable_of_isCoherent`. -/
theorem forall_isClosed_supp (X : Scheme.{u}) :
    ∀ F : X.Modules, F.IsCoherent → IsClosed (SheafOfModules.supp F) :=
  fun F hF => isClosed_supp_of_isCoherent F hF

/-- **Vanishing of every module with empty support**, as the hypothesis `hvanish` of
`Stacks.AlgebraicGeometry.DevissageNoetherian.isIdealDevissable_of_isCoherent`. -/
theorem forall_isZero_of_supp_eq_empty (X : Scheme.{u}) :
    ∀ F : X.Modules, SheafOfModules.supp F = ∅ → IsZero F :=
  fun F h => isZero_of_supp_eq_empty F h

end Stacks.AlgebraicGeometry.DevissageNoetherian

end

end
