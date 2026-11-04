module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSectionsSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions

/-!
# Local generators of a locally constant sheaf of modules of finite type

Let `(C, J)` be a site and `Λ` a ring. A sheaf `F` of `Λ`-modules which is locally constant of
finite type (`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`) is locally generated
by finitely many sections: on an object `Z` over which `F` is the constant sheaf `E̲` attached to
a finitely generated module `E`, the sections cut out by finitely many generators of `E`
generate `F` locally on `C/Z`, every section of `E̲` being locally the image of an element of `E`.

Read as a presheaf of modules over the constant presheaf of rings with value `Λ`
(`Stacks.PresheafOfModules.ofFunctorObj`), this says that `F` is of finite type in the
sheafification-free sense `Stacks.SheafOfModules.IsFiniteTypeSections`.

## Main results

* `ConstantSheaf.generatesLocally_trivSection`: the sections cut out by a generating family of
  `E` under a trivialization `E̲ ≅ F|_Z` generate `F` locally.
* `ConstantSheaf.isFiniteTypeSections_ofFunctorObj_of_isFiniteTypeLocallyConstantModuleSheaf`:
  a locally constant sheaf of finite type is of finite type in the sense of sections over the
  constant presheaf of rings.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace Stacks.ConstantSheaf

universe v u w r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Λ : Type r} [Ring Λ]

/-- **The sections of a trivialization cut out by generators generate locally.** Let
`α : E̲ ≅ F|_Z` trivialize a sheaf of `Λ`-modules `F` over `Z` by the constant sheaf attached to a
module `E`, and let `e` be a finite family spanning `E`. Then the sections of `F` over `Z` that
`α` attaches to the `e i` generate `F` locally over `Z`, as a presheaf of modules over the
constant presheaf of rings with value `Λ`. -/
theorem generatesLocally_trivSection {Z : C} {E : ModuleCat.{max u v w} Λ}
    {F : Sheaf J (ModuleCat.{max u v w} Λ)}
    (α : (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) Z).obj F)
    {n : ℕ} (e : Fin n → E) (he : Submodule.span Λ (Set.range e) = ⊤) :
    Stacks.SheafOfModules.GeneratesLocally J (Stacks.PresheafOfModules.ofFunctorObj Λ F.obj)
      (fun i => (trivSection α (Over.mk (𝟙 Z))).hom (e i)) := by
  intro V f t
  have := isLocallySurjective_toSheafify_moduleCat.{v, max u v, w} (J.over Z) Λ
    ((Functor.const (Over Z)ᵒᵖ).obj E)
  let t' := (α.inv.hom.app (op (Over.mk f))).hom t
  refine ⟨_, Presheaf.imageSieve_mem (J.over Z)
    (toSheafify (J.over Z) ((Functor.const (Over Z)ᵒᵖ).obj E)) (U := op (Over.mk f)) t',
    fun W g hg => ?_⟩
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨x, hx⟩ := hg
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1
    (he ▸ Submodule.mem_top : x ∈ Submodule.span Λ (Set.range e))
  refine ⟨a, ?_⟩
  have h1 : ∀ i, (Stacks.PresheafOfModules.ofFunctorObj Λ F.obj).restrictₛₗ (g ≫ f).op
      ((trivSection α (Over.mk (𝟙 Z))).hom (e i)) = (trivSection α (Over.mk (g ≫ f))).hom (e i) :=
    fun i => trivSection_restrict
      (Over.homMk (g ≫ f) (by simp) : Over.mk (g ≫ f) ⟶ Over.mk (𝟙 Z)) (e i)
  have hnat := ConcreteCategory.congr_hom
    (α.hom.hom.naturality (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f).op) t'
  have hinv : (α.hom.hom.app (op (Over.mk f))).hom t' = t :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (Over.mk f))) α.inv_hom_id) t
  have h2 : (trivSection α (Over.mk (g ≫ f))).hom x =
      (Stacks.PresheafOfModules.ofFunctorObj Λ F.obj).restrictₛₗ g.op t := by
    rw [trivSection_apply]
    refine (congrArg (α.hom.hom.app (op (Over.mk (g ≫ f)))).hom hx).trans ?_
    refine hnat.trans ?_
    rw [ConcreteCategory.comp_apply, hinv]
    rfl
  simp only [h1]
  rw [← h2, ← ha, map_sum]
  simp only [map_smul]
  rfl

/-- **A locally constant sheaf of finite type is of finite type in the sense of sections.** A
sheaf of `Λ`-modules which is locally constant of finite type, read as a presheaf of modules over
the constant presheaf of rings with value `Λ`, is of finite type in the sheafification-free sense:
the objects over which it is the constant sheaf of a finitely generated module cover the site,
and over each of them finitely many sections generate it locally
(`Stacks.ConstantSheaf.generatesLocally_trivSection`). -/
theorem isFiniteTypeSections_ofFunctorObj_of_isFiniteTypeLocallyConstantModuleSheaf
    {F : Sheaf J (ModuleCat.{max u v w} Λ)}
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F) :
    Stacks.SheafOfModules.IsFiniteTypeSections J
      (Stacks.PresheafOfModules.ofFunctorObj Λ F.obj) := by
  refine ⟨{Z : C // IsConstantFGOver J Λ Z F}, Subtype.val, fun Y => ?_, fun ⟨Z, E, hE, ⟨α⟩⟩ => ?_⟩
  · exact J.superset_covering (S := trivSieve J Λ F Y)
      (fun W g (hg : IsConstantFGOver J Λ W F) => ⟨⟨W, hg⟩, ⟨𝟙 W⟩⟩)
      ((isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem F).1 hF Y)
  · have : Module.Finite Λ E := hE
    obtain ⟨n, e, he⟩ := Module.Finite.exists_fin (R := Λ) (M := E)
    exact ⟨n, _, generatesLocally_trivSection α e he⟩

end Stacks.ConstantSheaf
