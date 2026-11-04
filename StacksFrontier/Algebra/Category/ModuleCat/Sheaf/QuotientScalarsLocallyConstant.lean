module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdeal

/-!
# Local constancy and restriction of coefficients to a quotient ring

Let `(C, J)` be a site, `Λ` a commutative ring and `I ⊆ Λ` an ideal. Restriction of coefficients
along `Λ → Λ ⧸ I` (`Stacks.ModuleSheaf.restrictQuotientScalars`) is fully faithful on sheaves of
modules, because it is so on modules. A sheaf `H` of `Λ ⧸ I`-modules is locally constant of
finite type exactly when its restriction of coefficients is so as a sheaf of `Λ`-modules.

Going down, a finitely generated `Λ ⧸ I`-module is finitely generated over `Λ`, and restriction
of coefficients commutes with constant sheaves and with restriction to a slice site. Going up, a
constant value `E` over an object not covered by the empty sieve injects into the sections of the
constant sheaf, which are killed by `I`; so `E` is a `Λ ⧸ I`-module, and the trivialization over
`Λ` comes from one over `Λ ⧸ I` by full faithfulness. Over an object covered by the empty sieve
every sheaf trivializes with value zero.

## Main results

* `Stacks.ModuleSheaf.fullyFaithfulRestrictQuotientScalars`: restriction of coefficients along
  `Λ → Λ ⧸ I` is fully faithful.
* `Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictQuotientScalars_iff`: local
  constancy of finite type is detected after restriction of coefficients.

## References

* [Stacks Project, Tag 09BU](https://stacks.math.columbia.edu/tag/09BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u r

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]
  (I : Ideal Λ)

/-- A finite module over `Λ ⧸ I` is finite over `Λ`. -/
theorem finite_restrictScalars_quotient {Λ : Type*} [CommRing Λ] (I : Ideal Λ)
    (M : ModuleCat.{w} (Λ ⧸ I)) [Module.Finite (Λ ⧸ I) M] :
    Module.Finite Λ ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M
  let : Module (Λ ⧸ I) M' := inferInstanceAs (Module (Λ ⧸ I) M)
  have : Module.Finite (Λ ⧸ I) M' := inferInstanceAs (Module.Finite (Λ ⧸ I) M)
  have : IsScalarTower Λ (Λ ⧸ I) M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans (Λ ⧸ I) M'

section FullyFaithful

variable [UnivLE.{max u v, w}]

/-- **Restriction of coefficients along `Λ → Λ ⧸ I` is fully faithful.** A `Λ`-linear map
between `Λ ⧸ I`-modules is `Λ ⧸ I`-linear, sectionwise. -/
def fullyFaithfulRestrictQuotientScalars :
    (restrictQuotientScalars.{u, v, w} J Λ I).FullyFaithful where
  preimage {G H} f := ⟨{
    app U := ModuleCat.ofHom
      { toFun := (f.hom.app U).hom
        map_add' := map_add _
        map_smul' c x := by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact (f.hom.app U).hom.map_smul a x }
    naturality U U' g := by
      ext x
      exact congrArg (fun φ => φ.hom x) (f.hom.naturality g) }⟩
  map_preimage f := rfl
  preimage_map f := rfl

end FullyFaithful


/-- Over any slice, both module categories have sheafification and restriction of scalars along
`Λ → Λ ⧸ I` preserves it. -/
private theorem hasSheafify_and_preservesSheafification_restrictScalars (X : C) :
    HasSheafify (J.over X) (ModuleCat.{max u v w r} Λ) ∧
      HasSheafify (J.over X) (ModuleCat.{max u v w r} (Λ ⧸ I)) ∧
      (J.over X).PreservesSheafification
        (ModuleCat.restrictScalars.{max u v w r} (Ideal.Quotient.mk I)) :=
  ⟨hasSheafify_moduleCat.{max u v, v, r, max w r} _ _,
    hasSheafify_moduleCat.{max u v, v, r, max w r} _ _,
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{max u v w} (Ideal.Quotient.mk I))⟩

/-- **Restriction of coefficients preserves local constancy of finite type.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_restrictQuotientScalars
    (H : Sheaf J (ModuleCat.{max u v w r} (Λ ⧸ I)))
    (hH : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J (Λ ⧸ I) H) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J Λ
      ((restrictQuotientScalars.{u, v, max u v w r} J Λ I).obj H) := by
  intro U
  obtain ⟨ι, V, f, hcov, hV⟩ := hH U
  refine ⟨ι, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hV i
  refine ⟨(ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj E, ?_, ⟨?_⟩⟩
  · rw [ModuleCat.isFG_iff] at hE ⊢
    exact finite_restrictScalars_quotient I E
  · obtain ⟨_, _, _⟩ := hasSheafify_and_preservesSheafification_restrictScalars J Λ I (V i)
    exact ((restrictQuotientScalarsConstantSheafIso.{max u v, v, max u v w r, r}
        (J.over (V i)) Λ I).app E).symm ≪≫
      (restrictQuotientScalars.{max u v, v, max u v w r, r} (J.over (V i)) Λ I).mapIso e ≪≫
      (overPullbackRestrictQuotientScalarsIso.{u, v, max u v w r, r} J Λ I (V i)).app H

/-- **Local constancy of finite type is detected after restriction of coefficients.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_restrictQuotientScalars
    (H : Sheaf J (ModuleCat.{max u v w r} (Λ ⧸ I)))
    (hH : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J Λ
      ((restrictQuotientScalars.{u, v, max u v w r} J Λ I).obj H)) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J (Λ ⧸ I) H := by
  intro U
  obtain ⟨ι, V, f, hcov, hV⟩ := hH U
  refine ⟨ι, V, f, hcov, fun i => ?_⟩
  by_cases hbot : (⊥ : Sieve (V i)) ∈ J (V i)
  · exact isConstantFGOver_of_bot_mem.{v, u, max w r, r} J (Λ ⧸ I) hbot H
  obtain ⟨E, hE, ⟨e⟩⟩ := hV i
  have hsec : ∀ a ∈ I, ∀ x : E, a • x = 0 := by
    intro a ha x
    apply injective_sliceUnit.{v, u, max w r, r} (J := J) (Λ := Λ) hbot E
    apply (ConcreteCategory.bijective_of_isIso
      (e.hom.hom.app (op (Over.mk (𝟙 (V i)))))).1
    rw [map_smul, map_smul, map_zero, map_zero]
    change (Ideal.Quotient.mk I a) • _ = (0 : H.obj.obj (op (V i)))
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact zero_smul (Λ ⧸ I) _
  have htors : Module.IsTorsionBySet Λ E I := fun x a => hsec a a.2 x
  let : Module (Λ ⧸ I) E := htors.module
  let E' : ModuleCat.{max u v w r} (Λ ⧸ I) := ModuleCat.of (Λ ⧸ I) E
  let eE : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj E' ≅ E :=
    LinearEquiv.toModuleIso
      { toFun := fun x => (x : E)
        invFun := fun x => (x : E')
        map_add' := fun _ _ => rfl
        map_smul' := fun a x => (htors.mk_smul a x).symm
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨E', ?_, ⟨?_⟩⟩
  · rw [ModuleCat.isFG_iff] at hE ⊢
    exact Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ I) E
  · obtain ⟨_, _, _⟩ := hasSheafify_and_preservesSheafification_restrictScalars J Λ I (V i)
    have hff : (restrictQuotientScalars.{max u v, v, max u v w r, r} (J.over (V i)) Λ
        I).FullyFaithful :=
      fullyFaithfulRestrictQuotientScalars.{max u v w r, v, max u v, r} _ _ _
    exact hff.preimageIso
      ((restrictQuotientScalarsConstantSheafIso.{max u v, v, max u v w r, r}
          (J.over (V i)) Λ I).app E' ≪≫
        (constantSheaf (J.over (V i)) (ModuleCat.{max u v w r} Λ)).mapIso eE ≪≫ e ≪≫
        ((overPullbackRestrictQuotientScalarsIso.{u, v, max u v w r, r} J Λ I (V i)).app H).symm)

/-- **Local constancy of finite type along `Λ → Λ ⧸ I`.** A sheaf of `Λ ⧸ I`-modules is locally
constant of finite type exactly when it is so as a sheaf of `Λ`-modules. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_restrictQuotientScalars_iff
    (H : Sheaf J (ModuleCat.{max u v w r} (Λ ⧸ I))) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J Λ
        ((restrictQuotientScalars.{u, v, max u v w r} J Λ I).obj H) ↔
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, max w r} J (Λ ⧸ I) H :=
  ⟨isFiniteTypeLocallyConstantModuleSheaf_of_restrictQuotientScalars J Λ I H,
    isFiniteTypeLocallyConstantModuleSheaf_restrictQuotientScalars J Λ I H⟩

end Stacks.ModuleSheaf

end
