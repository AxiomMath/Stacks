module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicAnySite
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective

/-!
# Total acyclicity of a direct image with an exact left adjoint

Let `(C, J)` and `(D, K)` be sites and let `P : Sh(D, Ab) ⥤ Sh(C, Ab)` be a functor of abelian
sheaves with an exact left adjoint `Λ`. For an injective sheaf of modules `I` on `D`, the abelian
sheaf `P(I)` is totally acyclic (Stacks 072Y): its cohomology over every sheaf of sets on `C`
vanishes in positive degrees.

This is the argument of Stacks 072Z with the morphism of topoi replaced by the adjunction
`Λ ⊣ P` alone. It applies in particular to the restriction of abelian sheaves along a continuous
functor `u : C ⥤ D` with a left adjoint, whose own left adjoint is exact by Stacks 08NH
(`nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous`);
that is the comparison of the small étale site of a scheme-like algebraic space with the Zariski
site of the scheme, which is where it is used.

## Main results

* `Stacks.Cohomology.AdjointPushforward.isTorsionFree_obj`: an exact additive functor of abelian
  sheaves preserves sectionwise torsion-freeness.
* `Stacks.Cohomology.AdjointPushforward.ext_eq_zero_of_isTorsionFree`: `Ext` out of a
  sectionwise torsion-free abelian sheaf into `P(I)` vanishes in positive degrees.
* `Stacks.Cohomology.AdjointPushforward.isTotallyAcyclic_of_injective`: `P(I)` is totally
  acyclic.

## Implementation notes

The extension lemma `exists_extension_of_ext_one_eq_zero` is private to
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/PushforwardOfAnInjective.lean`, which is
therefore imported with `import all`, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicAnySite.lean`.

## References

* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 072Y](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Tag 08NH](https://stacks.math.columbia.edu/tag/08NH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe x w v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.AdjointPushforward

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]

omit [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
/-- **An exact additive functor of abelian sheaves preserves sectionwise torsion-freeness**:
multiplication by a nonzero integer is a monomorphism on a sectionwise torsion-free sheaf, and a
left exact additive functor keeps it one. -/
lemma isTorsionFree_obj (L : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
    [L.Additive] [PreservesFiniteLimits L] (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) (U : Dᵒᵖ) :
    Module.IsTorsionFree ℤ ((L.obj F).obj.obj U) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n y hy
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have hmono : Mono (n • 𝟙 F) := by
    have hmono' : Mono (n • 𝟙 F).hom := by
      have (V : Cᵒᵖ) : Mono ((n • 𝟙 F).hom.app V) := by
        have := hF V
        exact (AddCommGrpCat.mono_iff_injective _).2 (IsSMulRegular.of_ne_zero hn)
      exact NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map hmono'
  have hm : Mono (((sheafToPresheaf K AddCommGrpCat.{w}).map (L.map (n • 𝟙 F))).app U) :=
    inferInstance
  have hi := (AddCommGrpCat.mono_iff_injective _).mp hm
  rw [Functor.map_zsmul, L.map_id] at hi
  change Function.Injective (fun z : (L.obj F).obj.obj U => n • z) at hi
  exact hi (by simpa only [smul_zero] using hy)

variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{w})] [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  {Λ : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
  {P : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} (adj : Λ ⊣ P)
  [PreservesFiniteLimits Λ]
  (R : Sheaf K RingCat.{w}) (I : SheafOfModules.{w} R) [Injective I]

include adj in
/-- **The core of Stacks 072Z for a direct image with an exact left adjoint.** `Ext` out of a
sectionwise torsion-free abelian sheaf into `P` of the abelian sheaf underlying an injective
sheaf of modules vanishes in positive degree.

The dévissage `ModuleSheafCohomology.ext_eq_zero_of_resolving` reduces to degree one, where the
adjunction `Λ ⊣ P` turns the extension problem into one on the source of `Λ`; there the exact
functor `Λ` has produced a short exact sequence with torsion-free third term, against which the
underlying abelian sheaf of an injective module is `Ext`-acyclic,
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`. -/
theorem ext_eq_zero_of_isTorsionFree
    (T : Sheaf J AddCommGrpCat.{w}) (hT : ∀ U, Module.IsTorsionFree ℤ (T.obj.obj U)) (n : ℕ)
    (a : Ext.{x} T (P.obj ((SheafOfModules.toSheaf R).obj I)) (n + 1)) :
    a = 0 := by
  have := HasExt.standard (Sheaf K AddCommGrpCat.{w})
  have : Λ.Additive := Functor.additive_of_preserves_binary_products _
  have : P.Additive := adj.right_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} Λ := adj.leftAdjoint_preservesColimits
  refine ModuleSheafCohomology.ext_eq_zero_of_resolving
    (fun G : Sheaf J AddCommGrpCat.{w} => ∀ U, Module.IsTorsionFree ℤ (G.obj.obj U))
    (fun m _ hH => ModuleSheafCohomology.isTorsionFree_of_mono J m hH)
    (ModuleSheafCohomology.exists_isTorsionFree_epi J) _ ?_ n T hT a
  apply ModuleSheafCohomology.ext_one_eq_zero_of_extension
  intro S hS hP m
  obtain ⟨g, hg⟩ := exists_extension_of_ext_one_eq_zero
    (ShortComplex.ShortExact.map_of_exact hS Λ) _
    (fun e => ObjectSections.ext_eq_zero_of_isTorsionFree K R I _
      (isTorsionFree_obj Λ S.X₃ hP) 0 e)
    ((adj.homEquiv _ _).symm m)
  have hg' : Λ.map S.f ≫ g = (adj.homEquiv _ _).symm m := hg
  exact ⟨adj.homEquiv _ _ g, by
    rw [← adj.homEquiv_naturality_left, hg', Equiv.apply_symm_apply]⟩

include adj in
/-- **Stacks 072Z for a direct image with an exact left adjoint.** `P` of the abelian sheaf
underlying an injective sheaf of modules is totally acyclic. The free abelian sheaf on a sheaf
of sets is sectionwise torsion free, so this is `ext_eq_zero_of_isTorsionFree`. -/
theorem isTotallyAcyclic_of_injective :
    IsTotallyAcyclic J (P.obj ((SheafOfModules.toSheaf R).obj I)) := by
  intro T p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have h := ext_eq_zero_of_isTorsionFree adj R I _ (isTorsionFree_freeAbelianSheaf J T) n
  exact ⟨fun a b ↦ (h a).trans (h b).symm⟩

end Stacks.Cohomology.AdjointPushforward

end
