module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a finite locally free sheaf of modules is its top exterior power

Let `F` be a sheaf of modules on a topological space which is finite locally free of constant
rank `r`, and let `det(F) ⊆ ⋀(F)` be the determinant of [Stacks, Tag 0FJN], the annihilator of
the degree-one part of the exterior algebra, formed degree by degree. Then `⋀ʳ F ≅ det(F)`.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`: the
  identification `⋀ʳ F ≅ det(F)` for `F` finite locally free of constant rank `r`.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_of_rank`: every local
  section of `⋀ʳ F` is exterior annihilated.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isIso_exteriorAnnihilator_ι`: the inclusion
  `det(F)_r ⟶ ⋀ʳ F` of the degree-`r` annihilator is an isomorphism.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isZero_exteriorAnnihilator`: away from the
  rank the degreewise annihilator vanishes.
* `Stacks.ExteriorAnnihilator.part_eq_bot_of_free_of_ne` and
  `Stacks.ExteriorAnnihilator.part_eq_top_of_free`: for a finite free module the annihilator of
  the degree-one elements is concentrated in the degree equal to the rank, where it is everything.

## References

* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf

universe u v

/-! ### A coproduct with a single nonzero summand -/

namespace CategoryTheory.Limits

/-- **A coproduct in which every summand but one is zero is that summand.** -/
noncomputable def sigmaIsoOfIsZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} [DecidableEq ι] (P : ι → C) [HasCoproduct P] (r : ι)
    (h : ∀ i, i ≠ r → IsZero (P i)) : P r ≅ ∐ P where
  hom := Sigma.ι P r
  inv := Sigma.desc fun i => if hi : i = r then eqToHom (by rw [hi]) else 0
  hom_inv_id := by
    rw [Sigma.ι_comp_desc]
    simp
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Category.comp_id, ← Category.assoc, Sigma.ι_comp_desc]
    by_cases hi : i = r
    · subst hi
      simp
    · simp only [hi, dite_false, Limits.zero_comp]
      exact ((h i hi).eq_of_src (Sigma.ι P i) 0).symm

/-- The inclusion of the surviving summand of a coproduct all of whose other summands are zero
is an isomorphism. -/
theorem isIso_sigmaι_of_isZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} (P : ι → C) [HasCoproduct P] (r : ι)
    (h : ∀ i, i ≠ r → IsZero (P i)) : IsIso (Sigma.ι P r) :=
  open scoped Classical in
  inferInstanceAs (IsIso (sigmaIsoOfIsZero P r h).hom)

end CategoryTheory.Limits

/-! ### The exterior annihilator of a finite free module -/

namespace Stacks.ExteriorAnnihilator

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- For a finite free module the annihilator of the degree-one elements of the exterior algebra
is the exterior power in the degree equal to the rank. -/
theorem annihilator_eq_exteriorPower_of_free [Module.Finite R M] [Module.Free R M] :
    (⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) =
      ⋀[R]^(Module.finrank R M) M :=
  have : Module.Projective R M := Module.Projective.of_free
  (ProjectiveDeterminant.determinant_submodule_eq_annihilator R M).symm.trans
    (ProjectiveDeterminant.submodule_eq_exteriorPower_of_free (R := R) (M := M))

/-- **Away from the rank the degreewise annihilator of a finite free module vanishes.** -/
theorem part_eq_bot_of_free_of_ne [Module.Finite R M] [Module.Free R M] (n : ℕ)
    (hn : n ≠ Module.finrank R M) : part R M n = ⊥ := by
  have hann := annihilator_eq_exteriorPower_of_free (R := R) (M := M)
  have hindep : iSupIndep (fun i : ℕ => ⋀[R]^i M) :=
    (DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[R]^i M)).submodule_iSupIndep
  refine le_antisymm (fun y hy => ?_) bot_le
  have hy' : (y : ExteriorAlgebra R M) ∈ ⋀[R]^(Module.finrank R M) M := by rwa [← hann]
  have hmem : (y : ExteriorAlgebra R M) ∈ ⨆ (j : ℕ) (_ : j ≠ n), ⋀[R]^j M :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hn) hy')
  exact (Submodule.mem_bot _).2
    (Subtype.ext (Submodule.disjoint_def.mp (hindep n) _ y.2 hmem))

/-- **At the rank the degreewise annihilator of a finite free module is everything.** -/
theorem part_eq_top_of_free [Module.Finite R M] [Module.Free R M] :
    part R M (Module.finrank R M) = ⊤ := by
  refine le_antisymm le_top fun y _ => Submodule.mem_comap.2 ?_
  rw [annihilator_eq_exteriorPower_of_free]
  exact y.2

/-- **The degreewise annihilator of a module over a trivial ring vanishes.** -/
theorem part_eq_bot_of_subsingleton [Subsingleton R] (n : ℕ) : part R M n = ⊥ :=
  have hE : Subsingleton (ExteriorAlgebra R M) := Module.subsingleton R _
  have : Subsingleton (⋀[R]^n M) := ⟨fun _ _ => Subtype.ext (hE.elim _ _)⟩
  le_antisymm (fun _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)) bot_le

end Stacks.ExteriorAnnihilator

/-! ### The determinant at constant rank -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

open AlgebraicGeometry

/-- The coproduct over the degrees of the degreewise exterior annihilators, which is what
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant` is, written out as a named
instantiation of Mathlib's instance. -/
theorem hasCoproduct_exteriorAnnihilator {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {Osharp : Sheaf J CommRingCat.{u}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {F : SheafOfModules.{u} (CategoryTheory.Sheaf.toRingCat J Osharp)}
    (A : TensorExteriorSymmetricAlgebras J F) :
    HasCoproduct (fun n : ℕ => (A.exteriorAnnihilator n).toSheafOfModules) := inferInstance

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)

section Top

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- **At the rank every local section of `⋀ʳ F` is exterior annihilated.** -/
theorem isExteriorAnnihilated_of_rank {U : (Opens ↥X)ᵒᵖ}
    (z : ToType ((A.exteriorPower r).val.obj U)) : A.IsExteriorAnnihilated r z := by
  intro V f m
  exact (wedgeGen_eq_zero_iff r V m _).mp <|
    Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt A r (r + 1) (by omega) V _

/-- The degree-`r` exterior annihilator of a sheaf of modules of constant rank `r` is the whole
of `⋀ʳ F`. -/
theorem exteriorAnnihilator_eq_top : A.exteriorAnnihilator r = ⊤ :=
  le_antisymm le_top fun _ z _ => A.isExteriorAnnihilated_of_rank r z

/-- **The inclusion of the degree-`r` exterior annihilator into `⋀ʳ F` is an isomorphism**, for
`F` of constant rank `r`. -/
instance isIso_exteriorAnnihilator_ι : IsIso (A.exteriorAnnihilator r).ι := by
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap]
  intro x
  refine ⟨?_, ?_⟩
  · exact (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
      (A.exteriorAnnihilator r).ι).1 inferInstance x
  · intro ξ
    obtain ⟨U, hx, t, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (A.exteriorPower r).val.presheaf ξ
    refine ⟨TopCat.Presheaf.germ (A.exteriorAnnihilator r).toSheafOfModules.val.presheaf U x hx
      (show ToType ((A.exteriorAnnihilator r).toSheafOfModules.val.presheaf.obj (op U)) from
        ⟨t, A.isExteriorAnnihilated_of_rank r t⟩), ?_⟩
    exact AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x (A.exteriorAnnihilator r).ι U hx _

/-- **`⋀ʳ F` is the degree-`r` summand of `det(F)`**, for `F` of constant rank `r`. -/
noncomputable def exteriorPowerIsoAnnihilator :
    A.exteriorPower r ≅ (A.exteriorAnnihilator r).toSheafOfModules :=
  (asIso (A.exteriorAnnihilator r).ι).symm

end Top

/-! ### Vanishing away from the rank -/

section Vanishing

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (x : ↥X)

/-- **The degreewise annihilator in the stalk vanishes away from the rank.** -/
theorem part_stalk_eq_bot (n : ℕ) (hn : n ≠ r) :
    Stacks.ExteriorAnnihilator.part (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) n = ⊥ := by
  obtain ⟨e⟩ := Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp F r x
  by_cases htriv : Subsingleton (ToType (TopCat.Presheaf.stalk Osharp.obj x))
  · have := htriv
    exact Stacks.ExteriorAnnihilator.part_eq_bot_of_subsingleton n
  · have hnt : Nontrivial (ToType (TopCat.Presheaf.stalk Osharp.obj x)) :=
      not_subsingleton_iff_nontrivial.mp htriv
    have b : Module.Basis (Fin r) (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := Module.Basis.ofRepr e
    have hfree : Module.Free (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := Module.Free.of_basis b
    have hfin : Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := Module.Finite.of_basis b
    have hrank : Module.finrank (ToType (TopCat.Presheaf.stalk Osharp.obj x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) = r := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    exact Stacks.ExteriorAnnihilator.part_eq_bot_of_free_of_ne n (by rw [hrank]; exact hn)

/-- Every germ of the degree-`n` exterior annihilator vanishes when `n` is not the rank. -/
theorem subsingleton_stalk_exteriorAnnihilator (n : ℕ) (hn : n ≠ r) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
      (A.exteriorAnnihilator n).toSheafOfModules.val.presheaf x)) := by
  have key : ∀ a : ToType (TopCat.Presheaf.stalk
      (A.exteriorAnnihilator n).toSheafOfModules.val.presheaf x), a = 0 := by
    intro a
    refine injective_submoduleStalkι x ?_
    rw [map_zero]
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (A.exteriorAnnihilator n).toSheafOfModules.val.presheaf a
    rw [submoduleStalkι_germ x U hx s]
    refine A.germ_eq_zero_of_germWedge_eq_zero x n hx _ ?_
    have hmem : A.exteriorPowerStalkEquiv n x
        (Stacks.SheafOfModules.germ (A.exteriorPower n) x hx
          ((A.exteriorAnnihilator n).ι.val.app (op U) s)) ∈
        Stacks.ExteriorAnnihilator.part (ToType (TopCat.Presheaf.stalk Osharp.obj x))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) n :=
      (Stacks.ExteriorAnnihilator.mem_part_iff _).mpr fun μ =>
        A.mul_germWedge_eq_zero_of_isExteriorAnnihilated x n hx _ (Subtype.property s) μ
    exact congrArg Subtype.val
      ((Submodule.mem_bot _).1 ((part_stalk_eq_bot r x n hn).le hmem))
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **The degree-`n` exterior annihilator of a sheaf of modules of constant rank `r` vanishes
for `n ≠ r`.** -/
theorem isZero_exteriorAnnihilator (n : ℕ) (hn : n ≠ r) :
    IsZero ((A.exteriorAnnihilator n).toSheafOfModules) :=
  (IsZero.iff_id_eq_zero _).2
    (Stacks.SheafOfModules.TopWedge.id_eq_zero_of_subsingleton_stalk _
      fun y => A.subsingleton_stalk_exteriorAnnihilator r y n hn)

end Vanishing

/-! ### The identification of the determinant with the top exterior power -/

section Iso

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- The degree-`r` summand of `det(F)` is the whole of it, for `F` of constant rank `r`. -/
instance isIso_determinantSummand : IsIso (A.determinantSummand r) :=
  have := A.hasCoproduct_exteriorAnnihilator
  isIso_sigmaι_of_isZero (fun n : ℕ => (A.exteriorAnnihilator n).toSheafOfModules) r
    fun n hn => A.isZero_exteriorAnnihilator r n hn

/-- **The determinant at constant rank.** For a sheaf of modules `F` which is
finite locally free of constant rank `r`, the determinant `det(F)` — the annihilator of the
degree-one part of the exterior algebra — is the top exterior power `⋀ʳ F`. -/
@[sga "3 XV 5.7" "special case"]
noncomputable def determinantIsoExteriorPower : A.exteriorPower r ≅ A.determinant :=
  A.exteriorPowerIsoAnnihilator r ≪≫ asIso (A.determinantSummand r)

/-- The identification `⋀ʳ F ≅ det(F)` is the inverse of the inclusion of the degree-`r`
annihilator, followed by the degree-`r` summand inclusion of the determinant. -/
theorem determinantIsoExteriorPower_hom :
    (A.determinantIsoExteriorPower r).hom =
      (asIso (A.exteriorAnnihilator r).ι).inv ≫ A.determinantSummand r := rfl

/-- The inclusion of the degree-`r` annihilator into `⋀ʳ F`, composed with the identification
`⋀ʳ F ≅ det(F)`, is the degree-`r` summand inclusion. -/
theorem exteriorAnnihilator_ι_comp_determinantIsoExteriorPower :
    (A.exteriorAnnihilator r).ι ≫ (A.determinantIsoExteriorPower r).hom =
      A.determinantSummand r := by
  rw [determinantIsoExteriorPower_hom, ← Category.assoc]
  simp

end Iso

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
