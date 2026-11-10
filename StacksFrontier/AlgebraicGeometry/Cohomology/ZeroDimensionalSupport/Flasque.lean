module

public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport

/-!
# A coherent module with zero-dimensional support is flasque

Let `X` be a locally Noetherian scheme and let `F` be a coherent `𝒪_X`-module whose support has
topological Krull dimension at most zero. Then every restriction map of `F` is surjective.

## Main results

* `AlgebraicGeometry.exists_restrict_eq_of_support_dim_le_zero`: a section of `F` over an open
  `U` extends to any larger open `V`.
* `AlgebraicGeometry.isFlasque_of_support_dim_le_zero`: `F` is flasque.

## References

* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopologicalSpace.Opens (infLELeft infLERight)

universe u

namespace AlgebraicGeometry

/-- Every subset of the support of a coherent module with zero-dimensional support is closed. -/
theorem isClosed_of_subset_supp_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    {T : Set X} (hT : T ⊆ SheafOfModules.supp F) : IsClosed T := by
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyS : y ∈ SheafOfModules.supp F :=
    (SheafOfModules.isClosed_supp F).closure_subset (closure_mono hT hy)
  obtain ⟨N, hyN, hN⟩ := exists_open_neighborhood_meets_support_singleton F hF ⟨y, hyS⟩
  obtain ⟨z, hzN, hzT⟩ := mem_closure_iff.mp hy N N.2 hyN
  have hzy : z = y := hN z hzN (hT hzT)
  exact hzy ▸ hzT

/-- **A section of a coherent module with zero-dimensional support extends to any larger open.**
This is the surjectivity of the restriction maps of such a module. -/
theorem exists_restrict_eq_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0)
    {U V : X.Opens} (hUV : U ≤ V) (s : F.presheaf.obj (op U)) :
    ∃ t : F.presheaf.obj (op V), F.presheaf.map (homOfLE hUV).op t = s := by
  classical
  let S := SheafOfModules.supp F
  let T : Set X := {y | y ∈ S ∧ y ∈ U}
  have hTsub : T ⊆ S := fun _ hy => hy.1
  have hTclosed : IsClosed T := isClosed_of_subset_supp_of_support_dim_le_zero F hF hTsub
  choose N hmemN hN using fun z : T =>
    exists_open_neighborhood_meets_support_singleton F hF ⟨(z : X), hTsub z.2⟩
  let Tc : X.Opens := ⟨Tᶜ, hTclosed.isOpen_compl⟩
  let 𝒰 : Option T → X.Opens := fun
    | none => V ⊓ Tc
    | some z => N z ⊓ U
  let s𝒰 : ∀ i : Option T, F.presheaf.obj (op (𝒰 i)) := fun
    | none => 0
    | some z => F.presheaf.map (homOfLE (inf_le_right : N z ⊓ U ≤ U)).op s
  let iUV : ∀ i : Option T, 𝒰 i ⟶ V := fun
    | none => homOfLE inf_le_left
    | some z => homOfLE (le_trans inf_le_right hUV)
  have hsub : ∀ (z : T) (W : X.Opens), W ≤ 𝒰 none → W ≤ 𝒰 (some z) →
      Subsingleton (F.presheaf.obj (op W)) := fun z W hW₀ hWz =>
    subsingleton_sections_of_avoiding_support F W fun y hyW hyS =>
      (hW₀ hyW).2 (hN z y (hWz hyW).1 hyS ▸ z.2)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf 𝒰 s𝒰 := by
    intro i j
    match i, j with
    | none, none => rfl
    | none, some z => exact (hsub z _ inf_le_left inf_le_right).elim _ _
    | some z, none => exact (hsub z _ inf_le_right inf_le_left).elim _ _
    | some z, some w =>
      change F.presheaf.map _ (F.presheaf.map _ s) = F.presheaf.map _ (F.presheaf.map _ s)
      have hmaps : (homOfLE (inf_le_right : N z ⊓ U ≤ U)).op ≫
            (infLELeft (𝒰 (some z)) (𝒰 (some w))).op =
          (homOfLE (inf_le_right : N w ⊓ U ≤ U)).op ≫
            (infLERight (𝒰 (some z)) (𝒰 (some w))).op :=
        Subsingleton.elim _ _
      simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, hmaps]
  have hcover : V ≤ iSup 𝒰 := by
    intro y hy
    by_cases hyT : y ∈ T
    · exact Opens.mem_iSup.2 ⟨some ⟨y, hyT⟩, hmemN ⟨y, hyT⟩, hyT.2⟩
    · exact Opens.mem_iSup.2 ⟨none, hy, hyT⟩
  let Fsh : TopCat.Sheaf AddCommGrpCat X := ⟨F.presheaf, F.isSheaf⟩
  obtain ⟨t, ht, -⟩ := Fsh.existsUnique_gluing' 𝒰 V iUV hcover s𝒰 hcompat
  refine ⟨t, ?_⟩
  apply TopCat.Presheaf.section_ext Fsh U
  intro x hxU
  by_cases hxS : x ∈ S
  · let z : T := ⟨x, ⟨hxS, hxU⟩⟩
    have hxz : x ∈ 𝒰 (some z) := ⟨hmemN z, hxU⟩
    calc F.presheaf.germ U x hxU (F.presheaf.map (homOfLE hUV).op t)
        = F.presheaf.germ V x (hUV hxU) t := F.presheaf.germ_res_apply _ x hxU t
      _ = F.presheaf.germ (𝒰 (some z)) x hxz (F.presheaf.map (iUV (some z)).op t) :=
          (F.presheaf.germ_res_apply (iUV (some z)) x hxz t).symm
      _ = F.presheaf.germ (𝒰 (some z)) x hxz
            (F.presheaf.map (homOfLE (inf_le_right : N z ⊓ U ≤ U)).op s) := by
          rw [ht (some z)]
      _ = F.presheaf.germ U x hxU s := F.presheaf.germ_res_apply _ x hxz s
  · have hzero (c : F.presheaf.stalk x) : c = 0 := by_contra fun hne => hxS ⟨c, hne⟩
    exact (hzero _).trans (hzero _).symm

/-- **A coherent module whose support has dimension at most zero on a locally Noetherian scheme
is flasque.** -/
theorem isFlasque_of_support_dim_le_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0) :
    TopCat.Presheaf.IsFlasque (X := TopCat.of X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj where
  epi {V U} i := by
    have hle : U.unop ≤ V.unop := leOfHom i.unop
    have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
    subst hi
    exact ConcreteCategory.epi_of_surjective _ (exists_restrict_eq_of_support_dim_le_zero F hF hle)

end AlgebraicGeometry

end
