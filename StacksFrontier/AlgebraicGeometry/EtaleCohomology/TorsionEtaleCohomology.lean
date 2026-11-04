module

public import Mathlib.GroupTheory.Torsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Étale cohomology of a torsion abelian sheaf

Let `X` be a quasi-compact and quasi-separated scheme and let `𝓕` be a torsion abelian sheaf on
the small étale site of `X`. Then `H^n_étale(X, 𝓕)` is a torsion abelian group for every `n`.

The proof is the one of [Stacks, Tag 0DDC] (1): the sheaf `𝓕` is the union of its `d`-torsion
subsheaves `𝓕[d]`, étale cohomology of a quasi-compact and quasi-separated scheme commutes with
filtered colimits ([Stacks, Tag 03Q5]), and `H^n_étale(X, 𝓕[d])` is annihilated by `d`. The
filtration used here is indexed by the factorials, `d = n !`, which is cofinal among all `d` and
makes the index category the linear order `ℕ` rather than the divisibility order.

## Main definitions

* `Stacks.Torsion.torsionFiltration` — the filtration of an abelian sheaf by the kernels of
  multiplication by `n !`, as a diagram indexed by `ℕ`.
* `Stacks.Torsion.torsionFiltrationι` — the kernel inclusions of that filtration, as a natural
  transformation to the constant diagram.
* `Stacks.Torsion.torsionFiltrationDesc` — the induced map from the colimit of the filtration to
  the sheaf.

## Main results

* `Stacks.Torsion.isIso_torsionFiltrationDesc` — a torsion abelian sheaf is the colimit of its
  torsion filtration.
* `Stacks.Torsion.isAddTorsion_of_isIso_colimit_post` — on an arbitrary site, if an additive
  functor to abelian groups turns the torsion filtration of a torsion sheaf into a colimit, then
  its value at that sheaf is a torsion abelian group.
* `Stacks.EtaleCohomology.etaleCohomology_isAddTorsion` — Tag 0DDC (1): the étale cohomology
  groups of a torsion abelian sheaf on a quasi-compact and quasi-separated scheme are torsion.

## Implementation notes

Étale cohomology is the right derived functor of Mathlib's global sections functor
`CategoryTheory.Sheaf.Γ` on the small étale site, with coefficients `AddCommGrpCat.{max (u+1) v}`
for a scheme universe `u`, as elsewhere in the étale abelian development; the index category of
the filtration is `ULift.{max (u+1) v} ℕ`, so that it is small in the coefficient universe, which
is what Tag 03Q5 requires of a filtered system.

That the comparison map out of the colimit of the filtration is an isomorphism is checked by
showing it is both a monomorphism and an epimorphism. Monomorphy is the exactness of filtered
colimits in the Grothendieck abelian category of abelian sheaves, applied to the monomorphism
from the filtration to the constant diagram; epimorphy is local surjectivity, which is exactly
the local annihilation of sections expressing torsion. Sections of the kernel sheaf are computed
by the evaluation functor `Sheaf J AddCommGrpCat ⥤ AddCommGrpCat` at an object of the site, which
preserves limits.

Part (2) of Tag 0DDC, for an object of `D⁺(X_étale)` with torsion cohomology sheaves, is not
proved here. Its proof is the spectral sequence of a Cartan–Eilenberg resolution: Tag 015J
(`CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`) identifies the
`''E₂`-page of that spectral sequence with `R^pΓ(H^q(K))`, which part (1) makes torsion, and Tag
0132 (`HomologicalComplex₂.isBounded_and_converges_totalFiltration₂`) propagates a weak Serre
subcategory containing a whole page to the cohomology of the total complex. What is missing is
the weak Serre class of torsion abelian groups, and a bounded-below complex representing the
object of `D⁺`, together with the wiring of the two tags.

## References

* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe w v u

namespace Stacks.Torsion

/-! ### Colimits of constant diagrams over a filtered index category -/

section Const

variable (I : Type w) [SmallCategory I] [IsFiltered I] {A : Type u} [Category.{v} A] (X : A)

/-- A filtered category is nonempty. -/
private instance nonempty_of_isFiltered : Nonempty I := IsFiltered.nonempty

/-- The cocone on a constant diagram all of whose legs are the identity. -/
private def constCocone : Cocone ((Functor.const I).obj X) := ⟨X, 𝟙 _⟩

/-- Any two legs of a cocone on a constant diagram over a filtered index category agree: both
factor through the leg at an upper bound of the two indices. -/
private theorem const_ι_eq (t : Cocone ((Functor.const I).obj X)) (i j : I) :
    t.ι.app i = t.ι.app j := by
  have h₁ := t.ι.naturality (IsFiltered.leftToMax i j)
  have h₂ := t.ι.naturality (IsFiltered.rightToMax i j)
  simp only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp,
    Category.comp_id] at h₁ h₂
  rw [← h₁, ← h₂]

/-- The identity cocone on a constant diagram over a filtered index category is a colimit: a
cocone on it has a single leg up to equality, and that leg is the unique factorisation. -/
private def isColimitConstCocone : IsColimit (constCocone I X) where
  desc t := t.ι.app (Classical.arbitrary I)
  fac t j := (Category.id_comp _).trans (const_ι_eq I X t (Classical.arbitrary I) j)
  uniq _ m hm := (Category.id_comp m).symm.trans (hm (Classical.arbitrary I))

/-- The colimit of a constant diagram over a filtered index category is its value. -/
private def constColimitIso [HasColimitsOfShape I A] :
    colimit ((Functor.const I).obj X) ≅ X :=
  colimit.isoColimitCocone ⟨constCocone I X, isColimitConstCocone I X⟩

/-- Each leg of the colimit of a constant diagram is inverse to the identification of that
colimit with the value of the diagram. -/
private theorem ι_constColimitIso_hom [HasColimitsOfShape I A] (j : I) :
    colimit.ι ((Functor.const I).obj X) j ≫ (constColimitIso I X).hom = 𝟙 X := by
  simp [constColimitIso, constCocone]

end Const

/-! ### Kernels of multiplication by an integer -/

section Kernels

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] (F : Sheaf J AddCommGrpCat.{w})

/-- Multiplication by `k` is the zero endomorphism of the kernel of multiplication by `k`: it
becomes zero after composing with the kernel inclusion, which is a monomorphism. -/
private theorem nsmul_id_kernel_eq_zero (k : ℕ) : k • 𝟙 (kernel (k • 𝟙 F)) = 0 := by
  apply (cancel_mono (kernel.ι (k • 𝟙 F))).1
  have h0 := kernel.condition (k • 𝟙 F)
  rw [Preadditive.comp_nsmul, Category.comp_id] at h0
  simpa [Preadditive.nsmul_comp] using h0

/-- A section of an abelian sheaf annihilated by `k` is a section of the kernel of multiplication
by `k`: evaluation at an object of the site preserves kernels, and the kernel of multiplication
by `k` on an abelian group is the subgroup of elements annihilated by `k`. -/
private theorem exists_app_eq_of_nsmul_eq_zero (k : ℕ) (U : Cᵒᵖ)
    (x : F.obj.obj U) (hx : k • x = 0) :
    ∃ y : (kernel (k • 𝟙 F)).obj.obj U, (kernel.ι (k • 𝟙 F)).hom.app U y = x := by
  let E := (sheafToPresheaf J AddCommGrpCat.{w}) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  have hE : E.map (k • 𝟙 F) = k • 𝟙 (E.obj F) := by rw [E.map_nsmul, E.map_id]
  have hker : (E.map (k • 𝟙 F)) x = 0 := by
    rw [hE]
    simpa using hx
  let z : (kernel (E.map (k • 𝟙 F)) : AddCommGrpCat.{w}) :=
    (AddCommGrpCat.kernelIsoKer (E.map (k • 𝟙 F))).inv ⟨x, hker⟩
  have hz : (kernel.ι (E.map (k • 𝟙 F))) z = x :=
    ConcreteCategory.congr_hom (AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map (k • 𝟙 F)))
      (⟨x, hker⟩ : (AddCommGrpCat.Hom.hom (E.map (k • 𝟙 F))).ker)
  refine ⟨CategoryTheory.inv (kernelComparison (k • 𝟙 F) E) z, ?_⟩
  have h1 : kernelComparison (k • 𝟙 F) E ≫ kernel.ι (E.map (k • 𝟙 F))
      = (kernel.ι (k • 𝟙 F)).hom.app U := kernelComparison_comp_ι _ _
  have h2 := ConcreteCategory.congr_hom h1
    (CategoryTheory.inv (kernelComparison (k • 𝟙 F) E) z)
  simp only [CategoryTheory.comp_apply] at h2
  rw [← h2, ← CategoryTheory.comp_apply (CategoryTheory.inv (kernelComparison (k • 𝟙 F) E))
    (kernelComparison (k • 𝟙 F) E), IsIso.inv_hom_id]
  simpa using hz

end Kernels

/-! ### The filtration of an abelian sheaf by its torsion subsheaves -/

section Filtration

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] (F : Sheaf J AddCommGrpCat.{w})

/-- The filtration of an abelian sheaf by the kernels of multiplication by `n !`, indexed by `ℕ`
in its linear order: for `n ≤ m` the `n !`-torsion is contained in the `m !`-torsion because
`n !` divides `m !`. Every positive integer divides some factorial, so this filtration is cofinal
among the kernels of multiplication by a positive integer. -/
def torsionFiltration : ULift.{w, 0} ℕ ⥤ Sheaf J AddCommGrpCat.{w} where
  obj n := kernel ((Nat.factorial n.down) • 𝟙 F)
  map {n m} h := kernel.lift _ (kernel.ι _) (by
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show n.down ≤ m.down from h.le)
    have h0 : (Nat.factorial n.down : ℕ) • kernel.ι ((Nat.factorial n.down) • 𝟙 F) = 0 := by
      simpa [Preadditive.comp_nsmul] using kernel.condition ((Nat.factorial n.down) • 𝟙 F)
    rw [Preadditive.comp_nsmul, Category.comp_id, hc, mul_nsmul, h0, smul_zero])
  map_id n := by
    apply (cancel_mono (kernel.ι ((Nat.factorial n.down) • 𝟙 F))).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp

/-- The kernel inclusions of the torsion filtration, as a natural transformation to the constant
diagram at the sheaf. -/
def torsionFiltrationι :
    torsionFiltration J F ⟶ (Functor.const (ULift.{w, 0} ℕ)).obj F where
  app _ := kernel.ι _
  naturality _ _ _ := by simp [torsionFiltration]

/-- The map from the colimit of the torsion filtration of an abelian sheaf to the sheaf, induced
by the kernel inclusions. -/
def torsionFiltrationDesc : colimit (torsionFiltration J F) ⟶ F :=
  colimit.desc (torsionFiltration J F) (Cocone.mk F (torsionFiltrationι J F))

/-- Composing the `n`-th leg of the colimit of the torsion filtration with the map to the sheaf
gives the `n !`-torsion inclusion. -/
theorem ι_torsionFiltrationDesc (n : ULift.{w, 0} ℕ) :
    colimit.ι (torsionFiltration J F) n ≫ torsionFiltrationDesc J F
      = (torsionFiltrationι J F).app n :=
  colimit.ι_desc _ _

/-- The map out of the colimit of the torsion filtration is a monomorphism: filtered colimits are
exact in the Grothendieck abelian category of abelian sheaves, so they preserve the monomorphism
from the filtration to the constant diagram. -/
theorem mono_torsionFiltrationDesc [IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w})] :
    Mono (torsionFiltrationDesc J F) := by
  have happ : ∀ n : ULift.{w, 0} ℕ, Mono ((torsionFiltrationι J F).app n) := fun n =>
    (inferInstance : Mono (kernel.ι ((Nat.factorial n.down) • 𝟙 F)))
  have hmono : Mono (torsionFiltrationι J F) := NatTrans.mono_of_mono_app _
  have h1 : Mono (colim.map (torsionFiltrationι J F)) := Functor.map_mono _ _
  rw [colim_map] at h1
  have h : torsionFiltrationDesc J F
      = colimMap (torsionFiltrationι J F) ≫ (constColimitIso (ULift.{w, 0} ℕ) F).hom := by
    refine colimit.hom_ext fun n => ?_
    rw [ι_torsionFiltrationDesc, ← Category.assoc, ι_colimMap, Category.assoc,
      ι_constColimitIso_hom]
    exact (Category.comp_id _).symm
  rw [h]
  exact mono_comp _ _

/-- The map out of the colimit of the torsion filtration of a *torsion* sheaf is locally
surjective, hence an epimorphism: a section of a torsion sheaf is, on each member of a covering
sieve, annihilated by a positive integer, hence a section of one of the kernels making up the
filtration. -/
theorem isLocallySurjective_torsionFiltrationDesc (hF : torsionSheafProperty J F) :
    Sheaf.IsLocallySurjective (torsionFiltrationDesc J F) := by
  constructor
  intro U s
  obtain ⟨R, hR, hann⟩ := hF U s
  refine J.superset_covering ?_ hR
  intro V f hf
  obtain ⟨n, hn, hzero⟩ := hann V f hf
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hn le_rfl
  have hfact : (Nat.factorial n) • (F.obj.map f.op s) = 0 := by
    rw [hc, mul_nsmul, hzero, smul_zero]
  obtain ⟨y, hy⟩ :=
    exists_app_eq_of_nsmul_eq_zero J F (Nat.factorial n) (op V) (F.obj.map f.op s) hfact
  refine ⟨(colimit.ι (torsionFiltration J F) ⟨n⟩).hom.app (op V) y, ?_⟩
  have h2 := ConcreteCategory.congr_hom
    (congr_app ((sheafToPresheaf J AddCommGrpCat.{w}).congr_map
      (ι_torsionFiltrationDesc J F ⟨n⟩)) (op V)) y
  simp only [Functor.map_comp, NatTrans.comp_app] at h2
  exact h2.trans hy

/-- A torsion abelian sheaf is the colimit of its torsion filtration. This is the union
`𝓕 = ⋃ 𝓕[d]` of [Stacks, Tag 0DDC]. -/
theorem isIso_torsionFiltrationDesc [IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w})]
    (hF : torsionSheafProperty J F) : IsIso (torsionFiltrationDesc J F) := by
  have := mono_torsionFiltrationDesc J F
  have := isLocallySurjective_torsionFiltrationDesc J F hF
  have : Epi (torsionFiltrationDesc J F) := Sheaf.epi_of_isLocallySurjective _
  exact isIso_of_mono_of_epi _

/-- Every element of the value of an additive functor at the `n !`-th stage of the torsion
filtration is annihilated by `n !`: multiplication by `n !` is the zero endomorphism of that
stage, and an additive functor takes it to the zero endomorphism. -/
theorem nsmul_eq_zero_of_mem_torsionFiltration
    (G : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w}) [G.Additive] (n : ULift.{w, 0} ℕ)
    (y : G.obj ((torsionFiltration J F).obj n)) : (Nat.factorial n.down) • y = 0 := by
  have hzero : (Nat.factorial n.down) • 𝟙 ((torsionFiltration J F).obj n) = 0 :=
    nsmul_id_kernel_eq_zero J F _
  have hG : (Nat.factorial n.down) • 𝟙 (G.obj ((torsionFiltration J F).obj n)) = 0 := by
    rw [← G.map_id, ← G.map_nsmul, hzero, G.map_zero]
  simpa using ConcreteCategory.congr_hom hG y

/-- If an additive functor to abelian groups carries the torsion filtration of a torsion abelian
sheaf to a colimit, then its value at that sheaf is a torsion abelian group: every element comes
from some stage of the filtration, and the stage `n !` is annihilated by `n !`. -/
theorem isAddTorsion_of_isIso_colimit_post
    [IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w})] (hF : torsionSheafProperty J F)
    (G : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w}) [G.Additive]
    (h : IsIso (colimit.post (torsionFiltration J F) G)) :
    IsAddTorsion (G.obj F) := by
  have hd : IsIso (torsionFiltrationDesc J F) := isIso_torsionFiltrationDesc J F hF
  intro x
  let z : (colimit (torsionFiltration J F ⋙ G) : AddCommGrpCat.{w}) :=
    (CategoryTheory.inv (colimit.post (torsionFiltration J F) G))
      ((G.map (CategoryTheory.inv (torsionFiltrationDesc J F))) x)
  obtain ⟨j, y, hy⟩ := Concrete.colimit_exists_rep (torsionFiltration J F ⋙ G) z
  have hpost : (G.map (colimit.ι (torsionFiltration J F) j)) y
      = (G.map (CategoryTheory.inv (torsionFiltrationDesc J F))) x := by
    have h1 := ConcreteCategory.congr_hom (colimit.ι_post (torsionFiltration J F) G j) y
    simp only [CategoryTheory.comp_apply] at h1
    rw [← h1, hy]
    exact IsIso.inv_hom_id_apply _ _
  have key : (G.map (colimit.ι (torsionFiltration J F) j ≫ torsionFiltrationDesc J F)) y = x := by
    rw [G.map_comp, CategoryTheory.comp_apply, hpost, ← CategoryTheory.comp_apply, ← G.map_comp,
      IsIso.inv_hom_id, G.map_id, CategoryTheory.id_apply]
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Nat.factorial j.down, Nat.factorial_pos _, ?_⟩
  rw [← key, ← map_nsmul, nsmul_eq_zero_of_mem_torsionFiltration J F G j y, map_zero]

end Filtration

end Stacks.Torsion

namespace Stacks.EtaleCohomology

section Additivity

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

-- NO `injectiveResolutions_additive` HERE. It re-proved the public instance
-- `additive_injectiveResolutions`
-- (`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean`:65),
-- which this module now imports; `infer_instance` below finds it directly.

-- NO `rightDerived_additive` HERE either. It stated and proved, character for character,
-- the public instance `CategoryTheory.Functor.additive_rightDerived` of the SAME module this
-- file already imports for `additive_injectiveResolutions`
-- (`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean`:89).

end Additivity

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- The right derived functors of global sections on the small étale site are additive, global
sections being additive and right derived functors of an additive functor additive. -/
instance additive_rightDerived_Γ_smallEtale (X : Scheme.{u}) (n : ℕ) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n).Additive :=
  Functor.additive_rightDerived _ n

/-- **Stacks 0DDC (1).** Let `X` be a quasi-compact and quasi-separated scheme. If `𝓕` is a
torsion abelian sheaf on the small étale site of `X`, then `H^n_étale(X, 𝓕)` is a torsion abelian
group for every `n`. Indeed `𝓕` is the colimit of its torsion subsheaves, étale cohomology of a
quasi-compact and quasi-separated scheme commutes with filtered colimits, and the cohomology of
the `d`-torsion subsheaf is annihilated by `d`. -/
@[stacks 0DDC "part (1) only, with no extra hypothesis; étale cohomology is the right derived
functor of global sections on the small étale site. Part (2) is not proved here",
  sga "4 IX 1.2" "(ii), (v)"]
theorem etaleCohomology_isAddTorsion (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    IsAddTorsion
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n).obj F) :=
  Stacks.Torsion.isAddTorsion_of_isIso_colimit_post X.smallEtaleTopology F hF _
    (isIso_colimit_post_rightDerived_Γ_smallEtale.{v} X n _)

end Stacks.EtaleCohomology

end
