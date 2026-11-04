module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.SetTheory.Ordinal.Basic
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of limits of inverse systems of complexes

Stacks, Homological Algebra, Section 12.31: the cohomology in degree 0 of the limit of a tower of
complexes of abelian groups, under Mittag-Leffler and essential-constancy hypotheses, is the limit
of the cohomologies (070E); and the limit of an ordinal-indexed inverse system of acyclic complexes
of abelian groups with surjective comparison maps is acyclic (0AAT).
-/

@[expose] public section

section

/-!
## Stacks tag 070E

Let `A^{-2}_i → A^{-1}_i → A^0_i → A^1_i` be an inverse system of complexes of abelian groups
indexed by `ℕᵒᵖ`. If `(A^{-2}_i)` and `(A^{-1}_i)` are Mittag-Leffler and the system `(H^{-1}_i)`
of cohomologies is essentially constant, then the cohomology in degree `0` of the limit complex
is the limit of the cohomologies `H^0_i`.

## Main results

* `isIso_comparisonHomologyLimit_of_isMittagLeffler`: the comparison map `comparisonHomologyLimit`
  is an isomorphism.
* `isMittagLeffler_of_shortExact`: Mittag-Leffler towers are closed under extensions.

## Proof outline

The cycles `(Z^{-1}_i)` are an extension of `(H^{-1}_i)` by the boundaries, a quotient of
`(A^{-2}_i)`, so they are Mittag-Leffler. They form the kernel of the boundary map
`A^{-1} → Z^0`, so two applications of Stacks 02N1 show that taking limits is exact on
`A^{-1} → Z^0 → H^0 → 0`. The limits of `(Z^0_i)` and `(H^0_i)` then form a left homology datum
for the limit complex, whose homology isomorphism is the comparison map.
-/

open CategoryTheory CategoryTheory.Limits

universe v w

/-- Given a chain `A ⟶ B ⟶ C` of natural transformations of inverse systems of
abelian groups with composition zero, the short complex at index `i`. -/
@[implicit_reducible, simps]
noncomputable def invSystemShortComplex {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0)
    (i : ℕᵒᵖ) : ShortComplex Ab.{v} :=
  ShortComplex.mk (f.app i) (g.app i) (h i)

/-- The morphism of short complexes `invSystemShortComplex f g h i ⟶ invSystemShortComplex f g h j`
given by the transition maps. -/
@[implicit_reducible, simps]
noncomputable def invSystemShortComplexMap {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) {i j : ℕᵒᵖ} (φ : i ⟶ j) :
    invSystemShortComplex f g h i ⟶ invSystemShortComplex f g h j where
  τ₁ := A.map φ
  τ₂ := B.map φ
  τ₃ := C.map φ
  comm₁₂ := f.naturality φ
  comm₂₃ := g.naturality φ

/-- `invSystemShortComplexMap` preserves identities. -/
@[simp]
lemma invSystemShortComplexMap_id {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) (i : ℕᵒᵖ) :
    invSystemShortComplexMap f g h (𝟙 i) = 𝟙 _ := by
  ext : 1 <;> simp

/-- `invSystemShortComplexMap` preserves composition. -/
@[simp]
lemma invSystemShortComplexMap_comp {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) {i j k : ℕᵒᵖ} (φ : i ⟶ j)
    (ψ : j ⟶ k) :
    invSystemShortComplexMap f g h (φ ≫ ψ) =
      invSystemShortComplexMap f g h φ ≫ invSystemShortComplexMap f g h ψ := by
  ext : 1 <;> simp

/-- The functor sending `i ↦ invSystemShortComplex f g h i`. -/
@[implicit_reducible, simps]
noncomputable def invSystemShortComplexFunctor {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) :
    ℕᵒᵖ ⥤ ShortComplex Ab.{v} where
  obj i := invSystemShortComplex f g h i
  map φ := invSystemShortComplexMap f g h φ

/-- The short complex `(limMap f, limMap g)` obtained by taking limits of the
natural transformations. -/
@[implicit_reducible, simps]
noncomputable def limitShortComplexOfInvSystem {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) :
    ShortComplex Ab.{v} :=
  ShortComplex.mk (limMap f) (limMap g) (limit.hom_ext fun j => by simp [h])

/-- The inverse system `(H_i)` of homologies. -/
@[implicit_reducible]
noncomputable def homologyInvSystem {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) :
    ℕᵒᵖ ⥤ Ab.{v} :=
  invSystemShortComplexFunctor f g h ⋙ ShortComplex.homologyFunctor Ab.{v}

/-- The morphism from the limit short complex to the short complex at index `i`, given by the
limit projections. -/
@[simps]
noncomputable def limitShortComplexπ {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) (i : ℕᵒᵖ) :
    limitShortComplexOfInvSystem f g h ⟶ invSystemShortComplex f g h i where
  τ₁ := limit.π A i
  τ₂ := limit.π B i
  τ₃ := limit.π C i
  comm₁₂ := (limMap_π f i).symm
  comm₂₃ := (limMap_π g i).symm

/-- The cone over `invSystemShortComplexFunctor f g h` with apex the limit short complex. -/
noncomputable def limitShortComplexCone {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) :
    Cone (invSystemShortComplexFunctor f g h) where
  pt := limitShortComplexOfInvSystem f g h
  π :=
    { app := limitShortComplexπ f g h
      naturality _ _ φ := by ext <;> simp }

/-- The canonical morphism from the homology of the limit short complex to the
limit of the inverse system of homologies. -/
@[ega "0 13.2.3" "special case"]
noncomputable def comparisonHomologyLimit {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0) :
    (limitShortComplexOfInvSystem f g h).homology ⟶
      limit (homologyInvSystem f g h) :=
  limit.lift (homologyInvSystem f g h)
    ((ShortComplex.homologyFunctor Ab.{v}).mapCone (limitShortComplexCone f g h))

/-- An essentially constant tower of abelian groups is Mittag-Leffler. -/
lemma isMittagLeffler_of_isEssentiallyConstantPro (F : ℕᵒᵖ ⥤ Ab.{v})
    (h : EssentiallyConstantPro.IsEssentiallyConstantPro F) : (F ⋙ forget Ab).IsMittagLeffler := by
  obtain ⟨c, i, s, hs⟩ := h
  rw [Functor.isMittagLeffler_iff_subset_range_comp]
  intro j
  obtain ⟨k, σ, τ, hτ⟩ := hs.cofinal j
  refine ⟨k, τ, fun l g y ⟨a, ha⟩ => ⟨c.π.app l (s (F.map σ a)), ?_⟩⟩
  have hc := ConcreteCategory.congr_hom (c.w (g ≫ τ)) (s (F.map σ a))
  have hτa := ConcreteCategory.congr_hom hτ a
  simp only [ConcreteCategory.comp_apply] at hc hτa
  simp only [← ha, Functor.comp_map, TypeCat.ofHom_apply]
  rw [hc, hτa]

/-- The kernel of an epimorphism of towers is short exact. -/
private lemma shortExact_kernel_ι {F G : ℕᵒᵖ ⥤ Ab.{v}} (p : F ⟶ G) [Epi p] :
    (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
  { exact := ShortComplex.exact_kernel p }

/-- A quotient of a Mittag-Leffler tower of abelian groups is Mittag-Leffler. -/
lemma isMittagLeffler_of_epi {F G : ℕᵒᵖ ⥤ Ab.{v}} (p : F ⟶ G) [Epi p]
    (hF : (F ⋙ forget Ab).IsMittagLeffler) : (G ⋙ forget Ab).IsMittagLeffler :=
  Ab.isMittagLeffler_X₃_of_shortExact _ (shortExact_kernel_ι p) hF

/-- In a short exact sequence of towers of abelian groups whose outer towers are
Mittag-Leffler, the middle tower is Mittag-Leffler. -/
@[ega "0 13.2.1" "(ii), systems over ℕ"]
lemma isMittagLeffler_of_shortExact (S : ShortComplex (ℕᵒᵖ ⥤ Ab.{v})) (hS : S.ShortExact)
    (h₁ : (S.X₁ ⋙ forget Ab).IsMittagLeffler) (h₃ : (S.X₃ ⋙ forget Ab).IsMittagLeffler) :
    (S.X₂ ⋙ forget Ab).IsMittagLeffler := by
  have hsurj (n : ℕᵒᵖ) : Function.Surjective (S.g.app n) :=
    (AddCommGrpCat.epi_iff_surjective _).1 (hS.map_of_exact ((evaluation ℕᵒᵖ Ab.{v}).obj n)).epi_g
  have hex (n : ℕᵒᵖ) (b : S.X₂.obj n) (hb : S.g.app n b = 0) : ∃ a, S.f.app n a = b :=
    (S.map ((evaluation ℕᵒᵖ Ab.{v}).obj n)).ab_exact_iff.1
      (hS.map_of_exact ((evaluation ℕᵒᵖ Ab.{v}).obj n)).exact b hb
  rw [Functor.isMittagLeffler_iff_subset_range_comp] at h₁ h₃ ⊢
  intro j
  obtain ⟨m, f, hf⟩ := h₁ j
  obtain ⟨n, g, hg⟩ := h₃ m
  refine ⟨n, g ≫ f, fun k χ y ⟨b, hb⟩ => ?_⟩
  subst hb
  obtain ⟨c, hc⟩ := hg χ ⟨S.g.app n b, rfl⟩
  obtain ⟨b', rfl⟩ := hsurj k c
  have hc' : S.X₃.map (χ ≫ g) (S.g.app k b') = S.X₃.map g (S.g.app n b) := by simpa using hc
  obtain ⟨a, ha⟩ := hex m (S.X₂.map g b - S.X₂.map (χ ≫ g) b') (by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hc', sub_self])
  obtain ⟨a', ha'⟩ := hf (χ ≫ g) ⟨a, rfl⟩
  have ha'' : S.X₁.map (χ ≫ g ≫ f) a' = S.X₁.map f a := by simpa using ha'
  refine ⟨b' + S.f.app k a', ?_⟩
  simp only [Functor.comp_map, TypeCat.ofHom_apply, map_add, ← NatTrans.naturality_apply, ha'']
  rw [NatTrans.naturality_apply, ha, map_sub]
  simp

namespace InverseSystemCycles

variable {A B C : ℕᵒᵖ ⥤ Ab.{v}}
variable (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0)

/-- The tower of cycles. -/
@[implicit_reducible]
noncomputable def cycles : ℕᵒᵖ ⥤ Ab.{v} :=
  invSystemShortComplexFunctor f g h ⋙ ShortComplex.cyclesFunctor Ab.{v}

/-- The inclusion of the cycles. -/
@[implicit_reducible]
noncomputable def inclusion : cycles f g h ⟶ B where
  app i := (invSystemShortComplex f g h i).iCycles
  naturality _ _ φ := ShortComplex.cyclesMap_i (invSystemShortComplexMap f g h φ)

/-- The map from the first term to the cycles. -/
@[implicit_reducible]
noncomputable def toCycles : A ⟶ cycles f g h where
  app i := (invSystemShortComplex f g h i).toCycles
  naturality _ _ φ :=
    (ShortComplex.toCycles_naturality (invSystemShortComplexMap f g h φ)).symm

/-- The projection from the cycles to the homology. -/
@[implicit_reducible]
noncomputable def projection : cycles f g h ⟶ homologyInvSystem f g h where
  app i := (invSystemShortComplex f g h i).homologyπ
  naturality _ _ φ :=
    (ShortComplex.homologyπ_naturality (invSystemShortComplexMap f g h φ)).symm

/-- The cycles at index `i` are killed by `g`. -/
lemma inclusion_app_g (i : ℕᵒᵖ) : (inclusion f g h).app i ≫ g.app i = 0 :=
  (invSystemShortComplex f g h i).iCycles_g

/-- At index `i`, the boundary map followed by the inclusion of the cycles is `f`. -/
lemma toCycles_app_inclusion_app (i : ℕᵒᵖ) :
    (toCycles f g h).app i ≫ (inclusion f g h).app i = f.app i :=
  (invSystemShortComplex f g h i).toCycles_i

/-- The boundaries at index `i` are killed by the homology projection. -/
lemma toCycles_app_projection_app (i : ℕᵒᵖ) :
    (toCycles f g h).app i ≫ (projection f g h).app i = 0 :=
  (invSystemShortComplex f g h i).toCycles_comp_homologyπ

instance (i : ℕᵒᵖ) : Mono ((inclusion f g h).app i) :=
  inferInstanceAs (Mono (invSystemShortComplex f g h i).iCycles)

instance (i : ℕᵒᵖ) : Epi ((projection f g h).app i) :=
  inferInstanceAs (Epi (invSystemShortComplex f g h i).homologyπ)

/-- The cycles are killed by `g`. -/
lemma inclusion_g : inclusion f g h ≫ g = 0 := by
  ext i : 2
  rw [NatTrans.comp_app, inclusion_app_g, NatTrans.app_zero]

/-- The boundary map followed by the inclusion of the cycles is `f`. -/
lemma toCycles_inclusion : toCycles f g h ≫ inclusion f g h = f := by
  ext i : 2
  rw [NatTrans.comp_app, toCycles_app_inclusion_app]

/-- The boundaries are killed by the homology projection. -/
lemma toCycles_projection : toCycles f g h ≫ projection f g h = 0 := by
  ext i : 2
  rw [NatTrans.comp_app, toCycles_app_projection_app, NatTrans.app_zero]

/-- A morphism of towers killed by `g` is killed by `g` at every index. -/
lemma app_comp_g {X : ℕᵒᵖ ⥤ Ab.{v}} (k : X ⟶ B) (hk : k ≫ g = 0) (i : ℕᵒᵖ) :
    k.app i ≫ (invSystemShortComplex f g h i).g = 0 := by
  simpa using NatTrans.congr_app hk i

/-- A morphism out of the cycles killing the boundaries does so at every index. -/
lemma toCycles_app_comp {X : ℕᵒᵖ ⥤ Ab.{v}} (k : cycles f g h ⟶ X)
    (hk : toCycles f g h ≫ k = 0) (i : ℕᵒᵖ) : (toCycles f g h).app i ≫ k.app i = 0 := by
  rw [← NatTrans.comp_app, hk, NatTrans.app_zero]

/-- The morphism into the cycles at index `i` induced by a morphism killed by `g`. -/
noncomputable def liftCyclesApp {X : ℕᵒᵖ ⥤ Ab.{v}} (k : X ⟶ B) (hk : k ≫ g = 0) (i : ℕᵒᵖ) :
    X.obj i ⟶ (cycles f g h).obj i :=
  (invSystemShortComplex f g h i).liftCycles (k.app i) (app_comp_g f g h k hk i)

/-- `liftCyclesApp k hk i` followed by the inclusion of the cycles is `k.app i`. -/
@[reassoc]
lemma liftCyclesApp_inclusion_app {X : ℕᵒᵖ ⥤ Ab.{v}} (k : X ⟶ B) (hk : k ≫ g = 0)
    (i : ℕᵒᵖ) : liftCyclesApp f g h k hk i ≫ (inclusion f g h).app i = k.app i :=
  (invSystemShortComplex f g h i).liftCycles_i _ _

/-- The cycle inclusions form a kernel in the category of towers. -/
noncomputable def cyclesIsKernel :
    IsLimit (KernelFork.ofι (inclusion f g h) (inclusion_g f g h)) :=
  KernelFork.IsLimit.ofι _ _
    (fun k hk =>
      { app := liftCyclesApp f g h k hk
        naturality := fun i j φ => by
          rw [← cancel_mono ((inclusion f g h).app j), Category.assoc, Category.assoc,
            liftCyclesApp_inclusion_app, (inclusion f g h).naturality,
            liftCyclesApp_inclusion_app_assoc]
          exact k.naturality φ })
    (fun k hk => by
      ext i : 2
      rw [NatTrans.comp_app]
      exact liftCyclesApp_inclusion_app f g h k hk i)
    (fun k hk l hl => by
      ext i : 2
      rw [← cancel_mono ((inclusion f g h).app i), ← NatTrans.comp_app, hl]
      exact (liftCyclesApp_inclusion_app f g h k hk i).symm)

/-- The morphism out of the homology at index `i` induced by a morphism out of the cycles that
kills the boundaries. -/
@[implicit_reducible]
noncomputable def descHomologyApp {X : ℕᵒᵖ ⥤ Ab.{v}} (k : cycles f g h ⟶ X)
    (hk : toCycles f g h ≫ k = 0) (i : ℕᵒᵖ) : (homologyInvSystem f g h).obj i ⟶ X.obj i :=
  (invSystemShortComplex f g h i).descHomology (k.app i) (toCycles_app_comp f g h k hk i)

/-- The homology projection followed by `descHomologyApp k hk i` is `k`, at index `i`. -/
@[reassoc]
lemma projection_app_descHomologyApp {X : ℕᵒᵖ ⥤ Ab.{v}} (k : cycles f g h ⟶ X)
    (hk : toCycles f g h ≫ k = 0) (i : ℕᵒᵖ) :
    (projection f g h).app i ≫ descHomologyApp f g h k hk i = k.app i :=
  ShortComplex.π_descHomology _ _ _

/-- The morphism out of the homology tower induced by a morphism out of the cycles that kills
the boundaries. -/
@[implicit_reducible]
noncomputable def descHomology {X : ℕᵒᵖ ⥤ Ab.{v}} (k : cycles f g h ⟶ X)
    (hk : toCycles f g h ≫ k = 0) : homologyInvSystem f g h ⟶ X where
  app := descHomologyApp f g h k hk
  naturality i j φ := by
    rw [← cancel_epi ((projection f g h).app i), ← (projection f g h).naturality_assoc,
      projection_app_descHomologyApp, projection_app_descHomologyApp_assoc]
    exact k.naturality φ

/-- The homology projection followed by `descHomology k hk` is `k`. -/
lemma projection_descHomology {X : ℕᵒᵖ ⥤ Ab.{v}} (k : cycles f g h ⟶ X)
    (hk : toCycles f g h ≫ k = 0) : projection f g h ≫ descHomology f g h k hk = k := by
  ext i : 2
  rw [NatTrans.comp_app]
  exact projection_app_descHomologyApp f g h k hk i

/-- Morphisms out of the homology tower are determined by their composites with the
projection. -/
lemma projection_hom_ext {X : ℕᵒᵖ ⥤ Ab.{v}} {l l' : homologyInvSystem f g h ⟶ X}
    (hl : projection f g h ≫ l = projection f g h ≫ l') : l = l' := by
  ext i : 2
  rw [← cancel_epi ((projection f g h).app i), ← NatTrans.comp_app, hl, NatTrans.comp_app]

/-- The homology projections form the cokernel of the boundary map. -/
noncomputable def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ (projection f g h) (toCycles_projection f g h)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun k hk => descHomology f g h k hk)
    (fun k hk => projection_descHomology f g h k hk)
    (fun k hk _ hl => projection_hom_ext f g h (hl.trans (projection_descHomology f g h k hk).symm))

instance : Mono (inclusion f g h) := NatTrans.mono_of_mono_app _

instance : Epi (projection f g h) := NatTrans.epi_of_epi_app _

/-- The boundary short complex `A → Z → H` of towers. -/
@[implicit_reducible, simps]
noncomputable def boundarySC : ShortComplex (ℕᵒᵖ ⥤ Ab.{v}) :=
  ShortComplex.mk (toCycles f g h) (projection f g h) (toCycles_projection f g h)

instance : Epi (boundarySC f g h).g := by
  rw [boundarySC_g]
  infer_instance

/-- The boundary short complex is exact. -/
lemma boundarySC_exact : (boundarySC f g h).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (projectionIsCokernel f g h)

/-- The boundaries are a quotient of the first term, hence inherit Mittag-Leffler. -/
@[ega "0 13.2.4" "partial"]
lemma boundaries_isMittagLeffler (hA : (A ⋙ forget Ab).IsMittagLeffler) :
    (kernel (projection f g h) ⋙ forget Ab).IsMittagLeffler :=
  have := (boundarySC_exact f g h).epi_kernelLift
  isMittagLeffler_of_epi (kernel.lift (boundarySC f g h).g (boundarySC f g h).f
    (boundarySC f g h).zero) hA

/-- The kernel of the boundary map `A → Z` is isomorphic to the kernel of `f`. -/
noncomputable def kernelToCyclesIso : kernel (toCycles f g h) ≅ kernel f :=
  (kernelCompMono (toCycles f g h) (inclusion f g h)).symm ≪≫
    kernelIsoOfEq (toCycles_inclusion f g h)

/-- The cycles tower is the kernel of `g`. -/
noncomputable def cyclesIsoKernel : cycles f g h ≅ kernel g :=
  (cyclesIsKernel f g h).conePointUniqueUpToIso (limit.isLimit _)

end InverseSystemCycles

open InverseSystemCycles

/-- If `(A^{-2}_i)` is Mittag-Leffler and `(H^{-1}_i)` is essentially constant, then the tower of
cycles `(Z^{-1}_i)` is Mittag-Leffler. -/
lemma cycles_isMittagLeffler {A_neg2 A_neg1 A_0 : ℕᵒᵖ ⥤ Ab.{v}}
    (d_neg2 : A_neg2 ⟶ A_neg1) (d_neg1 : A_neg1 ⟶ A_0)
    (h_neg1 : ∀ i, d_neg2.app i ≫ d_neg1.app i = 0)
    (hML_neg2 : (A_neg2 ⋙ forget Ab).IsMittagLeffler)
    (hEC : EssentiallyConstantPro.IsEssentiallyConstantPro
        (homologyInvSystem d_neg2 d_neg1 h_neg1)) :
    (cycles d_neg2 d_neg1 h_neg1 ⋙ forget Ab).IsMittagLeffler :=
  isMittagLeffler_of_shortExact _ (shortExact_kernel_ι (projection d_neg2 d_neg1 h_neg1))
    (boundaries_isMittagLeffler d_neg2 d_neg1 h_neg1 hML_neg2)
    (isMittagLeffler_of_isEssentiallyConstantPro _ hEC)

/-- Let `T` be an exact sequence of towers with epimorphic second map. If `T.X₁` and the kernel
of `T.f` are Mittag-Leffler, then the limit sequence is exact and its second map is an
epimorphism. -/
lemma limit_exact_of_isMittagLeffler (T : ShortComplex (ℕᵒᵖ ⥤ Ab.{v})) (hT : T.Exact) [Epi T.g]
    (hML : (T.X₁ ⋙ forget Ab).IsMittagLeffler) (hK : (kernel T.f ⋙ forget Ab).IsMittagLeffler) :
    (T.map lim).Exact ∧ Epi (T.map lim).g := by
  let p := kernel.lift T.g T.f T.zero
  have : Epi p := hT.epi_kernelLift
  let e : kernel T.f ≅ kernel p :=
    (kernelIsoOfEq (kernel.lift_ι T.g T.f T.zero)).symm ≪≫ kernelCompMono p (kernel.ι T.g)
  have hU := Ab.shortExact_lim_of_isMittagLeffler _ (shortExact_kernel_ι p)
    (isMittagLeffler_of_epi e.hom hK)
  have : Epi (limMap p) := hU.epi_g
  have hV := Ab.shortExact_lim_of_isMittagLeffler _ (shortExact_kernel_ι T.g)
    (isMittagLeffler_of_epi p hML)
  refine ⟨?_, hV.epi_g⟩
  let φ : T.map lim ⟶ (ShortComplex.mk (kernel.ι T.g) T.g (kernel.condition T.g)).map lim :=
    { τ₁ := limMap p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := limit.hom_ext fun n => by simp [p, ← NatTrans.comp_app] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hV.exact

namespace InverseSystemCycles

variable {A B C : ℕᵒᵖ ⥤ Ab.{v}}
variable (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0)

/-- The map from the cycles of the limit short complex to the cycles at index `n`. -/
noncomputable def limitCyclesπ (n : ℕᵒᵖ) :
    (limitShortComplexOfInvSystem f g h).cycles ⟶ (cycles f g h).obj n :=
  ShortComplex.cyclesMap (limitShortComplexπ f g h n)

/-- `limitCyclesπ n` followed by the inclusion of the cycles is the limit projection. -/
lemma limitCyclesπ_inclusion_app (n : ℕᵒᵖ) :
    limitCyclesπ f g h n ≫ (inclusion f g h).app n =
      (limitShortComplexOfInvSystem f g h).iCycles ≫ limit.π B n :=
  ShortComplex.cyclesMap_i _

/-- The components of the comparison map, precomposed with the homology projection. -/
lemma limitShortComplex_homologyπ_comparisonHomologyLimit_π (n : ℕᵒᵖ) :
    (limitShortComplexOfInvSystem f g h).homologyπ ≫ comparisonHomologyLimit f g h ≫
      limit.π (homologyInvSystem f g h) n =
      limitCyclesπ f g h n ≫ (projection f g h).app n :=
  (congrArg ((limitShortComplexOfInvSystem f g h).homologyπ ≫ ·) (limit.lift_π _ n)).trans
    (ShortComplex.homologyπ_naturality _)

/-- The limit of the cycles is killed by the limit of `g`. -/
lemma limMap_inclusion_g :
    limMap (inclusion f g h) ≫ (limitShortComplexOfInvSystem f g h).g = 0 := by
  rw [limitShortComplexOfInvSystem_g, limMap_eq, limMap_eq, ← Functor.map_comp, inclusion_g,
    Functor.map_zero]

/-- The limit of the cycle inclusions is a kernel of the limit of `g`. -/
noncomputable def limitCyclesIsKernel :
    IsLimit (KernelFork.ofι (limMap (inclusion f g h)) (limMap_inclusion_g f g h)) :=
  isLimitForkMapOfIsLimit' lim _ (cyclesIsKernel f g h)

/-- The map induced by `limMap f` into the limit of the cycles is the limit of the boundary
maps. -/
lemma limitCyclesIsKernel_lift :
    (limitCyclesIsKernel f g h).lift
        (KernelFork.ofι _ (limitShortComplexOfInvSystem f g h).zero) =
      limMap (toCycles f g h) :=
  Fork.IsLimit.hom_ext (limitCyclesIsKernel f g h) (by
    rw [Fork.IsLimit.lift_ι]
    exact limit.hom_ext fun n => by simp [toCycles_app_inclusion_app])

/-- The limits of the cycles and homology towers form a left homology datum for the limit short
complex, provided the first term and the kernel of the boundary map are Mittag-Leffler. -/
@[implicit_reducible, simps K H i π]
noncomputable def limitLeftHomologyData (hA : (A ⋙ forget Ab).IsMittagLeffler)
    (hK : (kernel (toCycles f g h) ⋙ forget Ab).IsMittagLeffler) :
    (limitShortComplexOfInvSystem f g h).LeftHomologyData where
  K := limit (cycles f g h)
  H := limit (homologyInvSystem f g h)
  i := limMap (inclusion f g h)
  π := limMap (projection f g h)
  wi := limMap_inclusion_g f g h
  hi := limitCyclesIsKernel f g h
  wπ := by
    rw [limitCyclesIsKernel_lift, limMap_eq (toCycles f g h), limMap_eq (projection f g h),
      ← Functor.map_comp, toCycles_projection, Functor.map_zero]
  hπ :=
    have hT := limit_exact_of_isMittagLeffler (boundarySC f g h) (boundarySC_exact f g h) hA hK
    have := hT.2
    CokernelCofork.IsColimit.ofπ _ _
      (fun k hk => hT.1.desc k (by rwa [limitCyclesIsKernel_lift] at hk))
      (fun k hk => hT.1.g_desc k _)
      (fun k hk _ hl => (cancel_epi ((boundarySC f g h).map lim).g).1
        (hl.trans (hT.1.g_desc k _).symm))

/-- The cycles of the limit short complex map to the cycles at index `n` by the limit
projections. -/
lemma limitLeftHomologyData_cyclesIso_hom_π (hA : (A ⋙ forget Ab).IsMittagLeffler)
    (hK : (kernel (toCycles f g h) ⋙ forget Ab).IsMittagLeffler) (n : ℕᵒᵖ) :
    (limitLeftHomologyData f g h hA hK).cyclesIso.hom ≫ limit.π (cycles f g h) n =
      limitCyclesπ f g h n := by
  rw [← cancel_mono ((inclusion f g h).app n), Category.assoc, ← limMap_π, ← Category.assoc,
    ← limitLeftHomologyData_i f g h hA hK, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
    limitCyclesπ_inclusion_app]

/-- The homology isomorphism of `limitLeftHomologyData` is the comparison map. -/
lemma limitLeftHomologyData_homologyIso_hom (hA : (A ⋙ forget Ab).IsMittagLeffler)
    (hK : (kernel (toCycles f g h) ⋙ forget Ab).IsMittagLeffler) :
    (limitLeftHomologyData f g h hA hK).homologyIso.hom = comparisonHomologyLimit f g h := by
  apply (cancel_epi (limitShortComplexOfInvSystem f g h).homologyπ).1
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, Category.assoc, limitShortComplex_homologyπ_comparisonHomologyLimit_π,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    limitLeftHomologyData_π, limMap_π, ← Category.assoc,
    limitLeftHomologyData_cyclesIso_hom_π]

end InverseSystemCycles

/-- If the first term and the kernel of the boundary map of a complex of towers are
Mittag-Leffler, the comparison map is an isomorphism. -/
lemma comparisonHomologyLimit_isIso_of_isMittagLeffler {A B C : ℕᵒᵖ ⥤ Ab.{v}}
    (f : A ⟶ B) (g : B ⟶ C) (h : ∀ i, f.app i ≫ g.app i = 0)
    (hA : (A ⋙ forget Ab).IsMittagLeffler)
    (hK : (kernel (toCycles f g h) ⋙ forget Ab).IsMittagLeffler) :
    IsIso (comparisonHomologyLimit f g h) := by
  rw [← limitLeftHomologyData_homologyIso_hom f g h hA hK]
  infer_instance

/-- For a countable inverse system of 4-term complexes of abelian groups, if
`(A^{-2}_i)` and `(A^{-1}_i)` are Mittag-Leffler and
`(H^{-1}_i)` is essentially constant, then the comparison morphism from the
`0`-cohomology of the limit complex to the limit of the `0`-cohomologies is an
isomorphism. -/
@[stacks 070E, ega "0 13.2.3" "special case"]
theorem isIso_comparisonHomologyLimit_of_isMittagLeffler
    (A_neg2 A_neg1 A_0 A_1 : ℕᵒᵖ ⥤ Ab.{v})
    (d_neg2 : A_neg2 ⟶ A_neg1) (d_neg1 : A_neg1 ⟶ A_0) (d_0 : A_0 ⟶ A_1)
    (h_neg1 : ∀ i, d_neg2.app i ≫ d_neg1.app i = 0)
    (h_0 : ∀ i, d_neg1.app i ≫ d_0.app i = 0)
    (hML_neg2 : (A_neg2 ⋙ forget Ab).IsMittagLeffler)
    (hML_neg1 : (A_neg1 ⋙ forget Ab).IsMittagLeffler)
    (hEC : EssentiallyConstantPro.IsEssentiallyConstantPro
      (homologyInvSystem d_neg2 d_neg1 h_neg1)) :
    IsIso (comparisonHomologyLimit d_neg1 d_0 h_0) := by
  have hZ := cycles_isMittagLeffler d_neg2 d_neg1 h_neg1 hML_neg2 hEC
  exact comparisonHomologyLimit_isIso_of_isMittagLeffler d_neg1 d_0 h_0 hML_neg1
    (isMittagLeffler_of_epi ((cyclesIsoKernel d_neg2 d_neg1 h_neg1) ≪≫
      (kernelToCyclesIso d_neg1 d_0 h_0).symm).hom hZ)

end

section

/-!
## Stacks tag 0AAT

Mittag-Leffler over ordinals: if every term `K_β` of an inverse system of
cochain complexes of abelian groups indexed by an ordinal `α` is acyclic, and
the comparison maps `K^n_β → lim_{γ < β} K^n_γ` are surjective for every `β`
and `n`, then the limit complex `lim_{β < α} K_β` is acyclic.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

/-- The inclusion functor of the set of ordinals strictly less than `β` into
`α.ToType`. -/
@[implicit_reducible]
noncomputable def belowInclusion (α : Ordinal.{u}) (β : α.ToType) :
    {γ : α.ToType // γ < β} ⥤ α.ToType :=
  Monotone.functor (Subtype.mono_coe _)

/-- The `n`-th degree of an inverse system of cochain complexes, as an inverse
system of abelian groups. -/
@[implicit_reducible]
noncomputable def evalAtDegree (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    (α.ToType)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  K ⋙ HomologicalComplex.eval AddCommGrpCat _ n

/-- Restriction of the `n`-th degree inverse system to the subcategory of
ordinals strictly less than `β`. -/
@[implicit_reducible]
noncomputable def restrictBelow (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (β : α.ToType) (n : ℤ) :
    ({γ : α.ToType // γ < β})ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (belowInclusion α β).op ⋙ evalAtDegree α K n

@[simp]
lemma evalAt0AAT_map (α : Ordinal.{u}) (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (n : ℤ) {a b : (α.ToType)ᵒᵖ} (f : a ⟶ b) : (evalAtDegree α K n).map f = (K.map f).f n := rfl

namespace OrdinalInverseSystem

variable {J : Type u} [LinearOrder J]

/-- The inclusion functor of `{i // i < j}` into a linear order `J`. -/
@[implicit_reducible]
def lowerIncl (j : J) : {i : J // i < j} ⥤ J :=
  Monotone.functor (Subtype.mono_coe _)

section Cone

variable {C : Type w} [Category.{w'} C]

/-- Any two morphisms between the same objects of the opposite of a linear order
have the same image under a functor. -/
lemma map_op_eq (F : Jᵒᵖ ⥤ C) {a b : Jᵒᵖ} (f g : a ⟶ b) : F.map f = F.map g :=
  congrArg F.map (Quiver.Hom.unop_inj.eq_iff.mp (Subsingleton.elim _ _))

/-- The cone with apex `F(j)` over the restriction of `F : Jᵒᵖ ⥤ C` to the
elements strictly below `j`. -/
@[implicit_reducible]
def coneBelow (F : Jᵒᵖ ⥤ C) (j : J) : Cone ((lowerIncl j).op ⋙ F) where
  pt := F.obj (op j)
  π :=
    { app := fun i => F.map (homOfLE i.unop.2.le).op
      naturality := fun _ _ f => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.comp_map, ← F.map_comp]
        exact map_op_eq F _ _ }

@[simp]
lemma coneBelow_pt (F : Jᵒᵖ ⥤ C) (j : J) : (coneBelow F j).pt = F.obj (op j) := rfl

@[simp]
lemma coneBelow_π_app (F : Jᵒᵖ ⥤ C) (j : J) (i : {i : J // i < j}ᵒᵖ) :
    (coneBelow F j).π.app i = F.map (homOfLE i.unop.2.le).op := rfl

end Cone

end OrdinalInverseSystem

/-- The cone with apex `K^n_β` over the restriction to ordinals less than `β`. -/
@[implicit_reducible]
noncomputable def coneAtBeta (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (β : α.ToType) (n : ℤ) :
    Cone (restrictBelow α K β n) :=
  OrdinalInverseSystem.coneBelow (evalAtDegree α K n) β

/-- The canonical comparison map `K^n_β ⟶ lim_{γ < β} K^n_γ`. -/
noncomputable def comparisonMap (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (β : α.ToType) (n : ℤ) :
    (evalAtDegree α K n).obj (op β) ⟶ limit (restrictBelow α K β n) :=
  limit.lift _ (coneAtBeta α K β n)

@[simp]
lemma coneAtBeta_π_app (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (β : α.ToType) (n : ℤ)
    (γ : {γ : α.ToType // γ < β}ᵒᵖ) :
    (coneAtBeta α K β n).π.app γ = (evalAtDegree α K n).map (homOfLE γ.unop.2.le).op := rfl

@[reassoc (attr := simp)]
lemma comparisonMap_π (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (β : α.ToType) (n : ℤ)
    (γ : {γ : α.ToType // γ < β}ᵒᵖ) :
    comparisonMap α K β n ≫ limit.π _ γ = (evalAtDegree α K n).map (homOfLE γ.unop.2.le).op := by
  rw [comparisonMap, limit.lift_π, coneAtBeta_π_app]

namespace OrdinalInverseSystem

variable {J : Type u} [LinearOrder J]

/-- Assemble compatible choices by well-founded recursion. -/
lemma compatibleChoice [WellFoundedLT J]
    (E : J → Type v) (r : ∀ {a b : J}, a ≤ b → E b → E a)
    (hne : ∀ j, Nonempty (E j))
    (hext : ∀ j (s : ∀ i, i < j → E i),
      (∀ a b (hab : a ≤ b) (hb : b < j), r hab (s b hb) = s a (lt_of_le_of_lt hab hb)) →
      ∃ x : E j, ∀ i (hi : i < j), r (le_of_lt hi) x = s i hi)
    (rid : ∀ j (x : E j), r (le_refl j) x = x) :
    ∃ s : ∀ j, E j, ∀ a b (h : a ≤ b), r h (s b) = s a := by
  classical
  let step (j : J) (s : ∀ i, i < j → E i) : E j :=
    if h : ∀ a b (hab : a ≤ b) (hb : b < j),
        r hab (s b hb) = s a (lt_of_le_of_lt hab hb) then
      (hext j s h).choose
    else (hne j).some
  obtain ⟨s, hfix⟩ : ∃ s : ∀ j, E j, ∀ j, s j = step j (fun i _ => s i) :=
    ⟨_, wellFounded_lt.fix_eq step⟩
  have hs (j : J) : ∀ i (hi : i < j), r (le_of_lt hi) (s j) = s i := by
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      have hc : ∀ a b (hab : a ≤ b) (hb : b < j), r hab (s b) = s a := by
        intro a b hab hb
        rcases hab.eq_or_lt with h | h
        · subst a; exact rid b (s b)
        · exact ih b hb a h
      rw [hfix j]
      dsimp only [step]
      rw [dite_eq_left hc]
      exact (hext j _ hc).choose_spec
  refine ⟨s, fun a b h => ?_⟩
  rcases h.eq_or_lt with h | h
  · subst a; exact rid b (s b)
  · exact hs b a h

lemma exact_elements (X : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    X.ExactAt n ↔ ∀ x : X.X n, X.d n (n + 1) x = 0 →
      ∃ y : X.X (n - 1), X.d (n - 1) n y = x := by
  rw [X.exactAt_iff' (i := n - 1) (j := n) (k := n + 1) (by simp) (by simp)]
  exact ShortComplex.ab_exact_iff _

/-- An element of the `n`-th degree of a limit of cochain complexes, given by a
compatible family of elements of the `n`-th degrees. -/
noncomputable def degreeElement {I : Type u} [Category.{u} I]
    (K : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)
    (x : ∀ j, (K.obj j).X n)
    (hx : ∀ i j (f : i ⟶ j), (K.map f).f n (x i) = x j) : (limit K).X n :=
  (Types.isLimitEquivSections (isLimitOfPreserves (forget AddCommGrpCat)
    (isLimitOfPreserves (HomologicalComplex.eval _ _ n) (limit.isLimit K)))).symm
      ⟨x, fun {_ _} f => hx _ _ f⟩

lemma degreeElement_π {I : Type u} [Category.{u} I]
    (K : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)
    (x : ∀ j, (K.obj j).X n)
    (hx : ∀ i j (f : i ⟶ j), (K.map f).f n (x i) = x j) (j : I) :
    (limit.π K j).f n (degreeElement K n x hx) = x j :=
  Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (forget AddCommGrpCat)
      (isLimitOfPreserves (HomologicalComplex.eval _ _ n) (limit.isLimit K)))
    ⟨x, fun {_ _} f => hx _ _ f⟩ j

lemma degree_ext {I : Type u} [Category.{u} I]
    (K : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)
    (x y : (limit K).X n)
    (h : ∀ j, (limit.π K j).f n x = (limit.π K j).f n y) : x = y :=
  Concrete.isLimit_ext (K ⋙ HomologicalComplex.eval _ _ n)
    (isLimitOfPreserves (HomologicalComplex.eval _ _ n) (limit.isLimit K)) x y h

lemma degree_w {I : Type u} [Category.{u} I]
    (K : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)
    {a b : I} (f : a ⟶ b) (x : (limit K).X n) :
    (K.map f).f n ((limit.π K a).f n x) = (limit.π K b).f n x := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, limit.w]

lemma comm_apply {X Y : CochainComplex AddCommGrpCat.{u} ℤ}
    (f : X ⟶ Y) (n m : ℤ) (x : X.X n) :
    f.f m (X.d n m x) = Y.d n m (f.f n x) :=
  (ConcreteCategory.congr_hom (f.comm n m) x).symm

/-- Correct an arbitrary primitive by a lifted boundary to give a prescribed image. -/
lemma liftPrimitive {X Y : CochainComplex AddCommGrpCat.{u} ℤ}
    (f : X ⟶ Y) (hX : X.Acyclic) (hY : Y.Acyclic)
    (hs : ∀ n, Function.Surjective (ConcreteCategory.hom (f.f n)))
    (n : ℤ) (x : X.X n) (hx : X.d n (n + 1) x = 0)
    (y : Y.X (n - 1)) (hy : Y.d (n - 1) n y = f.f n x) :
    ∃ z : X.X (n - 1), X.d (n - 1) n z = x ∧ f.f (n - 1) z = y := by
  obtain ⟨z, hz⟩ := (exact_elements X n).mp (hX n) x hx
  have hyz : Y.d (n - 1) (n - 1 + 1) (y - f.f (n - 1) z) = 0 := by
    rw [sub_add_cancel, map_sub, ← comm_apply, hz, hy, sub_self]
  obtain ⟨w, hw⟩ := (exact_elements Y (n - 1)).mp (hY (n - 1)) _ hyz
  obtain ⟨v, hv⟩ := hs (n - 1 - 1) w
  refine ⟨z + X.d (n - 1 - 1) (n - 1) v, ?_, ?_⟩
  · rw [map_add, hz]
    have hd := ConcreteCategory.congr_hom (X.d_comp_d (n - 1 - 1) (n - 1) n) v
    rw [ConcreteCategory.comp_apply] at hd
    rw [hd, AddCommGrpCat.zero_apply, add_zero]
  · rw [map_add, comm_apply, hv, hw]
    abel

/-- The comparison map `K_j ⟶ lim_{i < j} K_i` of an inverse system of cochain
complexes. -/
noncomputable def complexComparison (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (j : J) :
    K.obj (op j) ⟶ limit ((lowerIncl j).op ⋙ K) :=
  limit.lift _ (coneBelow K j)

@[reassoc (attr := simp)]
lemma complexComparison_π (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (j : J)
    (i : {i : J // i < j}ᵒᵖ) :
    complexComparison K j ≫ limit.π _ i = K.map (homOfLE i.unop.2.le).op := by
  simp [complexComparison]

lemma complexComparison_π_apply (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (j : J)
    (i : {i : J // i < j}ᵒᵖ) (n : ℤ) (x : (K.obj (op j)).X n) :
    (limit.π ((lowerIncl j).op ⋙ K) i).f n ((complexComparison K j).f n x) =
      (K.map (homOfLE i.unop.2.le).op).f n x := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, complexComparison_π]

/-- Extend a compatible family of primitives below `b` to a primitive at `b`. -/
lemma exists_primitive_extension (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (b : J) (hK : (K.obj (op b)).Acyclic)
    (hs : ∀ n, Function.Surjective (ConcreteCategory.hom ((complexComparison K b).f n)))
    (hP : (limit ((lowerIncl b).op ⋙ K)).Acyclic)
    (n : ℤ) (x : (limit K).X n) (hx : (limit K).d n (n + 1) x = 0)
    (s : ∀ a, a < b → (K.obj (op a)).X (n - 1))
    (hsd : ∀ a (ha : a < b), (K.obj (op a)).d (n - 1) n (s a ha) = (limit.π K (op a)).f n x)
    (hsc : ∀ a c (hac : a ≤ c) (hc : c < b),
      (K.map (homOfLE hac).op).f (n - 1) (s c hc) = s a (lt_of_le_of_lt hac hc)) :
    ∃ z : (K.obj (op b)).X (n - 1), (K.obj (op b)).d (n - 1) n z = (limit.π K (op b)).f n x ∧
      ∀ a (ha : a < b), (K.map (homOfLE ha.le).op).f (n - 1) z = s a ha := by
  let y := degreeElement ((lowerIncl b).op ⋙ K) (n - 1) (fun a => s a.unop.val a.unop.property)
    (fun a c f => by
      rw [Functor.comp_map,
        map_op_eq K _ (homOfLE (Subtype.coe_le_coe.mpr (leOfHom f.unop))).op]
      exact hsc c.unop.val a.unop.val _ a.unop.property)
  have hxb : (K.obj (op b)).d n (n + 1) ((limit.π K (op b)).f n x) = 0 := by
    rw [← comm_apply, hx, map_zero]
  have hy : (limit ((lowerIncl b).op ⋙ K)).d (n - 1) n y =
      (complexComparison K b).f n ((limit.π K (op b)).f n x) := by
    refine degree_ext ((lowerIncl b).op ⋙ K) n _ _ fun a => ?_
    rw [comm_apply, degreeElement_π, complexComparison_π_apply, degree_w]
    exact hsd a.unop.val a.unop.property
  obtain ⟨z, hz, hzy⟩ := liftPrimitive (complexComparison K b) hK hP hs n _ hxb y hy
  refine ⟨z, hz, fun a ha => ?_⟩
  have h := congrArg (fun w => (limit.π ((lowerIncl b).op ⋙ K) (op ⟨a, ha⟩)).f (n - 1) w) hzy
  rw [complexComparison_π_apply, degreeElement_π] at h
  exact h

/-- If every term of an inverse system of cochain complexes over a well-ordered
set is acyclic, the comparison maps to the partial limits are degreewise
surjective, and all partial limits are acyclic, then the limit is acyclic. -/
theorem acyclic_limit_of_acyclic_below [WellFoundedLT J]
    (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : ∀ j, (K.obj (op j)).Acyclic)
    (hs : ∀ j n, Function.Surjective (ConcreteCategory.hom ((complexComparison K j).f n)))
    (hP : ∀ j, (limit ((lowerIncl j).op ⋙ K)).Acyclic) :
    (limit K).Acyclic := by
  intro n
  refine (exact_elements _ n).mpr fun x hx => ?_
  let E (b : J) := {y : (K.obj (op b)).X (n - 1) //
    (K.obj (op b)).d (n - 1) n y = (limit.π K (op b)).f n x}
  let r {a b : J} (h : a ≤ b) (y : E b) : E a :=
    ⟨(K.map (homOfLE h).op).f (n - 1) y.val, by
      rw [← comm_apply, y.property, degree_w]⟩
  have hne (b : J) : Nonempty (E b) := by
    have hxb : (K.obj (op b)).d n (n + 1) ((limit.π K (op b)).f n x) = 0 := by
      rw [← comm_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := (exact_elements _ n).mp (hK b n) _ hxb
    exact ⟨⟨y, hy⟩⟩
  obtain ⟨s, hs'⟩ := compatibleChoice E r hne
    (fun b s hsc => by
      obtain ⟨z, hz, hzs⟩ := exists_primitive_extension K b (hK b) (hs b) (hP b) n x hx
        (fun a ha => (s a ha).val) (fun a ha => (s a ha).property)
        (fun a c hac hc => congrArg Subtype.val (hsc a c hac hc))
      exact ⟨⟨z, hz⟩, fun a ha => Subtype.ext (hzs a ha)⟩)
    (fun b y => Subtype.ext (by simp [r]))
  refine ⟨degreeElement K (n - 1) (fun a => (s a.unop).val)
    (fun a b f => by
      rw [map_op_eq K f (homOfLE (leOfHom f.unop)).op]
      exact congrArg Subtype.val (hs' b.unop a.unop (leOfHom f.unop))),
    degree_ext K n _ _ fun b => ?_⟩
  rw [comm_apply, degreeElement_π]
  exact (s b.unop).property

/-- The identification of the elements below `i` in `{x // x < j}` with the
elements below `i` in `J`. -/
@[implicit_reducible]
def lowerLower {j : J} (i : {x : J // x < j}) :
    {y : {x : J // x < j} // y < i} ⥤ {x : J // x < i.val} :=
  Monotone.functor (f := fun y => ⟨y.val.val, Subtype.coe_lt_coe.mpr y.property⟩)
    (fun _ _ h => Subtype.mk_le_mk.mpr (Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mpr h)))

instance {j : J} (i : {x : J // x < j}) : (lowerLower i).IsEquivalence where
  faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  full := ⟨fun f => ⟨homOfLE (Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mp
    (Subtype.coe_le_coe.mpr (leOfHom f)))), Subsingleton.elim _ _⟩⟩
  essSurj := ⟨fun x => ⟨⟨⟨x.val, x.property.trans i.property⟩, x.property⟩, ⟨Iso.refl _⟩⟩⟩

lemma complexComparison_restrict (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) {j : J}
    (i : {x : J // x < j}) :
    complexComparison ((lowerIncl j).op ⋙ K) i =
      complexComparison K i.val ≫ limit.pre ((lowerIncl i.val).op ⋙ K) (lowerLower i).op := by
  refine limit.hom_ext fun a => ?_
  rw [complexComparison_π, Category.assoc]
  refine Eq.trans ?_
    (congrArg (complexComparison K i.val ≫ ·) (limit.pre_π _ (lowerLower i).op a)).symm
  rw [complexComparison_π, Functor.comp_map]
  exact map_op_eq K _ _

/-- If every term of an inverse system of cochain complexes over a well-ordered
set is acyclic and the comparison maps to the partial limits are degreewise
surjective, then every partial limit is acyclic. -/
theorem acyclic_limit_below [WellFoundedLT J]
    (K : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : ∀ j, (K.obj (op j)).Acyclic)
    (hs : ∀ j n, Function.Surjective (ConcreteCategory.hom ((complexComparison K j).f n)))
    (j : J) : (limit ((lowerIncl j).op ⋙ K)).Acyclic := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    refine acyclic_limit_of_acyclic_below ((lowerIncl j).op ⋙ K) (fun i => hK i.val)
      (fun i n y => ?_) (fun i n => ?_)
    · let p := limit.pre ((lowerIncl i.val).op ⋙ K) (lowerLower i).op
      obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.f n)).2 y
      obtain ⟨w, rfl⟩ := hs i.val n z
      exact ⟨w, by rw [complexComparison_restrict, HomologicalComplex.comp_f,
        ConcreteCategory.comp_apply]⟩
    · let p := limit.pre ((lowerIncl i.val).op ⋙ K) (lowerLower i).op
      exact ((HomologicalComplex.acyclic_iff _).1 (ih i.val i.property) n).of_iso (asIso p)

end OrdinalInverseSystem

/-- The complex-level comparison map is degreewise surjective when the
comparison maps of the degrees are. -/
lemma complexComparison_f_surjective (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ) (β : α.ToType) (n : ℤ)
    (h : Function.Surjective (ConcreteCategory.hom (comparisonMap α K β n))) :
    Function.Surjective
      (ConcreteCategory.hom ((OrdinalInverseSystem.complexComparison K β).f n)) := by
  let e := preservesLimitIso (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) n)
    ((OrdinalInverseSystem.lowerIncl β).op ⋙ K)
  have he : comparisonMap α K β n = (OrdinalInverseSystem.complexComparison K β).f n ≫ e.hom := by
    refine limit.hom_ext fun γ => ?_
    rw [comparisonMap_π, Category.assoc]
    refine Eq.trans ?_ (congrArg ((OrdinalInverseSystem.complexComparison K β).f n ≫ ·)
      (preservesLimitIso_hom_π _ ((OrdinalInverseSystem.lowerIncl β).op ⋙ K) γ)).symm
    rw [HomologicalComplex.eval_map, ← HomologicalComplex.comp_f,
      OrdinalInverseSystem.complexComparison_π, evalAt0AAT_map]
  intro y
  obtain ⟨x, hx⟩ := h (e.hom y)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso e.hom).1 ?_⟩
  rw [← hx, he, ConcreteCategory.comp_apply]

/-- Let `α` be an ordinal and `K` an inverse system of cochain complexes of
abelian groups over `α`. If every `K_β` is acyclic and the comparison map
`K^n_β → lim_{γ < β} K^n_γ` is surjective for every `β` and `n`, then the
limit complex `lim_{β < α} K_β` is acyclic. -/
@[stacks 0AAT]
theorem acyclic_limit_of_acyclic_of_surjective (α : Ordinal.{u})
    (K : (α.ToType)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    (hAcyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hSurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective
        (ConcreteCategory.hom (comparisonMap α K β n))) :
    (limit K).Acyclic :=
  have hs β n := complexComparison_f_surjective α K β n (hSurj β n)
  OrdinalInverseSystem.acyclic_limit_of_acyclic_below K hAcyclic hs
    (OrdinalInverseSystem.acyclic_limit_below K hAcyclic hs)

end
