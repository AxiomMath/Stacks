module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt

/-!
# Čech cohomology along a cofiltered limit of families

Let `𝒰 = {U_i → U}_{i ∈ I}` be a finite family of morphisms with fixed target in a category `C`,
and suppose it is the limit of a cofiltered system of families `𝒰_λ = {U_{i,λ} → U_λ}`
with the same index set: the targets `U_λ` and each of the members `U_{i,λ}` form cofiltered
systems with compatible cones to `U` and `U_i`.  Let `F` be an abelian presheaf on `C` such that
for every tuple `(i_0, …, i_p)` the sections of `F` over the iterated fibre product
`U_{i_0} ×_U ⋯ ×_U U_{i_p}` are the filtered colimit of its sections over
`U_{i_0,λ} ×_{U_λ} ⋯ ×_{U_λ} U_{i_p,λ}`.  Then

  `Ȟ^p(𝒰, F) = colim_λ Ȟ^p(𝒰_λ, F)`,

and in particular the Čech cohomology of `𝒰` vanishes in every degree in which that of all the
`𝒰_λ` does.  This is the step "by exactness of filtered colimits" in the proof of Stacks 099U.

## Main definitions

* `Stacks.CechSite.stageFamily`: the family `𝒰_λ` at a stage of a cofiltered system of families.
* `Stacks.CechSite.stageFibreProduct`: the system `λ ↦ U_{i_0,λ} ×_{U_λ} ⋯ ×_{U_λ} U_{i_p,λ}`
  of iterated fibre products of a tuple, and `Stacks.CechSite.stageFibreProductCone` its cone
  with vertex `U_{i_0} ×_U ⋯ ×_U U_{i_p}`.

## Main results

* `HomologicalComplex.exactAt_of_forall_exists`: a complex of abelian groups which is
  approximated by exact complexes — every element in one degree comes from one of them, and
  every element in the next degree which dies comes from one where it already dies after a
  transition — is exact in that degree.
* `Stacks.CechSite.isZero_cechCohomology_of_isColimit`: the vanishing of the Čech cohomology of a
  cofiltered limit of families.
* `Stacks.CechSite.isPullback_map_cechProductMap`: iterated fibre products of a cartesian
  morphism of families are cartesian.

## Implementation notes

Only the elementwise content of "filtered colimits are exact" is used, so no functoriality of
the Čech complex in the system is needed beyond the maps of Stacks 03F4 between the families,
`Stacks.CechSite.cechComplexMap`.  The colimit hypothesis is stated on underlying sets, which is
the form in which Stacks 099S provides it.

## References

* [Stacks Project, Tag 099U](https://stacks.math.columbia.edu/tag/099U)
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w t t' v u

namespace HomologicalComplex

/-- A complex of abelian groups is exact in degree `i` as soon as it is approximated there by
exact complexes `K'_λ`: every element of `K^i` is the image of an element of some `K'_λ^i`, and
every element of `K'_λ^{i+1}` mapping to zero already maps to zero along a transition
`K'_λ ⟶ K'_μ` compatible with the maps to `K`.  This is the elementwise content of the
exactness of filtered colimits of abelian groups. -/
theorem exactAt_of_forall_exists {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex AddCommGrpCat.{a} c) (i : ι) {Λ : Type*}
    (K' : Λ → HomologicalComplex AddCommGrpCat.{a} c) (φ : ∀ j, K' j ⟶ K)
    (hK' : ∀ j, (K' j).ExactAt i) (hsurj : ∀ x : K.X i, ∃ j x', (φ j).f i x' = x)
    (hinj : ∀ j (y : (K' j).X (c.next i)), (φ j).f (c.next i) y = 0 →
      ∃ k, ∃ ψ : K' j ⟶ K' k, ψ ≫ φ k = φ j ∧ ψ.f (c.next i) y = 0) :
    K.ExactAt i := by
  rw [exactAt_iff, ShortComplex.ab_exact_iff]
  intro x hx
  obtain ⟨j, x', rfl⟩ := hsurj x
  have hy : (φ j).f (c.next i) ((K' j).d i (c.next i) x') = 0 := by
    rw [← ConcreteCategory.comp_apply, ← (φ j).comm, ConcreteCategory.comp_apply]
    exact hx
  obtain ⟨k, ψ, hψ, hψy⟩ := hinj j _ hy
  have hz : (K' k).d i (c.next i) (ψ.f i x') = 0 := by
    rw [← ConcreteCategory.comp_apply, ψ.comm, ConcreteCategory.comp_apply, hψy]
  obtain ⟨z, hz'⟩ := (ShortComplex.ab_exact_iff _).mp (((K' k).exactAt_iff i).mp (hK' k)) _ hz
  refine ⟨(φ k).f (c.prev i) z, ?_⟩
  change K.d (c.prev i) i ((φ k).f (c.prev i) z) = (φ j).f i x'
  change (K' k).d (c.prev i) i z = ψ.f i x' at hz'
  have h₁ := ConcreteCategory.congr_hom ((φ k).comm (c.prev i) i) z
  have h₂ := ConcreteCategory.congr_hom
    (congrArg (fun g : K' j ⟶ K ↦ g.f i) hψ) x'
  exact h₁.trans ((congrArg (ConcreteCategory.hom ((φ k).f i)) hz').trans h₂)

end HomologicalComplex

namespace Stacks.CechSite

/-- The components of the map of Čech complexes induced by a morphism of families, on
elements. -/
theorem cechComplexMap_f_apply_π {C : Type u} [Category.{v} C] {U V : C}
    (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w} V) {f : U ⟶ V}
    (φ : E.HomOver G f) [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    (x : (cechComplex G F).X n) :
    Pi.π (cochainFactor E F n) i ((cechComplexMap E G φ F).f n x) =
      F.map (cechProductMap E G φ n i).op (Pi.π (cochainFactor G F n) (φ.s₀ ∘ i) x) :=
  ConcreteCategory.congr_hom (cechComplexMap_f_Pi_π E G φ F n i) x

/-- Two Čech cochains are equal as soon as all their components are. -/
private theorem cechComplex_X_ext {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (n : ℕ) {x y : (cechComplex E F).X n}
    (h : ∀ t, Pi.π (cochainFactor E F n) t x = Pi.π (cochainFactor E F n) t y) : x = y :=
  (productAddEquiv (cochainFactor E F n)).injective (funext h)

/-- **Iterated fibre products of a cartesian morphism of families are cartesian.** Let
`φ : E ⟶ G` be a morphism of families over `f : U ⟶ V` and let `q : C ⥤ D` be a functor
preserving the iterated fibre products of a tuple `i`. If `q` carries each square
`E_{i a} ⟶ G_{φ (i a)}` over `f` to a pullback square, it carries the square of iterated fibre
products `E_{i 0} ×_U ⋯ ×_U E_{i n} ⟶ G_{φ (i 0)} ×_V ⋯ ×_V G_{φ (i n)}` over `f` to a pullback
square: the fibre products of base changes are the base change of the fibre product. -/
theorem isPullback_map_cechProductMap {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
    (q : C ⥤ D) {U V : C} (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{t} V)
    {f : U ⟶ V} (φ : E.HomOver G f) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    [PreservesLimit (Discrete.functor fun a ↦ Over.mk (E.f (i a))) (Over.post q)]
    [PreservesLimit (Discrete.functor fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) (Over.post q)]
    (hφ : ∀ a, IsPullback (q.map (φ.h₀ (i a))) (q.map (E.f (i a))) (q.map (G.f (φ.s₀ (i a))))
      (q.map f)) :
    IsPullback (q.map (cechProductMap E G φ n i))
      (q.map (∏ᶜ fun a ↦ Over.mk (E.f (i a))).hom)
      (q.map (∏ᶜ fun a ↦ Over.mk (G.f (φ.s₀ (i a)))).hom) (q.map f) := by
  have hE := isLimitFanMkObjOfIsLimit (Over.post q) _ _
    (productIsProduct fun a ↦ Over.mk (E.f (i a)))
  have hG := isLimitFanMkObjOfIsLimit (Over.post q) _ _
    (productIsProduct fun a ↦ Over.mk (G.f (φ.s₀ (i a))))
  have hw (a : Fin (n + 1)) := Over.w (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) a)
  have hwE (a : Fin (n + 1)) := Over.w (Pi.π (fun a ↦ Over.mk (E.f (i a))) a)
  refine IsPullback.of_isLimit' ⟨by rw [← q.map_comp, ← q.map_comp, cechProductMap_comp_hom]⟩ ?_
  let ℓ (s : PullbackCone (q.map (∏ᶜ fun a ↦ Over.mk (G.f (φ.s₀ (i a)))).hom) (q.map f))
      (a : Fin (n + 1)) : s.pt ⟶ q.obj (E.X (i a)) :=
    (hφ a).lift (s.fst ≫ q.map (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) a).left) s.snd (by
      rw [Category.assoc, ← q.map_comp]
      exact (congrArg (fun g ↦ s.fst ≫ q.map g) (hw a)).trans s.condition)
  let lift (s : PullbackCone (q.map (∏ᶜ fun a ↦ Over.mk (G.f (φ.s₀ (i a)))).hom) (q.map f)) :
      s.pt ⟶ q.obj (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left :=
    (hE.lift (Fan.mk (Over.mk s.snd) fun a ↦
      (Over.homMk (ℓ s a) ((hφ a).lift_snd _ _ _) :
        Over.mk s.snd ⟶ (Over.post q).obj (Over.mk (E.f (i a)))))).left
  have hlift (s : PullbackCone (q.map (∏ᶜ fun a ↦ Over.mk (G.f (φ.s₀ (i a)))).hom) (q.map f))
      (a : Fin (n + 1)) :
      lift s ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (i a))) a).left = ℓ s a :=
    (congrArg CommaMorphism.left (hE.fac _ ⟨a⟩)).trans rfl
  refine PullbackCone.IsLimit.mk _ lift (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · refine Over.left_hom_ext_of_isLimit hG fun b ↦ ?_
    change (lift s ≫ q.map (cechProductMap E G φ n i)) ≫
        q.map (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      s.fst ≫ q.map (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left
    rw [Category.assoc, ← q.map_comp, cechProductMap_comp_π_left_anyUniverses, q.map_comp,
      reassoc_of% (hlift s b)]
    exact (hφ b).lift_fst _ _ _
  · exact Over.w (hE.lift (Fan.mk (Over.mk s.snd) fun a ↦
      (Over.homMk (ℓ s a) ((hφ a).lift_snd _ _ _) :
        Over.mk s.snd ⟶ (Over.post q).obj (Over.mk (E.f (i a))))))
  · refine Over.left_hom_ext_of_isLimit hE fun b ↦ ?_
    change m ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left =
      lift s ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left
    rw [hlift s b]
    refine (hφ b).hom_ext ?_ ?_
    · rw [Category.assoc, ← q.map_comp, ← cechProductMap_comp_π_left_anyUniverses, q.map_comp,
        reassoc_of% h₁]
      exact ((hφ b).lift_fst _ _ _).symm
    · rw [Category.assoc, ← q.map_comp, show (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫
          E.f (i b) = _ from hwE b, h₂]
      exact ((hφ b).lift_snd _ _ _).symm

section System

variable {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{w} U)
  {Λ : Type t} [Category.{t'} Λ] (B : Λ ⥤ C) (M : E.I₀ → Λ ⥤ C) (m : ∀ i, M i ⟶ B)

/-- The family `{U_{i,λ} → U_λ}` at a stage `λ` of a cofiltered system of families indexed like
`E`. -/
abbrev stageFamily (j : Λ) : PreZeroHypercover.{w} (B.obj j) where
  I₀ := E.I₀
  X i := (M i).obj j
  f i := (m i).app j

/-- The transition morphism of families between two stages. -/
abbrev stageFamilyHomOver {j k : Λ} (g : j ⟶ k) :
    (stageFamily E B M m j).HomOver (stageFamily E B M m k) (B.map g) where
  s₀ i := i
  h₀ i := (M i).map g
  w₀ i := (m i).naturality g

/-- The components of the transition maps between iterated fibre products at two stages. -/
@[reassoc]
lemma cechProductMap_stageFamilyHomOver_comp_π_left {j k : Λ} (g : j ⟶ k) (n : ℕ)
    (t : Fin (n + 1) → E.I₀)
    [∀ t : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))]
    [∀ t : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk ((stageFamily E B M m k).f (t a)))]
    (b : Fin (n + 1)) :
    cechProductMap (stageFamily E B M m j) (stageFamily E B M m k)
        (stageFamilyHomOver E B M m g) n t ≫
        (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m k).f (t a))) b).left =
      (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b).left ≫ (M (t b)).map g :=
  cechProductMap_comp_π_left_anyUniverses (stageFamily E B M m j) (stageFamily E B M m k) _ n t b

variable (πB : (Functor.const Λ).obj U ⟶ B) (π : ∀ i, (Functor.const Λ).obj (E.X i) ⟶ M i)
  (hπ : ∀ i j, (π i).app j ≫ (m i).app j = E.f i ≫ πB.app j)

/-- The morphism of families from `E` to the family at a stage, given by the cones. -/
abbrev toStageFamily (j : Λ) : E.HomOver (stageFamily E B M m j) (πB.app j) where
  s₀ i := i
  h₀ i := (π i).app j
  w₀ i := hπ i j

/-- The components of the maps from the iterated fibre products of `E` to those at a stage. -/
@[reassoc]
lemma cechProductMap_toStageFamily_comp_π_left (j : Λ) (n : ℕ) (t : Fin (n + 1) → E.I₀)
    [∀ t : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (t a)))]
    [∀ t : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))]
    (b : Fin (n + 1)) :
    cechProductMap E (stageFamily E B M m j) (toStageFamily E B M m πB π hπ j) n t ≫
        (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (t a))) b).left ≫ (π (t b)).app j :=
  cechProductMap_comp_π_left_anyUniverses E (stageFamily E B M m j) _ n t b

variable [∀ (j : Λ) (n : ℕ) (t : Fin (n + 1) → (stageFamily E B M m j).I₀),
    HasProduct (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))]

/-- The system of iterated fibre products `λ ↦ U_{i_0,λ} ×_{U_λ} ⋯ ×_{U_λ} U_{i_n,λ}` of a
tuple of indices. -/
noncomputable abbrev stageFibreProduct (n : ℕ) (t : Fin (n + 1) → E.I₀) : Λ ⥤ C where
  obj j := (∏ᶜ (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))).left
  map {j k} g := cechProductMap (stageFamily E B M m j) (stageFamily E B M m k)
    (stageFamilyHomOver E B M m g) n t
  map_id j := cechProduct_left_hom_ext (stageFamily E B M m j) n t fun b ↦ by
    simp [cechProductMap_stageFamilyHomOver_comp_π_left]
  map_comp {j k l} f g := cechProduct_left_hom_ext (stageFamily E B M m l) n t fun b ↦ by
    simp [cechProductMap_stageFamilyHomOver_comp_π_left,
      cechProductMap_stageFamilyHomOver_comp_π_left_assoc]

/-- The transition maps of `stageFibreProduct` are the maps `cechProductMap` induced by the
transition morphisms of the stage families. -/
lemma stageFibreProduct_map (n : ℕ) (t : Fin (n + 1) → E.I₀) {j k : Λ} (g : j ⟶ k) :
    (stageFibreProduct E B M m n t).map g =
      cechProductMap (stageFamily E B M m j) (stageFamily E B M m k)
        (stageFamilyHomOver E B M m g) n t := rfl

variable [∀ (n : ℕ) (t : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (t a)))]

/-- The maps from the iterated fibre products of `E` to those at the stages are compatible with
the transitions. -/
lemma cechProductMap_toStageFamily_comp_stageFibreProduct_map (n : ℕ) (t : Fin (n + 1) → E.I₀)
    {j k : Λ} (g : j ⟶ k) :
    cechProductMap E (stageFamily E B M m j) (toStageFamily E B M m πB π hπ j) n t ≫
        cechProductMap (stageFamily E B M m j) (stageFamily E B M m k)
          (stageFamilyHomOver E B M m g) n t =
      cechProductMap E (stageFamily E B M m k) (toStageFamily E B M m πB π hπ k) n t := by
  refine cechProduct_left_hom_ext (stageFamily E B M m k) n t fun b ↦ ?_
  have h : (π (t b)).app j ≫ (M (t b)).map g = (π (t b)).app k := by
    simpa using ((π (t b)).naturality g).symm
  rw [Category.assoc, cechProductMap_stageFamilyHomOver_comp_π_left,
    cechProductMap_toStageFamily_comp_π_left_assoc, h,
    cechProductMap_toStageFamily_comp_π_left]

/-- The iterated fibre product `U_{i_0} ×_U ⋯ ×_U U_{i_n}` of a tuple, as a cone over the
system of iterated fibre products at the stages. -/
noncomputable abbrev stageFibreProductCone (n : ℕ) (t : Fin (n + 1) → E.I₀) :
    Cone (stageFibreProduct E B M m n t) :=
  Cone.mk (∏ᶜ (fun a ↦ Over.mk (E.f (t a)))).left
    { app := fun j ↦ cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t
      naturality := fun _ _ g ↦ (Category.id_comp _).trans
        (cechProductMap_toStageFamily_comp_stageFibreProduct_map E B M m πB π hπ n t g).symm }

/-- The projections of `stageFibreProductCone` are the maps `cechProductMap` induced by
`toStageFamily`. -/
lemma stageFibreProductCone_π_app (n : ℕ) (t : Fin (n + 1) → E.I₀) (j : Λ) :
    (stageFibreProductCone E B M m πB π hπ n t).π.app j =
      cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t := rfl

/-- Mapping a section along the transition maps of iterated fibre products and then to those of
`E` is the same as mapping it along the maps from `E` at the later stage. -/
private lemma map_cechProductMap_toStageFamily_apply (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (n : ℕ)
    (t : Fin (n + 1) → E.I₀) {j k : Λ} (g : j ⟶ k)
    (y : F.obj (op (∏ᶜ (fun a ↦ Over.mk ((stageFamily E B M m k).f (t a)))).left)) :
    F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t).op
        (F.map (cechProductMap (stageFamily E B M m j) (stageFamily E B M m k)
          (stageFamilyHomOver E B M m g) n t).op y) =
      F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ k) n t).op y := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
    cechProductMap_toStageFamily_comp_stageFibreProduct_map E B M m πB π hπ n t g]

section Limit

variable {D : Type*} [Category* D] (q : C ⥤ D)
  (hB : IsLimit (q.mapCone (Cone.mk U πB)))
  (hM : ∀ i, IsLimit (q.mapCone (Cone.mk (E.X i) (π i))))
  [hqE : ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
    PreservesLimit (Discrete.functor fun a ↦ Over.mk (E.f (t a))) (Over.post q)]
  [hqS : ∀ (j : Λ) (n : ℕ) (t : Fin (n + 1) → E.I₀),
    PreservesLimit (Discrete.functor fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))
      (Over.post q)]

/-- The base of a cone over the images of the iterated fibre products at the stages, as a cone
over the images of the targets. -/
noncomputable abbrev stageFibreProductBaseCone (n : ℕ) (t : Fin (n + 1) → E.I₀)
    (s : Cone (stageFibreProduct E B M m n t ⋙ q)) : Cone (B ⋙ q) where
  pt := s.pt
  π :=
    { app j := s.π.app j ≫ q.map (∏ᶜ (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))).hom
      naturality {j k} g := by
        have h := s.w g
        dsimp at h ⊢
        rw [Category.id_comp, ← h, Category.assoc, Category.assoc, ← q.map_comp, ← q.map_comp,
          cechProductMap_comp_hom] }

/-- The `a`-th factor of a cone over the images of the iterated fibre products at the stages, as
a cone over the images of the members. -/
noncomputable abbrev stageFibreProductFactorCone (n : ℕ) (t : Fin (n + 1) → E.I₀)
    (s : Cone (stageFibreProduct E B M m n t ⋙ q)) (b : Fin (n + 1)) : Cone (M (t b) ⋙ q) where
  pt := s.pt
  π :=
    { app j := s.π.app j ≫
        q.map (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b).left
      naturality {j k} g := by
        have h := s.w g
        dsimp at h ⊢
        rw [Category.id_comp, ← h, Category.assoc, Category.assoc, ← q.map_comp, ← q.map_comp,
          cechProductMap_stageFamilyHomOver_comp_π_left] }

include hB hM in
/-- **Iterated fibre products of a limit of families are limits.** If `q` carries the targets
and the members of `E` to the limits of the corresponding systems, and preserves the iterated
fibre products of `E` and of the families at the stages, then it carries the iterated fibre
product `U_{i_0} ×_U ⋯ ×_U U_{i_n}` to the limit of the system of iterated fibre products at
the stages. -/
noncomputable def isLimitMapConeStageFibreProductCone (n : ℕ) (t : Fin (n + 1) → E.I₀) :
    IsLimit (q.mapCone (stageFibreProductCone E B M m πB π hπ n t)) := by
  have hP := isLimitFanMkObjOfIsLimit (Over.post q) _ _
    (productIsProduct fun a ↦ Over.mk (E.f (t a)))
  have hPj (j : Λ) := isLimitFanMkObjOfIsLimit (Over.post q) _ _
    (productIsProduct fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))
  have hfac (s : Cone (stageFibreProduct E B M m n t ⋙ q)) (b : Fin (n + 1)) :
      (hM (t b)).lift (stageFibreProductFactorCone E B M m q n t s b) ≫ q.map (E.f (t b)) =
        hB.lift (stageFibreProductBaseCone E B M m q n t s) := by
    refine hB.hom_ext fun j ↦ ?_
    have h₁ := (hM (t b)).fac (stageFibreProductFactorCone E B M m q n t s b) j
    have h₂ := hB.fac (stageFibreProductBaseCone E B M m q n t s) j
    dsimp at h₁ h₂ ⊢
    rw [h₂, Category.assoc, ← q.map_comp, ← hπ, q.map_comp, reassoc_of% h₁, ← q.map_comp]
    exact congrArg (fun x ↦ s.π.app j ≫ q.map x)
      (Over.w (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b))
  let lift (s : Cone (stageFibreProduct E B M m n t ⋙ q)) :
      s.pt ⟶ q.obj (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left :=
    (hP.lift (Fan.mk (Over.mk (hB.lift (stageFibreProductBaseCone E B M m q n t s)))
      fun b ↦ (Over.homMk ((hM (t b)).lift (stageFibreProductFactorCone E B M m q n t s b))
        (hfac s b) : Over.mk (hB.lift (stageFibreProductBaseCone E B M m q n t s)) ⟶
          (Over.post q).obj (Over.mk (E.f (t b)))))).left
  have hlift (s : Cone (stageFibreProduct E B M m n t ⋙ q)) (b : Fin (n + 1)) :
      lift s ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (t a))) b).left =
        (hM (t b)).lift (stageFibreProductFactorCone E B M m q n t s b) :=
    (congrArg CommaMorphism.left (hP.fac _ ⟨b⟩)).trans rfl
  refine
    { lift := lift
      fac := fun s j ↦ Over.left_hom_ext_of_isLimit (hPj j) fun b ↦ ?_
      uniq := fun s f hf ↦ Over.left_hom_ext_of_isLimit hP fun b ↦ ?_ }
  · have h₁ := (hM (t b)).fac (stageFibreProductFactorCone E B M m q n t s b) j
    dsimp at h₁
    change (lift s ≫ q.map (cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t)) ≫
        q.map (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b).left =
      s.π.app j ≫ q.map (Pi.π (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a))) b).left
    rw [Category.assoc, ← q.map_comp, cechProductMap_toStageFamily_comp_π_left, q.map_comp,
      reassoc_of% (hlift s b), h₁]
  · have h₁ := (hM (t b)).fac (stageFibreProductFactorCone E B M m q n t s b)
    have h₂ := hf
    change f ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (t a))) b).left =
      lift s ≫ q.map (Pi.π (fun a ↦ Over.mk (E.f (t a))) b).left
    rw [hlift s b]
    refine (hM (t b)).hom_ext fun j ↦ ?_
    have h₁ := h₁ j
    have h₂ := h₂ j
    dsimp at h₁ h₂ ⊢
    rw [h₁, ← h₂, Category.assoc, Category.assoc, ← q.map_comp, ← q.map_comp,
      cechProductMap_toStageFamily_comp_π_left]

end Limit

variable [HasProducts.{w} AddCommGrpCat.{a}] (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})

/-- The maps of Čech complexes from the stages to `E` are compatible with the transitions. -/
lemma cechComplexMap_stageFamilyHomOver_comp {j k : Λ} (g : k ⟶ j) :
    cechComplexMap _ _ (stageFamilyHomOver E B M m g) F ≫
        cechComplexMap E _ (toStageFamily E B M m πB π hπ k) F =
      cechComplexMap E _ (toStageFamily E B M m πB π hπ j) F := by
  ext n : 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ cechComplex_X_ext E F n fun t ↦ ?_)
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply, cechComplexMap_f_apply_π,
    cechComplexMap_f_apply_π, cechComplexMap_f_apply_π]
  exact map_cechProductMap_toStageFamily_apply E B M m πB π hπ F n t g _

variable [IsCofiltered Λ] [Finite E.I₀]
  (hcolim : ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
    IsColimit ((F ⋙ forget AddCommGrpCat.{a}).mapCocone
      (stageFibreProductCone E B M m πB π hπ n t).op))

include hcolim in
/-- Every Čech cochain of `E` comes from a Čech cochain at some stage. -/
lemma exists_cechComplexMap_toStageFamily_apply_eq (n : ℕ) (x : (cechComplex E F).X n) :
    ∃ (j : Λ) (x' : (cechComplex (stageFamily E B M m j) F).X n),
      (cechComplexMap E _ (toStageFamily E B M m πB π hπ j) F).f n x' = x := by
  classical
  have : Fintype (Fin (n + 1) → E.I₀) := Fintype.ofFinite _
  have hx (t : Fin (n + 1) → E.I₀) : ∃ (j : Λ)
      (y : F.obj (op ((∏ᶜ (fun a ↦ Over.mk ((stageFamily E B M m j).f (t a)))).left))),
      F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t).op y =
        Pi.π (cochainFactor E F n) t x := by
    obtain ⟨j, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit (hcolim n t) (Pi.π (cochainFactor E F n) t x)
    exact ⟨j.unop, y, hy⟩
  choose J y hy using hx
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image J)
  have hk' (t : Fin (n + 1) → E.I₀) : Nonempty (k ⟶ J t) :=
    hk (Finset.mem_image_of_mem J (Finset.mem_univ t))
  let x' : (∏ᶜ cochainFactor (stageFamily E B M m k) F n : AddCommGrpCat.{a}) :=
    (productAddEquiv (cochainFactor (stageFamily E B M m k) F n)).symm fun t ↦
    F.map (cechProductMap (stageFamily E B M m k) (stageFamily E B M m (J t))
      (stageFamilyHomOver E B M m (hk' t).some) n t).op (y t)
  refine ⟨k, x', cechComplex_X_ext E F n fun t ↦ ?_⟩
  refine (cechComplexMap_f_apply_π E _ (toStageFamily E B M m πB π hπ k) F n t x').trans ?_
  rw [← hy t]
  have hx' : ConcreteCategory.hom (Pi.π (cochainFactor (stageFamily E B M m k) F n) t) x' =
      F.map (cechProductMap (stageFamily E B M m k) (stageFamily E B M m (J t))
        (stageFamilyHomOver E B M m (hk' t).some) n t).op (y t) :=
    congrFun ((productAddEquiv (cochainFactor (stageFamily E B M m k) F n)).apply_symm_apply _) t
  refine (congrArg (ConcreteCategory.hom
    (F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ k) n t).op)) hx').trans ?_
  exact map_cechProductMap_toStageFamily_apply E B M m πB π hπ F n t _ (y t)

include hcolim in
/-- A Čech cochain at a stage which becomes zero on `E` already becomes zero at a later
stage. -/
lemma exists_cechComplexMap_stageFamilyHomOver_apply_eq_zero (n : ℕ) (j : Λ)
    (y : (cechComplex (stageFamily E B M m j) F).X n)
    (hy : (cechComplexMap E _ (toStageFamily E B M m πB π hπ j) F).f n y = 0) :
    ∃ (k : Λ) (g : k ⟶ j),
      (cechComplexMap _ _ (stageFamilyHomOver E B M m g) F).f n y = 0 := by
  classical
  have : Fintype (Fin (n + 1) → E.I₀) := Fintype.ofFinite _
  have hy₀ (t : Fin (n + 1) → E.I₀) :
      F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t).op
        (ConcreteCategory.hom (Pi.π (cochainFactor (stageFamily E B M m j) F n) t) y) =
      F.map (cechProductMap E _ (toStageFamily E B M m πB π hπ j) n t).op 0 := by
    rw [map_zero]
    exact (cechComplexMap_f_apply_π E _ (toStageFamily E B M m πB π hπ j) F n t y).symm.trans
      ((congrArg (ConcreteCategory.hom (Pi.π (cochainFactor E F n) t)) hy).trans (map_zero _))
  have hK (t : Fin (n + 1) → E.I₀) : ∃ (k : Λ) (g : k ⟶ j),
      F.map ((stageFibreProduct E B M m n t).map g).op
          (ConcreteCategory.hom (Pi.π (cochainFactor (stageFamily E B M m j) F n) t) y) =
        0 := by
    obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' (hcolim n t) _ _).mp (hy₀ t)
    refine ⟨k.unop, g.unop, hg.trans ?_⟩
    exact map_zero (ConcreteCategory.hom (F.map ((stageFibreProduct E B M m n t).map g.unop).op))
  choose K g hg using hK
  let O : Finset Λ := insert j (Finset.univ.image K)
  have hKO (t : Fin (n + 1) → E.I₀) : K t ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem K (Finset.mem_univ t))
  have hjO : j ∈ O := Finset.mem_insert_self j _
  obtain ⟨k, T, hT⟩ := IsCofiltered.inf_exists O
    (Finset.univ.image fun t ↦ (⟨K t, j, hKO t, hjO, g t⟩ :
      (X : Λ) ×' (Y : Λ) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)))
  refine ⟨k, T hjO, cechComplex_X_ext _ F n fun t ↦ ?_⟩
  have hTt : T (hKO t) ≫ g t = T hjO :=
    hT (hKO t) hjO (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  refine (cechComplexMap_f_apply_π _ _ (stageFamilyHomOver E B M m (T hjO)) F n t y).trans
    (Eq.trans ?_ (map_zero (ConcreteCategory.hom
      (Pi.π (cochainFactor (stageFamily E B M m k) F n) t))).symm)
  change ConcreteCategory.hom (F.map ((stageFibreProduct E B M m n t).map (T hjO)).op)
    (ConcreteCategory.hom (Pi.π (cochainFactor (stageFamily E B M m j) F n) t) y) = 0
  have e : (stageFibreProduct E B M m n t).map (T hjO) =
      (stageFibreProduct E B M m n t).map (T (hKO t)) ≫ (stageFibreProduct E B M m n t).map (g t) :=
    by rw [← Functor.map_comp, hTt]
  rw [e, op_comp, F.map_comp]
  exact (congrArg (ConcreteCategory.hom (F.map ((stageFibreProduct E B M m n t).map
    (T (hKO t))).op)) (hg t)).trans (map_zero _)


include hcolim in
/-- **Čech cohomology of a cofiltered limit of families.** Let `E = {U_i → U}` be a finite
family which is the limit of a cofiltered system of families `{U_{i,λ} → U_λ}` with the same
index set, and let `F` be an abelian presheaf whose sections over every iterated fibre product
`U_{i_0} ×_U ⋯ ×_U U_{i_n}` are the filtered colimit of its sections over the iterated fibre
products `U_{i_0,λ} ×_{U_λ} ⋯ ×_{U_λ} U_{i_n,λ}`.  If the degree-`p` Čech cohomology of `F`
vanishes along every family `{U_{i,λ} → U_λ}`, it vanishes along `E`. -/
theorem isZero_cechCohomology_of_isColimit (p : ℕ)
    (hp : ∀ j, IsZero (cechCohomology (stageFamily E B M m j) F p)) :
    IsZero (cechCohomology E F p) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine HomologicalComplex.exactAt_of_forall_exists _ p
    (fun j ↦ cechComplex (stageFamily E B M m j) F)
    (fun j ↦ cechComplexMap E _ (toStageFamily E B M m πB π hπ j) F)
    (fun j ↦ (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hp j))
    (exists_cechComplexMap_toStageFamily_apply_eq E B M m πB π hπ F hcolim p) ?_
  intro j y hy
  obtain ⟨k, g, hg⟩ :=
    exists_cechComplexMap_stageFamilyHomOver_apply_eq_zero E B M m πB π hπ F hcolim _ j y hy
  exact ⟨k, cechComplexMap _ _ (stageFamilyHomOver E B M m g) F,
    cechComplexMap_stageFamilyHomOver_comp E B M m πB π hπ F g, hg⟩

end System

end Stacks.CechSite
