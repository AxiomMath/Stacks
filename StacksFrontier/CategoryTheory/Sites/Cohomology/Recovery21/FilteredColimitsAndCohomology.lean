module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FiniteCoveringsWithIntersections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing

/-!
# Filtered colimits and cohomology on a site

Let `B` be a collection of objects of a site and let a collection of covering families be
given which is cofinal among the coverings of every object of `B`, is finite, and whose
nonempty iterated fibre products again lie in `B`. Then filtered colimits of abelian sheaves
commute with cohomology over every object of `B`.

## Main results

* `Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections`: the canonical comparison
  from the filtered colimit of the cohomology groups to the cohomology of the filtered colimit
  is an isomorphism.

## Implementation notes

The hypothesis on the covering families is
`Stacks.Cohomology.HasIntersectionsIn`, which states an iterated fibre product invariantly as
the vertex of a limiting wide-pullback cone; `fanOverOfWidePullbackCone` turns such a cone into
the product in the over category that the Čech complex of Stacks 03AM is indexed by. The
conclusion uses `Functor.rightDerived` for cohomology and `colimit.post` for the canonical
comparison map.

The proof is the `δ`-functor argument of the source. Cohomology over `U` is presented as `Ext`
out of the sheafification of the free abelian presheaf on `yoneda.obj U`
(`sectionsExtDeltaFunctor`, identified with the right-derived sections functor by
`sectionsExtRightDerivedIso`), which makes it a `δ`-functor in the sheaf. The comparison with
the filtered colimit is then a morphism of `δ`-functors, and
`isIso_deltaFunctor_app_of_common_effacements` reduces being an isomorphism in every degree to
degree zero plus a common effacement. Degree zero is the statement that sections over `U`
commute with the filtered colimit, which is where the cofinal finite coverings are used; the
effacement is the vanishing of Čech cohomology of a filtered colimit of injective sheaves,
which comes from `Stacks.CechSite.injective_presheaf_cechCohomology_isZero` (Stacks 03OR) via
the Čech-to-sheaf-cohomology comparison of Stacks 03F9.

Since the chosen coverings have an unrestricted index universe but the Čech comparison of
Stacks 03F9 needs them in the universe of the site, the families are replaced by
index-reindexed copies generating the same sieve (`exists_small_cover_intersections`) and `B`
is replaced by its closure under isomorphism (`isoClosure`), which changes neither the sieves
nor the hypothesis.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab

/-- The functor of sections over `U`, from abelian sheaves on `J` to `Ab`, is additive. -/
noncomputable local instance sections_additive {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) :
    ((sheafSections J (Ab.{u})).obj (op U)).Additive where
  map_add := by intros; rfl


/-- A finite family can be reindexed by a type in a given universe without changing its sieve. -/
private lemma exists_restrictIndex_ulift {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) [Finite E.I₀] :
    ∃ e : ULift.{max u v} (Fin (Nat.card E.I₀)) ≃ E.I₀, (E.restrictIndex e).sieve₀ = E.sieve₀ := by
  classical
  let e : ULift.{max u v} (Fin (Nat.card E.I₀)) ≃ E.I₀ :=
    Equiv.ulift.trans (Finite.equivFin E.I₀).symm
  refine ⟨e, ?_⟩
  change Sieve.generate (E.restrictIndex e).presieve₀ = Sieve.generate E.presieve₀
  rw [E.presieve₀_restrictIndex_equiv e]

private lemma isQuasiCompactObject_of_finite_refinements {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C}
    (h : ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      Finite E.I₀ ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S) : J.IsQuasiCompactObject U := by
  classical
  intro E hE
  obtain ⟨E', hfin, hE', hle⟩ := h E.sieve₀ hE
  let := hfin
  obtain ⟨e, heq⟩ := exists_restrictIndex_ulift E'
  let E'' := E'.restrictIndex e
  have : Finite E''.I₀ := by dsimp [E'', PreZeroHypercover.restrictIndex]; infer_instance
  have hle' : E''.sieve₀ ≤ E.sieve₀ := heq ▸ hle
  choose s α hα using fun c : E''.I₀ =>
    (Sieve.mem_ofArrows_iff _ _ _).1 (hle' _ (E''.sieve₀_f c))
  exact ⟨E'', ⟨s, α, fun c => (hα c).symm⟩, heq ▸ hE', Set.finite_range _⟩

private lemma hasIntersectionsIn_restrictIndex {C : Type u} [Category.{v} C]
    {B : Set C} {U : C} {E : PreZeroHypercover.{w} U} (h : HasIntersectionsIn B E)
    {α : Type*} [Finite α] (f : α → E.I₀) : HasIntersectionsIn B (E.restrictIndex f) :=
  ⟨by dsimp [PreZeroHypercover.restrictIndex]; infer_instance, h.2.1,
    fun i => h.2.2.1 (f i), fun n a => h.2.2.2 n (f ∘ a)⟩

private lemma exists_small_cover_intersections {C : Type u} [Category.{v} C] {U : C}
    {B : Set C} (E : PreZeroHypercover.{w} U) (h : HasIntersectionsIn B E) :
    ∃ E' : PreZeroHypercover.{max u v} U,
      HasIntersectionsIn B E' ∧ E'.sieve₀ = E.sieve₀ := by
  let := h.1
  obtain ⟨e, he⟩ := exists_restrictIndex_ulift E
  exact ⟨E.restrictIndex e, hasIntersectionsIn_restrictIndex h e, he⟩

private lemma exists_pullback_mem {C : Type u} [Category.{v} C]
    {B : Set C} {U : C} {E : PreZeroHypercover.{w} U} (h : HasIntersectionsIn B E)
    (i j : E.I₀) : ∃ (W : C) (p : W ⟶ E.X i) (q : W ⟶ E.X j),
      IsPullback p q (E.f i) (E.f j) ∧ B W := by
  obtain ⟨t, ⟨ht⟩, hB⟩ := h.2.2.2 1 (Fin.cases i (fun _ => j))
  refine ⟨t.pt, t.π 0, t.π 1, ?_, hB⟩
  -- Construct the ordinary pullback cone from the two projections.
  apply IsPullback.of_isLimit (c := PullbackCone.mk (t.π 0) (t.π 1)
    ((t.condition 0).trans (t.condition 1).symm))
  refine PullbackCone.IsLimit.mk _ (fun s => WidePullbackCone.IsLimit.lift ht
    (s.fst ≫ E.f i) (fun k => Fin.cases s.fst (fun _ => s.snd) k)
      (by
        intro k
        fin_cases k
        · rfl
        · exact s.condition.symm)) ?_ ?_ ?_
  · intro s; exact WidePullbackCone.IsLimit.lift_π ht _ _ _ 0
  · intro s; exact WidePullbackCone.IsLimit.lift_π ht _ _ _ 1
  · intro s m h₁ h₂
    refine WidePullbackCone.IsLimit.hom_ext ht ?_ ?_
    · rw [WidePullbackCone.IsLimit.lift_base, ← t.condition 0, ← Category.assoc, h₁]
      rfl
    · intro k
      rw [WidePullbackCone.IsLimit.lift_π]
      fin_cases k
      · exact h₁
      · exact h₂

private lemma bijective_colimit_post_sections {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Type u)) (U : C) (hU : B U) :
    Function.Bijective (colimit.post F ((sheafSections J (Type u)).obj (op U))) := by
  have hqc : ∀ V, B V → J.IsQuasiCompactObject V := fun V hV =>
    isQuasiCompactObject_of_finite_refinements J (fun S hS => by
      obtain ⟨E, hE, hc, hr⟩ := h V hV S hS
      exact ⟨E, hE.1, hc, hr⟩)
  apply (Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.2
  intro S hS
  obtain ⟨E, hE, hc, hr⟩ := h U hU S hS
  obtain ⟨E', hE', he⟩ := exists_small_cover_intersections E hE
  refine ⟨E', hE'.1, he ▸ hc, he ▸ hr, ?_⟩
  intro i j
  obtain ⟨W, p, q, hpq, hW⟩ := exists_pullback_mem hE' i j
  exact ⟨W, p, q, hpq, hqc W hW⟩

private lemma preservesColimit_of_composite
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {I : Type*} [Category* I] (F : I ⥤ A) [HasColimit F]
    (L : A ⥤ B) (R : B ⥤ D) [PreservesColimit F L] [PreservesColimit F (L ⋙ R)] :
    PreservesColimit (F ⋙ L) R :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves L (colimit.isColimit F))
    (isColimitOfPreserves (L ⋙ R) (colimit.isColimit F))

private lemma preservesColimit_sheafCompose_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ Sheaf J Ab.{u}) :
    PreservesColimit F (sheafCompose J (forget Ab.{u})) := by
  let L := presheafToSheaf J Ab.{u}
  let R := sheafToPresheaf J Ab.{u}
  let V := sheafCompose J (forget Ab.{u})
  have h : PreservesColimit (F ⋙ R) (L ⋙ V) :=
    preservesColimit_of_natIso (F ⋙ R)
      (sheafComposeNatIso J (forget Ab.{u}) (sheafificationAdjunction J Ab.{u})
        (sheafificationAdjunction J (Type u)))
  have h' : PreservesColimit ((F ⋙ R) ⋙ L) V :=
    preservesColimit_of_composite (F ⋙ R) L V
  exact preservesColimit_of_iso_diagram V
    ((Functor.associator F R L) ≪≫
      Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J Ab.{u}).counit) ≪≫
      Functor.rightUnitor F)

private lemma preservesColimit_sections {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J Ab.{u}) (U : C) (hU : B U) :
    PreservesColimit F ((sheafSections J Ab.{u}).obj (op U)) := by
  let V := sheafCompose J (forget Ab.{u})
  let T := (sheafSections J (Type u)).obj (op U)
  let S := (sheafSections J Ab.{u}).obj (op U)
  have : IsIso (colimit.post (F ⋙ V) T) :=
    (isIso_iff_bijective _).2 (bijective_colimit_post_sections J B h (F ⋙ V) U hU)
  have : PreservesColimit (F ⋙ V) T := preservesColimit_of_isIso_post _ _
  have : PreservesColimit F V := preservesColimit_sheafCompose_forget J F
  have : PreservesColimit F (S ⋙ forget Ab.{u}) :=
    inferInstanceAs (PreservesColimit F (V ⋙ T))
  have : ReflectsColimit (F ⋙ S) (forget Ab.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves S (forget Ab.{u})

private lemma isIso_third_of_isColimit
    {A : Type*} [Category* A] [Abelian A]
    {S T : ShortComplex A} (φ : S ⟶ T)
    (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    (hT : IsColimit (CokernelCofork.ofπ T.g T.zero))
    [IsIso φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  let e : Arrow.mk S.f ≅ Arrow.mk T.f :=
    Arrow.isoMk (asIso φ.τ₁) (asIso φ.τ₂) φ.comm₁₂
  let i := CokernelCofork.mapIsoOfIsColimit hS hT e
  have he : φ.τ₃ = i.hom := by
    apply Cofork.IsColimit.hom_ext hS
    show S.g ≫ φ.τ₃ = S.g ≫ CokernelCofork.mapOfIsColimit hS (CokernelCofork.ofπ T.g T.zero) e.hom
    exact φ.comm₂₃.symm.trans
      (CokernelCofork.π_mapOfIsColimit hS (CokernelCofork.ofπ T.g T.zero) e.hom).symm
  rw [he]
  infer_instance

@[sga "4 XII 6.2" "partial", sga "4½ Arcata 4.3.6" "(iii) ⇒ (i)"]
private lemma isIso_deltaFunctor_app_of_common_effacements
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {D E : DeltaFunctor A B} (η : D ⟶ E) [IsIso (η.app 0)]
    (heff : ∀ (X : A) (n : ℕ), ∃ (Y : A) (f : X ⟶ Y),
      Mono f ∧ (D.functor (n + 1)).map f = 0 ∧ (E.functor (n + 1)).map f = 0)
    (n : ℕ) (X : A) : IsIso ((η.app n).app X) := by
  induction n generalizing X with
  | zero => infer_instance
  | succ n ih =>
    obtain ⟨Y, f, hf, hd, he⟩ := heff X n
    let := hf
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel f)) hf inferInstance
    let φ : D.scδ₁ hS n ⟶ E.scδ₁ hS n :=
      { τ₁ := (η.app n).app Y
        τ₂ := (η.app n).app (cokernel f)
        τ₃ := (η.app (n + 1)).app X
        comm₁₂ := ((η.app n).naturality (cokernel.π f)).symm
        comm₂₃ := η.comm hS n }
    have : IsIso φ.τ₁ := ih Y
    have : IsIso φ.τ₂ := ih (cokernel f)
    exact isIso_third_of_isColimit φ (D.δIsCokernel hS n hd) (E.δIsCokernel hS n he)

/-- A wide pullback cone on a family `{Xₐ ⟶ U}`, read as a fan on the same family seen in
`Over U`: the vertex is its base equipped with its own structure morphism, and the projections
are the legs. -/
private noncomputable abbrev fanOverOfWidePullbackCone
    {C : Type u} [Category.{v} C] {U : C} {α : Type w} {X : α → C}
    {f : ∀ a, X a ⟶ U} (t : WidePullbackCone f) : Fan (fun a => Over.mk (f a)) :=
  Fan.mk (Over.mk t.base) (fun a => Over.homMk (t.π a) (t.condition a))

/-- A limiting wide pullback cone gives a limiting fan in `Over U`: a product of the objects
`Over.mk (f a)` is the same thing as a wide fibre product of the `f a`. -/
private noncomputable def isLimitFanOverOfWidePullbackCone
    {C : Type u} [Category.{v} C] {U : C} {α : Type w} {X : α → C}
    {f : ∀ a, X a ⟶ U} (t : WidePullbackCone f) (ht : IsLimit t) :
    IsLimit (fanOverOfWidePullbackCone t) := by
  refine Fan.IsLimit.mk _ (fun s => Over.homMk
    (WidePullbackCone.IsLimit.lift ht s.pt.hom (fun a => (s.proj a).left)
      (fun a => Over.w (s.proj a))) ?_) ?_ ?_
  · exact WidePullbackCone.IsLimit.lift_base ht _ _ _
  · intro s a
    apply Over.OverMorphism.ext
    exact WidePullbackCone.IsLimit.lift_π ht _ _ _ a
  · intro s m hm
    apply Over.OverMorphism.ext
    refine WidePullbackCone.IsLimit.hom_ext ht ?_ ?_
    · change Over.Hom.left m ≫ t.base =
        WidePullbackCone.IsLimit.lift ht s.pt.hom (fun a => Over.Hom.left (s.proj a))
          (fun a => Over.w (s.proj a)) ≫ t.base
      rw [WidePullbackCone.IsLimit.lift_base]
      exact Over.w m
    · intro a
      change Over.Hom.left m ≫ t.π a =
        WidePullbackCone.IsLimit.lift ht s.pt.hom (fun b => Over.Hom.left (s.proj b))
          (fun b => Over.w (s.proj b)) ≫ t.π a
      rw [WidePullbackCone.IsLimit.lift_π]
      exact congrArg (fun f => f.left) (hm a)

/-- A choice of wide fibre product of a finite subfamily of a covering family all of whose
nonempty finite fibre products lie in `B`. -/
private noncomputable def intersectionsWidePullback
    {C : Type u} [Category.{v} C] {B : Set C} {U : C} {E : PreZeroHypercover.{w} U}
    (h : HasIntersectionsIn B E) (n : ℕ) (a : Fin (n + 1) → E.I₀) :
    WidePullbackCone (fun i ↦ E.f (a i)) := Classical.choose (h.2.2.2 n a)

/-- The defining property of `Stacks.Cohomology.intersectionsWidePullback`: it is a limit cone
and its vertex lies in `B`. -/
private lemma intersectionsWidePullback_spec
    {C : Type u} [Category.{v} C] {B : Set C} {U : C} {E : PreZeroHypercover.{w} U}
    (h : HasIntersectionsIn B E) (n : ℕ) (a : Fin (n + 1) → E.I₀) :
    Nonempty (IsLimit (intersectionsWidePullback h n a)) ∧
      B (intersectionsWidePullback h n a).pt := Classical.choose_spec (h.2.2.2 n a)

/-- A covering family whose nonempty finite fibre products exist — which is what
`Stacks.Cohomology.HasIntersectionsIn` provides — has the products in `Over U` out of which the
Čech complex of the family is built. -/
lemma HasIntersectionsIn.hasProduct_over
    {C : Type u} [Category.{v} C] {B : Set C} {U : C} {E : PreZeroHypercover.{w} U}
    (h : HasIntersectionsIn B E) (n : ℕ) (a : Fin (n + 1) → E.I₀) :
    HasProduct (fun i => Over.mk (E.f (a i))) := by
  let t := intersectionsWidePullback h n a
  obtain ⟨ht⟩ := (intersectionsWidePullback_spec h n a).1
  exact ⟨⟨fanOverOfWidePullbackCone t, isLimitFanOverOfWidePullbackCone t ht⟩⟩

/-- The vertex of such a product in `Over U` is isomorphic to an object of `B`. It need not be
*equal* to one: the product is a chosen limit, and `B` is a bare set of objects, so a consumer
asking for membership rather than for an isomorphism needs `B` closed under isomorphism. -/
lemma HasIntersectionsIn.exists_mem_iso_prod_over
    {C : Type u} [Category.{v} C] {B : Set C} {U : C} {E : PreZeroHypercover.{w} U}
    (h : HasIntersectionsIn B E) (n : ℕ) (a : Fin (n + 1) → E.I₀)
    [HasProduct (fun i => Over.mk (E.f (a i)))] :
    ∃ V, B V ∧ Nonempty ((∏ᶜ (fun i => Over.mk (E.f (a i)))).left ≅ V) := by
  obtain ⟨t, ⟨ht⟩, hB⟩ := h.2.2.2 n a
  let e : (∏ᶜ (fun i => Over.mk (E.f (a i)))) ≅ Over.mk t.base :=
    (limit.isLimit _).conePointUniqueUpToIso (isLimitFanOverOfWidePullbackCone t ht)
  exact ⟨t.pt, hB, ⟨(Over.forget U).mapIso e⟩⟩

private def isoClosure {C : Type u} [Category.{v} C] (B : Set C) : Set C :=
  {V | ∃ W, B W ∧ Nonempty (V ≅ W)}

private lemma mem_isoClosure_of_mem {C : Type u} [Category.{v} C] {B : Set C}
    {U : C} (hU : B U) : isoClosure B U :=
  ⟨U, hU, ⟨Iso.refl U⟩⟩

private lemma hasIntersectionsIn_pushforward_iso {C : Type u} [Category.{v} C]
    {B : Set C} {V W : C} {E : PreZeroHypercover.{w} W}
    (hE : HasIntersectionsIn B E) (e : V ≅ W) :
    HasIntersectionsIn (isoClosure B) (E.pushforward e.inv) := by
  refine ⟨hE.1, ⟨W, hE.2.1, ⟨e⟩⟩,
    fun i => ⟨E.X i, hE.2.2.1 i, ⟨Iso.refl _⟩⟩, ?_⟩
  intro n a
  let a' : Fin (n + 1) → E.I₀ := fun i => a i
  let t := intersectionsWidePullback hE n a'
  have ht := (intersectionsWidePullback_spec hE n a').1.some
  have hB := (intersectionsWidePullback_spec hE n a').2
  let t' : WidePullbackCone (fun i => (E.pushforward e.inv).f (a' i)) :=
    WidePullbackCone.mk (t.base ≫ e.inv) t.π (by
      intro i
      show t.π i ≫ (E.f (a' i) ≫ e.inv) = t.base ≫ e.inv
      rw [← Category.assoc, t.condition i])
  let oldCone (s : WidePullbackCone (fun i => (E.pushforward e.inv).f (a' i))) :
      WidePullbackCone (fun i => E.f (a' i)) :=
    WidePullbackCone.mk (s.base ≫ e.hom) s.π (by
      intro i
      have hi := s.condition i
      change s.π i ≫ (E.f (a' i) ≫ e.inv) = s.base at hi
      apply (cancel_mono e.inv).mp
      calc
        (s.π i ≫ E.f (a' i)) ≫ e.inv = s.base :=
          (Category.assoc _ _ _).trans hi
        _ = (s.base ≫ e.hom) ≫ e.inv := by simp)
  let lift (s : WidePullbackCone (fun i => (E.pushforward e.inv).f (a' i))) :=
    WidePullbackCone.IsLimit.lift ht (s.base ≫ e.hom) s.π (oldCone s).condition
  have hfac (s : WidePullbackCone (fun i => (E.pushforward e.inv).f (a' i))) :
      lift s ≫ t.base = s.base ≫ e.hom := by
    simpa [lift, t] using
      WidePullbackCone.IsLimit.lift_base ht (s.base ≫ e.hom) s.π (oldCone s).condition
  have hlπ (s : WidePullbackCone (fun i => (E.pushforward e.inv).f (a' i))) (i : Fin (n + 1)) :
      lift s ≫ t.π i = s.π i := by
    simpa [lift] using
      WidePullbackCone.IsLimit.lift_π ht (s.base ≫ e.hom) s.π (oldCone s).condition i
  have ht' : IsLimit t' := by
    refine WidePullbackCone.IsLimit.mk t' lift ?_ hlπ ?_
    · intro s
      show lift s ≫ (t.base ≫ e.inv) = s.base
      rw [← Category.assoc, hfac s]
      simp
    · intro s m hm hπ
      have hbase : m ≫ t.base = lift s ≫ t.base := by
        apply (cancel_mono e.inv).mp
        calc
          (m ≫ t.base) ≫ e.inv = m ≫ t'.base := Category.assoc _ _ _
          _ = s.base := by simpa [t'] using hm
          _ = (s.base ≫ e.hom) ≫ e.inv := by simp
          _ = (lift s ≫ t.base) ≫ e.inv :=
            congrArg (fun f => f ≫ e.inv) (hfac s).symm
      have hπ' : ∀ i, m ≫ t.π i = lift s ≫ t.π i := fun i => (hπ i).trans (hlπ s i).symm
      exact WidePullbackCone.IsLimit.hom_ext ht hbase hπ'
  exact ⟨t', ⟨ht'⟩, t.pt, hB, ⟨Iso.refl _⟩⟩

private lemma pushforward_sieve_eq_pullback_iso {C : Type u} [Category.{v} C]
    {V W : C} (e : V ≅ W) (E : PreZeroHypercover.{w} W) :
    (E.pushforward e.inv).sieve₀ = E.sieve₀.pullback e.hom := by
  rw [Sieve.pullback_ofArrows_of_iso E.X E.f e]
  rfl

private lemma exists_small_cover_isoClosure {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ V, B V → ∀ S ∈ J V, ∃ E : PreZeroHypercover.{w} V,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J V ∧ E.sieve₀ ≤ S)
    {U : C} (hU : isoClosure B U) (S : Sieve U) (hS : S ∈ J U) :
    ∃ E : PreZeroHypercover.{max u v} U,
      HasIntersectionsIn (isoClosure B) E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S := by
  obtain ⟨V, hV, ⟨e⟩⟩ := hU
  obtain ⟨E, hE, hEc, hES⟩ := h V hV (S.pullback e.inv) (J.pullback_stable e.inv hS)
  let E' := E.pushforward e.inv
  have hE' : HasIntersectionsIn (isoClosure B) E' :=
    hasIntersectionsIn_pushforward_iso hE e
  have hEc' : E'.sieve₀ ∈ J U := by
    rw [pushforward_sieve_eq_pullback_iso e E]
    exact J.pullback_stable e.hom hEc
  have hES' : E'.sieve₀ ≤ S := by
    rw [pushforward_sieve_eq_pullback_iso e E]
    intro X f hf
    have hf' : E.sieve₀ (f ≫ e.hom) := hf
    have hmem := hES (f ≫ e.hom) hf'
    change S ((f ≫ e.hom) ≫ e.inv) at hmem
    simpa [Category.assoc] using hmem
  obtain ⟨E'', hE'', hEq⟩ := exists_small_cover_intersections E' hE'
  exact ⟨E'', hE'', hEq ▸ hEc', hEq ▸ hES'⟩

private lemma preservesColimit_sections_of_iso
    {C A I : Type*} [Category* C] [Category* A] [Category* I]
    (J : GrothendieckTopology C) (F : I ⥤ Sheaf J A) {X Y : C} (e : X ≅ Y)
    [PreservesColimit F ((sheafSections J A).obj (op X))] :
    PreservesColimit F ((sheafSections J A).obj (op Y)) :=
  preservesColimit_of_natIso F ((sheafSections J A).mapIso e.symm.op)

private lemma preservesColimit_sections_isoClosure {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J Ab.{u}) {U : C} (hU : isoClosure B U) :
    PreservesColimit F ((sheafSections J Ab.{u}).obj (op U)) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := hU
  have := preservesColimit_sections J B h F V hV
  exact preservesColimit_sections_of_iso J F e.symm

private lemma preservesColimit_sections_intersections_isoClosure
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J Ab.{u}) {U : C} (E : PreZeroHypercover.{u} U)
    (hE : HasIntersectionsIn (isoClosure B) E) (n : ℕ)
    (a : Fin (n + 1) → E.I₀)
    [HasProduct (fun i => Over.mk (E.f (a i)))] :
    PreservesColimit F ((sheafSections J Ab.{u}).obj
      (op (∏ᶜ (fun i => Over.mk (E.f (a i)))).left)) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := HasIntersectionsIn.exists_mem_iso_prod_over hE n a
  have := preservesColimit_sections_isoClosure J B h F hV
  exact preservesColimit_sections_of_iso J F e.symm

private lemma isIso_colimit_post_limit_finite
    {I : Type u} {D : Type*} [SmallCategory I] [IsFiltered I]
    [SmallCategory D] [FinCategory D]
    [PreservesFiniteLimits (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u})]
    (F : I ⥤ (D ⥤ Ab.{u})) : IsIso (colimit.post F lim) := by
  let T := F.flip
  let e : colimit F ≅ T ⋙ colim := NatIso.ofComponents
    (fun d => colimitObjIsoColimitCompEvaluation F d) (by
      intro d d' f
      exact colimit_map_colimitObjIsoColimitCompEvaluation_hom F f)
  let s := Functor.isoWhiskerRight T.flipIsoCurrySwapUncurry lim
  have h : colimit.post F lim ≫ lim.map e.hom =
      colim.map s.hom ≫ colim.map (limitIsoSwapCompLim T).inv ≫
        (colimitLimitToLimitColimitCone T).hom := by
    apply colimit.hom_ext
    intro i
    apply limit.hom_ext
    intro d
    simp only [T, e, s, NatIso.ofComponents_hom_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app,
      Functor.comp_obj, lim_obj, colim_obj, lim_map, colimit.ι_post_assoc,
      Category.assoc, limMap_π, limMap_π_assoc, limit.cone_x, colim_map,
      colimitLimitToLimitColimitCone_hom, Functor.mapCone_pt, Functor.id_obj, Iso.app_inv,
      ι_colimMap_assoc, limitIsoSwapCompLim_inv_app, limitIsoSwapCompLim_hom_app,
      Iso.inv_hom_id_assoc, Functor.whiskerRight_app, ι_colimitLimitToLimitColimit_π_assoc,
      Functor.curry_obj_obj_obj, Prod.swap_obj, Functor.uncurry_obj_obj, ι_colimMap,
      Functor.currying_unitIso_inv_app_app_app, Category.id_comp, Functor.flip_obj_obj,
      Functor.flipIsoCurrySwapUncurry_hom_app_app, Functor.flipIsoCurrySwapUncurry_inv_app_app]
    show limit.π (F.obj i) d ≫ (colimit.ι F i).app d ≫
      (colimitObjIsoColimitCompEvaluation F d).hom =
      limit.π (F.flip.flip.obj i) d ≫ colimit.ι (F.flip.obj d) i
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom,
      CategoryTheory.comp_evaluation]
    rfl
  have hsource : IsLimit (colim.mapCone (limit.cone T)) :=
    (PreservesLimit.preserves (K := T) (F := colim) (limit.isLimit T)).some
  have hcone : IsIso (colimitLimitToLimitColimitCone T).hom := by
    let e' := hsource.conePointUniqueUpToIso (limit.isLimit (T ⋙ colim))
    have he : (colimitLimitToLimitColimitCone T).hom = e'.hom := by
      apply limit.hom_ext
      intro d
      calc
        (colimitLimitToLimitColimitCone T).hom ≫ limit.π (T ⋙ colim) d =
            (colim.mapCone (limit.cone T)).π.app d :=
          (colimitLimitToLimitColimitCone T).w d
        _ = e'.hom ≫ limit.π (T ⋙ colim) d := by
          simp [e']
    rw [he]
    infer_instance
  have : IsIso (colim.map (limitIsoSwapCompLim T).inv) := inferInstance
  have : IsIso (colim.map s.hom) := inferInstance
  have : IsIso (lim.map e.hom) := inferInstance
  have : IsIso (colimitLimitToLimitColimitCone T).hom := hcone
  have : IsIso (colimit.post F lim ≫ lim.map e.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (colimit.post F lim) (lim.map e.hom)

section derived_category

attribute [local instance] HasDerivedCategory.standard

private lemma preservesColimit_cechTerm {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (_F : I ⥤ Sheaf J Ab.{u}) {U : C} (E : PreZeroHypercover.{u} U) (n : ℕ)
    [UnivLE.{u, u}] [HasProducts.{u} Ab.{u}]
    [∀ (n : ℕ) (a : Fin (n + 1) → E.I₀), HasProduct (fun i => Over.mk (E.f (a i)))]
    (hE : HasIntersectionsIn (isoClosure B) E) :
    PreservesColimitsOfShape I
      (((sheafToPresheaf J Ab.{u}) ⋙ Stacks.CechSite.cechComplexFunctor E) ⋙
      HomologicalComplex.eval Ab (ComplexShape.up ℕ) n) := by
  refine ⟨?_⟩
  intro F
  let : Finite E.I₀ := hE.1
  let L : Sheaf J Ab.{u} ⥤ (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{u}) := {
      obj G := Discrete.functor fun (a : Fin (n + 1) → E.I₀) =>
        ((sheafSections J Ab.{u}).obj (op (∏ᶜ (fun i => Over.mk (E.f (a i)))).left)).obj G
      map {G G'} φ := Discrete.natTrans fun (a : Discrete (Fin (n + 1) → E.I₀)) =>
        ((sheafSections J Ab.{u}).obj
          (op (∏ᶜ (fun i => Over.mk (E.f (a.as i)))).left)).map φ
      map_id G := by ext a; simp
      map_comp φ ψ := by ext a; simp }
  let : Fintype (Fin (n + 1) → E.I₀) := Fintype.ofFinite _
  let : FinCategory (Discrete (Fin (n + 1) → E.I₀)) := inferInstance
  let P : (Discrete (Fin (n + 1) → E.I₀) ⥤ Ab.{u}) ⥤ Ab.{u} := lim
  have hL : PreservesColimit F L := by
    apply preservesColimit_of_evaluation L F
    intro a
    dsimp [L]
    exact preservesColimit_sections_intersections_isoClosure J B h F E hE n a.as
  have hlim : IsIso (colimit.post (F ⋙ L) P) :=
    isIso_colimit_post_limit_finite (F ⋙ L)
  let : PreservesColimit (F ⋙ L) P := preservesColimit_of_isIso_post _ _
  let : PreservesColimit F L := hL
  show PreservesColimit F (L ⋙ P)
  infer_instance

private lemma preservesColimit_cechComplex {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J Ab.{u}) {U : C} (E : PreZeroHypercover.{u} U)
    [UnivLE.{u, u}] [HasProducts.{u} Ab.{u}]
    [∀ (n : ℕ) (a : Fin (n + 1) → E.I₀), HasProduct (fun i => Over.mk (E.f (a i)))]
    (hE : HasIntersectionsIn (isoClosure B) E) :
    PreservesColimit F ((sheafToPresheaf J Ab.{u}) ⋙ Stacks.CechSite.cechComplexFunctor E) := by
  let : Finite E.I₀ := hE.1
  have hT : PreservesColimitsOfShape I
      ((sheafToPresheaf J Ab.{u}) ⋙ Stacks.CechSite.cechComplexFunctor E) :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n =>
      preservesColimit_cechTerm J B h F E n hE)
  exact hT.preservesColimit

open scoped ZeroObject in
private lemma exists_mono_into_injective_diagram
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    {I : Type*} [Category* I] (F : I ⥤ A) :
    ∃ (G : I ⥤ A) (α : F ⟶ G), Mono α ∧ ∀ i, Injective (G.obj i) := by
  let Z : I ⥤ Arrow A :=
    { obj i := Arrow.mk (0 : F.obj i ⟶ 0)
      map f := Arrow.homMk (F.map f) (𝟙 0) (by simp)
      map_id i := by ext <;> simp
      map_comp f g := by ext <;> simp }
  let d := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms A) (MorphismProperty.monomorphisms A).rlp
  let α : F ⟶ Z ⋙ d.Z :=
    { app i := d.i.app (Z.obj i)
      naturality i j f := d.i.naturality (Z.map f) }
  refine ⟨Z ⋙ d.Z, α, (NatTrans.mono_iff_mono_app α).2 fun i => d.hi (Z.obj i), fun i => ?_⟩
  exact inferInstanceAs
    (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : F.obj i ⟶ 0)).Z)

private lemma injective_cechCohomology_isZero_of_grothendieckTopology
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) {U : C}
    (E : PreZeroHypercover.{u} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [HasSheafify J Ab.{u}]
    (I : Sheaf J Ab.{u}) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E I.obj p) := by
  have : Injective I.obj :=
    (sheafificationAdjunction J Ab.{u}).map_injective I inferInstance
  exact Stacks.CechSite.injective_presheaf_cechCohomology_isZero.{u, u, u, u} E I.obj p hp

open CategoryTheory.Pretriangulated


private lemma exact_of_pointwise
    {I B : Type*} [SmallCategory I] [Category B] [Abelian B]
    (S : ShortComplex (I ⥤ B))
    (h : ∀ i, (S.map ((evaluation I B).obj i)).Exact) : S.Exact := by
  apply (ShortComplex.exact_iff_isZero_homology _).2
  apply (Functor.isZero_iff _).2
  intro i
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h i)).of_iso
    (S.mapHomologyIso ((evaluation I B).obj i)).symm

private lemma isZero_cechCohomology_colimit_of_injective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf J Ab.{u}) {U : C} (E : PreZeroHypercover.{u} U)
    (hE : HasIntersectionsIn (isoClosure B) E) (_hEc : E.sieve₀ ∈ J U)
    [UnivLE.{u, u}] [HasProducts.{u} Ab.{u}]
    [∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
      HasProduct (fun i => Over.mk (E.f (a i)))]
    (hG : ∀ i, Injective (G.obj i)) (p : ℕ) :
    IsZero (Stacks.CechSite.cechCohomology E (colimit G).obj (p + 1)) := by
  let T := (sheafToPresheaf J Ab.{u}) ⋙ Stacks.CechSite.cechComplexFunctor E
  let K := G ⋙ T
  have hpres : PreservesColimit G T :=
    preservesColimit_cechComplex J B h G E hE
  have hK (i : I) : (K.obj i).ExactAt (p + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ (p + 1)).2 (by
      simpa [K, T, Stacks.CechSite.cechCohomology] using
        injective_cechCohomology_isZero_of_grothendieckTopology J E
          (G.obj i) (p + 1) (Nat.zero_lt_succ p))
  have hcomm (k l : ℕ) (d : K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) k ⟶
      K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) l)
      (hd : ∀ i, d.app i = (K.obj i).d k l) :
      (preservesColimitIso (HomologicalComplex.eval Ab (ComplexShape.up ℕ) k) K).inv ≫
          (colimit K).d k l =
        colim.map d ≫
          (preservesColimitIso (HomologicalComplex.eval Ab (ComplexShape.up ℕ) l) K).inv := by
    refine colimit.hom_ext fun i => ?_
    simpa [hd] using (colimit.ι K i).comm k l
  let d₁ : (K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) p) ⟶
      (K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) (p + 1)) :=
    { app i := (K.obj i).d p (p + 1)
      naturality _ _ f := (K.map f).comm p (p + 1) }
  let d₂ : (K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) (p + 1)) ⟶
      (K ⋙ HomologicalComplex.eval Ab (ComplexShape.up ℕ) (p + 2)) :=
    { app i := (K.obj i).d (p + 1) (p + 2)
      naturality _ _ f := (K.map f).comm (p + 1) (p + 2) }
  let S : ShortComplex (I ⥤ Ab.{u}) := ShortComplex.mk d₁ d₂ (by ext i; simp [d₁, d₂])
  have hS : S.Exact := exact_of_pointwise S fun i => by
    show (HomologicalComplex.sc' (K.obj i) p (p + 1) (p + 2)).Exact
    exact (HomologicalComplex.exactAt_iff' (K.obj i) p (p + 1) (p + 2)
      (by simp) (by simp)).1 (hK i)
  let e (k : ℕ) := preservesColimitIso (HomologicalComplex.eval Ab (ComplexShape.up ℕ) k) K
  have hExact : (colimit K).ExactAt (p + 1) := by
    refine (HomologicalComplex.exactAt_iff' (colimit K) p (p + 1) (p + 2)
      (by simp) (by simp)).2 ((ShortComplex.exact_iff_of_iso ?_).1 (hS.map colim))
    exact ShortComplex.isoMk (e p).symm (e (p + 1)).symm (e (p + 2)).symm
      (hcomm p (p + 1) d₁ fun _ => rfl) (hcomm (p + 1) (p + 2) d₂ fun _ => rfl)
  exact (hExact.of_iso (asIso (colimit.post G T))).isZero_homology

private noncomputable def deltaPointwiseNatTrans
    {A B I : Type*} [Category A] [Category B] [SmallCategory I]
    [Abelian A] [Abelian B] (D : DeltaFunctor A B) {S : ShortComplex (I ⥤ A)}
    (hS : S.ShortExact) (n : ℕ) :
    ((Functor.whiskeringRight I A B).obj (D.functor n)).obj S.X₃ ⟶
      ((Functor.whiskeringRight I A B).obj (D.functor (n + 1))).obj S.X₁ := by
  let ev (i : I) := (evaluation I A).obj i
  refine
    { app := fun i => D.δ (hS.map_of_exact (ev i)) n
      naturality := ?_ }
  intro i j f
  let φ : (S.map (ev i)) ⟶ (S.map (ev j)) :=
    { τ₁ := S.X₁.map f
      τ₂ := S.X₂.map f
      τ₃ := S.X₃.map f
      comm₁₂ := S.f.naturality f
      comm₂₃ := S.g.naturality f }
  exact D.δ_naturality (hS.map_of_exact (ev i)) (hS.map_of_exact (ev j)) φ n

private noncomputable def deltaFunctorPointwise
    {A B I : Type*} [Category A] [Category B] [SmallCategory I]
    [Abelian A] [Abelian B] (D : DeltaFunctor A B) :
    DeltaFunctor (I ⥤ A) (I ⥤ B) := by
  let ev (i : I) := (evaluation I A).obj i
  let W (n : ℕ) := (Functor.whiskeringRight I A B).obj (D.functor n)
  refine
    { functor := W
      additive := fun n => inferInstance
      δ := fun {S} hS n => deltaPointwiseNatTrans D hS n
      map_g_δ := ?_
      δ_map_f := ?_
      mono_map_f := ?_
      exact_map := ?_
      exact_δ₁ := ?_
      exact_δ₂ := ?_
      δ_naturality := ?_ }
  · intro S hS n
    ext i
    exact D.map_g_δ (hS.map_of_exact (ev i)) n
  · intro S hS n
    ext i
    exact D.δ_map_f (hS.map_of_exact (ev i)) n
  · intro S hS
    exact (NatTrans.mono_iff_mono_app _).2 fun i => D.mono_map_f (hS.map_of_exact (ev i))
  · intro S hS n
    exact exact_of_pointwise (S.map (W n)) fun i => D.exact_map (hS.map_of_exact (ev i)) n
  · intro S hS n
    let S' : ShortComplex (I ⥤ B) :=
      ShortComplex.mk ((W n).map S.g) (deltaPointwiseNatTrans D hS n)
        (by ext i; exact D.map_g_δ (hS.map_of_exact (ev i)) n)
    change S'.Exact
    exact exact_of_pointwise S' fun i => D.exact_δ₁ (hS.map_of_exact (ev i)) n
  · intro S hS n
    let S' : ShortComplex (I ⥤ B) :=
      ShortComplex.mk (deltaPointwiseNatTrans D hS n) ((W (n + 1)).map S.f)
        (by ext i; exact D.δ_map_f (hS.map_of_exact (ev i)) n)
    change S'.Exact
    exact exact_of_pointwise S' fun i => D.exact_δ₂ (hS.map_of_exact (ev i)) n
  · intro S T hS hT φ n
    ext i
    exact D.δ_naturality (hS.map_of_exact (ev i)) (hT.map_of_exact (ev i))
      (ShortComplex.Hom.mk (φ.τ₁.app i) (φ.τ₂.app i) (φ.τ₃.app i)
        (NatTrans.congr_app φ.comm₁₂ i) (NatTrans.congr_app φ.comm₂₃ i)) n

private noncomputable def deltaFunctorMapExact
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C] (D : DeltaFunctor A B) (F : B ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    DeltaFunctor A C := by
  refine
    { functor := fun n => D.functor n ⋙ F
      additive := fun n => inferInstance
      δ := fun hS n => F.map (D.δ hS n)
      map_g_δ := ?_
      δ_map_f := ?_
      mono_map_f := ?_
      exact_map := ?_
      exact_δ₁ := ?_
      exact_δ₂ := ?_
      δ_naturality := ?_ }
  · intro S hS n
    change F.map ((D.functor n).map S.g) ≫ F.map (D.δ hS n) = 0
    rw [← F.map_comp, D.map_g_δ, F.map_zero]
  · intro S hS n
    change F.map (D.δ hS n) ≫ F.map ((D.functor (n + 1)).map S.f) = 0
    rw [← F.map_comp, D.δ_map_f, F.map_zero]
  · intro S hS
    let : Mono ((D.functor 0).map S.f) := D.mono_map_f hS
    exact Functor.map_mono F ((D.functor 0).map S.f)
  · intro S hS n
    exact (D.exact_map hS n).map F
  · intro S hS n
    exact (D.exact_δ₁ hS n).map F
  · intro S hS n
    exact (D.exact_δ₂ hS n).map F
  · intro S T hS hT φ n
    change F.map ((D.functor n).map φ.τ₃) ≫ F.map (D.δ hT n) =
      F.map (D.δ hS n) ≫ F.map ((D.functor (n + 1)).map φ.τ₁)
    rw [← F.map_comp, D.δ_naturality hS hT φ n]
    simp only [F.map_comp]

private noncomputable def deltaFunctorPrecomp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C] (D : DeltaFunctor B C) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    DeltaFunctor A C := by
  refine
    { functor := fun n => F ⋙ D.functor n
      additive := fun n => inferInstance
      δ := fun hS n => D.δ (hS.map_of_exact F) n
      map_g_δ := ?_
      δ_map_f := ?_
      mono_map_f := ?_
      exact_map := ?_
      exact_δ₁ := ?_
      exact_δ₂ := ?_
      δ_naturality := ?_ }
  · intro S hS n
    exact D.map_g_δ (hS.map_of_exact F) n
  · intro S hS n
    exact D.δ_map_f (hS.map_of_exact F) n
  · intro S hS
    exact D.mono_map_f (hS.map_of_exact F)
  · intro S hS n
    exact D.exact_map (hS.map_of_exact F) n
  · intro S hS n
    exact D.exact_δ₁ (hS.map_of_exact F) n
  · intro S hS n
    exact D.exact_δ₂ (hS.map_of_exact F) n
  · intro S T hS hT φ n
    exact D.δ_naturality (hS.map_of_exact F) (hT.map_of_exact F)
      (ShortComplex.Hom.mk (F.map φ.τ₁) (F.map φ.τ₂) (F.map φ.τ₃)
        (by
          change F.map φ.τ₁ ≫ F.map T.f = F.map S.f ≫ F.map φ.τ₂
          simpa only [F.map_comp] using congrArg F.map φ.comm₁₂)
        (by
          change F.map φ.τ₂ ≫ F.map T.g = F.map S.g ≫ F.map φ.τ₃
          simpa only [F.map_comp] using congrArg F.map φ.comm₂₃)) n

private noncomputable def deltaFunctorColimitPost
    {A I : Type*} [Category A] [Abelian A] [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I A] [HasColimitsOfShape I Ab.{u}]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]
    [PreservesFiniteColimits (colim : (I ⥤ A) ⥤ A)]
    [PreservesFiniteLimits (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u})]
    [PreservesFiniteColimits (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u})]
    (D : DeltaFunctor A Ab.{u}) :
    deltaFunctorMapExact (deltaFunctorPointwise D)
      (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u}) ⟶
    deltaFunctorPrecomp D (colim : (I ⥤ A) ⥤ A) where
  app n :=
    { app := fun F => colimit.post F (D.functor n)
      naturality := by
        intro F G φ
        exact (colimit.map_post (F := F) (α := φ) (D.functor n)).symm }
  comm := by
    intro S hS n
    apply colimit.hom_ext
    intro i
    let ev := (evaluation I A).obj i
    let φ : S.map ev ⟶ S.map colim :=
      { τ₁ := colimit.ι S.X₁ i
        τ₂ := colimit.ι S.X₂ i
        τ₃ := colimit.ι S.X₃ i
        comm₁₂ := colimit.ι_map S.f i
        comm₂₃ := colimit.ι_map S.g i }
    change colimit.ι (S.X₃ ⋙ D.functor n) i ≫
        colimit.post S.X₃ (D.functor n) ≫ D.δ (hS.map_of_exact colim) n =
      colimit.ι (S.X₃ ⋙ D.functor n) i ≫
        colim.map (deltaPointwiseNatTrans D hS n) ≫
          colimit.post S.X₁ (D.functor (n + 1))
    have hpost₃ : colimit.ι (S.X₃ ⋙ D.functor n) i ≫
        colimit.post S.X₃ (D.functor n) =
          (D.functor n).map (colimit.ι S.X₃ i) := by simp [colimit.post]
    have hpost₁ : colimit.ι (S.X₁ ⋙ D.functor (n + 1)) i ≫
        colimit.post S.X₁ (D.functor (n + 1)) =
          (D.functor (n + 1)).map (colimit.ι S.X₁ i) := by simp [colimit.post]
    have hδmap : colimit.ι (S.X₃ ⋙ D.functor n) i ≫
        colim.map (deltaPointwiseNatTrans D hS n) =
          (deltaPointwiseNatTrans D hS n).app i ≫
            colimit.ι (S.X₁ ⋙ D.functor (n + 1)) i := by simp
    calc
      _ = (D.functor n).map φ.τ₃ ≫ D.δ (hS.map_of_exact colim) n := by
        exact congrArg (fun f => f ≫ D.δ (hS.map_of_exact colim) n) hpost₃
      _ = D.δ (hS.map_of_exact ev) n ≫ (D.functor (n + 1)).map φ.τ₁ :=
        D.δ_naturality (hS.map_of_exact ev) (hS.map_of_exact colim) φ n
      _ = _ := by
        rw [← hpost₁]
        calc
          _ = ((deltaPointwiseNatTrans D hS n).app i ≫
              colimit.ι (S.X₁ ⋙ D.functor (n + 1)) i) ≫
                colimit.post S.X₁ (D.functor (n + 1)) := by
            simp [deltaPointwiseNatTrans, Category.assoc]
          _ = _ := congrArg (fun f => f ≫ colimit.post S.X₁ (D.functor (n + 1))) hδmap.symm

private noncomputable def sectionsExtDeltaFunctor
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    DeltaFunctor (Sheaf J Ab.{u}) Ab.{u} :=
  ModuleSheafCohomology.extDeltaFunctor (𝟭 (Sheaf J Ab.{u}))
    ((presheafToSheaf J Ab.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))

private noncomputable def sectionsRepresentingIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    ((sheafSections J Ab.{u}).obj (op U)) ≅
      preadditiveCoyoneda.obj (op ((presheafToSheaf J Ab.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free))) :=
  ModuleSheafCohomology.evaluationRepresentation J U

/-- The functor of sections over `U` on abelian sheaves preserves finite limits. -/
private lemma preservesFiniteLimits_sheafSections {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) :
    PreservesFiniteLimits ((sheafSections J Ab.{u}).obj (op U)) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf J Ab.{u} ⋙ (evaluation Cᵒᵖ Ab.{u}).obj (op U)))

private noncomputable def sectionsExtRightDerivedIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) (n : ℕ) :
    (sectionsExtDeltaFunctor J U).functor n ≅
      ((sheafSections J Ab.{u}).obj (op U)).rightDerived n := by
  let P := (presheafToSheaf J Ab.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  let e := sectionsRepresentingIso J U
  letI := preservesFiniteLimits_sheafSections J U
  cases n with
  | zero =>
      simpa [sectionsExtDeltaFunctor, ModuleSheafCohomology.extDeltaFunctor, P, e] using
        (Functor.leftUnitor _ ≪≫ ModuleSheafCohomology.extZeroIsoCoyoneda P ≪≫ e.symm ≪≫
          ((sheafSections J Ab.{u}).obj (op U)).rightDerivedZeroIsoSelf.symm)
  | succ n =>
      simpa [sectionsExtDeltaFunctor, ModuleSheafCohomology.extDeltaFunctor, P, e] using
        (Functor.leftUnitor _ ≪≫
          (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso P n).symm ≪≫
          (ModuleSheafCohomology.rightDerivedIso e (n + 1)).symm)

/-- Mathlib's sheaf cohomology `Sheaf.H'` is the `Ext`-group out of the sheafification of the
free abelian presheaf on `yoneda.obj U`, which is the degree-`n` component of
`sectionsExtDeltaFunctor`. The two are the same object; the identification is recorded here as
its own lemma because checking it inside a larger proof exhausts the heartbeat budget. -/
private lemma sheafH'_eq_sectionsExtDeltaFunctor {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]
    (F : Sheaf J Ab.{u}) (n : ℕ) (U : C) :
    Sheaf.H' F n U = ((sectionsExtDeltaFunctor J U).functor n).obj F := rfl

private lemma sectionsExt_isZero_of_injective_colimit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (B : Set C)
    (h : ∀ U, B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf J Ab.{u}) (hG : ∀ i, Injective (G.obj i))
    (U : C) (hU : B U) (p : ℕ) :
    IsZero (((sectionsExtDeltaFunctor J U).functor (p + 1)).obj (colimit G)) := by
  let B' := isoClosure B
  let Cov' : ∀ V : C,
      Set {E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V} :=
    fun _ => {E | HasIntersectionsIn B' E.1}
  have hProducts : ∀ {V : C}
      (E : {E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V}),
      E ∈ Cov' V → ∀ (n : ℕ) (a : Fin (n + 1) → E.1.I₀),
        HasProduct (fun i => Over.mk (E.1.f (a i))) :=
    fun _ hE n a => HasIntersectionsIn.hasProduct_over hE n a
  have hCovObjects : ∀ {V : C}
      (E : {E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V}) (hE : E ∈ Cov' V),
      V ∈ B' ∧ (∀ i, E.1.X i ∈ B') ∧
        ∀ (n : ℕ) (a : Fin (n + 1) → E.1.I₀),
          let : ∀ (q : ℕ) (b : Fin (q + 1) → E.1.I₀),
            HasProduct (fun i => Over.mk (E.1.f (b i))) := hProducts E hE
          (∏ᶜ (fun i => Over.mk (E.1.f (a i)))).left ∈ B' := by
    intro V E hE
    refine ⟨hE.2.1, hE.2.2.1, ?_⟩
    intro n a
    let : ∀ (q : ℕ) (b : Fin (q + 1) → E.1.I₀),
        HasProduct (fun i => Over.mk (E.1.f (b i))) := hProducts E hE
    obtain ⟨W, hW, ⟨e⟩⟩ := HasIntersectionsIn.exists_mem_iso_prod_over hE n a
    obtain ⟨Z, hZ, ⟨e'⟩⟩ := hW
    exact ⟨Z, hZ, ⟨e.trans e'⟩⟩
  have hCovCofinal : ∀ V ∈ B', ∀ S ∈ J V,
      ∃ (E : {E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V}),
        E ∈ Cov' V ∧ E.1.sieve₀ ≤ S := by
    intro V hV S hS
    let : Category.{u} C := inferInstance
    obtain ⟨E, hE, hEc, hES⟩ := exists_small_cover_isoClosure J B h hV S hS
    exact ⟨⟨E, hEc⟩, hE, hES⟩
  have hCech : ∀ {V : C}
      (E : {E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V}) (hE : E ∈ Cov' V)
      (n : ℕ), 0 < n →
        let : ∀ (q : ℕ) (a : Fin (q + 1) → E.1.I₀),
          HasProduct (fun i => Over.mk (E.1.f (a i))) := hProducts E hE
        IsZero (Stacks.CechSite.cechCohomology E.1 (colimit G).obj n) := by
    intro V E hE n hn
    cases n with
    | zero => omega
    | succ n =>
      let : ∀ (q : ℕ) (a : Fin (q + 1) → E.1.I₀),
          HasProduct (fun i => Over.mk (E.1.f (a i))) := hProducts E hE
      exact isZero_cechCohomology_colimit_of_injective J B h G E.1 hE E.2
        (fun i => hG i) n
  have hvan := Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero
    J B' Cov' hProducts hCovObjects hCovCofinal (colimit G) hCech U
    (mem_isoClosure_of_mem hU) (p + 1) (Nat.zero_lt_succ p)
  exact hvan.of_iso
    (eqToIso (sheafH'_eq_sectionsExtDeltaFunctor J (colimit G) (p + 1) U).symm)


end derived_category

attribute [-instance] CompleteLattice.toCompletePartialOrder in
/-- **Stacks 0739.** On a site, suppose a collection of finite covering families is cofinal
among the coverings of each object in `B`, and all nonempty iterated fibre products occurring
in those families remain in `B`. Then the canonical map from the filtered colimit of the
cohomology groups to the cohomology of the filtered colimit is an isomorphism. -/
@[stacks 0739]
public theorem isIso_colimit_post_rightDerived_sheafSections
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (PreZeroHypercover.{w} U))
    (hCov : ∀ (U : C) (E : PreZeroHypercover.{w} U), Cov U E → E.sieve₀ ∈ J U)
    (hfinite : ∀ (U : C) (E : PreZeroHypercover.{w} U), Cov U E →
      HasIntersectionsIn B E)
    (hcofinal : ∀ (U : C), B U → ∀ S ∈ J U, ∃ E : PreZeroHypercover.{w} U,
      Cov U E ∧ E.sieve₀ ≤ S)
    (p : ℕ) (U : C) (hU : B U)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : CategoryTheory.Functor I (Sheaf J (Ab.{u}))) :
    IsIso (colimit.post F
      (((sheafSections J (Ab.{u})).obj (op U)).rightDerived p)) := by
  let := HasDerivedCategory.standard (Sheaf J (Ab.{u}))
  have h : ∀ V, B V → ∀ S ∈ J V, ∃ E : PreZeroHypercover.{w} V,
      HasIntersectionsIn B E ∧ E.sieve₀ ∈ J V ∧ E.sieve₀ ≤ S := by
    intro V hV S hS
    obtain ⟨E, hE, hES⟩ := hcofinal V hV S hS
    exact ⟨E, hfinite V E hE, hCov V E hE, hES⟩
  have := preservesFiniteLimits_sheafSections J U
  cases p with
  | zero =>
    have := preservesColimit_sections J B h F U hU
    have := preservesColimit_of_natIso F
      ((sheafSections J Ab.{u}).obj (op U)).rightDerivedZeroIsoSelf.symm
    infer_instance
  | succ p =>
    let D : DeltaFunctor (Sheaf J (Ab.{u})) Ab.{u} := sectionsExtDeltaFunctor J U
    let η := deltaFunctorColimitPost (I := I) (A := Sheaf J (Ab.{u})) D
    let Dsource := deltaFunctorMapExact (deltaFunctorPointwise D)
      (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u})
    let Etarget := deltaFunctorPrecomp D
      (colim : (I ⥤ Sheaf J (Ab.{u})) ⥤ Sheaf J (Ab.{u}))
    have : IsIso (η.app 0) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro X
      let e := sectionsExtRightDerivedIso J U 0 ≪≫
        ((sheafSections J Ab.{u}).obj (op U)).rightDerivedZeroIsoSelf
      have : PreservesColimit X ((sheafSections J Ab.{u}).obj (op U)) :=
        preservesColimit_sections J B h X U hU
      let : PreservesColimit X (D.functor 0) :=
        preservesColimit_of_natIso X e.symm
      show IsIso (colimit.post X (D.functor 0))
      infer_instance
    have heff : ∀ (X : I ⥤ Sheaf J (Ab.{u})) (n : ℕ),
        ∃ (Y : I ⥤ Sheaf J (Ab.{u})) (f : X ⟶ Y),
          Mono f ∧
            (Dsource.functor (n + 1)).map f = 0 ∧
            (Etarget.functor (n + 1)).map f = 0 := by
      intro X n
      obtain ⟨Y, f, hf, hY⟩ := exists_mono_into_injective_diagram X
      have hsource : ((deltaFunctorPointwise D).functor (n + 1)).map f = 0 := by
        apply NatTrans.ext
        funext i
        let : Injective (Y.obj i) := hY i
        have hrd := Functor.isZero_rightDerived_obj_injective_succ
          ((sheafSections J Ab.{u}).obj (op U)) n (Y.obj i)
        exact ((Iso.isZero_iff
          ((sectionsExtRightDerivedIso J U (n + 1)).app (Y.obj i))).2 hrd).eq_zero_of_tgt _
      refine ⟨Y, f, hf, ?_, ?_⟩
      · show colim.map (((deltaFunctorPointwise D).functor (n + 1)).map f) = 0
        rw [hsource]
        exact Functor.map_zero (colim : (I ⥤ Ab.{u}) ⥤ Ab.{u}) _ _
      · show (D.functor (n + 1)).map (colim.map f) = 0
        exact (sectionsExt_isZero_of_injective_colimit J B h Y hY U hU n).eq_zero_of_tgt _
    have hη : IsIso ((η.app (p + 1)).app F) :=
      isIso_deltaFunctor_app_of_common_effacements η heff (p + 1) F
    let e := sectionsExtRightDerivedIso J U (p + 1)
    have hcomm :
        (η.app (p + 1)).app F ≫ (e.app (colimit F)).hom =
          colim.map (Functor.whiskerLeft F e.hom) ≫
            colimit.post F (((sheafSections J Ab.{u}).obj (op U)).rightDerived (p + 1)) := by
      apply colimit.hom_ext
      intro i
      show colimit.ι (F ⋙ D.functor (p + 1)) i ≫
          colimit.post F (D.functor (p + 1)) ≫ (e.app (colimit F)).hom =
        colimit.ι (F ⋙ D.functor (p + 1)) i ≫
          colim.map (Functor.whiskerLeft F e.hom) ≫
            colimit.post F (((sheafSections J Ab.{u}).obj (op U)).rightDerived (p + 1))
      calc
        _ = (D.functor (p + 1)).map (colimit.ι F i) ≫ (e.app (colimit F)).hom := by
          simp
        _ = (e.app (F.obj i)).hom ≫
            (((sheafSections J Ab.{u}).obj (op U)).rightDerived (p + 1)).map
              (colimit.ι F i) := e.hom.naturality (colimit.ι F i)
        _ = _ := by simp [Functor.whiskerLeft]
    have : IsIso (colim.map (Functor.whiskerLeft F e.hom) ≫
        colimit.post F (((sheafSections J Ab.{u}).obj (op U)).rightDerived (p + 1))) := by
      rw [← hcomm]
      exact (asIso ((η.app (p + 1)).app F) ≪≫ e.app (colimit F)).isIso_hom
    exact IsIso.of_isIso_comp_left (colim.map (Functor.whiskerLeft F e.hom)) _

/-- `Stacks.Cohomology.HasIntersectionsIn.hasProduct_over`, in this file's original spelling. -/
private alias hasProduct_over_of_hasIntersectionsIn := HasIntersectionsIn.hasProduct_over

/-- `Stacks.Cohomology.HasIntersectionsIn.exists_mem_iso_prod_over`, in this file's original
spelling. -/
private alias product_over_iso_mem_of_hasIntersectionsIn := HasIntersectionsIn.exists_mem_iso_prod_over

end Stacks.Cohomology
