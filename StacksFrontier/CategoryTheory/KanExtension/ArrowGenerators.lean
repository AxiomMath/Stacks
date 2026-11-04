module

public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import StacksFrontier.CategoryTheory.KanExtension.DenseCompactSubcategory

/-!
# Arrows between compact generators

Let `C` be a preadditive category and `P` a property of objects of `C` closed under binary
coproducts, cokernels and initial objects, consisting of categorically compact objects, such
that every object of `C` is a filtered colimit of `P`-objects. Then the arrows of `C` between
`P`-objects play the same role in the arrow category `Arrow C`: every arrow is a filtered
colimit of arrows between `P`-objects. This is what the right exactness paragraph of the proof
of Stacks 0GRJ uses ("write `𝓕'` as the union of its coherent submodules ... we have short
exact sequences `0 → 𝓕ᵢ → 𝓕'ᵢ → 𝓕''ᵢ → 0`"): a map of quasi-coherent modules is a filtered
colimit of maps of coherent modules.

## Main definitions

* `CategoryTheory.ObjectProperty.arrow`: the arrows whose source and target satisfy `P`.

## Main results

* `CategoryTheory.ObjectProperty.ArrowGenerators.isFiltered_J`,
  `CategoryTheory.ObjectProperty.ArrowGenerators.arrow_ι_isDense`,
  `CategoryTheory.ObjectProperty.ArrowGenerators.finallySmall_J`: the comma categories of
  `P`-arrows over an arrow are filtered and finally small, and their canonical cocones are
  colimits.
* `CategoryTheory.ObjectProperty.arrow_le_isFinitelyPresentable` and
  `CategoryTheory.ObjectProperty.arrow_ind`: the `P`-arrows are categorically compact, and
  every arrow is a filtered colimit of `P`-arrows.
-/

@[expose] public section

open CategoryTheory Category Limits Cardinal

universe w v u

namespace CategoryTheory.ObjectProperty

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- The arrows of `C` whose source and target both satisfy `P`. -/
abbrev arrow : ObjectProperty (Arrow C) := ObjectProperty.comma (𝟭 C) (𝟭 C) P P

namespace ArrowGenerators

variable (φ : Arrow C)

/-- The category of `P`-arrows over a fixed arrow `φ`. -/
abbrev J := CostructuredArrow P.arrow.ι φ

/-- The category of `P`-objects over the source of `φ`. -/
abbrev J₁ := CostructuredArrow P.ι φ.left

/-- The category of `P`-objects over the target of `φ`. -/
abbrev J₂ := CostructuredArrow P.ι φ.right

variable {P φ}

/-- Constructor for objects of `J P φ`. -/
abbrev J.mk (a : Arrow C) (ha₁ : P a.left) (ha₂ : P a.right) (u : a ⟶ φ) : J P φ :=
  CostructuredArrow.mk (Y := (⟨a, ha₁, ha₂⟩ : P.arrow.FullSubcategory)) u

/-- Constructor for morphisms of `J P φ`. -/
abbrev J.homMk {j j' : J P φ} (m : j.left.obj ⟶ j'.left.obj) (h : m ≫ j'.hom = j.hom) :
    j ⟶ j' :=
  CostructuredArrow.homMk (ObjectProperty.homMk m) h

/-- The source part of an object of `J P φ`. -/
abbrev J.fst (j : J P φ) : J₁ P φ :=
  CostructuredArrow.mk (Y := (⟨_, j.left.property.1⟩ : P.FullSubcategory)) (by exact j.hom.left)

/-- The target part of an object of `J P φ`. -/
abbrev J.snd (j : J P φ) : J₂ P φ :=
  CostructuredArrow.mk (Y := (⟨_, j.left.property.2⟩ : P.FullSubcategory)) (by exact j.hom.right)

variable (P φ) in
/-- The first projection `J P φ ⥤ J₁ P φ`. -/
@[implicit_reducible, simps]
def π₁ : J P φ ⥤ J₁ P φ where
  obj j := j.fst
  map m := CostructuredArrow.homMk (ObjectProperty.homMk (by exact m.left.hom.left))
    (by exact congr_arg CommaMorphism.left (CostructuredArrow.w m))

variable (P φ) in
/-- The second projection `J P φ ⥤ J₂ P φ`. -/
@[implicit_reducible, simps]
def π₂ : J P φ ⥤ J₂ P φ where
  obj j := j.snd
  map m := CostructuredArrow.homMk (ObjectProperty.homMk (by exact m.left.hom.right))
    (by exact congr_arg CommaMorphism.right (CostructuredArrow.w m))

/-- Two morphisms with the same composite with `h` have difference killed by `h`. -/
private theorem sub_comp_eq_zero_of_comp_eq [Preadditive C] {X Y Z : C} {f g : X ⟶ Y}
    {h : Y ⟶ Z} (H : f ≫ h = g ≫ h) : (f - g) ≫ h = 0 := by
  rw [Preadditive.sub_comp, sub_eq_zero, H]

/-- The cokernel projection of `f - g` identifies `f` and `g`. -/
private theorem comp_cokernel_π_sub_eq [Preadditive C] [HasCokernels C] {X Y : C} (f g : X ⟶ Y) :
    f ≫ cokernel.π (f - g) = g ≫ cokernel.π (f - g) := by
  rw [← sub_eq_zero, ← Preadditive.sub_comp, cokernel.condition]

section Filtered

variable [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]

omit [Preadditive C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})] in
/-- The binary coproduct of two `P`-objects satisfies `P`. -/
theorem prop_coprod {X Y : C} (hX : P X) (hY : P Y) : P (X ⨿ Y) :=
  P.prop_of_isColimit (colimit.isColimit (Limits.pair X Y))
    (fun (j : Discrete WalkingPair) ↦ by rcases j with ⟨⟨⟩⟩; exacts [hX, hY])

omit [HasBinaryCoproducts C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})] in
/-- The cokernel of a morphism between `P`-objects satisfies `P`. -/
theorem prop_cokernel {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P (cokernel f) :=
  P.prop_of_isColimit (colimit.isColimit (parallelPair f 0))
    (fun (j : WalkingParallelPair) ↦ by rcases j with (_ | _); exacts [hX, hY])

omit [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair] in
/-- The initial object of `C` satisfies `P`. -/
theorem prop_initial : P (⊥_ C) :=
  P.prop_of_isColimit (colimit.isColimit (Functor.empty C)) (fun j ↦ PEmpty.elim j.as)

variable (P φ) in
/-- The category `J P φ` of `P`-arrows over `φ` is filtered. -/
theorem isFiltered_J : IsFiltered (J P φ) where
  nonempty := ⟨J.mk (Arrow.mk (𝟙 (⊥_ C))) (prop_initial (P := P)) (prop_initial (P := P))
    (Arrow.homMk (initial.to _) (initial.to _) (initial.hom_ext _ _))⟩
  cocone_objs j₁ j₂ := by
    let a : Arrow C := Arrow.mk (coprod.map j₁.left.obj.hom j₂.left.obj.hom)
    let u : a ⟶ φ := Arrow.homMk (coprod.desc j₁.hom.left j₂.hom.left)
      (coprod.desc j₁.hom.right j₂.hom.right) (by
        apply coprod.hom_ext
        · simp [a]
        · simp [a])
    refine ⟨J.mk a (prop_coprod j₁.left.property.1 j₂.left.property.1)
      (prop_coprod j₁.left.property.2 j₂.left.property.2) u,
      J.homMk (Arrow.homMk coprod.inl coprod.inl (by simp [a])) ?_,
      J.homMk (Arrow.homMk coprod.inr coprod.inr (by simp [a])) ?_, trivial⟩
    · ext <;> exact coprod.inl_desc _ _
    · ext <;> exact coprod.inr_desc _ _
  cocone_maps {j j'} m m' := by
    let a' := j'.left.obj
    have hl : (m.left.hom.left - m'.left.hom.left) ≫ j'.hom.left = 0 :=
      sub_comp_eq_zero_of_comp_eq ((congr_arg CommaMorphism.left (CostructuredArrow.w m)).trans
        (congr_arg CommaMorphism.left (CostructuredArrow.w m')).symm)
    have hr : (m.left.hom.right - m'.left.hom.right) ≫ j'.hom.right = 0 :=
      sub_comp_eq_zero_of_comp_eq ((congr_arg CommaMorphism.right (CostructuredArrow.w m)).trans
        (congr_arg CommaMorphism.right (CostructuredArrow.w m')).symm)
    have hw : (m.left.hom.left - m'.left.hom.left) ≫ a'.hom ≫
        cokernel.π (m.left.hom.right - m'.left.hom.right) = 0 := by
      rw [← assoc, Preadditive.sub_comp, Arrow.w m.left.hom, Arrow.w m'.left.hom,
        ← Preadditive.comp_sub, assoc, cokernel.condition, comp_zero]
    let a'' : Arrow C := Arrow.mk (cokernel.desc _ (a'.hom ≫ cokernel.π _) hw)
    let u : a'' ⟶ φ := Arrow.homMk (cokernel.desc _ j'.hom.left hl)
      (cokernel.desc _ j'.hom.right hr) (by
        apply coequalizer.hom_ext
        simp [a'', a'])
    refine ⟨J.mk a'' (prop_cokernel _ j.left.property.1 j'.left.property.1)
      (prop_cokernel _ j.left.property.2 j'.left.property.2) u,
      J.homMk (Arrow.homMk (cokernel.π _) (cokernel.π _) (by simp [a'', a'])) ?_, ?_⟩
    · ext <;> simp [u]
    · ext
      · exact comp_cokernel_π_sub_eq _ _
      · exact comp_cokernel_π_sub_eq _ _

end Filtered

section Final

variable [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

include hP hgen

variable (P φ) in
/-- The first projection `π₁ P φ : J P φ ⥤ J₁ P φ` is final. -/
theorem final_π₁ : (π₁ P φ).Final := by
  have := isFiltered_J P φ
  have := isFiltered_costructuredArrow_ι P hP hgen φ.left
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun d ↦ ?_, fun {d c} s s' ↦ ?_⟩
  · obtain ⟨I, _, _, pres, hpres⟩ := hgen φ.right
    have : IsFinitelyPresentable.{w} (P.ι.obj d.left) := hP _ d.left.property
    obtain ⟨i, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit
      (d.hom ≫ φ.hom)
    exact ⟨J.mk (Arrow.mk g) d.left.property (hpres i)
      (Arrow.homMk d.hom (pres.ι.app i) hg.symm),
      ⟨CostructuredArrow.homMk (𝟙 d.left) (by rw [Functor.map_id, id_comp]; rfl)⟩⟩
  · let a := c.left.obj
    let δ : d.left.obj ⟶ a.left := s.left.hom - s'.left.hom
    have hw : c.hom.left ≫ φ.hom = a.hom ≫ c.hom.right := Arrow.w c.hom
    have hδ : δ ≫ c.hom.left = 0 :=
      sub_comp_eq_zero_of_comp_eq ((CostructuredArrow.w s).trans (CostructuredArrow.w s').symm)
    have hδ' : (δ ≫ a.hom) ≫ c.hom.right = 0 := by
      rw [assoc, ← hw, ← assoc, hδ, zero_comp]
    let a'' : Arrow C := Arrow.mk (cokernel.desc δ (a.hom ≫ cokernel.π (δ ≫ a.hom))
      (by rw [← assoc, cokernel.condition]))
    let u : a'' ⟶ φ := Arrow.homMk (cokernel.desc δ c.hom.left hδ)
      (cokernel.desc (δ ≫ a.hom) c.hom.right hδ') (by
        apply coequalizer.hom_ext
        simp [a'', a])
    refine ⟨J.mk a'' (prop_cokernel δ d.left.property c.left.property.1)
      (prop_cokernel _ d.left.property c.left.property.2) u,
      J.homMk (Arrow.homMk (cokernel.π δ) (cokernel.π (δ ≫ a.hom)) (by simp [a'', a]))
        (by ext <;> simp [u]), ?_⟩
    ext
    exact comp_cokernel_π_sub_eq _ _

variable (P φ) in
/-- The second projection `π₂ P φ : J P φ ⥤ J₂ P φ` is final. -/
theorem final_π₂ : (π₂ P φ).Final := by
  have := isFiltered_J P φ
  have := isFiltered_costructuredArrow_ι P hP hgen φ.right
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun d ↦ ?_, fun {d c} s s' ↦ ?_⟩
  · exact ⟨J.mk (Arrow.mk (initial.to d.left.obj)) (prop_initial (P := P)) d.left.property
      (Arrow.homMk (initial.to φ.left) d.hom (initial.hom_ext _ _)),
      ⟨CostructuredArrow.homMk (𝟙 d.left) (by rw [Functor.map_id, id_comp]; rfl)⟩⟩
  · let a := c.left.obj
    let δ : d.left.obj ⟶ a.right := s.left.hom - s'.left.hom
    have hw : c.hom.left ≫ φ.hom = a.hom ≫ c.hom.right := Arrow.w c.hom
    have hδ : δ ≫ c.hom.right = 0 :=
      sub_comp_eq_zero_of_comp_eq ((CostructuredArrow.w s).trans (CostructuredArrow.w s').symm)
    let a'' : Arrow C := Arrow.mk (a.hom ≫ cokernel.π δ)
    let u : a'' ⟶ φ := Arrow.homMk c.hom.left (cokernel.desc δ c.hom.right hδ) (by
      simp [a'', a])
    refine ⟨J.mk a'' c.left.property.1 (prop_cokernel δ d.left.property c.left.property.2) u,
      J.homMk (Arrow.homMk (𝟙 _) (cokernel.π δ) (by simp [a'', a])) (by ext <;> simp [u]), ?_⟩
    ext
    exact comp_cokernel_π_sub_eq _ _

/-- **The arrows between `P`-objects are dense in `Arrow C`**: every arrow is the colimit of the
canonical diagram of arrows between `P`-objects over it. -/
theorem arrow_ι_isDense : P.arrow.ι.IsDense := by
  have := isDense_ι P hP hgen
  refine ⟨fun φ ↦ ?_⟩
  have := final_π₁ P φ hP hgen
  have := final_π₂ P φ hP hgen
  exact ⟨Comma.fstSndJointlyReflectColimit
    ((Functor.Final.isColimitWhiskerEquiv (π₁ P φ) _).2 (P.ι.denseAt φ.left))
    ((Functor.Final.isColimitWhiskerEquiv (π₂ P φ) _).2 (P.ι.denseAt φ.right))⟩

end Final

section Small

variable [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

omit [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})] in
/-- The morphisms between two `P`-objects form a `w`-small type. -/
theorem small_hom_of_mem {X Y : C} (hX : P X) (hY : P Y) : Small.{w} (X ⟶ Y) :=
  small_of_injective (f := fun g : X ⟶ Y ↦
    (ObjectProperty.homMk g : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩))
    (fun _ _ h ↦ congr_arg InducedCategory.Hom.hom h)

omit [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})] in
variable (P) in
/-- The full subcategory of `P`-arrows in `Arrow C` is `w`-locally small. -/
theorem locallySmall_arrow : LocallySmall.{w} P.arrow.FullSubcategory where
  hom_small f g := by
    have : Small.{w} (f.obj.left ⟶ g.obj.left) :=
      small_hom_of_mem (P := P) f.property.1 g.property.1
    have : Small.{w} (f.obj.right ⟶ g.obj.right) :=
      small_hom_of_mem (P := P) f.property.2 g.property.2
    exact small_of_injective (f := fun m : f ⟶ g ↦ (m.hom.left, m.hom.right))
      (fun m m' h ↦ by
        ext
        · exact congr_arg _root_.Prod.fst h
        · exact congr_arg _root_.Prod.snd h)

include hP hgen

variable (P φ) in
/-- The category `J P φ` of `P`-arrows over an arrow `φ` is `w`-finally small. -/
theorem finallySmall_J : FinallySmall.{w} (J P φ) := by
  have := isFiltered_J P φ
  have := locallySmall_arrow.{w} P
  have : LocallySmall.{w} (J P φ) := locallySmall_of_faithful.{w} (CostructuredArrow.proj _ _)
  obtain ⟨I, _, _, pX, hpX⟩ := hgen φ.left
  obtain ⟨I', _, _, pY, hpY⟩ := hgen φ.right
  have hnY : ∀ {j j' : I'} (f : j ⟶ j'), pY.diag.map f ≫ pY.ι.app j' = pY.ι.app j :=
    fun f ↦ by simp
  let T := Σ (i : I) (i' : I'),
    {b : pX.diag.obj i ⟶ pY.diag.obj i' // b ≫ pY.ι.app i' = pX.ι.app i ≫ φ.hom}
  have : ∀ (i : I) (i' : I'), Small.{w}
      {b : pX.diag.obj i ⟶ pY.diag.obj i' // b ≫ pY.ι.app i' = pX.ι.app i ≫ φ.hom} :=
    fun i i' ↦ have := small_hom_of_mem (P := P) (hpX i) (hpY i'); inferInstance
  let f : T → J P φ := fun t ↦ J.mk (Arrow.mk t.2.2.1) (hpX t.1) (hpY t.2.1)
    (Arrow.homMk (pX.ι.app t.1) (pY.ι.app t.2.1) t.2.2.2.symm)
  let s : Set (J P φ) := Set.range f
  have hs : ∀ c : J P φ, ∃ c' ∈ s, Nonempty (c ⟶ c') := by
    intro c
    have hA : IsFinitelyPresentable.{w} (P.arrow.ι.obj c.left).left := hP _ c.left.property.1
    have hB : IsFinitelyPresentable.{w} (P.arrow.ι.obj c.left).right := hP _ c.left.property.2
    have hw : c.hom.left ≫ φ.hom = (P.arrow.ι.obj c.left).hom ≫ c.hom.right := Arrow.w c.hom
    obtain ⟨i, g₁, hg₁⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pX.isColimit c.hom.left
    have hXi : IsFinitelyPresentable.{w} (pX.diag.obj i) := hP _ (hpX i)
    obtain ⟨i₁, b, hb : b ≫ pY.ι.app i₁ = pX.ι.app i ≫ φ.hom⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit pY.isColimit (pX.ι.app i ≫ φ.hom)
    obtain ⟨i₂, g₂, hg₂ : g₂ ≫ pY.ι.app i₂ = c.hom.right⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit pY.isColimit c.hom.right
    change g₁ ≫ pX.ι.app i = c.hom.left at hg₁
    have : IsCardinalFiltered I' ℵ₀ := (isCardinalFiltered_aleph0_iff I').2 inferInstance
    obtain ⟨k, α, hα⟩ := IsCardinalPresentable.exists_eq_of_isColimit' ℵ₀ pY.isColimit
      ((P.arrow.ι.obj c.left).hom ≫ g₂ ≫ pY.diag.map (IsFiltered.rightToMax i₁ i₂))
      (g₁ ≫ b ≫ pY.diag.map (IsFiltered.leftToMax i₁ i₂)) (by
        show (_ ≫ _ ≫ _) ≫ pY.ι.app (IsFiltered.max i₁ i₂) =
          (_ ≫ _ ≫ _) ≫ pY.ι.app (IsFiltered.max i₁ i₂)
        rw [assoc, assoc, assoc, assoc, hnY, hnY, hg₂, hb, ← hw, ← assoc, hg₁])
    refine ⟨f ⟨i, k, ⟨(b ≫ pY.diag.map (IsFiltered.leftToMax i₁ i₂)) ≫ pY.diag.map α, ?_⟩⟩,
      Set.mem_range_self _, ⟨J.homMk (Arrow.homMk g₁
        ((g₂ ≫ pY.diag.map (IsFiltered.rightToMax i₁ i₂)) ≫ pY.diag.map α) ?_) ?_⟩⟩
    · rw [assoc, assoc, hnY, hnY, hb]
    · show g₁ ≫ ((b ≫ pY.diag.map _) ≫ pY.diag.map α) =
        (P.arrow.ι.obj c.left).hom ≫ ((g₂ ≫ pY.diag.map _) ≫ pY.diag.map α)
      simpa only [assoc] using hα.symm
    · ext
      · exact hg₁
      · show ((g₂ ≫ pY.diag.map _) ≫ pY.diag.map α) ≫ pY.ι.app k = c.hom.right
        rw [assoc, assoc, hnY, hnY, hg₂]
  have : Small.{w} s := small_range f
  have : (ObjectProperty.ι (· ∈ s)).Final :=
    Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ fun c ↦
      let ⟨c', hc', hc''⟩ := hs c; ⟨⟨c', hc'⟩, hc''⟩
  exact finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· ∈ s))

end Small

end ArrowGenerators

open ArrowGenerators in
/-- **Every arrow is a filtered colimit of arrows between `P`-objects.** -/
theorem arrow_ind [Preadditive C] [HasBinaryCoproducts C] [HasCokernels C] [HasInitial C]
    [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
    [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
    [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]
    [LocallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X) (φ : Arrow C) :
    P.arrow.ind.{w} φ := by
  have := isFiltered_J P φ
  have := finallySmall_J P φ hP hgen
  have := locallySmall_arrow.{w} P
  have : LocallySmall.{w} (J P φ) := locallySmall_of_faithful.{w} (CostructuredArrow.proj _ _)
  have := arrow_ι_isDense hP hgen
  let G := FinallySmall.fromFilteredFinalModel.{w} (J P φ)
  exact ⟨FinallySmall.FilteredFinalModel.{w} (J P φ), inferInstance, inferInstance,
    ⟨G ⋙ CostructuredArrow.proj _ _ ⋙ P.arrow.ι, _,
      (Functor.Final.isColimitWhiskerEquiv G _).symm (P.arrow.ι.denseAt φ)⟩,
    fun k ↦ (G.obj k).left.property⟩

/-- **Arrows between categorically compact objects are categorically compact** in `Arrow C`. -/
theorem arrow_le_isFinitelyPresentable [HasFilteredColimitsOfSize.{w, w} C]
    (hP : P ≤ isFinitelyPresentable.{w} C) :
    P.arrow ≤ isFinitelyPresentable.{w} (Arrow C) := by
  intro f hf
  have : HasCardinalFilteredColimits.{w} C ℵ₀ :=
    HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize.2 inferInstance
  have : IsCardinalPresentable.{w} f.left ℵ₀ := hP _ hf.1
  have : IsCardinalPresentable.{w} f.right ℵ₀ := hP _ hf.2
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) f.hom

end CategoryTheory.ObjectProperty
