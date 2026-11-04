module

public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonStructureIso
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonFullyFaithful

/-!
# The comparison at a square, read through spans and cocones

For a category fibred in groupoids `q` and a commutative square `f ≫ i = g ≫ j` of the base,
`Deformation.Artin.fiberSquareComparison` compares the fibre over the terminal corner with the
two-fibre product of the fibres over the two middle corners. This file translates its two halves
into the choice-free language of `CategoryTheory.Functor.SquareSpan`:

* the comparison is essentially surjective as soon as every span over `(f, g)` has a cocone for
  `(i, j)`;
* cocones are unique up to unique isomorphism as soon as the comparison is fully faithful.

## Main definitions

* `Deformation.Artin.fiberIsoOfIsHomLift`: a morphism between objects of one fibre lying over the
  identity, as an isomorphism of the fibre.

## Main results

* `Deformation.Artin.essSurj_fiberSquareComparison_of_nonempty_cocone`: the comparison is
  essentially surjective if every span over `(f, g)` has a cocone for `(i, j)`.
* `Deformation.Artin.hasUniqueSquareCocones_of_fullyFaithful`: cocones are unique up to unique
  isomorphism if the comparison is fully faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Deformation.Artin

universe v₁ v₂ u₁ u₂

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
variable {q : X ⥤ C} (hq : q.IsFiberedInGroupoids) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (h : f ≫ i = g ≫ j)

/-- In a category fibred in groupoids, a morphism between objects of one fibre lying over the
identity is an isomorphism of the fibre. -/
noncomputable def fiberIsoOfIsHomLift {S : C} {a b : q.Fiber S} (φ : a.1 ⟶ b.1)
    [q.IsHomLift (𝟙 S) φ] : a ≅ b :=
  haveI := hq.isIso_of_isHomLift_isIso (𝟙 S) φ
  { hom := ⟨φ, inferInstance⟩
    inv := ⟨CategoryTheory.inv φ, inferInstance⟩
    hom_inv_id := Fiber.hom_ext (IsIso.hom_inv_id φ)
    inv_hom_id := Fiber.hom_ext (IsIso.inv_hom_id φ) }

/-- The underlying morphism of `(fiberIsoOfIsHomLift hq φ).hom` is `φ`. -/
@[simp]
lemma fiberInclusion_map_fiberIsoOfIsHomLift_hom {S : C} {a b : q.Fiber S} (φ : a.1 ⟶ b.1)
    [q.IsHomLift (𝟙 S) φ] : Fiber.fiberInclusion.map (fiberIsoOfIsHomLift hq φ).hom = φ := rfl

/-- The underlying morphism of `(fiberIsoOfIsHomLift hq φ).inv` is the inverse of `φ`. -/
@[simp]
lemma fiberInclusion_map_fiberIsoOfIsHomLift_inv {S : C} {a b : q.Fiber S} (φ : a.1 ⟶ b.1)
    [q.IsHomLift (𝟙 S) φ] :
    Fiber.fiberInclusion.map (fiberIsoOfIsHomLift hq φ).inv =
      (haveI := hq.isIso_of_isHomLift_isIso (𝟙 S) φ; CategoryTheory.inv φ) := rfl

include hq in
/-- **Essential surjectivity of the comparison from cocones.** If every span over `(f, g)` has a
cocone for `(i, j)`, the comparison at the square is essentially surjective. -/
public theorem essSurj_fiberSquareComparison_of_nonempty_cocone
    (hcoc : ∀ s : SquareSpan q f g, Nonempty (s.Cocone i j)) :
    (fiberSquareComparison q c f g i j h).EssSurj where
  mem_essImage T := by
    have hα : q.IsHomLift f (c.map f T.fst) := inferInstance
    have hβ : q.IsHomLift g (Fiber.fiberInclusion.map T.iso.hom ≫ c.map g T.snd) :=
      inferInstance
    obtain ⟨K⟩ := hcoc ⟨_, _, _, _, _, hα, hβ⟩
    let zF : q.Fiber Z := Fiber.mk (IsHomLift.codomain_eq q i K.ξ)
    let ξ : T.fst.1 ⟶ zF.1 := K.ξ
    let η : T.snd.1 ⟶ zF.1 := K.η
    have : q.IsHomLift i ξ := K.isHomLift_ξ
    have : q.IsHomLift j η := K.isHomLift_η
    let φx : T.fst.1 ⟶ (c.obj i zF).1 :=
      hq.fill (f := i) (g := 𝟙 V) (f' := i) (by simp) (c.map i zF) ξ
    let φy : T.snd.1 ⟶ (c.obj j zF).1 :=
      hq.fill (f := j) (g := 𝟙 W) (f' := j) (by simp) (c.map j zF) η
    have : q.IsHomLift (𝟙 V) φx := hq.fill_isHomLift _ _ _
    have : q.IsHomLift (𝟙 W) φy := hq.fill_isHomLift _ _ _
    have eφx : φx ≫ c.map i zF = ξ := hq.fill_fac _ _ _
    have eφy : φy ≫ c.map j zF = η := hq.fill_fac _ _ _
    let ex : T.fst ≅ c.obj i zF := fiberIsoOfIsHomLift hq φx
    let ey : T.snd ≅ c.obj j zF := fiberIsoOfIsHomLift hq φy
    refine ⟨zF, ⟨(CategoricalPullback.mkIso ex ey ?_).symm⟩⟩
    apply Fiber.hom_ext
    have hcart : q.IsHomLift (g ≫ j) (c.map g (c.obj j zF) ≫ c.map j zF) := inferInstance
    have h₁ : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map
        ((c.pullbackFunctor f).map ex.hom ≫
          ((fiberSquareComparison q c f g i j h).obj zF).iso.hom)) := inferInstance
    have h₂ : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map
        (T.iso.hom ≫ (c.pullbackFunctor g).map ey.hom)) := inferInstance
    refine hq.hom_ext (f := g ≫ j) (𝟙 U) (c.map g (c.obj j zF) ≫ c.map j zF) ?_
    simp only [Functor.map_comp, Category.assoc, fiberSquareComparison_obj_iso_hom_fac,
      ChoiceOfPullbacks.pullbackFunctor_map]
    calc Fiber.fiberInclusion.map (c.homMap f ex.hom) ≫ c.map f (c.obj i zF) ≫ c.map i zF
        = (Fiber.fiberInclusion.map (c.homMap f ex.hom) ≫ c.map f (c.obj i zF)) ≫
            c.map i zF := (Category.assoc _ _ _).symm
      _ = c.map f T.fst ≫ ξ := by
        rw [c.homMap_fac f ex.hom, Category.assoc]
        exact congrArg _ eφx
      _ = (Fiber.fiberInclusion.map T.iso.hom ≫ c.map g T.snd) ≫ η := K.w
      _ = Fiber.fiberInclusion.map T.iso.hom ≫ (c.map g T.snd ≫
            Fiber.fiberInclusion.map ey.hom) ≫ c.map j zF := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (congrArg _ eφy.symm)
      _ = _ := by
        rw [← c.homMap_fac g ey.hom]
        simp only [Category.assoc]

include hq in
/-- **Uniqueness of cocones from full faithfulness of the comparison.** If the comparison at the
square is fully faithful, any two cocones over one span are related by exactly one morphism of
cocones. -/
public theorem hasUniqueSquareCocones_of_fullyFaithful
    (hF : (fiberSquareComparison q c f g i j h).FullyFaithful) :
    HasUniqueSquareCocones q f g i j := by
  intro s K K'
  let xF : q.Fiber V := Fiber.mk (IsHomLift.codomain_eq q f s.α)
  let yF : q.Fiber W := Fiber.mk (IsHomLift.codomain_eq q g s.β)
  let uF : q.Fiber U := Fiber.mk (IsHomLift.domain_eq q f s.α)
  let α : uF.1 ⟶ xF.1 := s.α
  let β : uF.1 ⟶ yF.1 := s.β
  have : q.IsHomLift f α := s.isHomLift_α
  have : q.IsHomLift g β := s.isHomLift_β
  let a : uF.1 ⟶ (c.obj f xF).1 := hq.fill (f := f) (g := 𝟙 U) (f' := f) (by simp) (c.map f xF) α
  let b : uF.1 ⟶ (c.obj g yF).1 := hq.fill (f := g) (g := 𝟙 U) (f' := g) (by simp) (c.map g yF) β
  have : q.IsHomLift (𝟙 U) a := hq.fill_isHomLift _ _ _
  have : q.IsHomLift (𝟙 U) b := hq.fill_isHomLift _ _ _
  have ea : a ≫ c.map f xF = α := hq.fill_fac _ _ _
  have eb : b ≫ c.map g yF = β := hq.fill_fac _ _ _
  let ia : uF ≅ c.obj f xF := fiberIsoOfIsHomLift hq a
  let ib : uF ≅ c.obj g yF := fiberIsoOfIsHomLift hq b
  let o : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) :=
    ⟨xF, yF, ia.symm ≪≫ ib⟩
  let zOf : s.Cocone i j → q.Fiber Z := fun L => Fiber.mk (IsHomLift.codomain_eq q i L.ξ)
  have key : ∀ (L : s.Cocone i j), ∃ (ι : o ≅ (fiberSquareComparison q c f g i j h).obj (zOf L)),
      Fiber.fiberInclusion.map ι.hom.fst ≫ c.map i (zOf L) = L.ξ ∧
      Fiber.fiberInclusion.map ι.hom.snd ≫ c.map j (zOf L) = L.η := by
    intro L
    let ξ : xF.1 ⟶ (zOf L).1 := L.ξ
    let η : yF.1 ⟶ (zOf L).1 := L.η
    have : q.IsHomLift i ξ := L.isHomLift_ξ
    have : q.IsHomLift j η := L.isHomLift_η
    have : q.IsHomLift i (c.map i (zOf L)) := inferInstance
    have : q.IsHomLift j (c.map j (zOf L)) := inferInstance
    let φx : xF.1 ⟶ (c.obj i (zOf L)).1 :=
      hq.fill (f := i) (g := 𝟙 V) (f' := i) (by simp) (c.map i (zOf L)) ξ
    let φy : yF.1 ⟶ (c.obj j (zOf L)).1 :=
      hq.fill (f := j) (g := 𝟙 W) (f' := j) (by simp) (c.map j (zOf L)) η
    have : q.IsHomLift (𝟙 V) φx := hq.fill_isHomLift _ _ _
    have : q.IsHomLift (𝟙 W) φy := hq.fill_isHomLift _ _ _
    have eφx : φx ≫ c.map i (zOf L) = ξ := hq.fill_fac _ _ _
    have eφy : φy ≫ c.map j (zOf L) = η := hq.fill_fac _ _ _
    have hw : α ≫ ξ = β ≫ η := L.w
    let ex : xF ≅ c.obj i (zOf L) := fiberIsoOfIsHomLift hq φx
    let ey : yF ≅ c.obj j (zOf L) := fiberIsoOfIsHomLift hq φy
    refine ⟨CategoricalPullback.mkIso ex ey ?_, ?_, ?_⟩
    · apply Fiber.hom_ext
      have : q.IsHomLift (g ≫ j) (c.map g (c.obj j (zOf L)) ≫ c.map j (zOf L)) := inferInstance
      have : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map
          ((c.pullbackFunctor f).map ex.hom ≫
            ((fiberSquareComparison q c f g i j h).obj (zOf L)).iso.hom)) := inferInstance
      have : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map
          (o.iso.hom ≫ (c.pullbackFunctor g).map ey.hom)) := inferInstance
      refine hq.hom_ext (f := g ≫ j) (𝟙 U) (c.map g (c.obj j (zOf L)) ≫ c.map j (zOf L)) ?_
      simp only [Functor.map_comp, Category.assoc, fiberSquareComparison_obj_iso_hom_fac]
      have : IsIso a := hq.isIso_of_isHomLift_isIso (𝟙 U) a
      rw [← cancel_epi a]
      calc a ≫ Fiber.fiberInclusion.map (c.homMap f ex.hom) ≫ c.map f (c.obj i (zOf L)) ≫
            c.map i (zOf L)
          = a ≫ (Fiber.fiberInclusion.map (c.homMap f ex.hom) ≫ c.map f (c.obj i (zOf L))) ≫
              c.map i (zOf L) := by rw [Category.assoc]
        _ = (a ≫ c.map f xF) ≫ ξ := by
            rw [c.homMap_fac f ex.hom, Category.assoc, Category.assoc]
            exact congrArg _ (congrArg _ eφx)
        _ = α ≫ ξ := by rw [ea]
        _ = β ≫ η := hw
        _ = (b ≫ c.map g yF) ≫ (Fiber.fiberInclusion.map ey.hom ≫ c.map j (zOf L)) := by
            rw [eb]; exact congrArg _ eφy.symm
        _ = a ≫ Fiber.fiberInclusion.map o.iso.hom ≫ Fiber.fiberInclusion.map
              (c.homMap g ey.hom) ≫ c.map g (c.obj j (zOf L)) ≫ c.map j (zOf L) := by
            rw [reassoc_of% (c.homMap_fac g ey.hom)]
            change (b ≫ c.map g yF) ≫ _ = a ≫ (CategoryTheory.inv a ≫ b) ≫ _
            simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    · exact eφx
    · exact eφy
  obtain ⟨ιK, hKξ, hKη⟩ := key K
  obtain ⟨ιK', hK'ξ, hK'η⟩ := key K'
  let ξK : xF.1 ⟶ (zOf K).1 := K.ξ
  let ηK : yF.1 ⟶ (zOf K).1 := K.η
  let ξK' : xF.1 ⟶ (zOf K').1 := K'.ξ
  let ηK' : yF.1 ⟶ (zOf K').1 := K'.η
  replace hKξ : Fiber.fiberInclusion.map ιK.hom.fst ≫ c.map i (zOf K) = ξK := hKξ
  replace hKη : Fiber.fiberInclusion.map ιK.hom.snd ≫ c.map j (zOf K) = ηK := hKη
  replace hK'ξ : Fiber.fiberInclusion.map ιK'.hom.fst ≫ c.map i (zOf K') = ξK' := hK'ξ
  replace hK'η : Fiber.fiberInclusion.map ιK'.hom.snd ≫ c.map j (zOf K') = ηK' := hK'η
  let F := fiberSquareComparison q c f g i j h
  have hfst : ∀ {z z' : q.Fiber Z} (t : z ⟶ z'), (F.map t).fst = c.homMap i t := fun _ => rfl
  have hsnd : ∀ {z z' : q.Fiber Z} (t : z ⟶ z'), (F.map t).snd = c.homMap j t := fun _ => rfl
  let θF : zOf K ⟶ zOf K' := hF.preimage (ιK.inv ≫ ιK'.hom)
  have hθF : F.map θF = ιK.inv ≫ ιK'.hom := hF.map_preimage _
  have hθ : q.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map θF) := inferInstance
  have hfst' : c.homMap i θF = ιK.inv.fst ≫ ιK'.hom.fst := by
    rw [← hfst, hθF]; rfl
  have hsnd' : c.homMap j θF = ιK.inv.snd ≫ ιK'.hom.snd := by
    rw [← hsnd, hθF]; rfl
  have hinvx : ιK.hom.fst ≫ ιK.inv.fst = 𝟙 _ := by
    rw [← CategoricalPullback.comp_fst, ιK.hom_inv_id]; rfl
  have hinvy : ιK.hom.snd ≫ ιK.inv.snd = 𝟙 _ := by
    rw [← CategoricalPullback.comp_snd, ιK.hom_inv_id]; rfl
  refine ⟨⟨⟨Fiber.fiberInclusion.map θF, hθ, ?_, ?_⟩⟩, ?_⟩
  · change ξK ≫ Fiber.fiberInclusion.map θF = ξK'
    calc ξK ≫ Fiber.fiberInclusion.map θF
        = Fiber.fiberInclusion.map ιK.hom.fst ≫ c.map i (zOf K) ≫
            Fiber.fiberInclusion.map θF := by rw [← hKξ, Category.assoc]
      _ = Fiber.fiberInclusion.map ιK.hom.fst ≫ Fiber.fiberInclusion.map (c.homMap i θF) ≫
            c.map i (zOf K') := by rw [c.homMap_fac]
      _ = ξK' := by
          rw [hfst', ← Category.assoc, ← Functor.map_comp, ← Category.assoc, hinvx,
            Category.id_comp, hK'ξ]
  · change ηK ≫ Fiber.fiberInclusion.map θF = ηK'
    calc ηK ≫ Fiber.fiberInclusion.map θF
        = Fiber.fiberInclusion.map ιK.hom.snd ≫ c.map j (zOf K) ≫
            Fiber.fiberInclusion.map θF := by rw [← hKη, Category.assoc]
      _ = Fiber.fiberInclusion.map ιK.hom.snd ≫ Fiber.fiberInclusion.map (c.homMap j θF) ≫
            c.map j (zOf K') := by rw [c.homMap_fac]
      _ = ηK' := by
          rw [hsnd', ← Category.assoc, ← Functor.map_comp, ← Category.assoc, hinvy,
            Category.id_comp, hK'η]
  · intro θ₁ θ₂
    let t₁ : zOf K ⟶ zOf K' := ⟨θ₁.θ, θ₁.isHomLift_θ⟩
    let t₂ : zOf K ⟶ zOf K' := ⟨θ₂.θ, θ₂.isHomLift_θ⟩
    have hιx : IsIso (Fiber.fiberInclusion.map ιK.hom.fst) := inferInstance
    have hιy : IsIso (Fiber.fiberInclusion.map ιK.hom.snd) := inferInstance
    let u₁ : (zOf K).1 ⟶ (zOf K').1 := θ₁.θ
    let u₂ : (zOf K).1 ⟶ (zOf K').1 := θ₂.θ
    have c₁ : ξK ≫ u₁ = ξK ≫ u₂ := θ₁.comm_ξ.trans θ₂.comm_ξ.symm
    have c₂ : ηK ≫ u₁ = ηK ≫ u₂ := θ₁.comm_η.trans θ₂.comm_η.symm
    have ex : c.map i (zOf K) ≫ u₁ = c.map i (zOf K) ≫ u₂ := by
      rw [← cancel_epi (Fiber.fiberInclusion.map ιK.hom.fst), ← Category.assoc, hKξ,
        ← Category.assoc, hKξ, c₁]
    have ey : c.map j (zOf K) ≫ u₁ = c.map j (zOf K) ≫ u₂ := by
      rw [← cancel_epi (Fiber.fiberInclusion.map ιK.hom.snd), ← Category.assoc, hKη,
        ← Category.assoc, hKη, c₂]
    have : F.map t₁ = F.map t₂ := by
      apply CategoricalPullback.hom_ext
      · rw [hfst, hfst]
        exact (c.homMap_uniq i t₁ _ (by rw [c.homMap_fac]; exact ex.symm)).symm
      · rw [hsnd, hsnd]
        exact (c.homMap_uniq j t₁ _ (by rw [c.homMap_fac]; exact ey.symm)).symm
    exact congrArg Fiber.fiberInclusion.map (hF.map_injective this)

end Deformation.Artin

