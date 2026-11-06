module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Vanishing
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Vanishing infinitesimal automorphisms and cofibredness in setoids

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and let `x₀` be an
object of the fibre over the residue field. The infinitesimal automorphisms of `x₀` vanish
exactly when the canonical morphism `ℱ_{x₀} ⟶ ℱ̄_{x₀}` from the localization of `𝓕` at `x₀`
to its functor of fibrewise isomorphism classes is an equivalence.

## Main results

* `Deformation.faithful_toIsomorphismClasses_iff`: the morphism to the functor of fibrewise
  isomorphism classes is faithful exactly when a morphism of the cofibered category is
  determined by its image in the base.
* `Deformation.full_toIsomorphismClasses` and `Deformation.essSurj_toIsomorphismClasses`:
  that morphism is always full and essentially surjective, so being an equivalence is
  exactly faithfulness.
* `Deformation.infinitesimalAutomorphisms_eq_bot_iff_isEquivalence`: **Stacks 06K0**.

## Implementation notes

The localization `ℱ_{x₀}` is `Deformation.objectsOverFunctor p x₀.1`, the slice of `𝓕` at
`x₀` (Tag 06GU), and `ℱ̄_{x₀}` is the category of elements of
`Deformation.isomorphismClasses` (Tag 07W5), the functor of fibrewise isomorphism classes of
the remark Tag 06GK; the canonical morphism is `Deformation.toIsomorphismClasses`. Being an
equivalence of categories cofibered in groupoids is rendered as the underlying functor being
an equivalence of categories; the morphism is a `CategoryTheory.BasedFunctor`, hence lies
strictly over `𝒞_Λ` by construction.

Since the canonical morphism is always full and essentially surjective, the whole content is
faithfulness, which for a category cofibered in groupoids is the same as the vanishing of
every automorphism group of every fibre: the "cofibered in setoids" condition of Tag 02XZ,
unfolded. One direction is then immediate, and the other is Tag 06JZ applied to the
structure morphism `x ⟶ x₀` of an object of `ℱ_{x₀}`, which lies over a morphism into the
residue field and hence over a surjection.

## References

* [Stacks Project, Tag 02XZ](https://stacks.math.columbia.edu/tag/02XZ)
* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 06GU](https://stacks.math.columbia.edu/tag/06GU)
* [Stacks Project, Tag 06JC](https://stacks.math.columbia.edu/tag/06JC)
* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JQ](https://stacks.math.columbia.edu/tag/06JQ)
* [Stacks Project, Tag 06JZ](https://stacks.math.columbia.edu/tag/06JZ)
* [Stacks Project, Tag 07W5](https://stacks.math.columbia.edu/tag/07W5)
* [Stacks Project, Tag 06K0](https://stacks.math.columbia.edu/tag/06K0)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

/-! ### Automorphisms of a fibre from vertical endomorphisms -/

section
open CategoryTheory
universe u v u₁ v₁

variable {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}

/-- An endomorphism of an object of a fibre lying over the identity has that identity for its
image. -/
theorem map_eq_id_of_isHomLift_id {A : C} {y : p.Fiber A}
    (f : y.1 ⟶ y.1) (hf : p.IsHomLift (𝟙 A) f) : p.map f = 𝟙 (p.obj y.1) := by
  have := hf
  simpa using IsHomLift.fac' p (𝟙 A) f

/-- The inverse of a vertical endomorphism of an object of a fibre of a category cofibered in
groupoids is again vertical. -/
theorem isHomLift_id_inv_isoOfIsHomLiftId (hp : IsCofiberedInGroupoids p) {A : C}
    {y : p.Fiber A} (f : y.1 ⟶ y.1) (hf : p.IsHomLift (𝟙 A) f) :
    p.IsHomLift (𝟙 A) (isoOfIsHomLiftId hp f hf).inv := by
  refine IsHomLift.of_fac p (𝟙 A) (isoOfIsHomLiftId hp f hf).inv y.2 y.2 ?_
  have hinv := congrArg p.map (isoOfIsHomLiftId hp f hf).inv_hom_id
  rw [p.map_comp, p.map_id, isoOfIsHomLiftId_hom hp f hf,
    map_eq_id_of_isHomLift_id f hf, Category.comp_id] at hinv
  rw [hinv]
  simp

/-- A vertical endomorphism of an object of a fibre of a category cofibered in groupoids is an
automorphism of that object in the fibre. -/
noncomputable def verticalAut (hp : IsCofiberedInGroupoids p) {A : C} {y : p.Fiber A}
    (f : y.1 ⟶ y.1) (hf : p.IsHomLift (𝟙 A) f) : Aut y :=
  .of
    { hom := ⟨f, hf⟩
      inv := ⟨(isoOfIsHomLiftId hp f hf).inv, isHomLift_id_inv_isoOfIsHomLiftId hp f hf⟩
      hom_inv_id := Functor.Fiber.hom_ext (isoOfIsHomLiftId hp f hf).hom_inv_id
      inv_hom_id := Functor.Fiber.hom_ext (isoOfIsHomLiftId hp f hf).inv_hom_id }

/-- The automorphism `verticalAut hp f hf` has underlying morphism `f`. -/
@[simp]
theorem verticalAut_hom_val (hp : IsCofiberedInGroupoids p) {A : C} {y : p.Fiber A}
    (f : y.1 ⟶ y.1) (hf : p.IsHomLift (𝟙 A) f) :
    (verticalAut hp f hf).asIso.hom.val = f := rfl

end

/-! ### Faithfulness, fullness and essential surjectivity -/

section
open CategoryTheory
universe u v u₁ v₁

variable {C : Type u} [Category.{v} C]

/-- The canonical morphism to the functor of fibrewise isomorphism classes records a morphism
only through its image in the base. -/
theorem toIsomorphismClasses_map_val (𝓕 : BasedCategory.{v₁, u₁} C)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {a b : 𝓕.obj} (α : a ⟶ b) :
    ((toIsomorphismClasses 𝓕 h𝓕).map α).hom = 𝓕.p.map α := rfl

/-- The canonical morphism to the functor of fibrewise isomorphism classes is faithful exactly
when a morphism of the cofibered category is determined by its image in the base. -/
theorem faithful_toIsomorphismClasses_iff (𝓕 : BasedCategory.{v₁, u₁} C)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    (toIsomorphismClasses 𝓕 h𝓕).toFunctor.Faithful ↔
      ∀ {a b : 𝓕.obj} (α β : a ⟶ b), 𝓕.p.map α = 𝓕.p.map β → α = β := by
  constructor
  · intro hf a b α β hαβ
    refine hf.map_injective (Functor.Elements.hom_ext ?_)
    rwa [toIsomorphismClasses_map_val, toIsomorphismClasses_map_val]
  · intro h
    refine ⟨fun {a b} α β hαβ => h α β ?_⟩
    rw [← toIsomorphismClasses_map_val 𝓕 h𝓕 α, ← toIsomorphismClasses_map_val 𝓕 h𝓕 β]
    exact congrArg Functor.Elements.Hom.hom hαβ

/-- The canonical morphism to the functor of fibrewise isomorphism classes is full: a morphism
of isomorphism classes is represented by a morphism of the cofibered category. -/
theorem full_toIsomorphismClasses (𝓕 : BasedCategory.{v₁, u₁} C)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) : (toIsomorphismClasses 𝓕 h𝓕).toFunctor.Full :=
  (isomorphismClassesData 𝓕 h𝓕).quotient.full

/-- The canonical morphism to the functor of fibrewise isomorphism classes is essentially
surjective: every isomorphism class is the class of an object. -/
theorem essSurj_toIsomorphismClasses (𝓕 : BasedCategory.{v₁, u₁} C)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) : (toIsomorphismClasses 𝓕 h𝓕).toFunctor.EssSurj := by
  classical
  let data := isomorphismClassesData 𝓕 h𝓕
  let φ := data.projection
  let target := BasedCategory.ofFunctor (Functor.Elements.π data.classes)
  refine ⟨fun z => ?_⟩
  have : (fiberFunctor φ (target.p.obj z)).EssSurj :=
    data.quotient.fiber_essSurj (target.p.obj z)
  obtain ⟨u, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (fiberFunctor φ (target.p.obj z))
    (Functor.Fiber.mk (p := target.p) (a := z) rfl)
  exact ⟨u.1, ⟨Functor.Fiber.fiberInclusion.mapIso e⟩⟩

/-- The canonical morphism to the functor of fibrewise isomorphism classes is an equivalence
exactly when it is faithful, since it is always full and essentially surjective. -/
theorem isEquivalence_toIsomorphismClasses_iff (𝓕 : BasedCategory.{v₁, u₁} C)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    (toIsomorphismClasses 𝓕 h𝓕).toFunctor.IsEquivalence ↔
      (toIsomorphismClasses 𝓕 h𝓕).toFunctor.Faithful :=
  ⟨fun h => h.faithful, fun h =>
    ⟨h, full_toIsomorphismClasses 𝓕 h𝓕, essSurj_toIsomorphismClasses 𝓕 h𝓕⟩⟩

end

/-! ### The localization at a point of the special fibre -/

section
open CategoryTheory IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The slice of a category cofibered in groupoids at an object of the fibre over the residue
field is again cofibered in groupoids, the residue field being a terminal object of `𝒞_Λ`. -/
theorem isCofiberedInGroupoids_objectsOverFunctor (hp : IsCofiberedInGroupoids p)
    {A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (hA₀ : maximalIdeal A₀ = ⊥) (x₀ : p.Fiber A₀) :
    IsCofiberedInGroupoids (objectsOverFunctor p x₀.1) := by
  obtain ⟨X₀, rfl⟩ := x₀
  exact isCofiberedInGroupoids_overForget hp X₀
    (ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _ hA₀)

/-- The localization `ℱ_{x₀}` of a category cofibered in groupoids at an object of the fibre
over the residue field, as a category over `𝒞_Λ`. -/
noncomputable abbrev pointLocalization (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (x₀ : F) :
    BasedCategory.{v₁, max u₁ v₁} (ArtinianLocalAlgCat.{u, v, w} Λ k) :=
  BasedCategory.ofFunctor (objectsOverFunctor p x₀)

end

/-! ### The equivalence criterion -/

section
open CategoryTheory IsLocalRing
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- **Stacks 06K0.** For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and an
object `x₀` of the fibre over the residue field, the infinitesimal automorphisms of `x₀`
vanish exactly when the canonical morphism `ℱ_{x₀} ⟶ ℱ̄_{x₀}` to the functor of fibrewise
isomorphism classes is an equivalence. -/
@[stacks 06K0]
theorem infinitesimalAutomorphisms_eq_bot_iff_isEquivalence (hrs : SatisfiesRS p)
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k} {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    infinitesimalAutomorphisms hrs.1 g e hpair i hi = ⊥ ↔
      (toIsomorphismClasses (pointLocalization p x₀.1)
        (isCofiberedInGroupoids_objectsOverFunctor hrs.1
          (maximalIdeal_eq_bot_of_isCanonicalDualNumberPair hpair)
            x₀)).toFunctor.IsEquivalence := by
  classical
  have hmaxA₀ : maximalIdeal A₀ = ⊥ :=
    maximalIdeal_eq_bot_of_isCanonicalDualNumberPair hpair
  have hcof := isCofiberedInGroupoids_objectsOverFunctor hrs.1 hmaxA₀ x₀
  have heq := (isEquivalence_toIsomorphismClasses_iff (pointLocalization p x₀.1) hcof).trans
    (faithful_toIsomorphismClasses_iff (pointLocalization p x₀.1) hcof)
  refine Iff.trans ?_ heq.symm
  constructor
  · -- vanishing infinitesimal automorphisms makes the morphism faithful
    intro htriv a b α β hαβ
    have hmap : p.map α.left = p.map β.left := hαβ
    obtain ⟨χ, ⟨hχmap, hχfac⟩, -⟩ :=
      exists_unique_cofibered_factor hrs.1 α.left β.left (𝟙 (p.obj b.left))
        (by rw [Category.comp_id]; exact hmap)
    have hχhom : χ ≫ b.hom = b.hom := by
      refine cofibered_left_cancel hrs.1 α.left ?_ ?_
      · rw [p.map_comp, hχmap, Category.id_comp]
      · rw [← Category.assoc, hχfac, Over.w β, Over.w α]
    have hχlift : p.IsHomLift (𝟙 (p.obj b.left)) χ := by
      refine IsHomLift.of_fac p (𝟙 (p.obj b.left)) χ rfl rfl ?_
      simp [hχmap]
    have hblift : p.IsHomLift (p.map b.hom ≫ eqToHom x₀.2) b.hom :=
      IsHomLift.of_fac p _ b.hom rfl x₀.2 (by simp)
    have hbot : relativeInfinitesimalAutomorphisms
        (x' := Functor.Fiber.mk (p := p) (a := b.left) rfl)
        (x := x₀) hrs.1 (p.map b.hom ≫ eqToHom x₀.2) b.hom hblift = ⊥ :=
      relativeInfinitesimalAutomorphisms_eq_bot hrs
        (x' := Functor.Fiber.mk (p := p) (a := b.left) rfl) (x := x₀)
        (x₀ := x₀) (xε := xε) (p.map b.hom ≫ eqToHom x₀.2) b.hom hblift
        (ArtinianLocalAlgCat.hom_surjective _ _ hmaxA₀ (p.map b.hom ≫ eqToHom x₀.2))
        (𝟙 A₀) (𝟙 x₀.1) (IsHomLift.id x₀.2) g e hpair i hi htriv
    have hone : verticalAut hrs.1 (y := Functor.Fiber.mk (p := p) (a := b.left) rfl)
        χ hχlift = 1 :=
      (Subgroup.eq_bot_iff_forall _).1 hbot _
        ((mem_relativeInfinitesimalAutomorphisms_iff
          (x' := Functor.Fiber.mk (p := p) (a := b.left) rfl) (x := x₀)
          hrs.1 (p.map b.hom ≫ eqToHom x₀.2) b.hom hblift _).mpr hχhom)
    have hχid : χ = 𝟙 b.left :=
      congrArg (fun z : Aut (Functor.Fiber.mk (p := p) (a := b.left) rfl) => z.asIso.hom.val)
        hone
    refine Over.OverMorphism.ext ?_
    rw [← hχfac, hχid, Category.comp_id]
  · -- a faithful morphism forces the infinitesimal automorphisms to vanish
    intro hfaith
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    rw [mem_infinitesimalAutomorphisms_iff] at ha
    set r := (canonicalRetraction hrs.1 g e hpair.split i hi).1
    have hαid : (Over.homMk (U := Over.mk r) (V := Over.mk r) a.asIso.hom.val ha) =
        𝟙 (Over.mk r) := by
      refine hfaith _ _ ?_
      show p.map a.asIso.hom.val = p.map (𝟙 xε.1)
      rw [p.map_id]
      exact map_eq_id_of_isHomLift_id a.asIso.hom.val a.asIso.hom.2
    exact Aut.ext (Iso.ext (Functor.Fiber.hom_ext (congrArg Over.Hom.left hαid)))

end

end Deformation

end
