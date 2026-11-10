module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.CategoryTheory.Subobject.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse systems in additive and abelian categories; the Mittag-Leffler condition

Stacks, Homological Algebra, Section 12.31: the category of inverse systems in an additive (resp.
abelian) category is additive (resp. abelian, with exactness detected termwise) (02MZ), and the
Mittag-Leffler condition for an inverse system in an abelian category (02N0).
-/

@[expose] public section

section

/-!
## Stacks Tag 02MZ (inverse systems over an additive/abelian category)

Let `C` be a category. We encode an inverse system in `C` (indexed by the
natural numbers, with the maps going from larger to smaller index) as a functor
`ℕᵒᵖ ⥤ C`.

1. If `C` is additive, then the category of inverse systems in `C` is additive.
   We split "additive" into its Mathlib components `Preadditive` and
   `HasFiniteBiproducts`.
2. If `C` is abelian, then the category of inverse systems in `C` is abelian,
   and a short complex `(Kᵢ) → (Lᵢ) → (Mᵢ)` of inverse systems is exact if and
   only if each `Kᵢ → Lᵢ → Mᵢ` is exact (i.e. exactness is detected pointwise by
   evaluation).
-/

open CategoryTheory CategoryTheory.Limits

/-- An inverse system in `C` indexed by the natural numbers: a functor
`ℕᵒᵖ ⥤ C`. -/
abbrev InverseSystemCategoricalFunctorial (C : Type*) [Category C] : Type _ := ℕᵒᵖ ⥤ C

/-- **Stacks 02MZ (1), preadditive.** If `C` is preadditive, then so is the
category of inverse systems in `C`. -/
@[stacks 02MZ "(1) preadditive", reducible]
noncomputable def inverseSystem_preadditive
    (C : Type*) [Category C] [Preadditive C] : Preadditive (InverseSystemCategoricalFunctorial C) :=
  inferInstance

/-- **Stacks 02MZ (1), biproducts.** If `C` is preadditive with finite
biproducts, then the category of inverse systems in `C` has finite biproducts. -/
@[stacks 02MZ "(1) biproducts"]
theorem inverseSystem_hasFiniteBiproducts
    (C : Type*) [Category C] [Preadditive C] [HasFiniteBiproducts C] :
    HasFiniteBiproducts (InverseSystemCategoricalFunctorial C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **Stacks 02MZ (2), abelian.** If `C` is an abelian category, then the
category of inverse systems in `C` is abelian. -/
@[stacks 02MZ "(2) abelian", reducible]
noncomputable def inverseSystem_abelian
    (C : Type*) [Category C] [Abelian C] : Abelian (InverseSystemCategoricalFunctorial C) :=
  inferInstance

/-- **Stacks 02MZ (2), exactness.** A short complex `(Kᵢ) → (Lᵢ) → (Mᵢ)` of
inverse systems over an abelian category is exact if and only if its evaluation
at every index `i` (i.e. `Kᵢ → Lᵢ → Mᵢ`) is exact. -/
@[stacks 02MZ "(2) exactness", sga "3 I 5.2" "partial"]
theorem inverseSystem_shortComplex_exact_iff
    (C : Type*) [Category C] [Abelian C] (S : ShortComplex (InverseSystemCategoricalFunctorial C)) :
    S.Exact ↔ ∀ (i : ℕᵒᵖ), (S.map ((evaluation ℕᵒᵖ C).obj i)).Exact := by
  refine ⟨fun h i => h.map ((evaluation ℕᵒᵖ C).obj i), fun h => ?_⟩
  rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  intro i
  exact .of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (h i))
    (S.mapHomologyIso ((evaluation ℕᵒᵖ C).obj i)).symm

end

section

/-!
The Mittag-Leffler condition for an inverse system in an abelian category.

A Stacks inverse system is indexed by the directed set `ℕ`, so we model it as a
functor `F : ℕᵒᵖ ⥤ C`. For `i ≤ k` the transition map `A_k → A_i` is
`F.map (homOfLE …).op`, and its image, as a subobject of `A_i`, is `transitionImage F i k`.
The system is Mittag-Leffler when for every `i` the images `Im(A_k → A_i)`
stabilize: there is some `c ≥ i` with `Im(A_k → A_i) = Im(A_c → A_i)` for all
`k ≥ c`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type*} [Category C] [Abelian C]

/-- The image of the transition map `A_k → A_i` (for `i ≤ k`) of the inverse
system `F : ℕᵒᵖ ⥤ C`, viewed as a subobject of `A_i = F.obj (op i)`. -/
noncomputable def transitionImage (F : ℕᵒᵖ ⥤ C) (i k : ℕ) (h : i ≤ k) :
    Subobject (F.obj (op i)) :=
  Subobject.mk (image.ι (F.map (homOfLE h).op))

/-- **Stacks Tag 02N0.** The inverse system `F : ℕᵒᵖ ⥤ C` over an abelian
category satisfies the *Mittag-Leffler condition* if for every `i` there exists
`c = c(i) ≥ i` such that `Im(A_k → A_i) = Im(A_c → A_i)` for all `k ≥ c`. -/
@[stacks 02N0, ega "0 13.1.2" "ℕ-indexed systems", ega "III 4.1.7", sga "4½ Rapport 4.11"]
def IsMittagLefflerCategorical (F : ℕᵒᵖ ⥤ C) : Prop :=
  ∀ i : ℕ, ∃ c : ℕ, ∃ hic : i ≤ c, ∀ k : ℕ, ∀ hck : c ≤ k,
    transitionImage F i k (hic.trans hck) = transitionImage F i c hic

end

section

/-!
## Functoriality of the Mittag-Leffler condition

The condition travels along the two comparisons one makes between inverse systems. An exact
functor carries each transition image to the transition image of the image system, so it
preserves the condition; and a natural isomorphism of systems induces an order isomorphism of
the subobject lattices matching the two systems' transition images, so the condition depends
only on the isomorphism class of the system.
-/

open CategoryTheory CategoryTheory.Limits Opposite

/-- The map of subobject lattices induced by a functor preserving monomorphisms: the subobject
of `X` presented by a mono `f` goes to the subobject of `U.obj X` presented by `U.map f`. -/
noncomputable def mapSubobjects {C : Type*} {D : Type*} [Category C] [Category D] (U : C ⥤ D)
    [U.PreservesMonomorphisms] (X : C) : Subobject X ⥤ Subobject (U.obj X) :=
  Subobject.lower (MonoOver.lift (Over.post U) fun f => U.map_mono f.arrow)

/-- `mapSubobjects U X` sends the subobject presented by a mono `f` to the one presented by
`U.map f`. -/
theorem mapSubobjects_mk {C : Type*} {D : Type*} [Category C] [Category D] (U : C ⥤ D)
    [U.PreservesMonomorphisms] {X Y : C} (f : Y ⟶ X) [Mono f] :
    (mapSubobjects U X).obj (Subobject.mk f) = Subobject.mk (U.map f) := rfl

/-- A functor preserving the limits and colimits that build images carries the image of `f` to
the image of `U.map f`: the two monomorphisms into `U.obj Y` present the same subobject. -/
theorem map_imageSubobject_eq {C : Type*} {D : Type*} [Category C] [Category D]
    [HasEqualizers C] [HasImages C] [StrongEpiCategory D] [HasImages D] {X Y : C} (U : C ⥤ D)
    [U.PreservesMonomorphisms]
    [∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) U]
    [∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) U]
    (f : X ⟶ Y) : Subobject.mk (U.map (image.ι f)) = Subobject.mk (image.ι (U.map f)) :=
  Subobject.mk_eq_mk_of_comm _ _ (CategoryTheory.PreservesImage.iso U f).symm
    (CategoryTheory.PreservesImage.inv_comp_image_ι_map U f)

/-- An exact functor turns an equality of transition images of `G` into the corresponding
equality for `G ⋙ U`. -/
theorem transitionImage_comp_eq_of_eq {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (G : ℕᵒᵖ ⥤ C) (U : C ⥤ D) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (i k c : ℕ) (hik : i ≤ k) (hic : i ≤ c)
    (h : transitionImage G i k hik = transitionImage G i c hic) :
    transitionImage (G ⋙ U) i k hik = transitionImage (G ⋙ U) i c hic := by
  let f := G.map (homOfLE hik).op
  let g := G.map (homOfLE hic).op
  change Subobject.mk (image.ι f) = Subobject.mk (image.ι g) at h
  change Subobject.mk (image.ι (U.map f)) = Subobject.mk (image.ι (U.map g))
  simpa only [mapSubobjects_mk, map_imageSubobject_eq] using
    congrArg (mapSubobjects U (G.obj (op i))).obj h

/-- An exact functor preserves the Mittag-Leffler condition: the index at which the transition
images of `G` stabilize serves for `G ⋙ U` as well. -/
theorem IsMittagLefflerCategorical.map {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (G : ℕᵒᵖ ⥤ C) (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U]
    [PreservesFiniteColimits U] (hG : IsMittagLefflerCategorical G) :
    IsMittagLefflerCategorical (G ⋙ U) := fun i => by
  obtain ⟨c, hic, hstab⟩ := hG i
  exact ⟨c, hic, fun k hck =>
    transitionImage_comp_eq_of_eq G U i k c (hic.trans hck) hic (hstab k hck)⟩

/-- Isomorphisms at `i` and `k` commuting with the transition maps match transition images. -/
private theorem transitionImage_map_of_comm_aux {C : Type*} [Category C] [Abelian C] {F G : ℕᵒᵖ ⥤ C}
    {i k : ℕ} (h : i ≤ k) (ei : F.obj (op i) ≅ G.obj (op i)) (ek : F.obj (op k) ≅ G.obj (op k))
    (w : F.map (homOfLE h).op ≫ ei.hom = ek.hom ≫ G.map (homOfLE h).op) :
    (Subobject.map ei.hom).obj (transitionImage F i k h) = transitionImage G i k h := by
  let f := F.map (homOfLE h).op
  let g := G.map (homOfLE h).op
  change (Subobject.map ei.hom).obj (imageSubobject f) = imageSubobject g
  rw [Subobject.map_mk]
  calc
    Subobject.mk (image.ι f ≫ ei.hom) = imageSubobject (f ≫ ei.hom) :=
      Subobject.mk_eq_mk_of_comm _ _ (image.compIso f ei.hom)
        (image.compIso_hom_comp_image_ι f ei.hom)
    _ = imageSubobject g := by
      simp only [f, w]
      exact imageSubobject_iso_comp ek.hom g

/-- A natural isomorphism of inverse systems matches their transition images: pushing the
transition image of `F` forward along the isomorphism's component at `i` gives that of `G`. -/
theorem transitionImage_mapIso {C : Type*} [Category C] [Abelian C] {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G)
    (i k : ℕ) (h : i ≤ k) :
    (Subobject.map (e.hom.app (op i))).obj (transitionImage F i k h) =
      transitionImage G i k h :=
  transitionImage_map_of_comm_aux h (e.app (op i)) (e.app (op k)) (e.hom.naturality _)

/-- If isomorphisms at `i`, `c`, `k` commute with the transition maps, equality of the transition
images `i ≤ k`, `i ≤ c` of `G` transfers to `F`. -/
private theorem transitionImage_eq_of_comm {C : Type*} [Category C] [Abelian C] {F G : ℕᵒᵖ ⥤ C}
    {i c k : ℕ} (hic : i ≤ c) (hik : i ≤ k) (ei : F.obj (op i) ≅ G.obj (op i))
    (ec : F.obj (op c) ≅ G.obj (op c)) (ek : F.obj (op k) ≅ G.obj (op k))
    (wic : F.map (homOfLE hic).op ≫ ei.hom = ec.hom ≫ G.map (homOfLE hic).op)
    (wik : F.map (homOfLE hik).op ≫ ei.hom = ek.hom ≫ G.map (homOfLE hik).op)
    (h : transitionImage G i k hik = transitionImage G i c hic) :
    transitionImage F i k hik = transitionImage F i c hic := by
  apply (Subobject.mapIsoToOrderIso ei).injective
  change (Subobject.map ei.hom).obj (transitionImage F i k hik) =
    (Subobject.map ei.hom).obj (transitionImage F i c hic)
  rw [transitionImage_map_of_comm_aux hik ei ek wik, transitionImage_map_of_comm_aux hic ei ec wic,
    h]

/-- The Mittag-Leffler condition depends only on the isomorphism class of the inverse system. -/
theorem IsMittagLefflerCategorical.of_natIso {C : Type*} [Category C] [Abelian C]
    {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) (hG : IsMittagLefflerCategorical G) :
    IsMittagLefflerCategorical F := fun i => by
  obtain ⟨c, hic, hstab⟩ := hG i
  exact ⟨c, hic, fun k hck => transitionImage_eq_of_comm hic (hic.trans hck) (e.app _) (e.app _)
    (e.app _) (e.hom.naturality _) (e.hom.naturality _) (hstab k hck)⟩

/-- Two isomorphisms `F_i ≅ G_i` and `F_k ≅ G_k` commuting with the transition maps `F_k ⟶ F_i`
and `G_k ⟶ G_i` match the corresponding transition images. No naturality is asked for at other
indices. -/
theorem transitionImage_map_of_comm {C : Type*} [Category C] [Abelian C] {F G : ℕᵒᵖ ⥤ C}
    {i k : ℕ} (h : i ≤ k) (ei : F.obj (op i) ≅ G.obj (op i)) (ek : F.obj (op k) ≅ G.obj (op k))
    (w : F.map (homOfLE h).op ≫ ei.hom = ek.hom ≫ G.map (homOfLE h).op) :
    (Subobject.map ei.hom).obj (transitionImage F i k h) = transitionImage G i k h :=
  transitionImage_map_of_comm_aux h ei ek w

/-- **Mittag-Leffler through triples.** Let `G` be a Mittag-Leffler inverse system. Suppose that
for all indices `k ≤ m ≤ n` the three-term piece `F_n ⟶ F_m ⟶ F_k` of `F` is isomorphic to the
piece `G_n ⟶ G_m ⟶ G_k` of `G`, by isomorphisms which may depend on the triple. Then `F` is
Mittag-Leffler. -/
theorem IsMittagLefflerCategorical.of_forall_iso_of_le_of_le {C : Type*} [Category C] [Abelian C]
    {F G : ℕᵒᵖ ⥤ C} (hG : IsMittagLefflerCategorical G)
    (h : ∀ (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n),
      ∃ (ek : F.obj (op k) ≅ G.obj (op k)) (em : F.obj (op m) ≅ G.obj (op m))
        (en : F.obj (op n) ≅ G.obj (op n)),
        F.map (homOfLE hkm).op ≫ ek.hom = em.hom ≫ G.map (homOfLE hkm).op ∧
        F.map (homOfLE hmn).op ≫ em.hom = en.hom ≫ G.map (homOfLE hmn).op) :
    IsMittagLefflerCategorical F := fun i => by
  obtain ⟨c, hic, hstab⟩ := hG i
  refine ⟨c, hic, fun k hck => ?_⟩
  obtain ⟨ei, ec, ek, wic, wck⟩ := h i c k hic hck
  have wik : F.map (homOfLE (hic.trans hck)).op ≫ ei.hom =
      ek.hom ≫ G.map (homOfLE (hic.trans hck)).op := by
    rw [show (homOfLE (hic.trans hck)).op = (homOfLE hck).op ≫ (homOfLE hic).op from rfl,
      F.map_comp, G.map_comp, Category.assoc, wic, ← Category.assoc, wck, Category.assoc]
  exact transitionImage_eq_of_comm hic _ ei ec ek wic wik (hstab k hck)

end
