module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Homology.FilteredDerivedCategory.InjectiveResolutions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An additive functor commutes with the total filtration of a double complex

Let `G : 𝒜 ⥤ ℬ` be an additive functor between abelian categories and let `K^{•,•}` be a double
complex of `𝒜` which has, in each total degree, only finitely many nonzero terms. Then
`HomologicalComplex₂.TotalMap.totalIsoOfFinite` is an isomorphism `Tot(G(K)) ≅ G(Tot(K))` of
cochain complexes, and this module upgrades it to an isomorphism of *filtered* complexes: the
filtration of `Tot(G(K))` by a weight `w` which increases along both differentials corresponds to
the filtration of `G(Tot(K))` by the images `G(F^p Tot(K))`.

The whole content is one naturality square,
`HomologicalComplex₂.TotalMap.totalProjector_totalMapf`: the comparison morphism
`Tot(G(K))^n ⟶ G(Tot(K)^n)` conjugates the projector of `Tot(G(K))^n` onto the summands
`G(K^{i,j})` with `P i j` into `G` of the projector of `Tot(K)^n` onto the summands `K^{i,j}`
with `P i j`. Since the steps of the filtration are presented as the images of those projectors
(`HomologicalComplex₂.totalFiltrationStep`), everything else is bookkeeping about images of
idempotents.

## Main definitions

* `CategoryTheory.Limits.mapImageSubobjectIsoOfIdempotent`: a functor carries the image of an
  idempotent to the image of a conjugate idempotent, `Im(e) ≅ G(Im(e₀))`.
* `HomologicalComplex₂.TotalMap.imageTotalProjectorIso`: the degreewise comparison between a
  filtration step of `Tot(G(K))` and `G` of the corresponding step of `Tot(K)`.
* `HomologicalComplex₂.TotalMap.totalFiltrationStepIso`: the same at the level of complexes.
* `HomologicalComplex₂.TotalMap.totalFiltrationIsoOfFinite`: **an additive functor commutes with
  the filtration of the total complex by a weight.**
* `HomologicalComplex₂.TotalMap.totalFiltration₁IsoOfFinite`: **an additive functor commutes with
  the first total filtration** `F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}`.

## Main results

* `CategoryTheory.Limits.isSplitMono_map_imageSubobject_arrow_of_idempotent`: the image of an
  idempotent is a split subobject, so **every** functor sends its inclusion to a split
  monomorphism. This is what makes the hypothesis of `CategoryTheory.FilteredObject.mapOfMono`
  automatic here (`HomologicalComplex₂.TotalMap.mono_map_totalFiltration_ι`).
* `HomologicalComplex₂.TotalMap.totalProjector_totalMapf`: the comparison morphism conjugates the
  summand projectors.
* `HomologicalComplex₂.TotalMap.totalFiltration₁IsoOfFinite_hom_hom`: the underlying morphism of
  complexes of the filtered isomorphism is `totalIsoOfFinite`.

## Implementation notes

The image of an idempotent `e` is a *split* subobject: `factorThruImageSubobject e` is a
retraction of `(imageSubobject e).arrow`
(`CategoryTheory.Limits.imageSubobject_arrow_comp_factorThru_of_idempotent`). This is the only
reason a functor with no exactness hypothesis whatsoever commutes with these filtration steps,
and it is also why the monomorphism hypothesis of `CategoryTheory.FilteredObject.mapOfMono` is
discharged rather than assumed; it is nevertheless kept as an argument of
`totalFiltration₁IsoOfFinite`, since `mapOfMono` takes the proof as data and `Mono` is a
proposition, so any proof gives the same filtered object.

The differential of a filtration step is a `Subobject.factorThru`, which is awkward to rewrite
with directly; `HomologicalComplex₂.totalFiltrationStep_d_comp_arrow` restates it as the
commuting square with the inclusion into the total complex, and that is the only form used below.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Limits

section OneCategory

variable {C : Type*} [Category* C] [Abelian C]

/-- An idempotent acts as the identity on the factorization through its own image. -/
lemma comp_factorThruImageSubobject_of_idempotent {X : C} (e : X ⟶ X) (he : e ≫ e = e) :
    e ≫ factorThruImageSubobject e = factorThruImageSubobject e := by
  rwa [← cancel_mono (imageSubobject e).arrow, Category.assoc, imageSubobject_arrow_comp]

/-- **The image of an idempotent is a split subobject**: `factorThruImageSubobject e` is a
retraction of `(imageSubobject e).arrow`. -/
lemma imageSubobject_arrow_comp_factorThru_of_idempotent {X : C} (e : X ⟶ X) (he : e ≫ e = e) :
    (imageSubobject e).arrow ≫ factorThruImageSubobject e = 𝟙 _ := by
  rw [← cancel_epi (factorThruImageSubobject e), ← Category.assoc, imageSubobject_arrow_comp,
    Category.comp_id, comp_factorThruImageSubobject_of_idempotent e he]

/-- An idempotent acts as the identity on its own image. -/
lemma imageSubobject_arrow_comp_self_of_idempotent {X : C} (e : X ⟶ X) (he : e ≫ e = e) :
    (imageSubobject e).arrow ≫ e = (imageSubobject e).arrow :=
  calc (imageSubobject e).arrow ≫ e
      = ((imageSubobject e).arrow ≫ factorThruImageSubobject e) ≫ (imageSubobject e).arrow := by
        rw [Category.assoc, imageSubobject_arrow_comp]
    _ = (imageSubobject e).arrow := by
        rw [imageSubobject_arrow_comp_factorThru_of_idempotent e he, Category.id_comp]

/-- The inclusion of the image of an idempotent is a split monomorphism. -/
lemma imageSubobject_isSplitMono_arrow_of_idempotent {X : C} (e : X ⟶ X) (he : e ≫ e = e) :
    IsSplitMono (imageSubobject e).arrow :=
  IsSplitMono.mk' ⟨factorThruImageSubobject e,
    imageSubobject_arrow_comp_factorThru_of_idempotent e he⟩

end OneCategory

section TwoCategories

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]

omit [Abelian B] in
/-- **Every functor sends the inclusion of the image of an idempotent to a split
monomorphism**, since that inclusion is already a split monomorphism. -/
lemma isSplitMono_map_imageSubobject_arrow_of_idempotent (G : A ⥤ B) {X : A} (e : X ⟶ X)
    (he : e ≫ e = e) : IsSplitMono (G.map (imageSubobject e).arrow) :=
  IsSplitMono.mk' ⟨G.map (factorThruImageSubobject e), by
    rw [← G.map_comp, imageSubobject_arrow_comp_factorThru_of_idempotent e he, G.map_id]⟩

/-- **A functor carries the image of an idempotent to the image of a conjugate idempotent.**
If `e₀ : X ⟶ X` and `e : Y ⟶ Y` are idempotents and `φ : Y ≅ G(X)` conjugates `e` into
`G(e₀)`, then `φ` restricts to an isomorphism `Im(e) ≅ G(Im(e₀))`; both are presented as the
splitting of an idempotent, and a functor preserves a splitting. -/
@[simps, sga "4 I 8.7.8" "special case"]
def mapImageSubobjectIsoOfIdempotent (G : A ⥤ B) {X : A} (e₀ : X ⟶ X) (he₀ : e₀ ≫ e₀ = e₀)
    {Y : B} (e : Y ⟶ Y) (he : e ≫ e = e) (φ : Y ≅ G.obj X)
    (hφ : e ≫ φ.hom = φ.hom ≫ G.map e₀) :
    (imageSubobject e : B) ≅ G.obj (imageSubobject e₀ : A) where
  hom := (imageSubobject e).arrow ≫ φ.hom ≫ G.map (factorThruImageSubobject e₀)
  inv := G.map (imageSubobject e₀).arrow ≫ φ.inv ≫ factorThruImageSubobject e
  hom_inv_id := by
    have h₁ : ∀ {Z : B} (f : G.obj X ⟶ Z),
        G.map (factorThruImageSubobject e₀) ≫ G.map (imageSubobject e₀).arrow ≫ f =
          G.map e₀ ≫ f := by
      intro Z f
      rw [← Category.assoc, ← G.map_comp, imageSubobject_arrow_comp]
    have h₂ : ∀ {Z : B} (f : G.obj X ⟶ Z), φ.hom ≫ G.map e₀ ≫ f = e ≫ φ.hom ≫ f := by
      intro Z f
      rw [← Category.assoc, ← hφ, Category.assoc]
    simp only [Category.assoc]
    rw [h₁, h₂, Iso.hom_inv_id_assoc, comp_factorThruImageSubobject_of_idempotent e he]
    exact imageSubobject_arrow_comp_factorThru_of_idempotent e he
  inv_hom_id := by
    have hφ' : φ.inv ≫ e = G.map e₀ ≫ φ.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hφ, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h₁ : ∀ {Z : B} (f : Y ⟶ Z), φ.inv ≫ e ≫ f = G.map e₀ ≫ φ.inv ≫ f := by
      intro Z f
      rw [← Category.assoc, hφ', Category.assoc]
    have h₂ : ∀ {Z : B} (f : G.obj X ⟶ Z),
        G.map (imageSubobject e₀).arrow ≫ G.map e₀ ≫ f =
          G.map (imageSubobject e₀).arrow ≫ f := by
      intro Z f
      rw [← Category.assoc, ← G.map_comp, imageSubobject_arrow_comp_self_of_idempotent e₀ he₀]
    have h₃ : ∀ {Z : B} (f : Y ⟶ Z),
        factorThruImageSubobject e ≫ (imageSubobject e).arrow ≫ f = e ≫ f := by
      intro Z f
      rw [← Category.assoc, imageSubobject_arrow_comp]
    simp only [Category.assoc]
    rw [h₃, h₁, h₂, Iso.inv_hom_id_assoc, ← G.map_comp,
      imageSubobject_arrow_comp_factorThru_of_idempotent e₀ he₀, G.map_id]

/-- The isomorphism `mapImageSubobjectIsoOfIdempotent` intertwines the inclusion of the image of
`e` with `G` of the inclusion of the image of `e₀`, along `φ`. -/
@[reassoc (attr := simp)]
lemma mapImageSubobjectIsoOfIdempotent_hom_comp_map_arrow (G : A ⥤ B) {X : A} (e₀ : X ⟶ X)
    (he₀ : e₀ ≫ e₀ = e₀) {Y : B} (e : Y ⟶ Y) (he : e ≫ e = e) (φ : Y ≅ G.obj X)
    (hφ : e ≫ φ.hom = φ.hom ≫ G.map e₀) :
    (mapImageSubobjectIsoOfIdempotent G e₀ he₀ e he φ hφ).hom ≫
        G.map (imageSubobject e₀).arrow =
      (imageSubobject e).arrow ≫ φ.hom := by
  rw [mapImageSubobjectIsoOfIdempotent_hom]
  simp only [Category.assoc]
  rw [← G.map_comp, imageSubobject_arrow_comp, ← hφ, ← Category.assoc,
    imageSubobject_arrow_comp_self_of_idempotent e he]

end TwoCategories

end CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The differential of the `p`-th filtration step `totalFiltrationStep`, followed by the inclusion
of the image of the projector in degree `m`, equals the inclusion in degree `n` followed by the
differential of the total complex. -/
lemma totalFiltrationStep_d_comp_arrow (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j)
    (h₂ : ∀ i j, w i j ≤ w i (j + 1)) (p n m : ℤ) :
    (K.totalFiltrationStep w h₁ h₂ p).d n m ≫
        (imageSubobject (K.totalProjector (fun i j => p ≤ w i j) m)).arrow =
      (imageSubobject (K.totalProjector (fun i j => p ≤ w i j) n)).arrow ≫
        (K.total (ComplexShape.up ℤ)).d n m :=
  Subobject.factorThru_arrow _ _
    (imageSubobject_factors_arrow_comp_of_comp_eq _ _ _
      (K.totalProjector_d (fun i j => p ≤ w i j) (fun i j h => h.trans (h₁ i j))
        (fun i j h => h.trans (h₂ i j)) n m))

end HomologicalComplex₂

namespace HomologicalComplex₂.TotalMap

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (G : A ⥤ B) [G.Additive]
  (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]
  [(mapBicomplex G K).HasTotal (ComplexShape.up ℤ)]

/-- The comparison morphism `Tot(G(K))^n ⟶ G(Tot(K)^n)` intertwines the summand projectors
`totalProjector P n` of the two total complexes. -/
@[reassoc]
lemma totalProjector_totalMapf (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ) :
    (mapBicomplex G K).totalProjector P n ≫ totalMapf G K n =
      totalMapf G K n ≫ G.map (K.totalProjector P n) := by
  refine HomologicalComplex₂.total.hom_ext _ fun i j h => ?_
  rw [ι_totalProjector_assoc, ι_totalMapf_assoc, ← G.map_comp, ι_totalProjector]
  split_ifs with hP
  · exact ι_totalMapf G K n i j h
  · rw [zero_comp, G.map_zero]

/-- **The degreewise comparison of filtration steps**: the summands of `Tot(G(K))^n` singled out
by `P` are `G` of the summands of `Tot(K)^n` singled out by `P`. -/
def imageTotalProjectorIso (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ)
    (hn : IsIso (totalMapf (c₁₂ := ComplexShape.up ℤ) G K n)) :
    (imageSubobject ((mapBicomplex G K).totalProjector P n) : B) ≅
      G.obj (imageSubobject (K.totalProjector P n) : A) :=
  mapImageSubobjectIsoOfIdempotent G (K.totalProjector P n) (totalProjector_idempotent P n)
    ((mapBicomplex G K).totalProjector P n) (totalProjector_idempotent P n)
    (@asIso _ _ _ _ (totalMapf (c₁₂ := ComplexShape.up ℤ) G K n) hn)
    (totalProjector_totalMapf G K P n)

/-- The isomorphism `imageTotalProjectorIso` intertwines the inclusions of the images of the two
projectors into the total complexes, along `totalMapf`. -/
@[reassoc (attr := simp)]
lemma imageTotalProjectorIso_hom_comp_map_arrow (P : ℤ → ℤ → Prop)
    [∀ i j, Decidable (P i j)] (n : ℤ)
    (hn : IsIso (totalMapf (c₁₂ := ComplexShape.up ℤ) G K n)) :
    (imageTotalProjectorIso G K P n hn).hom ≫
        G.map (imageSubobject (K.totalProjector P n)).arrow =
      (imageSubobject ((mapBicomplex G K).totalProjector P n)).arrow ≫
        totalMapf (c₁₂ := ComplexShape.up ℤ) G K n :=
  mapImageSubobjectIsoOfIdempotent_hom_comp_map_arrow _ _ _ _ _ _ _

section Weight

variable (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))

/-- **An additive functor commutes with a step of the filtration of the total complex.** -/
def totalFiltrationStepIso
    (hiso : ∀ n, IsIso (totalMapf (c₁₂ := ComplexShape.up ℤ) G K n)) (p : ℤ) :
    (mapBicomplex G K).totalFiltrationStep w h₁ h₂ p ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.totalFiltrationStep w h₁ h₂ p) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => imageTotalProjectorIso G K (fun i j => p ≤ w i j) n (hiso n))
    (fun n m _ => by
      have := isSplitMono_map_imageSubobject_arrow_of_idempotent G
        (K.totalProjector (fun i j => p ≤ w i j) m)
        (HomologicalComplex₂.totalProjector_idempotent (fun i j => p ≤ w i j) m)
      rw [Functor.mapHomologicalComplex_obj_d, ← cancel_mono (G.map (imageSubobject
        (K.totalProjector (fun i j => p ≤ w i j) m)).arrow)]
      conv_rhs => rw [Category.assoc, imageTotalProjectorIso_hom_comp_map_arrow,
        ← Category.assoc, HomologicalComplex₂.totalFiltrationStep_d_comp_arrow,
        Category.assoc, d_totalMapf]
      conv_lhs => rw [Category.assoc, ← G.map_comp,
        HomologicalComplex₂.totalFiltrationStep_d_comp_arrow, G.map_comp, ← Category.assoc,
        imageTotalProjectorIso_hom_comp_map_arrow, Category.assoc])

omit [(mapBicomplex G K).HasTotal (ComplexShape.up ℤ)] in
/-- **Every additive functor sends the inclusions of the steps of the total filtration to
monomorphisms**, because those inclusions are split: a step is the image of an idempotent. -/
lemma mono_map_totalFiltration_ι (p : ℤᵒᵖ) :
    Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((K.totalFiltration w h₁ h₂).filtration.ι.app p)) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  have := isSplitMono_map_imageSubobject_arrow_of_idempotent G
    (K.totalProjector (fun i j => p.unop ≤ w i j) n)
    (HomologicalComplex₂.totalProjector_idempotent (fun i j => p.unop ≤ w i j) n)
  dsimp
  infer_instance

/-- **An additive functor commutes with the filtration of the total complex by a weight `w`**
which increases along both differentials, for a double complex with finite support in each total
degree: the isomorphism `Tot(G(K)) ≅ G(Tot(K))` of `totalIsoOfFinite` carries the filtration of
`Tot(G(K))` by `w` to the filtration of `G(Tot(K))` by the images of `G` applied to the steps of
the filtration of `Tot(K)` by `w`. -/
def totalFiltrationIsoOfFinite
    (hfin : ∀ n, {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hmono : ∀ p, Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((K.totalFiltration w h₁ h₂).filtration.ι.app p))) :
    (mapBicomplex G K).totalFiltration w h₁ h₂ ≅
      (K.totalFiltration w h₁ h₂).mapOfMono
        (G.mapHomologicalComplex (ComplexShape.up ℤ)) hmono :=
  FilteredObject.isoMk (totalIsoOfFinite G K hfin)
    (fun p => totalFiltrationStepIso G K w h₁ h₂
      (fun n => isIso_totalMapf_of_finite G K n (hfin n)) p.unop)
    (fun p => HomologicalComplex.hom_ext _ _ fun n =>
      imageTotalProjectorIso_hom_comp_map_arrow G K (fun i j => p.unop ≤ w i j) n _)

/-- The underlying morphism of complexes of `totalFiltrationIsoOfFinite` is
`totalIsoOfFinite`. -/
@[simp]
theorem totalFiltrationIsoOfFinite_hom_hom
    (hfin : ∀ n, {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hmono : ∀ p, Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((K.totalFiltration w h₁ h₂).filtration.ι.app p))) :
    (totalFiltrationIsoOfFinite G K w h₁ h₂ hfin hmono).hom.hom =
      (totalIsoOfFinite G K hfin).hom :=
  rfl

end Weight

omit [(mapBicomplex G K).HasTotal (ComplexShape.up ℤ)] in
/-- **Every additive functor sends the inclusions of the steps of the first total filtration to
monomorphisms.** -/
lemma mono_map_totalFiltration₁_ι (p : ℤᵒᵖ) :
    Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (K.totalFiltration₁.filtration.ι.app p)) :=
  mono_map_totalFiltration_ι G K _ _ _ p

/-- **An additive functor commutes with the first total filtration** of a double complex with
finite support in each total degree: the isomorphism `Tot(G(K)) ≅ G(Tot(K))` of
`totalIsoOfFinite` is an isomorphism of filtered complexes from `Tot(G(K))` filtered by
`F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} G(K^{i,j})` to `G(Tot(K))` filtered by the images of `G`
applied to the steps `⨁_{i + j = n, i ≥ p} K^{i,j}`. -/
def totalFiltration₁IsoOfFinite
    (hfin : ∀ n, {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hmono : ∀ p, Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (K.totalFiltration₁.filtration.ι.app p))) :
    (mapBicomplex G K).totalFiltration₁ ≅
      K.totalFiltration₁.mapOfMono (G.mapHomologicalComplex (ComplexShape.up ℤ)) hmono :=
  totalFiltrationIsoOfFinite G K _ _ _ hfin hmono

/-- The underlying morphism of complexes of `totalFiltration₁IsoOfFinite` is
`totalIsoOfFinite`. -/
@[simp]
theorem totalFiltration₁IsoOfFinite_hom_hom
    (hfin : ∀ n, {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hmono : ∀ p, Mono ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (K.totalFiltration₁.filtration.ι.app p))) :
    (totalFiltration₁IsoOfFinite G K hfin hmono).hom.hom = (totalIsoOfFinite G K hfin).hom :=
  rfl

end HomologicalComplex₂.TotalMap

end
