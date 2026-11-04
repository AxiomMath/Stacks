module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit

/-! # The colimit of a diagram of cohomological δ-functors

Let `Φ : I ⥤ DeltaFunctor A B` be a diagram of cohomological δ-functors (Stacks 010Q) and
morphisms of δ-functors (Stacks 010R) between two abelian categories, and let `I` be a shape for
which colimits in `B` exist and are **exact**.  Then the degreewise colimit

  `(colimᵢ Φᵢ)ⁿ(X) = colimᵢ Φᵢⁿ(X)`

is again a cohomological δ-functor, with connecting morphism the colimit of the connecting
morphisms, and each `Φᵢ` maps into it by a morphism of δ-functors.  A family of morphisms of
δ-functors `Φᵢ ⟶ G` compatible with the transition maps induces a morphism of δ-functors
`colimᵢ Φᵢ ⟶ G`.

The connecting morphisms assemble into a *natural transformation of diagrams* exactly because `δ`
is natural in the short exact sequence — here applied not to a morphism of short exact sequences,
as in `StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/FilteredColimit.lean`, but to a morphism of
the index category of `Φ`, through the compatibility `CategoryTheory.DeltaFunctor.Hom.comm` of a
morphism of δ-functors with the connecting morphisms.  The vanishing and naturality fields are the
images under `colim` of the corresponding pointwise identities of diagrams, and the three
exactness fields are the exactness of `I`-colimits in `B` applied to the pointwise exact short
complexes of diagrams, through `CategoryTheory.ShortComplex.exact_of_exact_evaluation`.

This is one of the two ways the δ-functors appearing in the degree induction of Stacks 0A37 are
assembled.  The stage side of the comparison of Stacks 0A37 is
`𝒜 ↦ colim_{a : j → i} Hᵖ(f_a⁻¹U, 𝒜ⱼ)`, a colimit over the (filtered) opposite slice category of
the cohomology δ-functors over the stage opens, each precomposed with the exact evaluation functor
of the category of systems — that precomposition being
`StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/Precomp.lean`.

## Main definitions

* `CategoryTheory.DeltaFunctor.eval`: evaluation of a δ-functor in a fixed degree, as a functor
  `DeltaFunctor A B ⥤ (A ⥤ B)`.
* `CategoryTheory.DeltaFunctor.deg`: the degree-`n` diagram of a diagram of δ-functors, as a
  functor `A ⥤ (I ⥤ B)`.
* `CategoryTheory.DeltaFunctor.deltaDiagram`: the connecting morphisms of a short exact sequence
  assembled into a morphism of degree diagrams.
* `CategoryTheory.DeltaFunctor.colimitDelta`: the colimit δ-functor.
* `CategoryTheory.DeltaFunctor.colimitDeltaι`: the morphism of δ-functors `Φᵢ ⟶ colimᵢ Φᵢ`.
* `CategoryTheory.DeltaFunctor.colimitDeltaDesc`: the morphism of δ-functors out of the colimit
  induced by a compatible family.

## Main results

* `CategoryTheory.DeltaFunctor.colimitDelta_functor` and `colimitDelta_δ`: the component functors
  and the connecting morphisms of the colimit, by definition.
* `CategoryTheory.DeltaFunctor.isZero_colimitDelta_obj`: the colimit δ-functor kills an object in
  a degree in which every member of the diagram does.
* `CategoryTheory.DeltaFunctor.Effaceable.colimitDelta`: the colimit of a diagram of δ-functors
  effaced by a common family of monomorphisms is effaceable, hence universal by Stacks 010T.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.DeltaFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {I : Type u₃} [Category.{v₃} I]

/-! ### Evaluation in a fixed degree -/

/-- **Evaluation of a δ-functor in a fixed degree**, as a functor on the category of δ-functors:
a morphism of δ-functors is in particular a natural transformation in every degree, and the
identity and composition laws of the category of δ-functors are degreewise. -/
@[simps]
def eval (A : Type u₁) [Category.{v₁} A] [Abelian A] (B : Type u₂) [Category.{v₂} B] [Abelian B]
    (n : ℕ) : DeltaFunctor A B ⥤ (A ⥤ B) where
  obj F := F.functor n
  map η := η.app n

/-- **The additivity of the colimit functor on a functor category.**  A colimit inclusion is
jointly epimorphic with its fellows, and precomposition with one turns `colim.map` into the
component of the natural transformation, where addition is computed. -/
instance colim_additive [HasColimitsOfShape I B] : (colim : (I ⥤ B) ⥤ B).Additive where
  map_add {_F _G _α _β} := colimit.hom_ext fun i => by
    rw [colimit.ι_map, Preadditive.comp_add, colimit.ι_map, colimit.ι_map, NatTrans.app_add,
      Preadditive.add_comp]

section Diagram

variable (Φ : I ⥤ DeltaFunctor A B)

/-- **The degree-`n` diagram of a diagram of δ-functors**: the functor `A ⥤ (I ⥤ B)` sending an
object `X` to the diagram `i ↦ Φᵢⁿ(X)`.  It is the flip of `Φ` followed by evaluation in degree
`n`, so its value at `X` has `Φᵢⁿ(X)` at `i` and the degree-`n` component of the transition
morphism of δ-functors at an arrow of `I`. -/
abbrev deg (n : ℕ) : A ⥤ (I ⥤ B) := (Φ ⋙ eval A B n).flip

/-- The degree-`n` diagram is additive, because each `Φᵢⁿ` is and addition of natural
transformations is computed at each index. -/
instance deg_additive (n : ℕ) : (deg Φ n).Additive where
  map_add {_X _Y _f _g} := NatTrans.ext (funext fun i => ((Φ.obj i).functor n).map_add)

/-- **The connecting morphisms of a short exact sequence, assembled into a morphism of degree
diagrams.**  Naturality in the index is the compatibility of a morphism of δ-functors with the
connecting morphisms, `CategoryTheory.DeltaFunctor.Hom.comm`. -/
@[simps]
def deltaDiagram {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (deg Φ n).obj S.X₃ ⟶ (deg Φ (n + 1)).obj S.X₁ where
  app i := (Φ.obj i).δ hS n
  naturality _ _ g := (Φ.map g).comm hS n

variable [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]

/-- The degree-`n` short complex of diagrams `Φᵢⁿ(X₂) → Φᵢⁿ(X₃) → Φᵢⁿ⁺¹(X₁)`, whose colimit is
the corresponding stretch of the long exact sequence of the colimit δ-functor. -/
def degδ₁ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : ShortComplex (I ⥤ B) :=
  ShortComplex.mk ((deg Φ n).map S.g) (deltaDiagram Φ hS n)
    (NatTrans.ext (funext fun i => (Φ.obj i).map_g_δ hS n))

/-- The degree-`n` short complex of diagrams `Φᵢⁿ(X₃) → Φᵢⁿ⁺¹(X₁) → Φᵢⁿ⁺¹(X₂)`. -/
def degδ₂ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : ShortComplex (I ⥤ B) :=
  ShortComplex.mk (deltaDiagram Φ hS n) ((deg Φ (n + 1)).map S.f)
    (NatTrans.ext (funext fun i => (Φ.obj i).δ_map_f hS n))

/-- **The colimit of a diagram of cohomological δ-functors.**  Its degree-`n` component is
`X ↦ colimᵢ Φᵢⁿ(X)` and its connecting morphism at a short exact sequence is the colimit of the
connecting morphisms of the `Φᵢ`.

The three exactness conditions are the exactness of `I`-colimits in `B` applied to the pointwise
exact short complexes of diagrams; the two vanishing conditions are the images under `colim` of
the short complexes `degδ₁` and `degδ₂`, and naturality of `δ` is the image under `colim` of the
naturality square of the diagrams. -/
def colimitDelta : DeltaFunctor A B where
  functor n := deg Φ n ⋙ colim
  additive _ := inferInstance
  δ hS n := colim.map (deltaDiagram Φ hS n)
  map_g_δ hS n := ((degδ₁ Φ hS n).map colim).zero
  δ_map_f hS n := ((degδ₂ Φ hS n).map colim).zero
  mono_map_f {S} hS := by
    have : ∀ i, Mono (((deg Φ 0).map S.f).app i) := fun i => (Φ.obj i).mono_map_f hS
    have : Mono ((deg Φ 0).map S.f) := NatTrans.mono_of_mono_app _
    exact Functor.map_mono colim ((deg Φ 0).map S.f)
  exact_map {S} hS n :=
    (ShortComplex.exact_of_exact_evaluation (S.map (deg Φ n))
      fun i => (Φ.obj i).exact_map hS n).map colim
  exact_δ₁ {S} hS n :=
    (ShortComplex.exact_of_exact_evaluation (degδ₁ Φ hS n)
      fun i => (Φ.obj i).exact_δ₁ hS n).map colim
  exact_δ₂ {S} hS n :=
    (ShortComplex.exact_of_exact_evaluation (degδ₂ Φ hS n)
      fun i => (Φ.obj i).exact_δ₂ hS n).map colim
  δ_naturality hS hT φ n :=
    (CommSq.mk (NatTrans.ext (funext fun i => (Φ.obj i).δ_naturality hS hT φ n))).map colim |>.w

/-- The degree-`n` component of the colimit δ-functor. -/
@[simp]
theorem colimitDelta_functor (n : ℕ) : (colimitDelta Φ).functor n = deg Φ n ⋙ colim := rfl

/-- The connecting morphism of the colimit δ-functor is the colimit of the connecting
morphisms. -/
@[simp]
theorem colimitDelta_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (colimitDelta Φ).δ hS n = colim.map (deltaDiagram Φ hS n) := rfl

/-! ### The colimit cocone of δ-functors -/

/-- **The morphism of δ-functors from a member of the diagram into the colimit.**  Its degree-`n`
component is the colimit inclusion, whose naturality in the object and whose compatibility with
the connecting morphisms are both the computation of `colim.map` on a colimit inclusion. -/
@[simps]
def colimitDeltaι (i : I) : Φ.obj i ⟶ colimitDelta Φ where
  app n :=
    { app := fun X => colimit.ι ((deg Φ n).obj X) i
      naturality := fun _ _ f => (colimit.ι_map ((deg Φ n).map f) i).symm }
  comm hS n := colimit.ι_map (deltaDiagram Φ hS n) i

section Desc

variable {G : DeltaFunctor A B} (t : ∀ i, Φ.obj i ⟶ G)
  (ht : ∀ {i j : I} (g : i ⟶ j), Φ.map g ≫ t j = t i)

/-- **The cocone on the degree-`n` diagram at `X` whose legs are the components of a compatible
family of morphisms of δ-functors.**  The cocone identity is the compatibility of the family,
read in degree `n` at `X`. -/
abbrev descCocone (n : ℕ) (X : A) : Cocone ((deg Φ n).obj X) :=
  Cocone.mk ((G.functor n).obj X)
    { app := fun i => ((t i).app n).app X
      naturality := fun _ _ g =>
        (congrArg (fun z : Φ.obj _ ⟶ G => (z.app n).app X) (ht g)).trans
          (Category.comp_id _).symm }

/-- **The degree-`n` component of the morphism out of the colimit δ-functor** induced by a
compatible family of morphisms of δ-functors. -/
def descNat (n : ℕ) : (colimitDelta Φ).functor n ⟶ G.functor n where
  app X := colimit.desc _ (descCocone Φ t ht n X)
  naturality _ _ f := colimit.hom_ext fun i => by
    simp only [colimitDelta_functor, Functor.comp_map, colimit.ι_map_assoc, colimit.ι_desc,
      colimit.ι_desc_assoc]
    exact ((t i).app n).naturality f

/-- **A colimit inclusion followed by the induced morphism is the corresponding leg.** -/
@[simp]
theorem ι_comp_descNat (n : ℕ) (X : A) (i : I) :
    colimit.ι ((deg Φ n).obj X) i ≫ (descNat Φ t ht n).app X = ((t i).app n).app X :=
  colimit.ι_desc _ i

/-- **The morphism of δ-functors out of the colimit induced by a compatible family.**  Given
morphisms of δ-functors `t i : Φᵢ ⟶ G` with `Φ(g) ≫ t j = t i` for every `g : i ⟶ j`, this is the
induced morphism `colimᵢ Φᵢ ⟶ G`; it is the unique one whose composite with each
`colimitDeltaι` is `t i`.

The compatibility with the connecting morphisms is checked against the colimit inclusions, where
it is the compatibility of the leg `t i`; the rearrangement is written as an explicit chain of
`Eq.trans` because the two endpoints `colimᵢ Φᵢⁿ(X)` and `(colimᵢ Φᵢ)ⁿ(X)` differ by unfolding
the colimit functor, across which a rewriting tactic cannot build a motive. -/
def colimitDeltaDesc : colimitDelta Φ ⟶ G where
  app n := descNat Φ t ht n
  comm {S} hS n := colimit.hom_ext fun i => by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ G.δ hS n) (ι_comp_descNat Φ t ht n S.X₃ i)) ?_
    refine Eq.trans ((t i).comm hS n) ?_
    refine Eq.trans (congrArg (fun z => (Φ.obj i).δ hS n ≫ z)
      (ι_comp_descNat Φ t ht (n + 1) S.X₁ i).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ (descNat Φ t ht (n + 1)).app S.X₁)
      (colimit.ι_map (deltaDiagram Φ hS n) i).symm) ?_
    exact Category.assoc _ _ _

/-- The composite of a colimit inclusion with the induced morphism out of the colimit. -/
@[simp]
theorem colimitDeltaι_comp_colimitDeltaDesc (i : I) :
    colimitDeltaι Φ i ≫ colimitDeltaDesc Φ t ht = t i :=
  hom_ext fun _ => NatTrans.ext (funext fun _ => colimit.ι_desc _ i)

end Desc

/-! ### Vanishing and effaceability -/

/-- **The colimit δ-functor kills an object in a degree in which every member of the diagram
does.** -/
theorem isZero_colimitDelta_obj (n : ℕ) (X : A)
    (h : ∀ i, IsZero (((Φ.obj i).functor n).obj X)) :
    IsZero (((colimitDelta Φ).functor n).obj X) :=
  Functor.map_isZero colim (Functor.isZero_of_isZero_obj _ h)

/-- **The colimit of a diagram of δ-functors effaced by a common family of monomorphisms is
effaceable**, hence universal by Stacks 010T.  The effacing monomorphism of an object for the
colimit is the one that efface it for every member of the diagram at once; that is the form in
which the effaceability input of the degree induction of Stacks 0A37 arrives, the effacing object
being a single stagewise injective system. -/
theorem Effaceable.colimitDelta
    (heff : ∀ X : A, ∃ (E : A) (ι : X ⟶ E), Mono ι ∧
      ∀ (n : ℕ) (i : I), IsZero (((Φ.obj i).functor (n + 1)).obj E)) :
    (colimitDelta Φ).Effaceable where
  nonempty X n := by
    obtain ⟨E, ι, hι, hz⟩ := heff X
    exact ⟨{ I := E, ι := ι, mono := hι
             map_ι := (isZero_colimitDelta_obj Φ (n + 1) E (hz n)).eq_of_tgt _ _ }⟩

end Diagram

end CategoryTheory.DeltaFunctor

end
