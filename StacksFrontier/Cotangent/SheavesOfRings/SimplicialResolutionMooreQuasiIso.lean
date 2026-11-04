module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteColumnStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteFlatBaseChange
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangle
public import StacksFrontier.Cotangent.StandardResolutionIsResolution

/-!
# The standard resolution of a sheaf of rings is a resolution on the simplicial site

Let `(C, J)` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings
on `C` and let `𝒫_• ⟶ ℬ` be the standard resolution of `ℬ` over `𝒜`. Reading `𝒫_•` as a sheaf of
commutative rings `𝒫` on the simplicial site `Δ × C`, the augmentation becomes a homomorphism
`𝒫 ⟶ π^{-1}ℬ` there, and this file proves that the induced map of complexes of abelian sheaves

`s(𝒫) ⟶ s(π^{-1}ℬ)`

is a quasi-isomorphism. That is the parenthetical "here we use that `𝒫_• ⟶ 𝒜` is a resolution" of
the prose of §92.19 preceding [Stacks, Tag 09DH]: it is the hypothesis `hθ` of
`Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat`, which the theorems below
discharge for the standard resolution instead of carrying.

## Main results

* `AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences_forget`:
  [Stacks, Tag 08P2] for the reindexed Moore complex — a morphism of simplicial abelian groups
  whose underlying morphism of simplicial sets is a homotopy equivalence is a quasi-isomorphism
  on the Moore complexes indexed in cohomological degrees.
* `Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_unitMap_of_forall_homotopyEquivalences`:
  the quasi-isomorphism question about `s(-)` for a homomorphism of presheaves of commutative
  rings on `Δ × C` follows from the underlying morphism of simplicial sets being a homotopy
  equivalence over each object of `C`.
* `Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap`:
  the same question for a homomorphism of simplicial sheaves of commutative rings, from the
  homotopy equivalences of its sections.
* `CategoryTheory.Sheaf.homotopyEquivalences_standardResolution_hom_sections`: [Stacks, Tag 08ND]
  at the free-forgetful adjunction of sheaves of `𝒜`-algebras — the sections over an object of
  the site of the augmentation of the standard resolution are a homotopy equivalence of
  simplicial sets.
* `CategoryTheory.Sheaf.quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap`: **the
  statement the triangle of [Stacks, Tag 09DH] consumes** — `s(𝒫) ⟶ s(π^{-1}ℬ)` is a
  quasi-isomorphism.

## Implementation notes

The contracting homotopy of the bar resolution is not additive — the inclusion of the variables
`b ↦ [b]` is neither a ring map nor a group homomorphism — so there is no extra degeneracy at the
level of abelian sheaves and `SimplicialObject.Augmented.ExtraDegeneracyLast.ofGodement` does not
apply. The argument is therefore the one the source uses for rings: the augmentation whiskered
with the forgetful functor to sheaves of sets is a homotopy equivalence ([Stacks, Tag 08ND],
`CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution`), and a homotopy
equivalence of simplicial sets between simplicial abelian groups is a quasi-isomorphism of Moore
complexes ([Stacks, Tag 08P2]).

The passage from sheaves to sections is what makes the sheaf-level statement follow from the
set-level one with no sheaf-homotopy-group theory: a simplicial homotopy in sheaves of sets is a
diagram of morphisms, so it survives evaluation at an object of the site, and `s(-)` sheafifies a
presheaf-level Moore complex whose quasi-isomorphism question is one about each object of `C`
separately (`Stacks.SimplicialModules.quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft`
and `Stacks.SimplicialModules.quasiIso_mapHomologicalComplex_presheafToSheaf`). Degreewise
surjectivity of the augmentation, which the ring-level statement of [Stacks, Tag 0G5T] needs for
its converse direction, is never used: it is false on sections, and only the forward direction
[Stacks, Tag 08P2] is invoked.

No tag is claimed here. The parenthetical this discharges carries no tag of its own, and
[Stacks, Tag 09DH] stays where it is until the whole triangle is unconditional.

## References

* [Stacks Project, Tag 08ND](https://stacks.math.columbia.edu/tag/08ND)
* [Stacks Project, Tag 08P2](https://stacks.math.columbia.edu/tag/08P2)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace AlgebraicTopology

/-- **[Stacks, Tag 08P2] for the reindexed Moore complex.** Let `f` be a morphism of simplicial
abelian groups whose underlying morphism of simplicial sets is a homotopy equivalence. Then `f`
is a quasi-isomorphism on the Moore complexes indexed in cohomological degrees, simplicial degree
`n` sitting in degree `-n`.

The reindexing along `ComplexShape.embeddingUpIntLE 0` changes no homology group
(`HomologicalComplex.quasiIso_extendMap_iff`), so this is
`AlgebraicTopology.quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget`. -/
theorem quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences_forget
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight f (forget AddCommGrpCat.{u}))) :
    QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map f) := by
  have h : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map f) ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) :=
    HomologicalComplex.quasiIso_extendMap_iff
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) (ComplexShape.embeddingUpIntLE (0 : ℤ))
  exact h.2 (quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget f hf)

end AlgebraicTopology

namespace Stacks.PresheafOfModules.ChangeOfRings

universe u₀

variable {D : Type u₀} [SmallCategory D]

/-- `Stacks.PresheafOfModules.ChangeOfRings.unitMap'` preserves identities. -/
lemma unitMap_id (O : Dᵒᵖ ⥤ CommRingCat.{max u₀ u}) :
    unitMap' (𝟙 O) = 𝟙 (unitPresheaf' O) := rfl

/-- `Stacks.PresheafOfModules.ChangeOfRings.unitMap'` preserves composition. -/
lemma unitMap_comp {O₁ O₂ O₃ : Dᵒᵖ ⥤ CommRingCat.{max u₀ u}} (θ₁ : O₁ ⟶ O₂) (θ₂ : O₂ ⟶ O₃) :
    unitMap' (θ₁ ≫ θ₂) = unitMap' θ₁ ≫ unitMap' θ₂ := rfl

/-- An invertible homomorphism of presheaves of commutative rings is invertible on the underlying
presheaves of abelian groups. -/
instance isIso_unitMap {O₁ O₂ : Dᵒᵖ ⥤ CommRingCat.{max u₀ u}} (θ : O₁ ⟶ O₂) [IsIso θ] :
    IsIso (unitMap' θ) :=
  ⟨unitMap' (inv θ), by rw [← unitMap_comp, IsIso.hom_inv_id, unitMap_id],
    by rw [← unitMap_comp, IsIso.inv_hom_id, unitMap_id]⟩

end Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- A morphism of simplicial objects equal to a homotopy equivalence conjugated by isomorphisms is
a homotopy equivalence. -/
private theorem homotopyEquivalences_of_eq_iso_comp_iso {A : Type*} [Category* A]
    {X Y X' Y' : SimplicialObject A} (e : X' ≅ X) {a : X ⟶ Y} (e' : Y ≅ Y')
    (ha : SimplicialObject.homotopyEquivalences A a) {g : X' ⟶ Y'}
    (hg : g = e.hom ≫ a ≫ e'.hom) : SimplicialObject.homotopyEquivalences A g :=
  hg ▸ SimplicialObject.homotopyEquivalences_iso_comp_iso e a e' ha

/-! ### Reading the question about `s(-)` as one about sections over each object -/

/-- **A homomorphism of presheaves of commutative rings on `Δ × C` whose underlying morphism of
simplicial sets is a homotopy equivalence over every object of `C` is a quasi-isomorphism on the
complexes `s(-)`.** Sheafification creates no quasi-isomorphism question
(`Stacks.SimplicialModules.quasiIso_mapHomologicalComplex_presheafToSheaf`), the presheaf-level
question is one about each object of `C` separately
(`Stacks.SimplicialModules.quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft`), and over
an object it is [Stacks, Tag 08P2]. -/
theorem quasiIso_mooreAbSheafCochain_unitMap_of_forall_homotopyEquivalences
    (h : ∀ V : C, SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight (Functor.whiskerLeft (Functor.prodSectionFst V).op θ)
        (forget CommRingCat.{u}))) :
    QuasiIso ((mooreAbSheafCochain J).map (unitMap'.{u, u} θ)) :=
  quasiIso_mapHomologicalComplex_presheafToSheaf J _
    (quasiIso_mooreAbPresheafCochain_map_of_forall_whiskerLeft (unitMap'.{u, u} θ) fun V =>
      AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_of_homotopyEquivalences_forget
        _ (h V))

/-! ### The sections of the uncurried presheaf of a simplicial sheaf of rings -/

/-- **Restricting the presheaf of commutative rings on `Δ × C` of a simplicial sheaf of
commutative rings to the slice `Δ × {V}` gives the simplicial sheaf's sections over `V`.** Both
are `n ↦ A_n(V)`; the two differ only in that the uncurried presheaf inserts the identity
restriction map of the `C` direction, so the comparison is the identity in each degree. -/
def associatedCommRingPresheafSliceIso (A : SimplicialObject (Sheaf J CommRingCat.{u})) (V : C) :
    (Functor.prodSectionFst V).op ⋙ associatedCommRingPresheaf J A ≅
      A ⋙ sheafToPresheaf J CommRingCat.{u} ⋙
        (evaluation Cᵒᵖ CommRingCat.{u}).obj (op V) where
  hom :=
    { app := fun _ => 𝟙 _
      naturality := by
        intro X Y g
        dsimp [associatedCommRingPresheaf, Functor.prodSectionFst]
        simp }
  inv :=
    { app := fun _ => 𝟙 _
      naturality := by
        intro X Y g
        dsimp [associatedCommRingPresheaf, Functor.prodSectionFst]
        simp }

/-- The comparison `Stacks.SimplicialModules.associatedCommRingPresheafSliceIso` is natural in the
simplicial sheaf of commutative rings. Both sides are the sections of the homomorphism over `V`,
in each simplicial degree. -/
theorem whiskerRight_whiskerLeft_simplicialCommRingSheafMap_hom
    {A A' : SimplicialObject (Sheaf J CommRingCat.{u})} (τ : A ⟶ A') (V : C) :
    Functor.whiskerRight (Functor.whiskerLeft (Functor.prodSectionFst V).op
          (simplicialCommRingSheafMap J τ).hom) (forget CommRingCat.{u}) =
      (Functor.isoWhiskerRight (associatedCommRingPresheafSliceIso J A V)
          (forget CommRingCat.{u})).hom ≫
        Functor.whiskerRight τ ((sheafSections J CommRingCat.{u}).obj (op V) ⋙
          forget CommRingCat.{u}) ≫
        (Functor.isoWhiskerRight (associatedCommRingPresheafSliceIso J A' V)
          (forget CommRingCat.{u})).inv := by
  ext n x
  rfl

/-- **A homomorphism of simplicial sheaves of commutative rings whose sections over every object
of `C` are a homotopy equivalence of simplicial sets is a quasi-isomorphism on the complexes
`s(-)` of the associated sheaves of commutative rings on `Δ × C`.** This is
`Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_unitMap_of_forall_homotopyEquivalences`
read through `Stacks.SimplicialModules.associatedCommRingPresheafSliceIso`. -/
theorem quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap
    {A A' : SimplicialObject (Sheaf J CommRingCat.{u})} (τ : A ⟶ A')
    (h : ∀ V : C, SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight τ ((sheafSections J CommRingCat.{u}).obj (op V) ⋙
        forget CommRingCat.{u}))) :
    QuasiIso ((mooreAbSheafCochain J).map (unitMap' (simplicialCommRingSheafMap J τ).hom)) := by
  refine quasiIso_mooreAbSheafCochain_unitMap_of_forall_homotopyEquivalences J _ fun V => ?_
  exact homotopyEquivalences_of_eq_iso_comp_iso
    (Functor.isoWhiskerRight (associatedCommRingPresheafSliceIso J A V) (forget CommRingCat.{u}))
    (Functor.isoWhiskerRight (associatedCommRingPresheafSliceIso J A' V)
      (forget CommRingCat.{u})).symm (h V)
    (whiskerRight_whiskerLeft_simplicialCommRingSheafMap_hom J τ V)

end Stacks.SimplicialModules

namespace CategoryTheory.Sheaf

open Stacks.SimplicialModules Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-! ### The augmentation of the standard resolution is a homotopy equivalence -/

/-- **[Stacks, Tag 08ND] at the free-forgetful adjunction of sheaves of `𝒜`-algebras.** The
sections over an object `V` of the site of the augmentation `𝒫_• ⟶ ℬ` of the standard resolution
are a homotopy equivalence of simplicial sets: the map admits a morphism of simplicial sets back
whose two composites with it are homotopic to the identities.

The homotopy inverse in degree `n` is the `(n + 1)`-fold inclusion of the variables,
`b ↦ [⋯[b]⋯]`, which is a map of sheaves of sets and not a homomorphism of sheaves of rings; a
simplicial homotopy in sheaves of sets is a diagram of morphisms, so it survives evaluation
at `V`. -/
theorem homotopyEquivalences_standardResolution_hom_sections (V : C) :
    SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight (standardResolution.{u, u, u} J f).hom
        (Under.forget A ⋙ (sheafSections J CommRingCat.{u}).obj (op V) ⋙
          forget CommRingCat.{u})) := by
  classical
  have hND := CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution
    (freeAlgebraSheafAdjunction.{u, u, u} J A)
    (fun n => ((freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad : Under A ⥤ Under A).iterate n)
    (fun _ => rfl)
    (fun n j => Godement.face (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.ε n j)
    (fun n j => Godement.degeneracy (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.δ n j)
    rfl
    (fun n =>
      (Godement.Prep.face_zero
        (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.ε n).trans
          (Category.id_comp _).symm)
    (fun n j =>
      (Godement.Prep.face_succ
        (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.ε n j).trans (by simp))
    (fun n =>
      (Godement.Prep.degeneracy_zero
        (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.δ n).trans
      (CommAlgCat.eq_id_comp_comp_whiskerRight_id'
        (K := ((freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad :
          Under A ⥤ Under A).iterate (n + 1))
        ((freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad : Under A ⥤ Under A)
        (Functor.whiskerLeft
          (((freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad :
            Under A ⥤ Under A).iterate n)
          (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.δ)))
    (fun n j =>
      (Godement.Prep.degeneracy_succ
        (freeAlgebraSheafAdjunction.{u, u, u} J A).toComonad.δ n j).trans (by simp))
    (standardResolutionFunctor.{u, u, u} J A)
    (standardResolutionFunctor_obj.{u, u, u} J A)
    (standardResolutionFunctor_point.{u, u, u} J A)
    (fun n j => standardResolutionFunctor_face.{u, u, u} J A n j)
    (fun n j => standardResolutionFunctor_degeneracy.{u, u, u} J A n j)
    (standardResolutionFunctor_augmentation.{u, u, u} J A)
    (Functor.whiskerRight (standardResolutionFunctor.{u, u, u} J A).hom
      ((Functor.whiskeringRight _ _ _).obj
        (forgetAlgebraSheaf.{u, u, u} J A)))
    (fun _ => rfl)
    (Functor.whiskerRight (standardResolutionFunctor.{u, u, u} J A).hom
      ((Functor.whiskeringLeft _ _ _).obj
        (freeAlgebraSheaf.{u, u, u} J A)))
    (fun _ => rfl)
  have ha : SimplicialObject.homotopyEquivalences (Under A ⥤ Sheaf J (Type u))
      (Functor.whiskerRight (standardResolutionFunctor.{u, u, u} J A).hom
        ((Functor.whiskeringRight _ _ _).obj
          (forgetAlgebraSheaf.{u, u, u} J A))) :=
    ⟨hND.1.choose, hND.1.choose_spec.1, hND.1.choose_spec.2⟩
  have hEval := SimplicialObject.homotopyEquivalences_whiskering_map
    ((evaluation (Under A) (Sheaf J (Type u))).obj (Under.mk f) ⋙
      sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj (op V)) ha
  have hB : (standardResolutionFunctor.{u, u, u} J A).right.obj (Under.mk f) = Under.mk f :=
    Functor.congr_obj (standardResolutionFunctor_point.{u, u, u} J A) (Under.mk f)
  exact homotopyEquivalences_of_eq_iso_comp_iso (Iso.refl _)
    ((SimplicialObject.const (Type u)).mapIso
      ((Under.forget A ⋙ (sheafSections J CommRingCat.{u}).obj (op V) ⋙
        forget CommRingCat.{u}).mapIso (eqToIso hB))) hEval (by ext n x; rfl)

/-- **The sections over an object of the site of the augmentation `ε : 𝒫_• ⟶ ℬ` of the standard
resolution, read on simplicial sheaves of commutative rings, are a homotopy equivalence of
simplicial sets.** This is
`CategoryTheory.Sheaf.homotopyEquivalences_standardResolution_hom_sections`, the two differing
only by the identification `(const ℬ) ⋙ Under.forget 𝒜 ≅ const (Under.forget 𝒜 ℬ)` which
`CategoryTheory.Sheaf.resolutionCommAugmentation` composes with. -/
theorem homotopyEquivalences_resolutionCommAugmentation_sections (V : C) :
    SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight (resolutionCommAugmentation J f)
        ((sheafSections J CommRingCat.{u}).obj (op V) ⋙ forget CommRingCat.{u})) := by
  exact homotopyEquivalences_of_eq_iso_comp_iso (Iso.refl _)
    (Functor.isoWhiskerRight (Functor.constComp SimplexCategoryᵒᵖ (Under.mk f) (Under.forget A))
      ((sheafSections J CommRingCat.{u}).obj (op V) ⋙ forget CommRingCat.{u}))
    (homotopyEquivalences_standardResolution_hom_sections J f V) (by ext n x; rfl)

/-! ### The augmentation on the simplicial site is a quasi-isomorphism of Moore complexes -/

/-- **`s(𝒫) ⟶ s(ℬ_•)` is a quasi-isomorphism**, where `𝒫` is the sheaf of commutative rings on
`Δ × C` of the standard resolution of `ℬ` over `𝒜` and `ℬ_•` the one of the constant simplicial
sheaf `ℬ`. -/
theorem quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap_resolution :
    QuasiIso ((mooreAbSheafCochain J).map (unitMap'
      (simplicialCommRingSheafMap J (resolutionCommAugmentation J f)).hom)) :=
  quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap J _
    (homotopyEquivalences_resolutionCommAugmentation_sections J f)

/-- **The parenthetical of §92.19: `𝒫_• ⟶ ℬ` is a resolution.** The augmentation of the standard
resolution, read as the homomorphism `𝒫 ⟶ π^{-1}ℬ` of sheaves of commutative rings on `Δ × C`
along which [Stacks, Tag 09D3] extends scalars, induces a quasi-isomorphism

`s(𝒫) ⟶ s(π^{-1}ℬ)`

of complexes of abelian sheaves on `C`. This is the hypothesis `hθ` of
`Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat`, so that lemma applies to
the standard resolution with nothing left to assume.

The sheaf of commutative rings on `Δ × C` of the constant simplicial sheaf `ℬ` is `π^{-1}ℬ`
(`Stacks.SimplicialModules.constantSimplicialCommRingIso`), an isomorphism, so this is
`CategoryTheory.Sheaf`'s
`quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap_resolution`. -/
theorem quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap :
    QuasiIso ((mooreAbSheafCochain J).map (unitMap'
      (augmentationCommRingMap J (resolutionCommAugmentation J f)).hom)) := by
  have hcomp : (augmentationCommRingMap J (resolutionCommAugmentation J f)).hom =
      (simplicialCommRingSheafMap J (resolutionCommAugmentation J f)).hom ≫
        (constantSimplicialCommRingIso J B).hom.hom := rfl
  have : IsIso ((constantSimplicialCommRingIso J B).hom.hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Stacks.SimplicialModules.projectionTopology C J)
      CommRingCat.{u}).map (constantSimplicialCommRingIso J B).hom))
  have := quasiIso_mooreAbSheafCochain_unitMap_simplicialCommRingSheafMap_resolution J f
  rw [hcomp, unitMap_comp, Functor.map_comp]
  exact quasiIso_comp _ _

/-- **The base-change unit of a flat simplicial `𝒫`-module along the augmentation is a
quasi-isomorphism**, with nothing assumed about the standard resolution.

This is `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat` with its hypothesis
`hθ` filled by
`CategoryTheory.Sheaf.quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap`, which is
what the prose of §92.19 means by "here we use that `𝒫_• ⟶ 𝒜` is a resolution". -/
theorem quasiIso_mooreSheafBaseChange_app_augmentationCommRingMap_of_flat
    (F : PresheafOfModules.{u}
      (Stacks.ringPresheaf (associatedCommRingPresheaf J (resolutionCommRing J f))))
    (hF : ∀ X : (SimplexCategory × C)ᵒᵖ,
      Module.Flat
        ↥((Stacks.ringPresheaf
          (associatedCommRingPresheaf J (resolutionCommRing J f))).obj X) ↥(F.obj X)) :
    QuasiIso ((Stacks.SimplicialModules.mooreSheafBaseChange J
      (augmentationCommRingMap J (resolutionCommAugmentation J f)).hom).app F) :=
  Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat J _ F hF
    (quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap J f)

end CategoryTheory.Sheaf

end
