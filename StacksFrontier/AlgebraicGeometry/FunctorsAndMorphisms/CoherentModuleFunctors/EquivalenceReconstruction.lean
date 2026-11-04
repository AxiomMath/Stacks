module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.Extension
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Equivalences between categories of coherent modules

Let `X` and `Y` be Noetherian schemes. An equivalence `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` is the composite of
the inverse image along an isomorphism of schemes `f : Y ⟶ X` with tensoring by an invertible
`𝒪_Y`-module `ℒ`, that is, `𝓕 ↦ f^*𝓕 ⊗ ℒ`.

## Main definitions

* `AlgebraicGeometry.CoherentModuleFunctors.pullbackTensor` is the functor `𝓕 ↦ f^*𝓕 ⊗ ℒ`.
* `AlgebraicGeometry.CoherentModuleFunctors.coherentToModules` is the inclusion
  `Coh(𝒪_X) ⥤ Mod(𝒪_X)`.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.isEquivalence`: the
  filtered-colimit-preserving extension of an equivalence of categories of coherent modules is
  an equivalence of the categories of quasi-coherent modules.
* `AlgebraicGeometry.CoherentModuleFunctors.pullbackTensorFunctorIsoCompPullbackTensor`: the
  functor `𝓕 ↦ f^*𝓕 ⊗ ℒ` of this file is
  `AlgebraicGeometry.pullbackTensorFunctor`, the tensoring taken on the other side.
* `AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_quasicoherent`: Tag 0GPJ
  in the shape the deduction below consumes.
* `AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor`: the description of an
  equivalence `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` as `𝓕 ↦ f^*𝓕 ⊗ ℒ`.

## Implementation notes

The quasi-inverse of the given equivalence extends as well, and the two composites of the
extensions are extensions of the two composites of the original functors, hence — the identity
functor being an extension of the identity functor — are identified with the identity by the
uniqueness of Tag 0FZL. That is the whole content of
`FilteredColimitExtension.isEquivalence`, and it is why `FilteredColimitExtension.comp`,
`FilteredColimitExtension.ofIso` and `FilteredColimitExtension.id` are recorded first.

The prescribed form of the functor is stated after the inclusions of the coherent modules into
all `𝒪`-modules, where the inverse image and the tensor product already live, rather than as a
functor between the categories of coherent modules; the inclusions being fully faithful, this is
the displayed formula `F(𝓕) = f^*𝓕 ⊗ ℒ` of the source read in `Mod(𝒪_Y)`. Invertibility is the
universal-property class `Stacks.SheafOfModules.IsInvertible` of Tag 01CS.

Tag 0GPJ — the same description for an equivalence of the categories of *quasi-coherent*
modules — used to be carried as a hypothesis `hquasicoherent` here. It is now proved:
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` gives it for
quasi-compact quasi-separated schemes, which Noetherian schemes are, and
`exists_iso_pullbackTensor_quasicoherent` restates it at the spelling of this file. Nothing is
assumed; the coherent case is deduced by extending `F` to the quasi-coherent modules.

## References

* [Stacks Project, Tag 0GPK](https://stacks.math.columbia.edu/tag/0GPK)
* [Stacks Project, Tag 0GPJ](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry.CoherentModuleFunctors

/-! ### The functor `𝓕 ↦ f^*𝓕 ⊗ ℒ` -/

/-- The inverse image along `f : Y ⟶ X` of an `𝒪_X`-module, tensored by a fixed `𝒪_Y`-module
`L`: the functor `𝓕 ↦ f^*𝓕 ⊗ L` from `𝒪_X`-modules to `𝒪_Y`-modules. -/
def pullbackTensor {X Y : Scheme.{u}} (f : Y ⟶ X) (L : Y.Modules) : X.Modules ⥤ Y.Modules :=
  Scheme.Modules.pullback f ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).flip.obj L

/-- The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` of the coherent `𝒪_X`-modules into all
`𝒪_X`-modules. -/
def coherentToModules (X : Scheme.{u}) : CoherentModules X.ringCatSheaf ⥤ X.Modules :=
  ObjectProperty.ι fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent

/-- The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is the inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` followed by
the inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`. -/
def coherentToQuasicoherentCompιIso (X : Scheme.{u}) :
    coherentToQuasicoherent X ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ≅
      coherentToModules X :=
  ObjectProperty.ιOfLECompιIso _

/-! ### Operations on extensions -/

namespace FilteredColimitExtension

variable {X Y Z : Scheme.{u}}

/-- An extension of a functor is an extension of any functor isomorphic to it. -/
def ofIso {F G : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}
    (E : FilteredColimitExtension X Y F) (α : F ≅ G) : FilteredColimitExtension X Y G where
  functor := E.functor
  preservesFilteredColimits := E.preservesFilteredColimits
  iso := E.iso ≪≫ Functor.isoWhiskerRight α (coherentToQuasicoherent Y)

/-- The composite of two extensions is an extension of the composite. -/
def comp {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}
    {G : CoherentModules Y.ringCatSheaf ⥤ CoherentModules Z.ringCatSheaf}
    (E : FilteredColimitExtension X Y F) (E' : FilteredColimitExtension Y Z G) :
    FilteredColimitExtension X Z (F ⋙ G) where
  functor := E.functor ⋙ E'.functor
  preservesFilteredColimits := inferInstance
  iso := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.iso E'.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F E'.iso ≪≫
    (Functor.associator _ _ _).symm

/-- The identity functor on the quasi-coherent modules extends the identity functor on the
coherent modules. -/
def id (X : Scheme.{u}) : FilteredColimitExtension X X (𝟭 (CoherentModules X.ringCatSheaf)) where
  functor := 𝟭 _
  preservesFilteredColimits := inferInstance
  iso := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- **The extension of an equivalence of categories of coherent modules is an equivalence of the
categories of quasi-coherent modules.** The quasi-inverse extends too, and the composites of the
extensions are extensions of the identity functors, so the uniqueness of the extension identifies
them with the identity. -/
lemma isEquivalence [IsNoetherian X] [IsNoetherian Y]
    {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf} [F.IsEquivalence]
    (E : FilteredColimitExtension X Y F) : E.functor.IsEquivalence := by
  let e := F.asEquivalence
  let E' := filteredColimitExtension Y X e.inverse
  obtain ⟨η, -⟩ :=
    (existsUnique_iso ((E.comp E').ofIso e.unitIso.symm) (FilteredColimitExtension.id X)).exists
  obtain ⟨ε, -⟩ :=
    (existsUnique_iso ((E'.comp E).ofIso e.counitIso) (FilteredColimitExtension.id Y)).exists
  exact (CategoryTheory.Equivalence.mk E.functor E'.functor η.symm ε).isEquivalence_functor

end FilteredColimitExtension

/-! ### Tag 0GPJ, in the shape this file consumes -/

/-- **The functor `𝓕 ↦ f^*𝓕 ⊗ ℒ` of this file is `AlgebraicGeometry.pullbackTensorFunctor`.**
`AlgebraicGeometry.CoherentModuleFunctors.pullbackTensor` tensors on the *right* and
`AlgebraicGeometry.pullbackTensorFunctor` on the *left*; the two agree by
`Stacks.SheafOfModules.TensorRaised.tensorRightRaisedIso`, the canonical native tensor symmetry. -/
def pullbackTensorFunctorIsoCompPullbackTensor {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Y.Modules) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙ pullbackTensor g L ≅
      pullbackTensorFunctor g L :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
    (Stacks.SheafOfModules.TensorRaised.tensorRightRaisedIso.{u, u, u, u} Y.sheaf L))

/-- **Stacks Project, Tag 0GPJ**, for Noetherian schemes and in the spelling this file consumes:
an equivalence `G : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is `𝓕 ↦ g^*𝓕 ⊗ ℒ` for an isomorphism of schemes
`g : Y ≅ X` and an invertible `𝒪_Y`-module `ℒ`.

This is `AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` — a
Noetherian scheme is quasi-compact and quasi-separated — with the tensoring moved to the other
side by `pullbackTensorFunctorIsoCompPullbackTensor`.

No `stacks` attribute: this is a restatement of the tag at a different spelling, and the
covering set for Tag 0GPJ is
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` together
with the pieces already registered.  What matters here is that it is unconditional — it is
what used to be the carried hypothesis `hquasicoherent` of Tags 0GPK, 0GPL and 0FZR. -/
theorem exists_iso_pullbackTensor_quasicoherent (X' Y' : Scheme.{u}) (hX : IsNoetherian X')
    (hY : IsNoetherian Y')
    (G : (SheafOfModules.isQuasicoherent X'.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y'.ringCatSheaf).FullSubcategory) (hG : G.IsEquivalence) :
    ∃ (g : Y' ≅ X') (L : Y'.Modules),
      Stacks.SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L ∧
      Nonempty ((SheafOfModules.isQuasicoherent X'.ringCatSheaf).ι ⋙ pullbackTensor g.hom L ≅
        G ⋙ (SheafOfModules.isQuasicoherent Y'.ringCatSheaf).ι) := by
  have := hX
  have := hY
  have := hG
  obtain ⟨g, M, hM, ⟨θ⟩⟩ :=
    exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence G.asEquivalence
  exact ⟨g, M, hM, ⟨pullbackTensorFunctorIsoCompPullbackTensor g.hom M ≪≫ θ.symm⟩⟩

/-! ### Equivalences of categories of coherent modules -/

/-- **Stacks Project, Tag 0GPK.** Let `X` and `Y` be Noetherian schemes and let
`F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` be an equivalence of categories. Then there are an isomorphism of
schemes `f : Y ⟶ X` and an invertible `𝒪_Y`-module `ℒ` with `F(𝓕) = f^*𝓕 ⊗ ℒ`, naturally in the
coherent `𝒪_X`-module `𝓕`. The corresponding description of an equivalence of the categories of
quasi-coherent modules is Tag 0GPJ, available here as
`exists_iso_pullbackTensor_quasicoherent`; the coherent case follows from it by extending `F` to
the quasi-coherent modules. Nothing is hypothesised. -/
@[stacks 0GPK]
theorem exists_iso_pullbackTensor {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf) [F.IsEquivalence] :
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L ∧
      Nonempty (coherentToModules X ⋙ pullbackTensor f.hom L ≅ F ⋙ coherentToModules Y) := by
  let E := filteredColimitExtension X Y F
  obtain ⟨f, L, hL, ⟨θ⟩⟩ :=
    exists_iso_pullbackTensor_quasicoherent X Y inferInstance inferInstance E.functor
      E.isEquivalence
  refine ⟨f, L, hL, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (coherentToQuasicoherentCompιIso X).symm
      (pullbackTensor f.hom L) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coherentToQuasicoherent X) θ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.iso (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (coherentToQuasicoherentCompιIso Y)

end AlgebraicGeometry.CoherentModuleFunctors

end
