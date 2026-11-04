module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrantDoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAb
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectral sequence of an augmentation of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), let `a` be an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z) and let `F` be an abelian sheaf on the total site. Choosing an
injective resolution `F ⟶ I^•` and taking the degreewise direct images `a_{p,*}(I^q)_p` of
Stacks 0D79 gives the double complex `A^{q,p} = a_{p,*}(I^q)_p` of abelian sheaves on the
augmentation site, with the resolution degree outer and the simplicial degree inner. Its second
spectral sequence is a first-quadrant cohomological spectral sequence of abelian sheaves on the
augmentation site, functorial in `F`, and is the spectral sequence of Stacks 0D7A.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.degreewisePushforwardComplexNat`: the
  alternating-coface complex of the cosimplicial abelian sheaf `p ↦ a_{p,*}F_p` of
  Stacks 0D79, as a functor of `F`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.doubleComplex`: the double complex
  `A^{q,p} = a_{p,*}(I^q)_p` of the chosen injective resolution.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.spectralSequence`: **the spectral
  sequence**, as a functor of the abelian sheaf on the total site.

## Implementation notes

The index orientation is forced, as for the topological analogue of Stacks 09W6: the second
spectral sequence of a double complex has `''E_1^{p,q} = H^q(K^{•,p})`, homology in the outer
index of the column with inner index `p`, so the resolution degree has to be the outer one for
the first page to be the `q`-th cohomology of the complex of degreewise direct images in
simplicial degree `p`. Both indices are extended by zero from `ℕ` to `ℤ`.

The double complex is functorial in the sheaf only up to homotopy, an injective resolution being
functorial only into the homotopy category; `HomologicalComplex₂.FilteredHomotopy₂` is what the
spectral sequence construction needs, and homotopy invariance of the induced maps holds from the
first page on, which is why the spectral sequence is presented from its first page.

Three elaboration costs had to be paid down, all of them by naming things rather than by raising
a limit. The categories of abelian sheaves on the total and augmentation sites are reached only
through long instance chains, so the instances used here are named once at the top of the file;
without that the double complex does not elaborate. The homotopy carried through extension by
zero and an additive functor is stated over *abstract* complexes and an *abstract* functor in
`CategoryTheory.Functor.mapExtendUpNatHomotopy` and its two corollaries, because instantiating a
named lemma is cheap where elaborating the same chase at the chosen injective resolutions is not.
And `CategoryTheory.Functor.mapExtendUpNatHomotopyOfCompAt` takes the composite functor as
abstract data together with the equality identifying it, which leaves the multiplicativity law
with a single spelling crossing; stated directly at the composite, its conclusion has three and
exceeds the `isDefEq` budget.

## References

* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 09W6](https://stacks.math.columbia.edu/tag/09W6)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace CategoryTheory.Functor

/-- **An additive functor carries a homotopy of `ℕ`-indexed complexes to a homotopy of the
extensions by zero.** This is `CategoryTheory.Functor.mapHomotopy` of `Homotopy.extend`. -/
def mapExtendUpNatHomotopy {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {B : Type*} [Category* B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    {Z Z' : CochainComplex A ℕ} {φ ψ : Z ⟶ Z'} (H : Homotopy φ ψ) :
    Homotopy ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat)) :=
  G.mapHomotopy (H.extend ComplexShape.embeddingUpNat)


/-- **The image of a homotopy onto a composite under extension by zero and an additive
functor.** -/
def mapExtendUpNatHomotopyOfComp {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {B : Type*} [Category* B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    {Z Z' Z'' : CochainComplex A ℕ} {φ : Z ⟶ Z''} {ψ₁ : Z ⟶ Z'} {ψ₂ : Z' ⟶ Z''}
    (H : Homotopy φ (ψ₁ ≫ ψ₂)) :
    Homotopy ((ComplexShape.embeddingUpNat.extendFunctor A ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
      ((ComplexShape.embeddingUpNat.extendFunctor A ⋙
            G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₁ ≫
        (ComplexShape.embeddingUpNat.extendFunctor A ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₂) :=
  (G.mapExtendUpNatHomotopy H).trans
    (Homotopy.ofEq ((ComplexShape.embeddingUpNat.extendFunctor A ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp ψ₁ ψ₂))

/-- **The image of a homotopy onto an identity under extension by zero and an additive
functor.** -/
def mapExtendUpNatHomotopyOfId {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {B : Type*} [Category* B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    {Z : CochainComplex A ℕ} {φ : Z ⟶ Z} (H : Homotopy φ (𝟙 Z)) :
    Homotopy ((ComplexShape.embeddingUpNat.extendFunctor A ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) (𝟙 _) :=
  (G.mapExtendUpNatHomotopy H).trans
    (Homotopy.ofEq ((ComplexShape.embeddingUpNat.extendFunctor A ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ)).map_id Z))


/-- `CategoryTheory.Functor.mapExtendUpNatHomotopyOfComp` with the composite functor passed as
abstract data together with the equality identifying it. -/
def mapExtendUpNatHomotopyOfCompAt {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {B : Type*} [Category* B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    (E : CochainComplex A ℕ ⥤ HomologicalComplex B (ComplexShape.up ℤ))
    (hE : E = ComplexShape.embeddingUpNat.extendFunctor A ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ))
    {Z Z' Z'' : CochainComplex A ℕ} {φ : Z ⟶ Z''} {ψ₁ : Z ⟶ Z'} {ψ₂ : Z' ⟶ Z''}
    (H : Homotopy φ (ψ₁ ≫ ψ₂)) :
    Homotopy (E.map φ) (E.map ψ₁ ≫ E.map ψ₂) := by
  subst hE
  exact G.mapExtendUpNatHomotopyOfComp H

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) [HasSheafify K AddCommGrpCat.{u}]

/-! ### Short names for the instances of the two sheaf categories

Each of the following is the instance the unqualified search finds; naming it makes the search
one step long. Without them the elaboration of the double complex below exhausts the
instance-heartbeat and the `whnf` budgets, the categories of abelian sheaves on the total site
and on the augmentation site being reached only through long chains. -/

/-- Abelian sheaves on the augmentation site form an abelian category. -/
@[sga "4½ Arcata 1.6.3" "special case"]
noncomputable local instance abelianSheafTarget : Abelian (Sheaf K AddCommGrpCat.{u}) :=
  inferInstance

/-- Abelian sheaves on the total site form an abelian category. -/
@[sga "4½ Arcata 1.6.3" "special case"]
noncomputable local instance abelianSheafTotal :
    Abelian (Sheaf S.totalTopology AddCommGrpCat.{u}) := inferInstance

/-- Abelian sheaves on the total site have enough injectives. -/
noncomputable local instance hasInjectiveResolutionsSheafTotal :
    HasInjectiveResolutions (Sheaf S.totalTopology AddCommGrpCat.{u}) := inferInstance

/-- Abelian sheaves on the total site have a zero object. -/
noncomputable local instance hasZeroObjectSheafTotal :
    HasZeroObject (Sheaf S.totalTopology AddCommGrpCat.{u}) := inferInstance

/-- Abelian sheaves on the augmentation site have small colimits. -/
local instance hasColimitsOfSizeSheafTarget :
    HasColimitsOfSize.{0, 0} (Sheaf K AddCommGrpCat.{u}) := inferInstance

/-- Abelian sheaves on the augmentation site have coproducts indexed by a type in the zeroth
universe. -/
local instance hasColimitsOfShapeDiscreteSheafTarget (I : Type) :
    HasColimitsOfShape (Discrete I) (Sheaf K AddCommGrpCat.{u}) :=
  HasColimitsOfSize.has_colimits_of_shape (Discrete I)

/-! ### The complex of the degreewise direct images -/

/-- The alternating-coface complex of the cosimplicial abelian sheaf `n ↦ a_{n,*}F_n`, as a
functor of the abelian sheaf `F` on the total site. -/
def degreewisePushforwardComplexNat :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ CochainComplex (Sheaf K AddCommGrpCat.{u}) ℕ :=
  (abelianCosimplicialPushforward S D K a).flip ⋙
    alternatingCofaceMapComplex (Sheaf K AddCommGrpCat.{u})

/-- The functor `degreewisePushforwardComplexNat` is additive. -/
instance degreewisePushforwardComplexNat_additive :
    (degreewisePushforwardComplexNat S D K a).Additive where
  map_add := HomologicalComplex.hom_ext _ _ fun p =>
    (abelianComponentPushforward S D K a ⦋p⦌).map_add

/-- The same complex, indexed by the integers by extension by zero. -/
def degreewisePushforwardComplex :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ :=
  degreewisePushforwardComplexNat S D K a ⋙
    ComplexShape.embeddingUpNat.extendFunctor (Sheaf K AddCommGrpCat.{u})

/-- The functor `degreewisePushforwardComplex` is additive. -/
instance degreewisePushforwardComplex_additive :
    (degreewisePushforwardComplex S D K a).Additive := by
  dsimp only [degreewisePushforwardComplex]
  infer_instance

/-! ### The double complex -/

/-- The double complex of a complex of abelian sheaves on the total site, with the simplicial
index in `ℕ`. -/
def doubleComplexNatFunctor :
    CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ ⥤
      HomologicalComplex (CochainComplex (Sheaf K AddCommGrpCat.{u}) ℕ) (ComplexShape.up ℤ) :=
  (degreewisePushforwardComplexNat S D K a).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The double complex `A^{q,p} = a_{p,*}(Z^q)_p` of a complex `Z^•` of abelian sheaves on the
total site, with the degree in `Z^•` outer and the simplicial degree inner. -/
abbrev doubleComplexFunctor :
    CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ ⥤
      HomologicalComplex₂ (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (degreewisePushforwardComplex S D K a).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `doubleComplexFunctor` is `doubleComplexNatFunctor` with the simplicial index extended by
zero. -/
lemma doubleComplexFunctor_eq :
    doubleComplexFunctor S D K a =
      doubleComplexNatFunctor S D K a ⋙
        (ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf K AddCommGrpCat.{u})).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-- The extension by zero of an `ℕ`-indexed cochain complex vanishes in negative degrees. -/
private lemma isZero_extendUpNat_X_of_neg {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] (Y : CochainComplex C ℕ) (q : ℤ) (hq : q < 0) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor C).obj Y).X q) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
    fun i => by change ((i : ℕ) : ℤ) ≠ q; omega

/-- **First-quadrant vanishing of the double complex.** -/
lemma isZero_homology_doubleComplexFunctor_X
    (Z : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ)
    (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((((doubleComplexFunctor S D K a).obj Z).homology q).X p) := by
  rcases h with hp | hq
  · refine (Iso.isZero_iff ((HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u})
      (ComplexShape.up ℤ) p).mapIso
      ((Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor (Sheaf K AddCommGrpCat.{u}))
          (ComplexShape.up ℤ) q).app
          ((doubleComplexNatFunctor S D K a).obj Z)))).2 ?_
    exact isZero_extendUpNat_X_of_neg _ p hp
  · refine Functor.map_isZero (HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u})
      (ComplexShape.up ℤ) p) ?_
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
      (ShortComplex.exact_of_isZero_X₂ _ ?_)
    exact (degreewisePushforwardComplex S D K a).map_isZero (hZ q hq)

/-- The double complex of an `ℕ`-indexed complex of abelian sheaves on the total site: the
complex extended by zero in the negative degrees, fed to `doubleComplexFunctor`. -/
abbrev doubleComplexOfNatFunctor :
    CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℕ ⥤
      HomologicalComplex₂ (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat.extendFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) ⋙
    doubleComplexFunctor S D K a

/-- **The double complex `A^{q,p} = a_{p,*}(I^q)_p` of an abelian sheaf on the total site**, for
the chosen injective resolution `I^•` of the sheaf. -/
abbrev doubleComplex (F : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    HomologicalComplex₂ (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (doubleComplexOfNatFunctor S D K a).obj (injectiveResolution F).cocomplex

/-- The morphism of double complexes attached to a morphism of abelian sheaves. -/
abbrev doubleComplexMap {F F' : Sheaf S.totalTopology AddCommGrpCat.{u}} (f : F ⟶ F') :
    doubleComplex S D K a F ⟶ doubleComplex S D K a F' :=
  (doubleComplexOfNatFunctor S D K a).map
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- A homotopy between two morphisms of `ℕ`-indexed complexes of abelian sheaves on the total
site induces a homotopy between the induced morphisms of double complexes. -/
def extendMapHomotopy {Z Z' : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℕ}
    {φ ψ : Z ⟶ Z'} (H : Homotopy φ ψ) :=
  Functor.mapExtendUpNatHomotopy (degreewisePushforwardComplex S D K a) H

/-- `doubleComplexMap` sends an identity to a filtered homotopy class of the identity. -/
lemma filteredHomotopy₂_doubleComplexMap_id (F : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    HomologicalComplex₂.FilteredHomotopy₂ (doubleComplexMap S D K a (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    (Functor.mapExtendUpNatHomotopyOfId (degreewisePushforwardComplex S D K a)
      (InjectiveResolution.descIdHomotopy F (injectiveResolution F)))

/-- `doubleComplexMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_doubleComplexMap_comp
    {F F' F'' : Sheaf S.totalTopology AddCommGrpCat.{u}} (f : F ⟶ F') (g : F' ⟶ F'') :
    HomologicalComplex₂.FilteredHomotopy₂ (doubleComplexMap S D K a (f ≫ g))
      (doubleComplexMap S D K a f ≫ doubleComplexMap S D K a g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    (Functor.mapExtendUpNatHomotopyOfCompAt (degreewisePushforwardComplex S D K a)
      (doubleComplexOfNatFunctor S D K a) rfl
      (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
        (injectiveResolution F') (injectiveResolution F'')))

/-! ### The spectral sequence -/

/-- The chosen injective resolution, extended by zero, vanishes in negative degrees. -/
lemma isZero_injectiveResolutionExtend_X (F : Sheaf S.totalTopology AddCommGrpCat.{u}) (q : ℤ)
    (hq : q < 0) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf S.totalTopology AddCommGrpCat.{u})).obj
        (injectiveResolution F).cocomplex).X q) :=
  isZero_extendUpNat_X_of_neg _ q hq

/-- **The spectral sequence on `ℤ × ℤ`**, functorial in the abelian sheaf on the total site: the
second spectral sequence of the double complex `A^{q,p} = a_{p,*}(I^q)_p` of the chosen injective
resolution, presented from its first page. -/
def spectralSequenceZ :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequence (Sheaf K AddCommGrpCat.{u}) 1 where
  obj F := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 1 by omega)).obj
    (doubleComplex S D K a F).spectralSequence₂
  map f := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 1 by omega)).map
    (HomologicalComplex₂.spectralSequenceMap₂ (doubleComplexMap S D K a f))
  map_id F := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (filteredHomotopy₂_doubleComplexMap_id S D K a F)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_id]
    simp
  map_comp f g := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (filteredHomotopy₂_doubleComplexMap_comp S D K a f g)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_comp]
    rfl

/-- **The spectral sequence lies in the first quadrant.** -/
lemma isFirstQuadrant_spectralSequenceZ (F : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((spectralSequenceZ S D K a).obj F) := by
  refine CategoryTheory.SpectralSequence.isFirstQuadrant_of_isZero_page _ fun x hx => ?_
  refine (Iso.isZero_iff (HomologicalComplex₂.isoOnePageTotalFiltration₂
    (doubleComplex S D K a F) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) x.1 x.2)).2 ?_
  exact isZero_homology_doubleComplexFunctor_X S D K a _
    (isZero_injectiveResolutionExtend_X S F) x.1 x.2 hx

/-- **The spectral sequence of an abelian sheaf.** For an abelian sheaf `F` on the total site of
an augmented simplicial site, the second spectral sequence of the double complex
`A^{q,p} = a_{p,*}(I^q)_p` of a chosen injective resolution of `F`, built from the degreewise
direct images of Stacks 0D79: a first-quadrant cohomological spectral sequence of abelian sheaves
on the augmentation site, functorial in `F` and presented from its first page. -/
def spectralSequence :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequenceNat (Sheaf K AddCommGrpCat.{u}) 1 :=
  CategoryTheory.SpectralSequence.natRestrictComp (spectralSequenceZ S D K a)
    (isFirstQuadrant_spectralSequenceZ S D K a)

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
