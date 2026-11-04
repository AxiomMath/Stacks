module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of quasi-compact and quasi-separated schemes over a base

Stacks, Lemma 0FW9 (de Rham Chern classes) and Lemma 0FWB (the de Rham Chern character) apply
Weil Cohomology Theories, Section 45.12 to the category `𝒞` of all quasi-compact and
quasi-separated schemes (over `𝐙`, respectively over `𝐐`), with all morphisms (over the base).
This file defines that category over an arbitrary base scheme `B` and proves the closure
properties Section 45.12 asks of it:

* clause (1): every object is quasi-compact;
* clause (2): an open and closed subscheme of an object is an object, and a morphism of `𝒞` into
  `X` which factors through it is a morphism of `𝒞` into it;
* clause (3)(a): the projective bundle `𝐏(ℰ)` of a finite locally free module of constant rank on
  an object is an object, and its projection is a morphism of `𝒞`: the projection is proper, so
  `𝐏(ℰ)` is again quasi-compact and quasi-separated;
* clause (3)(b): for a morphism `f : X' ⟶ X` of `𝒞` the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a
  morphism of `𝒞`;
* clause (3)(c): for a surjection `ℰ ⟶ 𝓕` of finite locally free modules the induced closed
  immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`.

Since all morphisms of schemes over `B` between objects are morphisms of `𝒞`, clauses (3)(b) and
(3)(c) only ask that the constructed morphisms lie over `B`.

## Main definitions

* `Stacks.WeilCohomology.QCQSScheme B`: quasi-compact and quasi-separated schemes over `B`, as an
  object property of the category of schemes over `B`.
* `Stacks.WeilCohomology.QCQSScheme.bundleObject`: clause (3)(a).
* `Stacks.WeilCohomology.QCQSScheme.clopenSubobject`: clause (2).

## Main results

* `Stacks.WeilCohomology.QCQSScheme.exists_isBundleCompare`: clause (3)(b).
* `Stacks.WeilCohomology.QCQSScheme.exists_isBundleEmbedding`: clause (3)(c).

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology

/-- **Quasi-compact and quasi-separated schemes over `B`**, as an object property of the category
of schemes over `B`. -/
@[sga "6 II 3.0"]
def QCQSScheme (B : Scheme.{u}) : ObjectProperty (Over B) :=
  fun X => CompactSpace X.left ∧ QuasiSeparatedSpace X.left

namespace QCQSScheme

variable {B : Scheme.{u}}

/-- The underlying scheme of a quasi-compact and quasi-separated scheme over `B`. -/
abbrev toScheme (B : Scheme.{u}) : (QCQSScheme B).FullSubcategory ⥤ Scheme.{u} :=
  (QCQSScheme B).ι ⋙ Over.forget B

/-- An object of the category is quasi-compact; this is clause (1) of Section 45.12. -/
instance compactSpace (X : (QCQSScheme B).FullSubcategory) :
    CompactSpace ((toScheme B).obj X) :=
  X.2.1

/-- An object of the category is quasi-separated. -/
instance quasiSeparatedSpace (X : (QCQSScheme B).FullSubcategory) :
    QuasiSeparatedSpace ((toScheme B).obj X) :=
  X.2.2

/-- A quasi-compact and quasi-separated scheme over `B` from a scheme over `B`. -/
abbrev mk {Y : Scheme.{u}} (f : Y ⟶ B) (hc : CompactSpace Y) (hs : QuasiSeparatedSpace Y) :
    (QCQSScheme B).FullSubcategory :=
  ⟨Over.mk f, hc, hs⟩

/-- A morphism of schemes over `B` between objects is a morphism of the category. -/
abbrev homMk {X Y : (QCQSScheme B).FullSubcategory}
    (f : (toScheme B).obj X ⟶ (toScheme B).obj Y) (hf : f ≫ Y.obj.hom = X.obj.hom) : X ⟶ Y :=
  ObjectProperty.homMk (Over.homMk f hf)

/-- The underlying morphism of schemes of `homMk f hf` is `f`. -/
@[simp]
theorem map_homMk {X Y : (QCQSScheme B).FullSubcategory}
    (f : (toScheme B).obj X ⟶ (toScheme B).obj Y) (hf : f ≫ Y.obj.hom = X.obj.hom) :
    (toScheme B).map (homMk f hf) = f := rfl

/-- A morphism of the category is a morphism of schemes over `B`. -/
theorem w {X Y : (QCQSScheme B).FullSubcategory} (f : X ⟶ Y) :
    (toScheme B).map f ≫ Y.obj.hom = X.obj.hom :=
  Over.w f.hom

/-- A morphism of the category is determined by its underlying morphism of schemes. -/
theorem hom_ext' {X Y : (QCQSScheme B).FullSubcategory} {f g : X ⟶ Y}
    (h : (toScheme B).map f = (toScheme B).map g) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-! ### Clause (3)(a): projective bundles -/

section Bundle

variable (X : (QCQSScheme B).FullSubcategory) (E : ((toScheme B).obj X).Modules) (r : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))

/-- **The projective bundle `𝐏(ℰ)` of a finite locally free module of constant rank `r + 1` on a
quasi-compact and quasi-separated scheme is quasi-compact and quasi-separated**: its projection is
proper. -/
def bundle : (QCQSScheme B).FullSubcategory :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    (hM := hE)
  mk (Stacks.Chow.bundleProj E ≫ X.obj.hom)
    (QuasiCompact.compactSpace_of_compactSpace (Stacks.Chow.bundleProj E))
    (quasiSeparatedSpace_of_quasiSeparated (Stacks.Chow.bundleProj E))

/-- The projection `𝐏(ℰ) ⟶ X`. -/
def bundleProj : bundle X E r hE ⟶ X :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    (hM := hE)
  homMk (Stacks.Chow.bundleProj E) rfl

/-- **Clause (3)(a) of Section 45.12**: the projective bundle with its projection, as an object
of the category of quasi-compact and quasi-separated schemes over `B`. -/
def bundleObject : BundleObject (toScheme B) X E r where
  bundle := bundle X E r hE
  proj := bundleProj X E r hE
  isBundle :=
    { rank := hE
      iso := Iso.refl _
      iso_hom_comp_bundleProj := by
        simp only [Iso.refl_hom]
        rfl }

end Bundle

/-! ### Clause (2): open and closed subschemes -/

/-- **An open and closed subscheme of a quasi-compact and quasi-separated scheme is
quasi-compact and quasi-separated.** -/
def clopen (X : (QCQSScheme B).FullSubcategory) (U : ((toScheme B).obj X).Opens)
    (hU : IsClopen (U : Set ((toScheme B).obj X))) : (QCQSScheme B).FullSubcategory :=
  mk (U.ι ≫ X.obj.hom)
    (isCompact_iff_compactSpace.mp (hU.isClosed.isCompact))
    (quasiSeparatedSpace_of_quasiSeparated U.ι)

/-- **Clause (2) of Section 45.12**: an open and closed subscheme with its inclusion, as an object
of the category of quasi-compact and quasi-separated schemes over `B`. -/
def clopenSubobject (X : (QCQSScheme B).FullSubcategory) (U : ((toScheme B).obj X).Opens)
    (hU : IsClopen (U : Set ((toScheme B).obj X))) :
    ClopenSubobject (toScheme B) X U where
  obj := clopen X U hU
  hom := homMk U.ι rfl
  iso := Iso.refl _
  iso_hom_comp_ι := Category.id_comp _
  exists_factor {Z} h hZ := by
    have hV : IsOpenImmersion U.ι := inferInstance
    have hrange : Set.range ((toScheme B).map h) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hZ z
    refine ⟨homMk (@IsOpenImmersion.lift _ _ _ U.ι ((toScheme B).map h) hV hrange) ?_, ?_⟩
    · have h1 := @IsOpenImmersion.lift_fac _ _ _ U.ι ((toScheme B).map h) hV hrange
      have h2 : (@IsOpenImmersion.lift _ _ _ U.ι ((toScheme B).map h) hV hrange ≫ U.ι) ≫
          X.obj.hom = Z.obj.hom := by
        rw [h1]
        exact w h
      exact (Category.assoc _ _ _).symm.trans h2
    · refine hom_ext' ?_
      change @IsOpenImmersion.lift _ _ _ U.ι ((toScheme B).map h) hV hrange ≫ U.ι = _
      exact @IsOpenImmersion.lift_fac _ _ _ U.ι _ hV _

/-- Reading `homMk f hf` through the identity identifications of `bundleObject` gives `f`. -/
private theorem map_homMk_comp_id {X Y : (QCQSScheme B).FullSubcategory}
    (f : (toScheme B).obj X ⟶ (toScheme B).obj Y) (hf : f ≫ Y.obj.hom = X.obj.hom) :
    (toScheme B).map (homMk f hf) ≫ 𝟙 _ = 𝟙 _ ≫ f :=
  (Category.comp_id _).trans ((map_homMk _ _).trans (Category.id_comp _).symm)

/-! ### Clauses (3)(b) and (3)(c) -/

section Compare

variable {X X' : (QCQSScheme B).FullSubcategory} (f : X' ⟶ X)
  (E : ((toScheme B).obj X).Modules) (r : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
  (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (r + 1))

/-- The morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of schemes over `B`: it commutes with the
structure morphisms of the two bundles. -/
theorem bundleBaseChangeHom_comp_hom :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (r + 1) (hM := hE)
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (r + 1) (hM := hE')
    Stacks.Chow.bundleBaseChangeHom ((toScheme B).map f) E
        ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (Iso.refl _).symm ≫
      (Stacks.Chow.bundleProj E ≫ X.obj.hom) =
      Stacks.Chow.bundleProj ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) ≫
        X'.obj.hom := by
  rw [← Category.assoc, Stacks.Chow.bundleBaseChangeHom_bundleProj, Category.assoc, w f]

/-- The induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)`, as a morphism of `𝒞`. -/
def bundleCompareHom :
    (bundleObject X' ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) r hE').bundle ⟶
      (bundleObject X E r hE).bundle :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (r + 1) (hM := hE)
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (r + 1) (hM := hE')
  homMk (Stacks.Chow.bundleBaseChangeHom ((toScheme B).map f) E
    ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (Iso.refl _).symm)
    (bundleBaseChangeHom_comp_hom f E r hE hE')

/-- **Clause (3)(b) of Section 45.12**: for a morphism `f : X' ⟶ X` of `𝒞` and a module `ℰ` of
constant rank `r + 1` on `X`, the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. -/
theorem isBundleCompare_bundleCompareHom :
    IsBundleCompare f (bundleObject X E r hE)
      (bundleObject X' ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) r hE')
      (Iso.refl _) (bundleCompareHom f E r hE hE') where
  comp_proj := by
    let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (r + 1) (hM := hE)
    let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (r + 1) (hM := hE')
    refine hom_ext'
      (((toScheme B).map_comp _ _).trans (Eq.trans ?_ ((toScheme B).map_comp _ _).symm))
    exact Stacks.Chow.bundleBaseChangeHom_bundleProj _ _ _ _
  map_eq := by
    simp only [BundleObject.iso, bundleObject, Iso.refl_hom]
    exact map_homMk_comp_id _ _

end Compare

/-- **Clause (3)(b) of Section 45.12**, in the existential form of
`Stacks.WeilCohomology.BundleCompareClause`. -/
theorem exists_isBundleCompare (X X' : (QCQSScheme B).FullSubcategory) (f : X' ⟶ X)
    (E : ((toScheme B).obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) (r + 1)) :
    ∃ g : (bundleObject X' ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) r hE').bundle ⟶
        (bundleObject X E r hE).bundle,
      IsBundleCompare f (bundleObject X E r hE)
        (bundleObject X' ((Scheme.Modules.pullback ((toScheme B).map f)).obj E) r hE')
        (Iso.refl _) g :=
  ⟨bundleCompareHom f E r hE hE', isBundleCompare_bundleCompareHom f E r hE hE'⟩

section Embedding

variable {X : (QCQSScheme B).FullSubcategory}
  (T : ShortComplex ((toScheme B).obj X).Modules) (hT : T.ShortExact) (r : ℕ)
  (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ (r + 1 + 1))

/-- The closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of schemes over `B`: it commutes with the
structure morphisms of the two bundles. -/
theorem bundleEmbedding_comp_hom :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
      (r + 1 + 1) (hM := hE)
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
      (r + 1) (hM := hF)
    haveI := hT.epi_g
    Stacks.Chow.GenuineChern.bundleEmbedding T.g ≫ (Stacks.Chow.bundleProj T.X₂ ≫ X.obj.hom) =
      Stacks.Chow.bundleProj T.X₃ ≫ X.obj.hom := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
    (r + 1 + 1) (hM := hE)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
    (r + 1) (hM := hF)
  have := hT.epi_g
  rw [← Category.assoc, Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj]

/-- The induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)`, as a morphism of `𝒞`. -/
def bundleEmbeddingHom :
    (bundleObject X T.X₃ r hF).bundle ⟶ (bundleObject X T.X₂ (r + 1) hE).bundle :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
    (r + 1 + 1) (hM := hE)
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
    (r + 1) (hM := hF)
  haveI := hT.epi_g
  homMk (Stacks.Chow.GenuineChern.bundleEmbedding T.g) (bundleEmbedding_comp_hom T hT r hF hE)

/-- **Clause (3)(c) of Section 45.12**: for a short exact sequence `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` with `ℰ`
and `𝓕` finite locally free of ranks `r + 2` and `r + 1`, the induced closed immersion
`𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. -/
theorem isBundleEmbedding_bundleEmbeddingHom :
    IsBundleEmbedding T hT (bundleObject X T.X₂ (r + 1) hE) (bundleObject X T.X₃ r hF)
      (bundleEmbeddingHom T hT r hF hE) where
  comp_proj := by
    let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
      (r + 1 + 1) (hM := hE)
    let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
      (r + 1) (hM := hF)
    have := hT.epi_g
    refine hom_ext' (((toScheme B).map_comp _ _).trans ?_)
    exact Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj _
  map_eq := by
    simp only [BundleObject.iso, bundleObject, Iso.refl_hom]
    exact map_homMk_comp_id _ _

end Embedding

end QCQSScheme

end Stacks.WeilCohomology

end
