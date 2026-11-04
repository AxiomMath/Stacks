module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence

/-!
# The affine-section functor of a big site is fully faithful

Let `U = Spec A` be affine and let `B` be a chosen big `τ`-site over `U`. The affine-spectrum
functor `Stacks.Adequate.affineSpecOver` sends an `A`-algebra of the site to its spectrum,
regarded as an object of the site over `U`; the affine-section functor
`Stacks.Adequate.affineSectionsFunctor` is restriction of sections along it, followed by the
scalar identification `Stacks.Adequate.affineRingMap`. This file proves that the affine-section
functor is **fully faithful**.

This is the functor `j` of the proof of [Stacks, Tag 06ZS], and the source splits its full
faithfulness into [Stacks, Tag 021V] and its four analogues, the inclusion of sheaves of modules
into presheaves of modules, and the identification of presheaves of modules on `(Aff/U)_τ` with
module-valued functors on `Alg_A`. Here the three steps are:

* the affine-spectrum functor exhibits the `A`-algebras of the site as a **dense subsite** of the
  big site, which is Tag 021V and its four analogues transported along the anti-equivalence
  between affine schemes over `Spec A` and `A`-algebras;
* restriction of sheaves of modules along a dense subsite, twisted by an isomorphism of the
  sheaves of rings, is fully faithful — the Comparison Lemma for sheaves of modules of
  `Stacks.DenseSubsiteModules`, here at an independent module universe and for a scalar
  isomorphism rather than the identity;
* the affine-section functor **is** that restriction followed by the forgetful functor from
  sheaves of modules to presheaves of modules, which is fully faithful.

## Main definitions

* `Stacks.DenseSubsiteModules.fullyFaithfulPushforward` — restriction of sheaves of modules
  along a dense subsite together with an isomorphism of sheaves of rings is fully faithful.
* `Stacks.Adequate.affineSubsiteTopology` — the topology induced on the `A`-algebras of the
  site by the topology of the big site along the affine-spectrum functor.
* `Stacks.Adequate.affineAlgebraRingSheaf` — the tautological presheaf of rings on the
  `A`-algebras of the site, which that topology makes a sheaf.
* `Stacks.Adequate.affineRingSheafMap` — the scalar identification
  `Stacks.Adequate.affineRingMap` as an isomorphism of sheaves of rings.
* `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor` — **the main result**: the
  affine-section functor of a chosen big site over an affine base is fully faithful.

## Main results

* `Stacks.Adequate.affineSpecOver_full` and `Stacks.Adequate.affineSpecOver_faithful` — the
  affine-spectrum functor of `Spec A` over the base `Spec A` itself is fully faithful. This is
  the anti-equivalence between affine schemes over `Spec A` and `A`-algebras, `algSpec` being
  fully faithful; it is *false* over a general base `f : Spec A ⟶ S`, where a morphism of the
  site over `S` need not be a morphism over `Spec A`.
* `Stacks.Adequate.isAffine_iff_mem_essImage_affineSpecOver` — the essential image of the
  affine-spectrum functor is exactly the affine objects of the site, so that its source is
  `(Aff/U)_τ`.
* `Stacks.Adequate.coverByImage_affineSpecOver_of_isAffine` — every morphism out of an affine
  object of the site factors through an object in the image of the affine-spectrum functor,
  because an affine scheme over `Spec A` belonging to the site is the spectrum of an `A`-algebra
  belonging to the site (`AlgebraicGeometry.essImage_algSpec` together with the invariance of
  `AlgebraicGeometry.Scheme.size` under isomorphism).
* `Stacks.Adequate.exists_affineCovering_mem_topology` — every object of a chosen big site is
  covered by affine objects. This is the only step that looks at which of the five topologies
  was chosen: it is the cover-density half of the dense-subsite statement for the
  inclusion of the affine objects, namely Tag 020W, Tag 021E, Tag 021V, Tag 06VC and Tag 06VD.
* `Stacks.Adequate.affineSpecOver_isCoverDense` and
  `Stacks.Adequate.affineSpecOver_isDenseSubsite` — the dense-subsite statement for the
  affine-spectrum functor.
* `Stacks.Adequate.affineSectionsFunctor_eq` — the affine-section functor is the restriction of
  sheaves of modules along the affine-spectrum functor and the scalar identification, followed
  by the forgetful functor to presheaves of modules. This holds by definitional unfolding.

## Implementation notes

The general fully-faithfulness statement is proved here rather than in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteModules.lean` because the
statement there is at a *single* universe `w` serving both the sections of the sheaf of rings
and the sections of the modules, and for the identity morphism of sheaves of rings. Neither
specialization covers the affine-section functor: the sheaves of modules there are
`SheafOfModules.{m} B.structureSheaf` with `B.structureSheaf` a sheaf of rings in `RingCat.{u}`
and `m` independent of `u`, and the comparison of scalars is `Stacks.Adequate.affineRingMap`,
which is an isomorphism but not the identity. The proof is the same as there: restriction of
sheaves of modules and restriction of the underlying sheaves of abelian groups agree on the
nose, so faithfulness is inherited from Mathlib's
`CategoryTheory.Functor.IsDenseSubsite.faithful_sheafPushforwardContinuous`, and for fullness
the group-sheaf morphism produced by its `Full` companion has only to be shown linear, which is
checked after restricting along the cover of an object by the images of the functor. The one new
step is that linearity over the restricted sheaf of rings gives linearity over its image: a
scalar of the big site restricted to an object of the subsite is in the image of the scalar
isomorphism, so the linearity of the given morphism of modules applies to it.

The topology on the `A`-algebras of the site is `CategoryTheory.Functor.restrictedTopology`,
for which Mathlib supplies the dense-subsite instance from cover-density of a fully faithful
functor. The source instead describes `(Aff/U)_τ` by its own standard affine coverings; the two
agree because both are dense subsites of the same big site, but that identification is not
needed here and is not proved.

Full faithfulness of the affine-spectrum functor needs the base to be `Spec A` and the
structure morphism to be the identity. That is the only case the adequator uses, and the only
case in which it is true.

## References

* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 06VC](https://stacks.math.columbia.edu/tag/06VC)
* [Stacks Project, Tag 06VD](https://stacks.math.columbia.edu/tag/06VD)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

universe u m u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

/-! ### Restriction of sheaves of modules along a dense subsite and a scalar isomorphism -/

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- Restriction of sheaves of modules along `v` and `φ` is, on the underlying sheaves of
abelian groups, restriction along `v`: neither the precomposition with `v` nor the restriction
of scalars along `φ` changes the underlying abelian groups. -/
public lemma pushforward_comp_toSheaf :
    SheafOfModules.pushforward.{m} φ ⋙ SheafOfModules.toSheaf.{m} S =
      SheafOfModules.toSheaf.{m} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{m} J K := rfl

/-- Restriction of sheaves of modules along a dense subsite and a morphism of sheaves of rings
is faithful: it is restriction of the underlying sheaves of abelian groups, which is faithful on
a dense subsite. -/
public instance faithful_pushforward : (SheafOfModules.pushforward.{m} φ).Faithful := by
  have := Functor.IsDenseSubsite.isCoverDense J K v
  have := Functor.IsDenseSubsite.isLocallyFull J K v
  have : (v.sheafPushforwardContinuous AddCommGrpCat.{m} J K).Faithful := inferInstance
  exact Functor.Faithful.of_comp_eq (pushforward_comp_toSheaf J K v φ)

/-- Restriction of sheaves of modules along a dense subsite and an *isomorphism* of sheaves of
rings is full. A morphism of the restrictions is in particular a morphism of the restricted
sheaves of abelian groups, so it extends to a morphism `g` of sheaves of abelian groups on the
big site; `g` is linear because linearity is local and holds on the images of `v`, where a
scalar is the image under the scalar isomorphism of a scalar of the subsite. -/
public instance full_pushforward [IsIso φ] : (SheafOfModules.pushforward.{m} φ).Full := by
  have := Functor.IsDenseSubsite.isCoverDense J K v
  have := Functor.IsDenseSubsite.isLocallyFull J K v
  have : (v.sheafPushforwardContinuous AddCommGrpCat.{m} J K).Full := inferInstance
  have : IsIso φ.hom := (sheafToPresheaf J RingCat.{u}).map_isIso φ
  constructor
  intro M N f
  obtain ⟨g, hg⟩ := (v.sheafPushforwardContinuous AddCommGrpCat.{m} J K).map_surjective
    (X := (SheafOfModules.toSheaf.{m} R).obj M) (Y := (SheafOfModules.toSheaf.{m} R).obj N)
    ((SheafOfModules.toSheaf.{m} S).map f)
  have key : ∀ (Y : C) (x : M.val.obj (op (v.obj Y))),
      g.hom.app (op (v.obj Y)) x = f.val.app (op Y) x := by
    intro Y x
    have e := congrArg (fun p => (sheafToPresheaf J AddCommGrpCat.{m}).map p) hg
    exact CategoryTheory.congr_fun (NatTrans.congr_app e (op Y)) x
  have main : ∀ (Y : C) (r : R.obj.obj (op (v.obj Y))) (x : M.val.obj (op (v.obj Y))),
      (show N.val.obj (op (v.obj Y)) from g.hom.app (op (v.obj Y)) (r • x)) =
        r • (show N.val.obj (op (v.obj Y)) from g.hom.app (op (v.obj Y)) x) := by
    intro Y r x
    obtain ⟨s, rfl⟩ : ∃ s : S.obj.obj (op Y), (φ.hom.app (op Y)).hom s = r :=
      ⟨(inv (φ.hom.app (op Y))).hom r,
        RingHom.congr_fun
          (congrArg RingCat.Hom.hom (IsIso.inv_hom_id (φ.hom.app (op Y)))) r⟩
    refine (key Y _).trans (Eq.trans ((f.val.app (op Y)).hom.map_smul s
      (show ((SheafOfModules.pushforward.{m} φ).obj M).val.obj (op Y) from x)) ?_)
    congr 1
    exact (key Y x).symm
  refine ⟨⟨PresheafOfModules.homMk g.hom ?_⟩, ?_⟩
  · rintro ⟨X⟩ r y
    refine Functor.IsCoverDense.ext (K := K) v
      ((sheafCompose K (forget AddCommGrpCat.{m})).obj
        ((SheafOfModules.toSheaf.{m} R).obj N)) X (fun {Y} hY ↦ ?_)
    have nat : ∀ (x : M.val.obj (op X)),
        N.val.map hY.op (g.hom.app (op X) x) =
          g.hom.app (op (v.obj Y)) (M.val.map hY.op x) := fun x ↦
      (CategoryTheory.congr_fun (g.hom.naturality hY.op) x).symm
    refine (nat (r • y)).trans
      (Eq.trans ?_ (N.val.map_smul hY.op r (g.hom.app (op X) y)).symm)
    rw [M.val.map_smul]
    refine (main Y _ _).trans ?_
    congr 1
    exact (nat y).symm
  · apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Y
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x ↦ key Y.unop x)

/-- **The Comparison Lemma for sheaves of modules, in the form the affine-section functor
needs.** If `v` exhibits `(C, J)` as a dense subsite of `(C', K)` and `φ` is an isomorphism from
a sheaf of rings on `(C, J)` to the restriction of a sheaf of rings `R` on `(C', K)`, then
restriction of sections along `v` and of scalars along `φ` is fully faithful from sheaves of
`R`-modules to sheaves of modules over the source of `φ`. -/
public noncomputable def fullyFaithfulPushforward [IsIso φ] :
    (SheafOfModules.pushforward.{m} φ).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end Pushforward

end Stacks.DenseSubsiteModules

namespace Stacks.Adequate

/-! ### The affine-spectrum functor is fully faithful over an affine base -/

section FullyFaithful

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The affine-spectrum functor of `Spec A` over the base `Spec A`, composed with the canonical
functor to the schemes over `Spec A`: taking spectra of the `A`-algebras of the site. -/
private noncomputable abbrev affineSpecOverToOver :
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ ⥤
      Over (Spec A) :=
  (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)).op ⋙
    algSpec A ⋙ Over.map (𝟙 (Spec A))

/-- Taking spectra of the `A`-algebras of the site is faithful, `algSpec` being faithful. -/
private instance : (affineSpecOverToOver B).Faithful := by
  have : ((AdequateFunctor.siteAlgebraInclusion (A : Type u)
    (schemeSizeBelow B.cutoff)).op).Faithful := inferInstance
  infer_instance

/-- Taking spectra of the `A`-algebras of the site is full, `algSpec` being full. -/
private instance : (affineSpecOverToOver B).Full := by
  have : ((AdequateFunctor.siteAlgebraInclusion (A : Type u)
    (schemeSizeBelow B.cutoff)).op).Full := inferInstance
  infer_instance

/-- The affine-spectrum functor of a chosen big site over `Spec A`, for the identity structure
morphism, is faithful: a morphism of the site over `Spec A` between spectra of `A`-algebras is a
morphism of affine schemes over `Spec A`, and `algSpec` is faithful. -/
public instance affineSpecOver_faithful :
    (affineSpecOver B A (𝟙 (Spec A))).Faithful where
  map_injective {X Y} f g h := by
    apply (affineSpecOverToOver B).map_injective
    apply Over.OverMorphism.ext
    exact congrArg
      (fun (p : (affineSpecOver B A (𝟙 (Spec A))).obj X ⟶
        (affineSpecOver B A (𝟙 (Spec A))).obj Y) => p.left.hom) h

/-- The affine-spectrum functor of a chosen big site over `Spec A`, for the identity structure
morphism, is full: a morphism of the site over `Spec A` between the spectra of two `A`-algebras
commutes with the structure morphisms to `Spec A`, hence is a morphism of affine schemes over
`Spec A`, and `algSpec` is full. -/
public instance affineSpecOver_full : (affineSpecOver B A (𝟙 (Spec A))).Full where
  map_surjective {X Y} φ := by
    have hw : φ.left.hom ≫ ((affineSpecOverToOver B).obj Y).hom =
        ((affineSpecOverToOver B).obj X).hom :=
      congrArg (fun (p : _ ⟶ (⟨Spec A, B.base_mem⟩ : SchemeBelow B.cutoff)) => p.hom)
        (Over.w φ)
    obtain ⟨g, hg⟩ := (affineSpecOverToOver B).map_surjective (Over.homMk φ.left.hom hw)
    refine ⟨g, ?_⟩
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change ((affineSpecOverToOver B).map g).left = φ.left.hom
    rw [hg]
    rfl

/-! ### The affine objects of the site are a dense subsite -/

/-- The objects of a chosen big site over `Spec A` in the essential image of the affine-spectrum
functor are exactly its affine objects. An affine scheme over `Spec A` is the spectrum of an
`A`-algebra by `AlgebraicGeometry.essImage_algSpec`, and that algebra is an algebra of the site
because `AlgebraicGeometry.Scheme.size` is invariant under isomorphism; conversely a spectrum is
affine. -/
public theorem isAffine_iff_mem_essImage_affineSpecOver (X : B.category) :
    IsAffine X.left.obj ↔ (affineSpecOver B A (𝟙 (Spec A))).essImage X := by
  constructor
  · intro hX
    obtain ⟨R₀, ⟨e⟩⟩ := (essImage_algSpec (G := B.toOver.obj X)).mpr hX
    have hsize : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (R₀.unop : Type u))) :=
      (Scheme.size_congr ((Over.forget (Spec A)).mapIso e)).trans_lt X.left.property
    refine ⟨op ⟨R₀.unop, hsize⟩, ⟨?_⟩⟩
    refine Over.isoMk (ObjectProperty.isoMk _ ((Over.forget (Spec A)).mapIso e)) ?_
    apply ObjectProperty.hom_ext
    exact (Over.w e.hom).trans (Category.comp_id _).symm
  · rintro ⟨Z, ⟨e⟩⟩
    have : IsAffine ((ObjectProperty.ι _).obj
        ((Over.forget _).obj ((affineSpecOver B A (𝟙 (Spec A))).obj Z))) :=
      inferInstanceAs (IsAffine (Spec _))
    exact IsAffine.of_isIso ((ObjectProperty.ι _).mapIso ((Over.forget _).mapIso e)).inv

/-- A morphism out of an affine object of a chosen big site over `Spec A` factors through an
object in the image of the affine-spectrum functor: an affine scheme over `Spec A` is the
spectrum of an `A`-algebra by `AlgebraicGeometry.essImage_algSpec`, and that algebra belongs to
the site because `AlgebraicGeometry.Scheme.size` is invariant under isomorphism. -/
public theorem coverByImage_affineSpecOver_of_isAffine {W X : B.category}
    (hW : IsAffine W.left.obj) (h : W ⟶ X) :
    Presieve.coverByImage (affineSpecOver B A (𝟙 (Spec A))) X h := by
  obtain ⟨Z, ⟨e⟩⟩ := (isAffine_iff_mem_essImage_affineSpecOver B W).mp hW
  exact ⟨⟨Z, e.inv, e.hom ≫ h, e.inv_hom_id_assoc h⟩⟩

/-- If `w` is a dense subsite and every object in its image has property `Q`, then every object
of the target has a covering sieve all of whose morphisms factor through an object with `Q`. -/
private theorem exists_covering_factor_of_isCoverDense {D : Type u₁} [Category.{v₁} D]
    {D' : Type u₂} [Category.{v₂} D'] (w : D ⥤ D') (J : GrothendieckTopology D)
    (K : GrothendieckTopology D') [w.IsDenseSubsite J K] (Q : D' → Prop) (hw : ∀ V : D, Q (w.obj V))
    (X : D') :
    ∃ T ∈ K X, ∀ ⦃Y : D'⦄ (f : Y ⟶ X), (T : Sieve X).arrows f →
      ∃ (W : D') (g : Y ⟶ W) (h : W ⟶ X), Q W ∧ g ≫ h = f :=
  ⟨Sieve.coverByImage w X, (IsDenseSubsite.isCoverDense J K w).is_cover X,
    fun {_} _ ⟨⟨V, lift, h, fac⟩⟩ ↦ ⟨w.obj V, lift, h, hw V, fac⟩⟩

/-- Every object of a chosen big site over `S` admits a covering sieve all of whose morphisms
factor through an affine object of the site. This is the cover-density half of the
dense-subsite statement for the inclusion of the affine objects, one for each of the five
topologies: [Stacks, Tags 020W, 021E, 021V, 06VC and 06VD]. It is the only step of the full
faithfulness of the affine-section functor that looks at `Stacks.Adequate.BigSite.chosen`. -/
public theorem exists_affineCovering_mem_topology {S : Scheme.{u}} (B : BigSite τ S)
    (X : B.category) :
    ∃ T ∈ B.topology X, ∀ ⦃Y : B.category⦄ (f : Y ⟶ X), (T : Sieve X).arrows f →
      ∃ (W : B.category) (g : Y ⟶ W) (h : W ⟶ X),
        IsAffine W.left.obj ∧ g ≫ h = f := by
  rcases B with ⟨cutoff, base_mem, top, hsh, chosen⟩
  rcases chosen with ⟨-, B', hS', he, hheq⟩ | ⟨-, B', hS', he, hheq⟩ |
    ⟨-, B', hS', he, hheq⟩ | ⟨-, B', hS', he, hheq⟩ | ⟨-, B', hS', he, hheq⟩
  · subst he
    obtain rfl : top = BigZariskiOver.topology B' S hS' := eq_of_heq hheq
    exact exists_covering_factor_of_isCoverDense (BigAffineZariski.inclusion B' S hS')
      (BigAffineZariski.topology B' S hS') (BigZariskiOver.topology B' S hS')
      (fun W => IsAffine W.left.obj) (fun V => V.property) X
  · subst he
    obtain rfl : top = BigEtaleOver.topology B' S hS' := eq_of_heq hheq
    exact exists_covering_factor_of_isCoverDense (BigAffineEtale.inclusion B' S hS')
      (BigAffineEtale.topology B' S hS') (BigEtaleOver.topology B' S hS')
      (fun W => IsAffine W.left.obj) (fun V => V.property) X
  · subst he
    obtain rfl : top = BigFppfOver.topology B' S hS' := eq_of_heq hheq
    exact exists_covering_factor_of_isCoverDense (BigAffineFppf.inclusion B' S hS')
      (BigAffineFppf.topology B' S hS') (BigFppfOver.topology B' S hS')
      (fun W => IsAffine W.left.obj) (fun V => V.property) X
  · subst he
    obtain rfl : top = BigSmoothOver.topology B' S hS' := eq_of_heq hheq
    exact exists_covering_factor_of_isCoverDense (BigAffineSmooth.inclusion B' S hS')
      (BigAffineSmooth.topology B' S hS') (BigSmoothOver.topology B' S hS')
      (fun W => IsAffine W.left.obj) (fun V => V.property) X
  · subst he
    obtain rfl : top = BigSyntomicOver.topology B' S hS' := eq_of_heq hheq
    exact exists_covering_factor_of_isCoverDense (BigAffineSyntomic.inclusion B' S hS')
      (BigAffineSyntomic.topology B' S hS') (BigSyntomicOver.topology B' S hS')
      (fun W => IsAffine W.left.obj) (fun V => V.property) X

/-- The affine-spectrum functor of a chosen big site over `Spec A` is cover-dense: every object
is covered by affine objects, and every affine object of the site receives an isomorphism from
the spectrum of an `A`-algebra of the site. -/
public instance affineSpecOver_isCoverDense :
    (affineSpecOver B A (𝟙 (Spec A))).IsCoverDense B.topology where
  is_cover X := by
    obtain ⟨T, hT, hfac⟩ := exists_affineCovering_mem_topology B X
    refine B.topology.superset_covering ?_ hT
    intro Y f hf
    obtain ⟨W, g, h, hW, rfl⟩ := hfac f hf
    exact (Sieve.coverByImage (affineSpecOver B A (𝟙 (Spec A))) X).downward_closed
      (coverByImage_affineSpecOver_of_isAffine B hW h) g

/-- The topology induced on the `A`-algebras of a chosen big site over `Spec A` by the topology
of the site: a sieve covers exactly when its image generates a covering sieve of the site. -/
public noncomputable abbrev affineSubsiteTopology : GrothendieckTopology
    (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ :=
  (affineSpecOver B A (𝟙 (Spec A))).restrictedTopology B.topology

/-- **The `A`-algebras of a chosen big site over `Spec A` are a dense subsite.** This is
[Stacks, Tag 021V] and its four analogues, transported from the affine objects of the site to
the `A`-algebras of the site along the anti-equivalence of affine schemes over `Spec A` with
`A`-algebras. -/
public instance affineSpecOver_isDenseSubsite :
    (affineSpecOver B A (𝟙 (Spec A))).IsDenseSubsite (affineSubsiteTopology B) B.topology :=
  inferInstance

/-! ### The affine-section functor -/

/-- The tautological presheaf of rings on the `A`-algebras of the site is a sheaf for the
induced topology: the scalar identification `Stacks.Adequate.affineRingMap` identifies it with
the restriction of the structure sheaf of the big site, and the affine-spectrum functor is
continuous. -/
public theorem isSheaf_algebraRingDiagramOn :
    Presheaf.IsSheaf (affineSubsiteTopology B)
      (AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff))) :=
  (Presheaf.isSheaf_of_iso_iff (asIso (affineRingMap B A (𝟙 (Spec A))))).mpr
    ((affineSpecOver B A (𝟙 (Spec A))).op_comp_isSheaf_of_isSheaf (affineSubsiteTopology B)
      B.topology B.structureSheaf.obj B.isSheaf)

/-- The sheaf of rings of the `A`-algebras of the site: the tautological presheaf of rings,
which is a sheaf for the induced topology. The module-valued functors on the `A`-algebras of the
site are the presheaves of modules over it. -/
public noncomputable abbrev affineAlgebraRingSheaf : Sheaf (affineSubsiteTopology B) RingCat.{u} :=
  ⟨AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)),
    isSheaf_algebraRingDiagramOn B⟩

/-- The scalar identification `Stacks.Adequate.affineRingMap` as a morphism of sheaves of rings
from the tautological sheaf of rings on the `A`-algebras of the site to the restriction of the
structure sheaf of the big site. -/
public noncomputable abbrev affineRingSheafMap : affineAlgebraRingSheaf B ⟶
    ((affineSpecOver B A (𝟙 (Spec A))).sheafPushforwardContinuous RingCat.{u}
      (affineSubsiteTopology B) B.topology).obj B.structureSheaf :=
  ⟨affineRingMap B A (𝟙 (Spec A))⟩

/-- The scalar identification is an isomorphism of sheaves of rings: it is one on the underlying
presheaves of rings by `Stacks.Adequate.affineRingMap_isIso`, and the forgetful functor from
sheaves to presheaves reflects isomorphisms. -/
public instance affineRingSheafMap_isIso : IsIso (affineRingSheafMap B) := by
  have : IsIso ((sheafToPresheaf (affineSubsiteTopology B) RingCat.{u}).map
      (affineRingSheafMap B)) := by
    change IsIso (affineRingMap B A (𝟙 (Spec A)))
    infer_instance
  exact isIso_of_reflects_iso (affineRingSheafMap B)
    (sheafToPresheaf (affineSubsiteTopology B) RingCat.{u})

/-- The affine-section functor is restriction of sheaves of modules along the affine-spectrum
functor and the scalar identification, followed by the forgetful functor from sheaves of modules
to presheaves of modules. Both sides forget the sheaf condition and push forward along
`Stacks.Adequate.affineRingMap`, so this holds by definitional unfolding. -/
public theorem affineSectionsFunctor_eq :
    affineSectionsFunctor.{u, m} B A (𝟙 (Spec A)) =
      SheafOfModules.pushforward.{m} (affineRingSheafMap B) ⋙
        SheafOfModules.forget (affineAlgebraRingSheaf B) := rfl

/-- **The affine-section functor of a chosen big site over an affine base is fully faithful.**
This is full faithfulness of the functor `j` in the proof of [Stacks, Tag 06ZS]: the
`A`-algebras of the site are a dense subsite, so restriction of sheaves of modules along the
affine-spectrum functor and the scalar identification is fully faithful, and the forgetful
functor to presheaves of modules is fully faithful. -/
public noncomputable def fullyFaithfulAffineSectionsFunctor :
    (affineSectionsFunctor.{u, m} B A (𝟙 (Spec A))).FullyFaithful :=
  (Stacks.DenseSubsiteModules.fullyFaithfulPushforward (affineSubsiteTopology B)
      B.topology (affineSpecOver B A (𝟙 (Spec A))) (affineRingSheafMap B)).comp
    (SheafOfModules.fullyFaithfulForget (affineAlgebraRingSheaf B))

end FullyFaithful

end Stacks.Adequate

end
