module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement

/-!
# Right derived functors on the unbounded derived category

The functorial K-injective resolutions of [Stacks, Tag 079P] exhibit the inclusion of the
K-injective cochain complexes into all cochain complexes as a right derivability structure
for the quasi-isomorphisms.  Consequently every functor out of `CochainComplex C ℤ` which
inverts the quasi-isomorphisms between K-injective complexes has a right derived functor on
the whole unbounded derived category, and that derived functor is recognised by its unit
being invertible on K-injective complexes.

## Main definitions

* `Stacks.Injectives.KInjectiveResolution.isKInjectiveProperty` is the object property of being
  K-injective, and `Stacks.Injectives.KInjectiveResolution.kInjectiveLocalizerMorphism` the
  inclusion of the corresponding full subcategory, viewed as a morphism of localizers.
* `Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective` is the hypothesis under
  which a functor out of unbounded cochain complexes acquires a right derived functor.

## Main results

* `Stacks.Injectives.KInjectiveResolution.isRightDerivabilityStructure_kInjective`: the inclusion
  of the K-injective complexes is a right derivability structure.
* `Stacks.Injectives.KInjectiveResolution.hasPointwiseRightDerivedFunctor_of_isKInjective` and
  `Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_of_isKInjective`: existence of the
  derived functor.
* `Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`: a
  candidate is the derived functor exactly when its unit is invertible on K-injective complexes.
* `Stacks.Injectives.KInjectiveResolution.isIso_app_of_quasiIso_resolution`: the unit is also
  invertible at a complex which is not K-injective, as soon as the underived functor already
  inverts a K-injective resolution of it.
* `Stacks.Injectives.KInjectiveResolution.isIso_of_isIso_app_quotient_isKInjective` and
  `Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`:
  the same recognition for a functor on the homotopy category `K(A)`, which is the form
  [Stacks, Tag 070K] is stated in.
* `hasPointwiseRightDerivedFunctor_mapHomologicalComplex_comp_Q`: the case of an
  additive functor followed by the localization to the derived category, which is the shape
  in which derived sections and derived global sections occur.

## Implementation notes

The construction is Spaltenstein's, in the abstract form Mathlib gives it: a fully faithful
functor together with a functorial resolution against a multiplicative class with the
two-out-of-three property is a right derivability structure
(`CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions`).
Nothing here is bounded below, and no exactness of countable products (AB4*) is assumed:
the only input is the unconditional functorial resolution of
`Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective`.

The passage from a quasi-isomorphism between K-injective complexes to an isomorphism after
applying an additive functor goes through homotopy equivalences
(`CochainComplex.IsKInjective.quasiIso_iff`), which additive functors preserve.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u v' u' v'' u''

namespace Stacks.Injectives.KInjectiveResolution

section

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The property of a cochain complex of being K-injective. -/
def isKInjectiveProperty : ObjectProperty (CochainComplex C ℤ) :=
  fun K => K.IsKInjective

/-- The full subcategory of K-injective cochain complexes. -/
abbrev KInjectiveComplex : Type (max u v) := (isKInjectiveProperty C).FullSubcategory

/-- The inclusion of the K-injective cochain complexes, as a morphism of localizers from
the class of quasi-isomorphisms it reflects to the quasi-isomorphisms of cochain
complexes. -/
def kInjectiveLocalizerMorphism :
    LocalizerMorphism
      ((HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage
        (isKInjectiveProperty C).ι)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) where
  functor := (isKInjectiveProperty C).ι
  map := le_refl _

/-- The functor of `kInjectiveLocalizerMorphism C` is full. -/
instance : (kInjectiveLocalizerMorphism C).functor.Full :=
  inferInstanceAs ((isKInjectiveProperty C).ι).Full

/-- The functor of `kInjectiveLocalizerMorphism C` is faithful. -/
instance : (kInjectiveLocalizerMorphism C).functor.Faithful :=
  inferInstanceAs ((isKInjectiveProperty C).ι).Faithful

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The resolution functor of a functorial K-injective resolution, regarded as landing in
the full subcategory of K-injective complexes. -/
def kInjectiveResolutionFunctor (NR : FunctorialKInjectiveResolution C) :
    CochainComplex C ℤ ⥤ KInjectiveComplex C :=
  (isKInjectiveProperty C).lift NR.functor NR.isKInjective

/-- The unit of a functorial K-injective resolution, regarded as a natural transformation
to the composite of the resolution functor with the inclusion. -/
def kInjectiveResolutionUnit (NR : FunctorialKInjectiveResolution C) :
    Functor.id (CochainComplex C ℤ) ⟶
      kInjectiveResolutionFunctor NR ⋙ (kInjectiveLocalizerMorphism C).functor where
  app M := NR.inclusion.app M
  naturality _ _ f := NR.inclusion.naturality f

/-- Each component of `kInjectiveResolutionUnit NR` is a quasi-isomorphism. -/
lemma quasiIso_kInjectiveResolutionUnit_app (NR : FunctorialKInjectiveResolution C)
    (M : CochainComplex C ℤ) :
    HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
      ((kInjectiveResolutionUnit NR).app M) :=
  (HomologicalComplex.mem_quasiIso_iff _).2 (NR.quasiIso M)

end

section

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **Spaltenstein's theorem.**  In a Grothendieck abelian category the inclusion of the
K-injective cochain complexes into all cochain complexes is a right derivability structure
for the quasi-isomorphisms.

The functorial resolutions of [Stacks, Tag 079P] are the only input; in particular no
boundedness and no exactness of countable products is assumed. -/
theorem isRightDerivabilityStructure_kInjective :
    (kInjectiveLocalizerMorphism C).IsRightDerivabilityStructure :=
  LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions _
    (kInjectiveResolutionUnit
      (Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective C).some)
    (quasiIso_kInjectiveResolutionUnit_app _) rfl

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] {H : Type u'} [Category.{v'} H]

/-- The hypothesis under which a functor out of unbounded cochain complexes acquires a
right derived functor: it inverts the quasi-isomorphisms between K-injective complexes. -/
def InvertsQuasiIsoOfIsKInjective (F : CochainComplex C ℤ ⥤ H) : Prop :=
  ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L),
    K.IsKInjective → L.IsKInjective → QuasiIso f → IsIso (F.map f)

variable {F : CochainComplex C ℤ ⥤ H} [IsGrothendieckAbelian.{w} C]

omit [IsGrothendieckAbelian.{w} C] in
/-- A functor which inverts the quasi-isomorphisms between K-injective complexes is derived by
`kInjectiveLocalizerMorphism C`, that is, it inverts the quasi-isomorphisms of the full
subcategory of K-injective complexes. -/
lemma derives_kInjectiveLocalizerMorphism (hF : InvertsQuasiIsoOfIsKInjective F) :
    (kInjectiveLocalizerMorphism C).Derives F := by
  intro K L f hf
  exact hF ((isKInjectiveProperty C).ι.map f) K.property L.property
    ((HomologicalComplex.mem_quasiIso_iff _).1 hf)

/-- **The unbounded right derived functor exists, pointwise.**  A functor out of the
unbounded cochain complexes of a Grothendieck abelian category which inverts the
quasi-isomorphisms between K-injective complexes has a pointwise right derived functor with
respect to all quasi-isomorphisms. -/
@[sga "4 XVII 4.1.2" "partial"]
theorem hasPointwiseRightDerivedFunctor_of_isKInjective
    (hF : InvertsQuasiIsoOfIsKInjective F) :
    F.HasPointwiseRightDerivedFunctor (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  have := isRightDerivabilityStructure_kInjective C
  (derives_kInjectiveLocalizerMorphism hF).hasPointwiseRightDerivedFunctor

/-- **The unbounded right derived functor exists.** -/
theorem hasRightDerivedFunctor_of_isKInjective (hF : InvertsQuasiIsoOfIsKInjective F) :
    F.HasRightDerivedFunctor (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_of_isKInjective hF
  inferInstance

variable {D : Type u''} [Category.{v''} D] (L : CochainComplex C ℤ ⥤ D)
  [L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]
  (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)

/-- **K-injective complexes compute the right derived functor.**  A candidate `(RF, α)` is
the right derived functor of `F` precisely when the unit `α` is invertible at every
K-injective complex. -/
theorem isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    (hF : InvertsQuasiIsoOfIsKInjective F) :
    RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ↔
      ∀ (K : CochainComplex C ℤ), K.IsKInjective → IsIso (α.app K) :=
  have := isRightDerivabilityStructure_kInjective C
  ((derives_kInjectiveLocalizerMorphism hF).isRightDerivedFunctor_iff_isIso α).trans
    ⟨fun h K hK => h ⟨K, hK⟩, fun h K => h K.obj K.property⟩

/-- The unit of the right derived functor is invertible at every K-injective complex. -/
theorem isIso_app_of_isKInjective (hF : InvertsQuasiIsoOfIsKInjective F)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]
    (K : CochainComplex C ℤ) (hK : K.IsKInjective) : IsIso (α.app K) :=
  (isRightDerivedFunctor_iff_isIso_app_of_isKInjective L RF α hF).1 ‹_› K hK

/-- **The unit of a right derived functor is invertible at a complex whose K-injective
resolution the underived functor already inverts.**  Only two of the three maps in the naturality
square of `α` at `q` need be known: the unit at the K-injective end is invertible by
`Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective`, the localization of a
quasi-isomorphism is invertible, and the fourth map is the hypothesis.

This is the criterion that applies when the complex at hand is *not* K-injective but is still
computed by the derived functor, which is the situation of [Stacks, Tag 0D6J]. -/
theorem isIso_app_of_quasiIso_resolution (hF : InvertsQuasiIsoOfIsKInjective F)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]
    {Z I : CochainComplex C ℤ} (q : Z ⟶ I) (hI : I.IsKInjective) (hq : QuasiIso q)
    (hFq : IsIso (F.map q)) : IsIso (α.app Z) := by
  have h₁ := isIso_app_of_isKInjective L RF α hF I hI
  have h₂ : IsIso (L.map q) :=
    Localization.inverts L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ hq
  have h₃ : IsIso ((L ⋙ RF).map q) := inferInstanceAs (IsIso (RF.map (L.map q)))
  have h₄ : IsIso (α.app Z ≫ (L ⋙ RF).map q) := by
    rw [← α.naturality q]
    have := hFq
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((L ⋙ RF).map q)

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] {A : Type u'} [Category.{v'} A] [Abelian A]

/-- An additive functor sends a quasi-isomorphism between K-injective cochain complexes to
a homotopy equivalence, hence to a quasi-isomorphism. -/
lemma quasiIso_mapHomologicalComplex_map_of_isKInjective (G : C ⥤ A) [G.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (hK : K.IsKInjective) (hL : L.IsKInjective)
    (hf : QuasiIso f) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).1 hf
  rw [← HomologicalComplex.mem_quasiIso_iff]
  exact homotopyEquivalences_le_quasiIso A (ComplexShape.up ℤ) _
    (G.mapHomotopyEquiv e).homotopyEquivalences_hom

variable [HasDerivedCategory.{w'} A] [IsGrothendieckAbelian.{w} C]

omit [IsGrothendieckAbelian.{w} C] in
/-- The degreewise extension of an additive functor, followed by the localization to the derived
category, inverts the quasi-isomorphisms between K-injective complexes. -/
theorem invertsQuasiIso_mapHomologicalComplex_comp_Q (G : C ⥤ A) [G.Additive] :
    InvertsQuasiIsoOfIsKInjective
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  intro K L f hK hL hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_mapHomologicalComplex_map_of_isKInjective G f hK hL hf)

/-- **The right derived functor of an additive functor on the unbounded derived category.**
For an additive functor `G : C ⥤ A` out of a Grothendieck abelian category, the degreewise
extension of `G` followed by the localization of `A`-cochain complexes to `D(A)` has a
pointwise right derived functor on the whole unbounded derived category of `C`. -/
@[sga "4 XVII 4.1.2" "partial"]
theorem hasPointwiseRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (G : C ⥤ A) [G.Additive] :
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q).HasPointwiseRightDerivedFunctor
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  hasPointwiseRightDerivedFunctor_of_isKInjective
    (invertsQuasiIso_mapHomologicalComplex_comp_Q G)

/-- **The right derived functor of an additive functor on the unbounded derived category**,
existence form. -/
@[sga "4 XVII 4.1.2" "partial"]
theorem hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (G : C ⥤ A) [G.Additive] :
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_mapHomologicalComplex_comp_Q G
  inferInstance

end

/-! ### The criterion on the homotopy category -/

section HomotopyCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {H : Type u'} [Category.{v'} H]

/-- **A natural transformation of functors on the derived category is invertible as soon as it
is invertible at the K-injective complexes.**  Every object of `D(A)` is isomorphic to the image
of a K-injective complex, because `DerivedCategory.Qh` is a localization and the K-injective
resolution of a complex is a quasi-isomorphism. -/
theorem isIso_of_isIso_app_quotient_isKInjective
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {R S : DerivedCategory A ⥤ H} (τ : R ⟶ S)
    (hτ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    IsIso τ := by
  have := Localization.essSurj DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  refine (NatTrans.isIso_iff_isIso_app _).2 fun E => ?_
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Qh E
  refine (τ.isIso_app_iff_of_iso e).1 ?_
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, t, hI, ht⟩ := hA K
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).2 ht)
  exact (τ.isIso_app_iff_of_iso (asIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)))).2 (hτ I hI)

/-- **K-injective complexes recognise the right derived functor of a functor on the homotopy
category.**  A candidate `(R, α)` for the right derived functor of
`F : K(A) ⥤ H` along `DerivedCategory.Qh` is the right derived functor as soon as `α` is
invertible at the image of every K-injective complex.

This is the converse of the second conclusion of [Stacks, Tag 070K], which is
`CategoryTheory.Functor`'s
`hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`,
and `Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`
is the same statement for a functor on `CochainComplex A ℤ`.  Both directions are needed when a
derived functor is *constructed* -- for instance by composing a known derived functor with an
exact functor -- rather than obtained from the universal property. -/
theorem isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (R : DerivedCategory A ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ R)
    (hα : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have h := F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective hA
  have : F.HasPointwiseRightDerivedFunctor W := h.1
  have : F.HasRightDerivedFunctor W :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor F W
  refine (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (F.totalRightDerived DerivedCategory.Qh W)
    (F.totalRightDerivedUnit DerivedCategory.Qh W) W R α).2
    (isIso_of_isIso_app_quotient_isKInjective hA _ fun I hI => ?_)
  have := h.2 DerivedCategory.Qh (F.totalRightDerived DerivedCategory.Qh W)
    (F.totalRightDerivedUnit DerivedCategory.Qh W) I hI
  have := hα I hI
  have hfac : IsIso ((F.totalRightDerivedUnit DerivedCategory.Qh W).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
    (Functor.rightDerivedDesc (F.totalRightDerived DerivedCategory.Qh W)
        (F.totalRightDerivedUnit DerivedCategory.Qh W) W R α).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := by
    rw [Functor.rightDerived_fac_app]
    infer_instance
  exact IsIso.of_isIso_comp_left ((F.totalRightDerivedUnit DerivedCategory.Qh W).app
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) _

end HomotopyCategory

end Stacks.Injectives.KInjectiveResolution
