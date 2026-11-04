module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.DerivedCategory.CountableCoproducts

/-!
# Homotopy and derived categories of a product decomposition

Let `A` be an additive category and `(F i : A ⥤ B i)` a family of additive functors which
together identify `A` with the product `∏ i, B i`, that is, such that `Functor.pi' F` is an
equivalence. The index type is arbitrary. Then complexes, homotopies and homotopy classes of
maps in `A` are the same as families of such in the `B i`, so the induced functor
`K(A) ⥤ ∏ i, K(B i)` is an equivalence. When moreover `A` and the `B i` are abelian and the
`F i` are exact, a map of complexes in `A` is a quasi-isomorphism exactly when each of its
images is, and the left calculus of fractions of the quasi-isomorphisms in the homotopy
categories shows that `∏ i, D(B i)` is the localization of `∏ i, K(B i)` at the families of
quasi-isomorphisms. Hence the induced functor `D(A) ⥤ ∏ i, D(B i)` is an equivalence.

## Main results

* `CategoryTheory.Functor.isEquivalence_pi'_mapHomotopyCategory`: the functor
  `K(A) ⥤ ∏ i, K(B i)` induced by a product decomposition is an equivalence.
* `CategoryTheory.Functor.quasiIso_iff_forall_map`: a map of the homotopy category of `A` is a
  quasi-isomorphism if and only if each of its images is.
* `CategoryTheory.Functor.isEquivalence_pi'_mapDerivedCategory`: the functor
  `D(A) ⥤ ∏ i, D(B i)` induced by a product decomposition by exact functors is an equivalence.

## Implementation notes

The product `∏ i, B i` carries no preadditive or abelian structure here, so complexes are never
formed in it: a family of complexes is assembled into a complex of `A` through the full,
faithful and essentially surjective functor `Functor.pi' F`, one degree and one differential at
a time, and a family of homotopies likewise. For a finite index type the derived statement
would follow from `CategoryTheory.Functor.IsLocalization.pi`; for an arbitrary one the
localization of the product is
`Stacks.MappingTelescope.functorPi_isLocalization_of_leftCoF`, which uses the left calculus of
fractions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w vA uA vB uB

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] {ι : Type w} {B : ι → Type uB}
  [∀ i, Category.{vB} (B i)] (F : ∀ i, A ⥤ B i)

section Preimage

variable [(Functor.pi' F).IsEquivalence]

/-- The map `X ⟶ Y` of `A` with prescribed images `f i` under every `F i`, along a product
decomposition `Functor.pi' F`. -/
def piPreimage {X Y : A} (f : ∀ i, (F i).obj X ⟶ (F i).obj Y) : X ⟶ Y :=
  (Functor.pi' F).preimage (show (Functor.pi' F).obj X ⟶ (Functor.pi' F).obj Y from f)

/-- The image of `piPreimage F f` under `F i` is `f i`. -/
@[simp]
theorem map_piPreimage {X Y : A} (f : ∀ i, (F i).obj X ⟶ (F i).obj Y) (i : ι) :
    (F i).map (piPreimage F f) = f i :=
  congrFun ((Functor.pi' F).map_preimage
    (show (Functor.pi' F).obj X ⟶ (Functor.pi' F).obj Y from f)) i

/-- Maps of `A` are determined by their images under all the `F i`. -/
theorem pi_hom_ext {X Y : A} {f g : X ⟶ Y} (h : ∀ i, (F i).map f = (F i).map g) : f = g :=
  (Functor.pi' F).map_injective (funext h)

/-- A map `f : X ⟶ X'` is the comparison `s ≫ s'⁻¹` of two isomorphisms `s : X ≅ Y`,
`s' : X' ≅ Y` exactly when it is compatible with componentwise identifications through which
`s` and `s'` are described. -/
theorem eq_comp_inv_iff_pi {X X' Y : A} (s : X ≅ Y) (s' : X' ≅ Y) {Z : ∀ i, B i}
    (σ : ∀ i, (F i).obj X ≅ Z i) (σ' : ∀ i, (F i).obj X' ≅ Z i) (ε : ∀ i, (F i).obj Y ≅ Z i)
    (hs : ∀ i, (F i).map s.hom = (σ i).hom ≫ (ε i).inv)
    (hs' : ∀ i, (F i).map s'.hom = (σ' i).hom ≫ (ε i).inv) (f : X ⟶ X') :
    f = s.hom ≫ s'.inv ↔ ∀ i, (F i).map f ≫ (σ' i).hom = (σ i).hom := by
  have key : ∀ i, (F i).map (s.hom ≫ s'.inv) ≫ (σ' i).hom = (σ i).hom := fun i => by
    have h' : (F i).map s'.inv = (ε i).hom ≫ (σ' i).inv := by
      rw [← cancel_epi ((F i).map s'.hom), ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
        hs']
      simp
    rw [Functor.map_comp, hs, h']
    simp
  constructor
  · rintro rfl i
    exact key i
  · intro h
    refine pi_hom_ext F fun i => ?_
    rw [← cancel_mono (σ' i).hom, h i, key i]

/-- The `i`-th component of the object of `A` with prescribed images `Y i`. -/
def piObjIso (Y : ∀ i, B i) (i : ι) : (F i).obj ((Functor.pi' F).objPreimage Y) ≅ Y i :=
  Pi.isoApp ((Functor.pi' F).objObjPreimageIso Y) i

end Preimage

section Homotopy

variable [Preadditive A] [∀ i, Preadditive (B i)] [∀ i, (F i).Additive]
  {β : Type*} (c : ComplexShape β)

/-- A family of complexes of the `B i` assembled into one complex of `A`, along a product
decomposition `Functor.pi' F`. -/
def piAssembleComplex [(Functor.pi' F).IsEquivalence]
    (C : ∀ i, HomologicalComplex (B i) c) : HomologicalComplex A c where
  X p := (Functor.pi' F).objPreimage fun i => (C i).X p
  d p q := piPreimage F fun i =>
    (piObjIso F (fun i => (C i).X p) i).hom ≫ (C i).d p q ≫
      (piObjIso F (fun i => (C i).X q) i).inv
  shape p q h := pi_hom_ext F fun i => by simp [(C i).shape p q h]
  d_comp_d' p q r _ _ := pi_hom_ext F fun i => by simp

/-- The degree-`p` term of the assembled complex, read through `F i`. -/
def piAssembleComplexXIso [(Functor.pi' F).IsEquivalence]
    (C : ∀ i, HomologicalComplex (B i) c) (i : ι) (p : β) :
    (F i).obj ((piAssembleComplex F c C).X p) ≅ (C i).X p :=
  piObjIso F (fun i => (C i).X p) i

/-- The image under `F i` of a differential of the assembled complex is the corresponding
differential of the `i`-th complex, conjugated by `piAssembleComplexXIso`. -/
theorem map_piAssembleComplex_d [(Functor.pi' F).IsEquivalence]
    (C : ∀ i, HomologicalComplex (B i) c) (i : ι) (p q : β) :
    (F i).map ((piAssembleComplex F c C).d p q) =
      (piAssembleComplexXIso F c C i p).hom ≫ (C i).d p q ≫
        (piAssembleComplexXIso F c C i q).inv :=
  map_piPreimage F _ i

/-- The identifications `piAssembleComplexXIso` commute with the differentials of the assembled
complex, read through `F i`, and of the `i`-th complex. -/
theorem piAssembleComplexXIso_comp_d [(Functor.pi' F).IsEquivalence]
    (C : ∀ i, HomologicalComplex (B i) c) (i : ι) (p q : β) :
    (piAssembleComplexXIso F c C i p).hom ≫ (C i).d p q =
      (F i).map ((piAssembleComplex F c C).d p q) ≫ (piAssembleComplexXIso F c C i q).hom := by
  rw [map_piAssembleComplex_d]
  simp

/-- The image of the assembled complex under `F i` is the `i`-th complex of the family. -/
def piAssembleComplexIso [(Functor.pi' F).IsEquivalence]
    (C : ∀ i, HomologicalComplex (B i) c) (i : ι) :
    ((F i).mapHomologicalComplex c).obj (piAssembleComplex F c C) ≅ C i :=
  HomologicalComplex.Hom.isoOfComponents (fun p => piAssembleComplexXIso F c C i p)
    (fun p q _ => piAssembleComplexXIso_comp_d F c C i p q)

/-- A family of maps of complexes `F i X ⟶ F i Y` assembled into one map `X ⟶ Y`. -/
def piAssembleHom [(Functor.pi' F).IsEquivalence] {X Y : HomologicalComplex A c}
    (g : ∀ i, ((F i).mapHomologicalComplex c).obj X ⟶ ((F i).mapHomologicalComplex c).obj Y) :
    X ⟶ Y where
  f p := piPreimage F fun i => (g i).f p
  comm' p q _ := pi_hom_ext F fun i => by
    rw [Functor.map_comp, Functor.map_comp, map_piPreimage, map_piPreimage]
    exact (g i).comm p q

/-- The image of the assembled map `piAssembleHom F c g` under `F i` is `g i`. -/
theorem map_piAssembleHom [(Functor.pi' F).IsEquivalence] {X Y : HomologicalComplex A c}
    (g : ∀ i, ((F i).mapHomologicalComplex c).obj X ⟶ ((F i).mapHomologicalComplex c).obj Y)
    (i : ι) : ((F i).mapHomologicalComplex c).map (piAssembleHom F c g) = g i := by
  ext p
  exact map_piPreimage F (fun i => (g i).f p) i

/-- A family of homotopies between the images of two maps of complexes assembled into one
homotopy between the maps. -/
def piAssembleHomotopy [(Functor.pi' F).IsEquivalence] {X Y : HomologicalComplex A c}
    {f g : X ⟶ Y}
    (h : ∀ i, Homotopy (((F i).mapHomologicalComplex c).map f)
      (((F i).mapHomologicalComplex c).map g)) : Homotopy f g where
  hom p q := piPreimage F fun i => (h i).hom p q
  zero p q hpq := pi_hom_ext F fun i => by simp [(h i).zero p q hpq]
  comm p := pi_hom_ext F fun i => by
    have hc := (h i).comm p
    dsimp [dNext, prevD] at hc ⊢
    simp only [AddMonoidHom.mk'_apply, Functor.map_add, Functor.map_comp,
      map_piPreimage] at hc ⊢
    exact hc

variable [(Functor.pi' F).IsEquivalence]

/-- The functor `K(A) ⥤ ∏ i, K(B i)` induced by a product decomposition is full. -/
instance full_pi'_mapHomotopyCategory :
    (Functor.pi' fun i => (F i).mapHomotopyCategory c).Full where
  map_surjective {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    choose g hg using fun i => (HomotopyCategory.quotient (B i) c).map_surjective (f i)
    refine ⟨(HomotopyCategory.quotient A c).map (piAssembleHom F c g), ?_⟩
    funext i
    change (HomotopyCategory.quotient (B i) c).map
      (((F i).mapHomologicalComplex c).map (piAssembleHom F c g)) = f i
    rw [map_piAssembleHom, hg]

/-- The functor `K(A) ⥤ ∏ i, K(B i)` induced by a product decomposition is faithful. -/
instance faithful_pi'_mapHomotopyCategory :
    (Functor.pi' fun i => (F i).mapHomotopyCategory c).Faithful where
  map_injective {X Y} f₁ f₂ hf := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨g₁, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f₁
    obtain ⟨g₂, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f₂
    exact HomotopyCategory.eq_of_homotopy _ _ (piAssembleHomotopy F c fun i =>
      HomotopyCategory.homotopyOfEq _ _ (congrFun hf i))

/-- The functor `K(A) ⥤ ∏ i, K(B i)` induced by a product decomposition is essentially
surjective. -/
instance essSurj_pi'_mapHomotopyCategory :
    (Functor.pi' fun i => (F i).mapHomotopyCategory c).EssSurj where
  mem_essImage Y :=
    ⟨(HomotopyCategory.quotient A c).obj (piAssembleComplex F c fun i => (Y i).as),
      ⟨Pi.isoMk fun i =>
        (HomotopyCategory.quotient (B i) c).mapIso (piAssembleComplexIso F c _ i)⟩⟩

/-- **The homotopy category of a product decomposition.** If additive functors `F i : A ⥤ B i`
identify `A` with `∏ i, B i`, then they identify `K(A)` with `∏ i, K(B i)`. -/
instance isEquivalence_pi'_mapHomotopyCategory :
    (Functor.pi' fun i => (F i).mapHomotopyCategory c).IsEquivalence where

end Homotopy

section Derived

/-- A product of morphism properties which respect isomorphisms respects isomorphisms. -/
instance _root_.CategoryTheory.MorphismProperty.pi_respectsIso {C : ι → Type uB}
    [∀ i, Category.{vB} (C i)] (W : ∀ i, MorphismProperty (C i)) [∀ i, (W i).RespectsIso] :
    (MorphismProperty.pi W).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf i => by
      have := (isIso_pi_iff e.hom).mp inferInstance i
      exact MorphismProperty.RespectsIso.precomp (W i) (e.hom i) (f i) (hf i))
    (fun e f hf i => by
      have := (isIso_pi_iff e.hom).mp inferInstance i
      exact MorphismProperty.RespectsIso.postcomp (W i) (e.hom i) (f i) (hf i))

variable [Abelian A] [∀ i, Abelian (B i)] [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  [(Functor.pi' F).IsEquivalence]

/-- A map of complexes of `A` is a quasi-isomorphism if and only if its image under every
`F i` is, for exact functors `F i` identifying `A` with `∏ i, B i`. -/
theorem quasiIso_map_iff {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    QuasiIso f ↔ ∀ i, QuasiIso (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  refine ⟨fun _ i => inferInstance, fun h => ?_⟩
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rw [← isIso_iff_of_reflects_iso _ (Functor.pi' F), isIso_pi_iff]
  intro i
  have hi := (quasiIso_iff _).mp (h i) n
  rw [quasiIsoAt_iff_isIso_homologyMap] at hi
  show IsIso ((F i).map (HomologicalComplex.homologyMap f n))
  have e := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map f) (F i)
  have hi' : IsIso (ShortComplex.homologyMap ((F i).mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map f))) := hi
  have h2 : IsIso (((X.sc n).mapHomologyIso (F i)).hom ≫ (F i).map
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map f))) := by
    rw [← e]
    infer_instance
  have h3 : IsIso ((X.sc n).mapHomologyIso (F i)).hom := Iso.isIso_hom _
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h3 h2

/-- A map of the homotopy category of `A` is a quasi-isomorphism if and only if its image in
every `K(B i)` is. -/
theorem quasiIso_iff_forall_map {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f ↔
      ∀ i, HomotopyCategory.quasiIso (B i) (ComplexShape.up ℤ)
        (((F i).mapHomotopyCategory (ComplexShape.up ℤ)).map f) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective f
  show HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) ↔
    ∀ i, HomotopyCategory.quasiIso (B i) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (B i) (ComplexShape.up ℤ)).map
        (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).map g))
  simp only [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact quasiIso_map_iff F g

variable [HasDerivedCategory A] [∀ i, HasDerivedCategory (B i)]

/-- **The derived category of a product decomposition.** If exact functors `F i : A ⥤ B i`
identify `A` with `∏ i, B i`, then they identify `D(A)` with `∏ i, D(B i)`. -/
instance isEquivalence_pi'_mapDerivedCategory :
    (Functor.pi' fun i => (F i).mapDerivedCategory).IsEquivalence := by
  let Φ : LocalizerMorphism (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (MorphismProperty.pi fun i => HomotopyCategory.quasiIso (B i) (ComplexShape.up ℤ)) :=
    { functor := Functor.pi' fun i => (F i).mapHomotopyCategory (ComplexShape.up ℤ)
      map := fun _ _ f hf => (quasiIso_iff_forall_map F f).mp hf }
  have : Φ.functor.IsEquivalence :=
    inferInstanceAs (Functor.pi' fun i => (F i).mapHomotopyCategory (ComplexShape.up
        ℤ)).IsEquivalence
  have : Φ.IsInduced := ⟨by ext X Y f; exact (quasiIso_iff_forall_map F f).symm⟩
  have : Φ.IsLocalizedEquivalence := LocalizerMorphism.isLocalizedEquivalence_of_isInduced _
  have : (Functor.pi fun i => (DerivedCategory.Qh : HomotopyCategory (B i) _ ⥤ _)).IsLocalization
      (MorphismProperty.pi fun i => HomotopyCategory.quasiIso (B i) (ComplexShape.up ℤ)) :=
    Stacks.MappingTelescope.functorPi_isLocalization_of_leftCoF _ _
  have : CatCommSq Φ.functor DerivedCategory.Qh
      (Functor.pi fun i => (DerivedCategory.Qh : HomotopyCategory (B i) _ ⥤ _))
      (Functor.pi' fun i => (F i).mapDerivedCategory) :=
    ⟨NatIso.pi' fun i => (F i).mapDerivedCategoryFactorsh.symm⟩
  exact Φ.isEquivalence DerivedCategory.Qh
    (Functor.pi fun i => (DerivedCategory.Qh : HomotopyCategory (B i) _ ⥤ _)) _

end Derived

end CategoryTheory.Functor
