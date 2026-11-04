module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Functor.Derived.LocalizationLeftKanExtension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.LongExactSequence
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Restriction

/-!
# Unbounded relative Mayer--Vietoris

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `X = U ∪ V` be a cover of its source by
two open subsets.  Writing `a = f|_U`, `b = f|_V` and `c = f|_{U ∩ V}`, Stacks 08HZ asserts that
every object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished triangle

`Rf_* E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V}) ⟶ (Rf_* E)⟦1⟧`

functorially in `E`.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.openSubspaceInclusion`: the inclusion of the open
  subspace cut out by an open subset of a ringed space.
* `Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong` and
  `Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforward`: pullback along a map into
  the source followed by pushforward along its composite with `f`, and its special case for
  the inclusion of an open subset.
* `Stacks.Cohomology.RelativeMayerVietoris.homotopyToDerived`: an additive functor applied
  degreewise on the homotopy category and then localized; the functor whose right derived
  functor is a derived pushforward.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris`: **Stacks 08HZ**,
  the functorial distinguished triangle attached to a cover by two open subsets.

## Implementation notes

Rather than fixing models for the four derived pushforwards, the statement quantifies over
arbitrary functors `Rf`, `RU`, `RV`, `RUV` equipped with `Functor.IsRightDerivedFunctor` data,
so it applies to every choice of them.  Functoriality in the derived object is expressed by the
five maps of the triangle being natural transformations of those functors; at each object the
first two are assembled, and the next two split, through the binary biproduct.

The proof is the dévissage of the source.  Over an injective sheaf of modules the degree-zero
part of the relative Mayer--Vietoris sequence of Stacks 01EC is short exact: exactness on the
left and in the middle are two of its fields, and surjectivity on the right follows from the
vanishing of `R¹f_*` on an injective object.  Applying the three functors to the functorial
K-injective resolution of Stacks 079P, whose terms are injective, therefore yields a short
exact sequence of cochain complexes, hence a distinguished triangle in `D(𝒪_Y)` whose
connecting map is natural in the complex; that naturality is what descends it to a natural
transformation of the given derived functors.

The comparison between the degreewise image of a complex and the value of a right derived
functor on it is packaged as `CategoryTheory.Functor.cochainRightDerivedUnit` of an
isomorphism, which supplies its naturality in the complex and its invertibility on K-injective
complexes rather than leaving both to be proved by hand.

## References

* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

attribute [local instance] HasDerivedCategory.standard

/-- A binary biproduct of additive functors is additive: it is isomorphic to the pointwise
biproduct, which is additive because a biproduct of morphisms is additive in them. -/
private local instance biprodFunctorAdditive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [HasBinaryBiproduct F G] : (F ⊞ G).Additive := by
  have hH : (pointwiseBinaryBiproductData F G).bicone.pt.Additive := by
    refine ⟨?_⟩
    intro A B g h
    change biprod.map (F.map (g + h)) (G.map (g + h)) =
      biprod.map (F.map g) (G.map g) + biprod.map (F.map h) (G.map h)
    rw [Functor.map_add, Functor.map_add]
    apply biprod.hom_ext'
    · simp
    · simp
  exact Functor.additive_of_iso
    (biprod.uniqueUpToIso F G (pointwiseBinaryBiproductData F G).isBilimit)

section Abstract

/-- Transport of a naturality square along two commuting squares and an inverted one: the
shape of the comparison between a natural family defined on a resolution and the transported
family on arbitrary objects. Stated for bare morphisms so that no functor is unfolded. -/
private lemma comp_transport_comp {D : Type*} [Category D]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : D} {a : X₁ ⟶ X₂} {p : X₁ ⟶ X₃} {q : X₂ ⟶ X₄} {a' : X₃ ⟶ X₄}
    {dp : X₃ ⟶ Y₃} {dq : X₄ ⟶ Y₄} {b : Y₁ ⟶ Y₂} {b' : Y₃ ⟶ Y₄} {p' : Y₃ ⟶ Y₁}
    {q' : Y₄ ⟶ Y₂} (h₁ : a ≫ q = p ≫ a') (h₂ : a' ≫ dq = dp ≫ b')
    (h₃ : b' ≫ q' = p' ≫ b) :
    a ≫ q ≫ dq ≫ q' = (p ≫ dp ≫ p') ≫ b := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- Two composable functors turn a commuting square into the commuting square obtained by
inverting the two parallel sides, and a third functor carries it along. Stated abstractly so
that the rewriting happens on morphisms of abstract categories. -/
private lemma map_inv_comm {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*}
    [Category E] {E' : Type*} [Category E'] (Φ : C ⥤ D) (Ψ : D ⥤ E) (Θ : E ⥤ E')
    {K L K' L' : C} (g : K ⟶ L) (g' : K' ⟶ L') (p : K ⟶ K') (q : L ⟶ L')
    (h : g ≫ q = p ≫ g') [IsIso (Ψ.map (Φ.map p))] [IsIso (Ψ.map (Φ.map q))] :
    Θ.map (Ψ.map (Φ.map g')) ≫ Θ.map (inv (Ψ.map (Φ.map q))) =
      Θ.map (inv (Ψ.map (Φ.map p))) ≫ Θ.map (Ψ.map (Φ.map g)) := by
  rw [← Θ.map_comp, ← Θ.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Ψ.map_comp, ← Ψ.map_comp,
    ← Φ.map_comp, ← Φ.map_comp, h]

end Abstract

/-- The canonical inclusion of the open subspace cut out by an open subset of a ringed
space. -/
public abbrev openSubspaceInclusion (X : RingedSpace.{u, u}) (U : Opens X) :
    openSubspace X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

/-- Pullback of a module along `i`, followed by pushforward along `i ≫ f`.  For an open
immersion `i` this is "restrict, then push forward along the restriction of `f`", the
underived functor whose right derived functors are `restrictedHigherDirectImage`. -/
public abbrev restrictedPushforwardAlong {X Y U : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y) :=
  modulePullback i ⋙ modulePushforward (i ≫ f)

/-- Restriction of a module to the open subspace `U`, followed by pushforward along the
restriction of `f` to `U`. -/
public abbrev restrictedPushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens X) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y) :=
  restrictedPushforwardAlong f (openSubspaceInclusion X U)

/-- An additive functor applied degreewise on the homotopy category, followed by localization
to the derived category of its target. -/
public abbrev homotopyToDerived {X Y : RingedSpace.{u, u}}
    (F : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
    [F.Additive] :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

section Comparison

variable {X Y : RingedSpace.{u, u}}
  (F : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
  [F.Additive]

/-- Applying an additive functor degreewise and localizing is the same as passing to the
homotopy category first.  The two composites are definitionally equal, so this records the
canonical identification rather than any new content. -/
private def quotientMapComplexIso :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⋙
        homotopyToDerived F where
  hom :=
    { app := fun K => (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      naturality := fun _ _ g => DerivedCategory.quotientCompQhIso_inv_naturality
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) }
  inv :=
    { app := fun K => (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      naturality := fun _ _ g => DerivedCategory.quotientCompQhIso_hom_naturality
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) }
  hom_inv_id := by
    ext K
    exact (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Y))).inv_hom_id_app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  inv_hom_id := by
    ext K
    exact (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Y))).hom_inv_id_app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

variable (R : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (a : homotopyToDerived F ⟶ DerivedCategory.Qh ⋙ R)

/-- The comparison from the localized degreewise image of a complex to the value of a right
derived functor on that complex. -/
private def derivedComparison :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ R :=
  Functor.cochainRightDerivedUnit (quotientMapComplexIso F).hom a

private lemma derivedComparison_app
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedComparison F R a).app K = (quotientMapComplexIso F).hom.app K ≫
      a.app ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj K) ≫
      R.map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).hom.app K) :=
  Functor.cochainRightDerivedUnit_app _ _ _

private lemma isIso_derivedComparison_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (h : IsIso (a.app ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)).obj I))) :
    IsIso ((derivedComparison F R a).app I) := by
  have := h
  exact Functor.isIso_cochainRightDerivedUnit_app _ _ I

/-- The comparison is invertible at a K-injective complex. -/
private lemma isIso_derivedComparison_app_of_isKInjective
    [R.IsRightDerivedFunctor a (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedComparison F R a).app I) :=
  isIso_derivedComparison_app F R a I
    (Stacks.Cohomology.MayerVietoris.isIso_unit_app_of_isKInjective (L := DerivedCategory.Qh)
      _ (Stacks.Cohomology.MayerVietoris.exists_quasiIso_isKInjective _) R a I)

/-- The comparison at a complex which computes the derived functor, as an isomorphism with its
source and target spelled out. -/
private def derivedComparisonIso
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (h : IsIso ((derivedComparison F R a).app I)) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      R.obj (DerivedCategory.Q.obj I) :=
  have := h
  asIso ((derivedComparison F R a).app I)

private lemma derivedComparisonIso_hom
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (h : IsIso ((derivedComparison F R a).app I)) :
    (derivedComparisonIso F R a I h).hom = (derivedComparison F R a).app I := rfl

variable {G : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y)}
  [G.Additive]
  (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (b : homotopyToDerived G ⟶ DerivedCategory.Qh ⋙ T)

private lemma isRightDerivedFunctor_derivedComparison
    [R.IsRightDerivedFunctor a (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    R.IsRightDerivedFunctor (derivedComparison F R a)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_cochainRightDerivedUnit (quotientMapComplexIso F).hom a

variable {G : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y)}
  [G.Additive]
  (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (b : homotopyToDerived G ⟶ DerivedCategory.Qh ⋙ T)

/-- The natural transformation of right derived functors induced, at the cochain level, by a
natural transformation of the underived functors. -/
private def derivedNatTrans
    [R.IsRightDerivedFunctor a (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (α : F ⟶ G) : R ⟶ T :=
  have := isRightDerivedFunctor_derivedComparison F R a
  Functor.rightDerivedNatTrans R T (derivedComparison F R a) (derivedComparison G T b)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
      DerivedCategory.Q)

private lemma derivedComparison_derivedNatTrans
    [R.IsRightDerivedFunctor a (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (α : F ⟶ G) (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj K ⟶ E) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) ≫
        ((derivedComparison G T b).app K ≫ T.map e) =
      ((derivedComparison F R a).app K ≫ R.map e) ≫ (derivedNatTrans F R a T b α).app E := by
  have := isRightDerivedFunctor_derivedComparison F R a
  have h := Functor.rightDerivedNatTrans_app R T (derivedComparison F R a)
    (derivedComparison G T b)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
      DerivedCategory.Q) K
  simp only [Functor.whiskerRight_app] at h
  dsimp only [derivedNatTrans]
  rw [Category.assoc, NatTrans.naturality, reassoc_of% h]

private def mapComplexBiprodIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [HasBinaryBiproduct F G] (K : CochainComplex C ℤ) :
    ((F ⊞ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⊞
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal
    { pt := ((F ⊞ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      fst := (NatTrans.mapHomologicalComplex biprod.fst (ComplexShape.up ℤ)).app K
      snd := (NatTrans.mapHomologicalComplex biprod.snd (ComplexShape.up ℤ)).app K
      inl := (NatTrans.mapHomologicalComplex biprod.inl (ComplexShape.up ℤ)).app K
      inr := (NatTrans.mapHomologicalComplex biprod.inr (ComplexShape.up ℤ)).app K
      inl_fst := by
        ext n
        exact congrArg (fun α => α.app (K.X n)) (biprod.inl_fst (X := F) (Y := G))
      inl_snd := by
        ext n
        exact congrArg (fun α => α.app (K.X n)) (biprod.inl_snd (X := F) (Y := G))
      inr_fst := by
        ext n
        exact congrArg (fun α => α.app (K.X n)) (biprod.inr_fst (X := F) (Y := G))
      inr_snd := by
        ext n
        exact congrArg (fun α => α.app (K.X n)) (biprod.inr_snd (X := F) (Y := G)) }
    (by
      ext n
      exact congrArg (fun α => α.app (K.X n)) (biprod.total (X := F) (Y := G))))

private lemma mapComplexBiprodIso_hom {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [HasBinaryBiproduct F G] (K : CochainComplex C ℤ) :
    (mapComplexBiprodIso F G K).hom = biprod.lift
      ((NatTrans.mapHomologicalComplex biprod.fst (ComplexShape.up ℤ)).app K)
      ((NatTrans.mapHomologicalComplex biprod.snd (ComplexShape.up ℤ)).app K) := rfl

private lemma mapComplexBiprodIso_inv {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts D] (F G : C ⥤ D)
    [F.Additive] [G.Additive] [HasBinaryBiproduct F G] (K : CochainComplex C ℤ) :
    (mapComplexBiprodIso F G K).inv = biprod.desc
      ((NatTrans.mapHomologicalComplex biprod.inl (ComplexShape.up ℤ)).app K)
      ((NatTrans.mapHomologicalComplex biprod.inr (ComplexShape.up ℤ)).app K) := rfl

-- Past this point the comparison, the isomorphism it induces at a computing complex and the
-- induced transformation of derived functors are used only through the specifications proved
-- above.  Their bodies are the universal property of the localization, so leaving them
-- transparent makes every later unification unfold a left Kan extension.
attribute [irreducible] derivedComparison derivedComparisonIso derivedNatTrans

end Comparison

section Biprod

variable {X Y : RingedSpace.{u, u}}
  (F G : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
  [F.Additive] [G.Additive]
  (R T : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (a : homotopyToDerived F ⟶ DerivedCategory.Qh ⋙ R)
  (b : homotopyToDerived G ⟶ DerivedCategory.Qh ⋙ T)

/-- The localized degreewise image of a complex under a biproduct of two additive functors,
compared with the biproduct of the two right derived functors at the corresponding object. -/
private def biprodComparisonIso
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (ha : IsIso ((derivedComparison F R a).app I))
    (hb : IsIso ((derivedComparison G T b).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    DerivedCategory.Q.obj (((F ⊞ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      R.obj E ⊞ T.obj E :=
  have : PreservesBinaryBiproducts
      (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  DerivedCategory.Q.mapIso (mapComplexBiprodIso F G I) ≪≫
    DerivedCategory.Q.mapBiprod
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
    biprod.mapIso (derivedComparisonIso F R a I ha ≪≫ R.mapIso e)
      (derivedComparisonIso G T b I hb ≪≫ T.mapIso e)

private lemma biprodComparisonIso_hom_comp_fst
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (ha : IsIso ((derivedComparison F R a).app I))
    (hb : IsIso ((derivedComparison G T b).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    (biprodComparisonIso F G R T a b I ha hb e).hom ≫ biprod.fst (X := R.obj E) (Y := T.obj E) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (biprod.fst (X := F) (Y := G)) (ComplexShape.up ℤ)).app I) ≫
        (derivedComparison F R a).app I ≫ R.map e.hom := by
  dsimp only [biprodComparisonIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom,
    Functor.mapBiprod_hom, biprod.mapIso_hom, Category.assoc, biprod.map_fst,
    biprod.lift_fst_assoc]
  rw [← Functor.map_comp_assoc, mapComplexBiprodIso_hom, biprod.lift_fst]

private lemma biprodComparisonIso_hom_comp_snd
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (ha : IsIso ((derivedComparison F R a).app I))
    (hb : IsIso ((derivedComparison G T b).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    (biprodComparisonIso F G R T a b I ha hb e).hom ≫ biprod.snd (X := R.obj E) (Y := T.obj E) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (biprod.snd (X := F) (Y := G)) (ComplexShape.up ℤ)).app I) ≫
        (derivedComparison G T b).app I ≫ T.map e.hom := by
  dsimp only [biprodComparisonIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom,
    Functor.mapBiprod_hom, biprod.mapIso_hom, Category.assoc, biprod.map_snd,
    biprod.lift_snd_assoc]
  rw [← Functor.map_comp_assoc, mapComplexBiprodIso_hom, biprod.lift_snd]

private lemma biprod_inl_comp_biprodComparisonIso_inv
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (ha : IsIso ((derivedComparison F R a).app I))
    (hb : IsIso ((derivedComparison G T b).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    biprod.inl (X := R.obj E) (Y := T.obj E) ≫
        (biprodComparisonIso F G R T a b I ha hb e).inv =
      (derivedComparisonIso F R a I ha ≪≫ R.mapIso e).inv ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (biprod.inl (X := F) (Y := G)) (ComplexShape.up ℤ)).app I) := by
  dsimp only [biprodComparisonIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
  rw [Category.assoc, biprod.inl_map_assoc, biprod.inl_desc_assoc, ← Functor.map_comp,
    mapComplexBiprodIso_inv, biprod.inl_desc]

private lemma biprod_inr_comp_biprodComparisonIso_inv
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (ha : IsIso ((derivedComparison F R a).app I))
    (hb : IsIso ((derivedComparison G T b).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    biprod.inr (X := R.obj E) (Y := T.obj E) ≫
        (biprodComparisonIso F G R T a b I ha hb e).inv =
      (derivedComparisonIso G T b I hb ≪≫ T.mapIso e).inv ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (biprod.inr (X := F) (Y := G)) (ComplexShape.up ℤ)).app I) := by
  dsimp only [biprodComparisonIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
  rw [Category.assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc, ← Functor.map_comp,
    mapComplexBiprodIso_inv, biprod.inr_desc]

-- As above: the comparison isomorphism over a biproduct is used only through the four
-- specifications just proved.
attribute [irreducible] biprodComparisonIso

end Biprod

section TriangleSquares

variable {X Y : RingedSpace.{u, u}}
  (P A B Z : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
  [P.Additive] [A.Additive] [B.Additive] [Z.Additive]
  (RP RA RB RZ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (aP : homotopyToDerived P ⟶ DerivedCategory.Qh ⋙ RP)
  (aA : homotopyToDerived A ⟶ DerivedCategory.Qh ⋙ RA)
  (aB : homotopyToDerived B ⟶ DerivedCategory.Qh ⋙ RB)
  (aZ : homotopyToDerived Z ⟶ DerivedCategory.Qh ⋙ RZ)
  (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- The first square of the comparison between the triangle of a degreewise short exact
sequence and the triangle of right derived functors: the localized first map, read through
the comparison isomorphisms, is the biproduct of the two right-derived restrictions. -/
private lemma triangleSquare_mor₁
    [RP.IsRightDerivedFunctor aP (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (α : P ⟶ A ⊞ B)
    (hcP : IsIso ((derivedComparison P RP aP).app I))
    (hcA : IsIso ((derivedComparison A RA aA).app I))
    (hcB : IsIso ((derivedComparison B RB aB).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I) ≫
        (biprodComparisonIso A B RA RB aA aB I hcA hcB e).hom =
      (derivedComparisonIso P RP aP I hcP ≪≫ RP.mapIso e).hom ≫
        biprod.lift ((derivedNatTrans P RP aP RA aA (α ≫ biprod.fst)).app E)
          ((derivedNatTrans P RP aP RB aB (α ≫ biprod.snd)).app E) := by
  have hA := derivedComparison_derivedNatTrans P RP aP RA aA (α ≫ biprod.fst) I e.hom
  have hB := derivedComparison_derivedNatTrans P RP aP RB aB (α ≫ biprod.snd) I e.hom
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    rw [biprodComparisonIso_hom_comp_fst, ← Functor.map_comp_assoc]
    simpa only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom, Category.assoc,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using hA
  · simp only [Category.assoc, biprod.lift_snd]
    rw [biprodComparisonIso_hom_comp_snd, ← Functor.map_comp_assoc]
    simpa only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom, Category.assoc,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using hB

/-- The second square of that comparison: the localized second map, read through the
comparison isomorphisms, splits over the biproduct into the two right-derived differences. -/
private lemma triangleSquare_mor₂
    [RA.IsRightDerivedFunctor aA (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RB.IsRightDerivedFunctor aB (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (β : A ⊞ B ⟶ Z)
    (hcA : IsIso ((derivedComparison A RA aA).app I))
    (hcB : IsIso ((derivedComparison B RB aB).app I))
    (hcZ : IsIso ((derivedComparison Z RZ aZ).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I) ≫
        (derivedComparisonIso Z RZ aZ I hcZ ≪≫ RZ.mapIso e).hom =
      (biprodComparisonIso A B RA RB aA aB I hcA hcB e).hom ≫
        biprod.desc ((derivedNatTrans A RA aA RZ aZ (biprod.inl ≫ β)).app E)
          ((derivedNatTrans B RB aB RZ aZ (biprod.inr ≫ β)).app E) := by
  have hA := derivedComparison_derivedNatTrans A RA aA RZ aZ (biprod.inl ≫ β) I e.hom
  have hB := derivedComparison_derivedNatTrans B RB aB RZ aZ (biprod.inr ≫ β) I e.hom
  rw [← Iso.inv_comp_eq]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc, ← Category.assoc]
    rw [biprod_inl_comp_biprodComparisonIso_inv]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_comp_eq]
    simpa only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom, Category.assoc,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using hA
  · simp only [biprod.inr_desc, ← Category.assoc]
    rw [biprod_inr_comp_biprodComparisonIso_inv]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_comp_eq]
    simpa only [Iso.trans_hom, Functor.mapIso_hom, derivedComparisonIso_hom, Category.assoc,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using hB

/-- The third square of that comparison: the connecting map descends, through the universal
property of the right derived functor, to the natural transformation whose value at a
complex computing the derived functors is the chain-level connecting map. -/
private lemma triangleSquare_mor₃
    [RZ.IsRightDerivedFunctor (derivedComparison Z RZ aZ)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (ν : Z.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ))
    (d : DerivedCategory.Q.obj ((Z.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (DerivedCategory.Q.obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))⟦(1 : ℤ)⟧)
    (hν : ν.app I = d ≫ ((derivedComparison P RP aP).app I)⟦(1 : ℤ)⟧')
    (hcP : IsIso ((derivedComparison P RP aP).app I))
    (hcZ : IsIso ((derivedComparison Z RZ aZ).app I))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Q.obj I ≅ E) :
    d ≫ ((derivedComparisonIso P RP aP I hcP ≪≫ RP.mapIso e).hom)⟦(1 : ℤ)⟧' =
      (derivedComparisonIso Z RZ aZ I hcZ ≪≫ RZ.mapIso e).hom ≫
        (RZ.rightDerivedDesc (derivedComparison Z RZ aZ)
          (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)) _ ν).app E := by
  simp only [Iso.trans_hom, derivedComparisonIso_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [(RZ.rightDerivedDesc (derivedComparison Z RZ aZ)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    ν).naturality e.hom, Functor.rightDerived_fac_app_assoc, hν]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]

end TriangleSquares

section Sequence

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
  (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)

private lemma shortExact_relativeMayerVietoris_app_injective
    (S : RelativeMayerVietorisSequence f iU iV iW)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    ∃ h : (S.toCover 0).app I ≫ (S.toIntersection 0).app I = 0,
      (ShortComplex.mk ((S.toCover 0).app I) ((S.toIntersection 0).app I) h).ShortExact := by
  obtain ⟨h₀, hExact⟩ := S.exact_cover 0 I
  have hmono : Mono ((S.toCover 0).app I) := S.mono_zero I
  obtain ⟨h₁, hExact₁⟩ := S.exact_intersection 0 I
  have hR1 : IsZero (((modulePushforward f).rightDerived 1).obj I) :=
    Functor.isZero_rightDerived_obj_injective_succ (modulePushforward f) 0 I
  have hboundary : (S.boundary 0).app I = 0 := hR1.eq_of_tgt ((S.boundary 0).app I) 0
  have hepi : Epi ((S.toIntersection 0).app I) :=
    ((ShortComplex.mk ((S.toIntersection 0).app I) ((S.boundary 0).app I) h₁).exact_iff_epi
      hboundary).1 hExact₁
  exact ⟨h₀, ShortComplex.ShortExact.mk' hExact hmono hepi⟩

private def pushforwardRightDerivedZeroIso :
    higherDirectImage f 0 ≅ modulePushforward f :=
  have := modulePushforward_isRightAdjoint f
  Functor.rightDerivedZeroIsoSelf _

private def restrictedPushforwardRightDerivedZeroIso :
    restrictedHigherDirectImage f iU 0 ≅ restrictedPushforwardAlong f iU :=
  have := modulePushforward_isRightAdjoint (iU ≫ f)
  Functor.isoWhiskerLeft (modulePullback iU) (Functor.rightDerivedZeroIsoSelf _)

private def restrictedPushforwardPairRightDerivedZeroIso :
    (restrictedPushforwardAlong f iU ⊞ restrictedPushforwardAlong f iV) ≅
      (restrictedHigherDirectImage f iU 0 ⊞ restrictedHigherDirectImage f iV 0) :=
  biprod.mapIso (restrictedPushforwardRightDerivedZeroIso f iU).symm
    (restrictedPushforwardRightDerivedZeroIso f iV).symm

/-- The degree-zero restriction map of the relative Mayer--Vietoris sequence, read as a map
out of pushforward itself. -/
private def pushforwardZeroToCover (S : RelativeMayerVietorisSequence f iU iV iW) :
    modulePushforward f ⟶
      restrictedPushforwardAlong f iU ⊞ restrictedPushforwardAlong f iV :=
  (pushforwardRightDerivedZeroIso f).inv ≫ S.toCover 0 ≫
    (restrictedPushforwardPairRightDerivedZeroIso f iU iV).inv

/-- The degree-zero difference map of the relative Mayer--Vietoris sequence, read as a map
into the pushforward from the intersection. -/
private def pushforwardZeroToIntersection (S : RelativeMayerVietorisSequence f iU iV iW) :
    (restrictedPushforwardAlong f iU ⊞ restrictedPushforwardAlong f iV) ⟶
      restrictedPushforwardAlong f iW :=
  (restrictedPushforwardPairRightDerivedZeroIso f iU iV).hom ≫ S.toIntersection 0 ≫
    (restrictedPushforwardRightDerivedZeroIso f iW).hom

private lemma pushforwardToCover_comp_toIntersection_app
    (S : RelativeMayerVietorisSequence f iU iV iW) (M : SheafOfModules.{u} (structureSheafRing X)) :
    (pushforwardZeroToCover f iU iV iW S).app M ≫
      (pushforwardZeroToIntersection f iU iV iW S).app M = 0 := by
  obtain ⟨h, _⟩ := S.exact_cover 0 M
  dsimp only [pushforwardZeroToCover, pushforwardZeroToIntersection, NatTrans.comp_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc ((S.toCover 0).app M), h]
  simp

private lemma shortExact_pushforwardShortComplex_app_injective
    (S : RelativeMayerVietorisSequence f iU iV iW)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    (ShortComplex.mk ((pushforwardZeroToCover f iU iV iW S).app I)
      ((pushforwardZeroToIntersection f iU iV iW S).app I)
      (pushforwardToCover_comp_toIntersection_app f iU iV iW S I)).ShortExact := by
  obtain ⟨h, hS⟩ := shortExact_relativeMayerVietoris_app_injective f iU iV iW S I
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    ((pushforwardRightDerivedZeroIso f).symm.app I)
    ((restrictedPushforwardPairRightDerivedZeroIso f iU iV).app I)
    ((restrictedPushforwardRightDerivedZeroIso f iW).symm.app I) ?_ ?_).symm hS
  · dsimp only [pushforwardZeroToCover, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app]
    simp
  · dsimp only [pushforwardZeroToIntersection, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app]
    simp

/-- The Mayer--Vietoris short complex of complexes of modules on the target, obtained by
applying the three functors degreewise. -/
private abbrev pushforwardComplexShortComplex
    (S : RelativeMayerVietorisSequence f iU iV iW)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ShortComplex (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (pushforwardZeroToCover f iU iV iW S) (ComplexShape.up ℤ)).app I)
    ((NatTrans.mapHomologicalComplex
      (pushforwardZeroToIntersection f iU iV iW S) (ComplexShape.up ℤ)).app I)
    (by
      ext n : 1
      exact pushforwardToCover_comp_toIntersection_app f iU iV iW S (I.X n))

private lemma shortExact_pushforwardComplexShortComplex
    (S : RelativeMayerVietorisSequence f iU iV iW)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : ∀ n, Injective (I.X n)) :
    (pushforwardComplexShortComplex f iU iV iW S I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hI n
  exact shortExact_pushforwardShortComplex_app_injective f iU iV iW S (I.X n)

/-- The map of Mayer--Vietoris short complexes induced by a map of complexes. -/
private def pushforwardComplexShortComplexMap
    (S : RelativeMayerVietorisSequence f iU iV iW)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (g : K ⟶ L) :
    pushforwardComplexShortComplex f iU iV iW S K ⟶
      pushforwardComplexShortComplex f iU iV iW S L :=
  ShortComplex.Hom.mk
    (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map g)
    (((restrictedPushforwardAlong f iU ⊞
      restrictedPushforwardAlong f iV).mapHomologicalComplex (ComplexShape.up ℤ)).map g)
    (((restrictedPushforwardAlong f iW).mapHomologicalComplex (ComplexShape.up ℤ)).map g)
    ((NatTrans.mapHomologicalComplex
      (pushforwardZeroToCover f iU iV iW S) (ComplexShape.up ℤ)).naturality g)
    ((NatTrans.mapHomologicalComplex
      (pushforwardZeroToIntersection f iU iV iW S) (ComplexShape.up ℤ)).naturality g)

variable (S : RelativeMayerVietorisSequence f iU iV iW)
  (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (af : homotopyToDerived (modulePushforward f) ⟶ DerivedCategory.Qh ⋙ Rf)

/-- The connecting map of the Mayer--Vietoris triangle at a complex with injective terms. -/
private def pushforwardConnectingOfInjective
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    DerivedCategory.Q.obj
        (((restrictedPushforwardAlong f iW).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (Rf.obj (DerivedCategory.Q.obj K))⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ
      (shortExact_pushforwardComplexShortComplex f iU iV iW S K hK) ≫
    ((derivedComparison (modulePushforward f) Rf af).app K)⟦(1 : ℤ)⟧'

private lemma pushforwardConnectingOfInjective_naturality
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (hK : ∀ n, Injective (K.X n)) (hL : ∀ n, Injective (L.X n)) (g : K ⟶ L) :
    DerivedCategory.Q.map
          (((restrictedPushforwardAlong f iW).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) ≫
        pushforwardConnectingOfInjective f iU iV iW S Rf af L hL =
      pushforwardConnectingOfInjective f iU iV iW S Rf af K hK ≫
        (Rf.map (DerivedCategory.Q.map g))⟦(1 : ℤ)⟧' := by
  have hδ := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_pushforwardComplexShortComplex f iU iV iW S K hK)
    (shortExact_pushforwardComplexShortComplex f iU iV iW S L hL)
    (pushforwardComplexShortComplexMap f iU iV iW S g)
  dsimp only [pushforwardComplexShortComplexMap] at hδ
  have hc := (derivedComparison (modulePushforward f) Rf af).naturality g
  dsimp only [Functor.comp_map] at hc
  dsimp only [pushforwardConnectingOfInjective]
  rw [← reassoc_of% hδ]
  simp only [← Functor.map_comp]
  rw [hc]
  simp only [Functor.map_comp, Category.assoc]

/-- The connecting map of the Mayer--Vietoris triangle at an arbitrary complex, obtained by
transporting the connecting map of its functorial K-injective resolution. -/
private def pushforwardConnectingAtComplex
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    DerivedCategory.Q.obj
        (((restrictedPushforwardAlong f iW).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (Rf.obj (DerivedCategory.Q.obj K))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map
      (((restrictedPushforwardAlong f iW).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} (structureSheafRing X))).app K)) ≫
    pushforwardConnectingOfInjective f iU iV iW S Rf af
      ((Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (structureSheafRing X))).obj K)
      (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ K n) ≫
    (inv (Rf.map (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion
        (SheafOfModules.{u} (structureSheafRing X))).app K))))⟦(1 : ℤ)⟧'

private lemma pushforwardConnectingAtComplex_eq
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    pushforwardConnectingAtComplex f iU iV iW S Rf af K =
      pushforwardConnectingOfInjective f iU iV iW S Rf af K hK := by
  dsimp only [pushforwardConnectingAtComplex]
  rw [reassoc_of% (pushforwardConnectingOfInjective_naturality f iU iV iW S Rf af hK
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ K n)
    ((Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).app K))]
  simp only [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

private lemma pushforwardConnectingAtComplex_naturality
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (g : K ⟶ L) :
    DerivedCategory.Q.map
          (((restrictedPushforwardAlong f iW).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) ≫
        pushforwardConnectingAtComplex f iU iV iW S Rf af L =
      pushforwardConnectingAtComplex f iU iV iW S Rf af K ≫
        (Rf.map (DerivedCategory.Q.map g))⟦(1 : ℤ)⟧' := by
  have hι : g ≫ (Stacks.Injectives.kInjectiveResolutionInclusion
        (SheafOfModules.{u} (structureSheafRing X))).app L =
      (Stacks.Injectives.kInjectiveResolutionInclusion
        (SheafOfModules.{u} (structureSheafRing X))).app K ≫
        (Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} (structureSheafRing X))).map g :=
    (Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).naturality g
  have hnat := pushforwardConnectingOfInjective_naturality f iU iV iW S Rf af
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ K n)
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ L n)
    ((Stacks.Injectives.kInjectiveResolutionFunctor
      (SheafOfModules.{u} (structureSheafRing X))).map g)
  have hres := map_inv_comm DerivedCategory.Q Rf
    (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ)) g
    ((Stacks.Injectives.kInjectiveResolutionFunctor
      (SheafOfModules.{u} (structureSheafRing X))).map g)
    ((Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).app K)
    ((Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).app L) hι
  have hpre := congrArg (fun t => DerivedCategory.Q.map
    (((restrictedPushforwardAlong f iW).mapHomologicalComplex (ComplexShape.up ℤ)).map t)) hι
  simp only [Functor.map_comp] at hpre
  dsimp only [pushforwardConnectingAtComplex]
  exact comp_transport_comp hpre hnat hres

/-- The connecting map of the Mayer--Vietoris triangle, as a natural transformation of
functors of the cochain complex: this is what descends to a natural transformation of the
derived functors. -/
private def pushforwardConnectingNat :
    (restrictedPushforwardAlong f iW).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ Rf ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ) where
  app K := pushforwardConnectingAtComplex f iU iV iW S Rf af K
  naturality _ _ g := pushforwardConnectingAtComplex_naturality f iU iV iW S Rf af g

/-- The relative Mayer--Vietoris triangle built from the derived functors of the degree-zero
maps of `S` is distinguished at every object of the derived category. -/
private theorem triangle_mem_distTriang_of_sequence
    (RU RV RUV : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (aU : homotopyToDerived (restrictedPushforwardAlong f iU) ⟶ DerivedCategory.Qh ⋙ RU)
    (aV : homotopyToDerived (restrictedPushforwardAlong f iV) ⟶ DerivedCategory.Qh ⋙ RV)
    (aUV : homotopyToDerived (restrictedPushforwardAlong f iW) ⟶ DerivedCategory.Qh ⋙ RUV)
    [Rf.IsRightDerivedFunctor af (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RU.IsRightDerivedFunctor aU (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RV.IsRightDerivedFunctor aV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor aUV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor (derivedComparison (restrictedPushforwardAlong f iW) RUV aUV)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Triangle.mk
      (biprod.lift
        ((derivedNatTrans (modulePushforward f) Rf af RU aU
          (pushforwardZeroToCover f iU iV iW S ≫ biprod.fst)).app E)
        ((derivedNatTrans (modulePushforward f) Rf af RV aV
          (pushforwardZeroToCover f iU iV iW S ≫ biprod.snd)).app E))
      (biprod.desc
        ((derivedNatTrans (restrictedPushforwardAlong f iU) RU aU RUV aUV
          (biprod.inl ≫ pushforwardZeroToIntersection f iU iV iW S)).app E)
        ((derivedNatTrans (restrictedPushforwardAlong f iV) RV aV RUV aUV
          (biprod.inr ≫ pushforwardZeroToIntersection f iU iV iW S)).app E))
      ((RUV.rightDerivedDesc (derivedComparison (restrictedPushforwardAlong f iW) RUV aUV)
        (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) _ (pushforwardConnectingNat f iU iV iW S Rf af)).app E) ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) := by
  classical
  obtain ⟨I, hIK, hIinj, ⟨e⟩⟩ :
      ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (_ : I.IsKInjective)
        (_ : ∀ n, Injective (I.X n)), Nonempty (DerivedCategory.Q.obj I ≅ E) := by
    refine ⟨(Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (structureSheafRing X))).obj (DerivedCategory.Q.objPreimage E),
      inferInstance,
      fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ _ n, ⟨?_⟩⟩
    have hq : IsIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} (structureSheafRing X))).app (DerivedCategory.Q.objPreimage E))) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    exact (asIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} (structureSheafRing X))).app
            (DerivedCategory.Q.objPreimage E)))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso E
  have hcF := isIso_derivedComparison_app_of_isKInjective (modulePushforward f) Rf af I
  have hcU := isIso_derivedComparison_app_of_isKInjective (restrictedPushforwardAlong f iU) RU aU I
  have hcV := isIso_derivedComparison_app_of_isKInjective (restrictedPushforwardAlong f iV) RV aV I
  have hcW :=
    isIso_derivedComparison_app_of_isKInjective (restrictedPushforwardAlong f iW) RUV aUV I
  have hShort := shortExact_pushforwardComplexShortComplex f iU iV iW S I hIinj
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hShort) _ ?_
  refine (Triangle.isoMk _ _
      (derivedComparisonIso (modulePushforward f) Rf af I hcF ≪≫ Rf.mapIso e)
      (biprodComparisonIso (restrictedPushforwardAlong f iU) (restrictedPushforwardAlong f iV)
        RU RV aU aV I hcU hcV e)
      (derivedComparisonIso (restrictedPushforwardAlong f iW) RUV aUV I hcW ≪≫
        RUV.mapIso e) ?_ ?_ ?_).symm
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₁]
    exact triangleSquare_mor₁ (modulePushforward f) (restrictedPushforwardAlong f iU)
      (restrictedPushforwardAlong f iV) Rf RU RV af aU aV I
      (pushforwardZeroToCover f iU iV iW S) hcF hcU hcV e
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₂]
    exact triangleSquare_mor₂ (restrictedPushforwardAlong f iU)
      (restrictedPushforwardAlong f iV) (restrictedPushforwardAlong f iW) RU RV RUV aU aV aUV I
      (pushforwardZeroToIntersection f iU iV iW S) hcU hcV hcW e
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₃]
    exact triangleSquare_mor₃ (modulePushforward f) (restrictedPushforwardAlong f iW) Rf RUV
      af aUV I (pushforwardConnectingNat f iU iV iW S Rf af)
      (DerivedCategory.triangleOfSESδ hShort)
      (by
        dsimp only [pushforwardConnectingNat]
        exact pushforwardConnectingAtComplex_eq f iU iV iW S Rf af I hIinj) hcF hcW e

end Sequence

section Main

variable {X Y : RingedSpace.{u, u}}

private lemma openSubspaceInclusion_range (X : RingedSpace.{u, u}) (U : Opens X) :
    Set.range (openSubspaceInclusion X U).hom.base = U := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rintro ⟨y, rfl⟩
  exact y.2

private lemma exists_relativeMayerVietorisSequence_of_sup_eq_top
    (f : X ⟶ Y) (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    Nonempty (RelativeMayerVietorisSequence f (openSubspaceInclusion X U)
      (openSubspaceInclusion X V) (openSubspaceInclusion X (U ⊓ V))) := by
  have hU : SheafedSpace.IsOpenImmersion (openSubspaceInclusion X U) :=
    SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding
  have hV : SheafedSpace.IsOpenImmersion (openSubspaceInclusion X V) :=
    SheafedSpace.IsOpenImmersion.ofRestrict X V.isOpenEmbedding
  have hW : SheafedSpace.IsOpenImmersion (openSubspaceInclusion X (U ⊓ V)) :=
    SheafedSpace.IsOpenImmersion.ofRestrict X (U ⊓ V).isOpenEmbedding
  apply relativeMayerVietoris f (openSubspaceInclusion X U) (openSubspaceInclusion X V)
    (openSubspaceInclusion X (U ⊓ V))
  · rw [openSubspaceInclusion_range, openSubspaceInclusion_range]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    simpa using (show x ∈ U ⊔ V by rw [hUV]; trivial)
  · rw [openSubspaceInclusion_range, openSubspaceInclusion_range,
      openSubspaceInclusion_range]
    ext x
    simp

/-- **Stacks 08HZ.** For a morphism of ringed spaces and a cover of its source by two open
subsets, the four derived pushforwards attached to the cover fit into a distinguished triangle,
naturally in the object of the unbounded derived category.  The four derived pushforwards are
hypothesised only through `CategoryTheory.Functor.IsRightDerivedFunctor`, so the statement
applies to every choice of them; applying a cohomological functor to the triangle gives the
relative Mayer--Vietoris long exact sequence. -/
@[stacks 08HZ]
public theorem unboundedRelativeMayerVietoris (f : X ⟶ Y) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (Rf RU RV RUV : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (af : homotopyToDerived (modulePushforward f) ⟶ DerivedCategory.Qh ⋙ Rf)
    (aU : homotopyToDerived (restrictedPushforward f U) ⟶ DerivedCategory.Qh ⋙ RU)
    (aV : homotopyToDerived (restrictedPushforward f V) ⟶ DerivedCategory.Qh ⋙ RV)
    (aUV : homotopyToDerived (restrictedPushforward f (U ⊓ V)) ⟶ DerivedCategory.Qh ⋙ RUV)
    [Rf.IsRightDerivedFunctor af (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RU.IsRightDerivedFunctor aU (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RV.IsRightDerivedFunctor aV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor aUV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    ∃ (rU : Rf ⟶ RU) (rV : Rf ⟶ RV) (dU : RU ⟶ RUV) (dV : RV ⟶ RUV)
      (δ : RUV ⟶ Rf ⋙ shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ)),
      ∀ E, Triangle.mk (biprod.lift (rU.app E) (rV.app E))
        (biprod.desc (dU.app E) (dV.app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) := by
  classical
  obtain ⟨S⟩ := exists_relativeMayerVietorisSequence_of_sup_eq_top f U V hUV
  have hRf := isRightDerivedFunctor_derivedComparison (modulePushforward f) Rf af
  have hRU := isRightDerivedFunctor_derivedComparison (restrictedPushforward f U) RU aU
  have hRV := isRightDerivedFunctor_derivedComparison (restrictedPushforward f V) RV aV
  have hRUV := isRightDerivedFunctor_derivedComparison
    (restrictedPushforward f (U ⊓ V)) RUV aUV
  refine ⟨derivedNatTrans (modulePushforward f) Rf af RU aU
      (pushforwardZeroToCover f _ _ _ S ≫ biprod.fst),
    derivedNatTrans (modulePushforward f) Rf af RV aV
      (pushforwardZeroToCover f _ _ _ S ≫ biprod.snd),
    derivedNatTrans (restrictedPushforward f U) RU aU RUV aUV
      (biprod.inl ≫ pushforwardZeroToIntersection f _ _ _ S),
    derivedNatTrans (restrictedPushforward f V) RV aV RUV aUV
      (biprod.inr ≫ pushforwardZeroToIntersection f _ _ _ S),
    RUV.rightDerivedDesc (derivedComparison (restrictedPushforward f (U ⊓ V)) RUV aUV)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) _
      (pushforwardConnectingNat f _ _ _ S Rf af), ?_⟩
  exact fun E => triangle_mem_distTriang_of_sequence f _ _ _ S Rf af RU RV RUV aU aV aUV E

end Main

section Named

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
  (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  (S : RelativeMayerVietorisSequence f iU iV iW)
  (Rf RU RV RUV : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (af : homotopyToDerived (modulePushforward f) ⟶ DerivedCategory.Qh ⋙ Rf)
  (aU : homotopyToDerived (restrictedPushforwardAlong f iU) ⟶ DerivedCategory.Qh ⋙ RU)
  (aV : homotopyToDerived (restrictedPushforwardAlong f iV) ⟶ DerivedCategory.Qh ⋙ RV)
  (aUV : homotopyToDerived (restrictedPushforwardAlong f iW) ⟶ DerivedCategory.Qh ⋙ RUV)
  [Rf.IsRightDerivedFunctor af (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RU.IsRightDerivedFunctor aU (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RV.IsRightDerivedFunctor aV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RUV.IsRightDerivedFunctor aUV (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- Restriction of the derived direct image to the first member of the cover: the derived
functor of the first component of the degree-zero restriction map of the relative
Mayer--Vietoris sequence. -/
@[no_expose] public def pushforwardRestrictFst : Rf ⟶ RU :=
  derivedNatTrans (modulePushforward f) Rf af RU aU
    (pushforwardZeroToCover f iU iV iW S ≫ biprod.fst)

/-- Restriction of the derived direct image to the second member of the cover. -/
@[no_expose] public def pushforwardRestrictSnd : Rf ⟶ RV :=
  derivedNatTrans (modulePushforward f) Rf af RV aV
    (pushforwardZeroToCover f iU iV iW S ≫ biprod.snd)

/-- Restriction to the intersection from the first member of the cover: the derived functor of
the first component of the degree-zero difference map of the relative Mayer--Vietoris
sequence. -/
@[no_expose] public def pushforwardDiffFst : RU ⟶ RUV :=
  derivedNatTrans (restrictedPushforwardAlong f iU) RU aU RUV aUV
    (biprod.inl ≫ pushforwardZeroToIntersection f iU iV iW S)

/-- Restriction to the intersection from the second member of the cover, with the sign that
makes the composite with the two restrictions vanish. -/
@[no_expose] public def pushforwardDiffSnd : RV ⟶ RUV :=
  derivedNatTrans (restrictedPushforwardAlong f iV) RV aV RUV aUV
    (biprod.inr ≫ pushforwardZeroToIntersection f iU iV iW S)

/-- The connecting map of the relative Mayer--Vietoris triangle, obtained by descending the
connecting map of the short exact sequence of complexes through the universal property of the
right derived functor on the intersection. -/
@[no_expose] public def pushforwardDelta : RUV ⟶ Rf ⋙
    shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ) :=
  have := isRightDerivedFunctor_derivedComparison (restrictedPushforwardAlong f iW) RUV aUV
  RUV.rightDerivedDesc (derivedComparison (restrictedPushforwardAlong f iW) RUV aUV)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (pushforwardConnectingNat f iU iV iW S Rf af)

/-- **The relative Mayer--Vietoris triangle with named morphisms.**  At an object `E` of the
unbounded derived category of the source, the triangle
`Rf_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V}) ⟶ (Rf_* E)⟦1⟧` assembled from the four
restriction maps and the connecting map. -/
public def pushforwardTriangle
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  Triangle.mk
    (biprod.lift ((pushforwardRestrictFst f iU iV iW S Rf RU af aU).app E)
      ((pushforwardRestrictSnd f iU iV iW S Rf RV af aV).app E))
    (biprod.desc ((pushforwardDiffFst f iU iV iW S RU RUV aU aUV).app E)
      ((pushforwardDiffSnd f iU iV iW S RV RUV aV aUV).app E))
    ((pushforwardDelta f iU iV iW S Rf RUV af aUV).app E)

/-- The first vertex of the relative Mayer--Vietoris triangle is `Rf_*E`.  Recorded because
`pushforwardTriangle` is `no_expose`, so a consumer outside this module cannot read the vertices
off the definition. -/
public theorem pushforwardTriangle_obj₁
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E).obj₁ = Rf.obj E := rfl

/-- The second vertex of the relative Mayer--Vietoris triangle is the biproduct of the two
restricted direct images. -/
public theorem pushforwardTriangle_obj₂
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E).obj₂ =
      (RU.obj E ⊞ RV.obj E) := rfl

/-- The third vertex of the relative Mayer--Vietoris triangle is the direct image restricted to
the intersection of the two members of the cover. -/
public theorem pushforwardTriangle_obj₃
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E).obj₃ = RUV.obj E := rfl

/-- **Stacks 08HZ with named morphisms.**  The relative Mayer--Vietoris triangle assembled
from the four restriction maps and the connecting map is distinguished at every object of the
unbounded derived category. -/
public theorem pushforwardTriangle_distinguished
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) := by
  have := isRightDerivedFunctor_derivedComparison (restrictedPushforwardAlong f iW) RUV aUV
  exact triangle_mem_distTriang_of_sequence f iU iV iW S Rf af RU RV RUV aU aV aUV E

/-- The relative Mayer--Vietoris triangle is functorial in the derived object: a morphism
`e : E ⟶ E'` induces a morphism of triangles whose components are the four derived functors
applied to `e`. -/
@[no_expose, stacks 08HZ "functoriality of the triangle in `E`: the lemma's second \
assertion, which the existential form above cannot express because it hides the morphisms"]
public def pushforwardTriangleMap
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (e : E ⟶ E') :
    pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E ⟶
      pushforwardTriangle f iU iV iW S Rf RU RV RUV af aU aV aUV E' :=
  Triangle.homMk _ _ (Rf.map e) (biprod.map (RU.map e) (RV.map e)) (RUV.map e)
    (by
      have h₁ := (pushforwardRestrictFst f iU iV iW S Rf RU af aU).naturality e
      have h₂ := (pushforwardRestrictSnd f iU iV iW S Rf RV af aV).naturality e
      dsimp only [pushforwardTriangle, Triangle.mk_mor₁]
      refine biprod.hom_ext _ _ ?_ ?_ <;> simp [h₁, h₂])
    (by
      have h₁ := (pushforwardDiffFst f iU iV iW S RU RUV aU aUV).naturality e
      have h₂ := (pushforwardDiffSnd f iU iV iW S RV RUV aV aUV).naturality e
      dsimp only [pushforwardTriangle, Triangle.mk_mor₂]
      refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [h₁, h₂])
    (by
      have h := (pushforwardDelta f iU iV iW S Rf RUV af aUV).naturality e
      dsimp only [pushforwardTriangle, Triangle.mk_mor₃] at *
      simpa only [Functor.comp_map] using h.symm)

end Named

end Stacks.Cohomology.RelativeMayerVietoris

end


-- ===== the canonical sequence in degree zero =====

/-!
# The restriction maps of the triangle, for the canonical Mayer--Vietoris sequence

The maps of `Stacks.Cohomology.RelativeMayerVietoris.pushforwardTriangle` are the right derived
functors of the degree-zero maps of a `RelativeMayerVietorisSequence`, and for an arbitrary such
sequence nothing identifies them: the structure asserts only exactness.  For the canonical
sequence `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisSequence` of Stacks 01EC
they are identified here with the right derived functors of the unit-induced restriction of a
direct image along an open immersion, which is what lets two such triangles be compared.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardUnit`: the unit-induced
  restriction `f_* ⟶ i^* ⋙ (i ≫ f)_*` of a direct image along an open immersion.
* `Stacks.Cohomology.RelativeMayerVietoris.derivedPushforwardNatTrans`: the natural
  transformation of right derived functors induced by one of the underived functors.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.pushforwardRestrictFst_relativeMayerVietorisSequence`
  and `pushforwardRestrictSnd_relativeMayerVietorisSequence`: for the canonical sequence the two
  restriction maps of the triangle are the right derived functors of `restrictedPushforwardUnit`.

## Implementation notes

The two presentations of the restricted pushforward differ: the canonical degree-zero maps of
Stacks 01EC live on `restrictedPushforwardOpen f U = restrictPush U ⋙ f_*`, while the triangle
lives on `restrictedPushforwardAlong f i = i^* ⋙ (i ≫ f)_*`.  The passage between them is
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardOpenIso` in degree zero, which is
why these statements belong here rather than with the long exact sequence: the degree-zero
identification used by the triangle is `restrictedPushforwardRightDerivedZeroIso`, which is
private to this file.

## References

* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

attribute [local instance] HasDerivedCategory.standard

section CanonicalZero

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The unit-induced restriction of a direct image along an open immersion: restriction of
`f_*M` to the image of `i`, read as a map `f_* ⟶ i^* ⋙ (i ≫ f)_*`. -/
public noncomputable def restrictedPushforwardUnit
    (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    modulePushforward f ⟶ restrictedPushforwardAlong f i :=
  pushforwardCoverUnit f (immImage i) ≫ (restrictedPushforwardOpenIso f i).hom

variable (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
  [SheafedSpace.IsOpenImmersion iW]
  (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
  (intersection : Set.range iW.hom.base = Set.range iU.hom.base ∩ Set.range iV.hom.base)

/-- **The degree-zero restriction of the canonical sequence to the first member of the cover, in
the `restrictedPushforwardAlong` presentation.**  This is the degree-zero restriction map of
Stacks 01EC read through `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
public theorem toCover_zero_comp_fst_comp_rightDerivedZeroIsoSelf :
    (modulePushforward f).toRightDerivedZero ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toCover 0 ≫ biprod.fst ≫
          Functor.whiskerLeft (modulePullback iU)
            (Functor.rightDerivedZeroIsoSelf (modulePushforward (iU ≫ f))).hom =
      restrictedPushforwardUnit f iU := by
  rw [reassoc_of% (relativeMayerVietorisSequence_toCover_zero_comp_fst f iU iV iW cover
    intersection)]
  dsimp only [restrictedPushforwardToZero, restrictedPushforwardUnit]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id, Functor.whiskerLeft_id', Category.comp_id]

/-- **The degree-zero restriction of the canonical sequence to the second member of the
cover.** -/
public theorem toCover_zero_comp_snd_comp_rightDerivedZeroIsoSelf :
    (modulePushforward f).toRightDerivedZero ≫
        (relativeMayerVietorisSequence f iU iV iW cover intersection).toCover 0 ≫ biprod.snd ≫
          Functor.whiskerLeft (modulePullback iV)
            (Functor.rightDerivedZeroIsoSelf (modulePushforward (iV ≫ f))).hom =
      restrictedPushforwardUnit f iV := by
  rw [reassoc_of% (relativeMayerVietorisSequence_toCover_zero_comp_snd f iU iV iW cover
    intersection)]
  dsimp only [restrictedPushforwardToZero, restrictedPushforwardUnit]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id, Functor.whiskerLeft_id', Category.comp_id]

/-- The degree-zero restriction map of the canonical sequence, as the triangle reads it, is the
unit-induced restriction to the first member of the cover. -/
private lemma pushforwardZeroToCover_comp_fst :
    pushforwardZeroToCover f iU iV iW
          (relativeMayerVietorisSequence f iU iV iW cover intersection) ≫ biprod.fst =
      restrictedPushforwardUnit f iU := by
  dsimp only [pushforwardZeroToCover, pushforwardRightDerivedZeroIso,
    restrictedPushforwardPairRightDerivedZeroIso, restrictedPushforwardRightDerivedZeroIso]
  simp only [Category.assoc, biprod.mapIso_inv, Iso.symm_inv, biprod.map_fst,
    Functor.rightDerivedZeroIsoSelf_inv, Functor.isoWhiskerLeft_hom]
  exact toCover_zero_comp_fst_comp_rightDerivedZeroIsoSelf f iU iV iW cover intersection

/-- The same for the second member of the cover. -/
private lemma pushforwardZeroToCover_comp_snd :
    pushforwardZeroToCover f iU iV iW
          (relativeMayerVietorisSequence f iU iV iW cover intersection) ≫ biprod.snd =
      restrictedPushforwardUnit f iV := by
  dsimp only [pushforwardZeroToCover, pushforwardRightDerivedZeroIso,
    restrictedPushforwardPairRightDerivedZeroIso, restrictedPushforwardRightDerivedZeroIso]
  simp only [Category.assoc, biprod.mapIso_inv, Iso.symm_inv, biprod.map_snd,
    Functor.rightDerivedZeroIsoSelf_inv, Functor.isoWhiskerLeft_hom]
  exact toCover_zero_comp_snd_comp_rightDerivedZeroIsoSelf f iU iV iW cover intersection

end CanonicalZero

section Derived

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The natural transformation of right derived functors induced by a natural transformation of
the underived functors they are derived from. -/
@[no_expose] public noncomputable def derivedPushforwardNatTrans
    (F G : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
    [F.Additive] [G.Additive]
    (R T : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (a : homotopyToDerived F ⟶ DerivedCategory.Qh ⋙ R)
    (b : homotopyToDerived G ⟶ DerivedCategory.Qh ⋙ T)
    [R.IsRightDerivedFunctor a (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (α : F ⟶ G) : R ⟶ T :=
  derivedNatTrans F R a T b α

variable (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
  [SheafedSpace.IsOpenImmersion iW]
  (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
  (intersection : Set.range iW.hom.base = Set.range iU.hom.base ∩ Set.range iV.hom.base)
  (Rf RU RV : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
  (af : homotopyToDerived (modulePushforward f) ⟶ DerivedCategory.Qh ⋙ Rf)
  (aU : homotopyToDerived (restrictedPushforwardAlong f iU) ⟶ DerivedCategory.Qh ⋙ RU)
  (aV : homotopyToDerived (restrictedPushforwardAlong f iV) ⟶ DerivedCategory.Qh ⋙ RV)
  [Rf.IsRightDerivedFunctor af (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **The first restriction map of the Mayer--Vietoris triangle of the canonical sequence.**  It
is the right derived functor of the unit-induced restriction of a direct image to the first
member of the cover; in particular it does not depend on a choice of Mayer--Vietoris
sequence. -/
public theorem pushforwardRestrictFst_relativeMayerVietorisSequence :
    pushforwardRestrictFst f iU iV iW
        (relativeMayerVietorisSequence f iU iV iW cover intersection) Rf RU af aU =
      derivedPushforwardNatTrans (modulePushforward f) (restrictedPushforwardAlong f iU) Rf RU
        af aU (restrictedPushforwardUnit f iU) := by
  dsimp only [pushforwardRestrictFst, derivedPushforwardNatTrans]
  rw [pushforwardZeroToCover_comp_fst]

/-- **The second restriction map of the Mayer--Vietoris triangle of the canonical
sequence.** -/
public theorem pushforwardRestrictSnd_relativeMayerVietorisSequence :
    pushforwardRestrictSnd f iU iV iW
        (relativeMayerVietorisSequence f iU iV iW cover intersection) Rf RV af aV =
      derivedPushforwardNatTrans (modulePushforward f) (restrictedPushforwardAlong f iV) Rf RV
        af aV (restrictedPushforwardUnit f iV) := by
  dsimp only [pushforwardRestrictSnd, derivedPushforwardNatTrans]
  rw [pushforwardZeroToCover_comp_snd]

end Derived

end Stacks.Cohomology.RelativeMayerVietoris

end
