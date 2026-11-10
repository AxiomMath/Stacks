module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

set_option maxRecDepth 4096

/-!
# Derived tensor product and change of rings

Let `f : R →+* A` be a homomorphism of commutative rings and let `N` be a complex of
`A`-modules. Tensoring a complex of `R`-modules with `N` over `R` produces a complex of
`A`-modules, and this construction has an exact total left derived functor `- ⊗ᴸ_R N` from
`D(R)` to `D(A)`. It agrees with derived extension of scalars along `f` followed by derived
tensoring with `N` over `A`.

The three derived functors involved are pinned down by their left-derived universal properties
along the localization functors from cochain complexes, which is what makes them independent of
the K-flat resolutions used to construct them; the change-of-rings isomorphism is required to
be compatible with the three counits, and that compatibility determines it uniquely.

The ring universes of `R` and `A` are independent, and the module universe is independent of
both: a complex over `R` and a complex over `A` must live in one module universe, so that
universe is taken above both ring universes.

## Main definitions

* `CochainComplex.DerivedTensor.DerivedTensorChangeOfRings`: the derived tensor product
  `- ⊗ᴸ_R N` together with derived extension of scalars, derived tensoring over `A`, their
  three counits, and the change-of-rings isomorphism normalized by those counits.
* `CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings`: the construction of such
  a bundle for every `f` and every `N`.
* `CochainComplex.DerivedTensor.DerivedTensorChangeOfRings.map`: the map of derived tensor
  functors induced by a map of the fixed right-hand factor, characterized by the counits.
* `CochainComplex.DerivedTensor.DerivedTensorChangeOfRings.uniqueIso`: the unique
  counit-compatible isomorphism between two such bundles.

## Main results

* `CochainComplex.DerivedTensor.exists_derived_tensor_change_of_rings`: existence of the exact
  derived tensor functor, its computation on K-flat complexes, and the natural change-of-rings
  isomorphism.
* `CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat`: a
  comparison invertible on K-flat complexes exhibits a left derived functor.
* `CochainComplex.DerivedTensor.KFlatDerived.isIso_app_of_kFlat`: conversely, the counit of any
  left derived functor of a homotopy-invariant functor is invertible on K-flat complexes.
* `CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp`: derived
  extension of scalars is absolute, that is, its left-derived universal property survives
  arbitrary postcomposition with the counit whiskered along.
* `CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat`: the counit of
  derived extension of scalars is invertible on K-flat complexes.

## Implementation notes

The derived categories are instance arguments `[HasDerivedCategory.{w} _]` throughout rather
than fixed to `HasDerivedCategory.standard`, so the constructions apply to every model of the
derived category.

The K-flat complexes resolve every object of the homotopy category, so the inclusion of the
K-flat objects is a left derivability structure. That gives, for any functor inverting the
quasi-isomorphisms between K-flat complexes, a total left derived functor whose counit is
invertible on K-flat complexes, and conversely identifies any such comparison as universal.
Exactness of `- ⊗ᴸ_R N` follows because the fixed factor may be replaced by a K-flat
resolution, after which tensoring is already exact on the homotopy category.

Identifying the underlying `R`-complex of the `A`-valued construction uses the projection
formula `V ⊗_A (A ⊗_R W) ≅ V ⊗_R W` for a ring map `R → A`, spelled out degreewise on the
antidiagonal summands of the total complex, together with the signed interchange of the two
differentials.

## References

* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.LocalizerMorphism CategoryTheory.MonoidalCategory
open CategoryTheory.LeftDerivedByResolutions
open scoped TensorProduct ChangeOfRings

namespace CochainComplex.DerivedTensor

section Interface

universe uR uA v wR wA

/-- A normalized model of derived tensor product and change of rings. The counits are
part of the data: the change-of-rings isomorphism must commute with them. -/
public structure DerivedTensorChangeOfRings
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] where
  /-- The direct, `A`-valued tensor-total functor. -/
  directTensor : CochainComplex (ModuleCat.{max v uR uA} R) ℤ ⥤
    CochainComplex (ModuleCat.{max v uR uA} A) ℤ
  /-- Its underlying complex is the tensor total over `R`. -/
  directTensorUnderlying : directTensor ⋙ restrictScalarsLarge f ≅
    tensorRightLarge.{uR, max v uA} ((restrictScalarsLarge f).obj N)
  /-- The ordinary change-of-rings comparison. -/
  directTensorComparison : directTensor ≅ extendScalarsLarge f ⋙ tensorRightLarge.{uA, max v uR} N
  /-- Derived direct tensor product. -/
  F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A)
  /-- Derived extension of scalars. -/
  B : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A)
  /-- Derived tensor product over `A`. -/
  G : DerivedCategory (ModuleCat.{max v uR uA} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A)
  /-- Compatibility with shifts. -/
  commShift : F.CommShift ℤ
  /-- Exactness of derived tensor product. -/
  isTriangulated : letI := commShift; F.IsTriangulated
  /-- The direct tensor counit. -/
  alphaF : DerivedCategory.Q ⋙ F ⟶ directTensor ⋙ DerivedCategory.Q
  /-- The extension-of-scalars counit. -/
  alphaB : DerivedCategory.Q ⋙ B ⟶ extendScalarsLarge f ⋙ DerivedCategory.Q
  /-- The tensor counit over `A`. -/
  alphaG : DerivedCategory.Q ⋙ G ⟶ tensorRightLarge.{uA, max v uR} N ⋙ DerivedCategory.Q
  /-- The direct tensor universal property. -/
  isLeftDerivedF : F.IsLeftDerivedFunctor alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
  /-- The extension-of-scalars universal property. -/
  isLeftDerivedB : B.IsLeftDerivedFunctor alphaB
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
  /-- The tensor universal property over `A`. -/
  isLeftDerivedG : G.IsLeftDerivedFunctor alphaG
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} A) (ComplexShape.up ℤ))
  /-- K-flat complexes compute the direct derived tensor product. -/
  isIso_alphaF (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : KFlat.{uR, max v uA} K) : IsIso (alphaF.app K)
  /-- Derived change of rings. -/
  changeOfRings : F ≅ B ⋙ G
  /-- Its normalization by the three specified counits and the ordinary comparison. -/
  changeOfRings_coherence :
    Functor.whiskerLeft DerivedCategory.Q changeOfRings.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight alphaB G ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (extendScalarsLarge f) alphaG ≫
        (Functor.associator _ _ _).inv =
      alphaF ≫ Functor.whiskerRight directTensorComparison.hom DerivedCategory.Q

attribute [instance] DerivedTensorChangeOfRings.isLeftDerivedF
  DerivedTensorChangeOfRings.isLeftDerivedB DerivedTensorChangeOfRings.isLeftDerivedG
  DerivedTensorChangeOfRings.commShift DerivedTensorChangeOfRings.isTriangulated

namespace DerivedTensorChangeOfRings

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] {f : R →+* A}
  {L N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ}
  [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]

/-- The ordinary map of direct tensor functors induced by a map of right factors. -/
public noncomputable def directTensorMap (S : DerivedTensorChangeOfRings f L)
    (T : DerivedTensorChangeOfRings f N) (r : L ⟶ N) : S.directTensor ⟶ T.directTensor :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
  letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR}
  S.directTensorComparison.hom ≫
    Functor.whiskerLeft (extendScalarsLarge f)
      ((curriedTensor (ModuleCat.{max v uR uA} A)).map₂CochainComplex.flip.map r) ≫
    T.directTensorComparison.inv

/-- The induced map on derived tensor functors, defined by the right Kan universal property. -/
public noncomputable def map (S : DerivedTensorChangeOfRings f L)
    (T : DerivedTensorChangeOfRings f N) (r : L ⟶ N) : S.F ⟶ T.F :=
  Functor.leftDerivedNatTrans S.F T.F S.alphaF T.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
    (Functor.whiskerRight (S.directTensorMap T r) DerivedCategory.Q)

/-- The induced map is normalized by the specified counits. -/
@[reassoc]
public theorem map_fac (S : DerivedTensorChangeOfRings f L)
    (T : DerivedTensorChangeOfRings f N) (r : L ⟶ N) :
    Functor.whiskerLeft DerivedCategory.Q (S.map T r) ≫ T.alphaF =
      S.alphaF ≫ Functor.whiskerRight (S.directTensorMap T r) DerivedCategory.Q :=
  Functor.leftDerivedNatTrans_fac _ _ _ _ _ _

/-- This normalization determines the map uniquely. -/
public theorem map_unique (S : DerivedTensorChangeOfRings f L)
    (T : DerivedTensorChangeOfRings f N) (r : L ⟶ N) (t : S.F ⟶ T.F)
    (ht : Functor.whiskerLeft DerivedCategory.Q t ≫ T.alphaF =
      S.alphaF ≫ Functor.whiskerRight (S.directTensorMap T r) DerivedCategory.Q) :
    t = S.map T r :=
  Functor.leftDerived_ext T.F T.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
    S.F t (S.map T r) (ht.trans (S.map_fac T r).symm)

/-- The counit with values in extension of scalars followed by ordinary tensoring. -/
public noncomputable def directCounit (T : DerivedTensorChangeOfRings f N) :
    DerivedCategory.Q ⋙ T.F ⟶
      (extendScalarsLarge f ⋙ tensorRightLarge.{uA, max v uR} N) ⋙ DerivedCategory.Q :=
  T.alphaF ≫ Functor.whiskerRight T.directTensorComparison.hom DerivedCategory.Q

/-- The counit of the composite of the two derived functors. -/
public noncomputable def compositeCounit (T : DerivedTensorChangeOfRings f N) :
    DerivedCategory.Q ⋙ (T.B ⋙ T.G) ⟶
      (extendScalarsLarge f ⋙ tensorRightLarge.{uA, max v uR} N) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight T.alphaB T.G ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (extendScalarsLarge f) T.alphaG ≫
    (Functor.associator _ _ _).inv

/-- The comparison with extension of scalars followed by tensoring is again a left derived
functor counit: it differs from `alphaF` by the change-of-rings isomorphism of complexes. -/
public instance isLeftDerived_directCounit (T : DerivedTensorChangeOfRings f N) :
    T.F.IsLeftDerivedFunctor T.directCounit
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  rw [← Functor.isRightKanExtension_iff_of_iso₂ T.alphaF T.directCounit
    (Functor.isoWhiskerRight T.directTensorComparison DerivedCategory.Q) (Iso.refl T.F)
    (by simp [directCounit])]
  exact Functor.IsLeftDerivedFunctor.isRightKanExtension T.F T.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))

/-- The coherence equation is also the universal normalization of the composite counit. -/
public theorem changeOfRings_fac (T : DerivedTensorChangeOfRings f N) :
    Functor.whiskerLeft DerivedCategory.Q T.changeOfRings.hom ≫ T.compositeCounit =
      T.directCounit := by
  simpa only [compositeCounit, directCounit, Category.assoc] using T.changeOfRings_coherence

/-- The composite of the two derived functors, with its composite counit, is a left derived
functor of the same functor on complexes. -/
public instance isLeftDerived_compositeCounit (T : DerivedTensorChangeOfRings f N) :
    (T.B ⋙ T.G).IsLeftDerivedFunctor T.compositeCounit
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) :=
  (Functor.isLeftDerivedFunctor_iff_of_iso T.directCounit T.compositeCounit
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
    T.changeOfRings T.changeOfRings_fac).mp inferInstance

/-- There is only one change-of-rings isomorphism satisfying the specified normalization. -/
public theorem changeOfRings_unique (T : DerivedTensorChangeOfRings f N) (e : T.F ≅ T.B ⋙ T.G)
    (he : Functor.whiskerLeft DerivedCategory.Q e.hom ≫ T.compositeCounit = T.directCounit) :
    e = T.changeOfRings :=
  Iso.ext <| Functor.leftDerived_ext (T.B ⋙ T.G) T.compositeCounit
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
    T.F e.hom T.changeOfRings.hom (he.trans T.changeOfRings_fac.symm)

/-- Two normalized models are identified by the unique counit-compatible isomorphism. -/
public noncomputable def uniqueIso (S T : DerivedTensorChangeOfRings f N) : S.F ≅ T.F :=
  Functor.leftDerivedNatIso S.F T.F S.directCounit T.directCounit
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)) (Iso.refl _)

/-- The comparison isomorphism between two bundles is compatible with their counits. -/
public theorem uniqueIso_fac (S T : DerivedTensorChangeOfRings f N) :
    Functor.whiskerLeft DerivedCategory.Q (S.uniqueIso T).hom ≫ T.directCounit =
      S.directCounit := by
  simp [uniqueIso]

/-- Only one isomorphism of derived tensor functors is compatible with the two counits. -/
public theorem uniqueIso_unique (S T : DerivedTensorChangeOfRings f N) (e : S.F ≅ T.F)
    (he : Functor.whiskerLeft DerivedCategory.Q e.hom ≫ T.directCounit = S.directCounit) :
    e = S.uniqueIso T :=
  Iso.ext <| Functor.leftDerived_ext T.F T.directCounit
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))
    S.F e.hom (S.uniqueIso T).hom (he.trans (S.uniqueIso_fac T).symm)

/-- A homogeneous tensor in the direct construction, transported through its named ordinary
comparison. These elements specify the ordinary associator and the signed interchange. -/
public noncomputable def tensorElement (T : DerivedTensorChangeOfRings f N)
    (M : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : M.X i) (y : N.X j) :
    (T.directTensor.obj M).X n :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
  letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR}
  (T.directTensorComparison.inv.app M).f n
    (HomologicalComplex.ιTensorObj ((extendScalarsLarge f).obj M) N i j n h
      (((1 : A) ⊗ₜ[R,f] x) ⊗ₜ[A] y))

end DerivedTensorChangeOfRings
end Interface

section Construction

universe v₁ v₂ v₃ u₁ u₂ u₃


section TensorSymmetry

open CategoryTheory.MonoidalCategory HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
  [∀ K L : CochainComplex C ℤ,
    HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
/-- The symmetry on modules and the signed interchange of the two differentials
identify left and right tensoring by a complex. -/
private noncomputable def tleftCochainIsoTrightCochain
    (e : curriedTensor C ≅ (curriedTensor C).flip) (N : CochainComplex C ℤ) :
    TleftCochain N ≅ TrightCochain N :=
  NatIso.ofComponents (fun K =>
    mapBifunctorIso e N K ≪≫ HomologicalComplex.mapBifunctorFlipIso K N
      (curriedTensor C) (.up ℤ)) (fun {K L} f => by
        change mapBifunctorMap (𝟙 N) f (curriedTensor C) (.up ℤ) ≫
            (mapBifunctorIso e N L).hom ≫
              (HomologicalComplex.mapBifunctorFlipIso L N (curriedTensor C) (.up ℤ)).hom = _
        rw [reassoc_of% mapBifunctorIso_hom_naturality e (𝟙 N) f,
          HomologicalComplex.mapBifunctorFlipIso_hom_naturality]
        simp only [Iso.trans_hom, Category.assoc]
        rfl)

/-- Left tensoring by a fixed complex acts on the antidiagonal summand `N^i ⊗ K^j` by the
identity on `N^i` and the given map on `K^j`. -/
private lemma ι_tleftCochain_map
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ K L : CochainComplex C ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (ComplexShape.up ℤ)]
    (N : CochainComplex C ℤ) {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj N K i j n h ≫ ((TleftCochain N).map g).f n =
      (N.X i ◁ g.f j) ≫ HomologicalComplex.ιTensorObj N L i j n h := by
  change HomologicalComplex.ιMapBifunctor N K (curriedTensor C) (ComplexShape.up ℤ) i j n h ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 N) g (curriedTensor C)
      (ComplexShape.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

end TensorSymmetry


section KFlatResolutions

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory HomologicalComplex

universe u v w

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- The tensor product of modules is symmetric: the bifunctor agrees with its flip. -/
private noncomputable def moduleTensorCommIso {R : Type u} [CommRing R] :
    curriedTensor (ModuleCat.{max u v} R) ≅ (curriedTensor (ModuleCat.{max u v} R)).flip :=
  NatIso.ofComponents (fun M => NatIso.ofComponents
    (fun N => (TensorProduct.comm R M N).toModuleIso)
    (by intros; ext : 1; apply TensorProduct.ext'; intros; rfl))
    (by intros; ext N : 3; apply TensorProduct.ext'; intros; rfl)

/-- The chosen lift of a quasi-isomorphism of the homotopy category is a quasi-isomorphism. -/
private lemma quasiIso_out_of_quasiIso {C : Type*} [Category C] [Abelian C]
    {X Y : HomotopyCategory C (.up ℤ)} {s : X ⟶ Y}
    (hs : HomotopyCategory.quasiIso C (.up ℤ) s) : QuasiIso s.out :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff s.out).1 (by
    rwa [HomotopyCategory.quotient_map_out s])

/-- Naturally isomorphic functors to complexes have the same quasi-isomorphic images. -/
private lemma quasiIso_map_iff_of_iso {C D : Type*} [Category C] [Category D] [Abelian D]
    {F G : C ⥤ CochainComplex D ℤ} (e : F ≅ G) {X Y : C} (s : X ⟶ Y) :
    QuasiIso (F.map s) ↔ QuasiIso (G.map s) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality s).symm)

/-- Right tensoring on the homotopy category inverts exactly the maps whose representatives
tensor to quasi-isomorphisms. -/
private lemma quasiIso_tright_map_iff {R : Type u} [CommRing R]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (g : K ⟶ L) :
    HomotopyCategory.quasiIso _ (.up ℤ) ((HomotopyCategory.quotient _ _ ⋙ Tright N).map g) ↔
      QuasiIso ((TrightCochain N).map g) := by
  unfold Tright
  rw [descendF_comp_quotient]
  exact HomotopyCategory.quotient_map_mem_quasiIso_iff _

/-- Right tensoring by an arbitrary complex preserves a quasi-isomorphism between K-flat
complexes. -/
private lemma quasiIso_trightCochain_map_of_kFlat
    {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : K ⟶ L) [QuasiIso f] (hK : CochainComplex.KFlat K)
    (hL : CochainComplex.KFlat L) (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    QuasiIso ((TrightCochain N).map f) := by
  let e := tleftCochainIsoTrightCochain (moduleTensorCommIso (R := R)) N
  exact (quasiIso_map_iff_of_iso e f).1 (quasiIso_tleftCochain_map f hK hL N)

/-- Every object of the homotopy category receives a quasi-isomorphism from a K-flat complex. -/
public lemma exists_kFlat_resolution_homotopy
    {R : Type u} [CommRing R] (X : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ)) :
    ∃ (Y : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ)) (_ : CochainComplex.KFlat Y.as)
      (s : Y ⟶ X), HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ) s := by
  obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution X.as
  exact ⟨(HomotopyCategory.quotient _ _).obj K, hK,
    (HomotopyCategory.quotient _ _).map s,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩

set_option backward.isDefEq.respectTransparency false in
/-- Right tensoring, read on the homotopy category and followed by localization, inverts a
quasi-isomorphism between K-flat complexes. -/
private lemma isIso_tright_map_of_kFlat
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {X Y : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ) f)
    (hX : CochainComplex.KFlat X.as) (hY : CochainComplex.KFlat Y.as) :
    IsIso ((Tright N ⋙ DerivedCategory.Qh).map f) := by
  have := quasiIso_out_of_quasiIso hf
  have ht := quasiIso_trightCochain_map_of_kFlat f.out hX hY N
  apply (DerivedCategory.isIso_Qh_map_iff _).2
  rw [← HomotopyCategory.quotient_map_out f]
  exact (quasiIso_tright_map_iff N f.out).2 ht

/-- Right tensoring by a fixed complex has a pointwise total left derived functor, the K-flat
complexes being a resolving class. -/
private lemma hasPointwiseLeftDerivedFunctor_tright
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (Tright N ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_resolutions
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
    (fun K => CochainComplex.KFlat K.as)
    (exists_kFlat_resolution_homotopy (R := R)) _ (isIso_tright_map_of_kFlat N)

/-- K-flat complexes compute the counit of the left derived tensor functor. -/
private lemma isIso_leftDerivedTensorCounit_app
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (α : DerivedCategory.Qh ⋙ F ⟶ Tright N ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : CochainComplex.KFlat K) :
    IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) :=
  isIso_app_of_resolutions (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
    (fun K => CochainComplex.KFlat K.as)
    (exists_kFlat_resolution_homotopy (R := R)) _ (isIso_tright_map_of_kFlat N)
    DerivedCategory.Qh F α _ hK

/-- The left derived tensor functor exists and is computed on K-flat complexes. -/
private lemma exists_leftDerivedTensor
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ∃ (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
      (α : DerivedCategory.Qh ⋙ F ⟶ Tright N ⋙ DerivedCategory.Qh),
      F.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) ∧
        ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, CochainComplex.KFlat K →
          IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
  have := hasPointwiseLeftDerivedFunctor_tright N
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ)
  let U := Tright N ⋙ DerivedCategory.Qh
  exact ⟨U.totalLeftDerived DerivedCategory.Qh W,
    U.totalLeftDerivedCounit DerivedCategory.Qh W, inferInstance,
    isIso_leftDerivedTensorCounit_app N _ _⟩

/-- Tensoring on the left with a K-flat complex preserves quasi-isomorphisms. -/
private lemma quasiIso_tleftCochain_map_of_kFlat
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hK : K.KFlat) {P N : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (r : P ⟶ N) [QuasiIso r] : QuasiIso ((TleftCochain K).map r) := by
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK
    ((HomotopyCategory.quotient _ _).map r)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 (show QuasiIso r from inferInstance))
  let e := tleftCochainIsoTrightCochain (moduleTensorCommIso (R := R)) K
  exact (quasiIso_map_iff_of_iso e r).2 ((quasiIso_tright_map_iff K r).1 h)

/-- Resolving the fixed factor gives an exact tensor functor on the derived category. -/
private lemma exists_exact_leftDerivedTensor
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ∃ (G : DerivedCategory (ModuleCat.{max u v} R) ⥤
        DerivedCategory (ModuleCat.{max u v} R)) (cG : G.CommShift ℤ),
      letI := cG
      G.IsTriangulated ∧ ∃ α : DerivedCategory.Qh ⋙ G ⟶ Tright N ⋙ DerivedCategory.Qh,
        G.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
        ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, K.KFlat →
          IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
  obtain ⟨P, r, hP, _, hr, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution N
  have := hr
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ)
  let U := Tright P ⋙ DerivedCategory.Qh
  have hU : W.IsInvertedBy U := fun X Y s hs =>
    (DerivedCategory.isIso_Qh_map_iff _).2
      (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso P hP s hs)
  let G := Localization.lift U hU DerivedCategory.Qh
  let e := Localization.Lifting.iso DerivedCategory.Qh W U G
  obtain ⟨cP, htri⟩ := TotalTensorComplex.tright_isTriangulated P
  let := cP
  have := htri
  let cG := Functor.commShiftOfLocalization DerivedCategory.Qh W ℤ U G
  have hG : G.IsTriangulated := Functor.isTriangulated_of_precomp_iso e
  let α := e.hom ≫ whiskerRight (trightMap r) DerivedCategory.Qh
  have hα : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, K.KFlat →
      IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
    intro K hK
    have ht := quasiIso_tleftCochain_map_of_kFlat K hK r
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((TleftCochain K).map r))) :=
      (DerivedCategory.isIso_Qh_map_iff _).2
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
    change IsIso (e.hom.app ((HomotopyCategory.quotient _ _).obj K) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ((TleftCochain K).map r)))
    infer_instance
  refine ⟨G, cG, hG, α, ?_, hα⟩
  exact isLeftDerivedFunctor_of_isIso_on_resolutions W
    (fun K => CochainComplex.KFlat K.as) (exists_kFlat_resolution_homotopy (R := R))
    _ (isIso_tright_map_of_kFlat N) DerivedCategory.Qh G α (fun K hK => hα K.as hK)

/-- A comparison on complexes which is invertible on K-flat complexes is universal,
provided its ordinary functor descends to the homotopy category. -/
private lemma isLeftDerivedFunctor_of_isIso_on_kFlat
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {H : Type*} [Category H]
    (U : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ H)
    (Uh : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient _ _ ⋙ Uh ≅ U)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    (hβ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, K.KFlat → IsIso (β.app K)) :
    F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max u v} R) (.up ℤ)
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)
  let T := (whiskeringLeft _ _ H).obj Q
  have : T.Full := inferInstanceAs
    (((whiskeringLeft _ _ H).obj (CategoryTheory.Quotient.functor (homotopic _ _))).Full)
  let α₀ : Q ⋙ (DerivedCategory.Qh ⋙ F) ⟶ Q ⋙ Uh :=
    whiskerRight q.hom F ≫ β ≫ e.inv
  let α : DerivedCategory.Qh ⋙ F ⟶ Uh := T.preimage α₀
  have hα₀ : whiskerLeft Q α = α₀ := T.map_preimage α₀
  have hα : ∀ X : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ),
      CochainComplex.KFlat X.as → IsIso (α.app X) := by
    intro X hX
    have he : α.app X = α₀.app X.as := NatTrans.congr_app hα₀ X.as
    rw [he]
    have := hβ X.as hX
    dsimp [α₀]
    infer_instance
  have hUh : ∀ {X Y} (s : X ⟶ Y), HomotopyCategory.quasiIso _ (.up ℤ) s →
      CochainComplex.KFlat X.as → CochainComplex.KFlat Y.as → IsIso (Uh.map s) := by
    intro X Y s hs hX hY
    have := hα X hX
    have := hα Y hY
    have : IsIso (DerivedCategory.Qh.map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
    rw [← isIso_comp_left_iff (α.app X), ← α.naturality s]
    dsimp only [Functor.comp_map]
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
    (fun X => CochainComplex.KFlat X.as) (exists_kFlat_resolution_homotopy (R := R))
    Uh hUh DerivedCategory.Qh F α hα
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension F α
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
  have hk := CochainComplex.DerivedExtensionScalars.isRightKanExtension_precomp_of_fullyFaithful
    Q DerivedCategory.Qh Uh F α
  have hke : F.IsRightKanExtension (whiskerRight q.hom F ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator Q DerivedCategory.Qh F).hom ≫ whiskerLeft Q α)
      (whiskerRight q.hom F ≫ β) e (Iso.refl F) ?_).mp hk
    rw [hα₀]
    ext X
    simp [α₀]
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
    ((Q ⋙ DerivedCategory.Qh).rightUnitor ≪≫ q) β).2
  have := hke
  apply Functor.isRightKanExtension_of_iso F.leftUnitor.symm
    (whiskerRight q.hom F ≫ β)
  ext X
  simp only [comp_obj, Iso.symm_hom, Iso.trans_hom, whiskerRight_comp, Category.assoc,
    NatTrans.comp_app, id_obj, whiskerLeft_app, leftUnitor_inv_app, associator_inv_app,
    whiskerRight_app, rightUnitor_hom_app, map_id, Category.id_comp]
  exact Category.id_comp _

/-- The ordinary tensor functor and its homotopy descent agree after localization. -/
private noncomputable def quotientCompTrightIso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    HomotopyCategory.quotient _ _ ⋙ (Tright N ⋙ DerivedCategory.Qh) ≅
      TrightCochain N ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (descendF_comp_quotient (TrightCochain N)
      (TrightCochain_preservesHomotopyRel N))) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (TrightCochain N) (DerivedCategory.quotientCompQhIso _)

end KFlatResolutions

section ChangeOfRings

universe uR uA v

/-- At a module universe equal to the ring universe, large-universe K-flatness is
`CochainComplex.KFlat`. -/
private lemma kFlat_iff {R : Type uR} [CommRing R]
    (K : CochainComplex (ModuleCat.{uR} R) ℤ) :
    KFlat.{uR, 0} K ↔ CochainComplex.KFlat K := Iff.rfl

end ChangeOfRings

section ProjectionFormula

open CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe uR uA v

variable {R : Type uR} {R' : Type uA} [CommRing R] [CommRing R']

set_option maxHeartbeats 1000000 in
-- The projection formula comparison is assembled degreewise.
/-- The underlying complex of `R`-modules of the `A`-valued direct tensor construction is the
ordinary total tensor product over `R`: the comparison combines the two signed tensor
symmetries with the chain-level projection formula. -/
private noncomputable def tensorUnderlyingIso (φ : R →+* R')
    (N : CochainComplex (ModuleCat.{max v uR uA} R') ℤ) :
    (extendScalarsLarge.{v, uR, uA} φ ⋙ tensorRightLarge.{uA, max v uR} N) ⋙
        restrictScalarsLarge.{v, uR, uA} φ ≅
      tensorRightLarge.{uR, max v uA} ((restrictScalarsLarge.{v, uR, uA} φ).obj N) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  let eA := tleftCochainIsoTrightCochain (moduleTensorCommIso.{uA, max v uR} (R := R')) N
  let eR := tleftCochainIsoTrightCochain (moduleTensorCommIso.{uR, max v uA} (R := R))
    ((restrictScalarsLarge.{v, uR, uA} φ).obj N)
  exact isoWhiskerRight (isoWhiskerLeft (extendScalarsLarge.{v, uR, uA} φ) eA.symm)
    (restrictScalarsLarge.{v, uR, uA} φ) ≪≫
    NatIso.ofComponents (G := TleftCochain ((restrictScalarsLarge.{v, uR, uA} φ).obj N))
      (fun K => CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{uR, uA, v} φ K N)
      (fun g => CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso_naturality.{uR, uA, v}
        φ g N) ≪≫ eR

end ProjectionFormula

/-- Two invertible counit components give an invertible composite counit component. -/
private lemma isIso_compositeCounit_app
    {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    {D₁ : Type*} {D₂ : Type*} {D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
    (E : C₁ ⥤ C₂) (T : C₂ ⥤ C₃) (B : D₁ ⥤ D₂) (G : D₂ ⥤ D₃)
    (αB : L₁ ⋙ B ⟶ E ⋙ L₂) (αG : L₂ ⋙ G ⟶ T ⋙ L₃)
    (K : C₁) [IsIso (αB.app K)] [IsIso (αG.app (E.obj K))] :
    IsIso (((associator L₁ B G).inv ≫ whiskerRight αB G ≫
      (associator E L₂ G).hom ≫ whiskerLeft E αG ≫
      (associator E T L₃).inv).app K) := by
  simp only [NatTrans.comp_app, associator_inv_app, associator_hom_app,
    whiskerRight_app, whiskerLeft_app, Category.id_comp, Category.comp_id]
  infer_instance

universe uR uA v wR wA

set_option maxHeartbeats 2000000 in
-- The construction assembles three universal properties at independent ring universes.
/-- The exact derived tensor construction, normalized by its three counits. -/
private noncomputable def derivedTensorChangeOfRingsOfKFlatResolution
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    DerivedTensorChangeOfRings f N := by
  classical
  apply Classical.choice
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA}
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA}
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
  let : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR}
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} A) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR}
  obtain ⟨G, cG, hG, αh, hαh, hαhIso⟩ := exists_exact_leftDerivedTensor.{uA, max v uR} N
  let := cG
  have := hG
  let B := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v} f
  let cB : B.functor.CommShift ℤ := B.commShift
  have hBtri : B.functor.IsTriangulated := B.isTriangulated
  let E := extendScalarsLarge.{v, uR, uA} f
  let T := tensorRightLarge.{uA, max v uR} N
  let q := HomotopyCategory.quotient (ModuleCat.{max v uR uA} A) (.up ℤ)
  let eG := quotientCompTrightIso.{uA, max v uR} N
  let αG : DerivedCategory.Q ⋙ G ⟶ T ⋙ DerivedCategory.Q :=
    whiskerRight (DerivedCategory.quotientCompQhIso _).inv G ≫
      whiskerLeft q αh ≫ eG.hom
  have hαG : ∀ K : CochainComplex (ModuleCat.{max v uR uA} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR} K → IsIso (αG.app K) := by
    intro K hK
    have := hαhIso K hK
    dsimp [αG]
    infer_instance
  have hLG := isLeftDerivedFunctor_of_isIso_on_kFlat.{uA, max v uR} (T ⋙ DerivedCategory.Q)
    (Tright N ⋙ DerivedCategory.Qh) eG G αG hαG
  let αB : DerivedCategory.Q ⋙ B.functor ⟶ E ⋙ DerivedCategory.Q := B.comparison
  let F := B.functor ⋙ G
  let cF : F.CommShift ℤ := inferInstance
  have hFtri : F.IsTriangulated := inferInstance
  let αF : DerivedCategory.Q ⋙ F ⟶ (E ⋙ T) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ whiskerRight αB G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft E αG ≫ (Functor.associator _ _ _).inv
  have hαF : ∀ K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA} K → IsIso (αF.app K) := by
    intro K hK
    have hBK : IsIso (αB.app K) := B.comparison_isIso_of_kFlat K hK
    have hGK : IsIso (αG.app (E.obj K)) :=
      hαG (E.obj K)
        (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uA, v} f K hK)
    exact isIso_compositeCounit_app DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      E T B.functor G αB αG K
  let : (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive := by
    let := f.toAlgebra
    constructor
    intro X Y a b
    ext x
    change (1 : A) ⊗ₜ[R,f] ((a + b) x) =
      (1 : A) ⊗ₜ[R,f] a x + (1 : A) ⊗ₜ[R,f] b x
    rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]
  let Eh := (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ)
  let Uh := Eh ⋙ (Tright N ⋙ DerivedCategory.Qh)
  let eF : HomotopyCategory.quotient _ _ ⋙ Uh ≅ (E ⋙ T) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategoryFactors
        (.up ℤ))
        (Tright N ⋙ DerivedCategory.Qh) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft E eG ≪≫ (Functor.associator _ _ _).symm
  have hLF := isLeftDerivedFunctor_of_isIso_on_kFlat.{uR, max v uA} ((E ⋙ T) ⋙ DerivedCategory.Q)
    Uh eF F αF hαF
  refine ⟨{
    directTensor := E ⋙ T
    directTensorUnderlying := tensorUnderlyingIso f N
    directTensorComparison := Iso.refl _
    F := F
    B := B.functor
    G := G
    commShift := cF
    isTriangulated := hFtri
    alphaF := αF
    alphaB := αB
    alphaG := αG
    isLeftDerivedF := hLF
    isLeftDerivedB := B.isLeftDerived
    isLeftDerivedG := hLG
    isIso_alphaF := hαF
    changeOfRings := Iso.refl _
    changeOfRings_coherence := ?_ }⟩
  ext X
  simp [αF]
  rfl

end Construction

section Consequences

universe uR uA v wR wA

namespace KFlatDerived

open CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.LocalizerMorphism

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory HomologicalComplex

universe u w

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- A comparison on complexes which is invertible on K-flat complexes is universal,
provided its ordinary functor descends to the homotopy category. -/
public theorem isLeftDerivedFunctor_of_isIso_on_kFlat
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {H : Type*} [Category H]
    (U : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ H)
    (Uh : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient _ _ ⋙ Uh ≅ U)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    (hβ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, K.KFlat → IsIso (β.app K)) :
    F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)) :=
  CochainComplex.DerivedTensor.isLeftDerivedFunctor_of_isIso_on_kFlat.{u, v} U Uh e F β hβ

/-- The counit of a left derived functor of a functor that descends to the homotopy category
and inverts quasi-isomorphisms between K-flat complexes is invertible on K-flat complexes. -/
public theorem isIso_app_of_kFlat
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {H : Type*} [Category H]
    (U : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ H)
    (Uh : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient _ _ ⋙ Uh ≅ U)
    (hUh : ∀ {X Y} (s : X ⟶ Y), HomotopyCategory.quasiIso _ (.up ℤ) s →
      CochainComplex.KFlat X.as → CochainComplex.KFlat Y.as → IsIso (Uh.map s))
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    [F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ))]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (hK : K.KFlat) :
    IsIso (β.app K) := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ)
  let P : ObjectProperty (HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ)) :=
    fun X => CochainComplex.KFlat X.as
  have := hasPointwiseLeftDerivedFunctor_of_resolutions W P
    (exists_kFlat_resolution_homotopy (R := R)) Uh hUh
  let G := Uh.totalLeftDerived DerivedCategory.Qh W
  let α := Uh.totalLeftDerivedCounit DerivedCategory.Qh W
  let β₀ : DerivedCategory.Q ⋙ G ⟶ U :=
    whiskerRight (DerivedCategory.quotientCompQhIso _).inv G ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (HomotopyCategory.quotient _ _) α ≫ e.hom
  have hβ₀ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ,
      K.KFlat → IsIso (β₀.app K) := by
    intro K hK
    have := isIso_app_of_resolutions W P (exists_kFlat_resolution_homotopy (R := R))
      Uh hUh DerivedCategory.Qh G α ((HomotopyCategory.quotient _ _).obj K) hK
    dsimp [β₀]
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_on_kFlat U Uh e G β₀ hβ₀
  let i := Functor.leftDerivedUnique F G β₀ β (HomologicalComplex.quasiIso _ (.up ℤ))
  have hi : whiskerLeft DerivedCategory.Q i.hom ≫ β = β₀ := by
    simp [i, Functor.leftDerivedUnique]
  have heq : i.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = β₀.app K :=
    NatTrans.congr_app hi K
  rw [← isIso_comp_left_iff (i.hom.app (DerivedCategory.Q.obj K)), heq]
  exact hβ₀ K hK

/-- A left derived functor whose counit is invertible on K-flat complexes stays a left derived
functor, with the whiskered counit, after any postcomposition. -/
public theorem isLeftDerivedFunctor_postcomp_of_isIso_on_kFlat
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {D E : Type*} [Category D] [Category E]
    (U : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ D)
    (Uh : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ) ⥤ D)
    (e : HomotopyCategory.quotient _ _ ⋙ Uh ≅ U)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ D)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    (hβ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ, K.KFlat → IsIso (β.app K))
    (H : D ⥤ E) :
    (F ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q F H).inv ≫ whiskerRight β H)
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
  apply isLeftDerivedFunctor_of_isIso_on_kFlat (U ⋙ H) (Uh ⋙ H)
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e H)
  intro K hK
  have := hβ K hK
  dsimp
  infer_instance

set_option maxHeartbeats 800000 in
-- The single-complex comparison is checked on every antidiagonal summand.
/-- Tensoring degreewise with a module is naturally isomorphic to tensoring with the complex
concentrated in degree `0` and totalizing. -/
noncomputable def tensorLeftMapComplexIso
    {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R) :
    (tensorLeft N).mapHomologicalComplex (.up ℤ) ≅
      TleftCochain ((CochainComplex.singleFunctor _ 0).obj N) :=
  NatIso.ofComponents (fun K =>
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => CochainComplex.DerivedExtensionScalars.single_tlmHC_comps N K n)
      (fun i j hij =>
        CochainComplex.DerivedExtensionScalars.single_tlmHC_comm N K i j hij)).symm) (by
    intro K L f
    ext n : 1
    change _ ≫ HomologicalComplex.ιMapBifunctor
        ((CochainComplex.singleFunctor _ 0).obj N) L
        (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ) 0 n n (zero_add n) =
      HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor _ 0).obj N) K
        (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ) 0 n n (zero_add n) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 _) f
          (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ)).f n
    rw [HomologicalComplex.ι_mapBifunctorMap]
    change (N ◁ f.f n) ≫ _ = (𝟙 N ▷ K.X n) ≫ (N ◁ f.f n) ≫ _
    rw [id_whiskerRight, Category.id_comp])

end

section Extension

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory HomologicalComplex

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- Extension of scalars along a bare ring homomorphism is additive. -/
local instance extensionAdditive :
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : A) ⊗ₜ[R,f] ((a + b) x) =
    (1 : A) ⊗ₜ[R,f] a x + (1 : A) ⊗ₜ[R,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

/-- Extension of scalars along `f` followed by restriction of scalars is tensoring with `A`,
regarded as an `R`-module in the common module universe. -/
private noncomputable def extensionUnderlyingIso :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA}
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA}
    let N := (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max v uR} A))
    ModuleCat.extendScalars.{uR, uA, max v uR uA} f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft N := by
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA}
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA}
  letI := f.toAlgebra
  exact NatIso.ofComponents (fun M =>
    (TensorProduct.congr (ULift.moduleEquiv : ULift.{max v uR} A ≃ₗ[R] A)
      (LinearEquiv.refl R M)).symm.toModuleIso) (by
        intros
        ext : 1
        apply TensorProduct.ext'
        intros
        rfl)

/-- Extension of scalars preserves quasi-isomorphisms between K-flat complexes. -/
@[ega "III 6.10.3" "(ii), special case"]
public theorem quasiIso_extendScalars_map_of_kFlat
    {K L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ} (s : K ⟶ L)
    [QuasiIso s] (hK : CochainComplex.KFlat.{uR, max v uA} K)
    (hL : CochainComplex.KFlat.{uR, max v uA} L) :
    QuasiIso ((extendScalarsLarge f).map s) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA}
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA}
  let N := (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max v uR} A))
  let e : extendScalarsLarge f ⋙ restrictScalarsLarge f ≅
      TleftCochain ((CochainComplex.singleFunctor _ 0).obj N) :=
    Functor.mapHomologicalComplexCompIso (extensionUnderlyingIso f) (.up ℤ) ≪≫
      tensorLeftMapComplexIso.{max v uA, uR} N
  have ht := quasiIso_tleftCochain_map.{uR, max v uA} s hK hL
    ((CochainComplex.singleFunctor _ 0).obj N)
  have he : QuasiIso ((extendScalarsLarge f ⋙ restrictScalarsLarge f).map s) :=
    (quasiIso_map_iff_of_iso e s).2 ht
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((extendScalarsLarge f).map s) (ModuleCat.restrictScalars f)).1 he

/-- Degreewise extension of scalars read on the homotopy category, followed by localization. -/
private noncomputable abbrev extensionHomotopy
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :=
  (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-category form of extension of scalars factors the complex-level one. -/
private noncomputable def extensionHomotopyFactors
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    HomotopyCategory.quotient _ _ ⋙ extensionHomotopy f ≅
      extendScalarsLarge f ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategoryFactors
      (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (extendScalarsLarge f) (DerivedCategory.quotientCompQhIso _)

/-- Extension of scalars, read on the homotopy category and localized, inverts a
quasi-isomorphism between K-flat complexes. -/
private lemma isIso_extensionHomotopy_map
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    {X Y : HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ)} (s : X ⟶ Y)
    (hs : HomotopyCategory.quasiIso _ (.up ℤ) s)
    (hX : CochainComplex.KFlat.{uR, max v uA} X.as)
    (hY : CochainComplex.KFlat.{uR, max v uA} Y.as) :
    IsIso ((extensionHomotopy f).map s) := by
  have := quasiIso_out_of_quasiIso hs
  have := quasiIso_extendScalars_map_of_kFlat f s.out hX hY
  have : IsIso ((extendScalarsLarge f ⋙ DerivedCategory.Q).map s.out) := by
    dsimp
    infer_instance
  have : IsIso ((HomotopyCategory.quotient _ _ ⋙ extensionHomotopy f).map s.out) := by
    rw [← NatIso.naturality_2 (extensionHomotopyFactors f) s.out]
    dsimp
    infer_instance
  simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using this

/-- The counit of any total derived extension of scalars is invertible on K-flat
complexes. -/
public theorem isIso_extensionCounit_app_of_kFlat
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶ extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    IsIso (comparison.app K) :=
  isIso_app_of_kFlat.{max v uA, uR} _ (extensionHomotopy f) (extensionHomotopyFactors f)
    (isIso_extensionHomotopy_map f) F comparison K hK

/-- Derived extension of scalars is absolute: arbitrary postcomposition preserves
its left derived universal property with the original, whiskered counit. -/
public theorem isLeftDerivedFunctor_extension_postcomp
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶ extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ))]
    {E : Type*} [Category E] (H : DerivedCategory (ModuleCat.{max v uR uA} A) ⥤ E) :
    (F ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q F H).inv ≫ whiskerRight comparison H)
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ)) :=
  isLeftDerivedFunctor_postcomp_of_isIso_on_kFlat.{max v uA, uR} _ (extensionHomotopy f)
    (extensionHomotopyFactors f) F comparison (isIso_extensionCounit_app_of_kFlat f F comparison) H

end Extension

end KFlatDerived

/-- The derived tensor product `- ⊗ᴸ_R N` from `D(R)` to `D(A)`, with derived extension of
scalars, derived tensoring over `A` and the change-of-rings isomorphism normalized by their
counits. -/
@[stacks 06Y6, no_expose]
public noncomputable def canonicalDerivedTensorChangeOfRings
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    DerivedTensorChangeOfRings f N :=
  derivedTensorChangeOfRingsOfKFlatResolution f N

/-- The direct tensor-total construction `M ↦ Tot(M ⊗_R N)`, valued in complexes of
`A`-modules, has an exact left derived functor from `D(R)` to `D(A)`. It is computed by the
ordinary tensor-total construction on K-flat complexes and is naturally isomorphic to derived
extension of scalars followed by derived tensoring over `A`. The left-derived-functor universal
properties make all three derived constructions independent of the chosen resolutions.

The isomorphism `directTensorUnderlying` identifies the underlying `R`-complex of the direct
construction with the ordinary tensor-total complex over `R`; `directTensorComparison` is the
canonical natural change-of-rings isomorphism from that direct `A`-valued construction to
extension of scalars followed by tensoring over `A`. -/
public theorem exists_derived_tensor_change_of_rings
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max v uA}
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max v uR}
    let W_R := HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ)
    let W_A := HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} A) (ComplexShape.up ℤ)
    let U_base := extendScalarsLarge f ⋙ DerivedCategory.Q
    let U_tensor := TrightCochain N ⋙ DerivedCategory.Q
    ∃ (directTensor : CochainComplex (ModuleCat.{max v uR uA} R) ℤ ⥤
          CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
      (_directTensorUnderlying :
        directTensor ⋙ restrictScalarsLarge f ≅
          TrightCochain ((restrictScalarsLarge f).obj N))
      (directTensorComparison :
        directTensor ≅ extendScalarsLarge f ⋙ TrightCochain N)
      (F B : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
        DerivedCategory (ModuleCat.{max v uR uA} A))
      (G : DerivedCategory (ModuleCat.{max v uR uA} A) ⥤
        DerivedCategory (ModuleCat.{max v uR uA} A))
      (cF : F.CommShift ℤ),
      letI := cF
      F.IsTriangulated ∧
      ∃ (αF : DerivedCategory.Q ⋙ F ⟶ directTensor ⋙ DerivedCategory.Q)
        (αB : DerivedCategory.Q ⋙ B ⟶ U_base)
        (αG : DerivedCategory.Q ⋙ G ⟶ U_tensor),
        F.IsLeftDerivedFunctor αF W_R ∧
        B.IsLeftDerivedFunctor αB W_R ∧
        G.IsLeftDerivedFunctor αG W_A ∧
        (∀ (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ),
          KFlat.{uR, max v uA} K → IsIso (αF.app K)) ∧
        ∃ (changeOfRings : F ≅ B ⋙ G),
          CategoryTheory.Functor.whiskerLeft DerivedCategory.Q changeOfRings.hom ≫
              (Functor.associator _ _ _).inv ≫
              CategoryTheory.Functor.whiskerRight αB G ≫
              (Functor.associator _ _ _).hom ≫
              CategoryTheory.Functor.whiskerLeft (extendScalarsLarge f) αG ≫
              (Functor.associator _ _ _).inv =
            αF ≫ CategoryTheory.Functor.whiskerRight
              directTensorComparison.hom DerivedCategory.Q := by
  let T := canonicalDerivedTensorChangeOfRings f N
  exact ⟨T.directTensor, T.directTensorUnderlying, T.directTensorComparison,
    T.F, T.B, T.G, T.commShift, T.isTriangulated, T.alphaF, T.alphaB, T.alphaG,
    T.isLeftDerivedF, T.isLeftDerivedB, T.isLeftDerivedG, T.isIso_alphaF,
    T.changeOfRings, T.changeOfRings_coherence⟩
end Consequences

end CochainComplex.DerivedTensor

end
