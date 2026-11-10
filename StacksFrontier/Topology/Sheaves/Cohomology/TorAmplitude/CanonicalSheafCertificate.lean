module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# The canonical certificate of the derived tensor product on a ringed space

`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` reads the Tor-amplitude vocabulary
of Stacks 08CG against a derived tensor product supplied together with the datum that pins it
down: a comparison with termwise underived tensoring exhibiting each `- ⊗^{L} ℱ[0]` as the
*total left derived functor* of `- ⊗ ℱ`. This file constructs that certificate for the genuine
derived tensor product of Stacks 06YU on a ringed space.

The construction is the ringed-space analogue of
`StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`, and it is shorter: the
ringed-site structure of Stacks 06YU already carries a canonical map `toTensor` to the total
tensor complex which is invertible as soon as the *left* factor is K-flat, so no resolution of
the second variable is needed. What remains is to identify `Tot(K ⊗ ℱ[0])` with `K ⊗ ℱ` read
degreewise, and to turn "invertible on K-flat complexes" into the universal property. The latter
is Stacks 06Y6 read at the sheaf level: the K-flat complexes resolve every complex (Stacks 06YS)
and the quasi-isomorphisms of the homotopy category admit a right calculus of fractions, so a
comparison invertible on the resolving class is the counit of the total left derived functor.

## Main definitions

* `HomologicalComplex.map₂SingleRightNatIso`: for a bifunctor `F` and an object `N`, the total
  complex `Tot(F(-, N[0]))` is `F(-, N)` applied degreewise, naturally in the complex.
* `AlgebraicGeometry.RingedSpace.canonicalSheafTensorComparison`: the comparison of
  `- ⊗^{L}_{𝒪_X} ℱ[0]` with termwise tensoring by `ℱ`.
* `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes`:
  **the canonical certificate**, whose underived operation is `- ⊗_{𝒪_X} -` and whose derived
  operation is the derived tensor product of Stacks 06YU, certified by the resolving-complexes
  criterion of this file.

## Main results

* `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolvingComplexes`: a
  comparison on complexes which is invertible on a resolving class of complexes, and whose
  underived functor descends to the homotopy category, is a total left derived functor.
* `AlgebraicGeometry.RingedSpace.isIso_canonicalSheafTensorComparison_app`: the comparison is
  invertible at every K-flat complex. With the previous result this is the `isLeftDerived` field
  of the certificate: `- ⊗^{L} ℱ[0]` is the total left derived functor of `- ⊗ ℱ`.
* `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff`,
  `AlgebraicGeometry.RingedSpace.hasFiniteTorDimension_canonicalCertified_iff` and
  `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertified_iff`: clauses
  (1), (2) and (3) of Stacks 08CG at the canonical certificate are the clauses of
  `Stacks.Cohomology.TorAmplitude`, whose derived tensor product is pinned to the one of
  Stacks 06YU. Each is `Iff.rfl`, and together they are what makes the two registrations of
  the `08CG` tag — on the certificate-parameterized predicates and on the unconditional ones —
  registrations of the same clauses.

## Implementation notes

`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` is the other
certificate in the tree, and it is degenerate: by
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff` its Tor amplitude sees only
the cohomology of the object. A statement universally quantified over certificates is therefore
strictly stronger than Stacks 08CG and, for the properties Stacks 069C and Stacks 0DI0 compare,
false. The certificate below is what lets those statements name the genuine operation instead.

**Why the name carries `OfResolvingComplexes`.**
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring`, in
`StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate`, certifies the same
derived tensor product at the same type and with the same `tensor` and `derivedTensor` fields.
The two differ in the `comparison` datum, which is data and not a proof: there it is
`Stacks.DerivedTensor.RingedSite.sheafTensorComparison`, built from the ringed-site structure's
`toTensor` followed by `CochainComplex.KFlatBifunctor.totalSingleNatIso`, with the universal
property obtained along `CategoryTheory.DerivedCategory.Qh` and carried back to
`CategoryTheory.DerivedCategory.Q`; here it is
`AlgebraicGeometry.RingedSpace.canonicalSheafTensorComparison`, built from
`HomologicalComplex.map₂SingleRightNatIso`, with the universal property obtained from
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolvingComplexes`.
The two comparisons are the same map of the same functors, but `rfl` does not see it: the
inverses of the two natural isomorphisms are extracted through unexposed definitions (`inv`,
`Limits.getColimitCocone`), so the two certificates are not interchangeable definitionally and
must not be merged by renaming one to the other. Tor amplitude and finite Tor dimension read at
either are nevertheless the same propositions, since both predicates mention only
`derivedTensor`; unifying the two constructions is a dedup target.

Three spellings of the category of `𝒪_X`-modules meet here and are definitionally equal:
`StrictlyPerfect.OXMod X`, `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X` and
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`. Statements are written at the first, which is
the one `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` uses; the
`HasDerivedCategory` instance has to be seated by hand at the third, because an instance proved
at one spelling of a non-reducible definition does not fire at another. For the same reason
invertibility of `toTensor` at a K-flat left factor is proved once in the site vocabulary, where
`R` is a variable: at `R := X.sheaf` the structure sheaf enters through `TopCat.Sheaf`, and the
resulting statement is not type-correct at the transparency `rewrite` builds its motive with.

The resolving-class criterion is stated here over an arbitrary abelian category rather than
specialised to sheaves of modules, because the argument uses nothing about the category: it is
the passage from the homotopy category, where the quasi-isomorphisms admit a right calculus of
fractions, back to complexes, where they do not. The `ModuleCat` instance of the same argument
lives in `StacksFrontier.Homology.Tor.DerivedChangeOfRings`; unifying the two is a dedup target.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
  TopologicalSpace
open StrictlyPerfect

/-! ### `Tot(F(-, N[0]))` is `F(-, N)` degreewise, naturally -/

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u'

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u'} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (N : C₂)

/-- The bidegree-`(i, 0)` inclusion into `Tot(F(K, N[0]))` is natural in `K`: a morphism of
complexes acts on that summand by `F(f^i, N)`. -/
theorem singleRightι_mapBifunctorMap {K K' : CochainComplex C₁ ℤ} (f : K ⟶ K') (i : ℤ) :
    singleRightι F K N i ≫
        (mapBifunctorMap f (𝟙 ((CochainComplex.singleFunctor C₂ 0).obj N)) F
          (ComplexShape.up ℤ)).f i =
      (F.map (f.f i)).app (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) ≫
        singleRightι F K' N i := by
  simp [singleRightι]

variable [(F.flip.obj N).Additive]

/-- The identification of `F(-, N)` applied degreewise with `Tot(F(-, N[0]))` is natural in the
complex. -/
theorem singleRightIsoMapBifunctor_naturality {K K' : CochainComplex C₁ ℤ} (f : K ⟶ K') :
    ((F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
        (singleRightIsoMapBifunctor F K' N).hom =
      (singleRightIsoMapBifunctor F K N).hom ≫
        mapBifunctorMap f (𝟙 ((CochainComplex.singleFunctor C₂ 0).obj N)) F
          (ComplexShape.up ℤ) := by
  ext i
  change (F.map (f.f i)).app N ≫ (mapBifunctorSingleRightXIso F K' N i).inv =
    (mapBifunctorSingleRightXIso F K N i).inv ≫
      (mapBifunctorMap f (𝟙 ((CochainComplex.singleFunctor C₂ 0).obj N)) F
        (ComplexShape.up ℤ)).f i
  rw [mapBifunctorSingleRightXIso_inv, mapBifunctorSingleRightXIso_inv, Category.assoc,
    singleRightι_mapBifunctorMap F N f i, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun g => g ≫ singleRightι F K' N i)
    ((F.map (f.f i)).naturality (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).symm

/-- **`Tot(F(-, N[0]))` is `F(-, N)` applied degreewise, naturally in the complex.** The second
variable contributes no differential, and only the bidegree-`(i, 0)` summand survives. -/
def map₂SingleRightNatIso :
    (F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.map₂CochainComplex.flip.obj ((CochainComplex.singleFunctor C₂ 0).obj N) :=
  NatIso.ofComponents (fun K => singleRightIsoMapBifunctor F K N)
    (fun f => singleRightIsoMapBifunctor_naturality F N f)

end HomologicalComplex

/-! ### A comparison invertible on a resolving class of complexes is a left derived functor -/

namespace CategoryTheory.LeftDerivedByResolutions

universe v₁ u₁ d

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- **A comparison on complexes invertible on a resolving class is a total left derived
functor.** Let `P` be a class of complexes resolving every object of the homotopy category, let
the underived functor `U` factor through the homotopy category, and let the comparison `β` be
invertible at every complex in `P`. Then `β` exhibits `G` as the total left derived functor of
`U` at the quasi-isomorphisms of complexes.

The quasi-isomorphisms of complexes admit no calculus of fractions, so the resolving-class
criterion is applied on the homotopy category, where they do, and transported back along the
homotopy quotient, which is fully faithful on functor categories. -/
theorem isLeftDerivedFunctor_of_isIso_on_resolvingComplexes
    (P : CochainComplex A ℤ → Prop)
    (hP : ∀ Y : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (Z : HomotopyCategory A (ComplexShape.up ℤ)) (_ : P Z.as) (s : Z ⟶ Y),
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s)
    {H : Type*} [Category H]
    (U : CochainComplex A ℤ ⥤ H) (Uh : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ Uh ≅ U)
    (G : DerivedCategory A ⥤ H) (β : DerivedCategory.Q ⋙ G ⟶ U)
    (hβ : ∀ K : CochainComplex A ℤ, P K → IsIso (β.app K)) :
    G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  let Qt := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let q := DerivedCategory.quotientCompQhIso A
  let T := (whiskeringLeft _ _ H).obj Qt
  have : T.Full := inferInstanceAs
    (((whiskeringLeft _ _ H).obj
      (CategoryTheory.Quotient.functor (homotopic A (ComplexShape.up ℤ)))).Full)
  let α₀ : Qt ⋙ (DerivedCategory.Qh ⋙ G) ⟶ Qt ⋙ Uh := whiskerRight q.hom G ≫ β ≫ e.inv
  let α : DerivedCategory.Qh ⋙ G ⟶ Uh := T.preimage α₀
  have hα₀ : whiskerLeft Qt α = α₀ := T.map_preimage α₀
  have hα : ∀ Y : HomotopyCategory A (ComplexShape.up ℤ), P Y.as → IsIso (α.app Y) := by
    intro Y hY
    have he : α.app Y = α₀.app Y.as := NatTrans.congr_app hα₀ Y.as
    have hq : IsIso (G.map (q.hom.app Y.as)) := inferInstance
    have hb : IsIso (β.app Y.as) := hβ Y.as hY
    have hev : IsIso (e.inv.app Y.as) := inferInstance
    rw [he]
    dsimp only [α₀, NatTrans.comp_app, Functor.whiskerRight_app]
    exact IsIso.comp_isIso' hq (IsIso.comp_isIso' hb hev)
  have hUh : ∀ {Y Z : HomotopyCategory A (ComplexShape.up ℤ)} (s : Y ⟶ Z),
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s → P Y.as → P Z.as →
        IsIso (Uh.map s) := by
    intro Y Z s hs hY hZ
    have := hα Y hY
    have := hα Z hZ
    have : IsIso (DerivedCategory.Qh.map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
    rw [← isIso_comp_left_iff (α.app Y), ← α.naturality s]
    dsimp only [Functor.comp_map]
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (fun Y => P Y.as) hP Uh hUh
    DerivedCategory.Qh G α hα
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension G α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hke : G.IsRightKanExtension (whiskerRight q.hom G ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator Qt DerivedCategory.Qh G).hom ≫ whiskerLeft Qt α)
      (whiskerRight q.hom G ≫ β) e (Iso.refl G) ?_).mp
      (StacksDraft.Perfect.isRightKanExtension_precomp Qt DerivedCategory.Qh Uh G α)
    rw [hα₀]
    ext Y
    simp [α₀]
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
    ((Qt ⋙ DerivedCategory.Qh).rightUnitor ≪≫ q) β).2
  apply Functor.isRightKanExtension_of_iso G.leftUnitor.symm (whiskerRight q.hom G ≫ β)
  ext Y
  simp only [comp_obj, Iso.symm_hom, Iso.trans_hom, whiskerRight_comp, Category.assoc,
    NatTrans.comp_app, id_obj, whiskerLeft_app, leftUnitor_inv_app, associator_inv_app,
    whiskerRight_app, rightUnitor_hom_app, map_id, Category.id_comp]
  exact Category.id_comp _

end CategoryTheory.LeftDerivedByResolutions

/-! ### The canonical map to the total tensor complex at a K-flat left factor -/

namespace Stacks.DerivedTensor.RingedSite

universe u d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)]

/-- **The canonical map to the total tensor complex is invertible at a K-flat left factor**: it
is then the left K-flat comparison isomorphism of the derived tensor product. -/
theorem DerivedTensorProduct.isIso_toTensor_of_kFlatLeft (T : DerivedTensorProduct.{d, u} R)
    (K L : CochainComplex (Modules R) ℤ) (hK : Stacks.SheafOfModules.KFlat R K) :
    IsIso (T.toTensor K L) := by
  rw [T.toTensor_eq_comparisonLeft K L hK]
  infer_instance

/-- Naturality of the canonical map to the total tensor complex in the left variable alone. -/
theorem DerivedTensorProduct.toTensor_naturality_left (T : DerivedTensorProduct.{d, u} R)
    {K K' : CochainComplex (Modules R) ℤ} (f : K ⟶ K') (L : CochainComplex (Modules R) ℤ) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫ T.toTensor K' L =
      T.toTensor K L ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f (𝟙 L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using T.toTensor_naturality f (𝟙 L)

end Stacks.DerivedTensor.RingedSite

/-! ### The canonical certificate on a ringed space -/

namespace AlgebraicGeometry.RingedSpace

universe u d

variable (X : RingedSpace.{u, u})

/-- Tensoring on the right with a fixed `𝒪_X`-module is additive, because `⊗_{𝒪_X}` is additive
in its first variable. -/
instance sheafTensor_flip_additive (F : OXMod.{u, u} X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F).Additive :=
  haveI := KFlatDerivedPullback.sheafTensor_additive X
  { map_add := fun {_ _ f g} =>
      congrArg (fun α => NatTrans.app α F)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf).map_add (f := f) (g := g)) }

/-- **Stacks 06YS on the homotopy category.** Every object of `K(𝒪_X)` receives a
quasi-isomorphism from a K-flat complex. -/
theorem exists_kFlat_resolution_homotopy
    (Y : HomotopyCategory (OXMod.{u, u} X) (ComplexShape.up ℤ)) :
    ∃ (Z : HomotopyCategory (OXMod.{u, u} X) (ComplexShape.up ℤ))
      (_ : KFlatDerivedPullback.KFlat X Z.as) (s : Z ⟶ Y),
      HomotopyCategory.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ) s := by
  obtain ⟨K, p, hK, -, hp, -⟩ := KFlatDerivedPullback.exists_kFlatResolution X Y.as
  exact ⟨(HomotopyCategory.quotient _ _).obj K, hK, (HomotopyCategory.quotient _ _).map p,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **The canonical map from `- ⊗^{L}_{𝒪_X} ℱ[0]` to the total tensor complex `Tot(- ⊗ ℱ[0])`.**
It is the `toTensor` field of the derived tensor product of Stacks 06YU, read as a natural
transformation of functors on complexes. -/
def derivedToTotalTensor (F : OXMod.{u, u} X) :
    DerivedCategory.Q (C := OXMod.{u, u} X) ⋙
        (Stacks.Cohomology.TorAmplitude.derTensor X).tensor.flip.obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map₂CochainComplex.flip.obj
          ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) ⋙
        DerivedCategory.Q (C := OXMod.{u, u} X) where
  app K := (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor K
    ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F)
  naturality _ _ f :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).toTensor_naturality_left f
      ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F)

/-- **`Tot(- ⊗_{𝒪_X} ℱ[0])` is `- ⊗_{𝒪_X} ℱ` read degreewise**, after the localization: the
second factor contributes no differential, so only one summand of the total complex survives. -/
def totalTensorSingleIso (F : OXMod.{u, u} X) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map₂CochainComplex.flip.obj
          ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) ⋙
        DerivedCategory.Q (C := OXMod.{u, u} X) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := OXMod.{u, u} X) :=
  Functor.isoWhiskerRight (HomologicalComplex.map₂SingleRightNatIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) F).symm
    (DerivedCategory.Q (C := OXMod.{u, u} X))

/-- **Comparison of `- ⊗^{L}_{𝒪_X} ℱ[0]` with termwise tensoring by `ℱ`.** On a complex `K` it
is the canonical map of Stacks 06YU to the total tensor complex `Tot(K ⊗_{𝒪_X} ℱ[0])`, followed
by the identification of that complex with `K ⊗_{𝒪_X} ℱ` read degreewise. -/
def canonicalSheafTensorComparison (F : OXMod.{u, u} X) :
    DerivedCategory.Q (C := OXMod.{u, u} X) ⋙
        (Stacks.Cohomology.TorAmplitude.derTensor X).tensor.flip.obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := OXMod.{u, u} X) :=
  derivedToTotalTensor X F ≫ (totalTensorSingleIso X F).hom

/-- **At a K-flat complex the comparison is invertible.** The canonical map of Stacks 06YU to
the total tensor complex is an isomorphism as soon as the left factor is K-flat, and the
degreewise identification is an isomorphism always. -/
theorem isIso_canonicalSheafTensorComparison_app (F : OXMod.{u, u} X)
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (hK : KFlatDerivedPullback.KFlat X K) :
    IsIso ((canonicalSheafTensorComparison X F).app K) := by
  have h₁ : IsIso ((derivedToTotalTensor X F).app K) :=
    (Stacks.Cohomology.TorAmplitude.derTensor X).isIso_toTensor_of_kFlatLeft K
      ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) hK
  exact IsIso.comp_isIso' h₁ ((totalTensorSingleIso X F).app K).isIso_hom

/-- Termwise tensoring by `ℱ` read on the homotopy category, precomposed with the homotopy
quotient, is termwise tensoring on complexes followed by the localization. -/
def quotientCompTermwiseSheafTensorIso (F : OXMod.{u, u} X) :
    HomotopyCategory.quotient (OXMod.{u, u} X) (ComplexShape.up ℤ) ⋙
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf).flip.obj F).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := OXMod.{u, u} X)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := OXMod.{u, u} X) :=
  Functor.isoWhiskerRight
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)) (DerivedCategory.Qh (C := OXMod.{u, u} X)) ≪≫
    Functor.isoWhiskerLeft
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (OXMod.{u, u} X))

/-- **The canonical certified derived tensoring on a ringed space.** Its underived operation is
the tensor product `- ⊗_{𝒪_X} -` of sheaves of modules, the sheafification of
`U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`, and its derived operation is the derived tensor product of
Stacks 06YU; its `isLeftDerived` field says that `- ⊗^{L} ℱ[0]` is the total left derived
functor of `- ⊗ ℱ`, which holds because the comparison above is invertible at every K-flat
complex and the K-flat complexes resolve every complex (Stacks 06YS).

This is the certificate at which Stacks 08CG, and everything parameterised by a certificate,
says what its source says. -/
def canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes :
    CertifiedDerivedSheafTensoring.{d, u} X where
  tensor := Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩
  additive F := sheafTensor_flip_additive X F
  derivedTensor := (Stacks.Cohomology.TorAmplitude.derTensor X).tensor
  comparison := canonicalSheafTensorComparison X
  isLeftDerived := fun F =>
    CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolvingComplexes
      (fun K => KFlatDerivedPullback.KFlat X K) (exists_kFlat_resolution_homotopy X) _
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf).flip.obj F).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := OXMod.{u, u} X))
      (quotientCompTermwiseSheafTensorIso X F) _ (canonicalSheafTensorComparison X F)
      (fun K hK => isIso_canonicalSheafTensorComparison_app X F K hK)

/-- **Stacks 08CG (1) at the canonical certificate is Stacks 08CG (1) at the pinned derived
tensor product.** The two are the same proposition, since the certificate's derived operation is
the derived tensor product of Stacks 06YU. -/
theorem hasTorAmplitudeIn_canonicalCertified_iff
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    (canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes X).HasTorAmplitudeIn E a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b :=
  Iff.rfl

/-- **Stacks 08CG (2) at the canonical certificate is Stacks 08CG (2) at the pinned derived
tensor product.** -/
theorem hasFiniteTorDimension_canonicalCertified_iff
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes X).HasFiniteTorDimension E ↔
      Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X E :=
  Iff.rfl

universe d'

/-- **Stacks 08CG (3) at the canonical certificate on each open is Stacks 08CG (3) at the pinned
derived tensor product.** The certificate-family form quantifies over a derived tensor product on
every open subspace; taking each to be the canonical one of Stacks 06YU there makes it the same
proposition as the form with nothing assumed, since both predicates mention only
`derivedTensor`. -/
theorem locallyHasFiniteTorDimension_canonicalCertified_iff
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X
        (fun U =>
          canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes
            (X.restrict U.isOpenEmbedding)) E ↔
      Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension X E :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace

end
