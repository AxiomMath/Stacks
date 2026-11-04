module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackChangeOfBaseDerived
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceOfFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackLargeHoms

/-!
# The change of base scheme for `Complexes`

Let `g : T ⟶ S` be a morphism of the big fppf site, `D` a situation of Stacks 0DLE over `T` whose
base is final, and `D₁` a situation over `S` whose base is the representable presheaf of `g` and
whose source is the image of the source of `D` under the forward functor of Stacks 04SG. Then
`Complexes_{X/T}` is an algebraic stack over `T` exactly when `Complexes_{X₁/T}` is one over `S`:
the proposition `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`.

By Stacks 04X5 (`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase` and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_changeBase`), `Complexes_{X/T}` is algebraic over `T`
exactly when its image under Construction A is algebraic over `S`. That image is equivalent over
`(Sch/S)_fppf` to `Complexes_{X₁/T}`
(`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.equivalence`), and Stacks 03YQ
(`AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence`) transfers algebraicity along it.
The equivalence sends a test scheme `U ⟶ T` to `U ⟶ T ⟶ S` and a complex on `X_U` to the
corresponding complex on `X₁_U = Λ_g X_U` (Stacks 04SG); it is fully faithful by the comparison of
derived pullbacks of `AlgebraicGeometry.Space.smallerBaseDerivedPullbackIso`, and every object of
`Complexes_{X₁/T}` is isomorphic over an identity to one in its image.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.comparison`: the functor over
  `(Sch/S)_fppf` from Construction A of `Complexes_{X/T}` to `Complexes_{X₁/T}`.
* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum.equivalence`: it is an
  equivalence over `(Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.changeOfBaseComparison_proved`: the proposition
  `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison` holds.

## References

* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u z

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory

/-- Pasting a commutative square onto a factorization: from `l ≫ c = c' ≫ l'` and
`p ≫ c' = f₁ ≫ f₂ ≫ f₃`, `p ≫ l ≫ c ≫ r = f₁ ≫ f₂ ≫ f₃ ≫ l' ≫ r`. -/
theorem _root_.CategoryTheory.Category.square_paste_of_eq {𝒞 : Type*} [Category* 𝒞]
    {P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Z : 𝒞} (p : P₁ ⟶ P₂) (l : P₂ ⟶ P₃) (c : P₃ ⟶ P₄) (c' : P₂ ⟶ P₅)
    (l' : P₅ ⟶ P₄) (r : P₄ ⟶ Z) (f₁ : P₁ ⟶ Q₁) (f₂ : Q₁ ⟶ Q₂) (f₃ : Q₂ ⟶ P₅)
    (hsq : l ≫ c = c' ≫ l') (hf : p ≫ c' = f₁ ≫ f₂ ≫ f₃) :
    p ≫ l ≫ c ≫ r = f₁ ≫ f₂ ≫ f₃ ≫ l' ≫ r := by
  rw [reassoc_of% hsq, reassoc_of% hf]

/-- A morphism of objects over `Z` between two equal objects, whose underlying morphism is the
identification of the underlying objects, is the identification. -/
theorem _root_.CategoryTheory.Over.id_eq_eqToHom_comp_of_left_eq {𝒞 : Type*} [Category* 𝒞]
    {Z : 𝒞} {X Y : Over Z} (h : X = Y) (β : X ⟶ Y)
    (hβ : β.left = eqToHom (congrArg (fun W : Over Z => W.left) h)) :
    𝟙 Y = eqToHom h.symm ≫ β ≫ 𝟙 Y := by
  subst h
  ext
  simp [hβ]

namespace AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum

variable {B : BigFppfSite.{u}} {T S : Scheme.{u}} {hT : B.Contains T} {hS : B.Contains S}
  {g : B.obj hT ⟶ B.obj hS} (C : ChangeOfBaseDatum B hT hS g)

attribute [local instance] complexesCategory

/-! ### The functor on objects and morphisms -/

/-- **The comparison on objects**: a test scheme `U ⟶ T` with a complex on `X_U` goes to
`U ⟶ T ⟶ S` with the corresponding complex on `X₁_U`. -/
abbrev comparisonObj (X : ComplexesObject C.D) : ComplexesObject C.D₁ where
  T := C.testScheme X.T
  E := (smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso).inverse.obj X.E
  relativelyPerfect := ((Match.refl C X.T).isRelativelyPerfect_iff _).2
    (isRelativelyPerfect_of_iso
      ((smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso).counitIso.app X.E)
      X.relativelyPerfect)
  noNegativeFibreExt := ((Match.refl C X.T).hasNoNegativeFibreExt_iff _).2
    (hasNoNegativeFibreExt_of_iso
      ((smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso).counitIso.app X.E)
      X.noNegativeFibreExt)

variable {C}

/-- The fibre isomorphism `L(X_k)^* E' ≅ E` of a morphism of `Complexes_{X/T}`, read over `S`. -/
def comparisonFibreIso {X X' : ComplexesObject C.D} (k : X.T ⟶ X'.T)
    (φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj X'.E ≅ X.E) :
    ((smallEtaleDerivedPullbackData B S hS).pull (C.D₁.relativeMap (C.testSchemeMap k))).obj
        (C.comparisonObj X').E ≅ (C.comparisonObj X).E :=
  Match.transposeIso (Match.compatible_refl C k) _ X.E
    (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).mapIso
      ((smallerBaseDerivedEquivalence B g (Match.refl C X'.T).spaceIso).counitIso.app X'.E) ≪≫ φ)

/-- Under the functor of the derived equivalence followed by its counit, the fibre isomorphism
`comparisonFibreIso k φ` becomes the pullback comparison, followed by the pullback of the counit
and by `φ`. -/
theorem comparisonFibreIso_spec {X X' : ComplexesObject C.D} (k : X.T ⟶ X'.T)
    (φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj X'.E ≅ X.E) :
    (smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso).functor.map
        (comparisonFibreIso k φ).hom ≫
      (smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso).counit.app X.E =
    (Match.pullbackIso (Match.compatible_refl C k)).hom.app (C.comparisonObj X').E ≫
      ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).map
        ((smallerBaseDerivedEquivalence B g (Match.refl C X'.T).spaceIso).counit.app X'.E) ≫
        φ.hom := by
  rw [comparisonFibreIso, Match.transposeIso_hom]
  exact Match.transpose_spec _ _ _ _

variable (C)

/-- **The comparison on morphisms.** -/
def comparisonMap {X X' : ComplexesObject C.D} (m : ComplexesHom X X') :
    ComplexesHom (C.comparisonObj X) (C.comparisonObj X') where
  base := C.testSchemeMap m.base
  fibre := (comparisonFibreIso m.base (asIso m.fibre)).hom
  isIso_fibre := Iso.isIso_hom _

/-- `testSchemeMap` sends a composite to the composite of the images. -/
theorem testSchemeMap_comp {A A' A'' : SchemesOver C.D.Y} (k : A ⟶ A') (k' : A' ⟶ A'') :
    C.testSchemeMap (k ≫ k') = C.testSchemeMap k ≫ C.testSchemeMap k' :=
  rfl

/-- Two morphisms into the inverse image of an object under an equivalence agree when they agree
after the functor and the counit. -/
theorem _root_.CategoryTheory.Equivalence.eq_of_functor_map_comp_counit {𝒜 ℬ : Type*}
    [Category* 𝒜] [Category* ℬ] (F : 𝒜 ≌ ℬ) {Y : 𝒜} {E : ℬ} {f f' : Y ⟶ F.inverse.obj E}
    (h : F.functor.map f ≫ F.counit.app E = F.functor.map f' ≫ F.counit.app E) : f = f' := by
  have : IsIso (F.counit.app E) := inferInstanceAs (IsIso (F.counitIso.hom.app E))
  exact F.functor.map_injective ((cancel_mono (F.counit.app E)).1 h)

variable {C} in
/-- The fibre of the image of a composite, read along the composite of the images of the base
maps. -/
def comparisonFibreIsoComp {X X' X'' : ComplexesObject C.D} (m : ComplexesHom X X')
    (n : ComplexesHom X' X'') :
    ((smallEtaleDerivedPullbackData B S hS).pull
        (C.D₁.relativeMap (C.testSchemeMap m.base ≫ C.testSchemeMap n.base))).obj
        (C.comparisonObj X'').E ≅ (C.comparisonObj X).E :=
  Match.transposeIso ((Match.compatible_refl C m.base).comp (Match.compatible_refl C n.base))
    _ X.E
    (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap (m.base ≫ n.base))).mapIso
      ((smallerBaseDerivedEquivalence B g (Match.refl C X''.T).spaceIso).counitIso.app X''.E) ≪≫
      asIso (Functor.fibreComp (C.D.compComparison m.base n.base) m.fibre n.fibre))

variable {C} in
/-- The fibre isomorphism of the image of `m.comp n`, read along the composite of the images of the
base maps, is the composite of the fibres of the images of `m` and `n`. -/
theorem comparisonFibreIsoComp_eq {X X' X'' : ComplexesObject C.D} (m : ComplexesHom X X')
    (n : ComplexesHom X' X'') :
    (comparisonFibreIsoComp m n).hom =
      Functor.fibreComp (C.D₁.compComparison (C.testSchemeMap m.base) (C.testSchemeMap n.base))
        (comparisonFibreIso m.base (asIso m.fibre)).hom
        (comparisonFibreIso n.base (asIso n.fibre)).hom := by
  refine Equivalence.eq_of_functor_map_comp_counit
    (smallerBaseDerivedEquivalence B g (Match.refl C X.T).spaceIso) (E := X.E) ?_
  have hmn := Match.transpose_spec
    ((Match.compatible_refl C m.base).comp (Match.compatible_refl C n.base))
    (C.comparisonObj X'').E X.E
    (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap (m.base ≫ n.base))).map
      ((smallerBaseDerivedEquivalence B g (Match.refl C X''.T).spaceIso).counit.app X''.E) ≫
      Functor.fibreComp (C.D.compComparison m.base n.base) m.fibre n.fibre)
  have hm := comparisonFibreIso_spec m.base (asIso m.fibre)
  have hn := comparisonFibreIso_spec n.base (asIso n.fibre)
  have htri := Match.pullbackIso_triangle (Match.compatible_refl C m.base)
    (Match.compatible_refl C n.base)
    ((Match.compatible_refl C m.base).comp (Match.compatible_refl C n.base))
    (C.comparisonObj X'').E
  have hnat := (Match.pullbackIso (Match.compatible_refl C m.base)).hom.naturality
    (comparisonFibreIso n.base (asIso n.fibre)).hom
  have hcc := (C.D.compComparison m.base n.base).hom.naturality
    (X := (smallerBaseDerivedEquivalence B g (Match.refl C X''.T).spaceIso).functor.obj
        (C.comparisonObj X'').E)
    ((smallerBaseDerivedEquivalence B g (Match.refl C X''.T).spaceIso).counit.app X''.E)
  rw [Functor.comp_map, Functor.comp_map] at hnat
  rw [Functor.comp_map] at hcc
  rw [asIso_hom] at hm hn
  rw [comparisonFibreIsoComp, Match.transposeIso_hom, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom, hmn, Functor.fibreComp, Functor.fibreComp, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, hm, reassoc_of% hnat]
  have hn' : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap m.base)).map
        ((smallerBaseDerivedEquivalence B g (Match.refl C X'.T).spaceIso).functor.map
          (comparisonFibreIso n.base (asIso n.fibre)).hom) ≫
      ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap m.base)).map
        ((smallerBaseDerivedEquivalence B g (Match.refl C X'.T).spaceIso).counit.app X'.E) ≫
        m.fibre =
      ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap m.base)).map
          ((Match.pullbackIso (Match.compatible_refl C n.base)).hom.app (C.comparisonObj X'').E) ≫
        ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap m.base)).map
          (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap n.base)).map
            ((smallerBaseDerivedEquivalence B g (Match.refl C X''.T).spaceIso).counit.app X''.E)) ≫
        ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap m.base)).map n.fibre ≫
          m.fibre := by
    rw [← Functor.map_comp_assoc, hn, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc]
  rw [hn']
  exact Category.square_paste_of_eq _ _ _ _ _ _ _ _ _ hcc htri

variable {C} in
/-- **The comparison respects composition.** -/
theorem comparisonMap_comp {X X' X'' : ComplexesObject C.D} (m : ComplexesHom X X')
    (n : ComplexesHom X' X'') :
    C.comparisonMap (m.comp n) = (C.comparisonMap m).comp (C.comparisonMap n) :=
  complexesHom_eq_of_heq (C.testSchemeMap_comp m.base n.base)
    ((Match.transposeIso_hom_heq (C.testSchemeMap_comp m.base n.base) _ _ _ _ _).trans
      (heq_of_eq (comparisonFibreIsoComp_eq m n)))

/-- `testSchemeMap` sends an identity to an identity. -/
theorem testSchemeMap_id (A : SchemesOver C.D.Y) : C.testSchemeMap (𝟙 A) = 𝟙 (C.testScheme A) :=
  CostructuredArrow.hom_ext _ _ (by
    show (Over.map g).map (𝟙 A.left) = 𝟙 _
    rw [CategoryTheory.Functor.map_id])

variable {C} in
/-- **The comparison respects identities.** -/
theorem comparisonMap_id (X : ComplexesObject C.D) :
    C.comparisonMap (ComplexesHom.id X) = ComplexesHom.id (C.comparisonObj X) := by
  let e : C.comparisonObj X ⟶ C.comparisonObj X := C.comparisonMap (ComplexesHom.id X)
  have he : e ≫ e = e := by
    show (C.comparisonMap (ComplexesHom.id X)).comp (C.comparisonMap (ComplexesHom.id X)) = _
    rw [← comparisonMap_comp, ComplexesHom.id_comp]
  have : IsIso (C.comparisonMap (ComplexesHom.id X)).base := by
    show IsIso (C.testSchemeMap (𝟙 X.T))
    rw [testSchemeMap_id]
    infer_instance
  have : IsIso e := isIso_of_isIso_base e
  exact (cancel_epi e).1 (he.trans (Category.comp_id e).symm)

/-! ### The functor over `(Sch/S)_fppf` -/

/-- **The comparison functor** from Construction A of `Complexes_{X/T}` to `Complexes_{X₁/T}`,
over `(Sch/S)_fppf`. -/
def comparison :
    Stack.changeBase B T S hT hS g (complexesBasedCategory C.D) ⥤ᵇ
      complexesBasedCategory C.D₁ where
  obj := C.comparisonObj
  map m := C.comparisonMap m
  map_id X := comparisonMap_id X
  map_comp m n := comparisonMap_comp m n
  w := rfl

/-- The comparison functor is faithful. -/
instance comparison_faithful : (C.comparison).toFunctor.Faithful where
  map_injective {X X'} m m' h := by
    change C.comparisonMap m = C.comparisonMap m' at h
    have hb : m.base = m'.base :=
      CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (congrArg (fun t => t.base.left.left) h))
    obtain ⟨mb, mf, mi⟩ := m
    obtain ⟨mb', mf', mi'⟩ := m'
    change mb = mb' at hb
    subst hb
    change (⟨C.testSchemeMap mb, (comparisonFibreIso mb (asIso mf)).hom, Iso.isIso_hom _⟩ :
      ComplexesHom (C.comparisonObj X) (C.comparisonObj X')) =
        ⟨C.testSchemeMap mb, (comparisonFibreIso mb (asIso mf')).hom, Iso.isIso_hom _⟩ at h
    obtain ⟨-, hf⟩ := ComplexesHom.mk.inj h
    have hf := eq_of_heq hf
    dsimp only [comparisonFibreIso] at hf
    rw [Match.transposeIso_hom, Match.transposeIso_hom] at hf
    have hf' := (Match.transpose _ _ _).injective hf
    rw [Iso.trans_hom, Iso.trans_hom, asIso_hom, asIso_hom] at hf'
    have hmf : mf = mf' := (Iso.cancel_iso_hom_left _ _ _).1 hf'
    subst hmf
    rfl

/-- The comparison functor is full. -/
instance comparison_full : (C.comparison).toFunctor.Full where
  map_surjective {X X'} n := by
    obtain ⟨nb, nf, ni⟩ := n
    obtain ⟨k, hk⟩ : ∃ k : X.T ⟶ X'.T, C.testSchemeMap k = nb := by
      refine ⟨(Match.refl C X.T).homOfTarget (Match.refl C X'.T) nb, ?_⟩
      have h := (Match.refl C X.T).compatible_homOfTarget (Match.refl C X'.T) nb
      refine CostructuredArrow.hom_ext _ _ ?_
      have h' : 𝟙 _ ≫ nb.left = (Over.map g).map
          ((Match.refl C X.T).homOfTarget (Match.refl C X'.T) nb).left ≫ 𝟙 _ := h
      rw [Category.id_comp, Category.comp_id] at h'
      exact h'.symm
    subst hk
    let φ : ((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).obj X'.E ≅ X.E :=
      (((smallEtaleDerivedPullbackData B T hT).pull (C.D.relativeMap k)).mapIso
        ((smallerBaseDerivedEquivalence B g (Match.refl C X'.T).spaceIso).counitIso.app
          X'.E)).symm ≪≫
      Match.transposeSymmIso (Match.compatible_refl C k) _ X.E (@asIso _ _ _ _ nf ni)
    refine ⟨⟨k, φ.hom, inferInstance⟩, ?_⟩
    have hφ : (comparisonFibreIso k (asIso φ.hom)).hom = nf := by
      have e₁ : asIso φ.hom = φ := Iso.ext rfl
      rw [e₁]
      dsimp only [comparisonFibreIso]
      rw [Iso.self_symm_id_assoc, Match.transposeIso_transposeSymmIso_hom]
      rfl
    change (⟨C.testSchemeMap k, (comparisonFibreIso k (asIso φ.hom)).hom, _⟩ :
      ComplexesHom (C.comparisonObj X) (C.comparisonObj X')) = ⟨C.testSchemeMap k, nf, ni⟩
    congr 1

/-! ### Every object is in the essential image, over an identity -/

/-- **An object of `Complexes_{X₁/T}`, read over `T`.** -/
def preimageObj (y : ComplexesObject C.D₁) : ComplexesObject C.D where
  T := C.ofTarget y.T
  E := (smallerBaseDerivedEquivalence B g (Match.ofTarget C y.T).spaceIso).functor.obj y.E
  relativelyPerfect := ((Match.ofTarget C y.T).isRelativelyPerfect_iff y.E).1 y.relativelyPerfect
  noNegativeFibreExt :=
    ((Match.ofTarget C y.T).hasNoNegativeFibreExt_iff y.E).1 y.noNegativeFibreExt

/-- The identification of a test scheme over `D₁.Y`, read over `D.Y` and back, with itself. -/
def preimageBaseIso (y : ComplexesObject C.D₁) : C.testScheme (C.ofTarget y.T) ≅ y.T :=
  CostructuredArrow.isoMk (C.ofTargetIso y.T)
    (C.w_of_targetPoint _ ((Match.ofTarget C y.T).w.trans
      (C.targetPoint_testScheme (C.ofTarget y.T)).symm))

/-- The identity of `C.ofTarget y.T` and `(C.preimageBaseIso y).hom` are compatible for the
matches `Match.refl C (C.ofTarget y.T)` and `Match.ofTarget C y.T`. -/
theorem compatible_preimageBaseIso (y : ComplexesObject C.D₁) :
    (Match.refl C (C.ofTarget y.T)).Compatible (Match.ofTarget C y.T) (𝟙 _)
      (C.preimageBaseIso y).hom := by
  show 𝟙 _ ≫ (C.ofTargetIso y.T).hom = (Over.map g).map (𝟙 _) ≫ (C.ofTargetIso y.T).hom
  rw [CategoryTheory.Functor.map_id]

/-- The morphism from the image of the preimage of an object of `Complexes_{X₁/T}` to it. -/
def preimageHom (y : ComplexesObject C.D₁) :
    ComplexesHom (C.comparisonObj (C.preimageObj y)) y where
  base := (C.preimageBaseIso y).hom
  fibre := (Match.transposeIso (C.compatible_preimageBaseIso y) y.E (C.preimageObj y).E
    ((C.D.idComparison (C.ofTarget y.T)).app _)).hom
  isIso_fibre := Iso.isIso_hom _

/-- **Every object of `Complexes_{X₁/T}` is isomorphic to one in the image of the
comparison.** -/
def preimageIso (y : ComplexesObject C.D₁) : C.comparison.obj (C.preimageObj y) ≅ y :=
  haveI : IsIso (C.preimageHom y).base := inferInstanceAs (IsIso (C.preimageBaseIso y).hom)
  @asIso _ _ _ _ (C.preimageHom y : C.comparisonObj (C.preimageObj y) ⟶ y)
    (isIso_of_isIso_base (D := C.D₁) (C.preimageHom y))

/-- The isomorphism `C.preimageIso y` lies over the identity of the image of `y` in
`(Sch/S)_fppf`. -/
theorem isHomLift_preimageIso (y : ComplexesObject C.D₁) :
    (complexesFunctor C.D₁).IsHomLift (𝟙 ((complexesFunctor C.D₁).obj y))
      (C.preimageIso y).hom := by
  have ha : (complexesFunctor C.D₁).obj (C.comparisonObj (C.preimageObj y)) =
      (complexesFunctor C.D₁).obj y :=
    congrArg (fun f => Over.mk f) (Over.w (C.targetPoint y.T))
  refine IsHomLift.of_fac (p := complexesFunctor C.D₁) _ _ ha rfl ?_
  rw [eqToHom_refl]
  exact Over.id_eq_eqToHom_comp_of_left_eq ha _ (eqToHom_refl _ _).symm

/-- **Construction A of `Complexes_{X/T}` is equivalent over `(Sch/S)_fppf` to
`Complexes_{X₁/T}`.** -/
def equivalence :
    BasedCategory.Equivalence (Stack.changeBase B T S hT hS g (complexesBasedCategory C.D))
      (complexesBasedCategory C.D₁) :=
  BasedCategory.Equivalence.ofFullyFaithfulLift C.comparison
    (Functor.FullyFaithful.ofFullyFaithful _) C.preimageObj C.preimageIso
    C.isHomLift_preimageIso

end AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseDatum

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] complexesCategory

/-- **Stacks 04X5 for `Complexes`.** For `g : T ⟶ S` and a situation `D` over `T`,
`Complexes_{X/T}` is an algebraic stack over `T` exactly when its image under Construction A is
one over `S`. -/
theorem isAlgebraicStack_changeBase_complexes_iff {T S : Scheme.{u}} {hT : B.Contains T}
    {hS : B.Contains S} (g : B.obj hT ⟶ B.obj hS) (D : ComplexesSituation B T hT) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT (complexesBasedCategory D) ↔
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS
        (Stack.changeBase B T S hT hS g (complexesBasedCategory D)) := by
  let 𝒳 := complexesBasedCategory D
  have hfib : 𝒳.p.IsFiberedInGroupoids := complexesFunctor_isFiberedInGroupoids D
  have key : LocallySmall.{u} 𝒳.obj → (Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT 𝒳 ↔
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (Stack.changeBase B T S hT hS g 𝒳)) := by
    intro _
    let e := BasedCategory.shrinkHomsEquivalenceOver 𝒳
    let 𝒳s : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B T hT) :=
      CatFiberedInGroupoids.mk 𝒳.shrinkHoms
        (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e.symm hfib)
    constructor
    · intro h
      have hs : Stack.IsAlgebraicStack.{u, z} B T hT 𝒳s.val :=
        Stack.isAlgebraicStack_of_equivalenceOver B T hT e h
      exact Stack.isAlgebraicStack_of_equivalenceOver B S hS
        (𝒳 := Stack.changeBase B T S hT hS g 𝒳s.val) (e.symm.compRight (Over.map g))
        (Stack.isAlgebraicStack_changeBase.{u, z, z} B T S hT hS g 𝒳s hs)
    · intro h
      have hcs : Stack.IsAlgebraicStack.{u, z} B S hS (Stack.changeBase B T S hT hS g 𝒳s.val) :=
        Stack.isAlgebraicStack_of_equivalenceOver B S hS
          (𝒳 := Stack.changeBase B T S hT hS g 𝒳) (e.compRight (Over.map g)) h
      exact Stack.isAlgebraicStack_of_equivalenceOver B T hT e.symm
        (Stack.isAlgebraicStack_of_changeBase.{u, z, z} B T S hT hS g 𝒳s hcs)
  exact ⟨fun h => (key (Stack.locallySmall_of_isAlgebraicStack B T hT h)).1 h,
    fun h => (key (Stack.locallySmall_of_isAlgebraicStack B S hS h)).2 h⟩

/-- **The change-of-base comparison for `Complexes` holds.** For `g : T ⟶ S`, a situation `D`
over `T` with final base and a situation `D₁` over `S` whose base is the representable presheaf of
`g` and whose source is the image of the source of `D` under Stacks 04SG, `Complexes_{X/T}` is
algebraic over `T` exactly when `Complexes_{X₁/T}` is algebraic over `S`. -/
theorem changeOfBaseComparison_proved : ChangeOfBaseComparison.{u, z} B := by
  intro T S hT hS g D hD D₁ eY ⟨eX⟩
  let C : ChangeOfBaseDatum B hT hS g := ⟨D, hD.some, D₁, eY, eX⟩
  exact (isAlgebraicStack_changeBase_complexes_iff g D).trans
    (Stack.isAlgebraicStack_iff_of_equivalence B S hS C.equivalence)

end AlgebraicGeometry.Space.ComplexesSituation

end
