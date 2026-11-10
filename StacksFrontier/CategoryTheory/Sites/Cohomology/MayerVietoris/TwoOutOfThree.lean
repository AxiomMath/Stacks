module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# Two out of three for the comparison map of a square

For a commutative square in a ringed site, the canonical comparison from derived sections over
its final vertex to the mapping cocone of the signed restriction map is an isomorphism on the
third vertex of a distinguished triangle whenever it is an isomorphism on the other two
([Stacks, Tag 0EWP]).

## Main results

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.isCSquareIso_obj₃_of_distTriang` gives the third
  vertex from the first two.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.isCSquareIso_obj₁_of_distTriang` gives the first
  vertex from the last two.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.isCSquareIso_obj₂_of_distTriang` gives the second
  vertex from the other two.

## Implementation notes

The source calls the canonical chain-level maps quasi-isomorphisms. This is expressed by
`Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.IsCSquareIso`
on derived objects, which by
`Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.isCSquareIso_iff_quasiIso`
is equivalent to that condition on any K-injective representative.

The proof replaces the given distinguished triangle by a degreewise split short exact sequence
of K-injective complexes representing it: the mapping cone of a map of K-injective resolutions
is K-injective, and `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`
presents it degreewise split. Degreewise sections and the mapping cocone both carry such a
sequence to a short exact sequence of complexes of abelian groups — the mapping cocone because
it is degreewise a biproduct of three such — and the canonical map is a morphism between the
two resulting distinguished triangles of the derived category, so the two-out-of-three property
for isomorphisms in a triangulated category applies.

## References

* [Stacks Project, Tag 0EWP](https://stacks.math.columbia.edu/tag/0EWP)
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v w r

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes

attribute [local instance] HasDerivedCategory.standard sheafSections_obj_additive

section Engine

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}} (sq : Square C)

open Stacks.MayerVietoris.CanonicalMapOfComplexes

/-- The map of homotopy cofibres induced by a morphism of arrows is additive in that
morphism. -/
private theorem homotopyCofiber_mapArrowHom_add
    {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
    {F G F' G' : HomologicalComplex V c} (φ : F ⟶ G)
    [HomologicalComplex.HasHomotopyCofiber φ] [DecidableRel c.Rel]
    (φ' : F' ⟶ G') [HomologicalComplex.HasHomotopyCofiber φ']
    (H : ∀ j, ∃ i, c.Rel i j) (α β : Arrow.mk φ ⟶ Arrow.mk φ') :
    HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H (α + β) =
      HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H α +
        HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H β := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · apply HomologicalComplex.homotopyCofiber.ext_from_X φ (c.next i) i hi
    all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom, Homotopy.ofEq, Homotopy.trans,
      Homotopy.compLeft]
  · apply HomologicalComplex.homotopyCofiber.ext_from_X' φ i hi
    simp [HomologicalComplex.homotopyCofiber.mapArrowHom]

/-- The mapping cocone of the signed restriction map is an additive functor of the complex. -/
private theorem coconeComplexFunctor_additive :
    (coconeComplexFunctor.{u, v} (R := R) sq).Additive := by
  constructor
  intro I I' f g
  change (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ (secondMapArrowMap sq (f + g))) = _
  rw [show secondMapArrowMap sq (f + g) =
      secondMapArrowMap sq f + secondMapArrowMap sq g by
    apply Arrow.hom_ext
    · simp only [secondMapArrowMap, Arrow.homMk'_left, Arrow.Hom.add_left]
      apply biprod.hom_ext <;> simp
    · simp only [secondMapArrowMap, Arrow.homMk'_right, Arrow.Hom.add_right]
      exact Functor.map_add _]
  rw [homotopyCofiber_mapArrowHom_add]
  ext n x
  rfl

attribute [local instance] coconeComplexFunctor_additive

/-- The degreewise comparison of the map of homotopy cofibres with the biproduct
decomposition of the cofibre. -/
private theorem mapArrowHom_XIsoBiprod
    {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : Arrow.mk f ⟶ Arrow.mk g) (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    (HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, by simp [ComplexShape.up_Rel]⟩) a).f p ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod g p q hpq).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f p q hpq).hom ≫
        biprod.map (a.left.f q) (a.right.f p) := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X f q p hpq
  · dsimp only [HomologicalComplex.homotopyCofiber.mapArrowHom]
    rw [← Category.assoc, HomologicalComplex.homotopyCofiber.inlX_desc_f f _ _ q p hpq]
    simp [Homotopy.ofEq, Homotopy.trans, Homotopy.compLeft,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom g _ q p hpq,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
  · simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom,
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]

/-- The mapping cocone is degreewise the biproduct of the sections over the two middle corners
and the shifted sections over the first corner. -/
private noncomputable def coconeXIso (I : CochainComplex (SheafOfModules.{v} R) ℤ) (n : ℤ) :
    ((coconeComplexFunctor sq).obj I).X n ≅
      (((sectionsComplex R sq.X₃).obj I ⊞ (sectionsComplex R sq.X₂).obj I).X n ⊞
        ((sectionsComplex R sq.X₁).obj I).X (n - 1)) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (secondMap sq I) (n - 1) n (by simp)

/-- The degreewise biproduct decomposition of the mapping cocone is natural in the complex. -/
private theorem coconeXIso_naturality
    {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') (n : ℤ) :
    ((coconeComplexFunctor sq).map f).f n ≫ (coconeXIso sq I' n).hom =
      (coconeXIso sq I n).hom ≫ biprod.map
        ((biprod.map ((sectionsComplex R sq.X₃).map f)
          ((sectionsComplex R sq.X₂).map f)).f n)
        (((sectionsComplex R sq.X₁).map f).f (n - 1)) :=
  mapArrowHom_XIsoBiprod _ _ (secondMapArrowMap sq f) (n - 1) n (by simp)

end Engine

section Biprod

variable {V : Type*} [Category V] [Preadditive V]

/-- The biproduct of two short complexes. -/
private noncomputable def biprodShortComplex (S T : ShortComplex V)
    [HasBinaryBiproduct S.X₁ T.X₁] [HasBinaryBiproduct S.X₂ T.X₂]
    [HasBinaryBiproduct S.X₃ T.X₃] : ShortComplex V :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) (by apply biprod.hom_ext <;> simp)

/-- The biproduct of two retraction-section identities is again one. Stated for bare biproduct
maps rather than for the fields of `biprodShortComplex`, since the hidden additive structure on
the morphisms of the latter is not reducible and blocks rewriting. -/
private theorem biprod_map_splitting_id {X₁ X₂ X₃ Y₁ Y₂ Y₃ : V}
    [HasBinaryBiproduct X₁ Y₁] [HasBinaryBiproduct X₂ Y₂] [HasBinaryBiproduct X₃ Y₃]
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {r : X₂ ⟶ X₁} {s : X₃ ⟶ X₂}
    {f' : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃} {r' : Y₂ ⟶ Y₁} {s' : Y₃ ⟶ Y₂}
    (h : r ≫ f + g ≫ s = 𝟙 X₂) (h' : r' ≫ f' + g' ≫ s' = 𝟙 Y₂) :
    biprod.map r r' ≫ biprod.map f f' + biprod.map g g' ≫ biprod.map s s' = 𝟙 (X₂ ⊞ Y₂) := by
  apply biprod.hom_ext <;>
    simp only [Preadditive.add_comp, Category.assoc, biprod.map_fst, biprod.map_fst_assoc,
      biprod.map_snd, biprod.map_snd_assoc, ← Preadditive.comp_add, h, h', Category.comp_id,
      Category.id_comp]

/-- The biproduct of two split short complexes is split. -/
private noncomputable def biprodSplitting {S T : ShortComplex V}
    [HasBinaryBiproduct S.X₁ T.X₁] [HasBinaryBiproduct S.X₂ T.X₂]
    [HasBinaryBiproduct S.X₃ T.X₃] (s : S.Splitting) (t : T.Splitting) :
    (biprodShortComplex S T).Splitting where
  r := biprod.map s.r t.r
  s := biprod.map s.s t.s
  f_r := by apply biprod.hom_ext <;> simp [biprodShortComplex]
  s_g := by apply biprod.hom_ext <;> simp [biprodShortComplex]
  id := biprod_map_splitting_id s.id t.id

/-- Degreewise evaluation of a biproduct of maps of complexes. -/
private theorem biprodMap_f_naturality [HasBinaryBiproducts V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ K') (g : L ⟶ L') (n : ℤ) :
    (biprod.map f g).f n ≫ (HomologicalComplex.biprodXIso K' L' n).hom =
      (HomologicalComplex.biprodXIso K L n).hom ≫ biprod.map (f.f n) (g.f n) := by
  apply biprod.hom_ext <;> simp [← HomologicalComplex.comp_f]

/-- Degreewise evaluation commutes with the biproduct of short complexes of complexes. -/
private noncomputable def biprodShortComplexEvalIso [HasBinaryBiproducts V]
    (S T : ShortComplex (CochainComplex V ℤ)) (n : ℤ) :
    (biprodShortComplex S T).map (HomologicalComplex.eval V _ n) ≅
      biprodShortComplex (S.map (HomologicalComplex.eval V _ n))
        (T.map (HomologicalComplex.eval V _ n)) :=
  ShortComplex.isoMk (HomologicalComplex.biprodXIso _ _ n)
    (HomologicalComplex.biprodXIso _ _ n) (HomologicalComplex.biprodXIso _ _ n)
    (biprodMap_f_naturality S.f T.f n).symm (biprodMap_f_naturality S.g T.g n).symm

end Biprod

section ShortExact

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}} (sq : Square C)

open Stacks.MayerVietoris.CanonicalMapOfComplexes

attribute [local instance] coconeComplexFunctor_additive

/-- In each degree the mapping cocone of a short complex of complexes is the biproduct of the
two middle sections and the shifted first sections. -/
private noncomputable def coconeShortComplexIso
    (L : ShortComplex (CochainComplex (SheafOfModules.{v} R) ℤ)) (n : ℤ) :
    (L.map (coconeComplexFunctor sq)).map (HomologicalComplex.eval _ _ n) ≅
      biprodShortComplex
        ((biprodShortComplex (L.map (sectionsComplex R sq.X₃))
          (L.map (sectionsComplex R sq.X₂))).map (HomologicalComplex.eval _ _ n))
        ((L.map (sectionsComplex R sq.X₁)).map (HomologicalComplex.eval _ _ (n - 1))) :=
  ShortComplex.isoMk (coconeXIso sq L.X₁ n) (coconeXIso sq L.X₂ n) (coconeXIso sq L.X₃ n)
    (coconeXIso_naturality sq L.f n).symm (coconeXIso_naturality sq L.g n).symm

/-- The mapping cocone carries a degreewise split short complex of complexes to a short exact
sequence. -/
private theorem cocone_shortExact
    (L : ShortComplex (CochainComplex (SheafOfModules.{v} R) ℤ))
    (σ : ∀ n, (L.map (HomologicalComplex.eval _ _ n)).Splitting) :
    (L.map (coconeComplexFunctor sq)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    ((biprodSplitting ((biprodSplitting ((σ n).map (sections R sq.X₃))
        ((σ n).map (sections R sq.X₂))).ofIso
      (biprodShortComplexEvalIso (L.map (sectionsComplex R sq.X₃))
        (L.map (sectionsComplex R sq.X₂)) n).symm)
      ((σ (n - 1)).map (sections R sq.X₁))).ofIso
      (coconeShortComplexIso sq L n).symm).shortExact

/-- Degreewise sections carry a degreewise split short complex of complexes to a short exact
sequence. -/
private theorem sections_shortExact
    (L : ShortComplex (CochainComplex (SheafOfModules.{v} R) ℤ))
    (σ : ∀ n, (L.map (HomologicalComplex.eval _ _ n)).Splitting) (U : C) :
    (L.map (sectionsComplex R U)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => ((σ n).map (sections R U)).shortExact)

/-- The canonical map, as a morphism of short complexes. -/
private noncomputable def cSquareShortComplexMap
    (L : ShortComplex (CochainComplex (SheafOfModules.{v} R) ℤ)) :
    L.map (sectionsComplex R sq.X₄) ⟶ L.map (coconeComplexFunctor sq) where
  τ₁ := cSquare sq L.X₁
  τ₂ := cSquare sq L.X₂
  τ₃ := cSquare sq L.X₃
  comm₁₂ := (cSquare_natural sq L.f).symm
  comm₂₃ := (cSquare_natural sq L.g).symm

/-- Two out of three for the chain-level canonical map along a degreewise split short complex
of complexes. -/
private theorem cSquare_two_out_of_three
    (L : ShortComplex (CochainComplex (SheafOfModules.{v} R) ℤ))
    (σ : ∀ n, (L.map (HomologicalComplex.eval _ _ n)).Splitting) :
    (QuasiIso (cSquare sq L.X₁) → QuasiIso (cSquare sq L.X₂) → QuasiIso (cSquare sq L.X₃)) ∧
    (QuasiIso (cSquare sq L.X₂) → QuasiIso (cSquare sq L.X₃) → QuasiIso (cSquare sq L.X₁)) ∧
    (QuasiIso (cSquare sq L.X₁) → QuasiIso (cSquare sq L.X₃) → QuasiIso (cSquare sq L.X₂)) := by
  have h₁ := sections_shortExact L σ sq.X₄
  have h₂ := cocone_shortExact sq L σ
  have d₁ := DerivedCategory.triangleOfSES_distinguished h₁
  have d₂ := DerivedCategory.triangleOfSES_distinguished h₂
  let φ := DerivedCategory.triangleOfSES.map h₁ h₂ (cSquareShortComplexMap sq L)
  simp only [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact ⟨isIso₃_of_isIso₁₂ φ d₁ d₂, isIso₁_of_isIso₂₃ φ d₁ d₂, isIso₂_of_isIso₁₃ φ d₁ d₂⟩

end ShortExact

section Representatives

variable {A : Type*} [Category A] [Abelian A]

/-- K-injectivity only depends on the homotopy class of the complex. -/
private theorem isKInjective_of_homotopyCategory_iso {I K : CochainComplex A ℤ}
    (e : (HomotopyCategory.quotient _ _).obj I ≅ (HomotopyCategory.quotient _ _).obj K)
    [I.IsKInjective] : K.IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact ObjectProperty.prop_of_iso _ e (CochainComplex.IsKInjective.rightOrthogonal I)

/-- A homotopy equivalence of complexes becomes an isomorphism of the derived category. -/
private noncomputable def derivedIsoOfHomotopyIso
    {I K : CochainComplex A ℤ}
    (e : (HomotopyCategory.quotient _ _).obj I ≅ (HomotopyCategory.quotient _ _).obj K) :
    DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj K :=
  (DerivedCategory.quotientCompQhIso A).symm.app I ≪≫
    DerivedCategory.Qh.mapIso e ≪≫ (DerivedCategory.quotientCompQhIso A).app K

/-- Every distinguished triangle of the derived category is represented by a degreewise split
short exact sequence of K-injective complexes. -/
private theorem exists_degreewiseSplit_kInjective_representatives
    [IsGrothendieckAbelian.{v} A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) :
    ∃ (L : ShortComplex (CochainComplex A ℤ))
      (_σ : ∀ n, (L.map (HomologicalComplex.eval _ _ n)).Splitting),
      L.X₁.IsKInjective ∧ L.X₂.IsKInjective ∧ L.X₃.IsKInjective ∧
      Nonempty (DerivedCategory.Q.obj L.X₁ ≅ T.obj₁) ∧
      Nonempty (DerivedCategory.Q.obj L.X₂ ≅ T.obj₂) ∧
      Nonempty (DerivedCategory.Q.obj L.X₃ ≅ T.obj₃) := by
  obtain ⟨K, M, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).1 hT
  let Res := Stacks.Injectives.kInjectiveResolutionFunctor A
  let q := Stacks.Injectives.kInjectiveResolutionInclusion A
  let I := Res.obj K
  let Jc := Res.obj M
  let g := Res.map f
  have : I.IsKInjective := Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective A K
  have : Jc.IsKInjective := Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective A M
  have hg := HomotopyCategory.mappingCone_triangleh_distinguished g
  have : (CochainComplex.mappingCone g).IsKInjective := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hg
      (CochainComplex.IsKInjective.rightOrthogonal I)
      (CochainComplex.IsKInjective.rightOrthogonal Jc)
  let U := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g)
  let a : Arrow.mk (DerivedCategory.Q.map f) ≅ Arrow.mk (DerivedCategory.Q.map g) :=
    Arrow.isoMk (asIso (DerivedCategory.Q.map (q.app K)))
      (asIso (DerivedCategory.Q.map (q.app M))) (by
        symm
        change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (q.app M) =
          DerivedCategory.Q.map (q.app K) ≫ DerivedCategory.Q.map g
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg DerivedCategory.Q.map (q.naturality f))
  obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ U
    ((DerivedCategory.mem_distTriang_iff _).2 ⟨K, M, f, ⟨Iso.refl _⟩⟩)
    ((DerivedCategory.mem_distTriang_iff U).2 ⟨I, Jc, g, ⟨Iso.refl _⟩⟩) a
  let eT := e ≪≫ e'
  obtain ⟨L, σ, ⟨eL⟩⟩ :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).1 hg
  exact ⟨L, σ,
    isKInjective_of_homotopyCategory_iso (I := I) (K := L.X₁) (Triangle.π₁.mapIso eL),
    isKInjective_of_homotopyCategory_iso (I := Jc) (K := L.X₂) (Triangle.π₂.mapIso eL),
    isKInjective_of_homotopyCategory_iso (I := CochainComplex.mappingCone g) (K := L.X₃)
      (Triangle.π₃.mapIso eL),
    ⟨derivedIsoOfHomotopyIso (Triangle.π₁.mapIso eL.symm) ≪≫ (Triangle.π₁.mapIso eT).symm⟩,
    ⟨derivedIsoOfHomotopyIso (Triangle.π₂.mapIso eL.symm) ≪≫ (Triangle.π₂.mapIso eT).symm⟩,
    ⟨derivedIsoOfHomotopyIso (Triangle.π₃.mapIso eL.symm) ≪≫ (Triangle.π₃.mapIso eT).symm⟩⟩

end Representatives

section Main

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}} (sq : Square S.C)
  [HasSheafify S.J AddCommGrpCat.{v}]
  [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

open Stacks.MayerVietoris.CanonicalMapOfComplexes

/-- The two-out-of-three property for the derived comparison map of a square, in the three
cases at once. -/
private theorem isCSquareIso_two_out_of_three
    (T : Triangle (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))) :
    ((derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₁ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₂ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₃) ∧
    ((derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₂ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₃ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₁) ∧
    ((derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₁ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₃ →
      (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
          sq).IsCSquareIso T.obj₂) := by
  have : IsGrothendieckAbelian.{v}
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  obtain ⟨L, σ, _, _, _, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_degreewiseSplit_kInjective_representatives T hT
  rw [DerivedCSquareData.isCSquareIso_iff_quasiIso _ T.obj₁ L.X₁ e₁,
    DerivedCSquareData.isCSquareIso_iff_quasiIso _ T.obj₂ L.X₂ e₂,
    DerivedCSquareData.isCSquareIso_iff_quasiIso _ T.obj₃ L.X₃ e₃]
  exact cSquare_two_out_of_three sq L σ

/-- **Stacks Project, Tag 0EWP.** The comparison for the third vertex is an isomorphism if it is
so for the first two vertices of a distinguished triangle. -/
@[stacks 0EWP "first and second vertices imply the third"]
theorem isCSquareIso_obj₃_of_distTriang
    (T : Triangle (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (h₁ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₁)
    (h₂ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₂) :
    (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₃ :=
  (isCSquareIso_two_out_of_three sq T hT).1 h₁ h₂

/-- **Stacks Project, Tag 0EWP.** The comparison for the first vertex is an isomorphism if it is
so for the second and third vertices of a distinguished triangle. -/
@[stacks 0EWP "second and third vertices imply the first"]
theorem isCSquareIso_obj₁_of_distTriang
    (T : Triangle (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (h₂ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₂)
    (h₃ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₃) :
    (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₁ :=
  (isCSquareIso_two_out_of_three sq T hT).2.1 h₂ h₃

/-- **Stacks Project, Tag 0EWP.** The comparison for the second vertex is an isomorphism if it
is so for the first and third vertices of a distinguished triangle. -/
@[stacks 0EWP "first and third vertices imply the second"]
theorem isCSquareIso_obj₂_of_distTriang
    (T : Triangle (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (hT : T ∈ distTriang (DerivedCategory
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (h₁ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₁)
    (h₃ : (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      sq).IsCSquareIso T.obj₃) :
    (derivedCSquareData.{u, v} (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        sq).IsCSquareIso T.obj₂ :=
  (isCSquareIso_two_out_of_three sq T hT).2.2 h₁ h₃

end Main

end Stacks.MayerVietoris.CanonicalMapOfComplexes

end
