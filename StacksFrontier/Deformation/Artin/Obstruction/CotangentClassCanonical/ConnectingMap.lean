module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion

/-!
# The connecting map of a short exact sequence of modules

The first part of `StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical`: the long
exact sequence of a short exact sequence of modules after tensoring with a complex `K`, and the
connecting map of such a sequence read on a two-term complex.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### The long exact sequence of a short exact sequence of modules -/

/-- **A class killed by the connecting map comes from the middle term of the sequence.** For a
short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `A`-modules the sequence
`H¹(K ⊗ᴸ X₂) → H¹(K ⊗ᴸ X₃) → H²(K ⊗ᴸ X₁)` is exact, the triangle of the sequence staying
distinguished after tensoring with `K`. -/
public theorem exists_of_boundaryMap_eq_zero (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) (z : (derivedCohomology A K 1).obj Sq.X₃)
    (hz : boundaryMap A K hSq z = 0) :
    ∃ y : (derivedCohomology A K 1).obj Sq.X₂, (derivedCohomology A K 1).map Sq.g y = z := by
  have hT : (CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj
      hSq.singleTriangle ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    (CochainComplex.DerivedTensor.derivedTensorProduct K).map_distinguished _
      hSq.singleTriangle_distinguished
  exact (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₃ _ hT 1 2 (by omega)) z hz

/-! ### The connecting map of a short exact sequence read on a two-term complex -/

section ConnectingTwoTerm

open CategoryTheory.Limits HomologicalComplex CochainComplex

variable {A : Type u} [CommRing A]

/-- The morphism `(N ⟶ M) ⟶ Z[0]` of a two-term complex onto a module placed in degree zero,
given by a map `w : M ⟶ Z` killing the differential. -/
public def twoTermToSingle {T : TwoTerm.{u, u, u} A} {Z : ModuleCat.{u} A}
    (w : ModuleCat.of A T.X₀ ⟶ Z) (hw : ModuleCat.ofHom T.d ≫ w = 0) :
    twoTermComplex T ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Z :=
  mkHomFromDouble upIntRelNegOneZero (by omega : (-1 : ℤ) ≠ 0) 0
    (w ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv)
    (by rw [zero_comp, ← Category.assoc, hw, zero_comp])
    (fun k _ => by rw [single_obj_d, comp_zero])

/-- In degree zero, the projection `twoTermToSingle w hw` is `w`, up to the identifications of
the degree-zero terms of the two complexes with `T.X₀` and `Z`. -/
@[simp] public theorem twoTermToSingle_f_zero {T : TwoTerm.{u, u, u} A} {Z : ModuleCat.{u} A}
    (w : ModuleCat.of A T.X₀ ⟶ Z) (hw : ModuleCat.ofHom T.d ≫ w = 0) :
    (twoTermToSingle w hw).f 0 =
      (doubleXIso₁ (ModuleCat.ofHom T.d) upIntRelNegOneZero (by omega : (-1 : ℤ) ≠ 0)).hom ≫
        w ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv :=
  mkHomFromDouble_f₁ ..

/-- Postcomposing the projection of a two-term complex onto a module in degree zero with a map
of modules is the projection attached to the composite. -/
public theorem twoTermToSingle_comp {T : TwoTerm.{u, u, u} A} {Z Z' : ModuleCat.{u} A}
    (w : ModuleCat.of A T.X₀ ⟶ Z) (hw : ModuleCat.ofHom T.d ≫ w = 0) (g : Z ⟶ Z')
    (hwg : ModuleCat.ofHom T.d ≫ (w ≫ g) = 0) :
    twoTermToSingle (w ≫ g) hwg =
      twoTermToSingle w hw ≫ (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map g := by
  apply to_single_hom_ext
  rw [HomologicalComplex.comp_f, twoTermToSingle_f_zero, twoTermToSingle_f_zero,
    single_map_f_self]
  simp

/-- The inclusion of the degree-zero term of a two-term complex followed by the projection onto
a module placed in degree zero is that map of modules, placed in degree zero. -/
public theorem twoTermInclusion_comp_twoTermToSingle {T : TwoTerm.{u, u, u} A}
    {Z : ModuleCat.{u} A} (w : ModuleCat.of A T.X₀ ⟶ Z)
    (hw : ModuleCat.ofHom T.d ≫ w = 0) :
    twoTermInclusion (ModuleCat.ofHom T.d) ≫ twoTermToSingle w hw =
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map w := by
  apply to_single_hom_ext
  rw [HomologicalComplex.comp_f, twoTermInclusion_f_zero, twoTermToSingle_f_zero,
    single_map_f_self]
  simp

/-- The presentation-level projection onto the module of differentials is the projection
`twoTermToSingle` attached to `Algebra.Extension.toKaehler`. -/
public theorem presentationToDifferentials_eq {Λ : Type u} [CommRing Λ] [Algebra Λ A]
    {ι : Type u} (P : Algebra.Generators Λ A ι) :
    presentationToDifferentials P =
      twoTermToSingle (T := nlRestrict A P) (ModuleCat.ofHom P.toExtension.toKaehler)
        (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          exact P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero z) :=
  rfl

/-- The image in the derived category of the degree shift of the single functors, read through
the shift of the localization functor, is the degree shift of the derived single functors. -/
private theorem Q_map_singleShift_comp {Z : ModuleCat.{u} A} {Y : ModuleCat.{u} A}
    (a : Y ⟶ Z) :
    DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map a ≫
        ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
          (by omega)).inv.app Z) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Z) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map a ≫
        ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
          (by omega)).inv.app Z := by
  rw [Functor.map_comp, Category.assoc]
  dsimp only [DerivedCategory.singleFunctors]
  rw [SingleFunctors.postcomp_shiftIso_inv_app]
  rfl

/-- **The connecting map of a short exact sequence of modules, read on a two-term complex.**
Let `0 → X₁ → X₂ → X₃ → 0` be short exact and let `d : N ⟶ M` be a two-term complex mapping to
it by `a : N ⟶ X₁` and `b : M ⟶ X₂` with `a ≫ f + d ≫ b = 0`. Then the projection
`(N ⟶ M) ⟶ X₃[0]` given by `w = b ≫ g` followed by the connecting morphism
`X₃[0] ⟶ X₁[0]⟦1⟧` is the projection of the two-term complex onto `N[-1]` followed by the map
induced by `a`. In other words the composite of `w` with the boundary is computed in degree
`-1` by `a`, with no sign.

The proof twists `X₁[0]` by the two-term complex along the candidate morphism: the resulting
short exact sequence of cochain complexes is split in every degree with connecting morphism the
candidate itself, and it maps to the sequence of modules by the identity on `X₁[0]`, so the
naturality of the connecting morphism identifies the two. -/
public theorem twoTermToSingle_comp_singleδ {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) {T : TwoTerm.{u, u, u} A}
    (a : ModuleCat.of A T.X₁ ⟶ Sq.X₁) (b : ModuleCat.of A T.X₀ ⟶ Sq.X₂)
    (hab : a ≫ Sq.f + ModuleCat.ofHom T.d ≫ b = 0)
    (w : ModuleCat.of A T.X₀ ⟶ Sq.X₃) (hw : b ≫ Sq.g = w)
    (hdw : ModuleCat.ofHom T.d ≫ w = 0) :
    DerivedCategory.Q.map (twoTermToSingle w hdw) ≫ hSq.singleδ =
      DerivedCategory.Q.map (twoTermProjection (ModuleCat.ofHom T.d)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map a ≫
          ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
            (by omega)).inv.app Sq.X₁ := by
  set Z₁ := (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Sq.X₁ with hZ₁
  set ψ : (single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj (ModuleCat.of A T.X₁) ⟶
      Z₁⟦(1 : ℤ)⟧ :=
    (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map a ≫
      ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
        (by omega)).inv.app Sq.X₁ with hψ
  set φ : twoTermComplex T ⟶ Z₁⟦(1 : ℤ)⟧ :=
    twoTermProjection (ModuleCat.ofHom T.d) ≫ ψ with hφ
  -- the twist of `X₁[0]` by the two-term complex along `φ`
  have hS₁ : (CochainComplex.twistShortComplex φ).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun n => (CochainComplex.twistSplitting φ n).shortExact
  have hS₂ : (Sq.map (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)).ShortExact :=
    hSq.map_of_exact (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)
  -- the degree-zero component of the comparison of the twist with `X₂[0]`
  set φ₀ : (CochainComplex.twist φ).X 0 ⟶ Sq.X₂ :=
    Limits.biprod.desc ((singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₁).hom ≫ Sq.f)
      ((doubleXIso₁ (ModuleCat.ofHom T.d) upIntRelNegOneZero (by omega : (-1 : ℤ) ≠ 0)).hom ≫ b)
    with hφ₀
  have hdd : (CochainComplex.twist φ).d (-1) 0 =
      Limits.biprod.lift
        (Limits.biprod.fst ≫ Z₁.d (-1) 0 + Limits.biprod.snd ≫ φ.f (-1))
        (Limits.biprod.snd ≫ (twoTermComplex T).d (-1) 0) :=
    CochainComplex.twist_d φ (-1)
  have hφneg : φ.f (-1) =
      (doubleXIso₀ (ModuleCat.ofHom T.d) upIntRelNegOneZero).hom ≫ a ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₁).inv := by
    rw [hφ, HomologicalComplex.comp_f, twoTermProjection_f_neg_one, hψ,
      HomologicalComplex.comp_f]
    simp [CochainComplex.singleFunctors, CochainComplex.singleFunctor, single_map_f_self,
      singleObjXSelf, singleObjXIsoOfEq]
  have hd : ∀ k : ℤ, (ComplexShape.up ℤ).Rel k 0 →
      (CochainComplex.twist φ).d k 0 ≫ φ₀ = 0 := by
    intro k hk
    obtain rfl : k = -1 := by
      have h' : k + 1 = 0 := hk
      omega
    rw [hdd, hφ₀, Limits.biprod.lift_desc, show Z₁.d (-1) 0 = 0 from single_obj_d ..,
      Limits.comp_zero, zero_add, hφneg, double_d _ _ (by omega : (-1 : ℤ) ≠ 0)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Preadditive.comp_add]
    rw [hab, Limits.comp_zero, Limits.comp_zero]
  -- the morphism of short exact sequences of cochain complexes
  set F : CochainComplex.twistShortComplex φ ⟶
      Sq.map (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0) :=
    { τ₁ := 𝟙 _
      τ₂ := mkHomToSingle φ₀ hd
      τ₃ := twoTermToSingle w hdw
      comm₁₂ := by
        apply to_single_hom_ext
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, mkHomToSingle_f,
          CochainComplex.twistι_f, hφ₀]
        simp [single_map_f_self]
      comm₂₃ := by
        apply to_single_hom_ext
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, mkHomToSingle_f,
          CochainComplex.twistπ_f, twoTermToSingle_f_zero, hφ₀,
          show (Sq.map (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)).g =
            (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map Sq.g from rfl,
          single_map_f_self, ← hw]
        refine Limits.biprod.hom_ext' _ _ ?_ ?_
        · simp
        · simp } with hF
  have hδ₁ := triangleOfSESδ_eq_of_factorization (S := CochainComplex.twistShortComplex φ)
    (σ := CochainComplex.twistSplitting φ) hS₁ (twoTermProjection (ModuleCat.ofHom T.d)) ψ
    (CochainComplex.homOfDegreewiseSplit_twistSplitting φ)
  have hnat := DerivedCategory.triangleOfSESδ_naturality hS₁ hS₂ F
  rw [hF] at hnat
  rw [show hSq.singleδ = DerivedCategory.triangleOfSESδ hS₂ from rfl, ← hnat, hδ₁, hψ,
    Q_map_singleShift_comp a]
  simp

/-- **The evaluation of a class on a two-term complex at a map factoring through the conormal
module cannot see the degree-zero term.** The inclusion of the degree-zero term followed by the
projection onto the conormal module is zero. -/
public theorem twoTermInclusion_comp_projection_comp {T : TwoTerm.{u, u, u} A}
    {Z : ModuleCat.{u} A} (k : ModuleCat.of A T.X₁ ⟶ Z) :
    DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom T.d)) ≫
        DerivedCategory.Q.map (twoTermProjection (ModuleCat.ofHom T.d)) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map k = 0 := by
  rw [← Category.assoc, ← Functor.map_comp, twoTermInclusion_comp_twoTermProjection,
    Functor.map_zero, zero_comp]

/-- **The connecting map of a short exact sequence of modules, applied after a two-term
complex, is the degree shift of the map induced by the conormal component.** This is
`Deformation.Artin.twoTermToSingle_comp_singleδ` after applying `H¹(K ⊗ᴸ -)`: the evaluation of
a class on the two-term complex at `w` followed by the boundary map of the sequence is the
projection onto the conormal module followed by `a`, read through the degree shift
`H¹(K ⊗ᴸ X₁[1]) ≅ H²(K ⊗ᴸ X₁)`. -/
public theorem map_twoTermToSingle_comp_boundaryMap
    (K : DerivedCategory (ModuleCat.{u} A)) {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) {T : TwoTerm.{u, u, u} A}
    (a : ModuleCat.of A T.X₁ ⟶ Sq.X₁) (b : ModuleCat.of A T.X₀ ⟶ Sq.X₂)
    (hab : a ≫ Sq.f + ModuleCat.ofHom T.d ≫ b = 0)
    (w : ModuleCat.of A T.X₀ ⟶ Sq.X₃) (hw : b ≫ Sq.g = w)
    (hdw : ModuleCat.ofHom T.d ≫ w = 0) :
    (derivedTensorCohomology A K 1).map (DerivedCategory.Q.map (twoTermToSingle w hdw)) ≫
        boundaryMap A K hSq =
      (derivedTensorCohomology A K 1).map
          (DerivedCategory.Q.map (twoTermProjection (ModuleCat.ofHom T.d)) ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map a) ≫
        (shiftedCohomologyIso A K Sq.X₁).hom := by
  rw [shiftedCohomologyIso_hom_eq]
  change ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift 1).map
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
          (DerivedCategory.Q.map (twoTermToSingle w hdw))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftMap
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).map hSq.singleδ ≫
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) 1 2
        (by omega) = _
  rw [← Functor.shiftMap_comp', ← Category.assoc, ← Functor.map_comp,
    twoTermToSingle_comp_singleδ hSq a b hab w hw hdw, ← Category.assoc, Functor.map_comp,
    Category.assoc, Functor.shiftMap_comp']
  rfl

/-- **The evaluation of a class at a thickening whose extension class factors through the
conormal module of a presentation is the boundary of its image in `H¹(K ⊗ᴸ X₃)`.** Here `cls`
is the extension class `NL_{A/Λ} ⟶ X₁[1]` of the thickening and `proj` its projection onto
`X₃[0]`, each read through the comparison `iso` of the naive cotangent complex with the
two-term complex of a presentation. In the proof of 07YY this says that the obstruction
evaluation at `C'` is the boundary of `ξ_can`. -/
public theorem shiftedCohomologyIso_map_eq_boundaryMap
    (K : DerivedCategory (ModuleCat.{u} A)) {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) {T : TwoTerm.{u, u, u} A}
    (a : ModuleCat.of A T.X₁ ⟶ Sq.X₁) (b : ModuleCat.of A T.X₀ ⟶ Sq.X₂)
    (hab : a ≫ Sq.f + ModuleCat.ofHom T.d ≫ b = 0)
    (w : ModuleCat.of A T.X₀ ⟶ Sq.X₃) (hw : b ≫ Sq.g = w)
    (hdw : ModuleCat.ofHom T.d ≫ w = 0)
    {NL : DerivedCategory (ModuleCat.{u} A)}
    (iso : DerivedCategory.Q.obj (twoTermComplex T) ≅ NL)
    (cls : NL ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj Sq.X₁)
    (hcls : iso.hom ≫ cls =
      DerivedCategory.Q.map (twoTermProjection (ModuleCat.ofHom T.d)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map a)
    (proj : NL ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₃)
    (hproj : iso.hom ≫ proj = DerivedCategory.Q.map (twoTermToSingle w hdw))
    (ξ : (derivedTensorCohomology A K 1).obj NL) :
    (shiftedCohomologyIso A K Sq.X₁).hom ((derivedTensorCohomology A K 1).map cls ξ) =
      boundaryMap A K hSq ((derivedTensorCohomology A K 1).map proj ξ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ, (derivedTensorCohomology A K 1).map iso.hom ζ = ξ :=
    ⟨(derivedTensorCohomology A K 1).map iso.inv ξ, by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, iso.inv_hom_id]
      simp⟩
  subst hζ
  have key : ∀ {Y : DerivedCategory (ModuleCat.{u} A)} (f : NL ⟶ Y)
      (g : DerivedCategory.Q.obj (twoTermComplex T) ⟶ Y), iso.hom ≫ f = g →
      (derivedTensorCohomology A K 1).map f ((derivedTensorCohomology A K 1).map iso.hom ζ) =
        (derivedTensorCohomology A K 1).map g ζ := fun f g h => by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, h]
  rw [key _ _ hcls, key _ _ hproj, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    map_twoTermToSingle_comp_boundaryMap K hSq a b hab w hw hdw]

end ConnectingTwoTerm

end Deformation.Artin

end
