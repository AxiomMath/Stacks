module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardForgetTrivializationIsoClasses
public import StacksFrontier.AlgebraicGeometry.Quot.TrivializationSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization

/-!
# The forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` (Stacks 0D2A)

In Situation 0D25, let `σ : B ⟶ X` be a section.  The 1-morphism
`Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` forgetting the trivialisation is representable,
surjective and smooth.

Following the proof of Stacks 0D2A: over a scheme-valued point `ξ = (T, h, L)`, the forgetful
functor is faithful on fibre categories, so the base change is fibred in setoids, and its
isomorphism classes over `T' ⟶ T` are the trivialisations `𝒪_{T'} ≅ (T' ⟶ T)^*σ_T^*L`. That
presheaf is represented by a scheme `V` over `T` which is smooth and surjective over `T`, being
étale locally `𝔾_m × T`. The representing scheme is produced directly rather than through the
representability theorem 08K9 for `Isom`: the presheaf of trivialisations is an fppf sheaf, it is
étale locally the multiplicative group, and affine morphisms descend along surjective étale
coverings.

## Main results

* `AlgebraicGeometry.Space.forgetTrivialization_representable_surjective_smooth`: **Stacks 0D2A**,
  all three clauses: representable (Stacks 02Y7 and 02ZW), surjective and smooth (Stacks 03YK).
* `AlgebraicGeometry.Space.exists_isoClass_equiv_yoneda_overMap`: the base change along a
  scheme-valued point is represented by a scheme smooth and surjective over the test scheme.

## Implementation notes

The proofs are stated for an arbitrary coherence `hc` of the direct images (Stacks 03LU); the
registered statement instantiates the unconditional one,
`AlgebraicGeometry.Space.modulePushforwardCoherence`, with the coherence of the section transport
`AlgebraicGeometry.Space.sectionTransportCoherence`.  The family of test schemes of a
scheme-valued point is compared with the iterated slice through the terminal object of the
indexing category (`AlgebraicGeometry.Space.alongSliceIso`), so the two cases — points
`(Sch/U)_{fppf} ⟶ Picardstack_{X/B}` for Stacks 02ZW and 03YK, and 1-morphisms from slices
`𝒞/U ⟶ Picardstack_{X/B}` for Stacks 02Y7 — share one argument.

## References

* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space over `U` represented by a scheme `V` over `U`**: its structural morphism,
read over `S`, has a property respecting isomorphisms as soon as the Yoneda image of `V ⟶ U`
has it. -/
theorem prop_algebraicSpaceMap_of_iso_yoneda (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (V : BigFppfOver B U.left.1 U.left.2) (e : F ≅ yoneda.obj V)
    (hV : P (schemeSpaceMap (Over.homMk V.hom rfl : (Over.map U.hom).obj V ⟶ Over.mk U.hom) :
        (schemeSpace ((Over.map U.hom).obj V) :
          AlgebraicSpaces B S hS) ⟶
        schemeSpace (Over.mk U.hom))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  refine (prop_algebraicSpaceMap_iff B S hS P U F hF).mpr ?_
  let k : (Over.map U.hom).obj V ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let j : (OverShriek.relocalizePresheafFunctor U.hom).obj F ≅
      yoneda.obj ((Over.map U.hom).obj V) :=
    (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso U.hom).app V
  have hj : j.hom ≫ yoneda.map k = OverShriek.relocalizeToYoneda U.hom F := by
    dsimp only [j, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, relocalizeToYoneda_yoneda, relocalizeToYoneda_comp_map]
  let A : AlgebraicSpaces B S hS := ⟨(OverShriek.relocalizePresheafFunctor U.hom).obj F,
    isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF⟩
  let jA : A ≅ ⟨yoneda.obj ((Over.map U.hom).obj V), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ j
  have hfac : (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom F) :
      A ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) =
      jA.hom ≫ ObjectProperty.homMk (yoneda.map k) := by
    apply ObjectProperty.hom_ext
    exact hj.symm
  rw [hfac]
  exact (MorphismProperty.cancel_left_of_respectsIso P jA.hom _).mpr hV

end AlgebraicGeometry.Stack

/-- A presheaf mapping bijectively and naturally onto a presheaf isomorphic to the presheaf
represented by `W` is in natural bijection with the morphisms into `W`. -/
theorem CategoryTheory.exists_equiv_yoneda_of_bijective_of_iso {C : Type (u + 1)}
    [Category.{u} C] (A X : Cᵒᵖ ⥤ Type (u + 1)) (Φ : ∀ V, A.obj V → X.obj V)
    (hΦ : ∀ V, Function.Bijective (Φ V))
    (hnat : ∀ ⦃V₁ V₂ : Cᵒᵖ⦄ (f : V₁ ⟶ V₂) (x : A.obj V₁), Φ V₂ (A.map f x) = X.map f (Φ V₁ x))
    {W : C} (k : X ≅ yoneda.obj W ⋙ uliftFunctor.{u + 1}) :
    ∃ e : ∀ V : Cᵒᵖ, A.obj V ≃ (yoneda.obj W).obj V,
      ∀ ⦃V₁ V₂ : Cᵒᵖ⦄ (f : V₁ ⟶ V₂) (x : A.obj V₁),
        e V₂ (A.map f x) = (yoneda.obj W).map f (e V₁ x) := by
  refine ⟨fun V ↦ (Equiv.ofBijective (Φ V) (hΦ V)).trans ((k.app V).toEquiv.trans Equiv.ulift),
    fun V₁ V₂ f x ↦ ?_⟩
  exact (congrArg (fun z ↦ Equiv.ulift ((k.app V₂).toEquiv z)) (hnat f x)).trans
    (congrArg Equiv.ulift (ConcreteCategory.congr_hom (k.hom.naturality f) (Φ V₁ x)))

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
  (hc : ModulePushforwardCoherence B S hS)

section Slice

variable {𝒯 : Type*} [Category* 𝒯] (P𝒯 : 𝒯 ⥤ BigFppfOver B S hS)
  {y : 𝒯 ⥤ (picardCFG hc s).val.obj} (hy : y ⋙ (picardCFG hc s).val.p = P𝒯)
  {top : 𝒯} (htop : IsTerminal top)

/-- The family `P𝒯` read as a family of schemes over its value at the terminal object. -/
abbrev terminalSlice : 𝒯 ⥤ Over (P𝒯.obj top) :=
  P𝒯.toOver (P𝒯.obj top) (fun V ↦ P𝒯.map (htop.from V)) (fun g ↦ by
    rw [← P𝒯.map_comp, htop.hom_ext (_ ≫ htop.from _) (htop.from _)])

/-- **The family of test schemes of `y` over the one of `y(⊤)` is the family `P𝒯`**, once `y` lies
over `P𝒯`. -/
def alongSliceIso :
    alongSlice hc y.obj (familyMap hc y) (familyMap_id hc y) (familyMap_comp hc y) htop ≅
      terminalSlice P𝒯 htop ⋙ Over.map (eqToHom (Functor.congr_obj hy top).symm) :=
  NatIso.ofComponents (fun V ↦ Over.isoMk (eqToIso (Functor.congr_obj hy V)) (by
      have h := Functor.congr_hom hy (htop.from V)
      change eqToHom (Functor.congr_obj hy V) ≫ P𝒯.map (htop.from V) ≫
        eqToHom (Functor.congr_obj hy top).symm = (y.map (htop.from V)).base.left
      refine Eq.trans ?_ h.symm
      rfl))
    (fun {V W} g ↦ by
      have h := Functor.congr_hom hy g
      apply Over.OverMorphism.ext
      change (y.map g).base.left ≫ eqToHom (Functor.congr_obj hy W) =
        eqToHom (Functor.congr_obj hy V) ≫ P𝒯.map g
      have h' : (y.map g).base.left = eqToHom (Functor.congr_obj hy V) ≫ P𝒯.map g ≫
          eqToHom (Functor.congr_obj hy W).symm := h
      rw [h']
      exact (Category.assoc _ _ _).trans (congrArg (eqToHom _ ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg (P𝒯.map g ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans
          (Category.comp_id _)))))

end Slice

section Cases

/-- An object `U` of the big fppf site of `S` is the image of the terminal object of the big fppf
site of `U` under the functor reading schemes over `U` as schemes over `S`. -/
theorem eq_overMap_obj_mkId (U : BigFppfOver B S hS) :
    U = (Over.map U.hom).obj (Over.mk (𝟙 (B.obj U.left.2))) :=
  (congrArg Over.mk (Category.id_comp U.hom)).symm

/-- On the big fppf site of a scheme `U` over `S`, read over `S`, the family of schemes over the
value at the terminal object is the iterated slice. -/
def terminalSliceOverMapIso (U : BigFppfOver B S hS) :
    terminalSlice (Over.map U.hom) (Over.mkIdTerminal (X := B.obj U.left.2)) ≅
      U.iteratedSliceBackward ⋙ Over.map (eqToHom (eq_overMap_obj_mkId U)) :=
  NatIso.ofComponents (fun V ↦ Over.isoMk (Iso.refl _) (by
      apply Over.OverMorphism.ext
      have hw : (Over.mkIdTerminal.from V).left = V.hom := by simp
      have h1 : (eqToHom (eq_overMap_obj_mkId U)).left = 𝟙 _ :=
        (Over.eqToHom_left _).trans (eqToHom_refl _ _)
      refine Eq.trans ?_ hw.symm
      exact (Category.id_comp _).trans ((congrArg (V.hom ≫ ·) h1).trans (Category.comp_id _))))
    (fun {V W} g ↦ by
      apply Over.OverMorphism.ext
      apply Over.OverMorphism.ext
      simp only [Over.comp_left]
      rfl)

/-- On the slice over `U`, the family of schemes over the value at the terminal object is the
identity. -/
def terminalSliceOverForgetIso (U : BigFppfOver B S hS) :
    terminalSlice (Over.forget U) (Over.mkIdTerminal (X := U)) ≅ 𝟭 (Over U) :=
  NatIso.ofComponents (fun V ↦ Over.isoMk (Iso.refl _) (by
      have hw : (Over.mkIdTerminal.from V).left = V.hom := by simp
      exact (Category.id_comp _).trans hw.symm))
    (fun {V W} g ↦ by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left]
      rfl)

end Cases

section Represented

/-- **The trivialisations of an invertible module, along a functor isomorphic to the iterated
slice, are represented by a scheme smooth and surjective over the base.** -/
theorem exists_iso_yoneda_of_iso_iteratedSliceBackward (U T' : BigFppfOver B S hS) (h : U = T')
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj T').1
      ((schemeSpaceFunctor B S hS).obj T').2)
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj T') N)
    (L : BigFppfOver B U.left.1 U.left.2 ⥤ Over T')
    (iL : L ≅ U.iteratedSliceBackward ⋙ Over.map (eqToHom h)) :
    ∃ W : BigFppfOver B U.left.1 U.left.2,
      Nonempty (L.op ⋙ trivializationsPresheaf T' N ≅ yoneda.obj W ⋙ uliftFunctor.{u + 1}) ∧
      Smooth ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) := by
  subst h
  obtain ⟨W, i, hsm, hsu, -⟩ := exists_iso_yoneda_trivializationsSitePresheaf U N hN
  refine ⟨W, ⟨?_⟩, hsm, hsu⟩
  let k : U.iteratedSliceBackward ⋙ Over.map (eqToHom rfl) ≅ U.iteratedSliceBackward :=
    Functor.isoWhiskerLeft _ (Over.mapId U) ≪≫ Functor.rightUnitor _
  exact Functor.isoWhiskerRight (NatIso.op (iL ≪≫ k)).symm _ ≪≫
    eqToIso (trivializationsSliceFunctor_eq U N).symm ≪≫
      (shrinkSitePresheafIso (trivializationsSliceFunctor U N)).symm ≪≫
      Functor.isoWhiskerRight i uliftFunctor

/-- A presheaf with a universal element is isomorphic to the presheaf represented by its
carrier. -/
def isoYonedaOfBijective {C : Type (u + 1)} [Category.{u} C] (F : Cᵒᵖ ⥤ Type (u + 1)) {W : C}
    (τ : F.obj (op W)) (hτ : ∀ T : C, Function.Bijective (fun k : T ⟶ W ↦ F.map k.op τ)) :
    F ≅ yoneda.obj W ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T ↦ ((Equiv.ofBijective _ (hτ T.unop)).symm.trans
      Equiv.ulift.symm).toIso)
    (fun {T₁ T₂} f ↦ by
      apply ConcreteCategory.hom_ext
      intro x
      obtain ⟨k, rfl⟩ := (hτ T₁.unop).2 x
      change ULift.up ((Equiv.ofBijective _ (hτ T₂.unop)).symm (F.map f (F.map k.op τ))) =
        ULift.up (f.unop ≫ (Equiv.ofBijective _ (hτ T₁.unop)).symm (F.map k.op τ))
      congr 1
      have h1 : (Equiv.ofBijective _ (hτ T₁.unop)).symm (F.map k.op τ) = k :=
        Equiv.ofBijective_symm_apply_apply _ _ _
      rw [h1, Equiv.symm_apply_eq, Equiv.ofBijective_apply, op_comp, FunctorToTypes.map_comp_apply]
      rfl)

/-- **The trivialisations of an invertible module, along a functor isomorphic to the
identification of the slices, are represented.** -/
theorem exists_iso_yoneda_of_iso_overMap (U T' : BigFppfOver B S hS) (h : U = T')
    (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj T').1
      ((schemeSpaceFunctor B S hS).obj T').2)
    (hN : IsInvertibleModule ((schemeSpaceFunctor B S hS).obj T') N)
    (L : Over U ⥤ Over T') (iL : L ≅ Over.map (eqToHom h)) :
    ∃ W : Over U,
      Nonempty (L.op ⋙ trivializationsPresheaf T' N ≅ yoneda.obj W ⋙ uliftFunctor.{u + 1}) := by
  subst h
  obtain ⟨W, τ, hτ, -, -⟩ := exists_universal_trivializationsPresheaf U N hN
  exact ⟨W, ⟨Functor.isoWhiskerRight (NatIso.op (iL ≪≫ Over.mapId U)).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.opId _) _ ≪≫ Functor.leftUnitor _ ≪≫
      isoYonedaOfBijective (trivializationsPresheaf U N) τ hτ⟩⟩

end Represented

section IsoClasses

variable {𝒯 : Type*} [Category* 𝒯] (P𝒯 : 𝒯 ⥤ BigFppfOver B S hS)
  (y : 𝒯 ⥤ (picardCFG hc s).val.obj)

/-- **The fibres of the 2-fibre product of the forgetful 1-morphism are thin**: a morphism of a
fibre is determined by its two components, the first being an identity up to `eqToHom` and the
second being determined by the comparison square, since forgetting the trivialisation is faithful.
-/
theorem forgetTrivializationFibreFst_isThin (V : 𝒯) :
    Quiver.IsThin ((forgetTrivializationFibreFst σ hσ hc P𝒯 y).Fiber V) := by
  intro a b
  constructor
  intro φ ψ
  apply Functor.Fiber.hom_ext
  have hφ := φ.2
  have hψ := ψ.2
  have ha : φ.1.a = ψ.1.a :=
    (IsHomLift.fac' (forgetTrivializationFibreFst σ hσ hc P𝒯 y) (𝟙 V) φ.1).trans
      (IsHomLift.fac' (forgetTrivializationFibreFst σ hσ hc P𝒯 y) (𝟙 V) ψ.1).symm
  refine TwoFibreProductOver.Hom.ext' ha ?_
  apply PicardSituation.SectionedPicardHom.ext
  have wφ := φ.1.w
  have wψ := ψ.1.w
  rw [ha] at wφ
  exact (cancel_epi a.1.iso.hom).1 (wφ.symm.trans wψ)

end IsoClasses

section Equiv

variable {𝒯 : Type (u + 1)} [Category.{u} 𝒯] {P𝒯 : 𝒯 ⥤ BigFppfOver B S hS}
  {y : 𝒯 ⥤ (picardCFG hc s).val.obj}

/-- **The isomorphism classes of the 2-fibre product are the morphisms into a representing
object**, naturally, as soon as the trivialisations along the family of test schemes are
represented. -/
theorem exists_isoClass_equiv_of_iso_yoneda (hy : y ⋙ (picardCFG hc s).val.p = P𝒯) {top : 𝒯}
    (htop : IsTerminal top)
    (hfib : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFiberedInGroupoids)
    [(forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFibered] {W : 𝒯}
    (k : (alongSlice hc y.obj (familyMap hc y) (familyMap_id hc y) (familyMap_comp hc y)
        htop).op ⋙ trivializationsPresheaf (y.obj top).T.left
          ((PicardSituation.sectionPullback σ hσ (y.obj top).T).obj (y.obj top).lineBundle) ≅
      yoneda.obj W ⋙ uliftFunctor.{u + 1}) :
    ∃ e : ∀ V : 𝒯ᵒᵖ,
        (forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.obj V ≃ (yoneda.obj W).obj V,
      ∀ ⦃V₁ V₂ : 𝒯ᵒᵖ⦄ (f : V₁ ⟶ V₂)
        (x : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.obj V₁),
        e V₂ ((forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.map f x) =
          (yoneda.obj W).map f (e V₁ x) :=
  CategoryTheory.exists_equiv_yoneda_of_bijective_of_iso _ _
    (fun V ↦ forgetTrivializationIsoClassMap σ hσ hc P𝒯 y V.unop)
    (fun V ↦ bijective_forgetTrivializationIsoClassMap σ hσ hc P𝒯 y hfib hy V.unop)
    (fun _ _ f x ↦ forgetTrivializationIsoClassMap_naturality σ hσ hc P𝒯 y f.unop x)
    (trivializationsAlongIso σ hσ hc y.obj (familyMap hc y) (familyMap_id hc y)
      (familyMap_comp hc y) htop ≪≫ k)

end Equiv

section Core

/-- The first projection of the base change of the forgetful 1-morphism along a scheme-valued
point `(Sch/U)_{fppf} ⟶ Picardstack_{X/B}` is fibred in groupoids. -/
theorem isFiberedInGroupoids_forgetTrivializationFibreFst_overMap (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (picardCFG hc s).val.obj)
    (hy : y ⋙ (picardCFG hc s).val.p = Over.map U.hom) :
    (forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).IsFiberedInGroupoids :=
  Stack.fst_isFiberedInGroupoids_overMap U.hom _ _ y _
    (sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).property
    (picardCFG hc s).property hy
    (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom.w

/-- The first projection of the base change of the forgetful 1-morphism along a 1-morphism
`𝒞/U ⟶ Picardstack_{X/B}` is fibred in groupoids. -/
theorem isFiberedInGroupoids_forgetTrivializationFibreFst_overForget (U : BigFppfOver B S hS)
    (G : Over U ⥤ (picardCFG hc s).val.obj)
    (hG : G ⋙ (picardCFG hc s).val.p = Over.forget U) :
    (forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).IsFiberedInGroupoids :=
  TwoFibreProductOver.fst_isFiberedInGroupoids U _ _ _ G
    (sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).property
    (picardCFG hc s).property
    (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom.w hG

/-- **Over a scheme-valued point `y : (Sch/U)_{fppf} ⟶ Picardstack_{X/B}`, the isomorphism classes
of the base change of the forgetful 1-morphism are the morphisms into a scheme `W` over `U`, and
`W ⟶ U` is smooth and surjective.** -/
theorem exists_isoClass_equiv_yoneda_overMap (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (picardCFG hc s).val.obj)
    (hy : y ⋙ (picardCFG hc s).val.p = Over.map U.hom)
    [(forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).IsFibered] :
    ∃ (W : BigFppfOver B U.left.1 U.left.2) (e : ∀ V,
        (forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).isoClassPresheaf.obj V ≃
          (yoneda.obj W).obj V),
      (∀ ⦃V₁ V₂⦄ (f : V₁ ⟶ V₂)
        (x : (forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).isoClassPresheaf.obj V₁),
        e V₂ ((forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).isoClassPresheaf.map f x) =
          (yoneda.obj W).map f (e V₁ x)) ∧
      Smooth ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) ∧
      Surjective ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Over.mkIdTerminal.from W)) := by
  have hfib := isFiberedInGroupoids_forgetTrivializationFibreFst_overMap σ hσ hc U y hy
  let htop := Over.mkIdTerminal (X := B.obj U.left.2)
  have h : U = (y.obj (Over.mk (𝟙 (B.obj U.left.2)))).T.left :=
    (eq_overMap_obj_mkId U).trans (Functor.congr_obj hy _).symm
  let iL := alongSliceIso hc (Over.map U.hom) hy htop ≪≫
    Functor.isoWhiskerRight (terminalSliceOverMapIso U) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Over.mapComp _ _).symm ≪≫
        Over.mapCongr _ (eqToHom h) (eqToHom_trans _ _))
  obtain ⟨W, ⟨k⟩, hsm, hsu⟩ := exists_iso_yoneda_of_iso_iteratedSliceBackward U _ h _
    (modulePullbackInvertible _ _ (y.obj (Over.mk (𝟙 (B.obj U.left.2)))).invertible) _ iL
  obtain ⟨e, he⟩ := exists_isoClass_equiv_of_iso_yoneda σ hσ hc hy htop hfib k
  exact ⟨W, e, he, hsm, hsu⟩

/-- **Over a 1-morphism `G : 𝒞/U ⟶ Picardstack_{X/B}`, the isomorphism classes of the base change
of the forgetful 1-morphism are the morphisms into an object of `𝒞/U`.** -/
theorem exists_isoClass_equiv_yoneda_overForget (U : BigFppfOver B S hS)
    (G : Over U ⥤ (picardCFG hc s).val.obj)
    (hG : G ⋙ (picardCFG hc s).val.p = Over.forget U)
    [(forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).IsFibered] :
    ∃ (W : Over U) (e : ∀ V,
        (forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).isoClassPresheaf.obj V ≃
          (yoneda.obj W).obj V),
      ∀ ⦃V₁ V₂⦄ (f : V₁ ⟶ V₂)
        (x : (forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).isoClassPresheaf.obj V₁),
        e V₂ ((forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).isoClassPresheaf.map f x) =
          (yoneda.obj W).map f (e V₁ x) := by
  have hfib := isFiberedInGroupoids_forgetTrivializationFibreFst_overForget σ hσ hc U G hG
  let htop := Over.mkIdTerminal (X := U)
  have h : U = (G.obj (Over.mk (𝟙 U))).T.left := (Functor.congr_obj hG (Over.mk (𝟙 U))).symm
  let iL := alongSliceIso hc (Over.forget U) hG htop ≪≫
    Functor.isoWhiskerRight (terminalSliceOverForgetIso U) _ ≪≫ Functor.leftUnitor _
  obtain ⟨W, ⟨k⟩⟩ := exists_iso_yoneda_of_iso_overMap U _ h _
    (modulePullbackInvertible _ _ (G.obj (Over.mk (𝟙 U))).invertible) _ iL
  exact ⟨W, exists_isoClass_equiv_of_iso_yoneda σ hσ hc hG htop hfib k⟩

end Core

section Main

/-- **Stacks 0D2A, clause (1), in the form of Stacks 02ZW**: the forgetful 1-morphism is
representable by algebraic spaces, the base change along a scheme-valued point being represented
by a scheme. -/
theorem isRepresentableByAlgebraicSpaces_forgetTrivialization_of_coherence :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
      (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom := by
  intro U _ _ y hy
  have : (forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).IsFiberedInSetoids :=
    ⟨isFiberedInGroupoids_forgetTrivializationFibreFst_overMap σ hσ hc U y hy,
      forgetTrivializationFibreFst_isThin σ hσ hc _ y⟩
  obtain ⟨W, e, he, -, -⟩ := exists_isoClass_equiv_yoneda_overMap σ hσ hc U y hy
  exact ⟨yoneda.obj W, isAlgebraicSpace_yoneda B U.left.1 U.left.2 W,
    ⟨equivalenceOver_elements_of_setoids _ (yoneda.obj W) e he⟩⟩

/-- The base changes of the forgetful 1-morphism along scheme-valued points have structural
morphisms with every property respecting isomorphisms that the Yoneda images of smooth surjective
morphisms of schemes have. -/
theorem hasRelativeProperty_forgetTrivialization_of_yoneda
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hP : ∀ {V T : BigFppfOver B S hS} (k : V ⟶ T),
      Smooth ((BigFppfOver.toScheme B S hS).map k) →
      Surjective ((BigFppfOver.toScheme B S hS).map k) →
      P (schemeSpaceMap k :
        (schemeSpace V : AlgebraicSpaces B S hS) ⟶
          schemeSpace T)) :
    Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS P
      (forgetTrivialization hc (sectionTransportCoherence hc σ hσ))
      (isRepresentableByAlgebraicSpaces_forgetTrivialization_of_coherence σ hσ hc) := by
  intro U y hy F hF ⟨d⟩
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hs : (forgetTrivializationFibreFst σ hσ hc (Over.map U.hom) y).IsFiberedInSetoids :=
    ⟨isFiberedInGroupoids_forgetTrivializationFibreFst_overMap σ hσ hc U y hy,
      forgetTrivializationFibreFst_isThin σ hσ hc _ y⟩
  obtain ⟨W, e, he, hsm, hsu⟩ := exists_isoClass_equiv_yoneda_overMap σ hσ hc U y hy
  let i : F ≅ yoneda.obj W := PresheafOfCategories.isoOfEquivalenceOver d
    (equivalenceOver_elements_of_setoids _ (yoneda.obj W) e he)
  have hterm : Over.mkIdTerminal.from W = Over.homMk W.hom (by simp) :=
    Over.mkIdTerminal.hom_ext _ _
  rw [hterm] at hsm hsu
  exact Stack.prop_algebraicSpaceMap_of_iso_yoneda B S hS P U F hF W i (hP _ hsm hsu)

/-- **Stacks 0D2A, clause (3)**: the forgetful 1-morphism is smooth. -/
theorem hasRelativeProperty_smooth_forgetTrivialization_of_coherence :
    Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      (forgetTrivialization hc (sectionTransportCoherence hc σ hσ))
      (isRepresentableByAlgebraicSpaces_forgetTrivialization_of_coherence σ hσ hc) :=
  hasRelativeProperty_forgetTrivialization_of_yoneda σ hσ hc _
    (fun k hk _ ↦ Space.isSmooth_yoneda_map B S hS k hk)

/-- **Stacks 0D2A, clause (2)**: the forgetful 1-morphism is surjective. -/
theorem hasRelativeProperty_surjective_forgetTrivialization_of_coherence :
    Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      (forgetTrivialization hc (sectionTransportCoherence hc σ hσ))
      (isRepresentableByAlgebraicSpaces_forgetTrivialization_of_coherence σ hσ hc) :=
  hasRelativeProperty_forgetTrivialization_of_yoneda σ hσ hc _
    (fun k _ hk ↦ Space.isSurjective_yoneda_map B S hS k hk)

/-- **Stacks 0D2A, clause (1), in the form of Stacks 02Y7**: the forgetful 1-morphism is
representable, its base change along every 1-morphism from a slice being a representable
category fibred in groupoids. -/
theorem isRepresentableMorphism_forgetTrivialization_of_coherence :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
      (sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).val.p
      (picardCFG hc s).val.p
      (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom.toFunctor := by
  intro U G hG
  have : (forgetTrivializationFibreFst σ hσ hc (Over.forget U) G).IsFiberedInSetoids :=
    ⟨isFiberedInGroupoids_forgetTrivializationFibreFst_overForget σ hσ hc U G hG,
      forgetTrivializationFibreFst_isThin σ hσ hc _ G⟩
  obtain ⟨W, e, he⟩ := exists_isoClass_equiv_yoneda_overForget σ hσ hc U G hG
  exact Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _ ⟨W,
    ⟨(equivalenceOver_elements_of_setoids _ (yoneda.obj W) e he).trans
      (PresheafOfCategories.sliceElementsEquivalenceOver W).symm⟩⟩

/-- In Situation 0D25, let `σ : B ⟶ X` be a section.  The 1-morphism
`Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` forgetting the trivialisation is representable,
surjective and smooth: its base change along every 1-morphism from a slice of the site is
represented by an object of the site (Stacks 02Y7, 04ST), it is representable by algebraic spaces
(Stacks 02ZW), and every algebraic space representing its base change along a scheme-valued point
has surjective and smooth structural morphism (Stacks 03YK, 04SX). -/
@[stacks 0D2A]
theorem forgetTrivialization_representable_surjective_smooth :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
        (sectionedPicardCFG (modulePushforwardCoherence B S hS)
          (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)).val.p
        (picardCFG (modulePushforwardCoherence B S hS) s).val.p
        (forgetTrivialization (modulePushforwardCoherence B S hS)
          (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)).hom.toFunctor ∧
      ∃ hf : Stack.IsRepresentableByAlgebraicSpaces B S hS
          (forgetTrivialization (modulePushforwardCoherence B S hS)
            (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)).hom,
        Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS
            (Space.surjectiveMorphismProperty B S hS)
            (forgetTrivialization (modulePushforwardCoherence B S hS)
              (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)) hf ∧
          Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS
            (Space.smoothMorphismProperty B S hS)
            (forgetTrivialization (modulePushforwardCoherence B S hS)
              (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)) hf :=
  ⟨isRepresentableMorphism_forgetTrivialization_of_coherence σ hσ _,
    isRepresentableByAlgebraicSpaces_forgetTrivialization_of_coherence σ hσ _,
    hasRelativeProperty_surjective_forgetTrivialization_of_coherence σ hσ _,
    hasRelativeProperty_smooth_forgetTrivialization_of_coherence σ hσ _⟩

end Main

end AlgebraicGeometry.Space
